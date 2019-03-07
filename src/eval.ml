module Make = functor (D : Dyadic.DYADIC) ->
struct

  module I = Interval.Make(D)
  module Env = Environment.Make(D)
  module S = Syntax.Make(D)
  module N = Newton.Make(D)
  module R = Region.Make(D)
  module A = Approximate.Make(D)
	module TC = Typecheck.Make(D)

  let error = Message.runtime_error

  (* The target precision for top-level evaluation of real
     numbers. Default is 53 bits, like floating-point. *)

  let target_precision = ref (D.make_int ~prec:10 ~round:D.up 1 (-53))

  (* Given precision [prec] and interval [i], compute a precision which
     is better than [prec] and is suitable for working with intervals of
     width [i]. *)

  let make_prec prec i =
    let w = I.width ~prec:2 ~round:D.up i in
    let e1 = D.get_exp w in
    let e2 = max (D.get_exp (I.lower i)) (D.get_exp (I.upper i)) in
      max 2 (max prec (- 5 * (e1 - e2) / 4))

  (* [make_exists x i p] constructs the existential quantifier [Exists (x,i,p)]
     over an inhabited interval [i]. If [p] is [True] or [False] it shortcircuits
     the quantifier. *)

  let make_exists x i p =
    assert (I.forward i) ;
    if p = S.True then
      S.True
    else if p = S.False then
      S.False
    else
      S.Exists (x, i, p)

  (* [make_forall x i p] constructs the universal quantifier [Forall (x,i,p)]
     over an inhabited interval [i]. If [p] is [True] or [False] it shortcircuits
     the quantifier. *)

  let make_forall x i p =
    assert (I.forward i) ;
    if p = S.True then
      S.True
    else if p = S.False then
      S.False
    else
      S.Forall (x, i, p)


  (* \subsection{Evaluation} *)

  (* The general strategy for evaluation is to successively
     \emph{refine} a closed expressoin until it reaches a satisfactory
     form. An expression of type [Ty_Real] is `satisfactory' if its
     lower approximant is narrow enough (see the [\$precision]
     toplevel command). An proposition is satisfactory if it is [True]
     or [False]. Tuples are satisfactory, i.e., they are evaluated
     lazily (but the top-level [eval] evaluates top-level tuples to make
     the user happy). A $\lambda$-abstraction is not evaluated.
  *)

	let rec free_in y e = match e with
	| S.Var x -> x = y
	| S.RealVar _ | S.Dyadic _ | S.Interval _ | S.True | S.False
	| S.Integer _
	| S.Random _ -> false
	| S.Cut (x, i, p1, p2) -> x<>y && (free_in y p1 || free_in y p2)
	| S.Restrict (e1, e2)
	| S.Binary (_, e1, e2) -> free_in y e1 || free_in y e2
	| S.RandomF e
	| S.Unary (_, e) -> free_in y e
	| S.Power (e, k) -> free_in y e
	| S.Proj (e, k) ->
	    (match  e with
	       | S.Tuple _ as e' -> free_in y (A.proj e' k)
	       | e' -> free_in y e)
	| S.Less (e1, e2) -> free_in y e1 || free_in y e2
	| S.And lst
	| S.Or lst
	| S.Join lst
	| S.Tuple lst -> List.fold_left (fun p e -> p || free_in y e) false lst
	| S.Lambda (x, ty, e) -> x<>y && (free_in y e)
	| S.Exists (x, i, e) -> x<>y && (free_in y e)
	| S.Forall (x, i, e) -> x<>y && (free_in y e)
	| S.Integral (x, i, e) -> x<>y && (free_in y e)
	| S.App (e1, e2)  -> free_in y e1 || free_in y e2
	| S.Let (x, e1, e2) -> free_in y e1 || (x<>y && free_in y e2)
	| S.TyExpr t -> TC.free_in y t

    let rec free_in_env x env e =
      match env with
	| [] -> false
	| (y,e')::l -> (if free_in y e then free_in x e' else false) || free_in_env x l e

let rec list_bind xs f =
    match xs with
    | [] -> []
    | x :: xs -> f x @ list_bind xs f
  ;;

let rec list_prod (f : 'a -> 'b -> 'c) (xs : 'a list) (ys : 'b list) : 'c list = match xs with
  | [] -> []
	| x :: xs' -> List.map (f x) ys @ list_prod f xs' ys

let join1 xs = match xs with
  | [x] -> x
	| _ -> S.Join xs

let or1 xs = match xs with
  | [x] -> x
	| _ -> S.Or xs

let rec restrict p e = match e with
	| S.Cut (x, i, p1, p2) -> S.Cut (x, i, S.And [p; p1], S.And [p; p2])
	| S.Tuple lst -> S.Tuple (List.map (restrict p) lst)
	| S.True -> p
	| S.False -> S.False
	| S.Or _ -> S.And [p; e]
	| S.And lst -> S.And (p :: lst)
	| S.Less (e1, e2) -> S.And [p; e]
	| S.Restrict (q, e') -> restrict (S.And [p; q]) e'
	| _ -> S.Restrict (p, e)

  (* The first step of evaluation is to evaluate to head-normal form
     because we want to get rid of local definitions and redexes. This
     causes a huge inefficiency because it may unnecessarily multiply
     repeat subexpressions, but computation of derivatives cannot handle
     general applications and local definitions. *)

	let binary_int (op : S.binary) : int -> int -> int = match op with
    | S.Plus -> (+)
    | S.Minus -> (-)
    | S.Times -> fun x y -> x * y
    | S.Quotient -> (/)

  let rec hnf' ?(free=false) env e : S.expr list =
    let alpha1 x env e =
      if free_in_env x env e then
	let x' = S.fresh_name (S.string_of_name x) in
	  x', join1 (hnf' ~free:true (Env.extend x (S.Var x') []) e)
      else
	 x, e
    in
    let alpha2 x env e1 e2 =
      if free_in_env x env e1 || free_in_env x env e2 then
	let x' = S.fresh_name (S.string_of_name x) in
	  x', join1 (hnf' ~free:true (Env.extend x (S.Var x') []) e1)
		  , join1 (hnf' ~free:true (Env.extend x (S.Var x') []) e2)
      else
	 x, e1, e2
    in
    let hnf = hnf' ~free in
      match e with
	| S.Var x ->
	    (try
	       [List.assoc x env]
	     with Not_found ->
	       if free then [S.Var x] else error ("Unknown variable " ^ S.string_of_name x))
	| (S.RealVar _ | S.Dyadic _ | S.Interval _ | S.True | S.False | S.TyExpr _ | S.Random _ ) -> [e]
	| S.Integer _ -> [e]
	| S.Cut (x, i, p1, p2) ->
	    let x', p1', p2' = alpha2 x env p1 p2 in
	    let env' = Env.extend x' (S.Var x') env in
	      [S.Cut (x', i, or1 (hnf env' p1'), or1 (hnf env' p2'))]
	| S.Binary (op, e1, e2) ->
		  list_bind (hnf env e1) (fun e1' ->
			List.map (fun e2' -> match e1', e2' with
			  | S.Integer i1, S.Integer i2 -> S.Integer (binary_int op i1 i2)
				| _ -> S.Binary (op, e1', e2'))
			(hnf env e2))
	| S.Unary (op, e) ->
	   List.map (fun e' -> S.Unary (op, e')) (hnf env e)
	| S.Power (e, k) ->
		 List.map (fun e' -> S.Power (e', k )) (hnf env e)
	| S.Proj (e, k) -> List.map (fun e' ->
	    (match e' with
	       | S.Tuple _ as e' -> A.proj e' k
	       | e' -> S.Proj (e', k))
	    ) (hnf env e)
	| S.Less (e1, e2) ->
		  list_bind (hnf env e1) (fun e1' ->
			match e1' with
			| S.Cut (x, i, p1, p2) ->
			      hnf env (S.App (S.Lambda (x, S.Ty_Real, p2), e2))
			| _ ->
				list_bind (hnf env e2) (fun e2' ->
					match e2' with
					| S.Cut (x, i, p1, p2) ->
								hnf env (S.App (S.Lambda (x, S.Ty_Real, p1), e1'))
					| _ -> [S.Less (e1', e2')]
				)
			)
	| S.Restrict (e1, e2) ->
	    List.map (restrict (or1 (hnf env e1))) (hnf env e2)
	| S.And lst -> (match (List.map (hnf env) lst) with
	    | [] -> [S.True]
			| xs -> [S.And (List.map or1 xs)])
  | S.Or lst -> [or1 (list_bind lst (hnf env))]
	| S.Join lst -> list_bind lst (hnf env)
	| S.Tuple lst -> List.map (fun e -> S.Tuple e) (List.fold_right
	    (fun e (acc : S.expr list list) -> list_prod (fun x xs -> x :: xs) (hnf env e) acc)
			lst
			[[]]
			)
	| S.Lambda (x, ty, e) ->
	  let x',e' = alpha1 x env e in
	    [S.Lambda (x', ty, join1 (hnf (Env.extend x' (S.Var x') env) e'))]
	| S.Exists (x, i, e) ->
	  let x',e' = alpha1 x env e in
	    [S.Exists (x', i, or1 (hnf (Env.extend x' (S.Var x') env) e'))]
	| S.Forall (x, i, e) ->
	  let x',e' = alpha1 x env e in
	    [S.Forall (x', i, or1 (hnf (Env.extend x' (S.Var x') env) e'))]
	| S.Integral (x, i, e) ->
	  let x',e' = alpha1 x env e in
	    [S.Integral (x', i, join1 (hnf (Env.extend x' (S.Var x') env) e'))]
	| S.App (e1, e2)  ->
      list_bind (hnf env e2) (fun e2' ->
		  list_bind (hnf env e1) (fun e1' -> match e1' with
			  | S.Lambda (x, ty, e) ->
				    let x',e' = alpha1 x env e in
		        hnf (Env.extend x' e2' env) e'
		    | e1' ->
		      [S.App (e1', e2')]
			)
			)
	| S.Let (x, e1, e2) ->
	    list_bind (hnf env e1) (fun e1' ->
			  hnf (Env.extend x e1' env) e2
			)
	| S.RandomF e ->
	   List.map (function
		   | S.Integer n -> S.Random (n, ref (0, D.zero, D.new_rand_state n))
			 | e' -> S.RandomF e'
			 ) (hnf env e)

let hnf ?(free=false) env e = join1 (hnf' ~free env e)

  (* The function [refine k prec env e] performs one step of evaluation
     of expression [e] in environment [env], using precision [prec] to
     compute arithmetical expressions. This is used by [eval] below to
     make progress.  The counter [k] tells which successive refinement
     this is.

     We need to be able to refine expressions which contain free
     variables (in order to refine cuts and quantifiers). For this
     purpose we have a special expression [RealVar (x,i)] which denotes
     free variable [x] ranging over interval [i].
  *)

	exception Break1 of S.expr

  let rec refine k prec env e =
    let refn = refine k prec env in
	match e with
	  | S.Var x -> refn (Env.get x env)
	  | S.RealVar (x, _) -> S.Var x
	  | S.Dyadic _ -> e
		| S.Integer _ -> e
	  | S.Interval _ -> e
		| S.TyExpr _ -> e
	  | S.Cut (x, i, p1, p2) -> begin
	      let prec = make_prec prec i in
		(* To refine a cut [Cut(x,i,p1,p2)] we try to make the
		   interval [i] smaller and refine [p1] and [p2]. *)
	      let a = I.lower i in
	      let b = I.upper i in
		(* Bisection *)
	      let m1, m2 = I.thirds prec k i in
	      let a' = (if A.lower prec (Env.extend x (S.Dyadic m1) env) p1 = S.True then m1 else a) in
	      let b' = (if A.lower prec (Env.extend x (S.Dyadic m2) env) p2 = S.True then m2 else b) in

	      let j = I.make a' b' in
	      	(* Newton's method *)
	      let r2 = N.estimate_true' k prec env x j p1 in
	      let s2 = N.estimate_true' k prec env x j p2 in
        let a'' = D.max a' (R.supremum r2) in
	      let b'' = D.min b' (R.infimum  s2) in
	      match D.cmp a'' b'' with
		  | `less ->
		      (* The new interval *)
		    let l = I.make a'' b'' in
		    let env' = Env.extend x (S.RealVar (x, l)) env in
		    let q1 = refine k prec env' p1 in
		    let q2 = refine k prec env' p2 in
(*		    print_endline ("Cut: " ^ (S.string_of_name x) ^ ":" ^ (I.to_string i) ^ ":" ^ (I.to_string j) ^ (I.to_string l) ^ (S.string_of_expr q1) ^ (S.string_of_expr q2));*)
		      S.Cut (x, l, q1, q2)
		  | `equal ->
		      (* We found an exact value *)
		    S.Dyadic a''
		  | `greater ->
				let l = I.make a'' b'' in
			  print_endline (I.to_string l);
				print_endline (R.to_string r2 ^ " || " ^ R.to_string s2 );
			  print_endline "greater";
				S.Interval l
		      (* We have a backwards cut. Do nothing. Someone should think
			 whether this is ok. It would be nice if cuts could be
			 overlapping, but I have not thought whether this would break
			 anything else.
		      *)
	    end
	  | S.Binary (op, e1, e2) -> S.Binary (op, refn e1, refn e2)
	  | S.Unary (op, e) -> S.Unary (op, refn e)
	  | S.Power (e, k) -> S.Power (refn e, k)
	  | S.True -> S.True
	  | S.False -> S.False
		| S.Restrict (e1, e2) -> let e2' = refn e2 in (match refn e1 with
		   | S.True -> e2'
			 | e1' -> S.Restrict (e1', e2')
		   )
	  | S.Less (e1, e2) -> S.Less (refn e1, refn e2)
		| S.Join lst -> join1 (List.map refn lst)
	  | S.And lst -> A.fold_and refn lst
	  | S.Or lst -> A.fold_or refn lst
	  | S.Exists (x, i, p) ->
	      let prec = make_prec prec i in
	      let q = refine k prec (Env.extend x (S.RealVar (x, i)) env) p in
	    (*  let (a1,b1) = N.estimate k prec env x i q in
              if R.is_inhabited b1 then S.True
              else
                (if R.is_inhabited a1 then
                  let lst = R.to_closed_intervals (R.closure (R.intersection (R.of_interval i) (R.complement a1))) in
		      A.fold_or (fun i -> make_exists x i q) lst
                else
		  let i1,i2 = I.split prec 1 i in
	              A.fold_or (fun i -> make_exists x i q) [i1; i2])*)
	      let i1, i2 = I.split prec 1 i in
		(* Newton's method *)
	      let (a1, b1) = N.estimate k prec env x i1 q in

(*	      print_endline ("Exists: " ^ (S.string_of_name x) ^ ":" ^ (I.to_string i) ^ ":" ^ (R.to_string a1) ^ (R.to_string b1));*)
	      if R.is_inhabited b1 then
		(* We could collect [b1] as a witness here. *)
		S.True
	      else
		let (a2, b2) = N.estimate k prec env x i2 q in
(*		  print_endline ("Exists: " ^ (S.string_of_name x) ^ ":" ^ (I.to_string i) ^ ":" ^ (R.to_string a2) ^ (R.to_string b2));*)
		  if R.is_inhabited b2 then
		    (* We could collect [b2] as a witness here. *)
		    S.True
		  else
		    let lst1 = R.to_closed_intervals
		      (R.closure
			 (R.intersection
			    (R.of_interval i1)
			    (R.complement a1)))
		    in
		    let lst2 = R.to_closed_intervals
		      (R.closure
			 (R.intersection
			    (R.of_interval i2)
			    (R.complement a2)))
		    in
		      A.fold_or (fun i -> make_exists x i q) (lst1 @ lst2)

	      (*A.fold_or (fun i -> make_exists x i q) [i1; i2]*)

	  | S.Forall (x, i, p) ->
	      let prec = make_prec prec i in
	      let q = refine k prec (Env.extend x (S.RealVar (x, i)) env) p in
(*      let (a1, b1) = N.estimate k prec env x i q in
	      if R.is_inhabited a1 then
		(* We could take [a1] as witness for quantifier being false. *)
		S.False
	      else
                (if R.is_inhabited b1 then
 		    let lst = R.to_closed_intervals (R.closure (R.intersection (R.of_interval i) (R.complement b1))) in
		      A.fold_and (fun i -> make_forall x i q) lst
		else
	       	  let i1, i2 = I.split prec 1 i in
              	    A.fold_and (fun i -> make_forall x i q) [i1; i2])*)

	       let i1, i2 = I.split prec 1 i in
		(* Newton's method *)
              let (a1, b1) = N.estimate k prec env x i1 q in
(*	      print_endline ("Forall: " ^ (S.string_of_name x) ^ ":" ^ (I.to_string i) ^ ":" ^ (R.to_string a1) ^ (R.to_string b1));*)
	      if R.is_inhabited a1 then
		(* We could take [a1] as witness for quantifier being false. *)
		S.False
	      else
		let (a2, b2) = N.estimate k prec env x i2 q in
(*		print_endline ("Forall: " ^ (S.string_of_name x) ^ ":" ^ (I.to_string i) ^ ":" ^ (R.to_string a2) ^ (R.to_string b2));*)
		  if R.is_inhabited a2 then
		    (* We could take [a2] as witness for quantifier being false. *)
		    S.False
		  else
		    let lst1 = R.to_closed_intervals
		      (R.closure
			 (R.intersection
			    (R.of_interval i1)
			    (R.complement b1)))
		    in
		    let lst2 = R.to_closed_intervals
		      (R.closure
			 (R.intersection
			    (R.of_interval i2)
			    (R.complement b2)))
		    in
		      A.fold_and (fun i -> make_forall x i q) (lst1 @lst2)

              (*A.fold_and (fun i -> make_forall x i q) [i1; i2]*)
	  | S.Let (x, e1, e2) ->
	      refine k prec (Env.extend x (refn e1) env) e2
	  | S.Tuple xs -> S.Tuple (List.map refn xs)
	  | S.Proj (e, k) ->
	      (match refn e with
		 | S.Tuple lst ->
		     (try
			refn (List.nth lst k)
		      with Failure _ -> error "Tuple too short")
		 | e -> S.Proj (e, k))
	  | S.Lambda _ -> e
		| S.RandomF _ -> assert false
	  | S.App (e1, e2) ->
	      (match refn e1 with
		 | S.Lambda (x, _, e) -> refine k prec (Env.extend x (refn e2) env) e
		 | e -> S.App (e, e2))
		| S.Integral (x, i, p) ->
	      let prec = make_prec prec i in
	      let q = refine k prec (Env.extend x (S.RealVar (x, i)) env) p in
	      let (i1, i2) = I.split prec 1 i in S.Binary (S.Plus, S.Integral (x, i1, q), S.Integral (x, i2, q))
		| S.Random (n, r) ->
		    let (prec', x, s) = !r in
				let prec_r = prec - prec' in
				(if prec_r >= 1 then
					let rand_val = D.rand prec_r s in
					(* print_endline ("prec'=" ^ string_of_int prec');
					print_endline ("prec_r=" ^ string_of_int prec_r);
					print_endline ("random value: " ^ D.to_string rand_val); *)
					let x' = D.add ~prec:(prec' + prec_r) ~round:D.down x (D.shift ~prec:(prec' + prec_r) ~round:D.down rand_val (-prec')) in
					r := (prec' + prec_r, x', s));
				S.Random (n, r)


	type 'a step_result =
    | Step_Done of 'a
    | Step_Go of 'a * int

	let map_step_result f (x, sx) = (f x, match sx with
	  | Step_Done e -> Step_Done (f e)
		| Step_Go (e, p) -> Step_Go (f e, p)
		)


	let pair_step_result (x : 'a * 'a step_result) (y : 'b * 'b step_result) : ('a * 'b) * ('a * 'b) step_result =
	  let (e1, sx) = x in let (e2, sy) = y in
		((e1, e2),
	   match sx, sy with
	   | Step_Done e1', Step_Done e2' -> Step_Done (e1', e2')
	   | Step_Done e1', Step_Go (e2', p) -> Step_Go ((e1', e2'), p)
		 | Step_Go (e1', p), Step_Done e2' -> Step_Go ((e1', e2'), p)
		 | Step_Go (e1, p1), Step_Go (e2, p2) -> Step_Go ((e1, e2), max p1 p2)
		)

	let rec collect_step_result (xs : ('a * 'a step_result) list) : ('a list) * ('a list) step_result = match xs with
	| [x] -> map_step_result (fun z -> [z]) x
	| x :: xs' -> map_step_result (fun (z, zs) -> z :: zs) (pair_step_result x (collect_step_result xs'))
	| [] -> assert false

  let rec step env e (p : int) =
	let prec = p in
	let al = A.lower prec env e in
	match al with
	  | S.True -> Step_Done al
		| S.Integer n -> Step_Done al
		| S.Interval i ->
					let w = (I.width 10 D.up i) in
				if D.lt w !target_precision || D.is_positive_infinity (I.lower i) || D.is_negative_infinity (I.upper i) then
					Step_Done al
				else
					Step_Go (S.Interval i, make_prec (p+3) (I.make D.zero !target_precision))
		(* | S.Tuple [S.True; e2] -> Step_Done (S.Tuple [S.True; e2])
		| S.Tuple [e1; S.True] -> Step_Done (S.Tuple [e1; S.True]) *)
	  | _ -> let au = A.upper prec env e in
		  match au with
			| S.False -> Step_Done S.False
			(* | S.Tuple [S.False; S.False] -> Step_Done (S.Tuple [S.False; S.False]) *)
      | _ ->
	match e with
	| S.Var _ | S.RealVar _
	| S.Less _ | S.And _ | S.Or _ | S.Exists _ | S.Forall _
	| S.Let _ | S.Proj _ | S.App _ ->
	    Step_Go (al, p + 1)
	| S.Integer _
	| S.RandomF _
	| S.Binary _ | S.Unary _ | S.Power _ | S.Cut _ | S.Integral _ | S.Random _ -> assert false
	| S.TyExpr _
	| S.Dyadic _ | S.Interval _ | S.True | S.Lambda _ -> Step_Done e
	| S.Restrict _ -> Step_Go (al, p + 1)
	| S.Join _ -> assert false (* Need to fix this *)
	| S.Tuple lst -> snd (map_step_result (fun x -> S.Tuple x) (collect_step_result (List.map (fun e' -> (e', step env e' p)) lst)))
	| S.False -> Step_Done S.False

  let eval_bounded nloop env e =
    let rec loop k p e =
		  if k >= nloop then e
			  else
	    match step env e p with
			| Step_Done e' -> e'
			| Step_Go (a, p') -> loop (k+1) p' (refine k p env e)
    in
      loop 1 nloop (hnf env e);;


  (** [eval prec env e] evaluates expression [e] in environment [env] by
      repeatedly calling [refine]. It increases precision at each step,
      although we should do something more intelligent about that (not
      all subexpressions of [e] need the same precision). The argument
      [trace] determines whether debugging information should be printed
      out. *)
  let eval print_steps trace env e =
    let rec loop k p e =
      if trace then
	begin
	  print_endline ("--------------------------------------------------\n" ^
			   "Iteration: " ^ string_of_int k ^ "\n" ^
			   S.string_of_expr e ^ "\n" ^
			   "Press Enter to continue "
			) ;
	  ignore (read_line ())
	end ;
	    match step env e p with
			| Step_Done e' -> e'
			| Step_Go (a, p') ->
			  (if print_steps then print_endline (S.string_of_expr a));
			  loop (k+1) p' (refine k p env e)
    in
      loop 1 32 (hnf env e)
end;;

