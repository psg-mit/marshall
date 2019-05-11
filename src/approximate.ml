module Make = functor (D : Dyadic.DYADIC) ->
struct

  module I = Interval.Make(D)
  module Env = Environment.Make(D)
  module S = Syntax.Make(D)

  let error = Message.runtime_error

	  (* Does [x] occur freely in [e]? *)
  let rec free x = function
    | S.Var y -> x <> y
    | S.RealVar (y, _) -> x <> y
    | S.Dyadic _
    | S.Integer _
    | S.Interval _
		| S.TyExpr _
		| S.Random _
    | S.True
    | S.False -> true
    | S.Cut (y, _, p1, p2) -> x = y || (free x p1 && free x p2)
    | S.Binary (_, e1, e2)
    | S.Less (e1, e2)
    | S.Restrict (e1, e2)
    | S.App (e1, e2)  -> free x e1 && free x e2
    | S.Unary (_, e)
    | S.Power (e, _)
    | S.RandomF e
    | S.Proj (e, _) -> free x e
    | S.And lst
    | S.Or lst
    | S.Join lst
    | S.Tuple lst -> List.for_all (free x) lst
		| S.Integral (y, _, e)
    | S.Lambda (y, _, e)
    | S.Exists (y, _, e)
    | S.Forall (y, _, e) -> x = y || free x e
    | S.Let (y, e1, e2) -> free x e1 && (x = y || free x e2)

  (* Suppose [e] is an expression in environment [env] with a free
     variable [x]. Then [e] as a function of [x] maps a real [x] to an
     interval $[e_1(x), e_2(x)]$.

     For estimation of inequalities we need to compute upper and lower
     Lipschitz constants for $e_1(x)$ when $x$ ranges over a given
     interval. This we do by symbolic differentiation.

     We assume that the expressions are in head
     normal form and of type real. In particular, this means we are
     never going to see a lambda abstraction, a tuple, a projection, or
     a local definition.
  *)

  let zero = S.Dyadic D.zero
  let one = S.Dyadic D.one

  let rec diff x = function
    | S.Var y -> if x = y then one else zero
    | S.RealVar (y, _) -> if x = y then one else zero
    | S.Integer _
    | S.Dyadic _ -> zero
    | S.Interval _ -> zero
    | S.RandomF _
    | S.Random _ -> zero
    | S.Restrict (e1, e2) -> diff x e2 (* Is this okay? *)
    | S.Cut (y, i, p1, p2) ->
        if x = y || S.(free x p1 && free x p2) then
  	zero
        else
  	S.Interval I.bottom
    | S.Binary (S.Plus, e1, e2) -> S.Binary (S.Plus, diff x e1, diff x e2)
    | S.Binary (S.Minus, e1, e2) -> S.Binary (S.Minus, diff x e1, diff x e2)
    | S.Binary (S.Times, e1, e2) ->
        S.Binary (S.Plus,
  	      S.Binary (S.Times, diff x e1, e2),
  	      S.Binary (S.Times, e1, diff x e2))
    | S.Binary (S.Quotient, e1, e2) ->
        S.Binary (S.Quotient,
  	      S.Binary (S.Minus,
  		      S.Binary (S.Times, diff x e1, e2),
  		      S.Binary (S.Times, e1, diff x e2)),
  	      S.Power (e2, 2))
    | S.Unary (S.Opposite, e) -> S.Unary (S.Opposite, diff x e)
    | S.Unary (S.Inverse, e) -> S.Binary (S.Quotient, diff x e, S.Power (e, 2))
    | S.Unary (S.Exp, e) -> S.Binary (S.Times, S.Unary (S.Exp, e), diff x e)
    (* For some reason, Newton seems to be broken for sine, at least trying to compute pi that way *)
    | S.Unary (S.Sin, e) -> S.Binary (S.Times, S.Unary (S.Cos, e), diff x e)
    | S.Unary (S.Cos, e) -> S.Binary (S.Times, S.Unary (S.Opposite, S.Unary (S.Sin, e)), diff x e)
    | S.Unary (S.Erf, e) -> S.Interval I.bottom (* Could be improved *)
    | S.Power (e, 0) -> zero
    | S.Power (e, 1) -> diff x e
    | S.Power (e, k) ->
        S.Binary (S.Times,
  	      S.Dyadic (D.of_int ~round:D.down k),
  	      S.Binary (S.Times,
  		      S.Power (e, k-1),
  		      diff x e))
		| S.Integral (y, i, e) ->
		  (* Ideally, we'd use FTC, but this is conservative *)
				if x = y || S.(free x e)
				  then zero
          else S.Interval I.bottom
    | S.True
    | S.False
    | S.Less _
    | S.And _
    | S.Or _
    | S.Exists _
    | S.Forall _ -> Error.runtime "Cannot differentiate a proposition"
    | S.Join _ -> failwith "Cannot differentiate a join"
		| S.TyExpr _ -> failwith "Cannot differentiate a type"
    | S.Let (y, e1, e2) -> Error.runtime "Cannot differentiate a local definition"
    | S.Tuple _ -> failwith "Cannot differentiate a tuple"
    | S.Proj (_, _) -> failwith "Cannot differentiate a projection"
    | S.Lambda (x, ty, e) -> failwith "Cannot differentiate an abstraction"
    | S.App (e1, e2) -> failwith "Cannot differentiate a redex"

  (* \subsection{Auxiliary functions} *)

  (* Get the interval approximation of a simple numerical expression. *)

  let rec get_interval = function
    | S.Interval i -> i
    | S.Dyadic q -> I.of_dyadic q
    | S.Cut (_, i, _, _) -> i
		| S.Join lst ->
		   List.fold_left (fun acc e -> I.bin_or acc (get_interval e)) I.bottom lst
    | e -> error ("Numerical constant expected but got " ^ S.string_of_expr e)

  (* Get the bound variable and the matrix of an abstraction. *)

  let get_lambda = function
    | S.Lambda (x, _, e) -> x, e
    | _ -> error "Function expected"

  (* Project from a tuple. *)

  let proj e k =
    match e with
      | S.Tuple lst ->
         (try
            List.nth lst k
          with Failure _ -> error "Tuple too short")
      | _ -> error "Tuple expected"

  (* Apply a binary artithmetical operator with precision [prec]. The
     rounding mode, which is [Dyadic.down] or [Dyadic.up] tells whether
     we want a lower or an upper approximant. *)

  let bin_apply ~prec ~round op i1 i2 =
    match op with
      | S.Plus -> I.add ~prec ~round i1 i2
      | S.Minus -> I.sub ~prec ~round i1 i2
      | S.Times -> I.mul ~prec ~round i1 i2
      | S.Quotient -> I.div ~prec ~round i1 i2

  (* Apply a unary operator, see [bin_apply] for explanation of [prec]
     and [round]. *)

  let unary_apply ~prec ~round op i =
    match op with
      | S.Opposite -> I.neg ~prec ~round i
      | S.Inverse -> I.inv ~prec ~round i
	    | S.Exp -> I.exp ~prec ~round i
			| S.Sin -> I.sin ~prec ~round i
			| S.Cos -> I.cos ~prec ~round i
      | S.Erf -> I.erf ~prec ~round i

  (* [Break] is used to shortcircuit evaluation of conjunctions and
     disjunctions. *)

  exception Break
	exception Break1 of S.expr

  (* [fold_and f [x1,...,xn]] constructs the conjunction [And [f x1;
     ..., f xn]]. It throws out [True]'s and shortcircuits on
     [False]. *)

  let fold_and f lst =
    let rec fold acc = function
      | [] -> acc
      | p::ps ->
	  (match f p with
	     | S.True -> fold acc ps
	     | S.False -> raise Break
	     | q -> fold (q::acc) ps)
    in
      try
	match fold [] lst with
	  | [] -> S.True
	  | lst -> S.And (List.rev lst)
      with Break -> S.False

  (* [fold_or f [x1,...,xn]] constructs the disjunction [Or [f x1;
     ..., f xn]]. It throws out [False]'s and shortcircuits on
     [True]. *)

  let fold_or f lst =
    let rec fold acc = function
      | [] -> acc
      | p::ps ->
	  (match f p with
	     | S.True -> raise Break
	     | S.False -> fold acc ps
	     | q -> fold (q::acc) ps)
    in
      try
	match fold [] lst with
	  | [] -> S.False
	  | lst -> S.Or (List.rev lst)
      with Break -> S.True


  (* \subsection{Approximants} *)

  (* [lower prec env e] computes the lower approximant of [e] in
     environment [env], computing arithmetical expressions with precision
     [prec]. *)

  let rec lower prec env e =
    let approx = lower prec env in
      match e with
	| S.Var x -> approx (Env.get x env)
	| S.RealVar (_, i) -> S.Interval i
	| S.Dyadic q -> S.Interval (I.of_dyadic q)
  | S.Integer _ -> e
	| S.Interval _ as e -> e
	| S.Cut (_, i, _, _) -> S.Interval i
	| S.Random (_, r) -> let (p, d, _) = !r in
	  let d' = D.add ~prec ~round:D.up d (D.make_int ~prec ~round:D.up 1 (-p)) in
		S.Interval (I.make d d')
	| S.Binary (op, e1, e2) ->
	    let i1 = get_interval (approx e1) in
	    let i2 = get_interval (approx e2) in
	      S.Interval (bin_apply ~prec ~round:D.down op i1 i2)
	| S.Unary (op, e) ->
	    let i = get_interval (approx e) in
	      S.Interval (unary_apply ~prec ~round:D.down op i)
	| S.Integral (x, i, e) ->
	    (* Using  the derivative doesn't work great, yet *)
	    (* let deriv = get_interval (lower prec (Env.extend x (S.Interval i) env) (diff x e)) in
			let xmid = I.midpoint prec 1 i in
			let ymid = get_interval (lower prec (Env.extend x (S.Dyadic xmid) env) e) in
			let x1mid = I.sub ~prec ~round:D.down (I.of_dyadic (I.lower i)) (I.of_dyadic xmid) in
			let x2mid = I.sub ~prec ~round:D.down (I.of_dyadic (I.upper i)) (I.of_dyadic xmid) in
			let y1 = I.add ~prec ~round:D.down ymid (I.mul ~prec ~round:D.down x1mid deriv) in
			let y2 = I.add ~prec ~round:D.down ymid (I.mul ~prec ~round:D.down x2mid deriv) in
			let yavg = I.div ~prec ~round:D.down (I.add ~prec ~round:D.down y1 y2) (I.of_dyadic (D.two)) in
			let result = I.mul ~prec ~round:D.down yavg (I.iwidth ~prec ~round:D.down i)
			in if I.proper result then S.Interval result
			else *)
	    let ie = get_interval (lower prec (Env.extend x (S.Interval i) env) e) in
		    S.Interval (I.mul ~prec ~round:D.down (I.of_dyadic (I.width ~prec ~round:D.down i)) ie)
	| S.Power (e, k) ->
	    let i = get_interval (approx e) in
	      S.Interval (I.pow ~prec ~round:D.down i k)
	| S.True -> S.True
	| S.False -> S.False
	| S.Less (e1, e2) ->
	    let i1 = get_interval (approx e1) in
	    let i2 = get_interval (approx e2) in
	      if D.lt (I.upper i1) (I.lower i2) then
		S.True
	      else
		S.False
	| S.And lst -> fold_and approx lst
	| S.Or lst -> fold_or approx lst
  | S.Join [] -> assert false
  | S.Join (x :: xs) -> approx x (* Is this right? *)
	| S.Exists (x, s, e) ->
	    let m = S.Dyadic (I.midpoint prec 1 s) in
	      lower prec (Env.extend x m env) e
	| S.Forall (x, i, e) ->
	    lower prec (Env.extend x (S.Interval i) env) e
	| S.Let (x, e1, e2) ->
	    lower prec (Env.extend x (approx e1) env) e2
	| S.Tuple lst -> S.Tuple (List.map approx lst)
	| S.Proj (e, k) -> proj (approx e) k
	| S.TyExpr _ -> e
	| S.Lambda _ as e -> e
	| S.App (e1, e2) ->
	    let x, e = get_lambda (approx e1) in
	      lower prec (Env.extend x (approx e2) env) e
	| S.Restrict (e1, e2) -> (* currently assuming we must have a number *)
	    S.Interval I.bottom
  | S.RandomF e -> assert false



  (* Function [upper prec env e] computes the upper approximant of [e]
     in environment [env], computing arithmetical expressions with
     precision [prec]. *)

  let rec upper prec env e =
    let approx = upper prec env in
      match e with
	| S.Var x -> approx (Env.get x env)
	| S.RealVar (_, i) -> S.Interval (I.flip i)
	| S.Dyadic q -> S.Interval (I.of_dyadic q)
  | S.Integer _ -> e
	| S.Interval _ as e -> e
	| S.Cut (_, i, _, _) -> S.Interval (I.flip i)
	| S.Random (_, r) -> let (p, d, _) = !r in
	  let d' = D.add ~prec ~round:D.up d (D.make_int ~prec ~round:D.up 1 (-p)) in
		S.Interval (I.make d' d)
	| S.Binary (op, e1, e2) ->
	    let i1 = get_interval (approx e1) in
	    let i2 = get_interval (approx e2) in
	      S.Interval (bin_apply ~prec ~round:D.up op i1 i2)
	| S.Unary (op, e) ->
	    let i = get_interval (approx e) in
	      S.Interval (unary_apply ~prec ~round:D.up op i)
	| S.Integral (x, i, e) ->
	    let ie = get_interval (upper prec (Env.extend x (S.Interval i) env) e) in
		    S.Interval (I.mul ~prec ~round:D.up (I.of_dyadic (I.width ~prec ~round:D.up i)) ie)
	| S.Power (e, k) ->
	    let i = get_interval (approx e) in
	      S.Interval (I.pow ~prec ~round:D.up i k)
	| S.True -> S.True
	| S.False -> S.False
	| S.Less (e1, e2) ->
	    let i1 = get_interval (approx e1) in
	    let i2 = get_interval (approx e2) in
	      if D.lt (I.upper i1) (I.lower i2) then
		S.True
	      else
		S.False
	| S.And lst -> fold_and approx lst
	| S.Or lst -> fold_or approx lst
  | S.Join [] -> assert false
  | S.Join (x :: xs) -> assert false (* need to think about what to do here *)
	| S.Exists (x, i, e) ->
	    let j = I.flip i in
	      upper prec (Env.extend x (S.Interval j) env) e
	| S.Forall (x, i, e) ->
	    let m = S.Dyadic (I.midpoint prec 1 i) in
	      upper prec (Env.extend x m env) e
	| S.Let (x, e1, e2) ->
	    upper prec (Env.extend x e1 env) e2
	| S.Tuple lst -> S.Tuple (List.map approx lst)
	| S.Proj (e, k) -> proj (approx e) k
	| S.TyExpr _ -> e
	| S.Lambda _ as e -> e
	| S.App (e1, e2) ->
	    let x, e = get_lambda (approx e1) in
	      upper prec (Env.extend x (approx e2) env) e
	| S.Restrict (e1, e2) -> (* currently assuming we must have a number *)
	    S.Interval I.top
  | S.RandomF e -> assert false


end;;
