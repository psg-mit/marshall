module Make = functor (D : Dyadic.DYADIC) ->
struct

  module I = Interval.Make(D)
  module S = Syntax.Make(D)
  module R = Region.Make(D)
  module A = Approximate.Make(D)
  module Env = Environment.Make(D)

  (* \subsection{Newton's method} *)

  (* This section is not finished because we have to sort out problems which
     are caused by appearance of back-to-front intervals. *)




  let estimate_endpoint prec round x y d =
        match D.sgn d with
  	| `negative ->
  	    let b' = D.sub ~prec ~round x (D.div ~prec ~round:(D.anti round) y d) in
  		R.open_left_ray b'
  	| `zero ->
  	    (match D.sgn y with
  	       | `negative | `zero -> R.empty
  	       | `positive -> R.real_line)
  	| `positive ->
  	    let a' = D.sub ~prec ~round:(D.anti round) x (D.div ~prec ~round y d) in
  		R.open_right_ray a'

  (* The function [estimate_positive env x i e] returns a set such that
     in environment [env] the expression [e] with free variable [x]
     ranging over interval [i] we have [0 < e] everywhere on the set. It
     uses interval Newton's method.
  *)

  let estimate_positive prec env x i e =
    (* For infinite intervals we give up. We could try to do something
       more intelligent, such as computing the derivative at infinity
       (using a suitable transformation which moves infinity to a finite
       point). *)
    if not (I.proper i) then
      R.empty
    else
      let x1 = I.lower i in
      let x2 = I.upper i in
      let y1 = I.lower (A.get_interval (A.lower prec (Env.extend x (S.Dyadic x1) env) e)) in
      let y2 = I.lower (A.get_interval (A.lower prec (Env.extend x (S.Dyadic x2) env) e)) in
      let lif = A.get_interval (A.lower prec (Env.extend x (S.Interval i) env) (A.diff x e)) in  (* Lifschitz constant as an interval *)
      (* print_endline ("estimate_positive:" ^ S.string_of_expr (diff x e) ^ " | lif: " ^ I.to_string lif ^ "| i: " ^ I.to_string i); *)
	(R.union
	  (estimate_endpoint prec D.down x1 y1 (I.lower lif)) (* estimate at i.lower *)
	  (estimate_endpoint prec D.down x2 y2 (I.upper lif)))  (* estimate at i.upper*)

  (* The function [estimate_non_positive env x i e] returns a
     set such that in environment [env] the expression [e] with
     free variable [x] ranging over interval [i] is guaranteed to be
     non-positive everywhere on the complement of the set.
  *)

  let estimate_non_positive k prec env x i e =
    (* For infinite intervals we give up. We could try to do something
       more intelligent, such as computing the derivative at infinity
       (using a suitable transformation which moves infinity to a finite
       point). *)
    if not (I.proper i) then
      R.real_line
    else
      let diffexpr = A.diff x e in
      let x1 = I.lower i in
      let x2 = I.upper i in
      let y1 = I.lower (A.get_interval (A.upper prec (Env.extend x (S.Dyadic x1) env) e)) in
      let y2 = I.lower (A.get_interval (A.upper prec (Env.extend x (S.Dyadic x2) env) e)) in
      let lif = A.get_interval (A.upper prec (Env.extend x (S.Interval (I.flip i)) env) diffexpr) in  (* Lifschitz constant as an interval *)
      (* print_endline ("estimate_non_positive:" ^ S.string_of_expr diffexpr ^ " | lif: " ^ I.to_string lif); *)
      if not (I.proper (I.flip lif)) then R.real_line else
	  R.union (estimate_endpoint prec D.up x1 y1 (I.lower lif))
		 (estimate_endpoint prec D.up x2 y2 (I.upper lif))


  (* The function [estimate prec env i x p] returns a pair of sets [(a,b)]
     such that in environment [env] the proposition [p] with free
     variable [x] ranging over interval [i] fails everywhere on [a] and
     holds everywhere on [b].
  *)

  let rec estimate_true k prec env x i = function
    | S.True -> R.real_line
    | S.False -> R.empty
    | S.And lst ->
        List.fold_left
  	(fun r p -> R.intersection r (estimate_true k prec env x i p))
  	R.real_line
  	lst
    | S.Or lst ->
        List.fold_left
  	(fun r p -> R.union r (estimate_true k prec env x i p))
  	R.empty
  	lst
    | S.Less (e1, e2) -> (match e1, e2 with
      (* Quick special cases to cut down a Dedekind cut
         Useful for my ray  tracing example
      *)
      | S.Var x', S.Dyadic d when x = x' -> R.open_left_ray d
      | S.Dyadic d, S.Var x' when x = x' -> R.open_right_ray d
      | _ -> estimate_positive prec env x i (S.Binary (S.Minus, e2, e1)))
    | S.Exists (y, j, p) ->
        estimate_true k prec (Env.extend y (S.Dyadic (I.midpoint prec k j)) env) x i p
    | S.Forall (y, j, p) ->
        estimate_true k prec (Env.extend y (S.Interval j) env) x i p
    | S.Join lst -> estimate_true k prec env x i (S.Or lst)
    | e -> failwith ("Cannot estimate " ^ S.string_of_expr e)

  let rec estimate_false k prec env x i = function
    | S.True -> R.real_line
    | S.False -> R.empty
    | S.And lst ->
        List.fold_left
  	(fun r p -> R.intersection r (estimate_false k prec env x i p))
  	R.real_line
  	lst
    | S.Or lst ->
        List.fold_left
  	(fun r p -> R.union r (estimate_false k prec env x i p))
  	R.empty
  	lst
   (* | S.Less (e1, e2) -> estimate_non_positive prec env x i (S.Binary (S.Minus, e2, e1))*)
    | S.Less (e1, e2) ->
       let r = estimate_non_positive k prec env x i (S.Binary (S.Minus, e2, e1)) in
       (* print_endline ("Estimated " ^ S.string_of_name x ^ " on " ^ I.to_string i ^ " with " ^ Env.string_of_env env ^ " | " ^ S.string_of_expr (S.Less (e1, e2)) ^ " to be false on " ^ R.to_string r ^ "\n"); *)
	r
    | S.Exists (y, j, p) ->
        estimate_false k prec (Env.extend y (S.Interval (I.flip j)) env) x i p
    | S.Forall (y, j, p) ->
        estimate_false k prec (Env.extend y (S.Dyadic (I.midpoint prec k j)) env) x i p
    | S.Join lst -> estimate_false k prec env x i (S.Or lst)
    | e -> failwith ("Cannot estimate " ^ S.string_of_expr e)

  let estimate_true' k prec env x i p =
    R.intersection (estimate_true k prec env x i p) (R.of_interval i)

  let estimate_false' k prec env x i p =
    R.intersection (R.complement (estimate_false k prec env x i p)) (R.of_interval i)

  let estimate k prec env x i p =
    (estimate_false' k prec env x i p, estimate_true' k prec env x i p)

end;;

