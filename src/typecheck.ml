(* \section{Type checking (module [Typecheck])} *)

module Make = functor (D : Dyadic.DYADIC) ->
struct
  module I = Interval.Make(D)
  module S = Syntax.Make(D)
  open S

  let error = Message.typecheck_error

  let check_segment i =
    if not (I.forward i) then error "illegal interval"

  let check_compact_segment i =
    if not (I.proper i) then error "not a compact interval"

	let rec resolve ctx ty = match ty with
		| Ty_Var v -> (try List.assoc v ctx with Not_found -> ty)
		| Ty_Tuple ts -> Ty_Tuple (List.map (resolve ctx) ts)
		| Ty_Arrow (mv, t1, t2) ->
				let ctx' = match mv with
					| None -> ctx
					| Some v -> List.remove_assoc v ctx
				in Ty_Arrow (mv, resolve ctx t1, resolve ctx' t2)
		| _ -> ty

  let check_same ctx ty1 ty2 =
	  let ty1' = resolve ctx ty1 in
		let ty2' = resolve ctx ty2 in
	if ty1' <> ty2' then
		error (string_of_type ty1 ^ " expected but got " ^ string_of_type ty2)

  let rec ty_subst v t = function
    | Ty_Var v' -> if v = v' then t else Ty_Var v'
    | Ty_Arrow (mv, t1, t2) ->
	  let t1' = ty_subst v t t1 in
	  let t2' = match mv with
	    | None -> ty_subst v t t2
		| Some v' -> if v = v' then t2 else ty_subst v t t2
	  in Ty_Arrow (mv, t1', t2')
    | Ty_Tuple ts -> Ty_Tuple (List.map (ty_subst v t) ts)
	| ty -> ty

  (* [type_of ctx e] computes the type of expression [e] in context [ctx]. *)
  let rec type_of ctx = function
    | Var x ->
	(try
	   List.assoc x ctx
	 with Not_found -> error ("Unknown variable " ^ string_of_name x))
    | RealVar (x, _) ->
	error ("Typechecking encountered a real variable " ^ string_of_name x ^
		 ". This should not happen")
    | Dyadic _ -> Ty_Real
    | Interval _ -> Ty_Real
		| TyExpr _ -> Ty_Type
		| Random _ -> Ty_Real
    | Cut (x, i, p1, p2) ->
			check_segment i ;
			check ((x, Ty_Real)::ctx) Ty_Sigma p1 ;
			check ((x, Ty_Real)::ctx) Ty_Sigma p2 ;
			Ty_Real
    | Binary (_, e1, e2) ->
			check ctx Ty_Real e1 ;
			check ctx Ty_Real e2 ;
			Ty_Real
    | Restrict (e1, e2) ->
			check ctx Ty_Sigma e1 ;
			type_of ctx e2
    | Unary (_, e) ->
			check ctx Ty_Real e ;
			Ty_Real
    | Power (e, k) ->
			check ctx Ty_Real e ;
			Ty_Real
    | True -> Ty_Sigma
    | False -> Ty_Sigma
    | And lst
    | Or lst  -> List.iter (check ctx Ty_Sigma) lst ; Ty_Sigma
    | Join [] -> error "cannot infer type of empty join"
		| Join (e :: es) ->
			let ty = type_of ctx e in
			List.iter (check ctx ty) es;
			ty
    | Less (e1, e2) ->
			check ctx Ty_Real e1 ;
			check ctx Ty_Real e2 ;
			Ty_Sigma
		| MkBool (e1, e2) ->
			check ctx Ty_Sigma e1 ;
			check ctx Ty_Sigma e2 ;
			Ty_Bool
		| IsTrue e
		| IsFalse e ->
			check ctx Ty_Bool e ;
			Ty_Sigma
    | Exists (x, s, p) ->
			check_segment s ;
			check ((x,Ty_Real)::ctx) Ty_Sigma p ;
			Ty_Sigma
    | Forall (x, s, p) ->
			check_compact_segment s ;
			check ((x,Ty_Real)::ctx) Ty_Sigma p ;
			Ty_Sigma
    | Integral (x, s, p) ->
			check_compact_segment s ;
			check ((x,Ty_Real)::ctx) Ty_Real p ;
			Ty_Real
    | Let (x, e1, e2) ->
			let ty = type_of ctx e1 in
				type_of ((x,ty)::ctx) e2
    | Tuple lst -> Ty_Tuple (List.map (type_of ctx) lst)
    | Proj (e, k) ->
			(match resolve ctx (type_of ctx e) with
				| Ty_Tuple lst as ty ->
						(try List.nth lst k with Failure nth ->
					error ("Expected at least " ^ string_of_int k ^
						" components but got " ^ string_of_type ty))
				| ty -> error ("Expected a tuple but got " ^ string_of_type ty)
			)
    | Lambda (x, ty, e) -> (match ty with
	    | Ty_Type -> Ty_Arrow (Some x, Ty_Type, type_of ctx e)
			| _ -> Ty_Arrow (None, ty, type_of ((x,ty)::ctx) e))
    | App (e1, e2) ->
			(match resolve ctx (type_of ctx e1) with
				| Ty_Arrow (mv, ty1, ty2) -> (match mv with
						| None -> check ctx ty1 e2 ; ty2
					| Some v -> (match e2 with
						| TyExpr t -> ty_subst v t ty2
					| _ -> error ("Expected type argument but got " ^ string_of_expr e2)))
				| ty -> error ("Expected a function but got " ^ string_of_type ty))

  (* Does [e] have type [ty] in context [ctx]? *)
  and check ctx ty e =
    let ty' = type_of ctx e in
      check_same ctx ty ty'
end;;
