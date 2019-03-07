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

	let rec free_in y = function
		| S.Ty_Var x -> x = y
		| S.Ty_Arrow (mv, t1, t2) -> free_in y t1 || (match mv with
			| None -> free_in y t2
			| Some x -> x<>y && (free_in y t2)
		)
		| S.Ty_Tuple ts -> List.fold_left (fun p e -> p || free_in y e) false ts
		| S.Ty_App (f, x) -> free_in y f || free_in y x
		| S.Ty_Lam (x, e) -> x<>y && free_in y e
		| S.Ty_Sigma | S.Ty_Real | S.Ty_Int | S.Ty_Type -> false

	let rec free_in_env x env e =
      match env with
	| [] -> false
	| (y,e')::l -> (if free_in y e then free_in x e' else false) || free_in_env x l e

	let rec resolve tenv ty = match ty with
		| Ty_Var v -> (try List.assoc v tenv with Not_found -> ty)
		| Ty_Tuple ts -> Ty_Tuple (List.map (resolve tenv) ts)
		| Ty_Arrow (mv, t1, t2) -> let t1' = resolve tenv t1 in
			  (match mv with
					| None -> Ty_Arrow (None, t1', resolve tenv t2)
					| Some v -> let (v', t2') = alpha1 v tenv t2 in
					  Ty_Arrow (Some v', t1', resolve tenv t2')
				)
		| Ty_App (f, x) -> let x' = resolve tenv x in (match resolve tenv f with
		  | Ty_Lam (v, t) -> let v', t' = alpha1 v tenv t in resolve ((v', x') :: tenv) t'
			| f' -> Ty_App (f', x'))
		| Ty_Lam (v, t) -> let v', t' = alpha1 v tenv t in
			Ty_Lam (v', resolve tenv t')
    | Ty_Sigma | Ty_Real | Ty_Int | Ty_Type -> ty
	and alpha1 x tenv e =
					if free_in_env x tenv e then
						let x' = S.fresh_name (S.string_of_name x) in
						x', resolve [(x, Ty_Var x')] e
					else x, e

	let rec same_ty tenv ty1 ty2 =
		let ty1' = resolve tenv ty1 in
		let ty2' = resolve tenv ty2 in
		match ty1', ty2' with
		| Ty_Arrow (Some v1, a1, r1), Ty_Arrow (Some v2, a2, r2) -> same_ty tenv a1 a2 && (
		  let r2' = resolve [(v2, Ty_Var v1)] r2 in same_ty tenv r1 r2'
		  )
		| Ty_Arrow (None, a1, r1), Ty_Arrow (None, a2, r2) ->
		  same_ty tenv a1 a2 && same_ty tenv r1 r2
		| Ty_Tuple xs, Ty_Tuple ys ->
		  (try List.for_all2 (same_ty tenv) xs ys with Invalid_argument _ -> false)
		| Ty_Lam _, _
		| _,  Ty_Lam _
		| _, Ty_App _
		| Ty_App _, _ -> error "Should be no applications or lambdas remaining"
		| _ -> ty1' = ty2'

  let check_same tenv ty1 ty2 =
	  if not (same_ty tenv ty1 ty2)
		then error (string_of_type ty1 ^ " expected but got " ^ string_of_type ty2)

  (* XXX: Need to think about alpha conversion!! *)
  let rec ty_subst v t = function
	  | Ty_App (f, x) -> Ty_App (ty_subst v t f, ty_subst v t x)
		| Ty_Lam (v', x) -> Ty_Lam (v', if v = v' then x else ty_subst v t x)
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
  let rec type_of tenv ctx = function
    | Var x ->
	(try
	   List.assoc x ctx
	 with Not_found -> error ("Unknown variable " ^ string_of_name x))
    | RealVar (x, _) ->
	error ("Typechecking encountered a real variable " ^ string_of_name x ^
		 ". This should not happen")
    | Dyadic _ -> Ty_Real
    | Integer _ -> Ty_Int
    | Interval _ -> Ty_Real
		| TyExpr _ -> Ty_Type
		| Random _ -> Ty_Real
    | Cut (x, i, p1, p2) ->
			check_segment i ;
			check tenv ((x, Ty_Real)::ctx) Ty_Sigma p1 ;
			check tenv ((x, Ty_Real)::ctx) Ty_Sigma p2 ;
			Ty_Real
    | Binary (_, e1, e2) ->
		  let ty1 = resolve tenv (type_of tenv ctx e1) in
			(match ty1 with
			  | Ty_Real | Ty_Int ->
    			check tenv ctx ty1 e2 ;
			    ty1
				| _ -> error (string_of_type Ty_Real ^ " or " ^ string_of_type Ty_Int ^ " expected but got " ^ string_of_type ty1))
    | Restrict (e1, e2) ->
			check tenv ctx Ty_Sigma e1 ;
			type_of tenv ctx e2
    | Unary (_, e) ->
			check tenv ctx Ty_Real e ;
			Ty_Real
    | Power (e, k) ->
			check tenv ctx Ty_Real e ;
			Ty_Real
    | True -> Ty_Sigma
    | False -> Ty_Sigma
    | And lst
    | Or lst  -> List.iter (check tenv ctx Ty_Sigma) lst ; Ty_Sigma
    | Join [] -> error "cannot infer type of empty join"
		| Join (e :: es) ->
			let ty = type_of tenv ctx e in
			List.iter (check tenv ctx ty) es;
			ty
    | Less (e1, e2) ->
			check tenv ctx Ty_Real e1 ;
			check tenv ctx Ty_Real e2 ;
			Ty_Sigma
    | Exists (x, s, p) ->
			check_segment s ;
			check tenv ((x,Ty_Real)::ctx) Ty_Sigma p ;
			Ty_Sigma
    | Forall (x, s, p) ->
			check_compact_segment s ;
			check tenv ((x,Ty_Real)::ctx) Ty_Sigma p ;
			Ty_Sigma
    | Integral (x, s, p) ->
			check_compact_segment s ;
			check tenv ((x,Ty_Real)::ctx) Ty_Real p ;
			Ty_Real
    | Let (x, e1, e2) ->
			let ty = type_of tenv ctx e1 in
				type_of tenv ((x,ty)::ctx) e2
    | Tuple lst -> Ty_Tuple (List.map (type_of tenv ctx) lst)
    | Proj (e, k) ->
			(match resolve tenv (type_of tenv ctx e) with
				| Ty_Tuple lst as ty ->
						(try List.nth lst k with Failure nth ->
					error ("Expected at least " ^ string_of_int k ^
						" components but got " ^ string_of_type ty))
				| ty -> error ("Expected a tuple but got " ^ string_of_type ty)
			)
    | Lambda (x, ty, e) -> (match resolve tenv ty with
	    | Ty_Type -> Ty_Arrow (Some x, Ty_Type, type_of tenv ctx e)
			| ty' -> Ty_Arrow (None, ty', type_of tenv ((x,ty')::ctx) e))
    | App (e1, e2) ->
			(match resolve tenv (type_of tenv ctx e1) with
				| Ty_Arrow (mv, ty1, ty2) -> (match mv with
					| None -> check tenv ctx ty1 e2 ; resolve tenv ty2
					| Some v -> (match e2 with
						| TyExpr t -> let t' = resolve tenv t in resolve ((v, t') :: tenv) ty2
					| _ -> error ("Expected type argument but got " ^ string_of_expr e2)))
				| ty -> error ("Expected a function but got " ^ string_of_type ty))
		| RandomF i ->
		  check tenv ctx Ty_Int i ;
		  Ty_Real


  (* Does [e] have type [ty] in context [ctx]? *)
  and check tenv ctx ty e =
    let ty' = type_of tenv ctx e in
      check_same tenv ty ty'
end;;
