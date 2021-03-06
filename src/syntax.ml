(** Abstract syntax of the Marshall language. *)

module Make = functor (D: Dyadic.DYADIC) ->
struct
  module I = Interval.Make(D)

  (** The type of variable names. Variables are either original or generated. *)
  type name =
    | Ident of string
    | Gensym of string * int

  (** Generate a fresh variable name. *)
  let fresh_name =
    let k = ref 0 in
      fun s -> incr k; Gensym (s,!k)

  (** Convert a name to a string. *)
  let string_of_name = function
    | Ident str -> str
    | Gensym (s,k) -> s ^ string_of_int k

  (** In Marshall we have base types for reals and propositions, product types and
      function types. Function types are a mirage because all $\lambda$-abstractions get
      $\beta$-reduced away. *)
  type ty =
    | Ty_Sigma (* [prop] *)
    | Ty_Real  (* [real] *)
    | Ty_Int
    | Ty_Arrow of (name option * ty * ty) (* [t1 -> t2] *)
    | Ty_Tuple of ty list (* [t1 * t2 * ... * tn] *)
    | Ty_Var of name
    | Ty_App of ty * ty
    | Ty_Lam of (name * ty)
    | Ty_Type

  (** Binary arithmetical operations. *)
  type binary =
    | Plus
    | Minus
    | Times
    | Quotient

  (** Convert a binary operation to its string representation. *)
  let string_of_binary = function
    | Plus -> "+"
    | Minus -> "-"
    | Times -> "*"
    | Quotient -> "/"

  (** Operator precedences, used by [string_of_expr] below. *)
  let precs_of_binary = function
    | Times -> 50, 49, 50
    | Quotient -> 50, 49, 50
    | Plus -> 40, 39, 40
    | Minus -> 40, 39, 40

  (** Unary arithmetical operations. *)
  type unary =
    | Opposite
    | Inverse
    | Exp
    | Erf
    | Sin
    | Cos

  (** Convert a unary operation to its string representation. *)
  let string_of_unary = function
    | Opposite -> "-"
    | Inverse -> "inv"
    | Exp -> "exp"
    | Sin -> "sin"
    | Cos -> "cos"
    | Erf -> "erf"

  (** The abstract syntax of Marshall terms. *)
  type expr =
    | Var of name (* variable *)
    | RealVar of name * I.t (* real variable with a given range, see [Eval.refine] *)
    | Dyadic of D.t (* dyadic constant, syntax as in MPFR (subsumes floating-point) *)
    | Integer of int
    | Interval of I.t (* interval constant, no concrete syntax *)
    | Cut of name * I.t * expr * expr
	(* [Cut (x, [a, b], l, u)] is the real number in interval
	   $[a,b]$ whose lower cut is $\lambda x, l$ and upper cut is
	   $\lambda x, u$. There are three kinds of concrete syntax:
	   \begin{itemize}
	   \item [cut x left l right u]
	   \item [cut x : real left l right u]
	   \item [cut x : [a,b] left l right u]
	   \end{itemize} *)
    | Binary of binary * expr * expr
    | Unary of unary * expr
    | Power of expr * int (* Power by a natural constant *)
    | True
    | False
    | Less of expr * expr
	(* Apart from [a < b], concrete syntax also has sugars [a > b]
	   and $a ={e}= b$, which means $-e < a - b < e$. *)
    | And of expr list (* [p1 /\ p2 /\ ... /\ pn] *)
    | Or of expr list (* [p1 \/ p2 \/ ... \/ pn] *)
    | Join of expr list
    | Restrict of (expr * expr)
    | Exists of name * I.t * expr (* [exists x : [a,b], p] *)
    | Forall of name * I.t * expr (* [forall x : [a,b], p] *)
    | Integral of name * I.t * expr
    | Let of name * expr * expr (* [let x = e1 in e2] *)
    | Tuple of expr list (* [(e1, ..., en)] *)
    | Proj of expr * int (* Concrete syntax for $k$-th projection is [e#k] *)
    | Lambda of name * ty * expr (* Concrete syntax is [fun x : ty => e] *)
    | App of expr * expr
    | TyExpr of ty
    | Random of int * (int * D.t * D.rand_state) ref
    | RandomF of expr

  (** Toplevel commands *)
  type toplevel_cmd =
    | Expr of expr * bool       (* Expression, should it be traced? *)
    | Use of string             (* Include file [$use "<filename>"] *)
    | Definition of name * expr * ty option (* Top-level definition [let x = e] *)
    | TypeDefinition of name * ty
    | Precision of D.t          (* Target precision [$precision d] *)
    | Hnf of expr               (* Compute head-normal form *)
    | Help                      (* Print help *)
    | Plot of string * int * expr
    | Quit                      (* Exit toplevel [$quit] *)

  (** Convert a type to a string *)
  let string_of_type ty =
    let rec to_str n ty =
      let (m, str) =
	match ty with
	  | Ty_Sigma            -> (4, "prop")
	  | Ty_Real             -> (4, "real")
	  | Ty_Int              -> (4, "integer")
    | Ty_Type             -> (4, "type")
    | Ty_Var v            -> (4, string_of_name v)
	  | Ty_App (e1, e2)     -> (3, to_str 2 e1 ^ " " ^ to_str 3 e2)
    | Ty_Tuple [Ty_Sigma; Ty_Sigma] -> (4, "bool")
	  | Ty_Tuple lst        -> (2, String.concat "*" (List.map (to_str 2) lst))
	  | Ty_Arrow (mv, ty1, ty2) -> (1, match mv with
        | None -> to_str 1 ty1 ^ " -> " ^ to_str 0 ty2
        | Some v -> "(" ^ string_of_name v ^ " : " ^ to_str 1 ty1 ^ ") -> " ^ to_str 0 ty2)
    | Ty_Lam (x, t)       -> (0, "fun " ^ string_of_name x ^ " => " ^ to_str 0 t)
      in
	if m > n then str else "(" ^ str ^ ")"
    in
      to_str (-1) ty

  (** Convert a string to expression *)
  let rec string_of_expr e =
    let rec to_str n e =
      let (m, str) =
	match e with
	  | Var x   ->           (100, string_of_name x)
	  | RealVar (x, i) ->    (100, "(" ^ string_of_name x ^ ":" ^ I.to_string i ^ ")")
	  | Dyadic q ->          (100, D.to_string q)
	  | Integer n ->         (100, "i" ^ string_of_int n)
	  | Interval i ->        (100, I.to_string_number i)
	  | True | And [] ->     (100, "True")
	  | False | Or [] ->     (100, "False")
    | Random (n, r) ->     (100, "random " ^ string_of_int n)
    | TyExpr t ->          (100, "{" ^ string_of_type t ^ "}")
    | Tuple [True; False] -> (100, "tt")
    | Tuple [False; True] -> (100, "ff")
    | Tuple [False; False] -> (100, "_|_")
	  | Tuple lst ->         (100, "(" ^ (String.concat ", " (List.map (to_str 10) lst)) ^ ")")
	  | Proj (e, k) ->       (90, to_str 90 e ^ "#" ^ string_of_int k)
	  | App (e1, e2) ->      (85, to_str 84 e1 ^ " " ^ to_str 85 e2)
	  | Power (e, k) ->      (83, to_str 82 e ^ " ^ " ^ string_of_int k)
	  | Unary (op, e) ->     (80, string_of_unary op ^ " " ^ to_str 80 e)
    | RandomF e     ->     (80, "random " ^ to_str 80 e)
	  | Binary (op, e1, e2) ->
	      let p, p1, p2 = precs_of_binary op in
		(p, to_str p1 e1 ^ " " ^ string_of_binary op ^ " " ^ to_str p2 e2)
	  | Less (e1, e2) ->     (30, to_str 30 e1 ^ " < " ^ to_str 30 e2)
	  | And lst ->           (20, String.concat " /\\ " (List.map (to_str 19) lst))
	  | Or lst ->            (15, String.concat " \\/ " (List.map (to_str 14) lst))
	  | Restrict (e1, e2) -> (14, to_str 13 e1 ^ " ~> " ^ to_str 13 e2)
  	| Join lst ->         (13, "{" ^ String.concat " || "  (List.map (to_str 12) lst) ^ "}")
	  | Exists (x, t, p) ->  (10, "exists " ^ string_of_name x ^ " : " ^
				    I.to_string t ^ " , " ^ to_str 9 p)
	  | Forall (x, t, p) ->  (10, "forall " ^ string_of_name x ^ " : " ^
				    I.to_string t ^ " , " ^ to_str 9 p)
	  | Integral (x, t, p) ->  (10, "int " ^ string_of_name x ^ " : " ^
				    I.to_string t ^ " , " ^ to_str 9 p)
	  | Let (x, e1, e2)  ->  (10, "let " ^ string_of_name x ^ " = " ^ to_str 10 e1 ^
				    " in " ^ to_str 9 e2)
	  | Lambda (x, t, e) ->  (10, "fun " ^ string_of_name x ^ " : " ^ string_of_type t ^
				    " => " ^ to_str 9 e)
	  | Cut (x, i, p1, p2) -> (5, "cut " ^ string_of_name x ^ " : " ^
				     I.to_string i ^
				     " left " ^ to_str 5 p1 ^ " right " ^ to_str 5 p2)
      in
	if m > n then str else "(" ^ str ^ ")"
    in
      to_str (-1) e

let string_of_approx = function
	| False | Or [] ->    "?"
  | Tuple [False; False] -> "?"
  | e -> string_of_expr e

end
