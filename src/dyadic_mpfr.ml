(* \section{Dyadic numbers with MPFR (module [Dyadic_mpfr])} *)

(* Dyadic numbers with MPFR, wrapped up in a purely functional
   interface.

   We always specify output precision [prec], which measures bits of
   mantissa, and rounding mode. In other words, all operations are
   approximate. We never need to add or multiply two dyadics exactly
   (it is too expensive to do so, anyway). *)

type t = Mpfr.t

(* \subsection{Rounding modes} *)

type rounding_mode = Mpfr.round

type rand_state = Gmp_random.state

let down = Mpfr.Down

let up = Mpfr.Up

(* Invert the rounding mode.*)
let anti = function
  | Mpfr.Down -> Mpfr.Up
  | Mpfr.Up -> Mpfr.Down
  | _ -> raise (Invalid_argument "Dyadic.anti")

(* \subsection{Constructors} *)

(* OCaml [int] to dyadic. *)
let of_int ?prec ~round k =
  let prec = (match prec with None -> Sys.word_size | Some p -> p) in
  let q = Mpfr.init2 prec in
    ignore (Mpfr.set_si q k round) ;
    q

(* GMP large integer to dyadic. *)
let of_integer ~prec ~round k =
  let q = Mpfr.init2 prec in
    ignore (Mpfr.set_z q k round) ;
    q

let make_int ?prec ~round m e =
  let q = of_int ?prec ~round m in
    (if Mpfr.mul_2si q q e Mpfr.Zero <> 0 then assert false) ;
    q

let make ~prec ~round m e =
  let q = of_integer prec round m in
    (if Mpfr.mul_2si q q e Mpfr.Zero <> 0 then assert false) ;
    q

(* \subsection{Constants} *)

let zero = of_int ~round:down 0

let one = of_int ~round:down 1

let negative_one = of_int ~round:down (-1)

let two = of_int ~round:down 2

let half ?prec ~round = make_int ?prec ~round 1 (-1)

(* \subsection{Order} *)

let min a b =
  if Mpfr.cmp a b < 0 then a else b

let max a b =
  if Mpfr.cmp a b < 0 then b else a

let cmp a b =
  let c = Mpfr.cmp a b in
    if c < 0 then `less
    else if c = 0 then `equal
    else `greater

let sgn a =
  let c = Mpfr.sgn a in
    if c < 0 then `negative
    else if c = 0 then `zero
    else `positive

(* less *)
let lt a b = (Mpfr.cmp a b < 0)

(* greater *)
let gt a b = (Mpfr.cmp a b > 0)

(* equal *)
let eq a b = (Mpfr.cmp a b = 0)

(* less or equal *)
let leq a b = (Mpfr.cmp a b <= 0)

(* greater or equal *)
let geq a b = (Mpfr.cmp a b >= 0)

let is_zero a = Mpfr.sgn a = 0

let negative a = Mpfr.sgn a < 0

let positive a = Mpfr.sgn a > 0

let nonpositive a = Mpfr.sgn a <= 0

let nonnegative a = Mpfr.sgn a >= 0

(* \subsection{Special values} *)

let positive_infinity =
  let q = Mpfr.init () in
    ignore (Mpfr.set_inf q 1) ;
    q

let negative_infinity =
  let q = Mpfr.init () in
    ignore (Mpfr.set_inf q (-1)) ;
    q

(* Depending on the rounding mode, return negative or positive infinity *)
let infinity = function
  | Mpfr.Down -> negative_infinity
  | Mpfr.Up -> positive_infinity
  | _ -> raise (Invalid_argument "Dyadic.infinity")

let is_infinity = Mpfr.inf_p

let is_positive_infinity a =
  is_infinity a && positive a

let is_negative_infinity a =
  is_infinity a && negative a

let is_number = Mpfr.number_p

let is_nan = Mpfr.nan_p

let classify a =
  if is_number a then `number
  else if is_nan a then `nan
  else if Mpfr.sgn a > 0 then `positive_infinity
  else `negative_infinity


(* \subsection{Arithmetic} *)

(* Arithmetic operations need to take care of infinite operands when
   the result would be [nan] (not a number). *)

(* Addition. Special cases: $\infty + (-\infty)$ and $-\infty +
   \infty$. *)
let add ?prec ~round a b =
  let prec = (match prec with None -> Pervasives.max (Mpfr.get_prec a) (Mpfr.get_prec b) | Some p -> p) in
  if (is_negative_infinity a && is_positive_infinity b) ||
     (is_positive_infinity a && is_negative_infinity b)
  then
    infinity round
  else
    let q = Mpfr.init2 prec in
      ignore (Mpfr.add q a b round) ;
      q

(* Subtraction. Special cases: $\infty - \infty$ and $-\infty -
   (-\infty)$. *)
let sub ?prec ~round a b =
  let prec = (match prec with None -> Pervasives.max (Mpfr.get_prec a) (Mpfr.get_prec b) | Some p -> p) in
  if (is_negative_infinity a && is_negative_infinity b) ||
     (is_positive_infinity a && is_positive_infinity b)
  then
    infinity round
  else
    let q = Mpfr.init2 prec in
      ignore (Mpfr.sub q a b round) ;
      q

(* Negation. No special cases. *)
let neg ?prec ~round a =
  let prec = (match prec with None -> Mpfr.get_prec a | Some p -> p) in
  let q = Mpfr.init2 prec in
    ignore (Mpfr.neg q a round) ;
    q

(* Multiplication. Special cases: $\pm\infty \times 0$ and $0 \times
   \pm\infty$. *)
let mul ?prec ~round a b =
  let prec = (match prec with None -> (Mpfr.get_prec a)+(Mpfr.get_prec b) | Some p -> p) in
  if (is_zero a && is_infinity b) || (is_infinity a && is_zero b) then
    infinity round
  else
    let q = Mpfr.init2 prec in
      ignore (Mpfr.mul q a b round) ;
      q

(* Powers with non-negative exponents. No special cases. *)
let pow ?prec ~round a k =
  let prec = (match prec with None -> (Mpfr.get_prec a)*k | Some p -> p) in
  let q = Mpfr.init2 prec in
    ignore (Mpfr.pow_si q a k round) ;
    q

(* Division. Special cases: $0/0$ and $\pm\infty/\pm\infty$. *)
let div ~prec ~round a b =
  if (is_zero a && is_zero b) || (is_infinity a && is_infinity b) then
    infinity round
  else
    let q = Mpfr.init2 prec in
      ignore (Mpfr.div q a b round) ;
      q

let unop f ~prec ~round a =
  let q = Mpfr.init2 prec in
    ignore (f q a round) ;
    q

(* Just for fun we inlude the exponetial function. There are two
   special cases, but somebody should think about what happens in the
   case of underflow and overflow. *)
let exp ~prec ~round = unop Mpfr.exp ~prec ~round
let sin ~prec ~round = unop Mpfr.sin ~prec ~round
let cos ~prec ~round = unop Mpfr.cos ~prec ~round

(* Inverse. Special cases not handled by MPFR: $0^{-1}$ and
   $(\pm\infty)^{-1}$. *)
let inv ~prec ~round a =
  if is_zero a || is_infinity a then
    infinity round
  else
    let q = Mpfr.init2 prec in
      ignore (Mpfr.div q one a round) ;
      q

(* Shift by a power of two. No special cases. *)
let shift ?prec ~round a k =
  let prec = (match prec with None -> Mpfr.get_prec a | Some p -> p) in
  let q = Mpfr.init2 prec in
    ignore (Mpfr.set q a round) ;
    ignore (Mpfr.mul_2si q q k round) ;
    q

let halve ?prec ~round a =
  let prec = (match prec with None -> Mpfr.get_prec a | Some p -> p) in
    shift ~prec ~round a (-1)

let double ?prec ~round a =
  let prec = (match prec with None -> Mpfr.get_prec a | Some p -> p) in
    shift ~prec ~round a 1

(* [average a b] returns a dyadic which is guaranteed to be strictly
   between [a] and [b], close to the average. This only works for
   finite [a] and [b].
*)
let average a b =
  let prec = 1 + Pervasives.max (Mpfr.get_prec a) (Mpfr.get_prec b) in
  let q = add ~prec ~round:Mpfr.Near a b in
    ignore (Mpfr.mul_2si q q (-1) Mpfr.Near) ;
    q

(* \subsection{String conversions} *)

let of_string ?prec ~round str =
  let prec = (match prec with None -> Pervasives.max (4 * (String.length str)) Sys.word_size | Some p -> p) in
  let q = Mpfr.init2 prec in
  ignore (Mpfr.set_str q str 0 round) ;
  q

let trim_right ?(min_length = 0) str chr =
  let n = ref (String.length str) in
    while !n > min_length && str.[!n - 1] == chr do
      n := !n - 1
    done;
    String.sub str 0 !n

let string_insert a pos b =
  (String.sub a 0 pos) ^ b ^ (String.sub a pos (String.length a - pos))

let string_delete a pos len =
  (String.sub a 0 pos) ^ (String.sub a (pos + len) (String.length a - pos - len))

let to_string2 x =
  match classify x with
      | `nan -> "nan"
      | `positive_infinity -> "inf"
      | `negative_infinity -> "-inf"
      | `number ->
	let m = Mpz.init () in
	  let e = Mpfr.get_z_exp m x in
	  let m = Mpz.get_str ~base:10 m in
	    m ^ "p" ^ (string_of_int e) ^ "(p=" ^ string_of_int (Mpfr.get_prec x) ^ ")"

(* [Mpfr.to_string] produces rather unreadable results. This is an improved version. *)
let to_string x =
  let exp_notation = 4 in
  let trim = true in
    match classify x with
      | `nan -> "nan"
      | `positive_infinity -> "inf"
      | `negative_infinity -> "-inf"
      | `number ->
	  let (s, e) = Mpfr.get_str ~digits:0 ~base:10 x Mpfr.Near in
	  let (sign, str') =
	    if String.get s 0 = '-' then ("-", string_delete s 0 1) else ("", s)
	  in
	  let str =
	    if trim then trim_right ~min_length:(Pervasives.max 1 e) str' '0' else str'
	  in
	    if e > String.length str || e < - exp_notation then
	      sign ^ string_insert str 1 "." ^ "e" ^ string_of_int (e - 1)
	    else if e > 0 then
	      sign ^ string_insert str e "."
	    else
	      sign ^ "0." ^ String.make (-e) '0' ^ str
let get_exp x =
  Mpfr.get_exp x

let rand ~prec s =
  let q = Mpfr.init2 prec in
    ignore (Gmp_random.Mpfr.urandomb q s) ;
    q

let new_rand_state i =
  let s = Gmp_random.init_default () in
  ignore (Gmp_random.seed_ui s i);
  s