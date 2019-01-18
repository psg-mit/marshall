! Since there is no Boolean data type, we will encode Booleans
! with { x : R | x =/= 1/2 }, where anything less than 0.5 represents
! `ff`, and anything greater than 1/2 represents `tt`.
! Again, since we don't have sublocales, we will just use reals, and
! implicitly require that the input is not 1/2.

let is_true' =
  fun b : real => b > 0.5;;

let is_false' =
  fun b : real => b < 0.5;;

let max = fun a : real => fun b : real =>
  cut x
    left  (x < a \/ x < b)
    right (x > a /\ x > b)
;;

let min = fun a : real => fun b : real =>
  cut x
    left  (x < a /\ x < b)
    right (x > a \/ x > b)
;;

! The standard boolean operations with our real-number based
! encoding.
let andb = min;;
let orb = max;;
let tt = 1;;
let ff = 0;;
let negb =
  fun b : real => 1 - b
;;

let not_0 =
  fun x : real =>
  x < 0 \/ x > 0
;;

let is_0_eps =
  fun eps : real =>
  fun x : real =>
  -eps < x /\ x < eps
;;

let not_0_eps =
  fun eps : real =>
  fun x : real =>
     not_0 x ~> tt
  || is_0_eps eps x ~> ff
;;

! Forall-quantification of a nondeterministic-Boolean-valued
! predicate over the unit interval.
let forall_bool_interval =
  fun pred : real -> real =>
     (forall x : [0,1], is_true' (pred x)) ~> tt
  || (exists x : [0,1], is_false' (pred x)) ~> ff
;;

! Do we have any approximate roots of our function `f` on the
! unit interval, with tolerance `eps`?
let roots_interval' =
  fun eps : real =>
  fun f : real -> real =>
  negb (forall_bool_interval (fun x : real => not_0_eps eps (f x)))
;;

! A more "reduced" or low-level encoding of the above
let roots_interval =
  fun eps : real =>
  fun f : real -> real =>
     ((forall x : [0,1], not_0 (f x)) ~> ff)
  || ((exists x : [0,1], is_0_eps eps (f x)) ~> tt)
;;

let func_with_roots =
  fun x : real =>
  (x - 1)^2 + 0.1
;;

let test_roots =
  roots_interval' 0.1 func_with_roots;;