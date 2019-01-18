#use "examples/bool.asd";;

let not_0 =
  fun x : real =>
  x < 0 \/ x > 0
;;

let is_0_eps =
  fun eps : real =>
  fun x : real =>
  -eps < x /\ x < eps
;;

let restrictb =
  fun U : prop =>
  fun x : bool =>
  mkbool (U /\ is_true x) (U /\ is_false x)
  ;;

let mkboolp =
  fun U : prop =>
  fun V : prop =>
  restrictb U tt || restrictb V ff
  ;;

let is_0_eps_bool =
  fun eps : real =>
  fun x : real =>
     mkboolp (is_0_eps eps x) (not_0 x);;

! Forall-quantification of a nondeterministic-Boolean-valued
! predicate over the unit interval.
let exists_bool_interval =
  fun pred : real -> bool =>
  mkboolp
     (exists x : [0,1], is_true (pred x))
     (forall x : [0,1], is_false (pred x))
;;

! Do we have any approximate roots of our function `f` on the
! unit interval, with tolerance `eps`?
let roots_interval =
  fun eps : real =>
  fun f : real -> real =>
  exists_bool_interval (fun x : real => is_0_eps_bool eps (f x))
;;

let func_with_roots =
  fun x : real =>
  (x - 1)^2 + 0.1
;;

let test_roots =
  roots_interval 0.1 func_with_roots;;