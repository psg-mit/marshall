! This is a sample Marshall program.
! Comments begin with ! and end with end of line.
! Definitions and exprssions must be separated by double semicolons

let sqrt =
  fun a : real =>
    cut x
      left  (x < 0 \/ x * x < a)

      right (x > 0 /\ x * x > a)
;;

! Logarithmic map
let lg = fun x : real => 2 * (1 - x^2) - 1
;;

! Maximum of a function on the unit interval
let max =
  fun f : real -> real =>
    cut a
      left  (exists x : [0,1], a < f x)
      right (forall x : [0,1], f x < a)
;;

let restrictb =
  fun U : prop =>
  fun x : bool =>
  mkbool (U /\ is_true x) (U /\ is_false x)
  ;;

let aprx_compare = fun eps : real => fun x : real =>
     restrictb (x > - eps) (mkbool True False)
  || restrictb (x < eps)   (mkbool False True)
;;

! sqrt(2) is approximately larger than 1.4
let sqrt2_bigger_than_1_4 = aprx_compare 0.01 (sqrt(2) - 1.4);;

! The error tolerance is too wide, so we erroneously think it's true
let sqrt2_smaller_than_1_42_too_tolerant = aprx_compare 10 (sqrt(2) - 1.42);;

! With a smaller error tolerance, we get the right answer
let sqrt2_smaller_than_1_42 = aprx_compare 1 (sqrt(2) - 1.42);;

