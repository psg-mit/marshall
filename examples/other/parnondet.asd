let restrict =
  fun U : prop =>
  fun x : real =>
  cut z
     left U /\ z < x
     right U /\ x < z
;;

let imax =
  fun x : real =>
  fun y : real =>
  cut z
    left   z < x \/ z < y
    right  x < z \/ y < z
;;

let aprx_compare = fun eps : real => fun x : real =>
  imax (restrict (x > - eps) 1)
       (restrict (x < eps)   0)
;;

let sqrt =
  fun a : real =>
    cut x
      left  (x < 0 \/ x * x < a)

      right (x > 0 /\ x * x > a)
;;

! sqrt(2) is approximately larger than 1.4
let sqrt2_bigger_than_1_4 = aprx_compare 0.01 (sqrt(2) - 1.4);;

! The error tolerance is too wide, so we erroneously think it's true
let sqrt2_smaller_than_1_42_too_tolerant = aprx_compare 10 (sqrt(2) - 1.42);;

! With a smaller error tolerance, we get the right answer
let sqrt2_smaller_than_1_42 = aprx_compare 1 (sqrt(2) - 1.42);;
