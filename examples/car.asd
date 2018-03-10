! The example with the autonomous car deciding whether or not to brake

let max = fun a : real => fun b : real =>
  cut x
    left  (x < a \/ x < b)
    right (x > a /\ x > b)
;;

let eps = 0.01;;

let w = 1;;

let T = 1;;

let a_go = fun x : real => fun v : real =>
    max 0 (2 * (w + eps - x - v * T) / (T * T))
;;

let a_stop = fun x : real => fun v : real =>
    v * v / (2 * (x + eps))
;;

let restrict =
  fun U : prop =>
  fun x : real =>
  cut z
     left U /\ z < x
     right U /\ x < z
;;

let a_max = 10;;

let a_min = -10;;

let accel = fun x : real => fun v : real =>
  (  restrict (a_go x v    < a_max) (a_go x v)
  || restrict (a_stop x v  > a_min) (a_stop x v)
  )
;;

let accel_test_1 = accel -5 5;;
