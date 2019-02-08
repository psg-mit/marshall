#use "examples/car_visualization_example.asd";;

! --------- Set up and run the simulation ---------
let eps = 0.01;;
let a_max = 5;;
let a_min = -5;;
let w_car = 0.75;;
let w = 0.5;;
let T = 1;;

! Compute properties such as the separation distance and to know that it's positive
! Width of the car is not modelled
let a_stop (x v : real) : real =
    v * v / (2 * (x + eps))
  ;;

let a_go (x v : real) : real =
  max 0 (2 * (w + w_car + eps - x - v * T) / (T * T))
  ;;

let accel (x v : real) : real =
  (   a_go x v   < a_max  ~>  a_go x v
  ||| a_stop x v > a_min  ~>  a_stop x v )
  ;;

! move the car using the given acceleration function,
! and initial position and velocity
let move_car (acceleration : real -> real -> real) (x v : real)
             (car : ((real^2 -> bool) -> bool) * (real^2 -> bool)) =
  ! distance moved by accelerating as per acccel.
  translate_ok (((acceleration x v) * T * T / 2) + v * T, 0) car;;

let moved_car = move_car accel x v car;;

let updated_system = translate_ok (0.25, 0) (union_ok crossing moved_car);;

! ---------- Demonstrate Correctness ----------

! the separation (minimum distance) betweeen a given shape and a point
let shape_point_separation
    (shape1 : ((real^2 -> bool) -> bool) * (real^2 -> bool))
    (p : real^2) : real =
  dedekind_cut (fun cutoff : real => orb (lt cutoff 0)
    (shape1#0 (fun x : real^2 =>
    (cutoff^2) <b ((p#0 - x#0)^2 + (p#1 - x#1)^2)
    )));;

! Compute the max velocity as per page 9 of the paper
let v_max : real =
  -a_min * (T + (sqrt (T*T - 2*(T*T/2*a_max - (w + w_car) - 2 * eps)/a_min)));;

! Check that the car is safe for a given acceleration function
! for starting positions in the range [-2,-1] and velocities in
! the range [0, v_max], in this case v_max is about 11
! check if either the acceleration is illegal or we are safe
let go_is_safe (x v : real) : prop =
  let go_car = (move_car a_go x v car) in
  (a_go x v > a_max \/ is_true (is_separated go_car#0 crossing#0))
  ;;

let stop_is_safe (x v : real) : prop =
  let stop_car = (move_car a_stop x v car) in
  (a_stop x v < a_min \/ is_true (is_separated stop_car#0 crossing#0))
  ;;


! Check that both stopping and going is safe.
let all_is_safe : prop =
  forall x : [-2, -1],
  forall v : [0, 11],
  ! whenever I may choose to go, I avoid the intersection
  go_is_safe x v
  ! whenever I may choose to go, I avoid the intersection
  /\ stop_is_safe x v
  ! I always choose at least one option (stop or go)
  /\ (a_min < a_stop x v \/ a_go x v < a_max);;

! used to plot the car-crossing system in it's initial and final states.
! #plot 40 (quantified_shape_to_bool system);;
! #plot 40 (quantified_shape_to_bool updated_system);;
