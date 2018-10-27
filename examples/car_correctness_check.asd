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
let a_stop = fun x : real => fun v : real =>
    v * v / (2 * (x + eps))
  ;;

let a_go = fun x : real => fun v : real =>
  max 0 (2 * (w + w_car + eps - x - v * T) / (T * T))
  ;;

let accel = fun x : real => fun v : real =>
  (  a_go x v   < a_max  ~>  a_go x v
  || a_stop x v > a_min  ~>  a_stop x v )
  ;;

! move the car using the given acceleration function,
! and initial position and velocity
let move_car =
  fun acceleration : real -> real -> real =>
  fun x : real =>
  fun v : real =>

  fun car : (real -> real -> prop * prop)
          * ((real -> real -> prop) -> prop * prop) =>
  ! distance moved by accelerating as per acccel.
  translate_shape_x_y car (((acceleration x v) * T * T / 2) + v * T)  0;;

let moved_car = move_car accel x v car;;

let updated_system = translate_shape_x_y (union_quantified crossing moved_car) 0.25 0;;

! ---------- Demonstrate Correctness ----------

! minimum distance between two shapes
let separation =
  fun shape1 : (real -> real -> prop * prop)
      * ((real -> real -> prop) -> prop * prop) =>
  fun shape2 : (real -> real -> prop * prop)
          * ((real -> real -> prop) -> prop * prop) =>
  cut cutoff left (cutoff < 0 \/ (shape2#1 (fun x2 : real => fun y2 : real =>
                  (shape1#1 (fun x1 : real => fun y1 : real =>
                  (euclidean_dist (x1,y1) (x2,y2)) > cutoff))#0))#0)
             right (cutoff > 0 /\ (shape2#1 (fun x2 : real => fun y2 : real =>
                  (shape1#1 (fun x1 : real => fun y1 : real =>
                  (euclidean_dist (x1,y1) (x2,y2)) < cutoff))#1))#1)
  ;;

! the separation (minimum distance) betweeen a given shape and a point
let shape_point_separation =
  fun shape1 : (real -> real -> prop * prop)
      * ((real -> real -> prop) -> prop * prop) =>

  fun p : real*real =>

  cut cutoff left (cutoff < 0 \/
              (shape1#1 (fun x1 : real => fun y1 : real =>
              (euclidean_dist (x1,y1) p) > cutoff))#0)
          right (cutoff > 0 /\
              (shape1#1 (fun x1 : real => fun y1 : real =>
              (euclidean_dist (x1,y1) p) < cutoff))#1)
  ;;

! compute the hausdorff distance between two shapes.
! It is the max over every shape_point_separation
let hausdorff_distance =
  fun shape1 : (real -> real -> prop * prop)
      * ((real -> real -> prop) -> prop * prop) =>
  fun shape2 : (real -> real -> prop * prop)
          * ((real -> real -> prop) -> prop * prop) =>

  ! compute the sup_{x in shape1}(inf_{y in shape2} d(x,y))
  let sup_inf_distance =
      fun shape1 : (real -> real -> prop * prop)
          * ((real -> real -> prop) -> prop * prop) =>
      fun shape2 : (real -> real -> prop * prop)
              * ((real -> real -> prop) -> prop * prop) =>

      cut cutoff2
          left (cutoff2 < 0 \/
                  (shape2#1 (fun x2 : real => fun y2 : real =>
                    ((shape_point_separation shape1 (x2,y2)) > cutoff2)
                  ))#1
                )
          right (cutoff2 > 0 /\
                  (shape2#1 (fun x2 : real => fun y2 : real =>
                      ((shape_point_separation shape1 (x2,y2)) < cutoff2)
                  ))#0
                ) in

  ! compute max (sup_{x in shape1}(inf_{y in shape2} d(x,y)),
  !              sup_{y in shape2}(inf_{x in shape1} d(x,y)))
  max (sup_inf_distance shape1 shape2) (sup_inf_distance shape2 shape1)
  ;;



! Compute the max velocity as per page 9 of the paper
let v_max = -a_min * (T + (sqrt (T*T - 2*(T*T/2*a_max - (w + w_car) - 2 * eps)/a_min)));;

! Check that the car is safe for a given acceleration function
! for starting positions in the range [-2,-1] and velocities in
! the range [0, v_max], in this case v_max is about 11
! check if either the acceleration is illegal or we are safe
let go_is_safe =
  forall x : [-2, -1],
  forall v : [0, 11],
  let go_car = (move_car a_go x v car) in
  (((a_go x v) > a_max) \/ (is_separated go_car crossing))
  ;;

let go_is_safe =
  forall x : [-2, -1],
  forall v : [0, 11],
  let go_car = (move_car a_go x v car) in
  (((a_go x v) > a_max) \/ (is_separated go_car crossing))
  ;;


! Check that both stopping and going is safe.
let all_is_safe = go_is_safe /\ stop_is_safe;;

! used to plot the car-crossing system in it's initial and final states.
! #plot 40 (quantified_shape_to_bool system);;
! #plot 40 (quantified_shape_to_bool updated_system);;

! ---------- Notes and Test Shapes ----------

let zero_shape = (fun x : real => fun y : real => (False, True),
                  fun P : real -> real -> prop => (P 0 0, P 0 0));;

let test_prop =
  fun x1 : real =>
  fun x2 : real =>
  x1 < x2
  ;;

! How do foralls work
! Why can't foralls accept variable arguments?