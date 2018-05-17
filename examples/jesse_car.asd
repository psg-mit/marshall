! #plot 20 (quantified_shape_to_bool (scale_shape_x_y square_quantified 1 0.65));;

! ---------- Set Up the Shapes ---------- 
let to_bool =
  fun p : prop * prop =>
  mkbool p#0 p#1 ;;

let shape_to_bool =
  fun shape : real -> real -> prop * prop =>
  fun x : real =>
  fun y : real =>
  to_bool (shape x y);;
  
let quantified_shape_to_bool =
  fun shape : (real -> real -> prop * prop)
            * ((real -> real -> prop) -> prop * prop) =>
  fun x : real =>
  fun y : real =>
  to_bool (shape#0 x y)
  ;;

! create the quantifiers for the unit square.
let forall_exists_square = 
  fun p : real -> real -> prop =>
  let forall_square =   
    fun p : real -> real -> prop =>
    forall x : [-0.5, 0.5],
    forall y : [-0.5, 0.5],
    p x y in
  let exists_square =
    fun p : real -> real -> prop =>
    exists x1 : [-0.5, 0.5],
    exists y1 : [-0.5, 0.5],
    p x1 y1 in 
  (forall_square p, exists_square p)
  ;;

! unit disk centered at origin
let square_quantified =
  (square , forall_exists_square)
;;

! create the quantifiers for the unit circles.
let forall_exists_circle = 
  fun p : real -> real -> prop =>
  let forall_circle =   
    fun p : real -> real -> prop =>
    forall x : [-1, 1],
    forall y : [-1, 1],
    (circle x y)#1 \/ p x y in
  let exists_circle =
    fun p : real -> real -> prop =>
    exists x1 : [-1, 1],
    exists y1 : [-1, 1],
    (circle x1 y1)#0 /\ p x1 y1 in 
  (forall_circle p, exists_circle p)
  ;;

! unit disk centered at origin
let circle_quantified =
  (circle , forall_exists_circle)
;;

let scale_shape_x_y =
  fun shape : (real -> real -> prop * prop)
            * ((real -> real -> prop) -> prop * prop) =>
  fun cx : real =>
  fun cy : real =>
  (fun x : real => fun y : real =>
    shape#0 (x / cx) (y / cy)
    ,
  fun p' : real -> real -> prop => 
  shape#1 (fun x : real => fun y : real => p' (x * cx) (y * cy))
  )
  ;;

let translate_shape_x_y =
  fun shape : (real -> real -> prop * prop)
            * ((real -> real -> prop) -> prop * prop) =>
  fun tx : real =>
  fun ty : real =>
  (fun x : real => fun y : real =>
    shape#0 (x - tx) (y - ty)
    ,
  fun p' : real -> real -> prop => 
  shape#1 (fun x : real => fun y : real => p' (x - tx) (y - ty))
  )
  ;;

let union_quantified = 
  fun shape1 : (real -> real -> prop * prop)
        * ((real -> real -> prop) -> prop * prop) =>         
  fun shape2 : (real -> real -> prop * prop)
            * ((real -> real -> prop) -> prop * prop) =>
  ((fun x : real =>
   fun y : real =>
   ((shape1#0 x y)#0 \/ (shape2#0 x y)#0, 
    (shape1#0 x y)#1 \/ (shape2#0 x y)#1)),  
  ((fun pr : real -> real -> prop =>
   ((shape1#1 pr)#0 \/ (shape2#1 pr)#0, 
    (shape1#1 pr)#1 \/ (shape2#1 pr)#1))))
  ;;

let max = fun a : real => fun b : real =>
  cut x  left  (x < a \/ x < b)
         right (x > a /\ x > b);;

! --------- Make the car --------- 

! Set the starting position and velocity
let x = -0.5;;
let v = 0.25;;

! Create the car    
let car = 
  let wheel = (scale_shape_x_y circle_quantified 0.09 0.09) in 
  let right_wheel = (translate_shape_x_y wheel 0.25 0.125) in 
  let left_wheel = (translate_shape_x_y  wheel -0.25 0.125) in
  let car_body1 = (scale_shape_x_y square_quantified 0.75 0.15) in
  let car_body2 = (translate_shape_x_y (scale_shape_x_y square_quantified 0.5 0.35)  0 -0.125) in
  let car_body = union_quantified car_body1 car_body2 in 
  let wheels = union_quantified left_wheel right_wheel in
  translate_shape_x_y (union_quantified car_body wheels) (-0.375 + x) 0
  ;;

! Create the intersection
let crossing = (scale_shape_x_y square_quantified 0.5 0.5);;

! Make the system
let system = translate_shape_x_y (union_quantified crossing car) 0.25 0;;

! --------- Set up and run the simulation --------- 
let eps = 0.01;;
let a_max = 5;; 
let a_min = -5;;
! add in the length of the car to make sure the whole
! car clears the intersection.
let w = 0.5 + 0.75;;
let T = 1;;

! Compute properties such as the separation distance and to know that it's positive
! Width of the car is not modelled 
let a_stop = fun x : real => fun v : real =>
    v * v / (2 * (x + eps)) 
  ;;

let a_go = fun x : real => fun v : real =>
  max 0 (2 * (w + eps - x - v * T) / (T * T)) 
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
let v_max = -a_min * (T + (sqrt (T*T - 2*(T*T/2*a_max - w - 2 * eps)/a_min)));;

! Check that the car is safe for a given acceleration function
! for starting positions in the range [-2,-1] and velocities in
! the range [0, v_max], in this case v_max is about 11
! check if either the acceleration is illegal or we are safe
let stop_is_safe =
  forall x : [-2, -1],
  forall v : [0, 11],
  let stop_car = (move_car a_stop x v car) in 
  (((a_stop x v) < a_min) \/ ((separation stop_car crossing) > 0))
  ;;

let go_is_safe =
  forall x : [-2, -1],
  forall v : [0, 11],
  let go_car = (move_car a_go x v car) in 
  (((a_go x v) > a_max) \/ ((separation go_car crossing) > 0))
  ;;

! #plot 40 (quantified_shape_to_bool system);;
! #plot 40 (quantified_shape_to_bool updated_system);;

let zero_shape = (fun x : real => fun y : real => (False, True),
                  fun P : real -> real -> prop => (P 0 0, P 0 0));;

!let test_prop = 
!  fun x1 : real =>
!  fun x2 : real =>
!  x1 < x2
!  ;;

! Why can't foralls accept variable arguments?

                
