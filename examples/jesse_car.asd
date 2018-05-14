! #plot 20 (quantified_shape_to_bool (scale_shape_x_y square_quantified 1 0.65));;

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

    
let car = 
  let wheel = (scale_shape_x_y circle_quantified 0.09 0.09) in 
  let right_wheel = (translate_shape_x_y wheel 0.25 0.125) in 
  let left_wheel = (translate_shape_x_y  wheel -0.25 0.125) in
  let car_body1 = (scale_shape_x_y square_quantified 0.75 0.15) in
  let car_body2 = (translate_shape_x_y (scale_shape_x_y square_quantified 0.5 0.35)  0 -0.125) in
  let car_body = union_quantified car_body1 car_body2 in 
  let wheels = union_quantified left_wheel right_wheel in
  translate_shape_x_y (union_quantified car_body wheels) -0.6 0
  ;;

let intersection_for_car = (scale_shape_x_y square_quantified 0.5 0.5);;

let system = translate_shape_x_y (union_quantified intersection_for_car car) 0.25 0;;

let max = fun a : real => fun b : real =>
  cut x  left  (x < a \/ x < b)
         right (x > a /\ x > b);;

let eps = 0.01;;
let a_max = 5;; 
let a_min = -5;;
! add in the length of the car to make sure the whole
! car clears the intersection.
let w = 0.5 + 0.75;;
let T = 1;;

! compute properties such as the separation distance and to know that it's positive

! width of the car is not modelled 
let accel = fun x : real => fun v : real =>
  let a_go = fun x : real => fun v : real =>
    max 0 (2 * (w + eps - x - v * T) / (T * T)) in 
  let a_stop = fun x : real => fun v : real =>
    v * v / (2 * (x + eps)) in
  (  a_go x v   < a_max  ~>  a_go x v
  || a_stop x v > a_min  ~>  a_stop x v );;

! distance moved by accelerating as per ac.
 
let move_car = 
  fun x : real => 
  fun v : real =>
  fun car : (real -> real -> prop * prop)
          * ((real -> real -> prop) -> prop * prop) =>
  
  translate_shape_x_y car (((accel x v) * T * T / 2) + v * T)  0;;

let moved_car = move_car car x;;

let updated_system = translate_shape_x_y (union_quantified intersection_for_car moved_car) 0.25 0;;

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

let point_set_separation = 
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

let hausdorff_distance = 
    fun shape1 : (real -> real -> prop * prop)
        * ((real -> real -> prop) -> prop * prop) =>         
    fun shape2 : (real -> real -> prop * prop)
            * ((real -> real -> prop) -> prop * prop) =>

    cut cutoff2 
        left (cutoff2 < 0 \/ 
                (shape2#1 (fun x2 : real => fun y2 : real =>  
                  ((point_set_separation shape1 (x2,y2)) > cutoff2) 
                ))#1                 
              )
        right (cutoff2 > 0 /\ 
                (shape2#1 (fun x2 : real => fun y2 : real =>  
                    ((point_set_separation shape1 (x2,y2)) < cutoff2)    
                ))#0                  
              )
    ;;





! #plot 40 (quantified_shape_to_bool system);;
! #plot 40 (quantified_shape_to_bool updated_system);;

! Concern?
!# let x = pos 1 2;;
!uh-oh left cut-0.00000000000,-0.00000000000
!uh-oh right cut0.00000000000,0.00000000000

!#use "examples/jesse_bounding_box.asd";;
!rightmost_extent intersection_for_car;;

let zero_shape = (fun x : real => fun y : real => (False, True),
                  fun P : real -> real -> prop => (P 0 0, P 0 0));;

!let test_prop = 
!  fun x1 : real =>
!  fun x2 : real =>
!  x1 < x2
!  ;;

                
