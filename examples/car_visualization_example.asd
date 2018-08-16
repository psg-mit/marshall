#use "examples/quantified_interior_exterior_cad.asd";;

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
  shape#1 (fun x : real => fun y : real => p' (x + tx) (y + ty))
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
    (shape1#0 x y)#1 /\ (shape2#0 x y)#1)),  
  ((fun pr : real -> real -> prop =>
   ((shape1#1 pr)#0 /\ (shape2#1 pr)#0, 
    (shape1#1 pr)#1 \/ (shape2#1 pr)#1))))
  ;;

let max = fun a : real => fun b : real =>
  cut x  left  (x < a \/ x < b)
         right (x > a /\ x > b);;

! Two shapes are separated if they share no points in common.
! This is checking that separation is > 0, but is computationally more efficient.
! forall (x2,y2) in shape2 forall (x1,y1) in shape1 (x1 != x2 or y1 != y2) 
let is_separated = 
  fun shape1 : (real -> real -> prop * prop)
      * ((real -> real -> prop) -> prop * prop) =>         
  fun shape2 : (real -> real -> prop * prop)
          * ((real -> real -> prop) -> prop * prop) =>
  (shape2#1 (fun x2 : real => fun y2 : real => 
            (shape1#1 (fun x1 : real => fun y1 : real => 
                  (x1 < x2 \/ x1 > x2 \/ y1 > y2 \/ y1 < y2)))#0))#0  
  ;;

! --------- Make the car --------- 

! Set the starting position and velocity
let x = -1.5;;
let v = 3;;

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



                
