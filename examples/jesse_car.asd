! #plot 20 (quantified_shape_to_bool (scale_shape_x_y square_quantified 1 0.65));;
let car = 
  let wheel = (scale_shape_x_y circle_quantified 0.18 0.18) in 
  let right_wheel = (translate_shape_x_y wheel 0.5 0.4) in 
  let left_wheel = (translate_shape_x_y  wheel -0.5 0.4) in
  let car_body = (scale_shape_x_y square_quantified 1.5 0.75) in
  let wheels = union_quantified left_wheel right_wheel in
  union_quantified car_body wheels
  ;;

! #plot 20 (quantified_shape_to_bool (translate_shape_x_y (scale_shape_x_y circle_quantified 0.3 0.3) -0.5 0.5));;
let to_bool =
  fun p : prop * prop =>
  mkbool p#0 p#1 ;;

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
    forall x : [-1, 1],
    forall y : [-1, 1],
    p x y in
  let exists_square =
    fun p : real -> real -> prop =>
    exists x1 : [-1, 1],
    exists y1 : [-1, 1],
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
  shape#1 (fun x : real => fun y : real => p' (x / cx) (y / cy))
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
  fun p'' : real -> real -> prop => 
  shape#1 (fun x : real => fun y : real => p'' (x - tx) (y - ty))
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



  ! fun x : real => fun y : real =>
  ! shape#0 (x / cx) (y / cy)
  !!(fun x : real => fun y : real =>
  !!  shape#0 (x / cx) (y / cy)
  !!  , fun p' : real -> real -> prop =>
  !!  shape#1 (fun x : real => fun y : real => (p' x y)) 
  !!)
  !;;

!let forall_square =
!  fun p : real -> real -> prop =>
!  forall x : [-1, 1],
!  forall y : [-1, 1],
!  (square x y)#1 \/ p x y
!  ;;

!let exists_square =
!  fun p : real -> real -> prop =>
!  exists x1 : [-1, 1],
!  exists y1 : [-1, 1],
!  (square x1 y1)#0 /\ p x1 y1
!;;

let test_prop = 
  fun x1 : real =>
  fun x2 : real =>
  x1 < x2
  ;;

                
