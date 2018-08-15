#use "examples/sqrt.asd";;
#use "examples/cad.asd";;
#use "examples/jesse_cad.asd";;
#use "examples/jesse_bounding_box.asd";;
#use "examples/jesse_car.asd";; 

! Create a cam and piston system:
! https://en.wikipedia.org/wiki/Camshaft
! The cam is an ellipse centered at the origin that rotates over time,
! with a circle with it's center along the positive x-axis and it's 
! leftmost point touching the ellipse on the positive x-axis.

! NOTE: Quantifiers should be generalized to all a and b, but 
! cannot because marshall doesn't all variables in foralls.
let ellipse =
  fun a : real =>
  fun b : real =>
  fun x : real =>
  fun y : real =>
  (x * x / (a * a)  + y * y / (b * b) < 1, x * x / (a * a)  + y * y / (b * b) > 1)
  ;;

let a = 0.75;;
let b = 0.5;;
let cam_unquantified = ellipse a b;; 

! Rotates the given shape
let rotate_shape_cos_sin =
  fun shape : (real -> real -> prop * prop)
            * ((real -> real -> prop) -> prop * prop) =>
  fun cos : real =>
  fun sin : real =>

  ! Produce new shape
  (fun x : real => fun y : real =>
    
    ! Apply rotation matrix
    let x_new = cos * x - sin * y in  
    let y_new = sin * x + cos * y in 
    
    shape#0 (x_new) (y_new)
    ,
  fun p' : real -> real -> prop => 
    shape#1 (fun x : real => fun y : real =>
      ! Apply inverse rotation matrix
      let x_new = cos * x + sin * y in  
      let y_new = - sin * x + cos * y in         
      p' (x_new) (y_new))
  )
  ;;

! A higher order function that computes the quantifiers for a given shape.
let forall_exists_shape = 
  fun shape : real -> real -> prop * prop =>
  fun p' : real -> real -> prop =>
  let forall_shape =   
    fun p : real -> real -> prop =>
    forall x : [-1, 1],
    forall y : [-1, 1],
    (shape x y)#1 \/ p x y in
  let exists_shape =
    fun p : real -> real -> prop =>
    exists x1 : [-1, 1],
    exists y1 : [-1, 1],
    (shape x1 y1)#0 /\ p x1 y1 in 
  (forall_shape p', exists_shape p')
  ;;

! Set up the cam and piston
let forall_exists_cam = forall_exists_shape cam_unquantified;;
let cam = (cam_unquantified, forall_exists_cam);;
let piston = translate_shape_x_y (scale_shape_x_y circle_quantified 0.5 0.5) 1.25 0;;


let check_conditions = 
  forall cost : [-1,1],
  let pos_sint = sqrt (1 - cost*cost) in
  let neg_sint = - sqrt (1 - cost*cost) in

  ! Location of the point on the ellipse intersected with the positive x-axis 
  ! We use the parametric form of the ellipse
  let point_on_pos_x_axis =  a*cost + b*pos_sint in 
  let other_point_on_pos_x_axis = a*cost + b*neg_sint in 
  
  ! Rotate the piston
  let curr_cam = rotate_shape_cos_sin cam cost pos_sint in
  let other_curr_cam = rotate_shape_cos_sin cam cost neg_sint in 

  ! Move the circle around with the ellipse always touching the point
  ! on the positive x-axis 
  let amount_to_translate_piston = 
    point_on_pos_x_axis - 0.75 in 
  let other_amount_to_translate_piston = 
    other_point_on_pos_x_axis - 0.75 in
  
  let curr_piston = translate_shape_x_y piston amount_to_translate_piston 0 in
  let other_curr_piston = translate_shape_x_y piston amount_to_translate_piston 0 in
  
  let cam_piston = union_quantified curr_cam curr_piston in 
  let other_cam_piston = union_quantified other_curr_cam other_curr_piston in 

  let shifted_square = translate_shape_x_y square_quantified 3 0 in  
  is_separated cam_piston shifted_square /\
  is_separated other_cam_piston shifted_square
  ;;
  

