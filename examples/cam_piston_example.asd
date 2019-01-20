#use "examples/quantified_interior_exterior_cad.asd";;

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
  fun x : real * real =>
  x#0^2 / a^2  + x#1^2 / b^2  <b 1
  ;;

let a = 0.75;;
let b = 0.5;;
let cam_unquantified = ellipse a b;;

! Rotates the given shape
let rotate =
  fun cos_sin : real * real =>
  fun shape : ((real * real -> bool) -> bool) * (real * real -> bool) =>
  let cos = cos_sin#0 in
  let sin = cos_sin#1 in

  ! Produce new shape
  (fun p' : real * real -> bool =>
    shape#0 (fun x : real * real =>
      ! Apply rotation matrix
      let x_new = cos * x#0 + sin * x#1 in
      let y_new = - sin * x#0 + cos * x#1 in
      p' (x_new, y_new))
  ,
    fun x : real * real =>

    ! Apply inverse rotation matrix
    let x_new = cos * x#0 - sin * x#1 in
    let y_new = sin * x#0 + cos * x#1 in

    shape#1 (x_new, y_new)
  )
  ;;

let closed_of_compact =
  fun oshape : real * real -> bool =>
  fun kshape : (real * real -> bool) -> bool =>
  fun P : real * real -> bool =>
  kshape (fun x : real * real =>
    oshape x || P x
  );;

! Set up the cam and piston
let forall_exists_cam = closed_of_compact cam_unquantified quantify_unit_square;;
let cam = (forall_exists_cam, cam_unquantified);;
let piston = translate_ok (1.25, 0) (scale_x_y_ok 0.5 0.5 circle_quantified);;

let forall_circle1d =
  fun P : real * real -> bool =>
  forall_interval_sym (fun cost : real =>
  let pos_sint = sqrt (1 - cost^2) in
  let neg_sint = - pos_sint in
  P (cost, pos_sint) && P (cost, neg_sint)
  )
  ;;

let check_conditions =
  let shifted_square = translate_ok (3, 0) square_quantified in
  forall_circle1d (fun angle : real * real =>

    ! Rotate the cam
    let curr_cam = rotate angle cam in

    ! Location of the point on the ellipse intersected with the positive x-axis
    ! We use the parametric form of the ellipse
    let cost = angle#0 in let sint = angle#1 in
    let point_on_pos_x_axis =  a*cost + b*sint in

    ! Move the circle around with the ellipse always touching the point
    ! on the positive x-axis
    let amount_to_translate_piston = point_on_pos_x_axis - 0.75 in

    let curr_piston = translate_ok (amount_to_translate_piston, 0) piston in

    let cam_piston = union_ok curr_cam curr_piston in
    is_separated cam_piston#0 shifted_square#0
  )
  ;;


