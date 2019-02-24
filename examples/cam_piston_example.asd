#use "examples/cad.asd";;
#use "examples/stdlib.asd";;

! Create a cam and piston system:
! https://en.wikipedia.org/wiki/Camshaft
! The cam is an ellipse centered at the origin that rotates over time,
! with a circle with it's center along the positive x-axis and it's
! leftmost point touching the ellipse on the positive x-axis.

! NOTE: Quantifiers should be generalized to all a and b, but
! cannot because marshall doesn't all variables in foralls.
let ellipse (a b : real) =
  fun x : real^2 => x#0^2 / a^2  + x#1^2 / b^2  <b 1;;

let ellipse_k (a b : real) =
  intersect_ok (ellipse a b) (scale_x_y_k a b unit_square_k);;

let a = 0.75;;
let b = 0.5;;
let cam_unquantified = ellipse a b;;

let rotate_k (angle : real^2) (shape : (real^2 -> bool) -> bool) =
  let cost = angle#0 in
  let sint = angle#1 in
  fun P : real^2 -> bool =>
    shape (fun x : real^2 =>
      ! Apply rotation matrix
      let x_new = cost * x#0 + sint * x#1 in
      let y_new = - sint * x#0 + cost * x#1 in
      P (x_new, y_new));;

let rotate (angle : real^2) (shape : real^2 -> bool) =
  let cost = angle#0 in
  let sint = angle#1 in
    fun x : real^2 =>
    ! Apply inverse rotation matrix
    let x_new = cost * x#0 - sint * x#1 in
    let y_new = sint * x#0 + cost * x#1 in
    shape (x_new, y_new);;


! Rotates the given shape
let rotate_ok (angle : real^2) (shape : ((real^2 -> bool) -> bool) * (real^2 -> bool)) =
  (rotate_k angle shape#0, rotate angle shape#1);;

let axis_extent (n : real^2) (kshape : (real^2 -> bool) -> bool) : real =
    dedekind_cut (fun q : real => exists_k {real^2} kshape (fun x : real^2 =>
      q <b n#0 * x#0 + n#1 * x#1
    ));;

let translate_to_touch_axis
    (n : real^2)   ! should be a unit vector
    (reference shape : (real^2 -> bool) -> bool)
    : (real^2 -> bool) -> bool =
    let dist = axis_extent (-n#0, -n#1) shape + axis_extent n reference in
    translate_k (dist * n#0, dist * n#1) shape
    ;;


! Set up the cam and piston
let cam = ellipse_k a b;;
let piston = translate_k (1.25, 0) (scale_x_y_k 0.5 0.5 unit_disk_k);;

let unit_circle = fun P : real^2 -> bool =>
  unit_interval (fun t : real => let theta = twopi * t in P (cos theta, sin theta));;

let amount_to_translate_piston (angle : real^2) : real^2 =
    ! Location of the point on the ellipse intersected with the positive x-axis
    ! We use the parametric form of the ellipse
    let cost = angle#0 in let sint = angle#1 in
    let point_on_pos_x_axis =  a*cost + b*sint in

    ! Move the circle around with the ellipse always touching the point
    ! on the positive x-axis
    (point_on_pos_x_axis - 0.75, 0)
    ;;

let square_quantified = scale_x_y_ok 0.5 0.5 unit_square;;

let check_conditions : prop =
  let shifted_square = translate_k (3, 0) square_quantified#0 in
  forall_ks {real^2} unit_circle (fun angle : real^2 =>

    ! Rotate the cam
    let curr_cam = rotate_k angle cam in

    let curr_piston = translate_k (amount_to_translate_piston angle) piston in

    let cam_piston = union_k curr_cam curr_piston in
    disjoint_R2 cam_piston shifted_square
  )
  ;;

let rectangle_k (width height : real) =
  scale_x_y_k (width / 2) (height / 2) unit_square_k;;

let ellipse_width = 5;;
let ellipse_height = 3;;
let rectangle_width = 4;;

let translation_amount' (angle : real^2) : real =
  let cam_right_end = ellipse_width * angle#0 + ellipse_height * angle#1 in
  let rectangle_left_end = - rectangle_width / 2 in
  cam_right_end - rectangle_left_end;;

let cam_piston (angle : real^2) : (real^2 -> bool) -> bool =
  let cam = rotate_k angle (ellipse_k ellipse_width ellipse_height) in
  ! put piston just to the right of the cam
  let piston = translate_k (translation_amount' angle, 0) (rectangle_k rectangle_width 1) in
  !let piston = translate_to_touch_axis (1, 0) cam (rectangle_k rectangle_width 1) in
  union_k cam piston;;

let cam_piston_o (angle : real^2) : real^2 -> bool =
  let cam = rotate angle (ellipse ellipse_width ellipse_height) in
  ! put piston just to the right of the cam
  let piston = translate (translation_amount' angle, 0) (rectangle rectangle_width 1) in
  !let piston = translate_to_touch_axis (1, 0) cam (rectangle_k rectangle_width 1) in
  union {real^2} cam piston;;

let enclosure_piece : (real^2 -> bool) -> bool = translate_k (10, 0) (rectangle_k 5 2);;

let collision_safe : prop = forall_ks {real^2} unit_circle (fun angle : real^2 =>
  disjoint_R2 (cam_piston angle) enclosure_piece);;

let cam_piston_separation_dist : real = infimum
  (map {real^2} {real} (fun angle : real^2 => separation (cam_piston angle) enclosure_piece) unit_circle);;

! #plot 32 (scale (1/8) (cam_piston_o (1, 0)));;
