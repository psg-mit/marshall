#use "examples/cad.asd";;

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
  closed_of_compact (ellipse a b) (scale_x_y_k a b unit_square_k);;

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
    dedekind_cut (fun q : real => exists_k kshape (fun x : real^2 =>
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

let unit_circle =
  fun P : real^2 -> bool =>
  forall_interval_sym (fun cost : real =>
  let pos_sint = sqrt (1 - cost^2) in
  let neg_sint = - pos_sint in
  P (cost, pos_sint) && P (cost, neg_sint)
  )
  ;;

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

let check_conditions : bool =
  let shifted_square = translate_k (3, 0) square_quantified#0 in
  forall_k unit_circle (fun angle : real^2 =>

    ! Rotate the cam
    let curr_cam = rotate_k angle cam in

    let curr_piston = translate_k (amount_to_translate_piston angle) piston in

    let cam_piston = union_k curr_cam curr_piston in
    is_separated cam_piston shifted_square
  )
  ;;

let rectangle_k (width height : real) =
  scale_x_y_k (width / 2) (height / 2) unit_square_k;;

let infimum (s : (real -> bool) -> bool) : real =
  dedekind_cut (fun q : real => s (fun x : real => q <b x));;

let supremum (s : (real -> bool) -> bool) : real =
  dedekind_cut (fun q : real => ~ (s (fun x : real => x <b q)));;

let map (A B : type) (f : A -> B) (shape : (A -> bool) -> bool) : (B -> bool) -> bool =
  fun P : B -> bool => shape (fun x : A => P (f x));;

let cam_piston (angle : real^2) : (real^2 -> bool) -> bool =
  let cam = rotate_k angle (translate_k (1, 0) (ellipse_k 5 3)) in
  ! put piston just to the right of the cam
  let piston = translate_to_touch_axis (1, 0) cam (rectangle_k 1 4) in
  union_k cam piston;;

let enclosure_piece : (real^2 -> bool) -> bool = translate_k (7, 0) (rectangle_k 1 2);;

let collision_safe : bool = forall_k unit_circle (fun angle : real^2 =>
  is_separated (cam_piston angle) enclosure_piece);;

let cam_pistion_separation_dist : real = supremum
  (map {real^2} {real} (fun angle : real^2 => separation (cam_piston angle) enclosure_piece) unit_circle);;
