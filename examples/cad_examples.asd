#use "./cad.asd";;
#use "./sqrt.asd";;

let minkowski_ball (eps : real) (u : real^2 -> prop) : real^2 -> prop =
  fun x : real^2 =>
  Exists dx : real,
  Exists dy : real,
  dx^2 + dy^2 < eps /\ u (x#0 + dx, x#1 + dy)
;;

let grow_in_eps (eps : real) (shape : real^2 -> bool) =
  fun x : real^2 =>
  mkbool (minkowski_ball eps (fun x' : real^2 => is_true (shape x')) x)
         (is_false (shape x))
;;

let grow_out_eps (eps : real) (shape : real^2 -> bool) =
  fun x : real^2 =>
  mkbool (is_true (shape x))
         (minkowski_ball eps (fun x' : real^2 => is_false (shape x')) x)
;;

! Try a point on the border of the rectangle, having
! thickened the "in" part by a radius of 0.1.
let is_in_rect_in = grow_in_eps 0.1 (rectangle_o 2 2) (1, 1);;
! ANS: is_in_rect_in : bool = mkbool True False

! Try a point on the border of the rectangle, having
! thickened the "out" part by a radius of 0.1.
let is_in_rect_out = grow_out_eps 0.1 (rectangle_o 2 2) (1, 1);;
! ANS: is_in_rect_out : real = mkbool False True


! The intersection of the unit disk and unit square, translated
! by (5,5) is nonempty
let disk_int_square_nonempty =
  nonempty_R2 (translate_o (5, 5) (intersection_o {real^2} unit_disk (rectangle_o 1 1)));;
! ANS: disk_int_square_nonempty : prop = True

! The intersection of the unit square at the origin, and
! a unit disk centered at (5,5) is empty
let disk_int_square_empty =
  overlaps (translate_o (5, 5) unit_disk) (rectangle_o 1 1);;
! ANS: disk_int_square_empty : prop = False

! The unit disk is nonempty
let disk_nonempty = nonempty_R2 unit_disk;;
! ANS: disk_nonempty : prop = True

let rightmost_extent_2 (shape : (real^2 -> bool) -> bool) : real =
  dedekind_cut (fun x : real => negb (shape (fun x' : real^2 => x'#0 <b x)))
  ;;

let rightmost_extent_3 (shape : real^2 -> bool) : real =
  cut x
     left (Exists x' : real, x < x' /\ (Exists y' : real, is_true (shape (x', y'))))
     right (Forall x' : [-3, 3], x' < x \/ (Forall y' : [-3, 3], is_false (shape (x', y'))))
;;

! this is only upper semicomputable
let distance_from_point (shape : real^2 -> bool) (x : real^2) : real =
    cut z
      left  (z < 0)
      right (z > 0 /\ (Exists dx : real, Exists dy : real, is_true (shape (x#0 + dx, x#1 + dy)) /\ (dx * dx + dy * dy < z)))
;;


let restrict (U : prop) (x : real) : real =
  cut z
     left U /\ z < x
     right U /\ x < z
;;

let restrictb (U : prop) (x : bool) : bool =
  mkbool (U /\ is_true x) (U /\ is_false x)
  ;;

! (3/4, 0) is in the unit disk but not the unit square
let test_point =
  is_true (unit_disk (3/4, 0)) /\ is_false (rectangle_o 1 1 (3/4, 0));;
! ANS: test_point : prop = True

! Sloped line
let sloped_line (m : real) = line -1 (1/m) ;;

! Bad vertical line
let vertical_line = fun x : real^2 => x#0 <b 0;;

! Create a triangle centered at the origin
let triangle =
    let top_right = translate_o (0, 1) (sloped_line -3) in
    let top_left = translate_o (0, 1) (complement_o {real^2} (sloped_line 3)) in
    let bottom = translate_o (0 , -(sqrt 3) / 6) (line 0 1) in
    intersection_o {real^2} (intersection_o {real^2} top_right top_left) bottom
    ;;  ! intersection take more params

! Create a unit square centered at the origin with lines
let square_as_intersection =
  let right_side = translate_o (1/2, 0) vertical_line in
  let left_side = translate_o (-1/2, 0) (complement_o {real^2} vertical_line) in
  let top = translate_o (0, 1/2) (complement_o {real^2} (line 0 1)) in
  let bottom = translate_o (0, -1/2) (line 0 1) in
  let vertical_strip = intersection_o {real^2} left_side right_side in
  let horizontal_strip = intersection_o {real^2} top bottom in
  intersection_o {real^2} horizontal_strip vertical_strip
  ;;

let square2 (x : real) (y : real) : bool =
     ((-0.5) <b x && x <b 0.5) && ((-0.5) <b y && y <b 0.5)
    ;;

! Implementation of reflection of a shape across a line
! The line is ax + by + c = 0
! https://drive.google.com/file/d/0By83v5TWkGjvb2tuekNSUFo3cFE/view
let reflect =
    fun a : real =>
    fun b : real =>
    fun c : real =>
    fun shape : real^2 -> bool =>
    fun x : real =>
    fun y : real =>
    shape ((x * (a^2 - b^2) - 2*b*(a*y+c))/(a^2+b^2), (y*(b^2-a^2) - 2*a*(b*x+c))/(a^2+b^2))
    ;;


! Idea: maybe a reflect in/reflect out for reflection to move to interior. Might also include a minimal glide reflection.
! Idea: Use the roots of unity for common fixed rotations.
