#use "examples/cad.asd";;
#use "examples/sqrt.asd";;

! Implement line with an interior in the direction of the normal.
let line (nx : real) (ny : real) =
      fun x : real * real =>
      0 <b (nx * x#0 + ny * x#1);;

! Sloped line
let sloped_line (m : real) = line -1 (1/m) ;;

! Bad vertical line
let vertical_line = fun x : real * real => x#0 <b 0;;


! Create a triangle centered at the origin
let triangle =
    let top_right = translate (0, 1) (sloped_line -3) in
    let top_left = translate (0, 1) (complement(sloped_line 3)) in
    let bottom = translate (0 , -(sqrt 3) / 6) (line 0 1) in
    intersection (intersection top_right top_left) bottom
    ;;  ! intersection take more params

let square (x : real) (y : real) : bool =
     ((-0.5) <b x && x <b 0.5) && ((-0.5) <b y && y <b 0.5)
    ;;

! Create a unit square centered at the origin with lines
let square =
  let right_side = translate (1/2, 0) vertical_line in
  let left_side = translate (-1/2, 0) (complement vertical_line) in
  let top = translate (0, 1/2) (complement (line 0 1)) in
  let bottom = translate (0, -1/2) (line 0 1) in
  let vertical_strip = intersection left_side right_side in
  let horizontal_strip = intersection top bottom in
  intersection horizontal_strip vertical_strip
  ;;

! Implementation of reflection of a shape across a line
! The line is ax + by + c = 0
! https://drive.google.com/file/d/0By83v5TWkGjvb2tuekNSUFo3cFE/view
let reflect =
    fun a : real =>
    fun b : real =>
    fun c : real =>
    fun shape : real * real -> bool =>
    fun x : real =>
    fun y : real =>
    shape ((x * (a^2 - b^2) - 2*b*(a*y+c))/(a^2+b^2), (y*(b^2-a^2) - 2*a*(b*x+c))/(a^2+b^2))
    ;;


! Idea: maybe a reflect in/reflect out for reflection to move to interior. Might also include a minimal glide reflection.
! Idea: Use the roots of unity for common fixed rotations.




! ---------- Set Up the Shapes ----------

let square_quantified = scale_x_y_ok 0.5 0.5 unit_square;;

! unit disk centered at origin
let unit_disk_ok =
  (unit_disk_k, unit_disk)
;;

let translate_k (tx : real * real) (shape : (real * real -> bool) -> bool)
    : (real * real -> bool) -> bool =
    fun p : real * real -> bool => shape (fun x : real * real => p (x#0 + tx#0, x#1 + tx#1));;

let translate_ok (tx : real * real)
    (shape : ((real * real -> bool) -> bool) * (real * real -> bool)) =
  (translate_k tx shape#0, translate tx shape#1);;

let union_k
    (shape1 : (real * real -> bool) -> bool)
    (shape2 : (real * real -> bool) -> bool) =
  fun P : real * real -> bool => shape1 P && shape2 P;;

let union_ok
    (shape1 : ((real * real -> bool) -> bool) * (real * real -> bool))
    (shape2 : ((real * real -> bool) -> bool) * (real * real -> bool)) =
  (union_k shape1#0 shape2#0, union shape1#1 shape2#1);;

let max (a : real) (b : real) : real =
  dedekind_cut (fun x : real => (x <b a) || (x <b b));;

let neq (x : real) (y : real) : bool =
  mkbool (x <> y) False;;

! Two shapes are separated if they share no points in common.
! This is checking that separation is > 0, but is computationally more efficient.
! forall (x2,y2) in shape2 forall (x1,y1) in shape1 (x1 != x2 or y1 != y2)
let is_separated (shape1 : (real * real -> bool) -> bool)
                 (shape2 : (real * real -> bool) -> bool) : bool =
  shape1 (fun x1 : real * real =>
  shape2 (fun x2 : real * real =>
          neq x1#0 x2#0 || neq x1#1 x2#1))
  ;;

! minimum distance between two shapes
let separation (shape1 : (real * real -> bool) -> bool)
               (shape2 : (real * real -> bool) -> bool) : real =
  dedekind_cut (fun cutoff : real => orb (lt cutoff 0)
     (shape1 (fun x : real * real =>
      shape2 (fun x' : real * real =>
     (cutoff^2) <b ((x'#0 - x#0)^2 + (x'#1 - x#1)^2)))))
  ;;
