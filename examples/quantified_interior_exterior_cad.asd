#use "examples/cad.asd";;
#use "examples/sqrt.asd";;

! Implement line with an interior in the direction of the normal.
let line =
      fun nx : real => fun ny : real =>
      fun x  : real => fun y  : real =>
      lt 0 (nx * x + ny * y);;

! Sloped line
let sloped_line =
      fun m : real =>
      line -1 (1/m)
  ;;

! Bad vertical line
let vertical_line = fun x : real => fun y : real => lt x 0;;


! Create a triangle centered at the origin
let triangle =
    let top_right = translate 0 1 (sloped_line -3) in
    let top_left = translate 0 1 (complement(sloped_line 3)) in
    let bottom = translate 0 (-(sqrt 3) / 6) (line 0 1) in
    intersection (intersection top_right top_left) bottom
    ;;  ! intersection take more params

let square =
    fun x : real =>
    fun y : real =>
    andb (andb (lt (-0.5) x) (lt x 0.5))
         (andb (lt (-0.5) y) (lt y 0.5))
    ;;

! Create a unit square centered at the origin with lines
let square =
  let right_side = translate (1/2) 0 vertical_line in
  let left_side = translate (-1/2) 0 (complement vertical_line) in
  let top = translate 0 (1/2) (complement (line 0 1)) in
  let bottom = translate 0 (-1/2) (line 0 1) in
  let vertical_strip = intersection left_side right_side in
  let horizontal_strip = intersection top bottom in
  intersection horizontal_strip vertical_strip
  ;;

! Dot product
let dot =
    fun x1 : real =>
    fun y1 : real =>
    fun x2 : real =>
    fun y2 : real =>
    x1 * x2 + y1 * y2
    ;;

! Implementation of reflection of a shape across a line
! The line is ax + by + c = 0
! https://drive.google.com/file/d/0By83v5TWkGjvb2tuekNSUFo3cFE/view
let reflect =
    fun a : real =>
    fun b : real =>
    fun c : real =>
    fun shape : real -> real -> bool =>
    fun x : real =>
    fun y : real =>
    shape ((x * (a^2 - b^2) - 2*b*(a*y+c))/(a^2+b^2))    ((y*(b^2-a^2) - 2*a*(b*x+c))/(a^2+b^2))
    ;;


! Idea: maybe a reflect in/reflect out for reflection to move to interior. Might also include a minimal glide reflection.
! Idea: Use the roots of unity for common fixed rotations.




! ---------- Set Up the Shapes ----------

! unit disk centered at origin
let square_quantified = scale_x_y_shape 0.5 0.5 unit_square;;

! unit disk centered at origin
let circle_quantified =
  (forall_circle, circle)
;;

let translate_shape_x_y =
  fun shape : ((real -> real -> bool) -> bool)
            * (real -> real -> bool) =>
  fun tx : real =>
  fun ty : real =>
  (fun p' : real -> real -> bool =>
  shape#0 (fun x : real => fun y : real => p' (x + tx) (y + ty))
  , translate tx ty (shape#1)
  )
  ;;

let union_quantified =
  fun shape1 : ((real -> real -> bool) -> bool)
             * (real -> real -> bool) =>
  fun shape2 : ((real -> real -> bool) -> bool)
             * (real -> real -> bool) =>
  (fun pr : real -> real -> bool =>
   (andb (shape1#0 pr) (shape2#0 pr))
  , union (shape1#1) (shape2#1))
  ;;

let max = fun a : real => fun b : real =>
  dedekind_cut (fun x : real => orb (lt x a) (lt x b));;

let neq = fun x : real => fun y : real =>
  mkbool (x <> y) False;;

! Two shapes are separated if they share no points in common.
! This is checking that separation is > 0, but is computationally more efficient.
! forall (x2,y2) in shape2 forall (x1,y1) in shape1 (x1 != x2 or y1 != y2)
let is_separated =
  fun shape1 : ((real -> real -> bool) -> bool)
             * (real -> real -> bool) =>
  fun shape2 : ((real -> real -> bool) -> bool)
             * (real -> real -> bool) =>
  shape1#0 (fun x1 : real => fun y1 : real =>
            shape2#0 (fun x2 : real => fun y2 : real =>
                  orb (neq x1 x2) (neq y1 y2)))
  ;;

