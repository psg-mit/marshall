#use "examples/cad.asd";;
#use "examples/sqrt.asd";;

! takes two points as tuples and returns their euclidean distance
let euclidean_dist = 
    fun p1 : real * real =>
    fun p2 : real * real =>
    sqrt ((p1#0-p2#0)*(p1#0-p2#0) + (p1#1-p2#1)*(p1#1-p2#1))
    ;;

! Implement line with an interior in the direction of the normal.
let line =
      fun nx : real =>
      fun ny : real =>
      fun x  : real =>
      fun y  : real =>
      (nx * x + ny * y > 0, nx * x + ny * y < 0)
  ;;

! Sloped line
let sloped_line =
      fun m : real =>
      line -1 (1/m)
  ;;

! Bad vertical line
let vertical_line =
    fun x : real =>
    fun y : real =>
    (x<0,x>0)
    ;;


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
    (-0.5 < x /\ x < 0.5 /\ -0.5 < y /\ y < 0.5,
     -0.5 > x \/ x > 0.5 \/ -0.5 > y \/ y > 0.5)
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
    fun shape : real -> real -> prop * prop =>
    fun x : real =>
    fun y : real =>
    shape ((x * (a*a - b*b) - 2*b*(a*y+c))/(a*a+b*b))    ((y*(b*b-a*a) - 2*a*(b*x+c))/(a*a+b*b))
    ;;


! Idea: maybe a reflect in/reflect out for reflection to move to interior. Might also include a minimal glide reflection.
! Idea: Use the roots of unity for common fixed rotations.
