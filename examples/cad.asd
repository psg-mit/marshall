! A shape is a function from R^2 to a pair of predicates.
! The first predicate says if a point in the plane is strictly
! *inside* the shape, and the second says it if it strictly *outside*

let translate =
  fun trans_x : real =>
  fun trans_y : real =>
  fun shape : real -> real -> prop * prop =>
  fun x : real =>
  fun y : real =>
    shape (x - trans_x) (y - trans_y)
;;

! rectangle centered at the origin
let rectangle =
  fun width : real =>
  fun height : real =>
  fun x : real =>
  fun y : real =>
  (  - width  / 2 < x /\ x < width  / 2
  /\ - height / 2 < y /\ y < height / 2
  ,  - width  / 2 > x \/ x > width  / 2
  \/ - height / 2 > y \/ y > height / 2
  )
;;

! unit disk centered at origin
let circle =
  fun x : real =>
  fun y : real =>
  (x * x + y * y < 1, x * x + y * y > 1)
;;

let circle_compact =
  (-1, 1, -1, 1, circle);;

let rightmost_extent =
  fun shape : real -> real -> prop * prop =>
  cut x
     left (exists x' : real, x < x' /\ (exists y' : real, (shape x' y')#0))
     right (forall x' : [-3, 3], x' < x \/ (forall y' : [-3, 3], (shape x' y')#1))
;;


! Compute the intersection of two shapes.
let intersection =
  fun shape_1 : real -> real -> prop * prop =>
  fun shape_2 : real -> real -> prop * prop =>
  fun x : real =>
  fun y : real =>
  ((shape_1 x y)#0 /\ (shape_2 x y)#0,
   (shape_1 x y)#1 \/ (shape_2 x y)#1)
;;

! Compute the union of two shapes.
let union =
  fun shape_1 : real -> real -> prop * prop =>
  fun shape_2 : real -> real -> prop * prop =>
  fun x : real =>
  fun y : real =>
  ((shape_1 x y)#0 \/ (shape_2 x y)#0,
   (shape_1 x y)#1 /\ (shape_2 x y)#1)
;;

! The set-theoretic complement of a shape. Not sure where
! this may come in handy.
let complement =
  fun shape : real -> real -> prop * prop =>
  fun x : real =>
  fun y : real =>
  ((shape x y)#1, (shape x y)#0)
;;

! scaling centered at the origin!
! factor should be a *positive* real number
let scale =
  fun factor : real =>
  fun shape : real -> real -> prop * prop =>
  fun x : real =>
  fun y : real =>
  shape (x / factor) (y / factor)
;;

! this is only upper semicomputable
let distance_from_point =
  fun shape_in : real -> real -> prop =>
  fun shape_out : real -> real -> prop =>
  fun x : real =>
  fun y : real =>
    cut z
      left  (z < 0)
      right (z > 0 /\ (exists dx : real, exists dy : real, shape_in (x + dx) (y + dy) /\ (dx * dx + dy * dy < z)))
;;

! Is a shape nonempty?
let nonempty =
  fun shape : real -> real -> prop * prop =>
  exists x : real, exists y : real, (shape x y)#0
;;

! Do two shapes overlap?
let overlaps =
  fun shape_1 : real -> real -> prop * prop =>
  fun shape_2 : real -> real -> prop * prop =>
  nonempty (intersection shape_1 shape_2)
;;

! The unit disk is nonempty
let disk_nonempty = nonempty circle;;
! ANS: disk_nonempty : prop = True


! The intersection of the unit disk and unit square, translated
! by (5,5) is nonempty
let disk_int_square_nonempty =
  nonempty (translate 5 5 (intersection circle (rectangle 1 1)));;
! ANS: disk_int_square_nonempty : prop = True

! The intersection of the unit square at the origin, and
! a unit disk centered at (5,5) is empty
let disk_int_square_empty =
  overlaps (translate 5 5 circle) (rectangle 1 1);;
! ANS: disk_int_square_empty : prop = False

let minkowski_ball =
  fun eps : real =>
  fun u : real -> real -> prop =>
  fun x : real =>
  fun y : real =>
  exists dx : real,
  exists dy : real,
  dx^2 + dy^2 < 1 /\ u (x + dx) (y + dy)
;;

! (3/4, 0) is in the unit disk but not the unit square
let test_point =
  (circle (3/4) 0)#0 /\ (rectangle 1 1 (3/4) 0)#1;;
! ANS: test_point : prop = True

let is_in_bool =
  fun shape : real -> real -> prop * prop =>
  fun x : real =>
  fun y : real =>
  ( (shape x y)#0 ~> 1
  || (shape x y)#1 ~> 0
  )
;;

let grow_in_eps =
  fun eps : real =>
  fun shape : real -> real -> prop * prop =>
  fun x : real =>
  fun y : real =>
  (minkowski_ball eps (fun x' : real => fun y' : real => (shape x' y')#0) x y,
   (shape x y)#1)
;;

let grow_out_eps =
  fun eps : real =>
  fun shape : real -> real -> prop * prop =>
  fun x : real =>
  fun y : real =>
  ((shape x y)#0,
   minkowski_ball eps (fun x' : real => fun y' : real => (shape x' y')#1) x y)
;;

let is_in_bool =
  fun shape : real -> real -> prop * prop =>
  fun x : real =>
  fun y : real =>
  ( (shape x y)#0 ~> 1
  || (shape x y)#1 ~> 0
  )
;;

! Try a point on the border of the rectangle, having
! thickened the "in" part by a radius of 0.1.
let is_in_rect_in =
  is_in_bool (grow_in_eps 0.1 (rectangle 2 2)) 1 1;;
! ANS: is_in_rect_in : real = 1.0

! Try a point on the border of the rectangle, having
! thickened the "out" part by a radius of 0.1.
let is_in_rect_out =
  is_in_bool (grow_out_eps 0.1 (rectangle 2 2)) 1 1;;
! ANS: is_in_rect_out : real = 0.0