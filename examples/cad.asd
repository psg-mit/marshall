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

let quantify_unit_square =
  fun p : real -> real -> prop =>
  ( forall x : [-1, 1], forall y : [-1, 1], p x y
  , exists x : [-1, 1], exists y : [-1, 1], p x y
  );;

let unit_square =
  (quantify_unit_square, rectangle 2 2)
  ;;

let scale_x_y_shape =
  fun cx : real =>
  fun cy : real =>
  fun shape : ((real -> real -> prop) -> prop * prop)
            * (real -> real -> prop * prop) =>
  (fun p : real -> real -> prop =>
    shape#0 (fun x : real => fun y : real => (p x y))
  , fun x : real => fun y : real =>
    shape#1 (x / cx) (y / cy)
  );;

! unit disk centered at origin
let circle =
  fun x : real =>
  fun y : real =>
  (x * x + y * y < 1, x * x + y * y > 1)
;;

let forall_circle =
  fun p : real -> real -> prop =>
  forall x : [-1, 1],
  forall y : [-1, 1],
  (circle x y)#1 \/ p x y
;;

! Can't get the border - would need sine and cosine.
let exists_circle_int =
  fun p : real -> real -> prop =>
  exists x : [-1, 1],
  exists y : [-1, 1],
  (circle x y)#0 /\ p x y
;;

let rightmost_extent =
  fun shape : ((real -> real -> prop) -> prop * prop)
            * (real -> real -> prop * prop) =>
  cut x
     left  (((shape#0) (fun x' : real => fun y' : real => x < x'))#1)
     right (((shape#0) (fun x' : real => fun y' : real => x' < x))#0)
;;

let rightmost_extent_2 =
  fun shape : ((real -> real -> prop) -> prop * prop) =>
  cut x
     left  ((shape (fun x' : real => fun y' : real => x < x'))#1)
     right ((shape (fun x' : real => fun y' : real => x' < x))#0)
;;

let rightmost_extent_3 =
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

! Does one shape lie strictly inside another?
!let shape_inside =
!  fun shape_1 : ((real -> real -> prop) -> prop * prop)
!            * (real -> real -> prop * prop) =>
!  fun shape_2 : ((real -> real -> prop) -> prop * prop)
!            * (real -> real -> prop * prop) =>
!  shape_1#0 (fun x : real => fun y : real => (shape_2#0 x y)#0);;

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
  dx^2 + dy^2 < eps /\ u (x + dx) (y + dy)
;;

! (3/4, 0) is in the unit disk but not the unit square
let test_point =
  (circle (3/4) 0)#0 /\ (rectangle 1 1 (3/4) 0)#1;;
! ANS: test_point : prop = True

let restrict =
  fun U : prop =>
  fun x : real =>
  cut z
     left U /\ z < x
     right U /\ x < z
;;

let restrictb =
  fun U : prop =>
  fun x : bool =>
  mkbool (U /\ is_true x) (U /\ is_false x)
  ;;

let is_in_bool =
  fun shape : real -> real -> prop * prop =>
  fun x : real =>
  fun y : real =>
  (  restrictb ((shape x y)#0) (mkbool True False)
  || restrictb ((shape x y)#1) (mkbool False True)
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

let to_bool =
  fun p : prop * prop =>
  mkbool p#0 p#1 ;;

let shape_to_bool =
  fun shape : real -> real -> prop * prop =>
  fun x : real =>
  fun y : real =>
  to_bool (shape x y);;