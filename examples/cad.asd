#use "examples/bool.asd";;

! A shape is a function from R^2 to a pair of predicates.
! The first predicate says if a point in the plane is strictly
! *inside* the shape, and the second says it if it strictly *outside*

let translate =
  fun trans_x : real =>
  fun trans_y : real =>
  fun shape : real -> real -> bool =>
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
  andb (andb (lt (- width  / 2) x) (lt x (width / 2)))
       (andb (lt (- height / 2) y) (lt y (height / 2)))
;;

let forall_interval_sym =
  fun p : real -> bool =>
  mkbool (forall x : [-1, 1], is_true (p x)) (exists x : [-1, 1], is_false (p x))
  ;;

let quantify_unit_square =
  fun p : real -> real -> bool =>
  forall_interval_sym (fun x : real =>
  forall_interval_sym (fun y : real => p x y)
  );;

let unit_square =
  (quantify_unit_square, rectangle 2 2)
  ;;

! scaling centered at the origin!
! factor should be a *positive* real number
let scale =
  fun factor : real =>
  fun shape : real -> real -> bool =>
  fun x : real =>
  fun y : real =>
  shape (x / factor) (y / factor)
;;

let scale_x_y_shape =
  fun cx : real =>
  fun cy : real =>
  fun shape : ((real -> real -> bool) -> bool)
            * (real -> real -> bool) =>
  (fun p : real -> real -> bool =>
    shape#0 (fun x : real => fun y : real => p (cx * x) (cy * y))
  , fun x : real => fun y : real =>
    shape#1 (x / cx) (y / cy)
  );;

! unit disk centered at origin
let circle = fun x : real => fun y : real => lt (x^2 + y^2) 1;;

let forall_circle =
  fun p : real -> real -> bool =>
  forall_interval_sym (fun x : real =>
  forall_interval_sym (fun y : real =>
  orb (negb (circle x y)) (p x y)))
;;

let rightmost_extent_2 =
  fun shape : (real -> real -> bool) -> bool =>
  dedekind_cut (fun x : real => negb (shape (fun x' : real => fun y' : real => lt x' x)))
  ;;

let rightmost_extent =
  fun shape : ((real -> real -> bool) -> bool)
            * (real -> real -> bool) =>
  rightmost_extent_2 (shape#0);;

let rightmost_extent_3 =
  fun shape : real -> real -> prop * prop =>
  cut x
     left (exists x' : real, x < x' /\ (exists y' : real, (shape x' y')#0))
     right (forall x' : [-3, 3], x' < x \/ (forall y' : [-3, 3], (shape x' y')#1))
;;

! Compute the intersection of two shapes.
let intersection =
  fun shape_1 : real -> real -> bool =>
  fun shape_2 : real -> real -> bool =>
  fun x : real =>
  fun y : real =>
  andb (shape_1 x y) (shape_2 x y)
  ;;

! Compute the union of two shapes.
let union =
  fun shape_1 : real -> real -> bool =>
  fun shape_2 : real -> real -> bool =>
  fun x : real =>
  fun y : real =>
  orb (shape_1 x y) (shape_2 x y)
  ;;

! The set-theoretic complement of a shape. Not sure where
! this may come in handy.
let complement =
  fun shape : real -> real -> bool =>
  fun x : real =>
  fun y : real =>
  negb (shape x y)
  ;;

! this is only upper semicomputable
let distance_from_point =
  fun shape : real -> real -> bool =>
  fun x : real =>
  fun y : real =>
    cut z
      left  (z < 0)
      right (z > 0 /\ (exists dx : real, exists dy : real, is_true (shape (x + dx) (y + dy)) /\ (dx * dx + dy * dy < z)))
;;

! Is a shape nonempty?
let nonempty =
  fun shape : real -> real -> bool =>
  exists x : real, exists y : real, is_true (shape x y)
;;

! existential quantifier for a shape
let exists_shape =
  fun shape : ((real -> real -> bool) -> bool)
             * (real -> real -> bool) =>
  fun p : real -> real -> bool =>
  negb (shape#0 (fun x : real => fun y : real => negb (p x y)))
  ;;

! Do two shapes overlap?
let overlaps =
  fun shape_1 : real -> real -> bool =>
  fun shape_2 : real -> real -> bool =>
  nonempty (intersection shape_1 shape_2)
;;

! Does one shape lie strictly inside another?
let shape_inside =
  fun shape_1 : ((real -> real -> bool) -> bool)
            * (real -> real -> bool) =>
  fun shape_2 : ((real -> real -> bool) -> bool)
            * (real -> real -> bool) =>
  (shape_1#0) (fun x : real => fun y : real => (shape_2#1) x y);;

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
  is_true (circle (3/4) 0) /\ is_false (rectangle 1 1 (3/4) 0);;
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

let grow_in_eps =
  fun eps : real =>
  fun shape : real -> real -> bool =>
  fun x : real =>
  fun y : real =>
  mkbool (minkowski_ball eps (fun x' : real => fun y' : real => is_true (shape x' y')) x y)
         (is_false (shape x y))
;;

let grow_out_eps =
  fun eps : real =>
  fun shape : real -> real -> bool =>
  fun x : real =>
  fun y : real =>
  mkbool (is_true (shape x y))
         (minkowski_ball eps (fun x' : real => fun y' : real => is_false (shape x' y')) x y)
;;

! Try a point on the border of the rectangle, having
! thickened the "in" part by a radius of 0.1.
let is_in_rect_in = grow_in_eps 0.1 (rectangle 2 2) 1 1;;
! ANS: is_in_rect_in : bool = mkbool True False

! Try a point on the border of the rectangle, having
! thickened the "out" part by a radius of 0.1.
let is_in_rect_out = grow_out_eps 0.1 (rectangle 2 2) 1 1;;
! ANS: is_in_rect_out : real = mkbool False True

let peq = fun x : real => fun y : real => mkbool False (x <> y);;

! interior and exterior for points
let point =
  fun x : real => fun y : real =>
  (fun p : real -> real -> bool => p x y
  , fun x_test : real => fun y_test : real => andb (peq x x_test) (peq y y_test))
  ;;

let empty_shape =
   (fun p : real -> real -> bool => tt
   , fun x : real => fun y : real => ff);;