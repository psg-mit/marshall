#use "examples/bool.asd";;

! A shape is a function from R^2 to a pair of predicates.
! The first predicate says if a point in the plane is strictly
! *inside* the shape, and the second says it if it strictly *outside*

let translate (trans_x : real * real) (shape : real * real -> bool) =
  fun x : real * real =>
    shape (x#0 - trans_x#0, x#1 - trans_x#1)
;;

! rectangle centered at the origin
let rectangle (width : real) (height : real) =
  fun x : real * real =>
      (- width  / 2) <b x#0  &&  x#0 <b (width  / 2)
  &&  (- height / 2) <b x#1  &&  x#1 <b (height / 2)
;;

let forall_interval_sym (p : real -> bool) : bool =
  mkbool (forall x : [-1, 1], is_true (p x)) (exists x : [-1, 1], is_false (p x))
  ;;

let unit_square_k (p : real * real -> bool) : bool =
  forall_interval_sym (fun x : real =>
  forall_interval_sym (fun y : real => p (x, y))
  );;

let unit_square = (unit_square_k, rectangle 2 2);;

! scaling centered at the origin!
! factor should be a *positive* real number
let scale (factor : real) (shape : real * real -> bool) =
  fun x : real * real =>
  shape (x#0 / factor, x#1 / factor)
;;

let scale_x_y (cx : real) (cy : real)
    (shape : real * real -> bool) =
    fun x : real * real => shape (x#0 / cx, x#1 / cy);;

let scale_x_y_k (cx : real) (cy : real)
    (shape : (real * real -> bool) -> bool) =
  fun p : real * real -> bool =>
  shape (fun x : real * real => p (cx * x#0, cy * x#1));;


let scale_x_y_ok (cx : real) (cy : real)
  (shape : ((real * real -> bool) -> bool) * (real * real -> bool)) =
  (scale_x_y_k cx cy shape#0, scale_x_y cx cy shape#1);;

! unit disk centered at origin
let unit_disk = fun x : real * real => x#0^2 + x#1^2 <b 1;;

let unit_disk_k =
  fun p : real * real -> bool =>
  forall_interval_sym (fun x : real =>
  forall_interval_sym (fun y : real =>
  negb (unit_disk (x, y)) || p (x, y)
  ));;

let rightmost_extent_2 (shape : (real * real -> bool) -> bool) : real =
  dedekind_cut (fun x : real => negb (shape (fun x' : real * real => x'#0 <b x)))
  ;;

let rightmost_extent_3 (shape : real * real -> bool) : real =
  cut x
     left (exists x' : real, x < x' /\ (exists y' : real, is_true (shape (x', y'))))
     right (forall x' : [-3, 3], x' < x \/ (forall y' : [-3, 3], is_false (shape (x', y'))))
;;

! Compute the intersection of two shapes.
let intersection (A : type) (shape_1 : A -> bool) (shape_2 : A -> bool) =
  fun x : A =>
  shape_1 x && shape_2 x
  ;;

! Compute the union of two shapes.
let union (A : type) (shape_1 : A -> bool) (shape_2 : A -> bool) =
  fun x : A =>
  shape_1 x || shape_2 x
  ;;

! The set-theoretic complement of a shape. Not sure where
! this may come in handy.
let complement (A : type) (shape : A -> bool) =
  fun x : A =>
  ~ (shape x)
  ;;

! this is only upper semicomputable
let distance_from_point (shape : real * real -> bool) (x : real * real) : real =
    cut z
      left  (z < 0)
      right (z > 0 /\ (exists dx : real, exists dy : real, is_true (shape (x#0 + dx, x#1 + dy)) /\ (dx * dx + dy * dy < z)))
;;

! Is a shape nonempty?
let nonempty (shape : real * real -> bool) : prop =
  exists x : real, exists y : real, is_true (shape (x, y))
;;

! existential quantifier for a shape

let forall_k (shape : (real * real -> bool) -> bool) (p : real * real -> bool) : bool = shape p;;

let exists_k (shape : (real * real -> bool) -> bool) (p : real * real -> bool) : bool =
  ~ (shape (fun x : real * real => ~ (p x)))
  ;;

! Do two shapes overlap?
let overlaps (shape_1 : real * real -> bool) (shape_2 : real * real -> bool) : prop =
  nonempty (intersection {real * real} shape_1 shape_2)
;;

! Does one shape lie strictly inside another?
let shape_inside (A : type)
    (shape_1 : ((A -> bool) -> bool) * (A -> bool))
    (shape_2 : ((A-> bool) -> bool) * (A -> bool)) =
      (shape_1#0) (fun x : A => (shape_2#1) x);;

! The unit disk is nonempty
let disk_nonempty = nonempty unit_disk;;
! ANS: disk_nonempty : prop = True


! The intersection of the unit disk and unit square, translated
! by (5,5) is nonempty
let disk_int_square_nonempty =
  nonempty (translate (5, 5) (intersection {real * real} unit_disk (rectangle 1 1)));;
! ANS: disk_int_square_nonempty : prop = True

! The intersection of the unit square at the origin, and
! a unit disk centered at (5,5) is empty
let disk_int_square_empty =
  overlaps (translate (5, 5) unit_disk) (rectangle 1 1);;
! ANS: disk_int_square_empty : prop = False

let minkowski_ball (eps : real) (u : real * real -> prop) : real * real -> prop =
  fun x : real * real =>
  exists dx : real,
  exists dy : real,
  dx^2 + dy^2 < eps /\ u (x#0 + dx, x#1 + dy)
;;

! (3/4, 0) is in the unit disk but not the unit square
let test_point =
  is_true (unit_disk (3/4, 0)) /\ is_false (rectangle 1 1 (3/4, 0));;
! ANS: test_point : prop = True

let restrict (U : prop) (x : real) : real =
  cut z
     left U /\ z < x
     right U /\ x < z
;;

let restrictb (U : prop) (x : bool) : bool =
  mkbool (U /\ is_true x) (U /\ is_false x)
  ;;

let grow_in_eps (eps : real) (shape : real * real -> bool) =
  fun x : real * real =>
  mkbool (minkowski_ball eps (fun x' : real * real => is_true (shape x')) x)
         (is_false (shape x))
;;

let grow_out_eps (eps : real) (shape : real * real -> bool) =
  fun x : real * real =>
  mkbool (is_true (shape x))
         (minkowski_ball eps (fun x' : real * real => is_false (shape x')) x)
;;

! Try a point on the border of the rectangle, having
! thickened the "in" part by a radius of 0.1.
let is_in_rect_in = grow_in_eps 0.1 (rectangle 2 2) (1, 1);;
! ANS: is_in_rect_in : bool = mkbool True False

! Try a point on the border of the rectangle, having
! thickened the "out" part by a radius of 0.1.
let is_in_rect_out = grow_out_eps 0.1 (rectangle 2 2) (1, 1);;
! ANS: is_in_rect_out : real = mkbool False True

let peq (x : real) (y : real) = mkbool False (x <> y);;

! interior and exterior for points
let point (x : real) (y : real) =
  (fun p : real * real -> bool => p (x, y)
  , fun x_test : real * real => peq x x_test#0 && peq y x_test#1)
  ;;

let empty_shape (A : type) =
   (fun p : A -> bool => tt
   , fun x : A => ff);;
