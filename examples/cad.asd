#use "examples/bool.asd";;

! O-representation

! A shape is a function from R^2 to a pair of predicates.
! The first predicate says if a point in the plane is strictly
! *inside* the shape, and the second says it if it strictly *outside*

! Implement line with an interior in the direction of the normal.
let line (nx : real) (ny : real) =
      fun x : real * real =>
      0 <b (nx * x#0 + ny * x#1);;

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

! scaling centered at the origin!
! factor should be a *positive* real number
let scale (factor : real) (shape : real * real -> bool) =
  fun x : real * real =>
  shape (x#0 / factor, x#1 / factor)
;;

let scale_x_y (cx : real) (cy : real)
    (shape : real * real -> bool) =
    fun x : real * real => shape (x#0 / cx, x#1 / cy);;

! unit disk centered at origin
let unit_disk = fun x : real * real => x#0^2 + x#1^2 <b 1;;

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

! Is a shape nonempty?
let nonempty (shape : real * real -> bool) : prop =
  exists x : real, exists y : real, is_true (shape (x, y))
;;

! Do two shapes overlap?
let overlaps (shape_1 : real * real -> bool) (shape_2 : real * real -> bool) : prop =
  nonempty (intersection {real * real} shape_1 shape_2)
;;

! K-representation

let forall_k (shape : (real * real -> bool) -> bool) (p : real * real -> bool) : bool = shape p;;

! existential quantifier for a shape
let exists_k (shape : (real * real -> bool) -> bool) (p : real * real -> bool) : bool =
  ~ (shape (fun x : real * real => ~ (p x)))
  ;;

let scale_x_y_k (cx : real) (cy : real)
    (shape : (real * real -> bool) -> bool) =
  fun p : real * real -> bool =>
  shape (fun x : real * real => p (cx * x#0, cy * x#1));;

let translate_k (tx : real * real) (shape : (real * real -> bool) -> bool)
    : (real * real -> bool) -> bool =
    fun p : real * real -> bool => shape (fun x : real * real => p (x#0 + tx#0, x#1 + tx#1));;

let empty_shape_k (A : type) (p : A -> bool) : bool = tt;;

let union_k
    (shape1 : (real * real -> bool) -> bool)
    (shape2 : (real * real -> bool) -> bool) =
  fun P : real * real -> bool => shape1 P && shape2 P;;

let forall_interval_sym (p : real -> bool) : bool =
  mkbool (forall x : [-1, 1], is_true (p x)) (exists x : [-1, 1], is_false (p x))
  ;;

let unit_square_k (p : real * real -> bool) : bool =
  forall_interval_sym (fun x : real =>
  forall_interval_sym (fun y : real => p (x, y))
  );;

let unit_disk_k =
  fun p : real * real -> bool =>
  unit_square_k (fun x : real * real => ~ unit_disk x || p x);;

let point_k (A : type) (x : A) =
  fun p : A -> bool => p x ;;

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
  dedekind_cut (fun cutoff : real => (cutoff <b 0) ||
     (shape1 (fun x : real * real =>
      shape2 (fun x' : real * real =>
     (cutoff^2) <b ((x'#0 - x#0)^2 + (x'#1 - x#1)^2)))))
  ;;


! Both O- and K-representation

let unit_square = (unit_square_k, rectangle 2 2);;

! unit disk centered at origin
let unit_disk_ok =
  (unit_disk_k, unit_disk)
;;

let translate_ok (tx : real * real)
    (shape : ((real * real -> bool) -> bool) * (real * real -> bool)) =
  (translate_k tx shape#0, translate tx shape#1);;

let union_ok
    (shape1 : ((real * real -> bool) -> bool) * (real * real -> bool))
    (shape2 : ((real * real -> bool) -> bool) * (real * real -> bool)) =
  (union_k shape1#0 shape2#0, union {real * real} shape1#1 shape2#1);;


! Does one shape lie strictly inside another?
let shape_inside (A : type)
    (shape_1 : ((A -> bool) -> bool) * (A -> bool))
    (shape_2 : ((A -> bool) -> bool) * (A -> bool)) =
      (shape_1#0) (fun x : A => (shape_2#1) x);;


let peq (x : real) (y : real) = mkbool False (x <> y);;

! interior and exterior for points
let point (x : real) (y : real) =
  (fun p : real * real -> bool => p (x, y)
  , fun x_test : real * real => peq x x_test#0 && peq y x_test#1)
  ;;

let empty_shape (A : type) =
   (empty_shape_k {A}
   , fun x : A => ff);;


let scale_x_y_ok (cx : real) (cy : real)
  (shape : ((real * real -> bool) -> bool) * (real * real -> bool)) =
  (scale_x_y_k cx cy shape#0, scale_x_y cx cy shape#1);;
