#use "examples/bool.asd";;

! O-representation

! A shape is a function from R^2 to a pair of predicates.
! The first predicate says if a point in the plane is strictly
! *inside* the shape, and the second says it if it strictly *outside*

! Implement line with an interior in the direction of the normal.
let line (nx : real) (ny : real) =
      fun x : real^2 =>
      0 <b (nx * x#0 + ny * x#1);;

let translate (trans_x : real^2) (shape : real^2 -> bool) =
  fun x : real^2 =>
    shape (x#0 - trans_x#0, x#1 - trans_x#1)
;;

! rectangle centered at the origin
let rectangle (width : real) (height : real) =
  fun x : real^2 =>
      (- width  / 2) <b x#0  &&  x#0 <b (width  / 2)
  &&  (- height / 2) <b x#1  &&  x#1 <b (height / 2)
;;

! scaling centered at the origin!
! factor should be a *positive* real number
let scale (factor : real) (shape : real^2 -> bool) =
  fun x : real^2 =>
  shape (x#0 / factor, x#1 / factor)
;;

let scale_x_y (cx : real) (cy : real)
    (shape : real^2 -> bool) =
    fun x : real^2 => shape (x#0 / cx, x#1 / cy);;

! unit disk centered at origin
let unit_disk = fun x : real^2 => x#0^2 + x#1^2 <b 1;;

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
let nonempty (shape : real^2 -> bool) : prop =
  exists x : real, exists y : real, is_true (shape (x, y))
;;

! Do two shapes overlap?
let overlaps (shape_1 : real^2 -> bool) (shape_2 : real^2 -> bool) : prop =
  nonempty (intersection {real^2} shape_1 shape_2)
;;

! K-representation

let forall_k E (shape : (E -> bool) -> bool) (p : E -> bool) : bool = shape p;;

! existential quantifier for a shape
let exists_k E (shape : (E -> bool) -> bool) (p : E -> bool) : bool =
  ~ (shape (fun x : E => ~ (p x)))
  ;;

let scale_x_y_k (cx : real) (cy : real)
    (shape : (real^2 -> bool) -> bool) =
  fun p : real^2 -> bool =>
  shape (fun x : real^2 => p (cx * x#0, cy * x#1));;

let scale_k (c : real) = scale_x_y_k c c;;

let translate_k (tx : real^2) (shape : (real^2 -> bool) -> bool)
    : (real^2 -> bool) -> bool =
    fun p : real^2 -> bool => shape (fun x : real^2 => p (x#0 + tx#0, x#1 + tx#1));;

let empty_shape_k E (p : E -> bool) : bool = tt;;

let union_k (shape1 shape2 : (real^2 -> bool) -> bool) =
  fun P : real^2 -> bool => shape1 P && shape2 P;;

let compact_union E (i : (E -> bool) -> bool) F (f : E -> (F -> bool) -> bool) 
  : (F -> bool) -> bool 
  = fun P : F -> bool => i (fun x : E => f x P);;

let forall_interval_sym (p : real -> bool) : bool =
  mkbool (forall x : [-1, 1], is_true (p x)) (exists x : [-1, 1], is_false (p x))
  ;;

let unit_square_k (p : real^2 -> bool) : bool =
  forall_interval_sym (fun x : real =>
  forall_interval_sym (fun y : real => p (x, y))
  );;

let closed_of_compact (oshape : real^2 -> bool) (kshape : (real^2 -> bool) -> bool) =
  fun P : real^2 -> bool =>
  kshape (fun x : real^2 =>
    ~ oshape x || P x
  );;

let unit_disk_k =
  fun p : real^2 -> bool =>
  unit_square_k (fun x : real^2 => ~ unit_disk x || p x);;

let point_k E (x : E) =
  fun p : E -> bool => p x ;;

let unit_interval (p : real -> bool) : bool =
  mkbool (forall x : [0, 1], is_true (p x)) (exists x : [0, 1], is_false (p x));;

let unit_cone : (real^3 -> bool) -> bool =
  compact_union {real} unit_interval {real^3} (fun x : real =>
  compact_union {real^2} (scale_k x unit_disk_k) {real^3} (fun yz : real^2 =>
  point_k {real^3} (x, yz#0, yz#1)));;

let neq (x : real) (y : real) : bool =
  mkbool (x <> y) False;;

let exterior E (neq : E -> E -> bool) (shape : (E -> bool) -> bool) : E -> bool =
  fun x : E => shape (fun y : E => neq x y);;

let minkowski_sum E (plus : E -> E -> E)
  (s1 s2 : (E -> bool) -> bool) : (E -> bool) -> bool =
  fun P : E -> bool => s1 (fun x : E => s2 (fun y :  E => P (plus x y)));;

! let is_empty (E : type) (s : (E -> bool) -> bool) : bool = s (fun x : E => ff);;

! Two shapes are separated if they share no points in common.
! This is checking that separation is > 0, but is computationally more efficient.
! forall (x2,y2) in shape2 forall (x1,y1) in shape1 (x1 != x2 or y1 != y2)
let is_separated (shape1 shape2 : (real^2 -> bool) -> bool) : bool =
  shape1 (fun x1 : real^2 =>
  shape2 (fun x2 : real^2 =>
          neq x1#0 x2#0 || neq x1#1 x2#1))
  ;;

let separated E (neq : E -> E -> prop) (s1 s2 : (E -> bool) -> bool) : prop =
  is_true (s1 (fun x : E => s2 (fun y : E => mkbool (neq x y) False)));;

! minimum distance between two shapes
let separation (shape1 shape2 : (real^2 -> bool) -> bool) : real =
  dedekind_cut (fun cutoff : real => (cutoff <b 0) ||
     (shape1 (fun x : real^2 =>
      shape2 (fun x' : real^2 =>
     (cutoff^2) <b ((x'#0 - x#0)^2 + (x'#1 - x#1)^2)))))
  ;;

let directed_hausdorff_distance
    (shape1 shape2 : (real^2 -> bool) -> bool) : real =
  dedekind_cut (fun cutoff : real => cutoff <b 0 ||
     (forall_k {real^2} shape1 (fun x : real^2 =>
      exists_k {real^2} shape2 (fun x' : real^2 =>
     (cutoff^2) <b ((x'#0 - x#0)^2 + (x'#1 - x#1)^2)))))
  ;;

let directed_hausdorff_dist E (d : E -> E -> real) (s1 s2 : (E -> bool) -> bool) : real =
  dedekind_cut (fun cutoff : real => cutoff <b 0 ||
    forall_k {E} s1 (fun x : E => exists_k {E} s2 (fun y : E => cutoff <b d x y)));;

let max (a : real) (b : real) : real =
  dedekind_cut (fun x : real => x <b a || x <b b);;

! compute the hausdorff distance between two shapes.
! It is the max over every shape_point_separation
let hausdorff_distance (shape1 shape2 : (real^2 -> bool) -> bool) : real =
  max (directed_hausdorff_distance shape1 shape2)
      (directed_hausdorff_distance shape2 shape1);;

let hausdorff_dist E (d : E -> E -> real) (s1 s2 : (E -> bool) -> bool) : real =
  max (directed_hausdorff_dist {E} d s1 s2)
      (directed_hausdorff_dist {E} d s2 s1);;


! Both O- and K-representation

let unit_square = (unit_square_k, rectangle 2 2);;

! unit disk centered at origin
let unit_disk_ok =
  (unit_disk_k, unit_disk)
;;

let translate_ok (tx : real^2)
    (shape : ((real^2 -> bool) -> bool) * (real^2 -> bool)) =
  (translate_k tx shape#0, translate tx shape#1);;

let union_ok
    (shape1 shape2 : ((real^2 -> bool) -> bool) * (real^2 -> bool)) =
  (union_k shape1#0 shape2#0, union {real^2} shape1#1 shape2#1);;


! Does one shape lie strictly inside another?
let shape_inside (A : type)
    (shape_1 shape_2 : ((A -> bool) -> bool) * (A -> bool)) =
      (shape_1#0) (fun x : A => (shape_2#1) x);;


let peq (x : real) (y : real) = mkbool False (x <> y);;

! interior and exterior for points
let point (x : real) (y : real) =
  (fun p : real^2 -> bool => p (x, y)
  , fun x_test : real^2 => peq x x_test#0 && peq y x_test#1)
  ;;

let empty_shape E =
   (empty_shape_k {E}
   , fun x : E => ff);;


let scale_x_y_ok (cx : real) (cy : real)
  (shape : ((real^2 -> bool) -> bool) * (real^2 -> bool)) =
  (scale_x_y_k cx cy shape#0, scale_x_y cx cy shape#1);;
