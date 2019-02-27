#use "examples/orep.asd";;

! K-representation

let forall_k E (shape : (E -> bool) -> bool) (p : E -> bool) : bool = shape p;;

! existential quantifier for a shape
let exists_k E (shape : (E -> bool) -> bool) (p : E -> bool) : bool =
  ~ (shape (fun x : E => ~ (p x)))
  ;;

let scale_x_y_k (cx cy : real)
    (shape : (real^2 -> bool) -> bool) =
  fun p : real^2 -> bool =>
  shape (fun x : real^2 => p (cx * x#0, cy * x#1));;

let scale_k (c : real) = scale_x_y_k c c;;

let translate_k (tx : real^2) (shape : (real^2 -> bool) -> bool)
    : (real^2 -> bool) -> bool =
    fun p : real^2 -> bool => shape (fun x : real^2 => p (x#0 + tx#0, x#1 + tx#1));;

let empty_k E (p : E -> bool) : bool = tt;;

let union_k (k1 k2 : (real^2 -> bool) -> bool) =
  fun P : real^2 -> bool => k1 P && k2 P;;

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

let map E F (f : E -> F) (shape : (E -> bool) -> bool) : (F -> bool) -> bool =
  fun P : F -> bool => shape (fun x : E => P (f x));;

let intersect_ok E (o : E -> bool) (k : (E -> bool) -> bool) =
  fun P : E -> bool => k (fun x : E => ~ (o x) || P x);;

let unit_disk_k : (real^2 -> bool) -> bool =
  intersect_ok {real^2} unit_disk unit_square_k;;

let point E (x : E) =
  fun p : E -> bool => p x ;;

let unit_interval (p : real -> bool) : bool =
  mkbool (forall x : [0, 1], is_true (p x)) (exists x : [0, 1], is_false (p x));;

let unit_cone : (real^3 -> bool) -> bool =
  compact_union {real} unit_interval {real^3} (fun x : real =>
  compact_union {real^2} (scale_k x unit_disk_k) {real^3} (fun yz : real^2 =>
  point {real^3} (x, yz#0, yz#1)));;

let neq (x y : real) : bool =
  mkbool (x <> y) False;;

let exterior E (neq : E -> E -> bool) (shape : (E -> bool) -> bool) : E -> bool =
  fun x : E => shape (fun y : E => neq x y);;

let minkowski_sum E (plus : E -> E -> E)
  (s1 s2 : (E -> bool) -> bool) : (E -> bool) -> bool =
  fun P : E -> bool => s1 (fun x : E => s2 (fun y :  E => P (plus x y)));;

let is_empty (E : type) (k : (E -> bool) -> bool) : bool = k (fun x : E => ff);;

let forall_ks E (k : (E -> bool) -> bool) (p : E -> prop) : prop =
  is_true (k (fun x : E => mkbool (p x) False));;

let exists_ks E (k : (E -> bool) -> bool) (p : E -> prop) : prop =
  is_false (k (fun x : E => mkbool False (p x)));;

let disjoint E (neq : E -> E -> prop) (k1 k2 : (E -> bool) -> bool) : prop =
  forall_ks {E} k1 (fun x : E => forall_ks {E} k2 (fun y : E => neq x y));;

let neq_R2 (x y : real^2) : prop = x#0 <> y#0 \/ x#1 <> y#1;;
let neq_R3 (x y : real^3) : prop = x#0 <> y#0 \/ x#1 <> y#1 \/ x#2 <> y#2;;

! Two shapes are disjoint if they share no points in common.
! This is checking that separation is > 0, but is computationally more efficient.
! forall (x2,y2) in shape2 forall (x1,y1) in shape1 (x1 != x2 or y1 != y2)
let disjoint_R2 (k1 k2 : (real^2 -> bool) -> bool) : prop =
  disjoint {real^2} neq_R2 k1 k2;;

let disjoint_R3 (k1 k2 : (real^3 -> bool) -> bool) : prop =
  disjoint {real^3} neq_R3 k1 k2;;

! minimum distance between two shapes
let separation (shape1 shape2 : (real^2 -> bool) -> bool) : real =
  dedekind_cut (fun cutoff : real => (cutoff <b 0) ||
     (shape1 (fun x : real^2 =>
      shape2 (fun x' : real^2 =>
     (cutoff^2) <b ((x'#0 - x#0)^2 + (x'#1 - x#1)^2)))))
  ;;

let separation_dist E (d : E -> E -> real) (s1 s2 : (E -> bool) -> bool) : real =
  dedekind_cut (fun q : real => q <b 0 ||
     s1 (fun x : E => s2 (fun y : E => q <b d x y)));;

let directed_hausdorff_distance
    (shape1 shape2 : (real^2 -> bool) -> bool) : real =
  dedekind_cut (fun cutoff : real => cutoff <b 0 ||
     (exists_k {real^2} shape1 (fun x : real^2 =>
      forall_k {real^2} shape2 (fun x' : real^2 =>
     (cutoff^2) <b ((x'#0 - x#0)^2 + (x'#1 - x#1)^2)))))
  ;;

let directed_hausdorff_dist E (d : E -> E -> real) (s1 s2 : (E -> bool) -> bool) : real =
  dedekind_cut (fun cutoff : real => cutoff <b 0 ||
    exists_k {E} s1 (fun x : E => forall_k {E} s2 (fun y : E => cutoff <b d x y)));;

let max (a : real) (b : real) : real =
  dedekind_cut (fun x : real => x <b a || x <b b);;

! compute the hausdorff distance between two shapes.
! It is the max over every shape_point_separation
let hausdorff_distance (k1 k2 : (real^2 -> bool) -> bool) : real =
  max (directed_hausdorff_distance k1 k2)
      (directed_hausdorff_distance k2 k1);;

let hausdorff_dist E (d : E -> E -> real) (k1 k2 : (E -> bool) -> bool) : real =
  max (directed_hausdorff_dist {E} d k1 k2)
      (directed_hausdorff_dist {E} d k2 k1);;

let kshape_neq E (neq : E -> E -> prop) (k1 k2 : (E -> bool) -> bool) : prop =
    exists_ks {E} k1 (fun x1 : E =>
    forall_ks {E} k2 (fun x2 : E => neq x1 x2))
  \/ exists_ks {E} k2 (fun x2 : E =>
    forall_ks {E} k1 (fun x1 : E => neq x1 x2));;


let intersect_k_implies_equals E
  (intersect_k : ((E -> bool) -> bool) -> ((E -> bool) -> bool) -> (E -> bool) -> bool)
  (x y : E) : bool
  = ~ (is_empty {E} (intersect_k (point {E} x) (point {E} y)));;

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

let is_contained_in E (k : (E -> bool) -> bool) (o : E -> bool) : bool =
  forall_k {E} k (fun x : E => o x);;

! Does one shape lie strictly inside another?
let shape_inside (A : type)
    (shape_1 shape_2 : ((A -> bool) -> bool) * (A -> bool)) =
      (shape_1#0) (fun x : A => (shape_2#1) x);;


let peq (x : real) (y : real) = mkbool False (x <> y);;

! interior and exterior for points
let point_R2 (x : real) (y : real) =
  (fun p : real^2 -> bool => p (x, y)
  , fun x_test : real^2 => peq x x_test#0 && peq y x_test#1)
  ;;

let empty_shape E =
   (empty_k {E}
   , fun x : E => ff);;


let scale_x_y_ok (cx : real) (cy : real)
  (shape : ((real^2 -> bool) -> bool) * (real^2 -> bool)) =
  (scale_x_y_k cx cy shape#0, scale_x_y cx cy shape#1);;


let minkowski_sum_o E (plus : E -> E -> E)
  (o : E -> bool) (k : (E -> bool) -> bool) : E -> bool =
  fun x : E => exists_k {E} k (fun delta : E => o (plus x delta));;

let minkowski_diff_o E (plus : E -> E -> E)
  (o : E -> bool) (k : (E -> bool) -> bool) : E -> bool =
  fun x : E => forall_k {E} k (fun delta : E => o (plus x delta));;




let integrate_unit_interval (f : real -> real) : real =
  int x : [0, 1], f x;;

let integral (a b : real) (f : real -> real) : real =
  let range = b - a in
  range * integrate_unit_interval (fun x : real => f (a + range * x));;

let indicator (b : bool) : real =
  dedekind_cut (fun q : real => q <b 0 || (b && q <b 1));;

let infimum (s : (real -> bool) -> bool) : real =
  dedekind_cut (fun q : real => s (fun x : real => q <b x));;

let supremum (s : (real -> bool) -> bool) : real =
  dedekind_cut (fun q : real => ~ (s (fun x : real => x <b q)));;

let volume (s : ((real -> bool) -> bool) * (real -> bool)) : real =
  integral (infimum s#0) (supremum s#0) (fun x : real => indicator (s#1 x));;



let bezier E (cvx_comb : real -> E -> E -> E)
  (p0 p1 p2 : E) : (E -> bool) -> bool =
  map {real} {E} (fun t : real => cvx_comb t (cvx_comb t p2 p1) (cvx_comb t p1 p0))
              unit_interval;;


let compact_union_o E (k : (E -> bool) -> bool) F (o : E -> F -> bool) : F -> bool =
  fun f : F => k (fun e : E => o e f);;

let compact_intersection_o E (k : (E -> bool) -> bool) F (o : E -> F -> bool) : F -> bool =
  fun f : F => exists_k {E} k (fun e : E => o e f);;
