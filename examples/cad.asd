#use "examples/orep.asd";;

type KShape E = (E -> bool) -> bool;;

! K-representation

let forall_k E (shape : KShape E) (p : E -> bool) : bool = shape p;;

! existential quantifier for a shape
let exists_k E (shape : KShape E) (p : E -> bool) : bool =
  ~ (shape (fun x : E => ~ (p x)))
  ;;

let scale_x_y_k (cx cy : real) (shape : KShape (real^2)) =
  fun p : real^2 -> bool =>
  shape (fun x : real^2 => p (cx * x#0, cy * x#1));;

let scale_k (c : real) = scale_x_y_k c c;;

let translate_k (tx : real^2) (shape : KShape (real^2))
    : KShape (real^2) =
    fun p : real^2 -> bool => shape (fun x : real^2 => p (x#0 + tx#0, x#1 + tx#1));;

let empty_k E (p : E -> bool) : bool = tt;;

let union_k (k1 k2 : KShape (real^2)) =
  fun P : real^2 -> bool => k1 P && k2 P;;

let compact_union E (i : KShape E) F (f : E -> KShape F)
  : KShape F
  = fun P : F -> bool => i (fun x : E => f x P);;

let forall_interval_sym (p : real -> bool) : bool =
  mkbool (forall x : [-1, 1], is_true (p x)) (exists x : [-1, 1], is_false (p x))
  ;;

let unit_square_k (p : real^2 -> bool) : bool =
  forall_interval_sym (fun x : real =>
  forall_interval_sym (fun y : real => p (x, y))
  );;

let map E F (f : E -> F) (shape : KShape E) : KShape F =
  fun P : F -> bool => shape (fun x : E => P (f x));;

let intersect_ok E (o : E -> bool) (k : KShape E) =
  fun P : E -> bool => k (fun x : E => ~ (o x) || P x);;

let unit_disk_k : KShape (real^2) =
  intersect_ok {real^2} unit_disk unit_square_k;;

let point E (x : E) =
  fun p : E -> bool => p x ;;

let unit_interval (p : real -> bool) : bool =
  mkbool (forall x : [0, 1], is_true (p x)) (exists x : [0, 1], is_false (p x));;

let unit_cone : KShape (real^3) =
  compact_union {real} unit_interval {real^3} (fun x : real =>
  compact_union {real^2} (scale_k x unit_disk_k) {real^3} (fun yz : real^2 =>
  point {real^3} (x, yz#0, yz#1)));;

let neq (x y : real) : bool =
  mkbool (x <> y) False;;

let exterior E (neq : E -> E -> bool) (shape : KShape E) : E -> bool =
  fun x : E => shape (fun y : E => neq x y);;

let minkowski_sum E (plus : E -> E -> E)
  (s1 s2 : KShape E) : KShape E =
  fun P : E -> bool => s1 (fun x : E => s2 (fun y :  E => P (plus x y)));;

let is_empty (E : type) (k : KShape E) : bool = k (fun x : E => ff);;

let forall_ks E (k : KShape E) (p : E -> prop) : prop =
  is_true (k (fun x : E => mkbool (p x) False));;

let exists_ks E (k : KShape E) (p : E -> prop) : prop =
  is_false (k (fun x : E => mkbool False (p x)));;

let disjoint E (neq : E -> E -> prop) (k1 k2 : KShape E) : prop =
  forall_ks {E} k1 (fun x : E => forall_ks {E} k2 (fun y : E => neq x y));;

let neq_R2 (x y : real^2) : prop = x#0 <> y#0 \/ x#1 <> y#1;;
let neq_R3 (x y : real^3) : prop = x#0 <> y#0 \/ x#1 <> y#1 \/ x#2 <> y#2;;

! Two shapes are disjoint if they share no points in common.
! This is checking that separation is > 0, but is computationally more efficient.
! forall (x2,y2) in shape2 forall (x1,y1) in shape1 (x1 != x2 or y1 != y2)
let disjoint_R2 (k1 k2 : KShape (real^2)) : prop =
  disjoint {real^2} neq_R2 k1 k2;;

let disjoint_R3 (k1 k2 : KShape (real^3)) : prop =
  disjoint {real^3} neq_R3 k1 k2;;

! minimum distance between two shapes
let separation (shape1 shape2 : KShape (real^2)) : real =
  dedekind_cut (fun cutoff : real => (cutoff <b 0) ||
     (shape1 (fun x : real^2 =>
      shape2 (fun x' : real^2 =>
     (cutoff^2) <b ((x'#0 - x#0)^2 + (x'#1 - x#1)^2)))))
  ;;

let separation_dist E (d : E -> E -> real) (s1 s2 : KShape E) : real =
  dedekind_cut (fun q : real => q <b 0 ||
     s1 (fun x : E => s2 (fun y : E => q <b d x y)));;

let directed_hausdorff_distance
    (shape1 shape2 : KShape (real^2)) : real =
  dedekind_cut (fun cutoff : real => cutoff <b 0 ||
     (exists_k {real^2} shape1 (fun x : real^2 =>
      forall_k {real^2} shape2 (fun x' : real^2 =>
     (cutoff^2) <b ((x'#0 - x#0)^2 + (x'#1 - x#1)^2)))))
  ;;

let directed_hausdorff_dist E (d : E -> E -> real) (s1 s2 : KShape E) : real =
  dedekind_cut (fun cutoff : real => cutoff <b 0 ||
    exists_k {E} s1 (fun x : E => forall_k {E} s2 (fun y : E => cutoff <b d x y)));;

let max (a : real) (b : real) : real =
  dedekind_cut (fun x : real => x <b a || x <b b);;

! compute the hausdorff distance between two shapes.
! It is the max over every shape_point_separation
let hausdorff_distance (k1 k2 : KShape (real^2)) : real =
  max (directed_hausdorff_distance k1 k2)
      (directed_hausdorff_distance k2 k1);;

let hausdorff_dist E (d : E -> E -> real) (k1 k2 : KShape E) : real =
  max (directed_hausdorff_dist {E} d k1 k2)
      (directed_hausdorff_dist {E} d k2 k1);;

let kshape_neq E (neq : E -> E -> prop) (k1 k2 : KShape E) : prop =
    exists_ks {E} k1 (fun x1 : E =>
    forall_ks {E} k2 (fun x2 : E => neq x1 x2))
  \/ exists_ks {E} k2 (fun x2 : E =>
    forall_ks {E} k1 (fun x1 : E => neq x1 x2));;

let convex_hull E (cvx_comb : real -> E -> E -> E) (k : KShape E) : KShape E =
  compact_union {E} k {E} (fun x : E =>
  compact_union {E} k {E} (fun y : E =>
  compact_union {real} unit_interval {E} (fun c : real =>
    point {E} (cvx_comb c x y))));;


let intersect_k_implies_equals E
  (intersect_k : KShape E -> KShape E -> KShape E)
  (x y : E) : bool
  = ~ (is_empty {E} (intersect_k (point {E} x) (point {E} y)));;

! Both O- and K-representation

let unit_square = (unit_square_k, rectangle 2 2);;

! unit disk centered at origin
let unit_disk_ok =
  (unit_disk_k, unit_disk)
;;

let translate_ok (tx : real^2)
    (shape : KShape (real^2) * OShape (real^2)) =
  (translate_k tx shape#0, translate tx shape#1);;

let union_ok
    (shape1 shape2 : KShape (real^2) * OShape (real^2)) =
  (union_k shape1#0 shape2#0, union {real^2} shape1#1 shape2#1);;

let is_contained_in E (k : KShape E) (o : OShape E) : bool =
  forall_k {E} k (fun x : E => o x);;

! Does one shape lie strictly inside another?
let shape_inside E
    (shape_1 shape_2 : KShape E * OShape E) =
      (shape_1#0) (fun x : E => (shape_2#1) x);;


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
  (o : OShape E) (k : KShape E) : OShape E =
  fun x : E => exists_k {E} k (fun delta : E => o (plus x delta));;

let minkowski_diff_o E (plus : E -> E -> E)
  (o : OShape E) (k : KShape E) : OShape E =
  fun x : E => forall_k {E} k (fun delta : E => o (plus x delta));;




let integrate_unit_interval (f : real -> real) : real =
  int x : [0, 1], f x;;

let integral (a b : real) (f : real -> real) : real =
  let range = b - a in
  range * integrate_unit_interval (fun x : real => f (a + range * x));;

let indicator (b : bool) : real =
  dedekind_cut (fun q : real => q <b 0 || (b && q <b 1));;

let infimum (s : KShape real) : real =
  dedekind_cut (fun q : real => s (fun x : real => q <b x));;

let supremum (s : KShape real) : real =
  dedekind_cut (fun q : real => ~ (s (fun x : real => x <b q)));;

let volume (s : KShape real * OShape real) : real =
  integral (infimum s#0) (supremum s#0) (fun x : real => indicator (s#1 x));;



let bezier E (cvx_comb : real -> E -> E -> E)
  (p0 p1 p2 : E) : KShape E =
  map {real} {E} (fun t : real => cvx_comb t (cvx_comb t p2 p1) (cvx_comb t p1 p0))
              unit_interval;;


let compact_union_o E (k : KShape E) F (o : E -> OShape F) : OShape F =
  fun f : F => k (fun e : E => o e f);;

let compact_intersection_o E (k : KShape E) F (o : E -> OShape F) : OShape F =
  fun f : F => exists_k {E} k (fun e : E => o e f);;
