#use "examples/orep.asd";;

! K-representation

type KShape E = (E -> bool) -> bool;;

! Constructions

let unit_interval : KShape real =
  fun p : real -> bool =>
  mkbool (Forall x : [0, 1], is_true (p x)) (Exists x : [0, 1], is_false (p x));;

let forall_interval_sym (p : real -> bool) : bool =
  mkbool (Forall x : [-1, 1], is_true (p x)) (Exists x : [-1, 1], is_false (p x))
  ;;

let unit_square (p : real^2 -> bool) : bool =
  forall_interval_sym (fun x : real =>
  forall_interval_sym (fun y : real => p (x, y))
  );;

let intersect E (k : KShape E) (o : OShape E) : KShape E =
  fun P : E -> bool => k (fun x : E => ~ (o x) || P x);;

let unit_disk : KShape (real^2) =
  intersect {real^2} unit_square unit_disk_o;;

let point E (x : E) =
  fun p : E -> bool => p x ;;

let compact_union E (i : KShape E) F (f : E -> KShape F)
  : KShape F
  = fun P : F -> bool => i (fun x : E => f x P);;

let product E F (ke : KShape E) (kf : KShape F) : KShape (E * F) =
  fun P : E * F -> bool => ke (fun e : E => kf (fun f : F => P (e, f)));;

let empty E (p : E -> bool) : bool = tt;;

let union (k1 k2 : KShape (real^2)) =
  fun P : real^2 -> bool => k1 P && k2 P;;

let difference E (k : KShape E) (o : OShape E) : KShape E =
  intersect {E} k (complement_o {E} o);;

let map E F (f : E -> F) (shape : KShape E) : KShape F =
  fun P : F -> bool => shape (fun x : E => P (f x));;

let bezier E (cvx_comb : real -> E -> E -> E)
  (p0 p1 p2 : E) : KShape E =
  map {real} {E} (fun t : real => cvx_comb t (cvx_comb t p2 p1) (cvx_comb t p1 p0))
              unit_interval;;


! Analyses

let forall E (k : KShape E) (p : E -> bool) : bool = k p;;

! existential quantifier for a shape
let exists E (k : KShape E) (p : E -> bool) : bool =
  ~ (k (fun x : E => ~ (p x)))
  ;;

let forall_s E (k : KShape E) (p : E -> prop) : prop =
  is_true (k (fun x : E => mkbool (p x) False));;

let exists_s E (k : KShape E) (p : E -> prop) : prop =
  is_false (k (fun x : E => mkbool False (p x)));;

let is_empty (E : type) (k : KShape E) : bool = k (fun x : E => ff);;

let infimum (s : KShape real) : real =
  dedekind_cut (fun q : real => s (fun x : real => q <b x));;

let supremum (s : KShape real) : real =
  dedekind_cut (fun q : real => ~ (s (fun x : real => x <b q)));;

let disjoint E (neq : E -> E -> prop) (k1 k2 : KShape E) : prop =
  forall_s {E} k1 (fun x : E => forall_s {E} k2 (fun y : E => neq x y));;

let kshape_neq E (neq : E -> E -> prop) (k1 k2 : KShape E) : prop =
    exists_s {E} k1 (fun x1 : E =>
    forall_s {E} k2 (fun x2 : E => neq x1 x2))
  \/ exists_s {E} k2 (fun x2 : E =>
    forall_s {E} k1 (fun x1 : E => neq x1 x2));;

let separation_dist E (d : E -> E -> real) (s1 s2 : KShape E) : real =
  dedekind_cut (fun q : real => q <b 0 ||
     s1 (fun x : E => s2 (fun y : E => q <b d x y)));;

let directed_hausdorff_dist E (d : E -> E -> real) (s1 s2 : KShape E) : real =
  dedekind_cut (fun cutoff : real => cutoff <b 0 ||
    exists {E} s1 (fun x : E => forall {E} s2 (fun y : E => cutoff <b d x y)));;

let max (a : real) (b : real) : real =
  dedekind_cut (fun x : real => x <b a || x <b b);;

let hausdorff_dist E (d : E -> E -> real) (k1 k2 : KShape E) : real =
  max (directed_hausdorff_dist {E} d k1 k2)
      (directed_hausdorff_dist {E} d k2 k1);;

! Other

let scale_x_y (cx cy : real) (shape : KShape (real^2)) =
  fun p : real^2 -> bool =>
  shape (fun x : real^2 => p (cx * x#0, cy * x#1));;

let scale (c : real) = scale_x_y c c;;

let translate (tx : real^2) (shape : KShape (real^2))
    : KShape (real^2) =
    fun p : real^2 -> bool => shape (fun x : real^2 => p (x#0 + tx#0, x#1 + tx#1));;

let unit_cone : KShape (real^3) =
  compact_union {real} unit_interval {real^3} (fun x : real =>
  compact_union {real^2} (scale x unit_disk) {real^3} (fun yz : real^2 =>
  point {real^3} (x, yz#0, yz#1)));;

let neq (x y : real) : bool =
  mkbool (x <> y) False;;

let exterior E (neq : E -> E -> bool) (shape : KShape E) : E -> bool =
  fun x : E => shape (fun y : E => neq x y);;

let minkowski_sum E (plus : E -> E -> E)
  (s1 s2 : KShape E) : KShape E =
  fun P : E -> bool => s1 (fun x : E => s2 (fun y :  E => P (plus x y)));;

let neq_R2 (x y : real^2) : prop = x#0 <> y#0 \/ x#1 <> y#1;;
let neq_R3 (x y : real^3) : prop = x#0 <> y#0 \/ x#1 <> y#1 \/ x#2 <> y#2;;

! Two shapes are disjoint if they share no points in common.
! This is checking that separation is > 0, but is computationally more efficient.
! Forall (x2,y2) in shape2 Forall (x1,y1) in shape1 (x1 != x2 or y1 != y2)
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

let directed_hausdorff_distance
    (shape1 shape2 : KShape (real^2)) : real =
  dedekind_cut (fun cutoff : real => cutoff <b 0 ||
     (exists {real^2} shape1 (fun x : real^2 =>
      forall {real^2} shape2 (fun x' : real^2 =>
     (cutoff^2) <b ((x'#0 - x#0)^2 + (x'#1 - x#1)^2)))))
  ;;

! compute the hausdorff distance between two shapes.
! It is the max over every shape_point_separation
let hausdorff_distance (k1 k2 : KShape (real^2)) : real =
  max (directed_hausdorff_distance k1 k2)
      (directed_hausdorff_distance k2 k1);;


let convex_hull E (cvx_comb : real -> E -> E -> E) (k : KShape E) : KShape E =
  compact_union {E} k {E} (fun x : E =>
  compact_union {E} k {E} (fun y : E =>
  compact_union {real} unit_interval {E} (fun c : real =>
    point {E} (cvx_comb c x y))));;


let intersect_k_implies_equals E
  (intersect_k : KShape E -> KShape E -> KShape E)
  (x y : E) : bool
  = ~ (is_empty {E} (intersect_k (point {E} x) (point {E} y)));;