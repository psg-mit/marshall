#use "examples/cad.asd";;
#use "examples/stdlib.asd";;

let cvx3 (c : real) (x y : real^3) : real^3
  = (x#0 + c * (y#0 - x#0)
    ,x#1 + c * (y#1 - x#1)
    ,x#2 + c * (y#2 - x#2));;

let triangle_k (x y z : real^3) : KShape (real^3) =
  compact_union {real} unit_interval {real^3} (fun a : real =>
  compact_union {real} unit_interval {real^3} (fun b : real =>
  point {real^3} (cvx3 a x (cvx3 b y z))));;

let union3 (s1 s2 : KShape (real^3)) (P : real^3 -> bool) : bool
  = s1 P && s2 P;;

let cone_mesh : KShape (real^3) =
           triangle_k (-5.31758e-17,1.0,-6.14666e-16) (-0.707107,0.707107,-7.11643e-16) (-1.2909e-16,0.0,1.0)
  `union3` triangle_k (-5.31758e-17,1.0,-6.14666e-16) (-1.2909e-16,0.0,1.0) (0.707107,0.707107,-5.17689e-16)
  `union3` triangle_k (1.0,1.22465e-16,-4.7752e-16) (0.707107,0.707107,-5.17689e-16) (-1.2909e-16,0.0,1.0)
  `union3` triangle_k (0.707107,-0.707107,-5.17689e-16) (1.0,1.22465e-16,-4.7752e-16) (-1.2909e-16,0.0,1.0)
  `union3` triangle_k (1.91754e-16,-1.0,-6.14666e-16) (0.707107,-0.707107,-5.17689e-16) (-1.2909e-16,0.0,1.0)
  `union3` triangle_k (-0.707107,-0.707107,-7.11643e-16) (1.91754e-16,-1.0,-6.14666e-16) (-1.2909e-16,0.0,1.0)
  `union3` triangle_k (-1.0,0.0,-7.51812e-16) (-0.707107,-0.707107,-7.11643e-16) (-1.2909e-16,0.0,1.0)
  `union3` triangle_k (-0.707107,0.707107,-7.11643e-16) (-1.0,0.0,-7.51812e-16) (-1.2909e-16,0.0,1.0)
  `union3` triangle_k (1.0,1.22465e-16,-4.7752e-16) (0.707107,-0.707107,-5.17689e-16) (0.0,0.0,-2.39314e-16)
  `union3` triangle_k (1.0,1.22465e-16,-4.7752e-16) (0.0,0.0,-2.39314e-16) (0.707107,0.707107,-5.17689e-16)
  `union3` triangle_k (-1.0,0.0,-7.51812e-16) (-0.707107,0.707107,-7.11643e-16) (0.0,0.0,-2.39314e-16)
  `union3` triangle_k (-0.707107,0.707107,-7.11643e-16) (-5.31758e-17,1.0,-6.14666e-16) (0.0,0.0,-2.39314e-16)
  `union3` triangle_k (0.0,0.0,-2.39314e-16) (-5.31758e-17,1.0,-6.14666e-16) (0.707107,0.707107,-5.17689e-16)
  `union3` triangle_k (0.707107,-0.707107,-5.17689e-16) (1.91754e-16,-1.0,-6.14666e-16) (0.0,0.0,-2.39314e-16)
  `union3` triangle_k (1.91754e-16,-1.0,-6.14666e-16) (-0.707107,-0.707107,-7.11643e-16) (0.0,0.0,-2.39314e-16)
  `union3` triangle_k (0.0,0.0,-2.39314e-16) (-0.707107,-0.707107,-7.11643e-16) (-1.0,0.0,-7.51812e-16);;

let sqrt (a : real) : real =
  cut q : [0, inf) left q^2 < a right a < q^2;;

let unit_circle' = fun P : real^2 -> bool =>
     forall_interval_sym (fun cost : real => P (cost,   sqrt (1 - cost^2)))
  && forall_interval_sym (fun cost : real => P (cost, - sqrt (1 - cost^2)));;

let unit_circle'' = fun P : real^2 -> bool =>
  forall_interval_sym (fun cost : real => P (cost,   sqrt (1 - cost^2))
                                 && P (cost, - sqrt (1 - cost^2)));;

let unit_circle''' = fun P : real^2 -> bool =>
  unit_interval (fun t : real => let theta = twopi * t in P (cos theta, sin theta));;

let solid_cone : KShape (real^3) =
  compact_union {real} unit_interval {real^3} (fun z : real =>
  compact_union {real^2} (scale_k z unit_disk_k) {real^3} (fun xy : real^2 =>
  point {real^3} (xy#0, xy#1, 1 - z)));;

let cone : KShape (real^3) =
  compact_union {real} unit_interval {real^3} (fun z : real =>
  compact_union {real^2} (scale_k z unit_circle'') {real^3} (fun xy : real^2 =>
  point {real^3} (xy#0, xy#1, 1 - z)))
  `union3`
  map {real^2} {real^3} (fun xy : real^2 => (xy#0, xy#1, 0)) unit_disk_k;;

let directed_hausdorff_pred (s1 s2 : KShape (real^3)) (q : real) =
  exists_k {real^3} s1 (fun x : real^3 =>
  forall_k {real^3} s2 (fun y : real^3 =>
     q^2 <b ((y#0 - x#0)^2 + (y#1 - x#1)^2 + (y#2 - x#2)^2)));;

let directed_hausdorff3 (s1 s2 : KShape (real^3)) : real =
  cut q : [0, inf) left is_true   (directed_hausdorff_pred s1 s2 q)
                   right is_false (directed_hausdorff_pred s1 s2 q);;

let hausdorff3 (s1 s2 : KShape (real^3)) : real =
  cut q : [0, inf) left is_true   (directed_hausdorff_pred s1 s2 q) \/ is_true  (directed_hausdorff_pred s2 s1 q)
                   right is_false (directed_hausdorff_pred s1 s2 q) /\ is_false (directed_hausdorff_pred s2 s1 q);;
