#use "./krep.asd";;

! Both O- and K-representation

type OKShape E = KShape E * OShape E;;

let unit_square_ok = (unit_square, rectangle_o 2 2);;

! unit disk centered at origin
let unit_disk_ok =
  (unit_disk, unit_disk_o)
;;

let translate_ok (tx : real^2)
    (shape : KShape (real^2) * OShape (real^2)) =
  (translate tx shape#0, translate_o tx shape#1);;

let union_ok
    (shape1 shape2 : KShape (real^2) * OShape (real^2)) =
  (union shape1#0 shape2#0, union_o {real^2} shape1#1 shape2#1);;

let is_contained_in E (k : KShape E) (o : OShape E) : bool =
  forall {E} k (fun x : E => o x);;

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

let empty_ok E =
   (empty {E}
   , empty_o {E});;


let scale_x_y_ok (cx : real) (cy : real)
  (shape : ((real^2 -> bool) -> bool) * (real^2 -> bool)) =
  (scale_x_y cx cy shape#0, scale_x_y_o cx cy shape#1);;


let minkowski_sum_o E (plus : E -> E -> E)
  (o : OShape E) (k : KShape E) : OShape E =
  fun x : E => exists {E} k (fun delta : E => o (plus x delta));;

let minkowski_diff_o E (plus : E -> E -> E)
  (o : OShape E) (k : KShape E) : OShape E =
  fun x : E => forall {E} k (fun delta : E => o (plus x delta));;




let integrate_unit_interval (f : real -> real) : real =
  int x : [0, 1], f x;;

let integral (a b : real) (f : real -> real) : real =
  let range = b - a in
  range * integrate_unit_interval (fun x : real => f (a + range * x));;

let indicator (b : bool) : real =
  dedekind_cut (fun q : real => q <b 0 || (b && q <b 1));;

let volume (s : KShape real * OShape real) : real =
  integral (infimum s#0) (supremum s#0) (fun x : real => indicator (s#1 x));;


let compact_union_o E (k : KShape E) F (o : E -> OShape F) : OShape F =
  fun f : F => exists {E} k (fun e : E => o e f);;

let compact_intersection_o E (k : KShape E) F (o : E -> OShape F) : OShape F =
  fun f : F => forall {E} k (fun e : E => o e f);;
