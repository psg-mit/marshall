#use "examples/cad.asd";;

let line_segment (w : real) : KShape real =
  fun P : real -> bool =>
  mkbool (forall x : [0, 1], is_true (P (w * x)))
         (exists x : [0, 1], is_false (P (w * x)));;

let rotate_xyp (angle : real^2) (x : real^3) : real^3 =
  (angle#0 * x#0 + angle#1 * x#1
  , -(angle#1) * x#0 + angle#0 * x#1
  , x#2);;

let rotate_xy (angle : real^2) : KShape (real^3) -> KShape (real^3) =
  map {real^3} {real^3} (rotate_xyp angle);;

let box (w : real^3) : KShape (real^3) =
  fun P : real^3 -> bool =>
  mkbool (
  forall x : [0, 1],
  forall y : [0, 1],
  forall z : [0, 1],
  is_true (P (w#0 * x, w#1 * y, w#2 * z))
  )
  (
  exists x : [0, 1],
  exists y : [0, 1],
  exists z : [0, 1],
  is_false (P (w#0 * x, w#1 * y, w#2 * z))
  )
;;

let translate3 (trans : real^3) : KShape (real^3) -> KShape (real^3) = 
  map {real^3} {real^3} (fun x : real^3 => (x[0] + trans[0], x[1] + trans[1], x[2] + trans[2]));;

let piston : KShape (real^3) = 
  compact_union {real} (line_segment 20) {real^3} (fun x : real =>
  compact_union {real^2} unit_disk_k {real^3} (fun yz : real^2 =>
  point {real^3} (x, yz[0], yz[1])));;

let extrude (w : real) (k : KShape (real^2)) : KShape (real^3) =
  compact_union {real} (line_segment w) {real^3} (fun z : real =>
  compact_union {real^2} k {real^3} (fun xy : real^2 =>
  point {real^3} (xy#0, xy#1, z)));;

let scale2 (c : real) : KShape (real^2) -> KShape (real^2) =
  map {real^2} {real^2} (fun xy : real^2 => (c * xy#0, c * xy#1));;
  
let cam (angle : real^2) : KShape (real^3) = 
  rotate_xy angle (translate3 (-2.5, 0, 0) (extrude 1 (scale2 5 unit_disk_k)));;
  
let translated_piston (angle : real^2) : KShape (real^3) = 
  translate3 (5 + 2.5 * angle#0, 0, 0) piston;; !piston translates when cam rotates

let union_k E (k1 k2 : KShape E) =
  fun P : E -> bool => k1 P && k2 P;;

let cam_piston (angle : real^2) : KShape (real^3) =
  union_k {real^3} (cam angle) (translated_piston angle);;

let enclosure_piece : KShape (real^3) = translate3 (30, -1, 0) (box (2, 2, 2));;

let unit_circle = union_k {real^2}
  (map {real} {real^2} (fun x : real => (x,  sqrt (1 - x^2))) unit_interval)
  (map {real} {real^2} (fun x : real => (x, -sqrt (1 - x^2))) unit_interval);;

let neq_R3 (x y : real^3) : prop =
  x#0 <> y#0 \/ x#1 <> y#1 \/ x#2 <> y#2;;

let collision_safe : prop = forall_ks {real^2} unit_circle (fun angle : real^2 =>
  disjoint {real^3} neq_R3 (cam_piston angle) enclosure_piece);;

let d3 (x y : real^3) : real =
  sqrt ((x#0 - y#0)^2 + (x#1 - y#1)^2 + (x#2 - y#2)^2);;

let clearance_dist : real = infimum (
  map {real^2} {real} (fun angle : real^2 => separation_dist {real^3} d3 (cam_piston angle) enclosure_piece)
                unit_circle);;

collision_safe;;
