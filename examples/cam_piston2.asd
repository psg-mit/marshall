#use "examples/cad.asd";;
#use "examples/stdlib.asd";;

let unit_circle = fun P : real^2 -> bool =>
  unit_interval (fun t : real => let theta = twopi * t in P (cos theta, sin theta));;

let unit_circle' = fun P : real^2 -> bool =>
     forall_interval_sym (fun cost : real => P (cost,   sqrt (1 - cost^2)))
  && forall_interval_sym (fun cost : real => P (cost, - sqrt (1 - cost^2)));;

let piston (angle : real^2) = fun P : real^3 -> bool =>
  unit_interval (fun x  : real   =>
  unit_disk_k   (fun yz : real^2 =>
  P (x + angle#0, yz#0, yz#1)));;

let cube = fun P : real^3 -> bool =>
           unit_interval (fun x : real =>
           unit_interval (fun y : real =>
	   unit_interval (fun z : real => P (x, y, z))));;

let enclosure_piece = fun P : real^3 -> bool =>
   unit_interval (fun x : real =>
   unit_interval (fun y : real =>
   unit_interval (fun z : real =>
    P (3 + x, y * 10 - 5, z * 10 - 5))));;

let collision_safe : prop = forall_ks {real^2} unit_circle (fun angle : real^2 =>
  disjoint_R3 (piston angle) enclosure_piece);;

let separation3 (shape1 shape2 : (real^3 -> bool) -> bool) : real =
  dedekind_cut (fun cutoff : real => (cutoff <b 0) ||
     (shape1 (fun x : real^3 =>
      shape2 (fun x' : real^3 =>
     (cutoff^2) <b ((x'#0 - x#0)^2 + (x'#1 - x#1)^2 + (x'#2 - x#2)^2)))))
  ;;

let cam_piston_separation_dist : real = infimum
  (map {real^2} {real} (fun angle : real^2 => separation3 (piston angle) enclosure_piece) unit_circle');;
