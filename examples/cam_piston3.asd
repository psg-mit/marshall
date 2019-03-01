!#use "examples/cam_piston3.asd";;
#use "examples/cad.asd";;
#use "examples/stdlib.asd";;

! ###############################################
! # Set up cam-piston and enclosure #############
! ###############################################
let cam (angle : real^2) = fun P : real^3 -> bool =>
  unit_interval (fun z : real =>
    unit_disk_k (fun xy : real^2 =>
      let x = 5 * xy#0 in
      let y = 3 * xy#1 in
      let xp = angle#0 * x + angle#1 * y in
      let yp = - angle#1 * x + angle#0 * y in
      let zp = 2 * z in
    P (xp, yp, zp))
  );;

let piston (angle : real^2) = fun P : real^3 -> bool =>
  unit_interval (fun x  : real   =>
    unit_disk_k   (fun yz : real^2 =>
  P (20*x + 4 + angle#0, yz#0, yz#1)));;

let cam_piston (angle : real^2) = fun P : real^3 -> bool =>
  cam angle P && piston angle P;;

let enclosure_piece = fun P : real^3 -> bool =>
  unit_interval (fun x : real =>
    unit_interval (fun y : real =>
      unit_interval (fun z : real => P (x + 26, y, z))));;



! ###############################################
! # Perform verificaion #########################
! ###############################################
let unit_circle = fun P : real^2 -> bool =>
  unit_interval (fun t : real => let theta = twopi * t in P (cos theta, sin theta));;

let collision_safe : prop = forall_ks {real^2} unit_circle (fun angle : real^2 =>
  disjoint_R3 (cam_piston angle) enclosure_piece);;

collision_safe;;

!let mycam = cam (1, 0);;
!let leftmost = infimum (map {real^3} {real} (fun xyz : real^3 => xyz#0) (mycam));;
!let rightmost = supremum (map {real^3} {real} (fun xyz : real^3 => xyz#0) (mycam));;
!
!let bottommost = infimum (map {real^3} {real} (fun xyz : real^3 => xyz#1) (mycam));;
!let topmost = supremum (map {real^3} {real} (fun xyz : real^3 => xyz#1) (mycam));;
!
!let backmost = infimum (map {real^3} {real} (fun xyz : real^3 => xyz#2) (mycam));;
!let foremost = supremum (map {real^3} {real} (fun xyz : real^3 => xyz#2) (mycam));;
!
!let x = (leftmost, rightmost, bottommost, topmost, backmost, foremost);;
!
!x;;

!let mypiston = piston (1, 0);;
!let leftmost = infimum (map {real^3} {real} (fun xyz : real^3 => xyz#0) (mypiston));;
!let rightmost = supremum (map {real^3} {real} (fun xyz : real^3 => xyz#0) (mypiston));;
!
!let bottommost = infimum (map {real^3} {real} (fun xyz : real^3 => xyz#1) (mypiston));;
!let topmost = supremum (map {real^3} {real} (fun xyz : real^3 => xyz#1) (mypiston));;
!
!let backmost = infimum (map {real^3} {real} (fun xyz : real^3 => xyz#2) (mypiston));;
!let foremost = supremum (map {real^3} {real} (fun xyz : real^3 => xyz#2) (mypiston));;
!
!let x = (leftmost, rightmost, bottommost, topmost, backmost, foremost);;
!x;;

!let leftmost = infimum (map {real^3} {real} (fun xyz : real^3 => xyz#0) (enclosure));;
!let rightmost = supremum (map {real^3} {real} (fun xyz : real^3 => xyz#0) (enclosure));;
!
!let bottommost = infimum (map {real^3} {real} (fun xyz : real^3 => xyz#1) (enclosure));;
!let topmost = supremum (map {real^3} {real} (fun xyz : real^3 => xyz#1) (enclosure));;
!
!let backmost = infimum (map {real^3} {real} (fun xyz : real^3 => xyz#2) (enclosure));;
!let foremost = supremum (map {real^3} {real} (fun xyz : real^3 => xyz#2) (enclosure));;
!
!let x = (leftmost, rightmost, bottommost, topmost, backmost, foremost);;
!
!x;;