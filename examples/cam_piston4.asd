!#use "./cam_piston4.asd";;
#use "./cad.asd";;
#use "./stdlib.asd";;

! ###############################################
! # Set up cam-piston and enclosure #############
! ###############################################
let cam (angle : real) = fun P : real^3 -> bool =>
  unit_interval (fun z : real =>
    unit_disk (fun xy : real^2 =>
      let x = 5 * xy#0 in
      let y = 5 * xy#1 in
      let c = cos angle in
      let s = sin angle in
      let xp =   c * (x + 2.5) + s * y in
      let yp = - s * (x) + c * y in
      let zp = 2 * z in
    P (xp, yp, zp))
  );;

let piston (angle : real) = fun P : real^3 -> bool =>
  unit_interval (fun x  : real   =>
    unit_disk   (fun yz : real^2 =>
  P (20*x + 2.5*(cos (angle)) + 5, yz#0, yz#1)));;

let cam_piston (angle : real) = fun P : real^3 -> bool =>
  cam angle P && piston angle P;;

let enclosure_piece = fun P : real^3 -> bool =>
  unit_interval (fun x : real =>
    unit_interval (fun y : real =>
      unit_interval (fun z : real => P (x + 30, y, z))));;



! ###############################################
! # Perform verificaion #########################
! ###############################################
let unit_circle = fun P : real^2 -> bool =>
  unit_interval (fun t : real => let theta = twopi * t in P (cos theta, sin theta));;

let collision_safe : prop = Forall x : [0,1],
    let angle = twopi * x in
    disjoint_R3 (cam_piston angle) enclosure_piece;;

let separation3 (shape1 shape2 : (real^3 -> bool) -> bool) : real =
  dedekind_cut (fun cutoff : real => (cutoff <b 0) ||
     (shape1 (fun x : real^3 =>
      shape2 (fun x' : real^3 =>
     (cutoff^2) <b ((x'#0 - x#0)^2 + (x'#1 - x#1)^2 + (x'#2 - x#2)^2)))))
  ;;

let collision_dist (angle : real) : real =
  separation3 (cam_piston angle) enclosure_piece;;

let min_collision_dist : real =
  infimum (map {real} {real} (fun x : real => collision_dist (twopi * x)) unit_interval);;

collision_safe;;

! let angle : real = pi/4;;
!
! let mycam = cam angle;;
! let leftmost = infimum (map {real^3} {real} (fun xyz : real^3 => xyz#0) (mycam));;
! let rightmost = supremum (map {real^3} {real} (fun xyz : real^3 => xyz#0) (mycam));;
!
! let bottommost = infimum (map {real^3} {real} (fun xyz : real^3 => xyz#1) (mycam));;
! let topmost = supremum (map {real^3} {real} (fun xyz : real^3 => xyz#1) (mycam));;
!
! let backmost = infimum (map {real^3} {real} (fun xyz : real^3 => xyz#2) (mycam));;
! let foremost = supremum (map {real^3} {real} (fun xyz : real^3 => xyz#2) (mycam));;
!
! let x = (leftmost, rightmost, bottommost, topmost, backmost, foremost);;
!
! x;;
!
! let mypiston = piston angle;;
! let leftmost = infimum (map {real^3} {real} (fun xyz : real^3 => xyz#0) (mypiston));;
! let rightmost = supremum (map {real^3} {real} (fun xyz : real^3 => xyz#0) (mypiston));;
!
! let bottommost = infimum (map {real^3} {real} (fun xyz : real^3 => xyz#1) (mypiston));;
! let topmost = supremum (map {real^3} {real} (fun xyz : real^3 => xyz#1) (mypiston));;
!
! let backmost = infimum (map {real^3} {real} (fun xyz : real^3 => xyz#2) (mypiston));;
! let foremost = supremum (map {real^3} {real} (fun xyz : real^3 => xyz#2) (mypiston));;
!
! let x = (leftmost, rightmost, bottommost, topmost, backmost, foremost);;
! x;;

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