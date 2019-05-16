#use "./mesh.asd";;

! hausdorff_dist
!  {real^3}
!  (fun x : real^3 => fun y : real^3 => (y#0 - x#0)^2 + (y#1 - x#1)^2 + (y#2 - x#2)^2)
hausdorff3
  cone cone_mesh > 0.07;;
