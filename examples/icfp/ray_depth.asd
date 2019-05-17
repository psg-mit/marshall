#use "../sqrt.asd";;
#use "../stoneworks/cad.asd";;

let touches = exists;;

let lta (x : real) (y : real) : bool =
  mkbool (x < y + 0.01) (y < x);;

let table (x : real^3) : bool =
  lta x[2] (-1) && lta (-1) x[1] && lta x[1] 1;;

let ball (x : real^3) : bool =
  lta ((x[0] - 2)^2 + (x[1] - 0.7)^2 + x[2]^2) 1;;

let interval (l : real) : KShape real =
  map {real} {real} (fun x : real => x * l) unit_interval;;

let lft_root (f : real -> bool) : real =
  dedekind_cut (fun q : real => q <b 0 || ~ (touches {real} (interval q) f));;

! lft_root_max_depth_20 f = max 20 (lft_root f)
let lft_root_max_depth_20 (f : real -> bool) : real =
  cut q : [0, 20]
    left is_false (touches {real} (interval q) f)
    right is_true (touches {real} (interval q) f)
    ;;

let ray (disp : real^2) : real -> real^3 = let mag = sqrt (1 + disp[0]^2 + disp[1]^2) in
  fun t : real => (t / mag, t * disp[0] / mag, - t * disp[1] / mag);;

let ray_depth (scene : real^3 -> bool) (disp : real^2) : real =
  lft_root_max_depth_20 (fun t : real => scene (ray disp t));;

let ray_scene (disp : real^2) : real =
  1 - (ray_depth (union_o {real^3} table ball) disp / 20);;