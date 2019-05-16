#use "examples/sqrt.asd";;

let ray_unnorm (disp : real^2) =
  fun t : real =>
  (t, t * disp[0], t * -disp[1]);;

let lta (x : real) (y : real) : bool =
  mkbool (x < y + 0.01) (y < x);;

let table (x : real^3) : bool =
  lta x[2] (-1) && lta (-1) x[1] && lta x[1] 1;;

let ball (x : real^3) : bool =
  lta ((x[0] - 2)^2 + (x[1] - 0.7)^2 + x[2]^2) 1;;

let lft_root_max_depth' (f : real -> bool) : real =
  cut x : [0, 50]
    left Forall q : [0, 1], is_false (f (q * x))
    right Exists q : [0, 1], is_true (f (q * x))
    ;;

let ray_scene' (disp : real^2) =
  let mag = sqrt (1 + disp#0^2 + disp#1^2) in
  let md = mag / 20 in
  1 - (lft_root_max_depth' (fun t : real => let r = ray_unnorm disp t in table r || ball r) * md);;

#precision 1e-2;;
#plot 16 ray_scene';;
