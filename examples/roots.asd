#use "examples/bool.asd";;
#use "examples/sqrt.asd";;

let forall_interval (p : real -> bool) : bool =
  mkbool (forall x : [0, 1], is_true (p x)) (exists x : [0, 1], is_false (p x))
  ;;

let forall_interval' (a : real) (b : real) : (real -> bool) -> bool =
  let range = b - a in
  fun p : real -> bool =>
  forall_interval (fun x : real => p (a + x * range))
  ;;

let ltf_root (f : real -> bool) : real =
  dedekind_cut (fun q : real =>
  q <b 0 || forall_interval' 0 q f
  );;

let lft_root (f : real -> bool) : real =
  dedekind_cut (fun q : real =>
  q <b 0 || forall_interval' 0 q (fun x : real => ~ f x)
  );;

let min (a : real) (b : real) : real =
  dedekind_cut (fun x : real => x <b a && x <b b);;

let max (a : real) (b : real) : real =
  dedekind_cut (fun x : real => x <b a || x <b b);;

! find the earliest stable root of f on { x : R | x > 0 }
let l_root (f : real -> bool) : real =
  dedekind_cut (fun q : real =>
  q <b 0 || forall_interval' 0 q f
         || forall_interval' 0 q (fun x : real => ~ f x)
  );;

! regular root finding on real-valued functions
let l_root_real (f : real -> real) : real =
  l_root (fun x : real => 0 <b f x);;



! Let's do a ray-tracing example
let ray (disp : real * real) =
  let mag = sqrt (1 + disp#0^2 + disp#1^2) in
  let disp1 = disp#0 / mag in
  let disp2 = -disp#1 / mag in
  fun t : real => 
  (t / mag, t * disp1, t * disp2);;

let ray' (disp : real * real) =
  fun t : real => 
  (t, t * disp#0, t * disp#1);;

let lta (x : real) (y : real) : bool =
  mkbool (x < y + 0.01) (y < x);;

let table (x : real * real * real) : bool =
  lta x#2 -1 && lta -1 x#1 && lta x#1 1;;

let ball (x : real * real * real) : bool =
  ((x#0 - 3)^2 + (x#1 - 0.1)^2 + x#2^2) <b 1;;

let lft_root_max_depth (mx : real) (f : real -> bool) : real =
  dedekind_cut (fun q : real =>
  q <b 0 || (q <b mx && forall_interval' 0 q (fun x : real => ~ f x))
  );;

let ray_scene (disp : real * real) =
  1 - (lft_root_max_depth 20 (fun t : real => let r = ray disp t in table r || ball r) / 20);;
