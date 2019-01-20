#use "examples/bool.asd";;

let forall_interval (p : real -> bool) : bool =
  mkbool (forall x : [0, 1], is_true (p x)) (exists x : [0, 1], is_false (p x))
  ;;

let forall_interval' (a : real) (b : real) : (real -> bool) -> bool =
  let range = b - a in
  fun p : real -> bool =>
  forall_interval (fun x : real => p (a + x * range))
  ;;

let lft_root (f : real -> bool) : real =
  dedekind_cut (fun q : real =>
  q <b 0 || forall_interval' 0 q f
  );;

let ltf_root (f : real -> bool) : real =
  dedekind_cut (fun q : real =>
  q <b 0 || forall_interval' 0 q (fun x : real => ~ f x)
  );;

let min (a : real) (b : real) : real =
  dedekind_cut (fun x : real => x <b a && x <b b);;

let max (a : real) (b : real) : real =
  dedekind_cut (fun x : real => x <b a || x <b b);;

! find the earliest stable root of f on { x : R | x > 0 }
let l_root (f : real -> bool) : real =
  max (lft_root f) (ltf_root f);;

! regular root finding on real-valued functions
let l_root_real (f : real -> real) : real =
  l_root (fun x : real => 0 <b f x);;


!let exists_interval =
! fun p : real -> bool =>
!  ~ (forall_interval (fun x : real => ~ p x));;
