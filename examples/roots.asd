#use "examples/bool.asd";;

let forall_interval =
  fun p : real -> bool =>
  mkbool (forall x : [0, 1], is_true (p x)) (exists x : [0, 1], is_false (p x))
  ;;

let exists_interval =
  fun p : real -> bool =>
  ~ (forall_interval (fun x : real => ~ p x));;

let forall_interval' =
  fun a : real =>
  fun b : real =>
  let range = b - a in
  fun p : real -> bool =>
  forall_interval (fun x : real => p (a + x * range))
  ;;

let lnp_root = fun f : real -> bool =>
  dedekind_cut (fun q : real =>
  q <b 0 || forall_interval' 0 q f
  );;

let lpn_root = fun f : real -> bool =>
  dedekind_cut (fun q : real =>
  q <b 0 || forall_interval' 0 q (fun x : real => ~ f x)
  );;

let min =
  fun a : real =>
  fun b : real =>
  dedekind_cut (fun x : real => x <b a && x <b b);;

let max =
  fun a : real =>
  fun b : real =>
  dedekind_cut (fun x : real => x <b a || x <b b);;

! find the earliest stable root of f on { x : R | x > 0 }
let l_root = fun f : real -> bool =>
  max (lnp_root f) (lpn_root f);;

! regular root finding on real-valued functions
let l_root_real = fun f : real -> real =>
  l_root (fun x : real => 0 <b f x);;
