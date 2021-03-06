! This file contains definitions that are automatically loaded by Marshall

type bool = prop * prop;;
let mkbool (t f : prop) : bool  = (t, f);;
let is_true (x : bool) = x#0;;
let is_false (x : bool) = x#1;;

let andb (x : bool) (y : bool) : bool =
  mkbool (is_true x /\ is_true y)
          (is_false x \/ is_false y);;

let orb (x : bool) (y : bool) : bool =
  mkbool (is_true x \/ is_true y)
          (is_false x /\ is_false y);;

let negb (x : bool) : bool =
  mkbool (is_false x) (is_true x)
  ;;

let lt (x : real) (y : real) : bool =
  mkbool (x < y) (y < x);;

let dedekind_cut = fun p : real -> bool =>
  cut x
    left   is_true  (p x)
    right  is_false (p x)
  ;;
