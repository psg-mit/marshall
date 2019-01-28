! This file contains definitions that are automatically loaded by Marshall

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