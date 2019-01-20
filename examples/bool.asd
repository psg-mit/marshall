! The standard boolean operations with our real-number based
! encoding.
let andb (x : bool) (y : bool) : bool =
  mkbool (is_true x /\ is_true y)
          (is_false x \/ is_false y);;
let orb (x : bool) (y : bool) : bool =
  mkbool (is_true x \/ is_true y)
          (is_false x /\ is_false y);;
let tt : bool = mkbool True False;;
let ff : bool = mkbool False True;;
let negb (x : bool) : bool =
  mkbool (is_false x) (is_true x)
  ;;

let indicator (b : bool) : real =
  cut x
    left (x < 0 \/ (is_true b /\ x < 1))
    right (x > 1 \/ (is_false b /\ x > 0));;

let lt (x : real) (y : real) : bool =
  mkbool (x < y) (y < x);;

let dedekind_cut (p : real -> bool) : real =
  cut x
    left   is_true  (p x)
    right  is_false (p x)
  ;;

let sqrt (a : real) : real =
  dedekind_cut (fun x : real => x <b 0 || x^2 <b a);;
