! The standard boolean operations with our real-number based
! encoding.
let tt : bool = mkbool True False;;
let ff : bool = mkbool False True;;

let indicator (b : bool) : real =
  cut x
    left (x < 0 \/ (is_true b /\ x < 1))
    right (x > 1 \/ (is_false b /\ x > 0));;

let dedekind_cut (p : real -> bool) : real =
  cut x
    left   is_true  (p x)
    right  is_false (p x)
  ;;

#use "./sqrt.asd";;
