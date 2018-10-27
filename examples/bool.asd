! The standard boolean operations with our real-number based
! encoding.
let andb = fun x : bool => fun y : bool =>
  mkbool (is_true x /\ is_true y)
          (is_false x \/ is_false y);;
let orb = fun x : bool => fun y : bool =>
  mkbool (is_true x \/ is_true y)
          (is_false x /\ is_false y);;
let tt = mkbool True False;;
let ff = mkbool False True;;
let negb = fun x : bool =>
  mkboolp (is_false x) (is_true x)
  ;;

let indicator = fun b : bool =>
  cut x
    left (x < 0 \/ (is_true b /\ x < 1))
    right (x > 1 \/ (is_false b /\ x > 0));;