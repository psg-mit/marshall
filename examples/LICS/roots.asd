let tt = mkbool True False;;
let ff = mkbool False True;;
let eps = 0.01;;

let exists_bool_interval = fun pred : real -> bool =>
     (exists x : [0,1], is_true  (pred x)) ~> tt
  || (forall x : [0,1], is_false (pred x)) ~> ff ;;

let is_0_eps = fun x : real =>
        x < 0 \/ x > 0   ~> ff
  || -eps < x /\ x < eps ~> tt ;;

let roots_interval = fun f : real -> real =>
  exists_bool_interval (fun x : real => is_0_eps (f x));;
