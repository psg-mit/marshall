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
  mkbool (is_false x) (is_true x)
  ;;

let indicator = fun b : bool =>
  cut x
    left (x < 0 \/ (is_true b /\ x < 1))
    right (x > 1 \/ (is_false b /\ x > 0));;

let lt = fun x : real => fun y : real =>
  mkbool (x < y) (y < x);;

let dedekind_cut = fun p : real -> bool =>
  cut x
    left   is_true  (p x)
    right  is_false (p x)
  ;;

let sqrt = fun a : real =>
  dedekind_cut (fun x : real => orb (lt x 0) (lt (x^2) a));;

let interval =
  fun p : real -> bool =>
  mkbool (forall x : [-1, 1], is_true (p x)) (exists x : [-1, 1], is_false (p x))
  ;;

let square =
  fun p : real -> real -> bool =>
  interval (fun x : real =>
  interval (fun y : real => p x y)
  );;

let circle =
  fun p : real -> real -> bool =>
  interval (fun x : real =>
  interval (fun y : real =>
  orb (lt 1 (x^2 + y^2)) (p x y)
  ));;

let forall_shape =
  fun shape : (real -> real -> bool) -> bool =>
  fun p : real -> real -> bool =>
  shape p;;

let exists_shape =
  fun shape : (real -> real -> bool) -> bool =>
  fun p : real -> real -> bool =>
  negb (shape (fun x : real => fun y : real => negb (p x y)))
  ;;

let max = fun a : real => fun b : real =>
  dedekind_cut (fun x : real => orb (lt x a) (lt x b));;

let minimum =
  fun shape : (real -> bool) -> bool =>
  dedekind_cut (fun x : real => shape (lt x))
  ;;

let apply_1d =
  fun f : real -> real =>
  fun shape : (real -> bool) -> bool =>
  fun p : real -> bool =>
  shape (fun x : real => p (f x))
  ;;

let directed_hausdorff_distance =
  fun shape1 : (real -> real -> bool) -> bool =>
  fun shape2 : (real -> real -> bool) -> bool =>
  dedekind_cut (fun cutoff : real => orb (lt cutoff 0)
     (forall_shape shape1 (fun x : real => fun y : real =>
      exists_shape shape2 (fun x' : real => fun y' : real =>
     lt (cutoff^2) ((x' - x)^2 + (y' - y)^2)))))
  ;;

! compute the hausdorff distance between two shapes.
! It is the max over every shape_point_separation
let hausdorff_distance =
  fun shape1 : (real -> real -> bool) -> bool =>
  fun shape2 : (real -> real -> bool) -> bool =>
  max (directed_hausdorff_distance shape1 shape2)
      (directed_hausdorff_distance shape2 shape1);;

let neq = fun x : real => fun y : real =>
  mkbool (x <> y) False;;

let neq_shape_directed =
  fun shape1 : (real -> real -> bool) -> bool =>
  fun shape2 : (real -> real -> bool) -> bool =>
  forall_shape shape1 (fun x1 : real => fun y1 : real =>
  exists_shape shape2 (fun x2 : real => fun y2 : real =>
                  neq x1 x2))
  ;;

let neq_shape =
  fun shape1 : (real -> real -> bool) -> bool =>
  fun shape2 : (real -> real -> bool) -> bool =>
  orb (neq_shape shape1 shape2)
      (neq_shape shape2 shape1);;

let separation =
  fun shape1 : (real -> real -> bool) -> bool =>
  fun shape2 : (real -> real -> bool) -> bool =>
  dedekind_cut (fun cutoff : real => orb (lt cutoff 0)
     (forall_shape shape1 (fun x : real => fun y : real =>
      forall_shape shape2 (fun x' : real => fun y' : real =>
     lt (cutoff^2) ((x' - x)^2 + (y' - y)^2)))))
  ;;

let disjoint_R2 =
  fun shape1 : (real -> real -> bool) -> bool =>
  fun shape2 : (real -> real -> bool) -> bool =>
  forall_shape shape1 (fun x1 : real => fun y1 : real =>
  forall_shape shape2 (fun x2 : real => fun y2 : real =>
                  orb (neq x1 x2) (neq y1 y2)))
  ;;

let translate =
  fun tx : real =>
  fun ty : real =>
  fun shape : (real -> real -> bool) -> bool =>
  (fun p' : real -> real -> bool =>
  shape (fun x : real => fun y : real => p' (x + tx) (y + ty))
  )
  ;;

let union =
  fun shape1 : (real -> real -> bool) -> bool =>
  fun shape2 : (real -> real -> bool) -> bool =>
  fun pr : real -> real -> bool =>
   andb (shape1 pr) (shape2 pr)
  ;;

#precision 1e-2;;

let example =
  separation (translate 2 2 square) (circle)
  ;;

let example2 =
  minimum (apply_1d (fun x : real => x^2 - x) interval)
  ;;