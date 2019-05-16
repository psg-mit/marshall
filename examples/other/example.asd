! This is a sample Marshall program.
! Comments begin with ! and end with end of line.
! Definitions and exprssions must be separated by double semicolons

Forall x : [0, 1], 0 < (x + 0.1) * (x- 0.9) * (x - 1.1)
;;
Forall x : [0, 1], 0 > (x + 0.1) * (x- 0.1) * (x - 1.1)
;;
Exists x : [0, 1], 0 > (x + 0.1) * (x- 0.9) * (x - 1.1)
;;
Exists x : [0, 1], 0 < (x + 0.1) * (x- 0.1) * (x - 1.1)
;;

let some_arithmetic = 2 * 3^4 + 0.01 - 1.12e-1
;;

! The identity function using cuts
let id = fun a : real => cut t left t < a right a < t
;;

let sqrt =
  fun a : real =>
    cut x
      left  (x < 0 \/ x * x < a)

      right (x > 0 /\ x * x > a)
;;

! Square root of two
let sqrt_of_2 = sqrt 2
;;

! Compute the square of square root of 2
let square_of_sqrt_of_2 = sqrt_of_2^2
;;

! Square root of square root of 81
let sqrt_of_sqrt_of_81 = sqrt (sqrt 81)
;;

! Cube roots of numbers in [0,1] Exists up to precision 0.01
let p1 =
  Forall x : [0,1], Exists y : [0,1], x ={0.01}= y^3
;;

! There is an approximate solution of x^3 + 3 * x + 1 = 0
let p2 =
  Exists x : real, x^3 + 3 * x + 1 ={0.00001}= 0
;;

! Testing comparisons
let p3 =
  Forall x : [0,1], Forall y : [0,1], x < y \/ y < x + 0.01
;;

! Logarithmic map
let lg = fun x : real => 2 * (1 - x^2) - 1
;;

! We have to iterate by hand because we do not have recursion yet
let lg2 = fun x : real => lg (lg x) ;;
let lg4 = fun x : real => lg2 (lg2 x) ;;
let lg8 = fun x : real => lg4 (lg4 x) ;;
let lg16 = fun x : real => lg8 (lg8 x) ;;
let lg32 = fun x : real => lg16 (lg16 x) ;;
let lg64 = fun x : real => lg32 (lg32 x) ;;

! Now compute lg64 0.1.
let lg64_of_tenth = lg16 0.1 ;;


! Maximum of a function on the unit interval
let max =
  fun f : real -> real =>
    cut a
      left  (Exists x : [0,1], a < f x)
      right (Forall x : [0,1], f x < a)
;;

!! The next one is rather slow
let max_should_be_0_25 = max (fun x : real => x * (1 - x))
;;

let max_sqrt_should_be_1 = max sqrt ;;
#precision 1e-3;;

let max_6th_degree = max (fun x:real => 0.00756*x - 0.0726*x^2 + 0.299667*x^3 - 0.5675*x^4 + 0.5*x^5 - 0.166667*x^6);;
