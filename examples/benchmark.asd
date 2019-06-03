#use "./stdlib.asd";;

#precision 1e-1000;;
! from  CCA 2000 Exact Real Arithmetic Systems: Results of Competition
! Jens Blanck
! Level 0 problems

let e = exp 1;;
let ex1 = sqrt pi;;
let ex2 = log pi;;
let ex3 = sin e;;
let ex4 = cos e;;
let ex5 = sin (sin (sin 1));;
let ex6 = cos (cos (cos 1));;
let ex7 = exp (exp e);;
let ex8 = log (1 + log (1 + log (1 + pi)));;
let ex9 = log (1 + log (1 + log (1 + e)));;
let ex10 = sin (10 ^ 50);;
let ex11 = cos (10 ^ 50);;
let ex12 = exp 1000;;
! let ex13 = arctan (10 ^ 50);;

! CCA 2000 problems

let fifth_root (a : real) =
  cut x : [0, inf)
    left x^5 < a
    right x^5 > a;;

let ex14 = exp (pi * sqrt 163);;
let ex15 = fifth_root (fifth_root (32 / 5) - fifth_root (27/5))
  - (1 + fifth_root 3 - fifth_root 9) / fifth_root 25;;
let ex16 = sin (3 * log 640320 / sqrt 163);;
! let ex17 = 1000 iterations of the logistic map
!   x_{n + 1} = 15 / 4 (x_n -x_n^2)
