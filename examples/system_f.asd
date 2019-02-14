let ctrue A (t f : A) : A = t;;
let cfalse A (t f : A) : A = f;;

let cand (b1 b2 : (A : type) -> A -> A -> A) : (A : type) -> A -> A -> A
  = b1 {(A : type) -> A -> A -> A} b2 cfalse;;

let cor (b1 b2 : (A : type) -> A -> A -> A) : (A : type) -> A -> A -> A
  = b1 {(A : type) -> A -> A -> A} ctrue b2;;

let cnot (b : (A : type) -> A -> A -> A) : (A : type) -> A -> A -> A
  = b {(A : type) -> A -> A -> A} cfalse ctrue;;


let czero A (z : A) (s : A -> A) = z;;
let cone A (z : A) (s : A -> A) = s z;;
let ctwo A (z : A) (s : A -> A) = s (s z);;
let cthree A (z : A) (s : A -> A) = s (s (s z));;

let csucc (n : (A : type) -> A -> (A -> A) -> A) A (z : A) (s : A -> A) : A
  = n {A} (s z) s;;

let cplus (m n : (A : type) -> A -> (A -> A) -> A)
  : (A : type) -> A -> (A -> A) -> A
  = m {(A : type) -> A -> (A -> A) -> A} n csucc;;

let cmult (m n : (A : type) -> A -> (A -> A) -> A)
  : (A : type) -> A -> (A -> A) -> A
  = m {(A : type) -> A -> (A -> A) -> A} czero (cplus n);;

let nat_example : real
  = (cmult cthree cthree) {real} 0 (fun x : real => x + 1);;
