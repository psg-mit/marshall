type boolean = (A : type) -> A -> A -> A;;

let ctrue A (t f : A) : A = t;;
let cfalse A (t f : A) : A = f;;

let cand (b1 b2 : boolean) : boolean
  = b1 {boolean} b2 cfalse;;

let cor (b1 b2 : boolean) : boolean
  = b1 {boolean} ctrue b2;;

let cnot (b : boolean) : boolean
  = b {boolean} cfalse ctrue;;

type nat = (A : type) -> A -> (A -> A) -> A;;

let czero A (z : A) (s : A -> A) = z;;
let cone A (z : A) (s : A -> A) = s z;;
let ctwo A (z : A) (s : A -> A) = s (s z);;
let cthree A (z : A) (s : A -> A) = s (s (s z));;

let csucc (n : nat) A (z : A) (s : A -> A) : A
  = n {A} (s z) s;;

let cplus (m n : nat) : nat = m {nat} n csucc;;

let cmult (m n : nat) : nat = m {nat} czero (cplus n);;

let nat_example : real
  = (cmult cthree cthree) {real} 0 (fun x : real => x + 1);;
