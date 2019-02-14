type boolean = (A : type) -> A -> A -> A;;

let ctrue A (t f : A) : A = t;;
let cfalse A (t f : A) : A = f;;

let cand (b1 b2 : boolean) : boolean = b1 {boolean} b2 cfalse;;
let cor  (b1 b2 : boolean) : boolean = b1 {boolean} ctrue b2;;

let cnot (b : boolean) : boolean = b {boolean} cfalse ctrue;;

type nat = (A : type) -> A -> (A -> A) -> A;;

let czero A (z : A) (s : A -> A) = z;;
let cone A (z : A) (s : A -> A) = s z;;
let ctwo A (z : A) (s : A -> A) = s (s z);;
let cthree A (z : A) (s : A -> A) = s (s (s z));;

let csucc (n : nat) A (z : A) (s : A -> A) : A
  = s (n {A} z s);;

let cplus (m n : nat) : nat = m {nat} n csucc;;
let cmult (m n : nat) : nat = m {nat} czero (cplus n);;
let cpow (b e : nat) : nat = e {nat} cone (cmult b);;

let nat_to_real (n : nat) : real = n {real} 0 (fun x : real => x + 1);;

let nat_example : real = nat_to_real (cpow cthree cthree);;


type list_real = (A : type) -> A -> (real -> A -> A) -> A;;

let cnil A (z : A) (s : real -> A -> A) : A = z;;
let ccons (x : real) (xs : list_real) A (z : A) (s : real -> A -> A) : A
  = s x (xs {A} z s);;

let capp (xs ys : list_real) : list_real
  = xs {list_real} ys ccons;;

let sum_list_real (xs : list_real) : real
  = xs {real} 0 (fun x y : real => x + y);;
