#use "./types/boolean.asd";;

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


type list X = (A : type) -> A -> (X -> A -> A) -> A;;

let cnil X A (z : A) (s : X -> A -> A) : A = z;;
let ccons X (x : X) (xs : list X) A (z : A) (s : X -> A -> A) : A
  = s x (xs {A} z s);;

let capp X (xs ys : list X) : list X
  = xs {list X} ys (ccons {X});;

let sum_list_real (xs : list real) : real
  = xs {real} 0 (fun x y : real => x + y);;

let list_map A B (f : A -> B) (xs : list A) : list B =
  xs {list B} (cnil {B}) (fun x : A => ccons {B} (f x));;

let range' (n : nat) : real -> list real =
  n {real -> list real} (fun x : real => cnil {real})
    (fun ih : real -> list real => fun x : real => ccons {real} x (ih (x + 1)));;

let range_int' (n : nat) : integer -> list integer =
  n {integer -> list integer} (fun x : integer => cnil {integer})
    (fun ih : integer -> list integer => fun x : integer => ccons {integer} x (ih (x + i1)));;

let list_real_example : real =
  sum_list_real (range' (cmult cthree cthree) 0);;

let randomi (i : integer) : real = random i;;

let avg_of_many_randoms : real =
  let n = cpow ctwo (cmult ctwo ctwo) in
  sum_list_real (list_map {integer} {real} randomi (range_int' n i0)) / nat_to_real n;;
