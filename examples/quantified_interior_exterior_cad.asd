#use "examples/cad.asd";;

let max (a : real) (b : real) : real =
  dedekind_cut (fun x : real => x <b a || x <b b);;
