type boolean = (A : type) -> A -> A -> A;;

let ctrue A (t f : A) : A = t;;
let cfalse A (t f : A) : A = f;;

let cand (b1 b2 : boolean) : boolean = b1 {boolean} b2 cfalse;;
let cor  (b1 b2 : boolean) : boolean = b1 {boolean} ctrue b2;;

let cnot (b : boolean) : boolean = b {boolean} cfalse ctrue;;
