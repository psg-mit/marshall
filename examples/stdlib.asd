#use "./bool.asd";;

let log (x : real) : real = dedekind_cut (fun q : real => exp q <b x);;
let pi2 : real = 3 * (cut q : [1.0, 1.1] left cos q > 0.5 right cos q < 0.5);;
let pi : real = cut q : [3.1415926, 3.1415927] left sin q > 0 right sin q < 0;;
let twopi : real = cut q : [6.28318, 6.28319] left sin q < 0 right sin q > 0;;
