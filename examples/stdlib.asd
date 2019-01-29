let log (x : real) : real = dedekind_cut (fun q : real => q <b 0 || exp q <b x);;
let pi1 : real = 6 * (cut q : [0.5, 0.6] left sin q < 0.5 right sin q > 0.5);;
let pi : real = 6 * dedekind_cut (fun q : real => q <b 0.5 || (q<b 0.6 && sin q <b 0.5));;