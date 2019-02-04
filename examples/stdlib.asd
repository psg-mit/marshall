let log (x : real) : real = dedekind_cut (fun q : real => exp q <b x);;
let pi : real = 6 * (cut q : [0.5, 0.6] left sin q < 0.5 right sin q > 0.5);;
let pi2 : real = 3 * (cut q : [1.0, 1.1] left cos q > 0.5 right cos q < 0.5);;
