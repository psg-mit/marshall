
let comp (p q r : real^2) : real = (q#0 - p#0) * (r#1 - p#1)
                       - (q#1 - p#1) * (r#0 - p#0);;


let comparison (p q r : real^2) : bool = comp p q r <b 0;;

let qdef : real^2 = (12, 12);;
let rdef : real^2 = (24, 24);;
let pdef : real^2 = (1/2, 1/2);;

let ulp : real = (1/2) ^ 53;;

let pmod : real^2 = (pdef#0 + 41 * ulp, pdef#1 + 48*ulp);;

let test : bool = comparison pmod qdef rdef;;
