!!! SOUND ARITHMETIC

let ex1 : real = 1 + 1e100 - 1e100;;

let sqrt (x : real) : real =
  dedekind_cut (fun q : real => q <b 0 || q^2 <b x);;

let ex2 : real = (sqrt 2)^2;;
let ex3 : bool = 2 <b (sqrt 2)^2;;













! First logical value indicates truth, second indicates falsity.
type bool = prop * prop;;
let andb (x y : bool) : bool =
  mkbool (is_true x /\ is_true y)
          (is_false x \/ is_false y);;
let orb (x y : bool) : bool =
  mkbool (is_true x \/ is_true y)
          (is_false x /\ is_false y);;
let tt : bool = mkbool True False;;
let ff : bool = mkbool False True;;
let negb (x : bool) : bool = mkbool (is_false x) (is_true x) ;;
let lt (x y : real) : bool = mkbool (x < y) (y < x);;

let indicator (b : bool) : real =
  dedekind_cut (fun q : real => q <b 0 || (b && q <b 1));;











!!! SOLID MODELING

! Given a point (x : E), return whether I am in the interior
! or exterior of the shape
type OShape E = E -> bool;;

! Given a predicate P : E -> bool,
! return whether the predicate is true for all points in the shape,
! or false for some point the shape.
type KShape E = (E -> bool) -> bool;;
let forall_k E (k : KShape E) (p : E -> bool) : bool = k p;;
let exists_k E (k : KShape E) (p : E -> bool) : bool =
  ~ (k (fun x : E => ~ (p x)));;

! [0, 1]
let unit_interval : KShape real =
  fun p : real -> bool =>
  mkbool (forall x : [0, 1], is_true (p x))
         (exists x : [0, 1], is_false (p x));;

! [-1, 1]
let interval_sym : KShape real =
  fun p : real -> bool =>
  mkbool (forall x : [-1, 1], is_true (p x))
         (exists x : [-1, 1], is_false (p x));;

! [-1, 1]^2
let square_sym : KShape (real^2) =
  fun p : real^2 -> bool =>
  interval_sym (fun x : real =>
  interval_sym (fun y : real => p (x, y)));;

! disk with radius 1, center (0, 0)
let unit_disk_o : OShape (real^2) = fun x : real^2 => x#0^2 + x#1^2 <b 1;;

! disk with radius 1, center (0, 0)
let unit_disk : KShape (real^2) =
  fun P : real^2 -> bool =>
  interval_sym (fun x : real =>
  interval_sym (fun y : real => 1 <b x^2 + y^2  ||  P (x, y)));;

! squared distance between points
let d2 (x y : real^2) : real = (y[0] - x[0])^2 + (y[1] - x[1])^2;;

let hausdorff_dist (k1 k2 : KShape (real^2)) : real =
  dedekind_cut (fun q : real => q <b 0
   || exists_k {real^2} k1 (fun x : real^2 =>
        forall_k {real^2} k2 (fun y : real^2 => q^2 <b d2 x y))
   || exists_k {real^2} k2 (fun x : real^2 =>
        forall_k {real^2} k1 (fun y : real^2 => q^2 <b d2 x y))
   );;

let ex4 = hausdorff_dist square_sym unit_disk;;
let ex4_ground_truth = sqrt 2 - 1;;

let infimum (k : KShape real) : real =
  dedekind_cut (fun q : real => forall_k {real} k (fun x : real => q <b x));;


let touches = exists_k;;

let map E F (f : E -> F) (shape : KShape E) : KShape F =
  fun P : F -> bool => shape (fun x : E => P (f x));;

let interval (a b : real) : KShape real =
  map {real} {real} (fun x : real => a + x * (b - a)) unit_interval;;

let lft_root (f : real -> bool) : real =
  dedekind_cut (fun q : real => q <b 0
     || ~ (touches {real} (interval 0 q) f));;


let ex5 : real =
  lft_root (fun x : real => ((x - 1)^2 + (1/2)^2) <b 1);;

let ex5_ground_truth = 1 - sqrt 3 / 2;;






!!! RANDOMNESS

type Random A = (X : type) -> (A -> X) -> ((real -> X) -> X) -> X;;
! Constructors:
!   Ret : A -> Random A
!   SampleThen : (real -> Random A) -> Random A      (Uniform[0,1])


let rret A (x : A) : Random A =
  fun X : type => fun ret : A -> X => fun sampleThen : (real -> X) -> X =>
  ret x;;

let rSampleThen A (f : real -> Random A) : Random A =
  fun X : type => fun ret : A -> X => fun sampleThen : (real -> X) -> X =>
  sampleThen (fun x : real => f x {X} ret sampleThen);;

let rbind A B (x : Random A) (f : A -> Random B) : Random B =  
  x {Random B} f (fun k : real -> Random B => rSampleThen {B} k);;

let rmap A B (f : A -> B) (x : Random A) : Random B =
  x {Random B} (fun x : A => rret {B} (f x))
               (fun k : real -> Random B => rSampleThen {B} k);;
   
type Sampler A = integer -> integer * A;;

let sdirac A (x : A) : Sampler A =
  fun n : integer => (n, x);;

let sSampleThen A (f : real -> Sampler A) : Sampler A =
  fun n : integer => f (random n) (n + i1);;

let sbind A B (x : Sampler A) (f : A -> Sampler B)
  : Sampler B
  = fun n : integer => let res = x n in
    let n' = res[0] in
    let v = res[1] in
    f v n';;
    
let sample A (x : Random A) : Sampler A =
  x {Sampler A} (sdirac {A}) (sSampleThen {A});;

let runSample A (n : integer) (x : Random A) : A =
  (sample {A} x n)[1];;

type Expecter A = (A -> real) -> real;;

let edirac A (x : A) : Expecter A =
  fun f : A -> real => f x;;

let eSampleThen A (f : real -> Expecter A) : Expecter A =
  fun k : A -> real => int x : [0, 1], f x k;;

let expect A (x : Random A) : Expecter A =
  x {Expecter A} (edirac {A}) (eSampleThen {A});;


! The library of random functions
let uniform : Random real =
  rSampleThen {real} (fun x : real => rret {real} x);;

let bernoulli (p : real) : Random bool =
  rmap {real} {bool} (fun x : real => x <b p) uniform;;

let indicator (b : bool) : real =
  dedekind_cut (fun q : real => q <b 0 || (b && q <b 1));;

let log (x : real) : real = dedekind_cut (fun q : real => exp q <b x);;
let twopi : real = cut q : [6.28318, 6.28319]
                left sin q < 0 right sin q > 0;;

let box_muller_transform (u1 u2 : real) : real^2 =
  let theta = twopi * u2 in
  let r = sqrt (- 2 * log u1) in
  (r * cos theta, r * sin theta);;

let gaussians : Random (real^2) =
  rbind {real} {real^2} uniform (fun u1 : real =>
  rbind {real} {real^2} uniform (fun u2 : real =>
  rret {real^2} (box_muller_transform u1 u2)));;

let gaussian : Random real =
  rmap {real^2} {real} (fun x : real^2 => x[0]) gaussians;;

let chi_squared_1 : Random real =
  rmap {real} {real} (fun x : real => x^2) gaussian;;

let chi_squared_2 : Random real =
  rmap {real^2} {real} (fun x : real^2 => x[0]^2 + x[1]^2) gaussians;;

let abs (x : real) : real =
  cut q : [0, inf) left  q < x \/ q < - x
                   right x < q /\ -x < q;;

! Examples

let prob_true (x : Random bool) : real = expect {bool} x indicator;;

let expectation (x : Random real) : real = expect {real} x (fun z : real => z);;

let both_heads : Random bool =
  rbind {bool} {bool} (bernoulli 0.5) (fun c1 : bool =>
  rbind {bool} {bool} (bernoulli 0.5) (fun c2 : bool =>
  rret {bool} (c1 && c2)));;


let ex6 = runSample {bool} i0 both_heads;;
let ex7 = prob_true both_heads;;

let ex8 = runSample {real} i0 gaussian;;
let ex9 = prob_true (rmap {real} {bool} (fun x : real => 1 <b x) gaussian);;
