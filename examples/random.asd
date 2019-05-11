#use "examples/stdlib.asd";;

type Random A = (X : type) -> (A -> X) -> ((real -> X) -> X) -> X;;
! Constructors:
!   Ret : A -> Random A
!   SampleThen : (real -> Random A) -> Random A


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

let ebind A B (x : Expecter A) (f : A -> Expecter B)
  : Expecter B
  = fun k : B -> real => x (fun a : A => f a k);;

type unit = (X : type) -> X -> X;;

let I_unit : unit = fun A : type => fun x : A => x;;

let efactor (x : real) : Expecter unit =
  fun f : unit -> real => f I_unit * x;;

let enormalize A (e : Expecter A) : Expecter A =
  fun f : A -> real => e f / e (fun x : A => 1);;

let expect A (x : Random A) : Expecter A =
  x {Expecter A} (edirac {A}) (eSampleThen {A});;

let ebernoulli (p : real) : Expecter bool =
  fun f : bool -> real => p * f tt + (1 - p) * f ff;;

let euniform : Expecter real =
  fun f : real -> real => int x : [0, 1], f x;;

let ebernoulli_obs (p : real) (b : bool) : Expecter unit =
  efactor (indicator b * p + indicator (~ b) * (1 - p));;

let emap A B (f : A -> B) (e : Expecter A) : Expecter B =
  fun k : B -> real => e (fun x : A => k (f x));;


! The library of random functions
let uniform : Random real =
  rSampleThen {real} (fun x : real => rret {real} x);;

let bernoulli (p : real) : Random bool =
  rmap {real} {bool} (fun x : real => x <b p) uniform;;

let indicator (b : bool) : real =
  dedekind_cut (fun q : real => q <b 0 || (b && q <b 1));;

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

let simple_pp : Expecter bool = enormalize {bool} (
    ebind {bool} {bool} (ebernoulli 0.5) (fun b : bool =>
    ebind {unit} {bool} (efactor (exp (- indicator b))) (fun ignore : unit =>
    edirac {bool} b)));;

let beta_bernoulli : Expecter real =
  ebind {real} {real} euniform (fun p : real =>
  ebind {unit} {real} (ebernoulli_obs p tt) (fun ignore : unit =>
  edirac {real} p));;


let erf_inv (x : real) : real = dedekind_cut (fun q : real => erf q <b x);;

let probit (p : real) = sqrt 2 * erf_inv (2 * p - 1);;

let estdnormal : Expecter real = fun f : real -> real => int p : [0, 1], f (probit p)

