#use "examples/stdlib.asd";;

type Random A = (X : type) -> (A -> X) -> ((real -> X) -> X) -> X;;

! Ret : A -> Random A
! SampleThen : (real -> Random A) -> Random A

! Ret x >>= f = f x
! SampleThen (k : real -> Random A) >>= f = SampleThen
  ! (fun x : real => k x >>= f)

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

let uniform : Random real =
  rSampleThen {real} (fun x : real => rret {real} x);;

let bernoulli (p : real) : Random bool =
  rmap {real} {bool} (lt p) uniform;;

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
