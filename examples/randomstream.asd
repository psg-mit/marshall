#use "./random.asd";;
#use "./system_f.asd";;

type WR A = real -> Random (real * A);;

let wrret A (x : A) : WR A =
  fun w : real => rret {real * A} (w, x);;

let wrbind A B (x : WR A) (f : A -> WR B) : WR B =
  fun w : real => rbind {real * A} {real * B} (x w) (fun r : real * A =>
    f r[1] r[0]);;

let wrmap A B (f : A -> B) (x : WR A) : WR B =
  fun w : real => rmap {real * A} {real * B}
    (fun r : real * A => (r[0], f r[1])) (x w);;

let wrlift A (x : Random A) : WR A =
  fun w : real => rmap {A} {real * A} (fun a : A => (w, a)) x;;

! How to run a WR

let weightedExpectation A (integral : Expecter (real * A)) : Expecter A =
  let total_mass = integral (fun wx : real * A => wx[0]) in
  fun f : A -> real => integral (fun wx : real * A => wx[0] * f wx[1]) / total_mass;;

let expectWR A (x : WR A) : Expecter A =
  weightedExpectation {A} (expect {real * A} (x 1));;

let factor (ll : real) : WR unit =
  fun w : real => rret {real * unit} (w * ll, I_unit);;


type Distr A = Random A * (A -> real);;

let uniformScore : real -> real =
  fun x : real => indicator (0 <b x && x <b 1);;

let uniformDistr : Distr real =
  (uniform, uniformScore);;

let gaussianScore : real -> real =
  fun x : real => exp (- x^2 / 2) / sqrt (2 * pi);;

let gaussianDistr : Distr real =
  (gaussian, gaussianScore);;

let indicator' (b : bool) (l h : real) : real =
  dedekind_cut (fun q : real => q <b l || (b && q <b h));;

let bernoulliScore (p : real) : bool -> real =
  fun b : bool => indicator' (~ b) p 1 * indicator' b (1 - p) 1;;

let bernoulliDistr (p : real) : Distr bool =
  (bernoulli p, bernoulliScore p);;



let betaBernoulliExample (b1 b2 b3 : bool) : WR real =
  wrbind {real} {real} (wrlift {real} uniform) (fun p : real =>
  wrbind {unit} {real} (factor (bernoulliScore p b1)) (fun I : unit =>
  wrbind {unit} {real} (factor (bernoulliScore p b2)) (fun I : unit =>
  wrbind {unit} {real} (factor (bernoulliScore p b3)) (fun I : unit =>
  wrret {real} p))));;

let runBetaBernoulliExample : real =
  expectWR {real} (betaBernoulliExample tt tt tt) (fun z : real => z);;



type Either A B = (X : type) -> (A -> X) -> (B -> X) -> X;;

let Left A B (a : A) : Either A B =
  fun X : type => fun l : A -> X => fun r : B -> X => l a;;

let Right A B (b : B) : Either A B =
  fun X : type => fun l : A -> X => fun r : B -> X => r b;;


! Note! Streams do not work well, because Marshall tries to recurse under binders???

type ZStream A B =
  (X : type) -> ((S : type) -> S -> (S -> A -> S * B) -> X) -> X;;


let zconst A B (f : A -> B) : ZStream A B =
  fun X : type => fun x : (S : type) -> S -> (S -> A -> S * B) -> X =>
  x {unit} I_unit (fun s : unit => fun a : A => (s, f a));;

let zstep A B (str : ZStream A B) (a : A)
  : B * ZStream A B =
  str {B * ZStream A B}
      (fun S : type => fun s : S => fun step : S -> A -> S * B =>
      let res = step s a in (res[1],
  fun X : type => fun x : (S' : type) -> S' -> (S -> A -> S * B) -> X =>
     x {S} res[0] step));;

let zcompose A B C (f : ZStream A B) (g : ZStream B C) : ZStream A C =
  fun X : type => fun x : (S : type) -> S -> (S -> A -> S * C) -> X =>
  x {ZStream A B * ZStream B C}
    (f, g)
    (fun s : ZStream A B * ZStream B C => fun a : A =>
      let fa = zstep {A} {B} s[0] a in
      let gb = zstep {B} {C} s[1] fa[0] in
      ((fa[1], gb[1]), gb[0]));;

let zmap B B' (f : B -> B') A (str : ZStream A B) : ZStream A B' =
  fun X : type => fun x : (S : type) -> S -> (S -> A -> S * B') -> X =>
  x {ZStream A B} str
    (fun s : ZStream A B => fun a : A =>
      let res = zstep {A} {B} s a in
      (res[1], f res[0]));;

type ZWRStream A B =
  (X : type) -> ((S : type) -> S -> (S -> A -> WR (S * B)) -> X) -> X;;

let zwrconst A B (f : A -> B) : ZWRStream A B =
  fun X : type => fun x : (S : type) -> S -> (S -> A -> WR (S * B)) -> X =>
  x {unit} I_unit (fun s : unit => fun a : A => wrret {unit * B} (s, f a));;

let zwrstep A B (str : ZWRStream A B) (a : A)
  : WR (B * ZWRStream A B) =
  str {WR (B * ZWRStream A B)}
      (fun S : type => fun s : S => fun step : S -> A -> WR (S * B) =>
      wrbind {S * B} {B * ZWRStream A B} (step s a) (fun res : S * B =>
      wrret {B * ZWRStream A B} (res[1],
  fun X : type => fun x : (S' : type) -> S' -> (S -> A -> WR (S * B)) -> X =>
     x {S} res[0] step)));;

let zwrcompose A B C (f : ZWRStream A B) (g : ZWRStream B C) : ZWRStream A C =
  fun X : type => fun x : (S : type) -> S -> (S -> A -> WR (S * C)) -> X =>
  x {ZWRStream A B * ZWRStream B C}
    (f, g)
    (fun s : ZWRStream A B * ZWRStream B C => fun a : A =>
      wrbind {B * ZWRStream A B} {(ZWRStream A B * ZWRStream B C) * C}
             (zwrstep {A} {B} s[0] a) (fun fa : B * ZWRStream A B =>
      wrbind {C * ZWRStream B C} {(ZWRStream A B * ZWRStream B C) * C}
             (zwrstep {B} {C} s[1] fa[0]) (fun gb : C * ZWRStream B C =>
      wrret {(ZWRStream A B * ZWRStream B C) * C} ((fa[1], gb[1]), gb[0]))));;

type ZRStream A B =
  (X : type) -> ((S : type) -> S -> (S -> A -> Random (S * B)) -> X) -> X;;

let zrconst A B (f : A -> B) : ZRStream A B =
  fun X : type => fun x : (S : type) -> S -> (S -> A -> Random (S * B)) -> X =>
  x {unit} I_unit (fun s : unit => fun a : A => rret {unit * B} (s, f a));;

let zrstep A B (str : ZRStream A B) (a : A)
  : Random (B * ZRStream A B) =
  str {Random (B * ZRStream A B)}
      (fun S : type => fun s : S => fun step : S -> A -> Random (S * B) =>
      rbind {S * B} {B * ZRStream A B} (step s a) (fun res : S * B =>
      rret {B * ZRStream A B} (res[1],
  fun X : type => fun x : (S' : type) -> S' -> (S -> A -> Random (S * B)) -> X =>
     x {S} res[0] step)));;

let zrcompose A B C (f : ZRStream A B) (g : ZRStream B C) : ZRStream A C =
  fun X : type => fun x : (S : type) -> S -> (S -> A -> Random (S * C)) -> X =>
  x {ZRStream A B * ZRStream B C}
    (f, g)
    (fun s : ZRStream A B * ZRStream B C => fun a : A =>
      rbind {B * ZRStream A B} {(ZRStream A B * ZRStream B C) * C}
             (zrstep {A} {B} s[0] a) (fun fa : B * ZRStream A B =>
      rbind {C * ZRStream B C} {(ZRStream A B * ZRStream B C) * C}
             (zrstep {B} {C} s[1] fa[0]) (fun gb : C * ZRStream B C =>
      rret {(ZRStream A B * ZRStream B C) * C} ((fa[1], gb[1]), gb[0]))));;

let zwrToZr A B (f : ZWRStream A B) : ZRStream A (real * B) =
  fun X : type => fun x : (S : type) -> S -> (S -> A -> Random (S * (real * B))) -> X =>
  x {real * ZWRStream A B} (1, f)
    (fun s : real * ZWRStream A B => fun a : A =>
      rmap {real * (B * ZWRStream A B)}
           {(real * ZWRStream A B) * (real * B)}
	   (fun t : real * (B * ZWRStream A B) => let w = t[0] in
	     let bs' = t[1] in
	     ( (w, bs'[1]), (w, bs'[0]))
	   )
           (zwrstep {A} {B} s[1] a s[0]));;

let zrToZ A B (f : ZRStream A B) : ZStream A (Random B) =
  fun X : type => fun x : (S : type) -> S -> (S -> A -> S * Random B) -> X =>
  x {Random (ZRStream A B)} (rret {ZRStream A B} f)
  (fun s : Random (ZRStream A B) => fun a : A =>
    let res =
    rbind {ZRStream A B}
          {B * ZRStream A B}
	  s
	  (fun str : ZRStream A B => zrstep {A} {B} str a)
    in
    (rmap {B * ZRStream A B} {ZRStream A B} (fun x : B * ZRStream A B => x[1]) res
    ,rmap {B * ZRStream A B} {           B} (fun x : B * ZRStream A B => x[0]) res));;

let zwrInterp A B (f : ZWRStream A B) : ZStream A (Expecter B) =
  zmap {Random (real * B)} {Expecter B}
    (fun z : Random (real * B) => weightedExpectation {B} (expect {real * B} z))
    {A}
    (zrToZ {A} {real * B} (zwrToZr {A} {B} f));;

let zCoin (p : real) : ZWRStream bool real =
  fun X : type => fun x : (S : type) -> S -> (S -> bool -> WR (S * real)) -> X =>
  x {real} p (fun p' : real => fun b : bool =>
    wrmap {unit} {real * real} (fun s : unit => (p', p')) (factor (bernoulliScore p b)));;

! First Boolean observation is ignored...
let zCoin' : ZWRStream bool real =
  fun X : type => fun x : (S : type) -> S -> (S -> bool -> WR (S * real)) -> X =>
  x {Either unit real} (Left {unit} {real} I_unit)
  (fun p' : Either unit real => fun b : bool =>
    p' {WR (Either unit real * real)}
       (fun l : unit => wrmap {real} {Either unit real * real}
                           (fun p : real => (Right {unit} {real} p, p))
                           (wrlift {real} uniform)
       )
       (fun p : real =>
    wrmap {unit} {Either unit real * real} (fun s : unit => (Right {unit} {real} p, p)) (factor (bernoulliScore p b)))
  );;

let zsteps (n : nat) A (s : ZStream unit A) : ZStream unit A =
  n {ZStream unit A} s
    (fun ih : ZStream unit A => let res = zstep {unit} {A} ih I_unit in res[1]);;

let znth (n : nat) A (s : ZStream unit A) : A =
  let res = zstep {unit} {A} (zsteps n {A} s) I_unit in res[0];;

let zCoinMarginal (n : nat) : real =
  (znth n {Expecter real} (zcompose {unit} {bool} {Expecter real}
                                 (zconst {unit} {bool} (fun s : unit => tt))
				 (zwrInterp {bool} {real} zCoin'))

  )
  (fun z : real => z);;


type Stream Y A =
  (X : type) -> ((S : type) -> S -> (S -> Either (Y * S) A) -> X) -> X;;

let stret Y A (a : A) : Stream Y A =
  fun X : type => fun x : (S : type) -> S -> (S -> Either (Y * S) A) -> X =>
  x {unit} I_unit (fun s : unit => Right {Y * unit} {A} a);;

let strepeat Y A (y : Y) : Stream Y A =
  fun X : type => fun x : (S : type) -> S -> (S -> Either (Y * S) A) -> X =>
  x {unit} I_unit (fun s : unit => Left {Y * unit} {A} (y, s));;

let step Y A (str : Stream Y A) : Either (Y * Stream Y A) A =
  str {Either (Y * Stream Y A) A}
    (fun S : type => fun s : S => fun st : S -> Either (Y * S) A =>
      st s {Either (Y * Stream Y A) A}
           (fun ys : Y * S => Left {Y * Stream Y A} {A} (ys[0],
      fun X : type => fun x : (S : type) -> S -> (S -> Either (Y * S) A) -> X =>
        x {S} ys[1] st)
	   )
	   (fun a : A => Right {Y * Stream Y A} {A} a)
    );;

let step_n (n : nat) Y A (str : Stream Y A) : Either (Stream Y A) A =
  n {Either (Stream Y A) A}
    (Left {Stream Y A} {A} str)
    (fun ih : Either (Stream Y A) A =>
    ih {Either (Stream Y A) A}
       (fun str' : Stream Y A =>
        step {Y} {A} str' {Either (Stream Y A) A}
	                   (fun str'' : Y * Stream Y A => Left {Stream Y A} {A} str''[1])
			   (fun a : A => Right {Stream Y A} {A} a)
       )
       (fun a : A => Right {Stream Y A} {A} a));;

let nth_yield (n : nat) Y A (str : Stream Y A) : Either unit Y =
  let nothing = Left {unit} {Y} I_unit in
  let res = step_n n {Y} {A} str in
  res {Either unit Y}
      (fun str' : Stream Y A =>
        step {Y} {A} str' {Either unit Y}
	                  (fun ys : Y * Stream Y A => Right {unit} {Y} ys[0])
			  (fun a : A => nothing)
      )
      (fun a : A => nothing);;
