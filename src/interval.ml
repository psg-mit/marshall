(* \section{Interval arithmetic (module [Interval])} *)

(* An interval is a pair [(l,u)] of [Dyadic] numbers. There is no
   restriction that [l] should be smaller than [u], i.e., the library
   also works with back-to-front intervals. It uses Kaucher
   multiplication for back-to-front intervals. Infinity and negative
   infinity are allowed as endpoints. *)

(* An interval is represented as a pair of lazy [Mfpr.t] values. This is
   so because often we only need to evaluate one of the endpoints. *)

open Lazy

module Make = functor (D : Dyadic.DYADIC) ->
struct

  (* An interval is a record with fields [lower] and [upper]. *)
  type t = { lower : D.t Lazy.t; upper : D.t Lazy.t }

  (* \subsection{Basic mainpulation} *)

  (* [make l u] constructs an interal from two fiven dyadics. *)
  let make l u = { lower = from_val l; upper = from_val u }

  (* [lower i] computes the lower endpoint. *)
  let lower i = force_val i.lower

  (* [upper i] computes the upper endpoint. *)
  let upper i = force_val i.upper

  (* [flip i] exchanges the lower and upper endpoints. *)
  let flip i = { lower = i.upper; upper = i.lower }

  (* Compute the width of the interval *)
  let width ~prec ~round i = D.sub ~prec ~round (upper i) (lower i)

	let iwidth ~prec ~round i = make (width ~prec ~round i) (width ~prec ~round:(D.anti round) i)

  let of_dyadic q = make q q

	let of_string ?prec str = of_dyadic (D.of_string ?prec ~round:D.down str)
	(* XXX: need to figure how to handle strings that aren't exactly representable *)
	(* make (D.of_string ?prec ~round:D.down str) (D.of_string ?prec ~round:D.up str) *)

  let bottom = make D.negative_infinity D.positive_infinity

  let top = make D.positive_infinity D.negative_infinity

	let bin_or a b = make (D.min (lower a) (lower b)) (D.max (upper a) (upper b))

  (* \subsection{Testing for infinite endpoints and back-to-front.} *)

  (* [forward i] returns [true] if [i] is a front-to-back interval *)
  let forward i = D.leq (lower i) (upper i)

  (* [backward i] returns [true] if [i] is a back-to-front interval *)
  let backward i = D.gt (lower i) (upper i)

  (* [proper i] returns [true] of [i] is a front-to-back interval with finite endpoints. *)
  let proper i = forward i && D.is_number (lower i) && D.is_number (upper i)

  (* \subsection{String conversion} *)

  let to_string i =
	  let l = lower i in
		let lbrack = if false (*D.is_negative_infinity l*) then "(" else "[" in
		let r = upper i in
		let rbrack = if false (*D.is_positive_infinity r*) then ")" else "]" in
    lbrack ^ D.to_string (lower i) ^ ", " ^ D.to_string (upper i) ^ rbrack

  let to_string_number i =
    (* let a = lower i in
    let b = upper i in
      if D.is_number a && D.is_number b then
	let c = D.average a b in
	let r = D.halve ~round:D.up (D.sub ~round:D.up b a) in
	  D.to_string c ^ " +- " ^ D.to_string r
      else *)
	to_string i

  (* \subsection{Arithmetic} *)

  (* Results are computed to precision [prec] and rounded according to
     [round]. If [round] is [Dyadic.down] then the result approximates
     the true value from below. If [round] is [Dyadic.up] then the true
     value is approximated from above. It is perhaps more customary to
     always approximate the true value from below, but we need the other
     approximant in [Eval.upper]. *)

  let add ~prec ~round i j =
    let dnuor = D.anti round in
      { lower = lazy (D.add ~prec ~round (lower i) (lower j)) ;
	upper = lazy (D.add ~prec ~round:dnuor  (upper i) (upper j)) }

  let sub ~prec ~round i j =
    let dnuor = D.anti round in
      { lower = lazy (D.sub ~prec ~round (lower i) (upper j)) ;
	upper = lazy (D.sub ~prec ~round:dnuor (upper i) (lower j)) }

  let neg ~prec ~round i =
    let dnuor = D.anti round in
      { lower = lazy (D.neg ~prec ~round (upper i)) ;
	upper = lazy (D.neg ~prec ~round:dnuor (lower i)) }

  (* Kaucher multiplication of intervals is given by the following table.

     \begin{center}
     \begin{tabular}{|c|c|c|c|c|}
     \hline
     $[a,b] \times [c,d]$
     & $a, b \leq 0$ & $a \leq 0 \leq b$  & $b \leq 0 \leq a$  & $0 \leq a,b$ \\ \hline
     $ 0 \leq c, d$ & $[ad,bc]$ &  $[ad,bd]$ &  $[ac,bc]$ &  $[ac,bd]$ \\ \hline
     $ d \leq 0 \leq c$ & $[bd,bc]$ &   $[0,0]$ &    $[q,p]$  &  $[ac,ad]$ \\ \hline
     $ c \leq 0 \leq d$ & $[ad,ac]$ &   $[p,q]$ &    $[0,0]$  &  $[bc,bd]$ \\ \hline
     $ c, d \leq 0$ & $[bd,ac]$ &  $[bc,ac]$ &  $[bd,ad]$ &  $[bc,ad]$ \\ \hline
     \end{tabular}
     \end{center}

     Where $p = \min(ad,bc) \leq 0$ and $q = \max(ac,bd) \geq 0$.
  *)

  let mul ~prec ~round i j =
    let negative = D.negative in
      { lower = lazy (
	  let lmul = D.mul ~prec ~round in
	  let a = lower i in
	  let b = upper i in
	  let c = lower j in
	  let d = upper j in
	    if negative a then
	      if negative b then
		if negative d then lmul b d else lmul a d
	      else (* positive [b] *)
		if negative c then
		  if negative d then lmul b c else D.min (lmul a d) (lmul b c)
		else (* positive [c] *)
		  if negative d then D.zero else lmul a d
	    else (* positive [a] *)
	      if negative b then
		if negative c then
		  if negative d then lmul b d else D.zero
		else (* positive [c] *)
		  if negative d then D.max (lmul a c) (lmul b d) else lmul a c
	      else (* positive [b] *)
		if negative c then lmul b c else lmul a c) ;
	upper = lazy (
	  let umul = D.mul ~prec ~round:(D.anti round) in
	  let a = lower i in
	  let b = upper i in
	  let c = lower j in
	  let d = upper j in
	    if negative a then
	      if negative b then
		if negative c then umul a c else umul b c
	      else (* positive [b] *)
		if negative c then
		  if negative d then umul a c else D.max (umul a c) (umul b d)
		else (* positive [c] *)
		  if negative d then D.zero else umul b d
	    else (* positive [a] *)
	      if negative b then
		if negative c then
		  if negative d then umul a d else D.zero
		else (* positive [c] *)
		  if negative d then D.min (umul a d) (umul b c) else umul b c
	      else (* positive [b] *)
		if negative d then umul a d else umul b d)
      }

  (* Power by non-negative exponent. *)

  let pow ~prec ~round i k =
    let dnuor = D.anti round in
      if k mod 2 = 1 then
	{ lower = lazy (D.pow ~prec ~round:round (lower i) k) ;
	  upper = lazy (D.pow ~prec ~round:dnuor (upper i) k) }
      else
	let a = lower i in
	let b = upper i in
	  { lower = lazy (
	      let lpow = D.pow ~prec ~round in
		if D.negative a then
		  if D.negative b then
		    lpow b k
		  else (* non-negative [b] *)
		    D.zero
		else (* non-negative [a] *)
		  if D.negative b then
		    D.max (lpow a k) (lpow b k)
		  else (* non-negative [b] *)
		    lpow a k
	    ) ;
	    upper = lazy (
	      let upow = D.pow ~prec ~round:dnuor in
		if D.negative a then
		  if D.negative b then
		    upow a k
		  else (* non-negative [b] *)
		    D.max (upow a k) (upow b k)
		else (* non-negative [a] *)
		  if D.negative b then
		    D.zero
		  else (* non-negative [b] *)
		    upow b k
	    ) }


  let inv ~prec ~round i =
    let a = lower i in
    let b = upper i in
      { lower = lazy (
	  let linv = D.inv ~prec ~round in
	    match D.sgn a, D.sgn b with
	      | `negative, `negative -> linv b
	      | `zero, `negative -> linv b
	      | `positive, `negative -> D.positive_infinity
	      | `negative, `zero -> D.negative_infinity
	      | `zero, `zero -> D.negative_infinity
	      | `positive, `zero -> D.positive_infinity
	      | `negative, `positive -> D.negative_infinity
	      | `zero, `positive -> D.negative_infinity
	      | `positive, `positive -> linv b
	) ;
	upper = lazy (
	  let uinv = D.inv ~prec ~round:(D.anti round) in
	    match D.sgn a, D.sgn b with
	      | `negative, `negative -> uinv a
	      | `zero, `negative -> D.negative_infinity
	      | `positive, `negative -> D.negative_infinity
	      | `negative, `zero -> D.positive_infinity
	      | `zero, `zero -> D.positive_infinity
	      | `positive, `zero -> uinv a
	      | `negative, `positive -> D.positive_infinity
	      | `zero, `positive -> D.positive_infinity
	      | `positive, `positive -> uinv a
	) }

  let div ~prec ~round i j = mul ~prec ~round i (inv ~prec ~round j)

  let unop_monotone f ~prec ~round i =
    let dnuor = D.anti round in
    { lower = lazy (f prec round (lower i)) ;
    upper = lazy (f prec dnuor (upper i)) }

  let exp = unop_monotone (fun p r -> D.exp ~prec:p ~round:r)
  let erf = unop_monotone (fun p r -> D.erf ~prec:p ~round:r)
	let sin_monotone = unop_monotone (fun p r -> D.sin ~prec:p ~round:r)
	let cos_monotone = unop_monotone (fun p r -> D.cos ~prec:p ~round:r)


  (* I haven't carefully checked that this is correct! *)
	let sin_down ~prec i =
	  assert (forward i);
		if D.lt (D.of_int ~round:D.up 3) (width ~prec ~round:D.down i)
		  then make D.negative_one D.one
			else
			let a = lower i in
			let b = upper i in
			let deriva1 = D.cos ~prec ~round:D.down a in
			let derivb1 = D.cos ~prec ~round:D.down b in
			if D.nonnegative deriva1 && D.nonnegative derivb1 then
			   sin_monotone ~prec ~round:D.down i
			else
			let deriva2 = D.cos ~prec ~round:D.up a in
			let derivb2 = D.cos ~prec ~round:D.up b in
			if D.nonpositive deriva2 && D.nonpositive derivb2 then
			   sin_monotone ~prec ~round:D.down (flip i)
			else if D.nonnegative deriva1 && D.nonpositive derivb2 then
			  make (D.min (D.sin ~prec ~round:D.down a) (D.sin ~prec ~round:D.down b))
				      D.one
			else if D.nonpositive deriva1 && D.nonnegative derivb2 then
			  make D.negative_one
				     (D.max (D.sin ~prec ~round:D.up a) (D.sin ~prec ~round:D.up b))
			(* Not sure about the sign of either of the derivatives *)
			else make D.negative_one D.one

	(* I haven't carefully checked that this is correct! *)
	let cos_down ~prec i =
	  assert (forward i);
		if D.lt (D.of_int ~round:D.up 3) (width ~prec ~round:D.down i)
		  then make D.negative_one D.one
			else
			let a = lower i in
			let b = upper i in
			let negderiva1 = D.sin ~prec ~round:D.up a in
			let negderivb1 = D.sin ~prec ~round:D.up b in
			if D.nonpositive negderiva1 && D.nonpositive negderivb1 then
			   cos_monotone ~prec ~round:D.down i
			else
			let negderiva2 = D.sin ~prec ~round:D.down a in
			let negderivb2 = D.sin ~prec ~round:D.down b in
			if D.nonnegative negderiva2 && D.nonnegative negderivb2 then
			   cos_monotone ~prec ~round:D.down (flip i)
			else if D.nonpositive negderiva1 && D.nonnegative negderivb2 then
			  make (D.min (D.cos ~prec ~round:D.down a) (D.cos ~prec ~round:D.down b))
				      D.one
			else if D.nonnegative negderiva1 && D.nonpositive negderivb2 then
			  make D.negative_one
				     (D.max (D.cos ~prec ~round:D.up a) (D.cos ~prec ~round:D.up b))
			(* Not sure about the sign of either of the derivatives *)
			else make D.negative_one D.one

	let sin ~prec ~round i = if round = D.down
	  then sin_down ~prec i
		else flip (sin_down ~prec (flip i))

	let cos ~prec ~round i = if round = D.down
	  then cos_down ~prec i
		else flip (cos_down ~prec (flip i))

  (* \subsection{Interval splitting} *)

  (* [midpoint prec i] computes the midpoint of an interval [i]. It
     guarantees that the point is actually inside the interval (which
     means that it will use precision higher than [prec] if
     necessary. It works correctly for infinite and back-to-front
     intervals. For infinite intervals it goes closer to infinity as
     [prec] increases. *)

  let midpoint ~prec k i =
    let a = lower i in
    let b = upper i in
      match D.classify a, D.classify b with
	| `number, `number -> D.average a b
	| `negative_infinity, `positive_infinity
	| `positive_infinity, `negative_infinity -> D.zero
	| `negative_infinity, `number ->
	    if D.leq b D.negative_one then D.shift ~prec ~round:D.down b k
			else if D.leq b D.zero then D.sub ~prec ~round:D.down b D.one else D.negative_one
	| `positive_infinity, `number ->
	    if D.geq b D.one then D.shift ~prec ~round:D.up b k
			else if D.geq b D.zero then D.add ~prec ~round:D.up b D.one else D.one
	| `number, `positive_infinity ->
	    if D.geq a D.one then D.shift ~prec ~round:D.up a k
			else if D.geq a D.zero then D.add ~prec ~round:D.up a D.one else D.one
	| `number, `negative_infinity ->
	    if D.leq a D.negative_one then D.shift ~prec ~round:D.down a k
			else if D.leq a D.zero then D.sub ~prec ~round:D.down a D.one else D.negative_one
	| _ -> raise (Invalid_argument ("Interval.midpoint: " ^ to_string i))

  (* Split an interval into two smaller ones. *)

  let split ~prec k i =
    let m = lazy (midpoint ~prec k i) in
      ({ lower = i.lower;  upper = m }, { lower = m; upper = i.upper })

  (* [thirds prec i] computes points $m_1$ and $m_2$ which divide [i]
     into three roughly equal parts. If [i] is infinite it does a
     reasonable thing. *)

  let thirds ~prec k i =
    let i1, i2 = split prec k i in
      midpoint prec k i1, midpoint prec k i2

end;;
