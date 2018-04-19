! create the quantifiers for the unit square.
let forall_exists_square = 
  fun p : real -> real -> prop =>
  let forall_square =   
    fun p : real -> real -> prop =>
    forall x : [-1, 1],
    forall y : [-1, 1],
    (square x y)#1 \/ p x y in
  let exists_square =
    fun p : real -> real -> prop =>
    exists x1 : [-1, 1],
    exists y1 : [-1, 1],
    (square x1 y1)#0 /\ p x1 y1 in 
  (forall_square p, exists_square p)
  ;;

! unit disk centered at origin
let square_quantified =
  (square , forall_exists_square)
;;

let scale_x_y_shape =
  fun shape : (real -> real -> prop * prop)
            * ((real -> real -> prop) -> prop * prop) =>
  fun cx : real =>
  fun cy : real =>
  fun p : real -> real -> prop =>
  shape#1 (fun x : real => fun y : real => (p (x / cx) (y / cy)))
  ;;          

  ! fun x : real => fun y : real =>
  ! shape#0 (x / cx) (y / cy)
  !!(fun x : real => fun y : real =>
  !!  shape#0 (x / cx) (y / cy)
  !!  , fun p : real -> real -> prop =>
  !!  shape#1 (fun x : real => fun y : real => (p x y)) 
  !!)
  ;;

!let forall_square =
!  fun p : real -> real -> prop =>
!  forall x : [-1, 1],
!  forall y : [-1, 1],
!  (square x y)#1 \/ p x y
!  ;;

!let exists_square =
!  fun p : real -> real -> prop =>
!  exists x1 : [-1, 1],
!  exists y1 : [-1, 1],
!  (square x1 y1)#0 /\ p x1 y1
!;;

let test_prop = 
  fun x1 : real =>
  fun x2 : real =>
  x1 < x2
  ;;

                