#use "examples/bool.asd";;

! O-representation

! A shape is a function from R^2 to a pair of predicates.
! The first predicate says if a point in the plane is strictly
! *inside* the shape, and the second says it if it strictly *outside*

! Implement line with an interior in the direction of the normal.
let line (nx ny : real) : real^2 -> bool =
      fun x : real^2 =>
      0 <b (nx * x#0 + ny * x#1);;

let translate (trans : real^2) (shape : real^2 -> bool) =
  fun x : real^2 =>
    shape (x#0 - trans#0, x#1 - trans#1)
;;

! rectangle centered at the origin
let rectangle (width height : real) =
  fun x : real^2 =>
      (- width  / 2) <b x#0  &&  x#0 <b (width  / 2)
  &&  (- height / 2) <b x#1  &&  x#1 <b (height / 2)
;;

! scaling centered at the origin!
! factor should be a *positive* real number
let scale (factor : real) (shape : real^2 -> bool) =
  fun x : real^2 =>
  shape (x#0 / factor, x#1 / factor)
;;

let scale_x_y (cx : real) (cy : real)
    (shape : real^2 -> bool) =
    fun x : real^2 => shape (x#0 / cx, x#1 / cy);;

! unit disk centered at origin
let unit_disk = fun x : real^2 => x#0^2 + x#1^2 <b 1;;

! Compute the intersection of two shapes.
let intersection E (o1 o2 : E -> bool) : E -> bool =
  fun x : E => o1 x && o2 x;;

! Compute the union of two shapes.
let union E (o1 o2 : E -> bool) : E -> bool =
  fun x : E => o1 x || o2 x ;;

! The set-theoretic complement of a shape. Not sure where
! this may come in handy.
let complement E (shape : E -> bool) =
  fun x : E => ~ (shape x) ;;

let contramap E F (f : F -> E) (o : E -> bool) : F -> bool =
  fun x : F => o (f x);;

! Is a shape nonempty?
let nonempty E (exists_E : (E -> prop) -> prop) (s : E -> bool) : prop =
  exists_E (fun x : E => is_true (s x));;

let exists_R2 (P : real^2 -> prop) : prop = exists x : real, exists y : real, P (x, y);;

let nonempty_R2 : (real^2 -> bool) -> prop = nonempty {real^2} exists_R2;;

! Do two shapes overlap?
let overlaps (shape_1 : real^2 -> bool) (shape_2 : real^2 -> bool) : prop =
  nonempty_R2 (intersection {real^2} shape_1 shape_2)
;;
