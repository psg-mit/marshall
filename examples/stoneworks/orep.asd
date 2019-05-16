#use "../bool.asd";;

type OShape E = E -> bool;;

! O-representation

! A shape is a function from R^2 to a pair of predicates.
! The first predicate says if a point in the plane is strictly
! *inside* the shape, and the second says it if it strictly *outside*

let unit_interval_o : OShape real =
  fun x : real => 0 <b x && x <b 1;;

! unit disk centered at origin
let unit_disk_o : OShape (real^2) = fun x : real^2 => x#0^2 + x#1^2 <b 1;;

! rectangle centered at the origin
let rectangle_o (width height : real) : OShape (real^2) =
  fun x : real^2 =>
      (- width  / 2) <b x#0  &&  x#0 <b (width  / 2)
  &&  (- height / 2) <b x#1  &&  x#1 <b (height / 2)
;;

let unit_square_o : OShape (real^2) = rectangle_o 2 2;;

let product_o E F (oe : OShape E) (of : OShape F) : OShape (E * F) =
  fun x : E * F => oe x[0] && of x[1];;

let empty_o E : OShape E = fun x : E => ff;;
let full_o E : OShape E = fun x : E => tt;;

! Compute the union of two shapes.
let union_o E (o1 o2 : OShape E) : OShape E =
  fun x : E => o1 x || o2 x ;;

! Compute the intersection of two shapes.
let intersection_o E (o1 o2 : OShape E) : OShape E =
  fun x : E => o1 x && o2 x;;

! The set-theoretic complement of a shape. Not sure where
! this may come in handy.
let complement_o E (shape : OShape E) =
  fun x : E => ~ (shape x) ;;

let contramap E F (f : F -> E) (o : E -> bool) : F -> bool =
  fun x : F => o (f x);;

let translate_o (trans : real^2) (shape : OShape (real^2)) =
  fun x : real^2 =>
    shape (x#0 - trans#0, x#1 - trans#1)
;;

! Analyses
let is_in E (x : E) (o : OShape E) : bool = o x;;

! Is a shape nonempty?
let nonempty E (exists_E : (E -> prop) -> prop) (o : OShape E) : prop =
  exists_E (fun x : E => is_true (o x));;


! Additional functions

! scaling centered at the origin!
! factor should be a *positive* real number
let scale_o (factor : real) (shape : OShape (real^2)) =
  fun x : real^2 =>
  shape (x#0 / factor, x#1 / factor)
;;

let scale_x_y_o (cx : real) (cy : real)
    (shape : OShape (real^2)) =
    fun x : real^2 => shape (x#0 / cx, x#1 / cy);;

let exists_R2 (P : real^2 -> prop) : prop = Exists x : real, Exists y : real, P (x, y);;

let nonempty_R2 : OShape (real^2) -> prop = nonempty {real^2} exists_R2;;

! Do two shapes overlap?
let overlaps (shape_1 shape_2 : OShape (real^2)) : prop =
  nonempty_R2 (intersection_o {real^2} shape_1 shape_2)
;;


! Implement line with an interior in the direction of the normal.
let line (nx ny : real) : OShape (real^2) =
      fun x : real^2 =>
      0 <b (nx * x#0 + ny * x#1);;