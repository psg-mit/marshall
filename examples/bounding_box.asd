!#use "examples/cad.asd";;

let rightmost_extent =
  fun shape : ((real -> real -> bool) -> bool)
            * (real -> real -> bool) =>
  dedekind_cut (fun x : real => exists_shape shape (fun x' : real => fun y' : real => lt x x'))
;;

let leftmost_extent =
  fun shape : ((real -> real -> bool) -> bool)
            * (real -> real -> bool) =>
  dedekind_cut (fun x : real => (shape#0) (fun x' : real => fun y' : real => lt x x'))
;;

let topmost_extent =
  fun shape : ((real -> real -> bool) -> bool)
            * (real -> real -> bool) =>
  dedekind_cut (fun y : real => exists_shape shape (fun x' : real => fun y' : real => lt y y'))
;;

let bottommost_extent =
  fun shape : ((real -> real -> bool) -> bool)
            * (real -> real -> bool) =>
  dedekind_cut (fun y : real => (shape#0) (fun x' : real => fun y' : real => lt y y'))
;;

let get_bounding_box =
    fun shape : ((real -> real -> bool) -> bool)
              * (real -> real -> bool) =>
    (leftmost_extent shape, rightmost_extent shape,
     topmost_extent shape , bottommost_extent shape)
    ;;
