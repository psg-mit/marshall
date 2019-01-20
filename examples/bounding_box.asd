#use "examples/cad.asd";;

let rightmost_extent =
  fun shape : ((real * real -> bool) -> bool)
            * (real * real -> bool) =>
  dedekind_cut (fun q : real => exists_shape shape (fun x : real * real => lt q x#0))
;;

let leftmost_extent =
  fun shape : ((real * real -> bool) -> bool)
            * (real * real -> bool) =>
  dedekind_cut (fun q : real => (shape#0) (fun x : real * real => lt q x#0))
;;

let topmost_extent =
  fun shape : ((real * real -> bool) -> bool)
            * (real * real -> bool) =>
  dedekind_cut (fun q : real => exists_shape shape (fun x : real * real => lt q x#1))
;;

let bottommost_extent =
  fun shape : ((real * real -> bool) -> bool)
            * (real * real -> bool) =>
  dedekind_cut (fun q : real => (shape#0) (fun x : real * real => lt q x#1))
;;

let get_bounding_box =
    fun shape : ((real * real -> bool) -> bool)
              * (real * real -> bool) =>
    (leftmost_extent shape, rightmost_extent shape,
     topmost_extent shape, bottommost_extent shape)
    ;;
