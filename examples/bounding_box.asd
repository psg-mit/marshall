#use "examples/cad.asd";;

let rightmost_extent =
  fun shape : (real * real -> bool) -> bool =>
  dedekind_cut (fun q : real => exists_k shape (fun x : real * real => q <b x#0))
;;

let leftmost_extent =
  fun shape : (real * real -> bool) -> bool =>
  dedekind_cut (fun q : real => shape (fun x : real * real => q <b x#0))
;;

let topmost_extent =
  fun shape : (real * real -> bool) -> bool =>
  dedekind_cut (fun q : real => exists_k shape (fun x : real * real => q <b x#1))
;;

let bottommost_extent =
  fun shape : (real * real -> bool) -> bool =>
  dedekind_cut (fun q : real => shape (fun x : real * real => q <b x#1))
;;

let get_bounding_box =
    fun shape : (real * real -> bool) -> bool =>
    (leftmost_extent shape, rightmost_extent shape,
     topmost_extent shape, bottommost_extent shape)
    ;;
