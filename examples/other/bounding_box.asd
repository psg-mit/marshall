#use "../stoneworks/cad.asd";;

let rightmost_extent (shape : (real^2 -> bool) -> bool) : real =
  dedekind_cut (fun q : real => exists {real^2} shape (fun x : real^2 => q <b x#0))
;;

let leftmost_extent (shape : (real^2 -> bool) -> bool) : real =
  dedekind_cut (fun q : real => shape (fun x : real^2 => q <b x#0))
;;

let topmost_extent (shape : (real^2 -> bool) -> bool) : real =
  dedekind_cut (fun q : real => exists {real^2} shape (fun x : real^2 => q <b x#1))
;;

let bottommost_extent (shape : (real^2 -> bool) -> bool) : real =
  dedekind_cut (fun q : real => shape (fun x : real^2 => q <b x#1))
;;

let get_bounding_box (shape : (real^2 -> bool) -> bool) =
    (leftmost_extent shape, rightmost_extent shape,
     topmost_extent shape, bottommost_extent shape)
    ;;
