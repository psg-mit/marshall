!#use "examples/jesse_cad.asd";;
!#use "examples/cad.asd";;
!#plot 40 (shape_to_bool (scale_x_y_shape .5 quantify_unit_square));;

let rightmost_extent =
  fun shape : (real -> real -> prop * prop)
            * ((real -> real -> prop) -> prop * prop) =>
  cut x
     left  (((shape#1) (fun x' : real => fun y' : real => x < x'))#1)
     right (((shape#1) (fun x' : real => fun y' : real => x' < x))#0)
;;

let leftmost_extent =
  fun shape : (real -> real -> prop * prop)
            * ((real -> real -> prop) -> prop * prop) =>
  cut x
     left  (((shape#1) (fun x' : real => fun y' : real => x < x'))#0)
     right (((shape#1) (fun x' : real => fun y' : real => x' < x))#1)
;;

let topmost_extent =
  fun shape : (real -> real -> prop * prop)
            * ((real -> real -> prop) -> prop * prop) =>
  cut y
     left  (((shape#1) (fun x' : real => fun y' : real => y < y'))#1)
     right (((shape#1) (fun x' : real => fun y' : real => y' < y))#0)
;;

let bottommost_extent =
  fun shape : (real -> real -> prop * prop)
            * ((real -> real -> prop) -> prop * prop) =>
  cut y
     left  (((shape#1) (fun x' : real => fun y' : real => y < y'))#0)
     right (((shape#1) (fun x' : real => fun y' : real => y' < y))#1)
;;

let get_bounding_box = 
    fun shape : (real -> real -> prop*prop) *
                ((real -> real -> prop) -> prop*prop) =>
    (leftmost_extent shape, rightmost_extent shape,
     topmost_extent shape , bottommost_extent shape)  
    ;;
