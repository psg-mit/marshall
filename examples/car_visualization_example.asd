#use "examples/quantified_interior_exterior_cad.asd";;

! --------- Make the car ---------

! Set the starting position and velocity
let x = -1.5;;
let v = 3;;

! Create the car
let car =
  let wheel = (scale_x_y_shape 0.09 0.09 circle_quantified) in
  let right_wheel = (translate_shape_x_y wheel 0.25 0.125) in
  let left_wheel = (translate_shape_x_y  wheel -0.25 0.125) in
  let car_body1 = (scale_x_y_shape 0.75 0.15 square_quantified) in
  let car_body2 = (translate_shape_x_y (scale_x_y_shape 0.5 0.35 square_quantified)  0 -0.125) in
  let car_body = union_quantified car_body1 car_body2 in
  let wheels = union_quantified left_wheel right_wheel in
  translate_shape_x_y (union_quantified car_body wheels) (-0.375 + x) 0
  ;;

! Create the intersection
let crossing = (scale_x_y_shape 0.5 0.5 square_quantified);;

! Make the system
let system = translate_shape_x_y (union_quantified crossing car) 0.25 0;;

