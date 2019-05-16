#use "./cad.asd";;

! --------- Make the car ---------

! Set the starting position and velocity
let x = -1.5;;
let v = 3;;

! Create the car
let car =
  let wheel = scale_x_y_ok 0.09 0.09 unit_disk_ok in
  let right_wheel = translate_ok (0.25, 0.125) wheel in
  let left_wheel = translate_ok (-0.25, 0.125) wheel in
  let car_body1 = scale_x_y_ok 0.375 0.075 unit_square in
  let car_body2 = translate_ok (0, -0.125) (scale_x_y_ok 0.25 0.175 unit_square) in
  let car_body = union_ok car_body1 car_body2 in
  let wheels = union_ok left_wheel right_wheel in
  translate_ok (-0.375 + x, 0) (union_ok car_body wheels)
  ;;

! Create the intersection
let crossing = scale_x_y_ok 0.25 0.25 unit_square;;

! Make the system
let system = translate_ok (0.25, 0) (union_ok crossing car);;

