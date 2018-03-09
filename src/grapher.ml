(* This will actually query our shape. *)
let in_interior i j = if i < 0 then 0 else 255;;

let compute_grid box_lower_left_x box_lower_left_y box_upper_right_x box_upper_right_y in_interior =
  let width = box_upper_right_x - box_lower_left_x + 1 in
  let height = box_upper_right_y - box_lower_left_y + 1 in
  let arr = Bigarray.Array2.create Bigarray.int Bigarray.c_layout width height in
  for i = box_lower_left_x to box_upper_right_x do
    for j = box_lower_left_y to box_upper_right_y do
      ignore(arr.{i - box_lower_left_x, j - box_lower_left_y} <- in_interior i j);
    done;
  done;
  (arr, width, height);
;;

let create_bmp arr width height =
  let oc = open_out "picture.bmp" in
  Printf.fprintf oc "P6\n%d %d\n255\n" width height;
  for y = 0 to pred height do
    for x = 0 to pred width do
      output_char oc (char_of_int arr.{x,y});
      output_char oc (char_of_int arr.{x,y});
      output_char oc (char_of_int arr.{x,y});
    done;
  done;
  output_char oc '\n';
  flush oc;
  ;;

let plot box_lower_left_x box_lower_left_y box_upper_right_x box_upper_right_y in_interior =
  let arr, width, height = compute_grid box_lower_left_x box_lower_left_y box_upper_right_x box_upper_right_y in_interior in
  create_bmp arr width height;
  print_endline "Bitmap created!"
  ;;