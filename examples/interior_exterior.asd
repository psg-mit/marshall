# interior and exterior for points
let point_interior = fun test_x : real =>
                     fun test_y : real => 
                     False
    ;;

let point_exterior =   
    fun x : real =>
    fun y : real =>

    fun test_x : real =>
    fun test_y : real =>

    test_x < x \/ test_x > x \/ test_y < y \/ test_y > y
    ;;

let point_forall = 
    fun x : real =>
    fun y : real =>    
    fun p : real * real -> prop =>
    p (x, y) 
    ;;

let point_exists = point_forall;;

#use "examples/jesse_cad.asd";;
#use "examples/cad.asd";;


# interior and exterior for line (half-planes)
let shape_interior = 
    fun test_x : real =>
    fun test_y : real =>
    fun shape : real -> real -> prop*prop =>
    (shape test_x test_y)#0
    ;;

let shape_exterior = 
    fun test_x : real =>
    fun test_y : real =>
    fun shape : real -> real -> prop*prop =>
    (shape test_x test_y)#1
    ;;

let point_exists = 
    fun p : real -> real -> prop*prop =>
    fun p : real -> real -> prop*prop =>
    # exists all points x,y in shape, 
    (shape x y) /\ p (x, y) 
    ;;

let line_forall = 
    fun p : real -> real -> prop*prop =>
    forall x : [-1, 1],
    forall y : [-1, 1],
    p (x, y) 
    ;;

# want to quantify over arbitrary scalings of a circle/square etc.