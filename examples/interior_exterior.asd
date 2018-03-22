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