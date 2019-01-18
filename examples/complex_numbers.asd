! Define a complex number
let complex =
    fun r: real =>
    fun im:real =>
    (r,im)
    ;;

! Take the product of two complex numbers
let product =
    fun z1 : real * real =>
    fun z2 : real * real =>
    (z1#1 * z2#0 - z1#1 * z2#1, z1#0 * z2#1 + z1#1 * z2#0)
    ;;

! Compute the sum of two complex numbers
let sum =
    fun z1 : real * real =>
    fun z2 : real * real =>
    (z1#0 + z2#0, z1#1 + z2#1)
    ;;

! Take only the real component
let get_real =
    fun z: real * real =>
    z#0
    ;;

! Take only the imaginary component
let get_im =
    fun z: real * real =>
    z#1
    ;;

! Take only the imaginary component
let norm =
    fun z: real * real =>
    sqrt (z#0 * z#0 + z1 * z1)
    ;;

!! A general idea of how to find the roots of unity.
!let roots_of_unity =
!    fun z : real * real =>
!    cut z  ! this isn't defined. Not sure how to define it.
!        (left  ((get_real (product (product z z) z)) - 1) < 0 /\
!               (norm z) < 1)
!
!        (right ((get_real (product (product z z) z)) - 1) < 0 \/
!               (norm z) > 1)
