let sqrt =
  fun a : real =>
    cut x
      left  (x < 0 \/ x^2 < a)

      right (x > 0 /\ x^2 > a)
;;