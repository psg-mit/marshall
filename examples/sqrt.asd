let sqrt =
  fun a : real =>
    cut x
      left  (x < 0 \/ x * x < a)

      right (x > 0 /\ x * x > a)
;;