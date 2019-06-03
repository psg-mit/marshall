let sqrt (a : real) : real =
  cut x : [0, inf)
    left x^2 < a
    right x^2 > a;;
