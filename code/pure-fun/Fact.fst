module Fact

open FStar.Mul

// BEGIN: factorial
val factorial: nat -> nat

let rec factorial n
  = if n = 0 then 1 else n * (factorial (n - 1))
// END: factorial
