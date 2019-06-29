module Fact

open FStar.Mul

val factorial: nat -> Tot nat
let rec factorial n
  = if n = 0 then 1 else n * (factorial (n - 1))
