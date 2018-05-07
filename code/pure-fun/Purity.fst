module Purity

open FStar.Mul

val incr : x:int -> Tot (y:int{x < y})
let incr x = x + 1

val factorial : nat -> Tot nat
(* val factorial : int -> Tot int  -- does not work, wrong! *)
let rec factorial n = (if n = 0 then 1 else n * (factorial (n - 1)))
