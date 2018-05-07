module Types

open FStar.Mul

type nat = x:int{x>=0}

val factorial : nat -> nat
(* val factorial : x:int -> Pure int (requires (b2t (x >= 0))) *)
(*                                   (ensures (fun y -> y >= 0)) *)
let rec factorial n = (if n = 0 then 1 else n * (factorial (n - 1)))

