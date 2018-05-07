module Fact

open FStar.Mul

val factorial: nat -> Tot nat
let rec factorial n = 
  if n = 0 then 1 else n * (factorial (n - 1))

(* 1 >= 0 *)

(* n : nat *)
(* factorial : nat -> Tot nat *)
(* |-  *)
(* n * (factorial (n - 1)) >= 0 *)

(* n : nat, n != 0 |- n - 1 << n *)
