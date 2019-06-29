module FactorialST

open FStar.Heap
open FStar.ST
open FStar.Mul

val factorial_tot : nat -> Tot nat
let rec factorial_tot x = if x = 0 then 1 else x * factorial_tot (x - 1)

val factorial : r1:ref nat -> r2:ref nat -> ST unit (requires (fun h0     -> addr_of r1 <> addr_of r2))
                                                    (ensures (fun h0 _ h1 -> sel h1 r2 = factorial_tot (sel h0 r1) /\
                                                                             sel h1 r1 = 0 /\
                                                                             modifies !{r1,r2} h0 h1))
let rec factorial r1 r2 =
  let x1 = !r1 in
  if x1 = 0
  then r2 := 1
  else 
    (r1 := x1 - 1;
     factorial r1 r2;
     r2 := !r2 * x1)
