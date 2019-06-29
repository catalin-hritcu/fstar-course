module FactorialST

open FStar.Heap
open FStar.ST
open FStar.Mul

// BEGIN: factorial_ex
(* A purely-functional factorial function *)

val factorial_tot : nat -> Tot nat
let rec factorial_tot x = 
  if x = 0 then 1 else x * factorial_tot (x - 1)

(* Below is a stateful factorial function, where 
     a) r1 is a reference to a number whose factorial is computed 
     b) r2 is a reference where we will store the factorial of !r1 
     c) the factorial of !r1 stored in r2 agrees with factorial_tot
               
   Exercise: 1) give a precise spec to factorial according to a), b), c)
             2) remove the admit() clause with a real implementation    *)

val factorial : r1:ref nat -> r2:ref nat -> 
                                  ST unit (requires (fun h0      -> True))
                                          (ensures  (fun h0 _ h1 -> True))
let rec factorial r1 r2 =
  admit()
// END: factorial_ex
