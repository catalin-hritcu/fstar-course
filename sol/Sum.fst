module Sum

open FStar.Mul

let rec sum_rec (n:nat) = if n > 0 then n + sum_rec (n-1) else 0

let sum_tot (n:nat) : GTot nat = ((n+1) * n) / 2

let rec sum_rec_correct (n:nat) : Lemma (sum_rec n = sum_tot n) =
// BEGIN: proof
  if n > 0 then sum_rec_correct (n-1)
// END: proof

(* Case: n = 0 -- trivial
   Case: n > 0
     sum_rec (n-1) = (if n-1 = 0 then 0 else (n * (n-1))) / 2)
     n + sum_rec (n-1) = n + (if n-1 = 0 then 0 else (n * (n-1)) / 2)
                       = if n-1 = 0 then n else n + (n * (n-1)) / 2)
                                              = (2n + n^2 - n) / 2
                                              = (n^2 + n) / 2
                                              = ((n+1) * n) / 2 *)
