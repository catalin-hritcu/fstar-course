module SumST

open FStar.Ref
open FStar.Mul

let rec sum_rec (n:nat) = if n > 0 then n + sum_rec (n-1) else 0

let sum_tot (n:nat) = ((n+1) * n) / 2

let rec sum_rec_correct (n:nat) : Lemma (sum_rec n = sum_tot n) =
  if n > 0 then sum_rec_correct (n-1)

let rec sum_st' (r:ref nat) (n:nat) : ST unit (requires (fun h0 -> True))
    (ensures (fun h0 () h1 -> sel h1 r == sel h0 r + sum_rec n /\
                              modifies !{r} h0 h1)) = 
  if n > 0 then (r := !r + n; sum_st' r (n-1))

let rec sum_st (n:nat) : ST nat (requires (fun h0 -> True))
    (ensures (fun h0 x h1 -> x == sum_rec n /\ modifies !{} h0 h1)) =
  let r = alloc 0 in sum_st' r n; !r
