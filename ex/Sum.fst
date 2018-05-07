module Sum

open FStar.Mul

let rec sum_rec (n:nat) = if n > 0 then n + sum_rec (n-1) else 0

let sum_tot (n:nat) = ((n+1) * n) / 2

let rec sum_rec_correct (n:nat) : Lemma (sum_rec n = sum_tot n) =
  admit() (* replace this admit by a real proof *)
