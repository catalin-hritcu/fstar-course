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

(* We can put the informal proof as asserts in the code *)
let rec sum_rec_correct' (n:nat) : Lemma (sum_rec n = sum_tot n) =
  if n = 0 then
    assert(0 = (0+1) * 0 / 2)
  else
    (assert(sum_rec n = n + sum_rec (n-1));
     sum_rec_correct' (n-1);
     assert(n + sum_rec (n-1) = n + ((n * (n-1)) / 2)); (* by IH *)
     assert(n + ((n * (n-1)) / 2) = (2*n + n*(n-1)) / 2);
     assert((2*n + n*(n-1)) / 2 = (n*(n-1+2)) / 2);
     assert(((n*(n-1+2)) / 2) = ((n + 1) * n) / 2))

open FStar.Calc
open FStar.Tactics

#set-options "--z3rlimit 10"

(* Or better we can use `calc` statements for such proofs *)
let rec sum_rec_correct'' (n:nat) : Lemma (sum_rec n = sum_tot n) =
  if n = 0 then
    calc (==) {
      sum_rec 0            ; == {_ by (trefl())}
      0                    ; == {_ by (trefl())}
      ((0+1) * 0) / 2      ; == {_ by (trefl())}
      sum_tot 0            ;}
  else begin
    calc (==) {
      sum_rec n            ; == {}
      n + sum_rec (n-1)    ; == {sum_rec_correct'' (n-1)}
      n + (n * (n-1)) / 2  ; == {}
      (2*n + n*(n-1)) / 2  ; == {}
      (n*(n-1+2)) / 2      ; == {}
      ((n + 1) * n) / 2    ; == {_ by (trefl())}
      sum_tot n            ;}
    end
