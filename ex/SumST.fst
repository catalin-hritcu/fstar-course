module SumST

open FStar.Ref
open FStar.Mul

// BEGIN: sum_tot
let sum_tot (n:nat) = ((n+1) * n) / 2  (* equal to sum_rec, see lect. 1 *)
// END: sum_tot

(* Exercise: strengthen spec of sum_st' below so that sum_st verifies without admit *)

// BEGIN: sum_st
let rec sum_st' (r:ref nat) (n:nat)
  : ST unit (requires (fun _ -> True))
            (ensures  (fun _ _ _ -> True))

= if n > 0 then (r := !r + n;
                 sum_st' r (n - 1))


let rec sum_st (n:nat)
  : ST nat (requires (fun _ -> True))
           (ensures  (fun h0 x h1 -> x == sum_tot n /\
                                     modifies !{} h0 h1))
= let r = alloc 0 in
  sum_st' r n;
  admit ();
  !r
// END: sum_st
