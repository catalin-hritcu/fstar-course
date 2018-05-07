module CountST

open FStar.Ref

// BEGIN: count_st
let rec count_st' (r:ref nat) (n:nat) : ST unit (requires (fun h0 -> True))
    (ensures (fun h0 () h1 -> sel h1 r == sel h0 r + n /\ modifies !{r} h0 h1)) =
  if n > 0 then (r := !r + 1; count_st' r (n-1))

let rec count_st (n:nat) : ST nat (requires (fun h0 -> True))
    (ensures (fun h0 x h1 -> x == n /\ modifies !{} h0 h1)) =
  let r = alloc 0 in count_st' r n; !r
// END: count_st
