module IncrST

open FStar.Ref

// val incr : r:ref int -> St unit

// BEGIN: incr_type
val incr : r:ref int -> ST unit (requires (fun h0 -> True))
    (ensures (fun h0 _ h2 -> modifies !{r} h0 h2 /\ sel h2 r == sel h0 r + 1))
// END: incr_type
let incr r = (r := (!r + 1))

// BEGIN: modifies_trans
let modifies_trans (#a:Type) (s01 s12 : set nat) (h0 h1 h2 : heap) :
  Lemma (requires (modifies s01 h0 h1 /\ modifies s12 h1 h2))
        (ensures (modifies (s01 `Set.union` s12) h0 h2)) = ()
// END: modifies_trans

// BEGIN: two_refs
let two_refs (r1 r2 : ref int) : ST unit
  (requires (fun h0 -> addr_of r1 <> addr_of r2 /\
                       h0 `contains` r2))
  (ensures (fun h0 _ h1 -> modifies !{r1} h0 h1 /\
                           sel h1 r2 == sel h0 r2 /\ (* not entailed! *)
                           sel h1 r1 == sel h0 r1 + 1))
  = incr r1
// END: two_refs
