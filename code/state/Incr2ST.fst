module Incr2ST

open FStar.Ref

// BEGIN: incr2
val incr : r:ref int -> ST unit (requires (fun h0 -> True))
  (ensures (fun h0 _ h2 -> exists h1 x. modifies !{} h0 h1 /\ x == sel h0 r /\
                                        modifies !{r} h1 h2 /\ sel h2 r == x+1))
let incr r = let x = !r in r := x + 1
// END: incr2
