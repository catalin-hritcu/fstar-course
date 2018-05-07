module ST
open FStar.TSet
open FStar.Heap
open FStar.ST

// Much simpler types for alloc, !, and :=

// BEGIN: alloc
  val alloc : #a:Type -> init:a -> ST (ref a)
    (requires (fun (h0:heap) -> True))
    (ensures (fun h0 r h1 -> modifies !{} h0 h1 /\ sel h1 r == init /\
                             ~(h0 `contains` r) /\ h1 `contains` r))
// END: alloc

// BEGIN: ops
  val (!): #a:Type -> r:ref a -> ST a
    (requires (fun (h0:heap) -> True))
    (ensures (fun h0 (x:a) h1 -> modifies !{} h0 h1 /\ x == sel h0 r))

  val (:=): #a:Type -> r:ref a -> v:a -> ST unit
    (requires (fun (h0:heap) -> True))
    (ensures (fun h0 _ h1 -> modifies !{r} h0 h1 /\ sel h1 r == v))
// END: ops
