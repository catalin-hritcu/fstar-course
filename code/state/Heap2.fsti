module Heap2

  val heap : Type
  val ref : Type -> Type

  val sel : #a:Type -> heap -> ref a -> GTot a
  val addr_of: #a:Type -> ref a -> GTot nat

// BEGIN: modifies_contains
  val contains : #a:Type -> heap -> ref a -> Type0

  let modifies (s:FStar.TSet.set nat) (h0 h1 : heap) : Type0 =
    (forall (a:Type) (r:ref a).{:pattern (sel h1 r)}
      (~(addr_of r `FStar.TSet.mem` s) /\ h0 `contains` r) ==> sel h1 r == sel h0 r)
// END: modifies_contains
