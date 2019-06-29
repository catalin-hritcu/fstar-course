module Heap2

  open FStar.TSet

  val heap : Type
  val ref : Type -> Type

  val sel : #a:Type -> heap -> ref a -> GTot a
  val addr_of: #a:Type -> ref a -> GTot nat

  val contains : #a:Type -> heap -> ref a -> Type0

// BEGIN: modifies_contains
  let modifies (s:FStar.TSet.set nat) (h0 h1 : heap)
  = forall a (r:ref a). (~(addr_of r `mem` s) /\ h0 `contains` r)
                                                    ==> sel h1 r == sel h0 r
// END: modifies_contains
