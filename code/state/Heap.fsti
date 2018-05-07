module Heap
  open FStar.TSet

// BEGIN: heap_model
  val heap : Type
  val ref : Type -> Type

  val sel : #a:Type -> heap -> ref a -> GTot a
  val addr_of: #a:Type -> ref a -> GTot nat

  let modifies (s:set nat) (h0 h1 : heap) : Type0 =
  (forall (a:Type) (r:ref a).{:pattern (sel h1 r)}
    (~(addr_of r `mem` s)) ==> sel h1 r == sel h0 r)
// END: heap_model
