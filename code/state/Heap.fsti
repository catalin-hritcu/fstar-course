module Heap
  open FStar.TSet

// BEGIN: heap_model
  val heap : Type
  val ref  : Type -> Type

  val sel     : #a:Type -> heap -> ref a -> GTot a   (* in Ghost effect *)
  val addr_of : #a:Type -> ref a -> GTot nat         (* in Ghost effect *)

  let modifies (s:set nat) (h0 h1 : heap)

  = forall a (r:ref a). ~(addr_of r `mem` s) ==> sel h1 r == sel h0 r
// END: heap_model
