(* Prepared for the Computer Aided Security Proofs course at Aarhus, Denmark, October 2017
   - Aseem Rastogi, Microsoft Research *)

module InitFreezeRef

open FStar.Preorder
open FStar.Heap
open FStar.ST

open FStar.MRef

(*
 * A reference that starts uninitialized (unreadble), can be written to (mutable), and then ultimately can be frozen
 *)

(*
 * Three states that the refernce can be in
 *)
private type rstate (a:Type) =
  | Empty  : rstate a        //starts as Empty
  | Mutable: v:a -> rstate a  //becomes Mutable
  | Frozen : v:a -> rstate a  //frozen ultimately

(* Trying to define the state evolution as a preorder *)
private let evolve_broken0 (a:Type) :relation (rstate a) =
  fun r1 r2 ->
  match r1, r2 with
  | Empty,      Mutable _
  | Mutable _,  Mutable _ -> True
  | Mutable v1, Frozen v2 -> v1 == v2
  | _, _ -> False

(* private let evolve_broken (a:Type) :preorder (rstate a) = evolve_broken0 a
   -- fails as it should *)

private let evolve (a:Type) :relation (rstate a) =
  fun r1 r2 -> admit ()

(* Abstract type eref *)
abstract type eref (a:Type) :Type0 = mref (rstate a) (evolve a)

(* Ghost addr_of function *)
abstract let addr_of (#a:Type0) (r:eref a) :GTot nat = addr_of r

(* Liveness of eref *)
abstract let contains (#a:Type0) (h:heap) (r:eref a) :Type0 = h `Heap.contains` r

(* Freshness predicate *)
let fresh (#a:Type0) (r:eref a) (h0 h1:heap) :Type0 =
  addr_of r `Heap.addr_unused_in` h0 /\ h1 `contains` r

(*
 * sel is a bit tricky, it returns (option a)
 * sel from an Empty reference returns None
 * But our high-level interface for reading reference should ensure that read cannot be called on Empty refs
 *)
abstract let sel (#a:Type0) (h:heap) (r:eref a) :GTot (option a)
  = let x = sel h r in
    match x with
    | Empty     -> None
    | Mutable x
    | Frozen  x -> Some x

(***** set up predicates *****)

(* An eref is readable if it is not Empty *)
private let readable_pred (#a:Type) :rstate a -> Type
  = fun x -> (~ (Empty? x))

(* Clients can to play with readable predicate *)
abstract let readable (#a:Type0) (r:eref a) :Type0
  = token r readable_pred

(* Let's try to do the same for writable, a Frozen ref is non mutable *)
private let writable_pred (#a:Type0) :rstate a -> Type
  = fun x -> Empty? x \/ Mutable? x

(* abstract let writable (#a:Type0) (r:eref a) :Type0
  = token r (writable_pred #a)
  -- fails as it should, why? *)

(* Mutability is a stateful invariant, note this is still abstract, our interface needs to take care of it *)
abstract let writable_in (#a:Type0) (r:eref a) (h:heap) :Type0
  = let x = Heap.sel h r in Empty? x \/ Mutable? x

(* Setup for frozen predicate *)
private let frozen_at_pred (#a:Type0) (x:a) :rstate a -> Type
  = fun y -> y == Frozen x

(* frozen_at_pred is stable *)
abstract let frozen_at (#a:Type0) (r:eref a) (x:a) :Type0
  = token r (frozen_at_pred x)

(* fun begins *)

abstract let alloc (a:Type0)
  :ST (eref a) (requires (fun _       -> True))
               (ensures  (fun h0 r h1 ->
	                  modifies !{} h0 h1 /\  //existing refs are unmodified
			  fresh r h0 h1      /\  //returned eref's addr is different from all existing refs
			  r `writable_in` h1 /\  //the returned eref is writatble
			  sel h1 r == None))    //sel returns None
  = admit ()

abstract let write (#a:Type0) (r:eref a) (x:a)
  :ST unit (fun h0      -> r `writable_in` h0)  //stateful precondition that eref is mutable
           (fun h0 _ h1 -> modifies (Set.singleton (addr_of r)) h0 h1 /\  //only modify the addr of eref
	                readable r                                 /\  //the eref now becomes (or remains) readale
	                r `writable_in` h1                         /\  //eref is still writable
			sel h1 r == Some x)                            //sel returns what you wrote
  = admit ()

abstract let read (#a:Type0) (r:eref a{readable r})  //note the precondition asks for readability of the eref
  :ST a (requires (fun _       -> True))
        (ensures  (fun h0 x h1 -> h0 == h1 /\            //heap remains same
	                       sel h1 r == Some x))  //return what sel returns
  = admit ()

abstract let freeze (#a:Type0) (r:eref a{readable r})  //the precondition that we need is still readable
  :ST a (fun _       -> True)
        (fun h0 x h1 -> modifies (Set.singleton (addr_of r)) h0 h1 /\  //only modify the eref
	             sel h0 r == sel h1 r                       /\  //value remains same
		     sel h0 r == Some x                         /\  //is what we return
	             r `frozen_at` x)                              //and you get the stable predicate
  = admit ()

abstract let recall_freeze (#a:Type0) (r:eref a) (x:a{r `frozen_at` x})
  :ST unit (requires (fun _       -> True))
           (ensures  (fun h0 _ h1 -> h0 == h1 /\ sel h1 r == Some x))
  = admit ()
