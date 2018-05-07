(* Prepared for the Computer Aided Security Proofs course at Aarhus, Denmark, October 2017
   - Aseem Rastogi, Microsoft Research *)

module Counter

open FStar.Preorder

open FStar.Heap
open FStar.ST

open FStar.MRef

(*
 * A monotonically increasing counter.
 *)

(* Preorder to enforce that the contents of the counter reference increase monotonically as the state evolves *)
private let incr_pre :relation int = fun n1 n2 -> n2 >= n1

(* Counter type, abstract for the clients *)
abstract type counter = mref int incr_pre

(* Ghost sel function *)
abstract let sel (h:heap) (c:counter) :GTot int = sel h c

(* Ghost addr_of function, this is the footprint of the counter *)
abstract let addr_of (c:counter) :GTot nat = Heap.addr_of c

(* Liveness of the counter *)
abstract let contains (h:heap) (c:counter) :Type0 = h `Heap.contains` c

(*
 * Freshness predicate, note this is not abstract, clients can reason with its defn
 * Counter allocation will provide freshness as a postcondition
 * This would allow clients to reason that the addr of the counter is separate from the already allocated refs
 *)
let fresh (c:counter) (h0:heap) (h1:heap) :Type0 =
    addr_of c `Heap.addr_unused_in` h0 /\ h1 `contains` c

abstract let alloc () :ST counter (requires (fun _       -> True))
                                  (ensures  (fun h0 c h1 -> modifies !{} h0 h1 /\  //alloc does not modify existing references in the heap
				                         fresh c h0 h1      /\  //the counter is fresh
				                         sel h1 c == 0))       //counter starts at 0
  = ST.alloc 0

abstract let read (c:counter) :ST int (requires (fun _       -> True))
                                    (ensures  (fun h0 n h1 -> h0 == h1 /\ sel h1 c == n))  //read does not modify the heap
  = ST.read c

abstract let incr (c:counter) :ST unit (requires (fun _       -> True))
                                       (ensures  (fun h0 _ h1 ->
				                  modifies (Set.singleton (addr_of c)) h0 h1 /\  //modifies only c
				                  sel h1 c == sel h0 c + 1))                     //incremented by 1
  = ST.write c (ST.read c + 1)

(*****  set up for the at_least predicate *****)

(* A private predicate *)
private let is_at_least_p (n:int) :int -> Type0 =  fun m -> m >= n

(* This is the stable predicate that the library exposes to the clients *)
abstract let is_at_least (c:counter) (n:int) = token c (is_at_least_p n)

(* Clients can witness the at_least predicate *)
abstract let witness_at_least (c:counter) (n:int)
  :ST unit (requires (fun h0      -> sel h0 c >= n))                  //precondition that the current counter value should be at least n
           (ensures  (fun h0 _ h1 -> h0 == h1 /\ c `is_at_least` n))  //you get the (total!) at_least predicate as the postcondition
  = witness_token c (is_at_least_p n)

(* Clients can recall the at_least predicate *)
abstract let recall_at_least (c:counter) (n:int)
  :ST unit (requires (fun _       -> c `is_at_least` n))
           (ensures  (fun h0 _ h1 -> h0 == h1 /\ sel h1 c >= n))  //you get that the current counter value is at least n
  = recall_token c (is_at_least_p n)


(***** Exercise ******)

(*
 * Intuitively, if we have c `is_at_least` n1, then for any n2, s.t. n1 >= n2, we should be able to derive c `is_at_least` n2. But still, this is not provable directly.
 *)
let lemma_is_at_least_lt (c:counter) (n1:int) (n2:int{n1 >= n2})
  :Lemma (requires (c `is_at_least` n1))
         (ensures  (c `is_at_least` n2))
  = admit ()


(*
 * The metatheory of monotonicity in F* provides a functoriality axiom in that says, if p and q are stable predicates w.r.t. the preorder of a reference r, and forall x. p x ==> q x, then token r p ==> token r q. See lemma_functoriality in ulib/FStar.MRef.fst. Prove the above lemma using it.
 *)
