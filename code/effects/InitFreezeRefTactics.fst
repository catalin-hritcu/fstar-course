(* Prepared for the Computer Aided Security Proofs course at Aarhus, Denmark, October 2017
   - Aseem Rastogi, Microsoft Research *)

module InitFreezeRefTactics

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
private let evolve_broken (a:Type) :relation (rstate a) =
  fun r1 r2 ->
  match r1, r2 with
  | Empty,      Mutable _
  | Mutable _,  Mutable _ -> True
  | Mutable v1, Frozen v2 -> v1 == v2
  | _, _ -> False

(* private let evolve_broken (a:Type) :preorder (rstate a) = evolve_broken0 a
   -- fails as it should *)

noeq type multi (a:Type) (r : a -> a -> Type0) : a -> a -> Type =
| Multi_step : x:a -> y:a -> r x y -> multi a r x y
| Multi_refl : x:a -> multi a r x x
| Multi_trans : x:a -> y:a -> z:a -> multi a r x y -> multi a r y z -> multi a r x z

open FStar.Tactics
open FStar.Squash

let multi_preorder (a:Type) (r:relation a)
    : Lemma (preorder_rel (multi a r)) =
  assert_by_tactic (preorder_rel (multi a r)) (
    norm [delta];;
    split;; iseq [
       exact (quote (return_squash (return_squash
                             (fun x -> (Multi_refl #a #r x)))))
    ;
      (x <-- forall_intro;
       y <-- forall_intro;
       z <-- forall_intro;
       h <-- implies_intro;
       and_elim (pack (Tv_Var h));;
       h1 <-- implies_intro;
       h2 <-- implies_intro;
       x' <-- unquote (pack (Tv_Var x));
       y' <-- unquote (pack (Tv_Var y));
       z' <-- unquote (pack (Tv_Var z));
       // dump "print goal";;
       mapply (quote (Multi_trans #a #r x' y' z'));;
       apply (return (pack (Tv_Var h1)));;
       apply (return (pack (Tv_Var h2))))
    ]
  )

let multi_contains (a:Type) (r:relation a) (x y : a)
    : Lemma (r x y ==> multi a r x y) [SMTPat (multi a r x y)] =
  assert_by_tactic (r x y ==> multi a r x y) (
    h <-- implies_intro;
    mapply (quote (Multi_step #a #r x y));;
    apply (return (pack (Tv_Var h))))

private let evolve (a:Type) : Pure (relation (rstate a))
    (requires (True)) (ensures (fun r -> preorder_rel r)) =
  multi_preorder (rstate a) (evolve_broken a);
  multi (rstate a) (evolve_broken a)

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

private let rec stable_readable_pred_aux (a:Type) (s1 s2 : rstate a)
    (h:multi (rstate a) (evolve_broken a) s1 s2) :
    Lemma (requires (readable_pred s1))
          (ensures (readable_pred s2)) (decreases h) =
  match h with
  | Multi_step #_ #_ x y hxy -> ()
  | Multi_refl x -> ()
  | Multi_trans _ s12 _ h1 h2 -> stable_readable_pred_aux a s1 s12 h1;
                                 stable_readable_pred_aux a s12 s2 h2

// private let stable_readable_pred_aux' (a:Type) (s1 s2 : rstate a)
//     (h:evolve a s1 s2) :
//     Lemma (requires (readable_pred s1)) (ensures (readable_pred s2)) =
//   stable_readable_pred_aux a s1 s2 h
// Expected a term of type 'Type'; got InitFreezeRef.evolve a s1 s2 : uu___2526082:InitFreezeRef.rstate a -> uu___2526083:InitFreezeRef.rstate a -> Prims.Tot Type0

// private let stable_readable_pred_aux' (a:Type) (s1 s2 : rstate a)
//     (h:evolve a s1 s2) :
//     Lemma (requires (readable_pred s1)) (ensures (readable_pred s2)) =
//   let t : (rstate a -> rstate a -> Type0) = multi (rstate a) (evolve_broken a) in
//   let h : (t s1 s2) = h in
//   match h with
//   | Multi_step  #_ #_  x y hxy -> admit()
//   | Multi_refl  #_ #_  x -> admit()
//   | Multi_trans #_ #_  x y z hxy hyz -> admit()

(* this works, but still can't call with evolve a s1 s2 *)
private let stable_readable_pred_aux' (a:Type) (s1 s2 : rstate a)
    (h:((evolve a <: relation (rstate a)) s1 s2)) :
    Lemma (requires (readable_pred s1)) (ensures (readable_pred s2)) =
  stable_readable_pred_aux a s1 s2 h

// private let stable_readable_pred_aux'' (a:Type) (s1 s2 : rstate a)
//     (h:evolve a s1 s2) :
//     Lemma (requires (readable_pred s1)) (ensures (readable_pred s2)) =
//   stable_readable_pred_aux' a s1 s2 h
// Expected a term of type 'Type'; got InitFreezeRef.evolve a s1 s2 : uu___2633743:InitFreezeRef.rstate a -> uu___2633744:InitFreezeRef.rstate a -> Prims.Tot Type0

let unrefine (p:preorder 'a) : 'a -> 'a -> Type0 = p
private let stable_readable_pred_aux'' (a:Type) (s1 s2 : rstate a)
    (h : unrefine (evolve a) s1 s2) :
    Lemma (requires (readable_pred s1)) (ensures (readable_pred s2)) =
  stable_readable_pred_aux a s1 s2 h

private let stable_readable_pred (a:Type)
    : Lemma (ensures (stable readable_pred) (evolve a)) = admit()
// user tactic failed: intro: unification failed
//   assert_by_tactic (ensures (stable readable_pred) (evolve a)) (
//     norm [delta];;
//     dump "before failure";;
//     x <-- forall_intro;
//     y <-- forall_intro;
//     h <-- implies_intro;
//     and_elim (pack (Tv_Var h));;
//     h1 <-- implies_intro;
//     h2 <-- implies_intro;
//     mapply (quote stable_readable_pred_aux);;
//     idtac
//   )

(* Clients can to play with readable predicate *)
abstract let readable (#a:Type0) (r:eref a) :Type0
  = stable_readable_pred a; token r readable_pred

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

private let stable_frozen_at_pred (a:Type) (x:a)
    : Lemma (ensures (stable (frozen_at_pred x)) (evolve a)) = admit()

(* frozen_at_pred is stable *)
abstract let frozen_at (#a:Type0) (r:eref a) (x:a) :Type0
  = stable_frozen_at_pred a x; token r (frozen_at_pred x)

(* fun begins *)

abstract let alloc (a:Type0)
  :ST (eref a) (requires (fun _       -> True))
               (ensures  (fun h0 r h1 ->
	                  modifies !{} h0 h1 /\  //existing refs are unmodified
			  fresh r h0 h1      /\  //returned eref's addr is different from all existing refs
			  r `writable_in` h1 /\  //the returned eref is writatble
			  sel h1 r == None))    //sel returns None
  = admit ()

(*
 * Note: Using a mix of monotonic and stateful reasoning
 *)
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
