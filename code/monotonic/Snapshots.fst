module Snapshots

open FStar.Preorder
open FStar.Heap
open FStar.ST
open FStar.MRef

noeq type sval (a:Type0) = 
 | Ok  : current:a -> sval a 
 | Tmp : snapshot:a -> current:a -> sval a 

let srel (#a:Type0) (rel:preorder a) (s0 s1:sval a) =
  match s0 , s1 with
  | Ok  x0   , Ok  x1 
  | Ok  x0   , Tmp x1 _
  | Tmp x0 _ , Ok  x1
  | Tmp x0 _ , Tmp x1 _ -> rel x0 x1

let sref (a:Type0) (rel:preorder a) = mref (sval a) (srel rel)

let lift_predicate (#a:Type0) (p:predicate a) (s:sval a) = 
  match s with 
  | Ok  x   -> p x
  | Tmp x _ -> p x

val lift_stability : #a:Type0
                  -> #rel:preorder a
                  -> p:predicate a{stable p rel}
		  -> s0:sval a
		  -> s1:sval a
		  -> Lemma (requires (lift_predicate p s0 /\ srel rel s0 s1))
		           (ensures  (lift_predicate p s1))
let lift_stability #a #rel p s0 s1 = ()

let salloc (#a:Type0) (#rel:preorder a) (init:a)
  : ST (sref a rel) (requires (fun _       -> True))
                    (ensures  (fun h0 r h1 -> fresh r h0 h1 /\ 
                                              modifies !{} h0 h1 /\ 
                                              h1 `contains` r /\
                                              sel h1 r == Ok init))
  = alloc #(sval a) #(srel rel) (Ok init)

let sread (#a:Type0) (#rel:preorder a) (r:sref a rel) 
  : ST a (requires (fun _       -> True))
         (ensures  (fun h0 x h1 -> h0 == h1 /\ (match sel h1 r with 
                                                | Ok  y
                                                | Tmp _ y -> x == y)))
 = let x = !r in 
   match x with 
   | Ok    y
   | Tmp _ y -> y

let swrite (#a:Type0) (#rel:preorder a) (r:sref a rel) (v:a)
  : ST unit (requires (fun h0      -> match sel h0 r with
                                      | Ok  x 
                                      | Tmp x _ -> rel x v))
            (ensures  (fun h0 _ h1 -> modifies !{r} h0 h1 /\ 
                                      (match sel h0 r with 
                                       | Ok    _ -> sel h1 r == Ok v
                                       | Tmp x _ -> sel h1 r == Tmp x v)))
  = let x = !r in
    match x with 
    | Ok y    -> r := Ok v
    | Tmp y _ -> r := Tmp y v

let stoken (#a:Type0) (#rel:preorder a) (r:sref a rel) (p:(a -> Type){stable p rel})
  = token #(sval a) #(srel rel) r (lift_predicate p)

let switness (#a:Type0) (#rel:preorder a) (r:sref a rel) (p:(a -> Type){stable p rel})
  : ST unit (requires (fun h0      -> Ok? (sel h0 r) /\ (let Ok x = sel h0 r in p x)))
            (ensures  (fun h0 _ h1 -> h0 == h1 /\ stoken r p))
  = witness_token r (lift_predicate p)

let srecall (#a:Type0) (#rel:preorder a) (r:sref a rel) (p:(a -> Type){stable p rel})
  : ST unit (requires (fun h0      -> Ok? (sel h0 r) /\ stoken r p))
            (ensures  (fun h0 _ h1 -> h0 == h1 /\ Ok? (sel h1 r) /\ (let Ok x = sel h0 r in p x)))
  = recall_token r (lift_predicate p)

let escape (#a:Type0) (#rel:preorder a) (r:sref a rel) 
  : ST unit (requires (fun h0      -> Ok? (sel h0 r)))
            (ensures  (fun h0 _ h1 -> modifies !{r} h0 h1 /\ 
                                      Ok? (sel h0 r) /\ 
                                      (let Ok x = sel h0 r in sel h1 r == Tmp x x)))
  = let Ok x = !r in 
    r := Tmp x x

let return (#a:Type0) (#rel:preorder a) (r:sref a rel)
  : ST unit (requires (fun h0      -> Tmp? (sel h0 r) /\ (let Tmp x y = sel h0 r in rel x y)))
            (ensures  (fun h0 _ h1 -> modifies !{r} h0 h1 /\
                                      Tmp? (sel h0 r) /\
                                      (let Tmp _ x = sel h0 r in sel h1 r == Ok x)))
  = let Tmp _ x = !r in 
    r := Ok x
