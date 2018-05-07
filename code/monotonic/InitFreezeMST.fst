module InitFreezeMST

open FStar.Preorder
open FStar.Heap
open FStar.ST
open FStar.MRef

type rstate (a:Type) =
  | Empty   : rstate a
  | Mutable : v:a -> rstate a
  | Frozen  : v:a -> rstate a

let evolve_broken' (a:Type) = fun (r1 r2:rstate a) ->
  match r1 , r2 with
  | Empty      , Mutable _
  | Mutable _  , Mutable _ -> True
  | Mutable v1 , Frozen v2 -> v1 == v2
  | _          , _         -> False
(* let evolve_broken (a:Type) : Tot (preorder (rstate a)) = evolve_broken' a
   -- fails as it should *)

let evolve' (a:Type) = fun (r1 r2:rstate a) ->
  match r1 , r2 with
  | Empty     , _
  | Mutable _ , Mutable _
  | Mutable _ , Frozen _  -> True 
  | Frozen v1 , Frozen v2 -> v1 == v2
  | _         , _         -> False
let evolve (a:Type) : Tot (preorder (rstate a)) = evolve' a

let eref (a:Type) : Type = mref (rstate a) (evolve a)

let alloc (a:Type) = 
  alloc #_ #(evolve a) Empty
  
let read (#a:Type) (r:eref a) = 
  match (!r) with 
  | Mutable v 
  | Frozen  v -> v

let write (#a:Type) (r:eref a) (v:a) = 
  r := Mutable v

let freeze (#a:Type) (r:eref a) = 
  r := Frozen (Mutable?.v !r)

(* TODO: for some reason needed to mark these as private, otherwise
./InitFreezeMST.fst(35,41-35,43): (Error) Interface of InitFreezeMST violates its abstraction (add a 'private' qualifier to 'write'?): Too many arguments to function of type a:Type0 -> Prims.Tot (Preorder.preorder (InitFreezeMST.rstate a)); got 3 arguments (see also ./STx.fst(95,25-95,34)) *)

assume val complex_procedure (r:eref int) : St unit

let main() : St unit =
  let r = alloc int in
  (* ignore (read r) -- fails like it should *)
  write r 42;
  ignore (read r);                                    (* needs --use_two_phase_tc true *)
  write r 0;
  witness_token r (fun rs -> ~(Empty? rs));
  freeze r;
  (* write r 7; -- fails like it should *)
  ignore (read r);
  witness_token r (fun rs -> rs == Frozen 0);
  complex_procedure r;
  (* ignore (read r); -- fails like it should *)
  recall_token r (fun rs -> ~(Empty? rs));
  let x = read r in
  (* assert (x == 0) -- fails like it should *)
  recall_token r (fun rs -> rs == Frozen 0);
  assert (x == 0)
