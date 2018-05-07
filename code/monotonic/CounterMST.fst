module CounterMST

open FStar.Heap
open FStar.ST
open FStar.MRef

(* Monotonic counters *)

let increases (n m:int) : Type0 = n <= m
let counter = mref int (fun n m -> increases n m)

val create : i:int -> ST counter  (requires (fun _ -> True)) (ensures (fun h0 c h1 -> fresh c h0 h1 /\ modifies !{} h0 h1 /\ sel h1 c = i))
val read   : c:counter -> ST int  (requires (fun _ -> True)) (ensures (fun h0 i h1 -> h0 == h1 /\ sel h1 c = i))
val incr   : c:counter -> ST unit (requires (fun _ -> True)) (ensures (fun h0 _ h1 -> modifies !{c} h0 h1 /\ sel h1 c = sel h0 c + 1))

let create i = FStar.ST.alloc i
let read   c = !c
let incr   c = c := (!c + 1)


(* Example *)

let example (complex_procedure:counter -> St unit) : St unit = 
  let c = create 0 in 
  incr c;

  let i = read c in assert (i > 0);

  witness_token c (fun i -> i > 0);
  assert (token c (fun i -> i > 0));

  complex_procedure c;

  assert (token c (fun i -> i > 0));
  recall_token c (fun i -> i > 0);
  
  let j = read c in assert (j > 0)
