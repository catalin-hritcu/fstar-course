module BufferAlloc

open LowStar.BufferOps
open FStar.HyperStack.ST
open FStar.UInt64

let f (): Stack UInt64.t (requires (fun _ -> True))
                         (ensures  (fun _ _ _ -> True))
  = push_frame ();
    let b = LowStar.Buffer.alloca 1UL 64ul in
    assert (b.(42ul) = 1UL);
    b.(42ul) <- b.(42ul) +^ 42UL;
    let r = b.(42ul) in
    pop_frame ();
    assert (r = 43UL);
    r
