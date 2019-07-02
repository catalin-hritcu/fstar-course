module SwapIntRefsST

open FStar.Ref

// BEGIN: swap_add_sub
val swap_add_sub : r1:ref int -> r2:ref int ->
  ST unit (requires (fun _ -> addr_of r1 <> addr_of r2 ))
          (ensures  (fun h0 _ h3 -> modifies !{r1,r2} h0 h3 /\
                                    sel h3 r1 == sel h0 r2 /\
                                    sel h3 r2 == sel h0 r1))
let swap_add_sub r1 r2 =
  r1 := !r1 + !r2; (* Know (P1) : exists h1. modifies !{r1} h0 h1
                               /\ sel h1 r1 = (sel h0 r1) + (sel h0 r2) *)
  r2 := !r1 - !r2; (* Know (P2) : exists h2. modifies !{r2} h1 h2
                               /\ sel h2 r2 = (sel h1 r1) - (sel h1 r2) *)
  r1 := !r1 - !r2  (* Know (P3) :            modifies !{r1} h2 h3
                               /\ sel h3 r1 = (sel h2 r1) - (sel h2 r2) *)

(* F* computed pre for this code is `fun _ -> True` *)
(* F* computed post for this code is `fun h0 _ h3 -> (P1) /\ (P2) /\ (P3)` *)
(* to show (1) : user-provided pre ==> F* computed pre (=True). Trivial. *)
(* - by additivity of modifies we get `modifies !{r1,r2} h0 h3` *)
(* to show (2): F* computed post /\ user-provided pre ==> user-provided post *)
(* - for instance, to show `sel h3 r1 == sel h0 r2` we reason as follows:
        sel h3 r1 = (sel h2 r1) - (sel h2 r2)                    -- by (P3)
                  = (sel h2 r1) - ((sel h1 r1) - (sel h1 r2))    -- by (P2)
                  = sel h1 r2     -- by arithmetic and absence of underflows
                  = sel h0 r2     -- by `modifies !{r1} h0 h1`
                                     and `addr_of r1 <> addr_of r2`    *)
// END: swap_add_sub

open FStar.IO

let main =
  let r1 = alloc 1 in
  let r2 = alloc 2 in
  swap_add_sub r1 r2;
  print_string ("r1=" ^ string_of_int !r1 ^ "; " ^
                "r2=" ^ string_of_int !r2 ^ "\n")
