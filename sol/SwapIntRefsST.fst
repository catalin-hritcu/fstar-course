module SwapIntRefsST

open FStar.Ref
open FStar.IO

// BEGIN: swap_add_sub
val swap_add_sub : r1:ref int -> r2:ref int ->
  ST unit (requires (fun _ -> addr_of r1 <> addr_of r2 ))
          (ensures  (fun h0 _ h1 -> modifies !{r1,r2} h0 h1 /\
                                    sel h1 r1 == sel h0 r2 /\
                                    sel h1 r2 == sel h0 r1))
let swap_add_sub r1 r2 =
  r1 := !r1 + !r2;
  (*Know (P1) : exists h1. modifies !{r1} h0 h1 /\ sel h1 r1 = (sel h0 r1) + (sel h0 r2) *)
  r2 := !r1 - !r2;
  (*Know (P2) : exists h2. modifies !{r2} h1 h2 /\ sel h2 r2 = (sel h1 r1) - (sel h1 r2) *)
  r1 := !r1 - !r2
  (*Know (P3) :            modifies !{r1} h2 h3 /\ sel h3 r1 = (sel h2 r1) - (sel h2 r2) *)

  (* F* computed precondition for this code is fun _ -> True  *)
  (* F* computed postcondition for this code is (more or less)
     fun h0 _ h3 -> exists h1 h2. (P1).formula /\ (P2).formula /\ (P3).formula , where .formula removes exists*)
  (*to show : user-provided precondition ==> F* computed precondtion . Easy*)
  (*to show : F* computed postcondition ==> user-provided postcondition (rename h1 by h3 for better readability)*)
       (* - by hypothesis we change nothing but r1 and r2 so the following holds :  modifies !{r1,r2} h0 h3*)
       (* - Besides thanks to the hypothesis we can directly comupute (sel h3 ri) and it is what we want *)
  
// END: swap_add_sub

let main =
  let r1 = alloc 1 in
  let r2 = alloc 2 in
  swap_add_sub r1 r2;
  print_string ("r1=" ^ string_of_int !r1 ^ "; " ^
                "r2=" ^ string_of_int !r2 ^ "\n")
