module SwapIntRefsST

open FStar.Ref
open FStar.IO

// BEGIN: swap_add_sub
val swap_add_sub : r1:ref int -> r2:ref int -> ST unit
    (requires (fun h0 -> addr_of r1 <> addr_of r2 ))
    (ensures (fun h0 _ h1 -> modifies !{r1,r2} h0 h1 /\
                            sel h1 r1 == sel h0 r2 /\ sel h1 r2 == sel h0 r1))
let swap_add_sub r1 r2 =
  r1 := !r1 + !r2;
  r2 := !r1 - !r2;
  r1 := !r1 - !r2
// END: swap_add_sub

let main =
  let r1 = alloc 1 in
  let r2 = alloc 2 in
  swap_add_sub r1 r2;
  print_string ("r1=" ^ string_of_int !r1 ^ "; " ^
                "r2=" ^ string_of_int !r2 ^ "\n")
