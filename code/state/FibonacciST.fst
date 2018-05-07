module FibonacciST

open FStar.Ref

// BEGIN: fibonacci
let rec fibonacci (n:nat) : Tot nat =
  if n <= 1 then 1 else fibonacci (n-1) + fibonacci (n-2)
// END: fibonacci

// BEGIN: fibonacci_stprime
let rec fibonacci_st' (i:pos) (n:nat{n >= i}) (r1 r2:ref nat) : ST unit
          (requires (fun h0 -> addr_of r1 <> addr_of r2 /\
                               sel h0 r1 = fibonacci (i-1) /\
                               sel h0 r2 = fibonacci i ))
          (ensures (fun h0 a h1 -> sel h1 r1 = fibonacci (n-1) /\
                                   sel h1 r2 = fibonacci n /\
                                   modifies !{r1,r2} h0 h1)) =
  if i < n then
    (let temp = !r2 in
     r2 := !r1 + !r2;    (* fibonacci (i+1) = fibonacci i + fibonacci (i-1) *)
     r1 := temp;                             (* fibonacci i we already have *)
     fibonacci_st' (i+1) n r1 r2 (* tail-recursive call to compute the rest *))
// END: fibonacci_stprime

// BEGIN: fibonacci_st
let fibonacci_st (n:nat) : ST nat (requires (fun h0 -> True))
      (ensures (fun h0 x h1 -> x = fibonacci n /\ modifies !{} h0 h1)) =
  if n <= 1 then 1
  else (let r1 = alloc 1 in
        let r2 = alloc 1 in
        fibonacci_st' 1 n r1 r2;
        !r2)
// END: fibonacci_st
