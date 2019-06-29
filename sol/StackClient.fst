module StackClient

open Stack

let main() =

  let s0 = empty (* <: stack *) in
    
  lemma_empty_is_empty ();
  assert (is_empty s0);
    
  let s1 = push 3 s0 (* <: stack *) in
  assert (~(is_empty s1));
    
  let s2 = push 4 s1 (* <: stack *) in
  assert (~(is_empty s2));
    
  let i = top s2 (* <: option int *) in
  assert (Some?.v i = 4);
    
  let s3 = pop s2 (* <: option stack *) in
  assert (Some?.v s3 == s1)
