module RefinedStack

val stack : Type0  (* type of stacks *)

val is_empty : stack -> GTot bool
val empty : s:stack{is_empty s}

val push : int -> stack -> s:stack{~(is_empty s)}
val pop : s:stack{~(is_empty s)} -> stack           
val top : s:stack{~(is_empty s)} -> int

val lemma_push_top : s:stack -> i:int -> 
  Lemma (top (push i s) = i) 
  [SMTPat (top (push i s))]

val lemma_push_pop : s:stack -> i:int -> 
  Lemma (pop (push i s) == s) 
  [SMTPat (pop (push i s))]

val lemma_top_pop_push : s:stack{~(is_empty s)} -> 
  Lemma (push (top s) (pop s) == s)
  [SMTPat (push (top s) (pop s))]
