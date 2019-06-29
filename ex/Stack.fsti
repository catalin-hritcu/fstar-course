module Stack

// BEGIN: stack_types
val stack : Type0  (* type of stacks *)

val empty : stack
val is_empty : stack -> GTot bool

val push : int -> stack -> stack
val pop : stack -> option stack
val top : stack -> option int
// END: stack_types

// BEGIN: stack_lemmas
val lemma_empty_is_empty : unit -> Lemma (is_empty (empty))

val lemma_push_is_empty : s:stack -> i:int -> 
                                            Lemma (~(is_empty (push i s))) 

val lemma_is_empty_top_some : s:stack{~(is_empty s)} -> 
                                                     Lemma (Some? (top s)) 

val lemma_is_empty_pop_some : s:stack{~(is_empty s)} -> 
                                                     Lemma (Some? (pop s)) 


(* Hint1: You will need to provide some more lemmas about pop and top *)

(* Hint2: You will need to annotate some lemmas with [SMTPat (...)]s *)

// END: stack_lemmas
