module RefinedStack

abstract let stack = list int

abstract let is_empty (s : stack) : GTot bool = Nil? s

abstract let empty : s:stack{is_empty s} = []

abstract let push (i : int) (s0:stack) : s1:stack{~(is_empty s1)} = i :: s0
abstract let pop (s0:stack{~(is_empty s0)}) : stack = Cons?.tl s0
abstract let top (s0:stack{~(is_empty s0)}) : int = Cons?.hd s0

let lemma_push_top (s:stack) (i:int) : Lemma (top (push i s) = i) 
                                         [SMTPat (top (push i s))] = ()

let lemma_push_pop (s:stack) (i:int) : Lemma (pop (push i s) == s) 
                                         [SMTPat (pop (push i s))] = ()

let lemma_top_pop_push (s:stack{~(is_empty s)}) :
                                 Lemma (push (top s) (pop s) == s)
                                   [SMTPat (push (top s) (pop s))] = ()
