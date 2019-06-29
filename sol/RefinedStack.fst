module RefinedStack

let stack = list int

let is_empty s = Nil? s

let empty = []

let push i s = i :: s

let pop (i::s) = s

let top (i::s) = i

let lemma_push_top s i = ()

let lemma_push_pop s i = ()

let lemma_top_pop_push s = ()
