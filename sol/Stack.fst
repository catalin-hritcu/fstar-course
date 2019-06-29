module Stack

  let stack = list int
  
  let empty = []
  let is_empty xs = match xs with
                    | [] -> true
                    | x::xs' -> false
  let push x xs = x :: xs
  let pop xs = match xs with
               | [] -> None
               | x::xs' -> Some xs'
  let top xs = match xs with
               | [] -> None
               | x::xs' -> Some x

  let lemma_empty_is_empty () = ()

  let lemma_push_is_empty s i = ()

  let lemma_is_empty_top_some s = ()

  let lemma_is_empty_pop_some s = ()

  let lemma_push_top s i = ()

  let lemma_push_pop s i = ()

  let lemma_top_pop_push s = ()
