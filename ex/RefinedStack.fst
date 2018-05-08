module RefinedStack

  abstract type stack = list int
  
  abstract val is_empty : stack -> Tot bool
  let is_empty s = Nil? s

  abstract val empty : s:stack{is_empty s}
  let empty = []
  
  abstract val push : int -> stack -> Tot (s:stack{~(is_empty s)})
  let push x xs = Cons x xs

  abstract val pop : s:stack{~(is_empty s)} -> Tot stack
  let pop s = Cons?.tl s
  
  abstract val top : s:stack{~(is_empty s)} -> Tot int
  let top s = Cons?.hd s

