module RefinedStackLength

  open FStar.List.Tot

  abstract type stack = list int
  
  abstract val length : stack -> Tot nat
  let length s = List.Tot.length s

  abstract val empty : s:stack{length s = 0}
  let empty = []
  
  abstract val push : int -> s1:stack ->
    Tot (s2:stack{length s2 = length s1 + 1})
  let push x xs = Cons x xs

  abstract val pop : s1:stack{length s1 > 0} ->
    Tot (s2:stack{length s2 = length s1 - 1})
  let pop xs = Cons?.tl xs

  abstract val top : s:stack{length s > 0} -> Tot int
  let top = Cons?.hd
