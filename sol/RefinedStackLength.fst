module RefinedStackLength

  open FStar.List.Tot

  abstract type stack = list int
  
  abstract let length (s:stack) : nat = List.Tot.length s

  let is_empty (s:stack) : bool = (length s = 0)

  abstract let empty : s:stack{length s = 0}  = []

  abstract let push (i:int) (s0:stack)
  : s1:stack{length s1 = length s0 + 1} = Cons i s0

  abstract let pop (s0:stack{length s0 > 0})
  : s1:stack{length s1 = length s0 - 1} = Cons?.tl s0

  abstract let top (s0:stack{length s0 > 0}) : int = Cons?.hd s0
