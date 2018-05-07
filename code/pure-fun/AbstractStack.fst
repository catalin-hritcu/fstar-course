module AbstractStack

  abstract type stack = list int
  abstract let is_empty (s:stack) : Tot bool = Nil? s
  abstract let empty : s:stack{is_empty s} = []
  abstract let push (x:int) (xs:stack) : Tot (s:stack{~(is_empty s)}) = Cons x xs
  abstract let pop : s:stack{~(is_empty s)} -> Tot stack = Cons?.tl
  abstract let top : s:stack{~(is_empty s)} -> Tot int = Cons?.hd

  let top_push (i:int) (s:stack) :
    Lemma (top (push i s) = i) [SMTPat (top (push i s))] = ()

  let pop_push (i:int) (s:stack) :
    Lemma (pop (push i s) = s) [SMTPat (pop (push i s))] = ()

  let push_top_pop (s:stack{~(is_empty s)}) :
    Lemma (ensures (s = push (top s) (pop s))) = ()
