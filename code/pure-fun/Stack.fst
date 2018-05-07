module Stack

  let stack = list int
  let empty = []
  let push x xs = x :: xs
  let is_empty xs = match xs with
                    | [] -> true
                    | x::xs' -> false
  let pop xs = match xs with
               | [] -> None
               | x::xs' -> Some xs'
  let top xs = match xs with
               | [] -> None
               | x::xs' -> Some x
