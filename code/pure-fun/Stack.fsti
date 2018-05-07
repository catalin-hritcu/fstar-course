module Stack

  val stack : Type0  (* type stack *)

  val empty : stack
  val push : int -> stack -> stack
  val is_empty : stack -> bool
  val pop : stack -> option stack
  val top : stack -> option int
