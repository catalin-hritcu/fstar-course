module RefinedStack

val stack : Type0  (* type of stacks *)

(* Exercise: modify and implement this interface of refined stacks; 
             pop and top must not return in the option type here    *)

(* Hint: compared to Stack.fsti and Stack.fst, you will need to 
         refine stack types below with the is_empty predicate   *)

val empty : stack
val is_empty : stack -> GTot bool

val push : int -> stack -> stack
val pop : stack -> stack           (* before the type was `option stack`*)
val top : stack -> int             (* before the type was `option int`  *)
