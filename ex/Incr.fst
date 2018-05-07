module Incr

(* Quiz: can you find other types for incr? *)

val incr : x:int -> Tot (y:int{x < y})
let incr x = x + 1
