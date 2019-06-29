module Incr

val incr : x:int -> Tot (y:int{x + 1 = y})
let incr x = x + 1
