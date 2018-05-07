module Incr

(* val incr : int -> int *)
(* val incr : x:int -> y:int{x < y} *)
(* val incr : x:int -> y:int{y = x + 1} *)
(* val incr : nat -> nat *)
(* val incr : x:int{x>3} -> y:int{y>4} *)
(* val incr : x:nat -> y:nat{(x % 2 == 0 ==> y % 2 == 1) /\ *)
(*                           (x % 2 == 1 ==> y % 2 == 0)} *)
let incr x = x + 1
