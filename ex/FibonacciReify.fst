module FibonacciReify

(**********************************************************
 *                                                        *
 * Dijkstra Monads for Free : Simple int-valued state     *
 *                                                        *
 **********************************************************)

let state = int * int

let st (a:Type) = state -> M (a * state)

let return_st (a:Type) (x:a) : st a 
  = fun s0 -> (x,s0)

let bind_st (a:Type) (b:Type) (f:st a) (g:a -> st b) : st b
  = fun s0 -> let (x,s) = f s0 in 
              g x s

let get_left () : st int 
  = fun s0 -> (fst s0,s0)

let get_right () : st int 
  = fun s0 -> (snd s0,s0)

let put_left (x:int) : st unit 
  = fun s0 -> ((), (x,snd s0))

let put_right (x:int) : st unit 
  = fun s0 -> ((), (fst s0,x))

total reifiable reflectable new_effect {
  STATE : a:Type -> Effect
  with repr      = st
     ; bind      = bind_st
     ; return    = return_st
     ; get_left  = get_left
     ; get_right = get_right
     ; put_left  = put_left
     ; put_right = put_right
}

#reset-options

effect St (a:Type) = STATE a (fun _ p -> forall x s1 . p (x,s1))

(**********************************************************
 *                                                        *
 * Proof of stateful fibonacci using reification          *
 *                                                        *
 **********************************************************)

let rec fibonacci_tot (n:nat) : Tot nat 
  = if n <= 1 then 1 else fibonacci_tot (n - 1) + fibonacci_tot (n - 2)

(* Exercise1: give a definition of fibonacci using the St effect defined above *)

let rec fibonacci (i:pos) (n:nat{n >= i}) : St unit
= admit()

(* Exercise2: prove that fibonacci agrees with fibonacci_tot by using monadic reification *)

let lemma_fibonacci (i:pos) (n:nat{n >= i})
  : Lemma (True)
= admit()
