module Reader

open SumReify

(**************************************************************
 *                                                            *
 * Dijkstra Monads for Free : Simple int-valued reader effect *
 *                                                            *
 **************************************************************)

let state = int

let rd (a:Type) = state -> M a

let return_st (a:Type) (x:a) : rd a 
  = fun s0 -> x

let bind_st (a:Type) (b:Type) (f:rd a) (g:a -> rd b) : rd b
  = fun s0 -> let x = f s0 in 
              g x s0

let get () : rd state 
  = fun s0 -> s0

total reifiable reflectable new_effect {
  READER : a:Type -> Effect
  with repr     = rd
     ; bind     = bind_st
     ; return   = return_st
     ; get      = get
}

#reset-options

effect Rd (a:Type) = READER a (fun _ p -> forall x . p x)

let lift_rd_state (a:Type) (e:rd a) : st a
  = fun s0 -> let x = e s0 in (x,s0)

sub_effect READER ~> STATE {
  lift = lift_rd_state
}

(**********************************************************
 *                                                        *
 * Showing that the reader and state are correct          *
 *                                                        *
 **********************************************************)

let incr () : St unit = STATE?.put (READER?.get() + 1)

let incr' () : St unit = STATE?.put (READER?.reflect (fun s0 -> s0) + 1)
  
let lemma_incrs (s0:state)
  : Lemma (let (_,s1 ) = reify (incr  ()) s0 in 
           let (_,s1') = reify (incr' ()) s0 in 
           s1  = s0 + 1 /\
           s1' = s0 + 1)
= ()
