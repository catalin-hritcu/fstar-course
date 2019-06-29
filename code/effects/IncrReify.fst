module IncrReify

(**********************************************************
 *                                                        *
 * Dijkstra Monads for Free : Simple int-valued state     *
 *                                                        *
 **********************************************************)

let state = int

let st (a:Type) = state -> M (a * state)

let return_st (a:Type) (x:a) : st a 
  = fun s0 -> (x,s0)

let bind_st (a:Type) (b:Type) (f:st a) (g:a -> st b) : st b
  = fun s0 -> let (x,s) = f s0 in 
              g x s

let get () : st state 
  = fun s0 -> (s0,s0)

let put (x:state) : st unit 
  = fun s0 -> ((), x)

total reifiable reflectable new_effect {
  STATE : a:Type -> Effect
  with repr     = st
     ; bind     = bind_st
     ; return   = return_st
     ; get      = get
     ; put      = put
}

#reset-options

effect St (a:Type) = STATE a (fun _ p -> forall x s1 . p (x,s1))

(**********************************************************
 *                                                        *
 * Proof of correctness of incr using reification         *
 *                                                        *
 **********************************************************)

let incr () : St unit = STATE?.put (STATE?.get() + 1)

let incr' () : St unit = STATE?.put (STATE?.reflect (fun s0 -> (s0,s0)) + 1)
  
let lemma_incrs (s0:state)
  : Lemma (let (_,s1 ) = reify (incr  ()) s0 in 
           let (_,s1') = reify (incr' ()) s0 in 
           s1  = s0 + 1 /\
           s1' = s0 + 1)
= ()
