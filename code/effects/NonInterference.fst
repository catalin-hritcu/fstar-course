module NonInterference

(**********************************************************
 *                                                        *
 * Dijkstra Monads for Free : Simple int-valued state     *
 *                                                        *
 **********************************************************)

let state = int * int // (high * low) values

let st (a:Type) = state -> M (a * state)

let return_st (a:Type) (x:a) : st a 
  = fun s0 -> (x,s0)

let bind_st (a:Type) (b:Type) (f:st a) (g:a -> st b) : st b
  = fun s0 -> let (x,s) = f s0 in 
              g x s

let get_high () : st int 
  = fun s0 -> (fst s0,s0)

let get_low () : st int 
  = fun s0 -> (snd s0,s0)

let put_high (x:int) : st unit 
  = fun s0 -> ((), (x,snd s0))

let put_low (x:int) : st unit 
  = fun s0 -> ((), (fst s0,x))

total reifiable reflectable new_effect {
  STATE : a:Type -> Effect
  with repr     = st
     ; bind     = bind_st
     ; return   = return_st
     ; get_low  = get_low
     ; get_high = get_high
     ; put_low  = put_low
     ; put_high = put_high
}

effect St (a:Type) = STATE a (fun _ p -> forall x s1 . p (x,s1))

(**********************************************************
 *                                                        *
 * Proof of simple non-interference using reification     *
 *                                                        *
 **********************************************************)

let incr (n:int) : St unit 
  = STATE?.put_low (STATE?.get_low() + n)

let incr2 () : St unit 
  = if (STATE?.get_high() = 42) then (incr 2) 
                                else (incr 1; incr 1)

let non_interference ()
  : Lemma (forall h0 h1 n . let (_ , (h0' , n' )) = reify (incr2 ()) (h0,n) in 
                            let (_ , (h1' , n'')) = reify (incr2 ()) (h1,n) in
                            n' = n'')
  = ()
