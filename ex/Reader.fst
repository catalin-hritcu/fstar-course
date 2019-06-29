module Reader

open SumReify

(**************************************************************
 *                                                            *
 * Dijkstra Monads for Free : Simple int-valued reader effect *
 *                                                            *
 **************************************************************)

(* Exercise1: define the READER effect (see STATE in SumReify for inspiration); 

              as a hint, the underlying representation rd of the reader monad is provided;

              make sure your READER effect supports the standard get action
              *)

let state = int

let rd (a:Type) = state -> M a

(* Exercise2: state that your READER effect is a sub-effect of the STATE effect in SumReify *)


(**********************************************************
 *                                                        *
 * Showing that the reader and state are correct          *
 *                                                        *
 **********************************************************)

(* Exercise3: uncomment the code below to test whether your READER effect is correct wrt to STATE *)

(*
let incr () : St unit = STATE?.put (READER?.get() + 1)

let incr' () : St unit = STATE?.put (READER?.reflect (fun s0 -> s0) + 1)
  
let lemma_incrs (s0:state)
  : Lemma (let (_,s1 ) = reify (incr  ()) s0 in 
           let (_,s1') = reify (incr' ()) s0 in 
           s1  = s0 + 1 /\
           s1' = s0 + 1)
= ()
*)
