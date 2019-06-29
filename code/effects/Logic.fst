module Logic

open FStar.Tactics

assume val phi : Type0
assume val psi : Type0
assume val xi  : Type0

let tau () : Tac unit
  = let hyp_phi_xi = implies_intro () in
  
    right ();

    dump "proofstate 1";
    
    and_elim (binder_to_term hyp_phi_xi);
    
    dump "proofstate 2";
    
    let hyp_phi = implies_intro () in
    let hyp_xi = implies_intro () in 

    dump "proofstate 3";
    
    apply (`FStar.Squash.return_squash);
    
    dump "proofstate 4";
    
    exact (binder_to_term hyp_phi)
    

let _ = 
  assert_by_tactic (phi /\ xi ==> psi \/ phi) tau
