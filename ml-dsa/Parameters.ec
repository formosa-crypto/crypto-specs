require import AllCore IntDiv. 
op q : int = 8380417 axiomatized by qE.
axiom prime_q : prime q.
op d : int = 13.
op tau : int = 49.
op gamma1 : int = 2^19.
op gamma2 : int = (q - 1) %/ 32.
(* We have k x l matrices *)
op kvec : int = 6. 
op lvec : int = 5.
op Eta : int = 4.
op Beta : int = tau * Eta. 
lemma beta_val : Beta = 196 by auto.
op w_hint = 55.
