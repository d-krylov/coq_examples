From Coq Require Import Arith.

Lemma mult_distr_S : forall n p : nat, n * p + p =  S n * p.
Proof. 
 simpl; auto with arith. 
Qed.

Lemma four_n : forall n:nat, 
  n + n + n + n = 4 * n.
Proof.
  intro n. pattern n at 1.
  rewrite <- mult_1_l.
  rewrite mult_distr_S. rewrite mult_distr_S. 
  now rewrite mult_distr_S. 
Qed. 

