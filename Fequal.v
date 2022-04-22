Require Import Coq.Arith.Arith.

Lemma l1: forall m n : nat, 
  m * m = n * n -> m = n.
Proof.
  intros m n H. apply (f_equal Nat.sqrt) in H.
  rewrite Nat.sqrt_square in H. rewrite Nat.sqrt_square in H.
  apply H.
Qed.
