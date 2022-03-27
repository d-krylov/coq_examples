Theorem transitivity_example_1: forall (a b c : nat),
  a = b -> b = c -> a = c.
Proof.
  intros. transitivity b. 
  - apply H.
  - apply H0.
Qed. 
