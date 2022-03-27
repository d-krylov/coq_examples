Theorem rewrite_example_1: forall (a b c d : nat),
  a = b + c -> b = c + d -> d = 1 -> c = 2 -> a = 5.
Proof.
  intros a b c d H0 H1 H2 H3.
  rewrite H0.
  rewrite H1.
  rewrite H2.
  rewrite H3.
  reflexivity.
Qed.



