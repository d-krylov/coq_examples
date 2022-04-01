Lemma intros_example_1: forall (x y z : nat),
  x = y -> y = z -> x = z.
Proof.
  intros x y z H. intros ->. apply H.
Qed.

Lemma intros_example_2: forall A B C : Prop, 
  A \/ B /\ C -> (A -> C) -> C.
Proof.
  intros * [a | (b , c) ] f.
  - apply f. apply a.
  - apply c.
Qed.

Lemma intros_example_3: forall (x y : nat),
  S x = S y -> x = y.
Proof.
  intros x y. intros [= H]. apply H.
Qed.