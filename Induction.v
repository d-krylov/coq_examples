Theorem induction_example_plus_n_Sm : forall n m: nat,
  S (n + m) = n + (S m).
Proof.
  intros n m. induction n as [ | n IHn ].
  - simpl. reflexivity.
  - simpl. rewrite IHn. reflexivity.
Qed.

Theorem induction_example_add_0_r : forall n: nat, 
  n + 0 = n.
Proof.
  intros n. induction n as [ | n IHn ].
  - reflexivity.
  - simpl. rewrite -> IHn. reflexivity.
Qed.

Theorem add_comm : forall n m : nat,
  n + m = m + n.
Proof.
  intros n m. induction m as [ | m IHm ].
  - simpl. rewrite induction_example_add_0_r. reflexivity.
  - simpl. rewrite <- induction_example_plus_n_Sm. rewrite IHm. reflexivity.
Qed. 


Lemma induction_example_le_trans: forall m n o,
  m <= n -> n <= o -> m <= o.
Proof.
  intros m n o H1 H2. induction H2 as [ | no E IHno ].
  - apply H1. 
  - apply le_S. apply IHno.
Qed.