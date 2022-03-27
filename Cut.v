Theorem cut_example: forall (P Q R T: Prop),
  P -> (P -> Q) -> (Q -> R) -> ((P -> R) -> T) -> T.
Proof.
  intros.
  cut (P -> R). intro H3.
  apply H2. apply H3.
  cut (P -> Q). intros. 
  apply H1. apply H0. apply H.
  apply H0.
Qed.