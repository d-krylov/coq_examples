From Coq Require Import Bool.

Theorem bool_fn_applied_thrice : forall (f : bool -> bool) (b : bool),
  f (f (f b)) = f b.
Proof.
  intros f b. destruct b eqn:B.
  - destruct (f true) eqn:Q.
    * rewrite Q. apply Q.
    * destruct (f false) eqn:R.
      + apply Q.
      + apply R.
  - destruct (f false) eqn:Q.
    * destruct (f true) eqn:R.
      + apply R.
      + apply Q.
    * rewrite Q. apply Q.
Qed. 

Theorem andb_eq_orb : forall (b c : bool),
  b && c = b || c -> b = c.
Proof.
  intros b. case b.
  - simpl. intros c H. rewrite H. reflexivity.
  - simpl. intros c H. rewrite H. reflexivity.
Qed.


Lemma lemma_2:
  forall n m : nat, n = 0 \/ m = 0 -> n * m = 0.
Proof.
  intros n m H.
  destruct H as [ Ha | Hb ].
  - rewrite Ha. simpl. reflexivity.
  - rewrite Hb. rewrite <- mult_n_O. reflexivity.
Qed.

Lemma lemma_1 : forall P Q : Prop,
  P /\ Q -> Q.
Proof.
  intros P Q H.
  destruct H as (HA & HB).
  apply HB.
Qed.