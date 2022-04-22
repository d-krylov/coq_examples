From Coq Require Import Arith.

Fixpoint sum_simple (f : nat -> nat) (n : nat) : nat :=
  match n with
  | 0 => f 0
  | S m => f n + sum_simple f m
end.

Fixpoint sum_aux (a : nat) (f : nat -> nat) (n : nat) : nat :=
  match n with
  | 0 => f 0 + a
  | S m => sum_aux (f n + a) f m
end.

Definition sum_tail := sum_aux 0.

Lemma sum_aux_rec: forall a f n,
  sum_aux a f n = a + sum_aux 0 f n.
Proof.
  intros. generalize dependent a.
  induction n.
  - intros. simpl. rewrite Nat.add_0_r. rewrite Nat.add_comm. reflexivity.
  - intros. simpl. rewrite IHn. symmetry. rewrite IHn.
    rewrite Nat.add_0_r. rewrite Nat.add_assoc. rewrite Nat.add_comm with (a) (f (S n)).
    reflexivity.
Qed.