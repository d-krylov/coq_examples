Inductive even : nat -> Prop :=
  | even_0 : even 0
  | even_SS (n : nat) (H : even n) : even (S (S n)).

Inductive less : nat -> nat -> Prop :=
  | less_n (n : nat) : less n n
  | less_S (n m : nat) (H : less n m) : less n (S m).

Definition lt (n m:nat) := less (S n) m.

Inductive plusR : nat -> nat -> nat -> Prop :=
  | Plus_0 : forall m, plusR 0 m m
  | Plus_S : forall n m r, plusR n m r -> plusR (S n) m (S r).

Print plusR.

Notation "n <= m" := (less n m).
Notation "m < n"  := (lt m n).

Theorem O_less_n : forall n : nat,
  0 <= n.
Proof.
  intros. induction n as [ | n IHn ].
  - apply less_n.
  - apply less_S. apply IHn.
Qed.

Lemma less_trans : forall m n o,
  m <= n -> n <= o -> m <= o.
Proof.
  intros m n o H1 H2. induction H2 as [ | ns no E IHno ].
  - apply H1. 
  - apply less_S. apply IHno. apply H1.
Qed.

Theorem plus_n_m: forall n m: nat,
  plusR n m (n + m).
Proof.
  intros. induction n.
  - rename m into s. apply Plus_0 with (m := s).
  - apply Plus_S. apply IHn.
Qed. 

Theorem plusR_plus : forall n m r: nat,
  plusR n m r -> r = n + m.
Proof.
  intros. induction H as [ | ns ms rs E IHplus ]. 
  - reflexivity.
  - simpl. rewrite IHplus. reflexivity.
Qed.