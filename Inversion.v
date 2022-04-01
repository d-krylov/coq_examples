From Coq Require Import List. Import ListNotations.
From Coq Require Import ZArith.

Inductive even : nat -> Prop :=
  | even_0 : even 0
  | even_SS (n : nat) (H : even n) : even (S (S n)).

Theorem plus_2_even_inv : forall n: nat, 
  even (S (S n)) -> even n.
Proof.
  intros n H. inversion H as [ | ns IHn Eq ]. apply IHn.
Qed.

Open Scope Z_scope.

Inductive sorted : list Z -> Prop :=
  | sorted0 : sorted nil
  | sorted1 : forall z : Z, sorted (z :: nil)
  | sorted2 :
      forall (z1 z2: Z) (l: list Z),
        z1 <= z2 ->
        sorted (z2 :: l) -> sorted (z1 :: z2 :: l).

Theorem sorted_inv: forall (z : Z) (l : list Z), 
  sorted (z :: l) -> sorted l.
Proof.
  intros.
  inversion H as [ | | z1 z2 L Cond Heq ].
  - apply sorted0.
  - apply Heq.
Qed.