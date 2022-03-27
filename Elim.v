From Coq Require Import Nat.

Inductive even: nat -> Prop :=
  | evenO : even  O 
  | evenS : forall n, odd n -> even (S n)
  with
    odd  : nat -> Prop :=
    | oddS : forall n, even n -> odd (S n).

Theorem even_plus_four : forall n:nat, even n -> even (4 + n).
Proof.
 intros n H.
 elim H.
  - simpl. repeat constructor.
  - simpl. repeat constructor. assumption.
Qed. 
