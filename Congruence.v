Require Import Arith.
Require Import Coq.Classes.Morphisms.

Lemma congruence x y: 
  S x = S y -> x = y.
Proof.
  intros. congruence.
Qed.

Definition set := Set -> bool.

Definition set_eq (A B : set) := forall x, A x = B x.

Lemma set_eq_refl : Reflexive set_eq.
Proof.
  compute. congruence.
Qed.


 
