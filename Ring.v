Require Import Ring.
Require Import ZArith.
Require Import Init.Datatypes.

Open Scope Z_scope.

Definition G : Type := Z * Z.

Definition G0: G := (0, 0).
Definition G1: G := (1, 0).

Definition Gadd (g1 g2 : G) : G := (fst g1 + fst g2, snd g1 + snd g2).
Definition Gsub (g1 g2 : G) : G := (fst g1 - fst g2, snd g1 - snd g2).
Definition Gmul (g1 g2 : G) : G := (fst g1 * fst g2 - snd g1 * snd g2, fst g1 * snd g2 + snd g1 * fst g2).
Definition Gopp (g : G) : G := (- fst g, - snd g).

Lemma Gadd_0_l: forall (g: G),
  Gadd G0 g = g.
Proof.
  intros. destruct g. reflexivity.
Qed.

Lemma Gadd_comm: forall (g1 g2: G),
  Gadd g1 g2 = Gadd g2 g1.
Proof.
  intros. destruct g1. destruct g2. unfold Gadd. simpl.
  rewrite Zplus_comm. rewrite Zplus_comm with (z0) (z2).
  reflexivity.
Qed. 

Lemma Gadd_assoc: forall g1 g2 g3: G,
  Gadd g1 (Gadd g2 g3) = Gadd (Gadd g1 g2) g3.
Proof.
  intros. destruct g1. destruct g2. destruct g3.
  unfold Gadd. simpl. rewrite Zplus_assoc. 
  rewrite Zplus_assoc with (z0) (z2) (z4).
  reflexivity.
Qed. 

Lemma Gmul_1_l: forall g : G, 
  Gmul G1 g = g.
Proof.
  intros. unfold Gmul. unfold G1. destruct g. 
Admitted.

Lemma Gmul_comm: forall g1 g2 : G, 
  Gmul g1 g2 = Gmul g2 g1.
Proof.
  intros. unfold Gmul. destruct g1. destruct g2.
  simpl. rewrite Zmult_comm. 
  rewrite Zmult_comm with (z0) (z2).
  rewrite Zplus_comm with (z * z2) (z0 * z1).
  rewrite Zmult_comm with (z0) (z1).
  rewrite Zmult_comm with (z) (z2).
  reflexivity.
Qed.

Lemma Gmul_assoc: forall g1 g2 g3 : G, 
  ( Gmul g1 (Gmul g2 g3) ) = ( Gmul (Gmul g1 g2) g3 ).
Proof.
  Admitted.

Lemma Gdistr_l: forall g1 g2 g3: G, 
  Gmul (Gadd g1 g2) g3 = Gadd (Gmul g1 g3) (Gmul g2 g3).
Proof.
  Admitted.

Lemma Gopp_def : forall g : G,
  Gadd g (Gopp g) = G0.
Proof.
  intros. unfold Gadd. unfold Gopp. destruct g. 
  simpl. rewrite Z.add_opp_diag_r. rewrite Z.add_opp_diag_r.
  reflexivity.
Qed.

Lemma R_Ring_Theory : ring_theory G0 G1 Gadd Gmul Gsub Gopp eq.
Proof.
  constructor. 
  - apply Gadd_0_l.
  - apply Gadd_comm.
  - intros; rewrite Gadd_assoc; easy.
  - apply Gmul_1_l.
  - apply Gmul_comm.
  - intros; rewrite Gmul_assoc; easy.
  - apply Gdistr_l.
  - reflexivity.
  - apply Gopp_def.
Defined.
Add Ring RRing : R_Ring_Theory.

Declare Scope G_scope.
Bind Scope G_scope with G.
Open Scope G_scope.

Infix "+" := Gadd : G_scope.
Notation "- x" := (Gopp x) : G_scope.
Infix "-" := Gsub : G_scope.
Infix "*" := Gmul : G_scope.

Definition ZtoG (z : Z) : G := (z, 0).
Coercion ZtoG : Z >-> G.

Theorem ring_exercise: forall (g1 g2 : G),
  (g1 + g2) * (g1 + g2) = g1 * g1 + (2, 0) * g1 * g2 + g2 * g2.
Proof.
  intros. ring_simplify. reflexivity.
Qed.