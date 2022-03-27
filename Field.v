From Coq Require Import Reals.
From Coq Require Import QArith.
Require Import Field.
 
Open Scope R_scope.

Definition C : Type := R * R.

Definition RtoC (r : R) : C := (r, 0).
Coercion RtoC : R >-> C.

Declare Scope C_scope.
Bind Scope C_scope with C.
Open Scope C_scope.

Notation i := (0,1).
Notation "0" := (RtoC 0) : C_scope.
Notation "1" := (RtoC 1) : C_scope.

Definition Cadd (c1 c2 : C) : C := (fst c1 + fst c2, snd c1 + snd c2).
Definition Csub (c1 c2 : C) : C := (fst c1 - fst c2, snd c1 - snd c2).
Definition Cmul (c1 c2 : C) : C := (fst c1 * fst c2 - snd c1 * snd c2, fst c1 * snd c2 + snd c1 * fst c2).
Definition Copp (c : C) : C := (- fst c, - snd c).
Definition Cinv (c : C) : C := 
  ( fst c / (fst c * fst c + snd c * snd c), - snd c / (fst c * fst c + snd c * snd c) ).
Definition Cdiv (c1 c2 : C) : C := Cmul c1 (Cinv c2).

Lemma c_proj_eq : forall (c1 c2 : C),
  fst c1 = fst c2 -> snd c1 = snd c2 -> c1 = c2.
Proof. 
  intros. destruct c1, c2. simpl in *. subst. reflexivity. 
Qed.

Lemma Cadd_0_l: forall (c: C),
  Cadd 0 c = c.
Proof.
  intros. apply c_proj_eq; simpl; ring.
Qed.

Lemma Cadd_comm: forall (c1 c2: C),
  Cadd c1 c2 = Cadd c2 c1.
Proof.
  intros. apply c_proj_eq; simpl; ring.
Qed.

Lemma Cadd_assoc: forall c1 c2 c3: C,
  Cadd c1 (Cadd c2 c3) = Cadd (Cadd c1 c2) c3.
Proof.
  intros. apply c_proj_eq; simpl; ring.
Qed.

Lemma Cmul_1_l: forall c : C, 
  Cmul 1 c = c.
Proof.
  intros. apply c_proj_eq; simpl; ring.
Qed.

Lemma Cmul_comm: forall c1 c2 : C, 
  Cmul c1 c2 = Cmul c2 c1.
Proof.
  intros. apply c_proj_eq; simpl; ring.
Qed.

Lemma Cmul_assoc: forall c1 c2 c3 : C, 
  ( Cmul c1 (Cmul c2 c3) ) = ( Cmul (Cmul c1 c2) c3 ).
Proof.
  intros. apply c_proj_eq; simpl; ring.
Qed.

Lemma Cdistr_l: forall c1 c2 c3: C, 
  Cmul (Cadd c1 c2) c3 = Cadd (Cmul c1 c3) (Cmul c2 c3).
Proof.
  intros. apply c_proj_eq; simpl; ring.
Qed.

Lemma Copp_def : forall c : C,
  Cadd c (Copp c) = 0.
Proof.
  intros. apply c_proj_eq; simpl; ring.
Qed.

Lemma C1_neq_C0 : 1 <> 0. 
Proof. 
Admitted.

Lemma Cinv_l : forall c: C, 
  c <> 0 -> Cmul (Cinv c) c = 1.
Proof.
  Admitted.

Lemma C_Field_Theory : @field_theory C 0 1 Cadd Cmul Csub Copp Cdiv Cinv eq.
Proof.
  constructor. constructor.
  - apply Cadd_0_l.
  - apply Cadd_comm.
  - apply Cadd_assoc.
  - apply Cmul_1_l.
  - apply Cmul_comm.
  - apply Cmul_assoc.
  - apply Cdistr_l.
  - reflexivity.
  - apply Copp_def.
  - apply C1_neq_C0.
  - reflexivity.
  - apply Cinv_l.
Defined.
Add Field CField : C_Field_Theory.