Require Import Arith.PeanoNat.

Theorem exists_example_1 : forall n: nat,
  (exists m, n = 4 + m) -> (exists o, n = 2 + o).
Proof.
  intros. destruct H as [y H]. 
  exists (2 + y). 
  rewrite H. reflexivity.
Qed.

Theorem divide_trans: forall a b c: nat,
  Nat.divide a b -> Nat.divide b c -> Nat.divide a c.
Proof.
  intros. destruct H as [x H]. destruct H0 as [y H0].
  exists (y * x). rewrite H0. rewrite H. rewrite Nat.mul_assoc.
  reflexivity.
Qed. 
  

Theorem dist_exists_or : forall (X: Type) (P Q : X -> Prop),
  (exists x, P x \/ Q x) <-> (exists x, P x) \/ (exists x, Q x).
Proof.
  intros. split.
  - intros. destruct H as [ x [F | S] ].
    + left. exists x. apply F.
    + right. exists x. apply S.
  - intros [F | S].
    + destruct F. exists x. left. apply H.
    + destruct S. exists x. right. apply H.
Qed.