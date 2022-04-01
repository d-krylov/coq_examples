Require Import Arith.

Theorem sum_comm: forall (a b: nat),
  a + b = b + a.
Proof.
  intros. replace (a + b) with (b + a) by (rewrite Nat.add_comm; reflexivity).
  reflexivity.
Qed.