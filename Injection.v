From Coq Require Import Arith.

Theorem injection_example_1: forall (a b c : nat),
  a = S b -> a = S c -> b = c.
Proof.
  intros. rewrite H0 in H. 
  injection H as H. 
  rewrite H.  
  reflexivity.
Qed.