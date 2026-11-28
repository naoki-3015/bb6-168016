(* ================================================================= *)
(* Phase 62 (companion): NUM62a, 595648556 = 2 * 297824276 + 4, the             *)
(* hGRIND_even bridge of the TOP15 closings, by div/mod            *)
(* decomposition (the NUM60a pattern).  The sum side is            *)
(* decomposed symbolically: Nat.div_mod_eq is applied to each      *)
(* summand separately, and the parts are recombined with           *)
(* variable-only ring lemmas plus one small eqb step.              *)
(* ================================================================= *)

Require Import Arith Lia.
Require Import Grind30c15.

Lemma E62aS : 297824276 = 1048576 * 284 + 28692.
Proof.
  cbn [Nat.of_num_uint Nat.of_uint Nat.of_uint_acc].
  try (rewrite !Nat.tail_mul_spec).
  nia.
Qed.
Lemma HLT62aS : 28692 < 1048576.
Proof.
  cbn [Nat.of_num_uint Nat.of_uint Nat.of_uint_acc].
  try (rewrite !Nat.tail_mul_spec).
  nia.
Qed.
Lemma D62aS : 297824276 / 1048576 = 284.
Proof. symmetry. exact (Nat.div_unique _ _ _ _ HLT62aS E62aS). Qed.
Lemma M62aS : 297824276 mod 1048576 = 28692.
Proof. symmetry. exact (Nat.mod_unique _ _ _ _ HLT62aS E62aS). Qed.

Lemma R62a0 : forall x, 2 * x + 4 = (x + x) + 4.
Proof. intro x. ring. Qed.
Lemma R62a1 : forall k a r, (k * a + r) + (k * a + r) + 4
  = k * (a + a) + (r + r + 4).
Proof. intros k a r. ring. Qed.
Lemma R62a2 : forall k a r, k * a + (k + r) = k * (a + 1) + r.
Proof. intros k a r. ring. Qed.
Lemma E62a : 28692 + 28692 + 4 = 57388.
Proof. apply Nat.eqb_eq; vm_compute; reflexivity. Qed.
Lemma E62a2 : 284 + 284 = 568.
Proof. apply Nat.eqb_eq; vm_compute; reflexivity. Qed.

Lemma NUM62a : 595648556 = 2 * 297824276 + 4.
Proof.
  rewrite (Nat.div_mod_eq 595648556 1048576) at 1.
  rewrite D62aX, M62aX.
  rewrite R62a0.
  rewrite (Nat.div_mod_eq 297824276 1048576).
  rewrite D62aS, M62aS.
  rewrite R62a1.
  rewrite E62a.
  rewrite E62a2.
  reflexivity.
Qed.
