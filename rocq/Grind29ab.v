(* ================================================================= *)
(* Phase 61 (companion): NUM61a, 271970478 = 2 * 135985237 + 4, the             *)
(* hGRIND_even bridge of the TOP15 closings, by div/mod            *)
(* decomposition (the NUM60a pattern).  The sum side is            *)
(* decomposed symbolically: Nat.div_mod_eq is applied to each      *)
(* summand separately, and the parts are recombined with           *)
(* variable-only ring lemmas plus one small eqb step.              *)
(* ================================================================= *)

Require Import Arith Lia.
Require Import Grind29c14.

Lemma E61aS : 135985237 = 1048576 * 129 + 718933.
Proof.
  cbn [Nat.of_num_uint Nat.of_uint Nat.of_uint_acc].
  try (rewrite !Nat.tail_mul_spec).
  nia.
Qed.
Lemma HLT61aS : 718933 < 1048576.
Proof.
  cbn [Nat.of_num_uint Nat.of_uint Nat.of_uint_acc].
  try (rewrite !Nat.tail_mul_spec).
  nia.
Qed.
Lemma D61aS : 135985237 / 1048576 = 129.
Proof. symmetry. exact (Nat.div_unique _ _ _ _ HLT61aS E61aS). Qed.
Lemma M61aS : 135985237 mod 1048576 = 718933.
Proof. symmetry. exact (Nat.mod_unique _ _ _ _ HLT61aS E61aS). Qed.

Lemma R61a0 : forall x, 2 * x + 4 = (x + x) + 4.
Proof. intro x. ring. Qed.
Lemma R61a1 : forall k a r, (k * a + r) + (k * a + r) + 4
  = k * (a + a) + (r + r + 4).
Proof. intros k a r. ring. Qed.
Lemma R61a2 : forall k a r, k * a + (k + r) = k * (a + 1) + r.
Proof. intros k a r. ring. Qed.
Lemma E61a : 718933 + 718933 + 4 = 1048576 + 389294.
Proof. apply Nat.eqb_eq; vm_compute; reflexivity. Qed.

Lemma NUM61a : 271970478 = 2 * 135985237 + 4.
Proof.
  rewrite (Nat.div_mod_eq 271970478 1048576) at 1.
  rewrite D61aX, M61aX.
  rewrite R61a0.
  rewrite (Nat.div_mod_eq 135985237 1048576).
  rewrite D61aS, M61aS.
  rewrite R61a1.
  rewrite E61a.
  rewrite R61a2.
  reflexivity.
Qed.
