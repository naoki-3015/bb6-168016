(* ================================================================= *)
(* Phase 63 (companion): NUM63a, 1191297118 = 2 * 595648557 + 4, the             *)
(* hGRIND_even bridge of the TOP16 closings, by div/mod            *)
(* decomposition (the NUM60a pattern).  The sum side is            *)
(* decomposed symbolically: Nat.div_mod_eq is applied to each      *)
(* summand separately, and the parts are recombined with           *)
(* variable-only ring lemmas plus one small eqb step.              *)
(* ================================================================= *)

Require Import Arith Lia.
Require Import Grind31c15.

Lemma E63aS : 595648557 = 1048576 * 568 + 57389.
Proof.
  cbn [Nat.of_num_uint Nat.of_uint Nat.of_uint_acc].
  try (rewrite !Nat.tail_mul_spec).
  nia.
Qed.
Lemma HLT63aS : 57389 < 1048576.
Proof.
  cbn [Nat.of_num_uint Nat.of_uint Nat.of_uint_acc].
  try (rewrite !Nat.tail_mul_spec).
  nia.
Qed.
Lemma D63aS : 595648557 / 1048576 = 568.
Proof. symmetry. exact (Nat.div_unique _ _ _ _ HLT63aS E63aS). Qed.
Lemma M63aS : 595648557 mod 1048576 = 57389.
Proof. symmetry. exact (Nat.mod_unique _ _ _ _ HLT63aS E63aS). Qed.

Lemma R63a0 : forall x, 2 * x + 4 = (x + x) + 4.
Proof. intro x. ring. Qed.
Lemma R63a1 : forall k a r, (k * a + r) + (k * a + r) + 4
  = k * (a + a) + (r + r + 4).
Proof. intros k a r. ring. Qed.
Lemma R63a2 : forall k a r, k * a + (k + r) = k * (a + 1) + r.
Proof. intros k a r. ring. Qed.
Lemma E63a : 57389 + 57389 + 4 = 114782.
Proof. apply Nat.eqb_eq; vm_compute; reflexivity. Qed.
Lemma E63a2 : 568 + 568 = 1136.
Proof. apply Nat.eqb_eq; vm_compute; reflexivity. Qed.

Lemma NUM63a : 1191297118 = 2 * 595648557 + 4.
Proof.
  rewrite (Nat.div_mod_eq 1191297118 1048576) at 1.
  rewrite D63aX, M63aX.
  rewrite R63a0.
  rewrite (Nat.div_mod_eq 595648557 1048576).
  rewrite D63aS, M63aS.
  rewrite R63a1.
  rewrite E63a.
  rewrite E63a2.
  reflexivity.
Qed.
