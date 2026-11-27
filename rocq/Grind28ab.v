(* ================================================================= *)
(* Phase 60 (companion): NUM60a, 135985236 = 2 * 67992616 + 4, the  *)
(* hGRIND_even bridge of the TOP14 closings, by div/mod            *)
(* decomposition (see Grind28s.v's header).  The sum side is       *)
(* decomposed symbolically: Nat.div_mod_eq is applied to each      *)
(* summand separately (a whole-sum evaluation OOMs: probeDMY),     *)
(* and the parts are recombined with variable-only ring lemmas     *)
(* plus one small eqb step (ring does not accept concrete          *)
(* of_num_uint numerals: probeRing).                               *)
(* ================================================================= *)

Require Import Arith.
Require Import Grind28d.

Lemma D60aS : 67992616 / 1048576 = 64.
Proof. apply Nat.eqb_eq; vm_compute; reflexivity. Qed.
Lemma M60aS : 67992616 mod 1048576 = 883752.
Proof. apply Nat.eqb_eq; vm_compute; reflexivity. Qed.

Lemma R60a0 : forall x, 2 * x + 4 = (x + x) + 4.
Proof. intro x. ring. Qed.
Lemma R60a1 : forall k a r, (k * a + r) + (k * a + r) + 4
  = k * (a + a) + (r + r + 4).
Proof. intros k a r. ring. Qed.
Lemma R60a2 : forall k a r, k * a + (k + r) = k * (a + 1) + r.
Proof. intros k a r. ring. Qed.
Lemma E60a : 883752 + 883752 + 4 = 1048576 + 718932.
Proof. apply Nat.eqb_eq; vm_compute; reflexivity. Qed.

Lemma NUM60a : 135985236 = 2 * 67992616 + 4.
Proof.
  rewrite (Nat.div_mod_eq 135985236 1048576) at 1.
  rewrite D60aX, M60aX.
  rewrite R60a0.
  rewrite (Nat.div_mod_eq 67992616 1048576).
  rewrite D60aS, M60aS.
  rewrite R60a1.
  rewrite E60a.
  rewrite R60a2.
  reflexivity.
Qed.
