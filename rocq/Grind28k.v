(* ================================================================= *)
(* Phase 60 (companion): NUM60f', 135985238 = S (S (135985237 - 1)),*)
(* by div/mod decomposition (see Grind28s.v's header).             *)
(* ================================================================= *)

Require Import Arith.
Require Import Grind28e.

Lemma D60fY : (S (S (135985237 - 1))) / 1048576 = 129.
Proof. apply Nat.eqb_eq; vm_compute; reflexivity. Qed.
Lemma M60fY : (S (S (135985237 - 1))) mod 1048576 = 718934.
Proof. apply Nat.eqb_eq; vm_compute; reflexivity. Qed.

Lemma NUM60f' : 135985238 = S (S (135985237 - 1)).
Proof.
  rewrite (Nat.div_mod_eq 135985238 1048576) at 1.
  rewrite (Nat.div_mod_eq (S (S (135985237 - 1))) 1048576) at 1.
  rewrite D60fX, M60fX, D60fY, M60fY. reflexivity.
Qed.
