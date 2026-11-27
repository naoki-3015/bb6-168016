(* ================================================================= *)
(* Phase 60 (companion): NUM60n, 135985238 = S 135985237, by        *)
(* div/mod decomposition (see Grind28s.v's header).                 *)
(* ================================================================= *)

Require Import Arith.
Require Import Grind28s.

Lemma D60nY : (S 135985237) / 1048576 = 129.
Proof. apply Nat.eqb_eq; vm_compute; reflexivity. Qed.
Lemma M60nY : (S 135985237) mod 1048576 = 718934.
Proof. apply Nat.eqb_eq; vm_compute; reflexivity. Qed.

Lemma NUM60n : 135985238 = S 135985237.
Proof.
  rewrite (Nat.div_mod_eq 135985238 1048576) at 1.
  rewrite (Nat.div_mod_eq (S 135985237) 1048576) at 1.
  rewrite D60nX, M60nX, D60nY, M60nY. reflexivity.
Qed.
