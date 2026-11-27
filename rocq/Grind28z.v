(* ================================================================= *)
(* Phase 60 (companion): NUM60k, 135985236 = 135985239 - 3, by      *)
(* div/mod decomposition (see Grind28s.v's header).  The band      *)
(* floor of TOP60_BAND.                                            *)
(* ================================================================= *)

Require Import Arith.
Require Import Grind28g.

Lemma D60kY : (135985239 - 3) / 1048576 = 129.
Proof. apply Nat.eqb_eq; vm_compute; reflexivity. Qed.
Lemma M60kY : (135985239 - 3) mod 1048576 = 718932.
Proof. apply Nat.eqb_eq; vm_compute; reflexivity. Qed.

Lemma NUM60k : 135985236 = 135985239 - 3.
Proof.
  rewrite (Nat.div_mod_eq 135985236 1048576) at 1.
  rewrite (Nat.div_mod_eq (135985239 - 3) 1048576) at 1.
  rewrite D60kX, M60kX, D60kY, M60kY. reflexivity.
Qed.
