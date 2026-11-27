(* ================================================================= *)
(* Phase 60 (companion): NUM60h, 135985236 = 135985237 - 1, by      *)
(* div/mod decomposition (see Grind28s.v's header).  The sTUP      *)
(* bridge of the TOP14 closings.                                   *)
(* ================================================================= *)

Require Import Arith.
Require Import Grind28f.

Lemma D60hY : (135985237 - 1) / 1048576 = 129.
Proof. apply Nat.eqb_eq; vm_compute; reflexivity. Qed.
Lemma M60hY : (135985237 - 1) mod 1048576 = 718932.
Proof. apply Nat.eqb_eq; vm_compute; reflexivity. Qed.

Lemma NUM60h : 135985236 = 135985237 - 1.
Proof.
  rewrite (Nat.div_mod_eq 135985236 1048576) at 1.
  rewrite (Nat.div_mod_eq (135985237 - 1) 1048576) at 1.
  rewrite D60hX, M60hX, D60hY, M60hY. reflexivity.
Qed.
