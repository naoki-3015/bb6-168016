(* ================================================================= *)
(* Phase 60 (companion): NUM60m1, 135985239 = S 135985238, by       *)
(* div/mod decomposition (see Grind28s.v's header).                 *)
(* ================================================================= *)

Require Import Arith.
Require Import Grind28t.

Lemma D60m1Y : (S 135985238) / 1048576 = 129.
Proof. apply Nat.eqb_eq; vm_compute; reflexivity. Qed.
Lemma M60m1Y : (S 135985238) mod 1048576 = 718935.
Proof. apply Nat.eqb_eq; vm_compute; reflexivity. Qed.

Lemma NUM60m1 : 135985239 = S 135985238.
Proof.
  rewrite (Nat.div_mod_eq 135985239 1048576) at 1.
  rewrite (Nat.div_mod_eq (S 135985238) 1048576) at 1.
  rewrite D60m1X, M60m1X, D60m1Y, M60m1Y. reflexivity.
Qed.
