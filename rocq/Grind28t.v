(* ================================================================= *)
(* Phase 60 (companion): the div/mod values of 135985239 (see      *)
(* Grind28s.v's header for the div/mod rationale).                  *)
(* ================================================================= *)

Require Import Arith.

Lemma D60m1X : 135985239 / 1048576 = 129.
Proof. apply Nat.eqb_eq; vm_compute; reflexivity. Qed.
Lemma M60m1X : 135985239 mod 1048576 = 718935.
Proof. apply Nat.eqb_eq; vm_compute; reflexivity. Qed.
