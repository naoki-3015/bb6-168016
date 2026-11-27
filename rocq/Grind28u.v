(* ================================================================= *)
(* Phase 60 (companion): the div/mod values of 135985240 (see      *)
(* Grind28s.v's header for the div/mod rationale).                  *)
(* ================================================================= *)

Require Import Arith.

Lemma D60mX : 135985240 / 1048576 = 129.
Proof. apply Nat.eqb_eq; vm_compute; reflexivity. Qed.
Lemma M60mX : 135985240 mod 1048576 = 718936.
Proof. apply Nat.eqb_eq; vm_compute; reflexivity. Qed.
