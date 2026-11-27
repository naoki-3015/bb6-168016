(* ================================================================= *)
(* Phase 60 (companion): the div/mod values of 135985237, the      *)
(* X-side of NUM60j' (see Grind28s.v's header for the div/mod      *)
(* rationale).                                                     *)
(* ================================================================= *)

Require Import Arith.

Lemma D60jX : 135985237 / 1048576 = 129.
Proof. apply Nat.eqb_eq; vm_compute; reflexivity. Qed.
Lemma M60jX : 135985237 mod 1048576 = 718933.
Proof. apply Nat.eqb_eq; vm_compute; reflexivity. Qed.
