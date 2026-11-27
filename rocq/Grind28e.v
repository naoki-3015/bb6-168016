(* ================================================================= *)
(* Phase 60 (companion): the div/mod values of 135985238, the      *)
(* X-side of NUM60f' (see Grind28s.v's header for the div/mod      *)
(* rationale).                                                     *)
(* ================================================================= *)

Require Import Arith.

Lemma D60fX : 135985238 / 1048576 = 129.
Proof. apply Nat.eqb_eq; vm_compute; reflexivity. Qed.
Lemma M60fX : 135985238 mod 1048576 = 718934.
Proof. apply Nat.eqb_eq; vm_compute; reflexivity. Qed.
