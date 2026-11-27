(* ================================================================= *)
(* Phase 60 (companion): the div/mod values of 135985236, the      *)
(* X-side of NUM60a (see Grind28s.v's header for the div/mod       *)
(* rationale).                                                     *)
(* ================================================================= *)

Require Import Arith.

Lemma D60aX : 135985236 / 1048576 = 129.
Proof. apply Nat.eqb_eq; vm_compute; reflexivity. Qed.
Lemma M60aX : 135985236 mod 1048576 = 718932.
Proof. apply Nat.eqb_eq; vm_compute; reflexivity. Qed.
