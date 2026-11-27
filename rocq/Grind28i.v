(* ================================================================= *)
(* Phase 60 (companion): the div/mod values of 135985237, the      *)
(* X-side of S60rv2, and S60rv3 (see Grind28s.v's header for the   *)
(* div/mod rationale).                                             *)
(* ================================================================= *)

Require Import Arith.

Lemma D60rX : 135985237 / 1048576 = 129.
Proof. apply Nat.eqb_eq; vm_compute; reflexivity. Qed.
Lemma M60rX : 135985237 mod 1048576 = 718933.
Proof. apply Nat.eqb_eq; vm_compute; reflexivity. Qed.
Lemma S60rv3 : 2 <= 18372853.
Proof. apply Nat.leb_le. vm_compute. reflexivity. Qed.
