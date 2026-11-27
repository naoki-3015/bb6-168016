(* ================================================================= *)
(* Phase 59 (companion): NUM59j/k -- the S-form identity for
(* TOP59_4's TRANS2_2 step and the CLEANG_even floor identity of   *)
(* TOP59_BAND (split rationale in Grind27k.v's header).            *) *)
(* ================================================================= *)

Require Import Arith.

Lemma NUM59j : 58806191 = S (S 58806189).
Proof. apply Nat.eqb_eq; vm_compute; reflexivity. Qed.
(* CLEANG_even floor in TOP59_BAND, routed through Hj2:            *)
Lemma NUM59k : 58806190 = 58806193 - 3.
Proof. apply Nat.eqb_eq; vm_compute; reflexivity. Qed.
