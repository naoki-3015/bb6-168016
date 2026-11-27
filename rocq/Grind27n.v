(* ================================================================= *)
(* Phase 59 (companion): NUM59m/n -- the S-form identities
(* for the TAIL2_END13_of59 case split (split rationale in         *)
(* Grind27k.v's header).                                           *) *)
(* ================================================================= *)

Require Import Arith.

Lemma NUM59m : 58806194 = S 58806193.
Proof. apply Nat.eqb_eq; vm_compute; reflexivity. Qed.
Lemma NUM59n : 58806192 = S 58806191.
Proof. apply Nat.eqb_eq; vm_compute; reflexivity. Qed.
