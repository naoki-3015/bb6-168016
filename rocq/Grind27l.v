(* ================================================================= *)
(* Phase 59 (companion): NUM59h/i -- the subtraction and
(* S-form identities for the TOP13 closings (split rationale in    *)
(* Grind27k.v's header).                                           *) *)
(* ================================================================= *)

Require Import Arith.

Lemma NUM59h : 58806190 = 58806191 - 1.
Proof. apply Nat.eqb_eq; vm_compute; reflexivity. Qed.
Lemma NUM59i : 58806190 = S 58806189.
Proof. apply Nat.eqb_eq; vm_compute; reflexivity. Qed.
