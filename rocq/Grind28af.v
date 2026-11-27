(* ================================================================= *)
(* Phase 60 (companion): NUM60b, the S-form of the TOP14 counter,  *)
(* alone in a fresh process (see Grind28b.v's header).             *)
(* ================================================================= *)

Require Import Arith.

Lemma NUM60b : 74737818 = S 74737817.
Proof. apply Nat.eqb_eq; vm_compute; reflexivity. Qed.
