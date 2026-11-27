(* ================================================================= *)
(* Phase 60 (companion): NUM60g, the S-form of the TOP14 frame     *)
(* head (74.7M scale: the plain eqb/vm evaluation still fits       *)
(* there).  Alone in a fresh process: as a third vm lemma in       *)
(* Grind28k.v it OOM'd on the accumulated conversion garbage.      *)
(* ================================================================= *)

Require Import Arith.

Lemma NUM60g : 74737819 = S 74737818.
Proof. apply Nat.eqb_eq; vm_compute; reflexivity. Qed.
