(* ================================================================= *)
(* Phase 60 (companion): NUM60i', the TOP14 counter S-identity in   *)
(* (V - 1) form (see Grind28q.v's header for the 136M scale         *)
(* rationale).                                                     *)
(* ================================================================= *)

Require Import Arith.
Require Import Grind28q.

Lemma NUM60i' : 135985236 = S (135985236 - 1).
Proof.
  apply S_sub_1_60. apply Nat.leb_le. vm_compute. reflexivity.
Qed.
