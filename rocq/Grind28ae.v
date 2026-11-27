(* ================================================================= *)
(* Phase 60 (companion): S60h0, the sTUP premise of the TOP14      *)
(* closings, alone in a fresh process (see Grind28b.v's header).   *)
(* ================================================================= *)

Require Import Arith.

Lemma S60h0 : 2 <= 135985237.
Proof. apply Nat.leb_le; vm_compute; reflexivity. Qed.
