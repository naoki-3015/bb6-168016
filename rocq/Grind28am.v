(* ================================================================= *)
(* Phase 60 (companion): P660, the CLEANG_odd premise of CASCADE60   *)
(* step 660 (segment s).  closearith's lazy-leb fallback is a        *)
(* quadratic-conversion bomb at this scale (probes probeLeb /       *)
(* probeLeb2 / probe660a, build-logs-60/); the vm_compute cast      *)
(* route (the S60g pattern of Grind28b.v) proves it in a fresh       *)
(* process at ~1.8 GB.                                               *)
(* ================================================================= *)

Require Import Arith.

Lemma P660 : 9186421 + 2 <= 15931624.
Proof. apply Nat.leb_le; vm_compute; reflexivity. Qed.
