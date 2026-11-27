(* ================================================================= *)
(* Phase 60 (companion): the factored closed facts of the          *)
(* fourteenth descent II (cf. Grind27h.v): the leb side-goal       *)
(* lemmas S60g1 / S60g2 for the TOP14 closings' hGRIND_even        *)
(* premises (never lia on ~10^8-scale atoms).  Proved by           *)
(* Nat.leb_le + vm_compute in a fresh process.  S60h0 and NUM60b   *)
(* live in Grind28ae.v / Grind28af.v: with four evaluated lemmas   *)
(* in one file the conversion garbage OOM'd at Phase 60 depths.    *)
(* No lemma statement anywhere depends on this split.              *)
(* ================================================================= *)

Require Import Arith.

Lemma S60g1 : 1 <= 67992616.
Proof. apply Nat.leb_le; vm_compute; reflexivity. Qed.
Lemma S60g2 : 67992616 <= 74737817.
Proof. apply Nat.leb_le; vm_compute; reflexivity. Qed.
