(* ================================================================= *)
(* Phase 59 (companion): the factored closed facts of the          *)
(* thirteenth descent, proved once by Nat.eqb_eq / Nat.leb_le +    *)
(* vm_compute in a fresh process, before any large cascade         *)
(* environment has accumulated (the Phase 52-58 factoring          *)
(* pattern, one file earlier): the TOP12-front identities          *)
(* S59f1-f3 (the TOP59_TO_TOP13 offset arithmetic), the leb        *)
(* side-goal lemmas S59g0 / S59a1 for the front's big-atom         *)
(* premises (never lia on ~10^7-scale atoms -- the Phase 58        *)
(* finding), the S59g pair for the TOP13 closings' hGRIND_even     *)
(* (added with the closings), and the S59r singleton identities    *)
(* of CASCADE59 (added with the cascade).  No lemma statement      *)
(* anywhere depends on this split.                                 *)
(* ================================================================= *)

Require Import Arith.

(* The TOP59 front offset identities (cf. S58f1-f3).               *)
Lemma S59f1 : 29403095 = 29403096 - 1.
Proof. apply Nat.eqb_eq; vm_compute; reflexivity. Qed.
Lemma S59f2 : 29403095 = 29403092 + 3.
Proof. apply Nat.eqb_eq; vm_compute; reflexivity. Qed.
Lemma S59f3 : 29403096 = 29403092 + 4.
Proof. apply Nat.eqb_eq; vm_compute; reflexivity. Qed.

(* Leb side goals of the TOP12 front at ~2.9 x 10^7 atoms:         *)
(* the sTUP premise 2 <= 29403093 and the DIPGRIND premise         *)
(* 1 <= 29403092, discharged by boolean check, never by lia.       *)
Lemma S59g0 : 2 <= 29403093.
Proof. apply Nat.leb_le; vm_compute; reflexivity. Qed.
Lemma S59a1 : 1 <= 29403092.
Proof. apply Nat.leb_le; vm_compute; reflexivity. Qed.
