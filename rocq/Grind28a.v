(* ================================================================= *)
(* Phase 60 (companion): the factored closed facts of the          *)
(* fourteenth descent, proved once by Nat.eqb_eq / Nat.leb_le +    *)
(* vm_compute in a fresh process, before any large cascade         *)
(* environment has accumulated (the Phase 52-59 factoring          *)
(* pattern, one file earlier): the TOP13-front identities          *)
(* S60f1-f3 (the TOP60_TO_TOP14 offset arithmetic) and the leb     *)
(* side-goal lemma S60a1 for the front's DIPGRIND premise (never   *)
(* lia on ~10^7-scale atoms -- the Phase 58 finding).  S60f2/f3    *)
(* are stated in S-form (the Phase 60 scale forbids evaluating     *)
(* 58806190 + 3 / 58806190 + 4 directly: an add whose first         *)
(* argument is ~58.8M overflows the host ceiling; the S-form       *)
(* eqb/vm and lia's native S handling carry the same content).     *)
(* No lemma statement anywhere depends on this split.              *)
(* ================================================================= *)

Require Import Arith.

(* The TOP60 front offset identities (cf. S59f1-f3).               *)
Lemma S60f1 : 58806193 = 58806194 - 1.
Proof. apply Nat.eqb_eq; vm_compute; reflexivity. Qed.
Lemma S60f2 : 58806193 = S (S (S 58806190)).
Proof. apply Nat.eqb_eq; vm_compute; reflexivity. Qed.
Lemma S60f3 : 58806194 = S (S (S (S 58806190))).
Proof. apply Nat.eqb_eq; vm_compute; reflexivity. Qed.

(* The DIPGRIND premise of TOP60_TO_TOP14 (cf. S59a1).             *)
Lemma S60a1 : 1 <= 58806190.
Proof. apply Nat.leb_le; vm_compute; reflexivity. Qed.
Lemma S60f4 : 58806194 = S 58806193.
Proof.
  rewrite S60f3. rewrite <- S60f2. reflexivity.
Qed.
