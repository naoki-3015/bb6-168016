(* ================================================================= *)
(* Phase 58 (companion): the two closed numeral identities of the  *)
(* final CASCADE58r singleton (step 490, pop12 11874956), factored *)
(* into standalone lemmas proved once by Nat.eqb_eq + vm_compute   *)
(* in a fresh process.  At Phase 58's depths these vm_compute      *)
(* proofs are only affordable before a large cascade environment   *)
(* has accumulated (the Phase 52-57 factoring pattern, one file     *)
(* earlier).  No lemma statement anywhere depends on this split.   *)
(* ================================================================= *)

Require Import Arith.

Lemma S58r1 : 14897638 = 3022682 + 11874956.
Proof. apply Nat.eqb_eq; vm_compute; reflexivity. Qed.
Lemma S58r2 : 29403093 = 5653181 + 2 * 11874956.
Proof. apply Nat.eqb_eq; vm_compute; reflexivity. Qed.
Lemma S58f1 : 11874957 = 11874958 - 1.
Proof. apply Nat.eqb_eq; vm_compute; reflexivity. Qed.
Lemma S58f2 : 11874957 = 11874954 + 3.
Proof. apply Nat.eqb_eq; vm_compute; reflexivity. Qed.
Lemma S58f3 : 11874958 = 11874954 + 4.
Proof. apply Nat.eqb_eq; vm_compute; reflexivity. Qed.
Lemma S58g1 : 1 <= 14701544.
Proof. apply Nat.leb_le; vm_compute; reflexivity. Qed.
Lemma S58g2 : 14701544 <= 14897637.
Proof. apply Nat.leb_le; vm_compute; reflexivity. Qed.
