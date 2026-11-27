(* ================================================================= *)
(* Phase 60 (companion): the factored closed identities for the    *)
(* big pop12 singletons of CASCADE60 segments r and t and the      *)
(* A-side identity of segment v (the S59r pattern): proved once    *)
(* by Nat.eqb_eq / Nat.leb_le + vm_compute in a fresh process and  *)
(* rewritten in the singleton blocks of Grind28j.v.  The s-side    *)
(* identity of segment v (S60rv2, at 136M scale) and its leb       *)
(* premise S60rv3 live in Grind28i.v.  No lemma statement          *)
(* anywhere depends on this split.                                 *)
(* ================================================================= *)

Require Import Arith.

Lemma S60rr1 : 10126538 = 2160727 + 7965811.
Proof. apply Nat.eqb_eq; vm_compute; reflexivity. Qed.
Lemma S60rr2 : 15931625 = 3 + 2 * 7965811.
Proof. apply Nat.eqb_eq; vm_compute; reflexivity. Qed.
Lemma S60rr3 : 2 <= 3.
Proof. apply Nat.leb_le; vm_compute; reflexivity. Qed.
Lemma S60rt1 : 15931625 = 15931624 + 1.
Proof. apply Nat.eqb_eq; vm_compute; reflexivity. Qed.
Lemma S60rt2 : 18372852 = 18372850 + 2 * 1.
Proof. apply Nat.eqb_eq; vm_compute; reflexivity. Qed.
Lemma S60rt3 : 2 <= 18372850.
Proof. apply Nat.leb_le; vm_compute; reflexivity. Qed.
Lemma S60rv1 : 74737818 = 15931626 + 58806192.
Proof. apply Nat.eqb_eq; vm_compute; reflexivity. Qed.
