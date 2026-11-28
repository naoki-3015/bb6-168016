(* ================================================================= *)
(* Phase 61 (companion): the factored closed identities of the     *)
(* fifteenth descent's tail (front offsets S61f1-f3, the TOP15     *)
(* S-identities in (V - 1) form, the band floor NUM61k, and the    *)
(* closing bridges NUM61m / NUM61n), each proved by div/mod        *)
(* decomposition at k = 2^20 from the Grind29c* components.        *)
(* ================================================================= *)

Require Import Arith.
Require Import Grind29c1 Grind29c2 Grind29c3 Grind29c4 Grind29c5 Grind29c6 Grind29c7 Grind29c8 Grind29c9 Grind29c10 Grind29c11 Grind29c12 Grind29c13.

Lemma S61f1 : 135985239 = (135985240 - 1).
Proof.
  rewrite (Nat.div_mod_eq (135985239) 1048576) at 1.
  rewrite (Nat.div_mod_eq ((135985240 - 1)) 1048576) at 1.
  rewrite D61f1X, M61f1X, D61f1Y, M61f1Y. reflexivity.
Qed.

Lemma S61f2 : 135985239 = S (S (S 135985236)).
Proof.
  rewrite (Nat.div_mod_eq (135985239) 1048576) at 1.
  rewrite (Nat.div_mod_eq (S (S (S 135985236))) 1048576) at 1.
  rewrite D61f2X, M61f2X, D61f2Y, M61f2Y. reflexivity.
Qed.

Lemma S61f3 : 135985240 = S (S (S (S 135985236))).
Proof.
  rewrite (Nat.div_mod_eq (135985240) 1048576) at 1.
  rewrite (Nat.div_mod_eq (S (S (S (S 135985236)))) 1048576) at 1.
  rewrite D61f3X, M61f3X, D61f3Y, M61f3Y. reflexivity.
Qed.

Lemma NUM61h : 271970478 = (271970479 - 1).
Proof.
  rewrite (Nat.div_mod_eq (271970478) 1048576) at 1.
  rewrite (Nat.div_mod_eq ((271970479 - 1)) 1048576) at 1.
  rewrite D61hX, M61hX, D61hY, M61hY. reflexivity.
Qed.

Lemma NUM61b : 147491795 = S (147491795 - 1).
Proof.
  rewrite (Nat.div_mod_eq (147491795) 1048576) at 1.
  rewrite (Nat.div_mod_eq (S (147491795 - 1)) 1048576) at 1.
  rewrite D61bX, M61bX, D61bY, M61bY. reflexivity.
Qed.

Lemma NUM61e' : 271970479 = S (271970479 - 1).
Proof.
  rewrite (Nat.div_mod_eq (271970479) 1048576) at 1.
  rewrite (Nat.div_mod_eq (S (271970479 - 1)) 1048576) at 1.
  rewrite D61eX, M61eX, D61eY, M61eY. reflexivity.
Qed.

Lemma NUM61f' : 271970480 = S (S (271970479 - 1)).
Proof.
  rewrite (Nat.div_mod_eq (271970480) 1048576) at 1.
  rewrite (Nat.div_mod_eq (S (S (271970479 - 1))) 1048576) at 1.
  rewrite D61fpX, M61fpX, D61fpY, M61fpY. reflexivity.
Qed.

Lemma NUM61g : 147491796 = S 147491795.
Proof.
  rewrite (Nat.div_mod_eq (147491796) 1048576) at 1.
  rewrite (Nat.div_mod_eq (S 147491795) 1048576) at 1.
  rewrite D61gX, M61gX, D61gY, M61gY. reflexivity.
Qed.

Lemma NUM61i' : 271970478 = S (271970479 - 1 - 1).
Proof.
  rewrite (Nat.div_mod_eq (271970478) 1048576) at 1.
  rewrite (Nat.div_mod_eq (S (271970479 - 1 - 1)) 1048576) at 1.
  rewrite D61iX, M61iX, D61iY, M61iY. reflexivity.
Qed.

Lemma NUM61j' : 271970479 = S (S (271970479 - 1 - 1)).
Proof.
  rewrite (Nat.div_mod_eq (271970479) 1048576) at 1.
  rewrite (Nat.div_mod_eq (S (S (271970479 - 1 - 1))) 1048576) at 1.
  rewrite D61jX, M61jX, D61jY, M61jY. reflexivity.
Qed.

Lemma NUM61k : 271970478 = (271970479 + 2) - 3.
Proof.
  rewrite (Nat.div_mod_eq (271970478) 1048576) at 1.
  rewrite (Nat.div_mod_eq ((271970479 + 2) - 3) 1048576) at 1.
  rewrite D61kX, M61kX, D61kY, M61kY. reflexivity.
Qed.

Lemma NUM61m : 271970482 = S (271970479 + 2).
Proof.
  rewrite (Nat.div_mod_eq (271970482) 1048576) at 1.
  rewrite (Nat.div_mod_eq (S (271970479 + 2)) 1048576) at 1.
  rewrite D61mX, M61mX, D61mY, M61mY. reflexivity.
Qed.

Lemma NUM61n : 271970480 = S 271970479.
Proof.
  rewrite (Nat.div_mod_eq (271970480) 1048576) at 1.
  rewrite (Nat.div_mod_eq (S 271970479) 1048576) at 1.
  rewrite D61nX, M61nX, D61nY, M61nY. reflexivity.
Qed.

