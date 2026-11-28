(* ================================================================= *)
(* Phase 63 (companion): the factored closed identities of the     *)
(* seventeenth descent's tail (front offsets S63f1-f3, the TOP16     *)
(* S-identities in (V - 1) form, the band floor NUM63k, and the    *)
(* closing bridges NUM63m / NUM63n), each proved by div/mod        *)
(* decomposition at k = 2^20 from the Grind31c* components.        *)
(* ================================================================= *)

Require Import Arith.
Require Import Grind31c1 Grind31c2 Grind31c3 Grind31c4 Grind31c5 Grind31c6 Grind31c7 Grind31c8 Grind31c9 Grind31c10 Grind31c11 Grind31c12 Grind31c13 Grind31c14.

Lemma S63f1 : 595648559 = (595648560 - 1).
Proof.
  rewrite (Nat.div_mod_eq (595648559) 1048576) at 1.
  rewrite (Nat.div_mod_eq ((595648560 - 1)) 1048576) at 1.
  rewrite D63f1X, M63f1X, D63f1Y, M63f1Y. reflexivity.
Qed.

Lemma S63f2 : 595648559 = S (S (S 595648556)).
Proof.
  rewrite (Nat.div_mod_eq (595648559) 1048576) at 1.
  rewrite (Nat.div_mod_eq (S (S (S 595648556))) 1048576) at 1.
  rewrite D63f2X, M63f2X, D63f2Y, M63f2Y. reflexivity.
Qed.

Lemma S63f3 : 595648560 = S (S (S (S 595648556))).
Proof.
  rewrite (Nat.div_mod_eq (595648560) 1048576) at 1.
  rewrite (Nat.div_mod_eq (S (S (S (S 595648556)))) 1048576) at 1.
  rewrite D63f3X, M63f3X, D63f3Y, M63f3Y. reflexivity.
Qed.

Lemma NUM63h : 1191297118 = (1191297119 - 1).
Proof.
  rewrite (Nat.div_mod_eq (1191297118) 1048576) at 1.
  rewrite (Nat.div_mod_eq ((1191297119 - 1)) 1048576) at 1.
  rewrite D63hX, M63hX, D63hY, M63hY. reflexivity.
Qed.

Lemma NUM63b : 842094153 = S (842094153 - 1).
Proof.
  rewrite (Nat.div_mod_eq (842094153) 1048576) at 1.
  rewrite (Nat.div_mod_eq (S (842094153 - 1)) 1048576) at 1.
  rewrite D63bX, M63bX, D63bY, M63bY. reflexivity.
Qed.

Lemma NUM63e' : 1191297119 = S (1191297119 - 1).
Proof.
  rewrite (Nat.div_mod_eq (1191297119) 1048576) at 1.
  rewrite (Nat.div_mod_eq (S (1191297119 - 1)) 1048576) at 1.
  rewrite D63eX, M63eX, D63eY, M63eY. reflexivity.
Qed.

Lemma NUM63f' : 1191297120 = S (S (1191297119 - 1)).
Proof.
  rewrite (Nat.div_mod_eq (1191297120) 1048576) at 1.
  rewrite (Nat.div_mod_eq (S (S (1191297119 - 1))) 1048576) at 1.
  rewrite D63fpX, M63fpX, D63fpY, M63fpY. reflexivity.
Qed.

Lemma NUM63g : 842094154 = S 842094153.
Proof.
  rewrite (Nat.div_mod_eq (842094154) 1048576) at 1.
  rewrite (Nat.div_mod_eq (S 842094153) 1048576) at 1.
  rewrite D63gX, M63gX, D63gY, M63gY. reflexivity.
Qed.

Lemma NUM63i' : 1191297118 = S (1191297119 - 1 - 1).
Proof.
  rewrite (Nat.div_mod_eq (1191297118) 1048576) at 1.
  rewrite (Nat.div_mod_eq (S (1191297119 - 1 - 1)) 1048576) at 1.
  rewrite D63iX, M63iX, D63iY, M63iY. reflexivity.
Qed.

Lemma NUM63j' : 1191297119 = S (S (1191297119 - 1 - 1)).
Proof.
  rewrite (Nat.div_mod_eq (1191297119) 1048576) at 1.
  rewrite (Nat.div_mod_eq (S (S (1191297119 - 1 - 1))) 1048576) at 1.
  rewrite D63jX, M63jX, D63jY, M63jY. reflexivity.
Qed.

Lemma NUM63k : 1191297118 = (1191297119 + 2) - 3.
Proof.
  rewrite (Nat.div_mod_eq (1191297118) 1048576) at 1.
  rewrite (Nat.div_mod_eq ((1191297119 + 2) - 3) 1048576) at 1.
  rewrite D63kX, M63kX, D63kY, M63kY. reflexivity.
Qed.

Lemma NUM63m : 1191297122 = S (1191297119 + 2).
Proof.
  rewrite (Nat.div_mod_eq (1191297122) 1048576) at 1.
  rewrite (Nat.div_mod_eq (S (1191297119 + 2)) 1048576) at 1.
  rewrite D63mX, M63mX, D63mY, M63mY. reflexivity.
Qed.

Lemma NUM63n : 1191297120 = S 1191297119.
Proof.
  rewrite (Nat.div_mod_eq (1191297120) 1048576) at 1.
  rewrite (Nat.div_mod_eq (S 1191297119) 1048576) at 1.
  rewrite D63nX, M63nX, D63nY, M63nY. reflexivity.
Qed.

Lemma NUM63m2 : 595648560 = S 595648559.
Proof.
  rewrite (Nat.div_mod_eq (595648560) 1048576) at 1.
  rewrite (Nat.div_mod_eq (S 595648559) 1048576) at 1.
  rewrite D63m2X, M63m2X, D63m2Y, M63m2Y. reflexivity.
Qed.

