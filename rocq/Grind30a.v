(* ================================================================= *)
(* Phase 62 (companion): the factored closed identities of the     *)
(* sixteenth descent's tail (front offsets S62f1-f3, the TOP15     *)
(* S-identities in (V - 1) form, the band floor NUM62k, and the    *)
(* closing bridges NUM62m / NUM62n), each proved by div/mod        *)
(* decomposition at k = 2^20 from the Grind30c* components.        *)
(* ================================================================= *)

Require Import Arith.
Require Import Grind30c1 Grind30c2 Grind30c3 Grind30c4 Grind30c5 Grind30c6 Grind30c7 Grind30c8 Grind30c9 Grind30c10 Grind30c11 Grind30c12 Grind30c13 Grind30c14.

Lemma S62f1 : 271970481 = (271970482 - 1).
Proof.
  rewrite (Nat.div_mod_eq (271970481) 1048576) at 1.
  rewrite (Nat.div_mod_eq ((271970482 - 1)) 1048576) at 1.
  rewrite D62f1X, M62f1X, D62f1Y, M62f1Y. reflexivity.
Qed.

Lemma S62f2 : 271970481 = S (S (S 271970478)).
Proof.
  rewrite (Nat.div_mod_eq (271970481) 1048576) at 1.
  rewrite (Nat.div_mod_eq (S (S (S 271970478))) 1048576) at 1.
  rewrite D62f2X, M62f2X, D62f2Y, M62f2Y. reflexivity.
Qed.

Lemma S62f3 : 271970482 = S (S (S (S 271970478))).
Proof.
  rewrite (Nat.div_mod_eq (271970482) 1048576) at 1.
  rewrite (Nat.div_mod_eq (S (S (S (S 271970478)))) 1048576) at 1.
  rewrite D62f3X, M62f3X, D62f3Y, M62f3Y. reflexivity.
Qed.

Lemma NUM62h : 595648556 = (595648557 - 1).
Proof.
  rewrite (Nat.div_mod_eq (595648556) 1048576) at 1.
  rewrite (Nat.div_mod_eq ((595648557 - 1)) 1048576) at 1.
  rewrite D62hX, M62hX, D62hY, M62hY. reflexivity.
Qed.

Lemma NUM62b : 367754682 = S (367754682 - 1).
Proof.
  rewrite (Nat.div_mod_eq (367754682) 1048576) at 1.
  rewrite (Nat.div_mod_eq (S (367754682 - 1)) 1048576) at 1.
  rewrite D62bX, M62bX, D62bY, M62bY. reflexivity.
Qed.

Lemma NUM62e' : 595648557 = S (595648557 - 1).
Proof.
  rewrite (Nat.div_mod_eq (595648557) 1048576) at 1.
  rewrite (Nat.div_mod_eq (S (595648557 - 1)) 1048576) at 1.
  rewrite D62eX, M62eX, D62eY, M62eY. reflexivity.
Qed.

Lemma NUM62f' : 595648558 = S (S (595648557 - 1)).
Proof.
  rewrite (Nat.div_mod_eq (595648558) 1048576) at 1.
  rewrite (Nat.div_mod_eq (S (S (595648557 - 1))) 1048576) at 1.
  rewrite D62fpX, M62fpX, D62fpY, M62fpY. reflexivity.
Qed.

Lemma NUM62g : 367754683 = S 367754682.
Proof.
  rewrite (Nat.div_mod_eq (367754683) 1048576) at 1.
  rewrite (Nat.div_mod_eq (S 367754682) 1048576) at 1.
  rewrite D62gX, M62gX, D62gY, M62gY. reflexivity.
Qed.

Lemma NUM62i' : 595648556 = S (595648557 - 1 - 1).
Proof.
  rewrite (Nat.div_mod_eq (595648556) 1048576) at 1.
  rewrite (Nat.div_mod_eq (S (595648557 - 1 - 1)) 1048576) at 1.
  rewrite D62iX, M62iX, D62iY, M62iY. reflexivity.
Qed.

Lemma NUM62j' : 595648557 = S (S (595648557 - 1 - 1)).
Proof.
  rewrite (Nat.div_mod_eq (595648557) 1048576) at 1.
  rewrite (Nat.div_mod_eq (S (S (595648557 - 1 - 1))) 1048576) at 1.
  rewrite D62jX, M62jX, D62jY, M62jY. reflexivity.
Qed.

Lemma NUM62k : 595648556 = (595648557 + 2) - 3.
Proof.
  rewrite (Nat.div_mod_eq (595648556) 1048576) at 1.
  rewrite (Nat.div_mod_eq ((595648557 + 2) - 3) 1048576) at 1.
  rewrite D62kX, M62kX, D62kY, M62kY. reflexivity.
Qed.

Lemma NUM62m : 595648560 = S (595648557 + 2).
Proof.
  rewrite (Nat.div_mod_eq (595648560) 1048576) at 1.
  rewrite (Nat.div_mod_eq (S (595648557 + 2)) 1048576) at 1.
  rewrite D62mX, M62mX, D62mY, M62mY. reflexivity.
Qed.

Lemma NUM62n : 595648558 = S 595648557.
Proof.
  rewrite (Nat.div_mod_eq (595648558) 1048576) at 1.
  rewrite (Nat.div_mod_eq (S 595648557) 1048576) at 1.
  rewrite D62nX, M62nX, D62nY, M62nY. reflexivity.
Qed.

Lemma NUM62m2 : 271970482 = S 271970481.
Proof.
  rewrite (Nat.div_mod_eq (271970482) 1048576) at 1.
  rewrite (Nat.div_mod_eq (S 271970481) 1048576) at 1.
  rewrite D62m2X, M62m2X, D62m2Y, M62m2Y. reflexivity.
Qed.

