(* ================================================================= *)
(* Phase 60 (companion): NUM60j', 135985237 = S (S (135985236 - 1)),*)
(* by div/mod decomposition (see Grind28s.v's header).  The        *)
(* TRANS2_2 frame-head bridge of TOP60_4.                          *)
(* ================================================================= *)

Require Import Arith.
Require Import Grind28v.

Lemma D60jY : (S (S (135985236 - 1))) / 1048576 = 129.
Proof. apply Nat.eqb_eq; vm_compute; reflexivity. Qed.
Lemma M60jY : (S (S (135985236 - 1))) mod 1048576 = 718933.
Proof. apply Nat.eqb_eq; vm_compute; reflexivity. Qed.

Lemma NUM60j' : 135985237 = S (S (135985236 - 1)).
Proof.
  rewrite (Nat.div_mod_eq 135985237 1048576) at 1.
  rewrite (Nat.div_mod_eq (S (S (135985236 - 1))) 1048576) at 1.
  rewrite D60jX, M60jX, D60jY, M60jY. reflexivity.
Qed.
