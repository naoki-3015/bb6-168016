Require Import List Arith Lia.
Require Import Grind31h.

(* Factored list identities for the PX2A steps of           *)
(* CASCADE63 whose produced (1, 2)s merge into a spine      *)
(* repeat of length > 175000 (auto-detected by gen63.py).   *)
Lemma E63ssaX : 595648558 = 1048576 * 568 + 57390.
Proof.
  cbn [Nat.of_num_uint Nat.of_uint Nat.of_uint_acc].
  try (rewrite !Nat.tail_mul_spec).
  nia.
Qed.
Lemma HLT63ssaX : 57390 < 1048576.
Proof.
  cbn [Nat.of_num_uint Nat.of_uint Nat.of_uint_acc].
  try (rewrite !Nat.tail_mul_spec).
  nia.
Qed.
Lemma D63ssaX : 595648558 / 1048576 = 568.
Proof. symmetry. exact (Nat.div_unique _ _ _ _ HLT63ssaX E63ssaX). Qed.
Lemma M63ssaX : 595648558 mod 1048576 = 57390.
Proof. symmetry. exact (Nat.mod_unique _ _ _ _ HLT63ssaX E63ssaX). Qed.
Lemma E63ssaY : 595648556 = 1048576 * 568 + 57388.
Proof.
  cbn [Nat.of_num_uint Nat.of_uint Nat.of_uint_acc].
  try (rewrite !Nat.tail_mul_spec).
  nia.
Qed.
Lemma HLT63ssaY : 57388 < 1048576.
Proof.
  cbn [Nat.of_num_uint Nat.of_uint Nat.of_uint_acc].
  try (rewrite !Nat.tail_mul_spec).
  nia.
Qed.
Lemma D63ssaY : 595648556 / 1048576 = 568.
Proof. symmetry. exact (Nat.div_unique _ _ _ _ HLT63ssaY E63ssaY). Qed.
Lemma M63ssaY : 595648556 mod 1048576 = 57388.
Proof. symmetry. exact (Nat.mod_unique _ _ _ _ HLT63ssaY E63ssaY). Qed.
Lemma E63ssa : 57388 + 2 = 57390.
Proof. apply Nat.eqb_eq; vm_compute; reflexivity. Qed.
Lemma NUM63ssa : 595648558 = S (S 595648556).
Proof.
  rewrite <- (ADD2S 595648556).
  rewrite (Nat.div_mod_eq 595648558 1048576) at 1.
  rewrite D63ssaX, M63ssaX.
  rewrite (Nat.div_mod_eq 595648556 1048576).
  rewrite D63ssaY, M63ssaY.
  rewrite <- Nat.add_assoc.
  rewrite (E63ssa).
  reflexivity.
Qed.
Lemma REP63a : forall w,
  (1, 1) :: (1, 2) :: (1, 2) :: repeat (1, 2) 595648556 ++ w
  = (1, 1) :: repeat (1, 2) 595648558 ++ w.
Proof. intro w. rewrite NUM63ssa. reflexivity. Qed.
Lemma NUM63ta1 : 367754682 = S (S (S 367754679)).
Proof.
  cbn [Nat.of_num_uint Nat.of_uint Nat.of_uint_acc].
  try (rewrite !Nat.tail_mul_spec).
  nia.
Qed.
Lemma NUM63ta2 : 60654542 = S 60654541.
Proof.
  cbn [Nat.of_num_uint Nat.of_uint Nat.of_uint_acc].
  try (rewrite !Nat.tail_mul_spec).
  nia.
Qed.
Lemma NUM63ta3 : 367754680 = S 367754679.
Proof.
  cbn [Nat.of_num_uint Nat.of_uint Nat.of_uint_acc].
  try (rewrite !Nat.tail_mul_spec).
  nia.
Qed.
Lemma E63ssbX : 60654542 = 1048576 * 57 + 885710.
Proof.
  cbn [Nat.of_num_uint Nat.of_uint Nat.of_uint_acc].
  try (rewrite !Nat.tail_mul_spec).
  nia.
Qed.
Lemma HLT63ssbX : 885710 < 1048576.
Proof.
  cbn [Nat.of_num_uint Nat.of_uint Nat.of_uint_acc].
  try (rewrite !Nat.tail_mul_spec).
  nia.
Qed.
Lemma D63ssbX : 60654542 / 1048576 = 57.
Proof. symmetry. exact (Nat.div_unique _ _ _ _ HLT63ssbX E63ssbX). Qed.
Lemma M63ssbX : 60654542 mod 1048576 = 885710.
Proof. symmetry. exact (Nat.mod_unique _ _ _ _ HLT63ssbX E63ssbX). Qed.
Lemma E63ssbY : 60654540 = 1048576 * 57 + 885708.
Proof.
  cbn [Nat.of_num_uint Nat.of_uint Nat.of_uint_acc].
  try (rewrite !Nat.tail_mul_spec).
  nia.
Qed.
Lemma HLT63ssbY : 885708 < 1048576.
Proof.
  cbn [Nat.of_num_uint Nat.of_uint Nat.of_uint_acc].
  try (rewrite !Nat.tail_mul_spec).
  nia.
Qed.
Lemma D63ssbY : 60654540 / 1048576 = 57.
Proof. symmetry. exact (Nat.div_unique _ _ _ _ HLT63ssbY E63ssbY). Qed.
Lemma M63ssbY : 60654540 mod 1048576 = 885708.
Proof. symmetry. exact (Nat.mod_unique _ _ _ _ HLT63ssbY E63ssbY). Qed.
Lemma E63ssb : 885708 + 2 = 885710.
Proof. apply Nat.eqb_eq; vm_compute; reflexivity. Qed.
Lemma NUM63ssb : 60654542 = S (S 60654540).
Proof.
  rewrite <- (ADD2S 60654540).
  rewrite (Nat.div_mod_eq 60654542 1048576) at 1.
  rewrite D63ssbX, M63ssbX.
  rewrite (Nat.div_mod_eq 60654540 1048576).
  rewrite D63ssbY, M63ssbY.
  rewrite <- Nat.add_assoc.
  rewrite (E63ssb).
  reflexivity.
Qed.
Lemma REP63b : forall w,
  (1, 1) :: (1, 2) :: (1, 2) :: repeat (1, 2) 60654540 ++ w
  = (1, 1) :: repeat (1, 2) 60654542 ++ w.
Proof. intro w. rewrite NUM63ssb. reflexivity. Qed.
Lemma NUM63tb1 : 9546949 = S (S (S 9546946)).
Proof.
  cbn [Nat.of_num_uint Nat.of_uint Nat.of_uint_acc].
  try (rewrite !Nat.tail_mul_spec).
  nia.
Qed.
Lemma NUM63tb2 : 4860546 = S 4860545.
Proof.
  cbn [Nat.of_num_uint Nat.of_uint Nat.of_uint_acc].
  try (rewrite !Nat.tail_mul_spec).
  nia.
Qed.
Lemma NUM63tb3 : 9546947 = S 9546946.
Proof.
  cbn [Nat.of_num_uint Nat.of_uint Nat.of_uint_acc].
  try (rewrite !Nat.tail_mul_spec).
  nia.
Qed.
