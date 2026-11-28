Require Import List Arith Lia.
Require Import Grind30h.

(* Factored list identities for the PX2A steps of           *)
(* CASCADE62 whose produced (1, 2)s merge into a spine      *)
(* repeat of length > 175000 (auto-detected by gen62.py).   *)
Lemma E62ssaX : 271970480 = 1048576 * 259 + 389296.
Proof.
  cbn [Nat.of_num_uint Nat.of_uint Nat.of_uint_acc].
  try (rewrite !Nat.tail_mul_spec).
  nia.
Qed.
Lemma HLT62ssaX : 389296 < 1048576.
Proof.
  cbn [Nat.of_num_uint Nat.of_uint Nat.of_uint_acc].
  try (rewrite !Nat.tail_mul_spec).
  nia.
Qed.
Lemma D62ssaX : 271970480 / 1048576 = 259.
Proof. symmetry. exact (Nat.div_unique _ _ _ _ HLT62ssaX E62ssaX). Qed.
Lemma M62ssaX : 271970480 mod 1048576 = 389296.
Proof. symmetry. exact (Nat.mod_unique _ _ _ _ HLT62ssaX E62ssaX). Qed.
Lemma E62ssaY : 271970478 = 1048576 * 259 + 389294.
Proof.
  cbn [Nat.of_num_uint Nat.of_uint Nat.of_uint_acc].
  try (rewrite !Nat.tail_mul_spec).
  nia.
Qed.
Lemma HLT62ssaY : 389294 < 1048576.
Proof.
  cbn [Nat.of_num_uint Nat.of_uint Nat.of_uint_acc].
  try (rewrite !Nat.tail_mul_spec).
  nia.
Qed.
Lemma D62ssaY : 271970478 / 1048576 = 259.
Proof. symmetry. exact (Nat.div_unique _ _ _ _ HLT62ssaY E62ssaY). Qed.
Lemma M62ssaY : 271970478 mod 1048576 = 389294.
Proof. symmetry. exact (Nat.mod_unique _ _ _ _ HLT62ssaY E62ssaY). Qed.
Lemma E62ssa : 389294 + 2 = 389296.
Proof. apply Nat.eqb_eq; vm_compute; reflexivity. Qed.
Lemma NUM62ssa : 271970480 = S (S 271970478).
Proof.
  rewrite <- (ADD2S 271970478).
  rewrite (Nat.div_mod_eq 271970480 1048576) at 1.
  rewrite D62ssaX, M62ssaX.
  rewrite (Nat.div_mod_eq 271970478 1048576).
  rewrite D62ssaY, M62ssaY.
  rewrite <- Nat.add_assoc.
  rewrite (E62ssa).
  reflexivity.
Qed.
Lemma REP62a : forall w,
  (1, 1) :: (1, 2) :: (1, 2) :: repeat (1, 2) 271970478 ++ w
  = (1, 1) :: repeat (1, 2) 271970480 ++ w.
Proof. intro w. rewrite NUM62ssa. reflexivity. Qed.
Lemma NUM62ta1 : 147491795 = S (S (S 147491792)).
Proof.
  cbn [Nat.of_num_uint Nat.of_uint Nat.of_uint_acc].
  try (rewrite !Nat.tail_mul_spec).
  nia.
Qed.
Lemma NUM62ta2 : 47892099 = S 47892098.
Proof.
  cbn [Nat.of_num_uint Nat.of_uint Nat.of_uint_acc].
  try (rewrite !Nat.tail_mul_spec).
  nia.
Qed.
Lemma NUM62ta3 : 147491793 = S 147491792.
Proof.
  cbn [Nat.of_num_uint Nat.of_uint Nat.of_uint_acc].
  try (rewrite !Nat.tail_mul_spec).
  nia.
Qed.
Lemma E62ssbX : 47892099 = 1048576 * 45 + 706179.
Proof.
  cbn [Nat.of_num_uint Nat.of_uint Nat.of_uint_acc].
  try (rewrite !Nat.tail_mul_spec).
  nia.
Qed.
Lemma HLT62ssbX : 706179 < 1048576.
Proof.
  cbn [Nat.of_num_uint Nat.of_uint Nat.of_uint_acc].
  try (rewrite !Nat.tail_mul_spec).
  nia.
Qed.
Lemma D62ssbX : 47892099 / 1048576 = 45.
Proof. symmetry. exact (Nat.div_unique _ _ _ _ HLT62ssbX E62ssbX). Qed.
Lemma M62ssbX : 47892099 mod 1048576 = 706179.
Proof. symmetry. exact (Nat.mod_unique _ _ _ _ HLT62ssbX E62ssbX). Qed.
Lemma E62ssbY : 47892097 = 1048576 * 45 + 706177.
Proof.
  cbn [Nat.of_num_uint Nat.of_uint Nat.of_uint_acc].
  try (rewrite !Nat.tail_mul_spec).
  nia.
Qed.
Lemma HLT62ssbY : 706177 < 1048576.
Proof.
  cbn [Nat.of_num_uint Nat.of_uint Nat.of_uint_acc].
  try (rewrite !Nat.tail_mul_spec).
  nia.
Qed.
Lemma D62ssbY : 47892097 / 1048576 = 45.
Proof. symmetry. exact (Nat.div_unique _ _ _ _ HLT62ssbY E62ssbY). Qed.
Lemma M62ssbY : 47892097 mod 1048576 = 706177.
Proof. symmetry. exact (Nat.mod_unique _ _ _ _ HLT62ssbY E62ssbY). Qed.
Lemma E62ssb : 706177 + 2 = 706179.
Proof. apply Nat.eqb_eq; vm_compute; reflexivity. Qed.
Lemma NUM62ssb : 47892099 = S (S 47892097).
Proof.
  rewrite <- (ADD2S 47892097).
  rewrite (Nat.div_mod_eq 47892099 1048576) at 1.
  rewrite D62ssbX, M62ssbX.
  rewrite (Nat.div_mod_eq 47892097 1048576).
  rewrite D62ssbY, M62ssbY.
  rewrite <- Nat.add_assoc.
  rewrite (E62ssb).
  reflexivity.
Qed.
Lemma REP62b : forall w,
  (1, 1) :: (1, 2) :: (1, 2) :: repeat (1, 2) 47892097 ++ w
  = (1, 1) :: repeat (1, 2) 47892099 ++ w.
Proof. intro w. rewrite NUM62ssb. reflexivity. Qed.
Lemma NUM62tb1 : 24915618 = S (S (S 24915615)).
Proof.
  cbn [Nat.of_num_uint Nat.of_uint Nat.of_uint_acc].
  try (rewrite !Nat.tail_mul_spec).
  nia.
Qed.
Lemma NUM62tb2 : 1835911 = S 1835910.
Proof.
  cbn [Nat.of_num_uint Nat.of_uint Nat.of_uint_acc].
  try (rewrite !Nat.tail_mul_spec).
  nia.
Qed.
Lemma NUM62tb3 : 24915616 = S 24915615.
Proof.
  cbn [Nat.of_num_uint Nat.of_uint Nat.of_uint_acc].
  try (rewrite !Nat.tail_mul_spec).
  nia.
Qed.
Lemma NUM62ssc : 1835911 = S (S 1835909).
Proof.
  cbn [Nat.of_num_uint Nat.of_uint Nat.of_uint_acc].
  try (rewrite !Nat.tail_mul_spec).
  nia.
Qed.
Lemma REP62c : forall w,
  (1, 1) :: (1, 2) :: (1, 2) :: repeat (1, 2) 1835909 ++ w
  = (1, 1) :: repeat (1, 2) 1835911 ++ w.
Proof. intro w. rewrite NUM62ssc. reflexivity. Qed.
Lemma NUM62tc1 : 568849 = S (S (S 568846)).
Proof.
  cbn [Nat.of_num_uint Nat.of_uint Nat.of_uint_acc].
  try (rewrite !Nat.tail_mul_spec).
  nia.
Qed.
Lemma NUM62tc2 : 317482 = S 317481.
Proof.
  cbn [Nat.of_num_uint Nat.of_uint Nat.of_uint_acc].
  try (rewrite !Nat.tail_mul_spec).
  nia.
Qed.
Lemma NUM62tc3 : 568847 = S 568846.
Proof.
  cbn [Nat.of_num_uint Nat.of_uint Nat.of_uint_acc].
  try (rewrite !Nat.tail_mul_spec).
  nia.
Qed.
Lemma NUM62ssd : 4240674 = S (S 4240672).
Proof.
  cbn [Nat.of_num_uint Nat.of_uint Nat.of_uint_acc].
  try (rewrite !Nat.tail_mul_spec).
  nia.
Qed.
Lemma REP62d : forall w,
  (1, 1) :: (1, 2) :: (1, 2) :: repeat (1, 2) 4240672 ++ w
  = (1, 1) :: repeat (1, 2) 4240674 ++ w.
Proof. intro w. rewrite NUM62ssd. reflexivity. Qed.
Lemma NUM62td1 : 2153393 = S (S (S 2153390)).
Proof.
  cbn [Nat.of_num_uint Nat.of_uint Nat.of_uint_acc].
  try (rewrite !Nat.tail_mul_spec).
  nia.
Qed.
Lemma NUM62td2 : 29175 = S 29174.
Proof.
  cbn [Nat.of_num_uint Nat.of_uint Nat.of_uint_acc].
  try (rewrite !Nat.tail_mul_spec).
  nia.
Qed.
Lemma NUM62td3 : 2153391 = S 2153390.
Proof.
  cbn [Nat.of_num_uint Nat.of_uint Nat.of_uint_acc].
  try (rewrite !Nat.tail_mul_spec).
  nia.
Qed.
Lemma NUM62sse : 309934 = S (S 309932).
Proof.
  cbn [Nat.of_num_uint Nat.of_uint Nat.of_uint_acc].
  try (rewrite !Nat.tail_mul_spec).
  nia.
Qed.
Lemma REP62e : forall w,
  (1, 1) :: (1, 2) :: (1, 2) :: repeat (1, 2) 309932 ++ w
  = (1, 1) :: repeat (1, 2) 309934 ++ w.
Proof. intro w. rewrite NUM62sse. reflexivity. Qed.
Lemma NUM62te1 : 173750 = S (S (S 173747)).
Proof.
  cbn [Nat.of_num_uint Nat.of_uint Nat.of_uint_acc].
  try (rewrite !Nat.tail_mul_spec).
  nia.
Qed.
Lemma NUM62te2 : 20370 = S 20369.
Proof.
  cbn [Nat.of_num_uint Nat.of_uint Nat.of_uint_acc].
  try (rewrite !Nat.tail_mul_spec).
  nia.
Qed.
Lemma NUM62te3 : 173748 = S 173747.
Proof.
  cbn [Nat.of_num_uint Nat.of_uint Nat.of_uint_acc].
  try (rewrite !Nat.tail_mul_spec).
  nia.
Qed.
