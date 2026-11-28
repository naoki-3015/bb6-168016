Require Import List Arith Lia.
Require Import Grind29h.

(* Factored list identities for the PX2A steps of           *)
(* CASCADE61 whose produced (1, 2)s merge into a spine      *)
(* repeat of length > 175000 (auto-detected by gen61.py).   *)
Lemma E61ssaX : 135985238 = 1048576 * 129 + 718934.
Proof.
  cbn [Nat.of_num_uint Nat.of_uint Nat.of_uint_acc].
  try (rewrite !Nat.tail_mul_spec).
  nia.
Qed.
Lemma HLT61ssaX : 718934 < 1048576.
Proof.
  cbn [Nat.of_num_uint Nat.of_uint Nat.of_uint_acc].
  try (rewrite !Nat.tail_mul_spec).
  nia.
Qed.
Lemma D61ssaX : 135985238 / 1048576 = 129.
Proof. symmetry. exact (Nat.div_unique _ _ _ _ HLT61ssaX E61ssaX). Qed.
Lemma M61ssaX : 135985238 mod 1048576 = 718934.
Proof. symmetry. exact (Nat.mod_unique _ _ _ _ HLT61ssaX E61ssaX). Qed.
Lemma E61ssaY : 135985236 = 1048576 * 129 + 718932.
Proof.
  cbn [Nat.of_num_uint Nat.of_uint Nat.of_uint_acc].
  try (rewrite !Nat.tail_mul_spec).
  nia.
Qed.
Lemma HLT61ssaY : 718932 < 1048576.
Proof.
  cbn [Nat.of_num_uint Nat.of_uint Nat.of_uint_acc].
  try (rewrite !Nat.tail_mul_spec).
  nia.
Qed.
Lemma D61ssaY : 135985236 / 1048576 = 129.
Proof. symmetry. exact (Nat.div_unique _ _ _ _ HLT61ssaY E61ssaY). Qed.
Lemma M61ssaY : 135985236 mod 1048576 = 718932.
Proof. symmetry. exact (Nat.mod_unique _ _ _ _ HLT61ssaY E61ssaY). Qed.
Lemma E61ssa : 718932 + 2 = 718934.
Proof. apply Nat.eqb_eq; vm_compute; reflexivity. Qed.
Lemma NUM61ssa : 135985238 = S (S 135985236).
Proof.
  rewrite <- (ADD2S 135985236).
  rewrite (Nat.div_mod_eq 135985238 1048576) at 1.
  rewrite D61ssaX, M61ssaX.
  rewrite (Nat.div_mod_eq 135985236 1048576).
  rewrite D61ssaY, M61ssaY.
  rewrite <- Nat.add_assoc.
  rewrite (E61ssa).
  reflexivity.
Qed.
Lemma REP61a : forall w,
  (1, 1) :: (1, 2) :: (1, 2) :: repeat (1, 2) 135985236 ++ w
  = (1, 1) :: repeat (1, 2) 135985238 ++ w.
Proof. intro w. rewrite NUM61ssa. reflexivity. Qed.
Lemma NUM61ta1 : 74737818 = S (S (S 74737815)).
Proof.
  cbn [Nat.of_num_uint Nat.of_uint Nat.of_uint_acc].
  try (rewrite !Nat.tail_mul_spec).
  nia.
Qed.
Lemma NUM61ta2 : 10126538 = S 10126537.
Proof.
  cbn [Nat.of_num_uint Nat.of_uint Nat.of_uint_acc].
  try (rewrite !Nat.tail_mul_spec).
  nia.
Qed.
Lemma NUM61ta3 : 74737816 = S 74737815.
Proof.
  cbn [Nat.of_num_uint Nat.of_uint Nat.of_uint_acc].
  try (rewrite !Nat.tail_mul_spec).
  nia.
Qed.
Lemma NUM61ssb : 10126538 = S (S 10126536).
Proof.
  cbn [Nat.of_num_uint Nat.of_uint Nat.of_uint_acc].
  try (rewrite !Nat.tail_mul_spec).
  nia.
Qed.
Lemma REP61b : forall w,
  (1, 1) :: (1, 2) :: (1, 2) :: repeat (1, 2) 10126536 ++ w
  = (1, 1) :: repeat (1, 2) 10126538 ++ w.
Proof. intro w. rewrite NUM61ssb. reflexivity. Qed.
Lemma NUM61tb1 : 1236011 = S (S (S 1236008)).
Proof.
  cbn [Nat.of_num_uint Nat.of_uint Nat.of_uint_acc].
  try (rewrite !Nat.tail_mul_spec).
  nia.
Qed.
Lemma NUM61tb2 : 698173 = S 698172.
Proof.
  cbn [Nat.of_num_uint Nat.of_uint Nat.of_uint_acc].
  try (rewrite !Nat.tail_mul_spec).
  nia.
Qed.
Lemma NUM61tb3 : 1236009 = S 1236008.
Proof.
  cbn [Nat.of_num_uint Nat.of_uint Nat.of_uint_acc].
  try (rewrite !Nat.tail_mul_spec).
  nia.
Qed.
Lemma NUM61ssc : 21489090 = S (S 21489088).
Proof.
  cbn [Nat.of_num_uint Nat.of_uint Nat.of_uint_acc].
  try (rewrite !Nat.tail_mul_spec).
  nia.
Qed.
Lemma REP61c : forall w,
  (1, 1) :: (1, 2) :: (1, 2) :: repeat (1, 2) 21489088 ++ w
  = (1, 1) :: repeat (1, 2) 21489090 ++ w.
Proof. intro w. rewrite NUM61ssc. reflexivity. Qed.
Lemma NUM61tc1 : 10824711 = S (S (S 10824708)).
Proof.
  cbn [Nat.of_num_uint Nat.of_uint Nat.of_uint_acc].
  try (rewrite !Nat.tail_mul_spec).
  nia.
Qed.
Lemma NUM61tc2 : 177445 = S 177444.
Proof.
  cbn [Nat.of_num_uint Nat.of_uint Nat.of_uint_acc].
  try (rewrite !Nat.tail_mul_spec).
  nia.
Qed.
Lemma NUM61tc3 : 10824709 = S 10824708.
Proof.
  cbn [Nat.of_num_uint Nat.of_uint Nat.of_uint_acc].
  try (rewrite !Nat.tail_mul_spec).
  nia.
Qed.
Lemma NUM61ssd : 177445 = S (S 177443).
Proof.
  cbn [Nat.of_num_uint Nat.of_uint Nat.of_uint_acc].
  try (rewrite !Nat.tail_mul_spec).
  nia.
Qed.
Lemma REP61d : forall w,
  (1, 1) :: (1, 2) :: (1, 2) :: repeat (1, 2) 177443 ++ w
  = (1, 1) :: repeat (1, 2) 177445 ++ w.
Proof. intro w. rewrite NUM61ssd. reflexivity. Qed.
Lemma NUM61td1 : 95640 = S (S (S 95637)).
Proof.
  cbn [Nat.of_num_uint Nat.of_uint Nat.of_uint_acc].
  try (rewrite !Nat.tail_mul_spec).
  nia.
Qed.
Lemma NUM61td2 : 10129 = S 10128.
Proof.
  cbn [Nat.of_num_uint Nat.of_uint Nat.of_uint_acc].
  try (rewrite !Nat.tail_mul_spec).
  nia.
Qed.
Lemma NUM61td3 : 95638 = S 95637.
Proof.
  cbn [Nat.of_num_uint Nat.of_uint Nat.of_uint_acc].
  try (rewrite !Nat.tail_mul_spec).
  nia.
Qed.
Lemma NUM61sse : 354894 = S (S 354892).
Proof.
  cbn [Nat.of_num_uint Nat.of_uint Nat.of_uint_acc].
  try (rewrite !Nat.tail_mul_spec).
  nia.
Qed.
Lemma REP61e : forall w,
  (1, 1) :: (1, 2) :: (1, 2) :: repeat (1, 2) 354892 ++ w
  = (1, 1) :: repeat (1, 2) 354894 ++ w.
Proof. intro w. rewrite NUM61sse. reflexivity. Qed.
Lemma NUM61te1 : 210646 = S (S (S 210643)).
Proof.
  cbn [Nat.of_num_uint Nat.of_uint Nat.of_uint_acc].
  try (rewrite !Nat.tail_mul_spec).
  nia.
Qed.
Lemma NUM61te2 : 45309 = S 45308.
Proof.
  cbn [Nat.of_num_uint Nat.of_uint Nat.of_uint_acc].
  try (rewrite !Nat.tail_mul_spec).
  nia.
Qed.
Lemma NUM61te3 : 210644 = S 210643.
Proof.
  cbn [Nat.of_num_uint Nat.of_uint Nat.of_uint_acc].
  try (rewrite !Nat.tail_mul_spec).
  nia.
Qed.
Lemma NUM61ssf : 709792 = S (S 709790).
Proof.
  cbn [Nat.of_num_uint Nat.of_uint Nat.of_uint_acc].
  try (rewrite !Nat.tail_mul_spec).
  nia.
Qed.
Lemma REP61f : forall w,
  (1, 1) :: (1, 2) :: (1, 2) :: repeat (1, 2) 709790 ++ w
  = (1, 1) :: repeat (1, 2) 709792 ++ w.
Proof. intro w. rewrite NUM61ssf. reflexivity. Qed.
Lemma NUM61tf1 : 474919 = S (S (S 474916)).
Proof.
  cbn [Nat.of_num_uint Nat.of_uint Nat.of_uint_acc].
  try (rewrite !Nat.tail_mul_spec).
  nia.
Qed.
Lemma NUM61tf2 : 90621 = S 90620.
Proof.
  cbn [Nat.of_num_uint Nat.of_uint Nat.of_uint_acc].
  try (rewrite !Nat.tail_mul_spec).
  nia.
Qed.
Lemma NUM61tf3 : 474917 = S 474916.
Proof.
  cbn [Nat.of_num_uint Nat.of_uint Nat.of_uint_acc].
  try (rewrite !Nat.tail_mul_spec).
  nia.
Qed.
Lemma NUM61ssg : 1713262 = S (S 1713260).
Proof.
  cbn [Nat.of_num_uint Nat.of_uint Nat.of_uint_acc].
  try (rewrite !Nat.tail_mul_spec).
  nia.
Qed.
Lemma REP61g : forall w,
  (1, 1) :: (1, 2) :: (1, 2) :: repeat (1, 2) 1713260 ++ w
  = (1, 1) :: repeat (1, 2) 1713262 ++ w.
Proof. intro w. rewrite NUM61ssg. reflexivity. Qed.
Lemma NUM61tg1 : 891038 = S (S (S 891035)).
Proof.
  cbn [Nat.of_num_uint Nat.of_uint Nat.of_uint_acc].
  try (rewrite !Nat.tail_mul_spec).
  nia.
Qed.
Lemma NUM61tg2 : 120150 = S 120149.
Proof.
  cbn [Nat.of_num_uint Nat.of_uint Nat.of_uint_acc].
  try (rewrite !Nat.tail_mul_spec).
  nia.
Qed.
Lemma NUM61tg3 : 891036 = S 891035.
Proof.
  cbn [Nat.of_num_uint Nat.of_uint Nat.of_uint_acc].
  try (rewrite !Nat.tail_mul_spec).
  nia.
Qed.
Lemma NUM61ssh : 264042 = S (S 264040).
Proof.
  cbn [Nat.of_num_uint Nat.of_uint Nat.of_uint_acc].
  try (rewrite !Nat.tail_mul_spec).
  nia.
Qed.
Lemma REP61h : forall w,
  (1, 1) :: (1, 2) :: (1, 2) :: repeat (1, 2) 264040 ++ w
  = (1, 1) :: repeat (1, 2) 264042 ++ w.
Proof. intro w. rewrite NUM61ssh. reflexivity. Qed.
Lemma NUM61th1 : 136677 = S (S (S 136674)).
Proof.
  cbn [Nat.of_num_uint Nat.of_uint Nat.of_uint_acc].
  try (rewrite !Nat.tail_mul_spec).
  nia.
Qed.
Lemma NUM61th2 : 2607 = S 2606.
Proof.
  cbn [Nat.of_num_uint Nat.of_uint Nat.of_uint_acc].
  try (rewrite !Nat.tail_mul_spec).
  nia.
Qed.
Lemma NUM61th3 : 136675 = S 136674.
Proof.
  cbn [Nat.of_num_uint Nat.of_uint Nat.of_uint_acc].
  try (rewrite !Nat.tail_mul_spec).
  nia.
Qed.
