(* ================================================================= *)
(* Phase 61 (companion): symbolic helpers for the ~2.7 x 10^8      *)
(* arithmetic (the (V - 1)-form S-identity, the +2 S-form, the     *)
(* div/mod recombination step) and the closed leb premises of      *)
(* the tail, proved by the Horner/nia route (cbn digit-fold        *)
(* unfolding + tail_mul_spec + nia; evaluated comparisons and      *)
(* plain lia on the abstract of_num_uint literals both fail at     *)
(* this scale).                                                    *)
(* ================================================================= *)

Require Import Arith Lia.

(* V = S (V - 1) for V >= 1, symbolically (the NUM60e' route).     *)
Lemma S_sub_1_61 : forall V, 1 <= V -> V = S (V - 1).
Proof.
  intros V HV. rewrite Nat.sub_1_r. symmetry. apply Nat.succ_pred_pos.
  apply Nat.neq_0_lt_0. intros Hc. rewrite Hc in HV. simpl in HV.
  inversion HV.
Qed.

Lemma ADD2S : forall m, m + 2 = S (S m).
Proof. intro m. induction m; simpl; congruence. Qed.

(* div/mod recombination with a +2 carry on the remainder side:    *)
(* if r2 + 2 = k + r1 then k*(q+1) + r1 = (k*q + r2) + 2.          *)
Lemma R61ssB : forall k q r1 r2, r2 + 2 = k + r1 ->
  k * (q + 1) + r1 = (k * q + r2) + 2.
Proof. intros k q r1 r2 H. lia. Qed.

(* X = Y from the div/mod components at k = 2^20.                  *)
Lemma DIVEQ : forall X Y,
  X / 1048576 = Y / 1048576 -> X mod 1048576 = Y mod 1048576 ->
  X = Y.
Proof.
  intros X Y HD HM.
  rewrite (Nat.div_mod_eq X 1048576) at 1.
  rewrite (Nat.div_mod_eq Y 1048576) at 1.
  rewrite HD, HM. reflexivity.
Qed.

(* The DIPGRIND premise of TOP61_TO_TOP15.                         *)
Lemma S61a1 : 1 <= 135985236.
Proof.
  cbn [Nat.of_num_uint Nat.of_uint Nat.of_uint_acc].
  try (rewrite !Nat.tail_mul_spec).
  nia.
Qed.

(* The sTUP premise at the TOP15 state (2 <= shuttle).             *)
Lemma S61h0 : 2 <= 271970479.
Proof.
  cbn [Nat.of_num_uint Nat.of_uint Nat.of_uint_acc].
  try (rewrite !Nat.tail_mul_spec).
  nia.
Qed.

(* The hGRIND_even premises at the TOP15 state.                    *)
Lemma S61g1 : 1 <= 135985237.
Proof.
  cbn [Nat.of_num_uint Nat.of_uint Nat.of_uint_acc].
  try (rewrite !Nat.tail_mul_spec).
  nia.
Qed.
Lemma S61g2 : 135985237 <= 147491795 - 1.
Proof.
  cbn [Nat.of_num_uint Nat.of_uint Nat.of_uint_acc].
  try (rewrite !Nat.tail_mul_spec).
  nia.
Qed.
