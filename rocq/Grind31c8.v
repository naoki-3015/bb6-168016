(* ================================================================= *)
(* Phase 63 (companion): div/mod values, file Grind31c8.  At ~1.2 x 10^9      *)
(* scale no evaluated comparison survives (the abstract          *)
(* of_num_uint literals materialise as ~4 GB unary chains and    *)
(* div/mod recurse on the value), so each value is certified     *)
(* by an unevaluated Horner/nia equation E : expr = k * q + r    *)
(* plus r < k, and the div/mod values follow by the uniqueness   *)
(* lemmas.  X = Y then follows from the components through       *)
(* Nat.div_mod_eq (the Phase 60 pattern, evaluation-free).       *)
(* ================================================================= *)

Require Import Arith Lia.

Lemma E63gX : 842094154 = 1048576 * 803 + 87626.
Proof.
  cbn [Nat.of_num_uint Nat.of_uint Nat.of_uint_acc].
  try (rewrite !Nat.tail_mul_spec).
  nia.
Qed.

Lemma HLT63gX : 87626 < 1048576.
Proof.
  cbn [Nat.of_num_uint Nat.of_uint Nat.of_uint_acc].
  try (rewrite !Nat.tail_mul_spec).
  nia.
Qed.

Lemma D63gX : (842094154) / 1048576 = 803.
Proof. symmetry. exact (Nat.div_unique _ _ _ _ HLT63gX E63gX). Qed.

Lemma M63gX : (842094154) mod 1048576 = 87626.
Proof. symmetry. exact (Nat.mod_unique _ _ _ _ HLT63gX E63gX). Qed.

Lemma E63gY : S 842094153 = 1048576 * 803 + 87626.
Proof.
  cbn [Nat.of_num_uint Nat.of_uint Nat.of_uint_acc].
  try (rewrite !Nat.tail_mul_spec).
  nia.
Qed.

Lemma HLT63gY : 87626 < 1048576.
Proof.
  cbn [Nat.of_num_uint Nat.of_uint Nat.of_uint_acc].
  try (rewrite !Nat.tail_mul_spec).
  nia.
Qed.

Lemma D63gY : (S 842094153) / 1048576 = 803.
Proof. symmetry. exact (Nat.div_unique _ _ _ _ HLT63gY E63gY). Qed.

Lemma M63gY : (S 842094153) mod 1048576 = 87626.
Proof. symmetry. exact (Nat.mod_unique _ _ _ _ HLT63gY E63gY). Qed.
