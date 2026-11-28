(* ================================================================= *)
(* Phase 61 (companion): div/mod values, file Grind29c8.  At ~2.7 x 10^8      *)
(* scale no evaluated comparison survives (the abstract          *)
(* of_num_uint literals materialise as ~4 GB unary chains and    *)
(* div/mod recurse on the value), so each value is certified     *)
(* by an unevaluated Horner/nia equation E : expr = k * q + r    *)
(* plus r < k, and the div/mod values follow by the uniqueness   *)
(* lemmas.  X = Y then follows from the components through       *)
(* Nat.div_mod_eq (the Phase 60 pattern, evaluation-free).       *)
(* ================================================================= *)

Require Import Arith Lia.

Lemma E61gX : 147491796 = 1048576 * 140 + 691156.
Proof.
  cbn [Nat.of_num_uint Nat.of_uint Nat.of_uint_acc].
  try (rewrite !Nat.tail_mul_spec).
  nia.
Qed.

Lemma HLT61gX : 691156 < 1048576.
Proof.
  cbn [Nat.of_num_uint Nat.of_uint Nat.of_uint_acc].
  try (rewrite !Nat.tail_mul_spec).
  nia.
Qed.

Lemma D61gX : (147491796) / 1048576 = 140.
Proof. symmetry. exact (Nat.div_unique _ _ _ _ HLT61gX E61gX). Qed.

Lemma M61gX : (147491796) mod 1048576 = 691156.
Proof. symmetry. exact (Nat.mod_unique _ _ _ _ HLT61gX E61gX). Qed.

Lemma E61gY : S 147491795 = 1048576 * 140 + 691156.
Proof.
  cbn [Nat.of_num_uint Nat.of_uint Nat.of_uint_acc].
  try (rewrite !Nat.tail_mul_spec).
  nia.
Qed.

Lemma HLT61gY : 691156 < 1048576.
Proof.
  cbn [Nat.of_num_uint Nat.of_uint Nat.of_uint_acc].
  try (rewrite !Nat.tail_mul_spec).
  nia.
Qed.

Lemma D61gY : (S 147491795) / 1048576 = 140.
Proof. symmetry. exact (Nat.div_unique _ _ _ _ HLT61gY E61gY). Qed.

Lemma M61gY : (S 147491795) mod 1048576 = 691156.
Proof. symmetry. exact (Nat.mod_unique _ _ _ _ HLT61gY E61gY). Qed.
