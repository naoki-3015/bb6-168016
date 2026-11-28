(* ================================================================= *)
(* Phase 63 (companion): div/mod values, file Grind31c6.  At ~1.2 x 10^9      *)
(* scale no evaluated comparison survives (the abstract          *)
(* of_num_uint literals materialise as ~4 GB unary chains and    *)
(* div/mod recurse on the value), so each value is certified     *)
(* by an unevaluated Horner/nia equation E : expr = k * q + r    *)
(* plus r < k, and the div/mod values follow by the uniqueness   *)
(* lemmas.  X = Y then follows from the components through       *)
(* Nat.div_mod_eq (the Phase 60 pattern, evaluation-free).       *)
(* ================================================================= *)

Require Import Arith Lia.

Lemma E63eX : 1191297119 = 1048576 * 1136 + 114783.
Proof.
  cbn [Nat.of_num_uint Nat.of_uint Nat.of_uint_acc].
  try (rewrite !Nat.tail_mul_spec).
  nia.
Qed.

Lemma HLT63eX : 114783 < 1048576.
Proof.
  cbn [Nat.of_num_uint Nat.of_uint Nat.of_uint_acc].
  try (rewrite !Nat.tail_mul_spec).
  nia.
Qed.

Lemma D63eX : (1191297119) / 1048576 = 1136.
Proof. symmetry. exact (Nat.div_unique _ _ _ _ HLT63eX E63eX). Qed.

Lemma M63eX : (1191297119) mod 1048576 = 114783.
Proof. symmetry. exact (Nat.mod_unique _ _ _ _ HLT63eX E63eX). Qed.

Lemma E63eY : S (1191297119 - 1) = 1048576 * 1136 + 114783.
Proof.
  cbn [Nat.of_num_uint Nat.of_uint Nat.of_uint_acc].
  try (rewrite !Nat.tail_mul_spec).
  nia.
Qed.

Lemma HLT63eY : 114783 < 1048576.
Proof.
  cbn [Nat.of_num_uint Nat.of_uint Nat.of_uint_acc].
  try (rewrite !Nat.tail_mul_spec).
  nia.
Qed.

Lemma D63eY : (S (1191297119 - 1)) / 1048576 = 1136.
Proof. symmetry. exact (Nat.div_unique _ _ _ _ HLT63eY E63eY). Qed.

Lemma M63eY : (S (1191297119 - 1)) mod 1048576 = 114783.
Proof. symmetry. exact (Nat.mod_unique _ _ _ _ HLT63eY E63eY). Qed.
