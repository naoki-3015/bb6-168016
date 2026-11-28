(* ================================================================= *)
(* Phase 63 (companion): div/mod values, file Grind31c10.  At ~1.2 x 10^9      *)
(* scale no evaluated comparison survives (the abstract          *)
(* of_num_uint literals materialise as ~4 GB unary chains and    *)
(* div/mod recurse on the value), so each value is certified     *)
(* by an unevaluated Horner/nia equation E : expr = k * q + r    *)
(* plus r < k, and the div/mod values follow by the uniqueness   *)
(* lemmas.  X = Y then follows from the components through       *)
(* Nat.div_mod_eq (the Phase 60 pattern, evaluation-free).       *)
(* ================================================================= *)

Require Import Arith Lia.

Lemma E63jX : 1191297119 = 1048576 * 1136 + 114783.
Proof.
  cbn [Nat.of_num_uint Nat.of_uint Nat.of_uint_acc].
  try (rewrite !Nat.tail_mul_spec).
  nia.
Qed.

Lemma HLT63jX : 114783 < 1048576.
Proof.
  cbn [Nat.of_num_uint Nat.of_uint Nat.of_uint_acc].
  try (rewrite !Nat.tail_mul_spec).
  nia.
Qed.

Lemma D63jX : (1191297119) / 1048576 = 1136.
Proof. symmetry. exact (Nat.div_unique _ _ _ _ HLT63jX E63jX). Qed.

Lemma M63jX : (1191297119) mod 1048576 = 114783.
Proof. symmetry. exact (Nat.mod_unique _ _ _ _ HLT63jX E63jX). Qed.

Lemma E63jY : S (S (1191297119 - 1 - 1)) = 1048576 * 1136 + 114783.
Proof.
  cbn [Nat.of_num_uint Nat.of_uint Nat.of_uint_acc].
  try (rewrite !Nat.tail_mul_spec).
  nia.
Qed.

Lemma HLT63jY : 114783 < 1048576.
Proof.
  cbn [Nat.of_num_uint Nat.of_uint Nat.of_uint_acc].
  try (rewrite !Nat.tail_mul_spec).
  nia.
Qed.

Lemma D63jY : (S (S (1191297119 - 1 - 1))) / 1048576 = 1136.
Proof. symmetry. exact (Nat.div_unique _ _ _ _ HLT63jY E63jY). Qed.

Lemma M63jY : (S (S (1191297119 - 1 - 1))) mod 1048576 = 114783.
Proof. symmetry. exact (Nat.mod_unique _ _ _ _ HLT63jY E63jY). Qed.
