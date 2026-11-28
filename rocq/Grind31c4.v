(* ================================================================= *)
(* Phase 63 (companion): div/mod values, file Grind31c4.  At ~1.2 x 10^9      *)
(* scale no evaluated comparison survives (the abstract          *)
(* of_num_uint literals materialise as ~4 GB unary chains and    *)
(* div/mod recurse on the value), so each value is certified     *)
(* by an unevaluated Horner/nia equation E : expr = k * q + r    *)
(* plus r < k, and the div/mod values follow by the uniqueness   *)
(* lemmas.  X = Y then follows from the components through       *)
(* Nat.div_mod_eq (the Phase 60 pattern, evaluation-free).       *)
(* ================================================================= *)

Require Import Arith Lia.

Lemma E63hX : 1191297118 = 1048576 * 1136 + 114782.
Proof.
  cbn [Nat.of_num_uint Nat.of_uint Nat.of_uint_acc].
  try (rewrite !Nat.tail_mul_spec).
  nia.
Qed.

Lemma HLT63hX : 114782 < 1048576.
Proof.
  cbn [Nat.of_num_uint Nat.of_uint Nat.of_uint_acc].
  try (rewrite !Nat.tail_mul_spec).
  nia.
Qed.

Lemma D63hX : (1191297118) / 1048576 = 1136.
Proof. symmetry. exact (Nat.div_unique _ _ _ _ HLT63hX E63hX). Qed.

Lemma M63hX : (1191297118) mod 1048576 = 114782.
Proof. symmetry. exact (Nat.mod_unique _ _ _ _ HLT63hX E63hX). Qed.

Lemma E63hY : (1191297119 - 1) = 1048576 * 1136 + 114782.
Proof.
  cbn [Nat.of_num_uint Nat.of_uint Nat.of_uint_acc].
  try (rewrite !Nat.tail_mul_spec).
  nia.
Qed.

Lemma HLT63hY : 114782 < 1048576.
Proof.
  cbn [Nat.of_num_uint Nat.of_uint Nat.of_uint_acc].
  try (rewrite !Nat.tail_mul_spec).
  nia.
Qed.

Lemma D63hY : ((1191297119 - 1)) / 1048576 = 1136.
Proof. symmetry. exact (Nat.div_unique _ _ _ _ HLT63hY E63hY). Qed.

Lemma M63hY : ((1191297119 - 1)) mod 1048576 = 114782.
Proof. symmetry. exact (Nat.mod_unique _ _ _ _ HLT63hY E63hY). Qed.
