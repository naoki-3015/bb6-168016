(* ================================================================= *)
(* Phase 63 (companion): div/mod values, file Grind31c7.  At ~1.2 x 10^9      *)
(* scale no evaluated comparison survives (the abstract          *)
(* of_num_uint literals materialise as ~4 GB unary chains and    *)
(* div/mod recurse on the value), so each value is certified     *)
(* by an unevaluated Horner/nia equation E : expr = k * q + r    *)
(* plus r < k, and the div/mod values follow by the uniqueness   *)
(* lemmas.  X = Y then follows from the components through       *)
(* Nat.div_mod_eq (the Phase 60 pattern, evaluation-free).       *)
(* ================================================================= *)

Require Import Arith Lia.

Lemma E63fpX : 1191297120 = 1048576 * 1136 + 114784.
Proof.
  cbn [Nat.of_num_uint Nat.of_uint Nat.of_uint_acc].
  try (rewrite !Nat.tail_mul_spec).
  nia.
Qed.

Lemma HLT63fpX : 114784 < 1048576.
Proof.
  cbn [Nat.of_num_uint Nat.of_uint Nat.of_uint_acc].
  try (rewrite !Nat.tail_mul_spec).
  nia.
Qed.

Lemma D63fpX : (1191297120) / 1048576 = 1136.
Proof. symmetry. exact (Nat.div_unique _ _ _ _ HLT63fpX E63fpX). Qed.

Lemma M63fpX : (1191297120) mod 1048576 = 114784.
Proof. symmetry. exact (Nat.mod_unique _ _ _ _ HLT63fpX E63fpX). Qed.

Lemma E63fpY : S (S (1191297119 - 1)) = 1048576 * 1136 + 114784.
Proof.
  cbn [Nat.of_num_uint Nat.of_uint Nat.of_uint_acc].
  try (rewrite !Nat.tail_mul_spec).
  nia.
Qed.

Lemma HLT63fpY : 114784 < 1048576.
Proof.
  cbn [Nat.of_num_uint Nat.of_uint Nat.of_uint_acc].
  try (rewrite !Nat.tail_mul_spec).
  nia.
Qed.

Lemma D63fpY : (S (S (1191297119 - 1))) / 1048576 = 1136.
Proof. symmetry. exact (Nat.div_unique _ _ _ _ HLT63fpY E63fpY). Qed.

Lemma M63fpY : (S (S (1191297119 - 1))) mod 1048576 = 114784.
Proof. symmetry. exact (Nat.mod_unique _ _ _ _ HLT63fpY E63fpY). Qed.
