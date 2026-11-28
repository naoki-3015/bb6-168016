(* ================================================================= *)
(* Phase 61 (companion): div/mod values, file Grind29c11.  At ~2.7 x 10^8      *)
(* scale no evaluated comparison survives (the abstract          *)
(* of_num_uint literals materialise as ~4 GB unary chains and    *)
(* div/mod recurse on the value), so each value is certified     *)
(* by an unevaluated Horner/nia equation E : expr = k * q + r    *)
(* plus r < k, and the div/mod values follow by the uniqueness   *)
(* lemmas.  X = Y then follows from the components through       *)
(* Nat.div_mod_eq (the Phase 60 pattern, evaluation-free).       *)
(* ================================================================= *)

Require Import Arith Lia.

Lemma E61kX : 271970478 = 1048576 * 259 + 389294.
Proof.
  cbn [Nat.of_num_uint Nat.of_uint Nat.of_uint_acc].
  try (rewrite !Nat.tail_mul_spec).
  nia.
Qed.

Lemma HLT61kX : 389294 < 1048576.
Proof.
  cbn [Nat.of_num_uint Nat.of_uint Nat.of_uint_acc].
  try (rewrite !Nat.tail_mul_spec).
  nia.
Qed.

Lemma D61kX : (271970478) / 1048576 = 259.
Proof. symmetry. exact (Nat.div_unique _ _ _ _ HLT61kX E61kX). Qed.

Lemma M61kX : (271970478) mod 1048576 = 389294.
Proof. symmetry. exact (Nat.mod_unique _ _ _ _ HLT61kX E61kX). Qed.

Lemma E61kY : (271970479 + 2) - 3 = 1048576 * 259 + 389294.
Proof.
  cbn [Nat.of_num_uint Nat.of_uint Nat.of_uint_acc].
  try (rewrite !Nat.tail_mul_spec).
  nia.
Qed.

Lemma HLT61kY : 389294 < 1048576.
Proof.
  cbn [Nat.of_num_uint Nat.of_uint Nat.of_uint_acc].
  try (rewrite !Nat.tail_mul_spec).
  nia.
Qed.

Lemma D61kY : ((271970479 + 2) - 3) / 1048576 = 259.
Proof. symmetry. exact (Nat.div_unique _ _ _ _ HLT61kY E61kY). Qed.

Lemma M61kY : ((271970479 + 2) - 3) mod 1048576 = 389294.
Proof. symmetry. exact (Nat.mod_unique _ _ _ _ HLT61kY E61kY). Qed.
