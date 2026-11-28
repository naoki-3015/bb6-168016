(* ================================================================= *)
(* Phase 62 (companion): div/mod values, file Grind30c11.  At ~5.4 x 10^8      *)
(* scale no evaluated comparison survives (the abstract          *)
(* of_num_uint literals materialise as ~4 GB unary chains and    *)
(* div/mod recurse on the value), so each value is certified     *)
(* by an unevaluated Horner/nia equation E : expr = k * q + r    *)
(* plus r < k, and the div/mod values follow by the uniqueness   *)
(* lemmas.  X = Y then follows from the components through       *)
(* Nat.div_mod_eq (the Phase 60 pattern, evaluation-free).       *)
(* ================================================================= *)

Require Import Arith Lia.

Lemma E62kX : 595648556 = 1048576 * 568 + 57388.
Proof.
  cbn [Nat.of_num_uint Nat.of_uint Nat.of_uint_acc].
  try (rewrite !Nat.tail_mul_spec).
  nia.
Qed.

Lemma HLT62kX : 57388 < 1048576.
Proof.
  cbn [Nat.of_num_uint Nat.of_uint Nat.of_uint_acc].
  try (rewrite !Nat.tail_mul_spec).
  nia.
Qed.

Lemma D62kX : (595648556) / 1048576 = 568.
Proof. symmetry. exact (Nat.div_unique _ _ _ _ HLT62kX E62kX). Qed.

Lemma M62kX : (595648556) mod 1048576 = 57388.
Proof. symmetry. exact (Nat.mod_unique _ _ _ _ HLT62kX E62kX). Qed.

Lemma E62kY : (595648557 + 2) - 3 = 1048576 * 568 + 57388.
Proof.
  cbn [Nat.of_num_uint Nat.of_uint Nat.of_uint_acc].
  try (rewrite !Nat.tail_mul_spec).
  nia.
Qed.

Lemma HLT62kY : 57388 < 1048576.
Proof.
  cbn [Nat.of_num_uint Nat.of_uint Nat.of_uint_acc].
  try (rewrite !Nat.tail_mul_spec).
  nia.
Qed.

Lemma D62kY : ((595648557 + 2) - 3) / 1048576 = 568.
Proof. symmetry. exact (Nat.div_unique _ _ _ _ HLT62kY E62kY). Qed.

Lemma M62kY : ((595648557 + 2) - 3) mod 1048576 = 57388.
Proof. symmetry. exact (Nat.mod_unique _ _ _ _ HLT62kY E62kY). Qed.
