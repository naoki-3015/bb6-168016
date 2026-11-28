(* ================================================================= *)
(* Phase 61 (companion): div/mod values, file Grind29c12.  At ~2.7 x 10^8      *)
(* scale no evaluated comparison survives (the abstract          *)
(* of_num_uint literals materialise as ~4 GB unary chains and    *)
(* div/mod recurse on the value), so each value is certified     *)
(* by an unevaluated Horner/nia equation E : expr = k * q + r    *)
(* plus r < k, and the div/mod values follow by the uniqueness   *)
(* lemmas.  X = Y then follows from the components through       *)
(* Nat.div_mod_eq (the Phase 60 pattern, evaluation-free).       *)
(* ================================================================= *)

Require Import Arith Lia.

Lemma E61mX : 271970482 = 1048576 * 259 + 389298.
Proof.
  cbn [Nat.of_num_uint Nat.of_uint Nat.of_uint_acc].
  try (rewrite !Nat.tail_mul_spec).
  nia.
Qed.

Lemma HLT61mX : 389298 < 1048576.
Proof.
  cbn [Nat.of_num_uint Nat.of_uint Nat.of_uint_acc].
  try (rewrite !Nat.tail_mul_spec).
  nia.
Qed.

Lemma D61mX : (271970482) / 1048576 = 259.
Proof. symmetry. exact (Nat.div_unique _ _ _ _ HLT61mX E61mX). Qed.

Lemma M61mX : (271970482) mod 1048576 = 389298.
Proof. symmetry. exact (Nat.mod_unique _ _ _ _ HLT61mX E61mX). Qed.

Lemma E61mY : S (271970479 + 2) = 1048576 * 259 + 389298.
Proof.
  cbn [Nat.of_num_uint Nat.of_uint Nat.of_uint_acc].
  try (rewrite !Nat.tail_mul_spec).
  nia.
Qed.

Lemma HLT61mY : 389298 < 1048576.
Proof.
  cbn [Nat.of_num_uint Nat.of_uint Nat.of_uint_acc].
  try (rewrite !Nat.tail_mul_spec).
  nia.
Qed.

Lemma D61mY : (S (271970479 + 2)) / 1048576 = 259.
Proof. symmetry. exact (Nat.div_unique _ _ _ _ HLT61mY E61mY). Qed.

Lemma M61mY : (S (271970479 + 2)) mod 1048576 = 389298.
Proof. symmetry. exact (Nat.mod_unique _ _ _ _ HLT61mY E61mY). Qed.
