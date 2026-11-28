(* ================================================================= *)
(* Phase 62 (companion): div/mod values, file Grind30c5.  At ~5.4 x 10^8      *)
(* scale no evaluated comparison survives (the abstract          *)
(* of_num_uint literals materialise as ~4 GB unary chains and    *)
(* div/mod recurse on the value), so each value is certified     *)
(* by an unevaluated Horner/nia equation E : expr = k * q + r    *)
(* plus r < k, and the div/mod values follow by the uniqueness   *)
(* lemmas.  X = Y then follows from the components through       *)
(* Nat.div_mod_eq (the Phase 60 pattern, evaluation-free).       *)
(* ================================================================= *)

Require Import Arith Lia.

Lemma E62bX : 367754682 = 1048576 * 350 + 753082.
Proof.
  cbn [Nat.of_num_uint Nat.of_uint Nat.of_uint_acc].
  try (rewrite !Nat.tail_mul_spec).
  nia.
Qed.

Lemma HLT62bX : 753082 < 1048576.
Proof.
  cbn [Nat.of_num_uint Nat.of_uint Nat.of_uint_acc].
  try (rewrite !Nat.tail_mul_spec).
  nia.
Qed.

Lemma D62bX : (367754682) / 1048576 = 350.
Proof. symmetry. exact (Nat.div_unique _ _ _ _ HLT62bX E62bX). Qed.

Lemma M62bX : (367754682) mod 1048576 = 753082.
Proof. symmetry. exact (Nat.mod_unique _ _ _ _ HLT62bX E62bX). Qed.

Lemma E62bY : S (367754682 - 1) = 1048576 * 350 + 753082.
Proof.
  cbn [Nat.of_num_uint Nat.of_uint Nat.of_uint_acc].
  try (rewrite !Nat.tail_mul_spec).
  nia.
Qed.

Lemma HLT62bY : 753082 < 1048576.
Proof.
  cbn [Nat.of_num_uint Nat.of_uint Nat.of_uint_acc].
  try (rewrite !Nat.tail_mul_spec).
  nia.
Qed.

Lemma D62bY : (S (367754682 - 1)) / 1048576 = 350.
Proof. symmetry. exact (Nat.div_unique _ _ _ _ HLT62bY E62bY). Qed.

Lemma M62bY : (S (367754682 - 1)) mod 1048576 = 753082.
Proof. symmetry. exact (Nat.mod_unique _ _ _ _ HLT62bY E62bY). Qed.
