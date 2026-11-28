(* ================================================================= *)
(* Phase 62 (companion): div/mod values, file Grind30c7.  At ~5.4 x 10^8      *)
(* scale no evaluated comparison survives (the abstract          *)
(* of_num_uint literals materialise as ~4 GB unary chains and    *)
(* div/mod recurse on the value), so each value is certified     *)
(* by an unevaluated Horner/nia equation E : expr = k * q + r    *)
(* plus r < k, and the div/mod values follow by the uniqueness   *)
(* lemmas.  X = Y then follows from the components through       *)
(* Nat.div_mod_eq (the Phase 60 pattern, evaluation-free).       *)
(* ================================================================= *)

Require Import Arith Lia.

Lemma E62fpX : 595648558 = 1048576 * 568 + 57390.
Proof.
  cbn [Nat.of_num_uint Nat.of_uint Nat.of_uint_acc].
  try (rewrite !Nat.tail_mul_spec).
  nia.
Qed.

Lemma HLT62fpX : 57390 < 1048576.
Proof.
  cbn [Nat.of_num_uint Nat.of_uint Nat.of_uint_acc].
  try (rewrite !Nat.tail_mul_spec).
  nia.
Qed.

Lemma D62fpX : (595648558) / 1048576 = 568.
Proof. symmetry. exact (Nat.div_unique _ _ _ _ HLT62fpX E62fpX). Qed.

Lemma M62fpX : (595648558) mod 1048576 = 57390.
Proof. symmetry. exact (Nat.mod_unique _ _ _ _ HLT62fpX E62fpX). Qed.

Lemma E62fpY : S (S (595648557 - 1)) = 1048576 * 568 + 57390.
Proof.
  cbn [Nat.of_num_uint Nat.of_uint Nat.of_uint_acc].
  try (rewrite !Nat.tail_mul_spec).
  nia.
Qed.

Lemma HLT62fpY : 57390 < 1048576.
Proof.
  cbn [Nat.of_num_uint Nat.of_uint Nat.of_uint_acc].
  try (rewrite !Nat.tail_mul_spec).
  nia.
Qed.

Lemma D62fpY : (S (S (595648557 - 1))) / 1048576 = 568.
Proof. symmetry. exact (Nat.div_unique _ _ _ _ HLT62fpY E62fpY). Qed.

Lemma M62fpY : (S (S (595648557 - 1))) mod 1048576 = 57390.
Proof. symmetry. exact (Nat.mod_unique _ _ _ _ HLT62fpY E62fpY). Qed.
