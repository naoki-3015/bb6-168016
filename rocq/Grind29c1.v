(* ================================================================= *)
(* Phase 61 (companion): div/mod values, file Grind29c1.  At ~2.7 x 10^8      *)
(* scale no evaluated comparison survives (the abstract          *)
(* of_num_uint literals materialise as ~4 GB unary chains and    *)
(* div/mod recurse on the value), so each value is certified     *)
(* by an unevaluated Horner/nia equation E : expr = k * q + r    *)
(* plus r < k, and the div/mod values follow by the uniqueness   *)
(* lemmas.  X = Y then follows from the components through       *)
(* Nat.div_mod_eq (the Phase 60 pattern, evaluation-free).       *)
(* ================================================================= *)

Require Import Arith Lia.

Lemma E61f1X : 135985239 = 1048576 * 129 + 718935.
Proof.
  cbn [Nat.of_num_uint Nat.of_uint Nat.of_uint_acc].
  try (rewrite !Nat.tail_mul_spec).
  nia.
Qed.

Lemma HLT61f1X : 718935 < 1048576.
Proof.
  cbn [Nat.of_num_uint Nat.of_uint Nat.of_uint_acc].
  try (rewrite !Nat.tail_mul_spec).
  nia.
Qed.

Lemma D61f1X : (135985239) / 1048576 = 129.
Proof. symmetry. exact (Nat.div_unique _ _ _ _ HLT61f1X E61f1X). Qed.

Lemma M61f1X : (135985239) mod 1048576 = 718935.
Proof. symmetry. exact (Nat.mod_unique _ _ _ _ HLT61f1X E61f1X). Qed.

Lemma E61f1Y : (135985240 - 1) = 1048576 * 129 + 718935.
Proof.
  cbn [Nat.of_num_uint Nat.of_uint Nat.of_uint_acc].
  try (rewrite !Nat.tail_mul_spec).
  nia.
Qed.

Lemma HLT61f1Y : 718935 < 1048576.
Proof.
  cbn [Nat.of_num_uint Nat.of_uint Nat.of_uint_acc].
  try (rewrite !Nat.tail_mul_spec).
  nia.
Qed.

Lemma D61f1Y : ((135985240 - 1)) / 1048576 = 129.
Proof. symmetry. exact (Nat.div_unique _ _ _ _ HLT61f1Y E61f1Y). Qed.

Lemma M61f1Y : ((135985240 - 1)) mod 1048576 = 718935.
Proof. symmetry. exact (Nat.mod_unique _ _ _ _ HLT61f1Y E61f1Y). Qed.
