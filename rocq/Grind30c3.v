(* ================================================================= *)
(* Phase 62 (companion): div/mod values, file Grind30c3.  At ~5.4 x 10^8      *)
(* scale no evaluated comparison survives (the abstract          *)
(* of_num_uint literals materialise as ~4 GB unary chains and    *)
(* div/mod recurse on the value), so each value is certified     *)
(* by an unevaluated Horner/nia equation E : expr = k * q + r    *)
(* plus r < k, and the div/mod values follow by the uniqueness   *)
(* lemmas.  X = Y then follows from the components through       *)
(* Nat.div_mod_eq (the Phase 60 pattern, evaluation-free).       *)
(* ================================================================= *)

Require Import Arith Lia.

Lemma E62f3X : 271970482 = 1048576 * 259 + 389298.
Proof.
  cbn [Nat.of_num_uint Nat.of_uint Nat.of_uint_acc].
  try (rewrite !Nat.tail_mul_spec).
  nia.
Qed.

Lemma HLT62f3X : 389298 < 1048576.
Proof.
  cbn [Nat.of_num_uint Nat.of_uint Nat.of_uint_acc].
  try (rewrite !Nat.tail_mul_spec).
  nia.
Qed.

Lemma D62f3X : (271970482) / 1048576 = 259.
Proof. symmetry. exact (Nat.div_unique _ _ _ _ HLT62f3X E62f3X). Qed.

Lemma M62f3X : (271970482) mod 1048576 = 389298.
Proof. symmetry. exact (Nat.mod_unique _ _ _ _ HLT62f3X E62f3X). Qed.

Lemma E62f3Y : S (S (S (S 271970478))) = 1048576 * 259 + 389298.
Proof.
  cbn [Nat.of_num_uint Nat.of_uint Nat.of_uint_acc].
  try (rewrite !Nat.tail_mul_spec).
  nia.
Qed.

Lemma HLT62f3Y : 389298 < 1048576.
Proof.
  cbn [Nat.of_num_uint Nat.of_uint Nat.of_uint_acc].
  try (rewrite !Nat.tail_mul_spec).
  nia.
Qed.

Lemma D62f3Y : (S (S (S (S 271970478)))) / 1048576 = 259.
Proof. symmetry. exact (Nat.div_unique _ _ _ _ HLT62f3Y E62f3Y). Qed.

Lemma M62f3Y : (S (S (S (S 271970478)))) mod 1048576 = 389298.
Proof. symmetry. exact (Nat.mod_unique _ _ _ _ HLT62f3Y E62f3Y). Qed.
