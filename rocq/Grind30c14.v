(* ================================================================= *)
(* Phase 62 (companion): div/mod values, file Grind30c14.  At ~5.4 x 10^8      *)
(* scale no evaluated comparison survives (the abstract          *)
(* of_num_uint literals materialise as ~4 GB unary chains and    *)
(* div/mod recurse on the value), so each value is certified     *)
(* by an unevaluated Horner/nia equation E : expr = k * q + r    *)
(* plus r < k, and the div/mod values follow by the uniqueness   *)
(* lemmas.  X = Y then follows from the components through       *)
(* Nat.div_mod_eq (the Phase 60 pattern, evaluation-free).       *)
(* ================================================================= *)

Require Import Arith Lia.

Lemma E62m2X : 271970482 = 1048576 * 259 + 389298.
Proof.
  cbn [Nat.of_num_uint Nat.of_uint Nat.of_uint_acc].
  try (rewrite !Nat.tail_mul_spec).
  nia.
Qed.

Lemma HLT62m2X : 389298 < 1048576.
Proof.
  cbn [Nat.of_num_uint Nat.of_uint Nat.of_uint_acc].
  try (rewrite !Nat.tail_mul_spec).
  nia.
Qed.

Lemma D62m2X : (271970482) / 1048576 = 259.
Proof. symmetry. exact (Nat.div_unique _ _ _ _ HLT62m2X E62m2X). Qed.

Lemma M62m2X : (271970482) mod 1048576 = 389298.
Proof. symmetry. exact (Nat.mod_unique _ _ _ _ HLT62m2X E62m2X). Qed.

Lemma E62m2Y : S 271970481 = 1048576 * 259 + 389298.
Proof.
  cbn [Nat.of_num_uint Nat.of_uint Nat.of_uint_acc].
  try (rewrite !Nat.tail_mul_spec).
  nia.
Qed.

Lemma HLT62m2Y : 389298 < 1048576.
Proof.
  cbn [Nat.of_num_uint Nat.of_uint Nat.of_uint_acc].
  try (rewrite !Nat.tail_mul_spec).
  nia.
Qed.

Lemma D62m2Y : (S 271970481) / 1048576 = 259.
Proof. symmetry. exact (Nat.div_unique _ _ _ _ HLT62m2Y E62m2Y). Qed.

Lemma M62m2Y : (S 271970481) mod 1048576 = 389298.
Proof. symmetry. exact (Nat.mod_unique _ _ _ _ HLT62m2Y E62m2Y). Qed.
