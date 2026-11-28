(* ================================================================= *)
(* Phase 62 (companion): div/mod values, file Grind30c2.  At ~5.4 x 10^8      *)
(* scale no evaluated comparison survives (the abstract          *)
(* of_num_uint literals materialise as ~4 GB unary chains and    *)
(* div/mod recurse on the value), so each value is certified     *)
(* by an unevaluated Horner/nia equation E : expr = k * q + r    *)
(* plus r < k, and the div/mod values follow by the uniqueness   *)
(* lemmas.  X = Y then follows from the components through       *)
(* Nat.div_mod_eq (the Phase 60 pattern, evaluation-free).       *)
(* ================================================================= *)

Require Import Arith Lia.

Lemma E62f2X : 271970481 = 1048576 * 259 + 389297.
Proof.
  cbn [Nat.of_num_uint Nat.of_uint Nat.of_uint_acc].
  try (rewrite !Nat.tail_mul_spec).
  nia.
Qed.

Lemma HLT62f2X : 389297 < 1048576.
Proof.
  cbn [Nat.of_num_uint Nat.of_uint Nat.of_uint_acc].
  try (rewrite !Nat.tail_mul_spec).
  nia.
Qed.

Lemma D62f2X : (271970481) / 1048576 = 259.
Proof. symmetry. exact (Nat.div_unique _ _ _ _ HLT62f2X E62f2X). Qed.

Lemma M62f2X : (271970481) mod 1048576 = 389297.
Proof. symmetry. exact (Nat.mod_unique _ _ _ _ HLT62f2X E62f2X). Qed.

Lemma E62f2Y : S (S (S 271970478)) = 1048576 * 259 + 389297.
Proof.
  cbn [Nat.of_num_uint Nat.of_uint Nat.of_uint_acc].
  try (rewrite !Nat.tail_mul_spec).
  nia.
Qed.

Lemma HLT62f2Y : 389297 < 1048576.
Proof.
  cbn [Nat.of_num_uint Nat.of_uint Nat.of_uint_acc].
  try (rewrite !Nat.tail_mul_spec).
  nia.
Qed.

Lemma D62f2Y : (S (S (S 271970478))) / 1048576 = 259.
Proof. symmetry. exact (Nat.div_unique _ _ _ _ HLT62f2Y E62f2Y). Qed.

Lemma M62f2Y : (S (S (S 271970478))) mod 1048576 = 389297.
Proof. symmetry. exact (Nat.mod_unique _ _ _ _ HLT62f2Y E62f2Y). Qed.
