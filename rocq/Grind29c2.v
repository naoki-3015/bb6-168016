(* ================================================================= *)
(* Phase 61 (companion): div/mod values, file Grind29c2.  At ~2.7 x 10^8      *)
(* scale no evaluated comparison survives (the abstract          *)
(* of_num_uint literals materialise as ~4 GB unary chains and    *)
(* div/mod recurse on the value), so each value is certified     *)
(* by an unevaluated Horner/nia equation E : expr = k * q + r    *)
(* plus r < k, and the div/mod values follow by the uniqueness   *)
(* lemmas.  X = Y then follows from the components through       *)
(* Nat.div_mod_eq (the Phase 60 pattern, evaluation-free).       *)
(* ================================================================= *)

Require Import Arith Lia.

Lemma E61f2X : 135985239 = 1048576 * 129 + 718935.
Proof.
  cbn [Nat.of_num_uint Nat.of_uint Nat.of_uint_acc].
  try (rewrite !Nat.tail_mul_spec).
  nia.
Qed.

Lemma HLT61f2X : 718935 < 1048576.
Proof.
  cbn [Nat.of_num_uint Nat.of_uint Nat.of_uint_acc].
  try (rewrite !Nat.tail_mul_spec).
  nia.
Qed.

Lemma D61f2X : (135985239) / 1048576 = 129.
Proof. symmetry. exact (Nat.div_unique _ _ _ _ HLT61f2X E61f2X). Qed.

Lemma M61f2X : (135985239) mod 1048576 = 718935.
Proof. symmetry. exact (Nat.mod_unique _ _ _ _ HLT61f2X E61f2X). Qed.

Lemma E61f2Y : S (S (S 135985236)) = 1048576 * 129 + 718935.
Proof.
  cbn [Nat.of_num_uint Nat.of_uint Nat.of_uint_acc].
  try (rewrite !Nat.tail_mul_spec).
  nia.
Qed.

Lemma HLT61f2Y : 718935 < 1048576.
Proof.
  cbn [Nat.of_num_uint Nat.of_uint Nat.of_uint_acc].
  try (rewrite !Nat.tail_mul_spec).
  nia.
Qed.

Lemma D61f2Y : (S (S (S 135985236))) / 1048576 = 129.
Proof. symmetry. exact (Nat.div_unique _ _ _ _ HLT61f2Y E61f2Y). Qed.

Lemma M61f2Y : (S (S (S 135985236))) mod 1048576 = 718935.
Proof. symmetry. exact (Nat.mod_unique _ _ _ _ HLT61f2Y E61f2Y). Qed.
