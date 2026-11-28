(* ================================================================= *)
(* Phase 62 (companion): div/mod values, file Grind30c9.  At ~5.4 x 10^8      *)
(* scale no evaluated comparison survives (the abstract          *)
(* of_num_uint literals materialise as ~4 GB unary chains and    *)
(* div/mod recurse on the value), so each value is certified     *)
(* by an unevaluated Horner/nia equation E : expr = k * q + r    *)
(* plus r < k, and the div/mod values follow by the uniqueness   *)
(* lemmas.  X = Y then follows from the components through       *)
(* Nat.div_mod_eq (the Phase 60 pattern, evaluation-free).       *)
(* ================================================================= *)

Require Import Arith Lia.

Lemma E62iX : 595648556 = 1048576 * 568 + 57388.
Proof.
  cbn [Nat.of_num_uint Nat.of_uint Nat.of_uint_acc].
  try (rewrite !Nat.tail_mul_spec).
  nia.
Qed.

Lemma HLT62iX : 57388 < 1048576.
Proof.
  cbn [Nat.of_num_uint Nat.of_uint Nat.of_uint_acc].
  try (rewrite !Nat.tail_mul_spec).
  nia.
Qed.

Lemma D62iX : (595648556) / 1048576 = 568.
Proof. symmetry. exact (Nat.div_unique _ _ _ _ HLT62iX E62iX). Qed.

Lemma M62iX : (595648556) mod 1048576 = 57388.
Proof. symmetry. exact (Nat.mod_unique _ _ _ _ HLT62iX E62iX). Qed.

Lemma E62iY : S (595648557 - 1 - 1) = 1048576 * 568 + 57388.
Proof.
  cbn [Nat.of_num_uint Nat.of_uint Nat.of_uint_acc].
  try (rewrite !Nat.tail_mul_spec).
  nia.
Qed.

Lemma HLT62iY : 57388 < 1048576.
Proof.
  cbn [Nat.of_num_uint Nat.of_uint Nat.of_uint_acc].
  try (rewrite !Nat.tail_mul_spec).
  nia.
Qed.

Lemma D62iY : (S (595648557 - 1 - 1)) / 1048576 = 568.
Proof. symmetry. exact (Nat.div_unique _ _ _ _ HLT62iY E62iY). Qed.

Lemma M62iY : (S (595648557 - 1 - 1)) mod 1048576 = 57388.
Proof. symmetry. exact (Nat.mod_unique _ _ _ _ HLT62iY E62iY). Qed.
