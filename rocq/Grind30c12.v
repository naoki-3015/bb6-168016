(* ================================================================= *)
(* Phase 62 (companion): div/mod values, file Grind30c12.  At ~5.4 x 10^8      *)
(* scale no evaluated comparison survives (the abstract          *)
(* of_num_uint literals materialise as ~4 GB unary chains and    *)
(* div/mod recurse on the value), so each value is certified     *)
(* by an unevaluated Horner/nia equation E : expr = k * q + r    *)
(* plus r < k, and the div/mod values follow by the uniqueness   *)
(* lemmas.  X = Y then follows from the components through       *)
(* Nat.div_mod_eq (the Phase 60 pattern, evaluation-free).       *)
(* ================================================================= *)

Require Import Arith Lia.

Lemma E62mX : 595648560 = 1048576 * 568 + 57392.
Proof.
  cbn [Nat.of_num_uint Nat.of_uint Nat.of_uint_acc].
  try (rewrite !Nat.tail_mul_spec).
  nia.
Qed.

Lemma HLT62mX : 57392 < 1048576.
Proof.
  cbn [Nat.of_num_uint Nat.of_uint Nat.of_uint_acc].
  try (rewrite !Nat.tail_mul_spec).
  nia.
Qed.

Lemma D62mX : (595648560) / 1048576 = 568.
Proof. symmetry. exact (Nat.div_unique _ _ _ _ HLT62mX E62mX). Qed.

Lemma M62mX : (595648560) mod 1048576 = 57392.
Proof. symmetry. exact (Nat.mod_unique _ _ _ _ HLT62mX E62mX). Qed.

Lemma E62mY : S (595648557 + 2) = 1048576 * 568 + 57392.
Proof.
  cbn [Nat.of_num_uint Nat.of_uint Nat.of_uint_acc].
  try (rewrite !Nat.tail_mul_spec).
  nia.
Qed.

Lemma HLT62mY : 57392 < 1048576.
Proof.
  cbn [Nat.of_num_uint Nat.of_uint Nat.of_uint_acc].
  try (rewrite !Nat.tail_mul_spec).
  nia.
Qed.

Lemma D62mY : (S (595648557 + 2)) / 1048576 = 568.
Proof. symmetry. exact (Nat.div_unique _ _ _ _ HLT62mY E62mY). Qed.

Lemma M62mY : (S (595648557 + 2)) mod 1048576 = 57392.
Proof. symmetry. exact (Nat.mod_unique _ _ _ _ HLT62mY E62mY). Qed.
