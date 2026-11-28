(* ================================================================= *)
(* Phase 63 (companion): div/mod values, file Grind31c12.  At ~1.2 x 10^9      *)
(* scale no evaluated comparison survives (the abstract          *)
(* of_num_uint literals materialise as ~4 GB unary chains and    *)
(* div/mod recurse on the value), so each value is certified     *)
(* by an unevaluated Horner/nia equation E : expr = k * q + r    *)
(* plus r < k, and the div/mod values follow by the uniqueness   *)
(* lemmas.  X = Y then follows from the components through       *)
(* Nat.div_mod_eq (the Phase 60 pattern, evaluation-free).       *)
(* ================================================================= *)

Require Import Arith Lia.

Lemma E63mX : 1191297122 = 1048576 * 1136 + 114786.
Proof.
  cbn [Nat.of_num_uint Nat.of_uint Nat.of_uint_acc].
  try (rewrite !Nat.tail_mul_spec).
  nia.
Qed.

Lemma HLT63mX : 114786 < 1048576.
Proof.
  cbn [Nat.of_num_uint Nat.of_uint Nat.of_uint_acc].
  try (rewrite !Nat.tail_mul_spec).
  nia.
Qed.

Lemma D63mX : (1191297122) / 1048576 = 1136.
Proof. symmetry. exact (Nat.div_unique _ _ _ _ HLT63mX E63mX). Qed.

Lemma M63mX : (1191297122) mod 1048576 = 114786.
Proof. symmetry. exact (Nat.mod_unique _ _ _ _ HLT63mX E63mX). Qed.

Lemma E63mY : S (1191297119 + 2) = 1048576 * 1136 + 114786.
Proof.
  cbn [Nat.of_num_uint Nat.of_uint Nat.of_uint_acc].
  try (rewrite !Nat.tail_mul_spec).
  nia.
Qed.

Lemma HLT63mY : 114786 < 1048576.
Proof.
  cbn [Nat.of_num_uint Nat.of_uint Nat.of_uint_acc].
  try (rewrite !Nat.tail_mul_spec).
  nia.
Qed.

Lemma D63mY : (S (1191297119 + 2)) / 1048576 = 1136.
Proof. symmetry. exact (Nat.div_unique _ _ _ _ HLT63mY E63mY). Qed.

Lemma M63mY : (S (1191297119 + 2)) mod 1048576 = 114786.
Proof. symmetry. exact (Nat.mod_unique _ _ _ _ HLT63mY E63mY). Qed.
