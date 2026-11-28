(* ================================================================= *)
(* Phase 63 (companion): div/mod values, file Grind31c5.  At ~1.2 x 10^9      *)
(* scale no evaluated comparison survives (the abstract          *)
(* of_num_uint literals materialise as ~4 GB unary chains and    *)
(* div/mod recurse on the value), so each value is certified     *)
(* by an unevaluated Horner/nia equation E : expr = k * q + r    *)
(* plus r < k, and the div/mod values follow by the uniqueness   *)
(* lemmas.  X = Y then follows from the components through       *)
(* Nat.div_mod_eq (the Phase 60 pattern, evaluation-free).       *)
(* ================================================================= *)

Require Import Arith Lia.

Lemma E63bX : 842094153 = 1048576 * 803 + 87625.
Proof.
  cbn [Nat.of_num_uint Nat.of_uint Nat.of_uint_acc].
  try (rewrite !Nat.tail_mul_spec).
  nia.
Qed.

Lemma HLT63bX : 87625 < 1048576.
Proof.
  cbn [Nat.of_num_uint Nat.of_uint Nat.of_uint_acc].
  try (rewrite !Nat.tail_mul_spec).
  nia.
Qed.

Lemma D63bX : (842094153) / 1048576 = 803.
Proof. symmetry. exact (Nat.div_unique _ _ _ _ HLT63bX E63bX). Qed.

Lemma M63bX : (842094153) mod 1048576 = 87625.
Proof. symmetry. exact (Nat.mod_unique _ _ _ _ HLT63bX E63bX). Qed.

Lemma E63bY : S (842094153 - 1) = 1048576 * 803 + 87625.
Proof.
  cbn [Nat.of_num_uint Nat.of_uint Nat.of_uint_acc].
  try (rewrite !Nat.tail_mul_spec).
  nia.
Qed.

Lemma HLT63bY : 87625 < 1048576.
Proof.
  cbn [Nat.of_num_uint Nat.of_uint Nat.of_uint_acc].
  try (rewrite !Nat.tail_mul_spec).
  nia.
Qed.

Lemma D63bY : (S (842094153 - 1)) / 1048576 = 803.
Proof. symmetry. exact (Nat.div_unique _ _ _ _ HLT63bY E63bY). Qed.

Lemma M63bY : (S (842094153 - 1)) mod 1048576 = 87625.
Proof. symmetry. exact (Nat.mod_unique _ _ _ _ HLT63bY E63bY). Qed.
