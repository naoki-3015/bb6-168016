(* ================================================================= *)
(* Phase 61 (companion): div/mod values, file Grind29c13.  At ~2.7 x 10^8      *)
(* scale no evaluated comparison survives (the abstract          *)
(* of_num_uint literals materialise as ~4 GB unary chains and    *)
(* div/mod recurse on the value), so each value is certified     *)
(* by an unevaluated Horner/nia equation E : expr = k * q + r    *)
(* plus r < k, and the div/mod values follow by the uniqueness   *)
(* lemmas.  X = Y then follows from the components through       *)
(* Nat.div_mod_eq (the Phase 60 pattern, evaluation-free).       *)
(* ================================================================= *)

Require Import Arith Lia.

Lemma E61nX : 271970480 = 1048576 * 259 + 389296.
Proof.
  cbn [Nat.of_num_uint Nat.of_uint Nat.of_uint_acc].
  try (rewrite !Nat.tail_mul_spec).
  nia.
Qed.

Lemma HLT61nX : 389296 < 1048576.
Proof.
  cbn [Nat.of_num_uint Nat.of_uint Nat.of_uint_acc].
  try (rewrite !Nat.tail_mul_spec).
  nia.
Qed.

Lemma D61nX : (271970480) / 1048576 = 259.
Proof. symmetry. exact (Nat.div_unique _ _ _ _ HLT61nX E61nX). Qed.

Lemma M61nX : (271970480) mod 1048576 = 389296.
Proof. symmetry. exact (Nat.mod_unique _ _ _ _ HLT61nX E61nX). Qed.

Lemma E61nY : S 271970479 = 1048576 * 259 + 389296.
Proof.
  cbn [Nat.of_num_uint Nat.of_uint Nat.of_uint_acc].
  try (rewrite !Nat.tail_mul_spec).
  nia.
Qed.

Lemma HLT61nY : 389296 < 1048576.
Proof.
  cbn [Nat.of_num_uint Nat.of_uint Nat.of_uint_acc].
  try (rewrite !Nat.tail_mul_spec).
  nia.
Qed.

Lemma D61nY : (S 271970479) / 1048576 = 259.
Proof. symmetry. exact (Nat.div_unique _ _ _ _ HLT61nY E61nY). Qed.

Lemma M61nY : (S 271970479) mod 1048576 = 389296.
Proof. symmetry. exact (Nat.mod_unique _ _ _ _ HLT61nY E61nY). Qed.
