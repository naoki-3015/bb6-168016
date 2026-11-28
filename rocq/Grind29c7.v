(* ================================================================= *)
(* Phase 61 (companion): div/mod values, file Grind29c7.  At ~2.7 x 10^8      *)
(* scale no evaluated comparison survives (the abstract          *)
(* of_num_uint literals materialise as ~4 GB unary chains and    *)
(* div/mod recurse on the value), so each value is certified     *)
(* by an unevaluated Horner/nia equation E : expr = k * q + r    *)
(* plus r < k, and the div/mod values follow by the uniqueness   *)
(* lemmas.  X = Y then follows from the components through       *)
(* Nat.div_mod_eq (the Phase 60 pattern, evaluation-free).       *)
(* ================================================================= *)

Require Import Arith Lia.

Lemma E61fpX : 271970480 = 1048576 * 259 + 389296.
Proof.
  cbn [Nat.of_num_uint Nat.of_uint Nat.of_uint_acc].
  try (rewrite !Nat.tail_mul_spec).
  nia.
Qed.

Lemma HLT61fpX : 389296 < 1048576.
Proof.
  cbn [Nat.of_num_uint Nat.of_uint Nat.of_uint_acc].
  try (rewrite !Nat.tail_mul_spec).
  nia.
Qed.

Lemma D61fpX : (271970480) / 1048576 = 259.
Proof. symmetry. exact (Nat.div_unique _ _ _ _ HLT61fpX E61fpX). Qed.

Lemma M61fpX : (271970480) mod 1048576 = 389296.
Proof. symmetry. exact (Nat.mod_unique _ _ _ _ HLT61fpX E61fpX). Qed.

Lemma E61fpY : S (S (271970479 - 1)) = 1048576 * 259 + 389296.
Proof.
  cbn [Nat.of_num_uint Nat.of_uint Nat.of_uint_acc].
  try (rewrite !Nat.tail_mul_spec).
  nia.
Qed.

Lemma HLT61fpY : 389296 < 1048576.
Proof.
  cbn [Nat.of_num_uint Nat.of_uint Nat.of_uint_acc].
  try (rewrite !Nat.tail_mul_spec).
  nia.
Qed.

Lemma D61fpY : (S (S (271970479 - 1))) / 1048576 = 259.
Proof. symmetry. exact (Nat.div_unique _ _ _ _ HLT61fpY E61fpY). Qed.

Lemma M61fpY : (S (S (271970479 - 1))) mod 1048576 = 389296.
Proof. symmetry. exact (Nat.mod_unique _ _ _ _ HLT61fpY E61fpY). Qed.
