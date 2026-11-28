(* ================================================================= *)
(* Phase 62 (companion): div/mod values, file Grind30c8.  At ~5.4 x 10^8      *)
(* scale no evaluated comparison survives (the abstract          *)
(* of_num_uint literals materialise as ~4 GB unary chains and    *)
(* div/mod recurse on the value), so each value is certified     *)
(* by an unevaluated Horner/nia equation E : expr = k * q + r    *)
(* plus r < k, and the div/mod values follow by the uniqueness   *)
(* lemmas.  X = Y then follows from the components through       *)
(* Nat.div_mod_eq (the Phase 60 pattern, evaluation-free).       *)
(* ================================================================= *)

Require Import Arith Lia.

Lemma E62gX : 367754683 = 1048576 * 350 + 753083.
Proof.
  cbn [Nat.of_num_uint Nat.of_uint Nat.of_uint_acc].
  try (rewrite !Nat.tail_mul_spec).
  nia.
Qed.

Lemma HLT62gX : 753083 < 1048576.
Proof.
  cbn [Nat.of_num_uint Nat.of_uint Nat.of_uint_acc].
  try (rewrite !Nat.tail_mul_spec).
  nia.
Qed.

Lemma D62gX : (367754683) / 1048576 = 350.
Proof. symmetry. exact (Nat.div_unique _ _ _ _ HLT62gX E62gX). Qed.

Lemma M62gX : (367754683) mod 1048576 = 753083.
Proof. symmetry. exact (Nat.mod_unique _ _ _ _ HLT62gX E62gX). Qed.

Lemma E62gY : S 367754682 = 1048576 * 350 + 753083.
Proof.
  cbn [Nat.of_num_uint Nat.of_uint Nat.of_uint_acc].
  try (rewrite !Nat.tail_mul_spec).
  nia.
Qed.

Lemma HLT62gY : 753083 < 1048576.
Proof.
  cbn [Nat.of_num_uint Nat.of_uint Nat.of_uint_acc].
  try (rewrite !Nat.tail_mul_spec).
  nia.
Qed.

Lemma D62gY : (S 367754682) / 1048576 = 350.
Proof. symmetry. exact (Nat.div_unique _ _ _ _ HLT62gY E62gY). Qed.

Lemma M62gY : (S 367754682) mod 1048576 = 753083.
Proof. symmetry. exact (Nat.mod_unique _ _ _ _ HLT62gY E62gY). Qed.
