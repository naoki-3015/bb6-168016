(* ================================================================= *)
(* Phase 63 (companion): div/mod values, file Grind31c14.  At ~1.2 x 10^9      *)
(* scale no evaluated comparison survives (the abstract          *)
(* of_num_uint literals materialise as ~4 GB unary chains and    *)
(* div/mod recurse on the value), so each value is certified     *)
(* by an unevaluated Horner/nia equation E : expr = k * q + r    *)
(* plus r < k, and the div/mod values follow by the uniqueness   *)
(* lemmas.  X = Y then follows from the components through       *)
(* Nat.div_mod_eq (the Phase 60 pattern, evaluation-free).       *)
(* ================================================================= *)

Require Import Arith Lia.

Lemma E63m2X : 595648560 = 1048576 * 568 + 57392.
Proof.
  cbn [Nat.of_num_uint Nat.of_uint Nat.of_uint_acc].
  try (rewrite !Nat.tail_mul_spec).
  nia.
Qed.

Lemma HLT63m2X : 57392 < 1048576.
Proof.
  cbn [Nat.of_num_uint Nat.of_uint Nat.of_uint_acc].
  try (rewrite !Nat.tail_mul_spec).
  nia.
Qed.

Lemma D63m2X : (595648560) / 1048576 = 568.
Proof. symmetry. exact (Nat.div_unique _ _ _ _ HLT63m2X E63m2X). Qed.

Lemma M63m2X : (595648560) mod 1048576 = 57392.
Proof. symmetry. exact (Nat.mod_unique _ _ _ _ HLT63m2X E63m2X). Qed.

Lemma E63m2Y : S 595648559 = 1048576 * 568 + 57392.
Proof.
  cbn [Nat.of_num_uint Nat.of_uint Nat.of_uint_acc].
  try (rewrite !Nat.tail_mul_spec).
  nia.
Qed.

Lemma HLT63m2Y : 57392 < 1048576.
Proof.
  cbn [Nat.of_num_uint Nat.of_uint Nat.of_uint_acc].
  try (rewrite !Nat.tail_mul_spec).
  nia.
Qed.

Lemma D63m2Y : (S 595648559) / 1048576 = 568.
Proof. symmetry. exact (Nat.div_unique _ _ _ _ HLT63m2Y E63m2Y). Qed.

Lemma M63m2Y : (S 595648559) mod 1048576 = 57392.
Proof. symmetry. exact (Nat.mod_unique _ _ _ _ HLT63m2Y E63m2Y). Qed.
