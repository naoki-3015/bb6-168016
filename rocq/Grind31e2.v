Require Import Arith Lia.

(* NUM63X factored numeral identities (chunk 10). *)
Lemma NUM63X17 : 246445590 = 2 * 123222794 + 2.
Proof.
  cbn [Nat.of_num_uint Nat.of_uint Nat.of_uint_acc].
  try (rewrite !Nat.tail_mul_spec).
  nia.
Qed.
