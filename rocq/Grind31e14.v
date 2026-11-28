Require Import Arith Lia.

(* NUM63X factored numeral identities (chunk 6). *)
Lemma NUM63X18 : 246445594 = 2 * 123222794 + 6.
Proof.
  cbn [Nat.of_num_uint Nat.of_uint Nat.of_uint_acc].
  try (rewrite !Nat.tail_mul_spec).
  nia.
Qed.
