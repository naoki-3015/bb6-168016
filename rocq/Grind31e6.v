Require Import Arith Lia.

(* NUM63X factored numeral identities (chunk 14). *)
Lemma NUM63X13 : 130856034 = S 130856033.
Proof.
  cbn [Nat.of_num_uint Nat.of_uint Nat.of_uint_acc].
  try (rewrite !Nat.tail_mul_spec).
  nia.
Qed.
