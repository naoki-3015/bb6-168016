Require Import Arith Lia.

(* NUM63X factored numeral identities (chunk 12). *)
Lemma NUM63X9 : 130856034 = 130856035 - 1.
Proof.
  cbn [Nat.of_num_uint Nat.of_uint Nat.of_uint_acc].
  try (rewrite !Nat.tail_mul_spec).
  nia.
Qed.
