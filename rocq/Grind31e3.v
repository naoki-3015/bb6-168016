Require Import Arith Lia.

(* NUM63X factored numeral identities (chunk 11). *)
Lemma NUM63X21 : 130856035 = S 130856034.
Proof.
  cbn [Nat.of_num_uint Nat.of_uint Nat.of_uint_acc].
  try (rewrite !Nat.tail_mul_spec).
  nia.
Qed.
