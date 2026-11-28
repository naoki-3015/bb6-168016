Require Import Arith Lia.

(* NUM63X factored numeral identities (chunk 2). *)
Lemma NUM63X3 : 367754676 = 367754678 - 2.
Proof.
  cbn [Nat.of_num_uint Nat.of_uint Nat.of_uint_acc].
  try (rewrite !Nat.tail_mul_spec).
  nia.
Qed.
