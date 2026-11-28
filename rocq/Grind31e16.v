Require Import Arith Lia.

(* NUM63X factored numeral identities (chunk 8). *)
Lemma NUM63X15 : 246445592 = 246445594 - 2.
Proof.
  cbn [Nat.of_num_uint Nat.of_uint Nat.of_uint_acc].
  try (rewrite !Nat.tail_mul_spec).
  nia.
Qed.
