Require Import Arith Lia.

(* NUM63X factored numeral identities (chunk 9). *)
Lemma NUM63X16 : 246445590 = 246445592 - 2.
Proof.
  cbn [Nat.of_num_uint Nat.of_uint Nat.of_uint_acc].
  try (rewrite !Nat.tail_mul_spec).
  nia.
Qed.
