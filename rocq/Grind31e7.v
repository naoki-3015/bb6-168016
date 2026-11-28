Require Import Arith Lia.

(* NUM63X factored numeral identities (chunk 15). *)
Lemma NUM63X12 : 65515088 = S 65515087.
Proof.
  cbn [Nat.of_num_uint Nat.of_uint Nat.of_uint_acc].
  try (rewrite !Nat.tail_mul_spec).
  nia.
Qed.
