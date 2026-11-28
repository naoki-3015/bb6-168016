Require Import Arith Lia.

(* NUM63X factored numeral identities (chunk 16). *)
Lemma NUM63X14 : 65515088 = S 65515087.
Proof.
  cbn [Nat.of_num_uint Nat.of_uint Nat.of_uint_acc].
  try (rewrite !Nat.tail_mul_spec).
  nia.
Qed.
