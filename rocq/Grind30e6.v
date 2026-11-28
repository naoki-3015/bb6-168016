Require Import Arith Lia.

(* NUM62X factored numeral identities (chunk 14). *)
Lemma NUM62X91 : 51707589 = 51707591 - 2.
Proof.
  cbn [Nat.of_num_uint Nat.of_uint Nat.of_uint_acc].
  try (rewrite !Nat.tail_mul_spec).
  nia.
Qed.
