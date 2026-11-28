Require Import Arith Lia.

(* NUM62X factored numeral identities (chunk 13). *)
Lemma NUM62X90 : 51707591 = 51707593 - 2.
Proof.
  cbn [Nat.of_num_uint Nat.of_uint Nat.of_uint_acc].
  try (rewrite !Nat.tail_mul_spec).
  nia.
Qed.
