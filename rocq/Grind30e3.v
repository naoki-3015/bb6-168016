Require Import Arith Lia.

(* NUM62X factored numeral identities (chunk 11). *)
Lemma NUM62X93 : 51707594 = 2 * 25853793 + 8.
Proof.
  cbn [Nat.of_num_uint Nat.of_uint Nat.of_uint_acc].
  try (rewrite !Nat.tail_mul_spec).
  nia.
Qed.
