Require Import Arith Lia.

(* NUM62X factored numeral identities (chunk 12). *)
Lemma NUM62X85 : 51707593 = 51707595 - 2.
Proof.
  cbn [Nat.of_num_uint Nat.of_uint Nat.of_uint_acc].
  try (rewrite !Nat.tail_mul_spec).
  nia.
Qed.
