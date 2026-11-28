Require Import Arith Lia.

(* NUM62X factored numeral identities (chunk 16). *)
Lemma NUM62X1 : 47892098 = S 47892097.
Proof.
  cbn [Nat.of_num_uint Nat.of_uint Nat.of_uint_acc].
  try (rewrite !Nat.tail_mul_spec).
  nia.
Qed.
