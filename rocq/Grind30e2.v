Require Import Arith Lia.

(* NUM62X factored numeral identities (chunk 10). *)
Lemma NUM62X95 : 51707597 = 51707596 + 1.
Proof.
  cbn [Nat.of_num_uint Nat.of_uint Nat.of_uint_acc].
  try (rewrite !Nat.tail_mul_spec).
  nia.
Qed.
