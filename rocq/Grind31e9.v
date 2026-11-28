Require Import Arith Lia.

(* NUM63X factored numeral identities (chunk 17). *)
Lemma NUM63X1 : 60654541 = S 60654540.
Proof.
  cbn [Nat.of_num_uint Nat.of_uint Nat.of_uint_acc].
  try (rewrite !Nat.tail_mul_spec).
  nia.
Qed.
