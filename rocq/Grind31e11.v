Require Import Arith Lia.

(* NUM63X factored numeral identities (chunk 3). *)
Lemma NUM63X4 : 367754676 = 2 * 60654540 + 246445596.
Proof.
  cbn [Nat.of_num_uint Nat.of_uint Nat.of_uint_acc].
  try (rewrite !Nat.tail_mul_spec).
  nia.
Qed.
