Require Import Arith Lia.

(* NUM63X factored numeral identities (chunk 13). *)
Lemma NUM63X11 : 130856034 = 2 * 65428015 + 4.
Proof.
  cbn [Nat.of_num_uint Nat.of_uint Nat.of_uint_acc].
  try (rewrite !Nat.tail_mul_spec).
  nia.
Qed.
