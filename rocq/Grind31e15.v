Require Import Arith Lia.

(* NUM63X factored numeral identities (chunk 7). *)
Lemma NUM63X19 : 246445594 = S 246445593.
Proof.
  cbn [Nat.of_num_uint Nat.of_uint Nat.of_uint_acc].
  try (rewrite !Nat.tail_mul_spec).
  nia.
Qed.
