Require Import Arith Lia.

(* NUM63X factored numeral identities (chunk 4). *)
Lemma NUM63X20 : 246445595 = S (S 246445593).
Proof.
  cbn [Nat.of_num_uint Nat.of_uint Nat.of_uint_acc].
  try (rewrite !Nat.tail_mul_spec).
  nia.
Qed.
