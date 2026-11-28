Require Import Arith Lia.
Require Import Grind31h.
Lemma P63s15 : 123222794 + 1 <= 130856034.
Proof. cbn [Nat.of_num_uint Nat.of_uint Nat.of_uint_acc]. try (rewrite !Nat.tail_mul_spec). nia. Qed.
Lemma P63s7 : 4773472 + 1 <= 4860545.
Proof. cbn [Nat.of_num_uint Nat.of_uint Nat.of_uint_acc]. try (rewrite !Nat.tail_mul_spec). nia. Qed.
