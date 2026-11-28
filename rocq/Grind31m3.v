Require Import Arith Lia.
Require Import Grind31h.
Lemma P63u11 : 1 <= 65428015.
Proof. cbn [Nat.of_num_uint Nat.of_uint Nat.of_uint_acc]. try (rewrite !Nat.tail_mul_spec). nia. Qed.
