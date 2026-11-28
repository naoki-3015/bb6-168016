Require Import Arith Lia.
Require Import Grind31h.
Lemma P63s11 : 65428015 <= 65515087.
Proof. cbn [Nat.of_num_uint Nat.of_uint Nat.of_uint_acc]. try (rewrite !Nat.tail_mul_spec). nia. Qed.
