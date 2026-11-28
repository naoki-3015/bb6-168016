Require Import Arith Lia.

(* Factored closed identities for the big pop12       *)
(* singletons of CASCADE63 (the S60r pattern).        *)
Lemma S63rb1 : 65515088 = 4860546 + 60654542.
Proof.
  cbn [Nat.of_num_uint Nat.of_uint Nat.of_uint_acc].
  try (rewrite !Nat.tail_mul_spec).
  nia.
Qed.
Lemma S63rb2 : 130856035 = 9546951 + 2 * 60654542.
Proof.
  cbn [Nat.of_num_uint Nat.of_uint Nat.of_uint_acc].
  try (rewrite !Nat.tail_mul_spec).
  nia.
Qed.
Lemma S63rb3 : 2 <= 9546951.
Proof.
  cbn [Nat.of_num_uint Nat.of_uint Nat.of_uint_acc].
  try (rewrite !Nat.tail_mul_spec).
  nia.
Qed.
Lemma S63rd1 : 842094153 = 246445595 + 595648558.
Proof.
  cbn [Nat.of_num_uint Nat.of_uint Nat.of_uint_acc].
  try (rewrite !Nat.tail_mul_spec).
  nia.
Qed.
Lemma S63rd2 : 1191297119 = 3 + 2 * 595648558.
Proof.
  cbn [Nat.of_num_uint Nat.of_uint Nat.of_uint_acc].
  try (rewrite !Nat.tail_mul_spec).
  nia.
Qed.
Lemma S63rd3 : 2 <= 3.
Proof.
  cbn [Nat.of_num_uint Nat.of_uint Nat.of_uint_acc].
  try (rewrite !Nat.tail_mul_spec).
  nia.
Qed.
