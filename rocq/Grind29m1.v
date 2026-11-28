Require Import Arith.
Require Import Grind29h.
Lemma P61s1151 : 5753275 + 1 <= 47892098.
Proof. rewrite Nat.add_1_r. apply Nat.leb_le; vm_compute; reflexivity. Qed.
Lemma P61s1147 : 23946047 <= 24915617.
Proof. apply Nat.leb_le; vm_compute; reflexivity. Qed.
Lemma P61s11 : 10744542 <= 10824710.
Proof. apply Nat.leb_le; vm_compute; reflexivity. Qed.
Lemma P61u11 : 1 <= 10744542.
Proof. apply Nat.leb_le; vm_compute; reflexivity. Qed.
Lemma P61s1142 : 2456954 + 2 <= 3426526.
Proof. rewrite ADD2S. apply Nat.leb_le; vm_compute; reflexivity. Qed.
Lemma P61s1138 : 1713261 <= 1835910.
Proof. apply Nat.leb_le; vm_compute; reflexivity. Qed.
Lemma P61u1138 : 1 <= 1713261.
Proof. apply Nat.leb_le; vm_compute; reflexivity. Qed.
