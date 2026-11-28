Require Import Arith.
Require Import Grind30h.
Lemma P62s747 : 25853793 + 2 <= 95784200.
Proof. rewrite ADD2S. apply Nat.leb_le; vm_compute; reflexivity. Qed.
Lemma P62s739 : 6381218 + 1 <= 9546948.
Proof. rewrite Nat.add_1_r. apply Nat.leb_le; vm_compute; reflexivity. Qed.
Lemma P62s735 : 4773472 <= 4860545.
Proof. apply Nat.leb_le; vm_compute; reflexivity. Qed.
Lemma P62u735 : 1 <= 4773472.
Proof. apply Nat.leb_le; vm_compute; reflexivity. Qed.
Lemma P62s16 : 2120334 <= 2153392.
Proof. apply Nat.leb_le; vm_compute; reflexivity. Qed.
Lemma P62u16 : 1 <= 2120334.
Proof. apply Nat.leb_le; vm_compute; reflexivity. Qed.
