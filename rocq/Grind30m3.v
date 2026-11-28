Require Import Arith.
Require Import Grind30h.
Lemma P62u743 : 1 <= 47892098.
Proof. apply Nat.leb_le; vm_compute; reflexivity. Qed.
