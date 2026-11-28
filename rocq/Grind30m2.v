Require Import Arith.
Require Import Grind30h.
Lemma P62s743 : 47892098 <= 60654541.
Proof. apply Nat.leb_le; vm_compute; reflexivity. Qed.
