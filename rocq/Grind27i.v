(* ================================================================= *)
(* Phase 59 (companion): the factored closed identities of the
(* CASCADE59 pop12 singleton at step 578 (n = 3474178) and the    *)
(* first identity of the step-586 singleton, proved once in a     *)
(* fresh process (the S58r pattern) and rewritten in the          *)
(* singleton blocks in Grind27b.v.                                *) *)
(* ================================================================= *)

Require Import Arith.

Lemma S59rs1 : 4012920 = 538742 + 3474178.
Proof. apply Nat.eqb_eq; vm_compute; reflexivity. Qed.
Lemma S59rs2 : 7965811 = 1017455 + 2 * 3474178.
Proof. apply Nat.eqb_eq; vm_compute; reflexivity. Qed.
Lemma S59rs3 : 2 <= 1017455.
Proof. apply Nat.leb_le; vm_compute; reflexivity. Qed.
Lemma S59ru1 : 34304475 = 4901381 + 29403094.
Proof. apply Nat.eqb_eq; vm_compute; reflexivity. Qed.
