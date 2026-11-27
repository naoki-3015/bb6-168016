(* ================================================================= *)
(* Phase 59 (companion): the factored shuttle identity of the
(* CASCADE59 pop12 singleton at step 586 (n = 29403094).  It uses  *)
(* the split + symbolic ring reshape of Grind27j.v: a direct       *)
(* evaluation of 3 + 2 * 29403094 peaks ~5.5 GB and OOMs; with     *)
(* the addend split (29403094 = 14701547 + 14701547) and the sum   *)
(* right-associated, no Nat.add recursion exceeds 14701547.        *) *)
(* ================================================================= *)

Require Import Arith.

Lemma S59ru2 : 58806191 = 3 + 2 * 29403094.
Proof.
  assert (H : 29403094 = 14701547 + 14701547)
    by (apply Nat.eqb_eq; vm_compute; reflexivity).
  assert (SH : forall a b, 3 + 2 * (a + b)
             = a + (b + (a + (b + 3)))) by (intros; ring).
  rewrite H. rewrite SH.
  apply Nat.eqb_eq; vm_compute; reflexivity.
Qed.
Lemma S59ru3 : 2 <= 3.
Proof. apply Nat.leb_le; vm_compute; reflexivity. Qed.
