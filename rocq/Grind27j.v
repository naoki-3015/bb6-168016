(* ================================================================= *)
(* Phase 59 (companion): NUM59a alone.  The identity               *)
(* 58806190 = 2 * 29403093 + 4 (the hGRIND_even 29403093 form of   *)
(* the TOP13 shuttle) is the heaviest closed evaluation of the     *)
(* phase: a direct eqb/vm_compute evaluation peaks ~5.5 GB and     *)
(* OOMs against the ~6 GB host ceiling, GC tuning makes the VM     *)
(* thrash, and kernel conversion of the same identity OOMs too.    *)
(* The proof below therefore splits the addend                     *)
(* (29403093 = 14701546 + 14701547, a 29.4M identity), reshapes    *)
(* the sum SYMBOLICALLY by a generic ring identity over variables  *)
(* (no literal is ever evaluated), and only then evaluates the     *)
(* right-associated sum, in which no Nat.add recursion is deeper   *)
(* than 14701547: peak ~4.1 GB in a fresh process.                 *)
(* ================================================================= *)

Require Import Arith.

Lemma NUM59a : 58806190 = 2 * 29403093 + 4.
Proof.
  assert (H : 29403093 = 14701546 + 14701547)
    by (apply Nat.eqb_eq; vm_compute; reflexivity).
  assert (SH : forall a b, 2 * (a + b) + 4
             = a + (b + (a + (b + 4)))) by (intros; ring).
  rewrite H. rewrite SH.
  apply Nat.eqb_eq; vm_compute; reflexivity.
Qed.
