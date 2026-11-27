(* ================================================================= *)
(* Phase 60 (companion): NUM60m, 135985240 = S 135985239, by        *)
(* div/mod decomposition (see Grind28s.v's header).  Used at the   *)
(* band/fence boundary in TAIL2_END14_of60.                         *)
(* ================================================================= *)

Require Import Arith.
Require Import Grind28u.

Lemma D60mY : (S 135985239) / 1048576 = 129.
Proof. apply Nat.eqb_eq; vm_compute; reflexivity. Qed.
Lemma M60mY : (S 135985239) mod 1048576 = 718936.
Proof. apply Nat.eqb_eq; vm_compute; reflexivity. Qed.

Lemma NUM60m : 135985240 = S 135985239.
Proof.
  rewrite (Nat.div_mod_eq 135985240 1048576) at 1.
  rewrite (Nat.div_mod_eq (S 135985239) 1048576) at 1.
  rewrite D60mX, M60mX, D60mY, M60mY. reflexivity.
Qed.
