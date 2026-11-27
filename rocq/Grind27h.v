(* ================================================================= *)
(* Phase 59 (companion 2): the leb side-goal lemmas of the TOP13   *)
(* closings, VM-proved in a tiny early file (the S58g pattern):    *)
(* the hGRIND_even 29403093 premises 1 <= 29403093 and             *)
(* 29403093 <= 34304474, and 2 <= 58806191 for the band's first     *)
(* sTUP.  Never discharge ~10^7-scale <= goals by lia (Phase 58    *)
(* finding: it OOMs past the host ceiling).                        *)
(* ================================================================= *)

Require Import Arith.

Lemma S59g1 : 1 <= 29403093.
Proof. apply Nat.leb_le; vm_compute; reflexivity. Qed.
Lemma S59g2 : 29403093 <= 34304474.
Proof. apply Nat.leb_le; vm_compute; reflexivity. Qed.
Lemma S59h0 : 2 <= 58806191.
Proof. apply Nat.leb_le; vm_compute; reflexivity. Qed.

(* Two of the NUM59 closing identities (the rest live in           *)
(* Grind27j.v / Grind27k.v / Grind27l.v, split by evaluation       *)
(* weight; see Grind27.v's header).                                *)
Lemma NUM59b : 34304475 = S 34304474.
Proof. apply Nat.eqb_eq; vm_compute; reflexivity. Qed.
Lemma NUM59e : 58806191 = S 58806190.
Proof. apply Nat.eqb_eq; vm_compute; reflexivity. Qed.
