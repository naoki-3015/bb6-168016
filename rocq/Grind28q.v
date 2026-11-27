(* ================================================================= *)
(* Phase 60 (companion): NUM60e', the TOP14 shuttle S-identity in   *)
(* (V - 1) form.  At 136M scale every two-chain evaluated           *)
(* comparison OOMs (plain S-form eqb, addt, split+reshape: see     *)
(* build-logs-60/probes.txt), so the S-identities of the TOP14     *)
(* numerals are carried in (V - 1) form, proved from               *)
(* Nat.succ_pred_pos with a single-chain leb side condition         *)
(* (probeC60: rc=0, 3,380 MiB).  The closings instantiate the       *)
(* step lemmas at s' := (V - 1) accordingly.                        *)
(* ================================================================= *)

Require Import Arith.

Lemma S_sub_1_60 : forall V, 1 <= V -> V = S (V - 1).
Proof.
  intros V HV. rewrite Nat.sub_1_r. symmetry. apply Nat.succ_pred_pos.
  apply Nat.neq_0_lt_0. intros Hc. rewrite Hc in HV. simpl in HV.
  inversion HV.
Qed.

Lemma NUM60e' : 135985237 = S (135985237 - 1).
Proof.
  apply S_sub_1_60. apply Nat.leb_le. vm_compute. reflexivity.
Qed.
