(* ================================================================= *)
(* Phase 23 -- Finite.v: the finite segments of the proof of         *)
(* #168016, verified by kernel computation (vm_compute).             *)
(*                                                                   *)
(* Method: configurations are compared up to trailing blanks via a   *)
(* canonical form (strip trailing false cells on both sides).        *)
(* seg_check n c0 c1 decides "run n c0 reaches a configuration with  *)
(* the same state and the same tape as c1"; seg_check_sound turns a  *)
(* positive check into that semantic statement, and seg_no_halt      *)
(* extracts that no step on the way halts (no E-on-0 read), since    *)
(* run n c0 = Some _ already excludes it.                            *)
(* ================================================================= *)

Require Import List Bool Arith Lia ZArith.
Import ListNotations.
Require Import TM.
Require Import Configs.

(* Strip trailing blank (false) cells; the tape is unchanged. *)
Fixpoint strip0 (l : list sym) : list sym :=
  match l with
  | [] => []
  | x :: t => match strip0 t with
              | [] => if x then [x] else []
              | t' => x :: t'
              end
  end.

Lemma nth_nil : forall i, nth i (@nil sym) false = false.
Proof. destruct i; reflexivity. Qed.

Lemma nth_strip0 : forall l i, nth i (strip0 l) false = nth i l false.
Proof.
  induction l as [| x t IH]; intros i; [reflexivity |].
  destruct (strip0 t) as [| y t'] eqn:E.
  - change (strip0 (x :: t)) with
      (match strip0 t with
       | [] => if x then [x] else []
       | t' => x :: t' end).
    rewrite E. simpl.
    destruct x; destruct i; simpl; try reflexivity;
      rewrite <- IH; destruct i; reflexivity.
  - change (strip0 (x :: t)) with
      (match strip0 t with
       | [] => if x then [x] else []
       | t' => x :: t' end).
    rewrite E. simpl.
    destruct i; simpl; [reflexivity |].
    apply IH.
Qed.

Definition canon (c : config) : config :=
  mkCfg (cstate c) (strip0 (cleft c)) (strip0 (cright c)).

Lemma tape_of_canon : forall c p, tape_of (canon c) p = tape_of c p.
Proof.
  intros c p. unfold tape_of, canon. cbn [cright cleft].
  destruct (Z_le_dec 0 p); apply nth_strip0.
Qed.

Definition state_eqb (a b : state) : bool :=
  match a, b with
  | SA, SA | SB, SB | SC, SC | SD, SD | SE, SE | SF, SF => true
  | _, _ => false
  end.

Fixpoint syms_eqb (l1 l2 : list sym) : bool :=
  match l1, l2 with
  | [], [] => true
  | x :: t1, y :: t2 => eqb x y && syms_eqb t1 t2
  | _, _ => false
  end.

Lemma syms_eqb_nth : forall l1 l2, syms_eqb l1 l2 = true ->
  forall i, nth i l1 false = nth i l2 false.
Proof.
  induction l1 as [| x t1 IH]; intros l2 H i.
  - destruct l2; simpl in H; [reflexivity | discriminate].
  - destruct l2 as [| y t2]; simpl in H; [discriminate |].
    apply andb_true_iff in H. destruct H as [Hxy Ht].
    apply eqb_prop in Hxy. subst y.
    destruct i; simpl; [reflexivity | apply IH; exact Ht].
Qed.

Definition config_eqb (c1 c2 : config) : bool :=
  state_eqb (cstate c1) (cstate c2) &&
  syms_eqb (cleft c1) (cleft c2) &&
  syms_eqb (cright c1) (cright c2).

Lemma config_eqb_correct : forall c1 c2, config_eqb c1 c2 = true ->
  cstate c1 = cstate c2 /\ (forall p, tape_of c1 p = tape_of c2 p).
Proof.
  intros c1 c2 H. unfold config_eqb in H.
  apply andb_true_iff in H. destruct H as [H Hright].
  apply andb_true_iff in H. destruct H as [Hstate Hleft].
  split.
  - destruct (cstate c1), (cstate c2); simpl in Hstate;
      try discriminate; reflexivity.
  - intros p. unfold tape_of.
    destruct (Z_le_dec 0 p).
    + apply syms_eqb_nth. exact Hright.
    + apply syms_eqb_nth. exact Hleft.
Qed.

Definition seg_check (n : nat) (c0 c1 : config) : bool :=
  match run n c0 with
  | Some c => config_eqb (canon c) (canon c1)
  | None => false
  end.

Lemma seg_check_sound : forall n c0 c1, seg_check n c0 c1 = true ->
  exists c, run n c0 = Some c /\ cstate c = cstate c1 /\
            (forall p, tape_of c p = tape_of c1 p).
Proof.
  intros n c0 c1 H. unfold seg_check in H.
  destruct (run n c0) as [c |] eqn:E; [| discriminate].
  apply config_eqb_correct in H. destruct H as [Hs Ht].
  exists c. split; [reflexivity |]. split.
  - exact Hs.
  - intros p. rewrite <- (tape_of_canon c p), <- (tape_of_canon c1 p).
    apply Ht.
Qed.

Lemma seg_no_halt : forall n c0 c1, seg_check n c0 c1 = true ->
  forall m, m < n -> exists cm, run m c0 = Some cm /\ step cm <> None.
Proof.
  intros n c0 c1 H m Hm.
  destruct (seg_check_sound _ _ _ H) as [c [E _]].
  eapply run_some_step_neq; eassumption.
Qed.

(* ---------------------------------------------------------------- *)
(* The checks.  Each is proved by vm_compute: the kernel itself      *)
(* executes the machine.  Step counts and endpoints are those of     *)
(* 168016-proof.md and reproduce_168016.py (Phase 22: all exact).    *)
(* ---------------------------------------------------------------- *)

(* Formation: R -> first I-section in exactly 150 steps. *)
Lemma seg_R_Isec : seg_check 150 cfg_R cfg_Isec = true.
Proof. vm_compute. reflexivity. Qed.

(* D(132,66) -> R in exactly 403,455 steps (the m = 132 analytic
   break of the third family; R is the post-break record config). *)
Lemma seg_D132_R : seg_check 403455 cfg_D132 cfg_R = true.
Proof. vm_compute. reflexivity. Qed.

(* Right-edge token pass at beta_E = 4: sigma_re(4) reaches the
   beta = 2 configuration H_4 in T(4) = 102 steps, and the exit
   successor X_4 six steps later. *)
Lemma seg_exit4 : seg_check 102 cfg_sre4 cfg_H4 = true.
Proof. vm_compute. reflexivity. Qed.

Lemma seg_exit4_X : seg_check 6 cfg_H4 cfg_X4 = true.
Proof. vm_compute. reflexivity. Qed.

(* Same at beta_E = 8: T(8) = 2,850. *)
Lemma seg_exit8 : seg_check 2850 cfg_sre8 cfg_H8 = true.
Proof. vm_compute. reflexivity. Qed.

Lemma seg_exit8_X : seg_check 6 cfg_H8 cfg_X8 = true.
Proof. vm_compute. reflexivity. Qed.

(* S family arrivals: blank tape first reaches S(2) at step
   197,317 and S(4) 18 steps later (period P(2) = 18). *)
Lemma seg_blank_S2 : seg_check 197317 cfg_blank cfg_S2 = true.
Proof. vm_compute. reflexivity. Qed.

Lemma seg_S2_S4 : seg_check 18 cfg_S2 cfg_S4 = true.
Proof. vm_compute. reflexivity. Qed.

(* S' family: S'(2) -> S'(4) in P(2) = 18, S'(4) -> S'(6) in
   P(4) = 42. *)
Lemma seg_Sp2_Sp4 : seg_check 18 cfg_Sp2 cfg_Sp4 = true.
Proof. vm_compute. reflexivity. Qed.

Lemma seg_Sp4_Sp6 : seg_check 42 cfg_Sp4 cfg_Sp6 = true.
Proof. vm_compute. reflexivity. Qed.

(* Semantic forms of the headline segments. *)
Corollary D132_reaches_R : exists c, run 403455 cfg_D132 = Some c /\
  cstate c = cstate cfg_R /\ (forall p, tape_of c p = tape_of cfg_R p).
Proof. apply seg_check_sound. exact seg_D132_R. Qed.

Corollary R_reaches_Isec : exists c, run 150 cfg_R = Some c /\
  cstate c = cstate cfg_Isec /\
  (forall p, tape_of c p = tape_of cfg_Isec p).
Proof. apply seg_check_sound. exact seg_R_Isec. Qed.

Corollary exit4_reaches_H4 : exists c, run 102 cfg_sre4 = Some c /\
  cstate c = cstate cfg_H4 /\ (forall p, tape_of c p = tape_of cfg_H4 p).
Proof. apply seg_check_sound. exact seg_exit4. Qed.

Corollary exit8_reaches_H8 : exists c, run 2850 cfg_sre8 = Some c /\
  cstate c = cstate cfg_H8 /\ (forall p, tape_of c p = tape_of cfg_H8 p).
Proof. apply seg_check_sound. exact seg_exit8. Qed.
