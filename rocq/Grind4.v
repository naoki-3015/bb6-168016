(* ================================================================= *)
(* Grind4.v — Phase 33: the SECOND re-basing of the ESC grind.       *)
(*                                                                   *)
(* After REBASE (Grind3.v) the re-based grind at (pb = [5],          *)
(* a2 = 13) runs clean GG rounds while j + 1 <= 13.  At residue      *)
(* R2 = 30 (R = 42) round 13 is TUP + a grind of g0 = 29 at frame    *)
(* a2 = 13 = t — the boundary case — but at pb = [5], where          *)
(* hGRIND_dev (pb = []) does not apply: the dip-bottom dispatch is   *)
(* hPX2B5, not hPUSHX, and its landing (frame [0], an extra (1, 1)   *)
(* pair, shuttle 4) differs from hGRIND_dev's (+1, +1) shift.        *)
(*                                                                   *)
(* Route (a) at pb = [5]: hGRIND_dev5 mirrors hGRIND_dev with base   *)
(* case hPX2B5.  The landing form is not uniform: at t = 0 the       *)
(* landing carries extras [(1,1),(1,2),(1,2)]; for t >= 1 the        *)
(* extras are [(1,2),(1,2),(1,2)] (each level's closing POP          *)
(* consumes the head pair), so the t = 0 and t >= 1 forms are        *)
(* stated separately.  After the deviated round, three POPs absorb   *)
(* the extras; for R2 >= 32 the grind continues with an EVEN-g0      *)
(* grind hGRIND_even (g0 = 34 at a2 = 20) and a third phase of       *)
(* clean rounds at a2 = 34 (rounds_from4).                           *)
(*                                                                   *)
(* Result: ESC_TO_REGEN endpoints for R = 42, R = 44 and every       *)
(* R = 2m + 46 with m <= 34, hence ESC_ERA_LAW_33 and the combined   *)
(* ESC_ERA_LAW_114: the ESC-era law beta |-> 2 beta + 4 for every    *)
(* even R <= 114.                                                    *)
(*                                                                   *)
(* The new fence (precise): phase 3's rounds at a2 = 34 stay clean   *)
(* while R3 <= 70.  At R3 = 72 (R2 = 104, R = 116) the boundary      *)
(* grind g0 = 71 at a2 = 34, pb = [20; 0] dips to                    *)
(*   HC [20; 0] 0 3 2 ((1, 2) :: (1, 2) :: (1, 2) :: ...)            *)
(* where NO hstep constructor applies: hPX2A requires the second     *)
(* block to be S p' >= 1 (here it is 0) and hPX2A2 requires b = 2.   *)
(* The phase21 model agrees (its PX2A guard needs p >= 2 in model    *)
(* order; verified: step returns "PX2A guard b=20 p=0").  Closing    *)
(* R >= 116 needs a NEW machine-level deviation step list at         *)
(* pb = [20; 0] (Phase-28-style derivation), a new hstep             *)
(* constructor + soundness, and a deviated grind at pb = [20; 0];    *)
(* further phases beyond it are open.                                *)
(*                                                                   *)
(* All chains were pre-verified in an hstep-level simulator          *)
(* mirroring Grind.v's 20 constructors exactly (validated against    *)
(* the proved hGRIND_dev / REBASE_core / GG_clean chains).           *)
(* ================================================================= *)

Require Import List Bool Arith Lia ZArith.
Import ListNotations.
Require Import TM Sections Mirror TokenPass Recoord Era Esc Grind Dev Grind2 Grind3.

(* ================================================================= *)
(* Part 1: the deviated grind at pb = [5] (base case hPX2B5).        *)
(* ================================================================= *)

(* t = 0: a single hPX2B5 step. *)
Lemma hGRIND_dev5_0 : forall P G,
  hsteps (HC [5] 0 3 2 P G)
         (HB [0] 4 1 4 ((1, 1) :: (1, 2) :: (1, 2) :: P) G).
Proof.
  intros P G.
  apply (hsteps_step _ (HB [0] 4 1 4 ((1, 1) :: (1, 2) :: (1, 2) :: P) G)).
  { apply hPX2B5. }
  apply hsteps_refl.
Qed.

(* t >= 1: mirror of hGRIND_dev with pb = [5]; the spine is the      *)
(* t - 1 instance at stack ((1, 2) :: P) and the closing POP eats    *)
(* the head (1, 2), leaving three (1, 2) extras.                     *)
Lemma hGRIND_dev5 : forall t P G, 1 <= t ->
  hsteps (HC [5] t (2*t + 3) 2 P G)
         (HB [0] (t + 4) 1 (2*t + 3) ((1, 2) :: (1, 2) :: (1, 2) :: P) G).
Proof.
  induction t as [t IH] using lt_wf_ind.
  intros P G Ht.
  destruct t as [|v]; [exfalso; lia|].
  destruct v as [|u].
  - (* t = 1: PUSH, TDN, TUP, hGRIND_dev5_0 spine, POP (head (1,1)). *)
    apply (hsteps_trans _ (HC [5] 0 1 2 ((3, 2) :: P) G)).
    { replace (HC [5] 1 (2*1 + 3) 2 P G)
        with (HC [5] (S 0) (S (S (S 2))) 2 P G) by sec_eq.
      replace (HC [5] 0 1 2 ((3, 2) :: P) G)
        with (HC [5] 0 1 2 ((S 2, 2) :: P) G) by sec_eq.
      apply (hsteps_step _ (HC [5] 0 1 2 ((S 2, 2) :: P) G)).
      { apply hPUSH. }
      apply hsteps_refl. }
    apply (hsteps_trans _ (HB [5] 0 1 4 ((3, 2) :: P) G)).
    { apply (hsteps_step _ (HB [5] 0 1 4 ((3, 2) :: P) G)).
      { apply hTDN. }
      apply hsteps_refl. }
    apply (hsteps_trans _ (HC [5] 0 3 2 ((1, 2) :: P) G)).
    { apply (hsteps_step _ (HC [5] 0 3 2 ((1, 2) :: P) G)).
      { replace (HB [5] 0 1 4 ((3, 2) :: P) G)
          with (HB [5] 0 1 (S (S 2)) ((S (S (S 0)), 2) :: P) G)
          by sec_eq.
        replace (HC [5] 0 3 2 ((1, 2) :: P) G)
          with (HC [5] 0 (S 2) 2 ((S 0, 2) :: P) G) by sec_eq.
        apply hTUP. }
      apply hsteps_refl. }
    apply (hsteps_trans _
      (HB [0] 4 1 4 ((1, 1) :: (1, 2) :: (1, 2) :: (1, 2) :: P) G)).
    { apply hGRIND_dev5_0. }
    apply (hsteps_step _
      (HB [0] (1 + 4) 1 (2*1 + 3) ((1, 2) :: (1, 2) :: (1, 2) :: P) G)).
    { replace (HB [0] (1 + 4) 1 (2*1 + 3) ((1, 2) :: (1, 2) :: (1, 2) :: P) G)
        with (HB [0] (S 4) 1 (4 + 1) ((1, 2) :: (1, 2) :: (1, 2) :: P) G)
        by sec_eq.
      apply hPOP; lia. }
    apply hsteps_refl.
  - (* t = S (S u): the general step, mirroring hGRIND_dev. *)
    assert (Hloop : forall k i,
      2*i + 3 + 2*k = 2 * S (S u) + 1 -> i <= S u ->
      hsteps (HC [5] (S u) (2*i + 3) 2
                 ((2 * S (S u) + 2 - (2*i + 3), 2) :: P) G)
             (HC [5] (S u) (2 * S u + 3) 2 ((1, 2) :: P) G)).
    { induction k as [|k IHk]; intros i Hk Hi.
      - replace (2 * S (S u) + 2 - (2*i + 3)) with 1 by lia.
        replace (2*i + 3) with (2 * S u + 3) by lia.
        apply hsteps_refl.
      - apply (hsteps_trans _
          (HB [5] (S u) 1 (2*i + 6)
              ((2 * S (S u) + 2 - (2*i + 3), 2) :: P) G)).
        { apply (hGRIND i [5] (S u)
                   ((2 * S (S u) + 2 - (2*i + 3), 2) :: P) G).
          lia. }
        apply (hsteps_trans _
          (HC [5] (S u) (2*(i + 1) + 3) 2
              ((2 * S (S u) + 2 - (2*(i + 1) + 3), 2) :: P) G)).
        + apply (hsteps_step _
            (HC [5] (S u) (2*(i + 1) + 3) 2
                ((2 * S (S u) + 2 - (2*(i + 1) + 3), 2) :: P) G)).
          { replace (HB [5] (S u) 1 (2*i + 6)
                ((2 * S (S u) + 2 - (2*i + 3), 2) :: P) G)
              with (HB [5] (S u) 1 (S (S (2*i + 4)))
                ((S (S (S (2 * S u - 2*i - 2))), 2) :: P) G)
              by sec_eq.
            replace (HC [5] (S u) (2*(i + 1) + 3) 2
                ((2 * S (S u) + 2 - (2*(i + 1) + 3), 2) :: P) G)
              with (HC [5] (S u) (S (2*i + 4)) 2
                ((S (2 * S u - 2*i - 2), 2) :: P) G)
              by sec_eq.
            apply hTUP. }
          apply hsteps_refl.
        + apply IHk; lia. }
    apply (hsteps_trans _ (HC [5] (S u) 1 2 ((2 * S (S u) + 1, 2) :: P) G)).
    { replace (HC [5] (S (S u)) (2 * S (S u) + 3) 2 P G)
        with (HC [5] (S (S u)) (S (S (S (2 * S (S u))))) 2 P G)
        by sec_eq.
      replace (HC [5] (S u) 1 2 ((2 * S (S u) + 1, 2) :: P) G)
        with (HC [5] (S u) 1 2 ((S (2 * S (S u)), 2) :: P) G)
        by sec_eq.
      apply (hsteps_step _ (HC [5] (S u) 1 2 ((S (2 * S (S u)), 2) :: P) G)).
      { apply hPUSH. }
      apply hsteps_refl. }
    apply (hsteps_trans _ (HB [5] (S u) 1 4 ((2 * S (S u) + 1, 2) :: P) G)).
    { apply (hsteps_step _ (HB [5] (S u) 1 4 ((2 * S (S u) + 1, 2) :: P) G)).
      { apply hTDN. }
      apply hsteps_refl. }
    apply (hsteps_trans _ (HC [5] (S u) 3 2 ((2 * S (S u) - 1, 2) :: P) G)).
    { apply (hsteps_step _ (HC [5] (S u) 3 2 ((2 * S (S u) - 1, 2) :: P) G)).
      { replace (HB [5] (S u) 1 4 ((2 * S (S u) + 1, 2) :: P) G)
          with (HB [5] (S u) 1 (S (S 2)) ((S (S (S (2 * S u))), 2) :: P) G)
          by sec_eq.
        replace (HC [5] (S u) 3 2 ((2 * S (S u) - 1, 2) :: P) G)
          with (HC [5] (S u) (S 2) 2 ((S (2 * S u), 2) :: P) G)
          by sec_eq.
        apply hTUP. }
      apply hsteps_refl. }
    apply (hsteps_trans _ (HC [5] (S u) (2 * S u + 3) 2 ((1, 2) :: P) G)).
    { pose proof (Hloop (S u) 0 ltac:(lia) ltac:(lia)) as Hc4.
      replace (2 * S (S u) + 2 - (2*0 + 3)) with (2 * S (S u) - 1) in Hc4
        by lia.
      replace (2*0 + 3) with 3 in Hc4 by lia.
      exact Hc4. }
    apply (hsteps_trans _
      (HB [0] (S u + 4) 1 (2 * S u + 3)
          ((1, 2) :: (1, 2) :: (1, 2) :: (1, 2) :: P) G)).
    { apply (IH (S u) ltac:(lia) ((1, 2) :: P) G). lia. }
    apply (hsteps_step _
      (HB [0] (S (S u) + 4) 1 (2 * S (S u) + 3)
          ((1, 2) :: (1, 2) :: (1, 2) :: P) G)).
    { replace (HB [0] (S (S u) + 4) 1 (2 * S (S u) + 3)
          ((1, 2) :: (1, 2) :: (1, 2) :: P) G)
        with (HB [0] (S (S u + 4)) 1 ((2 * S u + 3) + 2)
          ((1, 2) :: (1, 2) :: (1, 2) :: P) G)
        by sec_eq.
      apply hPOP; lia. }
    apply hsteps_refl.
Qed.

(* ================================================================= *)
(* Part 2: the even-g0 grind (phase 2 continuation at R2 >= 32).     *)
(*   HC pb (S a2) (2t + 4) 2 P G -> HB pb a2 1 (2t + 4) ((2,2)::P) G *)
(* via PUSH . TDN . TUP, a loop of (hGRIND i + TUP) reaching g0 =    *)
(* 2t + 1 over the (2, 2) pair, and spine hGRIND (t - 1).            *)
(* ================================================================= *)

Lemma hGRIND_even : forall t pb a2 P G, 1 <= t -> t <= a2 ->
  hsteps (HC pb (S a2) (2*t + 4) 2 P G)
         (HB pb a2 1 (2*t + 4) ((2, 2) :: P) G).
Proof.
  intros t pb a2 P G Ht Hf.
  assert (Hloop : forall k i,
    2*i + 3 + 2*k = 2*t + 1 -> i + 1 <= a2 ->
    hsteps (HC pb a2 (2*i + 3) 2 ((2*t - 2*i, 2) :: P) G)
           (HC pb a2 (2*t + 1) 2 ((2, 2) :: P) G)).
  { induction k as [|k IHk]; intros i Hk Hi.
    - replace (2*t - 2*i) with 2 by lia.
      replace (2*i + 3) with (2*t + 1) by lia.
      apply hsteps_refl.
    - apply (hsteps_trans _
        (HB pb a2 1 (2*i + 6) ((2*t - 2*i, 2) :: P) G)).
      { apply (hGRIND i pb a2 ((2*t - 2*i, 2) :: P) G). exact Hi. }
      apply (hsteps_trans _
        (HC pb a2 (2*(i + 1) + 3) 2 ((2*t - 2*(i + 1), 2) :: P) G)).
      + apply (hsteps_step _
          (HC pb a2 (2*(i + 1) + 3) 2 ((2*t - 2*(i + 1), 2) :: P) G)).
        { replace (HB pb a2 1 (2*i + 6) ((2*t - 2*i, 2) :: P) G)
            with (HB pb a2 1 (S (S (2*i + 4)))
                     ((S (S (S (2*t - 2*i - 3))), 2) :: P) G)
            by sec_eq.
          replace (HC pb a2 (2*(i + 1) + 3) 2 ((2*t - 2*(i + 1), 2) :: P) G)
            with (HC pb a2 (S (2*i + 4)) 2 ((S (2*t - 2*i - 3), 2) :: P) G)
            by sec_eq.
          apply hTUP. }
        apply hsteps_refl.
      + apply IHk; lia. }
  apply (hsteps_trans _ (HC pb a2 1 2 ((2*t + 2, 2) :: P) G)).
  { replace (HC pb (S a2) (2*t + 4) 2 P G)
      with (HC pb (S a2) (S (S (S (2*t + 1)))) 2 P G) by sec_eq.
    replace (HC pb a2 1 2 ((2*t + 2, 2) :: P) G)
      with (HC pb a2 1 2 ((S (2*t + 1), 2) :: P) G) by sec_eq.
    apply (hsteps_step _ (HC pb a2 1 2 ((S (2*t + 1), 2) :: P) G)).
    { apply hPUSH. }
    apply hsteps_refl. }
  apply (hsteps_trans _ (HB pb a2 1 4 ((2*t + 2, 2) :: P) G)).
  { apply (hsteps_step _ (HB pb a2 1 4 ((2*t + 2, 2) :: P) G)).
    { apply hTDN. }
    apply hsteps_refl. }
  apply (hsteps_trans _ (HC pb a2 3 2 ((2*t, 2) :: P) G)).
  { apply (hsteps_step _ (HC pb a2 3 2 ((2*t, 2) :: P) G)).
    { replace (HB pb a2 1 4 ((2*t + 2, 2) :: P) G)
        with (HB pb a2 1 (S (S 2)) ((S (S (S (2*t - 1))), 2) :: P) G)
        by sec_eq.
      replace (HC pb a2 3 2 ((2*t, 2) :: P) G)
        with (HC pb a2 (S 2) 2 ((S (2*t - 1), 2) :: P) G) by sec_eq.
      apply hTUP. }
    apply hsteps_refl. }
  apply (hsteps_trans _ (HC pb a2 (2*t + 1) 2 ((2, 2) :: P) G)).
  { pose proof (Hloop (t - 1) 0 ltac:(lia) ltac:(lia)) as Hc3.
    replace (2 * t - 2 * 0) with (2 * t) in Hc3 by lia.
    replace (2 * 0 + 3) with 3 in Hc3 by lia.
    exact Hc3. }
  apply (hsteps_trans _ (HB pb a2 1 (2*t + 4) ((2, 2) :: P) G)).
  { pose proof (hGRIND (t - 1) pb a2 ((2, 2) :: P) G ltac:(lia)) as Hc.
    replace (2*(t - 1) + 3) with (2*t + 1) in Hc by lia.
    replace (2*(t - 1) + 6) with (2*t + 4) in Hc by lia.
    exact Hc. }
  apply hsteps_refl.
Qed.

(* ================================================================= *)
(* Part 3: generalised-residue round chains.                         *)
(* rounds_from6: GG rounds from shuttle 2*j0 + 6 with an arbitrary   *)
(* residue g (GG_rounds fixes g = 2m + 2).                           *)
(* rounds_from4: phase-3 rounds from shuttle 2*j0 + 4; the floor     *)
(* j0 + m <= a2 is exact (round j calls hGRIND j at frame a2).       *)
(* ================================================================= *)

Lemma rounds_from6 : forall m j0 pb a2 g P G,
  j0 + m + 1 <= a2 -> 2*m + 2 <= g ->
  hsteps (HB pb a2 1 (2*j0 + 6) ((g, 2) :: P) G)
         (HB pb a2 1 (2*(j0 + m) + 6) ((g - 2*m, 2) :: P) G).
Proof.
  induction m as [|m IH]; intros j0 pb a2 g P G Hf Hg.
  - replace (2 * (j0 + 0) + 6) with (2*j0 + 6) by lia.
    replace (g - 2 * 0) with g by lia.
    apply hsteps_refl.
  - apply (hsteps_trans _
      (HB pb a2 1 (2*(j0 + 1) + 6) ((g - 2, 2) :: P) G)).
    + replace (HB pb a2 1 (2*j0 + 6) ((g, 2) :: P) G)
        with (HB pb a2 1 (2*(j0 + 1) + 4) ((g, 2) :: P) G)
        by sec_eq.
      apply grind_round; lia.
    + replace (HB pb a2 1 (2*(j0 + S m) + 6) ((g - 2 * S m, 2) :: P) G)
        with (HB pb a2 1 (2*((j0 + 1) + m) + 6) (((g - 2) - 2*m, 2) :: P) G)
        by sec_eq.
      apply IH; lia.
Qed.

Lemma rounds_from4 : forall m j0 pb a2 P G, j0 + m <= a2 ->
  hsteps (HB pb a2 1 (2*j0 + 4) ((2*m + 2, 2) :: P) G)
         (HB pb a2 1 (2*(j0 + m) + 4) ((2, 2) :: P) G).
Proof.
  induction m as [|m IH]; intros j0 pb a2 P G Hf.
  - replace (2 * (j0 + 0) + 4) with (2*j0 + 4) by lia.
    replace (2 * 0 + 2) with 2 by lia.
    apply hsteps_refl.
  - apply (hsteps_trans _
      (HB pb a2 1 (2*j0 + 6) ((2 * S m + 2 - 2, 2) :: P) G)).
    { apply grind_round; lia. }
    replace (HB pb a2 1 (2*j0 + 6) ((2 * S m + 2 - 2, 2) :: P) G)
      with (HB pb a2 1 (2*(j0 + 1) + 4) ((2*m + 2, 2) :: P) G) by sec_eq.
    replace (HB pb a2 1 (2*(j0 + S m) + 4) ((2, 2) :: P) G)
      with (HB pb a2 1 (2*((j0 + 1) + m) + 4) ((2, 2) :: P) G) by sec_eq.
    apply IH; lia.
Qed.

(* ================================================================= *)
(* Part 4: the deviated round 13 and the extras absorption.          *)
(* ================================================================= *)

(* Round 13 at (pb = [5], a2 = 13): TUP into the boundary grind,     *)
(* then hGRIND_dev5 13.                                              *)
Lemma round13_dev5 : forall g P G, 3 <= g ->
  hsteps (HB [5] 13 1 30 ((g, 2) :: P) G)
         (HB [0] 17 1 29 ((1, 2) :: (1, 2) :: (1, 2) :: (g - 2, 2) :: P) G).
Proof.
  intros g P G Hg.
  apply (hsteps_trans _ (HC [5] 13 29 2 ((g - 2, 2) :: P) G)).
  - apply (hsteps_step _ (HC [5] 13 29 2 ((g - 2, 2) :: P) G)).
    { replace (HB [5] 13 1 30 ((g, 2) :: P) G)
        with (HB [5] 13 1 (S (S 28)) ((S (S (S (g - 3))), 2) :: P) G)
        by sec_eq.
      replace (HC [5] 13 29 2 ((g - 2, 2) :: P) G)
        with (HC [5] 13 (S 28) 2 ((S (g - 3), 2) :: P) G) by sec_eq.
      apply hTUP. }
    apply hsteps_refl.
  - replace (HC [5] 13 29 2 ((g - 2, 2) :: P) G)
      with (HC [5] 13 (2*13 + 3) 2 ((g - 2, 2) :: P) G) by sec_eq.
    replace (HB [0] 17 1 29 ((1, 2) :: (1, 2) :: (1, 2) :: (g - 2, 2) :: P) G)
      with (HB [0] (13 + 4) 1 (2*13 + 3)
              ((1, 2) :: (1, 2) :: (1, 2) :: (g - 2, 2) :: P) G) by sec_eq.
    apply hGRIND_dev5; lia.
Qed.

(* Three POPs absorb the (1, 2) extras left by hGRIND_dev5. *)
Lemma pop3_12 : forall Q G,
  hsteps (HB [0] 17 1 29 ((1, 2) :: (1, 2) :: (1, 2) :: Q) G)
         (HB [0] 20 1 35 Q G).
Proof.
  intros Q G.
  apply (hsteps_step _ (HB [0] 18 1 31 ((1, 2) :: (1, 2) :: Q) G)).
  { apply hPOP; lia. }
  apply (hsteps_step _ (HB [0] 19 1 33 ((1, 2) :: Q) G)).
  { apply hPOP; lia. }
  apply (hsteps_step _ (HB [0] 20 1 35 Q G)).
  { apply hPOP; lia. }
  apply hsteps_refl.
Qed.

(* ================================================================= *)
(* Part 5: ESC endpoints past the second re-basing.                  *)
(* Common prefix: ESC_GRIND_BIG (R >= 12) -> REBASE -> grind_prefix  *)
(* -> rounds_from6 (12 rounds at a2 = 13) -> round13_dev5 ->         *)
(* pop3_12, landing HB [0] 20 1 35 ((R2 - 28, 2) :: Pe) with         *)
(* Pe = (1, 1) :: repeat (1, 2) (beta - 1), R2 = R - 12.             *)
(* ================================================================= *)

(* R = 42 (R2 = 30): the POP x 3 landing is exactly TAIL's source. *)
Lemma ESC_TO_REGEN_42 : forall beta, 2 <= beta ->
  exists pb a,
    hsteps (HC [] 3 1 2 ((42, 2) :: (1, 1) :: repeat (1, 2) (beta - 1)) 1)
           (HB pb a 1 (2 * beta + 1) [] 1)
    /\ beta <= a.
Proof.
  intros beta Hb.
  set (Pe := (1, 1) :: repeat (1, 2) (beta - 1)).
  exists [21; 0], (35 + beta). split; [| lia].
  apply (hsteps_trans _ (HC [] 4 12 2 ((32, 2) :: Pe) 1)).
  { replace (HC [] 4 12 2 ((32, 2) :: Pe) 1)
      with (HC [] 4 12 2 ((42 - 10, 2) :: Pe) 1) by sec_eq.
    apply ESC_GRIND_BIG. lia. }
  apply (hsteps_trans _ (HC [5] 13 1 2 ((30, 2) :: Pe) 1)).
  { replace (HC [5] 13 1 2 ((30, 2) :: Pe) 1)
      with (HC [5] 13 1 2 ((32 - 2, 2) :: Pe) 1) by sec_eq.
    apply REBASE. lia. }
  apply (hsteps_trans _ (HB [5] 13 1 6 ((28, 2) :: Pe) 1)).
  { replace (HC [5] 13 1 2 ((30, 2) :: Pe) 1)
      with (HC [5] (S 12) 1 2 ((S (S (S 27)), 2) :: Pe) 1) by sec_eq.
    replace (HB [5] 13 1 6 ((28, 2) :: Pe) 1)
      with (HB [5] (S 12) 1 6 ((S 27, 2) :: Pe) 1) by sec_eq.
    apply grind_prefix. }
  apply (hsteps_trans _ (HB [5] 13 1 30 ((4, 2) :: Pe) 1)).
  { replace (HB [5] 13 1 6 ((28, 2) :: Pe) 1)
      with (HB [5] 13 1 (2*0 + 6) ((28, 2) :: Pe) 1) by sec_eq.
    replace (HB [5] 13 1 30 ((4, 2) :: Pe) 1)
      with (HB [5] 13 1 (2*(0 + 12) + 6) ((28 - 2*12, 2) :: Pe) 1) by sec_eq.
    apply rounds_from6; lia. }
  apply (hsteps_trans _
    (HB [0] 17 1 29 ((1, 2) :: (1, 2) :: (1, 2) :: (2, 2) :: Pe) 1)).
  { replace (HB [0] 17 1 29 ((1, 2) :: (1, 2) :: (1, 2) :: (2, 2) :: Pe) 1)
      with (HB [0] 17 1 29 ((1, 2) :: (1, 2) :: (1, 2) :: (4 - 2, 2) :: Pe) 1)
      by sec_eq.
    apply round13_dev5. lia. }
  apply (hsteps_trans _ (HB [0] 20 1 35 ((2, 2) :: Pe) 1)).
  { apply pop3_12. }
  replace (HB [0] 20 1 35 ((2, 2) :: Pe) 1)
    with (HB [0] 20 1 35 ((2, 2) :: (1, 1) :: repeat (1, 2) (beta - 1)) 1)
    by (unfold Pe; reflexivity).
  apply TAIL; lia.
Qed.

(* R = 44 (R2 = 32): after POP x 3, TUP + hGRIND_even 15 (the even   *)
(* grind), then TRANS2_2 over the era stack and pop_chain_h.         *)
Lemma ESC_TO_REGEN_44 : forall beta, 2 <= beta ->
  exists pb a,
    hsteps (HC [] 3 1 2 ((44, 2) :: (1, 1) :: repeat (1, 2) (beta - 1)) 1)
           (HB pb a 1 (2 * beta + 1) [] 1)
    /\ beta <= a.
Proof.
  intros beta Hb.
  set (Pe := (1, 1) :: repeat (1, 2) (beta - 1)).
  exists [35; 20; 0], (beta + 2). split; [| lia].
  apply (hsteps_trans _ (HC [] 4 12 2 ((34, 2) :: Pe) 1)).
  { replace (HC [] 4 12 2 ((34, 2) :: Pe) 1)
      with (HC [] 4 12 2 ((44 - 10, 2) :: Pe) 1) by sec_eq.
    apply ESC_GRIND_BIG. lia. }
  apply (hsteps_trans _ (HC [5] 13 1 2 ((32, 2) :: Pe) 1)).
  { replace (HC [5] 13 1 2 ((32, 2) :: Pe) 1)
      with (HC [5] 13 1 2 ((34 - 2, 2) :: Pe) 1) by sec_eq.
    apply REBASE. lia. }
  apply (hsteps_trans _ (HB [5] 13 1 6 ((30, 2) :: Pe) 1)).
  { replace (HC [5] 13 1 2 ((32, 2) :: Pe) 1)
      with (HC [5] (S 12) 1 2 ((S (S (S 29)), 2) :: Pe) 1) by sec_eq.
    replace (HB [5] 13 1 6 ((30, 2) :: Pe) 1)
      with (HB [5] (S 12) 1 6 ((S 29, 2) :: Pe) 1) by sec_eq.
    apply grind_prefix. }
  apply (hsteps_trans _ (HB [5] 13 1 30 ((6, 2) :: Pe) 1)).
  { replace (HB [5] 13 1 6 ((30, 2) :: Pe) 1)
      with (HB [5] 13 1 (2*0 + 6) ((30, 2) :: Pe) 1) by sec_eq.
    replace (HB [5] 13 1 30 ((6, 2) :: Pe) 1)
      with (HB [5] 13 1 (2*(0 + 12) + 6) ((30 - 2*12, 2) :: Pe) 1) by sec_eq.
    apply rounds_from6; lia. }
  apply (hsteps_trans _
    (HB [0] 17 1 29 ((1, 2) :: (1, 2) :: (1, 2) :: (4, 2) :: Pe) 1)).
  { replace (HB [0] 17 1 29 ((1, 2) :: (1, 2) :: (1, 2) :: (4, 2) :: Pe) 1)
      with (HB [0] 17 1 29 ((1, 2) :: (1, 2) :: (1, 2) :: (6 - 2, 2) :: Pe) 1)
      by sec_eq.
    apply round13_dev5. lia. }
  apply (hsteps_trans _ (HB [0] 20 1 35 ((4, 2) :: Pe) 1)).
  { apply pop3_12. }
  apply (hsteps_trans _ (HC [0] 20 34 2 ((2, 2) :: Pe) 1)).
  { apply (hsteps_step _ (HC [0] 20 34 2 ((2, 2) :: Pe) 1)).
    { replace (HB [0] 20 1 35 ((4, 2) :: Pe) 1)
        with (HB [0] 20 1 (S (S 33)) ((S (S (S 1)), 2) :: Pe) 1)
        by sec_eq.
      replace (HC [0] 20 34 2 ((2, 2) :: Pe) 1)
        with (HC [0] 20 (S 33) 2 ((S 1, 2) :: Pe) 1) by sec_eq.
      apply hTUP. }
    apply hsteps_refl. }
  apply (hsteps_trans _ (HB [0] 19 1 34 ((2, 2) :: (2, 2) :: Pe) 1)).
  { replace (HC [0] 20 34 2 ((2, 2) :: Pe) 1)
      with (HC [0] (S 19) (2*15 + 4) 2 ((2, 2) :: Pe) 1) by sec_eq.
    replace (HB [0] 19 1 34 ((2, 2) :: (2, 2) :: Pe) 1)
      with (HB [0] 19 1 (2*15 + 4) ((2, 2) :: (2, 2) :: Pe) 1) by sec_eq.
    apply hGRIND_even; lia. }
  apply (hsteps_trans _
    (HB [35; 20; 0] 3 1 3 (repeat (1, 2) (beta - 1)) 1)).
  { replace (HB [0] 19 1 34 ((2, 2) :: (2, 2) :: Pe) 1)
      with (HB [0] 19 1 (S 33)
              ((2, S 1) :: (2, S 1) :: (1, 1) :: repeat (1, 2) (beta - 1)) 1)
      by (unfold Pe; sec_eq).
    replace (HB [35; 20; 0] 3 1 3 (repeat (1, 2) (beta - 1)) 1)
      with (HB (S (S 33) :: S 19 :: [0]) (S (S 1)) 1 (S 1 + 1)
              (repeat (1, 2) (beta - 1)) 1) by sec_eq.
    apply (hsteps_step _
      (HB (S (S 33) :: S 19 :: [0]) (S (S 1)) 1 (S 1 + 1)
          (repeat (1, 2) (beta - 1)) 1)).
    { apply hTRANS2_2. lia. }
    apply hsteps_refl. }
  replace (HB [35; 20; 0] (beta + 2) 1 (2 * beta + 1) [] 1)
    with (HB [35; 20; 0] (3 + (beta - 1)) 1 (3 + 2 * (beta - 1)) [] 1)
    by sec_eq.
  apply pop_chain_h. lia.
Qed.

(* R = 2m + 46 (m <= 34), i.e. R2 = 2m + 34, R3 = 2m + 2: the even   *)
(* grind leaves residue R3 + 2 at pb = [0]; TUP2_1 re-bases to       *)
(* pb = [20; 0], a2 = 34, and phase-3 rounds (rounds_from4) run      *)
(* clean while m <= 34.  Then TRANS2_1 + pop_chain_h.                *)
Lemma ESC_TO_REGEN_BIG2 : forall m beta, m <= 34 -> 2 <= beta ->
  exists pb a,
    hsteps (HC [] 3 1 2 ((2*m + 46, 2) :: (1, 1) :: repeat (1, 2) (beta - 1)) 1)
           (HB pb a 1 (2 * beta + 1) [] 1)
    /\ beta <= a.
Proof.
  intros m beta Hm Hb.
  set (Pe := (1, 1) :: repeat (1, 2) (beta - 1)).
  exists [35; 20; 0], (2*m + beta + 4). split; [| lia].
  apply (hsteps_trans _ (HC [] 4 12 2 ((2*m + 36, 2) :: Pe) 1)).
  { replace (HC [] 4 12 2 ((2*m + 36, 2) :: Pe) 1)
      with (HC [] 4 12 2 ((2*m + 46 - 10, 2) :: Pe) 1) by sec_eq.
    apply ESC_GRIND_BIG. lia. }
  apply (hsteps_trans _ (HC [5] 13 1 2 ((2*m + 34, 2) :: Pe) 1)).
  { replace (HC [5] 13 1 2 ((2*m + 34, 2) :: Pe) 1)
      with (HC [5] 13 1 2 ((2*m + 36 - 2, 2) :: Pe) 1) by sec_eq.
    apply REBASE. lia. }
  apply (hsteps_trans _ (HB [5] 13 1 6 ((2*m + 32, 2) :: Pe) 1)).
  { replace (HC [5] 13 1 2 ((2*m + 34, 2) :: Pe) 1)
      with (HC [5] (S 12) 1 2 ((S (S (S (2*m + 31))), 2) :: Pe) 1) by sec_eq.
    replace (HB [5] 13 1 6 ((2*m + 32, 2) :: Pe) 1)
      with (HB [5] (S 12) 1 6 ((S (2*m + 31), 2) :: Pe) 1) by sec_eq.
    apply grind_prefix. }
  apply (hsteps_trans _ (HB [5] 13 1 30 ((2*m + 8, 2) :: Pe) 1)).
  { replace (HB [5] 13 1 6 ((2*m + 32, 2) :: Pe) 1)
      with (HB [5] 13 1 (2*0 + 6) ((2*m + 32, 2) :: Pe) 1) by sec_eq.
    replace (HB [5] 13 1 30 ((2*m + 8, 2) :: Pe) 1)
      with (HB [5] 13 1 (2*(0 + 12) + 6) ((2*m + 32 - 2*12, 2) :: Pe) 1)
      by sec_eq.
    apply rounds_from6; lia. }
  apply (hsteps_trans _
    (HB [0] 17 1 29 ((1, 2) :: (1, 2) :: (1, 2) :: (2*m + 6, 2) :: Pe) 1)).
  { replace (HB [0] 17 1 29
        ((1, 2) :: (1, 2) :: (1, 2) :: (2*m + 6, 2) :: Pe) 1)
      with (HB [0] 17 1 29
        ((1, 2) :: (1, 2) :: (1, 2) :: (2*m + 8 - 2, 2) :: Pe) 1)
      by sec_eq.
    apply round13_dev5. lia. }
  apply (hsteps_trans _ (HB [0] 20 1 35 ((2*m + 6, 2) :: Pe) 1)).
  { apply pop3_12. }
  apply (hsteps_trans _ (HC [0] 20 34 2 ((2*m + 4, 2) :: Pe) 1)).
  { apply (hsteps_step _ (HC [0] 20 34 2 ((2*m + 4, 2) :: Pe) 1)).
    { replace (HB [0] 20 1 35 ((2*m + 6, 2) :: Pe) 1)
        with (HB [0] 20 1 (S (S 33)) ((S (S (S (2*m + 3))), 2) :: Pe) 1)
        by sec_eq.
      replace (HC [0] 20 34 2 ((2*m + 4, 2) :: Pe) 1)
        with (HC [0] 20 (S 33) 2 ((S (2*m + 3), 2) :: Pe) 1) by sec_eq.
      apply hTUP. }
    apply hsteps_refl. }
  apply (hsteps_trans _ (HB [0] 19 1 34 ((2, 2) :: (2*m + 4, 2) :: Pe) 1)).
  { replace (HC [0] 20 34 2 ((2*m + 4, 2) :: Pe) 1)
      with (HC [0] (S 19) (2*15 + 4) 2 ((2*m + 4, 2) :: Pe) 1) by sec_eq.
    replace (HB [0] 19 1 34 ((2, 2) :: (2*m + 4, 2) :: Pe) 1)
      with (HB [0] 19 1 (2*15 + 4) ((2, 2) :: (2*m + 4, 2) :: Pe) 1) by sec_eq.
    apply hGRIND_even; lia. }
  apply (hsteps_trans _ (HC [20; 0] 34 1 2 ((2*m + 2, 2) :: Pe) 1)).
  { apply (hsteps_step _ (HC [20; 0] 34 1 2 ((2*m + 2, 2) :: Pe) 1)).
    { replace (HB [0] 19 1 34 ((2, 2) :: (2*m + 4, 2) :: Pe) 1)
        with (HB [0] 19 1 (S 33)
                ((2, S (S 0)) :: (S (S (S (2*m + 1))), 2) :: Pe) 1)
        by sec_eq.
      replace (HC [20; 0] 34 1 2 ((2*m + 2, 2) :: Pe) 1)
        with (HC (S 19 :: [0]) (S 33) (S 0) 2 ((S (2*m + 1), 2) :: Pe) 1)
        by sec_eq.
      apply hTUP2_1. }
    apply hsteps_refl. }
  apply (hsteps_trans _ (HB [20; 0] 34 1 4 ((2*m + 2, 2) :: Pe) 1)).
  { apply (hsteps_step _ (HB [20; 0] 34 1 4 ((2*m + 2, 2) :: Pe) 1)).
    { apply hTDN. }
    apply hsteps_refl. }
  apply (hsteps_trans _ (HB [20; 0] 34 1 (2*m + 4) ((2, 2) :: Pe) 1)).
  { replace (HB [20; 0] 34 1 4 ((2*m + 2, 2) :: Pe) 1)
      with (HB [20; 0] 34 1 (2*0 + 4) ((2*m + 2, 2) :: Pe) 1) by sec_eq.
    replace (HB [20; 0] 34 1 (2*m + 4) ((2, 2) :: Pe) 1)
      with (HB [20; 0] 34 1 (2*(0 + m) + 4) ((2, 2) :: Pe) 1) by sec_eq.
    apply rounds_from4. exact Hm. }
  apply (hsteps_trans _
    (HB [35; 20; 0] (2*m + 5) 1 3 (repeat (1, 2) (beta - 1)) 1)).
  { replace (HB [20; 0] 34 1 (2*m + 4) ((2, 2) :: Pe) 1)
      with (HB [20; 0] 34 1 (S (2*m + 3))
              ((2, S 1) :: (1, 1) :: repeat (1, 2) (beta - 1)) 1)
      by (unfold Pe; sec_eq).
    replace (HB [35; 20; 0] (2*m + 5) 1 3 (repeat (1, 2) (beta - 1)) 1)
      with (HB (S 34 :: [20; 0]) (S (S (2*m + 3))) 1 (S 1 + 1)
              (repeat (1, 2) (beta - 1)) 1) by sec_eq.
    apply (hsteps_step _
      (HB (S 34 :: [20; 0]) (S (S (2*m + 3))) 1 (S 1 + 1)
          (repeat (1, 2) (beta - 1)) 1)).
    { apply hTRANS2_1. lia. }
    apply hsteps_refl. }
  replace (HB [35; 20; 0] (2*m + beta + 4) 1 (2 * beta + 1) [] 1)
    with (HB [35; 20; 0] (2*m + 5 + (beta - 1)) 1 (3 + 2 * (beta - 1)) [] 1)
    by sec_eq.
  apply pop_chain_h. lia.
Qed.

(* ================================================================= *)
(* Part 6: the ESC-era law past the second re-basing.                *)
(* ================================================================= *)

(* The second-re-basing range: R = 42, 44, and R = 2m + 46 (m <= 34),*)
(* i.e. every even R with 42 <= R <= 114.                            *)
Lemma ESC_ERA_LAW_33 : forall R beta,
  (R = 42 \/ R = 44 \/ (exists m, R = 2 * m + 46 /\ m <= 34)) -> 2 <= beta ->
  exists n c pb a, run n (esc_src (R + 6) (beta - 2)) = Some c
    /\ cfg_sim c (rcsec (false :: repeat true (S a) ++ enc pb)
                        (2 * beta + 2) [(1, 2)])
    /\ beta <= a.
Proof.
  intros R beta HR Hb.
  destruct HR as [E42 | [E44 | HM]].
  - subst R. destruct (ESC_TO_REGEN_42 beta Hb) as [pb [a [Hc Hf]]].
    apply (ESC_ERA_LAW_of 42 beta pb a); [lia | exact Hc | exact Hf | exact Hb].
  - subst R. destruct (ESC_TO_REGEN_44 beta Hb) as [pb [a [Hc Hf]]].
    apply (ESC_ERA_LAW_of 44 beta pb a); [lia | exact Hc | exact Hf | exact Hb].
  - destruct HM as [m [ER Hm]]. subst R.
    destruct (ESC_TO_REGEN_BIG2 m beta Hm Hb) as [pb [a [Hc Hf]]].
    apply (ESC_ERA_LAW_of (2 * m + 46) beta pb a);
      [lia | exact Hc | exact Hf | exact Hb].
Qed.

(* The combined ESC-era law: every even R <= 114 (Phase 31's range   *)
(* together with Phase 33's).                                        *)
Lemma ESC_ERA_LAW_114 : forall R beta,
  (R = 2 \/ R = 4 \/ R = 6 \/ R = 8 \/ R = 10 \/ R = 12 \/ R = 14
   \/ (exists m, R = 2 * m + 16 /\ m <= 12)
   \/ R = 42 \/ R = 44 \/ (exists m, R = 2 * m + 46 /\ m <= 34))
  -> 2 <= beta ->
  exists n c pb a, run n (esc_src (R + 6) (beta - 2)) = Some c
    /\ cfg_sim c (rcsec (false :: repeat true (S a) ++ enc pb)
                        (2 * beta + 2) [(1, 2)])
    /\ beta <= a.
Proof.
  intros R beta HR Hb.
  destruct HR as [E | [E | [E | [E | [E | [E | [E | [HM | HR]]]]]]]].
  - apply (ESC_ERA_LAW_31 R beta); [left; exact E | exact Hb].
  - apply (ESC_ERA_LAW_31 R beta); [right; left; exact E | exact Hb].
  - apply (ESC_ERA_LAW_31 R beta); [do 2 right; left; exact E | exact Hb].
  - apply (ESC_ERA_LAW_31 R beta); [do 3 right; left; exact E | exact Hb].
  - apply (ESC_ERA_LAW_31 R beta); [do 4 right; left; exact E | exact Hb].
  - apply (ESC_ERA_LAW_31 R beta); [do 5 right; left; exact E | exact Hb].
  - apply (ESC_ERA_LAW_31 R beta); [do 6 right; left; exact E | exact Hb].
  - apply (ESC_ERA_LAW_31 R beta); [do 7 right; exact HM | exact Hb].
  - apply (ESC_ERA_LAW_33 R beta); [exact HR | exact Hb].
Qed.

(* ----------------------------------------------------------------- *)
(* Axiom audit                                                       *)
(* ----------------------------------------------------------------- *)

Print Assumptions hGRIND_dev5_0.
Print Assumptions hGRIND_dev5.
Print Assumptions hGRIND_even.
Print Assumptions rounds_from6.
Print Assumptions rounds_from4.
Print Assumptions round13_dev5.
Print Assumptions pop3_12.
Print Assumptions ESC_TO_REGEN_42.
Print Assumptions ESC_TO_REGEN_44.
Print Assumptions ESC_TO_REGEN_BIG2.
Print Assumptions ESC_ERA_LAW_33.
Print Assumptions ESC_ERA_LAW_114.
