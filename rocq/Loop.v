(* ================================================================= *)
(*  Loop.v -- the cross-era loop assembly (Phase 32).                *)
(*                                                                   *)
(*  The human proof (168016-proof.md SS3-SS4, post-exit-analysis.md, *)
(*  phase19-derivations.md SS2-SS3, phase21-derivations.md) closes   *)
(*  the post-R dynamics into a single ascending loop:                *)
(*                                                                   *)
(*    right-edge entry section (beta)                                *)
(*      -> token pass + beta = 2 exit            (#14, #15)          *)
(*      -> re-coordinatisation                   (#16)               *)
(*      -> era in the single-block frame                             *)
(*         settled era:  beta' = 2 beta + 34     (#18, rho = 29)     *)
(*         ESC era:      beta' = 2 beta + 4      (#19)               *)
(*      -> right-edge entry section (beta'),  beta' > beta           *)
(*                                                                   *)
(*  This file composes the mechanised components into that loop:     *)
(*                                                                   *)
(*   - PASS: the exit + stage 1 + stage 2, for an ARBITRARY frozen   *)
(*     prefix (STAGE1_exit of Recoord.v composed with DSTAGE2 of     *)
(*     DiagPass.v), landing on the escape section.  The escape       *)
(*     section over a single-block prefix is DEFINITIONALLY          *)
(*     Esc.esc_src (Lemma esc_bridge), so the ESC era law applies    *)
(*     with no further step list.                                    *)
(*   - SETTLED_ITER: one full settled iteration at the trajectory's  *)
(*     two-block prefix entryP 31 (RECOORD2_uncond + ERA_LAW):       *)
(*     beta = n + 2  |->  beta' = 2n + 38, landing on an entry        *)
(*     section whose frozen prefix is the single block 0 1^(n+19).   *)
(*   - SETTLED_ITER_GEN: the same iteration at a general two-block   *)
(*     prefix entryP B2, conditional on ERA_GEN -- the general-      *)
(*     residue era law (human: phase19 SS2, s1 = rho + 2 beta_E + 2, *)
(*     beta' = rho + 2 beta_E + 5), mechanised only at rho = 29      *)
(*     (ERA_LAW; the rho = 29 instance in ERA_GEN shape is           *)
(*     ERA_LAW_GEN below).  beta = n + 2  |->  beta' = B2 + 2n + 7.  *)
(*   - SETTLED_ITER_GEN_odd (Phase 35): the same iteration with      *)
(*     ERA_GEN discharged on its proved domain (EraGen.v:           *)
(*     ERA_GEN_proved for odd rho <= 33) -- unconditional for odd    *)
(*     B2 with 3 <= B2 <= 35.                                      *)
(*   - SETTLED_ITER_GEN_even (Phase 39): the same iteration at an    *)
(*     even prefix, via EraEven.v's ERA_GEN_even (the even era       *)
(*     law: the absorption rotates at the residue pair's gap 2,      *)
(*     s1 = 2m + 1, beta' = 2 beta + 4 independent of B2) --          *)
(*     unconditional for even B2 with 4 <= B2 <= 36.  With the       *)
(*     odd case, the settled iteration is unconditional for every    *)
(*     B2 with 3 <= B2 <= 36; only B2 >= 37 remains conditional.     *)
(*   - ESC_ITER: one full ESC iteration at a single-block prefix     *)
(*     (PASS + esc_bridge + ESC_ERA_LAW_31 of Grind3.v):             *)
(*     beta  |->  beta' = 2 beta + 4, for the residue                *)
(*     R = L - 6 in ESC_ERA_LAW_31's range (every even R <= 40).     *)
(*   - ESC_ITER_114 (Phase 33): the same iteration via               *)
(*     ESC_ERA_LAW_114 of Grind4.v (the second re-basing):           *)
(*     beta  |->  beta' = 2 beta + 4 for every even R <= 114.        *)
(*   - ESC_ITER_268 (Phase 37): the same iteration via               *)
(*     ESC_ERA_LAW_268 of Grind6.v (the third re-basing's merged     *)
(*     unwind at R = 116 and the phase-4/5 continuations):           *)
(*     beta  |->  beta' = 2 beta + 4 for every even R <= 268.        *)
(*   - ESC_ITER_602 (Phase 38): the same iteration via               *)
(*     ESC_ERA_LAW_602 of Grind7.v (the phase-6 merged unwind:       *)
(*     DIPDESC at [41; 14; 5], hPX2A, GRIND39_MID and the new-frame   *)
(*     finishes): beta  |->  beta' = 2 beta + 4 for every even        *)
(*     R <= 602.                                                     *)
(*   - TWO_ITERS: the first two loop iterations composed from the    *)
(*     entry landing entry_tgt 30 n, for n = 2j + 3, j <= 12         *)
(*     (so iteration 2's residue R = n + 13 = 2j + 16 <= 40):        *)
(*     beta = n + 2  |->  beta'' = 4n + 80.  Fully proved.           *)
(*   - LOOP_NONHALT: the abstract ascending-loop engine.  Given      *)
(*     loop_step at every entry section with beta >= 4, the run      *)
(*     from any entry section is total (defined for all N), via      *)
(*     chains of strictly increasing length (loop_chain).            *)
(*   - NONHALT_FROM_R: the headline assembly.  From the record       *)
(*     configuration R (cfg_R), the formation segment to the first   *)
(*     I-section is Finite.v's kernel-verified 150 steps             *)
(*     (R_reaches_Isec); what remains open is stated as two          *)
(*     explicit hypotheses (never axioms, never admits):             *)
(*       (H_STD)  from the first I-section cfg_Isec, the standard    *)
(*                regime reaches cfg_sim of some entry landing       *)
(*                entry_tgt (B2 - 1) n with B2 >= 3, n >= 2 --       *)
(*                component #10's assembly (totality and I+          *)
(*                preservation of the five standard rules in the     *)
(*                wall frame) plus the G-descent to the w = [1],     *)
(*                G = 2 exit of #11; human-proved in                 *)
(*                bounce-derivation.md / reexpansion-derivation.md,  *)
(*                not yet mechanised;                              *)
(*       (H_LOOP) loop_step at every entry section with beta >= 4.   *)
(*     H_LOOP is DISCHARGED above for: settled entries entryP B2     *)
(*     at B2 = 31 (fully) and at general B2 -- unconditionally for   *)
(*     every 3 <= B2 <= 36 (odd B2 <= 35: SETTLED_ITER_GEN_odd,      *)
(*     Phase 35, via ERA_GEN_proved; even B2, 4 <= B2 <= 36:         *)
(*     SETTLED_ITER_GEN_even, Phase 39, via ERA_GEN_even),           *)
(*     conditionally on the unrestricted ERA_GEN for B2 >= 37;       *)
(*     ESC entries at single-block                                   *)
(*     prefixes with R <= 40 (fully, ESC_ITER) and with every even  *)
(*     R <= 114 (fully, ESC_ITER_114, Phase 33) and with every even  *)
(*     R <= 268 (fully, ESC_ITER_268, Phase 37) and with every even  *)
(*     R <= 602 (fully, ESC_ITER_602, Phase 38).  The undischarged   *)
(*     instances are exactly: ESC entries with R >= 604 (the         *)
(*     phase-6 finish's rounds and final grind at the new frame      *)
(*     [110; 19; 0] hit their floors at m = 279 -- a phase-7         *)
(*     deviation, fenced in Grind7.v),                               *)
(*     settled entries at entryP B2 with B2 >= 37 (residues          *)
(*     beyond the frame-16 era laws of both parities, fenced in      *)
(*     EraGen.v / EraEven.v), and entry sections whose prefix is     *)
(*     an ESC-era                                                  *)
(*     landing form 0 1^(a+1) ++ enc pb (iterations >= 3: their      *)
(*     re-formation is the canonical two-block grind at general      *)
(*     residue -- ERA_GEN on its domain plus stage 3 at a general    *)
(*     far block).                                                   *)
(*                                                                   *)
(*  The theorem is stated from cfg_R: the blank-tape -> R segment    *)
(*  (components #1-#5) is not mechanised (see the status doc).       *)
(*  The #18 dip clause as a sequence statement is NOT used by this   *)
(*  assembly: ERA_LAW discharges GRIND's floor hypothesis directly   *)
(*  at every application, as recorded in Era.v.                      *)
(* ================================================================= *)

Require Import List Bool Arith Lia ZArith.
Import ListNotations.
Require Import TM Configs Finite Sections Mirror TokenPass DiagPass
               Recoord Era EraGen EraEven Esc Dev Grind Grind2 Grind3
               Grind4 Grind5 Grind6 Grind7.

(* ----------------------------------------------------------------- *)
(* Part 0: run-totality infrastructure.                              *)
(* ----------------------------------------------------------------- *)

(* Composition of two runs across a cfg_sim step (the second run is  *)
(* stated at the clean form, the first lands cfg_sim to it).         *)
Lemma run_trans_sim : forall t1 t2 c1 c2 c3 d,
  run t1 c1 = Some c2 -> cfg_sim c2 c3 -> run t2 c3 = Some d ->
  exists d', run (t1 + t2) c1 = Some d' /\ cfg_sim d' d.
Proof.
  intros t1 t2 c1 c2 c3 d Hr1 Hs Hr2.
  destruct (run_sim_transfer t2 c2 c3 d Hs Hr2) as [d' [Hr Hd']].
  exists d'. split; [| exact Hd'].
  rewrite run_split. rewrite Hr1. exact Hr.
Qed.

(* If the run from s is total and c1 reaches a cfg_sim of s, the     *)
(* run from c1 is total.                                             *)
Lemma total_transfer : forall c0 c1 s t0,
  run t0 c0 = Some c1 -> cfg_sim c1 s ->
  (forall N, exists c, run N s = Some c) ->
  forall N, exists c, run N c0 = Some c.
Proof.
  intros c0 c1 s t0 Hr Hs Htot N.
  destruct (Htot N) as [cN HN].
  destruct (run_sim_transfer N c1 s cN Hs HN) as [cN' [HN' _]].
  assert (Hbig : run (N + t0) c0 = Some cN').
  { replace (N + t0) with (t0 + N) by lia.
    rewrite run_split. rewrite Hr. exact HN'. }
  rewrite run_split in Hbig.
  destruct (run N c0) as [c |] eqn:E; [exists c; reflexivity | discriminate].
Qed.

(* ----------------------------------------------------------------- *)
(* Part 1: entry sections and the loop step.                         *)
(* ----------------------------------------------------------------- *)

(* The right-edge entry section with entry parameter beta >= 2:      *)
(* the rcsec b2 argument is beta - 2, the word is the single pair    *)
(* (1, 2) -- Mirror.v's ENTRY landing form (ENTRY_tape, sim_entry).  *)
Definition entry_sec (P : list sym) (beta : nat) : config :=
  rcsec P (beta - 2) [(1, 2)].

(* One full loop iteration: a positive-length run from the entry     *)
(* section to cfg_sim of an entry section with strictly larger       *)
(* beta (hence strictly larger span: the entry section's beta        *)
(* block has length beta).                                           *)
Definition loop_step (P : list sym) (beta : nat) : Prop :=
  exists P' beta' t c, 1 <= t
    /\ run t (entry_sec P beta) = Some c
    /\ cfg_sim c (entry_sec P' beta')
    /\ beta < beta'.

(* ----------------------------------------------------------------- *)
(* Part 2: PASS -- exit + stage 1 + stage 2, arbitrary prefix.       *)
(* ----------------------------------------------------------------- *)

Lemma PASS : forall P K, 2 <= K -> exists c,
  run ((Tk K + 6) + (2*K*K + 13*K + 14) + Tk K)
      (rcsec P K ((1, 2) :: [])) = Some c
  /\ cfg_sim c (rcsec P 0 ((3, 2) :: repeat (1, 2) K)).
Proof.
  intros P K HK.
  destruct (STAGE1_exit P K HK) as [c1 [Hrun1 Hsim1]].
  destruct (DSTAGE2 P K HK) as [c2 [Hrun2 Hsim2]].
  destruct (run_sim_transfer _ _ _ _ Hsim1 Hrun2) as [c2' [Hr2' Hs2']].
  exists c2'. split.
  - rewrite run_split. rewrite Hrun1. exact Hr2'.
  - eapply cfg_sim_trans; eassumption.
Qed.

(* The escape section over a single-block prefix IS Esc.esc_src:     *)
(* both are mkCfg SC (0 :: 1^L) (1 1 0^3 1^2 (0 1^2)^m) -- the        *)
(* rcsec form's leading 1 1 is the beta block's last two cells.      *)
Lemma esc_bridge : forall L m,
  rcsec (false :: repeat true L) 0 ((3, 2) :: repeat (1, 2) m)
  = esc_src L m.
Proof. intros L m. reflexivity. Qed.

(* ----------------------------------------------------------------- *)
(* Part 3: the settled iteration.                                    *)
(* ----------------------------------------------------------------- *)

(* One settled iteration at the trajectory prefix entryP 31: the     *)
(* pass (inside RECOORD2_uncond) + the settled era (ERA_LAW at era   *)
(* parameter n + 2).  beta = n + 2  |->  beta' = 2n + 38 = 2 beta +   *)
(* 34, and the next entry prefix is the single block 0 1^(n+19).     *)
Lemma SETTLED_ITER : forall n, 2 <= n -> exists t c,
  run t (entry_sec (entryP 31) (n + 2)) = Some c
  /\ cfg_sim c (entry_sec (false :: repeat true (n + 19)) (2 * n + 38))
  /\ 1 <= t.
Proof.
  intros n Hn.
  assert (Hsrc : entry_sec (entryP 31) (n + 2)
                 = rcsec (entryP 31) n [(1, 2)]).
  { unfold entry_sec. replace (n + 2 - 2) with n by lia. reflexivity. }
  assert (Hsim : cfg_sim (rcsec (entryP 31) n [(1, 2)])
                         (entry_tgt 30 n)).
  { apply cfg_sim_sym. exact (sim_entry 30 n). }
  destruct (RECOORD2_uncond 31 n ltac:(lia) Hn) as [c1 [Hr1 Hs1]].
  destruct (run_sim_transfer _ _ _ _ Hsim Hr1) as [c1' [Hr1' Hs1']].
  assert (Hsim1 : cfg_sim c1' (csec 16 29 2 ((1, 1) :: repeat (1, 2) (S n)) 1))
    by (eapply cfg_sim_trans; eassumption).
  destruct (ERA_LAW (n + 2) ltac:(lia)) as [cost [c2 [Hr2 Hs2]]].
  replace (n + 2 - 1) with (S n) in Hr2 by lia.
  destruct (run_trans_sim _ _ _ _ _ _ Hr1' Hsim1 Hr2) as [c2' [Hr HsT]].
  assert (Hs : cfg_sim c2' (rcsec (false :: repeat true (n + 2 + 17) ++ [])
                                  (2 * (n + 2) + 32) [(1, 2)]))
    by (eapply cfg_sim_trans; eassumption).
  assert (Hfin : rcsec (false :: repeat true (n + 2 + 17) ++ [])
                       (2 * (n + 2) + 32) [(1, 2)]
                 = entry_sec (false :: repeat true (n + 19)) (2 * n + 38)).
  { unfold entry_sec.
    replace (n + 2 + 17) with (n + 19) by lia.
    replace (2 * (n + 2) + 32) with (2 * n + 36) by lia.
    replace (2 * n + 38 - 2) with (2 * n + 36) by lia.
    rewrite app_nil_r. reflexivity. }
  rewrite Hfin in Hs.
  rewrite <- Hsrc in Hr.
  eexists. exists c2'. split; [exact Hr |]. split; [exact Hs | lia].
Qed.

Lemma SETTLED_ITER_step : forall n, 2 <= n -> loop_step (entryP 31) (n + 2).
Proof.
  intros n Hn. destruct (SETTLED_ITER n Hn) as [t [c [Hr [Hs Ht]]]].
  unfold loop_step.
  exists (false :: repeat true (n + 19)), (2 * n + 38), t, c.
  split; [exact Ht |]. split; [exact Hr |]. split; [exact Hs | lia].
Qed.

(* The general-residue era law, in exactly ERA_LAW's shape with the  *)
(* residue rho as a parameter (human form, phase19 SS2:              *)
(* s1 = rho + 2 beta_E + 2, beta' = rho + 2 beta_E + 5, i.e. the      *)
(* landing's rcsec argument is rho + 2 beta_E + 3).  Mechanised      *)
(* at rho = 29 (ERA_LAW) in Phase 27, and -- Phase 35 -- at every    *)
(* odd rho <= 33 in EraGen.v (ERA_GEN_proved: the residue grind's    *)
(* floor at the fixed frame a2 = 16 and the Stage-A era's G parity   *)
(* bound the domain exactly; even rho and rho >= 35 are fenced       *)
(* there with machine-checked obstructions).  The unrestricted       *)
(* statement below remains as the explicit hypothesis of the         *)
(* conditional SETTLED_ITER_GEN; SETTLED_ITER_GEN_odd discharges     *)
(* the same iteration unconditionally on the proved domain.          *)
Definition ERA_GEN : Prop :=
  forall rho m, 1 <= m -> exists P' cost c,
    run cost (csec 16 rho 2 ((1, 1) :: repeat (1, 2) (m - 1)) 1) = Some c
    /\ cfg_sim c (rcsec P' (rho + 2 * m + 3) [(1, 2)]).

(* The rho = 29 instance of ERA_GEN's shape is ERA_LAW itself.       *)
Lemma ERA_LAW_GEN : forall m, 1 <= m -> exists P' cost c,
  run cost (csec 16 29 2 ((1, 1) :: repeat (1, 2) (m - 1)) 1) = Some c
  /\ cfg_sim c (rcsec P' (29 + 2 * m + 3) [(1, 2)]).
Proof.
  intros m Hm. destruct (ERA_LAW m Hm) as [cost [c [Hr Hs]]].
  exists (false :: repeat true (m + 17) ++ []), cost, c.
  split; [exact Hr |].
  replace (29 + 2 * m + 3) with (2 * m + 32) by lia. exact Hs.
Qed.

(* One settled iteration at a general two-block prefix entryP B2,    *)
(* conditional on ERA_GEN: beta = n + 2  |->  beta' = B2 + 2n + 7    *)
(* (= rho + 2 beta_E + 5 at rho = B2 - 2, beta_E = n + 2).           *)
Lemma SETTLED_ITER_GEN : ERA_GEN -> forall B2 n, 3 <= B2 -> 2 <= n ->
  exists P' t c,
    run t (entry_sec (entryP B2) (n + 2)) = Some c
    /\ cfg_sim c (entry_sec P' (B2 + 2 * n + 7))
    /\ 1 <= t.
Proof.
  intros Hgen B2 n HB2 Hn.
  assert (Hsrc : entry_sec (entryP B2) (n + 2)
                 = rcsec (entryP B2) n [(1, 2)]).
  { unfold entry_sec. replace (n + 2 - 2) with n by lia. reflexivity. }
  pose proof (sim_entry (B2 - 1) n) as Hse.
  replace (S (B2 - 1)) with B2 in Hse by lia.
  assert (Hsim : cfg_sim (rcsec (entryP B2) n [(1, 2)])
                         (entry_tgt (B2 - 1) n)).
  { apply cfg_sim_sym. exact Hse. }
  destruct (RECOORD2_uncond B2 n HB2 Hn) as [c1 [Hr1 Hs1]].
  destruct (run_sim_transfer _ _ _ _ Hsim Hr1) as [c1' [Hr1' Hs1']].
  assert (Hsim1 : cfg_sim c1'
    (csec 16 (B2 - 2) 2 ((1, 1) :: repeat (1, 2) (S n)) 1))
    by (eapply cfg_sim_trans; eassumption).
  destruct (Hgen (B2 - 2) (n + 2) ltac:(lia)) as [P' [cost [c2 [Hr2 Hs2]]]].
  replace (n + 2 - 1) with (S n) in Hr2 by lia.
  destruct (run_trans_sim _ _ _ _ _ _ Hr1' Hsim1 Hr2) as [c2' [Hr HsT]].
  assert (Hs : cfg_sim c2' (rcsec P' (B2 - 2 + 2 * (n + 2) + 3) [(1, 2)]))
    by (eapply cfg_sim_trans; eassumption).
  assert (Hfin : rcsec P' (B2 - 2 + 2 * (n + 2) + 3) [(1, 2)]
                 = entry_sec P' (B2 + 2 * n + 7)).
  { unfold entry_sec.
    replace (B2 - 2 + 2 * (n + 2) + 3) with (B2 + 2 * n + 5) by lia.
    replace (B2 + 2 * n + 7 - 2) with (B2 + 2 * n + 5) by lia.
    reflexivity. }
  rewrite Hfin in Hs.
  rewrite <- Hsrc in Hr.
  exists P'. eexists. exists c2'. split; [exact Hr |].
  split; [exact Hs | lia].
Qed.

Lemma SETTLED_ITER_GEN_step : ERA_GEN ->
  forall B2 n, 3 <= B2 -> 2 <= n -> loop_step (entryP B2) (n + 2).
Proof.
  intros Hgen B2 n HB2 Hn.
  destruct (SETTLED_ITER_GEN Hgen B2 n HB2 Hn) as [P' [t [c [Hr [Hs Ht]]]]].
  unfold loop_step.
  exists P', (B2 + 2 * n + 7), t, c.
  split; [exact Ht |]. split; [exact Hr |]. split; [exact Hs | lia].
Qed.

(* Phase 35: the same settled iteration at a general two-block       *)
(* prefix, UNCONDITIONAL on ERA_GEN's proved domain.  The residue    *)
(* is rho = B2 - 2; ERA_GEN_proved (EraGen.v) covers odd rho <= 33,  *)
(* i.e. B2 odd with 3 <= B2 <= 35 (B2 = 31, the trajectory's block,   *)
(* is the ERA_LAW case).  Phase 39 (below) discharges the even       *)
(* prefixes 4 <= B2 <= 36 by a different-shaped era law              *)
(* (EraEven.v); B2 >= 37 (rho >= 35: the residue grind's dip         *)
(* exceeds the frame a2 = 16 in both parities) remains the           *)
(* conditional SETTLED_ITER_GEN above, i.e. an undischarged          *)
(* instance of H_LOOP; such prefixes arise only inside the           *)
(* iterations >= 3 re-formation.                                     *)
Lemma SETTLED_ITER_GEN_odd : forall B2 n,
  Nat.Odd B2 -> B2 <= 35 -> 3 <= B2 -> 2 <= n ->
  exists P' t c,
    run t (entry_sec (entryP B2) (n + 2)) = Some c
    /\ cfg_sim c (entry_sec P' (B2 + 2 * n + 7))
    /\ 1 <= t.
Proof.
  intros B2 n Hodd HB2le HB2 Hn.
  assert (Hsrc : entry_sec (entryP B2) (n + 2)
                 = rcsec (entryP B2) n [(1, 2)]).
  { unfold entry_sec. replace (n + 2 - 2) with n by lia. reflexivity. }
  pose proof (sim_entry (B2 - 1) n) as Hse.
  replace (S (B2 - 1)) with B2 in Hse by lia.
  assert (Hsim : cfg_sim (rcsec (entryP B2) n [(1, 2)])
                         (entry_tgt (B2 - 1) n)).
  { apply cfg_sim_sym. exact Hse. }
  destruct (RECOORD2_uncond B2 n HB2 Hn) as [c1 [Hr1 Hs1]].
  destruct (run_sim_transfer _ _ _ _ Hsim Hr1) as [c1' [Hr1' Hs1']].
  assert (Hsim1 : cfg_sim c1'
    (csec 16 (B2 - 2) 2 ((1, 1) :: repeat (1, 2) (S n)) 1))
    by (eapply cfg_sim_trans; eassumption).
  assert (Hodd2 : Nat.Odd (B2 - 2)).
  { destruct Hodd as [u Hu]. exists (u - 1). lia. }
  destruct (ERA_GEN_proved (B2 - 2) (n + 2) Hodd2 ltac:(lia) ltac:(lia))
    as [P' [cost [c2 [Hr2 Hs2]]]].
  replace (n + 2 - 1) with (S n) in Hr2 by lia.
  destruct (run_trans_sim _ _ _ _ _ _ Hr1' Hsim1 Hr2) as [c2' [Hr HsT]].
  assert (Hs : cfg_sim c2' (rcsec P' (B2 - 2 + 2 * (n + 2) + 3) [(1, 2)]))
    by (eapply cfg_sim_trans; eassumption).
  assert (Hfin : rcsec P' (B2 - 2 + 2 * (n + 2) + 3) [(1, 2)]
                 = entry_sec P' (B2 + 2 * n + 7)).
  { unfold entry_sec.
    replace (B2 - 2 + 2 * (n + 2) + 3) with (B2 + 2 * n + 5) by lia.
    replace (B2 + 2 * n + 7 - 2) with (B2 + 2 * n + 5) by lia.
    reflexivity. }
  rewrite Hfin in Hs.
  rewrite <- Hsrc in Hr.
  exists P'. eexists. exists c2'. split; [exact Hr |].
  split; [exact Hs | lia].
Qed.

Lemma SETTLED_ITER_GEN_odd_step : forall B2 n,
  Nat.Odd B2 -> B2 <= 35 -> 3 <= B2 -> 2 <= n ->
  loop_step (entryP B2) (n + 2).
Proof.
  intros B2 n Hodd HB2le HB2 Hn.
  destruct (SETTLED_ITER_GEN_odd B2 n Hodd HB2le HB2 Hn)
    as [P' [t [c [Hr [Hs Ht]]]]].
  unfold loop_step.
  exists P', (B2 + 2 * n + 7), t, c.
  split; [exact Ht |]. split; [exact Hr |]. split; [exact Hs | lia].
Qed.

(* Phase 39: the same settled iteration at an EVEN two-block        *)
(* prefix, UNCONDITIONAL via EraEven.ERA_GEN_even.  The residue is   *)
(* rho = B2 - 2 = 2k+2 with k = B2/2 - 2; the even era law covers    *)
(* k <= 16, i.e. even B2 with 4 <= B2 <= 36.  The era law's shape    *)
(* differs from ERA_GEN's: the absorption rotates (the residue       *)
(* pair's gap 2 becomes frame), so s1 = 2m + 1 and                   *)
(* beta' = 2 beta + 4 = 2n + 8 -- INDEPENDENT of B2 (the same        *)
(* closed form as the ESC era law), not B2 + 2n + 7.  Together       *)
(* with SETTLED_ITER_GEN_odd, the settled iteration is now           *)
(* unconditional for EVERY B2 with 3 <= B2 <= 36; B2 >= 37 remains   *)
(* on the conditional form (fenced in EraEven.v / the status doc).   *)
Lemma SETTLED_ITER_GEN_even : forall B2 n,
  Nat.Even B2 -> 4 <= B2 -> B2 <= 36 -> 2 <= n ->
  exists P' t c,
    run t (entry_sec (entryP B2) (n + 2)) = Some c
    /\ cfg_sim c (entry_sec P' (2 * n + 8))
    /\ 1 <= t.
Proof.
  intros B2 n Heven HB2lo HB2hi Hn.
  assert (Hsrc : entry_sec (entryP B2) (n + 2)
                 = rcsec (entryP B2) n [(1, 2)]).
  { unfold entry_sec. replace (n + 2 - 2) with n by lia. reflexivity. }
  pose proof (sim_entry (B2 - 1) n) as Hse.
  replace (S (B2 - 1)) with B2 in Hse by lia.
  assert (Hsim : cfg_sim (rcsec (entryP B2) n [(1, 2)])
                         (entry_tgt (B2 - 1) n)).
  { apply cfg_sim_sym. exact Hse. }
  destruct (RECOORD2_uncond B2 n ltac:(lia) Hn) as [c1 [Hr1 Hs1]].
  destruct (run_sim_transfer _ _ _ _ Hsim Hr1) as [c1' [Hr1' Hs1']].
  assert (Hsim1 : cfg_sim c1'
    (csec 16 (B2 - 2) 2 ((1, 1) :: repeat (1, 2) (S n)) 1))
    by (eapply cfg_sim_trans; eassumption).
  destruct Heven as [k' Hk'].
  destruct (ERA_GEN_even (k' - 2) (n + 2) ltac:(lia) ltac:(lia))
    as [P' [cost [c2 [Hr2 Hs2]]]].
  replace (2 * (k' - 2) + 2) with (B2 - 2) in Hr2 by lia.
  replace (n + 2 - 1) with (S n) in Hr2 by lia.
  destruct (run_trans_sim _ _ _ _ _ _ Hr1' Hsim1 Hr2) as [c2' [Hr HsT]].
  assert (Hs : cfg_sim c2' (rcsec P' (2 * (n + 2) + 2) [(1, 2)]))
    by (eapply cfg_sim_trans; eassumption).
  assert (Hfin : rcsec P' (2 * (n + 2) + 2) [(1, 2)]
                 = entry_sec P' (2 * n + 8)).
  { unfold entry_sec.
    replace (2 * (n + 2) + 2) with (2 * n + 6) by lia.
    replace (2 * n + 8 - 2) with (2 * n + 6) by lia.
    reflexivity. }
  rewrite Hfin in Hs.
  rewrite <- Hsrc in Hr.
  exists P'. eexists. exists c2'. split; [exact Hr |].
  split; [exact Hs | lia].
Qed.

Lemma SETTLED_ITER_GEN_even_step : forall B2 n,
  Nat.Even B2 -> 4 <= B2 -> B2 <= 36 -> 2 <= n ->
  loop_step (entryP B2) (n + 2).
Proof.
  intros B2 n Heven HB2lo HB2hi Hn.
  destruct (SETTLED_ITER_GEN_even B2 n Heven HB2lo HB2hi Hn)
    as [P' [t [c [Hr [Hs Ht]]]]].
  unfold loop_step.
  exists P', (2 * n + 8), t, c.
  split; [exact Ht |]. split; [exact Hr |]. split; [exact Hs | lia].
Qed.

(* ----------------------------------------------------------------- *)
(* Part 4: the ESC iteration.                                        *)
(* ----------------------------------------------------------------- *)

(* One ESC iteration at a single-block prefix 0 1^(R+6): PASS to     *)
(* the escape section (= esc_src (R + 6) (beta - 2) by esc_bridge),  *)
(* then ESC_ERA_LAW_31.  beta  |->  beta' = 2 beta + 4.  The next     *)
(* entry prefix is an ESC landing form 0 1^(a+1) ++ enc pb with      *)
(* a >= beta.                                                        *)
Lemma ESC_ITER : forall R beta,
  (R = 2 \/ R = 4 \/ R = 6 \/ R = 8 \/ R = 10 \/ R = 12 \/ R = 14
   \/ (exists m, R = 2 * m + 16 /\ m <= 12)) ->
  4 <= beta ->
  exists P' t c, run t (entry_sec (false :: repeat true (R + 6)) beta) = Some c
    /\ cfg_sim c (entry_sec P' (2 * beta + 4))
    /\ 1 <= t.
Proof.
  intros R beta HR Hb.
  destruct (PASS (false :: repeat true (R + 6)) (beta - 2) ltac:(lia))
    as [c1 [Hr1 Hs1]].
  rewrite (esc_bridge (R + 6) (beta - 2)) in Hs1.
  destruct (ESC_ERA_LAW_31 R beta HR ltac:(lia))
    as [n2 [c2 [pb [a [Hr2 [Hs2 Ha]]]]]].
  destruct (run_trans_sim _ _ _ _ _ _ Hr1 Hs1 Hr2) as [c2' [Hr HsT]].
  assert (Hs : cfg_sim c2' (rcsec (false :: repeat true (S a) ++ enc pb)
                                  (2 * beta + 2) [(1, 2)]))
    by (eapply cfg_sim_trans; eassumption).
  assert (Hfin : rcsec (false :: repeat true (S a) ++ enc pb)
                       (2 * beta + 2) [(1, 2)]
                 = entry_sec (false :: repeat true (S a) ++ enc pb)
                             (2 * beta + 4)).
  { unfold entry_sec.
    replace (2 * beta + 4 - 2) with (2 * beta + 2) by lia.
    reflexivity. }
  rewrite Hfin in Hs.
  exists (false :: repeat true (S a) ++ enc pb).
  eexists. exists c2'. split; [exact Hr |]. split; [exact Hs | lia].
Qed.

Lemma ESC_ITER_step : forall R beta,
  (R = 2 \/ R = 4 \/ R = 6 \/ R = 8 \/ R = 10 \/ R = 12 \/ R = 14
   \/ (exists m, R = 2 * m + 16 /\ m <= 12)) ->
  4 <= beta -> loop_step (false :: repeat true (R + 6)) beta.
Proof.
  intros R beta HR Hb.
  destruct (ESC_ITER R beta HR Hb) as [P' [t [c [Hr [Hs Ht]]]]].
  unfold loop_step.
  exists P', (2 * beta + 4), t, c.
  split; [exact Ht |]. split; [exact Hr |]. split; [exact Hs | lia].
Qed.

(* ----------------------------------------------------------------- *)
(* Part 4b (Phase 33): the ESC iteration past the second re-basing.  *)
(* ----------------------------------------------------------------- *)

(* One ESC iteration at a single-block prefix 0 1^(R+6) for every    *)
(* even R <= 114: PASS + esc_bridge + ESC_ERA_LAW_114 (Grind4.v).    *)
(* beta  |->  beta' = 2 beta + 4.  This discharges H_LOOP's ESC        *)
(* instances for 42 <= R <= 114; R >= 116 remains fenced (Grind4.v). *)
Lemma ESC_ITER_114 : forall R beta,
  (R = 2 \/ R = 4 \/ R = 6 \/ R = 8 \/ R = 10 \/ R = 12 \/ R = 14
   \/ (exists m, R = 2 * m + 16 /\ m <= 12)
   \/ R = 42 \/ R = 44 \/ (exists m, R = 2 * m + 46 /\ m <= 34)) ->
  4 <= beta ->
  exists P' t c, run t (entry_sec (false :: repeat true (R + 6)) beta) = Some c
    /\ cfg_sim c (entry_sec P' (2 * beta + 4))
    /\ 1 <= t.
Proof.
  intros R beta HR Hb.
  destruct (PASS (false :: repeat true (R + 6)) (beta - 2) ltac:(lia))
    as [c1 [Hr1 Hs1]].
  rewrite (esc_bridge (R + 6) (beta - 2)) in Hs1.
  destruct (ESC_ERA_LAW_114 R beta HR ltac:(lia))
    as [n2 [c2 [pb [a [Hr2 [Hs2 Ha]]]]]].
  destruct (run_trans_sim _ _ _ _ _ _ Hr1 Hs1 Hr2) as [c2' [Hr HsT]].
  assert (Hs : cfg_sim c2' (rcsec (false :: repeat true (S a) ++ enc pb)
                                  (2 * beta + 2) [(1, 2)]))
    by (eapply cfg_sim_trans; eassumption).
  assert (Hfin : rcsec (false :: repeat true (S a) ++ enc pb)
                       (2 * beta + 2) [(1, 2)]
                 = entry_sec (false :: repeat true (S a) ++ enc pb)
                             (2 * beta + 4)).
  { unfold entry_sec.
    replace (2 * beta + 4 - 2) with (2 * beta + 2) by lia.
    reflexivity. }
  rewrite Hfin in Hs.
  exists (false :: repeat true (S a) ++ enc pb).
  eexists. exists c2'. split; [exact Hr |]. split; [exact Hs | lia].
Qed.

Lemma ESC_ITER_114_step : forall R beta,
  (R = 2 \/ R = 4 \/ R = 6 \/ R = 8 \/ R = 10 \/ R = 12 \/ R = 14
   \/ (exists m, R = 2 * m + 16 /\ m <= 12)
   \/ R = 42 \/ R = 44 \/ (exists m, R = 2 * m + 46 /\ m <= 34)) ->
  4 <= beta -> loop_step (false :: repeat true (R + 6)) beta.
Proof.
  intros R beta HR Hb.
  destruct (ESC_ITER_114 R beta HR Hb) as [P' [t [c [Hr [Hs Ht]]]]].
  unfold loop_step.
  exists P', (2 * beta + 4), t, c.
  split; [exact Ht |]. split; [exact Hr |]. split; [exact Hs | lia].
Qed.

(* ----------------------------------------------------------------- *)
(* Part 4c (Phase 37): the ESC iteration past the third re-basing.   *)
(* ----------------------------------------------------------------- *)

(* One ESC iteration at a single-block prefix 0 1^(R+6) for every    *)
(* even R <= 268: PASS + esc_bridge + ESC_ERA_LAW_268 (Grind6.v).    *)
(* beta  |->  beta' = 2 beta + 4.  This discharges H_LOOP's ESC        *)
(* instances for 116 <= R <= 268; R >= 270 is discharged by          *)
(* ESC_ITER_602 below (Phase 38, Grind7.v).                            *)
Lemma ESC_ITER_268 : forall R beta,
  ((R = 2 \/ R = 4 \/ R = 6 \/ R = 8 \/ R = 10 \/ R = 12 \/ R = 14
    \/ (exists m, R = 2 * m + 16 /\ m <= 12)
    \/ R = 42 \/ R = 44 \/ (exists m, R = 2 * m + 46 /\ m <= 34))
   \/ (R = 116 \/ R = 118 \/ R = 120
       \/ (exists m, R = 2 * m + 46 /\ 38 <= m <= 111))) ->
  4 <= beta ->
  exists P' t c, run t (entry_sec (false :: repeat true (R + 6)) beta) = Some c
    /\ cfg_sim c (entry_sec P' (2 * beta + 4))
    /\ 1 <= t.
Proof.
  intros R beta HR Hb.
  destruct (PASS (false :: repeat true (R + 6)) (beta - 2) ltac:(lia))
    as [c1 [Hr1 Hs1]].
  rewrite (esc_bridge (R + 6) (beta - 2)) in Hs1.
  destruct (ESC_ERA_LAW_268 R beta HR ltac:(lia))
    as [n2 [c2 [pb [a [Hr2 [Hs2 Ha]]]]]].
  destruct (run_trans_sim _ _ _ _ _ _ Hr1 Hs1 Hr2) as [c2' [Hr HsT]].
  assert (Hs : cfg_sim c2' (rcsec (false :: repeat true (S a) ++ enc pb)
                                  (2 * beta + 2) [(1, 2)]))
    by (eapply cfg_sim_trans; eassumption).
  assert (Hfin : rcsec (false :: repeat true (S a) ++ enc pb)
                       (2 * beta + 2) [(1, 2)]
                 = entry_sec (false :: repeat true (S a) ++ enc pb)
                             (2 * beta + 4)).
  { unfold entry_sec.
    replace (2 * beta + 4 - 2) with (2 * beta + 2) by lia.
    reflexivity. }
  rewrite Hfin in Hs.
  exists (false :: repeat true (S a) ++ enc pb).
  eexists. exists c2'. split; [exact Hr |]. split; [exact Hs | lia].
Qed.

Lemma ESC_ITER_268_step : forall R beta,
  ((R = 2 \/ R = 4 \/ R = 6 \/ R = 8 \/ R = 10 \/ R = 12 \/ R = 14
    \/ (exists m, R = 2 * m + 16 /\ m <= 12)
    \/ R = 42 \/ R = 44 \/ (exists m, R = 2 * m + 46 /\ m <= 34))
   \/ (R = 116 \/ R = 118 \/ R = 120
       \/ (exists m, R = 2 * m + 46 /\ 38 <= m <= 111))) ->
  4 <= beta -> loop_step (false :: repeat true (R + 6)) beta.
Proof.
  intros R beta HR Hb.
  destruct (ESC_ITER_268 R beta HR Hb) as [P' [t [c [Hr [Hs Ht]]]]].
  unfold loop_step.
  exists P', (2 * beta + 4), t, c.
  split; [exact Ht |]. split; [exact Hr |]. split; [exact Hs | lia].
Qed.

(* One ESC iteration at a single-block prefix 0 1^(R+6) for every    *)
(* even R <= 602: PASS + esc_bridge + ESC_ERA_LAW_602 (Grind7.v).    *)
(* beta  |->  beta' = 2 beta + 4.  This discharges H_LOOP's ESC        *)
(* instances for 270 <= R <= 602; R >= 604 remains fenced            *)
(* (Grind7.v: the phase-6 finish's new-frame floors bind at          *)
(* m = 279 -- a phase-7 deviation).                                   *)
Lemma ESC_ITER_602 : forall R beta,
  (((R = 2 \/ R = 4 \/ R = 6 \/ R = 8 \/ R = 10 \/ R = 12 \/ R = 14
    \/ (exists m, R = 2 * m + 16 /\ m <= 12)
    \/ R = 42 \/ R = 44 \/ (exists m, R = 2 * m + 46 /\ m <= 34))
   \/ (R = 116 \/ R = 118 \/ R = 120
       \/ (exists m, R = 2 * m + 46 /\ 38 <= m <= 111)))
   \/ (R = 270 \/ R = 272 \/ R = 274
       \/ (exists m, R = 2 * m + 46 /\ 115 <= m <= 278))) ->
  4 <= beta ->
  exists P' t c, run t (entry_sec (false :: repeat true (R + 6)) beta) = Some c
    /\ cfg_sim c (entry_sec P' (2 * beta + 4))
    /\ 1 <= t.
Proof.
  intros R beta HR Hb.
  destruct (PASS (false :: repeat true (R + 6)) (beta - 2) ltac:(lia))
    as [c1 [Hr1 Hs1]].
  rewrite (esc_bridge (R + 6) (beta - 2)) in Hs1.
  destruct (ESC_ERA_LAW_602 R beta HR ltac:(lia))
    as [n2 [c2 [pb [a [Hr2 [Hs2 Ha]]]]]].
  destruct (run_trans_sim _ _ _ _ _ _ Hr1 Hs1 Hr2) as [c2' [Hr HsT]].
  assert (Hs : cfg_sim c2' (rcsec (false :: repeat true (S a) ++ enc pb)
                                  (2 * beta + 2) [(1, 2)]))
    by (eapply cfg_sim_trans; eassumption).
  assert (Hfin : rcsec (false :: repeat true (S a) ++ enc pb)
                       (2 * beta + 2) [(1, 2)]
                 = entry_sec (false :: repeat true (S a) ++ enc pb)
                             (2 * beta + 4)).
  { unfold entry_sec.
    replace (2 * beta + 4 - 2) with (2 * beta + 2) by lia.
    reflexivity. }
  rewrite Hfin in Hs.
  exists (false :: repeat true (S a) ++ enc pb).
  eexists. exists c2'. split; [exact Hr |]. split; [exact Hs | lia].
Qed.

Lemma ESC_ITER_602_step : forall R beta,
  (((R = 2 \/ R = 4 \/ R = 6 \/ R = 8 \/ R = 10 \/ R = 12 \/ R = 14
    \/ (exists m, R = 2 * m + 16 /\ m <= 12)
    \/ R = 42 \/ R = 44 \/ (exists m, R = 2 * m + 46 /\ m <= 34))
   \/ (R = 116 \/ R = 118 \/ R = 120
       \/ (exists m, R = 2 * m + 46 /\ 38 <= m <= 111)))
   \/ (R = 270 \/ R = 272 \/ R = 274
       \/ (exists m, R = 2 * m + 46 /\ 115 <= m <= 278))) ->
  4 <= beta -> loop_step (false :: repeat true (R + 6)) beta.
Proof.
  intros R beta HR Hb.
  destruct (ESC_ITER_602 R beta HR Hb) as [P' [t [c [Hr [Hs Ht]]]]].
  unfold loop_step.
  exists P', (2 * beta + 4), t, c.
  split; [exact Ht |]. split; [exact Hr |]. split; [exact Hs | lia].
Qed.

(* ----------------------------------------------------------------- *)
(* Part 5: the first two iterations, fully proved.                   *)
(* ----------------------------------------------------------------- *)

(* From the entry landing entry_tgt 30 n with n = 2j + 3, j <= 12:   *)
(* iteration 1 is SETTLED_ITER (beta = n + 2  |->  2n + 38, prefix   *)
(* the single block 0 1^(n+19)); iteration 2 is ESC_ITER at          *)
(* R = n + 13 = 2j + 16 <= 40 (beta  |->  4n + 80).                   *)
Lemma TWO_ITERS : forall n j, n = 2 * j + 3 -> j <= 12 ->
  exists P' t c, run t (entry_tgt 30 n) = Some c
    /\ cfg_sim c (entry_sec P' (4 * n + 80))
    /\ 1 <= t.
Proof.
  intros n j Hn Hj.
  assert (Hn2 : 2 <= n) by lia.
  destruct (SETTLED_ITER n Hn2) as [t1 [c1 [Hr1 [Hs1 Ht1]]]].
  assert (Hsim0 : cfg_sim (entry_tgt 30 n) (entry_sec (entryP 31) (n + 2))).
  { unfold entry_sec. replace (n + 2 - 2) with n by lia.
    exact (sim_entry 30 n). }
  destruct (run_sim_transfer _ _ _ _ Hsim0 Hr1) as [c1' [Hr1' Hs1']].
  assert (Hs1'' : cfg_sim c1'
    (entry_sec (false :: repeat true (n + 19)) (2 * n + 38)))
    by (eapply cfg_sim_trans; eassumption).
  assert (HR : (n + 13 = 2 \/ n + 13 = 4 \/ n + 13 = 6 \/ n + 13 = 8
    \/ n + 13 = 10 \/ n + 13 = 12 \/ n + 13 = 14
    \/ (exists m, n + 13 = 2 * m + 16 /\ m <= 12))).
  { do 7 right. exists j. split; lia. }
  destruct (ESC_ITER (n + 13) (2 * n + 38) HR ltac:(lia))
    as [P' [t2 [c2 [Hr2 [Hs2 Ht2]]]]].
  replace (n + 13 + 6) with (n + 19) in Hr2 by lia.
  destruct (run_trans_sim _ _ _ _ _ _ Hr1' Hs1'' Hr2) as [c2' [Hr HsT]].
  assert (Hs : cfg_sim c2' (entry_sec P' (2 * (2 * n + 38) + 4)))
    by (eapply cfg_sim_trans; eassumption).
  replace (2 * (2 * n + 38) + 4) with (4 * n + 80) in Hs by lia.
  exists P'. eexists. exists c2'. split; [exact Hr |].
  split; [exact Hs | lia].
Qed.

(* ----------------------------------------------------------------- *)
(* Part 6: the ascending loop and the headline assembly.             *)
(* ----------------------------------------------------------------- *)

(* Chains of loop iterations reach entry sections at strictly        *)
(* increasing times, with beta non-decreasing along the chain        *)
(* (in fact strictly increasing at every step).                      *)
Lemma loop_chain : forall (Hstep : forall P beta, 4 <= beta -> loop_step P beta),
  forall P beta, 4 <= beta -> forall k,
  exists Pk bk t c, run t (entry_sec P beta) = Some c
    /\ cfg_sim c (entry_sec Pk bk) /\ beta <= bk /\ k <= t.
Proof.
  intros Hstep P beta Hb k. induction k as [| k IH].
  - exists P, beta, 0, (entry_sec P beta).
    split; [reflexivity |].
    split; [apply cfg_sim_refl |]. split; lia.
  - destruct IH as [Pk [bk [t [c [Hr [Hs [Hb1 Hb2]]]]]]].
    destruct (Hstep Pk bk ltac:(lia))
      as [P' [b' [t' [c' [Ht' [Hr' [Hs' Hb']]]]]]].
    destruct (run_sim_transfer t' c (entry_sec Pk bk) c' Hs Hr')
      as [c'' [Hr'' Hs'']].
    exists P', b', (t + t'), c''.
    split.
    + rewrite run_split. rewrite Hr. exact Hr''.
    + split; [eapply cfg_sim_trans; eassumption |]. split; lia.
Qed.

(* The ascending-loop engine: if every entry section with            *)
(* beta >= 4 iterates, the run from any entry section never halts    *)
(* (run is defined at every length).                                 *)
Theorem LOOP_NONHALT : forall (Hstep : forall P beta, 4 <= beta -> loop_step P beta),
  forall P beta, 4 <= beta -> forall N, exists c, run N (entry_sec P beta) = Some c.
Proof.
  intros Hstep P beta Hb N.
  destruct (loop_chain Hstep P beta Hb N)
    as [Pk [bk [t [c [Hr [Hs [Hb1 Hb2]]]]]]].
  replace t with (N + (t - N)) in Hr by lia.
  rewrite run_split in Hr.
  destruct (run N (entry_sec P beta)) as [cN |] eqn:E;
    [exists cN; reflexivity | discriminate].
Qed.

(* The headline assembly, from the record configuration R.  The      *)
(* formation R -> first I-section (150 steps) is kernel-verified     *)
(* (Finite.R_reaches_Isec, used below); the two hypotheses are       *)
(* H_STD (the standard regime reaches an entry landing) and          *)
(* H_LOOP (loop_step at every entry section), as documented in the   *)
(* file header.                                                      *)
Theorem NONHALT_FROM_R :
  (exists t n B2 c, run t cfg_Isec = Some c
     /\ cfg_sim c (entry_tgt (B2 - 1) n) /\ 3 <= B2 /\ 2 <= n) ->
  (forall P beta, 4 <= beta -> loop_step P beta) ->
  forall N, exists c, run N cfg_R = Some c.
Proof.
  intros [t [n [B2 [c0 [Hr0 [Hs0 [HB2 Hn]]]]]]] Hstep.
  destruct R_reaches_Isec as [cR [HrR [HsRstate HsRtape]]].
  assert (HsR : cfg_sim cR cfg_Isec) by (unfold cfg_sim; split; assumption).
  destruct (run_sim_transfer t cR cfg_Isec c0 HsR Hr0)
    as [c0' [Hr0' Hs0']].
  assert (Hs1 : cfg_sim c0' (entry_tgt (B2 - 1) n))
    by (eapply cfg_sim_trans; eassumption).
  pose proof (sim_entry (B2 - 1) n) as Hse.
  replace (S (B2 - 1)) with B2 in Hse by lia.
  assert (Hs2 : cfg_sim c0' (entry_sec (entryP B2) (n + 2))).
  { eapply cfg_sim_trans; [exact Hs1 |].
    unfold entry_sec. replace (n + 2 - 2) with n by lia. exact Hse. }
  assert (Htot : forall N, exists c,
    run N (entry_sec (entryP B2) (n + 2)) = Some c).
  { apply (LOOP_NONHALT Hstep). lia. }
  assert (Hbig : run (150 + t) cfg_R = Some c0').
  { rewrite run_split. rewrite HrR. exact Hr0'. }
  exact (total_transfer cfg_R c0' (entry_sec (entryP B2) (n + 2))
           (150 + t) Hbig Hs2 Htot).
Qed.

(* ----------------------------------------------------------------- *)
(* Axiom audit: every headline result must be closed (the two        *)
(* hypotheses of NONHALT_FROM_R and ERA_GEN / Hstep are lemma        *)
(* parameters, not axioms).                                          *)
(* ----------------------------------------------------------------- *)

Print Assumptions PASS.
Print Assumptions esc_bridge.
Print Assumptions SETTLED_ITER.
Print Assumptions SETTLED_ITER_step.
Print Assumptions ERA_LAW_GEN.
Print Assumptions SETTLED_ITER_GEN.
Print Assumptions SETTLED_ITER_GEN_step.
Print Assumptions SETTLED_ITER_GEN_odd.
Print Assumptions SETTLED_ITER_GEN_odd_step.
Print Assumptions SETTLED_ITER_GEN_even.
Print Assumptions SETTLED_ITER_GEN_even_step.
Print Assumptions ESC_ITER.
Print Assumptions ESC_ITER_step.
Print Assumptions ESC_ITER_114.
Print Assumptions ESC_ITER_114_step.
Print Assumptions ESC_ITER_268.
Print Assumptions ESC_ITER_268_step.
Print Assumptions TWO_ITERS.
Print Assumptions loop_chain.
Print Assumptions LOOP_NONHALT.
Print Assumptions NONHALT_FROM_R.
