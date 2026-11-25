(* ================================================================= *)
(*  Std.v -- Phase 34: the standard-regime assembly (component #10   *)
(*  totality + the #11 exit dichotomy), discharging hypothesis       *)
(*  H_STD of Loop.v's NONHALT_FROM_R.                                *)
(*                                                                   *)
(*  H_STD asks: from the first I-section cfg_Isec (the formation     *)
(*  endpoint, Finite.v: state C, B2 = 97, s = 2, w = [1], G = 134),  *)
(*  the standard regime reaches cfg_sim of some entry landing        *)
(*  entry_tgt (B2 - 1) n with B2 >= 3, n >= 2.                       *)
(*                                                                   *)
(*  The human argument (bounce-derivation.md, reexpansion-           *)
(*  derivation.md S3): the five derived rules are total on           *)
(*  invariant I; the four bounce rules preserve G; Stage A fires     *)
(*  exactly at B-sections with w = [1] and sends G |-> G - 2; the    *)
(*  composed system therefore runs until the first w = [1]           *)
(*  B-section at G = 2 -- which IS the ENTRY source (entry_src),     *)
(*  whose excursion (Mirror.ENTRY) lands on entry_tgt.               *)
(*                                                                   *)
(*  Mechanisation: cfg_Isec is DEFINITIONALLY the word-model         *)
(*  section HC [17] 95 1 2 [] 134 (the frozen prefix [17] encodes     *)
(*  the separator 0 and the wall 1^17), and entry_src B2 s is        *)
(*  definitionally HB [17] B2 1 s [] 2.  The whole regime from       *)
(*  cfg_Isec is then one hsteps chain at pb = [17]:                  *)
(*                                                                   *)
(*    HC 95 1 2 [] 134                                               *)
(*      --hTDN-->  HB 95 1 4 [] 134                                  *)
(*      --hSTGA--> HC 95 3 2 [] 132          (collapse 1)            *)
(*      --STD_cycle t--> HC 95 (2t+5) 2 [] (130 - 2t),  t = 0..64    *)
(*           (hGRIND t at floor t + 1 <= 95, then hSTGA:             *)
(*            collapses 2..66, G: 132 -> 2)                          *)
(*      --hGRIND 65--> HB 95 1 136 [] 2      (= entry_src 95 136)    *)
(*      --ENTRY (148 steps)--> entry_tgt 95 136                      *)
(*                                                                   *)
(*  i.e. H_STD holds with (B2, n) = (96, 136).  The chain was        *)
(*  pre-verified on the real machine (rocq/std_verify.py): from      *)
(*  cfg_Isec the first 15 macro boundaries are hit in order with     *)
(*  TDN delta 6 and every Stage A delta exactly 2s + 6, and the      *)
(*  same assembly at G0 in {6, 8, 10} runs end-to-end through        *)
(*  ENTRY to entry_tgt 95 (G0 + 2).                                  *)
(*                                                                   *)
(*  Scope note: this discharges H_STD by exhibiting the concrete     *)
(*  chain from cfg_Isec -- the only instance NONHALT_FROM_R uses.    *)
(*  The general I+ preservation induction over ARBITRARY standard-   *)
(*  rule sequences is not separately formalised; it is no longer     *)
(*  load-bearing (the trajectory's sequence is the one above, and    *)
(*  each of its steps is a proved rule).                             *)
(* ================================================================= *)

Require Import List Bool Arith Lia ZArith.
Import ListNotations.
Require Import TM Configs Finite Sections Mirror TokenPass DiagPass
               Recoord Era Esc Dev Grind Grind2 Grind3 Grind4 Loop.

(* Section-equality tactic (same idiom as Grind2.v's sec_eq). *)
Ltac hsec_eq :=
  repeat (first [ solve [reflexivity] | solve [lia] | f_equal ]).

(* ----------------------------------------------------------------- *)
(* Part 1: one grind + collapse cycle.  From the C-section with      *)
(* g0 = 2t + 3 and empty stack, hGRIND t (floor t + 1 <= A) reaches  *)
(* the B-section with shuttle 2t + 6 at the same G, and Stage A      *)
(* (G >= 3) collapses to the next C-section with G - 2.              *)
(* ----------------------------------------------------------------- *)

Lemma STD_cycle : forall pb A t G, t + 1 <= A -> 3 <= G ->
  hsteps (HC pb A (2 * t + 3) 2 [] G) (HC pb A (2 * t + 5) 2 [] (G - 2)).
Proof.
  intros pb A t G Hfloor HG.
  apply (hsteps_trans _ (HB pb A 1 (2 * t + 6) [] G)).
  - apply hGRIND. exact Hfloor.
  - replace (HC pb A (2 * t + 5) 2 [] (G - 2))
      with (HC pb A (2 * t + 6 - 1) 2 [] (G - 2)) by hsec_eq.
    apply (hsteps_step _ (HC pb A (2 * t + 6 - 1) 2 [] (G - 2))).
    + apply hSTGA; lia.
    + apply hsteps_refl.
Qed.

(* ----------------------------------------------------------------- *)
(* Part 2: k cycles take G = 2k + 2 down to G = 2, the grind         *)
(* parameter rising from t to t + k.                                 *)
(* ----------------------------------------------------------------- *)

Lemma STD_cycles : forall k pb A t, t + k + 1 <= A ->
  hsteps (HC pb A (2 * t + 3) 2 [] (2 * k + 2))
         (HC pb A (2 * (t + k) + 3) 2 [] 2).
Proof.
  induction k as [| k IH]; intros pb A t Hfloor.
  - replace (2 * (t + 0) + 3) with (2 * t + 3) by lia.
    replace (2 * 0 + 2) with 2 by lia.
    apply hsteps_refl.
  - apply (hsteps_trans _ (HC pb A (2 * t + 5) 2 [] (2 * k + 2))).
    + replace (HC pb A (2 * t + 5) 2 [] (2 * k + 2))
        with (HC pb A (2 * t + 5) 2 [] (2 * S k + 2 - 2)) by hsec_eq.
      apply STD_cycle; lia.
    + replace (HC pb A (2 * (t + S k) + 3) 2 [] 2)
        with (HC pb A (2 * (S t + k) + 3) 2 [] 2) by hsec_eq.
      replace (HC pb A (2 * t + 5) 2 [] (2 * k + 2))
        with (HC pb A (2 * S t + 3) 2 [] (2 * k + 2)) by hsec_eq.
      apply IH. lia.
Qed.

(* ----------------------------------------------------------------- *)
(* Part 3: the regime totality for an empty-stack I-section.  From   *)
(* a C-section with g0 = 1, s = 2, w = [1] and even G = 2k + 6 >= 6,  *)
(* at any frame A >= k + 2, the regime reaches the w = [1]           *)
(* B-section at G = 2 with shuttle 2k + 8: TDN, one Stage A,         *)
(* k + 1 grind/collapse cycles, and the final grind.                 *)
(* ----------------------------------------------------------------- *)

Lemma STD_reach_entry : forall pb A k, k + 2 <= A ->
  hsteps (HC pb A 1 2 [] (2 * k + 6)) (HB pb A 1 (2 * k + 8) [] 2).
Proof.
  intros pb A k Hfloor.
  apply (hsteps_trans _ (HC pb A (2 * (k + 1) + 3) 2 [] 2)).
  - apply (hsteps_trans _ (HC pb A 3 2 [] (2 * k + 4))).
    + apply (hsteps_trans _ (HB pb A 1 4 [] (2 * k + 6))).
      * apply (hsteps_step _ (HB pb A 1 4 [] (2 * k + 6))).
        -- apply hTDN.
        -- apply hsteps_refl.
      * replace (HC pb A 3 2 [] (2 * k + 4))
          with (HC pb A (4 - 1) 2 [] (2 * k + 6 - 2)) by hsec_eq.
        apply (hsteps_step _ (HC pb A (4 - 1) 2 [] (2 * k + 6 - 2))).
        -- apply hSTGA; lia.
        -- apply hsteps_refl.
    + replace (HC pb A (2 * (k + 1) + 3) 2 [] 2)
        with (HC pb A (2 * (0 + (k + 1)) + 3) 2 [] 2) by hsec_eq.
      replace (HC pb A 3 2 [] (2 * k + 4))
        with (HC pb A (2 * 0 + 3) 2 [] (2 * (k + 1) + 2)) by hsec_eq.
      apply STD_cycles. lia.
  - replace (HB pb A 1 (2 * k + 8) [] 2)
      with (HB pb A 1 (2 * (k + 1) + 6) [] 2) by hsec_eq.
    apply hGRIND. lia.
Qed.

(* ----------------------------------------------------------------- *)
(* Part 4: the trajectory instance and the discharge of H_STD.       *)
(* ----------------------------------------------------------------- *)

(* The trajectory chain: G0 = 134 = 2 * 64 + 6, so k = 64, the       *)
(* final shuttle is 2 * 64 + 8 = 136, and the floor is               *)
(* 64 + 2 = 66 <= 95.  Stage A fires 66 times in total.              *)
Lemma STD_chain : hsteps (HC [17] 95 1 2 [] 134) (HB [17] 95 1 136 [] 2).
Proof.
  replace (HC [17] 95 1 2 [] 134)
    with (HC [17] 95 1 2 [] (2 * 64 + 6)) by hsec_eq.
  replace (HB [17] 95 1 136 [] 2)
    with (HB [17] 95 1 (2 * 64 + 8) [] 2) by hsec_eq.
  apply STD_reach_entry. lia.
Qed.

(* The first I-section IS the word-model section at pb = [17]. *)
Lemma Isec_hcfg : cfg_Isec = hcfg (HC [17] 95 1 2 [] 134).
Proof. reflexivity. Qed.

(* The chain's final B-section IS the ENTRY source at (95, 136). *)
Lemma final_entry_src : hcfg (HB [17] 95 1 136 [] 2) = entry_src 95 136.
Proof. reflexivity. Qed.

(* H_STD, discharged: from cfg_Isec the standard regime reaches     *)
(* entry_tgt 95 136 exactly -- H_STD's (B2, n) = (96, 136).          *)
Theorem H_STD_proved : exists t n B2 c, run t cfg_Isec = Some c
  /\ cfg_sim c (entry_tgt (B2 - 1) n) /\ 3 <= B2 /\ 2 <= n.
Proof.
  destruct (hsteps_sound _ _ STD_chain) as [t0 [c0 [Hr0 Hs0]]].
  rewrite <- Isec_hcfg in Hr0.
  rewrite final_entry_src in Hs0.
  assert (Hentry : run 148 (entry_src 95 136) = Some (entry_tgt 95 136)).
  { replace 148 with (S 135 + 12) by lia. apply ENTRY. }
  destruct (run_sim_transfer 148 c0 (entry_src 95 136)
              (entry_tgt 95 136) Hs0 Hentry) as [c1 [Hr1 Hs1]].
  exists (t0 + 148), 136, 96, c1.
  split; [| split; [| split]].
  - rewrite run_split. rewrite Hr0. exact Hr1.
  - replace (96 - 1) with 95 by lia. exact Hs1.
  - lia.
  - lia.
Qed.

(* The headline assembly with H_STD discharged: NONHALT_FROM_R      *)
(* now rests on the single remaining hypothesis H_LOOP.              *)
Theorem NONHALT_FROM_R_std :
  (forall P beta, 4 <= beta -> loop_step P beta) ->
  forall N, exists c, run N cfg_R = Some c.
Proof.
  intros Hstep. apply NONHALT_FROM_R.
  - exact H_STD_proved.
  - exact Hstep.
Qed.

(* ----------------------------------------------------------------- *)
(* Axiom audit: every headline result must be closed (H_LOOP in      *)
(* NONHALT_FROM_R_std is a lemma parameter, not an axiom).           *)
(* ----------------------------------------------------------------- *)

Print Assumptions STD_cycle.
Print Assumptions STD_cycles.
Print Assumptions STD_reach_entry.
Print Assumptions STD_chain.
Print Assumptions Isec_hcfg.
Print Assumptions final_entry_src.
Print Assumptions H_STD_proved.
Print Assumptions NONHALT_FROM_R_std.
