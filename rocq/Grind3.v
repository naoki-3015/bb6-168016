(* ================================================================= *)
(*  Grind3.v -- Phase 31: REBASE, the R >= 12 re-basing segment of  *)
(*  the ESC grind, and the ESC-era law beta_next = 2*beta + 4       *)
(*  extended to every even R <= 40.                                 *)
(*                                                                  *)
(*  Finding F-4 (against the Phase 29 fence in                      *)
(*  mechanisation-status.md): the fenced source                     *)
(*  HC [] 4 11 2 ((R-10, 2) :: P) 1 has g0 = 11, but the section    *)
(*  the ESC grind actually reaches after round 3 (deviated) and     *)
(*  its TUP is HC [] 4 12 2 ((R-10, 2) :: P) 1 -- the fence's 11 is  *)
(*  an off-by-one slip (it is the s'' of that TUP).  Model          *)
(*  evidence (phase21_model.py, beta = 4, R = 14 and R = 18): the   *)
(*  g0 = 11 section never occurs in the grind, and the chain from   *)
(*  it does not reach the fenced target; the chain from the         *)
(*  g0 = 12 section reaches HC [5] 13 1 2 ((R-12, 2) :: P) 1, with  *)
(*  every boundary below verified at R in {12, 14, 16, 20, 22       *)
(*  (beta = 7), 28, 38 (beta = 3), 40}.  The corrected REBASE is    *)
(*  proved here; the target is unchanged.                           *)
(*                                                                  *)
(*  Decomposition: the segment is NOT a new two-residue induction.  *)
(*  hGRIND and hGRIND_dev quantify over the whole carried stack,    *)
(*  so the second residue pair (u, 2) is a pure passenger:          *)
(*    PUSH + TDN + TUP   HC [] 4 12 2 [(u,2),P]                     *)
(*                         -> HC [] 3 3 2 [(8,2),(u,2),P]           *)
(*    hGRIND 0           -> HB [] 3 1 6 [(8,2),(u,2),P]             *)
(*    TUP + hGRIND 1     -> HB [] 3 1 8 [(6,2),(u,2),P]             *)
(*    TUP + hGRIND 2     -> HB [] 3 1 10 [(4,2),(u,2),P]            *)
(*    TUP + hGRIND_dev 3 -> HB [] 4 1 13 [(2,2),(u,2),P]            *)
(*  (= REBASE_core, no hypothesis on u), and for u >= 3 one          *)
(*  closing hTUP2_1 (r1 = 2, w2 = u):                               *)
(*    REBASE             -> HC [5] 13 1 2 [(u-2,2),P].              *)
(*  The segment's single PUSHX is the base step of hGRIND_dev 3     *)
(*  (the grind's second PUSHX overall, as the fence measured; the   *)
(*  fence's "three POPs" are the POPs of hGRIND_dev's closing       *)
(*  spine at idx 118-120 of the model trace).                       *)
(*                                                                  *)
(*  ESC_GRIND_BIG is the R >= 12 grind up to the REBASE source      *)
(*  (prefix + clean rounds 1-2 + TUP + hGRIND_dev 3 + TUP, the      *)
(*  ESC_GRIND_10 pattern at general R).  After REBASE, the          *)
(*  re-based grind at (pb = [5], a2 = 13) is GG_clean for residue   *)
(*  R - 12 = 2m + 4 with m <= 12, i.e. R <= 40; R = 14 closes by    *)
(*  TDN + TAIL and R = 12 by REBASE_core + hTRANS2_2 + the POP      *)
(*  chain.  ESC_ERA_LAW_31: beta_next = 2*beta + 4 for every even   *)
(*  R <= 40.  R >= 42 stays fenced (status doc): round 13 of the    *)
(*  re-based grind is a deviated grind at pb = [5], whose           *)
(*  dip-bottom dispatch is PX2B (b = 5), not PUSHX -- a             *)
(*  prefix-general deviated grind is the missing piece.             *)
(* ================================================================= *)

Require Import List Bool Arith Lia ZArith.
Import ListNotations.
Require Import TM Sections Mirror TokenPass Recoord Era Esc Grind Dev Grind2.

(* ================================================================= *)
(*  Part 1: REBASE_core and REBASE.                                  *)
(* ================================================================= *)

Lemma REBASE_core : forall u P G,
  hsteps (HC [] 4 12 2 ((u, 2) :: P) G)
         (HB [] 4 1 13 ((2, 2) :: (u, 2) :: P) G).
Proof.
  intros u P G.
  apply (hsteps_step _ (HC [] 3 1 2 ((10, 2) :: (u, 2) :: P) G)).
  { replace (HC [] 4 12 2 ((u, 2) :: P) G)
      with (HC [] (S 3) (S (S (S 9))) 2 ((u, 2) :: P) G) by sec_eq.
    replace (HC [] 3 1 2 ((10, 2) :: (u, 2) :: P) G)
      with (HC [] 3 1 2 ((S 9, 2) :: (u, 2) :: P) G) by sec_eq.
    apply hPUSH. }
  apply (hsteps_step _ (HB [] 3 1 4 ((10, 2) :: (u, 2) :: P) G)).
  { apply hTDN. }
  apply (hsteps_step _ (HC [] 3 3 2 ((8, 2) :: (u, 2) :: P) G)).
  { replace (HB [] 3 1 4 ((10, 2) :: (u, 2) :: P) G)
      with (HB [] 3 1 (S (S 2)) ((S (S (S 7)), 2) :: (u, 2) :: P) G)
      by sec_eq.
    replace (HC [] 3 3 2 ((8, 2) :: (u, 2) :: P) G)
      with (HC [] 3 (S 2) 2 ((S 7, 2) :: (u, 2) :: P) G) by sec_eq.
    apply hTUP. }
  apply (hsteps_trans _ (HB [] 3 1 6 ((8, 2) :: (u, 2) :: P) G)).
  { replace (HC [] 3 3 2 ((8, 2) :: (u, 2) :: P) G)
      with (HC [] 3 (2*0 + 3) 2 ((8, 2) :: (u, 2) :: P) G) by sec_eq.
    replace (HB [] 3 1 6 ((8, 2) :: (u, 2) :: P) G)
      with (HB [] 3 1 (2*0 + 6) ((8, 2) :: (u, 2) :: P) G) by sec_eq.
    apply hGRIND; lia. }
  apply (hsteps_step _ (HC [] 3 5 2 ((6, 2) :: (u, 2) :: P) G)).
  { replace (HB [] 3 1 6 ((8, 2) :: (u, 2) :: P) G)
      with (HB [] 3 1 (S (S 4)) ((S (S (S 5)), 2) :: (u, 2) :: P) G)
      by sec_eq.
    replace (HC [] 3 5 2 ((6, 2) :: (u, 2) :: P) G)
      with (HC [] 3 (S 4) 2 ((S 5, 2) :: (u, 2) :: P) G) by sec_eq.
    apply hTUP. }
  apply (hsteps_trans _ (HB [] 3 1 8 ((6, 2) :: (u, 2) :: P) G)).
  { replace (HC [] 3 5 2 ((6, 2) :: (u, 2) :: P) G)
      with (HC [] 3 (2*1 + 3) 2 ((6, 2) :: (u, 2) :: P) G) by sec_eq.
    replace (HB [] 3 1 8 ((6, 2) :: (u, 2) :: P) G)
      with (HB [] 3 1 (2*1 + 6) ((6, 2) :: (u, 2) :: P) G) by sec_eq.
    apply hGRIND; lia. }
  apply (hsteps_step _ (HC [] 3 7 2 ((4, 2) :: (u, 2) :: P) G)).
  { replace (HB [] 3 1 8 ((6, 2) :: (u, 2) :: P) G)
      with (HB [] 3 1 (S (S 6)) ((S (S (S 3)), 2) :: (u, 2) :: P) G)
      by sec_eq.
    replace (HC [] 3 7 2 ((4, 2) :: (u, 2) :: P) G)
      with (HC [] 3 (S 6) 2 ((S 3, 2) :: (u, 2) :: P) G) by sec_eq.
    apply hTUP. }
  apply (hsteps_trans _ (HB [] 3 1 10 ((4, 2) :: (u, 2) :: P) G)).
  { replace (HC [] 3 7 2 ((4, 2) :: (u, 2) :: P) G)
      with (HC [] 3 (2*2 + 3) 2 ((4, 2) :: (u, 2) :: P) G) by sec_eq.
    replace (HB [] 3 1 10 ((4, 2) :: (u, 2) :: P) G)
      with (HB [] 3 1 (2*2 + 6) ((4, 2) :: (u, 2) :: P) G) by sec_eq.
    apply hGRIND; lia. }
  apply (hsteps_step _ (HC [] 3 9 2 ((2, 2) :: (u, 2) :: P) G)).
  { replace (HB [] 3 1 10 ((4, 2) :: (u, 2) :: P) G)
      with (HB [] 3 1 (S (S 8)) ((S (S (S 1)), 2) :: (u, 2) :: P) G)
      by sec_eq.
    replace (HC [] 3 9 2 ((2, 2) :: (u, 2) :: P) G)
      with (HC [] 3 (S 8) 2 ((S 1, 2) :: (u, 2) :: P) G) by sec_eq.
    apply hTUP. }
  replace (HC [] 3 9 2 ((2, 2) :: (u, 2) :: P) G)
    with (HC [] 3 (2*3 + 3) 2 ((2, 2) :: (u, 2) :: P) G) by sec_eq.
  replace (HB [] 4 1 13 ((2, 2) :: (u, 2) :: P) G)
    with (HB [] (S 3) 1 (2*3 + 7) ((2, 2) :: (u, 2) :: P) G) by sec_eq.
  apply hGRIND_dev.
Qed.

Lemma REBASE : forall u P G, 3 <= u ->
  hsteps (HC [] 4 12 2 ((u, 2) :: P) G)
         (HC [5] 13 1 2 ((u - 2, 2) :: P) G).
Proof.
  intros u P G Hu.
  apply (hsteps_trans _ (HB [] 4 1 13 ((2, 2) :: (u, 2) :: P) G)).
  - apply REBASE_core.
  - apply (hsteps_step _ (HC [5] 13 1 2 ((u - 2, 2) :: P) G)).
    { replace (HB [] 4 1 13 ((2, 2) :: (u, 2) :: P) G)
        with (HB [] 4 1 (S 12)
                 ((2, S (S 0)) :: (S (S (S (u - 3))), 2) :: P) G)
        by sec_eq.
      replace (HC [5] 13 1 2 ((u - 2, 2) :: P) G)
        with (HC (S 4 :: []) (S 12) (S 0) 2 ((S (u - 3), 2) :: P) G)
        by sec_eq.
      apply hTUP2_1. }
    apply hsteps_refl.
Qed.

(* Invariant-threaded versions (grind_inv holds at every boundary: *)
(* all frames here have a, a2 >= 1, so the _pos lemmas discharge).  *)

Lemma REBASE_core_P : forall u P G,
  hstepsP grind_inv (HC [] 4 12 2 ((u, 2) :: P) G)
         (HB [] 4 1 13 ((2, 2) :: (u, 2) :: P) G).
Proof.
  intros u P G.
  apply (hstepsP_step _ _ (HC [] 3 1 2 ((10, 2) :: (u, 2) :: P) G)).
  { apply inv_HC_pos; lia. }
  { replace (HC [] 4 12 2 ((u, 2) :: P) G)
      with (HC [] (S 3) (S (S (S 9))) 2 ((u, 2) :: P) G) by sec_eq.
    replace (HC [] 3 1 2 ((10, 2) :: (u, 2) :: P) G)
      with (HC [] 3 1 2 ((S 9, 2) :: (u, 2) :: P) G) by sec_eq.
    apply hPUSH. }
  apply (hstepsP_step _ _ (HB [] 3 1 4 ((10, 2) :: (u, 2) :: P) G)).
  { apply inv_HC_low. }
  { apply hTDN. }
  apply (hstepsP_step _ _ (HC [] 3 3 2 ((8, 2) :: (u, 2) :: P) G)).
  { apply inv_HB_pos; lia. }
  { replace (HB [] 3 1 4 ((10, 2) :: (u, 2) :: P) G)
      with (HB [] 3 1 (S (S 2)) ((S (S (S 7)), 2) :: (u, 2) :: P) G)
      by sec_eq.
    replace (HC [] 3 3 2 ((8, 2) :: (u, 2) :: P) G)
      with (HC [] 3 (S 2) 2 ((S 7, 2) :: (u, 2) :: P) G) by sec_eq.
    apply hTUP. }
  apply (hstepsP_trans _ _ (HB [] 3 1 6 ((8, 2) :: (u, 2) :: P) G)).
  { replace (HC [] 3 3 2 ((8, 2) :: (u, 2) :: P) G)
      with (HC [] 3 (2*0 + 3) 2 ((8, 2) :: (u, 2) :: P) G) by sec_eq.
    replace (HB [] 3 1 6 ((8, 2) :: (u, 2) :: P) G)
      with (HB [] 3 1 (2*0 + 6) ((8, 2) :: (u, 2) :: P) G) by sec_eq.
    apply hGRIND_P; lia. }
  apply (hstepsP_step _ _ (HC [] 3 5 2 ((6, 2) :: (u, 2) :: P) G)).
  { apply inv_HB_pos; lia. }
  { replace (HB [] 3 1 6 ((8, 2) :: (u, 2) :: P) G)
      with (HB [] 3 1 (S (S 4)) ((S (S (S 5)), 2) :: (u, 2) :: P) G)
      by sec_eq.
    replace (HC [] 3 5 2 ((6, 2) :: (u, 2) :: P) G)
      with (HC [] 3 (S 4) 2 ((S 5, 2) :: (u, 2) :: P) G) by sec_eq.
    apply hTUP. }
  apply (hstepsP_trans _ _ (HB [] 3 1 8 ((6, 2) :: (u, 2) :: P) G)).
  { replace (HC [] 3 5 2 ((6, 2) :: (u, 2) :: P) G)
      with (HC [] 3 (2*1 + 3) 2 ((6, 2) :: (u, 2) :: P) G) by sec_eq.
    replace (HB [] 3 1 8 ((6, 2) :: (u, 2) :: P) G)
      with (HB [] 3 1 (2*1 + 6) ((6, 2) :: (u, 2) :: P) G) by sec_eq.
    apply hGRIND_P; lia. }
  apply (hstepsP_step _ _ (HC [] 3 7 2 ((4, 2) :: (u, 2) :: P) G)).
  { apply inv_HB_pos; lia. }
  { replace (HB [] 3 1 8 ((6, 2) :: (u, 2) :: P) G)
      with (HB [] 3 1 (S (S 6)) ((S (S (S 3)), 2) :: (u, 2) :: P) G)
      by sec_eq.
    replace (HC [] 3 7 2 ((4, 2) :: (u, 2) :: P) G)
      with (HC [] 3 (S 6) 2 ((S 3, 2) :: (u, 2) :: P) G) by sec_eq.
    apply hTUP. }
  apply (hstepsP_trans _ _ (HB [] 3 1 10 ((4, 2) :: (u, 2) :: P) G)).
  { replace (HC [] 3 7 2 ((4, 2) :: (u, 2) :: P) G)
      with (HC [] 3 (2*2 + 3) 2 ((4, 2) :: (u, 2) :: P) G) by sec_eq.
    replace (HB [] 3 1 10 ((4, 2) :: (u, 2) :: P) G)
      with (HB [] 3 1 (2*2 + 6) ((4, 2) :: (u, 2) :: P) G) by sec_eq.
    apply hGRIND_P; lia. }
  apply (hstepsP_step _ _ (HC [] 3 9 2 ((2, 2) :: (u, 2) :: P) G)).
  { apply inv_HB_pos; lia. }
  { replace (HB [] 3 1 10 ((4, 2) :: (u, 2) :: P) G)
      with (HB [] 3 1 (S (S 8)) ((S (S (S 1)), 2) :: (u, 2) :: P) G)
      by sec_eq.
    replace (HC [] 3 9 2 ((2, 2) :: (u, 2) :: P) G)
      with (HC [] 3 (S 8) 2 ((S 1, 2) :: (u, 2) :: P) G) by sec_eq.
    apply hTUP. }
  replace (HC [] 3 9 2 ((2, 2) :: (u, 2) :: P) G)
    with (HC [] 3 (2*3 + 3) 2 ((2, 2) :: (u, 2) :: P) G) by sec_eq.
  replace (HB [] 4 1 13 ((2, 2) :: (u, 2) :: P) G)
    with (HB [] (S 3) 1 (2*3 + 7) ((2, 2) :: (u, 2) :: P) G) by sec_eq.
  apply hGRIND_dev_P.
Qed.

Lemma REBASE_P : forall u P G, 3 <= u ->
  hstepsP grind_inv (HC [] 4 12 2 ((u, 2) :: P) G)
         (HC [5] 13 1 2 ((u - 2, 2) :: P) G).
Proof.
  intros u P G Hu.
  apply (hstepsP_trans _ _ (HB [] 4 1 13 ((2, 2) :: (u, 2) :: P) G)).
  - apply REBASE_core_P.
  - apply (hstepsP_step _ _ (HC [5] 13 1 2 ((u - 2, 2) :: P) G)).
    { apply inv_HB_pos; lia. }
    { replace (HB [] 4 1 13 ((2, 2) :: (u, 2) :: P) G)
        with (HB [] 4 1 (S 12)
                 ((2, S (S 0)) :: (S (S (S (u - 3))), 2) :: P) G)
        by sec_eq.
      replace (HC [5] 13 1 2 ((u - 2, 2) :: P) G)
        with (HC (S 4 :: []) (S 12) (S 0) 2 ((S (u - 3), 2) :: P) G)
        by sec_eq.
      apply hTUP2_1. }
    apply hstepsP_refl.
    apply inv_HC_pos; lia.
Qed.

(* ================================================================= *)
(*  Part 2: the R >= 12 ESC grind up to the REBASE source.           *)
(* ================================================================= *)

Lemma ESC_GRIND_BIG : forall R P G, 12 <= R ->
  hsteps (HC [] 3 1 2 ((R, 2) :: P) G)
         (HC [] 4 12 2 ((R - 10, 2) :: P) G).
Proof.
  intros R P G HR.
  apply (hsteps_trans _ (HB [] 3 1 6 ((R - 2, 2) :: P) G)).
  { replace (HC [] 3 1 2 ((R, 2) :: P) G)
      with (HC [] (S 2) 1 2 ((S (S (S (R - 3))), 2) :: P) G) by sec_eq.
    replace (HB [] 3 1 6 ((R - 2, 2) :: P) G)
      with (HB [] (S 2) 1 6 ((S (R - 3), 2) :: P) G) by sec_eq.
    apply grind_prefix. }
  apply (hsteps_trans _ (HB [] 3 1 8 ((R - 4, 2) :: P) G)).
  { replace (HB [] 3 1 6 ((R - 2, 2) :: P) G)
      with (HB [] 3 1 (2*1 + 4) ((R - 2, 2) :: P) G) by sec_eq.
    replace (HB [] 3 1 8 ((R - 4, 2) :: P) G)
      with (HB [] 3 1 (2*1 + 6) ((R - 2 - 2, 2) :: P) G) by sec_eq.
    apply grind_round; lia. }
  apply (hsteps_trans _ (HB [] 3 1 10 ((R - 6, 2) :: P) G)).
  { replace (HB [] 3 1 8 ((R - 4, 2) :: P) G)
      with (HB [] 3 1 (2*2 + 4) ((R - 4, 2) :: P) G) by sec_eq.
    replace (HB [] 3 1 10 ((R - 6, 2) :: P) G)
      with (HB [] 3 1 (2*2 + 6) ((R - 4 - 2, 2) :: P) G) by sec_eq.
    apply grind_round; lia. }
  apply (hsteps_step _ (HC [] 3 9 2 ((R - 8, 2) :: P) G)).
  { replace (HB [] 3 1 10 ((R - 6, 2) :: P) G)
      with (HB [] 3 1 (S (S 8)) ((S (S (S (R - 9))), 2) :: P) G)
      by sec_eq.
    replace (HC [] 3 9 2 ((R - 8, 2) :: P) G)
      with (HC [] 3 (S 8) 2 ((S (R - 9), 2) :: P) G) by sec_eq.
    apply hTUP. }
  apply (hsteps_trans _ (HB [] 4 1 13 ((R - 8, 2) :: P) G)).
  { replace (HC [] 3 9 2 ((R - 8, 2) :: P) G)
      with (HC [] 3 (2*3 + 3) 2 ((R - 8, 2) :: P) G) by sec_eq.
    replace (HB [] 4 1 13 ((R - 8, 2) :: P) G)
      with (HB [] (S 3) 1 (2*3 + 7) ((R - 8, 2) :: P) G) by sec_eq.
    apply hGRIND_dev. }
  apply (hsteps_step _ (HC [] 4 12 2 ((R - 10, 2) :: P) G)).
  { replace (HB [] 4 1 13 ((R - 8, 2) :: P) G)
      with (HB [] 4 1 (S (S 11)) ((S (S (S (R - 11))), 2) :: P) G)
      by sec_eq.
    replace (HC [] 4 12 2 ((R - 10, 2) :: P) G)
      with (HC [] 4 (S 11) 2 ((S (R - 11), 2) :: P) G) by sec_eq.
    apply hTUP. }
  apply hsteps_refl.
Qed.

Lemma ESC_GRIND_BIG_P : forall R P G, 12 <= R ->
  hstepsP grind_inv (HC [] 3 1 2 ((R, 2) :: P) G)
         (HC [] 4 12 2 ((R - 10, 2) :: P) G).
Proof.
  intros R P G HR.
  apply (hstepsP_trans _ _ (HB [] 3 1 6 ((R - 2, 2) :: P) G)).
  { replace (HC [] 3 1 2 ((R, 2) :: P) G)
      with (HC [] (S 2) 1 2 ((S (S (S (R - 3))), 2) :: P) G) by sec_eq.
    replace (HB [] 3 1 6 ((R - 2, 2) :: P) G)
      with (HB [] (S 2) 1 6 ((S (R - 3), 2) :: P) G) by sec_eq.
    apply grind_prefix_P. }
  apply (hstepsP_trans _ _ (HB [] 3 1 8 ((R - 4, 2) :: P) G)).
  { replace (HB [] 3 1 6 ((R - 2, 2) :: P) G)
      with (HB [] 3 1 (2*1 + 4) ((R - 2, 2) :: P) G) by sec_eq.
    replace (HB [] 3 1 8 ((R - 4, 2) :: P) G)
      with (HB [] 3 1 (2*1 + 6) ((R - 2 - 2, 2) :: P) G) by sec_eq.
    apply grind_round_P; lia. }
  apply (hstepsP_trans _ _ (HB [] 3 1 10 ((R - 6, 2) :: P) G)).
  { replace (HB [] 3 1 8 ((R - 4, 2) :: P) G)
      with (HB [] 3 1 (2*2 + 4) ((R - 4, 2) :: P) G) by sec_eq.
    replace (HB [] 3 1 10 ((R - 6, 2) :: P) G)
      with (HB [] 3 1 (2*2 + 6) ((R - 4 - 2, 2) :: P) G) by sec_eq.
    apply grind_round_P; lia. }
  apply (hstepsP_step _ _ (HC [] 3 9 2 ((R - 8, 2) :: P) G)).
  { apply inv_HB_pos; lia. }
  { replace (HB [] 3 1 10 ((R - 6, 2) :: P) G)
      with (HB [] 3 1 (S (S 8)) ((S (S (S (R - 9))), 2) :: P) G)
      by sec_eq.
    replace (HC [] 3 9 2 ((R - 8, 2) :: P) G)
      with (HC [] 3 (S 8) 2 ((S (R - 9), 2) :: P) G) by sec_eq.
    apply hTUP. }
  apply (hstepsP_trans _ _ (HB [] 4 1 13 ((R - 8, 2) :: P) G)).
  { replace (HC [] 3 9 2 ((R - 8, 2) :: P) G)
      with (HC [] 3 (2*3 + 3) 2 ((R - 8, 2) :: P) G) by sec_eq.
    replace (HB [] 4 1 13 ((R - 8, 2) :: P) G)
      with (HB [] (S 3) 1 (2*3 + 7) ((R - 8, 2) :: P) G) by sec_eq.
    apply hGRIND_dev_P. }
  apply (hstepsP_step _ _ (HC [] 4 12 2 ((R - 10, 2) :: P) G)).
  { apply inv_HB_pos; lia. }
  { replace (HB [] 4 1 13 ((R - 8, 2) :: P) G)
      with (HB [] 4 1 (S (S 11)) ((S (S (S (R - 11))), 2) :: P) G)
      by sec_eq.
    replace (HC [] 4 12 2 ((R - 10, 2) :: P) G)
      with (HC [] 4 (S 11) 2 ((S (R - 11), 2) :: P) G) by sec_eq.
    apply hTUP. }
  apply hstepsP_refl.
  apply inv_HC_pos; lia.
Qed.

(* ================================================================= *)
(*  Part 3: the ESC grind endpoints for R = 12, R = 14 and          *)
(*  R = 2m + 16 (m <= 12), in ESC_TO_REGEN's form.                  *)
(* ================================================================= *)

Lemma ESC_TO_REGEN_12 : forall beta, 2 <= beta ->
  exists pb a,
    hsteps (HC [] 3 1 2 ((12, 2) :: (1, 1) :: repeat (1, 2) (beta - 1)) 1)
           (HB pb a 1 (2 * beta + 1) [] 1)
    /\ beta <= a.
Proof.
  intros beta Hb.
  exists [14; 5], (beta + 2). split; [| lia].
  apply (hsteps_trans _
    (HC [] 4 12 2 ((2, 2) :: (1, 1) :: repeat (1, 2) (beta - 1)) 1)).
  { replace (HC [] 4 12 2 ((2, 2) :: (1, 1) :: repeat (1, 2) (beta - 1)) 1)
      with (HC [] 4 12 2 ((12 - 10, 2) :: (1, 1)
                            :: repeat (1, 2) (beta - 1)) 1)
      by sec_eq.
    apply ESC_GRIND_BIG; lia. }
  apply (hsteps_trans _
    (HB [] 4 1 13 ((2, 2) :: (2, 2) :: (1, 1)
                      :: repeat (1, 2) (beta - 1)) 1)).
  { apply REBASE_core. }
  apply (hsteps_trans _
    (HB [14; 5] 3 1 3 (repeat (1, 2) (beta - 1)) 1)).
  { apply (hsteps_step _
      (HB [14; 5] 3 1 3 (repeat (1, 2) (beta - 1)) 1)).
    { replace (HB [] 4 1 13 ((2, 2) :: (2, 2) :: (1, 1)
                                :: repeat (1, 2) (beta - 1)) 1)
        with (HB [] 4 1 (S 12)
                 ((2, S 1) :: (2, S 1) :: (1, 1)
                    :: repeat (1, 2) (beta - 1)) 1)
        by sec_eq.
      replace (HB [14; 5] 3 1 3 (repeat (1, 2) (beta - 1)) 1)
        with (HB (S (S 12) :: S 4 :: []) (S (S 1)) 1 (S 1 + 1)
                 (repeat (1, 2) (beta - 1)) 1)
        by sec_eq.
      apply hTRANS2_2; lia. }
    apply hsteps_refl. }
  replace (HB [14; 5] (beta + 2) 1 (2 * beta + 1) [] 1)
    with (HB [14; 5] (3 + (beta - 1)) 1 (3 + 2 * (beta - 1)) [] 1)
    by sec_eq.
  apply pop_chain_h; lia.
Qed.

Lemma ESC_TO_REGEN_14 : forall beta, 2 <= beta ->
  exists pb a,
    hsteps (HC [] 3 1 2 ((14, 2) :: (1, 1) :: repeat (1, 2) (beta - 1)) 1)
           (HB pb a 1 (2 * beta + 1) [] 1)
    /\ beta <= a.
Proof.
  intros beta Hb.
  exists [14; 5], (4 + beta). split; [| lia].
  apply (hsteps_trans _
    (HC [] 4 12 2 ((4, 2) :: (1, 1) :: repeat (1, 2) (beta - 1)) 1)).
  { replace (HC [] 4 12 2 ((4, 2) :: (1, 1) :: repeat (1, 2) (beta - 1)) 1)
      with (HC [] 4 12 2 ((14 - 10, 2) :: (1, 1)
                            :: repeat (1, 2) (beta - 1)) 1)
      by sec_eq.
    apply ESC_GRIND_BIG; lia. }
  apply (hsteps_trans _
    (HC [5] 13 1 2 ((2, 2) :: (1, 1) :: repeat (1, 2) (beta - 1)) 1)).
  { replace (HC [5] 13 1 2 ((2, 2) :: (1, 1) :: repeat (1, 2) (beta - 1)) 1)
      with (HC [5] 13 1 2 ((4 - 2, 2) :: (1, 1)
                             :: repeat (1, 2) (beta - 1)) 1)
      by sec_eq.
    apply REBASE; lia. }
  apply (hsteps_trans _
    (HB [5] 13 1 4 ((2, 2) :: (1, 1) :: repeat (1, 2) (beta - 1)) 1)).
  { apply (hsteps_step _
      (HB [5] 13 1 4 ((2, 2) :: (1, 1) :: repeat (1, 2) (beta - 1)) 1)).
    { apply hTDN. }
    apply hsteps_refl. }
  apply TAIL; lia.
Qed.

Lemma ESC_TO_REGEN_BIG : forall m beta, m <= 12 -> 2 <= beta ->
  exists pb a,
    hsteps (HC [] 3 1 2 ((2 * m + 16, 2) :: (1, 1)
                            :: repeat (1, 2) (beta - 1)) 1)
           (HB pb a 1 (2 * beta + 1) [] 1)
    /\ beta <= a.
Proof.
  intros m beta Hm Hb.
  exists [14; 5], (2 * m + 6 + beta). split; [| lia].
  apply (hsteps_trans _
    (HC [] 4 12 2 ((2 * m + 6, 2) :: (1, 1)
                      :: repeat (1, 2) (beta - 1)) 1)).
  { replace (HC [] 4 12 2 ((2 * m + 6, 2) :: (1, 1)
                              :: repeat (1, 2) (beta - 1)) 1)
      with (HC [] 4 12 2 ((2 * m + 16 - 10, 2) :: (1, 1)
                            :: repeat (1, 2) (beta - 1)) 1)
      by sec_eq.
    apply ESC_GRIND_BIG; lia. }
  apply (hsteps_trans _
    (HC [5] 13 1 2 ((2 * m + 4, 2) :: (1, 1)
                       :: repeat (1, 2) (beta - 1)) 1)).
  { replace (HC [5] 13 1 2 ((2 * m + 4, 2) :: (1, 1)
                               :: repeat (1, 2) (beta - 1)) 1)
      with (HC [5] 13 1 2 ((2 * m + 6 - 2, 2) :: (1, 1)
                             :: repeat (1, 2) (beta - 1)) 1)
      by sec_eq.
    apply REBASE; lia. }
  apply (hsteps_trans _
    (HB [5] 13 1 (2 * m + 6) ((2, 2) :: (1, 1)
                                 :: repeat (1, 2) (beta - 1)) 1)).
  { apply GG_clean; lia. }
  apply TAIL; lia.
Qed.

(* ================================================================= *)
(*  Part 4: the ESC-era law for every even R <= 40.  The assembly   *)
(*  after the grind endpoint is Grind2.ESC_ERA_LAW's, factored      *)
(*  into ESC_ERA_LAW_of so each new endpoint reuses it verbatim.    *)
(* ================================================================= *)

Lemma ESC_ERA_LAW_of : forall R beta pb a,
  1 <= R ->
  hsteps (HC [] 3 1 2 ((R, 2) :: (1, 1) :: repeat (1, 2) (beta - 1)) 1)
         (HB pb a 1 (2 * beta + 1) [] 1) ->
  beta <= a -> 2 <= beta ->
  exists n c pb' a',
    run n (esc_src (R + 6) (beta - 2)) = Some c
    /\ cfg_sim c (rcsec (false :: repeat true (S a') ++ enc pb')
                        (2 * beta + 2) [(1, 2)])
    /\ beta <= a'.
Proof.
  intros R beta pb a HRge Hchain Hfloor Hb.
  destruct (hsteps_sound _ _ Hchain) as [n2 [c2 [Hr2 Hs2]]].
  destruct (ERA_TAIL pb a beta Hb ltac:(lia)) as [n3 [c3 [Hr3 Hs3]]].
  pose proof (PROBE_PREFIX (R - 1) (beta - 2)) as Hprobe.
  replace (R - 1 + 7) with (R + 6) in Hprobe by lia.
  replace (S (R - 1)) with R in Hprobe by lia.
  pose proof (PROBE_PREFIX_sim R (beta - 2)) as Hsim0.
  replace (S (beta - 2)) with (beta - 1) in Hsim0 by lia.
  rewrite <- (gcsec_nil 3 1 2
    ((R, 2) :: (1, 1) :: repeat (1, 2) (beta - 1)) 1) in Hsim0.
  change (hcfg (HC [] 3 1 2 ((R, 2) :: (1, 1) :: repeat (1, 2) (beta - 1)) 1))
    with (gcsec (enc []) 3 1 2 ((R, 2) :: (1, 1) :: repeat (1, 2) (beta - 1)) 1)
    in Hr2.
  change (enc []) with ([] : list sym) in Hr2.
  destruct (run_sim_transfer n2 (e5form R (beta - 2))
              (gcsec [] 3 1 2 ((R, 2) :: (1, 1) :: repeat (1, 2) (beta - 1)) 1)
              c2 Hsim0 Hr2)
    as [c2' [Hr2' Hs2']].
  assert (Hsim2 : cfg_sim c2' (hcfg (HB pb a 1 (2 * beta + 1) [] 1))).
  { apply (cfg_sim_trans _ _ _ Hs2' Hs2). }
  destruct (run_sim_transfer n3 c2'
              (hcfg (HB pb a 1 (2 * beta + 1) [] 1)) c3 Hsim2 Hr3)
    as [c3' [Hr3' Hs3']].
  exists ((R - 1 + 49) + (n2 + n3)), c3', pb, a.
  split; [| split].
  - rewrite run_split. rewrite Hprobe.
    rewrite run_split. rewrite Hr2'. exact Hr3'.
  - apply (cfg_sim_trans _ _ _ Hs3' Hs3).
  - exact Hfloor.
Qed.

Lemma esc_disj_split : forall R,
  (R = 2 \/ R = 4 \/ R = 6 \/ R = 8 \/ R = 10 \/ R = 12 \/ R = 14
   \/ (exists m, R = 2 * m + 16 /\ m <= 12)) ->
  (R = 2 \/ R = 4 \/ R = 6 \/ R = 8 \/ R = 10)
  \/ R = 12 \/ R = 14
  \/ (exists m, R = 2 * m + 16 /\ m <= 12).
Proof.
  intros R [E|[E|[E|[E|[E|[E|[E|HM]]]]]]].
  - left. left. exact E.
  - left. right. left. exact E.
  - left. right. right. left. exact E.
  - left. right. right. right. left. exact E.
  - left. right. right. right. right. exact E.
  - right. left. exact E.
  - right. right. left. exact E.
  - right. right. right. exact HM.
Qed.

Lemma ESC_ERA_LAW_31 : forall R beta,
  (R = 2 \/ R = 4 \/ R = 6 \/ R = 8 \/ R = 10 \/ R = 12 \/ R = 14
   \/ (exists m, R = 2 * m + 16 /\ m <= 12)) -> 2 <= beta ->
  exists n c pb a,
    run n (esc_src (R + 6) (beta - 2)) = Some c
    /\ cfg_sim c (rcsec (false :: repeat true (S a) ++ enc pb)
                        (2 * beta + 2) [(1, 2)])
    /\ beta <= a.
Proof.
  intros R beta HR Hb.
  destruct (esc_disj_split R HR) as [HOLD | [E12 | [E14 | HM]]].
  - apply ESC_ERA_LAW; assumption.
  - subst R.
    destruct (ESC_TO_REGEN_12 beta Hb) as [pb [a [Hc Hf]]].
    apply (ESC_ERA_LAW_of 12 beta pb a); [lia | exact Hc | exact Hf | exact Hb].
  - subst R.
    destruct (ESC_TO_REGEN_14 beta Hb) as [pb [a [Hc Hf]]].
    apply (ESC_ERA_LAW_of 14 beta pb a); [lia | exact Hc | exact Hf | exact Hb].
  - destruct HM as [m [ER Hm]]. subst R.
    destruct (ESC_TO_REGEN_BIG m beta Hm Hb) as [pb [a [Hc Hf]]].
    apply (ESC_ERA_LAW_of (2 * m + 16) beta pb a);
      [lia | exact Hc | exact Hf | exact Hb].
Qed.

(* Axiom audit for this file's headline lemmas. *)
Print Assumptions REBASE_core.
Print Assumptions REBASE.
Print Assumptions REBASE_core_P.
Print Assumptions REBASE_P.
Print Assumptions ESC_GRIND_BIG.
Print Assumptions ESC_GRIND_BIG_P.
Print Assumptions ESC_TO_REGEN_12.
Print Assumptions ESC_TO_REGEN_14.
Print Assumptions ESC_TO_REGEN_BIG.
Print Assumptions ESC_ERA_LAW_of.
Print Assumptions ESC_ERA_LAW_31.
