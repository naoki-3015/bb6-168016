(* ================================================================= *)
(*  Grind9.v -- Phase 41: the phase-8 entry (even R >= 1278), its    *)
(*  funnel and the first three continuation stages.                  *)
(*                                                                   *)
(*  The Phase 40 fence: at R = 2m + 46 with m >= 616, phase 7's      *)
(*  finish breaks at frame ([235; 42; 19], 334): the rounds          *)
(*  (count m - 282) and the final grind (t = m - 282) both exceed    *)
(*  the frame, so every phase-8 entry takes the maximal 334          *)
(*  rounds and the final grind sits at exactly t = 334 = a2: a       *)
(*  boundary grind.  There are no phase-8 finishes of the earlier    *)
(*  kind (no TAIL / TAIL2 / transitional cases): the binding is      *)
(*  uniform in m.                                                    *)
(*                                                                   *)
(*  Mechanised here (all pre-verified in rocq/hsim41.py):            *)
(*   * PHASE8_TO_MID -- PHASE7_TRANS42, the maximal 334 rounds,      *)
(*     TUP, DIPDESC 334, and the dip hPX2A at [235; 42; 19],         *)
(*     landing on the phase-8 continuation source at frame           *)
(*     ([19], 41), g0 = 233 (GRIND233).                              *)
(*   * PHASE8_STAGE_A -- GRIND233's own grind: PUSH/TDN/TUP,         *)
(*     LOOPN 40 (floor met exactly), DIPDESC 40 to its dip at the    *)
(*     single block [19].  That dip fires the NEW dispatch           *)
(*     hPX2Bgen (Dev.v PX2Bgen, b >= 5; Phases 38/40 needed no       *)
(*     new step list -- phase 8 does).                               *)
(*   * PHASE8_STAGE_B -- TUP, TDN, TUP, LOOPN 3, DIPDESC 3, and      *)
(*     the dip hPX2B0 at [0].                                        *)
(*   * PHASE8_STAGE_C -- a POP run of 4, TUP, the even boundary      *)
(*     descent DIPDESC_even 4 (new, general: the g0 = 2t + 4         *)
(*     analogue of DIPDESC, closing onto a (2, 2) pair), hPUSHX,     *)
(*     a POP run of 3, and hTUP2_1 onto frame ([5], 13).             *)
(*   * PHASE8_TO_STAGE_D -- the composition: the mechanised          *)
(*     frontier of phase 8.                                          *)
(*                                                                   *)
(*  The fence beyond the frontier (machine evidence in hsim41.py):   *)
(*  from HC [5] 13 1 2 the continuation grind consumes the ENTIRE    *)
(*  remaining passenger stack -- the (1, 2)^40 spine, the residue    *)
(*  pair (149, 2), the (1, 2)^334 spine, the pair (2m - 1230, 2)     *)
(*  and all of Pe -- cascading through frames [24; 5],               *)
(*  [25; 24; 5], then a four-block and a five-block frame whose      *)
(*  values are iterated arithmetic in the stack contents, not a      *)
(*  closed form (at the hsim41 deep-passenger analogue:              *)
(*  [26; 25; 24; 5], then [13; 26; 25; 24; 5]; at a shallower        *)
(*  passenger: [23; 25; 24; 5], then [7; 23; 25; 24; 5]), and the    *)
(*  word walk ends stuck at a B-section over the EMPTY stack         *)
(*  (HB [13; 26; 25; 24; 5] 30 1 13 [] 1 at the analogue), where      *)
(*  no hstep rule applies; the raw machine's next recognised         *)
(*  sections there are not an era REGEN landing.                     *)
(*  Unlike the phase 6/7/8-stage continuations above, it is NOT      *)
(*  stack-local: no continuation lemma over an arbitrary carried     *)
(*  rest exists.  Closing ESC at phase 8 therefore needs the         *)
(*  totality/landing theorem for the deviation-inclusive grind       *)
(*  identified in Phase 38, not another merged unwind.  The ESC      *)
(*  era law stays at R <= 1276 (ESC_ERA_LAW_1276, Grind8.v);         *)
(*  H_LOOP's ESC instances at R >= 1278 remain open.                 *)
(* ================================================================= *)

Require Import List Bool Arith Lia ZArith.
Import ListNotations.
Require Import TM Sections Mirror TokenPass Recoord Era Esc Dev
               Grind Grind2 Grind3 Grind4 Grind5 Grind6 Grind7 Grind8.

Ltac sec_eq := repeat (first [ solve [reflexivity] | solve [lia]
                             | f_equal ]).

(* ----------------------------------------------------------------- *)
(* Part 1: DIPDESC_even -- the boundary descent at g0 = 2t + 4.      *)
(*                                                                   *)
(* DIPDESC (Grind7.v) descends HC pb t (2t + 3) 2 P to the dip       *)
(* HC pb 0 3 2 ((1, 2)^t ++ P).  The even-g0 boundary grind has      *)
(* the same one-level shape (PUSH/TDN/TUP + LOOPN t, grinding the    *)
(* pushed pair (2t + 2, 2) exactly to (2, 2)) and then closes by     *)
(* DIPDESC itself over the (2, 2) pair:                              *)
(*   HC pb (S u) (2 * S u + 4) 2 P -> HC pb 0 3 2                    *)
(*     ((1, 2)^u ++ ((2, 2) :: P)).                                   *)
(* No floor hypothesis, no induction: a direct composition.          *)
(* ----------------------------------------------------------------- *)

Lemma DIPDESC_even : forall u pb P G,
  hsteps (HC pb (S u) (2 * S u + 4) 2 P G)
         (HC pb 0 3 2 (repeat (1, 2) u ++ ((2, 2) :: P)) G).
Proof.
  intros u pb P G.
  (* PUSH *)
  apply (hsteps_trans _ (HC pb u 1 2 ((2 * u + 4, 2) :: P) G)).
  { apply (hsteps_step _ (HC pb u 1 2 ((2 * u + 4, 2) :: P) G)).
    { replace (HC pb (S u) (2 * S u + 4) 2 P G)
        with (HC pb (S u) (S (S (S (2 * u + 3)))) 2 P G) by sec_eq.
      replace (HC pb u 1 2 ((2 * u + 4, 2) :: P) G)
        with (HC pb u 1 2 ((S (2 * u + 3), 2) :: P) G) by sec_eq.
      apply hPUSH. }
    apply hsteps_refl. }
  (* TDN *)
  apply (hsteps_trans _ (HB pb u 1 4 ((2 * u + 4, 2) :: P) G)).
  { apply (hsteps_step _ (HB pb u 1 4 ((2 * u + 4, 2) :: P) G)).
    { apply hTDN. }
    apply hsteps_refl. }
  (* TUP *)
  apply (hsteps_trans _ (HC pb u 3 2 ((2 * u + 2, 2) :: P) G)).
  { apply (hsteps_step _ (HC pb u 3 2 ((2 * u + 2, 2) :: P) G)).
    { replace (HB pb u 1 4 ((2 * u + 4, 2) :: P) G)
        with (HB pb u 1 (S (S 2))
                ((S (S (S (2 * u + 1))), 2) :: P) G) by sec_eq.
      replace (HC pb u 3 2 ((2 * u + 2, 2) :: P) G)
        with (HC pb u (S 2) 2 ((S (2 * u + 1), 2) :: P) G) by sec_eq.
      apply hTUP. }
    apply hsteps_refl. }
  (* LOOPN u: the pushed pair (2u + 2, 2) ground exactly to (2, 2) *)
  apply (hsteps_trans _ (HC pb u (2 * u + 3) 2 ((2, 2) :: P) G)).
  { replace (HC pb u 3 2 ((2 * u + 2, 2) :: P) G)
      with (HC pb u (2 * 0 + 3) 2 ((2 * u + 2, 2) :: P) G) by sec_eq.
    replace (HC pb u (2 * u + 3) 2 ((2, 2) :: P) G)
      with (HC pb u (2 * (0 + u) + 3) 2
              (((2 * u + 2) - 2 * u, 2) :: P) G) by sec_eq.
    apply (LOOPN u 0 pb u (2 * u + 2) P G); lia. }
  (* DIPDESC u over the (2, 2) pair *)
  apply (DIPDESC u pb ((2, 2) :: P) G).
Qed.

(* ----------------------------------------------------------------- *)
(* Part 2: PHASE8_TO_MID -- the phase-8 funnel.  From phase 7's      *)
(* landing at frame ([42; 19], 235): the transitional segment to     *)
(* frame ([235; 42; 19], 334), the maximal 334 rounds (the frame     *)
(* binds before the passenger: 2 * 334 + 3 <= 2M - 560 iff           *)
(* M >= 616), TUP, the boundary descent DIPDESC 334, and the dip     *)
(* hPX2A at [235; 42; 19] onto frame ([19], 41), g0 = 233.           *)
(* ----------------------------------------------------------------- *)

Lemma PHASE8_TO_MID : forall M beta, 616 <= M -> 2 <= beta ->
  hsteps (HB [42; 19] 235 1 335
            ((2 * M - 556, 2) :: (1, 1) :: repeat (1, 2) (beta - 1)) 1)
         (HC [19] 41 233 2
            ((1, 1) :: (1, 2) :: (1, 2) ::
             repeat (1, 2) 334 ++
             ((2 * M - 1230, 2) :: (1, 1) ::
              repeat (1, 2) (beta - 1))) 1).
Proof.
  intros M beta HM Hb.
  (* PHASE7_TRANS42 *)
  apply (hsteps_trans _ (HB [235; 42; 19] 334 1 4
      ((2 * M - 560, 2) :: (1, 1) :: repeat (1, 2) (beta - 1)) 1)).
  { replace (HB [235; 42; 19] 334 1 4
        ((2 * M - 560, 2) :: (1, 1) :: repeat (1, 2) (beta - 1)) 1)
      with (HB [235; 42; 19] 334 1 4
        ((2 * M - 556 - 4, 2) :: (1, 1) :: repeat (1, 2) (beta - 1)) 1)
      by sec_eq.
    apply (PHASE7_TRANS42 (2 * M - 556) beta); lia. }
  (* the maximal 334 rounds *)
  apply (hsteps_trans _ (HB [235; 42; 19] 334 1 (2 * (0 + 334) + 4)
      (((2 * M - 560) - 2 * 334, 2) ::
       (1, 1) :: repeat (1, 2) (beta - 1)) 1)).
  { replace (HB [235; 42; 19] 334 1 4
        ((2 * M - 560, 2) :: (1, 1) :: repeat (1, 2) (beta - 1)) 1)
      with (HB [235; 42; 19] 334 1 (2 * 0 + 4)
        ((2 * M - 560, 2) :: (1, 1) :: repeat (1, 2) (beta - 1)) 1)
      by sec_eq.
    apply (rounds_from4g 334 0 [235; 42; 19] 334 (2 * M - 560)
             ((1, 1) :: repeat (1, 2) (beta - 1)) 1); lia. }
  (* TUP *)
  apply (hsteps_trans _ (HC [235; 42; 19] 334 671 2
      ((2 * M - 1230, 2) :: (1, 1) :: repeat (1, 2) (beta - 1)) 1)).
  { apply (hsteps_step _ (HC [235; 42; 19] 334 671 2
        ((2 * M - 1230, 2) :: (1, 1) :: repeat (1, 2) (beta - 1)) 1)).
    { replace (HB [235; 42; 19] 334 1 (2 * (0 + 334) + 4)
          (((2 * M - 560) - 2 * 334, 2) ::
           (1, 1) :: repeat (1, 2) (beta - 1)) 1)
        with (HB [235; 42; 19] 334 1 (S (S 670))
          ((S (S (S (2 * M - 1231))), 2) ::
           (1, 1) :: repeat (1, 2) (beta - 1)) 1) by sec_eq.
      replace (HC [235; 42; 19] 334 671 2
          ((2 * M - 1230, 2) :: (1, 1) :: repeat (1, 2) (beta - 1)) 1)
        with (HC [235; 42; 19] 334 (S 670) 2
          ((S (2 * M - 1231), 2) ::
           (1, 1) :: repeat (1, 2) (beta - 1)) 1) by sec_eq.
      apply hTUP. }
    apply hsteps_refl. }
  (* DIPDESC 334 *)
  apply (hsteps_trans _ (HC [235; 42; 19] 0 3 2
      (repeat (1, 2) 334 ++
       ((2 * M - 1230, 2) :: (1, 1) :: repeat (1, 2) (beta - 1))) 1)).
  { replace (HC [235; 42; 19] 334 671 2
        ((2 * M - 1230, 2) :: (1, 1) :: repeat (1, 2) (beta - 1)) 1)
      with (HC [235; 42; 19] 334 (2 * 334 + 3) 2
        ((2 * M - 1230, 2) :: (1, 1) :: repeat (1, 2) (beta - 1)) 1)
      by sec_eq.
    apply (DIPDESC 334 [235; 42; 19]
             ((2 * M - 1230, 2) :: (1, 1) ::
              repeat (1, 2) (beta - 1)) 1). }
  (* the dip: hPX2A at [235; 42; 19] *)
  apply (hsteps_step _ (HC [19] 41 233 2
      ((1, 1) :: (1, 2) :: (1, 2) ::
       repeat (1, 2) 334 ++
       ((2 * M - 1230, 2) :: (1, 1) :: repeat (1, 2) (beta - 1))) 1)).
  { replace (HC [235; 42; 19] 0 3 2
        (repeat (1, 2) 334 ++
         ((2 * M - 1230, 2) :: (1, 1) :: repeat (1, 2) (beta - 1))) 1)
      with (HC (S (S (S 232)) :: S 41 :: [19]) 0 3 2
        (repeat (1, 2) 334 ++
         ((2 * M - 1230, 2) :: (1, 1) :: repeat (1, 2) (beta - 1))) 1)
      by sec_eq.
    replace (HC [19] 41 233 2
        ((1, 1) :: (1, 2) :: (1, 2) ::
         repeat (1, 2) 334 ++
         ((2 * M - 1230, 2) :: (1, 1) :: repeat (1, 2) (beta - 1))) 1)
      with (HC [19] 41 (S 232) 2
        ((1, 1) :: (1, 2) :: (1, 2) ::
         repeat (1, 2) 334 ++
         ((2 * M - 1230, 2) :: (1, 1) :: repeat (1, 2) (beta - 1))) 1)
      by sec_eq.
    apply hPX2A. }
  apply hsteps_refl.
Qed.

(* ----------------------------------------------------------------- *)
(* Part 3: PHASE8_STAGE_A -- the GRIND233 grind at frame             *)
(* ([19], 41), g0 = 233, over an arbitrary carried rest:             *)
(* PUSH/TDN/TUP, LOOPN 40 (floor 0 + 40 <= 41 met exactly),          *)
(* DIPDESC 40 to the dip at the single block [19], and the new       *)
(* dispatch hPX2Bgen (b = 19 >= 5).                                  *)
(* ----------------------------------------------------------------- *)

Lemma PHASE8_STAGE_A : forall Rest G,
  hsteps (HC [19] 41 233 2 ((1, 1) :: (1, 2) :: (1, 2) :: Rest) G)
         (HB [0] 3 1 2
            ((15, 2) :: (1, 1) :: (1, 2) :: (1, 2) ::
             repeat (1, 2) 40 ++
             ((149, 2) :: (1, 1) :: (1, 2) :: (1, 2) :: Rest)) G).
Proof.
  intros Rest G.
  (* PUSH *)
  apply (hsteps_trans _ (HC [19] 40 1 2
      ((231, 2) :: (1, 1) :: (1, 2) :: (1, 2) :: Rest) G)).
  { apply (hsteps_step _ (HC [19] 40 1 2
        ((231, 2) :: (1, 1) :: (1, 2) :: (1, 2) :: Rest) G)).
    { replace (HC [19] 41 233 2 ((1, 1) :: (1, 2) :: (1, 2) :: Rest) G)
        with (HC [19] (S 40) (S (S (S 230))) 2
                ((1, 1) :: (1, 2) :: (1, 2) :: Rest) G) by sec_eq.
      replace (HC [19] 40 1 2
          ((231, 2) :: (1, 1) :: (1, 2) :: (1, 2) :: Rest) G)
        with (HC [19] 40 1 2
                ((S 230, 2) :: (1, 1) :: (1, 2) :: (1, 2) :: Rest) G)
        by sec_eq.
      apply hPUSH. }
    apply hsteps_refl. }
  (* TDN *)
  apply (hsteps_trans _ (HB [19] 40 1 4
      ((231, 2) :: (1, 1) :: (1, 2) :: (1, 2) :: Rest) G)).
  { apply (hsteps_step _ (HB [19] 40 1 4
        ((231, 2) :: (1, 1) :: (1, 2) :: (1, 2) :: Rest) G)).
    { apply hTDN. }
    apply hsteps_refl. }
  (* TUP *)
  apply (hsteps_trans _ (HC [19] 40 3 2
      ((229, 2) :: (1, 1) :: (1, 2) :: (1, 2) :: Rest) G)).
  { apply (hsteps_step _ (HC [19] 40 3 2
        ((229, 2) :: (1, 1) :: (1, 2) :: (1, 2) :: Rest) G)).
    { replace (HB [19] 40 1 4
          ((231, 2) :: (1, 1) :: (1, 2) :: (1, 2) :: Rest) G)
        with (HB [19] 40 1 (S (S 2))
                ((S (S (S 228)), 2) ::
                 (1, 1) :: (1, 2) :: (1, 2) :: Rest) G) by sec_eq.
      replace (HC [19] 40 3 2
          ((229, 2) :: (1, 1) :: (1, 2) :: (1, 2) :: Rest) G)
        with (HC [19] 40 (S 2) 2
                ((S 228, 2) :: (1, 1) :: (1, 2) :: (1, 2) :: Rest) G)
        by sec_eq.
      apply hTUP. }
    apply hsteps_refl. }
  (* LOOPN 40 *)
  apply (hsteps_trans _ (HC [19] 40 (2 * (0 + 40) + 3) 2
      ((229 - 2 * 40, 2) :: (1, 1) :: (1, 2) :: (1, 2) :: Rest) G)).
  { replace (HC [19] 40 3 2
        ((229, 2) :: (1, 1) :: (1, 2) :: (1, 2) :: Rest) G)
      with (HC [19] 40 (2 * 0 + 3) 2
              ((229, 2) :: (1, 1) :: (1, 2) :: (1, 2) :: Rest) G)
      by sec_eq.
    apply (LOOPN 40 0 [19] 40 229
             ((1, 1) :: (1, 2) :: (1, 2) :: Rest) G); lia. }
  (* DIPDESC 40 *)
  apply (hsteps_trans _ (HC [19] 0 3 2
      (repeat (1, 2) 40 ++
       ((149, 2) :: (1, 1) :: (1, 2) :: (1, 2) :: Rest)) G)).
  { replace (HC [19] 40 (2 * (0 + 40) + 3) 2
        ((229 - 2 * 40, 2) :: (1, 1) :: (1, 2) :: (1, 2) :: Rest) G)
      with (HC [19] 40 (2 * 40 + 3) 2
              ((149, 2) :: (1, 1) :: (1, 2) :: (1, 2) :: Rest) G)
      by sec_eq.
    apply (DIPDESC 40 [19]
             ((149, 2) :: (1, 1) :: (1, 2) :: (1, 2) :: Rest) G). }
  (* the dip: hPX2Bgen at [19] *)
  apply (hsteps_step _ (HB [0] 3 1 2
      ((15, 2) :: (1, 1) :: (1, 2) :: (1, 2) ::
       repeat (1, 2) 40 ++
       ((149, 2) :: (1, 1) :: (1, 2) :: (1, 2) :: Rest)) G)).
  { replace (HC [19] 0 3 2
        (repeat (1, 2) 40 ++
         ((149, 2) :: (1, 1) :: (1, 2) :: (1, 2) :: Rest)) G)
      with (HC [S (S (S (S (S 14))))] 0 3 2
        (repeat (1, 2) 40 ++
         ((149, 2) :: (1, 1) :: (1, 2) :: (1, 2) :: Rest)) G)
      by sec_eq.
    replace (HB [0] 3 1 2
        ((15, 2) :: (1, 1) :: (1, 2) :: (1, 2) ::
         repeat (1, 2) 40 ++
         ((149, 2) :: (1, 1) :: (1, 2) :: (1, 2) :: Rest)) G)
      with (HB [0] 3 1 2
        ((S 14, 2) :: (1, 1) :: (1, 2) :: (1, 2) ::
         repeat (1, 2) 40 ++
         ((149, 2) :: (1, 1) :: (1, 2) :: (1, 2) :: Rest)) G)
      by sec_eq.
    apply hPX2Bgen. }
  apply hsteps_refl.
Qed.

(* ----------------------------------------------------------------- *)
(* Part 4: PHASE8_STAGE_B -- from stage A's landing: TUP, TDN,       *)
(* TUP, LOOPN 3 (the (11, 2) pair ground to (5, 2)), DIPDESC 3       *)
(* to the dip at [0], and hPX2B0.  Over an arbitrary carried R2.     *)
(* ----------------------------------------------------------------- *)

Lemma PHASE8_STAGE_B : forall R2 G,
  hsteps (HB [0] 3 1 2 ((15, 2) :: (1, 1) :: R2) G)
         (HB [] 0 1 5
            ((1, 2) :: (1, 2) :: (1, 2) :: (1, 2) ::
             (5, 2) :: (1, 1) :: R2) G).
Proof.
  intros R2 G.
  (* TUP *)
  apply (hsteps_trans _ (HC [0] 3 1 2 ((13, 2) :: (1, 1) :: R2) G)).
  { apply (hsteps_step _ (HC [0] 3 1 2 ((13, 2) :: (1, 1) :: R2) G)).
    { replace (HB [0] 3 1 2 ((15, 2) :: (1, 1) :: R2) G)
        with (HB [0] 3 1 (S (S 0))
                ((S (S (S 12)), 2) :: (1, 1) :: R2) G) by sec_eq.
      replace (HC [0] 3 1 2 ((13, 2) :: (1, 1) :: R2) G)
        with (HC [0] 3 (S 0) 2 ((S 12, 2) :: (1, 1) :: R2) G) by sec_eq.
      apply hTUP. }
    apply hsteps_refl. }
  (* TDN *)
  apply (hsteps_trans _ (HB [0] 3 1 4 ((13, 2) :: (1, 1) :: R2) G)).
  { apply (hsteps_step _ (HB [0] 3 1 4 ((13, 2) :: (1, 1) :: R2) G)).
    { apply hTDN. }
    apply hsteps_refl. }
  (* TUP *)
  apply (hsteps_trans _ (HC [0] 3 3 2 ((11, 2) :: (1, 1) :: R2) G)).
  { apply (hsteps_step _ (HC [0] 3 3 2 ((11, 2) :: (1, 1) :: R2) G)).
    { replace (HB [0] 3 1 4 ((13, 2) :: (1, 1) :: R2) G)
        with (HB [0] 3 1 (S (S 2))
                ((S (S (S 10)), 2) :: (1, 1) :: R2) G) by sec_eq.
      replace (HC [0] 3 3 2 ((11, 2) :: (1, 1) :: R2) G)
        with (HC [0] 3 (S 2) 2 ((S 10, 2) :: (1, 1) :: R2) G) by sec_eq.
      apply hTUP. }
    apply hsteps_refl. }
  (* LOOPN 3 *)
  apply (hsteps_trans _ (HC [0] 3 (2 * (0 + 3) + 3) 2
      ((11 - 2 * 3, 2) :: (1, 1) :: R2) G)).
  { replace (HC [0] 3 3 2 ((11, 2) :: (1, 1) :: R2) G)
      with (HC [0] 3 (2 * 0 + 3) 2 ((11, 2) :: (1, 1) :: R2) G)
      by sec_eq.
    apply (LOOPN 3 0 [0] 3 11 ((1, 1) :: R2) G); lia. }
  (* DIPDESC 3 *)
  apply (hsteps_trans _ (HC [0] 0 3 2
      (repeat (1, 2) 3 ++ ((5, 2) :: (1, 1) :: R2)) G)).
  { replace (HC [0] 3 (2 * (0 + 3) + 3) 2
        ((11 - 2 * 3, 2) :: (1, 1) :: R2) G)
      with (HC [0] 3 (2 * 3 + 3) 2 ((5, 2) :: (1, 1) :: R2) G)
      by sec_eq.
    apply (DIPDESC 3 [0] ((5, 2) :: (1, 1) :: R2) G). }
  (* the dip: hPX2B0 at [0] *)
  apply (hsteps_step _ (HB [] 0 1 5
      ((1, 2) :: (1, 2) :: (1, 2) :: (1, 2) ::
       (5, 2) :: (1, 1) :: R2) G)).
  { replace (HB [] 0 1 5
        ((1, 2) :: (1, 2) :: (1, 2) :: (1, 2) ::
         (5, 2) :: (1, 1) :: R2) G)
      with (HB [] 0 1 5
              ((1, 2) :: (repeat (1, 2) 3 ++ ((5, 2) :: (1, 1) :: R2))) G)
      by sec_eq.
    apply hPX2B0. }
  apply hsteps_refl.
Qed.

(* ----------------------------------------------------------------- *)
(* Part 5: PHASE8_STAGE_C -- from stage B's landing: a POP run       *)
(* of 4 over the (1, 2) prefix, TUP onto the even boundary grind     *)
(* at pb = [] (a2 = 4, g0 = 12 = 2 * 4 + 4), DIPDESC_even 4 to       *)
(* the pb = [] dip, hPUSHX, a POP run of 3, and hTUP2_1 onto         *)
(* frame ([5], 13).  Over an arbitrary carried R2.                   *)
(* ----------------------------------------------------------------- *)

Lemma PHASE8_STAGE_C : forall R2 G,
  hsteps (HB [] 0 1 5
            ((1, 2) :: (1, 2) :: (1, 2) :: (1, 2) ::
             (5, 2) :: (1, 1) :: R2) G)
         (HC [5] 13 1 2 ((1, 2) :: (1, 1) :: R2) G).
Proof.
  intros R2 G.
  (* POP run of 4 *)
  apply (hsteps_trans _ (HB [] (0 + 4) 1 (5 + 2 * 4)
      ((5, 2) :: (1, 1) :: R2) G)).
  { replace (HB [] 0 1 5
        ((1, 2) :: (1, 2) :: (1, 2) :: (1, 2) ::
         (5, 2) :: (1, 1) :: R2) G)
      with (HB [] 0 1 5
              (repeat (1, 2) 4 ++ ((5, 2) :: (1, 1) :: R2)) G)
      by sec_eq.
    apply (pop_chain_h_app 4 [] 0 5 ((5, 2) :: (1, 1) :: R2) G);
      lia. }
  (* TUP *)
  apply (hsteps_trans _ (HC [] 4 12 2 ((3, 2) :: (1, 1) :: R2) G)).
  { apply (hsteps_step _ (HC [] 4 12 2 ((3, 2) :: (1, 1) :: R2) G)).
    { replace (HB [] (0 + 4) 1 (5 + 2 * 4) ((5, 2) :: (1, 1) :: R2) G)
        with (HB [] 4 1 (S (S 11))
                ((S (S (S 2)), 2) :: (1, 1) :: R2) G) by sec_eq.
      replace (HC [] 4 12 2 ((3, 2) :: (1, 1) :: R2) G)
        with (HC [] 4 (S 11) 2 ((S 2, 2) :: (1, 1) :: R2) G) by sec_eq.
      apply hTUP. }
    apply hsteps_refl. }
  (* DIPDESC_even 4 *)
  apply (hsteps_trans _ (HC [] 0 3 2
      (repeat (1, 2) 3 ++ ((2, 2) :: (3, 2) :: (1, 1) :: R2)) G)).
  { replace (HC [] 4 12 2 ((3, 2) :: (1, 1) :: R2) G)
      with (HC [] (S 3) (2 * S 3 + 4) 2 ((3, 2) :: (1, 1) :: R2) G)
      by sec_eq.
    apply (DIPDESC_even 3 [] ((3, 2) :: (1, 1) :: R2) G). }
  (* hPUSHX *)
  apply (hsteps_trans _ (HB [] 1 1 7
      (repeat (1, 2) 3 ++ ((2, 2) :: (3, 2) :: (1, 1) :: R2)) G)).
  { apply (hsteps_step _ (HB [] 1 1 7
        (repeat (1, 2) 3 ++ ((2, 2) :: (3, 2) :: (1, 1) :: R2)) G)).
    { apply hPUSHX. }
    apply hsteps_refl. }
  (* POP run of 3 *)
  apply (hsteps_trans _ (HB [] (1 + 3) 1 (7 + 2 * 3)
      ((2, 2) :: (3, 2) :: (1, 1) :: R2) G)).
  { apply (pop_chain_h_app 3 [] 1 7
             ((2, 2) :: (3, 2) :: (1, 1) :: R2) G); lia. }
  (* hTUP2_1 onto frame ([5], 13) *)
  apply (hsteps_step _ (HC [5] 13 1 2 ((1, 2) :: (1, 1) :: R2) G)).
  { replace (HB [] (1 + 3) 1 (7 + 2 * 3)
        ((2, 2) :: (3, 2) :: (1, 1) :: R2) G)
      with (HB [] 4 1 (S 12)
              ((2, S (S 0)) :: (S (S (S 0)), 2) :: (1, 1) :: R2) G)
      by sec_eq.
    replace (HC [5] 13 1 2 ((1, 2) :: (1, 1) :: R2) G)
      with (HC (S 4 :: []) (S 12) (S 0) 2
              ((S 0, 2) :: (1, 1) :: R2) G) by sec_eq.
    apply hTUP2_1. }
  apply hsteps_refl.
Qed.

(* ----------------------------------------------------------------- *)
(* Part 6: PHASE8_TO_STAGE_D -- the composed phase-8 frontier:       *)
(* from phase 7's landing at frame ([42; 19], 235), every entry      *)
(* with M >= 616 (even R = 2M + 46 >= 1278) reaches the frame        *)
(* ([5], 13) continuation source over the carried stack              *)
(*   (1, 2) :: (1, 1) :: R2,                                          *)
(*   R2 = (1, 2) :: (1, 2) :: (1, 2)^40 ++ ((149, 2) :: (1, 1) ::    *)
(*        (1, 2) :: (1, 2) :: (1, 2)^334 ++ ((2M - 1230, 2) :: Pe)).  *)
(* Beyond this point the continuation is the full-stack cascade      *)
(* fenced in the header: the ESC era law does NOT extend past        *)
(* R <= 1276 in the current vocabulary.                              *)
(* ----------------------------------------------------------------- *)

Lemma PHASE8_TO_STAGE_D : forall M beta, 616 <= M -> 2 <= beta ->
  hsteps (HB [42; 19] 235 1 335
            ((2 * M - 556, 2) :: (1, 1) :: repeat (1, 2) (beta - 1)) 1)
         (HC [5] 13 1 2
            ((1, 2) :: (1, 1) :: (1, 2) :: (1, 2) ::
             repeat (1, 2) 40 ++
             ((149, 2) :: (1, 1) :: (1, 2) :: (1, 2) ::
              repeat (1, 2) 334 ++
              ((2 * M - 1230, 2) :: (1, 1) ::
               repeat (1, 2) (beta - 1)))) 1).
Proof.
  intros M beta HM Hb.
  apply (hsteps_trans _ (HC [19] 41 233 2
      ((1, 1) :: (1, 2) :: (1, 2) ::
       repeat (1, 2) 334 ++
       ((2 * M - 1230, 2) :: (1, 1) :: repeat (1, 2) (beta - 1))) 1)).
  { apply (PHASE8_TO_MID M beta); lia. }
  apply (hsteps_trans _ (HB [0] 3 1 2
      ((15, 2) :: (1, 1) :: (1, 2) :: (1, 2) ::
       repeat (1, 2) 40 ++
       ((149, 2) :: (1, 1) :: (1, 2) :: (1, 2) ::
        repeat (1, 2) 334 ++
        ((2 * M - 1230, 2) :: (1, 1) :: repeat (1, 2) (beta - 1)))) 1)).
  { apply PHASE8_STAGE_A. }
  apply (hsteps_trans _ (HB [] 0 1 5
      ((1, 2) :: (1, 2) :: (1, 2) :: (1, 2) ::
       (5, 2) :: (1, 1) :: (1, 2) :: (1, 2) ::
       repeat (1, 2) 40 ++
       ((149, 2) :: (1, 1) :: (1, 2) :: (1, 2) ::
        repeat (1, 2) 334 ++
        ((2 * M - 1230, 2) :: (1, 1) :: repeat (1, 2) (beta - 1)))) 1)).
  { apply PHASE8_STAGE_B. }
  apply PHASE8_STAGE_C.
Qed.

Print Assumptions DIPDESC_even.
Print Assumptions PHASE8_TO_MID.
Print Assumptions PHASE8_STAGE_A.
Print Assumptions PHASE8_STAGE_B.
Print Assumptions PHASE8_STAGE_C.
Print Assumptions PHASE8_TO_STAGE_D.
