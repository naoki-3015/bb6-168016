(* ================================================================= *)
(*  Grind15.v -- Phase 47: the first re-descent cycle of the END    *)
(*  state, mechanised as a fixed parse, closing TAIL2_END for the   *)
(*  whole first k-band 3714 <= k <= 11142 and reducing the rest to  *)
(*  a strictly smaller core at the TOP state.                       *)
(*                                                                  *)
(*  Phase 46 left the ESC side of H_LOOP resting on TAIL2_END       *)
(*  (Grind14.v): the totality of the END state                      *)
(*                                                                  *)
(*    END(k, beta) = HB [317; 40; 14; 5] 2204 1 3711                *)
(*                    ((2k, 2) :: (1, 1) :: (1, 2)^(beta - 1))      *)
(*                                                                  *)
(*  for k >= 3714.  There the final clean grind of END46_big        *)
(*  (CLEANG_even at counter 3710) fails its floor 2k - 6 <= 2*3710  *)
(*  and the rounds take the DIPDESC boundary.  Phase 47 traces the  *)
(*  walk (rocq/hsim47.py, ALL PASS: the 37-waypoint chain below     *)
(*  asserted verbatim at (k, beta) in {(3714, 2), (3714, 3),        *)
(*  (3715, 2), (4000, 2), (5000, 3), (11142, 2), (11143, 2),        *)
(*  (12000, 2)}; band finals and the cycle-2 fence asserted too).   *)
(*                                                                  *)
(*  FINDING: the re-descent is NOT a return to the END state --     *)
(*  no END-shaped config recurs.  Instead the walk is a FIXED       *)
(*  parse, uniform in (k, beta), in which the residue pair          *)
(*  (rho, 2), rho = 2(k - 3713), rides untouched at the bottom      *)
(*  of the stack:                                                   *)
(*                                                                  *)
(*    END --TUP, hGRIND_even 1853, TUP2_1, TDN, TUP-->              *)
(*      HC [2204; 317; 40; 14; 5] 3710 3 2 ((2k - 6, 2) :: tail)    *)
(*    --DIPGRIND (3710, rho)-->                                     *)
(*      HC [2204; 317; 40; 14; 5] 0 3 2 ((1, 2)^3710 ++ W),         *)
(*        W = ((rho, 2) :: (1, 1) :: (1, 2)^(beta - 1))             *)
(*    --CASCADE47 (fixed parse, 34 segments)-->                     *)
(*      MID = HB [1279; 745; 151; 77; 35; 20; 0] 289 1 3            *)
(*              ((1, 2)^3712 ++ W)                                  *)
(*    --pop12 3712-->                                               *)
(*      TOP = HB [1279; 745; 151; 77; 35; 20; 0] 4001 1 7427 W.     *)
(*                                                                  *)
(*  CASCADE47's dip levels are DIPGRIND at (315, 1568), (12, 10),   *)
(*  (636, 290), (31, 258), (3, 5), (3, 2), (72, 108), (3, 36),      *)
(*  (3, 2), (13, 4) -- every frame and counter a literal; the       *)
(*  carried stack W is never inspected, so CASCADE47 is stated     *)
(*  for an ARBITRARY tail w.                                        *)
(*                                                                  *)
(*  TOP then closes by the size of rho:                             *)
(*    rho = 2:        TRANS2_1 + CASCADE_POPFIN, A = 7427 + beta;   *)
(*    rho = 4:        TUP + hGRIND_even 3711 + TRANS2_2             *)
(*                    + CASCADE_POPFIN, A = beta + 2;               *)
(*    rho = 6:        TUP + hGRIND_even 3711 + TUP2_1 + TDN         *)
(*                    + TRANS2_1 + CASCADE_POPFIN, A = beta + 4     *)
(*                    (after TUP2_1 the pair is (2, 2) itself, so   *)
(*                    TRANS2_1 fires at once -- no GRIND2 state);   *)
(*    8 <= rho <= 14858 (band 1): TUP + hGRIND_even 3711 + TUP2_1   *)
(*      + TDN + TUP onto HC [4001; 1279; ...] 7426 3 2              *)
(*      ((rho - 6, 2) :: tail), whose pair grinds CLEANLY by       *)
(*      CLEANG_even (floor (rho - 8)/2 + 1 <= 7426, exactly         *)
(*      rho <= 14858), then TRANS2_1 + CASCADE_POPFIN,              *)
(*      A = rho + beta - 2.                                         *)
(*                                                                  *)
(*  For rho >= 14860 (k >= 11143) the pair (rho - 6, 2) at counter  *)
(*  7426 exceeds the CLEANG_even floor and the rounds take the      *)
(*  DIPDESC boundary a SECOND time (hsim47 Part 3: the GRIND2       *)
(*  state and the DIPGRIND (7426, rho - 14858) landing both         *)
(*  occur at k = 11143, 12000, 20000).  The second descent is a     *)
(*  NEW cascade with different constants (frames [745; ...],       *)
(*  [225; 40; 14; 5], [1589; ...] -- not the first cascade          *)
(*  repeated), so no cycle induction in the current vocabulary      *)
(*  closes it; what remains is the strictly smaller core            *)
(*                                                                  *)
(*    TAIL2_END2: the totality of the ONE pair (2j, 2) at the ONE   *)
(*    fixed TOP state HB [1279; 745; 151; 77; 35; 20; 0] 4001 1     *)
(*    7427, for j >= 7430 (rho = 2j >= 14860), beta >= 2.           *)
(*                                                                  *)
(*  TAIL2_END is then proved modulo TAIL2_END2 (TAIL2_END_of47),    *)
(*  and ESC_ERA_LAW_47 carries it: the ESC instances at every       *)
(*  even R >= 1278 rest on TAIL2_END2 alone.  The k-range of the    *)
(*  core shrank from [3714, oo) to [11143, oo), and its statement   *)
(*  sits one full cycle below the END state.                        *)
(* ================================================================= *)

Require Import List Bool Arith Lia ZArith.
Import ListNotations.
Require Import TM Sections Mirror TokenPass Recoord Era Esc Dev
               Grind Grind2 Grind3 Grind4 Grind5 Grind6 Grind7 Grind8
               Grind9 Grind10 Grind11 Grind12 Grind13 Grind14.

Ltac sec_eq := repeat (first [ solve [reflexivity] | solve [lia]
                             | f_equal ]).

(* ----------------------------------------------------------------- *)
(* END47_FRONT: the END front (the first five steps of END46_big),  *)
(* landing on the DIPGRIND source at frame [2204; 317; 40; 14; 5].  *)
(* ----------------------------------------------------------------- *)

Lemma END47_FRONT : forall k beta, 4 <= k -> 2 <= beta ->
  hsteps (HB [317; 40; 14; 5] 2204 1 3711
            ((2 * k, 2) :: (1, 1) :: repeat (1, 2) (beta - 1)) 1)
         (HC [2204; 317; 40; 14; 5] 3710 3 2
            ((2 * k - 6, 2) :: (1, 1) :: repeat (1, 2) (beta - 1)) 1).
Proof.
  intros k beta Hk Hb.
  apply (hsteps_trans _ (HC [317; 40; 14; 5] 2204 3710 2
    ((2 * k - 2, 2) :: (1, 1) :: repeat (1, 2) (beta - 1)) 1)).
  { apply (sTUP [317; 40; 14; 5] 2204 3711 (2 * k) 2
           ((1, 1) :: repeat (1, 2) (beta - 1)) 1); lia. }
  apply (hsteps_trans _ (HB [317; 40; 14; 5] 2203 1 3710
    ((2, 2) :: (2 * k - 2, 2) :: (1, 1) :: repeat (1, 2) (beta - 1)) 1)).
  { apply (hGRIND_even 1853 [317; 40; 14; 5] 2203
           ((2 * k - 2, 2) :: (1, 1) :: repeat (1, 2) (beta - 1)) 1);
      lia. }
  apply (hsteps_trans _ (HC [2204; 317; 40; 14; 5] 3710 1 2
    ((2 * k - 4, 2) :: (1, 1) :: repeat (1, 2) (beta - 1)) 1)).
  { replace ((2 * k - 4, 2) :: (1, 1) :: repeat (1, 2) (beta - 1))
      with ((2 * k - 2 - 2, 2) :: (1, 1) :: repeat (1, 2) (beta - 1))
      by sec_eq.
    apply (sTUP2_1 [317; 40; 14; 5] 2203 3709 (2 * k - 2)
           ((1, 1) :: repeat (1, 2) (beta - 1)) 1); lia. }
  apply (hsteps_trans _ (HB [2204; 317; 40; 14; 5] 3710 1 4
    ((2 * k - 4, 2) :: (1, 1) :: repeat (1, 2) (beta - 1)) 1)).
  { apply (sTDN [2204; 317; 40; 14; 5] 3710
           ((2 * k - 4, 2) :: (1, 1) :: repeat (1, 2) (beta - 1)) 1). }
  replace ((2 * k - 6, 2) :: (1, 1) :: repeat (1, 2) (beta - 1))
    with ((2 * k - 4 - 2, 2) :: (1, 1) :: repeat (1, 2) (beta - 1))
    by sec_eq.
  apply (sTUP [2204; 317; 40; 14; 5] 3710 4 (2 * k - 4) 2
         ((1, 1) :: repeat (1, 2) (beta - 1)) 1); lia.
Qed.

(* ----------------------------------------------------------------- *)
(* CASCADE47: the fixed re-descent parse.  From the DIPGRIND        *)
(* landing at frame [2204; 317; 40; 14; 5] to MID, for an           *)
(* ARBITRARY carried tail w (the residue pair (rho, 2) and the      *)
(* era tail ride inside w, never inspected).  Waypoints are the     *)
(* hsim47 chain, asserted verbatim.                                 *)
(* ----------------------------------------------------------------- *)

Lemma CASCADE47 : forall w,
  hsteps (HC [2204; 317; 40; 14; 5] 0 3 2 (repeat (1, 2) 3710 ++ w) 1)
         (HB [1279; 745; 151; 77; 35; 20; 0] 289 1 3
            (repeat (1, 2) 3712 ++ w) 1).
Proof.
  intro w.
  (* S1: PX2A, PUSH, TDN, TUP onto frame [40; 14; 5], pair (2198, 2) *)
  apply (hsteps_trans _ (HC [40; 14; 5] 315 3 2
    ((2198, 2) :: (1, 1) :: repeat (1, 2) 3712 ++ w) 1)).
  { apply (hsteps_trans _ (HC [40; 14; 5] 316 2202 2
      ((1, 1) :: (1, 2) :: (1, 2) :: repeat (1, 2) 3710 ++ w) 1)).
    { apply (hsteps_step _ (HC [40; 14; 5] 316 2202 2
        ((1, 1) :: (1, 2) :: (1, 2) :: repeat (1, 2) 3710 ++ w) 1));
        [apply hPX2A | apply hsteps_refl]. }
    apply (hsteps_trans _ (HC [40; 14; 5] 315 1 2
      ((2200, 2) :: (1, 1) :: (1, 2) :: (1, 2)
       :: repeat (1, 2) 3710 ++ w) 1)).
    { apply (sPUSH [40; 14; 5] 315 2202
             ((1, 1) :: (1, 2) :: (1, 2) :: repeat (1, 2) 3710 ++ w)
             1); lia. }
    apply (hsteps_trans _ (HB [40; 14; 5] 315 1 4
      ((2200, 2) :: (1, 1) :: (1, 2) :: (1, 2)
       :: repeat (1, 2) 3710 ++ w) 1)).
    { apply (sTDN [40; 14; 5] 315
             ((2200, 2) :: (1, 1) :: (1, 2) :: (1, 2)
              :: repeat (1, 2) 3710 ++ w) 1). }
    replace ((2198, 2) :: (1, 1) :: repeat (1, 2) 3712 ++ w)
      with ((2200 - 2, 2) :: (1, 1) :: (1, 2) :: (1, 2)
            :: repeat (1, 2) 3710 ++ w) by sec_eq.
    apply (sTUP [40; 14; 5] 315 4 2200 2
           ((1, 1) :: (1, 2) :: (1, 2) :: repeat (1, 2) 3710 ++ w)
           1); lia. }
  (* S2: DIPGRIND (315, 1568) *)
  apply (hsteps_trans _ (HC [40; 14; 5] 0 3 2
    (repeat (1, 2) 315 ++ (1568, 2) :: (1, 1)
     :: repeat (1, 2) 3712 ++ w) 1)).
  { apply (DIPGRIND 315 1568 [40; 14; 5]
           ((1, 1) :: repeat (1, 2) 3712 ++ w) 1); lia. }
  (* S3: PX2A, PUSH, TDN, TUP onto frame [5], pair (34, 2) *)
  apply (hsteps_trans _ (HC [5] 12 3 2
    ((34, 2) :: (1, 1) :: repeat (1, 2) 317
     ++ (1568, 2) :: (1, 1) :: repeat (1, 2) 3712 ++ w) 1)).
  { apply (hsteps_trans _ (HC [5] 13 38 2
      ((1, 1) :: (1, 2) :: (1, 2) :: repeat (1, 2) 315
       ++ (1568, 2) :: (1, 1) :: repeat (1, 2) 3712 ++ w) 1)).
    { apply (hsteps_step _ (HC [5] 13 38 2
        ((1, 1) :: (1, 2) :: (1, 2) :: repeat (1, 2) 315
         ++ (1568, 2) :: (1, 1) :: repeat (1, 2) 3712 ++ w) 1));
        [apply hPX2A | apply hsteps_refl]. }
    apply (hsteps_trans _ (HC [5] 12 1 2
      ((36, 2) :: (1, 1) :: (1, 2) :: (1, 2) :: repeat (1, 2) 315
       ++ (1568, 2) :: (1, 1) :: repeat (1, 2) 3712 ++ w) 1)).
    { apply (sPUSH [5] 12 38
             ((1, 1) :: (1, 2) :: (1, 2) :: repeat (1, 2) 315
              ++ (1568, 2) :: (1, 1) :: repeat (1, 2) 3712 ++ w)
             1); lia. }
    apply (hsteps_trans _ (HB [5] 12 1 4
      ((36, 2) :: (1, 1) :: (1, 2) :: (1, 2) :: repeat (1, 2) 315
       ++ (1568, 2) :: (1, 1) :: repeat (1, 2) 3712 ++ w) 1)).
    { apply (sTDN [5] 12
             ((36, 2) :: (1, 1) :: (1, 2) :: (1, 2)
              :: repeat (1, 2) 315
              ++ (1568, 2) :: (1, 1) :: repeat (1, 2) 3712 ++ w)
             1). }
    replace ((34, 2) :: (1, 1) :: repeat (1, 2) 317
             ++ (1568, 2) :: (1, 1) :: repeat (1, 2) 3712 ++ w)
      with ((36 - 2, 2) :: (1, 1) :: (1, 2) :: (1, 2)
            :: repeat (1, 2) 315
            ++ (1568, 2) :: (1, 1) :: repeat (1, 2) 3712 ++ w)
      by sec_eq.
    apply (sTUP [5] 12 4 36 2
           ((1, 1) :: (1, 2) :: (1, 2) :: repeat (1, 2) 315
            ++ (1568, 2) :: (1, 1) :: repeat (1, 2) 3712 ++ w)
           1); lia. }
  (* S4: DIPGRIND (12, 10) *)
  apply (hsteps_trans _ (HC [5] 0 3 2
    (repeat (1, 2) 12 ++ (10, 2) :: (1, 1) :: repeat (1, 2) 317
     ++ (1568, 2) :: (1, 1) :: repeat (1, 2) 3712 ++ w) 1)).
  { apply (DIPGRIND 12 10 [5]
           ((1, 1) :: repeat (1, 2) 317
            ++ (1568, 2) :: (1, 1) :: repeat (1, 2) 3712 ++ w) 1);
      lia. }
  (* S5: PX2Bgen onto frame [0] *)
  apply (hsteps_trans _ (HB [0] 3 1 2
    ((1, 2) :: (1, 1) :: repeat (1, 2) 14 ++ (10, 2) :: (1, 1)
     :: repeat (1, 2) 317
     ++ (1568, 2) :: (1, 1) :: repeat (1, 2) 3712 ++ w) 1)).
  { apply (hsteps_step _ (HB [0] 3 1 2
      ((1, 2) :: (1, 1) :: repeat (1, 2) 14 ++ (10, 2) :: (1, 1)
       :: repeat (1, 2) 317
       ++ (1568, 2) :: (1, 1) :: repeat (1, 2) 3712 ++ w) 1)).
    - replace ((1, 2) :: (1, 1) :: repeat (1, 2) 14
               ++ (10, 2) :: (1, 1) :: repeat (1, 2) 317
               ++ (1568, 2) :: (1, 1) :: repeat (1, 2) 3712 ++ w)
        with ((0 + 1, 2) :: (1, 1) :: (1, 2) :: (1, 2)
              :: repeat (1, 2) 12 ++ (10, 2) :: (1, 1)
              :: repeat (1, 2) 317
              ++ (1568, 2) :: (1, 1) :: repeat (1, 2) 3712 ++ w)
        by sec_eq.
      apply hPX2Bgen.
    - apply hsteps_refl. }
  (* S6: pop12 1, POP, pop12 14, TUP, hGRIND_even 14, TUP2_1, TDN, *)
  (* TUP onto frame [19; 0], pair (4, 2)                            *)
  apply (hsteps_trans _ (HC [19; 0] 32 3 2
    ((4, 2) :: (1, 1) :: repeat (1, 2) 317
     ++ (1568, 2) :: (1, 1) :: repeat (1, 2) 3712 ++ w) 1)).
  { apply (hsteps_trans _ (HB [0] 4 1 4
      ((1, 1) :: repeat (1, 2) 14 ++ (10, 2) :: (1, 1)
       :: repeat (1, 2) 317
       ++ (1568, 2) :: (1, 1) :: repeat (1, 2) 3712 ++ w) 1)).
    { replace ((1, 2) :: (1, 1) :: repeat (1, 2) 14
               ++ (10, 2) :: (1, 1) :: repeat (1, 2) 317
               ++ (1568, 2) :: (1, 1) :: repeat (1, 2) 3712 ++ w)
        with (repeat (1, 2) 1
              ++ ((1, 1) :: repeat (1, 2) 14 ++ (10, 2) :: (1, 1)
                  :: repeat (1, 2) 317
                  ++ (1568, 2) :: (1, 1) :: repeat (1, 2) 3712 ++ w))
        by sec_eq.
      apply (pop12 1 [0] 3 2
             ((1, 1) :: repeat (1, 2) 14 ++ (10, 2) :: (1, 1)
              :: repeat (1, 2) 317
              ++ (1568, 2) :: (1, 1) :: repeat (1, 2) 3712 ++ w)
             1); lia. }
    apply (hsteps_trans _ (HB [0] 5 1 5
      (repeat (1, 2) 14 ++ (10, 2) :: (1, 1) :: repeat (1, 2) 317
       ++ (1568, 2) :: (1, 1) :: repeat (1, 2) 3712 ++ w) 1)).
    { apply (sPOP1 [0] 4 4
             (repeat (1, 2) 14 ++ (10, 2) :: (1, 1)
              :: repeat (1, 2) 317
              ++ (1568, 2) :: (1, 1) :: repeat (1, 2) 3712 ++ w)
             1); lia. }
    apply (hsteps_trans _ (HB [0] 19 1 33
      ((10, 2) :: (1, 1) :: repeat (1, 2) 317
       ++ (1568, 2) :: (1, 1) :: repeat (1, 2) 3712 ++ w) 1)).
    { apply (pop12 14 [0] 5 5
             ((10, 2) :: (1, 1) :: repeat (1, 2) 317
              ++ (1568, 2) :: (1, 1) :: repeat (1, 2) 3712 ++ w)
             1); lia. }
    apply (hsteps_trans _ (HC [0] 19 32 2
      ((8, 2) :: (1, 1) :: repeat (1, 2) 317
       ++ (1568, 2) :: (1, 1) :: repeat (1, 2) 3712 ++ w) 1)).
    { apply (sTUP [0] 19 33 10 2
             ((1, 1) :: repeat (1, 2) 317
              ++ (1568, 2) :: (1, 1) :: repeat (1, 2) 3712 ++ w)
             1); lia. }
    apply (hsteps_trans _ (HB [0] 18 1 32
      ((2, 2) :: (8, 2) :: (1, 1) :: repeat (1, 2) 317
       ++ (1568, 2) :: (1, 1) :: repeat (1, 2) 3712 ++ w) 1)).
    { apply (hGRIND_even 14 [0] 18
             ((8, 2) :: (1, 1) :: repeat (1, 2) 317
              ++ (1568, 2) :: (1, 1) :: repeat (1, 2) 3712 ++ w)
             1); lia. }
    apply (hsteps_trans _ (HC [19; 0] 32 1 2
      ((6, 2) :: (1, 1) :: repeat (1, 2) 317
       ++ (1568, 2) :: (1, 1) :: repeat (1, 2) 3712 ++ w) 1)).
    { apply (sTUP2_1 [0] 18 31 8
             ((1, 1) :: repeat (1, 2) 317
              ++ (1568, 2) :: (1, 1) :: repeat (1, 2) 3712 ++ w)
             1); lia. }
    apply (hsteps_trans _ (HB [19; 0] 32 1 4
      ((6, 2) :: (1, 1) :: repeat (1, 2) 317
       ++ (1568, 2) :: (1, 1) :: repeat (1, 2) 3712 ++ w) 1)).
    { apply (sTDN [19; 0] 32
             ((6, 2) :: (1, 1) :: repeat (1, 2) 317
              ++ (1568, 2) :: (1, 1) :: repeat (1, 2) 3712 ++ w)
             1). }
    apply (sTUP [19; 0] 32 4 6 2
           ((1, 1) :: repeat (1, 2) 317
            ++ (1568, 2) :: (1, 1) :: repeat (1, 2) 3712 ++ w)
           1); lia. }
  (* S7: CLEANG_even 1, TRANS2_1 onto frame [33; 19; 0] *)
  apply (hsteps_trans _ (HB [33; 19; 0] 9 1 3
    (repeat (1, 2) 317
     ++ (1568, 2) :: (1, 1) :: repeat (1, 2) 3712 ++ w) 1)).
  { apply (hsteps_trans _ (HB [19; 0] 32 1 8
      ((2, 2) :: (1, 1) :: repeat (1, 2) 317
       ++ (1568, 2) :: (1, 1) :: repeat (1, 2) 3712 ++ w) 1)).
    { apply (CLEANG_even 1 [19; 0] 32
             ((1, 1) :: repeat (1, 2) 317
              ++ (1568, 2) :: (1, 1) :: repeat (1, 2) 3712 ++ w)
             1); lia. }
    apply (sTRANS2_1 [19; 0] 32 7 1
           (repeat (1, 2) 317
            ++ (1568, 2) :: (1, 1) :: repeat (1, 2) 3712 ++ w)
           1); lia. }
  (* S8: pop12 317, TUP, hGRIND_even 316, TUP2_1, TDN, TUP onto *)
  (* frame [326; 33; 19; 0], pair (1562, 2)                     *)
  apply (hsteps_trans _ (HC [326; 33; 19; 0] 636 3 2
    ((1562, 2) :: (1, 1) :: repeat (1, 2) 3712 ++ w) 1)).
  { apply (hsteps_trans _ (HB [33; 19; 0] 326 1 637
      ((1568, 2) :: (1, 1) :: repeat (1, 2) 3712 ++ w) 1)).
    { apply (pop12 317 [33; 19; 0] 9 3
             ((1568, 2) :: (1, 1) :: repeat (1, 2) 3712 ++ w)
             1); lia. }
    apply (hsteps_trans _ (HC [33; 19; 0] 326 636 2
      ((1566, 2) :: (1, 1) :: repeat (1, 2) 3712 ++ w) 1)).
    { apply (sTUP [33; 19; 0] 326 637 1568 2
             ((1, 1) :: repeat (1, 2) 3712 ++ w) 1); lia. }
    apply (hsteps_trans _ (HB [33; 19; 0] 325 1 636
      ((2, 2) :: (1566, 2) :: (1, 1) :: repeat (1, 2) 3712 ++ w) 1)).
    { apply (hGRIND_even 316 [33; 19; 0] 325
             ((1566, 2) :: (1, 1) :: repeat (1, 2) 3712 ++ w)
             1); lia. }
    apply (hsteps_trans _ (HC [326; 33; 19; 0] 636 1 2
      ((1564, 2) :: (1, 1) :: repeat (1, 2) 3712 ++ w) 1)).
    { apply (sTUP2_1 [33; 19; 0] 325 635 1566
             ((1, 1) :: repeat (1, 2) 3712 ++ w) 1); lia. }
    apply (hsteps_trans _ (HB [326; 33; 19; 0] 636 1 4
      ((1564, 2) :: (1, 1) :: repeat (1, 2) 3712 ++ w) 1)).
    { apply (sTDN [326; 33; 19; 0] 636
             ((1564, 2) :: (1, 1) :: repeat (1, 2) 3712 ++ w)
             1). }
    apply (sTUP [326; 33; 19; 0] 636 4 1564 2
           ((1, 1) :: repeat (1, 2) 3712 ++ w) 1); lia. }
  (* S9: DIPGRIND (636, 290) *)
  apply (hsteps_trans _ (HC [326; 33; 19; 0] 0 3 2
    (repeat (1, 2) 636 ++ (290, 2) :: (1, 1)
     :: repeat (1, 2) 3712 ++ w) 1)).
  { apply (DIPGRIND 636 290 [326; 33; 19; 0]
           ((1, 1) :: repeat (1, 2) 3712 ++ w) 1); lia. }
  (* S10: PX2A, PUSH, TDN, TUP onto frame [19; 0], pair (320, 2) *)
  apply (hsteps_trans _ (HC [19; 0] 31 3 2
    ((320, 2) :: (1, 1) :: repeat (1, 2) 638
     ++ (290, 2) :: (1, 1) :: repeat (1, 2) 3712 ++ w) 1)).
  { apply (hsteps_trans _ (HC [19; 0] 32 324 2
      ((1, 1) :: (1, 2) :: (1, 2) :: repeat (1, 2) 636
       ++ (290, 2) :: (1, 1) :: repeat (1, 2) 3712 ++ w) 1)).
    { apply (hsteps_step _ (HC [19; 0] 32 324 2
        ((1, 1) :: (1, 2) :: (1, 2) :: repeat (1, 2) 636
         ++ (290, 2) :: (1, 1) :: repeat (1, 2) 3712 ++ w) 1));
        [apply hPX2A | apply hsteps_refl]. }
    apply (hsteps_trans _ (HC [19; 0] 31 1 2
      ((322, 2) :: (1, 1) :: (1, 2) :: (1, 2) :: repeat (1, 2) 636
       ++ (290, 2) :: (1, 1) :: repeat (1, 2) 3712 ++ w) 1)).
    { apply (sPUSH [19; 0] 31 324
             ((1, 1) :: (1, 2) :: (1, 2) :: repeat (1, 2) 636
              ++ (290, 2) :: (1, 1) :: repeat (1, 2) 3712 ++ w)
             1); lia. }
    apply (hsteps_trans _ (HB [19; 0] 31 1 4
      ((322, 2) :: (1, 1) :: (1, 2) :: (1, 2) :: repeat (1, 2) 636
       ++ (290, 2) :: (1, 1) :: repeat (1, 2) 3712 ++ w) 1)).
    { apply (sTDN [19; 0] 31
             ((322, 2) :: (1, 1) :: (1, 2) :: (1, 2)
              :: repeat (1, 2) 636
              ++ (290, 2) :: (1, 1) :: repeat (1, 2) 3712 ++ w)
             1). }
    replace ((320, 2) :: (1, 1) :: repeat (1, 2) 638
             ++ (290, 2) :: (1, 1) :: repeat (1, 2) 3712 ++ w)
      with ((322 - 2, 2) :: (1, 1) :: (1, 2) :: (1, 2)
            :: repeat (1, 2) 636
            ++ (290, 2) :: (1, 1) :: repeat (1, 2) 3712 ++ w)
      by sec_eq.
    apply (sTUP [19; 0] 31 4 322 2
           ((1, 1) :: (1, 2) :: (1, 2) :: repeat (1, 2) 636
            ++ (290, 2) :: (1, 1) :: repeat (1, 2) 3712 ++ w)
           1); lia. }
  (* S11: DIPGRIND (31, 258) *)
  apply (hsteps_trans _ (HC [19; 0] 0 3 2
    (repeat (1, 2) 31 ++ (258, 2) :: (1, 1) :: repeat (1, 2) 638
     ++ (290, 2) :: (1, 1) :: repeat (1, 2) 3712 ++ w) 1)).
  { apply (DIPGRIND 31 258 [19; 0]
           ((1, 1) :: repeat (1, 2) 638
            ++ (290, 2) :: (1, 1) :: repeat (1, 2) 3712 ++ w) 1);
      lia. }
  (* S12: PX2A0, TUP, TDN, TUP onto frame [0], pair (11, 2) *)
  apply (hsteps_trans _ (HC [0] 3 3 2
    ((11, 2) :: (1, 1) :: repeat (1, 2) 33
     ++ (258, 2) :: (1, 1) :: repeat (1, 2) 638
     ++ (290, 2) :: (1, 1) :: repeat (1, 2) 3712 ++ w) 1)).
  { apply (hsteps_trans _ (HB [0] 3 1 2
      ((15, 2) :: (1, 1) :: (1, 2) :: (1, 2) :: repeat (1, 2) 31
       ++ (258, 2) :: (1, 1) :: repeat (1, 2) 638
       ++ (290, 2) :: (1, 1) :: repeat (1, 2) 3712 ++ w) 1)).
    { apply (hsteps_step _ (HB [0] 3 1 2
        ((15, 2) :: (1, 1) :: (1, 2) :: (1, 2) :: repeat (1, 2) 31
         ++ (258, 2) :: (1, 1) :: repeat (1, 2) 638
         ++ (290, 2) :: (1, 1) :: repeat (1, 2) 3712 ++ w) 1));
        [apply hPX2A0 | apply hsteps_refl]. }
    apply (hsteps_trans _ (HC [0] 3 1 2
      ((13, 2) :: (1, 1) :: (1, 2) :: (1, 2) :: repeat (1, 2) 31
       ++ (258, 2) :: (1, 1) :: repeat (1, 2) 638
       ++ (290, 2) :: (1, 1) :: repeat (1, 2) 3712 ++ w) 1)).
    { apply (sTUP [0] 3 2 15 2
             ((1, 1) :: (1, 2) :: (1, 2) :: repeat (1, 2) 31
              ++ (258, 2) :: (1, 1) :: repeat (1, 2) 638
              ++ (290, 2) :: (1, 1) :: repeat (1, 2) 3712 ++ w)
             1); lia. }
    apply (hsteps_trans _ (HB [0] 3 1 4
      ((13, 2) :: (1, 1) :: (1, 2) :: (1, 2) :: repeat (1, 2) 31
       ++ (258, 2) :: (1, 1) :: repeat (1, 2) 638
       ++ (290, 2) :: (1, 1) :: repeat (1, 2) 3712 ++ w) 1)).
    { apply (sTDN [0] 3
             ((13, 2) :: (1, 1) :: (1, 2) :: (1, 2)
              :: repeat (1, 2) 31
              ++ (258, 2) :: (1, 1) :: repeat (1, 2) 638
              ++ (290, 2) :: (1, 1) :: repeat (1, 2) 3712 ++ w)
             1). }
    replace ((11, 2) :: (1, 1) :: repeat (1, 2) 33
             ++ (258, 2) :: (1, 1) :: repeat (1, 2) 638
             ++ (290, 2) :: (1, 1) :: repeat (1, 2) 3712 ++ w)
      with ((13 - 2, 2) :: (1, 1) :: (1, 2) :: (1, 2)
            :: repeat (1, 2) 31
            ++ (258, 2) :: (1, 1) :: repeat (1, 2) 638
            ++ (290, 2) :: (1, 1) :: repeat (1, 2) 3712 ++ w)
      by sec_eq.
    apply (sTUP [0] 3 4 13 2
           ((1, 1) :: (1, 2) :: (1, 2) :: repeat (1, 2) 31
            ++ (258, 2) :: (1, 1) :: repeat (1, 2) 638
            ++ (290, 2) :: (1, 1) :: repeat (1, 2) 3712 ++ w)
           1); lia. }
  (* S13: DIPGRIND (3, 5) *)
  apply (hsteps_trans _ (HC [0] 0 3 2
    (repeat (1, 2) 3 ++ (5, 2) :: (1, 1) :: repeat (1, 2) 33
     ++ (258, 2) :: (1, 1) :: repeat (1, 2) 638
     ++ (290, 2) :: (1, 1) :: repeat (1, 2) 3712 ++ w) 1)).
  { apply (DIPGRIND 3 5 [0]
           ((1, 1) :: repeat (1, 2) 33
            ++ (258, 2) :: (1, 1) :: repeat (1, 2) 638
            ++ (290, 2) :: (1, 1) :: repeat (1, 2) 3712 ++ w) 1);
      lia. }
  (* S14: PX2B0 onto the empty frame *)
  apply (hsteps_trans _ (HB [] 0 1 5
    (repeat (1, 2) 4 ++ (5, 2) :: (1, 1) :: repeat (1, 2) 33
     ++ (258, 2) :: (1, 1) :: repeat (1, 2) 638
     ++ (290, 2) :: (1, 1) :: repeat (1, 2) 3712 ++ w) 1)).
  { apply (hsteps_step _ (HB [] 0 1 5
      (repeat (1, 2) 4 ++ (5, 2) :: (1, 1) :: repeat (1, 2) 33
       ++ (258, 2) :: (1, 1) :: repeat (1, 2) 638
       ++ (290, 2) :: (1, 1) :: repeat (1, 2) 3712 ++ w) 1)).
    - replace (repeat (1, 2) 4 ++ (5, 2) :: (1, 1)
               :: repeat (1, 2) 33
               ++ (258, 2) :: (1, 1) :: repeat (1, 2) 638
               ++ (290, 2) :: (1, 1) :: repeat (1, 2) 3712 ++ w)
        with ((1, 2) :: repeat (1, 2) 3 ++ (5, 2) :: (1, 1)
              :: repeat (1, 2) 33
              ++ (258, 2) :: (1, 1) :: repeat (1, 2) 638
              ++ (290, 2) :: (1, 1) :: repeat (1, 2) 3712 ++ w)
        by sec_eq.
      apply hPX2B0.
    - apply hsteps_refl. }
  (* S15: pop12 4, TUP, PUSH, TDN, TUP: pair (8, 2) over (3, 2) *)
  apply (hsteps_trans _ (HC [] 3 3 2
    ((8, 2) :: (3, 2) :: (1, 1) :: repeat (1, 2) 33
     ++ (258, 2) :: (1, 1) :: repeat (1, 2) 638
     ++ (290, 2) :: (1, 1) :: repeat (1, 2) 3712 ++ w) 1)).
  { apply (hsteps_trans _ (HB [] 4 1 13
      ((5, 2) :: (1, 1) :: repeat (1, 2) 33
       ++ (258, 2) :: (1, 1) :: repeat (1, 2) 638
       ++ (290, 2) :: (1, 1) :: repeat (1, 2) 3712 ++ w) 1)).
    { apply (pop12 4 [] 0 5
             ((5, 2) :: (1, 1) :: repeat (1, 2) 33
              ++ (258, 2) :: (1, 1) :: repeat (1, 2) 638
              ++ (290, 2) :: (1, 1) :: repeat (1, 2) 3712 ++ w)
             1); lia. }
    apply (hsteps_trans _ (HC [] 4 12 2
      ((3, 2) :: (1, 1) :: repeat (1, 2) 33
       ++ (258, 2) :: (1, 1) :: repeat (1, 2) 638
       ++ (290, 2) :: (1, 1) :: repeat (1, 2) 3712 ++ w) 1)).
    { apply (sTUP [] 4 13 5 2
             ((1, 1) :: repeat (1, 2) 33
              ++ (258, 2) :: (1, 1) :: repeat (1, 2) 638
              ++ (290, 2) :: (1, 1) :: repeat (1, 2) 3712 ++ w)
             1); lia. }
    apply (hsteps_trans _ (HC [] 3 1 2
      ((10, 2) :: (3, 2) :: (1, 1) :: repeat (1, 2) 33
       ++ (258, 2) :: (1, 1) :: repeat (1, 2) 638
       ++ (290, 2) :: (1, 1) :: repeat (1, 2) 3712 ++ w) 1)).
    { apply (sPUSH [] 3 12
             ((3, 2) :: (1, 1) :: repeat (1, 2) 33
              ++ (258, 2) :: (1, 1) :: repeat (1, 2) 638
              ++ (290, 2) :: (1, 1) :: repeat (1, 2) 3712 ++ w)
             1); lia. }
    apply (hsteps_trans _ (HB [] 3 1 4
      ((10, 2) :: (3, 2) :: (1, 1) :: repeat (1, 2) 33
       ++ (258, 2) :: (1, 1) :: repeat (1, 2) 638
       ++ (290, 2) :: (1, 1) :: repeat (1, 2) 3712 ++ w) 1)).
    { apply (sTDN [] 3
             ((10, 2) :: (3, 2) :: (1, 1) :: repeat (1, 2) 33
              ++ (258, 2) :: (1, 1) :: repeat (1, 2) 638
              ++ (290, 2) :: (1, 1) :: repeat (1, 2) 3712 ++ w)
             1). }
    apply (sTUP [] 3 4 10 2
           ((3, 2) :: (1, 1) :: repeat (1, 2) 33
            ++ (258, 2) :: (1, 1) :: repeat (1, 2) 638
            ++ (290, 2) :: (1, 1) :: repeat (1, 2) 3712 ++ w)
           1); lia. }
  (* S16: DIPGRIND (3, 2) *)
  apply (hsteps_trans _ (HC [] 0 3 2
    (repeat (1, 2) 3 ++ (2, 2) :: (3, 2) :: (1, 1)
     :: repeat (1, 2) 33
     ++ (258, 2) :: (1, 1) :: repeat (1, 2) 638
     ++ (290, 2) :: (1, 1) :: repeat (1, 2) 3712 ++ w) 1)).
  { apply (DIPGRIND 3 2 []
           ((3, 2) :: (1, 1) :: repeat (1, 2) 33
            ++ (258, 2) :: (1, 1) :: repeat (1, 2) 638
            ++ (290, 2) :: (1, 1) :: repeat (1, 2) 3712 ++ w) 1);
      lia. }
  (* S17: PUSHX *)
  apply (hsteps_trans _ (HB [] 1 1 7
    (repeat (1, 2) 3 ++ (2, 2) :: (3, 2) :: (1, 1)
     :: repeat (1, 2) 33
     ++ (258, 2) :: (1, 1) :: repeat (1, 2) 638
     ++ (290, 2) :: (1, 1) :: repeat (1, 2) 3712 ++ w) 1)).
  { apply (hsteps_step _ (HB [] 1 1 7
      (repeat (1, 2) 3 ++ (2, 2) :: (3, 2) :: (1, 1)
       :: repeat (1, 2) 33
       ++ (258, 2) :: (1, 1) :: repeat (1, 2) 638
       ++ (290, 2) :: (1, 1) :: repeat (1, 2) 3712 ++ w) 1));
      [apply hPUSHX | apply hsteps_refl]. }
  (* S18: pop12 3, TUP2_1, TDN onto frame [5] *)
  apply (hsteps_trans _ (HB [5] 13 1 4
    ((1, 2) :: (1, 1) :: repeat (1, 2) 33
     ++ (258, 2) :: (1, 1) :: repeat (1, 2) 638
     ++ (290, 2) :: (1, 1) :: repeat (1, 2) 3712 ++ w) 1)).
  { apply (hsteps_trans _ (HB [] 4 1 13
      ((2, 2) :: (3, 2) :: (1, 1) :: repeat (1, 2) 33
       ++ (258, 2) :: (1, 1) :: repeat (1, 2) 638
       ++ (290, 2) :: (1, 1) :: repeat (1, 2) 3712 ++ w) 1)).
    { apply (pop12 3 [] 1 7
             ((2, 2) :: (3, 2) :: (1, 1) :: repeat (1, 2) 33
              ++ (258, 2) :: (1, 1) :: repeat (1, 2) 638
              ++ (290, 2) :: (1, 1) :: repeat (1, 2) 3712 ++ w)
             1); lia. }
    apply (hsteps_trans _ (HC [5] 13 1 2
      ((1, 2) :: (1, 1) :: repeat (1, 2) 33
       ++ (258, 2) :: (1, 1) :: repeat (1, 2) 638
       ++ (290, 2) :: (1, 1) :: repeat (1, 2) 3712 ++ w) 1)).
    { replace ((1, 2) :: (1, 1) :: repeat (1, 2) 33
               ++ (258, 2) :: (1, 1) :: repeat (1, 2) 638
               ++ (290, 2) :: (1, 1) :: repeat (1, 2) 3712 ++ w)
        with ((3 - 2, 2) :: (1, 1) :: repeat (1, 2) 33
              ++ (258, 2) :: (1, 1) :: repeat (1, 2) 638
              ++ (290, 2) :: (1, 1) :: repeat (1, 2) 3712 ++ w)
        by sec_eq.
      apply (sTUP2_1 [] 4 12 3
             ((1, 1) :: repeat (1, 2) 33
              ++ (258, 2) :: (1, 1) :: repeat (1, 2) 638
              ++ (290, 2) :: (1, 1) :: repeat (1, 2) 3712 ++ w)
             1); lia. }
    apply (sTDN [5] 13
           ((1, 2) :: (1, 1) :: repeat (1, 2) 33
            ++ (258, 2) :: (1, 1) :: repeat (1, 2) 638
            ++ (290, 2) :: (1, 1) :: repeat (1, 2) 3712 ++ w)
           1). }
  (* S19: pop12 1, POP, pop12 33, TUP, hGRIND_even 34, TUP2_1, *)
  (* TDN, TUP onto frame [48; 5], pair (252, 2)                 *)
  apply (hsteps_trans _ (HC [48; 5] 72 3 2
    ((252, 2) :: (1, 1) :: repeat (1, 2) 638
     ++ (290, 2) :: (1, 1) :: repeat (1, 2) 3712 ++ w) 1)).
  { apply (hsteps_trans _ (HB [5] 14 1 6
      ((1, 1) :: repeat (1, 2) 33
       ++ (258, 2) :: (1, 1) :: repeat (1, 2) 638
       ++ (290, 2) :: (1, 1) :: repeat (1, 2) 3712 ++ w) 1)).
    { replace ((1, 2) :: (1, 1) :: repeat (1, 2) 33
               ++ (258, 2) :: (1, 1) :: repeat (1, 2) 638
               ++ (290, 2) :: (1, 1) :: repeat (1, 2) 3712 ++ w)
        with (repeat (1, 2) 1
              ++ ((1, 1) :: repeat (1, 2) 33
                  ++ (258, 2) :: (1, 1) :: repeat (1, 2) 638
                  ++ (290, 2) :: (1, 1) :: repeat (1, 2) 3712 ++ w))
        by sec_eq.
      apply (pop12 1 [5] 13 4
             ((1, 1) :: repeat (1, 2) 33
              ++ (258, 2) :: (1, 1) :: repeat (1, 2) 638
              ++ (290, 2) :: (1, 1) :: repeat (1, 2) 3712 ++ w)
             1); lia. }
    apply (hsteps_trans _ (HB [5] 15 1 7
      (repeat (1, 2) 33
       ++ (258, 2) :: (1, 1) :: repeat (1, 2) 638
       ++ (290, 2) :: (1, 1) :: repeat (1, 2) 3712 ++ w) 1)).
    { apply (sPOP1 [5] 14 6
             (repeat (1, 2) 33
              ++ (258, 2) :: (1, 1) :: repeat (1, 2) 638
              ++ (290, 2) :: (1, 1) :: repeat (1, 2) 3712 ++ w)
             1); lia. }
    apply (hsteps_trans _ (HB [5] 48 1 73
      ((258, 2) :: (1, 1) :: repeat (1, 2) 638
       ++ (290, 2) :: (1, 1) :: repeat (1, 2) 3712 ++ w) 1)).
    { apply (pop12 33 [5] 15 7
             ((258, 2) :: (1, 1) :: repeat (1, 2) 638
              ++ (290, 2) :: (1, 1) :: repeat (1, 2) 3712 ++ w)
             1); lia. }
    apply (hsteps_trans _ (HC [5] 48 72 2
      ((256, 2) :: (1, 1) :: repeat (1, 2) 638
       ++ (290, 2) :: (1, 1) :: repeat (1, 2) 3712 ++ w) 1)).
    { apply (sTUP [5] 48 73 258 2
             ((1, 1) :: repeat (1, 2) 638
              ++ (290, 2) :: (1, 1) :: repeat (1, 2) 3712 ++ w)
             1); lia. }
    apply (hsteps_trans _ (HB [5] 47 1 72
      ((2, 2) :: (256, 2) :: (1, 1) :: repeat (1, 2) 638
       ++ (290, 2) :: (1, 1) :: repeat (1, 2) 3712 ++ w) 1)).
    { apply (hGRIND_even 34 [5] 47
             ((256, 2) :: (1, 1) :: repeat (1, 2) 638
              ++ (290, 2) :: (1, 1) :: repeat (1, 2) 3712 ++ w)
             1); lia. }
    apply (hsteps_trans _ (HC [48; 5] 72 1 2
      ((254, 2) :: (1, 1) :: repeat (1, 2) 638
       ++ (290, 2) :: (1, 1) :: repeat (1, 2) 3712 ++ w) 1)).
    { apply (sTUP2_1 [5] 47 71 256
             ((1, 1) :: repeat (1, 2) 638
              ++ (290, 2) :: (1, 1) :: repeat (1, 2) 3712 ++ w)
             1); lia. }
    apply (hsteps_trans _ (HB [48; 5] 72 1 4
      ((254, 2) :: (1, 1) :: repeat (1, 2) 638
       ++ (290, 2) :: (1, 1) :: repeat (1, 2) 3712 ++ w) 1)).
    { apply (sTDN [48; 5] 72
             ((254, 2) :: (1, 1) :: repeat (1, 2) 638
              ++ (290, 2) :: (1, 1) :: repeat (1, 2) 3712 ++ w)
             1). }
    apply (sTUP [48; 5] 72 4 254 2
           ((1, 1) :: repeat (1, 2) 638
            ++ (290, 2) :: (1, 1) :: repeat (1, 2) 3712 ++ w)
           1); lia. }
  (* S20: DIPGRIND (72, 108) *)
  apply (hsteps_trans _ (HC [48; 5] 0 3 2
    (repeat (1, 2) 72 ++ (108, 2) :: (1, 1) :: repeat (1, 2) 638
     ++ (290, 2) :: (1, 1) :: repeat (1, 2) 3712 ++ w) 1)).
  { apply (DIPGRIND 72 108 [48; 5]
           ((1, 1) :: repeat (1, 2) 638
            ++ (290, 2) :: (1, 1) :: repeat (1, 2) 3712 ++ w) 1);
      lia. }
  (* S21: PX2A, PUSH, TDN, TUP onto frame [], pair (42, 2) *)
  apply (hsteps_trans _ (HC [] 3 3 2
    ((42, 2) :: (1, 1) :: repeat (1, 2) 74
     ++ (108, 2) :: (1, 1) :: repeat (1, 2) 638
     ++ (290, 2) :: (1, 1) :: repeat (1, 2) 3712 ++ w) 1)).
  { apply (hsteps_trans _ (HC [] 4 46 2
      ((1, 1) :: (1, 2) :: (1, 2) :: repeat (1, 2) 72
       ++ (108, 2) :: (1, 1) :: repeat (1, 2) 638
       ++ (290, 2) :: (1, 1) :: repeat (1, 2) 3712 ++ w) 1)).
    { apply (hsteps_step _ (HC [] 4 46 2
        ((1, 1) :: (1, 2) :: (1, 2) :: repeat (1, 2) 72
         ++ (108, 2) :: (1, 1) :: repeat (1, 2) 638
         ++ (290, 2) :: (1, 1) :: repeat (1, 2) 3712 ++ w) 1));
        [apply hPX2A | apply hsteps_refl]. }
    apply (hsteps_trans _ (HC [] 3 1 2
      ((44, 2) :: (1, 1) :: (1, 2) :: (1, 2) :: repeat (1, 2) 72
       ++ (108, 2) :: (1, 1) :: repeat (1, 2) 638
       ++ (290, 2) :: (1, 1) :: repeat (1, 2) 3712 ++ w) 1)).
    { apply (sPUSH [] 3 46
             ((1, 1) :: (1, 2) :: (1, 2) :: repeat (1, 2) 72
              ++ (108, 2) :: (1, 1) :: repeat (1, 2) 638
              ++ (290, 2) :: (1, 1) :: repeat (1, 2) 3712 ++ w)
             1); lia. }
    apply (hsteps_trans _ (HB [] 3 1 4
      ((44, 2) :: (1, 1) :: (1, 2) :: (1, 2) :: repeat (1, 2) 72
       ++ (108, 2) :: (1, 1) :: repeat (1, 2) 638
       ++ (290, 2) :: (1, 1) :: repeat (1, 2) 3712 ++ w) 1)).
    { apply (sTDN [] 3
             ((44, 2) :: (1, 1) :: (1, 2) :: (1, 2)
              :: repeat (1, 2) 72
              ++ (108, 2) :: (1, 1) :: repeat (1, 2) 638
              ++ (290, 2) :: (1, 1) :: repeat (1, 2) 3712 ++ w)
             1). }
    replace ((42, 2) :: (1, 1) :: repeat (1, 2) 74
             ++ (108, 2) :: (1, 1) :: repeat (1, 2) 638
             ++ (290, 2) :: (1, 1) :: repeat (1, 2) 3712 ++ w)
      with ((44 - 2, 2) :: (1, 1) :: (1, 2) :: (1, 2)
            :: repeat (1, 2) 72
            ++ (108, 2) :: (1, 1) :: repeat (1, 2) 638
            ++ (290, 2) :: (1, 1) :: repeat (1, 2) 3712 ++ w)
      by sec_eq.
    apply (sTUP [] 3 4 44 2
           ((1, 1) :: (1, 2) :: (1, 2) :: repeat (1, 2) 72
            ++ (108, 2) :: (1, 1) :: repeat (1, 2) 638
            ++ (290, 2) :: (1, 1) :: repeat (1, 2) 3712 ++ w)
           1); lia. }
  (* S22: DIPGRIND (3, 36) *)
  apply (hsteps_trans _ (HC [] 0 3 2
    (repeat (1, 2) 3 ++ (36, 2) :: (1, 1) :: repeat (1, 2) 74
     ++ (108, 2) :: (1, 1) :: repeat (1, 2) 638
     ++ (290, 2) :: (1, 1) :: repeat (1, 2) 3712 ++ w) 1)).
  { apply (DIPGRIND 3 36 []
           ((1, 1) :: repeat (1, 2) 74
            ++ (108, 2) :: (1, 1) :: repeat (1, 2) 638
            ++ (290, 2) :: (1, 1) :: repeat (1, 2) 3712 ++ w) 1);
      lia. }
  (* S23: PUSHX *)
  apply (hsteps_trans _ (HB [] 1 1 7
    (repeat (1, 2) 3 ++ (36, 2) :: (1, 1) :: repeat (1, 2) 74
     ++ (108, 2) :: (1, 1) :: repeat (1, 2) 638
     ++ (290, 2) :: (1, 1) :: repeat (1, 2) 3712 ++ w) 1)).
  { apply (hsteps_step _ (HB [] 1 1 7
      (repeat (1, 2) 3 ++ (36, 2) :: (1, 1) :: repeat (1, 2) 74
       ++ (108, 2) :: (1, 1) :: repeat (1, 2) 638
       ++ (290, 2) :: (1, 1) :: repeat (1, 2) 3712 ++ w) 1));
      [apply hPUSHX | apply hsteps_refl]. }
  (* S24: pop12 3, TUP, PUSH, TDN, TUP: pair (8, 2) over (34, 2) *)
  apply (hsteps_trans _ (HC [] 3 3 2
    ((8, 2) :: (34, 2) :: (1, 1) :: repeat (1, 2) 74
     ++ (108, 2) :: (1, 1) :: repeat (1, 2) 638
     ++ (290, 2) :: (1, 1) :: repeat (1, 2) 3712 ++ w) 1)).
  { apply (hsteps_trans _ (HB [] 4 1 13
      ((36, 2) :: (1, 1) :: repeat (1, 2) 74
       ++ (108, 2) :: (1, 1) :: repeat (1, 2) 638
       ++ (290, 2) :: (1, 1) :: repeat (1, 2) 3712 ++ w) 1)).
    { apply (pop12 3 [] 1 7
             ((36, 2) :: (1, 1) :: repeat (1, 2) 74
              ++ (108, 2) :: (1, 1) :: repeat (1, 2) 638
              ++ (290, 2) :: (1, 1) :: repeat (1, 2) 3712 ++ w)
             1); lia. }
    apply (hsteps_trans _ (HC [] 4 12 2
      ((34, 2) :: (1, 1) :: repeat (1, 2) 74
       ++ (108, 2) :: (1, 1) :: repeat (1, 2) 638
       ++ (290, 2) :: (1, 1) :: repeat (1, 2) 3712 ++ w) 1)).
    { apply (sTUP [] 4 13 36 2
             ((1, 1) :: repeat (1, 2) 74
              ++ (108, 2) :: (1, 1) :: repeat (1, 2) 638
              ++ (290, 2) :: (1, 1) :: repeat (1, 2) 3712 ++ w)
             1); lia. }
    apply (hsteps_trans _ (HC [] 3 1 2
      ((10, 2) :: (34, 2) :: (1, 1) :: repeat (1, 2) 74
       ++ (108, 2) :: (1, 1) :: repeat (1, 2) 638
       ++ (290, 2) :: (1, 1) :: repeat (1, 2) 3712 ++ w) 1)).
    { apply (sPUSH [] 3 12
             ((34, 2) :: (1, 1) :: repeat (1, 2) 74
              ++ (108, 2) :: (1, 1) :: repeat (1, 2) 638
              ++ (290, 2) :: (1, 1) :: repeat (1, 2) 3712 ++ w)
             1); lia. }
    apply (hsteps_trans _ (HB [] 3 1 4
      ((10, 2) :: (34, 2) :: (1, 1) :: repeat (1, 2) 74
       ++ (108, 2) :: (1, 1) :: repeat (1, 2) 638
       ++ (290, 2) :: (1, 1) :: repeat (1, 2) 3712 ++ w) 1)).
    { apply (sTDN [] 3
             ((10, 2) :: (34, 2) :: (1, 1) :: repeat (1, 2) 74
              ++ (108, 2) :: (1, 1) :: repeat (1, 2) 638
              ++ (290, 2) :: (1, 1) :: repeat (1, 2) 3712 ++ w)
             1). }
    apply (sTUP [] 3 4 10 2
           ((34, 2) :: (1, 1) :: repeat (1, 2) 74
            ++ (108, 2) :: (1, 1) :: repeat (1, 2) 638
            ++ (290, 2) :: (1, 1) :: repeat (1, 2) 3712 ++ w)
           1); lia. }
  (* S25: DIPGRIND (3, 2) *)
  apply (hsteps_trans _ (HC [] 0 3 2
    (repeat (1, 2) 3 ++ (2, 2) :: (34, 2) :: (1, 1)
     :: repeat (1, 2) 74
     ++ (108, 2) :: (1, 1) :: repeat (1, 2) 638
     ++ (290, 2) :: (1, 1) :: repeat (1, 2) 3712 ++ w) 1)).
  { apply (DIPGRIND 3 2 []
           ((34, 2) :: (1, 1) :: repeat (1, 2) 74
            ++ (108, 2) :: (1, 1) :: repeat (1, 2) 638
            ++ (290, 2) :: (1, 1) :: repeat (1, 2) 3712 ++ w) 1);
      lia. }
  (* S26: PUSHX *)
  apply (hsteps_trans _ (HB [] 1 1 7
    (repeat (1, 2) 3 ++ (2, 2) :: (34, 2) :: (1, 1)
     :: repeat (1, 2) 74
     ++ (108, 2) :: (1, 1) :: repeat (1, 2) 638
     ++ (290, 2) :: (1, 1) :: repeat (1, 2) 3712 ++ w) 1)).
  { apply (hsteps_step _ (HB [] 1 1 7
      (repeat (1, 2) 3 ++ (2, 2) :: (34, 2) :: (1, 1)
       :: repeat (1, 2) 74
       ++ (108, 2) :: (1, 1) :: repeat (1, 2) 638
       ++ (290, 2) :: (1, 1) :: repeat (1, 2) 3712 ++ w) 1));
      [apply hPUSHX | apply hsteps_refl]. }
  (* S27: pop12 3, TUP2_1, TDN, TUP onto frame [5], pair (30, 2) *)
  apply (hsteps_trans _ (HC [5] 13 3 2
    ((30, 2) :: (1, 1) :: repeat (1, 2) 74
     ++ (108, 2) :: (1, 1) :: repeat (1, 2) 638
     ++ (290, 2) :: (1, 1) :: repeat (1, 2) 3712 ++ w) 1)).
  { apply (hsteps_trans _ (HB [] 4 1 13
      ((2, 2) :: (34, 2) :: (1, 1) :: repeat (1, 2) 74
       ++ (108, 2) :: (1, 1) :: repeat (1, 2) 638
       ++ (290, 2) :: (1, 1) :: repeat (1, 2) 3712 ++ w) 1)).
    { apply (pop12 3 [] 1 7
             ((2, 2) :: (34, 2) :: (1, 1) :: repeat (1, 2) 74
              ++ (108, 2) :: (1, 1) :: repeat (1, 2) 638
              ++ (290, 2) :: (1, 1) :: repeat (1, 2) 3712 ++ w)
             1); lia. }
    apply (hsteps_trans _ (HC [5] 13 1 2
      ((32, 2) :: (1, 1) :: repeat (1, 2) 74
       ++ (108, 2) :: (1, 1) :: repeat (1, 2) 638
       ++ (290, 2) :: (1, 1) :: repeat (1, 2) 3712 ++ w) 1)).
    { apply (sTUP2_1 [] 4 12 34
             ((1, 1) :: repeat (1, 2) 74
              ++ (108, 2) :: (1, 1) :: repeat (1, 2) 638
              ++ (290, 2) :: (1, 1) :: repeat (1, 2) 3712 ++ w)
             1); lia. }
    apply (hsteps_trans _ (HB [5] 13 1 4
      ((32, 2) :: (1, 1) :: repeat (1, 2) 74
       ++ (108, 2) :: (1, 1) :: repeat (1, 2) 638
       ++ (290, 2) :: (1, 1) :: repeat (1, 2) 3712 ++ w) 1)).
    { apply (sTDN [5] 13
             ((32, 2) :: (1, 1) :: repeat (1, 2) 74
              ++ (108, 2) :: (1, 1) :: repeat (1, 2) 638
              ++ (290, 2) :: (1, 1) :: repeat (1, 2) 3712 ++ w)
             1). }
    apply (sTUP [5] 13 4 32 2
           ((1, 1) :: repeat (1, 2) 74
            ++ (108, 2) :: (1, 1) :: repeat (1, 2) 638
            ++ (290, 2) :: (1, 1) :: repeat (1, 2) 3712 ++ w)
           1); lia. }
  (* S28: DIPGRIND (13, 4) *)
  apply (hsteps_trans _ (HC [5] 0 3 2
    (repeat (1, 2) 13 ++ (4, 2) :: (1, 1) :: repeat (1, 2) 74
     ++ (108, 2) :: (1, 1) :: repeat (1, 2) 638
     ++ (290, 2) :: (1, 1) :: repeat (1, 2) 3712 ++ w) 1)).
  { apply (DIPGRIND 13 4 [5]
           ((1, 1) :: repeat (1, 2) 74
            ++ (108, 2) :: (1, 1) :: repeat (1, 2) 638
            ++ (290, 2) :: (1, 1) :: repeat (1, 2) 3712 ++ w) 1);
      lia. }
  (* S29: PX2Bgen onto frame [0] *)
  apply (hsteps_trans _ (HB [0] 3 1 2
    ((1, 2) :: (1, 1) :: repeat (1, 2) 15 ++ (4, 2) :: (1, 1)
     :: repeat (1, 2) 74
     ++ (108, 2) :: (1, 1) :: repeat (1, 2) 638
     ++ (290, 2) :: (1, 1) :: repeat (1, 2) 3712 ++ w) 1)).
  { apply (hsteps_step _ (HB [0] 3 1 2
      ((1, 2) :: (1, 1) :: repeat (1, 2) 15 ++ (4, 2) :: (1, 1)
       :: repeat (1, 2) 74
       ++ (108, 2) :: (1, 1) :: repeat (1, 2) 638
       ++ (290, 2) :: (1, 1) :: repeat (1, 2) 3712 ++ w) 1)).
    - replace ((1, 2) :: (1, 1) :: repeat (1, 2) 15
               ++ (4, 2) :: (1, 1) :: repeat (1, 2) 74
               ++ (108, 2) :: (1, 1) :: repeat (1, 2) 638
               ++ (290, 2) :: (1, 1) :: repeat (1, 2) 3712 ++ w)
        with ((0 + 1, 2) :: (1, 1) :: (1, 2) :: (1, 2)
              :: repeat (1, 2) 13 ++ (4, 2) :: (1, 1)
              :: repeat (1, 2) 74
              ++ (108, 2) :: (1, 1) :: repeat (1, 2) 638
              ++ (290, 2) :: (1, 1) :: repeat (1, 2) 3712 ++ w)
        by sec_eq.
      apply hPX2Bgen.
    - apply hsteps_refl. }
  (* S30: pop12 1, POP, pop12 15, TUP, hGRIND_even 15, TRANS2_2 *)
  (* onto frame [35; 20; 0]                                    *)
  apply (hsteps_trans _ (HB [35; 20; 0] 3 1 3
    (repeat (1, 2) 74
     ++ (108, 2) :: (1, 1) :: repeat (1, 2) 638
     ++ (290, 2) :: (1, 1) :: repeat (1, 2) 3712 ++ w) 1)).
  { apply (hsteps_trans _ (HB [0] 4 1 4
      ((1, 1) :: repeat (1, 2) 15 ++ (4, 2) :: (1, 1)
       :: repeat (1, 2) 74
       ++ (108, 2) :: (1, 1) :: repeat (1, 2) 638
       ++ (290, 2) :: (1, 1) :: repeat (1, 2) 3712 ++ w) 1)).
    { replace ((1, 2) :: (1, 1) :: repeat (1, 2) 15
               ++ (4, 2) :: (1, 1) :: repeat (1, 2) 74
               ++ (108, 2) :: (1, 1) :: repeat (1, 2) 638
               ++ (290, 2) :: (1, 1) :: repeat (1, 2) 3712 ++ w)
        with (repeat (1, 2) 1
              ++ ((1, 1) :: repeat (1, 2) 15 ++ (4, 2) :: (1, 1)
                  :: repeat (1, 2) 74
                  ++ (108, 2) :: (1, 1) :: repeat (1, 2) 638
                  ++ (290, 2) :: (1, 1) :: repeat (1, 2) 3712 ++ w))
        by sec_eq.
      apply (pop12 1 [0] 3 2
             ((1, 1) :: repeat (1, 2) 15 ++ (4, 2) :: (1, 1)
              :: repeat (1, 2) 74
              ++ (108, 2) :: (1, 1) :: repeat (1, 2) 638
              ++ (290, 2) :: (1, 1) :: repeat (1, 2) 3712 ++ w)
             1); lia. }
    apply (hsteps_trans _ (HB [0] 5 1 5
      (repeat (1, 2) 15 ++ (4, 2) :: (1, 1) :: repeat (1, 2) 74
       ++ (108, 2) :: (1, 1) :: repeat (1, 2) 638
       ++ (290, 2) :: (1, 1) :: repeat (1, 2) 3712 ++ w) 1)).
    { apply (sPOP1 [0] 4 4
             (repeat (1, 2) 15 ++ (4, 2) :: (1, 1)
              :: repeat (1, 2) 74
              ++ (108, 2) :: (1, 1) :: repeat (1, 2) 638
              ++ (290, 2) :: (1, 1) :: repeat (1, 2) 3712 ++ w)
             1); lia. }
    apply (hsteps_trans _ (HB [0] 20 1 35
      ((4, 2) :: (1, 1) :: repeat (1, 2) 74
       ++ (108, 2) :: (1, 1) :: repeat (1, 2) 638
       ++ (290, 2) :: (1, 1) :: repeat (1, 2) 3712 ++ w) 1)).
    { apply (pop12 15 [0] 5 5
             ((4, 2) :: (1, 1) :: repeat (1, 2) 74
              ++ (108, 2) :: (1, 1) :: repeat (1, 2) 638
              ++ (290, 2) :: (1, 1) :: repeat (1, 2) 3712 ++ w)
             1); lia. }
    apply (hsteps_trans _ (HC [0] 20 34 2
      ((2, 2) :: (1, 1) :: repeat (1, 2) 74
       ++ (108, 2) :: (1, 1) :: repeat (1, 2) 638
       ++ (290, 2) :: (1, 1) :: repeat (1, 2) 3712 ++ w) 1)).
    { apply (sTUP [0] 20 35 4 2
             ((1, 1) :: repeat (1, 2) 74
              ++ (108, 2) :: (1, 1) :: repeat (1, 2) 638
              ++ (290, 2) :: (1, 1) :: repeat (1, 2) 3712 ++ w)
             1); lia. }
    apply (hsteps_trans _ (HB [0] 19 1 34
      ((2, 2) :: (2, 2) :: (1, 1) :: repeat (1, 2) 74
       ++ (108, 2) :: (1, 1) :: repeat (1, 2) 638
       ++ (290, 2) :: (1, 1) :: repeat (1, 2) 3712 ++ w) 1)).
    { apply (hGRIND_even 15 [0] 19
             ((2, 2) :: (1, 1) :: repeat (1, 2) 74
              ++ (108, 2) :: (1, 1) :: repeat (1, 2) 638
              ++ (290, 2) :: (1, 1) :: repeat (1, 2) 3712 ++ w)
             1); lia. }
    apply (hsteps_step _ (HB [35; 20; 0] 3 1 3
      (repeat (1, 2) 74
       ++ (108, 2) :: (1, 1) :: repeat (1, 2) 638
       ++ (290, 2) :: (1, 1) :: repeat (1, 2) 3712 ++ w) 1));
      [apply hTRANS2_2; lia | apply hsteps_refl]. }
  (* S31: pop12 74, TUP, hGRIND_even 73, TUP2_1, TDN, TUP onto *)
  (* frame [77; 35; 20; 0], pair (102, 2)                      *)
  apply (hsteps_trans _ (HC [77; 35; 20; 0] 150 3 2
    ((102, 2) :: (1, 1) :: repeat (1, 2) 638
     ++ (290, 2) :: (1, 1) :: repeat (1, 2) 3712 ++ w) 1)).
  { apply (hsteps_trans _ (HB [35; 20; 0] 77 1 151
      ((108, 2) :: (1, 1) :: repeat (1, 2) 638
       ++ (290, 2) :: (1, 1) :: repeat (1, 2) 3712 ++ w) 1)).
    { apply (pop12 74 [35; 20; 0] 3 3
             ((108, 2) :: (1, 1) :: repeat (1, 2) 638
              ++ (290, 2) :: (1, 1) :: repeat (1, 2) 3712 ++ w)
             1); lia. }
    apply (hsteps_trans _ (HC [35; 20; 0] 77 150 2
      ((106, 2) :: (1, 1) :: repeat (1, 2) 638
       ++ (290, 2) :: (1, 1) :: repeat (1, 2) 3712 ++ w) 1)).
    { apply (sTUP [35; 20; 0] 77 151 108 2
             ((1, 1) :: repeat (1, 2) 638
              ++ (290, 2) :: (1, 1) :: repeat (1, 2) 3712 ++ w)
             1); lia. }
    apply (hsteps_trans _ (HB [35; 20; 0] 76 1 150
      ((2, 2) :: (106, 2) :: (1, 1) :: repeat (1, 2) 638
       ++ (290, 2) :: (1, 1) :: repeat (1, 2) 3712 ++ w) 1)).
    { apply (hGRIND_even 73 [35; 20; 0] 76
             ((106, 2) :: (1, 1) :: repeat (1, 2) 638
              ++ (290, 2) :: (1, 1) :: repeat (1, 2) 3712 ++ w)
             1); lia. }
    apply (hsteps_trans _ (HC [77; 35; 20; 0] 150 1 2
      ((104, 2) :: (1, 1) :: repeat (1, 2) 638
       ++ (290, 2) :: (1, 1) :: repeat (1, 2) 3712 ++ w) 1)).
    { apply (sTUP2_1 [35; 20; 0] 76 149 106
             ((1, 1) :: repeat (1, 2) 638
              ++ (290, 2) :: (1, 1) :: repeat (1, 2) 3712 ++ w)
             1); lia. }
    apply (hsteps_trans _ (HB [77; 35; 20; 0] 150 1 4
      ((104, 2) :: (1, 1) :: repeat (1, 2) 638
       ++ (290, 2) :: (1, 1) :: repeat (1, 2) 3712 ++ w) 1)).
    { apply (sTDN [77; 35; 20; 0] 150
             ((104, 2) :: (1, 1) :: repeat (1, 2) 638
              ++ (290, 2) :: (1, 1) :: repeat (1, 2) 3712 ++ w)
             1). }
    apply (sTUP [77; 35; 20; 0] 150 4 104 2
           ((1, 1) :: repeat (1, 2) 638
            ++ (290, 2) :: (1, 1) :: repeat (1, 2) 3712 ++ w)
           1); lia. }
  (* S32: CLEANG_even 50, TRANS2_1 onto frame [151; 77; 35; 20; 0] *)
  apply (hsteps_trans _ (HB [151; 77; 35; 20; 0] 107 1 3
    (repeat (1, 2) 638
     ++ (290, 2) :: (1, 1) :: repeat (1, 2) 3712 ++ w) 1)).
  { apply (hsteps_trans _ (HB [77; 35; 20; 0] 150 1 106
      ((2, 2) :: (1, 1) :: repeat (1, 2) 638
       ++ (290, 2) :: (1, 1) :: repeat (1, 2) 3712 ++ w) 1)).
    { apply (CLEANG_even 50 [77; 35; 20; 0] 150
             ((1, 1) :: repeat (1, 2) 638
              ++ (290, 2) :: (1, 1) :: repeat (1, 2) 3712 ++ w)
             1); lia. }
    apply (sTRANS2_1 [77; 35; 20; 0] 150 105 1
           (repeat (1, 2) 638
            ++ (290, 2) :: (1, 1) :: repeat (1, 2) 3712 ++ w)
           1); lia. }
  (* S33: pop12 638, TUP, hGRIND_even 637, TUP2_1, TDN, TUP onto *)
  (* frame [745; 151; 77; 35; 20; 0], pair (284, 2)              *)
  apply (hsteps_trans _ (HC [745; 151; 77; 35; 20; 0] 1278 3 2
    ((284, 2) :: (1, 1) :: repeat (1, 2) 3712 ++ w) 1)).
  { apply (hsteps_trans _ (HB [151; 77; 35; 20; 0] 745 1 1279
      ((290, 2) :: (1, 1) :: repeat (1, 2) 3712 ++ w) 1)).
    { apply (pop12 638 [151; 77; 35; 20; 0] 107 3
             ((290, 2) :: (1, 1) :: repeat (1, 2) 3712 ++ w)
             1); lia. }
    apply (hsteps_trans _ (HC [151; 77; 35; 20; 0] 745 1278 2
      ((288, 2) :: (1, 1) :: repeat (1, 2) 3712 ++ w) 1)).
    { apply (sTUP [151; 77; 35; 20; 0] 745 1279 290 2
             ((1, 1) :: repeat (1, 2) 3712 ++ w) 1); lia. }
    apply (hsteps_trans _ (HB [151; 77; 35; 20; 0] 744 1 1278
      ((2, 2) :: (288, 2) :: (1, 1) :: repeat (1, 2) 3712 ++ w) 1)).
    { apply (hGRIND_even 637 [151; 77; 35; 20; 0] 744
             ((288, 2) :: (1, 1) :: repeat (1, 2) 3712 ++ w)
             1); lia. }
    apply (hsteps_trans _ (HC [745; 151; 77; 35; 20; 0] 1278 1 2
      ((286, 2) :: (1, 1) :: repeat (1, 2) 3712 ++ w) 1)).
    { apply (sTUP2_1 [151; 77; 35; 20; 0] 744 1277 288
             ((1, 1) :: repeat (1, 2) 3712 ++ w) 1); lia. }
    apply (hsteps_trans _ (HB [745; 151; 77; 35; 20; 0] 1278 1 4
      ((286, 2) :: (1, 1) :: repeat (1, 2) 3712 ++ w) 1)).
    { apply (sTDN [745; 151; 77; 35; 20; 0] 1278
             ((286, 2) :: (1, 1) :: repeat (1, 2) 3712 ++ w)
             1). }
    apply (sTUP [745; 151; 77; 35; 20; 0] 1278 4 286 2
           ((1, 1) :: repeat (1, 2) 3712 ++ w) 1); lia. }
  (* S34: CLEANG_even 141, TRANS2_1 onto MID *)
  apply (hsteps_trans _ (HB [745; 151; 77; 35; 20; 0] 1278 1 288
    ((2, 2) :: (1, 1) :: repeat (1, 2) 3712 ++ w) 1)).
  { apply (CLEANG_even 141 [745; 151; 77; 35; 20; 0] 1278
           ((1, 1) :: repeat (1, 2) 3712 ++ w) 1); lia. }
  apply (sTRANS2_1 [745; 151; 77; 35; 20; 0] 1278 287 1
         (repeat (1, 2) 3712 ++ w) 1); lia.
Qed.

(* ----------------------------------------------------------------- *)
(* END47_TO_TOP: END -> front -> DIPGRIND (3710, rho) -> CASCADE47  *)
(* -> pop12 3712 -> TOP, uniform in (k, beta) for k >= 3714.        *)
(* ----------------------------------------------------------------- *)

Lemma END47_TO_TOP : forall k beta, 3714 <= k -> 2 <= beta ->
  hsteps (HB [317; 40; 14; 5] 2204 1 3711
            ((2 * k, 2) :: (1, 1) :: repeat (1, 2) (beta - 1)) 1)
         (HB [1279; 745; 151; 77; 35; 20; 0] 4001 1 7427
            ((2 * (k - 3713), 2) :: (1, 1)
             :: repeat (1, 2) (beta - 1)) 1).
Proof.
  intros k beta Hk Hb.
  apply (hsteps_trans _ (HC [2204; 317; 40; 14; 5] 3710 3 2
    ((2 * k - 6, 2) :: (1, 1) :: repeat (1, 2) (beta - 1)) 1)).
  { apply (END47_FRONT k beta); lia. }
  apply (hsteps_trans _ (HC [2204; 317; 40; 14; 5] 0 3 2
    (repeat (1, 2) 3710
     ++ ((2 * (k - 3713), 2) :: (1, 1)
         :: repeat (1, 2) (beta - 1))) 1)).
  { replace (2 * k - 6) with (2 * 3710 + 2 * (k - 3713)) by lia.
    apply (DIPGRIND 3710 (2 * (k - 3713)) [2204; 317; 40; 14; 5]
           ((1, 1) :: repeat (1, 2) (beta - 1)) 1); lia. }
  apply (hsteps_trans _ (HB [1279; 745; 151; 77; 35; 20; 0] 289 1 3
    (repeat (1, 2) 3712
     ++ ((2 * (k - 3713), 2) :: (1, 1)
         :: repeat (1, 2) (beta - 1))) 1)).
  { apply (CASCADE47 ((2 * (k - 3713), 2) :: (1, 1)
                      :: repeat (1, 2) (beta - 1))). }
  apply (pop12 3712 [1279; 745; 151; 77; 35; 20; 0] 289 3
         ((2 * (k - 3713), 2) :: (1, 1) :: repeat (1, 2) (beta - 1))
         1); lia.
Qed.

(* ----------------------------------------------------------------- *)
(* The TOP closings: rho = 2, rho = 4, rho = 6, and band 1          *)
(* (rho = 2 * j, 4 <= j <= 7429, i.e. 8 <= rho <= 14858).           *)
(* ----------------------------------------------------------------- *)

(* Note: literals >= 7426 are parsed as Nat.of_num_uint atoms,    *)
(* which lia cannot compare; closearith falls back to computing    *)
(* the boolean <= for closed side conditions.                      *)
Ltac closearith := first [ lia | apply Nat.leb_le; reflexivity ].

Lemma TOP47_2 : forall beta, 2 <= beta ->
  hsteps (HB [1279; 745; 151; 77; 35; 20; 0] 4001 1 7427
            ((2, 2) :: (1, 1) :: repeat (1, 2) (beta - 1)) 1)
         (HB [4002; 1279; 745; 151; 77; 35; 20; 0]
            (7428 + (beta - 1)) 1 (2 * beta + 1) [] 1).
Proof.
  intros beta Hb.
  apply (hsteps_trans _ (HB [4002; 1279; 745; 151; 77; 35; 20; 0]
    7428 1 3 (repeat (1, 2) (beta - 1)) 1)).
  { apply (sTRANS2_1 [1279; 745; 151; 77; 35; 20; 0] 4001 7426 1
           (repeat (1, 2) (beta - 1)) 1); lia. }
  apply (CASCADE_POPFIN [4002; 1279; 745; 151; 77; 35; 20; 0] 7428
         beta); lia.
Qed.

Lemma TOP47_4 : forall beta, 2 <= beta ->
  hsteps (HB [1279; 745; 151; 77; 35; 20; 0] 4001 1 7427
            ((4, 2) :: (1, 1) :: repeat (1, 2) (beta - 1)) 1)
         (HB [7427; 4001; 1279; 745; 151; 77; 35; 20; 0] (beta + 2) 1
            (2 * beta + 1) [] 1).
Proof.
  intros beta Hb.
  apply (hsteps_trans _ (HC [1279; 745; 151; 77; 35; 20; 0] 4001
    7426 2 ((2, 2) :: (1, 1) :: repeat (1, 2) (beta - 1)) 1)).
  { apply (sTUP [1279; 745; 151; 77; 35; 20; 0] 4001 7427 4 2
           ((1, 1) :: repeat (1, 2) (beta - 1)) 1); closearith. }
  apply (hsteps_trans _ (HB [1279; 745; 151; 77; 35; 20; 0] 4000
    1 7426 ((2, 2) :: (2, 2) :: (1, 1)
            :: repeat (1, 2) (beta - 1)) 1)).
  { apply (hGRIND_even 3711 [1279; 745; 151; 77; 35; 20; 0] 4000
           ((2, 2) :: (1, 1) :: repeat (1, 2) (beta - 1)) 1);
      closearith. }
  apply (hsteps_trans _ (HB [7427; 4001; 1279; 745; 151; 77; 35; 20; 0]
    3 1 3 (repeat (1, 2) (beta - 1)) 1)).
  { apply (hsteps_step _ (HB [7427; 4001; 1279; 745; 151; 77; 35; 20; 0]
      3 1 3 (repeat (1, 2) (beta - 1)) 1));
      [apply hTRANS2_2; lia | apply hsteps_refl]. }
  replace (beta + 2) with (3 + (beta - 1)) by lia.
  apply (CASCADE_POPFIN [7427; 4001; 1279; 745; 151; 77; 35; 20; 0] 3
         beta); lia.
Qed.

Lemma TOP47_6 : forall beta, 2 <= beta ->
  hsteps (HB [1279; 745; 151; 77; 35; 20; 0] 4001 1 7427
            ((6, 2) :: (1, 1) :: repeat (1, 2) (beta - 1)) 1)
         (HB [7427; 4001; 1279; 745; 151; 77; 35; 20; 0] (beta + 4) 1
            (2 * beta + 1) [] 1).
Proof.
  intros beta Hb.
  apply (hsteps_trans _ (HC [1279; 745; 151; 77; 35; 20; 0] 4001
    7426 2 ((4, 2) :: (1, 1) :: repeat (1, 2) (beta - 1)) 1)).
  { apply (sTUP [1279; 745; 151; 77; 35; 20; 0] 4001 7427 6 2
           ((1, 1) :: repeat (1, 2) (beta - 1)) 1); closearith. }
  apply (hsteps_trans _ (HB [1279; 745; 151; 77; 35; 20; 0] 4000
    1 7426 ((2, 2) :: (4, 2) :: (1, 1)
            :: repeat (1, 2) (beta - 1)) 1)).
  { apply (hGRIND_even 3711 [1279; 745; 151; 77; 35; 20; 0] 4000
           ((4, 2) :: (1, 1) :: repeat (1, 2) (beta - 1)) 1);
      closearith. }
  apply (hsteps_trans _ (HC [4001; 1279; 745; 151; 77; 35; 20; 0]
    7426 1 2 ((2, 2) :: (1, 1) :: repeat (1, 2) (beta - 1)) 1)).
  { replace ((2, 2) :: (1, 1) :: repeat (1, 2) (beta - 1))
      with ((4 - 2, 2) :: (1, 1) :: repeat (1, 2) (beta - 1))
      by sec_eq.
    apply (sTUP2_1 [1279; 745; 151; 77; 35; 20; 0] 4000 7425 4
           ((1, 1) :: repeat (1, 2) (beta - 1)) 1); lia. }
  apply (hsteps_trans _ (HB [4001; 1279; 745; 151; 77; 35; 20; 0]
    7426 1 4 ((2, 2) :: (1, 1) :: repeat (1, 2) (beta - 1)) 1)).
  { apply (sTDN [4001; 1279; 745; 151; 77; 35; 20; 0] 7426
           ((2, 2) :: (1, 1) :: repeat (1, 2) (beta - 1)) 1). }
  apply (hsteps_trans _ (HB [7427; 4001; 1279; 745; 151; 77; 35; 20; 0]
    5 1 3 (repeat (1, 2) (beta - 1)) 1)).
  { apply (sTRANS2_1 [4001; 1279; 745; 151; 77; 35; 20; 0] 7426 3 1
           (repeat (1, 2) (beta - 1)) 1); lia. }
  replace (beta + 4) with (5 + (beta - 1)) by lia.
  apply (CASCADE_POPFIN [7427; 4001; 1279; 745; 151; 77; 35; 20; 0] 5
         beta); lia.
Qed.

Lemma TOP47_BAND : forall j beta, 4 <= j -> j <= 7429 -> 2 <= beta ->
  hsteps (HB [1279; 745; 151; 77; 35; 20; 0] 4001 1 7427
            ((2 * j, 2) :: (1, 1) :: repeat (1, 2) (beta - 1)) 1)
         (HB [7427; 4001; 1279; 745; 151; 77; 35; 20; 0]
            (2 * j + beta - 2) 1 (2 * beta + 1) [] 1).
Proof.
  intros j beta Hj1 Hj2 Hb.
  apply (hsteps_trans _ (HC [1279; 745; 151; 77; 35; 20; 0] 4001
    7426 2 ((2 * j - 2, 2) :: (1, 1) :: repeat (1, 2) (beta - 1)) 1)).
  { apply (sTUP [1279; 745; 151; 77; 35; 20; 0] 4001 7427 (2 * j) 2
           ((1, 1) :: repeat (1, 2) (beta - 1)) 1); closearith. }
  apply (hsteps_trans _ (HB [1279; 745; 151; 77; 35; 20; 0] 4000
    1 7426 ((2, 2) :: (2 * j - 2, 2) :: (1, 1)
            :: repeat (1, 2) (beta - 1)) 1)).
  { apply (hGRIND_even 3711 [1279; 745; 151; 77; 35; 20; 0] 4000
           ((2 * j - 2, 2) :: (1, 1) :: repeat (1, 2) (beta - 1))
           1); closearith. }
  apply (hsteps_trans _ (HC [4001; 1279; 745; 151; 77; 35; 20; 0]
    7426 1 2 ((2 * j - 4, 2) :: (1, 1) :: repeat (1, 2) (beta - 1)) 1)).
  { replace ((2 * j - 4, 2) :: (1, 1) :: repeat (1, 2) (beta - 1))
      with ((2 * j - 2 - 2, 2) :: (1, 1) :: repeat (1, 2) (beta - 1))
      by sec_eq.
    apply (sTUP2_1 [1279; 745; 151; 77; 35; 20; 0] 4000 7425
           (2 * j - 2) ((1, 1) :: repeat (1, 2) (beta - 1)) 1); lia. }
  apply (hsteps_trans _ (HB [4001; 1279; 745; 151; 77; 35; 20; 0]
    7426 1 4 ((2 * j - 4, 2) :: (1, 1) :: repeat (1, 2) (beta - 1)) 1)).
  { apply (sTDN [4001; 1279; 745; 151; 77; 35; 20; 0] 7426
           ((2 * j - 4, 2) :: (1, 1) :: repeat (1, 2) (beta - 1))
           1). }
  apply (hsteps_trans _ (HC [4001; 1279; 745; 151; 77; 35; 20; 0]
    7426 3 2 ((2 * j - 6, 2) :: (1, 1) :: repeat (1, 2) (beta - 1)) 1)).
  { replace ((2 * j - 6, 2) :: (1, 1) :: repeat (1, 2) (beta - 1))
      with ((2 * j - 4 - 2, 2) :: (1, 1) :: repeat (1, 2) (beta - 1))
      by sec_eq.
    apply (sTUP [4001; 1279; 745; 151; 77; 35; 20; 0] 7426 4
           (2 * j - 4) 2 ((1, 1) :: repeat (1, 2) (beta - 1)) 1);
      lia. }
  apply (hsteps_trans _ (HB [4001; 1279; 745; 151; 77; 35; 20; 0]
    7426 1 (2 * j - 2)
    ((2, 2) :: (1, 1) :: repeat (1, 2) (beta - 1)) 1)).
  { replace (2 * j - 6) with (2 * (j - 4) + 2) by lia.
    replace (2 * j - 2) with (2 * (j - 4) + 6) by lia.
    apply (CLEANG_even (j - 4) [4001; 1279; 745; 151; 77; 35; 20; 0]
           7426 ((1, 1) :: repeat (1, 2) (beta - 1)) 1).
    (* the floor (j - 4) + 1 <= 7426: lia cannot compare the *)
    (* of_num_uint atom 7426, so route via j <= 7429          *)
    apply Nat.le_trans with (j - 3).
    - lia.
    - change 7426 with (7429 - 3).
      apply Nat.sub_le_mono_r. exact Hj2. }
  apply (hsteps_trans _ (HB [7427; 4001; 1279; 745; 151; 77; 35; 20; 0]
    (2 * j - 1) 1 3 (repeat (1, 2) (beta - 1)) 1)).
  { replace (2 * j - 2) with (S (2 * j - 3)) by lia.
    replace (2 * j - 1) with (S (S (2 * j - 3))) by lia.
    apply (sTRANS2_1 [4001; 1279; 745; 151; 77; 35; 20; 0] 7426
           (2 * j - 3) 1 (repeat (1, 2) (beta - 1)) 1); lia. }
  replace (2 * j + beta - 2) with (2 * j - 1 + (beta - 1)) by lia.
  apply (CASCADE_POPFIN [7427; 4001; 1279; 745; 151; 77; 35; 20; 0]
         (2 * j - 1) beta); lia.
Qed.

(* ----------------------------------------------------------------- *)
(* TAIL2_END2: the strictly smaller residual core -- the totality   *)
(* of the TOP state for rho = 2 * j, j >= 7430 (rho >= 14860),      *)
(* where the GRIND2 pair (rho - 6, 2) at counter 7426 takes the     *)
(* DIPDESC boundary a second time.  A Definition (lemma             *)
(* parameter), never an axiom.                                      *)
(* ----------------------------------------------------------------- *)

Definition TAIL2_END2 : Prop :=
  forall j beta, 7430 <= j -> 2 <= beta ->
  exists pb A, beta <= A /\
    hsteps (HB [1279; 745; 151; 77; 35; 20; 0] 4001 1 7427
              ((2 * j, 2) :: (1, 1) :: repeat (1, 2) (beta - 1)) 1)
           (HB pb A 1 (2 * beta + 1) [] 1).

(* ----------------------------------------------------------------- *)
(* TAIL2_END_of47: TAIL2_END, modulo TAIL2_END2.  The k-range       *)
(* splits at rho = 2 (k - 3713): the four small cases and band 1    *)
(* are proved above; j >= 7430 is the core.                         *)
(* ----------------------------------------------------------------- *)

Lemma TAIL2_END_of47 : TAIL2_END2 -> TAIL2_END.
Proof.
  intros H2 k beta Hk Hb.
  pose proof (END47_TO_TOP k beta Hk Hb) as Htop.
  destruct (le_lt_dec 7430 (k - 3713)) as [Hbig | Hsmall].
  - (* j = k - 3713 >= 7430: the core *)
    destruct (H2 (k - 3713) beta Hbig Hb)
      as [pb [A [Ha Hsteps]]].
    exists pb, A. split; [exact Ha |].
    exact (hsteps_trans _ _ _ Htop Hsteps).
  - destruct (Nat.eq_dec k 3714) as [-> | Hne1].
    + (* rho = 2 *)
      exists [4002; 1279; 745; 151; 77; 35; 20; 0],
        (7428 + (beta - 1)).
      split; [change 7428 with (S 7427); lia |].
      exact (hsteps_trans _ _ _ Htop (TOP47_2 beta Hb)).
    + destruct (Nat.eq_dec k 3715) as [-> | Hne2].
      * (* rho = 4 *)
        exists [7427; 4001; 1279; 745; 151; 77; 35; 20; 0],
          (beta + 2).
        split; [lia |].
        exact (hsteps_trans _ _ _ Htop (TOP47_4 beta Hb)).
      * destruct (Nat.eq_dec k 3716) as [-> | Hne3].
        -- (* rho = 6 *)
           exists [7427; 4001; 1279; 745; 151; 77; 35; 20; 0],
             (beta + 4).
           split; [lia |].
           exact (hsteps_trans _ _ _ Htop (TOP47_6 beta Hb)).
        -- (* band 1: j = k - 3713, 4 <= j <= 7429 *)
           exists [7427; 4001; 1279; 745; 151; 77; 35; 20; 0],
             (2 * (k - 3713) + beta - 2).
           split; [lia |].
           assert (Hj2 : k - 3713 <= 7429).
           { change 7430 with (S 7429) in Hsmall.
             apply (proj1 (Nat.lt_succ_r _ _) Hsmall). }
           exact (hsteps_trans _ _ _ Htop
                    (TOP47_BAND (k - 3713) beta
                       ltac:(lia) Hj2 Hb)).
Qed.

(* ----------------------------------------------------------------- *)
(* ESC_ERA_LAW_47: the phase-8 ESC era law at every even            *)
(* R >= 1278, modulo TAIL2_END2 alone.                              *)
(* ----------------------------------------------------------------- *)

Lemma ESC_ERA_LAW_47 : TAIL2_END2 ->
  forall M beta, 616 <= M -> 2 <= beta ->
  exists n c pb a,
    run n (esc_src (2 * M + 52) (beta - 2)) = Some c
    /\ cfg_sim c (rcsec (false :: repeat true (S a) ++ enc pb)
                        (2 * beta + 2) [(1, 2)])
    /\ beta <= a.
Proof.
  intros H M beta HM Hb.
  apply (ESC_ERA_LAW_46 (TAIL2_END_of47 H) M beta HM Hb).
Qed.

(* ----------------------------------------------------------------- *)
(* Assumption audit                                                  *)
(* ----------------------------------------------------------------- *)

Print Assumptions END47_FRONT.
Print Assumptions CASCADE47.
Print Assumptions END47_TO_TOP.
Print Assumptions TOP47_2.
Print Assumptions TOP47_4.
Print Assumptions TOP47_6.
Print Assumptions TOP47_BAND.
Print Assumptions TAIL2_END_of47.
Print Assumptions ESC_ERA_LAW_47.
