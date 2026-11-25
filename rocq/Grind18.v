(* ================================================================= *)
(*  Grind18.v -- Phase 50: the fourth re-descent cascade of the     *)
(*  TOP3 state, mechanised as a fixed parse, closing TAIL2_END4     *)
(*  for the whole first j-band 32606 <= j <= 99728 (TOP3            *)
(*  parameters) and reducing the rest to a strictly smaller core    *)
(*  at the TOP4 state.                                              *)
(*                                                                  *)
(*  Phase 49 left the ESC side of H_LOOP resting on TAIL2_END4      *)
(*  (Grind17.v): the totality of the TOP3 state                     *)
(*                                                                  *)
(*    TOP3(j, beta) = HB [7493; 3816; 259; 93; 50; 14; 5] 16899     *)
(*                    1 32603 ((2j, 2) :: (1, 1) :: (1, 2)^(beta-1)) *)
(*                                                                  *)
(*  for j >= 32606.  There the GRIND4 pair (2j - 6, 2) at counter   *)
(*  32602 exceeds the CLEANG_even floor and takes the DIPDESC       *)
(*  boundary a fourth time.  Phase 50 traces the walk               *)
(*  (rocq/hsim50.py, ALL PASS: the 82-waypoint chain below          *)
(*  asserted verbatim at (j, beta) in {(32606, 2), (32606, 3),      *)
(*  (32607, 2), (40000, 2), (99728, 2)}; TOP4 finals and the        *)
(*  cycle-5 fence asserted too; a junk-tail probe confirms          *)
(*  CASCADE50 is stated for an arbitrary tail; the streaming        *)
(*  walker of hsim49 is reused).                                    *)
(*                                                                  *)
(*  FINDING: the fourth descent is again a FIXED parse, uniform     *)
(*  in (j, beta) -- not a return to TOP3, TOP2 or TOP.  Writing     *)
(*  r4 = 2j - 65210 >= 2 for the DIPGRIND residue at GRIND4:        *)
(*                                                                  *)
(*    TOP3 --front (TUP, hGRIND_even 16299, TUP2_1, TDN, TUP)-->    *)
(*      GRIND4 = HC [16899; 7493; 3816; 259; 93; 50; 14; 5]         *)
(*                 32602 3 2 ((2j - 6, 2) :: tail)                  *)
(*    --DIPGRIND (32602, r4)-->                                     *)
(*      HC [16899; 7493; ...] 0 3 2 ((1, 2)^32602 ++ W),            *)
(*        W = ((r4, 2) :: (1, 1) :: (1, 2)^(beta - 1))              *)
(*    --CASCADE50 (fixed parse, arbitrary tail)-->                  *)
(*      TOP4 = HB [9558; 1285; 774; 112; 20; 0] 47594 1 67121 W.    *)
(*                                                                  *)
(*  CASCADE50 descends the TOP3 frame's own blocks by PX2A +        *)
(*  DIPGRIND levels (7491, 1911), (257, 3296), (612, 2066),         *)
(*  (12, 279), (32, 209), (3, 5), (3, 2), (74, 55), (3, 37),        *)
(*  (3, 2), (13, 5), with fronts (TUP + hGRIND_even t + TUP2_1 +    *)
(*  TDN + TUP) at pairs 3296, 279, 209, 55, 2066, 1911, two         *)
(*  PX2Bgen dips, two bottom-frame excursions (PX2B0 + PUSHX        *)
(*  regrowth), CLEANG_odd grinds 23, 951 and a CLEANG_even grind    *)
(*  1029, landing on TOP4.  No harness-caught correction this       *)
(*  phase: the characterisation matched the Phase 46-49 pattern     *)
(*  on the first full run (one harness fix only: the source         *)
(*  config itself is not a walker record, so the asserted chain     *)
(*  starts at the front's TUP landing).                             *)
(*                                                                  *)
(*  TOP4 then closes by the size of r4 = 2 * j4 (j4 = j - 32605     *)
(*  in TOP4's own parameter):                                      *)
(*    r4 = 2:       TRANS2_1 + CASCADE_POPFIN, A = 67121 + beta;    *)
(*    r4 = 4:       TUP + hGRIND_even 33558 + TRANS2_2              *)
(*                    + CASCADE_POPFIN, A = beta + 2;               *)
(*    r4 = 6:       TUP + hGRIND_even 33558 + TUP2_1 + TDN          *)
(*                    + TRANS2_1 + CASCADE_POPFIN, A = beta + 4;    *)
(*    8 <= r4 <= 134246 (band 4): TUP + hGRIND_even 33558 + TUP2_1  *)
(*      + TDN + TUP onto GRIND5 = HC [47594; 9558; ...] 67120 3 2   *)
(*      ((r4 - 6, 2) :: tail), whose pair grinds CLEANLY by         *)
(*      CLEANG_even (floor (r4 - 8)/2 + 1 <= 67120, exactly         *)
(*      r4 <= 134246), then TRANS2_1 + CASCADE_POPFIN,              *)
(*      A = r4 + beta - 2, frame [67121; 47594; 9558; ...].         *)
(*      (The band counter is again the shuttle moved into the       *)
(*      counter slot by TUP2_1: 67120, not 47594.)                  *)
(*                                                                  *)
(*  For r4 >= 134248 (j4 >= 67124, i.e. TOP3-parameter              *)
(*  j >= 99729) the pair (r4 - 6, 2) at counter 67120 exceeds       *)
(*  the CLEANG_even floor and the rounds take the DIPDESC           *)
(*  boundary a FIFTH time (hsim50 Part 3: the GRIND5 state and      *)
(*  the DIPGRIND (67120, r4 - 134246) landing both occur at         *)
(*  j = 99729, 99800, 120000).  The fifth descent is expected to    *)
(*  be a NEW cascade with different constants, so no cycle          *)
(*  induction in the current vocabulary closes it; what remains     *)
(*  is the strictly smaller core                                    *)
(*                                                                  *)
(*    TAIL2_END5: the totality of the ONE pair (2j, 2) at the ONE   *)
(*    fixed TOP4 state HB [9558; 1285; 774; 112; 20; 0] 47594       *)
(*    1 67121, for j >= 67124 (r4 = 2j >= 134248), beta >= 2.       *)
(*                                                                  *)
(*  The core's range shrank from [32606, infty) to [99729, infty)   *)
(*  in TOP3 parameters; the band width roughly doubled again        *)
(*  (32606 -> 99728).  Via TAIL2_END4_of50 + TAIL2_END3_of49 +      *)
(*  ESC_ERA_LAW_49 the ESC instances at every even R >= 1278 now    *)
(*  rest on TAIL2_END5 alone (ESC_ERA_LAW_50 below; Loop.v          *)
(*  Part 4k).                                                       *)
(* ================================================================= *)

Require Import List Bool Arith Lia ZArith.
Import ListNotations.
Require Import TM Sections Mirror TokenPass Recoord Era Esc Dev
               Grind Grind2 Grind3 Grind4 Grind5 Grind6 Grind7 Grind8
               Grind9 Grind10 Grind11 Grind12 Grind13 Grind14 Grind15
               Grind16 Grind17.

(* Section equality: componentwise, arithmetic leaves by lia.      *)
Ltac sec_eq :=
  repeat (first [ solve [reflexivity] | solve [lia] | f_equal ]).

(* Closed-numeral arithmetic: literals >= 7426 are parsed as       *)
(* Nat.of_num_uint atoms, which lia cannot relate to variables;    *)
(* for purely closed <= goals the boolean check decides them.      *)
Ltac closearith :=
  first [ lia | apply Nat.leb_le; reflexivity ].

(* ----------------------------------------------------------------- *)
(* CASCADE50: the DIP4 spine over frame [16899; 7493; 3816; 259;    *)
(* 93; 50; 14; 5] regrows onto TOP4, for an ARBITRARY tail w.       *)
(* Segment map (waypoints asserted verbatim in hsim50.py):          *)
(*   S1  PX2A + PUSH + TDN + TUP onto [3816; 259; 93; 50; 14; 5]    *)
(*   S2  DIPGRIND (7491, 1911)                                      *)
(*   S3  PX2A + PUSH + TDN + TUP onto [93; 50; 14; 5]               *)
(*   S4  DIPGRIND (257, 3296)                                       *)
(*   S5  PX2A onto [14; 5], S6 hGRIND 44, S7 POP, S8 pop12 259      *)
(*   S9  front(3296) onto [309; 14; 5]                              *)
(*   S10 DIPGRIND (612, 2066)                                       *)
(*   S11 PX2A + PUSH + TDN + TUP onto [5]                           *)
(*   S12 DIPGRIND (12, 279)                                         *)
(*   S13 PX2Bgen onto [0], S14 pop12 1, S15 POP, S16 pop12 14       *)
(*   S17 front(279) onto [19; 0]                                    *)
(*   S18 DIPGRIND (32, 209)                                         *)
(*   S19 PX2A0 + TUP + TDN + TUP at [0]                             *)
(*   S20 DIPGRIND (3, 5)                                            *)
(*   S21 PX2B0 at [], S22 pop12 4                                   *)
(*   S23 bottom front (TUP + PUSH + TDN + TUP) at []                *)
(*   S24 DIPGRIND (3, 2)                                            *)
(*   S25 PUSHX, S26 pop12 3, S27 TUP2_1 + TDN regrowth onto [5],    *)
(*       S28 pop12 1, S29 POP, S30 pop12 34                         *)
(*   S31 front(209) onto [49; 5]                                    *)
(*   S32 DIPGRIND (74, 55)                                          *)
(*   S33 PX2A + PUSH + TDN + TUP onto []                            *)
(*   S34 DIPGRIND (3, 37)                                           *)
(*   S35 PUSHX, S36 pop12 3                                         *)
(*   S37 bottom front at []                                         *)
(*   S38 DIPGRIND (3, 2)                                            *)
(*   S39 PUSHX, S40 pop12 3                                         *)
(*   S41 TUP2_1 + TDN + TUP regrowth onto [5]                       *)
(*   S42 DIPGRIND (13, 5)                                           *)
(*   S43 PX2Bgen onto [0], S44 pop12 1, S45 POP, S46 pop12 15       *)
(*   S47 front(5) partial onto [20; 0]                              *)
(*   S48 pop12 1, S49 POP, S50 pop12 76                             *)
(*   S51 front(55) onto [112; 20; 0]                                *)
(*   S52 CLEANG_odd 23, S53 pop12 1, S54 POP, S55 pop12 614         *)
(*   S56 front(2066) onto [774; 112; 20; 0]                         *)
(*   S57 CLEANG_even 1029, S58 TRANS2_1, S59 pop12 7493             *)
(*   S60 front(1911) onto [9558; 1285; 774; 112; 20; 0]             *)
(*   S61 CLEANG_odd 951, S62 pop12 1, S63 POP, S64 pop12 32604      *)
(*       = TOP4                                                     *)
(* ----------------------------------------------------------------- *)

Lemma CASCADE50 : forall w,
  hsteps (HC [16899; 7493; 3816; 259; 93; 50; 14; 5] 0 3 2
            (repeat (1, 2) 32602 ++ w) 1)
         (HB [9558; 1285; 774; 112; 20; 0] 47594 1 67121 w 1).
Proof.
  intro w.
  (* S1: PX2A + PUSH + TDN + TUP onto [3816; 259; 93; 50; 14; 5], pair (16893, 2) *)
  apply (hsteps_trans _ (HC [3816; 259; 93; 50; 14; 5] 7491 3 2
                         ((16893, 2) :: (1, 1) :: repeat (1, 2) 32604 ++ w) 1)).
  {
    apply (hsteps_trans _ (HC [3816; 259; 93; 50; 14; 5] 7492 16897 2
                           ((1, 1) :: (1, 2) :: (1, 2) :: repeat (1, 2) 32602 ++ w) 1)).
    {
      apply (hsteps_step _ (HC [3816; 259; 93; 50; 14; 5] 7492 16897 2
                     ((1, 1) :: (1, 2) :: (1, 2) :: repeat (1, 2) 32602 ++ w) 1));
        [apply hPX2A | apply hsteps_refl].
    }
    apply (hsteps_trans _ (HC [3816; 259; 93; 50; 14; 5] 7491 1 2
                           ((16895, 2) :: (1, 1) :: (1, 2) :: (1, 2) :: repeat (1, 2) 32602 ++ w) 1)).
    {
      apply (sPUSH [3816; 259; 93; 50; 14; 5] 7491 16897
             ((1, 1) :: (1, 2) :: (1, 2) :: repeat (1, 2) 32602 ++ w) 1); closearith.
    }
    apply (hsteps_trans _ (HB [3816; 259; 93; 50; 14; 5] 7491 1 4
                           ((16895, 2) :: (1, 1) :: (1, 2) :: (1, 2) :: repeat (1, 2) 32602 ++ w) 1)).
    {
      apply (sTDN [3816; 259; 93; 50; 14; 5] 7491
             ((16895, 2) :: (1, 1) :: (1, 2) :: (1, 2) :: repeat (1, 2) 32602 ++ w) 1).
    }
    replace ((16893, 2) :: (1, 1) :: repeat (1, 2) 32604 ++ w)
      with ((16895 - 2, 2) :: (1, 1) :: (1, 2) :: (1, 2) :: repeat (1, 2) 32602 ++ w)
      by sec_eq.
    apply (sTUP [3816; 259; 93; 50; 14; 5] 7491 4 16895 2
           ((1, 1) :: (1, 2) :: (1, 2) :: repeat (1, 2) 32602 ++ w) 1); closearith.
  }
  (* S2: DIPGRIND (7491, 1911) *)
  apply (hsteps_trans _ (HC [3816; 259; 93; 50; 14; 5] 0 3 2
                         (repeat (1, 2) 7491 ++ (1911, 2) :: (1, 1) :: repeat (1, 2) 32604 ++ w) 1)).
  {
    apply (DIPGRIND 7491 1911 [3816; 259; 93; 50; 14; 5]
           ((1, 1) :: repeat (1, 2) 32604 ++ w) 1); closearith.
  }
  (* S3: PX2A + PUSH + TDN + TUP onto [93; 50; 14; 5], pair (3810, 2) *)
  apply (hsteps_trans _ (HC [93; 50; 14; 5] 257 3 2
                         ((3810, 2) :: (1, 1) :: repeat (1, 2) 7493 ++ (1911, 2) :: (1, 1) :: repeat (1, 2) 32604 ++ w) 1)).
  {
    apply (hsteps_trans _ (HC [93; 50; 14; 5] 258 3814 2
                           ((1, 1) :: (1, 2) :: (1, 2) :: repeat (1, 2) 7491 ++ (1911, 2) :: (1, 1) :: repeat (1, 2) 32604 ++ w) 1)).
    {
      apply (hsteps_step _ (HC [93; 50; 14; 5] 258 3814 2
                     ((1, 1) :: (1, 2) :: (1, 2) :: repeat (1, 2) 7491 ++ (1911, 2) :: (1, 1) :: repeat (1, 2) 32604 ++ w) 1));
        [apply hPX2A | apply hsteps_refl].
    }
    apply (hsteps_trans _ (HC [93; 50; 14; 5] 257 1 2
                           ((3812, 2) :: (1, 1) :: (1, 2) :: (1, 2) :: repeat (1, 2) 7491 ++ (1911, 2) :: (1, 1) :: repeat (1, 2) 32604 ++ w) 1)).
    {
      apply (sPUSH [93; 50; 14; 5] 257 3814
             ((1, 1) :: (1, 2) :: (1, 2) :: repeat (1, 2) 7491 ++ (1911, 2) :: (1, 1) :: repeat (1, 2) 32604 ++ w) 1); closearith.
    }
    apply (hsteps_trans _ (HB [93; 50; 14; 5] 257 1 4
                           ((3812, 2) :: (1, 1) :: (1, 2) :: (1, 2) :: repeat (1, 2) 7491 ++ (1911, 2) :: (1, 1) :: repeat (1, 2) 32604 ++ w) 1)).
    {
      apply (sTDN [93; 50; 14; 5] 257
             ((3812, 2) :: (1, 1) :: (1, 2) :: (1, 2) :: repeat (1, 2) 7491 ++ (1911, 2) :: (1, 1) :: repeat (1, 2) 32604 ++ w) 1).
    }
    replace ((3810, 2) :: (1, 1) :: repeat (1, 2) 7493 ++ (1911, 2) :: (1, 1) :: repeat (1, 2) 32604 ++ w)
      with ((3812 - 2, 2) :: (1, 1) :: (1, 2) :: (1, 2) :: repeat (1, 2) 7491 ++ (1911, 2) :: (1, 1) :: repeat (1, 2) 32604 ++ w)
      by sec_eq.
    apply (sTUP [93; 50; 14; 5] 257 4 3812 2
           ((1, 1) :: (1, 2) :: (1, 2) :: repeat (1, 2) 7491 ++ (1911, 2) :: (1, 1) :: repeat (1, 2) 32604 ++ w) 1); closearith.
  }
  (* S4: DIPGRIND (257, 3296) *)
  apply (hsteps_trans _ (HC [93; 50; 14; 5] 0 3 2
                         (repeat (1, 2) 257 ++ (3296, 2) :: (1, 1) :: repeat (1, 2) 7493 ++ (1911, 2) :: (1, 1) :: repeat (1, 2) 32604 ++ w) 1)).
  {
    apply (DIPGRIND 257 3296 [93; 50; 14; 5]
           ((1, 1) :: repeat (1, 2) 7493 ++ (1911, 2) :: (1, 1) :: repeat (1, 2) 32604 ++ w) 1); closearith.
  }
  (* S5: PX2A onto [14; 5] *)
  apply (hsteps_trans _ (HC [14; 5] 49 91 2
                         ((1, 1) :: (1, 2) :: (1, 2) :: repeat (1, 2) 257 ++ (3296, 2) :: (1, 1) :: repeat (1, 2) 7493 ++ (1911, 2) :: (1, 1) :: repeat (1, 2) 32604 ++ w) 1)).
  {
    apply (hsteps_step _ (HC [14; 5] 49 91 2
                   ((1, 1) :: (1, 2) :: (1, 2) :: repeat (1, 2) 257 ++ (3296, 2) :: (1, 1) :: repeat (1, 2) 7493 ++ (1911, 2) :: (1, 1) :: repeat (1, 2) 32604 ++ w) 1));
      [apply hPX2A | apply hsteps_refl].
  }
  (* S6: hGRIND 44 *)
  apply (hsteps_trans _ (HB [14; 5] 49 1 94
                         ((1, 1) :: (1, 2) :: (1, 2) :: repeat (1, 2) 257 ++ (3296, 2) :: (1, 1) :: repeat (1, 2) 7493 ++ (1911, 2) :: (1, 1) :: repeat (1, 2) 32604 ++ w) 1)).
  {
    apply (hGRIND 44 [14; 5] 49
           ((1, 1) :: (1, 2) :: (1, 2) :: repeat (1, 2) 257 ++ (3296, 2) :: (1, 1) :: repeat (1, 2) 7493 ++ (1911, 2) :: (1, 1) :: repeat (1, 2) 32604 ++ w) 1); closearith.
  }
  (* S7: POP (the (1, 1) pair) *)
  apply (hsteps_trans _ (HB [14; 5] 50 1 95
                         ((1, 2) :: (1, 2) :: repeat (1, 2) 257 ++ (3296, 2) :: (1, 1) :: repeat (1, 2) 7493 ++ (1911, 2) :: (1, 1) :: repeat (1, 2) 32604 ++ w) 1)).
  {
    apply (sPOP1 [14; 5] 49 94
           ((1, 2) :: (1, 2) :: repeat (1, 2) 257 ++ (3296, 2) :: (1, 1) :: repeat (1, 2) 7493 ++ (1911, 2) :: (1, 1) :: repeat (1, 2) 32604 ++ w) 1); closearith.
  }
  (* S8: pop12 259 *)
  apply (hsteps_trans _ (HB [14; 5] 309 1 613
                         ((3296, 2) :: (1, 1) :: repeat (1, 2) 7493 ++ (1911, 2) :: (1, 1) :: repeat (1, 2) 32604 ++ w) 1)).
  {
    replace ((1, 2) :: (1, 2) :: repeat (1, 2) 257 ++ (3296, 2) :: (1, 1) :: repeat (1, 2) 7493 ++ (1911, 2) :: (1, 1) :: repeat (1, 2) 32604 ++ w)
      with (repeat (1, 2) 259 ++ ((3296, 2) :: (1, 1) :: repeat (1, 2) 7493 ++ (1911, 2) :: (1, 1) :: repeat (1, 2) 32604 ++ w))
      by sec_eq.
    apply (pop12 259 [14; 5] 50 95
           ((3296, 2) :: (1, 1) :: repeat (1, 2) 7493 ++ (1911, 2) :: (1, 1) :: repeat (1, 2) 32604 ++ w) 1); closearith.
  }
  (* S9: front(3296) onto [309; 14; 5] *)
  apply (hsteps_trans _ (HC [309; 14; 5] 612 3 2
                         ((3290, 2) :: (1, 1) :: repeat (1, 2) 7493 ++ (1911, 2) :: (1, 1) :: repeat (1, 2) 32604 ++ w) 1)).
  {
    apply (hsteps_trans _ (HC [14; 5] 309 612 2
                           ((3294, 2) :: (1, 1) :: repeat (1, 2) 7493 ++ (1911, 2) :: (1, 1) :: repeat (1, 2) 32604 ++ w) 1)).
    {
      apply (sTUP [14; 5] 309 613 3296 2
             ((1, 1) :: repeat (1, 2) 7493 ++ (1911, 2) :: (1, 1) :: repeat (1, 2) 32604 ++ w) 1); closearith.
    }
    apply (hsteps_trans _ (HB [14; 5] 308 1 612
                           ((2, 2) :: (3294, 2) :: (1, 1) :: repeat (1, 2) 7493 ++ (1911, 2) :: (1, 1) :: repeat (1, 2) 32604 ++ w) 1)).
    {
      apply (hGRIND_even 304 [14; 5] 308
             ((3294, 2) :: (1, 1) :: repeat (1, 2) 7493 ++ (1911, 2) :: (1, 1) :: repeat (1, 2) 32604 ++ w) 1); closearith.
    }
    apply (hsteps_trans _ (HC [309; 14; 5] 612 1 2
                           ((3292, 2) :: (1, 1) :: repeat (1, 2) 7493 ++ (1911, 2) :: (1, 1) :: repeat (1, 2) 32604 ++ w) 1)).
    {
      replace ((3292, 2) :: (1, 1) :: repeat (1, 2) 7493 ++ (1911, 2) :: (1, 1) :: repeat (1, 2) 32604 ++ w)
        with ((3294 - 2, 2) :: (1, 1) :: repeat (1, 2) 7493 ++ (1911, 2) :: (1, 1) :: repeat (1, 2) 32604 ++ w)
        by sec_eq.
      apply (sTUP2_1 [14; 5] 308 611 3294
             ((1, 1) :: repeat (1, 2) 7493 ++ (1911, 2) :: (1, 1) :: repeat (1, 2) 32604 ++ w) 1); closearith.
    }
    apply (hsteps_trans _ (HB [309; 14; 5] 612 1 4
                           ((3292, 2) :: (1, 1) :: repeat (1, 2) 7493 ++ (1911, 2) :: (1, 1) :: repeat (1, 2) 32604 ++ w) 1)).
    {
      apply (sTDN [309; 14; 5] 612
             ((3292, 2) :: (1, 1) :: repeat (1, 2) 7493 ++ (1911, 2) :: (1, 1) :: repeat (1, 2) 32604 ++ w) 1).
    }
    replace ((3290, 2) :: (1, 1) :: repeat (1, 2) 7493 ++ (1911, 2) :: (1, 1) :: repeat (1, 2) 32604 ++ w)
      with ((3292 - 2, 2) :: (1, 1) :: repeat (1, 2) 7493 ++ (1911, 2) :: (1, 1) :: repeat (1, 2) 32604 ++ w)
      by sec_eq.
    apply (sTUP [309; 14; 5] 612 4 3292 2
           ((1, 1) :: repeat (1, 2) 7493 ++ (1911, 2) :: (1, 1) :: repeat (1, 2) 32604 ++ w) 1); closearith.
  }
  (* S10: DIPGRIND (612, 2066) *)
  apply (hsteps_trans _ (HC [309; 14; 5] 0 3 2
                         (repeat (1, 2) 612 ++ (2066, 2) :: (1, 1) :: repeat (1, 2) 7493 ++ (1911, 2) :: (1, 1) :: repeat (1, 2) 32604 ++ w) 1)).
  {
    apply (DIPGRIND 612 2066 [309; 14; 5]
           ((1, 1) :: repeat (1, 2) 7493 ++ (1911, 2) :: (1, 1) :: repeat (1, 2) 32604 ++ w) 1); closearith.
  }
  (* S11: PX2A + PUSH + TDN + TUP onto [5], pair (303, 2) *)
  apply (hsteps_trans _ (HC [5] 12 3 2
                         ((303, 2) :: (1, 1) :: repeat (1, 2) 614 ++ (2066, 2) :: (1, 1) :: repeat (1, 2) 7493 ++ (1911, 2) :: (1, 1) :: repeat (1, 2) 32604 ++ w) 1)).
  {
    apply (hsteps_trans _ (HC [5] 13 307 2
                           ((1, 1) :: (1, 2) :: (1, 2) :: repeat (1, 2) 612 ++ (2066, 2) :: (1, 1) :: repeat (1, 2) 7493 ++ (1911, 2) :: (1, 1) :: repeat (1, 2) 32604 ++ w) 1)).
    {
      apply (hsteps_step _ (HC [5] 13 307 2
                     ((1, 1) :: (1, 2) :: (1, 2) :: repeat (1, 2) 612 ++ (2066, 2) :: (1, 1) :: repeat (1, 2) 7493 ++ (1911, 2) :: (1, 1) :: repeat (1, 2) 32604 ++ w) 1));
        [apply hPX2A | apply hsteps_refl].
    }
    apply (hsteps_trans _ (HC [5] 12 1 2
                           ((305, 2) :: (1, 1) :: (1, 2) :: (1, 2) :: repeat (1, 2) 612 ++ (2066, 2) :: (1, 1) :: repeat (1, 2) 7493 ++ (1911, 2) :: (1, 1) :: repeat (1, 2) 32604 ++ w) 1)).
    {
      apply (sPUSH [5] 12 307
             ((1, 1) :: (1, 2) :: (1, 2) :: repeat (1, 2) 612 ++ (2066, 2) :: (1, 1) :: repeat (1, 2) 7493 ++ (1911, 2) :: (1, 1) :: repeat (1, 2) 32604 ++ w) 1); closearith.
    }
    apply (hsteps_trans _ (HB [5] 12 1 4
                           ((305, 2) :: (1, 1) :: (1, 2) :: (1, 2) :: repeat (1, 2) 612 ++ (2066, 2) :: (1, 1) :: repeat (1, 2) 7493 ++ (1911, 2) :: (1, 1) :: repeat (1, 2) 32604 ++ w) 1)).
    {
      apply (sTDN [5] 12
             ((305, 2) :: (1, 1) :: (1, 2) :: (1, 2) :: repeat (1, 2) 612 ++ (2066, 2) :: (1, 1) :: repeat (1, 2) 7493 ++ (1911, 2) :: (1, 1) :: repeat (1, 2) 32604 ++ w) 1).
    }
    replace ((303, 2) :: (1, 1) :: repeat (1, 2) 614 ++ (2066, 2) :: (1, 1) :: repeat (1, 2) 7493 ++ (1911, 2) :: (1, 1) :: repeat (1, 2) 32604 ++ w)
      with ((305 - 2, 2) :: (1, 1) :: (1, 2) :: (1, 2) :: repeat (1, 2) 612 ++ (2066, 2) :: (1, 1) :: repeat (1, 2) 7493 ++ (1911, 2) :: (1, 1) :: repeat (1, 2) 32604 ++ w)
      by sec_eq.
    apply (sTUP [5] 12 4 305 2
           ((1, 1) :: (1, 2) :: (1, 2) :: repeat (1, 2) 612 ++ (2066, 2) :: (1, 1) :: repeat (1, 2) 7493 ++ (1911, 2) :: (1, 1) :: repeat (1, 2) 32604 ++ w) 1); closearith.
  }
  (* S12: DIPGRIND (12, 279) *)
  apply (hsteps_trans _ (HC [5] 0 3 2
                         (repeat (1, 2) 12 ++ (279, 2) :: (1, 1) :: repeat (1, 2) 614 ++ (2066, 2) :: (1, 1) :: repeat (1, 2) 7493 ++ (1911, 2) :: (1, 1) :: repeat (1, 2) 32604 ++ w) 1)).
  {
    apply (DIPGRIND 12 279 [5]
           ((1, 1) :: repeat (1, 2) 614 ++ (2066, 2) :: (1, 1) :: repeat (1, 2) 7493 ++ (1911, 2) :: (1, 1) :: repeat (1, 2) 32604 ++ w) 1); closearith.
  }
  (* S13: PX2Bgen onto [0] *)
  apply (hsteps_trans _ (HB [0] 3 1 2
                         ((1, 2) :: (1, 1) :: (1, 2) :: (1, 2) :: repeat (1, 2) 12 ++ (279, 2) :: (1, 1) :: repeat (1, 2) 614 ++ (2066, 2) :: (1, 1) :: repeat (1, 2) 7493 ++ (1911, 2) :: (1, 1) :: repeat (1, 2) 32604 ++ w) 1)).
  {
    apply (hsteps_step _ (HB [0] 3 1 2
                   ((1, 2) :: (1, 1) :: (1, 2) :: (1, 2) :: repeat (1, 2) 12 ++ (279, 2) :: (1, 1) :: repeat (1, 2) 614 ++ (2066, 2) :: (1, 1) :: repeat (1, 2) 7493 ++ (1911, 2) :: (1, 1) :: repeat (1, 2) 32604 ++ w) 1));
      [apply hPX2Bgen | apply hsteps_refl].
  }
  (* S14: pop12 1 *)
  apply (hsteps_trans _ (HB [0] 4 1 4
                         ((1, 1) :: (1, 2) :: (1, 2) :: repeat (1, 2) 12 ++ (279, 2) :: (1, 1) :: repeat (1, 2) 614 ++ (2066, 2) :: (1, 1) :: repeat (1, 2) 7493 ++ (1911, 2) :: (1, 1) :: repeat (1, 2) 32604 ++ w) 1)).
  {
    replace ((1, 2) :: (1, 1) :: (1, 2) :: (1, 2) :: repeat (1, 2) 12 ++ (279, 2) :: (1, 1) :: repeat (1, 2) 614 ++ (2066, 2) :: (1, 1) :: repeat (1, 2) 7493 ++ (1911, 2) :: (1, 1) :: repeat (1, 2) 32604 ++ w)
      with (repeat (1, 2) 1 ++ ((1, 1) :: (1, 2) :: (1, 2) :: repeat (1, 2) 12 ++ (279, 2) :: (1, 1) :: repeat (1, 2) 614 ++ (2066, 2) :: (1, 1) :: repeat (1, 2) 7493 ++ (1911, 2) :: (1, 1) :: repeat (1, 2) 32604 ++ w))
      by sec_eq.
    apply (pop12 1 [0] 3 2
           ((1, 1) :: (1, 2) :: (1, 2) :: repeat (1, 2) 12 ++ (279, 2) :: (1, 1) :: repeat (1, 2) 614 ++ (2066, 2) :: (1, 1) :: repeat (1, 2) 7493 ++ (1911, 2) :: (1, 1) :: repeat (1, 2) 32604 ++ w) 1); closearith.
  }
  (* S15: POP *)
  apply (hsteps_trans _ (HB [0] 5 1 5
                         ((1, 2) :: (1, 2) :: repeat (1, 2) 12 ++ (279, 2) :: (1, 1) :: repeat (1, 2) 614 ++ (2066, 2) :: (1, 1) :: repeat (1, 2) 7493 ++ (1911, 2) :: (1, 1) :: repeat (1, 2) 32604 ++ w) 1)).
  {
    apply (sPOP1 [0] 4 4
           ((1, 2) :: (1, 2) :: repeat (1, 2) 12 ++ (279, 2) :: (1, 1) :: repeat (1, 2) 614 ++ (2066, 2) :: (1, 1) :: repeat (1, 2) 7493 ++ (1911, 2) :: (1, 1) :: repeat (1, 2) 32604 ++ w) 1); closearith.
  }
  (* S16: pop12 14 *)
  apply (hsteps_trans _ (HB [0] 19 1 33
                         ((279, 2) :: (1, 1) :: repeat (1, 2) 614 ++ (2066, 2) :: (1, 1) :: repeat (1, 2) 7493 ++ (1911, 2) :: (1, 1) :: repeat (1, 2) 32604 ++ w) 1)).
  {
    replace ((1, 2) :: (1, 2) :: repeat (1, 2) 12 ++ (279, 2) :: (1, 1) :: repeat (1, 2) 614 ++ (2066, 2) :: (1, 1) :: repeat (1, 2) 7493 ++ (1911, 2) :: (1, 1) :: repeat (1, 2) 32604 ++ w)
      with (repeat (1, 2) 14 ++ ((279, 2) :: (1, 1) :: repeat (1, 2) 614 ++ (2066, 2) :: (1, 1) :: repeat (1, 2) 7493 ++ (1911, 2) :: (1, 1) :: repeat (1, 2) 32604 ++ w))
      by sec_eq.
    apply (pop12 14 [0] 5 5
           ((279, 2) :: (1, 1) :: repeat (1, 2) 614 ++ (2066, 2) :: (1, 1) :: repeat (1, 2) 7493 ++ (1911, 2) :: (1, 1) :: repeat (1, 2) 32604 ++ w) 1); closearith.
  }
  (* S17: front(279) onto [19; 0] *)
  apply (hsteps_trans _ (HC [19; 0] 32 3 2
                         ((273, 2) :: (1, 1) :: repeat (1, 2) 614 ++ (2066, 2) :: (1, 1) :: repeat (1, 2) 7493 ++ (1911, 2) :: (1, 1) :: repeat (1, 2) 32604 ++ w) 1)).
  {
    apply (hsteps_trans _ (HC [0] 19 32 2
                           ((277, 2) :: (1, 1) :: repeat (1, 2) 614 ++ (2066, 2) :: (1, 1) :: repeat (1, 2) 7493 ++ (1911, 2) :: (1, 1) :: repeat (1, 2) 32604 ++ w) 1)).
    {
      apply (sTUP [0] 19 33 279 2
             ((1, 1) :: repeat (1, 2) 614 ++ (2066, 2) :: (1, 1) :: repeat (1, 2) 7493 ++ (1911, 2) :: (1, 1) :: repeat (1, 2) 32604 ++ w) 1); closearith.
    }
    apply (hsteps_trans _ (HB [0] 18 1 32
                           ((2, 2) :: (277, 2) :: (1, 1) :: repeat (1, 2) 614 ++ (2066, 2) :: (1, 1) :: repeat (1, 2) 7493 ++ (1911, 2) :: (1, 1) :: repeat (1, 2) 32604 ++ w) 1)).
    {
      apply (hGRIND_even 14 [0] 18
             ((277, 2) :: (1, 1) :: repeat (1, 2) 614 ++ (2066, 2) :: (1, 1) :: repeat (1, 2) 7493 ++ (1911, 2) :: (1, 1) :: repeat (1, 2) 32604 ++ w) 1); closearith.
    }
    apply (hsteps_trans _ (HC [19; 0] 32 1 2
                           ((275, 2) :: (1, 1) :: repeat (1, 2) 614 ++ (2066, 2) :: (1, 1) :: repeat (1, 2) 7493 ++ (1911, 2) :: (1, 1) :: repeat (1, 2) 32604 ++ w) 1)).
    {
      replace ((275, 2) :: (1, 1) :: repeat (1, 2) 614 ++ (2066, 2) :: (1, 1) :: repeat (1, 2) 7493 ++ (1911, 2) :: (1, 1) :: repeat (1, 2) 32604 ++ w)
        with ((277 - 2, 2) :: (1, 1) :: repeat (1, 2) 614 ++ (2066, 2) :: (1, 1) :: repeat (1, 2) 7493 ++ (1911, 2) :: (1, 1) :: repeat (1, 2) 32604 ++ w)
        by sec_eq.
      apply (sTUP2_1 [0] 18 31 277
             ((1, 1) :: repeat (1, 2) 614 ++ (2066, 2) :: (1, 1) :: repeat (1, 2) 7493 ++ (1911, 2) :: (1, 1) :: repeat (1, 2) 32604 ++ w) 1); closearith.
    }
    apply (hsteps_trans _ (HB [19; 0] 32 1 4
                           ((275, 2) :: (1, 1) :: repeat (1, 2) 614 ++ (2066, 2) :: (1, 1) :: repeat (1, 2) 7493 ++ (1911, 2) :: (1, 1) :: repeat (1, 2) 32604 ++ w) 1)).
    {
      apply (sTDN [19; 0] 32
             ((275, 2) :: (1, 1) :: repeat (1, 2) 614 ++ (2066, 2) :: (1, 1) :: repeat (1, 2) 7493 ++ (1911, 2) :: (1, 1) :: repeat (1, 2) 32604 ++ w) 1).
    }
    replace ((273, 2) :: (1, 1) :: repeat (1, 2) 614 ++ (2066, 2) :: (1, 1) :: repeat (1, 2) 7493 ++ (1911, 2) :: (1, 1) :: repeat (1, 2) 32604 ++ w)
      with ((275 - 2, 2) :: (1, 1) :: repeat (1, 2) 614 ++ (2066, 2) :: (1, 1) :: repeat (1, 2) 7493 ++ (1911, 2) :: (1, 1) :: repeat (1, 2) 32604 ++ w)
      by sec_eq.
    apply (sTUP [19; 0] 32 4 275 2
           ((1, 1) :: repeat (1, 2) 614 ++ (2066, 2) :: (1, 1) :: repeat (1, 2) 7493 ++ (1911, 2) :: (1, 1) :: repeat (1, 2) 32604 ++ w) 1); closearith.
  }
  (* S18: DIPGRIND (32, 209) *)
  apply (hsteps_trans _ (HC [19; 0] 0 3 2
                         (repeat (1, 2) 32 ++ (209, 2) :: (1, 1) :: repeat (1, 2) 614 ++ (2066, 2) :: (1, 1) :: repeat (1, 2) 7493 ++ (1911, 2) :: (1, 1) :: repeat (1, 2) 32604 ++ w) 1)).
  {
    apply (DIPGRIND 32 209 [19; 0]
           ((1, 1) :: repeat (1, 2) 614 ++ (2066, 2) :: (1, 1) :: repeat (1, 2) 7493 ++ (1911, 2) :: (1, 1) :: repeat (1, 2) 32604 ++ w) 1); closearith.
  }
  (* S19: PX2A0 + TUP + TDN + TUP at [0], pair (11, 2) *)
  apply (hsteps_trans _ (HC [0] 3 3 2
                         ((11, 2) :: (1, 1) :: repeat (1, 2) 34 ++ (209, 2) :: (1, 1) :: repeat (1, 2) 614 ++ (2066, 2) :: (1, 1) :: repeat (1, 2) 7493 ++ (1911, 2) :: (1, 1) :: repeat (1, 2) 32604 ++ w) 1)).
  {
    apply (hsteps_trans _ (HB [0] 3 1 2
                           ((15, 2) :: (1, 1) :: (1, 2) :: (1, 2) :: repeat (1, 2) 32 ++ (209, 2) :: (1, 1) :: repeat (1, 2) 614 ++ (2066, 2) :: (1, 1) :: repeat (1, 2) 7493 ++ (1911, 2) :: (1, 1) :: repeat (1, 2) 32604 ++ w) 1)).
    {
      apply (hsteps_step _ (HB [0] 3 1 2
                     ((15, 2) :: (1, 1) :: (1, 2) :: (1, 2) :: repeat (1, 2) 32 ++ (209, 2) :: (1, 1) :: repeat (1, 2) 614 ++ (2066, 2) :: (1, 1) :: repeat (1, 2) 7493 ++ (1911, 2) :: (1, 1) :: repeat (1, 2) 32604 ++ w) 1));
        [apply hPX2A0 | apply hsteps_refl].
    }
    apply (hsteps_trans _ (HC [0] 3 1 2
                           ((13, 2) :: (1, 1) :: (1, 2) :: (1, 2) :: repeat (1, 2) 32 ++ (209, 2) :: (1, 1) :: repeat (1, 2) 614 ++ (2066, 2) :: (1, 1) :: repeat (1, 2) 7493 ++ (1911, 2) :: (1, 1) :: repeat (1, 2) 32604 ++ w) 1)).
    {
      replace ((13, 2) :: (1, 1) :: (1, 2) :: (1, 2) :: repeat (1, 2) 32 ++ (209, 2) :: (1, 1) :: repeat (1, 2) 614 ++ (2066, 2) :: (1, 1) :: repeat (1, 2) 7493 ++ (1911, 2) :: (1, 1) :: repeat (1, 2) 32604 ++ w)
        with ((15 - 2, 2) :: (1, 1) :: (1, 2) :: (1, 2) :: repeat (1, 2) 32 ++ (209, 2) :: (1, 1) :: repeat (1, 2) 614 ++ (2066, 2) :: (1, 1) :: repeat (1, 2) 7493 ++ (1911, 2) :: (1, 1) :: repeat (1, 2) 32604 ++ w)
        by sec_eq.
      apply (sTUP [0] 3 2 15 2
             ((1, 1) :: (1, 2) :: (1, 2) :: repeat (1, 2) 32 ++ (209, 2) :: (1, 1) :: repeat (1, 2) 614 ++ (2066, 2) :: (1, 1) :: repeat (1, 2) 7493 ++ (1911, 2) :: (1, 1) :: repeat (1, 2) 32604 ++ w) 1); closearith.
    }
    apply (hsteps_trans _ (HB [0] 3 1 4
                           ((13, 2) :: (1, 1) :: (1, 2) :: (1, 2) :: repeat (1, 2) 32 ++ (209, 2) :: (1, 1) :: repeat (1, 2) 614 ++ (2066, 2) :: (1, 1) :: repeat (1, 2) 7493 ++ (1911, 2) :: (1, 1) :: repeat (1, 2) 32604 ++ w) 1)).
    {
      apply (sTDN [0] 3
             ((13, 2) :: (1, 1) :: (1, 2) :: (1, 2) :: repeat (1, 2) 32 ++ (209, 2) :: (1, 1) :: repeat (1, 2) 614 ++ (2066, 2) :: (1, 1) :: repeat (1, 2) 7493 ++ (1911, 2) :: (1, 1) :: repeat (1, 2) 32604 ++ w) 1).
    }
    replace ((11, 2) :: (1, 1) :: repeat (1, 2) 34 ++ (209, 2) :: (1, 1) :: repeat (1, 2) 614 ++ (2066, 2) :: (1, 1) :: repeat (1, 2) 7493 ++ (1911, 2) :: (1, 1) :: repeat (1, 2) 32604 ++ w)
      with ((13 - 2, 2) :: (1, 1) :: (1, 2) :: (1, 2) :: repeat (1, 2) 32 ++ (209, 2) :: (1, 1) :: repeat (1, 2) 614 ++ (2066, 2) :: (1, 1) :: repeat (1, 2) 7493 ++ (1911, 2) :: (1, 1) :: repeat (1, 2) 32604 ++ w)
      by sec_eq.
    apply (sTUP [0] 3 4 13 2
           ((1, 1) :: (1, 2) :: (1, 2) :: repeat (1, 2) 32 ++ (209, 2) :: (1, 1) :: repeat (1, 2) 614 ++ (2066, 2) :: (1, 1) :: repeat (1, 2) 7493 ++ (1911, 2) :: (1, 1) :: repeat (1, 2) 32604 ++ w) 1); closearith.
  }
  (* S20: DIPGRIND (3, 5) *)
  apply (hsteps_trans _ (HC [0] 0 3 2
                         (repeat (1, 2) 3 ++ (5, 2) :: (1, 1) :: repeat (1, 2) 34 ++ (209, 2) :: (1, 1) :: repeat (1, 2) 614 ++ (2066, 2) :: (1, 1) :: repeat (1, 2) 7493 ++ (1911, 2) :: (1, 1) :: repeat (1, 2) 32604 ++ w) 1)).
  {
    apply (DIPGRIND 3 5 [0]
           ((1, 1) :: repeat (1, 2) 34 ++ (209, 2) :: (1, 1) :: repeat (1, 2) 614 ++ (2066, 2) :: (1, 1) :: repeat (1, 2) 7493 ++ (1911, 2) :: (1, 1) :: repeat (1, 2) 32604 ++ w) 1); closearith.
  }
  (* S21: PX2B0 at [] *)
  apply (hsteps_trans _ (HB [] 0 1 5
                         (repeat (1, 2) 4 ++ (5, 2) :: (1, 1) :: repeat (1, 2) 34 ++ (209, 2) :: (1, 1) :: repeat (1, 2) 614 ++ (2066, 2) :: (1, 1) :: repeat (1, 2) 7493 ++ (1911, 2) :: (1, 1) :: repeat (1, 2) 32604 ++ w) 1)).
  {
    apply (hsteps_step _ (HB [] 0 1 5
                   (repeat (1, 2) 4 ++ (5, 2) :: (1, 1) :: repeat (1, 2) 34 ++ (209, 2) :: (1, 1) :: repeat (1, 2) 614 ++ (2066, 2) :: (1, 1) :: repeat (1, 2) 7493 ++ (1911, 2) :: (1, 1) :: repeat (1, 2) 32604 ++ w) 1));
      [apply hPX2B0 | apply hsteps_refl].
  }
  (* S22: pop12 4 *)
  apply (hsteps_trans _ (HB [] 4 1 13
                         ((5, 2) :: (1, 1) :: repeat (1, 2) 34 ++ (209, 2) :: (1, 1) :: repeat (1, 2) 614 ++ (2066, 2) :: (1, 1) :: repeat (1, 2) 7493 ++ (1911, 2) :: (1, 1) :: repeat (1, 2) 32604 ++ w) 1)).
  {
    apply (pop12 4 [] 0 5
           ((5, 2) :: (1, 1) :: repeat (1, 2) 34 ++ (209, 2) :: (1, 1) :: repeat (1, 2) 614 ++ (2066, 2) :: (1, 1) :: repeat (1, 2) 7493 ++ (1911, 2) :: (1, 1) :: repeat (1, 2) 32604 ++ w) 1); closearith.
  }
  (* S23: bottom front (TUP + PUSH + TDN + TUP) at [], pair (8, 2) over (3, 2) *)
  apply (hsteps_trans _ (HC [] 3 3 2
                         ((8, 2) :: (3, 2) :: (1, 1) :: repeat (1, 2) 34 ++ (209, 2) :: (1, 1) :: repeat (1, 2) 614 ++ (2066, 2) :: (1, 1) :: repeat (1, 2) 7493 ++ (1911, 2) :: (1, 1) :: repeat (1, 2) 32604 ++ w) 1)).
  {
    apply (hsteps_trans _ (HC [] 4 12 2
                           ((3, 2) :: (1, 1) :: repeat (1, 2) 34 ++ (209, 2) :: (1, 1) :: repeat (1, 2) 614 ++ (2066, 2) :: (1, 1) :: repeat (1, 2) 7493 ++ (1911, 2) :: (1, 1) :: repeat (1, 2) 32604 ++ w) 1)).
    {
      apply (sTUP [] 4 13 5 2
             ((1, 1) :: repeat (1, 2) 34 ++ (209, 2) :: (1, 1) :: repeat (1, 2) 614 ++ (2066, 2) :: (1, 1) :: repeat (1, 2) 7493 ++ (1911, 2) :: (1, 1) :: repeat (1, 2) 32604 ++ w) 1); closearith.
    }
    apply (hsteps_trans _ (HC [] 3 1 2
                           ((10, 2) :: (3, 2) :: (1, 1) :: repeat (1, 2) 34 ++ (209, 2) :: (1, 1) :: repeat (1, 2) 614 ++ (2066, 2) :: (1, 1) :: repeat (1, 2) 7493 ++ (1911, 2) :: (1, 1) :: repeat (1, 2) 32604 ++ w) 1)).
    {
      apply (sPUSH [] 3 12
             ((3, 2) :: (1, 1) :: repeat (1, 2) 34 ++ (209, 2) :: (1, 1) :: repeat (1, 2) 614 ++ (2066, 2) :: (1, 1) :: repeat (1, 2) 7493 ++ (1911, 2) :: (1, 1) :: repeat (1, 2) 32604 ++ w) 1); closearith.
    }
    apply (hsteps_trans _ (HB [] 3 1 4
                           ((10, 2) :: (3, 2) :: (1, 1) :: repeat (1, 2) 34 ++ (209, 2) :: (1, 1) :: repeat (1, 2) 614 ++ (2066, 2) :: (1, 1) :: repeat (1, 2) 7493 ++ (1911, 2) :: (1, 1) :: repeat (1, 2) 32604 ++ w) 1)).
    {
      apply (sTDN [] 3
             ((10, 2) :: (3, 2) :: (1, 1) :: repeat (1, 2) 34 ++ (209, 2) :: (1, 1) :: repeat (1, 2) 614 ++ (2066, 2) :: (1, 1) :: repeat (1, 2) 7493 ++ (1911, 2) :: (1, 1) :: repeat (1, 2) 32604 ++ w) 1).
    }
    replace ((8, 2) :: (3, 2) :: (1, 1) :: repeat (1, 2) 34 ++ (209, 2) :: (1, 1) :: repeat (1, 2) 614 ++ (2066, 2) :: (1, 1) :: repeat (1, 2) 7493 ++ (1911, 2) :: (1, 1) :: repeat (1, 2) 32604 ++ w)
      with ((10 - 2, 2) :: (3, 2) :: (1, 1) :: repeat (1, 2) 34 ++ (209, 2) :: (1, 1) :: repeat (1, 2) 614 ++ (2066, 2) :: (1, 1) :: repeat (1, 2) 7493 ++ (1911, 2) :: (1, 1) :: repeat (1, 2) 32604 ++ w)
      by sec_eq.
    apply (sTUP [] 3 4 10 2
           ((3, 2) :: (1, 1) :: repeat (1, 2) 34 ++ (209, 2) :: (1, 1) :: repeat (1, 2) 614 ++ (2066, 2) :: (1, 1) :: repeat (1, 2) 7493 ++ (1911, 2) :: (1, 1) :: repeat (1, 2) 32604 ++ w) 1); closearith.
  }
  (* S24: DIPGRIND (3, 2) *)
  apply (hsteps_trans _ (HC [] 0 3 2
                         (repeat (1, 2) 3 ++ (2, 2) :: (3, 2) :: (1, 1) :: repeat (1, 2) 34 ++ (209, 2) :: (1, 1) :: repeat (1, 2) 614 ++ (2066, 2) :: (1, 1) :: repeat (1, 2) 7493 ++ (1911, 2) :: (1, 1) :: repeat (1, 2) 32604 ++ w) 1)).
  {
    apply (DIPGRIND 3 2 []
           ((3, 2) :: (1, 1) :: repeat (1, 2) 34 ++ (209, 2) :: (1, 1) :: repeat (1, 2) 614 ++ (2066, 2) :: (1, 1) :: repeat (1, 2) 7493 ++ (1911, 2) :: (1, 1) :: repeat (1, 2) 32604 ++ w) 1); closearith.
  }
  (* S25: PUSHX *)
  apply (hsteps_trans _ (HB [] 1 1 7
                         (repeat (1, 2) 3 ++ (2, 2) :: (3, 2) :: (1, 1) :: repeat (1, 2) 34 ++ (209, 2) :: (1, 1) :: repeat (1, 2) 614 ++ (2066, 2) :: (1, 1) :: repeat (1, 2) 7493 ++ (1911, 2) :: (1, 1) :: repeat (1, 2) 32604 ++ w) 1)).
  {
    apply (hsteps_step _ (HB [] 1 1 7
                   (repeat (1, 2) 3 ++ (2, 2) :: (3, 2) :: (1, 1) :: repeat (1, 2) 34 ++ (209, 2) :: (1, 1) :: repeat (1, 2) 614 ++ (2066, 2) :: (1, 1) :: repeat (1, 2) 7493 ++ (1911, 2) :: (1, 1) :: repeat (1, 2) 32604 ++ w) 1));
      [apply hPUSHX | apply hsteps_refl].
  }
  (* S26: pop12 3 *)
  apply (hsteps_trans _ (HB [] 4 1 13
                         ((2, 2) :: (3, 2) :: (1, 1) :: repeat (1, 2) 34 ++ (209, 2) :: (1, 1) :: repeat (1, 2) 614 ++ (2066, 2) :: (1, 1) :: repeat (1, 2) 7493 ++ (1911, 2) :: (1, 1) :: repeat (1, 2) 32604 ++ w) 1)).
  {
    apply (pop12 3 [] 1 7
           ((2, 2) :: (3, 2) :: (1, 1) :: repeat (1, 2) 34 ++ (209, 2) :: (1, 1) :: repeat (1, 2) 614 ++ (2066, 2) :: (1, 1) :: repeat (1, 2) 7493 ++ (1911, 2) :: (1, 1) :: repeat (1, 2) 32604 ++ w) 1); closearith.
  }
  (* S27: TUP2_1 + TDN regrowth onto [5] *)
  apply (hsteps_trans _ (HB [5] 13 1 4
                         ((1, 2) :: (1, 1) :: repeat (1, 2) 34 ++ (209, 2) :: (1, 1) :: repeat (1, 2) 614 ++ (2066, 2) :: (1, 1) :: repeat (1, 2) 7493 ++ (1911, 2) :: (1, 1) :: repeat (1, 2) 32604 ++ w) 1)).
  {
    apply (hsteps_trans _ (HC [5] 13 1 2
                           ((1, 2) :: (1, 1) :: repeat (1, 2) 34 ++ (209, 2) :: (1, 1) :: repeat (1, 2) 614 ++ (2066, 2) :: (1, 1) :: repeat (1, 2) 7493 ++ (1911, 2) :: (1, 1) :: repeat (1, 2) 32604 ++ w) 1)).
    {
      replace ((1, 2) :: (1, 1) :: repeat (1, 2) 34 ++ (209, 2) :: (1, 1) :: repeat (1, 2) 614 ++ (2066, 2) :: (1, 1) :: repeat (1, 2) 7493 ++ (1911, 2) :: (1, 1) :: repeat (1, 2) 32604 ++ w)
        with ((3 - 2, 2) :: (1, 1) :: repeat (1, 2) 34 ++ (209, 2) :: (1, 1) :: repeat (1, 2) 614 ++ (2066, 2) :: (1, 1) :: repeat (1, 2) 7493 ++ (1911, 2) :: (1, 1) :: repeat (1, 2) 32604 ++ w)
        by sec_eq.
      apply (sTUP2_1 [] 4 12 3
             ((1, 1) :: repeat (1, 2) 34 ++ (209, 2) :: (1, 1) :: repeat (1, 2) 614 ++ (2066, 2) :: (1, 1) :: repeat (1, 2) 7493 ++ (1911, 2) :: (1, 1) :: repeat (1, 2) 32604 ++ w) 1); closearith.
    }
    apply (sTDN [5] 13
           ((1, 2) :: (1, 1) :: repeat (1, 2) 34 ++ (209, 2) :: (1, 1) :: repeat (1, 2) 614 ++ (2066, 2) :: (1, 1) :: repeat (1, 2) 7493 ++ (1911, 2) :: (1, 1) :: repeat (1, 2) 32604 ++ w) 1).
  }
  (* S28: pop12 1 *)
  apply (hsteps_trans _ (HB [5] 14 1 6
                         ((1, 1) :: repeat (1, 2) 34 ++ (209, 2) :: (1, 1) :: repeat (1, 2) 614 ++ (2066, 2) :: (1, 1) :: repeat (1, 2) 7493 ++ (1911, 2) :: (1, 1) :: repeat (1, 2) 32604 ++ w) 1)).
  {
    replace ((1, 2) :: (1, 1) :: repeat (1, 2) 34 ++ (209, 2) :: (1, 1) :: repeat (1, 2) 614 ++ (2066, 2) :: (1, 1) :: repeat (1, 2) 7493 ++ (1911, 2) :: (1, 1) :: repeat (1, 2) 32604 ++ w)
      with (repeat (1, 2) 1 ++ ((1, 1) :: repeat (1, 2) 34 ++ (209, 2) :: (1, 1) :: repeat (1, 2) 614 ++ (2066, 2) :: (1, 1) :: repeat (1, 2) 7493 ++ (1911, 2) :: (1, 1) :: repeat (1, 2) 32604 ++ w))
      by sec_eq.
    apply (pop12 1 [5] 13 4
           ((1, 1) :: repeat (1, 2) 34 ++ (209, 2) :: (1, 1) :: repeat (1, 2) 614 ++ (2066, 2) :: (1, 1) :: repeat (1, 2) 7493 ++ (1911, 2) :: (1, 1) :: repeat (1, 2) 32604 ++ w) 1); closearith.
  }
  (* S29: POP *)
  apply (hsteps_trans _ (HB [5] 15 1 7
                         (repeat (1, 2) 34 ++ (209, 2) :: (1, 1) :: repeat (1, 2) 614 ++ (2066, 2) :: (1, 1) :: repeat (1, 2) 7493 ++ (1911, 2) :: (1, 1) :: repeat (1, 2) 32604 ++ w) 1)).
  {
    apply (sPOP1 [5] 14 6
           (repeat (1, 2) 34 ++ (209, 2) :: (1, 1) :: repeat (1, 2) 614 ++ (2066, 2) :: (1, 1) :: repeat (1, 2) 7493 ++ (1911, 2) :: (1, 1) :: repeat (1, 2) 32604 ++ w) 1); closearith.
  }
  (* S30: pop12 34 *)
  apply (hsteps_trans _ (HB [5] 49 1 75
                         ((209, 2) :: (1, 1) :: repeat (1, 2) 614 ++ (2066, 2) :: (1, 1) :: repeat (1, 2) 7493 ++ (1911, 2) :: (1, 1) :: repeat (1, 2) 32604 ++ w) 1)).
  {
    apply (pop12 34 [5] 15 7
           ((209, 2) :: (1, 1) :: repeat (1, 2) 614 ++ (2066, 2) :: (1, 1) :: repeat (1, 2) 7493 ++ (1911, 2) :: (1, 1) :: repeat (1, 2) 32604 ++ w) 1); closearith.
  }
  (* S31: front(209) onto [49; 5] *)
  apply (hsteps_trans _ (HC [49; 5] 74 3 2
                         ((203, 2) :: (1, 1) :: repeat (1, 2) 614 ++ (2066, 2) :: (1, 1) :: repeat (1, 2) 7493 ++ (1911, 2) :: (1, 1) :: repeat (1, 2) 32604 ++ w) 1)).
  {
    apply (hsteps_trans _ (HC [5] 49 74 2
                           ((207, 2) :: (1, 1) :: repeat (1, 2) 614 ++ (2066, 2) :: (1, 1) :: repeat (1, 2) 7493 ++ (1911, 2) :: (1, 1) :: repeat (1, 2) 32604 ++ w) 1)).
    {
      apply (sTUP [5] 49 75 209 2
             ((1, 1) :: repeat (1, 2) 614 ++ (2066, 2) :: (1, 1) :: repeat (1, 2) 7493 ++ (1911, 2) :: (1, 1) :: repeat (1, 2) 32604 ++ w) 1); closearith.
    }
    apply (hsteps_trans _ (HB [5] 48 1 74
                           ((2, 2) :: (207, 2) :: (1, 1) :: repeat (1, 2) 614 ++ (2066, 2) :: (1, 1) :: repeat (1, 2) 7493 ++ (1911, 2) :: (1, 1) :: repeat (1, 2) 32604 ++ w) 1)).
    {
      apply (hGRIND_even 35 [5] 48
             ((207, 2) :: (1, 1) :: repeat (1, 2) 614 ++ (2066, 2) :: (1, 1) :: repeat (1, 2) 7493 ++ (1911, 2) :: (1, 1) :: repeat (1, 2) 32604 ++ w) 1); closearith.
    }
    apply (hsteps_trans _ (HC [49; 5] 74 1 2
                           ((205, 2) :: (1, 1) :: repeat (1, 2) 614 ++ (2066, 2) :: (1, 1) :: repeat (1, 2) 7493 ++ (1911, 2) :: (1, 1) :: repeat (1, 2) 32604 ++ w) 1)).
    {
      replace ((205, 2) :: (1, 1) :: repeat (1, 2) 614 ++ (2066, 2) :: (1, 1) :: repeat (1, 2) 7493 ++ (1911, 2) :: (1, 1) :: repeat (1, 2) 32604 ++ w)
        with ((207 - 2, 2) :: (1, 1) :: repeat (1, 2) 614 ++ (2066, 2) :: (1, 1) :: repeat (1, 2) 7493 ++ (1911, 2) :: (1, 1) :: repeat (1, 2) 32604 ++ w)
        by sec_eq.
      apply (sTUP2_1 [5] 48 73 207
             ((1, 1) :: repeat (1, 2) 614 ++ (2066, 2) :: (1, 1) :: repeat (1, 2) 7493 ++ (1911, 2) :: (1, 1) :: repeat (1, 2) 32604 ++ w) 1); closearith.
    }
    apply (hsteps_trans _ (HB [49; 5] 74 1 4
                           ((205, 2) :: (1, 1) :: repeat (1, 2) 614 ++ (2066, 2) :: (1, 1) :: repeat (1, 2) 7493 ++ (1911, 2) :: (1, 1) :: repeat (1, 2) 32604 ++ w) 1)).
    {
      apply (sTDN [49; 5] 74
             ((205, 2) :: (1, 1) :: repeat (1, 2) 614 ++ (2066, 2) :: (1, 1) :: repeat (1, 2) 7493 ++ (1911, 2) :: (1, 1) :: repeat (1, 2) 32604 ++ w) 1).
    }
    replace ((203, 2) :: (1, 1) :: repeat (1, 2) 614 ++ (2066, 2) :: (1, 1) :: repeat (1, 2) 7493 ++ (1911, 2) :: (1, 1) :: repeat (1, 2) 32604 ++ w)
      with ((205 - 2, 2) :: (1, 1) :: repeat (1, 2) 614 ++ (2066, 2) :: (1, 1) :: repeat (1, 2) 7493 ++ (1911, 2) :: (1, 1) :: repeat (1, 2) 32604 ++ w)
      by sec_eq.
    apply (sTUP [49; 5] 74 4 205 2
           ((1, 1) :: repeat (1, 2) 614 ++ (2066, 2) :: (1, 1) :: repeat (1, 2) 7493 ++ (1911, 2) :: (1, 1) :: repeat (1, 2) 32604 ++ w) 1); closearith.
  }
  (* S32: DIPGRIND (74, 55) *)
  apply (hsteps_trans _ (HC [49; 5] 0 3 2
                         (repeat (1, 2) 74 ++ (55, 2) :: (1, 1) :: repeat (1, 2) 614 ++ (2066, 2) :: (1, 1) :: repeat (1, 2) 7493 ++ (1911, 2) :: (1, 1) :: repeat (1, 2) 32604 ++ w) 1)).
  {
    apply (DIPGRIND 74 55 [49; 5]
           ((1, 1) :: repeat (1, 2) 614 ++ (2066, 2) :: (1, 1) :: repeat (1, 2) 7493 ++ (1911, 2) :: (1, 1) :: repeat (1, 2) 32604 ++ w) 1); closearith.
  }
  (* S33: PX2A + PUSH + TDN + TUP onto [], pair (43, 2) *)
  apply (hsteps_trans _ (HC [] 3 3 2
                         ((43, 2) :: (1, 1) :: repeat (1, 2) 76 ++ (55, 2) :: (1, 1) :: repeat (1, 2) 614 ++ (2066, 2) :: (1, 1) :: repeat (1, 2) 7493 ++ (1911, 2) :: (1, 1) :: repeat (1, 2) 32604 ++ w) 1)).
  {
    apply (hsteps_trans _ (HC [] 4 47 2
                           ((1, 1) :: (1, 2) :: (1, 2) :: repeat (1, 2) 74 ++ (55, 2) :: (1, 1) :: repeat (1, 2) 614 ++ (2066, 2) :: (1, 1) :: repeat (1, 2) 7493 ++ (1911, 2) :: (1, 1) :: repeat (1, 2) 32604 ++ w) 1)).
    {
      apply (hsteps_step _ (HC [] 4 47 2
                     ((1, 1) :: (1, 2) :: (1, 2) :: repeat (1, 2) 74 ++ (55, 2) :: (1, 1) :: repeat (1, 2) 614 ++ (2066, 2) :: (1, 1) :: repeat (1, 2) 7493 ++ (1911, 2) :: (1, 1) :: repeat (1, 2) 32604 ++ w) 1));
        [apply hPX2A | apply hsteps_refl].
    }
    apply (hsteps_trans _ (HC [] 3 1 2
                           ((45, 2) :: (1, 1) :: (1, 2) :: (1, 2) :: repeat (1, 2) 74 ++ (55, 2) :: (1, 1) :: repeat (1, 2) 614 ++ (2066, 2) :: (1, 1) :: repeat (1, 2) 7493 ++ (1911, 2) :: (1, 1) :: repeat (1, 2) 32604 ++ w) 1)).
    {
      apply (sPUSH [] 3 47
             ((1, 1) :: (1, 2) :: (1, 2) :: repeat (1, 2) 74 ++ (55, 2) :: (1, 1) :: repeat (1, 2) 614 ++ (2066, 2) :: (1, 1) :: repeat (1, 2) 7493 ++ (1911, 2) :: (1, 1) :: repeat (1, 2) 32604 ++ w) 1); closearith.
    }
    apply (hsteps_trans _ (HB [] 3 1 4
                           ((45, 2) :: (1, 1) :: (1, 2) :: (1, 2) :: repeat (1, 2) 74 ++ (55, 2) :: (1, 1) :: repeat (1, 2) 614 ++ (2066, 2) :: (1, 1) :: repeat (1, 2) 7493 ++ (1911, 2) :: (1, 1) :: repeat (1, 2) 32604 ++ w) 1)).
    {
      apply (sTDN [] 3
             ((45, 2) :: (1, 1) :: (1, 2) :: (1, 2) :: repeat (1, 2) 74 ++ (55, 2) :: (1, 1) :: repeat (1, 2) 614 ++ (2066, 2) :: (1, 1) :: repeat (1, 2) 7493 ++ (1911, 2) :: (1, 1) :: repeat (1, 2) 32604 ++ w) 1).
    }
    replace ((43, 2) :: (1, 1) :: repeat (1, 2) 76 ++ (55, 2) :: (1, 1) :: repeat (1, 2) 614 ++ (2066, 2) :: (1, 1) :: repeat (1, 2) 7493 ++ (1911, 2) :: (1, 1) :: repeat (1, 2) 32604 ++ w)
      with ((45 - 2, 2) :: (1, 1) :: (1, 2) :: (1, 2) :: repeat (1, 2) 74 ++ (55, 2) :: (1, 1) :: repeat (1, 2) 614 ++ (2066, 2) :: (1, 1) :: repeat (1, 2) 7493 ++ (1911, 2) :: (1, 1) :: repeat (1, 2) 32604 ++ w)
      by sec_eq.
    apply (sTUP [] 3 4 45 2
           ((1, 1) :: (1, 2) :: (1, 2) :: repeat (1, 2) 74 ++ (55, 2) :: (1, 1) :: repeat (1, 2) 614 ++ (2066, 2) :: (1, 1) :: repeat (1, 2) 7493 ++ (1911, 2) :: (1, 1) :: repeat (1, 2) 32604 ++ w) 1); closearith.
  }
  (* S34: DIPGRIND (3, 37) *)
  apply (hsteps_trans _ (HC [] 0 3 2
                         (repeat (1, 2) 3 ++ (37, 2) :: (1, 1) :: repeat (1, 2) 76 ++ (55, 2) :: (1, 1) :: repeat (1, 2) 614 ++ (2066, 2) :: (1, 1) :: repeat (1, 2) 7493 ++ (1911, 2) :: (1, 1) :: repeat (1, 2) 32604 ++ w) 1)).
  {
    apply (DIPGRIND 3 37 []
           ((1, 1) :: repeat (1, 2) 76 ++ (55, 2) :: (1, 1) :: repeat (1, 2) 614 ++ (2066, 2) :: (1, 1) :: repeat (1, 2) 7493 ++ (1911, 2) :: (1, 1) :: repeat (1, 2) 32604 ++ w) 1); closearith.
  }
  (* S35: PUSHX *)
  apply (hsteps_trans _ (HB [] 1 1 7
                         (repeat (1, 2) 3 ++ (37, 2) :: (1, 1) :: repeat (1, 2) 76 ++ (55, 2) :: (1, 1) :: repeat (1, 2) 614 ++ (2066, 2) :: (1, 1) :: repeat (1, 2) 7493 ++ (1911, 2) :: (1, 1) :: repeat (1, 2) 32604 ++ w) 1)).
  {
    apply (hsteps_step _ (HB [] 1 1 7
                   (repeat (1, 2) 3 ++ (37, 2) :: (1, 1) :: repeat (1, 2) 76 ++ (55, 2) :: (1, 1) :: repeat (1, 2) 614 ++ (2066, 2) :: (1, 1) :: repeat (1, 2) 7493 ++ (1911, 2) :: (1, 1) :: repeat (1, 2) 32604 ++ w) 1));
      [apply hPUSHX | apply hsteps_refl].
  }
  (* S36: pop12 3 *)
  apply (hsteps_trans _ (HB [] 4 1 13
                         ((37, 2) :: (1, 1) :: repeat (1, 2) 76 ++ (55, 2) :: (1, 1) :: repeat (1, 2) 614 ++ (2066, 2) :: (1, 1) :: repeat (1, 2) 7493 ++ (1911, 2) :: (1, 1) :: repeat (1, 2) 32604 ++ w) 1)).
  {
    apply (pop12 3 [] 1 7
           ((37, 2) :: (1, 1) :: repeat (1, 2) 76 ++ (55, 2) :: (1, 1) :: repeat (1, 2) 614 ++ (2066, 2) :: (1, 1) :: repeat (1, 2) 7493 ++ (1911, 2) :: (1, 1) :: repeat (1, 2) 32604 ++ w) 1); closearith.
  }
  (* S37: bottom front at [], pair (8, 2) over (35, 2) *)
  apply (hsteps_trans _ (HC [] 3 3 2
                         ((8, 2) :: (35, 2) :: (1, 1) :: repeat (1, 2) 76 ++ (55, 2) :: (1, 1) :: repeat (1, 2) 614 ++ (2066, 2) :: (1, 1) :: repeat (1, 2) 7493 ++ (1911, 2) :: (1, 1) :: repeat (1, 2) 32604 ++ w) 1)).
  {
    apply (hsteps_trans _ (HC [] 4 12 2
                           ((35, 2) :: (1, 1) :: repeat (1, 2) 76 ++ (55, 2) :: (1, 1) :: repeat (1, 2) 614 ++ (2066, 2) :: (1, 1) :: repeat (1, 2) 7493 ++ (1911, 2) :: (1, 1) :: repeat (1, 2) 32604 ++ w) 1)).
    {
      apply (sTUP [] 4 13 37 2
             ((1, 1) :: repeat (1, 2) 76 ++ (55, 2) :: (1, 1) :: repeat (1, 2) 614 ++ (2066, 2) :: (1, 1) :: repeat (1, 2) 7493 ++ (1911, 2) :: (1, 1) :: repeat (1, 2) 32604 ++ w) 1); closearith.
    }
    apply (hsteps_trans _ (HC [] 3 1 2
                           ((10, 2) :: (35, 2) :: (1, 1) :: repeat (1, 2) 76 ++ (55, 2) :: (1, 1) :: repeat (1, 2) 614 ++ (2066, 2) :: (1, 1) :: repeat (1, 2) 7493 ++ (1911, 2) :: (1, 1) :: repeat (1, 2) 32604 ++ w) 1)).
    {
      apply (sPUSH [] 3 12
             ((35, 2) :: (1, 1) :: repeat (1, 2) 76 ++ (55, 2) :: (1, 1) :: repeat (1, 2) 614 ++ (2066, 2) :: (1, 1) :: repeat (1, 2) 7493 ++ (1911, 2) :: (1, 1) :: repeat (1, 2) 32604 ++ w) 1); closearith.
    }
    apply (hsteps_trans _ (HB [] 3 1 4
                           ((10, 2) :: (35, 2) :: (1, 1) :: repeat (1, 2) 76 ++ (55, 2) :: (1, 1) :: repeat (1, 2) 614 ++ (2066, 2) :: (1, 1) :: repeat (1, 2) 7493 ++ (1911, 2) :: (1, 1) :: repeat (1, 2) 32604 ++ w) 1)).
    {
      apply (sTDN [] 3
             ((10, 2) :: (35, 2) :: (1, 1) :: repeat (1, 2) 76 ++ (55, 2) :: (1, 1) :: repeat (1, 2) 614 ++ (2066, 2) :: (1, 1) :: repeat (1, 2) 7493 ++ (1911, 2) :: (1, 1) :: repeat (1, 2) 32604 ++ w) 1).
    }
    replace ((8, 2) :: (35, 2) :: (1, 1) :: repeat (1, 2) 76 ++ (55, 2) :: (1, 1) :: repeat (1, 2) 614 ++ (2066, 2) :: (1, 1) :: repeat (1, 2) 7493 ++ (1911, 2) :: (1, 1) :: repeat (1, 2) 32604 ++ w)
      with ((10 - 2, 2) :: (35, 2) :: (1, 1) :: repeat (1, 2) 76 ++ (55, 2) :: (1, 1) :: repeat (1, 2) 614 ++ (2066, 2) :: (1, 1) :: repeat (1, 2) 7493 ++ (1911, 2) :: (1, 1) :: repeat (1, 2) 32604 ++ w)
      by sec_eq.
    apply (sTUP [] 3 4 10 2
           ((35, 2) :: (1, 1) :: repeat (1, 2) 76 ++ (55, 2) :: (1, 1) :: repeat (1, 2) 614 ++ (2066, 2) :: (1, 1) :: repeat (1, 2) 7493 ++ (1911, 2) :: (1, 1) :: repeat (1, 2) 32604 ++ w) 1); closearith.
  }
  (* S38: DIPGRIND (3, 2) *)
  apply (hsteps_trans _ (HC [] 0 3 2
                         (repeat (1, 2) 3 ++ (2, 2) :: (35, 2) :: (1, 1) :: repeat (1, 2) 76 ++ (55, 2) :: (1, 1) :: repeat (1, 2) 614 ++ (2066, 2) :: (1, 1) :: repeat (1, 2) 7493 ++ (1911, 2) :: (1, 1) :: repeat (1, 2) 32604 ++ w) 1)).
  {
    apply (DIPGRIND 3 2 []
           ((35, 2) :: (1, 1) :: repeat (1, 2) 76 ++ (55, 2) :: (1, 1) :: repeat (1, 2) 614 ++ (2066, 2) :: (1, 1) :: repeat (1, 2) 7493 ++ (1911, 2) :: (1, 1) :: repeat (1, 2) 32604 ++ w) 1); closearith.
  }
  (* S39: PUSHX *)
  apply (hsteps_trans _ (HB [] 1 1 7
                         (repeat (1, 2) 3 ++ (2, 2) :: (35, 2) :: (1, 1) :: repeat (1, 2) 76 ++ (55, 2) :: (1, 1) :: repeat (1, 2) 614 ++ (2066, 2) :: (1, 1) :: repeat (1, 2) 7493 ++ (1911, 2) :: (1, 1) :: repeat (1, 2) 32604 ++ w) 1)).
  {
    apply (hsteps_step _ (HB [] 1 1 7
                   (repeat (1, 2) 3 ++ (2, 2) :: (35, 2) :: (1, 1) :: repeat (1, 2) 76 ++ (55, 2) :: (1, 1) :: repeat (1, 2) 614 ++ (2066, 2) :: (1, 1) :: repeat (1, 2) 7493 ++ (1911, 2) :: (1, 1) :: repeat (1, 2) 32604 ++ w) 1));
      [apply hPUSHX | apply hsteps_refl].
  }
  (* S40: pop12 3 *)
  apply (hsteps_trans _ (HB [] 4 1 13
                         ((2, 2) :: (35, 2) :: (1, 1) :: repeat (1, 2) 76 ++ (55, 2) :: (1, 1) :: repeat (1, 2) 614 ++ (2066, 2) :: (1, 1) :: repeat (1, 2) 7493 ++ (1911, 2) :: (1, 1) :: repeat (1, 2) 32604 ++ w) 1)).
  {
    apply (pop12 3 [] 1 7
           ((2, 2) :: (35, 2) :: (1, 1) :: repeat (1, 2) 76 ++ (55, 2) :: (1, 1) :: repeat (1, 2) 614 ++ (2066, 2) :: (1, 1) :: repeat (1, 2) 7493 ++ (1911, 2) :: (1, 1) :: repeat (1, 2) 32604 ++ w) 1); closearith.
  }
  (* S41: TUP2_1 + TDN + TUP regrowth onto [5], pair (31, 2) *)
  apply (hsteps_trans _ (HC [5] 13 3 2
                         ((31, 2) :: (1, 1) :: repeat (1, 2) 76 ++ (55, 2) :: (1, 1) :: repeat (1, 2) 614 ++ (2066, 2) :: (1, 1) :: repeat (1, 2) 7493 ++ (1911, 2) :: (1, 1) :: repeat (1, 2) 32604 ++ w) 1)).
  {
    apply (hsteps_trans _ (HC [5] 13 1 2
                           ((33, 2) :: (1, 1) :: repeat (1, 2) 76 ++ (55, 2) :: (1, 1) :: repeat (1, 2) 614 ++ (2066, 2) :: (1, 1) :: repeat (1, 2) 7493 ++ (1911, 2) :: (1, 1) :: repeat (1, 2) 32604 ++ w) 1)).
    {
      replace ((33, 2) :: (1, 1) :: repeat (1, 2) 76 ++ (55, 2) :: (1, 1) :: repeat (1, 2) 614 ++ (2066, 2) :: (1, 1) :: repeat (1, 2) 7493 ++ (1911, 2) :: (1, 1) :: repeat (1, 2) 32604 ++ w)
        with ((35 - 2, 2) :: (1, 1) :: repeat (1, 2) 76 ++ (55, 2) :: (1, 1) :: repeat (1, 2) 614 ++ (2066, 2) :: (1, 1) :: repeat (1, 2) 7493 ++ (1911, 2) :: (1, 1) :: repeat (1, 2) 32604 ++ w)
        by sec_eq.
      apply (sTUP2_1 [] 4 12 35
             ((1, 1) :: repeat (1, 2) 76 ++ (55, 2) :: (1, 1) :: repeat (1, 2) 614 ++ (2066, 2) :: (1, 1) :: repeat (1, 2) 7493 ++ (1911, 2) :: (1, 1) :: repeat (1, 2) 32604 ++ w) 1); closearith.
    }
    apply (hsteps_trans _ (HB [5] 13 1 4
                           ((33, 2) :: (1, 1) :: repeat (1, 2) 76 ++ (55, 2) :: (1, 1) :: repeat (1, 2) 614 ++ (2066, 2) :: (1, 1) :: repeat (1, 2) 7493 ++ (1911, 2) :: (1, 1) :: repeat (1, 2) 32604 ++ w) 1)).
    {
      apply (sTDN [5] 13
             ((33, 2) :: (1, 1) :: repeat (1, 2) 76 ++ (55, 2) :: (1, 1) :: repeat (1, 2) 614 ++ (2066, 2) :: (1, 1) :: repeat (1, 2) 7493 ++ (1911, 2) :: (1, 1) :: repeat (1, 2) 32604 ++ w) 1).
    }
    replace ((31, 2) :: (1, 1) :: repeat (1, 2) 76 ++ (55, 2) :: (1, 1) :: repeat (1, 2) 614 ++ (2066, 2) :: (1, 1) :: repeat (1, 2) 7493 ++ (1911, 2) :: (1, 1) :: repeat (1, 2) 32604 ++ w)
      with ((33 - 2, 2) :: (1, 1) :: repeat (1, 2) 76 ++ (55, 2) :: (1, 1) :: repeat (1, 2) 614 ++ (2066, 2) :: (1, 1) :: repeat (1, 2) 7493 ++ (1911, 2) :: (1, 1) :: repeat (1, 2) 32604 ++ w)
      by sec_eq.
    apply (sTUP [5] 13 4 33 2
           ((1, 1) :: repeat (1, 2) 76 ++ (55, 2) :: (1, 1) :: repeat (1, 2) 614 ++ (2066, 2) :: (1, 1) :: repeat (1, 2) 7493 ++ (1911, 2) :: (1, 1) :: repeat (1, 2) 32604 ++ w) 1); closearith.
  }
  (* S42: DIPGRIND (13, 5) *)
  apply (hsteps_trans _ (HC [5] 0 3 2
                         (repeat (1, 2) 13 ++ (5, 2) :: (1, 1) :: repeat (1, 2) 76 ++ (55, 2) :: (1, 1) :: repeat (1, 2) 614 ++ (2066, 2) :: (1, 1) :: repeat (1, 2) 7493 ++ (1911, 2) :: (1, 1) :: repeat (1, 2) 32604 ++ w) 1)).
  {
    apply (DIPGRIND 13 5 [5]
           ((1, 1) :: repeat (1, 2) 76 ++ (55, 2) :: (1, 1) :: repeat (1, 2) 614 ++ (2066, 2) :: (1, 1) :: repeat (1, 2) 7493 ++ (1911, 2) :: (1, 1) :: repeat (1, 2) 32604 ++ w) 1); closearith.
  }
  (* S43: PX2Bgen onto [0] *)
  apply (hsteps_trans _ (HB [0] 3 1 2
                         ((1, 2) :: (1, 1) :: (1, 2) :: (1, 2) :: repeat (1, 2) 13 ++ (5, 2) :: (1, 1) :: repeat (1, 2) 76 ++ (55, 2) :: (1, 1) :: repeat (1, 2) 614 ++ (2066, 2) :: (1, 1) :: repeat (1, 2) 7493 ++ (1911, 2) :: (1, 1) :: repeat (1, 2) 32604 ++ w) 1)).
  {
    apply (hsteps_step _ (HB [0] 3 1 2
                   ((1, 2) :: (1, 1) :: (1, 2) :: (1, 2) :: repeat (1, 2) 13 ++ (5, 2) :: (1, 1) :: repeat (1, 2) 76 ++ (55, 2) :: (1, 1) :: repeat (1, 2) 614 ++ (2066, 2) :: (1, 1) :: repeat (1, 2) 7493 ++ (1911, 2) :: (1, 1) :: repeat (1, 2) 32604 ++ w) 1));
      [apply hPX2Bgen | apply hsteps_refl].
  }
  (* S44: pop12 1 *)
  apply (hsteps_trans _ (HB [0] 4 1 4
                         ((1, 1) :: (1, 2) :: (1, 2) :: repeat (1, 2) 13 ++ (5, 2) :: (1, 1) :: repeat (1, 2) 76 ++ (55, 2) :: (1, 1) :: repeat (1, 2) 614 ++ (2066, 2) :: (1, 1) :: repeat (1, 2) 7493 ++ (1911, 2) :: (1, 1) :: repeat (1, 2) 32604 ++ w) 1)).
  {
    replace ((1, 2) :: (1, 1) :: (1, 2) :: (1, 2) :: repeat (1, 2) 13 ++ (5, 2) :: (1, 1) :: repeat (1, 2) 76 ++ (55, 2) :: (1, 1) :: repeat (1, 2) 614 ++ (2066, 2) :: (1, 1) :: repeat (1, 2) 7493 ++ (1911, 2) :: (1, 1) :: repeat (1, 2) 32604 ++ w)
      with (repeat (1, 2) 1 ++ ((1, 1) :: (1, 2) :: (1, 2) :: repeat (1, 2) 13 ++ (5, 2) :: (1, 1) :: repeat (1, 2) 76 ++ (55, 2) :: (1, 1) :: repeat (1, 2) 614 ++ (2066, 2) :: (1, 1) :: repeat (1, 2) 7493 ++ (1911, 2) :: (1, 1) :: repeat (1, 2) 32604 ++ w))
      by sec_eq.
    apply (pop12 1 [0] 3 2
           ((1, 1) :: (1, 2) :: (1, 2) :: repeat (1, 2) 13 ++ (5, 2) :: (1, 1) :: repeat (1, 2) 76 ++ (55, 2) :: (1, 1) :: repeat (1, 2) 614 ++ (2066, 2) :: (1, 1) :: repeat (1, 2) 7493 ++ (1911, 2) :: (1, 1) :: repeat (1, 2) 32604 ++ w) 1); closearith.
  }
  (* S45: POP *)
  apply (hsteps_trans _ (HB [0] 5 1 5
                         ((1, 2) :: (1, 2) :: repeat (1, 2) 13 ++ (5, 2) :: (1, 1) :: repeat (1, 2) 76 ++ (55, 2) :: (1, 1) :: repeat (1, 2) 614 ++ (2066, 2) :: (1, 1) :: repeat (1, 2) 7493 ++ (1911, 2) :: (1, 1) :: repeat (1, 2) 32604 ++ w) 1)).
  {
    apply (sPOP1 [0] 4 4
           ((1, 2) :: (1, 2) :: repeat (1, 2) 13 ++ (5, 2) :: (1, 1) :: repeat (1, 2) 76 ++ (55, 2) :: (1, 1) :: repeat (1, 2) 614 ++ (2066, 2) :: (1, 1) :: repeat (1, 2) 7493 ++ (1911, 2) :: (1, 1) :: repeat (1, 2) 32604 ++ w) 1); closearith.
  }
  (* S46: pop12 15 *)
  apply (hsteps_trans _ (HB [0] 20 1 35
                         ((5, 2) :: (1, 1) :: repeat (1, 2) 76 ++ (55, 2) :: (1, 1) :: repeat (1, 2) 614 ++ (2066, 2) :: (1, 1) :: repeat (1, 2) 7493 ++ (1911, 2) :: (1, 1) :: repeat (1, 2) 32604 ++ w) 1)).
  {
    replace ((1, 2) :: (1, 2) :: repeat (1, 2) 13 ++ (5, 2) :: (1, 1) :: repeat (1, 2) 76 ++ (55, 2) :: (1, 1) :: repeat (1, 2) 614 ++ (2066, 2) :: (1, 1) :: repeat (1, 2) 7493 ++ (1911, 2) :: (1, 1) :: repeat (1, 2) 32604 ++ w)
      with (repeat (1, 2) 15 ++ ((5, 2) :: (1, 1) :: repeat (1, 2) 76 ++ (55, 2) :: (1, 1) :: repeat (1, 2) 614 ++ (2066, 2) :: (1, 1) :: repeat (1, 2) 7493 ++ (1911, 2) :: (1, 1) :: repeat (1, 2) 32604 ++ w))
      by sec_eq.
    apply (pop12 15 [0] 5 5
           ((5, 2) :: (1, 1) :: repeat (1, 2) 76 ++ (55, 2) :: (1, 1) :: repeat (1, 2) 614 ++ (2066, 2) :: (1, 1) :: repeat (1, 2) 7493 ++ (1911, 2) :: (1, 1) :: repeat (1, 2) 32604 ++ w) 1); closearith.
  }
  (* S47: front(5) partial (TUP + hGRIND_even 15 + TUP2_1 + TDN) onto [20; 0] *)
  apply (hsteps_trans _ (HB [20; 0] 34 1 4
                         ((1, 2) :: (1, 1) :: repeat (1, 2) 76 ++ (55, 2) :: (1, 1) :: repeat (1, 2) 614 ++ (2066, 2) :: (1, 1) :: repeat (1, 2) 7493 ++ (1911, 2) :: (1, 1) :: repeat (1, 2) 32604 ++ w) 1)).
  {
    apply (hsteps_trans _ (HC [0] 20 34 2
                           ((3, 2) :: (1, 1) :: repeat (1, 2) 76 ++ (55, 2) :: (1, 1) :: repeat (1, 2) 614 ++ (2066, 2) :: (1, 1) :: repeat (1, 2) 7493 ++ (1911, 2) :: (1, 1) :: repeat (1, 2) 32604 ++ w) 1)).
    {
      apply (sTUP [0] 20 35 5 2
             ((1, 1) :: repeat (1, 2) 76 ++ (55, 2) :: (1, 1) :: repeat (1, 2) 614 ++ (2066, 2) :: (1, 1) :: repeat (1, 2) 7493 ++ (1911, 2) :: (1, 1) :: repeat (1, 2) 32604 ++ w) 1); closearith.
    }
    apply (hsteps_trans _ (HB [0] 19 1 34
                           ((2, 2) :: (3, 2) :: (1, 1) :: repeat (1, 2) 76 ++ (55, 2) :: (1, 1) :: repeat (1, 2) 614 ++ (2066, 2) :: (1, 1) :: repeat (1, 2) 7493 ++ (1911, 2) :: (1, 1) :: repeat (1, 2) 32604 ++ w) 1)).
    {
      apply (hGRIND_even 15 [0] 19
             ((3, 2) :: (1, 1) :: repeat (1, 2) 76 ++ (55, 2) :: (1, 1) :: repeat (1, 2) 614 ++ (2066, 2) :: (1, 1) :: repeat (1, 2) 7493 ++ (1911, 2) :: (1, 1) :: repeat (1, 2) 32604 ++ w) 1); closearith.
    }
    apply (hsteps_trans _ (HC [20; 0] 34 1 2
                           ((1, 2) :: (1, 1) :: repeat (1, 2) 76 ++ (55, 2) :: (1, 1) :: repeat (1, 2) 614 ++ (2066, 2) :: (1, 1) :: repeat (1, 2) 7493 ++ (1911, 2) :: (1, 1) :: repeat (1, 2) 32604 ++ w) 1)).
    {
      replace ((1, 2) :: (1, 1) :: repeat (1, 2) 76 ++ (55, 2) :: (1, 1) :: repeat (1, 2) 614 ++ (2066, 2) :: (1, 1) :: repeat (1, 2) 7493 ++ (1911, 2) :: (1, 1) :: repeat (1, 2) 32604 ++ w)
        with ((3 - 2, 2) :: (1, 1) :: repeat (1, 2) 76 ++ (55, 2) :: (1, 1) :: repeat (1, 2) 614 ++ (2066, 2) :: (1, 1) :: repeat (1, 2) 7493 ++ (1911, 2) :: (1, 1) :: repeat (1, 2) 32604 ++ w)
        by sec_eq.
      apply (sTUP2_1 [0] 19 33 3
             ((1, 1) :: repeat (1, 2) 76 ++ (55, 2) :: (1, 1) :: repeat (1, 2) 614 ++ (2066, 2) :: (1, 1) :: repeat (1, 2) 7493 ++ (1911, 2) :: (1, 1) :: repeat (1, 2) 32604 ++ w) 1); closearith.
    }
    apply (sTDN [20; 0] 34
           ((1, 2) :: (1, 1) :: repeat (1, 2) 76 ++ (55, 2) :: (1, 1) :: repeat (1, 2) 614 ++ (2066, 2) :: (1, 1) :: repeat (1, 2) 7493 ++ (1911, 2) :: (1, 1) :: repeat (1, 2) 32604 ++ w) 1).
  }
  (* S48: pop12 1 *)
  apply (hsteps_trans _ (HB [20; 0] 35 1 6
                         ((1, 1) :: repeat (1, 2) 76 ++ (55, 2) :: (1, 1) :: repeat (1, 2) 614 ++ (2066, 2) :: (1, 1) :: repeat (1, 2) 7493 ++ (1911, 2) :: (1, 1) :: repeat (1, 2) 32604 ++ w) 1)).
  {
    replace ((1, 2) :: (1, 1) :: repeat (1, 2) 76 ++ (55, 2) :: (1, 1) :: repeat (1, 2) 614 ++ (2066, 2) :: (1, 1) :: repeat (1, 2) 7493 ++ (1911, 2) :: (1, 1) :: repeat (1, 2) 32604 ++ w)
      with (repeat (1, 2) 1 ++ ((1, 1) :: repeat (1, 2) 76 ++ (55, 2) :: (1, 1) :: repeat (1, 2) 614 ++ (2066, 2) :: (1, 1) :: repeat (1, 2) 7493 ++ (1911, 2) :: (1, 1) :: repeat (1, 2) 32604 ++ w))
      by sec_eq.
    apply (pop12 1 [20; 0] 34 4
           ((1, 1) :: repeat (1, 2) 76 ++ (55, 2) :: (1, 1) :: repeat (1, 2) 614 ++ (2066, 2) :: (1, 1) :: repeat (1, 2) 7493 ++ (1911, 2) :: (1, 1) :: repeat (1, 2) 32604 ++ w) 1); closearith.
  }
  (* S49: POP *)
  apply (hsteps_trans _ (HB [20; 0] 36 1 7
                         (repeat (1, 2) 76 ++ (55, 2) :: (1, 1) :: repeat (1, 2) 614 ++ (2066, 2) :: (1, 1) :: repeat (1, 2) 7493 ++ (1911, 2) :: (1, 1) :: repeat (1, 2) 32604 ++ w) 1)).
  {
    apply (sPOP1 [20; 0] 35 6
           (repeat (1, 2) 76 ++ (55, 2) :: (1, 1) :: repeat (1, 2) 614 ++ (2066, 2) :: (1, 1) :: repeat (1, 2) 7493 ++ (1911, 2) :: (1, 1) :: repeat (1, 2) 32604 ++ w) 1); closearith.
  }
  (* S50: pop12 76 *)
  apply (hsteps_trans _ (HB [20; 0] 112 1 159
                         ((55, 2) :: (1, 1) :: repeat (1, 2) 614 ++ (2066, 2) :: (1, 1) :: repeat (1, 2) 7493 ++ (1911, 2) :: (1, 1) :: repeat (1, 2) 32604 ++ w) 1)).
  {
    apply (pop12 76 [20; 0] 36 7
           ((55, 2) :: (1, 1) :: repeat (1, 2) 614 ++ (2066, 2) :: (1, 1) :: repeat (1, 2) 7493 ++ (1911, 2) :: (1, 1) :: repeat (1, 2) 32604 ++ w) 1); closearith.
  }
  (* S51: front(55) onto [112; 20; 0] *)
  apply (hsteps_trans _ (HC [112; 20; 0] 158 3 2
                         ((49, 2) :: (1, 1) :: repeat (1, 2) 614 ++ (2066, 2) :: (1, 1) :: repeat (1, 2) 7493 ++ (1911, 2) :: (1, 1) :: repeat (1, 2) 32604 ++ w) 1)).
  {
    apply (hsteps_trans _ (HC [20; 0] 112 158 2
                           ((53, 2) :: (1, 1) :: repeat (1, 2) 614 ++ (2066, 2) :: (1, 1) :: repeat (1, 2) 7493 ++ (1911, 2) :: (1, 1) :: repeat (1, 2) 32604 ++ w) 1)).
    {
      apply (sTUP [20; 0] 112 159 55 2
             ((1, 1) :: repeat (1, 2) 614 ++ (2066, 2) :: (1, 1) :: repeat (1, 2) 7493 ++ (1911, 2) :: (1, 1) :: repeat (1, 2) 32604 ++ w) 1); closearith.
    }
    apply (hsteps_trans _ (HB [20; 0] 111 1 158
                           ((2, 2) :: (53, 2) :: (1, 1) :: repeat (1, 2) 614 ++ (2066, 2) :: (1, 1) :: repeat (1, 2) 7493 ++ (1911, 2) :: (1, 1) :: repeat (1, 2) 32604 ++ w) 1)).
    {
      apply (hGRIND_even 77 [20; 0] 111
             ((53, 2) :: (1, 1) :: repeat (1, 2) 614 ++ (2066, 2) :: (1, 1) :: repeat (1, 2) 7493 ++ (1911, 2) :: (1, 1) :: repeat (1, 2) 32604 ++ w) 1); closearith.
    }
    apply (hsteps_trans _ (HC [112; 20; 0] 158 1 2
                           ((51, 2) :: (1, 1) :: repeat (1, 2) 614 ++ (2066, 2) :: (1, 1) :: repeat (1, 2) 7493 ++ (1911, 2) :: (1, 1) :: repeat (1, 2) 32604 ++ w) 1)).
    {
      replace ((51, 2) :: (1, 1) :: repeat (1, 2) 614 ++ (2066, 2) :: (1, 1) :: repeat (1, 2) 7493 ++ (1911, 2) :: (1, 1) :: repeat (1, 2) 32604 ++ w)
        with ((53 - 2, 2) :: (1, 1) :: repeat (1, 2) 614 ++ (2066, 2) :: (1, 1) :: repeat (1, 2) 7493 ++ (1911, 2) :: (1, 1) :: repeat (1, 2) 32604 ++ w)
        by sec_eq.
      apply (sTUP2_1 [20; 0] 111 157 53
             ((1, 1) :: repeat (1, 2) 614 ++ (2066, 2) :: (1, 1) :: repeat (1, 2) 7493 ++ (1911, 2) :: (1, 1) :: repeat (1, 2) 32604 ++ w) 1); closearith.
    }
    apply (hsteps_trans _ (HB [112; 20; 0] 158 1 4
                           ((51, 2) :: (1, 1) :: repeat (1, 2) 614 ++ (2066, 2) :: (1, 1) :: repeat (1, 2) 7493 ++ (1911, 2) :: (1, 1) :: repeat (1, 2) 32604 ++ w) 1)).
    {
      apply (sTDN [112; 20; 0] 158
             ((51, 2) :: (1, 1) :: repeat (1, 2) 614 ++ (2066, 2) :: (1, 1) :: repeat (1, 2) 7493 ++ (1911, 2) :: (1, 1) :: repeat (1, 2) 32604 ++ w) 1).
    }
    replace ((49, 2) :: (1, 1) :: repeat (1, 2) 614 ++ (2066, 2) :: (1, 1) :: repeat (1, 2) 7493 ++ (1911, 2) :: (1, 1) :: repeat (1, 2) 32604 ++ w)
      with ((51 - 2, 2) :: (1, 1) :: repeat (1, 2) 614 ++ (2066, 2) :: (1, 1) :: repeat (1, 2) 7493 ++ (1911, 2) :: (1, 1) :: repeat (1, 2) 32604 ++ w)
      by sec_eq.
    apply (sTUP [112; 20; 0] 158 4 51 2
           ((1, 1) :: repeat (1, 2) 614 ++ (2066, 2) :: (1, 1) :: repeat (1, 2) 7493 ++ (1911, 2) :: (1, 1) :: repeat (1, 2) 32604 ++ w) 1); closearith.
  }
  (* S52: CLEANG_odd 23 *)
  apply (hsteps_trans _ (HB [112; 20; 0] 158 1 54
                         ((1, 2) :: (1, 1) :: repeat (1, 2) 614 ++ (2066, 2) :: (1, 1) :: repeat (1, 2) 7493 ++ (1911, 2) :: (1, 1) :: repeat (1, 2) 32604 ++ w) 1)).
  {
    apply (CLEANG_odd 23 [112; 20; 0] 158
           ((1, 1) :: repeat (1, 2) 614 ++ (2066, 2) :: (1, 1) :: repeat (1, 2) 7493 ++ (1911, 2) :: (1, 1) :: repeat (1, 2) 32604 ++ w) 1); closearith.
  }
  (* S53: pop12 1 *)
  apply (hsteps_trans _ (HB [112; 20; 0] 159 1 56
                         ((1, 1) :: repeat (1, 2) 614 ++ (2066, 2) :: (1, 1) :: repeat (1, 2) 7493 ++ (1911, 2) :: (1, 1) :: repeat (1, 2) 32604 ++ w) 1)).
  {
    replace ((1, 2) :: (1, 1) :: repeat (1, 2) 614 ++ (2066, 2) :: (1, 1) :: repeat (1, 2) 7493 ++ (1911, 2) :: (1, 1) :: repeat (1, 2) 32604 ++ w)
      with (repeat (1, 2) 1 ++ ((1, 1) :: repeat (1, 2) 614 ++ (2066, 2) :: (1, 1) :: repeat (1, 2) 7493 ++ (1911, 2) :: (1, 1) :: repeat (1, 2) 32604 ++ w))
      by sec_eq.
    apply (pop12 1 [112; 20; 0] 158 54
           ((1, 1) :: repeat (1, 2) 614 ++ (2066, 2) :: (1, 1) :: repeat (1, 2) 7493 ++ (1911, 2) :: (1, 1) :: repeat (1, 2) 32604 ++ w) 1); closearith.
  }
  (* S54: POP *)
  apply (hsteps_trans _ (HB [112; 20; 0] 160 1 57
                         (repeat (1, 2) 614 ++ (2066, 2) :: (1, 1) :: repeat (1, 2) 7493 ++ (1911, 2) :: (1, 1) :: repeat (1, 2) 32604 ++ w) 1)).
  {
    apply (sPOP1 [112; 20; 0] 159 56
           (repeat (1, 2) 614 ++ (2066, 2) :: (1, 1) :: repeat (1, 2) 7493 ++ (1911, 2) :: (1, 1) :: repeat (1, 2) 32604 ++ w) 1); closearith.
  }
  (* S55: pop12 614 *)
  apply (hsteps_trans _ (HB [112; 20; 0] 774 1 1285
                         ((2066, 2) :: (1, 1) :: repeat (1, 2) 7493 ++ (1911, 2) :: (1, 1) :: repeat (1, 2) 32604 ++ w) 1)).
  {
    apply (pop12 614 [112; 20; 0] 160 57
           ((2066, 2) :: (1, 1) :: repeat (1, 2) 7493 ++ (1911, 2) :: (1, 1) :: repeat (1, 2) 32604 ++ w) 1); closearith.
  }
  (* S56: front(2066) onto [774; 112; 20; 0] *)
  apply (hsteps_trans _ (HC [774; 112; 20; 0] 1284 3 2
                         ((2060, 2) :: (1, 1) :: repeat (1, 2) 7493 ++ (1911, 2) :: (1, 1) :: repeat (1, 2) 32604 ++ w) 1)).
  {
    apply (hsteps_trans _ (HC [112; 20; 0] 774 1284 2
                           ((2064, 2) :: (1, 1) :: repeat (1, 2) 7493 ++ (1911, 2) :: (1, 1) :: repeat (1, 2) 32604 ++ w) 1)).
    {
      apply (sTUP [112; 20; 0] 774 1285 2066 2
             ((1, 1) :: repeat (1, 2) 7493 ++ (1911, 2) :: (1, 1) :: repeat (1, 2) 32604 ++ w) 1); closearith.
    }
    apply (hsteps_trans _ (HB [112; 20; 0] 773 1 1284
                           ((2, 2) :: (2064, 2) :: (1, 1) :: repeat (1, 2) 7493 ++ (1911, 2) :: (1, 1) :: repeat (1, 2) 32604 ++ w) 1)).
    {
      apply (hGRIND_even 640 [112; 20; 0] 773
             ((2064, 2) :: (1, 1) :: repeat (1, 2) 7493 ++ (1911, 2) :: (1, 1) :: repeat (1, 2) 32604 ++ w) 1); closearith.
    }
    apply (hsteps_trans _ (HC [774; 112; 20; 0] 1284 1 2
                           ((2062, 2) :: (1, 1) :: repeat (1, 2) 7493 ++ (1911, 2) :: (1, 1) :: repeat (1, 2) 32604 ++ w) 1)).
    {
      replace ((2062, 2) :: (1, 1) :: repeat (1, 2) 7493 ++ (1911, 2) :: (1, 1) :: repeat (1, 2) 32604 ++ w)
        with ((2064 - 2, 2) :: (1, 1) :: repeat (1, 2) 7493 ++ (1911, 2) :: (1, 1) :: repeat (1, 2) 32604 ++ w)
        by sec_eq.
      apply (sTUP2_1 [112; 20; 0] 773 1283 2064
             ((1, 1) :: repeat (1, 2) 7493 ++ (1911, 2) :: (1, 1) :: repeat (1, 2) 32604 ++ w) 1); closearith.
    }
    apply (hsteps_trans _ (HB [774; 112; 20; 0] 1284 1 4
                           ((2062, 2) :: (1, 1) :: repeat (1, 2) 7493 ++ (1911, 2) :: (1, 1) :: repeat (1, 2) 32604 ++ w) 1)).
    {
      apply (sTDN [774; 112; 20; 0] 1284
             ((2062, 2) :: (1, 1) :: repeat (1, 2) 7493 ++ (1911, 2) :: (1, 1) :: repeat (1, 2) 32604 ++ w) 1).
    }
    replace ((2060, 2) :: (1, 1) :: repeat (1, 2) 7493 ++ (1911, 2) :: (1, 1) :: repeat (1, 2) 32604 ++ w)
      with ((2062 - 2, 2) :: (1, 1) :: repeat (1, 2) 7493 ++ (1911, 2) :: (1, 1) :: repeat (1, 2) 32604 ++ w)
      by sec_eq.
    apply (sTUP [774; 112; 20; 0] 1284 4 2062 2
           ((1, 1) :: repeat (1, 2) 7493 ++ (1911, 2) :: (1, 1) :: repeat (1, 2) 32604 ++ w) 1); closearith.
  }
  (* S57: CLEANG_even 1029 *)
  apply (hsteps_trans _ (HB [774; 112; 20; 0] 1284 1 2064
                         ((2, 2) :: (1, 1) :: repeat (1, 2) 7493 ++ (1911, 2) :: (1, 1) :: repeat (1, 2) 32604 ++ w) 1)).
  {
    apply (CLEANG_even 1029 [774; 112; 20; 0] 1284
           ((1, 1) :: repeat (1, 2) 7493 ++ (1911, 2) :: (1, 1) :: repeat (1, 2) 32604 ++ w) 1); closearith.
  }
  (* S58: TRANS2_1 onto [1285; 774; 112; 20; 0] *)
  apply (hsteps_trans _ (HB [1285; 774; 112; 20; 0] 2065 1 3
                         (repeat (1, 2) 7493 ++ (1911, 2) :: (1, 1) :: repeat (1, 2) 32604 ++ w) 1)).
  {
    apply (sTRANS2_1 [774; 112; 20; 0] 1284 2063 1
           (repeat (1, 2) 7493 ++ (1911, 2) :: (1, 1) :: repeat (1, 2) 32604 ++ w) 1); lia.
  }
  (* S59: pop12 7493 *)
  apply (hsteps_trans _ (HB [1285; 774; 112; 20; 0] 9558 1 14989
                         ((1911, 2) :: (1, 1) :: repeat (1, 2) 32604 ++ w) 1)).
  {
    apply (pop12 7493 [1285; 774; 112; 20; 0] 2065 3
           ((1911, 2) :: (1, 1) :: repeat (1, 2) 32604 ++ w) 1); closearith.
  }
  (* S60: front(1911) onto [9558; 1285; 774; 112; 20; 0] *)
  apply (hsteps_trans _ (HC [9558; 1285; 774; 112; 20; 0] 14988 3 2
                         ((1905, 2) :: (1, 1) :: repeat (1, 2) 32604 ++ w) 1)).
  {
    apply (hsteps_trans _ (HC [1285; 774; 112; 20; 0] 9558 14988 2
                           ((1909, 2) :: (1, 1) :: repeat (1, 2) 32604 ++ w) 1)).
    {
      apply (sTUP [1285; 774; 112; 20; 0] 9558 14989 1911 2
             ((1, 1) :: repeat (1, 2) 32604 ++ w) 1); closearith.
    }
    apply (hsteps_trans _ (HB [1285; 774; 112; 20; 0] 9557 1 14988
                           ((2, 2) :: (1909, 2) :: (1, 1) :: repeat (1, 2) 32604 ++ w) 1)).
    {
      apply (hGRIND_even 7492 [1285; 774; 112; 20; 0] 9557
             ((1909, 2) :: (1, 1) :: repeat (1, 2) 32604 ++ w) 1); closearith.
    }
    apply (hsteps_trans _ (HC [9558; 1285; 774; 112; 20; 0] 14988 1 2
                           ((1907, 2) :: (1, 1) :: repeat (1, 2) 32604 ++ w) 1)).
    {
      replace ((1907, 2) :: (1, 1) :: repeat (1, 2) 32604 ++ w)
        with ((1909 - 2, 2) :: (1, 1) :: repeat (1, 2) 32604 ++ w)
        by sec_eq.
      apply (sTUP2_1 [1285; 774; 112; 20; 0] 9557 14987 1909
             ((1, 1) :: repeat (1, 2) 32604 ++ w) 1); closearith.
    }
    apply (hsteps_trans _ (HB [9558; 1285; 774; 112; 20; 0] 14988 1 4
                           ((1907, 2) :: (1, 1) :: repeat (1, 2) 32604 ++ w) 1)).
    {
      apply (sTDN [9558; 1285; 774; 112; 20; 0] 14988
             ((1907, 2) :: (1, 1) :: repeat (1, 2) 32604 ++ w) 1).
    }
    replace ((1905, 2) :: (1, 1) :: repeat (1, 2) 32604 ++ w)
      with ((1907 - 2, 2) :: (1, 1) :: repeat (1, 2) 32604 ++ w)
      by sec_eq.
    apply (sTUP [9558; 1285; 774; 112; 20; 0] 14988 4 1907 2
           ((1, 1) :: repeat (1, 2) 32604 ++ w) 1); closearith.
  }
  (* S61: CLEANG_odd 951 *)
  apply (hsteps_trans _ (HB [9558; 1285; 774; 112; 20; 0] 14988 1 1910
                         ((1, 2) :: (1, 1) :: repeat (1, 2) 32604 ++ w) 1)).
  {
    apply (CLEANG_odd 951 [9558; 1285; 774; 112; 20; 0] 14988
           ((1, 1) :: repeat (1, 2) 32604 ++ w) 1); closearith.
  }
  (* S62: pop12 1 *)
  apply (hsteps_trans _ (HB [9558; 1285; 774; 112; 20; 0] 14989 1 1912
                         ((1, 1) :: repeat (1, 2) 32604 ++ w) 1)).
  {
    replace ((1, 2) :: (1, 1) :: repeat (1, 2) 32604 ++ w)
      with (repeat (1, 2) 1 ++ ((1, 1) :: repeat (1, 2) 32604 ++ w))
      by sec_eq.
    apply (pop12 1 [9558; 1285; 774; 112; 20; 0] 14988 1910
           ((1, 1) :: repeat (1, 2) 32604 ++ w) 1); closearith.
  }
  (* S63: POP *)
  apply (hsteps_trans _ (HB [9558; 1285; 774; 112; 20; 0] 14990 1 1913
                         (repeat (1, 2) 32604 ++ w) 1)).
  {
    apply (sPOP1 [9558; 1285; 774; 112; 20; 0] 14989 1912
           (repeat (1, 2) 32604 ++ w) 1); closearith.
  }
  (* S64: pop12 32604 = TOP4 *)
  apply (pop12 32604 [9558; 1285; 774; 112; 20; 0] 14990 1913
         (w) 1); closearith.
Qed.

(* ----------------------------------------------------------------- *)
(* TOP50_TO_TOP4: TOP3 -> front (TUP, hGRIND_even 16299, TUP2_1,   *)
(* TDN, TUP -- the TOP49_BAND front shape) -> GRIND4 ->             *)
(* DIPGRIND (32602, 2 * (j - 32605)) -> CASCADE50 -> TOP4, uniform  *)
(* in (j, beta) for j >= 32606.  The target pair is written         *)
(* (2 * (j - 32605), 2) so it matches the TOP50_BAND /              *)
(* TAIL2_END5 instantiations syntactically.                         *)
(* ----------------------------------------------------------------- *)

Lemma TOP50_TO_TOP4 : forall j beta, 32606 <= j -> 2 <= beta ->
  hsteps (HB [7493; 3816; 259; 93; 50; 14; 5] 16899 1 32603
            ((2 * j, 2) :: (1, 1) :: repeat (1, 2) (beta - 1)) 1)
         (HB [9558; 1285; 774; 112; 20; 0] 47594 1 67121
            ((2 * (j - 32605), 2) :: (1, 1)
             :: repeat (1, 2) (beta - 1)) 1).
Proof.
  intros j beta Hj Hb.
  (* lia cannot use Hj directly: 32606 is an of_num_uint atom,    *)
  (* unrelated in lia's eyes to the numerals below.  Derive a     *)
  (* numeral lower bound on j, and normalise the 32605/32606      *)
  (* atoms onto the single atom 32602 where an identity needs     *)
  (* them.                                                        *)
  assert (Hj4 : 4 <= j).
  { apply Nat.le_trans with 32606; [closearith | exact Hj]. }
  assert (Hr : 1 <= j - 32605).
  { change 32605 with (32606 - 1). lia. }
  assert (Heq : 2 * j - 6 = 2 * 32602 + 2 * (j - 32605)).
  { change 32605 with (32602 + 3).
    change 32606 with (32602 + 4) in Hj. lia. }
  apply (hsteps_trans _ (HC [7493; 3816; 259; 93; 50; 14; 5] 16899
    32602 2 ((2 * j - 2, 2) :: (1, 1) :: repeat (1, 2) (beta - 1)) 1)).
  { apply (sTUP [7493; 3816; 259; 93; 50; 14; 5] 16899 32603 (2 * j) 2
           ((1, 1) :: repeat (1, 2) (beta - 1)) 1); closearith. }
  apply (hsteps_trans _ (HB [7493; 3816; 259; 93; 50; 14; 5] 16898
    1 32602 ((2, 2) :: (2 * j - 2, 2) :: (1, 1)
            :: repeat (1, 2) (beta - 1)) 1)).
  { apply (hGRIND_even 16299 [7493; 3816; 259; 93; 50; 14; 5] 16898
           ((2 * j - 2, 2) :: (1, 1) :: repeat (1, 2) (beta - 1))
           1); closearith. }
  apply (hsteps_trans _ (HC [16899; 7493; 3816; 259; 93; 50; 14; 5]
    32602 1 2 ((2 * j - 4, 2) :: (1, 1) :: repeat (1, 2) (beta - 1)) 1)).
  { replace ((2 * j - 4, 2) :: (1, 1) :: repeat (1, 2) (beta - 1))
      with ((2 * j - 2 - 2, 2) :: (1, 1) :: repeat (1, 2) (beta - 1))
      by sec_eq.
    apply (sTUP2_1 [7493; 3816; 259; 93; 50; 14; 5] 16898 32601
           (2 * j - 2) ((1, 1) :: repeat (1, 2) (beta - 1)) 1); lia. }
  apply (hsteps_trans _ (HB [16899; 7493; 3816; 259; 93; 50; 14; 5]
    32602 1 4 ((2 * j - 4, 2) :: (1, 1) :: repeat (1, 2) (beta - 1)) 1)).
  { apply (sTDN [16899; 7493; 3816; 259; 93; 50; 14; 5] 32602
           ((2 * j - 4, 2) :: (1, 1) :: repeat (1, 2) (beta - 1))
           1). }
  apply (hsteps_trans _ (HC [16899; 7493; 3816; 259; 93; 50; 14; 5]
    32602 3 2 ((2 * j - 6, 2) :: (1, 1) :: repeat (1, 2) (beta - 1)) 1)).
  { replace ((2 * j - 6, 2) :: (1, 1) :: repeat (1, 2) (beta - 1))
      with ((2 * j - 4 - 2, 2) :: (1, 1) :: repeat (1, 2) (beta - 1))
      by sec_eq.
    apply (sTUP [16899; 7493; 3816; 259; 93; 50; 14; 5] 32602 4
           (2 * j - 4) 2 ((1, 1) :: repeat (1, 2) (beta - 1)) 1);
      lia. }
  apply (hsteps_trans _ (HC [16899; 7493; 3816; 259; 93; 50; 14; 5]
    0 3 2 (repeat (1, 2) 32602
     ++ ((2 * (j - 32605), 2) :: (1, 1)
         :: repeat (1, 2) (beta - 1))) 1)).
  { rewrite Heq.
    apply (DIPGRIND 32602 (2 * (j - 32605))
           [16899; 7493; 3816; 259; 93; 50; 14; 5]
           ((1, 1) :: repeat (1, 2) (beta - 1)) 1);
      [closearith | lia]. }
  apply (CASCADE50 ((2 * (j - 32605), 2) :: (1, 1)
                    :: repeat (1, 2) (beta - 1))).
Qed.

(* ----------------------------------------------------------------- *)
(* The TOP4 closings: r4 = 2, r4 = 4, r4 = 6, and band 4            *)
(* (r4 = 2 * j4, 4 <= j4 <= 67123, i.e. 8 <= r4 <= 134246).         *)
(* ----------------------------------------------------------------- *)

Lemma TOP50_2 : forall beta, 2 <= beta ->
  hsteps (HB [9558; 1285; 774; 112; 20; 0] 47594 1 67121
            ((2, 2) :: (1, 1) :: repeat (1, 2) (beta - 1)) 1)
         (HB [47595; 9558; 1285; 774; 112; 20; 0]
            (67122 + (beta - 1)) 1 (2 * beta + 1) [] 1).
Proof.
  intros beta Hb.
  apply (hsteps_trans _ (HB [47595; 9558; 1285; 774; 112; 20; 0]
    67122 1 3 (repeat (1, 2) (beta - 1)) 1)).
  { apply (sTRANS2_1 [9558; 1285; 774; 112; 20; 0] 47594 67120 1
           (repeat (1, 2) (beta - 1)) 1); lia. }
  apply (CASCADE_POPFIN [47595; 9558; 1285; 774; 112; 20; 0]
         67122 beta); lia.
Qed.

Lemma TOP50_4 : forall beta, 2 <= beta ->
  hsteps (HB [9558; 1285; 774; 112; 20; 0] 47594 1 67121
            ((4, 2) :: (1, 1) :: repeat (1, 2) (beta - 1)) 1)
         (HB [67121; 47594; 9558; 1285; 774; 112; 20; 0]
            (beta + 2) 1 (2 * beta + 1) [] 1).
Proof.
  intros beta Hb.
  apply (hsteps_trans _ (HC [9558; 1285; 774; 112; 20; 0] 47594
    67120 2 ((2, 2) :: (1, 1) :: repeat (1, 2) (beta - 1)) 1)).
  { apply (sTUP [9558; 1285; 774; 112; 20; 0] 47594 67121 4 2
           ((1, 1) :: repeat (1, 2) (beta - 1)) 1); closearith. }
  apply (hsteps_trans _ (HB [9558; 1285; 774; 112; 20; 0] 47593
    1 67120 ((2, 2) :: (2, 2) :: (1, 1)
            :: repeat (1, 2) (beta - 1)) 1)).
  { apply (hGRIND_even 33558 [9558; 1285; 774; 112; 20; 0] 47593
           ((2, 2) :: (1, 1) :: repeat (1, 2) (beta - 1)) 1);
      closearith. }
  apply (hsteps_trans _ (HB [67121; 47594; 9558; 1285; 774; 112;
    20; 0] 3 1 3 (repeat (1, 2) (beta - 1)) 1)).
  { apply (hsteps_step _ (HB [67121; 47594; 9558; 1285; 774; 112;
      20; 0] 3 1 3 (repeat (1, 2) (beta - 1)) 1));
      [apply hTRANS2_2; closearith | apply hsteps_refl]. }
  replace (beta + 2) with (3 + (beta - 1)) by lia.
  apply (CASCADE_POPFIN [67121; 47594; 9558; 1285; 774; 112; 20; 0]
         3 beta); lia.
Qed.

Lemma TOP50_6 : forall beta, 2 <= beta ->
  hsteps (HB [9558; 1285; 774; 112; 20; 0] 47594 1 67121
            ((6, 2) :: (1, 1) :: repeat (1, 2) (beta - 1)) 1)
         (HB [67121; 47594; 9558; 1285; 774; 112; 20; 0]
            (beta + 4) 1 (2 * beta + 1) [] 1).
Proof.
  intros beta Hb.
  apply (hsteps_trans _ (HC [9558; 1285; 774; 112; 20; 0] 47594
    67120 2 ((4, 2) :: (1, 1) :: repeat (1, 2) (beta - 1)) 1)).
  { apply (sTUP [9558; 1285; 774; 112; 20; 0] 47594 67121 6 2
           ((1, 1) :: repeat (1, 2) (beta - 1)) 1); closearith. }
  apply (hsteps_trans _ (HB [9558; 1285; 774; 112; 20; 0] 47593
    1 67120 ((2, 2) :: (4, 2) :: (1, 1)
            :: repeat (1, 2) (beta - 1)) 1)).
  { apply (hGRIND_even 33558 [9558; 1285; 774; 112; 20; 0] 47593
           ((4, 2) :: (1, 1) :: repeat (1, 2) (beta - 1)) 1);
      closearith. }
  apply (hsteps_trans _ (HC [47594; 9558; 1285; 774; 112; 20; 0]
    67120 1 2 ((2, 2) :: (1, 1) :: repeat (1, 2) (beta - 1)) 1)).
  { replace ((2, 2) :: (1, 1) :: repeat (1, 2) (beta - 1))
      with ((4 - 2, 2) :: (1, 1) :: repeat (1, 2) (beta - 1))
      by sec_eq.
    apply (sTUP2_1 [9558; 1285; 774; 112; 20; 0] 47593 67119 4
           ((1, 1) :: repeat (1, 2) (beta - 1)) 1); lia. }
  apply (hsteps_trans _ (HB [47594; 9558; 1285; 774; 112; 20; 0]
    67120 1 4 ((2, 2) :: (1, 1) :: repeat (1, 2) (beta - 1)) 1)).
  { apply (sTDN [47594; 9558; 1285; 774; 112; 20; 0] 67120
           ((2, 2) :: (1, 1) :: repeat (1, 2) (beta - 1)) 1). }
  apply (hsteps_trans _ (HB [67121; 47594; 9558; 1285; 774; 112;
    20; 0] 5 1 3 (repeat (1, 2) (beta - 1)) 1)).
  { apply (sTRANS2_1 [47594; 9558; 1285; 774; 112; 20; 0] 67120
           3 1 (repeat (1, 2) (beta - 1)) 1); lia. }
  replace (beta + 4) with (5 + (beta - 1)) by lia.
  apply (CASCADE_POPFIN [67121; 47594; 9558; 1285; 774; 112; 20; 0]
         5 beta); lia.
Qed.

Lemma TOP50_BAND : forall j beta, 4 <= j -> j <= 67123 -> 2 <= beta ->
  hsteps (HB [9558; 1285; 774; 112; 20; 0] 47594 1 67121
            ((2 * j, 2) :: (1, 1) :: repeat (1, 2) (beta - 1)) 1)
         (HB [67121; 47594; 9558; 1285; 774; 112; 20; 0]
            (2 * j + beta - 2) 1 (2 * beta + 1) [] 1).
Proof.
  intros j beta Hj1 Hj2 Hb.
  apply (hsteps_trans _ (HC [9558; 1285; 774; 112; 20; 0] 47594
    67120 2 ((2 * j - 2, 2) :: (1, 1) :: repeat (1, 2) (beta - 1)) 1)).
  { apply (sTUP [9558; 1285; 774; 112; 20; 0] 47594 67121 (2 * j) 2
           ((1, 1) :: repeat (1, 2) (beta - 1)) 1); closearith. }
  apply (hsteps_trans _ (HB [9558; 1285; 774; 112; 20; 0] 47593
    1 67120 ((2, 2) :: (2 * j - 2, 2) :: (1, 1)
            :: repeat (1, 2) (beta - 1)) 1)).
  { apply (hGRIND_even 33558 [9558; 1285; 774; 112; 20; 0] 47593
           ((2 * j - 2, 2) :: (1, 1) :: repeat (1, 2) (beta - 1))
           1); closearith. }
  apply (hsteps_trans _ (HC [47594; 9558; 1285; 774; 112; 20; 0]
    67120 1 2 ((2 * j - 4, 2) :: (1, 1) :: repeat (1, 2) (beta - 1)) 1)).
  { replace ((2 * j - 4, 2) :: (1, 1) :: repeat (1, 2) (beta - 1))
      with ((2 * j - 2 - 2, 2) :: (1, 1) :: repeat (1, 2) (beta - 1))
      by sec_eq.
    apply (sTUP2_1 [9558; 1285; 774; 112; 20; 0] 47593 67119
           (2 * j - 2) ((1, 1) :: repeat (1, 2) (beta - 1)) 1); lia. }
  apply (hsteps_trans _ (HB [47594; 9558; 1285; 774; 112; 20; 0]
    67120 1 4 ((2 * j - 4, 2) :: (1, 1) :: repeat (1, 2) (beta - 1)) 1)).
  { apply (sTDN [47594; 9558; 1285; 774; 112; 20; 0] 67120
           ((2 * j - 4, 2) :: (1, 1) :: repeat (1, 2) (beta - 1))
           1). }
  apply (hsteps_trans _ (HC [47594; 9558; 1285; 774; 112; 20; 0]
    67120 3 2 ((2 * j - 6, 2) :: (1, 1) :: repeat (1, 2) (beta - 1)) 1)).
  { replace ((2 * j - 6, 2) :: (1, 1) :: repeat (1, 2) (beta - 1))
      with ((2 * j - 4 - 2, 2) :: (1, 1) :: repeat (1, 2) (beta - 1))
      by sec_eq.
    apply (sTUP [47594; 9558; 1285; 774; 112; 20; 0] 67120 4
           (2 * j - 4) 2 ((1, 1) :: repeat (1, 2) (beta - 1)) 1);
      lia. }
  apply (hsteps_trans _ (HB [47594; 9558; 1285; 774; 112; 20; 0]
    67120 1 (2 * j - 2)
    ((2, 2) :: (1, 1) :: repeat (1, 2) (beta - 1)) 1)).
  { replace (2 * j - 6) with (2 * (j - 4) + 2) by lia.
    replace (2 * j - 2) with (2 * (j - 4) + 6) by lia.
    apply (CLEANG_even (j - 4) [47594; 9558; 1285; 774; 112; 20; 0]
           67120 ((1, 1) :: repeat (1, 2) (beta - 1)) 1).
    (* the floor (j - 4) + 1 <= 67120: route via j <= 67123 *)
    apply Nat.le_trans with (j - 3).
    - lia.
    - change 67120 with (67123 - 3).
      apply Nat.sub_le_mono_r. exact Hj2. }
  apply (hsteps_trans _ (HB [67121; 47594; 9558; 1285; 774; 112;
    20; 0] (2 * j - 1) 1 3 (repeat (1, 2) (beta - 1)) 1)).
  { replace (2 * j - 2) with (S (2 * j - 3)) by lia.
    replace (2 * j - 1) with (S (S (2 * j - 3))) by lia.
    apply (sTRANS2_1 [47594; 9558; 1285; 774; 112; 20; 0] 67120
           (2 * j - 3) 1 (repeat (1, 2) (beta - 1)) 1); lia. }
  replace (2 * j + beta - 2) with (2 * j - 1 + (beta - 1)) by lia.
  apply (CASCADE_POPFIN [67121; 47594; 9558; 1285; 774; 112; 20; 0]
         (2 * j - 1) beta); lia.
Qed.

(* ----------------------------------------------------------------- *)
(* TAIL2_END5: the strictly smaller residual core -- the totality   *)
(* of the TOP4 state for r4 = 2 * j, j >= 67124 (r4 >= 134248),     *)
(* where the GRIND5 pair (r4 - 6, 2) at counter 67120 takes the     *)
(* DIPDESC boundary a fifth time.  A Definition (lemma              *)
(* parameter), never an axiom.                                      *)
(* ----------------------------------------------------------------- *)

Definition TAIL2_END5 : Prop :=
  forall j beta, 67124 <= j -> 2 <= beta ->
  exists pb A, beta <= A /\
    hsteps (HB [9558; 1285; 774; 112; 20; 0] 47594 1 67121
              ((2 * j, 2) :: (1, 1) :: repeat (1, 2) (beta - 1)) 1)
           (HB pb A 1 (2 * beta + 1) [] 1).

(* ----------------------------------------------------------------- *)
(* TAIL2_END4_of50: TAIL2_END4, modulo TAIL2_END5.  The j-range     *)
(* splits at r4 = 2 * (j - 32605): the three small cases and        *)
(* band 4 are proved above; j - 32605 >= 67124 is the core.         *)
(* ----------------------------------------------------------------- *)

Lemma TAIL2_END4_of50 : TAIL2_END5 -> TAIL2_END4.
Proof.
  intros H5 j beta Hj Hb.
  pose proof (TOP50_TO_TOP4 j beta Hj Hb) as Htop.
  destruct (le_lt_dec 67124 (j - 32605)) as [Hbig | Hsmall].
  - (* j4 = j - 32605 >= 67124: the core *)
    destruct (H5 (j - 32605) beta Hbig Hb)
      as [pb [A [Ha Hsteps]]].
    exists pb, A. split; [exact Ha |].
    exact (hsteps_trans _ _ _ Htop Hsteps).
  - destruct (le_lt_dec 4 (j - 32605)) as [Hband | Htiny].
    + (* band 4: j4 = j - 32605, 4 <= j4 <= 67123 *)
      exists [67121; 47594; 9558; 1285; 774; 112; 20; 0],
        (2 * (j - 32605) + beta - 2).
      split; [lia |].
      assert (Hj2 : j - 32605 <= 67123).
      { change 67124 with (S 67123) in Hsmall.
        apply (proj1 (Nat.lt_succ_r _ _) Hsmall). }
      exact (hsteps_trans _ _ _ Htop
               (TOP50_BAND (j - 32605) beta Hband Hj2 Hb)).
    + (* tiny: j4 = j - 32605 <= 3; j4 >= 1 since 32606 <= j *)
      destruct (Nat.eq_dec (j - 32605) 1) as [He | Hne].
      * (* r4 = 2 *)
        rewrite He in Htop.
        exists [47595; 9558; 1285; 774; 112; 20; 0],
          (67122 + (beta - 1)).
        split; [change 67122 with (S 67121); lia |].
        exact (hsteps_trans _ _ _ Htop (TOP50_2 beta Hb)).
      * destruct (Nat.eq_dec (j - 32605) 2) as [He | Hne'].
        -- (* r4 = 4 *)
           rewrite He in Htop.
           exists [67121; 47594; 9558; 1285; 774; 112; 20; 0],
             (beta + 2).
           split; [lia |].
           exact (hsteps_trans _ _ _ Htop (TOP50_4 beta Hb)).
        -- destruct (Nat.eq_dec (j - 32605) 3) as [He | Hne''].
           ++ (* r4 = 6 *)
              rewrite He in Htop.
              exists [67121; 47594; 9558; 1285; 774; 112; 20; 0],
                (beta + 4).
              split; [lia |].
              exact (hsteps_trans _ _ _ Htop (TOP50_6 beta Hb)).
           ++ (* j4 = 0, contradicting 32606 <= j *)
              exfalso.
              assert (H0 : j - 32605 = 0) by lia.
              change 32606 with (S 32605) in Hj.
              lia.
Qed.

(* ----------------------------------------------------------------- *)
(* ESC_ERA_LAW_50: the phase-8 ESC era law at every even            *)
(* R >= 1278, modulo TAIL2_END5 alone.                              *)
(* ----------------------------------------------------------------- *)

Lemma ESC_ERA_LAW_50 : TAIL2_END5 ->
  forall M beta, 616 <= M -> 2 <= beta ->
  exists n c pb a,
    run n (esc_src (2 * M + 52) (beta - 2)) = Some c
    /\ cfg_sim c (rcsec (false :: repeat true (S a) ++ enc pb)
                        (2 * beta + 2) [(1, 2)])
    /\ beta <= a.
Proof.
  intros H M beta HM Hb.
  apply (ESC_ERA_LAW_49 (TAIL2_END4_of50 H) M beta HM Hb).
Qed.

(* ----------------------------------------------------------------- *)
(* Assumption audit                                                  *)
(* ----------------------------------------------------------------- *)

Print Assumptions CASCADE50.
Print Assumptions TOP50_TO_TOP4.
Print Assumptions TOP50_2.
Print Assumptions TOP50_4.
Print Assumptions TOP50_6.
Print Assumptions TOP50_BAND.
Print Assumptions TAIL2_END4_of50.
Print Assumptions ESC_ERA_LAW_50.
