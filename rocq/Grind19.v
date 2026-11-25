(* ================================================================= *)
(*  Grind19.v -- Phase 51: the fifth re-descent cascade of the      *)
(*  TOP4 state, mechanised as a fixed parse, closing TAIL2_END5     *)
(*  for the whole first j-band 67124 <= j <= 201372 (TOP4           *)
(*  parameters) and reducing the rest to a strictly smaller core    *)
(*  at the TOP5 state.                                              *)
(*                                                                  *)
(*  Phase 50 left the ESC side of H_LOOP resting on TAIL2_END5      *)
(*  (Grind18.v): the totality of the TOP4 state                     *)
(*                                                                  *)
(*    TOP4(j, beta) = HB [9558; 1285; 774; 112; 20; 0] 47594        *)
(*                    1 67121 ((2j, 2) :: (1, 1) :: (1, 2)^(beta-1)) *)
(*                                                                  *)
(*  for j >= 67124.  There the GRIND5 pair (2j - 6, 2) at counter   *)
(*  67120 exceeds the CLEANG_even floor and takes the DIPDESC       *)
(*  boundary a fifth time.  Phase 51 traces the walk                *)
(*  (rocq/hsim51.py, ALL PASS: the 16-waypoint chain below          *)
(*  asserted verbatim at (j, beta) in {(67124, 2), (67124, 3),      *)
(*  (67125, 2), (100000, 2), (201372, 2)}; TOP5 finals and the      *)
(*  cycle-6 fence asserted too; a junk-tail probe confirms          *)
(*  CASCADE51 is stated for an arbitrary tail; the streaming        *)
(*  walker of hsim49/hsim50 is reused).                             *)
(*                                                                  *)
(*  FINDING: the fifth descent is again a FIXED parse, uniform      *)
(*  in (j, beta) -- not a return to TOP4, TOP3, TOP2 or TOP.        *)
(*  Writing r5 = 2j - 134246 >= 2 for the DIPGRIND residue at       *)
(*  GRIND5:                                                         *)
(*                                                                  *)
(*    TOP4 --front (TUP, hGRIND_even 33558, TUP2_1, TDN, TUP)-->    *)
(*      GRIND5 = HC [47594; 9558; 1285; 774; 112; 20; 0]            *)
(*                 67120 3 2 ((2j - 6, 2) :: tail)                  *)
(*    --DIPGRIND (67120, r5)-->                                     *)
(*      HC [47594; 9558; ...] 0 3 2 ((1, 2)^67120 ++ W),            *)
(*        W = ((r5, 2) :: (1, 1) :: (1, 2)^(beta - 1))              *)
(*    --CASCADE51 (fixed parse, arbitrary tail)-->                  *)
(*      TOP5 = HB [20403; 10332; 112; 20; 0] 95597 1 134247 W.      *)
(*                                                                  *)
(*  CASCADE51 descends the TOP4 frame's own blocks: PX2A + PUSH     *)
(*  + TDN + TUP onto [1285; 774; 112; 20; 0] (pair 47588), a        *)
(*  DIPGRIND level (9556, 28476), PX2A onto [112; 20; 0],           *)
(*  hGRIND 640, POP, pop12 9558, TUP + hGRIND_even 10199 onto       *)
(*  the front of pair 28474, TUP2_1 + TDN + TUP onto                *)
(*  [10332; 112; 20; 0] (pair 28470), CLEANG_even 14234,            *)
(*  TRANS2_1, pop12 67122, landing on TOP5.  (Shorter than          *)
(*  CASCADE50's 64 segments: the TOP4 frame's blocks happen to      *)
(*  align so that two DIPGRIND levels and one clean grind           *)
(*  suffice.)                                                       *)
(*                                                                  *)
(*  TOP5 then closes by the size of r5 = 2 * j5 (j5 = j - 67123     *)
(*  in TOP5's own parameter):                                      *)
(*    r5 = 2:       TRANS2_1 + CASCADE_POPFIN, A = 134247 + beta;   *)
(*    r5 = 4:       TUP + hGRIND_even 67121 + TRANS2_2              *)
(*                    + CASCADE_POPFIN, A = beta + 2;               *)
(*    r5 = 6:       TUP + hGRIND_even 67121 + TUP2_1 + TDN          *)
(*                    + TRANS2_1 + CASCADE_POPFIN, A = beta + 4;    *)
(*    8 <= r5 <= 268498 (band 5): TUP + hGRIND_even 67121 + TUP2_1  *)
(*      + TDN + TUP onto GRIND6 = HC [95597; 20403; ...] 134246     *)
(*      3 2 ((r5 - 6, 2) :: tail), whose pair grinds CLEANLY by     *)
(*      CLEANG_even (floor (r5 - 8)/2 + 1 <= 134246, exactly         *)
(*      r5 <= 268498), then TRANS2_1 + CASCADE_POPFIN,              *)
(*      A = r5 + beta - 2, frame [134247; 95597; 20403; ...].       *)
(*      (The band counter is again the shuttle moved into the       *)
(*      counter slot by TUP2_1: 134246, not 95597.)                 *)
(*                                                                  *)
(*  For r5 >= 268500 (j5 >= 134250, i.e. TOP4-parameter             *)
(*  j >= 201373) the pair (r5 - 6, 2) at counter 134246 exceeds     *)
(*  the CLEANG_even floor and the rounds take the DIPDESC           *)
(*  boundary a SIXTH time (hsim51 Part 3: the GRIND6 state and      *)
(*  the DIPGRIND (134246, r5 - 268498) landing both occur at         *)
(*  j = 201373, 201374, 210000).  The sixth descent is expected     *)
(*  to be a NEW cascade with different constants, so no cycle       *)
(*  induction in the current vocabulary closes it; what remains     *)
(*  is the strictly smaller core                                    *)
(*                                                                  *)
(*    TAIL2_END6: the totality of the ONE pair (2j, 2) at the ONE   *)
(*    fixed TOP5 state HB [20403; 10332; 112; 20; 0] 95597          *)
(*    1 134247, for j >= 134250 (r5 = 2j >= 268500), beta >= 2.     *)
(*                                                                  *)
(*  The core's range shrank from [67124, infty) to [201373, infty)  *)
(*  in TOP4 parameters; the band width roughly doubled again        *)
(*  (67124 -> 201372).  Via TAIL2_END5_of51 + TAIL2_END4_of50 +     *)
(*  ESC_ERA_LAW_50 the ESC instances at every even R >= 1278 now    *)
(*  rest on TAIL2_END6 alone (ESC_ERA_LAW_51 below; Loop.v          *)
(*  Part 4l).                                                       *)
(* ================================================================= *)

Require Import List Bool Arith Lia ZArith.
Import ListNotations.
Require Import TM Sections Mirror TokenPass Recoord Era Esc Dev
               Grind Grind2 Grind3 Grind4 Grind5 Grind6 Grind7 Grind8
               Grind9 Grind10 Grind11 Grind12 Grind13 Grind14 Grind15
               Grind16 Grind17 Grind18.

(* Section equality: componentwise, arithmetic leaves by lia.      *)
Ltac sec_eq :=
  repeat (first [ solve [reflexivity] | solve [lia] | f_equal ]).

(* Closed-numeral arithmetic: literals >= 7426 are parsed as       *)
(* Nat.of_num_uint atoms, which lia cannot relate to variables;    *)
(* for purely closed <= goals the boolean check decides them.      *)
Ltac closearith :=
  first [ lia | apply Nat.leb_le; reflexivity ].

(* ----------------------------------------------------------------- *)
(* CASCADE51: the DIP5 spine over frame [47594; 9558; 1285; 774;    *)
(* 112; 20; 0] regrows onto TOP5, for an ARBITRARY tail w.          *)
(* Segment map (waypoints asserted verbatim in hsim51.py):         *)
(*   S1  PX2A + PUSH + TDN + TUP onto [1285; 774; 112; 20; 0]       *)
(*   S2  DIPGRIND (9556, 28476)                                     *)
(*   S3  PX2A onto [112; 20; 0]                                     *)
(*   S4  hGRIND 640, S5 POP, S6 pop12 9558                          *)
(*   S7  TUP, S8 hGRIND_even 10199 (front of pair 28474)            *)
(*   S9  TUP2_1 + TDN + TUP onto [10332; 112; 20; 0]                *)
(*   S10 CLEANG_even 14234, S11 TRANS2_1, S12 pop12 67122 = TOP5    *)
(* ----------------------------------------------------------------- *)

Lemma CASCADE51 : forall w,
  hsteps (HC [47594; 9558; 1285; 774; 112; 20; 0] 0 3 2
            (repeat (1, 2) 67120 ++ w) 1)
         (HB [20403; 10332; 112; 20; 0] 95597 1 134247 w 1).
Proof.
  intro w.
  (* S1: PX2A + PUSH + TDN + TUP onto [1285; 774; 112; 20; 0], pair (47588, 2) *)
  apply (hsteps_trans _ (HC [1285; 774; 112; 20; 0] 9556 3 2
                         ((47588, 2) :: (1, 1) :: repeat (1, 2) 67122 ++ w) 1)).
  {
    apply (hsteps_trans _ (HC [1285; 774; 112; 20; 0] 9557 47592 2
                           ((1, 1) :: (1, 2) :: (1, 2) :: repeat (1, 2) 67120 ++ w) 1)).
    {
      apply (hsteps_step _ (HC [1285; 774; 112; 20; 0] 9557 47592 2
                     ((1, 1) :: (1, 2) :: (1, 2) :: repeat (1, 2) 67120 ++ w) 1));
        [apply hPX2A | apply hsteps_refl].
    }
    apply (hsteps_trans _ (HC [1285; 774; 112; 20; 0] 9556 1 2
                           ((47590, 2) :: (1, 1) :: (1, 2) :: (1, 2) :: repeat (1, 2) 67120 ++ w) 1)).
    {
      apply (sPUSH [1285; 774; 112; 20; 0] 9556 47592
             ((1, 1) :: (1, 2) :: (1, 2) :: repeat (1, 2) 67120 ++ w) 1); closearith.
    }
    apply (hsteps_trans _ (HB [1285; 774; 112; 20; 0] 9556 1 4
                           ((47590, 2) :: (1, 1) :: (1, 2) :: (1, 2) :: repeat (1, 2) 67120 ++ w) 1)).
    {
      apply (sTDN [1285; 774; 112; 20; 0] 9556
             ((47590, 2) :: (1, 1) :: (1, 2) :: (1, 2) :: repeat (1, 2) 67120 ++ w) 1).
    }
    replace ((47588, 2) :: (1, 1) :: repeat (1, 2) 67122 ++ w)
      with ((47590 - 2, 2) :: (1, 1) :: (1, 2) :: (1, 2) :: repeat (1, 2) 67120 ++ w)
      by sec_eq.
    apply (sTUP [1285; 774; 112; 20; 0] 9556 4 47590 2
           ((1, 1) :: (1, 2) :: (1, 2) :: repeat (1, 2) 67120 ++ w) 1); closearith.
  }
  (* S2: DIPGRIND (9556, 28476) *)
  apply (hsteps_trans _ (HC [1285; 774; 112; 20; 0] 0 3 2
                         (repeat (1, 2) 9556 ++ (28476, 2) :: (1, 1) :: repeat (1, 2) 67122 ++ w) 1)).
  {
    apply (DIPGRIND 9556 28476 [1285; 774; 112; 20; 0]
           ((1, 1) :: repeat (1, 2) 67122 ++ w) 1); closearith.
  }
  (* S3: PX2A onto [112; 20; 0] *)
  apply (hsteps_trans _ (HC [112; 20; 0] 773 1283 2
                         ((1, 1) :: (1, 2) :: (1, 2) :: repeat (1, 2) 9556 ++ (28476, 2) :: (1, 1) :: repeat (1, 2) 67122 ++ w) 1)).
  {
    apply (hsteps_step _ (HC [112; 20; 0] 773 1283 2
                   ((1, 1) :: (1, 2) :: (1, 2) :: repeat (1, 2) 9556 ++ (28476, 2) :: (1, 1) :: repeat (1, 2) 67122 ++ w) 1));
      [apply hPX2A | apply hsteps_refl].
  }
  (* S4: hGRIND 640 *)
  apply (hsteps_trans _ (HB [112; 20; 0] 773 1 1286
                         ((1, 1) :: (1, 2) :: (1, 2) :: repeat (1, 2) 9556 ++ (28476, 2) :: (1, 1) :: repeat (1, 2) 67122 ++ w) 1)).
  {
    apply (hGRIND 640 [112; 20; 0] 773
           ((1, 1) :: (1, 2) :: (1, 2) :: repeat (1, 2) 9556 ++ (28476, 2) :: (1, 1) :: repeat (1, 2) 67122 ++ w) 1); closearith.
  }
  (* S5: POP (the (1, 1) pair) *)
  apply (hsteps_trans _ (HB [112; 20; 0] 774 1 1287
                         ((1, 2) :: (1, 2) :: repeat (1, 2) 9556 ++ (28476, 2) :: (1, 1) :: repeat (1, 2) 67122 ++ w) 1)).
  {
    apply (sPOP1 [112; 20; 0] 773 1286
           ((1, 2) :: (1, 2) :: repeat (1, 2) 9556 ++ (28476, 2) :: (1, 1) :: repeat (1, 2) 67122 ++ w) 1); closearith.
  }
  (* S6: pop12 9558 *)
  apply (hsteps_trans _ (HB [112; 20; 0] 10332 1 20403
                         ((28476, 2) :: (1, 1) :: repeat (1, 2) 67122 ++ w) 1)).
  {
    replace ((1, 2) :: (1, 2) :: repeat (1, 2) 9556 ++ (28476, 2) :: (1, 1) :: repeat (1, 2) 67122 ++ w)
      with (repeat (1, 2) 9558 ++ ((28476, 2) :: (1, 1) :: repeat (1, 2) 67122 ++ w))
      by sec_eq.
    apply (pop12 9558 [112; 20; 0] 774 1287
           ((28476, 2) :: (1, 1) :: repeat (1, 2) 67122 ++ w) 1); closearith.
  }
  (* S7: TUP (front of pair 28476, first half) *)
  apply (hsteps_trans _ (HC [112; 20; 0] 10332 20402 2
                         ((28474, 2) :: (1, 1) :: repeat (1, 2) 67122 ++ w) 1)).
  {
    replace ((28474, 2) :: (1, 1) :: repeat (1, 2) 67122 ++ w)
      with ((28476 - 2, 2) :: (1, 1) :: repeat (1, 2) 67122 ++ w)
      by sec_eq.
    apply (sTUP [112; 20; 0] 10332 20403 28476 2
           ((1, 1) :: repeat (1, 2) 67122 ++ w) 1); closearith.
  }
  (* S8: hGRIND_even 10199 (front of pair 28474, second half) *)
  apply (hsteps_trans _ (HB [112; 20; 0] 10331 1 20402
                         ((2, 2) :: (28474, 2) :: (1, 1) :: repeat (1, 2) 67122 ++ w) 1)).
  {
    apply (hGRIND_even 10199 [112; 20; 0] 10331
           ((28474, 2) :: (1, 1) :: repeat (1, 2) 67122 ++ w) 1); closearith.
  }
  (* S9: TUP2_1 + TDN + TUP onto [10332; 112; 20; 0], pair (28470, 2) *)
  apply (hsteps_trans _ (HC [10332; 112; 20; 0] 20402 3 2
                         ((28470, 2) :: (1, 1) :: repeat (1, 2) 67122 ++ w) 1)).
  {
    apply (hsteps_trans _ (HC [10332; 112; 20; 0] 20402 1 2
                           ((28472, 2) :: (1, 1) :: repeat (1, 2) 67122 ++ w) 1)).
    {
      replace ((28472, 2) :: (1, 1) :: repeat (1, 2) 67122 ++ w)
        with ((28474 - 2, 2) :: (1, 1) :: repeat (1, 2) 67122 ++ w)
        by sec_eq.
      apply (sTUP2_1 [112; 20; 0] 10331 20401 28474
             ((1, 1) :: repeat (1, 2) 67122 ++ w) 1); closearith.
    }
    apply (hsteps_trans _ (HB [10332; 112; 20; 0] 20402 1 4
                           ((28472, 2) :: (1, 1) :: repeat (1, 2) 67122 ++ w) 1)).
    {
      apply (sTDN [10332; 112; 20; 0] 20402
             ((28472, 2) :: (1, 1) :: repeat (1, 2) 67122 ++ w) 1).
    }
    replace ((28470, 2) :: (1, 1) :: repeat (1, 2) 67122 ++ w)
      with ((28472 - 2, 2) :: (1, 1) :: repeat (1, 2) 67122 ++ w)
      by sec_eq.
    apply (sTUP [10332; 112; 20; 0] 20402 4 28472 2
           ((1, 1) :: repeat (1, 2) 67122 ++ w) 1); closearith.
  }
  (* S10: CLEANG_even 14234 *)
  apply (hsteps_trans _ (HB [10332; 112; 20; 0] 20402 1 28474
                         ((2, 2) :: (1, 1) :: repeat (1, 2) 67122 ++ w) 1)).
  {
    apply (CLEANG_even 14234 [10332; 112; 20; 0] 20402
           ((1, 1) :: repeat (1, 2) 67122 ++ w) 1); closearith.
  }
  (* S11: TRANS2_1 *)
  apply (hsteps_trans _ (HB [20403; 10332; 112; 20; 0] 28475 1 3
                         (repeat (1, 2) 67122 ++ w) 1)).
  {
    apply (sTRANS2_1 [10332; 112; 20; 0] 20402 28473 1
           (repeat (1, 2) 67122 ++ w) 1); lia.
  }
  (* S12: pop12 67122 = TOP5 *)
  apply (pop12 67122 [20403; 10332; 112; 20; 0] 28475 3 w 1);
    closearith.
Qed.

(* ----------------------------------------------------------------- *)
(* TOP51_TO_TOP5: the TOP4 front + DIPGRIND (67120, r5) +           *)
(* CASCADE51, landing on TOP5 with the pair (2 * (j - 67123), 2).   *)
(* ----------------------------------------------------------------- *)

Lemma TOP51_TO_TOP5 : forall j beta, 67124 <= j -> 2 <= beta ->
  hsteps (HB [9558; 1285; 774; 112; 20; 0] 47594 1 67121
            ((2 * j, 2) :: (1, 1) :: repeat (1, 2) (beta - 1)) 1)
         (HB [20403; 10332; 112; 20; 0] 95597 1 134247
            ((2 * (j - 67123), 2) :: (1, 1)
             :: repeat (1, 2) (beta - 1)) 1).
Proof.
  intros j beta Hj Hb.
  (* lia cannot use Hj directly: 67124 is an of_num_uint atom,     *)
  (* unrelated in lia's eyes to the numerals below.  Derive a      *)
  (* numeral lower bound on j, and normalise the 67123/67124       *)
  (* atoms onto the single atom 67120 where an identity needs      *)
  (* them.                                                         *)
  assert (Hj4 : 4 <= j).
  { apply Nat.le_trans with 67124; [closearith | exact Hj]. }
  assert (Hr : 1 <= j - 67123).
  { change 67123 with (67124 - 1). lia. }
  assert (Heq : 2 * j - 6 = 2 * 67120 + 2 * (j - 67123)).
  { change 67123 with (67120 + 3).
    change 67124 with (67120 + 4) in Hj. lia. }
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
  apply (hsteps_trans _ (HC [47594; 9558; 1285; 774; 112; 20; 0]
    0 3 2 (repeat (1, 2) 67120
     ++ ((2 * (j - 67123), 2) :: (1, 1)
         :: repeat (1, 2) (beta - 1))) 1)).
  { rewrite Heq.
    apply (DIPGRIND 67120 (2 * (j - 67123))
           [47594; 9558; 1285; 774; 112; 20; 0]
           ((1, 1) :: repeat (1, 2) (beta - 1)) 1);
      [closearith | lia]. }
  apply (CASCADE51 ((2 * (j - 67123), 2) :: (1, 1)
                    :: repeat (1, 2) (beta - 1))).
Qed.

(* ----------------------------------------------------------------- *)
(* The TOP5 closings: r5 = 2, 4, 6 and band 5 (8 <= r5 <= 268498).  *)
(* ----------------------------------------------------------------- *)

Lemma TOP51_2 : forall beta, 2 <= beta ->
  hsteps (HB [20403; 10332; 112; 20; 0] 95597 1 134247
            ((2, 2) :: (1, 1) :: repeat (1, 2) (beta - 1)) 1)
         (HB [95598; 20403; 10332; 112; 20; 0]
            (134248 + (beta - 1)) 1 (2 * beta + 1) [] 1).
Proof.
  intros beta Hb.
  apply (hsteps_trans _ (HB [95598; 20403; 10332; 112; 20; 0]
    134248 1 3 (repeat (1, 2) (beta - 1)) 1)).
  { apply (sTRANS2_1 [20403; 10332; 112; 20; 0] 95597 134246 1
           (repeat (1, 2) (beta - 1)) 1); lia. }
  apply (CASCADE_POPFIN [95598; 20403; 10332; 112; 20; 0]
         134248 beta); lia.
Qed.

Lemma TOP51_4 : forall beta, 2 <= beta ->
  hsteps (HB [20403; 10332; 112; 20; 0] 95597 1 134247
            ((4, 2) :: (1, 1) :: repeat (1, 2) (beta - 1)) 1)
         (HB [134247; 95597; 20403; 10332; 112; 20; 0]
            (beta + 2) 1 (2 * beta + 1) [] 1).
Proof.
  intros beta Hb.
  apply (hsteps_trans _ (HC [20403; 10332; 112; 20; 0] 95597
    134246 2 ((2, 2) :: (1, 1) :: repeat (1, 2) (beta - 1)) 1)).
  { apply (sTUP [20403; 10332; 112; 20; 0] 95597 134247 4 2
           ((1, 1) :: repeat (1, 2) (beta - 1)) 1); closearith. }
  apply (hsteps_trans _ (HB [20403; 10332; 112; 20; 0] 95596
    1 134246 ((2, 2) :: (2, 2) :: (1, 1)
            :: repeat (1, 2) (beta - 1)) 1)).
  { apply (hGRIND_even 67121 [20403; 10332; 112; 20; 0] 95596
           ((2, 2) :: (1, 1) :: repeat (1, 2) (beta - 1)) 1);
      closearith. }
  apply (hsteps_trans _ (HB [134247; 95597; 20403; 10332; 112;
    20; 0] 3 1 3 (repeat (1, 2) (beta - 1)) 1)).
  { apply (hsteps_step _ (HB [134247; 95597; 20403; 10332; 112;
      20; 0] 3 1 3 (repeat (1, 2) (beta - 1)) 1));
      [apply hTRANS2_2; closearith | apply hsteps_refl]. }
  replace (beta + 2) with (3 + (beta - 1)) by lia.
  apply (CASCADE_POPFIN [134247; 95597; 20403; 10332; 112; 20; 0]
         3 beta); lia.
Qed.

Lemma TOP51_6 : forall beta, 2 <= beta ->
  hsteps (HB [20403; 10332; 112; 20; 0] 95597 1 134247
            ((6, 2) :: (1, 1) :: repeat (1, 2) (beta - 1)) 1)
         (HB [134247; 95597; 20403; 10332; 112; 20; 0]
            (beta + 4) 1 (2 * beta + 1) [] 1).
Proof.
  intros beta Hb.
  apply (hsteps_trans _ (HC [20403; 10332; 112; 20; 0] 95597
    134246 2 ((4, 2) :: (1, 1) :: repeat (1, 2) (beta - 1)) 1)).
  { apply (sTUP [20403; 10332; 112; 20; 0] 95597 134247 6 2
           ((1, 1) :: repeat (1, 2) (beta - 1)) 1); closearith. }
  apply (hsteps_trans _ (HB [20403; 10332; 112; 20; 0] 95596
    1 134246 ((2, 2) :: (4, 2) :: (1, 1)
            :: repeat (1, 2) (beta - 1)) 1)).
  { apply (hGRIND_even 67121 [20403; 10332; 112; 20; 0] 95596
           ((4, 2) :: (1, 1) :: repeat (1, 2) (beta - 1)) 1);
      closearith. }
  apply (hsteps_trans _ (HC [95597; 20403; 10332; 112; 20; 0]
    134246 1 2 ((2, 2) :: (1, 1) :: repeat (1, 2) (beta - 1)) 1)).
  { replace ((2, 2) :: (1, 1) :: repeat (1, 2) (beta - 1))
      with ((4 - 2, 2) :: (1, 1) :: repeat (1, 2) (beta - 1))
      by sec_eq.
    apply (sTUP2_1 [20403; 10332; 112; 20; 0] 95596 134245 4
           ((1, 1) :: repeat (1, 2) (beta - 1)) 1); lia. }
  apply (hsteps_trans _ (HB [95597; 20403; 10332; 112; 20; 0]
    134246 1 4 ((2, 2) :: (1, 1) :: repeat (1, 2) (beta - 1)) 1)).
  { apply (sTDN [95597; 20403; 10332; 112; 20; 0] 134246
           ((2, 2) :: (1, 1) :: repeat (1, 2) (beta - 1)) 1). }
  apply (hsteps_trans _ (HB [134247; 95597; 20403; 10332; 112;
    20; 0] 5 1 3 (repeat (1, 2) (beta - 1)) 1)).
  { apply (sTRANS2_1 [95597; 20403; 10332; 112; 20; 0] 134246
           3 1 (repeat (1, 2) (beta - 1)) 1); lia. }
  replace (beta + 4) with (5 + (beta - 1)) by lia.
  apply (CASCADE_POPFIN [134247; 95597; 20403; 10332; 112; 20; 0]
         5 beta); lia.
Qed.

Lemma TOP51_BAND : forall j beta, 4 <= j -> j <= 134249 -> 2 <= beta ->
  hsteps (HB [20403; 10332; 112; 20; 0] 95597 1 134247
            ((2 * j, 2) :: (1, 1) :: repeat (1, 2) (beta - 1)) 1)
         (HB [134247; 95597; 20403; 10332; 112; 20; 0]
            (2 * j + beta - 2) 1 (2 * beta + 1) [] 1).
Proof.
  intros j beta Hj1 Hj2 Hb.
  apply (hsteps_trans _ (HC [20403; 10332; 112; 20; 0] 95597
    134246 2 ((2 * j - 2, 2) :: (1, 1) :: repeat (1, 2) (beta - 1)) 1)).
  { apply (sTUP [20403; 10332; 112; 20; 0] 95597 134247 (2 * j) 2
           ((1, 1) :: repeat (1, 2) (beta - 1)) 1); closearith. }
  apply (hsteps_trans _ (HB [20403; 10332; 112; 20; 0] 95596
    1 134246 ((2, 2) :: (2 * j - 2, 2) :: (1, 1)
            :: repeat (1, 2) (beta - 1)) 1)).
  { apply (hGRIND_even 67121 [20403; 10332; 112; 20; 0] 95596
           ((2 * j - 2, 2) :: (1, 1) :: repeat (1, 2) (beta - 1))
           1); closearith. }
  apply (hsteps_trans _ (HC [95597; 20403; 10332; 112; 20; 0]
    134246 1 2 ((2 * j - 4, 2) :: (1, 1) :: repeat (1, 2) (beta - 1)) 1)).
  { replace ((2 * j - 4, 2) :: (1, 1) :: repeat (1, 2) (beta - 1))
      with ((2 * j - 2 - 2, 2) :: (1, 1) :: repeat (1, 2) (beta - 1))
      by sec_eq.
    apply (sTUP2_1 [20403; 10332; 112; 20; 0] 95596 134245
           (2 * j - 2) ((1, 1) :: repeat (1, 2) (beta - 1)) 1); lia. }
  apply (hsteps_trans _ (HB [95597; 20403; 10332; 112; 20; 0]
    134246 1 4 ((2 * j - 4, 2) :: (1, 1) :: repeat (1, 2) (beta - 1)) 1)).
  { apply (sTDN [95597; 20403; 10332; 112; 20; 0] 134246
           ((2 * j - 4, 2) :: (1, 1) :: repeat (1, 2) (beta - 1))
           1). }
  apply (hsteps_trans _ (HC [95597; 20403; 10332; 112; 20; 0]
    134246 3 2 ((2 * j - 6, 2) :: (1, 1) :: repeat (1, 2) (beta - 1)) 1)).
  { replace ((2 * j - 6, 2) :: (1, 1) :: repeat (1, 2) (beta - 1))
      with ((2 * j - 4 - 2, 2) :: (1, 1) :: repeat (1, 2) (beta - 1))
      by sec_eq.
    apply (sTUP [95597; 20403; 10332; 112; 20; 0] 134246 4
           (2 * j - 4) 2 ((1, 1) :: repeat (1, 2) (beta - 1)) 1);
      lia. }
  apply (hsteps_trans _ (HB [95597; 20403; 10332; 112; 20; 0]
    134246 1 (2 * j - 2)
    ((2, 2) :: (1, 1) :: repeat (1, 2) (beta - 1)) 1)).
  { replace (2 * j - 6) with (2 * (j - 4) + 2) by lia.
    replace (2 * j - 2) with (2 * (j - 4) + 6) by lia.
    apply (CLEANG_even (j - 4) [95597; 20403; 10332; 112; 20; 0]
           134246 ((1, 1) :: repeat (1, 2) (beta - 1)) 1).
    (* the floor (j - 4) + 1 <= 134246: route via j <= 134249 *)
    apply Nat.le_trans with (j - 3).
    - lia.
    - change 134246 with (134249 - 3).
      apply Nat.sub_le_mono_r. exact Hj2. }
  apply (hsteps_trans _ (HB [134247; 95597; 20403; 10332; 112;
    20; 0] (2 * j - 1) 1 3 (repeat (1, 2) (beta - 1)) 1)).
  { replace (2 * j - 2) with (S (2 * j - 3)) by lia.
    replace (2 * j - 1) with (S (S (2 * j - 3))) by lia.
    apply (sTRANS2_1 [95597; 20403; 10332; 112; 20; 0] 134246
           (2 * j - 3) 1 (repeat (1, 2) (beta - 1)) 1); lia. }
  replace (2 * j + beta - 2) with (2 * j - 1 + (beta - 1)) by lia.
  apply (CASCADE_POPFIN [134247; 95597; 20403; 10332; 112; 20; 0]
         (2 * j - 1) beta); lia.
Qed.

(* ----------------------------------------------------------------- *)
(* TAIL2_END6: the strictly smaller residual core -- the totality   *)
(* of the TOP5 state for r5 = 2 * j, j >= 134250 (r5 >= 268500),    *)
(* where the GRIND6 pair (r5 - 6, 2) at counter 134246 takes the    *)
(* DIPDESC boundary a sixth time.  A Definition (lemma              *)
(* parameter), never an axiom.                                      *)
(* ----------------------------------------------------------------- *)

Definition TAIL2_END6 : Prop :=
  forall j beta, 134250 <= j -> 2 <= beta ->
  exists pb A, beta <= A /\
    hsteps (HB [20403; 10332; 112; 20; 0] 95597 1 134247
              ((2 * j, 2) :: (1, 1) :: repeat (1, 2) (beta - 1)) 1)
           (HB pb A 1 (2 * beta + 1) [] 1).

(* ----------------------------------------------------------------- *)
(* TAIL2_END5_of51: TAIL2_END5, modulo TAIL2_END6.  The j-range     *)
(* splits at r5 = 2 * (j - 67123): the three small cases and        *)
(* band 5 are proved above; j - 67123 >= 134250 is the core.        *)
(* ----------------------------------------------------------------- *)

Lemma TAIL2_END5_of51 : TAIL2_END6 -> TAIL2_END5.
Proof.
  intros H6 j beta Hj Hb.
  pose proof (TOP51_TO_TOP5 j beta Hj Hb) as Htop.
  destruct (le_lt_dec 134250 (j - 67123)) as [Hbig | Hsmall].
  - (* j5 = j - 67123 >= 134250: the core *)
    destruct (H6 (j - 67123) beta Hbig Hb)
      as [pb [A [Ha Hsteps]]].
    exists pb, A. split; [exact Ha |].
    exact (hsteps_trans _ _ _ Htop Hsteps).
  - destruct (le_lt_dec 4 (j - 67123)) as [Hband | Htiny].
    + (* band 5: j5 = j - 67123, 4 <= j5 <= 134249 *)
      exists [134247; 95597; 20403; 10332; 112; 20; 0],
        (2 * (j - 67123) + beta - 2).
      split; [lia |].
      assert (Hj2 : j - 67123 <= 134249).
      { change 134250 with (S 134249) in Hsmall.
        apply (proj1 (Nat.lt_succ_r _ _) Hsmall). }
      exact (hsteps_trans _ _ _ Htop
               (TOP51_BAND (j - 67123) beta Hband Hj2 Hb)).
    + (* tiny: j5 = j - 67123 <= 3; j5 >= 1 since 67124 <= j *)
      destruct (Nat.eq_dec (j - 67123) 1) as [He | Hne].
      * (* r5 = 2 *)
        rewrite He in Htop.
        exists [95598; 20403; 10332; 112; 20; 0],
          (134248 + (beta - 1)).
        split; [change 134248 with (S 134247); lia |].
        exact (hsteps_trans _ _ _ Htop (TOP51_2 beta Hb)).
      * destruct (Nat.eq_dec (j - 67123) 2) as [He | Hne'].
        -- (* r5 = 4 *)
           rewrite He in Htop.
           exists [134247; 95597; 20403; 10332; 112; 20; 0],
             (beta + 2).
           split; [lia |].
           exact (hsteps_trans _ _ _ Htop (TOP51_4 beta Hb)).
        -- destruct (Nat.eq_dec (j - 67123) 3) as [He | Hne''].
           ++ (* r5 = 6 *)
              rewrite He in Htop.
              exists [134247; 95597; 20403; 10332; 112; 20; 0],
                (beta + 4).
              split; [lia |].
              exact (hsteps_trans _ _ _ Htop (TOP51_6 beta Hb)).
           ++ (* j5 = 0, contradicting 67124 <= j *)
              exfalso.
              assert (H0 : j - 67123 = 0) by lia.
              change 67124 with (S 67123) in Hj.
              lia.
Qed.

(* ----------------------------------------------------------------- *)
(* ESC_ERA_LAW_51: the phase-8 ESC era law at every even            *)
(* R >= 1278, modulo TAIL2_END6 alone.                              *)
(* ----------------------------------------------------------------- *)

Lemma ESC_ERA_LAW_51 : TAIL2_END6 ->
  forall M beta, 616 <= M -> 2 <= beta ->
  exists n c pb a,
    run n (esc_src (2 * M + 52) (beta - 2)) = Some c
    /\ cfg_sim c (rcsec (false :: repeat true (S a) ++ enc pb)
                        (2 * beta + 2) [(1, 2)])
    /\ beta <= a.
Proof.
  intros H M beta HM Hb.
  apply (ESC_ERA_LAW_50 (TAIL2_END5_of51 H) M beta HM Hb).
Qed.

(* ----------------------------------------------------------------- *)
(* Assumption audit                                                  *)
(* ----------------------------------------------------------------- *)

Print Assumptions CASCADE51.
Print Assumptions TOP51_TO_TOP5.
Print Assumptions TOP51_2.
Print Assumptions TOP51_4.
Print Assumptions TOP51_6.
Print Assumptions TOP51_BAND.
Print Assumptions TAIL2_END5_of51.
Print Assumptions ESC_ERA_LAW_51.
