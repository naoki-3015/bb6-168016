(* ================================================================= *)
(*  Grind17.v -- Phase 49: the third re-descent cascade of the      *)
(*  TOP2 state, mechanised as a fixed parse, closing TAIL2_END3     *)
(*  for the whole first j-band 16302 <= j <= 48906 (TOP2            *)
(*  parameters) and reducing the rest to a strictly smaller core    *)
(*  at the TOP3 state.                                              *)
(*                                                                  *)
(*  Phase 48 left the ESC side of H_LOOP resting on TAIL2_END3      *)
(*  (Grind16.v): the totality of the TOP2 state                     *)
(*                                                                  *)
(*    TOP2(j, beta) = HB [1589; 225; 40; 14; 5] 10430 1 16299       *)
(*                    ((2j, 2) :: (1, 1) :: (1, 2)^(beta - 1))      *)
(*                                                                  *)
(*  for j >= 16302.  There the GRIND3 pair (2j - 6, 2) at counter   *)
(*  16298 exceeds the CLEANG_even floor and takes the DIPDESC       *)
(*  boundary a third time.  Phase 49 traces the walk                *)
(*  (rocq/hsim49.py, ALL PASS: the 49-waypoint chain below          *)
(*  asserted verbatim at (j, beta) in {(16302, 2), (16302, 3),      *)
(*  (16303, 2), (20000, 2), (48906, 2)}; TOP3 finals and the        *)
(*  cycle-4 fence asserted too; a junk-tail probe confirms          *)
(*  CASCADE49 is stated for an arbitrary tail).                     *)
(*                                                                  *)
(*  FINDING: the third descent is again a FIXED parse, uniform      *)
(*  in (j, beta) -- not a return to TOP2 or TOP.  Writing           *)
(*  r3 = 2j - 32602 >= 2 for the DIPGRIND residue at GRIND3:        *)
(*                                                                  *)
(*    TOP2 --front (TUP, hGRIND_even 8147, TUP2_1, TDN, TUP)-->     *)
(*      GRIND3 = HC [10430; 1589; 225; 40; 14; 5] 16298 3 2         *)
(*                 ((2j - 6, 2) :: tail)                            *)
(*    --DIPGRIND (16298, r3)-->                                     *)
(*      HC [10430; 1589; ...] 0 3 2 ((1, 2)^16298 ++ W),            *)
(*        W = ((r3, 2) :: (1, 1) :: (1, 2)^(beta - 1))              *)
(*    --CASCADE49 (fixed parse, arbitrary tail)-->                  *)
(*      TOP3 = HB [7493; 3816; 259; 93; 50; 14; 5] 16899 1 32603 W. *)
(*                                                                  *)
(*  CASCADE49 descends the TOP2 frame's own blocks by DIPGRIND +    *)
(*  PX2A levels (1587, 7250), (38, 143), (3, 2), regrows onto       *)
(*  [5], then works through the regrown frames with fronts          *)
(*  (TUP + hGRIND_even t + TUP2_1 + TDN + TUP) at pairs 143,        *)
(*  7250, 1563, 13, 1333, 16, 843, 600, DIPGRIND levels             *)
(*  (3322, 600), (52, 1563), (112, 1333), (3, 45), (13, 13),        *)
(*  (242, 843), (18, 108), (43, 16), (3, 6), three PX2Bgen dips,    *)
(*  three bottom-frame excursions (PX2B0 + PUSHX regrowth),         *)
(*  CLEANG_odd grinds 67, 2, 417 and CLEANG_even grinds 4, 296,     *)
(*  landing on TOP3.  No harness-caught correction this phase:      *)
(*  the characterisation matched the Phase 46-48 pattern on the     *)
(*  first full run (after the walker was made streaming -- the      *)
(*  recording walker was OOM-killed on ~50k-pair stacks).           *)
(*                                                                  *)
(*  TOP3 then closes by the size of r3 = 2 * j3 (j3 = j - 16301     *)
(*  in TOP3's own parameter):                                      *)
(*    r3 = 2:       TRANS2_1 + CASCADE_POPFIN, A = 32603 + beta;    *)
(*    r3 = 4:       TUP + hGRIND_even 16299 + TRANS2_2              *)
(*                    + CASCADE_POPFIN, A = beta + 2;               *)
(*    r3 = 6:       TUP + hGRIND_even 16299 + TUP2_1 + TDN          *)
(*                    + TRANS2_1 + CASCADE_POPFIN, A = beta + 4;    *)
(*    8 <= r3 <= 65210 (band 3): TUP + hGRIND_even 16299 + TUP2_1   *)
(*      + TDN + TUP onto GRIND4 = HC [16899; 7493; ...] 32602 3 2   *)
(*      ((r3 - 6, 2) :: tail), whose pair grinds CLEANLY by         *)
(*      CLEANG_even (floor (r3 - 8)/2 + 1 <= 32602, exactly         *)
(*      r3 <= 65210), then TRANS2_1 + CASCADE_POPFIN,               *)
(*      A = r3 + beta - 2, frame [32603; 16899; 7493; ...].         *)
(*      (The band counter is again the shuttle moved into the       *)
(*      counter slot by TUP2_1: 32602, not 16899.)                  *)
(*                                                                  *)
(*  For r3 >= 65212 (j3 >= 32606, i.e. TOP2-parameter               *)
(*  j >= 48907) the pair (r3 - 6, 2) at counter 32602 exceeds       *)
(*  the CLEANG_even floor and the rounds take the DIPDESC           *)
(*  boundary a FOURTH time (hsim49 Part 3: the GRIND4 state and     *)
(*  the DIPGRIND (32602, r3 - 65210) landing both occur at          *)
(*  j = 48907, 49000, 60000).  The fourth descent is expected to    *)
(*  be a NEW cascade with different constants, so no cycle          *)
(*  induction in the current vocabulary closes it; what remains     *)
(*  is the strictly smaller core                                    *)
(*                                                                  *)
(*    TAIL2_END4: the totality of the ONE pair (2j, 2) at the ONE   *)
(*    fixed TOP3 state HB [7493; 3816; 259; 93; 50; 14; 5] 16899    *)
(*    1 32603, for j >= 32606 (r3 = 2j >= 65212), beta >= 2.        *)
(*                                                                  *)
(*  The core's range shrank from [16302, infty) to [48907, infty)   *)
(*  in TOP2 parameters; the band width roughly doubled again       *)
(*  (16302 -> 48906).  Via TAIL2_END3_of49 + TAIL2_END2_of48 +      *)
(*  ESC_ERA_LAW_48 the ESC instances at every even R >= 1278 now    *)
(*  rest on TAIL2_END4 alone (ESC_ERA_LAW_49 below; Loop.v          *)
(*  Part 4j).                                                       *)
(* ================================================================= *)

Require Import List Bool Arith Lia ZArith.
Import ListNotations.
Require Import TM Sections Mirror TokenPass Recoord Era Esc Dev
               Grind Grind2 Grind3 Grind4 Grind5 Grind6 Grind7 Grind8
               Grind9 Grind10 Grind11 Grind12 Grind13 Grind14 Grind15
               Grind16.

(* Section equality: componentwise, arithmetic leaves by lia.      *)
Ltac sec_eq :=
  repeat (first [ solve [reflexivity] | solve [lia] | f_equal ]).

(* Closed-numeral arithmetic: literals >= 7426 are parsed as       *)
(* Nat.of_num_uint atoms, which lia cannot relate to variables;    *)
(* for purely closed <= goals the boolean check decides them.      *)
Ltac closearith :=
  first [ lia | apply Nat.leb_le; reflexivity ].

(* ----------------------------------------------------------------- *)
(* CASCADE49: the DIP3 spine over frame [10430; 1589; 225; 40;      *)
(* 14; 5] regrows onto TOP3, for an ARBITRARY tail w.  Segment      *)
(* map (waypoints asserted verbatim in hsim49.py):                  *)
(*   S1  PX2A + PUSH + TDN + TUP onto [225; 40; 14; 5],             *)
(*       pair (10424, 2)                                            *)
(*   S2  DIPGRIND (1587, 7250)                                      *)
(*   S3  PX2A + PUSH + TDN + TUP onto [14; 5], pair (219, 2)        *)
(*   S4  DIPGRIND (38, 143)                                         *)
(*   S5  PX2A + PUSH + TDN + TUP onto [], pair (8, 2)               *)
(*   S6  DIPGRIND (3, 2)                                            *)
(*   S7  PUSHX + pop12 3 + TRANS2_1 regrowth onto [5]               *)
(*   S8  pop12 40, front(143) onto [54; 5]                          *)
(*   S9  CLEANG_odd 67                                              *)
(*   S10 pop12 1 + POP + pop12 1589, front(7250) onto               *)
(*       [1673; 54; 5]                                              *)
(*   S11 DIPGRIND (3322, 600)                                       *)
(*   S12 PX2A + PUSH + TDN + TUP onto [5], pair (1667, 2)           *)
(*   S13 DIPGRIND (52, 1563)                                        *)
(*   S14 PX2Bgen onto [0]                                           *)
(*   S15 pop12 1 + POP + pop12 54, front(1563) onto [59; 0]         *)
(*   S16 DIPGRIND (112, 1333)                                       *)
(*   S17 PX2A0 + TUP + TDN + TUP at [0], pair (51, 2)               *)
(*   S18 DIPGRIND (3, 45)                                           *)
(*   S19 PX2B0 + pop12 4 at []                                      *)
(*   S20 bottom front (TUP + PUSH + TDN + TUP), pair (8, 2)         *)
(*   S21 DIPGRIND (3, 2)                                            *)
(*   S22 PUSHX + pop12 3 + TUP2_1 + TDN + TUP onto [5],             *)
(*       pair (39, 2)                                               *)
(*   S23 DIPGRIND (13, 13)                                          *)
(*   S24 PX2Bgen onto [0]                                           *)
(*   S25 pop12 1 + POP + pop12 15, front(13) onto [20; 0]           *)
(*   S26 CLEANG_odd 2                                               *)
(*   S27 pop12 1 + POP + pop12 114, front(1333) onto [150; 20; 0]   *)
(*   S28 DIPGRIND (242, 843)                                        *)
(*   S29 PX2A + PUSH + TDN + TUP onto [0], pair (144, 2)            *)
(*   S30 DIPGRIND (18, 108)                                         *)
(*   S31 PX2B0 + pop12 19 at []                                     *)
(*   S32 bottom front, pair (38, 2)                                 *)
(*   S33 DIPGRIND (18, 2)                                           *)
(*   S34 PUSHX + pop12 18 + TUP2_1 + TDN + TUP onto [20],           *)
(*       pair (102, 2)                                              *)
(*   S35 DIPGRIND (43, 16)                                          *)
(*   S36 PX2Bgen + TUP + TDN + TUP at [0], pair (12, 2)             *)
(*   S37 DIPGRIND (3, 6)                                            *)
(*   S38 PX2B0 + pop12 4 at []                                      *)
(*   S39 bottom front, pair (8, 2)                                  *)
(*   S40 DIPGRIND (3, 2)                                            *)
(*   S41 PUSHX + pop12 3 + TUP2_1 + TDN + TRANS2_1 regrowth         *)
(*       onto [14; 5]                                               *)
(*   S42 pop12 45, front(16) onto [50; 14; 5]                       *)
(*   S43 CLEANG_even 4 + TRANS2_1 onto [93; 50; 14; 5]              *)
(*   S44 pop12 244, front(843) onto [259; 93; 50; 14; 5]            *)
(*   S45 CLEANG_odd 417                                             *)
(*   S46 pop12 1 + POP + pop12 3324, front(600) onto                *)
(*       [3816; 259; 93; 50; 14; 5]                                 *)
(*   S47 CLEANG_even 296 + TRANS2_1 onto [7493; 3816; ...] +        *)
(*       pop12 16300 = TOP3                                         *)
(* A "front(g)" is TUP + hGRIND_even t + TUP2_1 + TDN + TUP on      *)
(* the pair (g, 2), the TOP48 front shape.                          *)
(* ----------------------------------------------------------------- *)

Lemma CASCADE49 : forall w,
  hsteps (HC [10430; 1589; 225; 40; 14; 5] 0 3 2
            (repeat (1, 2) 16298 ++ w) 1)
         (HB [7493; 3816; 259; 93; 50; 14; 5] 16899 1 32603 w 1).
Proof.
  intro w.
  (* S1: PX2A + PUSH + TDN + TUP onto [225; 40; 14; 5] *)
  apply (hsteps_trans _ (HC [225; 40; 14; 5] 1587 3 2
    ((10424, 2) :: (1, 1) :: repeat (1, 2) 16300 ++ w) 1)).
  { apply (hsteps_trans _ (HC [225; 40; 14; 5] 1588 10428 2
      ((1, 1) :: (1, 2) :: (1, 2)
       :: repeat (1, 2) 16298 ++ w) 1)).
    { apply (hsteps_step _ (HC [225; 40; 14; 5] 1588 10428 2
                 ((1, 1) :: (1, 2) :: (1, 2)
                  :: repeat (1, 2) 16298 ++ w) 1));
        [apply hPX2A | apply hsteps_refl]. }
    apply (hsteps_trans _ (HC [225; 40; 14; 5] 1587 1 2
      ((10426, 2) :: (1, 1) :: (1, 2) :: (1, 2)
       :: repeat (1, 2) 16298 ++ w) 1)).
    { apply (sPUSH [225; 40; 14; 5] 1587 10428
             ((1, 1) :: (1, 2) :: (1, 2)
              :: repeat (1, 2) 16298 ++ w) 1); closearith. }
    apply (hsteps_trans _ (HB [225; 40; 14; 5] 1587 1 4
      ((10426, 2) :: (1, 1) :: (1, 2) :: (1, 2)
       :: repeat (1, 2) 16298 ++ w) 1)).
    { apply (sTDN [225; 40; 14; 5] 1587
             ((10426, 2) :: (1, 1) :: (1, 2) :: (1, 2)
              :: repeat (1, 2) 16298 ++ w) 1). }
    replace ((10424, 2) :: (1, 1) :: repeat (1, 2) 16300 ++ w)
      with ((10426 - 2, 2) :: (1, 1) :: (1, 2) :: (1, 2)
            :: repeat (1, 2) 16298 ++ w)
      by sec_eq.
    apply (sTUP [225; 40; 14; 5] 1587 4 10426 2
           ((1, 1) :: (1, 2) :: (1, 2)
            :: repeat (1, 2) 16298 ++ w) 1); closearith. }
  (* S2: DIPGRIND (1587, 7250) *)
  apply (hsteps_trans _ (HC [225; 40; 14; 5] 0 3 2
    (repeat (1, 2) 1587
     ++ (7250, 2) :: (1, 1) :: repeat (1, 2) 16300 ++ w) 1)).
  { apply (DIPGRIND 1587 7250 [225; 40; 14; 5]
           ((1, 1) :: repeat (1, 2) 16300 ++ w) 1); closearith. }
  (* S3: PX2A + PUSH + TDN + TUP onto [14; 5] *)
  apply (hsteps_trans _ (HC [14; 5] 38 3 2
    ((219, 2) :: (1, 1) :: repeat (1, 2) 1589
     ++ (7250, 2) :: (1, 1) :: repeat (1, 2) 16300 ++ w) 1)).
  { apply (hsteps_trans _ (HC [14; 5] 39 223 2
      ((1, 1) :: (1, 2) :: (1, 2) :: repeat (1, 2) 1587
       ++ (7250, 2) :: (1, 1) :: repeat (1, 2) 16300 ++ w) 1)).
    { apply (hsteps_step _ (HC [14; 5] 39 223 2
                 ((1, 1) :: (1, 2) :: (1, 2)
                  :: repeat (1, 2) 1587
                  ++ (7250, 2) :: (1, 1)
                  :: repeat (1, 2) 16300 ++ w) 1));
        [apply hPX2A | apply hsteps_refl]. }
    apply (hsteps_trans _ (HC [14; 5] 38 1 2
      ((221, 2) :: (1, 1) :: (1, 2) :: (1, 2)
       :: repeat (1, 2) 1587
       ++ (7250, 2) :: (1, 1) :: repeat (1, 2) 16300 ++ w) 1)).
    { apply (sPUSH [14; 5] 38 223
             ((1, 1) :: (1, 2) :: (1, 2) :: repeat (1, 2) 1587
              ++ (7250, 2) :: (1, 1)
              :: repeat (1, 2) 16300 ++ w) 1); closearith. }
    apply (hsteps_trans _ (HB [14; 5] 38 1 4
      ((221, 2) :: (1, 1) :: (1, 2) :: (1, 2)
       :: repeat (1, 2) 1587
       ++ (7250, 2) :: (1, 1) :: repeat (1, 2) 16300 ++ w) 1)).
    { apply (sTDN [14; 5] 38
             ((221, 2) :: (1, 1) :: (1, 2) :: (1, 2)
              :: repeat (1, 2) 1587
              ++ (7250, 2) :: (1, 1)
              :: repeat (1, 2) 16300 ++ w) 1). }
    replace ((219, 2) :: (1, 1) :: repeat (1, 2) 1589
             ++ (7250, 2) :: (1, 1) :: repeat (1, 2) 16300 ++ w)
      with ((221 - 2, 2) :: (1, 1) :: (1, 2) :: (1, 2)
            :: repeat (1, 2) 1587
            ++ (7250, 2) :: (1, 1) :: repeat (1, 2) 16300 ++ w)
      by sec_eq.
    apply (sTUP [14; 5] 38 4 221 2
           ((1, 1) :: (1, 2) :: (1, 2) :: repeat (1, 2) 1587
            ++ (7250, 2) :: (1, 1)
            :: repeat (1, 2) 16300 ++ w) 1); closearith. }
  (* S4: DIPGRIND (38, 143) *)
  apply (hsteps_trans _ (HC [14; 5] 0 3 2
    (repeat (1, 2) 38
     ++ (143, 2) :: (1, 1) :: repeat (1, 2) 1589
     ++ (7250, 2) :: (1, 1) :: repeat (1, 2) 16300 ++ w) 1)).
  { apply (DIPGRIND 38 143 [14; 5]
           ((1, 1) :: repeat (1, 2) 1589
            ++ (7250, 2) :: (1, 1) :: repeat (1, 2) 16300 ++ w)
           1); closearith. }
  (* S5: PX2A + PUSH + TDN + TUP onto [] *)
  apply (hsteps_trans _ (HC [] 3 3 2
    ((8, 2) :: (1, 1) :: repeat (1, 2) 40
     ++ (143, 2) :: (1, 1) :: repeat (1, 2) 1589
     ++ (7250, 2) :: (1, 1) :: repeat (1, 2) 16300 ++ w) 1)).
  { apply (hsteps_trans _ (HC [] 4 12 2
      ((1, 1) :: (1, 2) :: (1, 2) :: repeat (1, 2) 38
       ++ (143, 2) :: (1, 1) :: repeat (1, 2) 1589
       ++ (7250, 2) :: (1, 1) :: repeat (1, 2) 16300 ++ w) 1)).
    { apply (hsteps_step _ (HC [] 4 12 2
                 ((1, 1) :: (1, 2) :: (1, 2)
                  :: repeat (1, 2) 38
                  ++ (143, 2) :: (1, 1) :: repeat (1, 2) 1589
                  ++ (7250, 2) :: (1, 1)
                  :: repeat (1, 2) 16300 ++ w) 1));
        [apply hPX2A | apply hsteps_refl]. }
    apply (hsteps_trans _ (HC [] 3 1 2
      ((10, 2) :: (1, 1) :: (1, 2) :: (1, 2)
       :: repeat (1, 2) 38
       ++ (143, 2) :: (1, 1) :: repeat (1, 2) 1589
       ++ (7250, 2) :: (1, 1) :: repeat (1, 2) 16300 ++ w) 1)).
    { apply (sPUSH [] 3 12
             ((1, 1) :: (1, 2) :: (1, 2) :: repeat (1, 2) 38
              ++ (143, 2) :: (1, 1) :: repeat (1, 2) 1589
              ++ (7250, 2) :: (1, 1)
              :: repeat (1, 2) 16300 ++ w) 1); closearith. }
    apply (hsteps_trans _ (HB [] 3 1 4
      ((10, 2) :: (1, 1) :: (1, 2) :: (1, 2)
       :: repeat (1, 2) 38
       ++ (143, 2) :: (1, 1) :: repeat (1, 2) 1589
       ++ (7250, 2) :: (1, 1) :: repeat (1, 2) 16300 ++ w) 1)).
    { apply (sTDN [] 3
             ((10, 2) :: (1, 1) :: (1, 2) :: (1, 2)
              :: repeat (1, 2) 38
              ++ (143, 2) :: (1, 1) :: repeat (1, 2) 1589
              ++ (7250, 2) :: (1, 1)
              :: repeat (1, 2) 16300 ++ w) 1). }
    replace ((8, 2) :: (1, 1) :: repeat (1, 2) 40
             ++ (143, 2) :: (1, 1) :: repeat (1, 2) 1589
             ++ (7250, 2) :: (1, 1) :: repeat (1, 2) 16300 ++ w)
      with ((10 - 2, 2) :: (1, 1) :: (1, 2) :: (1, 2)
            :: repeat (1, 2) 38
            ++ (143, 2) :: (1, 1) :: repeat (1, 2) 1589
            ++ (7250, 2) :: (1, 1) :: repeat (1, 2) 16300 ++ w)
      by sec_eq.
    apply (sTUP [] 3 4 10 2
           ((1, 1) :: (1, 2) :: (1, 2) :: repeat (1, 2) 38
            ++ (143, 2) :: (1, 1) :: repeat (1, 2) 1589
            ++ (7250, 2) :: (1, 1)
            :: repeat (1, 2) 16300 ++ w) 1); closearith. }
  (* S6: DIPGRIND (3, 2) *)
  apply (hsteps_trans _ (HC [] 0 3 2
    (repeat (1, 2) 3
     ++ (2, 2) :: (1, 1) :: repeat (1, 2) 40
     ++ (143, 2) :: (1, 1) :: repeat (1, 2) 1589
     ++ (7250, 2) :: (1, 1) :: repeat (1, 2) 16300 ++ w) 1)).
  { apply (DIPGRIND 3 2 []
           ((1, 1) :: repeat (1, 2) 40
            ++ (143, 2) :: (1, 1) :: repeat (1, 2) 1589
            ++ (7250, 2) :: (1, 1) :: repeat (1, 2) 16300 ++ w)
           1); closearith. }
  (* S7: PUSHX + pop12 3 + TRANS2_1 regrowth onto [5] *)
  apply (hsteps_trans _ (HB [5] 14 1 3
    (repeat (1, 2) 40
     ++ (143, 2) :: (1, 1) :: repeat (1, 2) 1589
     ++ (7250, 2) :: (1, 1) :: repeat (1, 2) 16300 ++ w) 1)).
  { apply (hsteps_trans _ (HB [] 1 1 7
      (repeat (1, 2) 3
       ++ (2, 2) :: (1, 1) :: repeat (1, 2) 40
       ++ (143, 2) :: (1, 1) :: repeat (1, 2) 1589
       ++ (7250, 2) :: (1, 1) :: repeat (1, 2) 16300 ++ w) 1)).
    { apply (hsteps_step _ (HB [] 1 1 7
                 (repeat (1, 2) 3
                  ++ (2, 2) :: (1, 1) :: repeat (1, 2) 40
                  ++ (143, 2) :: (1, 1) :: repeat (1, 2) 1589
                  ++ (7250, 2) :: (1, 1)
                  :: repeat (1, 2) 16300 ++ w) 1));
        [apply hPUSHX | apply hsteps_refl]. }
    apply (hsteps_trans _ (HB [] 4 1 13
      ((2, 2) :: (1, 1) :: repeat (1, 2) 40
       ++ (143, 2) :: (1, 1) :: repeat (1, 2) 1589
       ++ (7250, 2) :: (1, 1) :: repeat (1, 2) 16300 ++ w) 1)).
    { apply (pop12 3 [] 1 7
             ((2, 2) :: (1, 1) :: repeat (1, 2) 40
              ++ (143, 2) :: (1, 1) :: repeat (1, 2) 1589
              ++ (7250, 2) :: (1, 1)
              :: repeat (1, 2) 16300 ++ w) 1); closearith. }
    apply (sTRANS2_1 [] 4 12 1
           (repeat (1, 2) 40
            ++ (143, 2) :: (1, 1) :: repeat (1, 2) 1589
            ++ (7250, 2) :: (1, 1) :: repeat (1, 2) 16300 ++ w)
           1); closearith. }
  (* S8: pop12 40, front(143) onto [54; 5] *)
  apply (hsteps_trans _ (HC [54; 5] 82 3 2
    ((137, 2) :: (1, 1) :: repeat (1, 2) 1589
     ++ (7250, 2) :: (1, 1) :: repeat (1, 2) 16300 ++ w) 1)).
  { apply (hsteps_trans _ (HB [5] 54 1 83
      ((143, 2) :: (1, 1) :: repeat (1, 2) 1589
       ++ (7250, 2) :: (1, 1) :: repeat (1, 2) 16300 ++ w) 1)).
    { apply (pop12 40 [5] 14 3
             ((143, 2) :: (1, 1) :: repeat (1, 2) 1589
              ++ (7250, 2) :: (1, 1)
              :: repeat (1, 2) 16300 ++ w) 1); closearith. }
    apply (hsteps_trans _ (HC [5] 54 82 2
      ((141, 2) :: (1, 1) :: repeat (1, 2) 1589
       ++ (7250, 2) :: (1, 1) :: repeat (1, 2) 16300 ++ w) 1)).
    { apply (sTUP [5] 54 83 143 2
             ((1, 1) :: repeat (1, 2) 1589
              ++ (7250, 2) :: (1, 1)
              :: repeat (1, 2) 16300 ++ w) 1); closearith. }
    apply (hsteps_trans _ (HB [5] 53 1 82
      ((2, 2) :: (141, 2) :: (1, 1) :: repeat (1, 2) 1589
       ++ (7250, 2) :: (1, 1) :: repeat (1, 2) 16300 ++ w) 1)).
    { apply (hGRIND_even 39 [5] 53
             ((141, 2) :: (1, 1) :: repeat (1, 2) 1589
              ++ (7250, 2) :: (1, 1)
              :: repeat (1, 2) 16300 ++ w) 1); closearith. }
    apply (hsteps_trans _ (HC [54; 5] 82 1 2
      ((139, 2) :: (1, 1) :: repeat (1, 2) 1589
       ++ (7250, 2) :: (1, 1) :: repeat (1, 2) 16300 ++ w) 1)).
    { replace ((139, 2) :: (1, 1) :: repeat (1, 2) 1589
               ++ (7250, 2) :: (1, 1)
               :: repeat (1, 2) 16300 ++ w)
        with ((141 - 2, 2) :: (1, 1) :: repeat (1, 2) 1589
              ++ (7250, 2) :: (1, 1)
              :: repeat (1, 2) 16300 ++ w)
        by sec_eq.
      apply (sTUP2_1 [5] 53 81 141
             ((1, 1) :: repeat (1, 2) 1589
              ++ (7250, 2) :: (1, 1)
              :: repeat (1, 2) 16300 ++ w) 1); closearith. }
    apply (hsteps_trans _ (HB [54; 5] 82 1 4
      ((139, 2) :: (1, 1) :: repeat (1, 2) 1589
       ++ (7250, 2) :: (1, 1) :: repeat (1, 2) 16300 ++ w) 1)).
    { apply (sTDN [54; 5] 82
             ((139, 2) :: (1, 1) :: repeat (1, 2) 1589
              ++ (7250, 2) :: (1, 1)
              :: repeat (1, 2) 16300 ++ w) 1). }
    replace ((137, 2) :: (1, 1) :: repeat (1, 2) 1589
             ++ (7250, 2) :: (1, 1) :: repeat (1, 2) 16300 ++ w)
      with ((139 - 2, 2) :: (1, 1) :: repeat (1, 2) 1589
            ++ (7250, 2) :: (1, 1) :: repeat (1, 2) 16300 ++ w)
      by sec_eq.
    apply (sTUP [54; 5] 82 4 139 2
           ((1, 1) :: repeat (1, 2) 1589
            ++ (7250, 2) :: (1, 1) :: repeat (1, 2) 16300 ++ w)
           1); closearith. }
  (* S9: CLEANG_odd 67 *)
  apply (hsteps_trans _ (HB [54; 5] 82 1 142
    ((1, 2) :: (1, 1) :: repeat (1, 2) 1589
     ++ (7250, 2) :: (1, 1) :: repeat (1, 2) 16300 ++ w) 1)).
  { apply (CLEANG_odd 67 [54; 5] 82
           ((1, 1) :: repeat (1, 2) 1589
            ++ (7250, 2) :: (1, 1) :: repeat (1, 2) 16300 ++ w)
           1); closearith. }
  (* S10: pop12 1 + POP + pop12 1589, front(7250) onto [1673; 54; 5] *)
  apply (hsteps_trans _ (HC [1673; 54; 5] 3322 3 2
    ((7244, 2) :: (1, 1) :: repeat (1, 2) 16300 ++ w) 1)).
  { apply (hsteps_trans _ (HB [54; 5] 83 1 144
      ((1, 1) :: repeat (1, 2) 1589
       ++ (7250, 2) :: (1, 1) :: repeat (1, 2) 16300 ++ w) 1)).
    { replace ((1, 2) :: (1, 1) :: repeat (1, 2) 1589
               ++ (7250, 2) :: (1, 1)
               :: repeat (1, 2) 16300 ++ w)
        with (repeat (1, 2) 1
              ++ ((1, 1) :: repeat (1, 2) 1589
                  ++ (7250, 2) :: (1, 1)
                  :: repeat (1, 2) 16300 ++ w))
        by sec_eq.
      apply (pop12 1 [54; 5] 82 142
             ((1, 1) :: repeat (1, 2) 1589
              ++ (7250, 2) :: (1, 1)
              :: repeat (1, 2) 16300 ++ w) 1); closearith. }
    apply (hsteps_trans _ (HB [54; 5] 84 1 145
      (repeat (1, 2) 1589
       ++ (7250, 2) :: (1, 1) :: repeat (1, 2) 16300 ++ w) 1)).
    { apply (sPOP1 [54; 5] 83 144
             (repeat (1, 2) 1589
              ++ (7250, 2) :: (1, 1)
              :: repeat (1, 2) 16300 ++ w) 1); closearith. }
    apply (hsteps_trans _ (HB [54; 5] 1673 1 3323
      ((7250, 2) :: (1, 1) :: repeat (1, 2) 16300 ++ w) 1)).
    { apply (pop12 1589 [54; 5] 84 145
             ((7250, 2) :: (1, 1) :: repeat (1, 2) 16300 ++ w)
             1); closearith. }
    apply (hsteps_trans _ (HC [54; 5] 1673 3322 2
      ((7248, 2) :: (1, 1) :: repeat (1, 2) 16300 ++ w) 1)).
    { apply (sTUP [54; 5] 1673 3323 7250 2
             ((1, 1) :: repeat (1, 2) 16300 ++ w) 1);
        closearith. }
    apply (hsteps_trans _ (HB [54; 5] 1672 1 3322
      ((2, 2) :: (7248, 2) :: (1, 1)
       :: repeat (1, 2) 16300 ++ w) 1)).
    { apply (hGRIND_even 1659 [54; 5] 1672
             ((7248, 2) :: (1, 1) :: repeat (1, 2) 16300 ++ w)
             1); closearith. }
    apply (hsteps_trans _ (HC [1673; 54; 5] 3322 1 2
      ((7246, 2) :: (1, 1) :: repeat (1, 2) 16300 ++ w) 1)).
    { replace ((7246, 2) :: (1, 1) :: repeat (1, 2) 16300 ++ w)
        with ((7248 - 2, 2) :: (1, 1)
              :: repeat (1, 2) 16300 ++ w)
        by sec_eq.
      apply (sTUP2_1 [54; 5] 1672 3321 7248
             ((1, 1) :: repeat (1, 2) 16300 ++ w) 1);
        closearith. }
    apply (hsteps_trans _ (HB [1673; 54; 5] 3322 1 4
      ((7246, 2) :: (1, 1) :: repeat (1, 2) 16300 ++ w) 1)).
    { apply (sTDN [1673; 54; 5] 3322
             ((7246, 2) :: (1, 1) :: repeat (1, 2) 16300 ++ w)
             1). }
    replace ((7244, 2) :: (1, 1) :: repeat (1, 2) 16300 ++ w)
      with ((7246 - 2, 2) :: (1, 1) :: repeat (1, 2) 16300 ++ w)
      by sec_eq.
    apply (sTUP [1673; 54; 5] 3322 4 7246 2
           ((1, 1) :: repeat (1, 2) 16300 ++ w) 1);
      closearith. }
  (* S11: DIPGRIND (3322, 600) *)
  apply (hsteps_trans _ (HC [1673; 54; 5] 0 3 2
    (repeat (1, 2) 3322
     ++ (600, 2) :: (1, 1) :: repeat (1, 2) 16300 ++ w) 1)).
  { apply (DIPGRIND 3322 600 [1673; 54; 5]
           ((1, 1) :: repeat (1, 2) 16300 ++ w) 1); closearith. }
  (* S12: PX2A + PUSH + TDN + TUP onto [5] *)
  apply (hsteps_trans _ (HC [5] 52 3 2
    ((1667, 2) :: (1, 1) :: repeat (1, 2) 3324
     ++ (600, 2) :: (1, 1) :: repeat (1, 2) 16300 ++ w) 1)).
  { apply (hsteps_trans _ (HC [5] 53 1671 2
      ((1, 1) :: (1, 2) :: (1, 2) :: repeat (1, 2) 3322
       ++ (600, 2) :: (1, 1) :: repeat (1, 2) 16300 ++ w) 1)).
    { apply (hsteps_step _ (HC [5] 53 1671 2
                 ((1, 1) :: (1, 2) :: (1, 2)
                  :: repeat (1, 2) 3322
                  ++ (600, 2) :: (1, 1)
                  :: repeat (1, 2) 16300 ++ w) 1));
        [apply hPX2A | apply hsteps_refl]. }
    apply (hsteps_trans _ (HC [5] 52 1 2
      ((1669, 2) :: (1, 1) :: (1, 2) :: (1, 2)
       :: repeat (1, 2) 3322
       ++ (600, 2) :: (1, 1) :: repeat (1, 2) 16300 ++ w) 1)).
    { apply (sPUSH [5] 52 1671
             ((1, 1) :: (1, 2) :: (1, 2) :: repeat (1, 2) 3322
              ++ (600, 2) :: (1, 1)
              :: repeat (1, 2) 16300 ++ w) 1); closearith. }
    apply (hsteps_trans _ (HB [5] 52 1 4
      ((1669, 2) :: (1, 1) :: (1, 2) :: (1, 2)
       :: repeat (1, 2) 3322
       ++ (600, 2) :: (1, 1) :: repeat (1, 2) 16300 ++ w) 1)).
    { apply (sTDN [5] 52
             ((1669, 2) :: (1, 1) :: (1, 2) :: (1, 2)
              :: repeat (1, 2) 3322
              ++ (600, 2) :: (1, 1)
              :: repeat (1, 2) 16300 ++ w) 1). }
    replace ((1667, 2) :: (1, 1) :: repeat (1, 2) 3324
             ++ (600, 2) :: (1, 1) :: repeat (1, 2) 16300 ++ w)
      with ((1669 - 2, 2) :: (1, 1) :: (1, 2) :: (1, 2)
            :: repeat (1, 2) 3322
            ++ (600, 2) :: (1, 1) :: repeat (1, 2) 16300 ++ w)
      by sec_eq.
    apply (sTUP [5] 52 4 1669 2
           ((1, 1) :: (1, 2) :: (1, 2) :: repeat (1, 2) 3322
            ++ (600, 2) :: (1, 1)
            :: repeat (1, 2) 16300 ++ w) 1); closearith. }
  (* S13: DIPGRIND (52, 1563) *)
  apply (hsteps_trans _ (HC [5] 0 3 2
    (repeat (1, 2) 52
     ++ (1563, 2) :: (1, 1) :: repeat (1, 2) 3324
     ++ (600, 2) :: (1, 1) :: repeat (1, 2) 16300 ++ w) 1)).
  { apply (DIPGRIND 52 1563 [5]
           ((1, 1) :: repeat (1, 2) 3324
            ++ (600, 2) :: (1, 1) :: repeat (1, 2) 16300 ++ w)
           1); closearith. }
  (* S14: PX2Bgen onto [0] (raw landing form) *)
  apply (hsteps_trans _ (HB [0] 3 1 2
    ((1, 2) :: (1, 1) :: (1, 2) :: (1, 2) :: repeat (1, 2) 52
     ++ (1563, 2) :: (1, 1) :: repeat (1, 2) 3324
     ++ (600, 2) :: (1, 1) :: repeat (1, 2) 16300 ++ w) 1)).
  { apply (hsteps_step _ (HB [0] 3 1 2
               ((1, 2) :: (1, 1) :: (1, 2) :: (1, 2)
                :: repeat (1, 2) 52
                ++ (1563, 2) :: (1, 1) :: repeat (1, 2) 3324
                ++ (600, 2) :: (1, 1)
                :: repeat (1, 2) 16300 ++ w) 1));
        [apply hPX2Bgen | apply hsteps_refl]. }
  (* S15: pop12 1 + POP + pop12 54, front(1563) onto [59; 0] *)
  apply (hsteps_trans _ (HC [59; 0] 112 3 2
    ((1557, 2) :: (1, 1) :: repeat (1, 2) 3324
     ++ (600, 2) :: (1, 1) :: repeat (1, 2) 16300 ++ w) 1)).
  { apply (hsteps_trans _ (HB [0] 4 1 4
      ((1, 1) :: (1, 2) :: (1, 2) :: repeat (1, 2) 52
       ++ (1563, 2) :: (1, 1) :: repeat (1, 2) 3324
       ++ (600, 2) :: (1, 1) :: repeat (1, 2) 16300 ++ w) 1)).
    { replace ((1, 2) :: (1, 1) :: (1, 2) :: (1, 2)
               :: repeat (1, 2) 52
               ++ (1563, 2) :: (1, 1) :: repeat (1, 2) 3324
               ++ (600, 2) :: (1, 1)
               :: repeat (1, 2) 16300 ++ w)
        with (repeat (1, 2) 1
              ++ ((1, 1) :: (1, 2) :: (1, 2)
                  :: repeat (1, 2) 52
                  ++ (1563, 2) :: (1, 1) :: repeat (1, 2) 3324
                  ++ (600, 2) :: (1, 1)
                  :: repeat (1, 2) 16300 ++ w))
        by sec_eq.
      apply (pop12 1 [0] 3 2
             ((1, 1) :: (1, 2) :: (1, 2) :: repeat (1, 2) 52
              ++ (1563, 2) :: (1, 1) :: repeat (1, 2) 3324
              ++ (600, 2) :: (1, 1)
              :: repeat (1, 2) 16300 ++ w) 1); closearith. }
    apply (hsteps_trans _ (HB [0] 5 1 5
      ((1, 2) :: (1, 2) :: repeat (1, 2) 52
       ++ (1563, 2) :: (1, 1) :: repeat (1, 2) 3324
       ++ (600, 2) :: (1, 1) :: repeat (1, 2) 16300 ++ w) 1)).
    { apply (sPOP1 [0] 4 4
             ((1, 2) :: (1, 2) :: repeat (1, 2) 52
              ++ (1563, 2) :: (1, 1) :: repeat (1, 2) 3324
              ++ (600, 2) :: (1, 1)
              :: repeat (1, 2) 16300 ++ w) 1); closearith. }
    apply (hsteps_trans _ (HB [0] 59 1 113
      ((1563, 2) :: (1, 1) :: repeat (1, 2) 3324
       ++ (600, 2) :: (1, 1) :: repeat (1, 2) 16300 ++ w) 1)).
    { replace ((1, 2) :: (1, 2) :: repeat (1, 2) 52
               ++ (1563, 2) :: (1, 1) :: repeat (1, 2) 3324
               ++ (600, 2) :: (1, 1)
               :: repeat (1, 2) 16300 ++ w)
        with (repeat (1, 2) 54
              ++ ((1563, 2) :: (1, 1) :: repeat (1, 2) 3324
                  ++ (600, 2) :: (1, 1)
                  :: repeat (1, 2) 16300 ++ w))
        by sec_eq.
      apply (pop12 54 [0] 5 5
             ((1563, 2) :: (1, 1) :: repeat (1, 2) 3324
              ++ (600, 2) :: (1, 1)
              :: repeat (1, 2) 16300 ++ w) 1); closearith. }
    apply (hsteps_trans _ (HC [0] 59 112 2
      ((1561, 2) :: (1, 1) :: repeat (1, 2) 3324
       ++ (600, 2) :: (1, 1) :: repeat (1, 2) 16300 ++ w) 1)).
    { apply (sTUP [0] 59 113 1563 2
             ((1, 1) :: repeat (1, 2) 3324
              ++ (600, 2) :: (1, 1)
              :: repeat (1, 2) 16300 ++ w) 1); closearith. }
    apply (hsteps_trans _ (HB [0] 58 1 112
      ((2, 2) :: (1561, 2) :: (1, 1) :: repeat (1, 2) 3324
       ++ (600, 2) :: (1, 1) :: repeat (1, 2) 16300 ++ w) 1)).
    { apply (hGRIND_even 54 [0] 58
             ((1561, 2) :: (1, 1) :: repeat (1, 2) 3324
              ++ (600, 2) :: (1, 1)
              :: repeat (1, 2) 16300 ++ w) 1); closearith. }
    apply (hsteps_trans _ (HC [59; 0] 112 1 2
      ((1559, 2) :: (1, 1) :: repeat (1, 2) 3324
       ++ (600, 2) :: (1, 1) :: repeat (1, 2) 16300 ++ w) 1)).
    { replace ((1559, 2) :: (1, 1) :: repeat (1, 2) 3324
               ++ (600, 2) :: (1, 1)
               :: repeat (1, 2) 16300 ++ w)
        with ((1561 - 2, 2) :: (1, 1) :: repeat (1, 2) 3324
              ++ (600, 2) :: (1, 1)
              :: repeat (1, 2) 16300 ++ w)
        by sec_eq.
      apply (sTUP2_1 [0] 58 111 1561
             ((1, 1) :: repeat (1, 2) 3324
              ++ (600, 2) :: (1, 1)
              :: repeat (1, 2) 16300 ++ w) 1); closearith. }
    apply (hsteps_trans _ (HB [59; 0] 112 1 4
      ((1559, 2) :: (1, 1) :: repeat (1, 2) 3324
       ++ (600, 2) :: (1, 1) :: repeat (1, 2) 16300 ++ w) 1)).
    { apply (sTDN [59; 0] 112
             ((1559, 2) :: (1, 1) :: repeat (1, 2) 3324
              ++ (600, 2) :: (1, 1)
              :: repeat (1, 2) 16300 ++ w) 1). }
    replace ((1557, 2) :: (1, 1) :: repeat (1, 2) 3324
             ++ (600, 2) :: (1, 1) :: repeat (1, 2) 16300 ++ w)
      with ((1559 - 2, 2) :: (1, 1) :: repeat (1, 2) 3324
            ++ (600, 2) :: (1, 1) :: repeat (1, 2) 16300 ++ w)
      by sec_eq.
    apply (sTUP [59; 0] 112 4 1559 2
           ((1, 1) :: repeat (1, 2) 3324
            ++ (600, 2) :: (1, 1) :: repeat (1, 2) 16300 ++ w)
           1); closearith. }
  (* S16: DIPGRIND (112, 1333) *)
  apply (hsteps_trans _ (HC [59; 0] 0 3 2
    (repeat (1, 2) 112
     ++ (1333, 2) :: (1, 1) :: repeat (1, 2) 3324
     ++ (600, 2) :: (1, 1) :: repeat (1, 2) 16300 ++ w) 1)).
  { apply (DIPGRIND 112 1333 [59; 0]
           ((1, 1) :: repeat (1, 2) 3324
            ++ (600, 2) :: (1, 1) :: repeat (1, 2) 16300 ++ w)
           1); closearith. }
  (* S17: PX2A0 + TUP + TDN + TUP at [0] *)
  apply (hsteps_trans _ (HC [0] 3 3 2
    ((51, 2) :: (1, 1) :: repeat (1, 2) 114
     ++ (1333, 2) :: (1, 1) :: repeat (1, 2) 3324
     ++ (600, 2) :: (1, 1) :: repeat (1, 2) 16300 ++ w) 1)).
  { apply (hsteps_trans _ (HB [0] 3 1 2
      ((55, 2) :: (1, 1) :: (1, 2) :: (1, 2)
       :: repeat (1, 2) 112
       ++ (1333, 2) :: (1, 1) :: repeat (1, 2) 3324
       ++ (600, 2) :: (1, 1) :: repeat (1, 2) 16300 ++ w) 1)).
    { apply (hsteps_step _ (HB [0] 3 1 2
                 ((55, 2) :: (1, 1) :: (1, 2) :: (1, 2)
                  :: repeat (1, 2) 112
                  ++ (1333, 2) :: (1, 1) :: repeat (1, 2) 3324
                  ++ (600, 2) :: (1, 1)
                  :: repeat (1, 2) 16300 ++ w) 1));
        [apply hPX2A0 | apply hsteps_refl]. }
    apply (hsteps_trans _ (HC [0] 3 1 2
      ((53, 2) :: (1, 1) :: (1, 2) :: (1, 2)
       :: repeat (1, 2) 112
       ++ (1333, 2) :: (1, 1) :: repeat (1, 2) 3324
       ++ (600, 2) :: (1, 1) :: repeat (1, 2) 16300 ++ w) 1)).
    { apply (sTUP [0] 3 2 55 2
             ((1, 1) :: (1, 2) :: (1, 2) :: repeat (1, 2) 112
              ++ (1333, 2) :: (1, 1) :: repeat (1, 2) 3324
              ++ (600, 2) :: (1, 1)
              :: repeat (1, 2) 16300 ++ w) 1); closearith. }
    apply (hsteps_trans _ (HB [0] 3 1 4
      ((53, 2) :: (1, 1) :: (1, 2) :: (1, 2)
       :: repeat (1, 2) 112
       ++ (1333, 2) :: (1, 1) :: repeat (1, 2) 3324
       ++ (600, 2) :: (1, 1) :: repeat (1, 2) 16300 ++ w) 1)).
    { apply (sTDN [0] 3
             ((53, 2) :: (1, 1) :: (1, 2) :: (1, 2)
              :: repeat (1, 2) 112
              ++ (1333, 2) :: (1, 1) :: repeat (1, 2) 3324
              ++ (600, 2) :: (1, 1)
              :: repeat (1, 2) 16300 ++ w) 1). }
    replace ((51, 2) :: (1, 1) :: repeat (1, 2) 114
             ++ (1333, 2) :: (1, 1) :: repeat (1, 2) 3324
             ++ (600, 2) :: (1, 1) :: repeat (1, 2) 16300 ++ w)
      with ((53 - 2, 2) :: (1, 1) :: (1, 2) :: (1, 2)
            :: repeat (1, 2) 112
            ++ (1333, 2) :: (1, 1) :: repeat (1, 2) 3324
            ++ (600, 2) :: (1, 1) :: repeat (1, 2) 16300 ++ w)
      by sec_eq.
    apply (sTUP [0] 3 4 53 2
           ((1, 1) :: (1, 2) :: (1, 2) :: repeat (1, 2) 112
            ++ (1333, 2) :: (1, 1) :: repeat (1, 2) 3324
            ++ (600, 2) :: (1, 1)
            :: repeat (1, 2) 16300 ++ w) 1); closearith. }
  (* S18: DIPGRIND (3, 45) *)
  apply (hsteps_trans _ (HC [0] 0 3 2
    (repeat (1, 2) 3
     ++ (45, 2) :: (1, 1) :: repeat (1, 2) 114
     ++ (1333, 2) :: (1, 1) :: repeat (1, 2) 3324
     ++ (600, 2) :: (1, 1) :: repeat (1, 2) 16300 ++ w) 1)).
  { apply (DIPGRIND 3 45 [0]
           ((1, 1) :: repeat (1, 2) 114
            ++ (1333, 2) :: (1, 1) :: repeat (1, 2) 3324
            ++ (600, 2) :: (1, 1) :: repeat (1, 2) 16300 ++ w)
           1); closearith. }
  (* S19: PX2B0 + pop12 4 at [] *)
  apply (hsteps_trans _ (HB [] 4 1 13
    ((45, 2) :: (1, 1) :: repeat (1, 2) 114
     ++ (1333, 2) :: (1, 1) :: repeat (1, 2) 3324
     ++ (600, 2) :: (1, 1) :: repeat (1, 2) 16300 ++ w) 1)).
  { apply (hsteps_trans _ (HB [] 0 1 5
      (repeat (1, 2) 4
       ++ (45, 2) :: (1, 1) :: repeat (1, 2) 114
       ++ (1333, 2) :: (1, 1) :: repeat (1, 2) 3324
       ++ (600, 2) :: (1, 1) :: repeat (1, 2) 16300 ++ w) 1)).
    { apply (hsteps_step _ (HB [] 0 1 5
                 (repeat (1, 2) 4
                  ++ (45, 2) :: (1, 1) :: repeat (1, 2) 114
                  ++ (1333, 2) :: (1, 1) :: repeat (1, 2) 3324
                  ++ (600, 2) :: (1, 1)
                  :: repeat (1, 2) 16300 ++ w) 1));
        [apply hPX2B0 | apply hsteps_refl]. }
    apply (pop12 4 [] 0 5
           ((45, 2) :: (1, 1) :: repeat (1, 2) 114
            ++ (1333, 2) :: (1, 1) :: repeat (1, 2) 3324
            ++ (600, 2) :: (1, 1) :: repeat (1, 2) 16300 ++ w)
           1); closearith. }
  (* S20: bottom front (TUP + PUSH + TDN + TUP) *)
  apply (hsteps_trans _ (HC [] 3 3 2
    ((8, 2) :: (43, 2) :: (1, 1) :: repeat (1, 2) 114
     ++ (1333, 2) :: (1, 1) :: repeat (1, 2) 3324
     ++ (600, 2) :: (1, 1) :: repeat (1, 2) 16300 ++ w) 1)).
  { apply (hsteps_trans _ (HC [] 4 12 2
      ((43, 2) :: (1, 1) :: repeat (1, 2) 114
       ++ (1333, 2) :: (1, 1) :: repeat (1, 2) 3324
       ++ (600, 2) :: (1, 1) :: repeat (1, 2) 16300 ++ w) 1)).
    { apply (sTUP [] 4 13 45 2
             ((1, 1) :: repeat (1, 2) 114
              ++ (1333, 2) :: (1, 1) :: repeat (1, 2) 3324
              ++ (600, 2) :: (1, 1)
              :: repeat (1, 2) 16300 ++ w) 1); closearith. }
    apply (hsteps_trans _ (HC [] 3 1 2
      ((10, 2) :: (43, 2) :: (1, 1) :: repeat (1, 2) 114
       ++ (1333, 2) :: (1, 1) :: repeat (1, 2) 3324
       ++ (600, 2) :: (1, 1) :: repeat (1, 2) 16300 ++ w) 1)).
    { apply (sPUSH [] 3 12
             ((43, 2) :: (1, 1) :: repeat (1, 2) 114
              ++ (1333, 2) :: (1, 1) :: repeat (1, 2) 3324
              ++ (600, 2) :: (1, 1)
              :: repeat (1, 2) 16300 ++ w) 1); closearith. }
    apply (hsteps_trans _ (HB [] 3 1 4
      ((10, 2) :: (43, 2) :: (1, 1) :: repeat (1, 2) 114
       ++ (1333, 2) :: (1, 1) :: repeat (1, 2) 3324
       ++ (600, 2) :: (1, 1) :: repeat (1, 2) 16300 ++ w) 1)).
    { apply (sTDN [] 3
             ((10, 2) :: (43, 2) :: (1, 1) :: repeat (1, 2) 114
              ++ (1333, 2) :: (1, 1) :: repeat (1, 2) 3324
              ++ (600, 2) :: (1, 1)
              :: repeat (1, 2) 16300 ++ w) 1). }
    apply (sTUP [] 3 4 10 2
           ((43, 2) :: (1, 1) :: repeat (1, 2) 114
            ++ (1333, 2) :: (1, 1) :: repeat (1, 2) 3324
            ++ (600, 2) :: (1, 1)
            :: repeat (1, 2) 16300 ++ w) 1); closearith. }
  (* S21: DIPGRIND (3, 2) *)
  apply (hsteps_trans _ (HC [] 0 3 2
    (repeat (1, 2) 3
     ++ (2, 2) :: (43, 2) :: (1, 1) :: repeat (1, 2) 114
     ++ (1333, 2) :: (1, 1) :: repeat (1, 2) 3324
     ++ (600, 2) :: (1, 1) :: repeat (1, 2) 16300 ++ w) 1)).
  { apply (DIPGRIND 3 2 []
           ((43, 2) :: (1, 1) :: repeat (1, 2) 114
            ++ (1333, 2) :: (1, 1) :: repeat (1, 2) 3324
            ++ (600, 2) :: (1, 1) :: repeat (1, 2) 16300 ++ w)
           1); closearith. }
  (* S22: PUSHX + pop12 3 + TUP2_1 + TDN + TUP onto [5] *)
  apply (hsteps_trans _ (HC [5] 13 3 2
    ((39, 2) :: (1, 1) :: repeat (1, 2) 114
     ++ (1333, 2) :: (1, 1) :: repeat (1, 2) 3324
     ++ (600, 2) :: (1, 1) :: repeat (1, 2) 16300 ++ w) 1)).
  { apply (hsteps_trans _ (HB [] 1 1 7
      (repeat (1, 2) 3
       ++ (2, 2) :: (43, 2) :: (1, 1) :: repeat (1, 2) 114
       ++ (1333, 2) :: (1, 1) :: repeat (1, 2) 3324
       ++ (600, 2) :: (1, 1) :: repeat (1, 2) 16300 ++ w) 1)).
    { apply (hsteps_step _ (HB [] 1 1 7
                 (repeat (1, 2) 3
                  ++ (2, 2) :: (43, 2) :: (1, 1)
                  :: repeat (1, 2) 114
                  ++ (1333, 2) :: (1, 1) :: repeat (1, 2) 3324
                  ++ (600, 2) :: (1, 1)
                  :: repeat (1, 2) 16300 ++ w) 1));
        [apply hPUSHX | apply hsteps_refl]. }
    apply (hsteps_trans _ (HB [] 4 1 13
      ((2, 2) :: (43, 2) :: (1, 1) :: repeat (1, 2) 114
       ++ (1333, 2) :: (1, 1) :: repeat (1, 2) 3324
       ++ (600, 2) :: (1, 1) :: repeat (1, 2) 16300 ++ w) 1)).
    { apply (pop12 3 [] 1 7
             ((2, 2) :: (43, 2) :: (1, 1) :: repeat (1, 2) 114
              ++ (1333, 2) :: (1, 1) :: repeat (1, 2) 3324
              ++ (600, 2) :: (1, 1)
              :: repeat (1, 2) 16300 ++ w) 1); closearith. }
    apply (hsteps_trans _ (HC [5] 13 1 2
      ((41, 2) :: (1, 1) :: repeat (1, 2) 114
       ++ (1333, 2) :: (1, 1) :: repeat (1, 2) 3324
       ++ (600, 2) :: (1, 1) :: repeat (1, 2) 16300 ++ w) 1)).
    { replace ((41, 2) :: (1, 1) :: repeat (1, 2) 114
               ++ (1333, 2) :: (1, 1) :: repeat (1, 2) 3324
               ++ (600, 2) :: (1, 1)
               :: repeat (1, 2) 16300 ++ w)
        with ((43 - 2, 2) :: (1, 1) :: repeat (1, 2) 114
              ++ (1333, 2) :: (1, 1) :: repeat (1, 2) 3324
              ++ (600, 2) :: (1, 1)
              :: repeat (1, 2) 16300 ++ w)
        by sec_eq.
      apply (sTUP2_1 [] 4 12 43
             ((1, 1) :: repeat (1, 2) 114
              ++ (1333, 2) :: (1, 1) :: repeat (1, 2) 3324
              ++ (600, 2) :: (1, 1)
              :: repeat (1, 2) 16300 ++ w) 1); closearith. }
    apply (hsteps_trans _ (HB [5] 13 1 4
      ((41, 2) :: (1, 1) :: repeat (1, 2) 114
       ++ (1333, 2) :: (1, 1) :: repeat (1, 2) 3324
       ++ (600, 2) :: (1, 1) :: repeat (1, 2) 16300 ++ w) 1)).
    { apply (sTDN [5] 13
             ((41, 2) :: (1, 1) :: repeat (1, 2) 114
              ++ (1333, 2) :: (1, 1) :: repeat (1, 2) 3324
              ++ (600, 2) :: (1, 1)
              :: repeat (1, 2) 16300 ++ w) 1). }
    replace ((39, 2) :: (1, 1) :: repeat (1, 2) 114
             ++ (1333, 2) :: (1, 1) :: repeat (1, 2) 3324
             ++ (600, 2) :: (1, 1) :: repeat (1, 2) 16300 ++ w)
      with ((41 - 2, 2) :: (1, 1) :: repeat (1, 2) 114
            ++ (1333, 2) :: (1, 1) :: repeat (1, 2) 3324
            ++ (600, 2) :: (1, 1) :: repeat (1, 2) 16300 ++ w)
      by sec_eq.
    apply (sTUP [5] 13 4 41 2
           ((1, 1) :: repeat (1, 2) 114
            ++ (1333, 2) :: (1, 1) :: repeat (1, 2) 3324
            ++ (600, 2) :: (1, 1)
            :: repeat (1, 2) 16300 ++ w) 1); closearith. }
  (* S23: DIPGRIND (13, 13) *)
  apply (hsteps_trans _ (HC [5] 0 3 2
    (repeat (1, 2) 13
     ++ (13, 2) :: (1, 1) :: repeat (1, 2) 114
     ++ (1333, 2) :: (1, 1) :: repeat (1, 2) 3324
     ++ (600, 2) :: (1, 1) :: repeat (1, 2) 16300 ++ w) 1)).
  { apply (DIPGRIND 13 13 [5]
           ((1, 1) :: repeat (1, 2) 114
            ++ (1333, 2) :: (1, 1) :: repeat (1, 2) 3324
            ++ (600, 2) :: (1, 1) :: repeat (1, 2) 16300 ++ w)
           1); closearith. }
  (* S24: PX2Bgen onto [0] (raw landing form) *)
  apply (hsteps_trans _ (HB [0] 3 1 2
    ((1, 2) :: (1, 1) :: (1, 2) :: (1, 2) :: repeat (1, 2) 13
     ++ (13, 2) :: (1, 1) :: repeat (1, 2) 114
     ++ (1333, 2) :: (1, 1) :: repeat (1, 2) 3324
     ++ (600, 2) :: (1, 1) :: repeat (1, 2) 16300 ++ w) 1)).
  { apply (hsteps_step _ (HB [0] 3 1 2
               ((1, 2) :: (1, 1) :: (1, 2) :: (1, 2)
                :: repeat (1, 2) 13
                ++ (13, 2) :: (1, 1) :: repeat (1, 2) 114
                ++ (1333, 2) :: (1, 1) :: repeat (1, 2) 3324
                ++ (600, 2) :: (1, 1)
                :: repeat (1, 2) 16300 ++ w) 1));
        [apply hPX2Bgen | apply hsteps_refl]. }
  (* S25: pop12 1 + POP + pop12 15, front(13) onto [20; 0] *)
  apply (hsteps_trans _ (HC [20; 0] 34 3 2
    ((7, 2) :: (1, 1) :: repeat (1, 2) 114
     ++ (1333, 2) :: (1, 1) :: repeat (1, 2) 3324
     ++ (600, 2) :: (1, 1) :: repeat (1, 2) 16300 ++ w) 1)).
  { apply (hsteps_trans _ (HB [0] 4 1 4
      ((1, 1) :: (1, 2) :: (1, 2) :: repeat (1, 2) 13
       ++ (13, 2) :: (1, 1) :: repeat (1, 2) 114
       ++ (1333, 2) :: (1, 1) :: repeat (1, 2) 3324
       ++ (600, 2) :: (1, 1) :: repeat (1, 2) 16300 ++ w) 1)).
    { replace ((1, 2) :: (1, 1) :: (1, 2) :: (1, 2)
               :: repeat (1, 2) 13
               ++ (13, 2) :: (1, 1) :: repeat (1, 2) 114
               ++ (1333, 2) :: (1, 1) :: repeat (1, 2) 3324
               ++ (600, 2) :: (1, 1)
               :: repeat (1, 2) 16300 ++ w)
        with (repeat (1, 2) 1
              ++ ((1, 1) :: (1, 2) :: (1, 2)
                  :: repeat (1, 2) 13
                  ++ (13, 2) :: (1, 1) :: repeat (1, 2) 114
                  ++ (1333, 2) :: (1, 1) :: repeat (1, 2) 3324
                  ++ (600, 2) :: (1, 1)
                  :: repeat (1, 2) 16300 ++ w))
        by sec_eq.
      apply (pop12 1 [0] 3 2
             ((1, 1) :: (1, 2) :: (1, 2) :: repeat (1, 2) 13
              ++ (13, 2) :: (1, 1) :: repeat (1, 2) 114
              ++ (1333, 2) :: (1, 1) :: repeat (1, 2) 3324
              ++ (600, 2) :: (1, 1)
              :: repeat (1, 2) 16300 ++ w) 1); closearith. }
    apply (hsteps_trans _ (HB [0] 5 1 5
      ((1, 2) :: (1, 2) :: repeat (1, 2) 13
       ++ (13, 2) :: (1, 1) :: repeat (1, 2) 114
       ++ (1333, 2) :: (1, 1) :: repeat (1, 2) 3324
       ++ (600, 2) :: (1, 1) :: repeat (1, 2) 16300 ++ w) 1)).
    { apply (sPOP1 [0] 4 4
             ((1, 2) :: (1, 2) :: repeat (1, 2) 13
              ++ (13, 2) :: (1, 1) :: repeat (1, 2) 114
              ++ (1333, 2) :: (1, 1) :: repeat (1, 2) 3324
              ++ (600, 2) :: (1, 1)
              :: repeat (1, 2) 16300 ++ w) 1); closearith. }
    apply (hsteps_trans _ (HB [0] 20 1 35
      ((13, 2) :: (1, 1) :: repeat (1, 2) 114
       ++ (1333, 2) :: (1, 1) :: repeat (1, 2) 3324
       ++ (600, 2) :: (1, 1) :: repeat (1, 2) 16300 ++ w) 1)).
    { replace ((1, 2) :: (1, 2) :: repeat (1, 2) 13
               ++ (13, 2) :: (1, 1) :: repeat (1, 2) 114
               ++ (1333, 2) :: (1, 1) :: repeat (1, 2) 3324
               ++ (600, 2) :: (1, 1)
               :: repeat (1, 2) 16300 ++ w)
        with (repeat (1, 2) 15
              ++ ((13, 2) :: (1, 1) :: repeat (1, 2) 114
                  ++ (1333, 2) :: (1, 1) :: repeat (1, 2) 3324
                  ++ (600, 2) :: (1, 1)
                  :: repeat (1, 2) 16300 ++ w))
        by sec_eq.
      apply (pop12 15 [0] 5 5
             ((13, 2) :: (1, 1) :: repeat (1, 2) 114
              ++ (1333, 2) :: (1, 1) :: repeat (1, 2) 3324
              ++ (600, 2) :: (1, 1)
              :: repeat (1, 2) 16300 ++ w) 1); closearith. }
    apply (hsteps_trans _ (HC [0] 20 34 2
      ((11, 2) :: (1, 1) :: repeat (1, 2) 114
       ++ (1333, 2) :: (1, 1) :: repeat (1, 2) 3324
       ++ (600, 2) :: (1, 1) :: repeat (1, 2) 16300 ++ w) 1)).
    { apply (sTUP [0] 20 35 13 2
             ((1, 1) :: repeat (1, 2) 114
              ++ (1333, 2) :: (1, 1) :: repeat (1, 2) 3324
              ++ (600, 2) :: (1, 1)
              :: repeat (1, 2) 16300 ++ w) 1); closearith. }
    apply (hsteps_trans _ (HB [0] 19 1 34
      ((2, 2) :: (11, 2) :: (1, 1) :: repeat (1, 2) 114
       ++ (1333, 2) :: (1, 1) :: repeat (1, 2) 3324
       ++ (600, 2) :: (1, 1) :: repeat (1, 2) 16300 ++ w) 1)).
    { apply (hGRIND_even 15 [0] 19
             ((11, 2) :: (1, 1) :: repeat (1, 2) 114
              ++ (1333, 2) :: (1, 1) :: repeat (1, 2) 3324
              ++ (600, 2) :: (1, 1)
              :: repeat (1, 2) 16300 ++ w) 1); closearith. }
    apply (hsteps_trans _ (HC [20; 0] 34 1 2
      ((9, 2) :: (1, 1) :: repeat (1, 2) 114
       ++ (1333, 2) :: (1, 1) :: repeat (1, 2) 3324
       ++ (600, 2) :: (1, 1) :: repeat (1, 2) 16300 ++ w) 1)).
    { replace ((9, 2) :: (1, 1) :: repeat (1, 2) 114
               ++ (1333, 2) :: (1, 1) :: repeat (1, 2) 3324
               ++ (600, 2) :: (1, 1)
               :: repeat (1, 2) 16300 ++ w)
        with ((11 - 2, 2) :: (1, 1) :: repeat (1, 2) 114
              ++ (1333, 2) :: (1, 1) :: repeat (1, 2) 3324
              ++ (600, 2) :: (1, 1)
              :: repeat (1, 2) 16300 ++ w)
        by sec_eq.
      apply (sTUP2_1 [0] 19 33 11
             ((1, 1) :: repeat (1, 2) 114
              ++ (1333, 2) :: (1, 1) :: repeat (1, 2) 3324
              ++ (600, 2) :: (1, 1)
              :: repeat (1, 2) 16300 ++ w) 1); closearith. }
    apply (hsteps_trans _ (HB [20; 0] 34 1 4
      ((9, 2) :: (1, 1) :: repeat (1, 2) 114
       ++ (1333, 2) :: (1, 1) :: repeat (1, 2) 3324
       ++ (600, 2) :: (1, 1) :: repeat (1, 2) 16300 ++ w) 1)).
    { apply (sTDN [20; 0] 34
             ((9, 2) :: (1, 1) :: repeat (1, 2) 114
              ++ (1333, 2) :: (1, 1) :: repeat (1, 2) 3324
              ++ (600, 2) :: (1, 1)
              :: repeat (1, 2) 16300 ++ w) 1). }
    replace ((7, 2) :: (1, 1) :: repeat (1, 2) 114
             ++ (1333, 2) :: (1, 1) :: repeat (1, 2) 3324
             ++ (600, 2) :: (1, 1) :: repeat (1, 2) 16300 ++ w)
      with ((9 - 2, 2) :: (1, 1) :: repeat (1, 2) 114
            ++ (1333, 2) :: (1, 1) :: repeat (1, 2) 3324
            ++ (600, 2) :: (1, 1) :: repeat (1, 2) 16300 ++ w)
      by sec_eq.
    apply (sTUP [20; 0] 34 4 9 2
           ((1, 1) :: repeat (1, 2) 114
            ++ (1333, 2) :: (1, 1) :: repeat (1, 2) 3324
            ++ (600, 2) :: (1, 1) :: repeat (1, 2) 16300 ++ w)
           1); closearith. }
  (* S26: CLEANG_odd 2 *)
  apply (hsteps_trans _ (HB [20; 0] 34 1 12
    ((1, 2) :: (1, 1) :: repeat (1, 2) 114
     ++ (1333, 2) :: (1, 1) :: repeat (1, 2) 3324
     ++ (600, 2) :: (1, 1) :: repeat (1, 2) 16300 ++ w) 1)).
  { apply (CLEANG_odd 2 [20; 0] 34
           ((1, 1) :: repeat (1, 2) 114
            ++ (1333, 2) :: (1, 1) :: repeat (1, 2) 3324
            ++ (600, 2) :: (1, 1) :: repeat (1, 2) 16300 ++ w)
           1); closearith. }
  (* S27: pop12 1 + POP + pop12 114, front(1333) onto [150; 20; 0] *)
  apply (hsteps_trans _ (HC [150; 20; 0] 242 3 2
    ((1327, 2) :: (1, 1) :: repeat (1, 2) 3324
     ++ (600, 2) :: (1, 1) :: repeat (1, 2) 16300 ++ w) 1)).
  { apply (hsteps_trans _ (HB [20; 0] 35 1 14
      ((1, 1) :: repeat (1, 2) 114
       ++ (1333, 2) :: (1, 1) :: repeat (1, 2) 3324
       ++ (600, 2) :: (1, 1) :: repeat (1, 2) 16300 ++ w) 1)).
    { replace ((1, 2) :: (1, 1) :: repeat (1, 2) 114
               ++ (1333, 2) :: (1, 1) :: repeat (1, 2) 3324
               ++ (600, 2) :: (1, 1)
               :: repeat (1, 2) 16300 ++ w)
        with (repeat (1, 2) 1
              ++ ((1, 1) :: repeat (1, 2) 114
                  ++ (1333, 2) :: (1, 1) :: repeat (1, 2) 3324
                  ++ (600, 2) :: (1, 1)
                  :: repeat (1, 2) 16300 ++ w))
        by sec_eq.
      apply (pop12 1 [20; 0] 34 12
             ((1, 1) :: repeat (1, 2) 114
              ++ (1333, 2) :: (1, 1) :: repeat (1, 2) 3324
              ++ (600, 2) :: (1, 1)
              :: repeat (1, 2) 16300 ++ w) 1); closearith. }
    apply (hsteps_trans _ (HB [20; 0] 36 1 15
      (repeat (1, 2) 114
       ++ (1333, 2) :: (1, 1) :: repeat (1, 2) 3324
       ++ (600, 2) :: (1, 1) :: repeat (1, 2) 16300 ++ w) 1)).
    { apply (sPOP1 [20; 0] 35 14
             (repeat (1, 2) 114
              ++ (1333, 2) :: (1, 1) :: repeat (1, 2) 3324
              ++ (600, 2) :: (1, 1)
              :: repeat (1, 2) 16300 ++ w) 1); closearith. }
    apply (hsteps_trans _ (HB [20; 0] 150 1 243
      ((1333, 2) :: (1, 1) :: repeat (1, 2) 3324
       ++ (600, 2) :: (1, 1) :: repeat (1, 2) 16300 ++ w) 1)).
    { apply (pop12 114 [20; 0] 36 15
             ((1333, 2) :: (1, 1) :: repeat (1, 2) 3324
              ++ (600, 2) :: (1, 1)
              :: repeat (1, 2) 16300 ++ w) 1); closearith. }
    apply (hsteps_trans _ (HC [20; 0] 150 242 2
      ((1331, 2) :: (1, 1) :: repeat (1, 2) 3324
       ++ (600, 2) :: (1, 1) :: repeat (1, 2) 16300 ++ w) 1)).
    { apply (sTUP [20; 0] 150 243 1333 2
             ((1, 1) :: repeat (1, 2) 3324
              ++ (600, 2) :: (1, 1)
              :: repeat (1, 2) 16300 ++ w) 1); closearith. }
    apply (hsteps_trans _ (HB [20; 0] 149 1 242
      ((2, 2) :: (1331, 2) :: (1, 1) :: repeat (1, 2) 3324
       ++ (600, 2) :: (1, 1) :: repeat (1, 2) 16300 ++ w) 1)).
    { apply (hGRIND_even 119 [20; 0] 149
             ((1331, 2) :: (1, 1) :: repeat (1, 2) 3324
              ++ (600, 2) :: (1, 1)
              :: repeat (1, 2) 16300 ++ w) 1); closearith. }
    apply (hsteps_trans _ (HC [150; 20; 0] 242 1 2
      ((1329, 2) :: (1, 1) :: repeat (1, 2) 3324
       ++ (600, 2) :: (1, 1) :: repeat (1, 2) 16300 ++ w) 1)).
    { replace ((1329, 2) :: (1, 1) :: repeat (1, 2) 3324
               ++ (600, 2) :: (1, 1)
               :: repeat (1, 2) 16300 ++ w)
        with ((1331 - 2, 2) :: (1, 1) :: repeat (1, 2) 3324
              ++ (600, 2) :: (1, 1)
              :: repeat (1, 2) 16300 ++ w)
        by sec_eq.
      apply (sTUP2_1 [20; 0] 149 241 1331
             ((1, 1) :: repeat (1, 2) 3324
              ++ (600, 2) :: (1, 1)
              :: repeat (1, 2) 16300 ++ w) 1); closearith. }
    apply (hsteps_trans _ (HB [150; 20; 0] 242 1 4
      ((1329, 2) :: (1, 1) :: repeat (1, 2) 3324
       ++ (600, 2) :: (1, 1) :: repeat (1, 2) 16300 ++ w) 1)).
    { apply (sTDN [150; 20; 0] 242
             ((1329, 2) :: (1, 1) :: repeat (1, 2) 3324
              ++ (600, 2) :: (1, 1)
              :: repeat (1, 2) 16300 ++ w) 1). }
    replace ((1327, 2) :: (1, 1) :: repeat (1, 2) 3324
             ++ (600, 2) :: (1, 1) :: repeat (1, 2) 16300 ++ w)
      with ((1329 - 2, 2) :: (1, 1) :: repeat (1, 2) 3324
            ++ (600, 2) :: (1, 1) :: repeat (1, 2) 16300 ++ w)
      by sec_eq.
    apply (sTUP [150; 20; 0] 242 4 1329 2
           ((1, 1) :: repeat (1, 2) 3324
            ++ (600, 2) :: (1, 1) :: repeat (1, 2) 16300 ++ w)
           1); closearith. }
  (* S28: DIPGRIND (242, 843) *)
  apply (hsteps_trans _ (HC [150; 20; 0] 0 3 2
    (repeat (1, 2) 242
     ++ (843, 2) :: (1, 1) :: repeat (1, 2) 3324
     ++ (600, 2) :: (1, 1) :: repeat (1, 2) 16300 ++ w) 1)).
  { apply (DIPGRIND 242 843 [150; 20; 0]
           ((1, 1) :: repeat (1, 2) 3324
            ++ (600, 2) :: (1, 1) :: repeat (1, 2) 16300 ++ w)
           1); closearith. }
  (* S29: PX2A + PUSH + TDN + TUP onto [0] *)
  apply (hsteps_trans _ (HC [0] 18 3 2
    ((144, 2) :: (1, 1) :: repeat (1, 2) 244
     ++ (843, 2) :: (1, 1) :: repeat (1, 2) 3324
     ++ (600, 2) :: (1, 1) :: repeat (1, 2) 16300 ++ w) 1)).
  { apply (hsteps_trans _ (HC [0] 19 148 2
      ((1, 1) :: (1, 2) :: (1, 2) :: repeat (1, 2) 242
       ++ (843, 2) :: (1, 1) :: repeat (1, 2) 3324
       ++ (600, 2) :: (1, 1) :: repeat (1, 2) 16300 ++ w) 1)).
    { apply (hsteps_step _ (HC [0] 19 148 2
                 ((1, 1) :: (1, 2) :: (1, 2)
                  :: repeat (1, 2) 242
                  ++ (843, 2) :: (1, 1) :: repeat (1, 2) 3324
                  ++ (600, 2) :: (1, 1)
                  :: repeat (1, 2) 16300 ++ w) 1));
        [apply hPX2A | apply hsteps_refl]. }
    apply (hsteps_trans _ (HC [0] 18 1 2
      ((146, 2) :: (1, 1) :: (1, 2) :: (1, 2)
       :: repeat (1, 2) 242
       ++ (843, 2) :: (1, 1) :: repeat (1, 2) 3324
       ++ (600, 2) :: (1, 1) :: repeat (1, 2) 16300 ++ w) 1)).
    { apply (sPUSH [0] 18 148
             ((1, 1) :: (1, 2) :: (1, 2) :: repeat (1, 2) 242
              ++ (843, 2) :: (1, 1) :: repeat (1, 2) 3324
              ++ (600, 2) :: (1, 1)
              :: repeat (1, 2) 16300 ++ w) 1); closearith. }
    apply (hsteps_trans _ (HB [0] 18 1 4
      ((146, 2) :: (1, 1) :: (1, 2) :: (1, 2)
       :: repeat (1, 2) 242
       ++ (843, 2) :: (1, 1) :: repeat (1, 2) 3324
       ++ (600, 2) :: (1, 1) :: repeat (1, 2) 16300 ++ w) 1)).
    { apply (sTDN [0] 18
             ((146, 2) :: (1, 1) :: (1, 2) :: (1, 2)
              :: repeat (1, 2) 242
              ++ (843, 2) :: (1, 1) :: repeat (1, 2) 3324
              ++ (600, 2) :: (1, 1)
              :: repeat (1, 2) 16300 ++ w) 1). }
    replace ((144, 2) :: (1, 1) :: repeat (1, 2) 244
             ++ (843, 2) :: (1, 1) :: repeat (1, 2) 3324
             ++ (600, 2) :: (1, 1) :: repeat (1, 2) 16300 ++ w)
      with ((146 - 2, 2) :: (1, 1) :: (1, 2) :: (1, 2)
            :: repeat (1, 2) 242
            ++ (843, 2) :: (1, 1) :: repeat (1, 2) 3324
            ++ (600, 2) :: (1, 1) :: repeat (1, 2) 16300 ++ w)
      by sec_eq.
    apply (sTUP [0] 18 4 146 2
           ((1, 1) :: (1, 2) :: (1, 2) :: repeat (1, 2) 242
            ++ (843, 2) :: (1, 1) :: repeat (1, 2) 3324
            ++ (600, 2) :: (1, 1)
            :: repeat (1, 2) 16300 ++ w) 1); closearith. }
  (* S30: DIPGRIND (18, 108) *)
  apply (hsteps_trans _ (HC [0] 0 3 2
    (repeat (1, 2) 18
     ++ (108, 2) :: (1, 1) :: repeat (1, 2) 244
     ++ (843, 2) :: (1, 1) :: repeat (1, 2) 3324
     ++ (600, 2) :: (1, 1) :: repeat (1, 2) 16300 ++ w) 1)).
  { apply (DIPGRIND 18 108 [0]
           ((1, 1) :: repeat (1, 2) 244
            ++ (843, 2) :: (1, 1) :: repeat (1, 2) 3324
            ++ (600, 2) :: (1, 1) :: repeat (1, 2) 16300 ++ w)
           1); closearith. }
  (* S31: PX2B0 + pop12 19 at [] *)
  apply (hsteps_trans _ (HB [] 19 1 43
    ((108, 2) :: (1, 1) :: repeat (1, 2) 244
     ++ (843, 2) :: (1, 1) :: repeat (1, 2) 3324
     ++ (600, 2) :: (1, 1) :: repeat (1, 2) 16300 ++ w) 1)).
  { apply (hsteps_trans _ (HB [] 0 1 5
      (repeat (1, 2) 19
       ++ (108, 2) :: (1, 1) :: repeat (1, 2) 244
       ++ (843, 2) :: (1, 1) :: repeat (1, 2) 3324
       ++ (600, 2) :: (1, 1) :: repeat (1, 2) 16300 ++ w) 1)).
    { apply (hsteps_step _ (HB [] 0 1 5
                 (repeat (1, 2) 19
                  ++ (108, 2) :: (1, 1) :: repeat (1, 2) 244
                  ++ (843, 2) :: (1, 1) :: repeat (1, 2) 3324
                  ++ (600, 2) :: (1, 1)
                  :: repeat (1, 2) 16300 ++ w) 1));
        [apply hPX2B0 | apply hsteps_refl]. }
    apply (pop12 19 [] 0 5
           ((108, 2) :: (1, 1) :: repeat (1, 2) 244
            ++ (843, 2) :: (1, 1) :: repeat (1, 2) 3324
            ++ (600, 2) :: (1, 1) :: repeat (1, 2) 16300 ++ w)
           1); closearith. }
  (* S32: bottom front (TUP + PUSH + TDN + TUP) *)
  apply (hsteps_trans _ (HC [] 18 3 2
    ((38, 2) :: (106, 2) :: (1, 1) :: repeat (1, 2) 244
     ++ (843, 2) :: (1, 1) :: repeat (1, 2) 3324
     ++ (600, 2) :: (1, 1) :: repeat (1, 2) 16300 ++ w) 1)).
  { apply (hsteps_trans _ (HC [] 19 42 2
      ((106, 2) :: (1, 1) :: repeat (1, 2) 244
       ++ (843, 2) :: (1, 1) :: repeat (1, 2) 3324
       ++ (600, 2) :: (1, 1) :: repeat (1, 2) 16300 ++ w) 1)).
    { apply (sTUP [] 19 43 108 2
             ((1, 1) :: repeat (1, 2) 244
              ++ (843, 2) :: (1, 1) :: repeat (1, 2) 3324
              ++ (600, 2) :: (1, 1)
              :: repeat (1, 2) 16300 ++ w) 1); closearith. }
    apply (hsteps_trans _ (HC [] 18 1 2
      ((40, 2) :: (106, 2) :: (1, 1) :: repeat (1, 2) 244
       ++ (843, 2) :: (1, 1) :: repeat (1, 2) 3324
       ++ (600, 2) :: (1, 1) :: repeat (1, 2) 16300 ++ w) 1)).
    { apply (sPUSH [] 18 42
             ((106, 2) :: (1, 1) :: repeat (1, 2) 244
              ++ (843, 2) :: (1, 1) :: repeat (1, 2) 3324
              ++ (600, 2) :: (1, 1)
              :: repeat (1, 2) 16300 ++ w) 1); closearith. }
    apply (hsteps_trans _ (HB [] 18 1 4
      ((40, 2) :: (106, 2) :: (1, 1) :: repeat (1, 2) 244
       ++ (843, 2) :: (1, 1) :: repeat (1, 2) 3324
       ++ (600, 2) :: (1, 1) :: repeat (1, 2) 16300 ++ w) 1)).
    { apply (sTDN [] 18
             ((40, 2) :: (106, 2) :: (1, 1) :: repeat (1, 2) 244
              ++ (843, 2) :: (1, 1) :: repeat (1, 2) 3324
              ++ (600, 2) :: (1, 1)
              :: repeat (1, 2) 16300 ++ w) 1). }
    apply (sTUP [] 18 4 40 2
           ((106, 2) :: (1, 1) :: repeat (1, 2) 244
            ++ (843, 2) :: (1, 1) :: repeat (1, 2) 3324
            ++ (600, 2) :: (1, 1)
            :: repeat (1, 2) 16300 ++ w) 1); closearith. }
  (* S33: DIPGRIND (18, 2) *)
  apply (hsteps_trans _ (HC [] 0 3 2
    (repeat (1, 2) 18
     ++ (2, 2) :: (106, 2) :: (1, 1) :: repeat (1, 2) 244
     ++ (843, 2) :: (1, 1) :: repeat (1, 2) 3324
     ++ (600, 2) :: (1, 1) :: repeat (1, 2) 16300 ++ w) 1)).
  { apply (DIPGRIND 18 2 []
           ((106, 2) :: (1, 1) :: repeat (1, 2) 244
            ++ (843, 2) :: (1, 1) :: repeat (1, 2) 3324
            ++ (600, 2) :: (1, 1) :: repeat (1, 2) 16300 ++ w)
           1); closearith. }
  (* S34: PUSHX + pop12 18 + TUP2_1 + TDN + TUP onto [20] *)
  apply (hsteps_trans _ (HC [20] 43 3 2
    ((102, 2) :: (1, 1) :: repeat (1, 2) 244
     ++ (843, 2) :: (1, 1) :: repeat (1, 2) 3324
     ++ (600, 2) :: (1, 1) :: repeat (1, 2) 16300 ++ w) 1)).
  { apply (hsteps_trans _ (HB [] 1 1 7
      (repeat (1, 2) 18
       ++ (2, 2) :: (106, 2) :: (1, 1) :: repeat (1, 2) 244
       ++ (843, 2) :: (1, 1) :: repeat (1, 2) 3324
       ++ (600, 2) :: (1, 1) :: repeat (1, 2) 16300 ++ w) 1)).
    { apply (hsteps_step _ (HB [] 1 1 7
                 (repeat (1, 2) 18
                  ++ (2, 2) :: (106, 2) :: (1, 1)
                  :: repeat (1, 2) 244
                  ++ (843, 2) :: (1, 1) :: repeat (1, 2) 3324
                  ++ (600, 2) :: (1, 1)
                  :: repeat (1, 2) 16300 ++ w) 1));
        [apply hPUSHX | apply hsteps_refl]. }
    apply (hsteps_trans _ (HB [] 19 1 43
      ((2, 2) :: (106, 2) :: (1, 1) :: repeat (1, 2) 244
       ++ (843, 2) :: (1, 1) :: repeat (1, 2) 3324
       ++ (600, 2) :: (1, 1) :: repeat (1, 2) 16300 ++ w) 1)).
    { apply (pop12 18 [] 1 7
             ((2, 2) :: (106, 2) :: (1, 1) :: repeat (1, 2) 244
              ++ (843, 2) :: (1, 1) :: repeat (1, 2) 3324
              ++ (600, 2) :: (1, 1)
              :: repeat (1, 2) 16300 ++ w) 1); closearith. }
    apply (hsteps_trans _ (HC [20] 43 1 2
      ((104, 2) :: (1, 1) :: repeat (1, 2) 244
       ++ (843, 2) :: (1, 1) :: repeat (1, 2) 3324
       ++ (600, 2) :: (1, 1) :: repeat (1, 2) 16300 ++ w) 1)).
    { replace ((104, 2) :: (1, 1) :: repeat (1, 2) 244
               ++ (843, 2) :: (1, 1) :: repeat (1, 2) 3324
               ++ (600, 2) :: (1, 1)
               :: repeat (1, 2) 16300 ++ w)
        with ((106 - 2, 2) :: (1, 1) :: repeat (1, 2) 244
              ++ (843, 2) :: (1, 1) :: repeat (1, 2) 3324
              ++ (600, 2) :: (1, 1)
              :: repeat (1, 2) 16300 ++ w)
        by sec_eq.
      apply (sTUP2_1 [] 19 42 106
             ((1, 1) :: repeat (1, 2) 244
              ++ (843, 2) :: (1, 1) :: repeat (1, 2) 3324
              ++ (600, 2) :: (1, 1)
              :: repeat (1, 2) 16300 ++ w) 1); closearith. }
    apply (hsteps_trans _ (HB [20] 43 1 4
      ((104, 2) :: (1, 1) :: repeat (1, 2) 244
       ++ (843, 2) :: (1, 1) :: repeat (1, 2) 3324
       ++ (600, 2) :: (1, 1) :: repeat (1, 2) 16300 ++ w) 1)).
    { apply (sTDN [20] 43
             ((104, 2) :: (1, 1) :: repeat (1, 2) 244
              ++ (843, 2) :: (1, 1) :: repeat (1, 2) 3324
              ++ (600, 2) :: (1, 1)
              :: repeat (1, 2) 16300 ++ w) 1). }
    replace ((102, 2) :: (1, 1) :: repeat (1, 2) 244
             ++ (843, 2) :: (1, 1) :: repeat (1, 2) 3324
             ++ (600, 2) :: (1, 1) :: repeat (1, 2) 16300 ++ w)
      with ((104 - 2, 2) :: (1, 1) :: repeat (1, 2) 244
            ++ (843, 2) :: (1, 1) :: repeat (1, 2) 3324
            ++ (600, 2) :: (1, 1) :: repeat (1, 2) 16300 ++ w)
      by sec_eq.
    apply (sTUP [20] 43 4 104 2
           ((1, 1) :: repeat (1, 2) 244
            ++ (843, 2) :: (1, 1) :: repeat (1, 2) 3324
            ++ (600, 2) :: (1, 1) :: repeat (1, 2) 16300 ++ w)
           1); closearith. }
  (* S35: DIPGRIND (43, 16) *)
  apply (hsteps_trans _ (HC [20] 0 3 2
    (repeat (1, 2) 43
     ++ (16, 2) :: (1, 1) :: repeat (1, 2) 244
     ++ (843, 2) :: (1, 1) :: repeat (1, 2) 3324
     ++ (600, 2) :: (1, 1) :: repeat (1, 2) 16300 ++ w) 1)).
  { apply (DIPGRIND 43 16 [20]
           ((1, 1) :: repeat (1, 2) 244
            ++ (843, 2) :: (1, 1) :: repeat (1, 2) 3324
            ++ (600, 2) :: (1, 1) :: repeat (1, 2) 16300 ++ w)
           1); closearith. }
  (* S36: PX2Bgen + TUP + TDN + TUP at [0] *)
  apply (hsteps_trans _ (HC [0] 3 3 2
    ((12, 2) :: (1, 1) :: repeat (1, 2) 45
     ++ (16, 2) :: (1, 1) :: repeat (1, 2) 244
     ++ (843, 2) :: (1, 1) :: repeat (1, 2) 3324
     ++ (600, 2) :: (1, 1) :: repeat (1, 2) 16300 ++ w) 1)).
  { apply (hsteps_trans _ (HB [0] 3 1 2
      ((16, 2) :: (1, 1) :: (1, 2) :: (1, 2)
       :: repeat (1, 2) 43
       ++ (16, 2) :: (1, 1) :: repeat (1, 2) 244
       ++ (843, 2) :: (1, 1) :: repeat (1, 2) 3324
       ++ (600, 2) :: (1, 1) :: repeat (1, 2) 16300 ++ w) 1)).
    { apply (hsteps_step _ (HB [0] 3 1 2
                 ((16, 2) :: (1, 1) :: (1, 2) :: (1, 2)
                  :: repeat (1, 2) 43
                  ++ (16, 2) :: (1, 1) :: repeat (1, 2) 244
                  ++ (843, 2) :: (1, 1) :: repeat (1, 2) 3324
                  ++ (600, 2) :: (1, 1)
                  :: repeat (1, 2) 16300 ++ w) 1));
        [apply hPX2Bgen | apply hsteps_refl]. }
    apply (hsteps_trans _ (HC [0] 3 1 2
      ((14, 2) :: (1, 1) :: (1, 2) :: (1, 2)
       :: repeat (1, 2) 43
       ++ (16, 2) :: (1, 1) :: repeat (1, 2) 244
       ++ (843, 2) :: (1, 1) :: repeat (1, 2) 3324
       ++ (600, 2) :: (1, 1) :: repeat (1, 2) 16300 ++ w) 1)).
    { apply (sTUP [0] 3 2 16 2
             ((1, 1) :: (1, 2) :: (1, 2) :: repeat (1, 2) 43
              ++ (16, 2) :: (1, 1) :: repeat (1, 2) 244
              ++ (843, 2) :: (1, 1) :: repeat (1, 2) 3324
              ++ (600, 2) :: (1, 1)
              :: repeat (1, 2) 16300 ++ w) 1); closearith. }
    apply (hsteps_trans _ (HB [0] 3 1 4
      ((14, 2) :: (1, 1) :: (1, 2) :: (1, 2)
       :: repeat (1, 2) 43
       ++ (16, 2) :: (1, 1) :: repeat (1, 2) 244
       ++ (843, 2) :: (1, 1) :: repeat (1, 2) 3324
       ++ (600, 2) :: (1, 1) :: repeat (1, 2) 16300 ++ w) 1)).
    { apply (sTDN [0] 3
             ((14, 2) :: (1, 1) :: (1, 2) :: (1, 2)
              :: repeat (1, 2) 43
              ++ (16, 2) :: (1, 1) :: repeat (1, 2) 244
              ++ (843, 2) :: (1, 1) :: repeat (1, 2) 3324
              ++ (600, 2) :: (1, 1)
              :: repeat (1, 2) 16300 ++ w) 1). }
    replace ((12, 2) :: (1, 1) :: repeat (1, 2) 45
             ++ (16, 2) :: (1, 1) :: repeat (1, 2) 244
             ++ (843, 2) :: (1, 1) :: repeat (1, 2) 3324
             ++ (600, 2) :: (1, 1) :: repeat (1, 2) 16300 ++ w)
      with ((14 - 2, 2) :: (1, 1) :: (1, 2) :: (1, 2)
            :: repeat (1, 2) 43
            ++ (16, 2) :: (1, 1) :: repeat (1, 2) 244
            ++ (843, 2) :: (1, 1) :: repeat (1, 2) 3324
            ++ (600, 2) :: (1, 1) :: repeat (1, 2) 16300 ++ w)
      by sec_eq.
    apply (sTUP [0] 3 4 14 2
           ((1, 1) :: (1, 2) :: (1, 2) :: repeat (1, 2) 43
            ++ (16, 2) :: (1, 1) :: repeat (1, 2) 244
            ++ (843, 2) :: (1, 1) :: repeat (1, 2) 3324
            ++ (600, 2) :: (1, 1)
            :: repeat (1, 2) 16300 ++ w) 1); closearith. }
  (* S37: DIPGRIND (3, 6) *)
  apply (hsteps_trans _ (HC [0] 0 3 2
    (repeat (1, 2) 3
     ++ (6, 2) :: (1, 1) :: repeat (1, 2) 45
     ++ (16, 2) :: (1, 1) :: repeat (1, 2) 244
     ++ (843, 2) :: (1, 1) :: repeat (1, 2) 3324
     ++ (600, 2) :: (1, 1) :: repeat (1, 2) 16300 ++ w) 1)).
  { apply (DIPGRIND 3 6 [0]
           ((1, 1) :: repeat (1, 2) 45
            ++ (16, 2) :: (1, 1) :: repeat (1, 2) 244
            ++ (843, 2) :: (1, 1) :: repeat (1, 2) 3324
            ++ (600, 2) :: (1, 1) :: repeat (1, 2) 16300 ++ w)
           1); closearith. }
  (* S38: PX2B0 + pop12 4 at [] *)
  apply (hsteps_trans _ (HB [] 4 1 13
    ((6, 2) :: (1, 1) :: repeat (1, 2) 45
     ++ (16, 2) :: (1, 1) :: repeat (1, 2) 244
     ++ (843, 2) :: (1, 1) :: repeat (1, 2) 3324
     ++ (600, 2) :: (1, 1) :: repeat (1, 2) 16300 ++ w) 1)).
  { apply (hsteps_trans _ (HB [] 0 1 5
      (repeat (1, 2) 4
       ++ (6, 2) :: (1, 1) :: repeat (1, 2) 45
       ++ (16, 2) :: (1, 1) :: repeat (1, 2) 244
       ++ (843, 2) :: (1, 1) :: repeat (1, 2) 3324
       ++ (600, 2) :: (1, 1) :: repeat (1, 2) 16300 ++ w) 1)).
    { apply (hsteps_step _ (HB [] 0 1 5
                 (repeat (1, 2) 4
                  ++ (6, 2) :: (1, 1) :: repeat (1, 2) 45
                  ++ (16, 2) :: (1, 1) :: repeat (1, 2) 244
                  ++ (843, 2) :: (1, 1) :: repeat (1, 2) 3324
                  ++ (600, 2) :: (1, 1)
                  :: repeat (1, 2) 16300 ++ w) 1));
        [apply hPX2B0 | apply hsteps_refl]. }
    apply (pop12 4 [] 0 5
           ((6, 2) :: (1, 1) :: repeat (1, 2) 45
            ++ (16, 2) :: (1, 1) :: repeat (1, 2) 244
            ++ (843, 2) :: (1, 1) :: repeat (1, 2) 3324
            ++ (600, 2) :: (1, 1) :: repeat (1, 2) 16300 ++ w)
           1); closearith. }
  (* S39: bottom front (TUP + PUSH + TDN + TUP) *)
  apply (hsteps_trans _ (HC [] 3 3 2
    ((8, 2) :: (4, 2) :: (1, 1) :: repeat (1, 2) 45
     ++ (16, 2) :: (1, 1) :: repeat (1, 2) 244
     ++ (843, 2) :: (1, 1) :: repeat (1, 2) 3324
     ++ (600, 2) :: (1, 1) :: repeat (1, 2) 16300 ++ w) 1)).
  { apply (hsteps_trans _ (HC [] 4 12 2
      ((4, 2) :: (1, 1) :: repeat (1, 2) 45
       ++ (16, 2) :: (1, 1) :: repeat (1, 2) 244
       ++ (843, 2) :: (1, 1) :: repeat (1, 2) 3324
       ++ (600, 2) :: (1, 1) :: repeat (1, 2) 16300 ++ w) 1)).
    { apply (sTUP [] 4 13 6 2
             ((1, 1) :: repeat (1, 2) 45
              ++ (16, 2) :: (1, 1) :: repeat (1, 2) 244
              ++ (843, 2) :: (1, 1) :: repeat (1, 2) 3324
              ++ (600, 2) :: (1, 1)
              :: repeat (1, 2) 16300 ++ w) 1); closearith. }
    apply (hsteps_trans _ (HC [] 3 1 2
      ((10, 2) :: (4, 2) :: (1, 1) :: repeat (1, 2) 45
       ++ (16, 2) :: (1, 1) :: repeat (1, 2) 244
       ++ (843, 2) :: (1, 1) :: repeat (1, 2) 3324
       ++ (600, 2) :: (1, 1) :: repeat (1, 2) 16300 ++ w) 1)).
    { apply (sPUSH [] 3 12
             ((4, 2) :: (1, 1) :: repeat (1, 2) 45
              ++ (16, 2) :: (1, 1) :: repeat (1, 2) 244
              ++ (843, 2) :: (1, 1) :: repeat (1, 2) 3324
              ++ (600, 2) :: (1, 1)
              :: repeat (1, 2) 16300 ++ w) 1); closearith. }
    apply (hsteps_trans _ (HB [] 3 1 4
      ((10, 2) :: (4, 2) :: (1, 1) :: repeat (1, 2) 45
       ++ (16, 2) :: (1, 1) :: repeat (1, 2) 244
       ++ (843, 2) :: (1, 1) :: repeat (1, 2) 3324
       ++ (600, 2) :: (1, 1) :: repeat (1, 2) 16300 ++ w) 1)).
    { apply (sTDN [] 3
             ((10, 2) :: (4, 2) :: (1, 1) :: repeat (1, 2) 45
              ++ (16, 2) :: (1, 1) :: repeat (1, 2) 244
              ++ (843, 2) :: (1, 1) :: repeat (1, 2) 3324
              ++ (600, 2) :: (1, 1)
              :: repeat (1, 2) 16300 ++ w) 1). }
    apply (sTUP [] 3 4 10 2
           ((4, 2) :: (1, 1) :: repeat (1, 2) 45
            ++ (16, 2) :: (1, 1) :: repeat (1, 2) 244
            ++ (843, 2) :: (1, 1) :: repeat (1, 2) 3324
            ++ (600, 2) :: (1, 1)
            :: repeat (1, 2) 16300 ++ w) 1); closearith. }
  (* S40: DIPGRIND (3, 2) *)
  apply (hsteps_trans _ (HC [] 0 3 2
    (repeat (1, 2) 3
     ++ (2, 2) :: (4, 2) :: (1, 1) :: repeat (1, 2) 45
     ++ (16, 2) :: (1, 1) :: repeat (1, 2) 244
     ++ (843, 2) :: (1, 1) :: repeat (1, 2) 3324
     ++ (600, 2) :: (1, 1) :: repeat (1, 2) 16300 ++ w) 1)).
  { apply (DIPGRIND 3 2 []
           ((4, 2) :: (1, 1) :: repeat (1, 2) 45
            ++ (16, 2) :: (1, 1) :: repeat (1, 2) 244
            ++ (843, 2) :: (1, 1) :: repeat (1, 2) 3324
            ++ (600, 2) :: (1, 1) :: repeat (1, 2) 16300 ++ w)
           1); closearith. }
  (* S41: PUSHX + pop12 3 + TUP2_1 + TDN + TRANS2_1 onto [14; 5] *)
  apply (hsteps_trans _ (HB [14; 5] 5 1 3
    (repeat (1, 2) 45
     ++ (16, 2) :: (1, 1) :: repeat (1, 2) 244
     ++ (843, 2) :: (1, 1) :: repeat (1, 2) 3324
     ++ (600, 2) :: (1, 1) :: repeat (1, 2) 16300 ++ w) 1)).
  { apply (hsteps_trans _ (HB [] 1 1 7
      (repeat (1, 2) 3
       ++ (2, 2) :: (4, 2) :: (1, 1) :: repeat (1, 2) 45
       ++ (16, 2) :: (1, 1) :: repeat (1, 2) 244
       ++ (843, 2) :: (1, 1) :: repeat (1, 2) 3324
       ++ (600, 2) :: (1, 1) :: repeat (1, 2) 16300 ++ w) 1)).
    { apply (hsteps_step _ (HB [] 1 1 7
                 (repeat (1, 2) 3
                  ++ (2, 2) :: (4, 2) :: (1, 1)
                  :: repeat (1, 2) 45
                  ++ (16, 2) :: (1, 1) :: repeat (1, 2) 244
                  ++ (843, 2) :: (1, 1) :: repeat (1, 2) 3324
                  ++ (600, 2) :: (1, 1)
                  :: repeat (1, 2) 16300 ++ w) 1));
        [apply hPUSHX | apply hsteps_refl]. }
    apply (hsteps_trans _ (HB [] 4 1 13
      ((2, 2) :: (4, 2) :: (1, 1) :: repeat (1, 2) 45
       ++ (16, 2) :: (1, 1) :: repeat (1, 2) 244
       ++ (843, 2) :: (1, 1) :: repeat (1, 2) 3324
       ++ (600, 2) :: (1, 1) :: repeat (1, 2) 16300 ++ w) 1)).
    { apply (pop12 3 [] 1 7
             ((2, 2) :: (4, 2) :: (1, 1) :: repeat (1, 2) 45
              ++ (16, 2) :: (1, 1) :: repeat (1, 2) 244
              ++ (843, 2) :: (1, 1) :: repeat (1, 2) 3324
              ++ (600, 2) :: (1, 1)
              :: repeat (1, 2) 16300 ++ w) 1); closearith. }
    apply (hsteps_trans _ (HC [5] 13 1 2
      ((2, 2) :: (1, 1) :: repeat (1, 2) 45
       ++ (16, 2) :: (1, 1) :: repeat (1, 2) 244
       ++ (843, 2) :: (1, 1) :: repeat (1, 2) 3324
       ++ (600, 2) :: (1, 1) :: repeat (1, 2) 16300 ++ w) 1)).
    { replace ((2, 2) :: (1, 1) :: repeat (1, 2) 45
               ++ (16, 2) :: (1, 1) :: repeat (1, 2) 244
               ++ (843, 2) :: (1, 1) :: repeat (1, 2) 3324
               ++ (600, 2) :: (1, 1)
               :: repeat (1, 2) 16300 ++ w)
        with ((4 - 2, 2) :: (1, 1) :: repeat (1, 2) 45
              ++ (16, 2) :: (1, 1) :: repeat (1, 2) 244
              ++ (843, 2) :: (1, 1) :: repeat (1, 2) 3324
              ++ (600, 2) :: (1, 1)
              :: repeat (1, 2) 16300 ++ w)
        by sec_eq.
      apply (sTUP2_1 [] 4 12 4
             ((1, 1) :: repeat (1, 2) 45
              ++ (16, 2) :: (1, 1) :: repeat (1, 2) 244
              ++ (843, 2) :: (1, 1) :: repeat (1, 2) 3324
              ++ (600, 2) :: (1, 1)
              :: repeat (1, 2) 16300 ++ w) 1); closearith. }
    apply (hsteps_trans _ (HB [5] 13 1 4
      ((2, 2) :: (1, 1) :: repeat (1, 2) 45
       ++ (16, 2) :: (1, 1) :: repeat (1, 2) 244
       ++ (843, 2) :: (1, 1) :: repeat (1, 2) 3324
       ++ (600, 2) :: (1, 1) :: repeat (1, 2) 16300 ++ w) 1)).
    { apply (sTDN [5] 13
             ((2, 2) :: (1, 1) :: repeat (1, 2) 45
              ++ (16, 2) :: (1, 1) :: repeat (1, 2) 244
              ++ (843, 2) :: (1, 1) :: repeat (1, 2) 3324
              ++ (600, 2) :: (1, 1)
              :: repeat (1, 2) 16300 ++ w) 1). }
    apply (sTRANS2_1 [5] 13 3 1
           (repeat (1, 2) 45
            ++ (16, 2) :: (1, 1) :: repeat (1, 2) 244
            ++ (843, 2) :: (1, 1) :: repeat (1, 2) 3324
            ++ (600, 2) :: (1, 1) :: repeat (1, 2) 16300 ++ w)
           1); closearith. }
  (* S42: pop12 45, front(16) onto [50; 14; 5] *)
  apply (hsteps_trans _ (HC [50; 14; 5] 92 3 2
    ((10, 2) :: (1, 1) :: repeat (1, 2) 244
     ++ (843, 2) :: (1, 1) :: repeat (1, 2) 3324
     ++ (600, 2) :: (1, 1) :: repeat (1, 2) 16300 ++ w) 1)).
  { apply (hsteps_trans _ (HB [14; 5] 50 1 93
      ((16, 2) :: (1, 1) :: repeat (1, 2) 244
       ++ (843, 2) :: (1, 1) :: repeat (1, 2) 3324
       ++ (600, 2) :: (1, 1) :: repeat (1, 2) 16300 ++ w) 1)).
    { apply (pop12 45 [14; 5] 5 3
             ((16, 2) :: (1, 1) :: repeat (1, 2) 244
              ++ (843, 2) :: (1, 1) :: repeat (1, 2) 3324
              ++ (600, 2) :: (1, 1)
              :: repeat (1, 2) 16300 ++ w) 1); closearith. }
    apply (hsteps_trans _ (HC [14; 5] 50 92 2
      ((14, 2) :: (1, 1) :: repeat (1, 2) 244
       ++ (843, 2) :: (1, 1) :: repeat (1, 2) 3324
       ++ (600, 2) :: (1, 1) :: repeat (1, 2) 16300 ++ w) 1)).
    { apply (sTUP [14; 5] 50 93 16 2
             ((1, 1) :: repeat (1, 2) 244
              ++ (843, 2) :: (1, 1) :: repeat (1, 2) 3324
              ++ (600, 2) :: (1, 1)
              :: repeat (1, 2) 16300 ++ w) 1); closearith. }
    apply (hsteps_trans _ (HB [14; 5] 49 1 92
      ((2, 2) :: (14, 2) :: (1, 1) :: repeat (1, 2) 244
       ++ (843, 2) :: (1, 1) :: repeat (1, 2) 3324
       ++ (600, 2) :: (1, 1) :: repeat (1, 2) 16300 ++ w) 1)).
    { apply (hGRIND_even 44 [14; 5] 49
             ((14, 2) :: (1, 1) :: repeat (1, 2) 244
              ++ (843, 2) :: (1, 1) :: repeat (1, 2) 3324
              ++ (600, 2) :: (1, 1)
              :: repeat (1, 2) 16300 ++ w) 1); closearith. }
    apply (hsteps_trans _ (HC [50; 14; 5] 92 1 2
      ((12, 2) :: (1, 1) :: repeat (1, 2) 244
       ++ (843, 2) :: (1, 1) :: repeat (1, 2) 3324
       ++ (600, 2) :: (1, 1) :: repeat (1, 2) 16300 ++ w) 1)).
    { replace ((12, 2) :: (1, 1) :: repeat (1, 2) 244
               ++ (843, 2) :: (1, 1) :: repeat (1, 2) 3324
               ++ (600, 2) :: (1, 1)
               :: repeat (1, 2) 16300 ++ w)
        with ((14 - 2, 2) :: (1, 1) :: repeat (1, 2) 244
              ++ (843, 2) :: (1, 1) :: repeat (1, 2) 3324
              ++ (600, 2) :: (1, 1)
              :: repeat (1, 2) 16300 ++ w)
        by sec_eq.
      apply (sTUP2_1 [14; 5] 49 91 14
             ((1, 1) :: repeat (1, 2) 244
              ++ (843, 2) :: (1, 1) :: repeat (1, 2) 3324
              ++ (600, 2) :: (1, 1)
              :: repeat (1, 2) 16300 ++ w) 1); closearith. }
    apply (hsteps_trans _ (HB [50; 14; 5] 92 1 4
      ((12, 2) :: (1, 1) :: repeat (1, 2) 244
       ++ (843, 2) :: (1, 1) :: repeat (1, 2) 3324
       ++ (600, 2) :: (1, 1) :: repeat (1, 2) 16300 ++ w) 1)).
    { apply (sTDN [50; 14; 5] 92
             ((12, 2) :: (1, 1) :: repeat (1, 2) 244
              ++ (843, 2) :: (1, 1) :: repeat (1, 2) 3324
              ++ (600, 2) :: (1, 1)
              :: repeat (1, 2) 16300 ++ w) 1). }
    replace ((10, 2) :: (1, 1) :: repeat (1, 2) 244
             ++ (843, 2) :: (1, 1) :: repeat (1, 2) 3324
             ++ (600, 2) :: (1, 1) :: repeat (1, 2) 16300 ++ w)
      with ((12 - 2, 2) :: (1, 1) :: repeat (1, 2) 244
            ++ (843, 2) :: (1, 1) :: repeat (1, 2) 3324
            ++ (600, 2) :: (1, 1) :: repeat (1, 2) 16300 ++ w)
      by sec_eq.
    apply (sTUP [50; 14; 5] 92 4 12 2
           ((1, 1) :: repeat (1, 2) 244
            ++ (843, 2) :: (1, 1) :: repeat (1, 2) 3324
            ++ (600, 2) :: (1, 1) :: repeat (1, 2) 16300 ++ w)
           1); closearith. }
  (* S43: CLEANG_even 4 + TRANS2_1 onto [93; 50; 14; 5] *)
  apply (hsteps_trans _ (HB [93; 50; 14; 5] 15 1 3
    (repeat (1, 2) 244
     ++ (843, 2) :: (1, 1) :: repeat (1, 2) 3324
     ++ (600, 2) :: (1, 1) :: repeat (1, 2) 16300 ++ w) 1)).
  { apply (hsteps_trans _ (HB [50; 14; 5] 92 1 14
      ((2, 2) :: (1, 1) :: repeat (1, 2) 244
       ++ (843, 2) :: (1, 1) :: repeat (1, 2) 3324
       ++ (600, 2) :: (1, 1) :: repeat (1, 2) 16300 ++ w) 1)).
    { apply (CLEANG_even 4 [50; 14; 5] 92
             ((1, 1) :: repeat (1, 2) 244
              ++ (843, 2) :: (1, 1) :: repeat (1, 2) 3324
              ++ (600, 2) :: (1, 1)
              :: repeat (1, 2) 16300 ++ w) 1); closearith. }
    apply (sTRANS2_1 [50; 14; 5] 92 13 1
           (repeat (1, 2) 244
            ++ (843, 2) :: (1, 1) :: repeat (1, 2) 3324
            ++ (600, 2) :: (1, 1) :: repeat (1, 2) 16300 ++ w)
           1); closearith. }
  (* S44: pop12 244, front(843) onto [259; 93; 50; 14; 5] *)
  apply (hsteps_trans _ (HC [259; 93; 50; 14; 5] 490 3 2
    ((837, 2) :: (1, 1) :: repeat (1, 2) 3324
     ++ (600, 2) :: (1, 1) :: repeat (1, 2) 16300 ++ w) 1)).
  { apply (hsteps_trans _ (HB [93; 50; 14; 5] 259 1 491
      ((843, 2) :: (1, 1) :: repeat (1, 2) 3324
       ++ (600, 2) :: (1, 1) :: repeat (1, 2) 16300 ++ w) 1)).
    { apply (pop12 244 [93; 50; 14; 5] 15 3
             ((843, 2) :: (1, 1) :: repeat (1, 2) 3324
              ++ (600, 2) :: (1, 1)
              :: repeat (1, 2) 16300 ++ w) 1); closearith. }
    apply (hsteps_trans _ (HC [93; 50; 14; 5] 259 490 2
      ((841, 2) :: (1, 1) :: repeat (1, 2) 3324
       ++ (600, 2) :: (1, 1) :: repeat (1, 2) 16300 ++ w) 1)).
    { apply (sTUP [93; 50; 14; 5] 259 491 843 2
             ((1, 1) :: repeat (1, 2) 3324
              ++ (600, 2) :: (1, 1)
              :: repeat (1, 2) 16300 ++ w) 1); closearith. }
    apply (hsteps_trans _ (HB [93; 50; 14; 5] 258 1 490
      ((2, 2) :: (841, 2) :: (1, 1) :: repeat (1, 2) 3324
       ++ (600, 2) :: (1, 1) :: repeat (1, 2) 16300 ++ w) 1)).
    { apply (hGRIND_even 243 [93; 50; 14; 5] 258
             ((841, 2) :: (1, 1) :: repeat (1, 2) 3324
              ++ (600, 2) :: (1, 1)
              :: repeat (1, 2) 16300 ++ w) 1); closearith. }
    apply (hsteps_trans _ (HC [259; 93; 50; 14; 5] 490 1 2
      ((839, 2) :: (1, 1) :: repeat (1, 2) 3324
       ++ (600, 2) :: (1, 1) :: repeat (1, 2) 16300 ++ w) 1)).
    { replace ((839, 2) :: (1, 1) :: repeat (1, 2) 3324
               ++ (600, 2) :: (1, 1)
               :: repeat (1, 2) 16300 ++ w)
        with ((841 - 2, 2) :: (1, 1) :: repeat (1, 2) 3324
              ++ (600, 2) :: (1, 1)
              :: repeat (1, 2) 16300 ++ w)
        by sec_eq.
      apply (sTUP2_1 [93; 50; 14; 5] 258 489 841
             ((1, 1) :: repeat (1, 2) 3324
              ++ (600, 2) :: (1, 1)
              :: repeat (1, 2) 16300 ++ w) 1); closearith. }
    apply (hsteps_trans _ (HB [259; 93; 50; 14; 5] 490 1 4
      ((839, 2) :: (1, 1) :: repeat (1, 2) 3324
       ++ (600, 2) :: (1, 1) :: repeat (1, 2) 16300 ++ w) 1)).
    { apply (sTDN [259; 93; 50; 14; 5] 490
             ((839, 2) :: (1, 1) :: repeat (1, 2) 3324
              ++ (600, 2) :: (1, 1)
              :: repeat (1, 2) 16300 ++ w) 1). }
    replace ((837, 2) :: (1, 1) :: repeat (1, 2) 3324
             ++ (600, 2) :: (1, 1) :: repeat (1, 2) 16300 ++ w)
      with ((839 - 2, 2) :: (1, 1) :: repeat (1, 2) 3324
            ++ (600, 2) :: (1, 1) :: repeat (1, 2) 16300 ++ w)
      by sec_eq.
    apply (sTUP [259; 93; 50; 14; 5] 490 4 839 2
           ((1, 1) :: repeat (1, 2) 3324
            ++ (600, 2) :: (1, 1) :: repeat (1, 2) 16300 ++ w)
           1); closearith. }
  (* S45: CLEANG_odd 417 *)
  apply (hsteps_trans _ (HB [259; 93; 50; 14; 5] 490 1 842
    ((1, 2) :: (1, 1) :: repeat (1, 2) 3324
     ++ (600, 2) :: (1, 1) :: repeat (1, 2) 16300 ++ w) 1)).
  { apply (CLEANG_odd 417 [259; 93; 50; 14; 5] 490
           ((1, 1) :: repeat (1, 2) 3324
            ++ (600, 2) :: (1, 1) :: repeat (1, 2) 16300 ++ w)
           1); closearith. }
  (* S46: pop12 1 + POP + pop12 3324, front(600) onto *)
  (* [3816; 259; 93; 50; 14; 5]                            *)
  apply (hsteps_trans _ (HC [3816; 259; 93; 50; 14; 5] 7492 3 2
    ((594, 2) :: (1, 1) :: repeat (1, 2) 16300 ++ w) 1)).
  { apply (hsteps_trans _ (HB [259; 93; 50; 14; 5] 491 1 844
      ((1, 1) :: repeat (1, 2) 3324
       ++ (600, 2) :: (1, 1) :: repeat (1, 2) 16300 ++ w) 1)).
    { replace ((1, 2) :: (1, 1) :: repeat (1, 2) 3324
               ++ (600, 2) :: (1, 1)
               :: repeat (1, 2) 16300 ++ w)
        with (repeat (1, 2) 1
              ++ ((1, 1) :: repeat (1, 2) 3324
                  ++ (600, 2) :: (1, 1)
                  :: repeat (1, 2) 16300 ++ w))
        by sec_eq.
      apply (pop12 1 [259; 93; 50; 14; 5] 490 842
             ((1, 1) :: repeat (1, 2) 3324
              ++ (600, 2) :: (1, 1)
              :: repeat (1, 2) 16300 ++ w) 1); closearith. }
    apply (hsteps_trans _ (HB [259; 93; 50; 14; 5] 492 1 845
      (repeat (1, 2) 3324
       ++ (600, 2) :: (1, 1) :: repeat (1, 2) 16300 ++ w) 1)).
    { apply (sPOP1 [259; 93; 50; 14; 5] 491 844
             (repeat (1, 2) 3324
              ++ (600, 2) :: (1, 1)
              :: repeat (1, 2) 16300 ++ w) 1); closearith. }
    apply (hsteps_trans _ (HB [259; 93; 50; 14; 5] 3816 1 7493
      ((600, 2) :: (1, 1) :: repeat (1, 2) 16300 ++ w) 1)).
    { apply (pop12 3324 [259; 93; 50; 14; 5] 492 845
             ((600, 2) :: (1, 1) :: repeat (1, 2) 16300 ++ w)
             1); closearith. }
    apply (hsteps_trans _ (HC [259; 93; 50; 14; 5] 3816 7492 2
      ((598, 2) :: (1, 1) :: repeat (1, 2) 16300 ++ w) 1)).
    { apply (sTUP [259; 93; 50; 14; 5] 3816 7493 600 2
             ((1, 1) :: repeat (1, 2) 16300 ++ w) 1);
        closearith. }
    apply (hsteps_trans _ (HB [259; 93; 50; 14; 5] 3815 1 7492
      ((2, 2) :: (598, 2) :: (1, 1)
       :: repeat (1, 2) 16300 ++ w) 1)).
    { apply (hGRIND_even 3744 [259; 93; 50; 14; 5] 3815
             ((598, 2) :: (1, 1) :: repeat (1, 2) 16300 ++ w)
             1); closearith. }
    apply (hsteps_trans _ (HC [3816; 259; 93; 50; 14; 5]
      7492 1 2 ((596, 2) :: (1, 1)
       :: repeat (1, 2) 16300 ++ w) 1)).
    { replace ((596, 2) :: (1, 1) :: repeat (1, 2) 16300 ++ w)
        with ((598 - 2, 2) :: (1, 1)
              :: repeat (1, 2) 16300 ++ w)
        by sec_eq.
      apply (sTUP2_1 [259; 93; 50; 14; 5] 3815 7491 598
             ((1, 1) :: repeat (1, 2) 16300 ++ w) 1);
        closearith. }
    apply (hsteps_trans _ (HB [3816; 259; 93; 50; 14; 5]
      7492 1 4 ((596, 2) :: (1, 1)
       :: repeat (1, 2) 16300 ++ w) 1)).
    { apply (sTDN [3816; 259; 93; 50; 14; 5] 7492
             ((596, 2) :: (1, 1) :: repeat (1, 2) 16300 ++ w)
             1). }
    replace ((594, 2) :: (1, 1) :: repeat (1, 2) 16300 ++ w)
      with ((596 - 2, 2) :: (1, 1) :: repeat (1, 2) 16300 ++ w)
      by sec_eq.
    apply (sTUP [3816; 259; 93; 50; 14; 5] 7492 4 596 2
           ((1, 1) :: repeat (1, 2) 16300 ++ w) 1);
      closearith. }
  (* S47: CLEANG_even 296 + TRANS2_1 + pop12 16300 = TOP3 *)
  apply (hsteps_trans _ (HB [3816; 259; 93; 50; 14; 5] 7492 1 598
    ((2, 2) :: (1, 1) :: repeat (1, 2) 16300 ++ w) 1)).
  { apply (CLEANG_even 296 [3816; 259; 93; 50; 14; 5] 7492
           ((1, 1) :: repeat (1, 2) 16300 ++ w) 1);
      closearith. }
  apply (hsteps_trans _ (HB [7493; 3816; 259; 93; 50; 14; 5]
    599 1 3 (repeat (1, 2) 16300 ++ w) 1)).
  { apply (sTRANS2_1 [3816; 259; 93; 50; 14; 5] 7492 597 1
           (repeat (1, 2) 16300 ++ w) 1); closearith. }
  apply (pop12 16300 [7493; 3816; 259; 93; 50; 14; 5] 599 3 w 1);
    closearith.
Qed.

(* ----------------------------------------------------------------- *)
(* TOP49_TO_TOP3: TOP2 -> front (TUP, hGRIND_even 8147, TUP2_1,    *)
(* TDN, TUP -- the TOP48_BAND front shape) -> GRIND3 ->             *)
(* DIPGRIND (16298, 2 * (j - 16301)) -> CASCADE49 -> TOP3, uniform  *)
(* in (j, beta) for j >= 16302.  The target pair is written         *)
(* (2 * (j - 16301), 2) so it matches the TOP49_BAND /              *)
(* TAIL2_END4 instantiations syntactically.                         *)
(* ----------------------------------------------------------------- *)

Lemma TOP49_TO_TOP3 : forall j beta, 16302 <= j -> 2 <= beta ->
  hsteps (HB [1589; 225; 40; 14; 5] 10430 1 16299
            ((2 * j, 2) :: (1, 1) :: repeat (1, 2) (beta - 1)) 1)
         (HB [7493; 3816; 259; 93; 50; 14; 5] 16899 1 32603
            ((2 * (j - 16301), 2) :: (1, 1)
             :: repeat (1, 2) (beta - 1)) 1).
Proof.
  intros j beta Hj Hb.
  (* lia cannot use Hj directly: 16302 is an of_num_uint atom,    *)
  (* unrelated in lia's eyes to the numerals below.  Derive a     *)
  (* numeral lower bound on j, and normalise the 16301/16302      *)
  (* atoms onto the single atom 16298 where an identity needs     *)
  (* them.                                                        *)
  assert (Hj4 : 4 <= j).
  { apply Nat.le_trans with 16302; [closearith | exact Hj]. }
  assert (Hr : 1 <= j - 16301).
  { change 16301 with (16302 - 1). lia. }
  assert (Heq : 2 * j - 6 = 2 * 16298 + 2 * (j - 16301)).
  { change 16301 with (16298 + 3).
    change 16302 with (16298 + 4) in Hj. lia. }
  apply (hsteps_trans _ (HC [1589; 225; 40; 14; 5] 10430
    16298 2 ((2 * j - 2, 2) :: (1, 1) :: repeat (1, 2) (beta - 1)) 1)).
  { apply (sTUP [1589; 225; 40; 14; 5] 10430 16299 (2 * j) 2
           ((1, 1) :: repeat (1, 2) (beta - 1)) 1); closearith. }
  apply (hsteps_trans _ (HB [1589; 225; 40; 14; 5] 10429
    1 16298 ((2, 2) :: (2 * j - 2, 2) :: (1, 1)
            :: repeat (1, 2) (beta - 1)) 1)).
  { apply (hGRIND_even 8147 [1589; 225; 40; 14; 5] 10429
           ((2 * j - 2, 2) :: (1, 1) :: repeat (1, 2) (beta - 1))
           1); closearith. }
  apply (hsteps_trans _ (HC [10430; 1589; 225; 40; 14; 5]
    16298 1 2 ((2 * j - 4, 2) :: (1, 1) :: repeat (1, 2) (beta - 1)) 1)).
  { replace ((2 * j - 4, 2) :: (1, 1) :: repeat (1, 2) (beta - 1))
      with ((2 * j - 2 - 2, 2) :: (1, 1) :: repeat (1, 2) (beta - 1))
      by sec_eq.
    apply (sTUP2_1 [1589; 225; 40; 14; 5] 10429 16297
           (2 * j - 2) ((1, 1) :: repeat (1, 2) (beta - 1)) 1); lia. }
  apply (hsteps_trans _ (HB [10430; 1589; 225; 40; 14; 5]
    16298 1 4 ((2 * j - 4, 2) :: (1, 1) :: repeat (1, 2) (beta - 1)) 1)).
  { apply (sTDN [10430; 1589; 225; 40; 14; 5] 16298
           ((2 * j - 4, 2) :: (1, 1) :: repeat (1, 2) (beta - 1))
           1). }
  apply (hsteps_trans _ (HC [10430; 1589; 225; 40; 14; 5]
    16298 3 2 ((2 * j - 6, 2) :: (1, 1) :: repeat (1, 2) (beta - 1)) 1)).
  { replace ((2 * j - 6, 2) :: (1, 1) :: repeat (1, 2) (beta - 1))
      with ((2 * j - 4 - 2, 2) :: (1, 1) :: repeat (1, 2) (beta - 1))
      by sec_eq.
    apply (sTUP [10430; 1589; 225; 40; 14; 5] 16298 4
           (2 * j - 4) 2 ((1, 1) :: repeat (1, 2) (beta - 1)) 1);
      lia. }
  apply (hsteps_trans _ (HC [10430; 1589; 225; 40; 14; 5]
    0 3 2 (repeat (1, 2) 16298
     ++ ((2 * (j - 16301), 2) :: (1, 1)
         :: repeat (1, 2) (beta - 1))) 1)).
  { rewrite Heq.
    apply (DIPGRIND 16298 (2 * (j - 16301))
           [10430; 1589; 225; 40; 14; 5]
           ((1, 1) :: repeat (1, 2) (beta - 1)) 1);
      [closearith | lia]. }
  apply (CASCADE49 ((2 * (j - 16301), 2) :: (1, 1)
                    :: repeat (1, 2) (beta - 1))).
Qed.

(* ----------------------------------------------------------------- *)
(* The TOP3 closings: r3 = 2, r3 = 4, r3 = 6, and band 3            *)
(* (r3 = 2 * j3, 4 <= j3 <= 32605, i.e. 8 <= r3 <= 65210).          *)
(* ----------------------------------------------------------------- *)

Lemma TOP49_2 : forall beta, 2 <= beta ->
  hsteps (HB [7493; 3816; 259; 93; 50; 14; 5] 16899 1 32603
            ((2, 2) :: (1, 1) :: repeat (1, 2) (beta - 1)) 1)
         (HB [16900; 7493; 3816; 259; 93; 50; 14; 5]
            (32604 + (beta - 1)) 1 (2 * beta + 1) [] 1).
Proof.
  intros beta Hb.
  apply (hsteps_trans _ (HB [16900; 7493; 3816; 259; 93; 50; 14; 5]
    32604 1 3 (repeat (1, 2) (beta - 1)) 1)).
  { apply (sTRANS2_1 [7493; 3816; 259; 93; 50; 14; 5] 16899 32602 1
           (repeat (1, 2) (beta - 1)) 1); lia. }
  apply (CASCADE_POPFIN [16900; 7493; 3816; 259; 93; 50; 14; 5]
         32604 beta); lia.
Qed.

Lemma TOP49_4 : forall beta, 2 <= beta ->
  hsteps (HB [7493; 3816; 259; 93; 50; 14; 5] 16899 1 32603
            ((4, 2) :: (1, 1) :: repeat (1, 2) (beta - 1)) 1)
         (HB [32603; 16899; 7493; 3816; 259; 93; 50; 14; 5]
            (beta + 2) 1 (2 * beta + 1) [] 1).
Proof.
  intros beta Hb.
  apply (hsteps_trans _ (HC [7493; 3816; 259; 93; 50; 14; 5] 16899
    32602 2 ((2, 2) :: (1, 1) :: repeat (1, 2) (beta - 1)) 1)).
  { apply (sTUP [7493; 3816; 259; 93; 50; 14; 5] 16899 32603 4 2
           ((1, 1) :: repeat (1, 2) (beta - 1)) 1); closearith. }
  apply (hsteps_trans _ (HB [7493; 3816; 259; 93; 50; 14; 5] 16898
    1 32602 ((2, 2) :: (2, 2) :: (1, 1)
            :: repeat (1, 2) (beta - 1)) 1)).
  { apply (hGRIND_even 16299 [7493; 3816; 259; 93; 50; 14; 5] 16898
           ((2, 2) :: (1, 1) :: repeat (1, 2) (beta - 1)) 1);
      closearith. }
  apply (hsteps_trans _ (HB [32603; 16899; 7493; 3816; 259; 93;
    50; 14; 5] 3 1 3 (repeat (1, 2) (beta - 1)) 1)).
  { apply (hsteps_step _ (HB [32603; 16899; 7493; 3816; 259; 93;
      50; 14; 5] 3 1 3 (repeat (1, 2) (beta - 1)) 1));
      [apply hTRANS2_2; closearith | apply hsteps_refl]. }
  replace (beta + 2) with (3 + (beta - 1)) by lia.
  apply (CASCADE_POPFIN [32603; 16899; 7493; 3816; 259; 93; 50; 14; 5]
         3 beta); lia.
Qed.

Lemma TOP49_6 : forall beta, 2 <= beta ->
  hsteps (HB [7493; 3816; 259; 93; 50; 14; 5] 16899 1 32603
            ((6, 2) :: (1, 1) :: repeat (1, 2) (beta - 1)) 1)
         (HB [32603; 16899; 7493; 3816; 259; 93; 50; 14; 5]
            (beta + 4) 1 (2 * beta + 1) [] 1).
Proof.
  intros beta Hb.
  apply (hsteps_trans _ (HC [7493; 3816; 259; 93; 50; 14; 5] 16899
    32602 2 ((4, 2) :: (1, 1) :: repeat (1, 2) (beta - 1)) 1)).
  { apply (sTUP [7493; 3816; 259; 93; 50; 14; 5] 16899 32603 6 2
           ((1, 1) :: repeat (1, 2) (beta - 1)) 1); closearith. }
  apply (hsteps_trans _ (HB [7493; 3816; 259; 93; 50; 14; 5] 16898
    1 32602 ((2, 2) :: (4, 2) :: (1, 1)
            :: repeat (1, 2) (beta - 1)) 1)).
  { apply (hGRIND_even 16299 [7493; 3816; 259; 93; 50; 14; 5] 16898
           ((4, 2) :: (1, 1) :: repeat (1, 2) (beta - 1)) 1);
      closearith. }
  apply (hsteps_trans _ (HC [16899; 7493; 3816; 259; 93; 50; 14; 5]
    32602 1 2 ((2, 2) :: (1, 1) :: repeat (1, 2) (beta - 1)) 1)).
  { replace ((2, 2) :: (1, 1) :: repeat (1, 2) (beta - 1))
      with ((4 - 2, 2) :: (1, 1) :: repeat (1, 2) (beta - 1))
      by sec_eq.
    apply (sTUP2_1 [7493; 3816; 259; 93; 50; 14; 5] 16898 32601 4
           ((1, 1) :: repeat (1, 2) (beta - 1)) 1); lia. }
  apply (hsteps_trans _ (HB [16899; 7493; 3816; 259; 93; 50; 14; 5]
    32602 1 4 ((2, 2) :: (1, 1) :: repeat (1, 2) (beta - 1)) 1)).
  { apply (sTDN [16899; 7493; 3816; 259; 93; 50; 14; 5] 32602
           ((2, 2) :: (1, 1) :: repeat (1, 2) (beta - 1)) 1). }
  apply (hsteps_trans _ (HB [32603; 16899; 7493; 3816; 259; 93;
    50; 14; 5] 5 1 3 (repeat (1, 2) (beta - 1)) 1)).
  { apply (sTRANS2_1 [16899; 7493; 3816; 259; 93; 50; 14; 5] 32602
           3 1 (repeat (1, 2) (beta - 1)) 1); lia. }
  replace (beta + 4) with (5 + (beta - 1)) by lia.
  apply (CASCADE_POPFIN [32603; 16899; 7493; 3816; 259; 93; 50; 14; 5]
         5 beta); lia.
Qed.

Lemma TOP49_BAND : forall j beta, 4 <= j -> j <= 32605 -> 2 <= beta ->
  hsteps (HB [7493; 3816; 259; 93; 50; 14; 5] 16899 1 32603
            ((2 * j, 2) :: (1, 1) :: repeat (1, 2) (beta - 1)) 1)
         (HB [32603; 16899; 7493; 3816; 259; 93; 50; 14; 5]
            (2 * j + beta - 2) 1 (2 * beta + 1) [] 1).
Proof.
  intros j beta Hj1 Hj2 Hb.
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
  apply (hsteps_trans _ (HB [16899; 7493; 3816; 259; 93; 50; 14; 5]
    32602 1 (2 * j - 2)
    ((2, 2) :: (1, 1) :: repeat (1, 2) (beta - 1)) 1)).
  { replace (2 * j - 6) with (2 * (j - 4) + 2) by lia.
    replace (2 * j - 2) with (2 * (j - 4) + 6) by lia.
    apply (CLEANG_even (j - 4) [16899; 7493; 3816; 259; 93; 50; 14; 5]
           32602 ((1, 1) :: repeat (1, 2) (beta - 1)) 1).
    (* the floor (j - 4) + 1 <= 32602: route via j <= 32605 *)
    apply Nat.le_trans with (j - 3).
    - lia.
    - change 32602 with (32605 - 3).
      apply Nat.sub_le_mono_r. exact Hj2. }
  apply (hsteps_trans _ (HB [32603; 16899; 7493; 3816; 259; 93;
    50; 14; 5] (2 * j - 1) 1 3 (repeat (1, 2) (beta - 1)) 1)).
  { replace (2 * j - 2) with (S (2 * j - 3)) by lia.
    replace (2 * j - 1) with (S (S (2 * j - 3))) by lia.
    apply (sTRANS2_1 [16899; 7493; 3816; 259; 93; 50; 14; 5] 32602
           (2 * j - 3) 1 (repeat (1, 2) (beta - 1)) 1); lia. }
  replace (2 * j + beta - 2) with (2 * j - 1 + (beta - 1)) by lia.
  apply (CASCADE_POPFIN [32603; 16899; 7493; 3816; 259; 93; 50; 14; 5]
         (2 * j - 1) beta); lia.
Qed.

(* ----------------------------------------------------------------- *)
(* TAIL2_END4: the strictly smaller residual core -- the totality   *)
(* of the TOP3 state for r3 = 2 * j, j >= 32606 (r3 >= 65212),      *)
(* where the GRIND4 pair (r3 - 6, 2) at counter 32602 takes the     *)
(* DIPDESC boundary a fourth time.  A Definition (lemma             *)
(* parameter), never an axiom.                                      *)
(* ----------------------------------------------------------------- *)

Definition TAIL2_END4 : Prop :=
  forall j beta, 32606 <= j -> 2 <= beta ->
  exists pb A, beta <= A /\
    hsteps (HB [7493; 3816; 259; 93; 50; 14; 5] 16899 1 32603
              ((2 * j, 2) :: (1, 1) :: repeat (1, 2) (beta - 1)) 1)
           (HB pb A 1 (2 * beta + 1) [] 1).

(* ----------------------------------------------------------------- *)
(* TAIL2_END3_of49: TAIL2_END3, modulo TAIL2_END4.  The j-range     *)
(* splits at r3 = 2 * (j - 16301): the three small cases and        *)
(* band 3 are proved above; j - 16301 >= 32606 is the core.         *)
(* ----------------------------------------------------------------- *)

Lemma TAIL2_END3_of49 : TAIL2_END4 -> TAIL2_END3.
Proof.
  intros H4 j beta Hj Hb.
  pose proof (TOP49_TO_TOP3 j beta Hj Hb) as Htop.
  destruct (le_lt_dec 32606 (j - 16301)) as [Hbig | Hsmall].
  - (* j3 = j - 16301 >= 32606: the core *)
    destruct (H4 (j - 16301) beta Hbig Hb)
      as [pb [A [Ha Hsteps]]].
    exists pb, A. split; [exact Ha |].
    exact (hsteps_trans _ _ _ Htop Hsteps).
  - destruct (le_lt_dec 4 (j - 16301)) as [Hband | Htiny].
    + (* band 3: j3 = j - 16301, 4 <= j3 <= 32605 *)
      exists [32603; 16899; 7493; 3816; 259; 93; 50; 14; 5],
        (2 * (j - 16301) + beta - 2).
      split; [lia |].
      assert (Hj2 : j - 16301 <= 32605).
      { change 32606 with (S 32605) in Hsmall.
        apply (proj1 (Nat.lt_succ_r _ _) Hsmall). }
      exact (hsteps_trans _ _ _ Htop
               (TOP49_BAND (j - 16301) beta Hband Hj2 Hb)).
    + (* tiny: j3 = j - 16301 <= 3; j3 >= 1 since 16302 <= j *)
      destruct (Nat.eq_dec (j - 16301) 1) as [He | Hne].
      * (* r3 = 2 *)
        rewrite He in Htop.
        exists [16900; 7493; 3816; 259; 93; 50; 14; 5],
          (32604 + (beta - 1)).
        split; [change 32604 with (S 32603); lia |].
        exact (hsteps_trans _ _ _ Htop (TOP49_2 beta Hb)).
      * destruct (Nat.eq_dec (j - 16301) 2) as [He | Hne'].
        -- (* r3 = 4 *)
           rewrite He in Htop.
           exists [32603; 16899; 7493; 3816; 259; 93; 50; 14; 5],
             (beta + 2).
           split; [lia |].
           exact (hsteps_trans _ _ _ Htop (TOP49_4 beta Hb)).
        -- destruct (Nat.eq_dec (j - 16301) 3) as [He | Hne''].
           ++ (* r3 = 6 *)
              rewrite He in Htop.
              exists [32603; 16899; 7493; 3816; 259; 93; 50; 14; 5],
                (beta + 4).
              split; [lia |].
              exact (hsteps_trans _ _ _ Htop (TOP49_6 beta Hb)).
           ++ (* j3 = 0, contradicting 16302 <= j *)
              exfalso.
              assert (H0 : j - 16301 = 0) by lia.
              change 16302 with (S 16301) in Hj.
              lia.
Qed.

(* ----------------------------------------------------------------- *)
(* ESC_ERA_LAW_49: the phase-8 ESC era law at every even            *)
(* R >= 1278, modulo TAIL2_END4 alone.                              *)
(* ----------------------------------------------------------------- *)

Lemma ESC_ERA_LAW_49 : TAIL2_END4 ->
  forall M beta, 616 <= M -> 2 <= beta ->
  exists n c pb a,
    run n (esc_src (2 * M + 52) (beta - 2)) = Some c
    /\ cfg_sim c (rcsec (false :: repeat true (S a) ++ enc pb)
                        (2 * beta + 2) [(1, 2)])
    /\ beta <= a.
Proof.
  intros H M beta HM Hb.
  apply (ESC_ERA_LAW_48 (TAIL2_END3_of49 H) M beta HM Hb).
Qed.

(* ----------------------------------------------------------------- *)
(* Assumption audit                                                  *)
(* ----------------------------------------------------------------- *)

Print Assumptions CASCADE49.
Print Assumptions TOP49_TO_TOP3.
Print Assumptions TOP49_2.
Print Assumptions TOP49_4.
Print Assumptions TOP49_6.
Print Assumptions TOP49_BAND.
Print Assumptions TAIL2_END3_of49.
Print Assumptions ESC_ERA_LAW_49.
