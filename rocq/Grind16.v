(* ================================================================= *)
(*  Grind16.v -- Phase 48: the second re-descent cascade of the     *)
(*  TOP state, mechanised as a fixed parse, closing TAIL2_END2      *)
(*  for the whole first j-band 7430 <= j <= 23730 and reducing      *)
(*  the rest to a strictly smaller core at the TOP2 state.          *)
(*                                                                  *)
(*  Phase 47 left the ESC side of H_LOOP resting on TAIL2_END2      *)
(*  (Grind15.v): the totality of the TOP state                      *)
(*                                                                  *)
(*    TOP(j, beta) = HB [1279; 745; 151; 77; 35; 20; 0] 4001 1      *)
(*                    7427 ((2j, 2) :: (1, 1) :: (1, 2)^(beta - 1)) *)
(*                                                                  *)
(*  for j >= 7430.  There the GRIND2 pair (2j - 6, 2) at counter    *)
(*  7426 exceeds the CLEANG_even floor and takes the DIPDESC        *)
(*  boundary a second time.  Phase 48 traces the walk               *)
(*  (rocq/hsim48.py, ALL PASS: the 26-waypoint chain below          *)
(*  asserted verbatim at (j, beta) in {(7430, 2), (7430, 3),        *)
(*  (7431, 2), (8000, 2), (23730, 2), (23731, 2)}; TOP2 finals      *)
(*  and the cycle-3 fence asserted too; a junk-tail probe           *)
(*  confirms CASCADE48 is stated for an arbitrary tail).            *)
(*                                                                  *)
(*  FINDING: the second descent is again a FIXED parse, uniform     *)
(*  in (j, beta), in which the residue pair (r, 2),                 *)
(*  r = 2(j - 7429) = 2j - 14858, rides untouched at the bottom     *)
(*  of the stack:                                                   *)
(*                                                                  *)
(*    TOP --front (TUP, hGRIND_even 3711, TUP2_1, TDN, TUP)-->      *)
(*      GRIND2 = HC [4001; 1279; ...] 7426 3 2 ((2j - 6, 2) :: t)   *)
(*    --DIPGRIND (7426, r)-->                                       *)
(*      HC [4001; 1279; ...] 0 3 2 ((1, 2)^7426 ++ W),              *)
(*        W = ((r, 2) :: (1, 1) :: (1, 2)^(beta - 1))               *)
(*    --CASCADE48 (fixed parse, arbitrary tail)-->                  *)
(*      TOP2 = HB [1589; 225; 40; 14; 5] 10430 1 16299 W.           *)
(*                                                                  *)
(*  CASCADE48 descends the TOP frame's own blocks by DIPGRIND +     *)
(*  PX2A levels (1277, 1441), (149, 441), (33, 5), then PX2A0,      *)
(*  DIPGRIND (3, 6), PX2B0, a small bottom-frame grind              *)
(*  (DIPGRIND (3, 2), PUSHX, TRANS2_1 regrowth onto [14; 5]),       *)
(*  and two CLEANG_odd grinds (216 at [225; 40; 14; 5], 716 at      *)
(*  [1589; 225; 40; 14; 5]) consuming the carried pairs             *)
(*  (1441, 2) and (1435, 2).                                        *)
(*                                                                  *)
(*  TOP2 then closes by the size of r:                              *)
(*    r = 2:        TRANS2_1 + CASCADE_POPFIN, A = 16299 + beta;    *)
(*    r = 4:        TUP + hGRIND_even 8147 + TRANS2_2               *)
(*                    + CASCADE_POPFIN, A = beta + 2;               *)
(*    r = 6:        TUP + hGRIND_even 8147 + TUP2_1 + TDN           *)
(*                    + TRANS2_1 + CASCADE_POPFIN, A = beta + 4;    *)
(*    8 <= r <= 32602 (band 2): TUP + hGRIND_even 8147 + TUP2_1     *)
(*      + TDN + TUP onto GRIND3 = HC [10430; 1589; ...] 16298 3 2   *)
(*      ((r - 6, 2) :: tail), whose pair grinds CLEANLY by          *)
(*      CLEANG_even (floor (r - 8)/2 + 1 <= 16298, exactly          *)
(*      r <= 32602), then TRANS2_1 + CASCADE_POPFIN,                *)
(*      A = r + beta - 2, frame [16299; 10430; 1589; ...].          *)
(*                                                                  *)
(*  NOTE (a harness-caught correction, before mechanisation):       *)
(*  the band counter is 16298, not 10430 -- TUP2_1 moves the        *)
(*  shuttle 16298 into the counter slot at GRIND3, exactly as       *)
(*  TUP2_1 did at GRIND2 in Phase 47.  A first characterisation     *)
(*  draft with counter 10430 (band r <= 20866) was REFUTED by       *)
(*  hsim48's final-frame assertions and corrected; no proved        *)
(*  statement was ever affected.                                    *)
(*                                                                  *)
(*  For r >= 32604 (j >= 23731) the pair (r - 6, 2) at counter      *)
(*  16298 exceeds the CLEANG_even floor and the rounds take the     *)
(*  DIPDESC boundary a THIRD time (hsim48 Part 3: the GRIND3        *)
(*  state and the DIPGRIND (16298, r - 32602) landing both occur    *)
(*  at j = 23731, 24000, 30000).  The third descent is a NEW         *)
(*  cascade with different constants, so no cycle induction in      *)
(*  the current vocabulary closes it; what remains is the           *)
(*  strictly smaller core                                           *)
(*                                                                  *)
(*    TAIL2_END3: the totality of the ONE pair (2j, 2) at the ONE   *)
(*    fixed TOP2 state HB [1589; 225; 40; 14; 5] 10430 1 16299,     *)
(*    for j >= 16302 (r = 2j >= 32604), beta >= 2.                  *)
(*                                                                  *)
(*  TAIL2_END2 is then proved modulo TAIL2_END3                     *)
(*  (TAIL2_END2_of48), and ESC_ERA_LAW_48 carries it: the ESC       *)
(*  instances at every even R >= 1278 rest on TAIL2_END3 alone.     *)
(*  The j-range of the core shrank from [7430, oo) to               *)
(*  [23731, oo) (in TOP2's own parameter, [16302, oo)), and its     *)
(*  statement sits one full cycle below the TOP state.              *)
(* ================================================================= *)

Require Import List Bool Arith Lia ZArith.
Import ListNotations.
Require Import TM Sections Mirror TokenPass Recoord Era Esc Dev
               Grind Grind2 Grind3 Grind4 Grind5 Grind6 Grind7 Grind8
               Grind9 Grind10 Grind11 Grind12 Grind13 Grind14 Grind15.

Ltac sec_eq := repeat (first [ solve [reflexivity] | solve [lia]
                             | f_equal ]).

(* Note: literals >= 7426 are parsed as Nat.of_num_uint atoms,    *)
(* which lia cannot compare; closearith falls back to computing    *)
(* the boolean <= for closed side conditions.                      *)
Ltac closearith := first [ lia | apply Nat.leb_le; reflexivity ].

(* ----------------------------------------------------------------- *)
(* CASCADE48: the fixed second-descent parse.  From the DIPGRIND    *)
(* landing at frame [4001; 1279; 745; 151; 77; 35; 20; 0] to TOP2,  *)
(* for an ARBITRARY carried tail w (the residue pair (r, 2) and     *)
(* the era tail ride inside w, never inspected).  Waypoints are     *)
(* the hsim48 chain, asserted verbatim.  Stack abbreviations in     *)
(* the comments:                                                    *)
(*   U1 = (1, 1) :: (1, 2)^7428 ++ w          T1 = (1441, 2) :: U1  *)
(*   U2 = (1, 1) :: (1, 2)^1279 ++ T1         T2 = (441, 2) :: U2   *)
(*   U3 = (1, 1) :: (1, 2)^151 ++ T2          T3 = (5, 2) :: U3     *)
(*   U4 = (1, 1) :: (1, 2)^35 ++ T3           U5 = (4, 2) :: U4     *)
(* ----------------------------------------------------------------- *)

Lemma CASCADE48 : forall w,
  hsteps (HC [4001; 1279; 745; 151; 77; 35; 20; 0] 0 3 2
            (repeat (1, 2) 7426 ++ w) 1)
         (HB [1589; 225; 40; 14; 5] 10430 1 16299 w 1).
Proof.
  intro w.
  (* S1: PX2A, PUSH, TDN, TUP onto frame [745; 151; 77; 35; 20; 0], *)
  (* pair (3995, 2)                                                  *)
  apply (hsteps_trans _ (HC [745; 151; 77; 35; 20; 0] 1277 3 2
    ((3995, 2) :: (1, 1) :: repeat (1, 2) 7428 ++ w) 1)).
  { apply (hsteps_trans _ (HC [745; 151; 77; 35; 20; 0] 1278 3999 2
      ((1, 1) :: (1, 2) :: (1, 2) :: repeat (1, 2) 7426 ++ w) 1)).
    { apply (hsteps_step _ (HC [745; 151; 77; 35; 20; 0] 1278 3999 2
        ((1, 1) :: (1, 2) :: (1, 2) :: repeat (1, 2) 7426 ++ w) 1));
        [apply hPX2A | apply hsteps_refl]. }
    apply (hsteps_trans _ (HC [745; 151; 77; 35; 20; 0] 1277 1 2
      ((3997, 2) :: (1, 1) :: (1, 2) :: (1, 2)
       :: repeat (1, 2) 7426 ++ w) 1)).
    { apply (sPUSH [745; 151; 77; 35; 20; 0] 1277 3999
             ((1, 1) :: (1, 2) :: (1, 2) :: repeat (1, 2) 7426 ++ w)
             1); lia. }
    apply (hsteps_trans _ (HB [745; 151; 77; 35; 20; 0] 1277 1 4
      ((3997, 2) :: (1, 1) :: (1, 2) :: (1, 2)
       :: repeat (1, 2) 7426 ++ w) 1)).
    { apply (sTDN [745; 151; 77; 35; 20; 0] 1277
             ((3997, 2) :: (1, 1) :: (1, 2) :: (1, 2)
              :: repeat (1, 2) 7426 ++ w) 1). }
    replace ((3995, 2) :: (1, 1) :: repeat (1, 2) 7428 ++ w)
      with ((3997 - 2, 2) :: (1, 1) :: (1, 2) :: (1, 2)
            :: repeat (1, 2) 7426 ++ w) by sec_eq.
    apply (sTUP [745; 151; 77; 35; 20; 0] 1277 4 3997 2
           ((1, 1) :: (1, 2) :: (1, 2) :: repeat (1, 2) 7426 ++ w)
           1); lia. }
  (* S2: DIPGRIND (1277, 1441) *)
  apply (hsteps_trans _ (HC [745; 151; 77; 35; 20; 0] 0 3 2
    (repeat (1, 2) 1277 ++ (1441, 2) :: (1, 1)
     :: repeat (1, 2) 7428 ++ w) 1)).
  { apply (DIPGRIND 1277 1441 [745; 151; 77; 35; 20; 0]
           ((1, 1) :: repeat (1, 2) 7428 ++ w) 1); lia. }
  (* S3: PX2A, PUSH, TDN, TUP onto frame [77; 35; 20; 0],          *)
  (* pair (739, 2)                                                  *)
  apply (hsteps_trans _ (HC [77; 35; 20; 0] 149 3 2
    ((739, 2) :: (1, 1) :: repeat (1, 2) 1279
     ++ (1441, 2) :: (1, 1) :: repeat (1, 2) 7428 ++ w) 1)).
  { apply (hsteps_trans _ (HC [77; 35; 20; 0] 150 743 2
      ((1, 1) :: (1, 2) :: (1, 2) :: repeat (1, 2) 1277
       ++ (1441, 2) :: (1, 1) :: repeat (1, 2) 7428 ++ w) 1)).
    { apply (hsteps_step _ (HC [77; 35; 20; 0] 150 743 2
        ((1, 1) :: (1, 2) :: (1, 2) :: repeat (1, 2) 1277
         ++ (1441, 2) :: (1, 1) :: repeat (1, 2) 7428 ++ w) 1));
        [apply hPX2A | apply hsteps_refl]. }
    apply (hsteps_trans _ (HC [77; 35; 20; 0] 149 1 2
      ((741, 2) :: (1, 1) :: (1, 2) :: (1, 2)
       :: repeat (1, 2) 1277
       ++ (1441, 2) :: (1, 1) :: repeat (1, 2) 7428 ++ w) 1)).
    { apply (sPUSH [77; 35; 20; 0] 149 743
             ((1, 1) :: (1, 2) :: (1, 2) :: repeat (1, 2) 1277
              ++ (1441, 2) :: (1, 1) :: repeat (1, 2) 7428 ++ w)
             1); lia. }
    apply (hsteps_trans _ (HB [77; 35; 20; 0] 149 1 4
      ((741, 2) :: (1, 1) :: (1, 2) :: (1, 2)
       :: repeat (1, 2) 1277
       ++ (1441, 2) :: (1, 1) :: repeat (1, 2) 7428 ++ w) 1)).
    { apply (sTDN [77; 35; 20; 0] 149
             ((741, 2) :: (1, 1) :: (1, 2) :: (1, 2)
              :: repeat (1, 2) 1277
              ++ (1441, 2) :: (1, 1) :: repeat (1, 2) 7428 ++ w)
             1). }
    replace ((739, 2) :: (1, 1) :: repeat (1, 2) 1279
             ++ (1441, 2) :: (1, 1) :: repeat (1, 2) 7428 ++ w)
      with ((741 - 2, 2) :: (1, 1) :: (1, 2) :: (1, 2)
            :: repeat (1, 2) 1277
            ++ (1441, 2) :: (1, 1) :: repeat (1, 2) 7428 ++ w)
      by sec_eq.
    apply (sTUP [77; 35; 20; 0] 149 4 741 2
           ((1, 1) :: (1, 2) :: (1, 2) :: repeat (1, 2) 1277
            ++ (1441, 2) :: (1, 1) :: repeat (1, 2) 7428 ++ w)
           1); lia. }
  (* S4: DIPGRIND (149, 441) *)
  apply (hsteps_trans _ (HC [77; 35; 20; 0] 0 3 2
    (repeat (1, 2) 149 ++ (441, 2) :: (1, 1) :: repeat (1, 2) 1279
     ++ (1441, 2) :: (1, 1) :: repeat (1, 2) 7428 ++ w) 1)).
  { apply (DIPGRIND 149 441 [77; 35; 20; 0]
           ((1, 1) :: repeat (1, 2) 1279
            ++ (1441, 2) :: (1, 1) :: repeat (1, 2) 7428 ++ w) 1);
      lia. }
  (* S5: PX2A, PUSH, TDN, TUP onto frame [20; 0], pair (71, 2) *)
  apply (hsteps_trans _ (HC [20; 0] 33 3 2
    ((71, 2) :: (1, 1) :: repeat (1, 2) 151
     ++ (441, 2) :: (1, 1) :: repeat (1, 2) 1279
     ++ (1441, 2) :: (1, 1) :: repeat (1, 2) 7428 ++ w) 1)).
  { apply (hsteps_trans _ (HC [20; 0] 34 75 2
      ((1, 1) :: (1, 2) :: (1, 2) :: repeat (1, 2) 149
       ++ (441, 2) :: (1, 1) :: repeat (1, 2) 1279
       ++ (1441, 2) :: (1, 1) :: repeat (1, 2) 7428 ++ w) 1)).
    { apply (hsteps_step _ (HC [20; 0] 34 75 2
        ((1, 1) :: (1, 2) :: (1, 2) :: repeat (1, 2) 149
         ++ (441, 2) :: (1, 1) :: repeat (1, 2) 1279
         ++ (1441, 2) :: (1, 1) :: repeat (1, 2) 7428 ++ w) 1));
        [apply hPX2A | apply hsteps_refl]. }
    apply (hsteps_trans _ (HC [20; 0] 33 1 2
      ((73, 2) :: (1, 1) :: (1, 2) :: (1, 2)
       :: repeat (1, 2) 149
       ++ (441, 2) :: (1, 1) :: repeat (1, 2) 1279
       ++ (1441, 2) :: (1, 1) :: repeat (1, 2) 7428 ++ w) 1)).
    { apply (sPUSH [20; 0] 33 75
             ((1, 1) :: (1, 2) :: (1, 2) :: repeat (1, 2) 149
              ++ (441, 2) :: (1, 1) :: repeat (1, 2) 1279
              ++ (1441, 2) :: (1, 1) :: repeat (1, 2) 7428 ++ w)
             1); lia. }
    apply (hsteps_trans _ (HB [20; 0] 33 1 4
      ((73, 2) :: (1, 1) :: (1, 2) :: (1, 2)
       :: repeat (1, 2) 149
       ++ (441, 2) :: (1, 1) :: repeat (1, 2) 1279
       ++ (1441, 2) :: (1, 1) :: repeat (1, 2) 7428 ++ w) 1)).
    { apply (sTDN [20; 0] 33
             ((73, 2) :: (1, 1) :: (1, 2) :: (1, 2)
              :: repeat (1, 2) 149
              ++ (441, 2) :: (1, 1) :: repeat (1, 2) 1279
              ++ (1441, 2) :: (1, 1) :: repeat (1, 2) 7428 ++ w)
             1). }
    replace ((71, 2) :: (1, 1) :: repeat (1, 2) 151
             ++ (441, 2) :: (1, 1) :: repeat (1, 2) 1279
             ++ (1441, 2) :: (1, 1) :: repeat (1, 2) 7428 ++ w)
      with ((73 - 2, 2) :: (1, 1) :: (1, 2) :: (1, 2)
            :: repeat (1, 2) 149
            ++ (441, 2) :: (1, 1) :: repeat (1, 2) 1279
            ++ (1441, 2) :: (1, 1) :: repeat (1, 2) 7428 ++ w)
      by sec_eq.
    apply (sTUP [20; 0] 33 4 73 2
           ((1, 1) :: (1, 2) :: (1, 2) :: repeat (1, 2) 149
            ++ (441, 2) :: (1, 1) :: repeat (1, 2) 1279
            ++ (1441, 2) :: (1, 1) :: repeat (1, 2) 7428 ++ w)
           1); lia. }
  (* S6: DIPGRIND (33, 5) *)
  apply (hsteps_trans _ (HC [20; 0] 0 3 2
    (repeat (1, 2) 33 ++ (5, 2) :: (1, 1) :: repeat (1, 2) 151
     ++ (441, 2) :: (1, 1) :: repeat (1, 2) 1279
     ++ (1441, 2) :: (1, 1) :: repeat (1, 2) 7428 ++ w) 1)).
  { apply (DIPGRIND 33 5 [20; 0]
           ((1, 1) :: repeat (1, 2) 151
            ++ (441, 2) :: (1, 1) :: repeat (1, 2) 1279
            ++ (1441, 2) :: (1, 1) :: repeat (1, 2) 7428 ++ w) 1);
      lia. }
  (* S7: PX2A0, TUP, TDN, TUP onto frame [0], pair (12, 2) *)
  apply (hsteps_trans _ (HC [0] 3 3 2
    ((12, 2) :: (1, 1) :: repeat (1, 2) 35
     ++ (5, 2) :: (1, 1) :: repeat (1, 2) 151
     ++ (441, 2) :: (1, 1) :: repeat (1, 2) 1279
     ++ (1441, 2) :: (1, 1) :: repeat (1, 2) 7428 ++ w) 1)).
  { apply (hsteps_trans _ (HB [0] 3 1 2
      ((16, 2) :: (1, 1) :: (1, 2) :: (1, 2)
       :: repeat (1, 2) 33
       ++ (5, 2) :: (1, 1) :: repeat (1, 2) 151
       ++ (441, 2) :: (1, 1) :: repeat (1, 2) 1279
       ++ (1441, 2) :: (1, 1) :: repeat (1, 2) 7428 ++ w) 1)).
    { apply (hsteps_step _ (HB [0] 3 1 2
        ((16, 2) :: (1, 1) :: (1, 2) :: (1, 2)
         :: repeat (1, 2) 33
         ++ (5, 2) :: (1, 1) :: repeat (1, 2) 151
         ++ (441, 2) :: (1, 1) :: repeat (1, 2) 1279
         ++ (1441, 2) :: (1, 1) :: repeat (1, 2) 7428 ++ w) 1));
        [apply hPX2A0 | apply hsteps_refl]. }
    apply (hsteps_trans _ (HC [0] 3 1 2
      ((14, 2) :: (1, 1) :: (1, 2) :: (1, 2)
       :: repeat (1, 2) 33
       ++ (5, 2) :: (1, 1) :: repeat (1, 2) 151
       ++ (441, 2) :: (1, 1) :: repeat (1, 2) 1279
       ++ (1441, 2) :: (1, 1) :: repeat (1, 2) 7428 ++ w) 1)).
    { apply (sTUP [0] 3 2 16 2
             ((1, 1) :: (1, 2) :: (1, 2) :: repeat (1, 2) 33
              ++ (5, 2) :: (1, 1) :: repeat (1, 2) 151
              ++ (441, 2) :: (1, 1) :: repeat (1, 2) 1279
              ++ (1441, 2) :: (1, 1) :: repeat (1, 2) 7428 ++ w)
             1); lia. }
    apply (hsteps_trans _ (HB [0] 3 1 4
      ((14, 2) :: (1, 1) :: (1, 2) :: (1, 2)
       :: repeat (1, 2) 33
       ++ (5, 2) :: (1, 1) :: repeat (1, 2) 151
       ++ (441, 2) :: (1, 1) :: repeat (1, 2) 1279
       ++ (1441, 2) :: (1, 1) :: repeat (1, 2) 7428 ++ w) 1)).
    { apply (sTDN [0] 3
             ((14, 2) :: (1, 1) :: (1, 2) :: (1, 2)
              :: repeat (1, 2) 33
              ++ (5, 2) :: (1, 1) :: repeat (1, 2) 151
              ++ (441, 2) :: (1, 1) :: repeat (1, 2) 1279
              ++ (1441, 2) :: (1, 1) :: repeat (1, 2) 7428 ++ w)
             1). }
    replace ((12, 2) :: (1, 1) :: repeat (1, 2) 35
             ++ (5, 2) :: (1, 1) :: repeat (1, 2) 151
             ++ (441, 2) :: (1, 1) :: repeat (1, 2) 1279
             ++ (1441, 2) :: (1, 1) :: repeat (1, 2) 7428 ++ w)
      with ((14 - 2, 2) :: (1, 1) :: (1, 2) :: (1, 2)
            :: repeat (1, 2) 33
            ++ (5, 2) :: (1, 1) :: repeat (1, 2) 151
            ++ (441, 2) :: (1, 1) :: repeat (1, 2) 1279
            ++ (1441, 2) :: (1, 1) :: repeat (1, 2) 7428 ++ w)
      by sec_eq.
    apply (sTUP [0] 3 4 14 2
           ((1, 1) :: (1, 2) :: (1, 2) :: repeat (1, 2) 33
            ++ (5, 2) :: (1, 1) :: repeat (1, 2) 151
            ++ (441, 2) :: (1, 1) :: repeat (1, 2) 1279
            ++ (1441, 2) :: (1, 1) :: repeat (1, 2) 7428 ++ w)
           1); lia. }
  (* S8: DIPGRIND (3, 6) *)
  apply (hsteps_trans _ (HC [0] 0 3 2
    (repeat (1, 2) 3 ++ (6, 2) :: (1, 1) :: repeat (1, 2) 35
     ++ (5, 2) :: (1, 1) :: repeat (1, 2) 151
     ++ (441, 2) :: (1, 1) :: repeat (1, 2) 1279
     ++ (1441, 2) :: (1, 1) :: repeat (1, 2) 7428 ++ w) 1)).
  { apply (DIPGRIND 3 6 [0]
           ((1, 1) :: repeat (1, 2) 35
            ++ (5, 2) :: (1, 1) :: repeat (1, 2) 151
            ++ (441, 2) :: (1, 1) :: repeat (1, 2) 1279
            ++ (1441, 2) :: (1, 1) :: repeat (1, 2) 7428 ++ w) 1);
      lia. }
  (* S9: PX2B0 onto the bottom frame [] *)
  apply (hsteps_trans _ (HB [] 0 1 5
    (repeat (1, 2) 4 ++ (6, 2) :: (1, 1) :: repeat (1, 2) 35
     ++ (5, 2) :: (1, 1) :: repeat (1, 2) 151
     ++ (441, 2) :: (1, 1) :: repeat (1, 2) 1279
     ++ (1441, 2) :: (1, 1) :: repeat (1, 2) 7428 ++ w) 1)).
  { apply (hsteps_step _ (HB [] 0 1 5
      (repeat (1, 2) 4 ++ (6, 2) :: (1, 1) :: repeat (1, 2) 35
       ++ (5, 2) :: (1, 1) :: repeat (1, 2) 151
       ++ (441, 2) :: (1, 1) :: repeat (1, 2) 1279
       ++ (1441, 2) :: (1, 1) :: repeat (1, 2) 7428 ++ w) 1));
      [apply hPX2B0 | apply hsteps_refl]. }
  (* S10: pop12 4 *)
  apply (hsteps_trans _ (HB [] 4 1 13
    ((6, 2) :: (1, 1) :: repeat (1, 2) 35
     ++ (5, 2) :: (1, 1) :: repeat (1, 2) 151
     ++ (441, 2) :: (1, 1) :: repeat (1, 2) 1279
     ++ (1441, 2) :: (1, 1) :: repeat (1, 2) 7428 ++ w) 1)).
  { apply (pop12 4 [] 0 5
           ((6, 2) :: (1, 1) :: repeat (1, 2) 35
            ++ (5, 2) :: (1, 1) :: repeat (1, 2) 151
            ++ (441, 2) :: (1, 1) :: repeat (1, 2) 1279
            ++ (1441, 2) :: (1, 1) :: repeat (1, 2) 7428 ++ w)
           1); lia. }
  (* S11: TUP, PUSH, TDN, TUP -- the small bottom-frame grind's    *)
  (* front, landing on the DIPGRIND (3, 2) source                   *)
  apply (hsteps_trans _ (HC [] 3 3 2
    ((8, 2) :: (4, 2) :: (1, 1) :: repeat (1, 2) 35
     ++ (5, 2) :: (1, 1) :: repeat (1, 2) 151
     ++ (441, 2) :: (1, 1) :: repeat (1, 2) 1279
     ++ (1441, 2) :: (1, 1) :: repeat (1, 2) 7428 ++ w) 1)).
  { apply (hsteps_trans _ (HC [] 4 12 2
      ((4, 2) :: (1, 1) :: repeat (1, 2) 35
       ++ (5, 2) :: (1, 1) :: repeat (1, 2) 151
       ++ (441, 2) :: (1, 1) :: repeat (1, 2) 1279
       ++ (1441, 2) :: (1, 1) :: repeat (1, 2) 7428 ++ w) 1)).
    { apply (sTUP [] 4 13 6 2
             ((1, 1) :: repeat (1, 2) 35
              ++ (5, 2) :: (1, 1) :: repeat (1, 2) 151
              ++ (441, 2) :: (1, 1) :: repeat (1, 2) 1279
              ++ (1441, 2) :: (1, 1) :: repeat (1, 2) 7428 ++ w)
             1); lia. }
    apply (hsteps_trans _ (HC [] 3 1 2
      ((10, 2) :: (4, 2) :: (1, 1) :: repeat (1, 2) 35
       ++ (5, 2) :: (1, 1) :: repeat (1, 2) 151
       ++ (441, 2) :: (1, 1) :: repeat (1, 2) 1279
       ++ (1441, 2) :: (1, 1) :: repeat (1, 2) 7428 ++ w) 1)).
    { apply (sPUSH [] 3 12
             ((4, 2) :: (1, 1) :: repeat (1, 2) 35
              ++ (5, 2) :: (1, 1) :: repeat (1, 2) 151
              ++ (441, 2) :: (1, 1) :: repeat (1, 2) 1279
              ++ (1441, 2) :: (1, 1) :: repeat (1, 2) 7428 ++ w)
             1); lia. }
    apply (hsteps_trans _ (HB [] 3 1 4
      ((10, 2) :: (4, 2) :: (1, 1) :: repeat (1, 2) 35
       ++ (5, 2) :: (1, 1) :: repeat (1, 2) 151
       ++ (441, 2) :: (1, 1) :: repeat (1, 2) 1279
       ++ (1441, 2) :: (1, 1) :: repeat (1, 2) 7428 ++ w) 1)).
    { apply (sTDN [] 3
             ((10, 2) :: (4, 2) :: (1, 1) :: repeat (1, 2) 35
              ++ (5, 2) :: (1, 1) :: repeat (1, 2) 151
              ++ (441, 2) :: (1, 1) :: repeat (1, 2) 1279
              ++ (1441, 2) :: (1, 1) :: repeat (1, 2) 7428 ++ w)
             1). }
    apply (sTUP [] 3 4 10 2
           ((4, 2) :: (1, 1) :: repeat (1, 2) 35
            ++ (5, 2) :: (1, 1) :: repeat (1, 2) 151
            ++ (441, 2) :: (1, 1) :: repeat (1, 2) 1279
            ++ (1441, 2) :: (1, 1) :: repeat (1, 2) 7428 ++ w)
           1); lia. }
  (* S12: DIPGRIND (3, 2) *)
  apply (hsteps_trans _ (HC [] 0 3 2
    (repeat (1, 2) 3 ++ (2, 2) :: (4, 2) :: (1, 1)
     :: repeat (1, 2) 35
     ++ (5, 2) :: (1, 1) :: repeat (1, 2) 151
     ++ (441, 2) :: (1, 1) :: repeat (1, 2) 1279
     ++ (1441, 2) :: (1, 1) :: repeat (1, 2) 7428 ++ w) 1)).
  { apply (DIPGRIND 3 2 []
           ((4, 2) :: (1, 1) :: repeat (1, 2) 35
            ++ (5, 2) :: (1, 1) :: repeat (1, 2) 151
            ++ (441, 2) :: (1, 1) :: repeat (1, 2) 1279
            ++ (1441, 2) :: (1, 1) :: repeat (1, 2) 7428 ++ w) 1);
      lia. }
  (* S13: PUSHX *)
  apply (hsteps_trans _ (HB [] 1 1 7
    (repeat (1, 2) 3 ++ (2, 2) :: (4, 2) :: (1, 1)
     :: repeat (1, 2) 35
     ++ (5, 2) :: (1, 1) :: repeat (1, 2) 151
     ++ (441, 2) :: (1, 1) :: repeat (1, 2) 1279
     ++ (1441, 2) :: (1, 1) :: repeat (1, 2) 7428 ++ w) 1)).
  { apply (hsteps_step _ (HB [] 1 1 7
      (repeat (1, 2) 3 ++ (2, 2) :: (4, 2) :: (1, 1)
       :: repeat (1, 2) 35
       ++ (5, 2) :: (1, 1) :: repeat (1, 2) 151
       ++ (441, 2) :: (1, 1) :: repeat (1, 2) 1279
       ++ (1441, 2) :: (1, 1) :: repeat (1, 2) 7428 ++ w) 1));
      [apply hPUSHX | apply hsteps_refl]. }
  (* S14: pop12 3 *)
  apply (hsteps_trans _ (HB [] 4 1 13
    ((2, 2) :: (4, 2) :: (1, 1) :: repeat (1, 2) 35
     ++ (5, 2) :: (1, 1) :: repeat (1, 2) 151
     ++ (441, 2) :: (1, 1) :: repeat (1, 2) 1279
     ++ (1441, 2) :: (1, 1) :: repeat (1, 2) 7428 ++ w) 1)).
  { apply (pop12 3 [] 1 7
           ((2, 2) :: (4, 2) :: (1, 1) :: repeat (1, 2) 35
            ++ (5, 2) :: (1, 1) :: repeat (1, 2) 151
            ++ (441, 2) :: (1, 1) :: repeat (1, 2) 1279
            ++ (1441, 2) :: (1, 1) :: repeat (1, 2) 7428 ++ w)
           1); lia. }
  (* S15: TUP2_1, TDN, TRANS2_1 -- regrowth onto frame [14; 5] *)
  apply (hsteps_trans _ (HB [14; 5] 5 1 3
    (repeat (1, 2) 35
     ++ (5, 2) :: (1, 1) :: repeat (1, 2) 151
     ++ (441, 2) :: (1, 1) :: repeat (1, 2) 1279
     ++ (1441, 2) :: (1, 1) :: repeat (1, 2) 7428 ++ w) 1)).
  { apply (hsteps_trans _ (HC [5] 13 1 2
      ((2, 2) :: (1, 1) :: repeat (1, 2) 35
       ++ (5, 2) :: (1, 1) :: repeat (1, 2) 151
       ++ (441, 2) :: (1, 1) :: repeat (1, 2) 1279
       ++ (1441, 2) :: (1, 1) :: repeat (1, 2) 7428 ++ w) 1)).
    { apply (sTUP2_1 [] 4 12 4
             ((1, 1) :: repeat (1, 2) 35
              ++ (5, 2) :: (1, 1) :: repeat (1, 2) 151
              ++ (441, 2) :: (1, 1) :: repeat (1, 2) 1279
              ++ (1441, 2) :: (1, 1) :: repeat (1, 2) 7428 ++ w)
             1); lia. }
    apply (hsteps_trans _ (HB [5] 13 1 4
      ((2, 2) :: (1, 1) :: repeat (1, 2) 35
       ++ (5, 2) :: (1, 1) :: repeat (1, 2) 151
       ++ (441, 2) :: (1, 1) :: repeat (1, 2) 1279
       ++ (1441, 2) :: (1, 1) :: repeat (1, 2) 7428 ++ w) 1)).
    { apply (sTDN [5] 13
             ((2, 2) :: (1, 1) :: repeat (1, 2) 35
              ++ (5, 2) :: (1, 1) :: repeat (1, 2) 151
              ++ (441, 2) :: (1, 1) :: repeat (1, 2) 1279
              ++ (1441, 2) :: (1, 1) :: repeat (1, 2) 7428 ++ w)
             1). }
    apply (sTRANS2_1 [5] 13 3 1
           (repeat (1, 2) 35
            ++ (5, 2) :: (1, 1) :: repeat (1, 2) 151
            ++ (441, 2) :: (1, 1) :: repeat (1, 2) 1279
            ++ (1441, 2) :: (1, 1) :: repeat (1, 2) 7428 ++ w)
           1); lia. }
  (* S16: pop12 35 *)
  apply (hsteps_trans _ (HB [14; 5] 40 1 73
    ((5, 2) :: (1, 1) :: repeat (1, 2) 151
     ++ (441, 2) :: (1, 1) :: repeat (1, 2) 1279
     ++ (1441, 2) :: (1, 1) :: repeat (1, 2) 7428 ++ w) 1)).
  { apply (pop12 35 [14; 5] 5 3
           ((5, 2) :: (1, 1) :: repeat (1, 2) 151
            ++ (441, 2) :: (1, 1) :: repeat (1, 2) 1279
            ++ (1441, 2) :: (1, 1) :: repeat (1, 2) 7428 ++ w)
           1); lia. }
  (* S17: TUP, hGRIND_even 34, TUP2_1, TDN onto frame [40; 14; 5] *)
  apply (hsteps_trans _ (HB [40; 14; 5] 72 1 4
    ((1, 2) :: (1, 1) :: repeat (1, 2) 151
     ++ (441, 2) :: (1, 1) :: repeat (1, 2) 1279
     ++ (1441, 2) :: (1, 1) :: repeat (1, 2) 7428 ++ w) 1)).
  { apply (hsteps_trans _ (HC [14; 5] 40 72 2
      ((3, 2) :: (1, 1) :: repeat (1, 2) 151
       ++ (441, 2) :: (1, 1) :: repeat (1, 2) 1279
       ++ (1441, 2) :: (1, 1) :: repeat (1, 2) 7428 ++ w) 1)).
    { apply (sTUP [14; 5] 40 73 5 2
             ((1, 1) :: repeat (1, 2) 151
              ++ (441, 2) :: (1, 1) :: repeat (1, 2) 1279
              ++ (1441, 2) :: (1, 1) :: repeat (1, 2) 7428 ++ w)
             1); lia. }
    apply (hsteps_trans _ (HB [14; 5] 39 1 72
      ((2, 2) :: (3, 2) :: (1, 1) :: repeat (1, 2) 151
       ++ (441, 2) :: (1, 1) :: repeat (1, 2) 1279
       ++ (1441, 2) :: (1, 1) :: repeat (1, 2) 7428 ++ w) 1)).
    { apply (hGRIND_even 34 [14; 5] 39
             ((3, 2) :: (1, 1) :: repeat (1, 2) 151
              ++ (441, 2) :: (1, 1) :: repeat (1, 2) 1279
              ++ (1441, 2) :: (1, 1) :: repeat (1, 2) 7428 ++ w)
             1); lia. }
    apply (hsteps_trans _ (HC [40; 14; 5] 72 1 2
      ((1, 2) :: (1, 1) :: repeat (1, 2) 151
       ++ (441, 2) :: (1, 1) :: repeat (1, 2) 1279
       ++ (1441, 2) :: (1, 1) :: repeat (1, 2) 7428 ++ w) 1)).
    { apply (sTUP2_1 [14; 5] 39 71 3
             ((1, 1) :: repeat (1, 2) 151
              ++ (441, 2) :: (1, 1) :: repeat (1, 2) 1279
              ++ (1441, 2) :: (1, 1) :: repeat (1, 2) 7428 ++ w)
             1); lia. }
    apply (sTDN [40; 14; 5] 72
           ((1, 2) :: (1, 1) :: repeat (1, 2) 151
            ++ (441, 2) :: (1, 1) :: repeat (1, 2) 1279
            ++ (1441, 2) :: (1, 1) :: repeat (1, 2) 7428 ++ w)
           1). }
  (* S18: pop12 1, POP, pop12 151 *)
  apply (hsteps_trans _ (HB [40; 14; 5] 225 1 309
    ((441, 2) :: (1, 1) :: repeat (1, 2) 1279
     ++ (1441, 2) :: (1, 1) :: repeat (1, 2) 7428 ++ w) 1)).
  { apply (hsteps_trans _ (HB [40; 14; 5] 73 1 6
      ((1, 1) :: repeat (1, 2) 151
       ++ (441, 2) :: (1, 1) :: repeat (1, 2) 1279
       ++ (1441, 2) :: (1, 1) :: repeat (1, 2) 7428 ++ w) 1)).
    { replace ((1, 2) :: (1, 1) :: repeat (1, 2) 151
               ++ (441, 2) :: (1, 1) :: repeat (1, 2) 1279
               ++ (1441, 2) :: (1, 1) :: repeat (1, 2) 7428 ++ w)
        with (repeat (1, 2) 1
              ++ ((1, 1) :: repeat (1, 2) 151
                  ++ (441, 2) :: (1, 1) :: repeat (1, 2) 1279
                  ++ (1441, 2) :: (1, 1) :: repeat (1, 2) 7428 ++ w))
        by sec_eq.
      apply (pop12 1 [40; 14; 5] 72 4
             ((1, 1) :: repeat (1, 2) 151
              ++ (441, 2) :: (1, 1) :: repeat (1, 2) 1279
              ++ (1441, 2) :: (1, 1) :: repeat (1, 2) 7428 ++ w)
             1); lia. }
    apply (hsteps_trans _ (HB [40; 14; 5] 74 1 7
      (repeat (1, 2) 151
       ++ (441, 2) :: (1, 1) :: repeat (1, 2) 1279
       ++ (1441, 2) :: (1, 1) :: repeat (1, 2) 7428 ++ w) 1)).
    { apply (sPOP1 [40; 14; 5] 73 6
             (repeat (1, 2) 151
              ++ (441, 2) :: (1, 1) :: repeat (1, 2) 1279
              ++ (1441, 2) :: (1, 1) :: repeat (1, 2) 7428 ++ w)
             1); lia. }
    apply (pop12 151 [40; 14; 5] 74 7
           ((441, 2) :: (1, 1) :: repeat (1, 2) 1279
            ++ (1441, 2) :: (1, 1) :: repeat (1, 2) 7428 ++ w)
           1); lia. }
  (* S19: TUP, hGRIND_even 152, TUP2_1, TDN, TUP onto frame *)
  (* [225; 40; 14; 5], pair (435, 2)                          *)
  apply (hsteps_trans _ (HC [225; 40; 14; 5] 308 3 2
    ((435, 2) :: (1, 1) :: repeat (1, 2) 1279
     ++ (1441, 2) :: (1, 1) :: repeat (1, 2) 7428 ++ w) 1)).
  { apply (hsteps_trans _ (HC [40; 14; 5] 225 308 2
      ((439, 2) :: (1, 1) :: repeat (1, 2) 1279
       ++ (1441, 2) :: (1, 1) :: repeat (1, 2) 7428 ++ w) 1)).
    { apply (sTUP [40; 14; 5] 225 309 441 2
             ((1, 1) :: repeat (1, 2) 1279
              ++ (1441, 2) :: (1, 1) :: repeat (1, 2) 7428 ++ w)
             1); lia. }
    apply (hsteps_trans _ (HB [40; 14; 5] 224 1 308
      ((2, 2) :: (439, 2) :: (1, 1) :: repeat (1, 2) 1279
       ++ (1441, 2) :: (1, 1) :: repeat (1, 2) 7428 ++ w) 1)).
    { apply (hGRIND_even 152 [40; 14; 5] 224
             ((439, 2) :: (1, 1) :: repeat (1, 2) 1279
              ++ (1441, 2) :: (1, 1) :: repeat (1, 2) 7428 ++ w)
             1); lia. }
    apply (hsteps_trans _ (HC [225; 40; 14; 5] 308 1 2
      ((437, 2) :: (1, 1) :: repeat (1, 2) 1279
       ++ (1441, 2) :: (1, 1) :: repeat (1, 2) 7428 ++ w) 1)).
    { apply (sTUP2_1 [40; 14; 5] 224 307 439
             ((1, 1) :: repeat (1, 2) 1279
              ++ (1441, 2) :: (1, 1) :: repeat (1, 2) 7428 ++ w)
             1); lia. }
    apply (hsteps_trans _ (HB [225; 40; 14; 5] 308 1 4
      ((437, 2) :: (1, 1) :: repeat (1, 2) 1279
       ++ (1441, 2) :: (1, 1) :: repeat (1, 2) 7428 ++ w) 1)).
    { apply (sTDN [225; 40; 14; 5] 308
             ((437, 2) :: (1, 1) :: repeat (1, 2) 1279
              ++ (1441, 2) :: (1, 1) :: repeat (1, 2) 7428 ++ w)
             1). }
    apply (sTUP [225; 40; 14; 5] 308 4 437 2
           ((1, 1) :: repeat (1, 2) 1279
            ++ (1441, 2) :: (1, 1) :: repeat (1, 2) 7428 ++ w)
           1); lia. }
  (* S20: CLEANG_odd at the pair (435, 2) = (2*216+3, 2) *)
  apply (hsteps_trans _ (HB [225; 40; 14; 5] 308 1 440
    ((1, 2) :: (1, 1) :: repeat (1, 2) 1279
     ++ (1441, 2) :: (1, 1) :: repeat (1, 2) 7428 ++ w) 1)).
  { replace (435, 2) with (2 * 216 + 3, 2) by sec_eq.
    replace 440 with (2 * 216 + 8) by lia.
    apply (CLEANG_odd 216 [225; 40; 14; 5] 308
           ((1, 1) :: repeat (1, 2) 1279
            ++ (1441, 2) :: (1, 1) :: repeat (1, 2) 7428 ++ w)
           1); lia. }
  (* S21: pop12 1, POP, pop12 1279 *)
  apply (hsteps_trans _ (HB [225; 40; 14; 5] 1589 1 3001
    ((1441, 2) :: (1, 1) :: repeat (1, 2) 7428 ++ w) 1)).
  { apply (hsteps_trans _ (HB [225; 40; 14; 5] 309 1 442
      ((1, 1) :: repeat (1, 2) 1279
       ++ (1441, 2) :: (1, 1) :: repeat (1, 2) 7428 ++ w) 1)).
    { replace ((1, 2) :: (1, 1) :: repeat (1, 2) 1279
               ++ (1441, 2) :: (1, 1) :: repeat (1, 2) 7428 ++ w)
        with (repeat (1, 2) 1
              ++ ((1, 1) :: repeat (1, 2) 1279
                  ++ (1441, 2) :: (1, 1) :: repeat (1, 2) 7428 ++ w))
        by sec_eq.
      apply (pop12 1 [225; 40; 14; 5] 308 440
             ((1, 1) :: repeat (1, 2) 1279
              ++ (1441, 2) :: (1, 1) :: repeat (1, 2) 7428 ++ w)
             1); lia. }
    apply (hsteps_trans _ (HB [225; 40; 14; 5] 310 1 443
      (repeat (1, 2) 1279
       ++ (1441, 2) :: (1, 1) :: repeat (1, 2) 7428 ++ w) 1)).
    { apply (sPOP1 [225; 40; 14; 5] 309 442
             (repeat (1, 2) 1279
              ++ (1441, 2) :: (1, 1) :: repeat (1, 2) 7428 ++ w)
             1); lia. }
    apply (pop12 1279 [225; 40; 14; 5] 310 443
           ((1441, 2) :: (1, 1) :: repeat (1, 2) 7428 ++ w)
           1); lia. }
  (* S22: TUP, hGRIND_even 1498, TUP2_1, TDN, TUP onto frame *)
  (* [1589; 225; 40; 14; 5], pair (1435, 2)                   *)
  apply (hsteps_trans _ (HC [1589; 225; 40; 14; 5] 3000 3 2
    ((1435, 2) :: (1, 1) :: repeat (1, 2) 7428 ++ w) 1)).
  { apply (hsteps_trans _ (HC [225; 40; 14; 5] 1589 3000 2
      ((1439, 2) :: (1, 1) :: repeat (1, 2) 7428 ++ w) 1)).
    { apply (sTUP [225; 40; 14; 5] 1589 3001 1441 2
             ((1, 1) :: repeat (1, 2) 7428 ++ w) 1); lia. }
    apply (hsteps_trans _ (HB [225; 40; 14; 5] 1588 1 3000
      ((2, 2) :: (1439, 2) :: (1, 1) :: repeat (1, 2) 7428 ++ w)
      1)).
    { apply (hGRIND_even 1498 [225; 40; 14; 5] 1588
             ((1439, 2) :: (1, 1) :: repeat (1, 2) 7428 ++ w)
             1); lia. }
    apply (hsteps_trans _ (HC [1589; 225; 40; 14; 5] 3000 1 2
      ((1437, 2) :: (1, 1) :: repeat (1, 2) 7428 ++ w) 1)).
    { apply (sTUP2_1 [225; 40; 14; 5] 1588 2999 1439
             ((1, 1) :: repeat (1, 2) 7428 ++ w) 1); lia. }
    apply (hsteps_trans _ (HB [1589; 225; 40; 14; 5] 3000 1 4
      ((1437, 2) :: (1, 1) :: repeat (1, 2) 7428 ++ w) 1)).
    { apply (sTDN [1589; 225; 40; 14; 5] 3000
             ((1437, 2) :: (1, 1) :: repeat (1, 2) 7428 ++ w)
             1). }
    apply (sTUP [1589; 225; 40; 14; 5] 3000 4 1437 2
           ((1, 1) :: repeat (1, 2) 7428 ++ w) 1); lia. }
  (* S23: CLEANG_odd at the pair (1435, 2) = (2*716+3, 2) *)
  apply (hsteps_trans _ (HB [1589; 225; 40; 14; 5] 3000 1 1440
    ((1, 2) :: (1, 1) :: repeat (1, 2) 7428 ++ w) 1)).
  { replace (1435, 2) with (2 * 716 + 3, 2) by sec_eq.
    replace 1440 with (2 * 716 + 8) by lia.
    apply (CLEANG_odd 716 [1589; 225; 40; 14; 5] 3000
           ((1, 1) :: repeat (1, 2) 7428 ++ w) 1); lia. }
  (* S24: pop12 1, POP, pop12 7428 -- the TOP2 state *)
  apply (hsteps_trans _ (HB [1589; 225; 40; 14; 5] 3001 1 1442
    ((1, 1) :: repeat (1, 2) 7428 ++ w) 1)).
  { replace ((1, 2) :: (1, 1) :: repeat (1, 2) 7428 ++ w)
      with (repeat (1, 2) 1
            ++ ((1, 1) :: repeat (1, 2) 7428 ++ w))
      by sec_eq.
    apply (pop12 1 [1589; 225; 40; 14; 5] 3000 1440
           ((1, 1) :: repeat (1, 2) 7428 ++ w) 1); lia. }
  apply (hsteps_trans _ (HB [1589; 225; 40; 14; 5] 3002 1 1443
    (repeat (1, 2) 7428 ++ w) 1)).
  { apply (sPOP1 [1589; 225; 40; 14; 5] 3001 1442
           (repeat (1, 2) 7428 ++ w) 1); lia. }
  apply (pop12 7428 [1589; 225; 40; 14; 5] 3002 1443 w 1); lia.
Qed.

(* ----------------------------------------------------------------- *)
(* TOP48_TO_TOP2: TOP -> front (TUP, hGRIND_even 3711, TUP2_1,     *)
(* TDN, TUP -- the first five steps of TOP47_BAND) -> GRIND2 ->     *)
(* DIPGRIND (7426, 2 * (j - 7429)) -> CASCADE48 -> TOP2, uniform    *)
(* in (j, beta) for j >= 7430.  The target pair is written          *)
(* (2 * (j - 7429), 2) so it matches the TOP48_BAND / TAIL2_END3    *)
(* instantiations syntactically.                                    *)
(* ----------------------------------------------------------------- *)

Lemma TOP48_TO_TOP2 : forall j beta, 7430 <= j -> 2 <= beta ->
  hsteps (HB [1279; 745; 151; 77; 35; 20; 0] 4001 1 7427
            ((2 * j, 2) :: (1, 1) :: repeat (1, 2) (beta - 1)) 1)
         (HB [1589; 225; 40; 14; 5] 10430 1 16299
            ((2 * (j - 7429), 2) :: (1, 1)
             :: repeat (1, 2) (beta - 1)) 1).
Proof.
  intros j beta Hj Hb.
  (* lia cannot use Hj directly: 7430 is an of_num_uint atom,     *)
  (* unrelated in lia's eyes to the numerals below.  Derive a     *)
  (* numeral lower bound on j, and normalise the 7429/7430 atoms  *)
  (* onto the single atom 7426 where an identity needs them.      *)
  assert (Hj4 : 4 <= j).
  { apply Nat.le_trans with 7430; [closearith | exact Hj]. }
  assert (Hr : 1 <= j - 7429).
  { change 7429 with (7430 - 1). lia. }
  assert (Heq : 2 * j - 6 = 2 * 7426 + 2 * (j - 7429)).
  { change 7429 with (7426 + 3).
    change 7430 with (7426 + 4) in Hj. lia. }
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
  apply (hsteps_trans _ (HC [4001; 1279; 745; 151; 77; 35; 20; 0]
    0 3 2 (repeat (1, 2) 7426
     ++ ((2 * (j - 7429), 2) :: (1, 1)
         :: repeat (1, 2) (beta - 1))) 1)).
  { rewrite Heq.
    apply (DIPGRIND 7426 (2 * (j - 7429))
           [4001; 1279; 745; 151; 77; 35; 20; 0]
           ((1, 1) :: repeat (1, 2) (beta - 1)) 1);
      [closearith | lia]. }
  apply (CASCADE48 ((2 * (j - 7429), 2) :: (1, 1)
                    :: repeat (1, 2) (beta - 1))).
Qed.

(* ----------------------------------------------------------------- *)
(* The TOP2 closings: r = 2, r = 4, r = 6, and band 2               *)
(* (r = 2 * j2, 4 <= j2 <= 16301, i.e. 8 <= r <= 32602).            *)
(* ----------------------------------------------------------------- *)

Lemma TOP48_2 : forall beta, 2 <= beta ->
  hsteps (HB [1589; 225; 40; 14; 5] 10430 1 16299
            ((2, 2) :: (1, 1) :: repeat (1, 2) (beta - 1)) 1)
         (HB [10431; 1589; 225; 40; 14; 5]
            (16300 + (beta - 1)) 1 (2 * beta + 1) [] 1).
Proof.
  intros beta Hb.
  apply (hsteps_trans _ (HB [10431; 1589; 225; 40; 14; 5]
    16300 1 3 (repeat (1, 2) (beta - 1)) 1)).
  { apply (sTRANS2_1 [1589; 225; 40; 14; 5] 10430 16298 1
           (repeat (1, 2) (beta - 1)) 1); lia. }
  apply (CASCADE_POPFIN [10431; 1589; 225; 40; 14; 5] 16300
         beta); lia.
Qed.

Lemma TOP48_4 : forall beta, 2 <= beta ->
  hsteps (HB [1589; 225; 40; 14; 5] 10430 1 16299
            ((4, 2) :: (1, 1) :: repeat (1, 2) (beta - 1)) 1)
         (HB [16299; 10430; 1589; 225; 40; 14; 5] (beta + 2) 1
            (2 * beta + 1) [] 1).
Proof.
  intros beta Hb.
  apply (hsteps_trans _ (HC [1589; 225; 40; 14; 5] 10430
    16298 2 ((2, 2) :: (1, 1) :: repeat (1, 2) (beta - 1)) 1)).
  { apply (sTUP [1589; 225; 40; 14; 5] 10430 16299 4 2
           ((1, 1) :: repeat (1, 2) (beta - 1)) 1); closearith. }
  apply (hsteps_trans _ (HB [1589; 225; 40; 14; 5] 10429
    1 16298 ((2, 2) :: (2, 2) :: (1, 1)
            :: repeat (1, 2) (beta - 1)) 1)).
  { apply (hGRIND_even 8147 [1589; 225; 40; 14; 5] 10429
           ((2, 2) :: (1, 1) :: repeat (1, 2) (beta - 1)) 1);
      closearith. }
  apply (hsteps_trans _ (HB [16299; 10430; 1589; 225; 40; 14; 5]
    3 1 3 (repeat (1, 2) (beta - 1)) 1)).
  { apply (hsteps_step _ (HB [16299; 10430; 1589; 225; 40; 14; 5]
      3 1 3 (repeat (1, 2) (beta - 1)) 1));
      [apply hTRANS2_2; lia | apply hsteps_refl]. }
  replace (beta + 2) with (3 + (beta - 1)) by lia.
  apply (CASCADE_POPFIN [16299; 10430; 1589; 225; 40; 14; 5] 3
         beta); lia.
Qed.

Lemma TOP48_6 : forall beta, 2 <= beta ->
  hsteps (HB [1589; 225; 40; 14; 5] 10430 1 16299
            ((6, 2) :: (1, 1) :: repeat (1, 2) (beta - 1)) 1)
         (HB [16299; 10430; 1589; 225; 40; 14; 5] (beta + 4) 1
            (2 * beta + 1) [] 1).
Proof.
  intros beta Hb.
  apply (hsteps_trans _ (HC [1589; 225; 40; 14; 5] 10430
    16298 2 ((4, 2) :: (1, 1) :: repeat (1, 2) (beta - 1)) 1)).
  { apply (sTUP [1589; 225; 40; 14; 5] 10430 16299 6 2
           ((1, 1) :: repeat (1, 2) (beta - 1)) 1); closearith. }
  apply (hsteps_trans _ (HB [1589; 225; 40; 14; 5] 10429
    1 16298 ((2, 2) :: (4, 2) :: (1, 1)
            :: repeat (1, 2) (beta - 1)) 1)).
  { apply (hGRIND_even 8147 [1589; 225; 40; 14; 5] 10429
           ((4, 2) :: (1, 1) :: repeat (1, 2) (beta - 1)) 1);
      closearith. }
  apply (hsteps_trans _ (HC [10430; 1589; 225; 40; 14; 5]
    16298 1 2 ((2, 2) :: (1, 1) :: repeat (1, 2) (beta - 1)) 1)).
  { replace ((2, 2) :: (1, 1) :: repeat (1, 2) (beta - 1))
      with ((4 - 2, 2) :: (1, 1) :: repeat (1, 2) (beta - 1))
      by sec_eq.
    apply (sTUP2_1 [1589; 225; 40; 14; 5] 10429 16297 4
           ((1, 1) :: repeat (1, 2) (beta - 1)) 1); lia. }
  apply (hsteps_trans _ (HB [10430; 1589; 225; 40; 14; 5]
    16298 1 4 ((2, 2) :: (1, 1) :: repeat (1, 2) (beta - 1)) 1)).
  { apply (sTDN [10430; 1589; 225; 40; 14; 5] 16298
           ((2, 2) :: (1, 1) :: repeat (1, 2) (beta - 1)) 1). }
  apply (hsteps_trans _ (HB [16299; 10430; 1589; 225; 40; 14; 5]
    5 1 3 (repeat (1, 2) (beta - 1)) 1)).
  { apply (sTRANS2_1 [10430; 1589; 225; 40; 14; 5] 16298 3 1
           (repeat (1, 2) (beta - 1)) 1); lia. }
  replace (beta + 4) with (5 + (beta - 1)) by lia.
  apply (CASCADE_POPFIN [16299; 10430; 1589; 225; 40; 14; 5] 5
         beta); lia.
Qed.

Lemma TOP48_BAND : forall j beta, 4 <= j -> j <= 16301 -> 2 <= beta ->
  hsteps (HB [1589; 225; 40; 14; 5] 10430 1 16299
            ((2 * j, 2) :: (1, 1) :: repeat (1, 2) (beta - 1)) 1)
         (HB [16299; 10430; 1589; 225; 40; 14; 5]
            (2 * j + beta - 2) 1 (2 * beta + 1) [] 1).
Proof.
  intros j beta Hj1 Hj2 Hb.
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
  apply (hsteps_trans _ (HB [10430; 1589; 225; 40; 14; 5]
    16298 1 (2 * j - 2)
    ((2, 2) :: (1, 1) :: repeat (1, 2) (beta - 1)) 1)).
  { replace (2 * j - 6) with (2 * (j - 4) + 2) by lia.
    replace (2 * j - 2) with (2 * (j - 4) + 6) by lia.
    apply (CLEANG_even (j - 4) [10430; 1589; 225; 40; 14; 5]
           16298 ((1, 1) :: repeat (1, 2) (beta - 1)) 1).
    (* the floor (j - 4) + 1 <= 16298: route via j <= 16301 *)
    apply Nat.le_trans with (j - 3).
    - lia.
    - change 16298 with (16301 - 3).
      apply Nat.sub_le_mono_r. exact Hj2. }
  apply (hsteps_trans _ (HB [16299; 10430; 1589; 225; 40; 14; 5]
    (2 * j - 1) 1 3 (repeat (1, 2) (beta - 1)) 1)).
  { replace (2 * j - 2) with (S (2 * j - 3)) by lia.
    replace (2 * j - 1) with (S (S (2 * j - 3))) by lia.
    apply (sTRANS2_1 [10430; 1589; 225; 40; 14; 5] 16298
           (2 * j - 3) 1 (repeat (1, 2) (beta - 1)) 1); lia. }
  replace (2 * j + beta - 2) with (2 * j - 1 + (beta - 1)) by lia.
  apply (CASCADE_POPFIN [16299; 10430; 1589; 225; 40; 14; 5]
         (2 * j - 1) beta); lia.
Qed.

(* ----------------------------------------------------------------- *)
(* TAIL2_END3: the strictly smaller residual core -- the totality   *)
(* of the TOP2 state for r = 2 * j, j >= 16302 (r >= 32604),        *)
(* where the GRIND3 pair (r - 6, 2) at counter 16298 takes the      *)
(* DIPDESC boundary a third time.  A Definition (lemma              *)
(* parameter), never an axiom.                                      *)
(* ----------------------------------------------------------------- *)

Definition TAIL2_END3 : Prop :=
  forall j beta, 16302 <= j -> 2 <= beta ->
  exists pb A, beta <= A /\
    hsteps (HB [1589; 225; 40; 14; 5] 10430 1 16299
              ((2 * j, 2) :: (1, 1) :: repeat (1, 2) (beta - 1)) 1)
           (HB pb A 1 (2 * beta + 1) [] 1).

(* ----------------------------------------------------------------- *)
(* TAIL2_END2_of48: TAIL2_END2, modulo TAIL2_END3.  The j-range     *)
(* splits at r = 2 * (j - 7429): the three small cases and band 2   *)
(* are proved above; j - 7429 >= 16302 is the core.                 *)
(* ----------------------------------------------------------------- *)

Lemma TAIL2_END2_of48 : TAIL2_END3 -> TAIL2_END2.
Proof.
  intros H3 j beta Hj Hb.
  pose proof (TOP48_TO_TOP2 j beta Hj Hb) as Htop.
  destruct (le_lt_dec 16302 (j - 7429)) as [Hbig | Hsmall].
  - (* j2 = j - 7429 >= 16302: the core *)
    destruct (H3 (j - 7429) beta Hbig Hb)
      as [pb [A [Ha Hsteps]]].
    exists pb, A. split; [exact Ha |].
    exact (hsteps_trans _ _ _ Htop Hsteps).
  - destruct (le_lt_dec 4 (j - 7429)) as [Hband | Htiny].
    + (* band 2: j2 = j - 7429, 4 <= j2 <= 16301 *)
      exists [16299; 10430; 1589; 225; 40; 14; 5],
        (2 * (j - 7429) + beta - 2).
      split; [lia |].
      assert (Hj2 : j - 7429 <= 16301).
      { change 16302 with (S 16301) in Hsmall.
        apply (proj1 (Nat.lt_succ_r _ _) Hsmall). }
      exact (hsteps_trans _ _ _ Htop
               (TOP48_BAND (j - 7429) beta Hband Hj2 Hb)).
    + (* tiny: j2 = j - 7429 <= 3; j2 >= 1 since 7430 <= j *)
      destruct (Nat.eq_dec (j - 7429) 1) as [He | Hne].
      * (* r = 2 *)
        rewrite He in Htop.
        exists [10431; 1589; 225; 40; 14; 5],
          (16300 + (beta - 1)).
        split; [change 16300 with (S 16299); lia |].
        exact (hsteps_trans _ _ _ Htop (TOP48_2 beta Hb)).
      * destruct (Nat.eq_dec (j - 7429) 2) as [He | Hne'].
        -- (* r = 4 *)
           rewrite He in Htop.
           exists [16299; 10430; 1589; 225; 40; 14; 5],
             (beta + 2).
           split; [lia |].
           exact (hsteps_trans _ _ _ Htop (TOP48_4 beta Hb)).
        -- destruct (Nat.eq_dec (j - 7429) 3) as [He | Hne''].
           ++ (* r = 6 *)
              rewrite He in Htop.
              exists [16299; 10430; 1589; 225; 40; 14; 5],
                (beta + 4).
              split; [lia |].
              exact (hsteps_trans _ _ _ Htop (TOP48_6 beta Hb)).
           ++ (* j2 = 0, contradicting 7430 <= j *)
              exfalso.
              assert (H0 : j - 7429 = 0) by lia.
              change 7430 with (S 7429) in Hj.
              lia.
Qed.

(* ----------------------------------------------------------------- *)
(* ESC_ERA_LAW_48: the phase-8 ESC era law at every even            *)
(* R >= 1278, modulo TAIL2_END3 alone.                              *)
(* ----------------------------------------------------------------- *)

Lemma ESC_ERA_LAW_48 : TAIL2_END3 ->
  forall M beta, 616 <= M -> 2 <= beta ->
  exists n c pb a,
    run n (esc_src (2 * M + 52) (beta - 2)) = Some c
    /\ cfg_sim c (rcsec (false :: repeat true (S a) ++ enc pb)
                        (2 * beta + 2) [(1, 2)])
    /\ beta <= a.
Proof.
  intros H M beta HM Hb.
  apply (ESC_ERA_LAW_47 (TAIL2_END2_of48 H) M beta HM Hb).
Qed.

(* ----------------------------------------------------------------- *)
(* Assumption audit                                                  *)
(* ----------------------------------------------------------------- *)

Print Assumptions CASCADE48.
Print Assumptions TOP48_TO_TOP2.
Print Assumptions TOP48_2.
Print Assumptions TOP48_4.
Print Assumptions TOP48_6.
Print Assumptions TOP48_BAND.
Print Assumptions TAIL2_END2_of48.
Print Assumptions ESC_ERA_LAW_48.
