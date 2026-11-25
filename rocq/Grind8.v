(* ================================================================= *)
(*  Grind8.v -- Phase 40: the phase-7 merged unwind, covering       *)
(*  every even R <= 1276.                                            *)
(*                                                                   *)
(*  The Phase 38 fence: at R = 2m + 46 with m >= 279, phase 6's      *)
(*  finish (ESC_TO_REGEN_BIG6 in Grind7.v) breaks at the new frame   *)
(*  ([110; 19; 0], 164): the rounds (count m - 115) and the final    *)
(*  grind (t = m - 115, floor t + 1 <= 164) both bind.  Taking the   *)
(*  maximal 164 clean rounds leaves the final grind at exactly      *)
(*  t = 164 = a2 over the passenger residue ((2m - 556, 2) :: Pe):   *)
(*  a boundary grind.  Its descent is DIPDESC 164 (Grind7.v,         *)
(*  pb-general, no floor hypothesis), and the dip at                 *)
(*  [110; 19; 0] fires the existing hPX2A (Dev.v), landing at        *)
(*  HC [0] 18 108 2 with the dispatch's three extra pairs over       *)
(*  the (1, 2)^164 spine.  No new deviation step list is needed.     *)
(*                                                                   *)
(*  The continuation is the ([0], 18) grind at g0 = 108 over an      *)
(*  arbitrary carried rest (GRIND108_MID):                           *)
(*  PUSH/TDN/TUP + LOOPN 17 (floor met exactly) + DIPDESC 17         *)
(*  to its own dip, hPX2B0, a POP run of 18, TUP; then the           *)
(*  boundary even grind at pb = [] (g0 = 40 = 2*18 + 4, the          *)
(*  hGRIND_even shape one past its floor): PUSH/TDN/TUP +            *)
(*  LOOPN 17 (floor-exact, (36, 2) ground to (2, 2)) +              *)
(*  PUSH/TDN/TUP + LOOPN 16 (floor-exact, (33, 2) to (1, 2)) +       *)
(*  DIPDESC 16 to the pb = [] dip, hPUSHX, a POP run of 17,          *)
(*  hTUP2_1 onto frame ([19], 41), TDN, TUP; then LOOPN 31 +         *)
(*  PUSH/TDN/TUP + LOOPN 30 + the clean hGRIND 30 + POP +            *)
(*  hTRANS2_1 + a POP chain over the spine, landing at               *)
(*  HB [42; 19] (71 + n) 1 (7 + 2n) Rest for spine length n.         *)
(*                                                                   *)
(*  Finishes: m = 279 (R = 604) is TAIL at that landing;             *)
(*  m = 280 (R = 606) runs TUP + hGRIND_even 165 and closes          *)
(*  with the TRANS2_2 tail (TAIL2); m = 281 (R = 608) runs the       *)
(*  transitional round onto frame ([235; 42; 19], 334) and TAIL;    *)
(*  282 <= m <= 615 (R <= 1276) continues with rounds at the         *)
(*  new frame, a final clean grind and TAIL.  The next fence is      *)
(*  m = 616 (R = 1278): the rounds and the final grind at frame      *)
(*  334 both bind; the final grind at t = a2 would again be a        *)
(*  DIPDESC descent whose dip at [235; 42; 19] fires hPX2A           *)
(*  into a phase-8 continuation.                                     *)
(*                                                                   *)
(*  All forms pre-verified in rocq/hsim40.py: the hPX2A dispatch     *)
(*  at the phase-7 dip shape, DIPDESC at [110; 19; 0], the           *)
(*  GRIND108 stages A and B as primitive word walks at the real      *)
(*  parameters (1,048,574 and 1,048,575 rules), stage C at the       *)
(*  real frame ([19], 41) with a shrunk passenger, the whole         *)
(*  parse at two shrunk analogues (a2, g0) in {(6, 36), (8, 48)}     *)
(*  with word/machine boundary agreement, and shrunk analogues       *)
(*  of all four finishes.                                            *)
(* ================================================================= *)

Require Import List Bool Arith Lia ZArith.
Import ListNotations.
Require Import TM Sections Mirror TokenPass Recoord Era Esc Dev
               Grind Grind2 Grind3 Grind4 Grind5 Grind6 Grind7.

Ltac sec_eq := repeat (first [ solve [reflexivity] | solve [lia]
                             | f_equal ]).

(* ----------------------------------------------------------------- *)
(* Part 1: GRIND108_MID -- the continuation grind at ([0], 18),      *)
(* g0 = 108, over an arbitrary carried rest.  Segment boundaries     *)
(* are the hsim40.py walk: PUSH/TDN/TUP, LOOPN 17, DIPDESC 17,       *)
(* hPX2B0, POP x18, TUP (stage A); PUSH/TDN/TUP, LOOPN 17,           *)
(* PUSH/TDN/TUP, LOOPN 16, DIPDESC 16, hPUSHX, POP x17, hTUP2_1,     *)
(* TDN, TUP (stage B); LOOPN 31, PUSH/TDN/TUP, LOOPN 30,             *)
(* hGRIND 30, POP, hTRANS2_1 and the spine POP chain (stage C).      *)
(* ----------------------------------------------------------------- *)

Lemma GRIND108_MID : forall n Rest,
  hsteps (HC [0] 18 108 2
            ((1, 1) :: (1, 2) :: (1, 2)
             :: repeat (1, 2) n ++ Rest) 1)
         (HB [42; 19] (71 + n) 1 (7 + 2*n) Rest 1).
Proof.
  intros n Rest.
  (* PUSH *)
  apply (hsteps_trans _ (HC [0] 17 1 2 ((106, 2)
      :: (1, 1) :: (1, 2) :: (1, 2)
         :: repeat (1, 2) n ++ Rest) 1)).
  { apply (hsteps_step _ (HC [0] 17 1 2 ((106, 2)
        :: (1, 1) :: (1, 2) :: (1, 2)
           :: repeat (1, 2) n ++ Rest) 1)).
    { replace (HC [0] 18 108 2
                ((1, 1) :: (1, 2) :: (1, 2)
                 :: repeat (1, 2) n ++ Rest) 1)
        with (HC [0] (S 17) (S (S (S 105))) 2
                ((1, 1) :: (1, 2) :: (1, 2)
                 :: repeat (1, 2) n ++ Rest) 1) by sec_eq.
      replace (HC [0] 17 1 2 ((106, 2)
                :: (1, 1) :: (1, 2) :: (1, 2)
                   :: repeat (1, 2) n ++ Rest) 1)
        with (HC [0] 17 1 2 ((S 105, 2)
                :: (1, 1) :: (1, 2) :: (1, 2)
                   :: repeat (1, 2) n ++ Rest) 1) by sec_eq.
      apply hPUSH. }
    apply hsteps_refl. }
  (* TDN *)
  apply (hsteps_trans _ (HB [0] 17 1 4 ((106, 2)
      :: (1, 1) :: (1, 2) :: (1, 2)
         :: repeat (1, 2) n ++ Rest) 1)).
  { apply (hsteps_step _ (HB [0] 17 1 4 ((106, 2)
        :: (1, 1) :: (1, 2) :: (1, 2)
           :: repeat (1, 2) n ++ Rest) 1)).
    { apply hTDN. }
    apply hsteps_refl. }
  (* TUP *)
  apply (hsteps_trans _ (HC [0] 17 3 2 ((104, 2)
      :: (1, 1) :: (1, 2) :: (1, 2)
         :: repeat (1, 2) n ++ Rest) 1)).
  { apply (hsteps_step _ (HC [0] 17 3 2 ((104, 2)
        :: (1, 1) :: (1, 2) :: (1, 2)
           :: repeat (1, 2) n ++ Rest) 1)).
    { replace (HB [0] 17 1 4 ((106, 2)
                :: (1, 1) :: (1, 2) :: (1, 2)
                   :: repeat (1, 2) n ++ Rest) 1)
        with (HB [0] 17 1 (S (S 2)) ((S (S (S 103)), 2)
                :: (1, 1) :: (1, 2) :: (1, 2)
                   :: repeat (1, 2) n ++ Rest) 1) by sec_eq.
      replace (HC [0] 17 3 2 ((104, 2)
                :: (1, 1) :: (1, 2) :: (1, 2)
                   :: repeat (1, 2) n ++ Rest) 1)
        with (HC [0] 17 (S 2) 2 ((S 103, 2)
                :: (1, 1) :: (1, 2) :: (1, 2)
                   :: repeat (1, 2) n ++ Rest) 1) by sec_eq.
      apply hTUP. }
    apply hsteps_refl. }
  (* LOOPN 17 *)
  apply (hsteps_trans _ (HC [0] 17 37 2 ((70, 2)
      :: (1, 1) :: (1, 2) :: (1, 2)
         :: repeat (1, 2) n ++ Rest) 1)).
  { replace (HC [0] 17 3 2 ((104, 2)
              :: (1, 1) :: (1, 2) :: (1, 2)
                 :: repeat (1, 2) n ++ Rest) 1)
      with (HC [0] 17 (2*0 + 3) 2 ((104, 2)
              :: (1, 1) :: (1, 2) :: (1, 2)
                 :: repeat (1, 2) n ++ Rest) 1) by sec_eq.
    replace (HC [0] 17 37 2 ((70, 2)
              :: (1, 1) :: (1, 2) :: (1, 2)
                 :: repeat (1, 2) n ++ Rest) 1)
      with (HC [0] 17 (2*(0 + 17) + 3) 2 ((104 - 2*17, 2)
              :: (1, 1) :: (1, 2) :: (1, 2)
                 :: repeat (1, 2) n ++ Rest) 1) by sec_eq.
    apply (LOOPN 17 0 [0] 17 104
             ((1, 1) :: (1, 2) :: (1, 2)
              :: repeat (1, 2) n ++ Rest) 1); lia. }
  (* DIPDESC 17 *)
  apply (hsteps_trans _ (HC [0] 0 3 2
      (repeat (1, 2) 17 ++ ((70, 2)
        :: (1, 1) :: (1, 2) :: (1, 2)
           :: repeat (1, 2) n ++ Rest)) 1)).
  { apply (DIPDESC 17 [0] ((70, 2)
             :: (1, 1) :: (1, 2) :: (1, 2)
                :: repeat (1, 2) n ++ Rest) 1). }
  (* PX2B0 *)
  apply (hsteps_trans _ (HB [] 0 1 5
      ((1, 2) :: repeat (1, 2) 17 ++ ((70, 2)
        :: (1, 1) :: (1, 2) :: (1, 2)
           :: repeat (1, 2) n ++ Rest)) 1)).
  { apply (hsteps_step _ (HB [] 0 1 5
        ((1, 2) :: repeat (1, 2) 17 ++ ((70, 2)
          :: (1, 1) :: (1, 2) :: (1, 2)
             :: repeat (1, 2) n ++ Rest)) 1)).
    { apply hPX2B0. }
    apply hsteps_refl. }
  (* POP x18 *)
  apply (hsteps_trans _ (HB [] 18 1 41 ((70, 2)
      :: (1, 1) :: (1, 2) :: (1, 2)
         :: repeat (1, 2) n ++ Rest) 1)).
  { replace (HB [] 0 1 5
              ((1, 2) :: repeat (1, 2) 17 ++ ((70, 2)
               :: (1, 1) :: (1, 2) :: (1, 2)
                  :: repeat (1, 2) n ++ Rest)) 1)
      with (HB [] 0 1 5
              (repeat (1, 2) 18 ++ ((70, 2)
               :: (1, 1) :: (1, 2) :: (1, 2)
                  :: repeat (1, 2) n ++ Rest)) 1) by sec_eq.
    replace (HB [] 18 1 41 ((70, 2)
              :: (1, 1) :: (1, 2) :: (1, 2)
                 :: repeat (1, 2) n ++ Rest) 1)
      with (HB [] (0 + 18) 1 (5 + 2*18) ((70, 2)
              :: (1, 1) :: (1, 2) :: (1, 2)
                 :: repeat (1, 2) n ++ Rest) 1) by sec_eq.
    apply pop_chain_h_app; lia. }
  (* TUP *)
  apply (hsteps_trans _ (HC [] 18 40 2 ((68, 2)
      :: (1, 1) :: (1, 2) :: (1, 2)
         :: repeat (1, 2) n ++ Rest) 1)).
  { apply (hsteps_step _ (HC [] 18 40 2 ((68, 2)
        :: (1, 1) :: (1, 2) :: (1, 2)
           :: repeat (1, 2) n ++ Rest) 1)).
    { replace (HB [] 18 1 41 ((70, 2)
                :: (1, 1) :: (1, 2) :: (1, 2)
                   :: repeat (1, 2) n ++ Rest) 1)
        with (HB [] 18 1 (S (S 39)) ((S (S (S 67)), 2)
                :: (1, 1) :: (1, 2) :: (1, 2)
                   :: repeat (1, 2) n ++ Rest) 1) by sec_eq.
      replace (HC [] 18 40 2 ((68, 2)
                :: (1, 1) :: (1, 2) :: (1, 2)
                   :: repeat (1, 2) n ++ Rest) 1)
        with (HC [] 18 (S 39) 2 ((S 67, 2)
                :: (1, 1) :: (1, 2) :: (1, 2)
                   :: repeat (1, 2) n ++ Rest) 1) by sec_eq.
      apply hTUP. }
    apply hsteps_refl. }
  (* stage B: PUSH *)
  apply (hsteps_trans _ (HC [] 17 1 2 ((38, 2) :: (68, 2)
      :: (1, 1) :: (1, 2) :: (1, 2)
         :: repeat (1, 2) n ++ Rest) 1)).
  { apply (hsteps_step _ (HC [] 17 1 2 ((38, 2) :: (68, 2)
        :: (1, 1) :: (1, 2) :: (1, 2)
           :: repeat (1, 2) n ++ Rest) 1)).
    { replace (HC [] 18 40 2 ((68, 2)
                :: (1, 1) :: (1, 2) :: (1, 2)
                   :: repeat (1, 2) n ++ Rest) 1)
        with (HC [] (S 17) (S (S (S 37))) 2 ((68, 2)
                :: (1, 1) :: (1, 2) :: (1, 2)
                   :: repeat (1, 2) n ++ Rest) 1) by sec_eq.
      replace (HC [] 17 1 2 ((38, 2) :: (68, 2)
                :: (1, 1) :: (1, 2) :: (1, 2)
                   :: repeat (1, 2) n ++ Rest) 1)
        with (HC [] 17 1 2 ((S 37, 2) :: (68, 2)
                :: (1, 1) :: (1, 2) :: (1, 2)
                   :: repeat (1, 2) n ++ Rest) 1) by sec_eq.
      apply hPUSH. }
    apply hsteps_refl. }
  (* TDN *)
  apply (hsteps_trans _ (HB [] 17 1 4 ((38, 2) :: (68, 2)
      :: (1, 1) :: (1, 2) :: (1, 2)
         :: repeat (1, 2) n ++ Rest) 1)).
  { apply (hsteps_step _ (HB [] 17 1 4 ((38, 2) :: (68, 2)
        :: (1, 1) :: (1, 2) :: (1, 2)
           :: repeat (1, 2) n ++ Rest) 1)).
    { apply hTDN. }
    apply hsteps_refl. }
  (* TUP *)
  apply (hsteps_trans _ (HC [] 17 3 2 ((36, 2) :: (68, 2)
      :: (1, 1) :: (1, 2) :: (1, 2)
         :: repeat (1, 2) n ++ Rest) 1)).
  { apply (hsteps_step _ (HC [] 17 3 2 ((36, 2) :: (68, 2)
        :: (1, 1) :: (1, 2) :: (1, 2)
           :: repeat (1, 2) n ++ Rest) 1)).
    { replace (HB [] 17 1 4 ((38, 2) :: (68, 2)
                :: (1, 1) :: (1, 2) :: (1, 2)
                   :: repeat (1, 2) n ++ Rest) 1)
        with (HB [] 17 1 (S (S 2)) ((S (S (S 35)), 2) :: (68, 2)
                :: (1, 1) :: (1, 2) :: (1, 2)
                   :: repeat (1, 2) n ++ Rest) 1) by sec_eq.
      replace (HC [] 17 3 2 ((36, 2) :: (68, 2)
                :: (1, 1) :: (1, 2) :: (1, 2)
                   :: repeat (1, 2) n ++ Rest) 1)
        with (HC [] 17 (S 2) 2 ((S 35, 2) :: (68, 2)
                :: (1, 1) :: (1, 2) :: (1, 2)
                   :: repeat (1, 2) n ++ Rest) 1) by sec_eq.
      apply hTUP. }
    apply hsteps_refl. }
  (* LOOPN 17 *)
  apply (hsteps_trans _ (HC [] 17 37 2 ((2, 2) :: (68, 2)
      :: (1, 1) :: (1, 2) :: (1, 2)
         :: repeat (1, 2) n ++ Rest) 1)).
  { replace (HC [] 17 3 2 ((36, 2) :: (68, 2)
              :: (1, 1) :: (1, 2) :: (1, 2)
                 :: repeat (1, 2) n ++ Rest) 1)
      with (HC [] 17 (2*0 + 3) 2 ((36, 2) :: (68, 2)
              :: (1, 1) :: (1, 2) :: (1, 2)
                 :: repeat (1, 2) n ++ Rest) 1) by sec_eq.
    replace (HC [] 17 37 2 ((2, 2) :: (68, 2)
              :: (1, 1) :: (1, 2) :: (1, 2)
                 :: repeat (1, 2) n ++ Rest) 1)
      with (HC [] 17 (2*(0 + 17) + 3) 2 ((36 - 2*17, 2) :: (68, 2)
              :: (1, 1) :: (1, 2) :: (1, 2)
                 :: repeat (1, 2) n ++ Rest) 1) by sec_eq.
    apply (LOOPN 17 0 [] 17 36
             ((68, 2) :: (1, 1) :: (1, 2) :: (1, 2)
              :: repeat (1, 2) n ++ Rest) 1); lia. }
  (* PUSH *)
  apply (hsteps_trans _ (HC [] 16 1 2 ((35, 2) :: (2, 2) :: (68, 2)
      :: (1, 1) :: (1, 2) :: (1, 2)
         :: repeat (1, 2) n ++ Rest) 1)).
  { apply (hsteps_step _ (HC [] 16 1 2 ((35, 2) :: (2, 2) :: (68, 2)
        :: (1, 1) :: (1, 2) :: (1, 2)
           :: repeat (1, 2) n ++ Rest) 1)).
    { replace (HC [] 17 37 2 ((2, 2) :: (68, 2)
                :: (1, 1) :: (1, 2) :: (1, 2)
                   :: repeat (1, 2) n ++ Rest) 1)
        with (HC [] (S 16) (S (S (S 34))) 2 ((2, 2) :: (68, 2)
                :: (1, 1) :: (1, 2) :: (1, 2)
                   :: repeat (1, 2) n ++ Rest) 1) by sec_eq.
      replace (HC [] 16 1 2 ((35, 2) :: (2, 2) :: (68, 2)
                :: (1, 1) :: (1, 2) :: (1, 2)
                   :: repeat (1, 2) n ++ Rest) 1)
        with (HC [] 16 1 2 ((S 34, 2) :: (2, 2) :: (68, 2)
                :: (1, 1) :: (1, 2) :: (1, 2)
                   :: repeat (1, 2) n ++ Rest) 1) by sec_eq.
      apply hPUSH. }
    apply hsteps_refl. }
  (* TDN *)
  apply (hsteps_trans _ (HB [] 16 1 4 ((35, 2) :: (2, 2) :: (68, 2)
      :: (1, 1) :: (1, 2) :: (1, 2)
         :: repeat (1, 2) n ++ Rest) 1)).
  { apply (hsteps_step _ (HB [] 16 1 4 ((35, 2) :: (2, 2) :: (68, 2)
        :: (1, 1) :: (1, 2) :: (1, 2)
           :: repeat (1, 2) n ++ Rest) 1)).
    { apply hTDN. }
    apply hsteps_refl. }
  (* TUP *)
  apply (hsteps_trans _ (HC [] 16 3 2 ((33, 2) :: (2, 2) :: (68, 2)
      :: (1, 1) :: (1, 2) :: (1, 2)
         :: repeat (1, 2) n ++ Rest) 1)).
  { apply (hsteps_step _ (HC [] 16 3 2 ((33, 2) :: (2, 2) :: (68, 2)
        :: (1, 1) :: (1, 2) :: (1, 2)
           :: repeat (1, 2) n ++ Rest) 1)).
    { replace (HB [] 16 1 4 ((35, 2) :: (2, 2) :: (68, 2)
                :: (1, 1) :: (1, 2) :: (1, 2)
                   :: repeat (1, 2) n ++ Rest) 1)
        with (HB [] 16 1 (S (S 2)) ((S (S (S 32)), 2) :: (2, 2)
                :: (68, 2) :: (1, 1) :: (1, 2) :: (1, 2)
                   :: repeat (1, 2) n ++ Rest) 1) by sec_eq.
      replace (HC [] 16 3 2 ((33, 2) :: (2, 2) :: (68, 2)
                :: (1, 1) :: (1, 2) :: (1, 2)
                   :: repeat (1, 2) n ++ Rest) 1)
        with (HC [] 16 (S 2) 2 ((S 32, 2) :: (2, 2) :: (68, 2)
                :: (1, 1) :: (1, 2) :: (1, 2)
                   :: repeat (1, 2) n ++ Rest) 1) by sec_eq.
      apply hTUP. }
    apply hsteps_refl. }
  (* LOOPN 16 *)
  apply (hsteps_trans _ (HC [] 16 35 2 ((1, 2) :: (2, 2) :: (68, 2)
      :: (1, 1) :: (1, 2) :: (1, 2)
         :: repeat (1, 2) n ++ Rest) 1)).
  { replace (HC [] 16 3 2 ((33, 2) :: (2, 2) :: (68, 2)
              :: (1, 1) :: (1, 2) :: (1, 2)
                 :: repeat (1, 2) n ++ Rest) 1)
      with (HC [] 16 (2*0 + 3) 2 ((33, 2) :: (2, 2) :: (68, 2)
              :: (1, 1) :: (1, 2) :: (1, 2)
                 :: repeat (1, 2) n ++ Rest) 1) by sec_eq.
    replace (HC [] 16 35 2 ((1, 2) :: (2, 2) :: (68, 2)
              :: (1, 1) :: (1, 2) :: (1, 2)
                 :: repeat (1, 2) n ++ Rest) 1)
      with (HC [] 16 (2*(0 + 16) + 3) 2 ((33 - 2*16, 2) :: (2, 2)
              :: (68, 2) :: (1, 1) :: (1, 2) :: (1, 2)
                 :: repeat (1, 2) n ++ Rest) 1) by sec_eq.
    apply (LOOPN 16 0 [] 16 33
             ((2, 2) :: (68, 2) :: (1, 1) :: (1, 2) :: (1, 2)
              :: repeat (1, 2) n ++ Rest) 1); lia. }
  (* DIPDESC 16 *)
  apply (hsteps_trans _ (HC [] 0 3 2
      (repeat (1, 2) 16 ++ ((1, 2) :: (2, 2) :: (68, 2)
        :: (1, 1) :: (1, 2) :: (1, 2)
           :: repeat (1, 2) n ++ Rest)) 1)).
  { apply (DIPDESC 16 [] ((1, 2) :: (2, 2) :: (68, 2)
             :: (1, 1) :: (1, 2) :: (1, 2)
                :: repeat (1, 2) n ++ Rest) 1). }
  (* PUSHX *)
  apply (hsteps_trans _ (HB [] 1 1 7
      (repeat (1, 2) 16 ++ ((1, 2) :: (2, 2) :: (68, 2)
        :: (1, 1) :: (1, 2) :: (1, 2)
           :: repeat (1, 2) n ++ Rest)) 1)).
  { apply (hsteps_step _ (HB [] 1 1 7
        (repeat (1, 2) 16 ++ ((1, 2) :: (2, 2) :: (68, 2)
          :: (1, 1) :: (1, 2) :: (1, 2)
             :: repeat (1, 2) n ++ Rest)) 1)).
    { apply hPUSHX. }
    apply hsteps_refl. }
  (* POP x17 *)
  apply (hsteps_trans _ (HB [] 18 1 41 ((2, 2) :: (68, 2)
      :: (1, 1) :: (1, 2) :: (1, 2)
         :: repeat (1, 2) n ++ Rest) 1)).
  { replace (HB [] 1 1 7
              (repeat (1, 2) 16 ++ ((1, 2) :: (2, 2) :: (68, 2)
               :: (1, 1) :: (1, 2) :: (1, 2)
                  :: repeat (1, 2) n ++ Rest)) 1)
      with (HB [] 1 1 7
              (repeat (1, 2) 17 ++ ((2, 2) :: (68, 2)
               :: (1, 1) :: (1, 2) :: (1, 2)
                  :: repeat (1, 2) n ++ Rest)) 1) by sec_eq.
    replace (HB [] 18 1 41 ((2, 2) :: (68, 2)
              :: (1, 1) :: (1, 2) :: (1, 2)
                 :: repeat (1, 2) n ++ Rest) 1)
      with (HB [] (1 + 17) 1 (7 + 2*17) ((2, 2) :: (68, 2)
              :: (1, 1) :: (1, 2) :: (1, 2)
                 :: repeat (1, 2) n ++ Rest) 1) by sec_eq.
    apply pop_chain_h_app; lia. }
  (* TUP2_1 *)
  apply (hsteps_trans _ (HC [19] 41 1 2 ((66, 2)
      :: (1, 1) :: (1, 2) :: (1, 2)
         :: repeat (1, 2) n ++ Rest) 1)).
  { apply (hsteps_step _ (HC [19] 41 1 2 ((66, 2)
        :: (1, 1) :: (1, 2) :: (1, 2)
           :: repeat (1, 2) n ++ Rest) 1)).
    { replace (HB [] 18 1 41 ((2, 2) :: (68, 2)
                :: (1, 1) :: (1, 2) :: (1, 2)
                   :: repeat (1, 2) n ++ Rest) 1)
        with (HB [] 18 1 (S 40)
                ((2, S (S 0)) :: (S (S (S 65)), 2)
                 :: (1, 1) :: (1, 2) :: (1, 2)
                    :: repeat (1, 2) n ++ Rest) 1) by sec_eq.
      replace (HC [19] 41 1 2 ((66, 2)
                :: (1, 1) :: (1, 2) :: (1, 2)
                   :: repeat (1, 2) n ++ Rest) 1)
        with (HC (S 18 :: []) (S 40) (S 0) 2 ((S 65, 2)
                :: (1, 1) :: (1, 2) :: (1, 2)
                   :: repeat (1, 2) n ++ Rest) 1) by sec_eq.
      apply hTUP2_1. }
    apply hsteps_refl. }
  (* TDN *)
  apply (hsteps_trans _ (HB [19] 41 1 4 ((66, 2)
      :: (1, 1) :: (1, 2) :: (1, 2)
         :: repeat (1, 2) n ++ Rest) 1)).
  { apply (hsteps_step _ (HB [19] 41 1 4 ((66, 2)
        :: (1, 1) :: (1, 2) :: (1, 2)
           :: repeat (1, 2) n ++ Rest) 1)).
    { apply hTDN. }
    apply hsteps_refl. }
  (* TUP *)
  apply (hsteps_trans _ (HC [19] 41 3 2 ((64, 2)
      :: (1, 1) :: (1, 2) :: (1, 2)
         :: repeat (1, 2) n ++ Rest) 1)).
  { apply (hsteps_step _ (HC [19] 41 3 2 ((64, 2)
        :: (1, 1) :: (1, 2) :: (1, 2)
           :: repeat (1, 2) n ++ Rest) 1)).
    { replace (HB [19] 41 1 4 ((66, 2)
                :: (1, 1) :: (1, 2) :: (1, 2)
                   :: repeat (1, 2) n ++ Rest) 1)
        with (HB [19] 41 1 (S (S 2)) ((S (S (S 63)), 2)
                :: (1, 1) :: (1, 2) :: (1, 2)
                   :: repeat (1, 2) n ++ Rest) 1) by sec_eq.
      replace (HC [19] 41 3 2 ((64, 2)
                :: (1, 1) :: (1, 2) :: (1, 2)
                   :: repeat (1, 2) n ++ Rest) 1)
        with (HC [19] 41 (S 2) 2 ((S 63, 2)
                :: (1, 1) :: (1, 2) :: (1, 2)
                   :: repeat (1, 2) n ++ Rest) 1) by sec_eq.
      apply hTUP. }
    apply hsteps_refl. }
  (* stage C: LOOPN 31 *)
  apply (hsteps_trans _ (HC [19] 41 65 2 ((2, 2)
      :: (1, 1) :: (1, 2) :: (1, 2)
         :: repeat (1, 2) n ++ Rest) 1)).
  { replace (HC [19] 41 3 2 ((64, 2)
              :: (1, 1) :: (1, 2) :: (1, 2)
                 :: repeat (1, 2) n ++ Rest) 1)
      with (HC [19] 41 (2*0 + 3) 2 ((64, 2)
              :: (1, 1) :: (1, 2) :: (1, 2)
                 :: repeat (1, 2) n ++ Rest) 1) by sec_eq.
    replace (HC [19] 41 65 2 ((2, 2)
              :: (1, 1) :: (1, 2) :: (1, 2)
                 :: repeat (1, 2) n ++ Rest) 1)
      with (HC [19] 41 (2*(0 + 31) + 3) 2 ((64 - 2*31, 2)
              :: (1, 1) :: (1, 2) :: (1, 2)
                 :: repeat (1, 2) n ++ Rest) 1) by sec_eq.
    apply (LOOPN 31 0 [19] 41 64
             ((1, 1) :: (1, 2) :: (1, 2)
              :: repeat (1, 2) n ++ Rest) 1); lia. }
  (* PUSH *)
  apply (hsteps_trans _ (HC [19] 40 1 2 ((63, 2) :: (2, 2)
      :: (1, 1) :: (1, 2) :: (1, 2)
         :: repeat (1, 2) n ++ Rest) 1)).
  { apply (hsteps_step _ (HC [19] 40 1 2 ((63, 2) :: (2, 2)
        :: (1, 1) :: (1, 2) :: (1, 2)
           :: repeat (1, 2) n ++ Rest) 1)).
    { replace (HC [19] 41 65 2 ((2, 2)
                :: (1, 1) :: (1, 2) :: (1, 2)
                   :: repeat (1, 2) n ++ Rest) 1)
        with (HC [19] (S 40) (S (S (S 62))) 2 ((2, 2)
                :: (1, 1) :: (1, 2) :: (1, 2)
                   :: repeat (1, 2) n ++ Rest) 1) by sec_eq.
      replace (HC [19] 40 1 2 ((63, 2) :: (2, 2)
                :: (1, 1) :: (1, 2) :: (1, 2)
                   :: repeat (1, 2) n ++ Rest) 1)
        with (HC [19] 40 1 2 ((S 62, 2) :: (2, 2)
                :: (1, 1) :: (1, 2) :: (1, 2)
                   :: repeat (1, 2) n ++ Rest) 1) by sec_eq.
      apply hPUSH. }
    apply hsteps_refl. }
  (* TDN *)
  apply (hsteps_trans _ (HB [19] 40 1 4 ((63, 2) :: (2, 2)
      :: (1, 1) :: (1, 2) :: (1, 2)
         :: repeat (1, 2) n ++ Rest) 1)).
  { apply (hsteps_step _ (HB [19] 40 1 4 ((63, 2) :: (2, 2)
        :: (1, 1) :: (1, 2) :: (1, 2)
           :: repeat (1, 2) n ++ Rest) 1)).
    { apply hTDN. }
    apply hsteps_refl. }
  (* TUP *)
  apply (hsteps_trans _ (HC [19] 40 3 2 ((61, 2) :: (2, 2)
      :: (1, 1) :: (1, 2) :: (1, 2)
         :: repeat (1, 2) n ++ Rest) 1)).
  { apply (hsteps_step _ (HC [19] 40 3 2 ((61, 2) :: (2, 2)
        :: (1, 1) :: (1, 2) :: (1, 2)
           :: repeat (1, 2) n ++ Rest) 1)).
    { replace (HB [19] 40 1 4 ((63, 2) :: (2, 2)
                :: (1, 1) :: (1, 2) :: (1, 2)
                   :: repeat (1, 2) n ++ Rest) 1)
        with (HB [19] 40 1 (S (S 2)) ((S (S (S 60)), 2) :: (2, 2)
                :: (1, 1) :: (1, 2) :: (1, 2)
                   :: repeat (1, 2) n ++ Rest) 1) by sec_eq.
      replace (HC [19] 40 3 2 ((61, 2) :: (2, 2)
                :: (1, 1) :: (1, 2) :: (1, 2)
                   :: repeat (1, 2) n ++ Rest) 1)
        with (HC [19] 40 (S 2) 2 ((S 60, 2) :: (2, 2)
                :: (1, 1) :: (1, 2) :: (1, 2)
                   :: repeat (1, 2) n ++ Rest) 1) by sec_eq.
      apply hTUP. }
    apply hsteps_refl. }
  (* LOOPN 30 *)
  apply (hsteps_trans _ (HC [19] 40 63 2 ((1, 2) :: (2, 2)
      :: (1, 1) :: (1, 2) :: (1, 2)
         :: repeat (1, 2) n ++ Rest) 1)).
  { replace (HC [19] 40 3 2 ((61, 2) :: (2, 2)
              :: (1, 1) :: (1, 2) :: (1, 2)
                 :: repeat (1, 2) n ++ Rest) 1)
      with (HC [19] 40 (2*0 + 3) 2 ((61, 2) :: (2, 2)
              :: (1, 1) :: (1, 2) :: (1, 2)
                 :: repeat (1, 2) n ++ Rest) 1) by sec_eq.
    replace (HC [19] 40 63 2 ((1, 2) :: (2, 2)
              :: (1, 1) :: (1, 2) :: (1, 2)
                 :: repeat (1, 2) n ++ Rest) 1)
      with (HC [19] 40 (2*(0 + 30) + 3) 2 ((61 - 2*30, 2) :: (2, 2)
              :: (1, 1) :: (1, 2) :: (1, 2)
                 :: repeat (1, 2) n ++ Rest) 1) by sec_eq.
    apply (LOOPN 30 0 [19] 40 61
             ((2, 2) :: (1, 1) :: (1, 2) :: (1, 2)
              :: repeat (1, 2) n ++ Rest) 1); lia. }
  (* hGRIND 30 *)
  apply (hsteps_trans _ (HB [19] 40 1 66 ((1, 2) :: (2, 2)
      :: (1, 1) :: (1, 2) :: (1, 2)
         :: repeat (1, 2) n ++ Rest) 1)).
  { replace (HC [19] 40 63 2 ((1, 2) :: (2, 2)
              :: (1, 1) :: (1, 2) :: (1, 2)
                 :: repeat (1, 2) n ++ Rest) 1)
      with (HC [19] 40 (2*30 + 3) 2 ((1, 2) :: (2, 2)
              :: (1, 1) :: (1, 2) :: (1, 2)
                 :: repeat (1, 2) n ++ Rest) 1) by sec_eq.
    replace (HB [19] 40 1 66 ((1, 2) :: (2, 2)
              :: (1, 1) :: (1, 2) :: (1, 2)
                 :: repeat (1, 2) n ++ Rest) 1)
      with (HB [19] 40 1 (2*30 + 6) ((1, 2) :: (2, 2)
              :: (1, 1) :: (1, 2) :: (1, 2)
                 :: repeat (1, 2) n ++ Rest) 1) by sec_eq.
    apply hGRIND; lia. }
  (* POP *)
  apply (hsteps_trans _ (HB [19] 41 1 68 ((2, 2)
      :: (1, 1) :: (1, 2) :: (1, 2)
         :: repeat (1, 2) n ++ Rest) 1)).
  { apply (hsteps_step _ (HB [19] 41 1 68 ((2, 2)
        :: (1, 1) :: (1, 2) :: (1, 2)
           :: repeat (1, 2) n ++ Rest) 1)).
    { replace (HB [19] 41 1 68 ((2, 2)
                :: (1, 1) :: (1, 2) :: (1, 2)
                   :: repeat (1, 2) n ++ Rest) 1)
        with (HB [19] (S 40) 1 (66 + 2) ((2, 2)
                :: (1, 1) :: (1, 2) :: (1, 2)
                   :: repeat (1, 2) n ++ Rest) 1) by sec_eq.
      apply hPOP; lia. }
    apply hsteps_refl. }
  (* TRANS2_1 *)
  apply (hsteps_trans _ (HB [42; 19] 69 1 3
      ((1, 2) :: (1, 2) :: repeat (1, 2) n ++ Rest) 1)).
  { apply (hsteps_step _ (HB [42; 19] 69 1 3
        ((1, 2) :: (1, 2) :: repeat (1, 2) n ++ Rest) 1)).
    { replace (HB [19] 41 1 68 ((2, 2)
                :: (1, 1) :: (1, 2) :: (1, 2)
                   :: repeat (1, 2) n ++ Rest) 1)
        with (HB [19] 41 1 (S 67)
                ((2, S 1) :: (1, 1) :: (1, 2) :: (1, 2)
                 :: repeat (1, 2) n ++ Rest) 1) by sec_eq.
      replace (HB [42; 19] 69 1 3
                ((1, 2) :: (1, 2) :: repeat (1, 2) n ++ Rest) 1)
        with (HB (S 41 :: [19]) (S (S 67)) 1 (S 1 + 1)
                ((1, 2) :: (1, 2) :: repeat (1, 2) n ++ Rest) 1)
        by sec_eq.
      apply hTRANS2_1; lia. }
    apply hsteps_refl. }
  (* spine POP chain *)
  replace (HB [42; 19] (71 + n) 1 (7 + 2*n) Rest 1)
    with (HB [42; 19] (69 + S (S n)) 1 (3 + 2 * S (S n)) Rest 1)
    by sec_eq.
  replace ((1, 2) :: (1, 2) :: repeat (1, 2) n ++ Rest)
    with (repeat (1, 2) (S (S n)) ++ Rest) by sec_eq.
  apply pop_chain_h_app; lia.
Qed.

(* ----------------------------------------------------------------- *)
(* Part 2: PHASE7_TRANS19 -- the transitional segment at frame       *)
(* ([19; 0], 110): TUP + hGRIND_even 80 + hTUP2_1 + TDN onto         *)
(* frame ([110; 19; 0], 164).  Residue-general (r >= 6).             *)
(* ----------------------------------------------------------------- *)

Lemma PHASE7_TRANS19 : forall r beta, 6 <= r -> 2 <= beta ->
  hsteps (HB [19; 0] 110 1 165
            ((r, 2) :: (1, 1) :: repeat (1, 2) (beta - 1)) 1)
         (HB [110; 19; 0] 164 1 4
            ((r - 4, 2) :: (1, 1) :: repeat (1, 2) (beta - 1)) 1).
Proof.
  intros r beta Hr Hb.
  (* TUP *)
  apply (hsteps_trans _ (HC [19; 0] 110 164 2
      ((r - 2, 2) :: (1, 1) :: repeat (1, 2) (beta - 1)) 1)).
  { apply (hsteps_step _ (HC [19; 0] 110 164 2
        ((r - 2, 2) :: (1, 1) :: repeat (1, 2) (beta - 1)) 1)).
    { replace (HB [19; 0] 110 1 165
                ((r, 2) :: (1, 1) :: repeat (1, 2) (beta - 1)) 1)
        with (HB [19; 0] 110 1 (S (S 163))
                ((S (S (S (r - 3))), 2)
                 :: (1, 1) :: repeat (1, 2) (beta - 1)) 1) by sec_eq.
      replace (HC [19; 0] 110 164 2
                ((r - 2, 2) :: (1, 1) :: repeat (1, 2) (beta - 1)) 1)
        with (HC [19; 0] 110 (S 163) 2
                ((S (r - 3), 2)
                 :: (1, 1) :: repeat (1, 2) (beta - 1)) 1) by sec_eq.
      apply hTUP. }
    apply hsteps_refl. }
  (* hGRIND_even 80 *)
  apply (hsteps_trans _ (HB [19; 0] 109 1 164
      ((2, 2) :: (r - 2, 2)
       :: (1, 1) :: repeat (1, 2) (beta - 1)) 1)).
  { replace (HC [19; 0] 110 164 2
              ((r - 2, 2) :: (1, 1) :: repeat (1, 2) (beta - 1)) 1)
      with (HC [19; 0] (S 109) (2*80 + 4) 2
              ((r - 2, 2) :: (1, 1) :: repeat (1, 2) (beta - 1)) 1)
      by sec_eq.
    replace (HB [19; 0] 109 1 164
              ((2, 2) :: (r - 2, 2)
               :: (1, 1) :: repeat (1, 2) (beta - 1)) 1)
      with (HB [19; 0] 109 1 (2*80 + 4)
              ((2, 2) :: (r - 2, 2)
               :: (1, 1) :: repeat (1, 2) (beta - 1)) 1) by sec_eq.
    apply hGRIND_even; lia. }
  (* TUP2_1 *)
  apply (hsteps_trans _ (HC [110; 19; 0] 164 1 2
      ((r - 4, 2) :: (1, 1) :: repeat (1, 2) (beta - 1)) 1)).
  { apply (hsteps_step _ (HC [110; 19; 0] 164 1 2
        ((r - 4, 2) :: (1, 1) :: repeat (1, 2) (beta - 1)) 1)).
    { replace (HB [19; 0] 109 1 164
                ((2, 2) :: (r - 2, 2)
                 :: (1, 1) :: repeat (1, 2) (beta - 1)) 1)
        with (HB [19; 0] 109 1 (S 163)
                ((2, S (S 0)) :: (S (S (S (r - 5))), 2)
                 :: (1, 1) :: repeat (1, 2) (beta - 1)) 1) by sec_eq.
      replace (HC [110; 19; 0] 164 1 2
                ((r - 4, 2) :: (1, 1) :: repeat (1, 2) (beta - 1)) 1)
        with (HC (S 109 :: [19; 0]) (S 163) (S 0) 2
                ((S (r - 5), 2)
                 :: (1, 1) :: repeat (1, 2) (beta - 1)) 1) by sec_eq.
      apply hTUP2_1. }
    apply hsteps_refl. }
  (* TDN *)
  apply (hsteps_step _ (HB [110; 19; 0] 164 1 4
      ((r - 4, 2) :: (1, 1) :: repeat (1, 2) (beta - 1)) 1)).
  { apply hTDN. }
  apply hsteps_refl.
Qed.

(* ----------------------------------------------------------------- *)
(* Part 3: PHASE7_TO_MID -- from the ESC source at R = 2m + 46       *)
(* (m >= 279) through PHASE6_TO_MID, the transitional segment,       *)
(* 164 clean rounds at frame ([110; 19; 0], 164), the boundary       *)
(* final grind (DIPDESC 164), the hPX2A dip dispatch and             *)
(* GRIND108_MID, landing at HB [42; 19] 235 1 335 over the           *)
(* passenger ((2m - 556, 2) :: Pe).                                  *)
(* ----------------------------------------------------------------- *)

Lemma PHASE7_TO_MID : forall m beta, 279 <= m -> 2 <= beta ->
  hsteps (HC [] 3 1 2
            ((2*m + 46, 2) :: (1, 1) :: repeat (1, 2) (beta - 1)) 1)
         (HB [42; 19] 235 1 335
            ((2*m - 556, 2) :: (1, 1) :: repeat (1, 2) (beta - 1)) 1).
Proof.
  intros m beta Hm Hb.
  (* phase 6 to its landing *)
  apply (hsteps_trans _ (HB [19; 0] 110 1 165
      ((2*m - 222, 2) :: (1, 1) :: repeat (1, 2) (beta - 1)) 1)).
  { apply (PHASE6_TO_MID m beta); lia. }
  (* transitional segment onto frame ([110; 19; 0], 164) *)
  apply (hsteps_trans _ (HB [110; 19; 0] 164 1 4
      ((2*m - 226, 2) :: (1, 1) :: repeat (1, 2) (beta - 1)) 1)).
  { replace (HB [110; 19; 0] 164 1 4
              ((2*m - 226, 2) :: (1, 1) :: repeat (1, 2) (beta - 1)) 1)
      with (HB [110; 19; 0] 164 1 4
              ((2*m - 222 - 4, 2)
               :: (1, 1) :: repeat (1, 2) (beta - 1)) 1) by sec_eq.
    apply (PHASE7_TRANS19 (2*m - 222) beta); lia. }
  (* 164 clean rounds *)
  apply (hsteps_trans _ (HB [110; 19; 0] 164 1 332
      ((2*m - 554, 2) :: (1, 1) :: repeat (1, 2) (beta - 1)) 1)).
  { replace (HB [110; 19; 0] 164 1 4
              ((2*m - 226, 2) :: (1, 1) :: repeat (1, 2) (beta - 1)) 1)
      with (HB [110; 19; 0] 164 1 (2*0 + 4)
              ((2*m - 226, 2) :: (1, 1) :: repeat (1, 2) (beta - 1)) 1)
      by sec_eq.
    replace (HB [110; 19; 0] 164 1 332
              ((2*m - 554, 2) :: (1, 1) :: repeat (1, 2) (beta - 1)) 1)
      with (HB [110; 19; 0] 164 1 (2*(0 + 164) + 4)
              ((2*m - 226 - 2*164, 2)
               :: (1, 1) :: repeat (1, 2) (beta - 1)) 1) by sec_eq.
    apply (rounds_from4g 164 0 [110; 19; 0] 164 (2*m - 226)
             ((1, 1) :: repeat (1, 2) (beta - 1)) 1); lia. }
  (* final TUP *)
  apply (hsteps_trans _ (HC [110; 19; 0] 164 331 2
      ((2*m - 556, 2) :: (1, 1) :: repeat (1, 2) (beta - 1)) 1)).
  { apply (hsteps_step _ (HC [110; 19; 0] 164 331 2
        ((2*m - 556, 2) :: (1, 1) :: repeat (1, 2) (beta - 1)) 1)).
    { replace (HB [110; 19; 0] 164 1 332
                ((2*m - 554, 2) :: (1, 1) :: repeat (1, 2) (beta - 1)) 1)
        with (HB [110; 19; 0] 164 1 (S (S 330))
                ((S (S (S (2*m - 557))), 2)
                 :: (1, 1) :: repeat (1, 2) (beta - 1)) 1) by sec_eq.
      replace (HC [110; 19; 0] 164 331 2
                ((2*m - 556, 2) :: (1, 1) :: repeat (1, 2) (beta - 1)) 1)
        with (HC [110; 19; 0] 164 (S 330) 2
                ((S (2*m - 557), 2)
                 :: (1, 1) :: repeat (1, 2) (beta - 1)) 1) by sec_eq.
      apply hTUP. }
    apply hsteps_refl. }
  (* DIPDESC 164: the boundary descent *)
  apply (hsteps_trans _ (HC [110; 19; 0] 0 3 2
      (repeat (1, 2) 164
       ++ ((2*m - 556, 2) :: (1, 1) :: repeat (1, 2) (beta - 1))) 1)).
  { replace (HC [110; 19; 0] 164 331 2
              ((2*m - 556, 2) :: (1, 1) :: repeat (1, 2) (beta - 1)) 1)
      with (HC [110; 19; 0] 164 (2*164 + 3) 2
              ((2*m - 556, 2) :: (1, 1) :: repeat (1, 2) (beta - 1)) 1)
      by sec_eq.
    apply (DIPDESC 164 [110; 19; 0]
             ((2*m - 556, 2) :: (1, 1) :: repeat (1, 2) (beta - 1)) 1). }
  (* the dip fires hPX2A *)
  apply (hsteps_trans _ (HC [0] 18 108 2
      ((1, 1) :: (1, 2) :: (1, 2) :: repeat (1, 2) 164
       ++ ((2*m - 556, 2) :: (1, 1) :: repeat (1, 2) (beta - 1))) 1)).
  { apply (hsteps_step _ (HC [0] 18 108 2
        ((1, 1) :: (1, 2) :: (1, 2) :: repeat (1, 2) 164
         ++ ((2*m - 556, 2) :: (1, 1) :: repeat (1, 2) (beta - 1))) 1)).
    { replace (HC [110; 19; 0] 0 3 2
                (repeat (1, 2) 164
                 ++ ((2*m - 556, 2)
                     :: (1, 1) :: repeat (1, 2) (beta - 1))) 1)
        with (HC (S (S (S 107)) :: S 18 :: [0]) 0 3 2
                (repeat (1, 2) 164
                 ++ ((2*m - 556, 2)
                     :: (1, 1) :: repeat (1, 2) (beta - 1))) 1) by sec_eq.
      replace (HC [0] 18 108 2
                ((1, 1) :: (1, 2) :: (1, 2) :: repeat (1, 2) 164
                 ++ ((2*m - 556, 2)
                     :: (1, 1) :: repeat (1, 2) (beta - 1))) 1)
        with (HC [0] 18 (S 107) 2
                ((1, 1) :: (1, 2) :: (1, 2) :: repeat (1, 2) 164
                 ++ ((2*m - 556, 2)
                     :: (1, 1) :: repeat (1, 2) (beta - 1))) 1) by sec_eq.
      apply hPX2A. }
    apply hsteps_refl. }
  (* GRIND108_MID *)
  replace (HB [42; 19] 235 1 335
            ((2*m - 556, 2) :: (1, 1) :: repeat (1, 2) (beta - 1)) 1)
    with (HB [42; 19] (71 + 164) 1 (7 + 2*164)
            ((2*m - 556, 2) :: (1, 1) :: repeat (1, 2) (beta - 1)) 1)
    by sec_eq.
  apply GRIND108_MID.
Qed.

(* ----------------------------------------------------------------- *)
(* Part 4: PHASE7_TRANS42 -- the transitional segment at frame       *)
(* ([42; 19], 235): TUP + hGRIND_even 165 + hTUP2_1 + TDN onto        *)
(* frame ([235; 42; 19], 334).  Residue-general (r >= 6).            *)
(* ----------------------------------------------------------------- *)

Lemma PHASE7_TRANS42 : forall r beta, 6 <= r -> 2 <= beta ->
  hsteps (HB [42; 19] 235 1 335
            ((r, 2) :: (1, 1) :: repeat (1, 2) (beta - 1)) 1)
         (HB [235; 42; 19] 334 1 4
            ((r - 4, 2) :: (1, 1) :: repeat (1, 2) (beta - 1)) 1).
Proof.
  intros r beta Hr Hb.
  (* TUP *)
  apply (hsteps_trans _ (HC [42; 19] 235 334 2
      ((r - 2, 2) :: (1, 1) :: repeat (1, 2) (beta - 1)) 1)).
  { apply (hsteps_step _ (HC [42; 19] 235 334 2
        ((r - 2, 2) :: (1, 1) :: repeat (1, 2) (beta - 1)) 1)).
    { replace (HB [42; 19] 235 1 335
                ((r, 2) :: (1, 1) :: repeat (1, 2) (beta - 1)) 1)
        with (HB [42; 19] 235 1 (S (S 333))
                ((S (S (S (r - 3))), 2)
                 :: (1, 1) :: repeat (1, 2) (beta - 1)) 1) by sec_eq.
      replace (HC [42; 19] 235 334 2
                ((r - 2, 2) :: (1, 1) :: repeat (1, 2) (beta - 1)) 1)
        with (HC [42; 19] 235 (S 333) 2
                ((S (r - 3), 2)
                 :: (1, 1) :: repeat (1, 2) (beta - 1)) 1) by sec_eq.
      apply hTUP. }
    apply hsteps_refl. }
  (* hGRIND_even 165 *)
  apply (hsteps_trans _ (HB [42; 19] 234 1 334
      ((2, 2) :: (r - 2, 2)
       :: (1, 1) :: repeat (1, 2) (beta - 1)) 1)).
  { replace (HC [42; 19] 235 334 2
              ((r - 2, 2) :: (1, 1) :: repeat (1, 2) (beta - 1)) 1)
      with (HC [42; 19] (S 234) (2*165 + 4) 2
              ((r - 2, 2) :: (1, 1) :: repeat (1, 2) (beta - 1)) 1)
      by sec_eq.
    replace (HB [42; 19] 234 1 334
              ((2, 2) :: (r - 2, 2)
               :: (1, 1) :: repeat (1, 2) (beta - 1)) 1)
      with (HB [42; 19] 234 1 (2*165 + 4)
              ((2, 2) :: (r - 2, 2)
               :: (1, 1) :: repeat (1, 2) (beta - 1)) 1) by sec_eq.
    apply hGRIND_even; lia. }
  (* TUP2_1 *)
  apply (hsteps_trans _ (HC [235; 42; 19] 334 1 2
      ((r - 4, 2) :: (1, 1) :: repeat (1, 2) (beta - 1)) 1)).
  { apply (hsteps_step _ (HC [235; 42; 19] 334 1 2
        ((r - 4, 2) :: (1, 1) :: repeat (1, 2) (beta - 1)) 1)).
    { replace (HB [42; 19] 234 1 334
                ((2, 2) :: (r - 2, 2)
                 :: (1, 1) :: repeat (1, 2) (beta - 1)) 1)
        with (HB [42; 19] 234 1 (S 333)
                ((2, S (S 0)) :: (S (S (S (r - 5))), 2)
                 :: (1, 1) :: repeat (1, 2) (beta - 1)) 1) by sec_eq.
      replace (HC [235; 42; 19] 334 1 2
                ((r - 4, 2) :: (1, 1) :: repeat (1, 2) (beta - 1)) 1)
        with (HC (S 234 :: [42; 19]) (S 333) (S 0) 2
                ((S (r - 5), 2)
                 :: (1, 1) :: repeat (1, 2) (beta - 1)) 1) by sec_eq.
      apply hTUP2_1. }
    apply hsteps_refl. }
  (* TDN *)
  apply (hsteps_step _ (HB [235; 42; 19] 334 1 4
      ((r - 4, 2) :: (1, 1) :: repeat (1, 2) (beta - 1)) 1)).
  { apply hTDN. }
  apply hsteps_refl.
Qed.

(* ----------------------------------------------------------------- *)
(* Part 5: the phase-7 finishes.                                     *)
(* ----------------------------------------------------------------- *)

Lemma ESC_TO_REGEN_604 : forall beta, 2 <= beta ->
  exists pb a,
    hsteps (HC [] 3 1 2
              ((604, 2) :: (1, 1) :: repeat (1, 2) (beta - 1)) 1)
           (HB pb a 1 (2*beta + 1) [] 1) /\ beta <= a.
Proof.
  intros beta Hb.
  exists [236; 42; 19], (335 + beta). split; [| lia].
  apply (hsteps_trans _ (HB [42; 19] 235 1 335
      ((2, 2) :: (1, 1) :: repeat (1, 2) (beta - 1)) 1)).
  { apply (PHASE7_TO_MID 279 beta); lia. }
  apply (TAIL [42; 19] 235 335 beta); lia.
Qed.

Lemma ESC_TO_REGEN_606 : forall beta, 2 <= beta ->
  exists pb a,
    hsteps (HC [] 3 1 2
              ((606, 2) :: (1, 1) :: repeat (1, 2) (beta - 1)) 1)
           (HB pb a 1 (2*beta + 1) [] 1) /\ beta <= a.
Proof.
  intros beta Hb.
  exists [335; 235; 42; 19], (beta + 2). split; [| lia].
  apply (hsteps_trans _ (HB [42; 19] 235 1 335
      ((4, 2) :: (1, 1) :: repeat (1, 2) (beta - 1)) 1)).
  { apply (PHASE7_TO_MID 280 beta); lia. }
  (* TUP *)
  apply (hsteps_trans _ (HC [42; 19] 235 334 2
      ((2, 2) :: (1, 1) :: repeat (1, 2) (beta - 1)) 1)).
  { apply (hsteps_step _ (HC [42; 19] 235 334 2
        ((2, 2) :: (1, 1) :: repeat (1, 2) (beta - 1)) 1)).
    { replace (HB [42; 19] 235 1 335
                ((4, 2) :: (1, 1) :: repeat (1, 2) (beta - 1)) 1)
        with (HB [42; 19] 235 1 (S (S 333))
                ((S (S (S 1)), 2)
                 :: (1, 1) :: repeat (1, 2) (beta - 1)) 1) by sec_eq.
      replace (HC [42; 19] 235 334 2
                ((2, 2) :: (1, 1) :: repeat (1, 2) (beta - 1)) 1)
        with (HC [42; 19] 235 (S 333) 2
                ((S 1, 2)
                 :: (1, 1) :: repeat (1, 2) (beta - 1)) 1) by sec_eq.
      apply hTUP. }
    apply hsteps_refl. }
  (* hGRIND_even 165 *)
  apply (hsteps_trans _ (HB [42; 19] 234 1 334
      ((2, 2) :: (2, 2) :: (1, 1) :: repeat (1, 2) (beta - 1)) 1)).
  { replace (HC [42; 19] 235 334 2
              ((2, 2) :: (1, 1) :: repeat (1, 2) (beta - 1)) 1)
      with (HC [42; 19] (S 234) (2*165 + 4) 2
              ((2, 2) :: (1, 1) :: repeat (1, 2) (beta - 1)) 1)
      by sec_eq.
    replace (HB [42; 19] 234 1 334
              ((2, 2) :: (2, 2)
               :: (1, 1) :: repeat (1, 2) (beta - 1)) 1)
      with (HB [42; 19] 234 1 (2*165 + 4)
              ((2, 2) :: (2, 2)
               :: (1, 1) :: repeat (1, 2) (beta - 1)) 1) by sec_eq.
    apply hGRIND_even; lia. }
  (* TAIL2 *)
  apply (TAIL2 [42; 19] 234 333 beta); lia.
Qed.

Lemma ESC_TO_REGEN_608 : forall beta, 2 <= beta ->
  exists pb a,
    hsteps (HC [] 3 1 2
              ((608, 2) :: (1, 1) :: repeat (1, 2) (beta - 1)) 1)
           (HB pb a 1 (2*beta + 1) [] 1) /\ beta <= a.
Proof.
  intros beta Hb.
  exists [335; 235; 42; 19], (4 + beta). split; [| lia].
  apply (hsteps_trans _ (HB [42; 19] 235 1 335
      ((6, 2) :: (1, 1) :: repeat (1, 2) (beta - 1)) 1)).
  { apply (PHASE7_TO_MID 281 beta); lia. }
  apply (hsteps_trans _ (HB [235; 42; 19] 334 1 4
      ((2, 2) :: (1, 1) :: repeat (1, 2) (beta - 1)) 1)).
  { apply (PHASE7_TRANS42 6 beta); lia. }
  apply (TAIL [235; 42; 19] 334 4 beta); lia.
Qed.

Lemma ESC_TO_REGEN_BIG7 : forall m beta,
  282 <= m -> m <= 615 -> 2 <= beta ->
  exists pb a,
    hsteps (HC [] 3 1 2
              ((2*m + 46, 2) :: (1, 1) :: repeat (1, 2) (beta - 1)) 1)
           (HB pb a 1 (2*beta + 1) [] 1) /\ beta <= a.
Proof.
  intros m beta Hm1 Hm2 Hb.
  exists [335; 235; 42; 19], (2*m - 558 + beta). split; [| lia].
  apply (hsteps_trans _ (HB [42; 19] 235 1 335
      ((2*m - 556, 2) :: (1, 1) :: repeat (1, 2) (beta - 1)) 1)).
  { apply (PHASE7_TO_MID m beta); lia. }
  apply (hsteps_trans _ (HB [235; 42; 19] 334 1 4
      ((2*m - 560, 2) :: (1, 1) :: repeat (1, 2) (beta - 1)) 1)).
  { replace (HB [235; 42; 19] 334 1 4
              ((2*m - 560, 2) :: (1, 1) :: repeat (1, 2) (beta - 1)) 1)
      with (HB [235; 42; 19] 334 1 4
              ((2*m - 556 - 4, 2)
               :: (1, 1) :: repeat (1, 2) (beta - 1)) 1) by sec_eq.
    apply (PHASE7_TRANS42 (2*m - 556) beta); lia. }
  (* rounds at the new frame *)
  apply (hsteps_trans _ (HB [235; 42; 19] 334 1 (2*m - 560)
      ((4, 2) :: (1, 1) :: repeat (1, 2) (beta - 1)) 1)).
  { replace (HB [235; 42; 19] 334 1 4
              ((2*m - 560, 2) :: (1, 1) :: repeat (1, 2) (beta - 1)) 1)
      with (HB [235; 42; 19] 334 1 (2*0 + 4)
              ((2*m - 560, 2) :: (1, 1) :: repeat (1, 2) (beta - 1)) 1)
      by sec_eq.
    replace (HB [235; 42; 19] 334 1 (2*m - 560)
              ((4, 2) :: (1, 1) :: repeat (1, 2) (beta - 1)) 1)
      with (HB [235; 42; 19] 334 1 (2*(0 + (m - 282)) + 4)
              ((2*m - 560 - 2*(m - 282), 2)
               :: (1, 1) :: repeat (1, 2) (beta - 1)) 1) by sec_eq.
    apply (rounds_from4g (m - 282) 0 [235; 42; 19] 334 (2*m - 560)
             ((1, 1) :: repeat (1, 2) (beta - 1)) 1); lia. }
  (* final TUP *)
  apply (hsteps_trans _ (HC [235; 42; 19] 334 (2*m - 561) 2
      ((2, 2) :: (1, 1) :: repeat (1, 2) (beta - 1)) 1)).
  { apply (hsteps_step _ (HC [235; 42; 19] 334 (2*m - 561) 2
        ((2, 2) :: (1, 1) :: repeat (1, 2) (beta - 1)) 1)).
    { replace (HB [235; 42; 19] 334 1 (2*m - 560)
                ((4, 2) :: (1, 1) :: repeat (1, 2) (beta - 1)) 1)
        with (HB [235; 42; 19] 334 1 (S (S (2*m - 562)))
                ((S (S (S 1)), 2)
                 :: (1, 1) :: repeat (1, 2) (beta - 1)) 1) by sec_eq.
      replace (HC [235; 42; 19] 334 (2*m - 561) 2
                ((2, 2) :: (1, 1) :: repeat (1, 2) (beta - 1)) 1)
        with (HC [235; 42; 19] 334 (S (2*m - 562)) 2
                ((S 1, 2)
                 :: (1, 1) :: repeat (1, 2) (beta - 1)) 1) by sec_eq.
      apply hTUP. }
    apply hsteps_refl. }
  (* final grind *)
  apply (hsteps_trans _ (HB [235; 42; 19] 334 1 (2*m - 558)
      ((2, 2) :: (1, 1) :: repeat (1, 2) (beta - 1)) 1)).
  { replace (HC [235; 42; 19] 334 (2*m - 561) 2
              ((2, 2) :: (1, 1) :: repeat (1, 2) (beta - 1)) 1)
      with (HC [235; 42; 19] 334 (2*(m - 282) + 3) 2
              ((2, 2) :: (1, 1) :: repeat (1, 2) (beta - 1)) 1)
      by sec_eq.
    replace (HB [235; 42; 19] 334 1 (2*m - 558)
              ((2, 2) :: (1, 1) :: repeat (1, 2) (beta - 1)) 1)
      with (HB [235; 42; 19] 334 1 (2*(m - 282) + 6)
              ((2, 2) :: (1, 1) :: repeat (1, 2) (beta - 1)) 1)
      by sec_eq.
    apply hGRIND; lia. }
  (* TAIL *)
  apply (TAIL [235; 42; 19] 334 (2*m - 558) beta); lia.
Qed.

(* ----------------------------------------------------------------- *)
(* Part 6: the phase-7 era law and the combined law through          *)
(* R <= 1276.                                                        *)
(* ----------------------------------------------------------------- *)

Lemma ESC_ERA_LAW_40 : forall R beta,
  (R = 604 \/ R = 606 \/ R = 608
   \/ (exists m, R = 2 * m + 46 /\ 282 <= m <= 615)) ->
  2 <= beta ->
  exists n c pb a, run n (esc_src (R + 6) (beta - 2)) = Some c
    /\ cfg_sim c (rcsec (false :: repeat true (S a) ++ enc pb)
                        (2 * beta + 2) [(1, 2)])
    /\ beta <= a.
Proof.
  intros R beta HR Hb.
  destruct HR as [E | [E | [E | [m [ER Hm]]]]].
  - subst R.
    destruct (ESC_TO_REGEN_604 beta Hb) as [pb [a [Hc Hf]]].
    apply (ESC_ERA_LAW_of 604 beta pb a);
      [lia | exact Hc | exact Hf | exact Hb].
  - subst R.
    destruct (ESC_TO_REGEN_606 beta Hb) as [pb [a [Hc Hf]]].
    apply (ESC_ERA_LAW_of 606 beta pb a);
      [lia | exact Hc | exact Hf | exact Hb].
  - subst R.
    destruct (ESC_TO_REGEN_608 beta Hb) as [pb [a [Hc Hf]]].
    apply (ESC_ERA_LAW_of 608 beta pb a);
      [lia | exact Hc | exact Hf | exact Hb].
  - subst R.
    destruct (ESC_TO_REGEN_BIG7 m beta ltac:(lia) ltac:(lia) Hb)
      as [pb [a [Hc Hf]]].
    apply (ESC_ERA_LAW_of (2 * m + 46) beta pb a);
      [lia | exact Hc | exact Hf | exact Hb].
Qed.

Lemma ESC_ERA_LAW_1276 : forall R beta,
  ((((R = 2 \/ R = 4 \/ R = 6 \/ R = 8 \/ R = 10 \/ R = 12 \/ R = 14
    \/ (exists m, R = 2 * m + 16 /\ m <= 12)
    \/ R = 42 \/ R = 44 \/ (exists m, R = 2 * m + 46 /\ m <= 34))
   \/ (R = 116 \/ R = 118 \/ R = 120
       \/ (exists m, R = 2 * m + 46 /\ 38 <= m <= 111)))
   \/ (R = 270 \/ R = 272 \/ R = 274
       \/ (exists m, R = 2 * m + 46 /\ 115 <= m <= 278)))
   \/ (R = 604 \/ R = 606 \/ R = 608
       \/ (exists m, R = 2 * m + 46 /\ 282 <= m <= 615)))
  -> 2 <= beta ->
  exists n c pb a, run n (esc_src (R + 6) (beta - 2)) = Some c
    /\ cfg_sim c (rcsec (false :: repeat true (S a) ++ enc pb)
                        (2 * beta + 2) [(1, 2)])
    /\ beta <= a.
Proof.
  intros R beta [HOLD | HNEW] Hb.
  - apply (ESC_ERA_LAW_602 R beta); [exact HOLD | exact Hb].
  - apply (ESC_ERA_LAW_40 R beta); [exact HNEW | exact Hb].
Qed.

(* ----------------------------------------------------------------- *)
(* Assumption audit                                                  *)
(* ----------------------------------------------------------------- *)

Print Assumptions ESC_ERA_LAW_1276.
Print Assumptions GRIND108_MID.
Print Assumptions PHASE7_TO_MID.
