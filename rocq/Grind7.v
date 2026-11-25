(* ================================================================= *)
(*  Grind7.v -- Phase 38: the phase-6 merged unwind, covering       *)
(*  every even R <= 602.                                             *)
(*                                                                   *)
(*  The Phase 37 fence: at R = 2m + 46 with m >= 112, phase 5's      *)
(*  finish (ESC_TO_REGEN_BIG3 in Grind6.v) breaks twice over: the    *)
(*  rounds at ([41; 14; 5], 74) admit at most 74 rounds, and the     *)
(*  final grind (t = m - 38 at frame 74) is over-floor for           *)
(*  t > 74.  Taking the maximal 74 clean rounds leaves the final     *)
(*  grind at exactly t = 74 = a2 over the passenger residue          *)
(*  ((2m - 222, 2) :: Pe): a boundary grind.  Its dip bottom is       *)
(*  NOT a new dispatch case: the descent to the dip is the           *)
(*  t = a2 case of the grind recursion (new lemma DIPDESC,          *)
(*  pb-general, no floor hypothesis), and the dip at                 *)
(*  [41; 14; 5] fires the existing hPX2A (Dev.v, cost 52),           *)
(*  landing at HC [5] 13 39 2 with the stack grown by the            *)
(*  dispatch's three extra pairs.  The continuation is the           *)
(*  ([5], 13) grind at g0 = 39 over an arbitrary carried rest        *)
(*  (GRIND39_MID): PUSH/TDN/TUP + a truncated loop (LOOPN) +         *)
(*  DIPDESC 12 to its own dip, hPX2B5, a 15-POP run, hTUP,           *)
(*  hGRIND_even 14, hTUP2_1, grind_prefix, two clean rounds and      *)
(*  a POP chain over the spine, landing at                           *)
(*  HB [19; 0] (36 + n) 1 (17 + 2n) Rest for spine length n.         *)
(*                                                                   *)
(*  Finishes: m = 112 (R = 270) is TAIL at that landing;             *)
(*  m = 113 (R = 272) runs one transitional round (TUP +             *)
(*  hGRIND_even 80) and closes with the TRANS2_2 tail (TAIL2);       *)
(*  m = 114 (R = 274) runs the transitional round and TAIL;          *)
(*  115 <= m <= 278 (R <= 602) continues with rounds at the new      *)
(*  frame ([110; 19; 0], 164), a final clean grind and TAIL.         *)
(*  The next fence is m = 279 (R = 604): the rounds at frame 164     *)
(*  (count m - 115 <= 164) and the final grind (t = m - 115,         *)
(*  floor t + 1 <= 164) both bind; the final grind at t = a2         *)
(*  would again be a DIPDESC descent whose dip at                    *)
(*  [110; 19; 0] fires hPX2A into a phase-7 continuation.            *)
(*                                                                   *)
(*  On the general-induction question (assessed in Phase 38):        *)
(*  the phase recursion does NOT close by induction on phase         *)
(*  depth in the current lemma vocabulary.  DIPDESC, LOOPN and       *)
(*  hGRIND_even are general, but each phase's continuation is        *)
(*  determined by (i) which dip dispatch fires -- a finite case      *)
(*  split on the literal first two prefix blocks (hPX2A here;        *)
(*  hPX2A0 / hPX2B0..6 / hPUSHX elsewhere, with mutually             *)
(*  different landing shapes) -- and (ii) the landing frame and      *)
(*  grind parameters, which are arithmetic accidents of the          *)
(*  specific prefix values (here 41 and 14 give frame 13 and         *)
(*  g0 = 39, whose continuation decomposes as LOOPN 12 +             *)
(*  DIPDESC 12 + hGRIND_even 14).  A general closure would be a      *)
(*  totality/landing theorem for the deviation-inclusive grind       *)
(*  relation over arbitrary prefixes -- a strictly larger            *)
(*  theorem than any single phase.  Each phase is therefore a        *)
(*  finite extension; this one reaches R <= 602.                     *)
(*                                                                   *)
(*  All forms pre-verified in rocq/hsim38.py: DIPDESC and LOOPN      *)
(*  word boundaries at small parameters, GRIND39 word boundaries     *)
(*  at (spine, beta) in {(0, 2), (2, 2), (3, 3)} (98,338 rules)      *)
(*  with word/machine boundary agreement at (0, 2) (1,180,078        *)
(*  machine steps), shrunk analogues of the m = 113 / m = 114 /      *)
(*  transitional / BIG6 finishes, and the hPX2A dispatch at the      *)
(*  phase-6 dip shape.                                               *)
(* ================================================================= *)

Require Import List Bool Arith Lia ZArith.
Import ListNotations.
Require Import TM Sections Mirror TokenPass Recoord Era Esc Dev
               Grind Grind2 Grind3 Grind4 Grind5 Grind6.

Ltac sec_eq := repeat (first [ solve [reflexivity] | solve [lia]
                             | f_equal ]).

(* ----------------------------------------------------------------- *)
(* Part 1: LOOPN -- the truncated grind loop.                        *)
(*                                                                   *)
(* hGRIND's internal loop (Grind2.v, a local assert) runs the        *)
(* countdown to (1, 2); the boundary analyses need the partial       *)
(* form: cnt iterations of (hGRIND i + hTUP), grinding the gap       *)
(* 2i + 3 up and the passenger pair g down by 2 each time.  The      *)
(* only floor is the sub-grinds': i + cnt <= a2.                     *)
(* ----------------------------------------------------------------- *)

Lemma LOOPN : forall cnt i pb a2 g P G,
  i + cnt <= a2 -> 2 * cnt + 1 <= g ->
  hsteps (HC pb a2 (2*i + 3) 2 ((g, 2) :: P) G)
         (HC pb a2 (2*(i + cnt) + 3) 2 ((g - 2*cnt, 2) :: P) G).
Proof.
  induction cnt as [|cnt IH]; intros i pb a2 g P G Hfloor Hg.
  - replace (2 * (i + 0) + 3) with (2 * i + 3) by lia.
    replace (g - 2 * 0) with g by lia.
    apply hsteps_refl.
  - apply (hsteps_trans _ (HB pb a2 1 (2*i + 6) ((g, 2) :: P) G)).
    { apply (hGRIND i pb a2 ((g, 2) :: P) G); lia. }
    apply (hsteps_trans _ (HC pb a2 (2*(i + 1) + 3) 2
                             ((g - 2, 2) :: P) G)).
    { apply (hsteps_step _ (HC pb a2 (2*(i + 1) + 3) 2
                              ((g - 2, 2) :: P) G)).
      { replace (HB pb a2 1 (2*i + 6) ((g, 2) :: P) G)
          with (HB pb a2 1 (S (S (2*i + 4)))
                  ((S (S (S (g - 3))), 2) :: P) G) by sec_eq.
        replace (HC pb a2 (2*(i + 1) + 3) 2 ((g - 2, 2) :: P) G)
          with (HC pb a2 (S (2*i + 4)) 2 ((S (g - 3), 2) :: P) G)
          by sec_eq.
        apply hTUP. }
      apply hsteps_refl. }
    replace (2 * (i + S cnt) + 3) with (2 * (i + 1 + cnt) + 3)
      by lia.
    replace (g - 2 * S cnt) with ((g - 2) - 2 * cnt) by lia.
    apply IH; lia.
Qed.

(* ----------------------------------------------------------------- *)
(* Part 2: DIPDESC -- the boundary descent at t = a2.                *)
(*                                                                   *)
(* The clean grind hGRIND t needs t + 1 <= a2; the deviated grind    *)
(* hGRIND_dev0 lives at pb = [0].  The third boundary form is the    *)
(* grind at exactly t = a2, at an arbitrary prefix: its loop is      *)
(* frame-truncated (LOOPN with cnt = a2 - 1 iterations grinds the    *)
(* pushed pair (2t - 1, 2) exactly to (1, 2)), and the recursion      *)
(* descends level by level to the dip HC pb 0 3 2 with the stack     *)
(* grown by one (1, 2) per level.  No floor hypothesis: the          *)
(* statement is the recursion's own fixed point.                     *)
(* ----------------------------------------------------------------- *)

Lemma repeat_snoc12 : forall n (P : list (nat * nat)),
  repeat (1, 2) n ++ ((1, 2) :: P) = repeat (1, 2) (S n) ++ P.
Proof.
  induction n as [|n IH]; intros P.
  - reflexivity.
  - simpl. rewrite IH. reflexivity.
Qed.

Lemma DIPDESC : forall t pb P G,
  hsteps (HC pb t (2*t + 3) 2 P G)
         (HC pb 0 3 2 (repeat (1, 2) t ++ P) G).
Proof.
  induction t as [|u IH]; intros pb P G.
  - apply hsteps_refl.
  - apply (hsteps_trans _ (HC pb u 1 2 ((2*u + 3, 2) :: P) G)).
    { apply (hsteps_step _ (HC pb u 1 2 ((2*u + 3, 2) :: P) G)).
      { replace (HC pb (S u) (2 * S u + 3) 2 P G)
          with (HC pb (S u) (S (S (S (2*u + 2)))) 2 P G) by sec_eq.
        replace (HC pb u 1 2 ((2*u + 3, 2) :: P) G)
          with (HC pb u 1 2 ((S (2*u + 2), 2) :: P) G) by sec_eq.
        apply hPUSH. }
      apply hsteps_refl. }
    apply (hsteps_trans _ (HB pb u 1 4 ((2*u + 3, 2) :: P) G)).
    { apply (hsteps_step _ (HB pb u 1 4 ((2*u + 3, 2) :: P) G)).
      { apply hTDN. }
      apply hsteps_refl. }
    apply (hsteps_trans _ (HC pb u 3 2 ((2*u + 1, 2) :: P) G)).
    { apply (hsteps_step _ (HC pb u 3 2 ((2*u + 1, 2) :: P) G)).
      { replace (HB pb u 1 4 ((2*u + 3, 2) :: P) G)
          with (HB pb u 1 (S (S 2)) ((S (S (S (2*u))), 2) :: P) G)
          by sec_eq.
        replace (HC pb u 3 2 ((2*u + 1, 2) :: P) G)
          with (HC pb u (S 2) 2 ((S (2*u), 2) :: P) G) by sec_eq.
        apply hTUP. }
      apply hsteps_refl. }
    apply (hsteps_trans _ (HC pb u (2*u + 3) 2 ((1, 2) :: P) G)).
    { replace (HC pb u 3 2 ((2*u + 1, 2) :: P) G)
        with (HC pb u (2*0 + 3) 2 ((2*u + 1, 2) :: P) G) by sec_eq.
      replace (HC pb u (2*u + 3) 2 ((1, 2) :: P) G)
        with (HC pb u (2*(0 + u) + 3) 2
                (((2*u + 1) - 2*u, 2) :: P) G) by sec_eq.
      apply (LOOPN u 0 pb u (2*u + 1) P G); lia. }
    replace (repeat (1, 2) (S u) ++ P)
      with (repeat (1, 2) u ++ ((1, 2) :: P))
      by apply repeat_snoc12.
    apply IH.
Qed.

(* ----------------------------------------------------------------- *)
(* Part 3: GRIND39_MID -- the continuation grind at ([5], 13),       *)
(* g0 = 39, over an arbitrary carried rest.  Segment boundaries      *)
(* are the hsim38.py walk: PUSH/TDN/TUP, LOOPN 12, DIPDESC 12        *)
(* (the segment's own dip), hPX2B5, POP x15, hTUP, hGRIND_even 14,   *)
(* hTUP2_1, grind_prefix, grind_round 1, grind_round 2, POP x4       *)
(* and the spine POP chain.                                          *)
(* ----------------------------------------------------------------- *)

Lemma GRIND39_MID : forall n Rest,
  hsteps (HC [5] 13 39 2
            ((1, 1) :: (1, 2) :: (1, 2)
             :: repeat (1, 2) n ++ Rest) 1)
         (HB [19; 0] (36 + n) 1 (17 + 2*n) Rest 1).
Proof.
  intros n Rest.
  (* PUSH *)
  apply (hsteps_trans _ (HC [5] 12 1 2 ((37, 2)
      :: (1, 1) :: (1, 2) :: (1, 2)
         :: repeat (1, 2) n ++ Rest) 1)).
  { apply (hsteps_step _ (HC [5] 12 1 2 ((37, 2)
        :: (1, 1) :: (1, 2) :: (1, 2)
           :: repeat (1, 2) n ++ Rest) 1)).
    { replace (HC [5] 13 39 2
                ((1, 1) :: (1, 2) :: (1, 2)
                 :: repeat (1, 2) n ++ Rest) 1)
        with (HC [5] (S 12) (S (S (S 36))) 2
                ((1, 1) :: (1, 2) :: (1, 2)
                 :: repeat (1, 2) n ++ Rest) 1) by sec_eq.
      replace (HC [5] 12 1 2 ((37, 2)
                :: (1, 1) :: (1, 2) :: (1, 2)
                   :: repeat (1, 2) n ++ Rest) 1)
        with (HC [5] 12 1 2 ((S 36, 2)
                :: (1, 1) :: (1, 2) :: (1, 2)
                   :: repeat (1, 2) n ++ Rest) 1) by sec_eq.
      apply hPUSH. }
    apply hsteps_refl. }
  (* TDN *)
  apply (hsteps_trans _ (HB [5] 12 1 4 ((37, 2)
      :: (1, 1) :: (1, 2) :: (1, 2)
         :: repeat (1, 2) n ++ Rest) 1)).
  { apply (hsteps_step _ (HB [5] 12 1 4 ((37, 2)
        :: (1, 1) :: (1, 2) :: (1, 2)
           :: repeat (1, 2) n ++ Rest) 1)).
    { apply hTDN. }
    apply hsteps_refl. }
  (* TUP *)
  apply (hsteps_trans _ (HC [5] 12 3 2 ((35, 2)
      :: (1, 1) :: (1, 2) :: (1, 2)
         :: repeat (1, 2) n ++ Rest) 1)).
  { apply (hsteps_step _ (HC [5] 12 3 2 ((35, 2)
        :: (1, 1) :: (1, 2) :: (1, 2)
           :: repeat (1, 2) n ++ Rest) 1)).
    { replace (HB [5] 12 1 4 ((37, 2)
                :: (1, 1) :: (1, 2) :: (1, 2)
                   :: repeat (1, 2) n ++ Rest) 1)
        with (HB [5] 12 1 (S (S 2)) ((S (S (S 34)), 2)
                :: (1, 1) :: (1, 2) :: (1, 2)
                   :: repeat (1, 2) n ++ Rest) 1) by sec_eq.
      replace (HC [5] 12 3 2 ((35, 2)
                :: (1, 1) :: (1, 2) :: (1, 2)
                   :: repeat (1, 2) n ++ Rest) 1)
        with (HC [5] 12 (S 2) 2 ((S 34, 2)
                :: (1, 1) :: (1, 2) :: (1, 2)
                   :: repeat (1, 2) n ++ Rest) 1) by sec_eq.
      apply hTUP. }
    apply hsteps_refl. }
  (* LOOPN 12 *)
  apply (hsteps_trans _ (HC [5] 12 27 2 ((11, 2)
      :: (1, 1) :: (1, 2) :: (1, 2)
         :: repeat (1, 2) n ++ Rest) 1)).
  { replace (HC [5] 12 3 2 ((35, 2)
              :: (1, 1) :: (1, 2) :: (1, 2)
                 :: repeat (1, 2) n ++ Rest) 1)
      with (HC [5] 12 (2*0 + 3) 2 ((35, 2)
              :: (1, 1) :: (1, 2) :: (1, 2)
                 :: repeat (1, 2) n ++ Rest) 1) by sec_eq.
    replace (HC [5] 12 27 2 ((11, 2)
              :: (1, 1) :: (1, 2) :: (1, 2)
                 :: repeat (1, 2) n ++ Rest) 1)
      with (HC [5] 12 (2*(0 + 12) + 3) 2 ((35 - 2*12, 2)
              :: (1, 1) :: (1, 2) :: (1, 2)
                 :: repeat (1, 2) n ++ Rest) 1) by sec_eq.
    apply (LOOPN 12 0 [5] 12 35
             ((1, 1) :: (1, 2) :: (1, 2)
              :: repeat (1, 2) n ++ Rest) 1); lia. }
  (* DIPDESC 12 *)
  apply (hsteps_trans _ (HC [5] 0 3 2
      (repeat (1, 2) 12 ++ ((11, 2)
        :: (1, 1) :: (1, 2) :: (1, 2)
           :: repeat (1, 2) n ++ Rest)) 1)).
  { apply (DIPDESC 12 [5] ((11, 2)
             :: (1, 1) :: (1, 2) :: (1, 2)
                :: repeat (1, 2) n ++ Rest) 1). }
  (* PX2B5 *)
  apply (hsteps_trans _ (HB [0] 4 1 4
      ((1, 1) :: (1, 2) :: (1, 2)
       :: repeat (1, 2) 12 ++ ((11, 2)
        :: (1, 1) :: (1, 2) :: (1, 2)
           :: repeat (1, 2) n ++ Rest)) 1)).
  { apply (hsteps_step _ (HB [0] 4 1 4
        ((1, 1) :: (1, 2) :: (1, 2)
         :: repeat (1, 2) 12 ++ ((11, 2)
          :: (1, 1) :: (1, 2) :: (1, 2)
             :: repeat (1, 2) n ++ Rest)) 1)).
    { apply hPX2B5. }
    apply hsteps_refl. }
  (* POP (1, 1) *)
  apply (hsteps_trans _ (HB [0] 5 1 5
      ((1, 2) :: (1, 2)
       :: repeat (1, 2) 12 ++ ((11, 2)
        :: (1, 1) :: (1, 2) :: (1, 2)
           :: repeat (1, 2) n ++ Rest)) 1)).
  { apply (hsteps_step _ (HB [0] 5 1 5
        ((1, 2) :: (1, 2)
         :: repeat (1, 2) 12 ++ ((11, 2)
          :: (1, 1) :: (1, 2) :: (1, 2)
             :: repeat (1, 2) n ++ Rest)) 1)).
    { replace (HB [0] 5 1 5
                ((1, 2) :: (1, 2)
                 :: repeat (1, 2) 12 ++ ((11, 2)
                  :: (1, 1) :: (1, 2) :: (1, 2)
                     :: repeat (1, 2) n ++ Rest)) 1)
        with (HB [0] (S 4) 1 (4 + 1)
                ((1, 2) :: (1, 2)
                 :: repeat (1, 2) 12 ++ ((11, 2)
                  :: (1, 1) :: (1, 2) :: (1, 2)
                     :: repeat (1, 2) n ++ Rest)) 1) by sec_eq.
      apply hPOP; lia. }
    apply hsteps_refl. }
  (* pop_chain_h_app 14 *)
  apply (hsteps_trans _ (HB [0] 19 1 33 ((11, 2)
      :: (1, 1) :: (1, 2) :: (1, 2)
         :: repeat (1, 2) n ++ Rest) 1)).
  { replace (HB [0] 5 1 5
              ((1, 2) :: (1, 2)
               :: repeat (1, 2) 12 ++ ((11, 2)
                :: (1, 1) :: (1, 2) :: (1, 2)
                   :: repeat (1, 2) n ++ Rest)) 1)
      with (HB [0] 5 1 5
              (repeat (1, 2) 14 ++ ((11, 2)
               :: (1, 1) :: (1, 2) :: (1, 2)
                  :: repeat (1, 2) n ++ Rest)) 1) by sec_eq.
    replace (HB [0] 19 1 33 ((11, 2)
              :: (1, 1) :: (1, 2) :: (1, 2)
                 :: repeat (1, 2) n ++ Rest) 1)
      with (HB [0] (5 + 14) 1 (5 + 2*14) ((11, 2)
              :: (1, 1) :: (1, 2) :: (1, 2)
                 :: repeat (1, 2) n ++ Rest) 1) by sec_eq.
    apply pop_chain_h_app; lia. }
  (* TUP *)
  apply (hsteps_trans _ (HC [0] 19 32 2 ((9, 2)
      :: (1, 1) :: (1, 2) :: (1, 2)
         :: repeat (1, 2) n ++ Rest) 1)).
  { apply (hsteps_step _ (HC [0] 19 32 2 ((9, 2)
        :: (1, 1) :: (1, 2) :: (1, 2)
           :: repeat (1, 2) n ++ Rest) 1)).
    { replace (HB [0] 19 1 33 ((11, 2)
                :: (1, 1) :: (1, 2) :: (1, 2)
                   :: repeat (1, 2) n ++ Rest) 1)
        with (HB [0] 19 1 (S (S 31)) ((S (S (S 8)), 2)
                :: (1, 1) :: (1, 2) :: (1, 2)
                   :: repeat (1, 2) n ++ Rest) 1) by sec_eq.
      replace (HC [0] 19 32 2 ((9, 2)
                :: (1, 1) :: (1, 2) :: (1, 2)
                   :: repeat (1, 2) n ++ Rest) 1)
        with (HC [0] 19 (S 31) 2 ((S 8, 2)
                :: (1, 1) :: (1, 2) :: (1, 2)
                   :: repeat (1, 2) n ++ Rest) 1) by sec_eq.
      apply hTUP. }
    apply hsteps_refl. }
  (* hGRIND_even 14 *)
  apply (hsteps_trans _ (HB [0] 18 1 32 ((2, 2) :: (9, 2)
      :: (1, 1) :: (1, 2) :: (1, 2)
         :: repeat (1, 2) n ++ Rest) 1)).
  { replace (HC [0] 19 32 2 ((9, 2)
              :: (1, 1) :: (1, 2) :: (1, 2)
                 :: repeat (1, 2) n ++ Rest) 1)
      with (HC [0] (S 18) (2*14 + 4) 2 ((9, 2)
              :: (1, 1) :: (1, 2) :: (1, 2)
                 :: repeat (1, 2) n ++ Rest) 1) by sec_eq.
    replace (HB [0] 18 1 32 ((2, 2) :: (9, 2)
              :: (1, 1) :: (1, 2) :: (1, 2)
                 :: repeat (1, 2) n ++ Rest) 1)
      with (HB [0] 18 1 (2*14 + 4) ((2, 2) :: (9, 2)
              :: (1, 1) :: (1, 2) :: (1, 2)
                 :: repeat (1, 2) n ++ Rest) 1) by sec_eq.
    apply hGRIND_even; lia. }
  (* TUP2_1 *)
  apply (hsteps_trans _ (HC [19; 0] 32 1 2 ((7, 2)
      :: (1, 1) :: (1, 2) :: (1, 2)
         :: repeat (1, 2) n ++ Rest) 1)).
  { apply (hsteps_step _ (HC [19; 0] 32 1 2 ((7, 2)
        :: (1, 1) :: (1, 2) :: (1, 2)
           :: repeat (1, 2) n ++ Rest) 1)).
    { replace (HB [0] 18 1 32 ((2, 2) :: (9, 2)
                :: (1, 1) :: (1, 2) :: (1, 2)
                   :: repeat (1, 2) n ++ Rest) 1)
        with (HB [0] 18 1 (S 31)
                ((2, S (S 0)) :: (S (S (S 6)), 2)
                 :: (1, 1) :: (1, 2) :: (1, 2)
                    :: repeat (1, 2) n ++ Rest) 1) by sec_eq.
      replace (HC [19; 0] 32 1 2 ((7, 2)
                :: (1, 1) :: (1, 2) :: (1, 2)
                   :: repeat (1, 2) n ++ Rest) 1)
        with (HC (S 18 :: [0]) (S 31) (S 0) 2 ((S 6, 2)
                :: (1, 1) :: (1, 2) :: (1, 2)
                   :: repeat (1, 2) n ++ Rest) 1) by sec_eq.
      apply hTUP2_1. }
    apply hsteps_refl. }
  (* grind_prefix *)
  apply (hsteps_trans _ (HB [19; 0] 32 1 6 ((5, 2)
      :: (1, 1) :: (1, 2) :: (1, 2)
         :: repeat (1, 2) n ++ Rest) 1)).
  { replace (HC [19; 0] 32 1 2 ((7, 2)
              :: (1, 1) :: (1, 2) :: (1, 2)
                 :: repeat (1, 2) n ++ Rest) 1)
      with (HC [19; 0] (S 31) 1 2 ((S (S (S 4)), 2)
              :: (1, 1) :: (1, 2) :: (1, 2)
                 :: repeat (1, 2) n ++ Rest) 1) by sec_eq.
    replace (HB [19; 0] 32 1 6 ((5, 2)
              :: (1, 1) :: (1, 2) :: (1, 2)
                 :: repeat (1, 2) n ++ Rest) 1)
      with (HB [19; 0] (S 31) 1 6 ((S 4, 2)
              :: (1, 1) :: (1, 2) :: (1, 2)
                 :: repeat (1, 2) n ++ Rest) 1) by sec_eq.
    apply grind_prefix. }
  (* grind_round 1 *)
  apply (hsteps_trans _ (HB [19; 0] 32 1 8 ((3, 2)
      :: (1, 1) :: (1, 2) :: (1, 2)
         :: repeat (1, 2) n ++ Rest) 1)).
  { replace (HB [19; 0] 32 1 6 ((5, 2)
              :: (1, 1) :: (1, 2) :: (1, 2)
                 :: repeat (1, 2) n ++ Rest) 1)
      with (HB [19; 0] 32 1 (2*1 + 4) ((5, 2)
              :: (1, 1) :: (1, 2) :: (1, 2)
                 :: repeat (1, 2) n ++ Rest) 1) by sec_eq.
    replace (HB [19; 0] 32 1 8 ((3, 2)
              :: (1, 1) :: (1, 2) :: (1, 2)
                 :: repeat (1, 2) n ++ Rest) 1)
      with (HB [19; 0] 32 1 (2*1 + 6) ((5 - 2, 2)
              :: (1, 1) :: (1, 2) :: (1, 2)
                 :: repeat (1, 2) n ++ Rest) 1) by sec_eq.
    apply grind_round; lia. }
  (* grind_round 2 *)
  apply (hsteps_trans _ (HB [19; 0] 32 1 10 ((1, 2)
      :: (1, 1) :: (1, 2) :: (1, 2)
         :: repeat (1, 2) n ++ Rest) 1)).
  { replace (HB [19; 0] 32 1 8 ((3, 2)
              :: (1, 1) :: (1, 2) :: (1, 2)
                 :: repeat (1, 2) n ++ Rest) 1)
      with (HB [19; 0] 32 1 (2*2 + 4) ((3, 2)
              :: (1, 1) :: (1, 2) :: (1, 2)
                 :: repeat (1, 2) n ++ Rest) 1) by sec_eq.
    replace (HB [19; 0] 32 1 10 ((1, 2)
              :: (1, 1) :: (1, 2) :: (1, 2)
                 :: repeat (1, 2) n ++ Rest) 1)
      with (HB [19; 0] 32 1 (2*2 + 6) ((3 - 2, 2)
              :: (1, 1) :: (1, 2) :: (1, 2)
                 :: repeat (1, 2) n ++ Rest) 1) by sec_eq.
    apply grind_round; lia. }
  (* POP (1, 2): the ground pair *)
  apply (hsteps_trans _ (HB [19; 0] 33 1 12
      ((1, 1) :: (1, 2) :: (1, 2)
       :: repeat (1, 2) n ++ Rest) 1)).
  { apply (hsteps_step _ (HB [19; 0] 33 1 12
        ((1, 1) :: (1, 2) :: (1, 2)
         :: repeat (1, 2) n ++ Rest) 1)).
    { replace (HB [19; 0] 33 1 12
                ((1, 1) :: (1, 2) :: (1, 2)
                 :: repeat (1, 2) n ++ Rest) 1)
        with (HB [19; 0] (S 32) 1 (10 + 2)
                ((1, 1) :: (1, 2) :: (1, 2)
                 :: repeat (1, 2) n ++ Rest) 1) by sec_eq.
      apply hPOP; lia. }
    apply hsteps_refl. }
  (* POP (1, 1) *)
  apply (hsteps_trans _ (HB [19; 0] 34 1 13
      ((1, 2) :: (1, 2) :: repeat (1, 2) n ++ Rest) 1)).
  { apply (hsteps_step _ (HB [19; 0] 34 1 13
        ((1, 2) :: (1, 2) :: repeat (1, 2) n ++ Rest) 1)).
    { replace (HB [19; 0] 34 1 13
                ((1, 2) :: (1, 2) :: repeat (1, 2) n ++ Rest) 1)
        with (HB [19; 0] (S 33) 1 (12 + 1)
                ((1, 2) :: (1, 2) :: repeat (1, 2) n ++ Rest) 1)
        by sec_eq.
      apply hPOP; lia. }
    apply hsteps_refl. }
  (* POP (1, 2) *)
  apply (hsteps_trans _ (HB [19; 0] 35 1 15
      ((1, 2) :: repeat (1, 2) n ++ Rest) 1)).
  { apply (hsteps_step _ (HB [19; 0] 35 1 15
        ((1, 2) :: repeat (1, 2) n ++ Rest) 1)).
    { replace (HB [19; 0] 35 1 15
                ((1, 2) :: repeat (1, 2) n ++ Rest) 1)
        with (HB [19; 0] (S 34) 1 (13 + 2)
                ((1, 2) :: repeat (1, 2) n ++ Rest) 1) by sec_eq.
      apply hPOP; lia. }
    apply hsteps_refl. }
  (* POP (1, 2) *)
  apply (hsteps_trans _ (HB [19; 0] 36 1 17
      (repeat (1, 2) n ++ Rest) 1)).
  { apply (hsteps_step _ (HB [19; 0] 36 1 17
        (repeat (1, 2) n ++ Rest) 1)).
    { replace (HB [19; 0] 36 1 17 (repeat (1, 2) n ++ Rest) 1)
        with (HB [19; 0] (S 35) 1 (15 + 2)
                (repeat (1, 2) n ++ Rest) 1) by sec_eq.
      apply hPOP; lia. }
    apply hsteps_refl. }
  (* spine POP chain *)
  apply pop_chain_h_app; lia.
Qed.

(* ----------------------------------------------------------------- *)
(* Part 4: TAIL2 -- the TRANS2_2 tail.  At a B-section whose stack   *)
(* is ((2, 2) :: (2, 2) :: Pe) (the m = 113 landing), the closing    *)
(* transfer is hTRANS2_2, not hTRANS2_1: it prepends two blocks      *)
(* (S (S s0) and S a) and lands at a = 3, s = 3 over the             *)
(* (1, 2)^(beta - 1) remainder; the POP chain then reaches the       *)
(* REGEN source with a = beta + 2.                                   *)
(* ----------------------------------------------------------------- *)

Lemma TAIL2 : forall pb a s0 beta, 2 <= beta ->
  hsteps (HB pb a 1 (S s0)
            ((2, 2) :: (2, 2) :: (1, 1)
             :: repeat (1, 2) (beta - 1)) 1)
         (HB (S (S s0) :: S a :: pb) (beta + 2) 1
             (2 * beta + 1) [] 1).
Proof.
  intros pb a s0 beta Hb.
  apply (hsteps_trans _ (HB (S (S s0) :: S a :: pb) 3 1 3
                           (repeat (1, 2) (beta - 1)) 1)).
  { apply (hsteps_step _ (HB (S (S s0) :: S a :: pb) 3 1 3
                            (repeat (1, 2) (beta - 1)) 1)).
    { replace (HB pb a 1 (S s0)
                ((2, 2) :: (2, 2) :: (1, 1)
                 :: repeat (1, 2) (beta - 1)) 1)
        with (HB pb a 1 (S s0)
                ((2, S 1) :: (2, S 1) :: (1, 1)
                 :: repeat (1, 2) (beta - 1)) 1) by sec_eq.
      replace (HB (S (S s0) :: S a :: pb) 3 1 3
                (repeat (1, 2) (beta - 1)) 1)
        with (HB (S (S s0) :: S a :: pb) (S (S 1)) 1 (S 1 + 1)
                (repeat (1, 2) (beta - 1)) 1) by sec_eq.
      apply hTRANS2_2; lia. }
    apply hsteps_refl. }
  replace (beta + 2) with (3 + (beta - 1)) by lia.
  replace (2 * beta + 1) with (3 + 2 * (beta - 1)) by lia.
  apply pop_chain_h; lia.
Qed.

(* ----------------------------------------------------------------- *)
(* Part 5: PHASE6_PREFIX -- the common chain of the phase-6          *)
(* finishes: PHASE3_DEEP (Grind6.v) and the segment of               *)
(* ESC_TO_REGEN_BIG3 that follows it (TUP, hGRIND_even 35,           *)
(* hTUP2_1, hTDN), landing at the rounds source                      *)
(* HB [41; 14; 5] 74 1 4 ((2m - 72, 2) :: Pe).                       *)
(* ----------------------------------------------------------------- *)

Lemma PHASE6_PREFIX : forall m beta, 37 <= m -> 2 <= beta ->
  hsteps (HC [] 3 1 2
            ((2*m + 46, 2) :: (1, 1) :: repeat (1, 2) (beta - 1)) 1)
         (HB [41; 14; 5] 74 1 4
            ((2*m - 72, 2) :: (1, 1) :: repeat (1, 2) (beta - 1)) 1).
Proof.
  intros m beta Hm Hb.
  pose proof (PHASE3_DEEP m beta ltac:(lia) Hb) as H.
  apply (hsteps_trans _ (HB [14; 5] 41 1 75 ((2*m - 68, 2)
      :: (1, 1) :: repeat (1, 2) (beta - 1)) 1)); [exact H |].
  apply (hsteps_trans _ (HC [14; 5] 41 74 2 ((2*m - 70, 2)
      :: (1, 1) :: repeat (1, 2) (beta - 1)) 1)).
  { apply (hsteps_step _ (HC [14; 5] 41 74 2 ((2*m - 70, 2)
        :: (1, 1) :: repeat (1, 2) (beta - 1)) 1)).
    { replace (HB [14; 5] 41 1 75 ((2*m - 68, 2)
          :: (1, 1) :: repeat (1, 2) (beta - 1)) 1)
        with (HB [14; 5] 41 1 (S (S 73)) ((S (S (S (2*m - 71))), 2)
            :: (1, 1) :: repeat (1, 2) (beta - 1)) 1) by sec_eq.
      replace (HC [14; 5] 41 74 2 ((2*m - 70, 2)
          :: (1, 1) :: repeat (1, 2) (beta - 1)) 1)
        with (HC [14; 5] 41 (S 73) 2 ((S (2*m - 71), 2)
            :: (1, 1) :: repeat (1, 2) (beta - 1)) 1) by sec_eq.
      apply hTUP. }
    apply hsteps_refl. }
  apply (hsteps_trans _ (HB [14; 5] 40 1 74 ((2, 2) :: (2*m - 70, 2)
      :: (1, 1) :: repeat (1, 2) (beta - 1)) 1)).
  { replace (HC [14; 5] 41 74 2 ((2*m - 70, 2)
        :: (1, 1) :: repeat (1, 2) (beta - 1)) 1)
      with (HC [14; 5] (S 40) (2*35 + 4) 2 ((2*m - 70, 2)
          :: (1, 1) :: repeat (1, 2) (beta - 1)) 1) by sec_eq.
    replace (HB [14; 5] 40 1 74 ((2, 2) :: (2*m - 70, 2)
        :: (1, 1) :: repeat (1, 2) (beta - 1)) 1)
      with (HB [14; 5] 40 1 (2*35 + 4) ((2, 2) :: (2*m - 70, 2)
          :: (1, 1) :: repeat (1, 2) (beta - 1)) 1) by sec_eq.
    apply hGRIND_even; lia. }
  apply (hsteps_trans _ (HC [41; 14; 5] 74 1 2 ((2*m - 72, 2)
      :: (1, 1) :: repeat (1, 2) (beta - 1)) 1)).
  { apply (hsteps_step _ (HC [41; 14; 5] 74 1 2 ((2*m - 72, 2)
        :: (1, 1) :: repeat (1, 2) (beta - 1)) 1)).
    { replace (HB [14; 5] 40 1 74 ((2, 2) :: (2*m - 70, 2)
          :: (1, 1) :: repeat (1, 2) (beta - 1)) 1)
        with (HB [14; 5] 40 1 (S 73)
                ((2, S (S 0)) :: (S (S (S (2*m - 73))), 2)
                 :: (1, 1) :: repeat (1, 2) (beta - 1)) 1) by sec_eq.
      replace (HC [41; 14; 5] 74 1 2 ((2*m - 72, 2)
          :: (1, 1) :: repeat (1, 2) (beta - 1)) 1)
        with (HC (S 40 :: [14; 5]) (S 73) (S 0) 2
                ((S (2*m - 73), 2)
                 :: (1, 1) :: repeat (1, 2) (beta - 1)) 1) by sec_eq.
      apply hTUP2_1. }
    apply hsteps_refl. }
  apply (hsteps_trans _ (HB [41; 14; 5] 74 1 4 ((2*m - 72, 2)
      :: (1, 1) :: repeat (1, 2) (beta - 1)) 1)).
  { apply (hsteps_step _ (HB [41; 14; 5] 74 1 4 ((2*m - 72, 2)
        :: (1, 1) :: repeat (1, 2) (beta - 1)) 1)).
    { apply hTDN. }
    apply hsteps_refl. }
  apply hsteps_refl.
Qed.

(* ----------------------------------------------------------------- *)
(* Part 6: the phase-6 finishes.                                     *)
(*                                                                   *)
(* PHASE6_TO_MID factors the common chain for every m >= 112:        *)
(* PHASE6_PREFIX, the maximal 74 clean rounds (rounds_from4g,        *)
(* floor met exactly), the final TUP, the boundary final grind       *)
(* (DIPDESC 74 at [41; 14; 5]), hPX2A and GRIND39_MID, landing       *)
(* at HB [19; 0] 110 1 165 ((2m - 222, 2) :: Pe).                    *)
(* ----------------------------------------------------------------- *)

Lemma PHASE6_TO_MID : forall m beta, 112 <= m -> 2 <= beta ->
  hsteps (HC [] 3 1 2
            ((2*m + 46, 2) :: (1, 1) :: repeat (1, 2) (beta - 1)) 1)
         (HB [19; 0] 110 1 165
            ((2*m - 222, 2) :: (1, 1) :: repeat (1, 2) (beta - 1)) 1).
Proof.
  intros m beta Hm Hb.
  pose proof (PHASE6_PREFIX m beta ltac:(lia) Hb) as H.
  apply (hsteps_trans _ (HB [41; 14; 5] 74 1 4 ((2*m - 72, 2)
      :: (1, 1) :: repeat (1, 2) (beta - 1)) 1)); [exact H |].
  (* 74 clean rounds *)
  apply (hsteps_trans _ (HB [41; 14; 5] 74 1 152 ((2*m - 220, 2)
      :: (1, 1) :: repeat (1, 2) (beta - 1)) 1)).
  { replace (HB [41; 14; 5] 74 1 4 ((2*m - 72, 2)
        :: (1, 1) :: repeat (1, 2) (beta - 1)) 1)
      with (HB [41; 14; 5] 74 1 (2*0 + 4) ((2*m - 72, 2)
          :: (1, 1) :: repeat (1, 2) (beta - 1)) 1) by sec_eq.
    replace (HB [41; 14; 5] 74 1 152 ((2*m - 220, 2)
        :: (1, 1) :: repeat (1, 2) (beta - 1)) 1)
      with (HB [41; 14; 5] 74 1 (2*(0 + 74) + 4)
              ((2*m - 72 - 2*74, 2)
               :: (1, 1) :: repeat (1, 2) (beta - 1)) 1) by sec_eq.
    apply rounds_from4g; lia. }
  (* final TUP *)
  apply (hsteps_trans _ (HC [41; 14; 5] 74 151 2 ((2*m - 222, 2)
      :: (1, 1) :: repeat (1, 2) (beta - 1)) 1)).
  { apply (hsteps_step _ (HC [41; 14; 5] 74 151 2 ((2*m - 222, 2)
        :: (1, 1) :: repeat (1, 2) (beta - 1)) 1)).
    { replace (HB [41; 14; 5] 74 1 152 ((2*m - 220, 2)
          :: (1, 1) :: repeat (1, 2) (beta - 1)) 1)
        with (HB [41; 14; 5] 74 1 (S (S 150))
                ((S (S (S (2*m - 223))), 2)
                 :: (1, 1) :: repeat (1, 2) (beta - 1)) 1) by sec_eq.
      replace (HC [41; 14; 5] 74 151 2 ((2*m - 222, 2)
          :: (1, 1) :: repeat (1, 2) (beta - 1)) 1)
        with (HC [41; 14; 5] 74 (S 150) 2 ((S (2*m - 223), 2)
            :: (1, 1) :: repeat (1, 2) (beta - 1)) 1) by sec_eq.
      apply hTUP. }
    apply hsteps_refl. }
  (* boundary final grind: DIPDESC 74 *)
  apply (hsteps_trans _ (HC [41; 14; 5] 0 3 2
      (repeat (1, 2) 74 ++ ((2*m - 222, 2)
        :: (1, 1) :: repeat (1, 2) (beta - 1))) 1)).
  { apply (DIPDESC 74 [41; 14; 5] ((2*m - 222, 2)
             :: (1, 1) :: repeat (1, 2) (beta - 1)) 1). }
  (* hPX2A *)
  apply (hsteps_trans _ (HC [5] 13 39 2
      ((1, 1) :: (1, 2) :: (1, 2)
       :: repeat (1, 2) 74 ++ ((2*m - 222, 2)
        :: (1, 1) :: repeat (1, 2) (beta - 1))) 1)).
  { apply (hsteps_step _ (HC [5] 13 39 2
        ((1, 1) :: (1, 2) :: (1, 2)
         :: repeat (1, 2) 74 ++ ((2*m - 222, 2)
          :: (1, 1) :: repeat (1, 2) (beta - 1))) 1)).
    { replace (HC [41; 14; 5] 0 3 2
                (repeat (1, 2) 74 ++ ((2*m - 222, 2)
                 :: (1, 1) :: repeat (1, 2) (beta - 1))) 1)
        with (HC (S (S (S 38)) :: S 13 :: [5]) 0 3 2
                (repeat (1, 2) 74 ++ ((2*m - 222, 2)
                 :: (1, 1) :: repeat (1, 2) (beta - 1))) 1) by sec_eq.
      replace (HC [5] 13 39 2
                ((1, 1) :: (1, 2) :: (1, 2)
                 :: repeat (1, 2) 74 ++ ((2*m - 222, 2)
                  :: (1, 1) :: repeat (1, 2) (beta - 1))) 1)
        with (HC [5] 13 (S 38) 2
                ((1, 1) :: (1, 2) :: (1, 2)
                 :: repeat (1, 2) 74 ++ ((2*m - 222, 2)
                  :: (1, 1) :: repeat (1, 2) (beta - 1))) 1)
        by sec_eq.
      apply hPX2A. }
    apply hsteps_refl. }
  (* GRIND39_MID *)
  replace (HB [19; 0] 110 1 165 ((2*m - 222, 2)
            :: (1, 1) :: repeat (1, 2) (beta - 1)) 1)
    with (HB [19; 0] (36 + 74) 1 (17 + 2*74) ((2*m - 222, 2)
            :: (1, 1) :: repeat (1, 2) (beta - 1)) 1) by sec_eq.
  apply (GRIND39_MID 74 ((2*m - 222, 2)
           :: (1, 1) :: repeat (1, 2) (beta - 1))).
Qed.

(* m = 112 (R = 270): the residue is already (2, 2); TAIL closes. *)
Lemma ESC_TO_REGEN_112 : forall beta, 2 <= beta ->
  exists pb a,
    hsteps (HC [] 3 1 2
              ((270, 2) :: (1, 1) :: repeat (1, 2) (beta - 1)) 1)
           (HB pb a 1 (2 * beta + 1) [] 1) /\ beta <= a.
Proof.
  intros beta Hb.
  pose proof (PHASE6_TO_MID 112 beta ltac:(lia) Hb) as H.
  exists [111; 19; 0], (165 + beta). split; [| lia].
  apply (hsteps_trans _ (HB [19; 0] 110 1 165 ((2, 2)
      :: (1, 1) :: repeat (1, 2) (beta - 1)) 1)); [exact H |].
  replace (HB [111; 19; 0] (165 + beta) 1 (2 * beta + 1) [] 1)
    with (HB (S 110 :: [19; 0]) (165 + beta) 1 (2 * beta + 1) [] 1)
    by sec_eq.
  apply TAIL; lia.
Qed.

(* m = 113 (R = 272): one transitional round, then the TRANS2_2    *)
(* tail at the ((2, 2) :: (2, 2) :: Pe) landing.                     *)
Lemma ESC_TO_REGEN_113 : forall beta, 2 <= beta ->
  exists pb a,
    hsteps (HC [] 3 1 2
              ((272, 2) :: (1, 1) :: repeat (1, 2) (beta - 1)) 1)
           (HB pb a 1 (2 * beta + 1) [] 1) /\ beta <= a.
Proof.
  intros beta Hb.
  pose proof (PHASE6_TO_MID 113 beta ltac:(lia) Hb) as H.
  exists [165; 110; 19; 0], (beta + 2). split; [| lia].
  apply (hsteps_trans _ (HB [19; 0] 110 1 165 ((4, 2)
      :: (1, 1) :: repeat (1, 2) (beta - 1)) 1)); [exact H |].
  (* TUP *)
  apply (hsteps_trans _ (HC [19; 0] 110 164 2 ((2, 2)
      :: (1, 1) :: repeat (1, 2) (beta - 1)) 1)).
  { apply (hsteps_step _ (HC [19; 0] 110 164 2 ((2, 2)
        :: (1, 1) :: repeat (1, 2) (beta - 1)) 1)).
    { replace (HB [19; 0] 110 1 165 ((4, 2)
          :: (1, 1) :: repeat (1, 2) (beta - 1)) 1)
        with (HB [19; 0] 110 1 (S (S 163)) ((S (S (S 1)), 2)
            :: (1, 1) :: repeat (1, 2) (beta - 1)) 1) by sec_eq.
      replace (HC [19; 0] 110 164 2 ((2, 2)
          :: (1, 1) :: repeat (1, 2) (beta - 1)) 1)
        with (HC [19; 0] 110 (S 163) 2 ((S 1, 2)
            :: (1, 1) :: repeat (1, 2) (beta - 1)) 1) by sec_eq.
      apply hTUP. }
    apply hsteps_refl. }
  (* hGRIND_even 80 *)
  apply (hsteps_trans _ (HB [19; 0] 109 1 164 ((2, 2) :: (2, 2)
      :: (1, 1) :: repeat (1, 2) (beta - 1)) 1)).
  { replace (HC [19; 0] 110 164 2 ((2, 2)
        :: (1, 1) :: repeat (1, 2) (beta - 1)) 1)
      with (HC [19; 0] (S 109) (2*80 + 4) 2 ((2, 2)
          :: (1, 1) :: repeat (1, 2) (beta - 1)) 1) by sec_eq.
    replace (HB [19; 0] 109 1 164 ((2, 2) :: (2, 2)
        :: (1, 1) :: repeat (1, 2) (beta - 1)) 1)
      with (HB [19; 0] 109 1 (2*80 + 4) ((2, 2) :: (2, 2)
          :: (1, 1) :: repeat (1, 2) (beta - 1)) 1) by sec_eq.
    apply hGRIND_even; lia. }
  (* TAIL2 *)
  apply (TAIL2 [19; 0] 109 163 beta Hb).
Qed.

(* m = 114 (R = 274): the transitional round lands the residue at  *)
(* (2, 2) one frame deeper; TAIL closes.                             *)
Lemma ESC_TO_REGEN_114 : forall beta, 2 <= beta ->
  exists pb a,
    hsteps (HC [] 3 1 2
              ((274, 2) :: (1, 1) :: repeat (1, 2) (beta - 1)) 1)
           (HB pb a 1 (2 * beta + 1) [] 1) /\ beta <= a.
Proof.
  intros beta Hb.
  pose proof (PHASE6_TO_MID 114 beta ltac:(lia) Hb) as H.
  exists [165; 110; 19; 0], (4 + beta). split; [| lia].
  apply (hsteps_trans _ (HB [19; 0] 110 1 165 ((6, 2)
      :: (1, 1) :: repeat (1, 2) (beta - 1)) 1)); [exact H |].
  (* TUP *)
  apply (hsteps_trans _ (HC [19; 0] 110 164 2 ((4, 2)
      :: (1, 1) :: repeat (1, 2) (beta - 1)) 1)).
  { apply (hsteps_step _ (HC [19; 0] 110 164 2 ((4, 2)
        :: (1, 1) :: repeat (1, 2) (beta - 1)) 1)).
    { replace (HB [19; 0] 110 1 165 ((6, 2)
          :: (1, 1) :: repeat (1, 2) (beta - 1)) 1)
        with (HB [19; 0] 110 1 (S (S 163)) ((S (S (S 3)), 2)
            :: (1, 1) :: repeat (1, 2) (beta - 1)) 1) by sec_eq.
      replace (HC [19; 0] 110 164 2 ((4, 2)
          :: (1, 1) :: repeat (1, 2) (beta - 1)) 1)
        with (HC [19; 0] 110 (S 163) 2 ((S 3, 2)
            :: (1, 1) :: repeat (1, 2) (beta - 1)) 1) by sec_eq.
      apply hTUP. }
    apply hsteps_refl. }
  (* hGRIND_even 80 *)
  apply (hsteps_trans _ (HB [19; 0] 109 1 164 ((2, 2) :: (4, 2)
      :: (1, 1) :: repeat (1, 2) (beta - 1)) 1)).
  { replace (HC [19; 0] 110 164 2 ((4, 2)
        :: (1, 1) :: repeat (1, 2) (beta - 1)) 1)
      with (HC [19; 0] (S 109) (2*80 + 4) 2 ((4, 2)
          :: (1, 1) :: repeat (1, 2) (beta - 1)) 1) by sec_eq.
    replace (HB [19; 0] 109 1 164 ((2, 2) :: (4, 2)
        :: (1, 1) :: repeat (1, 2) (beta - 1)) 1)
      with (HB [19; 0] 109 1 (2*80 + 4) ((2, 2) :: (4, 2)
          :: (1, 1) :: repeat (1, 2) (beta - 1)) 1) by sec_eq.
    apply hGRIND_even; lia. }
  (* TUP2_1 *)
  apply (hsteps_trans _ (HC [110; 19; 0] 164 1 2 ((2, 2)
      :: (1, 1) :: repeat (1, 2) (beta - 1)) 1)).
  { apply (hsteps_step _ (HC [110; 19; 0] 164 1 2 ((2, 2)
        :: (1, 1) :: repeat (1, 2) (beta - 1)) 1)).
    { replace (HB [19; 0] 109 1 164 ((2, 2) :: (4, 2)
          :: (1, 1) :: repeat (1, 2) (beta - 1)) 1)
        with (HB [19; 0] 109 1 (S 163)
                ((2, S (S 0)) :: (S (S (S 1)), 2)
                 :: (1, 1) :: repeat (1, 2) (beta - 1)) 1) by sec_eq.
      replace (HC [110; 19; 0] 164 1 2 ((2, 2)
          :: (1, 1) :: repeat (1, 2) (beta - 1)) 1)
        with (HC (S 109 :: [19; 0]) (S 163) (S 0) 2 ((S 1, 2)
            :: (1, 1) :: repeat (1, 2) (beta - 1)) 1) by sec_eq.
      apply hTUP2_1. }
    apply hsteps_refl. }
  (* TDN *)
  apply (hsteps_trans _ (HB [110; 19; 0] 164 1 4 ((2, 2)
      :: (1, 1) :: repeat (1, 2) (beta - 1)) 1)).
  { apply (hsteps_step _ (HB [110; 19; 0] 164 1 4 ((2, 2)
        :: (1, 1) :: repeat (1, 2) (beta - 1)) 1)).
    { apply hTDN. }
    apply hsteps_refl. }
  (* TAIL *)
  replace (HB [165; 110; 19; 0] (4 + beta) 1 (2 * beta + 1) [] 1)
    with (HB (S 164 :: [110; 19; 0]) (4 + beta) 1
            (2 * beta + 1) [] 1) by sec_eq.
  apply TAIL; lia.
Qed.

(* 115 <= m <= 278 (R <= 602): the transitional round, then        *)
(* rounds at the new frame ([110; 19; 0], 164), the final clean    *)
(* grind and TAIL.                                                   *)
Lemma ESC_TO_REGEN_BIG6 : forall m beta,
  115 <= m -> m <= 278 -> 2 <= beta ->
  exists pb a,
    hsteps (HC [] 3 1 2
              ((2*m + 46, 2) :: (1, 1) :: repeat (1, 2) (beta - 1)) 1)
           (HB pb a 1 (2 * beta + 1) [] 1) /\ beta <= a.
Proof.
  intros m beta Hm1 Hm2 Hb.
  pose proof (PHASE6_TO_MID m beta ltac:(lia) Hb) as H.
  exists [165; 110; 19; 0], (2*m - 224 + beta). split; [| lia].
  apply (hsteps_trans _ (HB [19; 0] 110 1 165 ((2*m - 222, 2)
      :: (1, 1) :: repeat (1, 2) (beta - 1)) 1)); [exact H |].
  (* transitional round: TUP *)
  apply (hsteps_trans _ (HC [19; 0] 110 164 2 ((2*m - 224, 2)
      :: (1, 1) :: repeat (1, 2) (beta - 1)) 1)).
  { apply (hsteps_step _ (HC [19; 0] 110 164 2 ((2*m - 224, 2)
        :: (1, 1) :: repeat (1, 2) (beta - 1)) 1)).
    { replace (HB [19; 0] 110 1 165 ((2*m - 222, 2)
          :: (1, 1) :: repeat (1, 2) (beta - 1)) 1)
        with (HB [19; 0] 110 1 (S (S 163))
                ((S (S (S (2*m - 225))), 2)
                 :: (1, 1) :: repeat (1, 2) (beta - 1)) 1) by sec_eq.
      replace (HC [19; 0] 110 164 2 ((2*m - 224, 2)
          :: (1, 1) :: repeat (1, 2) (beta - 1)) 1)
        with (HC [19; 0] 110 (S 163) 2 ((S (2*m - 225), 2)
            :: (1, 1) :: repeat (1, 2) (beta - 1)) 1) by sec_eq.
      apply hTUP. }
    apply hsteps_refl. }
  (* transitional round: hGRIND_even 80 *)
  apply (hsteps_trans _ (HB [19; 0] 109 1 164
      ((2, 2) :: (2*m - 224, 2)
       :: (1, 1) :: repeat (1, 2) (beta - 1)) 1)).
  { replace (HC [19; 0] 110 164 2 ((2*m - 224, 2)
        :: (1, 1) :: repeat (1, 2) (beta - 1)) 1)
      with (HC [19; 0] (S 109) (2*80 + 4) 2 ((2*m - 224, 2)
          :: (1, 1) :: repeat (1, 2) (beta - 1)) 1) by sec_eq.
    replace (HB [19; 0] 109 1 164
        ((2, 2) :: (2*m - 224, 2)
         :: (1, 1) :: repeat (1, 2) (beta - 1)) 1)
      with (HB [19; 0] 109 1 (2*80 + 4)
              ((2, 2) :: (2*m - 224, 2)
               :: (1, 1) :: repeat (1, 2) (beta - 1)) 1) by sec_eq.
    apply hGRIND_even; lia. }
  (* transitional round: TUP2_1 *)
  apply (hsteps_trans _ (HC [110; 19; 0] 164 1 2 ((2*m - 226, 2)
      :: (1, 1) :: repeat (1, 2) (beta - 1)) 1)).
  { apply (hsteps_step _ (HC [110; 19; 0] 164 1 2 ((2*m - 226, 2)
        :: (1, 1) :: repeat (1, 2) (beta - 1)) 1)).
    { replace (HB [19; 0] 109 1 164
          ((2, 2) :: (2*m - 224, 2)
           :: (1, 1) :: repeat (1, 2) (beta - 1)) 1)
        with (HB [19; 0] 109 1 (S 163)
                ((2, S (S 0)) :: (S (S (S (2*m - 227))), 2)
                 :: (1, 1) :: repeat (1, 2) (beta - 1)) 1) by sec_eq.
      replace (HC [110; 19; 0] 164 1 2 ((2*m - 226, 2)
          :: (1, 1) :: repeat (1, 2) (beta - 1)) 1)
        with (HC (S 109 :: [19; 0]) (S 163) (S 0) 2
                ((S (2*m - 227), 2)
                 :: (1, 1) :: repeat (1, 2) (beta - 1)) 1) by sec_eq.
      apply hTUP2_1. }
    apply hsteps_refl. }
  (* TDN *)
  apply (hsteps_trans _ (HB [110; 19; 0] 164 1 4 ((2*m - 226, 2)
      :: (1, 1) :: repeat (1, 2) (beta - 1)) 1)).
  { apply (hsteps_step _ (HB [110; 19; 0] 164 1 4 ((2*m - 226, 2)
        :: (1, 1) :: repeat (1, 2) (beta - 1)) 1)).
    { apply hTDN. }
    apply hsteps_refl. }
  (* rounds at the new frame *)
  apply (hsteps_trans _ (HB [110; 19; 0] 164 1 (2*m - 226) ((4, 2)
      :: (1, 1) :: repeat (1, 2) (beta - 1)) 1)).
  { replace (HB [110; 19; 0] 164 1 4 ((2*m - 226, 2)
        :: (1, 1) :: repeat (1, 2) (beta - 1)) 1)
      with (HB [110; 19; 0] 164 1 (2*0 + 4) ((2*m - 226, 2)
          :: (1, 1) :: repeat (1, 2) (beta - 1)) 1) by sec_eq.
    replace (HB [110; 19; 0] 164 1 (2*m - 226) ((4, 2)
        :: (1, 1) :: repeat (1, 2) (beta - 1)) 1)
      with (HB [110; 19; 0] 164 1 (2*(0 + (m - 115)) + 4)
              ((2*m - 226 - 2*(m - 115), 2)
               :: (1, 1) :: repeat (1, 2) (beta - 1)) 1) by sec_eq.
    apply rounds_from4g; lia. }
  (* final TUP *)
  apply (hsteps_trans _ (HC [110; 19; 0] 164 (2*m - 227) 2 ((2, 2)
      :: (1, 1) :: repeat (1, 2) (beta - 1)) 1)).
  { apply (hsteps_step _ (HC [110; 19; 0] 164 (2*m - 227) 2 ((2, 2)
        :: (1, 1) :: repeat (1, 2) (beta - 1)) 1)).
    { replace (HB [110; 19; 0] 164 1 (2*m - 226) ((4, 2)
          :: (1, 1) :: repeat (1, 2) (beta - 1)) 1)
        with (HB [110; 19; 0] 164 1 (S (S (2*m - 228)))
                ((S (S (S 1)), 2)
                 :: (1, 1) :: repeat (1, 2) (beta - 1)) 1) by sec_eq.
      replace (HC [110; 19; 0] 164 (2*m - 227) 2 ((2, 2)
          :: (1, 1) :: repeat (1, 2) (beta - 1)) 1)
        with (HC [110; 19; 0] 164 (S (2*m - 228)) 2 ((S 1, 2)
            :: (1, 1) :: repeat (1, 2) (beta - 1)) 1) by sec_eq.
      apply hTUP. }
    apply hsteps_refl. }
  (* final grind *)
  apply (hsteps_trans _ (HB [110; 19; 0] 164 1 (2*m - 224) ((2, 2)
      :: (1, 1) :: repeat (1, 2) (beta - 1)) 1)).
  { replace (HC [110; 19; 0] 164 (2*m - 227) 2 ((2, 2)
        :: (1, 1) :: repeat (1, 2) (beta - 1)) 1)
      with (HC [110; 19; 0] 164 (2*(m - 115) + 3) 2 ((2, 2)
          :: (1, 1) :: repeat (1, 2) (beta - 1)) 1) by sec_eq.
    replace (HB [110; 19; 0] 164 1 (2*m - 224) ((2, 2)
        :: (1, 1) :: repeat (1, 2) (beta - 1)) 1)
      with (HB [110; 19; 0] 164 1 (2*(m - 115) + 6) ((2, 2)
          :: (1, 1) :: repeat (1, 2) (beta - 1)) 1) by sec_eq.
    apply hGRIND; lia. }
  (* TAIL *)
  replace (HB [165; 110; 19; 0] (2*m - 224 + beta) 1
             (2 * beta + 1) [] 1)
    with (HB (S 164 :: [110; 19; 0]) ((2*m - 224) + beta) 1
            (2 * beta + 1) [] 1) by sec_eq.
  apply TAIL; lia.
Qed.

(* ----------------------------------------------------------------- *)
(* Part 7: the ESC era law through R = 602.                          *)
(* ----------------------------------------------------------------- *)

Lemma ESC_ERA_LAW_38 : forall R beta,
  (R = 270 \/ R = 272 \/ R = 274
   \/ (exists m, R = 2 * m + 46 /\ 115 <= m <= 278)) ->
  2 <= beta ->
  exists n c pb a, run n (esc_src (R + 6) (beta - 2)) = Some c
    /\ cfg_sim c (rcsec (false :: repeat true (S a) ++ enc pb)
                        (2 * beta + 2) [(1, 2)])
    /\ beta <= a.
Proof.
  intros R beta HR Hb.
  destruct HR as [E | [E | [E | [m [ER Hm]]]]].
  - subst R.
    destruct (ESC_TO_REGEN_112 beta Hb) as [pb [a [Hc Hf]]].
    apply (ESC_ERA_LAW_of 270 beta pb a);
      [lia | exact Hc | exact Hf | exact Hb].
  - subst R.
    destruct (ESC_TO_REGEN_113 beta Hb) as [pb [a [Hc Hf]]].
    apply (ESC_ERA_LAW_of 272 beta pb a);
      [lia | exact Hc | exact Hf | exact Hb].
  - subst R.
    destruct (ESC_TO_REGEN_114 beta Hb) as [pb [a [Hc Hf]]].
    apply (ESC_ERA_LAW_of 274 beta pb a);
      [lia | exact Hc | exact Hf | exact Hb].
  - subst R.
    destruct (ESC_TO_REGEN_BIG6 m beta ltac:(lia) ltac:(lia) Hb)
      as [pb [a [Hc Hf]]].
    apply (ESC_ERA_LAW_of (2 * m + 46) beta pb a);
      [lia | exact Hc | exact Hf | exact Hb].
Qed.

Lemma ESC_ERA_LAW_602 : forall R beta,
  (((R = 2 \/ R = 4 \/ R = 6 \/ R = 8 \/ R = 10 \/ R = 12 \/ R = 14
    \/ (exists m, R = 2 * m + 16 /\ m <= 12)
    \/ R = 42 \/ R = 44 \/ (exists m, R = 2 * m + 46 /\ m <= 34))
   \/ (R = 116 \/ R = 118 \/ R = 120
       \/ (exists m, R = 2 * m + 46 /\ 38 <= m <= 111)))
   \/ (R = 270 \/ R = 272 \/ R = 274
       \/ (exists m, R = 2 * m + 46 /\ 115 <= m <= 278)))
  -> 2 <= beta ->
  exists n c pb a, run n (esc_src (R + 6) (beta - 2)) = Some c
    /\ cfg_sim c (rcsec (false :: repeat true (S a) ++ enc pb)
                        (2 * beta + 2) [(1, 2)])
    /\ beta <= a.
Proof.
  intros R beta [HOLD | HNEW] Hb.
  - apply (ESC_ERA_LAW_268 R beta); [exact HOLD | exact Hb].
  - apply (ESC_ERA_LAW_38 R beta); [exact HNEW | exact Hb].
Qed.

(* ----------------------------------------------------------------- *)
(* Print Assumptions audit (Phase 38): the headline lemmas must be   *)
(* closed under the global context.                                  *)
(* ----------------------------------------------------------------- *)

Print Assumptions ESC_ERA_LAW_602.
Print Assumptions DIPDESC.
Print Assumptions GRIND39_MID.
