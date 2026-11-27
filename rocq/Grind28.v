(* ================================================================= *)
(* Phase 60: the fourteenth descent of the TOP13 state, the        *)
(* TOP14 state and the residual core TAIL2_END15.                  *)
(*                                                                 *)
(* The phase-59 status doc left exactly one ESC-side core:         *)
(* TAIL2_END14, the totality of                                *)
(*   TOP13 = HB [7965811; 4012920; 308090; 49409; 7710; 1059;       *)
(*           199; 101; 0] 34304475 1 58806191 W                     *)
(* at r13' = 2 * j13, j13 >= 58806194 (TOP13 parameters).  This    *)
(* phase discharges it on a finite range and reduces it to the     *)
(* same statement one level down.  Method: the lemma-step          *)
(* classifier of phase55-work/classify.py, validated by exact      *)
(* reproduction of the phase-59 chain (594 steps, 0 mismatches)    *)
(* before any phase-60 use, then run at TOP13(58806194, beta)      *)
(* (rocq/hsim60.py, phase60-work/chain60f.py).                     *)
(*                                                                 *)
(* Characterisation (chains at (58806194, 2) and (58806194, 3)):   *)
(*   1. TOP13's front is UNIFORM in (j, beta): TUP +                *)
(*      hGRIND_even 29403093 + TUP2_1 + TDN + TUP lands on          *)
(*      GRIND14 = HC [34304475; 7965811; ...] 58806190 3 2          *)
(*      ((2j - 6, 2) :: tail(beta)); the DIPGRIND boundary round    *)
(*      (58806190, 2(j - 58806193)) lands on the DIP14 spine        *)
(*      repeat (1, 2) 58806190 ++ ((2(j - 58806193), 2) :: tail).   *)
(*   2. From the spine the walk follows a FIXED parse, independent *)
(*      of (j, beta) (the label sequence and the abstracted        *)
(*      targets at beta = 2 and beta = 3 agree at every one of      *)
(*      the 663 steps): CASCADE60, 663 lemma steps (the            *)
(*      CASCADE59 pattern, one level deeper and longer):          *)
(*      148 TUP, 97 TDN, 92 pop12, 66 DIPGRIND, 52 TUP2_1,          *)
(*      39 hGRIND_even, 38 PUSH, 26 PX2A, 26 POP, 17 PUSHX,         *)
(*      14 CLEANG_odd, 14 TRANS2_1, 10 PX2B0, 9 PX2Bgen,            *)
(*      9 CLEANG_even, 5 PX2A0, 1 hGRIND.  The frame is             *)
(*      REPLACED, not grown: nine blocks become nine:              *)
(*      -> TOP14 = HB [10126538; 1236011; 698173; 177445;           *)
(*         95640; 10129; 1243; 207; 19] 74737818 1 135985237 W.     *)
(*      (CASCADE60 is stated for an ARBITRARY tail w in            *)
(*      Grind28.v / Grind28j.v; hsim60.py Part 1b probes that      *)
(*      generality with a junk tail.)                              *)
(*   3. TOP14 closings by r14' = 2 * j14, j14 = j - 58806193:      *)
(*      r14' = 2:       TRANS2_1 + POPFIN, A = 135985237 + beta,    *)
(*                     frame [74737819; 10126538; ...].             *)
(*      r14' = 4:       TUP + hGRIND_even 67992616 + TRANS2_2       *)
(*                     + POPFIN, A = beta + 2,                      *)
(*                     frame [135985237; 74737818; 10126538; ...].  *)
(*      r14' = 6:       TUP + hGRIND_even 67992616 + TUP2_1         *)
(*                     + TDN + TRANS2_1 + POPFIN, A = beta + 4,     *)
(*                     frame as r14' = 4.                           *)
(*      8 <= r14' <= 271970478 (band 14): TUP + hGRIND_even         *)
(*                     67992616 + TUP2_1 + TDN + TUP -> GRIND15     *)
(*                     = HC [74737818; 10126538; ...] 135985236     *)
(*                     3 2 ((r14'-6, 2) :: tail(beta))  -- TUP2_1   *)
(*                     moves the shuttle 135985237 into the         *)
(*                     counter slot, so the band counter is         *)
(*                     135985236; CLEANG_even ((r14'-8)/2) (floor    *)
(*                     (r14'-8)/2 + 1 <= 135985236, exactly          *)
(*                     r14' <= 271970478); TRANS2_1 + POPFIN,       *)
(*                     A = r14' + beta - 2, frame as r14' = 4.      *)
(*      r14' >= 271970480: GRIND15's pair (r14'-6, 2) exceeds       *)
(*      the CLEANG_even floor; DIPGRIND (135985236,                 *)
(*      r14' - 271970478) landing occurs (asserted by hsim60.py     *)
(*      Part 3).  This is the residual core TAIL2_END15 (at         *)
(*      TOP14, r14' = 2*j14, j14 >= 135985240).                     *)
(*                                                                 *)
(* Band boundary: r14' <= 271970478  <=>  j <= 194791432 (TOP13     *)
(*                params)  <=>  j14 <= 135985239 (TOP14 params).    *)
(*                                                                 *)
(* File layout (compile-resident-set management at Phase 60        *)
(* numeral depths; host ceiling ~6 GB): the tiny Arith-only        *)
(* companions Grind28a.v (S60f/S60a1), Grind28b.v                   *)
(* (S60g1/S60g2; S60h0 and NUM60b in Grind28ae.v / Grind28af.v)    *)
(* and Grind28c.v (the S60r singleton  *)
(* identities of segments r/t and S60rv1) are proved in fresh      *)
(* processes.  At 136M scale every two-chain evaluated             *)
(* comparison OOMs (plain S-form eqb, the tail-recursive           *)
(* accumulator, the Phase 59 split + ring-reshape pattern:         *)
(* build-logs-60/probes.txt), so the remaining TOP14 identities    *)
(* take two single-chain forms: the S-identities are carried in    *)
(* (V - 1) form via Nat.succ_pred_pos (Grind28q.v NUM60e',         *)
(* Grind28r.v NUM60i'; the closings instantiate the step lemmas    *)
(* at s' := (V - 1)), and the plain identities are proved by       *)
(* div/mod decomposition at 2^20 -- X = Y from X / 2^20 =          *)
(* Y / 2^20 and X mod 2^20 = Y mod 2^20, each a single-chain vm     *)
(* evaluation, combined symbolically through Nat.div_mod_eq        *)
(* (Grind28s/w.v NUM60n, Grind28t/x.v NUM60m1, Grind28u/y.v        *)
(* NUM60m, Grind28f/h.v NUM60h, Grind28g/z.v NUM60k,               *)
(* Grind28e/k.v NUM60f', Grind28ad.v NUM60g, Grind28v/aa.v         *)
(* NUM60j', and                                                    *)
(* Grind28d/ab.v NUM60a and Grind28i/ac.v S60rv2 by symbolic       *)
(* summand decomposition).  Grind28ag.v carries the REP60          *)
(* identities and the NUM60X identities; Grind28.v carries         *)
(* CASCADE60a-e and Grind28ah.v CASCADE60f-j;                      *)
(* Grind28j.v carries CASCADE60k-v and CASCADE60; Grind28l.v       *)
(* carries TOP60_TO_TOP14; Grind28m/n/o.v carry TOP60_2/4/6;       *)
(* Grind28p.v carries TOP60_BAND, TAIL2_END15, TAIL2_END14_of60    *)
(* and ESC_ERA_LAW_60.  Every lemma statement is the one the       *)
(* phase's single-file draft would carry; no statement depends     *)
(* on the split.                                                   *)
(* ================================================================= *)

Require Import List Bool Arith Lia ZArith.
Import ListNotations.
Require Import TM Sections Mirror TokenPass Recoord Era Esc Dev
               Grind Grind2 Grind3 Grind4 Grind5 Grind6 Grind7 Grind8
               Grind9 Grind10 Grind11 Grind12 Grind13 Grind14 Grind15
               Grind16 Grind17 Grind18 Grind19 Grind20 Grind21 Grind22
               Grind23 Grind24 Grind25 Grind26 Grind26a Grind26b
               Grind26c Grind26d Grind26e Grind26f Grind26g Grind27a
               Grind27b Grind27c Grind27d Grind27e Grind27f Grind27g
               Grind28a Grind28ag.

(* Section equality: componentwise, arithmetic leaves by lia.      *)
Ltac sec_eq :=
  repeat (first [ solve [reflexivity] | solve [lia] | f_equal ]).

(* Closed-numeral arithmetic: literals >= 7426 are parsed as       *)
(* Nat.of_num_uint atoms, which lia cannot relate to variables;    *)
(* for purely closed <= goals the boolean check decides them.      *)
Ltac closearith :=
  first [ lia | apply Nat.leb_le; reflexivity ].

(* CASCADE60a: steps 1-56 of the CASCADE60 chain. *)
Lemma CASCADE60a : forall w,
  hsteps (HC [34304475; 7965811; 4012920; 308090; 49409; 7710; 1059; 199; 101; 0] 0 3 2 (repeat (1, 2) 58806190 ++ w) 1)
         (HC [235; 20; 0] 454 3 2 ((653, 2) :: (1, 1) :: repeat (1, 2) 7710 ++ (33987, 2) :: (1, 1) :: repeat (1, 2) 308090 ++ (3396738, 2) :: (1, 1) :: repeat (1, 2) 7965811 ++ (18372851, 2) :: (1, 1) :: repeat (1, 2) 58806192 ++ w) 1).
Proof.
  intro w.
  (* step 1: P PX2A *)
  apply (hsteps_trans _ (HC [4012920; 308090; 49409; 7710; 1059; 199; 101; 0] 7965810 34304473 2 ((1, 1) :: repeat (1, 2) 58806192 ++ w) 1)).
  {
    rewrite NUM60ta1. rewrite NUM60ta2. rewrite NUM60ta3.
    replace ((1, 1) :: repeat (1, 2) 58806192 ++ w)
      with ((1, 1) :: (1, 2) :: (1, 2) :: repeat (1, 2) 58806190 ++ w)
      by (apply REP60a).
    exact (hsteps_step _ _ _ (hPX2A 34304472 7965810 [4012920; 308090; 49409; 7710; 1059; 199; 101; 0] (repeat (1, 2) 58806190 ++ w) 1) (hsteps_refl _)).
  }
  (* step 2: P PUSH *)
  apply (hsteps_trans _ (HC [4012920; 308090; 49409; 7710; 1059; 199; 101; 0] 7965809 1 2 ((34304471, 2) :: (1, 1) :: repeat (1, 2) 58806192 ++ w) 1)).
  {
    rewrite NUM60X1.
    rewrite NUM60X2.
    apply (sPUSH [4012920; 308090; 49409; 7710; 1059; 199; 101; 0] 7965809 34304473 ((1, 1) :: repeat (1, 2) 58806192 ++ w) 1); closearith.
  }
  (* step 3: P TDN *)
  apply (hsteps_trans _ (HB [4012920; 308090; 49409; 7710; 1059; 199; 101; 0] 7965809 1 4 ((34304471, 2) :: (1, 1) :: repeat (1, 2) 58806192 ++ w) 1)).
  {
    apply (sTDN [4012920; 308090; 49409; 7710; 1059; 199; 101; 0] 7965809 ((34304471, 2) :: (1, 1) :: repeat (1, 2) 58806192 ++ w) 1).
  }
  (* step 4: sTUP *)
  apply (hsteps_trans _ (HC [4012920; 308090; 49409; 7710; 1059; 199; 101; 0] 7965809 3 2 ((34304469, 2) :: (1, 1) :: repeat (1, 2) 58806192 ++ w) 1)).
  {
    rewrite NUM60X3.
    apply (sTUP [4012920; 308090; 49409; 7710; 1059; 199; 101; 0] 7965809 4 34304471 2 ((1, 1) :: repeat (1, 2) 58806192 ++ w) 1); closearith.
  }
  (* step 5: DIPGRIND 7965809 18372851 *)
  apply (hsteps_trans _ (HC [4012920; 308090; 49409; 7710; 1059; 199; 101; 0] 0 3 2 (repeat (1, 2) 7965809 ++ (18372851, 2) :: (1, 1) :: repeat (1, 2) 58806192 ++ w) 1)).
  {
    rewrite NUM60X4.
    apply (DIPGRIND 7965809 18372851 [4012920; 308090; 49409; 7710; 1059; 199; 101; 0] ((1, 1) :: repeat (1, 2) 58806192 ++ w) 1); closearith.
  }
  (* step 6: P PX2A *)
  apply (hsteps_trans _ (HC [49409; 7710; 1059; 199; 101; 0] 308089 4012918 2 ((1, 1) :: repeat (1, 2) 7965811 ++ (18372851, 2) :: (1, 1) :: repeat (1, 2) 58806192 ++ w) 1)).
  {
    rewrite NUM60tb1. rewrite NUM60tb2. rewrite NUM60tb3.
    replace ((1, 1) :: repeat (1, 2) 7965811 ++ (18372851, 2) :: (1, 1) :: repeat (1, 2) 58806192 ++ w)
      with ((1, 1) :: (1, 2) :: (1, 2) :: repeat (1, 2) 7965809 ++ (18372851, 2) :: (1, 1) :: repeat (1, 2) 58806192 ++ w)
      by (apply REP60b).
    exact (hsteps_step _ _ _ (hPX2A 4012917 308089 [49409; 7710; 1059; 199; 101; 0] (repeat (1, 2) 7965809 ++ (18372851, 2) :: (1, 1) :: repeat (1, 2) 58806192 ++ w) 1) (hsteps_refl _)).
  }
  (* step 7: P PUSH *)
  apply (hsteps_trans _ (HC [49409; 7710; 1059; 199; 101; 0] 308088 1 2 ((4012916, 2) :: (1, 1) :: repeat (1, 2) 7965811 ++ (18372851, 2) :: (1, 1) :: repeat (1, 2) 58806192 ++ w) 1)).
  {
    rewrite NUM60X5.
    rewrite NUM60X6.
    apply (sPUSH [49409; 7710; 1059; 199; 101; 0] 308088 4012918 ((1, 1) :: repeat (1, 2) 7965811 ++ (18372851, 2) :: (1, 1) :: repeat (1, 2) 58806192 ++ w) 1); closearith.
  }
  (* step 8: P TDN *)
  apply (hsteps_trans _ (HB [49409; 7710; 1059; 199; 101; 0] 308088 1 4 ((4012916, 2) :: (1, 1) :: repeat (1, 2) 7965811 ++ (18372851, 2) :: (1, 1) :: repeat (1, 2) 58806192 ++ w) 1)).
  {
    apply (sTDN [49409; 7710; 1059; 199; 101; 0] 308088 ((4012916, 2) :: (1, 1) :: repeat (1, 2) 7965811 ++ (18372851, 2) :: (1, 1) :: repeat (1, 2) 58806192 ++ w) 1).
  }
  (* step 9: sTUP *)
  apply (hsteps_trans _ (HC [49409; 7710; 1059; 199; 101; 0] 308088 3 2 ((4012914, 2) :: (1, 1) :: repeat (1, 2) 7965811 ++ (18372851, 2) :: (1, 1) :: repeat (1, 2) 58806192 ++ w) 1)).
  {
    rewrite NUM60X7.
    apply (sTUP [49409; 7710; 1059; 199; 101; 0] 308088 4 4012916 2 ((1, 1) :: repeat (1, 2) 7965811 ++ (18372851, 2) :: (1, 1) :: repeat (1, 2) 58806192 ++ w) 1); closearith.
  }
  (* step 10: DIPGRIND 308088 3396738 *)
  apply (hsteps_trans _ (HC [49409; 7710; 1059; 199; 101; 0] 0 3 2 (repeat (1, 2) 308088 ++ (3396738, 2) :: (1, 1) :: repeat (1, 2) 7965811 ++ (18372851, 2) :: (1, 1) :: repeat (1, 2) 58806192 ++ w) 1)).
  {
    rewrite NUM60X8.
    apply (DIPGRIND 308088 3396738 [49409; 7710; 1059; 199; 101; 0] ((1, 1) :: repeat (1, 2) 7965811 ++ (18372851, 2) :: (1, 1) :: repeat (1, 2) 58806192 ++ w) 1); closearith.
  }
  (* step 11: P PX2A *)
  apply (hsteps_trans _ (HC [1059; 199; 101; 0] 7709 49407 2 ((1, 1) :: repeat (1, 2) 308090 ++ (3396738, 2) :: (1, 1) :: repeat (1, 2) 7965811 ++ (18372851, 2) :: (1, 1) :: repeat (1, 2) 58806192 ++ w) 1)).
  {
    rewrite NUM60tc1. rewrite NUM60tc2. rewrite NUM60tc3.
    replace ((1, 1) :: repeat (1, 2) 308090 ++ (3396738, 2) :: (1, 1) :: repeat (1, 2) 7965811 ++ (18372851, 2) :: (1, 1) :: repeat (1, 2) 58806192 ++ w)
      with ((1, 1) :: (1, 2) :: (1, 2) :: repeat (1, 2) 308088 ++ (3396738, 2) :: (1, 1) :: repeat (1, 2) 7965811 ++ (18372851, 2) :: (1, 1) :: repeat (1, 2) 58806192 ++ w)
      by (apply REP60c).
    exact (hsteps_step _ _ _ (hPX2A 49406 7709 [1059; 199; 101; 0] (repeat (1, 2) 308088 ++ (3396738, 2) :: (1, 1) :: repeat (1, 2) 7965811 ++ (18372851, 2) :: (1, 1) :: repeat (1, 2) 58806192 ++ w) 1) (hsteps_refl _)).
  }
  (* step 12: P PUSH *)
  apply (hsteps_trans _ (HC [1059; 199; 101; 0] 7708 1 2 ((49405, 2) :: (1, 1) :: repeat (1, 2) 308090 ++ (3396738, 2) :: (1, 1) :: repeat (1, 2) 7965811 ++ (18372851, 2) :: (1, 1) :: repeat (1, 2) 58806192 ++ w) 1)).
  {
    replace ((49405, 2) :: (1, 1) :: repeat (1, 2) 308090 ++ (3396738, 2) :: (1, 1) :: repeat (1, 2) 7965811 ++ (18372851, 2) :: (1, 1) :: repeat (1, 2) 58806192 ++ w) with ((49407 - 2, 2) :: (1, 1) :: repeat (1, 2) 308090 ++ (3396738, 2) :: (1, 1) :: repeat (1, 2) 7965811 ++ (18372851, 2) :: (1, 1) :: repeat (1, 2) 58806192 ++ w) by sec_eq.
    apply (sPUSH [1059; 199; 101; 0] 7708 49407 ((1, 1) :: repeat (1, 2) 308090 ++ (3396738, 2) :: (1, 1) :: repeat (1, 2) 7965811 ++ (18372851, 2) :: (1, 1) :: repeat (1, 2) 58806192 ++ w) 1); closearith.
  }
  (* step 13: P TDN *)
  apply (hsteps_trans _ (HB [1059; 199; 101; 0] 7708 1 4 ((49405, 2) :: (1, 1) :: repeat (1, 2) 308090 ++ (3396738, 2) :: (1, 1) :: repeat (1, 2) 7965811 ++ (18372851, 2) :: (1, 1) :: repeat (1, 2) 58806192 ++ w) 1)).
  {
    apply (sTDN [1059; 199; 101; 0] 7708 ((49405, 2) :: (1, 1) :: repeat (1, 2) 308090 ++ (3396738, 2) :: (1, 1) :: repeat (1, 2) 7965811 ++ (18372851, 2) :: (1, 1) :: repeat (1, 2) 58806192 ++ w) 1).
  }
  (* step 14: sTUP *)
  apply (hsteps_trans _ (HC [1059; 199; 101; 0] 7708 3 2 ((49403, 2) :: (1, 1) :: repeat (1, 2) 308090 ++ (3396738, 2) :: (1, 1) :: repeat (1, 2) 7965811 ++ (18372851, 2) :: (1, 1) :: repeat (1, 2) 58806192 ++ w) 1)).
  {
    replace ((49403, 2) :: (1, 1) :: repeat (1, 2) 308090 ++ (3396738, 2) :: (1, 1) :: repeat (1, 2) 7965811 ++ (18372851, 2) :: (1, 1) :: repeat (1, 2) 58806192 ++ w) with ((49405 - 2, 2) :: (1, 1) :: repeat (1, 2) 308090 ++ (3396738, 2) :: (1, 1) :: repeat (1, 2) 7965811 ++ (18372851, 2) :: (1, 1) :: repeat (1, 2) 58806192 ++ w) by sec_eq.
    apply (sTUP [1059; 199; 101; 0] 7708 4 49405 2 ((1, 1) :: repeat (1, 2) 308090 ++ (3396738, 2) :: (1, 1) :: repeat (1, 2) 7965811 ++ (18372851, 2) :: (1, 1) :: repeat (1, 2) 58806192 ++ w) 1); closearith.
  }
  (* step 15: DIPGRIND 7708 33987 *)
  apply (hsteps_trans _ (HC [1059; 199; 101; 0] 0 3 2 (repeat (1, 2) 7708 ++ (33987, 2) :: (1, 1) :: repeat (1, 2) 308090 ++ (3396738, 2) :: (1, 1) :: repeat (1, 2) 7965811 ++ (18372851, 2) :: (1, 1) :: repeat (1, 2) 58806192 ++ w) 1)).
  {
    apply (DIPGRIND 7708 33987 [1059; 199; 101; 0] ((1, 1) :: repeat (1, 2) 308090 ++ (3396738, 2) :: (1, 1) :: repeat (1, 2) 7965811 ++ (18372851, 2) :: (1, 1) :: repeat (1, 2) 58806192 ++ w) 1); closearith.
  }
  (* step 16: P PX2A *)
  apply (hsteps_trans _ (HC [101; 0] 198 1057 2 ((1, 1) :: repeat (1, 2) 7710 ++ (33987, 2) :: (1, 1) :: repeat (1, 2) 308090 ++ (3396738, 2) :: (1, 1) :: repeat (1, 2) 7965811 ++ (18372851, 2) :: (1, 1) :: repeat (1, 2) 58806192 ++ w) 1)).
  {
    exact (hsteps_step _ _ _ (hPX2A 1056 198 [101; 0] (repeat (1, 2) 7708 ++ (33987, 2) :: (1, 1) :: repeat (1, 2) 308090 ++ (3396738, 2) :: (1, 1) :: repeat (1, 2) 7965811 ++ (18372851, 2) :: (1, 1) :: repeat (1, 2) 58806192 ++ w) 1) (hsteps_refl _)).
  }
  (* step 17: P PUSH *)
  apply (hsteps_trans _ (HC [101; 0] 197 1 2 ((1055, 2) :: (1, 1) :: repeat (1, 2) 7710 ++ (33987, 2) :: (1, 1) :: repeat (1, 2) 308090 ++ (3396738, 2) :: (1, 1) :: repeat (1, 2) 7965811 ++ (18372851, 2) :: (1, 1) :: repeat (1, 2) 58806192 ++ w) 1)).
  {
    replace ((1055, 2) :: (1, 1) :: repeat (1, 2) 7710 ++ (33987, 2) :: (1, 1) :: repeat (1, 2) 308090 ++ (3396738, 2) :: (1, 1) :: repeat (1, 2) 7965811 ++ (18372851, 2) :: (1, 1) :: repeat (1, 2) 58806192 ++ w) with ((1057 - 2, 2) :: (1, 1) :: repeat (1, 2) 7710 ++ (33987, 2) :: (1, 1) :: repeat (1, 2) 308090 ++ (3396738, 2) :: (1, 1) :: repeat (1, 2) 7965811 ++ (18372851, 2) :: (1, 1) :: repeat (1, 2) 58806192 ++ w) by sec_eq.
    apply (sPUSH [101; 0] 197 1057 ((1, 1) :: repeat (1, 2) 7710 ++ (33987, 2) :: (1, 1) :: repeat (1, 2) 308090 ++ (3396738, 2) :: (1, 1) :: repeat (1, 2) 7965811 ++ (18372851, 2) :: (1, 1) :: repeat (1, 2) 58806192 ++ w) 1); closearith.
  }
  (* step 18: P TDN *)
  apply (hsteps_trans _ (HB [101; 0] 197 1 4 ((1055, 2) :: (1, 1) :: repeat (1, 2) 7710 ++ (33987, 2) :: (1, 1) :: repeat (1, 2) 308090 ++ (3396738, 2) :: (1, 1) :: repeat (1, 2) 7965811 ++ (18372851, 2) :: (1, 1) :: repeat (1, 2) 58806192 ++ w) 1)).
  {
    apply (sTDN [101; 0] 197 ((1055, 2) :: (1, 1) :: repeat (1, 2) 7710 ++ (33987, 2) :: (1, 1) :: repeat (1, 2) 308090 ++ (3396738, 2) :: (1, 1) :: repeat (1, 2) 7965811 ++ (18372851, 2) :: (1, 1) :: repeat (1, 2) 58806192 ++ w) 1).
  }
  (* step 19: sTUP *)
  apply (hsteps_trans _ (HC [101; 0] 197 3 2 ((1053, 2) :: (1, 1) :: repeat (1, 2) 7710 ++ (33987, 2) :: (1, 1) :: repeat (1, 2) 308090 ++ (3396738, 2) :: (1, 1) :: repeat (1, 2) 7965811 ++ (18372851, 2) :: (1, 1) :: repeat (1, 2) 58806192 ++ w) 1)).
  {
    replace ((1053, 2) :: (1, 1) :: repeat (1, 2) 7710 ++ (33987, 2) :: (1, 1) :: repeat (1, 2) 308090 ++ (3396738, 2) :: (1, 1) :: repeat (1, 2) 7965811 ++ (18372851, 2) :: (1, 1) :: repeat (1, 2) 58806192 ++ w) with ((1055 - 2, 2) :: (1, 1) :: repeat (1, 2) 7710 ++ (33987, 2) :: (1, 1) :: repeat (1, 2) 308090 ++ (3396738, 2) :: (1, 1) :: repeat (1, 2) 7965811 ++ (18372851, 2) :: (1, 1) :: repeat (1, 2) 58806192 ++ w) by sec_eq.
    apply (sTUP [101; 0] 197 4 1055 2 ((1, 1) :: repeat (1, 2) 7710 ++ (33987, 2) :: (1, 1) :: repeat (1, 2) 308090 ++ (3396738, 2) :: (1, 1) :: repeat (1, 2) 7965811 ++ (18372851, 2) :: (1, 1) :: repeat (1, 2) 58806192 ++ w) 1); closearith.
  }
  (* step 20: DIPGRIND 197 659 *)
  apply (hsteps_trans _ (HC [101; 0] 0 3 2 (repeat (1, 2) 197 ++ (659, 2) :: (1, 1) :: repeat (1, 2) 7710 ++ (33987, 2) :: (1, 1) :: repeat (1, 2) 308090 ++ (3396738, 2) :: (1, 1) :: repeat (1, 2) 7965811 ++ (18372851, 2) :: (1, 1) :: repeat (1, 2) 58806192 ++ w) 1)).
  {
    apply (DIPGRIND 197 659 [101; 0] ((1, 1) :: repeat (1, 2) 7710 ++ (33987, 2) :: (1, 1) :: repeat (1, 2) 308090 ++ (3396738, 2) :: (1, 1) :: repeat (1, 2) 7965811 ++ (18372851, 2) :: (1, 1) :: repeat (1, 2) 58806192 ++ w) 1); closearith.
  }
  (* step 21: P PX2A0 *)
  apply (hsteps_trans _ (HB [0] 3 1 2 ((97, 2) :: (1, 1) :: repeat (1, 2) 199 ++ (659, 2) :: (1, 1) :: repeat (1, 2) 7710 ++ (33987, 2) :: (1, 1) :: repeat (1, 2) 308090 ++ (3396738, 2) :: (1, 1) :: repeat (1, 2) 7965811 ++ (18372851, 2) :: (1, 1) :: repeat (1, 2) 58806192 ++ w) 1)).
  {
    exact (hsteps_step _ _ _ (hPX2A0 96 (repeat (1, 2) 197 ++ (659, 2) :: (1, 1) :: repeat (1, 2) 7710 ++ (33987, 2) :: (1, 1) :: repeat (1, 2) 308090 ++ (3396738, 2) :: (1, 1) :: repeat (1, 2) 7965811 ++ (18372851, 2) :: (1, 1) :: repeat (1, 2) 58806192 ++ w) 1) (hsteps_refl _)).
  }
  (* step 22: sTUP *)
  apply (hsteps_trans _ (HC [0] 3 1 2 ((95, 2) :: (1, 1) :: repeat (1, 2) 199 ++ (659, 2) :: (1, 1) :: repeat (1, 2) 7710 ++ (33987, 2) :: (1, 1) :: repeat (1, 2) 308090 ++ (3396738, 2) :: (1, 1) :: repeat (1, 2) 7965811 ++ (18372851, 2) :: (1, 1) :: repeat (1, 2) 58806192 ++ w) 1)).
  {
    replace ((95, 2) :: (1, 1) :: repeat (1, 2) 199 ++ (659, 2) :: (1, 1) :: repeat (1, 2) 7710 ++ (33987, 2) :: (1, 1) :: repeat (1, 2) 308090 ++ (3396738, 2) :: (1, 1) :: repeat (1, 2) 7965811 ++ (18372851, 2) :: (1, 1) :: repeat (1, 2) 58806192 ++ w) with ((97 - 2, 2) :: (1, 1) :: repeat (1, 2) 199 ++ (659, 2) :: (1, 1) :: repeat (1, 2) 7710 ++ (33987, 2) :: (1, 1) :: repeat (1, 2) 308090 ++ (3396738, 2) :: (1, 1) :: repeat (1, 2) 7965811 ++ (18372851, 2) :: (1, 1) :: repeat (1, 2) 58806192 ++ w) by sec_eq.
    apply (sTUP [0] 3 2 97 2 ((1, 1) :: repeat (1, 2) 199 ++ (659, 2) :: (1, 1) :: repeat (1, 2) 7710 ++ (33987, 2) :: (1, 1) :: repeat (1, 2) 308090 ++ (3396738, 2) :: (1, 1) :: repeat (1, 2) 7965811 ++ (18372851, 2) :: (1, 1) :: repeat (1, 2) 58806192 ++ w) 1); closearith.
  }
  (* step 23: P TDN *)
  apply (hsteps_trans _ (HB [0] 3 1 4 ((95, 2) :: (1, 1) :: repeat (1, 2) 199 ++ (659, 2) :: (1, 1) :: repeat (1, 2) 7710 ++ (33987, 2) :: (1, 1) :: repeat (1, 2) 308090 ++ (3396738, 2) :: (1, 1) :: repeat (1, 2) 7965811 ++ (18372851, 2) :: (1, 1) :: repeat (1, 2) 58806192 ++ w) 1)).
  {
    apply (sTDN [0] 3 ((95, 2) :: (1, 1) :: repeat (1, 2) 199 ++ (659, 2) :: (1, 1) :: repeat (1, 2) 7710 ++ (33987, 2) :: (1, 1) :: repeat (1, 2) 308090 ++ (3396738, 2) :: (1, 1) :: repeat (1, 2) 7965811 ++ (18372851, 2) :: (1, 1) :: repeat (1, 2) 58806192 ++ w) 1).
  }
  (* step 24: sTUP *)
  apply (hsteps_trans _ (HC [0] 3 3 2 ((93, 2) :: (1, 1) :: repeat (1, 2) 199 ++ (659, 2) :: (1, 1) :: repeat (1, 2) 7710 ++ (33987, 2) :: (1, 1) :: repeat (1, 2) 308090 ++ (3396738, 2) :: (1, 1) :: repeat (1, 2) 7965811 ++ (18372851, 2) :: (1, 1) :: repeat (1, 2) 58806192 ++ w) 1)).
  {
    replace ((93, 2) :: (1, 1) :: repeat (1, 2) 199 ++ (659, 2) :: (1, 1) :: repeat (1, 2) 7710 ++ (33987, 2) :: (1, 1) :: repeat (1, 2) 308090 ++ (3396738, 2) :: (1, 1) :: repeat (1, 2) 7965811 ++ (18372851, 2) :: (1, 1) :: repeat (1, 2) 58806192 ++ w) with ((95 - 2, 2) :: (1, 1) :: repeat (1, 2) 199 ++ (659, 2) :: (1, 1) :: repeat (1, 2) 7710 ++ (33987, 2) :: (1, 1) :: repeat (1, 2) 308090 ++ (3396738, 2) :: (1, 1) :: repeat (1, 2) 7965811 ++ (18372851, 2) :: (1, 1) :: repeat (1, 2) 58806192 ++ w) by sec_eq.
    apply (sTUP [0] 3 4 95 2 ((1, 1) :: repeat (1, 2) 199 ++ (659, 2) :: (1, 1) :: repeat (1, 2) 7710 ++ (33987, 2) :: (1, 1) :: repeat (1, 2) 308090 ++ (3396738, 2) :: (1, 1) :: repeat (1, 2) 7965811 ++ (18372851, 2) :: (1, 1) :: repeat (1, 2) 58806192 ++ w) 1); closearith.
  }
  (* step 25: DIPGRIND 3 87 *)
  apply (hsteps_trans _ (HC [0] 0 3 2 (repeat (1, 2) 3 ++ (87, 2) :: (1, 1) :: repeat (1, 2) 199 ++ (659, 2) :: (1, 1) :: repeat (1, 2) 7710 ++ (33987, 2) :: (1, 1) :: repeat (1, 2) 308090 ++ (3396738, 2) :: (1, 1) :: repeat (1, 2) 7965811 ++ (18372851, 2) :: (1, 1) :: repeat (1, 2) 58806192 ++ w) 1)).
  {
    apply (DIPGRIND 3 87 [0] ((1, 1) :: repeat (1, 2) 199 ++ (659, 2) :: (1, 1) :: repeat (1, 2) 7710 ++ (33987, 2) :: (1, 1) :: repeat (1, 2) 308090 ++ (3396738, 2) :: (1, 1) :: repeat (1, 2) 7965811 ++ (18372851, 2) :: (1, 1) :: repeat (1, 2) 58806192 ++ w) 1); closearith.
  }
  (* step 26: P PX2B0 *)
  apply (hsteps_trans _ (HB [] 0 1 5 (repeat (1, 2) 4 ++ (87, 2) :: (1, 1) :: repeat (1, 2) 199 ++ (659, 2) :: (1, 1) :: repeat (1, 2) 7710 ++ (33987, 2) :: (1, 1) :: repeat (1, 2) 308090 ++ (3396738, 2) :: (1, 1) :: repeat (1, 2) 7965811 ++ (18372851, 2) :: (1, 1) :: repeat (1, 2) 58806192 ++ w) 1)).
  {
    exact (hsteps_step _ _ _ (hPX2B0 (repeat (1, 2) 3 ++ (87, 2) :: (1, 1) :: repeat (1, 2) 199 ++ (659, 2) :: (1, 1) :: repeat (1, 2) 7710 ++ (33987, 2) :: (1, 1) :: repeat (1, 2) 308090 ++ (3396738, 2) :: (1, 1) :: repeat (1, 2) 7965811 ++ (18372851, 2) :: (1, 1) :: repeat (1, 2) 58806192 ++ w) 1) (hsteps_refl _)).
  }
  (* step 27: M pop12 (4,) *)
  apply (hsteps_trans _ (HB [] 4 1 13 ((87, 2) :: (1, 1) :: repeat (1, 2) 199 ++ (659, 2) :: (1, 1) :: repeat (1, 2) 7710 ++ (33987, 2) :: (1, 1) :: repeat (1, 2) 308090 ++ (3396738, 2) :: (1, 1) :: repeat (1, 2) 7965811 ++ (18372851, 2) :: (1, 1) :: repeat (1, 2) 58806192 ++ w) 1)).
  {
    apply (pop12 4 [] 0 5 ((87, 2) :: (1, 1) :: repeat (1, 2) 199 ++ (659, 2) :: (1, 1) :: repeat (1, 2) 7710 ++ (33987, 2) :: (1, 1) :: repeat (1, 2) 308090 ++ (3396738, 2) :: (1, 1) :: repeat (1, 2) 7965811 ++ (18372851, 2) :: (1, 1) :: repeat (1, 2) 58806192 ++ w) 1); closearith.
  }
  (* step 28: sTUP *)
  apply (hsteps_trans _ (HC [] 4 12 2 ((85, 2) :: (1, 1) :: repeat (1, 2) 199 ++ (659, 2) :: (1, 1) :: repeat (1, 2) 7710 ++ (33987, 2) :: (1, 1) :: repeat (1, 2) 308090 ++ (3396738, 2) :: (1, 1) :: repeat (1, 2) 7965811 ++ (18372851, 2) :: (1, 1) :: repeat (1, 2) 58806192 ++ w) 1)).
  {
    replace ((85, 2) :: (1, 1) :: repeat (1, 2) 199 ++ (659, 2) :: (1, 1) :: repeat (1, 2) 7710 ++ (33987, 2) :: (1, 1) :: repeat (1, 2) 308090 ++ (3396738, 2) :: (1, 1) :: repeat (1, 2) 7965811 ++ (18372851, 2) :: (1, 1) :: repeat (1, 2) 58806192 ++ w) with ((87 - 2, 2) :: (1, 1) :: repeat (1, 2) 199 ++ (659, 2) :: (1, 1) :: repeat (1, 2) 7710 ++ (33987, 2) :: (1, 1) :: repeat (1, 2) 308090 ++ (3396738, 2) :: (1, 1) :: repeat (1, 2) 7965811 ++ (18372851, 2) :: (1, 1) :: repeat (1, 2) 58806192 ++ w) by sec_eq.
    apply (sTUP [] 4 13 87 2 ((1, 1) :: repeat (1, 2) 199 ++ (659, 2) :: (1, 1) :: repeat (1, 2) 7710 ++ (33987, 2) :: (1, 1) :: repeat (1, 2) 308090 ++ (3396738, 2) :: (1, 1) :: repeat (1, 2) 7965811 ++ (18372851, 2) :: (1, 1) :: repeat (1, 2) 58806192 ++ w) 1); closearith.
  }
  (* step 29: P PUSH *)
  apply (hsteps_trans _ (HC [] 3 1 2 ((10, 2) :: (85, 2) :: (1, 1) :: repeat (1, 2) 199 ++ (659, 2) :: (1, 1) :: repeat (1, 2) 7710 ++ (33987, 2) :: (1, 1) :: repeat (1, 2) 308090 ++ (3396738, 2) :: (1, 1) :: repeat (1, 2) 7965811 ++ (18372851, 2) :: (1, 1) :: repeat (1, 2) 58806192 ++ w) 1)).
  {
    replace ((10, 2) :: (85, 2) :: (1, 1) :: repeat (1, 2) 199 ++ (659, 2) :: (1, 1) :: repeat (1, 2) 7710 ++ (33987, 2) :: (1, 1) :: repeat (1, 2) 308090 ++ (3396738, 2) :: (1, 1) :: repeat (1, 2) 7965811 ++ (18372851, 2) :: (1, 1) :: repeat (1, 2) 58806192 ++ w) with ((12 - 2, 2) :: (85, 2) :: (1, 1) :: repeat (1, 2) 199 ++ (659, 2) :: (1, 1) :: repeat (1, 2) 7710 ++ (33987, 2) :: (1, 1) :: repeat (1, 2) 308090 ++ (3396738, 2) :: (1, 1) :: repeat (1, 2) 7965811 ++ (18372851, 2) :: (1, 1) :: repeat (1, 2) 58806192 ++ w) by sec_eq.
    apply (sPUSH [] 3 12 ((85, 2) :: (1, 1) :: repeat (1, 2) 199 ++ (659, 2) :: (1, 1) :: repeat (1, 2) 7710 ++ (33987, 2) :: (1, 1) :: repeat (1, 2) 308090 ++ (3396738, 2) :: (1, 1) :: repeat (1, 2) 7965811 ++ (18372851, 2) :: (1, 1) :: repeat (1, 2) 58806192 ++ w) 1); closearith.
  }
  (* step 30: P TDN *)
  apply (hsteps_trans _ (HB [] 3 1 4 ((10, 2) :: (85, 2) :: (1, 1) :: repeat (1, 2) 199 ++ (659, 2) :: (1, 1) :: repeat (1, 2) 7710 ++ (33987, 2) :: (1, 1) :: repeat (1, 2) 308090 ++ (3396738, 2) :: (1, 1) :: repeat (1, 2) 7965811 ++ (18372851, 2) :: (1, 1) :: repeat (1, 2) 58806192 ++ w) 1)).
  {
    apply (sTDN [] 3 ((10, 2) :: (85, 2) :: (1, 1) :: repeat (1, 2) 199 ++ (659, 2) :: (1, 1) :: repeat (1, 2) 7710 ++ (33987, 2) :: (1, 1) :: repeat (1, 2) 308090 ++ (3396738, 2) :: (1, 1) :: repeat (1, 2) 7965811 ++ (18372851, 2) :: (1, 1) :: repeat (1, 2) 58806192 ++ w) 1).
  }
  (* step 31: sTUP *)
  apply (hsteps_trans _ (HC [] 3 3 2 ((8, 2) :: (85, 2) :: (1, 1) :: repeat (1, 2) 199 ++ (659, 2) :: (1, 1) :: repeat (1, 2) 7710 ++ (33987, 2) :: (1, 1) :: repeat (1, 2) 308090 ++ (3396738, 2) :: (1, 1) :: repeat (1, 2) 7965811 ++ (18372851, 2) :: (1, 1) :: repeat (1, 2) 58806192 ++ w) 1)).
  {
    replace ((8, 2) :: (85, 2) :: (1, 1) :: repeat (1, 2) 199 ++ (659, 2) :: (1, 1) :: repeat (1, 2) 7710 ++ (33987, 2) :: (1, 1) :: repeat (1, 2) 308090 ++ (3396738, 2) :: (1, 1) :: repeat (1, 2) 7965811 ++ (18372851, 2) :: (1, 1) :: repeat (1, 2) 58806192 ++ w) with ((10 - 2, 2) :: (85, 2) :: (1, 1) :: repeat (1, 2) 199 ++ (659, 2) :: (1, 1) :: repeat (1, 2) 7710 ++ (33987, 2) :: (1, 1) :: repeat (1, 2) 308090 ++ (3396738, 2) :: (1, 1) :: repeat (1, 2) 7965811 ++ (18372851, 2) :: (1, 1) :: repeat (1, 2) 58806192 ++ w) by sec_eq.
    apply (sTUP [] 3 4 10 2 ((85, 2) :: (1, 1) :: repeat (1, 2) 199 ++ (659, 2) :: (1, 1) :: repeat (1, 2) 7710 ++ (33987, 2) :: (1, 1) :: repeat (1, 2) 308090 ++ (3396738, 2) :: (1, 1) :: repeat (1, 2) 7965811 ++ (18372851, 2) :: (1, 1) :: repeat (1, 2) 58806192 ++ w) 1); closearith.
  }
  (* step 32: DIPGRIND 3 2 *)
  apply (hsteps_trans _ (HC [] 0 3 2 (repeat (1, 2) 3 ++ (2, 2) :: (85, 2) :: (1, 1) :: repeat (1, 2) 199 ++ (659, 2) :: (1, 1) :: repeat (1, 2) 7710 ++ (33987, 2) :: (1, 1) :: repeat (1, 2) 308090 ++ (3396738, 2) :: (1, 1) :: repeat (1, 2) 7965811 ++ (18372851, 2) :: (1, 1) :: repeat (1, 2) 58806192 ++ w) 1)).
  {
    apply (DIPGRIND 3 2 [] ((85, 2) :: (1, 1) :: repeat (1, 2) 199 ++ (659, 2) :: (1, 1) :: repeat (1, 2) 7710 ++ (33987, 2) :: (1, 1) :: repeat (1, 2) 308090 ++ (3396738, 2) :: (1, 1) :: repeat (1, 2) 7965811 ++ (18372851, 2) :: (1, 1) :: repeat (1, 2) 58806192 ++ w) 1); closearith.
  }
  (* step 33: P PUSHX *)
  apply (hsteps_trans _ (HB [] 1 1 7 (repeat (1, 2) 3 ++ (2, 2) :: (85, 2) :: (1, 1) :: repeat (1, 2) 199 ++ (659, 2) :: (1, 1) :: repeat (1, 2) 7710 ++ (33987, 2) :: (1, 1) :: repeat (1, 2) 308090 ++ (3396738, 2) :: (1, 1) :: repeat (1, 2) 7965811 ++ (18372851, 2) :: (1, 1) :: repeat (1, 2) 58806192 ++ w) 1)).
  {
    exact (hsteps_step _ _ _ (hPUSHX (repeat (1, 2) 3 ++ (2, 2) :: (85, 2) :: (1, 1) :: repeat (1, 2) 199 ++ (659, 2) :: (1, 1) :: repeat (1, 2) 7710 ++ (33987, 2) :: (1, 1) :: repeat (1, 2) 308090 ++ (3396738, 2) :: (1, 1) :: repeat (1, 2) 7965811 ++ (18372851, 2) :: (1, 1) :: repeat (1, 2) 58806192 ++ w) 1) (hsteps_refl _)).
  }
  (* step 34: M pop12 (3,) *)
  apply (hsteps_trans _ (HB [] 4 1 13 ((2, 2) :: (85, 2) :: (1, 1) :: repeat (1, 2) 199 ++ (659, 2) :: (1, 1) :: repeat (1, 2) 7710 ++ (33987, 2) :: (1, 1) :: repeat (1, 2) 308090 ++ (3396738, 2) :: (1, 1) :: repeat (1, 2) 7965811 ++ (18372851, 2) :: (1, 1) :: repeat (1, 2) 58806192 ++ w) 1)).
  {
    apply (pop12 3 [] 1 7 ((2, 2) :: (85, 2) :: (1, 1) :: repeat (1, 2) 199 ++ (659, 2) :: (1, 1) :: repeat (1, 2) 7710 ++ (33987, 2) :: (1, 1) :: repeat (1, 2) 308090 ++ (3396738, 2) :: (1, 1) :: repeat (1, 2) 7965811 ++ (18372851, 2) :: (1, 1) :: repeat (1, 2) 58806192 ++ w) 1); closearith.
  }
  (* step 35: P TUP2_1 *)
  apply (hsteps_trans _ (HC [5] 13 1 2 ((83, 2) :: (1, 1) :: repeat (1, 2) 199 ++ (659, 2) :: (1, 1) :: repeat (1, 2) 7710 ++ (33987, 2) :: (1, 1) :: repeat (1, 2) 308090 ++ (3396738, 2) :: (1, 1) :: repeat (1, 2) 7965811 ++ (18372851, 2) :: (1, 1) :: repeat (1, 2) 58806192 ++ w) 1)).
  {
    replace ((83, 2) :: (1, 1) :: repeat (1, 2) 199 ++ (659, 2) :: (1, 1) :: repeat (1, 2) 7710 ++ (33987, 2) :: (1, 1) :: repeat (1, 2) 308090 ++ (3396738, 2) :: (1, 1) :: repeat (1, 2) 7965811 ++ (18372851, 2) :: (1, 1) :: repeat (1, 2) 58806192 ++ w) with ((85 - 2, 2) :: (1, 1) :: repeat (1, 2) 199 ++ (659, 2) :: (1, 1) :: repeat (1, 2) 7710 ++ (33987, 2) :: (1, 1) :: repeat (1, 2) 308090 ++ (3396738, 2) :: (1, 1) :: repeat (1, 2) 7965811 ++ (18372851, 2) :: (1, 1) :: repeat (1, 2) 58806192 ++ w) by sec_eq.
    apply (sTUP2_1 [] 4 12 85 ((1, 1) :: repeat (1, 2) 199 ++ (659, 2) :: (1, 1) :: repeat (1, 2) 7710 ++ (33987, 2) :: (1, 1) :: repeat (1, 2) 308090 ++ (3396738, 2) :: (1, 1) :: repeat (1, 2) 7965811 ++ (18372851, 2) :: (1, 1) :: repeat (1, 2) 58806192 ++ w) 1); closearith.
  }
  (* step 36: P TDN *)
  apply (hsteps_trans _ (HB [5] 13 1 4 ((83, 2) :: (1, 1) :: repeat (1, 2) 199 ++ (659, 2) :: (1, 1) :: repeat (1, 2) 7710 ++ (33987, 2) :: (1, 1) :: repeat (1, 2) 308090 ++ (3396738, 2) :: (1, 1) :: repeat (1, 2) 7965811 ++ (18372851, 2) :: (1, 1) :: repeat (1, 2) 58806192 ++ w) 1)).
  {
    apply (sTDN [5] 13 ((83, 2) :: (1, 1) :: repeat (1, 2) 199 ++ (659, 2) :: (1, 1) :: repeat (1, 2) 7710 ++ (33987, 2) :: (1, 1) :: repeat (1, 2) 308090 ++ (3396738, 2) :: (1, 1) :: repeat (1, 2) 7965811 ++ (18372851, 2) :: (1, 1) :: repeat (1, 2) 58806192 ++ w) 1).
  }
  (* step 37: sTUP *)
  apply (hsteps_trans _ (HC [5] 13 3 2 ((81, 2) :: (1, 1) :: repeat (1, 2) 199 ++ (659, 2) :: (1, 1) :: repeat (1, 2) 7710 ++ (33987, 2) :: (1, 1) :: repeat (1, 2) 308090 ++ (3396738, 2) :: (1, 1) :: repeat (1, 2) 7965811 ++ (18372851, 2) :: (1, 1) :: repeat (1, 2) 58806192 ++ w) 1)).
  {
    replace ((81, 2) :: (1, 1) :: repeat (1, 2) 199 ++ (659, 2) :: (1, 1) :: repeat (1, 2) 7710 ++ (33987, 2) :: (1, 1) :: repeat (1, 2) 308090 ++ (3396738, 2) :: (1, 1) :: repeat (1, 2) 7965811 ++ (18372851, 2) :: (1, 1) :: repeat (1, 2) 58806192 ++ w) with ((83 - 2, 2) :: (1, 1) :: repeat (1, 2) 199 ++ (659, 2) :: (1, 1) :: repeat (1, 2) 7710 ++ (33987, 2) :: (1, 1) :: repeat (1, 2) 308090 ++ (3396738, 2) :: (1, 1) :: repeat (1, 2) 7965811 ++ (18372851, 2) :: (1, 1) :: repeat (1, 2) 58806192 ++ w) by sec_eq.
    apply (sTUP [5] 13 4 83 2 ((1, 1) :: repeat (1, 2) 199 ++ (659, 2) :: (1, 1) :: repeat (1, 2) 7710 ++ (33987, 2) :: (1, 1) :: repeat (1, 2) 308090 ++ (3396738, 2) :: (1, 1) :: repeat (1, 2) 7965811 ++ (18372851, 2) :: (1, 1) :: repeat (1, 2) 58806192 ++ w) 1); closearith.
  }
  (* step 38: DIPGRIND 13 55 *)
  apply (hsteps_trans _ (HC [5] 0 3 2 (repeat (1, 2) 13 ++ (55, 2) :: (1, 1) :: repeat (1, 2) 199 ++ (659, 2) :: (1, 1) :: repeat (1, 2) 7710 ++ (33987, 2) :: (1, 1) :: repeat (1, 2) 308090 ++ (3396738, 2) :: (1, 1) :: repeat (1, 2) 7965811 ++ (18372851, 2) :: (1, 1) :: repeat (1, 2) 58806192 ++ w) 1)).
  {
    apply (DIPGRIND 13 55 [5] ((1, 1) :: repeat (1, 2) 199 ++ (659, 2) :: (1, 1) :: repeat (1, 2) 7710 ++ (33987, 2) :: (1, 1) :: repeat (1, 2) 308090 ++ (3396738, 2) :: (1, 1) :: repeat (1, 2) 7965811 ++ (18372851, 2) :: (1, 1) :: repeat (1, 2) 58806192 ++ w) 1); closearith.
  }
  (* step 39: P PX2Bgen *)
  apply (hsteps_trans _ (HB [0] 3 1 2 (repeat (1, 2) 1 ++ (1, 1) :: repeat (1, 2) 15 ++ (55, 2) :: (1, 1) :: repeat (1, 2) 199 ++ (659, 2) :: (1, 1) :: repeat (1, 2) 7710 ++ (33987, 2) :: (1, 1) :: repeat (1, 2) 308090 ++ (3396738, 2) :: (1, 1) :: repeat (1, 2) 7965811 ++ (18372851, 2) :: (1, 1) :: repeat (1, 2) 58806192 ++ w) 1)).
  {
    exact (hsteps_step _ _ _ (hPX2Bgen 0 (repeat (1, 2) 13 ++ (55, 2) :: (1, 1) :: repeat (1, 2) 199 ++ (659, 2) :: (1, 1) :: repeat (1, 2) 7710 ++ (33987, 2) :: (1, 1) :: repeat (1, 2) 308090 ++ (3396738, 2) :: (1, 1) :: repeat (1, 2) 7965811 ++ (18372851, 2) :: (1, 1) :: repeat (1, 2) 58806192 ++ w) 1) (hsteps_refl _)).
  }
  (* step 40: M pop12 (1,) *)
  apply (hsteps_trans _ (HB [0] 4 1 4 ((1, 1) :: repeat (1, 2) 15 ++ (55, 2) :: (1, 1) :: repeat (1, 2) 199 ++ (659, 2) :: (1, 1) :: repeat (1, 2) 7710 ++ (33987, 2) :: (1, 1) :: repeat (1, 2) 308090 ++ (3396738, 2) :: (1, 1) :: repeat (1, 2) 7965811 ++ (18372851, 2) :: (1, 1) :: repeat (1, 2) 58806192 ++ w) 1)).
  {
    apply (pop12 1 [0] 3 2 ((1, 1) :: repeat (1, 2) 15 ++ (55, 2) :: (1, 1) :: repeat (1, 2) 199 ++ (659, 2) :: (1, 1) :: repeat (1, 2) 7710 ++ (33987, 2) :: (1, 1) :: repeat (1, 2) 308090 ++ (3396738, 2) :: (1, 1) :: repeat (1, 2) 7965811 ++ (18372851, 2) :: (1, 1) :: repeat (1, 2) 58806192 ++ w) 1); closearith.
  }
  (* step 41: P POP *)
  apply (hsteps_trans _ (HB [0] 5 1 5 (repeat (1, 2) 15 ++ (55, 2) :: (1, 1) :: repeat (1, 2) 199 ++ (659, 2) :: (1, 1) :: repeat (1, 2) 7710 ++ (33987, 2) :: (1, 1) :: repeat (1, 2) 308090 ++ (3396738, 2) :: (1, 1) :: repeat (1, 2) 7965811 ++ (18372851, 2) :: (1, 1) :: repeat (1, 2) 58806192 ++ w) 1)).
  {
    apply (sPOP1 [0] 4 4 (repeat (1, 2) 15 ++ (55, 2) :: (1, 1) :: repeat (1, 2) 199 ++ (659, 2) :: (1, 1) :: repeat (1, 2) 7710 ++ (33987, 2) :: (1, 1) :: repeat (1, 2) 308090 ++ (3396738, 2) :: (1, 1) :: repeat (1, 2) 7965811 ++ (18372851, 2) :: (1, 1) :: repeat (1, 2) 58806192 ++ w) 1); closearith.
  }
  (* step 42: M pop12 (15,) *)
  apply (hsteps_trans _ (HB [0] 20 1 35 ((55, 2) :: (1, 1) :: repeat (1, 2) 199 ++ (659, 2) :: (1, 1) :: repeat (1, 2) 7710 ++ (33987, 2) :: (1, 1) :: repeat (1, 2) 308090 ++ (3396738, 2) :: (1, 1) :: repeat (1, 2) 7965811 ++ (18372851, 2) :: (1, 1) :: repeat (1, 2) 58806192 ++ w) 1)).
  {
    apply (pop12 15 [0] 5 5 ((55, 2) :: (1, 1) :: repeat (1, 2) 199 ++ (659, 2) :: (1, 1) :: repeat (1, 2) 7710 ++ (33987, 2) :: (1, 1) :: repeat (1, 2) 308090 ++ (3396738, 2) :: (1, 1) :: repeat (1, 2) 7965811 ++ (18372851, 2) :: (1, 1) :: repeat (1, 2) 58806192 ++ w) 1); closearith.
  }
  (* step 43: sTUP *)
  apply (hsteps_trans _ (HC [0] 20 34 2 ((53, 2) :: (1, 1) :: repeat (1, 2) 199 ++ (659, 2) :: (1, 1) :: repeat (1, 2) 7710 ++ (33987, 2) :: (1, 1) :: repeat (1, 2) 308090 ++ (3396738, 2) :: (1, 1) :: repeat (1, 2) 7965811 ++ (18372851, 2) :: (1, 1) :: repeat (1, 2) 58806192 ++ w) 1)).
  {
    replace ((53, 2) :: (1, 1) :: repeat (1, 2) 199 ++ (659, 2) :: (1, 1) :: repeat (1, 2) 7710 ++ (33987, 2) :: (1, 1) :: repeat (1, 2) 308090 ++ (3396738, 2) :: (1, 1) :: repeat (1, 2) 7965811 ++ (18372851, 2) :: (1, 1) :: repeat (1, 2) 58806192 ++ w) with ((55 - 2, 2) :: (1, 1) :: repeat (1, 2) 199 ++ (659, 2) :: (1, 1) :: repeat (1, 2) 7710 ++ (33987, 2) :: (1, 1) :: repeat (1, 2) 308090 ++ (3396738, 2) :: (1, 1) :: repeat (1, 2) 7965811 ++ (18372851, 2) :: (1, 1) :: repeat (1, 2) 58806192 ++ w) by sec_eq.
    apply (sTUP [0] 20 35 55 2 ((1, 1) :: repeat (1, 2) 199 ++ (659, 2) :: (1, 1) :: repeat (1, 2) 7710 ++ (33987, 2) :: (1, 1) :: repeat (1, 2) 308090 ++ (3396738, 2) :: (1, 1) :: repeat (1, 2) 7965811 ++ (18372851, 2) :: (1, 1) :: repeat (1, 2) 58806192 ++ w) 1); closearith.
  }
  (* step 44: hGRIND_even 15 *)
  apply (hsteps_trans _ (HB [0] 19 1 34 ((2, 2) :: (53, 2) :: (1, 1) :: repeat (1, 2) 199 ++ (659, 2) :: (1, 1) :: repeat (1, 2) 7710 ++ (33987, 2) :: (1, 1) :: repeat (1, 2) 308090 ++ (3396738, 2) :: (1, 1) :: repeat (1, 2) 7965811 ++ (18372851, 2) :: (1, 1) :: repeat (1, 2) 58806192 ++ w) 1)).
  {
    apply (hGRIND_even 15 [0] 19 ((53, 2) :: (1, 1) :: repeat (1, 2) 199 ++ (659, 2) :: (1, 1) :: repeat (1, 2) 7710 ++ (33987, 2) :: (1, 1) :: repeat (1, 2) 308090 ++ (3396738, 2) :: (1, 1) :: repeat (1, 2) 7965811 ++ (18372851, 2) :: (1, 1) :: repeat (1, 2) 58806192 ++ w) 1); closearith.
  }
  (* step 45: P TUP2_1 *)
  apply (hsteps_trans _ (HC [20; 0] 34 1 2 ((51, 2) :: (1, 1) :: repeat (1, 2) 199 ++ (659, 2) :: (1, 1) :: repeat (1, 2) 7710 ++ (33987, 2) :: (1, 1) :: repeat (1, 2) 308090 ++ (3396738, 2) :: (1, 1) :: repeat (1, 2) 7965811 ++ (18372851, 2) :: (1, 1) :: repeat (1, 2) 58806192 ++ w) 1)).
  {
    replace ((51, 2) :: (1, 1) :: repeat (1, 2) 199 ++ (659, 2) :: (1, 1) :: repeat (1, 2) 7710 ++ (33987, 2) :: (1, 1) :: repeat (1, 2) 308090 ++ (3396738, 2) :: (1, 1) :: repeat (1, 2) 7965811 ++ (18372851, 2) :: (1, 1) :: repeat (1, 2) 58806192 ++ w) with ((53 - 2, 2) :: (1, 1) :: repeat (1, 2) 199 ++ (659, 2) :: (1, 1) :: repeat (1, 2) 7710 ++ (33987, 2) :: (1, 1) :: repeat (1, 2) 308090 ++ (3396738, 2) :: (1, 1) :: repeat (1, 2) 7965811 ++ (18372851, 2) :: (1, 1) :: repeat (1, 2) 58806192 ++ w) by sec_eq.
    apply (sTUP2_1 [0] 19 33 53 ((1, 1) :: repeat (1, 2) 199 ++ (659, 2) :: (1, 1) :: repeat (1, 2) 7710 ++ (33987, 2) :: (1, 1) :: repeat (1, 2) 308090 ++ (3396738, 2) :: (1, 1) :: repeat (1, 2) 7965811 ++ (18372851, 2) :: (1, 1) :: repeat (1, 2) 58806192 ++ w) 1); closearith.
  }
  (* step 46: P TDN *)
  apply (hsteps_trans _ (HB [20; 0] 34 1 4 ((51, 2) :: (1, 1) :: repeat (1, 2) 199 ++ (659, 2) :: (1, 1) :: repeat (1, 2) 7710 ++ (33987, 2) :: (1, 1) :: repeat (1, 2) 308090 ++ (3396738, 2) :: (1, 1) :: repeat (1, 2) 7965811 ++ (18372851, 2) :: (1, 1) :: repeat (1, 2) 58806192 ++ w) 1)).
  {
    apply (sTDN [20; 0] 34 ((51, 2) :: (1, 1) :: repeat (1, 2) 199 ++ (659, 2) :: (1, 1) :: repeat (1, 2) 7710 ++ (33987, 2) :: (1, 1) :: repeat (1, 2) 308090 ++ (3396738, 2) :: (1, 1) :: repeat (1, 2) 7965811 ++ (18372851, 2) :: (1, 1) :: repeat (1, 2) 58806192 ++ w) 1).
  }
  (* step 47: sTUP *)
  apply (hsteps_trans _ (HC [20; 0] 34 3 2 ((49, 2) :: (1, 1) :: repeat (1, 2) 199 ++ (659, 2) :: (1, 1) :: repeat (1, 2) 7710 ++ (33987, 2) :: (1, 1) :: repeat (1, 2) 308090 ++ (3396738, 2) :: (1, 1) :: repeat (1, 2) 7965811 ++ (18372851, 2) :: (1, 1) :: repeat (1, 2) 58806192 ++ w) 1)).
  {
    replace ((49, 2) :: (1, 1) :: repeat (1, 2) 199 ++ (659, 2) :: (1, 1) :: repeat (1, 2) 7710 ++ (33987, 2) :: (1, 1) :: repeat (1, 2) 308090 ++ (3396738, 2) :: (1, 1) :: repeat (1, 2) 7965811 ++ (18372851, 2) :: (1, 1) :: repeat (1, 2) 58806192 ++ w) with ((51 - 2, 2) :: (1, 1) :: repeat (1, 2) 199 ++ (659, 2) :: (1, 1) :: repeat (1, 2) 7710 ++ (33987, 2) :: (1, 1) :: repeat (1, 2) 308090 ++ (3396738, 2) :: (1, 1) :: repeat (1, 2) 7965811 ++ (18372851, 2) :: (1, 1) :: repeat (1, 2) 58806192 ++ w) by sec_eq.
    apply (sTUP [20; 0] 34 4 51 2 ((1, 1) :: repeat (1, 2) 199 ++ (659, 2) :: (1, 1) :: repeat (1, 2) 7710 ++ (33987, 2) :: (1, 1) :: repeat (1, 2) 308090 ++ (3396738, 2) :: (1, 1) :: repeat (1, 2) 7965811 ++ (18372851, 2) :: (1, 1) :: repeat (1, 2) 58806192 ++ w) 1); closearith.
  }
  (* step 48: CLEANG_odd 23 *)
  apply (hsteps_trans _ (HB [20; 0] 34 1 54 (repeat (1, 2) 1 ++ (1, 1) :: repeat (1, 2) 199 ++ (659, 2) :: (1, 1) :: repeat (1, 2) 7710 ++ (33987, 2) :: (1, 1) :: repeat (1, 2) 308090 ++ (3396738, 2) :: (1, 1) :: repeat (1, 2) 7965811 ++ (18372851, 2) :: (1, 1) :: repeat (1, 2) 58806192 ++ w) 1)).
  {
    replace (repeat (1, 2) 1 ++ (1, 1) :: repeat (1, 2) 199 ++ (659, 2) :: (1, 1) :: repeat (1, 2) 7710 ++ (33987, 2) :: (1, 1) :: repeat (1, 2) 308090 ++ (3396738, 2) :: (1, 1) :: repeat (1, 2) 7965811 ++ (18372851, 2) :: (1, 1) :: repeat (1, 2) 58806192 ++ w) with ((1, 2) :: (1, 1) :: repeat (1, 2) 199 ++ (659, 2) :: (1, 1) :: repeat (1, 2) 7710 ++ (33987, 2) :: (1, 1) :: repeat (1, 2) 308090 ++ (3396738, 2) :: (1, 1) :: repeat (1, 2) 7965811 ++ (18372851, 2) :: (1, 1) :: repeat (1, 2) 58806192 ++ w) by sec_eq.
    apply (CLEANG_odd 23 [20; 0] 34 ((1, 1) :: repeat (1, 2) 199 ++ (659, 2) :: (1, 1) :: repeat (1, 2) 7710 ++ (33987, 2) :: (1, 1) :: repeat (1, 2) 308090 ++ (3396738, 2) :: (1, 1) :: repeat (1, 2) 7965811 ++ (18372851, 2) :: (1, 1) :: repeat (1, 2) 58806192 ++ w) 1); closearith.
  }
  (* step 49: M pop12 (1,) *)
  apply (hsteps_trans _ (HB [20; 0] 35 1 56 ((1, 1) :: repeat (1, 2) 199 ++ (659, 2) :: (1, 1) :: repeat (1, 2) 7710 ++ (33987, 2) :: (1, 1) :: repeat (1, 2) 308090 ++ (3396738, 2) :: (1, 1) :: repeat (1, 2) 7965811 ++ (18372851, 2) :: (1, 1) :: repeat (1, 2) 58806192 ++ w) 1)).
  {
    apply (pop12 1 [20; 0] 34 54 ((1, 1) :: repeat (1, 2) 199 ++ (659, 2) :: (1, 1) :: repeat (1, 2) 7710 ++ (33987, 2) :: (1, 1) :: repeat (1, 2) 308090 ++ (3396738, 2) :: (1, 1) :: repeat (1, 2) 7965811 ++ (18372851, 2) :: (1, 1) :: repeat (1, 2) 58806192 ++ w) 1); closearith.
  }
  (* step 50: P POP *)
  apply (hsteps_trans _ (HB [20; 0] 36 1 57 (repeat (1, 2) 199 ++ (659, 2) :: (1, 1) :: repeat (1, 2) 7710 ++ (33987, 2) :: (1, 1) :: repeat (1, 2) 308090 ++ (3396738, 2) :: (1, 1) :: repeat (1, 2) 7965811 ++ (18372851, 2) :: (1, 1) :: repeat (1, 2) 58806192 ++ w) 1)).
  {
    apply (sPOP1 [20; 0] 35 56 (repeat (1, 2) 199 ++ (659, 2) :: (1, 1) :: repeat (1, 2) 7710 ++ (33987, 2) :: (1, 1) :: repeat (1, 2) 308090 ++ (3396738, 2) :: (1, 1) :: repeat (1, 2) 7965811 ++ (18372851, 2) :: (1, 1) :: repeat (1, 2) 58806192 ++ w) 1); closearith.
  }
  (* step 51: M pop12 (199,) *)
  apply (hsteps_trans _ (HB [20; 0] 235 1 455 ((659, 2) :: (1, 1) :: repeat (1, 2) 7710 ++ (33987, 2) :: (1, 1) :: repeat (1, 2) 308090 ++ (3396738, 2) :: (1, 1) :: repeat (1, 2) 7965811 ++ (18372851, 2) :: (1, 1) :: repeat (1, 2) 58806192 ++ w) 1)).
  {
    apply (pop12 199 [20; 0] 36 57 ((659, 2) :: (1, 1) :: repeat (1, 2) 7710 ++ (33987, 2) :: (1, 1) :: repeat (1, 2) 308090 ++ (3396738, 2) :: (1, 1) :: repeat (1, 2) 7965811 ++ (18372851, 2) :: (1, 1) :: repeat (1, 2) 58806192 ++ w) 1); closearith.
  }
  (* step 52: sTUP *)
  apply (hsteps_trans _ (HC [20; 0] 235 454 2 ((657, 2) :: (1, 1) :: repeat (1, 2) 7710 ++ (33987, 2) :: (1, 1) :: repeat (1, 2) 308090 ++ (3396738, 2) :: (1, 1) :: repeat (1, 2) 7965811 ++ (18372851, 2) :: (1, 1) :: repeat (1, 2) 58806192 ++ w) 1)).
  {
    replace ((657, 2) :: (1, 1) :: repeat (1, 2) 7710 ++ (33987, 2) :: (1, 1) :: repeat (1, 2) 308090 ++ (3396738, 2) :: (1, 1) :: repeat (1, 2) 7965811 ++ (18372851, 2) :: (1, 1) :: repeat (1, 2) 58806192 ++ w) with ((659 - 2, 2) :: (1, 1) :: repeat (1, 2) 7710 ++ (33987, 2) :: (1, 1) :: repeat (1, 2) 308090 ++ (3396738, 2) :: (1, 1) :: repeat (1, 2) 7965811 ++ (18372851, 2) :: (1, 1) :: repeat (1, 2) 58806192 ++ w) by sec_eq.
    apply (sTUP [20; 0] 235 455 659 2 ((1, 1) :: repeat (1, 2) 7710 ++ (33987, 2) :: (1, 1) :: repeat (1, 2) 308090 ++ (3396738, 2) :: (1, 1) :: repeat (1, 2) 7965811 ++ (18372851, 2) :: (1, 1) :: repeat (1, 2) 58806192 ++ w) 1); closearith.
  }
  (* step 53: hGRIND_even 225 *)
  apply (hsteps_trans _ (HB [20; 0] 234 1 454 ((2, 2) :: (657, 2) :: (1, 1) :: repeat (1, 2) 7710 ++ (33987, 2) :: (1, 1) :: repeat (1, 2) 308090 ++ (3396738, 2) :: (1, 1) :: repeat (1, 2) 7965811 ++ (18372851, 2) :: (1, 1) :: repeat (1, 2) 58806192 ++ w) 1)).
  {
    apply (hGRIND_even 225 [20; 0] 234 ((657, 2) :: (1, 1) :: repeat (1, 2) 7710 ++ (33987, 2) :: (1, 1) :: repeat (1, 2) 308090 ++ (3396738, 2) :: (1, 1) :: repeat (1, 2) 7965811 ++ (18372851, 2) :: (1, 1) :: repeat (1, 2) 58806192 ++ w) 1); closearith.
  }
  (* step 54: P TUP2_1 *)
  apply (hsteps_trans _ (HC [235; 20; 0] 454 1 2 ((655, 2) :: (1, 1) :: repeat (1, 2) 7710 ++ (33987, 2) :: (1, 1) :: repeat (1, 2) 308090 ++ (3396738, 2) :: (1, 1) :: repeat (1, 2) 7965811 ++ (18372851, 2) :: (1, 1) :: repeat (1, 2) 58806192 ++ w) 1)).
  {
    replace ((655, 2) :: (1, 1) :: repeat (1, 2) 7710 ++ (33987, 2) :: (1, 1) :: repeat (1, 2) 308090 ++ (3396738, 2) :: (1, 1) :: repeat (1, 2) 7965811 ++ (18372851, 2) :: (1, 1) :: repeat (1, 2) 58806192 ++ w) with ((657 - 2, 2) :: (1, 1) :: repeat (1, 2) 7710 ++ (33987, 2) :: (1, 1) :: repeat (1, 2) 308090 ++ (3396738, 2) :: (1, 1) :: repeat (1, 2) 7965811 ++ (18372851, 2) :: (1, 1) :: repeat (1, 2) 58806192 ++ w) by sec_eq.
    apply (sTUP2_1 [20; 0] 234 453 657 ((1, 1) :: repeat (1, 2) 7710 ++ (33987, 2) :: (1, 1) :: repeat (1, 2) 308090 ++ (3396738, 2) :: (1, 1) :: repeat (1, 2) 7965811 ++ (18372851, 2) :: (1, 1) :: repeat (1, 2) 58806192 ++ w) 1); closearith.
  }
  (* step 55: P TDN *)
  apply (hsteps_trans _ (HB [235; 20; 0] 454 1 4 ((655, 2) :: (1, 1) :: repeat (1, 2) 7710 ++ (33987, 2) :: (1, 1) :: repeat (1, 2) 308090 ++ (3396738, 2) :: (1, 1) :: repeat (1, 2) 7965811 ++ (18372851, 2) :: (1, 1) :: repeat (1, 2) 58806192 ++ w) 1)).
  {
    apply (sTDN [235; 20; 0] 454 ((655, 2) :: (1, 1) :: repeat (1, 2) 7710 ++ (33987, 2) :: (1, 1) :: repeat (1, 2) 308090 ++ (3396738, 2) :: (1, 1) :: repeat (1, 2) 7965811 ++ (18372851, 2) :: (1, 1) :: repeat (1, 2) 58806192 ++ w) 1).
  }
  (* step 56: sTUP *)
  replace ((653, 2) :: (1, 1) :: repeat (1, 2) 7710 ++ (33987, 2) :: (1, 1) :: repeat (1, 2) 308090 ++ (3396738, 2) :: (1, 1) :: repeat (1, 2) 7965811 ++ (18372851, 2) :: (1, 1) :: repeat (1, 2) 58806192 ++ w) with ((655 - 2, 2) :: (1, 1) :: repeat (1, 2) 7710 ++ (33987, 2) :: (1, 1) :: repeat (1, 2) 308090 ++ (3396738, 2) :: (1, 1) :: repeat (1, 2) 7965811 ++ (18372851, 2) :: (1, 1) :: repeat (1, 2) 58806192 ++ w) by sec_eq.
  apply (sTUP [235; 20; 0] 454 4 655 2 ((1, 1) :: repeat (1, 2) 7710 ++ (33987, 2) :: (1, 1) :: repeat (1, 2) 308090 ++ (3396738, 2) :: (1, 1) :: repeat (1, 2) 7965811 ++ (18372851, 2) :: (1, 1) :: repeat (1, 2) 58806192 ++ w) 1); closearith.
Qed.

(* CASCADE60b: steps 57-112 of the CASCADE60 chain. *)
Lemma CASCADE60b : forall w,
  hsteps (HC [235; 20; 0] 454 3 2 ((653, 2) :: (1, 1) :: repeat (1, 2) 7710 ++ (33987, 2) :: (1, 1) :: repeat (1, 2) 308090 ++ (3396738, 2) :: (1, 1) :: repeat (1, 2) 7965811 ++ (18372851, 2) :: (1, 1) :: repeat (1, 2) 58806192 ++ w) 1)
         (HC [0] 3 1 2 ((13, 2) :: (1, 1) :: repeat (1, 2) 34 ++ (140, 2) :: (1, 1) :: repeat (1, 2) 474 ++ (6744, 2) :: (1, 1) :: repeat (1, 2) 16082 ++ (1821, 2) :: (1, 1) :: repeat (1, 2) 308090 ++ (3396738, 2) :: (1, 1) :: repeat (1, 2) 7965811 ++ (18372851, 2) :: (1, 1) :: repeat (1, 2) 58806192 ++ w) 1).
Proof.
  intro w.
  (* step 57: CLEANG_odd 325 *)
  apply (hsteps_trans _ (HB [235; 20; 0] 454 1 658 (repeat (1, 2) 1 ++ (1, 1) :: repeat (1, 2) 7710 ++ (33987, 2) :: (1, 1) :: repeat (1, 2) 308090 ++ (3396738, 2) :: (1, 1) :: repeat (1, 2) 7965811 ++ (18372851, 2) :: (1, 1) :: repeat (1, 2) 58806192 ++ w) 1)).
  {
    replace (repeat (1, 2) 1 ++ (1, 1) :: repeat (1, 2) 7710 ++ (33987, 2) :: (1, 1) :: repeat (1, 2) 308090 ++ (3396738, 2) :: (1, 1) :: repeat (1, 2) 7965811 ++ (18372851, 2) :: (1, 1) :: repeat (1, 2) 58806192 ++ w) with ((1, 2) :: (1, 1) :: repeat (1, 2) 7710 ++ (33987, 2) :: (1, 1) :: repeat (1, 2) 308090 ++ (3396738, 2) :: (1, 1) :: repeat (1, 2) 7965811 ++ (18372851, 2) :: (1, 1) :: repeat (1, 2) 58806192 ++ w) by sec_eq.
    apply (CLEANG_odd 325 [235; 20; 0] 454 ((1, 1) :: repeat (1, 2) 7710 ++ (33987, 2) :: (1, 1) :: repeat (1, 2) 308090 ++ (3396738, 2) :: (1, 1) :: repeat (1, 2) 7965811 ++ (18372851, 2) :: (1, 1) :: repeat (1, 2) 58806192 ++ w) 1); closearith.
  }
  (* step 58: M pop12 (1,) *)
  apply (hsteps_trans _ (HB [235; 20; 0] 455 1 660 ((1, 1) :: repeat (1, 2) 7710 ++ (33987, 2) :: (1, 1) :: repeat (1, 2) 308090 ++ (3396738, 2) :: (1, 1) :: repeat (1, 2) 7965811 ++ (18372851, 2) :: (1, 1) :: repeat (1, 2) 58806192 ++ w) 1)).
  {
    apply (pop12 1 [235; 20; 0] 454 658 ((1, 1) :: repeat (1, 2) 7710 ++ (33987, 2) :: (1, 1) :: repeat (1, 2) 308090 ++ (3396738, 2) :: (1, 1) :: repeat (1, 2) 7965811 ++ (18372851, 2) :: (1, 1) :: repeat (1, 2) 58806192 ++ w) 1); closearith.
  }
  (* step 59: P POP *)
  apply (hsteps_trans _ (HB [235; 20; 0] 456 1 661 (repeat (1, 2) 7710 ++ (33987, 2) :: (1, 1) :: repeat (1, 2) 308090 ++ (3396738, 2) :: (1, 1) :: repeat (1, 2) 7965811 ++ (18372851, 2) :: (1, 1) :: repeat (1, 2) 58806192 ++ w) 1)).
  {
    apply (sPOP1 [235; 20; 0] 455 660 (repeat (1, 2) 7710 ++ (33987, 2) :: (1, 1) :: repeat (1, 2) 308090 ++ (3396738, 2) :: (1, 1) :: repeat (1, 2) 7965811 ++ (18372851, 2) :: (1, 1) :: repeat (1, 2) 58806192 ++ w) 1); closearith.
  }
  (* step 60: M pop12 (7710,) *)
  apply (hsteps_trans _ (HB [235; 20; 0] 8166 1 16081 ((33987, 2) :: (1, 1) :: repeat (1, 2) 308090 ++ (3396738, 2) :: (1, 1) :: repeat (1, 2) 7965811 ++ (18372851, 2) :: (1, 1) :: repeat (1, 2) 58806192 ++ w) 1)).
  {
    apply (pop12 7710 [235; 20; 0] 456 661 ((33987, 2) :: (1, 1) :: repeat (1, 2) 308090 ++ (3396738, 2) :: (1, 1) :: repeat (1, 2) 7965811 ++ (18372851, 2) :: (1, 1) :: repeat (1, 2) 58806192 ++ w) 1); closearith.
  }
  (* step 61: sTUP *)
  apply (hsteps_trans _ (HC [235; 20; 0] 8166 16080 2 ((33985, 2) :: (1, 1) :: repeat (1, 2) 308090 ++ (3396738, 2) :: (1, 1) :: repeat (1, 2) 7965811 ++ (18372851, 2) :: (1, 1) :: repeat (1, 2) 58806192 ++ w) 1)).
  {
    replace ((33985, 2) :: (1, 1) :: repeat (1, 2) 308090 ++ (3396738, 2) :: (1, 1) :: repeat (1, 2) 7965811 ++ (18372851, 2) :: (1, 1) :: repeat (1, 2) 58806192 ++ w) with ((33987 - 2, 2) :: (1, 1) :: repeat (1, 2) 308090 ++ (3396738, 2) :: (1, 1) :: repeat (1, 2) 7965811 ++ (18372851, 2) :: (1, 1) :: repeat (1, 2) 58806192 ++ w) by sec_eq.
    apply (sTUP [235; 20; 0] 8166 16081 33987 2 ((1, 1) :: repeat (1, 2) 308090 ++ (3396738, 2) :: (1, 1) :: repeat (1, 2) 7965811 ++ (18372851, 2) :: (1, 1) :: repeat (1, 2) 58806192 ++ w) 1); closearith.
  }
  (* step 62: hGRIND_even 8038 *)
  apply (hsteps_trans _ (HB [235; 20; 0] 8165 1 16080 ((2, 2) :: (33985, 2) :: (1, 1) :: repeat (1, 2) 308090 ++ (3396738, 2) :: (1, 1) :: repeat (1, 2) 7965811 ++ (18372851, 2) :: (1, 1) :: repeat (1, 2) 58806192 ++ w) 1)).
  {
    rewrite NUM60X9.
    apply (hGRIND_even 8038 [235; 20; 0] 8165 ((33985, 2) :: (1, 1) :: repeat (1, 2) 308090 ++ (3396738, 2) :: (1, 1) :: repeat (1, 2) 7965811 ++ (18372851, 2) :: (1, 1) :: repeat (1, 2) 58806192 ++ w) 1); closearith.
  }
  (* step 63: P TUP2_1 *)
  apply (hsteps_trans _ (HC [8166; 235; 20; 0] 16080 1 2 ((33983, 2) :: (1, 1) :: repeat (1, 2) 308090 ++ (3396738, 2) :: (1, 1) :: repeat (1, 2) 7965811 ++ (18372851, 2) :: (1, 1) :: repeat (1, 2) 58806192 ++ w) 1)).
  {
    replace ((33983, 2) :: (1, 1) :: repeat (1, 2) 308090 ++ (3396738, 2) :: (1, 1) :: repeat (1, 2) 7965811 ++ (18372851, 2) :: (1, 1) :: repeat (1, 2) 58806192 ++ w) with ((33985 - 2, 2) :: (1, 1) :: repeat (1, 2) 308090 ++ (3396738, 2) :: (1, 1) :: repeat (1, 2) 7965811 ++ (18372851, 2) :: (1, 1) :: repeat (1, 2) 58806192 ++ w) by sec_eq.
    apply (sTUP2_1 [235; 20; 0] 8165 16079 33985 ((1, 1) :: repeat (1, 2) 308090 ++ (3396738, 2) :: (1, 1) :: repeat (1, 2) 7965811 ++ (18372851, 2) :: (1, 1) :: repeat (1, 2) 58806192 ++ w) 1); closearith.
  }
  (* step 64: P TDN *)
  apply (hsteps_trans _ (HB [8166; 235; 20; 0] 16080 1 4 ((33983, 2) :: (1, 1) :: repeat (1, 2) 308090 ++ (3396738, 2) :: (1, 1) :: repeat (1, 2) 7965811 ++ (18372851, 2) :: (1, 1) :: repeat (1, 2) 58806192 ++ w) 1)).
  {
    apply (sTDN [8166; 235; 20; 0] 16080 ((33983, 2) :: (1, 1) :: repeat (1, 2) 308090 ++ (3396738, 2) :: (1, 1) :: repeat (1, 2) 7965811 ++ (18372851, 2) :: (1, 1) :: repeat (1, 2) 58806192 ++ w) 1).
  }
  (* step 65: sTUP *)
  apply (hsteps_trans _ (HC [8166; 235; 20; 0] 16080 3 2 ((33981, 2) :: (1, 1) :: repeat (1, 2) 308090 ++ (3396738, 2) :: (1, 1) :: repeat (1, 2) 7965811 ++ (18372851, 2) :: (1, 1) :: repeat (1, 2) 58806192 ++ w) 1)).
  {
    replace ((33981, 2) :: (1, 1) :: repeat (1, 2) 308090 ++ (3396738, 2) :: (1, 1) :: repeat (1, 2) 7965811 ++ (18372851, 2) :: (1, 1) :: repeat (1, 2) 58806192 ++ w) with ((33983 - 2, 2) :: (1, 1) :: repeat (1, 2) 308090 ++ (3396738, 2) :: (1, 1) :: repeat (1, 2) 7965811 ++ (18372851, 2) :: (1, 1) :: repeat (1, 2) 58806192 ++ w) by sec_eq.
    apply (sTUP [8166; 235; 20; 0] 16080 4 33983 2 ((1, 1) :: repeat (1, 2) 308090 ++ (3396738, 2) :: (1, 1) :: repeat (1, 2) 7965811 ++ (18372851, 2) :: (1, 1) :: repeat (1, 2) 58806192 ++ w) 1); closearith.
  }
  (* step 66: DIPGRIND 16080 1821 *)
  apply (hsteps_trans _ (HC [8166; 235; 20; 0] 0 3 2 (repeat (1, 2) 16080 ++ (1821, 2) :: (1, 1) :: repeat (1, 2) 308090 ++ (3396738, 2) :: (1, 1) :: repeat (1, 2) 7965811 ++ (18372851, 2) :: (1, 1) :: repeat (1, 2) 58806192 ++ w) 1)).
  {
    apply (DIPGRIND 16080 1821 [8166; 235; 20; 0] ((1, 1) :: repeat (1, 2) 308090 ++ (3396738, 2) :: (1, 1) :: repeat (1, 2) 7965811 ++ (18372851, 2) :: (1, 1) :: repeat (1, 2) 58806192 ++ w) 1); closearith.
  }
  (* step 67: P PX2A *)
  apply (hsteps_trans _ (HC [20; 0] 234 8164 2 ((1, 1) :: repeat (1, 2) 16082 ++ (1821, 2) :: (1, 1) :: repeat (1, 2) 308090 ++ (3396738, 2) :: (1, 1) :: repeat (1, 2) 7965811 ++ (18372851, 2) :: (1, 1) :: repeat (1, 2) 58806192 ++ w) 1)).
  {
    exact (hsteps_step _ _ _ (hPX2A 8163 234 [20; 0] (repeat (1, 2) 16080 ++ (1821, 2) :: (1, 1) :: repeat (1, 2) 308090 ++ (3396738, 2) :: (1, 1) :: repeat (1, 2) 7965811 ++ (18372851, 2) :: (1, 1) :: repeat (1, 2) 58806192 ++ w) 1) (hsteps_refl _)).
  }
  (* step 68: P PUSH *)
  apply (hsteps_trans _ (HC [20; 0] 233 1 2 ((8162, 2) :: (1, 1) :: repeat (1, 2) 16082 ++ (1821, 2) :: (1, 1) :: repeat (1, 2) 308090 ++ (3396738, 2) :: (1, 1) :: repeat (1, 2) 7965811 ++ (18372851, 2) :: (1, 1) :: repeat (1, 2) 58806192 ++ w) 1)).
  {
    replace ((8162, 2) :: (1, 1) :: repeat (1, 2) 16082 ++ (1821, 2) :: (1, 1) :: repeat (1, 2) 308090 ++ (3396738, 2) :: (1, 1) :: repeat (1, 2) 7965811 ++ (18372851, 2) :: (1, 1) :: repeat (1, 2) 58806192 ++ w) with ((8164 - 2, 2) :: (1, 1) :: repeat (1, 2) 16082 ++ (1821, 2) :: (1, 1) :: repeat (1, 2) 308090 ++ (3396738, 2) :: (1, 1) :: repeat (1, 2) 7965811 ++ (18372851, 2) :: (1, 1) :: repeat (1, 2) 58806192 ++ w) by sec_eq.
    apply (sPUSH [20; 0] 233 8164 ((1, 1) :: repeat (1, 2) 16082 ++ (1821, 2) :: (1, 1) :: repeat (1, 2) 308090 ++ (3396738, 2) :: (1, 1) :: repeat (1, 2) 7965811 ++ (18372851, 2) :: (1, 1) :: repeat (1, 2) 58806192 ++ w) 1); closearith.
  }
  (* step 69: P TDN *)
  apply (hsteps_trans _ (HB [20; 0] 233 1 4 ((8162, 2) :: (1, 1) :: repeat (1, 2) 16082 ++ (1821, 2) :: (1, 1) :: repeat (1, 2) 308090 ++ (3396738, 2) :: (1, 1) :: repeat (1, 2) 7965811 ++ (18372851, 2) :: (1, 1) :: repeat (1, 2) 58806192 ++ w) 1)).
  {
    apply (sTDN [20; 0] 233 ((8162, 2) :: (1, 1) :: repeat (1, 2) 16082 ++ (1821, 2) :: (1, 1) :: repeat (1, 2) 308090 ++ (3396738, 2) :: (1, 1) :: repeat (1, 2) 7965811 ++ (18372851, 2) :: (1, 1) :: repeat (1, 2) 58806192 ++ w) 1).
  }
  (* step 70: sTUP *)
  apply (hsteps_trans _ (HC [20; 0] 233 3 2 ((8160, 2) :: (1, 1) :: repeat (1, 2) 16082 ++ (1821, 2) :: (1, 1) :: repeat (1, 2) 308090 ++ (3396738, 2) :: (1, 1) :: repeat (1, 2) 7965811 ++ (18372851, 2) :: (1, 1) :: repeat (1, 2) 58806192 ++ w) 1)).
  {
    replace ((8160, 2) :: (1, 1) :: repeat (1, 2) 16082 ++ (1821, 2) :: (1, 1) :: repeat (1, 2) 308090 ++ (3396738, 2) :: (1, 1) :: repeat (1, 2) 7965811 ++ (18372851, 2) :: (1, 1) :: repeat (1, 2) 58806192 ++ w) with ((8162 - 2, 2) :: (1, 1) :: repeat (1, 2) 16082 ++ (1821, 2) :: (1, 1) :: repeat (1, 2) 308090 ++ (3396738, 2) :: (1, 1) :: repeat (1, 2) 7965811 ++ (18372851, 2) :: (1, 1) :: repeat (1, 2) 58806192 ++ w) by sec_eq.
    apply (sTUP [20; 0] 233 4 8162 2 ((1, 1) :: repeat (1, 2) 16082 ++ (1821, 2) :: (1, 1) :: repeat (1, 2) 308090 ++ (3396738, 2) :: (1, 1) :: repeat (1, 2) 7965811 ++ (18372851, 2) :: (1, 1) :: repeat (1, 2) 58806192 ++ w) 1); closearith.
  }
  (* step 71: DIPGRIND 233 7694 *)
  apply (hsteps_trans _ (HC [20; 0] 0 3 2 (repeat (1, 2) 233 ++ (7694, 2) :: (1, 1) :: repeat (1, 2) 16082 ++ (1821, 2) :: (1, 1) :: repeat (1, 2) 308090 ++ (3396738, 2) :: (1, 1) :: repeat (1, 2) 7965811 ++ (18372851, 2) :: (1, 1) :: repeat (1, 2) 58806192 ++ w) 1)).
  {
    apply (DIPGRIND 233 7694 [20; 0] ((1, 1) :: repeat (1, 2) 16082 ++ (1821, 2) :: (1, 1) :: repeat (1, 2) 308090 ++ (3396738, 2) :: (1, 1) :: repeat (1, 2) 7965811 ++ (18372851, 2) :: (1, 1) :: repeat (1, 2) 58806192 ++ w) 1); closearith.
  }
  (* step 72: P PX2A0 *)
  apply (hsteps_trans _ (HB [0] 3 1 2 ((16, 2) :: (1, 1) :: repeat (1, 2) 235 ++ (7694, 2) :: (1, 1) :: repeat (1, 2) 16082 ++ (1821, 2) :: (1, 1) :: repeat (1, 2) 308090 ++ (3396738, 2) :: (1, 1) :: repeat (1, 2) 7965811 ++ (18372851, 2) :: (1, 1) :: repeat (1, 2) 58806192 ++ w) 1)).
  {
    exact (hsteps_step _ _ _ (hPX2A0 15 (repeat (1, 2) 233 ++ (7694, 2) :: (1, 1) :: repeat (1, 2) 16082 ++ (1821, 2) :: (1, 1) :: repeat (1, 2) 308090 ++ (3396738, 2) :: (1, 1) :: repeat (1, 2) 7965811 ++ (18372851, 2) :: (1, 1) :: repeat (1, 2) 58806192 ++ w) 1) (hsteps_refl _)).
  }
  (* step 73: sTUP *)
  apply (hsteps_trans _ (HC [0] 3 1 2 ((14, 2) :: (1, 1) :: repeat (1, 2) 235 ++ (7694, 2) :: (1, 1) :: repeat (1, 2) 16082 ++ (1821, 2) :: (1, 1) :: repeat (1, 2) 308090 ++ (3396738, 2) :: (1, 1) :: repeat (1, 2) 7965811 ++ (18372851, 2) :: (1, 1) :: repeat (1, 2) 58806192 ++ w) 1)).
  {
    replace ((14, 2) :: (1, 1) :: repeat (1, 2) 235 ++ (7694, 2) :: (1, 1) :: repeat (1, 2) 16082 ++ (1821, 2) :: (1, 1) :: repeat (1, 2) 308090 ++ (3396738, 2) :: (1, 1) :: repeat (1, 2) 7965811 ++ (18372851, 2) :: (1, 1) :: repeat (1, 2) 58806192 ++ w) with ((16 - 2, 2) :: (1, 1) :: repeat (1, 2) 235 ++ (7694, 2) :: (1, 1) :: repeat (1, 2) 16082 ++ (1821, 2) :: (1, 1) :: repeat (1, 2) 308090 ++ (3396738, 2) :: (1, 1) :: repeat (1, 2) 7965811 ++ (18372851, 2) :: (1, 1) :: repeat (1, 2) 58806192 ++ w) by sec_eq.
    apply (sTUP [0] 3 2 16 2 ((1, 1) :: repeat (1, 2) 235 ++ (7694, 2) :: (1, 1) :: repeat (1, 2) 16082 ++ (1821, 2) :: (1, 1) :: repeat (1, 2) 308090 ++ (3396738, 2) :: (1, 1) :: repeat (1, 2) 7965811 ++ (18372851, 2) :: (1, 1) :: repeat (1, 2) 58806192 ++ w) 1); closearith.
  }
  (* step 74: P TDN *)
  apply (hsteps_trans _ (HB [0] 3 1 4 ((14, 2) :: (1, 1) :: repeat (1, 2) 235 ++ (7694, 2) :: (1, 1) :: repeat (1, 2) 16082 ++ (1821, 2) :: (1, 1) :: repeat (1, 2) 308090 ++ (3396738, 2) :: (1, 1) :: repeat (1, 2) 7965811 ++ (18372851, 2) :: (1, 1) :: repeat (1, 2) 58806192 ++ w) 1)).
  {
    apply (sTDN [0] 3 ((14, 2) :: (1, 1) :: repeat (1, 2) 235 ++ (7694, 2) :: (1, 1) :: repeat (1, 2) 16082 ++ (1821, 2) :: (1, 1) :: repeat (1, 2) 308090 ++ (3396738, 2) :: (1, 1) :: repeat (1, 2) 7965811 ++ (18372851, 2) :: (1, 1) :: repeat (1, 2) 58806192 ++ w) 1).
  }
  (* step 75: sTUP *)
  apply (hsteps_trans _ (HC [0] 3 3 2 ((12, 2) :: (1, 1) :: repeat (1, 2) 235 ++ (7694, 2) :: (1, 1) :: repeat (1, 2) 16082 ++ (1821, 2) :: (1, 1) :: repeat (1, 2) 308090 ++ (3396738, 2) :: (1, 1) :: repeat (1, 2) 7965811 ++ (18372851, 2) :: (1, 1) :: repeat (1, 2) 58806192 ++ w) 1)).
  {
    replace ((12, 2) :: (1, 1) :: repeat (1, 2) 235 ++ (7694, 2) :: (1, 1) :: repeat (1, 2) 16082 ++ (1821, 2) :: (1, 1) :: repeat (1, 2) 308090 ++ (3396738, 2) :: (1, 1) :: repeat (1, 2) 7965811 ++ (18372851, 2) :: (1, 1) :: repeat (1, 2) 58806192 ++ w) with ((14 - 2, 2) :: (1, 1) :: repeat (1, 2) 235 ++ (7694, 2) :: (1, 1) :: repeat (1, 2) 16082 ++ (1821, 2) :: (1, 1) :: repeat (1, 2) 308090 ++ (3396738, 2) :: (1, 1) :: repeat (1, 2) 7965811 ++ (18372851, 2) :: (1, 1) :: repeat (1, 2) 58806192 ++ w) by sec_eq.
    apply (sTUP [0] 3 4 14 2 ((1, 1) :: repeat (1, 2) 235 ++ (7694, 2) :: (1, 1) :: repeat (1, 2) 16082 ++ (1821, 2) :: (1, 1) :: repeat (1, 2) 308090 ++ (3396738, 2) :: (1, 1) :: repeat (1, 2) 7965811 ++ (18372851, 2) :: (1, 1) :: repeat (1, 2) 58806192 ++ w) 1); closearith.
  }
  (* step 76: DIPGRIND 3 6 *)
  apply (hsteps_trans _ (HC [0] 0 3 2 (repeat (1, 2) 3 ++ (6, 2) :: (1, 1) :: repeat (1, 2) 235 ++ (7694, 2) :: (1, 1) :: repeat (1, 2) 16082 ++ (1821, 2) :: (1, 1) :: repeat (1, 2) 308090 ++ (3396738, 2) :: (1, 1) :: repeat (1, 2) 7965811 ++ (18372851, 2) :: (1, 1) :: repeat (1, 2) 58806192 ++ w) 1)).
  {
    apply (DIPGRIND 3 6 [0] ((1, 1) :: repeat (1, 2) 235 ++ (7694, 2) :: (1, 1) :: repeat (1, 2) 16082 ++ (1821, 2) :: (1, 1) :: repeat (1, 2) 308090 ++ (3396738, 2) :: (1, 1) :: repeat (1, 2) 7965811 ++ (18372851, 2) :: (1, 1) :: repeat (1, 2) 58806192 ++ w) 1); closearith.
  }
  (* step 77: P PX2B0 *)
  apply (hsteps_trans _ (HB [] 0 1 5 (repeat (1, 2) 4 ++ (6, 2) :: (1, 1) :: repeat (1, 2) 235 ++ (7694, 2) :: (1, 1) :: repeat (1, 2) 16082 ++ (1821, 2) :: (1, 1) :: repeat (1, 2) 308090 ++ (3396738, 2) :: (1, 1) :: repeat (1, 2) 7965811 ++ (18372851, 2) :: (1, 1) :: repeat (1, 2) 58806192 ++ w) 1)).
  {
    exact (hsteps_step _ _ _ (hPX2B0 (repeat (1, 2) 3 ++ (6, 2) :: (1, 1) :: repeat (1, 2) 235 ++ (7694, 2) :: (1, 1) :: repeat (1, 2) 16082 ++ (1821, 2) :: (1, 1) :: repeat (1, 2) 308090 ++ (3396738, 2) :: (1, 1) :: repeat (1, 2) 7965811 ++ (18372851, 2) :: (1, 1) :: repeat (1, 2) 58806192 ++ w) 1) (hsteps_refl _)).
  }
  (* step 78: M pop12 (4,) *)
  apply (hsteps_trans _ (HB [] 4 1 13 ((6, 2) :: (1, 1) :: repeat (1, 2) 235 ++ (7694, 2) :: (1, 1) :: repeat (1, 2) 16082 ++ (1821, 2) :: (1, 1) :: repeat (1, 2) 308090 ++ (3396738, 2) :: (1, 1) :: repeat (1, 2) 7965811 ++ (18372851, 2) :: (1, 1) :: repeat (1, 2) 58806192 ++ w) 1)).
  {
    apply (pop12 4 [] 0 5 ((6, 2) :: (1, 1) :: repeat (1, 2) 235 ++ (7694, 2) :: (1, 1) :: repeat (1, 2) 16082 ++ (1821, 2) :: (1, 1) :: repeat (1, 2) 308090 ++ (3396738, 2) :: (1, 1) :: repeat (1, 2) 7965811 ++ (18372851, 2) :: (1, 1) :: repeat (1, 2) 58806192 ++ w) 1); closearith.
  }
  (* step 79: sTUP *)
  apply (hsteps_trans _ (HC [] 4 12 2 ((4, 2) :: (1, 1) :: repeat (1, 2) 235 ++ (7694, 2) :: (1, 1) :: repeat (1, 2) 16082 ++ (1821, 2) :: (1, 1) :: repeat (1, 2) 308090 ++ (3396738, 2) :: (1, 1) :: repeat (1, 2) 7965811 ++ (18372851, 2) :: (1, 1) :: repeat (1, 2) 58806192 ++ w) 1)).
  {
    replace ((4, 2) :: (1, 1) :: repeat (1, 2) 235 ++ (7694, 2) :: (1, 1) :: repeat (1, 2) 16082 ++ (1821, 2) :: (1, 1) :: repeat (1, 2) 308090 ++ (3396738, 2) :: (1, 1) :: repeat (1, 2) 7965811 ++ (18372851, 2) :: (1, 1) :: repeat (1, 2) 58806192 ++ w) with ((6 - 2, 2) :: (1, 1) :: repeat (1, 2) 235 ++ (7694, 2) :: (1, 1) :: repeat (1, 2) 16082 ++ (1821, 2) :: (1, 1) :: repeat (1, 2) 308090 ++ (3396738, 2) :: (1, 1) :: repeat (1, 2) 7965811 ++ (18372851, 2) :: (1, 1) :: repeat (1, 2) 58806192 ++ w) by sec_eq.
    apply (sTUP [] 4 13 6 2 ((1, 1) :: repeat (1, 2) 235 ++ (7694, 2) :: (1, 1) :: repeat (1, 2) 16082 ++ (1821, 2) :: (1, 1) :: repeat (1, 2) 308090 ++ (3396738, 2) :: (1, 1) :: repeat (1, 2) 7965811 ++ (18372851, 2) :: (1, 1) :: repeat (1, 2) 58806192 ++ w) 1); closearith.
  }
  (* step 80: P PUSH *)
  apply (hsteps_trans _ (HC [] 3 1 2 ((10, 2) :: (4, 2) :: (1, 1) :: repeat (1, 2) 235 ++ (7694, 2) :: (1, 1) :: repeat (1, 2) 16082 ++ (1821, 2) :: (1, 1) :: repeat (1, 2) 308090 ++ (3396738, 2) :: (1, 1) :: repeat (1, 2) 7965811 ++ (18372851, 2) :: (1, 1) :: repeat (1, 2) 58806192 ++ w) 1)).
  {
    replace ((10, 2) :: (4, 2) :: (1, 1) :: repeat (1, 2) 235 ++ (7694, 2) :: (1, 1) :: repeat (1, 2) 16082 ++ (1821, 2) :: (1, 1) :: repeat (1, 2) 308090 ++ (3396738, 2) :: (1, 1) :: repeat (1, 2) 7965811 ++ (18372851, 2) :: (1, 1) :: repeat (1, 2) 58806192 ++ w) with ((12 - 2, 2) :: (4, 2) :: (1, 1) :: repeat (1, 2) 235 ++ (7694, 2) :: (1, 1) :: repeat (1, 2) 16082 ++ (1821, 2) :: (1, 1) :: repeat (1, 2) 308090 ++ (3396738, 2) :: (1, 1) :: repeat (1, 2) 7965811 ++ (18372851, 2) :: (1, 1) :: repeat (1, 2) 58806192 ++ w) by sec_eq.
    apply (sPUSH [] 3 12 ((4, 2) :: (1, 1) :: repeat (1, 2) 235 ++ (7694, 2) :: (1, 1) :: repeat (1, 2) 16082 ++ (1821, 2) :: (1, 1) :: repeat (1, 2) 308090 ++ (3396738, 2) :: (1, 1) :: repeat (1, 2) 7965811 ++ (18372851, 2) :: (1, 1) :: repeat (1, 2) 58806192 ++ w) 1); closearith.
  }
  (* step 81: P TDN *)
  apply (hsteps_trans _ (HB [] 3 1 4 ((10, 2) :: (4, 2) :: (1, 1) :: repeat (1, 2) 235 ++ (7694, 2) :: (1, 1) :: repeat (1, 2) 16082 ++ (1821, 2) :: (1, 1) :: repeat (1, 2) 308090 ++ (3396738, 2) :: (1, 1) :: repeat (1, 2) 7965811 ++ (18372851, 2) :: (1, 1) :: repeat (1, 2) 58806192 ++ w) 1)).
  {
    apply (sTDN [] 3 ((10, 2) :: (4, 2) :: (1, 1) :: repeat (1, 2) 235 ++ (7694, 2) :: (1, 1) :: repeat (1, 2) 16082 ++ (1821, 2) :: (1, 1) :: repeat (1, 2) 308090 ++ (3396738, 2) :: (1, 1) :: repeat (1, 2) 7965811 ++ (18372851, 2) :: (1, 1) :: repeat (1, 2) 58806192 ++ w) 1).
  }
  (* step 82: sTUP *)
  apply (hsteps_trans _ (HC [] 3 3 2 ((8, 2) :: (4, 2) :: (1, 1) :: repeat (1, 2) 235 ++ (7694, 2) :: (1, 1) :: repeat (1, 2) 16082 ++ (1821, 2) :: (1, 1) :: repeat (1, 2) 308090 ++ (3396738, 2) :: (1, 1) :: repeat (1, 2) 7965811 ++ (18372851, 2) :: (1, 1) :: repeat (1, 2) 58806192 ++ w) 1)).
  {
    replace ((8, 2) :: (4, 2) :: (1, 1) :: repeat (1, 2) 235 ++ (7694, 2) :: (1, 1) :: repeat (1, 2) 16082 ++ (1821, 2) :: (1, 1) :: repeat (1, 2) 308090 ++ (3396738, 2) :: (1, 1) :: repeat (1, 2) 7965811 ++ (18372851, 2) :: (1, 1) :: repeat (1, 2) 58806192 ++ w) with ((10 - 2, 2) :: (4, 2) :: (1, 1) :: repeat (1, 2) 235 ++ (7694, 2) :: (1, 1) :: repeat (1, 2) 16082 ++ (1821, 2) :: (1, 1) :: repeat (1, 2) 308090 ++ (3396738, 2) :: (1, 1) :: repeat (1, 2) 7965811 ++ (18372851, 2) :: (1, 1) :: repeat (1, 2) 58806192 ++ w) by sec_eq.
    apply (sTUP [] 3 4 10 2 ((4, 2) :: (1, 1) :: repeat (1, 2) 235 ++ (7694, 2) :: (1, 1) :: repeat (1, 2) 16082 ++ (1821, 2) :: (1, 1) :: repeat (1, 2) 308090 ++ (3396738, 2) :: (1, 1) :: repeat (1, 2) 7965811 ++ (18372851, 2) :: (1, 1) :: repeat (1, 2) 58806192 ++ w) 1); closearith.
  }
  (* step 83: DIPGRIND 3 2 *)
  apply (hsteps_trans _ (HC [] 0 3 2 (repeat (1, 2) 3 ++ (2, 2) :: (4, 2) :: (1, 1) :: repeat (1, 2) 235 ++ (7694, 2) :: (1, 1) :: repeat (1, 2) 16082 ++ (1821, 2) :: (1, 1) :: repeat (1, 2) 308090 ++ (3396738, 2) :: (1, 1) :: repeat (1, 2) 7965811 ++ (18372851, 2) :: (1, 1) :: repeat (1, 2) 58806192 ++ w) 1)).
  {
    apply (DIPGRIND 3 2 [] ((4, 2) :: (1, 1) :: repeat (1, 2) 235 ++ (7694, 2) :: (1, 1) :: repeat (1, 2) 16082 ++ (1821, 2) :: (1, 1) :: repeat (1, 2) 308090 ++ (3396738, 2) :: (1, 1) :: repeat (1, 2) 7965811 ++ (18372851, 2) :: (1, 1) :: repeat (1, 2) 58806192 ++ w) 1); closearith.
  }
  (* step 84: P PUSHX *)
  apply (hsteps_trans _ (HB [] 1 1 7 (repeat (1, 2) 3 ++ (2, 2) :: (4, 2) :: (1, 1) :: repeat (1, 2) 235 ++ (7694, 2) :: (1, 1) :: repeat (1, 2) 16082 ++ (1821, 2) :: (1, 1) :: repeat (1, 2) 308090 ++ (3396738, 2) :: (1, 1) :: repeat (1, 2) 7965811 ++ (18372851, 2) :: (1, 1) :: repeat (1, 2) 58806192 ++ w) 1)).
  {
    exact (hsteps_step _ _ _ (hPUSHX (repeat (1, 2) 3 ++ (2, 2) :: (4, 2) :: (1, 1) :: repeat (1, 2) 235 ++ (7694, 2) :: (1, 1) :: repeat (1, 2) 16082 ++ (1821, 2) :: (1, 1) :: repeat (1, 2) 308090 ++ (3396738, 2) :: (1, 1) :: repeat (1, 2) 7965811 ++ (18372851, 2) :: (1, 1) :: repeat (1, 2) 58806192 ++ w) 1) (hsteps_refl _)).
  }
  (* step 85: M pop12 (3,) *)
  apply (hsteps_trans _ (HB [] 4 1 13 ((2, 2) :: (4, 2) :: (1, 1) :: repeat (1, 2) 235 ++ (7694, 2) :: (1, 1) :: repeat (1, 2) 16082 ++ (1821, 2) :: (1, 1) :: repeat (1, 2) 308090 ++ (3396738, 2) :: (1, 1) :: repeat (1, 2) 7965811 ++ (18372851, 2) :: (1, 1) :: repeat (1, 2) 58806192 ++ w) 1)).
  {
    apply (pop12 3 [] 1 7 ((2, 2) :: (4, 2) :: (1, 1) :: repeat (1, 2) 235 ++ (7694, 2) :: (1, 1) :: repeat (1, 2) 16082 ++ (1821, 2) :: (1, 1) :: repeat (1, 2) 308090 ++ (3396738, 2) :: (1, 1) :: repeat (1, 2) 7965811 ++ (18372851, 2) :: (1, 1) :: repeat (1, 2) 58806192 ++ w) 1); closearith.
  }
  (* step 86: P TUP2_1 *)
  apply (hsteps_trans _ (HC [5] 13 1 2 ((2, 2) :: (1, 1) :: repeat (1, 2) 235 ++ (7694, 2) :: (1, 1) :: repeat (1, 2) 16082 ++ (1821, 2) :: (1, 1) :: repeat (1, 2) 308090 ++ (3396738, 2) :: (1, 1) :: repeat (1, 2) 7965811 ++ (18372851, 2) :: (1, 1) :: repeat (1, 2) 58806192 ++ w) 1)).
  {
    replace ((2, 2) :: (1, 1) :: repeat (1, 2) 235 ++ (7694, 2) :: (1, 1) :: repeat (1, 2) 16082 ++ (1821, 2) :: (1, 1) :: repeat (1, 2) 308090 ++ (3396738, 2) :: (1, 1) :: repeat (1, 2) 7965811 ++ (18372851, 2) :: (1, 1) :: repeat (1, 2) 58806192 ++ w) with ((4 - 2, 2) :: (1, 1) :: repeat (1, 2) 235 ++ (7694, 2) :: (1, 1) :: repeat (1, 2) 16082 ++ (1821, 2) :: (1, 1) :: repeat (1, 2) 308090 ++ (3396738, 2) :: (1, 1) :: repeat (1, 2) 7965811 ++ (18372851, 2) :: (1, 1) :: repeat (1, 2) 58806192 ++ w) by sec_eq.
    apply (sTUP2_1 [] 4 12 4 ((1, 1) :: repeat (1, 2) 235 ++ (7694, 2) :: (1, 1) :: repeat (1, 2) 16082 ++ (1821, 2) :: (1, 1) :: repeat (1, 2) 308090 ++ (3396738, 2) :: (1, 1) :: repeat (1, 2) 7965811 ++ (18372851, 2) :: (1, 1) :: repeat (1, 2) 58806192 ++ w) 1); closearith.
  }
  (* step 87: P TDN *)
  apply (hsteps_trans _ (HB [5] 13 1 4 ((2, 2) :: (1, 1) :: repeat (1, 2) 235 ++ (7694, 2) :: (1, 1) :: repeat (1, 2) 16082 ++ (1821, 2) :: (1, 1) :: repeat (1, 2) 308090 ++ (3396738, 2) :: (1, 1) :: repeat (1, 2) 7965811 ++ (18372851, 2) :: (1, 1) :: repeat (1, 2) 58806192 ++ w) 1)).
  {
    apply (sTDN [5] 13 ((2, 2) :: (1, 1) :: repeat (1, 2) 235 ++ (7694, 2) :: (1, 1) :: repeat (1, 2) 16082 ++ (1821, 2) :: (1, 1) :: repeat (1, 2) 308090 ++ (3396738, 2) :: (1, 1) :: repeat (1, 2) 7965811 ++ (18372851, 2) :: (1, 1) :: repeat (1, 2) 58806192 ++ w) 1).
  }
  (* step 88: P TRANS2_1 *)
  apply (hsteps_trans _ (HB [14; 5] 5 1 3 (repeat (1, 2) 235 ++ (7694, 2) :: (1, 1) :: repeat (1, 2) 16082 ++ (1821, 2) :: (1, 1) :: repeat (1, 2) 308090 ++ (3396738, 2) :: (1, 1) :: repeat (1, 2) 7965811 ++ (18372851, 2) :: (1, 1) :: repeat (1, 2) 58806192 ++ w) 1)).
  {
    apply (sTRANS2_1 [5] 13 3 1 (repeat (1, 2) 235 ++ (7694, 2) :: (1, 1) :: repeat (1, 2) 16082 ++ (1821, 2) :: (1, 1) :: repeat (1, 2) 308090 ++ (3396738, 2) :: (1, 1) :: repeat (1, 2) 7965811 ++ (18372851, 2) :: (1, 1) :: repeat (1, 2) 58806192 ++ w) 1); closearith.
  }
  (* step 89: M pop12 (235,) *)
  apply (hsteps_trans _ (HB [14; 5] 240 1 473 ((7694, 2) :: (1, 1) :: repeat (1, 2) 16082 ++ (1821, 2) :: (1, 1) :: repeat (1, 2) 308090 ++ (3396738, 2) :: (1, 1) :: repeat (1, 2) 7965811 ++ (18372851, 2) :: (1, 1) :: repeat (1, 2) 58806192 ++ w) 1)).
  {
    apply (pop12 235 [14; 5] 5 3 ((7694, 2) :: (1, 1) :: repeat (1, 2) 16082 ++ (1821, 2) :: (1, 1) :: repeat (1, 2) 308090 ++ (3396738, 2) :: (1, 1) :: repeat (1, 2) 7965811 ++ (18372851, 2) :: (1, 1) :: repeat (1, 2) 58806192 ++ w) 1); closearith.
  }
  (* step 90: sTUP *)
  apply (hsteps_trans _ (HC [14; 5] 240 472 2 ((7692, 2) :: (1, 1) :: repeat (1, 2) 16082 ++ (1821, 2) :: (1, 1) :: repeat (1, 2) 308090 ++ (3396738, 2) :: (1, 1) :: repeat (1, 2) 7965811 ++ (18372851, 2) :: (1, 1) :: repeat (1, 2) 58806192 ++ w) 1)).
  {
    replace ((7692, 2) :: (1, 1) :: repeat (1, 2) 16082 ++ (1821, 2) :: (1, 1) :: repeat (1, 2) 308090 ++ (3396738, 2) :: (1, 1) :: repeat (1, 2) 7965811 ++ (18372851, 2) :: (1, 1) :: repeat (1, 2) 58806192 ++ w) with ((7694 - 2, 2) :: (1, 1) :: repeat (1, 2) 16082 ++ (1821, 2) :: (1, 1) :: repeat (1, 2) 308090 ++ (3396738, 2) :: (1, 1) :: repeat (1, 2) 7965811 ++ (18372851, 2) :: (1, 1) :: repeat (1, 2) 58806192 ++ w) by sec_eq.
    apply (sTUP [14; 5] 240 473 7694 2 ((1, 1) :: repeat (1, 2) 16082 ++ (1821, 2) :: (1, 1) :: repeat (1, 2) 308090 ++ (3396738, 2) :: (1, 1) :: repeat (1, 2) 7965811 ++ (18372851, 2) :: (1, 1) :: repeat (1, 2) 58806192 ++ w) 1); closearith.
  }
  (* step 91: hGRIND_even 234 *)
  apply (hsteps_trans _ (HB [14; 5] 239 1 472 ((2, 2) :: (7692, 2) :: (1, 1) :: repeat (1, 2) 16082 ++ (1821, 2) :: (1, 1) :: repeat (1, 2) 308090 ++ (3396738, 2) :: (1, 1) :: repeat (1, 2) 7965811 ++ (18372851, 2) :: (1, 1) :: repeat (1, 2) 58806192 ++ w) 1)).
  {
    apply (hGRIND_even 234 [14; 5] 239 ((7692, 2) :: (1, 1) :: repeat (1, 2) 16082 ++ (1821, 2) :: (1, 1) :: repeat (1, 2) 308090 ++ (3396738, 2) :: (1, 1) :: repeat (1, 2) 7965811 ++ (18372851, 2) :: (1, 1) :: repeat (1, 2) 58806192 ++ w) 1); closearith.
  }
  (* step 92: P TUP2_1 *)
  apply (hsteps_trans _ (HC [240; 14; 5] 472 1 2 ((7690, 2) :: (1, 1) :: repeat (1, 2) 16082 ++ (1821, 2) :: (1, 1) :: repeat (1, 2) 308090 ++ (3396738, 2) :: (1, 1) :: repeat (1, 2) 7965811 ++ (18372851, 2) :: (1, 1) :: repeat (1, 2) 58806192 ++ w) 1)).
  {
    replace ((7690, 2) :: (1, 1) :: repeat (1, 2) 16082 ++ (1821, 2) :: (1, 1) :: repeat (1, 2) 308090 ++ (3396738, 2) :: (1, 1) :: repeat (1, 2) 7965811 ++ (18372851, 2) :: (1, 1) :: repeat (1, 2) 58806192 ++ w) with ((7692 - 2, 2) :: (1, 1) :: repeat (1, 2) 16082 ++ (1821, 2) :: (1, 1) :: repeat (1, 2) 308090 ++ (3396738, 2) :: (1, 1) :: repeat (1, 2) 7965811 ++ (18372851, 2) :: (1, 1) :: repeat (1, 2) 58806192 ++ w) by sec_eq.
    apply (sTUP2_1 [14; 5] 239 471 7692 ((1, 1) :: repeat (1, 2) 16082 ++ (1821, 2) :: (1, 1) :: repeat (1, 2) 308090 ++ (3396738, 2) :: (1, 1) :: repeat (1, 2) 7965811 ++ (18372851, 2) :: (1, 1) :: repeat (1, 2) 58806192 ++ w) 1); closearith.
  }
  (* step 93: P TDN *)
  apply (hsteps_trans _ (HB [240; 14; 5] 472 1 4 ((7690, 2) :: (1, 1) :: repeat (1, 2) 16082 ++ (1821, 2) :: (1, 1) :: repeat (1, 2) 308090 ++ (3396738, 2) :: (1, 1) :: repeat (1, 2) 7965811 ++ (18372851, 2) :: (1, 1) :: repeat (1, 2) 58806192 ++ w) 1)).
  {
    apply (sTDN [240; 14; 5] 472 ((7690, 2) :: (1, 1) :: repeat (1, 2) 16082 ++ (1821, 2) :: (1, 1) :: repeat (1, 2) 308090 ++ (3396738, 2) :: (1, 1) :: repeat (1, 2) 7965811 ++ (18372851, 2) :: (1, 1) :: repeat (1, 2) 58806192 ++ w) 1).
  }
  (* step 94: sTUP *)
  apply (hsteps_trans _ (HC [240; 14; 5] 472 3 2 ((7688, 2) :: (1, 1) :: repeat (1, 2) 16082 ++ (1821, 2) :: (1, 1) :: repeat (1, 2) 308090 ++ (3396738, 2) :: (1, 1) :: repeat (1, 2) 7965811 ++ (18372851, 2) :: (1, 1) :: repeat (1, 2) 58806192 ++ w) 1)).
  {
    replace ((7688, 2) :: (1, 1) :: repeat (1, 2) 16082 ++ (1821, 2) :: (1, 1) :: repeat (1, 2) 308090 ++ (3396738, 2) :: (1, 1) :: repeat (1, 2) 7965811 ++ (18372851, 2) :: (1, 1) :: repeat (1, 2) 58806192 ++ w) with ((7690 - 2, 2) :: (1, 1) :: repeat (1, 2) 16082 ++ (1821, 2) :: (1, 1) :: repeat (1, 2) 308090 ++ (3396738, 2) :: (1, 1) :: repeat (1, 2) 7965811 ++ (18372851, 2) :: (1, 1) :: repeat (1, 2) 58806192 ++ w) by sec_eq.
    apply (sTUP [240; 14; 5] 472 4 7690 2 ((1, 1) :: repeat (1, 2) 16082 ++ (1821, 2) :: (1, 1) :: repeat (1, 2) 308090 ++ (3396738, 2) :: (1, 1) :: repeat (1, 2) 7965811 ++ (18372851, 2) :: (1, 1) :: repeat (1, 2) 58806192 ++ w) 1); closearith.
  }
  (* step 95: DIPGRIND 472 6744 *)
  apply (hsteps_trans _ (HC [240; 14; 5] 0 3 2 (repeat (1, 2) 472 ++ (6744, 2) :: (1, 1) :: repeat (1, 2) 16082 ++ (1821, 2) :: (1, 1) :: repeat (1, 2) 308090 ++ (3396738, 2) :: (1, 1) :: repeat (1, 2) 7965811 ++ (18372851, 2) :: (1, 1) :: repeat (1, 2) 58806192 ++ w) 1)).
  {
    apply (DIPGRIND 472 6744 [240; 14; 5] ((1, 1) :: repeat (1, 2) 16082 ++ (1821, 2) :: (1, 1) :: repeat (1, 2) 308090 ++ (3396738, 2) :: (1, 1) :: repeat (1, 2) 7965811 ++ (18372851, 2) :: (1, 1) :: repeat (1, 2) 58806192 ++ w) 1); closearith.
  }
  (* step 96: P PX2A *)
  apply (hsteps_trans _ (HC [5] 13 238 2 ((1, 1) :: repeat (1, 2) 474 ++ (6744, 2) :: (1, 1) :: repeat (1, 2) 16082 ++ (1821, 2) :: (1, 1) :: repeat (1, 2) 308090 ++ (3396738, 2) :: (1, 1) :: repeat (1, 2) 7965811 ++ (18372851, 2) :: (1, 1) :: repeat (1, 2) 58806192 ++ w) 1)).
  {
    exact (hsteps_step _ _ _ (hPX2A 237 13 [5] (repeat (1, 2) 472 ++ (6744, 2) :: (1, 1) :: repeat (1, 2) 16082 ++ (1821, 2) :: (1, 1) :: repeat (1, 2) 308090 ++ (3396738, 2) :: (1, 1) :: repeat (1, 2) 7965811 ++ (18372851, 2) :: (1, 1) :: repeat (1, 2) 58806192 ++ w) 1) (hsteps_refl _)).
  }
  (* step 97: P PUSH *)
  apply (hsteps_trans _ (HC [5] 12 1 2 ((236, 2) :: (1, 1) :: repeat (1, 2) 474 ++ (6744, 2) :: (1, 1) :: repeat (1, 2) 16082 ++ (1821, 2) :: (1, 1) :: repeat (1, 2) 308090 ++ (3396738, 2) :: (1, 1) :: repeat (1, 2) 7965811 ++ (18372851, 2) :: (1, 1) :: repeat (1, 2) 58806192 ++ w) 1)).
  {
    replace ((236, 2) :: (1, 1) :: repeat (1, 2) 474 ++ (6744, 2) :: (1, 1) :: repeat (1, 2) 16082 ++ (1821, 2) :: (1, 1) :: repeat (1, 2) 308090 ++ (3396738, 2) :: (1, 1) :: repeat (1, 2) 7965811 ++ (18372851, 2) :: (1, 1) :: repeat (1, 2) 58806192 ++ w) with ((238 - 2, 2) :: (1, 1) :: repeat (1, 2) 474 ++ (6744, 2) :: (1, 1) :: repeat (1, 2) 16082 ++ (1821, 2) :: (1, 1) :: repeat (1, 2) 308090 ++ (3396738, 2) :: (1, 1) :: repeat (1, 2) 7965811 ++ (18372851, 2) :: (1, 1) :: repeat (1, 2) 58806192 ++ w) by sec_eq.
    apply (sPUSH [5] 12 238 ((1, 1) :: repeat (1, 2) 474 ++ (6744, 2) :: (1, 1) :: repeat (1, 2) 16082 ++ (1821, 2) :: (1, 1) :: repeat (1, 2) 308090 ++ (3396738, 2) :: (1, 1) :: repeat (1, 2) 7965811 ++ (18372851, 2) :: (1, 1) :: repeat (1, 2) 58806192 ++ w) 1); closearith.
  }
  (* step 98: P TDN *)
  apply (hsteps_trans _ (HB [5] 12 1 4 ((236, 2) :: (1, 1) :: repeat (1, 2) 474 ++ (6744, 2) :: (1, 1) :: repeat (1, 2) 16082 ++ (1821, 2) :: (1, 1) :: repeat (1, 2) 308090 ++ (3396738, 2) :: (1, 1) :: repeat (1, 2) 7965811 ++ (18372851, 2) :: (1, 1) :: repeat (1, 2) 58806192 ++ w) 1)).
  {
    apply (sTDN [5] 12 ((236, 2) :: (1, 1) :: repeat (1, 2) 474 ++ (6744, 2) :: (1, 1) :: repeat (1, 2) 16082 ++ (1821, 2) :: (1, 1) :: repeat (1, 2) 308090 ++ (3396738, 2) :: (1, 1) :: repeat (1, 2) 7965811 ++ (18372851, 2) :: (1, 1) :: repeat (1, 2) 58806192 ++ w) 1).
  }
  (* step 99: sTUP *)
  apply (hsteps_trans _ (HC [5] 12 3 2 ((234, 2) :: (1, 1) :: repeat (1, 2) 474 ++ (6744, 2) :: (1, 1) :: repeat (1, 2) 16082 ++ (1821, 2) :: (1, 1) :: repeat (1, 2) 308090 ++ (3396738, 2) :: (1, 1) :: repeat (1, 2) 7965811 ++ (18372851, 2) :: (1, 1) :: repeat (1, 2) 58806192 ++ w) 1)).
  {
    replace ((234, 2) :: (1, 1) :: repeat (1, 2) 474 ++ (6744, 2) :: (1, 1) :: repeat (1, 2) 16082 ++ (1821, 2) :: (1, 1) :: repeat (1, 2) 308090 ++ (3396738, 2) :: (1, 1) :: repeat (1, 2) 7965811 ++ (18372851, 2) :: (1, 1) :: repeat (1, 2) 58806192 ++ w) with ((236 - 2, 2) :: (1, 1) :: repeat (1, 2) 474 ++ (6744, 2) :: (1, 1) :: repeat (1, 2) 16082 ++ (1821, 2) :: (1, 1) :: repeat (1, 2) 308090 ++ (3396738, 2) :: (1, 1) :: repeat (1, 2) 7965811 ++ (18372851, 2) :: (1, 1) :: repeat (1, 2) 58806192 ++ w) by sec_eq.
    apply (sTUP [5] 12 4 236 2 ((1, 1) :: repeat (1, 2) 474 ++ (6744, 2) :: (1, 1) :: repeat (1, 2) 16082 ++ (1821, 2) :: (1, 1) :: repeat (1, 2) 308090 ++ (3396738, 2) :: (1, 1) :: repeat (1, 2) 7965811 ++ (18372851, 2) :: (1, 1) :: repeat (1, 2) 58806192 ++ w) 1); closearith.
  }
  (* step 100: DIPGRIND 12 210 *)
  apply (hsteps_trans _ (HC [5] 0 3 2 (repeat (1, 2) 12 ++ (210, 2) :: (1, 1) :: repeat (1, 2) 474 ++ (6744, 2) :: (1, 1) :: repeat (1, 2) 16082 ++ (1821, 2) :: (1, 1) :: repeat (1, 2) 308090 ++ (3396738, 2) :: (1, 1) :: repeat (1, 2) 7965811 ++ (18372851, 2) :: (1, 1) :: repeat (1, 2) 58806192 ++ w) 1)).
  {
    apply (DIPGRIND 12 210 [5] ((1, 1) :: repeat (1, 2) 474 ++ (6744, 2) :: (1, 1) :: repeat (1, 2) 16082 ++ (1821, 2) :: (1, 1) :: repeat (1, 2) 308090 ++ (3396738, 2) :: (1, 1) :: repeat (1, 2) 7965811 ++ (18372851, 2) :: (1, 1) :: repeat (1, 2) 58806192 ++ w) 1); closearith.
  }
  (* step 101: P PX2Bgen *)
  apply (hsteps_trans _ (HB [0] 3 1 2 (repeat (1, 2) 1 ++ (1, 1) :: repeat (1, 2) 14 ++ (210, 2) :: (1, 1) :: repeat (1, 2) 474 ++ (6744, 2) :: (1, 1) :: repeat (1, 2) 16082 ++ (1821, 2) :: (1, 1) :: repeat (1, 2) 308090 ++ (3396738, 2) :: (1, 1) :: repeat (1, 2) 7965811 ++ (18372851, 2) :: (1, 1) :: repeat (1, 2) 58806192 ++ w) 1)).
  {
    exact (hsteps_step _ _ _ (hPX2Bgen 0 (repeat (1, 2) 12 ++ (210, 2) :: (1, 1) :: repeat (1, 2) 474 ++ (6744, 2) :: (1, 1) :: repeat (1, 2) 16082 ++ (1821, 2) :: (1, 1) :: repeat (1, 2) 308090 ++ (3396738, 2) :: (1, 1) :: repeat (1, 2) 7965811 ++ (18372851, 2) :: (1, 1) :: repeat (1, 2) 58806192 ++ w) 1) (hsteps_refl _)).
  }
  (* step 102: M pop12 (1,) *)
  apply (hsteps_trans _ (HB [0] 4 1 4 ((1, 1) :: repeat (1, 2) 14 ++ (210, 2) :: (1, 1) :: repeat (1, 2) 474 ++ (6744, 2) :: (1, 1) :: repeat (1, 2) 16082 ++ (1821, 2) :: (1, 1) :: repeat (1, 2) 308090 ++ (3396738, 2) :: (1, 1) :: repeat (1, 2) 7965811 ++ (18372851, 2) :: (1, 1) :: repeat (1, 2) 58806192 ++ w) 1)).
  {
    apply (pop12 1 [0] 3 2 ((1, 1) :: repeat (1, 2) 14 ++ (210, 2) :: (1, 1) :: repeat (1, 2) 474 ++ (6744, 2) :: (1, 1) :: repeat (1, 2) 16082 ++ (1821, 2) :: (1, 1) :: repeat (1, 2) 308090 ++ (3396738, 2) :: (1, 1) :: repeat (1, 2) 7965811 ++ (18372851, 2) :: (1, 1) :: repeat (1, 2) 58806192 ++ w) 1); closearith.
  }
  (* step 103: P POP *)
  apply (hsteps_trans _ (HB [0] 5 1 5 (repeat (1, 2) 14 ++ (210, 2) :: (1, 1) :: repeat (1, 2) 474 ++ (6744, 2) :: (1, 1) :: repeat (1, 2) 16082 ++ (1821, 2) :: (1, 1) :: repeat (1, 2) 308090 ++ (3396738, 2) :: (1, 1) :: repeat (1, 2) 7965811 ++ (18372851, 2) :: (1, 1) :: repeat (1, 2) 58806192 ++ w) 1)).
  {
    apply (sPOP1 [0] 4 4 (repeat (1, 2) 14 ++ (210, 2) :: (1, 1) :: repeat (1, 2) 474 ++ (6744, 2) :: (1, 1) :: repeat (1, 2) 16082 ++ (1821, 2) :: (1, 1) :: repeat (1, 2) 308090 ++ (3396738, 2) :: (1, 1) :: repeat (1, 2) 7965811 ++ (18372851, 2) :: (1, 1) :: repeat (1, 2) 58806192 ++ w) 1); closearith.
  }
  (* step 104: M pop12 (14,) *)
  apply (hsteps_trans _ (HB [0] 19 1 33 ((210, 2) :: (1, 1) :: repeat (1, 2) 474 ++ (6744, 2) :: (1, 1) :: repeat (1, 2) 16082 ++ (1821, 2) :: (1, 1) :: repeat (1, 2) 308090 ++ (3396738, 2) :: (1, 1) :: repeat (1, 2) 7965811 ++ (18372851, 2) :: (1, 1) :: repeat (1, 2) 58806192 ++ w) 1)).
  {
    apply (pop12 14 [0] 5 5 ((210, 2) :: (1, 1) :: repeat (1, 2) 474 ++ (6744, 2) :: (1, 1) :: repeat (1, 2) 16082 ++ (1821, 2) :: (1, 1) :: repeat (1, 2) 308090 ++ (3396738, 2) :: (1, 1) :: repeat (1, 2) 7965811 ++ (18372851, 2) :: (1, 1) :: repeat (1, 2) 58806192 ++ w) 1); closearith.
  }
  (* step 105: sTUP *)
  apply (hsteps_trans _ (HC [0] 19 32 2 ((208, 2) :: (1, 1) :: repeat (1, 2) 474 ++ (6744, 2) :: (1, 1) :: repeat (1, 2) 16082 ++ (1821, 2) :: (1, 1) :: repeat (1, 2) 308090 ++ (3396738, 2) :: (1, 1) :: repeat (1, 2) 7965811 ++ (18372851, 2) :: (1, 1) :: repeat (1, 2) 58806192 ++ w) 1)).
  {
    replace ((208, 2) :: (1, 1) :: repeat (1, 2) 474 ++ (6744, 2) :: (1, 1) :: repeat (1, 2) 16082 ++ (1821, 2) :: (1, 1) :: repeat (1, 2) 308090 ++ (3396738, 2) :: (1, 1) :: repeat (1, 2) 7965811 ++ (18372851, 2) :: (1, 1) :: repeat (1, 2) 58806192 ++ w) with ((210 - 2, 2) :: (1, 1) :: repeat (1, 2) 474 ++ (6744, 2) :: (1, 1) :: repeat (1, 2) 16082 ++ (1821, 2) :: (1, 1) :: repeat (1, 2) 308090 ++ (3396738, 2) :: (1, 1) :: repeat (1, 2) 7965811 ++ (18372851, 2) :: (1, 1) :: repeat (1, 2) 58806192 ++ w) by sec_eq.
    apply (sTUP [0] 19 33 210 2 ((1, 1) :: repeat (1, 2) 474 ++ (6744, 2) :: (1, 1) :: repeat (1, 2) 16082 ++ (1821, 2) :: (1, 1) :: repeat (1, 2) 308090 ++ (3396738, 2) :: (1, 1) :: repeat (1, 2) 7965811 ++ (18372851, 2) :: (1, 1) :: repeat (1, 2) 58806192 ++ w) 1); closearith.
  }
  (* step 106: hGRIND_even 14 *)
  apply (hsteps_trans _ (HB [0] 18 1 32 ((2, 2) :: (208, 2) :: (1, 1) :: repeat (1, 2) 474 ++ (6744, 2) :: (1, 1) :: repeat (1, 2) 16082 ++ (1821, 2) :: (1, 1) :: repeat (1, 2) 308090 ++ (3396738, 2) :: (1, 1) :: repeat (1, 2) 7965811 ++ (18372851, 2) :: (1, 1) :: repeat (1, 2) 58806192 ++ w) 1)).
  {
    apply (hGRIND_even 14 [0] 18 ((208, 2) :: (1, 1) :: repeat (1, 2) 474 ++ (6744, 2) :: (1, 1) :: repeat (1, 2) 16082 ++ (1821, 2) :: (1, 1) :: repeat (1, 2) 308090 ++ (3396738, 2) :: (1, 1) :: repeat (1, 2) 7965811 ++ (18372851, 2) :: (1, 1) :: repeat (1, 2) 58806192 ++ w) 1); closearith.
  }
  (* step 107: P TUP2_1 *)
  apply (hsteps_trans _ (HC [19; 0] 32 1 2 ((206, 2) :: (1, 1) :: repeat (1, 2) 474 ++ (6744, 2) :: (1, 1) :: repeat (1, 2) 16082 ++ (1821, 2) :: (1, 1) :: repeat (1, 2) 308090 ++ (3396738, 2) :: (1, 1) :: repeat (1, 2) 7965811 ++ (18372851, 2) :: (1, 1) :: repeat (1, 2) 58806192 ++ w) 1)).
  {
    replace ((206, 2) :: (1, 1) :: repeat (1, 2) 474 ++ (6744, 2) :: (1, 1) :: repeat (1, 2) 16082 ++ (1821, 2) :: (1, 1) :: repeat (1, 2) 308090 ++ (3396738, 2) :: (1, 1) :: repeat (1, 2) 7965811 ++ (18372851, 2) :: (1, 1) :: repeat (1, 2) 58806192 ++ w) with ((208 - 2, 2) :: (1, 1) :: repeat (1, 2) 474 ++ (6744, 2) :: (1, 1) :: repeat (1, 2) 16082 ++ (1821, 2) :: (1, 1) :: repeat (1, 2) 308090 ++ (3396738, 2) :: (1, 1) :: repeat (1, 2) 7965811 ++ (18372851, 2) :: (1, 1) :: repeat (1, 2) 58806192 ++ w) by sec_eq.
    apply (sTUP2_1 [0] 18 31 208 ((1, 1) :: repeat (1, 2) 474 ++ (6744, 2) :: (1, 1) :: repeat (1, 2) 16082 ++ (1821, 2) :: (1, 1) :: repeat (1, 2) 308090 ++ (3396738, 2) :: (1, 1) :: repeat (1, 2) 7965811 ++ (18372851, 2) :: (1, 1) :: repeat (1, 2) 58806192 ++ w) 1); closearith.
  }
  (* step 108: P TDN *)
  apply (hsteps_trans _ (HB [19; 0] 32 1 4 ((206, 2) :: (1, 1) :: repeat (1, 2) 474 ++ (6744, 2) :: (1, 1) :: repeat (1, 2) 16082 ++ (1821, 2) :: (1, 1) :: repeat (1, 2) 308090 ++ (3396738, 2) :: (1, 1) :: repeat (1, 2) 7965811 ++ (18372851, 2) :: (1, 1) :: repeat (1, 2) 58806192 ++ w) 1)).
  {
    apply (sTDN [19; 0] 32 ((206, 2) :: (1, 1) :: repeat (1, 2) 474 ++ (6744, 2) :: (1, 1) :: repeat (1, 2) 16082 ++ (1821, 2) :: (1, 1) :: repeat (1, 2) 308090 ++ (3396738, 2) :: (1, 1) :: repeat (1, 2) 7965811 ++ (18372851, 2) :: (1, 1) :: repeat (1, 2) 58806192 ++ w) 1).
  }
  (* step 109: sTUP *)
  apply (hsteps_trans _ (HC [19; 0] 32 3 2 ((204, 2) :: (1, 1) :: repeat (1, 2) 474 ++ (6744, 2) :: (1, 1) :: repeat (1, 2) 16082 ++ (1821, 2) :: (1, 1) :: repeat (1, 2) 308090 ++ (3396738, 2) :: (1, 1) :: repeat (1, 2) 7965811 ++ (18372851, 2) :: (1, 1) :: repeat (1, 2) 58806192 ++ w) 1)).
  {
    replace ((204, 2) :: (1, 1) :: repeat (1, 2) 474 ++ (6744, 2) :: (1, 1) :: repeat (1, 2) 16082 ++ (1821, 2) :: (1, 1) :: repeat (1, 2) 308090 ++ (3396738, 2) :: (1, 1) :: repeat (1, 2) 7965811 ++ (18372851, 2) :: (1, 1) :: repeat (1, 2) 58806192 ++ w) with ((206 - 2, 2) :: (1, 1) :: repeat (1, 2) 474 ++ (6744, 2) :: (1, 1) :: repeat (1, 2) 16082 ++ (1821, 2) :: (1, 1) :: repeat (1, 2) 308090 ++ (3396738, 2) :: (1, 1) :: repeat (1, 2) 7965811 ++ (18372851, 2) :: (1, 1) :: repeat (1, 2) 58806192 ++ w) by sec_eq.
    apply (sTUP [19; 0] 32 4 206 2 ((1, 1) :: repeat (1, 2) 474 ++ (6744, 2) :: (1, 1) :: repeat (1, 2) 16082 ++ (1821, 2) :: (1, 1) :: repeat (1, 2) 308090 ++ (3396738, 2) :: (1, 1) :: repeat (1, 2) 7965811 ++ (18372851, 2) :: (1, 1) :: repeat (1, 2) 58806192 ++ w) 1); closearith.
  }
  (* step 110: DIPGRIND 32 140 *)
  apply (hsteps_trans _ (HC [19; 0] 0 3 2 (repeat (1, 2) 32 ++ (140, 2) :: (1, 1) :: repeat (1, 2) 474 ++ (6744, 2) :: (1, 1) :: repeat (1, 2) 16082 ++ (1821, 2) :: (1, 1) :: repeat (1, 2) 308090 ++ (3396738, 2) :: (1, 1) :: repeat (1, 2) 7965811 ++ (18372851, 2) :: (1, 1) :: repeat (1, 2) 58806192 ++ w) 1)).
  {
    apply (DIPGRIND 32 140 [19; 0] ((1, 1) :: repeat (1, 2) 474 ++ (6744, 2) :: (1, 1) :: repeat (1, 2) 16082 ++ (1821, 2) :: (1, 1) :: repeat (1, 2) 308090 ++ (3396738, 2) :: (1, 1) :: repeat (1, 2) 7965811 ++ (18372851, 2) :: (1, 1) :: repeat (1, 2) 58806192 ++ w) 1); closearith.
  }
  (* step 111: P PX2A0 *)
  apply (hsteps_trans _ (HB [0] 3 1 2 ((15, 2) :: (1, 1) :: repeat (1, 2) 34 ++ (140, 2) :: (1, 1) :: repeat (1, 2) 474 ++ (6744, 2) :: (1, 1) :: repeat (1, 2) 16082 ++ (1821, 2) :: (1, 1) :: repeat (1, 2) 308090 ++ (3396738, 2) :: (1, 1) :: repeat (1, 2) 7965811 ++ (18372851, 2) :: (1, 1) :: repeat (1, 2) 58806192 ++ w) 1)).
  {
    exact (hsteps_step _ _ _ (hPX2A0 14 (repeat (1, 2) 32 ++ (140, 2) :: (1, 1) :: repeat (1, 2) 474 ++ (6744, 2) :: (1, 1) :: repeat (1, 2) 16082 ++ (1821, 2) :: (1, 1) :: repeat (1, 2) 308090 ++ (3396738, 2) :: (1, 1) :: repeat (1, 2) 7965811 ++ (18372851, 2) :: (1, 1) :: repeat (1, 2) 58806192 ++ w) 1) (hsteps_refl _)).
  }
  (* step 112: sTUP *)
  replace ((13, 2) :: (1, 1) :: repeat (1, 2) 34 ++ (140, 2) :: (1, 1) :: repeat (1, 2) 474 ++ (6744, 2) :: (1, 1) :: repeat (1, 2) 16082 ++ (1821, 2) :: (1, 1) :: repeat (1, 2) 308090 ++ (3396738, 2) :: (1, 1) :: repeat (1, 2) 7965811 ++ (18372851, 2) :: (1, 1) :: repeat (1, 2) 58806192 ++ w) with ((15 - 2, 2) :: (1, 1) :: repeat (1, 2) 34 ++ (140, 2) :: (1, 1) :: repeat (1, 2) 474 ++ (6744, 2) :: (1, 1) :: repeat (1, 2) 16082 ++ (1821, 2) :: (1, 1) :: repeat (1, 2) 308090 ++ (3396738, 2) :: (1, 1) :: repeat (1, 2) 7965811 ++ (18372851, 2) :: (1, 1) :: repeat (1, 2) 58806192 ++ w) by sec_eq.
  apply (sTUP [0] 3 2 15 2 ((1, 1) :: repeat (1, 2) 34 ++ (140, 2) :: (1, 1) :: repeat (1, 2) 474 ++ (6744, 2) :: (1, 1) :: repeat (1, 2) 16082 ++ (1821, 2) :: (1, 1) :: repeat (1, 2) 308090 ++ (3396738, 2) :: (1, 1) :: repeat (1, 2) 7965811 ++ (18372851, 2) :: (1, 1) :: repeat (1, 2) 58806192 ++ w) 1); closearith.
Qed.

(* CASCADE60c: steps 113-168 of the CASCADE60 chain. *)
Lemma CASCADE60c : forall w,
  hsteps (HC [0] 3 1 2 ((13, 2) :: (1, 1) :: repeat (1, 2) 34 ++ (140, 2) :: (1, 1) :: repeat (1, 2) 474 ++ (6744, 2) :: (1, 1) :: repeat (1, 2) 16082 ++ (1821, 2) :: (1, 1) :: repeat (1, 2) 308090 ++ (3396738, 2) :: (1, 1) :: repeat (1, 2) 7965811 ++ (18372851, 2) :: (1, 1) :: repeat (1, 2) 58806192 ++ w) 1)
         (HB [0] 4 1 4 ((1, 1) :: repeat (1, 2) 15 ++ (5, 2) :: (1, 1) :: repeat (1, 2) 75 ++ (461, 2) :: (1, 1) :: repeat (1, 2) 952 ++ (4838, 2) :: (1, 1) :: repeat (1, 2) 16082 ++ (1821, 2) :: (1, 1) :: repeat (1, 2) 308090 ++ (3396738, 2) :: (1, 1) :: repeat (1, 2) 7965811 ++ (18372851, 2) :: (1, 1) :: repeat (1, 2) 58806192 ++ w) 1).
Proof.
  intro w.
  (* step 113: P TDN *)
  apply (hsteps_trans _ (HB [0] 3 1 4 ((13, 2) :: (1, 1) :: repeat (1, 2) 34 ++ (140, 2) :: (1, 1) :: repeat (1, 2) 474 ++ (6744, 2) :: (1, 1) :: repeat (1, 2) 16082 ++ (1821, 2) :: (1, 1) :: repeat (1, 2) 308090 ++ (3396738, 2) :: (1, 1) :: repeat (1, 2) 7965811 ++ (18372851, 2) :: (1, 1) :: repeat (1, 2) 58806192 ++ w) 1)).
  {
    apply (sTDN [0] 3 ((13, 2) :: (1, 1) :: repeat (1, 2) 34 ++ (140, 2) :: (1, 1) :: repeat (1, 2) 474 ++ (6744, 2) :: (1, 1) :: repeat (1, 2) 16082 ++ (1821, 2) :: (1, 1) :: repeat (1, 2) 308090 ++ (3396738, 2) :: (1, 1) :: repeat (1, 2) 7965811 ++ (18372851, 2) :: (1, 1) :: repeat (1, 2) 58806192 ++ w) 1).
  }
  (* step 114: sTUP *)
  apply (hsteps_trans _ (HC [0] 3 3 2 ((11, 2) :: (1, 1) :: repeat (1, 2) 34 ++ (140, 2) :: (1, 1) :: repeat (1, 2) 474 ++ (6744, 2) :: (1, 1) :: repeat (1, 2) 16082 ++ (1821, 2) :: (1, 1) :: repeat (1, 2) 308090 ++ (3396738, 2) :: (1, 1) :: repeat (1, 2) 7965811 ++ (18372851, 2) :: (1, 1) :: repeat (1, 2) 58806192 ++ w) 1)).
  {
    replace ((11, 2) :: (1, 1) :: repeat (1, 2) 34 ++ (140, 2) :: (1, 1) :: repeat (1, 2) 474 ++ (6744, 2) :: (1, 1) :: repeat (1, 2) 16082 ++ (1821, 2) :: (1, 1) :: repeat (1, 2) 308090 ++ (3396738, 2) :: (1, 1) :: repeat (1, 2) 7965811 ++ (18372851, 2) :: (1, 1) :: repeat (1, 2) 58806192 ++ w) with ((13 - 2, 2) :: (1, 1) :: repeat (1, 2) 34 ++ (140, 2) :: (1, 1) :: repeat (1, 2) 474 ++ (6744, 2) :: (1, 1) :: repeat (1, 2) 16082 ++ (1821, 2) :: (1, 1) :: repeat (1, 2) 308090 ++ (3396738, 2) :: (1, 1) :: repeat (1, 2) 7965811 ++ (18372851, 2) :: (1, 1) :: repeat (1, 2) 58806192 ++ w) by sec_eq.
    apply (sTUP [0] 3 4 13 2 ((1, 1) :: repeat (1, 2) 34 ++ (140, 2) :: (1, 1) :: repeat (1, 2) 474 ++ (6744, 2) :: (1, 1) :: repeat (1, 2) 16082 ++ (1821, 2) :: (1, 1) :: repeat (1, 2) 308090 ++ (3396738, 2) :: (1, 1) :: repeat (1, 2) 7965811 ++ (18372851, 2) :: (1, 1) :: repeat (1, 2) 58806192 ++ w) 1); closearith.
  }
  (* step 115: DIPGRIND 3 5 *)
  apply (hsteps_trans _ (HC [0] 0 3 2 (repeat (1, 2) 3 ++ (5, 2) :: (1, 1) :: repeat (1, 2) 34 ++ (140, 2) :: (1, 1) :: repeat (1, 2) 474 ++ (6744, 2) :: (1, 1) :: repeat (1, 2) 16082 ++ (1821, 2) :: (1, 1) :: repeat (1, 2) 308090 ++ (3396738, 2) :: (1, 1) :: repeat (1, 2) 7965811 ++ (18372851, 2) :: (1, 1) :: repeat (1, 2) 58806192 ++ w) 1)).
  {
    apply (DIPGRIND 3 5 [0] ((1, 1) :: repeat (1, 2) 34 ++ (140, 2) :: (1, 1) :: repeat (1, 2) 474 ++ (6744, 2) :: (1, 1) :: repeat (1, 2) 16082 ++ (1821, 2) :: (1, 1) :: repeat (1, 2) 308090 ++ (3396738, 2) :: (1, 1) :: repeat (1, 2) 7965811 ++ (18372851, 2) :: (1, 1) :: repeat (1, 2) 58806192 ++ w) 1); closearith.
  }
  (* step 116: P PX2B0 *)
  apply (hsteps_trans _ (HB [] 0 1 5 (repeat (1, 2) 4 ++ (5, 2) :: (1, 1) :: repeat (1, 2) 34 ++ (140, 2) :: (1, 1) :: repeat (1, 2) 474 ++ (6744, 2) :: (1, 1) :: repeat (1, 2) 16082 ++ (1821, 2) :: (1, 1) :: repeat (1, 2) 308090 ++ (3396738, 2) :: (1, 1) :: repeat (1, 2) 7965811 ++ (18372851, 2) :: (1, 1) :: repeat (1, 2) 58806192 ++ w) 1)).
  {
    exact (hsteps_step _ _ _ (hPX2B0 (repeat (1, 2) 3 ++ (5, 2) :: (1, 1) :: repeat (1, 2) 34 ++ (140, 2) :: (1, 1) :: repeat (1, 2) 474 ++ (6744, 2) :: (1, 1) :: repeat (1, 2) 16082 ++ (1821, 2) :: (1, 1) :: repeat (1, 2) 308090 ++ (3396738, 2) :: (1, 1) :: repeat (1, 2) 7965811 ++ (18372851, 2) :: (1, 1) :: repeat (1, 2) 58806192 ++ w) 1) (hsteps_refl _)).
  }
  (* step 117: M pop12 (4,) *)
  apply (hsteps_trans _ (HB [] 4 1 13 ((5, 2) :: (1, 1) :: repeat (1, 2) 34 ++ (140, 2) :: (1, 1) :: repeat (1, 2) 474 ++ (6744, 2) :: (1, 1) :: repeat (1, 2) 16082 ++ (1821, 2) :: (1, 1) :: repeat (1, 2) 308090 ++ (3396738, 2) :: (1, 1) :: repeat (1, 2) 7965811 ++ (18372851, 2) :: (1, 1) :: repeat (1, 2) 58806192 ++ w) 1)).
  {
    apply (pop12 4 [] 0 5 ((5, 2) :: (1, 1) :: repeat (1, 2) 34 ++ (140, 2) :: (1, 1) :: repeat (1, 2) 474 ++ (6744, 2) :: (1, 1) :: repeat (1, 2) 16082 ++ (1821, 2) :: (1, 1) :: repeat (1, 2) 308090 ++ (3396738, 2) :: (1, 1) :: repeat (1, 2) 7965811 ++ (18372851, 2) :: (1, 1) :: repeat (1, 2) 58806192 ++ w) 1); closearith.
  }
  (* step 118: sTUP *)
  apply (hsteps_trans _ (HC [] 4 12 2 ((3, 2) :: (1, 1) :: repeat (1, 2) 34 ++ (140, 2) :: (1, 1) :: repeat (1, 2) 474 ++ (6744, 2) :: (1, 1) :: repeat (1, 2) 16082 ++ (1821, 2) :: (1, 1) :: repeat (1, 2) 308090 ++ (3396738, 2) :: (1, 1) :: repeat (1, 2) 7965811 ++ (18372851, 2) :: (1, 1) :: repeat (1, 2) 58806192 ++ w) 1)).
  {
    replace ((3, 2) :: (1, 1) :: repeat (1, 2) 34 ++ (140, 2) :: (1, 1) :: repeat (1, 2) 474 ++ (6744, 2) :: (1, 1) :: repeat (1, 2) 16082 ++ (1821, 2) :: (1, 1) :: repeat (1, 2) 308090 ++ (3396738, 2) :: (1, 1) :: repeat (1, 2) 7965811 ++ (18372851, 2) :: (1, 1) :: repeat (1, 2) 58806192 ++ w) with ((5 - 2, 2) :: (1, 1) :: repeat (1, 2) 34 ++ (140, 2) :: (1, 1) :: repeat (1, 2) 474 ++ (6744, 2) :: (1, 1) :: repeat (1, 2) 16082 ++ (1821, 2) :: (1, 1) :: repeat (1, 2) 308090 ++ (3396738, 2) :: (1, 1) :: repeat (1, 2) 7965811 ++ (18372851, 2) :: (1, 1) :: repeat (1, 2) 58806192 ++ w) by sec_eq.
    apply (sTUP [] 4 13 5 2 ((1, 1) :: repeat (1, 2) 34 ++ (140, 2) :: (1, 1) :: repeat (1, 2) 474 ++ (6744, 2) :: (1, 1) :: repeat (1, 2) 16082 ++ (1821, 2) :: (1, 1) :: repeat (1, 2) 308090 ++ (3396738, 2) :: (1, 1) :: repeat (1, 2) 7965811 ++ (18372851, 2) :: (1, 1) :: repeat (1, 2) 58806192 ++ w) 1); closearith.
  }
  (* step 119: P PUSH *)
  apply (hsteps_trans _ (HC [] 3 1 2 ((10, 2) :: (3, 2) :: (1, 1) :: repeat (1, 2) 34 ++ (140, 2) :: (1, 1) :: repeat (1, 2) 474 ++ (6744, 2) :: (1, 1) :: repeat (1, 2) 16082 ++ (1821, 2) :: (1, 1) :: repeat (1, 2) 308090 ++ (3396738, 2) :: (1, 1) :: repeat (1, 2) 7965811 ++ (18372851, 2) :: (1, 1) :: repeat (1, 2) 58806192 ++ w) 1)).
  {
    replace ((10, 2) :: (3, 2) :: (1, 1) :: repeat (1, 2) 34 ++ (140, 2) :: (1, 1) :: repeat (1, 2) 474 ++ (6744, 2) :: (1, 1) :: repeat (1, 2) 16082 ++ (1821, 2) :: (1, 1) :: repeat (1, 2) 308090 ++ (3396738, 2) :: (1, 1) :: repeat (1, 2) 7965811 ++ (18372851, 2) :: (1, 1) :: repeat (1, 2) 58806192 ++ w) with ((12 - 2, 2) :: (3, 2) :: (1, 1) :: repeat (1, 2) 34 ++ (140, 2) :: (1, 1) :: repeat (1, 2) 474 ++ (6744, 2) :: (1, 1) :: repeat (1, 2) 16082 ++ (1821, 2) :: (1, 1) :: repeat (1, 2) 308090 ++ (3396738, 2) :: (1, 1) :: repeat (1, 2) 7965811 ++ (18372851, 2) :: (1, 1) :: repeat (1, 2) 58806192 ++ w) by sec_eq.
    apply (sPUSH [] 3 12 ((3, 2) :: (1, 1) :: repeat (1, 2) 34 ++ (140, 2) :: (1, 1) :: repeat (1, 2) 474 ++ (6744, 2) :: (1, 1) :: repeat (1, 2) 16082 ++ (1821, 2) :: (1, 1) :: repeat (1, 2) 308090 ++ (3396738, 2) :: (1, 1) :: repeat (1, 2) 7965811 ++ (18372851, 2) :: (1, 1) :: repeat (1, 2) 58806192 ++ w) 1); closearith.
  }
  (* step 120: P TDN *)
  apply (hsteps_trans _ (HB [] 3 1 4 ((10, 2) :: (3, 2) :: (1, 1) :: repeat (1, 2) 34 ++ (140, 2) :: (1, 1) :: repeat (1, 2) 474 ++ (6744, 2) :: (1, 1) :: repeat (1, 2) 16082 ++ (1821, 2) :: (1, 1) :: repeat (1, 2) 308090 ++ (3396738, 2) :: (1, 1) :: repeat (1, 2) 7965811 ++ (18372851, 2) :: (1, 1) :: repeat (1, 2) 58806192 ++ w) 1)).
  {
    apply (sTDN [] 3 ((10, 2) :: (3, 2) :: (1, 1) :: repeat (1, 2) 34 ++ (140, 2) :: (1, 1) :: repeat (1, 2) 474 ++ (6744, 2) :: (1, 1) :: repeat (1, 2) 16082 ++ (1821, 2) :: (1, 1) :: repeat (1, 2) 308090 ++ (3396738, 2) :: (1, 1) :: repeat (1, 2) 7965811 ++ (18372851, 2) :: (1, 1) :: repeat (1, 2) 58806192 ++ w) 1).
  }
  (* step 121: sTUP *)
  apply (hsteps_trans _ (HC [] 3 3 2 ((8, 2) :: (3, 2) :: (1, 1) :: repeat (1, 2) 34 ++ (140, 2) :: (1, 1) :: repeat (1, 2) 474 ++ (6744, 2) :: (1, 1) :: repeat (1, 2) 16082 ++ (1821, 2) :: (1, 1) :: repeat (1, 2) 308090 ++ (3396738, 2) :: (1, 1) :: repeat (1, 2) 7965811 ++ (18372851, 2) :: (1, 1) :: repeat (1, 2) 58806192 ++ w) 1)).
  {
    replace ((8, 2) :: (3, 2) :: (1, 1) :: repeat (1, 2) 34 ++ (140, 2) :: (1, 1) :: repeat (1, 2) 474 ++ (6744, 2) :: (1, 1) :: repeat (1, 2) 16082 ++ (1821, 2) :: (1, 1) :: repeat (1, 2) 308090 ++ (3396738, 2) :: (1, 1) :: repeat (1, 2) 7965811 ++ (18372851, 2) :: (1, 1) :: repeat (1, 2) 58806192 ++ w) with ((10 - 2, 2) :: (3, 2) :: (1, 1) :: repeat (1, 2) 34 ++ (140, 2) :: (1, 1) :: repeat (1, 2) 474 ++ (6744, 2) :: (1, 1) :: repeat (1, 2) 16082 ++ (1821, 2) :: (1, 1) :: repeat (1, 2) 308090 ++ (3396738, 2) :: (1, 1) :: repeat (1, 2) 7965811 ++ (18372851, 2) :: (1, 1) :: repeat (1, 2) 58806192 ++ w) by sec_eq.
    apply (sTUP [] 3 4 10 2 ((3, 2) :: (1, 1) :: repeat (1, 2) 34 ++ (140, 2) :: (1, 1) :: repeat (1, 2) 474 ++ (6744, 2) :: (1, 1) :: repeat (1, 2) 16082 ++ (1821, 2) :: (1, 1) :: repeat (1, 2) 308090 ++ (3396738, 2) :: (1, 1) :: repeat (1, 2) 7965811 ++ (18372851, 2) :: (1, 1) :: repeat (1, 2) 58806192 ++ w) 1); closearith.
  }
  (* step 122: DIPGRIND 3 2 *)
  apply (hsteps_trans _ (HC [] 0 3 2 (repeat (1, 2) 3 ++ (2, 2) :: (3, 2) :: (1, 1) :: repeat (1, 2) 34 ++ (140, 2) :: (1, 1) :: repeat (1, 2) 474 ++ (6744, 2) :: (1, 1) :: repeat (1, 2) 16082 ++ (1821, 2) :: (1, 1) :: repeat (1, 2) 308090 ++ (3396738, 2) :: (1, 1) :: repeat (1, 2) 7965811 ++ (18372851, 2) :: (1, 1) :: repeat (1, 2) 58806192 ++ w) 1)).
  {
    apply (DIPGRIND 3 2 [] ((3, 2) :: (1, 1) :: repeat (1, 2) 34 ++ (140, 2) :: (1, 1) :: repeat (1, 2) 474 ++ (6744, 2) :: (1, 1) :: repeat (1, 2) 16082 ++ (1821, 2) :: (1, 1) :: repeat (1, 2) 308090 ++ (3396738, 2) :: (1, 1) :: repeat (1, 2) 7965811 ++ (18372851, 2) :: (1, 1) :: repeat (1, 2) 58806192 ++ w) 1); closearith.
  }
  (* step 123: P PUSHX *)
  apply (hsteps_trans _ (HB [] 1 1 7 (repeat (1, 2) 3 ++ (2, 2) :: (3, 2) :: (1, 1) :: repeat (1, 2) 34 ++ (140, 2) :: (1, 1) :: repeat (1, 2) 474 ++ (6744, 2) :: (1, 1) :: repeat (1, 2) 16082 ++ (1821, 2) :: (1, 1) :: repeat (1, 2) 308090 ++ (3396738, 2) :: (1, 1) :: repeat (1, 2) 7965811 ++ (18372851, 2) :: (1, 1) :: repeat (1, 2) 58806192 ++ w) 1)).
  {
    exact (hsteps_step _ _ _ (hPUSHX (repeat (1, 2) 3 ++ (2, 2) :: (3, 2) :: (1, 1) :: repeat (1, 2) 34 ++ (140, 2) :: (1, 1) :: repeat (1, 2) 474 ++ (6744, 2) :: (1, 1) :: repeat (1, 2) 16082 ++ (1821, 2) :: (1, 1) :: repeat (1, 2) 308090 ++ (3396738, 2) :: (1, 1) :: repeat (1, 2) 7965811 ++ (18372851, 2) :: (1, 1) :: repeat (1, 2) 58806192 ++ w) 1) (hsteps_refl _)).
  }
  (* step 124: M pop12 (3,) *)
  apply (hsteps_trans _ (HB [] 4 1 13 ((2, 2) :: (3, 2) :: (1, 1) :: repeat (1, 2) 34 ++ (140, 2) :: (1, 1) :: repeat (1, 2) 474 ++ (6744, 2) :: (1, 1) :: repeat (1, 2) 16082 ++ (1821, 2) :: (1, 1) :: repeat (1, 2) 308090 ++ (3396738, 2) :: (1, 1) :: repeat (1, 2) 7965811 ++ (18372851, 2) :: (1, 1) :: repeat (1, 2) 58806192 ++ w) 1)).
  {
    apply (pop12 3 [] 1 7 ((2, 2) :: (3, 2) :: (1, 1) :: repeat (1, 2) 34 ++ (140, 2) :: (1, 1) :: repeat (1, 2) 474 ++ (6744, 2) :: (1, 1) :: repeat (1, 2) 16082 ++ (1821, 2) :: (1, 1) :: repeat (1, 2) 308090 ++ (3396738, 2) :: (1, 1) :: repeat (1, 2) 7965811 ++ (18372851, 2) :: (1, 1) :: repeat (1, 2) 58806192 ++ w) 1); closearith.
  }
  (* step 125: P TUP2_1 *)
  apply (hsteps_trans _ (HC [5] 13 1 2 (repeat (1, 2) 1 ++ (1, 1) :: repeat (1, 2) 34 ++ (140, 2) :: (1, 1) :: repeat (1, 2) 474 ++ (6744, 2) :: (1, 1) :: repeat (1, 2) 16082 ++ (1821, 2) :: (1, 1) :: repeat (1, 2) 308090 ++ (3396738, 2) :: (1, 1) :: repeat (1, 2) 7965811 ++ (18372851, 2) :: (1, 1) :: repeat (1, 2) 58806192 ++ w) 1)).
  {
    replace (repeat (1, 2) 1 ++ (1, 1) :: repeat (1, 2) 34 ++ (140, 2) :: (1, 1) :: repeat (1, 2) 474 ++ (6744, 2) :: (1, 1) :: repeat (1, 2) 16082 ++ (1821, 2) :: (1, 1) :: repeat (1, 2) 308090 ++ (3396738, 2) :: (1, 1) :: repeat (1, 2) 7965811 ++ (18372851, 2) :: (1, 1) :: repeat (1, 2) 58806192 ++ w) with ((3 - 2, 2) :: (1, 1) :: repeat (1, 2) 34 ++ (140, 2) :: (1, 1) :: repeat (1, 2) 474 ++ (6744, 2) :: (1, 1) :: repeat (1, 2) 16082 ++ (1821, 2) :: (1, 1) :: repeat (1, 2) 308090 ++ (3396738, 2) :: (1, 1) :: repeat (1, 2) 7965811 ++ (18372851, 2) :: (1, 1) :: repeat (1, 2) 58806192 ++ w) by sec_eq.
    apply (sTUP2_1 [] 4 12 3 ((1, 1) :: repeat (1, 2) 34 ++ (140, 2) :: (1, 1) :: repeat (1, 2) 474 ++ (6744, 2) :: (1, 1) :: repeat (1, 2) 16082 ++ (1821, 2) :: (1, 1) :: repeat (1, 2) 308090 ++ (3396738, 2) :: (1, 1) :: repeat (1, 2) 7965811 ++ (18372851, 2) :: (1, 1) :: repeat (1, 2) 58806192 ++ w) 1); closearith.
  }
  (* step 126: P TDN *)
  apply (hsteps_trans _ (HB [5] 13 1 4 (repeat (1, 2) 1 ++ (1, 1) :: repeat (1, 2) 34 ++ (140, 2) :: (1, 1) :: repeat (1, 2) 474 ++ (6744, 2) :: (1, 1) :: repeat (1, 2) 16082 ++ (1821, 2) :: (1, 1) :: repeat (1, 2) 308090 ++ (3396738, 2) :: (1, 1) :: repeat (1, 2) 7965811 ++ (18372851, 2) :: (1, 1) :: repeat (1, 2) 58806192 ++ w) 1)).
  {
    apply (sTDN [5] 13 (repeat (1, 2) 1 ++ (1, 1) :: repeat (1, 2) 34 ++ (140, 2) :: (1, 1) :: repeat (1, 2) 474 ++ (6744, 2) :: (1, 1) :: repeat (1, 2) 16082 ++ (1821, 2) :: (1, 1) :: repeat (1, 2) 308090 ++ (3396738, 2) :: (1, 1) :: repeat (1, 2) 7965811 ++ (18372851, 2) :: (1, 1) :: repeat (1, 2) 58806192 ++ w) 1).
  }
  (* step 127: M pop12 (1,) *)
  apply (hsteps_trans _ (HB [5] 14 1 6 ((1, 1) :: repeat (1, 2) 34 ++ (140, 2) :: (1, 1) :: repeat (1, 2) 474 ++ (6744, 2) :: (1, 1) :: repeat (1, 2) 16082 ++ (1821, 2) :: (1, 1) :: repeat (1, 2) 308090 ++ (3396738, 2) :: (1, 1) :: repeat (1, 2) 7965811 ++ (18372851, 2) :: (1, 1) :: repeat (1, 2) 58806192 ++ w) 1)).
  {
    apply (pop12 1 [5] 13 4 ((1, 1) :: repeat (1, 2) 34 ++ (140, 2) :: (1, 1) :: repeat (1, 2) 474 ++ (6744, 2) :: (1, 1) :: repeat (1, 2) 16082 ++ (1821, 2) :: (1, 1) :: repeat (1, 2) 308090 ++ (3396738, 2) :: (1, 1) :: repeat (1, 2) 7965811 ++ (18372851, 2) :: (1, 1) :: repeat (1, 2) 58806192 ++ w) 1); closearith.
  }
  (* step 128: P POP *)
  apply (hsteps_trans _ (HB [5] 15 1 7 (repeat (1, 2) 34 ++ (140, 2) :: (1, 1) :: repeat (1, 2) 474 ++ (6744, 2) :: (1, 1) :: repeat (1, 2) 16082 ++ (1821, 2) :: (1, 1) :: repeat (1, 2) 308090 ++ (3396738, 2) :: (1, 1) :: repeat (1, 2) 7965811 ++ (18372851, 2) :: (1, 1) :: repeat (1, 2) 58806192 ++ w) 1)).
  {
    apply (sPOP1 [5] 14 6 (repeat (1, 2) 34 ++ (140, 2) :: (1, 1) :: repeat (1, 2) 474 ++ (6744, 2) :: (1, 1) :: repeat (1, 2) 16082 ++ (1821, 2) :: (1, 1) :: repeat (1, 2) 308090 ++ (3396738, 2) :: (1, 1) :: repeat (1, 2) 7965811 ++ (18372851, 2) :: (1, 1) :: repeat (1, 2) 58806192 ++ w) 1); closearith.
  }
  (* step 129: M pop12 (34,) *)
  apply (hsteps_trans _ (HB [5] 49 1 75 ((140, 2) :: (1, 1) :: repeat (1, 2) 474 ++ (6744, 2) :: (1, 1) :: repeat (1, 2) 16082 ++ (1821, 2) :: (1, 1) :: repeat (1, 2) 308090 ++ (3396738, 2) :: (1, 1) :: repeat (1, 2) 7965811 ++ (18372851, 2) :: (1, 1) :: repeat (1, 2) 58806192 ++ w) 1)).
  {
    apply (pop12 34 [5] 15 7 ((140, 2) :: (1, 1) :: repeat (1, 2) 474 ++ (6744, 2) :: (1, 1) :: repeat (1, 2) 16082 ++ (1821, 2) :: (1, 1) :: repeat (1, 2) 308090 ++ (3396738, 2) :: (1, 1) :: repeat (1, 2) 7965811 ++ (18372851, 2) :: (1, 1) :: repeat (1, 2) 58806192 ++ w) 1); closearith.
  }
  (* step 130: sTUP *)
  apply (hsteps_trans _ (HC [5] 49 74 2 ((138, 2) :: (1, 1) :: repeat (1, 2) 474 ++ (6744, 2) :: (1, 1) :: repeat (1, 2) 16082 ++ (1821, 2) :: (1, 1) :: repeat (1, 2) 308090 ++ (3396738, 2) :: (1, 1) :: repeat (1, 2) 7965811 ++ (18372851, 2) :: (1, 1) :: repeat (1, 2) 58806192 ++ w) 1)).
  {
    replace ((138, 2) :: (1, 1) :: repeat (1, 2) 474 ++ (6744, 2) :: (1, 1) :: repeat (1, 2) 16082 ++ (1821, 2) :: (1, 1) :: repeat (1, 2) 308090 ++ (3396738, 2) :: (1, 1) :: repeat (1, 2) 7965811 ++ (18372851, 2) :: (1, 1) :: repeat (1, 2) 58806192 ++ w) with ((140 - 2, 2) :: (1, 1) :: repeat (1, 2) 474 ++ (6744, 2) :: (1, 1) :: repeat (1, 2) 16082 ++ (1821, 2) :: (1, 1) :: repeat (1, 2) 308090 ++ (3396738, 2) :: (1, 1) :: repeat (1, 2) 7965811 ++ (18372851, 2) :: (1, 1) :: repeat (1, 2) 58806192 ++ w) by sec_eq.
    apply (sTUP [5] 49 75 140 2 ((1, 1) :: repeat (1, 2) 474 ++ (6744, 2) :: (1, 1) :: repeat (1, 2) 16082 ++ (1821, 2) :: (1, 1) :: repeat (1, 2) 308090 ++ (3396738, 2) :: (1, 1) :: repeat (1, 2) 7965811 ++ (18372851, 2) :: (1, 1) :: repeat (1, 2) 58806192 ++ w) 1); closearith.
  }
  (* step 131: hGRIND_even 35 *)
  apply (hsteps_trans _ (HB [5] 48 1 74 ((2, 2) :: (138, 2) :: (1, 1) :: repeat (1, 2) 474 ++ (6744, 2) :: (1, 1) :: repeat (1, 2) 16082 ++ (1821, 2) :: (1, 1) :: repeat (1, 2) 308090 ++ (3396738, 2) :: (1, 1) :: repeat (1, 2) 7965811 ++ (18372851, 2) :: (1, 1) :: repeat (1, 2) 58806192 ++ w) 1)).
  {
    apply (hGRIND_even 35 [5] 48 ((138, 2) :: (1, 1) :: repeat (1, 2) 474 ++ (6744, 2) :: (1, 1) :: repeat (1, 2) 16082 ++ (1821, 2) :: (1, 1) :: repeat (1, 2) 308090 ++ (3396738, 2) :: (1, 1) :: repeat (1, 2) 7965811 ++ (18372851, 2) :: (1, 1) :: repeat (1, 2) 58806192 ++ w) 1); closearith.
  }
  (* step 132: P TUP2_1 *)
  apply (hsteps_trans _ (HC [49; 5] 74 1 2 ((136, 2) :: (1, 1) :: repeat (1, 2) 474 ++ (6744, 2) :: (1, 1) :: repeat (1, 2) 16082 ++ (1821, 2) :: (1, 1) :: repeat (1, 2) 308090 ++ (3396738, 2) :: (1, 1) :: repeat (1, 2) 7965811 ++ (18372851, 2) :: (1, 1) :: repeat (1, 2) 58806192 ++ w) 1)).
  {
    replace ((136, 2) :: (1, 1) :: repeat (1, 2) 474 ++ (6744, 2) :: (1, 1) :: repeat (1, 2) 16082 ++ (1821, 2) :: (1, 1) :: repeat (1, 2) 308090 ++ (3396738, 2) :: (1, 1) :: repeat (1, 2) 7965811 ++ (18372851, 2) :: (1, 1) :: repeat (1, 2) 58806192 ++ w) with ((138 - 2, 2) :: (1, 1) :: repeat (1, 2) 474 ++ (6744, 2) :: (1, 1) :: repeat (1, 2) 16082 ++ (1821, 2) :: (1, 1) :: repeat (1, 2) 308090 ++ (3396738, 2) :: (1, 1) :: repeat (1, 2) 7965811 ++ (18372851, 2) :: (1, 1) :: repeat (1, 2) 58806192 ++ w) by sec_eq.
    apply (sTUP2_1 [5] 48 73 138 ((1, 1) :: repeat (1, 2) 474 ++ (6744, 2) :: (1, 1) :: repeat (1, 2) 16082 ++ (1821, 2) :: (1, 1) :: repeat (1, 2) 308090 ++ (3396738, 2) :: (1, 1) :: repeat (1, 2) 7965811 ++ (18372851, 2) :: (1, 1) :: repeat (1, 2) 58806192 ++ w) 1); closearith.
  }
  (* step 133: P TDN *)
  apply (hsteps_trans _ (HB [49; 5] 74 1 4 ((136, 2) :: (1, 1) :: repeat (1, 2) 474 ++ (6744, 2) :: (1, 1) :: repeat (1, 2) 16082 ++ (1821, 2) :: (1, 1) :: repeat (1, 2) 308090 ++ (3396738, 2) :: (1, 1) :: repeat (1, 2) 7965811 ++ (18372851, 2) :: (1, 1) :: repeat (1, 2) 58806192 ++ w) 1)).
  {
    apply (sTDN [49; 5] 74 ((136, 2) :: (1, 1) :: repeat (1, 2) 474 ++ (6744, 2) :: (1, 1) :: repeat (1, 2) 16082 ++ (1821, 2) :: (1, 1) :: repeat (1, 2) 308090 ++ (3396738, 2) :: (1, 1) :: repeat (1, 2) 7965811 ++ (18372851, 2) :: (1, 1) :: repeat (1, 2) 58806192 ++ w) 1).
  }
  (* step 134: sTUP *)
  apply (hsteps_trans _ (HC [49; 5] 74 3 2 ((134, 2) :: (1, 1) :: repeat (1, 2) 474 ++ (6744, 2) :: (1, 1) :: repeat (1, 2) 16082 ++ (1821, 2) :: (1, 1) :: repeat (1, 2) 308090 ++ (3396738, 2) :: (1, 1) :: repeat (1, 2) 7965811 ++ (18372851, 2) :: (1, 1) :: repeat (1, 2) 58806192 ++ w) 1)).
  {
    replace ((134, 2) :: (1, 1) :: repeat (1, 2) 474 ++ (6744, 2) :: (1, 1) :: repeat (1, 2) 16082 ++ (1821, 2) :: (1, 1) :: repeat (1, 2) 308090 ++ (3396738, 2) :: (1, 1) :: repeat (1, 2) 7965811 ++ (18372851, 2) :: (1, 1) :: repeat (1, 2) 58806192 ++ w) with ((136 - 2, 2) :: (1, 1) :: repeat (1, 2) 474 ++ (6744, 2) :: (1, 1) :: repeat (1, 2) 16082 ++ (1821, 2) :: (1, 1) :: repeat (1, 2) 308090 ++ (3396738, 2) :: (1, 1) :: repeat (1, 2) 7965811 ++ (18372851, 2) :: (1, 1) :: repeat (1, 2) 58806192 ++ w) by sec_eq.
    apply (sTUP [49; 5] 74 4 136 2 ((1, 1) :: repeat (1, 2) 474 ++ (6744, 2) :: (1, 1) :: repeat (1, 2) 16082 ++ (1821, 2) :: (1, 1) :: repeat (1, 2) 308090 ++ (3396738, 2) :: (1, 1) :: repeat (1, 2) 7965811 ++ (18372851, 2) :: (1, 1) :: repeat (1, 2) 58806192 ++ w) 1); closearith.
  }
  (* step 135: CLEANG_even 66 *)
  apply (hsteps_trans _ (HB [49; 5] 74 1 138 ((2, 2) :: (1, 1) :: repeat (1, 2) 474 ++ (6744, 2) :: (1, 1) :: repeat (1, 2) 16082 ++ (1821, 2) :: (1, 1) :: repeat (1, 2) 308090 ++ (3396738, 2) :: (1, 1) :: repeat (1, 2) 7965811 ++ (18372851, 2) :: (1, 1) :: repeat (1, 2) 58806192 ++ w) 1)).
  {
    apply (CLEANG_even 66 [49; 5] 74 ((1, 1) :: repeat (1, 2) 474 ++ (6744, 2) :: (1, 1) :: repeat (1, 2) 16082 ++ (1821, 2) :: (1, 1) :: repeat (1, 2) 308090 ++ (3396738, 2) :: (1, 1) :: repeat (1, 2) 7965811 ++ (18372851, 2) :: (1, 1) :: repeat (1, 2) 58806192 ++ w) 1); closearith.
  }
  (* step 136: P TRANS2_1 *)
  apply (hsteps_trans _ (HB [75; 49; 5] 139 1 3 (repeat (1, 2) 474 ++ (6744, 2) :: (1, 1) :: repeat (1, 2) 16082 ++ (1821, 2) :: (1, 1) :: repeat (1, 2) 308090 ++ (3396738, 2) :: (1, 1) :: repeat (1, 2) 7965811 ++ (18372851, 2) :: (1, 1) :: repeat (1, 2) 58806192 ++ w) 1)).
  {
    apply (sTRANS2_1 [49; 5] 74 137 1 (repeat (1, 2) 474 ++ (6744, 2) :: (1, 1) :: repeat (1, 2) 16082 ++ (1821, 2) :: (1, 1) :: repeat (1, 2) 308090 ++ (3396738, 2) :: (1, 1) :: repeat (1, 2) 7965811 ++ (18372851, 2) :: (1, 1) :: repeat (1, 2) 58806192 ++ w) 1); closearith.
  }
  (* step 137: M pop12 (474,) *)
  apply (hsteps_trans _ (HB [75; 49; 5] 613 1 951 ((6744, 2) :: (1, 1) :: repeat (1, 2) 16082 ++ (1821, 2) :: (1, 1) :: repeat (1, 2) 308090 ++ (3396738, 2) :: (1, 1) :: repeat (1, 2) 7965811 ++ (18372851, 2) :: (1, 1) :: repeat (1, 2) 58806192 ++ w) 1)).
  {
    apply (pop12 474 [75; 49; 5] 139 3 ((6744, 2) :: (1, 1) :: repeat (1, 2) 16082 ++ (1821, 2) :: (1, 1) :: repeat (1, 2) 308090 ++ (3396738, 2) :: (1, 1) :: repeat (1, 2) 7965811 ++ (18372851, 2) :: (1, 1) :: repeat (1, 2) 58806192 ++ w) 1); closearith.
  }
  (* step 138: sTUP *)
  apply (hsteps_trans _ (HC [75; 49; 5] 613 950 2 ((6742, 2) :: (1, 1) :: repeat (1, 2) 16082 ++ (1821, 2) :: (1, 1) :: repeat (1, 2) 308090 ++ (3396738, 2) :: (1, 1) :: repeat (1, 2) 7965811 ++ (18372851, 2) :: (1, 1) :: repeat (1, 2) 58806192 ++ w) 1)).
  {
    replace ((6742, 2) :: (1, 1) :: repeat (1, 2) 16082 ++ (1821, 2) :: (1, 1) :: repeat (1, 2) 308090 ++ (3396738, 2) :: (1, 1) :: repeat (1, 2) 7965811 ++ (18372851, 2) :: (1, 1) :: repeat (1, 2) 58806192 ++ w) with ((6744 - 2, 2) :: (1, 1) :: repeat (1, 2) 16082 ++ (1821, 2) :: (1, 1) :: repeat (1, 2) 308090 ++ (3396738, 2) :: (1, 1) :: repeat (1, 2) 7965811 ++ (18372851, 2) :: (1, 1) :: repeat (1, 2) 58806192 ++ w) by sec_eq.
    apply (sTUP [75; 49; 5] 613 951 6744 2 ((1, 1) :: repeat (1, 2) 16082 ++ (1821, 2) :: (1, 1) :: repeat (1, 2) 308090 ++ (3396738, 2) :: (1, 1) :: repeat (1, 2) 7965811 ++ (18372851, 2) :: (1, 1) :: repeat (1, 2) 58806192 ++ w) 1); closearith.
  }
  (* step 139: hGRIND_even 473 *)
  apply (hsteps_trans _ (HB [75; 49; 5] 612 1 950 ((2, 2) :: (6742, 2) :: (1, 1) :: repeat (1, 2) 16082 ++ (1821, 2) :: (1, 1) :: repeat (1, 2) 308090 ++ (3396738, 2) :: (1, 1) :: repeat (1, 2) 7965811 ++ (18372851, 2) :: (1, 1) :: repeat (1, 2) 58806192 ++ w) 1)).
  {
    apply (hGRIND_even 473 [75; 49; 5] 612 ((6742, 2) :: (1, 1) :: repeat (1, 2) 16082 ++ (1821, 2) :: (1, 1) :: repeat (1, 2) 308090 ++ (3396738, 2) :: (1, 1) :: repeat (1, 2) 7965811 ++ (18372851, 2) :: (1, 1) :: repeat (1, 2) 58806192 ++ w) 1); closearith.
  }
  (* step 140: P TUP2_1 *)
  apply (hsteps_trans _ (HC [613; 75; 49; 5] 950 1 2 ((6740, 2) :: (1, 1) :: repeat (1, 2) 16082 ++ (1821, 2) :: (1, 1) :: repeat (1, 2) 308090 ++ (3396738, 2) :: (1, 1) :: repeat (1, 2) 7965811 ++ (18372851, 2) :: (1, 1) :: repeat (1, 2) 58806192 ++ w) 1)).
  {
    replace ((6740, 2) :: (1, 1) :: repeat (1, 2) 16082 ++ (1821, 2) :: (1, 1) :: repeat (1, 2) 308090 ++ (3396738, 2) :: (1, 1) :: repeat (1, 2) 7965811 ++ (18372851, 2) :: (1, 1) :: repeat (1, 2) 58806192 ++ w) with ((6742 - 2, 2) :: (1, 1) :: repeat (1, 2) 16082 ++ (1821, 2) :: (1, 1) :: repeat (1, 2) 308090 ++ (3396738, 2) :: (1, 1) :: repeat (1, 2) 7965811 ++ (18372851, 2) :: (1, 1) :: repeat (1, 2) 58806192 ++ w) by sec_eq.
    apply (sTUP2_1 [75; 49; 5] 612 949 6742 ((1, 1) :: repeat (1, 2) 16082 ++ (1821, 2) :: (1, 1) :: repeat (1, 2) 308090 ++ (3396738, 2) :: (1, 1) :: repeat (1, 2) 7965811 ++ (18372851, 2) :: (1, 1) :: repeat (1, 2) 58806192 ++ w) 1); closearith.
  }
  (* step 141: P TDN *)
  apply (hsteps_trans _ (HB [613; 75; 49; 5] 950 1 4 ((6740, 2) :: (1, 1) :: repeat (1, 2) 16082 ++ (1821, 2) :: (1, 1) :: repeat (1, 2) 308090 ++ (3396738, 2) :: (1, 1) :: repeat (1, 2) 7965811 ++ (18372851, 2) :: (1, 1) :: repeat (1, 2) 58806192 ++ w) 1)).
  {
    apply (sTDN [613; 75; 49; 5] 950 ((6740, 2) :: (1, 1) :: repeat (1, 2) 16082 ++ (1821, 2) :: (1, 1) :: repeat (1, 2) 308090 ++ (3396738, 2) :: (1, 1) :: repeat (1, 2) 7965811 ++ (18372851, 2) :: (1, 1) :: repeat (1, 2) 58806192 ++ w) 1).
  }
  (* step 142: sTUP *)
  apply (hsteps_trans _ (HC [613; 75; 49; 5] 950 3 2 ((6738, 2) :: (1, 1) :: repeat (1, 2) 16082 ++ (1821, 2) :: (1, 1) :: repeat (1, 2) 308090 ++ (3396738, 2) :: (1, 1) :: repeat (1, 2) 7965811 ++ (18372851, 2) :: (1, 1) :: repeat (1, 2) 58806192 ++ w) 1)).
  {
    replace ((6738, 2) :: (1, 1) :: repeat (1, 2) 16082 ++ (1821, 2) :: (1, 1) :: repeat (1, 2) 308090 ++ (3396738, 2) :: (1, 1) :: repeat (1, 2) 7965811 ++ (18372851, 2) :: (1, 1) :: repeat (1, 2) 58806192 ++ w) with ((6740 - 2, 2) :: (1, 1) :: repeat (1, 2) 16082 ++ (1821, 2) :: (1, 1) :: repeat (1, 2) 308090 ++ (3396738, 2) :: (1, 1) :: repeat (1, 2) 7965811 ++ (18372851, 2) :: (1, 1) :: repeat (1, 2) 58806192 ++ w) by sec_eq.
    apply (sTUP [613; 75; 49; 5] 950 4 6740 2 ((1, 1) :: repeat (1, 2) 16082 ++ (1821, 2) :: (1, 1) :: repeat (1, 2) 308090 ++ (3396738, 2) :: (1, 1) :: repeat (1, 2) 7965811 ++ (18372851, 2) :: (1, 1) :: repeat (1, 2) 58806192 ++ w) 1); closearith.
  }
  (* step 143: DIPGRIND 950 4838 *)
  apply (hsteps_trans _ (HC [613; 75; 49; 5] 0 3 2 (repeat (1, 2) 950 ++ (4838, 2) :: (1, 1) :: repeat (1, 2) 16082 ++ (1821, 2) :: (1, 1) :: repeat (1, 2) 308090 ++ (3396738, 2) :: (1, 1) :: repeat (1, 2) 7965811 ++ (18372851, 2) :: (1, 1) :: repeat (1, 2) 58806192 ++ w) 1)).
  {
    apply (DIPGRIND 950 4838 [613; 75; 49; 5] ((1, 1) :: repeat (1, 2) 16082 ++ (1821, 2) :: (1, 1) :: repeat (1, 2) 308090 ++ (3396738, 2) :: (1, 1) :: repeat (1, 2) 7965811 ++ (18372851, 2) :: (1, 1) :: repeat (1, 2) 58806192 ++ w) 1); closearith.
  }
  (* step 144: P PX2A *)
  apply (hsteps_trans _ (HC [49; 5] 74 611 2 ((1, 1) :: repeat (1, 2) 952 ++ (4838, 2) :: (1, 1) :: repeat (1, 2) 16082 ++ (1821, 2) :: (1, 1) :: repeat (1, 2) 308090 ++ (3396738, 2) :: (1, 1) :: repeat (1, 2) 7965811 ++ (18372851, 2) :: (1, 1) :: repeat (1, 2) 58806192 ++ w) 1)).
  {
    exact (hsteps_step _ _ _ (hPX2A 610 74 [49; 5] (repeat (1, 2) 950 ++ (4838, 2) :: (1, 1) :: repeat (1, 2) 16082 ++ (1821, 2) :: (1, 1) :: repeat (1, 2) 308090 ++ (3396738, 2) :: (1, 1) :: repeat (1, 2) 7965811 ++ (18372851, 2) :: (1, 1) :: repeat (1, 2) 58806192 ++ w) 1) (hsteps_refl _)).
  }
  (* step 145: P PUSH *)
  apply (hsteps_trans _ (HC [49; 5] 73 1 2 ((609, 2) :: (1, 1) :: repeat (1, 2) 952 ++ (4838, 2) :: (1, 1) :: repeat (1, 2) 16082 ++ (1821, 2) :: (1, 1) :: repeat (1, 2) 308090 ++ (3396738, 2) :: (1, 1) :: repeat (1, 2) 7965811 ++ (18372851, 2) :: (1, 1) :: repeat (1, 2) 58806192 ++ w) 1)).
  {
    replace ((609, 2) :: (1, 1) :: repeat (1, 2) 952 ++ (4838, 2) :: (1, 1) :: repeat (1, 2) 16082 ++ (1821, 2) :: (1, 1) :: repeat (1, 2) 308090 ++ (3396738, 2) :: (1, 1) :: repeat (1, 2) 7965811 ++ (18372851, 2) :: (1, 1) :: repeat (1, 2) 58806192 ++ w) with ((611 - 2, 2) :: (1, 1) :: repeat (1, 2) 952 ++ (4838, 2) :: (1, 1) :: repeat (1, 2) 16082 ++ (1821, 2) :: (1, 1) :: repeat (1, 2) 308090 ++ (3396738, 2) :: (1, 1) :: repeat (1, 2) 7965811 ++ (18372851, 2) :: (1, 1) :: repeat (1, 2) 58806192 ++ w) by sec_eq.
    apply (sPUSH [49; 5] 73 611 ((1, 1) :: repeat (1, 2) 952 ++ (4838, 2) :: (1, 1) :: repeat (1, 2) 16082 ++ (1821, 2) :: (1, 1) :: repeat (1, 2) 308090 ++ (3396738, 2) :: (1, 1) :: repeat (1, 2) 7965811 ++ (18372851, 2) :: (1, 1) :: repeat (1, 2) 58806192 ++ w) 1); closearith.
  }
  (* step 146: P TDN *)
  apply (hsteps_trans _ (HB [49; 5] 73 1 4 ((609, 2) :: (1, 1) :: repeat (1, 2) 952 ++ (4838, 2) :: (1, 1) :: repeat (1, 2) 16082 ++ (1821, 2) :: (1, 1) :: repeat (1, 2) 308090 ++ (3396738, 2) :: (1, 1) :: repeat (1, 2) 7965811 ++ (18372851, 2) :: (1, 1) :: repeat (1, 2) 58806192 ++ w) 1)).
  {
    apply (sTDN [49; 5] 73 ((609, 2) :: (1, 1) :: repeat (1, 2) 952 ++ (4838, 2) :: (1, 1) :: repeat (1, 2) 16082 ++ (1821, 2) :: (1, 1) :: repeat (1, 2) 308090 ++ (3396738, 2) :: (1, 1) :: repeat (1, 2) 7965811 ++ (18372851, 2) :: (1, 1) :: repeat (1, 2) 58806192 ++ w) 1).
  }
  (* step 147: sTUP *)
  apply (hsteps_trans _ (HC [49; 5] 73 3 2 ((607, 2) :: (1, 1) :: repeat (1, 2) 952 ++ (4838, 2) :: (1, 1) :: repeat (1, 2) 16082 ++ (1821, 2) :: (1, 1) :: repeat (1, 2) 308090 ++ (3396738, 2) :: (1, 1) :: repeat (1, 2) 7965811 ++ (18372851, 2) :: (1, 1) :: repeat (1, 2) 58806192 ++ w) 1)).
  {
    replace ((607, 2) :: (1, 1) :: repeat (1, 2) 952 ++ (4838, 2) :: (1, 1) :: repeat (1, 2) 16082 ++ (1821, 2) :: (1, 1) :: repeat (1, 2) 308090 ++ (3396738, 2) :: (1, 1) :: repeat (1, 2) 7965811 ++ (18372851, 2) :: (1, 1) :: repeat (1, 2) 58806192 ++ w) with ((609 - 2, 2) :: (1, 1) :: repeat (1, 2) 952 ++ (4838, 2) :: (1, 1) :: repeat (1, 2) 16082 ++ (1821, 2) :: (1, 1) :: repeat (1, 2) 308090 ++ (3396738, 2) :: (1, 1) :: repeat (1, 2) 7965811 ++ (18372851, 2) :: (1, 1) :: repeat (1, 2) 58806192 ++ w) by sec_eq.
    apply (sTUP [49; 5] 73 4 609 2 ((1, 1) :: repeat (1, 2) 952 ++ (4838, 2) :: (1, 1) :: repeat (1, 2) 16082 ++ (1821, 2) :: (1, 1) :: repeat (1, 2) 308090 ++ (3396738, 2) :: (1, 1) :: repeat (1, 2) 7965811 ++ (18372851, 2) :: (1, 1) :: repeat (1, 2) 58806192 ++ w) 1); closearith.
  }
  (* step 148: DIPGRIND 73 461 *)
  apply (hsteps_trans _ (HC [49; 5] 0 3 2 (repeat (1, 2) 73 ++ (461, 2) :: (1, 1) :: repeat (1, 2) 952 ++ (4838, 2) :: (1, 1) :: repeat (1, 2) 16082 ++ (1821, 2) :: (1, 1) :: repeat (1, 2) 308090 ++ (3396738, 2) :: (1, 1) :: repeat (1, 2) 7965811 ++ (18372851, 2) :: (1, 1) :: repeat (1, 2) 58806192 ++ w) 1)).
  {
    apply (DIPGRIND 73 461 [49; 5] ((1, 1) :: repeat (1, 2) 952 ++ (4838, 2) :: (1, 1) :: repeat (1, 2) 16082 ++ (1821, 2) :: (1, 1) :: repeat (1, 2) 308090 ++ (3396738, 2) :: (1, 1) :: repeat (1, 2) 7965811 ++ (18372851, 2) :: (1, 1) :: repeat (1, 2) 58806192 ++ w) 1); closearith.
  }
  (* step 149: P PX2A *)
  apply (hsteps_trans _ (HC [] 4 47 2 ((1, 1) :: repeat (1, 2) 75 ++ (461, 2) :: (1, 1) :: repeat (1, 2) 952 ++ (4838, 2) :: (1, 1) :: repeat (1, 2) 16082 ++ (1821, 2) :: (1, 1) :: repeat (1, 2) 308090 ++ (3396738, 2) :: (1, 1) :: repeat (1, 2) 7965811 ++ (18372851, 2) :: (1, 1) :: repeat (1, 2) 58806192 ++ w) 1)).
  {
    exact (hsteps_step _ _ _ (hPX2A 46 4 [] (repeat (1, 2) 73 ++ (461, 2) :: (1, 1) :: repeat (1, 2) 952 ++ (4838, 2) :: (1, 1) :: repeat (1, 2) 16082 ++ (1821, 2) :: (1, 1) :: repeat (1, 2) 308090 ++ (3396738, 2) :: (1, 1) :: repeat (1, 2) 7965811 ++ (18372851, 2) :: (1, 1) :: repeat (1, 2) 58806192 ++ w) 1) (hsteps_refl _)).
  }
  (* step 150: P PUSH *)
  apply (hsteps_trans _ (HC [] 3 1 2 ((45, 2) :: (1, 1) :: repeat (1, 2) 75 ++ (461, 2) :: (1, 1) :: repeat (1, 2) 952 ++ (4838, 2) :: (1, 1) :: repeat (1, 2) 16082 ++ (1821, 2) :: (1, 1) :: repeat (1, 2) 308090 ++ (3396738, 2) :: (1, 1) :: repeat (1, 2) 7965811 ++ (18372851, 2) :: (1, 1) :: repeat (1, 2) 58806192 ++ w) 1)).
  {
    replace ((45, 2) :: (1, 1) :: repeat (1, 2) 75 ++ (461, 2) :: (1, 1) :: repeat (1, 2) 952 ++ (4838, 2) :: (1, 1) :: repeat (1, 2) 16082 ++ (1821, 2) :: (1, 1) :: repeat (1, 2) 308090 ++ (3396738, 2) :: (1, 1) :: repeat (1, 2) 7965811 ++ (18372851, 2) :: (1, 1) :: repeat (1, 2) 58806192 ++ w) with ((47 - 2, 2) :: (1, 1) :: repeat (1, 2) 75 ++ (461, 2) :: (1, 1) :: repeat (1, 2) 952 ++ (4838, 2) :: (1, 1) :: repeat (1, 2) 16082 ++ (1821, 2) :: (1, 1) :: repeat (1, 2) 308090 ++ (3396738, 2) :: (1, 1) :: repeat (1, 2) 7965811 ++ (18372851, 2) :: (1, 1) :: repeat (1, 2) 58806192 ++ w) by sec_eq.
    apply (sPUSH [] 3 47 ((1, 1) :: repeat (1, 2) 75 ++ (461, 2) :: (1, 1) :: repeat (1, 2) 952 ++ (4838, 2) :: (1, 1) :: repeat (1, 2) 16082 ++ (1821, 2) :: (1, 1) :: repeat (1, 2) 308090 ++ (3396738, 2) :: (1, 1) :: repeat (1, 2) 7965811 ++ (18372851, 2) :: (1, 1) :: repeat (1, 2) 58806192 ++ w) 1); closearith.
  }
  (* step 151: P TDN *)
  apply (hsteps_trans _ (HB [] 3 1 4 ((45, 2) :: (1, 1) :: repeat (1, 2) 75 ++ (461, 2) :: (1, 1) :: repeat (1, 2) 952 ++ (4838, 2) :: (1, 1) :: repeat (1, 2) 16082 ++ (1821, 2) :: (1, 1) :: repeat (1, 2) 308090 ++ (3396738, 2) :: (1, 1) :: repeat (1, 2) 7965811 ++ (18372851, 2) :: (1, 1) :: repeat (1, 2) 58806192 ++ w) 1)).
  {
    apply (sTDN [] 3 ((45, 2) :: (1, 1) :: repeat (1, 2) 75 ++ (461, 2) :: (1, 1) :: repeat (1, 2) 952 ++ (4838, 2) :: (1, 1) :: repeat (1, 2) 16082 ++ (1821, 2) :: (1, 1) :: repeat (1, 2) 308090 ++ (3396738, 2) :: (1, 1) :: repeat (1, 2) 7965811 ++ (18372851, 2) :: (1, 1) :: repeat (1, 2) 58806192 ++ w) 1).
  }
  (* step 152: sTUP *)
  apply (hsteps_trans _ (HC [] 3 3 2 ((43, 2) :: (1, 1) :: repeat (1, 2) 75 ++ (461, 2) :: (1, 1) :: repeat (1, 2) 952 ++ (4838, 2) :: (1, 1) :: repeat (1, 2) 16082 ++ (1821, 2) :: (1, 1) :: repeat (1, 2) 308090 ++ (3396738, 2) :: (1, 1) :: repeat (1, 2) 7965811 ++ (18372851, 2) :: (1, 1) :: repeat (1, 2) 58806192 ++ w) 1)).
  {
    replace ((43, 2) :: (1, 1) :: repeat (1, 2) 75 ++ (461, 2) :: (1, 1) :: repeat (1, 2) 952 ++ (4838, 2) :: (1, 1) :: repeat (1, 2) 16082 ++ (1821, 2) :: (1, 1) :: repeat (1, 2) 308090 ++ (3396738, 2) :: (1, 1) :: repeat (1, 2) 7965811 ++ (18372851, 2) :: (1, 1) :: repeat (1, 2) 58806192 ++ w) with ((45 - 2, 2) :: (1, 1) :: repeat (1, 2) 75 ++ (461, 2) :: (1, 1) :: repeat (1, 2) 952 ++ (4838, 2) :: (1, 1) :: repeat (1, 2) 16082 ++ (1821, 2) :: (1, 1) :: repeat (1, 2) 308090 ++ (3396738, 2) :: (1, 1) :: repeat (1, 2) 7965811 ++ (18372851, 2) :: (1, 1) :: repeat (1, 2) 58806192 ++ w) by sec_eq.
    apply (sTUP [] 3 4 45 2 ((1, 1) :: repeat (1, 2) 75 ++ (461, 2) :: (1, 1) :: repeat (1, 2) 952 ++ (4838, 2) :: (1, 1) :: repeat (1, 2) 16082 ++ (1821, 2) :: (1, 1) :: repeat (1, 2) 308090 ++ (3396738, 2) :: (1, 1) :: repeat (1, 2) 7965811 ++ (18372851, 2) :: (1, 1) :: repeat (1, 2) 58806192 ++ w) 1); closearith.
  }
  (* step 153: DIPGRIND 3 37 *)
  apply (hsteps_trans _ (HC [] 0 3 2 (repeat (1, 2) 3 ++ (37, 2) :: (1, 1) :: repeat (1, 2) 75 ++ (461, 2) :: (1, 1) :: repeat (1, 2) 952 ++ (4838, 2) :: (1, 1) :: repeat (1, 2) 16082 ++ (1821, 2) :: (1, 1) :: repeat (1, 2) 308090 ++ (3396738, 2) :: (1, 1) :: repeat (1, 2) 7965811 ++ (18372851, 2) :: (1, 1) :: repeat (1, 2) 58806192 ++ w) 1)).
  {
    apply (DIPGRIND 3 37 [] ((1, 1) :: repeat (1, 2) 75 ++ (461, 2) :: (1, 1) :: repeat (1, 2) 952 ++ (4838, 2) :: (1, 1) :: repeat (1, 2) 16082 ++ (1821, 2) :: (1, 1) :: repeat (1, 2) 308090 ++ (3396738, 2) :: (1, 1) :: repeat (1, 2) 7965811 ++ (18372851, 2) :: (1, 1) :: repeat (1, 2) 58806192 ++ w) 1); closearith.
  }
  (* step 154: P PUSHX *)
  apply (hsteps_trans _ (HB [] 1 1 7 (repeat (1, 2) 3 ++ (37, 2) :: (1, 1) :: repeat (1, 2) 75 ++ (461, 2) :: (1, 1) :: repeat (1, 2) 952 ++ (4838, 2) :: (1, 1) :: repeat (1, 2) 16082 ++ (1821, 2) :: (1, 1) :: repeat (1, 2) 308090 ++ (3396738, 2) :: (1, 1) :: repeat (1, 2) 7965811 ++ (18372851, 2) :: (1, 1) :: repeat (1, 2) 58806192 ++ w) 1)).
  {
    exact (hsteps_step _ _ _ (hPUSHX (repeat (1, 2) 3 ++ (37, 2) :: (1, 1) :: repeat (1, 2) 75 ++ (461, 2) :: (1, 1) :: repeat (1, 2) 952 ++ (4838, 2) :: (1, 1) :: repeat (1, 2) 16082 ++ (1821, 2) :: (1, 1) :: repeat (1, 2) 308090 ++ (3396738, 2) :: (1, 1) :: repeat (1, 2) 7965811 ++ (18372851, 2) :: (1, 1) :: repeat (1, 2) 58806192 ++ w) 1) (hsteps_refl _)).
  }
  (* step 155: M pop12 (3,) *)
  apply (hsteps_trans _ (HB [] 4 1 13 ((37, 2) :: (1, 1) :: repeat (1, 2) 75 ++ (461, 2) :: (1, 1) :: repeat (1, 2) 952 ++ (4838, 2) :: (1, 1) :: repeat (1, 2) 16082 ++ (1821, 2) :: (1, 1) :: repeat (1, 2) 308090 ++ (3396738, 2) :: (1, 1) :: repeat (1, 2) 7965811 ++ (18372851, 2) :: (1, 1) :: repeat (1, 2) 58806192 ++ w) 1)).
  {
    apply (pop12 3 [] 1 7 ((37, 2) :: (1, 1) :: repeat (1, 2) 75 ++ (461, 2) :: (1, 1) :: repeat (1, 2) 952 ++ (4838, 2) :: (1, 1) :: repeat (1, 2) 16082 ++ (1821, 2) :: (1, 1) :: repeat (1, 2) 308090 ++ (3396738, 2) :: (1, 1) :: repeat (1, 2) 7965811 ++ (18372851, 2) :: (1, 1) :: repeat (1, 2) 58806192 ++ w) 1); closearith.
  }
  (* step 156: sTUP *)
  apply (hsteps_trans _ (HC [] 4 12 2 ((35, 2) :: (1, 1) :: repeat (1, 2) 75 ++ (461, 2) :: (1, 1) :: repeat (1, 2) 952 ++ (4838, 2) :: (1, 1) :: repeat (1, 2) 16082 ++ (1821, 2) :: (1, 1) :: repeat (1, 2) 308090 ++ (3396738, 2) :: (1, 1) :: repeat (1, 2) 7965811 ++ (18372851, 2) :: (1, 1) :: repeat (1, 2) 58806192 ++ w) 1)).
  {
    replace ((35, 2) :: (1, 1) :: repeat (1, 2) 75 ++ (461, 2) :: (1, 1) :: repeat (1, 2) 952 ++ (4838, 2) :: (1, 1) :: repeat (1, 2) 16082 ++ (1821, 2) :: (1, 1) :: repeat (1, 2) 308090 ++ (3396738, 2) :: (1, 1) :: repeat (1, 2) 7965811 ++ (18372851, 2) :: (1, 1) :: repeat (1, 2) 58806192 ++ w) with ((37 - 2, 2) :: (1, 1) :: repeat (1, 2) 75 ++ (461, 2) :: (1, 1) :: repeat (1, 2) 952 ++ (4838, 2) :: (1, 1) :: repeat (1, 2) 16082 ++ (1821, 2) :: (1, 1) :: repeat (1, 2) 308090 ++ (3396738, 2) :: (1, 1) :: repeat (1, 2) 7965811 ++ (18372851, 2) :: (1, 1) :: repeat (1, 2) 58806192 ++ w) by sec_eq.
    apply (sTUP [] 4 13 37 2 ((1, 1) :: repeat (1, 2) 75 ++ (461, 2) :: (1, 1) :: repeat (1, 2) 952 ++ (4838, 2) :: (1, 1) :: repeat (1, 2) 16082 ++ (1821, 2) :: (1, 1) :: repeat (1, 2) 308090 ++ (3396738, 2) :: (1, 1) :: repeat (1, 2) 7965811 ++ (18372851, 2) :: (1, 1) :: repeat (1, 2) 58806192 ++ w) 1); closearith.
  }
  (* step 157: P PUSH *)
  apply (hsteps_trans _ (HC [] 3 1 2 ((10, 2) :: (35, 2) :: (1, 1) :: repeat (1, 2) 75 ++ (461, 2) :: (1, 1) :: repeat (1, 2) 952 ++ (4838, 2) :: (1, 1) :: repeat (1, 2) 16082 ++ (1821, 2) :: (1, 1) :: repeat (1, 2) 308090 ++ (3396738, 2) :: (1, 1) :: repeat (1, 2) 7965811 ++ (18372851, 2) :: (1, 1) :: repeat (1, 2) 58806192 ++ w) 1)).
  {
    replace ((10, 2) :: (35, 2) :: (1, 1) :: repeat (1, 2) 75 ++ (461, 2) :: (1, 1) :: repeat (1, 2) 952 ++ (4838, 2) :: (1, 1) :: repeat (1, 2) 16082 ++ (1821, 2) :: (1, 1) :: repeat (1, 2) 308090 ++ (3396738, 2) :: (1, 1) :: repeat (1, 2) 7965811 ++ (18372851, 2) :: (1, 1) :: repeat (1, 2) 58806192 ++ w) with ((12 - 2, 2) :: (35, 2) :: (1, 1) :: repeat (1, 2) 75 ++ (461, 2) :: (1, 1) :: repeat (1, 2) 952 ++ (4838, 2) :: (1, 1) :: repeat (1, 2) 16082 ++ (1821, 2) :: (1, 1) :: repeat (1, 2) 308090 ++ (3396738, 2) :: (1, 1) :: repeat (1, 2) 7965811 ++ (18372851, 2) :: (1, 1) :: repeat (1, 2) 58806192 ++ w) by sec_eq.
    apply (sPUSH [] 3 12 ((35, 2) :: (1, 1) :: repeat (1, 2) 75 ++ (461, 2) :: (1, 1) :: repeat (1, 2) 952 ++ (4838, 2) :: (1, 1) :: repeat (1, 2) 16082 ++ (1821, 2) :: (1, 1) :: repeat (1, 2) 308090 ++ (3396738, 2) :: (1, 1) :: repeat (1, 2) 7965811 ++ (18372851, 2) :: (1, 1) :: repeat (1, 2) 58806192 ++ w) 1); closearith.
  }
  (* step 158: P TDN *)
  apply (hsteps_trans _ (HB [] 3 1 4 ((10, 2) :: (35, 2) :: (1, 1) :: repeat (1, 2) 75 ++ (461, 2) :: (1, 1) :: repeat (1, 2) 952 ++ (4838, 2) :: (1, 1) :: repeat (1, 2) 16082 ++ (1821, 2) :: (1, 1) :: repeat (1, 2) 308090 ++ (3396738, 2) :: (1, 1) :: repeat (1, 2) 7965811 ++ (18372851, 2) :: (1, 1) :: repeat (1, 2) 58806192 ++ w) 1)).
  {
    apply (sTDN [] 3 ((10, 2) :: (35, 2) :: (1, 1) :: repeat (1, 2) 75 ++ (461, 2) :: (1, 1) :: repeat (1, 2) 952 ++ (4838, 2) :: (1, 1) :: repeat (1, 2) 16082 ++ (1821, 2) :: (1, 1) :: repeat (1, 2) 308090 ++ (3396738, 2) :: (1, 1) :: repeat (1, 2) 7965811 ++ (18372851, 2) :: (1, 1) :: repeat (1, 2) 58806192 ++ w) 1).
  }
  (* step 159: sTUP *)
  apply (hsteps_trans _ (HC [] 3 3 2 ((8, 2) :: (35, 2) :: (1, 1) :: repeat (1, 2) 75 ++ (461, 2) :: (1, 1) :: repeat (1, 2) 952 ++ (4838, 2) :: (1, 1) :: repeat (1, 2) 16082 ++ (1821, 2) :: (1, 1) :: repeat (1, 2) 308090 ++ (3396738, 2) :: (1, 1) :: repeat (1, 2) 7965811 ++ (18372851, 2) :: (1, 1) :: repeat (1, 2) 58806192 ++ w) 1)).
  {
    replace ((8, 2) :: (35, 2) :: (1, 1) :: repeat (1, 2) 75 ++ (461, 2) :: (1, 1) :: repeat (1, 2) 952 ++ (4838, 2) :: (1, 1) :: repeat (1, 2) 16082 ++ (1821, 2) :: (1, 1) :: repeat (1, 2) 308090 ++ (3396738, 2) :: (1, 1) :: repeat (1, 2) 7965811 ++ (18372851, 2) :: (1, 1) :: repeat (1, 2) 58806192 ++ w) with ((10 - 2, 2) :: (35, 2) :: (1, 1) :: repeat (1, 2) 75 ++ (461, 2) :: (1, 1) :: repeat (1, 2) 952 ++ (4838, 2) :: (1, 1) :: repeat (1, 2) 16082 ++ (1821, 2) :: (1, 1) :: repeat (1, 2) 308090 ++ (3396738, 2) :: (1, 1) :: repeat (1, 2) 7965811 ++ (18372851, 2) :: (1, 1) :: repeat (1, 2) 58806192 ++ w) by sec_eq.
    apply (sTUP [] 3 4 10 2 ((35, 2) :: (1, 1) :: repeat (1, 2) 75 ++ (461, 2) :: (1, 1) :: repeat (1, 2) 952 ++ (4838, 2) :: (1, 1) :: repeat (1, 2) 16082 ++ (1821, 2) :: (1, 1) :: repeat (1, 2) 308090 ++ (3396738, 2) :: (1, 1) :: repeat (1, 2) 7965811 ++ (18372851, 2) :: (1, 1) :: repeat (1, 2) 58806192 ++ w) 1); closearith.
  }
  (* step 160: DIPGRIND 3 2 *)
  apply (hsteps_trans _ (HC [] 0 3 2 (repeat (1, 2) 3 ++ (2, 2) :: (35, 2) :: (1, 1) :: repeat (1, 2) 75 ++ (461, 2) :: (1, 1) :: repeat (1, 2) 952 ++ (4838, 2) :: (1, 1) :: repeat (1, 2) 16082 ++ (1821, 2) :: (1, 1) :: repeat (1, 2) 308090 ++ (3396738, 2) :: (1, 1) :: repeat (1, 2) 7965811 ++ (18372851, 2) :: (1, 1) :: repeat (1, 2) 58806192 ++ w) 1)).
  {
    apply (DIPGRIND 3 2 [] ((35, 2) :: (1, 1) :: repeat (1, 2) 75 ++ (461, 2) :: (1, 1) :: repeat (1, 2) 952 ++ (4838, 2) :: (1, 1) :: repeat (1, 2) 16082 ++ (1821, 2) :: (1, 1) :: repeat (1, 2) 308090 ++ (3396738, 2) :: (1, 1) :: repeat (1, 2) 7965811 ++ (18372851, 2) :: (1, 1) :: repeat (1, 2) 58806192 ++ w) 1); closearith.
  }
  (* step 161: P PUSHX *)
  apply (hsteps_trans _ (HB [] 1 1 7 (repeat (1, 2) 3 ++ (2, 2) :: (35, 2) :: (1, 1) :: repeat (1, 2) 75 ++ (461, 2) :: (1, 1) :: repeat (1, 2) 952 ++ (4838, 2) :: (1, 1) :: repeat (1, 2) 16082 ++ (1821, 2) :: (1, 1) :: repeat (1, 2) 308090 ++ (3396738, 2) :: (1, 1) :: repeat (1, 2) 7965811 ++ (18372851, 2) :: (1, 1) :: repeat (1, 2) 58806192 ++ w) 1)).
  {
    exact (hsteps_step _ _ _ (hPUSHX (repeat (1, 2) 3 ++ (2, 2) :: (35, 2) :: (1, 1) :: repeat (1, 2) 75 ++ (461, 2) :: (1, 1) :: repeat (1, 2) 952 ++ (4838, 2) :: (1, 1) :: repeat (1, 2) 16082 ++ (1821, 2) :: (1, 1) :: repeat (1, 2) 308090 ++ (3396738, 2) :: (1, 1) :: repeat (1, 2) 7965811 ++ (18372851, 2) :: (1, 1) :: repeat (1, 2) 58806192 ++ w) 1) (hsteps_refl _)).
  }
  (* step 162: M pop12 (3,) *)
  apply (hsteps_trans _ (HB [] 4 1 13 ((2, 2) :: (35, 2) :: (1, 1) :: repeat (1, 2) 75 ++ (461, 2) :: (1, 1) :: repeat (1, 2) 952 ++ (4838, 2) :: (1, 1) :: repeat (1, 2) 16082 ++ (1821, 2) :: (1, 1) :: repeat (1, 2) 308090 ++ (3396738, 2) :: (1, 1) :: repeat (1, 2) 7965811 ++ (18372851, 2) :: (1, 1) :: repeat (1, 2) 58806192 ++ w) 1)).
  {
    apply (pop12 3 [] 1 7 ((2, 2) :: (35, 2) :: (1, 1) :: repeat (1, 2) 75 ++ (461, 2) :: (1, 1) :: repeat (1, 2) 952 ++ (4838, 2) :: (1, 1) :: repeat (1, 2) 16082 ++ (1821, 2) :: (1, 1) :: repeat (1, 2) 308090 ++ (3396738, 2) :: (1, 1) :: repeat (1, 2) 7965811 ++ (18372851, 2) :: (1, 1) :: repeat (1, 2) 58806192 ++ w) 1); closearith.
  }
  (* step 163: P TUP2_1 *)
  apply (hsteps_trans _ (HC [5] 13 1 2 ((33, 2) :: (1, 1) :: repeat (1, 2) 75 ++ (461, 2) :: (1, 1) :: repeat (1, 2) 952 ++ (4838, 2) :: (1, 1) :: repeat (1, 2) 16082 ++ (1821, 2) :: (1, 1) :: repeat (1, 2) 308090 ++ (3396738, 2) :: (1, 1) :: repeat (1, 2) 7965811 ++ (18372851, 2) :: (1, 1) :: repeat (1, 2) 58806192 ++ w) 1)).
  {
    replace ((33, 2) :: (1, 1) :: repeat (1, 2) 75 ++ (461, 2) :: (1, 1) :: repeat (1, 2) 952 ++ (4838, 2) :: (1, 1) :: repeat (1, 2) 16082 ++ (1821, 2) :: (1, 1) :: repeat (1, 2) 308090 ++ (3396738, 2) :: (1, 1) :: repeat (1, 2) 7965811 ++ (18372851, 2) :: (1, 1) :: repeat (1, 2) 58806192 ++ w) with ((35 - 2, 2) :: (1, 1) :: repeat (1, 2) 75 ++ (461, 2) :: (1, 1) :: repeat (1, 2) 952 ++ (4838, 2) :: (1, 1) :: repeat (1, 2) 16082 ++ (1821, 2) :: (1, 1) :: repeat (1, 2) 308090 ++ (3396738, 2) :: (1, 1) :: repeat (1, 2) 7965811 ++ (18372851, 2) :: (1, 1) :: repeat (1, 2) 58806192 ++ w) by sec_eq.
    apply (sTUP2_1 [] 4 12 35 ((1, 1) :: repeat (1, 2) 75 ++ (461, 2) :: (1, 1) :: repeat (1, 2) 952 ++ (4838, 2) :: (1, 1) :: repeat (1, 2) 16082 ++ (1821, 2) :: (1, 1) :: repeat (1, 2) 308090 ++ (3396738, 2) :: (1, 1) :: repeat (1, 2) 7965811 ++ (18372851, 2) :: (1, 1) :: repeat (1, 2) 58806192 ++ w) 1); closearith.
  }
  (* step 164: P TDN *)
  apply (hsteps_trans _ (HB [5] 13 1 4 ((33, 2) :: (1, 1) :: repeat (1, 2) 75 ++ (461, 2) :: (1, 1) :: repeat (1, 2) 952 ++ (4838, 2) :: (1, 1) :: repeat (1, 2) 16082 ++ (1821, 2) :: (1, 1) :: repeat (1, 2) 308090 ++ (3396738, 2) :: (1, 1) :: repeat (1, 2) 7965811 ++ (18372851, 2) :: (1, 1) :: repeat (1, 2) 58806192 ++ w) 1)).
  {
    apply (sTDN [5] 13 ((33, 2) :: (1, 1) :: repeat (1, 2) 75 ++ (461, 2) :: (1, 1) :: repeat (1, 2) 952 ++ (4838, 2) :: (1, 1) :: repeat (1, 2) 16082 ++ (1821, 2) :: (1, 1) :: repeat (1, 2) 308090 ++ (3396738, 2) :: (1, 1) :: repeat (1, 2) 7965811 ++ (18372851, 2) :: (1, 1) :: repeat (1, 2) 58806192 ++ w) 1).
  }
  (* step 165: sTUP *)
  apply (hsteps_trans _ (HC [5] 13 3 2 ((31, 2) :: (1, 1) :: repeat (1, 2) 75 ++ (461, 2) :: (1, 1) :: repeat (1, 2) 952 ++ (4838, 2) :: (1, 1) :: repeat (1, 2) 16082 ++ (1821, 2) :: (1, 1) :: repeat (1, 2) 308090 ++ (3396738, 2) :: (1, 1) :: repeat (1, 2) 7965811 ++ (18372851, 2) :: (1, 1) :: repeat (1, 2) 58806192 ++ w) 1)).
  {
    replace ((31, 2) :: (1, 1) :: repeat (1, 2) 75 ++ (461, 2) :: (1, 1) :: repeat (1, 2) 952 ++ (4838, 2) :: (1, 1) :: repeat (1, 2) 16082 ++ (1821, 2) :: (1, 1) :: repeat (1, 2) 308090 ++ (3396738, 2) :: (1, 1) :: repeat (1, 2) 7965811 ++ (18372851, 2) :: (1, 1) :: repeat (1, 2) 58806192 ++ w) with ((33 - 2, 2) :: (1, 1) :: repeat (1, 2) 75 ++ (461, 2) :: (1, 1) :: repeat (1, 2) 952 ++ (4838, 2) :: (1, 1) :: repeat (1, 2) 16082 ++ (1821, 2) :: (1, 1) :: repeat (1, 2) 308090 ++ (3396738, 2) :: (1, 1) :: repeat (1, 2) 7965811 ++ (18372851, 2) :: (1, 1) :: repeat (1, 2) 58806192 ++ w) by sec_eq.
    apply (sTUP [5] 13 4 33 2 ((1, 1) :: repeat (1, 2) 75 ++ (461, 2) :: (1, 1) :: repeat (1, 2) 952 ++ (4838, 2) :: (1, 1) :: repeat (1, 2) 16082 ++ (1821, 2) :: (1, 1) :: repeat (1, 2) 308090 ++ (3396738, 2) :: (1, 1) :: repeat (1, 2) 7965811 ++ (18372851, 2) :: (1, 1) :: repeat (1, 2) 58806192 ++ w) 1); closearith.
  }
  (* step 166: DIPGRIND 13 5 *)
  apply (hsteps_trans _ (HC [5] 0 3 2 (repeat (1, 2) 13 ++ (5, 2) :: (1, 1) :: repeat (1, 2) 75 ++ (461, 2) :: (1, 1) :: repeat (1, 2) 952 ++ (4838, 2) :: (1, 1) :: repeat (1, 2) 16082 ++ (1821, 2) :: (1, 1) :: repeat (1, 2) 308090 ++ (3396738, 2) :: (1, 1) :: repeat (1, 2) 7965811 ++ (18372851, 2) :: (1, 1) :: repeat (1, 2) 58806192 ++ w) 1)).
  {
    apply (DIPGRIND 13 5 [5] ((1, 1) :: repeat (1, 2) 75 ++ (461, 2) :: (1, 1) :: repeat (1, 2) 952 ++ (4838, 2) :: (1, 1) :: repeat (1, 2) 16082 ++ (1821, 2) :: (1, 1) :: repeat (1, 2) 308090 ++ (3396738, 2) :: (1, 1) :: repeat (1, 2) 7965811 ++ (18372851, 2) :: (1, 1) :: repeat (1, 2) 58806192 ++ w) 1); closearith.
  }
  (* step 167: P PX2Bgen *)
  apply (hsteps_trans _ (HB [0] 3 1 2 (repeat (1, 2) 1 ++ (1, 1) :: repeat (1, 2) 15 ++ (5, 2) :: (1, 1) :: repeat (1, 2) 75 ++ (461, 2) :: (1, 1) :: repeat (1, 2) 952 ++ (4838, 2) :: (1, 1) :: repeat (1, 2) 16082 ++ (1821, 2) :: (1, 1) :: repeat (1, 2) 308090 ++ (3396738, 2) :: (1, 1) :: repeat (1, 2) 7965811 ++ (18372851, 2) :: (1, 1) :: repeat (1, 2) 58806192 ++ w) 1)).
  {
    exact (hsteps_step _ _ _ (hPX2Bgen 0 (repeat (1, 2) 13 ++ (5, 2) :: (1, 1) :: repeat (1, 2) 75 ++ (461, 2) :: (1, 1) :: repeat (1, 2) 952 ++ (4838, 2) :: (1, 1) :: repeat (1, 2) 16082 ++ (1821, 2) :: (1, 1) :: repeat (1, 2) 308090 ++ (3396738, 2) :: (1, 1) :: repeat (1, 2) 7965811 ++ (18372851, 2) :: (1, 1) :: repeat (1, 2) 58806192 ++ w) 1) (hsteps_refl _)).
  }
  (* step 168: M pop12 (1,) *)
  apply (pop12 1 [0] 3 2 ((1, 1) :: repeat (1, 2) 15 ++ (5, 2) :: (1, 1) :: repeat (1, 2) 75 ++ (461, 2) :: (1, 1) :: repeat (1, 2) 952 ++ (4838, 2) :: (1, 1) :: repeat (1, 2) 16082 ++ (1821, 2) :: (1, 1) :: repeat (1, 2) 308090 ++ (3396738, 2) :: (1, 1) :: repeat (1, 2) 7965811 ++ (18372851, 2) :: (1, 1) :: repeat (1, 2) 58806192 ++ w) 1); closearith.
Qed.

(* CASCADE60d: steps 169-224 of the CASCADE60 chain. *)
Lemma CASCADE60d : forall w,
  hsteps (HB [0] 4 1 4 ((1, 1) :: repeat (1, 2) 15 ++ (5, 2) :: (1, 1) :: repeat (1, 2) 75 ++ (461, 2) :: (1, 1) :: repeat (1, 2) 952 ++ (4838, 2) :: (1, 1) :: repeat (1, 2) 16082 ++ (1821, 2) :: (1, 1) :: repeat (1, 2) 308090 ++ (3396738, 2) :: (1, 1) :: repeat (1, 2) 7965811 ++ (18372851, 2) :: (1, 1) :: repeat (1, 2) 58806192 ++ w) 1)
         (HC [20] 0 3 2 (repeat (1, 2) 201 ++ (932, 2) :: (1, 1) :: repeat (1, 2) 2050 ++ (736, 2) :: (1, 1) :: repeat (1, 2) 16082 ++ (1821, 2) :: (1, 1) :: repeat (1, 2) 308090 ++ (3396738, 2) :: (1, 1) :: repeat (1, 2) 7965811 ++ (18372851, 2) :: (1, 1) :: repeat (1, 2) 58806192 ++ w) 1).
Proof.
  intro w.
  (* step 169: P POP *)
  apply (hsteps_trans _ (HB [0] 5 1 5 (repeat (1, 2) 15 ++ (5, 2) :: (1, 1) :: repeat (1, 2) 75 ++ (461, 2) :: (1, 1) :: repeat (1, 2) 952 ++ (4838, 2) :: (1, 1) :: repeat (1, 2) 16082 ++ (1821, 2) :: (1, 1) :: repeat (1, 2) 308090 ++ (3396738, 2) :: (1, 1) :: repeat (1, 2) 7965811 ++ (18372851, 2) :: (1, 1) :: repeat (1, 2) 58806192 ++ w) 1)).
  {
    apply (sPOP1 [0] 4 4 (repeat (1, 2) 15 ++ (5, 2) :: (1, 1) :: repeat (1, 2) 75 ++ (461, 2) :: (1, 1) :: repeat (1, 2) 952 ++ (4838, 2) :: (1, 1) :: repeat (1, 2) 16082 ++ (1821, 2) :: (1, 1) :: repeat (1, 2) 308090 ++ (3396738, 2) :: (1, 1) :: repeat (1, 2) 7965811 ++ (18372851, 2) :: (1, 1) :: repeat (1, 2) 58806192 ++ w) 1); closearith.
  }
  (* step 170: M pop12 (15,) *)
  apply (hsteps_trans _ (HB [0] 20 1 35 ((5, 2) :: (1, 1) :: repeat (1, 2) 75 ++ (461, 2) :: (1, 1) :: repeat (1, 2) 952 ++ (4838, 2) :: (1, 1) :: repeat (1, 2) 16082 ++ (1821, 2) :: (1, 1) :: repeat (1, 2) 308090 ++ (3396738, 2) :: (1, 1) :: repeat (1, 2) 7965811 ++ (18372851, 2) :: (1, 1) :: repeat (1, 2) 58806192 ++ w) 1)).
  {
    apply (pop12 15 [0] 5 5 ((5, 2) :: (1, 1) :: repeat (1, 2) 75 ++ (461, 2) :: (1, 1) :: repeat (1, 2) 952 ++ (4838, 2) :: (1, 1) :: repeat (1, 2) 16082 ++ (1821, 2) :: (1, 1) :: repeat (1, 2) 308090 ++ (3396738, 2) :: (1, 1) :: repeat (1, 2) 7965811 ++ (18372851, 2) :: (1, 1) :: repeat (1, 2) 58806192 ++ w) 1); closearith.
  }
  (* step 171: sTUP *)
  apply (hsteps_trans _ (HC [0] 20 34 2 ((3, 2) :: (1, 1) :: repeat (1, 2) 75 ++ (461, 2) :: (1, 1) :: repeat (1, 2) 952 ++ (4838, 2) :: (1, 1) :: repeat (1, 2) 16082 ++ (1821, 2) :: (1, 1) :: repeat (1, 2) 308090 ++ (3396738, 2) :: (1, 1) :: repeat (1, 2) 7965811 ++ (18372851, 2) :: (1, 1) :: repeat (1, 2) 58806192 ++ w) 1)).
  {
    replace ((3, 2) :: (1, 1) :: repeat (1, 2) 75 ++ (461, 2) :: (1, 1) :: repeat (1, 2) 952 ++ (4838, 2) :: (1, 1) :: repeat (1, 2) 16082 ++ (1821, 2) :: (1, 1) :: repeat (1, 2) 308090 ++ (3396738, 2) :: (1, 1) :: repeat (1, 2) 7965811 ++ (18372851, 2) :: (1, 1) :: repeat (1, 2) 58806192 ++ w) with ((5 - 2, 2) :: (1, 1) :: repeat (1, 2) 75 ++ (461, 2) :: (1, 1) :: repeat (1, 2) 952 ++ (4838, 2) :: (1, 1) :: repeat (1, 2) 16082 ++ (1821, 2) :: (1, 1) :: repeat (1, 2) 308090 ++ (3396738, 2) :: (1, 1) :: repeat (1, 2) 7965811 ++ (18372851, 2) :: (1, 1) :: repeat (1, 2) 58806192 ++ w) by sec_eq.
    apply (sTUP [0] 20 35 5 2 ((1, 1) :: repeat (1, 2) 75 ++ (461, 2) :: (1, 1) :: repeat (1, 2) 952 ++ (4838, 2) :: (1, 1) :: repeat (1, 2) 16082 ++ (1821, 2) :: (1, 1) :: repeat (1, 2) 308090 ++ (3396738, 2) :: (1, 1) :: repeat (1, 2) 7965811 ++ (18372851, 2) :: (1, 1) :: repeat (1, 2) 58806192 ++ w) 1); closearith.
  }
  (* step 172: hGRIND_even 15 *)
  apply (hsteps_trans _ (HB [0] 19 1 34 ((2, 2) :: (3, 2) :: (1, 1) :: repeat (1, 2) 75 ++ (461, 2) :: (1, 1) :: repeat (1, 2) 952 ++ (4838, 2) :: (1, 1) :: repeat (1, 2) 16082 ++ (1821, 2) :: (1, 1) :: repeat (1, 2) 308090 ++ (3396738, 2) :: (1, 1) :: repeat (1, 2) 7965811 ++ (18372851, 2) :: (1, 1) :: repeat (1, 2) 58806192 ++ w) 1)).
  {
    apply (hGRIND_even 15 [0] 19 ((3, 2) :: (1, 1) :: repeat (1, 2) 75 ++ (461, 2) :: (1, 1) :: repeat (1, 2) 952 ++ (4838, 2) :: (1, 1) :: repeat (1, 2) 16082 ++ (1821, 2) :: (1, 1) :: repeat (1, 2) 308090 ++ (3396738, 2) :: (1, 1) :: repeat (1, 2) 7965811 ++ (18372851, 2) :: (1, 1) :: repeat (1, 2) 58806192 ++ w) 1); closearith.
  }
  (* step 173: P TUP2_1 *)
  apply (hsteps_trans _ (HC [20; 0] 34 1 2 (repeat (1, 2) 1 ++ (1, 1) :: repeat (1, 2) 75 ++ (461, 2) :: (1, 1) :: repeat (1, 2) 952 ++ (4838, 2) :: (1, 1) :: repeat (1, 2) 16082 ++ (1821, 2) :: (1, 1) :: repeat (1, 2) 308090 ++ (3396738, 2) :: (1, 1) :: repeat (1, 2) 7965811 ++ (18372851, 2) :: (1, 1) :: repeat (1, 2) 58806192 ++ w) 1)).
  {
    replace (repeat (1, 2) 1 ++ (1, 1) :: repeat (1, 2) 75 ++ (461, 2) :: (1, 1) :: repeat (1, 2) 952 ++ (4838, 2) :: (1, 1) :: repeat (1, 2) 16082 ++ (1821, 2) :: (1, 1) :: repeat (1, 2) 308090 ++ (3396738, 2) :: (1, 1) :: repeat (1, 2) 7965811 ++ (18372851, 2) :: (1, 1) :: repeat (1, 2) 58806192 ++ w) with ((3 - 2, 2) :: (1, 1) :: repeat (1, 2) 75 ++ (461, 2) :: (1, 1) :: repeat (1, 2) 952 ++ (4838, 2) :: (1, 1) :: repeat (1, 2) 16082 ++ (1821, 2) :: (1, 1) :: repeat (1, 2) 308090 ++ (3396738, 2) :: (1, 1) :: repeat (1, 2) 7965811 ++ (18372851, 2) :: (1, 1) :: repeat (1, 2) 58806192 ++ w) by sec_eq.
    apply (sTUP2_1 [0] 19 33 3 ((1, 1) :: repeat (1, 2) 75 ++ (461, 2) :: (1, 1) :: repeat (1, 2) 952 ++ (4838, 2) :: (1, 1) :: repeat (1, 2) 16082 ++ (1821, 2) :: (1, 1) :: repeat (1, 2) 308090 ++ (3396738, 2) :: (1, 1) :: repeat (1, 2) 7965811 ++ (18372851, 2) :: (1, 1) :: repeat (1, 2) 58806192 ++ w) 1); closearith.
  }
  (* step 174: P TDN *)
  apply (hsteps_trans _ (HB [20; 0] 34 1 4 (repeat (1, 2) 1 ++ (1, 1) :: repeat (1, 2) 75 ++ (461, 2) :: (1, 1) :: repeat (1, 2) 952 ++ (4838, 2) :: (1, 1) :: repeat (1, 2) 16082 ++ (1821, 2) :: (1, 1) :: repeat (1, 2) 308090 ++ (3396738, 2) :: (1, 1) :: repeat (1, 2) 7965811 ++ (18372851, 2) :: (1, 1) :: repeat (1, 2) 58806192 ++ w) 1)).
  {
    apply (sTDN [20; 0] 34 (repeat (1, 2) 1 ++ (1, 1) :: repeat (1, 2) 75 ++ (461, 2) :: (1, 1) :: repeat (1, 2) 952 ++ (4838, 2) :: (1, 1) :: repeat (1, 2) 16082 ++ (1821, 2) :: (1, 1) :: repeat (1, 2) 308090 ++ (3396738, 2) :: (1, 1) :: repeat (1, 2) 7965811 ++ (18372851, 2) :: (1, 1) :: repeat (1, 2) 58806192 ++ w) 1).
  }
  (* step 175: M pop12 (1,) *)
  apply (hsteps_trans _ (HB [20; 0] 35 1 6 ((1, 1) :: repeat (1, 2) 75 ++ (461, 2) :: (1, 1) :: repeat (1, 2) 952 ++ (4838, 2) :: (1, 1) :: repeat (1, 2) 16082 ++ (1821, 2) :: (1, 1) :: repeat (1, 2) 308090 ++ (3396738, 2) :: (1, 1) :: repeat (1, 2) 7965811 ++ (18372851, 2) :: (1, 1) :: repeat (1, 2) 58806192 ++ w) 1)).
  {
    apply (pop12 1 [20; 0] 34 4 ((1, 1) :: repeat (1, 2) 75 ++ (461, 2) :: (1, 1) :: repeat (1, 2) 952 ++ (4838, 2) :: (1, 1) :: repeat (1, 2) 16082 ++ (1821, 2) :: (1, 1) :: repeat (1, 2) 308090 ++ (3396738, 2) :: (1, 1) :: repeat (1, 2) 7965811 ++ (18372851, 2) :: (1, 1) :: repeat (1, 2) 58806192 ++ w) 1); closearith.
  }
  (* step 176: P POP *)
  apply (hsteps_trans _ (HB [20; 0] 36 1 7 (repeat (1, 2) 75 ++ (461, 2) :: (1, 1) :: repeat (1, 2) 952 ++ (4838, 2) :: (1, 1) :: repeat (1, 2) 16082 ++ (1821, 2) :: (1, 1) :: repeat (1, 2) 308090 ++ (3396738, 2) :: (1, 1) :: repeat (1, 2) 7965811 ++ (18372851, 2) :: (1, 1) :: repeat (1, 2) 58806192 ++ w) 1)).
  {
    apply (sPOP1 [20; 0] 35 6 (repeat (1, 2) 75 ++ (461, 2) :: (1, 1) :: repeat (1, 2) 952 ++ (4838, 2) :: (1, 1) :: repeat (1, 2) 16082 ++ (1821, 2) :: (1, 1) :: repeat (1, 2) 308090 ++ (3396738, 2) :: (1, 1) :: repeat (1, 2) 7965811 ++ (18372851, 2) :: (1, 1) :: repeat (1, 2) 58806192 ++ w) 1); closearith.
  }
  (* step 177: M pop12 (75,) *)
  apply (hsteps_trans _ (HB [20; 0] 111 1 157 ((461, 2) :: (1, 1) :: repeat (1, 2) 952 ++ (4838, 2) :: (1, 1) :: repeat (1, 2) 16082 ++ (1821, 2) :: (1, 1) :: repeat (1, 2) 308090 ++ (3396738, 2) :: (1, 1) :: repeat (1, 2) 7965811 ++ (18372851, 2) :: (1, 1) :: repeat (1, 2) 58806192 ++ w) 1)).
  {
    apply (pop12 75 [20; 0] 36 7 ((461, 2) :: (1, 1) :: repeat (1, 2) 952 ++ (4838, 2) :: (1, 1) :: repeat (1, 2) 16082 ++ (1821, 2) :: (1, 1) :: repeat (1, 2) 308090 ++ (3396738, 2) :: (1, 1) :: repeat (1, 2) 7965811 ++ (18372851, 2) :: (1, 1) :: repeat (1, 2) 58806192 ++ w) 1); closearith.
  }
  (* step 178: sTUP *)
  apply (hsteps_trans _ (HC [20; 0] 111 156 2 ((459, 2) :: (1, 1) :: repeat (1, 2) 952 ++ (4838, 2) :: (1, 1) :: repeat (1, 2) 16082 ++ (1821, 2) :: (1, 1) :: repeat (1, 2) 308090 ++ (3396738, 2) :: (1, 1) :: repeat (1, 2) 7965811 ++ (18372851, 2) :: (1, 1) :: repeat (1, 2) 58806192 ++ w) 1)).
  {
    replace ((459, 2) :: (1, 1) :: repeat (1, 2) 952 ++ (4838, 2) :: (1, 1) :: repeat (1, 2) 16082 ++ (1821, 2) :: (1, 1) :: repeat (1, 2) 308090 ++ (3396738, 2) :: (1, 1) :: repeat (1, 2) 7965811 ++ (18372851, 2) :: (1, 1) :: repeat (1, 2) 58806192 ++ w) with ((461 - 2, 2) :: (1, 1) :: repeat (1, 2) 952 ++ (4838, 2) :: (1, 1) :: repeat (1, 2) 16082 ++ (1821, 2) :: (1, 1) :: repeat (1, 2) 308090 ++ (3396738, 2) :: (1, 1) :: repeat (1, 2) 7965811 ++ (18372851, 2) :: (1, 1) :: repeat (1, 2) 58806192 ++ w) by sec_eq.
    apply (sTUP [20; 0] 111 157 461 2 ((1, 1) :: repeat (1, 2) 952 ++ (4838, 2) :: (1, 1) :: repeat (1, 2) 16082 ++ (1821, 2) :: (1, 1) :: repeat (1, 2) 308090 ++ (3396738, 2) :: (1, 1) :: repeat (1, 2) 7965811 ++ (18372851, 2) :: (1, 1) :: repeat (1, 2) 58806192 ++ w) 1); closearith.
  }
  (* step 179: hGRIND_even 76 *)
  apply (hsteps_trans _ (HB [20; 0] 110 1 156 ((2, 2) :: (459, 2) :: (1, 1) :: repeat (1, 2) 952 ++ (4838, 2) :: (1, 1) :: repeat (1, 2) 16082 ++ (1821, 2) :: (1, 1) :: repeat (1, 2) 308090 ++ (3396738, 2) :: (1, 1) :: repeat (1, 2) 7965811 ++ (18372851, 2) :: (1, 1) :: repeat (1, 2) 58806192 ++ w) 1)).
  {
    apply (hGRIND_even 76 [20; 0] 110 ((459, 2) :: (1, 1) :: repeat (1, 2) 952 ++ (4838, 2) :: (1, 1) :: repeat (1, 2) 16082 ++ (1821, 2) :: (1, 1) :: repeat (1, 2) 308090 ++ (3396738, 2) :: (1, 1) :: repeat (1, 2) 7965811 ++ (18372851, 2) :: (1, 1) :: repeat (1, 2) 58806192 ++ w) 1); closearith.
  }
  (* step 180: P TUP2_1 *)
  apply (hsteps_trans _ (HC [111; 20; 0] 156 1 2 ((457, 2) :: (1, 1) :: repeat (1, 2) 952 ++ (4838, 2) :: (1, 1) :: repeat (1, 2) 16082 ++ (1821, 2) :: (1, 1) :: repeat (1, 2) 308090 ++ (3396738, 2) :: (1, 1) :: repeat (1, 2) 7965811 ++ (18372851, 2) :: (1, 1) :: repeat (1, 2) 58806192 ++ w) 1)).
  {
    replace ((457, 2) :: (1, 1) :: repeat (1, 2) 952 ++ (4838, 2) :: (1, 1) :: repeat (1, 2) 16082 ++ (1821, 2) :: (1, 1) :: repeat (1, 2) 308090 ++ (3396738, 2) :: (1, 1) :: repeat (1, 2) 7965811 ++ (18372851, 2) :: (1, 1) :: repeat (1, 2) 58806192 ++ w) with ((459 - 2, 2) :: (1, 1) :: repeat (1, 2) 952 ++ (4838, 2) :: (1, 1) :: repeat (1, 2) 16082 ++ (1821, 2) :: (1, 1) :: repeat (1, 2) 308090 ++ (3396738, 2) :: (1, 1) :: repeat (1, 2) 7965811 ++ (18372851, 2) :: (1, 1) :: repeat (1, 2) 58806192 ++ w) by sec_eq.
    apply (sTUP2_1 [20; 0] 110 155 459 ((1, 1) :: repeat (1, 2) 952 ++ (4838, 2) :: (1, 1) :: repeat (1, 2) 16082 ++ (1821, 2) :: (1, 1) :: repeat (1, 2) 308090 ++ (3396738, 2) :: (1, 1) :: repeat (1, 2) 7965811 ++ (18372851, 2) :: (1, 1) :: repeat (1, 2) 58806192 ++ w) 1); closearith.
  }
  (* step 181: P TDN *)
  apply (hsteps_trans _ (HB [111; 20; 0] 156 1 4 ((457, 2) :: (1, 1) :: repeat (1, 2) 952 ++ (4838, 2) :: (1, 1) :: repeat (1, 2) 16082 ++ (1821, 2) :: (1, 1) :: repeat (1, 2) 308090 ++ (3396738, 2) :: (1, 1) :: repeat (1, 2) 7965811 ++ (18372851, 2) :: (1, 1) :: repeat (1, 2) 58806192 ++ w) 1)).
  {
    apply (sTDN [111; 20; 0] 156 ((457, 2) :: (1, 1) :: repeat (1, 2) 952 ++ (4838, 2) :: (1, 1) :: repeat (1, 2) 16082 ++ (1821, 2) :: (1, 1) :: repeat (1, 2) 308090 ++ (3396738, 2) :: (1, 1) :: repeat (1, 2) 7965811 ++ (18372851, 2) :: (1, 1) :: repeat (1, 2) 58806192 ++ w) 1).
  }
  (* step 182: sTUP *)
  apply (hsteps_trans _ (HC [111; 20; 0] 156 3 2 ((455, 2) :: (1, 1) :: repeat (1, 2) 952 ++ (4838, 2) :: (1, 1) :: repeat (1, 2) 16082 ++ (1821, 2) :: (1, 1) :: repeat (1, 2) 308090 ++ (3396738, 2) :: (1, 1) :: repeat (1, 2) 7965811 ++ (18372851, 2) :: (1, 1) :: repeat (1, 2) 58806192 ++ w) 1)).
  {
    replace ((455, 2) :: (1, 1) :: repeat (1, 2) 952 ++ (4838, 2) :: (1, 1) :: repeat (1, 2) 16082 ++ (1821, 2) :: (1, 1) :: repeat (1, 2) 308090 ++ (3396738, 2) :: (1, 1) :: repeat (1, 2) 7965811 ++ (18372851, 2) :: (1, 1) :: repeat (1, 2) 58806192 ++ w) with ((457 - 2, 2) :: (1, 1) :: repeat (1, 2) 952 ++ (4838, 2) :: (1, 1) :: repeat (1, 2) 16082 ++ (1821, 2) :: (1, 1) :: repeat (1, 2) 308090 ++ (3396738, 2) :: (1, 1) :: repeat (1, 2) 7965811 ++ (18372851, 2) :: (1, 1) :: repeat (1, 2) 58806192 ++ w) by sec_eq.
    apply (sTUP [111; 20; 0] 156 4 457 2 ((1, 1) :: repeat (1, 2) 952 ++ (4838, 2) :: (1, 1) :: repeat (1, 2) 16082 ++ (1821, 2) :: (1, 1) :: repeat (1, 2) 308090 ++ (3396738, 2) :: (1, 1) :: repeat (1, 2) 7965811 ++ (18372851, 2) :: (1, 1) :: repeat (1, 2) 58806192 ++ w) 1); closearith.
  }
  (* step 183: DIPGRIND 156 143 *)
  apply (hsteps_trans _ (HC [111; 20; 0] 0 3 2 (repeat (1, 2) 156 ++ (143, 2) :: (1, 1) :: repeat (1, 2) 952 ++ (4838, 2) :: (1, 1) :: repeat (1, 2) 16082 ++ (1821, 2) :: (1, 1) :: repeat (1, 2) 308090 ++ (3396738, 2) :: (1, 1) :: repeat (1, 2) 7965811 ++ (18372851, 2) :: (1, 1) :: repeat (1, 2) 58806192 ++ w) 1)).
  {
    apply (DIPGRIND 156 143 [111; 20; 0] ((1, 1) :: repeat (1, 2) 952 ++ (4838, 2) :: (1, 1) :: repeat (1, 2) 16082 ++ (1821, 2) :: (1, 1) :: repeat (1, 2) 308090 ++ (3396738, 2) :: (1, 1) :: repeat (1, 2) 7965811 ++ (18372851, 2) :: (1, 1) :: repeat (1, 2) 58806192 ++ w) 1); closearith.
  }
  (* step 184: P PX2A *)
  apply (hsteps_trans _ (HC [0] 19 109 2 ((1, 1) :: repeat (1, 2) 158 ++ (143, 2) :: (1, 1) :: repeat (1, 2) 952 ++ (4838, 2) :: (1, 1) :: repeat (1, 2) 16082 ++ (1821, 2) :: (1, 1) :: repeat (1, 2) 308090 ++ (3396738, 2) :: (1, 1) :: repeat (1, 2) 7965811 ++ (18372851, 2) :: (1, 1) :: repeat (1, 2) 58806192 ++ w) 1)).
  {
    exact (hsteps_step _ _ _ (hPX2A 108 19 [0] (repeat (1, 2) 156 ++ (143, 2) :: (1, 1) :: repeat (1, 2) 952 ++ (4838, 2) :: (1, 1) :: repeat (1, 2) 16082 ++ (1821, 2) :: (1, 1) :: repeat (1, 2) 308090 ++ (3396738, 2) :: (1, 1) :: repeat (1, 2) 7965811 ++ (18372851, 2) :: (1, 1) :: repeat (1, 2) 58806192 ++ w) 1) (hsteps_refl _)).
  }
  (* step 185: P PUSH *)
  apply (hsteps_trans _ (HC [0] 18 1 2 ((107, 2) :: (1, 1) :: repeat (1, 2) 158 ++ (143, 2) :: (1, 1) :: repeat (1, 2) 952 ++ (4838, 2) :: (1, 1) :: repeat (1, 2) 16082 ++ (1821, 2) :: (1, 1) :: repeat (1, 2) 308090 ++ (3396738, 2) :: (1, 1) :: repeat (1, 2) 7965811 ++ (18372851, 2) :: (1, 1) :: repeat (1, 2) 58806192 ++ w) 1)).
  {
    replace ((107, 2) :: (1, 1) :: repeat (1, 2) 158 ++ (143, 2) :: (1, 1) :: repeat (1, 2) 952 ++ (4838, 2) :: (1, 1) :: repeat (1, 2) 16082 ++ (1821, 2) :: (1, 1) :: repeat (1, 2) 308090 ++ (3396738, 2) :: (1, 1) :: repeat (1, 2) 7965811 ++ (18372851, 2) :: (1, 1) :: repeat (1, 2) 58806192 ++ w) with ((109 - 2, 2) :: (1, 1) :: repeat (1, 2) 158 ++ (143, 2) :: (1, 1) :: repeat (1, 2) 952 ++ (4838, 2) :: (1, 1) :: repeat (1, 2) 16082 ++ (1821, 2) :: (1, 1) :: repeat (1, 2) 308090 ++ (3396738, 2) :: (1, 1) :: repeat (1, 2) 7965811 ++ (18372851, 2) :: (1, 1) :: repeat (1, 2) 58806192 ++ w) by sec_eq.
    apply (sPUSH [0] 18 109 ((1, 1) :: repeat (1, 2) 158 ++ (143, 2) :: (1, 1) :: repeat (1, 2) 952 ++ (4838, 2) :: (1, 1) :: repeat (1, 2) 16082 ++ (1821, 2) :: (1, 1) :: repeat (1, 2) 308090 ++ (3396738, 2) :: (1, 1) :: repeat (1, 2) 7965811 ++ (18372851, 2) :: (1, 1) :: repeat (1, 2) 58806192 ++ w) 1); closearith.
  }
  (* step 186: P TDN *)
  apply (hsteps_trans _ (HB [0] 18 1 4 ((107, 2) :: (1, 1) :: repeat (1, 2) 158 ++ (143, 2) :: (1, 1) :: repeat (1, 2) 952 ++ (4838, 2) :: (1, 1) :: repeat (1, 2) 16082 ++ (1821, 2) :: (1, 1) :: repeat (1, 2) 308090 ++ (3396738, 2) :: (1, 1) :: repeat (1, 2) 7965811 ++ (18372851, 2) :: (1, 1) :: repeat (1, 2) 58806192 ++ w) 1)).
  {
    apply (sTDN [0] 18 ((107, 2) :: (1, 1) :: repeat (1, 2) 158 ++ (143, 2) :: (1, 1) :: repeat (1, 2) 952 ++ (4838, 2) :: (1, 1) :: repeat (1, 2) 16082 ++ (1821, 2) :: (1, 1) :: repeat (1, 2) 308090 ++ (3396738, 2) :: (1, 1) :: repeat (1, 2) 7965811 ++ (18372851, 2) :: (1, 1) :: repeat (1, 2) 58806192 ++ w) 1).
  }
  (* step 187: sTUP *)
  apply (hsteps_trans _ (HC [0] 18 3 2 ((105, 2) :: (1, 1) :: repeat (1, 2) 158 ++ (143, 2) :: (1, 1) :: repeat (1, 2) 952 ++ (4838, 2) :: (1, 1) :: repeat (1, 2) 16082 ++ (1821, 2) :: (1, 1) :: repeat (1, 2) 308090 ++ (3396738, 2) :: (1, 1) :: repeat (1, 2) 7965811 ++ (18372851, 2) :: (1, 1) :: repeat (1, 2) 58806192 ++ w) 1)).
  {
    replace ((105, 2) :: (1, 1) :: repeat (1, 2) 158 ++ (143, 2) :: (1, 1) :: repeat (1, 2) 952 ++ (4838, 2) :: (1, 1) :: repeat (1, 2) 16082 ++ (1821, 2) :: (1, 1) :: repeat (1, 2) 308090 ++ (3396738, 2) :: (1, 1) :: repeat (1, 2) 7965811 ++ (18372851, 2) :: (1, 1) :: repeat (1, 2) 58806192 ++ w) with ((107 - 2, 2) :: (1, 1) :: repeat (1, 2) 158 ++ (143, 2) :: (1, 1) :: repeat (1, 2) 952 ++ (4838, 2) :: (1, 1) :: repeat (1, 2) 16082 ++ (1821, 2) :: (1, 1) :: repeat (1, 2) 308090 ++ (3396738, 2) :: (1, 1) :: repeat (1, 2) 7965811 ++ (18372851, 2) :: (1, 1) :: repeat (1, 2) 58806192 ++ w) by sec_eq.
    apply (sTUP [0] 18 4 107 2 ((1, 1) :: repeat (1, 2) 158 ++ (143, 2) :: (1, 1) :: repeat (1, 2) 952 ++ (4838, 2) :: (1, 1) :: repeat (1, 2) 16082 ++ (1821, 2) :: (1, 1) :: repeat (1, 2) 308090 ++ (3396738, 2) :: (1, 1) :: repeat (1, 2) 7965811 ++ (18372851, 2) :: (1, 1) :: repeat (1, 2) 58806192 ++ w) 1); closearith.
  }
  (* step 188: DIPGRIND 18 69 *)
  apply (hsteps_trans _ (HC [0] 0 3 2 (repeat (1, 2) 18 ++ (69, 2) :: (1, 1) :: repeat (1, 2) 158 ++ (143, 2) :: (1, 1) :: repeat (1, 2) 952 ++ (4838, 2) :: (1, 1) :: repeat (1, 2) 16082 ++ (1821, 2) :: (1, 1) :: repeat (1, 2) 308090 ++ (3396738, 2) :: (1, 1) :: repeat (1, 2) 7965811 ++ (18372851, 2) :: (1, 1) :: repeat (1, 2) 58806192 ++ w) 1)).
  {
    apply (DIPGRIND 18 69 [0] ((1, 1) :: repeat (1, 2) 158 ++ (143, 2) :: (1, 1) :: repeat (1, 2) 952 ++ (4838, 2) :: (1, 1) :: repeat (1, 2) 16082 ++ (1821, 2) :: (1, 1) :: repeat (1, 2) 308090 ++ (3396738, 2) :: (1, 1) :: repeat (1, 2) 7965811 ++ (18372851, 2) :: (1, 1) :: repeat (1, 2) 58806192 ++ w) 1); closearith.
  }
  (* step 189: P PX2B0 *)
  apply (hsteps_trans _ (HB [] 0 1 5 (repeat (1, 2) 19 ++ (69, 2) :: (1, 1) :: repeat (1, 2) 158 ++ (143, 2) :: (1, 1) :: repeat (1, 2) 952 ++ (4838, 2) :: (1, 1) :: repeat (1, 2) 16082 ++ (1821, 2) :: (1, 1) :: repeat (1, 2) 308090 ++ (3396738, 2) :: (1, 1) :: repeat (1, 2) 7965811 ++ (18372851, 2) :: (1, 1) :: repeat (1, 2) 58806192 ++ w) 1)).
  {
    exact (hsteps_step _ _ _ (hPX2B0 (repeat (1, 2) 18 ++ (69, 2) :: (1, 1) :: repeat (1, 2) 158 ++ (143, 2) :: (1, 1) :: repeat (1, 2) 952 ++ (4838, 2) :: (1, 1) :: repeat (1, 2) 16082 ++ (1821, 2) :: (1, 1) :: repeat (1, 2) 308090 ++ (3396738, 2) :: (1, 1) :: repeat (1, 2) 7965811 ++ (18372851, 2) :: (1, 1) :: repeat (1, 2) 58806192 ++ w) 1) (hsteps_refl _)).
  }
  (* step 190: M pop12 (19,) *)
  apply (hsteps_trans _ (HB [] 19 1 43 ((69, 2) :: (1, 1) :: repeat (1, 2) 158 ++ (143, 2) :: (1, 1) :: repeat (1, 2) 952 ++ (4838, 2) :: (1, 1) :: repeat (1, 2) 16082 ++ (1821, 2) :: (1, 1) :: repeat (1, 2) 308090 ++ (3396738, 2) :: (1, 1) :: repeat (1, 2) 7965811 ++ (18372851, 2) :: (1, 1) :: repeat (1, 2) 58806192 ++ w) 1)).
  {
    apply (pop12 19 [] 0 5 ((69, 2) :: (1, 1) :: repeat (1, 2) 158 ++ (143, 2) :: (1, 1) :: repeat (1, 2) 952 ++ (4838, 2) :: (1, 1) :: repeat (1, 2) 16082 ++ (1821, 2) :: (1, 1) :: repeat (1, 2) 308090 ++ (3396738, 2) :: (1, 1) :: repeat (1, 2) 7965811 ++ (18372851, 2) :: (1, 1) :: repeat (1, 2) 58806192 ++ w) 1); closearith.
  }
  (* step 191: sTUP *)
  apply (hsteps_trans _ (HC [] 19 42 2 ((67, 2) :: (1, 1) :: repeat (1, 2) 158 ++ (143, 2) :: (1, 1) :: repeat (1, 2) 952 ++ (4838, 2) :: (1, 1) :: repeat (1, 2) 16082 ++ (1821, 2) :: (1, 1) :: repeat (1, 2) 308090 ++ (3396738, 2) :: (1, 1) :: repeat (1, 2) 7965811 ++ (18372851, 2) :: (1, 1) :: repeat (1, 2) 58806192 ++ w) 1)).
  {
    replace ((67, 2) :: (1, 1) :: repeat (1, 2) 158 ++ (143, 2) :: (1, 1) :: repeat (1, 2) 952 ++ (4838, 2) :: (1, 1) :: repeat (1, 2) 16082 ++ (1821, 2) :: (1, 1) :: repeat (1, 2) 308090 ++ (3396738, 2) :: (1, 1) :: repeat (1, 2) 7965811 ++ (18372851, 2) :: (1, 1) :: repeat (1, 2) 58806192 ++ w) with ((69 - 2, 2) :: (1, 1) :: repeat (1, 2) 158 ++ (143, 2) :: (1, 1) :: repeat (1, 2) 952 ++ (4838, 2) :: (1, 1) :: repeat (1, 2) 16082 ++ (1821, 2) :: (1, 1) :: repeat (1, 2) 308090 ++ (3396738, 2) :: (1, 1) :: repeat (1, 2) 7965811 ++ (18372851, 2) :: (1, 1) :: repeat (1, 2) 58806192 ++ w) by sec_eq.
    apply (sTUP [] 19 43 69 2 ((1, 1) :: repeat (1, 2) 158 ++ (143, 2) :: (1, 1) :: repeat (1, 2) 952 ++ (4838, 2) :: (1, 1) :: repeat (1, 2) 16082 ++ (1821, 2) :: (1, 1) :: repeat (1, 2) 308090 ++ (3396738, 2) :: (1, 1) :: repeat (1, 2) 7965811 ++ (18372851, 2) :: (1, 1) :: repeat (1, 2) 58806192 ++ w) 1); closearith.
  }
  (* step 192: P PUSH *)
  apply (hsteps_trans _ (HC [] 18 1 2 ((40, 2) :: (67, 2) :: (1, 1) :: repeat (1, 2) 158 ++ (143, 2) :: (1, 1) :: repeat (1, 2) 952 ++ (4838, 2) :: (1, 1) :: repeat (1, 2) 16082 ++ (1821, 2) :: (1, 1) :: repeat (1, 2) 308090 ++ (3396738, 2) :: (1, 1) :: repeat (1, 2) 7965811 ++ (18372851, 2) :: (1, 1) :: repeat (1, 2) 58806192 ++ w) 1)).
  {
    replace ((40, 2) :: (67, 2) :: (1, 1) :: repeat (1, 2) 158 ++ (143, 2) :: (1, 1) :: repeat (1, 2) 952 ++ (4838, 2) :: (1, 1) :: repeat (1, 2) 16082 ++ (1821, 2) :: (1, 1) :: repeat (1, 2) 308090 ++ (3396738, 2) :: (1, 1) :: repeat (1, 2) 7965811 ++ (18372851, 2) :: (1, 1) :: repeat (1, 2) 58806192 ++ w) with ((42 - 2, 2) :: (67, 2) :: (1, 1) :: repeat (1, 2) 158 ++ (143, 2) :: (1, 1) :: repeat (1, 2) 952 ++ (4838, 2) :: (1, 1) :: repeat (1, 2) 16082 ++ (1821, 2) :: (1, 1) :: repeat (1, 2) 308090 ++ (3396738, 2) :: (1, 1) :: repeat (1, 2) 7965811 ++ (18372851, 2) :: (1, 1) :: repeat (1, 2) 58806192 ++ w) by sec_eq.
    apply (sPUSH [] 18 42 ((67, 2) :: (1, 1) :: repeat (1, 2) 158 ++ (143, 2) :: (1, 1) :: repeat (1, 2) 952 ++ (4838, 2) :: (1, 1) :: repeat (1, 2) 16082 ++ (1821, 2) :: (1, 1) :: repeat (1, 2) 308090 ++ (3396738, 2) :: (1, 1) :: repeat (1, 2) 7965811 ++ (18372851, 2) :: (1, 1) :: repeat (1, 2) 58806192 ++ w) 1); closearith.
  }
  (* step 193: P TDN *)
  apply (hsteps_trans _ (HB [] 18 1 4 ((40, 2) :: (67, 2) :: (1, 1) :: repeat (1, 2) 158 ++ (143, 2) :: (1, 1) :: repeat (1, 2) 952 ++ (4838, 2) :: (1, 1) :: repeat (1, 2) 16082 ++ (1821, 2) :: (1, 1) :: repeat (1, 2) 308090 ++ (3396738, 2) :: (1, 1) :: repeat (1, 2) 7965811 ++ (18372851, 2) :: (1, 1) :: repeat (1, 2) 58806192 ++ w) 1)).
  {
    apply (sTDN [] 18 ((40, 2) :: (67, 2) :: (1, 1) :: repeat (1, 2) 158 ++ (143, 2) :: (1, 1) :: repeat (1, 2) 952 ++ (4838, 2) :: (1, 1) :: repeat (1, 2) 16082 ++ (1821, 2) :: (1, 1) :: repeat (1, 2) 308090 ++ (3396738, 2) :: (1, 1) :: repeat (1, 2) 7965811 ++ (18372851, 2) :: (1, 1) :: repeat (1, 2) 58806192 ++ w) 1).
  }
  (* step 194: sTUP *)
  apply (hsteps_trans _ (HC [] 18 3 2 ((38, 2) :: (67, 2) :: (1, 1) :: repeat (1, 2) 158 ++ (143, 2) :: (1, 1) :: repeat (1, 2) 952 ++ (4838, 2) :: (1, 1) :: repeat (1, 2) 16082 ++ (1821, 2) :: (1, 1) :: repeat (1, 2) 308090 ++ (3396738, 2) :: (1, 1) :: repeat (1, 2) 7965811 ++ (18372851, 2) :: (1, 1) :: repeat (1, 2) 58806192 ++ w) 1)).
  {
    replace ((38, 2) :: (67, 2) :: (1, 1) :: repeat (1, 2) 158 ++ (143, 2) :: (1, 1) :: repeat (1, 2) 952 ++ (4838, 2) :: (1, 1) :: repeat (1, 2) 16082 ++ (1821, 2) :: (1, 1) :: repeat (1, 2) 308090 ++ (3396738, 2) :: (1, 1) :: repeat (1, 2) 7965811 ++ (18372851, 2) :: (1, 1) :: repeat (1, 2) 58806192 ++ w) with ((40 - 2, 2) :: (67, 2) :: (1, 1) :: repeat (1, 2) 158 ++ (143, 2) :: (1, 1) :: repeat (1, 2) 952 ++ (4838, 2) :: (1, 1) :: repeat (1, 2) 16082 ++ (1821, 2) :: (1, 1) :: repeat (1, 2) 308090 ++ (3396738, 2) :: (1, 1) :: repeat (1, 2) 7965811 ++ (18372851, 2) :: (1, 1) :: repeat (1, 2) 58806192 ++ w) by sec_eq.
    apply (sTUP [] 18 4 40 2 ((67, 2) :: (1, 1) :: repeat (1, 2) 158 ++ (143, 2) :: (1, 1) :: repeat (1, 2) 952 ++ (4838, 2) :: (1, 1) :: repeat (1, 2) 16082 ++ (1821, 2) :: (1, 1) :: repeat (1, 2) 308090 ++ (3396738, 2) :: (1, 1) :: repeat (1, 2) 7965811 ++ (18372851, 2) :: (1, 1) :: repeat (1, 2) 58806192 ++ w) 1); closearith.
  }
  (* step 195: DIPGRIND 18 2 *)
  apply (hsteps_trans _ (HC [] 0 3 2 (repeat (1, 2) 18 ++ (2, 2) :: (67, 2) :: (1, 1) :: repeat (1, 2) 158 ++ (143, 2) :: (1, 1) :: repeat (1, 2) 952 ++ (4838, 2) :: (1, 1) :: repeat (1, 2) 16082 ++ (1821, 2) :: (1, 1) :: repeat (1, 2) 308090 ++ (3396738, 2) :: (1, 1) :: repeat (1, 2) 7965811 ++ (18372851, 2) :: (1, 1) :: repeat (1, 2) 58806192 ++ w) 1)).
  {
    apply (DIPGRIND 18 2 [] ((67, 2) :: (1, 1) :: repeat (1, 2) 158 ++ (143, 2) :: (1, 1) :: repeat (1, 2) 952 ++ (4838, 2) :: (1, 1) :: repeat (1, 2) 16082 ++ (1821, 2) :: (1, 1) :: repeat (1, 2) 308090 ++ (3396738, 2) :: (1, 1) :: repeat (1, 2) 7965811 ++ (18372851, 2) :: (1, 1) :: repeat (1, 2) 58806192 ++ w) 1); closearith.
  }
  (* step 196: P PUSHX *)
  apply (hsteps_trans _ (HB [] 1 1 7 (repeat (1, 2) 18 ++ (2, 2) :: (67, 2) :: (1, 1) :: repeat (1, 2) 158 ++ (143, 2) :: (1, 1) :: repeat (1, 2) 952 ++ (4838, 2) :: (1, 1) :: repeat (1, 2) 16082 ++ (1821, 2) :: (1, 1) :: repeat (1, 2) 308090 ++ (3396738, 2) :: (1, 1) :: repeat (1, 2) 7965811 ++ (18372851, 2) :: (1, 1) :: repeat (1, 2) 58806192 ++ w) 1)).
  {
    exact (hsteps_step _ _ _ (hPUSHX (repeat (1, 2) 18 ++ (2, 2) :: (67, 2) :: (1, 1) :: repeat (1, 2) 158 ++ (143, 2) :: (1, 1) :: repeat (1, 2) 952 ++ (4838, 2) :: (1, 1) :: repeat (1, 2) 16082 ++ (1821, 2) :: (1, 1) :: repeat (1, 2) 308090 ++ (3396738, 2) :: (1, 1) :: repeat (1, 2) 7965811 ++ (18372851, 2) :: (1, 1) :: repeat (1, 2) 58806192 ++ w) 1) (hsteps_refl _)).
  }
  (* step 197: M pop12 (18,) *)
  apply (hsteps_trans _ (HB [] 19 1 43 ((2, 2) :: (67, 2) :: (1, 1) :: repeat (1, 2) 158 ++ (143, 2) :: (1, 1) :: repeat (1, 2) 952 ++ (4838, 2) :: (1, 1) :: repeat (1, 2) 16082 ++ (1821, 2) :: (1, 1) :: repeat (1, 2) 308090 ++ (3396738, 2) :: (1, 1) :: repeat (1, 2) 7965811 ++ (18372851, 2) :: (1, 1) :: repeat (1, 2) 58806192 ++ w) 1)).
  {
    apply (pop12 18 [] 1 7 ((2, 2) :: (67, 2) :: (1, 1) :: repeat (1, 2) 158 ++ (143, 2) :: (1, 1) :: repeat (1, 2) 952 ++ (4838, 2) :: (1, 1) :: repeat (1, 2) 16082 ++ (1821, 2) :: (1, 1) :: repeat (1, 2) 308090 ++ (3396738, 2) :: (1, 1) :: repeat (1, 2) 7965811 ++ (18372851, 2) :: (1, 1) :: repeat (1, 2) 58806192 ++ w) 1); closearith.
  }
  (* step 198: P TUP2_1 *)
  apply (hsteps_trans _ (HC [20] 43 1 2 ((65, 2) :: (1, 1) :: repeat (1, 2) 158 ++ (143, 2) :: (1, 1) :: repeat (1, 2) 952 ++ (4838, 2) :: (1, 1) :: repeat (1, 2) 16082 ++ (1821, 2) :: (1, 1) :: repeat (1, 2) 308090 ++ (3396738, 2) :: (1, 1) :: repeat (1, 2) 7965811 ++ (18372851, 2) :: (1, 1) :: repeat (1, 2) 58806192 ++ w) 1)).
  {
    replace ((65, 2) :: (1, 1) :: repeat (1, 2) 158 ++ (143, 2) :: (1, 1) :: repeat (1, 2) 952 ++ (4838, 2) :: (1, 1) :: repeat (1, 2) 16082 ++ (1821, 2) :: (1, 1) :: repeat (1, 2) 308090 ++ (3396738, 2) :: (1, 1) :: repeat (1, 2) 7965811 ++ (18372851, 2) :: (1, 1) :: repeat (1, 2) 58806192 ++ w) with ((67 - 2, 2) :: (1, 1) :: repeat (1, 2) 158 ++ (143, 2) :: (1, 1) :: repeat (1, 2) 952 ++ (4838, 2) :: (1, 1) :: repeat (1, 2) 16082 ++ (1821, 2) :: (1, 1) :: repeat (1, 2) 308090 ++ (3396738, 2) :: (1, 1) :: repeat (1, 2) 7965811 ++ (18372851, 2) :: (1, 1) :: repeat (1, 2) 58806192 ++ w) by sec_eq.
    apply (sTUP2_1 [] 19 42 67 ((1, 1) :: repeat (1, 2) 158 ++ (143, 2) :: (1, 1) :: repeat (1, 2) 952 ++ (4838, 2) :: (1, 1) :: repeat (1, 2) 16082 ++ (1821, 2) :: (1, 1) :: repeat (1, 2) 308090 ++ (3396738, 2) :: (1, 1) :: repeat (1, 2) 7965811 ++ (18372851, 2) :: (1, 1) :: repeat (1, 2) 58806192 ++ w) 1); closearith.
  }
  (* step 199: P TDN *)
  apply (hsteps_trans _ (HB [20] 43 1 4 ((65, 2) :: (1, 1) :: repeat (1, 2) 158 ++ (143, 2) :: (1, 1) :: repeat (1, 2) 952 ++ (4838, 2) :: (1, 1) :: repeat (1, 2) 16082 ++ (1821, 2) :: (1, 1) :: repeat (1, 2) 308090 ++ (3396738, 2) :: (1, 1) :: repeat (1, 2) 7965811 ++ (18372851, 2) :: (1, 1) :: repeat (1, 2) 58806192 ++ w) 1)).
  {
    apply (sTDN [20] 43 ((65, 2) :: (1, 1) :: repeat (1, 2) 158 ++ (143, 2) :: (1, 1) :: repeat (1, 2) 952 ++ (4838, 2) :: (1, 1) :: repeat (1, 2) 16082 ++ (1821, 2) :: (1, 1) :: repeat (1, 2) 308090 ++ (3396738, 2) :: (1, 1) :: repeat (1, 2) 7965811 ++ (18372851, 2) :: (1, 1) :: repeat (1, 2) 58806192 ++ w) 1).
  }
  (* step 200: sTUP *)
  apply (hsteps_trans _ (HC [20] 43 3 2 ((63, 2) :: (1, 1) :: repeat (1, 2) 158 ++ (143, 2) :: (1, 1) :: repeat (1, 2) 952 ++ (4838, 2) :: (1, 1) :: repeat (1, 2) 16082 ++ (1821, 2) :: (1, 1) :: repeat (1, 2) 308090 ++ (3396738, 2) :: (1, 1) :: repeat (1, 2) 7965811 ++ (18372851, 2) :: (1, 1) :: repeat (1, 2) 58806192 ++ w) 1)).
  {
    replace ((63, 2) :: (1, 1) :: repeat (1, 2) 158 ++ (143, 2) :: (1, 1) :: repeat (1, 2) 952 ++ (4838, 2) :: (1, 1) :: repeat (1, 2) 16082 ++ (1821, 2) :: (1, 1) :: repeat (1, 2) 308090 ++ (3396738, 2) :: (1, 1) :: repeat (1, 2) 7965811 ++ (18372851, 2) :: (1, 1) :: repeat (1, 2) 58806192 ++ w) with ((65 - 2, 2) :: (1, 1) :: repeat (1, 2) 158 ++ (143, 2) :: (1, 1) :: repeat (1, 2) 952 ++ (4838, 2) :: (1, 1) :: repeat (1, 2) 16082 ++ (1821, 2) :: (1, 1) :: repeat (1, 2) 308090 ++ (3396738, 2) :: (1, 1) :: repeat (1, 2) 7965811 ++ (18372851, 2) :: (1, 1) :: repeat (1, 2) 58806192 ++ w) by sec_eq.
    apply (sTUP [20] 43 4 65 2 ((1, 1) :: repeat (1, 2) 158 ++ (143, 2) :: (1, 1) :: repeat (1, 2) 952 ++ (4838, 2) :: (1, 1) :: repeat (1, 2) 16082 ++ (1821, 2) :: (1, 1) :: repeat (1, 2) 308090 ++ (3396738, 2) :: (1, 1) :: repeat (1, 2) 7965811 ++ (18372851, 2) :: (1, 1) :: repeat (1, 2) 58806192 ++ w) 1); closearith.
  }
  (* step 201: CLEANG_odd 30 *)
  apply (hsteps_trans _ (HB [20] 43 1 68 (repeat (1, 2) 1 ++ (1, 1) :: repeat (1, 2) 158 ++ (143, 2) :: (1, 1) :: repeat (1, 2) 952 ++ (4838, 2) :: (1, 1) :: repeat (1, 2) 16082 ++ (1821, 2) :: (1, 1) :: repeat (1, 2) 308090 ++ (3396738, 2) :: (1, 1) :: repeat (1, 2) 7965811 ++ (18372851, 2) :: (1, 1) :: repeat (1, 2) 58806192 ++ w) 1)).
  {
    replace (repeat (1, 2) 1 ++ (1, 1) :: repeat (1, 2) 158 ++ (143, 2) :: (1, 1) :: repeat (1, 2) 952 ++ (4838, 2) :: (1, 1) :: repeat (1, 2) 16082 ++ (1821, 2) :: (1, 1) :: repeat (1, 2) 308090 ++ (3396738, 2) :: (1, 1) :: repeat (1, 2) 7965811 ++ (18372851, 2) :: (1, 1) :: repeat (1, 2) 58806192 ++ w) with ((1, 2) :: (1, 1) :: repeat (1, 2) 158 ++ (143, 2) :: (1, 1) :: repeat (1, 2) 952 ++ (4838, 2) :: (1, 1) :: repeat (1, 2) 16082 ++ (1821, 2) :: (1, 1) :: repeat (1, 2) 308090 ++ (3396738, 2) :: (1, 1) :: repeat (1, 2) 7965811 ++ (18372851, 2) :: (1, 1) :: repeat (1, 2) 58806192 ++ w) by sec_eq.
    apply (CLEANG_odd 30 [20] 43 ((1, 1) :: repeat (1, 2) 158 ++ (143, 2) :: (1, 1) :: repeat (1, 2) 952 ++ (4838, 2) :: (1, 1) :: repeat (1, 2) 16082 ++ (1821, 2) :: (1, 1) :: repeat (1, 2) 308090 ++ (3396738, 2) :: (1, 1) :: repeat (1, 2) 7965811 ++ (18372851, 2) :: (1, 1) :: repeat (1, 2) 58806192 ++ w) 1); closearith.
  }
  (* step 202: M pop12 (1,) *)
  apply (hsteps_trans _ (HB [20] 44 1 70 ((1, 1) :: repeat (1, 2) 158 ++ (143, 2) :: (1, 1) :: repeat (1, 2) 952 ++ (4838, 2) :: (1, 1) :: repeat (1, 2) 16082 ++ (1821, 2) :: (1, 1) :: repeat (1, 2) 308090 ++ (3396738, 2) :: (1, 1) :: repeat (1, 2) 7965811 ++ (18372851, 2) :: (1, 1) :: repeat (1, 2) 58806192 ++ w) 1)).
  {
    apply (pop12 1 [20] 43 68 ((1, 1) :: repeat (1, 2) 158 ++ (143, 2) :: (1, 1) :: repeat (1, 2) 952 ++ (4838, 2) :: (1, 1) :: repeat (1, 2) 16082 ++ (1821, 2) :: (1, 1) :: repeat (1, 2) 308090 ++ (3396738, 2) :: (1, 1) :: repeat (1, 2) 7965811 ++ (18372851, 2) :: (1, 1) :: repeat (1, 2) 58806192 ++ w) 1); closearith.
  }
  (* step 203: P POP *)
  apply (hsteps_trans _ (HB [20] 45 1 71 (repeat (1, 2) 158 ++ (143, 2) :: (1, 1) :: repeat (1, 2) 952 ++ (4838, 2) :: (1, 1) :: repeat (1, 2) 16082 ++ (1821, 2) :: (1, 1) :: repeat (1, 2) 308090 ++ (3396738, 2) :: (1, 1) :: repeat (1, 2) 7965811 ++ (18372851, 2) :: (1, 1) :: repeat (1, 2) 58806192 ++ w) 1)).
  {
    apply (sPOP1 [20] 44 70 (repeat (1, 2) 158 ++ (143, 2) :: (1, 1) :: repeat (1, 2) 952 ++ (4838, 2) :: (1, 1) :: repeat (1, 2) 16082 ++ (1821, 2) :: (1, 1) :: repeat (1, 2) 308090 ++ (3396738, 2) :: (1, 1) :: repeat (1, 2) 7965811 ++ (18372851, 2) :: (1, 1) :: repeat (1, 2) 58806192 ++ w) 1); closearith.
  }
  (* step 204: M pop12 (158,) *)
  apply (hsteps_trans _ (HB [20] 203 1 387 ((143, 2) :: (1, 1) :: repeat (1, 2) 952 ++ (4838, 2) :: (1, 1) :: repeat (1, 2) 16082 ++ (1821, 2) :: (1, 1) :: repeat (1, 2) 308090 ++ (3396738, 2) :: (1, 1) :: repeat (1, 2) 7965811 ++ (18372851, 2) :: (1, 1) :: repeat (1, 2) 58806192 ++ w) 1)).
  {
    apply (pop12 158 [20] 45 71 ((143, 2) :: (1, 1) :: repeat (1, 2) 952 ++ (4838, 2) :: (1, 1) :: repeat (1, 2) 16082 ++ (1821, 2) :: (1, 1) :: repeat (1, 2) 308090 ++ (3396738, 2) :: (1, 1) :: repeat (1, 2) 7965811 ++ (18372851, 2) :: (1, 1) :: repeat (1, 2) 58806192 ++ w) 1); closearith.
  }
  (* step 205: sTUP *)
  apply (hsteps_trans _ (HC [20] 203 386 2 ((141, 2) :: (1, 1) :: repeat (1, 2) 952 ++ (4838, 2) :: (1, 1) :: repeat (1, 2) 16082 ++ (1821, 2) :: (1, 1) :: repeat (1, 2) 308090 ++ (3396738, 2) :: (1, 1) :: repeat (1, 2) 7965811 ++ (18372851, 2) :: (1, 1) :: repeat (1, 2) 58806192 ++ w) 1)).
  {
    replace ((141, 2) :: (1, 1) :: repeat (1, 2) 952 ++ (4838, 2) :: (1, 1) :: repeat (1, 2) 16082 ++ (1821, 2) :: (1, 1) :: repeat (1, 2) 308090 ++ (3396738, 2) :: (1, 1) :: repeat (1, 2) 7965811 ++ (18372851, 2) :: (1, 1) :: repeat (1, 2) 58806192 ++ w) with ((143 - 2, 2) :: (1, 1) :: repeat (1, 2) 952 ++ (4838, 2) :: (1, 1) :: repeat (1, 2) 16082 ++ (1821, 2) :: (1, 1) :: repeat (1, 2) 308090 ++ (3396738, 2) :: (1, 1) :: repeat (1, 2) 7965811 ++ (18372851, 2) :: (1, 1) :: repeat (1, 2) 58806192 ++ w) by sec_eq.
    apply (sTUP [20] 203 387 143 2 ((1, 1) :: repeat (1, 2) 952 ++ (4838, 2) :: (1, 1) :: repeat (1, 2) 16082 ++ (1821, 2) :: (1, 1) :: repeat (1, 2) 308090 ++ (3396738, 2) :: (1, 1) :: repeat (1, 2) 7965811 ++ (18372851, 2) :: (1, 1) :: repeat (1, 2) 58806192 ++ w) 1); closearith.
  }
  (* step 206: hGRIND_even 191 *)
  apply (hsteps_trans _ (HB [20] 202 1 386 ((2, 2) :: (141, 2) :: (1, 1) :: repeat (1, 2) 952 ++ (4838, 2) :: (1, 1) :: repeat (1, 2) 16082 ++ (1821, 2) :: (1, 1) :: repeat (1, 2) 308090 ++ (3396738, 2) :: (1, 1) :: repeat (1, 2) 7965811 ++ (18372851, 2) :: (1, 1) :: repeat (1, 2) 58806192 ++ w) 1)).
  {
    apply (hGRIND_even 191 [20] 202 ((141, 2) :: (1, 1) :: repeat (1, 2) 952 ++ (4838, 2) :: (1, 1) :: repeat (1, 2) 16082 ++ (1821, 2) :: (1, 1) :: repeat (1, 2) 308090 ++ (3396738, 2) :: (1, 1) :: repeat (1, 2) 7965811 ++ (18372851, 2) :: (1, 1) :: repeat (1, 2) 58806192 ++ w) 1); closearith.
  }
  (* step 207: P TUP2_1 *)
  apply (hsteps_trans _ (HC [203; 20] 386 1 2 ((139, 2) :: (1, 1) :: repeat (1, 2) 952 ++ (4838, 2) :: (1, 1) :: repeat (1, 2) 16082 ++ (1821, 2) :: (1, 1) :: repeat (1, 2) 308090 ++ (3396738, 2) :: (1, 1) :: repeat (1, 2) 7965811 ++ (18372851, 2) :: (1, 1) :: repeat (1, 2) 58806192 ++ w) 1)).
  {
    replace ((139, 2) :: (1, 1) :: repeat (1, 2) 952 ++ (4838, 2) :: (1, 1) :: repeat (1, 2) 16082 ++ (1821, 2) :: (1, 1) :: repeat (1, 2) 308090 ++ (3396738, 2) :: (1, 1) :: repeat (1, 2) 7965811 ++ (18372851, 2) :: (1, 1) :: repeat (1, 2) 58806192 ++ w) with ((141 - 2, 2) :: (1, 1) :: repeat (1, 2) 952 ++ (4838, 2) :: (1, 1) :: repeat (1, 2) 16082 ++ (1821, 2) :: (1, 1) :: repeat (1, 2) 308090 ++ (3396738, 2) :: (1, 1) :: repeat (1, 2) 7965811 ++ (18372851, 2) :: (1, 1) :: repeat (1, 2) 58806192 ++ w) by sec_eq.
    apply (sTUP2_1 [20] 202 385 141 ((1, 1) :: repeat (1, 2) 952 ++ (4838, 2) :: (1, 1) :: repeat (1, 2) 16082 ++ (1821, 2) :: (1, 1) :: repeat (1, 2) 308090 ++ (3396738, 2) :: (1, 1) :: repeat (1, 2) 7965811 ++ (18372851, 2) :: (1, 1) :: repeat (1, 2) 58806192 ++ w) 1); closearith.
  }
  (* step 208: P TDN *)
  apply (hsteps_trans _ (HB [203; 20] 386 1 4 ((139, 2) :: (1, 1) :: repeat (1, 2) 952 ++ (4838, 2) :: (1, 1) :: repeat (1, 2) 16082 ++ (1821, 2) :: (1, 1) :: repeat (1, 2) 308090 ++ (3396738, 2) :: (1, 1) :: repeat (1, 2) 7965811 ++ (18372851, 2) :: (1, 1) :: repeat (1, 2) 58806192 ++ w) 1)).
  {
    apply (sTDN [203; 20] 386 ((139, 2) :: (1, 1) :: repeat (1, 2) 952 ++ (4838, 2) :: (1, 1) :: repeat (1, 2) 16082 ++ (1821, 2) :: (1, 1) :: repeat (1, 2) 308090 ++ (3396738, 2) :: (1, 1) :: repeat (1, 2) 7965811 ++ (18372851, 2) :: (1, 1) :: repeat (1, 2) 58806192 ++ w) 1).
  }
  (* step 209: sTUP *)
  apply (hsteps_trans _ (HC [203; 20] 386 3 2 ((137, 2) :: (1, 1) :: repeat (1, 2) 952 ++ (4838, 2) :: (1, 1) :: repeat (1, 2) 16082 ++ (1821, 2) :: (1, 1) :: repeat (1, 2) 308090 ++ (3396738, 2) :: (1, 1) :: repeat (1, 2) 7965811 ++ (18372851, 2) :: (1, 1) :: repeat (1, 2) 58806192 ++ w) 1)).
  {
    replace ((137, 2) :: (1, 1) :: repeat (1, 2) 952 ++ (4838, 2) :: (1, 1) :: repeat (1, 2) 16082 ++ (1821, 2) :: (1, 1) :: repeat (1, 2) 308090 ++ (3396738, 2) :: (1, 1) :: repeat (1, 2) 7965811 ++ (18372851, 2) :: (1, 1) :: repeat (1, 2) 58806192 ++ w) with ((139 - 2, 2) :: (1, 1) :: repeat (1, 2) 952 ++ (4838, 2) :: (1, 1) :: repeat (1, 2) 16082 ++ (1821, 2) :: (1, 1) :: repeat (1, 2) 308090 ++ (3396738, 2) :: (1, 1) :: repeat (1, 2) 7965811 ++ (18372851, 2) :: (1, 1) :: repeat (1, 2) 58806192 ++ w) by sec_eq.
    apply (sTUP [203; 20] 386 4 139 2 ((1, 1) :: repeat (1, 2) 952 ++ (4838, 2) :: (1, 1) :: repeat (1, 2) 16082 ++ (1821, 2) :: (1, 1) :: repeat (1, 2) 308090 ++ (3396738, 2) :: (1, 1) :: repeat (1, 2) 7965811 ++ (18372851, 2) :: (1, 1) :: repeat (1, 2) 58806192 ++ w) 1); closearith.
  }
  (* step 210: CLEANG_odd 67 *)
  apply (hsteps_trans _ (HB [203; 20] 386 1 142 (repeat (1, 2) 1 ++ (1, 1) :: repeat (1, 2) 952 ++ (4838, 2) :: (1, 1) :: repeat (1, 2) 16082 ++ (1821, 2) :: (1, 1) :: repeat (1, 2) 308090 ++ (3396738, 2) :: (1, 1) :: repeat (1, 2) 7965811 ++ (18372851, 2) :: (1, 1) :: repeat (1, 2) 58806192 ++ w) 1)).
  {
    replace (repeat (1, 2) 1 ++ (1, 1) :: repeat (1, 2) 952 ++ (4838, 2) :: (1, 1) :: repeat (1, 2) 16082 ++ (1821, 2) :: (1, 1) :: repeat (1, 2) 308090 ++ (3396738, 2) :: (1, 1) :: repeat (1, 2) 7965811 ++ (18372851, 2) :: (1, 1) :: repeat (1, 2) 58806192 ++ w) with ((1, 2) :: (1, 1) :: repeat (1, 2) 952 ++ (4838, 2) :: (1, 1) :: repeat (1, 2) 16082 ++ (1821, 2) :: (1, 1) :: repeat (1, 2) 308090 ++ (3396738, 2) :: (1, 1) :: repeat (1, 2) 7965811 ++ (18372851, 2) :: (1, 1) :: repeat (1, 2) 58806192 ++ w) by sec_eq.
    apply (CLEANG_odd 67 [203; 20] 386 ((1, 1) :: repeat (1, 2) 952 ++ (4838, 2) :: (1, 1) :: repeat (1, 2) 16082 ++ (1821, 2) :: (1, 1) :: repeat (1, 2) 308090 ++ (3396738, 2) :: (1, 1) :: repeat (1, 2) 7965811 ++ (18372851, 2) :: (1, 1) :: repeat (1, 2) 58806192 ++ w) 1); closearith.
  }
  (* step 211: M pop12 (1,) *)
  apply (hsteps_trans _ (HB [203; 20] 387 1 144 ((1, 1) :: repeat (1, 2) 952 ++ (4838, 2) :: (1, 1) :: repeat (1, 2) 16082 ++ (1821, 2) :: (1, 1) :: repeat (1, 2) 308090 ++ (3396738, 2) :: (1, 1) :: repeat (1, 2) 7965811 ++ (18372851, 2) :: (1, 1) :: repeat (1, 2) 58806192 ++ w) 1)).
  {
    apply (pop12 1 [203; 20] 386 142 ((1, 1) :: repeat (1, 2) 952 ++ (4838, 2) :: (1, 1) :: repeat (1, 2) 16082 ++ (1821, 2) :: (1, 1) :: repeat (1, 2) 308090 ++ (3396738, 2) :: (1, 1) :: repeat (1, 2) 7965811 ++ (18372851, 2) :: (1, 1) :: repeat (1, 2) 58806192 ++ w) 1); closearith.
  }
  (* step 212: P POP *)
  apply (hsteps_trans _ (HB [203; 20] 388 1 145 (repeat (1, 2) 952 ++ (4838, 2) :: (1, 1) :: repeat (1, 2) 16082 ++ (1821, 2) :: (1, 1) :: repeat (1, 2) 308090 ++ (3396738, 2) :: (1, 1) :: repeat (1, 2) 7965811 ++ (18372851, 2) :: (1, 1) :: repeat (1, 2) 58806192 ++ w) 1)).
  {
    apply (sPOP1 [203; 20] 387 144 (repeat (1, 2) 952 ++ (4838, 2) :: (1, 1) :: repeat (1, 2) 16082 ++ (1821, 2) :: (1, 1) :: repeat (1, 2) 308090 ++ (3396738, 2) :: (1, 1) :: repeat (1, 2) 7965811 ++ (18372851, 2) :: (1, 1) :: repeat (1, 2) 58806192 ++ w) 1); closearith.
  }
  (* step 213: M pop12 (952,) *)
  apply (hsteps_trans _ (HB [203; 20] 1340 1 2049 ((4838, 2) :: (1, 1) :: repeat (1, 2) 16082 ++ (1821, 2) :: (1, 1) :: repeat (1, 2) 308090 ++ (3396738, 2) :: (1, 1) :: repeat (1, 2) 7965811 ++ (18372851, 2) :: (1, 1) :: repeat (1, 2) 58806192 ++ w) 1)).
  {
    apply (pop12 952 [203; 20] 388 145 ((4838, 2) :: (1, 1) :: repeat (1, 2) 16082 ++ (1821, 2) :: (1, 1) :: repeat (1, 2) 308090 ++ (3396738, 2) :: (1, 1) :: repeat (1, 2) 7965811 ++ (18372851, 2) :: (1, 1) :: repeat (1, 2) 58806192 ++ w) 1); closearith.
  }
  (* step 214: sTUP *)
  apply (hsteps_trans _ (HC [203; 20] 1340 2048 2 ((4836, 2) :: (1, 1) :: repeat (1, 2) 16082 ++ (1821, 2) :: (1, 1) :: repeat (1, 2) 308090 ++ (3396738, 2) :: (1, 1) :: repeat (1, 2) 7965811 ++ (18372851, 2) :: (1, 1) :: repeat (1, 2) 58806192 ++ w) 1)).
  {
    replace ((4836, 2) :: (1, 1) :: repeat (1, 2) 16082 ++ (1821, 2) :: (1, 1) :: repeat (1, 2) 308090 ++ (3396738, 2) :: (1, 1) :: repeat (1, 2) 7965811 ++ (18372851, 2) :: (1, 1) :: repeat (1, 2) 58806192 ++ w) with ((4838 - 2, 2) :: (1, 1) :: repeat (1, 2) 16082 ++ (1821, 2) :: (1, 1) :: repeat (1, 2) 308090 ++ (3396738, 2) :: (1, 1) :: repeat (1, 2) 7965811 ++ (18372851, 2) :: (1, 1) :: repeat (1, 2) 58806192 ++ w) by sec_eq.
    apply (sTUP [203; 20] 1340 2049 4838 2 ((1, 1) :: repeat (1, 2) 16082 ++ (1821, 2) :: (1, 1) :: repeat (1, 2) 308090 ++ (3396738, 2) :: (1, 1) :: repeat (1, 2) 7965811 ++ (18372851, 2) :: (1, 1) :: repeat (1, 2) 58806192 ++ w) 1); closearith.
  }
  (* step 215: hGRIND_even 1022 *)
  apply (hsteps_trans _ (HB [203; 20] 1339 1 2048 ((2, 2) :: (4836, 2) :: (1, 1) :: repeat (1, 2) 16082 ++ (1821, 2) :: (1, 1) :: repeat (1, 2) 308090 ++ (3396738, 2) :: (1, 1) :: repeat (1, 2) 7965811 ++ (18372851, 2) :: (1, 1) :: repeat (1, 2) 58806192 ++ w) 1)).
  {
    apply (hGRIND_even 1022 [203; 20] 1339 ((4836, 2) :: (1, 1) :: repeat (1, 2) 16082 ++ (1821, 2) :: (1, 1) :: repeat (1, 2) 308090 ++ (3396738, 2) :: (1, 1) :: repeat (1, 2) 7965811 ++ (18372851, 2) :: (1, 1) :: repeat (1, 2) 58806192 ++ w) 1); closearith.
  }
  (* step 216: P TUP2_1 *)
  apply (hsteps_trans _ (HC [1340; 203; 20] 2048 1 2 ((4834, 2) :: (1, 1) :: repeat (1, 2) 16082 ++ (1821, 2) :: (1, 1) :: repeat (1, 2) 308090 ++ (3396738, 2) :: (1, 1) :: repeat (1, 2) 7965811 ++ (18372851, 2) :: (1, 1) :: repeat (1, 2) 58806192 ++ w) 1)).
  {
    replace ((4834, 2) :: (1, 1) :: repeat (1, 2) 16082 ++ (1821, 2) :: (1, 1) :: repeat (1, 2) 308090 ++ (3396738, 2) :: (1, 1) :: repeat (1, 2) 7965811 ++ (18372851, 2) :: (1, 1) :: repeat (1, 2) 58806192 ++ w) with ((4836 - 2, 2) :: (1, 1) :: repeat (1, 2) 16082 ++ (1821, 2) :: (1, 1) :: repeat (1, 2) 308090 ++ (3396738, 2) :: (1, 1) :: repeat (1, 2) 7965811 ++ (18372851, 2) :: (1, 1) :: repeat (1, 2) 58806192 ++ w) by sec_eq.
    apply (sTUP2_1 [203; 20] 1339 2047 4836 ((1, 1) :: repeat (1, 2) 16082 ++ (1821, 2) :: (1, 1) :: repeat (1, 2) 308090 ++ (3396738, 2) :: (1, 1) :: repeat (1, 2) 7965811 ++ (18372851, 2) :: (1, 1) :: repeat (1, 2) 58806192 ++ w) 1); closearith.
  }
  (* step 217: P TDN *)
  apply (hsteps_trans _ (HB [1340; 203; 20] 2048 1 4 ((4834, 2) :: (1, 1) :: repeat (1, 2) 16082 ++ (1821, 2) :: (1, 1) :: repeat (1, 2) 308090 ++ (3396738, 2) :: (1, 1) :: repeat (1, 2) 7965811 ++ (18372851, 2) :: (1, 1) :: repeat (1, 2) 58806192 ++ w) 1)).
  {
    apply (sTDN [1340; 203; 20] 2048 ((4834, 2) :: (1, 1) :: repeat (1, 2) 16082 ++ (1821, 2) :: (1, 1) :: repeat (1, 2) 308090 ++ (3396738, 2) :: (1, 1) :: repeat (1, 2) 7965811 ++ (18372851, 2) :: (1, 1) :: repeat (1, 2) 58806192 ++ w) 1).
  }
  (* step 218: sTUP *)
  apply (hsteps_trans _ (HC [1340; 203; 20] 2048 3 2 ((4832, 2) :: (1, 1) :: repeat (1, 2) 16082 ++ (1821, 2) :: (1, 1) :: repeat (1, 2) 308090 ++ (3396738, 2) :: (1, 1) :: repeat (1, 2) 7965811 ++ (18372851, 2) :: (1, 1) :: repeat (1, 2) 58806192 ++ w) 1)).
  {
    replace ((4832, 2) :: (1, 1) :: repeat (1, 2) 16082 ++ (1821, 2) :: (1, 1) :: repeat (1, 2) 308090 ++ (3396738, 2) :: (1, 1) :: repeat (1, 2) 7965811 ++ (18372851, 2) :: (1, 1) :: repeat (1, 2) 58806192 ++ w) with ((4834 - 2, 2) :: (1, 1) :: repeat (1, 2) 16082 ++ (1821, 2) :: (1, 1) :: repeat (1, 2) 308090 ++ (3396738, 2) :: (1, 1) :: repeat (1, 2) 7965811 ++ (18372851, 2) :: (1, 1) :: repeat (1, 2) 58806192 ++ w) by sec_eq.
    apply (sTUP [1340; 203; 20] 2048 4 4834 2 ((1, 1) :: repeat (1, 2) 16082 ++ (1821, 2) :: (1, 1) :: repeat (1, 2) 308090 ++ (3396738, 2) :: (1, 1) :: repeat (1, 2) 7965811 ++ (18372851, 2) :: (1, 1) :: repeat (1, 2) 58806192 ++ w) 1); closearith.
  }
  (* step 219: DIPGRIND 2048 736 *)
  apply (hsteps_trans _ (HC [1340; 203; 20] 0 3 2 (repeat (1, 2) 2048 ++ (736, 2) :: (1, 1) :: repeat (1, 2) 16082 ++ (1821, 2) :: (1, 1) :: repeat (1, 2) 308090 ++ (3396738, 2) :: (1, 1) :: repeat (1, 2) 7965811 ++ (18372851, 2) :: (1, 1) :: repeat (1, 2) 58806192 ++ w) 1)).
  {
    apply (DIPGRIND 2048 736 [1340; 203; 20] ((1, 1) :: repeat (1, 2) 16082 ++ (1821, 2) :: (1, 1) :: repeat (1, 2) 308090 ++ (3396738, 2) :: (1, 1) :: repeat (1, 2) 7965811 ++ (18372851, 2) :: (1, 1) :: repeat (1, 2) 58806192 ++ w) 1); closearith.
  }
  (* step 220: P PX2A *)
  apply (hsteps_trans _ (HC [20] 202 1338 2 ((1, 1) :: repeat (1, 2) 2050 ++ (736, 2) :: (1, 1) :: repeat (1, 2) 16082 ++ (1821, 2) :: (1, 1) :: repeat (1, 2) 308090 ++ (3396738, 2) :: (1, 1) :: repeat (1, 2) 7965811 ++ (18372851, 2) :: (1, 1) :: repeat (1, 2) 58806192 ++ w) 1)).
  {
    exact (hsteps_step _ _ _ (hPX2A 1337 202 [20] (repeat (1, 2) 2048 ++ (736, 2) :: (1, 1) :: repeat (1, 2) 16082 ++ (1821, 2) :: (1, 1) :: repeat (1, 2) 308090 ++ (3396738, 2) :: (1, 1) :: repeat (1, 2) 7965811 ++ (18372851, 2) :: (1, 1) :: repeat (1, 2) 58806192 ++ w) 1) (hsteps_refl _)).
  }
  (* step 221: P PUSH *)
  apply (hsteps_trans _ (HC [20] 201 1 2 ((1336, 2) :: (1, 1) :: repeat (1, 2) 2050 ++ (736, 2) :: (1, 1) :: repeat (1, 2) 16082 ++ (1821, 2) :: (1, 1) :: repeat (1, 2) 308090 ++ (3396738, 2) :: (1, 1) :: repeat (1, 2) 7965811 ++ (18372851, 2) :: (1, 1) :: repeat (1, 2) 58806192 ++ w) 1)).
  {
    replace ((1336, 2) :: (1, 1) :: repeat (1, 2) 2050 ++ (736, 2) :: (1, 1) :: repeat (1, 2) 16082 ++ (1821, 2) :: (1, 1) :: repeat (1, 2) 308090 ++ (3396738, 2) :: (1, 1) :: repeat (1, 2) 7965811 ++ (18372851, 2) :: (1, 1) :: repeat (1, 2) 58806192 ++ w) with ((1338 - 2, 2) :: (1, 1) :: repeat (1, 2) 2050 ++ (736, 2) :: (1, 1) :: repeat (1, 2) 16082 ++ (1821, 2) :: (1, 1) :: repeat (1, 2) 308090 ++ (3396738, 2) :: (1, 1) :: repeat (1, 2) 7965811 ++ (18372851, 2) :: (1, 1) :: repeat (1, 2) 58806192 ++ w) by sec_eq.
    apply (sPUSH [20] 201 1338 ((1, 1) :: repeat (1, 2) 2050 ++ (736, 2) :: (1, 1) :: repeat (1, 2) 16082 ++ (1821, 2) :: (1, 1) :: repeat (1, 2) 308090 ++ (3396738, 2) :: (1, 1) :: repeat (1, 2) 7965811 ++ (18372851, 2) :: (1, 1) :: repeat (1, 2) 58806192 ++ w) 1); closearith.
  }
  (* step 222: P TDN *)
  apply (hsteps_trans _ (HB [20] 201 1 4 ((1336, 2) :: (1, 1) :: repeat (1, 2) 2050 ++ (736, 2) :: (1, 1) :: repeat (1, 2) 16082 ++ (1821, 2) :: (1, 1) :: repeat (1, 2) 308090 ++ (3396738, 2) :: (1, 1) :: repeat (1, 2) 7965811 ++ (18372851, 2) :: (1, 1) :: repeat (1, 2) 58806192 ++ w) 1)).
  {
    apply (sTDN [20] 201 ((1336, 2) :: (1, 1) :: repeat (1, 2) 2050 ++ (736, 2) :: (1, 1) :: repeat (1, 2) 16082 ++ (1821, 2) :: (1, 1) :: repeat (1, 2) 308090 ++ (3396738, 2) :: (1, 1) :: repeat (1, 2) 7965811 ++ (18372851, 2) :: (1, 1) :: repeat (1, 2) 58806192 ++ w) 1).
  }
  (* step 223: sTUP *)
  apply (hsteps_trans _ (HC [20] 201 3 2 ((1334, 2) :: (1, 1) :: repeat (1, 2) 2050 ++ (736, 2) :: (1, 1) :: repeat (1, 2) 16082 ++ (1821, 2) :: (1, 1) :: repeat (1, 2) 308090 ++ (3396738, 2) :: (1, 1) :: repeat (1, 2) 7965811 ++ (18372851, 2) :: (1, 1) :: repeat (1, 2) 58806192 ++ w) 1)).
  {
    replace ((1334, 2) :: (1, 1) :: repeat (1, 2) 2050 ++ (736, 2) :: (1, 1) :: repeat (1, 2) 16082 ++ (1821, 2) :: (1, 1) :: repeat (1, 2) 308090 ++ (3396738, 2) :: (1, 1) :: repeat (1, 2) 7965811 ++ (18372851, 2) :: (1, 1) :: repeat (1, 2) 58806192 ++ w) with ((1336 - 2, 2) :: (1, 1) :: repeat (1, 2) 2050 ++ (736, 2) :: (1, 1) :: repeat (1, 2) 16082 ++ (1821, 2) :: (1, 1) :: repeat (1, 2) 308090 ++ (3396738, 2) :: (1, 1) :: repeat (1, 2) 7965811 ++ (18372851, 2) :: (1, 1) :: repeat (1, 2) 58806192 ++ w) by sec_eq.
    apply (sTUP [20] 201 4 1336 2 ((1, 1) :: repeat (1, 2) 2050 ++ (736, 2) :: (1, 1) :: repeat (1, 2) 16082 ++ (1821, 2) :: (1, 1) :: repeat (1, 2) 308090 ++ (3396738, 2) :: (1, 1) :: repeat (1, 2) 7965811 ++ (18372851, 2) :: (1, 1) :: repeat (1, 2) 58806192 ++ w) 1); closearith.
  }
  (* step 224: DIPGRIND 201 932 *)
  apply (DIPGRIND 201 932 [20] ((1, 1) :: repeat (1, 2) 2050 ++ (736, 2) :: (1, 1) :: repeat (1, 2) 16082 ++ (1821, 2) :: (1, 1) :: repeat (1, 2) 308090 ++ (3396738, 2) :: (1, 1) :: repeat (1, 2) 7965811 ++ (18372851, 2) :: (1, 1) :: repeat (1, 2) 58806192 ++ w) 1); closearith.
Qed.

(* CASCADE60e: steps 225-280 of the CASCADE60 chain. *)
Lemma CASCADE60e : forall w,
  hsteps (HC [20] 0 3 2 (repeat (1, 2) 201 ++ (932, 2) :: (1, 1) :: repeat (1, 2) 2050 ++ (736, 2) :: (1, 1) :: repeat (1, 2) 16082 ++ (1821, 2) :: (1, 1) :: repeat (1, 2) 308090 ++ (3396738, 2) :: (1, 1) :: repeat (1, 2) 7965811 ++ (18372851, 2) :: (1, 1) :: repeat (1, 2) 58806192 ++ w) 1)
         (HB [5] 14 1 6 ((1, 1) :: repeat (1, 2) 34 ++ (108, 2) :: (1, 1) :: repeat (1, 2) 410 ++ (110, 2) :: (1, 1) :: repeat (1, 2) 2050 ++ (736, 2) :: (1, 1) :: repeat (1, 2) 16082 ++ (1821, 2) :: (1, 1) :: repeat (1, 2) 308090 ++ (3396738, 2) :: (1, 1) :: repeat (1, 2) 7965811 ++ (18372851, 2) :: (1, 1) :: repeat (1, 2) 58806192 ++ w) 1).
Proof.
  intro w.
  (* step 225: P PX2Bgen *)
  apply (hsteps_trans _ (HB [0] 3 1 2 ((16, 2) :: (1, 1) :: repeat (1, 2) 203 ++ (932, 2) :: (1, 1) :: repeat (1, 2) 2050 ++ (736, 2) :: (1, 1) :: repeat (1, 2) 16082 ++ (1821, 2) :: (1, 1) :: repeat (1, 2) 308090 ++ (3396738, 2) :: (1, 1) :: repeat (1, 2) 7965811 ++ (18372851, 2) :: (1, 1) :: repeat (1, 2) 58806192 ++ w) 1)).
  {
    exact (hsteps_step _ _ _ (hPX2Bgen 15 (repeat (1, 2) 201 ++ (932, 2) :: (1, 1) :: repeat (1, 2) 2050 ++ (736, 2) :: (1, 1) :: repeat (1, 2) 16082 ++ (1821, 2) :: (1, 1) :: repeat (1, 2) 308090 ++ (3396738, 2) :: (1, 1) :: repeat (1, 2) 7965811 ++ (18372851, 2) :: (1, 1) :: repeat (1, 2) 58806192 ++ w) 1) (hsteps_refl _)).
  }
  (* step 226: sTUP *)
  apply (hsteps_trans _ (HC [0] 3 1 2 ((14, 2) :: (1, 1) :: repeat (1, 2) 203 ++ (932, 2) :: (1, 1) :: repeat (1, 2) 2050 ++ (736, 2) :: (1, 1) :: repeat (1, 2) 16082 ++ (1821, 2) :: (1, 1) :: repeat (1, 2) 308090 ++ (3396738, 2) :: (1, 1) :: repeat (1, 2) 7965811 ++ (18372851, 2) :: (1, 1) :: repeat (1, 2) 58806192 ++ w) 1)).
  {
    replace ((14, 2) :: (1, 1) :: repeat (1, 2) 203 ++ (932, 2) :: (1, 1) :: repeat (1, 2) 2050 ++ (736, 2) :: (1, 1) :: repeat (1, 2) 16082 ++ (1821, 2) :: (1, 1) :: repeat (1, 2) 308090 ++ (3396738, 2) :: (1, 1) :: repeat (1, 2) 7965811 ++ (18372851, 2) :: (1, 1) :: repeat (1, 2) 58806192 ++ w) with ((16 - 2, 2) :: (1, 1) :: repeat (1, 2) 203 ++ (932, 2) :: (1, 1) :: repeat (1, 2) 2050 ++ (736, 2) :: (1, 1) :: repeat (1, 2) 16082 ++ (1821, 2) :: (1, 1) :: repeat (1, 2) 308090 ++ (3396738, 2) :: (1, 1) :: repeat (1, 2) 7965811 ++ (18372851, 2) :: (1, 1) :: repeat (1, 2) 58806192 ++ w) by sec_eq.
    apply (sTUP [0] 3 2 16 2 ((1, 1) :: repeat (1, 2) 203 ++ (932, 2) :: (1, 1) :: repeat (1, 2) 2050 ++ (736, 2) :: (1, 1) :: repeat (1, 2) 16082 ++ (1821, 2) :: (1, 1) :: repeat (1, 2) 308090 ++ (3396738, 2) :: (1, 1) :: repeat (1, 2) 7965811 ++ (18372851, 2) :: (1, 1) :: repeat (1, 2) 58806192 ++ w) 1); closearith.
  }
  (* step 227: P TDN *)
  apply (hsteps_trans _ (HB [0] 3 1 4 ((14, 2) :: (1, 1) :: repeat (1, 2) 203 ++ (932, 2) :: (1, 1) :: repeat (1, 2) 2050 ++ (736, 2) :: (1, 1) :: repeat (1, 2) 16082 ++ (1821, 2) :: (1, 1) :: repeat (1, 2) 308090 ++ (3396738, 2) :: (1, 1) :: repeat (1, 2) 7965811 ++ (18372851, 2) :: (1, 1) :: repeat (1, 2) 58806192 ++ w) 1)).
  {
    apply (sTDN [0] 3 ((14, 2) :: (1, 1) :: repeat (1, 2) 203 ++ (932, 2) :: (1, 1) :: repeat (1, 2) 2050 ++ (736, 2) :: (1, 1) :: repeat (1, 2) 16082 ++ (1821, 2) :: (1, 1) :: repeat (1, 2) 308090 ++ (3396738, 2) :: (1, 1) :: repeat (1, 2) 7965811 ++ (18372851, 2) :: (1, 1) :: repeat (1, 2) 58806192 ++ w) 1).
  }
  (* step 228: sTUP *)
  apply (hsteps_trans _ (HC [0] 3 3 2 ((12, 2) :: (1, 1) :: repeat (1, 2) 203 ++ (932, 2) :: (1, 1) :: repeat (1, 2) 2050 ++ (736, 2) :: (1, 1) :: repeat (1, 2) 16082 ++ (1821, 2) :: (1, 1) :: repeat (1, 2) 308090 ++ (3396738, 2) :: (1, 1) :: repeat (1, 2) 7965811 ++ (18372851, 2) :: (1, 1) :: repeat (1, 2) 58806192 ++ w) 1)).
  {
    replace ((12, 2) :: (1, 1) :: repeat (1, 2) 203 ++ (932, 2) :: (1, 1) :: repeat (1, 2) 2050 ++ (736, 2) :: (1, 1) :: repeat (1, 2) 16082 ++ (1821, 2) :: (1, 1) :: repeat (1, 2) 308090 ++ (3396738, 2) :: (1, 1) :: repeat (1, 2) 7965811 ++ (18372851, 2) :: (1, 1) :: repeat (1, 2) 58806192 ++ w) with ((14 - 2, 2) :: (1, 1) :: repeat (1, 2) 203 ++ (932, 2) :: (1, 1) :: repeat (1, 2) 2050 ++ (736, 2) :: (1, 1) :: repeat (1, 2) 16082 ++ (1821, 2) :: (1, 1) :: repeat (1, 2) 308090 ++ (3396738, 2) :: (1, 1) :: repeat (1, 2) 7965811 ++ (18372851, 2) :: (1, 1) :: repeat (1, 2) 58806192 ++ w) by sec_eq.
    apply (sTUP [0] 3 4 14 2 ((1, 1) :: repeat (1, 2) 203 ++ (932, 2) :: (1, 1) :: repeat (1, 2) 2050 ++ (736, 2) :: (1, 1) :: repeat (1, 2) 16082 ++ (1821, 2) :: (1, 1) :: repeat (1, 2) 308090 ++ (3396738, 2) :: (1, 1) :: repeat (1, 2) 7965811 ++ (18372851, 2) :: (1, 1) :: repeat (1, 2) 58806192 ++ w) 1); closearith.
  }
  (* step 229: DIPGRIND 3 6 *)
  apply (hsteps_trans _ (HC [0] 0 3 2 (repeat (1, 2) 3 ++ (6, 2) :: (1, 1) :: repeat (1, 2) 203 ++ (932, 2) :: (1, 1) :: repeat (1, 2) 2050 ++ (736, 2) :: (1, 1) :: repeat (1, 2) 16082 ++ (1821, 2) :: (1, 1) :: repeat (1, 2) 308090 ++ (3396738, 2) :: (1, 1) :: repeat (1, 2) 7965811 ++ (18372851, 2) :: (1, 1) :: repeat (1, 2) 58806192 ++ w) 1)).
  {
    apply (DIPGRIND 3 6 [0] ((1, 1) :: repeat (1, 2) 203 ++ (932, 2) :: (1, 1) :: repeat (1, 2) 2050 ++ (736, 2) :: (1, 1) :: repeat (1, 2) 16082 ++ (1821, 2) :: (1, 1) :: repeat (1, 2) 308090 ++ (3396738, 2) :: (1, 1) :: repeat (1, 2) 7965811 ++ (18372851, 2) :: (1, 1) :: repeat (1, 2) 58806192 ++ w) 1); closearith.
  }
  (* step 230: P PX2B0 *)
  apply (hsteps_trans _ (HB [] 0 1 5 (repeat (1, 2) 4 ++ (6, 2) :: (1, 1) :: repeat (1, 2) 203 ++ (932, 2) :: (1, 1) :: repeat (1, 2) 2050 ++ (736, 2) :: (1, 1) :: repeat (1, 2) 16082 ++ (1821, 2) :: (1, 1) :: repeat (1, 2) 308090 ++ (3396738, 2) :: (1, 1) :: repeat (1, 2) 7965811 ++ (18372851, 2) :: (1, 1) :: repeat (1, 2) 58806192 ++ w) 1)).
  {
    exact (hsteps_step _ _ _ (hPX2B0 (repeat (1, 2) 3 ++ (6, 2) :: (1, 1) :: repeat (1, 2) 203 ++ (932, 2) :: (1, 1) :: repeat (1, 2) 2050 ++ (736, 2) :: (1, 1) :: repeat (1, 2) 16082 ++ (1821, 2) :: (1, 1) :: repeat (1, 2) 308090 ++ (3396738, 2) :: (1, 1) :: repeat (1, 2) 7965811 ++ (18372851, 2) :: (1, 1) :: repeat (1, 2) 58806192 ++ w) 1) (hsteps_refl _)).
  }
  (* step 231: M pop12 (4,) *)
  apply (hsteps_trans _ (HB [] 4 1 13 ((6, 2) :: (1, 1) :: repeat (1, 2) 203 ++ (932, 2) :: (1, 1) :: repeat (1, 2) 2050 ++ (736, 2) :: (1, 1) :: repeat (1, 2) 16082 ++ (1821, 2) :: (1, 1) :: repeat (1, 2) 308090 ++ (3396738, 2) :: (1, 1) :: repeat (1, 2) 7965811 ++ (18372851, 2) :: (1, 1) :: repeat (1, 2) 58806192 ++ w) 1)).
  {
    apply (pop12 4 [] 0 5 ((6, 2) :: (1, 1) :: repeat (1, 2) 203 ++ (932, 2) :: (1, 1) :: repeat (1, 2) 2050 ++ (736, 2) :: (1, 1) :: repeat (1, 2) 16082 ++ (1821, 2) :: (1, 1) :: repeat (1, 2) 308090 ++ (3396738, 2) :: (1, 1) :: repeat (1, 2) 7965811 ++ (18372851, 2) :: (1, 1) :: repeat (1, 2) 58806192 ++ w) 1); closearith.
  }
  (* step 232: sTUP *)
  apply (hsteps_trans _ (HC [] 4 12 2 ((4, 2) :: (1, 1) :: repeat (1, 2) 203 ++ (932, 2) :: (1, 1) :: repeat (1, 2) 2050 ++ (736, 2) :: (1, 1) :: repeat (1, 2) 16082 ++ (1821, 2) :: (1, 1) :: repeat (1, 2) 308090 ++ (3396738, 2) :: (1, 1) :: repeat (1, 2) 7965811 ++ (18372851, 2) :: (1, 1) :: repeat (1, 2) 58806192 ++ w) 1)).
  {
    replace ((4, 2) :: (1, 1) :: repeat (1, 2) 203 ++ (932, 2) :: (1, 1) :: repeat (1, 2) 2050 ++ (736, 2) :: (1, 1) :: repeat (1, 2) 16082 ++ (1821, 2) :: (1, 1) :: repeat (1, 2) 308090 ++ (3396738, 2) :: (1, 1) :: repeat (1, 2) 7965811 ++ (18372851, 2) :: (1, 1) :: repeat (1, 2) 58806192 ++ w) with ((6 - 2, 2) :: (1, 1) :: repeat (1, 2) 203 ++ (932, 2) :: (1, 1) :: repeat (1, 2) 2050 ++ (736, 2) :: (1, 1) :: repeat (1, 2) 16082 ++ (1821, 2) :: (1, 1) :: repeat (1, 2) 308090 ++ (3396738, 2) :: (1, 1) :: repeat (1, 2) 7965811 ++ (18372851, 2) :: (1, 1) :: repeat (1, 2) 58806192 ++ w) by sec_eq.
    apply (sTUP [] 4 13 6 2 ((1, 1) :: repeat (1, 2) 203 ++ (932, 2) :: (1, 1) :: repeat (1, 2) 2050 ++ (736, 2) :: (1, 1) :: repeat (1, 2) 16082 ++ (1821, 2) :: (1, 1) :: repeat (1, 2) 308090 ++ (3396738, 2) :: (1, 1) :: repeat (1, 2) 7965811 ++ (18372851, 2) :: (1, 1) :: repeat (1, 2) 58806192 ++ w) 1); closearith.
  }
  (* step 233: P PUSH *)
  apply (hsteps_trans _ (HC [] 3 1 2 ((10, 2) :: (4, 2) :: (1, 1) :: repeat (1, 2) 203 ++ (932, 2) :: (1, 1) :: repeat (1, 2) 2050 ++ (736, 2) :: (1, 1) :: repeat (1, 2) 16082 ++ (1821, 2) :: (1, 1) :: repeat (1, 2) 308090 ++ (3396738, 2) :: (1, 1) :: repeat (1, 2) 7965811 ++ (18372851, 2) :: (1, 1) :: repeat (1, 2) 58806192 ++ w) 1)).
  {
    replace ((10, 2) :: (4, 2) :: (1, 1) :: repeat (1, 2) 203 ++ (932, 2) :: (1, 1) :: repeat (1, 2) 2050 ++ (736, 2) :: (1, 1) :: repeat (1, 2) 16082 ++ (1821, 2) :: (1, 1) :: repeat (1, 2) 308090 ++ (3396738, 2) :: (1, 1) :: repeat (1, 2) 7965811 ++ (18372851, 2) :: (1, 1) :: repeat (1, 2) 58806192 ++ w) with ((12 - 2, 2) :: (4, 2) :: (1, 1) :: repeat (1, 2) 203 ++ (932, 2) :: (1, 1) :: repeat (1, 2) 2050 ++ (736, 2) :: (1, 1) :: repeat (1, 2) 16082 ++ (1821, 2) :: (1, 1) :: repeat (1, 2) 308090 ++ (3396738, 2) :: (1, 1) :: repeat (1, 2) 7965811 ++ (18372851, 2) :: (1, 1) :: repeat (1, 2) 58806192 ++ w) by sec_eq.
    apply (sPUSH [] 3 12 ((4, 2) :: (1, 1) :: repeat (1, 2) 203 ++ (932, 2) :: (1, 1) :: repeat (1, 2) 2050 ++ (736, 2) :: (1, 1) :: repeat (1, 2) 16082 ++ (1821, 2) :: (1, 1) :: repeat (1, 2) 308090 ++ (3396738, 2) :: (1, 1) :: repeat (1, 2) 7965811 ++ (18372851, 2) :: (1, 1) :: repeat (1, 2) 58806192 ++ w) 1); closearith.
  }
  (* step 234: P TDN *)
  apply (hsteps_trans _ (HB [] 3 1 4 ((10, 2) :: (4, 2) :: (1, 1) :: repeat (1, 2) 203 ++ (932, 2) :: (1, 1) :: repeat (1, 2) 2050 ++ (736, 2) :: (1, 1) :: repeat (1, 2) 16082 ++ (1821, 2) :: (1, 1) :: repeat (1, 2) 308090 ++ (3396738, 2) :: (1, 1) :: repeat (1, 2) 7965811 ++ (18372851, 2) :: (1, 1) :: repeat (1, 2) 58806192 ++ w) 1)).
  {
    apply (sTDN [] 3 ((10, 2) :: (4, 2) :: (1, 1) :: repeat (1, 2) 203 ++ (932, 2) :: (1, 1) :: repeat (1, 2) 2050 ++ (736, 2) :: (1, 1) :: repeat (1, 2) 16082 ++ (1821, 2) :: (1, 1) :: repeat (1, 2) 308090 ++ (3396738, 2) :: (1, 1) :: repeat (1, 2) 7965811 ++ (18372851, 2) :: (1, 1) :: repeat (1, 2) 58806192 ++ w) 1).
  }
  (* step 235: sTUP *)
  apply (hsteps_trans _ (HC [] 3 3 2 ((8, 2) :: (4, 2) :: (1, 1) :: repeat (1, 2) 203 ++ (932, 2) :: (1, 1) :: repeat (1, 2) 2050 ++ (736, 2) :: (1, 1) :: repeat (1, 2) 16082 ++ (1821, 2) :: (1, 1) :: repeat (1, 2) 308090 ++ (3396738, 2) :: (1, 1) :: repeat (1, 2) 7965811 ++ (18372851, 2) :: (1, 1) :: repeat (1, 2) 58806192 ++ w) 1)).
  {
    replace ((8, 2) :: (4, 2) :: (1, 1) :: repeat (1, 2) 203 ++ (932, 2) :: (1, 1) :: repeat (1, 2) 2050 ++ (736, 2) :: (1, 1) :: repeat (1, 2) 16082 ++ (1821, 2) :: (1, 1) :: repeat (1, 2) 308090 ++ (3396738, 2) :: (1, 1) :: repeat (1, 2) 7965811 ++ (18372851, 2) :: (1, 1) :: repeat (1, 2) 58806192 ++ w) with ((10 - 2, 2) :: (4, 2) :: (1, 1) :: repeat (1, 2) 203 ++ (932, 2) :: (1, 1) :: repeat (1, 2) 2050 ++ (736, 2) :: (1, 1) :: repeat (1, 2) 16082 ++ (1821, 2) :: (1, 1) :: repeat (1, 2) 308090 ++ (3396738, 2) :: (1, 1) :: repeat (1, 2) 7965811 ++ (18372851, 2) :: (1, 1) :: repeat (1, 2) 58806192 ++ w) by sec_eq.
    apply (sTUP [] 3 4 10 2 ((4, 2) :: (1, 1) :: repeat (1, 2) 203 ++ (932, 2) :: (1, 1) :: repeat (1, 2) 2050 ++ (736, 2) :: (1, 1) :: repeat (1, 2) 16082 ++ (1821, 2) :: (1, 1) :: repeat (1, 2) 308090 ++ (3396738, 2) :: (1, 1) :: repeat (1, 2) 7965811 ++ (18372851, 2) :: (1, 1) :: repeat (1, 2) 58806192 ++ w) 1); closearith.
  }
  (* step 236: DIPGRIND 3 2 *)
  apply (hsteps_trans _ (HC [] 0 3 2 (repeat (1, 2) 3 ++ (2, 2) :: (4, 2) :: (1, 1) :: repeat (1, 2) 203 ++ (932, 2) :: (1, 1) :: repeat (1, 2) 2050 ++ (736, 2) :: (1, 1) :: repeat (1, 2) 16082 ++ (1821, 2) :: (1, 1) :: repeat (1, 2) 308090 ++ (3396738, 2) :: (1, 1) :: repeat (1, 2) 7965811 ++ (18372851, 2) :: (1, 1) :: repeat (1, 2) 58806192 ++ w) 1)).
  {
    apply (DIPGRIND 3 2 [] ((4, 2) :: (1, 1) :: repeat (1, 2) 203 ++ (932, 2) :: (1, 1) :: repeat (1, 2) 2050 ++ (736, 2) :: (1, 1) :: repeat (1, 2) 16082 ++ (1821, 2) :: (1, 1) :: repeat (1, 2) 308090 ++ (3396738, 2) :: (1, 1) :: repeat (1, 2) 7965811 ++ (18372851, 2) :: (1, 1) :: repeat (1, 2) 58806192 ++ w) 1); closearith.
  }
  (* step 237: P PUSHX *)
  apply (hsteps_trans _ (HB [] 1 1 7 (repeat (1, 2) 3 ++ (2, 2) :: (4, 2) :: (1, 1) :: repeat (1, 2) 203 ++ (932, 2) :: (1, 1) :: repeat (1, 2) 2050 ++ (736, 2) :: (1, 1) :: repeat (1, 2) 16082 ++ (1821, 2) :: (1, 1) :: repeat (1, 2) 308090 ++ (3396738, 2) :: (1, 1) :: repeat (1, 2) 7965811 ++ (18372851, 2) :: (1, 1) :: repeat (1, 2) 58806192 ++ w) 1)).
  {
    exact (hsteps_step _ _ _ (hPUSHX (repeat (1, 2) 3 ++ (2, 2) :: (4, 2) :: (1, 1) :: repeat (1, 2) 203 ++ (932, 2) :: (1, 1) :: repeat (1, 2) 2050 ++ (736, 2) :: (1, 1) :: repeat (1, 2) 16082 ++ (1821, 2) :: (1, 1) :: repeat (1, 2) 308090 ++ (3396738, 2) :: (1, 1) :: repeat (1, 2) 7965811 ++ (18372851, 2) :: (1, 1) :: repeat (1, 2) 58806192 ++ w) 1) (hsteps_refl _)).
  }
  (* step 238: M pop12 (3,) *)
  apply (hsteps_trans _ (HB [] 4 1 13 ((2, 2) :: (4, 2) :: (1, 1) :: repeat (1, 2) 203 ++ (932, 2) :: (1, 1) :: repeat (1, 2) 2050 ++ (736, 2) :: (1, 1) :: repeat (1, 2) 16082 ++ (1821, 2) :: (1, 1) :: repeat (1, 2) 308090 ++ (3396738, 2) :: (1, 1) :: repeat (1, 2) 7965811 ++ (18372851, 2) :: (1, 1) :: repeat (1, 2) 58806192 ++ w) 1)).
  {
    apply (pop12 3 [] 1 7 ((2, 2) :: (4, 2) :: (1, 1) :: repeat (1, 2) 203 ++ (932, 2) :: (1, 1) :: repeat (1, 2) 2050 ++ (736, 2) :: (1, 1) :: repeat (1, 2) 16082 ++ (1821, 2) :: (1, 1) :: repeat (1, 2) 308090 ++ (3396738, 2) :: (1, 1) :: repeat (1, 2) 7965811 ++ (18372851, 2) :: (1, 1) :: repeat (1, 2) 58806192 ++ w) 1); closearith.
  }
  (* step 239: P TUP2_1 *)
  apply (hsteps_trans _ (HC [5] 13 1 2 ((2, 2) :: (1, 1) :: repeat (1, 2) 203 ++ (932, 2) :: (1, 1) :: repeat (1, 2) 2050 ++ (736, 2) :: (1, 1) :: repeat (1, 2) 16082 ++ (1821, 2) :: (1, 1) :: repeat (1, 2) 308090 ++ (3396738, 2) :: (1, 1) :: repeat (1, 2) 7965811 ++ (18372851, 2) :: (1, 1) :: repeat (1, 2) 58806192 ++ w) 1)).
  {
    replace ((2, 2) :: (1, 1) :: repeat (1, 2) 203 ++ (932, 2) :: (1, 1) :: repeat (1, 2) 2050 ++ (736, 2) :: (1, 1) :: repeat (1, 2) 16082 ++ (1821, 2) :: (1, 1) :: repeat (1, 2) 308090 ++ (3396738, 2) :: (1, 1) :: repeat (1, 2) 7965811 ++ (18372851, 2) :: (1, 1) :: repeat (1, 2) 58806192 ++ w) with ((4 - 2, 2) :: (1, 1) :: repeat (1, 2) 203 ++ (932, 2) :: (1, 1) :: repeat (1, 2) 2050 ++ (736, 2) :: (1, 1) :: repeat (1, 2) 16082 ++ (1821, 2) :: (1, 1) :: repeat (1, 2) 308090 ++ (3396738, 2) :: (1, 1) :: repeat (1, 2) 7965811 ++ (18372851, 2) :: (1, 1) :: repeat (1, 2) 58806192 ++ w) by sec_eq.
    apply (sTUP2_1 [] 4 12 4 ((1, 1) :: repeat (1, 2) 203 ++ (932, 2) :: (1, 1) :: repeat (1, 2) 2050 ++ (736, 2) :: (1, 1) :: repeat (1, 2) 16082 ++ (1821, 2) :: (1, 1) :: repeat (1, 2) 308090 ++ (3396738, 2) :: (1, 1) :: repeat (1, 2) 7965811 ++ (18372851, 2) :: (1, 1) :: repeat (1, 2) 58806192 ++ w) 1); closearith.
  }
  (* step 240: P TDN *)
  apply (hsteps_trans _ (HB [5] 13 1 4 ((2, 2) :: (1, 1) :: repeat (1, 2) 203 ++ (932, 2) :: (1, 1) :: repeat (1, 2) 2050 ++ (736, 2) :: (1, 1) :: repeat (1, 2) 16082 ++ (1821, 2) :: (1, 1) :: repeat (1, 2) 308090 ++ (3396738, 2) :: (1, 1) :: repeat (1, 2) 7965811 ++ (18372851, 2) :: (1, 1) :: repeat (1, 2) 58806192 ++ w) 1)).
  {
    apply (sTDN [5] 13 ((2, 2) :: (1, 1) :: repeat (1, 2) 203 ++ (932, 2) :: (1, 1) :: repeat (1, 2) 2050 ++ (736, 2) :: (1, 1) :: repeat (1, 2) 16082 ++ (1821, 2) :: (1, 1) :: repeat (1, 2) 308090 ++ (3396738, 2) :: (1, 1) :: repeat (1, 2) 7965811 ++ (18372851, 2) :: (1, 1) :: repeat (1, 2) 58806192 ++ w) 1).
  }
  (* step 241: P TRANS2_1 *)
  apply (hsteps_trans _ (HB [14; 5] 5 1 3 (repeat (1, 2) 203 ++ (932, 2) :: (1, 1) :: repeat (1, 2) 2050 ++ (736, 2) :: (1, 1) :: repeat (1, 2) 16082 ++ (1821, 2) :: (1, 1) :: repeat (1, 2) 308090 ++ (3396738, 2) :: (1, 1) :: repeat (1, 2) 7965811 ++ (18372851, 2) :: (1, 1) :: repeat (1, 2) 58806192 ++ w) 1)).
  {
    apply (sTRANS2_1 [5] 13 3 1 (repeat (1, 2) 203 ++ (932, 2) :: (1, 1) :: repeat (1, 2) 2050 ++ (736, 2) :: (1, 1) :: repeat (1, 2) 16082 ++ (1821, 2) :: (1, 1) :: repeat (1, 2) 308090 ++ (3396738, 2) :: (1, 1) :: repeat (1, 2) 7965811 ++ (18372851, 2) :: (1, 1) :: repeat (1, 2) 58806192 ++ w) 1); closearith.
  }
  (* step 242: M pop12 (203,) *)
  apply (hsteps_trans _ (HB [14; 5] 208 1 409 ((932, 2) :: (1, 1) :: repeat (1, 2) 2050 ++ (736, 2) :: (1, 1) :: repeat (1, 2) 16082 ++ (1821, 2) :: (1, 1) :: repeat (1, 2) 308090 ++ (3396738, 2) :: (1, 1) :: repeat (1, 2) 7965811 ++ (18372851, 2) :: (1, 1) :: repeat (1, 2) 58806192 ++ w) 1)).
  {
    apply (pop12 203 [14; 5] 5 3 ((932, 2) :: (1, 1) :: repeat (1, 2) 2050 ++ (736, 2) :: (1, 1) :: repeat (1, 2) 16082 ++ (1821, 2) :: (1, 1) :: repeat (1, 2) 308090 ++ (3396738, 2) :: (1, 1) :: repeat (1, 2) 7965811 ++ (18372851, 2) :: (1, 1) :: repeat (1, 2) 58806192 ++ w) 1); closearith.
  }
  (* step 243: sTUP *)
  apply (hsteps_trans _ (HC [14; 5] 208 408 2 ((930, 2) :: (1, 1) :: repeat (1, 2) 2050 ++ (736, 2) :: (1, 1) :: repeat (1, 2) 16082 ++ (1821, 2) :: (1, 1) :: repeat (1, 2) 308090 ++ (3396738, 2) :: (1, 1) :: repeat (1, 2) 7965811 ++ (18372851, 2) :: (1, 1) :: repeat (1, 2) 58806192 ++ w) 1)).
  {
    replace ((930, 2) :: (1, 1) :: repeat (1, 2) 2050 ++ (736, 2) :: (1, 1) :: repeat (1, 2) 16082 ++ (1821, 2) :: (1, 1) :: repeat (1, 2) 308090 ++ (3396738, 2) :: (1, 1) :: repeat (1, 2) 7965811 ++ (18372851, 2) :: (1, 1) :: repeat (1, 2) 58806192 ++ w) with ((932 - 2, 2) :: (1, 1) :: repeat (1, 2) 2050 ++ (736, 2) :: (1, 1) :: repeat (1, 2) 16082 ++ (1821, 2) :: (1, 1) :: repeat (1, 2) 308090 ++ (3396738, 2) :: (1, 1) :: repeat (1, 2) 7965811 ++ (18372851, 2) :: (1, 1) :: repeat (1, 2) 58806192 ++ w) by sec_eq.
    apply (sTUP [14; 5] 208 409 932 2 ((1, 1) :: repeat (1, 2) 2050 ++ (736, 2) :: (1, 1) :: repeat (1, 2) 16082 ++ (1821, 2) :: (1, 1) :: repeat (1, 2) 308090 ++ (3396738, 2) :: (1, 1) :: repeat (1, 2) 7965811 ++ (18372851, 2) :: (1, 1) :: repeat (1, 2) 58806192 ++ w) 1); closearith.
  }
  (* step 244: hGRIND_even 202 *)
  apply (hsteps_trans _ (HB [14; 5] 207 1 408 ((2, 2) :: (930, 2) :: (1, 1) :: repeat (1, 2) 2050 ++ (736, 2) :: (1, 1) :: repeat (1, 2) 16082 ++ (1821, 2) :: (1, 1) :: repeat (1, 2) 308090 ++ (3396738, 2) :: (1, 1) :: repeat (1, 2) 7965811 ++ (18372851, 2) :: (1, 1) :: repeat (1, 2) 58806192 ++ w) 1)).
  {
    apply (hGRIND_even 202 [14; 5] 207 ((930, 2) :: (1, 1) :: repeat (1, 2) 2050 ++ (736, 2) :: (1, 1) :: repeat (1, 2) 16082 ++ (1821, 2) :: (1, 1) :: repeat (1, 2) 308090 ++ (3396738, 2) :: (1, 1) :: repeat (1, 2) 7965811 ++ (18372851, 2) :: (1, 1) :: repeat (1, 2) 58806192 ++ w) 1); closearith.
  }
  (* step 245: P TUP2_1 *)
  apply (hsteps_trans _ (HC [208; 14; 5] 408 1 2 ((928, 2) :: (1, 1) :: repeat (1, 2) 2050 ++ (736, 2) :: (1, 1) :: repeat (1, 2) 16082 ++ (1821, 2) :: (1, 1) :: repeat (1, 2) 308090 ++ (3396738, 2) :: (1, 1) :: repeat (1, 2) 7965811 ++ (18372851, 2) :: (1, 1) :: repeat (1, 2) 58806192 ++ w) 1)).
  {
    replace ((928, 2) :: (1, 1) :: repeat (1, 2) 2050 ++ (736, 2) :: (1, 1) :: repeat (1, 2) 16082 ++ (1821, 2) :: (1, 1) :: repeat (1, 2) 308090 ++ (3396738, 2) :: (1, 1) :: repeat (1, 2) 7965811 ++ (18372851, 2) :: (1, 1) :: repeat (1, 2) 58806192 ++ w) with ((930 - 2, 2) :: (1, 1) :: repeat (1, 2) 2050 ++ (736, 2) :: (1, 1) :: repeat (1, 2) 16082 ++ (1821, 2) :: (1, 1) :: repeat (1, 2) 308090 ++ (3396738, 2) :: (1, 1) :: repeat (1, 2) 7965811 ++ (18372851, 2) :: (1, 1) :: repeat (1, 2) 58806192 ++ w) by sec_eq.
    apply (sTUP2_1 [14; 5] 207 407 930 ((1, 1) :: repeat (1, 2) 2050 ++ (736, 2) :: (1, 1) :: repeat (1, 2) 16082 ++ (1821, 2) :: (1, 1) :: repeat (1, 2) 308090 ++ (3396738, 2) :: (1, 1) :: repeat (1, 2) 7965811 ++ (18372851, 2) :: (1, 1) :: repeat (1, 2) 58806192 ++ w) 1); closearith.
  }
  (* step 246: P TDN *)
  apply (hsteps_trans _ (HB [208; 14; 5] 408 1 4 ((928, 2) :: (1, 1) :: repeat (1, 2) 2050 ++ (736, 2) :: (1, 1) :: repeat (1, 2) 16082 ++ (1821, 2) :: (1, 1) :: repeat (1, 2) 308090 ++ (3396738, 2) :: (1, 1) :: repeat (1, 2) 7965811 ++ (18372851, 2) :: (1, 1) :: repeat (1, 2) 58806192 ++ w) 1)).
  {
    apply (sTDN [208; 14; 5] 408 ((928, 2) :: (1, 1) :: repeat (1, 2) 2050 ++ (736, 2) :: (1, 1) :: repeat (1, 2) 16082 ++ (1821, 2) :: (1, 1) :: repeat (1, 2) 308090 ++ (3396738, 2) :: (1, 1) :: repeat (1, 2) 7965811 ++ (18372851, 2) :: (1, 1) :: repeat (1, 2) 58806192 ++ w) 1).
  }
  (* step 247: sTUP *)
  apply (hsteps_trans _ (HC [208; 14; 5] 408 3 2 ((926, 2) :: (1, 1) :: repeat (1, 2) 2050 ++ (736, 2) :: (1, 1) :: repeat (1, 2) 16082 ++ (1821, 2) :: (1, 1) :: repeat (1, 2) 308090 ++ (3396738, 2) :: (1, 1) :: repeat (1, 2) 7965811 ++ (18372851, 2) :: (1, 1) :: repeat (1, 2) 58806192 ++ w) 1)).
  {
    replace ((926, 2) :: (1, 1) :: repeat (1, 2) 2050 ++ (736, 2) :: (1, 1) :: repeat (1, 2) 16082 ++ (1821, 2) :: (1, 1) :: repeat (1, 2) 308090 ++ (3396738, 2) :: (1, 1) :: repeat (1, 2) 7965811 ++ (18372851, 2) :: (1, 1) :: repeat (1, 2) 58806192 ++ w) with ((928 - 2, 2) :: (1, 1) :: repeat (1, 2) 2050 ++ (736, 2) :: (1, 1) :: repeat (1, 2) 16082 ++ (1821, 2) :: (1, 1) :: repeat (1, 2) 308090 ++ (3396738, 2) :: (1, 1) :: repeat (1, 2) 7965811 ++ (18372851, 2) :: (1, 1) :: repeat (1, 2) 58806192 ++ w) by sec_eq.
    apply (sTUP [208; 14; 5] 408 4 928 2 ((1, 1) :: repeat (1, 2) 2050 ++ (736, 2) :: (1, 1) :: repeat (1, 2) 16082 ++ (1821, 2) :: (1, 1) :: repeat (1, 2) 308090 ++ (3396738, 2) :: (1, 1) :: repeat (1, 2) 7965811 ++ (18372851, 2) :: (1, 1) :: repeat (1, 2) 58806192 ++ w) 1); closearith.
  }
  (* step 248: DIPGRIND 408 110 *)
  apply (hsteps_trans _ (HC [208; 14; 5] 0 3 2 (repeat (1, 2) 408 ++ (110, 2) :: (1, 1) :: repeat (1, 2) 2050 ++ (736, 2) :: (1, 1) :: repeat (1, 2) 16082 ++ (1821, 2) :: (1, 1) :: repeat (1, 2) 308090 ++ (3396738, 2) :: (1, 1) :: repeat (1, 2) 7965811 ++ (18372851, 2) :: (1, 1) :: repeat (1, 2) 58806192 ++ w) 1)).
  {
    apply (DIPGRIND 408 110 [208; 14; 5] ((1, 1) :: repeat (1, 2) 2050 ++ (736, 2) :: (1, 1) :: repeat (1, 2) 16082 ++ (1821, 2) :: (1, 1) :: repeat (1, 2) 308090 ++ (3396738, 2) :: (1, 1) :: repeat (1, 2) 7965811 ++ (18372851, 2) :: (1, 1) :: repeat (1, 2) 58806192 ++ w) 1); closearith.
  }
  (* step 249: P PX2A *)
  apply (hsteps_trans _ (HC [5] 13 206 2 ((1, 1) :: repeat (1, 2) 410 ++ (110, 2) :: (1, 1) :: repeat (1, 2) 2050 ++ (736, 2) :: (1, 1) :: repeat (1, 2) 16082 ++ (1821, 2) :: (1, 1) :: repeat (1, 2) 308090 ++ (3396738, 2) :: (1, 1) :: repeat (1, 2) 7965811 ++ (18372851, 2) :: (1, 1) :: repeat (1, 2) 58806192 ++ w) 1)).
  {
    exact (hsteps_step _ _ _ (hPX2A 205 13 [5] (repeat (1, 2) 408 ++ (110, 2) :: (1, 1) :: repeat (1, 2) 2050 ++ (736, 2) :: (1, 1) :: repeat (1, 2) 16082 ++ (1821, 2) :: (1, 1) :: repeat (1, 2) 308090 ++ (3396738, 2) :: (1, 1) :: repeat (1, 2) 7965811 ++ (18372851, 2) :: (1, 1) :: repeat (1, 2) 58806192 ++ w) 1) (hsteps_refl _)).
  }
  (* step 250: P PUSH *)
  apply (hsteps_trans _ (HC [5] 12 1 2 ((204, 2) :: (1, 1) :: repeat (1, 2) 410 ++ (110, 2) :: (1, 1) :: repeat (1, 2) 2050 ++ (736, 2) :: (1, 1) :: repeat (1, 2) 16082 ++ (1821, 2) :: (1, 1) :: repeat (1, 2) 308090 ++ (3396738, 2) :: (1, 1) :: repeat (1, 2) 7965811 ++ (18372851, 2) :: (1, 1) :: repeat (1, 2) 58806192 ++ w) 1)).
  {
    replace ((204, 2) :: (1, 1) :: repeat (1, 2) 410 ++ (110, 2) :: (1, 1) :: repeat (1, 2) 2050 ++ (736, 2) :: (1, 1) :: repeat (1, 2) 16082 ++ (1821, 2) :: (1, 1) :: repeat (1, 2) 308090 ++ (3396738, 2) :: (1, 1) :: repeat (1, 2) 7965811 ++ (18372851, 2) :: (1, 1) :: repeat (1, 2) 58806192 ++ w) with ((206 - 2, 2) :: (1, 1) :: repeat (1, 2) 410 ++ (110, 2) :: (1, 1) :: repeat (1, 2) 2050 ++ (736, 2) :: (1, 1) :: repeat (1, 2) 16082 ++ (1821, 2) :: (1, 1) :: repeat (1, 2) 308090 ++ (3396738, 2) :: (1, 1) :: repeat (1, 2) 7965811 ++ (18372851, 2) :: (1, 1) :: repeat (1, 2) 58806192 ++ w) by sec_eq.
    apply (sPUSH [5] 12 206 ((1, 1) :: repeat (1, 2) 410 ++ (110, 2) :: (1, 1) :: repeat (1, 2) 2050 ++ (736, 2) :: (1, 1) :: repeat (1, 2) 16082 ++ (1821, 2) :: (1, 1) :: repeat (1, 2) 308090 ++ (3396738, 2) :: (1, 1) :: repeat (1, 2) 7965811 ++ (18372851, 2) :: (1, 1) :: repeat (1, 2) 58806192 ++ w) 1); closearith.
  }
  (* step 251: P TDN *)
  apply (hsteps_trans _ (HB [5] 12 1 4 ((204, 2) :: (1, 1) :: repeat (1, 2) 410 ++ (110, 2) :: (1, 1) :: repeat (1, 2) 2050 ++ (736, 2) :: (1, 1) :: repeat (1, 2) 16082 ++ (1821, 2) :: (1, 1) :: repeat (1, 2) 308090 ++ (3396738, 2) :: (1, 1) :: repeat (1, 2) 7965811 ++ (18372851, 2) :: (1, 1) :: repeat (1, 2) 58806192 ++ w) 1)).
  {
    apply (sTDN [5] 12 ((204, 2) :: (1, 1) :: repeat (1, 2) 410 ++ (110, 2) :: (1, 1) :: repeat (1, 2) 2050 ++ (736, 2) :: (1, 1) :: repeat (1, 2) 16082 ++ (1821, 2) :: (1, 1) :: repeat (1, 2) 308090 ++ (3396738, 2) :: (1, 1) :: repeat (1, 2) 7965811 ++ (18372851, 2) :: (1, 1) :: repeat (1, 2) 58806192 ++ w) 1).
  }
  (* step 252: sTUP *)
  apply (hsteps_trans _ (HC [5] 12 3 2 ((202, 2) :: (1, 1) :: repeat (1, 2) 410 ++ (110, 2) :: (1, 1) :: repeat (1, 2) 2050 ++ (736, 2) :: (1, 1) :: repeat (1, 2) 16082 ++ (1821, 2) :: (1, 1) :: repeat (1, 2) 308090 ++ (3396738, 2) :: (1, 1) :: repeat (1, 2) 7965811 ++ (18372851, 2) :: (1, 1) :: repeat (1, 2) 58806192 ++ w) 1)).
  {
    replace ((202, 2) :: (1, 1) :: repeat (1, 2) 410 ++ (110, 2) :: (1, 1) :: repeat (1, 2) 2050 ++ (736, 2) :: (1, 1) :: repeat (1, 2) 16082 ++ (1821, 2) :: (1, 1) :: repeat (1, 2) 308090 ++ (3396738, 2) :: (1, 1) :: repeat (1, 2) 7965811 ++ (18372851, 2) :: (1, 1) :: repeat (1, 2) 58806192 ++ w) with ((204 - 2, 2) :: (1, 1) :: repeat (1, 2) 410 ++ (110, 2) :: (1, 1) :: repeat (1, 2) 2050 ++ (736, 2) :: (1, 1) :: repeat (1, 2) 16082 ++ (1821, 2) :: (1, 1) :: repeat (1, 2) 308090 ++ (3396738, 2) :: (1, 1) :: repeat (1, 2) 7965811 ++ (18372851, 2) :: (1, 1) :: repeat (1, 2) 58806192 ++ w) by sec_eq.
    apply (sTUP [5] 12 4 204 2 ((1, 1) :: repeat (1, 2) 410 ++ (110, 2) :: (1, 1) :: repeat (1, 2) 2050 ++ (736, 2) :: (1, 1) :: repeat (1, 2) 16082 ++ (1821, 2) :: (1, 1) :: repeat (1, 2) 308090 ++ (3396738, 2) :: (1, 1) :: repeat (1, 2) 7965811 ++ (18372851, 2) :: (1, 1) :: repeat (1, 2) 58806192 ++ w) 1); closearith.
  }
  (* step 253: DIPGRIND 12 178 *)
  apply (hsteps_trans _ (HC [5] 0 3 2 (repeat (1, 2) 12 ++ (178, 2) :: (1, 1) :: repeat (1, 2) 410 ++ (110, 2) :: (1, 1) :: repeat (1, 2) 2050 ++ (736, 2) :: (1, 1) :: repeat (1, 2) 16082 ++ (1821, 2) :: (1, 1) :: repeat (1, 2) 308090 ++ (3396738, 2) :: (1, 1) :: repeat (1, 2) 7965811 ++ (18372851, 2) :: (1, 1) :: repeat (1, 2) 58806192 ++ w) 1)).
  {
    apply (DIPGRIND 12 178 [5] ((1, 1) :: repeat (1, 2) 410 ++ (110, 2) :: (1, 1) :: repeat (1, 2) 2050 ++ (736, 2) :: (1, 1) :: repeat (1, 2) 16082 ++ (1821, 2) :: (1, 1) :: repeat (1, 2) 308090 ++ (3396738, 2) :: (1, 1) :: repeat (1, 2) 7965811 ++ (18372851, 2) :: (1, 1) :: repeat (1, 2) 58806192 ++ w) 1); closearith.
  }
  (* step 254: P PX2Bgen *)
  apply (hsteps_trans _ (HB [0] 3 1 2 (repeat (1, 2) 1 ++ (1, 1) :: repeat (1, 2) 14 ++ (178, 2) :: (1, 1) :: repeat (1, 2) 410 ++ (110, 2) :: (1, 1) :: repeat (1, 2) 2050 ++ (736, 2) :: (1, 1) :: repeat (1, 2) 16082 ++ (1821, 2) :: (1, 1) :: repeat (1, 2) 308090 ++ (3396738, 2) :: (1, 1) :: repeat (1, 2) 7965811 ++ (18372851, 2) :: (1, 1) :: repeat (1, 2) 58806192 ++ w) 1)).
  {
    exact (hsteps_step _ _ _ (hPX2Bgen 0 (repeat (1, 2) 12 ++ (178, 2) :: (1, 1) :: repeat (1, 2) 410 ++ (110, 2) :: (1, 1) :: repeat (1, 2) 2050 ++ (736, 2) :: (1, 1) :: repeat (1, 2) 16082 ++ (1821, 2) :: (1, 1) :: repeat (1, 2) 308090 ++ (3396738, 2) :: (1, 1) :: repeat (1, 2) 7965811 ++ (18372851, 2) :: (1, 1) :: repeat (1, 2) 58806192 ++ w) 1) (hsteps_refl _)).
  }
  (* step 255: M pop12 (1,) *)
  apply (hsteps_trans _ (HB [0] 4 1 4 ((1, 1) :: repeat (1, 2) 14 ++ (178, 2) :: (1, 1) :: repeat (1, 2) 410 ++ (110, 2) :: (1, 1) :: repeat (1, 2) 2050 ++ (736, 2) :: (1, 1) :: repeat (1, 2) 16082 ++ (1821, 2) :: (1, 1) :: repeat (1, 2) 308090 ++ (3396738, 2) :: (1, 1) :: repeat (1, 2) 7965811 ++ (18372851, 2) :: (1, 1) :: repeat (1, 2) 58806192 ++ w) 1)).
  {
    apply (pop12 1 [0] 3 2 ((1, 1) :: repeat (1, 2) 14 ++ (178, 2) :: (1, 1) :: repeat (1, 2) 410 ++ (110, 2) :: (1, 1) :: repeat (1, 2) 2050 ++ (736, 2) :: (1, 1) :: repeat (1, 2) 16082 ++ (1821, 2) :: (1, 1) :: repeat (1, 2) 308090 ++ (3396738, 2) :: (1, 1) :: repeat (1, 2) 7965811 ++ (18372851, 2) :: (1, 1) :: repeat (1, 2) 58806192 ++ w) 1); closearith.
  }
  (* step 256: P POP *)
  apply (hsteps_trans _ (HB [0] 5 1 5 (repeat (1, 2) 14 ++ (178, 2) :: (1, 1) :: repeat (1, 2) 410 ++ (110, 2) :: (1, 1) :: repeat (1, 2) 2050 ++ (736, 2) :: (1, 1) :: repeat (1, 2) 16082 ++ (1821, 2) :: (1, 1) :: repeat (1, 2) 308090 ++ (3396738, 2) :: (1, 1) :: repeat (1, 2) 7965811 ++ (18372851, 2) :: (1, 1) :: repeat (1, 2) 58806192 ++ w) 1)).
  {
    apply (sPOP1 [0] 4 4 (repeat (1, 2) 14 ++ (178, 2) :: (1, 1) :: repeat (1, 2) 410 ++ (110, 2) :: (1, 1) :: repeat (1, 2) 2050 ++ (736, 2) :: (1, 1) :: repeat (1, 2) 16082 ++ (1821, 2) :: (1, 1) :: repeat (1, 2) 308090 ++ (3396738, 2) :: (1, 1) :: repeat (1, 2) 7965811 ++ (18372851, 2) :: (1, 1) :: repeat (1, 2) 58806192 ++ w) 1); closearith.
  }
  (* step 257: M pop12 (14,) *)
  apply (hsteps_trans _ (HB [0] 19 1 33 ((178, 2) :: (1, 1) :: repeat (1, 2) 410 ++ (110, 2) :: (1, 1) :: repeat (1, 2) 2050 ++ (736, 2) :: (1, 1) :: repeat (1, 2) 16082 ++ (1821, 2) :: (1, 1) :: repeat (1, 2) 308090 ++ (3396738, 2) :: (1, 1) :: repeat (1, 2) 7965811 ++ (18372851, 2) :: (1, 1) :: repeat (1, 2) 58806192 ++ w) 1)).
  {
    apply (pop12 14 [0] 5 5 ((178, 2) :: (1, 1) :: repeat (1, 2) 410 ++ (110, 2) :: (1, 1) :: repeat (1, 2) 2050 ++ (736, 2) :: (1, 1) :: repeat (1, 2) 16082 ++ (1821, 2) :: (1, 1) :: repeat (1, 2) 308090 ++ (3396738, 2) :: (1, 1) :: repeat (1, 2) 7965811 ++ (18372851, 2) :: (1, 1) :: repeat (1, 2) 58806192 ++ w) 1); closearith.
  }
  (* step 258: sTUP *)
  apply (hsteps_trans _ (HC [0] 19 32 2 ((176, 2) :: (1, 1) :: repeat (1, 2) 410 ++ (110, 2) :: (1, 1) :: repeat (1, 2) 2050 ++ (736, 2) :: (1, 1) :: repeat (1, 2) 16082 ++ (1821, 2) :: (1, 1) :: repeat (1, 2) 308090 ++ (3396738, 2) :: (1, 1) :: repeat (1, 2) 7965811 ++ (18372851, 2) :: (1, 1) :: repeat (1, 2) 58806192 ++ w) 1)).
  {
    replace ((176, 2) :: (1, 1) :: repeat (1, 2) 410 ++ (110, 2) :: (1, 1) :: repeat (1, 2) 2050 ++ (736, 2) :: (1, 1) :: repeat (1, 2) 16082 ++ (1821, 2) :: (1, 1) :: repeat (1, 2) 308090 ++ (3396738, 2) :: (1, 1) :: repeat (1, 2) 7965811 ++ (18372851, 2) :: (1, 1) :: repeat (1, 2) 58806192 ++ w) with ((178 - 2, 2) :: (1, 1) :: repeat (1, 2) 410 ++ (110, 2) :: (1, 1) :: repeat (1, 2) 2050 ++ (736, 2) :: (1, 1) :: repeat (1, 2) 16082 ++ (1821, 2) :: (1, 1) :: repeat (1, 2) 308090 ++ (3396738, 2) :: (1, 1) :: repeat (1, 2) 7965811 ++ (18372851, 2) :: (1, 1) :: repeat (1, 2) 58806192 ++ w) by sec_eq.
    apply (sTUP [0] 19 33 178 2 ((1, 1) :: repeat (1, 2) 410 ++ (110, 2) :: (1, 1) :: repeat (1, 2) 2050 ++ (736, 2) :: (1, 1) :: repeat (1, 2) 16082 ++ (1821, 2) :: (1, 1) :: repeat (1, 2) 308090 ++ (3396738, 2) :: (1, 1) :: repeat (1, 2) 7965811 ++ (18372851, 2) :: (1, 1) :: repeat (1, 2) 58806192 ++ w) 1); closearith.
  }
  (* step 259: hGRIND_even 14 *)
  apply (hsteps_trans _ (HB [0] 18 1 32 ((2, 2) :: (176, 2) :: (1, 1) :: repeat (1, 2) 410 ++ (110, 2) :: (1, 1) :: repeat (1, 2) 2050 ++ (736, 2) :: (1, 1) :: repeat (1, 2) 16082 ++ (1821, 2) :: (1, 1) :: repeat (1, 2) 308090 ++ (3396738, 2) :: (1, 1) :: repeat (1, 2) 7965811 ++ (18372851, 2) :: (1, 1) :: repeat (1, 2) 58806192 ++ w) 1)).
  {
    apply (hGRIND_even 14 [0] 18 ((176, 2) :: (1, 1) :: repeat (1, 2) 410 ++ (110, 2) :: (1, 1) :: repeat (1, 2) 2050 ++ (736, 2) :: (1, 1) :: repeat (1, 2) 16082 ++ (1821, 2) :: (1, 1) :: repeat (1, 2) 308090 ++ (3396738, 2) :: (1, 1) :: repeat (1, 2) 7965811 ++ (18372851, 2) :: (1, 1) :: repeat (1, 2) 58806192 ++ w) 1); closearith.
  }
  (* step 260: P TUP2_1 *)
  apply (hsteps_trans _ (HC [19; 0] 32 1 2 ((174, 2) :: (1, 1) :: repeat (1, 2) 410 ++ (110, 2) :: (1, 1) :: repeat (1, 2) 2050 ++ (736, 2) :: (1, 1) :: repeat (1, 2) 16082 ++ (1821, 2) :: (1, 1) :: repeat (1, 2) 308090 ++ (3396738, 2) :: (1, 1) :: repeat (1, 2) 7965811 ++ (18372851, 2) :: (1, 1) :: repeat (1, 2) 58806192 ++ w) 1)).
  {
    replace ((174, 2) :: (1, 1) :: repeat (1, 2) 410 ++ (110, 2) :: (1, 1) :: repeat (1, 2) 2050 ++ (736, 2) :: (1, 1) :: repeat (1, 2) 16082 ++ (1821, 2) :: (1, 1) :: repeat (1, 2) 308090 ++ (3396738, 2) :: (1, 1) :: repeat (1, 2) 7965811 ++ (18372851, 2) :: (1, 1) :: repeat (1, 2) 58806192 ++ w) with ((176 - 2, 2) :: (1, 1) :: repeat (1, 2) 410 ++ (110, 2) :: (1, 1) :: repeat (1, 2) 2050 ++ (736, 2) :: (1, 1) :: repeat (1, 2) 16082 ++ (1821, 2) :: (1, 1) :: repeat (1, 2) 308090 ++ (3396738, 2) :: (1, 1) :: repeat (1, 2) 7965811 ++ (18372851, 2) :: (1, 1) :: repeat (1, 2) 58806192 ++ w) by sec_eq.
    apply (sTUP2_1 [0] 18 31 176 ((1, 1) :: repeat (1, 2) 410 ++ (110, 2) :: (1, 1) :: repeat (1, 2) 2050 ++ (736, 2) :: (1, 1) :: repeat (1, 2) 16082 ++ (1821, 2) :: (1, 1) :: repeat (1, 2) 308090 ++ (3396738, 2) :: (1, 1) :: repeat (1, 2) 7965811 ++ (18372851, 2) :: (1, 1) :: repeat (1, 2) 58806192 ++ w) 1); closearith.
  }
  (* step 261: P TDN *)
  apply (hsteps_trans _ (HB [19; 0] 32 1 4 ((174, 2) :: (1, 1) :: repeat (1, 2) 410 ++ (110, 2) :: (1, 1) :: repeat (1, 2) 2050 ++ (736, 2) :: (1, 1) :: repeat (1, 2) 16082 ++ (1821, 2) :: (1, 1) :: repeat (1, 2) 308090 ++ (3396738, 2) :: (1, 1) :: repeat (1, 2) 7965811 ++ (18372851, 2) :: (1, 1) :: repeat (1, 2) 58806192 ++ w) 1)).
  {
    apply (sTDN [19; 0] 32 ((174, 2) :: (1, 1) :: repeat (1, 2) 410 ++ (110, 2) :: (1, 1) :: repeat (1, 2) 2050 ++ (736, 2) :: (1, 1) :: repeat (1, 2) 16082 ++ (1821, 2) :: (1, 1) :: repeat (1, 2) 308090 ++ (3396738, 2) :: (1, 1) :: repeat (1, 2) 7965811 ++ (18372851, 2) :: (1, 1) :: repeat (1, 2) 58806192 ++ w) 1).
  }
  (* step 262: sTUP *)
  apply (hsteps_trans _ (HC [19; 0] 32 3 2 ((172, 2) :: (1, 1) :: repeat (1, 2) 410 ++ (110, 2) :: (1, 1) :: repeat (1, 2) 2050 ++ (736, 2) :: (1, 1) :: repeat (1, 2) 16082 ++ (1821, 2) :: (1, 1) :: repeat (1, 2) 308090 ++ (3396738, 2) :: (1, 1) :: repeat (1, 2) 7965811 ++ (18372851, 2) :: (1, 1) :: repeat (1, 2) 58806192 ++ w) 1)).
  {
    replace ((172, 2) :: (1, 1) :: repeat (1, 2) 410 ++ (110, 2) :: (1, 1) :: repeat (1, 2) 2050 ++ (736, 2) :: (1, 1) :: repeat (1, 2) 16082 ++ (1821, 2) :: (1, 1) :: repeat (1, 2) 308090 ++ (3396738, 2) :: (1, 1) :: repeat (1, 2) 7965811 ++ (18372851, 2) :: (1, 1) :: repeat (1, 2) 58806192 ++ w) with ((174 - 2, 2) :: (1, 1) :: repeat (1, 2) 410 ++ (110, 2) :: (1, 1) :: repeat (1, 2) 2050 ++ (736, 2) :: (1, 1) :: repeat (1, 2) 16082 ++ (1821, 2) :: (1, 1) :: repeat (1, 2) 308090 ++ (3396738, 2) :: (1, 1) :: repeat (1, 2) 7965811 ++ (18372851, 2) :: (1, 1) :: repeat (1, 2) 58806192 ++ w) by sec_eq.
    apply (sTUP [19; 0] 32 4 174 2 ((1, 1) :: repeat (1, 2) 410 ++ (110, 2) :: (1, 1) :: repeat (1, 2) 2050 ++ (736, 2) :: (1, 1) :: repeat (1, 2) 16082 ++ (1821, 2) :: (1, 1) :: repeat (1, 2) 308090 ++ (3396738, 2) :: (1, 1) :: repeat (1, 2) 7965811 ++ (18372851, 2) :: (1, 1) :: repeat (1, 2) 58806192 ++ w) 1); closearith.
  }
  (* step 263: DIPGRIND 32 108 *)
  apply (hsteps_trans _ (HC [19; 0] 0 3 2 (repeat (1, 2) 32 ++ (108, 2) :: (1, 1) :: repeat (1, 2) 410 ++ (110, 2) :: (1, 1) :: repeat (1, 2) 2050 ++ (736, 2) :: (1, 1) :: repeat (1, 2) 16082 ++ (1821, 2) :: (1, 1) :: repeat (1, 2) 308090 ++ (3396738, 2) :: (1, 1) :: repeat (1, 2) 7965811 ++ (18372851, 2) :: (1, 1) :: repeat (1, 2) 58806192 ++ w) 1)).
  {
    apply (DIPGRIND 32 108 [19; 0] ((1, 1) :: repeat (1, 2) 410 ++ (110, 2) :: (1, 1) :: repeat (1, 2) 2050 ++ (736, 2) :: (1, 1) :: repeat (1, 2) 16082 ++ (1821, 2) :: (1, 1) :: repeat (1, 2) 308090 ++ (3396738, 2) :: (1, 1) :: repeat (1, 2) 7965811 ++ (18372851, 2) :: (1, 1) :: repeat (1, 2) 58806192 ++ w) 1); closearith.
  }
  (* step 264: P PX2A0 *)
  apply (hsteps_trans _ (HB [0] 3 1 2 ((15, 2) :: (1, 1) :: repeat (1, 2) 34 ++ (108, 2) :: (1, 1) :: repeat (1, 2) 410 ++ (110, 2) :: (1, 1) :: repeat (1, 2) 2050 ++ (736, 2) :: (1, 1) :: repeat (1, 2) 16082 ++ (1821, 2) :: (1, 1) :: repeat (1, 2) 308090 ++ (3396738, 2) :: (1, 1) :: repeat (1, 2) 7965811 ++ (18372851, 2) :: (1, 1) :: repeat (1, 2) 58806192 ++ w) 1)).
  {
    exact (hsteps_step _ _ _ (hPX2A0 14 (repeat (1, 2) 32 ++ (108, 2) :: (1, 1) :: repeat (1, 2) 410 ++ (110, 2) :: (1, 1) :: repeat (1, 2) 2050 ++ (736, 2) :: (1, 1) :: repeat (1, 2) 16082 ++ (1821, 2) :: (1, 1) :: repeat (1, 2) 308090 ++ (3396738, 2) :: (1, 1) :: repeat (1, 2) 7965811 ++ (18372851, 2) :: (1, 1) :: repeat (1, 2) 58806192 ++ w) 1) (hsteps_refl _)).
  }
  (* step 265: sTUP *)
  apply (hsteps_trans _ (HC [0] 3 1 2 ((13, 2) :: (1, 1) :: repeat (1, 2) 34 ++ (108, 2) :: (1, 1) :: repeat (1, 2) 410 ++ (110, 2) :: (1, 1) :: repeat (1, 2) 2050 ++ (736, 2) :: (1, 1) :: repeat (1, 2) 16082 ++ (1821, 2) :: (1, 1) :: repeat (1, 2) 308090 ++ (3396738, 2) :: (1, 1) :: repeat (1, 2) 7965811 ++ (18372851, 2) :: (1, 1) :: repeat (1, 2) 58806192 ++ w) 1)).
  {
    replace ((13, 2) :: (1, 1) :: repeat (1, 2) 34 ++ (108, 2) :: (1, 1) :: repeat (1, 2) 410 ++ (110, 2) :: (1, 1) :: repeat (1, 2) 2050 ++ (736, 2) :: (1, 1) :: repeat (1, 2) 16082 ++ (1821, 2) :: (1, 1) :: repeat (1, 2) 308090 ++ (3396738, 2) :: (1, 1) :: repeat (1, 2) 7965811 ++ (18372851, 2) :: (1, 1) :: repeat (1, 2) 58806192 ++ w) with ((15 - 2, 2) :: (1, 1) :: repeat (1, 2) 34 ++ (108, 2) :: (1, 1) :: repeat (1, 2) 410 ++ (110, 2) :: (1, 1) :: repeat (1, 2) 2050 ++ (736, 2) :: (1, 1) :: repeat (1, 2) 16082 ++ (1821, 2) :: (1, 1) :: repeat (1, 2) 308090 ++ (3396738, 2) :: (1, 1) :: repeat (1, 2) 7965811 ++ (18372851, 2) :: (1, 1) :: repeat (1, 2) 58806192 ++ w) by sec_eq.
    apply (sTUP [0] 3 2 15 2 ((1, 1) :: repeat (1, 2) 34 ++ (108, 2) :: (1, 1) :: repeat (1, 2) 410 ++ (110, 2) :: (1, 1) :: repeat (1, 2) 2050 ++ (736, 2) :: (1, 1) :: repeat (1, 2) 16082 ++ (1821, 2) :: (1, 1) :: repeat (1, 2) 308090 ++ (3396738, 2) :: (1, 1) :: repeat (1, 2) 7965811 ++ (18372851, 2) :: (1, 1) :: repeat (1, 2) 58806192 ++ w) 1); closearith.
  }
  (* step 266: P TDN *)
  apply (hsteps_trans _ (HB [0] 3 1 4 ((13, 2) :: (1, 1) :: repeat (1, 2) 34 ++ (108, 2) :: (1, 1) :: repeat (1, 2) 410 ++ (110, 2) :: (1, 1) :: repeat (1, 2) 2050 ++ (736, 2) :: (1, 1) :: repeat (1, 2) 16082 ++ (1821, 2) :: (1, 1) :: repeat (1, 2) 308090 ++ (3396738, 2) :: (1, 1) :: repeat (1, 2) 7965811 ++ (18372851, 2) :: (1, 1) :: repeat (1, 2) 58806192 ++ w) 1)).
  {
    apply (sTDN [0] 3 ((13, 2) :: (1, 1) :: repeat (1, 2) 34 ++ (108, 2) :: (1, 1) :: repeat (1, 2) 410 ++ (110, 2) :: (1, 1) :: repeat (1, 2) 2050 ++ (736, 2) :: (1, 1) :: repeat (1, 2) 16082 ++ (1821, 2) :: (1, 1) :: repeat (1, 2) 308090 ++ (3396738, 2) :: (1, 1) :: repeat (1, 2) 7965811 ++ (18372851, 2) :: (1, 1) :: repeat (1, 2) 58806192 ++ w) 1).
  }
  (* step 267: sTUP *)
  apply (hsteps_trans _ (HC [0] 3 3 2 ((11, 2) :: (1, 1) :: repeat (1, 2) 34 ++ (108, 2) :: (1, 1) :: repeat (1, 2) 410 ++ (110, 2) :: (1, 1) :: repeat (1, 2) 2050 ++ (736, 2) :: (1, 1) :: repeat (1, 2) 16082 ++ (1821, 2) :: (1, 1) :: repeat (1, 2) 308090 ++ (3396738, 2) :: (1, 1) :: repeat (1, 2) 7965811 ++ (18372851, 2) :: (1, 1) :: repeat (1, 2) 58806192 ++ w) 1)).
  {
    replace ((11, 2) :: (1, 1) :: repeat (1, 2) 34 ++ (108, 2) :: (1, 1) :: repeat (1, 2) 410 ++ (110, 2) :: (1, 1) :: repeat (1, 2) 2050 ++ (736, 2) :: (1, 1) :: repeat (1, 2) 16082 ++ (1821, 2) :: (1, 1) :: repeat (1, 2) 308090 ++ (3396738, 2) :: (1, 1) :: repeat (1, 2) 7965811 ++ (18372851, 2) :: (1, 1) :: repeat (1, 2) 58806192 ++ w) with ((13 - 2, 2) :: (1, 1) :: repeat (1, 2) 34 ++ (108, 2) :: (1, 1) :: repeat (1, 2) 410 ++ (110, 2) :: (1, 1) :: repeat (1, 2) 2050 ++ (736, 2) :: (1, 1) :: repeat (1, 2) 16082 ++ (1821, 2) :: (1, 1) :: repeat (1, 2) 308090 ++ (3396738, 2) :: (1, 1) :: repeat (1, 2) 7965811 ++ (18372851, 2) :: (1, 1) :: repeat (1, 2) 58806192 ++ w) by sec_eq.
    apply (sTUP [0] 3 4 13 2 ((1, 1) :: repeat (1, 2) 34 ++ (108, 2) :: (1, 1) :: repeat (1, 2) 410 ++ (110, 2) :: (1, 1) :: repeat (1, 2) 2050 ++ (736, 2) :: (1, 1) :: repeat (1, 2) 16082 ++ (1821, 2) :: (1, 1) :: repeat (1, 2) 308090 ++ (3396738, 2) :: (1, 1) :: repeat (1, 2) 7965811 ++ (18372851, 2) :: (1, 1) :: repeat (1, 2) 58806192 ++ w) 1); closearith.
  }
  (* step 268: DIPGRIND 3 5 *)
  apply (hsteps_trans _ (HC [0] 0 3 2 (repeat (1, 2) 3 ++ (5, 2) :: (1, 1) :: repeat (1, 2) 34 ++ (108, 2) :: (1, 1) :: repeat (1, 2) 410 ++ (110, 2) :: (1, 1) :: repeat (1, 2) 2050 ++ (736, 2) :: (1, 1) :: repeat (1, 2) 16082 ++ (1821, 2) :: (1, 1) :: repeat (1, 2) 308090 ++ (3396738, 2) :: (1, 1) :: repeat (1, 2) 7965811 ++ (18372851, 2) :: (1, 1) :: repeat (1, 2) 58806192 ++ w) 1)).
  {
    apply (DIPGRIND 3 5 [0] ((1, 1) :: repeat (1, 2) 34 ++ (108, 2) :: (1, 1) :: repeat (1, 2) 410 ++ (110, 2) :: (1, 1) :: repeat (1, 2) 2050 ++ (736, 2) :: (1, 1) :: repeat (1, 2) 16082 ++ (1821, 2) :: (1, 1) :: repeat (1, 2) 308090 ++ (3396738, 2) :: (1, 1) :: repeat (1, 2) 7965811 ++ (18372851, 2) :: (1, 1) :: repeat (1, 2) 58806192 ++ w) 1); closearith.
  }
  (* step 269: P PX2B0 *)
  apply (hsteps_trans _ (HB [] 0 1 5 (repeat (1, 2) 4 ++ (5, 2) :: (1, 1) :: repeat (1, 2) 34 ++ (108, 2) :: (1, 1) :: repeat (1, 2) 410 ++ (110, 2) :: (1, 1) :: repeat (1, 2) 2050 ++ (736, 2) :: (1, 1) :: repeat (1, 2) 16082 ++ (1821, 2) :: (1, 1) :: repeat (1, 2) 308090 ++ (3396738, 2) :: (1, 1) :: repeat (1, 2) 7965811 ++ (18372851, 2) :: (1, 1) :: repeat (1, 2) 58806192 ++ w) 1)).
  {
    exact (hsteps_step _ _ _ (hPX2B0 (repeat (1, 2) 3 ++ (5, 2) :: (1, 1) :: repeat (1, 2) 34 ++ (108, 2) :: (1, 1) :: repeat (1, 2) 410 ++ (110, 2) :: (1, 1) :: repeat (1, 2) 2050 ++ (736, 2) :: (1, 1) :: repeat (1, 2) 16082 ++ (1821, 2) :: (1, 1) :: repeat (1, 2) 308090 ++ (3396738, 2) :: (1, 1) :: repeat (1, 2) 7965811 ++ (18372851, 2) :: (1, 1) :: repeat (1, 2) 58806192 ++ w) 1) (hsteps_refl _)).
  }
  (* step 270: M pop12 (4,) *)
  apply (hsteps_trans _ (HB [] 4 1 13 ((5, 2) :: (1, 1) :: repeat (1, 2) 34 ++ (108, 2) :: (1, 1) :: repeat (1, 2) 410 ++ (110, 2) :: (1, 1) :: repeat (1, 2) 2050 ++ (736, 2) :: (1, 1) :: repeat (1, 2) 16082 ++ (1821, 2) :: (1, 1) :: repeat (1, 2) 308090 ++ (3396738, 2) :: (1, 1) :: repeat (1, 2) 7965811 ++ (18372851, 2) :: (1, 1) :: repeat (1, 2) 58806192 ++ w) 1)).
  {
    apply (pop12 4 [] 0 5 ((5, 2) :: (1, 1) :: repeat (1, 2) 34 ++ (108, 2) :: (1, 1) :: repeat (1, 2) 410 ++ (110, 2) :: (1, 1) :: repeat (1, 2) 2050 ++ (736, 2) :: (1, 1) :: repeat (1, 2) 16082 ++ (1821, 2) :: (1, 1) :: repeat (1, 2) 308090 ++ (3396738, 2) :: (1, 1) :: repeat (1, 2) 7965811 ++ (18372851, 2) :: (1, 1) :: repeat (1, 2) 58806192 ++ w) 1); closearith.
  }
  (* step 271: sTUP *)
  apply (hsteps_trans _ (HC [] 4 12 2 ((3, 2) :: (1, 1) :: repeat (1, 2) 34 ++ (108, 2) :: (1, 1) :: repeat (1, 2) 410 ++ (110, 2) :: (1, 1) :: repeat (1, 2) 2050 ++ (736, 2) :: (1, 1) :: repeat (1, 2) 16082 ++ (1821, 2) :: (1, 1) :: repeat (1, 2) 308090 ++ (3396738, 2) :: (1, 1) :: repeat (1, 2) 7965811 ++ (18372851, 2) :: (1, 1) :: repeat (1, 2) 58806192 ++ w) 1)).
  {
    replace ((3, 2) :: (1, 1) :: repeat (1, 2) 34 ++ (108, 2) :: (1, 1) :: repeat (1, 2) 410 ++ (110, 2) :: (1, 1) :: repeat (1, 2) 2050 ++ (736, 2) :: (1, 1) :: repeat (1, 2) 16082 ++ (1821, 2) :: (1, 1) :: repeat (1, 2) 308090 ++ (3396738, 2) :: (1, 1) :: repeat (1, 2) 7965811 ++ (18372851, 2) :: (1, 1) :: repeat (1, 2) 58806192 ++ w) with ((5 - 2, 2) :: (1, 1) :: repeat (1, 2) 34 ++ (108, 2) :: (1, 1) :: repeat (1, 2) 410 ++ (110, 2) :: (1, 1) :: repeat (1, 2) 2050 ++ (736, 2) :: (1, 1) :: repeat (1, 2) 16082 ++ (1821, 2) :: (1, 1) :: repeat (1, 2) 308090 ++ (3396738, 2) :: (1, 1) :: repeat (1, 2) 7965811 ++ (18372851, 2) :: (1, 1) :: repeat (1, 2) 58806192 ++ w) by sec_eq.
    apply (sTUP [] 4 13 5 2 ((1, 1) :: repeat (1, 2) 34 ++ (108, 2) :: (1, 1) :: repeat (1, 2) 410 ++ (110, 2) :: (1, 1) :: repeat (1, 2) 2050 ++ (736, 2) :: (1, 1) :: repeat (1, 2) 16082 ++ (1821, 2) :: (1, 1) :: repeat (1, 2) 308090 ++ (3396738, 2) :: (1, 1) :: repeat (1, 2) 7965811 ++ (18372851, 2) :: (1, 1) :: repeat (1, 2) 58806192 ++ w) 1); closearith.
  }
  (* step 272: P PUSH *)
  apply (hsteps_trans _ (HC [] 3 1 2 ((10, 2) :: (3, 2) :: (1, 1) :: repeat (1, 2) 34 ++ (108, 2) :: (1, 1) :: repeat (1, 2) 410 ++ (110, 2) :: (1, 1) :: repeat (1, 2) 2050 ++ (736, 2) :: (1, 1) :: repeat (1, 2) 16082 ++ (1821, 2) :: (1, 1) :: repeat (1, 2) 308090 ++ (3396738, 2) :: (1, 1) :: repeat (1, 2) 7965811 ++ (18372851, 2) :: (1, 1) :: repeat (1, 2) 58806192 ++ w) 1)).
  {
    replace ((10, 2) :: (3, 2) :: (1, 1) :: repeat (1, 2) 34 ++ (108, 2) :: (1, 1) :: repeat (1, 2) 410 ++ (110, 2) :: (1, 1) :: repeat (1, 2) 2050 ++ (736, 2) :: (1, 1) :: repeat (1, 2) 16082 ++ (1821, 2) :: (1, 1) :: repeat (1, 2) 308090 ++ (3396738, 2) :: (1, 1) :: repeat (1, 2) 7965811 ++ (18372851, 2) :: (1, 1) :: repeat (1, 2) 58806192 ++ w) with ((12 - 2, 2) :: (3, 2) :: (1, 1) :: repeat (1, 2) 34 ++ (108, 2) :: (1, 1) :: repeat (1, 2) 410 ++ (110, 2) :: (1, 1) :: repeat (1, 2) 2050 ++ (736, 2) :: (1, 1) :: repeat (1, 2) 16082 ++ (1821, 2) :: (1, 1) :: repeat (1, 2) 308090 ++ (3396738, 2) :: (1, 1) :: repeat (1, 2) 7965811 ++ (18372851, 2) :: (1, 1) :: repeat (1, 2) 58806192 ++ w) by sec_eq.
    apply (sPUSH [] 3 12 ((3, 2) :: (1, 1) :: repeat (1, 2) 34 ++ (108, 2) :: (1, 1) :: repeat (1, 2) 410 ++ (110, 2) :: (1, 1) :: repeat (1, 2) 2050 ++ (736, 2) :: (1, 1) :: repeat (1, 2) 16082 ++ (1821, 2) :: (1, 1) :: repeat (1, 2) 308090 ++ (3396738, 2) :: (1, 1) :: repeat (1, 2) 7965811 ++ (18372851, 2) :: (1, 1) :: repeat (1, 2) 58806192 ++ w) 1); closearith.
  }
  (* step 273: P TDN *)
  apply (hsteps_trans _ (HB [] 3 1 4 ((10, 2) :: (3, 2) :: (1, 1) :: repeat (1, 2) 34 ++ (108, 2) :: (1, 1) :: repeat (1, 2) 410 ++ (110, 2) :: (1, 1) :: repeat (1, 2) 2050 ++ (736, 2) :: (1, 1) :: repeat (1, 2) 16082 ++ (1821, 2) :: (1, 1) :: repeat (1, 2) 308090 ++ (3396738, 2) :: (1, 1) :: repeat (1, 2) 7965811 ++ (18372851, 2) :: (1, 1) :: repeat (1, 2) 58806192 ++ w) 1)).
  {
    apply (sTDN [] 3 ((10, 2) :: (3, 2) :: (1, 1) :: repeat (1, 2) 34 ++ (108, 2) :: (1, 1) :: repeat (1, 2) 410 ++ (110, 2) :: (1, 1) :: repeat (1, 2) 2050 ++ (736, 2) :: (1, 1) :: repeat (1, 2) 16082 ++ (1821, 2) :: (1, 1) :: repeat (1, 2) 308090 ++ (3396738, 2) :: (1, 1) :: repeat (1, 2) 7965811 ++ (18372851, 2) :: (1, 1) :: repeat (1, 2) 58806192 ++ w) 1).
  }
  (* step 274: sTUP *)
  apply (hsteps_trans _ (HC [] 3 3 2 ((8, 2) :: (3, 2) :: (1, 1) :: repeat (1, 2) 34 ++ (108, 2) :: (1, 1) :: repeat (1, 2) 410 ++ (110, 2) :: (1, 1) :: repeat (1, 2) 2050 ++ (736, 2) :: (1, 1) :: repeat (1, 2) 16082 ++ (1821, 2) :: (1, 1) :: repeat (1, 2) 308090 ++ (3396738, 2) :: (1, 1) :: repeat (1, 2) 7965811 ++ (18372851, 2) :: (1, 1) :: repeat (1, 2) 58806192 ++ w) 1)).
  {
    replace ((8, 2) :: (3, 2) :: (1, 1) :: repeat (1, 2) 34 ++ (108, 2) :: (1, 1) :: repeat (1, 2) 410 ++ (110, 2) :: (1, 1) :: repeat (1, 2) 2050 ++ (736, 2) :: (1, 1) :: repeat (1, 2) 16082 ++ (1821, 2) :: (1, 1) :: repeat (1, 2) 308090 ++ (3396738, 2) :: (1, 1) :: repeat (1, 2) 7965811 ++ (18372851, 2) :: (1, 1) :: repeat (1, 2) 58806192 ++ w) with ((10 - 2, 2) :: (3, 2) :: (1, 1) :: repeat (1, 2) 34 ++ (108, 2) :: (1, 1) :: repeat (1, 2) 410 ++ (110, 2) :: (1, 1) :: repeat (1, 2) 2050 ++ (736, 2) :: (1, 1) :: repeat (1, 2) 16082 ++ (1821, 2) :: (1, 1) :: repeat (1, 2) 308090 ++ (3396738, 2) :: (1, 1) :: repeat (1, 2) 7965811 ++ (18372851, 2) :: (1, 1) :: repeat (1, 2) 58806192 ++ w) by sec_eq.
    apply (sTUP [] 3 4 10 2 ((3, 2) :: (1, 1) :: repeat (1, 2) 34 ++ (108, 2) :: (1, 1) :: repeat (1, 2) 410 ++ (110, 2) :: (1, 1) :: repeat (1, 2) 2050 ++ (736, 2) :: (1, 1) :: repeat (1, 2) 16082 ++ (1821, 2) :: (1, 1) :: repeat (1, 2) 308090 ++ (3396738, 2) :: (1, 1) :: repeat (1, 2) 7965811 ++ (18372851, 2) :: (1, 1) :: repeat (1, 2) 58806192 ++ w) 1); closearith.
  }
  (* step 275: DIPGRIND 3 2 *)
  apply (hsteps_trans _ (HC [] 0 3 2 (repeat (1, 2) 3 ++ (2, 2) :: (3, 2) :: (1, 1) :: repeat (1, 2) 34 ++ (108, 2) :: (1, 1) :: repeat (1, 2) 410 ++ (110, 2) :: (1, 1) :: repeat (1, 2) 2050 ++ (736, 2) :: (1, 1) :: repeat (1, 2) 16082 ++ (1821, 2) :: (1, 1) :: repeat (1, 2) 308090 ++ (3396738, 2) :: (1, 1) :: repeat (1, 2) 7965811 ++ (18372851, 2) :: (1, 1) :: repeat (1, 2) 58806192 ++ w) 1)).
  {
    apply (DIPGRIND 3 2 [] ((3, 2) :: (1, 1) :: repeat (1, 2) 34 ++ (108, 2) :: (1, 1) :: repeat (1, 2) 410 ++ (110, 2) :: (1, 1) :: repeat (1, 2) 2050 ++ (736, 2) :: (1, 1) :: repeat (1, 2) 16082 ++ (1821, 2) :: (1, 1) :: repeat (1, 2) 308090 ++ (3396738, 2) :: (1, 1) :: repeat (1, 2) 7965811 ++ (18372851, 2) :: (1, 1) :: repeat (1, 2) 58806192 ++ w) 1); closearith.
  }
  (* step 276: P PUSHX *)
  apply (hsteps_trans _ (HB [] 1 1 7 (repeat (1, 2) 3 ++ (2, 2) :: (3, 2) :: (1, 1) :: repeat (1, 2) 34 ++ (108, 2) :: (1, 1) :: repeat (1, 2) 410 ++ (110, 2) :: (1, 1) :: repeat (1, 2) 2050 ++ (736, 2) :: (1, 1) :: repeat (1, 2) 16082 ++ (1821, 2) :: (1, 1) :: repeat (1, 2) 308090 ++ (3396738, 2) :: (1, 1) :: repeat (1, 2) 7965811 ++ (18372851, 2) :: (1, 1) :: repeat (1, 2) 58806192 ++ w) 1)).
  {
    exact (hsteps_step _ _ _ (hPUSHX (repeat (1, 2) 3 ++ (2, 2) :: (3, 2) :: (1, 1) :: repeat (1, 2) 34 ++ (108, 2) :: (1, 1) :: repeat (1, 2) 410 ++ (110, 2) :: (1, 1) :: repeat (1, 2) 2050 ++ (736, 2) :: (1, 1) :: repeat (1, 2) 16082 ++ (1821, 2) :: (1, 1) :: repeat (1, 2) 308090 ++ (3396738, 2) :: (1, 1) :: repeat (1, 2) 7965811 ++ (18372851, 2) :: (1, 1) :: repeat (1, 2) 58806192 ++ w) 1) (hsteps_refl _)).
  }
  (* step 277: M pop12 (3,) *)
  apply (hsteps_trans _ (HB [] 4 1 13 ((2, 2) :: (3, 2) :: (1, 1) :: repeat (1, 2) 34 ++ (108, 2) :: (1, 1) :: repeat (1, 2) 410 ++ (110, 2) :: (1, 1) :: repeat (1, 2) 2050 ++ (736, 2) :: (1, 1) :: repeat (1, 2) 16082 ++ (1821, 2) :: (1, 1) :: repeat (1, 2) 308090 ++ (3396738, 2) :: (1, 1) :: repeat (1, 2) 7965811 ++ (18372851, 2) :: (1, 1) :: repeat (1, 2) 58806192 ++ w) 1)).
  {
    apply (pop12 3 [] 1 7 ((2, 2) :: (3, 2) :: (1, 1) :: repeat (1, 2) 34 ++ (108, 2) :: (1, 1) :: repeat (1, 2) 410 ++ (110, 2) :: (1, 1) :: repeat (1, 2) 2050 ++ (736, 2) :: (1, 1) :: repeat (1, 2) 16082 ++ (1821, 2) :: (1, 1) :: repeat (1, 2) 308090 ++ (3396738, 2) :: (1, 1) :: repeat (1, 2) 7965811 ++ (18372851, 2) :: (1, 1) :: repeat (1, 2) 58806192 ++ w) 1); closearith.
  }
  (* step 278: P TUP2_1 *)
  apply (hsteps_trans _ (HC [5] 13 1 2 (repeat (1, 2) 1 ++ (1, 1) :: repeat (1, 2) 34 ++ (108, 2) :: (1, 1) :: repeat (1, 2) 410 ++ (110, 2) :: (1, 1) :: repeat (1, 2) 2050 ++ (736, 2) :: (1, 1) :: repeat (1, 2) 16082 ++ (1821, 2) :: (1, 1) :: repeat (1, 2) 308090 ++ (3396738, 2) :: (1, 1) :: repeat (1, 2) 7965811 ++ (18372851, 2) :: (1, 1) :: repeat (1, 2) 58806192 ++ w) 1)).
  {
    replace (repeat (1, 2) 1 ++ (1, 1) :: repeat (1, 2) 34 ++ (108, 2) :: (1, 1) :: repeat (1, 2) 410 ++ (110, 2) :: (1, 1) :: repeat (1, 2) 2050 ++ (736, 2) :: (1, 1) :: repeat (1, 2) 16082 ++ (1821, 2) :: (1, 1) :: repeat (1, 2) 308090 ++ (3396738, 2) :: (1, 1) :: repeat (1, 2) 7965811 ++ (18372851, 2) :: (1, 1) :: repeat (1, 2) 58806192 ++ w) with ((3 - 2, 2) :: (1, 1) :: repeat (1, 2) 34 ++ (108, 2) :: (1, 1) :: repeat (1, 2) 410 ++ (110, 2) :: (1, 1) :: repeat (1, 2) 2050 ++ (736, 2) :: (1, 1) :: repeat (1, 2) 16082 ++ (1821, 2) :: (1, 1) :: repeat (1, 2) 308090 ++ (3396738, 2) :: (1, 1) :: repeat (1, 2) 7965811 ++ (18372851, 2) :: (1, 1) :: repeat (1, 2) 58806192 ++ w) by sec_eq.
    apply (sTUP2_1 [] 4 12 3 ((1, 1) :: repeat (1, 2) 34 ++ (108, 2) :: (1, 1) :: repeat (1, 2) 410 ++ (110, 2) :: (1, 1) :: repeat (1, 2) 2050 ++ (736, 2) :: (1, 1) :: repeat (1, 2) 16082 ++ (1821, 2) :: (1, 1) :: repeat (1, 2) 308090 ++ (3396738, 2) :: (1, 1) :: repeat (1, 2) 7965811 ++ (18372851, 2) :: (1, 1) :: repeat (1, 2) 58806192 ++ w) 1); closearith.
  }
  (* step 279: P TDN *)
  apply (hsteps_trans _ (HB [5] 13 1 4 (repeat (1, 2) 1 ++ (1, 1) :: repeat (1, 2) 34 ++ (108, 2) :: (1, 1) :: repeat (1, 2) 410 ++ (110, 2) :: (1, 1) :: repeat (1, 2) 2050 ++ (736, 2) :: (1, 1) :: repeat (1, 2) 16082 ++ (1821, 2) :: (1, 1) :: repeat (1, 2) 308090 ++ (3396738, 2) :: (1, 1) :: repeat (1, 2) 7965811 ++ (18372851, 2) :: (1, 1) :: repeat (1, 2) 58806192 ++ w) 1)).
  {
    apply (sTDN [5] 13 (repeat (1, 2) 1 ++ (1, 1) :: repeat (1, 2) 34 ++ (108, 2) :: (1, 1) :: repeat (1, 2) 410 ++ (110, 2) :: (1, 1) :: repeat (1, 2) 2050 ++ (736, 2) :: (1, 1) :: repeat (1, 2) 16082 ++ (1821, 2) :: (1, 1) :: repeat (1, 2) 308090 ++ (3396738, 2) :: (1, 1) :: repeat (1, 2) 7965811 ++ (18372851, 2) :: (1, 1) :: repeat (1, 2) 58806192 ++ w) 1).
  }
  (* step 280: M pop12 (1,) *)
  apply (pop12 1 [5] 13 4 ((1, 1) :: repeat (1, 2) 34 ++ (108, 2) :: (1, 1) :: repeat (1, 2) 410 ++ (110, 2) :: (1, 1) :: repeat (1, 2) 2050 ++ (736, 2) :: (1, 1) :: repeat (1, 2) 16082 ++ (1821, 2) :: (1, 1) :: repeat (1, 2) 308090 ++ (3396738, 2) :: (1, 1) :: repeat (1, 2) 7965811 ++ (18372851, 2) :: (1, 1) :: repeat (1, 2) 58806192 ++ w) 1); closearith.
Qed.

