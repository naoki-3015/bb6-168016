(* ================================================================= *)
(* Phase 56: the TENTH descent -- TAIL2_END10 modulo TAIL2_END11.    *)
(*                                                                   *)
(* The TOP9 state (frame [297773; 149464; 1260; 147; 20; 0],        *)
(* counter 2020419, shuttle 2851851) at pair (2j, 2), j >= 2851854,  *)
(* beta >= 2, is mechanised by the same fixed-parse pattern as       *)
(* Phases 47-55:                                                       *)
(*                                                                   *)
(*  1. FRONT (identical in shape to the Phase 55 front): TUP,        *)
(*     hGRIND_even 1425923, TUP2_1, TDN, TUP                         *)
(*     -> GRIND10 = HC [2020419; 297773; 149464; 1260; 147; 20; 0]   *)
(*        2851850 3 2 ((2j - 6, 2) :: tail(beta)).                   *)
(*  2. DIPGRIND (2851850, r10), r10 = 2j - 5703706 >= 2:             *)
(*     -> HC [2020419; 297773; ...] 0 3 2 (spine 2851850 ++ W),      *)
(*        W = ((r10, 2) :: (1, 1) :: (1, 2)^(beta-1)).               *)
(*  3. CASCADE56: a FIXED parse of 799 lemma steps from the spine    *)
(*     to TOP10 (hsim56 Part 1: the 805-waypoint chain verified at   *)
(*     six (j, beta) points; the cascade's label sequence and        *)
(*     abstracted targets are beta-uniform, checked at beta = 2, 3;  *)
(*     Part 1b: the cascade is stated for an arbitrary tail w).      *)
(*     Unlike CASCADE55 (17 steps), the tenth descent unwinds the    *)
(*     whole stack: it descends the TOP9 frame through PX2A /        *)
(*     DIPGRIND levels (297771, 1424871), (1258, 146942),             *)
(*     (18, 105), reaches the bottom frame [] and regrows an         *)
(*     ELEVEN-block frame through 81 DIPGRIND levels in all:         *)
(*                                                                   *)
(*       TOP10 = HB [652285; 206767; 138671; 25145; 13306; 4643;     *)
(*                   2871; 335; 235; 42; 19]                         *)
(*               4042956 1 5937475 W.                                *)
(*                                                                   *)
(*  4. TOP10 closings by r10' = 2 * j10, j10 = j - 2851853:          *)
(*    r10' = 2:       TRANS2_1 + CASCADE_POPFIN, A = 5937475 + beta, *)
(*                    frame [4042957; 652285; 206767; ...];          *)
(*    r10' = 4:       TUP + hGRIND_even 2968735 + TRANS2_2           *)
(*                    + CASCADE_POPFIN, A = beta + 2;                *)
(*    r10' = 6:       TUP + hGRIND_even 2968735 + TUP2_1 + TDN       *)
(*                    + TRANS2_1 + CASCADE_POPFIN, A = beta + 4;     *)
(*    8 <= r10' <= 11874954 (band 10): TUP + hGRIND_even 2968735     *)
(*      + TUP2_1 + TDN + TUP onto GRIND11 = HC [4042956; 652285;     *)
(*      ...] 5937474 3 2 ((r10' - 6, 2) :: tail), whose pair grinds  *)
(*      CLEANLY by CLEANG_even (floor (r10' - 8)/2 + 1 <= 5937474,   *)
(*      exactly r10' <= 11874954), then TRANS2_1 + CASCADE_POPFIN,   *)
(*      A = r10' + beta - 2, frame [5937475; 4042956; 652285; ...].  *)
(*      (The band counter is again the shuttle moved into the        *)
(*      counter slot by TUP2_1: 5937474, not 4042956.)               *)
(*                                                                   *)
(*  For r10' >= 11874956 (j10 >= 5937478, i.e. TOP9-parameter        *)
(*  j >= 8789331) the pair (r10' - 6, 2) at counter 5937474 exceeds  *)
(*  the CLEANG_even floor and the rounds take the DIPDESC            *)
(*  boundary an ELEVENTH time (hsim56 Part 3: the GRIND11 state and  *)
(*  the DIPGRIND (5937474, r10' - 11874954) landing both occur at    *)
(*  j = 8789331, 8789332, 9000000).  The eleventh descent is         *)
(*  expected to be a NEW cascade with different constants, so no     *)
(*  cycle induction in the current vocabulary closes it; what        *)
(*  remains is the strictly smaller core                             *)
(*                                                                   *)
(*    TAIL2_END11: the totality of the ONE pair (2j, 2) at the ONE   *)
(*    fixed TOP10 state HB [652285; 206767; 138671; 25145; 13306;    *)
(*    4643; 2871; 335; 235; 42; 19] 4042956 1 5937475, for           *)
(*    j >= 5937478 (r10' = 2j >= 11874956), beta >= 2.               *)
(*                                                                   *)
(*  The core's range shrank from [2851854, infty) to [8789331,       *)
(*  infty) in TOP9 parameters; the band width roughly doubled        *)
(*  again (2851854 -> 8789330).  Via TAIL2_END10_of56 +               *)
(*  TAIL2_END9_of55 + ESC_ERA_LAW_55 the ESC instances at every      *)
(*  even R >= 1278 now rest on TAIL2_END11 alone                     *)
(*  (ESC_ERA_LAW_56 below; Loop.v Part 4q).                          *)
(* ================================================================= *)

Require Import List Bool Arith Lia ZArith.
Import ListNotations.
Require Import TM Sections Mirror TokenPass Recoord Era Esc Dev
               Grind Grind2 Grind3 Grind4 Grind5 Grind6 Grind7 Grind8
               Grind9 Grind10 Grind11 Grind12 Grind13 Grind14 Grind15
               Grind16 Grind17 Grind18 Grind19 Grind20 Grind21 Grind22
               Grind23.

(* Section equality: componentwise, arithmetic leaves by lia.      *)
Ltac sec_eq :=
  repeat (first [ solve [reflexivity] | solve [lia] | f_equal ]).

(* Closed-numeral arithmetic: literals >= 7426 are parsed as       *)
(* Nat.of_num_uint atoms, which lia cannot relate to variables;    *)
(* for purely closed <= goals the boolean check decides them.      *)
Ltac closearith :=
  first [ lia | apply Nat.leb_le; reflexivity ].

(* Numeral identities for the steps below, factored into           *)
(* standalone lemmas proved by Nat.eqb_eq + vm_compute             *)
(* (VM-cast conversion) and used via plain `rewrite` -- the         *)
(* Phase 52-55 pattern, applied from the start at this phase's      *)
(* scale (constants to ~5937475).                                   *)
(* hGRIND_even 2968735 in the TOP10 closings:                       *)
Lemma NUM56a : 5937474 = 2 * 2968735 + 4.
Proof. apply Nat.eqb_eq; vm_compute; reflexivity. Qed.
Lemma NUM56b : 4042956 = S 4042955.
Proof. apply Nat.eqb_eq; vm_compute; reflexivity. Qed.
(* The r10' = 2 closing (TRANS2_1 at TOP10):                        *)
Lemma NUM56e : 5937475 = S 5937474.
Proof. apply Nat.eqb_eq; vm_compute; reflexivity. Qed.
Lemma NUM56f : 5937476 = S (S 5937474).
Proof. apply Nat.eqb_eq; vm_compute; reflexivity. Qed.
Lemma NUM56g : 4042957 = S 4042956.
Proof. apply Nat.eqb_eq; vm_compute; reflexivity. Qed.
(* The r10' = 4 / 6 / band first TUP (shuttle form):                *)
Lemma NUM56h : 5937474 = 5937475 - 1.
Proof. apply Nat.eqb_eq; vm_compute; reflexivity. Qed.
(* The r10' = 4 TRANS2_2 step and the TUP2_1 steps:                 *)
Lemma NUM56i : 5937474 = S 5937473.
Proof. apply Nat.eqb_eq; vm_compute; reflexivity. Qed.
Lemma NUM56j : 5937475 = S (S 5937473).
Proof. apply Nat.eqb_eq; vm_compute; reflexivity. Qed.
(* The band CLEANG_even floor:                                      *)
Lemma NUM56k : 5937474 = 5937477 - 3.
Proof. apply Nat.eqb_eq; vm_compute; reflexivity. Qed.
(* The TAIL2_END10_of56 case split:                                 *)
Lemma NUM56m : 5937478 = S 5937477.
Proof. apply Nat.eqb_eq; vm_compute; reflexivity. Qed.
Lemma NUM56n : 5937476 = S 5937475.
Proof. apply Nat.eqb_eq; vm_compute; reflexivity. Qed.

(* Factored list identities for the three PX2A steps of     *)
(* CASCADE56 whose produced (1, 2)s merge into a spine      *)
(* repeat of length > 175000 (cascade steps 1, 6, 468):     *)
(* the goal's stated target is first rewritten to the       *)
(* constructor's unmerged form via REP56a-c (whose proofs   *)
(* rewrite the run length to S-form and close by            *)
(* reflexivity), and the frame atoms are put in S-form via  *)
(* NUM56ta1-3 / tb1-3 / tc1-3, since hPX2A's frame pattern   *)
(* is S (S (S b')) :: S p' :: pb and its target counter is  *)
(* S b' (the CASCADE55 step-1 pattern, generalised).       *)
Lemma NUM56ssa : 2851852 = S (S 2851850).
Proof. apply Nat.eqb_eq; vm_compute; reflexivity. Qed.
Lemma REP56a : forall w,
  (1, 1) :: (1, 2) :: (1, 2) :: repeat (1, 2) 2851850 ++ w
  = (1, 1) :: repeat (1, 2) 2851852 ++ w.
Proof. intro w. rewrite NUM56ssa. reflexivity. Qed.
Lemma NUM56ta1 : 2020419 = S (S (S 2020416)).
Proof. apply Nat.eqb_eq; vm_compute; reflexivity. Qed.
Lemma NUM56ta2 : 297773 = S 297772.
Proof. apply Nat.eqb_eq; vm_compute; reflexivity. Qed.
Lemma NUM56ta3 : 2020417 = S 2020416.
Proof. apply Nat.eqb_eq; vm_compute; reflexivity. Qed.
Lemma NUM56ssb : 297773 = S (S 297771).
Proof. apply Nat.eqb_eq; vm_compute; reflexivity. Qed.
Lemma REP56b : forall w,
  (1, 1) :: (1, 2) :: (1, 2) :: repeat (1, 2) 297771 ++ w
  = (1, 1) :: repeat (1, 2) 297773 ++ w.
Proof. intro w. rewrite NUM56ssb. reflexivity. Qed.
Lemma NUM56tb1 : 149464 = S (S (S 149461)).
Proof. apply Nat.eqb_eq; vm_compute; reflexivity. Qed.
Lemma NUM56tb2 : 1260 = S 1259.
Proof. apply Nat.eqb_eq; vm_compute; reflexivity. Qed.
Lemma NUM56tb3 : 149462 = S 149461.
Proof. apply Nat.eqb_eq; vm_compute; reflexivity. Qed.
Lemma NUM56ssc : 595550 = S (S 595548).
Proof. apply Nat.eqb_eq; vm_compute; reflexivity. Qed.
Lemma REP56c : forall w,
  (1, 1) :: (1, 2) :: (1, 2) :: repeat (1, 2) 595548 ++ w
  = (1, 1) :: repeat (1, 2) 595550 ++ w.
Proof. intro w. rewrite NUM56ssc. reflexivity. Qed.
Lemma NUM56tc1 : 366882 = S (S (S 366879)).
Proof. apply Nat.eqb_eq; vm_compute; reflexivity. Qed.
Lemma NUM56tc2 : 51689 = S 51688.
Proof. apply Nat.eqb_eq; vm_compute; reflexivity. Qed.
Lemma NUM56tc3 : 366880 = S 366879.
Proof. apply Nat.eqb_eq; vm_compute; reflexivity. Qed.

(* Closed arithmetic identities for the large DIPGRIND /   *)
(* hGRIND_even / CLEANG steps and the head-pair             *)
(* normalisations of CASCADE56, factored into standalone    *)
(* lemmas (eqb/vm proofs) and rewritten in the step blocks, *)
(* so the applies meet the lemmas' arithmetic forms        *)
(* syntactically instead of by a closed multiplication or   *)
(* subtraction conversion at depth >= 100000                *)
(* (cf. NUM56ss / REP56a-c).                                *)
Lemma NUM56X1 : 297772 = S 297771.
Proof. apply Nat.eqb_eq; vm_compute; reflexivity. Qed.
Lemma NUM56X2 : 2020415 = 2020417 - 2.
Proof. apply Nat.eqb_eq; vm_compute; reflexivity. Qed.
Lemma NUM56X3 : 2020413 = 2020415 - 2.
Proof. apply Nat.eqb_eq; vm_compute; reflexivity. Qed.
Lemma NUM56X4 : 2020413 = 2 * 297771 + 1424871.
Proof. apply Nat.eqb_eq; vm_compute; reflexivity. Qed.
Lemma NUM56X5 : 149458 = 2 * 1258 + 146942.
Proof. apply Nat.eqb_eq; vm_compute; reflexivity. Qed.
Lemma NUM56X6 : 146936 = 2 * 2534 + 141868.
Proof. apply Nat.eqb_eq; vm_compute; reflexivity. Qed.
Lemma NUM56X7 : 141862 = 2 * 5074 + 131714.
Proof. apply Nat.eqb_eq; vm_compute; reflexivity. Qed.
Lemma NUM56X8 : 131708 = 2 * 10430 + 110848.
Proof. apply Nat.eqb_eq; vm_compute; reflexivity. Qed.
Lemma NUM56X9 : 110842 = 2 * 20866 + 69110.
Proof. apply Nat.eqb_eq; vm_compute; reflexivity. Qed.
Lemma NUM56X10 : 51688 = 2 * 25842 + 4.
Proof. apply Nat.eqb_eq; vm_compute; reflexivity. Qed.
Lemma NUM56X11 : 69104 = 2 * 34551 + 2.
Proof. apply Nat.eqb_eq; vm_compute; reflexivity. Qed.
Lemma NUM56X12 : 69108 = 2 * 34551 + 6.
Proof. apply Nat.eqb_eq; vm_compute; reflexivity. Qed.
Lemma NUM56X13 : 595548 = 595549 - 1.
Proof. apply Nat.eqb_eq; vm_compute; reflexivity. Qed.
Lemma NUM56X14 : 1424869 = 1424871 - 2.
Proof. apply Nat.eqb_eq; vm_compute; reflexivity. Qed.
Lemma NUM56X15 : 595548 = 2 * 297772 + 4.
Proof. apply Nat.eqb_eq; vm_compute; reflexivity. Qed.
Lemma NUM56X16 : 595548 = S 595547.
Proof. apply Nat.eqb_eq; vm_compute; reflexivity. Qed.
Lemma NUM56X17 : 366882 = S 366881.
Proof. apply Nat.eqb_eq; vm_compute; reflexivity. Qed.
Lemma NUM56X18 : 1424867 = 1424869 - 2.
Proof. apply Nat.eqb_eq; vm_compute; reflexivity. Qed.
Lemma NUM56X19 : 1424865 = 1424867 - 2.
Proof. apply Nat.eqb_eq; vm_compute; reflexivity. Qed.
Lemma NUM56X20 : 1424865 = 2 * 595548 + 233769.
Proof. apply Nat.eqb_eq; vm_compute; reflexivity. Qed.
Lemma NUM56X21 : 366878 = 366880 - 2.
Proof. apply Nat.eqb_eq; vm_compute; reflexivity. Qed.
Lemma NUM56X22 : 366876 = 366878 - 2.
Proof. apply Nat.eqb_eq; vm_compute; reflexivity. Qed.
Lemma NUM56X23 : 366876 = 2 * 51687 + 263502.
Proof. apply Nat.eqb_eq; vm_compute; reflexivity. Qed.
Lemma NUM56X24 : 103380 = 103381 - 1.
Proof. apply Nat.eqb_eq; vm_compute; reflexivity. Qed.
Lemma NUM56X25 : 263500 = 263502 - 2.
Proof. apply Nat.eqb_eq; vm_compute; reflexivity. Qed.
Lemma NUM56X26 : 103380 = 2 * 51688 + 4.
Proof. apply Nat.eqb_eq; vm_compute; reflexivity. Qed.
Lemma NUM56X27 : 103380 = S 103379.
Proof. apply Nat.eqb_eq; vm_compute; reflexivity. Qed.
Lemma NUM56X28 : 263498 = 263500 - 2.
Proof. apply Nat.eqb_eq; vm_compute; reflexivity. Qed.
Lemma NUM56X29 : 263496 = 263498 - 2.
Proof. apply Nat.eqb_eq; vm_compute; reflexivity. Qed.
Lemma NUM56X30 : 263496 = 2 * 103380 + 56736.
Proof. apply Nat.eqb_eq; vm_compute; reflexivity. Qed.
Lemma NUM56X31 : 206766 = 206767 - 1.
Proof. apply Nat.eqb_eq; vm_compute; reflexivity. Qed.
Lemma NUM56X32 : 206766 = 2 * 103381 + 4.
Proof. apply Nat.eqb_eq; vm_compute; reflexivity. Qed.
Lemma NUM56X33 : 206766 = S 206765.
Proof. apply Nat.eqb_eq; vm_compute; reflexivity. Qed.
Lemma NUM56X34 : 138671 = S 138670.
Proof. apply Nat.eqb_eq; vm_compute; reflexivity. Qed.
Lemma NUM56X35 : 56730 = 2 * 28364 + 2.
Proof. apply Nat.eqb_eq; vm_compute; reflexivity. Qed.
Lemma NUM56X36 : 56734 = 2 * 28364 + 6.
Proof. apply Nat.eqb_eq; vm_compute; reflexivity. Qed.
Lemma NUM56X37 : 206767 = S 206766.
Proof. apply Nat.eqb_eq; vm_compute; reflexivity. Qed.
Lemma NUM56X38 : 1191102 = 1191103 - 1.
Proof. apply Nat.eqb_eq; vm_compute; reflexivity. Qed.
Lemma NUM56X39 : 233767 = 233769 - 2.
Proof. apply Nat.eqb_eq; vm_compute; reflexivity. Qed.
Lemma NUM56X40 : 1191102 = 2 * 595549 + 4.
Proof. apply Nat.eqb_eq; vm_compute; reflexivity. Qed.
Lemma NUM56X41 : 1191102 = S 1191101.
Proof. apply Nat.eqb_eq; vm_compute; reflexivity. Qed.
Lemma NUM56X42 : 652285 = S 652284.
Proof. apply Nat.eqb_eq; vm_compute; reflexivity. Qed.
Lemma NUM56X43 : 233765 = 233767 - 2.
Proof. apply Nat.eqb_eq; vm_compute; reflexivity. Qed.
Lemma NUM56X44 : 233763 = 233765 - 2.
Proof. apply Nat.eqb_eq; vm_compute; reflexivity. Qed.
Lemma NUM56X45 : 233763 = 2 * 116880 + 3.
Proof. apply Nat.eqb_eq; vm_compute; reflexivity. Qed.
Lemma NUM56X46 : 233768 = 2 * 116880 + 8.
Proof. apply Nat.eqb_eq; vm_compute; reflexivity. Qed.
Lemma NUM56X47 : 1191104 = S 1191103.
Proof. apply Nat.eqb_eq; vm_compute; reflexivity. Qed.
Lemma NUM56X48 : 233771 = 233770 + 1.
Proof. apply Nat.eqb_eq; vm_compute; reflexivity. Qed.

(* ----------------------------------------------------------------- *)
(* CASCADE56: the tenth fixed-parse cascade (799 steps).           *)
(* ----------------------------------------------------------------- *)

(* CASCADE56a: steps 1-56 of the CASCADE56 chain. *)
Lemma CASCADE56a : forall w,
  hsteps (HC [2020419; 297773; 149464; 1260; 147; 20; 0] 0 3 2 (repeat (1, 2) 2851850 ++ w) 1)
         (HC [50; 14; 5] 1354 2534 2 ((146940, 2) :: (1, 1) :: repeat (1, 2) 297773 ++ (1424871, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) 1).
Proof.
  intro w.
  (* step 1: P PX2A *)
  apply (hsteps_trans _ (HC [149464; 1260; 147; 20; 0] 297772 2020417 2 ((1, 1) :: repeat (1, 2) 2851852 ++ w) 1)).
  {
    rewrite NUM56ta1. rewrite NUM56ta2. rewrite NUM56ta3.
    replace ((1, 1) :: repeat (1, 2) 2851852 ++ w)
      with ((1, 1) :: (1, 2) :: (1, 2) :: repeat (1, 2) 2851850 ++ w)
      by (apply REP56a).
    exact (hsteps_step _ _ _ (hPX2A 2020416 297772 [149464; 1260; 147; 20; 0] (repeat (1, 2) 2851850 ++ w) 1) (hsteps_refl _)).
  }
  (* step 2: P PUSH *)
  apply (hsteps_trans _ (HC [149464; 1260; 147; 20; 0] 297771 1 2 ((2020415, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) 1)).
  {
    rewrite NUM56X1.
    rewrite NUM56X2.
    apply (sPUSH [149464; 1260; 147; 20; 0] 297771 2020417 ((1, 1) :: repeat (1, 2) 2851852 ++ w) 1); closearith.
  }
  (* step 3: P TDN *)
  apply (hsteps_trans _ (HB [149464; 1260; 147; 20; 0] 297771 1 4 ((2020415, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) 1)).
  {
    apply (sTDN [149464; 1260; 147; 20; 0] 297771 ((2020415, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) 1).
  }
  (* step 4: sTUP *)
  apply (hsteps_trans _ (HC [149464; 1260; 147; 20; 0] 297771 3 2 ((2020413, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) 1)).
  {
    rewrite NUM56X3.
    apply (sTUP [149464; 1260; 147; 20; 0] 297771 4 2020415 2 ((1, 1) :: repeat (1, 2) 2851852 ++ w) 1); closearith.
  }
  (* step 5: DIPGRIND 297771 1424871 *)
  apply (hsteps_trans _ (HC [149464; 1260; 147; 20; 0] 0 3 2 (repeat (1, 2) 297771 ++ (1424871, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) 1)).
  {
    rewrite NUM56X4.
    apply (DIPGRIND 297771 1424871 [149464; 1260; 147; 20; 0] ((1, 1) :: repeat (1, 2) 2851852 ++ w) 1); closearith.
  }
  (* step 6: P PX2A *)
  apply (hsteps_trans _ (HC [147; 20; 0] 1259 149462 2 ((1, 1) :: repeat (1, 2) 297773 ++ (1424871, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) 1)).
  {
    rewrite NUM56tb1. rewrite NUM56tb3.
    replace ((1, 1) :: repeat (1, 2) 297773 ++ (1424871, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w)
      with ((1, 1) :: (1, 2) :: (1, 2) :: repeat (1, 2) 297771 ++ (1424871, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w)
      by (apply REP56b).
    exact (hsteps_step _ _ _ (hPX2A 149461 1259 [147; 20; 0] (repeat (1, 2) 297771 ++ (1424871, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) 1) (hsteps_refl _)).
  }
  (* step 7: P PUSH *)
  apply (hsteps_trans _ (HC [147; 20; 0] 1258 1 2 ((149460, 2) :: (1, 1) :: repeat (1, 2) 297773 ++ (1424871, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) 1)).
  {
    replace ((149460, 2) :: (1, 1) :: repeat (1, 2) 297773 ++ (1424871, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) with ((149462 - 2, 2) :: (1, 1) :: repeat (1, 2) 297773 ++ (1424871, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) by sec_eq.
    apply (sPUSH [147; 20; 0] 1258 149462 ((1, 1) :: repeat (1, 2) 297773 ++ (1424871, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) 1); closearith.
  }
  (* step 8: P TDN *)
  apply (hsteps_trans _ (HB [147; 20; 0] 1258 1 4 ((149460, 2) :: (1, 1) :: repeat (1, 2) 297773 ++ (1424871, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) 1)).
  {
    apply (sTDN [147; 20; 0] 1258 ((149460, 2) :: (1, 1) :: repeat (1, 2) 297773 ++ (1424871, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) 1).
  }
  (* step 9: sTUP *)
  apply (hsteps_trans _ (HC [147; 20; 0] 1258 3 2 ((149458, 2) :: (1, 1) :: repeat (1, 2) 297773 ++ (1424871, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) 1)).
  {
    replace ((149458, 2) :: (1, 1) :: repeat (1, 2) 297773 ++ (1424871, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) with ((149460 - 2, 2) :: (1, 1) :: repeat (1, 2) 297773 ++ (1424871, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) by sec_eq.
    apply (sTUP [147; 20; 0] 1258 4 149460 2 ((1, 1) :: repeat (1, 2) 297773 ++ (1424871, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) 1); closearith.
  }
  (* step 10: DIPGRIND 1258 146942 *)
  apply (hsteps_trans _ (HC [147; 20; 0] 0 3 2 (repeat (1, 2) 1258 ++ (146942, 2) :: (1, 1) :: repeat (1, 2) 297773 ++ (1424871, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) 1)).
  {
    rewrite NUM56X5.
    apply (DIPGRIND 1258 146942 [147; 20; 0] ((1, 1) :: repeat (1, 2) 297773 ++ (1424871, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) 1); closearith.
  }
  (* step 11: P PX2A *)
  apply (hsteps_trans _ (HC [0] 19 145 2 ((1, 1) :: repeat (1, 2) 1260 ++ (146942, 2) :: (1, 1) :: repeat (1, 2) 297773 ++ (1424871, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) 1)).
  {
    exact (hsteps_step _ _ _ (hPX2A 144 19 [0] (repeat (1, 2) 1258 ++ (146942, 2) :: (1, 1) :: repeat (1, 2) 297773 ++ (1424871, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) 1) (hsteps_refl _)).
  }
  (* step 12: P PUSH *)
  apply (hsteps_trans _ (HC [0] 18 1 2 ((143, 2) :: (1, 1) :: repeat (1, 2) 1260 ++ (146942, 2) :: (1, 1) :: repeat (1, 2) 297773 ++ (1424871, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) 1)).
  {
    replace ((143, 2) :: (1, 1) :: repeat (1, 2) 1260 ++ (146942, 2) :: (1, 1) :: repeat (1, 2) 297773 ++ (1424871, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) with ((145 - 2, 2) :: (1, 1) :: repeat (1, 2) 1260 ++ (146942, 2) :: (1, 1) :: repeat (1, 2) 297773 ++ (1424871, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) by sec_eq.
    apply (sPUSH [0] 18 145 ((1, 1) :: repeat (1, 2) 1260 ++ (146942, 2) :: (1, 1) :: repeat (1, 2) 297773 ++ (1424871, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) 1); closearith.
  }
  (* step 13: P TDN *)
  apply (hsteps_trans _ (HB [0] 18 1 4 ((143, 2) :: (1, 1) :: repeat (1, 2) 1260 ++ (146942, 2) :: (1, 1) :: repeat (1, 2) 297773 ++ (1424871, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) 1)).
  {
    apply (sTDN [0] 18 ((143, 2) :: (1, 1) :: repeat (1, 2) 1260 ++ (146942, 2) :: (1, 1) :: repeat (1, 2) 297773 ++ (1424871, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) 1).
  }
  (* step 14: sTUP *)
  apply (hsteps_trans _ (HC [0] 18 3 2 ((141, 2) :: (1, 1) :: repeat (1, 2) 1260 ++ (146942, 2) :: (1, 1) :: repeat (1, 2) 297773 ++ (1424871, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) 1)).
  {
    replace ((141, 2) :: (1, 1) :: repeat (1, 2) 1260 ++ (146942, 2) :: (1, 1) :: repeat (1, 2) 297773 ++ (1424871, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) with ((143 - 2, 2) :: (1, 1) :: repeat (1, 2) 1260 ++ (146942, 2) :: (1, 1) :: repeat (1, 2) 297773 ++ (1424871, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) by sec_eq.
    apply (sTUP [0] 18 4 143 2 ((1, 1) :: repeat (1, 2) 1260 ++ (146942, 2) :: (1, 1) :: repeat (1, 2) 297773 ++ (1424871, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) 1); closearith.
  }
  (* step 15: DIPGRIND 18 105 *)
  apply (hsteps_trans _ (HC [0] 0 3 2 (repeat (1, 2) 18 ++ (105, 2) :: (1, 1) :: repeat (1, 2) 1260 ++ (146942, 2) :: (1, 1) :: repeat (1, 2) 297773 ++ (1424871, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) 1)).
  {
    apply (DIPGRIND 18 105 [0] ((1, 1) :: repeat (1, 2) 1260 ++ (146942, 2) :: (1, 1) :: repeat (1, 2) 297773 ++ (1424871, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) 1); closearith.
  }
  (* step 16: P PX2B0 *)
  apply (hsteps_trans _ (HB [] 0 1 5 (repeat (1, 2) 19 ++ (105, 2) :: (1, 1) :: repeat (1, 2) 1260 ++ (146942, 2) :: (1, 1) :: repeat (1, 2) 297773 ++ (1424871, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) 1)).
  {
    exact (hsteps_step _ _ _ (hPX2B0 (repeat (1, 2) 18 ++ (105, 2) :: (1, 1) :: repeat (1, 2) 1260 ++ (146942, 2) :: (1, 1) :: repeat (1, 2) 297773 ++ (1424871, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) 1) (hsteps_refl _)).
  }
  (* step 17: M pop12 (19,) *)
  apply (hsteps_trans _ (HB [] 19 1 43 ((105, 2) :: (1, 1) :: repeat (1, 2) 1260 ++ (146942, 2) :: (1, 1) :: repeat (1, 2) 297773 ++ (1424871, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) 1)).
  {
    apply (pop12 19 [] 0 5 ((105, 2) :: (1, 1) :: repeat (1, 2) 1260 ++ (146942, 2) :: (1, 1) :: repeat (1, 2) 297773 ++ (1424871, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) 1); closearith.
  }
  (* step 18: sTUP *)
  apply (hsteps_trans _ (HC [] 19 42 2 ((103, 2) :: (1, 1) :: repeat (1, 2) 1260 ++ (146942, 2) :: (1, 1) :: repeat (1, 2) 297773 ++ (1424871, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) 1)).
  {
    replace ((103, 2) :: (1, 1) :: repeat (1, 2) 1260 ++ (146942, 2) :: (1, 1) :: repeat (1, 2) 297773 ++ (1424871, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) with ((105 - 2, 2) :: (1, 1) :: repeat (1, 2) 1260 ++ (146942, 2) :: (1, 1) :: repeat (1, 2) 297773 ++ (1424871, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) by sec_eq.
    apply (sTUP [] 19 43 105 2 ((1, 1) :: repeat (1, 2) 1260 ++ (146942, 2) :: (1, 1) :: repeat (1, 2) 297773 ++ (1424871, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) 1); closearith.
  }
  (* step 19: P PUSH *)
  apply (hsteps_trans _ (HC [] 18 1 2 ((40, 2) :: (103, 2) :: (1, 1) :: repeat (1, 2) 1260 ++ (146942, 2) :: (1, 1) :: repeat (1, 2) 297773 ++ (1424871, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) 1)).
  {
    replace ((40, 2) :: (103, 2) :: (1, 1) :: repeat (1, 2) 1260 ++ (146942, 2) :: (1, 1) :: repeat (1, 2) 297773 ++ (1424871, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) with ((42 - 2, 2) :: (103, 2) :: (1, 1) :: repeat (1, 2) 1260 ++ (146942, 2) :: (1, 1) :: repeat (1, 2) 297773 ++ (1424871, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) by sec_eq.
    apply (sPUSH [] 18 42 ((103, 2) :: (1, 1) :: repeat (1, 2) 1260 ++ (146942, 2) :: (1, 1) :: repeat (1, 2) 297773 ++ (1424871, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) 1); closearith.
  }
  (* step 20: P TDN *)
  apply (hsteps_trans _ (HB [] 18 1 4 ((40, 2) :: (103, 2) :: (1, 1) :: repeat (1, 2) 1260 ++ (146942, 2) :: (1, 1) :: repeat (1, 2) 297773 ++ (1424871, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) 1)).
  {
    apply (sTDN [] 18 ((40, 2) :: (103, 2) :: (1, 1) :: repeat (1, 2) 1260 ++ (146942, 2) :: (1, 1) :: repeat (1, 2) 297773 ++ (1424871, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) 1).
  }
  (* step 21: sTUP *)
  apply (hsteps_trans _ (HC [] 18 3 2 ((38, 2) :: (103, 2) :: (1, 1) :: repeat (1, 2) 1260 ++ (146942, 2) :: (1, 1) :: repeat (1, 2) 297773 ++ (1424871, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) 1)).
  {
    replace ((38, 2) :: (103, 2) :: (1, 1) :: repeat (1, 2) 1260 ++ (146942, 2) :: (1, 1) :: repeat (1, 2) 297773 ++ (1424871, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) with ((40 - 2, 2) :: (103, 2) :: (1, 1) :: repeat (1, 2) 1260 ++ (146942, 2) :: (1, 1) :: repeat (1, 2) 297773 ++ (1424871, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) by sec_eq.
    apply (sTUP [] 18 4 40 2 ((103, 2) :: (1, 1) :: repeat (1, 2) 1260 ++ (146942, 2) :: (1, 1) :: repeat (1, 2) 297773 ++ (1424871, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) 1); closearith.
  }
  (* step 22: DIPGRIND 18 2 *)
  apply (hsteps_trans _ (HC [] 0 3 2 (repeat (1, 2) 18 ++ (2, 2) :: (103, 2) :: (1, 1) :: repeat (1, 2) 1260 ++ (146942, 2) :: (1, 1) :: repeat (1, 2) 297773 ++ (1424871, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) 1)).
  {
    apply (DIPGRIND 18 2 [] ((103, 2) :: (1, 1) :: repeat (1, 2) 1260 ++ (146942, 2) :: (1, 1) :: repeat (1, 2) 297773 ++ (1424871, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) 1); closearith.
  }
  (* step 23: P PUSHX *)
  apply (hsteps_trans _ (HB [] 1 1 7 (repeat (1, 2) 18 ++ (2, 2) :: (103, 2) :: (1, 1) :: repeat (1, 2) 1260 ++ (146942, 2) :: (1, 1) :: repeat (1, 2) 297773 ++ (1424871, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) 1)).
  {
    exact (hsteps_step _ _ _ (hPUSHX (repeat (1, 2) 18 ++ (2, 2) :: (103, 2) :: (1, 1) :: repeat (1, 2) 1260 ++ (146942, 2) :: (1, 1) :: repeat (1, 2) 297773 ++ (1424871, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) 1) (hsteps_refl _)).
  }
  (* step 24: M pop12 (18,) *)
  apply (hsteps_trans _ (HB [] 19 1 43 ((2, 2) :: (103, 2) :: (1, 1) :: repeat (1, 2) 1260 ++ (146942, 2) :: (1, 1) :: repeat (1, 2) 297773 ++ (1424871, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) 1)).
  {
    apply (pop12 18 [] 1 7 ((2, 2) :: (103, 2) :: (1, 1) :: repeat (1, 2) 1260 ++ (146942, 2) :: (1, 1) :: repeat (1, 2) 297773 ++ (1424871, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) 1); closearith.
  }
  (* step 25: P TUP2_1 *)
  apply (hsteps_trans _ (HC [20] 43 1 2 ((101, 2) :: (1, 1) :: repeat (1, 2) 1260 ++ (146942, 2) :: (1, 1) :: repeat (1, 2) 297773 ++ (1424871, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) 1)).
  {
    replace ((101, 2) :: (1, 1) :: repeat (1, 2) 1260 ++ (146942, 2) :: (1, 1) :: repeat (1, 2) 297773 ++ (1424871, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) with ((103 - 2, 2) :: (1, 1) :: repeat (1, 2) 1260 ++ (146942, 2) :: (1, 1) :: repeat (1, 2) 297773 ++ (1424871, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) by sec_eq.
    apply (sTUP2_1 [] 19 42 103 ((1, 1) :: repeat (1, 2) 1260 ++ (146942, 2) :: (1, 1) :: repeat (1, 2) 297773 ++ (1424871, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) 1); closearith.
  }
  (* step 26: P TDN *)
  apply (hsteps_trans _ (HB [20] 43 1 4 ((101, 2) :: (1, 1) :: repeat (1, 2) 1260 ++ (146942, 2) :: (1, 1) :: repeat (1, 2) 297773 ++ (1424871, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) 1)).
  {
    apply (sTDN [20] 43 ((101, 2) :: (1, 1) :: repeat (1, 2) 1260 ++ (146942, 2) :: (1, 1) :: repeat (1, 2) 297773 ++ (1424871, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) 1).
  }
  (* step 27: sTUP *)
  apply (hsteps_trans _ (HC [20] 43 3 2 ((99, 2) :: (1, 1) :: repeat (1, 2) 1260 ++ (146942, 2) :: (1, 1) :: repeat (1, 2) 297773 ++ (1424871, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) 1)).
  {
    replace ((99, 2) :: (1, 1) :: repeat (1, 2) 1260 ++ (146942, 2) :: (1, 1) :: repeat (1, 2) 297773 ++ (1424871, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) with ((101 - 2, 2) :: (1, 1) :: repeat (1, 2) 1260 ++ (146942, 2) :: (1, 1) :: repeat (1, 2) 297773 ++ (1424871, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) by sec_eq.
    apply (sTUP [20] 43 4 101 2 ((1, 1) :: repeat (1, 2) 1260 ++ (146942, 2) :: (1, 1) :: repeat (1, 2) 297773 ++ (1424871, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) 1); closearith.
  }
  (* step 28: DIPGRIND 43 13 *)
  apply (hsteps_trans _ (HC [20] 0 3 2 (repeat (1, 2) 43 ++ (13, 2) :: (1, 1) :: repeat (1, 2) 1260 ++ (146942, 2) :: (1, 1) :: repeat (1, 2) 297773 ++ (1424871, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) 1)).
  {
    apply (DIPGRIND 43 13 [20] ((1, 1) :: repeat (1, 2) 1260 ++ (146942, 2) :: (1, 1) :: repeat (1, 2) 297773 ++ (1424871, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) 1); closearith.
  }
  (* step 29: P PX2Bgen *)
  apply (hsteps_trans _ (HB [0] 3 1 2 ((16, 2) :: (1, 1) :: repeat (1, 2) 45 ++ (13, 2) :: (1, 1) :: repeat (1, 2) 1260 ++ (146942, 2) :: (1, 1) :: repeat (1, 2) 297773 ++ (1424871, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) 1)).
  {
    exact (hsteps_step _ _ _ (hPX2Bgen 15 (repeat (1, 2) 43 ++ (13, 2) :: (1, 1) :: repeat (1, 2) 1260 ++ (146942, 2) :: (1, 1) :: repeat (1, 2) 297773 ++ (1424871, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) 1) (hsteps_refl _)).
  }
  (* step 30: sTUP *)
  apply (hsteps_trans _ (HC [0] 3 1 2 ((14, 2) :: (1, 1) :: repeat (1, 2) 45 ++ (13, 2) :: (1, 1) :: repeat (1, 2) 1260 ++ (146942, 2) :: (1, 1) :: repeat (1, 2) 297773 ++ (1424871, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) 1)).
  {
    replace ((14, 2) :: (1, 1) :: repeat (1, 2) 45 ++ (13, 2) :: (1, 1) :: repeat (1, 2) 1260 ++ (146942, 2) :: (1, 1) :: repeat (1, 2) 297773 ++ (1424871, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) with ((16 - 2, 2) :: (1, 1) :: repeat (1, 2) 45 ++ (13, 2) :: (1, 1) :: repeat (1, 2) 1260 ++ (146942, 2) :: (1, 1) :: repeat (1, 2) 297773 ++ (1424871, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) by sec_eq.
    apply (sTUP [0] 3 2 16 2 ((1, 1) :: repeat (1, 2) 45 ++ (13, 2) :: (1, 1) :: repeat (1, 2) 1260 ++ (146942, 2) :: (1, 1) :: repeat (1, 2) 297773 ++ (1424871, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) 1); closearith.
  }
  (* step 31: P TDN *)
  apply (hsteps_trans _ (HB [0] 3 1 4 ((14, 2) :: (1, 1) :: repeat (1, 2) 45 ++ (13, 2) :: (1, 1) :: repeat (1, 2) 1260 ++ (146942, 2) :: (1, 1) :: repeat (1, 2) 297773 ++ (1424871, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) 1)).
  {
    apply (sTDN [0] 3 ((14, 2) :: (1, 1) :: repeat (1, 2) 45 ++ (13, 2) :: (1, 1) :: repeat (1, 2) 1260 ++ (146942, 2) :: (1, 1) :: repeat (1, 2) 297773 ++ (1424871, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) 1).
  }
  (* step 32: sTUP *)
  apply (hsteps_trans _ (HC [0] 3 3 2 ((12, 2) :: (1, 1) :: repeat (1, 2) 45 ++ (13, 2) :: (1, 1) :: repeat (1, 2) 1260 ++ (146942, 2) :: (1, 1) :: repeat (1, 2) 297773 ++ (1424871, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) 1)).
  {
    replace ((12, 2) :: (1, 1) :: repeat (1, 2) 45 ++ (13, 2) :: (1, 1) :: repeat (1, 2) 1260 ++ (146942, 2) :: (1, 1) :: repeat (1, 2) 297773 ++ (1424871, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) with ((14 - 2, 2) :: (1, 1) :: repeat (1, 2) 45 ++ (13, 2) :: (1, 1) :: repeat (1, 2) 1260 ++ (146942, 2) :: (1, 1) :: repeat (1, 2) 297773 ++ (1424871, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) by sec_eq.
    apply (sTUP [0] 3 4 14 2 ((1, 1) :: repeat (1, 2) 45 ++ (13, 2) :: (1, 1) :: repeat (1, 2) 1260 ++ (146942, 2) :: (1, 1) :: repeat (1, 2) 297773 ++ (1424871, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) 1); closearith.
  }
  (* step 33: DIPGRIND 3 6 *)
  apply (hsteps_trans _ (HC [0] 0 3 2 (repeat (1, 2) 3 ++ (6, 2) :: (1, 1) :: repeat (1, 2) 45 ++ (13, 2) :: (1, 1) :: repeat (1, 2) 1260 ++ (146942, 2) :: (1, 1) :: repeat (1, 2) 297773 ++ (1424871, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) 1)).
  {
    apply (DIPGRIND 3 6 [0] ((1, 1) :: repeat (1, 2) 45 ++ (13, 2) :: (1, 1) :: repeat (1, 2) 1260 ++ (146942, 2) :: (1, 1) :: repeat (1, 2) 297773 ++ (1424871, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) 1); closearith.
  }
  (* step 34: P PX2B0 *)
  apply (hsteps_trans _ (HB [] 0 1 5 (repeat (1, 2) 4 ++ (6, 2) :: (1, 1) :: repeat (1, 2) 45 ++ (13, 2) :: (1, 1) :: repeat (1, 2) 1260 ++ (146942, 2) :: (1, 1) :: repeat (1, 2) 297773 ++ (1424871, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) 1)).
  {
    exact (hsteps_step _ _ _ (hPX2B0 (repeat (1, 2) 3 ++ (6, 2) :: (1, 1) :: repeat (1, 2) 45 ++ (13, 2) :: (1, 1) :: repeat (1, 2) 1260 ++ (146942, 2) :: (1, 1) :: repeat (1, 2) 297773 ++ (1424871, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) 1) (hsteps_refl _)).
  }
  (* step 35: M pop12 (4,) *)
  apply (hsteps_trans _ (HB [] 4 1 13 ((6, 2) :: (1, 1) :: repeat (1, 2) 45 ++ (13, 2) :: (1, 1) :: repeat (1, 2) 1260 ++ (146942, 2) :: (1, 1) :: repeat (1, 2) 297773 ++ (1424871, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) 1)).
  {
    apply (pop12 4 [] 0 5 ((6, 2) :: (1, 1) :: repeat (1, 2) 45 ++ (13, 2) :: (1, 1) :: repeat (1, 2) 1260 ++ (146942, 2) :: (1, 1) :: repeat (1, 2) 297773 ++ (1424871, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) 1); closearith.
  }
  (* step 36: sTUP *)
  apply (hsteps_trans _ (HC [] 4 12 2 ((4, 2) :: (1, 1) :: repeat (1, 2) 45 ++ (13, 2) :: (1, 1) :: repeat (1, 2) 1260 ++ (146942, 2) :: (1, 1) :: repeat (1, 2) 297773 ++ (1424871, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) 1)).
  {
    replace ((4, 2) :: (1, 1) :: repeat (1, 2) 45 ++ (13, 2) :: (1, 1) :: repeat (1, 2) 1260 ++ (146942, 2) :: (1, 1) :: repeat (1, 2) 297773 ++ (1424871, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) with ((6 - 2, 2) :: (1, 1) :: repeat (1, 2) 45 ++ (13, 2) :: (1, 1) :: repeat (1, 2) 1260 ++ (146942, 2) :: (1, 1) :: repeat (1, 2) 297773 ++ (1424871, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) by sec_eq.
    apply (sTUP [] 4 13 6 2 ((1, 1) :: repeat (1, 2) 45 ++ (13, 2) :: (1, 1) :: repeat (1, 2) 1260 ++ (146942, 2) :: (1, 1) :: repeat (1, 2) 297773 ++ (1424871, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) 1); closearith.
  }
  (* step 37: P PUSH *)
  apply (hsteps_trans _ (HC [] 3 1 2 ((10, 2) :: (4, 2) :: (1, 1) :: repeat (1, 2) 45 ++ (13, 2) :: (1, 1) :: repeat (1, 2) 1260 ++ (146942, 2) :: (1, 1) :: repeat (1, 2) 297773 ++ (1424871, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) 1)).
  {
    replace ((10, 2) :: (4, 2) :: (1, 1) :: repeat (1, 2) 45 ++ (13, 2) :: (1, 1) :: repeat (1, 2) 1260 ++ (146942, 2) :: (1, 1) :: repeat (1, 2) 297773 ++ (1424871, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) with ((12 - 2, 2) :: (4, 2) :: (1, 1) :: repeat (1, 2) 45 ++ (13, 2) :: (1, 1) :: repeat (1, 2) 1260 ++ (146942, 2) :: (1, 1) :: repeat (1, 2) 297773 ++ (1424871, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) by sec_eq.
    apply (sPUSH [] 3 12 ((4, 2) :: (1, 1) :: repeat (1, 2) 45 ++ (13, 2) :: (1, 1) :: repeat (1, 2) 1260 ++ (146942, 2) :: (1, 1) :: repeat (1, 2) 297773 ++ (1424871, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) 1); closearith.
  }
  (* step 38: P TDN *)
  apply (hsteps_trans _ (HB [] 3 1 4 ((10, 2) :: (4, 2) :: (1, 1) :: repeat (1, 2) 45 ++ (13, 2) :: (1, 1) :: repeat (1, 2) 1260 ++ (146942, 2) :: (1, 1) :: repeat (1, 2) 297773 ++ (1424871, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) 1)).
  {
    apply (sTDN [] 3 ((10, 2) :: (4, 2) :: (1, 1) :: repeat (1, 2) 45 ++ (13, 2) :: (1, 1) :: repeat (1, 2) 1260 ++ (146942, 2) :: (1, 1) :: repeat (1, 2) 297773 ++ (1424871, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) 1).
  }
  (* step 39: sTUP *)
  apply (hsteps_trans _ (HC [] 3 3 2 ((8, 2) :: (4, 2) :: (1, 1) :: repeat (1, 2) 45 ++ (13, 2) :: (1, 1) :: repeat (1, 2) 1260 ++ (146942, 2) :: (1, 1) :: repeat (1, 2) 297773 ++ (1424871, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) 1)).
  {
    replace ((8, 2) :: (4, 2) :: (1, 1) :: repeat (1, 2) 45 ++ (13, 2) :: (1, 1) :: repeat (1, 2) 1260 ++ (146942, 2) :: (1, 1) :: repeat (1, 2) 297773 ++ (1424871, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) with ((10 - 2, 2) :: (4, 2) :: (1, 1) :: repeat (1, 2) 45 ++ (13, 2) :: (1, 1) :: repeat (1, 2) 1260 ++ (146942, 2) :: (1, 1) :: repeat (1, 2) 297773 ++ (1424871, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) by sec_eq.
    apply (sTUP [] 3 4 10 2 ((4, 2) :: (1, 1) :: repeat (1, 2) 45 ++ (13, 2) :: (1, 1) :: repeat (1, 2) 1260 ++ (146942, 2) :: (1, 1) :: repeat (1, 2) 297773 ++ (1424871, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) 1); closearith.
  }
  (* step 40: DIPGRIND 3 2 *)
  apply (hsteps_trans _ (HC [] 0 3 2 (repeat (1, 2) 3 ++ (2, 2) :: (4, 2) :: (1, 1) :: repeat (1, 2) 45 ++ (13, 2) :: (1, 1) :: repeat (1, 2) 1260 ++ (146942, 2) :: (1, 1) :: repeat (1, 2) 297773 ++ (1424871, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) 1)).
  {
    apply (DIPGRIND 3 2 [] ((4, 2) :: (1, 1) :: repeat (1, 2) 45 ++ (13, 2) :: (1, 1) :: repeat (1, 2) 1260 ++ (146942, 2) :: (1, 1) :: repeat (1, 2) 297773 ++ (1424871, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) 1); closearith.
  }
  (* step 41: P PUSHX *)
  apply (hsteps_trans _ (HB [] 1 1 7 (repeat (1, 2) 3 ++ (2, 2) :: (4, 2) :: (1, 1) :: repeat (1, 2) 45 ++ (13, 2) :: (1, 1) :: repeat (1, 2) 1260 ++ (146942, 2) :: (1, 1) :: repeat (1, 2) 297773 ++ (1424871, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) 1)).
  {
    exact (hsteps_step _ _ _ (hPUSHX (repeat (1, 2) 3 ++ (2, 2) :: (4, 2) :: (1, 1) :: repeat (1, 2) 45 ++ (13, 2) :: (1, 1) :: repeat (1, 2) 1260 ++ (146942, 2) :: (1, 1) :: repeat (1, 2) 297773 ++ (1424871, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) 1) (hsteps_refl _)).
  }
  (* step 42: M pop12 (3,) *)
  apply (hsteps_trans _ (HB [] 4 1 13 ((2, 2) :: (4, 2) :: (1, 1) :: repeat (1, 2) 45 ++ (13, 2) :: (1, 1) :: repeat (1, 2) 1260 ++ (146942, 2) :: (1, 1) :: repeat (1, 2) 297773 ++ (1424871, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) 1)).
  {
    apply (pop12 3 [] 1 7 ((2, 2) :: (4, 2) :: (1, 1) :: repeat (1, 2) 45 ++ (13, 2) :: (1, 1) :: repeat (1, 2) 1260 ++ (146942, 2) :: (1, 1) :: repeat (1, 2) 297773 ++ (1424871, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) 1); closearith.
  }
  (* step 43: P TUP2_1 *)
  apply (hsteps_trans _ (HC [5] 13 1 2 ((2, 2) :: (1, 1) :: repeat (1, 2) 45 ++ (13, 2) :: (1, 1) :: repeat (1, 2) 1260 ++ (146942, 2) :: (1, 1) :: repeat (1, 2) 297773 ++ (1424871, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) 1)).
  {
    replace ((2, 2) :: (1, 1) :: repeat (1, 2) 45 ++ (13, 2) :: (1, 1) :: repeat (1, 2) 1260 ++ (146942, 2) :: (1, 1) :: repeat (1, 2) 297773 ++ (1424871, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) with ((4 - 2, 2) :: (1, 1) :: repeat (1, 2) 45 ++ (13, 2) :: (1, 1) :: repeat (1, 2) 1260 ++ (146942, 2) :: (1, 1) :: repeat (1, 2) 297773 ++ (1424871, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) by sec_eq.
    apply (sTUP2_1 [] 4 12 4 ((1, 1) :: repeat (1, 2) 45 ++ (13, 2) :: (1, 1) :: repeat (1, 2) 1260 ++ (146942, 2) :: (1, 1) :: repeat (1, 2) 297773 ++ (1424871, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) 1); closearith.
  }
  (* step 44: P TDN *)
  apply (hsteps_trans _ (HB [5] 13 1 4 ((2, 2) :: (1, 1) :: repeat (1, 2) 45 ++ (13, 2) :: (1, 1) :: repeat (1, 2) 1260 ++ (146942, 2) :: (1, 1) :: repeat (1, 2) 297773 ++ (1424871, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) 1)).
  {
    apply (sTDN [5] 13 ((2, 2) :: (1, 1) :: repeat (1, 2) 45 ++ (13, 2) :: (1, 1) :: repeat (1, 2) 1260 ++ (146942, 2) :: (1, 1) :: repeat (1, 2) 297773 ++ (1424871, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) 1).
  }
  (* step 45: P TRANS2_1 *)
  apply (hsteps_trans _ (HB [14; 5] 5 1 3 (repeat (1, 2) 45 ++ (13, 2) :: (1, 1) :: repeat (1, 2) 1260 ++ (146942, 2) :: (1, 1) :: repeat (1, 2) 297773 ++ (1424871, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) 1)).
  {
    apply (sTRANS2_1 [5] 13 3 1 (repeat (1, 2) 45 ++ (13, 2) :: (1, 1) :: repeat (1, 2) 1260 ++ (146942, 2) :: (1, 1) :: repeat (1, 2) 297773 ++ (1424871, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) 1); closearith.
  }
  (* step 46: M pop12 (45,) *)
  apply (hsteps_trans _ (HB [14; 5] 50 1 93 ((13, 2) :: (1, 1) :: repeat (1, 2) 1260 ++ (146942, 2) :: (1, 1) :: repeat (1, 2) 297773 ++ (1424871, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) 1)).
  {
    apply (pop12 45 [14; 5] 5 3 ((13, 2) :: (1, 1) :: repeat (1, 2) 1260 ++ (146942, 2) :: (1, 1) :: repeat (1, 2) 297773 ++ (1424871, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) 1); closearith.
  }
  (* step 47: sTUP *)
  apply (hsteps_trans _ (HC [14; 5] 50 92 2 ((11, 2) :: (1, 1) :: repeat (1, 2) 1260 ++ (146942, 2) :: (1, 1) :: repeat (1, 2) 297773 ++ (1424871, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) 1)).
  {
    replace ((11, 2) :: (1, 1) :: repeat (1, 2) 1260 ++ (146942, 2) :: (1, 1) :: repeat (1, 2) 297773 ++ (1424871, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) with ((13 - 2, 2) :: (1, 1) :: repeat (1, 2) 1260 ++ (146942, 2) :: (1, 1) :: repeat (1, 2) 297773 ++ (1424871, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) by sec_eq.
    apply (sTUP [14; 5] 50 93 13 2 ((1, 1) :: repeat (1, 2) 1260 ++ (146942, 2) :: (1, 1) :: repeat (1, 2) 297773 ++ (1424871, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) 1); closearith.
  }
  (* step 48: hGRIND_even 44 *)
  apply (hsteps_trans _ (HB [14; 5] 49 1 92 ((2, 2) :: (11, 2) :: (1, 1) :: repeat (1, 2) 1260 ++ (146942, 2) :: (1, 1) :: repeat (1, 2) 297773 ++ (1424871, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) 1)).
  {
    apply (hGRIND_even 44 [14; 5] 49 ((11, 2) :: (1, 1) :: repeat (1, 2) 1260 ++ (146942, 2) :: (1, 1) :: repeat (1, 2) 297773 ++ (1424871, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) 1); closearith.
  }
  (* step 49: P TUP2_1 *)
  apply (hsteps_trans _ (HC [50; 14; 5] 92 1 2 ((9, 2) :: (1, 1) :: repeat (1, 2) 1260 ++ (146942, 2) :: (1, 1) :: repeat (1, 2) 297773 ++ (1424871, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) 1)).
  {
    replace ((9, 2) :: (1, 1) :: repeat (1, 2) 1260 ++ (146942, 2) :: (1, 1) :: repeat (1, 2) 297773 ++ (1424871, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) with ((11 - 2, 2) :: (1, 1) :: repeat (1, 2) 1260 ++ (146942, 2) :: (1, 1) :: repeat (1, 2) 297773 ++ (1424871, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) by sec_eq.
    apply (sTUP2_1 [14; 5] 49 91 11 ((1, 1) :: repeat (1, 2) 1260 ++ (146942, 2) :: (1, 1) :: repeat (1, 2) 297773 ++ (1424871, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) 1); closearith.
  }
  (* step 50: P TDN *)
  apply (hsteps_trans _ (HB [50; 14; 5] 92 1 4 ((9, 2) :: (1, 1) :: repeat (1, 2) 1260 ++ (146942, 2) :: (1, 1) :: repeat (1, 2) 297773 ++ (1424871, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) 1)).
  {
    apply (sTDN [50; 14; 5] 92 ((9, 2) :: (1, 1) :: repeat (1, 2) 1260 ++ (146942, 2) :: (1, 1) :: repeat (1, 2) 297773 ++ (1424871, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) 1).
  }
  (* step 51: sTUP *)
  apply (hsteps_trans _ (HC [50; 14; 5] 92 3 2 ((7, 2) :: (1, 1) :: repeat (1, 2) 1260 ++ (146942, 2) :: (1, 1) :: repeat (1, 2) 297773 ++ (1424871, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) 1)).
  {
    replace ((7, 2) :: (1, 1) :: repeat (1, 2) 1260 ++ (146942, 2) :: (1, 1) :: repeat (1, 2) 297773 ++ (1424871, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) with ((9 - 2, 2) :: (1, 1) :: repeat (1, 2) 1260 ++ (146942, 2) :: (1, 1) :: repeat (1, 2) 297773 ++ (1424871, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) by sec_eq.
    apply (sTUP [50; 14; 5] 92 4 9 2 ((1, 1) :: repeat (1, 2) 1260 ++ (146942, 2) :: (1, 1) :: repeat (1, 2) 297773 ++ (1424871, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) 1); closearith.
  }
  (* step 52: CLEANG_odd 2 *)
  apply (hsteps_trans _ (HB [50; 14; 5] 92 1 12 (repeat (1, 2) 1 ++ (1, 1) :: repeat (1, 2) 1260 ++ (146942, 2) :: (1, 1) :: repeat (1, 2) 297773 ++ (1424871, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) 1)).
  {
    replace (repeat (1, 2) 1 ++ (1, 1) :: repeat (1, 2) 1260 ++ (146942, 2) :: (1, 1) :: repeat (1, 2) 297773 ++ (1424871, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) with ((1, 2) :: (1, 1) :: repeat (1, 2) 1260 ++ (146942, 2) :: (1, 1) :: repeat (1, 2) 297773 ++ (1424871, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) by sec_eq.
    apply (CLEANG_odd 2 [50; 14; 5] 92 ((1, 1) :: repeat (1, 2) 1260 ++ (146942, 2) :: (1, 1) :: repeat (1, 2) 297773 ++ (1424871, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) 1); closearith.
  }
  (* step 53: M pop12 (1,) *)
  apply (hsteps_trans _ (HB [50; 14; 5] 93 1 14 ((1, 1) :: repeat (1, 2) 1260 ++ (146942, 2) :: (1, 1) :: repeat (1, 2) 297773 ++ (1424871, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) 1)).
  {
    apply (pop12 1 [50; 14; 5] 92 12 ((1, 1) :: repeat (1, 2) 1260 ++ (146942, 2) :: (1, 1) :: repeat (1, 2) 297773 ++ (1424871, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) 1); closearith.
  }
  (* step 54: P POP *)
  apply (hsteps_trans _ (HB [50; 14; 5] 94 1 15 (repeat (1, 2) 1260 ++ (146942, 2) :: (1, 1) :: repeat (1, 2) 297773 ++ (1424871, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) 1)).
  {
    apply (sPOP1 [50; 14; 5] 93 14 (repeat (1, 2) 1260 ++ (146942, 2) :: (1, 1) :: repeat (1, 2) 297773 ++ (1424871, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) 1); closearith.
  }
  (* step 55: M pop12 (1260,) *)
  apply (hsteps_trans _ (HB [50; 14; 5] 1354 1 2535 ((146942, 2) :: (1, 1) :: repeat (1, 2) 297773 ++ (1424871, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) 1)).
  {
    apply (pop12 1260 [50; 14; 5] 94 15 ((146942, 2) :: (1, 1) :: repeat (1, 2) 297773 ++ (1424871, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) 1); closearith.
  }
  (* step 56: sTUP *)
  replace ((146940, 2) :: (1, 1) :: repeat (1, 2) 297773 ++ (1424871, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) with ((146942 - 2, 2) :: (1, 1) :: repeat (1, 2) 297773 ++ (1424871, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) by sec_eq.
  apply (sTUP [50; 14; 5] 1354 2535 146942 2 ((1, 1) :: repeat (1, 2) 297773 ++ (1424871, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) 1); closearith.
Qed.

(* CASCADE56b: steps 57-112 of the CASCADE56 chain. *)
Lemma CASCADE56b : forall w,
  hsteps (HC [50; 14; 5] 1354 2534 2 ((146940, 2) :: (1, 1) :: repeat (1, 2) 297773 ++ (1424871, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) 1)
         (HC [35; 20; 0] 123 210 2 ((1040, 2) :: (1, 1) :: repeat (1, 2) 2536 ++ (141868, 2) :: (1, 1) :: repeat (1, 2) 297773 ++ (1424871, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) 1).
Proof.
  intro w.
  (* step 57: hGRIND_even 1265 *)
  apply (hsteps_trans _ (HB [50; 14; 5] 1353 1 2534 ((2, 2) :: (146940, 2) :: (1, 1) :: repeat (1, 2) 297773 ++ (1424871, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) 1)).
  {
    apply (hGRIND_even 1265 [50; 14; 5] 1353 ((146940, 2) :: (1, 1) :: repeat (1, 2) 297773 ++ (1424871, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) 1); closearith.
  }
  (* step 58: P TUP2_1 *)
  apply (hsteps_trans _ (HC [1354; 50; 14; 5] 2534 1 2 ((146938, 2) :: (1, 1) :: repeat (1, 2) 297773 ++ (1424871, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) 1)).
  {
    replace ((146938, 2) :: (1, 1) :: repeat (1, 2) 297773 ++ (1424871, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) with ((146940 - 2, 2) :: (1, 1) :: repeat (1, 2) 297773 ++ (1424871, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) by sec_eq.
    apply (sTUP2_1 [50; 14; 5] 1353 2533 146940 ((1, 1) :: repeat (1, 2) 297773 ++ (1424871, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) 1); closearith.
  }
  (* step 59: P TDN *)
  apply (hsteps_trans _ (HB [1354; 50; 14; 5] 2534 1 4 ((146938, 2) :: (1, 1) :: repeat (1, 2) 297773 ++ (1424871, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) 1)).
  {
    apply (sTDN [1354; 50; 14; 5] 2534 ((146938, 2) :: (1, 1) :: repeat (1, 2) 297773 ++ (1424871, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) 1).
  }
  (* step 60: sTUP *)
  apply (hsteps_trans _ (HC [1354; 50; 14; 5] 2534 3 2 ((146936, 2) :: (1, 1) :: repeat (1, 2) 297773 ++ (1424871, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) 1)).
  {
    replace ((146936, 2) :: (1, 1) :: repeat (1, 2) 297773 ++ (1424871, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) with ((146938 - 2, 2) :: (1, 1) :: repeat (1, 2) 297773 ++ (1424871, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) by sec_eq.
    apply (sTUP [1354; 50; 14; 5] 2534 4 146938 2 ((1, 1) :: repeat (1, 2) 297773 ++ (1424871, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) 1); closearith.
  }
  (* step 61: DIPGRIND 2534 141868 *)
  apply (hsteps_trans _ (HC [1354; 50; 14; 5] 0 3 2 (repeat (1, 2) 2534 ++ (141868, 2) :: (1, 1) :: repeat (1, 2) 297773 ++ (1424871, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) 1)).
  {
    rewrite NUM56X6.
    apply (DIPGRIND 2534 141868 [1354; 50; 14; 5] ((1, 1) :: repeat (1, 2) 297773 ++ (1424871, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) 1); closearith.
  }
  (* step 62: P PX2A *)
  apply (hsteps_trans _ (HC [14; 5] 49 1352 2 ((1, 1) :: repeat (1, 2) 2536 ++ (141868, 2) :: (1, 1) :: repeat (1, 2) 297773 ++ (1424871, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) 1)).
  {
    exact (hsteps_step _ _ _ (hPX2A 1351 49 [14; 5] (repeat (1, 2) 2534 ++ (141868, 2) :: (1, 1) :: repeat (1, 2) 297773 ++ (1424871, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) 1) (hsteps_refl _)).
  }
  (* step 63: P PUSH *)
  apply (hsteps_trans _ (HC [14; 5] 48 1 2 ((1350, 2) :: (1, 1) :: repeat (1, 2) 2536 ++ (141868, 2) :: (1, 1) :: repeat (1, 2) 297773 ++ (1424871, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) 1)).
  {
    replace ((1350, 2) :: (1, 1) :: repeat (1, 2) 2536 ++ (141868, 2) :: (1, 1) :: repeat (1, 2) 297773 ++ (1424871, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) with ((1352 - 2, 2) :: (1, 1) :: repeat (1, 2) 2536 ++ (141868, 2) :: (1, 1) :: repeat (1, 2) 297773 ++ (1424871, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) by sec_eq.
    apply (sPUSH [14; 5] 48 1352 ((1, 1) :: repeat (1, 2) 2536 ++ (141868, 2) :: (1, 1) :: repeat (1, 2) 297773 ++ (1424871, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) 1); closearith.
  }
  (* step 64: P TDN *)
  apply (hsteps_trans _ (HB [14; 5] 48 1 4 ((1350, 2) :: (1, 1) :: repeat (1, 2) 2536 ++ (141868, 2) :: (1, 1) :: repeat (1, 2) 297773 ++ (1424871, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) 1)).
  {
    apply (sTDN [14; 5] 48 ((1350, 2) :: (1, 1) :: repeat (1, 2) 2536 ++ (141868, 2) :: (1, 1) :: repeat (1, 2) 297773 ++ (1424871, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) 1).
  }
  (* step 65: sTUP *)
  apply (hsteps_trans _ (HC [14; 5] 48 3 2 ((1348, 2) :: (1, 1) :: repeat (1, 2) 2536 ++ (141868, 2) :: (1, 1) :: repeat (1, 2) 297773 ++ (1424871, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) 1)).
  {
    replace ((1348, 2) :: (1, 1) :: repeat (1, 2) 2536 ++ (141868, 2) :: (1, 1) :: repeat (1, 2) 297773 ++ (1424871, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) with ((1350 - 2, 2) :: (1, 1) :: repeat (1, 2) 2536 ++ (141868, 2) :: (1, 1) :: repeat (1, 2) 297773 ++ (1424871, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) by sec_eq.
    apply (sTUP [14; 5] 48 4 1350 2 ((1, 1) :: repeat (1, 2) 2536 ++ (141868, 2) :: (1, 1) :: repeat (1, 2) 297773 ++ (1424871, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) 1); closearith.
  }
  (* step 66: DIPGRIND 48 1252 *)
  apply (hsteps_trans _ (HC [14; 5] 0 3 2 (repeat (1, 2) 48 ++ (1252, 2) :: (1, 1) :: repeat (1, 2) 2536 ++ (141868, 2) :: (1, 1) :: repeat (1, 2) 297773 ++ (1424871, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) 1)).
  {
    apply (DIPGRIND 48 1252 [14; 5] ((1, 1) :: repeat (1, 2) 2536 ++ (141868, 2) :: (1, 1) :: repeat (1, 2) 297773 ++ (1424871, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) 1); closearith.
  }
  (* step 67: P PX2A *)
  apply (hsteps_trans _ (HC [] 4 12 2 ((1, 1) :: repeat (1, 2) 50 ++ (1252, 2) :: (1, 1) :: repeat (1, 2) 2536 ++ (141868, 2) :: (1, 1) :: repeat (1, 2) 297773 ++ (1424871, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) 1)).
  {
    exact (hsteps_step _ _ _ (hPX2A 11 4 [] (repeat (1, 2) 48 ++ (1252, 2) :: (1, 1) :: repeat (1, 2) 2536 ++ (141868, 2) :: (1, 1) :: repeat (1, 2) 297773 ++ (1424871, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) 1) (hsteps_refl _)).
  }
  (* step 68: P PUSH *)
  apply (hsteps_trans _ (HC [] 3 1 2 ((10, 2) :: (1, 1) :: repeat (1, 2) 50 ++ (1252, 2) :: (1, 1) :: repeat (1, 2) 2536 ++ (141868, 2) :: (1, 1) :: repeat (1, 2) 297773 ++ (1424871, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) 1)).
  {
    replace ((10, 2) :: (1, 1) :: repeat (1, 2) 50 ++ (1252, 2) :: (1, 1) :: repeat (1, 2) 2536 ++ (141868, 2) :: (1, 1) :: repeat (1, 2) 297773 ++ (1424871, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) with ((12 - 2, 2) :: (1, 1) :: repeat (1, 2) 50 ++ (1252, 2) :: (1, 1) :: repeat (1, 2) 2536 ++ (141868, 2) :: (1, 1) :: repeat (1, 2) 297773 ++ (1424871, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) by sec_eq.
    apply (sPUSH [] 3 12 ((1, 1) :: repeat (1, 2) 50 ++ (1252, 2) :: (1, 1) :: repeat (1, 2) 2536 ++ (141868, 2) :: (1, 1) :: repeat (1, 2) 297773 ++ (1424871, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) 1); closearith.
  }
  (* step 69: P TDN *)
  apply (hsteps_trans _ (HB [] 3 1 4 ((10, 2) :: (1, 1) :: repeat (1, 2) 50 ++ (1252, 2) :: (1, 1) :: repeat (1, 2) 2536 ++ (141868, 2) :: (1, 1) :: repeat (1, 2) 297773 ++ (1424871, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) 1)).
  {
    apply (sTDN [] 3 ((10, 2) :: (1, 1) :: repeat (1, 2) 50 ++ (1252, 2) :: (1, 1) :: repeat (1, 2) 2536 ++ (141868, 2) :: (1, 1) :: repeat (1, 2) 297773 ++ (1424871, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) 1).
  }
  (* step 70: sTUP *)
  apply (hsteps_trans _ (HC [] 3 3 2 ((8, 2) :: (1, 1) :: repeat (1, 2) 50 ++ (1252, 2) :: (1, 1) :: repeat (1, 2) 2536 ++ (141868, 2) :: (1, 1) :: repeat (1, 2) 297773 ++ (1424871, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) 1)).
  {
    replace ((8, 2) :: (1, 1) :: repeat (1, 2) 50 ++ (1252, 2) :: (1, 1) :: repeat (1, 2) 2536 ++ (141868, 2) :: (1, 1) :: repeat (1, 2) 297773 ++ (1424871, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) with ((10 - 2, 2) :: (1, 1) :: repeat (1, 2) 50 ++ (1252, 2) :: (1, 1) :: repeat (1, 2) 2536 ++ (141868, 2) :: (1, 1) :: repeat (1, 2) 297773 ++ (1424871, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) by sec_eq.
    apply (sTUP [] 3 4 10 2 ((1, 1) :: repeat (1, 2) 50 ++ (1252, 2) :: (1, 1) :: repeat (1, 2) 2536 ++ (141868, 2) :: (1, 1) :: repeat (1, 2) 297773 ++ (1424871, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) 1); closearith.
  }
  (* step 71: DIPGRIND 3 2 *)
  apply (hsteps_trans _ (HC [] 0 3 2 (repeat (1, 2) 3 ++ (2, 2) :: (1, 1) :: repeat (1, 2) 50 ++ (1252, 2) :: (1, 1) :: repeat (1, 2) 2536 ++ (141868, 2) :: (1, 1) :: repeat (1, 2) 297773 ++ (1424871, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) 1)).
  {
    apply (DIPGRIND 3 2 [] ((1, 1) :: repeat (1, 2) 50 ++ (1252, 2) :: (1, 1) :: repeat (1, 2) 2536 ++ (141868, 2) :: (1, 1) :: repeat (1, 2) 297773 ++ (1424871, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) 1); closearith.
  }
  (* step 72: P PUSHX *)
  apply (hsteps_trans _ (HB [] 1 1 7 (repeat (1, 2) 3 ++ (2, 2) :: (1, 1) :: repeat (1, 2) 50 ++ (1252, 2) :: (1, 1) :: repeat (1, 2) 2536 ++ (141868, 2) :: (1, 1) :: repeat (1, 2) 297773 ++ (1424871, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) 1)).
  {
    exact (hsteps_step _ _ _ (hPUSHX (repeat (1, 2) 3 ++ (2, 2) :: (1, 1) :: repeat (1, 2) 50 ++ (1252, 2) :: (1, 1) :: repeat (1, 2) 2536 ++ (141868, 2) :: (1, 1) :: repeat (1, 2) 297773 ++ (1424871, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) 1) (hsteps_refl _)).
  }
  (* step 73: M pop12 (3,) *)
  apply (hsteps_trans _ (HB [] 4 1 13 ((2, 2) :: (1, 1) :: repeat (1, 2) 50 ++ (1252, 2) :: (1, 1) :: repeat (1, 2) 2536 ++ (141868, 2) :: (1, 1) :: repeat (1, 2) 297773 ++ (1424871, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) 1)).
  {
    apply (pop12 3 [] 1 7 ((2, 2) :: (1, 1) :: repeat (1, 2) 50 ++ (1252, 2) :: (1, 1) :: repeat (1, 2) 2536 ++ (141868, 2) :: (1, 1) :: repeat (1, 2) 297773 ++ (1424871, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) 1); closearith.
  }
  (* step 74: P TRANS2_1 *)
  apply (hsteps_trans _ (HB [5] 14 1 3 (repeat (1, 2) 50 ++ (1252, 2) :: (1, 1) :: repeat (1, 2) 2536 ++ (141868, 2) :: (1, 1) :: repeat (1, 2) 297773 ++ (1424871, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) 1)).
  {
    apply (sTRANS2_1 [] 4 12 1 (repeat (1, 2) 50 ++ (1252, 2) :: (1, 1) :: repeat (1, 2) 2536 ++ (141868, 2) :: (1, 1) :: repeat (1, 2) 297773 ++ (1424871, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) 1); closearith.
  }
  (* step 75: M pop12 (50,) *)
  apply (hsteps_trans _ (HB [5] 64 1 103 ((1252, 2) :: (1, 1) :: repeat (1, 2) 2536 ++ (141868, 2) :: (1, 1) :: repeat (1, 2) 297773 ++ (1424871, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) 1)).
  {
    apply (pop12 50 [5] 14 3 ((1252, 2) :: (1, 1) :: repeat (1, 2) 2536 ++ (141868, 2) :: (1, 1) :: repeat (1, 2) 297773 ++ (1424871, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) 1); closearith.
  }
  (* step 76: sTUP *)
  apply (hsteps_trans _ (HC [5] 64 102 2 ((1250, 2) :: (1, 1) :: repeat (1, 2) 2536 ++ (141868, 2) :: (1, 1) :: repeat (1, 2) 297773 ++ (1424871, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) 1)).
  {
    replace ((1250, 2) :: (1, 1) :: repeat (1, 2) 2536 ++ (141868, 2) :: (1, 1) :: repeat (1, 2) 297773 ++ (1424871, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) with ((1252 - 2, 2) :: (1, 1) :: repeat (1, 2) 2536 ++ (141868, 2) :: (1, 1) :: repeat (1, 2) 297773 ++ (1424871, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) by sec_eq.
    apply (sTUP [5] 64 103 1252 2 ((1, 1) :: repeat (1, 2) 2536 ++ (141868, 2) :: (1, 1) :: repeat (1, 2) 297773 ++ (1424871, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) 1); closearith.
  }
  (* step 77: hGRIND_even 49 *)
  apply (hsteps_trans _ (HB [5] 63 1 102 ((2, 2) :: (1250, 2) :: (1, 1) :: repeat (1, 2) 2536 ++ (141868, 2) :: (1, 1) :: repeat (1, 2) 297773 ++ (1424871, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) 1)).
  {
    apply (hGRIND_even 49 [5] 63 ((1250, 2) :: (1, 1) :: repeat (1, 2) 2536 ++ (141868, 2) :: (1, 1) :: repeat (1, 2) 297773 ++ (1424871, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) 1); closearith.
  }
  (* step 78: P TUP2_1 *)
  apply (hsteps_trans _ (HC [64; 5] 102 1 2 ((1248, 2) :: (1, 1) :: repeat (1, 2) 2536 ++ (141868, 2) :: (1, 1) :: repeat (1, 2) 297773 ++ (1424871, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) 1)).
  {
    replace ((1248, 2) :: (1, 1) :: repeat (1, 2) 2536 ++ (141868, 2) :: (1, 1) :: repeat (1, 2) 297773 ++ (1424871, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) with ((1250 - 2, 2) :: (1, 1) :: repeat (1, 2) 2536 ++ (141868, 2) :: (1, 1) :: repeat (1, 2) 297773 ++ (1424871, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) by sec_eq.
    apply (sTUP2_1 [5] 63 101 1250 ((1, 1) :: repeat (1, 2) 2536 ++ (141868, 2) :: (1, 1) :: repeat (1, 2) 297773 ++ (1424871, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) 1); closearith.
  }
  (* step 79: P TDN *)
  apply (hsteps_trans _ (HB [64; 5] 102 1 4 ((1248, 2) :: (1, 1) :: repeat (1, 2) 2536 ++ (141868, 2) :: (1, 1) :: repeat (1, 2) 297773 ++ (1424871, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) 1)).
  {
    apply (sTDN [64; 5] 102 ((1248, 2) :: (1, 1) :: repeat (1, 2) 2536 ++ (141868, 2) :: (1, 1) :: repeat (1, 2) 297773 ++ (1424871, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) 1).
  }
  (* step 80: sTUP *)
  apply (hsteps_trans _ (HC [64; 5] 102 3 2 ((1246, 2) :: (1, 1) :: repeat (1, 2) 2536 ++ (141868, 2) :: (1, 1) :: repeat (1, 2) 297773 ++ (1424871, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) 1)).
  {
    replace ((1246, 2) :: (1, 1) :: repeat (1, 2) 2536 ++ (141868, 2) :: (1, 1) :: repeat (1, 2) 297773 ++ (1424871, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) with ((1248 - 2, 2) :: (1, 1) :: repeat (1, 2) 2536 ++ (141868, 2) :: (1, 1) :: repeat (1, 2) 297773 ++ (1424871, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) by sec_eq.
    apply (sTUP [64; 5] 102 4 1248 2 ((1, 1) :: repeat (1, 2) 2536 ++ (141868, 2) :: (1, 1) :: repeat (1, 2) 297773 ++ (1424871, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) 1); closearith.
  }
  (* step 81: DIPGRIND 102 1042 *)
  apply (hsteps_trans _ (HC [64; 5] 0 3 2 (repeat (1, 2) 102 ++ (1042, 2) :: (1, 1) :: repeat (1, 2) 2536 ++ (141868, 2) :: (1, 1) :: repeat (1, 2) 297773 ++ (1424871, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) 1)).
  {
    apply (DIPGRIND 102 1042 [64; 5] ((1, 1) :: repeat (1, 2) 2536 ++ (141868, 2) :: (1, 1) :: repeat (1, 2) 297773 ++ (1424871, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) 1); closearith.
  }
  (* step 82: P PX2A *)
  apply (hsteps_trans _ (HC [] 4 62 2 ((1, 1) :: repeat (1, 2) 104 ++ (1042, 2) :: (1, 1) :: repeat (1, 2) 2536 ++ (141868, 2) :: (1, 1) :: repeat (1, 2) 297773 ++ (1424871, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) 1)).
  {
    exact (hsteps_step _ _ _ (hPX2A 61 4 [] (repeat (1, 2) 102 ++ (1042, 2) :: (1, 1) :: repeat (1, 2) 2536 ++ (141868, 2) :: (1, 1) :: repeat (1, 2) 297773 ++ (1424871, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) 1) (hsteps_refl _)).
  }
  (* step 83: P PUSH *)
  apply (hsteps_trans _ (HC [] 3 1 2 ((60, 2) :: (1, 1) :: repeat (1, 2) 104 ++ (1042, 2) :: (1, 1) :: repeat (1, 2) 2536 ++ (141868, 2) :: (1, 1) :: repeat (1, 2) 297773 ++ (1424871, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) 1)).
  {
    replace ((60, 2) :: (1, 1) :: repeat (1, 2) 104 ++ (1042, 2) :: (1, 1) :: repeat (1, 2) 2536 ++ (141868, 2) :: (1, 1) :: repeat (1, 2) 297773 ++ (1424871, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) with ((62 - 2, 2) :: (1, 1) :: repeat (1, 2) 104 ++ (1042, 2) :: (1, 1) :: repeat (1, 2) 2536 ++ (141868, 2) :: (1, 1) :: repeat (1, 2) 297773 ++ (1424871, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) by sec_eq.
    apply (sPUSH [] 3 62 ((1, 1) :: repeat (1, 2) 104 ++ (1042, 2) :: (1, 1) :: repeat (1, 2) 2536 ++ (141868, 2) :: (1, 1) :: repeat (1, 2) 297773 ++ (1424871, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) 1); closearith.
  }
  (* step 84: P TDN *)
  apply (hsteps_trans _ (HB [] 3 1 4 ((60, 2) :: (1, 1) :: repeat (1, 2) 104 ++ (1042, 2) :: (1, 1) :: repeat (1, 2) 2536 ++ (141868, 2) :: (1, 1) :: repeat (1, 2) 297773 ++ (1424871, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) 1)).
  {
    apply (sTDN [] 3 ((60, 2) :: (1, 1) :: repeat (1, 2) 104 ++ (1042, 2) :: (1, 1) :: repeat (1, 2) 2536 ++ (141868, 2) :: (1, 1) :: repeat (1, 2) 297773 ++ (1424871, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) 1).
  }
  (* step 85: sTUP *)
  apply (hsteps_trans _ (HC [] 3 3 2 ((58, 2) :: (1, 1) :: repeat (1, 2) 104 ++ (1042, 2) :: (1, 1) :: repeat (1, 2) 2536 ++ (141868, 2) :: (1, 1) :: repeat (1, 2) 297773 ++ (1424871, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) 1)).
  {
    replace ((58, 2) :: (1, 1) :: repeat (1, 2) 104 ++ (1042, 2) :: (1, 1) :: repeat (1, 2) 2536 ++ (141868, 2) :: (1, 1) :: repeat (1, 2) 297773 ++ (1424871, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) with ((60 - 2, 2) :: (1, 1) :: repeat (1, 2) 104 ++ (1042, 2) :: (1, 1) :: repeat (1, 2) 2536 ++ (141868, 2) :: (1, 1) :: repeat (1, 2) 297773 ++ (1424871, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) by sec_eq.
    apply (sTUP [] 3 4 60 2 ((1, 1) :: repeat (1, 2) 104 ++ (1042, 2) :: (1, 1) :: repeat (1, 2) 2536 ++ (141868, 2) :: (1, 1) :: repeat (1, 2) 297773 ++ (1424871, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) 1); closearith.
  }
  (* step 86: DIPGRIND 3 52 *)
  apply (hsteps_trans _ (HC [] 0 3 2 (repeat (1, 2) 3 ++ (52, 2) :: (1, 1) :: repeat (1, 2) 104 ++ (1042, 2) :: (1, 1) :: repeat (1, 2) 2536 ++ (141868, 2) :: (1, 1) :: repeat (1, 2) 297773 ++ (1424871, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) 1)).
  {
    apply (DIPGRIND 3 52 [] ((1, 1) :: repeat (1, 2) 104 ++ (1042, 2) :: (1, 1) :: repeat (1, 2) 2536 ++ (141868, 2) :: (1, 1) :: repeat (1, 2) 297773 ++ (1424871, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) 1); closearith.
  }
  (* step 87: P PUSHX *)
  apply (hsteps_trans _ (HB [] 1 1 7 (repeat (1, 2) 3 ++ (52, 2) :: (1, 1) :: repeat (1, 2) 104 ++ (1042, 2) :: (1, 1) :: repeat (1, 2) 2536 ++ (141868, 2) :: (1, 1) :: repeat (1, 2) 297773 ++ (1424871, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) 1)).
  {
    exact (hsteps_step _ _ _ (hPUSHX (repeat (1, 2) 3 ++ (52, 2) :: (1, 1) :: repeat (1, 2) 104 ++ (1042, 2) :: (1, 1) :: repeat (1, 2) 2536 ++ (141868, 2) :: (1, 1) :: repeat (1, 2) 297773 ++ (1424871, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) 1) (hsteps_refl _)).
  }
  (* step 88: M pop12 (3,) *)
  apply (hsteps_trans _ (HB [] 4 1 13 ((52, 2) :: (1, 1) :: repeat (1, 2) 104 ++ (1042, 2) :: (1, 1) :: repeat (1, 2) 2536 ++ (141868, 2) :: (1, 1) :: repeat (1, 2) 297773 ++ (1424871, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) 1)).
  {
    apply (pop12 3 [] 1 7 ((52, 2) :: (1, 1) :: repeat (1, 2) 104 ++ (1042, 2) :: (1, 1) :: repeat (1, 2) 2536 ++ (141868, 2) :: (1, 1) :: repeat (1, 2) 297773 ++ (1424871, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) 1); closearith.
  }
  (* step 89: sTUP *)
  apply (hsteps_trans _ (HC [] 4 12 2 ((50, 2) :: (1, 1) :: repeat (1, 2) 104 ++ (1042, 2) :: (1, 1) :: repeat (1, 2) 2536 ++ (141868, 2) :: (1, 1) :: repeat (1, 2) 297773 ++ (1424871, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) 1)).
  {
    replace ((50, 2) :: (1, 1) :: repeat (1, 2) 104 ++ (1042, 2) :: (1, 1) :: repeat (1, 2) 2536 ++ (141868, 2) :: (1, 1) :: repeat (1, 2) 297773 ++ (1424871, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) with ((52 - 2, 2) :: (1, 1) :: repeat (1, 2) 104 ++ (1042, 2) :: (1, 1) :: repeat (1, 2) 2536 ++ (141868, 2) :: (1, 1) :: repeat (1, 2) 297773 ++ (1424871, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) by sec_eq.
    apply (sTUP [] 4 13 52 2 ((1, 1) :: repeat (1, 2) 104 ++ (1042, 2) :: (1, 1) :: repeat (1, 2) 2536 ++ (141868, 2) :: (1, 1) :: repeat (1, 2) 297773 ++ (1424871, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) 1); closearith.
  }
  (* step 90: P PUSH *)
  apply (hsteps_trans _ (HC [] 3 1 2 ((10, 2) :: (50, 2) :: (1, 1) :: repeat (1, 2) 104 ++ (1042, 2) :: (1, 1) :: repeat (1, 2) 2536 ++ (141868, 2) :: (1, 1) :: repeat (1, 2) 297773 ++ (1424871, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) 1)).
  {
    replace ((10, 2) :: (50, 2) :: (1, 1) :: repeat (1, 2) 104 ++ (1042, 2) :: (1, 1) :: repeat (1, 2) 2536 ++ (141868, 2) :: (1, 1) :: repeat (1, 2) 297773 ++ (1424871, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) with ((12 - 2, 2) :: (50, 2) :: (1, 1) :: repeat (1, 2) 104 ++ (1042, 2) :: (1, 1) :: repeat (1, 2) 2536 ++ (141868, 2) :: (1, 1) :: repeat (1, 2) 297773 ++ (1424871, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) by sec_eq.
    apply (sPUSH [] 3 12 ((50, 2) :: (1, 1) :: repeat (1, 2) 104 ++ (1042, 2) :: (1, 1) :: repeat (1, 2) 2536 ++ (141868, 2) :: (1, 1) :: repeat (1, 2) 297773 ++ (1424871, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) 1); closearith.
  }
  (* step 91: P TDN *)
  apply (hsteps_trans _ (HB [] 3 1 4 ((10, 2) :: (50, 2) :: (1, 1) :: repeat (1, 2) 104 ++ (1042, 2) :: (1, 1) :: repeat (1, 2) 2536 ++ (141868, 2) :: (1, 1) :: repeat (1, 2) 297773 ++ (1424871, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) 1)).
  {
    apply (sTDN [] 3 ((10, 2) :: (50, 2) :: (1, 1) :: repeat (1, 2) 104 ++ (1042, 2) :: (1, 1) :: repeat (1, 2) 2536 ++ (141868, 2) :: (1, 1) :: repeat (1, 2) 297773 ++ (1424871, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) 1).
  }
  (* step 92: sTUP *)
  apply (hsteps_trans _ (HC [] 3 3 2 ((8, 2) :: (50, 2) :: (1, 1) :: repeat (1, 2) 104 ++ (1042, 2) :: (1, 1) :: repeat (1, 2) 2536 ++ (141868, 2) :: (1, 1) :: repeat (1, 2) 297773 ++ (1424871, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) 1)).
  {
    replace ((8, 2) :: (50, 2) :: (1, 1) :: repeat (1, 2) 104 ++ (1042, 2) :: (1, 1) :: repeat (1, 2) 2536 ++ (141868, 2) :: (1, 1) :: repeat (1, 2) 297773 ++ (1424871, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) with ((10 - 2, 2) :: (50, 2) :: (1, 1) :: repeat (1, 2) 104 ++ (1042, 2) :: (1, 1) :: repeat (1, 2) 2536 ++ (141868, 2) :: (1, 1) :: repeat (1, 2) 297773 ++ (1424871, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) by sec_eq.
    apply (sTUP [] 3 4 10 2 ((50, 2) :: (1, 1) :: repeat (1, 2) 104 ++ (1042, 2) :: (1, 1) :: repeat (1, 2) 2536 ++ (141868, 2) :: (1, 1) :: repeat (1, 2) 297773 ++ (1424871, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) 1); closearith.
  }
  (* step 93: DIPGRIND 3 2 *)
  apply (hsteps_trans _ (HC [] 0 3 2 (repeat (1, 2) 3 ++ (2, 2) :: (50, 2) :: (1, 1) :: repeat (1, 2) 104 ++ (1042, 2) :: (1, 1) :: repeat (1, 2) 2536 ++ (141868, 2) :: (1, 1) :: repeat (1, 2) 297773 ++ (1424871, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) 1)).
  {
    apply (DIPGRIND 3 2 [] ((50, 2) :: (1, 1) :: repeat (1, 2) 104 ++ (1042, 2) :: (1, 1) :: repeat (1, 2) 2536 ++ (141868, 2) :: (1, 1) :: repeat (1, 2) 297773 ++ (1424871, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) 1); closearith.
  }
  (* step 94: P PUSHX *)
  apply (hsteps_trans _ (HB [] 1 1 7 (repeat (1, 2) 3 ++ (2, 2) :: (50, 2) :: (1, 1) :: repeat (1, 2) 104 ++ (1042, 2) :: (1, 1) :: repeat (1, 2) 2536 ++ (141868, 2) :: (1, 1) :: repeat (1, 2) 297773 ++ (1424871, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) 1)).
  {
    exact (hsteps_step _ _ _ (hPUSHX (repeat (1, 2) 3 ++ (2, 2) :: (50, 2) :: (1, 1) :: repeat (1, 2) 104 ++ (1042, 2) :: (1, 1) :: repeat (1, 2) 2536 ++ (141868, 2) :: (1, 1) :: repeat (1, 2) 297773 ++ (1424871, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) 1) (hsteps_refl _)).
  }
  (* step 95: M pop12 (3,) *)
  apply (hsteps_trans _ (HB [] 4 1 13 ((2, 2) :: (50, 2) :: (1, 1) :: repeat (1, 2) 104 ++ (1042, 2) :: (1, 1) :: repeat (1, 2) 2536 ++ (141868, 2) :: (1, 1) :: repeat (1, 2) 297773 ++ (1424871, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) 1)).
  {
    apply (pop12 3 [] 1 7 ((2, 2) :: (50, 2) :: (1, 1) :: repeat (1, 2) 104 ++ (1042, 2) :: (1, 1) :: repeat (1, 2) 2536 ++ (141868, 2) :: (1, 1) :: repeat (1, 2) 297773 ++ (1424871, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) 1); closearith.
  }
  (* step 96: P TUP2_1 *)
  apply (hsteps_trans _ (HC [5] 13 1 2 ((48, 2) :: (1, 1) :: repeat (1, 2) 104 ++ (1042, 2) :: (1, 1) :: repeat (1, 2) 2536 ++ (141868, 2) :: (1, 1) :: repeat (1, 2) 297773 ++ (1424871, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) 1)).
  {
    replace ((48, 2) :: (1, 1) :: repeat (1, 2) 104 ++ (1042, 2) :: (1, 1) :: repeat (1, 2) 2536 ++ (141868, 2) :: (1, 1) :: repeat (1, 2) 297773 ++ (1424871, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) with ((50 - 2, 2) :: (1, 1) :: repeat (1, 2) 104 ++ (1042, 2) :: (1, 1) :: repeat (1, 2) 2536 ++ (141868, 2) :: (1, 1) :: repeat (1, 2) 297773 ++ (1424871, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) by sec_eq.
    apply (sTUP2_1 [] 4 12 50 ((1, 1) :: repeat (1, 2) 104 ++ (1042, 2) :: (1, 1) :: repeat (1, 2) 2536 ++ (141868, 2) :: (1, 1) :: repeat (1, 2) 297773 ++ (1424871, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) 1); closearith.
  }
  (* step 97: P TDN *)
  apply (hsteps_trans _ (HB [5] 13 1 4 ((48, 2) :: (1, 1) :: repeat (1, 2) 104 ++ (1042, 2) :: (1, 1) :: repeat (1, 2) 2536 ++ (141868, 2) :: (1, 1) :: repeat (1, 2) 297773 ++ (1424871, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) 1)).
  {
    apply (sTDN [5] 13 ((48, 2) :: (1, 1) :: repeat (1, 2) 104 ++ (1042, 2) :: (1, 1) :: repeat (1, 2) 2536 ++ (141868, 2) :: (1, 1) :: repeat (1, 2) 297773 ++ (1424871, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) 1).
  }
  (* step 98: sTUP *)
  apply (hsteps_trans _ (HC [5] 13 3 2 ((46, 2) :: (1, 1) :: repeat (1, 2) 104 ++ (1042, 2) :: (1, 1) :: repeat (1, 2) 2536 ++ (141868, 2) :: (1, 1) :: repeat (1, 2) 297773 ++ (1424871, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) 1)).
  {
    replace ((46, 2) :: (1, 1) :: repeat (1, 2) 104 ++ (1042, 2) :: (1, 1) :: repeat (1, 2) 2536 ++ (141868, 2) :: (1, 1) :: repeat (1, 2) 297773 ++ (1424871, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) with ((48 - 2, 2) :: (1, 1) :: repeat (1, 2) 104 ++ (1042, 2) :: (1, 1) :: repeat (1, 2) 2536 ++ (141868, 2) :: (1, 1) :: repeat (1, 2) 297773 ++ (1424871, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) by sec_eq.
    apply (sTUP [5] 13 4 48 2 ((1, 1) :: repeat (1, 2) 104 ++ (1042, 2) :: (1, 1) :: repeat (1, 2) 2536 ++ (141868, 2) :: (1, 1) :: repeat (1, 2) 297773 ++ (1424871, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) 1); closearith.
  }
  (* step 99: DIPGRIND 13 20 *)
  apply (hsteps_trans _ (HC [5] 0 3 2 (repeat (1, 2) 13 ++ (20, 2) :: (1, 1) :: repeat (1, 2) 104 ++ (1042, 2) :: (1, 1) :: repeat (1, 2) 2536 ++ (141868, 2) :: (1, 1) :: repeat (1, 2) 297773 ++ (1424871, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) 1)).
  {
    apply (DIPGRIND 13 20 [5] ((1, 1) :: repeat (1, 2) 104 ++ (1042, 2) :: (1, 1) :: repeat (1, 2) 2536 ++ (141868, 2) :: (1, 1) :: repeat (1, 2) 297773 ++ (1424871, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) 1); closearith.
  }
  (* step 100: P PX2Bgen *)
  apply (hsteps_trans _ (HB [0] 3 1 2 (repeat (1, 2) 1 ++ (1, 1) :: repeat (1, 2) 15 ++ (20, 2) :: (1, 1) :: repeat (1, 2) 104 ++ (1042, 2) :: (1, 1) :: repeat (1, 2) 2536 ++ (141868, 2) :: (1, 1) :: repeat (1, 2) 297773 ++ (1424871, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) 1)).
  {
    exact (hsteps_step _ _ _ (hPX2Bgen 0 (repeat (1, 2) 13 ++ (20, 2) :: (1, 1) :: repeat (1, 2) 104 ++ (1042, 2) :: (1, 1) :: repeat (1, 2) 2536 ++ (141868, 2) :: (1, 1) :: repeat (1, 2) 297773 ++ (1424871, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) 1) (hsteps_refl _)).
  }
  (* step 101: M pop12 (1,) *)
  apply (hsteps_trans _ (HB [0] 4 1 4 ((1, 1) :: repeat (1, 2) 15 ++ (20, 2) :: (1, 1) :: repeat (1, 2) 104 ++ (1042, 2) :: (1, 1) :: repeat (1, 2) 2536 ++ (141868, 2) :: (1, 1) :: repeat (1, 2) 297773 ++ (1424871, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) 1)).
  {
    apply (pop12 1 [0] 3 2 ((1, 1) :: repeat (1, 2) 15 ++ (20, 2) :: (1, 1) :: repeat (1, 2) 104 ++ (1042, 2) :: (1, 1) :: repeat (1, 2) 2536 ++ (141868, 2) :: (1, 1) :: repeat (1, 2) 297773 ++ (1424871, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) 1); closearith.
  }
  (* step 102: P POP *)
  apply (hsteps_trans _ (HB [0] 5 1 5 (repeat (1, 2) 15 ++ (20, 2) :: (1, 1) :: repeat (1, 2) 104 ++ (1042, 2) :: (1, 1) :: repeat (1, 2) 2536 ++ (141868, 2) :: (1, 1) :: repeat (1, 2) 297773 ++ (1424871, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) 1)).
  {
    apply (sPOP1 [0] 4 4 (repeat (1, 2) 15 ++ (20, 2) :: (1, 1) :: repeat (1, 2) 104 ++ (1042, 2) :: (1, 1) :: repeat (1, 2) 2536 ++ (141868, 2) :: (1, 1) :: repeat (1, 2) 297773 ++ (1424871, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) 1); closearith.
  }
  (* step 103: M pop12 (15,) *)
  apply (hsteps_trans _ (HB [0] 20 1 35 ((20, 2) :: (1, 1) :: repeat (1, 2) 104 ++ (1042, 2) :: (1, 1) :: repeat (1, 2) 2536 ++ (141868, 2) :: (1, 1) :: repeat (1, 2) 297773 ++ (1424871, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) 1)).
  {
    apply (pop12 15 [0] 5 5 ((20, 2) :: (1, 1) :: repeat (1, 2) 104 ++ (1042, 2) :: (1, 1) :: repeat (1, 2) 2536 ++ (141868, 2) :: (1, 1) :: repeat (1, 2) 297773 ++ (1424871, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) 1); closearith.
  }
  (* step 104: sTUP *)
  apply (hsteps_trans _ (HC [0] 20 34 2 ((18, 2) :: (1, 1) :: repeat (1, 2) 104 ++ (1042, 2) :: (1, 1) :: repeat (1, 2) 2536 ++ (141868, 2) :: (1, 1) :: repeat (1, 2) 297773 ++ (1424871, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) 1)).
  {
    replace ((18, 2) :: (1, 1) :: repeat (1, 2) 104 ++ (1042, 2) :: (1, 1) :: repeat (1, 2) 2536 ++ (141868, 2) :: (1, 1) :: repeat (1, 2) 297773 ++ (1424871, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) with ((20 - 2, 2) :: (1, 1) :: repeat (1, 2) 104 ++ (1042, 2) :: (1, 1) :: repeat (1, 2) 2536 ++ (141868, 2) :: (1, 1) :: repeat (1, 2) 297773 ++ (1424871, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) by sec_eq.
    apply (sTUP [0] 20 35 20 2 ((1, 1) :: repeat (1, 2) 104 ++ (1042, 2) :: (1, 1) :: repeat (1, 2) 2536 ++ (141868, 2) :: (1, 1) :: repeat (1, 2) 297773 ++ (1424871, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) 1); closearith.
  }
  (* step 105: hGRIND_even 15 *)
  apply (hsteps_trans _ (HB [0] 19 1 34 ((2, 2) :: (18, 2) :: (1, 1) :: repeat (1, 2) 104 ++ (1042, 2) :: (1, 1) :: repeat (1, 2) 2536 ++ (141868, 2) :: (1, 1) :: repeat (1, 2) 297773 ++ (1424871, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) 1)).
  {
    apply (hGRIND_even 15 [0] 19 ((18, 2) :: (1, 1) :: repeat (1, 2) 104 ++ (1042, 2) :: (1, 1) :: repeat (1, 2) 2536 ++ (141868, 2) :: (1, 1) :: repeat (1, 2) 297773 ++ (1424871, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) 1); closearith.
  }
  (* step 106: P TUP2_1 *)
  apply (hsteps_trans _ (HC [20; 0] 34 1 2 ((16, 2) :: (1, 1) :: repeat (1, 2) 104 ++ (1042, 2) :: (1, 1) :: repeat (1, 2) 2536 ++ (141868, 2) :: (1, 1) :: repeat (1, 2) 297773 ++ (1424871, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) 1)).
  {
    replace ((16, 2) :: (1, 1) :: repeat (1, 2) 104 ++ (1042, 2) :: (1, 1) :: repeat (1, 2) 2536 ++ (141868, 2) :: (1, 1) :: repeat (1, 2) 297773 ++ (1424871, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) with ((18 - 2, 2) :: (1, 1) :: repeat (1, 2) 104 ++ (1042, 2) :: (1, 1) :: repeat (1, 2) 2536 ++ (141868, 2) :: (1, 1) :: repeat (1, 2) 297773 ++ (1424871, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) by sec_eq.
    apply (sTUP2_1 [0] 19 33 18 ((1, 1) :: repeat (1, 2) 104 ++ (1042, 2) :: (1, 1) :: repeat (1, 2) 2536 ++ (141868, 2) :: (1, 1) :: repeat (1, 2) 297773 ++ (1424871, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) 1); closearith.
  }
  (* step 107: P TDN *)
  apply (hsteps_trans _ (HB [20; 0] 34 1 4 ((16, 2) :: (1, 1) :: repeat (1, 2) 104 ++ (1042, 2) :: (1, 1) :: repeat (1, 2) 2536 ++ (141868, 2) :: (1, 1) :: repeat (1, 2) 297773 ++ (1424871, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) 1)).
  {
    apply (sTDN [20; 0] 34 ((16, 2) :: (1, 1) :: repeat (1, 2) 104 ++ (1042, 2) :: (1, 1) :: repeat (1, 2) 2536 ++ (141868, 2) :: (1, 1) :: repeat (1, 2) 297773 ++ (1424871, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) 1).
  }
  (* step 108: sTUP *)
  apply (hsteps_trans _ (HC [20; 0] 34 3 2 ((14, 2) :: (1, 1) :: repeat (1, 2) 104 ++ (1042, 2) :: (1, 1) :: repeat (1, 2) 2536 ++ (141868, 2) :: (1, 1) :: repeat (1, 2) 297773 ++ (1424871, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) 1)).
  {
    replace ((14, 2) :: (1, 1) :: repeat (1, 2) 104 ++ (1042, 2) :: (1, 1) :: repeat (1, 2) 2536 ++ (141868, 2) :: (1, 1) :: repeat (1, 2) 297773 ++ (1424871, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) with ((16 - 2, 2) :: (1, 1) :: repeat (1, 2) 104 ++ (1042, 2) :: (1, 1) :: repeat (1, 2) 2536 ++ (141868, 2) :: (1, 1) :: repeat (1, 2) 297773 ++ (1424871, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) by sec_eq.
    apply (sTUP [20; 0] 34 4 16 2 ((1, 1) :: repeat (1, 2) 104 ++ (1042, 2) :: (1, 1) :: repeat (1, 2) 2536 ++ (141868, 2) :: (1, 1) :: repeat (1, 2) 297773 ++ (1424871, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) 1); closearith.
  }
  (* step 109: CLEANG_even 6 *)
  apply (hsteps_trans _ (HB [20; 0] 34 1 18 ((2, 2) :: (1, 1) :: repeat (1, 2) 104 ++ (1042, 2) :: (1, 1) :: repeat (1, 2) 2536 ++ (141868, 2) :: (1, 1) :: repeat (1, 2) 297773 ++ (1424871, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) 1)).
  {
    apply (CLEANG_even 6 [20; 0] 34 ((1, 1) :: repeat (1, 2) 104 ++ (1042, 2) :: (1, 1) :: repeat (1, 2) 2536 ++ (141868, 2) :: (1, 1) :: repeat (1, 2) 297773 ++ (1424871, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) 1); closearith.
  }
  (* step 110: P TRANS2_1 *)
  apply (hsteps_trans _ (HB [35; 20; 0] 19 1 3 (repeat (1, 2) 104 ++ (1042, 2) :: (1, 1) :: repeat (1, 2) 2536 ++ (141868, 2) :: (1, 1) :: repeat (1, 2) 297773 ++ (1424871, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) 1)).
  {
    apply (sTRANS2_1 [20; 0] 34 17 1 (repeat (1, 2) 104 ++ (1042, 2) :: (1, 1) :: repeat (1, 2) 2536 ++ (141868, 2) :: (1, 1) :: repeat (1, 2) 297773 ++ (1424871, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) 1); closearith.
  }
  (* step 111: M pop12 (104,) *)
  apply (hsteps_trans _ (HB [35; 20; 0] 123 1 211 ((1042, 2) :: (1, 1) :: repeat (1, 2) 2536 ++ (141868, 2) :: (1, 1) :: repeat (1, 2) 297773 ++ (1424871, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) 1)).
  {
    apply (pop12 104 [35; 20; 0] 19 3 ((1042, 2) :: (1, 1) :: repeat (1, 2) 2536 ++ (141868, 2) :: (1, 1) :: repeat (1, 2) 297773 ++ (1424871, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) 1); closearith.
  }
  (* step 112: sTUP *)
  replace ((1040, 2) :: (1, 1) :: repeat (1, 2) 2536 ++ (141868, 2) :: (1, 1) :: repeat (1, 2) 297773 ++ (1424871, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) with ((1042 - 2, 2) :: (1, 1) :: repeat (1, 2) 2536 ++ (141868, 2) :: (1, 1) :: repeat (1, 2) 297773 ++ (1424871, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) by sec_eq.
  apply (sTUP [35; 20; 0] 123 211 1042 2 ((1, 1) :: repeat (1, 2) 2536 ++ (141868, 2) :: (1, 1) :: repeat (1, 2) 297773 ++ (1424871, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) 1); closearith.
Qed.

(* CASCADE56c: steps 113-168 of the CASCADE56 chain. *)
Lemma CASCADE56c : forall w,
  hsteps (HC [35; 20; 0] 123 210 2 ((1040, 2) :: (1, 1) :: repeat (1, 2) 2536 ++ (141868, 2) :: (1, 1) :: repeat (1, 2) 297773 ++ (1424871, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) 1)
         (HC [286; 40; 14; 5] 0 3 2 (repeat (1, 2) 475 ++ (2195, 2) :: (1, 1) :: repeat (1, 2) 5076 ++ (131714, 2) :: (1, 1) :: repeat (1, 2) 297773 ++ (1424871, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) 1).
Proof.
  intro w.
  (* step 113: hGRIND_even 103 *)
  apply (hsteps_trans _ (HB [35; 20; 0] 122 1 210 ((2, 2) :: (1040, 2) :: (1, 1) :: repeat (1, 2) 2536 ++ (141868, 2) :: (1, 1) :: repeat (1, 2) 297773 ++ (1424871, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) 1)).
  {
    apply (hGRIND_even 103 [35; 20; 0] 122 ((1040, 2) :: (1, 1) :: repeat (1, 2) 2536 ++ (141868, 2) :: (1, 1) :: repeat (1, 2) 297773 ++ (1424871, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) 1); closearith.
  }
  (* step 114: P TUP2_1 *)
  apply (hsteps_trans _ (HC [123; 35; 20; 0] 210 1 2 ((1038, 2) :: (1, 1) :: repeat (1, 2) 2536 ++ (141868, 2) :: (1, 1) :: repeat (1, 2) 297773 ++ (1424871, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) 1)).
  {
    replace ((1038, 2) :: (1, 1) :: repeat (1, 2) 2536 ++ (141868, 2) :: (1, 1) :: repeat (1, 2) 297773 ++ (1424871, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) with ((1040 - 2, 2) :: (1, 1) :: repeat (1, 2) 2536 ++ (141868, 2) :: (1, 1) :: repeat (1, 2) 297773 ++ (1424871, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) by sec_eq.
    apply (sTUP2_1 [35; 20; 0] 122 209 1040 ((1, 1) :: repeat (1, 2) 2536 ++ (141868, 2) :: (1, 1) :: repeat (1, 2) 297773 ++ (1424871, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) 1); closearith.
  }
  (* step 115: P TDN *)
  apply (hsteps_trans _ (HB [123; 35; 20; 0] 210 1 4 ((1038, 2) :: (1, 1) :: repeat (1, 2) 2536 ++ (141868, 2) :: (1, 1) :: repeat (1, 2) 297773 ++ (1424871, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) 1)).
  {
    apply (sTDN [123; 35; 20; 0] 210 ((1038, 2) :: (1, 1) :: repeat (1, 2) 2536 ++ (141868, 2) :: (1, 1) :: repeat (1, 2) 297773 ++ (1424871, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) 1).
  }
  (* step 116: sTUP *)
  apply (hsteps_trans _ (HC [123; 35; 20; 0] 210 3 2 ((1036, 2) :: (1, 1) :: repeat (1, 2) 2536 ++ (141868, 2) :: (1, 1) :: repeat (1, 2) 297773 ++ (1424871, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) 1)).
  {
    replace ((1036, 2) :: (1, 1) :: repeat (1, 2) 2536 ++ (141868, 2) :: (1, 1) :: repeat (1, 2) 297773 ++ (1424871, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) with ((1038 - 2, 2) :: (1, 1) :: repeat (1, 2) 2536 ++ (141868, 2) :: (1, 1) :: repeat (1, 2) 297773 ++ (1424871, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) by sec_eq.
    apply (sTUP [123; 35; 20; 0] 210 4 1038 2 ((1, 1) :: repeat (1, 2) 2536 ++ (141868, 2) :: (1, 1) :: repeat (1, 2) 297773 ++ (1424871, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) 1); closearith.
  }
  (* step 117: DIPGRIND 210 616 *)
  apply (hsteps_trans _ (HC [123; 35; 20; 0] 0 3 2 (repeat (1, 2) 210 ++ (616, 2) :: (1, 1) :: repeat (1, 2) 2536 ++ (141868, 2) :: (1, 1) :: repeat (1, 2) 297773 ++ (1424871, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) 1)).
  {
    apply (DIPGRIND 210 616 [123; 35; 20; 0] ((1, 1) :: repeat (1, 2) 2536 ++ (141868, 2) :: (1, 1) :: repeat (1, 2) 297773 ++ (1424871, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) 1); closearith.
  }
  (* step 118: P PX2A *)
  apply (hsteps_trans _ (HC [20; 0] 34 121 2 ((1, 1) :: repeat (1, 2) 212 ++ (616, 2) :: (1, 1) :: repeat (1, 2) 2536 ++ (141868, 2) :: (1, 1) :: repeat (1, 2) 297773 ++ (1424871, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) 1)).
  {
    exact (hsteps_step _ _ _ (hPX2A 120 34 [20; 0] (repeat (1, 2) 210 ++ (616, 2) :: (1, 1) :: repeat (1, 2) 2536 ++ (141868, 2) :: (1, 1) :: repeat (1, 2) 297773 ++ (1424871, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) 1) (hsteps_refl _)).
  }
  (* step 119: P PUSH *)
  apply (hsteps_trans _ (HC [20; 0] 33 1 2 ((119, 2) :: (1, 1) :: repeat (1, 2) 212 ++ (616, 2) :: (1, 1) :: repeat (1, 2) 2536 ++ (141868, 2) :: (1, 1) :: repeat (1, 2) 297773 ++ (1424871, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) 1)).
  {
    replace ((119, 2) :: (1, 1) :: repeat (1, 2) 212 ++ (616, 2) :: (1, 1) :: repeat (1, 2) 2536 ++ (141868, 2) :: (1, 1) :: repeat (1, 2) 297773 ++ (1424871, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) with ((121 - 2, 2) :: (1, 1) :: repeat (1, 2) 212 ++ (616, 2) :: (1, 1) :: repeat (1, 2) 2536 ++ (141868, 2) :: (1, 1) :: repeat (1, 2) 297773 ++ (1424871, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) by sec_eq.
    apply (sPUSH [20; 0] 33 121 ((1, 1) :: repeat (1, 2) 212 ++ (616, 2) :: (1, 1) :: repeat (1, 2) 2536 ++ (141868, 2) :: (1, 1) :: repeat (1, 2) 297773 ++ (1424871, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) 1); closearith.
  }
  (* step 120: P TDN *)
  apply (hsteps_trans _ (HB [20; 0] 33 1 4 ((119, 2) :: (1, 1) :: repeat (1, 2) 212 ++ (616, 2) :: (1, 1) :: repeat (1, 2) 2536 ++ (141868, 2) :: (1, 1) :: repeat (1, 2) 297773 ++ (1424871, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) 1)).
  {
    apply (sTDN [20; 0] 33 ((119, 2) :: (1, 1) :: repeat (1, 2) 212 ++ (616, 2) :: (1, 1) :: repeat (1, 2) 2536 ++ (141868, 2) :: (1, 1) :: repeat (1, 2) 297773 ++ (1424871, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) 1).
  }
  (* step 121: sTUP *)
  apply (hsteps_trans _ (HC [20; 0] 33 3 2 ((117, 2) :: (1, 1) :: repeat (1, 2) 212 ++ (616, 2) :: (1, 1) :: repeat (1, 2) 2536 ++ (141868, 2) :: (1, 1) :: repeat (1, 2) 297773 ++ (1424871, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) 1)).
  {
    replace ((117, 2) :: (1, 1) :: repeat (1, 2) 212 ++ (616, 2) :: (1, 1) :: repeat (1, 2) 2536 ++ (141868, 2) :: (1, 1) :: repeat (1, 2) 297773 ++ (1424871, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) with ((119 - 2, 2) :: (1, 1) :: repeat (1, 2) 212 ++ (616, 2) :: (1, 1) :: repeat (1, 2) 2536 ++ (141868, 2) :: (1, 1) :: repeat (1, 2) 297773 ++ (1424871, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) by sec_eq.
    apply (sTUP [20; 0] 33 4 119 2 ((1, 1) :: repeat (1, 2) 212 ++ (616, 2) :: (1, 1) :: repeat (1, 2) 2536 ++ (141868, 2) :: (1, 1) :: repeat (1, 2) 297773 ++ (1424871, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) 1); closearith.
  }
  (* step 122: DIPGRIND 33 51 *)
  apply (hsteps_trans _ (HC [20; 0] 0 3 2 (repeat (1, 2) 33 ++ (51, 2) :: (1, 1) :: repeat (1, 2) 212 ++ (616, 2) :: (1, 1) :: repeat (1, 2) 2536 ++ (141868, 2) :: (1, 1) :: repeat (1, 2) 297773 ++ (1424871, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) 1)).
  {
    apply (DIPGRIND 33 51 [20; 0] ((1, 1) :: repeat (1, 2) 212 ++ (616, 2) :: (1, 1) :: repeat (1, 2) 2536 ++ (141868, 2) :: (1, 1) :: repeat (1, 2) 297773 ++ (1424871, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) 1); closearith.
  }
  (* step 123: P PX2A0 *)
  apply (hsteps_trans _ (HB [0] 3 1 2 ((16, 2) :: (1, 1) :: repeat (1, 2) 35 ++ (51, 2) :: (1, 1) :: repeat (1, 2) 212 ++ (616, 2) :: (1, 1) :: repeat (1, 2) 2536 ++ (141868, 2) :: (1, 1) :: repeat (1, 2) 297773 ++ (1424871, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) 1)).
  {
    exact (hsteps_step _ _ _ (hPX2A0 15 (repeat (1, 2) 33 ++ (51, 2) :: (1, 1) :: repeat (1, 2) 212 ++ (616, 2) :: (1, 1) :: repeat (1, 2) 2536 ++ (141868, 2) :: (1, 1) :: repeat (1, 2) 297773 ++ (1424871, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) 1) (hsteps_refl _)).
  }
  (* step 124: sTUP *)
  apply (hsteps_trans _ (HC [0] 3 1 2 ((14, 2) :: (1, 1) :: repeat (1, 2) 35 ++ (51, 2) :: (1, 1) :: repeat (1, 2) 212 ++ (616, 2) :: (1, 1) :: repeat (1, 2) 2536 ++ (141868, 2) :: (1, 1) :: repeat (1, 2) 297773 ++ (1424871, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) 1)).
  {
    replace ((14, 2) :: (1, 1) :: repeat (1, 2) 35 ++ (51, 2) :: (1, 1) :: repeat (1, 2) 212 ++ (616, 2) :: (1, 1) :: repeat (1, 2) 2536 ++ (141868, 2) :: (1, 1) :: repeat (1, 2) 297773 ++ (1424871, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) with ((16 - 2, 2) :: (1, 1) :: repeat (1, 2) 35 ++ (51, 2) :: (1, 1) :: repeat (1, 2) 212 ++ (616, 2) :: (1, 1) :: repeat (1, 2) 2536 ++ (141868, 2) :: (1, 1) :: repeat (1, 2) 297773 ++ (1424871, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) by sec_eq.
    apply (sTUP [0] 3 2 16 2 ((1, 1) :: repeat (1, 2) 35 ++ (51, 2) :: (1, 1) :: repeat (1, 2) 212 ++ (616, 2) :: (1, 1) :: repeat (1, 2) 2536 ++ (141868, 2) :: (1, 1) :: repeat (1, 2) 297773 ++ (1424871, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) 1); closearith.
  }
  (* step 125: P TDN *)
  apply (hsteps_trans _ (HB [0] 3 1 4 ((14, 2) :: (1, 1) :: repeat (1, 2) 35 ++ (51, 2) :: (1, 1) :: repeat (1, 2) 212 ++ (616, 2) :: (1, 1) :: repeat (1, 2) 2536 ++ (141868, 2) :: (1, 1) :: repeat (1, 2) 297773 ++ (1424871, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) 1)).
  {
    apply (sTDN [0] 3 ((14, 2) :: (1, 1) :: repeat (1, 2) 35 ++ (51, 2) :: (1, 1) :: repeat (1, 2) 212 ++ (616, 2) :: (1, 1) :: repeat (1, 2) 2536 ++ (141868, 2) :: (1, 1) :: repeat (1, 2) 297773 ++ (1424871, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) 1).
  }
  (* step 126: sTUP *)
  apply (hsteps_trans _ (HC [0] 3 3 2 ((12, 2) :: (1, 1) :: repeat (1, 2) 35 ++ (51, 2) :: (1, 1) :: repeat (1, 2) 212 ++ (616, 2) :: (1, 1) :: repeat (1, 2) 2536 ++ (141868, 2) :: (1, 1) :: repeat (1, 2) 297773 ++ (1424871, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) 1)).
  {
    replace ((12, 2) :: (1, 1) :: repeat (1, 2) 35 ++ (51, 2) :: (1, 1) :: repeat (1, 2) 212 ++ (616, 2) :: (1, 1) :: repeat (1, 2) 2536 ++ (141868, 2) :: (1, 1) :: repeat (1, 2) 297773 ++ (1424871, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) with ((14 - 2, 2) :: (1, 1) :: repeat (1, 2) 35 ++ (51, 2) :: (1, 1) :: repeat (1, 2) 212 ++ (616, 2) :: (1, 1) :: repeat (1, 2) 2536 ++ (141868, 2) :: (1, 1) :: repeat (1, 2) 297773 ++ (1424871, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) by sec_eq.
    apply (sTUP [0] 3 4 14 2 ((1, 1) :: repeat (1, 2) 35 ++ (51, 2) :: (1, 1) :: repeat (1, 2) 212 ++ (616, 2) :: (1, 1) :: repeat (1, 2) 2536 ++ (141868, 2) :: (1, 1) :: repeat (1, 2) 297773 ++ (1424871, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) 1); closearith.
  }
  (* step 127: DIPGRIND 3 6 *)
  apply (hsteps_trans _ (HC [0] 0 3 2 (repeat (1, 2) 3 ++ (6, 2) :: (1, 1) :: repeat (1, 2) 35 ++ (51, 2) :: (1, 1) :: repeat (1, 2) 212 ++ (616, 2) :: (1, 1) :: repeat (1, 2) 2536 ++ (141868, 2) :: (1, 1) :: repeat (1, 2) 297773 ++ (1424871, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) 1)).
  {
    apply (DIPGRIND 3 6 [0] ((1, 1) :: repeat (1, 2) 35 ++ (51, 2) :: (1, 1) :: repeat (1, 2) 212 ++ (616, 2) :: (1, 1) :: repeat (1, 2) 2536 ++ (141868, 2) :: (1, 1) :: repeat (1, 2) 297773 ++ (1424871, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) 1); closearith.
  }
  (* step 128: P PX2B0 *)
  apply (hsteps_trans _ (HB [] 0 1 5 (repeat (1, 2) 4 ++ (6, 2) :: (1, 1) :: repeat (1, 2) 35 ++ (51, 2) :: (1, 1) :: repeat (1, 2) 212 ++ (616, 2) :: (1, 1) :: repeat (1, 2) 2536 ++ (141868, 2) :: (1, 1) :: repeat (1, 2) 297773 ++ (1424871, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) 1)).
  {
    exact (hsteps_step _ _ _ (hPX2B0 (repeat (1, 2) 3 ++ (6, 2) :: (1, 1) :: repeat (1, 2) 35 ++ (51, 2) :: (1, 1) :: repeat (1, 2) 212 ++ (616, 2) :: (1, 1) :: repeat (1, 2) 2536 ++ (141868, 2) :: (1, 1) :: repeat (1, 2) 297773 ++ (1424871, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) 1) (hsteps_refl _)).
  }
  (* step 129: M pop12 (4,) *)
  apply (hsteps_trans _ (HB [] 4 1 13 ((6, 2) :: (1, 1) :: repeat (1, 2) 35 ++ (51, 2) :: (1, 1) :: repeat (1, 2) 212 ++ (616, 2) :: (1, 1) :: repeat (1, 2) 2536 ++ (141868, 2) :: (1, 1) :: repeat (1, 2) 297773 ++ (1424871, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) 1)).
  {
    apply (pop12 4 [] 0 5 ((6, 2) :: (1, 1) :: repeat (1, 2) 35 ++ (51, 2) :: (1, 1) :: repeat (1, 2) 212 ++ (616, 2) :: (1, 1) :: repeat (1, 2) 2536 ++ (141868, 2) :: (1, 1) :: repeat (1, 2) 297773 ++ (1424871, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) 1); closearith.
  }
  (* step 130: sTUP *)
  apply (hsteps_trans _ (HC [] 4 12 2 ((4, 2) :: (1, 1) :: repeat (1, 2) 35 ++ (51, 2) :: (1, 1) :: repeat (1, 2) 212 ++ (616, 2) :: (1, 1) :: repeat (1, 2) 2536 ++ (141868, 2) :: (1, 1) :: repeat (1, 2) 297773 ++ (1424871, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) 1)).
  {
    replace ((4, 2) :: (1, 1) :: repeat (1, 2) 35 ++ (51, 2) :: (1, 1) :: repeat (1, 2) 212 ++ (616, 2) :: (1, 1) :: repeat (1, 2) 2536 ++ (141868, 2) :: (1, 1) :: repeat (1, 2) 297773 ++ (1424871, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) with ((6 - 2, 2) :: (1, 1) :: repeat (1, 2) 35 ++ (51, 2) :: (1, 1) :: repeat (1, 2) 212 ++ (616, 2) :: (1, 1) :: repeat (1, 2) 2536 ++ (141868, 2) :: (1, 1) :: repeat (1, 2) 297773 ++ (1424871, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) by sec_eq.
    apply (sTUP [] 4 13 6 2 ((1, 1) :: repeat (1, 2) 35 ++ (51, 2) :: (1, 1) :: repeat (1, 2) 212 ++ (616, 2) :: (1, 1) :: repeat (1, 2) 2536 ++ (141868, 2) :: (1, 1) :: repeat (1, 2) 297773 ++ (1424871, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) 1); closearith.
  }
  (* step 131: P PUSH *)
  apply (hsteps_trans _ (HC [] 3 1 2 ((10, 2) :: (4, 2) :: (1, 1) :: repeat (1, 2) 35 ++ (51, 2) :: (1, 1) :: repeat (1, 2) 212 ++ (616, 2) :: (1, 1) :: repeat (1, 2) 2536 ++ (141868, 2) :: (1, 1) :: repeat (1, 2) 297773 ++ (1424871, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) 1)).
  {
    replace ((10, 2) :: (4, 2) :: (1, 1) :: repeat (1, 2) 35 ++ (51, 2) :: (1, 1) :: repeat (1, 2) 212 ++ (616, 2) :: (1, 1) :: repeat (1, 2) 2536 ++ (141868, 2) :: (1, 1) :: repeat (1, 2) 297773 ++ (1424871, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) with ((12 - 2, 2) :: (4, 2) :: (1, 1) :: repeat (1, 2) 35 ++ (51, 2) :: (1, 1) :: repeat (1, 2) 212 ++ (616, 2) :: (1, 1) :: repeat (1, 2) 2536 ++ (141868, 2) :: (1, 1) :: repeat (1, 2) 297773 ++ (1424871, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) by sec_eq.
    apply (sPUSH [] 3 12 ((4, 2) :: (1, 1) :: repeat (1, 2) 35 ++ (51, 2) :: (1, 1) :: repeat (1, 2) 212 ++ (616, 2) :: (1, 1) :: repeat (1, 2) 2536 ++ (141868, 2) :: (1, 1) :: repeat (1, 2) 297773 ++ (1424871, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) 1); closearith.
  }
  (* step 132: P TDN *)
  apply (hsteps_trans _ (HB [] 3 1 4 ((10, 2) :: (4, 2) :: (1, 1) :: repeat (1, 2) 35 ++ (51, 2) :: (1, 1) :: repeat (1, 2) 212 ++ (616, 2) :: (1, 1) :: repeat (1, 2) 2536 ++ (141868, 2) :: (1, 1) :: repeat (1, 2) 297773 ++ (1424871, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) 1)).
  {
    apply (sTDN [] 3 ((10, 2) :: (4, 2) :: (1, 1) :: repeat (1, 2) 35 ++ (51, 2) :: (1, 1) :: repeat (1, 2) 212 ++ (616, 2) :: (1, 1) :: repeat (1, 2) 2536 ++ (141868, 2) :: (1, 1) :: repeat (1, 2) 297773 ++ (1424871, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) 1).
  }
  (* step 133: sTUP *)
  apply (hsteps_trans _ (HC [] 3 3 2 ((8, 2) :: (4, 2) :: (1, 1) :: repeat (1, 2) 35 ++ (51, 2) :: (1, 1) :: repeat (1, 2) 212 ++ (616, 2) :: (1, 1) :: repeat (1, 2) 2536 ++ (141868, 2) :: (1, 1) :: repeat (1, 2) 297773 ++ (1424871, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) 1)).
  {
    replace ((8, 2) :: (4, 2) :: (1, 1) :: repeat (1, 2) 35 ++ (51, 2) :: (1, 1) :: repeat (1, 2) 212 ++ (616, 2) :: (1, 1) :: repeat (1, 2) 2536 ++ (141868, 2) :: (1, 1) :: repeat (1, 2) 297773 ++ (1424871, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) with ((10 - 2, 2) :: (4, 2) :: (1, 1) :: repeat (1, 2) 35 ++ (51, 2) :: (1, 1) :: repeat (1, 2) 212 ++ (616, 2) :: (1, 1) :: repeat (1, 2) 2536 ++ (141868, 2) :: (1, 1) :: repeat (1, 2) 297773 ++ (1424871, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) by sec_eq.
    apply (sTUP [] 3 4 10 2 ((4, 2) :: (1, 1) :: repeat (1, 2) 35 ++ (51, 2) :: (1, 1) :: repeat (1, 2) 212 ++ (616, 2) :: (1, 1) :: repeat (1, 2) 2536 ++ (141868, 2) :: (1, 1) :: repeat (1, 2) 297773 ++ (1424871, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) 1); closearith.
  }
  (* step 134: DIPGRIND 3 2 *)
  apply (hsteps_trans _ (HC [] 0 3 2 (repeat (1, 2) 3 ++ (2, 2) :: (4, 2) :: (1, 1) :: repeat (1, 2) 35 ++ (51, 2) :: (1, 1) :: repeat (1, 2) 212 ++ (616, 2) :: (1, 1) :: repeat (1, 2) 2536 ++ (141868, 2) :: (1, 1) :: repeat (1, 2) 297773 ++ (1424871, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) 1)).
  {
    apply (DIPGRIND 3 2 [] ((4, 2) :: (1, 1) :: repeat (1, 2) 35 ++ (51, 2) :: (1, 1) :: repeat (1, 2) 212 ++ (616, 2) :: (1, 1) :: repeat (1, 2) 2536 ++ (141868, 2) :: (1, 1) :: repeat (1, 2) 297773 ++ (1424871, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) 1); closearith.
  }
  (* step 135: P PUSHX *)
  apply (hsteps_trans _ (HB [] 1 1 7 (repeat (1, 2) 3 ++ (2, 2) :: (4, 2) :: (1, 1) :: repeat (1, 2) 35 ++ (51, 2) :: (1, 1) :: repeat (1, 2) 212 ++ (616, 2) :: (1, 1) :: repeat (1, 2) 2536 ++ (141868, 2) :: (1, 1) :: repeat (1, 2) 297773 ++ (1424871, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) 1)).
  {
    exact (hsteps_step _ _ _ (hPUSHX (repeat (1, 2) 3 ++ (2, 2) :: (4, 2) :: (1, 1) :: repeat (1, 2) 35 ++ (51, 2) :: (1, 1) :: repeat (1, 2) 212 ++ (616, 2) :: (1, 1) :: repeat (1, 2) 2536 ++ (141868, 2) :: (1, 1) :: repeat (1, 2) 297773 ++ (1424871, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) 1) (hsteps_refl _)).
  }
  (* step 136: M pop12 (3,) *)
  apply (hsteps_trans _ (HB [] 4 1 13 ((2, 2) :: (4, 2) :: (1, 1) :: repeat (1, 2) 35 ++ (51, 2) :: (1, 1) :: repeat (1, 2) 212 ++ (616, 2) :: (1, 1) :: repeat (1, 2) 2536 ++ (141868, 2) :: (1, 1) :: repeat (1, 2) 297773 ++ (1424871, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) 1)).
  {
    apply (pop12 3 [] 1 7 ((2, 2) :: (4, 2) :: (1, 1) :: repeat (1, 2) 35 ++ (51, 2) :: (1, 1) :: repeat (1, 2) 212 ++ (616, 2) :: (1, 1) :: repeat (1, 2) 2536 ++ (141868, 2) :: (1, 1) :: repeat (1, 2) 297773 ++ (1424871, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) 1); closearith.
  }
  (* step 137: P TUP2_1 *)
  apply (hsteps_trans _ (HC [5] 13 1 2 ((2, 2) :: (1, 1) :: repeat (1, 2) 35 ++ (51, 2) :: (1, 1) :: repeat (1, 2) 212 ++ (616, 2) :: (1, 1) :: repeat (1, 2) 2536 ++ (141868, 2) :: (1, 1) :: repeat (1, 2) 297773 ++ (1424871, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) 1)).
  {
    replace ((2, 2) :: (1, 1) :: repeat (1, 2) 35 ++ (51, 2) :: (1, 1) :: repeat (1, 2) 212 ++ (616, 2) :: (1, 1) :: repeat (1, 2) 2536 ++ (141868, 2) :: (1, 1) :: repeat (1, 2) 297773 ++ (1424871, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) with ((4 - 2, 2) :: (1, 1) :: repeat (1, 2) 35 ++ (51, 2) :: (1, 1) :: repeat (1, 2) 212 ++ (616, 2) :: (1, 1) :: repeat (1, 2) 2536 ++ (141868, 2) :: (1, 1) :: repeat (1, 2) 297773 ++ (1424871, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) by sec_eq.
    apply (sTUP2_1 [] 4 12 4 ((1, 1) :: repeat (1, 2) 35 ++ (51, 2) :: (1, 1) :: repeat (1, 2) 212 ++ (616, 2) :: (1, 1) :: repeat (1, 2) 2536 ++ (141868, 2) :: (1, 1) :: repeat (1, 2) 297773 ++ (1424871, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) 1); closearith.
  }
  (* step 138: P TDN *)
  apply (hsteps_trans _ (HB [5] 13 1 4 ((2, 2) :: (1, 1) :: repeat (1, 2) 35 ++ (51, 2) :: (1, 1) :: repeat (1, 2) 212 ++ (616, 2) :: (1, 1) :: repeat (1, 2) 2536 ++ (141868, 2) :: (1, 1) :: repeat (1, 2) 297773 ++ (1424871, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) 1)).
  {
    apply (sTDN [5] 13 ((2, 2) :: (1, 1) :: repeat (1, 2) 35 ++ (51, 2) :: (1, 1) :: repeat (1, 2) 212 ++ (616, 2) :: (1, 1) :: repeat (1, 2) 2536 ++ (141868, 2) :: (1, 1) :: repeat (1, 2) 297773 ++ (1424871, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) 1).
  }
  (* step 139: P TRANS2_1 *)
  apply (hsteps_trans _ (HB [14; 5] 5 1 3 (repeat (1, 2) 35 ++ (51, 2) :: (1, 1) :: repeat (1, 2) 212 ++ (616, 2) :: (1, 1) :: repeat (1, 2) 2536 ++ (141868, 2) :: (1, 1) :: repeat (1, 2) 297773 ++ (1424871, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) 1)).
  {
    apply (sTRANS2_1 [5] 13 3 1 (repeat (1, 2) 35 ++ (51, 2) :: (1, 1) :: repeat (1, 2) 212 ++ (616, 2) :: (1, 1) :: repeat (1, 2) 2536 ++ (141868, 2) :: (1, 1) :: repeat (1, 2) 297773 ++ (1424871, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) 1); closearith.
  }
  (* step 140: M pop12 (35,) *)
  apply (hsteps_trans _ (HB [14; 5] 40 1 73 ((51, 2) :: (1, 1) :: repeat (1, 2) 212 ++ (616, 2) :: (1, 1) :: repeat (1, 2) 2536 ++ (141868, 2) :: (1, 1) :: repeat (1, 2) 297773 ++ (1424871, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) 1)).
  {
    apply (pop12 35 [14; 5] 5 3 ((51, 2) :: (1, 1) :: repeat (1, 2) 212 ++ (616, 2) :: (1, 1) :: repeat (1, 2) 2536 ++ (141868, 2) :: (1, 1) :: repeat (1, 2) 297773 ++ (1424871, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) 1); closearith.
  }
  (* step 141: sTUP *)
  apply (hsteps_trans _ (HC [14; 5] 40 72 2 ((49, 2) :: (1, 1) :: repeat (1, 2) 212 ++ (616, 2) :: (1, 1) :: repeat (1, 2) 2536 ++ (141868, 2) :: (1, 1) :: repeat (1, 2) 297773 ++ (1424871, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) 1)).
  {
    replace ((49, 2) :: (1, 1) :: repeat (1, 2) 212 ++ (616, 2) :: (1, 1) :: repeat (1, 2) 2536 ++ (141868, 2) :: (1, 1) :: repeat (1, 2) 297773 ++ (1424871, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) with ((51 - 2, 2) :: (1, 1) :: repeat (1, 2) 212 ++ (616, 2) :: (1, 1) :: repeat (1, 2) 2536 ++ (141868, 2) :: (1, 1) :: repeat (1, 2) 297773 ++ (1424871, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) by sec_eq.
    apply (sTUP [14; 5] 40 73 51 2 ((1, 1) :: repeat (1, 2) 212 ++ (616, 2) :: (1, 1) :: repeat (1, 2) 2536 ++ (141868, 2) :: (1, 1) :: repeat (1, 2) 297773 ++ (1424871, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) 1); closearith.
  }
  (* step 142: hGRIND_even 34 *)
  apply (hsteps_trans _ (HB [14; 5] 39 1 72 ((2, 2) :: (49, 2) :: (1, 1) :: repeat (1, 2) 212 ++ (616, 2) :: (1, 1) :: repeat (1, 2) 2536 ++ (141868, 2) :: (1, 1) :: repeat (1, 2) 297773 ++ (1424871, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) 1)).
  {
    apply (hGRIND_even 34 [14; 5] 39 ((49, 2) :: (1, 1) :: repeat (1, 2) 212 ++ (616, 2) :: (1, 1) :: repeat (1, 2) 2536 ++ (141868, 2) :: (1, 1) :: repeat (1, 2) 297773 ++ (1424871, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) 1); closearith.
  }
  (* step 143: P TUP2_1 *)
  apply (hsteps_trans _ (HC [40; 14; 5] 72 1 2 ((47, 2) :: (1, 1) :: repeat (1, 2) 212 ++ (616, 2) :: (1, 1) :: repeat (1, 2) 2536 ++ (141868, 2) :: (1, 1) :: repeat (1, 2) 297773 ++ (1424871, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) 1)).
  {
    replace ((47, 2) :: (1, 1) :: repeat (1, 2) 212 ++ (616, 2) :: (1, 1) :: repeat (1, 2) 2536 ++ (141868, 2) :: (1, 1) :: repeat (1, 2) 297773 ++ (1424871, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) with ((49 - 2, 2) :: (1, 1) :: repeat (1, 2) 212 ++ (616, 2) :: (1, 1) :: repeat (1, 2) 2536 ++ (141868, 2) :: (1, 1) :: repeat (1, 2) 297773 ++ (1424871, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) by sec_eq.
    apply (sTUP2_1 [14; 5] 39 71 49 ((1, 1) :: repeat (1, 2) 212 ++ (616, 2) :: (1, 1) :: repeat (1, 2) 2536 ++ (141868, 2) :: (1, 1) :: repeat (1, 2) 297773 ++ (1424871, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) 1); closearith.
  }
  (* step 144: P TDN *)
  apply (hsteps_trans _ (HB [40; 14; 5] 72 1 4 ((47, 2) :: (1, 1) :: repeat (1, 2) 212 ++ (616, 2) :: (1, 1) :: repeat (1, 2) 2536 ++ (141868, 2) :: (1, 1) :: repeat (1, 2) 297773 ++ (1424871, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) 1)).
  {
    apply (sTDN [40; 14; 5] 72 ((47, 2) :: (1, 1) :: repeat (1, 2) 212 ++ (616, 2) :: (1, 1) :: repeat (1, 2) 2536 ++ (141868, 2) :: (1, 1) :: repeat (1, 2) 297773 ++ (1424871, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) 1).
  }
  (* step 145: sTUP *)
  apply (hsteps_trans _ (HC [40; 14; 5] 72 3 2 ((45, 2) :: (1, 1) :: repeat (1, 2) 212 ++ (616, 2) :: (1, 1) :: repeat (1, 2) 2536 ++ (141868, 2) :: (1, 1) :: repeat (1, 2) 297773 ++ (1424871, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) 1)).
  {
    replace ((45, 2) :: (1, 1) :: repeat (1, 2) 212 ++ (616, 2) :: (1, 1) :: repeat (1, 2) 2536 ++ (141868, 2) :: (1, 1) :: repeat (1, 2) 297773 ++ (1424871, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) with ((47 - 2, 2) :: (1, 1) :: repeat (1, 2) 212 ++ (616, 2) :: (1, 1) :: repeat (1, 2) 2536 ++ (141868, 2) :: (1, 1) :: repeat (1, 2) 297773 ++ (1424871, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) by sec_eq.
    apply (sTUP [40; 14; 5] 72 4 47 2 ((1, 1) :: repeat (1, 2) 212 ++ (616, 2) :: (1, 1) :: repeat (1, 2) 2536 ++ (141868, 2) :: (1, 1) :: repeat (1, 2) 297773 ++ (1424871, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) 1); closearith.
  }
  (* step 146: CLEANG_odd 21 *)
  apply (hsteps_trans _ (HB [40; 14; 5] 72 1 50 (repeat (1, 2) 1 ++ (1, 1) :: repeat (1, 2) 212 ++ (616, 2) :: (1, 1) :: repeat (1, 2) 2536 ++ (141868, 2) :: (1, 1) :: repeat (1, 2) 297773 ++ (1424871, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) 1)).
  {
    replace (repeat (1, 2) 1 ++ (1, 1) :: repeat (1, 2) 212 ++ (616, 2) :: (1, 1) :: repeat (1, 2) 2536 ++ (141868, 2) :: (1, 1) :: repeat (1, 2) 297773 ++ (1424871, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) with ((1, 2) :: (1, 1) :: repeat (1, 2) 212 ++ (616, 2) :: (1, 1) :: repeat (1, 2) 2536 ++ (141868, 2) :: (1, 1) :: repeat (1, 2) 297773 ++ (1424871, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) by sec_eq.
    apply (CLEANG_odd 21 [40; 14; 5] 72 ((1, 1) :: repeat (1, 2) 212 ++ (616, 2) :: (1, 1) :: repeat (1, 2) 2536 ++ (141868, 2) :: (1, 1) :: repeat (1, 2) 297773 ++ (1424871, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) 1); closearith.
  }
  (* step 147: M pop12 (1,) *)
  apply (hsteps_trans _ (HB [40; 14; 5] 73 1 52 ((1, 1) :: repeat (1, 2) 212 ++ (616, 2) :: (1, 1) :: repeat (1, 2) 2536 ++ (141868, 2) :: (1, 1) :: repeat (1, 2) 297773 ++ (1424871, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) 1)).
  {
    apply (pop12 1 [40; 14; 5] 72 50 ((1, 1) :: repeat (1, 2) 212 ++ (616, 2) :: (1, 1) :: repeat (1, 2) 2536 ++ (141868, 2) :: (1, 1) :: repeat (1, 2) 297773 ++ (1424871, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) 1); closearith.
  }
  (* step 148: P POP *)
  apply (hsteps_trans _ (HB [40; 14; 5] 74 1 53 (repeat (1, 2) 212 ++ (616, 2) :: (1, 1) :: repeat (1, 2) 2536 ++ (141868, 2) :: (1, 1) :: repeat (1, 2) 297773 ++ (1424871, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) 1)).
  {
    apply (sPOP1 [40; 14; 5] 73 52 (repeat (1, 2) 212 ++ (616, 2) :: (1, 1) :: repeat (1, 2) 2536 ++ (141868, 2) :: (1, 1) :: repeat (1, 2) 297773 ++ (1424871, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) 1); closearith.
  }
  (* step 149: M pop12 (212,) *)
  apply (hsteps_trans _ (HB [40; 14; 5] 286 1 477 ((616, 2) :: (1, 1) :: repeat (1, 2) 2536 ++ (141868, 2) :: (1, 1) :: repeat (1, 2) 297773 ++ (1424871, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) 1)).
  {
    apply (pop12 212 [40; 14; 5] 74 53 ((616, 2) :: (1, 1) :: repeat (1, 2) 2536 ++ (141868, 2) :: (1, 1) :: repeat (1, 2) 297773 ++ (1424871, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) 1); closearith.
  }
  (* step 150: sTUP *)
  apply (hsteps_trans _ (HC [40; 14; 5] 286 476 2 ((614, 2) :: (1, 1) :: repeat (1, 2) 2536 ++ (141868, 2) :: (1, 1) :: repeat (1, 2) 297773 ++ (1424871, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) 1)).
  {
    replace ((614, 2) :: (1, 1) :: repeat (1, 2) 2536 ++ (141868, 2) :: (1, 1) :: repeat (1, 2) 297773 ++ (1424871, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) with ((616 - 2, 2) :: (1, 1) :: repeat (1, 2) 2536 ++ (141868, 2) :: (1, 1) :: repeat (1, 2) 297773 ++ (1424871, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) by sec_eq.
    apply (sTUP [40; 14; 5] 286 477 616 2 ((1, 1) :: repeat (1, 2) 2536 ++ (141868, 2) :: (1, 1) :: repeat (1, 2) 297773 ++ (1424871, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) 1); closearith.
  }
  (* step 151: hGRIND_even 236 *)
  apply (hsteps_trans _ (HB [40; 14; 5] 285 1 476 ((2, 2) :: (614, 2) :: (1, 1) :: repeat (1, 2) 2536 ++ (141868, 2) :: (1, 1) :: repeat (1, 2) 297773 ++ (1424871, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) 1)).
  {
    apply (hGRIND_even 236 [40; 14; 5] 285 ((614, 2) :: (1, 1) :: repeat (1, 2) 2536 ++ (141868, 2) :: (1, 1) :: repeat (1, 2) 297773 ++ (1424871, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) 1); closearith.
  }
  (* step 152: P TUP2_1 *)
  apply (hsteps_trans _ (HC [286; 40; 14; 5] 476 1 2 ((612, 2) :: (1, 1) :: repeat (1, 2) 2536 ++ (141868, 2) :: (1, 1) :: repeat (1, 2) 297773 ++ (1424871, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) 1)).
  {
    replace ((612, 2) :: (1, 1) :: repeat (1, 2) 2536 ++ (141868, 2) :: (1, 1) :: repeat (1, 2) 297773 ++ (1424871, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) with ((614 - 2, 2) :: (1, 1) :: repeat (1, 2) 2536 ++ (141868, 2) :: (1, 1) :: repeat (1, 2) 297773 ++ (1424871, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) by sec_eq.
    apply (sTUP2_1 [40; 14; 5] 285 475 614 ((1, 1) :: repeat (1, 2) 2536 ++ (141868, 2) :: (1, 1) :: repeat (1, 2) 297773 ++ (1424871, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) 1); closearith.
  }
  (* step 153: P TDN *)
  apply (hsteps_trans _ (HB [286; 40; 14; 5] 476 1 4 ((612, 2) :: (1, 1) :: repeat (1, 2) 2536 ++ (141868, 2) :: (1, 1) :: repeat (1, 2) 297773 ++ (1424871, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) 1)).
  {
    apply (sTDN [286; 40; 14; 5] 476 ((612, 2) :: (1, 1) :: repeat (1, 2) 2536 ++ (141868, 2) :: (1, 1) :: repeat (1, 2) 297773 ++ (1424871, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) 1).
  }
  (* step 154: sTUP *)
  apply (hsteps_trans _ (HC [286; 40; 14; 5] 476 3 2 ((610, 2) :: (1, 1) :: repeat (1, 2) 2536 ++ (141868, 2) :: (1, 1) :: repeat (1, 2) 297773 ++ (1424871, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) 1)).
  {
    replace ((610, 2) :: (1, 1) :: repeat (1, 2) 2536 ++ (141868, 2) :: (1, 1) :: repeat (1, 2) 297773 ++ (1424871, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) with ((612 - 2, 2) :: (1, 1) :: repeat (1, 2) 2536 ++ (141868, 2) :: (1, 1) :: repeat (1, 2) 297773 ++ (1424871, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) by sec_eq.
    apply (sTUP [286; 40; 14; 5] 476 4 612 2 ((1, 1) :: repeat (1, 2) 2536 ++ (141868, 2) :: (1, 1) :: repeat (1, 2) 297773 ++ (1424871, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) 1); closearith.
  }
  (* step 155: CLEANG_even 304 *)
  apply (hsteps_trans _ (HB [286; 40; 14; 5] 476 1 614 ((2, 2) :: (1, 1) :: repeat (1, 2) 2536 ++ (141868, 2) :: (1, 1) :: repeat (1, 2) 297773 ++ (1424871, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) 1)).
  {
    apply (CLEANG_even 304 [286; 40; 14; 5] 476 ((1, 1) :: repeat (1, 2) 2536 ++ (141868, 2) :: (1, 1) :: repeat (1, 2) 297773 ++ (1424871, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) 1); closearith.
  }
  (* step 156: P TRANS2_1 *)
  apply (hsteps_trans _ (HB [477; 286; 40; 14; 5] 615 1 3 (repeat (1, 2) 2536 ++ (141868, 2) :: (1, 1) :: repeat (1, 2) 297773 ++ (1424871, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) 1)).
  {
    apply (sTRANS2_1 [286; 40; 14; 5] 476 613 1 (repeat (1, 2) 2536 ++ (141868, 2) :: (1, 1) :: repeat (1, 2) 297773 ++ (1424871, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) 1); closearith.
  }
  (* step 157: M pop12 (2536,) *)
  apply (hsteps_trans _ (HB [477; 286; 40; 14; 5] 3151 1 5075 ((141868, 2) :: (1, 1) :: repeat (1, 2) 297773 ++ (1424871, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) 1)).
  {
    apply (pop12 2536 [477; 286; 40; 14; 5] 615 3 ((141868, 2) :: (1, 1) :: repeat (1, 2) 297773 ++ (1424871, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) 1); closearith.
  }
  (* step 158: sTUP *)
  apply (hsteps_trans _ (HC [477; 286; 40; 14; 5] 3151 5074 2 ((141866, 2) :: (1, 1) :: repeat (1, 2) 297773 ++ (1424871, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) 1)).
  {
    replace ((141866, 2) :: (1, 1) :: repeat (1, 2) 297773 ++ (1424871, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) with ((141868 - 2, 2) :: (1, 1) :: repeat (1, 2) 297773 ++ (1424871, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) by sec_eq.
    apply (sTUP [477; 286; 40; 14; 5] 3151 5075 141868 2 ((1, 1) :: repeat (1, 2) 297773 ++ (1424871, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) 1); closearith.
  }
  (* step 159: hGRIND_even 2535 *)
  apply (hsteps_trans _ (HB [477; 286; 40; 14; 5] 3150 1 5074 ((2, 2) :: (141866, 2) :: (1, 1) :: repeat (1, 2) 297773 ++ (1424871, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) 1)).
  {
    apply (hGRIND_even 2535 [477; 286; 40; 14; 5] 3150 ((141866, 2) :: (1, 1) :: repeat (1, 2) 297773 ++ (1424871, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) 1); closearith.
  }
  (* step 160: P TUP2_1 *)
  apply (hsteps_trans _ (HC [3151; 477; 286; 40; 14; 5] 5074 1 2 ((141864, 2) :: (1, 1) :: repeat (1, 2) 297773 ++ (1424871, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) 1)).
  {
    replace ((141864, 2) :: (1, 1) :: repeat (1, 2) 297773 ++ (1424871, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) with ((141866 - 2, 2) :: (1, 1) :: repeat (1, 2) 297773 ++ (1424871, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) by sec_eq.
    apply (sTUP2_1 [477; 286; 40; 14; 5] 3150 5073 141866 ((1, 1) :: repeat (1, 2) 297773 ++ (1424871, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) 1); closearith.
  }
  (* step 161: P TDN *)
  apply (hsteps_trans _ (HB [3151; 477; 286; 40; 14; 5] 5074 1 4 ((141864, 2) :: (1, 1) :: repeat (1, 2) 297773 ++ (1424871, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) 1)).
  {
    apply (sTDN [3151; 477; 286; 40; 14; 5] 5074 ((141864, 2) :: (1, 1) :: repeat (1, 2) 297773 ++ (1424871, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) 1).
  }
  (* step 162: sTUP *)
  apply (hsteps_trans _ (HC [3151; 477; 286; 40; 14; 5] 5074 3 2 ((141862, 2) :: (1, 1) :: repeat (1, 2) 297773 ++ (1424871, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) 1)).
  {
    replace ((141862, 2) :: (1, 1) :: repeat (1, 2) 297773 ++ (1424871, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) with ((141864 - 2, 2) :: (1, 1) :: repeat (1, 2) 297773 ++ (1424871, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) by sec_eq.
    apply (sTUP [3151; 477; 286; 40; 14; 5] 5074 4 141864 2 ((1, 1) :: repeat (1, 2) 297773 ++ (1424871, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) 1); closearith.
  }
  (* step 163: DIPGRIND 5074 131714 *)
  apply (hsteps_trans _ (HC [3151; 477; 286; 40; 14; 5] 0 3 2 (repeat (1, 2) 5074 ++ (131714, 2) :: (1, 1) :: repeat (1, 2) 297773 ++ (1424871, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) 1)).
  {
    rewrite NUM56X7.
    apply (DIPGRIND 5074 131714 [3151; 477; 286; 40; 14; 5] ((1, 1) :: repeat (1, 2) 297773 ++ (1424871, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) 1); closearith.
  }
  (* step 164: P PX2A *)
  apply (hsteps_trans _ (HC [286; 40; 14; 5] 476 3149 2 ((1, 1) :: repeat (1, 2) 5076 ++ (131714, 2) :: (1, 1) :: repeat (1, 2) 297773 ++ (1424871, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) 1)).
  {
    exact (hsteps_step _ _ _ (hPX2A 3148 476 [286; 40; 14; 5] (repeat (1, 2) 5074 ++ (131714, 2) :: (1, 1) :: repeat (1, 2) 297773 ++ (1424871, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) 1) (hsteps_refl _)).
  }
  (* step 165: P PUSH *)
  apply (hsteps_trans _ (HC [286; 40; 14; 5] 475 1 2 ((3147, 2) :: (1, 1) :: repeat (1, 2) 5076 ++ (131714, 2) :: (1, 1) :: repeat (1, 2) 297773 ++ (1424871, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) 1)).
  {
    replace ((3147, 2) :: (1, 1) :: repeat (1, 2) 5076 ++ (131714, 2) :: (1, 1) :: repeat (1, 2) 297773 ++ (1424871, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) with ((3149 - 2, 2) :: (1, 1) :: repeat (1, 2) 5076 ++ (131714, 2) :: (1, 1) :: repeat (1, 2) 297773 ++ (1424871, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) by sec_eq.
    apply (sPUSH [286; 40; 14; 5] 475 3149 ((1, 1) :: repeat (1, 2) 5076 ++ (131714, 2) :: (1, 1) :: repeat (1, 2) 297773 ++ (1424871, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) 1); closearith.
  }
  (* step 166: P TDN *)
  apply (hsteps_trans _ (HB [286; 40; 14; 5] 475 1 4 ((3147, 2) :: (1, 1) :: repeat (1, 2) 5076 ++ (131714, 2) :: (1, 1) :: repeat (1, 2) 297773 ++ (1424871, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) 1)).
  {
    apply (sTDN [286; 40; 14; 5] 475 ((3147, 2) :: (1, 1) :: repeat (1, 2) 5076 ++ (131714, 2) :: (1, 1) :: repeat (1, 2) 297773 ++ (1424871, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) 1).
  }
  (* step 167: sTUP *)
  apply (hsteps_trans _ (HC [286; 40; 14; 5] 475 3 2 ((3145, 2) :: (1, 1) :: repeat (1, 2) 5076 ++ (131714, 2) :: (1, 1) :: repeat (1, 2) 297773 ++ (1424871, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) 1)).
  {
    replace ((3145, 2) :: (1, 1) :: repeat (1, 2) 5076 ++ (131714, 2) :: (1, 1) :: repeat (1, 2) 297773 ++ (1424871, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) with ((3147 - 2, 2) :: (1, 1) :: repeat (1, 2) 5076 ++ (131714, 2) :: (1, 1) :: repeat (1, 2) 297773 ++ (1424871, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) by sec_eq.
    apply (sTUP [286; 40; 14; 5] 475 4 3147 2 ((1, 1) :: repeat (1, 2) 5076 ++ (131714, 2) :: (1, 1) :: repeat (1, 2) 297773 ++ (1424871, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) 1); closearith.
  }
  (* step 168: DIPGRIND 475 2195 *)
  apply (DIPGRIND 475 2195 [286; 40; 14; 5] ((1, 1) :: repeat (1, 2) 5076 ++ (131714, 2) :: (1, 1) :: repeat (1, 2) 297773 ++ (1424871, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) 1); closearith.
Qed.

(* CASCADE56d: steps 169-224 of the CASCADE56 chain. *)
Lemma CASCADE56d : forall w,
  hsteps (HC [286; 40; 14; 5] 0 3 2 (repeat (1, 2) 475 ++ (2195, 2) :: (1, 1) :: repeat (1, 2) 5076 ++ (131714, 2) :: (1, 1) :: repeat (1, 2) 297773 ++ (1424871, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) 1)
         (HB [93; 35; 20; 0] 170 1 32 ((2, 2) :: (1, 1) :: repeat (1, 2) 477 ++ (2195, 2) :: (1, 1) :: repeat (1, 2) 5076 ++ (131714, 2) :: (1, 1) :: repeat (1, 2) 297773 ++ (1424871, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) 1).
Proof.
  intro w.
  (* step 169: P PX2A *)
  apply (hsteps_trans _ (HC [14; 5] 39 284 2 ((1, 1) :: repeat (1, 2) 477 ++ (2195, 2) :: (1, 1) :: repeat (1, 2) 5076 ++ (131714, 2) :: (1, 1) :: repeat (1, 2) 297773 ++ (1424871, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) 1)).
  {
    exact (hsteps_step _ _ _ (hPX2A 283 39 [14; 5] (repeat (1, 2) 475 ++ (2195, 2) :: (1, 1) :: repeat (1, 2) 5076 ++ (131714, 2) :: (1, 1) :: repeat (1, 2) 297773 ++ (1424871, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) 1) (hsteps_refl _)).
  }
  (* step 170: P PUSH *)
  apply (hsteps_trans _ (HC [14; 5] 38 1 2 ((282, 2) :: (1, 1) :: repeat (1, 2) 477 ++ (2195, 2) :: (1, 1) :: repeat (1, 2) 5076 ++ (131714, 2) :: (1, 1) :: repeat (1, 2) 297773 ++ (1424871, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) 1)).
  {
    replace ((282, 2) :: (1, 1) :: repeat (1, 2) 477 ++ (2195, 2) :: (1, 1) :: repeat (1, 2) 5076 ++ (131714, 2) :: (1, 1) :: repeat (1, 2) 297773 ++ (1424871, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) with ((284 - 2, 2) :: (1, 1) :: repeat (1, 2) 477 ++ (2195, 2) :: (1, 1) :: repeat (1, 2) 5076 ++ (131714, 2) :: (1, 1) :: repeat (1, 2) 297773 ++ (1424871, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) by sec_eq.
    apply (sPUSH [14; 5] 38 284 ((1, 1) :: repeat (1, 2) 477 ++ (2195, 2) :: (1, 1) :: repeat (1, 2) 5076 ++ (131714, 2) :: (1, 1) :: repeat (1, 2) 297773 ++ (1424871, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) 1); closearith.
  }
  (* step 171: P TDN *)
  apply (hsteps_trans _ (HB [14; 5] 38 1 4 ((282, 2) :: (1, 1) :: repeat (1, 2) 477 ++ (2195, 2) :: (1, 1) :: repeat (1, 2) 5076 ++ (131714, 2) :: (1, 1) :: repeat (1, 2) 297773 ++ (1424871, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) 1)).
  {
    apply (sTDN [14; 5] 38 ((282, 2) :: (1, 1) :: repeat (1, 2) 477 ++ (2195, 2) :: (1, 1) :: repeat (1, 2) 5076 ++ (131714, 2) :: (1, 1) :: repeat (1, 2) 297773 ++ (1424871, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) 1).
  }
  (* step 172: sTUP *)
  apply (hsteps_trans _ (HC [14; 5] 38 3 2 ((280, 2) :: (1, 1) :: repeat (1, 2) 477 ++ (2195, 2) :: (1, 1) :: repeat (1, 2) 5076 ++ (131714, 2) :: (1, 1) :: repeat (1, 2) 297773 ++ (1424871, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) 1)).
  {
    replace ((280, 2) :: (1, 1) :: repeat (1, 2) 477 ++ (2195, 2) :: (1, 1) :: repeat (1, 2) 5076 ++ (131714, 2) :: (1, 1) :: repeat (1, 2) 297773 ++ (1424871, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) with ((282 - 2, 2) :: (1, 1) :: repeat (1, 2) 477 ++ (2195, 2) :: (1, 1) :: repeat (1, 2) 5076 ++ (131714, 2) :: (1, 1) :: repeat (1, 2) 297773 ++ (1424871, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) by sec_eq.
    apply (sTUP [14; 5] 38 4 282 2 ((1, 1) :: repeat (1, 2) 477 ++ (2195, 2) :: (1, 1) :: repeat (1, 2) 5076 ++ (131714, 2) :: (1, 1) :: repeat (1, 2) 297773 ++ (1424871, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) 1); closearith.
  }
  (* step 173: DIPGRIND 38 204 *)
  apply (hsteps_trans _ (HC [14; 5] 0 3 2 (repeat (1, 2) 38 ++ (204, 2) :: (1, 1) :: repeat (1, 2) 477 ++ (2195, 2) :: (1, 1) :: repeat (1, 2) 5076 ++ (131714, 2) :: (1, 1) :: repeat (1, 2) 297773 ++ (1424871, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) 1)).
  {
    apply (DIPGRIND 38 204 [14; 5] ((1, 1) :: repeat (1, 2) 477 ++ (2195, 2) :: (1, 1) :: repeat (1, 2) 5076 ++ (131714, 2) :: (1, 1) :: repeat (1, 2) 297773 ++ (1424871, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) 1); closearith.
  }
  (* step 174: P PX2A *)
  apply (hsteps_trans _ (HC [] 4 12 2 ((1, 1) :: repeat (1, 2) 40 ++ (204, 2) :: (1, 1) :: repeat (1, 2) 477 ++ (2195, 2) :: (1, 1) :: repeat (1, 2) 5076 ++ (131714, 2) :: (1, 1) :: repeat (1, 2) 297773 ++ (1424871, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) 1)).
  {
    exact (hsteps_step _ _ _ (hPX2A 11 4 [] (repeat (1, 2) 38 ++ (204, 2) :: (1, 1) :: repeat (1, 2) 477 ++ (2195, 2) :: (1, 1) :: repeat (1, 2) 5076 ++ (131714, 2) :: (1, 1) :: repeat (1, 2) 297773 ++ (1424871, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) 1) (hsteps_refl _)).
  }
  (* step 175: P PUSH *)
  apply (hsteps_trans _ (HC [] 3 1 2 ((10, 2) :: (1, 1) :: repeat (1, 2) 40 ++ (204, 2) :: (1, 1) :: repeat (1, 2) 477 ++ (2195, 2) :: (1, 1) :: repeat (1, 2) 5076 ++ (131714, 2) :: (1, 1) :: repeat (1, 2) 297773 ++ (1424871, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) 1)).
  {
    replace ((10, 2) :: (1, 1) :: repeat (1, 2) 40 ++ (204, 2) :: (1, 1) :: repeat (1, 2) 477 ++ (2195, 2) :: (1, 1) :: repeat (1, 2) 5076 ++ (131714, 2) :: (1, 1) :: repeat (1, 2) 297773 ++ (1424871, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) with ((12 - 2, 2) :: (1, 1) :: repeat (1, 2) 40 ++ (204, 2) :: (1, 1) :: repeat (1, 2) 477 ++ (2195, 2) :: (1, 1) :: repeat (1, 2) 5076 ++ (131714, 2) :: (1, 1) :: repeat (1, 2) 297773 ++ (1424871, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) by sec_eq.
    apply (sPUSH [] 3 12 ((1, 1) :: repeat (1, 2) 40 ++ (204, 2) :: (1, 1) :: repeat (1, 2) 477 ++ (2195, 2) :: (1, 1) :: repeat (1, 2) 5076 ++ (131714, 2) :: (1, 1) :: repeat (1, 2) 297773 ++ (1424871, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) 1); closearith.
  }
  (* step 176: P TDN *)
  apply (hsteps_trans _ (HB [] 3 1 4 ((10, 2) :: (1, 1) :: repeat (1, 2) 40 ++ (204, 2) :: (1, 1) :: repeat (1, 2) 477 ++ (2195, 2) :: (1, 1) :: repeat (1, 2) 5076 ++ (131714, 2) :: (1, 1) :: repeat (1, 2) 297773 ++ (1424871, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) 1)).
  {
    apply (sTDN [] 3 ((10, 2) :: (1, 1) :: repeat (1, 2) 40 ++ (204, 2) :: (1, 1) :: repeat (1, 2) 477 ++ (2195, 2) :: (1, 1) :: repeat (1, 2) 5076 ++ (131714, 2) :: (1, 1) :: repeat (1, 2) 297773 ++ (1424871, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) 1).
  }
  (* step 177: sTUP *)
  apply (hsteps_trans _ (HC [] 3 3 2 ((8, 2) :: (1, 1) :: repeat (1, 2) 40 ++ (204, 2) :: (1, 1) :: repeat (1, 2) 477 ++ (2195, 2) :: (1, 1) :: repeat (1, 2) 5076 ++ (131714, 2) :: (1, 1) :: repeat (1, 2) 297773 ++ (1424871, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) 1)).
  {
    replace ((8, 2) :: (1, 1) :: repeat (1, 2) 40 ++ (204, 2) :: (1, 1) :: repeat (1, 2) 477 ++ (2195, 2) :: (1, 1) :: repeat (1, 2) 5076 ++ (131714, 2) :: (1, 1) :: repeat (1, 2) 297773 ++ (1424871, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) with ((10 - 2, 2) :: (1, 1) :: repeat (1, 2) 40 ++ (204, 2) :: (1, 1) :: repeat (1, 2) 477 ++ (2195, 2) :: (1, 1) :: repeat (1, 2) 5076 ++ (131714, 2) :: (1, 1) :: repeat (1, 2) 297773 ++ (1424871, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) by sec_eq.
    apply (sTUP [] 3 4 10 2 ((1, 1) :: repeat (1, 2) 40 ++ (204, 2) :: (1, 1) :: repeat (1, 2) 477 ++ (2195, 2) :: (1, 1) :: repeat (1, 2) 5076 ++ (131714, 2) :: (1, 1) :: repeat (1, 2) 297773 ++ (1424871, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) 1); closearith.
  }
  (* step 178: DIPGRIND 3 2 *)
  apply (hsteps_trans _ (HC [] 0 3 2 (repeat (1, 2) 3 ++ (2, 2) :: (1, 1) :: repeat (1, 2) 40 ++ (204, 2) :: (1, 1) :: repeat (1, 2) 477 ++ (2195, 2) :: (1, 1) :: repeat (1, 2) 5076 ++ (131714, 2) :: (1, 1) :: repeat (1, 2) 297773 ++ (1424871, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) 1)).
  {
    apply (DIPGRIND 3 2 [] ((1, 1) :: repeat (1, 2) 40 ++ (204, 2) :: (1, 1) :: repeat (1, 2) 477 ++ (2195, 2) :: (1, 1) :: repeat (1, 2) 5076 ++ (131714, 2) :: (1, 1) :: repeat (1, 2) 297773 ++ (1424871, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) 1); closearith.
  }
  (* step 179: P PUSHX *)
  apply (hsteps_trans _ (HB [] 1 1 7 (repeat (1, 2) 3 ++ (2, 2) :: (1, 1) :: repeat (1, 2) 40 ++ (204, 2) :: (1, 1) :: repeat (1, 2) 477 ++ (2195, 2) :: (1, 1) :: repeat (1, 2) 5076 ++ (131714, 2) :: (1, 1) :: repeat (1, 2) 297773 ++ (1424871, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) 1)).
  {
    exact (hsteps_step _ _ _ (hPUSHX (repeat (1, 2) 3 ++ (2, 2) :: (1, 1) :: repeat (1, 2) 40 ++ (204, 2) :: (1, 1) :: repeat (1, 2) 477 ++ (2195, 2) :: (1, 1) :: repeat (1, 2) 5076 ++ (131714, 2) :: (1, 1) :: repeat (1, 2) 297773 ++ (1424871, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) 1) (hsteps_refl _)).
  }
  (* step 180: M pop12 (3,) *)
  apply (hsteps_trans _ (HB [] 4 1 13 ((2, 2) :: (1, 1) :: repeat (1, 2) 40 ++ (204, 2) :: (1, 1) :: repeat (1, 2) 477 ++ (2195, 2) :: (1, 1) :: repeat (1, 2) 5076 ++ (131714, 2) :: (1, 1) :: repeat (1, 2) 297773 ++ (1424871, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) 1)).
  {
    apply (pop12 3 [] 1 7 ((2, 2) :: (1, 1) :: repeat (1, 2) 40 ++ (204, 2) :: (1, 1) :: repeat (1, 2) 477 ++ (2195, 2) :: (1, 1) :: repeat (1, 2) 5076 ++ (131714, 2) :: (1, 1) :: repeat (1, 2) 297773 ++ (1424871, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) 1); closearith.
  }
  (* step 181: P TRANS2_1 *)
  apply (hsteps_trans _ (HB [5] 14 1 3 (repeat (1, 2) 40 ++ (204, 2) :: (1, 1) :: repeat (1, 2) 477 ++ (2195, 2) :: (1, 1) :: repeat (1, 2) 5076 ++ (131714, 2) :: (1, 1) :: repeat (1, 2) 297773 ++ (1424871, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) 1)).
  {
    apply (sTRANS2_1 [] 4 12 1 (repeat (1, 2) 40 ++ (204, 2) :: (1, 1) :: repeat (1, 2) 477 ++ (2195, 2) :: (1, 1) :: repeat (1, 2) 5076 ++ (131714, 2) :: (1, 1) :: repeat (1, 2) 297773 ++ (1424871, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) 1); closearith.
  }
  (* step 182: M pop12 (40,) *)
  apply (hsteps_trans _ (HB [5] 54 1 83 ((204, 2) :: (1, 1) :: repeat (1, 2) 477 ++ (2195, 2) :: (1, 1) :: repeat (1, 2) 5076 ++ (131714, 2) :: (1, 1) :: repeat (1, 2) 297773 ++ (1424871, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) 1)).
  {
    apply (pop12 40 [5] 14 3 ((204, 2) :: (1, 1) :: repeat (1, 2) 477 ++ (2195, 2) :: (1, 1) :: repeat (1, 2) 5076 ++ (131714, 2) :: (1, 1) :: repeat (1, 2) 297773 ++ (1424871, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) 1); closearith.
  }
  (* step 183: sTUP *)
  apply (hsteps_trans _ (HC [5] 54 82 2 ((202, 2) :: (1, 1) :: repeat (1, 2) 477 ++ (2195, 2) :: (1, 1) :: repeat (1, 2) 5076 ++ (131714, 2) :: (1, 1) :: repeat (1, 2) 297773 ++ (1424871, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) 1)).
  {
    replace ((202, 2) :: (1, 1) :: repeat (1, 2) 477 ++ (2195, 2) :: (1, 1) :: repeat (1, 2) 5076 ++ (131714, 2) :: (1, 1) :: repeat (1, 2) 297773 ++ (1424871, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) with ((204 - 2, 2) :: (1, 1) :: repeat (1, 2) 477 ++ (2195, 2) :: (1, 1) :: repeat (1, 2) 5076 ++ (131714, 2) :: (1, 1) :: repeat (1, 2) 297773 ++ (1424871, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) by sec_eq.
    apply (sTUP [5] 54 83 204 2 ((1, 1) :: repeat (1, 2) 477 ++ (2195, 2) :: (1, 1) :: repeat (1, 2) 5076 ++ (131714, 2) :: (1, 1) :: repeat (1, 2) 297773 ++ (1424871, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) 1); closearith.
  }
  (* step 184: hGRIND_even 39 *)
  apply (hsteps_trans _ (HB [5] 53 1 82 ((2, 2) :: (202, 2) :: (1, 1) :: repeat (1, 2) 477 ++ (2195, 2) :: (1, 1) :: repeat (1, 2) 5076 ++ (131714, 2) :: (1, 1) :: repeat (1, 2) 297773 ++ (1424871, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) 1)).
  {
    apply (hGRIND_even 39 [5] 53 ((202, 2) :: (1, 1) :: repeat (1, 2) 477 ++ (2195, 2) :: (1, 1) :: repeat (1, 2) 5076 ++ (131714, 2) :: (1, 1) :: repeat (1, 2) 297773 ++ (1424871, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) 1); closearith.
  }
  (* step 185: P TUP2_1 *)
  apply (hsteps_trans _ (HC [54; 5] 82 1 2 ((200, 2) :: (1, 1) :: repeat (1, 2) 477 ++ (2195, 2) :: (1, 1) :: repeat (1, 2) 5076 ++ (131714, 2) :: (1, 1) :: repeat (1, 2) 297773 ++ (1424871, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) 1)).
  {
    replace ((200, 2) :: (1, 1) :: repeat (1, 2) 477 ++ (2195, 2) :: (1, 1) :: repeat (1, 2) 5076 ++ (131714, 2) :: (1, 1) :: repeat (1, 2) 297773 ++ (1424871, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) with ((202 - 2, 2) :: (1, 1) :: repeat (1, 2) 477 ++ (2195, 2) :: (1, 1) :: repeat (1, 2) 5076 ++ (131714, 2) :: (1, 1) :: repeat (1, 2) 297773 ++ (1424871, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) by sec_eq.
    apply (sTUP2_1 [5] 53 81 202 ((1, 1) :: repeat (1, 2) 477 ++ (2195, 2) :: (1, 1) :: repeat (1, 2) 5076 ++ (131714, 2) :: (1, 1) :: repeat (1, 2) 297773 ++ (1424871, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) 1); closearith.
  }
  (* step 186: P TDN *)
  apply (hsteps_trans _ (HB [54; 5] 82 1 4 ((200, 2) :: (1, 1) :: repeat (1, 2) 477 ++ (2195, 2) :: (1, 1) :: repeat (1, 2) 5076 ++ (131714, 2) :: (1, 1) :: repeat (1, 2) 297773 ++ (1424871, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) 1)).
  {
    apply (sTDN [54; 5] 82 ((200, 2) :: (1, 1) :: repeat (1, 2) 477 ++ (2195, 2) :: (1, 1) :: repeat (1, 2) 5076 ++ (131714, 2) :: (1, 1) :: repeat (1, 2) 297773 ++ (1424871, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) 1).
  }
  (* step 187: sTUP *)
  apply (hsteps_trans _ (HC [54; 5] 82 3 2 ((198, 2) :: (1, 1) :: repeat (1, 2) 477 ++ (2195, 2) :: (1, 1) :: repeat (1, 2) 5076 ++ (131714, 2) :: (1, 1) :: repeat (1, 2) 297773 ++ (1424871, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) 1)).
  {
    replace ((198, 2) :: (1, 1) :: repeat (1, 2) 477 ++ (2195, 2) :: (1, 1) :: repeat (1, 2) 5076 ++ (131714, 2) :: (1, 1) :: repeat (1, 2) 297773 ++ (1424871, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) with ((200 - 2, 2) :: (1, 1) :: repeat (1, 2) 477 ++ (2195, 2) :: (1, 1) :: repeat (1, 2) 5076 ++ (131714, 2) :: (1, 1) :: repeat (1, 2) 297773 ++ (1424871, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) by sec_eq.
    apply (sTUP [54; 5] 82 4 200 2 ((1, 1) :: repeat (1, 2) 477 ++ (2195, 2) :: (1, 1) :: repeat (1, 2) 5076 ++ (131714, 2) :: (1, 1) :: repeat (1, 2) 297773 ++ (1424871, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) 1); closearith.
  }
  (* step 188: DIPGRIND 82 34 *)
  apply (hsteps_trans _ (HC [54; 5] 0 3 2 (repeat (1, 2) 82 ++ (34, 2) :: (1, 1) :: repeat (1, 2) 477 ++ (2195, 2) :: (1, 1) :: repeat (1, 2) 5076 ++ (131714, 2) :: (1, 1) :: repeat (1, 2) 297773 ++ (1424871, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) 1)).
  {
    apply (DIPGRIND 82 34 [54; 5] ((1, 1) :: repeat (1, 2) 477 ++ (2195, 2) :: (1, 1) :: repeat (1, 2) 5076 ++ (131714, 2) :: (1, 1) :: repeat (1, 2) 297773 ++ (1424871, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) 1); closearith.
  }
  (* step 189: P PX2A *)
  apply (hsteps_trans _ (HC [] 4 52 2 ((1, 1) :: repeat (1, 2) 84 ++ (34, 2) :: (1, 1) :: repeat (1, 2) 477 ++ (2195, 2) :: (1, 1) :: repeat (1, 2) 5076 ++ (131714, 2) :: (1, 1) :: repeat (1, 2) 297773 ++ (1424871, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) 1)).
  {
    exact (hsteps_step _ _ _ (hPX2A 51 4 [] (repeat (1, 2) 82 ++ (34, 2) :: (1, 1) :: repeat (1, 2) 477 ++ (2195, 2) :: (1, 1) :: repeat (1, 2) 5076 ++ (131714, 2) :: (1, 1) :: repeat (1, 2) 297773 ++ (1424871, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) 1) (hsteps_refl _)).
  }
  (* step 190: P PUSH *)
  apply (hsteps_trans _ (HC [] 3 1 2 ((50, 2) :: (1, 1) :: repeat (1, 2) 84 ++ (34, 2) :: (1, 1) :: repeat (1, 2) 477 ++ (2195, 2) :: (1, 1) :: repeat (1, 2) 5076 ++ (131714, 2) :: (1, 1) :: repeat (1, 2) 297773 ++ (1424871, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) 1)).
  {
    replace ((50, 2) :: (1, 1) :: repeat (1, 2) 84 ++ (34, 2) :: (1, 1) :: repeat (1, 2) 477 ++ (2195, 2) :: (1, 1) :: repeat (1, 2) 5076 ++ (131714, 2) :: (1, 1) :: repeat (1, 2) 297773 ++ (1424871, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) with ((52 - 2, 2) :: (1, 1) :: repeat (1, 2) 84 ++ (34, 2) :: (1, 1) :: repeat (1, 2) 477 ++ (2195, 2) :: (1, 1) :: repeat (1, 2) 5076 ++ (131714, 2) :: (1, 1) :: repeat (1, 2) 297773 ++ (1424871, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) by sec_eq.
    apply (sPUSH [] 3 52 ((1, 1) :: repeat (1, 2) 84 ++ (34, 2) :: (1, 1) :: repeat (1, 2) 477 ++ (2195, 2) :: (1, 1) :: repeat (1, 2) 5076 ++ (131714, 2) :: (1, 1) :: repeat (1, 2) 297773 ++ (1424871, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) 1); closearith.
  }
  (* step 191: P TDN *)
  apply (hsteps_trans _ (HB [] 3 1 4 ((50, 2) :: (1, 1) :: repeat (1, 2) 84 ++ (34, 2) :: (1, 1) :: repeat (1, 2) 477 ++ (2195, 2) :: (1, 1) :: repeat (1, 2) 5076 ++ (131714, 2) :: (1, 1) :: repeat (1, 2) 297773 ++ (1424871, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) 1)).
  {
    apply (sTDN [] 3 ((50, 2) :: (1, 1) :: repeat (1, 2) 84 ++ (34, 2) :: (1, 1) :: repeat (1, 2) 477 ++ (2195, 2) :: (1, 1) :: repeat (1, 2) 5076 ++ (131714, 2) :: (1, 1) :: repeat (1, 2) 297773 ++ (1424871, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) 1).
  }
  (* step 192: sTUP *)
  apply (hsteps_trans _ (HC [] 3 3 2 ((48, 2) :: (1, 1) :: repeat (1, 2) 84 ++ (34, 2) :: (1, 1) :: repeat (1, 2) 477 ++ (2195, 2) :: (1, 1) :: repeat (1, 2) 5076 ++ (131714, 2) :: (1, 1) :: repeat (1, 2) 297773 ++ (1424871, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) 1)).
  {
    replace ((48, 2) :: (1, 1) :: repeat (1, 2) 84 ++ (34, 2) :: (1, 1) :: repeat (1, 2) 477 ++ (2195, 2) :: (1, 1) :: repeat (1, 2) 5076 ++ (131714, 2) :: (1, 1) :: repeat (1, 2) 297773 ++ (1424871, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) with ((50 - 2, 2) :: (1, 1) :: repeat (1, 2) 84 ++ (34, 2) :: (1, 1) :: repeat (1, 2) 477 ++ (2195, 2) :: (1, 1) :: repeat (1, 2) 5076 ++ (131714, 2) :: (1, 1) :: repeat (1, 2) 297773 ++ (1424871, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) by sec_eq.
    apply (sTUP [] 3 4 50 2 ((1, 1) :: repeat (1, 2) 84 ++ (34, 2) :: (1, 1) :: repeat (1, 2) 477 ++ (2195, 2) :: (1, 1) :: repeat (1, 2) 5076 ++ (131714, 2) :: (1, 1) :: repeat (1, 2) 297773 ++ (1424871, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) 1); closearith.
  }
  (* step 193: DIPGRIND 3 42 *)
  apply (hsteps_trans _ (HC [] 0 3 2 (repeat (1, 2) 3 ++ (42, 2) :: (1, 1) :: repeat (1, 2) 84 ++ (34, 2) :: (1, 1) :: repeat (1, 2) 477 ++ (2195, 2) :: (1, 1) :: repeat (1, 2) 5076 ++ (131714, 2) :: (1, 1) :: repeat (1, 2) 297773 ++ (1424871, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) 1)).
  {
    apply (DIPGRIND 3 42 [] ((1, 1) :: repeat (1, 2) 84 ++ (34, 2) :: (1, 1) :: repeat (1, 2) 477 ++ (2195, 2) :: (1, 1) :: repeat (1, 2) 5076 ++ (131714, 2) :: (1, 1) :: repeat (1, 2) 297773 ++ (1424871, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) 1); closearith.
  }
  (* step 194: P PUSHX *)
  apply (hsteps_trans _ (HB [] 1 1 7 (repeat (1, 2) 3 ++ (42, 2) :: (1, 1) :: repeat (1, 2) 84 ++ (34, 2) :: (1, 1) :: repeat (1, 2) 477 ++ (2195, 2) :: (1, 1) :: repeat (1, 2) 5076 ++ (131714, 2) :: (1, 1) :: repeat (1, 2) 297773 ++ (1424871, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) 1)).
  {
    exact (hsteps_step _ _ _ (hPUSHX (repeat (1, 2) 3 ++ (42, 2) :: (1, 1) :: repeat (1, 2) 84 ++ (34, 2) :: (1, 1) :: repeat (1, 2) 477 ++ (2195, 2) :: (1, 1) :: repeat (1, 2) 5076 ++ (131714, 2) :: (1, 1) :: repeat (1, 2) 297773 ++ (1424871, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) 1) (hsteps_refl _)).
  }
  (* step 195: M pop12 (3,) *)
  apply (hsteps_trans _ (HB [] 4 1 13 ((42, 2) :: (1, 1) :: repeat (1, 2) 84 ++ (34, 2) :: (1, 1) :: repeat (1, 2) 477 ++ (2195, 2) :: (1, 1) :: repeat (1, 2) 5076 ++ (131714, 2) :: (1, 1) :: repeat (1, 2) 297773 ++ (1424871, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) 1)).
  {
    apply (pop12 3 [] 1 7 ((42, 2) :: (1, 1) :: repeat (1, 2) 84 ++ (34, 2) :: (1, 1) :: repeat (1, 2) 477 ++ (2195, 2) :: (1, 1) :: repeat (1, 2) 5076 ++ (131714, 2) :: (1, 1) :: repeat (1, 2) 297773 ++ (1424871, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) 1); closearith.
  }
  (* step 196: sTUP *)
  apply (hsteps_trans _ (HC [] 4 12 2 ((40, 2) :: (1, 1) :: repeat (1, 2) 84 ++ (34, 2) :: (1, 1) :: repeat (1, 2) 477 ++ (2195, 2) :: (1, 1) :: repeat (1, 2) 5076 ++ (131714, 2) :: (1, 1) :: repeat (1, 2) 297773 ++ (1424871, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) 1)).
  {
    replace ((40, 2) :: (1, 1) :: repeat (1, 2) 84 ++ (34, 2) :: (1, 1) :: repeat (1, 2) 477 ++ (2195, 2) :: (1, 1) :: repeat (1, 2) 5076 ++ (131714, 2) :: (1, 1) :: repeat (1, 2) 297773 ++ (1424871, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) with ((42 - 2, 2) :: (1, 1) :: repeat (1, 2) 84 ++ (34, 2) :: (1, 1) :: repeat (1, 2) 477 ++ (2195, 2) :: (1, 1) :: repeat (1, 2) 5076 ++ (131714, 2) :: (1, 1) :: repeat (1, 2) 297773 ++ (1424871, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) by sec_eq.
    apply (sTUP [] 4 13 42 2 ((1, 1) :: repeat (1, 2) 84 ++ (34, 2) :: (1, 1) :: repeat (1, 2) 477 ++ (2195, 2) :: (1, 1) :: repeat (1, 2) 5076 ++ (131714, 2) :: (1, 1) :: repeat (1, 2) 297773 ++ (1424871, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) 1); closearith.
  }
  (* step 197: P PUSH *)
  apply (hsteps_trans _ (HC [] 3 1 2 ((10, 2) :: (40, 2) :: (1, 1) :: repeat (1, 2) 84 ++ (34, 2) :: (1, 1) :: repeat (1, 2) 477 ++ (2195, 2) :: (1, 1) :: repeat (1, 2) 5076 ++ (131714, 2) :: (1, 1) :: repeat (1, 2) 297773 ++ (1424871, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) 1)).
  {
    replace ((10, 2) :: (40, 2) :: (1, 1) :: repeat (1, 2) 84 ++ (34, 2) :: (1, 1) :: repeat (1, 2) 477 ++ (2195, 2) :: (1, 1) :: repeat (1, 2) 5076 ++ (131714, 2) :: (1, 1) :: repeat (1, 2) 297773 ++ (1424871, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) with ((12 - 2, 2) :: (40, 2) :: (1, 1) :: repeat (1, 2) 84 ++ (34, 2) :: (1, 1) :: repeat (1, 2) 477 ++ (2195, 2) :: (1, 1) :: repeat (1, 2) 5076 ++ (131714, 2) :: (1, 1) :: repeat (1, 2) 297773 ++ (1424871, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) by sec_eq.
    apply (sPUSH [] 3 12 ((40, 2) :: (1, 1) :: repeat (1, 2) 84 ++ (34, 2) :: (1, 1) :: repeat (1, 2) 477 ++ (2195, 2) :: (1, 1) :: repeat (1, 2) 5076 ++ (131714, 2) :: (1, 1) :: repeat (1, 2) 297773 ++ (1424871, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) 1); closearith.
  }
  (* step 198: P TDN *)
  apply (hsteps_trans _ (HB [] 3 1 4 ((10, 2) :: (40, 2) :: (1, 1) :: repeat (1, 2) 84 ++ (34, 2) :: (1, 1) :: repeat (1, 2) 477 ++ (2195, 2) :: (1, 1) :: repeat (1, 2) 5076 ++ (131714, 2) :: (1, 1) :: repeat (1, 2) 297773 ++ (1424871, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) 1)).
  {
    apply (sTDN [] 3 ((10, 2) :: (40, 2) :: (1, 1) :: repeat (1, 2) 84 ++ (34, 2) :: (1, 1) :: repeat (1, 2) 477 ++ (2195, 2) :: (1, 1) :: repeat (1, 2) 5076 ++ (131714, 2) :: (1, 1) :: repeat (1, 2) 297773 ++ (1424871, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) 1).
  }
  (* step 199: sTUP *)
  apply (hsteps_trans _ (HC [] 3 3 2 ((8, 2) :: (40, 2) :: (1, 1) :: repeat (1, 2) 84 ++ (34, 2) :: (1, 1) :: repeat (1, 2) 477 ++ (2195, 2) :: (1, 1) :: repeat (1, 2) 5076 ++ (131714, 2) :: (1, 1) :: repeat (1, 2) 297773 ++ (1424871, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) 1)).
  {
    replace ((8, 2) :: (40, 2) :: (1, 1) :: repeat (1, 2) 84 ++ (34, 2) :: (1, 1) :: repeat (1, 2) 477 ++ (2195, 2) :: (1, 1) :: repeat (1, 2) 5076 ++ (131714, 2) :: (1, 1) :: repeat (1, 2) 297773 ++ (1424871, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) with ((10 - 2, 2) :: (40, 2) :: (1, 1) :: repeat (1, 2) 84 ++ (34, 2) :: (1, 1) :: repeat (1, 2) 477 ++ (2195, 2) :: (1, 1) :: repeat (1, 2) 5076 ++ (131714, 2) :: (1, 1) :: repeat (1, 2) 297773 ++ (1424871, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) by sec_eq.
    apply (sTUP [] 3 4 10 2 ((40, 2) :: (1, 1) :: repeat (1, 2) 84 ++ (34, 2) :: (1, 1) :: repeat (1, 2) 477 ++ (2195, 2) :: (1, 1) :: repeat (1, 2) 5076 ++ (131714, 2) :: (1, 1) :: repeat (1, 2) 297773 ++ (1424871, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) 1); closearith.
  }
  (* step 200: DIPGRIND 3 2 *)
  apply (hsteps_trans _ (HC [] 0 3 2 (repeat (1, 2) 3 ++ (2, 2) :: (40, 2) :: (1, 1) :: repeat (1, 2) 84 ++ (34, 2) :: (1, 1) :: repeat (1, 2) 477 ++ (2195, 2) :: (1, 1) :: repeat (1, 2) 5076 ++ (131714, 2) :: (1, 1) :: repeat (1, 2) 297773 ++ (1424871, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) 1)).
  {
    apply (DIPGRIND 3 2 [] ((40, 2) :: (1, 1) :: repeat (1, 2) 84 ++ (34, 2) :: (1, 1) :: repeat (1, 2) 477 ++ (2195, 2) :: (1, 1) :: repeat (1, 2) 5076 ++ (131714, 2) :: (1, 1) :: repeat (1, 2) 297773 ++ (1424871, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) 1); closearith.
  }
  (* step 201: P PUSHX *)
  apply (hsteps_trans _ (HB [] 1 1 7 (repeat (1, 2) 3 ++ (2, 2) :: (40, 2) :: (1, 1) :: repeat (1, 2) 84 ++ (34, 2) :: (1, 1) :: repeat (1, 2) 477 ++ (2195, 2) :: (1, 1) :: repeat (1, 2) 5076 ++ (131714, 2) :: (1, 1) :: repeat (1, 2) 297773 ++ (1424871, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) 1)).
  {
    exact (hsteps_step _ _ _ (hPUSHX (repeat (1, 2) 3 ++ (2, 2) :: (40, 2) :: (1, 1) :: repeat (1, 2) 84 ++ (34, 2) :: (1, 1) :: repeat (1, 2) 477 ++ (2195, 2) :: (1, 1) :: repeat (1, 2) 5076 ++ (131714, 2) :: (1, 1) :: repeat (1, 2) 297773 ++ (1424871, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) 1) (hsteps_refl _)).
  }
  (* step 202: M pop12 (3,) *)
  apply (hsteps_trans _ (HB [] 4 1 13 ((2, 2) :: (40, 2) :: (1, 1) :: repeat (1, 2) 84 ++ (34, 2) :: (1, 1) :: repeat (1, 2) 477 ++ (2195, 2) :: (1, 1) :: repeat (1, 2) 5076 ++ (131714, 2) :: (1, 1) :: repeat (1, 2) 297773 ++ (1424871, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) 1)).
  {
    apply (pop12 3 [] 1 7 ((2, 2) :: (40, 2) :: (1, 1) :: repeat (1, 2) 84 ++ (34, 2) :: (1, 1) :: repeat (1, 2) 477 ++ (2195, 2) :: (1, 1) :: repeat (1, 2) 5076 ++ (131714, 2) :: (1, 1) :: repeat (1, 2) 297773 ++ (1424871, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) 1); closearith.
  }
  (* step 203: P TUP2_1 *)
  apply (hsteps_trans _ (HC [5] 13 1 2 ((38, 2) :: (1, 1) :: repeat (1, 2) 84 ++ (34, 2) :: (1, 1) :: repeat (1, 2) 477 ++ (2195, 2) :: (1, 1) :: repeat (1, 2) 5076 ++ (131714, 2) :: (1, 1) :: repeat (1, 2) 297773 ++ (1424871, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) 1)).
  {
    replace ((38, 2) :: (1, 1) :: repeat (1, 2) 84 ++ (34, 2) :: (1, 1) :: repeat (1, 2) 477 ++ (2195, 2) :: (1, 1) :: repeat (1, 2) 5076 ++ (131714, 2) :: (1, 1) :: repeat (1, 2) 297773 ++ (1424871, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) with ((40 - 2, 2) :: (1, 1) :: repeat (1, 2) 84 ++ (34, 2) :: (1, 1) :: repeat (1, 2) 477 ++ (2195, 2) :: (1, 1) :: repeat (1, 2) 5076 ++ (131714, 2) :: (1, 1) :: repeat (1, 2) 297773 ++ (1424871, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) by sec_eq.
    apply (sTUP2_1 [] 4 12 40 ((1, 1) :: repeat (1, 2) 84 ++ (34, 2) :: (1, 1) :: repeat (1, 2) 477 ++ (2195, 2) :: (1, 1) :: repeat (1, 2) 5076 ++ (131714, 2) :: (1, 1) :: repeat (1, 2) 297773 ++ (1424871, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) 1); closearith.
  }
  (* step 204: P TDN *)
  apply (hsteps_trans _ (HB [5] 13 1 4 ((38, 2) :: (1, 1) :: repeat (1, 2) 84 ++ (34, 2) :: (1, 1) :: repeat (1, 2) 477 ++ (2195, 2) :: (1, 1) :: repeat (1, 2) 5076 ++ (131714, 2) :: (1, 1) :: repeat (1, 2) 297773 ++ (1424871, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) 1)).
  {
    apply (sTDN [5] 13 ((38, 2) :: (1, 1) :: repeat (1, 2) 84 ++ (34, 2) :: (1, 1) :: repeat (1, 2) 477 ++ (2195, 2) :: (1, 1) :: repeat (1, 2) 5076 ++ (131714, 2) :: (1, 1) :: repeat (1, 2) 297773 ++ (1424871, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) 1).
  }
  (* step 205: sTUP *)
  apply (hsteps_trans _ (HC [5] 13 3 2 ((36, 2) :: (1, 1) :: repeat (1, 2) 84 ++ (34, 2) :: (1, 1) :: repeat (1, 2) 477 ++ (2195, 2) :: (1, 1) :: repeat (1, 2) 5076 ++ (131714, 2) :: (1, 1) :: repeat (1, 2) 297773 ++ (1424871, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) 1)).
  {
    replace ((36, 2) :: (1, 1) :: repeat (1, 2) 84 ++ (34, 2) :: (1, 1) :: repeat (1, 2) 477 ++ (2195, 2) :: (1, 1) :: repeat (1, 2) 5076 ++ (131714, 2) :: (1, 1) :: repeat (1, 2) 297773 ++ (1424871, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) with ((38 - 2, 2) :: (1, 1) :: repeat (1, 2) 84 ++ (34, 2) :: (1, 1) :: repeat (1, 2) 477 ++ (2195, 2) :: (1, 1) :: repeat (1, 2) 5076 ++ (131714, 2) :: (1, 1) :: repeat (1, 2) 297773 ++ (1424871, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) by sec_eq.
    apply (sTUP [5] 13 4 38 2 ((1, 1) :: repeat (1, 2) 84 ++ (34, 2) :: (1, 1) :: repeat (1, 2) 477 ++ (2195, 2) :: (1, 1) :: repeat (1, 2) 5076 ++ (131714, 2) :: (1, 1) :: repeat (1, 2) 297773 ++ (1424871, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) 1); closearith.
  }
  (* step 206: DIPGRIND 13 10 *)
  apply (hsteps_trans _ (HC [5] 0 3 2 (repeat (1, 2) 13 ++ (10, 2) :: (1, 1) :: repeat (1, 2) 84 ++ (34, 2) :: (1, 1) :: repeat (1, 2) 477 ++ (2195, 2) :: (1, 1) :: repeat (1, 2) 5076 ++ (131714, 2) :: (1, 1) :: repeat (1, 2) 297773 ++ (1424871, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) 1)).
  {
    apply (DIPGRIND 13 10 [5] ((1, 1) :: repeat (1, 2) 84 ++ (34, 2) :: (1, 1) :: repeat (1, 2) 477 ++ (2195, 2) :: (1, 1) :: repeat (1, 2) 5076 ++ (131714, 2) :: (1, 1) :: repeat (1, 2) 297773 ++ (1424871, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) 1); closearith.
  }
  (* step 207: P PX2Bgen *)
  apply (hsteps_trans _ (HB [0] 3 1 2 (repeat (1, 2) 1 ++ (1, 1) :: repeat (1, 2) 15 ++ (10, 2) :: (1, 1) :: repeat (1, 2) 84 ++ (34, 2) :: (1, 1) :: repeat (1, 2) 477 ++ (2195, 2) :: (1, 1) :: repeat (1, 2) 5076 ++ (131714, 2) :: (1, 1) :: repeat (1, 2) 297773 ++ (1424871, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) 1)).
  {
    exact (hsteps_step _ _ _ (hPX2Bgen 0 (repeat (1, 2) 13 ++ (10, 2) :: (1, 1) :: repeat (1, 2) 84 ++ (34, 2) :: (1, 1) :: repeat (1, 2) 477 ++ (2195, 2) :: (1, 1) :: repeat (1, 2) 5076 ++ (131714, 2) :: (1, 1) :: repeat (1, 2) 297773 ++ (1424871, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) 1) (hsteps_refl _)).
  }
  (* step 208: M pop12 (1,) *)
  apply (hsteps_trans _ (HB [0] 4 1 4 ((1, 1) :: repeat (1, 2) 15 ++ (10, 2) :: (1, 1) :: repeat (1, 2) 84 ++ (34, 2) :: (1, 1) :: repeat (1, 2) 477 ++ (2195, 2) :: (1, 1) :: repeat (1, 2) 5076 ++ (131714, 2) :: (1, 1) :: repeat (1, 2) 297773 ++ (1424871, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) 1)).
  {
    apply (pop12 1 [0] 3 2 ((1, 1) :: repeat (1, 2) 15 ++ (10, 2) :: (1, 1) :: repeat (1, 2) 84 ++ (34, 2) :: (1, 1) :: repeat (1, 2) 477 ++ (2195, 2) :: (1, 1) :: repeat (1, 2) 5076 ++ (131714, 2) :: (1, 1) :: repeat (1, 2) 297773 ++ (1424871, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) 1); closearith.
  }
  (* step 209: P POP *)
  apply (hsteps_trans _ (HB [0] 5 1 5 (repeat (1, 2) 15 ++ (10, 2) :: (1, 1) :: repeat (1, 2) 84 ++ (34, 2) :: (1, 1) :: repeat (1, 2) 477 ++ (2195, 2) :: (1, 1) :: repeat (1, 2) 5076 ++ (131714, 2) :: (1, 1) :: repeat (1, 2) 297773 ++ (1424871, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) 1)).
  {
    apply (sPOP1 [0] 4 4 (repeat (1, 2) 15 ++ (10, 2) :: (1, 1) :: repeat (1, 2) 84 ++ (34, 2) :: (1, 1) :: repeat (1, 2) 477 ++ (2195, 2) :: (1, 1) :: repeat (1, 2) 5076 ++ (131714, 2) :: (1, 1) :: repeat (1, 2) 297773 ++ (1424871, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) 1); closearith.
  }
  (* step 210: M pop12 (15,) *)
  apply (hsteps_trans _ (HB [0] 20 1 35 ((10, 2) :: (1, 1) :: repeat (1, 2) 84 ++ (34, 2) :: (1, 1) :: repeat (1, 2) 477 ++ (2195, 2) :: (1, 1) :: repeat (1, 2) 5076 ++ (131714, 2) :: (1, 1) :: repeat (1, 2) 297773 ++ (1424871, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) 1)).
  {
    apply (pop12 15 [0] 5 5 ((10, 2) :: (1, 1) :: repeat (1, 2) 84 ++ (34, 2) :: (1, 1) :: repeat (1, 2) 477 ++ (2195, 2) :: (1, 1) :: repeat (1, 2) 5076 ++ (131714, 2) :: (1, 1) :: repeat (1, 2) 297773 ++ (1424871, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) 1); closearith.
  }
  (* step 211: sTUP *)
  apply (hsteps_trans _ (HC [0] 20 34 2 ((8, 2) :: (1, 1) :: repeat (1, 2) 84 ++ (34, 2) :: (1, 1) :: repeat (1, 2) 477 ++ (2195, 2) :: (1, 1) :: repeat (1, 2) 5076 ++ (131714, 2) :: (1, 1) :: repeat (1, 2) 297773 ++ (1424871, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) 1)).
  {
    replace ((8, 2) :: (1, 1) :: repeat (1, 2) 84 ++ (34, 2) :: (1, 1) :: repeat (1, 2) 477 ++ (2195, 2) :: (1, 1) :: repeat (1, 2) 5076 ++ (131714, 2) :: (1, 1) :: repeat (1, 2) 297773 ++ (1424871, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) with ((10 - 2, 2) :: (1, 1) :: repeat (1, 2) 84 ++ (34, 2) :: (1, 1) :: repeat (1, 2) 477 ++ (2195, 2) :: (1, 1) :: repeat (1, 2) 5076 ++ (131714, 2) :: (1, 1) :: repeat (1, 2) 297773 ++ (1424871, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) by sec_eq.
    apply (sTUP [0] 20 35 10 2 ((1, 1) :: repeat (1, 2) 84 ++ (34, 2) :: (1, 1) :: repeat (1, 2) 477 ++ (2195, 2) :: (1, 1) :: repeat (1, 2) 5076 ++ (131714, 2) :: (1, 1) :: repeat (1, 2) 297773 ++ (1424871, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) 1); closearith.
  }
  (* step 212: hGRIND_even 15 *)
  apply (hsteps_trans _ (HB [0] 19 1 34 ((2, 2) :: (8, 2) :: (1, 1) :: repeat (1, 2) 84 ++ (34, 2) :: (1, 1) :: repeat (1, 2) 477 ++ (2195, 2) :: (1, 1) :: repeat (1, 2) 5076 ++ (131714, 2) :: (1, 1) :: repeat (1, 2) 297773 ++ (1424871, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) 1)).
  {
    apply (hGRIND_even 15 [0] 19 ((8, 2) :: (1, 1) :: repeat (1, 2) 84 ++ (34, 2) :: (1, 1) :: repeat (1, 2) 477 ++ (2195, 2) :: (1, 1) :: repeat (1, 2) 5076 ++ (131714, 2) :: (1, 1) :: repeat (1, 2) 297773 ++ (1424871, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) 1); closearith.
  }
  (* step 213: P TUP2_1 *)
  apply (hsteps_trans _ (HC [20; 0] 34 1 2 ((6, 2) :: (1, 1) :: repeat (1, 2) 84 ++ (34, 2) :: (1, 1) :: repeat (1, 2) 477 ++ (2195, 2) :: (1, 1) :: repeat (1, 2) 5076 ++ (131714, 2) :: (1, 1) :: repeat (1, 2) 297773 ++ (1424871, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) 1)).
  {
    replace ((6, 2) :: (1, 1) :: repeat (1, 2) 84 ++ (34, 2) :: (1, 1) :: repeat (1, 2) 477 ++ (2195, 2) :: (1, 1) :: repeat (1, 2) 5076 ++ (131714, 2) :: (1, 1) :: repeat (1, 2) 297773 ++ (1424871, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) with ((8 - 2, 2) :: (1, 1) :: repeat (1, 2) 84 ++ (34, 2) :: (1, 1) :: repeat (1, 2) 477 ++ (2195, 2) :: (1, 1) :: repeat (1, 2) 5076 ++ (131714, 2) :: (1, 1) :: repeat (1, 2) 297773 ++ (1424871, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) by sec_eq.
    apply (sTUP2_1 [0] 19 33 8 ((1, 1) :: repeat (1, 2) 84 ++ (34, 2) :: (1, 1) :: repeat (1, 2) 477 ++ (2195, 2) :: (1, 1) :: repeat (1, 2) 5076 ++ (131714, 2) :: (1, 1) :: repeat (1, 2) 297773 ++ (1424871, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) 1); closearith.
  }
  (* step 214: P TDN *)
  apply (hsteps_trans _ (HB [20; 0] 34 1 4 ((6, 2) :: (1, 1) :: repeat (1, 2) 84 ++ (34, 2) :: (1, 1) :: repeat (1, 2) 477 ++ (2195, 2) :: (1, 1) :: repeat (1, 2) 5076 ++ (131714, 2) :: (1, 1) :: repeat (1, 2) 297773 ++ (1424871, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) 1)).
  {
    apply (sTDN [20; 0] 34 ((6, 2) :: (1, 1) :: repeat (1, 2) 84 ++ (34, 2) :: (1, 1) :: repeat (1, 2) 477 ++ (2195, 2) :: (1, 1) :: repeat (1, 2) 5076 ++ (131714, 2) :: (1, 1) :: repeat (1, 2) 297773 ++ (1424871, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) 1).
  }
  (* step 215: sTUP *)
  apply (hsteps_trans _ (HC [20; 0] 34 3 2 ((4, 2) :: (1, 1) :: repeat (1, 2) 84 ++ (34, 2) :: (1, 1) :: repeat (1, 2) 477 ++ (2195, 2) :: (1, 1) :: repeat (1, 2) 5076 ++ (131714, 2) :: (1, 1) :: repeat (1, 2) 297773 ++ (1424871, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) 1)).
  {
    replace ((4, 2) :: (1, 1) :: repeat (1, 2) 84 ++ (34, 2) :: (1, 1) :: repeat (1, 2) 477 ++ (2195, 2) :: (1, 1) :: repeat (1, 2) 5076 ++ (131714, 2) :: (1, 1) :: repeat (1, 2) 297773 ++ (1424871, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) with ((6 - 2, 2) :: (1, 1) :: repeat (1, 2) 84 ++ (34, 2) :: (1, 1) :: repeat (1, 2) 477 ++ (2195, 2) :: (1, 1) :: repeat (1, 2) 5076 ++ (131714, 2) :: (1, 1) :: repeat (1, 2) 297773 ++ (1424871, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) by sec_eq.
    apply (sTUP [20; 0] 34 4 6 2 ((1, 1) :: repeat (1, 2) 84 ++ (34, 2) :: (1, 1) :: repeat (1, 2) 477 ++ (2195, 2) :: (1, 1) :: repeat (1, 2) 5076 ++ (131714, 2) :: (1, 1) :: repeat (1, 2) 297773 ++ (1424871, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) 1); closearith.
  }
  (* step 216: CLEANG_even 1 *)
  apply (hsteps_trans _ (HB [20; 0] 34 1 8 ((2, 2) :: (1, 1) :: repeat (1, 2) 84 ++ (34, 2) :: (1, 1) :: repeat (1, 2) 477 ++ (2195, 2) :: (1, 1) :: repeat (1, 2) 5076 ++ (131714, 2) :: (1, 1) :: repeat (1, 2) 297773 ++ (1424871, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) 1)).
  {
    apply (CLEANG_even 1 [20; 0] 34 ((1, 1) :: repeat (1, 2) 84 ++ (34, 2) :: (1, 1) :: repeat (1, 2) 477 ++ (2195, 2) :: (1, 1) :: repeat (1, 2) 5076 ++ (131714, 2) :: (1, 1) :: repeat (1, 2) 297773 ++ (1424871, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) 1); closearith.
  }
  (* step 217: P TRANS2_1 *)
  apply (hsteps_trans _ (HB [35; 20; 0] 9 1 3 (repeat (1, 2) 84 ++ (34, 2) :: (1, 1) :: repeat (1, 2) 477 ++ (2195, 2) :: (1, 1) :: repeat (1, 2) 5076 ++ (131714, 2) :: (1, 1) :: repeat (1, 2) 297773 ++ (1424871, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) 1)).
  {
    apply (sTRANS2_1 [20; 0] 34 7 1 (repeat (1, 2) 84 ++ (34, 2) :: (1, 1) :: repeat (1, 2) 477 ++ (2195, 2) :: (1, 1) :: repeat (1, 2) 5076 ++ (131714, 2) :: (1, 1) :: repeat (1, 2) 297773 ++ (1424871, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) 1); closearith.
  }
  (* step 218: M pop12 (84,) *)
  apply (hsteps_trans _ (HB [35; 20; 0] 93 1 171 ((34, 2) :: (1, 1) :: repeat (1, 2) 477 ++ (2195, 2) :: (1, 1) :: repeat (1, 2) 5076 ++ (131714, 2) :: (1, 1) :: repeat (1, 2) 297773 ++ (1424871, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) 1)).
  {
    apply (pop12 84 [35; 20; 0] 9 3 ((34, 2) :: (1, 1) :: repeat (1, 2) 477 ++ (2195, 2) :: (1, 1) :: repeat (1, 2) 5076 ++ (131714, 2) :: (1, 1) :: repeat (1, 2) 297773 ++ (1424871, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) 1); closearith.
  }
  (* step 219: sTUP *)
  apply (hsteps_trans _ (HC [35; 20; 0] 93 170 2 ((32, 2) :: (1, 1) :: repeat (1, 2) 477 ++ (2195, 2) :: (1, 1) :: repeat (1, 2) 5076 ++ (131714, 2) :: (1, 1) :: repeat (1, 2) 297773 ++ (1424871, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) 1)).
  {
    replace ((32, 2) :: (1, 1) :: repeat (1, 2) 477 ++ (2195, 2) :: (1, 1) :: repeat (1, 2) 5076 ++ (131714, 2) :: (1, 1) :: repeat (1, 2) 297773 ++ (1424871, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) with ((34 - 2, 2) :: (1, 1) :: repeat (1, 2) 477 ++ (2195, 2) :: (1, 1) :: repeat (1, 2) 5076 ++ (131714, 2) :: (1, 1) :: repeat (1, 2) 297773 ++ (1424871, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) by sec_eq.
    apply (sTUP [35; 20; 0] 93 171 34 2 ((1, 1) :: repeat (1, 2) 477 ++ (2195, 2) :: (1, 1) :: repeat (1, 2) 5076 ++ (131714, 2) :: (1, 1) :: repeat (1, 2) 297773 ++ (1424871, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) 1); closearith.
  }
  (* step 220: hGRIND_even 83 *)
  apply (hsteps_trans _ (HB [35; 20; 0] 92 1 170 ((2, 2) :: (32, 2) :: (1, 1) :: repeat (1, 2) 477 ++ (2195, 2) :: (1, 1) :: repeat (1, 2) 5076 ++ (131714, 2) :: (1, 1) :: repeat (1, 2) 297773 ++ (1424871, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) 1)).
  {
    apply (hGRIND_even 83 [35; 20; 0] 92 ((32, 2) :: (1, 1) :: repeat (1, 2) 477 ++ (2195, 2) :: (1, 1) :: repeat (1, 2) 5076 ++ (131714, 2) :: (1, 1) :: repeat (1, 2) 297773 ++ (1424871, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) 1); closearith.
  }
  (* step 221: P TUP2_1 *)
  apply (hsteps_trans _ (HC [93; 35; 20; 0] 170 1 2 ((30, 2) :: (1, 1) :: repeat (1, 2) 477 ++ (2195, 2) :: (1, 1) :: repeat (1, 2) 5076 ++ (131714, 2) :: (1, 1) :: repeat (1, 2) 297773 ++ (1424871, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) 1)).
  {
    replace ((30, 2) :: (1, 1) :: repeat (1, 2) 477 ++ (2195, 2) :: (1, 1) :: repeat (1, 2) 5076 ++ (131714, 2) :: (1, 1) :: repeat (1, 2) 297773 ++ (1424871, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) with ((32 - 2, 2) :: (1, 1) :: repeat (1, 2) 477 ++ (2195, 2) :: (1, 1) :: repeat (1, 2) 5076 ++ (131714, 2) :: (1, 1) :: repeat (1, 2) 297773 ++ (1424871, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) by sec_eq.
    apply (sTUP2_1 [35; 20; 0] 92 169 32 ((1, 1) :: repeat (1, 2) 477 ++ (2195, 2) :: (1, 1) :: repeat (1, 2) 5076 ++ (131714, 2) :: (1, 1) :: repeat (1, 2) 297773 ++ (1424871, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) 1); closearith.
  }
  (* step 222: P TDN *)
  apply (hsteps_trans _ (HB [93; 35; 20; 0] 170 1 4 ((30, 2) :: (1, 1) :: repeat (1, 2) 477 ++ (2195, 2) :: (1, 1) :: repeat (1, 2) 5076 ++ (131714, 2) :: (1, 1) :: repeat (1, 2) 297773 ++ (1424871, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) 1)).
  {
    apply (sTDN [93; 35; 20; 0] 170 ((30, 2) :: (1, 1) :: repeat (1, 2) 477 ++ (2195, 2) :: (1, 1) :: repeat (1, 2) 5076 ++ (131714, 2) :: (1, 1) :: repeat (1, 2) 297773 ++ (1424871, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) 1).
  }
  (* step 223: sTUP *)
  apply (hsteps_trans _ (HC [93; 35; 20; 0] 170 3 2 ((28, 2) :: (1, 1) :: repeat (1, 2) 477 ++ (2195, 2) :: (1, 1) :: repeat (1, 2) 5076 ++ (131714, 2) :: (1, 1) :: repeat (1, 2) 297773 ++ (1424871, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) 1)).
  {
    replace ((28, 2) :: (1, 1) :: repeat (1, 2) 477 ++ (2195, 2) :: (1, 1) :: repeat (1, 2) 5076 ++ (131714, 2) :: (1, 1) :: repeat (1, 2) 297773 ++ (1424871, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) with ((30 - 2, 2) :: (1, 1) :: repeat (1, 2) 477 ++ (2195, 2) :: (1, 1) :: repeat (1, 2) 5076 ++ (131714, 2) :: (1, 1) :: repeat (1, 2) 297773 ++ (1424871, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) by sec_eq.
    apply (sTUP [93; 35; 20; 0] 170 4 30 2 ((1, 1) :: repeat (1, 2) 477 ++ (2195, 2) :: (1, 1) :: repeat (1, 2) 5076 ++ (131714, 2) :: (1, 1) :: repeat (1, 2) 297773 ++ (1424871, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) 1); closearith.
  }
  (* step 224: CLEANG_even 13 *)
  apply (CLEANG_even 13 [93; 35; 20; 0] 170 ((1, 1) :: repeat (1, 2) 477 ++ (2195, 2) :: (1, 1) :: repeat (1, 2) 5076 ++ (131714, 2) :: (1, 1) :: repeat (1, 2) 297773 ++ (1424871, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) 1); closearith.
Qed.

(* CASCADE56e: steps 225-280 of the CASCADE56 chain. *)
Lemma CASCADE56e : forall w,
  hsteps (HB [93; 35; 20; 0] 170 1 32 ((2, 2) :: (1, 1) :: repeat (1, 2) 477 ++ (2195, 2) :: (1, 1) :: repeat (1, 2) 5076 ++ (131714, 2) :: (1, 1) :: repeat (1, 2) 297773 ++ (1424871, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) 1)
         (HC [1123; 365; 245; 40; 14; 5] 1918 1 2 ((273, 2) :: (1, 1) :: repeat (1, 2) 5076 ++ (131714, 2) :: (1, 1) :: repeat (1, 2) 297773 ++ (1424871, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) 1).
Proof.
  intro w.
  (* step 225: P TRANS2_1 *)
  apply (hsteps_trans _ (HB [171; 93; 35; 20; 0] 33 1 3 (repeat (1, 2) 477 ++ (2195, 2) :: (1, 1) :: repeat (1, 2) 5076 ++ (131714, 2) :: (1, 1) :: repeat (1, 2) 297773 ++ (1424871, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) 1)).
  {
    apply (sTRANS2_1 [93; 35; 20; 0] 170 31 1 (repeat (1, 2) 477 ++ (2195, 2) :: (1, 1) :: repeat (1, 2) 5076 ++ (131714, 2) :: (1, 1) :: repeat (1, 2) 297773 ++ (1424871, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) 1); closearith.
  }
  (* step 226: M pop12 (477,) *)
  apply (hsteps_trans _ (HB [171; 93; 35; 20; 0] 510 1 957 ((2195, 2) :: (1, 1) :: repeat (1, 2) 5076 ++ (131714, 2) :: (1, 1) :: repeat (1, 2) 297773 ++ (1424871, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) 1)).
  {
    apply (pop12 477 [171; 93; 35; 20; 0] 33 3 ((2195, 2) :: (1, 1) :: repeat (1, 2) 5076 ++ (131714, 2) :: (1, 1) :: repeat (1, 2) 297773 ++ (1424871, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) 1); closearith.
  }
  (* step 227: sTUP *)
  apply (hsteps_trans _ (HC [171; 93; 35; 20; 0] 510 956 2 ((2193, 2) :: (1, 1) :: repeat (1, 2) 5076 ++ (131714, 2) :: (1, 1) :: repeat (1, 2) 297773 ++ (1424871, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) 1)).
  {
    replace ((2193, 2) :: (1, 1) :: repeat (1, 2) 5076 ++ (131714, 2) :: (1, 1) :: repeat (1, 2) 297773 ++ (1424871, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) with ((2195 - 2, 2) :: (1, 1) :: repeat (1, 2) 5076 ++ (131714, 2) :: (1, 1) :: repeat (1, 2) 297773 ++ (1424871, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) by sec_eq.
    apply (sTUP [171; 93; 35; 20; 0] 510 957 2195 2 ((1, 1) :: repeat (1, 2) 5076 ++ (131714, 2) :: (1, 1) :: repeat (1, 2) 297773 ++ (1424871, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) 1); closearith.
  }
  (* step 228: hGRIND_even 476 *)
  apply (hsteps_trans _ (HB [171; 93; 35; 20; 0] 509 1 956 ((2, 2) :: (2193, 2) :: (1, 1) :: repeat (1, 2) 5076 ++ (131714, 2) :: (1, 1) :: repeat (1, 2) 297773 ++ (1424871, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) 1)).
  {
    apply (hGRIND_even 476 [171; 93; 35; 20; 0] 509 ((2193, 2) :: (1, 1) :: repeat (1, 2) 5076 ++ (131714, 2) :: (1, 1) :: repeat (1, 2) 297773 ++ (1424871, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) 1); closearith.
  }
  (* step 229: P TUP2_1 *)
  apply (hsteps_trans _ (HC [510; 171; 93; 35; 20; 0] 956 1 2 ((2191, 2) :: (1, 1) :: repeat (1, 2) 5076 ++ (131714, 2) :: (1, 1) :: repeat (1, 2) 297773 ++ (1424871, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) 1)).
  {
    replace ((2191, 2) :: (1, 1) :: repeat (1, 2) 5076 ++ (131714, 2) :: (1, 1) :: repeat (1, 2) 297773 ++ (1424871, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) with ((2193 - 2, 2) :: (1, 1) :: repeat (1, 2) 5076 ++ (131714, 2) :: (1, 1) :: repeat (1, 2) 297773 ++ (1424871, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) by sec_eq.
    apply (sTUP2_1 [171; 93; 35; 20; 0] 509 955 2193 ((1, 1) :: repeat (1, 2) 5076 ++ (131714, 2) :: (1, 1) :: repeat (1, 2) 297773 ++ (1424871, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) 1); closearith.
  }
  (* step 230: P TDN *)
  apply (hsteps_trans _ (HB [510; 171; 93; 35; 20; 0] 956 1 4 ((2191, 2) :: (1, 1) :: repeat (1, 2) 5076 ++ (131714, 2) :: (1, 1) :: repeat (1, 2) 297773 ++ (1424871, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) 1)).
  {
    apply (sTDN [510; 171; 93; 35; 20; 0] 956 ((2191, 2) :: (1, 1) :: repeat (1, 2) 5076 ++ (131714, 2) :: (1, 1) :: repeat (1, 2) 297773 ++ (1424871, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) 1).
  }
  (* step 231: sTUP *)
  apply (hsteps_trans _ (HC [510; 171; 93; 35; 20; 0] 956 3 2 ((2189, 2) :: (1, 1) :: repeat (1, 2) 5076 ++ (131714, 2) :: (1, 1) :: repeat (1, 2) 297773 ++ (1424871, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) 1)).
  {
    replace ((2189, 2) :: (1, 1) :: repeat (1, 2) 5076 ++ (131714, 2) :: (1, 1) :: repeat (1, 2) 297773 ++ (1424871, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) with ((2191 - 2, 2) :: (1, 1) :: repeat (1, 2) 5076 ++ (131714, 2) :: (1, 1) :: repeat (1, 2) 297773 ++ (1424871, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) by sec_eq.
    apply (sTUP [510; 171; 93; 35; 20; 0] 956 4 2191 2 ((1, 1) :: repeat (1, 2) 5076 ++ (131714, 2) :: (1, 1) :: repeat (1, 2) 297773 ++ (1424871, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) 1); closearith.
  }
  (* step 232: DIPGRIND 956 277 *)
  apply (hsteps_trans _ (HC [510; 171; 93; 35; 20; 0] 0 3 2 (repeat (1, 2) 956 ++ (277, 2) :: (1, 1) :: repeat (1, 2) 5076 ++ (131714, 2) :: (1, 1) :: repeat (1, 2) 297773 ++ (1424871, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) 1)).
  {
    apply (DIPGRIND 956 277 [510; 171; 93; 35; 20; 0] ((1, 1) :: repeat (1, 2) 5076 ++ (131714, 2) :: (1, 1) :: repeat (1, 2) 297773 ++ (1424871, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) 1); closearith.
  }
  (* step 233: P PX2A *)
  apply (hsteps_trans _ (HC [93; 35; 20; 0] 170 508 2 ((1, 1) :: repeat (1, 2) 958 ++ (277, 2) :: (1, 1) :: repeat (1, 2) 5076 ++ (131714, 2) :: (1, 1) :: repeat (1, 2) 297773 ++ (1424871, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) 1)).
  {
    exact (hsteps_step _ _ _ (hPX2A 507 170 [93; 35; 20; 0] (repeat (1, 2) 956 ++ (277, 2) :: (1, 1) :: repeat (1, 2) 5076 ++ (131714, 2) :: (1, 1) :: repeat (1, 2) 297773 ++ (1424871, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) 1) (hsteps_refl _)).
  }
  (* step 234: P PUSH *)
  apply (hsteps_trans _ (HC [93; 35; 20; 0] 169 1 2 ((506, 2) :: (1, 1) :: repeat (1, 2) 958 ++ (277, 2) :: (1, 1) :: repeat (1, 2) 5076 ++ (131714, 2) :: (1, 1) :: repeat (1, 2) 297773 ++ (1424871, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) 1)).
  {
    replace ((506, 2) :: (1, 1) :: repeat (1, 2) 958 ++ (277, 2) :: (1, 1) :: repeat (1, 2) 5076 ++ (131714, 2) :: (1, 1) :: repeat (1, 2) 297773 ++ (1424871, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) with ((508 - 2, 2) :: (1, 1) :: repeat (1, 2) 958 ++ (277, 2) :: (1, 1) :: repeat (1, 2) 5076 ++ (131714, 2) :: (1, 1) :: repeat (1, 2) 297773 ++ (1424871, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) by sec_eq.
    apply (sPUSH [93; 35; 20; 0] 169 508 ((1, 1) :: repeat (1, 2) 958 ++ (277, 2) :: (1, 1) :: repeat (1, 2) 5076 ++ (131714, 2) :: (1, 1) :: repeat (1, 2) 297773 ++ (1424871, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) 1); closearith.
  }
  (* step 235: P TDN *)
  apply (hsteps_trans _ (HB [93; 35; 20; 0] 169 1 4 ((506, 2) :: (1, 1) :: repeat (1, 2) 958 ++ (277, 2) :: (1, 1) :: repeat (1, 2) 5076 ++ (131714, 2) :: (1, 1) :: repeat (1, 2) 297773 ++ (1424871, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) 1)).
  {
    apply (sTDN [93; 35; 20; 0] 169 ((506, 2) :: (1, 1) :: repeat (1, 2) 958 ++ (277, 2) :: (1, 1) :: repeat (1, 2) 5076 ++ (131714, 2) :: (1, 1) :: repeat (1, 2) 297773 ++ (1424871, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) 1).
  }
  (* step 236: sTUP *)
  apply (hsteps_trans _ (HC [93; 35; 20; 0] 169 3 2 ((504, 2) :: (1, 1) :: repeat (1, 2) 958 ++ (277, 2) :: (1, 1) :: repeat (1, 2) 5076 ++ (131714, 2) :: (1, 1) :: repeat (1, 2) 297773 ++ (1424871, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) 1)).
  {
    replace ((504, 2) :: (1, 1) :: repeat (1, 2) 958 ++ (277, 2) :: (1, 1) :: repeat (1, 2) 5076 ++ (131714, 2) :: (1, 1) :: repeat (1, 2) 297773 ++ (1424871, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) with ((506 - 2, 2) :: (1, 1) :: repeat (1, 2) 958 ++ (277, 2) :: (1, 1) :: repeat (1, 2) 5076 ++ (131714, 2) :: (1, 1) :: repeat (1, 2) 297773 ++ (1424871, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) by sec_eq.
    apply (sTUP [93; 35; 20; 0] 169 4 506 2 ((1, 1) :: repeat (1, 2) 958 ++ (277, 2) :: (1, 1) :: repeat (1, 2) 5076 ++ (131714, 2) :: (1, 1) :: repeat (1, 2) 297773 ++ (1424871, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) 1); closearith.
  }
  (* step 237: DIPGRIND 169 166 *)
  apply (hsteps_trans _ (HC [93; 35; 20; 0] 0 3 2 (repeat (1, 2) 169 ++ (166, 2) :: (1, 1) :: repeat (1, 2) 958 ++ (277, 2) :: (1, 1) :: repeat (1, 2) 5076 ++ (131714, 2) :: (1, 1) :: repeat (1, 2) 297773 ++ (1424871, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) 1)).
  {
    apply (DIPGRIND 169 166 [93; 35; 20; 0] ((1, 1) :: repeat (1, 2) 958 ++ (277, 2) :: (1, 1) :: repeat (1, 2) 5076 ++ (131714, 2) :: (1, 1) :: repeat (1, 2) 297773 ++ (1424871, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) 1); closearith.
  }
  (* step 238: P PX2A *)
  apply (hsteps_trans _ (HC [20; 0] 34 91 2 ((1, 1) :: repeat (1, 2) 171 ++ (166, 2) :: (1, 1) :: repeat (1, 2) 958 ++ (277, 2) :: (1, 1) :: repeat (1, 2) 5076 ++ (131714, 2) :: (1, 1) :: repeat (1, 2) 297773 ++ (1424871, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) 1)).
  {
    exact (hsteps_step _ _ _ (hPX2A 90 34 [20; 0] (repeat (1, 2) 169 ++ (166, 2) :: (1, 1) :: repeat (1, 2) 958 ++ (277, 2) :: (1, 1) :: repeat (1, 2) 5076 ++ (131714, 2) :: (1, 1) :: repeat (1, 2) 297773 ++ (1424871, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) 1) (hsteps_refl _)).
  }
  (* step 239: P PUSH *)
  apply (hsteps_trans _ (HC [20; 0] 33 1 2 ((89, 2) :: (1, 1) :: repeat (1, 2) 171 ++ (166, 2) :: (1, 1) :: repeat (1, 2) 958 ++ (277, 2) :: (1, 1) :: repeat (1, 2) 5076 ++ (131714, 2) :: (1, 1) :: repeat (1, 2) 297773 ++ (1424871, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) 1)).
  {
    replace ((89, 2) :: (1, 1) :: repeat (1, 2) 171 ++ (166, 2) :: (1, 1) :: repeat (1, 2) 958 ++ (277, 2) :: (1, 1) :: repeat (1, 2) 5076 ++ (131714, 2) :: (1, 1) :: repeat (1, 2) 297773 ++ (1424871, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) with ((91 - 2, 2) :: (1, 1) :: repeat (1, 2) 171 ++ (166, 2) :: (1, 1) :: repeat (1, 2) 958 ++ (277, 2) :: (1, 1) :: repeat (1, 2) 5076 ++ (131714, 2) :: (1, 1) :: repeat (1, 2) 297773 ++ (1424871, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) by sec_eq.
    apply (sPUSH [20; 0] 33 91 ((1, 1) :: repeat (1, 2) 171 ++ (166, 2) :: (1, 1) :: repeat (1, 2) 958 ++ (277, 2) :: (1, 1) :: repeat (1, 2) 5076 ++ (131714, 2) :: (1, 1) :: repeat (1, 2) 297773 ++ (1424871, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) 1); closearith.
  }
  (* step 240: P TDN *)
  apply (hsteps_trans _ (HB [20; 0] 33 1 4 ((89, 2) :: (1, 1) :: repeat (1, 2) 171 ++ (166, 2) :: (1, 1) :: repeat (1, 2) 958 ++ (277, 2) :: (1, 1) :: repeat (1, 2) 5076 ++ (131714, 2) :: (1, 1) :: repeat (1, 2) 297773 ++ (1424871, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) 1)).
  {
    apply (sTDN [20; 0] 33 ((89, 2) :: (1, 1) :: repeat (1, 2) 171 ++ (166, 2) :: (1, 1) :: repeat (1, 2) 958 ++ (277, 2) :: (1, 1) :: repeat (1, 2) 5076 ++ (131714, 2) :: (1, 1) :: repeat (1, 2) 297773 ++ (1424871, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) 1).
  }
  (* step 241: sTUP *)
  apply (hsteps_trans _ (HC [20; 0] 33 3 2 ((87, 2) :: (1, 1) :: repeat (1, 2) 171 ++ (166, 2) :: (1, 1) :: repeat (1, 2) 958 ++ (277, 2) :: (1, 1) :: repeat (1, 2) 5076 ++ (131714, 2) :: (1, 1) :: repeat (1, 2) 297773 ++ (1424871, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) 1)).
  {
    replace ((87, 2) :: (1, 1) :: repeat (1, 2) 171 ++ (166, 2) :: (1, 1) :: repeat (1, 2) 958 ++ (277, 2) :: (1, 1) :: repeat (1, 2) 5076 ++ (131714, 2) :: (1, 1) :: repeat (1, 2) 297773 ++ (1424871, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) with ((89 - 2, 2) :: (1, 1) :: repeat (1, 2) 171 ++ (166, 2) :: (1, 1) :: repeat (1, 2) 958 ++ (277, 2) :: (1, 1) :: repeat (1, 2) 5076 ++ (131714, 2) :: (1, 1) :: repeat (1, 2) 297773 ++ (1424871, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) by sec_eq.
    apply (sTUP [20; 0] 33 4 89 2 ((1, 1) :: repeat (1, 2) 171 ++ (166, 2) :: (1, 1) :: repeat (1, 2) 958 ++ (277, 2) :: (1, 1) :: repeat (1, 2) 5076 ++ (131714, 2) :: (1, 1) :: repeat (1, 2) 297773 ++ (1424871, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) 1); closearith.
  }
  (* step 242: DIPGRIND 33 21 *)
  apply (hsteps_trans _ (HC [20; 0] 0 3 2 (repeat (1, 2) 33 ++ (21, 2) :: (1, 1) :: repeat (1, 2) 171 ++ (166, 2) :: (1, 1) :: repeat (1, 2) 958 ++ (277, 2) :: (1, 1) :: repeat (1, 2) 5076 ++ (131714, 2) :: (1, 1) :: repeat (1, 2) 297773 ++ (1424871, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) 1)).
  {
    apply (DIPGRIND 33 21 [20; 0] ((1, 1) :: repeat (1, 2) 171 ++ (166, 2) :: (1, 1) :: repeat (1, 2) 958 ++ (277, 2) :: (1, 1) :: repeat (1, 2) 5076 ++ (131714, 2) :: (1, 1) :: repeat (1, 2) 297773 ++ (1424871, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) 1); closearith.
  }
  (* step 243: P PX2A0 *)
  apply (hsteps_trans _ (HB [0] 3 1 2 ((16, 2) :: (1, 1) :: repeat (1, 2) 35 ++ (21, 2) :: (1, 1) :: repeat (1, 2) 171 ++ (166, 2) :: (1, 1) :: repeat (1, 2) 958 ++ (277, 2) :: (1, 1) :: repeat (1, 2) 5076 ++ (131714, 2) :: (1, 1) :: repeat (1, 2) 297773 ++ (1424871, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) 1)).
  {
    exact (hsteps_step _ _ _ (hPX2A0 15 (repeat (1, 2) 33 ++ (21, 2) :: (1, 1) :: repeat (1, 2) 171 ++ (166, 2) :: (1, 1) :: repeat (1, 2) 958 ++ (277, 2) :: (1, 1) :: repeat (1, 2) 5076 ++ (131714, 2) :: (1, 1) :: repeat (1, 2) 297773 ++ (1424871, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) 1) (hsteps_refl _)).
  }
  (* step 244: sTUP *)
  apply (hsteps_trans _ (HC [0] 3 1 2 ((14, 2) :: (1, 1) :: repeat (1, 2) 35 ++ (21, 2) :: (1, 1) :: repeat (1, 2) 171 ++ (166, 2) :: (1, 1) :: repeat (1, 2) 958 ++ (277, 2) :: (1, 1) :: repeat (1, 2) 5076 ++ (131714, 2) :: (1, 1) :: repeat (1, 2) 297773 ++ (1424871, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) 1)).
  {
    replace ((14, 2) :: (1, 1) :: repeat (1, 2) 35 ++ (21, 2) :: (1, 1) :: repeat (1, 2) 171 ++ (166, 2) :: (1, 1) :: repeat (1, 2) 958 ++ (277, 2) :: (1, 1) :: repeat (1, 2) 5076 ++ (131714, 2) :: (1, 1) :: repeat (1, 2) 297773 ++ (1424871, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) with ((16 - 2, 2) :: (1, 1) :: repeat (1, 2) 35 ++ (21, 2) :: (1, 1) :: repeat (1, 2) 171 ++ (166, 2) :: (1, 1) :: repeat (1, 2) 958 ++ (277, 2) :: (1, 1) :: repeat (1, 2) 5076 ++ (131714, 2) :: (1, 1) :: repeat (1, 2) 297773 ++ (1424871, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) by sec_eq.
    apply (sTUP [0] 3 2 16 2 ((1, 1) :: repeat (1, 2) 35 ++ (21, 2) :: (1, 1) :: repeat (1, 2) 171 ++ (166, 2) :: (1, 1) :: repeat (1, 2) 958 ++ (277, 2) :: (1, 1) :: repeat (1, 2) 5076 ++ (131714, 2) :: (1, 1) :: repeat (1, 2) 297773 ++ (1424871, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) 1); closearith.
  }
  (* step 245: P TDN *)
  apply (hsteps_trans _ (HB [0] 3 1 4 ((14, 2) :: (1, 1) :: repeat (1, 2) 35 ++ (21, 2) :: (1, 1) :: repeat (1, 2) 171 ++ (166, 2) :: (1, 1) :: repeat (1, 2) 958 ++ (277, 2) :: (1, 1) :: repeat (1, 2) 5076 ++ (131714, 2) :: (1, 1) :: repeat (1, 2) 297773 ++ (1424871, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) 1)).
  {
    apply (sTDN [0] 3 ((14, 2) :: (1, 1) :: repeat (1, 2) 35 ++ (21, 2) :: (1, 1) :: repeat (1, 2) 171 ++ (166, 2) :: (1, 1) :: repeat (1, 2) 958 ++ (277, 2) :: (1, 1) :: repeat (1, 2) 5076 ++ (131714, 2) :: (1, 1) :: repeat (1, 2) 297773 ++ (1424871, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) 1).
  }
  (* step 246: sTUP *)
  apply (hsteps_trans _ (HC [0] 3 3 2 ((12, 2) :: (1, 1) :: repeat (1, 2) 35 ++ (21, 2) :: (1, 1) :: repeat (1, 2) 171 ++ (166, 2) :: (1, 1) :: repeat (1, 2) 958 ++ (277, 2) :: (1, 1) :: repeat (1, 2) 5076 ++ (131714, 2) :: (1, 1) :: repeat (1, 2) 297773 ++ (1424871, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) 1)).
  {
    replace ((12, 2) :: (1, 1) :: repeat (1, 2) 35 ++ (21, 2) :: (1, 1) :: repeat (1, 2) 171 ++ (166, 2) :: (1, 1) :: repeat (1, 2) 958 ++ (277, 2) :: (1, 1) :: repeat (1, 2) 5076 ++ (131714, 2) :: (1, 1) :: repeat (1, 2) 297773 ++ (1424871, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) with ((14 - 2, 2) :: (1, 1) :: repeat (1, 2) 35 ++ (21, 2) :: (1, 1) :: repeat (1, 2) 171 ++ (166, 2) :: (1, 1) :: repeat (1, 2) 958 ++ (277, 2) :: (1, 1) :: repeat (1, 2) 5076 ++ (131714, 2) :: (1, 1) :: repeat (1, 2) 297773 ++ (1424871, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) by sec_eq.
    apply (sTUP [0] 3 4 14 2 ((1, 1) :: repeat (1, 2) 35 ++ (21, 2) :: (1, 1) :: repeat (1, 2) 171 ++ (166, 2) :: (1, 1) :: repeat (1, 2) 958 ++ (277, 2) :: (1, 1) :: repeat (1, 2) 5076 ++ (131714, 2) :: (1, 1) :: repeat (1, 2) 297773 ++ (1424871, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) 1); closearith.
  }
  (* step 247: DIPGRIND 3 6 *)
  apply (hsteps_trans _ (HC [0] 0 3 2 (repeat (1, 2) 3 ++ (6, 2) :: (1, 1) :: repeat (1, 2) 35 ++ (21, 2) :: (1, 1) :: repeat (1, 2) 171 ++ (166, 2) :: (1, 1) :: repeat (1, 2) 958 ++ (277, 2) :: (1, 1) :: repeat (1, 2) 5076 ++ (131714, 2) :: (1, 1) :: repeat (1, 2) 297773 ++ (1424871, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) 1)).
  {
    apply (DIPGRIND 3 6 [0] ((1, 1) :: repeat (1, 2) 35 ++ (21, 2) :: (1, 1) :: repeat (1, 2) 171 ++ (166, 2) :: (1, 1) :: repeat (1, 2) 958 ++ (277, 2) :: (1, 1) :: repeat (1, 2) 5076 ++ (131714, 2) :: (1, 1) :: repeat (1, 2) 297773 ++ (1424871, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) 1); closearith.
  }
  (* step 248: P PX2B0 *)
  apply (hsteps_trans _ (HB [] 0 1 5 (repeat (1, 2) 4 ++ (6, 2) :: (1, 1) :: repeat (1, 2) 35 ++ (21, 2) :: (1, 1) :: repeat (1, 2) 171 ++ (166, 2) :: (1, 1) :: repeat (1, 2) 958 ++ (277, 2) :: (1, 1) :: repeat (1, 2) 5076 ++ (131714, 2) :: (1, 1) :: repeat (1, 2) 297773 ++ (1424871, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) 1)).
  {
    exact (hsteps_step _ _ _ (hPX2B0 (repeat (1, 2) 3 ++ (6, 2) :: (1, 1) :: repeat (1, 2) 35 ++ (21, 2) :: (1, 1) :: repeat (1, 2) 171 ++ (166, 2) :: (1, 1) :: repeat (1, 2) 958 ++ (277, 2) :: (1, 1) :: repeat (1, 2) 5076 ++ (131714, 2) :: (1, 1) :: repeat (1, 2) 297773 ++ (1424871, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) 1) (hsteps_refl _)).
  }
  (* step 249: M pop12 (4,) *)
  apply (hsteps_trans _ (HB [] 4 1 13 ((6, 2) :: (1, 1) :: repeat (1, 2) 35 ++ (21, 2) :: (1, 1) :: repeat (1, 2) 171 ++ (166, 2) :: (1, 1) :: repeat (1, 2) 958 ++ (277, 2) :: (1, 1) :: repeat (1, 2) 5076 ++ (131714, 2) :: (1, 1) :: repeat (1, 2) 297773 ++ (1424871, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) 1)).
  {
    apply (pop12 4 [] 0 5 ((6, 2) :: (1, 1) :: repeat (1, 2) 35 ++ (21, 2) :: (1, 1) :: repeat (1, 2) 171 ++ (166, 2) :: (1, 1) :: repeat (1, 2) 958 ++ (277, 2) :: (1, 1) :: repeat (1, 2) 5076 ++ (131714, 2) :: (1, 1) :: repeat (1, 2) 297773 ++ (1424871, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) 1); closearith.
  }
  (* step 250: sTUP *)
  apply (hsteps_trans _ (HC [] 4 12 2 ((4, 2) :: (1, 1) :: repeat (1, 2) 35 ++ (21, 2) :: (1, 1) :: repeat (1, 2) 171 ++ (166, 2) :: (1, 1) :: repeat (1, 2) 958 ++ (277, 2) :: (1, 1) :: repeat (1, 2) 5076 ++ (131714, 2) :: (1, 1) :: repeat (1, 2) 297773 ++ (1424871, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) 1)).
  {
    replace ((4, 2) :: (1, 1) :: repeat (1, 2) 35 ++ (21, 2) :: (1, 1) :: repeat (1, 2) 171 ++ (166, 2) :: (1, 1) :: repeat (1, 2) 958 ++ (277, 2) :: (1, 1) :: repeat (1, 2) 5076 ++ (131714, 2) :: (1, 1) :: repeat (1, 2) 297773 ++ (1424871, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) with ((6 - 2, 2) :: (1, 1) :: repeat (1, 2) 35 ++ (21, 2) :: (1, 1) :: repeat (1, 2) 171 ++ (166, 2) :: (1, 1) :: repeat (1, 2) 958 ++ (277, 2) :: (1, 1) :: repeat (1, 2) 5076 ++ (131714, 2) :: (1, 1) :: repeat (1, 2) 297773 ++ (1424871, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) by sec_eq.
    apply (sTUP [] 4 13 6 2 ((1, 1) :: repeat (1, 2) 35 ++ (21, 2) :: (1, 1) :: repeat (1, 2) 171 ++ (166, 2) :: (1, 1) :: repeat (1, 2) 958 ++ (277, 2) :: (1, 1) :: repeat (1, 2) 5076 ++ (131714, 2) :: (1, 1) :: repeat (1, 2) 297773 ++ (1424871, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) 1); closearith.
  }
  (* step 251: P PUSH *)
  apply (hsteps_trans _ (HC [] 3 1 2 ((10, 2) :: (4, 2) :: (1, 1) :: repeat (1, 2) 35 ++ (21, 2) :: (1, 1) :: repeat (1, 2) 171 ++ (166, 2) :: (1, 1) :: repeat (1, 2) 958 ++ (277, 2) :: (1, 1) :: repeat (1, 2) 5076 ++ (131714, 2) :: (1, 1) :: repeat (1, 2) 297773 ++ (1424871, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) 1)).
  {
    replace ((10, 2) :: (4, 2) :: (1, 1) :: repeat (1, 2) 35 ++ (21, 2) :: (1, 1) :: repeat (1, 2) 171 ++ (166, 2) :: (1, 1) :: repeat (1, 2) 958 ++ (277, 2) :: (1, 1) :: repeat (1, 2) 5076 ++ (131714, 2) :: (1, 1) :: repeat (1, 2) 297773 ++ (1424871, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) with ((12 - 2, 2) :: (4, 2) :: (1, 1) :: repeat (1, 2) 35 ++ (21, 2) :: (1, 1) :: repeat (1, 2) 171 ++ (166, 2) :: (1, 1) :: repeat (1, 2) 958 ++ (277, 2) :: (1, 1) :: repeat (1, 2) 5076 ++ (131714, 2) :: (1, 1) :: repeat (1, 2) 297773 ++ (1424871, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) by sec_eq.
    apply (sPUSH [] 3 12 ((4, 2) :: (1, 1) :: repeat (1, 2) 35 ++ (21, 2) :: (1, 1) :: repeat (1, 2) 171 ++ (166, 2) :: (1, 1) :: repeat (1, 2) 958 ++ (277, 2) :: (1, 1) :: repeat (1, 2) 5076 ++ (131714, 2) :: (1, 1) :: repeat (1, 2) 297773 ++ (1424871, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) 1); closearith.
  }
  (* step 252: P TDN *)
  apply (hsteps_trans _ (HB [] 3 1 4 ((10, 2) :: (4, 2) :: (1, 1) :: repeat (1, 2) 35 ++ (21, 2) :: (1, 1) :: repeat (1, 2) 171 ++ (166, 2) :: (1, 1) :: repeat (1, 2) 958 ++ (277, 2) :: (1, 1) :: repeat (1, 2) 5076 ++ (131714, 2) :: (1, 1) :: repeat (1, 2) 297773 ++ (1424871, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) 1)).
  {
    apply (sTDN [] 3 ((10, 2) :: (4, 2) :: (1, 1) :: repeat (1, 2) 35 ++ (21, 2) :: (1, 1) :: repeat (1, 2) 171 ++ (166, 2) :: (1, 1) :: repeat (1, 2) 958 ++ (277, 2) :: (1, 1) :: repeat (1, 2) 5076 ++ (131714, 2) :: (1, 1) :: repeat (1, 2) 297773 ++ (1424871, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) 1).
  }
  (* step 253: sTUP *)
  apply (hsteps_trans _ (HC [] 3 3 2 ((8, 2) :: (4, 2) :: (1, 1) :: repeat (1, 2) 35 ++ (21, 2) :: (1, 1) :: repeat (1, 2) 171 ++ (166, 2) :: (1, 1) :: repeat (1, 2) 958 ++ (277, 2) :: (1, 1) :: repeat (1, 2) 5076 ++ (131714, 2) :: (1, 1) :: repeat (1, 2) 297773 ++ (1424871, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) 1)).
  {
    replace ((8, 2) :: (4, 2) :: (1, 1) :: repeat (1, 2) 35 ++ (21, 2) :: (1, 1) :: repeat (1, 2) 171 ++ (166, 2) :: (1, 1) :: repeat (1, 2) 958 ++ (277, 2) :: (1, 1) :: repeat (1, 2) 5076 ++ (131714, 2) :: (1, 1) :: repeat (1, 2) 297773 ++ (1424871, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) with ((10 - 2, 2) :: (4, 2) :: (1, 1) :: repeat (1, 2) 35 ++ (21, 2) :: (1, 1) :: repeat (1, 2) 171 ++ (166, 2) :: (1, 1) :: repeat (1, 2) 958 ++ (277, 2) :: (1, 1) :: repeat (1, 2) 5076 ++ (131714, 2) :: (1, 1) :: repeat (1, 2) 297773 ++ (1424871, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) by sec_eq.
    apply (sTUP [] 3 4 10 2 ((4, 2) :: (1, 1) :: repeat (1, 2) 35 ++ (21, 2) :: (1, 1) :: repeat (1, 2) 171 ++ (166, 2) :: (1, 1) :: repeat (1, 2) 958 ++ (277, 2) :: (1, 1) :: repeat (1, 2) 5076 ++ (131714, 2) :: (1, 1) :: repeat (1, 2) 297773 ++ (1424871, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) 1); closearith.
  }
  (* step 254: DIPGRIND 3 2 *)
  apply (hsteps_trans _ (HC [] 0 3 2 (repeat (1, 2) 3 ++ (2, 2) :: (4, 2) :: (1, 1) :: repeat (1, 2) 35 ++ (21, 2) :: (1, 1) :: repeat (1, 2) 171 ++ (166, 2) :: (1, 1) :: repeat (1, 2) 958 ++ (277, 2) :: (1, 1) :: repeat (1, 2) 5076 ++ (131714, 2) :: (1, 1) :: repeat (1, 2) 297773 ++ (1424871, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) 1)).
  {
    apply (DIPGRIND 3 2 [] ((4, 2) :: (1, 1) :: repeat (1, 2) 35 ++ (21, 2) :: (1, 1) :: repeat (1, 2) 171 ++ (166, 2) :: (1, 1) :: repeat (1, 2) 958 ++ (277, 2) :: (1, 1) :: repeat (1, 2) 5076 ++ (131714, 2) :: (1, 1) :: repeat (1, 2) 297773 ++ (1424871, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) 1); closearith.
  }
  (* step 255: P PUSHX *)
  apply (hsteps_trans _ (HB [] 1 1 7 (repeat (1, 2) 3 ++ (2, 2) :: (4, 2) :: (1, 1) :: repeat (1, 2) 35 ++ (21, 2) :: (1, 1) :: repeat (1, 2) 171 ++ (166, 2) :: (1, 1) :: repeat (1, 2) 958 ++ (277, 2) :: (1, 1) :: repeat (1, 2) 5076 ++ (131714, 2) :: (1, 1) :: repeat (1, 2) 297773 ++ (1424871, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) 1)).
  {
    exact (hsteps_step _ _ _ (hPUSHX (repeat (1, 2) 3 ++ (2, 2) :: (4, 2) :: (1, 1) :: repeat (1, 2) 35 ++ (21, 2) :: (1, 1) :: repeat (1, 2) 171 ++ (166, 2) :: (1, 1) :: repeat (1, 2) 958 ++ (277, 2) :: (1, 1) :: repeat (1, 2) 5076 ++ (131714, 2) :: (1, 1) :: repeat (1, 2) 297773 ++ (1424871, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) 1) (hsteps_refl _)).
  }
  (* step 256: M pop12 (3,) *)
  apply (hsteps_trans _ (HB [] 4 1 13 ((2, 2) :: (4, 2) :: (1, 1) :: repeat (1, 2) 35 ++ (21, 2) :: (1, 1) :: repeat (1, 2) 171 ++ (166, 2) :: (1, 1) :: repeat (1, 2) 958 ++ (277, 2) :: (1, 1) :: repeat (1, 2) 5076 ++ (131714, 2) :: (1, 1) :: repeat (1, 2) 297773 ++ (1424871, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) 1)).
  {
    apply (pop12 3 [] 1 7 ((2, 2) :: (4, 2) :: (1, 1) :: repeat (1, 2) 35 ++ (21, 2) :: (1, 1) :: repeat (1, 2) 171 ++ (166, 2) :: (1, 1) :: repeat (1, 2) 958 ++ (277, 2) :: (1, 1) :: repeat (1, 2) 5076 ++ (131714, 2) :: (1, 1) :: repeat (1, 2) 297773 ++ (1424871, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) 1); closearith.
  }
  (* step 257: P TUP2_1 *)
  apply (hsteps_trans _ (HC [5] 13 1 2 ((2, 2) :: (1, 1) :: repeat (1, 2) 35 ++ (21, 2) :: (1, 1) :: repeat (1, 2) 171 ++ (166, 2) :: (1, 1) :: repeat (1, 2) 958 ++ (277, 2) :: (1, 1) :: repeat (1, 2) 5076 ++ (131714, 2) :: (1, 1) :: repeat (1, 2) 297773 ++ (1424871, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) 1)).
  {
    replace ((2, 2) :: (1, 1) :: repeat (1, 2) 35 ++ (21, 2) :: (1, 1) :: repeat (1, 2) 171 ++ (166, 2) :: (1, 1) :: repeat (1, 2) 958 ++ (277, 2) :: (1, 1) :: repeat (1, 2) 5076 ++ (131714, 2) :: (1, 1) :: repeat (1, 2) 297773 ++ (1424871, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) with ((4 - 2, 2) :: (1, 1) :: repeat (1, 2) 35 ++ (21, 2) :: (1, 1) :: repeat (1, 2) 171 ++ (166, 2) :: (1, 1) :: repeat (1, 2) 958 ++ (277, 2) :: (1, 1) :: repeat (1, 2) 5076 ++ (131714, 2) :: (1, 1) :: repeat (1, 2) 297773 ++ (1424871, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) by sec_eq.
    apply (sTUP2_1 [] 4 12 4 ((1, 1) :: repeat (1, 2) 35 ++ (21, 2) :: (1, 1) :: repeat (1, 2) 171 ++ (166, 2) :: (1, 1) :: repeat (1, 2) 958 ++ (277, 2) :: (1, 1) :: repeat (1, 2) 5076 ++ (131714, 2) :: (1, 1) :: repeat (1, 2) 297773 ++ (1424871, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) 1); closearith.
  }
  (* step 258: P TDN *)
  apply (hsteps_trans _ (HB [5] 13 1 4 ((2, 2) :: (1, 1) :: repeat (1, 2) 35 ++ (21, 2) :: (1, 1) :: repeat (1, 2) 171 ++ (166, 2) :: (1, 1) :: repeat (1, 2) 958 ++ (277, 2) :: (1, 1) :: repeat (1, 2) 5076 ++ (131714, 2) :: (1, 1) :: repeat (1, 2) 297773 ++ (1424871, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) 1)).
  {
    apply (sTDN [5] 13 ((2, 2) :: (1, 1) :: repeat (1, 2) 35 ++ (21, 2) :: (1, 1) :: repeat (1, 2) 171 ++ (166, 2) :: (1, 1) :: repeat (1, 2) 958 ++ (277, 2) :: (1, 1) :: repeat (1, 2) 5076 ++ (131714, 2) :: (1, 1) :: repeat (1, 2) 297773 ++ (1424871, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) 1).
  }
  (* step 259: P TRANS2_1 *)
  apply (hsteps_trans _ (HB [14; 5] 5 1 3 (repeat (1, 2) 35 ++ (21, 2) :: (1, 1) :: repeat (1, 2) 171 ++ (166, 2) :: (1, 1) :: repeat (1, 2) 958 ++ (277, 2) :: (1, 1) :: repeat (1, 2) 5076 ++ (131714, 2) :: (1, 1) :: repeat (1, 2) 297773 ++ (1424871, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) 1)).
  {
    apply (sTRANS2_1 [5] 13 3 1 (repeat (1, 2) 35 ++ (21, 2) :: (1, 1) :: repeat (1, 2) 171 ++ (166, 2) :: (1, 1) :: repeat (1, 2) 958 ++ (277, 2) :: (1, 1) :: repeat (1, 2) 5076 ++ (131714, 2) :: (1, 1) :: repeat (1, 2) 297773 ++ (1424871, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) 1); closearith.
  }
  (* step 260: M pop12 (35,) *)
  apply (hsteps_trans _ (HB [14; 5] 40 1 73 ((21, 2) :: (1, 1) :: repeat (1, 2) 171 ++ (166, 2) :: (1, 1) :: repeat (1, 2) 958 ++ (277, 2) :: (1, 1) :: repeat (1, 2) 5076 ++ (131714, 2) :: (1, 1) :: repeat (1, 2) 297773 ++ (1424871, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) 1)).
  {
    apply (pop12 35 [14; 5] 5 3 ((21, 2) :: (1, 1) :: repeat (1, 2) 171 ++ (166, 2) :: (1, 1) :: repeat (1, 2) 958 ++ (277, 2) :: (1, 1) :: repeat (1, 2) 5076 ++ (131714, 2) :: (1, 1) :: repeat (1, 2) 297773 ++ (1424871, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) 1); closearith.
  }
  (* step 261: sTUP *)
  apply (hsteps_trans _ (HC [14; 5] 40 72 2 ((19, 2) :: (1, 1) :: repeat (1, 2) 171 ++ (166, 2) :: (1, 1) :: repeat (1, 2) 958 ++ (277, 2) :: (1, 1) :: repeat (1, 2) 5076 ++ (131714, 2) :: (1, 1) :: repeat (1, 2) 297773 ++ (1424871, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) 1)).
  {
    replace ((19, 2) :: (1, 1) :: repeat (1, 2) 171 ++ (166, 2) :: (1, 1) :: repeat (1, 2) 958 ++ (277, 2) :: (1, 1) :: repeat (1, 2) 5076 ++ (131714, 2) :: (1, 1) :: repeat (1, 2) 297773 ++ (1424871, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) with ((21 - 2, 2) :: (1, 1) :: repeat (1, 2) 171 ++ (166, 2) :: (1, 1) :: repeat (1, 2) 958 ++ (277, 2) :: (1, 1) :: repeat (1, 2) 5076 ++ (131714, 2) :: (1, 1) :: repeat (1, 2) 297773 ++ (1424871, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) by sec_eq.
    apply (sTUP [14; 5] 40 73 21 2 ((1, 1) :: repeat (1, 2) 171 ++ (166, 2) :: (1, 1) :: repeat (1, 2) 958 ++ (277, 2) :: (1, 1) :: repeat (1, 2) 5076 ++ (131714, 2) :: (1, 1) :: repeat (1, 2) 297773 ++ (1424871, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) 1); closearith.
  }
  (* step 262: hGRIND_even 34 *)
  apply (hsteps_trans _ (HB [14; 5] 39 1 72 ((2, 2) :: (19, 2) :: (1, 1) :: repeat (1, 2) 171 ++ (166, 2) :: (1, 1) :: repeat (1, 2) 958 ++ (277, 2) :: (1, 1) :: repeat (1, 2) 5076 ++ (131714, 2) :: (1, 1) :: repeat (1, 2) 297773 ++ (1424871, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) 1)).
  {
    apply (hGRIND_even 34 [14; 5] 39 ((19, 2) :: (1, 1) :: repeat (1, 2) 171 ++ (166, 2) :: (1, 1) :: repeat (1, 2) 958 ++ (277, 2) :: (1, 1) :: repeat (1, 2) 5076 ++ (131714, 2) :: (1, 1) :: repeat (1, 2) 297773 ++ (1424871, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) 1); closearith.
  }
  (* step 263: P TUP2_1 *)
  apply (hsteps_trans _ (HC [40; 14; 5] 72 1 2 ((17, 2) :: (1, 1) :: repeat (1, 2) 171 ++ (166, 2) :: (1, 1) :: repeat (1, 2) 958 ++ (277, 2) :: (1, 1) :: repeat (1, 2) 5076 ++ (131714, 2) :: (1, 1) :: repeat (1, 2) 297773 ++ (1424871, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) 1)).
  {
    replace ((17, 2) :: (1, 1) :: repeat (1, 2) 171 ++ (166, 2) :: (1, 1) :: repeat (1, 2) 958 ++ (277, 2) :: (1, 1) :: repeat (1, 2) 5076 ++ (131714, 2) :: (1, 1) :: repeat (1, 2) 297773 ++ (1424871, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) with ((19 - 2, 2) :: (1, 1) :: repeat (1, 2) 171 ++ (166, 2) :: (1, 1) :: repeat (1, 2) 958 ++ (277, 2) :: (1, 1) :: repeat (1, 2) 5076 ++ (131714, 2) :: (1, 1) :: repeat (1, 2) 297773 ++ (1424871, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) by sec_eq.
    apply (sTUP2_1 [14; 5] 39 71 19 ((1, 1) :: repeat (1, 2) 171 ++ (166, 2) :: (1, 1) :: repeat (1, 2) 958 ++ (277, 2) :: (1, 1) :: repeat (1, 2) 5076 ++ (131714, 2) :: (1, 1) :: repeat (1, 2) 297773 ++ (1424871, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) 1); closearith.
  }
  (* step 264: P TDN *)
  apply (hsteps_trans _ (HB [40; 14; 5] 72 1 4 ((17, 2) :: (1, 1) :: repeat (1, 2) 171 ++ (166, 2) :: (1, 1) :: repeat (1, 2) 958 ++ (277, 2) :: (1, 1) :: repeat (1, 2) 5076 ++ (131714, 2) :: (1, 1) :: repeat (1, 2) 297773 ++ (1424871, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) 1)).
  {
    apply (sTDN [40; 14; 5] 72 ((17, 2) :: (1, 1) :: repeat (1, 2) 171 ++ (166, 2) :: (1, 1) :: repeat (1, 2) 958 ++ (277, 2) :: (1, 1) :: repeat (1, 2) 5076 ++ (131714, 2) :: (1, 1) :: repeat (1, 2) 297773 ++ (1424871, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) 1).
  }
  (* step 265: sTUP *)
  apply (hsteps_trans _ (HC [40; 14; 5] 72 3 2 ((15, 2) :: (1, 1) :: repeat (1, 2) 171 ++ (166, 2) :: (1, 1) :: repeat (1, 2) 958 ++ (277, 2) :: (1, 1) :: repeat (1, 2) 5076 ++ (131714, 2) :: (1, 1) :: repeat (1, 2) 297773 ++ (1424871, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) 1)).
  {
    replace ((15, 2) :: (1, 1) :: repeat (1, 2) 171 ++ (166, 2) :: (1, 1) :: repeat (1, 2) 958 ++ (277, 2) :: (1, 1) :: repeat (1, 2) 5076 ++ (131714, 2) :: (1, 1) :: repeat (1, 2) 297773 ++ (1424871, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) with ((17 - 2, 2) :: (1, 1) :: repeat (1, 2) 171 ++ (166, 2) :: (1, 1) :: repeat (1, 2) 958 ++ (277, 2) :: (1, 1) :: repeat (1, 2) 5076 ++ (131714, 2) :: (1, 1) :: repeat (1, 2) 297773 ++ (1424871, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) by sec_eq.
    apply (sTUP [40; 14; 5] 72 4 17 2 ((1, 1) :: repeat (1, 2) 171 ++ (166, 2) :: (1, 1) :: repeat (1, 2) 958 ++ (277, 2) :: (1, 1) :: repeat (1, 2) 5076 ++ (131714, 2) :: (1, 1) :: repeat (1, 2) 297773 ++ (1424871, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) 1); closearith.
  }
  (* step 266: CLEANG_odd 6 *)
  apply (hsteps_trans _ (HB [40; 14; 5] 72 1 20 (repeat (1, 2) 1 ++ (1, 1) :: repeat (1, 2) 171 ++ (166, 2) :: (1, 1) :: repeat (1, 2) 958 ++ (277, 2) :: (1, 1) :: repeat (1, 2) 5076 ++ (131714, 2) :: (1, 1) :: repeat (1, 2) 297773 ++ (1424871, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) 1)).
  {
    replace (repeat (1, 2) 1 ++ (1, 1) :: repeat (1, 2) 171 ++ (166, 2) :: (1, 1) :: repeat (1, 2) 958 ++ (277, 2) :: (1, 1) :: repeat (1, 2) 5076 ++ (131714, 2) :: (1, 1) :: repeat (1, 2) 297773 ++ (1424871, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) with ((1, 2) :: (1, 1) :: repeat (1, 2) 171 ++ (166, 2) :: (1, 1) :: repeat (1, 2) 958 ++ (277, 2) :: (1, 1) :: repeat (1, 2) 5076 ++ (131714, 2) :: (1, 1) :: repeat (1, 2) 297773 ++ (1424871, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) by sec_eq.
    apply (CLEANG_odd 6 [40; 14; 5] 72 ((1, 1) :: repeat (1, 2) 171 ++ (166, 2) :: (1, 1) :: repeat (1, 2) 958 ++ (277, 2) :: (1, 1) :: repeat (1, 2) 5076 ++ (131714, 2) :: (1, 1) :: repeat (1, 2) 297773 ++ (1424871, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) 1); closearith.
  }
  (* step 267: M pop12 (1,) *)
  apply (hsteps_trans _ (HB [40; 14; 5] 73 1 22 ((1, 1) :: repeat (1, 2) 171 ++ (166, 2) :: (1, 1) :: repeat (1, 2) 958 ++ (277, 2) :: (1, 1) :: repeat (1, 2) 5076 ++ (131714, 2) :: (1, 1) :: repeat (1, 2) 297773 ++ (1424871, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) 1)).
  {
    apply (pop12 1 [40; 14; 5] 72 20 ((1, 1) :: repeat (1, 2) 171 ++ (166, 2) :: (1, 1) :: repeat (1, 2) 958 ++ (277, 2) :: (1, 1) :: repeat (1, 2) 5076 ++ (131714, 2) :: (1, 1) :: repeat (1, 2) 297773 ++ (1424871, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) 1); closearith.
  }
  (* step 268: P POP *)
  apply (hsteps_trans _ (HB [40; 14; 5] 74 1 23 (repeat (1, 2) 171 ++ (166, 2) :: (1, 1) :: repeat (1, 2) 958 ++ (277, 2) :: (1, 1) :: repeat (1, 2) 5076 ++ (131714, 2) :: (1, 1) :: repeat (1, 2) 297773 ++ (1424871, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) 1)).
  {
    apply (sPOP1 [40; 14; 5] 73 22 (repeat (1, 2) 171 ++ (166, 2) :: (1, 1) :: repeat (1, 2) 958 ++ (277, 2) :: (1, 1) :: repeat (1, 2) 5076 ++ (131714, 2) :: (1, 1) :: repeat (1, 2) 297773 ++ (1424871, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) 1); closearith.
  }
  (* step 269: M pop12 (171,) *)
  apply (hsteps_trans _ (HB [40; 14; 5] 245 1 365 ((166, 2) :: (1, 1) :: repeat (1, 2) 958 ++ (277, 2) :: (1, 1) :: repeat (1, 2) 5076 ++ (131714, 2) :: (1, 1) :: repeat (1, 2) 297773 ++ (1424871, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) 1)).
  {
    apply (pop12 171 [40; 14; 5] 74 23 ((166, 2) :: (1, 1) :: repeat (1, 2) 958 ++ (277, 2) :: (1, 1) :: repeat (1, 2) 5076 ++ (131714, 2) :: (1, 1) :: repeat (1, 2) 297773 ++ (1424871, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) 1); closearith.
  }
  (* step 270: sTUP *)
  apply (hsteps_trans _ (HC [40; 14; 5] 245 364 2 ((164, 2) :: (1, 1) :: repeat (1, 2) 958 ++ (277, 2) :: (1, 1) :: repeat (1, 2) 5076 ++ (131714, 2) :: (1, 1) :: repeat (1, 2) 297773 ++ (1424871, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) 1)).
  {
    replace ((164, 2) :: (1, 1) :: repeat (1, 2) 958 ++ (277, 2) :: (1, 1) :: repeat (1, 2) 5076 ++ (131714, 2) :: (1, 1) :: repeat (1, 2) 297773 ++ (1424871, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) with ((166 - 2, 2) :: (1, 1) :: repeat (1, 2) 958 ++ (277, 2) :: (1, 1) :: repeat (1, 2) 5076 ++ (131714, 2) :: (1, 1) :: repeat (1, 2) 297773 ++ (1424871, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) by sec_eq.
    apply (sTUP [40; 14; 5] 245 365 166 2 ((1, 1) :: repeat (1, 2) 958 ++ (277, 2) :: (1, 1) :: repeat (1, 2) 5076 ++ (131714, 2) :: (1, 1) :: repeat (1, 2) 297773 ++ (1424871, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) 1); closearith.
  }
  (* step 271: hGRIND_even 180 *)
  apply (hsteps_trans _ (HB [40; 14; 5] 244 1 364 ((2, 2) :: (164, 2) :: (1, 1) :: repeat (1, 2) 958 ++ (277, 2) :: (1, 1) :: repeat (1, 2) 5076 ++ (131714, 2) :: (1, 1) :: repeat (1, 2) 297773 ++ (1424871, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) 1)).
  {
    apply (hGRIND_even 180 [40; 14; 5] 244 ((164, 2) :: (1, 1) :: repeat (1, 2) 958 ++ (277, 2) :: (1, 1) :: repeat (1, 2) 5076 ++ (131714, 2) :: (1, 1) :: repeat (1, 2) 297773 ++ (1424871, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) 1); closearith.
  }
  (* step 272: P TUP2_1 *)
  apply (hsteps_trans _ (HC [245; 40; 14; 5] 364 1 2 ((162, 2) :: (1, 1) :: repeat (1, 2) 958 ++ (277, 2) :: (1, 1) :: repeat (1, 2) 5076 ++ (131714, 2) :: (1, 1) :: repeat (1, 2) 297773 ++ (1424871, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) 1)).
  {
    replace ((162, 2) :: (1, 1) :: repeat (1, 2) 958 ++ (277, 2) :: (1, 1) :: repeat (1, 2) 5076 ++ (131714, 2) :: (1, 1) :: repeat (1, 2) 297773 ++ (1424871, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) with ((164 - 2, 2) :: (1, 1) :: repeat (1, 2) 958 ++ (277, 2) :: (1, 1) :: repeat (1, 2) 5076 ++ (131714, 2) :: (1, 1) :: repeat (1, 2) 297773 ++ (1424871, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) by sec_eq.
    apply (sTUP2_1 [40; 14; 5] 244 363 164 ((1, 1) :: repeat (1, 2) 958 ++ (277, 2) :: (1, 1) :: repeat (1, 2) 5076 ++ (131714, 2) :: (1, 1) :: repeat (1, 2) 297773 ++ (1424871, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) 1); closearith.
  }
  (* step 273: P TDN *)
  apply (hsteps_trans _ (HB [245; 40; 14; 5] 364 1 4 ((162, 2) :: (1, 1) :: repeat (1, 2) 958 ++ (277, 2) :: (1, 1) :: repeat (1, 2) 5076 ++ (131714, 2) :: (1, 1) :: repeat (1, 2) 297773 ++ (1424871, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) 1)).
  {
    apply (sTDN [245; 40; 14; 5] 364 ((162, 2) :: (1, 1) :: repeat (1, 2) 958 ++ (277, 2) :: (1, 1) :: repeat (1, 2) 5076 ++ (131714, 2) :: (1, 1) :: repeat (1, 2) 297773 ++ (1424871, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) 1).
  }
  (* step 274: sTUP *)
  apply (hsteps_trans _ (HC [245; 40; 14; 5] 364 3 2 ((160, 2) :: (1, 1) :: repeat (1, 2) 958 ++ (277, 2) :: (1, 1) :: repeat (1, 2) 5076 ++ (131714, 2) :: (1, 1) :: repeat (1, 2) 297773 ++ (1424871, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) 1)).
  {
    replace ((160, 2) :: (1, 1) :: repeat (1, 2) 958 ++ (277, 2) :: (1, 1) :: repeat (1, 2) 5076 ++ (131714, 2) :: (1, 1) :: repeat (1, 2) 297773 ++ (1424871, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) with ((162 - 2, 2) :: (1, 1) :: repeat (1, 2) 958 ++ (277, 2) :: (1, 1) :: repeat (1, 2) 5076 ++ (131714, 2) :: (1, 1) :: repeat (1, 2) 297773 ++ (1424871, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) by sec_eq.
    apply (sTUP [245; 40; 14; 5] 364 4 162 2 ((1, 1) :: repeat (1, 2) 958 ++ (277, 2) :: (1, 1) :: repeat (1, 2) 5076 ++ (131714, 2) :: (1, 1) :: repeat (1, 2) 297773 ++ (1424871, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) 1); closearith.
  }
  (* step 275: CLEANG_even 79 *)
  apply (hsteps_trans _ (HB [245; 40; 14; 5] 364 1 164 ((2, 2) :: (1, 1) :: repeat (1, 2) 958 ++ (277, 2) :: (1, 1) :: repeat (1, 2) 5076 ++ (131714, 2) :: (1, 1) :: repeat (1, 2) 297773 ++ (1424871, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) 1)).
  {
    apply (CLEANG_even 79 [245; 40; 14; 5] 364 ((1, 1) :: repeat (1, 2) 958 ++ (277, 2) :: (1, 1) :: repeat (1, 2) 5076 ++ (131714, 2) :: (1, 1) :: repeat (1, 2) 297773 ++ (1424871, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) 1); closearith.
  }
  (* step 276: P TRANS2_1 *)
  apply (hsteps_trans _ (HB [365; 245; 40; 14; 5] 165 1 3 (repeat (1, 2) 958 ++ (277, 2) :: (1, 1) :: repeat (1, 2) 5076 ++ (131714, 2) :: (1, 1) :: repeat (1, 2) 297773 ++ (1424871, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) 1)).
  {
    apply (sTRANS2_1 [245; 40; 14; 5] 364 163 1 (repeat (1, 2) 958 ++ (277, 2) :: (1, 1) :: repeat (1, 2) 5076 ++ (131714, 2) :: (1, 1) :: repeat (1, 2) 297773 ++ (1424871, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) 1); closearith.
  }
  (* step 277: M pop12 (958,) *)
  apply (hsteps_trans _ (HB [365; 245; 40; 14; 5] 1123 1 1919 ((277, 2) :: (1, 1) :: repeat (1, 2) 5076 ++ (131714, 2) :: (1, 1) :: repeat (1, 2) 297773 ++ (1424871, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) 1)).
  {
    apply (pop12 958 [365; 245; 40; 14; 5] 165 3 ((277, 2) :: (1, 1) :: repeat (1, 2) 5076 ++ (131714, 2) :: (1, 1) :: repeat (1, 2) 297773 ++ (1424871, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) 1); closearith.
  }
  (* step 278: sTUP *)
  apply (hsteps_trans _ (HC [365; 245; 40; 14; 5] 1123 1918 2 ((275, 2) :: (1, 1) :: repeat (1, 2) 5076 ++ (131714, 2) :: (1, 1) :: repeat (1, 2) 297773 ++ (1424871, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) 1)).
  {
    replace ((275, 2) :: (1, 1) :: repeat (1, 2) 5076 ++ (131714, 2) :: (1, 1) :: repeat (1, 2) 297773 ++ (1424871, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) with ((277 - 2, 2) :: (1, 1) :: repeat (1, 2) 5076 ++ (131714, 2) :: (1, 1) :: repeat (1, 2) 297773 ++ (1424871, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) by sec_eq.
    apply (sTUP [365; 245; 40; 14; 5] 1123 1919 277 2 ((1, 1) :: repeat (1, 2) 5076 ++ (131714, 2) :: (1, 1) :: repeat (1, 2) 297773 ++ (1424871, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) 1); closearith.
  }
  (* step 279: hGRIND_even 957 *)
  apply (hsteps_trans _ (HB [365; 245; 40; 14; 5] 1122 1 1918 ((2, 2) :: (275, 2) :: (1, 1) :: repeat (1, 2) 5076 ++ (131714, 2) :: (1, 1) :: repeat (1, 2) 297773 ++ (1424871, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) 1)).
  {
    apply (hGRIND_even 957 [365; 245; 40; 14; 5] 1122 ((275, 2) :: (1, 1) :: repeat (1, 2) 5076 ++ (131714, 2) :: (1, 1) :: repeat (1, 2) 297773 ++ (1424871, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) 1); closearith.
  }
  (* step 280: P TUP2_1 *)
  replace ((273, 2) :: (1, 1) :: repeat (1, 2) 5076 ++ (131714, 2) :: (1, 1) :: repeat (1, 2) 297773 ++ (1424871, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) with ((275 - 2, 2) :: (1, 1) :: repeat (1, 2) 5076 ++ (131714, 2) :: (1, 1) :: repeat (1, 2) 297773 ++ (1424871, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) by sec_eq.
  apply (sTUP2_1 [365; 245; 40; 14; 5] 1122 1917 275 ((1, 1) :: repeat (1, 2) 5076 ++ (131714, 2) :: (1, 1) :: repeat (1, 2) 297773 ++ (1424871, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) 1); closearith.
Qed.

(* CASCADE56f: steps 281-336 of the CASCADE56 chain. *)
Lemma CASCADE56f : forall w,
  hsteps (HC [1123; 365; 245; 40; 14; 5] 1918 1 2 ((273, 2) :: (1, 1) :: repeat (1, 2) 5076 ++ (131714, 2) :: (1, 1) :: repeat (1, 2) 297773 ++ (1424871, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) 1)
         (HB [5] 53 1 82 ((2, 2) :: (1284, 2) :: (1, 1) :: repeat (1, 2) 2613 ++ (9951, 2) :: (1, 1) :: repeat (1, 2) 20868 ++ (69110, 2) :: (1, 1) :: repeat (1, 2) 297773 ++ (1424871, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) 1).
Proof.
  intro w.
  (* step 281: P TDN *)
  apply (hsteps_trans _ (HB [1123; 365; 245; 40; 14; 5] 1918 1 4 ((273, 2) :: (1, 1) :: repeat (1, 2) 5076 ++ (131714, 2) :: (1, 1) :: repeat (1, 2) 297773 ++ (1424871, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) 1)).
  {
    apply (sTDN [1123; 365; 245; 40; 14; 5] 1918 ((273, 2) :: (1, 1) :: repeat (1, 2) 5076 ++ (131714, 2) :: (1, 1) :: repeat (1, 2) 297773 ++ (1424871, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) 1).
  }
  (* step 282: sTUP *)
  apply (hsteps_trans _ (HC [1123; 365; 245; 40; 14; 5] 1918 3 2 ((271, 2) :: (1, 1) :: repeat (1, 2) 5076 ++ (131714, 2) :: (1, 1) :: repeat (1, 2) 297773 ++ (1424871, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) 1)).
  {
    replace ((271, 2) :: (1, 1) :: repeat (1, 2) 5076 ++ (131714, 2) :: (1, 1) :: repeat (1, 2) 297773 ++ (1424871, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) with ((273 - 2, 2) :: (1, 1) :: repeat (1, 2) 5076 ++ (131714, 2) :: (1, 1) :: repeat (1, 2) 297773 ++ (1424871, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) by sec_eq.
    apply (sTUP [1123; 365; 245; 40; 14; 5] 1918 4 273 2 ((1, 1) :: repeat (1, 2) 5076 ++ (131714, 2) :: (1, 1) :: repeat (1, 2) 297773 ++ (1424871, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) 1); closearith.
  }
  (* step 283: CLEANG_odd 134 *)
  apply (hsteps_trans _ (HB [1123; 365; 245; 40; 14; 5] 1918 1 276 (repeat (1, 2) 1 ++ (1, 1) :: repeat (1, 2) 5076 ++ (131714, 2) :: (1, 1) :: repeat (1, 2) 297773 ++ (1424871, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) 1)).
  {
    replace (repeat (1, 2) 1 ++ (1, 1) :: repeat (1, 2) 5076 ++ (131714, 2) :: (1, 1) :: repeat (1, 2) 297773 ++ (1424871, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) with ((1, 2) :: (1, 1) :: repeat (1, 2) 5076 ++ (131714, 2) :: (1, 1) :: repeat (1, 2) 297773 ++ (1424871, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) by sec_eq.
    apply (CLEANG_odd 134 [1123; 365; 245; 40; 14; 5] 1918 ((1, 1) :: repeat (1, 2) 5076 ++ (131714, 2) :: (1, 1) :: repeat (1, 2) 297773 ++ (1424871, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) 1); closearith.
  }
  (* step 284: M pop12 (1,) *)
  apply (hsteps_trans _ (HB [1123; 365; 245; 40; 14; 5] 1919 1 278 ((1, 1) :: repeat (1, 2) 5076 ++ (131714, 2) :: (1, 1) :: repeat (1, 2) 297773 ++ (1424871, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) 1)).
  {
    apply (pop12 1 [1123; 365; 245; 40; 14; 5] 1918 276 ((1, 1) :: repeat (1, 2) 5076 ++ (131714, 2) :: (1, 1) :: repeat (1, 2) 297773 ++ (1424871, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) 1); closearith.
  }
  (* step 285: P POP *)
  apply (hsteps_trans _ (HB [1123; 365; 245; 40; 14; 5] 1920 1 279 (repeat (1, 2) 5076 ++ (131714, 2) :: (1, 1) :: repeat (1, 2) 297773 ++ (1424871, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) 1)).
  {
    apply (sPOP1 [1123; 365; 245; 40; 14; 5] 1919 278 (repeat (1, 2) 5076 ++ (131714, 2) :: (1, 1) :: repeat (1, 2) 297773 ++ (1424871, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) 1); closearith.
  }
  (* step 286: M pop12 (5076,) *)
  apply (hsteps_trans _ (HB [1123; 365; 245; 40; 14; 5] 6996 1 10431 ((131714, 2) :: (1, 1) :: repeat (1, 2) 297773 ++ (1424871, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) 1)).
  {
    apply (pop12 5076 [1123; 365; 245; 40; 14; 5] 1920 279 ((131714, 2) :: (1, 1) :: repeat (1, 2) 297773 ++ (1424871, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) 1); closearith.
  }
  (* step 287: sTUP *)
  apply (hsteps_trans _ (HC [1123; 365; 245; 40; 14; 5] 6996 10430 2 ((131712, 2) :: (1, 1) :: repeat (1, 2) 297773 ++ (1424871, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) 1)).
  {
    replace ((131712, 2) :: (1, 1) :: repeat (1, 2) 297773 ++ (1424871, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) with ((131714 - 2, 2) :: (1, 1) :: repeat (1, 2) 297773 ++ (1424871, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) by sec_eq.
    apply (sTUP [1123; 365; 245; 40; 14; 5] 6996 10431 131714 2 ((1, 1) :: repeat (1, 2) 297773 ++ (1424871, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) 1); closearith.
  }
  (* step 288: hGRIND_even 5213 *)
  apply (hsteps_trans _ (HB [1123; 365; 245; 40; 14; 5] 6995 1 10430 ((2, 2) :: (131712, 2) :: (1, 1) :: repeat (1, 2) 297773 ++ (1424871, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) 1)).
  {
    apply (hGRIND_even 5213 [1123; 365; 245; 40; 14; 5] 6995 ((131712, 2) :: (1, 1) :: repeat (1, 2) 297773 ++ (1424871, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) 1); closearith.
  }
  (* step 289: P TUP2_1 *)
  apply (hsteps_trans _ (HC [6996; 1123; 365; 245; 40; 14; 5] 10430 1 2 ((131710, 2) :: (1, 1) :: repeat (1, 2) 297773 ++ (1424871, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) 1)).
  {
    replace ((131710, 2) :: (1, 1) :: repeat (1, 2) 297773 ++ (1424871, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) with ((131712 - 2, 2) :: (1, 1) :: repeat (1, 2) 297773 ++ (1424871, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) by sec_eq.
    apply (sTUP2_1 [1123; 365; 245; 40; 14; 5] 6995 10429 131712 ((1, 1) :: repeat (1, 2) 297773 ++ (1424871, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) 1); closearith.
  }
  (* step 290: P TDN *)
  apply (hsteps_trans _ (HB [6996; 1123; 365; 245; 40; 14; 5] 10430 1 4 ((131710, 2) :: (1, 1) :: repeat (1, 2) 297773 ++ (1424871, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) 1)).
  {
    apply (sTDN [6996; 1123; 365; 245; 40; 14; 5] 10430 ((131710, 2) :: (1, 1) :: repeat (1, 2) 297773 ++ (1424871, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) 1).
  }
  (* step 291: sTUP *)
  apply (hsteps_trans _ (HC [6996; 1123; 365; 245; 40; 14; 5] 10430 3 2 ((131708, 2) :: (1, 1) :: repeat (1, 2) 297773 ++ (1424871, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) 1)).
  {
    replace ((131708, 2) :: (1, 1) :: repeat (1, 2) 297773 ++ (1424871, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) with ((131710 - 2, 2) :: (1, 1) :: repeat (1, 2) 297773 ++ (1424871, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) by sec_eq.
    apply (sTUP [6996; 1123; 365; 245; 40; 14; 5] 10430 4 131710 2 ((1, 1) :: repeat (1, 2) 297773 ++ (1424871, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) 1); closearith.
  }
  (* step 292: DIPGRIND 10430 110848 *)
  apply (hsteps_trans _ (HC [6996; 1123; 365; 245; 40; 14; 5] 0 3 2 (repeat (1, 2) 10430 ++ (110848, 2) :: (1, 1) :: repeat (1, 2) 297773 ++ (1424871, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) 1)).
  {
    rewrite NUM56X8.
    apply (DIPGRIND 10430 110848 [6996; 1123; 365; 245; 40; 14; 5] ((1, 1) :: repeat (1, 2) 297773 ++ (1424871, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) 1); closearith.
  }
  (* step 293: P PX2A *)
  apply (hsteps_trans _ (HC [365; 245; 40; 14; 5] 1122 6994 2 ((1, 1) :: repeat (1, 2) 10432 ++ (110848, 2) :: (1, 1) :: repeat (1, 2) 297773 ++ (1424871, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) 1)).
  {
    exact (hsteps_step _ _ _ (hPX2A 6993 1122 [365; 245; 40; 14; 5] (repeat (1, 2) 10430 ++ (110848, 2) :: (1, 1) :: repeat (1, 2) 297773 ++ (1424871, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) 1) (hsteps_refl _)).
  }
  (* step 294: P PUSH *)
  apply (hsteps_trans _ (HC [365; 245; 40; 14; 5] 1121 1 2 ((6992, 2) :: (1, 1) :: repeat (1, 2) 10432 ++ (110848, 2) :: (1, 1) :: repeat (1, 2) 297773 ++ (1424871, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) 1)).
  {
    replace ((6992, 2) :: (1, 1) :: repeat (1, 2) 10432 ++ (110848, 2) :: (1, 1) :: repeat (1, 2) 297773 ++ (1424871, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) with ((6994 - 2, 2) :: (1, 1) :: repeat (1, 2) 10432 ++ (110848, 2) :: (1, 1) :: repeat (1, 2) 297773 ++ (1424871, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) by sec_eq.
    apply (sPUSH [365; 245; 40; 14; 5] 1121 6994 ((1, 1) :: repeat (1, 2) 10432 ++ (110848, 2) :: (1, 1) :: repeat (1, 2) 297773 ++ (1424871, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) 1); closearith.
  }
  (* step 295: P TDN *)
  apply (hsteps_trans _ (HB [365; 245; 40; 14; 5] 1121 1 4 ((6992, 2) :: (1, 1) :: repeat (1, 2) 10432 ++ (110848, 2) :: (1, 1) :: repeat (1, 2) 297773 ++ (1424871, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) 1)).
  {
    apply (sTDN [365; 245; 40; 14; 5] 1121 ((6992, 2) :: (1, 1) :: repeat (1, 2) 10432 ++ (110848, 2) :: (1, 1) :: repeat (1, 2) 297773 ++ (1424871, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) 1).
  }
  (* step 296: sTUP *)
  apply (hsteps_trans _ (HC [365; 245; 40; 14; 5] 1121 3 2 ((6990, 2) :: (1, 1) :: repeat (1, 2) 10432 ++ (110848, 2) :: (1, 1) :: repeat (1, 2) 297773 ++ (1424871, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) 1)).
  {
    replace ((6990, 2) :: (1, 1) :: repeat (1, 2) 10432 ++ (110848, 2) :: (1, 1) :: repeat (1, 2) 297773 ++ (1424871, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) with ((6992 - 2, 2) :: (1, 1) :: repeat (1, 2) 10432 ++ (110848, 2) :: (1, 1) :: repeat (1, 2) 297773 ++ (1424871, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) by sec_eq.
    apply (sTUP [365; 245; 40; 14; 5] 1121 4 6992 2 ((1, 1) :: repeat (1, 2) 10432 ++ (110848, 2) :: (1, 1) :: repeat (1, 2) 297773 ++ (1424871, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) 1); closearith.
  }
  (* step 297: DIPGRIND 1121 4748 *)
  apply (hsteps_trans _ (HC [365; 245; 40; 14; 5] 0 3 2 (repeat (1, 2) 1121 ++ (4748, 2) :: (1, 1) :: repeat (1, 2) 10432 ++ (110848, 2) :: (1, 1) :: repeat (1, 2) 297773 ++ (1424871, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) 1)).
  {
    apply (DIPGRIND 1121 4748 [365; 245; 40; 14; 5] ((1, 1) :: repeat (1, 2) 10432 ++ (110848, 2) :: (1, 1) :: repeat (1, 2) 297773 ++ (1424871, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) 1); closearith.
  }
  (* step 298: P PX2A *)
  apply (hsteps_trans _ (HC [40; 14; 5] 244 363 2 ((1, 1) :: repeat (1, 2) 1123 ++ (4748, 2) :: (1, 1) :: repeat (1, 2) 10432 ++ (110848, 2) :: (1, 1) :: repeat (1, 2) 297773 ++ (1424871, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) 1)).
  {
    exact (hsteps_step _ _ _ (hPX2A 362 244 [40; 14; 5] (repeat (1, 2) 1121 ++ (4748, 2) :: (1, 1) :: repeat (1, 2) 10432 ++ (110848, 2) :: (1, 1) :: repeat (1, 2) 297773 ++ (1424871, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) 1) (hsteps_refl _)).
  }
  (* step 299: hGRIND 180 *)
  apply (hsteps_trans _ (HB [40; 14; 5] 244 1 366 ((1, 1) :: repeat (1, 2) 1123 ++ (4748, 2) :: (1, 1) :: repeat (1, 2) 10432 ++ (110848, 2) :: (1, 1) :: repeat (1, 2) 297773 ++ (1424871, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) 1)).
  {
    apply (hGRIND 180 [40; 14; 5] 244 ((1, 1) :: repeat (1, 2) 1123 ++ (4748, 2) :: (1, 1) :: repeat (1, 2) 10432 ++ (110848, 2) :: (1, 1) :: repeat (1, 2) 297773 ++ (1424871, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) 1); closearith.
  }
  (* step 300: P POP *)
  apply (hsteps_trans _ (HB [40; 14; 5] 245 1 367 (repeat (1, 2) 1123 ++ (4748, 2) :: (1, 1) :: repeat (1, 2) 10432 ++ (110848, 2) :: (1, 1) :: repeat (1, 2) 297773 ++ (1424871, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) 1)).
  {
    apply (sPOP1 [40; 14; 5] 244 366 (repeat (1, 2) 1123 ++ (4748, 2) :: (1, 1) :: repeat (1, 2) 10432 ++ (110848, 2) :: (1, 1) :: repeat (1, 2) 297773 ++ (1424871, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) 1); closearith.
  }
  (* step 301: M pop12 (1123,) *)
  apply (hsteps_trans _ (HB [40; 14; 5] 1368 1 2613 ((4748, 2) :: (1, 1) :: repeat (1, 2) 10432 ++ (110848, 2) :: (1, 1) :: repeat (1, 2) 297773 ++ (1424871, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) 1)).
  {
    apply (pop12 1123 [40; 14; 5] 245 367 ((4748, 2) :: (1, 1) :: repeat (1, 2) 10432 ++ (110848, 2) :: (1, 1) :: repeat (1, 2) 297773 ++ (1424871, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) 1); closearith.
  }
  (* step 302: sTUP *)
  apply (hsteps_trans _ (HC [40; 14; 5] 1368 2612 2 ((4746, 2) :: (1, 1) :: repeat (1, 2) 10432 ++ (110848, 2) :: (1, 1) :: repeat (1, 2) 297773 ++ (1424871, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) 1)).
  {
    replace ((4746, 2) :: (1, 1) :: repeat (1, 2) 10432 ++ (110848, 2) :: (1, 1) :: repeat (1, 2) 297773 ++ (1424871, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) with ((4748 - 2, 2) :: (1, 1) :: repeat (1, 2) 10432 ++ (110848, 2) :: (1, 1) :: repeat (1, 2) 297773 ++ (1424871, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) by sec_eq.
    apply (sTUP [40; 14; 5] 1368 2613 4748 2 ((1, 1) :: repeat (1, 2) 10432 ++ (110848, 2) :: (1, 1) :: repeat (1, 2) 297773 ++ (1424871, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) 1); closearith.
  }
  (* step 303: hGRIND_even 1304 *)
  apply (hsteps_trans _ (HB [40; 14; 5] 1367 1 2612 ((2, 2) :: (4746, 2) :: (1, 1) :: repeat (1, 2) 10432 ++ (110848, 2) :: (1, 1) :: repeat (1, 2) 297773 ++ (1424871, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) 1)).
  {
    apply (hGRIND_even 1304 [40; 14; 5] 1367 ((4746, 2) :: (1, 1) :: repeat (1, 2) 10432 ++ (110848, 2) :: (1, 1) :: repeat (1, 2) 297773 ++ (1424871, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) 1); closearith.
  }
  (* step 304: P TUP2_1 *)
  apply (hsteps_trans _ (HC [1368; 40; 14; 5] 2612 1 2 ((4744, 2) :: (1, 1) :: repeat (1, 2) 10432 ++ (110848, 2) :: (1, 1) :: repeat (1, 2) 297773 ++ (1424871, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) 1)).
  {
    replace ((4744, 2) :: (1, 1) :: repeat (1, 2) 10432 ++ (110848, 2) :: (1, 1) :: repeat (1, 2) 297773 ++ (1424871, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) with ((4746 - 2, 2) :: (1, 1) :: repeat (1, 2) 10432 ++ (110848, 2) :: (1, 1) :: repeat (1, 2) 297773 ++ (1424871, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) by sec_eq.
    apply (sTUP2_1 [40; 14; 5] 1367 2611 4746 ((1, 1) :: repeat (1, 2) 10432 ++ (110848, 2) :: (1, 1) :: repeat (1, 2) 297773 ++ (1424871, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) 1); closearith.
  }
  (* step 305: P TDN *)
  apply (hsteps_trans _ (HB [1368; 40; 14; 5] 2612 1 4 ((4744, 2) :: (1, 1) :: repeat (1, 2) 10432 ++ (110848, 2) :: (1, 1) :: repeat (1, 2) 297773 ++ (1424871, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) 1)).
  {
    apply (sTDN [1368; 40; 14; 5] 2612 ((4744, 2) :: (1, 1) :: repeat (1, 2) 10432 ++ (110848, 2) :: (1, 1) :: repeat (1, 2) 297773 ++ (1424871, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) 1).
  }
  (* step 306: sTUP *)
  apply (hsteps_trans _ (HC [1368; 40; 14; 5] 2612 3 2 ((4742, 2) :: (1, 1) :: repeat (1, 2) 10432 ++ (110848, 2) :: (1, 1) :: repeat (1, 2) 297773 ++ (1424871, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) 1)).
  {
    replace ((4742, 2) :: (1, 1) :: repeat (1, 2) 10432 ++ (110848, 2) :: (1, 1) :: repeat (1, 2) 297773 ++ (1424871, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) with ((4744 - 2, 2) :: (1, 1) :: repeat (1, 2) 10432 ++ (110848, 2) :: (1, 1) :: repeat (1, 2) 297773 ++ (1424871, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) by sec_eq.
    apply (sTUP [1368; 40; 14; 5] 2612 4 4744 2 ((1, 1) :: repeat (1, 2) 10432 ++ (110848, 2) :: (1, 1) :: repeat (1, 2) 297773 ++ (1424871, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) 1); closearith.
  }
  (* step 307: CLEANG_even 2370 *)
  apply (hsteps_trans _ (HB [1368; 40; 14; 5] 2612 1 4746 ((2, 2) :: (1, 1) :: repeat (1, 2) 10432 ++ (110848, 2) :: (1, 1) :: repeat (1, 2) 297773 ++ (1424871, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) 1)).
  {
    apply (CLEANG_even 2370 [1368; 40; 14; 5] 2612 ((1, 1) :: repeat (1, 2) 10432 ++ (110848, 2) :: (1, 1) :: repeat (1, 2) 297773 ++ (1424871, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) 1); closearith.
  }
  (* step 308: P TRANS2_1 *)
  apply (hsteps_trans _ (HB [2613; 1368; 40; 14; 5] 4747 1 3 (repeat (1, 2) 10432 ++ (110848, 2) :: (1, 1) :: repeat (1, 2) 297773 ++ (1424871, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) 1)).
  {
    apply (sTRANS2_1 [1368; 40; 14; 5] 2612 4745 1 (repeat (1, 2) 10432 ++ (110848, 2) :: (1, 1) :: repeat (1, 2) 297773 ++ (1424871, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) 1); closearith.
  }
  (* step 309: M pop12 (10432,) *)
  apply (hsteps_trans _ (HB [2613; 1368; 40; 14; 5] 15179 1 20867 ((110848, 2) :: (1, 1) :: repeat (1, 2) 297773 ++ (1424871, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) 1)).
  {
    apply (pop12 10432 [2613; 1368; 40; 14; 5] 4747 3 ((110848, 2) :: (1, 1) :: repeat (1, 2) 297773 ++ (1424871, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) 1); closearith.
  }
  (* step 310: sTUP *)
  apply (hsteps_trans _ (HC [2613; 1368; 40; 14; 5] 15179 20866 2 ((110846, 2) :: (1, 1) :: repeat (1, 2) 297773 ++ (1424871, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) 1)).
  {
    replace ((110846, 2) :: (1, 1) :: repeat (1, 2) 297773 ++ (1424871, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) with ((110848 - 2, 2) :: (1, 1) :: repeat (1, 2) 297773 ++ (1424871, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) by sec_eq.
    apply (sTUP [2613; 1368; 40; 14; 5] 15179 20867 110848 2 ((1, 1) :: repeat (1, 2) 297773 ++ (1424871, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) 1); closearith.
  }
  (* step 311: hGRIND_even 10431 *)
  apply (hsteps_trans _ (HB [2613; 1368; 40; 14; 5] 15178 1 20866 ((2, 2) :: (110846, 2) :: (1, 1) :: repeat (1, 2) 297773 ++ (1424871, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) 1)).
  {
    apply (hGRIND_even 10431 [2613; 1368; 40; 14; 5] 15178 ((110846, 2) :: (1, 1) :: repeat (1, 2) 297773 ++ (1424871, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) 1); closearith.
  }
  (* step 312: P TUP2_1 *)
  apply (hsteps_trans _ (HC [15179; 2613; 1368; 40; 14; 5] 20866 1 2 ((110844, 2) :: (1, 1) :: repeat (1, 2) 297773 ++ (1424871, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) 1)).
  {
    replace ((110844, 2) :: (1, 1) :: repeat (1, 2) 297773 ++ (1424871, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) with ((110846 - 2, 2) :: (1, 1) :: repeat (1, 2) 297773 ++ (1424871, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) by sec_eq.
    apply (sTUP2_1 [2613; 1368; 40; 14; 5] 15178 20865 110846 ((1, 1) :: repeat (1, 2) 297773 ++ (1424871, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) 1); closearith.
  }
  (* step 313: P TDN *)
  apply (hsteps_trans _ (HB [15179; 2613; 1368; 40; 14; 5] 20866 1 4 ((110844, 2) :: (1, 1) :: repeat (1, 2) 297773 ++ (1424871, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) 1)).
  {
    apply (sTDN [15179; 2613; 1368; 40; 14; 5] 20866 ((110844, 2) :: (1, 1) :: repeat (1, 2) 297773 ++ (1424871, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) 1).
  }
  (* step 314: sTUP *)
  apply (hsteps_trans _ (HC [15179; 2613; 1368; 40; 14; 5] 20866 3 2 ((110842, 2) :: (1, 1) :: repeat (1, 2) 297773 ++ (1424871, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) 1)).
  {
    replace ((110842, 2) :: (1, 1) :: repeat (1, 2) 297773 ++ (1424871, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) with ((110844 - 2, 2) :: (1, 1) :: repeat (1, 2) 297773 ++ (1424871, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) by sec_eq.
    apply (sTUP [15179; 2613; 1368; 40; 14; 5] 20866 4 110844 2 ((1, 1) :: repeat (1, 2) 297773 ++ (1424871, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) 1); closearith.
  }
  (* step 315: DIPGRIND 20866 69110 *)
  apply (hsteps_trans _ (HC [15179; 2613; 1368; 40; 14; 5] 0 3 2 (repeat (1, 2) 20866 ++ (69110, 2) :: (1, 1) :: repeat (1, 2) 297773 ++ (1424871, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) 1)).
  {
    rewrite NUM56X9.
    apply (DIPGRIND 20866 69110 [15179; 2613; 1368; 40; 14; 5] ((1, 1) :: repeat (1, 2) 297773 ++ (1424871, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) 1); closearith.
  }
  (* step 316: P PX2A *)
  apply (hsteps_trans _ (HC [1368; 40; 14; 5] 2612 15177 2 ((1, 1) :: repeat (1, 2) 20868 ++ (69110, 2) :: (1, 1) :: repeat (1, 2) 297773 ++ (1424871, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) 1)).
  {
    exact (hsteps_step _ _ _ (hPX2A 15176 2612 [1368; 40; 14; 5] (repeat (1, 2) 20866 ++ (69110, 2) :: (1, 1) :: repeat (1, 2) 297773 ++ (1424871, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) 1) (hsteps_refl _)).
  }
  (* step 317: P PUSH *)
  apply (hsteps_trans _ (HC [1368; 40; 14; 5] 2611 1 2 ((15175, 2) :: (1, 1) :: repeat (1, 2) 20868 ++ (69110, 2) :: (1, 1) :: repeat (1, 2) 297773 ++ (1424871, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) 1)).
  {
    replace ((15175, 2) :: (1, 1) :: repeat (1, 2) 20868 ++ (69110, 2) :: (1, 1) :: repeat (1, 2) 297773 ++ (1424871, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) with ((15177 - 2, 2) :: (1, 1) :: repeat (1, 2) 20868 ++ (69110, 2) :: (1, 1) :: repeat (1, 2) 297773 ++ (1424871, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) by sec_eq.
    apply (sPUSH [1368; 40; 14; 5] 2611 15177 ((1, 1) :: repeat (1, 2) 20868 ++ (69110, 2) :: (1, 1) :: repeat (1, 2) 297773 ++ (1424871, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) 1); closearith.
  }
  (* step 318: P TDN *)
  apply (hsteps_trans _ (HB [1368; 40; 14; 5] 2611 1 4 ((15175, 2) :: (1, 1) :: repeat (1, 2) 20868 ++ (69110, 2) :: (1, 1) :: repeat (1, 2) 297773 ++ (1424871, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) 1)).
  {
    apply (sTDN [1368; 40; 14; 5] 2611 ((15175, 2) :: (1, 1) :: repeat (1, 2) 20868 ++ (69110, 2) :: (1, 1) :: repeat (1, 2) 297773 ++ (1424871, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) 1).
  }
  (* step 319: sTUP *)
  apply (hsteps_trans _ (HC [1368; 40; 14; 5] 2611 3 2 ((15173, 2) :: (1, 1) :: repeat (1, 2) 20868 ++ (69110, 2) :: (1, 1) :: repeat (1, 2) 297773 ++ (1424871, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) 1)).
  {
    replace ((15173, 2) :: (1, 1) :: repeat (1, 2) 20868 ++ (69110, 2) :: (1, 1) :: repeat (1, 2) 297773 ++ (1424871, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) with ((15175 - 2, 2) :: (1, 1) :: repeat (1, 2) 20868 ++ (69110, 2) :: (1, 1) :: repeat (1, 2) 297773 ++ (1424871, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) by sec_eq.
    apply (sTUP [1368; 40; 14; 5] 2611 4 15175 2 ((1, 1) :: repeat (1, 2) 20868 ++ (69110, 2) :: (1, 1) :: repeat (1, 2) 297773 ++ (1424871, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) 1); closearith.
  }
  (* step 320: DIPGRIND 2611 9951 *)
  apply (hsteps_trans _ (HC [1368; 40; 14; 5] 0 3 2 (repeat (1, 2) 2611 ++ (9951, 2) :: (1, 1) :: repeat (1, 2) 20868 ++ (69110, 2) :: (1, 1) :: repeat (1, 2) 297773 ++ (1424871, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) 1)).
  {
    apply (DIPGRIND 2611 9951 [1368; 40; 14; 5] ((1, 1) :: repeat (1, 2) 20868 ++ (69110, 2) :: (1, 1) :: repeat (1, 2) 297773 ++ (1424871, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) 1); closearith.
  }
  (* step 321: P PX2A *)
  apply (hsteps_trans _ (HC [14; 5] 39 1366 2 ((1, 1) :: repeat (1, 2) 2613 ++ (9951, 2) :: (1, 1) :: repeat (1, 2) 20868 ++ (69110, 2) :: (1, 1) :: repeat (1, 2) 297773 ++ (1424871, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) 1)).
  {
    exact (hsteps_step _ _ _ (hPX2A 1365 39 [14; 5] (repeat (1, 2) 2611 ++ (9951, 2) :: (1, 1) :: repeat (1, 2) 20868 ++ (69110, 2) :: (1, 1) :: repeat (1, 2) 297773 ++ (1424871, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) 1) (hsteps_refl _)).
  }
  (* step 322: P PUSH *)
  apply (hsteps_trans _ (HC [14; 5] 38 1 2 ((1364, 2) :: (1, 1) :: repeat (1, 2) 2613 ++ (9951, 2) :: (1, 1) :: repeat (1, 2) 20868 ++ (69110, 2) :: (1, 1) :: repeat (1, 2) 297773 ++ (1424871, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) 1)).
  {
    replace ((1364, 2) :: (1, 1) :: repeat (1, 2) 2613 ++ (9951, 2) :: (1, 1) :: repeat (1, 2) 20868 ++ (69110, 2) :: (1, 1) :: repeat (1, 2) 297773 ++ (1424871, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) with ((1366 - 2, 2) :: (1, 1) :: repeat (1, 2) 2613 ++ (9951, 2) :: (1, 1) :: repeat (1, 2) 20868 ++ (69110, 2) :: (1, 1) :: repeat (1, 2) 297773 ++ (1424871, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) by sec_eq.
    apply (sPUSH [14; 5] 38 1366 ((1, 1) :: repeat (1, 2) 2613 ++ (9951, 2) :: (1, 1) :: repeat (1, 2) 20868 ++ (69110, 2) :: (1, 1) :: repeat (1, 2) 297773 ++ (1424871, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) 1); closearith.
  }
  (* step 323: P TDN *)
  apply (hsteps_trans _ (HB [14; 5] 38 1 4 ((1364, 2) :: (1, 1) :: repeat (1, 2) 2613 ++ (9951, 2) :: (1, 1) :: repeat (1, 2) 20868 ++ (69110, 2) :: (1, 1) :: repeat (1, 2) 297773 ++ (1424871, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) 1)).
  {
    apply (sTDN [14; 5] 38 ((1364, 2) :: (1, 1) :: repeat (1, 2) 2613 ++ (9951, 2) :: (1, 1) :: repeat (1, 2) 20868 ++ (69110, 2) :: (1, 1) :: repeat (1, 2) 297773 ++ (1424871, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) 1).
  }
  (* step 324: sTUP *)
  apply (hsteps_trans _ (HC [14; 5] 38 3 2 ((1362, 2) :: (1, 1) :: repeat (1, 2) 2613 ++ (9951, 2) :: (1, 1) :: repeat (1, 2) 20868 ++ (69110, 2) :: (1, 1) :: repeat (1, 2) 297773 ++ (1424871, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) 1)).
  {
    replace ((1362, 2) :: (1, 1) :: repeat (1, 2) 2613 ++ (9951, 2) :: (1, 1) :: repeat (1, 2) 20868 ++ (69110, 2) :: (1, 1) :: repeat (1, 2) 297773 ++ (1424871, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) with ((1364 - 2, 2) :: (1, 1) :: repeat (1, 2) 2613 ++ (9951, 2) :: (1, 1) :: repeat (1, 2) 20868 ++ (69110, 2) :: (1, 1) :: repeat (1, 2) 297773 ++ (1424871, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) by sec_eq.
    apply (sTUP [14; 5] 38 4 1364 2 ((1, 1) :: repeat (1, 2) 2613 ++ (9951, 2) :: (1, 1) :: repeat (1, 2) 20868 ++ (69110, 2) :: (1, 1) :: repeat (1, 2) 297773 ++ (1424871, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) 1); closearith.
  }
  (* step 325: DIPGRIND 38 1286 *)
  apply (hsteps_trans _ (HC [14; 5] 0 3 2 (repeat (1, 2) 38 ++ (1286, 2) :: (1, 1) :: repeat (1, 2) 2613 ++ (9951, 2) :: (1, 1) :: repeat (1, 2) 20868 ++ (69110, 2) :: (1, 1) :: repeat (1, 2) 297773 ++ (1424871, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) 1)).
  {
    apply (DIPGRIND 38 1286 [14; 5] ((1, 1) :: repeat (1, 2) 2613 ++ (9951, 2) :: (1, 1) :: repeat (1, 2) 20868 ++ (69110, 2) :: (1, 1) :: repeat (1, 2) 297773 ++ (1424871, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) 1); closearith.
  }
  (* step 326: P PX2A *)
  apply (hsteps_trans _ (HC [] 4 12 2 ((1, 1) :: repeat (1, 2) 40 ++ (1286, 2) :: (1, 1) :: repeat (1, 2) 2613 ++ (9951, 2) :: (1, 1) :: repeat (1, 2) 20868 ++ (69110, 2) :: (1, 1) :: repeat (1, 2) 297773 ++ (1424871, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) 1)).
  {
    exact (hsteps_step _ _ _ (hPX2A 11 4 [] (repeat (1, 2) 38 ++ (1286, 2) :: (1, 1) :: repeat (1, 2) 2613 ++ (9951, 2) :: (1, 1) :: repeat (1, 2) 20868 ++ (69110, 2) :: (1, 1) :: repeat (1, 2) 297773 ++ (1424871, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) 1) (hsteps_refl _)).
  }
  (* step 327: P PUSH *)
  apply (hsteps_trans _ (HC [] 3 1 2 ((10, 2) :: (1, 1) :: repeat (1, 2) 40 ++ (1286, 2) :: (1, 1) :: repeat (1, 2) 2613 ++ (9951, 2) :: (1, 1) :: repeat (1, 2) 20868 ++ (69110, 2) :: (1, 1) :: repeat (1, 2) 297773 ++ (1424871, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) 1)).
  {
    replace ((10, 2) :: (1, 1) :: repeat (1, 2) 40 ++ (1286, 2) :: (1, 1) :: repeat (1, 2) 2613 ++ (9951, 2) :: (1, 1) :: repeat (1, 2) 20868 ++ (69110, 2) :: (1, 1) :: repeat (1, 2) 297773 ++ (1424871, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) with ((12 - 2, 2) :: (1, 1) :: repeat (1, 2) 40 ++ (1286, 2) :: (1, 1) :: repeat (1, 2) 2613 ++ (9951, 2) :: (1, 1) :: repeat (1, 2) 20868 ++ (69110, 2) :: (1, 1) :: repeat (1, 2) 297773 ++ (1424871, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) by sec_eq.
    apply (sPUSH [] 3 12 ((1, 1) :: repeat (1, 2) 40 ++ (1286, 2) :: (1, 1) :: repeat (1, 2) 2613 ++ (9951, 2) :: (1, 1) :: repeat (1, 2) 20868 ++ (69110, 2) :: (1, 1) :: repeat (1, 2) 297773 ++ (1424871, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) 1); closearith.
  }
  (* step 328: P TDN *)
  apply (hsteps_trans _ (HB [] 3 1 4 ((10, 2) :: (1, 1) :: repeat (1, 2) 40 ++ (1286, 2) :: (1, 1) :: repeat (1, 2) 2613 ++ (9951, 2) :: (1, 1) :: repeat (1, 2) 20868 ++ (69110, 2) :: (1, 1) :: repeat (1, 2) 297773 ++ (1424871, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) 1)).
  {
    apply (sTDN [] 3 ((10, 2) :: (1, 1) :: repeat (1, 2) 40 ++ (1286, 2) :: (1, 1) :: repeat (1, 2) 2613 ++ (9951, 2) :: (1, 1) :: repeat (1, 2) 20868 ++ (69110, 2) :: (1, 1) :: repeat (1, 2) 297773 ++ (1424871, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) 1).
  }
  (* step 329: sTUP *)
  apply (hsteps_trans _ (HC [] 3 3 2 ((8, 2) :: (1, 1) :: repeat (1, 2) 40 ++ (1286, 2) :: (1, 1) :: repeat (1, 2) 2613 ++ (9951, 2) :: (1, 1) :: repeat (1, 2) 20868 ++ (69110, 2) :: (1, 1) :: repeat (1, 2) 297773 ++ (1424871, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) 1)).
  {
    replace ((8, 2) :: (1, 1) :: repeat (1, 2) 40 ++ (1286, 2) :: (1, 1) :: repeat (1, 2) 2613 ++ (9951, 2) :: (1, 1) :: repeat (1, 2) 20868 ++ (69110, 2) :: (1, 1) :: repeat (1, 2) 297773 ++ (1424871, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) with ((10 - 2, 2) :: (1, 1) :: repeat (1, 2) 40 ++ (1286, 2) :: (1, 1) :: repeat (1, 2) 2613 ++ (9951, 2) :: (1, 1) :: repeat (1, 2) 20868 ++ (69110, 2) :: (1, 1) :: repeat (1, 2) 297773 ++ (1424871, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) by sec_eq.
    apply (sTUP [] 3 4 10 2 ((1, 1) :: repeat (1, 2) 40 ++ (1286, 2) :: (1, 1) :: repeat (1, 2) 2613 ++ (9951, 2) :: (1, 1) :: repeat (1, 2) 20868 ++ (69110, 2) :: (1, 1) :: repeat (1, 2) 297773 ++ (1424871, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) 1); closearith.
  }
  (* step 330: DIPGRIND 3 2 *)
  apply (hsteps_trans _ (HC [] 0 3 2 (repeat (1, 2) 3 ++ (2, 2) :: (1, 1) :: repeat (1, 2) 40 ++ (1286, 2) :: (1, 1) :: repeat (1, 2) 2613 ++ (9951, 2) :: (1, 1) :: repeat (1, 2) 20868 ++ (69110, 2) :: (1, 1) :: repeat (1, 2) 297773 ++ (1424871, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) 1)).
  {
    apply (DIPGRIND 3 2 [] ((1, 1) :: repeat (1, 2) 40 ++ (1286, 2) :: (1, 1) :: repeat (1, 2) 2613 ++ (9951, 2) :: (1, 1) :: repeat (1, 2) 20868 ++ (69110, 2) :: (1, 1) :: repeat (1, 2) 297773 ++ (1424871, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) 1); closearith.
  }
  (* step 331: P PUSHX *)
  apply (hsteps_trans _ (HB [] 1 1 7 (repeat (1, 2) 3 ++ (2, 2) :: (1, 1) :: repeat (1, 2) 40 ++ (1286, 2) :: (1, 1) :: repeat (1, 2) 2613 ++ (9951, 2) :: (1, 1) :: repeat (1, 2) 20868 ++ (69110, 2) :: (1, 1) :: repeat (1, 2) 297773 ++ (1424871, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) 1)).
  {
    exact (hsteps_step _ _ _ (hPUSHX (repeat (1, 2) 3 ++ (2, 2) :: (1, 1) :: repeat (1, 2) 40 ++ (1286, 2) :: (1, 1) :: repeat (1, 2) 2613 ++ (9951, 2) :: (1, 1) :: repeat (1, 2) 20868 ++ (69110, 2) :: (1, 1) :: repeat (1, 2) 297773 ++ (1424871, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) 1) (hsteps_refl _)).
  }
  (* step 332: M pop12 (3,) *)
  apply (hsteps_trans _ (HB [] 4 1 13 ((2, 2) :: (1, 1) :: repeat (1, 2) 40 ++ (1286, 2) :: (1, 1) :: repeat (1, 2) 2613 ++ (9951, 2) :: (1, 1) :: repeat (1, 2) 20868 ++ (69110, 2) :: (1, 1) :: repeat (1, 2) 297773 ++ (1424871, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) 1)).
  {
    apply (pop12 3 [] 1 7 ((2, 2) :: (1, 1) :: repeat (1, 2) 40 ++ (1286, 2) :: (1, 1) :: repeat (1, 2) 2613 ++ (9951, 2) :: (1, 1) :: repeat (1, 2) 20868 ++ (69110, 2) :: (1, 1) :: repeat (1, 2) 297773 ++ (1424871, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) 1); closearith.
  }
  (* step 333: P TRANS2_1 *)
  apply (hsteps_trans _ (HB [5] 14 1 3 (repeat (1, 2) 40 ++ (1286, 2) :: (1, 1) :: repeat (1, 2) 2613 ++ (9951, 2) :: (1, 1) :: repeat (1, 2) 20868 ++ (69110, 2) :: (1, 1) :: repeat (1, 2) 297773 ++ (1424871, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) 1)).
  {
    apply (sTRANS2_1 [] 4 12 1 (repeat (1, 2) 40 ++ (1286, 2) :: (1, 1) :: repeat (1, 2) 2613 ++ (9951, 2) :: (1, 1) :: repeat (1, 2) 20868 ++ (69110, 2) :: (1, 1) :: repeat (1, 2) 297773 ++ (1424871, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) 1); closearith.
  }
  (* step 334: M pop12 (40,) *)
  apply (hsteps_trans _ (HB [5] 54 1 83 ((1286, 2) :: (1, 1) :: repeat (1, 2) 2613 ++ (9951, 2) :: (1, 1) :: repeat (1, 2) 20868 ++ (69110, 2) :: (1, 1) :: repeat (1, 2) 297773 ++ (1424871, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) 1)).
  {
    apply (pop12 40 [5] 14 3 ((1286, 2) :: (1, 1) :: repeat (1, 2) 2613 ++ (9951, 2) :: (1, 1) :: repeat (1, 2) 20868 ++ (69110, 2) :: (1, 1) :: repeat (1, 2) 297773 ++ (1424871, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) 1); closearith.
  }
  (* step 335: sTUP *)
  apply (hsteps_trans _ (HC [5] 54 82 2 ((1284, 2) :: (1, 1) :: repeat (1, 2) 2613 ++ (9951, 2) :: (1, 1) :: repeat (1, 2) 20868 ++ (69110, 2) :: (1, 1) :: repeat (1, 2) 297773 ++ (1424871, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) 1)).
  {
    replace ((1284, 2) :: (1, 1) :: repeat (1, 2) 2613 ++ (9951, 2) :: (1, 1) :: repeat (1, 2) 20868 ++ (69110, 2) :: (1, 1) :: repeat (1, 2) 297773 ++ (1424871, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) with ((1286 - 2, 2) :: (1, 1) :: repeat (1, 2) 2613 ++ (9951, 2) :: (1, 1) :: repeat (1, 2) 20868 ++ (69110, 2) :: (1, 1) :: repeat (1, 2) 297773 ++ (1424871, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) by sec_eq.
    apply (sTUP [5] 54 83 1286 2 ((1, 1) :: repeat (1, 2) 2613 ++ (9951, 2) :: (1, 1) :: repeat (1, 2) 20868 ++ (69110, 2) :: (1, 1) :: repeat (1, 2) 297773 ++ (1424871, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) 1); closearith.
  }
  (* step 336: hGRIND_even 39 *)
  apply (hGRIND_even 39 [5] 53 ((1284, 2) :: (1, 1) :: repeat (1, 2) 2613 ++ (9951, 2) :: (1, 1) :: repeat (1, 2) 20868 ++ (69110, 2) :: (1, 1) :: repeat (1, 2) 297773 ++ (1424871, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) 1); closearith.
Qed.

(* CASCADE56g: steps 337-392 of the CASCADE56 chain. *)
Lemma CASCADE56g : forall w,
  hsteps (HB [5] 53 1 82 ((2, 2) :: (1284, 2) :: (1, 1) :: repeat (1, 2) 2613 ++ (9951, 2) :: (1, 1) :: repeat (1, 2) 20868 ++ (69110, 2) :: (1, 1) :: repeat (1, 2) 297773 ++ (1424871, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) 1)
         (HC [] 3 3 2 ((8, 2) :: (4, 2) :: (1, 1) :: repeat (1, 2) 35 ++ (21, 2) :: (1, 1) :: repeat (1, 2) 172 ++ (770, 2) :: (1, 1) :: repeat (1, 2) 2613 ++ (9951, 2) :: (1, 1) :: repeat (1, 2) 20868 ++ (69110, 2) :: (1, 1) :: repeat (1, 2) 297773 ++ (1424871, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) 1).
Proof.
  intro w.
  (* step 337: P TUP2_1 *)
  apply (hsteps_trans _ (HC [54; 5] 82 1 2 ((1282, 2) :: (1, 1) :: repeat (1, 2) 2613 ++ (9951, 2) :: (1, 1) :: repeat (1, 2) 20868 ++ (69110, 2) :: (1, 1) :: repeat (1, 2) 297773 ++ (1424871, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) 1)).
  {
    replace ((1282, 2) :: (1, 1) :: repeat (1, 2) 2613 ++ (9951, 2) :: (1, 1) :: repeat (1, 2) 20868 ++ (69110, 2) :: (1, 1) :: repeat (1, 2) 297773 ++ (1424871, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) with ((1284 - 2, 2) :: (1, 1) :: repeat (1, 2) 2613 ++ (9951, 2) :: (1, 1) :: repeat (1, 2) 20868 ++ (69110, 2) :: (1, 1) :: repeat (1, 2) 297773 ++ (1424871, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) by sec_eq.
    apply (sTUP2_1 [5] 53 81 1284 ((1, 1) :: repeat (1, 2) 2613 ++ (9951, 2) :: (1, 1) :: repeat (1, 2) 20868 ++ (69110, 2) :: (1, 1) :: repeat (1, 2) 297773 ++ (1424871, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) 1); closearith.
  }
  (* step 338: P TDN *)
  apply (hsteps_trans _ (HB [54; 5] 82 1 4 ((1282, 2) :: (1, 1) :: repeat (1, 2) 2613 ++ (9951, 2) :: (1, 1) :: repeat (1, 2) 20868 ++ (69110, 2) :: (1, 1) :: repeat (1, 2) 297773 ++ (1424871, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) 1)).
  {
    apply (sTDN [54; 5] 82 ((1282, 2) :: (1, 1) :: repeat (1, 2) 2613 ++ (9951, 2) :: (1, 1) :: repeat (1, 2) 20868 ++ (69110, 2) :: (1, 1) :: repeat (1, 2) 297773 ++ (1424871, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) 1).
  }
  (* step 339: sTUP *)
  apply (hsteps_trans _ (HC [54; 5] 82 3 2 ((1280, 2) :: (1, 1) :: repeat (1, 2) 2613 ++ (9951, 2) :: (1, 1) :: repeat (1, 2) 20868 ++ (69110, 2) :: (1, 1) :: repeat (1, 2) 297773 ++ (1424871, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) 1)).
  {
    replace ((1280, 2) :: (1, 1) :: repeat (1, 2) 2613 ++ (9951, 2) :: (1, 1) :: repeat (1, 2) 20868 ++ (69110, 2) :: (1, 1) :: repeat (1, 2) 297773 ++ (1424871, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) with ((1282 - 2, 2) :: (1, 1) :: repeat (1, 2) 2613 ++ (9951, 2) :: (1, 1) :: repeat (1, 2) 20868 ++ (69110, 2) :: (1, 1) :: repeat (1, 2) 297773 ++ (1424871, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) by sec_eq.
    apply (sTUP [54; 5] 82 4 1282 2 ((1, 1) :: repeat (1, 2) 2613 ++ (9951, 2) :: (1, 1) :: repeat (1, 2) 20868 ++ (69110, 2) :: (1, 1) :: repeat (1, 2) 297773 ++ (1424871, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) 1); closearith.
  }
  (* step 340: DIPGRIND 82 1116 *)
  apply (hsteps_trans _ (HC [54; 5] 0 3 2 (repeat (1, 2) 82 ++ (1116, 2) :: (1, 1) :: repeat (1, 2) 2613 ++ (9951, 2) :: (1, 1) :: repeat (1, 2) 20868 ++ (69110, 2) :: (1, 1) :: repeat (1, 2) 297773 ++ (1424871, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) 1)).
  {
    apply (DIPGRIND 82 1116 [54; 5] ((1, 1) :: repeat (1, 2) 2613 ++ (9951, 2) :: (1, 1) :: repeat (1, 2) 20868 ++ (69110, 2) :: (1, 1) :: repeat (1, 2) 297773 ++ (1424871, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) 1); closearith.
  }
  (* step 341: P PX2A *)
  apply (hsteps_trans _ (HC [] 4 52 2 ((1, 1) :: repeat (1, 2) 84 ++ (1116, 2) :: (1, 1) :: repeat (1, 2) 2613 ++ (9951, 2) :: (1, 1) :: repeat (1, 2) 20868 ++ (69110, 2) :: (1, 1) :: repeat (1, 2) 297773 ++ (1424871, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) 1)).
  {
    exact (hsteps_step _ _ _ (hPX2A 51 4 [] (repeat (1, 2) 82 ++ (1116, 2) :: (1, 1) :: repeat (1, 2) 2613 ++ (9951, 2) :: (1, 1) :: repeat (1, 2) 20868 ++ (69110, 2) :: (1, 1) :: repeat (1, 2) 297773 ++ (1424871, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) 1) (hsteps_refl _)).
  }
  (* step 342: P PUSH *)
  apply (hsteps_trans _ (HC [] 3 1 2 ((50, 2) :: (1, 1) :: repeat (1, 2) 84 ++ (1116, 2) :: (1, 1) :: repeat (1, 2) 2613 ++ (9951, 2) :: (1, 1) :: repeat (1, 2) 20868 ++ (69110, 2) :: (1, 1) :: repeat (1, 2) 297773 ++ (1424871, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) 1)).
  {
    replace ((50, 2) :: (1, 1) :: repeat (1, 2) 84 ++ (1116, 2) :: (1, 1) :: repeat (1, 2) 2613 ++ (9951, 2) :: (1, 1) :: repeat (1, 2) 20868 ++ (69110, 2) :: (1, 1) :: repeat (1, 2) 297773 ++ (1424871, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) with ((52 - 2, 2) :: (1, 1) :: repeat (1, 2) 84 ++ (1116, 2) :: (1, 1) :: repeat (1, 2) 2613 ++ (9951, 2) :: (1, 1) :: repeat (1, 2) 20868 ++ (69110, 2) :: (1, 1) :: repeat (1, 2) 297773 ++ (1424871, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) by sec_eq.
    apply (sPUSH [] 3 52 ((1, 1) :: repeat (1, 2) 84 ++ (1116, 2) :: (1, 1) :: repeat (1, 2) 2613 ++ (9951, 2) :: (1, 1) :: repeat (1, 2) 20868 ++ (69110, 2) :: (1, 1) :: repeat (1, 2) 297773 ++ (1424871, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) 1); closearith.
  }
  (* step 343: P TDN *)
  apply (hsteps_trans _ (HB [] 3 1 4 ((50, 2) :: (1, 1) :: repeat (1, 2) 84 ++ (1116, 2) :: (1, 1) :: repeat (1, 2) 2613 ++ (9951, 2) :: (1, 1) :: repeat (1, 2) 20868 ++ (69110, 2) :: (1, 1) :: repeat (1, 2) 297773 ++ (1424871, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) 1)).
  {
    apply (sTDN [] 3 ((50, 2) :: (1, 1) :: repeat (1, 2) 84 ++ (1116, 2) :: (1, 1) :: repeat (1, 2) 2613 ++ (9951, 2) :: (1, 1) :: repeat (1, 2) 20868 ++ (69110, 2) :: (1, 1) :: repeat (1, 2) 297773 ++ (1424871, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) 1).
  }
  (* step 344: sTUP *)
  apply (hsteps_trans _ (HC [] 3 3 2 ((48, 2) :: (1, 1) :: repeat (1, 2) 84 ++ (1116, 2) :: (1, 1) :: repeat (1, 2) 2613 ++ (9951, 2) :: (1, 1) :: repeat (1, 2) 20868 ++ (69110, 2) :: (1, 1) :: repeat (1, 2) 297773 ++ (1424871, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) 1)).
  {
    replace ((48, 2) :: (1, 1) :: repeat (1, 2) 84 ++ (1116, 2) :: (1, 1) :: repeat (1, 2) 2613 ++ (9951, 2) :: (1, 1) :: repeat (1, 2) 20868 ++ (69110, 2) :: (1, 1) :: repeat (1, 2) 297773 ++ (1424871, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) with ((50 - 2, 2) :: (1, 1) :: repeat (1, 2) 84 ++ (1116, 2) :: (1, 1) :: repeat (1, 2) 2613 ++ (9951, 2) :: (1, 1) :: repeat (1, 2) 20868 ++ (69110, 2) :: (1, 1) :: repeat (1, 2) 297773 ++ (1424871, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) by sec_eq.
    apply (sTUP [] 3 4 50 2 ((1, 1) :: repeat (1, 2) 84 ++ (1116, 2) :: (1, 1) :: repeat (1, 2) 2613 ++ (9951, 2) :: (1, 1) :: repeat (1, 2) 20868 ++ (69110, 2) :: (1, 1) :: repeat (1, 2) 297773 ++ (1424871, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) 1); closearith.
  }
  (* step 345: DIPGRIND 3 42 *)
  apply (hsteps_trans _ (HC [] 0 3 2 (repeat (1, 2) 3 ++ (42, 2) :: (1, 1) :: repeat (1, 2) 84 ++ (1116, 2) :: (1, 1) :: repeat (1, 2) 2613 ++ (9951, 2) :: (1, 1) :: repeat (1, 2) 20868 ++ (69110, 2) :: (1, 1) :: repeat (1, 2) 297773 ++ (1424871, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) 1)).
  {
    apply (DIPGRIND 3 42 [] ((1, 1) :: repeat (1, 2) 84 ++ (1116, 2) :: (1, 1) :: repeat (1, 2) 2613 ++ (9951, 2) :: (1, 1) :: repeat (1, 2) 20868 ++ (69110, 2) :: (1, 1) :: repeat (1, 2) 297773 ++ (1424871, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) 1); closearith.
  }
  (* step 346: P PUSHX *)
  apply (hsteps_trans _ (HB [] 1 1 7 (repeat (1, 2) 3 ++ (42, 2) :: (1, 1) :: repeat (1, 2) 84 ++ (1116, 2) :: (1, 1) :: repeat (1, 2) 2613 ++ (9951, 2) :: (1, 1) :: repeat (1, 2) 20868 ++ (69110, 2) :: (1, 1) :: repeat (1, 2) 297773 ++ (1424871, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) 1)).
  {
    exact (hsteps_step _ _ _ (hPUSHX (repeat (1, 2) 3 ++ (42, 2) :: (1, 1) :: repeat (1, 2) 84 ++ (1116, 2) :: (1, 1) :: repeat (1, 2) 2613 ++ (9951, 2) :: (1, 1) :: repeat (1, 2) 20868 ++ (69110, 2) :: (1, 1) :: repeat (1, 2) 297773 ++ (1424871, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) 1) (hsteps_refl _)).
  }
  (* step 347: M pop12 (3,) *)
  apply (hsteps_trans _ (HB [] 4 1 13 ((42, 2) :: (1, 1) :: repeat (1, 2) 84 ++ (1116, 2) :: (1, 1) :: repeat (1, 2) 2613 ++ (9951, 2) :: (1, 1) :: repeat (1, 2) 20868 ++ (69110, 2) :: (1, 1) :: repeat (1, 2) 297773 ++ (1424871, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) 1)).
  {
    apply (pop12 3 [] 1 7 ((42, 2) :: (1, 1) :: repeat (1, 2) 84 ++ (1116, 2) :: (1, 1) :: repeat (1, 2) 2613 ++ (9951, 2) :: (1, 1) :: repeat (1, 2) 20868 ++ (69110, 2) :: (1, 1) :: repeat (1, 2) 297773 ++ (1424871, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) 1); closearith.
  }
  (* step 348: sTUP *)
  apply (hsteps_trans _ (HC [] 4 12 2 ((40, 2) :: (1, 1) :: repeat (1, 2) 84 ++ (1116, 2) :: (1, 1) :: repeat (1, 2) 2613 ++ (9951, 2) :: (1, 1) :: repeat (1, 2) 20868 ++ (69110, 2) :: (1, 1) :: repeat (1, 2) 297773 ++ (1424871, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) 1)).
  {
    replace ((40, 2) :: (1, 1) :: repeat (1, 2) 84 ++ (1116, 2) :: (1, 1) :: repeat (1, 2) 2613 ++ (9951, 2) :: (1, 1) :: repeat (1, 2) 20868 ++ (69110, 2) :: (1, 1) :: repeat (1, 2) 297773 ++ (1424871, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) with ((42 - 2, 2) :: (1, 1) :: repeat (1, 2) 84 ++ (1116, 2) :: (1, 1) :: repeat (1, 2) 2613 ++ (9951, 2) :: (1, 1) :: repeat (1, 2) 20868 ++ (69110, 2) :: (1, 1) :: repeat (1, 2) 297773 ++ (1424871, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) by sec_eq.
    apply (sTUP [] 4 13 42 2 ((1, 1) :: repeat (1, 2) 84 ++ (1116, 2) :: (1, 1) :: repeat (1, 2) 2613 ++ (9951, 2) :: (1, 1) :: repeat (1, 2) 20868 ++ (69110, 2) :: (1, 1) :: repeat (1, 2) 297773 ++ (1424871, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) 1); closearith.
  }
  (* step 349: P PUSH *)
  apply (hsteps_trans _ (HC [] 3 1 2 ((10, 2) :: (40, 2) :: (1, 1) :: repeat (1, 2) 84 ++ (1116, 2) :: (1, 1) :: repeat (1, 2) 2613 ++ (9951, 2) :: (1, 1) :: repeat (1, 2) 20868 ++ (69110, 2) :: (1, 1) :: repeat (1, 2) 297773 ++ (1424871, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) 1)).
  {
    replace ((10, 2) :: (40, 2) :: (1, 1) :: repeat (1, 2) 84 ++ (1116, 2) :: (1, 1) :: repeat (1, 2) 2613 ++ (9951, 2) :: (1, 1) :: repeat (1, 2) 20868 ++ (69110, 2) :: (1, 1) :: repeat (1, 2) 297773 ++ (1424871, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) with ((12 - 2, 2) :: (40, 2) :: (1, 1) :: repeat (1, 2) 84 ++ (1116, 2) :: (1, 1) :: repeat (1, 2) 2613 ++ (9951, 2) :: (1, 1) :: repeat (1, 2) 20868 ++ (69110, 2) :: (1, 1) :: repeat (1, 2) 297773 ++ (1424871, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) by sec_eq.
    apply (sPUSH [] 3 12 ((40, 2) :: (1, 1) :: repeat (1, 2) 84 ++ (1116, 2) :: (1, 1) :: repeat (1, 2) 2613 ++ (9951, 2) :: (1, 1) :: repeat (1, 2) 20868 ++ (69110, 2) :: (1, 1) :: repeat (1, 2) 297773 ++ (1424871, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) 1); closearith.
  }
  (* step 350: P TDN *)
  apply (hsteps_trans _ (HB [] 3 1 4 ((10, 2) :: (40, 2) :: (1, 1) :: repeat (1, 2) 84 ++ (1116, 2) :: (1, 1) :: repeat (1, 2) 2613 ++ (9951, 2) :: (1, 1) :: repeat (1, 2) 20868 ++ (69110, 2) :: (1, 1) :: repeat (1, 2) 297773 ++ (1424871, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) 1)).
  {
    apply (sTDN [] 3 ((10, 2) :: (40, 2) :: (1, 1) :: repeat (1, 2) 84 ++ (1116, 2) :: (1, 1) :: repeat (1, 2) 2613 ++ (9951, 2) :: (1, 1) :: repeat (1, 2) 20868 ++ (69110, 2) :: (1, 1) :: repeat (1, 2) 297773 ++ (1424871, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) 1).
  }
  (* step 351: sTUP *)
  apply (hsteps_trans _ (HC [] 3 3 2 ((8, 2) :: (40, 2) :: (1, 1) :: repeat (1, 2) 84 ++ (1116, 2) :: (1, 1) :: repeat (1, 2) 2613 ++ (9951, 2) :: (1, 1) :: repeat (1, 2) 20868 ++ (69110, 2) :: (1, 1) :: repeat (1, 2) 297773 ++ (1424871, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) 1)).
  {
    replace ((8, 2) :: (40, 2) :: (1, 1) :: repeat (1, 2) 84 ++ (1116, 2) :: (1, 1) :: repeat (1, 2) 2613 ++ (9951, 2) :: (1, 1) :: repeat (1, 2) 20868 ++ (69110, 2) :: (1, 1) :: repeat (1, 2) 297773 ++ (1424871, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) with ((10 - 2, 2) :: (40, 2) :: (1, 1) :: repeat (1, 2) 84 ++ (1116, 2) :: (1, 1) :: repeat (1, 2) 2613 ++ (9951, 2) :: (1, 1) :: repeat (1, 2) 20868 ++ (69110, 2) :: (1, 1) :: repeat (1, 2) 297773 ++ (1424871, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) by sec_eq.
    apply (sTUP [] 3 4 10 2 ((40, 2) :: (1, 1) :: repeat (1, 2) 84 ++ (1116, 2) :: (1, 1) :: repeat (1, 2) 2613 ++ (9951, 2) :: (1, 1) :: repeat (1, 2) 20868 ++ (69110, 2) :: (1, 1) :: repeat (1, 2) 297773 ++ (1424871, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) 1); closearith.
  }
  (* step 352: DIPGRIND 3 2 *)
  apply (hsteps_trans _ (HC [] 0 3 2 (repeat (1, 2) 3 ++ (2, 2) :: (40, 2) :: (1, 1) :: repeat (1, 2) 84 ++ (1116, 2) :: (1, 1) :: repeat (1, 2) 2613 ++ (9951, 2) :: (1, 1) :: repeat (1, 2) 20868 ++ (69110, 2) :: (1, 1) :: repeat (1, 2) 297773 ++ (1424871, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) 1)).
  {
    apply (DIPGRIND 3 2 [] ((40, 2) :: (1, 1) :: repeat (1, 2) 84 ++ (1116, 2) :: (1, 1) :: repeat (1, 2) 2613 ++ (9951, 2) :: (1, 1) :: repeat (1, 2) 20868 ++ (69110, 2) :: (1, 1) :: repeat (1, 2) 297773 ++ (1424871, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) 1); closearith.
  }
  (* step 353: P PUSHX *)
  apply (hsteps_trans _ (HB [] 1 1 7 (repeat (1, 2) 3 ++ (2, 2) :: (40, 2) :: (1, 1) :: repeat (1, 2) 84 ++ (1116, 2) :: (1, 1) :: repeat (1, 2) 2613 ++ (9951, 2) :: (1, 1) :: repeat (1, 2) 20868 ++ (69110, 2) :: (1, 1) :: repeat (1, 2) 297773 ++ (1424871, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) 1)).
  {
    exact (hsteps_step _ _ _ (hPUSHX (repeat (1, 2) 3 ++ (2, 2) :: (40, 2) :: (1, 1) :: repeat (1, 2) 84 ++ (1116, 2) :: (1, 1) :: repeat (1, 2) 2613 ++ (9951, 2) :: (1, 1) :: repeat (1, 2) 20868 ++ (69110, 2) :: (1, 1) :: repeat (1, 2) 297773 ++ (1424871, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) 1) (hsteps_refl _)).
  }
  (* step 354: M pop12 (3,) *)
  apply (hsteps_trans _ (HB [] 4 1 13 ((2, 2) :: (40, 2) :: (1, 1) :: repeat (1, 2) 84 ++ (1116, 2) :: (1, 1) :: repeat (1, 2) 2613 ++ (9951, 2) :: (1, 1) :: repeat (1, 2) 20868 ++ (69110, 2) :: (1, 1) :: repeat (1, 2) 297773 ++ (1424871, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) 1)).
  {
    apply (pop12 3 [] 1 7 ((2, 2) :: (40, 2) :: (1, 1) :: repeat (1, 2) 84 ++ (1116, 2) :: (1, 1) :: repeat (1, 2) 2613 ++ (9951, 2) :: (1, 1) :: repeat (1, 2) 20868 ++ (69110, 2) :: (1, 1) :: repeat (1, 2) 297773 ++ (1424871, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) 1); closearith.
  }
  (* step 355: P TUP2_1 *)
  apply (hsteps_trans _ (HC [5] 13 1 2 ((38, 2) :: (1, 1) :: repeat (1, 2) 84 ++ (1116, 2) :: (1, 1) :: repeat (1, 2) 2613 ++ (9951, 2) :: (1, 1) :: repeat (1, 2) 20868 ++ (69110, 2) :: (1, 1) :: repeat (1, 2) 297773 ++ (1424871, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) 1)).
  {
    replace ((38, 2) :: (1, 1) :: repeat (1, 2) 84 ++ (1116, 2) :: (1, 1) :: repeat (1, 2) 2613 ++ (9951, 2) :: (1, 1) :: repeat (1, 2) 20868 ++ (69110, 2) :: (1, 1) :: repeat (1, 2) 297773 ++ (1424871, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) with ((40 - 2, 2) :: (1, 1) :: repeat (1, 2) 84 ++ (1116, 2) :: (1, 1) :: repeat (1, 2) 2613 ++ (9951, 2) :: (1, 1) :: repeat (1, 2) 20868 ++ (69110, 2) :: (1, 1) :: repeat (1, 2) 297773 ++ (1424871, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) by sec_eq.
    apply (sTUP2_1 [] 4 12 40 ((1, 1) :: repeat (1, 2) 84 ++ (1116, 2) :: (1, 1) :: repeat (1, 2) 2613 ++ (9951, 2) :: (1, 1) :: repeat (1, 2) 20868 ++ (69110, 2) :: (1, 1) :: repeat (1, 2) 297773 ++ (1424871, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) 1); closearith.
  }
  (* step 356: P TDN *)
  apply (hsteps_trans _ (HB [5] 13 1 4 ((38, 2) :: (1, 1) :: repeat (1, 2) 84 ++ (1116, 2) :: (1, 1) :: repeat (1, 2) 2613 ++ (9951, 2) :: (1, 1) :: repeat (1, 2) 20868 ++ (69110, 2) :: (1, 1) :: repeat (1, 2) 297773 ++ (1424871, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) 1)).
  {
    apply (sTDN [5] 13 ((38, 2) :: (1, 1) :: repeat (1, 2) 84 ++ (1116, 2) :: (1, 1) :: repeat (1, 2) 2613 ++ (9951, 2) :: (1, 1) :: repeat (1, 2) 20868 ++ (69110, 2) :: (1, 1) :: repeat (1, 2) 297773 ++ (1424871, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) 1).
  }
  (* step 357: sTUP *)
  apply (hsteps_trans _ (HC [5] 13 3 2 ((36, 2) :: (1, 1) :: repeat (1, 2) 84 ++ (1116, 2) :: (1, 1) :: repeat (1, 2) 2613 ++ (9951, 2) :: (1, 1) :: repeat (1, 2) 20868 ++ (69110, 2) :: (1, 1) :: repeat (1, 2) 297773 ++ (1424871, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) 1)).
  {
    replace ((36, 2) :: (1, 1) :: repeat (1, 2) 84 ++ (1116, 2) :: (1, 1) :: repeat (1, 2) 2613 ++ (9951, 2) :: (1, 1) :: repeat (1, 2) 20868 ++ (69110, 2) :: (1, 1) :: repeat (1, 2) 297773 ++ (1424871, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) with ((38 - 2, 2) :: (1, 1) :: repeat (1, 2) 84 ++ (1116, 2) :: (1, 1) :: repeat (1, 2) 2613 ++ (9951, 2) :: (1, 1) :: repeat (1, 2) 20868 ++ (69110, 2) :: (1, 1) :: repeat (1, 2) 297773 ++ (1424871, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) by sec_eq.
    apply (sTUP [5] 13 4 38 2 ((1, 1) :: repeat (1, 2) 84 ++ (1116, 2) :: (1, 1) :: repeat (1, 2) 2613 ++ (9951, 2) :: (1, 1) :: repeat (1, 2) 20868 ++ (69110, 2) :: (1, 1) :: repeat (1, 2) 297773 ++ (1424871, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) 1); closearith.
  }
  (* step 358: DIPGRIND 13 10 *)
  apply (hsteps_trans _ (HC [5] 0 3 2 (repeat (1, 2) 13 ++ (10, 2) :: (1, 1) :: repeat (1, 2) 84 ++ (1116, 2) :: (1, 1) :: repeat (1, 2) 2613 ++ (9951, 2) :: (1, 1) :: repeat (1, 2) 20868 ++ (69110, 2) :: (1, 1) :: repeat (1, 2) 297773 ++ (1424871, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) 1)).
  {
    apply (DIPGRIND 13 10 [5] ((1, 1) :: repeat (1, 2) 84 ++ (1116, 2) :: (1, 1) :: repeat (1, 2) 2613 ++ (9951, 2) :: (1, 1) :: repeat (1, 2) 20868 ++ (69110, 2) :: (1, 1) :: repeat (1, 2) 297773 ++ (1424871, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) 1); closearith.
  }
  (* step 359: P PX2Bgen *)
  apply (hsteps_trans _ (HB [0] 3 1 2 (repeat (1, 2) 1 ++ (1, 1) :: repeat (1, 2) 15 ++ (10, 2) :: (1, 1) :: repeat (1, 2) 84 ++ (1116, 2) :: (1, 1) :: repeat (1, 2) 2613 ++ (9951, 2) :: (1, 1) :: repeat (1, 2) 20868 ++ (69110, 2) :: (1, 1) :: repeat (1, 2) 297773 ++ (1424871, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) 1)).
  {
    exact (hsteps_step _ _ _ (hPX2Bgen 0 (repeat (1, 2) 13 ++ (10, 2) :: (1, 1) :: repeat (1, 2) 84 ++ (1116, 2) :: (1, 1) :: repeat (1, 2) 2613 ++ (9951, 2) :: (1, 1) :: repeat (1, 2) 20868 ++ (69110, 2) :: (1, 1) :: repeat (1, 2) 297773 ++ (1424871, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) 1) (hsteps_refl _)).
  }
  (* step 360: M pop12 (1,) *)
  apply (hsteps_trans _ (HB [0] 4 1 4 ((1, 1) :: repeat (1, 2) 15 ++ (10, 2) :: (1, 1) :: repeat (1, 2) 84 ++ (1116, 2) :: (1, 1) :: repeat (1, 2) 2613 ++ (9951, 2) :: (1, 1) :: repeat (1, 2) 20868 ++ (69110, 2) :: (1, 1) :: repeat (1, 2) 297773 ++ (1424871, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) 1)).
  {
    apply (pop12 1 [0] 3 2 ((1, 1) :: repeat (1, 2) 15 ++ (10, 2) :: (1, 1) :: repeat (1, 2) 84 ++ (1116, 2) :: (1, 1) :: repeat (1, 2) 2613 ++ (9951, 2) :: (1, 1) :: repeat (1, 2) 20868 ++ (69110, 2) :: (1, 1) :: repeat (1, 2) 297773 ++ (1424871, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) 1); closearith.
  }
  (* step 361: P POP *)
  apply (hsteps_trans _ (HB [0] 5 1 5 (repeat (1, 2) 15 ++ (10, 2) :: (1, 1) :: repeat (1, 2) 84 ++ (1116, 2) :: (1, 1) :: repeat (1, 2) 2613 ++ (9951, 2) :: (1, 1) :: repeat (1, 2) 20868 ++ (69110, 2) :: (1, 1) :: repeat (1, 2) 297773 ++ (1424871, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) 1)).
  {
    apply (sPOP1 [0] 4 4 (repeat (1, 2) 15 ++ (10, 2) :: (1, 1) :: repeat (1, 2) 84 ++ (1116, 2) :: (1, 1) :: repeat (1, 2) 2613 ++ (9951, 2) :: (1, 1) :: repeat (1, 2) 20868 ++ (69110, 2) :: (1, 1) :: repeat (1, 2) 297773 ++ (1424871, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) 1); closearith.
  }
  (* step 362: M pop12 (15,) *)
  apply (hsteps_trans _ (HB [0] 20 1 35 ((10, 2) :: (1, 1) :: repeat (1, 2) 84 ++ (1116, 2) :: (1, 1) :: repeat (1, 2) 2613 ++ (9951, 2) :: (1, 1) :: repeat (1, 2) 20868 ++ (69110, 2) :: (1, 1) :: repeat (1, 2) 297773 ++ (1424871, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) 1)).
  {
    apply (pop12 15 [0] 5 5 ((10, 2) :: (1, 1) :: repeat (1, 2) 84 ++ (1116, 2) :: (1, 1) :: repeat (1, 2) 2613 ++ (9951, 2) :: (1, 1) :: repeat (1, 2) 20868 ++ (69110, 2) :: (1, 1) :: repeat (1, 2) 297773 ++ (1424871, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) 1); closearith.
  }
  (* step 363: sTUP *)
  apply (hsteps_trans _ (HC [0] 20 34 2 ((8, 2) :: (1, 1) :: repeat (1, 2) 84 ++ (1116, 2) :: (1, 1) :: repeat (1, 2) 2613 ++ (9951, 2) :: (1, 1) :: repeat (1, 2) 20868 ++ (69110, 2) :: (1, 1) :: repeat (1, 2) 297773 ++ (1424871, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) 1)).
  {
    replace ((8, 2) :: (1, 1) :: repeat (1, 2) 84 ++ (1116, 2) :: (1, 1) :: repeat (1, 2) 2613 ++ (9951, 2) :: (1, 1) :: repeat (1, 2) 20868 ++ (69110, 2) :: (1, 1) :: repeat (1, 2) 297773 ++ (1424871, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) with ((10 - 2, 2) :: (1, 1) :: repeat (1, 2) 84 ++ (1116, 2) :: (1, 1) :: repeat (1, 2) 2613 ++ (9951, 2) :: (1, 1) :: repeat (1, 2) 20868 ++ (69110, 2) :: (1, 1) :: repeat (1, 2) 297773 ++ (1424871, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) by sec_eq.
    apply (sTUP [0] 20 35 10 2 ((1, 1) :: repeat (1, 2) 84 ++ (1116, 2) :: (1, 1) :: repeat (1, 2) 2613 ++ (9951, 2) :: (1, 1) :: repeat (1, 2) 20868 ++ (69110, 2) :: (1, 1) :: repeat (1, 2) 297773 ++ (1424871, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) 1); closearith.
  }
  (* step 364: hGRIND_even 15 *)
  apply (hsteps_trans _ (HB [0] 19 1 34 ((2, 2) :: (8, 2) :: (1, 1) :: repeat (1, 2) 84 ++ (1116, 2) :: (1, 1) :: repeat (1, 2) 2613 ++ (9951, 2) :: (1, 1) :: repeat (1, 2) 20868 ++ (69110, 2) :: (1, 1) :: repeat (1, 2) 297773 ++ (1424871, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) 1)).
  {
    apply (hGRIND_even 15 [0] 19 ((8, 2) :: (1, 1) :: repeat (1, 2) 84 ++ (1116, 2) :: (1, 1) :: repeat (1, 2) 2613 ++ (9951, 2) :: (1, 1) :: repeat (1, 2) 20868 ++ (69110, 2) :: (1, 1) :: repeat (1, 2) 297773 ++ (1424871, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) 1); closearith.
  }
  (* step 365: P TUP2_1 *)
  apply (hsteps_trans _ (HC [20; 0] 34 1 2 ((6, 2) :: (1, 1) :: repeat (1, 2) 84 ++ (1116, 2) :: (1, 1) :: repeat (1, 2) 2613 ++ (9951, 2) :: (1, 1) :: repeat (1, 2) 20868 ++ (69110, 2) :: (1, 1) :: repeat (1, 2) 297773 ++ (1424871, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) 1)).
  {
    replace ((6, 2) :: (1, 1) :: repeat (1, 2) 84 ++ (1116, 2) :: (1, 1) :: repeat (1, 2) 2613 ++ (9951, 2) :: (1, 1) :: repeat (1, 2) 20868 ++ (69110, 2) :: (1, 1) :: repeat (1, 2) 297773 ++ (1424871, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) with ((8 - 2, 2) :: (1, 1) :: repeat (1, 2) 84 ++ (1116, 2) :: (1, 1) :: repeat (1, 2) 2613 ++ (9951, 2) :: (1, 1) :: repeat (1, 2) 20868 ++ (69110, 2) :: (1, 1) :: repeat (1, 2) 297773 ++ (1424871, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) by sec_eq.
    apply (sTUP2_1 [0] 19 33 8 ((1, 1) :: repeat (1, 2) 84 ++ (1116, 2) :: (1, 1) :: repeat (1, 2) 2613 ++ (9951, 2) :: (1, 1) :: repeat (1, 2) 20868 ++ (69110, 2) :: (1, 1) :: repeat (1, 2) 297773 ++ (1424871, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) 1); closearith.
  }
  (* step 366: P TDN *)
  apply (hsteps_trans _ (HB [20; 0] 34 1 4 ((6, 2) :: (1, 1) :: repeat (1, 2) 84 ++ (1116, 2) :: (1, 1) :: repeat (1, 2) 2613 ++ (9951, 2) :: (1, 1) :: repeat (1, 2) 20868 ++ (69110, 2) :: (1, 1) :: repeat (1, 2) 297773 ++ (1424871, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) 1)).
  {
    apply (sTDN [20; 0] 34 ((6, 2) :: (1, 1) :: repeat (1, 2) 84 ++ (1116, 2) :: (1, 1) :: repeat (1, 2) 2613 ++ (9951, 2) :: (1, 1) :: repeat (1, 2) 20868 ++ (69110, 2) :: (1, 1) :: repeat (1, 2) 297773 ++ (1424871, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) 1).
  }
  (* step 367: sTUP *)
  apply (hsteps_trans _ (HC [20; 0] 34 3 2 ((4, 2) :: (1, 1) :: repeat (1, 2) 84 ++ (1116, 2) :: (1, 1) :: repeat (1, 2) 2613 ++ (9951, 2) :: (1, 1) :: repeat (1, 2) 20868 ++ (69110, 2) :: (1, 1) :: repeat (1, 2) 297773 ++ (1424871, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) 1)).
  {
    replace ((4, 2) :: (1, 1) :: repeat (1, 2) 84 ++ (1116, 2) :: (1, 1) :: repeat (1, 2) 2613 ++ (9951, 2) :: (1, 1) :: repeat (1, 2) 20868 ++ (69110, 2) :: (1, 1) :: repeat (1, 2) 297773 ++ (1424871, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) with ((6 - 2, 2) :: (1, 1) :: repeat (1, 2) 84 ++ (1116, 2) :: (1, 1) :: repeat (1, 2) 2613 ++ (9951, 2) :: (1, 1) :: repeat (1, 2) 20868 ++ (69110, 2) :: (1, 1) :: repeat (1, 2) 297773 ++ (1424871, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) by sec_eq.
    apply (sTUP [20; 0] 34 4 6 2 ((1, 1) :: repeat (1, 2) 84 ++ (1116, 2) :: (1, 1) :: repeat (1, 2) 2613 ++ (9951, 2) :: (1, 1) :: repeat (1, 2) 20868 ++ (69110, 2) :: (1, 1) :: repeat (1, 2) 297773 ++ (1424871, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) 1); closearith.
  }
  (* step 368: CLEANG_even 1 *)
  apply (hsteps_trans _ (HB [20; 0] 34 1 8 ((2, 2) :: (1, 1) :: repeat (1, 2) 84 ++ (1116, 2) :: (1, 1) :: repeat (1, 2) 2613 ++ (9951, 2) :: (1, 1) :: repeat (1, 2) 20868 ++ (69110, 2) :: (1, 1) :: repeat (1, 2) 297773 ++ (1424871, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) 1)).
  {
    apply (CLEANG_even 1 [20; 0] 34 ((1, 1) :: repeat (1, 2) 84 ++ (1116, 2) :: (1, 1) :: repeat (1, 2) 2613 ++ (9951, 2) :: (1, 1) :: repeat (1, 2) 20868 ++ (69110, 2) :: (1, 1) :: repeat (1, 2) 297773 ++ (1424871, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) 1); closearith.
  }
  (* step 369: P TRANS2_1 *)
  apply (hsteps_trans _ (HB [35; 20; 0] 9 1 3 (repeat (1, 2) 84 ++ (1116, 2) :: (1, 1) :: repeat (1, 2) 2613 ++ (9951, 2) :: (1, 1) :: repeat (1, 2) 20868 ++ (69110, 2) :: (1, 1) :: repeat (1, 2) 297773 ++ (1424871, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) 1)).
  {
    apply (sTRANS2_1 [20; 0] 34 7 1 (repeat (1, 2) 84 ++ (1116, 2) :: (1, 1) :: repeat (1, 2) 2613 ++ (9951, 2) :: (1, 1) :: repeat (1, 2) 20868 ++ (69110, 2) :: (1, 1) :: repeat (1, 2) 297773 ++ (1424871, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) 1); closearith.
  }
  (* step 370: M pop12 (84,) *)
  apply (hsteps_trans _ (HB [35; 20; 0] 93 1 171 ((1116, 2) :: (1, 1) :: repeat (1, 2) 2613 ++ (9951, 2) :: (1, 1) :: repeat (1, 2) 20868 ++ (69110, 2) :: (1, 1) :: repeat (1, 2) 297773 ++ (1424871, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) 1)).
  {
    apply (pop12 84 [35; 20; 0] 9 3 ((1116, 2) :: (1, 1) :: repeat (1, 2) 2613 ++ (9951, 2) :: (1, 1) :: repeat (1, 2) 20868 ++ (69110, 2) :: (1, 1) :: repeat (1, 2) 297773 ++ (1424871, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) 1); closearith.
  }
  (* step 371: sTUP *)
  apply (hsteps_trans _ (HC [35; 20; 0] 93 170 2 ((1114, 2) :: (1, 1) :: repeat (1, 2) 2613 ++ (9951, 2) :: (1, 1) :: repeat (1, 2) 20868 ++ (69110, 2) :: (1, 1) :: repeat (1, 2) 297773 ++ (1424871, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) 1)).
  {
    replace ((1114, 2) :: (1, 1) :: repeat (1, 2) 2613 ++ (9951, 2) :: (1, 1) :: repeat (1, 2) 20868 ++ (69110, 2) :: (1, 1) :: repeat (1, 2) 297773 ++ (1424871, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) with ((1116 - 2, 2) :: (1, 1) :: repeat (1, 2) 2613 ++ (9951, 2) :: (1, 1) :: repeat (1, 2) 20868 ++ (69110, 2) :: (1, 1) :: repeat (1, 2) 297773 ++ (1424871, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) by sec_eq.
    apply (sTUP [35; 20; 0] 93 171 1116 2 ((1, 1) :: repeat (1, 2) 2613 ++ (9951, 2) :: (1, 1) :: repeat (1, 2) 20868 ++ (69110, 2) :: (1, 1) :: repeat (1, 2) 297773 ++ (1424871, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) 1); closearith.
  }
  (* step 372: hGRIND_even 83 *)
  apply (hsteps_trans _ (HB [35; 20; 0] 92 1 170 ((2, 2) :: (1114, 2) :: (1, 1) :: repeat (1, 2) 2613 ++ (9951, 2) :: (1, 1) :: repeat (1, 2) 20868 ++ (69110, 2) :: (1, 1) :: repeat (1, 2) 297773 ++ (1424871, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) 1)).
  {
    apply (hGRIND_even 83 [35; 20; 0] 92 ((1114, 2) :: (1, 1) :: repeat (1, 2) 2613 ++ (9951, 2) :: (1, 1) :: repeat (1, 2) 20868 ++ (69110, 2) :: (1, 1) :: repeat (1, 2) 297773 ++ (1424871, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) 1); closearith.
  }
  (* step 373: P TUP2_1 *)
  apply (hsteps_trans _ (HC [93; 35; 20; 0] 170 1 2 ((1112, 2) :: (1, 1) :: repeat (1, 2) 2613 ++ (9951, 2) :: (1, 1) :: repeat (1, 2) 20868 ++ (69110, 2) :: (1, 1) :: repeat (1, 2) 297773 ++ (1424871, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) 1)).
  {
    replace ((1112, 2) :: (1, 1) :: repeat (1, 2) 2613 ++ (9951, 2) :: (1, 1) :: repeat (1, 2) 20868 ++ (69110, 2) :: (1, 1) :: repeat (1, 2) 297773 ++ (1424871, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) with ((1114 - 2, 2) :: (1, 1) :: repeat (1, 2) 2613 ++ (9951, 2) :: (1, 1) :: repeat (1, 2) 20868 ++ (69110, 2) :: (1, 1) :: repeat (1, 2) 297773 ++ (1424871, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) by sec_eq.
    apply (sTUP2_1 [35; 20; 0] 92 169 1114 ((1, 1) :: repeat (1, 2) 2613 ++ (9951, 2) :: (1, 1) :: repeat (1, 2) 20868 ++ (69110, 2) :: (1, 1) :: repeat (1, 2) 297773 ++ (1424871, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) 1); closearith.
  }
  (* step 374: P TDN *)
  apply (hsteps_trans _ (HB [93; 35; 20; 0] 170 1 4 ((1112, 2) :: (1, 1) :: repeat (1, 2) 2613 ++ (9951, 2) :: (1, 1) :: repeat (1, 2) 20868 ++ (69110, 2) :: (1, 1) :: repeat (1, 2) 297773 ++ (1424871, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) 1)).
  {
    apply (sTDN [93; 35; 20; 0] 170 ((1112, 2) :: (1, 1) :: repeat (1, 2) 2613 ++ (9951, 2) :: (1, 1) :: repeat (1, 2) 20868 ++ (69110, 2) :: (1, 1) :: repeat (1, 2) 297773 ++ (1424871, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) 1).
  }
  (* step 375: sTUP *)
  apply (hsteps_trans _ (HC [93; 35; 20; 0] 170 3 2 ((1110, 2) :: (1, 1) :: repeat (1, 2) 2613 ++ (9951, 2) :: (1, 1) :: repeat (1, 2) 20868 ++ (69110, 2) :: (1, 1) :: repeat (1, 2) 297773 ++ (1424871, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) 1)).
  {
    replace ((1110, 2) :: (1, 1) :: repeat (1, 2) 2613 ++ (9951, 2) :: (1, 1) :: repeat (1, 2) 20868 ++ (69110, 2) :: (1, 1) :: repeat (1, 2) 297773 ++ (1424871, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) with ((1112 - 2, 2) :: (1, 1) :: repeat (1, 2) 2613 ++ (9951, 2) :: (1, 1) :: repeat (1, 2) 20868 ++ (69110, 2) :: (1, 1) :: repeat (1, 2) 297773 ++ (1424871, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) by sec_eq.
    apply (sTUP [93; 35; 20; 0] 170 4 1112 2 ((1, 1) :: repeat (1, 2) 2613 ++ (9951, 2) :: (1, 1) :: repeat (1, 2) 20868 ++ (69110, 2) :: (1, 1) :: repeat (1, 2) 297773 ++ (1424871, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) 1); closearith.
  }
  (* step 376: DIPGRIND 170 770 *)
  apply (hsteps_trans _ (HC [93; 35; 20; 0] 0 3 2 (repeat (1, 2) 170 ++ (770, 2) :: (1, 1) :: repeat (1, 2) 2613 ++ (9951, 2) :: (1, 1) :: repeat (1, 2) 20868 ++ (69110, 2) :: (1, 1) :: repeat (1, 2) 297773 ++ (1424871, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) 1)).
  {
    apply (DIPGRIND 170 770 [93; 35; 20; 0] ((1, 1) :: repeat (1, 2) 2613 ++ (9951, 2) :: (1, 1) :: repeat (1, 2) 20868 ++ (69110, 2) :: (1, 1) :: repeat (1, 2) 297773 ++ (1424871, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) 1); closearith.
  }
  (* step 377: P PX2A *)
  apply (hsteps_trans _ (HC [20; 0] 34 91 2 ((1, 1) :: repeat (1, 2) 172 ++ (770, 2) :: (1, 1) :: repeat (1, 2) 2613 ++ (9951, 2) :: (1, 1) :: repeat (1, 2) 20868 ++ (69110, 2) :: (1, 1) :: repeat (1, 2) 297773 ++ (1424871, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) 1)).
  {
    exact (hsteps_step _ _ _ (hPX2A 90 34 [20; 0] (repeat (1, 2) 170 ++ (770, 2) :: (1, 1) :: repeat (1, 2) 2613 ++ (9951, 2) :: (1, 1) :: repeat (1, 2) 20868 ++ (69110, 2) :: (1, 1) :: repeat (1, 2) 297773 ++ (1424871, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) 1) (hsteps_refl _)).
  }
  (* step 378: P PUSH *)
  apply (hsteps_trans _ (HC [20; 0] 33 1 2 ((89, 2) :: (1, 1) :: repeat (1, 2) 172 ++ (770, 2) :: (1, 1) :: repeat (1, 2) 2613 ++ (9951, 2) :: (1, 1) :: repeat (1, 2) 20868 ++ (69110, 2) :: (1, 1) :: repeat (1, 2) 297773 ++ (1424871, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) 1)).
  {
    replace ((89, 2) :: (1, 1) :: repeat (1, 2) 172 ++ (770, 2) :: (1, 1) :: repeat (1, 2) 2613 ++ (9951, 2) :: (1, 1) :: repeat (1, 2) 20868 ++ (69110, 2) :: (1, 1) :: repeat (1, 2) 297773 ++ (1424871, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) with ((91 - 2, 2) :: (1, 1) :: repeat (1, 2) 172 ++ (770, 2) :: (1, 1) :: repeat (1, 2) 2613 ++ (9951, 2) :: (1, 1) :: repeat (1, 2) 20868 ++ (69110, 2) :: (1, 1) :: repeat (1, 2) 297773 ++ (1424871, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) by sec_eq.
    apply (sPUSH [20; 0] 33 91 ((1, 1) :: repeat (1, 2) 172 ++ (770, 2) :: (1, 1) :: repeat (1, 2) 2613 ++ (9951, 2) :: (1, 1) :: repeat (1, 2) 20868 ++ (69110, 2) :: (1, 1) :: repeat (1, 2) 297773 ++ (1424871, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) 1); closearith.
  }
  (* step 379: P TDN *)
  apply (hsteps_trans _ (HB [20; 0] 33 1 4 ((89, 2) :: (1, 1) :: repeat (1, 2) 172 ++ (770, 2) :: (1, 1) :: repeat (1, 2) 2613 ++ (9951, 2) :: (1, 1) :: repeat (1, 2) 20868 ++ (69110, 2) :: (1, 1) :: repeat (1, 2) 297773 ++ (1424871, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) 1)).
  {
    apply (sTDN [20; 0] 33 ((89, 2) :: (1, 1) :: repeat (1, 2) 172 ++ (770, 2) :: (1, 1) :: repeat (1, 2) 2613 ++ (9951, 2) :: (1, 1) :: repeat (1, 2) 20868 ++ (69110, 2) :: (1, 1) :: repeat (1, 2) 297773 ++ (1424871, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) 1).
  }
  (* step 380: sTUP *)
  apply (hsteps_trans _ (HC [20; 0] 33 3 2 ((87, 2) :: (1, 1) :: repeat (1, 2) 172 ++ (770, 2) :: (1, 1) :: repeat (1, 2) 2613 ++ (9951, 2) :: (1, 1) :: repeat (1, 2) 20868 ++ (69110, 2) :: (1, 1) :: repeat (1, 2) 297773 ++ (1424871, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) 1)).
  {
    replace ((87, 2) :: (1, 1) :: repeat (1, 2) 172 ++ (770, 2) :: (1, 1) :: repeat (1, 2) 2613 ++ (9951, 2) :: (1, 1) :: repeat (1, 2) 20868 ++ (69110, 2) :: (1, 1) :: repeat (1, 2) 297773 ++ (1424871, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) with ((89 - 2, 2) :: (1, 1) :: repeat (1, 2) 172 ++ (770, 2) :: (1, 1) :: repeat (1, 2) 2613 ++ (9951, 2) :: (1, 1) :: repeat (1, 2) 20868 ++ (69110, 2) :: (1, 1) :: repeat (1, 2) 297773 ++ (1424871, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) by sec_eq.
    apply (sTUP [20; 0] 33 4 89 2 ((1, 1) :: repeat (1, 2) 172 ++ (770, 2) :: (1, 1) :: repeat (1, 2) 2613 ++ (9951, 2) :: (1, 1) :: repeat (1, 2) 20868 ++ (69110, 2) :: (1, 1) :: repeat (1, 2) 297773 ++ (1424871, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) 1); closearith.
  }
  (* step 381: DIPGRIND 33 21 *)
  apply (hsteps_trans _ (HC [20; 0] 0 3 2 (repeat (1, 2) 33 ++ (21, 2) :: (1, 1) :: repeat (1, 2) 172 ++ (770, 2) :: (1, 1) :: repeat (1, 2) 2613 ++ (9951, 2) :: (1, 1) :: repeat (1, 2) 20868 ++ (69110, 2) :: (1, 1) :: repeat (1, 2) 297773 ++ (1424871, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) 1)).
  {
    apply (DIPGRIND 33 21 [20; 0] ((1, 1) :: repeat (1, 2) 172 ++ (770, 2) :: (1, 1) :: repeat (1, 2) 2613 ++ (9951, 2) :: (1, 1) :: repeat (1, 2) 20868 ++ (69110, 2) :: (1, 1) :: repeat (1, 2) 297773 ++ (1424871, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) 1); closearith.
  }
  (* step 382: P PX2A0 *)
  apply (hsteps_trans _ (HB [0] 3 1 2 ((16, 2) :: (1, 1) :: repeat (1, 2) 35 ++ (21, 2) :: (1, 1) :: repeat (1, 2) 172 ++ (770, 2) :: (1, 1) :: repeat (1, 2) 2613 ++ (9951, 2) :: (1, 1) :: repeat (1, 2) 20868 ++ (69110, 2) :: (1, 1) :: repeat (1, 2) 297773 ++ (1424871, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) 1)).
  {
    exact (hsteps_step _ _ _ (hPX2A0 15 (repeat (1, 2) 33 ++ (21, 2) :: (1, 1) :: repeat (1, 2) 172 ++ (770, 2) :: (1, 1) :: repeat (1, 2) 2613 ++ (9951, 2) :: (1, 1) :: repeat (1, 2) 20868 ++ (69110, 2) :: (1, 1) :: repeat (1, 2) 297773 ++ (1424871, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) 1) (hsteps_refl _)).
  }
  (* step 383: sTUP *)
  apply (hsteps_trans _ (HC [0] 3 1 2 ((14, 2) :: (1, 1) :: repeat (1, 2) 35 ++ (21, 2) :: (1, 1) :: repeat (1, 2) 172 ++ (770, 2) :: (1, 1) :: repeat (1, 2) 2613 ++ (9951, 2) :: (1, 1) :: repeat (1, 2) 20868 ++ (69110, 2) :: (1, 1) :: repeat (1, 2) 297773 ++ (1424871, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) 1)).
  {
    replace ((14, 2) :: (1, 1) :: repeat (1, 2) 35 ++ (21, 2) :: (1, 1) :: repeat (1, 2) 172 ++ (770, 2) :: (1, 1) :: repeat (1, 2) 2613 ++ (9951, 2) :: (1, 1) :: repeat (1, 2) 20868 ++ (69110, 2) :: (1, 1) :: repeat (1, 2) 297773 ++ (1424871, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) with ((16 - 2, 2) :: (1, 1) :: repeat (1, 2) 35 ++ (21, 2) :: (1, 1) :: repeat (1, 2) 172 ++ (770, 2) :: (1, 1) :: repeat (1, 2) 2613 ++ (9951, 2) :: (1, 1) :: repeat (1, 2) 20868 ++ (69110, 2) :: (1, 1) :: repeat (1, 2) 297773 ++ (1424871, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) by sec_eq.
    apply (sTUP [0] 3 2 16 2 ((1, 1) :: repeat (1, 2) 35 ++ (21, 2) :: (1, 1) :: repeat (1, 2) 172 ++ (770, 2) :: (1, 1) :: repeat (1, 2) 2613 ++ (9951, 2) :: (1, 1) :: repeat (1, 2) 20868 ++ (69110, 2) :: (1, 1) :: repeat (1, 2) 297773 ++ (1424871, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) 1); closearith.
  }
  (* step 384: P TDN *)
  apply (hsteps_trans _ (HB [0] 3 1 4 ((14, 2) :: (1, 1) :: repeat (1, 2) 35 ++ (21, 2) :: (1, 1) :: repeat (1, 2) 172 ++ (770, 2) :: (1, 1) :: repeat (1, 2) 2613 ++ (9951, 2) :: (1, 1) :: repeat (1, 2) 20868 ++ (69110, 2) :: (1, 1) :: repeat (1, 2) 297773 ++ (1424871, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) 1)).
  {
    apply (sTDN [0] 3 ((14, 2) :: (1, 1) :: repeat (1, 2) 35 ++ (21, 2) :: (1, 1) :: repeat (1, 2) 172 ++ (770, 2) :: (1, 1) :: repeat (1, 2) 2613 ++ (9951, 2) :: (1, 1) :: repeat (1, 2) 20868 ++ (69110, 2) :: (1, 1) :: repeat (1, 2) 297773 ++ (1424871, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) 1).
  }
  (* step 385: sTUP *)
  apply (hsteps_trans _ (HC [0] 3 3 2 ((12, 2) :: (1, 1) :: repeat (1, 2) 35 ++ (21, 2) :: (1, 1) :: repeat (1, 2) 172 ++ (770, 2) :: (1, 1) :: repeat (1, 2) 2613 ++ (9951, 2) :: (1, 1) :: repeat (1, 2) 20868 ++ (69110, 2) :: (1, 1) :: repeat (1, 2) 297773 ++ (1424871, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) 1)).
  {
    replace ((12, 2) :: (1, 1) :: repeat (1, 2) 35 ++ (21, 2) :: (1, 1) :: repeat (1, 2) 172 ++ (770, 2) :: (1, 1) :: repeat (1, 2) 2613 ++ (9951, 2) :: (1, 1) :: repeat (1, 2) 20868 ++ (69110, 2) :: (1, 1) :: repeat (1, 2) 297773 ++ (1424871, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) with ((14 - 2, 2) :: (1, 1) :: repeat (1, 2) 35 ++ (21, 2) :: (1, 1) :: repeat (1, 2) 172 ++ (770, 2) :: (1, 1) :: repeat (1, 2) 2613 ++ (9951, 2) :: (1, 1) :: repeat (1, 2) 20868 ++ (69110, 2) :: (1, 1) :: repeat (1, 2) 297773 ++ (1424871, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) by sec_eq.
    apply (sTUP [0] 3 4 14 2 ((1, 1) :: repeat (1, 2) 35 ++ (21, 2) :: (1, 1) :: repeat (1, 2) 172 ++ (770, 2) :: (1, 1) :: repeat (1, 2) 2613 ++ (9951, 2) :: (1, 1) :: repeat (1, 2) 20868 ++ (69110, 2) :: (1, 1) :: repeat (1, 2) 297773 ++ (1424871, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) 1); closearith.
  }
  (* step 386: DIPGRIND 3 6 *)
  apply (hsteps_trans _ (HC [0] 0 3 2 (repeat (1, 2) 3 ++ (6, 2) :: (1, 1) :: repeat (1, 2) 35 ++ (21, 2) :: (1, 1) :: repeat (1, 2) 172 ++ (770, 2) :: (1, 1) :: repeat (1, 2) 2613 ++ (9951, 2) :: (1, 1) :: repeat (1, 2) 20868 ++ (69110, 2) :: (1, 1) :: repeat (1, 2) 297773 ++ (1424871, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) 1)).
  {
    apply (DIPGRIND 3 6 [0] ((1, 1) :: repeat (1, 2) 35 ++ (21, 2) :: (1, 1) :: repeat (1, 2) 172 ++ (770, 2) :: (1, 1) :: repeat (1, 2) 2613 ++ (9951, 2) :: (1, 1) :: repeat (1, 2) 20868 ++ (69110, 2) :: (1, 1) :: repeat (1, 2) 297773 ++ (1424871, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) 1); closearith.
  }
  (* step 387: P PX2B0 *)
  apply (hsteps_trans _ (HB [] 0 1 5 (repeat (1, 2) 4 ++ (6, 2) :: (1, 1) :: repeat (1, 2) 35 ++ (21, 2) :: (1, 1) :: repeat (1, 2) 172 ++ (770, 2) :: (1, 1) :: repeat (1, 2) 2613 ++ (9951, 2) :: (1, 1) :: repeat (1, 2) 20868 ++ (69110, 2) :: (1, 1) :: repeat (1, 2) 297773 ++ (1424871, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) 1)).
  {
    exact (hsteps_step _ _ _ (hPX2B0 (repeat (1, 2) 3 ++ (6, 2) :: (1, 1) :: repeat (1, 2) 35 ++ (21, 2) :: (1, 1) :: repeat (1, 2) 172 ++ (770, 2) :: (1, 1) :: repeat (1, 2) 2613 ++ (9951, 2) :: (1, 1) :: repeat (1, 2) 20868 ++ (69110, 2) :: (1, 1) :: repeat (1, 2) 297773 ++ (1424871, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) 1) (hsteps_refl _)).
  }
  (* step 388: M pop12 (4,) *)
  apply (hsteps_trans _ (HB [] 4 1 13 ((6, 2) :: (1, 1) :: repeat (1, 2) 35 ++ (21, 2) :: (1, 1) :: repeat (1, 2) 172 ++ (770, 2) :: (1, 1) :: repeat (1, 2) 2613 ++ (9951, 2) :: (1, 1) :: repeat (1, 2) 20868 ++ (69110, 2) :: (1, 1) :: repeat (1, 2) 297773 ++ (1424871, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) 1)).
  {
    apply (pop12 4 [] 0 5 ((6, 2) :: (1, 1) :: repeat (1, 2) 35 ++ (21, 2) :: (1, 1) :: repeat (1, 2) 172 ++ (770, 2) :: (1, 1) :: repeat (1, 2) 2613 ++ (9951, 2) :: (1, 1) :: repeat (1, 2) 20868 ++ (69110, 2) :: (1, 1) :: repeat (1, 2) 297773 ++ (1424871, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) 1); closearith.
  }
  (* step 389: sTUP *)
  apply (hsteps_trans _ (HC [] 4 12 2 ((4, 2) :: (1, 1) :: repeat (1, 2) 35 ++ (21, 2) :: (1, 1) :: repeat (1, 2) 172 ++ (770, 2) :: (1, 1) :: repeat (1, 2) 2613 ++ (9951, 2) :: (1, 1) :: repeat (1, 2) 20868 ++ (69110, 2) :: (1, 1) :: repeat (1, 2) 297773 ++ (1424871, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) 1)).
  {
    replace ((4, 2) :: (1, 1) :: repeat (1, 2) 35 ++ (21, 2) :: (1, 1) :: repeat (1, 2) 172 ++ (770, 2) :: (1, 1) :: repeat (1, 2) 2613 ++ (9951, 2) :: (1, 1) :: repeat (1, 2) 20868 ++ (69110, 2) :: (1, 1) :: repeat (1, 2) 297773 ++ (1424871, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) with ((6 - 2, 2) :: (1, 1) :: repeat (1, 2) 35 ++ (21, 2) :: (1, 1) :: repeat (1, 2) 172 ++ (770, 2) :: (1, 1) :: repeat (1, 2) 2613 ++ (9951, 2) :: (1, 1) :: repeat (1, 2) 20868 ++ (69110, 2) :: (1, 1) :: repeat (1, 2) 297773 ++ (1424871, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) by sec_eq.
    apply (sTUP [] 4 13 6 2 ((1, 1) :: repeat (1, 2) 35 ++ (21, 2) :: (1, 1) :: repeat (1, 2) 172 ++ (770, 2) :: (1, 1) :: repeat (1, 2) 2613 ++ (9951, 2) :: (1, 1) :: repeat (1, 2) 20868 ++ (69110, 2) :: (1, 1) :: repeat (1, 2) 297773 ++ (1424871, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) 1); closearith.
  }
  (* step 390: P PUSH *)
  apply (hsteps_trans _ (HC [] 3 1 2 ((10, 2) :: (4, 2) :: (1, 1) :: repeat (1, 2) 35 ++ (21, 2) :: (1, 1) :: repeat (1, 2) 172 ++ (770, 2) :: (1, 1) :: repeat (1, 2) 2613 ++ (9951, 2) :: (1, 1) :: repeat (1, 2) 20868 ++ (69110, 2) :: (1, 1) :: repeat (1, 2) 297773 ++ (1424871, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) 1)).
  {
    replace ((10, 2) :: (4, 2) :: (1, 1) :: repeat (1, 2) 35 ++ (21, 2) :: (1, 1) :: repeat (1, 2) 172 ++ (770, 2) :: (1, 1) :: repeat (1, 2) 2613 ++ (9951, 2) :: (1, 1) :: repeat (1, 2) 20868 ++ (69110, 2) :: (1, 1) :: repeat (1, 2) 297773 ++ (1424871, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) with ((12 - 2, 2) :: (4, 2) :: (1, 1) :: repeat (1, 2) 35 ++ (21, 2) :: (1, 1) :: repeat (1, 2) 172 ++ (770, 2) :: (1, 1) :: repeat (1, 2) 2613 ++ (9951, 2) :: (1, 1) :: repeat (1, 2) 20868 ++ (69110, 2) :: (1, 1) :: repeat (1, 2) 297773 ++ (1424871, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) by sec_eq.
    apply (sPUSH [] 3 12 ((4, 2) :: (1, 1) :: repeat (1, 2) 35 ++ (21, 2) :: (1, 1) :: repeat (1, 2) 172 ++ (770, 2) :: (1, 1) :: repeat (1, 2) 2613 ++ (9951, 2) :: (1, 1) :: repeat (1, 2) 20868 ++ (69110, 2) :: (1, 1) :: repeat (1, 2) 297773 ++ (1424871, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) 1); closearith.
  }
  (* step 391: P TDN *)
  apply (hsteps_trans _ (HB [] 3 1 4 ((10, 2) :: (4, 2) :: (1, 1) :: repeat (1, 2) 35 ++ (21, 2) :: (1, 1) :: repeat (1, 2) 172 ++ (770, 2) :: (1, 1) :: repeat (1, 2) 2613 ++ (9951, 2) :: (1, 1) :: repeat (1, 2) 20868 ++ (69110, 2) :: (1, 1) :: repeat (1, 2) 297773 ++ (1424871, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) 1)).
  {
    apply (sTDN [] 3 ((10, 2) :: (4, 2) :: (1, 1) :: repeat (1, 2) 35 ++ (21, 2) :: (1, 1) :: repeat (1, 2) 172 ++ (770, 2) :: (1, 1) :: repeat (1, 2) 2613 ++ (9951, 2) :: (1, 1) :: repeat (1, 2) 20868 ++ (69110, 2) :: (1, 1) :: repeat (1, 2) 297773 ++ (1424871, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) 1).
  }
  (* step 392: sTUP *)
  replace ((8, 2) :: (4, 2) :: (1, 1) :: repeat (1, 2) 35 ++ (21, 2) :: (1, 1) :: repeat (1, 2) 172 ++ (770, 2) :: (1, 1) :: repeat (1, 2) 2613 ++ (9951, 2) :: (1, 1) :: repeat (1, 2) 20868 ++ (69110, 2) :: (1, 1) :: repeat (1, 2) 297773 ++ (1424871, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) with ((10 - 2, 2) :: (4, 2) :: (1, 1) :: repeat (1, 2) 35 ++ (21, 2) :: (1, 1) :: repeat (1, 2) 172 ++ (770, 2) :: (1, 1) :: repeat (1, 2) 2613 ++ (9951, 2) :: (1, 1) :: repeat (1, 2) 20868 ++ (69110, 2) :: (1, 1) :: repeat (1, 2) 297773 ++ (1424871, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) by sec_eq.
  apply (sTUP [] 3 4 10 2 ((4, 2) :: (1, 1) :: repeat (1, 2) 35 ++ (21, 2) :: (1, 1) :: repeat (1, 2) 172 ++ (770, 2) :: (1, 1) :: repeat (1, 2) 2613 ++ (9951, 2) :: (1, 1) :: repeat (1, 2) 20868 ++ (69110, 2) :: (1, 1) :: repeat (1, 2) 297773 ++ (1424871, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) 1); closearith.
Qed.

(* CASCADE56h: steps 393-448 of the CASCADE56 chain. *)
Lemma CASCADE56h : forall w,
  hsteps (HC [] 3 3 2 ((8, 2) :: (4, 2) :: (1, 1) :: repeat (1, 2) 35 ++ (21, 2) :: (1, 1) :: repeat (1, 2) 172 ++ (770, 2) :: (1, 1) :: repeat (1, 2) 2613 ++ (9951, 2) :: (1, 1) :: repeat (1, 2) 20868 ++ (69110, 2) :: (1, 1) :: repeat (1, 2) 297773 ++ (1424871, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) 1)
         (HB [2644; 739; 531; 83; 54; 5] 5228 1 4 ((9947, 2) :: (1, 1) :: repeat (1, 2) 20868 ++ (69110, 2) :: (1, 1) :: repeat (1, 2) 297773 ++ (1424871, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) 1).
Proof.
  intro w.
  (* step 393: DIPGRIND 3 2 *)
  apply (hsteps_trans _ (HC [] 0 3 2 (repeat (1, 2) 3 ++ (2, 2) :: (4, 2) :: (1, 1) :: repeat (1, 2) 35 ++ (21, 2) :: (1, 1) :: repeat (1, 2) 172 ++ (770, 2) :: (1, 1) :: repeat (1, 2) 2613 ++ (9951, 2) :: (1, 1) :: repeat (1, 2) 20868 ++ (69110, 2) :: (1, 1) :: repeat (1, 2) 297773 ++ (1424871, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) 1)).
  {
    apply (DIPGRIND 3 2 [] ((4, 2) :: (1, 1) :: repeat (1, 2) 35 ++ (21, 2) :: (1, 1) :: repeat (1, 2) 172 ++ (770, 2) :: (1, 1) :: repeat (1, 2) 2613 ++ (9951, 2) :: (1, 1) :: repeat (1, 2) 20868 ++ (69110, 2) :: (1, 1) :: repeat (1, 2) 297773 ++ (1424871, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) 1); closearith.
  }
  (* step 394: P PUSHX *)
  apply (hsteps_trans _ (HB [] 1 1 7 (repeat (1, 2) 3 ++ (2, 2) :: (4, 2) :: (1, 1) :: repeat (1, 2) 35 ++ (21, 2) :: (1, 1) :: repeat (1, 2) 172 ++ (770, 2) :: (1, 1) :: repeat (1, 2) 2613 ++ (9951, 2) :: (1, 1) :: repeat (1, 2) 20868 ++ (69110, 2) :: (1, 1) :: repeat (1, 2) 297773 ++ (1424871, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) 1)).
  {
    exact (hsteps_step _ _ _ (hPUSHX (repeat (1, 2) 3 ++ (2, 2) :: (4, 2) :: (1, 1) :: repeat (1, 2) 35 ++ (21, 2) :: (1, 1) :: repeat (1, 2) 172 ++ (770, 2) :: (1, 1) :: repeat (1, 2) 2613 ++ (9951, 2) :: (1, 1) :: repeat (1, 2) 20868 ++ (69110, 2) :: (1, 1) :: repeat (1, 2) 297773 ++ (1424871, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) 1) (hsteps_refl _)).
  }
  (* step 395: M pop12 (3,) *)
  apply (hsteps_trans _ (HB [] 4 1 13 ((2, 2) :: (4, 2) :: (1, 1) :: repeat (1, 2) 35 ++ (21, 2) :: (1, 1) :: repeat (1, 2) 172 ++ (770, 2) :: (1, 1) :: repeat (1, 2) 2613 ++ (9951, 2) :: (1, 1) :: repeat (1, 2) 20868 ++ (69110, 2) :: (1, 1) :: repeat (1, 2) 297773 ++ (1424871, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) 1)).
  {
    apply (pop12 3 [] 1 7 ((2, 2) :: (4, 2) :: (1, 1) :: repeat (1, 2) 35 ++ (21, 2) :: (1, 1) :: repeat (1, 2) 172 ++ (770, 2) :: (1, 1) :: repeat (1, 2) 2613 ++ (9951, 2) :: (1, 1) :: repeat (1, 2) 20868 ++ (69110, 2) :: (1, 1) :: repeat (1, 2) 297773 ++ (1424871, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) 1); closearith.
  }
  (* step 396: P TUP2_1 *)
  apply (hsteps_trans _ (HC [5] 13 1 2 ((2, 2) :: (1, 1) :: repeat (1, 2) 35 ++ (21, 2) :: (1, 1) :: repeat (1, 2) 172 ++ (770, 2) :: (1, 1) :: repeat (1, 2) 2613 ++ (9951, 2) :: (1, 1) :: repeat (1, 2) 20868 ++ (69110, 2) :: (1, 1) :: repeat (1, 2) 297773 ++ (1424871, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) 1)).
  {
    replace ((2, 2) :: (1, 1) :: repeat (1, 2) 35 ++ (21, 2) :: (1, 1) :: repeat (1, 2) 172 ++ (770, 2) :: (1, 1) :: repeat (1, 2) 2613 ++ (9951, 2) :: (1, 1) :: repeat (1, 2) 20868 ++ (69110, 2) :: (1, 1) :: repeat (1, 2) 297773 ++ (1424871, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) with ((4 - 2, 2) :: (1, 1) :: repeat (1, 2) 35 ++ (21, 2) :: (1, 1) :: repeat (1, 2) 172 ++ (770, 2) :: (1, 1) :: repeat (1, 2) 2613 ++ (9951, 2) :: (1, 1) :: repeat (1, 2) 20868 ++ (69110, 2) :: (1, 1) :: repeat (1, 2) 297773 ++ (1424871, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) by sec_eq.
    apply (sTUP2_1 [] 4 12 4 ((1, 1) :: repeat (1, 2) 35 ++ (21, 2) :: (1, 1) :: repeat (1, 2) 172 ++ (770, 2) :: (1, 1) :: repeat (1, 2) 2613 ++ (9951, 2) :: (1, 1) :: repeat (1, 2) 20868 ++ (69110, 2) :: (1, 1) :: repeat (1, 2) 297773 ++ (1424871, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) 1); closearith.
  }
  (* step 397: P TDN *)
  apply (hsteps_trans _ (HB [5] 13 1 4 ((2, 2) :: (1, 1) :: repeat (1, 2) 35 ++ (21, 2) :: (1, 1) :: repeat (1, 2) 172 ++ (770, 2) :: (1, 1) :: repeat (1, 2) 2613 ++ (9951, 2) :: (1, 1) :: repeat (1, 2) 20868 ++ (69110, 2) :: (1, 1) :: repeat (1, 2) 297773 ++ (1424871, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) 1)).
  {
    apply (sTDN [5] 13 ((2, 2) :: (1, 1) :: repeat (1, 2) 35 ++ (21, 2) :: (1, 1) :: repeat (1, 2) 172 ++ (770, 2) :: (1, 1) :: repeat (1, 2) 2613 ++ (9951, 2) :: (1, 1) :: repeat (1, 2) 20868 ++ (69110, 2) :: (1, 1) :: repeat (1, 2) 297773 ++ (1424871, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) 1).
  }
  (* step 398: P TRANS2_1 *)
  apply (hsteps_trans _ (HB [14; 5] 5 1 3 (repeat (1, 2) 35 ++ (21, 2) :: (1, 1) :: repeat (1, 2) 172 ++ (770, 2) :: (1, 1) :: repeat (1, 2) 2613 ++ (9951, 2) :: (1, 1) :: repeat (1, 2) 20868 ++ (69110, 2) :: (1, 1) :: repeat (1, 2) 297773 ++ (1424871, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) 1)).
  {
    apply (sTRANS2_1 [5] 13 3 1 (repeat (1, 2) 35 ++ (21, 2) :: (1, 1) :: repeat (1, 2) 172 ++ (770, 2) :: (1, 1) :: repeat (1, 2) 2613 ++ (9951, 2) :: (1, 1) :: repeat (1, 2) 20868 ++ (69110, 2) :: (1, 1) :: repeat (1, 2) 297773 ++ (1424871, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) 1); closearith.
  }
  (* step 399: M pop12 (35,) *)
  apply (hsteps_trans _ (HB [14; 5] 40 1 73 ((21, 2) :: (1, 1) :: repeat (1, 2) 172 ++ (770, 2) :: (1, 1) :: repeat (1, 2) 2613 ++ (9951, 2) :: (1, 1) :: repeat (1, 2) 20868 ++ (69110, 2) :: (1, 1) :: repeat (1, 2) 297773 ++ (1424871, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) 1)).
  {
    apply (pop12 35 [14; 5] 5 3 ((21, 2) :: (1, 1) :: repeat (1, 2) 172 ++ (770, 2) :: (1, 1) :: repeat (1, 2) 2613 ++ (9951, 2) :: (1, 1) :: repeat (1, 2) 20868 ++ (69110, 2) :: (1, 1) :: repeat (1, 2) 297773 ++ (1424871, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) 1); closearith.
  }
  (* step 400: sTUP *)
  apply (hsteps_trans _ (HC [14; 5] 40 72 2 ((19, 2) :: (1, 1) :: repeat (1, 2) 172 ++ (770, 2) :: (1, 1) :: repeat (1, 2) 2613 ++ (9951, 2) :: (1, 1) :: repeat (1, 2) 20868 ++ (69110, 2) :: (1, 1) :: repeat (1, 2) 297773 ++ (1424871, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) 1)).
  {
    replace ((19, 2) :: (1, 1) :: repeat (1, 2) 172 ++ (770, 2) :: (1, 1) :: repeat (1, 2) 2613 ++ (9951, 2) :: (1, 1) :: repeat (1, 2) 20868 ++ (69110, 2) :: (1, 1) :: repeat (1, 2) 297773 ++ (1424871, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) with ((21 - 2, 2) :: (1, 1) :: repeat (1, 2) 172 ++ (770, 2) :: (1, 1) :: repeat (1, 2) 2613 ++ (9951, 2) :: (1, 1) :: repeat (1, 2) 20868 ++ (69110, 2) :: (1, 1) :: repeat (1, 2) 297773 ++ (1424871, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) by sec_eq.
    apply (sTUP [14; 5] 40 73 21 2 ((1, 1) :: repeat (1, 2) 172 ++ (770, 2) :: (1, 1) :: repeat (1, 2) 2613 ++ (9951, 2) :: (1, 1) :: repeat (1, 2) 20868 ++ (69110, 2) :: (1, 1) :: repeat (1, 2) 297773 ++ (1424871, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) 1); closearith.
  }
  (* step 401: hGRIND_even 34 *)
  apply (hsteps_trans _ (HB [14; 5] 39 1 72 ((2, 2) :: (19, 2) :: (1, 1) :: repeat (1, 2) 172 ++ (770, 2) :: (1, 1) :: repeat (1, 2) 2613 ++ (9951, 2) :: (1, 1) :: repeat (1, 2) 20868 ++ (69110, 2) :: (1, 1) :: repeat (1, 2) 297773 ++ (1424871, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) 1)).
  {
    apply (hGRIND_even 34 [14; 5] 39 ((19, 2) :: (1, 1) :: repeat (1, 2) 172 ++ (770, 2) :: (1, 1) :: repeat (1, 2) 2613 ++ (9951, 2) :: (1, 1) :: repeat (1, 2) 20868 ++ (69110, 2) :: (1, 1) :: repeat (1, 2) 297773 ++ (1424871, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) 1); closearith.
  }
  (* step 402: P TUP2_1 *)
  apply (hsteps_trans _ (HC [40; 14; 5] 72 1 2 ((17, 2) :: (1, 1) :: repeat (1, 2) 172 ++ (770, 2) :: (1, 1) :: repeat (1, 2) 2613 ++ (9951, 2) :: (1, 1) :: repeat (1, 2) 20868 ++ (69110, 2) :: (1, 1) :: repeat (1, 2) 297773 ++ (1424871, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) 1)).
  {
    replace ((17, 2) :: (1, 1) :: repeat (1, 2) 172 ++ (770, 2) :: (1, 1) :: repeat (1, 2) 2613 ++ (9951, 2) :: (1, 1) :: repeat (1, 2) 20868 ++ (69110, 2) :: (1, 1) :: repeat (1, 2) 297773 ++ (1424871, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) with ((19 - 2, 2) :: (1, 1) :: repeat (1, 2) 172 ++ (770, 2) :: (1, 1) :: repeat (1, 2) 2613 ++ (9951, 2) :: (1, 1) :: repeat (1, 2) 20868 ++ (69110, 2) :: (1, 1) :: repeat (1, 2) 297773 ++ (1424871, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) by sec_eq.
    apply (sTUP2_1 [14; 5] 39 71 19 ((1, 1) :: repeat (1, 2) 172 ++ (770, 2) :: (1, 1) :: repeat (1, 2) 2613 ++ (9951, 2) :: (1, 1) :: repeat (1, 2) 20868 ++ (69110, 2) :: (1, 1) :: repeat (1, 2) 297773 ++ (1424871, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) 1); closearith.
  }
  (* step 403: P TDN *)
  apply (hsteps_trans _ (HB [40; 14; 5] 72 1 4 ((17, 2) :: (1, 1) :: repeat (1, 2) 172 ++ (770, 2) :: (1, 1) :: repeat (1, 2) 2613 ++ (9951, 2) :: (1, 1) :: repeat (1, 2) 20868 ++ (69110, 2) :: (1, 1) :: repeat (1, 2) 297773 ++ (1424871, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) 1)).
  {
    apply (sTDN [40; 14; 5] 72 ((17, 2) :: (1, 1) :: repeat (1, 2) 172 ++ (770, 2) :: (1, 1) :: repeat (1, 2) 2613 ++ (9951, 2) :: (1, 1) :: repeat (1, 2) 20868 ++ (69110, 2) :: (1, 1) :: repeat (1, 2) 297773 ++ (1424871, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) 1).
  }
  (* step 404: sTUP *)
  apply (hsteps_trans _ (HC [40; 14; 5] 72 3 2 ((15, 2) :: (1, 1) :: repeat (1, 2) 172 ++ (770, 2) :: (1, 1) :: repeat (1, 2) 2613 ++ (9951, 2) :: (1, 1) :: repeat (1, 2) 20868 ++ (69110, 2) :: (1, 1) :: repeat (1, 2) 297773 ++ (1424871, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) 1)).
  {
    replace ((15, 2) :: (1, 1) :: repeat (1, 2) 172 ++ (770, 2) :: (1, 1) :: repeat (1, 2) 2613 ++ (9951, 2) :: (1, 1) :: repeat (1, 2) 20868 ++ (69110, 2) :: (1, 1) :: repeat (1, 2) 297773 ++ (1424871, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) with ((17 - 2, 2) :: (1, 1) :: repeat (1, 2) 172 ++ (770, 2) :: (1, 1) :: repeat (1, 2) 2613 ++ (9951, 2) :: (1, 1) :: repeat (1, 2) 20868 ++ (69110, 2) :: (1, 1) :: repeat (1, 2) 297773 ++ (1424871, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) by sec_eq.
    apply (sTUP [40; 14; 5] 72 4 17 2 ((1, 1) :: repeat (1, 2) 172 ++ (770, 2) :: (1, 1) :: repeat (1, 2) 2613 ++ (9951, 2) :: (1, 1) :: repeat (1, 2) 20868 ++ (69110, 2) :: (1, 1) :: repeat (1, 2) 297773 ++ (1424871, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) 1); closearith.
  }
  (* step 405: CLEANG_odd 6 *)
  apply (hsteps_trans _ (HB [40; 14; 5] 72 1 20 (repeat (1, 2) 1 ++ (1, 1) :: repeat (1, 2) 172 ++ (770, 2) :: (1, 1) :: repeat (1, 2) 2613 ++ (9951, 2) :: (1, 1) :: repeat (1, 2) 20868 ++ (69110, 2) :: (1, 1) :: repeat (1, 2) 297773 ++ (1424871, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) 1)).
  {
    replace (repeat (1, 2) 1 ++ (1, 1) :: repeat (1, 2) 172 ++ (770, 2) :: (1, 1) :: repeat (1, 2) 2613 ++ (9951, 2) :: (1, 1) :: repeat (1, 2) 20868 ++ (69110, 2) :: (1, 1) :: repeat (1, 2) 297773 ++ (1424871, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) with ((1, 2) :: (1, 1) :: repeat (1, 2) 172 ++ (770, 2) :: (1, 1) :: repeat (1, 2) 2613 ++ (9951, 2) :: (1, 1) :: repeat (1, 2) 20868 ++ (69110, 2) :: (1, 1) :: repeat (1, 2) 297773 ++ (1424871, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) by sec_eq.
    apply (CLEANG_odd 6 [40; 14; 5] 72 ((1, 1) :: repeat (1, 2) 172 ++ (770, 2) :: (1, 1) :: repeat (1, 2) 2613 ++ (9951, 2) :: (1, 1) :: repeat (1, 2) 20868 ++ (69110, 2) :: (1, 1) :: repeat (1, 2) 297773 ++ (1424871, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) 1); closearith.
  }
  (* step 406: M pop12 (1,) *)
  apply (hsteps_trans _ (HB [40; 14; 5] 73 1 22 ((1, 1) :: repeat (1, 2) 172 ++ (770, 2) :: (1, 1) :: repeat (1, 2) 2613 ++ (9951, 2) :: (1, 1) :: repeat (1, 2) 20868 ++ (69110, 2) :: (1, 1) :: repeat (1, 2) 297773 ++ (1424871, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) 1)).
  {
    apply (pop12 1 [40; 14; 5] 72 20 ((1, 1) :: repeat (1, 2) 172 ++ (770, 2) :: (1, 1) :: repeat (1, 2) 2613 ++ (9951, 2) :: (1, 1) :: repeat (1, 2) 20868 ++ (69110, 2) :: (1, 1) :: repeat (1, 2) 297773 ++ (1424871, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) 1); closearith.
  }
  (* step 407: P POP *)
  apply (hsteps_trans _ (HB [40; 14; 5] 74 1 23 (repeat (1, 2) 172 ++ (770, 2) :: (1, 1) :: repeat (1, 2) 2613 ++ (9951, 2) :: (1, 1) :: repeat (1, 2) 20868 ++ (69110, 2) :: (1, 1) :: repeat (1, 2) 297773 ++ (1424871, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) 1)).
  {
    apply (sPOP1 [40; 14; 5] 73 22 (repeat (1, 2) 172 ++ (770, 2) :: (1, 1) :: repeat (1, 2) 2613 ++ (9951, 2) :: (1, 1) :: repeat (1, 2) 20868 ++ (69110, 2) :: (1, 1) :: repeat (1, 2) 297773 ++ (1424871, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) 1); closearith.
  }
  (* step 408: M pop12 (172,) *)
  apply (hsteps_trans _ (HB [40; 14; 5] 246 1 367 ((770, 2) :: (1, 1) :: repeat (1, 2) 2613 ++ (9951, 2) :: (1, 1) :: repeat (1, 2) 20868 ++ (69110, 2) :: (1, 1) :: repeat (1, 2) 297773 ++ (1424871, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) 1)).
  {
    apply (pop12 172 [40; 14; 5] 74 23 ((770, 2) :: (1, 1) :: repeat (1, 2) 2613 ++ (9951, 2) :: (1, 1) :: repeat (1, 2) 20868 ++ (69110, 2) :: (1, 1) :: repeat (1, 2) 297773 ++ (1424871, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) 1); closearith.
  }
  (* step 409: sTUP *)
  apply (hsteps_trans _ (HC [40; 14; 5] 246 366 2 ((768, 2) :: (1, 1) :: repeat (1, 2) 2613 ++ (9951, 2) :: (1, 1) :: repeat (1, 2) 20868 ++ (69110, 2) :: (1, 1) :: repeat (1, 2) 297773 ++ (1424871, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) 1)).
  {
    replace ((768, 2) :: (1, 1) :: repeat (1, 2) 2613 ++ (9951, 2) :: (1, 1) :: repeat (1, 2) 20868 ++ (69110, 2) :: (1, 1) :: repeat (1, 2) 297773 ++ (1424871, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) with ((770 - 2, 2) :: (1, 1) :: repeat (1, 2) 2613 ++ (9951, 2) :: (1, 1) :: repeat (1, 2) 20868 ++ (69110, 2) :: (1, 1) :: repeat (1, 2) 297773 ++ (1424871, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) by sec_eq.
    apply (sTUP [40; 14; 5] 246 367 770 2 ((1, 1) :: repeat (1, 2) 2613 ++ (9951, 2) :: (1, 1) :: repeat (1, 2) 20868 ++ (69110, 2) :: (1, 1) :: repeat (1, 2) 297773 ++ (1424871, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) 1); closearith.
  }
  (* step 410: hGRIND_even 181 *)
  apply (hsteps_trans _ (HB [40; 14; 5] 245 1 366 ((2, 2) :: (768, 2) :: (1, 1) :: repeat (1, 2) 2613 ++ (9951, 2) :: (1, 1) :: repeat (1, 2) 20868 ++ (69110, 2) :: (1, 1) :: repeat (1, 2) 297773 ++ (1424871, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) 1)).
  {
    apply (hGRIND_even 181 [40; 14; 5] 245 ((768, 2) :: (1, 1) :: repeat (1, 2) 2613 ++ (9951, 2) :: (1, 1) :: repeat (1, 2) 20868 ++ (69110, 2) :: (1, 1) :: repeat (1, 2) 297773 ++ (1424871, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) 1); closearith.
  }
  (* step 411: P TUP2_1 *)
  apply (hsteps_trans _ (HC [246; 40; 14; 5] 366 1 2 ((766, 2) :: (1, 1) :: repeat (1, 2) 2613 ++ (9951, 2) :: (1, 1) :: repeat (1, 2) 20868 ++ (69110, 2) :: (1, 1) :: repeat (1, 2) 297773 ++ (1424871, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) 1)).
  {
    replace ((766, 2) :: (1, 1) :: repeat (1, 2) 2613 ++ (9951, 2) :: (1, 1) :: repeat (1, 2) 20868 ++ (69110, 2) :: (1, 1) :: repeat (1, 2) 297773 ++ (1424871, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) with ((768 - 2, 2) :: (1, 1) :: repeat (1, 2) 2613 ++ (9951, 2) :: (1, 1) :: repeat (1, 2) 20868 ++ (69110, 2) :: (1, 1) :: repeat (1, 2) 297773 ++ (1424871, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) by sec_eq.
    apply (sTUP2_1 [40; 14; 5] 245 365 768 ((1, 1) :: repeat (1, 2) 2613 ++ (9951, 2) :: (1, 1) :: repeat (1, 2) 20868 ++ (69110, 2) :: (1, 1) :: repeat (1, 2) 297773 ++ (1424871, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) 1); closearith.
  }
  (* step 412: P TDN *)
  apply (hsteps_trans _ (HB [246; 40; 14; 5] 366 1 4 ((766, 2) :: (1, 1) :: repeat (1, 2) 2613 ++ (9951, 2) :: (1, 1) :: repeat (1, 2) 20868 ++ (69110, 2) :: (1, 1) :: repeat (1, 2) 297773 ++ (1424871, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) 1)).
  {
    apply (sTDN [246; 40; 14; 5] 366 ((766, 2) :: (1, 1) :: repeat (1, 2) 2613 ++ (9951, 2) :: (1, 1) :: repeat (1, 2) 20868 ++ (69110, 2) :: (1, 1) :: repeat (1, 2) 297773 ++ (1424871, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) 1).
  }
  (* step 413: sTUP *)
  apply (hsteps_trans _ (HC [246; 40; 14; 5] 366 3 2 ((764, 2) :: (1, 1) :: repeat (1, 2) 2613 ++ (9951, 2) :: (1, 1) :: repeat (1, 2) 20868 ++ (69110, 2) :: (1, 1) :: repeat (1, 2) 297773 ++ (1424871, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) 1)).
  {
    replace ((764, 2) :: (1, 1) :: repeat (1, 2) 2613 ++ (9951, 2) :: (1, 1) :: repeat (1, 2) 20868 ++ (69110, 2) :: (1, 1) :: repeat (1, 2) 297773 ++ (1424871, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) with ((766 - 2, 2) :: (1, 1) :: repeat (1, 2) 2613 ++ (9951, 2) :: (1, 1) :: repeat (1, 2) 20868 ++ (69110, 2) :: (1, 1) :: repeat (1, 2) 297773 ++ (1424871, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) by sec_eq.
    apply (sTUP [246; 40; 14; 5] 366 4 766 2 ((1, 1) :: repeat (1, 2) 2613 ++ (9951, 2) :: (1, 1) :: repeat (1, 2) 20868 ++ (69110, 2) :: (1, 1) :: repeat (1, 2) 297773 ++ (1424871, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) 1); closearith.
  }
  (* step 414: DIPGRIND 366 32 *)
  apply (hsteps_trans _ (HC [246; 40; 14; 5] 0 3 2 (repeat (1, 2) 366 ++ (32, 2) :: (1, 1) :: repeat (1, 2) 2613 ++ (9951, 2) :: (1, 1) :: repeat (1, 2) 20868 ++ (69110, 2) :: (1, 1) :: repeat (1, 2) 297773 ++ (1424871, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) 1)).
  {
    apply (DIPGRIND 366 32 [246; 40; 14; 5] ((1, 1) :: repeat (1, 2) 2613 ++ (9951, 2) :: (1, 1) :: repeat (1, 2) 20868 ++ (69110, 2) :: (1, 1) :: repeat (1, 2) 297773 ++ (1424871, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) 1); closearith.
  }
  (* step 415: P PX2A *)
  apply (hsteps_trans _ (HC [14; 5] 39 244 2 ((1, 1) :: repeat (1, 2) 368 ++ (32, 2) :: (1, 1) :: repeat (1, 2) 2613 ++ (9951, 2) :: (1, 1) :: repeat (1, 2) 20868 ++ (69110, 2) :: (1, 1) :: repeat (1, 2) 297773 ++ (1424871, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) 1)).
  {
    exact (hsteps_step _ _ _ (hPX2A 243 39 [14; 5] (repeat (1, 2) 366 ++ (32, 2) :: (1, 1) :: repeat (1, 2) 2613 ++ (9951, 2) :: (1, 1) :: repeat (1, 2) 20868 ++ (69110, 2) :: (1, 1) :: repeat (1, 2) 297773 ++ (1424871, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) 1) (hsteps_refl _)).
  }
  (* step 416: P PUSH *)
  apply (hsteps_trans _ (HC [14; 5] 38 1 2 ((242, 2) :: (1, 1) :: repeat (1, 2) 368 ++ (32, 2) :: (1, 1) :: repeat (1, 2) 2613 ++ (9951, 2) :: (1, 1) :: repeat (1, 2) 20868 ++ (69110, 2) :: (1, 1) :: repeat (1, 2) 297773 ++ (1424871, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) 1)).
  {
    replace ((242, 2) :: (1, 1) :: repeat (1, 2) 368 ++ (32, 2) :: (1, 1) :: repeat (1, 2) 2613 ++ (9951, 2) :: (1, 1) :: repeat (1, 2) 20868 ++ (69110, 2) :: (1, 1) :: repeat (1, 2) 297773 ++ (1424871, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) with ((244 - 2, 2) :: (1, 1) :: repeat (1, 2) 368 ++ (32, 2) :: (1, 1) :: repeat (1, 2) 2613 ++ (9951, 2) :: (1, 1) :: repeat (1, 2) 20868 ++ (69110, 2) :: (1, 1) :: repeat (1, 2) 297773 ++ (1424871, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) by sec_eq.
    apply (sPUSH [14; 5] 38 244 ((1, 1) :: repeat (1, 2) 368 ++ (32, 2) :: (1, 1) :: repeat (1, 2) 2613 ++ (9951, 2) :: (1, 1) :: repeat (1, 2) 20868 ++ (69110, 2) :: (1, 1) :: repeat (1, 2) 297773 ++ (1424871, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) 1); closearith.
  }
  (* step 417: P TDN *)
  apply (hsteps_trans _ (HB [14; 5] 38 1 4 ((242, 2) :: (1, 1) :: repeat (1, 2) 368 ++ (32, 2) :: (1, 1) :: repeat (1, 2) 2613 ++ (9951, 2) :: (1, 1) :: repeat (1, 2) 20868 ++ (69110, 2) :: (1, 1) :: repeat (1, 2) 297773 ++ (1424871, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) 1)).
  {
    apply (sTDN [14; 5] 38 ((242, 2) :: (1, 1) :: repeat (1, 2) 368 ++ (32, 2) :: (1, 1) :: repeat (1, 2) 2613 ++ (9951, 2) :: (1, 1) :: repeat (1, 2) 20868 ++ (69110, 2) :: (1, 1) :: repeat (1, 2) 297773 ++ (1424871, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) 1).
  }
  (* step 418: sTUP *)
  apply (hsteps_trans _ (HC [14; 5] 38 3 2 ((240, 2) :: (1, 1) :: repeat (1, 2) 368 ++ (32, 2) :: (1, 1) :: repeat (1, 2) 2613 ++ (9951, 2) :: (1, 1) :: repeat (1, 2) 20868 ++ (69110, 2) :: (1, 1) :: repeat (1, 2) 297773 ++ (1424871, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) 1)).
  {
    replace ((240, 2) :: (1, 1) :: repeat (1, 2) 368 ++ (32, 2) :: (1, 1) :: repeat (1, 2) 2613 ++ (9951, 2) :: (1, 1) :: repeat (1, 2) 20868 ++ (69110, 2) :: (1, 1) :: repeat (1, 2) 297773 ++ (1424871, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) with ((242 - 2, 2) :: (1, 1) :: repeat (1, 2) 368 ++ (32, 2) :: (1, 1) :: repeat (1, 2) 2613 ++ (9951, 2) :: (1, 1) :: repeat (1, 2) 20868 ++ (69110, 2) :: (1, 1) :: repeat (1, 2) 297773 ++ (1424871, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) by sec_eq.
    apply (sTUP [14; 5] 38 4 242 2 ((1, 1) :: repeat (1, 2) 368 ++ (32, 2) :: (1, 1) :: repeat (1, 2) 2613 ++ (9951, 2) :: (1, 1) :: repeat (1, 2) 20868 ++ (69110, 2) :: (1, 1) :: repeat (1, 2) 297773 ++ (1424871, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) 1); closearith.
  }
  (* step 419: DIPGRIND 38 164 *)
  apply (hsteps_trans _ (HC [14; 5] 0 3 2 (repeat (1, 2) 38 ++ (164, 2) :: (1, 1) :: repeat (1, 2) 368 ++ (32, 2) :: (1, 1) :: repeat (1, 2) 2613 ++ (9951, 2) :: (1, 1) :: repeat (1, 2) 20868 ++ (69110, 2) :: (1, 1) :: repeat (1, 2) 297773 ++ (1424871, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) 1)).
  {
    apply (DIPGRIND 38 164 [14; 5] ((1, 1) :: repeat (1, 2) 368 ++ (32, 2) :: (1, 1) :: repeat (1, 2) 2613 ++ (9951, 2) :: (1, 1) :: repeat (1, 2) 20868 ++ (69110, 2) :: (1, 1) :: repeat (1, 2) 297773 ++ (1424871, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) 1); closearith.
  }
  (* step 420: P PX2A *)
  apply (hsteps_trans _ (HC [] 4 12 2 ((1, 1) :: repeat (1, 2) 40 ++ (164, 2) :: (1, 1) :: repeat (1, 2) 368 ++ (32, 2) :: (1, 1) :: repeat (1, 2) 2613 ++ (9951, 2) :: (1, 1) :: repeat (1, 2) 20868 ++ (69110, 2) :: (1, 1) :: repeat (1, 2) 297773 ++ (1424871, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) 1)).
  {
    exact (hsteps_step _ _ _ (hPX2A 11 4 [] (repeat (1, 2) 38 ++ (164, 2) :: (1, 1) :: repeat (1, 2) 368 ++ (32, 2) :: (1, 1) :: repeat (1, 2) 2613 ++ (9951, 2) :: (1, 1) :: repeat (1, 2) 20868 ++ (69110, 2) :: (1, 1) :: repeat (1, 2) 297773 ++ (1424871, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) 1) (hsteps_refl _)).
  }
  (* step 421: P PUSH *)
  apply (hsteps_trans _ (HC [] 3 1 2 ((10, 2) :: (1, 1) :: repeat (1, 2) 40 ++ (164, 2) :: (1, 1) :: repeat (1, 2) 368 ++ (32, 2) :: (1, 1) :: repeat (1, 2) 2613 ++ (9951, 2) :: (1, 1) :: repeat (1, 2) 20868 ++ (69110, 2) :: (1, 1) :: repeat (1, 2) 297773 ++ (1424871, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) 1)).
  {
    replace ((10, 2) :: (1, 1) :: repeat (1, 2) 40 ++ (164, 2) :: (1, 1) :: repeat (1, 2) 368 ++ (32, 2) :: (1, 1) :: repeat (1, 2) 2613 ++ (9951, 2) :: (1, 1) :: repeat (1, 2) 20868 ++ (69110, 2) :: (1, 1) :: repeat (1, 2) 297773 ++ (1424871, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) with ((12 - 2, 2) :: (1, 1) :: repeat (1, 2) 40 ++ (164, 2) :: (1, 1) :: repeat (1, 2) 368 ++ (32, 2) :: (1, 1) :: repeat (1, 2) 2613 ++ (9951, 2) :: (1, 1) :: repeat (1, 2) 20868 ++ (69110, 2) :: (1, 1) :: repeat (1, 2) 297773 ++ (1424871, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) by sec_eq.
    apply (sPUSH [] 3 12 ((1, 1) :: repeat (1, 2) 40 ++ (164, 2) :: (1, 1) :: repeat (1, 2) 368 ++ (32, 2) :: (1, 1) :: repeat (1, 2) 2613 ++ (9951, 2) :: (1, 1) :: repeat (1, 2) 20868 ++ (69110, 2) :: (1, 1) :: repeat (1, 2) 297773 ++ (1424871, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) 1); closearith.
  }
  (* step 422: P TDN *)
  apply (hsteps_trans _ (HB [] 3 1 4 ((10, 2) :: (1, 1) :: repeat (1, 2) 40 ++ (164, 2) :: (1, 1) :: repeat (1, 2) 368 ++ (32, 2) :: (1, 1) :: repeat (1, 2) 2613 ++ (9951, 2) :: (1, 1) :: repeat (1, 2) 20868 ++ (69110, 2) :: (1, 1) :: repeat (1, 2) 297773 ++ (1424871, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) 1)).
  {
    apply (sTDN [] 3 ((10, 2) :: (1, 1) :: repeat (1, 2) 40 ++ (164, 2) :: (1, 1) :: repeat (1, 2) 368 ++ (32, 2) :: (1, 1) :: repeat (1, 2) 2613 ++ (9951, 2) :: (1, 1) :: repeat (1, 2) 20868 ++ (69110, 2) :: (1, 1) :: repeat (1, 2) 297773 ++ (1424871, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) 1).
  }
  (* step 423: sTUP *)
  apply (hsteps_trans _ (HC [] 3 3 2 ((8, 2) :: (1, 1) :: repeat (1, 2) 40 ++ (164, 2) :: (1, 1) :: repeat (1, 2) 368 ++ (32, 2) :: (1, 1) :: repeat (1, 2) 2613 ++ (9951, 2) :: (1, 1) :: repeat (1, 2) 20868 ++ (69110, 2) :: (1, 1) :: repeat (1, 2) 297773 ++ (1424871, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) 1)).
  {
    replace ((8, 2) :: (1, 1) :: repeat (1, 2) 40 ++ (164, 2) :: (1, 1) :: repeat (1, 2) 368 ++ (32, 2) :: (1, 1) :: repeat (1, 2) 2613 ++ (9951, 2) :: (1, 1) :: repeat (1, 2) 20868 ++ (69110, 2) :: (1, 1) :: repeat (1, 2) 297773 ++ (1424871, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) with ((10 - 2, 2) :: (1, 1) :: repeat (1, 2) 40 ++ (164, 2) :: (1, 1) :: repeat (1, 2) 368 ++ (32, 2) :: (1, 1) :: repeat (1, 2) 2613 ++ (9951, 2) :: (1, 1) :: repeat (1, 2) 20868 ++ (69110, 2) :: (1, 1) :: repeat (1, 2) 297773 ++ (1424871, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) by sec_eq.
    apply (sTUP [] 3 4 10 2 ((1, 1) :: repeat (1, 2) 40 ++ (164, 2) :: (1, 1) :: repeat (1, 2) 368 ++ (32, 2) :: (1, 1) :: repeat (1, 2) 2613 ++ (9951, 2) :: (1, 1) :: repeat (1, 2) 20868 ++ (69110, 2) :: (1, 1) :: repeat (1, 2) 297773 ++ (1424871, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) 1); closearith.
  }
  (* step 424: DIPGRIND 3 2 *)
  apply (hsteps_trans _ (HC [] 0 3 2 (repeat (1, 2) 3 ++ (2, 2) :: (1, 1) :: repeat (1, 2) 40 ++ (164, 2) :: (1, 1) :: repeat (1, 2) 368 ++ (32, 2) :: (1, 1) :: repeat (1, 2) 2613 ++ (9951, 2) :: (1, 1) :: repeat (1, 2) 20868 ++ (69110, 2) :: (1, 1) :: repeat (1, 2) 297773 ++ (1424871, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) 1)).
  {
    apply (DIPGRIND 3 2 [] ((1, 1) :: repeat (1, 2) 40 ++ (164, 2) :: (1, 1) :: repeat (1, 2) 368 ++ (32, 2) :: (1, 1) :: repeat (1, 2) 2613 ++ (9951, 2) :: (1, 1) :: repeat (1, 2) 20868 ++ (69110, 2) :: (1, 1) :: repeat (1, 2) 297773 ++ (1424871, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) 1); closearith.
  }
  (* step 425: P PUSHX *)
  apply (hsteps_trans _ (HB [] 1 1 7 (repeat (1, 2) 3 ++ (2, 2) :: (1, 1) :: repeat (1, 2) 40 ++ (164, 2) :: (1, 1) :: repeat (1, 2) 368 ++ (32, 2) :: (1, 1) :: repeat (1, 2) 2613 ++ (9951, 2) :: (1, 1) :: repeat (1, 2) 20868 ++ (69110, 2) :: (1, 1) :: repeat (1, 2) 297773 ++ (1424871, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) 1)).
  {
    exact (hsteps_step _ _ _ (hPUSHX (repeat (1, 2) 3 ++ (2, 2) :: (1, 1) :: repeat (1, 2) 40 ++ (164, 2) :: (1, 1) :: repeat (1, 2) 368 ++ (32, 2) :: (1, 1) :: repeat (1, 2) 2613 ++ (9951, 2) :: (1, 1) :: repeat (1, 2) 20868 ++ (69110, 2) :: (1, 1) :: repeat (1, 2) 297773 ++ (1424871, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) 1) (hsteps_refl _)).
  }
  (* step 426: M pop12 (3,) *)
  apply (hsteps_trans _ (HB [] 4 1 13 ((2, 2) :: (1, 1) :: repeat (1, 2) 40 ++ (164, 2) :: (1, 1) :: repeat (1, 2) 368 ++ (32, 2) :: (1, 1) :: repeat (1, 2) 2613 ++ (9951, 2) :: (1, 1) :: repeat (1, 2) 20868 ++ (69110, 2) :: (1, 1) :: repeat (1, 2) 297773 ++ (1424871, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) 1)).
  {
    apply (pop12 3 [] 1 7 ((2, 2) :: (1, 1) :: repeat (1, 2) 40 ++ (164, 2) :: (1, 1) :: repeat (1, 2) 368 ++ (32, 2) :: (1, 1) :: repeat (1, 2) 2613 ++ (9951, 2) :: (1, 1) :: repeat (1, 2) 20868 ++ (69110, 2) :: (1, 1) :: repeat (1, 2) 297773 ++ (1424871, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) 1); closearith.
  }
  (* step 427: P TRANS2_1 *)
  apply (hsteps_trans _ (HB [5] 14 1 3 (repeat (1, 2) 40 ++ (164, 2) :: (1, 1) :: repeat (1, 2) 368 ++ (32, 2) :: (1, 1) :: repeat (1, 2) 2613 ++ (9951, 2) :: (1, 1) :: repeat (1, 2) 20868 ++ (69110, 2) :: (1, 1) :: repeat (1, 2) 297773 ++ (1424871, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) 1)).
  {
    apply (sTRANS2_1 [] 4 12 1 (repeat (1, 2) 40 ++ (164, 2) :: (1, 1) :: repeat (1, 2) 368 ++ (32, 2) :: (1, 1) :: repeat (1, 2) 2613 ++ (9951, 2) :: (1, 1) :: repeat (1, 2) 20868 ++ (69110, 2) :: (1, 1) :: repeat (1, 2) 297773 ++ (1424871, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) 1); closearith.
  }
  (* step 428: M pop12 (40,) *)
  apply (hsteps_trans _ (HB [5] 54 1 83 ((164, 2) :: (1, 1) :: repeat (1, 2) 368 ++ (32, 2) :: (1, 1) :: repeat (1, 2) 2613 ++ (9951, 2) :: (1, 1) :: repeat (1, 2) 20868 ++ (69110, 2) :: (1, 1) :: repeat (1, 2) 297773 ++ (1424871, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) 1)).
  {
    apply (pop12 40 [5] 14 3 ((164, 2) :: (1, 1) :: repeat (1, 2) 368 ++ (32, 2) :: (1, 1) :: repeat (1, 2) 2613 ++ (9951, 2) :: (1, 1) :: repeat (1, 2) 20868 ++ (69110, 2) :: (1, 1) :: repeat (1, 2) 297773 ++ (1424871, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) 1); closearith.
  }
  (* step 429: sTUP *)
  apply (hsteps_trans _ (HC [5] 54 82 2 ((162, 2) :: (1, 1) :: repeat (1, 2) 368 ++ (32, 2) :: (1, 1) :: repeat (1, 2) 2613 ++ (9951, 2) :: (1, 1) :: repeat (1, 2) 20868 ++ (69110, 2) :: (1, 1) :: repeat (1, 2) 297773 ++ (1424871, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) 1)).
  {
    replace ((162, 2) :: (1, 1) :: repeat (1, 2) 368 ++ (32, 2) :: (1, 1) :: repeat (1, 2) 2613 ++ (9951, 2) :: (1, 1) :: repeat (1, 2) 20868 ++ (69110, 2) :: (1, 1) :: repeat (1, 2) 297773 ++ (1424871, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) with ((164 - 2, 2) :: (1, 1) :: repeat (1, 2) 368 ++ (32, 2) :: (1, 1) :: repeat (1, 2) 2613 ++ (9951, 2) :: (1, 1) :: repeat (1, 2) 20868 ++ (69110, 2) :: (1, 1) :: repeat (1, 2) 297773 ++ (1424871, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) by sec_eq.
    apply (sTUP [5] 54 83 164 2 ((1, 1) :: repeat (1, 2) 368 ++ (32, 2) :: (1, 1) :: repeat (1, 2) 2613 ++ (9951, 2) :: (1, 1) :: repeat (1, 2) 20868 ++ (69110, 2) :: (1, 1) :: repeat (1, 2) 297773 ++ (1424871, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) 1); closearith.
  }
  (* step 430: hGRIND_even 39 *)
  apply (hsteps_trans _ (HB [5] 53 1 82 ((2, 2) :: (162, 2) :: (1, 1) :: repeat (1, 2) 368 ++ (32, 2) :: (1, 1) :: repeat (1, 2) 2613 ++ (9951, 2) :: (1, 1) :: repeat (1, 2) 20868 ++ (69110, 2) :: (1, 1) :: repeat (1, 2) 297773 ++ (1424871, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) 1)).
  {
    apply (hGRIND_even 39 [5] 53 ((162, 2) :: (1, 1) :: repeat (1, 2) 368 ++ (32, 2) :: (1, 1) :: repeat (1, 2) 2613 ++ (9951, 2) :: (1, 1) :: repeat (1, 2) 20868 ++ (69110, 2) :: (1, 1) :: repeat (1, 2) 297773 ++ (1424871, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) 1); closearith.
  }
  (* step 431: P TUP2_1 *)
  apply (hsteps_trans _ (HC [54; 5] 82 1 2 ((160, 2) :: (1, 1) :: repeat (1, 2) 368 ++ (32, 2) :: (1, 1) :: repeat (1, 2) 2613 ++ (9951, 2) :: (1, 1) :: repeat (1, 2) 20868 ++ (69110, 2) :: (1, 1) :: repeat (1, 2) 297773 ++ (1424871, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) 1)).
  {
    replace ((160, 2) :: (1, 1) :: repeat (1, 2) 368 ++ (32, 2) :: (1, 1) :: repeat (1, 2) 2613 ++ (9951, 2) :: (1, 1) :: repeat (1, 2) 20868 ++ (69110, 2) :: (1, 1) :: repeat (1, 2) 297773 ++ (1424871, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) with ((162 - 2, 2) :: (1, 1) :: repeat (1, 2) 368 ++ (32, 2) :: (1, 1) :: repeat (1, 2) 2613 ++ (9951, 2) :: (1, 1) :: repeat (1, 2) 20868 ++ (69110, 2) :: (1, 1) :: repeat (1, 2) 297773 ++ (1424871, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) by sec_eq.
    apply (sTUP2_1 [5] 53 81 162 ((1, 1) :: repeat (1, 2) 368 ++ (32, 2) :: (1, 1) :: repeat (1, 2) 2613 ++ (9951, 2) :: (1, 1) :: repeat (1, 2) 20868 ++ (69110, 2) :: (1, 1) :: repeat (1, 2) 297773 ++ (1424871, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) 1); closearith.
  }
  (* step 432: P TDN *)
  apply (hsteps_trans _ (HB [54; 5] 82 1 4 ((160, 2) :: (1, 1) :: repeat (1, 2) 368 ++ (32, 2) :: (1, 1) :: repeat (1, 2) 2613 ++ (9951, 2) :: (1, 1) :: repeat (1, 2) 20868 ++ (69110, 2) :: (1, 1) :: repeat (1, 2) 297773 ++ (1424871, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) 1)).
  {
    apply (sTDN [54; 5] 82 ((160, 2) :: (1, 1) :: repeat (1, 2) 368 ++ (32, 2) :: (1, 1) :: repeat (1, 2) 2613 ++ (9951, 2) :: (1, 1) :: repeat (1, 2) 20868 ++ (69110, 2) :: (1, 1) :: repeat (1, 2) 297773 ++ (1424871, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) 1).
  }
  (* step 433: sTUP *)
  apply (hsteps_trans _ (HC [54; 5] 82 3 2 ((158, 2) :: (1, 1) :: repeat (1, 2) 368 ++ (32, 2) :: (1, 1) :: repeat (1, 2) 2613 ++ (9951, 2) :: (1, 1) :: repeat (1, 2) 20868 ++ (69110, 2) :: (1, 1) :: repeat (1, 2) 297773 ++ (1424871, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) 1)).
  {
    replace ((158, 2) :: (1, 1) :: repeat (1, 2) 368 ++ (32, 2) :: (1, 1) :: repeat (1, 2) 2613 ++ (9951, 2) :: (1, 1) :: repeat (1, 2) 20868 ++ (69110, 2) :: (1, 1) :: repeat (1, 2) 297773 ++ (1424871, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) with ((160 - 2, 2) :: (1, 1) :: repeat (1, 2) 368 ++ (32, 2) :: (1, 1) :: repeat (1, 2) 2613 ++ (9951, 2) :: (1, 1) :: repeat (1, 2) 20868 ++ (69110, 2) :: (1, 1) :: repeat (1, 2) 297773 ++ (1424871, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) by sec_eq.
    apply (sTUP [54; 5] 82 4 160 2 ((1, 1) :: repeat (1, 2) 368 ++ (32, 2) :: (1, 1) :: repeat (1, 2) 2613 ++ (9951, 2) :: (1, 1) :: repeat (1, 2) 20868 ++ (69110, 2) :: (1, 1) :: repeat (1, 2) 297773 ++ (1424871, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) 1); closearith.
  }
  (* step 434: CLEANG_even 78 *)
  apply (hsteps_trans _ (HB [54; 5] 82 1 162 ((2, 2) :: (1, 1) :: repeat (1, 2) 368 ++ (32, 2) :: (1, 1) :: repeat (1, 2) 2613 ++ (9951, 2) :: (1, 1) :: repeat (1, 2) 20868 ++ (69110, 2) :: (1, 1) :: repeat (1, 2) 297773 ++ (1424871, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) 1)).
  {
    apply (CLEANG_even 78 [54; 5] 82 ((1, 1) :: repeat (1, 2) 368 ++ (32, 2) :: (1, 1) :: repeat (1, 2) 2613 ++ (9951, 2) :: (1, 1) :: repeat (1, 2) 20868 ++ (69110, 2) :: (1, 1) :: repeat (1, 2) 297773 ++ (1424871, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) 1); closearith.
  }
  (* step 435: P TRANS2_1 *)
  apply (hsteps_trans _ (HB [83; 54; 5] 163 1 3 (repeat (1, 2) 368 ++ (32, 2) :: (1, 1) :: repeat (1, 2) 2613 ++ (9951, 2) :: (1, 1) :: repeat (1, 2) 20868 ++ (69110, 2) :: (1, 1) :: repeat (1, 2) 297773 ++ (1424871, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) 1)).
  {
    apply (sTRANS2_1 [54; 5] 82 161 1 (repeat (1, 2) 368 ++ (32, 2) :: (1, 1) :: repeat (1, 2) 2613 ++ (9951, 2) :: (1, 1) :: repeat (1, 2) 20868 ++ (69110, 2) :: (1, 1) :: repeat (1, 2) 297773 ++ (1424871, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) 1); closearith.
  }
  (* step 436: M pop12 (368,) *)
  apply (hsteps_trans _ (HB [83; 54; 5] 531 1 739 ((32, 2) :: (1, 1) :: repeat (1, 2) 2613 ++ (9951, 2) :: (1, 1) :: repeat (1, 2) 20868 ++ (69110, 2) :: (1, 1) :: repeat (1, 2) 297773 ++ (1424871, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) 1)).
  {
    apply (pop12 368 [83; 54; 5] 163 3 ((32, 2) :: (1, 1) :: repeat (1, 2) 2613 ++ (9951, 2) :: (1, 1) :: repeat (1, 2) 20868 ++ (69110, 2) :: (1, 1) :: repeat (1, 2) 297773 ++ (1424871, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) 1); closearith.
  }
  (* step 437: sTUP *)
  apply (hsteps_trans _ (HC [83; 54; 5] 531 738 2 ((30, 2) :: (1, 1) :: repeat (1, 2) 2613 ++ (9951, 2) :: (1, 1) :: repeat (1, 2) 20868 ++ (69110, 2) :: (1, 1) :: repeat (1, 2) 297773 ++ (1424871, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) 1)).
  {
    replace ((30, 2) :: (1, 1) :: repeat (1, 2) 2613 ++ (9951, 2) :: (1, 1) :: repeat (1, 2) 20868 ++ (69110, 2) :: (1, 1) :: repeat (1, 2) 297773 ++ (1424871, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) with ((32 - 2, 2) :: (1, 1) :: repeat (1, 2) 2613 ++ (9951, 2) :: (1, 1) :: repeat (1, 2) 20868 ++ (69110, 2) :: (1, 1) :: repeat (1, 2) 297773 ++ (1424871, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) by sec_eq.
    apply (sTUP [83; 54; 5] 531 739 32 2 ((1, 1) :: repeat (1, 2) 2613 ++ (9951, 2) :: (1, 1) :: repeat (1, 2) 20868 ++ (69110, 2) :: (1, 1) :: repeat (1, 2) 297773 ++ (1424871, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) 1); closearith.
  }
  (* step 438: hGRIND_even 367 *)
  apply (hsteps_trans _ (HB [83; 54; 5] 530 1 738 ((2, 2) :: (30, 2) :: (1, 1) :: repeat (1, 2) 2613 ++ (9951, 2) :: (1, 1) :: repeat (1, 2) 20868 ++ (69110, 2) :: (1, 1) :: repeat (1, 2) 297773 ++ (1424871, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) 1)).
  {
    apply (hGRIND_even 367 [83; 54; 5] 530 ((30, 2) :: (1, 1) :: repeat (1, 2) 2613 ++ (9951, 2) :: (1, 1) :: repeat (1, 2) 20868 ++ (69110, 2) :: (1, 1) :: repeat (1, 2) 297773 ++ (1424871, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) 1); closearith.
  }
  (* step 439: P TUP2_1 *)
  apply (hsteps_trans _ (HC [531; 83; 54; 5] 738 1 2 ((28, 2) :: (1, 1) :: repeat (1, 2) 2613 ++ (9951, 2) :: (1, 1) :: repeat (1, 2) 20868 ++ (69110, 2) :: (1, 1) :: repeat (1, 2) 297773 ++ (1424871, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) 1)).
  {
    replace ((28, 2) :: (1, 1) :: repeat (1, 2) 2613 ++ (9951, 2) :: (1, 1) :: repeat (1, 2) 20868 ++ (69110, 2) :: (1, 1) :: repeat (1, 2) 297773 ++ (1424871, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) with ((30 - 2, 2) :: (1, 1) :: repeat (1, 2) 2613 ++ (9951, 2) :: (1, 1) :: repeat (1, 2) 20868 ++ (69110, 2) :: (1, 1) :: repeat (1, 2) 297773 ++ (1424871, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) by sec_eq.
    apply (sTUP2_1 [83; 54; 5] 530 737 30 ((1, 1) :: repeat (1, 2) 2613 ++ (9951, 2) :: (1, 1) :: repeat (1, 2) 20868 ++ (69110, 2) :: (1, 1) :: repeat (1, 2) 297773 ++ (1424871, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) 1); closearith.
  }
  (* step 440: P TDN *)
  apply (hsteps_trans _ (HB [531; 83; 54; 5] 738 1 4 ((28, 2) :: (1, 1) :: repeat (1, 2) 2613 ++ (9951, 2) :: (1, 1) :: repeat (1, 2) 20868 ++ (69110, 2) :: (1, 1) :: repeat (1, 2) 297773 ++ (1424871, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) 1)).
  {
    apply (sTDN [531; 83; 54; 5] 738 ((28, 2) :: (1, 1) :: repeat (1, 2) 2613 ++ (9951, 2) :: (1, 1) :: repeat (1, 2) 20868 ++ (69110, 2) :: (1, 1) :: repeat (1, 2) 297773 ++ (1424871, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) 1).
  }
  (* step 441: sTUP *)
  apply (hsteps_trans _ (HC [531; 83; 54; 5] 738 3 2 ((26, 2) :: (1, 1) :: repeat (1, 2) 2613 ++ (9951, 2) :: (1, 1) :: repeat (1, 2) 20868 ++ (69110, 2) :: (1, 1) :: repeat (1, 2) 297773 ++ (1424871, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) 1)).
  {
    replace ((26, 2) :: (1, 1) :: repeat (1, 2) 2613 ++ (9951, 2) :: (1, 1) :: repeat (1, 2) 20868 ++ (69110, 2) :: (1, 1) :: repeat (1, 2) 297773 ++ (1424871, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) with ((28 - 2, 2) :: (1, 1) :: repeat (1, 2) 2613 ++ (9951, 2) :: (1, 1) :: repeat (1, 2) 20868 ++ (69110, 2) :: (1, 1) :: repeat (1, 2) 297773 ++ (1424871, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) by sec_eq.
    apply (sTUP [531; 83; 54; 5] 738 4 28 2 ((1, 1) :: repeat (1, 2) 2613 ++ (9951, 2) :: (1, 1) :: repeat (1, 2) 20868 ++ (69110, 2) :: (1, 1) :: repeat (1, 2) 297773 ++ (1424871, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) 1); closearith.
  }
  (* step 442: CLEANG_even 12 *)
  apply (hsteps_trans _ (HB [531; 83; 54; 5] 738 1 30 ((2, 2) :: (1, 1) :: repeat (1, 2) 2613 ++ (9951, 2) :: (1, 1) :: repeat (1, 2) 20868 ++ (69110, 2) :: (1, 1) :: repeat (1, 2) 297773 ++ (1424871, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) 1)).
  {
    apply (CLEANG_even 12 [531; 83; 54; 5] 738 ((1, 1) :: repeat (1, 2) 2613 ++ (9951, 2) :: (1, 1) :: repeat (1, 2) 20868 ++ (69110, 2) :: (1, 1) :: repeat (1, 2) 297773 ++ (1424871, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) 1); closearith.
  }
  (* step 443: P TRANS2_1 *)
  apply (hsteps_trans _ (HB [739; 531; 83; 54; 5] 31 1 3 (repeat (1, 2) 2613 ++ (9951, 2) :: (1, 1) :: repeat (1, 2) 20868 ++ (69110, 2) :: (1, 1) :: repeat (1, 2) 297773 ++ (1424871, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) 1)).
  {
    apply (sTRANS2_1 [531; 83; 54; 5] 738 29 1 (repeat (1, 2) 2613 ++ (9951, 2) :: (1, 1) :: repeat (1, 2) 20868 ++ (69110, 2) :: (1, 1) :: repeat (1, 2) 297773 ++ (1424871, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) 1); closearith.
  }
  (* step 444: M pop12 (2613,) *)
  apply (hsteps_trans _ (HB [739; 531; 83; 54; 5] 2644 1 5229 ((9951, 2) :: (1, 1) :: repeat (1, 2) 20868 ++ (69110, 2) :: (1, 1) :: repeat (1, 2) 297773 ++ (1424871, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) 1)).
  {
    apply (pop12 2613 [739; 531; 83; 54; 5] 31 3 ((9951, 2) :: (1, 1) :: repeat (1, 2) 20868 ++ (69110, 2) :: (1, 1) :: repeat (1, 2) 297773 ++ (1424871, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) 1); closearith.
  }
  (* step 445: sTUP *)
  apply (hsteps_trans _ (HC [739; 531; 83; 54; 5] 2644 5228 2 ((9949, 2) :: (1, 1) :: repeat (1, 2) 20868 ++ (69110, 2) :: (1, 1) :: repeat (1, 2) 297773 ++ (1424871, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) 1)).
  {
    replace ((9949, 2) :: (1, 1) :: repeat (1, 2) 20868 ++ (69110, 2) :: (1, 1) :: repeat (1, 2) 297773 ++ (1424871, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) with ((9951 - 2, 2) :: (1, 1) :: repeat (1, 2) 20868 ++ (69110, 2) :: (1, 1) :: repeat (1, 2) 297773 ++ (1424871, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) by sec_eq.
    apply (sTUP [739; 531; 83; 54; 5] 2644 5229 9951 2 ((1, 1) :: repeat (1, 2) 20868 ++ (69110, 2) :: (1, 1) :: repeat (1, 2) 297773 ++ (1424871, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) 1); closearith.
  }
  (* step 446: hGRIND_even 2612 *)
  apply (hsteps_trans _ (HB [739; 531; 83; 54; 5] 2643 1 5228 ((2, 2) :: (9949, 2) :: (1, 1) :: repeat (1, 2) 20868 ++ (69110, 2) :: (1, 1) :: repeat (1, 2) 297773 ++ (1424871, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) 1)).
  {
    apply (hGRIND_even 2612 [739; 531; 83; 54; 5] 2643 ((9949, 2) :: (1, 1) :: repeat (1, 2) 20868 ++ (69110, 2) :: (1, 1) :: repeat (1, 2) 297773 ++ (1424871, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) 1); closearith.
  }
  (* step 447: P TUP2_1 *)
  apply (hsteps_trans _ (HC [2644; 739; 531; 83; 54; 5] 5228 1 2 ((9947, 2) :: (1, 1) :: repeat (1, 2) 20868 ++ (69110, 2) :: (1, 1) :: repeat (1, 2) 297773 ++ (1424871, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) 1)).
  {
    replace ((9947, 2) :: (1, 1) :: repeat (1, 2) 20868 ++ (69110, 2) :: (1, 1) :: repeat (1, 2) 297773 ++ (1424871, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) with ((9949 - 2, 2) :: (1, 1) :: repeat (1, 2) 20868 ++ (69110, 2) :: (1, 1) :: repeat (1, 2) 297773 ++ (1424871, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) by sec_eq.
    apply (sTUP2_1 [739; 531; 83; 54; 5] 2643 5227 9949 ((1, 1) :: repeat (1, 2) 20868 ++ (69110, 2) :: (1, 1) :: repeat (1, 2) 297773 ++ (1424871, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) 1); closearith.
  }
  (* step 448: P TDN *)
  apply (sTDN [2644; 739; 531; 83; 54; 5] 5228 ((9947, 2) :: (1, 1) :: repeat (1, 2) 20868 ++ (69110, 2) :: (1, 1) :: repeat (1, 2) 297773 ++ (1424871, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) 1).
Qed.

(* CASCADE56i: steps 449-460 of the CASCADE56 chain. *)
Lemma CASCADE56i : forall w,
  hsteps (HB [2644; 739; 531; 83; 54; 5] 5228 1 4 ((9947, 2) :: (1, 1) :: repeat (1, 2) 20868 ++ (69110, 2) :: (1, 1) :: repeat (1, 2) 297773 ++ (1424871, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) 1)
         (HB [51689; 26098; 2644; 739; 531; 83; 54; 5] 69109 1 3 (repeat (1, 2) 297773 ++ (1424871, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) 1).
Proof.
  intro w.
  (* step 449: sTUP *)
  apply (hsteps_trans _ (HC [2644; 739; 531; 83; 54; 5] 5228 3 2 ((9945, 2) :: (1, 1) :: repeat (1, 2) 20868 ++ (69110, 2) :: (1, 1) :: repeat (1, 2) 297773 ++ (1424871, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) 1)).
  {
    replace ((9945, 2) :: (1, 1) :: repeat (1, 2) 20868 ++ (69110, 2) :: (1, 1) :: repeat (1, 2) 297773 ++ (1424871, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) with ((9947 - 2, 2) :: (1, 1) :: repeat (1, 2) 20868 ++ (69110, 2) :: (1, 1) :: repeat (1, 2) 297773 ++ (1424871, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) by sec_eq.
    apply (sTUP [2644; 739; 531; 83; 54; 5] 5228 4 9947 2 ((1, 1) :: repeat (1, 2) 20868 ++ (69110, 2) :: (1, 1) :: repeat (1, 2) 297773 ++ (1424871, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) 1); closearith.
  }
  (* step 450: CLEANG_odd 4971 *)
  apply (hsteps_trans _ (HB [2644; 739; 531; 83; 54; 5] 5228 1 9950 (repeat (1, 2) 1 ++ (1, 1) :: repeat (1, 2) 20868 ++ (69110, 2) :: (1, 1) :: repeat (1, 2) 297773 ++ (1424871, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) 1)).
  {
    replace (repeat (1, 2) 1 ++ (1, 1) :: repeat (1, 2) 20868 ++ (69110, 2) :: (1, 1) :: repeat (1, 2) 297773 ++ (1424871, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) with ((1, 2) :: (1, 1) :: repeat (1, 2) 20868 ++ (69110, 2) :: (1, 1) :: repeat (1, 2) 297773 ++ (1424871, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) by sec_eq.
    apply (CLEANG_odd 4971 [2644; 739; 531; 83; 54; 5] 5228 ((1, 1) :: repeat (1, 2) 20868 ++ (69110, 2) :: (1, 1) :: repeat (1, 2) 297773 ++ (1424871, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) 1); closearith.
  }
  (* step 451: M pop12 (1,) *)
  apply (hsteps_trans _ (HB [2644; 739; 531; 83; 54; 5] 5229 1 9952 ((1, 1) :: repeat (1, 2) 20868 ++ (69110, 2) :: (1, 1) :: repeat (1, 2) 297773 ++ (1424871, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) 1)).
  {
    apply (pop12 1 [2644; 739; 531; 83; 54; 5] 5228 9950 ((1, 1) :: repeat (1, 2) 20868 ++ (69110, 2) :: (1, 1) :: repeat (1, 2) 297773 ++ (1424871, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) 1); closearith.
  }
  (* step 452: P POP *)
  apply (hsteps_trans _ (HB [2644; 739; 531; 83; 54; 5] 5230 1 9953 (repeat (1, 2) 20868 ++ (69110, 2) :: (1, 1) :: repeat (1, 2) 297773 ++ (1424871, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) 1)).
  {
    apply (sPOP1 [2644; 739; 531; 83; 54; 5] 5229 9952 (repeat (1, 2) 20868 ++ (69110, 2) :: (1, 1) :: repeat (1, 2) 297773 ++ (1424871, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) 1); closearith.
  }
  (* step 453: M pop12 (20868,) *)
  apply (hsteps_trans _ (HB [2644; 739; 531; 83; 54; 5] 26098 1 51689 ((69110, 2) :: (1, 1) :: repeat (1, 2) 297773 ++ (1424871, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) 1)).
  {
    apply (pop12 20868 [2644; 739; 531; 83; 54; 5] 5230 9953 ((69110, 2) :: (1, 1) :: repeat (1, 2) 297773 ++ (1424871, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) 1); closearith.
  }
  (* step 454: sTUP *)
  apply (hsteps_trans _ (HC [2644; 739; 531; 83; 54; 5] 26098 51688 2 ((69108, 2) :: (1, 1) :: repeat (1, 2) 297773 ++ (1424871, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) 1)).
  {
    replace ((69108, 2) :: (1, 1) :: repeat (1, 2) 297773 ++ (1424871, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) with ((69110 - 2, 2) :: (1, 1) :: repeat (1, 2) 297773 ++ (1424871, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) by sec_eq.
    apply (sTUP [2644; 739; 531; 83; 54; 5] 26098 51689 69110 2 ((1, 1) :: repeat (1, 2) 297773 ++ (1424871, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) 1); closearith.
  }
  (* step 455: hGRIND_even 25842 *)
  apply (hsteps_trans _ (HB [2644; 739; 531; 83; 54; 5] 26097 1 51688 ((2, 2) :: (69108, 2) :: (1, 1) :: repeat (1, 2) 297773 ++ (1424871, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) 1)).
  {
    rewrite NUM56X10.
    apply (hGRIND_even 25842 [2644; 739; 531; 83; 54; 5] 26097 ((69108, 2) :: (1, 1) :: repeat (1, 2) 297773 ++ (1424871, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) 1); closearith.
  }
  (* step 456: P TUP2_1 *)
  apply (hsteps_trans _ (HC [26098; 2644; 739; 531; 83; 54; 5] 51688 1 2 ((69106, 2) :: (1, 1) :: repeat (1, 2) 297773 ++ (1424871, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) 1)).
  {
    replace ((69106, 2) :: (1, 1) :: repeat (1, 2) 297773 ++ (1424871, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) with ((69108 - 2, 2) :: (1, 1) :: repeat (1, 2) 297773 ++ (1424871, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) by sec_eq.
    apply (sTUP2_1 [2644; 739; 531; 83; 54; 5] 26097 51687 69108 ((1, 1) :: repeat (1, 2) 297773 ++ (1424871, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) 1); closearith.
  }
  (* step 457: P TDN *)
  apply (hsteps_trans _ (HB [26098; 2644; 739; 531; 83; 54; 5] 51688 1 4 ((69106, 2) :: (1, 1) :: repeat (1, 2) 297773 ++ (1424871, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) 1)).
  {
    apply (sTDN [26098; 2644; 739; 531; 83; 54; 5] 51688 ((69106, 2) :: (1, 1) :: repeat (1, 2) 297773 ++ (1424871, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) 1).
  }
  (* step 458: sTUP *)
  apply (hsteps_trans _ (HC [26098; 2644; 739; 531; 83; 54; 5] 51688 3 2 ((69104, 2) :: (1, 1) :: repeat (1, 2) 297773 ++ (1424871, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) 1)).
  {
    replace ((69104, 2) :: (1, 1) :: repeat (1, 2) 297773 ++ (1424871, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) with ((69106 - 2, 2) :: (1, 1) :: repeat (1, 2) 297773 ++ (1424871, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) by sec_eq.
    apply (sTUP [26098; 2644; 739; 531; 83; 54; 5] 51688 4 69106 2 ((1, 1) :: repeat (1, 2) 297773 ++ (1424871, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) 1); closearith.
  }
  (* step 459: CLEANG_even 34551 *)
  apply (hsteps_trans _ (HB [26098; 2644; 739; 531; 83; 54; 5] 51688 1 69108 ((2, 2) :: (1, 1) :: repeat (1, 2) 297773 ++ (1424871, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) 1)).
  {
    rewrite NUM56X11.
    rewrite NUM56X12.
    apply (CLEANG_even 34551 [26098; 2644; 739; 531; 83; 54; 5] 51688 ((1, 1) :: repeat (1, 2) 297773 ++ (1424871, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) 1); closearith.
  }
  (* step 460: P TRANS2_1 *)
  apply (sTRANS2_1 [26098; 2644; 739; 531; 83; 54; 5] 51688 69107 1 (repeat (1, 2) 297773 ++ (1424871, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) 1); closearith.
Qed.

(* CASCADE56j: steps 461-461 of the CASCADE56 chain. *)
Lemma CASCADE56j : forall w,
  hsteps (HB [51689; 26098; 2644; 739; 531; 83; 54; 5] 69109 1 3 (repeat (1, 2) 297773 ++ (1424871, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) 1)
         (HB [51689; 26098; 2644; 739; 531; 83; 54; 5] 366882 1 595549 ((1424871, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) 1).
Proof.
  intro w.
  replace 366882 with (69109 + 297773)
    by (apply Nat.eqb_eq; vm_compute; reflexivity).
  replace 595549 with (3 + 2 * 297773)
    by (apply Nat.eqb_eq; vm_compute; reflexivity).
  (* step 461: M pop12 (297773,) *)
  apply (pop12 297773 [51689; 26098; 2644; 739; 531; 83; 54; 5] 69109 3 ((1424871, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) 1); closearith.
Qed.

(* CASCADE56k: steps 462-517 of the CASCADE56 chain. *)
Lemma CASCADE56k : forall w,
  hsteps (HB [51689; 26098; 2644; 739; 531; 83; 54; 5] 366882 1 595549 ((1424871, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) 1)
         (HC [20; 0] 34 1 2 ((6, 2) :: (1, 1) :: repeat (1, 2) 83 ++ (3007, 2) :: (1, 1) :: repeat (1, 2) 6030 ++ (8746, 2) :: (1, 1) :: repeat (1, 2) 51689 ++ (263502, 2) :: (1, 1) :: repeat (1, 2) 595550 ++ (233769, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) 1).
Proof.
  intro w.
  (* step 462: sTUP *)
  apply (hsteps_trans _ (HC [51689; 26098; 2644; 739; 531; 83; 54; 5] 366882 595548 2 ((1424869, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) 1)).
  {
    rewrite NUM56X13.
    rewrite NUM56X14.
    apply (sTUP [51689; 26098; 2644; 739; 531; 83; 54; 5] 366882 595549 1424871 2 ((1, 1) :: repeat (1, 2) 2851852 ++ w) 1); closearith.
  }
  (* step 463: hGRIND_even 297772 *)
  apply (hsteps_trans _ (HB [51689; 26098; 2644; 739; 531; 83; 54; 5] 366881 1 595548 ((2, 2) :: (1424869, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) 1)).
  {
    rewrite NUM56X15.
    apply (hGRIND_even 297772 [51689; 26098; 2644; 739; 531; 83; 54; 5] 366881 ((1424869, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) 1); closearith.
  }
  (* step 464: P TUP2_1 *)
  apply (hsteps_trans _ (HC [366882; 51689; 26098; 2644; 739; 531; 83; 54; 5] 595548 1 2 ((1424867, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) 1)).
  {
    rewrite NUM56X16.
    rewrite NUM56X17.
    rewrite NUM56X18.
    apply (sTUP2_1 [51689; 26098; 2644; 739; 531; 83; 54; 5] 366881 595547 1424869 ((1, 1) :: repeat (1, 2) 2851852 ++ w) 1); closearith.
  }
  (* step 465: P TDN *)
  apply (hsteps_trans _ (HB [366882; 51689; 26098; 2644; 739; 531; 83; 54; 5] 595548 1 4 ((1424867, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) 1)).
  {
    apply (sTDN [366882; 51689; 26098; 2644; 739; 531; 83; 54; 5] 595548 ((1424867, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) 1).
  }
  (* step 466: sTUP *)
  apply (hsteps_trans _ (HC [366882; 51689; 26098; 2644; 739; 531; 83; 54; 5] 595548 3 2 ((1424865, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) 1)).
  {
    rewrite NUM56X19.
    apply (sTUP [366882; 51689; 26098; 2644; 739; 531; 83; 54; 5] 595548 4 1424867 2 ((1, 1) :: repeat (1, 2) 2851852 ++ w) 1); closearith.
  }
  (* step 467: DIPGRIND 595548 233769 *)
  apply (hsteps_trans _ (HC [366882; 51689; 26098; 2644; 739; 531; 83; 54; 5] 0 3 2 (repeat (1, 2) 595548 ++ (233769, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) 1)).
  {
    rewrite NUM56X20.
    apply (DIPGRIND 595548 233769 [366882; 51689; 26098; 2644; 739; 531; 83; 54; 5] ((1, 1) :: repeat (1, 2) 2851852 ++ w) 1); closearith.
  }
  (* step 468: P PX2A *)
  apply (hsteps_trans _ (HC [26098; 2644; 739; 531; 83; 54; 5] 51688 366880 2 ((1, 1) :: repeat (1, 2) 595550 ++ (233769, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) 1)).
  {
    rewrite NUM56tc1. rewrite NUM56tc2. rewrite NUM56tc3.
    replace ((1, 1) :: repeat (1, 2) 595550 ++ (233769, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w)
      with ((1, 1) :: (1, 2) :: (1, 2) :: repeat (1, 2) 595548 ++ (233769, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w)
      by (apply REP56c).
    exact (hsteps_step _ _ _ (hPX2A 366879 51688 [26098; 2644; 739; 531; 83; 54; 5] (repeat (1, 2) 595548 ++ (233769, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) 1) (hsteps_refl _)).
  }
  (* step 469: P PUSH *)
  apply (hsteps_trans _ (HC [26098; 2644; 739; 531; 83; 54; 5] 51687 1 2 ((366878, 2) :: (1, 1) :: repeat (1, 2) 595550 ++ (233769, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) 1)).
  {
    rewrite NUM56X21.
    apply (sPUSH [26098; 2644; 739; 531; 83; 54; 5] 51687 366880 ((1, 1) :: repeat (1, 2) 595550 ++ (233769, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) 1); closearith.
  }
  (* step 470: P TDN *)
  apply (hsteps_trans _ (HB [26098; 2644; 739; 531; 83; 54; 5] 51687 1 4 ((366878, 2) :: (1, 1) :: repeat (1, 2) 595550 ++ (233769, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) 1)).
  {
    apply (sTDN [26098; 2644; 739; 531; 83; 54; 5] 51687 ((366878, 2) :: (1, 1) :: repeat (1, 2) 595550 ++ (233769, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) 1).
  }
  (* step 471: sTUP *)
  apply (hsteps_trans _ (HC [26098; 2644; 739; 531; 83; 54; 5] 51687 3 2 ((366876, 2) :: (1, 1) :: repeat (1, 2) 595550 ++ (233769, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) 1)).
  {
    rewrite NUM56X22.
    apply (sTUP [26098; 2644; 739; 531; 83; 54; 5] 51687 4 366878 2 ((1, 1) :: repeat (1, 2) 595550 ++ (233769, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) 1); closearith.
  }
  (* step 472: DIPGRIND 51687 263502 *)
  apply (hsteps_trans _ (HC [26098; 2644; 739; 531; 83; 54; 5] 0 3 2 (repeat (1, 2) 51687 ++ (263502, 2) :: (1, 1) :: repeat (1, 2) 595550 ++ (233769, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) 1)).
  {
    rewrite NUM56X23.
    apply (DIPGRIND 51687 263502 [26098; 2644; 739; 531; 83; 54; 5] ((1, 1) :: repeat (1, 2) 595550 ++ (233769, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) 1); closearith.
  }
  (* step 473: P PX2A *)
  apply (hsteps_trans _ (HC [739; 531; 83; 54; 5] 2643 26096 2 ((1, 1) :: repeat (1, 2) 51689 ++ (263502, 2) :: (1, 1) :: repeat (1, 2) 595550 ++ (233769, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) 1)).
  {
    exact (hsteps_step _ _ _ (hPX2A 26095 2643 [739; 531; 83; 54; 5] (repeat (1, 2) 51687 ++ (263502, 2) :: (1, 1) :: repeat (1, 2) 595550 ++ (233769, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) 1) (hsteps_refl _)).
  }
  (* step 474: P PUSH *)
  apply (hsteps_trans _ (HC [739; 531; 83; 54; 5] 2642 1 2 ((26094, 2) :: (1, 1) :: repeat (1, 2) 51689 ++ (263502, 2) :: (1, 1) :: repeat (1, 2) 595550 ++ (233769, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) 1)).
  {
    replace ((26094, 2) :: (1, 1) :: repeat (1, 2) 51689 ++ (263502, 2) :: (1, 1) :: repeat (1, 2) 595550 ++ (233769, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) with ((26096 - 2, 2) :: (1, 1) :: repeat (1, 2) 51689 ++ (263502, 2) :: (1, 1) :: repeat (1, 2) 595550 ++ (233769, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) by sec_eq.
    apply (sPUSH [739; 531; 83; 54; 5] 2642 26096 ((1, 1) :: repeat (1, 2) 51689 ++ (263502, 2) :: (1, 1) :: repeat (1, 2) 595550 ++ (233769, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) 1); closearith.
  }
  (* step 475: P TDN *)
  apply (hsteps_trans _ (HB [739; 531; 83; 54; 5] 2642 1 4 ((26094, 2) :: (1, 1) :: repeat (1, 2) 51689 ++ (263502, 2) :: (1, 1) :: repeat (1, 2) 595550 ++ (233769, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) 1)).
  {
    apply (sTDN [739; 531; 83; 54; 5] 2642 ((26094, 2) :: (1, 1) :: repeat (1, 2) 51689 ++ (263502, 2) :: (1, 1) :: repeat (1, 2) 595550 ++ (233769, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) 1).
  }
  (* step 476: sTUP *)
  apply (hsteps_trans _ (HC [739; 531; 83; 54; 5] 2642 3 2 ((26092, 2) :: (1, 1) :: repeat (1, 2) 51689 ++ (263502, 2) :: (1, 1) :: repeat (1, 2) 595550 ++ (233769, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) 1)).
  {
    replace ((26092, 2) :: (1, 1) :: repeat (1, 2) 51689 ++ (263502, 2) :: (1, 1) :: repeat (1, 2) 595550 ++ (233769, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) with ((26094 - 2, 2) :: (1, 1) :: repeat (1, 2) 51689 ++ (263502, 2) :: (1, 1) :: repeat (1, 2) 595550 ++ (233769, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) by sec_eq.
    apply (sTUP [739; 531; 83; 54; 5] 2642 4 26094 2 ((1, 1) :: repeat (1, 2) 51689 ++ (263502, 2) :: (1, 1) :: repeat (1, 2) 595550 ++ (233769, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) 1); closearith.
  }
  (* step 477: DIPGRIND 2642 20808 *)
  apply (hsteps_trans _ (HC [739; 531; 83; 54; 5] 0 3 2 (repeat (1, 2) 2642 ++ (20808, 2) :: (1, 1) :: repeat (1, 2) 51689 ++ (263502, 2) :: (1, 1) :: repeat (1, 2) 595550 ++ (233769, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) 1)).
  {
    apply (DIPGRIND 2642 20808 [739; 531; 83; 54; 5] ((1, 1) :: repeat (1, 2) 51689 ++ (263502, 2) :: (1, 1) :: repeat (1, 2) 595550 ++ (233769, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) 1); closearith.
  }
  (* step 478: P PX2A *)
  apply (hsteps_trans _ (HC [83; 54; 5] 530 737 2 ((1, 1) :: repeat (1, 2) 2644 ++ (20808, 2) :: (1, 1) :: repeat (1, 2) 51689 ++ (263502, 2) :: (1, 1) :: repeat (1, 2) 595550 ++ (233769, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) 1)).
  {
    exact (hsteps_step _ _ _ (hPX2A 736 530 [83; 54; 5] (repeat (1, 2) 2642 ++ (20808, 2) :: (1, 1) :: repeat (1, 2) 51689 ++ (263502, 2) :: (1, 1) :: repeat (1, 2) 595550 ++ (233769, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) 1) (hsteps_refl _)).
  }
  (* step 479: hGRIND 367 *)
  apply (hsteps_trans _ (HB [83; 54; 5] 530 1 740 ((1, 1) :: repeat (1, 2) 2644 ++ (20808, 2) :: (1, 1) :: repeat (1, 2) 51689 ++ (263502, 2) :: (1, 1) :: repeat (1, 2) 595550 ++ (233769, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) 1)).
  {
    apply (hGRIND 367 [83; 54; 5] 530 ((1, 1) :: repeat (1, 2) 2644 ++ (20808, 2) :: (1, 1) :: repeat (1, 2) 51689 ++ (263502, 2) :: (1, 1) :: repeat (1, 2) 595550 ++ (233769, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) 1); closearith.
  }
  (* step 480: P POP *)
  apply (hsteps_trans _ (HB [83; 54; 5] 531 1 741 (repeat (1, 2) 2644 ++ (20808, 2) :: (1, 1) :: repeat (1, 2) 51689 ++ (263502, 2) :: (1, 1) :: repeat (1, 2) 595550 ++ (233769, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) 1)).
  {
    apply (sPOP1 [83; 54; 5] 530 740 (repeat (1, 2) 2644 ++ (20808, 2) :: (1, 1) :: repeat (1, 2) 51689 ++ (263502, 2) :: (1, 1) :: repeat (1, 2) 595550 ++ (233769, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) 1); closearith.
  }
  (* step 481: M pop12 (2644,) *)
  apply (hsteps_trans _ (HB [83; 54; 5] 3175 1 6029 ((20808, 2) :: (1, 1) :: repeat (1, 2) 51689 ++ (263502, 2) :: (1, 1) :: repeat (1, 2) 595550 ++ (233769, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) 1)).
  {
    apply (pop12 2644 [83; 54; 5] 531 741 ((20808, 2) :: (1, 1) :: repeat (1, 2) 51689 ++ (263502, 2) :: (1, 1) :: repeat (1, 2) 595550 ++ (233769, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) 1); closearith.
  }
  (* step 482: sTUP *)
  apply (hsteps_trans _ (HC [83; 54; 5] 3175 6028 2 ((20806, 2) :: (1, 1) :: repeat (1, 2) 51689 ++ (263502, 2) :: (1, 1) :: repeat (1, 2) 595550 ++ (233769, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) 1)).
  {
    replace ((20806, 2) :: (1, 1) :: repeat (1, 2) 51689 ++ (263502, 2) :: (1, 1) :: repeat (1, 2) 595550 ++ (233769, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) with ((20808 - 2, 2) :: (1, 1) :: repeat (1, 2) 51689 ++ (263502, 2) :: (1, 1) :: repeat (1, 2) 595550 ++ (233769, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) by sec_eq.
    apply (sTUP [83; 54; 5] 3175 6029 20808 2 ((1, 1) :: repeat (1, 2) 51689 ++ (263502, 2) :: (1, 1) :: repeat (1, 2) 595550 ++ (233769, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) 1); closearith.
  }
  (* step 483: hGRIND_even 3012 *)
  apply (hsteps_trans _ (HB [83; 54; 5] 3174 1 6028 ((2, 2) :: (20806, 2) :: (1, 1) :: repeat (1, 2) 51689 ++ (263502, 2) :: (1, 1) :: repeat (1, 2) 595550 ++ (233769, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) 1)).
  {
    apply (hGRIND_even 3012 [83; 54; 5] 3174 ((20806, 2) :: (1, 1) :: repeat (1, 2) 51689 ++ (263502, 2) :: (1, 1) :: repeat (1, 2) 595550 ++ (233769, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) 1); closearith.
  }
  (* step 484: P TUP2_1 *)
  apply (hsteps_trans _ (HC [3175; 83; 54; 5] 6028 1 2 ((20804, 2) :: (1, 1) :: repeat (1, 2) 51689 ++ (263502, 2) :: (1, 1) :: repeat (1, 2) 595550 ++ (233769, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) 1)).
  {
    replace ((20804, 2) :: (1, 1) :: repeat (1, 2) 51689 ++ (263502, 2) :: (1, 1) :: repeat (1, 2) 595550 ++ (233769, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) with ((20806 - 2, 2) :: (1, 1) :: repeat (1, 2) 51689 ++ (263502, 2) :: (1, 1) :: repeat (1, 2) 595550 ++ (233769, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) by sec_eq.
    apply (sTUP2_1 [83; 54; 5] 3174 6027 20806 ((1, 1) :: repeat (1, 2) 51689 ++ (263502, 2) :: (1, 1) :: repeat (1, 2) 595550 ++ (233769, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) 1); closearith.
  }
  (* step 485: P TDN *)
  apply (hsteps_trans _ (HB [3175; 83; 54; 5] 6028 1 4 ((20804, 2) :: (1, 1) :: repeat (1, 2) 51689 ++ (263502, 2) :: (1, 1) :: repeat (1, 2) 595550 ++ (233769, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) 1)).
  {
    apply (sTDN [3175; 83; 54; 5] 6028 ((20804, 2) :: (1, 1) :: repeat (1, 2) 51689 ++ (263502, 2) :: (1, 1) :: repeat (1, 2) 595550 ++ (233769, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) 1).
  }
  (* step 486: sTUP *)
  apply (hsteps_trans _ (HC [3175; 83; 54; 5] 6028 3 2 ((20802, 2) :: (1, 1) :: repeat (1, 2) 51689 ++ (263502, 2) :: (1, 1) :: repeat (1, 2) 595550 ++ (233769, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) 1)).
  {
    replace ((20802, 2) :: (1, 1) :: repeat (1, 2) 51689 ++ (263502, 2) :: (1, 1) :: repeat (1, 2) 595550 ++ (233769, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) with ((20804 - 2, 2) :: (1, 1) :: repeat (1, 2) 51689 ++ (263502, 2) :: (1, 1) :: repeat (1, 2) 595550 ++ (233769, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) by sec_eq.
    apply (sTUP [3175; 83; 54; 5] 6028 4 20804 2 ((1, 1) :: repeat (1, 2) 51689 ++ (263502, 2) :: (1, 1) :: repeat (1, 2) 595550 ++ (233769, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) 1); closearith.
  }
  (* step 487: DIPGRIND 6028 8746 *)
  apply (hsteps_trans _ (HC [3175; 83; 54; 5] 0 3 2 (repeat (1, 2) 6028 ++ (8746, 2) :: (1, 1) :: repeat (1, 2) 51689 ++ (263502, 2) :: (1, 1) :: repeat (1, 2) 595550 ++ (233769, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) 1)).
  {
    apply (DIPGRIND 6028 8746 [3175; 83; 54; 5] ((1, 1) :: repeat (1, 2) 51689 ++ (263502, 2) :: (1, 1) :: repeat (1, 2) 595550 ++ (233769, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) 1); closearith.
  }
  (* step 488: P PX2A *)
  apply (hsteps_trans _ (HC [54; 5] 82 3173 2 ((1, 1) :: repeat (1, 2) 6030 ++ (8746, 2) :: (1, 1) :: repeat (1, 2) 51689 ++ (263502, 2) :: (1, 1) :: repeat (1, 2) 595550 ++ (233769, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) 1)).
  {
    exact (hsteps_step _ _ _ (hPX2A 3172 82 [54; 5] (repeat (1, 2) 6028 ++ (8746, 2) :: (1, 1) :: repeat (1, 2) 51689 ++ (263502, 2) :: (1, 1) :: repeat (1, 2) 595550 ++ (233769, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) 1) (hsteps_refl _)).
  }
  (* step 489: P PUSH *)
  apply (hsteps_trans _ (HC [54; 5] 81 1 2 ((3171, 2) :: (1, 1) :: repeat (1, 2) 6030 ++ (8746, 2) :: (1, 1) :: repeat (1, 2) 51689 ++ (263502, 2) :: (1, 1) :: repeat (1, 2) 595550 ++ (233769, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) 1)).
  {
    replace ((3171, 2) :: (1, 1) :: repeat (1, 2) 6030 ++ (8746, 2) :: (1, 1) :: repeat (1, 2) 51689 ++ (263502, 2) :: (1, 1) :: repeat (1, 2) 595550 ++ (233769, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) with ((3173 - 2, 2) :: (1, 1) :: repeat (1, 2) 6030 ++ (8746, 2) :: (1, 1) :: repeat (1, 2) 51689 ++ (263502, 2) :: (1, 1) :: repeat (1, 2) 595550 ++ (233769, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) by sec_eq.
    apply (sPUSH [54; 5] 81 3173 ((1, 1) :: repeat (1, 2) 6030 ++ (8746, 2) :: (1, 1) :: repeat (1, 2) 51689 ++ (263502, 2) :: (1, 1) :: repeat (1, 2) 595550 ++ (233769, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) 1); closearith.
  }
  (* step 490: P TDN *)
  apply (hsteps_trans _ (HB [54; 5] 81 1 4 ((3171, 2) :: (1, 1) :: repeat (1, 2) 6030 ++ (8746, 2) :: (1, 1) :: repeat (1, 2) 51689 ++ (263502, 2) :: (1, 1) :: repeat (1, 2) 595550 ++ (233769, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) 1)).
  {
    apply (sTDN [54; 5] 81 ((3171, 2) :: (1, 1) :: repeat (1, 2) 6030 ++ (8746, 2) :: (1, 1) :: repeat (1, 2) 51689 ++ (263502, 2) :: (1, 1) :: repeat (1, 2) 595550 ++ (233769, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) 1).
  }
  (* step 491: sTUP *)
  apply (hsteps_trans _ (HC [54; 5] 81 3 2 ((3169, 2) :: (1, 1) :: repeat (1, 2) 6030 ++ (8746, 2) :: (1, 1) :: repeat (1, 2) 51689 ++ (263502, 2) :: (1, 1) :: repeat (1, 2) 595550 ++ (233769, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) 1)).
  {
    replace ((3169, 2) :: (1, 1) :: repeat (1, 2) 6030 ++ (8746, 2) :: (1, 1) :: repeat (1, 2) 51689 ++ (263502, 2) :: (1, 1) :: repeat (1, 2) 595550 ++ (233769, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) with ((3171 - 2, 2) :: (1, 1) :: repeat (1, 2) 6030 ++ (8746, 2) :: (1, 1) :: repeat (1, 2) 51689 ++ (263502, 2) :: (1, 1) :: repeat (1, 2) 595550 ++ (233769, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) by sec_eq.
    apply (sTUP [54; 5] 81 4 3171 2 ((1, 1) :: repeat (1, 2) 6030 ++ (8746, 2) :: (1, 1) :: repeat (1, 2) 51689 ++ (263502, 2) :: (1, 1) :: repeat (1, 2) 595550 ++ (233769, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) 1); closearith.
  }
  (* step 492: DIPGRIND 81 3007 *)
  apply (hsteps_trans _ (HC [54; 5] 0 3 2 (repeat (1, 2) 81 ++ (3007, 2) :: (1, 1) :: repeat (1, 2) 6030 ++ (8746, 2) :: (1, 1) :: repeat (1, 2) 51689 ++ (263502, 2) :: (1, 1) :: repeat (1, 2) 595550 ++ (233769, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) 1)).
  {
    apply (DIPGRIND 81 3007 [54; 5] ((1, 1) :: repeat (1, 2) 6030 ++ (8746, 2) :: (1, 1) :: repeat (1, 2) 51689 ++ (263502, 2) :: (1, 1) :: repeat (1, 2) 595550 ++ (233769, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) 1); closearith.
  }
  (* step 493: P PX2A *)
  apply (hsteps_trans _ (HC [] 4 52 2 ((1, 1) :: repeat (1, 2) 83 ++ (3007, 2) :: (1, 1) :: repeat (1, 2) 6030 ++ (8746, 2) :: (1, 1) :: repeat (1, 2) 51689 ++ (263502, 2) :: (1, 1) :: repeat (1, 2) 595550 ++ (233769, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) 1)).
  {
    exact (hsteps_step _ _ _ (hPX2A 51 4 [] (repeat (1, 2) 81 ++ (3007, 2) :: (1, 1) :: repeat (1, 2) 6030 ++ (8746, 2) :: (1, 1) :: repeat (1, 2) 51689 ++ (263502, 2) :: (1, 1) :: repeat (1, 2) 595550 ++ (233769, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) 1) (hsteps_refl _)).
  }
  (* step 494: P PUSH *)
  apply (hsteps_trans _ (HC [] 3 1 2 ((50, 2) :: (1, 1) :: repeat (1, 2) 83 ++ (3007, 2) :: (1, 1) :: repeat (1, 2) 6030 ++ (8746, 2) :: (1, 1) :: repeat (1, 2) 51689 ++ (263502, 2) :: (1, 1) :: repeat (1, 2) 595550 ++ (233769, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) 1)).
  {
    replace ((50, 2) :: (1, 1) :: repeat (1, 2) 83 ++ (3007, 2) :: (1, 1) :: repeat (1, 2) 6030 ++ (8746, 2) :: (1, 1) :: repeat (1, 2) 51689 ++ (263502, 2) :: (1, 1) :: repeat (1, 2) 595550 ++ (233769, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) with ((52 - 2, 2) :: (1, 1) :: repeat (1, 2) 83 ++ (3007, 2) :: (1, 1) :: repeat (1, 2) 6030 ++ (8746, 2) :: (1, 1) :: repeat (1, 2) 51689 ++ (263502, 2) :: (1, 1) :: repeat (1, 2) 595550 ++ (233769, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) by sec_eq.
    apply (sPUSH [] 3 52 ((1, 1) :: repeat (1, 2) 83 ++ (3007, 2) :: (1, 1) :: repeat (1, 2) 6030 ++ (8746, 2) :: (1, 1) :: repeat (1, 2) 51689 ++ (263502, 2) :: (1, 1) :: repeat (1, 2) 595550 ++ (233769, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) 1); closearith.
  }
  (* step 495: P TDN *)
  apply (hsteps_trans _ (HB [] 3 1 4 ((50, 2) :: (1, 1) :: repeat (1, 2) 83 ++ (3007, 2) :: (1, 1) :: repeat (1, 2) 6030 ++ (8746, 2) :: (1, 1) :: repeat (1, 2) 51689 ++ (263502, 2) :: (1, 1) :: repeat (1, 2) 595550 ++ (233769, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) 1)).
  {
    apply (sTDN [] 3 ((50, 2) :: (1, 1) :: repeat (1, 2) 83 ++ (3007, 2) :: (1, 1) :: repeat (1, 2) 6030 ++ (8746, 2) :: (1, 1) :: repeat (1, 2) 51689 ++ (263502, 2) :: (1, 1) :: repeat (1, 2) 595550 ++ (233769, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) 1).
  }
  (* step 496: sTUP *)
  apply (hsteps_trans _ (HC [] 3 3 2 ((48, 2) :: (1, 1) :: repeat (1, 2) 83 ++ (3007, 2) :: (1, 1) :: repeat (1, 2) 6030 ++ (8746, 2) :: (1, 1) :: repeat (1, 2) 51689 ++ (263502, 2) :: (1, 1) :: repeat (1, 2) 595550 ++ (233769, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) 1)).
  {
    replace ((48, 2) :: (1, 1) :: repeat (1, 2) 83 ++ (3007, 2) :: (1, 1) :: repeat (1, 2) 6030 ++ (8746, 2) :: (1, 1) :: repeat (1, 2) 51689 ++ (263502, 2) :: (1, 1) :: repeat (1, 2) 595550 ++ (233769, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) with ((50 - 2, 2) :: (1, 1) :: repeat (1, 2) 83 ++ (3007, 2) :: (1, 1) :: repeat (1, 2) 6030 ++ (8746, 2) :: (1, 1) :: repeat (1, 2) 51689 ++ (263502, 2) :: (1, 1) :: repeat (1, 2) 595550 ++ (233769, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) by sec_eq.
    apply (sTUP [] 3 4 50 2 ((1, 1) :: repeat (1, 2) 83 ++ (3007, 2) :: (1, 1) :: repeat (1, 2) 6030 ++ (8746, 2) :: (1, 1) :: repeat (1, 2) 51689 ++ (263502, 2) :: (1, 1) :: repeat (1, 2) 595550 ++ (233769, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) 1); closearith.
  }
  (* step 497: DIPGRIND 3 42 *)
  apply (hsteps_trans _ (HC [] 0 3 2 (repeat (1, 2) 3 ++ (42, 2) :: (1, 1) :: repeat (1, 2) 83 ++ (3007, 2) :: (1, 1) :: repeat (1, 2) 6030 ++ (8746, 2) :: (1, 1) :: repeat (1, 2) 51689 ++ (263502, 2) :: (1, 1) :: repeat (1, 2) 595550 ++ (233769, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) 1)).
  {
    apply (DIPGRIND 3 42 [] ((1, 1) :: repeat (1, 2) 83 ++ (3007, 2) :: (1, 1) :: repeat (1, 2) 6030 ++ (8746, 2) :: (1, 1) :: repeat (1, 2) 51689 ++ (263502, 2) :: (1, 1) :: repeat (1, 2) 595550 ++ (233769, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) 1); closearith.
  }
  (* step 498: P PUSHX *)
  apply (hsteps_trans _ (HB [] 1 1 7 (repeat (1, 2) 3 ++ (42, 2) :: (1, 1) :: repeat (1, 2) 83 ++ (3007, 2) :: (1, 1) :: repeat (1, 2) 6030 ++ (8746, 2) :: (1, 1) :: repeat (1, 2) 51689 ++ (263502, 2) :: (1, 1) :: repeat (1, 2) 595550 ++ (233769, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) 1)).
  {
    exact (hsteps_step _ _ _ (hPUSHX (repeat (1, 2) 3 ++ (42, 2) :: (1, 1) :: repeat (1, 2) 83 ++ (3007, 2) :: (1, 1) :: repeat (1, 2) 6030 ++ (8746, 2) :: (1, 1) :: repeat (1, 2) 51689 ++ (263502, 2) :: (1, 1) :: repeat (1, 2) 595550 ++ (233769, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) 1) (hsteps_refl _)).
  }
  (* step 499: M pop12 (3,) *)
  apply (hsteps_trans _ (HB [] 4 1 13 ((42, 2) :: (1, 1) :: repeat (1, 2) 83 ++ (3007, 2) :: (1, 1) :: repeat (1, 2) 6030 ++ (8746, 2) :: (1, 1) :: repeat (1, 2) 51689 ++ (263502, 2) :: (1, 1) :: repeat (1, 2) 595550 ++ (233769, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) 1)).
  {
    apply (pop12 3 [] 1 7 ((42, 2) :: (1, 1) :: repeat (1, 2) 83 ++ (3007, 2) :: (1, 1) :: repeat (1, 2) 6030 ++ (8746, 2) :: (1, 1) :: repeat (1, 2) 51689 ++ (263502, 2) :: (1, 1) :: repeat (1, 2) 595550 ++ (233769, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) 1); closearith.
  }
  (* step 500: sTUP *)
  apply (hsteps_trans _ (HC [] 4 12 2 ((40, 2) :: (1, 1) :: repeat (1, 2) 83 ++ (3007, 2) :: (1, 1) :: repeat (1, 2) 6030 ++ (8746, 2) :: (1, 1) :: repeat (1, 2) 51689 ++ (263502, 2) :: (1, 1) :: repeat (1, 2) 595550 ++ (233769, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) 1)).
  {
    replace ((40, 2) :: (1, 1) :: repeat (1, 2) 83 ++ (3007, 2) :: (1, 1) :: repeat (1, 2) 6030 ++ (8746, 2) :: (1, 1) :: repeat (1, 2) 51689 ++ (263502, 2) :: (1, 1) :: repeat (1, 2) 595550 ++ (233769, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) with ((42 - 2, 2) :: (1, 1) :: repeat (1, 2) 83 ++ (3007, 2) :: (1, 1) :: repeat (1, 2) 6030 ++ (8746, 2) :: (1, 1) :: repeat (1, 2) 51689 ++ (263502, 2) :: (1, 1) :: repeat (1, 2) 595550 ++ (233769, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) by sec_eq.
    apply (sTUP [] 4 13 42 2 ((1, 1) :: repeat (1, 2) 83 ++ (3007, 2) :: (1, 1) :: repeat (1, 2) 6030 ++ (8746, 2) :: (1, 1) :: repeat (1, 2) 51689 ++ (263502, 2) :: (1, 1) :: repeat (1, 2) 595550 ++ (233769, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) 1); closearith.
  }
  (* step 501: P PUSH *)
  apply (hsteps_trans _ (HC [] 3 1 2 ((10, 2) :: (40, 2) :: (1, 1) :: repeat (1, 2) 83 ++ (3007, 2) :: (1, 1) :: repeat (1, 2) 6030 ++ (8746, 2) :: (1, 1) :: repeat (1, 2) 51689 ++ (263502, 2) :: (1, 1) :: repeat (1, 2) 595550 ++ (233769, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) 1)).
  {
    replace ((10, 2) :: (40, 2) :: (1, 1) :: repeat (1, 2) 83 ++ (3007, 2) :: (1, 1) :: repeat (1, 2) 6030 ++ (8746, 2) :: (1, 1) :: repeat (1, 2) 51689 ++ (263502, 2) :: (1, 1) :: repeat (1, 2) 595550 ++ (233769, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) with ((12 - 2, 2) :: (40, 2) :: (1, 1) :: repeat (1, 2) 83 ++ (3007, 2) :: (1, 1) :: repeat (1, 2) 6030 ++ (8746, 2) :: (1, 1) :: repeat (1, 2) 51689 ++ (263502, 2) :: (1, 1) :: repeat (1, 2) 595550 ++ (233769, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) by sec_eq.
    apply (sPUSH [] 3 12 ((40, 2) :: (1, 1) :: repeat (1, 2) 83 ++ (3007, 2) :: (1, 1) :: repeat (1, 2) 6030 ++ (8746, 2) :: (1, 1) :: repeat (1, 2) 51689 ++ (263502, 2) :: (1, 1) :: repeat (1, 2) 595550 ++ (233769, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) 1); closearith.
  }
  (* step 502: P TDN *)
  apply (hsteps_trans _ (HB [] 3 1 4 ((10, 2) :: (40, 2) :: (1, 1) :: repeat (1, 2) 83 ++ (3007, 2) :: (1, 1) :: repeat (1, 2) 6030 ++ (8746, 2) :: (1, 1) :: repeat (1, 2) 51689 ++ (263502, 2) :: (1, 1) :: repeat (1, 2) 595550 ++ (233769, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) 1)).
  {
    apply (sTDN [] 3 ((10, 2) :: (40, 2) :: (1, 1) :: repeat (1, 2) 83 ++ (3007, 2) :: (1, 1) :: repeat (1, 2) 6030 ++ (8746, 2) :: (1, 1) :: repeat (1, 2) 51689 ++ (263502, 2) :: (1, 1) :: repeat (1, 2) 595550 ++ (233769, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) 1).
  }
  (* step 503: sTUP *)
  apply (hsteps_trans _ (HC [] 3 3 2 ((8, 2) :: (40, 2) :: (1, 1) :: repeat (1, 2) 83 ++ (3007, 2) :: (1, 1) :: repeat (1, 2) 6030 ++ (8746, 2) :: (1, 1) :: repeat (1, 2) 51689 ++ (263502, 2) :: (1, 1) :: repeat (1, 2) 595550 ++ (233769, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) 1)).
  {
    replace ((8, 2) :: (40, 2) :: (1, 1) :: repeat (1, 2) 83 ++ (3007, 2) :: (1, 1) :: repeat (1, 2) 6030 ++ (8746, 2) :: (1, 1) :: repeat (1, 2) 51689 ++ (263502, 2) :: (1, 1) :: repeat (1, 2) 595550 ++ (233769, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) with ((10 - 2, 2) :: (40, 2) :: (1, 1) :: repeat (1, 2) 83 ++ (3007, 2) :: (1, 1) :: repeat (1, 2) 6030 ++ (8746, 2) :: (1, 1) :: repeat (1, 2) 51689 ++ (263502, 2) :: (1, 1) :: repeat (1, 2) 595550 ++ (233769, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) by sec_eq.
    apply (sTUP [] 3 4 10 2 ((40, 2) :: (1, 1) :: repeat (1, 2) 83 ++ (3007, 2) :: (1, 1) :: repeat (1, 2) 6030 ++ (8746, 2) :: (1, 1) :: repeat (1, 2) 51689 ++ (263502, 2) :: (1, 1) :: repeat (1, 2) 595550 ++ (233769, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) 1); closearith.
  }
  (* step 504: DIPGRIND 3 2 *)
  apply (hsteps_trans _ (HC [] 0 3 2 (repeat (1, 2) 3 ++ (2, 2) :: (40, 2) :: (1, 1) :: repeat (1, 2) 83 ++ (3007, 2) :: (1, 1) :: repeat (1, 2) 6030 ++ (8746, 2) :: (1, 1) :: repeat (1, 2) 51689 ++ (263502, 2) :: (1, 1) :: repeat (1, 2) 595550 ++ (233769, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) 1)).
  {
    apply (DIPGRIND 3 2 [] ((40, 2) :: (1, 1) :: repeat (1, 2) 83 ++ (3007, 2) :: (1, 1) :: repeat (1, 2) 6030 ++ (8746, 2) :: (1, 1) :: repeat (1, 2) 51689 ++ (263502, 2) :: (1, 1) :: repeat (1, 2) 595550 ++ (233769, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) 1); closearith.
  }
  (* step 505: P PUSHX *)
  apply (hsteps_trans _ (HB [] 1 1 7 (repeat (1, 2) 3 ++ (2, 2) :: (40, 2) :: (1, 1) :: repeat (1, 2) 83 ++ (3007, 2) :: (1, 1) :: repeat (1, 2) 6030 ++ (8746, 2) :: (1, 1) :: repeat (1, 2) 51689 ++ (263502, 2) :: (1, 1) :: repeat (1, 2) 595550 ++ (233769, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) 1)).
  {
    exact (hsteps_step _ _ _ (hPUSHX (repeat (1, 2) 3 ++ (2, 2) :: (40, 2) :: (1, 1) :: repeat (1, 2) 83 ++ (3007, 2) :: (1, 1) :: repeat (1, 2) 6030 ++ (8746, 2) :: (1, 1) :: repeat (1, 2) 51689 ++ (263502, 2) :: (1, 1) :: repeat (1, 2) 595550 ++ (233769, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) 1) (hsteps_refl _)).
  }
  (* step 506: M pop12 (3,) *)
  apply (hsteps_trans _ (HB [] 4 1 13 ((2, 2) :: (40, 2) :: (1, 1) :: repeat (1, 2) 83 ++ (3007, 2) :: (1, 1) :: repeat (1, 2) 6030 ++ (8746, 2) :: (1, 1) :: repeat (1, 2) 51689 ++ (263502, 2) :: (1, 1) :: repeat (1, 2) 595550 ++ (233769, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) 1)).
  {
    apply (pop12 3 [] 1 7 ((2, 2) :: (40, 2) :: (1, 1) :: repeat (1, 2) 83 ++ (3007, 2) :: (1, 1) :: repeat (1, 2) 6030 ++ (8746, 2) :: (1, 1) :: repeat (1, 2) 51689 ++ (263502, 2) :: (1, 1) :: repeat (1, 2) 595550 ++ (233769, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) 1); closearith.
  }
  (* step 507: P TUP2_1 *)
  apply (hsteps_trans _ (HC [5] 13 1 2 ((38, 2) :: (1, 1) :: repeat (1, 2) 83 ++ (3007, 2) :: (1, 1) :: repeat (1, 2) 6030 ++ (8746, 2) :: (1, 1) :: repeat (1, 2) 51689 ++ (263502, 2) :: (1, 1) :: repeat (1, 2) 595550 ++ (233769, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) 1)).
  {
    replace ((38, 2) :: (1, 1) :: repeat (1, 2) 83 ++ (3007, 2) :: (1, 1) :: repeat (1, 2) 6030 ++ (8746, 2) :: (1, 1) :: repeat (1, 2) 51689 ++ (263502, 2) :: (1, 1) :: repeat (1, 2) 595550 ++ (233769, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) with ((40 - 2, 2) :: (1, 1) :: repeat (1, 2) 83 ++ (3007, 2) :: (1, 1) :: repeat (1, 2) 6030 ++ (8746, 2) :: (1, 1) :: repeat (1, 2) 51689 ++ (263502, 2) :: (1, 1) :: repeat (1, 2) 595550 ++ (233769, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) by sec_eq.
    apply (sTUP2_1 [] 4 12 40 ((1, 1) :: repeat (1, 2) 83 ++ (3007, 2) :: (1, 1) :: repeat (1, 2) 6030 ++ (8746, 2) :: (1, 1) :: repeat (1, 2) 51689 ++ (263502, 2) :: (1, 1) :: repeat (1, 2) 595550 ++ (233769, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) 1); closearith.
  }
  (* step 508: P TDN *)
  apply (hsteps_trans _ (HB [5] 13 1 4 ((38, 2) :: (1, 1) :: repeat (1, 2) 83 ++ (3007, 2) :: (1, 1) :: repeat (1, 2) 6030 ++ (8746, 2) :: (1, 1) :: repeat (1, 2) 51689 ++ (263502, 2) :: (1, 1) :: repeat (1, 2) 595550 ++ (233769, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) 1)).
  {
    apply (sTDN [5] 13 ((38, 2) :: (1, 1) :: repeat (1, 2) 83 ++ (3007, 2) :: (1, 1) :: repeat (1, 2) 6030 ++ (8746, 2) :: (1, 1) :: repeat (1, 2) 51689 ++ (263502, 2) :: (1, 1) :: repeat (1, 2) 595550 ++ (233769, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) 1).
  }
  (* step 509: sTUP *)
  apply (hsteps_trans _ (HC [5] 13 3 2 ((36, 2) :: (1, 1) :: repeat (1, 2) 83 ++ (3007, 2) :: (1, 1) :: repeat (1, 2) 6030 ++ (8746, 2) :: (1, 1) :: repeat (1, 2) 51689 ++ (263502, 2) :: (1, 1) :: repeat (1, 2) 595550 ++ (233769, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) 1)).
  {
    replace ((36, 2) :: (1, 1) :: repeat (1, 2) 83 ++ (3007, 2) :: (1, 1) :: repeat (1, 2) 6030 ++ (8746, 2) :: (1, 1) :: repeat (1, 2) 51689 ++ (263502, 2) :: (1, 1) :: repeat (1, 2) 595550 ++ (233769, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) with ((38 - 2, 2) :: (1, 1) :: repeat (1, 2) 83 ++ (3007, 2) :: (1, 1) :: repeat (1, 2) 6030 ++ (8746, 2) :: (1, 1) :: repeat (1, 2) 51689 ++ (263502, 2) :: (1, 1) :: repeat (1, 2) 595550 ++ (233769, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) by sec_eq.
    apply (sTUP [5] 13 4 38 2 ((1, 1) :: repeat (1, 2) 83 ++ (3007, 2) :: (1, 1) :: repeat (1, 2) 6030 ++ (8746, 2) :: (1, 1) :: repeat (1, 2) 51689 ++ (263502, 2) :: (1, 1) :: repeat (1, 2) 595550 ++ (233769, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) 1); closearith.
  }
  (* step 510: DIPGRIND 13 10 *)
  apply (hsteps_trans _ (HC [5] 0 3 2 (repeat (1, 2) 13 ++ (10, 2) :: (1, 1) :: repeat (1, 2) 83 ++ (3007, 2) :: (1, 1) :: repeat (1, 2) 6030 ++ (8746, 2) :: (1, 1) :: repeat (1, 2) 51689 ++ (263502, 2) :: (1, 1) :: repeat (1, 2) 595550 ++ (233769, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) 1)).
  {
    apply (DIPGRIND 13 10 [5] ((1, 1) :: repeat (1, 2) 83 ++ (3007, 2) :: (1, 1) :: repeat (1, 2) 6030 ++ (8746, 2) :: (1, 1) :: repeat (1, 2) 51689 ++ (263502, 2) :: (1, 1) :: repeat (1, 2) 595550 ++ (233769, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) 1); closearith.
  }
  (* step 511: P PX2Bgen *)
  apply (hsteps_trans _ (HB [0] 3 1 2 (repeat (1, 2) 1 ++ (1, 1) :: repeat (1, 2) 15 ++ (10, 2) :: (1, 1) :: repeat (1, 2) 83 ++ (3007, 2) :: (1, 1) :: repeat (1, 2) 6030 ++ (8746, 2) :: (1, 1) :: repeat (1, 2) 51689 ++ (263502, 2) :: (1, 1) :: repeat (1, 2) 595550 ++ (233769, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) 1)).
  {
    exact (hsteps_step _ _ _ (hPX2Bgen 0 (repeat (1, 2) 13 ++ (10, 2) :: (1, 1) :: repeat (1, 2) 83 ++ (3007, 2) :: (1, 1) :: repeat (1, 2) 6030 ++ (8746, 2) :: (1, 1) :: repeat (1, 2) 51689 ++ (263502, 2) :: (1, 1) :: repeat (1, 2) 595550 ++ (233769, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) 1) (hsteps_refl _)).
  }
  (* step 512: M pop12 (1,) *)
  apply (hsteps_trans _ (HB [0] 4 1 4 ((1, 1) :: repeat (1, 2) 15 ++ (10, 2) :: (1, 1) :: repeat (1, 2) 83 ++ (3007, 2) :: (1, 1) :: repeat (1, 2) 6030 ++ (8746, 2) :: (1, 1) :: repeat (1, 2) 51689 ++ (263502, 2) :: (1, 1) :: repeat (1, 2) 595550 ++ (233769, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) 1)).
  {
    apply (pop12 1 [0] 3 2 ((1, 1) :: repeat (1, 2) 15 ++ (10, 2) :: (1, 1) :: repeat (1, 2) 83 ++ (3007, 2) :: (1, 1) :: repeat (1, 2) 6030 ++ (8746, 2) :: (1, 1) :: repeat (1, 2) 51689 ++ (263502, 2) :: (1, 1) :: repeat (1, 2) 595550 ++ (233769, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) 1); closearith.
  }
  (* step 513: P POP *)
  apply (hsteps_trans _ (HB [0] 5 1 5 (repeat (1, 2) 15 ++ (10, 2) :: (1, 1) :: repeat (1, 2) 83 ++ (3007, 2) :: (1, 1) :: repeat (1, 2) 6030 ++ (8746, 2) :: (1, 1) :: repeat (1, 2) 51689 ++ (263502, 2) :: (1, 1) :: repeat (1, 2) 595550 ++ (233769, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) 1)).
  {
    apply (sPOP1 [0] 4 4 (repeat (1, 2) 15 ++ (10, 2) :: (1, 1) :: repeat (1, 2) 83 ++ (3007, 2) :: (1, 1) :: repeat (1, 2) 6030 ++ (8746, 2) :: (1, 1) :: repeat (1, 2) 51689 ++ (263502, 2) :: (1, 1) :: repeat (1, 2) 595550 ++ (233769, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) 1); closearith.
  }
  (* step 514: M pop12 (15,) *)
  apply (hsteps_trans _ (HB [0] 20 1 35 ((10, 2) :: (1, 1) :: repeat (1, 2) 83 ++ (3007, 2) :: (1, 1) :: repeat (1, 2) 6030 ++ (8746, 2) :: (1, 1) :: repeat (1, 2) 51689 ++ (263502, 2) :: (1, 1) :: repeat (1, 2) 595550 ++ (233769, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) 1)).
  {
    apply (pop12 15 [0] 5 5 ((10, 2) :: (1, 1) :: repeat (1, 2) 83 ++ (3007, 2) :: (1, 1) :: repeat (1, 2) 6030 ++ (8746, 2) :: (1, 1) :: repeat (1, 2) 51689 ++ (263502, 2) :: (1, 1) :: repeat (1, 2) 595550 ++ (233769, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) 1); closearith.
  }
  (* step 515: sTUP *)
  apply (hsteps_trans _ (HC [0] 20 34 2 ((8, 2) :: (1, 1) :: repeat (1, 2) 83 ++ (3007, 2) :: (1, 1) :: repeat (1, 2) 6030 ++ (8746, 2) :: (1, 1) :: repeat (1, 2) 51689 ++ (263502, 2) :: (1, 1) :: repeat (1, 2) 595550 ++ (233769, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) 1)).
  {
    replace ((8, 2) :: (1, 1) :: repeat (1, 2) 83 ++ (3007, 2) :: (1, 1) :: repeat (1, 2) 6030 ++ (8746, 2) :: (1, 1) :: repeat (1, 2) 51689 ++ (263502, 2) :: (1, 1) :: repeat (1, 2) 595550 ++ (233769, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) with ((10 - 2, 2) :: (1, 1) :: repeat (1, 2) 83 ++ (3007, 2) :: (1, 1) :: repeat (1, 2) 6030 ++ (8746, 2) :: (1, 1) :: repeat (1, 2) 51689 ++ (263502, 2) :: (1, 1) :: repeat (1, 2) 595550 ++ (233769, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) by sec_eq.
    apply (sTUP [0] 20 35 10 2 ((1, 1) :: repeat (1, 2) 83 ++ (3007, 2) :: (1, 1) :: repeat (1, 2) 6030 ++ (8746, 2) :: (1, 1) :: repeat (1, 2) 51689 ++ (263502, 2) :: (1, 1) :: repeat (1, 2) 595550 ++ (233769, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) 1); closearith.
  }
  (* step 516: hGRIND_even 15 *)
  apply (hsteps_trans _ (HB [0] 19 1 34 ((2, 2) :: (8, 2) :: (1, 1) :: repeat (1, 2) 83 ++ (3007, 2) :: (1, 1) :: repeat (1, 2) 6030 ++ (8746, 2) :: (1, 1) :: repeat (1, 2) 51689 ++ (263502, 2) :: (1, 1) :: repeat (1, 2) 595550 ++ (233769, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) 1)).
  {
    apply (hGRIND_even 15 [0] 19 ((8, 2) :: (1, 1) :: repeat (1, 2) 83 ++ (3007, 2) :: (1, 1) :: repeat (1, 2) 6030 ++ (8746, 2) :: (1, 1) :: repeat (1, 2) 51689 ++ (263502, 2) :: (1, 1) :: repeat (1, 2) 595550 ++ (233769, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) 1); closearith.
  }
  (* step 517: P TUP2_1 *)
  replace ((6, 2) :: (1, 1) :: repeat (1, 2) 83 ++ (3007, 2) :: (1, 1) :: repeat (1, 2) 6030 ++ (8746, 2) :: (1, 1) :: repeat (1, 2) 51689 ++ (263502, 2) :: (1, 1) :: repeat (1, 2) 595550 ++ (233769, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) with ((8 - 2, 2) :: (1, 1) :: repeat (1, 2) 83 ++ (3007, 2) :: (1, 1) :: repeat (1, 2) 6030 ++ (8746, 2) :: (1, 1) :: repeat (1, 2) 51689 ++ (263502, 2) :: (1, 1) :: repeat (1, 2) 595550 ++ (233769, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) by sec_eq.
  apply (sTUP2_1 [0] 19 33 8 ((1, 1) :: repeat (1, 2) 83 ++ (3007, 2) :: (1, 1) :: repeat (1, 2) 6030 ++ (8746, 2) :: (1, 1) :: repeat (1, 2) 51689 ++ (263502, 2) :: (1, 1) :: repeat (1, 2) 595550 ++ (233769, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) 1); closearith.
Qed.

(* CASCADE56l: steps 518-573 of the CASCADE56 chain. *)
Lemma CASCADE56l : forall w,
  hsteps (HC [20; 0] 34 1 2 ((6, 2) :: (1, 1) :: repeat (1, 2) 83 ++ (3007, 2) :: (1, 1) :: repeat (1, 2) 6030 ++ (8746, 2) :: (1, 1) :: repeat (1, 2) 51689 ++ (263502, 2) :: (1, 1) :: repeat (1, 2) 595550 ++ (233769, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) 1)
         (HB [5] 12 1 4 ((36, 2) :: (1, 1) :: repeat (1, 2) 73 ++ (41, 2) :: (1, 1) :: repeat (1, 2) 344 ++ (1975, 2) :: (1, 1) :: repeat (1, 2) 6030 ++ (8746, 2) :: (1, 1) :: repeat (1, 2) 51689 ++ (263502, 2) :: (1, 1) :: repeat (1, 2) 595550 ++ (233769, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) 1).
Proof.
  intro w.
  (* step 518: P TDN *)
  apply (hsteps_trans _ (HB [20; 0] 34 1 4 ((6, 2) :: (1, 1) :: repeat (1, 2) 83 ++ (3007, 2) :: (1, 1) :: repeat (1, 2) 6030 ++ (8746, 2) :: (1, 1) :: repeat (1, 2) 51689 ++ (263502, 2) :: (1, 1) :: repeat (1, 2) 595550 ++ (233769, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) 1)).
  {
    apply (sTDN [20; 0] 34 ((6, 2) :: (1, 1) :: repeat (1, 2) 83 ++ (3007, 2) :: (1, 1) :: repeat (1, 2) 6030 ++ (8746, 2) :: (1, 1) :: repeat (1, 2) 51689 ++ (263502, 2) :: (1, 1) :: repeat (1, 2) 595550 ++ (233769, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) 1).
  }
  (* step 519: sTUP *)
  apply (hsteps_trans _ (HC [20; 0] 34 3 2 ((4, 2) :: (1, 1) :: repeat (1, 2) 83 ++ (3007, 2) :: (1, 1) :: repeat (1, 2) 6030 ++ (8746, 2) :: (1, 1) :: repeat (1, 2) 51689 ++ (263502, 2) :: (1, 1) :: repeat (1, 2) 595550 ++ (233769, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) 1)).
  {
    replace ((4, 2) :: (1, 1) :: repeat (1, 2) 83 ++ (3007, 2) :: (1, 1) :: repeat (1, 2) 6030 ++ (8746, 2) :: (1, 1) :: repeat (1, 2) 51689 ++ (263502, 2) :: (1, 1) :: repeat (1, 2) 595550 ++ (233769, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) with ((6 - 2, 2) :: (1, 1) :: repeat (1, 2) 83 ++ (3007, 2) :: (1, 1) :: repeat (1, 2) 6030 ++ (8746, 2) :: (1, 1) :: repeat (1, 2) 51689 ++ (263502, 2) :: (1, 1) :: repeat (1, 2) 595550 ++ (233769, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) by sec_eq.
    apply (sTUP [20; 0] 34 4 6 2 ((1, 1) :: repeat (1, 2) 83 ++ (3007, 2) :: (1, 1) :: repeat (1, 2) 6030 ++ (8746, 2) :: (1, 1) :: repeat (1, 2) 51689 ++ (263502, 2) :: (1, 1) :: repeat (1, 2) 595550 ++ (233769, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) 1); closearith.
  }
  (* step 520: CLEANG_even 1 *)
  apply (hsteps_trans _ (HB [20; 0] 34 1 8 ((2, 2) :: (1, 1) :: repeat (1, 2) 83 ++ (3007, 2) :: (1, 1) :: repeat (1, 2) 6030 ++ (8746, 2) :: (1, 1) :: repeat (1, 2) 51689 ++ (263502, 2) :: (1, 1) :: repeat (1, 2) 595550 ++ (233769, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) 1)).
  {
    apply (CLEANG_even 1 [20; 0] 34 ((1, 1) :: repeat (1, 2) 83 ++ (3007, 2) :: (1, 1) :: repeat (1, 2) 6030 ++ (8746, 2) :: (1, 1) :: repeat (1, 2) 51689 ++ (263502, 2) :: (1, 1) :: repeat (1, 2) 595550 ++ (233769, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) 1); closearith.
  }
  (* step 521: P TRANS2_1 *)
  apply (hsteps_trans _ (HB [35; 20; 0] 9 1 3 (repeat (1, 2) 83 ++ (3007, 2) :: (1, 1) :: repeat (1, 2) 6030 ++ (8746, 2) :: (1, 1) :: repeat (1, 2) 51689 ++ (263502, 2) :: (1, 1) :: repeat (1, 2) 595550 ++ (233769, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) 1)).
  {
    apply (sTRANS2_1 [20; 0] 34 7 1 (repeat (1, 2) 83 ++ (3007, 2) :: (1, 1) :: repeat (1, 2) 6030 ++ (8746, 2) :: (1, 1) :: repeat (1, 2) 51689 ++ (263502, 2) :: (1, 1) :: repeat (1, 2) 595550 ++ (233769, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) 1); closearith.
  }
  (* step 522: M pop12 (83,) *)
  apply (hsteps_trans _ (HB [35; 20; 0] 92 1 169 ((3007, 2) :: (1, 1) :: repeat (1, 2) 6030 ++ (8746, 2) :: (1, 1) :: repeat (1, 2) 51689 ++ (263502, 2) :: (1, 1) :: repeat (1, 2) 595550 ++ (233769, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) 1)).
  {
    apply (pop12 83 [35; 20; 0] 9 3 ((3007, 2) :: (1, 1) :: repeat (1, 2) 6030 ++ (8746, 2) :: (1, 1) :: repeat (1, 2) 51689 ++ (263502, 2) :: (1, 1) :: repeat (1, 2) 595550 ++ (233769, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) 1); closearith.
  }
  (* step 523: sTUP *)
  apply (hsteps_trans _ (HC [35; 20; 0] 92 168 2 ((3005, 2) :: (1, 1) :: repeat (1, 2) 6030 ++ (8746, 2) :: (1, 1) :: repeat (1, 2) 51689 ++ (263502, 2) :: (1, 1) :: repeat (1, 2) 595550 ++ (233769, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) 1)).
  {
    replace ((3005, 2) :: (1, 1) :: repeat (1, 2) 6030 ++ (8746, 2) :: (1, 1) :: repeat (1, 2) 51689 ++ (263502, 2) :: (1, 1) :: repeat (1, 2) 595550 ++ (233769, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) with ((3007 - 2, 2) :: (1, 1) :: repeat (1, 2) 6030 ++ (8746, 2) :: (1, 1) :: repeat (1, 2) 51689 ++ (263502, 2) :: (1, 1) :: repeat (1, 2) 595550 ++ (233769, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) by sec_eq.
    apply (sTUP [35; 20; 0] 92 169 3007 2 ((1, 1) :: repeat (1, 2) 6030 ++ (8746, 2) :: (1, 1) :: repeat (1, 2) 51689 ++ (263502, 2) :: (1, 1) :: repeat (1, 2) 595550 ++ (233769, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) 1); closearith.
  }
  (* step 524: hGRIND_even 82 *)
  apply (hsteps_trans _ (HB [35; 20; 0] 91 1 168 ((2, 2) :: (3005, 2) :: (1, 1) :: repeat (1, 2) 6030 ++ (8746, 2) :: (1, 1) :: repeat (1, 2) 51689 ++ (263502, 2) :: (1, 1) :: repeat (1, 2) 595550 ++ (233769, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) 1)).
  {
    apply (hGRIND_even 82 [35; 20; 0] 91 ((3005, 2) :: (1, 1) :: repeat (1, 2) 6030 ++ (8746, 2) :: (1, 1) :: repeat (1, 2) 51689 ++ (263502, 2) :: (1, 1) :: repeat (1, 2) 595550 ++ (233769, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) 1); closearith.
  }
  (* step 525: P TUP2_1 *)
  apply (hsteps_trans _ (HC [92; 35; 20; 0] 168 1 2 ((3003, 2) :: (1, 1) :: repeat (1, 2) 6030 ++ (8746, 2) :: (1, 1) :: repeat (1, 2) 51689 ++ (263502, 2) :: (1, 1) :: repeat (1, 2) 595550 ++ (233769, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) 1)).
  {
    replace ((3003, 2) :: (1, 1) :: repeat (1, 2) 6030 ++ (8746, 2) :: (1, 1) :: repeat (1, 2) 51689 ++ (263502, 2) :: (1, 1) :: repeat (1, 2) 595550 ++ (233769, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) with ((3005 - 2, 2) :: (1, 1) :: repeat (1, 2) 6030 ++ (8746, 2) :: (1, 1) :: repeat (1, 2) 51689 ++ (263502, 2) :: (1, 1) :: repeat (1, 2) 595550 ++ (233769, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) by sec_eq.
    apply (sTUP2_1 [35; 20; 0] 91 167 3005 ((1, 1) :: repeat (1, 2) 6030 ++ (8746, 2) :: (1, 1) :: repeat (1, 2) 51689 ++ (263502, 2) :: (1, 1) :: repeat (1, 2) 595550 ++ (233769, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) 1); closearith.
  }
  (* step 526: P TDN *)
  apply (hsteps_trans _ (HB [92; 35; 20; 0] 168 1 4 ((3003, 2) :: (1, 1) :: repeat (1, 2) 6030 ++ (8746, 2) :: (1, 1) :: repeat (1, 2) 51689 ++ (263502, 2) :: (1, 1) :: repeat (1, 2) 595550 ++ (233769, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) 1)).
  {
    apply (sTDN [92; 35; 20; 0] 168 ((3003, 2) :: (1, 1) :: repeat (1, 2) 6030 ++ (8746, 2) :: (1, 1) :: repeat (1, 2) 51689 ++ (263502, 2) :: (1, 1) :: repeat (1, 2) 595550 ++ (233769, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) 1).
  }
  (* step 527: sTUP *)
  apply (hsteps_trans _ (HC [92; 35; 20; 0] 168 3 2 ((3001, 2) :: (1, 1) :: repeat (1, 2) 6030 ++ (8746, 2) :: (1, 1) :: repeat (1, 2) 51689 ++ (263502, 2) :: (1, 1) :: repeat (1, 2) 595550 ++ (233769, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) 1)).
  {
    replace ((3001, 2) :: (1, 1) :: repeat (1, 2) 6030 ++ (8746, 2) :: (1, 1) :: repeat (1, 2) 51689 ++ (263502, 2) :: (1, 1) :: repeat (1, 2) 595550 ++ (233769, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) with ((3003 - 2, 2) :: (1, 1) :: repeat (1, 2) 6030 ++ (8746, 2) :: (1, 1) :: repeat (1, 2) 51689 ++ (263502, 2) :: (1, 1) :: repeat (1, 2) 595550 ++ (233769, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) by sec_eq.
    apply (sTUP [92; 35; 20; 0] 168 4 3003 2 ((1, 1) :: repeat (1, 2) 6030 ++ (8746, 2) :: (1, 1) :: repeat (1, 2) 51689 ++ (263502, 2) :: (1, 1) :: repeat (1, 2) 595550 ++ (233769, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) 1); closearith.
  }
  (* step 528: DIPGRIND 168 2665 *)
  apply (hsteps_trans _ (HC [92; 35; 20; 0] 0 3 2 (repeat (1, 2) 168 ++ (2665, 2) :: (1, 1) :: repeat (1, 2) 6030 ++ (8746, 2) :: (1, 1) :: repeat (1, 2) 51689 ++ (263502, 2) :: (1, 1) :: repeat (1, 2) 595550 ++ (233769, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) 1)).
  {
    apply (DIPGRIND 168 2665 [92; 35; 20; 0] ((1, 1) :: repeat (1, 2) 6030 ++ (8746, 2) :: (1, 1) :: repeat (1, 2) 51689 ++ (263502, 2) :: (1, 1) :: repeat (1, 2) 595550 ++ (233769, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) 1); closearith.
  }
  (* step 529: P PX2A *)
  apply (hsteps_trans _ (HC [20; 0] 34 90 2 ((1, 1) :: repeat (1, 2) 170 ++ (2665, 2) :: (1, 1) :: repeat (1, 2) 6030 ++ (8746, 2) :: (1, 1) :: repeat (1, 2) 51689 ++ (263502, 2) :: (1, 1) :: repeat (1, 2) 595550 ++ (233769, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) 1)).
  {
    exact (hsteps_step _ _ _ (hPX2A 89 34 [20; 0] (repeat (1, 2) 168 ++ (2665, 2) :: (1, 1) :: repeat (1, 2) 6030 ++ (8746, 2) :: (1, 1) :: repeat (1, 2) 51689 ++ (263502, 2) :: (1, 1) :: repeat (1, 2) 595550 ++ (233769, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) 1) (hsteps_refl _)).
  }
  (* step 530: P PUSH *)
  apply (hsteps_trans _ (HC [20; 0] 33 1 2 ((88, 2) :: (1, 1) :: repeat (1, 2) 170 ++ (2665, 2) :: (1, 1) :: repeat (1, 2) 6030 ++ (8746, 2) :: (1, 1) :: repeat (1, 2) 51689 ++ (263502, 2) :: (1, 1) :: repeat (1, 2) 595550 ++ (233769, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) 1)).
  {
    replace ((88, 2) :: (1, 1) :: repeat (1, 2) 170 ++ (2665, 2) :: (1, 1) :: repeat (1, 2) 6030 ++ (8746, 2) :: (1, 1) :: repeat (1, 2) 51689 ++ (263502, 2) :: (1, 1) :: repeat (1, 2) 595550 ++ (233769, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) with ((90 - 2, 2) :: (1, 1) :: repeat (1, 2) 170 ++ (2665, 2) :: (1, 1) :: repeat (1, 2) 6030 ++ (8746, 2) :: (1, 1) :: repeat (1, 2) 51689 ++ (263502, 2) :: (1, 1) :: repeat (1, 2) 595550 ++ (233769, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) by sec_eq.
    apply (sPUSH [20; 0] 33 90 ((1, 1) :: repeat (1, 2) 170 ++ (2665, 2) :: (1, 1) :: repeat (1, 2) 6030 ++ (8746, 2) :: (1, 1) :: repeat (1, 2) 51689 ++ (263502, 2) :: (1, 1) :: repeat (1, 2) 595550 ++ (233769, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) 1); closearith.
  }
  (* step 531: P TDN *)
  apply (hsteps_trans _ (HB [20; 0] 33 1 4 ((88, 2) :: (1, 1) :: repeat (1, 2) 170 ++ (2665, 2) :: (1, 1) :: repeat (1, 2) 6030 ++ (8746, 2) :: (1, 1) :: repeat (1, 2) 51689 ++ (263502, 2) :: (1, 1) :: repeat (1, 2) 595550 ++ (233769, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) 1)).
  {
    apply (sTDN [20; 0] 33 ((88, 2) :: (1, 1) :: repeat (1, 2) 170 ++ (2665, 2) :: (1, 1) :: repeat (1, 2) 6030 ++ (8746, 2) :: (1, 1) :: repeat (1, 2) 51689 ++ (263502, 2) :: (1, 1) :: repeat (1, 2) 595550 ++ (233769, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) 1).
  }
  (* step 532: sTUP *)
  apply (hsteps_trans _ (HC [20; 0] 33 3 2 ((86, 2) :: (1, 1) :: repeat (1, 2) 170 ++ (2665, 2) :: (1, 1) :: repeat (1, 2) 6030 ++ (8746, 2) :: (1, 1) :: repeat (1, 2) 51689 ++ (263502, 2) :: (1, 1) :: repeat (1, 2) 595550 ++ (233769, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) 1)).
  {
    replace ((86, 2) :: (1, 1) :: repeat (1, 2) 170 ++ (2665, 2) :: (1, 1) :: repeat (1, 2) 6030 ++ (8746, 2) :: (1, 1) :: repeat (1, 2) 51689 ++ (263502, 2) :: (1, 1) :: repeat (1, 2) 595550 ++ (233769, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) with ((88 - 2, 2) :: (1, 1) :: repeat (1, 2) 170 ++ (2665, 2) :: (1, 1) :: repeat (1, 2) 6030 ++ (8746, 2) :: (1, 1) :: repeat (1, 2) 51689 ++ (263502, 2) :: (1, 1) :: repeat (1, 2) 595550 ++ (233769, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) by sec_eq.
    apply (sTUP [20; 0] 33 4 88 2 ((1, 1) :: repeat (1, 2) 170 ++ (2665, 2) :: (1, 1) :: repeat (1, 2) 6030 ++ (8746, 2) :: (1, 1) :: repeat (1, 2) 51689 ++ (263502, 2) :: (1, 1) :: repeat (1, 2) 595550 ++ (233769, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) 1); closearith.
  }
  (* step 533: DIPGRIND 33 20 *)
  apply (hsteps_trans _ (HC [20; 0] 0 3 2 (repeat (1, 2) 33 ++ (20, 2) :: (1, 1) :: repeat (1, 2) 170 ++ (2665, 2) :: (1, 1) :: repeat (1, 2) 6030 ++ (8746, 2) :: (1, 1) :: repeat (1, 2) 51689 ++ (263502, 2) :: (1, 1) :: repeat (1, 2) 595550 ++ (233769, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) 1)).
  {
    apply (DIPGRIND 33 20 [20; 0] ((1, 1) :: repeat (1, 2) 170 ++ (2665, 2) :: (1, 1) :: repeat (1, 2) 6030 ++ (8746, 2) :: (1, 1) :: repeat (1, 2) 51689 ++ (263502, 2) :: (1, 1) :: repeat (1, 2) 595550 ++ (233769, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) 1); closearith.
  }
  (* step 534: P PX2A0 *)
  apply (hsteps_trans _ (HB [0] 3 1 2 ((16, 2) :: (1, 1) :: repeat (1, 2) 35 ++ (20, 2) :: (1, 1) :: repeat (1, 2) 170 ++ (2665, 2) :: (1, 1) :: repeat (1, 2) 6030 ++ (8746, 2) :: (1, 1) :: repeat (1, 2) 51689 ++ (263502, 2) :: (1, 1) :: repeat (1, 2) 595550 ++ (233769, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) 1)).
  {
    exact (hsteps_step _ _ _ (hPX2A0 15 (repeat (1, 2) 33 ++ (20, 2) :: (1, 1) :: repeat (1, 2) 170 ++ (2665, 2) :: (1, 1) :: repeat (1, 2) 6030 ++ (8746, 2) :: (1, 1) :: repeat (1, 2) 51689 ++ (263502, 2) :: (1, 1) :: repeat (1, 2) 595550 ++ (233769, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) 1) (hsteps_refl _)).
  }
  (* step 535: sTUP *)
  apply (hsteps_trans _ (HC [0] 3 1 2 ((14, 2) :: (1, 1) :: repeat (1, 2) 35 ++ (20, 2) :: (1, 1) :: repeat (1, 2) 170 ++ (2665, 2) :: (1, 1) :: repeat (1, 2) 6030 ++ (8746, 2) :: (1, 1) :: repeat (1, 2) 51689 ++ (263502, 2) :: (1, 1) :: repeat (1, 2) 595550 ++ (233769, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) 1)).
  {
    replace ((14, 2) :: (1, 1) :: repeat (1, 2) 35 ++ (20, 2) :: (1, 1) :: repeat (1, 2) 170 ++ (2665, 2) :: (1, 1) :: repeat (1, 2) 6030 ++ (8746, 2) :: (1, 1) :: repeat (1, 2) 51689 ++ (263502, 2) :: (1, 1) :: repeat (1, 2) 595550 ++ (233769, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) with ((16 - 2, 2) :: (1, 1) :: repeat (1, 2) 35 ++ (20, 2) :: (1, 1) :: repeat (1, 2) 170 ++ (2665, 2) :: (1, 1) :: repeat (1, 2) 6030 ++ (8746, 2) :: (1, 1) :: repeat (1, 2) 51689 ++ (263502, 2) :: (1, 1) :: repeat (1, 2) 595550 ++ (233769, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) by sec_eq.
    apply (sTUP [0] 3 2 16 2 ((1, 1) :: repeat (1, 2) 35 ++ (20, 2) :: (1, 1) :: repeat (1, 2) 170 ++ (2665, 2) :: (1, 1) :: repeat (1, 2) 6030 ++ (8746, 2) :: (1, 1) :: repeat (1, 2) 51689 ++ (263502, 2) :: (1, 1) :: repeat (1, 2) 595550 ++ (233769, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) 1); closearith.
  }
  (* step 536: P TDN *)
  apply (hsteps_trans _ (HB [0] 3 1 4 ((14, 2) :: (1, 1) :: repeat (1, 2) 35 ++ (20, 2) :: (1, 1) :: repeat (1, 2) 170 ++ (2665, 2) :: (1, 1) :: repeat (1, 2) 6030 ++ (8746, 2) :: (1, 1) :: repeat (1, 2) 51689 ++ (263502, 2) :: (1, 1) :: repeat (1, 2) 595550 ++ (233769, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) 1)).
  {
    apply (sTDN [0] 3 ((14, 2) :: (1, 1) :: repeat (1, 2) 35 ++ (20, 2) :: (1, 1) :: repeat (1, 2) 170 ++ (2665, 2) :: (1, 1) :: repeat (1, 2) 6030 ++ (8746, 2) :: (1, 1) :: repeat (1, 2) 51689 ++ (263502, 2) :: (1, 1) :: repeat (1, 2) 595550 ++ (233769, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) 1).
  }
  (* step 537: sTUP *)
  apply (hsteps_trans _ (HC [0] 3 3 2 ((12, 2) :: (1, 1) :: repeat (1, 2) 35 ++ (20, 2) :: (1, 1) :: repeat (1, 2) 170 ++ (2665, 2) :: (1, 1) :: repeat (1, 2) 6030 ++ (8746, 2) :: (1, 1) :: repeat (1, 2) 51689 ++ (263502, 2) :: (1, 1) :: repeat (1, 2) 595550 ++ (233769, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) 1)).
  {
    replace ((12, 2) :: (1, 1) :: repeat (1, 2) 35 ++ (20, 2) :: (1, 1) :: repeat (1, 2) 170 ++ (2665, 2) :: (1, 1) :: repeat (1, 2) 6030 ++ (8746, 2) :: (1, 1) :: repeat (1, 2) 51689 ++ (263502, 2) :: (1, 1) :: repeat (1, 2) 595550 ++ (233769, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) with ((14 - 2, 2) :: (1, 1) :: repeat (1, 2) 35 ++ (20, 2) :: (1, 1) :: repeat (1, 2) 170 ++ (2665, 2) :: (1, 1) :: repeat (1, 2) 6030 ++ (8746, 2) :: (1, 1) :: repeat (1, 2) 51689 ++ (263502, 2) :: (1, 1) :: repeat (1, 2) 595550 ++ (233769, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) by sec_eq.
    apply (sTUP [0] 3 4 14 2 ((1, 1) :: repeat (1, 2) 35 ++ (20, 2) :: (1, 1) :: repeat (1, 2) 170 ++ (2665, 2) :: (1, 1) :: repeat (1, 2) 6030 ++ (8746, 2) :: (1, 1) :: repeat (1, 2) 51689 ++ (263502, 2) :: (1, 1) :: repeat (1, 2) 595550 ++ (233769, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) 1); closearith.
  }
  (* step 538: DIPGRIND 3 6 *)
  apply (hsteps_trans _ (HC [0] 0 3 2 (repeat (1, 2) 3 ++ (6, 2) :: (1, 1) :: repeat (1, 2) 35 ++ (20, 2) :: (1, 1) :: repeat (1, 2) 170 ++ (2665, 2) :: (1, 1) :: repeat (1, 2) 6030 ++ (8746, 2) :: (1, 1) :: repeat (1, 2) 51689 ++ (263502, 2) :: (1, 1) :: repeat (1, 2) 595550 ++ (233769, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) 1)).
  {
    apply (DIPGRIND 3 6 [0] ((1, 1) :: repeat (1, 2) 35 ++ (20, 2) :: (1, 1) :: repeat (1, 2) 170 ++ (2665, 2) :: (1, 1) :: repeat (1, 2) 6030 ++ (8746, 2) :: (1, 1) :: repeat (1, 2) 51689 ++ (263502, 2) :: (1, 1) :: repeat (1, 2) 595550 ++ (233769, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) 1); closearith.
  }
  (* step 539: P PX2B0 *)
  apply (hsteps_trans _ (HB [] 0 1 5 (repeat (1, 2) 4 ++ (6, 2) :: (1, 1) :: repeat (1, 2) 35 ++ (20, 2) :: (1, 1) :: repeat (1, 2) 170 ++ (2665, 2) :: (1, 1) :: repeat (1, 2) 6030 ++ (8746, 2) :: (1, 1) :: repeat (1, 2) 51689 ++ (263502, 2) :: (1, 1) :: repeat (1, 2) 595550 ++ (233769, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) 1)).
  {
    exact (hsteps_step _ _ _ (hPX2B0 (repeat (1, 2) 3 ++ (6, 2) :: (1, 1) :: repeat (1, 2) 35 ++ (20, 2) :: (1, 1) :: repeat (1, 2) 170 ++ (2665, 2) :: (1, 1) :: repeat (1, 2) 6030 ++ (8746, 2) :: (1, 1) :: repeat (1, 2) 51689 ++ (263502, 2) :: (1, 1) :: repeat (1, 2) 595550 ++ (233769, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) 1) (hsteps_refl _)).
  }
  (* step 540: M pop12 (4,) *)
  apply (hsteps_trans _ (HB [] 4 1 13 ((6, 2) :: (1, 1) :: repeat (1, 2) 35 ++ (20, 2) :: (1, 1) :: repeat (1, 2) 170 ++ (2665, 2) :: (1, 1) :: repeat (1, 2) 6030 ++ (8746, 2) :: (1, 1) :: repeat (1, 2) 51689 ++ (263502, 2) :: (1, 1) :: repeat (1, 2) 595550 ++ (233769, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) 1)).
  {
    apply (pop12 4 [] 0 5 ((6, 2) :: (1, 1) :: repeat (1, 2) 35 ++ (20, 2) :: (1, 1) :: repeat (1, 2) 170 ++ (2665, 2) :: (1, 1) :: repeat (1, 2) 6030 ++ (8746, 2) :: (1, 1) :: repeat (1, 2) 51689 ++ (263502, 2) :: (1, 1) :: repeat (1, 2) 595550 ++ (233769, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) 1); closearith.
  }
  (* step 541: sTUP *)
  apply (hsteps_trans _ (HC [] 4 12 2 ((4, 2) :: (1, 1) :: repeat (1, 2) 35 ++ (20, 2) :: (1, 1) :: repeat (1, 2) 170 ++ (2665, 2) :: (1, 1) :: repeat (1, 2) 6030 ++ (8746, 2) :: (1, 1) :: repeat (1, 2) 51689 ++ (263502, 2) :: (1, 1) :: repeat (1, 2) 595550 ++ (233769, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) 1)).
  {
    replace ((4, 2) :: (1, 1) :: repeat (1, 2) 35 ++ (20, 2) :: (1, 1) :: repeat (1, 2) 170 ++ (2665, 2) :: (1, 1) :: repeat (1, 2) 6030 ++ (8746, 2) :: (1, 1) :: repeat (1, 2) 51689 ++ (263502, 2) :: (1, 1) :: repeat (1, 2) 595550 ++ (233769, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) with ((6 - 2, 2) :: (1, 1) :: repeat (1, 2) 35 ++ (20, 2) :: (1, 1) :: repeat (1, 2) 170 ++ (2665, 2) :: (1, 1) :: repeat (1, 2) 6030 ++ (8746, 2) :: (1, 1) :: repeat (1, 2) 51689 ++ (263502, 2) :: (1, 1) :: repeat (1, 2) 595550 ++ (233769, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) by sec_eq.
    apply (sTUP [] 4 13 6 2 ((1, 1) :: repeat (1, 2) 35 ++ (20, 2) :: (1, 1) :: repeat (1, 2) 170 ++ (2665, 2) :: (1, 1) :: repeat (1, 2) 6030 ++ (8746, 2) :: (1, 1) :: repeat (1, 2) 51689 ++ (263502, 2) :: (1, 1) :: repeat (1, 2) 595550 ++ (233769, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) 1); closearith.
  }
  (* step 542: P PUSH *)
  apply (hsteps_trans _ (HC [] 3 1 2 ((10, 2) :: (4, 2) :: (1, 1) :: repeat (1, 2) 35 ++ (20, 2) :: (1, 1) :: repeat (1, 2) 170 ++ (2665, 2) :: (1, 1) :: repeat (1, 2) 6030 ++ (8746, 2) :: (1, 1) :: repeat (1, 2) 51689 ++ (263502, 2) :: (1, 1) :: repeat (1, 2) 595550 ++ (233769, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) 1)).
  {
    replace ((10, 2) :: (4, 2) :: (1, 1) :: repeat (1, 2) 35 ++ (20, 2) :: (1, 1) :: repeat (1, 2) 170 ++ (2665, 2) :: (1, 1) :: repeat (1, 2) 6030 ++ (8746, 2) :: (1, 1) :: repeat (1, 2) 51689 ++ (263502, 2) :: (1, 1) :: repeat (1, 2) 595550 ++ (233769, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) with ((12 - 2, 2) :: (4, 2) :: (1, 1) :: repeat (1, 2) 35 ++ (20, 2) :: (1, 1) :: repeat (1, 2) 170 ++ (2665, 2) :: (1, 1) :: repeat (1, 2) 6030 ++ (8746, 2) :: (1, 1) :: repeat (1, 2) 51689 ++ (263502, 2) :: (1, 1) :: repeat (1, 2) 595550 ++ (233769, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) by sec_eq.
    apply (sPUSH [] 3 12 ((4, 2) :: (1, 1) :: repeat (1, 2) 35 ++ (20, 2) :: (1, 1) :: repeat (1, 2) 170 ++ (2665, 2) :: (1, 1) :: repeat (1, 2) 6030 ++ (8746, 2) :: (1, 1) :: repeat (1, 2) 51689 ++ (263502, 2) :: (1, 1) :: repeat (1, 2) 595550 ++ (233769, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) 1); closearith.
  }
  (* step 543: P TDN *)
  apply (hsteps_trans _ (HB [] 3 1 4 ((10, 2) :: (4, 2) :: (1, 1) :: repeat (1, 2) 35 ++ (20, 2) :: (1, 1) :: repeat (1, 2) 170 ++ (2665, 2) :: (1, 1) :: repeat (1, 2) 6030 ++ (8746, 2) :: (1, 1) :: repeat (1, 2) 51689 ++ (263502, 2) :: (1, 1) :: repeat (1, 2) 595550 ++ (233769, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) 1)).
  {
    apply (sTDN [] 3 ((10, 2) :: (4, 2) :: (1, 1) :: repeat (1, 2) 35 ++ (20, 2) :: (1, 1) :: repeat (1, 2) 170 ++ (2665, 2) :: (1, 1) :: repeat (1, 2) 6030 ++ (8746, 2) :: (1, 1) :: repeat (1, 2) 51689 ++ (263502, 2) :: (1, 1) :: repeat (1, 2) 595550 ++ (233769, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) 1).
  }
  (* step 544: sTUP *)
  apply (hsteps_trans _ (HC [] 3 3 2 ((8, 2) :: (4, 2) :: (1, 1) :: repeat (1, 2) 35 ++ (20, 2) :: (1, 1) :: repeat (1, 2) 170 ++ (2665, 2) :: (1, 1) :: repeat (1, 2) 6030 ++ (8746, 2) :: (1, 1) :: repeat (1, 2) 51689 ++ (263502, 2) :: (1, 1) :: repeat (1, 2) 595550 ++ (233769, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) 1)).
  {
    replace ((8, 2) :: (4, 2) :: (1, 1) :: repeat (1, 2) 35 ++ (20, 2) :: (1, 1) :: repeat (1, 2) 170 ++ (2665, 2) :: (1, 1) :: repeat (1, 2) 6030 ++ (8746, 2) :: (1, 1) :: repeat (1, 2) 51689 ++ (263502, 2) :: (1, 1) :: repeat (1, 2) 595550 ++ (233769, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) with ((10 - 2, 2) :: (4, 2) :: (1, 1) :: repeat (1, 2) 35 ++ (20, 2) :: (1, 1) :: repeat (1, 2) 170 ++ (2665, 2) :: (1, 1) :: repeat (1, 2) 6030 ++ (8746, 2) :: (1, 1) :: repeat (1, 2) 51689 ++ (263502, 2) :: (1, 1) :: repeat (1, 2) 595550 ++ (233769, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) by sec_eq.
    apply (sTUP [] 3 4 10 2 ((4, 2) :: (1, 1) :: repeat (1, 2) 35 ++ (20, 2) :: (1, 1) :: repeat (1, 2) 170 ++ (2665, 2) :: (1, 1) :: repeat (1, 2) 6030 ++ (8746, 2) :: (1, 1) :: repeat (1, 2) 51689 ++ (263502, 2) :: (1, 1) :: repeat (1, 2) 595550 ++ (233769, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) 1); closearith.
  }
  (* step 545: DIPGRIND 3 2 *)
  apply (hsteps_trans _ (HC [] 0 3 2 (repeat (1, 2) 3 ++ (2, 2) :: (4, 2) :: (1, 1) :: repeat (1, 2) 35 ++ (20, 2) :: (1, 1) :: repeat (1, 2) 170 ++ (2665, 2) :: (1, 1) :: repeat (1, 2) 6030 ++ (8746, 2) :: (1, 1) :: repeat (1, 2) 51689 ++ (263502, 2) :: (1, 1) :: repeat (1, 2) 595550 ++ (233769, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) 1)).
  {
    apply (DIPGRIND 3 2 [] ((4, 2) :: (1, 1) :: repeat (1, 2) 35 ++ (20, 2) :: (1, 1) :: repeat (1, 2) 170 ++ (2665, 2) :: (1, 1) :: repeat (1, 2) 6030 ++ (8746, 2) :: (1, 1) :: repeat (1, 2) 51689 ++ (263502, 2) :: (1, 1) :: repeat (1, 2) 595550 ++ (233769, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) 1); closearith.
  }
  (* step 546: P PUSHX *)
  apply (hsteps_trans _ (HB [] 1 1 7 (repeat (1, 2) 3 ++ (2, 2) :: (4, 2) :: (1, 1) :: repeat (1, 2) 35 ++ (20, 2) :: (1, 1) :: repeat (1, 2) 170 ++ (2665, 2) :: (1, 1) :: repeat (1, 2) 6030 ++ (8746, 2) :: (1, 1) :: repeat (1, 2) 51689 ++ (263502, 2) :: (1, 1) :: repeat (1, 2) 595550 ++ (233769, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) 1)).
  {
    exact (hsteps_step _ _ _ (hPUSHX (repeat (1, 2) 3 ++ (2, 2) :: (4, 2) :: (1, 1) :: repeat (1, 2) 35 ++ (20, 2) :: (1, 1) :: repeat (1, 2) 170 ++ (2665, 2) :: (1, 1) :: repeat (1, 2) 6030 ++ (8746, 2) :: (1, 1) :: repeat (1, 2) 51689 ++ (263502, 2) :: (1, 1) :: repeat (1, 2) 595550 ++ (233769, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) 1) (hsteps_refl _)).
  }
  (* step 547: M pop12 (3,) *)
  apply (hsteps_trans _ (HB [] 4 1 13 ((2, 2) :: (4, 2) :: (1, 1) :: repeat (1, 2) 35 ++ (20, 2) :: (1, 1) :: repeat (1, 2) 170 ++ (2665, 2) :: (1, 1) :: repeat (1, 2) 6030 ++ (8746, 2) :: (1, 1) :: repeat (1, 2) 51689 ++ (263502, 2) :: (1, 1) :: repeat (1, 2) 595550 ++ (233769, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) 1)).
  {
    apply (pop12 3 [] 1 7 ((2, 2) :: (4, 2) :: (1, 1) :: repeat (1, 2) 35 ++ (20, 2) :: (1, 1) :: repeat (1, 2) 170 ++ (2665, 2) :: (1, 1) :: repeat (1, 2) 6030 ++ (8746, 2) :: (1, 1) :: repeat (1, 2) 51689 ++ (263502, 2) :: (1, 1) :: repeat (1, 2) 595550 ++ (233769, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) 1); closearith.
  }
  (* step 548: P TUP2_1 *)
  apply (hsteps_trans _ (HC [5] 13 1 2 ((2, 2) :: (1, 1) :: repeat (1, 2) 35 ++ (20, 2) :: (1, 1) :: repeat (1, 2) 170 ++ (2665, 2) :: (1, 1) :: repeat (1, 2) 6030 ++ (8746, 2) :: (1, 1) :: repeat (1, 2) 51689 ++ (263502, 2) :: (1, 1) :: repeat (1, 2) 595550 ++ (233769, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) 1)).
  {
    replace ((2, 2) :: (1, 1) :: repeat (1, 2) 35 ++ (20, 2) :: (1, 1) :: repeat (1, 2) 170 ++ (2665, 2) :: (1, 1) :: repeat (1, 2) 6030 ++ (8746, 2) :: (1, 1) :: repeat (1, 2) 51689 ++ (263502, 2) :: (1, 1) :: repeat (1, 2) 595550 ++ (233769, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) with ((4 - 2, 2) :: (1, 1) :: repeat (1, 2) 35 ++ (20, 2) :: (1, 1) :: repeat (1, 2) 170 ++ (2665, 2) :: (1, 1) :: repeat (1, 2) 6030 ++ (8746, 2) :: (1, 1) :: repeat (1, 2) 51689 ++ (263502, 2) :: (1, 1) :: repeat (1, 2) 595550 ++ (233769, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) by sec_eq.
    apply (sTUP2_1 [] 4 12 4 ((1, 1) :: repeat (1, 2) 35 ++ (20, 2) :: (1, 1) :: repeat (1, 2) 170 ++ (2665, 2) :: (1, 1) :: repeat (1, 2) 6030 ++ (8746, 2) :: (1, 1) :: repeat (1, 2) 51689 ++ (263502, 2) :: (1, 1) :: repeat (1, 2) 595550 ++ (233769, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) 1); closearith.
  }
  (* step 549: P TDN *)
  apply (hsteps_trans _ (HB [5] 13 1 4 ((2, 2) :: (1, 1) :: repeat (1, 2) 35 ++ (20, 2) :: (1, 1) :: repeat (1, 2) 170 ++ (2665, 2) :: (1, 1) :: repeat (1, 2) 6030 ++ (8746, 2) :: (1, 1) :: repeat (1, 2) 51689 ++ (263502, 2) :: (1, 1) :: repeat (1, 2) 595550 ++ (233769, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) 1)).
  {
    apply (sTDN [5] 13 ((2, 2) :: (1, 1) :: repeat (1, 2) 35 ++ (20, 2) :: (1, 1) :: repeat (1, 2) 170 ++ (2665, 2) :: (1, 1) :: repeat (1, 2) 6030 ++ (8746, 2) :: (1, 1) :: repeat (1, 2) 51689 ++ (263502, 2) :: (1, 1) :: repeat (1, 2) 595550 ++ (233769, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) 1).
  }
  (* step 550: P TRANS2_1 *)
  apply (hsteps_trans _ (HB [14; 5] 5 1 3 (repeat (1, 2) 35 ++ (20, 2) :: (1, 1) :: repeat (1, 2) 170 ++ (2665, 2) :: (1, 1) :: repeat (1, 2) 6030 ++ (8746, 2) :: (1, 1) :: repeat (1, 2) 51689 ++ (263502, 2) :: (1, 1) :: repeat (1, 2) 595550 ++ (233769, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) 1)).
  {
    apply (sTRANS2_1 [5] 13 3 1 (repeat (1, 2) 35 ++ (20, 2) :: (1, 1) :: repeat (1, 2) 170 ++ (2665, 2) :: (1, 1) :: repeat (1, 2) 6030 ++ (8746, 2) :: (1, 1) :: repeat (1, 2) 51689 ++ (263502, 2) :: (1, 1) :: repeat (1, 2) 595550 ++ (233769, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) 1); closearith.
  }
  (* step 551: M pop12 (35,) *)
  apply (hsteps_trans _ (HB [14; 5] 40 1 73 ((20, 2) :: (1, 1) :: repeat (1, 2) 170 ++ (2665, 2) :: (1, 1) :: repeat (1, 2) 6030 ++ (8746, 2) :: (1, 1) :: repeat (1, 2) 51689 ++ (263502, 2) :: (1, 1) :: repeat (1, 2) 595550 ++ (233769, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) 1)).
  {
    apply (pop12 35 [14; 5] 5 3 ((20, 2) :: (1, 1) :: repeat (1, 2) 170 ++ (2665, 2) :: (1, 1) :: repeat (1, 2) 6030 ++ (8746, 2) :: (1, 1) :: repeat (1, 2) 51689 ++ (263502, 2) :: (1, 1) :: repeat (1, 2) 595550 ++ (233769, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) 1); closearith.
  }
  (* step 552: sTUP *)
  apply (hsteps_trans _ (HC [14; 5] 40 72 2 ((18, 2) :: (1, 1) :: repeat (1, 2) 170 ++ (2665, 2) :: (1, 1) :: repeat (1, 2) 6030 ++ (8746, 2) :: (1, 1) :: repeat (1, 2) 51689 ++ (263502, 2) :: (1, 1) :: repeat (1, 2) 595550 ++ (233769, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) 1)).
  {
    replace ((18, 2) :: (1, 1) :: repeat (1, 2) 170 ++ (2665, 2) :: (1, 1) :: repeat (1, 2) 6030 ++ (8746, 2) :: (1, 1) :: repeat (1, 2) 51689 ++ (263502, 2) :: (1, 1) :: repeat (1, 2) 595550 ++ (233769, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) with ((20 - 2, 2) :: (1, 1) :: repeat (1, 2) 170 ++ (2665, 2) :: (1, 1) :: repeat (1, 2) 6030 ++ (8746, 2) :: (1, 1) :: repeat (1, 2) 51689 ++ (263502, 2) :: (1, 1) :: repeat (1, 2) 595550 ++ (233769, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) by sec_eq.
    apply (sTUP [14; 5] 40 73 20 2 ((1, 1) :: repeat (1, 2) 170 ++ (2665, 2) :: (1, 1) :: repeat (1, 2) 6030 ++ (8746, 2) :: (1, 1) :: repeat (1, 2) 51689 ++ (263502, 2) :: (1, 1) :: repeat (1, 2) 595550 ++ (233769, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) 1); closearith.
  }
  (* step 553: hGRIND_even 34 *)
  apply (hsteps_trans _ (HB [14; 5] 39 1 72 ((2, 2) :: (18, 2) :: (1, 1) :: repeat (1, 2) 170 ++ (2665, 2) :: (1, 1) :: repeat (1, 2) 6030 ++ (8746, 2) :: (1, 1) :: repeat (1, 2) 51689 ++ (263502, 2) :: (1, 1) :: repeat (1, 2) 595550 ++ (233769, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) 1)).
  {
    apply (hGRIND_even 34 [14; 5] 39 ((18, 2) :: (1, 1) :: repeat (1, 2) 170 ++ (2665, 2) :: (1, 1) :: repeat (1, 2) 6030 ++ (8746, 2) :: (1, 1) :: repeat (1, 2) 51689 ++ (263502, 2) :: (1, 1) :: repeat (1, 2) 595550 ++ (233769, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) 1); closearith.
  }
  (* step 554: P TUP2_1 *)
  apply (hsteps_trans _ (HC [40; 14; 5] 72 1 2 ((16, 2) :: (1, 1) :: repeat (1, 2) 170 ++ (2665, 2) :: (1, 1) :: repeat (1, 2) 6030 ++ (8746, 2) :: (1, 1) :: repeat (1, 2) 51689 ++ (263502, 2) :: (1, 1) :: repeat (1, 2) 595550 ++ (233769, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) 1)).
  {
    replace ((16, 2) :: (1, 1) :: repeat (1, 2) 170 ++ (2665, 2) :: (1, 1) :: repeat (1, 2) 6030 ++ (8746, 2) :: (1, 1) :: repeat (1, 2) 51689 ++ (263502, 2) :: (1, 1) :: repeat (1, 2) 595550 ++ (233769, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) with ((18 - 2, 2) :: (1, 1) :: repeat (1, 2) 170 ++ (2665, 2) :: (1, 1) :: repeat (1, 2) 6030 ++ (8746, 2) :: (1, 1) :: repeat (1, 2) 51689 ++ (263502, 2) :: (1, 1) :: repeat (1, 2) 595550 ++ (233769, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) by sec_eq.
    apply (sTUP2_1 [14; 5] 39 71 18 ((1, 1) :: repeat (1, 2) 170 ++ (2665, 2) :: (1, 1) :: repeat (1, 2) 6030 ++ (8746, 2) :: (1, 1) :: repeat (1, 2) 51689 ++ (263502, 2) :: (1, 1) :: repeat (1, 2) 595550 ++ (233769, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) 1); closearith.
  }
  (* step 555: P TDN *)
  apply (hsteps_trans _ (HB [40; 14; 5] 72 1 4 ((16, 2) :: (1, 1) :: repeat (1, 2) 170 ++ (2665, 2) :: (1, 1) :: repeat (1, 2) 6030 ++ (8746, 2) :: (1, 1) :: repeat (1, 2) 51689 ++ (263502, 2) :: (1, 1) :: repeat (1, 2) 595550 ++ (233769, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) 1)).
  {
    apply (sTDN [40; 14; 5] 72 ((16, 2) :: (1, 1) :: repeat (1, 2) 170 ++ (2665, 2) :: (1, 1) :: repeat (1, 2) 6030 ++ (8746, 2) :: (1, 1) :: repeat (1, 2) 51689 ++ (263502, 2) :: (1, 1) :: repeat (1, 2) 595550 ++ (233769, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) 1).
  }
  (* step 556: sTUP *)
  apply (hsteps_trans _ (HC [40; 14; 5] 72 3 2 ((14, 2) :: (1, 1) :: repeat (1, 2) 170 ++ (2665, 2) :: (1, 1) :: repeat (1, 2) 6030 ++ (8746, 2) :: (1, 1) :: repeat (1, 2) 51689 ++ (263502, 2) :: (1, 1) :: repeat (1, 2) 595550 ++ (233769, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) 1)).
  {
    replace ((14, 2) :: (1, 1) :: repeat (1, 2) 170 ++ (2665, 2) :: (1, 1) :: repeat (1, 2) 6030 ++ (8746, 2) :: (1, 1) :: repeat (1, 2) 51689 ++ (263502, 2) :: (1, 1) :: repeat (1, 2) 595550 ++ (233769, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) with ((16 - 2, 2) :: (1, 1) :: repeat (1, 2) 170 ++ (2665, 2) :: (1, 1) :: repeat (1, 2) 6030 ++ (8746, 2) :: (1, 1) :: repeat (1, 2) 51689 ++ (263502, 2) :: (1, 1) :: repeat (1, 2) 595550 ++ (233769, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) by sec_eq.
    apply (sTUP [40; 14; 5] 72 4 16 2 ((1, 1) :: repeat (1, 2) 170 ++ (2665, 2) :: (1, 1) :: repeat (1, 2) 6030 ++ (8746, 2) :: (1, 1) :: repeat (1, 2) 51689 ++ (263502, 2) :: (1, 1) :: repeat (1, 2) 595550 ++ (233769, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) 1); closearith.
  }
  (* step 557: CLEANG_even 6 *)
  apply (hsteps_trans _ (HB [40; 14; 5] 72 1 18 ((2, 2) :: (1, 1) :: repeat (1, 2) 170 ++ (2665, 2) :: (1, 1) :: repeat (1, 2) 6030 ++ (8746, 2) :: (1, 1) :: repeat (1, 2) 51689 ++ (263502, 2) :: (1, 1) :: repeat (1, 2) 595550 ++ (233769, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) 1)).
  {
    apply (CLEANG_even 6 [40; 14; 5] 72 ((1, 1) :: repeat (1, 2) 170 ++ (2665, 2) :: (1, 1) :: repeat (1, 2) 6030 ++ (8746, 2) :: (1, 1) :: repeat (1, 2) 51689 ++ (263502, 2) :: (1, 1) :: repeat (1, 2) 595550 ++ (233769, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) 1); closearith.
  }
  (* step 558: P TRANS2_1 *)
  apply (hsteps_trans _ (HB [73; 40; 14; 5] 19 1 3 (repeat (1, 2) 170 ++ (2665, 2) :: (1, 1) :: repeat (1, 2) 6030 ++ (8746, 2) :: (1, 1) :: repeat (1, 2) 51689 ++ (263502, 2) :: (1, 1) :: repeat (1, 2) 595550 ++ (233769, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) 1)).
  {
    apply (sTRANS2_1 [40; 14; 5] 72 17 1 (repeat (1, 2) 170 ++ (2665, 2) :: (1, 1) :: repeat (1, 2) 6030 ++ (8746, 2) :: (1, 1) :: repeat (1, 2) 51689 ++ (263502, 2) :: (1, 1) :: repeat (1, 2) 595550 ++ (233769, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) 1); closearith.
  }
  (* step 559: M pop12 (170,) *)
  apply (hsteps_trans _ (HB [73; 40; 14; 5] 189 1 343 ((2665, 2) :: (1, 1) :: repeat (1, 2) 6030 ++ (8746, 2) :: (1, 1) :: repeat (1, 2) 51689 ++ (263502, 2) :: (1, 1) :: repeat (1, 2) 595550 ++ (233769, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) 1)).
  {
    apply (pop12 170 [73; 40; 14; 5] 19 3 ((2665, 2) :: (1, 1) :: repeat (1, 2) 6030 ++ (8746, 2) :: (1, 1) :: repeat (1, 2) 51689 ++ (263502, 2) :: (1, 1) :: repeat (1, 2) 595550 ++ (233769, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) 1); closearith.
  }
  (* step 560: sTUP *)
  apply (hsteps_trans _ (HC [73; 40; 14; 5] 189 342 2 ((2663, 2) :: (1, 1) :: repeat (1, 2) 6030 ++ (8746, 2) :: (1, 1) :: repeat (1, 2) 51689 ++ (263502, 2) :: (1, 1) :: repeat (1, 2) 595550 ++ (233769, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) 1)).
  {
    replace ((2663, 2) :: (1, 1) :: repeat (1, 2) 6030 ++ (8746, 2) :: (1, 1) :: repeat (1, 2) 51689 ++ (263502, 2) :: (1, 1) :: repeat (1, 2) 595550 ++ (233769, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) with ((2665 - 2, 2) :: (1, 1) :: repeat (1, 2) 6030 ++ (8746, 2) :: (1, 1) :: repeat (1, 2) 51689 ++ (263502, 2) :: (1, 1) :: repeat (1, 2) 595550 ++ (233769, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) by sec_eq.
    apply (sTUP [73; 40; 14; 5] 189 343 2665 2 ((1, 1) :: repeat (1, 2) 6030 ++ (8746, 2) :: (1, 1) :: repeat (1, 2) 51689 ++ (263502, 2) :: (1, 1) :: repeat (1, 2) 595550 ++ (233769, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) 1); closearith.
  }
  (* step 561: hGRIND_even 169 *)
  apply (hsteps_trans _ (HB [73; 40; 14; 5] 188 1 342 ((2, 2) :: (2663, 2) :: (1, 1) :: repeat (1, 2) 6030 ++ (8746, 2) :: (1, 1) :: repeat (1, 2) 51689 ++ (263502, 2) :: (1, 1) :: repeat (1, 2) 595550 ++ (233769, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) 1)).
  {
    apply (hGRIND_even 169 [73; 40; 14; 5] 188 ((2663, 2) :: (1, 1) :: repeat (1, 2) 6030 ++ (8746, 2) :: (1, 1) :: repeat (1, 2) 51689 ++ (263502, 2) :: (1, 1) :: repeat (1, 2) 595550 ++ (233769, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) 1); closearith.
  }
  (* step 562: P TUP2_1 *)
  apply (hsteps_trans _ (HC [189; 73; 40; 14; 5] 342 1 2 ((2661, 2) :: (1, 1) :: repeat (1, 2) 6030 ++ (8746, 2) :: (1, 1) :: repeat (1, 2) 51689 ++ (263502, 2) :: (1, 1) :: repeat (1, 2) 595550 ++ (233769, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) 1)).
  {
    replace ((2661, 2) :: (1, 1) :: repeat (1, 2) 6030 ++ (8746, 2) :: (1, 1) :: repeat (1, 2) 51689 ++ (263502, 2) :: (1, 1) :: repeat (1, 2) 595550 ++ (233769, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) with ((2663 - 2, 2) :: (1, 1) :: repeat (1, 2) 6030 ++ (8746, 2) :: (1, 1) :: repeat (1, 2) 51689 ++ (263502, 2) :: (1, 1) :: repeat (1, 2) 595550 ++ (233769, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) by sec_eq.
    apply (sTUP2_1 [73; 40; 14; 5] 188 341 2663 ((1, 1) :: repeat (1, 2) 6030 ++ (8746, 2) :: (1, 1) :: repeat (1, 2) 51689 ++ (263502, 2) :: (1, 1) :: repeat (1, 2) 595550 ++ (233769, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) 1); closearith.
  }
  (* step 563: P TDN *)
  apply (hsteps_trans _ (HB [189; 73; 40; 14; 5] 342 1 4 ((2661, 2) :: (1, 1) :: repeat (1, 2) 6030 ++ (8746, 2) :: (1, 1) :: repeat (1, 2) 51689 ++ (263502, 2) :: (1, 1) :: repeat (1, 2) 595550 ++ (233769, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) 1)).
  {
    apply (sTDN [189; 73; 40; 14; 5] 342 ((2661, 2) :: (1, 1) :: repeat (1, 2) 6030 ++ (8746, 2) :: (1, 1) :: repeat (1, 2) 51689 ++ (263502, 2) :: (1, 1) :: repeat (1, 2) 595550 ++ (233769, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) 1).
  }
  (* step 564: sTUP *)
  apply (hsteps_trans _ (HC [189; 73; 40; 14; 5] 342 3 2 ((2659, 2) :: (1, 1) :: repeat (1, 2) 6030 ++ (8746, 2) :: (1, 1) :: repeat (1, 2) 51689 ++ (263502, 2) :: (1, 1) :: repeat (1, 2) 595550 ++ (233769, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) 1)).
  {
    replace ((2659, 2) :: (1, 1) :: repeat (1, 2) 6030 ++ (8746, 2) :: (1, 1) :: repeat (1, 2) 51689 ++ (263502, 2) :: (1, 1) :: repeat (1, 2) 595550 ++ (233769, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) with ((2661 - 2, 2) :: (1, 1) :: repeat (1, 2) 6030 ++ (8746, 2) :: (1, 1) :: repeat (1, 2) 51689 ++ (263502, 2) :: (1, 1) :: repeat (1, 2) 595550 ++ (233769, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) by sec_eq.
    apply (sTUP [189; 73; 40; 14; 5] 342 4 2661 2 ((1, 1) :: repeat (1, 2) 6030 ++ (8746, 2) :: (1, 1) :: repeat (1, 2) 51689 ++ (263502, 2) :: (1, 1) :: repeat (1, 2) 595550 ++ (233769, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) 1); closearith.
  }
  (* step 565: DIPGRIND 342 1975 *)
  apply (hsteps_trans _ (HC [189; 73; 40; 14; 5] 0 3 2 (repeat (1, 2) 342 ++ (1975, 2) :: (1, 1) :: repeat (1, 2) 6030 ++ (8746, 2) :: (1, 1) :: repeat (1, 2) 51689 ++ (263502, 2) :: (1, 1) :: repeat (1, 2) 595550 ++ (233769, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) 1)).
  {
    apply (DIPGRIND 342 1975 [189; 73; 40; 14; 5] ((1, 1) :: repeat (1, 2) 6030 ++ (8746, 2) :: (1, 1) :: repeat (1, 2) 51689 ++ (263502, 2) :: (1, 1) :: repeat (1, 2) 595550 ++ (233769, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) 1); closearith.
  }
  (* step 566: P PX2A *)
  apply (hsteps_trans _ (HC [40; 14; 5] 72 187 2 ((1, 1) :: repeat (1, 2) 344 ++ (1975, 2) :: (1, 1) :: repeat (1, 2) 6030 ++ (8746, 2) :: (1, 1) :: repeat (1, 2) 51689 ++ (263502, 2) :: (1, 1) :: repeat (1, 2) 595550 ++ (233769, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) 1)).
  {
    exact (hsteps_step _ _ _ (hPX2A 186 72 [40; 14; 5] (repeat (1, 2) 342 ++ (1975, 2) :: (1, 1) :: repeat (1, 2) 6030 ++ (8746, 2) :: (1, 1) :: repeat (1, 2) 51689 ++ (263502, 2) :: (1, 1) :: repeat (1, 2) 595550 ++ (233769, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) 1) (hsteps_refl _)).
  }
  (* step 567: P PUSH *)
  apply (hsteps_trans _ (HC [40; 14; 5] 71 1 2 ((185, 2) :: (1, 1) :: repeat (1, 2) 344 ++ (1975, 2) :: (1, 1) :: repeat (1, 2) 6030 ++ (8746, 2) :: (1, 1) :: repeat (1, 2) 51689 ++ (263502, 2) :: (1, 1) :: repeat (1, 2) 595550 ++ (233769, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) 1)).
  {
    replace ((185, 2) :: (1, 1) :: repeat (1, 2) 344 ++ (1975, 2) :: (1, 1) :: repeat (1, 2) 6030 ++ (8746, 2) :: (1, 1) :: repeat (1, 2) 51689 ++ (263502, 2) :: (1, 1) :: repeat (1, 2) 595550 ++ (233769, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) with ((187 - 2, 2) :: (1, 1) :: repeat (1, 2) 344 ++ (1975, 2) :: (1, 1) :: repeat (1, 2) 6030 ++ (8746, 2) :: (1, 1) :: repeat (1, 2) 51689 ++ (263502, 2) :: (1, 1) :: repeat (1, 2) 595550 ++ (233769, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) by sec_eq.
    apply (sPUSH [40; 14; 5] 71 187 ((1, 1) :: repeat (1, 2) 344 ++ (1975, 2) :: (1, 1) :: repeat (1, 2) 6030 ++ (8746, 2) :: (1, 1) :: repeat (1, 2) 51689 ++ (263502, 2) :: (1, 1) :: repeat (1, 2) 595550 ++ (233769, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) 1); closearith.
  }
  (* step 568: P TDN *)
  apply (hsteps_trans _ (HB [40; 14; 5] 71 1 4 ((185, 2) :: (1, 1) :: repeat (1, 2) 344 ++ (1975, 2) :: (1, 1) :: repeat (1, 2) 6030 ++ (8746, 2) :: (1, 1) :: repeat (1, 2) 51689 ++ (263502, 2) :: (1, 1) :: repeat (1, 2) 595550 ++ (233769, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) 1)).
  {
    apply (sTDN [40; 14; 5] 71 ((185, 2) :: (1, 1) :: repeat (1, 2) 344 ++ (1975, 2) :: (1, 1) :: repeat (1, 2) 6030 ++ (8746, 2) :: (1, 1) :: repeat (1, 2) 51689 ++ (263502, 2) :: (1, 1) :: repeat (1, 2) 595550 ++ (233769, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) 1).
  }
  (* step 569: sTUP *)
  apply (hsteps_trans _ (HC [40; 14; 5] 71 3 2 ((183, 2) :: (1, 1) :: repeat (1, 2) 344 ++ (1975, 2) :: (1, 1) :: repeat (1, 2) 6030 ++ (8746, 2) :: (1, 1) :: repeat (1, 2) 51689 ++ (263502, 2) :: (1, 1) :: repeat (1, 2) 595550 ++ (233769, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) 1)).
  {
    replace ((183, 2) :: (1, 1) :: repeat (1, 2) 344 ++ (1975, 2) :: (1, 1) :: repeat (1, 2) 6030 ++ (8746, 2) :: (1, 1) :: repeat (1, 2) 51689 ++ (263502, 2) :: (1, 1) :: repeat (1, 2) 595550 ++ (233769, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) with ((185 - 2, 2) :: (1, 1) :: repeat (1, 2) 344 ++ (1975, 2) :: (1, 1) :: repeat (1, 2) 6030 ++ (8746, 2) :: (1, 1) :: repeat (1, 2) 51689 ++ (263502, 2) :: (1, 1) :: repeat (1, 2) 595550 ++ (233769, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) by sec_eq.
    apply (sTUP [40; 14; 5] 71 4 185 2 ((1, 1) :: repeat (1, 2) 344 ++ (1975, 2) :: (1, 1) :: repeat (1, 2) 6030 ++ (8746, 2) :: (1, 1) :: repeat (1, 2) 51689 ++ (263502, 2) :: (1, 1) :: repeat (1, 2) 595550 ++ (233769, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) 1); closearith.
  }
  (* step 570: DIPGRIND 71 41 *)
  apply (hsteps_trans _ (HC [40; 14; 5] 0 3 2 (repeat (1, 2) 71 ++ (41, 2) :: (1, 1) :: repeat (1, 2) 344 ++ (1975, 2) :: (1, 1) :: repeat (1, 2) 6030 ++ (8746, 2) :: (1, 1) :: repeat (1, 2) 51689 ++ (263502, 2) :: (1, 1) :: repeat (1, 2) 595550 ++ (233769, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) 1)).
  {
    apply (DIPGRIND 71 41 [40; 14; 5] ((1, 1) :: repeat (1, 2) 344 ++ (1975, 2) :: (1, 1) :: repeat (1, 2) 6030 ++ (8746, 2) :: (1, 1) :: repeat (1, 2) 51689 ++ (263502, 2) :: (1, 1) :: repeat (1, 2) 595550 ++ (233769, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) 1); closearith.
  }
  (* step 571: P PX2A *)
  apply (hsteps_trans _ (HC [5] 13 38 2 ((1, 1) :: repeat (1, 2) 73 ++ (41, 2) :: (1, 1) :: repeat (1, 2) 344 ++ (1975, 2) :: (1, 1) :: repeat (1, 2) 6030 ++ (8746, 2) :: (1, 1) :: repeat (1, 2) 51689 ++ (263502, 2) :: (1, 1) :: repeat (1, 2) 595550 ++ (233769, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) 1)).
  {
    exact (hsteps_step _ _ _ (hPX2A 37 13 [5] (repeat (1, 2) 71 ++ (41, 2) :: (1, 1) :: repeat (1, 2) 344 ++ (1975, 2) :: (1, 1) :: repeat (1, 2) 6030 ++ (8746, 2) :: (1, 1) :: repeat (1, 2) 51689 ++ (263502, 2) :: (1, 1) :: repeat (1, 2) 595550 ++ (233769, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) 1) (hsteps_refl _)).
  }
  (* step 572: P PUSH *)
  apply (hsteps_trans _ (HC [5] 12 1 2 ((36, 2) :: (1, 1) :: repeat (1, 2) 73 ++ (41, 2) :: (1, 1) :: repeat (1, 2) 344 ++ (1975, 2) :: (1, 1) :: repeat (1, 2) 6030 ++ (8746, 2) :: (1, 1) :: repeat (1, 2) 51689 ++ (263502, 2) :: (1, 1) :: repeat (1, 2) 595550 ++ (233769, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) 1)).
  {
    replace ((36, 2) :: (1, 1) :: repeat (1, 2) 73 ++ (41, 2) :: (1, 1) :: repeat (1, 2) 344 ++ (1975, 2) :: (1, 1) :: repeat (1, 2) 6030 ++ (8746, 2) :: (1, 1) :: repeat (1, 2) 51689 ++ (263502, 2) :: (1, 1) :: repeat (1, 2) 595550 ++ (233769, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) with ((38 - 2, 2) :: (1, 1) :: repeat (1, 2) 73 ++ (41, 2) :: (1, 1) :: repeat (1, 2) 344 ++ (1975, 2) :: (1, 1) :: repeat (1, 2) 6030 ++ (8746, 2) :: (1, 1) :: repeat (1, 2) 51689 ++ (263502, 2) :: (1, 1) :: repeat (1, 2) 595550 ++ (233769, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) by sec_eq.
    apply (sPUSH [5] 12 38 ((1, 1) :: repeat (1, 2) 73 ++ (41, 2) :: (1, 1) :: repeat (1, 2) 344 ++ (1975, 2) :: (1, 1) :: repeat (1, 2) 6030 ++ (8746, 2) :: (1, 1) :: repeat (1, 2) 51689 ++ (263502, 2) :: (1, 1) :: repeat (1, 2) 595550 ++ (233769, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) 1); closearith.
  }
  (* step 573: P TDN *)
  apply (sTDN [5] 12 ((36, 2) :: (1, 1) :: repeat (1, 2) 73 ++ (41, 2) :: (1, 1) :: repeat (1, 2) 344 ++ (1975, 2) :: (1, 1) :: repeat (1, 2) 6030 ++ (8746, 2) :: (1, 1) :: repeat (1, 2) 51689 ++ (263502, 2) :: (1, 1) :: repeat (1, 2) 595550 ++ (233769, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) 1).
Qed.

(* CASCADE56m: steps 574-629 of the CASCADE56 chain. *)
Lemma CASCADE56m : forall w,
  hsteps (HB [5] 12 1 4 ((36, 2) :: (1, 1) :: repeat (1, 2) 73 ++ (41, 2) :: (1, 1) :: repeat (1, 2) 344 ++ (1975, 2) :: (1, 1) :: repeat (1, 2) 6030 ++ (8746, 2) :: (1, 1) :: repeat (1, 2) 51689 ++ (263502, 2) :: (1, 1) :: repeat (1, 2) 595550 ++ (233769, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) 1)
         (HC [1059; 199; 101; 0] 7498 12570 2 ((8744, 2) :: (1, 1) :: repeat (1, 2) 51689 ++ (263502, 2) :: (1, 1) :: repeat (1, 2) 595550 ++ (233769, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) 1).
Proof.
  intro w.
  (* step 574: sTUP *)
  apply (hsteps_trans _ (HC [5] 12 3 2 ((34, 2) :: (1, 1) :: repeat (1, 2) 73 ++ (41, 2) :: (1, 1) :: repeat (1, 2) 344 ++ (1975, 2) :: (1, 1) :: repeat (1, 2) 6030 ++ (8746, 2) :: (1, 1) :: repeat (1, 2) 51689 ++ (263502, 2) :: (1, 1) :: repeat (1, 2) 595550 ++ (233769, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) 1)).
  {
    replace ((34, 2) :: (1, 1) :: repeat (1, 2) 73 ++ (41, 2) :: (1, 1) :: repeat (1, 2) 344 ++ (1975, 2) :: (1, 1) :: repeat (1, 2) 6030 ++ (8746, 2) :: (1, 1) :: repeat (1, 2) 51689 ++ (263502, 2) :: (1, 1) :: repeat (1, 2) 595550 ++ (233769, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) with ((36 - 2, 2) :: (1, 1) :: repeat (1, 2) 73 ++ (41, 2) :: (1, 1) :: repeat (1, 2) 344 ++ (1975, 2) :: (1, 1) :: repeat (1, 2) 6030 ++ (8746, 2) :: (1, 1) :: repeat (1, 2) 51689 ++ (263502, 2) :: (1, 1) :: repeat (1, 2) 595550 ++ (233769, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) by sec_eq.
    apply (sTUP [5] 12 4 36 2 ((1, 1) :: repeat (1, 2) 73 ++ (41, 2) :: (1, 1) :: repeat (1, 2) 344 ++ (1975, 2) :: (1, 1) :: repeat (1, 2) 6030 ++ (8746, 2) :: (1, 1) :: repeat (1, 2) 51689 ++ (263502, 2) :: (1, 1) :: repeat (1, 2) 595550 ++ (233769, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) 1); closearith.
  }
  (* step 575: DIPGRIND 12 10 *)
  apply (hsteps_trans _ (HC [5] 0 3 2 (repeat (1, 2) 12 ++ (10, 2) :: (1, 1) :: repeat (1, 2) 73 ++ (41, 2) :: (1, 1) :: repeat (1, 2) 344 ++ (1975, 2) :: (1, 1) :: repeat (1, 2) 6030 ++ (8746, 2) :: (1, 1) :: repeat (1, 2) 51689 ++ (263502, 2) :: (1, 1) :: repeat (1, 2) 595550 ++ (233769, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) 1)).
  {
    apply (DIPGRIND 12 10 [5] ((1, 1) :: repeat (1, 2) 73 ++ (41, 2) :: (1, 1) :: repeat (1, 2) 344 ++ (1975, 2) :: (1, 1) :: repeat (1, 2) 6030 ++ (8746, 2) :: (1, 1) :: repeat (1, 2) 51689 ++ (263502, 2) :: (1, 1) :: repeat (1, 2) 595550 ++ (233769, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) 1); closearith.
  }
  (* step 576: P PX2Bgen *)
  apply (hsteps_trans _ (HB [0] 3 1 2 (repeat (1, 2) 1 ++ (1, 1) :: repeat (1, 2) 14 ++ (10, 2) :: (1, 1) :: repeat (1, 2) 73 ++ (41, 2) :: (1, 1) :: repeat (1, 2) 344 ++ (1975, 2) :: (1, 1) :: repeat (1, 2) 6030 ++ (8746, 2) :: (1, 1) :: repeat (1, 2) 51689 ++ (263502, 2) :: (1, 1) :: repeat (1, 2) 595550 ++ (233769, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) 1)).
  {
    exact (hsteps_step _ _ _ (hPX2Bgen 0 (repeat (1, 2) 12 ++ (10, 2) :: (1, 1) :: repeat (1, 2) 73 ++ (41, 2) :: (1, 1) :: repeat (1, 2) 344 ++ (1975, 2) :: (1, 1) :: repeat (1, 2) 6030 ++ (8746, 2) :: (1, 1) :: repeat (1, 2) 51689 ++ (263502, 2) :: (1, 1) :: repeat (1, 2) 595550 ++ (233769, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) 1) (hsteps_refl _)).
  }
  (* step 577: M pop12 (1,) *)
  apply (hsteps_trans _ (HB [0] 4 1 4 ((1, 1) :: repeat (1, 2) 14 ++ (10, 2) :: (1, 1) :: repeat (1, 2) 73 ++ (41, 2) :: (1, 1) :: repeat (1, 2) 344 ++ (1975, 2) :: (1, 1) :: repeat (1, 2) 6030 ++ (8746, 2) :: (1, 1) :: repeat (1, 2) 51689 ++ (263502, 2) :: (1, 1) :: repeat (1, 2) 595550 ++ (233769, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) 1)).
  {
    apply (pop12 1 [0] 3 2 ((1, 1) :: repeat (1, 2) 14 ++ (10, 2) :: (1, 1) :: repeat (1, 2) 73 ++ (41, 2) :: (1, 1) :: repeat (1, 2) 344 ++ (1975, 2) :: (1, 1) :: repeat (1, 2) 6030 ++ (8746, 2) :: (1, 1) :: repeat (1, 2) 51689 ++ (263502, 2) :: (1, 1) :: repeat (1, 2) 595550 ++ (233769, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) 1); closearith.
  }
  (* step 578: P POP *)
  apply (hsteps_trans _ (HB [0] 5 1 5 (repeat (1, 2) 14 ++ (10, 2) :: (1, 1) :: repeat (1, 2) 73 ++ (41, 2) :: (1, 1) :: repeat (1, 2) 344 ++ (1975, 2) :: (1, 1) :: repeat (1, 2) 6030 ++ (8746, 2) :: (1, 1) :: repeat (1, 2) 51689 ++ (263502, 2) :: (1, 1) :: repeat (1, 2) 595550 ++ (233769, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) 1)).
  {
    apply (sPOP1 [0] 4 4 (repeat (1, 2) 14 ++ (10, 2) :: (1, 1) :: repeat (1, 2) 73 ++ (41, 2) :: (1, 1) :: repeat (1, 2) 344 ++ (1975, 2) :: (1, 1) :: repeat (1, 2) 6030 ++ (8746, 2) :: (1, 1) :: repeat (1, 2) 51689 ++ (263502, 2) :: (1, 1) :: repeat (1, 2) 595550 ++ (233769, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) 1); closearith.
  }
  (* step 579: M pop12 (14,) *)
  apply (hsteps_trans _ (HB [0] 19 1 33 ((10, 2) :: (1, 1) :: repeat (1, 2) 73 ++ (41, 2) :: (1, 1) :: repeat (1, 2) 344 ++ (1975, 2) :: (1, 1) :: repeat (1, 2) 6030 ++ (8746, 2) :: (1, 1) :: repeat (1, 2) 51689 ++ (263502, 2) :: (1, 1) :: repeat (1, 2) 595550 ++ (233769, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) 1)).
  {
    apply (pop12 14 [0] 5 5 ((10, 2) :: (1, 1) :: repeat (1, 2) 73 ++ (41, 2) :: (1, 1) :: repeat (1, 2) 344 ++ (1975, 2) :: (1, 1) :: repeat (1, 2) 6030 ++ (8746, 2) :: (1, 1) :: repeat (1, 2) 51689 ++ (263502, 2) :: (1, 1) :: repeat (1, 2) 595550 ++ (233769, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) 1); closearith.
  }
  (* step 580: sTUP *)
  apply (hsteps_trans _ (HC [0] 19 32 2 ((8, 2) :: (1, 1) :: repeat (1, 2) 73 ++ (41, 2) :: (1, 1) :: repeat (1, 2) 344 ++ (1975, 2) :: (1, 1) :: repeat (1, 2) 6030 ++ (8746, 2) :: (1, 1) :: repeat (1, 2) 51689 ++ (263502, 2) :: (1, 1) :: repeat (1, 2) 595550 ++ (233769, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) 1)).
  {
    replace ((8, 2) :: (1, 1) :: repeat (1, 2) 73 ++ (41, 2) :: (1, 1) :: repeat (1, 2) 344 ++ (1975, 2) :: (1, 1) :: repeat (1, 2) 6030 ++ (8746, 2) :: (1, 1) :: repeat (1, 2) 51689 ++ (263502, 2) :: (1, 1) :: repeat (1, 2) 595550 ++ (233769, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) with ((10 - 2, 2) :: (1, 1) :: repeat (1, 2) 73 ++ (41, 2) :: (1, 1) :: repeat (1, 2) 344 ++ (1975, 2) :: (1, 1) :: repeat (1, 2) 6030 ++ (8746, 2) :: (1, 1) :: repeat (1, 2) 51689 ++ (263502, 2) :: (1, 1) :: repeat (1, 2) 595550 ++ (233769, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) by sec_eq.
    apply (sTUP [0] 19 33 10 2 ((1, 1) :: repeat (1, 2) 73 ++ (41, 2) :: (1, 1) :: repeat (1, 2) 344 ++ (1975, 2) :: (1, 1) :: repeat (1, 2) 6030 ++ (8746, 2) :: (1, 1) :: repeat (1, 2) 51689 ++ (263502, 2) :: (1, 1) :: repeat (1, 2) 595550 ++ (233769, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) 1); closearith.
  }
  (* step 581: hGRIND_even 14 *)
  apply (hsteps_trans _ (HB [0] 18 1 32 ((2, 2) :: (8, 2) :: (1, 1) :: repeat (1, 2) 73 ++ (41, 2) :: (1, 1) :: repeat (1, 2) 344 ++ (1975, 2) :: (1, 1) :: repeat (1, 2) 6030 ++ (8746, 2) :: (1, 1) :: repeat (1, 2) 51689 ++ (263502, 2) :: (1, 1) :: repeat (1, 2) 595550 ++ (233769, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) 1)).
  {
    apply (hGRIND_even 14 [0] 18 ((8, 2) :: (1, 1) :: repeat (1, 2) 73 ++ (41, 2) :: (1, 1) :: repeat (1, 2) 344 ++ (1975, 2) :: (1, 1) :: repeat (1, 2) 6030 ++ (8746, 2) :: (1, 1) :: repeat (1, 2) 51689 ++ (263502, 2) :: (1, 1) :: repeat (1, 2) 595550 ++ (233769, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) 1); closearith.
  }
  (* step 582: P TUP2_1 *)
  apply (hsteps_trans _ (HC [19; 0] 32 1 2 ((6, 2) :: (1, 1) :: repeat (1, 2) 73 ++ (41, 2) :: (1, 1) :: repeat (1, 2) 344 ++ (1975, 2) :: (1, 1) :: repeat (1, 2) 6030 ++ (8746, 2) :: (1, 1) :: repeat (1, 2) 51689 ++ (263502, 2) :: (1, 1) :: repeat (1, 2) 595550 ++ (233769, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) 1)).
  {
    replace ((6, 2) :: (1, 1) :: repeat (1, 2) 73 ++ (41, 2) :: (1, 1) :: repeat (1, 2) 344 ++ (1975, 2) :: (1, 1) :: repeat (1, 2) 6030 ++ (8746, 2) :: (1, 1) :: repeat (1, 2) 51689 ++ (263502, 2) :: (1, 1) :: repeat (1, 2) 595550 ++ (233769, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) with ((8 - 2, 2) :: (1, 1) :: repeat (1, 2) 73 ++ (41, 2) :: (1, 1) :: repeat (1, 2) 344 ++ (1975, 2) :: (1, 1) :: repeat (1, 2) 6030 ++ (8746, 2) :: (1, 1) :: repeat (1, 2) 51689 ++ (263502, 2) :: (1, 1) :: repeat (1, 2) 595550 ++ (233769, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) by sec_eq.
    apply (sTUP2_1 [0] 18 31 8 ((1, 1) :: repeat (1, 2) 73 ++ (41, 2) :: (1, 1) :: repeat (1, 2) 344 ++ (1975, 2) :: (1, 1) :: repeat (1, 2) 6030 ++ (8746, 2) :: (1, 1) :: repeat (1, 2) 51689 ++ (263502, 2) :: (1, 1) :: repeat (1, 2) 595550 ++ (233769, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) 1); closearith.
  }
  (* step 583: P TDN *)
  apply (hsteps_trans _ (HB [19; 0] 32 1 4 ((6, 2) :: (1, 1) :: repeat (1, 2) 73 ++ (41, 2) :: (1, 1) :: repeat (1, 2) 344 ++ (1975, 2) :: (1, 1) :: repeat (1, 2) 6030 ++ (8746, 2) :: (1, 1) :: repeat (1, 2) 51689 ++ (263502, 2) :: (1, 1) :: repeat (1, 2) 595550 ++ (233769, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) 1)).
  {
    apply (sTDN [19; 0] 32 ((6, 2) :: (1, 1) :: repeat (1, 2) 73 ++ (41, 2) :: (1, 1) :: repeat (1, 2) 344 ++ (1975, 2) :: (1, 1) :: repeat (1, 2) 6030 ++ (8746, 2) :: (1, 1) :: repeat (1, 2) 51689 ++ (263502, 2) :: (1, 1) :: repeat (1, 2) 595550 ++ (233769, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) 1).
  }
  (* step 584: sTUP *)
  apply (hsteps_trans _ (HC [19; 0] 32 3 2 ((4, 2) :: (1, 1) :: repeat (1, 2) 73 ++ (41, 2) :: (1, 1) :: repeat (1, 2) 344 ++ (1975, 2) :: (1, 1) :: repeat (1, 2) 6030 ++ (8746, 2) :: (1, 1) :: repeat (1, 2) 51689 ++ (263502, 2) :: (1, 1) :: repeat (1, 2) 595550 ++ (233769, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) 1)).
  {
    replace ((4, 2) :: (1, 1) :: repeat (1, 2) 73 ++ (41, 2) :: (1, 1) :: repeat (1, 2) 344 ++ (1975, 2) :: (1, 1) :: repeat (1, 2) 6030 ++ (8746, 2) :: (1, 1) :: repeat (1, 2) 51689 ++ (263502, 2) :: (1, 1) :: repeat (1, 2) 595550 ++ (233769, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) with ((6 - 2, 2) :: (1, 1) :: repeat (1, 2) 73 ++ (41, 2) :: (1, 1) :: repeat (1, 2) 344 ++ (1975, 2) :: (1, 1) :: repeat (1, 2) 6030 ++ (8746, 2) :: (1, 1) :: repeat (1, 2) 51689 ++ (263502, 2) :: (1, 1) :: repeat (1, 2) 595550 ++ (233769, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) by sec_eq.
    apply (sTUP [19; 0] 32 4 6 2 ((1, 1) :: repeat (1, 2) 73 ++ (41, 2) :: (1, 1) :: repeat (1, 2) 344 ++ (1975, 2) :: (1, 1) :: repeat (1, 2) 6030 ++ (8746, 2) :: (1, 1) :: repeat (1, 2) 51689 ++ (263502, 2) :: (1, 1) :: repeat (1, 2) 595550 ++ (233769, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) 1); closearith.
  }
  (* step 585: CLEANG_even 1 *)
  apply (hsteps_trans _ (HB [19; 0] 32 1 8 ((2, 2) :: (1, 1) :: repeat (1, 2) 73 ++ (41, 2) :: (1, 1) :: repeat (1, 2) 344 ++ (1975, 2) :: (1, 1) :: repeat (1, 2) 6030 ++ (8746, 2) :: (1, 1) :: repeat (1, 2) 51689 ++ (263502, 2) :: (1, 1) :: repeat (1, 2) 595550 ++ (233769, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) 1)).
  {
    apply (CLEANG_even 1 [19; 0] 32 ((1, 1) :: repeat (1, 2) 73 ++ (41, 2) :: (1, 1) :: repeat (1, 2) 344 ++ (1975, 2) :: (1, 1) :: repeat (1, 2) 6030 ++ (8746, 2) :: (1, 1) :: repeat (1, 2) 51689 ++ (263502, 2) :: (1, 1) :: repeat (1, 2) 595550 ++ (233769, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) 1); closearith.
  }
  (* step 586: P TRANS2_1 *)
  apply (hsteps_trans _ (HB [33; 19; 0] 9 1 3 (repeat (1, 2) 73 ++ (41, 2) :: (1, 1) :: repeat (1, 2) 344 ++ (1975, 2) :: (1, 1) :: repeat (1, 2) 6030 ++ (8746, 2) :: (1, 1) :: repeat (1, 2) 51689 ++ (263502, 2) :: (1, 1) :: repeat (1, 2) 595550 ++ (233769, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) 1)).
  {
    apply (sTRANS2_1 [19; 0] 32 7 1 (repeat (1, 2) 73 ++ (41, 2) :: (1, 1) :: repeat (1, 2) 344 ++ (1975, 2) :: (1, 1) :: repeat (1, 2) 6030 ++ (8746, 2) :: (1, 1) :: repeat (1, 2) 51689 ++ (263502, 2) :: (1, 1) :: repeat (1, 2) 595550 ++ (233769, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) 1); closearith.
  }
  (* step 587: M pop12 (73,) *)
  apply (hsteps_trans _ (HB [33; 19; 0] 82 1 149 ((41, 2) :: (1, 1) :: repeat (1, 2) 344 ++ (1975, 2) :: (1, 1) :: repeat (1, 2) 6030 ++ (8746, 2) :: (1, 1) :: repeat (1, 2) 51689 ++ (263502, 2) :: (1, 1) :: repeat (1, 2) 595550 ++ (233769, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) 1)).
  {
    apply (pop12 73 [33; 19; 0] 9 3 ((41, 2) :: (1, 1) :: repeat (1, 2) 344 ++ (1975, 2) :: (1, 1) :: repeat (1, 2) 6030 ++ (8746, 2) :: (1, 1) :: repeat (1, 2) 51689 ++ (263502, 2) :: (1, 1) :: repeat (1, 2) 595550 ++ (233769, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) 1); closearith.
  }
  (* step 588: sTUP *)
  apply (hsteps_trans _ (HC [33; 19; 0] 82 148 2 ((39, 2) :: (1, 1) :: repeat (1, 2) 344 ++ (1975, 2) :: (1, 1) :: repeat (1, 2) 6030 ++ (8746, 2) :: (1, 1) :: repeat (1, 2) 51689 ++ (263502, 2) :: (1, 1) :: repeat (1, 2) 595550 ++ (233769, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) 1)).
  {
    replace ((39, 2) :: (1, 1) :: repeat (1, 2) 344 ++ (1975, 2) :: (1, 1) :: repeat (1, 2) 6030 ++ (8746, 2) :: (1, 1) :: repeat (1, 2) 51689 ++ (263502, 2) :: (1, 1) :: repeat (1, 2) 595550 ++ (233769, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) with ((41 - 2, 2) :: (1, 1) :: repeat (1, 2) 344 ++ (1975, 2) :: (1, 1) :: repeat (1, 2) 6030 ++ (8746, 2) :: (1, 1) :: repeat (1, 2) 51689 ++ (263502, 2) :: (1, 1) :: repeat (1, 2) 595550 ++ (233769, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) by sec_eq.
    apply (sTUP [33; 19; 0] 82 149 41 2 ((1, 1) :: repeat (1, 2) 344 ++ (1975, 2) :: (1, 1) :: repeat (1, 2) 6030 ++ (8746, 2) :: (1, 1) :: repeat (1, 2) 51689 ++ (263502, 2) :: (1, 1) :: repeat (1, 2) 595550 ++ (233769, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) 1); closearith.
  }
  (* step 589: hGRIND_even 72 *)
  apply (hsteps_trans _ (HB [33; 19; 0] 81 1 148 ((2, 2) :: (39, 2) :: (1, 1) :: repeat (1, 2) 344 ++ (1975, 2) :: (1, 1) :: repeat (1, 2) 6030 ++ (8746, 2) :: (1, 1) :: repeat (1, 2) 51689 ++ (263502, 2) :: (1, 1) :: repeat (1, 2) 595550 ++ (233769, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) 1)).
  {
    apply (hGRIND_even 72 [33; 19; 0] 81 ((39, 2) :: (1, 1) :: repeat (1, 2) 344 ++ (1975, 2) :: (1, 1) :: repeat (1, 2) 6030 ++ (8746, 2) :: (1, 1) :: repeat (1, 2) 51689 ++ (263502, 2) :: (1, 1) :: repeat (1, 2) 595550 ++ (233769, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) 1); closearith.
  }
  (* step 590: P TUP2_1 *)
  apply (hsteps_trans _ (HC [82; 33; 19; 0] 148 1 2 ((37, 2) :: (1, 1) :: repeat (1, 2) 344 ++ (1975, 2) :: (1, 1) :: repeat (1, 2) 6030 ++ (8746, 2) :: (1, 1) :: repeat (1, 2) 51689 ++ (263502, 2) :: (1, 1) :: repeat (1, 2) 595550 ++ (233769, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) 1)).
  {
    replace ((37, 2) :: (1, 1) :: repeat (1, 2) 344 ++ (1975, 2) :: (1, 1) :: repeat (1, 2) 6030 ++ (8746, 2) :: (1, 1) :: repeat (1, 2) 51689 ++ (263502, 2) :: (1, 1) :: repeat (1, 2) 595550 ++ (233769, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) with ((39 - 2, 2) :: (1, 1) :: repeat (1, 2) 344 ++ (1975, 2) :: (1, 1) :: repeat (1, 2) 6030 ++ (8746, 2) :: (1, 1) :: repeat (1, 2) 51689 ++ (263502, 2) :: (1, 1) :: repeat (1, 2) 595550 ++ (233769, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) by sec_eq.
    apply (sTUP2_1 [33; 19; 0] 81 147 39 ((1, 1) :: repeat (1, 2) 344 ++ (1975, 2) :: (1, 1) :: repeat (1, 2) 6030 ++ (8746, 2) :: (1, 1) :: repeat (1, 2) 51689 ++ (263502, 2) :: (1, 1) :: repeat (1, 2) 595550 ++ (233769, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) 1); closearith.
  }
  (* step 591: P TDN *)
  apply (hsteps_trans _ (HB [82; 33; 19; 0] 148 1 4 ((37, 2) :: (1, 1) :: repeat (1, 2) 344 ++ (1975, 2) :: (1, 1) :: repeat (1, 2) 6030 ++ (8746, 2) :: (1, 1) :: repeat (1, 2) 51689 ++ (263502, 2) :: (1, 1) :: repeat (1, 2) 595550 ++ (233769, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) 1)).
  {
    apply (sTDN [82; 33; 19; 0] 148 ((37, 2) :: (1, 1) :: repeat (1, 2) 344 ++ (1975, 2) :: (1, 1) :: repeat (1, 2) 6030 ++ (8746, 2) :: (1, 1) :: repeat (1, 2) 51689 ++ (263502, 2) :: (1, 1) :: repeat (1, 2) 595550 ++ (233769, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) 1).
  }
  (* step 592: sTUP *)
  apply (hsteps_trans _ (HC [82; 33; 19; 0] 148 3 2 ((35, 2) :: (1, 1) :: repeat (1, 2) 344 ++ (1975, 2) :: (1, 1) :: repeat (1, 2) 6030 ++ (8746, 2) :: (1, 1) :: repeat (1, 2) 51689 ++ (263502, 2) :: (1, 1) :: repeat (1, 2) 595550 ++ (233769, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) 1)).
  {
    replace ((35, 2) :: (1, 1) :: repeat (1, 2) 344 ++ (1975, 2) :: (1, 1) :: repeat (1, 2) 6030 ++ (8746, 2) :: (1, 1) :: repeat (1, 2) 51689 ++ (263502, 2) :: (1, 1) :: repeat (1, 2) 595550 ++ (233769, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) with ((37 - 2, 2) :: (1, 1) :: repeat (1, 2) 344 ++ (1975, 2) :: (1, 1) :: repeat (1, 2) 6030 ++ (8746, 2) :: (1, 1) :: repeat (1, 2) 51689 ++ (263502, 2) :: (1, 1) :: repeat (1, 2) 595550 ++ (233769, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) by sec_eq.
    apply (sTUP [82; 33; 19; 0] 148 4 37 2 ((1, 1) :: repeat (1, 2) 344 ++ (1975, 2) :: (1, 1) :: repeat (1, 2) 6030 ++ (8746, 2) :: (1, 1) :: repeat (1, 2) 51689 ++ (263502, 2) :: (1, 1) :: repeat (1, 2) 595550 ++ (233769, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) 1); closearith.
  }
  (* step 593: CLEANG_odd 16 *)
  apply (hsteps_trans _ (HB [82; 33; 19; 0] 148 1 40 (repeat (1, 2) 1 ++ (1, 1) :: repeat (1, 2) 344 ++ (1975, 2) :: (1, 1) :: repeat (1, 2) 6030 ++ (8746, 2) :: (1, 1) :: repeat (1, 2) 51689 ++ (263502, 2) :: (1, 1) :: repeat (1, 2) 595550 ++ (233769, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) 1)).
  {
    replace (repeat (1, 2) 1 ++ (1, 1) :: repeat (1, 2) 344 ++ (1975, 2) :: (1, 1) :: repeat (1, 2) 6030 ++ (8746, 2) :: (1, 1) :: repeat (1, 2) 51689 ++ (263502, 2) :: (1, 1) :: repeat (1, 2) 595550 ++ (233769, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) with ((1, 2) :: (1, 1) :: repeat (1, 2) 344 ++ (1975, 2) :: (1, 1) :: repeat (1, 2) 6030 ++ (8746, 2) :: (1, 1) :: repeat (1, 2) 51689 ++ (263502, 2) :: (1, 1) :: repeat (1, 2) 595550 ++ (233769, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) by sec_eq.
    apply (CLEANG_odd 16 [82; 33; 19; 0] 148 ((1, 1) :: repeat (1, 2) 344 ++ (1975, 2) :: (1, 1) :: repeat (1, 2) 6030 ++ (8746, 2) :: (1, 1) :: repeat (1, 2) 51689 ++ (263502, 2) :: (1, 1) :: repeat (1, 2) 595550 ++ (233769, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) 1); closearith.
  }
  (* step 594: M pop12 (1,) *)
  apply (hsteps_trans _ (HB [82; 33; 19; 0] 149 1 42 ((1, 1) :: repeat (1, 2) 344 ++ (1975, 2) :: (1, 1) :: repeat (1, 2) 6030 ++ (8746, 2) :: (1, 1) :: repeat (1, 2) 51689 ++ (263502, 2) :: (1, 1) :: repeat (1, 2) 595550 ++ (233769, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) 1)).
  {
    apply (pop12 1 [82; 33; 19; 0] 148 40 ((1, 1) :: repeat (1, 2) 344 ++ (1975, 2) :: (1, 1) :: repeat (1, 2) 6030 ++ (8746, 2) :: (1, 1) :: repeat (1, 2) 51689 ++ (263502, 2) :: (1, 1) :: repeat (1, 2) 595550 ++ (233769, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) 1); closearith.
  }
  (* step 595: P POP *)
  apply (hsteps_trans _ (HB [82; 33; 19; 0] 150 1 43 (repeat (1, 2) 344 ++ (1975, 2) :: (1, 1) :: repeat (1, 2) 6030 ++ (8746, 2) :: (1, 1) :: repeat (1, 2) 51689 ++ (263502, 2) :: (1, 1) :: repeat (1, 2) 595550 ++ (233769, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) 1)).
  {
    apply (sPOP1 [82; 33; 19; 0] 149 42 (repeat (1, 2) 344 ++ (1975, 2) :: (1, 1) :: repeat (1, 2) 6030 ++ (8746, 2) :: (1, 1) :: repeat (1, 2) 51689 ++ (263502, 2) :: (1, 1) :: repeat (1, 2) 595550 ++ (233769, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) 1); closearith.
  }
  (* step 596: M pop12 (344,) *)
  apply (hsteps_trans _ (HB [82; 33; 19; 0] 494 1 731 ((1975, 2) :: (1, 1) :: repeat (1, 2) 6030 ++ (8746, 2) :: (1, 1) :: repeat (1, 2) 51689 ++ (263502, 2) :: (1, 1) :: repeat (1, 2) 595550 ++ (233769, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) 1)).
  {
    apply (pop12 344 [82; 33; 19; 0] 150 43 ((1975, 2) :: (1, 1) :: repeat (1, 2) 6030 ++ (8746, 2) :: (1, 1) :: repeat (1, 2) 51689 ++ (263502, 2) :: (1, 1) :: repeat (1, 2) 595550 ++ (233769, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) 1); closearith.
  }
  (* step 597: sTUP *)
  apply (hsteps_trans _ (HC [82; 33; 19; 0] 494 730 2 ((1973, 2) :: (1, 1) :: repeat (1, 2) 6030 ++ (8746, 2) :: (1, 1) :: repeat (1, 2) 51689 ++ (263502, 2) :: (1, 1) :: repeat (1, 2) 595550 ++ (233769, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) 1)).
  {
    replace ((1973, 2) :: (1, 1) :: repeat (1, 2) 6030 ++ (8746, 2) :: (1, 1) :: repeat (1, 2) 51689 ++ (263502, 2) :: (1, 1) :: repeat (1, 2) 595550 ++ (233769, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) with ((1975 - 2, 2) :: (1, 1) :: repeat (1, 2) 6030 ++ (8746, 2) :: (1, 1) :: repeat (1, 2) 51689 ++ (263502, 2) :: (1, 1) :: repeat (1, 2) 595550 ++ (233769, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) by sec_eq.
    apply (sTUP [82; 33; 19; 0] 494 731 1975 2 ((1, 1) :: repeat (1, 2) 6030 ++ (8746, 2) :: (1, 1) :: repeat (1, 2) 51689 ++ (263502, 2) :: (1, 1) :: repeat (1, 2) 595550 ++ (233769, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) 1); closearith.
  }
  (* step 598: hGRIND_even 363 *)
  apply (hsteps_trans _ (HB [82; 33; 19; 0] 493 1 730 ((2, 2) :: (1973, 2) :: (1, 1) :: repeat (1, 2) 6030 ++ (8746, 2) :: (1, 1) :: repeat (1, 2) 51689 ++ (263502, 2) :: (1, 1) :: repeat (1, 2) 595550 ++ (233769, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) 1)).
  {
    apply (hGRIND_even 363 [82; 33; 19; 0] 493 ((1973, 2) :: (1, 1) :: repeat (1, 2) 6030 ++ (8746, 2) :: (1, 1) :: repeat (1, 2) 51689 ++ (263502, 2) :: (1, 1) :: repeat (1, 2) 595550 ++ (233769, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) 1); closearith.
  }
  (* step 599: P TUP2_1 *)
  apply (hsteps_trans _ (HC [494; 82; 33; 19; 0] 730 1 2 ((1971, 2) :: (1, 1) :: repeat (1, 2) 6030 ++ (8746, 2) :: (1, 1) :: repeat (1, 2) 51689 ++ (263502, 2) :: (1, 1) :: repeat (1, 2) 595550 ++ (233769, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) 1)).
  {
    replace ((1971, 2) :: (1, 1) :: repeat (1, 2) 6030 ++ (8746, 2) :: (1, 1) :: repeat (1, 2) 51689 ++ (263502, 2) :: (1, 1) :: repeat (1, 2) 595550 ++ (233769, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) with ((1973 - 2, 2) :: (1, 1) :: repeat (1, 2) 6030 ++ (8746, 2) :: (1, 1) :: repeat (1, 2) 51689 ++ (263502, 2) :: (1, 1) :: repeat (1, 2) 595550 ++ (233769, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) by sec_eq.
    apply (sTUP2_1 [82; 33; 19; 0] 493 729 1973 ((1, 1) :: repeat (1, 2) 6030 ++ (8746, 2) :: (1, 1) :: repeat (1, 2) 51689 ++ (263502, 2) :: (1, 1) :: repeat (1, 2) 595550 ++ (233769, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) 1); closearith.
  }
  (* step 600: P TDN *)
  apply (hsteps_trans _ (HB [494; 82; 33; 19; 0] 730 1 4 ((1971, 2) :: (1, 1) :: repeat (1, 2) 6030 ++ (8746, 2) :: (1, 1) :: repeat (1, 2) 51689 ++ (263502, 2) :: (1, 1) :: repeat (1, 2) 595550 ++ (233769, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) 1)).
  {
    apply (sTDN [494; 82; 33; 19; 0] 730 ((1971, 2) :: (1, 1) :: repeat (1, 2) 6030 ++ (8746, 2) :: (1, 1) :: repeat (1, 2) 51689 ++ (263502, 2) :: (1, 1) :: repeat (1, 2) 595550 ++ (233769, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) 1).
  }
  (* step 601: sTUP *)
  apply (hsteps_trans _ (HC [494; 82; 33; 19; 0] 730 3 2 ((1969, 2) :: (1, 1) :: repeat (1, 2) 6030 ++ (8746, 2) :: (1, 1) :: repeat (1, 2) 51689 ++ (263502, 2) :: (1, 1) :: repeat (1, 2) 595550 ++ (233769, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) 1)).
  {
    replace ((1969, 2) :: (1, 1) :: repeat (1, 2) 6030 ++ (8746, 2) :: (1, 1) :: repeat (1, 2) 51689 ++ (263502, 2) :: (1, 1) :: repeat (1, 2) 595550 ++ (233769, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) with ((1971 - 2, 2) :: (1, 1) :: repeat (1, 2) 6030 ++ (8746, 2) :: (1, 1) :: repeat (1, 2) 51689 ++ (263502, 2) :: (1, 1) :: repeat (1, 2) 595550 ++ (233769, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) by sec_eq.
    apply (sTUP [494; 82; 33; 19; 0] 730 4 1971 2 ((1, 1) :: repeat (1, 2) 6030 ++ (8746, 2) :: (1, 1) :: repeat (1, 2) 51689 ++ (263502, 2) :: (1, 1) :: repeat (1, 2) 595550 ++ (233769, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) 1); closearith.
  }
  (* step 602: DIPGRIND 730 509 *)
  apply (hsteps_trans _ (HC [494; 82; 33; 19; 0] 0 3 2 (repeat (1, 2) 730 ++ (509, 2) :: (1, 1) :: repeat (1, 2) 6030 ++ (8746, 2) :: (1, 1) :: repeat (1, 2) 51689 ++ (263502, 2) :: (1, 1) :: repeat (1, 2) 595550 ++ (233769, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) 1)).
  {
    apply (DIPGRIND 730 509 [494; 82; 33; 19; 0] ((1, 1) :: repeat (1, 2) 6030 ++ (8746, 2) :: (1, 1) :: repeat (1, 2) 51689 ++ (263502, 2) :: (1, 1) :: repeat (1, 2) 595550 ++ (233769, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) 1); closearith.
  }
  (* step 603: P PX2A *)
  apply (hsteps_trans _ (HC [33; 19; 0] 81 492 2 ((1, 1) :: repeat (1, 2) 732 ++ (509, 2) :: (1, 1) :: repeat (1, 2) 6030 ++ (8746, 2) :: (1, 1) :: repeat (1, 2) 51689 ++ (263502, 2) :: (1, 1) :: repeat (1, 2) 595550 ++ (233769, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) 1)).
  {
    exact (hsteps_step _ _ _ (hPX2A 491 81 [33; 19; 0] (repeat (1, 2) 730 ++ (509, 2) :: (1, 1) :: repeat (1, 2) 6030 ++ (8746, 2) :: (1, 1) :: repeat (1, 2) 51689 ++ (263502, 2) :: (1, 1) :: repeat (1, 2) 595550 ++ (233769, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) 1) (hsteps_refl _)).
  }
  (* step 604: P PUSH *)
  apply (hsteps_trans _ (HC [33; 19; 0] 80 1 2 ((490, 2) :: (1, 1) :: repeat (1, 2) 732 ++ (509, 2) :: (1, 1) :: repeat (1, 2) 6030 ++ (8746, 2) :: (1, 1) :: repeat (1, 2) 51689 ++ (263502, 2) :: (1, 1) :: repeat (1, 2) 595550 ++ (233769, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) 1)).
  {
    replace ((490, 2) :: (1, 1) :: repeat (1, 2) 732 ++ (509, 2) :: (1, 1) :: repeat (1, 2) 6030 ++ (8746, 2) :: (1, 1) :: repeat (1, 2) 51689 ++ (263502, 2) :: (1, 1) :: repeat (1, 2) 595550 ++ (233769, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) with ((492 - 2, 2) :: (1, 1) :: repeat (1, 2) 732 ++ (509, 2) :: (1, 1) :: repeat (1, 2) 6030 ++ (8746, 2) :: (1, 1) :: repeat (1, 2) 51689 ++ (263502, 2) :: (1, 1) :: repeat (1, 2) 595550 ++ (233769, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) by sec_eq.
    apply (sPUSH [33; 19; 0] 80 492 ((1, 1) :: repeat (1, 2) 732 ++ (509, 2) :: (1, 1) :: repeat (1, 2) 6030 ++ (8746, 2) :: (1, 1) :: repeat (1, 2) 51689 ++ (263502, 2) :: (1, 1) :: repeat (1, 2) 595550 ++ (233769, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) 1); closearith.
  }
  (* step 605: P TDN *)
  apply (hsteps_trans _ (HB [33; 19; 0] 80 1 4 ((490, 2) :: (1, 1) :: repeat (1, 2) 732 ++ (509, 2) :: (1, 1) :: repeat (1, 2) 6030 ++ (8746, 2) :: (1, 1) :: repeat (1, 2) 51689 ++ (263502, 2) :: (1, 1) :: repeat (1, 2) 595550 ++ (233769, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) 1)).
  {
    apply (sTDN [33; 19; 0] 80 ((490, 2) :: (1, 1) :: repeat (1, 2) 732 ++ (509, 2) :: (1, 1) :: repeat (1, 2) 6030 ++ (8746, 2) :: (1, 1) :: repeat (1, 2) 51689 ++ (263502, 2) :: (1, 1) :: repeat (1, 2) 595550 ++ (233769, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) 1).
  }
  (* step 606: sTUP *)
  apply (hsteps_trans _ (HC [33; 19; 0] 80 3 2 ((488, 2) :: (1, 1) :: repeat (1, 2) 732 ++ (509, 2) :: (1, 1) :: repeat (1, 2) 6030 ++ (8746, 2) :: (1, 1) :: repeat (1, 2) 51689 ++ (263502, 2) :: (1, 1) :: repeat (1, 2) 595550 ++ (233769, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) 1)).
  {
    replace ((488, 2) :: (1, 1) :: repeat (1, 2) 732 ++ (509, 2) :: (1, 1) :: repeat (1, 2) 6030 ++ (8746, 2) :: (1, 1) :: repeat (1, 2) 51689 ++ (263502, 2) :: (1, 1) :: repeat (1, 2) 595550 ++ (233769, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) with ((490 - 2, 2) :: (1, 1) :: repeat (1, 2) 732 ++ (509, 2) :: (1, 1) :: repeat (1, 2) 6030 ++ (8746, 2) :: (1, 1) :: repeat (1, 2) 51689 ++ (263502, 2) :: (1, 1) :: repeat (1, 2) 595550 ++ (233769, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) by sec_eq.
    apply (sTUP [33; 19; 0] 80 4 490 2 ((1, 1) :: repeat (1, 2) 732 ++ (509, 2) :: (1, 1) :: repeat (1, 2) 6030 ++ (8746, 2) :: (1, 1) :: repeat (1, 2) 51689 ++ (263502, 2) :: (1, 1) :: repeat (1, 2) 595550 ++ (233769, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) 1); closearith.
  }
  (* step 607: DIPGRIND 80 328 *)
  apply (hsteps_trans _ (HC [33; 19; 0] 0 3 2 (repeat (1, 2) 80 ++ (328, 2) :: (1, 1) :: repeat (1, 2) 732 ++ (509, 2) :: (1, 1) :: repeat (1, 2) 6030 ++ (8746, 2) :: (1, 1) :: repeat (1, 2) 51689 ++ (263502, 2) :: (1, 1) :: repeat (1, 2) 595550 ++ (233769, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) 1)).
  {
    apply (DIPGRIND 80 328 [33; 19; 0] ((1, 1) :: repeat (1, 2) 732 ++ (509, 2) :: (1, 1) :: repeat (1, 2) 6030 ++ (8746, 2) :: (1, 1) :: repeat (1, 2) 51689 ++ (263502, 2) :: (1, 1) :: repeat (1, 2) 595550 ++ (233769, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) 1); closearith.
  }
  (* step 608: P PX2A *)
  apply (hsteps_trans _ (HC [0] 18 31 2 ((1, 1) :: repeat (1, 2) 82 ++ (328, 2) :: (1, 1) :: repeat (1, 2) 732 ++ (509, 2) :: (1, 1) :: repeat (1, 2) 6030 ++ (8746, 2) :: (1, 1) :: repeat (1, 2) 51689 ++ (263502, 2) :: (1, 1) :: repeat (1, 2) 595550 ++ (233769, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) 1)).
  {
    exact (hsteps_step _ _ _ (hPX2A 30 18 [0] (repeat (1, 2) 80 ++ (328, 2) :: (1, 1) :: repeat (1, 2) 732 ++ (509, 2) :: (1, 1) :: repeat (1, 2) 6030 ++ (8746, 2) :: (1, 1) :: repeat (1, 2) 51689 ++ (263502, 2) :: (1, 1) :: repeat (1, 2) 595550 ++ (233769, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) 1) (hsteps_refl _)).
  }
  (* step 609: hGRIND 14 *)
  apply (hsteps_trans _ (HB [0] 18 1 34 ((1, 1) :: repeat (1, 2) 82 ++ (328, 2) :: (1, 1) :: repeat (1, 2) 732 ++ (509, 2) :: (1, 1) :: repeat (1, 2) 6030 ++ (8746, 2) :: (1, 1) :: repeat (1, 2) 51689 ++ (263502, 2) :: (1, 1) :: repeat (1, 2) 595550 ++ (233769, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) 1)).
  {
    apply (hGRIND 14 [0] 18 ((1, 1) :: repeat (1, 2) 82 ++ (328, 2) :: (1, 1) :: repeat (1, 2) 732 ++ (509, 2) :: (1, 1) :: repeat (1, 2) 6030 ++ (8746, 2) :: (1, 1) :: repeat (1, 2) 51689 ++ (263502, 2) :: (1, 1) :: repeat (1, 2) 595550 ++ (233769, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) 1); closearith.
  }
  (* step 610: P POP *)
  apply (hsteps_trans _ (HB [0] 19 1 35 (repeat (1, 2) 82 ++ (328, 2) :: (1, 1) :: repeat (1, 2) 732 ++ (509, 2) :: (1, 1) :: repeat (1, 2) 6030 ++ (8746, 2) :: (1, 1) :: repeat (1, 2) 51689 ++ (263502, 2) :: (1, 1) :: repeat (1, 2) 595550 ++ (233769, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) 1)).
  {
    apply (sPOP1 [0] 18 34 (repeat (1, 2) 82 ++ (328, 2) :: (1, 1) :: repeat (1, 2) 732 ++ (509, 2) :: (1, 1) :: repeat (1, 2) 6030 ++ (8746, 2) :: (1, 1) :: repeat (1, 2) 51689 ++ (263502, 2) :: (1, 1) :: repeat (1, 2) 595550 ++ (233769, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) 1); closearith.
  }
  (* step 611: M pop12 (82,) *)
  apply (hsteps_trans _ (HB [0] 101 1 199 ((328, 2) :: (1, 1) :: repeat (1, 2) 732 ++ (509, 2) :: (1, 1) :: repeat (1, 2) 6030 ++ (8746, 2) :: (1, 1) :: repeat (1, 2) 51689 ++ (263502, 2) :: (1, 1) :: repeat (1, 2) 595550 ++ (233769, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) 1)).
  {
    apply (pop12 82 [0] 19 35 ((328, 2) :: (1, 1) :: repeat (1, 2) 732 ++ (509, 2) :: (1, 1) :: repeat (1, 2) 6030 ++ (8746, 2) :: (1, 1) :: repeat (1, 2) 51689 ++ (263502, 2) :: (1, 1) :: repeat (1, 2) 595550 ++ (233769, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) 1); closearith.
  }
  (* step 612: sTUP *)
  apply (hsteps_trans _ (HC [0] 101 198 2 ((326, 2) :: (1, 1) :: repeat (1, 2) 732 ++ (509, 2) :: (1, 1) :: repeat (1, 2) 6030 ++ (8746, 2) :: (1, 1) :: repeat (1, 2) 51689 ++ (263502, 2) :: (1, 1) :: repeat (1, 2) 595550 ++ (233769, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) 1)).
  {
    replace ((326, 2) :: (1, 1) :: repeat (1, 2) 732 ++ (509, 2) :: (1, 1) :: repeat (1, 2) 6030 ++ (8746, 2) :: (1, 1) :: repeat (1, 2) 51689 ++ (263502, 2) :: (1, 1) :: repeat (1, 2) 595550 ++ (233769, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) with ((328 - 2, 2) :: (1, 1) :: repeat (1, 2) 732 ++ (509, 2) :: (1, 1) :: repeat (1, 2) 6030 ++ (8746, 2) :: (1, 1) :: repeat (1, 2) 51689 ++ (263502, 2) :: (1, 1) :: repeat (1, 2) 595550 ++ (233769, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) by sec_eq.
    apply (sTUP [0] 101 199 328 2 ((1, 1) :: repeat (1, 2) 732 ++ (509, 2) :: (1, 1) :: repeat (1, 2) 6030 ++ (8746, 2) :: (1, 1) :: repeat (1, 2) 51689 ++ (263502, 2) :: (1, 1) :: repeat (1, 2) 595550 ++ (233769, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) 1); closearith.
  }
  (* step 613: hGRIND_even 97 *)
  apply (hsteps_trans _ (HB [0] 100 1 198 ((2, 2) :: (326, 2) :: (1, 1) :: repeat (1, 2) 732 ++ (509, 2) :: (1, 1) :: repeat (1, 2) 6030 ++ (8746, 2) :: (1, 1) :: repeat (1, 2) 51689 ++ (263502, 2) :: (1, 1) :: repeat (1, 2) 595550 ++ (233769, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) 1)).
  {
    apply (hGRIND_even 97 [0] 100 ((326, 2) :: (1, 1) :: repeat (1, 2) 732 ++ (509, 2) :: (1, 1) :: repeat (1, 2) 6030 ++ (8746, 2) :: (1, 1) :: repeat (1, 2) 51689 ++ (263502, 2) :: (1, 1) :: repeat (1, 2) 595550 ++ (233769, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) 1); closearith.
  }
  (* step 614: P TUP2_1 *)
  apply (hsteps_trans _ (HC [101; 0] 198 1 2 ((324, 2) :: (1, 1) :: repeat (1, 2) 732 ++ (509, 2) :: (1, 1) :: repeat (1, 2) 6030 ++ (8746, 2) :: (1, 1) :: repeat (1, 2) 51689 ++ (263502, 2) :: (1, 1) :: repeat (1, 2) 595550 ++ (233769, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) 1)).
  {
    replace ((324, 2) :: (1, 1) :: repeat (1, 2) 732 ++ (509, 2) :: (1, 1) :: repeat (1, 2) 6030 ++ (8746, 2) :: (1, 1) :: repeat (1, 2) 51689 ++ (263502, 2) :: (1, 1) :: repeat (1, 2) 595550 ++ (233769, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) with ((326 - 2, 2) :: (1, 1) :: repeat (1, 2) 732 ++ (509, 2) :: (1, 1) :: repeat (1, 2) 6030 ++ (8746, 2) :: (1, 1) :: repeat (1, 2) 51689 ++ (263502, 2) :: (1, 1) :: repeat (1, 2) 595550 ++ (233769, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) by sec_eq.
    apply (sTUP2_1 [0] 100 197 326 ((1, 1) :: repeat (1, 2) 732 ++ (509, 2) :: (1, 1) :: repeat (1, 2) 6030 ++ (8746, 2) :: (1, 1) :: repeat (1, 2) 51689 ++ (263502, 2) :: (1, 1) :: repeat (1, 2) 595550 ++ (233769, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) 1); closearith.
  }
  (* step 615: P TDN *)
  apply (hsteps_trans _ (HB [101; 0] 198 1 4 ((324, 2) :: (1, 1) :: repeat (1, 2) 732 ++ (509, 2) :: (1, 1) :: repeat (1, 2) 6030 ++ (8746, 2) :: (1, 1) :: repeat (1, 2) 51689 ++ (263502, 2) :: (1, 1) :: repeat (1, 2) 595550 ++ (233769, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) 1)).
  {
    apply (sTDN [101; 0] 198 ((324, 2) :: (1, 1) :: repeat (1, 2) 732 ++ (509, 2) :: (1, 1) :: repeat (1, 2) 6030 ++ (8746, 2) :: (1, 1) :: repeat (1, 2) 51689 ++ (263502, 2) :: (1, 1) :: repeat (1, 2) 595550 ++ (233769, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) 1).
  }
  (* step 616: sTUP *)
  apply (hsteps_trans _ (HC [101; 0] 198 3 2 ((322, 2) :: (1, 1) :: repeat (1, 2) 732 ++ (509, 2) :: (1, 1) :: repeat (1, 2) 6030 ++ (8746, 2) :: (1, 1) :: repeat (1, 2) 51689 ++ (263502, 2) :: (1, 1) :: repeat (1, 2) 595550 ++ (233769, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) 1)).
  {
    replace ((322, 2) :: (1, 1) :: repeat (1, 2) 732 ++ (509, 2) :: (1, 1) :: repeat (1, 2) 6030 ++ (8746, 2) :: (1, 1) :: repeat (1, 2) 51689 ++ (263502, 2) :: (1, 1) :: repeat (1, 2) 595550 ++ (233769, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) with ((324 - 2, 2) :: (1, 1) :: repeat (1, 2) 732 ++ (509, 2) :: (1, 1) :: repeat (1, 2) 6030 ++ (8746, 2) :: (1, 1) :: repeat (1, 2) 51689 ++ (263502, 2) :: (1, 1) :: repeat (1, 2) 595550 ++ (233769, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) by sec_eq.
    apply (sTUP [101; 0] 198 4 324 2 ((1, 1) :: repeat (1, 2) 732 ++ (509, 2) :: (1, 1) :: repeat (1, 2) 6030 ++ (8746, 2) :: (1, 1) :: repeat (1, 2) 51689 ++ (263502, 2) :: (1, 1) :: repeat (1, 2) 595550 ++ (233769, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) 1); closearith.
  }
  (* step 617: CLEANG_even 160 *)
  apply (hsteps_trans _ (HB [101; 0] 198 1 326 ((2, 2) :: (1, 1) :: repeat (1, 2) 732 ++ (509, 2) :: (1, 1) :: repeat (1, 2) 6030 ++ (8746, 2) :: (1, 1) :: repeat (1, 2) 51689 ++ (263502, 2) :: (1, 1) :: repeat (1, 2) 595550 ++ (233769, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) 1)).
  {
    apply (CLEANG_even 160 [101; 0] 198 ((1, 1) :: repeat (1, 2) 732 ++ (509, 2) :: (1, 1) :: repeat (1, 2) 6030 ++ (8746, 2) :: (1, 1) :: repeat (1, 2) 51689 ++ (263502, 2) :: (1, 1) :: repeat (1, 2) 595550 ++ (233769, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) 1); closearith.
  }
  (* step 618: P TRANS2_1 *)
  apply (hsteps_trans _ (HB [199; 101; 0] 327 1 3 (repeat (1, 2) 732 ++ (509, 2) :: (1, 1) :: repeat (1, 2) 6030 ++ (8746, 2) :: (1, 1) :: repeat (1, 2) 51689 ++ (263502, 2) :: (1, 1) :: repeat (1, 2) 595550 ++ (233769, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) 1)).
  {
    apply (sTRANS2_1 [101; 0] 198 325 1 (repeat (1, 2) 732 ++ (509, 2) :: (1, 1) :: repeat (1, 2) 6030 ++ (8746, 2) :: (1, 1) :: repeat (1, 2) 51689 ++ (263502, 2) :: (1, 1) :: repeat (1, 2) 595550 ++ (233769, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) 1); closearith.
  }
  (* step 619: M pop12 (732,) *)
  apply (hsteps_trans _ (HB [199; 101; 0] 1059 1 1467 ((509, 2) :: (1, 1) :: repeat (1, 2) 6030 ++ (8746, 2) :: (1, 1) :: repeat (1, 2) 51689 ++ (263502, 2) :: (1, 1) :: repeat (1, 2) 595550 ++ (233769, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) 1)).
  {
    apply (pop12 732 [199; 101; 0] 327 3 ((509, 2) :: (1, 1) :: repeat (1, 2) 6030 ++ (8746, 2) :: (1, 1) :: repeat (1, 2) 51689 ++ (263502, 2) :: (1, 1) :: repeat (1, 2) 595550 ++ (233769, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) 1); closearith.
  }
  (* step 620: sTUP *)
  apply (hsteps_trans _ (HC [199; 101; 0] 1059 1466 2 ((507, 2) :: (1, 1) :: repeat (1, 2) 6030 ++ (8746, 2) :: (1, 1) :: repeat (1, 2) 51689 ++ (263502, 2) :: (1, 1) :: repeat (1, 2) 595550 ++ (233769, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) 1)).
  {
    replace ((507, 2) :: (1, 1) :: repeat (1, 2) 6030 ++ (8746, 2) :: (1, 1) :: repeat (1, 2) 51689 ++ (263502, 2) :: (1, 1) :: repeat (1, 2) 595550 ++ (233769, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) with ((509 - 2, 2) :: (1, 1) :: repeat (1, 2) 6030 ++ (8746, 2) :: (1, 1) :: repeat (1, 2) 51689 ++ (263502, 2) :: (1, 1) :: repeat (1, 2) 595550 ++ (233769, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) by sec_eq.
    apply (sTUP [199; 101; 0] 1059 1467 509 2 ((1, 1) :: repeat (1, 2) 6030 ++ (8746, 2) :: (1, 1) :: repeat (1, 2) 51689 ++ (263502, 2) :: (1, 1) :: repeat (1, 2) 595550 ++ (233769, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) 1); closearith.
  }
  (* step 621: hGRIND_even 731 *)
  apply (hsteps_trans _ (HB [199; 101; 0] 1058 1 1466 ((2, 2) :: (507, 2) :: (1, 1) :: repeat (1, 2) 6030 ++ (8746, 2) :: (1, 1) :: repeat (1, 2) 51689 ++ (263502, 2) :: (1, 1) :: repeat (1, 2) 595550 ++ (233769, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) 1)).
  {
    apply (hGRIND_even 731 [199; 101; 0] 1058 ((507, 2) :: (1, 1) :: repeat (1, 2) 6030 ++ (8746, 2) :: (1, 1) :: repeat (1, 2) 51689 ++ (263502, 2) :: (1, 1) :: repeat (1, 2) 595550 ++ (233769, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) 1); closearith.
  }
  (* step 622: P TUP2_1 *)
  apply (hsteps_trans _ (HC [1059; 199; 101; 0] 1466 1 2 ((505, 2) :: (1, 1) :: repeat (1, 2) 6030 ++ (8746, 2) :: (1, 1) :: repeat (1, 2) 51689 ++ (263502, 2) :: (1, 1) :: repeat (1, 2) 595550 ++ (233769, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) 1)).
  {
    replace ((505, 2) :: (1, 1) :: repeat (1, 2) 6030 ++ (8746, 2) :: (1, 1) :: repeat (1, 2) 51689 ++ (263502, 2) :: (1, 1) :: repeat (1, 2) 595550 ++ (233769, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) with ((507 - 2, 2) :: (1, 1) :: repeat (1, 2) 6030 ++ (8746, 2) :: (1, 1) :: repeat (1, 2) 51689 ++ (263502, 2) :: (1, 1) :: repeat (1, 2) 595550 ++ (233769, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) by sec_eq.
    apply (sTUP2_1 [199; 101; 0] 1058 1465 507 ((1, 1) :: repeat (1, 2) 6030 ++ (8746, 2) :: (1, 1) :: repeat (1, 2) 51689 ++ (263502, 2) :: (1, 1) :: repeat (1, 2) 595550 ++ (233769, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) 1); closearith.
  }
  (* step 623: P TDN *)
  apply (hsteps_trans _ (HB [1059; 199; 101; 0] 1466 1 4 ((505, 2) :: (1, 1) :: repeat (1, 2) 6030 ++ (8746, 2) :: (1, 1) :: repeat (1, 2) 51689 ++ (263502, 2) :: (1, 1) :: repeat (1, 2) 595550 ++ (233769, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) 1)).
  {
    apply (sTDN [1059; 199; 101; 0] 1466 ((505, 2) :: (1, 1) :: repeat (1, 2) 6030 ++ (8746, 2) :: (1, 1) :: repeat (1, 2) 51689 ++ (263502, 2) :: (1, 1) :: repeat (1, 2) 595550 ++ (233769, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) 1).
  }
  (* step 624: sTUP *)
  apply (hsteps_trans _ (HC [1059; 199; 101; 0] 1466 3 2 ((503, 2) :: (1, 1) :: repeat (1, 2) 6030 ++ (8746, 2) :: (1, 1) :: repeat (1, 2) 51689 ++ (263502, 2) :: (1, 1) :: repeat (1, 2) 595550 ++ (233769, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) 1)).
  {
    replace ((503, 2) :: (1, 1) :: repeat (1, 2) 6030 ++ (8746, 2) :: (1, 1) :: repeat (1, 2) 51689 ++ (263502, 2) :: (1, 1) :: repeat (1, 2) 595550 ++ (233769, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) with ((505 - 2, 2) :: (1, 1) :: repeat (1, 2) 6030 ++ (8746, 2) :: (1, 1) :: repeat (1, 2) 51689 ++ (263502, 2) :: (1, 1) :: repeat (1, 2) 595550 ++ (233769, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) by sec_eq.
    apply (sTUP [1059; 199; 101; 0] 1466 4 505 2 ((1, 1) :: repeat (1, 2) 6030 ++ (8746, 2) :: (1, 1) :: repeat (1, 2) 51689 ++ (263502, 2) :: (1, 1) :: repeat (1, 2) 595550 ++ (233769, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) 1); closearith.
  }
  (* step 625: CLEANG_odd 250 *)
  apply (hsteps_trans _ (HB [1059; 199; 101; 0] 1466 1 508 (repeat (1, 2) 1 ++ (1, 1) :: repeat (1, 2) 6030 ++ (8746, 2) :: (1, 1) :: repeat (1, 2) 51689 ++ (263502, 2) :: (1, 1) :: repeat (1, 2) 595550 ++ (233769, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) 1)).
  {
    replace (repeat (1, 2) 1 ++ (1, 1) :: repeat (1, 2) 6030 ++ (8746, 2) :: (1, 1) :: repeat (1, 2) 51689 ++ (263502, 2) :: (1, 1) :: repeat (1, 2) 595550 ++ (233769, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) with ((1, 2) :: (1, 1) :: repeat (1, 2) 6030 ++ (8746, 2) :: (1, 1) :: repeat (1, 2) 51689 ++ (263502, 2) :: (1, 1) :: repeat (1, 2) 595550 ++ (233769, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) by sec_eq.
    apply (CLEANG_odd 250 [1059; 199; 101; 0] 1466 ((1, 1) :: repeat (1, 2) 6030 ++ (8746, 2) :: (1, 1) :: repeat (1, 2) 51689 ++ (263502, 2) :: (1, 1) :: repeat (1, 2) 595550 ++ (233769, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) 1); closearith.
  }
  (* step 626: M pop12 (1,) *)
  apply (hsteps_trans _ (HB [1059; 199; 101; 0] 1467 1 510 ((1, 1) :: repeat (1, 2) 6030 ++ (8746, 2) :: (1, 1) :: repeat (1, 2) 51689 ++ (263502, 2) :: (1, 1) :: repeat (1, 2) 595550 ++ (233769, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) 1)).
  {
    apply (pop12 1 [1059; 199; 101; 0] 1466 508 ((1, 1) :: repeat (1, 2) 6030 ++ (8746, 2) :: (1, 1) :: repeat (1, 2) 51689 ++ (263502, 2) :: (1, 1) :: repeat (1, 2) 595550 ++ (233769, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) 1); closearith.
  }
  (* step 627: P POP *)
  apply (hsteps_trans _ (HB [1059; 199; 101; 0] 1468 1 511 (repeat (1, 2) 6030 ++ (8746, 2) :: (1, 1) :: repeat (1, 2) 51689 ++ (263502, 2) :: (1, 1) :: repeat (1, 2) 595550 ++ (233769, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) 1)).
  {
    apply (sPOP1 [1059; 199; 101; 0] 1467 510 (repeat (1, 2) 6030 ++ (8746, 2) :: (1, 1) :: repeat (1, 2) 51689 ++ (263502, 2) :: (1, 1) :: repeat (1, 2) 595550 ++ (233769, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) 1); closearith.
  }
  (* step 628: M pop12 (6030,) *)
  apply (hsteps_trans _ (HB [1059; 199; 101; 0] 7498 1 12571 ((8746, 2) :: (1, 1) :: repeat (1, 2) 51689 ++ (263502, 2) :: (1, 1) :: repeat (1, 2) 595550 ++ (233769, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) 1)).
  {
    apply (pop12 6030 [1059; 199; 101; 0] 1468 511 ((8746, 2) :: (1, 1) :: repeat (1, 2) 51689 ++ (263502, 2) :: (1, 1) :: repeat (1, 2) 595550 ++ (233769, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) 1); closearith.
  }
  (* step 629: sTUP *)
  replace ((8744, 2) :: (1, 1) :: repeat (1, 2) 51689 ++ (263502, 2) :: (1, 1) :: repeat (1, 2) 595550 ++ (233769, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) with ((8746 - 2, 2) :: (1, 1) :: repeat (1, 2) 51689 ++ (263502, 2) :: (1, 1) :: repeat (1, 2) 595550 ++ (233769, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) by sec_eq.
  apply (sTUP [1059; 199; 101; 0] 7498 12571 8746 2 ((1, 1) :: repeat (1, 2) 51689 ++ (263502, 2) :: (1, 1) :: repeat (1, 2) 595550 ++ (233769, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) 1); closearith.
Qed.

(* CASCADE56n: steps 630-685 of the CASCADE56 chain. *)
Lemma CASCADE56n : forall w,
  hsteps (HC [1059; 199; 101; 0] 7498 12570 2 ((8744, 2) :: (1, 1) :: repeat (1, 2) 51689 ++ (263502, 2) :: (1, 1) :: repeat (1, 2) 595550 ++ (233769, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) 1)
         (HC [0] 20 34 2 ((1112, 2) :: (1, 1) :: repeat (1, 2) 2320 ++ (736, 2) :: (1, 1) :: repeat (1, 2) 12571 ++ (35290, 2) :: (1, 1) :: repeat (1, 2) 103382 ++ (56736, 2) :: (1, 1) :: repeat (1, 2) 595550 ++ (233769, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) 1).
Proof.
  intro w.
  (* step 630: hGRIND_even 6283 *)
  apply (hsteps_trans _ (HB [1059; 199; 101; 0] 7497 1 12570 ((2, 2) :: (8744, 2) :: (1, 1) :: repeat (1, 2) 51689 ++ (263502, 2) :: (1, 1) :: repeat (1, 2) 595550 ++ (233769, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) 1)).
  {
    apply (hGRIND_even 6283 [1059; 199; 101; 0] 7497 ((8744, 2) :: (1, 1) :: repeat (1, 2) 51689 ++ (263502, 2) :: (1, 1) :: repeat (1, 2) 595550 ++ (233769, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) 1); closearith.
  }
  (* step 631: P TUP2_1 *)
  apply (hsteps_trans _ (HC [7498; 1059; 199; 101; 0] 12570 1 2 ((8742, 2) :: (1, 1) :: repeat (1, 2) 51689 ++ (263502, 2) :: (1, 1) :: repeat (1, 2) 595550 ++ (233769, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) 1)).
  {
    replace ((8742, 2) :: (1, 1) :: repeat (1, 2) 51689 ++ (263502, 2) :: (1, 1) :: repeat (1, 2) 595550 ++ (233769, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) with ((8744 - 2, 2) :: (1, 1) :: repeat (1, 2) 51689 ++ (263502, 2) :: (1, 1) :: repeat (1, 2) 595550 ++ (233769, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) by sec_eq.
    apply (sTUP2_1 [1059; 199; 101; 0] 7497 12569 8744 ((1, 1) :: repeat (1, 2) 51689 ++ (263502, 2) :: (1, 1) :: repeat (1, 2) 595550 ++ (233769, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) 1); closearith.
  }
  (* step 632: P TDN *)
  apply (hsteps_trans _ (HB [7498; 1059; 199; 101; 0] 12570 1 4 ((8742, 2) :: (1, 1) :: repeat (1, 2) 51689 ++ (263502, 2) :: (1, 1) :: repeat (1, 2) 595550 ++ (233769, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) 1)).
  {
    apply (sTDN [7498; 1059; 199; 101; 0] 12570 ((8742, 2) :: (1, 1) :: repeat (1, 2) 51689 ++ (263502, 2) :: (1, 1) :: repeat (1, 2) 595550 ++ (233769, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) 1).
  }
  (* step 633: sTUP *)
  apply (hsteps_trans _ (HC [7498; 1059; 199; 101; 0] 12570 3 2 ((8740, 2) :: (1, 1) :: repeat (1, 2) 51689 ++ (263502, 2) :: (1, 1) :: repeat (1, 2) 595550 ++ (233769, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) 1)).
  {
    replace ((8740, 2) :: (1, 1) :: repeat (1, 2) 51689 ++ (263502, 2) :: (1, 1) :: repeat (1, 2) 595550 ++ (233769, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) with ((8742 - 2, 2) :: (1, 1) :: repeat (1, 2) 51689 ++ (263502, 2) :: (1, 1) :: repeat (1, 2) 595550 ++ (233769, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) by sec_eq.
    apply (sTUP [7498; 1059; 199; 101; 0] 12570 4 8742 2 ((1, 1) :: repeat (1, 2) 51689 ++ (263502, 2) :: (1, 1) :: repeat (1, 2) 595550 ++ (233769, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) 1); closearith.
  }
  (* step 634: CLEANG_even 4369 *)
  apply (hsteps_trans _ (HB [7498; 1059; 199; 101; 0] 12570 1 8744 ((2, 2) :: (1, 1) :: repeat (1, 2) 51689 ++ (263502, 2) :: (1, 1) :: repeat (1, 2) 595550 ++ (233769, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) 1)).
  {
    apply (CLEANG_even 4369 [7498; 1059; 199; 101; 0] 12570 ((1, 1) :: repeat (1, 2) 51689 ++ (263502, 2) :: (1, 1) :: repeat (1, 2) 595550 ++ (233769, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) 1); closearith.
  }
  (* step 635: P TRANS2_1 *)
  apply (hsteps_trans _ (HB [12571; 7498; 1059; 199; 101; 0] 8745 1 3 (repeat (1, 2) 51689 ++ (263502, 2) :: (1, 1) :: repeat (1, 2) 595550 ++ (233769, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) 1)).
  {
    apply (sTRANS2_1 [7498; 1059; 199; 101; 0] 12570 8743 1 (repeat (1, 2) 51689 ++ (263502, 2) :: (1, 1) :: repeat (1, 2) 595550 ++ (233769, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) 1); closearith.
  }
  (* step 636: M pop12 (51689,) *)
  apply (hsteps_trans _ (HB [12571; 7498; 1059; 199; 101; 0] 60434 1 103381 ((263502, 2) :: (1, 1) :: repeat (1, 2) 595550 ++ (233769, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) 1)).
  {
    apply (pop12 51689 [12571; 7498; 1059; 199; 101; 0] 8745 3 ((263502, 2) :: (1, 1) :: repeat (1, 2) 595550 ++ (233769, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) 1); closearith.
  }
  (* step 637: sTUP *)
  apply (hsteps_trans _ (HC [12571; 7498; 1059; 199; 101; 0] 60434 103380 2 ((263500, 2) :: (1, 1) :: repeat (1, 2) 595550 ++ (233769, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) 1)).
  {
    rewrite NUM56X24.
    rewrite NUM56X25.
    apply (sTUP [12571; 7498; 1059; 199; 101; 0] 60434 103381 263502 2 ((1, 1) :: repeat (1, 2) 595550 ++ (233769, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) 1); closearith.
  }
  (* step 638: hGRIND_even 51688 *)
  apply (hsteps_trans _ (HB [12571; 7498; 1059; 199; 101; 0] 60433 1 103380 ((2, 2) :: (263500, 2) :: (1, 1) :: repeat (1, 2) 595550 ++ (233769, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) 1)).
  {
    rewrite NUM56X26.
    apply (hGRIND_even 51688 [12571; 7498; 1059; 199; 101; 0] 60433 ((263500, 2) :: (1, 1) :: repeat (1, 2) 595550 ++ (233769, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) 1); closearith.
  }
  (* step 639: P TUP2_1 *)
  apply (hsteps_trans _ (HC [60434; 12571; 7498; 1059; 199; 101; 0] 103380 1 2 ((263498, 2) :: (1, 1) :: repeat (1, 2) 595550 ++ (233769, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) 1)).
  {
    rewrite NUM56X27.
    rewrite NUM56X28.
    apply (sTUP2_1 [12571; 7498; 1059; 199; 101; 0] 60433 103379 263500 ((1, 1) :: repeat (1, 2) 595550 ++ (233769, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) 1); closearith.
  }
  (* step 640: P TDN *)
  apply (hsteps_trans _ (HB [60434; 12571; 7498; 1059; 199; 101; 0] 103380 1 4 ((263498, 2) :: (1, 1) :: repeat (1, 2) 595550 ++ (233769, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) 1)).
  {
    apply (sTDN [60434; 12571; 7498; 1059; 199; 101; 0] 103380 ((263498, 2) :: (1, 1) :: repeat (1, 2) 595550 ++ (233769, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) 1).
  }
  (* step 641: sTUP *)
  apply (hsteps_trans _ (HC [60434; 12571; 7498; 1059; 199; 101; 0] 103380 3 2 ((263496, 2) :: (1, 1) :: repeat (1, 2) 595550 ++ (233769, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) 1)).
  {
    rewrite NUM56X29.
    apply (sTUP [60434; 12571; 7498; 1059; 199; 101; 0] 103380 4 263498 2 ((1, 1) :: repeat (1, 2) 595550 ++ (233769, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) 1); closearith.
  }
  (* step 642: DIPGRIND 103380 56736 *)
  apply (hsteps_trans _ (HC [60434; 12571; 7498; 1059; 199; 101; 0] 0 3 2 (repeat (1, 2) 103380 ++ (56736, 2) :: (1, 1) :: repeat (1, 2) 595550 ++ (233769, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) 1)).
  {
    rewrite NUM56X30.
    apply (DIPGRIND 103380 56736 [60434; 12571; 7498; 1059; 199; 101; 0] ((1, 1) :: repeat (1, 2) 595550 ++ (233769, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) 1); closearith.
  }
  (* step 643: P PX2A *)
  apply (hsteps_trans _ (HC [7498; 1059; 199; 101; 0] 12570 60432 2 ((1, 1) :: repeat (1, 2) 103382 ++ (56736, 2) :: (1, 1) :: repeat (1, 2) 595550 ++ (233769, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) 1)).
  {
    exact (hsteps_step _ _ _ (hPX2A 60431 12570 [7498; 1059; 199; 101; 0] (repeat (1, 2) 103380 ++ (56736, 2) :: (1, 1) :: repeat (1, 2) 595550 ++ (233769, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) 1) (hsteps_refl _)).
  }
  (* step 644: P PUSH *)
  apply (hsteps_trans _ (HC [7498; 1059; 199; 101; 0] 12569 1 2 ((60430, 2) :: (1, 1) :: repeat (1, 2) 103382 ++ (56736, 2) :: (1, 1) :: repeat (1, 2) 595550 ++ (233769, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) 1)).
  {
    replace ((60430, 2) :: (1, 1) :: repeat (1, 2) 103382 ++ (56736, 2) :: (1, 1) :: repeat (1, 2) 595550 ++ (233769, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) with ((60432 - 2, 2) :: (1, 1) :: repeat (1, 2) 103382 ++ (56736, 2) :: (1, 1) :: repeat (1, 2) 595550 ++ (233769, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) by sec_eq.
    apply (sPUSH [7498; 1059; 199; 101; 0] 12569 60432 ((1, 1) :: repeat (1, 2) 103382 ++ (56736, 2) :: (1, 1) :: repeat (1, 2) 595550 ++ (233769, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) 1); closearith.
  }
  (* step 645: P TDN *)
  apply (hsteps_trans _ (HB [7498; 1059; 199; 101; 0] 12569 1 4 ((60430, 2) :: (1, 1) :: repeat (1, 2) 103382 ++ (56736, 2) :: (1, 1) :: repeat (1, 2) 595550 ++ (233769, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) 1)).
  {
    apply (sTDN [7498; 1059; 199; 101; 0] 12569 ((60430, 2) :: (1, 1) :: repeat (1, 2) 103382 ++ (56736, 2) :: (1, 1) :: repeat (1, 2) 595550 ++ (233769, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) 1).
  }
  (* step 646: sTUP *)
  apply (hsteps_trans _ (HC [7498; 1059; 199; 101; 0] 12569 3 2 ((60428, 2) :: (1, 1) :: repeat (1, 2) 103382 ++ (56736, 2) :: (1, 1) :: repeat (1, 2) 595550 ++ (233769, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) 1)).
  {
    replace ((60428, 2) :: (1, 1) :: repeat (1, 2) 103382 ++ (56736, 2) :: (1, 1) :: repeat (1, 2) 595550 ++ (233769, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) with ((60430 - 2, 2) :: (1, 1) :: repeat (1, 2) 103382 ++ (56736, 2) :: (1, 1) :: repeat (1, 2) 595550 ++ (233769, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) by sec_eq.
    apply (sTUP [7498; 1059; 199; 101; 0] 12569 4 60430 2 ((1, 1) :: repeat (1, 2) 103382 ++ (56736, 2) :: (1, 1) :: repeat (1, 2) 595550 ++ (233769, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) 1); closearith.
  }
  (* step 647: DIPGRIND 12569 35290 *)
  apply (hsteps_trans _ (HC [7498; 1059; 199; 101; 0] 0 3 2 (repeat (1, 2) 12569 ++ (35290, 2) :: (1, 1) :: repeat (1, 2) 103382 ++ (56736, 2) :: (1, 1) :: repeat (1, 2) 595550 ++ (233769, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) 1)).
  {
    apply (DIPGRIND 12569 35290 [7498; 1059; 199; 101; 0] ((1, 1) :: repeat (1, 2) 103382 ++ (56736, 2) :: (1, 1) :: repeat (1, 2) 595550 ++ (233769, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) 1); closearith.
  }
  (* step 648: P PX2A *)
  apply (hsteps_trans _ (HC [199; 101; 0] 1058 7496 2 ((1, 1) :: repeat (1, 2) 12571 ++ (35290, 2) :: (1, 1) :: repeat (1, 2) 103382 ++ (56736, 2) :: (1, 1) :: repeat (1, 2) 595550 ++ (233769, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) 1)).
  {
    exact (hsteps_step _ _ _ (hPX2A 7495 1058 [199; 101; 0] (repeat (1, 2) 12569 ++ (35290, 2) :: (1, 1) :: repeat (1, 2) 103382 ++ (56736, 2) :: (1, 1) :: repeat (1, 2) 595550 ++ (233769, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) 1) (hsteps_refl _)).
  }
  (* step 649: P PUSH *)
  apply (hsteps_trans _ (HC [199; 101; 0] 1057 1 2 ((7494, 2) :: (1, 1) :: repeat (1, 2) 12571 ++ (35290, 2) :: (1, 1) :: repeat (1, 2) 103382 ++ (56736, 2) :: (1, 1) :: repeat (1, 2) 595550 ++ (233769, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) 1)).
  {
    replace ((7494, 2) :: (1, 1) :: repeat (1, 2) 12571 ++ (35290, 2) :: (1, 1) :: repeat (1, 2) 103382 ++ (56736, 2) :: (1, 1) :: repeat (1, 2) 595550 ++ (233769, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) with ((7496 - 2, 2) :: (1, 1) :: repeat (1, 2) 12571 ++ (35290, 2) :: (1, 1) :: repeat (1, 2) 103382 ++ (56736, 2) :: (1, 1) :: repeat (1, 2) 595550 ++ (233769, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) by sec_eq.
    apply (sPUSH [199; 101; 0] 1057 7496 ((1, 1) :: repeat (1, 2) 12571 ++ (35290, 2) :: (1, 1) :: repeat (1, 2) 103382 ++ (56736, 2) :: (1, 1) :: repeat (1, 2) 595550 ++ (233769, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) 1); closearith.
  }
  (* step 650: P TDN *)
  apply (hsteps_trans _ (HB [199; 101; 0] 1057 1 4 ((7494, 2) :: (1, 1) :: repeat (1, 2) 12571 ++ (35290, 2) :: (1, 1) :: repeat (1, 2) 103382 ++ (56736, 2) :: (1, 1) :: repeat (1, 2) 595550 ++ (233769, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) 1)).
  {
    apply (sTDN [199; 101; 0] 1057 ((7494, 2) :: (1, 1) :: repeat (1, 2) 12571 ++ (35290, 2) :: (1, 1) :: repeat (1, 2) 103382 ++ (56736, 2) :: (1, 1) :: repeat (1, 2) 595550 ++ (233769, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) 1).
  }
  (* step 651: sTUP *)
  apply (hsteps_trans _ (HC [199; 101; 0] 1057 3 2 ((7492, 2) :: (1, 1) :: repeat (1, 2) 12571 ++ (35290, 2) :: (1, 1) :: repeat (1, 2) 103382 ++ (56736, 2) :: (1, 1) :: repeat (1, 2) 595550 ++ (233769, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) 1)).
  {
    replace ((7492, 2) :: (1, 1) :: repeat (1, 2) 12571 ++ (35290, 2) :: (1, 1) :: repeat (1, 2) 103382 ++ (56736, 2) :: (1, 1) :: repeat (1, 2) 595550 ++ (233769, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) with ((7494 - 2, 2) :: (1, 1) :: repeat (1, 2) 12571 ++ (35290, 2) :: (1, 1) :: repeat (1, 2) 103382 ++ (56736, 2) :: (1, 1) :: repeat (1, 2) 595550 ++ (233769, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) by sec_eq.
    apply (sTUP [199; 101; 0] 1057 4 7494 2 ((1, 1) :: repeat (1, 2) 12571 ++ (35290, 2) :: (1, 1) :: repeat (1, 2) 103382 ++ (56736, 2) :: (1, 1) :: repeat (1, 2) 595550 ++ (233769, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) 1); closearith.
  }
  (* step 652: DIPGRIND 1057 5378 *)
  apply (hsteps_trans _ (HC [199; 101; 0] 0 3 2 (repeat (1, 2) 1057 ++ (5378, 2) :: (1, 1) :: repeat (1, 2) 12571 ++ (35290, 2) :: (1, 1) :: repeat (1, 2) 103382 ++ (56736, 2) :: (1, 1) :: repeat (1, 2) 595550 ++ (233769, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) 1)).
  {
    apply (DIPGRIND 1057 5378 [199; 101; 0] ((1, 1) :: repeat (1, 2) 12571 ++ (35290, 2) :: (1, 1) :: repeat (1, 2) 103382 ++ (56736, 2) :: (1, 1) :: repeat (1, 2) 595550 ++ (233769, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) 1); closearith.
  }
  (* step 653: P PX2A *)
  apply (hsteps_trans _ (HC [0] 100 197 2 ((1, 1) :: repeat (1, 2) 1059 ++ (5378, 2) :: (1, 1) :: repeat (1, 2) 12571 ++ (35290, 2) :: (1, 1) :: repeat (1, 2) 103382 ++ (56736, 2) :: (1, 1) :: repeat (1, 2) 595550 ++ (233769, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) 1)).
  {
    exact (hsteps_step _ _ _ (hPX2A 196 100 [0] (repeat (1, 2) 1057 ++ (5378, 2) :: (1, 1) :: repeat (1, 2) 12571 ++ (35290, 2) :: (1, 1) :: repeat (1, 2) 103382 ++ (56736, 2) :: (1, 1) :: repeat (1, 2) 595550 ++ (233769, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) 1) (hsteps_refl _)).
  }
  (* step 654: hGRIND 97 *)
  apply (hsteps_trans _ (HB [0] 100 1 200 ((1, 1) :: repeat (1, 2) 1059 ++ (5378, 2) :: (1, 1) :: repeat (1, 2) 12571 ++ (35290, 2) :: (1, 1) :: repeat (1, 2) 103382 ++ (56736, 2) :: (1, 1) :: repeat (1, 2) 595550 ++ (233769, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) 1)).
  {
    apply (hGRIND 97 [0] 100 ((1, 1) :: repeat (1, 2) 1059 ++ (5378, 2) :: (1, 1) :: repeat (1, 2) 12571 ++ (35290, 2) :: (1, 1) :: repeat (1, 2) 103382 ++ (56736, 2) :: (1, 1) :: repeat (1, 2) 595550 ++ (233769, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) 1); closearith.
  }
  (* step 655: P POP *)
  apply (hsteps_trans _ (HB [0] 101 1 201 (repeat (1, 2) 1059 ++ (5378, 2) :: (1, 1) :: repeat (1, 2) 12571 ++ (35290, 2) :: (1, 1) :: repeat (1, 2) 103382 ++ (56736, 2) :: (1, 1) :: repeat (1, 2) 595550 ++ (233769, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) 1)).
  {
    apply (sPOP1 [0] 100 200 (repeat (1, 2) 1059 ++ (5378, 2) :: (1, 1) :: repeat (1, 2) 12571 ++ (35290, 2) :: (1, 1) :: repeat (1, 2) 103382 ++ (56736, 2) :: (1, 1) :: repeat (1, 2) 595550 ++ (233769, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) 1); closearith.
  }
  (* step 656: M pop12 (1059,) *)
  apply (hsteps_trans _ (HB [0] 1160 1 2319 ((5378, 2) :: (1, 1) :: repeat (1, 2) 12571 ++ (35290, 2) :: (1, 1) :: repeat (1, 2) 103382 ++ (56736, 2) :: (1, 1) :: repeat (1, 2) 595550 ++ (233769, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) 1)).
  {
    apply (pop12 1059 [0] 101 201 ((5378, 2) :: (1, 1) :: repeat (1, 2) 12571 ++ (35290, 2) :: (1, 1) :: repeat (1, 2) 103382 ++ (56736, 2) :: (1, 1) :: repeat (1, 2) 595550 ++ (233769, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) 1); closearith.
  }
  (* step 657: sTUP *)
  apply (hsteps_trans _ (HC [0] 1160 2318 2 ((5376, 2) :: (1, 1) :: repeat (1, 2) 12571 ++ (35290, 2) :: (1, 1) :: repeat (1, 2) 103382 ++ (56736, 2) :: (1, 1) :: repeat (1, 2) 595550 ++ (233769, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) 1)).
  {
    replace ((5376, 2) :: (1, 1) :: repeat (1, 2) 12571 ++ (35290, 2) :: (1, 1) :: repeat (1, 2) 103382 ++ (56736, 2) :: (1, 1) :: repeat (1, 2) 595550 ++ (233769, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) with ((5378 - 2, 2) :: (1, 1) :: repeat (1, 2) 12571 ++ (35290, 2) :: (1, 1) :: repeat (1, 2) 103382 ++ (56736, 2) :: (1, 1) :: repeat (1, 2) 595550 ++ (233769, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) by sec_eq.
    apply (sTUP [0] 1160 2319 5378 2 ((1, 1) :: repeat (1, 2) 12571 ++ (35290, 2) :: (1, 1) :: repeat (1, 2) 103382 ++ (56736, 2) :: (1, 1) :: repeat (1, 2) 595550 ++ (233769, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) 1); closearith.
  }
  (* step 658: hGRIND_even 1157 *)
  apply (hsteps_trans _ (HB [0] 1159 1 2318 ((2, 2) :: (5376, 2) :: (1, 1) :: repeat (1, 2) 12571 ++ (35290, 2) :: (1, 1) :: repeat (1, 2) 103382 ++ (56736, 2) :: (1, 1) :: repeat (1, 2) 595550 ++ (233769, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) 1)).
  {
    apply (hGRIND_even 1157 [0] 1159 ((5376, 2) :: (1, 1) :: repeat (1, 2) 12571 ++ (35290, 2) :: (1, 1) :: repeat (1, 2) 103382 ++ (56736, 2) :: (1, 1) :: repeat (1, 2) 595550 ++ (233769, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) 1); closearith.
  }
  (* step 659: P TUP2_1 *)
  apply (hsteps_trans _ (HC [1160; 0] 2318 1 2 ((5374, 2) :: (1, 1) :: repeat (1, 2) 12571 ++ (35290, 2) :: (1, 1) :: repeat (1, 2) 103382 ++ (56736, 2) :: (1, 1) :: repeat (1, 2) 595550 ++ (233769, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) 1)).
  {
    replace ((5374, 2) :: (1, 1) :: repeat (1, 2) 12571 ++ (35290, 2) :: (1, 1) :: repeat (1, 2) 103382 ++ (56736, 2) :: (1, 1) :: repeat (1, 2) 595550 ++ (233769, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) with ((5376 - 2, 2) :: (1, 1) :: repeat (1, 2) 12571 ++ (35290, 2) :: (1, 1) :: repeat (1, 2) 103382 ++ (56736, 2) :: (1, 1) :: repeat (1, 2) 595550 ++ (233769, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) by sec_eq.
    apply (sTUP2_1 [0] 1159 2317 5376 ((1, 1) :: repeat (1, 2) 12571 ++ (35290, 2) :: (1, 1) :: repeat (1, 2) 103382 ++ (56736, 2) :: (1, 1) :: repeat (1, 2) 595550 ++ (233769, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) 1); closearith.
  }
  (* step 660: P TDN *)
  apply (hsteps_trans _ (HB [1160; 0] 2318 1 4 ((5374, 2) :: (1, 1) :: repeat (1, 2) 12571 ++ (35290, 2) :: (1, 1) :: repeat (1, 2) 103382 ++ (56736, 2) :: (1, 1) :: repeat (1, 2) 595550 ++ (233769, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) 1)).
  {
    apply (sTDN [1160; 0] 2318 ((5374, 2) :: (1, 1) :: repeat (1, 2) 12571 ++ (35290, 2) :: (1, 1) :: repeat (1, 2) 103382 ++ (56736, 2) :: (1, 1) :: repeat (1, 2) 595550 ++ (233769, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) 1).
  }
  (* step 661: sTUP *)
  apply (hsteps_trans _ (HC [1160; 0] 2318 3 2 ((5372, 2) :: (1, 1) :: repeat (1, 2) 12571 ++ (35290, 2) :: (1, 1) :: repeat (1, 2) 103382 ++ (56736, 2) :: (1, 1) :: repeat (1, 2) 595550 ++ (233769, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) 1)).
  {
    replace ((5372, 2) :: (1, 1) :: repeat (1, 2) 12571 ++ (35290, 2) :: (1, 1) :: repeat (1, 2) 103382 ++ (56736, 2) :: (1, 1) :: repeat (1, 2) 595550 ++ (233769, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) with ((5374 - 2, 2) :: (1, 1) :: repeat (1, 2) 12571 ++ (35290, 2) :: (1, 1) :: repeat (1, 2) 103382 ++ (56736, 2) :: (1, 1) :: repeat (1, 2) 595550 ++ (233769, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) by sec_eq.
    apply (sTUP [1160; 0] 2318 4 5374 2 ((1, 1) :: repeat (1, 2) 12571 ++ (35290, 2) :: (1, 1) :: repeat (1, 2) 103382 ++ (56736, 2) :: (1, 1) :: repeat (1, 2) 595550 ++ (233769, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) 1); closearith.
  }
  (* step 662: DIPGRIND 2318 736 *)
  apply (hsteps_trans _ (HC [1160; 0] 0 3 2 (repeat (1, 2) 2318 ++ (736, 2) :: (1, 1) :: repeat (1, 2) 12571 ++ (35290, 2) :: (1, 1) :: repeat (1, 2) 103382 ++ (56736, 2) :: (1, 1) :: repeat (1, 2) 595550 ++ (233769, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) 1)).
  {
    apply (DIPGRIND 2318 736 [1160; 0] ((1, 1) :: repeat (1, 2) 12571 ++ (35290, 2) :: (1, 1) :: repeat (1, 2) 103382 ++ (56736, 2) :: (1, 1) :: repeat (1, 2) 595550 ++ (233769, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) 1); closearith.
  }
  (* step 663: P PX2A0 *)
  apply (hsteps_trans _ (HB [0] 3 1 2 ((1156, 2) :: (1, 1) :: repeat (1, 2) 2320 ++ (736, 2) :: (1, 1) :: repeat (1, 2) 12571 ++ (35290, 2) :: (1, 1) :: repeat (1, 2) 103382 ++ (56736, 2) :: (1, 1) :: repeat (1, 2) 595550 ++ (233769, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) 1)).
  {
    exact (hsteps_step _ _ _ (hPX2A0 1155 (repeat (1, 2) 2318 ++ (736, 2) :: (1, 1) :: repeat (1, 2) 12571 ++ (35290, 2) :: (1, 1) :: repeat (1, 2) 103382 ++ (56736, 2) :: (1, 1) :: repeat (1, 2) 595550 ++ (233769, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) 1) (hsteps_refl _)).
  }
  (* step 664: sTUP *)
  apply (hsteps_trans _ (HC [0] 3 1 2 ((1154, 2) :: (1, 1) :: repeat (1, 2) 2320 ++ (736, 2) :: (1, 1) :: repeat (1, 2) 12571 ++ (35290, 2) :: (1, 1) :: repeat (1, 2) 103382 ++ (56736, 2) :: (1, 1) :: repeat (1, 2) 595550 ++ (233769, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) 1)).
  {
    replace ((1154, 2) :: (1, 1) :: repeat (1, 2) 2320 ++ (736, 2) :: (1, 1) :: repeat (1, 2) 12571 ++ (35290, 2) :: (1, 1) :: repeat (1, 2) 103382 ++ (56736, 2) :: (1, 1) :: repeat (1, 2) 595550 ++ (233769, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) with ((1156 - 2, 2) :: (1, 1) :: repeat (1, 2) 2320 ++ (736, 2) :: (1, 1) :: repeat (1, 2) 12571 ++ (35290, 2) :: (1, 1) :: repeat (1, 2) 103382 ++ (56736, 2) :: (1, 1) :: repeat (1, 2) 595550 ++ (233769, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) by sec_eq.
    apply (sTUP [0] 3 2 1156 2 ((1, 1) :: repeat (1, 2) 2320 ++ (736, 2) :: (1, 1) :: repeat (1, 2) 12571 ++ (35290, 2) :: (1, 1) :: repeat (1, 2) 103382 ++ (56736, 2) :: (1, 1) :: repeat (1, 2) 595550 ++ (233769, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) 1); closearith.
  }
  (* step 665: P TDN *)
  apply (hsteps_trans _ (HB [0] 3 1 4 ((1154, 2) :: (1, 1) :: repeat (1, 2) 2320 ++ (736, 2) :: (1, 1) :: repeat (1, 2) 12571 ++ (35290, 2) :: (1, 1) :: repeat (1, 2) 103382 ++ (56736, 2) :: (1, 1) :: repeat (1, 2) 595550 ++ (233769, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) 1)).
  {
    apply (sTDN [0] 3 ((1154, 2) :: (1, 1) :: repeat (1, 2) 2320 ++ (736, 2) :: (1, 1) :: repeat (1, 2) 12571 ++ (35290, 2) :: (1, 1) :: repeat (1, 2) 103382 ++ (56736, 2) :: (1, 1) :: repeat (1, 2) 595550 ++ (233769, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) 1).
  }
  (* step 666: sTUP *)
  apply (hsteps_trans _ (HC [0] 3 3 2 ((1152, 2) :: (1, 1) :: repeat (1, 2) 2320 ++ (736, 2) :: (1, 1) :: repeat (1, 2) 12571 ++ (35290, 2) :: (1, 1) :: repeat (1, 2) 103382 ++ (56736, 2) :: (1, 1) :: repeat (1, 2) 595550 ++ (233769, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) 1)).
  {
    replace ((1152, 2) :: (1, 1) :: repeat (1, 2) 2320 ++ (736, 2) :: (1, 1) :: repeat (1, 2) 12571 ++ (35290, 2) :: (1, 1) :: repeat (1, 2) 103382 ++ (56736, 2) :: (1, 1) :: repeat (1, 2) 595550 ++ (233769, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) with ((1154 - 2, 2) :: (1, 1) :: repeat (1, 2) 2320 ++ (736, 2) :: (1, 1) :: repeat (1, 2) 12571 ++ (35290, 2) :: (1, 1) :: repeat (1, 2) 103382 ++ (56736, 2) :: (1, 1) :: repeat (1, 2) 595550 ++ (233769, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) by sec_eq.
    apply (sTUP [0] 3 4 1154 2 ((1, 1) :: repeat (1, 2) 2320 ++ (736, 2) :: (1, 1) :: repeat (1, 2) 12571 ++ (35290, 2) :: (1, 1) :: repeat (1, 2) 103382 ++ (56736, 2) :: (1, 1) :: repeat (1, 2) 595550 ++ (233769, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) 1); closearith.
  }
  (* step 667: DIPGRIND 3 1146 *)
  apply (hsteps_trans _ (HC [0] 0 3 2 (repeat (1, 2) 3 ++ (1146, 2) :: (1, 1) :: repeat (1, 2) 2320 ++ (736, 2) :: (1, 1) :: repeat (1, 2) 12571 ++ (35290, 2) :: (1, 1) :: repeat (1, 2) 103382 ++ (56736, 2) :: (1, 1) :: repeat (1, 2) 595550 ++ (233769, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) 1)).
  {
    apply (DIPGRIND 3 1146 [0] ((1, 1) :: repeat (1, 2) 2320 ++ (736, 2) :: (1, 1) :: repeat (1, 2) 12571 ++ (35290, 2) :: (1, 1) :: repeat (1, 2) 103382 ++ (56736, 2) :: (1, 1) :: repeat (1, 2) 595550 ++ (233769, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) 1); closearith.
  }
  (* step 668: P PX2B0 *)
  apply (hsteps_trans _ (HB [] 0 1 5 (repeat (1, 2) 4 ++ (1146, 2) :: (1, 1) :: repeat (1, 2) 2320 ++ (736, 2) :: (1, 1) :: repeat (1, 2) 12571 ++ (35290, 2) :: (1, 1) :: repeat (1, 2) 103382 ++ (56736, 2) :: (1, 1) :: repeat (1, 2) 595550 ++ (233769, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) 1)).
  {
    exact (hsteps_step _ _ _ (hPX2B0 (repeat (1, 2) 3 ++ (1146, 2) :: (1, 1) :: repeat (1, 2) 2320 ++ (736, 2) :: (1, 1) :: repeat (1, 2) 12571 ++ (35290, 2) :: (1, 1) :: repeat (1, 2) 103382 ++ (56736, 2) :: (1, 1) :: repeat (1, 2) 595550 ++ (233769, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) 1) (hsteps_refl _)).
  }
  (* step 669: M pop12 (4,) *)
  apply (hsteps_trans _ (HB [] 4 1 13 ((1146, 2) :: (1, 1) :: repeat (1, 2) 2320 ++ (736, 2) :: (1, 1) :: repeat (1, 2) 12571 ++ (35290, 2) :: (1, 1) :: repeat (1, 2) 103382 ++ (56736, 2) :: (1, 1) :: repeat (1, 2) 595550 ++ (233769, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) 1)).
  {
    apply (pop12 4 [] 0 5 ((1146, 2) :: (1, 1) :: repeat (1, 2) 2320 ++ (736, 2) :: (1, 1) :: repeat (1, 2) 12571 ++ (35290, 2) :: (1, 1) :: repeat (1, 2) 103382 ++ (56736, 2) :: (1, 1) :: repeat (1, 2) 595550 ++ (233769, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) 1); closearith.
  }
  (* step 670: sTUP *)
  apply (hsteps_trans _ (HC [] 4 12 2 ((1144, 2) :: (1, 1) :: repeat (1, 2) 2320 ++ (736, 2) :: (1, 1) :: repeat (1, 2) 12571 ++ (35290, 2) :: (1, 1) :: repeat (1, 2) 103382 ++ (56736, 2) :: (1, 1) :: repeat (1, 2) 595550 ++ (233769, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) 1)).
  {
    replace ((1144, 2) :: (1, 1) :: repeat (1, 2) 2320 ++ (736, 2) :: (1, 1) :: repeat (1, 2) 12571 ++ (35290, 2) :: (1, 1) :: repeat (1, 2) 103382 ++ (56736, 2) :: (1, 1) :: repeat (1, 2) 595550 ++ (233769, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) with ((1146 - 2, 2) :: (1, 1) :: repeat (1, 2) 2320 ++ (736, 2) :: (1, 1) :: repeat (1, 2) 12571 ++ (35290, 2) :: (1, 1) :: repeat (1, 2) 103382 ++ (56736, 2) :: (1, 1) :: repeat (1, 2) 595550 ++ (233769, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) by sec_eq.
    apply (sTUP [] 4 13 1146 2 ((1, 1) :: repeat (1, 2) 2320 ++ (736, 2) :: (1, 1) :: repeat (1, 2) 12571 ++ (35290, 2) :: (1, 1) :: repeat (1, 2) 103382 ++ (56736, 2) :: (1, 1) :: repeat (1, 2) 595550 ++ (233769, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) 1); closearith.
  }
  (* step 671: P PUSH *)
  apply (hsteps_trans _ (HC [] 3 1 2 ((10, 2) :: (1144, 2) :: (1, 1) :: repeat (1, 2) 2320 ++ (736, 2) :: (1, 1) :: repeat (1, 2) 12571 ++ (35290, 2) :: (1, 1) :: repeat (1, 2) 103382 ++ (56736, 2) :: (1, 1) :: repeat (1, 2) 595550 ++ (233769, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) 1)).
  {
    replace ((10, 2) :: (1144, 2) :: (1, 1) :: repeat (1, 2) 2320 ++ (736, 2) :: (1, 1) :: repeat (1, 2) 12571 ++ (35290, 2) :: (1, 1) :: repeat (1, 2) 103382 ++ (56736, 2) :: (1, 1) :: repeat (1, 2) 595550 ++ (233769, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) with ((12 - 2, 2) :: (1144, 2) :: (1, 1) :: repeat (1, 2) 2320 ++ (736, 2) :: (1, 1) :: repeat (1, 2) 12571 ++ (35290, 2) :: (1, 1) :: repeat (1, 2) 103382 ++ (56736, 2) :: (1, 1) :: repeat (1, 2) 595550 ++ (233769, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) by sec_eq.
    apply (sPUSH [] 3 12 ((1144, 2) :: (1, 1) :: repeat (1, 2) 2320 ++ (736, 2) :: (1, 1) :: repeat (1, 2) 12571 ++ (35290, 2) :: (1, 1) :: repeat (1, 2) 103382 ++ (56736, 2) :: (1, 1) :: repeat (1, 2) 595550 ++ (233769, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) 1); closearith.
  }
  (* step 672: P TDN *)
  apply (hsteps_trans _ (HB [] 3 1 4 ((10, 2) :: (1144, 2) :: (1, 1) :: repeat (1, 2) 2320 ++ (736, 2) :: (1, 1) :: repeat (1, 2) 12571 ++ (35290, 2) :: (1, 1) :: repeat (1, 2) 103382 ++ (56736, 2) :: (1, 1) :: repeat (1, 2) 595550 ++ (233769, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) 1)).
  {
    apply (sTDN [] 3 ((10, 2) :: (1144, 2) :: (1, 1) :: repeat (1, 2) 2320 ++ (736, 2) :: (1, 1) :: repeat (1, 2) 12571 ++ (35290, 2) :: (1, 1) :: repeat (1, 2) 103382 ++ (56736, 2) :: (1, 1) :: repeat (1, 2) 595550 ++ (233769, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) 1).
  }
  (* step 673: sTUP *)
  apply (hsteps_trans _ (HC [] 3 3 2 ((8, 2) :: (1144, 2) :: (1, 1) :: repeat (1, 2) 2320 ++ (736, 2) :: (1, 1) :: repeat (1, 2) 12571 ++ (35290, 2) :: (1, 1) :: repeat (1, 2) 103382 ++ (56736, 2) :: (1, 1) :: repeat (1, 2) 595550 ++ (233769, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) 1)).
  {
    replace ((8, 2) :: (1144, 2) :: (1, 1) :: repeat (1, 2) 2320 ++ (736, 2) :: (1, 1) :: repeat (1, 2) 12571 ++ (35290, 2) :: (1, 1) :: repeat (1, 2) 103382 ++ (56736, 2) :: (1, 1) :: repeat (1, 2) 595550 ++ (233769, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) with ((10 - 2, 2) :: (1144, 2) :: (1, 1) :: repeat (1, 2) 2320 ++ (736, 2) :: (1, 1) :: repeat (1, 2) 12571 ++ (35290, 2) :: (1, 1) :: repeat (1, 2) 103382 ++ (56736, 2) :: (1, 1) :: repeat (1, 2) 595550 ++ (233769, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) by sec_eq.
    apply (sTUP [] 3 4 10 2 ((1144, 2) :: (1, 1) :: repeat (1, 2) 2320 ++ (736, 2) :: (1, 1) :: repeat (1, 2) 12571 ++ (35290, 2) :: (1, 1) :: repeat (1, 2) 103382 ++ (56736, 2) :: (1, 1) :: repeat (1, 2) 595550 ++ (233769, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) 1); closearith.
  }
  (* step 674: DIPGRIND 3 2 *)
  apply (hsteps_trans _ (HC [] 0 3 2 (repeat (1, 2) 3 ++ (2, 2) :: (1144, 2) :: (1, 1) :: repeat (1, 2) 2320 ++ (736, 2) :: (1, 1) :: repeat (1, 2) 12571 ++ (35290, 2) :: (1, 1) :: repeat (1, 2) 103382 ++ (56736, 2) :: (1, 1) :: repeat (1, 2) 595550 ++ (233769, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) 1)).
  {
    apply (DIPGRIND 3 2 [] ((1144, 2) :: (1, 1) :: repeat (1, 2) 2320 ++ (736, 2) :: (1, 1) :: repeat (1, 2) 12571 ++ (35290, 2) :: (1, 1) :: repeat (1, 2) 103382 ++ (56736, 2) :: (1, 1) :: repeat (1, 2) 595550 ++ (233769, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) 1); closearith.
  }
  (* step 675: P PUSHX *)
  apply (hsteps_trans _ (HB [] 1 1 7 (repeat (1, 2) 3 ++ (2, 2) :: (1144, 2) :: (1, 1) :: repeat (1, 2) 2320 ++ (736, 2) :: (1, 1) :: repeat (1, 2) 12571 ++ (35290, 2) :: (1, 1) :: repeat (1, 2) 103382 ++ (56736, 2) :: (1, 1) :: repeat (1, 2) 595550 ++ (233769, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) 1)).
  {
    exact (hsteps_step _ _ _ (hPUSHX (repeat (1, 2) 3 ++ (2, 2) :: (1144, 2) :: (1, 1) :: repeat (1, 2) 2320 ++ (736, 2) :: (1, 1) :: repeat (1, 2) 12571 ++ (35290, 2) :: (1, 1) :: repeat (1, 2) 103382 ++ (56736, 2) :: (1, 1) :: repeat (1, 2) 595550 ++ (233769, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) 1) (hsteps_refl _)).
  }
  (* step 676: M pop12 (3,) *)
  apply (hsteps_trans _ (HB [] 4 1 13 ((2, 2) :: (1144, 2) :: (1, 1) :: repeat (1, 2) 2320 ++ (736, 2) :: (1, 1) :: repeat (1, 2) 12571 ++ (35290, 2) :: (1, 1) :: repeat (1, 2) 103382 ++ (56736, 2) :: (1, 1) :: repeat (1, 2) 595550 ++ (233769, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) 1)).
  {
    apply (pop12 3 [] 1 7 ((2, 2) :: (1144, 2) :: (1, 1) :: repeat (1, 2) 2320 ++ (736, 2) :: (1, 1) :: repeat (1, 2) 12571 ++ (35290, 2) :: (1, 1) :: repeat (1, 2) 103382 ++ (56736, 2) :: (1, 1) :: repeat (1, 2) 595550 ++ (233769, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) 1); closearith.
  }
  (* step 677: P TUP2_1 *)
  apply (hsteps_trans _ (HC [5] 13 1 2 ((1142, 2) :: (1, 1) :: repeat (1, 2) 2320 ++ (736, 2) :: (1, 1) :: repeat (1, 2) 12571 ++ (35290, 2) :: (1, 1) :: repeat (1, 2) 103382 ++ (56736, 2) :: (1, 1) :: repeat (1, 2) 595550 ++ (233769, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) 1)).
  {
    replace ((1142, 2) :: (1, 1) :: repeat (1, 2) 2320 ++ (736, 2) :: (1, 1) :: repeat (1, 2) 12571 ++ (35290, 2) :: (1, 1) :: repeat (1, 2) 103382 ++ (56736, 2) :: (1, 1) :: repeat (1, 2) 595550 ++ (233769, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) with ((1144 - 2, 2) :: (1, 1) :: repeat (1, 2) 2320 ++ (736, 2) :: (1, 1) :: repeat (1, 2) 12571 ++ (35290, 2) :: (1, 1) :: repeat (1, 2) 103382 ++ (56736, 2) :: (1, 1) :: repeat (1, 2) 595550 ++ (233769, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) by sec_eq.
    apply (sTUP2_1 [] 4 12 1144 ((1, 1) :: repeat (1, 2) 2320 ++ (736, 2) :: (1, 1) :: repeat (1, 2) 12571 ++ (35290, 2) :: (1, 1) :: repeat (1, 2) 103382 ++ (56736, 2) :: (1, 1) :: repeat (1, 2) 595550 ++ (233769, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) 1); closearith.
  }
  (* step 678: P TDN *)
  apply (hsteps_trans _ (HB [5] 13 1 4 ((1142, 2) :: (1, 1) :: repeat (1, 2) 2320 ++ (736, 2) :: (1, 1) :: repeat (1, 2) 12571 ++ (35290, 2) :: (1, 1) :: repeat (1, 2) 103382 ++ (56736, 2) :: (1, 1) :: repeat (1, 2) 595550 ++ (233769, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) 1)).
  {
    apply (sTDN [5] 13 ((1142, 2) :: (1, 1) :: repeat (1, 2) 2320 ++ (736, 2) :: (1, 1) :: repeat (1, 2) 12571 ++ (35290, 2) :: (1, 1) :: repeat (1, 2) 103382 ++ (56736, 2) :: (1, 1) :: repeat (1, 2) 595550 ++ (233769, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) 1).
  }
  (* step 679: sTUP *)
  apply (hsteps_trans _ (HC [5] 13 3 2 ((1140, 2) :: (1, 1) :: repeat (1, 2) 2320 ++ (736, 2) :: (1, 1) :: repeat (1, 2) 12571 ++ (35290, 2) :: (1, 1) :: repeat (1, 2) 103382 ++ (56736, 2) :: (1, 1) :: repeat (1, 2) 595550 ++ (233769, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) 1)).
  {
    replace ((1140, 2) :: (1, 1) :: repeat (1, 2) 2320 ++ (736, 2) :: (1, 1) :: repeat (1, 2) 12571 ++ (35290, 2) :: (1, 1) :: repeat (1, 2) 103382 ++ (56736, 2) :: (1, 1) :: repeat (1, 2) 595550 ++ (233769, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) with ((1142 - 2, 2) :: (1, 1) :: repeat (1, 2) 2320 ++ (736, 2) :: (1, 1) :: repeat (1, 2) 12571 ++ (35290, 2) :: (1, 1) :: repeat (1, 2) 103382 ++ (56736, 2) :: (1, 1) :: repeat (1, 2) 595550 ++ (233769, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) by sec_eq.
    apply (sTUP [5] 13 4 1142 2 ((1, 1) :: repeat (1, 2) 2320 ++ (736, 2) :: (1, 1) :: repeat (1, 2) 12571 ++ (35290, 2) :: (1, 1) :: repeat (1, 2) 103382 ++ (56736, 2) :: (1, 1) :: repeat (1, 2) 595550 ++ (233769, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) 1); closearith.
  }
  (* step 680: DIPGRIND 13 1114 *)
  apply (hsteps_trans _ (HC [5] 0 3 2 (repeat (1, 2) 13 ++ (1114, 2) :: (1, 1) :: repeat (1, 2) 2320 ++ (736, 2) :: (1, 1) :: repeat (1, 2) 12571 ++ (35290, 2) :: (1, 1) :: repeat (1, 2) 103382 ++ (56736, 2) :: (1, 1) :: repeat (1, 2) 595550 ++ (233769, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) 1)).
  {
    apply (DIPGRIND 13 1114 [5] ((1, 1) :: repeat (1, 2) 2320 ++ (736, 2) :: (1, 1) :: repeat (1, 2) 12571 ++ (35290, 2) :: (1, 1) :: repeat (1, 2) 103382 ++ (56736, 2) :: (1, 1) :: repeat (1, 2) 595550 ++ (233769, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) 1); closearith.
  }
  (* step 681: P PX2Bgen *)
  apply (hsteps_trans _ (HB [0] 3 1 2 (repeat (1, 2) 1 ++ (1, 1) :: repeat (1, 2) 15 ++ (1114, 2) :: (1, 1) :: repeat (1, 2) 2320 ++ (736, 2) :: (1, 1) :: repeat (1, 2) 12571 ++ (35290, 2) :: (1, 1) :: repeat (1, 2) 103382 ++ (56736, 2) :: (1, 1) :: repeat (1, 2) 595550 ++ (233769, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) 1)).
  {
    exact (hsteps_step _ _ _ (hPX2Bgen 0 (repeat (1, 2) 13 ++ (1114, 2) :: (1, 1) :: repeat (1, 2) 2320 ++ (736, 2) :: (1, 1) :: repeat (1, 2) 12571 ++ (35290, 2) :: (1, 1) :: repeat (1, 2) 103382 ++ (56736, 2) :: (1, 1) :: repeat (1, 2) 595550 ++ (233769, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) 1) (hsteps_refl _)).
  }
  (* step 682: M pop12 (1,) *)
  apply (hsteps_trans _ (HB [0] 4 1 4 ((1, 1) :: repeat (1, 2) 15 ++ (1114, 2) :: (1, 1) :: repeat (1, 2) 2320 ++ (736, 2) :: (1, 1) :: repeat (1, 2) 12571 ++ (35290, 2) :: (1, 1) :: repeat (1, 2) 103382 ++ (56736, 2) :: (1, 1) :: repeat (1, 2) 595550 ++ (233769, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) 1)).
  {
    apply (pop12 1 [0] 3 2 ((1, 1) :: repeat (1, 2) 15 ++ (1114, 2) :: (1, 1) :: repeat (1, 2) 2320 ++ (736, 2) :: (1, 1) :: repeat (1, 2) 12571 ++ (35290, 2) :: (1, 1) :: repeat (1, 2) 103382 ++ (56736, 2) :: (1, 1) :: repeat (1, 2) 595550 ++ (233769, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) 1); closearith.
  }
  (* step 683: P POP *)
  apply (hsteps_trans _ (HB [0] 5 1 5 (repeat (1, 2) 15 ++ (1114, 2) :: (1, 1) :: repeat (1, 2) 2320 ++ (736, 2) :: (1, 1) :: repeat (1, 2) 12571 ++ (35290, 2) :: (1, 1) :: repeat (1, 2) 103382 ++ (56736, 2) :: (1, 1) :: repeat (1, 2) 595550 ++ (233769, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) 1)).
  {
    apply (sPOP1 [0] 4 4 (repeat (1, 2) 15 ++ (1114, 2) :: (1, 1) :: repeat (1, 2) 2320 ++ (736, 2) :: (1, 1) :: repeat (1, 2) 12571 ++ (35290, 2) :: (1, 1) :: repeat (1, 2) 103382 ++ (56736, 2) :: (1, 1) :: repeat (1, 2) 595550 ++ (233769, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) 1); closearith.
  }
  (* step 684: M pop12 (15,) *)
  apply (hsteps_trans _ (HB [0] 20 1 35 ((1114, 2) :: (1, 1) :: repeat (1, 2) 2320 ++ (736, 2) :: (1, 1) :: repeat (1, 2) 12571 ++ (35290, 2) :: (1, 1) :: repeat (1, 2) 103382 ++ (56736, 2) :: (1, 1) :: repeat (1, 2) 595550 ++ (233769, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) 1)).
  {
    apply (pop12 15 [0] 5 5 ((1114, 2) :: (1, 1) :: repeat (1, 2) 2320 ++ (736, 2) :: (1, 1) :: repeat (1, 2) 12571 ++ (35290, 2) :: (1, 1) :: repeat (1, 2) 103382 ++ (56736, 2) :: (1, 1) :: repeat (1, 2) 595550 ++ (233769, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) 1); closearith.
  }
  (* step 685: sTUP *)
  replace ((1112, 2) :: (1, 1) :: repeat (1, 2) 2320 ++ (736, 2) :: (1, 1) :: repeat (1, 2) 12571 ++ (35290, 2) :: (1, 1) :: repeat (1, 2) 103382 ++ (56736, 2) :: (1, 1) :: repeat (1, 2) 595550 ++ (233769, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) with ((1114 - 2, 2) :: (1, 1) :: repeat (1, 2) 2320 ++ (736, 2) :: (1, 1) :: repeat (1, 2) 12571 ++ (35290, 2) :: (1, 1) :: repeat (1, 2) 103382 ++ (56736, 2) :: (1, 1) :: repeat (1, 2) 595550 ++ (233769, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) by sec_eq.
  apply (sTUP [0] 20 35 1114 2 ((1, 1) :: repeat (1, 2) 2320 ++ (736, 2) :: (1, 1) :: repeat (1, 2) 12571 ++ (35290, 2) :: (1, 1) :: repeat (1, 2) 103382 ++ (56736, 2) :: (1, 1) :: repeat (1, 2) 595550 ++ (233769, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) 1); closearith.
Qed.

(* CASCADE56o: steps 686-741 of the CASCADE56 chain. *)
Lemma CASCADE56o : forall w,
  hsteps (HC [0] 20 34 2 ((1112, 2) :: (1, 1) :: repeat (1, 2) 2320 ++ (736, 2) :: (1, 1) :: repeat (1, 2) 12571 ++ (35290, 2) :: (1, 1) :: repeat (1, 2) 103382 ++ (56736, 2) :: (1, 1) :: repeat (1, 2) 595550 ++ (233769, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) 1)
         (HB [0] 17 1 4 ((106, 2) :: (1, 1) :: repeat (1, 2) 166 ++ (552, 2) :: (1, 1) :: repeat (1, 2) 2320 ++ (736, 2) :: (1, 1) :: repeat (1, 2) 12571 ++ (35290, 2) :: (1, 1) :: repeat (1, 2) 103382 ++ (56736, 2) :: (1, 1) :: repeat (1, 2) 595550 ++ (233769, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) 1).
Proof.
  intro w.
  (* step 686: hGRIND_even 15 *)
  apply (hsteps_trans _ (HB [0] 19 1 34 ((2, 2) :: (1112, 2) :: (1, 1) :: repeat (1, 2) 2320 ++ (736, 2) :: (1, 1) :: repeat (1, 2) 12571 ++ (35290, 2) :: (1, 1) :: repeat (1, 2) 103382 ++ (56736, 2) :: (1, 1) :: repeat (1, 2) 595550 ++ (233769, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) 1)).
  {
    apply (hGRIND_even 15 [0] 19 ((1112, 2) :: (1, 1) :: repeat (1, 2) 2320 ++ (736, 2) :: (1, 1) :: repeat (1, 2) 12571 ++ (35290, 2) :: (1, 1) :: repeat (1, 2) 103382 ++ (56736, 2) :: (1, 1) :: repeat (1, 2) 595550 ++ (233769, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) 1); closearith.
  }
  (* step 687: P TUP2_1 *)
  apply (hsteps_trans _ (HC [20; 0] 34 1 2 ((1110, 2) :: (1, 1) :: repeat (1, 2) 2320 ++ (736, 2) :: (1, 1) :: repeat (1, 2) 12571 ++ (35290, 2) :: (1, 1) :: repeat (1, 2) 103382 ++ (56736, 2) :: (1, 1) :: repeat (1, 2) 595550 ++ (233769, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) 1)).
  {
    replace ((1110, 2) :: (1, 1) :: repeat (1, 2) 2320 ++ (736, 2) :: (1, 1) :: repeat (1, 2) 12571 ++ (35290, 2) :: (1, 1) :: repeat (1, 2) 103382 ++ (56736, 2) :: (1, 1) :: repeat (1, 2) 595550 ++ (233769, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) with ((1112 - 2, 2) :: (1, 1) :: repeat (1, 2) 2320 ++ (736, 2) :: (1, 1) :: repeat (1, 2) 12571 ++ (35290, 2) :: (1, 1) :: repeat (1, 2) 103382 ++ (56736, 2) :: (1, 1) :: repeat (1, 2) 595550 ++ (233769, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) by sec_eq.
    apply (sTUP2_1 [0] 19 33 1112 ((1, 1) :: repeat (1, 2) 2320 ++ (736, 2) :: (1, 1) :: repeat (1, 2) 12571 ++ (35290, 2) :: (1, 1) :: repeat (1, 2) 103382 ++ (56736, 2) :: (1, 1) :: repeat (1, 2) 595550 ++ (233769, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) 1); closearith.
  }
  (* step 688: P TDN *)
  apply (hsteps_trans _ (HB [20; 0] 34 1 4 ((1110, 2) :: (1, 1) :: repeat (1, 2) 2320 ++ (736, 2) :: (1, 1) :: repeat (1, 2) 12571 ++ (35290, 2) :: (1, 1) :: repeat (1, 2) 103382 ++ (56736, 2) :: (1, 1) :: repeat (1, 2) 595550 ++ (233769, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) 1)).
  {
    apply (sTDN [20; 0] 34 ((1110, 2) :: (1, 1) :: repeat (1, 2) 2320 ++ (736, 2) :: (1, 1) :: repeat (1, 2) 12571 ++ (35290, 2) :: (1, 1) :: repeat (1, 2) 103382 ++ (56736, 2) :: (1, 1) :: repeat (1, 2) 595550 ++ (233769, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) 1).
  }
  (* step 689: sTUP *)
  apply (hsteps_trans _ (HC [20; 0] 34 3 2 ((1108, 2) :: (1, 1) :: repeat (1, 2) 2320 ++ (736, 2) :: (1, 1) :: repeat (1, 2) 12571 ++ (35290, 2) :: (1, 1) :: repeat (1, 2) 103382 ++ (56736, 2) :: (1, 1) :: repeat (1, 2) 595550 ++ (233769, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) 1)).
  {
    replace ((1108, 2) :: (1, 1) :: repeat (1, 2) 2320 ++ (736, 2) :: (1, 1) :: repeat (1, 2) 12571 ++ (35290, 2) :: (1, 1) :: repeat (1, 2) 103382 ++ (56736, 2) :: (1, 1) :: repeat (1, 2) 595550 ++ (233769, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) with ((1110 - 2, 2) :: (1, 1) :: repeat (1, 2) 2320 ++ (736, 2) :: (1, 1) :: repeat (1, 2) 12571 ++ (35290, 2) :: (1, 1) :: repeat (1, 2) 103382 ++ (56736, 2) :: (1, 1) :: repeat (1, 2) 595550 ++ (233769, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) by sec_eq.
    apply (sTUP [20; 0] 34 4 1110 2 ((1, 1) :: repeat (1, 2) 2320 ++ (736, 2) :: (1, 1) :: repeat (1, 2) 12571 ++ (35290, 2) :: (1, 1) :: repeat (1, 2) 103382 ++ (56736, 2) :: (1, 1) :: repeat (1, 2) 595550 ++ (233769, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) 1); closearith.
  }
  (* step 690: DIPGRIND 34 1040 *)
  apply (hsteps_trans _ (HC [20; 0] 0 3 2 (repeat (1, 2) 34 ++ (1040, 2) :: (1, 1) :: repeat (1, 2) 2320 ++ (736, 2) :: (1, 1) :: repeat (1, 2) 12571 ++ (35290, 2) :: (1, 1) :: repeat (1, 2) 103382 ++ (56736, 2) :: (1, 1) :: repeat (1, 2) 595550 ++ (233769, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) 1)).
  {
    apply (DIPGRIND 34 1040 [20; 0] ((1, 1) :: repeat (1, 2) 2320 ++ (736, 2) :: (1, 1) :: repeat (1, 2) 12571 ++ (35290, 2) :: (1, 1) :: repeat (1, 2) 103382 ++ (56736, 2) :: (1, 1) :: repeat (1, 2) 595550 ++ (233769, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) 1); closearith.
  }
  (* step 691: P PX2A0 *)
  apply (hsteps_trans _ (HB [0] 3 1 2 ((16, 2) :: (1, 1) :: repeat (1, 2) 36 ++ (1040, 2) :: (1, 1) :: repeat (1, 2) 2320 ++ (736, 2) :: (1, 1) :: repeat (1, 2) 12571 ++ (35290, 2) :: (1, 1) :: repeat (1, 2) 103382 ++ (56736, 2) :: (1, 1) :: repeat (1, 2) 595550 ++ (233769, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) 1)).
  {
    exact (hsteps_step _ _ _ (hPX2A0 15 (repeat (1, 2) 34 ++ (1040, 2) :: (1, 1) :: repeat (1, 2) 2320 ++ (736, 2) :: (1, 1) :: repeat (1, 2) 12571 ++ (35290, 2) :: (1, 1) :: repeat (1, 2) 103382 ++ (56736, 2) :: (1, 1) :: repeat (1, 2) 595550 ++ (233769, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) 1) (hsteps_refl _)).
  }
  (* step 692: sTUP *)
  apply (hsteps_trans _ (HC [0] 3 1 2 ((14, 2) :: (1, 1) :: repeat (1, 2) 36 ++ (1040, 2) :: (1, 1) :: repeat (1, 2) 2320 ++ (736, 2) :: (1, 1) :: repeat (1, 2) 12571 ++ (35290, 2) :: (1, 1) :: repeat (1, 2) 103382 ++ (56736, 2) :: (1, 1) :: repeat (1, 2) 595550 ++ (233769, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) 1)).
  {
    replace ((14, 2) :: (1, 1) :: repeat (1, 2) 36 ++ (1040, 2) :: (1, 1) :: repeat (1, 2) 2320 ++ (736, 2) :: (1, 1) :: repeat (1, 2) 12571 ++ (35290, 2) :: (1, 1) :: repeat (1, 2) 103382 ++ (56736, 2) :: (1, 1) :: repeat (1, 2) 595550 ++ (233769, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) with ((16 - 2, 2) :: (1, 1) :: repeat (1, 2) 36 ++ (1040, 2) :: (1, 1) :: repeat (1, 2) 2320 ++ (736, 2) :: (1, 1) :: repeat (1, 2) 12571 ++ (35290, 2) :: (1, 1) :: repeat (1, 2) 103382 ++ (56736, 2) :: (1, 1) :: repeat (1, 2) 595550 ++ (233769, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) by sec_eq.
    apply (sTUP [0] 3 2 16 2 ((1, 1) :: repeat (1, 2) 36 ++ (1040, 2) :: (1, 1) :: repeat (1, 2) 2320 ++ (736, 2) :: (1, 1) :: repeat (1, 2) 12571 ++ (35290, 2) :: (1, 1) :: repeat (1, 2) 103382 ++ (56736, 2) :: (1, 1) :: repeat (1, 2) 595550 ++ (233769, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) 1); closearith.
  }
  (* step 693: P TDN *)
  apply (hsteps_trans _ (HB [0] 3 1 4 ((14, 2) :: (1, 1) :: repeat (1, 2) 36 ++ (1040, 2) :: (1, 1) :: repeat (1, 2) 2320 ++ (736, 2) :: (1, 1) :: repeat (1, 2) 12571 ++ (35290, 2) :: (1, 1) :: repeat (1, 2) 103382 ++ (56736, 2) :: (1, 1) :: repeat (1, 2) 595550 ++ (233769, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) 1)).
  {
    apply (sTDN [0] 3 ((14, 2) :: (1, 1) :: repeat (1, 2) 36 ++ (1040, 2) :: (1, 1) :: repeat (1, 2) 2320 ++ (736, 2) :: (1, 1) :: repeat (1, 2) 12571 ++ (35290, 2) :: (1, 1) :: repeat (1, 2) 103382 ++ (56736, 2) :: (1, 1) :: repeat (1, 2) 595550 ++ (233769, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) 1).
  }
  (* step 694: sTUP *)
  apply (hsteps_trans _ (HC [0] 3 3 2 ((12, 2) :: (1, 1) :: repeat (1, 2) 36 ++ (1040, 2) :: (1, 1) :: repeat (1, 2) 2320 ++ (736, 2) :: (1, 1) :: repeat (1, 2) 12571 ++ (35290, 2) :: (1, 1) :: repeat (1, 2) 103382 ++ (56736, 2) :: (1, 1) :: repeat (1, 2) 595550 ++ (233769, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) 1)).
  {
    replace ((12, 2) :: (1, 1) :: repeat (1, 2) 36 ++ (1040, 2) :: (1, 1) :: repeat (1, 2) 2320 ++ (736, 2) :: (1, 1) :: repeat (1, 2) 12571 ++ (35290, 2) :: (1, 1) :: repeat (1, 2) 103382 ++ (56736, 2) :: (1, 1) :: repeat (1, 2) 595550 ++ (233769, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) with ((14 - 2, 2) :: (1, 1) :: repeat (1, 2) 36 ++ (1040, 2) :: (1, 1) :: repeat (1, 2) 2320 ++ (736, 2) :: (1, 1) :: repeat (1, 2) 12571 ++ (35290, 2) :: (1, 1) :: repeat (1, 2) 103382 ++ (56736, 2) :: (1, 1) :: repeat (1, 2) 595550 ++ (233769, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) by sec_eq.
    apply (sTUP [0] 3 4 14 2 ((1, 1) :: repeat (1, 2) 36 ++ (1040, 2) :: (1, 1) :: repeat (1, 2) 2320 ++ (736, 2) :: (1, 1) :: repeat (1, 2) 12571 ++ (35290, 2) :: (1, 1) :: repeat (1, 2) 103382 ++ (56736, 2) :: (1, 1) :: repeat (1, 2) 595550 ++ (233769, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) 1); closearith.
  }
  (* step 695: DIPGRIND 3 6 *)
  apply (hsteps_trans _ (HC [0] 0 3 2 (repeat (1, 2) 3 ++ (6, 2) :: (1, 1) :: repeat (1, 2) 36 ++ (1040, 2) :: (1, 1) :: repeat (1, 2) 2320 ++ (736, 2) :: (1, 1) :: repeat (1, 2) 12571 ++ (35290, 2) :: (1, 1) :: repeat (1, 2) 103382 ++ (56736, 2) :: (1, 1) :: repeat (1, 2) 595550 ++ (233769, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) 1)).
  {
    apply (DIPGRIND 3 6 [0] ((1, 1) :: repeat (1, 2) 36 ++ (1040, 2) :: (1, 1) :: repeat (1, 2) 2320 ++ (736, 2) :: (1, 1) :: repeat (1, 2) 12571 ++ (35290, 2) :: (1, 1) :: repeat (1, 2) 103382 ++ (56736, 2) :: (1, 1) :: repeat (1, 2) 595550 ++ (233769, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) 1); closearith.
  }
  (* step 696: P PX2B0 *)
  apply (hsteps_trans _ (HB [] 0 1 5 (repeat (1, 2) 4 ++ (6, 2) :: (1, 1) :: repeat (1, 2) 36 ++ (1040, 2) :: (1, 1) :: repeat (1, 2) 2320 ++ (736, 2) :: (1, 1) :: repeat (1, 2) 12571 ++ (35290, 2) :: (1, 1) :: repeat (1, 2) 103382 ++ (56736, 2) :: (1, 1) :: repeat (1, 2) 595550 ++ (233769, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) 1)).
  {
    exact (hsteps_step _ _ _ (hPX2B0 (repeat (1, 2) 3 ++ (6, 2) :: (1, 1) :: repeat (1, 2) 36 ++ (1040, 2) :: (1, 1) :: repeat (1, 2) 2320 ++ (736, 2) :: (1, 1) :: repeat (1, 2) 12571 ++ (35290, 2) :: (1, 1) :: repeat (1, 2) 103382 ++ (56736, 2) :: (1, 1) :: repeat (1, 2) 595550 ++ (233769, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) 1) (hsteps_refl _)).
  }
  (* step 697: M pop12 (4,) *)
  apply (hsteps_trans _ (HB [] 4 1 13 ((6, 2) :: (1, 1) :: repeat (1, 2) 36 ++ (1040, 2) :: (1, 1) :: repeat (1, 2) 2320 ++ (736, 2) :: (1, 1) :: repeat (1, 2) 12571 ++ (35290, 2) :: (1, 1) :: repeat (1, 2) 103382 ++ (56736, 2) :: (1, 1) :: repeat (1, 2) 595550 ++ (233769, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) 1)).
  {
    apply (pop12 4 [] 0 5 ((6, 2) :: (1, 1) :: repeat (1, 2) 36 ++ (1040, 2) :: (1, 1) :: repeat (1, 2) 2320 ++ (736, 2) :: (1, 1) :: repeat (1, 2) 12571 ++ (35290, 2) :: (1, 1) :: repeat (1, 2) 103382 ++ (56736, 2) :: (1, 1) :: repeat (1, 2) 595550 ++ (233769, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) 1); closearith.
  }
  (* step 698: sTUP *)
  apply (hsteps_trans _ (HC [] 4 12 2 ((4, 2) :: (1, 1) :: repeat (1, 2) 36 ++ (1040, 2) :: (1, 1) :: repeat (1, 2) 2320 ++ (736, 2) :: (1, 1) :: repeat (1, 2) 12571 ++ (35290, 2) :: (1, 1) :: repeat (1, 2) 103382 ++ (56736, 2) :: (1, 1) :: repeat (1, 2) 595550 ++ (233769, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) 1)).
  {
    replace ((4, 2) :: (1, 1) :: repeat (1, 2) 36 ++ (1040, 2) :: (1, 1) :: repeat (1, 2) 2320 ++ (736, 2) :: (1, 1) :: repeat (1, 2) 12571 ++ (35290, 2) :: (1, 1) :: repeat (1, 2) 103382 ++ (56736, 2) :: (1, 1) :: repeat (1, 2) 595550 ++ (233769, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) with ((6 - 2, 2) :: (1, 1) :: repeat (1, 2) 36 ++ (1040, 2) :: (1, 1) :: repeat (1, 2) 2320 ++ (736, 2) :: (1, 1) :: repeat (1, 2) 12571 ++ (35290, 2) :: (1, 1) :: repeat (1, 2) 103382 ++ (56736, 2) :: (1, 1) :: repeat (1, 2) 595550 ++ (233769, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) by sec_eq.
    apply (sTUP [] 4 13 6 2 ((1, 1) :: repeat (1, 2) 36 ++ (1040, 2) :: (1, 1) :: repeat (1, 2) 2320 ++ (736, 2) :: (1, 1) :: repeat (1, 2) 12571 ++ (35290, 2) :: (1, 1) :: repeat (1, 2) 103382 ++ (56736, 2) :: (1, 1) :: repeat (1, 2) 595550 ++ (233769, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) 1); closearith.
  }
  (* step 699: P PUSH *)
  apply (hsteps_trans _ (HC [] 3 1 2 ((10, 2) :: (4, 2) :: (1, 1) :: repeat (1, 2) 36 ++ (1040, 2) :: (1, 1) :: repeat (1, 2) 2320 ++ (736, 2) :: (1, 1) :: repeat (1, 2) 12571 ++ (35290, 2) :: (1, 1) :: repeat (1, 2) 103382 ++ (56736, 2) :: (1, 1) :: repeat (1, 2) 595550 ++ (233769, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) 1)).
  {
    replace ((10, 2) :: (4, 2) :: (1, 1) :: repeat (1, 2) 36 ++ (1040, 2) :: (1, 1) :: repeat (1, 2) 2320 ++ (736, 2) :: (1, 1) :: repeat (1, 2) 12571 ++ (35290, 2) :: (1, 1) :: repeat (1, 2) 103382 ++ (56736, 2) :: (1, 1) :: repeat (1, 2) 595550 ++ (233769, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) with ((12 - 2, 2) :: (4, 2) :: (1, 1) :: repeat (1, 2) 36 ++ (1040, 2) :: (1, 1) :: repeat (1, 2) 2320 ++ (736, 2) :: (1, 1) :: repeat (1, 2) 12571 ++ (35290, 2) :: (1, 1) :: repeat (1, 2) 103382 ++ (56736, 2) :: (1, 1) :: repeat (1, 2) 595550 ++ (233769, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) by sec_eq.
    apply (sPUSH [] 3 12 ((4, 2) :: (1, 1) :: repeat (1, 2) 36 ++ (1040, 2) :: (1, 1) :: repeat (1, 2) 2320 ++ (736, 2) :: (1, 1) :: repeat (1, 2) 12571 ++ (35290, 2) :: (1, 1) :: repeat (1, 2) 103382 ++ (56736, 2) :: (1, 1) :: repeat (1, 2) 595550 ++ (233769, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) 1); closearith.
  }
  (* step 700: P TDN *)
  apply (hsteps_trans _ (HB [] 3 1 4 ((10, 2) :: (4, 2) :: (1, 1) :: repeat (1, 2) 36 ++ (1040, 2) :: (1, 1) :: repeat (1, 2) 2320 ++ (736, 2) :: (1, 1) :: repeat (1, 2) 12571 ++ (35290, 2) :: (1, 1) :: repeat (1, 2) 103382 ++ (56736, 2) :: (1, 1) :: repeat (1, 2) 595550 ++ (233769, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) 1)).
  {
    apply (sTDN [] 3 ((10, 2) :: (4, 2) :: (1, 1) :: repeat (1, 2) 36 ++ (1040, 2) :: (1, 1) :: repeat (1, 2) 2320 ++ (736, 2) :: (1, 1) :: repeat (1, 2) 12571 ++ (35290, 2) :: (1, 1) :: repeat (1, 2) 103382 ++ (56736, 2) :: (1, 1) :: repeat (1, 2) 595550 ++ (233769, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) 1).
  }
  (* step 701: sTUP *)
  apply (hsteps_trans _ (HC [] 3 3 2 ((8, 2) :: (4, 2) :: (1, 1) :: repeat (1, 2) 36 ++ (1040, 2) :: (1, 1) :: repeat (1, 2) 2320 ++ (736, 2) :: (1, 1) :: repeat (1, 2) 12571 ++ (35290, 2) :: (1, 1) :: repeat (1, 2) 103382 ++ (56736, 2) :: (1, 1) :: repeat (1, 2) 595550 ++ (233769, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) 1)).
  {
    replace ((8, 2) :: (4, 2) :: (1, 1) :: repeat (1, 2) 36 ++ (1040, 2) :: (1, 1) :: repeat (1, 2) 2320 ++ (736, 2) :: (1, 1) :: repeat (1, 2) 12571 ++ (35290, 2) :: (1, 1) :: repeat (1, 2) 103382 ++ (56736, 2) :: (1, 1) :: repeat (1, 2) 595550 ++ (233769, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) with ((10 - 2, 2) :: (4, 2) :: (1, 1) :: repeat (1, 2) 36 ++ (1040, 2) :: (1, 1) :: repeat (1, 2) 2320 ++ (736, 2) :: (1, 1) :: repeat (1, 2) 12571 ++ (35290, 2) :: (1, 1) :: repeat (1, 2) 103382 ++ (56736, 2) :: (1, 1) :: repeat (1, 2) 595550 ++ (233769, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) by sec_eq.
    apply (sTUP [] 3 4 10 2 ((4, 2) :: (1, 1) :: repeat (1, 2) 36 ++ (1040, 2) :: (1, 1) :: repeat (1, 2) 2320 ++ (736, 2) :: (1, 1) :: repeat (1, 2) 12571 ++ (35290, 2) :: (1, 1) :: repeat (1, 2) 103382 ++ (56736, 2) :: (1, 1) :: repeat (1, 2) 595550 ++ (233769, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) 1); closearith.
  }
  (* step 702: DIPGRIND 3 2 *)
  apply (hsteps_trans _ (HC [] 0 3 2 (repeat (1, 2) 3 ++ (2, 2) :: (4, 2) :: (1, 1) :: repeat (1, 2) 36 ++ (1040, 2) :: (1, 1) :: repeat (1, 2) 2320 ++ (736, 2) :: (1, 1) :: repeat (1, 2) 12571 ++ (35290, 2) :: (1, 1) :: repeat (1, 2) 103382 ++ (56736, 2) :: (1, 1) :: repeat (1, 2) 595550 ++ (233769, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) 1)).
  {
    apply (DIPGRIND 3 2 [] ((4, 2) :: (1, 1) :: repeat (1, 2) 36 ++ (1040, 2) :: (1, 1) :: repeat (1, 2) 2320 ++ (736, 2) :: (1, 1) :: repeat (1, 2) 12571 ++ (35290, 2) :: (1, 1) :: repeat (1, 2) 103382 ++ (56736, 2) :: (1, 1) :: repeat (1, 2) 595550 ++ (233769, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) 1); closearith.
  }
  (* step 703: P PUSHX *)
  apply (hsteps_trans _ (HB [] 1 1 7 (repeat (1, 2) 3 ++ (2, 2) :: (4, 2) :: (1, 1) :: repeat (1, 2) 36 ++ (1040, 2) :: (1, 1) :: repeat (1, 2) 2320 ++ (736, 2) :: (1, 1) :: repeat (1, 2) 12571 ++ (35290, 2) :: (1, 1) :: repeat (1, 2) 103382 ++ (56736, 2) :: (1, 1) :: repeat (1, 2) 595550 ++ (233769, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) 1)).
  {
    exact (hsteps_step _ _ _ (hPUSHX (repeat (1, 2) 3 ++ (2, 2) :: (4, 2) :: (1, 1) :: repeat (1, 2) 36 ++ (1040, 2) :: (1, 1) :: repeat (1, 2) 2320 ++ (736, 2) :: (1, 1) :: repeat (1, 2) 12571 ++ (35290, 2) :: (1, 1) :: repeat (1, 2) 103382 ++ (56736, 2) :: (1, 1) :: repeat (1, 2) 595550 ++ (233769, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) 1) (hsteps_refl _)).
  }
  (* step 704: M pop12 (3,) *)
  apply (hsteps_trans _ (HB [] 4 1 13 ((2, 2) :: (4, 2) :: (1, 1) :: repeat (1, 2) 36 ++ (1040, 2) :: (1, 1) :: repeat (1, 2) 2320 ++ (736, 2) :: (1, 1) :: repeat (1, 2) 12571 ++ (35290, 2) :: (1, 1) :: repeat (1, 2) 103382 ++ (56736, 2) :: (1, 1) :: repeat (1, 2) 595550 ++ (233769, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) 1)).
  {
    apply (pop12 3 [] 1 7 ((2, 2) :: (4, 2) :: (1, 1) :: repeat (1, 2) 36 ++ (1040, 2) :: (1, 1) :: repeat (1, 2) 2320 ++ (736, 2) :: (1, 1) :: repeat (1, 2) 12571 ++ (35290, 2) :: (1, 1) :: repeat (1, 2) 103382 ++ (56736, 2) :: (1, 1) :: repeat (1, 2) 595550 ++ (233769, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) 1); closearith.
  }
  (* step 705: P TUP2_1 *)
  apply (hsteps_trans _ (HC [5] 13 1 2 ((2, 2) :: (1, 1) :: repeat (1, 2) 36 ++ (1040, 2) :: (1, 1) :: repeat (1, 2) 2320 ++ (736, 2) :: (1, 1) :: repeat (1, 2) 12571 ++ (35290, 2) :: (1, 1) :: repeat (1, 2) 103382 ++ (56736, 2) :: (1, 1) :: repeat (1, 2) 595550 ++ (233769, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) 1)).
  {
    replace ((2, 2) :: (1, 1) :: repeat (1, 2) 36 ++ (1040, 2) :: (1, 1) :: repeat (1, 2) 2320 ++ (736, 2) :: (1, 1) :: repeat (1, 2) 12571 ++ (35290, 2) :: (1, 1) :: repeat (1, 2) 103382 ++ (56736, 2) :: (1, 1) :: repeat (1, 2) 595550 ++ (233769, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) with ((4 - 2, 2) :: (1, 1) :: repeat (1, 2) 36 ++ (1040, 2) :: (1, 1) :: repeat (1, 2) 2320 ++ (736, 2) :: (1, 1) :: repeat (1, 2) 12571 ++ (35290, 2) :: (1, 1) :: repeat (1, 2) 103382 ++ (56736, 2) :: (1, 1) :: repeat (1, 2) 595550 ++ (233769, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) by sec_eq.
    apply (sTUP2_1 [] 4 12 4 ((1, 1) :: repeat (1, 2) 36 ++ (1040, 2) :: (1, 1) :: repeat (1, 2) 2320 ++ (736, 2) :: (1, 1) :: repeat (1, 2) 12571 ++ (35290, 2) :: (1, 1) :: repeat (1, 2) 103382 ++ (56736, 2) :: (1, 1) :: repeat (1, 2) 595550 ++ (233769, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) 1); closearith.
  }
  (* step 706: P TDN *)
  apply (hsteps_trans _ (HB [5] 13 1 4 ((2, 2) :: (1, 1) :: repeat (1, 2) 36 ++ (1040, 2) :: (1, 1) :: repeat (1, 2) 2320 ++ (736, 2) :: (1, 1) :: repeat (1, 2) 12571 ++ (35290, 2) :: (1, 1) :: repeat (1, 2) 103382 ++ (56736, 2) :: (1, 1) :: repeat (1, 2) 595550 ++ (233769, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) 1)).
  {
    apply (sTDN [5] 13 ((2, 2) :: (1, 1) :: repeat (1, 2) 36 ++ (1040, 2) :: (1, 1) :: repeat (1, 2) 2320 ++ (736, 2) :: (1, 1) :: repeat (1, 2) 12571 ++ (35290, 2) :: (1, 1) :: repeat (1, 2) 103382 ++ (56736, 2) :: (1, 1) :: repeat (1, 2) 595550 ++ (233769, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) 1).
  }
  (* step 707: P TRANS2_1 *)
  apply (hsteps_trans _ (HB [14; 5] 5 1 3 (repeat (1, 2) 36 ++ (1040, 2) :: (1, 1) :: repeat (1, 2) 2320 ++ (736, 2) :: (1, 1) :: repeat (1, 2) 12571 ++ (35290, 2) :: (1, 1) :: repeat (1, 2) 103382 ++ (56736, 2) :: (1, 1) :: repeat (1, 2) 595550 ++ (233769, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) 1)).
  {
    apply (sTRANS2_1 [5] 13 3 1 (repeat (1, 2) 36 ++ (1040, 2) :: (1, 1) :: repeat (1, 2) 2320 ++ (736, 2) :: (1, 1) :: repeat (1, 2) 12571 ++ (35290, 2) :: (1, 1) :: repeat (1, 2) 103382 ++ (56736, 2) :: (1, 1) :: repeat (1, 2) 595550 ++ (233769, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) 1); closearith.
  }
  (* step 708: M pop12 (36,) *)
  apply (hsteps_trans _ (HB [14; 5] 41 1 75 ((1040, 2) :: (1, 1) :: repeat (1, 2) 2320 ++ (736, 2) :: (1, 1) :: repeat (1, 2) 12571 ++ (35290, 2) :: (1, 1) :: repeat (1, 2) 103382 ++ (56736, 2) :: (1, 1) :: repeat (1, 2) 595550 ++ (233769, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) 1)).
  {
    apply (pop12 36 [14; 5] 5 3 ((1040, 2) :: (1, 1) :: repeat (1, 2) 2320 ++ (736, 2) :: (1, 1) :: repeat (1, 2) 12571 ++ (35290, 2) :: (1, 1) :: repeat (1, 2) 103382 ++ (56736, 2) :: (1, 1) :: repeat (1, 2) 595550 ++ (233769, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) 1); closearith.
  }
  (* step 709: sTUP *)
  apply (hsteps_trans _ (HC [14; 5] 41 74 2 ((1038, 2) :: (1, 1) :: repeat (1, 2) 2320 ++ (736, 2) :: (1, 1) :: repeat (1, 2) 12571 ++ (35290, 2) :: (1, 1) :: repeat (1, 2) 103382 ++ (56736, 2) :: (1, 1) :: repeat (1, 2) 595550 ++ (233769, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) 1)).
  {
    replace ((1038, 2) :: (1, 1) :: repeat (1, 2) 2320 ++ (736, 2) :: (1, 1) :: repeat (1, 2) 12571 ++ (35290, 2) :: (1, 1) :: repeat (1, 2) 103382 ++ (56736, 2) :: (1, 1) :: repeat (1, 2) 595550 ++ (233769, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) with ((1040 - 2, 2) :: (1, 1) :: repeat (1, 2) 2320 ++ (736, 2) :: (1, 1) :: repeat (1, 2) 12571 ++ (35290, 2) :: (1, 1) :: repeat (1, 2) 103382 ++ (56736, 2) :: (1, 1) :: repeat (1, 2) 595550 ++ (233769, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) by sec_eq.
    apply (sTUP [14; 5] 41 75 1040 2 ((1, 1) :: repeat (1, 2) 2320 ++ (736, 2) :: (1, 1) :: repeat (1, 2) 12571 ++ (35290, 2) :: (1, 1) :: repeat (1, 2) 103382 ++ (56736, 2) :: (1, 1) :: repeat (1, 2) 595550 ++ (233769, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) 1); closearith.
  }
  (* step 710: hGRIND_even 35 *)
  apply (hsteps_trans _ (HB [14; 5] 40 1 74 ((2, 2) :: (1038, 2) :: (1, 1) :: repeat (1, 2) 2320 ++ (736, 2) :: (1, 1) :: repeat (1, 2) 12571 ++ (35290, 2) :: (1, 1) :: repeat (1, 2) 103382 ++ (56736, 2) :: (1, 1) :: repeat (1, 2) 595550 ++ (233769, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) 1)).
  {
    apply (hGRIND_even 35 [14; 5] 40 ((1038, 2) :: (1, 1) :: repeat (1, 2) 2320 ++ (736, 2) :: (1, 1) :: repeat (1, 2) 12571 ++ (35290, 2) :: (1, 1) :: repeat (1, 2) 103382 ++ (56736, 2) :: (1, 1) :: repeat (1, 2) 595550 ++ (233769, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) 1); closearith.
  }
  (* step 711: P TUP2_1 *)
  apply (hsteps_trans _ (HC [41; 14; 5] 74 1 2 ((1036, 2) :: (1, 1) :: repeat (1, 2) 2320 ++ (736, 2) :: (1, 1) :: repeat (1, 2) 12571 ++ (35290, 2) :: (1, 1) :: repeat (1, 2) 103382 ++ (56736, 2) :: (1, 1) :: repeat (1, 2) 595550 ++ (233769, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) 1)).
  {
    replace ((1036, 2) :: (1, 1) :: repeat (1, 2) 2320 ++ (736, 2) :: (1, 1) :: repeat (1, 2) 12571 ++ (35290, 2) :: (1, 1) :: repeat (1, 2) 103382 ++ (56736, 2) :: (1, 1) :: repeat (1, 2) 595550 ++ (233769, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) with ((1038 - 2, 2) :: (1, 1) :: repeat (1, 2) 2320 ++ (736, 2) :: (1, 1) :: repeat (1, 2) 12571 ++ (35290, 2) :: (1, 1) :: repeat (1, 2) 103382 ++ (56736, 2) :: (1, 1) :: repeat (1, 2) 595550 ++ (233769, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) by sec_eq.
    apply (sTUP2_1 [14; 5] 40 73 1038 ((1, 1) :: repeat (1, 2) 2320 ++ (736, 2) :: (1, 1) :: repeat (1, 2) 12571 ++ (35290, 2) :: (1, 1) :: repeat (1, 2) 103382 ++ (56736, 2) :: (1, 1) :: repeat (1, 2) 595550 ++ (233769, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) 1); closearith.
  }
  (* step 712: P TDN *)
  apply (hsteps_trans _ (HB [41; 14; 5] 74 1 4 ((1036, 2) :: (1, 1) :: repeat (1, 2) 2320 ++ (736, 2) :: (1, 1) :: repeat (1, 2) 12571 ++ (35290, 2) :: (1, 1) :: repeat (1, 2) 103382 ++ (56736, 2) :: (1, 1) :: repeat (1, 2) 595550 ++ (233769, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) 1)).
  {
    apply (sTDN [41; 14; 5] 74 ((1036, 2) :: (1, 1) :: repeat (1, 2) 2320 ++ (736, 2) :: (1, 1) :: repeat (1, 2) 12571 ++ (35290, 2) :: (1, 1) :: repeat (1, 2) 103382 ++ (56736, 2) :: (1, 1) :: repeat (1, 2) 595550 ++ (233769, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) 1).
  }
  (* step 713: sTUP *)
  apply (hsteps_trans _ (HC [41; 14; 5] 74 3 2 ((1034, 2) :: (1, 1) :: repeat (1, 2) 2320 ++ (736, 2) :: (1, 1) :: repeat (1, 2) 12571 ++ (35290, 2) :: (1, 1) :: repeat (1, 2) 103382 ++ (56736, 2) :: (1, 1) :: repeat (1, 2) 595550 ++ (233769, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) 1)).
  {
    replace ((1034, 2) :: (1, 1) :: repeat (1, 2) 2320 ++ (736, 2) :: (1, 1) :: repeat (1, 2) 12571 ++ (35290, 2) :: (1, 1) :: repeat (1, 2) 103382 ++ (56736, 2) :: (1, 1) :: repeat (1, 2) 595550 ++ (233769, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) with ((1036 - 2, 2) :: (1, 1) :: repeat (1, 2) 2320 ++ (736, 2) :: (1, 1) :: repeat (1, 2) 12571 ++ (35290, 2) :: (1, 1) :: repeat (1, 2) 103382 ++ (56736, 2) :: (1, 1) :: repeat (1, 2) 595550 ++ (233769, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) by sec_eq.
    apply (sTUP [41; 14; 5] 74 4 1036 2 ((1, 1) :: repeat (1, 2) 2320 ++ (736, 2) :: (1, 1) :: repeat (1, 2) 12571 ++ (35290, 2) :: (1, 1) :: repeat (1, 2) 103382 ++ (56736, 2) :: (1, 1) :: repeat (1, 2) 595550 ++ (233769, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) 1); closearith.
  }
  (* step 714: DIPGRIND 74 886 *)
  apply (hsteps_trans _ (HC [41; 14; 5] 0 3 2 (repeat (1, 2) 74 ++ (886, 2) :: (1, 1) :: repeat (1, 2) 2320 ++ (736, 2) :: (1, 1) :: repeat (1, 2) 12571 ++ (35290, 2) :: (1, 1) :: repeat (1, 2) 103382 ++ (56736, 2) :: (1, 1) :: repeat (1, 2) 595550 ++ (233769, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) 1)).
  {
    apply (DIPGRIND 74 886 [41; 14; 5] ((1, 1) :: repeat (1, 2) 2320 ++ (736, 2) :: (1, 1) :: repeat (1, 2) 12571 ++ (35290, 2) :: (1, 1) :: repeat (1, 2) 103382 ++ (56736, 2) :: (1, 1) :: repeat (1, 2) 595550 ++ (233769, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) 1); closearith.
  }
  (* step 715: P PX2A *)
  apply (hsteps_trans _ (HC [5] 13 39 2 ((1, 1) :: repeat (1, 2) 76 ++ (886, 2) :: (1, 1) :: repeat (1, 2) 2320 ++ (736, 2) :: (1, 1) :: repeat (1, 2) 12571 ++ (35290, 2) :: (1, 1) :: repeat (1, 2) 103382 ++ (56736, 2) :: (1, 1) :: repeat (1, 2) 595550 ++ (233769, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) 1)).
  {
    exact (hsteps_step _ _ _ (hPX2A 38 13 [5] (repeat (1, 2) 74 ++ (886, 2) :: (1, 1) :: repeat (1, 2) 2320 ++ (736, 2) :: (1, 1) :: repeat (1, 2) 12571 ++ (35290, 2) :: (1, 1) :: repeat (1, 2) 103382 ++ (56736, 2) :: (1, 1) :: repeat (1, 2) 595550 ++ (233769, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) 1) (hsteps_refl _)).
  }
  (* step 716: P PUSH *)
  apply (hsteps_trans _ (HC [5] 12 1 2 ((37, 2) :: (1, 1) :: repeat (1, 2) 76 ++ (886, 2) :: (1, 1) :: repeat (1, 2) 2320 ++ (736, 2) :: (1, 1) :: repeat (1, 2) 12571 ++ (35290, 2) :: (1, 1) :: repeat (1, 2) 103382 ++ (56736, 2) :: (1, 1) :: repeat (1, 2) 595550 ++ (233769, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) 1)).
  {
    replace ((37, 2) :: (1, 1) :: repeat (1, 2) 76 ++ (886, 2) :: (1, 1) :: repeat (1, 2) 2320 ++ (736, 2) :: (1, 1) :: repeat (1, 2) 12571 ++ (35290, 2) :: (1, 1) :: repeat (1, 2) 103382 ++ (56736, 2) :: (1, 1) :: repeat (1, 2) 595550 ++ (233769, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) with ((39 - 2, 2) :: (1, 1) :: repeat (1, 2) 76 ++ (886, 2) :: (1, 1) :: repeat (1, 2) 2320 ++ (736, 2) :: (1, 1) :: repeat (1, 2) 12571 ++ (35290, 2) :: (1, 1) :: repeat (1, 2) 103382 ++ (56736, 2) :: (1, 1) :: repeat (1, 2) 595550 ++ (233769, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) by sec_eq.
    apply (sPUSH [5] 12 39 ((1, 1) :: repeat (1, 2) 76 ++ (886, 2) :: (1, 1) :: repeat (1, 2) 2320 ++ (736, 2) :: (1, 1) :: repeat (1, 2) 12571 ++ (35290, 2) :: (1, 1) :: repeat (1, 2) 103382 ++ (56736, 2) :: (1, 1) :: repeat (1, 2) 595550 ++ (233769, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) 1); closearith.
  }
  (* step 717: P TDN *)
  apply (hsteps_trans _ (HB [5] 12 1 4 ((37, 2) :: (1, 1) :: repeat (1, 2) 76 ++ (886, 2) :: (1, 1) :: repeat (1, 2) 2320 ++ (736, 2) :: (1, 1) :: repeat (1, 2) 12571 ++ (35290, 2) :: (1, 1) :: repeat (1, 2) 103382 ++ (56736, 2) :: (1, 1) :: repeat (1, 2) 595550 ++ (233769, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) 1)).
  {
    apply (sTDN [5] 12 ((37, 2) :: (1, 1) :: repeat (1, 2) 76 ++ (886, 2) :: (1, 1) :: repeat (1, 2) 2320 ++ (736, 2) :: (1, 1) :: repeat (1, 2) 12571 ++ (35290, 2) :: (1, 1) :: repeat (1, 2) 103382 ++ (56736, 2) :: (1, 1) :: repeat (1, 2) 595550 ++ (233769, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) 1).
  }
  (* step 718: sTUP *)
  apply (hsteps_trans _ (HC [5] 12 3 2 ((35, 2) :: (1, 1) :: repeat (1, 2) 76 ++ (886, 2) :: (1, 1) :: repeat (1, 2) 2320 ++ (736, 2) :: (1, 1) :: repeat (1, 2) 12571 ++ (35290, 2) :: (1, 1) :: repeat (1, 2) 103382 ++ (56736, 2) :: (1, 1) :: repeat (1, 2) 595550 ++ (233769, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) 1)).
  {
    replace ((35, 2) :: (1, 1) :: repeat (1, 2) 76 ++ (886, 2) :: (1, 1) :: repeat (1, 2) 2320 ++ (736, 2) :: (1, 1) :: repeat (1, 2) 12571 ++ (35290, 2) :: (1, 1) :: repeat (1, 2) 103382 ++ (56736, 2) :: (1, 1) :: repeat (1, 2) 595550 ++ (233769, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) with ((37 - 2, 2) :: (1, 1) :: repeat (1, 2) 76 ++ (886, 2) :: (1, 1) :: repeat (1, 2) 2320 ++ (736, 2) :: (1, 1) :: repeat (1, 2) 12571 ++ (35290, 2) :: (1, 1) :: repeat (1, 2) 103382 ++ (56736, 2) :: (1, 1) :: repeat (1, 2) 595550 ++ (233769, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) by sec_eq.
    apply (sTUP [5] 12 4 37 2 ((1, 1) :: repeat (1, 2) 76 ++ (886, 2) :: (1, 1) :: repeat (1, 2) 2320 ++ (736, 2) :: (1, 1) :: repeat (1, 2) 12571 ++ (35290, 2) :: (1, 1) :: repeat (1, 2) 103382 ++ (56736, 2) :: (1, 1) :: repeat (1, 2) 595550 ++ (233769, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) 1); closearith.
  }
  (* step 719: DIPGRIND 12 11 *)
  apply (hsteps_trans _ (HC [5] 0 3 2 (repeat (1, 2) 12 ++ (11, 2) :: (1, 1) :: repeat (1, 2) 76 ++ (886, 2) :: (1, 1) :: repeat (1, 2) 2320 ++ (736, 2) :: (1, 1) :: repeat (1, 2) 12571 ++ (35290, 2) :: (1, 1) :: repeat (1, 2) 103382 ++ (56736, 2) :: (1, 1) :: repeat (1, 2) 595550 ++ (233769, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) 1)).
  {
    apply (DIPGRIND 12 11 [5] ((1, 1) :: repeat (1, 2) 76 ++ (886, 2) :: (1, 1) :: repeat (1, 2) 2320 ++ (736, 2) :: (1, 1) :: repeat (1, 2) 12571 ++ (35290, 2) :: (1, 1) :: repeat (1, 2) 103382 ++ (56736, 2) :: (1, 1) :: repeat (1, 2) 595550 ++ (233769, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) 1); closearith.
  }
  (* step 720: P PX2Bgen *)
  apply (hsteps_trans _ (HB [0] 3 1 2 (repeat (1, 2) 1 ++ (1, 1) :: repeat (1, 2) 14 ++ (11, 2) :: (1, 1) :: repeat (1, 2) 76 ++ (886, 2) :: (1, 1) :: repeat (1, 2) 2320 ++ (736, 2) :: (1, 1) :: repeat (1, 2) 12571 ++ (35290, 2) :: (1, 1) :: repeat (1, 2) 103382 ++ (56736, 2) :: (1, 1) :: repeat (1, 2) 595550 ++ (233769, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) 1)).
  {
    exact (hsteps_step _ _ _ (hPX2Bgen 0 (repeat (1, 2) 12 ++ (11, 2) :: (1, 1) :: repeat (1, 2) 76 ++ (886, 2) :: (1, 1) :: repeat (1, 2) 2320 ++ (736, 2) :: (1, 1) :: repeat (1, 2) 12571 ++ (35290, 2) :: (1, 1) :: repeat (1, 2) 103382 ++ (56736, 2) :: (1, 1) :: repeat (1, 2) 595550 ++ (233769, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) 1) (hsteps_refl _)).
  }
  (* step 721: M pop12 (1,) *)
  apply (hsteps_trans _ (HB [0] 4 1 4 ((1, 1) :: repeat (1, 2) 14 ++ (11, 2) :: (1, 1) :: repeat (1, 2) 76 ++ (886, 2) :: (1, 1) :: repeat (1, 2) 2320 ++ (736, 2) :: (1, 1) :: repeat (1, 2) 12571 ++ (35290, 2) :: (1, 1) :: repeat (1, 2) 103382 ++ (56736, 2) :: (1, 1) :: repeat (1, 2) 595550 ++ (233769, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) 1)).
  {
    apply (pop12 1 [0] 3 2 ((1, 1) :: repeat (1, 2) 14 ++ (11, 2) :: (1, 1) :: repeat (1, 2) 76 ++ (886, 2) :: (1, 1) :: repeat (1, 2) 2320 ++ (736, 2) :: (1, 1) :: repeat (1, 2) 12571 ++ (35290, 2) :: (1, 1) :: repeat (1, 2) 103382 ++ (56736, 2) :: (1, 1) :: repeat (1, 2) 595550 ++ (233769, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) 1); closearith.
  }
  (* step 722: P POP *)
  apply (hsteps_trans _ (HB [0] 5 1 5 (repeat (1, 2) 14 ++ (11, 2) :: (1, 1) :: repeat (1, 2) 76 ++ (886, 2) :: (1, 1) :: repeat (1, 2) 2320 ++ (736, 2) :: (1, 1) :: repeat (1, 2) 12571 ++ (35290, 2) :: (1, 1) :: repeat (1, 2) 103382 ++ (56736, 2) :: (1, 1) :: repeat (1, 2) 595550 ++ (233769, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) 1)).
  {
    apply (sPOP1 [0] 4 4 (repeat (1, 2) 14 ++ (11, 2) :: (1, 1) :: repeat (1, 2) 76 ++ (886, 2) :: (1, 1) :: repeat (1, 2) 2320 ++ (736, 2) :: (1, 1) :: repeat (1, 2) 12571 ++ (35290, 2) :: (1, 1) :: repeat (1, 2) 103382 ++ (56736, 2) :: (1, 1) :: repeat (1, 2) 595550 ++ (233769, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) 1); closearith.
  }
  (* step 723: M pop12 (14,) *)
  apply (hsteps_trans _ (HB [0] 19 1 33 ((11, 2) :: (1, 1) :: repeat (1, 2) 76 ++ (886, 2) :: (1, 1) :: repeat (1, 2) 2320 ++ (736, 2) :: (1, 1) :: repeat (1, 2) 12571 ++ (35290, 2) :: (1, 1) :: repeat (1, 2) 103382 ++ (56736, 2) :: (1, 1) :: repeat (1, 2) 595550 ++ (233769, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) 1)).
  {
    apply (pop12 14 [0] 5 5 ((11, 2) :: (1, 1) :: repeat (1, 2) 76 ++ (886, 2) :: (1, 1) :: repeat (1, 2) 2320 ++ (736, 2) :: (1, 1) :: repeat (1, 2) 12571 ++ (35290, 2) :: (1, 1) :: repeat (1, 2) 103382 ++ (56736, 2) :: (1, 1) :: repeat (1, 2) 595550 ++ (233769, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) 1); closearith.
  }
  (* step 724: sTUP *)
  apply (hsteps_trans _ (HC [0] 19 32 2 ((9, 2) :: (1, 1) :: repeat (1, 2) 76 ++ (886, 2) :: (1, 1) :: repeat (1, 2) 2320 ++ (736, 2) :: (1, 1) :: repeat (1, 2) 12571 ++ (35290, 2) :: (1, 1) :: repeat (1, 2) 103382 ++ (56736, 2) :: (1, 1) :: repeat (1, 2) 595550 ++ (233769, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) 1)).
  {
    replace ((9, 2) :: (1, 1) :: repeat (1, 2) 76 ++ (886, 2) :: (1, 1) :: repeat (1, 2) 2320 ++ (736, 2) :: (1, 1) :: repeat (1, 2) 12571 ++ (35290, 2) :: (1, 1) :: repeat (1, 2) 103382 ++ (56736, 2) :: (1, 1) :: repeat (1, 2) 595550 ++ (233769, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) with ((11 - 2, 2) :: (1, 1) :: repeat (1, 2) 76 ++ (886, 2) :: (1, 1) :: repeat (1, 2) 2320 ++ (736, 2) :: (1, 1) :: repeat (1, 2) 12571 ++ (35290, 2) :: (1, 1) :: repeat (1, 2) 103382 ++ (56736, 2) :: (1, 1) :: repeat (1, 2) 595550 ++ (233769, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) by sec_eq.
    apply (sTUP [0] 19 33 11 2 ((1, 1) :: repeat (1, 2) 76 ++ (886, 2) :: (1, 1) :: repeat (1, 2) 2320 ++ (736, 2) :: (1, 1) :: repeat (1, 2) 12571 ++ (35290, 2) :: (1, 1) :: repeat (1, 2) 103382 ++ (56736, 2) :: (1, 1) :: repeat (1, 2) 595550 ++ (233769, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) 1); closearith.
  }
  (* step 725: hGRIND_even 14 *)
  apply (hsteps_trans _ (HB [0] 18 1 32 ((2, 2) :: (9, 2) :: (1, 1) :: repeat (1, 2) 76 ++ (886, 2) :: (1, 1) :: repeat (1, 2) 2320 ++ (736, 2) :: (1, 1) :: repeat (1, 2) 12571 ++ (35290, 2) :: (1, 1) :: repeat (1, 2) 103382 ++ (56736, 2) :: (1, 1) :: repeat (1, 2) 595550 ++ (233769, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) 1)).
  {
    apply (hGRIND_even 14 [0] 18 ((9, 2) :: (1, 1) :: repeat (1, 2) 76 ++ (886, 2) :: (1, 1) :: repeat (1, 2) 2320 ++ (736, 2) :: (1, 1) :: repeat (1, 2) 12571 ++ (35290, 2) :: (1, 1) :: repeat (1, 2) 103382 ++ (56736, 2) :: (1, 1) :: repeat (1, 2) 595550 ++ (233769, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) 1); closearith.
  }
  (* step 726: P TUP2_1 *)
  apply (hsteps_trans _ (HC [19; 0] 32 1 2 ((7, 2) :: (1, 1) :: repeat (1, 2) 76 ++ (886, 2) :: (1, 1) :: repeat (1, 2) 2320 ++ (736, 2) :: (1, 1) :: repeat (1, 2) 12571 ++ (35290, 2) :: (1, 1) :: repeat (1, 2) 103382 ++ (56736, 2) :: (1, 1) :: repeat (1, 2) 595550 ++ (233769, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) 1)).
  {
    replace ((7, 2) :: (1, 1) :: repeat (1, 2) 76 ++ (886, 2) :: (1, 1) :: repeat (1, 2) 2320 ++ (736, 2) :: (1, 1) :: repeat (1, 2) 12571 ++ (35290, 2) :: (1, 1) :: repeat (1, 2) 103382 ++ (56736, 2) :: (1, 1) :: repeat (1, 2) 595550 ++ (233769, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) with ((9 - 2, 2) :: (1, 1) :: repeat (1, 2) 76 ++ (886, 2) :: (1, 1) :: repeat (1, 2) 2320 ++ (736, 2) :: (1, 1) :: repeat (1, 2) 12571 ++ (35290, 2) :: (1, 1) :: repeat (1, 2) 103382 ++ (56736, 2) :: (1, 1) :: repeat (1, 2) 595550 ++ (233769, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) by sec_eq.
    apply (sTUP2_1 [0] 18 31 9 ((1, 1) :: repeat (1, 2) 76 ++ (886, 2) :: (1, 1) :: repeat (1, 2) 2320 ++ (736, 2) :: (1, 1) :: repeat (1, 2) 12571 ++ (35290, 2) :: (1, 1) :: repeat (1, 2) 103382 ++ (56736, 2) :: (1, 1) :: repeat (1, 2) 595550 ++ (233769, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) 1); closearith.
  }
  (* step 727: P TDN *)
  apply (hsteps_trans _ (HB [19; 0] 32 1 4 ((7, 2) :: (1, 1) :: repeat (1, 2) 76 ++ (886, 2) :: (1, 1) :: repeat (1, 2) 2320 ++ (736, 2) :: (1, 1) :: repeat (1, 2) 12571 ++ (35290, 2) :: (1, 1) :: repeat (1, 2) 103382 ++ (56736, 2) :: (1, 1) :: repeat (1, 2) 595550 ++ (233769, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) 1)).
  {
    apply (sTDN [19; 0] 32 ((7, 2) :: (1, 1) :: repeat (1, 2) 76 ++ (886, 2) :: (1, 1) :: repeat (1, 2) 2320 ++ (736, 2) :: (1, 1) :: repeat (1, 2) 12571 ++ (35290, 2) :: (1, 1) :: repeat (1, 2) 103382 ++ (56736, 2) :: (1, 1) :: repeat (1, 2) 595550 ++ (233769, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) 1).
  }
  (* step 728: sTUP *)
  apply (hsteps_trans _ (HC [19; 0] 32 3 2 ((5, 2) :: (1, 1) :: repeat (1, 2) 76 ++ (886, 2) :: (1, 1) :: repeat (1, 2) 2320 ++ (736, 2) :: (1, 1) :: repeat (1, 2) 12571 ++ (35290, 2) :: (1, 1) :: repeat (1, 2) 103382 ++ (56736, 2) :: (1, 1) :: repeat (1, 2) 595550 ++ (233769, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) 1)).
  {
    replace ((5, 2) :: (1, 1) :: repeat (1, 2) 76 ++ (886, 2) :: (1, 1) :: repeat (1, 2) 2320 ++ (736, 2) :: (1, 1) :: repeat (1, 2) 12571 ++ (35290, 2) :: (1, 1) :: repeat (1, 2) 103382 ++ (56736, 2) :: (1, 1) :: repeat (1, 2) 595550 ++ (233769, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) with ((7 - 2, 2) :: (1, 1) :: repeat (1, 2) 76 ++ (886, 2) :: (1, 1) :: repeat (1, 2) 2320 ++ (736, 2) :: (1, 1) :: repeat (1, 2) 12571 ++ (35290, 2) :: (1, 1) :: repeat (1, 2) 103382 ++ (56736, 2) :: (1, 1) :: repeat (1, 2) 595550 ++ (233769, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) by sec_eq.
    apply (sTUP [19; 0] 32 4 7 2 ((1, 1) :: repeat (1, 2) 76 ++ (886, 2) :: (1, 1) :: repeat (1, 2) 2320 ++ (736, 2) :: (1, 1) :: repeat (1, 2) 12571 ++ (35290, 2) :: (1, 1) :: repeat (1, 2) 103382 ++ (56736, 2) :: (1, 1) :: repeat (1, 2) 595550 ++ (233769, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) 1); closearith.
  }
  (* step 729: CLEANG_odd 1 *)
  apply (hsteps_trans _ (HB [19; 0] 32 1 10 (repeat (1, 2) 1 ++ (1, 1) :: repeat (1, 2) 76 ++ (886, 2) :: (1, 1) :: repeat (1, 2) 2320 ++ (736, 2) :: (1, 1) :: repeat (1, 2) 12571 ++ (35290, 2) :: (1, 1) :: repeat (1, 2) 103382 ++ (56736, 2) :: (1, 1) :: repeat (1, 2) 595550 ++ (233769, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) 1)).
  {
    replace (repeat (1, 2) 1 ++ (1, 1) :: repeat (1, 2) 76 ++ (886, 2) :: (1, 1) :: repeat (1, 2) 2320 ++ (736, 2) :: (1, 1) :: repeat (1, 2) 12571 ++ (35290, 2) :: (1, 1) :: repeat (1, 2) 103382 ++ (56736, 2) :: (1, 1) :: repeat (1, 2) 595550 ++ (233769, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) with ((1, 2) :: (1, 1) :: repeat (1, 2) 76 ++ (886, 2) :: (1, 1) :: repeat (1, 2) 2320 ++ (736, 2) :: (1, 1) :: repeat (1, 2) 12571 ++ (35290, 2) :: (1, 1) :: repeat (1, 2) 103382 ++ (56736, 2) :: (1, 1) :: repeat (1, 2) 595550 ++ (233769, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) by sec_eq.
    apply (CLEANG_odd 1 [19; 0] 32 ((1, 1) :: repeat (1, 2) 76 ++ (886, 2) :: (1, 1) :: repeat (1, 2) 2320 ++ (736, 2) :: (1, 1) :: repeat (1, 2) 12571 ++ (35290, 2) :: (1, 1) :: repeat (1, 2) 103382 ++ (56736, 2) :: (1, 1) :: repeat (1, 2) 595550 ++ (233769, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) 1); closearith.
  }
  (* step 730: M pop12 (1,) *)
  apply (hsteps_trans _ (HB [19; 0] 33 1 12 ((1, 1) :: repeat (1, 2) 76 ++ (886, 2) :: (1, 1) :: repeat (1, 2) 2320 ++ (736, 2) :: (1, 1) :: repeat (1, 2) 12571 ++ (35290, 2) :: (1, 1) :: repeat (1, 2) 103382 ++ (56736, 2) :: (1, 1) :: repeat (1, 2) 595550 ++ (233769, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) 1)).
  {
    apply (pop12 1 [19; 0] 32 10 ((1, 1) :: repeat (1, 2) 76 ++ (886, 2) :: (1, 1) :: repeat (1, 2) 2320 ++ (736, 2) :: (1, 1) :: repeat (1, 2) 12571 ++ (35290, 2) :: (1, 1) :: repeat (1, 2) 103382 ++ (56736, 2) :: (1, 1) :: repeat (1, 2) 595550 ++ (233769, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) 1); closearith.
  }
  (* step 731: P POP *)
  apply (hsteps_trans _ (HB [19; 0] 34 1 13 (repeat (1, 2) 76 ++ (886, 2) :: (1, 1) :: repeat (1, 2) 2320 ++ (736, 2) :: (1, 1) :: repeat (1, 2) 12571 ++ (35290, 2) :: (1, 1) :: repeat (1, 2) 103382 ++ (56736, 2) :: (1, 1) :: repeat (1, 2) 595550 ++ (233769, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) 1)).
  {
    apply (sPOP1 [19; 0] 33 12 (repeat (1, 2) 76 ++ (886, 2) :: (1, 1) :: repeat (1, 2) 2320 ++ (736, 2) :: (1, 1) :: repeat (1, 2) 12571 ++ (35290, 2) :: (1, 1) :: repeat (1, 2) 103382 ++ (56736, 2) :: (1, 1) :: repeat (1, 2) 595550 ++ (233769, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) 1); closearith.
  }
  (* step 732: M pop12 (76,) *)
  apply (hsteps_trans _ (HB [19; 0] 110 1 165 ((886, 2) :: (1, 1) :: repeat (1, 2) 2320 ++ (736, 2) :: (1, 1) :: repeat (1, 2) 12571 ++ (35290, 2) :: (1, 1) :: repeat (1, 2) 103382 ++ (56736, 2) :: (1, 1) :: repeat (1, 2) 595550 ++ (233769, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) 1)).
  {
    apply (pop12 76 [19; 0] 34 13 ((886, 2) :: (1, 1) :: repeat (1, 2) 2320 ++ (736, 2) :: (1, 1) :: repeat (1, 2) 12571 ++ (35290, 2) :: (1, 1) :: repeat (1, 2) 103382 ++ (56736, 2) :: (1, 1) :: repeat (1, 2) 595550 ++ (233769, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) 1); closearith.
  }
  (* step 733: sTUP *)
  apply (hsteps_trans _ (HC [19; 0] 110 164 2 ((884, 2) :: (1, 1) :: repeat (1, 2) 2320 ++ (736, 2) :: (1, 1) :: repeat (1, 2) 12571 ++ (35290, 2) :: (1, 1) :: repeat (1, 2) 103382 ++ (56736, 2) :: (1, 1) :: repeat (1, 2) 595550 ++ (233769, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) 1)).
  {
    replace ((884, 2) :: (1, 1) :: repeat (1, 2) 2320 ++ (736, 2) :: (1, 1) :: repeat (1, 2) 12571 ++ (35290, 2) :: (1, 1) :: repeat (1, 2) 103382 ++ (56736, 2) :: (1, 1) :: repeat (1, 2) 595550 ++ (233769, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) with ((886 - 2, 2) :: (1, 1) :: repeat (1, 2) 2320 ++ (736, 2) :: (1, 1) :: repeat (1, 2) 12571 ++ (35290, 2) :: (1, 1) :: repeat (1, 2) 103382 ++ (56736, 2) :: (1, 1) :: repeat (1, 2) 595550 ++ (233769, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) by sec_eq.
    apply (sTUP [19; 0] 110 165 886 2 ((1, 1) :: repeat (1, 2) 2320 ++ (736, 2) :: (1, 1) :: repeat (1, 2) 12571 ++ (35290, 2) :: (1, 1) :: repeat (1, 2) 103382 ++ (56736, 2) :: (1, 1) :: repeat (1, 2) 595550 ++ (233769, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) 1); closearith.
  }
  (* step 734: hGRIND_even 80 *)
  apply (hsteps_trans _ (HB [19; 0] 109 1 164 ((2, 2) :: (884, 2) :: (1, 1) :: repeat (1, 2) 2320 ++ (736, 2) :: (1, 1) :: repeat (1, 2) 12571 ++ (35290, 2) :: (1, 1) :: repeat (1, 2) 103382 ++ (56736, 2) :: (1, 1) :: repeat (1, 2) 595550 ++ (233769, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) 1)).
  {
    apply (hGRIND_even 80 [19; 0] 109 ((884, 2) :: (1, 1) :: repeat (1, 2) 2320 ++ (736, 2) :: (1, 1) :: repeat (1, 2) 12571 ++ (35290, 2) :: (1, 1) :: repeat (1, 2) 103382 ++ (56736, 2) :: (1, 1) :: repeat (1, 2) 595550 ++ (233769, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) 1); closearith.
  }
  (* step 735: P TUP2_1 *)
  apply (hsteps_trans _ (HC [110; 19; 0] 164 1 2 ((882, 2) :: (1, 1) :: repeat (1, 2) 2320 ++ (736, 2) :: (1, 1) :: repeat (1, 2) 12571 ++ (35290, 2) :: (1, 1) :: repeat (1, 2) 103382 ++ (56736, 2) :: (1, 1) :: repeat (1, 2) 595550 ++ (233769, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) 1)).
  {
    replace ((882, 2) :: (1, 1) :: repeat (1, 2) 2320 ++ (736, 2) :: (1, 1) :: repeat (1, 2) 12571 ++ (35290, 2) :: (1, 1) :: repeat (1, 2) 103382 ++ (56736, 2) :: (1, 1) :: repeat (1, 2) 595550 ++ (233769, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) with ((884 - 2, 2) :: (1, 1) :: repeat (1, 2) 2320 ++ (736, 2) :: (1, 1) :: repeat (1, 2) 12571 ++ (35290, 2) :: (1, 1) :: repeat (1, 2) 103382 ++ (56736, 2) :: (1, 1) :: repeat (1, 2) 595550 ++ (233769, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) by sec_eq.
    apply (sTUP2_1 [19; 0] 109 163 884 ((1, 1) :: repeat (1, 2) 2320 ++ (736, 2) :: (1, 1) :: repeat (1, 2) 12571 ++ (35290, 2) :: (1, 1) :: repeat (1, 2) 103382 ++ (56736, 2) :: (1, 1) :: repeat (1, 2) 595550 ++ (233769, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) 1); closearith.
  }
  (* step 736: P TDN *)
  apply (hsteps_trans _ (HB [110; 19; 0] 164 1 4 ((882, 2) :: (1, 1) :: repeat (1, 2) 2320 ++ (736, 2) :: (1, 1) :: repeat (1, 2) 12571 ++ (35290, 2) :: (1, 1) :: repeat (1, 2) 103382 ++ (56736, 2) :: (1, 1) :: repeat (1, 2) 595550 ++ (233769, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) 1)).
  {
    apply (sTDN [110; 19; 0] 164 ((882, 2) :: (1, 1) :: repeat (1, 2) 2320 ++ (736, 2) :: (1, 1) :: repeat (1, 2) 12571 ++ (35290, 2) :: (1, 1) :: repeat (1, 2) 103382 ++ (56736, 2) :: (1, 1) :: repeat (1, 2) 595550 ++ (233769, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) 1).
  }
  (* step 737: sTUP *)
  apply (hsteps_trans _ (HC [110; 19; 0] 164 3 2 ((880, 2) :: (1, 1) :: repeat (1, 2) 2320 ++ (736, 2) :: (1, 1) :: repeat (1, 2) 12571 ++ (35290, 2) :: (1, 1) :: repeat (1, 2) 103382 ++ (56736, 2) :: (1, 1) :: repeat (1, 2) 595550 ++ (233769, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) 1)).
  {
    replace ((880, 2) :: (1, 1) :: repeat (1, 2) 2320 ++ (736, 2) :: (1, 1) :: repeat (1, 2) 12571 ++ (35290, 2) :: (1, 1) :: repeat (1, 2) 103382 ++ (56736, 2) :: (1, 1) :: repeat (1, 2) 595550 ++ (233769, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) with ((882 - 2, 2) :: (1, 1) :: repeat (1, 2) 2320 ++ (736, 2) :: (1, 1) :: repeat (1, 2) 12571 ++ (35290, 2) :: (1, 1) :: repeat (1, 2) 103382 ++ (56736, 2) :: (1, 1) :: repeat (1, 2) 595550 ++ (233769, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) by sec_eq.
    apply (sTUP [110; 19; 0] 164 4 882 2 ((1, 1) :: repeat (1, 2) 2320 ++ (736, 2) :: (1, 1) :: repeat (1, 2) 12571 ++ (35290, 2) :: (1, 1) :: repeat (1, 2) 103382 ++ (56736, 2) :: (1, 1) :: repeat (1, 2) 595550 ++ (233769, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) 1); closearith.
  }
  (* step 738: DIPGRIND 164 552 *)
  apply (hsteps_trans _ (HC [110; 19; 0] 0 3 2 (repeat (1, 2) 164 ++ (552, 2) :: (1, 1) :: repeat (1, 2) 2320 ++ (736, 2) :: (1, 1) :: repeat (1, 2) 12571 ++ (35290, 2) :: (1, 1) :: repeat (1, 2) 103382 ++ (56736, 2) :: (1, 1) :: repeat (1, 2) 595550 ++ (233769, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) 1)).
  {
    apply (DIPGRIND 164 552 [110; 19; 0] ((1, 1) :: repeat (1, 2) 2320 ++ (736, 2) :: (1, 1) :: repeat (1, 2) 12571 ++ (35290, 2) :: (1, 1) :: repeat (1, 2) 103382 ++ (56736, 2) :: (1, 1) :: repeat (1, 2) 595550 ++ (233769, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) 1); closearith.
  }
  (* step 739: P PX2A *)
  apply (hsteps_trans _ (HC [0] 18 108 2 ((1, 1) :: repeat (1, 2) 166 ++ (552, 2) :: (1, 1) :: repeat (1, 2) 2320 ++ (736, 2) :: (1, 1) :: repeat (1, 2) 12571 ++ (35290, 2) :: (1, 1) :: repeat (1, 2) 103382 ++ (56736, 2) :: (1, 1) :: repeat (1, 2) 595550 ++ (233769, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) 1)).
  {
    exact (hsteps_step _ _ _ (hPX2A 107 18 [0] (repeat (1, 2) 164 ++ (552, 2) :: (1, 1) :: repeat (1, 2) 2320 ++ (736, 2) :: (1, 1) :: repeat (1, 2) 12571 ++ (35290, 2) :: (1, 1) :: repeat (1, 2) 103382 ++ (56736, 2) :: (1, 1) :: repeat (1, 2) 595550 ++ (233769, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) 1) (hsteps_refl _)).
  }
  (* step 740: P PUSH *)
  apply (hsteps_trans _ (HC [0] 17 1 2 ((106, 2) :: (1, 1) :: repeat (1, 2) 166 ++ (552, 2) :: (1, 1) :: repeat (1, 2) 2320 ++ (736, 2) :: (1, 1) :: repeat (1, 2) 12571 ++ (35290, 2) :: (1, 1) :: repeat (1, 2) 103382 ++ (56736, 2) :: (1, 1) :: repeat (1, 2) 595550 ++ (233769, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) 1)).
  {
    replace ((106, 2) :: (1, 1) :: repeat (1, 2) 166 ++ (552, 2) :: (1, 1) :: repeat (1, 2) 2320 ++ (736, 2) :: (1, 1) :: repeat (1, 2) 12571 ++ (35290, 2) :: (1, 1) :: repeat (1, 2) 103382 ++ (56736, 2) :: (1, 1) :: repeat (1, 2) 595550 ++ (233769, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) with ((108 - 2, 2) :: (1, 1) :: repeat (1, 2) 166 ++ (552, 2) :: (1, 1) :: repeat (1, 2) 2320 ++ (736, 2) :: (1, 1) :: repeat (1, 2) 12571 ++ (35290, 2) :: (1, 1) :: repeat (1, 2) 103382 ++ (56736, 2) :: (1, 1) :: repeat (1, 2) 595550 ++ (233769, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) by sec_eq.
    apply (sPUSH [0] 17 108 ((1, 1) :: repeat (1, 2) 166 ++ (552, 2) :: (1, 1) :: repeat (1, 2) 2320 ++ (736, 2) :: (1, 1) :: repeat (1, 2) 12571 ++ (35290, 2) :: (1, 1) :: repeat (1, 2) 103382 ++ (56736, 2) :: (1, 1) :: repeat (1, 2) 595550 ++ (233769, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) 1); closearith.
  }
  (* step 741: P TDN *)
  apply (sTDN [0] 17 ((106, 2) :: (1, 1) :: repeat (1, 2) 166 ++ (552, 2) :: (1, 1) :: repeat (1, 2) 2320 ++ (736, 2) :: (1, 1) :: repeat (1, 2) 12571 ++ (35290, 2) :: (1, 1) :: repeat (1, 2) 103382 ++ (56736, 2) :: (1, 1) :: repeat (1, 2) 595550 ++ (233769, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) 1).
Qed.

(* CASCADE56p: steps 742-781 of the CASCADE56 chain. *)
Lemma CASCADE56p : forall w,
  hsteps (HB [0] 17 1 4 ((106, 2) :: (1, 1) :: repeat (1, 2) 166 ++ (552, 2) :: (1, 1) :: repeat (1, 2) 2320 ++ (736, 2) :: (1, 1) :: repeat (1, 2) 12571 ++ (35290, 2) :: (1, 1) :: repeat (1, 2) 103382 ++ (56736, 2) :: (1, 1) :: repeat (1, 2) 595550 ++ (233769, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) 1)
         (HB [25145; 13306; 4643; 2871; 335; 235; 42; 19] 35289 1 3 (repeat (1, 2) 103382 ++ (56736, 2) :: (1, 1) :: repeat (1, 2) 595550 ++ (233769, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) 1).
Proof.
  intro w.
  (* step 742: sTUP *)
  apply (hsteps_trans _ (HC [0] 17 3 2 ((104, 2) :: (1, 1) :: repeat (1, 2) 166 ++ (552, 2) :: (1, 1) :: repeat (1, 2) 2320 ++ (736, 2) :: (1, 1) :: repeat (1, 2) 12571 ++ (35290, 2) :: (1, 1) :: repeat (1, 2) 103382 ++ (56736, 2) :: (1, 1) :: repeat (1, 2) 595550 ++ (233769, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) 1)).
  {
    replace ((104, 2) :: (1, 1) :: repeat (1, 2) 166 ++ (552, 2) :: (1, 1) :: repeat (1, 2) 2320 ++ (736, 2) :: (1, 1) :: repeat (1, 2) 12571 ++ (35290, 2) :: (1, 1) :: repeat (1, 2) 103382 ++ (56736, 2) :: (1, 1) :: repeat (1, 2) 595550 ++ (233769, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) with ((106 - 2, 2) :: (1, 1) :: repeat (1, 2) 166 ++ (552, 2) :: (1, 1) :: repeat (1, 2) 2320 ++ (736, 2) :: (1, 1) :: repeat (1, 2) 12571 ++ (35290, 2) :: (1, 1) :: repeat (1, 2) 103382 ++ (56736, 2) :: (1, 1) :: repeat (1, 2) 595550 ++ (233769, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) by sec_eq.
    apply (sTUP [0] 17 4 106 2 ((1, 1) :: repeat (1, 2) 166 ++ (552, 2) :: (1, 1) :: repeat (1, 2) 2320 ++ (736, 2) :: (1, 1) :: repeat (1, 2) 12571 ++ (35290, 2) :: (1, 1) :: repeat (1, 2) 103382 ++ (56736, 2) :: (1, 1) :: repeat (1, 2) 595550 ++ (233769, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) 1); closearith.
  }
  (* step 743: DIPGRIND 17 70 *)
  apply (hsteps_trans _ (HC [0] 0 3 2 (repeat (1, 2) 17 ++ (70, 2) :: (1, 1) :: repeat (1, 2) 166 ++ (552, 2) :: (1, 1) :: repeat (1, 2) 2320 ++ (736, 2) :: (1, 1) :: repeat (1, 2) 12571 ++ (35290, 2) :: (1, 1) :: repeat (1, 2) 103382 ++ (56736, 2) :: (1, 1) :: repeat (1, 2) 595550 ++ (233769, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) 1)).
  {
    apply (DIPGRIND 17 70 [0] ((1, 1) :: repeat (1, 2) 166 ++ (552, 2) :: (1, 1) :: repeat (1, 2) 2320 ++ (736, 2) :: (1, 1) :: repeat (1, 2) 12571 ++ (35290, 2) :: (1, 1) :: repeat (1, 2) 103382 ++ (56736, 2) :: (1, 1) :: repeat (1, 2) 595550 ++ (233769, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) 1); closearith.
  }
  (* step 744: P PX2B0 *)
  apply (hsteps_trans _ (HB [] 0 1 5 (repeat (1, 2) 18 ++ (70, 2) :: (1, 1) :: repeat (1, 2) 166 ++ (552, 2) :: (1, 1) :: repeat (1, 2) 2320 ++ (736, 2) :: (1, 1) :: repeat (1, 2) 12571 ++ (35290, 2) :: (1, 1) :: repeat (1, 2) 103382 ++ (56736, 2) :: (1, 1) :: repeat (1, 2) 595550 ++ (233769, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) 1)).
  {
    exact (hsteps_step _ _ _ (hPX2B0 (repeat (1, 2) 17 ++ (70, 2) :: (1, 1) :: repeat (1, 2) 166 ++ (552, 2) :: (1, 1) :: repeat (1, 2) 2320 ++ (736, 2) :: (1, 1) :: repeat (1, 2) 12571 ++ (35290, 2) :: (1, 1) :: repeat (1, 2) 103382 ++ (56736, 2) :: (1, 1) :: repeat (1, 2) 595550 ++ (233769, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) 1) (hsteps_refl _)).
  }
  (* step 745: M pop12 (18,) *)
  apply (hsteps_trans _ (HB [] 18 1 41 ((70, 2) :: (1, 1) :: repeat (1, 2) 166 ++ (552, 2) :: (1, 1) :: repeat (1, 2) 2320 ++ (736, 2) :: (1, 1) :: repeat (1, 2) 12571 ++ (35290, 2) :: (1, 1) :: repeat (1, 2) 103382 ++ (56736, 2) :: (1, 1) :: repeat (1, 2) 595550 ++ (233769, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) 1)).
  {
    apply (pop12 18 [] 0 5 ((70, 2) :: (1, 1) :: repeat (1, 2) 166 ++ (552, 2) :: (1, 1) :: repeat (1, 2) 2320 ++ (736, 2) :: (1, 1) :: repeat (1, 2) 12571 ++ (35290, 2) :: (1, 1) :: repeat (1, 2) 103382 ++ (56736, 2) :: (1, 1) :: repeat (1, 2) 595550 ++ (233769, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) 1); closearith.
  }
  (* step 746: sTUP *)
  apply (hsteps_trans _ (HC [] 18 40 2 ((68, 2) :: (1, 1) :: repeat (1, 2) 166 ++ (552, 2) :: (1, 1) :: repeat (1, 2) 2320 ++ (736, 2) :: (1, 1) :: repeat (1, 2) 12571 ++ (35290, 2) :: (1, 1) :: repeat (1, 2) 103382 ++ (56736, 2) :: (1, 1) :: repeat (1, 2) 595550 ++ (233769, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) 1)).
  {
    replace ((68, 2) :: (1, 1) :: repeat (1, 2) 166 ++ (552, 2) :: (1, 1) :: repeat (1, 2) 2320 ++ (736, 2) :: (1, 1) :: repeat (1, 2) 12571 ++ (35290, 2) :: (1, 1) :: repeat (1, 2) 103382 ++ (56736, 2) :: (1, 1) :: repeat (1, 2) 595550 ++ (233769, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) with ((70 - 2, 2) :: (1, 1) :: repeat (1, 2) 166 ++ (552, 2) :: (1, 1) :: repeat (1, 2) 2320 ++ (736, 2) :: (1, 1) :: repeat (1, 2) 12571 ++ (35290, 2) :: (1, 1) :: repeat (1, 2) 103382 ++ (56736, 2) :: (1, 1) :: repeat (1, 2) 595550 ++ (233769, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) by sec_eq.
    apply (sTUP [] 18 41 70 2 ((1, 1) :: repeat (1, 2) 166 ++ (552, 2) :: (1, 1) :: repeat (1, 2) 2320 ++ (736, 2) :: (1, 1) :: repeat (1, 2) 12571 ++ (35290, 2) :: (1, 1) :: repeat (1, 2) 103382 ++ (56736, 2) :: (1, 1) :: repeat (1, 2) 595550 ++ (233769, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) 1); closearith.
  }
  (* step 747: P PUSH *)
  apply (hsteps_trans _ (HC [] 17 1 2 ((38, 2) :: (68, 2) :: (1, 1) :: repeat (1, 2) 166 ++ (552, 2) :: (1, 1) :: repeat (1, 2) 2320 ++ (736, 2) :: (1, 1) :: repeat (1, 2) 12571 ++ (35290, 2) :: (1, 1) :: repeat (1, 2) 103382 ++ (56736, 2) :: (1, 1) :: repeat (1, 2) 595550 ++ (233769, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) 1)).
  {
    replace ((38, 2) :: (68, 2) :: (1, 1) :: repeat (1, 2) 166 ++ (552, 2) :: (1, 1) :: repeat (1, 2) 2320 ++ (736, 2) :: (1, 1) :: repeat (1, 2) 12571 ++ (35290, 2) :: (1, 1) :: repeat (1, 2) 103382 ++ (56736, 2) :: (1, 1) :: repeat (1, 2) 595550 ++ (233769, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) with ((40 - 2, 2) :: (68, 2) :: (1, 1) :: repeat (1, 2) 166 ++ (552, 2) :: (1, 1) :: repeat (1, 2) 2320 ++ (736, 2) :: (1, 1) :: repeat (1, 2) 12571 ++ (35290, 2) :: (1, 1) :: repeat (1, 2) 103382 ++ (56736, 2) :: (1, 1) :: repeat (1, 2) 595550 ++ (233769, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) by sec_eq.
    apply (sPUSH [] 17 40 ((68, 2) :: (1, 1) :: repeat (1, 2) 166 ++ (552, 2) :: (1, 1) :: repeat (1, 2) 2320 ++ (736, 2) :: (1, 1) :: repeat (1, 2) 12571 ++ (35290, 2) :: (1, 1) :: repeat (1, 2) 103382 ++ (56736, 2) :: (1, 1) :: repeat (1, 2) 595550 ++ (233769, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) 1); closearith.
  }
  (* step 748: P TDN *)
  apply (hsteps_trans _ (HB [] 17 1 4 ((38, 2) :: (68, 2) :: (1, 1) :: repeat (1, 2) 166 ++ (552, 2) :: (1, 1) :: repeat (1, 2) 2320 ++ (736, 2) :: (1, 1) :: repeat (1, 2) 12571 ++ (35290, 2) :: (1, 1) :: repeat (1, 2) 103382 ++ (56736, 2) :: (1, 1) :: repeat (1, 2) 595550 ++ (233769, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) 1)).
  {
    apply (sTDN [] 17 ((38, 2) :: (68, 2) :: (1, 1) :: repeat (1, 2) 166 ++ (552, 2) :: (1, 1) :: repeat (1, 2) 2320 ++ (736, 2) :: (1, 1) :: repeat (1, 2) 12571 ++ (35290, 2) :: (1, 1) :: repeat (1, 2) 103382 ++ (56736, 2) :: (1, 1) :: repeat (1, 2) 595550 ++ (233769, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) 1).
  }
  (* step 749: sTUP *)
  apply (hsteps_trans _ (HC [] 17 3 2 ((36, 2) :: (68, 2) :: (1, 1) :: repeat (1, 2) 166 ++ (552, 2) :: (1, 1) :: repeat (1, 2) 2320 ++ (736, 2) :: (1, 1) :: repeat (1, 2) 12571 ++ (35290, 2) :: (1, 1) :: repeat (1, 2) 103382 ++ (56736, 2) :: (1, 1) :: repeat (1, 2) 595550 ++ (233769, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) 1)).
  {
    replace ((36, 2) :: (68, 2) :: (1, 1) :: repeat (1, 2) 166 ++ (552, 2) :: (1, 1) :: repeat (1, 2) 2320 ++ (736, 2) :: (1, 1) :: repeat (1, 2) 12571 ++ (35290, 2) :: (1, 1) :: repeat (1, 2) 103382 ++ (56736, 2) :: (1, 1) :: repeat (1, 2) 595550 ++ (233769, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) with ((38 - 2, 2) :: (68, 2) :: (1, 1) :: repeat (1, 2) 166 ++ (552, 2) :: (1, 1) :: repeat (1, 2) 2320 ++ (736, 2) :: (1, 1) :: repeat (1, 2) 12571 ++ (35290, 2) :: (1, 1) :: repeat (1, 2) 103382 ++ (56736, 2) :: (1, 1) :: repeat (1, 2) 595550 ++ (233769, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) by sec_eq.
    apply (sTUP [] 17 4 38 2 ((68, 2) :: (1, 1) :: repeat (1, 2) 166 ++ (552, 2) :: (1, 1) :: repeat (1, 2) 2320 ++ (736, 2) :: (1, 1) :: repeat (1, 2) 12571 ++ (35290, 2) :: (1, 1) :: repeat (1, 2) 103382 ++ (56736, 2) :: (1, 1) :: repeat (1, 2) 595550 ++ (233769, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) 1); closearith.
  }
  (* step 750: DIPGRIND 17 2 *)
  apply (hsteps_trans _ (HC [] 0 3 2 (repeat (1, 2) 17 ++ (2, 2) :: (68, 2) :: (1, 1) :: repeat (1, 2) 166 ++ (552, 2) :: (1, 1) :: repeat (1, 2) 2320 ++ (736, 2) :: (1, 1) :: repeat (1, 2) 12571 ++ (35290, 2) :: (1, 1) :: repeat (1, 2) 103382 ++ (56736, 2) :: (1, 1) :: repeat (1, 2) 595550 ++ (233769, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) 1)).
  {
    apply (DIPGRIND 17 2 [] ((68, 2) :: (1, 1) :: repeat (1, 2) 166 ++ (552, 2) :: (1, 1) :: repeat (1, 2) 2320 ++ (736, 2) :: (1, 1) :: repeat (1, 2) 12571 ++ (35290, 2) :: (1, 1) :: repeat (1, 2) 103382 ++ (56736, 2) :: (1, 1) :: repeat (1, 2) 595550 ++ (233769, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) 1); closearith.
  }
  (* step 751: P PUSHX *)
  apply (hsteps_trans _ (HB [] 1 1 7 (repeat (1, 2) 17 ++ (2, 2) :: (68, 2) :: (1, 1) :: repeat (1, 2) 166 ++ (552, 2) :: (1, 1) :: repeat (1, 2) 2320 ++ (736, 2) :: (1, 1) :: repeat (1, 2) 12571 ++ (35290, 2) :: (1, 1) :: repeat (1, 2) 103382 ++ (56736, 2) :: (1, 1) :: repeat (1, 2) 595550 ++ (233769, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) 1)).
  {
    exact (hsteps_step _ _ _ (hPUSHX (repeat (1, 2) 17 ++ (2, 2) :: (68, 2) :: (1, 1) :: repeat (1, 2) 166 ++ (552, 2) :: (1, 1) :: repeat (1, 2) 2320 ++ (736, 2) :: (1, 1) :: repeat (1, 2) 12571 ++ (35290, 2) :: (1, 1) :: repeat (1, 2) 103382 ++ (56736, 2) :: (1, 1) :: repeat (1, 2) 595550 ++ (233769, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) 1) (hsteps_refl _)).
  }
  (* step 752: M pop12 (17,) *)
  apply (hsteps_trans _ (HB [] 18 1 41 ((2, 2) :: (68, 2) :: (1, 1) :: repeat (1, 2) 166 ++ (552, 2) :: (1, 1) :: repeat (1, 2) 2320 ++ (736, 2) :: (1, 1) :: repeat (1, 2) 12571 ++ (35290, 2) :: (1, 1) :: repeat (1, 2) 103382 ++ (56736, 2) :: (1, 1) :: repeat (1, 2) 595550 ++ (233769, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) 1)).
  {
    apply (pop12 17 [] 1 7 ((2, 2) :: (68, 2) :: (1, 1) :: repeat (1, 2) 166 ++ (552, 2) :: (1, 1) :: repeat (1, 2) 2320 ++ (736, 2) :: (1, 1) :: repeat (1, 2) 12571 ++ (35290, 2) :: (1, 1) :: repeat (1, 2) 103382 ++ (56736, 2) :: (1, 1) :: repeat (1, 2) 595550 ++ (233769, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) 1); closearith.
  }
  (* step 753: P TUP2_1 *)
  apply (hsteps_trans _ (HC [19] 41 1 2 ((66, 2) :: (1, 1) :: repeat (1, 2) 166 ++ (552, 2) :: (1, 1) :: repeat (1, 2) 2320 ++ (736, 2) :: (1, 1) :: repeat (1, 2) 12571 ++ (35290, 2) :: (1, 1) :: repeat (1, 2) 103382 ++ (56736, 2) :: (1, 1) :: repeat (1, 2) 595550 ++ (233769, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) 1)).
  {
    replace ((66, 2) :: (1, 1) :: repeat (1, 2) 166 ++ (552, 2) :: (1, 1) :: repeat (1, 2) 2320 ++ (736, 2) :: (1, 1) :: repeat (1, 2) 12571 ++ (35290, 2) :: (1, 1) :: repeat (1, 2) 103382 ++ (56736, 2) :: (1, 1) :: repeat (1, 2) 595550 ++ (233769, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) with ((68 - 2, 2) :: (1, 1) :: repeat (1, 2) 166 ++ (552, 2) :: (1, 1) :: repeat (1, 2) 2320 ++ (736, 2) :: (1, 1) :: repeat (1, 2) 12571 ++ (35290, 2) :: (1, 1) :: repeat (1, 2) 103382 ++ (56736, 2) :: (1, 1) :: repeat (1, 2) 595550 ++ (233769, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) by sec_eq.
    apply (sTUP2_1 [] 18 40 68 ((1, 1) :: repeat (1, 2) 166 ++ (552, 2) :: (1, 1) :: repeat (1, 2) 2320 ++ (736, 2) :: (1, 1) :: repeat (1, 2) 12571 ++ (35290, 2) :: (1, 1) :: repeat (1, 2) 103382 ++ (56736, 2) :: (1, 1) :: repeat (1, 2) 595550 ++ (233769, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) 1); closearith.
  }
  (* step 754: P TDN *)
  apply (hsteps_trans _ (HB [19] 41 1 4 ((66, 2) :: (1, 1) :: repeat (1, 2) 166 ++ (552, 2) :: (1, 1) :: repeat (1, 2) 2320 ++ (736, 2) :: (1, 1) :: repeat (1, 2) 12571 ++ (35290, 2) :: (1, 1) :: repeat (1, 2) 103382 ++ (56736, 2) :: (1, 1) :: repeat (1, 2) 595550 ++ (233769, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) 1)).
  {
    apply (sTDN [19] 41 ((66, 2) :: (1, 1) :: repeat (1, 2) 166 ++ (552, 2) :: (1, 1) :: repeat (1, 2) 2320 ++ (736, 2) :: (1, 1) :: repeat (1, 2) 12571 ++ (35290, 2) :: (1, 1) :: repeat (1, 2) 103382 ++ (56736, 2) :: (1, 1) :: repeat (1, 2) 595550 ++ (233769, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) 1).
  }
  (* step 755: sTUP *)
  apply (hsteps_trans _ (HC [19] 41 3 2 ((64, 2) :: (1, 1) :: repeat (1, 2) 166 ++ (552, 2) :: (1, 1) :: repeat (1, 2) 2320 ++ (736, 2) :: (1, 1) :: repeat (1, 2) 12571 ++ (35290, 2) :: (1, 1) :: repeat (1, 2) 103382 ++ (56736, 2) :: (1, 1) :: repeat (1, 2) 595550 ++ (233769, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) 1)).
  {
    replace ((64, 2) :: (1, 1) :: repeat (1, 2) 166 ++ (552, 2) :: (1, 1) :: repeat (1, 2) 2320 ++ (736, 2) :: (1, 1) :: repeat (1, 2) 12571 ++ (35290, 2) :: (1, 1) :: repeat (1, 2) 103382 ++ (56736, 2) :: (1, 1) :: repeat (1, 2) 595550 ++ (233769, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) with ((66 - 2, 2) :: (1, 1) :: repeat (1, 2) 166 ++ (552, 2) :: (1, 1) :: repeat (1, 2) 2320 ++ (736, 2) :: (1, 1) :: repeat (1, 2) 12571 ++ (35290, 2) :: (1, 1) :: repeat (1, 2) 103382 ++ (56736, 2) :: (1, 1) :: repeat (1, 2) 595550 ++ (233769, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) by sec_eq.
    apply (sTUP [19] 41 4 66 2 ((1, 1) :: repeat (1, 2) 166 ++ (552, 2) :: (1, 1) :: repeat (1, 2) 2320 ++ (736, 2) :: (1, 1) :: repeat (1, 2) 12571 ++ (35290, 2) :: (1, 1) :: repeat (1, 2) 103382 ++ (56736, 2) :: (1, 1) :: repeat (1, 2) 595550 ++ (233769, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) 1); closearith.
  }
  (* step 756: CLEANG_even 31 *)
  apply (hsteps_trans _ (HB [19] 41 1 68 ((2, 2) :: (1, 1) :: repeat (1, 2) 166 ++ (552, 2) :: (1, 1) :: repeat (1, 2) 2320 ++ (736, 2) :: (1, 1) :: repeat (1, 2) 12571 ++ (35290, 2) :: (1, 1) :: repeat (1, 2) 103382 ++ (56736, 2) :: (1, 1) :: repeat (1, 2) 595550 ++ (233769, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) 1)).
  {
    apply (CLEANG_even 31 [19] 41 ((1, 1) :: repeat (1, 2) 166 ++ (552, 2) :: (1, 1) :: repeat (1, 2) 2320 ++ (736, 2) :: (1, 1) :: repeat (1, 2) 12571 ++ (35290, 2) :: (1, 1) :: repeat (1, 2) 103382 ++ (56736, 2) :: (1, 1) :: repeat (1, 2) 595550 ++ (233769, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) 1); closearith.
  }
  (* step 757: P TRANS2_1 *)
  apply (hsteps_trans _ (HB [42; 19] 69 1 3 (repeat (1, 2) 166 ++ (552, 2) :: (1, 1) :: repeat (1, 2) 2320 ++ (736, 2) :: (1, 1) :: repeat (1, 2) 12571 ++ (35290, 2) :: (1, 1) :: repeat (1, 2) 103382 ++ (56736, 2) :: (1, 1) :: repeat (1, 2) 595550 ++ (233769, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) 1)).
  {
    apply (sTRANS2_1 [19] 41 67 1 (repeat (1, 2) 166 ++ (552, 2) :: (1, 1) :: repeat (1, 2) 2320 ++ (736, 2) :: (1, 1) :: repeat (1, 2) 12571 ++ (35290, 2) :: (1, 1) :: repeat (1, 2) 103382 ++ (56736, 2) :: (1, 1) :: repeat (1, 2) 595550 ++ (233769, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) 1); closearith.
  }
  (* step 758: M pop12 (166,) *)
  apply (hsteps_trans _ (HB [42; 19] 235 1 335 ((552, 2) :: (1, 1) :: repeat (1, 2) 2320 ++ (736, 2) :: (1, 1) :: repeat (1, 2) 12571 ++ (35290, 2) :: (1, 1) :: repeat (1, 2) 103382 ++ (56736, 2) :: (1, 1) :: repeat (1, 2) 595550 ++ (233769, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) 1)).
  {
    apply (pop12 166 [42; 19] 69 3 ((552, 2) :: (1, 1) :: repeat (1, 2) 2320 ++ (736, 2) :: (1, 1) :: repeat (1, 2) 12571 ++ (35290, 2) :: (1, 1) :: repeat (1, 2) 103382 ++ (56736, 2) :: (1, 1) :: repeat (1, 2) 595550 ++ (233769, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) 1); closearith.
  }
  (* step 759: sTUP *)
  apply (hsteps_trans _ (HC [42; 19] 235 334 2 ((550, 2) :: (1, 1) :: repeat (1, 2) 2320 ++ (736, 2) :: (1, 1) :: repeat (1, 2) 12571 ++ (35290, 2) :: (1, 1) :: repeat (1, 2) 103382 ++ (56736, 2) :: (1, 1) :: repeat (1, 2) 595550 ++ (233769, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) 1)).
  {
    replace ((550, 2) :: (1, 1) :: repeat (1, 2) 2320 ++ (736, 2) :: (1, 1) :: repeat (1, 2) 12571 ++ (35290, 2) :: (1, 1) :: repeat (1, 2) 103382 ++ (56736, 2) :: (1, 1) :: repeat (1, 2) 595550 ++ (233769, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) with ((552 - 2, 2) :: (1, 1) :: repeat (1, 2) 2320 ++ (736, 2) :: (1, 1) :: repeat (1, 2) 12571 ++ (35290, 2) :: (1, 1) :: repeat (1, 2) 103382 ++ (56736, 2) :: (1, 1) :: repeat (1, 2) 595550 ++ (233769, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) by sec_eq.
    apply (sTUP [42; 19] 235 335 552 2 ((1, 1) :: repeat (1, 2) 2320 ++ (736, 2) :: (1, 1) :: repeat (1, 2) 12571 ++ (35290, 2) :: (1, 1) :: repeat (1, 2) 103382 ++ (56736, 2) :: (1, 1) :: repeat (1, 2) 595550 ++ (233769, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) 1); closearith.
  }
  (* step 760: hGRIND_even 165 *)
  apply (hsteps_trans _ (HB [42; 19] 234 1 334 ((2, 2) :: (550, 2) :: (1, 1) :: repeat (1, 2) 2320 ++ (736, 2) :: (1, 1) :: repeat (1, 2) 12571 ++ (35290, 2) :: (1, 1) :: repeat (1, 2) 103382 ++ (56736, 2) :: (1, 1) :: repeat (1, 2) 595550 ++ (233769, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) 1)).
  {
    apply (hGRIND_even 165 [42; 19] 234 ((550, 2) :: (1, 1) :: repeat (1, 2) 2320 ++ (736, 2) :: (1, 1) :: repeat (1, 2) 12571 ++ (35290, 2) :: (1, 1) :: repeat (1, 2) 103382 ++ (56736, 2) :: (1, 1) :: repeat (1, 2) 595550 ++ (233769, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) 1); closearith.
  }
  (* step 761: P TUP2_1 *)
  apply (hsteps_trans _ (HC [235; 42; 19] 334 1 2 ((548, 2) :: (1, 1) :: repeat (1, 2) 2320 ++ (736, 2) :: (1, 1) :: repeat (1, 2) 12571 ++ (35290, 2) :: (1, 1) :: repeat (1, 2) 103382 ++ (56736, 2) :: (1, 1) :: repeat (1, 2) 595550 ++ (233769, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) 1)).
  {
    replace ((548, 2) :: (1, 1) :: repeat (1, 2) 2320 ++ (736, 2) :: (1, 1) :: repeat (1, 2) 12571 ++ (35290, 2) :: (1, 1) :: repeat (1, 2) 103382 ++ (56736, 2) :: (1, 1) :: repeat (1, 2) 595550 ++ (233769, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) with ((550 - 2, 2) :: (1, 1) :: repeat (1, 2) 2320 ++ (736, 2) :: (1, 1) :: repeat (1, 2) 12571 ++ (35290, 2) :: (1, 1) :: repeat (1, 2) 103382 ++ (56736, 2) :: (1, 1) :: repeat (1, 2) 595550 ++ (233769, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) by sec_eq.
    apply (sTUP2_1 [42; 19] 234 333 550 ((1, 1) :: repeat (1, 2) 2320 ++ (736, 2) :: (1, 1) :: repeat (1, 2) 12571 ++ (35290, 2) :: (1, 1) :: repeat (1, 2) 103382 ++ (56736, 2) :: (1, 1) :: repeat (1, 2) 595550 ++ (233769, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) 1); closearith.
  }
  (* step 762: P TDN *)
  apply (hsteps_trans _ (HB [235; 42; 19] 334 1 4 ((548, 2) :: (1, 1) :: repeat (1, 2) 2320 ++ (736, 2) :: (1, 1) :: repeat (1, 2) 12571 ++ (35290, 2) :: (1, 1) :: repeat (1, 2) 103382 ++ (56736, 2) :: (1, 1) :: repeat (1, 2) 595550 ++ (233769, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) 1)).
  {
    apply (sTDN [235; 42; 19] 334 ((548, 2) :: (1, 1) :: repeat (1, 2) 2320 ++ (736, 2) :: (1, 1) :: repeat (1, 2) 12571 ++ (35290, 2) :: (1, 1) :: repeat (1, 2) 103382 ++ (56736, 2) :: (1, 1) :: repeat (1, 2) 595550 ++ (233769, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) 1).
  }
  (* step 763: sTUP *)
  apply (hsteps_trans _ (HC [235; 42; 19] 334 3 2 ((546, 2) :: (1, 1) :: repeat (1, 2) 2320 ++ (736, 2) :: (1, 1) :: repeat (1, 2) 12571 ++ (35290, 2) :: (1, 1) :: repeat (1, 2) 103382 ++ (56736, 2) :: (1, 1) :: repeat (1, 2) 595550 ++ (233769, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) 1)).
  {
    replace ((546, 2) :: (1, 1) :: repeat (1, 2) 2320 ++ (736, 2) :: (1, 1) :: repeat (1, 2) 12571 ++ (35290, 2) :: (1, 1) :: repeat (1, 2) 103382 ++ (56736, 2) :: (1, 1) :: repeat (1, 2) 595550 ++ (233769, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) with ((548 - 2, 2) :: (1, 1) :: repeat (1, 2) 2320 ++ (736, 2) :: (1, 1) :: repeat (1, 2) 12571 ++ (35290, 2) :: (1, 1) :: repeat (1, 2) 103382 ++ (56736, 2) :: (1, 1) :: repeat (1, 2) 595550 ++ (233769, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) by sec_eq.
    apply (sTUP [235; 42; 19] 334 4 548 2 ((1, 1) :: repeat (1, 2) 2320 ++ (736, 2) :: (1, 1) :: repeat (1, 2) 12571 ++ (35290, 2) :: (1, 1) :: repeat (1, 2) 103382 ++ (56736, 2) :: (1, 1) :: repeat (1, 2) 595550 ++ (233769, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) 1); closearith.
  }
  (* step 764: CLEANG_even 272 *)
  apply (hsteps_trans _ (HB [235; 42; 19] 334 1 550 ((2, 2) :: (1, 1) :: repeat (1, 2) 2320 ++ (736, 2) :: (1, 1) :: repeat (1, 2) 12571 ++ (35290, 2) :: (1, 1) :: repeat (1, 2) 103382 ++ (56736, 2) :: (1, 1) :: repeat (1, 2) 595550 ++ (233769, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) 1)).
  {
    apply (CLEANG_even 272 [235; 42; 19] 334 ((1, 1) :: repeat (1, 2) 2320 ++ (736, 2) :: (1, 1) :: repeat (1, 2) 12571 ++ (35290, 2) :: (1, 1) :: repeat (1, 2) 103382 ++ (56736, 2) :: (1, 1) :: repeat (1, 2) 595550 ++ (233769, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) 1); closearith.
  }
  (* step 765: P TRANS2_1 *)
  apply (hsteps_trans _ (HB [335; 235; 42; 19] 551 1 3 (repeat (1, 2) 2320 ++ (736, 2) :: (1, 1) :: repeat (1, 2) 12571 ++ (35290, 2) :: (1, 1) :: repeat (1, 2) 103382 ++ (56736, 2) :: (1, 1) :: repeat (1, 2) 595550 ++ (233769, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) 1)).
  {
    apply (sTRANS2_1 [235; 42; 19] 334 549 1 (repeat (1, 2) 2320 ++ (736, 2) :: (1, 1) :: repeat (1, 2) 12571 ++ (35290, 2) :: (1, 1) :: repeat (1, 2) 103382 ++ (56736, 2) :: (1, 1) :: repeat (1, 2) 595550 ++ (233769, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) 1); closearith.
  }
  (* step 766: M pop12 (2320,) *)
  apply (hsteps_trans _ (HB [335; 235; 42; 19] 2871 1 4643 ((736, 2) :: (1, 1) :: repeat (1, 2) 12571 ++ (35290, 2) :: (1, 1) :: repeat (1, 2) 103382 ++ (56736, 2) :: (1, 1) :: repeat (1, 2) 595550 ++ (233769, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) 1)).
  {
    apply (pop12 2320 [335; 235; 42; 19] 551 3 ((736, 2) :: (1, 1) :: repeat (1, 2) 12571 ++ (35290, 2) :: (1, 1) :: repeat (1, 2) 103382 ++ (56736, 2) :: (1, 1) :: repeat (1, 2) 595550 ++ (233769, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) 1); closearith.
  }
  (* step 767: sTUP *)
  apply (hsteps_trans _ (HC [335; 235; 42; 19] 2871 4642 2 ((734, 2) :: (1, 1) :: repeat (1, 2) 12571 ++ (35290, 2) :: (1, 1) :: repeat (1, 2) 103382 ++ (56736, 2) :: (1, 1) :: repeat (1, 2) 595550 ++ (233769, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) 1)).
  {
    replace ((734, 2) :: (1, 1) :: repeat (1, 2) 12571 ++ (35290, 2) :: (1, 1) :: repeat (1, 2) 103382 ++ (56736, 2) :: (1, 1) :: repeat (1, 2) 595550 ++ (233769, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) with ((736 - 2, 2) :: (1, 1) :: repeat (1, 2) 12571 ++ (35290, 2) :: (1, 1) :: repeat (1, 2) 103382 ++ (56736, 2) :: (1, 1) :: repeat (1, 2) 595550 ++ (233769, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) by sec_eq.
    apply (sTUP [335; 235; 42; 19] 2871 4643 736 2 ((1, 1) :: repeat (1, 2) 12571 ++ (35290, 2) :: (1, 1) :: repeat (1, 2) 103382 ++ (56736, 2) :: (1, 1) :: repeat (1, 2) 595550 ++ (233769, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) 1); closearith.
  }
  (* step 768: hGRIND_even 2319 *)
  apply (hsteps_trans _ (HB [335; 235; 42; 19] 2870 1 4642 ((2, 2) :: (734, 2) :: (1, 1) :: repeat (1, 2) 12571 ++ (35290, 2) :: (1, 1) :: repeat (1, 2) 103382 ++ (56736, 2) :: (1, 1) :: repeat (1, 2) 595550 ++ (233769, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) 1)).
  {
    apply (hGRIND_even 2319 [335; 235; 42; 19] 2870 ((734, 2) :: (1, 1) :: repeat (1, 2) 12571 ++ (35290, 2) :: (1, 1) :: repeat (1, 2) 103382 ++ (56736, 2) :: (1, 1) :: repeat (1, 2) 595550 ++ (233769, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) 1); closearith.
  }
  (* step 769: P TUP2_1 *)
  apply (hsteps_trans _ (HC [2871; 335; 235; 42; 19] 4642 1 2 ((732, 2) :: (1, 1) :: repeat (1, 2) 12571 ++ (35290, 2) :: (1, 1) :: repeat (1, 2) 103382 ++ (56736, 2) :: (1, 1) :: repeat (1, 2) 595550 ++ (233769, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) 1)).
  {
    replace ((732, 2) :: (1, 1) :: repeat (1, 2) 12571 ++ (35290, 2) :: (1, 1) :: repeat (1, 2) 103382 ++ (56736, 2) :: (1, 1) :: repeat (1, 2) 595550 ++ (233769, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) with ((734 - 2, 2) :: (1, 1) :: repeat (1, 2) 12571 ++ (35290, 2) :: (1, 1) :: repeat (1, 2) 103382 ++ (56736, 2) :: (1, 1) :: repeat (1, 2) 595550 ++ (233769, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) by sec_eq.
    apply (sTUP2_1 [335; 235; 42; 19] 2870 4641 734 ((1, 1) :: repeat (1, 2) 12571 ++ (35290, 2) :: (1, 1) :: repeat (1, 2) 103382 ++ (56736, 2) :: (1, 1) :: repeat (1, 2) 595550 ++ (233769, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) 1); closearith.
  }
  (* step 770: P TDN *)
  apply (hsteps_trans _ (HB [2871; 335; 235; 42; 19] 4642 1 4 ((732, 2) :: (1, 1) :: repeat (1, 2) 12571 ++ (35290, 2) :: (1, 1) :: repeat (1, 2) 103382 ++ (56736, 2) :: (1, 1) :: repeat (1, 2) 595550 ++ (233769, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) 1)).
  {
    apply (sTDN [2871; 335; 235; 42; 19] 4642 ((732, 2) :: (1, 1) :: repeat (1, 2) 12571 ++ (35290, 2) :: (1, 1) :: repeat (1, 2) 103382 ++ (56736, 2) :: (1, 1) :: repeat (1, 2) 595550 ++ (233769, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) 1).
  }
  (* step 771: sTUP *)
  apply (hsteps_trans _ (HC [2871; 335; 235; 42; 19] 4642 3 2 ((730, 2) :: (1, 1) :: repeat (1, 2) 12571 ++ (35290, 2) :: (1, 1) :: repeat (1, 2) 103382 ++ (56736, 2) :: (1, 1) :: repeat (1, 2) 595550 ++ (233769, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) 1)).
  {
    replace ((730, 2) :: (1, 1) :: repeat (1, 2) 12571 ++ (35290, 2) :: (1, 1) :: repeat (1, 2) 103382 ++ (56736, 2) :: (1, 1) :: repeat (1, 2) 595550 ++ (233769, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) with ((732 - 2, 2) :: (1, 1) :: repeat (1, 2) 12571 ++ (35290, 2) :: (1, 1) :: repeat (1, 2) 103382 ++ (56736, 2) :: (1, 1) :: repeat (1, 2) 595550 ++ (233769, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) by sec_eq.
    apply (sTUP [2871; 335; 235; 42; 19] 4642 4 732 2 ((1, 1) :: repeat (1, 2) 12571 ++ (35290, 2) :: (1, 1) :: repeat (1, 2) 103382 ++ (56736, 2) :: (1, 1) :: repeat (1, 2) 595550 ++ (233769, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) 1); closearith.
  }
  (* step 772: CLEANG_even 364 *)
  apply (hsteps_trans _ (HB [2871; 335; 235; 42; 19] 4642 1 734 ((2, 2) :: (1, 1) :: repeat (1, 2) 12571 ++ (35290, 2) :: (1, 1) :: repeat (1, 2) 103382 ++ (56736, 2) :: (1, 1) :: repeat (1, 2) 595550 ++ (233769, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) 1)).
  {
    apply (CLEANG_even 364 [2871; 335; 235; 42; 19] 4642 ((1, 1) :: repeat (1, 2) 12571 ++ (35290, 2) :: (1, 1) :: repeat (1, 2) 103382 ++ (56736, 2) :: (1, 1) :: repeat (1, 2) 595550 ++ (233769, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) 1); closearith.
  }
  (* step 773: P TRANS2_1 *)
  apply (hsteps_trans _ (HB [4643; 2871; 335; 235; 42; 19] 735 1 3 (repeat (1, 2) 12571 ++ (35290, 2) :: (1, 1) :: repeat (1, 2) 103382 ++ (56736, 2) :: (1, 1) :: repeat (1, 2) 595550 ++ (233769, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) 1)).
  {
    apply (sTRANS2_1 [2871; 335; 235; 42; 19] 4642 733 1 (repeat (1, 2) 12571 ++ (35290, 2) :: (1, 1) :: repeat (1, 2) 103382 ++ (56736, 2) :: (1, 1) :: repeat (1, 2) 595550 ++ (233769, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) 1); closearith.
  }
  (* step 774: M pop12 (12571,) *)
  apply (hsteps_trans _ (HB [4643; 2871; 335; 235; 42; 19] 13306 1 25145 ((35290, 2) :: (1, 1) :: repeat (1, 2) 103382 ++ (56736, 2) :: (1, 1) :: repeat (1, 2) 595550 ++ (233769, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) 1)).
  {
    apply (pop12 12571 [4643; 2871; 335; 235; 42; 19] 735 3 ((35290, 2) :: (1, 1) :: repeat (1, 2) 103382 ++ (56736, 2) :: (1, 1) :: repeat (1, 2) 595550 ++ (233769, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) 1); closearith.
  }
  (* step 775: sTUP *)
  apply (hsteps_trans _ (HC [4643; 2871; 335; 235; 42; 19] 13306 25144 2 ((35288, 2) :: (1, 1) :: repeat (1, 2) 103382 ++ (56736, 2) :: (1, 1) :: repeat (1, 2) 595550 ++ (233769, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) 1)).
  {
    replace ((35288, 2) :: (1, 1) :: repeat (1, 2) 103382 ++ (56736, 2) :: (1, 1) :: repeat (1, 2) 595550 ++ (233769, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) with ((35290 - 2, 2) :: (1, 1) :: repeat (1, 2) 103382 ++ (56736, 2) :: (1, 1) :: repeat (1, 2) 595550 ++ (233769, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) by sec_eq.
    apply (sTUP [4643; 2871; 335; 235; 42; 19] 13306 25145 35290 2 ((1, 1) :: repeat (1, 2) 103382 ++ (56736, 2) :: (1, 1) :: repeat (1, 2) 595550 ++ (233769, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) 1); closearith.
  }
  (* step 776: hGRIND_even 12570 *)
  apply (hsteps_trans _ (HB [4643; 2871; 335; 235; 42; 19] 13305 1 25144 ((2, 2) :: (35288, 2) :: (1, 1) :: repeat (1, 2) 103382 ++ (56736, 2) :: (1, 1) :: repeat (1, 2) 595550 ++ (233769, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) 1)).
  {
    apply (hGRIND_even 12570 [4643; 2871; 335; 235; 42; 19] 13305 ((35288, 2) :: (1, 1) :: repeat (1, 2) 103382 ++ (56736, 2) :: (1, 1) :: repeat (1, 2) 595550 ++ (233769, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) 1); closearith.
  }
  (* step 777: P TUP2_1 *)
  apply (hsteps_trans _ (HC [13306; 4643; 2871; 335; 235; 42; 19] 25144 1 2 ((35286, 2) :: (1, 1) :: repeat (1, 2) 103382 ++ (56736, 2) :: (1, 1) :: repeat (1, 2) 595550 ++ (233769, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) 1)).
  {
    replace ((35286, 2) :: (1, 1) :: repeat (1, 2) 103382 ++ (56736, 2) :: (1, 1) :: repeat (1, 2) 595550 ++ (233769, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) with ((35288 - 2, 2) :: (1, 1) :: repeat (1, 2) 103382 ++ (56736, 2) :: (1, 1) :: repeat (1, 2) 595550 ++ (233769, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) by sec_eq.
    apply (sTUP2_1 [4643; 2871; 335; 235; 42; 19] 13305 25143 35288 ((1, 1) :: repeat (1, 2) 103382 ++ (56736, 2) :: (1, 1) :: repeat (1, 2) 595550 ++ (233769, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) 1); closearith.
  }
  (* step 778: P TDN *)
  apply (hsteps_trans _ (HB [13306; 4643; 2871; 335; 235; 42; 19] 25144 1 4 ((35286, 2) :: (1, 1) :: repeat (1, 2) 103382 ++ (56736, 2) :: (1, 1) :: repeat (1, 2) 595550 ++ (233769, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) 1)).
  {
    apply (sTDN [13306; 4643; 2871; 335; 235; 42; 19] 25144 ((35286, 2) :: (1, 1) :: repeat (1, 2) 103382 ++ (56736, 2) :: (1, 1) :: repeat (1, 2) 595550 ++ (233769, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) 1).
  }
  (* step 779: sTUP *)
  apply (hsteps_trans _ (HC [13306; 4643; 2871; 335; 235; 42; 19] 25144 3 2 ((35284, 2) :: (1, 1) :: repeat (1, 2) 103382 ++ (56736, 2) :: (1, 1) :: repeat (1, 2) 595550 ++ (233769, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) 1)).
  {
    replace ((35284, 2) :: (1, 1) :: repeat (1, 2) 103382 ++ (56736, 2) :: (1, 1) :: repeat (1, 2) 595550 ++ (233769, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) with ((35286 - 2, 2) :: (1, 1) :: repeat (1, 2) 103382 ++ (56736, 2) :: (1, 1) :: repeat (1, 2) 595550 ++ (233769, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) by sec_eq.
    apply (sTUP [13306; 4643; 2871; 335; 235; 42; 19] 25144 4 35286 2 ((1, 1) :: repeat (1, 2) 103382 ++ (56736, 2) :: (1, 1) :: repeat (1, 2) 595550 ++ (233769, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) 1); closearith.
  }
  (* step 780: CLEANG_even 17641 *)
  apply (hsteps_trans _ (HB [13306; 4643; 2871; 335; 235; 42; 19] 25144 1 35288 ((2, 2) :: (1, 1) :: repeat (1, 2) 103382 ++ (56736, 2) :: (1, 1) :: repeat (1, 2) 595550 ++ (233769, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) 1)).
  {
    apply (CLEANG_even 17641 [13306; 4643; 2871; 335; 235; 42; 19] 25144 ((1, 1) :: repeat (1, 2) 103382 ++ (56736, 2) :: (1, 1) :: repeat (1, 2) 595550 ++ (233769, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) 1); closearith.
  }
  (* step 781: P TRANS2_1 *)
  apply (sTRANS2_1 [13306; 4643; 2871; 335; 235; 42; 19] 25144 35287 1 (repeat (1, 2) 103382 ++ (56736, 2) :: (1, 1) :: repeat (1, 2) 595550 ++ (233769, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) 1); closearith.
Qed.

(* CASCADE56q: steps 782-782 of the CASCADE56 chain. *)
Lemma CASCADE56q : forall w,
  hsteps (HB [25145; 13306; 4643; 2871; 335; 235; 42; 19] 35289 1 3 (repeat (1, 2) 103382 ++ (56736, 2) :: (1, 1) :: repeat (1, 2) 595550 ++ (233769, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) 1)
         (HB [25145; 13306; 4643; 2871; 335; 235; 42; 19] 138671 1 206767 ((56736, 2) :: (1, 1) :: repeat (1, 2) 595550 ++ (233769, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) 1).
Proof.
  intro w.
  replace 138671 with (35289 + 103382)
    by (apply Nat.eqb_eq; vm_compute; reflexivity).
  replace 206767 with (3 + 2 * 103382)
    by (apply Nat.eqb_eq; vm_compute; reflexivity).
  (* step 782: M pop12 (103382,) *)
  apply (pop12 103382 [25145; 13306; 4643; 2871; 335; 235; 42; 19] 35289 3 ((56736, 2) :: (1, 1) :: repeat (1, 2) 595550 ++ (233769, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) 1); closearith.
Qed.

(* CASCADE56r: steps 783-789 of the CASCADE56 chain. *)
Lemma CASCADE56r : forall w,
  hsteps (HB [25145; 13306; 4643; 2871; 335; 235; 42; 19] 138671 1 206767 ((56736, 2) :: (1, 1) :: repeat (1, 2) 595550 ++ (233769, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) 1)
         (HB [206767; 138671; 25145; 13306; 4643; 2871; 335; 235; 42; 19] 56735 1 3 (repeat (1, 2) 595550 ++ (233769, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) 1).
Proof.
  intro w.
  (* step 783: sTUP *)
  apply (hsteps_trans _ (HC [25145; 13306; 4643; 2871; 335; 235; 42; 19] 138671 206766 2 ((56734, 2) :: (1, 1) :: repeat (1, 2) 595550 ++ (233769, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) 1)).
  {
    rewrite NUM56X31.
    replace ((56734, 2) :: (1, 1) :: repeat (1, 2) 595550 ++ (233769, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) with ((56736 - 2, 2) :: (1, 1) :: repeat (1, 2) 595550 ++ (233769, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) by sec_eq.
    apply (sTUP [25145; 13306; 4643; 2871; 335; 235; 42; 19] 138671 206767 56736 2 ((1, 1) :: repeat (1, 2) 595550 ++ (233769, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) 1); closearith.
  }
  (* step 784: hGRIND_even 103381 *)
  apply (hsteps_trans _ (HB [25145; 13306; 4643; 2871; 335; 235; 42; 19] 138670 1 206766 ((2, 2) :: (56734, 2) :: (1, 1) :: repeat (1, 2) 595550 ++ (233769, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) 1)).
  {
    rewrite NUM56X32.
    apply (hGRIND_even 103381 [25145; 13306; 4643; 2871; 335; 235; 42; 19] 138670 ((56734, 2) :: (1, 1) :: repeat (1, 2) 595550 ++ (233769, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) 1); closearith.
  }
  (* step 785: P TUP2_1 *)
  apply (hsteps_trans _ (HC [138671; 25145; 13306; 4643; 2871; 335; 235; 42; 19] 206766 1 2 ((56732, 2) :: (1, 1) :: repeat (1, 2) 595550 ++ (233769, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) 1)).
  {
    rewrite NUM56X33.
    rewrite NUM56X34.
    replace ((56732, 2) :: (1, 1) :: repeat (1, 2) 595550 ++ (233769, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) with ((56734 - 2, 2) :: (1, 1) :: repeat (1, 2) 595550 ++ (233769, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) by sec_eq.
    apply (sTUP2_1 [25145; 13306; 4643; 2871; 335; 235; 42; 19] 138670 206765 56734 ((1, 1) :: repeat (1, 2) 595550 ++ (233769, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) 1); closearith.
  }
  (* step 786: P TDN *)
  apply (hsteps_trans _ (HB [138671; 25145; 13306; 4643; 2871; 335; 235; 42; 19] 206766 1 4 ((56732, 2) :: (1, 1) :: repeat (1, 2) 595550 ++ (233769, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) 1)).
  {
    apply (sTDN [138671; 25145; 13306; 4643; 2871; 335; 235; 42; 19] 206766 ((56732, 2) :: (1, 1) :: repeat (1, 2) 595550 ++ (233769, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) 1).
  }
  (* step 787: sTUP *)
  apply (hsteps_trans _ (HC [138671; 25145; 13306; 4643; 2871; 335; 235; 42; 19] 206766 3 2 ((56730, 2) :: (1, 1) :: repeat (1, 2) 595550 ++ (233769, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) 1)).
  {
    replace ((56730, 2) :: (1, 1) :: repeat (1, 2) 595550 ++ (233769, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) with ((56732 - 2, 2) :: (1, 1) :: repeat (1, 2) 595550 ++ (233769, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) by sec_eq.
    apply (sTUP [138671; 25145; 13306; 4643; 2871; 335; 235; 42; 19] 206766 4 56732 2 ((1, 1) :: repeat (1, 2) 595550 ++ (233769, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) 1); closearith.
  }
  (* step 788: CLEANG_even 28364 *)
  apply (hsteps_trans _ (HB [138671; 25145; 13306; 4643; 2871; 335; 235; 42; 19] 206766 1 56734 ((2, 2) :: (1, 1) :: repeat (1, 2) 595550 ++ (233769, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) 1)).
  {
    rewrite NUM56X35.
    rewrite NUM56X36.
    apply (CLEANG_even 28364 [138671; 25145; 13306; 4643; 2871; 335; 235; 42; 19] 206766 ((1, 1) :: repeat (1, 2) 595550 ++ (233769, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) 1); closearith.
  }
  (* step 789: P TRANS2_1 *)
  rewrite NUM56X37.
  apply (sTRANS2_1 [138671; 25145; 13306; 4643; 2871; 335; 235; 42; 19] 206766 56733 1 (repeat (1, 2) 595550 ++ (233769, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) 1); closearith.
Qed.

(* CASCADE56s: steps 790-790 of the CASCADE56 chain. *)
Lemma CASCADE56s : forall w,
  hsteps (HB [206767; 138671; 25145; 13306; 4643; 2871; 335; 235; 42; 19] 56735 1 3 (repeat (1, 2) 595550 ++ (233769, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) 1)
         (HB [206767; 138671; 25145; 13306; 4643; 2871; 335; 235; 42; 19] 652285 1 1191103 ((233769, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) 1).
Proof.
  intro w.
  replace 652285 with (56735 + 595550)
    by (apply Nat.eqb_eq; vm_compute; reflexivity).
  replace 1191103 with (3 + 2 * 595550)
    by (apply Nat.eqb_eq; vm_compute; reflexivity).
  (* step 790: M pop12 (595550,) *)
  apply (pop12 595550 [206767; 138671; 25145; 13306; 4643; 2871; 335; 235; 42; 19] 56735 3 ((233769, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) 1); closearith.
Qed.

(* CASCADE56t: steps 791-796 of the CASCADE56 chain. *)
Lemma CASCADE56t : forall w,
  hsteps (HB [206767; 138671; 25145; 13306; 4643; 2871; 335; 235; 42; 19] 652285 1 1191103 ((233769, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) 1)
         (HB [652285; 206767; 138671; 25145; 13306; 4643; 2871; 335; 235; 42; 19] 1191102 1 233768 (repeat (1, 2) 1 ++ (1, 1) :: repeat (1, 2) 2851852 ++ w) 1).
Proof.
  intro w.
  (* step 791: sTUP *)
  apply (hsteps_trans _ (HC [206767; 138671; 25145; 13306; 4643; 2871; 335; 235; 42; 19] 652285 1191102 2 ((233767, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) 1)).
  {
    rewrite NUM56X38.
    rewrite NUM56X39.
    apply (sTUP [206767; 138671; 25145; 13306; 4643; 2871; 335; 235; 42; 19] 652285 1191103 233769 2 ((1, 1) :: repeat (1, 2) 2851852 ++ w) 1); closearith.
  }
  (* step 792: hGRIND_even 595549 *)
  apply (hsteps_trans _ (HB [206767; 138671; 25145; 13306; 4643; 2871; 335; 235; 42; 19] 652284 1 1191102 ((2, 2) :: (233767, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) 1)).
  {
    rewrite NUM56X40.
    apply (hGRIND_even 595549 [206767; 138671; 25145; 13306; 4643; 2871; 335; 235; 42; 19] 652284 ((233767, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) 1); closearith.
  }
  (* step 793: P TUP2_1 *)
  apply (hsteps_trans _ (HC [652285; 206767; 138671; 25145; 13306; 4643; 2871; 335; 235; 42; 19] 1191102 1 2 ((233765, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) 1)).
  {
    rewrite NUM56X41.
    rewrite NUM56X42.
    rewrite NUM56X43.
    apply (sTUP2_1 [206767; 138671; 25145; 13306; 4643; 2871; 335; 235; 42; 19] 652284 1191101 233767 ((1, 1) :: repeat (1, 2) 2851852 ++ w) 1); closearith.
  }
  (* step 794: P TDN *)
  apply (hsteps_trans _ (HB [652285; 206767; 138671; 25145; 13306; 4643; 2871; 335; 235; 42; 19] 1191102 1 4 ((233765, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) 1)).
  {
    apply (sTDN [652285; 206767; 138671; 25145; 13306; 4643; 2871; 335; 235; 42; 19] 1191102 ((233765, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) 1).
  }
  (* step 795: sTUP *)
  apply (hsteps_trans _ (HC [652285; 206767; 138671; 25145; 13306; 4643; 2871; 335; 235; 42; 19] 1191102 3 2 ((233763, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) 1)).
  {
    rewrite NUM56X44.
    apply (sTUP [652285; 206767; 138671; 25145; 13306; 4643; 2871; 335; 235; 42; 19] 1191102 4 233765 2 ((1, 1) :: repeat (1, 2) 2851852 ++ w) 1); closearith.
  }
  (* step 796: CLEANG_odd 116880 *)
  rewrite NUM56X45.
  rewrite NUM56X46.
  replace (repeat (1, 2) 1 ++ (1, 1) :: repeat (1, 2) 2851852 ++ w) with ((1, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) by sec_eq.
  apply (CLEANG_odd 116880 [652285; 206767; 138671; 25145; 13306; 4643; 2871; 335; 235; 42; 19] 1191102 ((1, 1) :: repeat (1, 2) 2851852 ++ w) 1); closearith.
Qed.

(* CASCADE56u: steps 797-797 of the CASCADE56 chain. *)
Lemma CASCADE56u : forall w,
  hsteps (HB [652285; 206767; 138671; 25145; 13306; 4643; 2871; 335; 235; 42; 19] 1191102 1 233768 (repeat (1, 2) 1 ++ (1, 1) :: repeat (1, 2) 2851852 ++ w) 1)
         (HB [652285; 206767; 138671; 25145; 13306; 4643; 2871; 335; 235; 42; 19] 1191103 1 233770 ((1, 1) :: repeat (1, 2) 2851852 ++ w) 1).
Proof.
  intro w.
  replace 1191103 with (1191102 + 1)
    by (apply Nat.eqb_eq; vm_compute; reflexivity).
  replace 233770 with (233768 + 2 * 1)
    by (apply Nat.eqb_eq; vm_compute; reflexivity).
  (* step 797: M pop12 (1,) *)
  apply (pop12 1 [652285; 206767; 138671; 25145; 13306; 4643; 2871; 335; 235; 42; 19] 1191102 233768 ((1, 1) :: repeat (1, 2) 2851852 ++ w) 1); closearith.
Qed.

(* CASCADE56v: steps 798-798 of the CASCADE56 chain. *)
Lemma CASCADE56v : forall w,
  hsteps (HB [652285; 206767; 138671; 25145; 13306; 4643; 2871; 335; 235; 42; 19] 1191103 1 233770 ((1, 1) :: repeat (1, 2) 2851852 ++ w) 1)
         (HB [652285; 206767; 138671; 25145; 13306; 4643; 2871; 335; 235; 42; 19] 1191104 1 233771 (repeat (1, 2) 2851852 ++ w) 1).
Proof.
  intro w.
  (* step 798: P POP *)
  rewrite NUM56X47.
  rewrite NUM56X48.
  apply (sPOP1 [652285; 206767; 138671; 25145; 13306; 4643; 2871; 335; 235; 42; 19] 1191103 233770 (repeat (1, 2) 2851852 ++ w) 1); closearith.
Qed.

(* CASCADE56w: steps 799-799 of the CASCADE56 chain. *)
Lemma CASCADE56w : forall w,
  hsteps (HB [652285; 206767; 138671; 25145; 13306; 4643; 2871; 335; 235; 42; 19] 1191104 1 233771 (repeat (1, 2) 2851852 ++ w) 1)
         (HB [652285; 206767; 138671; 25145; 13306; 4643; 2871; 335; 235; 42; 19] 4042956 1 5937475 (w) 1).
Proof.
  intro w.
  replace 4042956 with (1191104 + 2851852)
    by (apply Nat.eqb_eq; vm_compute; reflexivity).
  replace 5937475 with (233771 + 2 * 2851852)
    by (apply Nat.eqb_eq; vm_compute; reflexivity).
  (* step 799: M pop12 (2851852,) *)
  apply (pop12 2851852 [652285; 206767; 138671; 25145; 13306; 4643; 2871; 335; 235; 42; 19] 1191104 233771 (w) 1); closearith.
Qed.

Lemma CASCADE56 : forall w,
  hsteps (HC [2020419; 297773; 149464; 1260; 147; 20; 0] 0 3 2 (repeat (1, 2) 2851850 ++ w) 1)
         (HB [652285; 206767; 138671; 25145; 13306; 4643; 2871; 335; 235; 42; 19] 4042956 1 5937475 (w) 1).
Proof.
  intro w.
  apply (hsteps_trans _ (HC [50; 14; 5] 1354 2534 2 ((146940, 2) :: (1, 1) :: repeat (1, 2) 297773 ++ (1424871, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) 1)).
  { apply (CASCADE56a w). }
  apply (hsteps_trans _ (HC [35; 20; 0] 123 210 2 ((1040, 2) :: (1, 1) :: repeat (1, 2) 2536 ++ (141868, 2) :: (1, 1) :: repeat (1, 2) 297773 ++ (1424871, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) 1)).
  { apply (CASCADE56b w). }
  apply (hsteps_trans _ (HC [286; 40; 14; 5] 0 3 2 (repeat (1, 2) 475 ++ (2195, 2) :: (1, 1) :: repeat (1, 2) 5076 ++ (131714, 2) :: (1, 1) :: repeat (1, 2) 297773 ++ (1424871, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) 1)).
  { apply (CASCADE56c w). }
  apply (hsteps_trans _ (HB [93; 35; 20; 0] 170 1 32 ((2, 2) :: (1, 1) :: repeat (1, 2) 477 ++ (2195, 2) :: (1, 1) :: repeat (1, 2) 5076 ++ (131714, 2) :: (1, 1) :: repeat (1, 2) 297773 ++ (1424871, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) 1)).
  { apply (CASCADE56d w). }
  apply (hsteps_trans _ (HC [1123; 365; 245; 40; 14; 5] 1918 1 2 ((273, 2) :: (1, 1) :: repeat (1, 2) 5076 ++ (131714, 2) :: (1, 1) :: repeat (1, 2) 297773 ++ (1424871, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) 1)).
  { apply (CASCADE56e w). }
  apply (hsteps_trans _ (HB [5] 53 1 82 ((2, 2) :: (1284, 2) :: (1, 1) :: repeat (1, 2) 2613 ++ (9951, 2) :: (1, 1) :: repeat (1, 2) 20868 ++ (69110, 2) :: (1, 1) :: repeat (1, 2) 297773 ++ (1424871, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) 1)).
  { apply (CASCADE56f w). }
  apply (hsteps_trans _ (HC [] 3 3 2 ((8, 2) :: (4, 2) :: (1, 1) :: repeat (1, 2) 35 ++ (21, 2) :: (1, 1) :: repeat (1, 2) 172 ++ (770, 2) :: (1, 1) :: repeat (1, 2) 2613 ++ (9951, 2) :: (1, 1) :: repeat (1, 2) 20868 ++ (69110, 2) :: (1, 1) :: repeat (1, 2) 297773 ++ (1424871, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) 1)).
  { apply (CASCADE56g w). }
  apply (hsteps_trans _ (HB [2644; 739; 531; 83; 54; 5] 5228 1 4 ((9947, 2) :: (1, 1) :: repeat (1, 2) 20868 ++ (69110, 2) :: (1, 1) :: repeat (1, 2) 297773 ++ (1424871, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) 1)).
  { apply (CASCADE56h w). }
  apply (hsteps_trans _ (HB [51689; 26098; 2644; 739; 531; 83; 54; 5] 69109 1 3 (repeat (1, 2) 297773 ++ (1424871, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) 1)).
  { apply (CASCADE56i w). }
  apply (hsteps_trans _ (HB [51689; 26098; 2644; 739; 531; 83; 54; 5] 366882 1 595549 ((1424871, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) 1)).
  { apply (CASCADE56j w). }
  apply (hsteps_trans _ (HC [20; 0] 34 1 2 ((6, 2) :: (1, 1) :: repeat (1, 2) 83 ++ (3007, 2) :: (1, 1) :: repeat (1, 2) 6030 ++ (8746, 2) :: (1, 1) :: repeat (1, 2) 51689 ++ (263502, 2) :: (1, 1) :: repeat (1, 2) 595550 ++ (233769, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) 1)).
  { apply (CASCADE56k w). }
  apply (hsteps_trans _ (HB [5] 12 1 4 ((36, 2) :: (1, 1) :: repeat (1, 2) 73 ++ (41, 2) :: (1, 1) :: repeat (1, 2) 344 ++ (1975, 2) :: (1, 1) :: repeat (1, 2) 6030 ++ (8746, 2) :: (1, 1) :: repeat (1, 2) 51689 ++ (263502, 2) :: (1, 1) :: repeat (1, 2) 595550 ++ (233769, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) 1)).
  { apply (CASCADE56l w). }
  apply (hsteps_trans _ (HC [1059; 199; 101; 0] 7498 12570 2 ((8744, 2) :: (1, 1) :: repeat (1, 2) 51689 ++ (263502, 2) :: (1, 1) :: repeat (1, 2) 595550 ++ (233769, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) 1)).
  { apply (CASCADE56m w). }
  apply (hsteps_trans _ (HC [0] 20 34 2 ((1112, 2) :: (1, 1) :: repeat (1, 2) 2320 ++ (736, 2) :: (1, 1) :: repeat (1, 2) 12571 ++ (35290, 2) :: (1, 1) :: repeat (1, 2) 103382 ++ (56736, 2) :: (1, 1) :: repeat (1, 2) 595550 ++ (233769, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) 1)).
  { apply (CASCADE56n w). }
  apply (hsteps_trans _ (HB [0] 17 1 4 ((106, 2) :: (1, 1) :: repeat (1, 2) 166 ++ (552, 2) :: (1, 1) :: repeat (1, 2) 2320 ++ (736, 2) :: (1, 1) :: repeat (1, 2) 12571 ++ (35290, 2) :: (1, 1) :: repeat (1, 2) 103382 ++ (56736, 2) :: (1, 1) :: repeat (1, 2) 595550 ++ (233769, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) 1)).
  { apply (CASCADE56o w). }
  apply (hsteps_trans _ (HB [25145; 13306; 4643; 2871; 335; 235; 42; 19] 35289 1 3 (repeat (1, 2) 103382 ++ (56736, 2) :: (1, 1) :: repeat (1, 2) 595550 ++ (233769, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) 1)).
  { apply (CASCADE56p w). }
  apply (hsteps_trans _ (HB [25145; 13306; 4643; 2871; 335; 235; 42; 19] 138671 1 206767 ((56736, 2) :: (1, 1) :: repeat (1, 2) 595550 ++ (233769, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) 1)).
  { apply (CASCADE56q w). }
  apply (hsteps_trans _ (HB [206767; 138671; 25145; 13306; 4643; 2871; 335; 235; 42; 19] 56735 1 3 (repeat (1, 2) 595550 ++ (233769, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) 1)).
  { apply (CASCADE56r w). }
  apply (hsteps_trans _ (HB [206767; 138671; 25145; 13306; 4643; 2871; 335; 235; 42; 19] 652285 1 1191103 ((233769, 2) :: (1, 1) :: repeat (1, 2) 2851852 ++ w) 1)).
  { apply (CASCADE56s w). }
  apply (hsteps_trans _ (HB [652285; 206767; 138671; 25145; 13306; 4643; 2871; 335; 235; 42; 19] 1191102 1 233768 (repeat (1, 2) 1 ++ (1, 1) :: repeat (1, 2) 2851852 ++ w) 1)).
  { apply (CASCADE56t w). }
  apply (hsteps_trans _ (HB [652285; 206767; 138671; 25145; 13306; 4643; 2871; 335; 235; 42; 19] 1191103 1 233770 ((1, 1) :: repeat (1, 2) 2851852 ++ w) 1)).
  { apply (CASCADE56u w). }
  apply (hsteps_trans _ (HB [652285; 206767; 138671; 25145; 13306; 4643; 2871; 335; 235; 42; 19] 1191104 1 233771 (repeat (1, 2) 2851852 ++ w) 1)).
  { apply (CASCADE56v w). }
  apply (CASCADE56w w).
Qed.

(* ----------------------------------------------------------------- *)
(* TOP56_TO_TOP10: the TOP9 state at (2j, 2) reaches TOP10 at the    *)
(* pair (2 * (j - 2851853), 2).  The front is the Phase 55 front      *)
(* verbatim at the new constants: the first TUP rewrites via         *)
(* NUM55h (2851850 = 2851851 - 1, inherited from Grind23.v), the     *)
(* hGRIND_even 1425923 step rewrites the goal by the standalone      *)
(* identities NUM55a / NUM55b (2851850 = 2 * 1425923 + 4,            *)
(* 2020419 = S 2020418), and the TUP2_1 step rewrites via NUM55i     *)
(* (2851850 = S 2851849) / NUM55b.                                   *)
(* ----------------------------------------------------------------- *)

Lemma TOP56_TO_TOP10 : forall j beta, 2851854 <= j -> 2 <= beta ->
  hsteps (HB [297773; 149464; 1260; 147; 20; 0] 2020419 1 2851851
            ((2 * j, 2) :: (1, 1) :: repeat (1, 2) (beta - 1)) 1)
         (HB [652285; 206767; 138671; 25145; 13306; 4643; 2871; 335; 235; 42; 19] 4042956 1 5937475
            ((2 * (j - 2851853), 2) :: (1, 1)
             :: repeat (1, 2) (beta - 1)) 1).
Proof.
  intros j beta Hj Hb.
  assert (Hj4 : 4 <= j).
  { apply Nat.le_trans with 2851854; [closearith | exact Hj]. }
  assert (Hr : 1 <= j - 2851853).
  { assert (E : 2851853 = 2851854 - 1)
      by (apply Nat.eqb_eq; vm_compute; reflexivity).
    rewrite E. lia. }
  assert (Heq : 2 * j - 6 = 2 * 2851850 + 2 * (j - 2851853)).
  { assert (E1 : 2851853 = 2851850 + 3)
      by (apply Nat.eqb_eq; vm_compute; reflexivity).
    assert (E2 : 2851854 = 2851850 + 4)
      by (apply Nat.eqb_eq; vm_compute; reflexivity).
    rewrite E1. rewrite E2 in Hj. lia. }
  apply (hsteps_trans _ (HC [297773; 149464; 1260; 147; 20; 0] 2020419
    2851850 2 ((2 * j - 2, 2) :: (1, 1) :: repeat (1, 2) (beta - 1)) 1)).
  { rewrite NUM55h.
    apply (sTUP [297773; 149464; 1260; 147; 20; 0] 2020419 2851851 (2 * j) 2
           ((1, 1) :: repeat (1, 2) (beta - 1)) 1); closearith. }
  apply (hsteps_trans _ (HB [297773; 149464; 1260; 147; 20; 0] 2020418
    1 2851850 ((2, 2) :: (2 * j - 2, 2) :: (1, 1)
            :: repeat (1, 2) (beta - 1)) 1)).
  { rewrite NUM55a. rewrite NUM55b.
    apply (hGRIND_even 1425923 [297773; 149464; 1260; 147; 20; 0]
           2020418 ((2 * j - 2, 2) :: (1, 1) :: repeat (1, 2) (beta - 1))
           1); closearith. }
  apply (hsteps_trans _ (HC [2020419; 297773; 149464; 1260; 147; 20; 0] 2851850 1 2 ((2 * j - 4, 2) :: (1, 1)
            :: repeat (1, 2) (beta - 1)) 1)).
  { rewrite NUM55i. rewrite NUM55b.
    replace ((2 * j - 4, 2) :: (1, 1) :: repeat (1, 2) (beta - 1))
      with ((2 * j - 2 - 2, 2) :: (1, 1) :: repeat (1, 2) (beta - 1))
      by sec_eq.
    apply (sTUP2_1 [297773; 149464; 1260; 147; 20; 0] 2020418
           2851849 (2 * j - 2) ((1, 1) :: repeat (1, 2) (beta - 1)) 1); lia. }
  apply (hsteps_trans _ (HB [2020419; 297773; 149464; 1260; 147; 20; 0] 2851850 1 4 ((2 * j - 4, 2) :: (1, 1)
            :: repeat (1, 2) (beta - 1)) 1)).
  { apply (sTDN [2020419; 297773; 149464; 1260; 147; 20; 0] 2851850
           ((2 * j - 4, 2) :: (1, 1) :: repeat (1, 2) (beta - 1))
           1). }
  apply (hsteps_trans _ (HC [2020419; 297773; 149464; 1260; 147; 20; 0] 2851850 3 2 ((2 * j - 6, 2) :: (1, 1)
            :: repeat (1, 2) (beta - 1)) 1)).
  { replace ((2 * j - 6, 2) :: (1, 1) :: repeat (1, 2) (beta - 1))
      with ((2 * j - 4 - 2, 2) :: (1, 1) :: repeat (1, 2) (beta - 1))
      by sec_eq.
    apply (sTUP [2020419; 297773; 149464; 1260; 147; 20; 0] 2851850 4
           (2 * j - 4) 2 ((1, 1) :: repeat (1, 2) (beta - 1)) 1);
      lia. }
  apply (hsteps_trans _ (HC [2020419; 297773; 149464; 1260; 147; 20; 0]
    0 3 2 (repeat (1, 2) 2851850
     ++ ((2 * (j - 2851853), 2) :: (1, 1)
         :: repeat (1, 2) (beta - 1))) 1)).
  { rewrite Heq.
    apply (DIPGRIND 2851850 (2 * (j - 2851853))
           [2020419; 297773; 149464; 1260; 147; 20; 0]
           ((1, 1) :: repeat (1, 2) (beta - 1)) 1);
      [closearith | lia]. }
  apply (CASCADE56 ((2 * (j - 2851853), 2) :: (1, 1)
                    :: repeat (1, 2) (beta - 1))).
Qed.

(* ----------------------------------------------------------------- *)
(* The TOP10 closings: r10' = 2, 4, 6 and band 10                    *)
(* (8 <= r10' <= 11874954).                                          *)
(* ----------------------------------------------------------------- *)

Lemma TOP56_2 : forall beta, 2 <= beta ->
  hsteps (HB [652285; 206767; 138671; 25145; 13306; 4643; 2871; 335; 235; 42; 19] 4042956 1 5937475
            ((2, 2) :: (1, 1) :: repeat (1, 2) (beta - 1)) 1)
         (HB [4042957; 652285; 206767; 138671; 25145; 13306; 4643; 2871; 335; 235; 42; 19]
            (5937476 + (beta - 1)) 1 (2 * beta + 1) [] 1).
Proof.
  intros beta Hb.
  apply (hsteps_trans _ (HB [4042957; 652285; 206767; 138671; 25145; 13306; 4643; 2871; 335; 235; 42; 19] 5937476 1 3 (repeat (1, 2) (beta - 1)) 1)).
  { rewrite NUM56e. rewrite NUM56f. rewrite NUM56g.
    apply (sTRANS2_1 [652285; 206767; 138671; 25145; 13306; 4643; 2871; 335; 235; 42; 19] 4042956
           5937474 1 (repeat (1, 2) (beta - 1)) 1); lia. }
  apply (CASCADE_POPFIN [4042957; 652285; 206767; 138671; 25145; 13306; 4643; 2871; 335; 235; 42; 19] 5937476 beta); lia.
Qed.

Lemma TOP56_4 : forall beta, 2 <= beta ->
  hsteps (HB [652285; 206767; 138671; 25145; 13306; 4643; 2871; 335; 235; 42; 19] 4042956 1 5937475
            ((4, 2) :: (1, 1) :: repeat (1, 2) (beta - 1)) 1)
         (HB [5937475; 4042956; 652285; 206767; 138671; 25145; 13306; 4643; 2871; 335; 235; 42; 19]
            (beta + 2) 1 (2 * beta + 1) [] 1).
Proof.
  intros beta Hb.
  apply (hsteps_trans _ (HC [652285; 206767; 138671; 25145; 13306; 4643; 2871; 335; 235; 42; 19]
    4042956 5937474 2
    ((2, 2) :: (1, 1) :: repeat (1, 2) (beta - 1)) 1)).
  { rewrite NUM56h.
    apply (sTUP [652285; 206767; 138671; 25145; 13306; 4643; 2871; 335; 235; 42; 19] 4042956 5937475
           4 2 ((1, 1) :: repeat (1, 2) (beta - 1)) 1); closearith. }
  apply (hsteps_trans _ (HB [652285; 206767; 138671; 25145; 13306; 4643; 2871; 335; 235; 42; 19]
    4042955 1 5937474 ((2, 2) :: (2, 2) :: (1, 1)
            :: repeat (1, 2) (beta - 1)) 1)).
  { rewrite NUM56a. rewrite NUM56b.
    apply (hGRIND_even 2968735 [652285; 206767; 138671; 25145; 13306; 4643; 2871; 335; 235; 42; 19]
           4042955 ((2, 2) :: (1, 1) :: repeat (1, 2) (beta - 1)) 1);
      closearith. }
  apply (hsteps_trans _ (HB [5937475; 4042956; 652285; 206767; 138671; 25145; 13306; 4643; 2871; 335; 235; 42; 19] 3 1 3 (repeat (1, 2) (beta - 1)) 1)).
  { rewrite NUM56i. rewrite NUM56j. rewrite NUM56b.
    apply (hsteps_step _ (HB [S (S 5937473); S 4042955; 652285; 206767; 138671; 25145; 13306; 4643; 2871; 335; 235; 42; 19] 3 1 3 (repeat (1, 2) (beta - 1)) 1));
      [apply hTRANS2_2; closearith | apply hsteps_refl]. }
  replace (beta + 2) with (3 + (beta - 1)) by lia.
  apply (CASCADE_POPFIN [5937475; 4042956; 652285; 206767; 138671; 25145; 13306; 4643; 2871; 335; 235; 42; 19] 3 beta); lia.
Qed.

Lemma TOP56_6 : forall beta, 2 <= beta ->
  hsteps (HB [652285; 206767; 138671; 25145; 13306; 4643; 2871; 335; 235; 42; 19] 4042956 1 5937475
            ((6, 2) :: (1, 1) :: repeat (1, 2) (beta - 1)) 1)
         (HB [5937475; 4042956; 652285; 206767; 138671; 25145; 13306; 4643; 2871; 335; 235; 42; 19]
            (beta + 4) 1 (2 * beta + 1) [] 1).
Proof.
  intros beta Hb.
  apply (hsteps_trans _ (HC [652285; 206767; 138671; 25145; 13306; 4643; 2871; 335; 235; 42; 19]
    4042956 5937474 2
    ((4, 2) :: (1, 1) :: repeat (1, 2) (beta - 1)) 1)).
  { rewrite NUM56h.
    apply (sTUP [652285; 206767; 138671; 25145; 13306; 4643; 2871; 335; 235; 42; 19] 4042956 5937475
           6 2 ((1, 1) :: repeat (1, 2) (beta - 1)) 1); closearith. }
  apply (hsteps_trans _ (HB [652285; 206767; 138671; 25145; 13306; 4643; 2871; 335; 235; 42; 19]
    4042955 1 5937474 ((2, 2) :: (4, 2) :: (1, 1)
            :: repeat (1, 2) (beta - 1)) 1)).
  { rewrite NUM56a. rewrite NUM56b.
    apply (hGRIND_even 2968735 [652285; 206767; 138671; 25145; 13306; 4643; 2871; 335; 235; 42; 19]
           4042955 ((4, 2) :: (1, 1) :: repeat (1, 2) (beta - 1)) 1);
      closearith. }
  apply (hsteps_trans _ (HC [4042956; 652285; 206767; 138671; 25145; 13306; 4643; 2871; 335; 235; 42; 19] 5937474 1 2
    ((2, 2) :: (1, 1) :: repeat (1, 2) (beta - 1)) 1)).
  { rewrite NUM56i. rewrite NUM56b.
    replace ((2, 2) :: (1, 1) :: repeat (1, 2) (beta - 1))
      with ((4 - 2, 2) :: (1, 1) :: repeat (1, 2) (beta - 1))
      by sec_eq.
    apply (sTUP2_1 [652285; 206767; 138671; 25145; 13306; 4643; 2871; 335; 235; 42; 19] 4042955
           5937473 4 ((1, 1) :: repeat (1, 2) (beta - 1)) 1); lia. }
  apply (hsteps_trans _ (HB [4042956; 652285; 206767; 138671; 25145; 13306; 4643; 2871; 335; 235; 42; 19] 5937474 1 4
    ((2, 2) :: (1, 1) :: repeat (1, 2) (beta - 1)) 1)).
  { apply (sTDN [4042956; 652285; 206767; 138671; 25145; 13306; 4643; 2871; 335; 235; 42; 19] 5937474
           ((2, 2) :: (1, 1) :: repeat (1, 2) (beta - 1))
           1). }
  apply (hsteps_trans _ (HB [5937475; 4042956; 652285; 206767; 138671; 25145; 13306; 4643; 2871; 335; 235; 42; 19] 5 1 3 (repeat (1, 2) (beta - 1)) 1)).
  { rewrite NUM56e.
    apply (sTRANS2_1 [4042956; 652285; 206767; 138671; 25145; 13306; 4643; 2871; 335; 235; 42; 19]
           5937474 3 1 (repeat (1, 2) (beta - 1)) 1); lia. }
  replace (beta + 4) with (5 + (beta - 1)) by lia.
  apply (CASCADE_POPFIN [5937475; 4042956; 652285; 206767; 138671; 25145; 13306; 4643; 2871; 335; 235; 42; 19] 5 beta); lia.
Qed.

Lemma TOP56_BAND : forall j beta, 4 <= j -> j <= 5937477 -> 2 <= beta ->
  hsteps (HB [652285; 206767; 138671; 25145; 13306; 4643; 2871; 335; 235; 42; 19] 4042956 1 5937475
            ((2 * j, 2) :: (1, 1) :: repeat (1, 2) (beta - 1)) 1)
         (HB [5937475; 4042956; 652285; 206767; 138671; 25145; 13306; 4643; 2871; 335; 235; 42; 19]
            (2 * j + beta - 2) 1 (2 * beta + 1) [] 1).
Proof.
  intros j beta Hj1 Hj2 Hb.
  apply (hsteps_trans _ (HC [652285; 206767; 138671; 25145; 13306; 4643; 2871; 335; 235; 42; 19]
    4042956 5937474 2 ((2 * j - 2, 2) :: (1, 1)
            :: repeat (1, 2) (beta - 1)) 1)).
  { rewrite NUM56h.
    apply (sTUP [652285; 206767; 138671; 25145; 13306; 4643; 2871; 335; 235; 42; 19] 4042956 5937475
           (2 * j) 2 ((1, 1) :: repeat (1, 2) (beta - 1)) 1);
      closearith. }
  apply (hsteps_trans _ (HB [652285; 206767; 138671; 25145; 13306; 4643; 2871; 335; 235; 42; 19]
    4042955 1 5937474 ((2, 2) :: (2 * j - 2, 2) :: (1, 1)
            :: repeat (1, 2) (beta - 1)) 1)).
  { rewrite NUM56a. rewrite NUM56b.
    apply (hGRIND_even 2968735 [652285; 206767; 138671; 25145; 13306; 4643; 2871; 335; 235; 42; 19]
           4042955 ((2 * j - 2, 2) :: (1, 1)
           :: repeat (1, 2) (beta - 1)) 1); closearith. }
  apply (hsteps_trans _ (HC [4042956; 652285; 206767; 138671; 25145; 13306; 4643; 2871; 335; 235; 42; 19] 5937474 1 2 ((2 * j - 4, 2) :: (1, 1)
            :: repeat (1, 2) (beta - 1)) 1)).
  { rewrite NUM56i. rewrite NUM56b.
    replace ((2 * j - 4, 2) :: (1, 1) :: repeat (1, 2) (beta - 1))
      with ((2 * j - 2 - 2, 2) :: (1, 1)
            :: repeat (1, 2) (beta - 1)) by sec_eq.
    apply (sTUP2_1 [652285; 206767; 138671; 25145; 13306; 4643; 2871; 335; 235; 42; 19] 4042955
           5937473 (2 * j - 2) ((1, 1) :: repeat (1, 2) (beta - 1))
           1); lia. }
  apply (hsteps_trans _ (HB [4042956; 652285; 206767; 138671; 25145; 13306; 4643; 2871; 335; 235; 42; 19] 5937474 1 4 ((2 * j - 4, 2) :: (1, 1)
            :: repeat (1, 2) (beta - 1)) 1)).
  { apply (sTDN [4042956; 652285; 206767; 138671; 25145; 13306; 4643; 2871; 335; 235; 42; 19] 5937474
           ((2 * j - 4, 2) :: (1, 1) :: repeat (1, 2) (beta - 1))
           1). }
  apply (hsteps_trans _ (HC [4042956; 652285; 206767; 138671; 25145; 13306; 4643; 2871; 335; 235; 42; 19] 5937474 3 2 ((2 * j - 6, 2) :: (1, 1)
            :: repeat (1, 2) (beta - 1)) 1)).
  { replace ((2 * j - 6, 2) :: (1, 1) :: repeat (1, 2) (beta - 1))
      with ((2 * j - 4 - 2, 2) :: (1, 1)
            :: repeat (1, 2) (beta - 1)) by sec_eq.
    apply (sTUP [4042956; 652285; 206767; 138671; 25145; 13306; 4643; 2871; 335; 235; 42; 19] 5937474
           4 (2 * j - 4) 2 ((1, 1) :: repeat (1, 2) (beta - 1)) 1);
      lia. }
  apply (hsteps_trans _ (HB [4042956; 652285; 206767; 138671; 25145; 13306; 4643; 2871; 335; 235; 42; 19] 5937474 1 (2 * j - 2)
    ((2, 2) :: (1, 1) :: repeat (1, 2) (beta - 1)) 1)).
  { replace (2 * j - 6) with (2 * (j - 4) + 2) by lia.
    replace (2 * j - 2) with (2 * (j - 4) + 6) by lia.
    apply (CLEANG_even (j - 4) [4042956; 652285; 206767; 138671; 25145; 13306; 4643; 2871; 335; 235; 42; 19] 5937474 ((1, 1) :: repeat (1, 2) (beta - 1))
           1).
    (* the floor (j - 4) + 1 <= 5937474: route via j <= 5937477 *)
    apply Nat.le_trans with (j - 3).
    - lia.
    - rewrite NUM56k.
      apply Nat.sub_le_mono_r. exact Hj2. }
  apply (hsteps_trans _ (HB [5937475; 4042956; 652285; 206767; 138671; 25145; 13306; 4643; 2871; 335; 235; 42; 19] (2 * j - 1) 1 3 (repeat (1, 2) (beta - 1)) 1)).
  { replace (2 * j - 2) with (S (2 * j - 3)) by lia.
    replace (2 * j - 1) with (S (S (2 * j - 3))) by lia.
    rewrite NUM56e.
    apply (sTRANS2_1 [4042956; 652285; 206767; 138671; 25145; 13306; 4643; 2871; 335; 235; 42; 19]
           5937474 (2 * j - 3) 1 (repeat (1, 2) (beta - 1)) 1); lia. }
  replace (2 * j + beta - 2) with (2 * j - 1 + (beta - 1)) by lia.
  apply (CASCADE_POPFIN [5937475; 4042956; 652285; 206767; 138671; 25145; 13306; 4643; 2871; 335; 235; 42; 19] (2 * j - 1) beta); lia.
Qed.

(* ----------------------------------------------------------------- *)
(* TAIL2_END11: the strictly smaller residual core -- the totality  *)
(* of the TOP10 state for r10' = 2 * j, j >= 5937478                 *)
(* (r10' >= 11874956), where the GRIND11 pair (r10' - 6, 2) at       *)
(* counter 5937474 takes the DIPDESC boundary an eleventh time.      *)
(* A Definition (lemma parameter), never an axiom.                   *)
(* ----------------------------------------------------------------- *)

Definition TAIL2_END11 : Prop :=
  forall j beta, 5937478 <= j -> 2 <= beta ->
  exists pb A, beta <= A /\
    hsteps (HB [652285; 206767; 138671; 25145; 13306; 4643; 2871; 335; 235; 42; 19] 4042956 1 5937475
              ((2 * j, 2) :: (1, 1) :: repeat (1, 2) (beta - 1)) 1)
           (HB pb A 1 (2 * beta + 1) [] 1).

(* ----------------------------------------------------------------- *)
(* TAIL2_END10_of56: TAIL2_END10, modulo TAIL2_END11.  The j-range  *)
(* splits at r10' = 2 * (j - 2851853): the three small cases and     *)
(* band 10 are proved above; j - 2851853 >= 5937478 is the core.     *)
(* (Numeral hygiene: all S-conversions at these depths are          *)
(* eqb/vm-proved equality rewrites, per the Phase 53-55 pattern.)    *)
(* ----------------------------------------------------------------- *)

Lemma TAIL2_END10_of56 : TAIL2_END11 -> TAIL2_END10.
Proof.
  intros H11 j beta Hj Hb.
  pose proof (TOP56_TO_TOP10 j beta Hj Hb) as Htop.
  destruct (le_lt_dec 5937478 (j - 2851853)) as [Hbig | Hsmall].
  - (* j10 = j - 2851853 >= 5937478: the core *)
    destruct (H11 (j - 2851853) beta Hbig Hb)
      as [pb [A [Ha Hsteps]]].
    exists pb, A. split; [exact Ha |].
    exact (hsteps_trans _ _ _ Htop Hsteps).
  - destruct (le_lt_dec 4 (j - 2851853)) as [Hband | Htiny].
    + (* band 10: j10 = j - 2851853, 4 <= j10 <= 5937477 *)
      exists [5937475; 4042956; 652285; 206767; 138671; 25145; 13306; 4643; 2871; 335; 235; 42; 19],
        (2 * (j - 2851853) + beta - 2).
      split; [lia |].
      assert (Hj2 : j - 2851853 <= 5937477).
      { rewrite NUM56m in Hsmall.
        apply (proj1 (Nat.lt_succ_r _ _) Hsmall). }
      exact (hsteps_trans _ _ _ Htop
               (TOP56_BAND (j - 2851853) beta Hband Hj2 Hb)).
    + (* tiny: j10 = j - 2851853 <= 3; j10 >= 1 since 2851854 <= j *)
      destruct (Nat.eq_dec (j - 2851853) 1) as [He | Hne].
      * (* r10' = 2 *)
        rewrite He in Htop.
        exists [4042957; 652285; 206767; 138671; 25145; 13306; 4643; 2871; 335; 235; 42; 19],
          (5937476 + (beta - 1)).
        split; [rewrite NUM56n; lia |].
        exact (hsteps_trans _ _ _ Htop (TOP56_2 beta Hb)).
      * destruct (Nat.eq_dec (j - 2851853) 2) as [He | Hne'].
        -- (* r10' = 4 *)
           rewrite He in Htop.
           exists [5937475; 4042956; 652285; 206767; 138671; 25145; 13306; 4643; 2871; 335; 235; 42; 19], (beta + 2).
           split; [lia |].
           exact (hsteps_trans _ _ _ Htop (TOP56_4 beta Hb)).
        -- destruct (Nat.eq_dec (j - 2851853) 3) as [He | Hne''].
           ++ (* r10' = 6 *)
              rewrite He in Htop.
              exists [5937475; 4042956; 652285; 206767; 138671; 25145; 13306; 4643; 2871; 335; 235; 42; 19], (beta + 4).
              split; [lia |].
              exact (hsteps_trans _ _ _ Htop (TOP56_6 beta Hb)).
           ++ (* j10 = 0, contradicting 2851854 <= j *)
              exfalso.
              assert (H0 : j - 2851853 = 0) by lia.
              rewrite NUM55m in Hj.
              lia.
Qed.

(* ----------------------------------------------------------------- *)
(* ESC_ERA_LAW_56: the phase-8 ESC era law at every even            *)
(* R >= 1278 (M >= 616), modulo TAIL2_END11 alone.                  *)
(* ----------------------------------------------------------------- *)

Lemma ESC_ERA_LAW_56 : TAIL2_END11 ->
  forall M beta, 616 <= M -> 2 <= beta ->
  exists n c pb a,
    run n (esc_src (2 * M + 52) (beta - 2)) = Some c
    /\ cfg_sim c (rcsec (false :: repeat true (S a) ++ enc pb)
                        (2 * beta + 2) [(1, 2)])
    /\ beta <= a.
Proof.
  intros H M beta HM Hb.
  apply (ESC_ERA_LAW_55 (TAIL2_END10_of56 H) M beta HM Hb).
Qed.

(* ----------------------------------------------------------------- *)
(* Assumption audit                                                  *)
(* ----------------------------------------------------------------- *)

Print Assumptions CASCADE56.
Print Assumptions TOP56_TO_TOP10.
Print Assumptions TOP56_2.
Print Assumptions TOP56_4.
Print Assumptions TOP56_6.
Print Assumptions TOP56_BAND.
Print Assumptions TAIL2_END10_of56.
Print Assumptions ESC_ERA_LAW_56.
