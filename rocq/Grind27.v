(* ================================================================= *)
(* Phase 59: the thirteenth descent of the TOP12 state, the        *)
(* TOP13 state and the residual core TAIL2_END14.                  *)
(*                                                                 *)
(* The phase-58 status doc left exactly one ESC-side core:         *)
(* TAIL2_END13, the totality of                                *)
(*   TOP12 = HB [1523948; 426279; 308525; 58213; 30332; 931;        *)
(*           608; 77; 35; 20; 0] 14897638 1 29403093 W              *)
(* at r12' = 2 * j12, j12 >= 29403096 (TOP12 parameters).  This     *)
(* phase discharges it on a finite range and reduces it to the     *)
(* same statement one level down.  Method: the lemma-step          *)
(* classifier of phase55-work/classify.py, validated by exact      *)
(* reproduction of the phase-58 chain (498 steps, 0 mismatches)    *)
(* before any phase-59 use, then run at TOP12(29403096, beta)      *)
(* (rocq/hsim59.py, phase59-work/chain59f.py).                     *)
(*                                                                 *)
(* Characterisation (chains at (29403096, 2) and (29403096, 3)):   *)
(*   1. TOP12's front is UNIFORM in (j, beta): TUP +                *)
(*      hGRIND_even 14701544 + TUP2_1 + TDN + TUP lands on          *)
(*      GRIND13 = HC [14897638; 1523948; ...] 29403092 3 2          *)
(*      ((2j - 6, 2) :: tail(beta)); the DIPGRIND boundary round    *)
(*      (29403092, 2(j - 29403095)) lands on the DIP13 spine        *)
(*      repeat (1, 2) 29403092 ++ ((2(j - 29403095), 2) :: tail).   *)
(*   2. From the spine the walk follows a FIXED parse, independent *)
(*      of (j, beta) (the label sequence and the abstracted        *)
(*      targets at beta = 2 and beta = 3 agree at every one of      *)
(*      the 586 steps): CASCADE59, 586 lemma steps (the            *)
(*      CASCADE58 pattern, one level deeper and longer):          *)
(*      131 TUP, 84 TDN, 72 pop12, 56 DIPGRIND, 46 TUP2_1,          *)
(*      39 hGRIND_even, 33 PUSH, 30 PX2A, 20 POP, 19 TRANS2_1,      *)
(*      15 CLEANG_even, 11 PUSHX, 8 CLEANG_odd, 6 PX2B0,            *)
(*      6 PX2Bgen, 5 hGRIND, 4 PX2A0, 1 TRANS2_2.  The frame is     *)
(*      REPLACED, not grown: eleven blocks become nine:            *)
(*      -> TOP13 = HB [7965811; 4012920; 308090; 49409; 7710;       *)
(*         1059; 199; 101; 0] 34304475 1 58806191 W.                *)
(*      (CASCADE59 is stated for an ARBITRARY tail w in            *)
(*      Grind27.v / Grind27b.v; hsim59.py Part 1b probes that      *)
(*      generality with a junk tail.)                              *)
(*   3. TOP13 closings by r13' = 2 * j13, j13 = j - 29403095:      *)
(*      r13' = 2:       TRANS2_1 + POPFIN, A = 58806191 + beta,     *)
(*                     frame [34304476; 7965811; ...].              *)
(*      r13' = 4:       TUP + hGRIND_even 29403093 + TRANS2_2       *)
(*                     + POPFIN, A = beta + 2,                      *)
(*                     frame [58806191; 34304475; 7965811; ...].    *)
(*      r13' = 6:       TUP + hGRIND_even 29403093 + TUP2_1         *)
(*                     + TDN + TRANS2_1 + POPFIN, A = beta + 4,     *)
(*                     frame as r13' = 4.                           *)
(*      8 <= r13' <= 117612386 (band 13): TUP + hGRIND_even         *)
(*                     29403093 + TUP2_1 + TDN + TUP -> GRIND14     *)
(*                     = HC [34304475; 7965811; ...] 58806190       *)
(*                     3 2 ((r13'-6, 2) :: tail(beta))  -- TUP2_1   *)
(*                     moves the shuttle 58806191 into the          *)
(*                     counter slot, so the band counter is         *)
(*                     58806190; CLEANG_even ((r13'-8)/2) (floor    *)
(*                     (r13'-8)/2 + 1 <= 58806190, exactly          *)
(*                     r13' <= 117612386); TRANS2_1 + POPFIN,       *)
(*                     A = r13' + beta - 2, frame as r13' = 4.      *)
(*      r13' >= 117612388: GRIND14's pair (r13'-6, 2) exceeds       *)
(*      the CLEANG_even floor; DIPGRIND (58806190,                  *)
(*      r13' - 117612386) landing occurs (asserted by hsim59.py     *)
(*      Part 3).  This is the residual core TAIL2_END14 (at         *)
(*      TOP13, r13' = 2*j13, j13 >= 58806194).                      *)
(*                                                                 *)
(* Band boundary: r13' <= 117612386  <=>  j <= 88209288 (TOP12      *)
(*                params)  <=>  j13 <= 58806193 (TOP13 params).     *)
(*                                                                 *)
(* File layout (compile-resident-set management at Phase 59        *)
(* numeral depths; host ceiling ~6 GB): the tiny Arith-only        *)
(* companions Grind27a.v (S59f/S59g0/S59a1), Grind27h.v            *)
(* (S59g1/S59g2/S59h0 + NUM59b/e), Grind27i.v + Grind27o.v (the    *)
(* S59r singleton identities), Grind27j.v (NUM59a alone) and       *)
(* Grind27k/l/m/n.v (NUM59f/g, h/i, j/k, m/n -- at most two        *)
(* 58.8M-scale identities per file: each eqb/vm evaluation peaks   *)
(* ~3.4 GB and several in one process accumulate past the          *)
(* ceiling; NUM59a's add evaluation peaks ~5.5 GB directly and     *)
(* is proved by the split + symbolic ring reshape in Grind27j.v)   *)
(* are proved by eqb/leb + vm_compute in fresh processes;          *)
(* Grind27.v carries the REP59 identities, the NUM59X identities   *)
(* and CASCADE59a-j; Grind27b.v carries                            *)
(* CASCADE59k-u and CASCADE59; Grind27c.v carries                  *)
(* TOP59_TO_TOP13; Grind27d/e/f.v carry TOP59_2/4/6; Grind27g.v    *)
(* carries TOP59_BAND, TAIL2_END14, TAIL2_END13_of59 and           *)
(* ESC_ERA_LAW_59.  Every lemma statement is the one the phase's   *)
(* single-file draft would carry; no statement depends on the      *)
(* split.                                                          *)
(* ================================================================= *)

Require Import List Bool Arith Lia ZArith.
Import ListNotations.
Require Import TM Sections Mirror TokenPass Recoord Era Esc Dev
               Grind Grind2 Grind3 Grind4 Grind5 Grind6 Grind7 Grind8
               Grind9 Grind10 Grind11 Grind12 Grind13 Grind14 Grind15
               Grind16 Grind17 Grind18 Grind19 Grind20 Grind21 Grind22
               Grind23 Grind24 Grind25 Grind26 Grind26a Grind26b
               Grind26c Grind26d Grind26e Grind26f Grind26g Grind27a.

(* Section equality: componentwise, arithmetic leaves by lia.      *)
Ltac sec_eq :=
  repeat (first [ solve [reflexivity] | solve [lia] | f_equal ]).

(* Closed-numeral arithmetic: literals >= 7426 are parsed as       *)
(* Nat.of_num_uint atoms, which lia cannot relate to variables;    *)
(* for purely closed <= goals the boolean check decides them.      *)
Ltac closearith :=
  first [ lia | apply Nat.leb_le; reflexivity ].

(* Factored list identities for the PX2A steps of           *)
(* CASCADE59 whose produced (1, 2)s merge into a spine      *)
(* repeat of length > 175000 (auto-detected by gen59.py):   *)
(* the goal's stated target is first rewritten to the       *)
(* constructor's unmerged form via REP59a-c (whose proofs   *)
(* proofs rewrite the run length to S-form and close by     *)
(* reflexivity), and the frame atoms are put in S-form via  *)
(* the NUM59t<step>1-3 lemmas, since hPX2A's frame pattern *)
(* is S (S (S b')) :: S p' :: pb and its target counter is  *)
(* S b' (the CASCADE55 step-1 pattern, generalised).       *)
Lemma NUM59ssa : 29403094 = S (S 29403092).
Proof. apply Nat.eqb_eq; vm_compute; reflexivity. Qed.
Lemma REP59a : forall w,
  (1, 1) :: (1, 2) :: (1, 2) :: repeat (1, 2) 29403092 ++ w
  = (1, 1) :: repeat (1, 2) 29403094 ++ w.
Proof. intro w. rewrite NUM59ssa. reflexivity. Qed.
Lemma NUM59ta1 : 14897638 = S (S (S 14897635)).
Proof. apply Nat.eqb_eq; vm_compute; reflexivity. Qed.
Lemma NUM59ta2 : 1523948 = S 1523947.
Proof. apply Nat.eqb_eq; vm_compute; reflexivity. Qed.
Lemma NUM59ta3 : 14897636 = S 14897635.
Proof. apply Nat.eqb_eq; vm_compute; reflexivity. Qed.
Lemma NUM59ssb : 1523948 = S (S 1523946).
Proof. apply Nat.eqb_eq; vm_compute; reflexivity. Qed.
Lemma REP59b : forall w,
  (1, 1) :: (1, 2) :: (1, 2) :: repeat (1, 2) 1523946 ++ w
  = (1, 1) :: repeat (1, 2) 1523948 ++ w.
Proof. intro w. rewrite NUM59ssb. reflexivity. Qed.
Lemma NUM59tb1 : 426279 = S (S (S 426276)).
Proof. apply Nat.eqb_eq; vm_compute; reflexivity. Qed.
Lemma NUM59tb2 : 308525 = S 308524.
Proof. apply Nat.eqb_eq; vm_compute; reflexivity. Qed.
Lemma NUM59tb3 : 426277 = S 426276.
Proof. apply Nat.eqb_eq; vm_compute; reflexivity. Qed.
Lemma NUM59ssc : 3474178 = S (S 3474176).
Proof. apply Nat.eqb_eq; vm_compute; reflexivity. Qed.
Lemma REP59c : forall w,
  (1, 1) :: (1, 2) :: (1, 2) :: repeat (1, 2) 3474176 ++ w
  = (1, 1) :: repeat (1, 2) 3474178 ++ w.
Proof. intro w. rewrite NUM59ssc. reflexivity. Qed.
Lemma NUM59tc1 : 1832473 = S (S (S 1832470)).
Proof. apply Nat.eqb_eq; vm_compute; reflexivity. Qed.
Lemma NUM59tc2 : 58213 = S 58212.
Proof. apply Nat.eqb_eq; vm_compute; reflexivity. Qed.
Lemma NUM59tc3 : 1832471 = S 1832470.
Proof. apply Nat.eqb_eq; vm_compute; reflexivity. Qed.
Lemma NUM59ssd : 232864 = S (S 232862).
Proof. apply Nat.eqb_eq; vm_compute; reflexivity. Qed.
Lemma REP59d : forall w,
  (1, 1) :: (1, 2) :: (1, 2) :: repeat (1, 2) 232862 ++ w
  = (1, 1) :: repeat (1, 2) 232864 ++ w.
Proof. intro w. rewrite NUM59ssd. reflexivity. Qed.
Lemma NUM59td1 : 145667 = S (S (S 145664)).
Proof. apply Nat.eqb_eq; vm_compute; reflexivity. Qed.
Lemma NUM59td2 : 36327 = S 36326.
Proof. apply Nat.eqb_eq; vm_compute; reflexivity. Qed.
Lemma NUM59td3 : 145665 = S 145664.
Proof. apply Nat.eqb_eq; vm_compute; reflexivity. Qed.

(* Closed arithmetic identities for the large DIPGRIND /   *)
(* hGRIND_even / CLEANG steps and the head-pair             *)
(* normalisations of CASCADE59, factored into standalone    *)
(* lemmas (eqb/vm proofs) and rewritten in the step blocks, *)
(* so the applies meet the lemmas' arithmetic forms        *)
(* syntactically instead of by a closed multiplication or   *)
(* subtraction conversion at depth >= 100000                *)
(* (cf. the NUM59ss / REP59 lemmas).                       *)
Lemma NUM59X1 : 1523947 = S 1523946.
Proof. apply Nat.eqb_eq; vm_compute; reflexivity. Qed.
Lemma NUM59X2 : 14897634 = 14897636 - 2.
Proof. apply Nat.eqb_eq; vm_compute; reflexivity. Qed.
Lemma NUM59X3 : 14897632 = 14897634 - 2.
Proof. apply Nat.eqb_eq; vm_compute; reflexivity. Qed.
Lemma NUM59X4 : 14897632 = 2 * 1523946 + 11849740.
Proof. apply Nat.eqb_eq; vm_compute; reflexivity. Qed.
Lemma NUM59X5 : 426277 = 2 * 213137 + 3.
Proof. apply Nat.eqb_eq; vm_compute; reflexivity. Qed.
Lemma NUM59X6 : 426280 = 2 * 213137 + 6.
Proof. apply Nat.eqb_eq; vm_compute; reflexivity. Qed.
Lemma NUM59X7 : 308525 = S 308524.
Proof. apply Nat.eqb_eq; vm_compute; reflexivity. Qed.
Lemma NUM59X8 : 426281 = 426280 + 1.
Proof. apply Nat.eqb_eq; vm_compute; reflexivity. Qed.
Lemma NUM59X9 : 3474176 = 3474177 - 1.
Proof. apply Nat.eqb_eq; vm_compute; reflexivity. Qed.
Lemma NUM59X10 : 11849738 = 11849740 - 2.
Proof. apply Nat.eqb_eq; vm_compute; reflexivity. Qed.
Lemma NUM59X11 : 3474176 = 2 * 1737086 + 4.
Proof. apply Nat.eqb_eq; vm_compute; reflexivity. Qed.
Lemma NUM59X12 : 1832473 = S 1832472.
Proof. apply Nat.eqb_eq; vm_compute; reflexivity. Qed.
Lemma NUM59X13 : 3474176 = S 3474175.
Proof. apply Nat.eqb_eq; vm_compute; reflexivity. Qed.
Lemma NUM59X14 : 1832473 = S 1832472.
Proof. apply Nat.eqb_eq; vm_compute; reflexivity. Qed.
Lemma NUM59X15 : 11849736 = 11849738 - 2.
Proof. apply Nat.eqb_eq; vm_compute; reflexivity. Qed.
Lemma NUM59X16 : 11849734 = 11849736 - 2.
Proof. apply Nat.eqb_eq; vm_compute; reflexivity. Qed.
Lemma NUM59X17 : 11849734 = 2 * 3474176 + 4901382.
Proof. apply Nat.eqb_eq; vm_compute; reflexivity. Qed.
Lemma NUM59X18 : 1832469 = 1832471 - 2.
Proof. apply Nat.eqb_eq; vm_compute; reflexivity. Qed.
Lemma NUM59X19 : 1832467 = 1832469 - 2.
Proof. apply Nat.eqb_eq; vm_compute; reflexivity. Qed.
Lemma NUM59X20 : 1832467 = 2 * 58211 + 1716045.
Proof. apply Nat.eqb_eq; vm_compute; reflexivity. Qed.
Lemma NUM59X21 : 10759 = S 10758.
Proof. apply Nat.eqb_eq; vm_compute; reflexivity. Qed.
Lemma NUM59X22 : 116428 = 116429 - 1.
Proof. apply Nat.eqb_eq; vm_compute; reflexivity. Qed.
Lemma NUM59X23 : 1716043 = 1716045 - 2.
Proof. apply Nat.eqb_eq; vm_compute; reflexivity. Qed.
Lemma NUM59X24 : 116428 = 2 * 58212 + 4.
Proof. apply Nat.eqb_eq; vm_compute; reflexivity. Qed.
Lemma NUM59X25 : 60062 = S 60061.
Proof. apply Nat.eqb_eq; vm_compute; reflexivity. Qed.
Lemma NUM59X26 : 116428 = S 116427.
Proof. apply Nat.eqb_eq; vm_compute; reflexivity. Qed.
Lemma NUM59X27 : 1716041 = 1716043 - 2.
Proof. apply Nat.eqb_eq; vm_compute; reflexivity. Qed.
Lemma NUM59X28 : 1716039 = 1716041 - 2.
Proof. apply Nat.eqb_eq; vm_compute; reflexivity. Qed.
Lemma NUM59X29 : 1716039 = 2 * 116428 + 1483183.
Proof. apply Nat.eqb_eq; vm_compute; reflexivity. Qed.
Lemma NUM59X30 : 20669 = S 20668.
Proof. apply Nat.eqb_eq; vm_compute; reflexivity. Qed.
Lemma NUM59X31 : 232862 = 232863 - 1.
Proof. apply Nat.eqb_eq; vm_compute; reflexivity. Qed.
Lemma NUM59X32 : 1483181 = 1483183 - 2.
Proof. apply Nat.eqb_eq; vm_compute; reflexivity. Qed.
Lemma NUM59X33 : 232862 = 2 * 116429 + 4.
Proof. apply Nat.eqb_eq; vm_compute; reflexivity. Qed.
Lemma NUM59X34 : 145667 = S 145666.
Proof. apply Nat.eqb_eq; vm_compute; reflexivity. Qed.
Lemma NUM59X35 : 232862 = S 232861.
Proof. apply Nat.eqb_eq; vm_compute; reflexivity. Qed.
Lemma NUM59X36 : 145667 = S 145666.
Proof. apply Nat.eqb_eq; vm_compute; reflexivity. Qed.
Lemma NUM59X37 : 1483179 = 1483181 - 2.
Proof. apply Nat.eqb_eq; vm_compute; reflexivity. Qed.
Lemma NUM59X38 : 1483177 = 1483179 - 2.
Proof. apply Nat.eqb_eq; vm_compute; reflexivity. Qed.
Lemma NUM59X39 : 1483177 = 2 * 232862 + 1017453.
Proof. apply Nat.eqb_eq; vm_compute; reflexivity. Qed.
Lemma NUM59X40 : 145661 = 2 * 36325 + 73011.
Proof. apply Nat.eqb_eq; vm_compute; reflexivity. Qed.
Lemma NUM59X41 : 7710 = S 7709.
Proof. apply Nat.eqb_eq; vm_compute; reflexivity. Qed.
Lemma NUM59X42 : 75224 = 2 * 37610 + 4.
Proof. apply Nat.eqb_eq; vm_compute; reflexivity. Qed.
Lemma NUM59X43 : 49409 = S 49408.
Proof. apply Nat.eqb_eq; vm_compute; reflexivity. Qed.
Lemma NUM59X44 : 73005 = 2 * 36501 + 3.
Proof. apply Nat.eqb_eq; vm_compute; reflexivity. Qed.
Lemma NUM59X45 : 73010 = 2 * 36501 + 8.
Proof. apply Nat.eqb_eq; vm_compute; reflexivity. Qed.
Lemma NUM59X46 : 538740 = 538741 - 1.
Proof. apply Nat.eqb_eq; vm_compute; reflexivity. Qed.
Lemma NUM59X47 : 1017451 = 1017453 - 2.
Proof. apply Nat.eqb_eq; vm_compute; reflexivity. Qed.
Lemma NUM59X48 : 538740 = 2 * 269368 + 4.
Proof. apply Nat.eqb_eq; vm_compute; reflexivity. Qed.
Lemma NUM59X49 : 308090 = S 308089.
Proof. apply Nat.eqb_eq; vm_compute; reflexivity. Qed.
Lemma NUM59X50 : 538740 = S 538739.
Proof. apply Nat.eqb_eq; vm_compute; reflexivity. Qed.
Lemma NUM59X51 : 308090 = S 308089.
Proof. apply Nat.eqb_eq; vm_compute; reflexivity. Qed.
Lemma NUM59X52 : 1017449 = 1017451 - 2.
Proof. apply Nat.eqb_eq; vm_compute; reflexivity. Qed.
Lemma NUM59X53 : 1017447 = 1017449 - 2.
Proof. apply Nat.eqb_eq; vm_compute; reflexivity. Qed.
Lemma NUM59X54 : 1017447 = 2 * 508722 + 3.
Proof. apply Nat.eqb_eq; vm_compute; reflexivity. Qed.
Lemma NUM59X55 : 1017452 = 2 * 508722 + 8.
Proof. apply Nat.eqb_eq; vm_compute; reflexivity. Qed.
Lemma NUM59X56 : 538742 = S 538741.
Proof. apply Nat.eqb_eq; vm_compute; reflexivity. Qed.
Lemma NUM59X57 : 1017455 = 1017454 + 1.
Proof. apply Nat.eqb_eq; vm_compute; reflexivity. Qed.
Lemma NUM59X58 : 7965810 = 7965811 - 1.
Proof. apply Nat.eqb_eq; vm_compute; reflexivity. Qed.
Lemma NUM59X59 : 4901380 = 4901382 - 2.
Proof. apply Nat.eqb_eq; vm_compute; reflexivity. Qed.
Lemma NUM59X60 : 7965810 = 2 * 3982903 + 4.
Proof. apply Nat.eqb_eq; vm_compute; reflexivity. Qed.
Lemma NUM59X61 : 4012920 = S 4012919.
Proof. apply Nat.eqb_eq; vm_compute; reflexivity. Qed.
Lemma NUM59X62 : 7965810 = S 7965809.
Proof. apply Nat.eqb_eq; vm_compute; reflexivity. Qed.
Lemma NUM59X63 : 4012920 = S 4012919.
Proof. apply Nat.eqb_eq; vm_compute; reflexivity. Qed.
Lemma NUM59X64 : 4901378 = 4901380 - 2.
Proof. apply Nat.eqb_eq; vm_compute; reflexivity. Qed.
Lemma NUM59X65 : 4901376 = 4901378 - 2.
Proof. apply Nat.eqb_eq; vm_compute; reflexivity. Qed.
Lemma NUM59X66 : 4901376 = 2 * 2450687 + 2.
Proof. apply Nat.eqb_eq; vm_compute; reflexivity. Qed.
Lemma NUM59X67 : 4901380 = 2 * 2450687 + 6.
Proof. apply Nat.eqb_eq; vm_compute; reflexivity. Qed.
Lemma NUM59X68 : 4901380 = S 4901379.
Proof. apply Nat.eqb_eq; vm_compute; reflexivity. Qed.
Lemma NUM59X69 : 4901381 = S (S 4901379).
Proof. apply Nat.eqb_eq; vm_compute; reflexivity. Qed.
Lemma NUM59X70 : 7965811 = S 7965810.
Proof. apply Nat.eqb_eq; vm_compute; reflexivity. Qed.


(* CASCADE59a: steps 1-8 of the CASCADE59 chain. *)
Lemma CASCADE59a : forall w,
  hsteps (HC [14897638; 1523948; 426279; 308525; 58213; 30332; 931; 608; 77; 35; 20; 0] 0 3 2 (repeat (1, 2) 29403092 ++ w) 1)
         (HB [58213; 30332; 931; 608; 77; 35; 20; 0] 308525 1 426281 (repeat (1, 2) 1523948 ++ (11849740, 2) :: (1, 1) :: repeat (1, 2) 29403094 ++ w) 1).
Proof.
  intro w.
  (* step 1: P PX2A *)
  apply (hsteps_trans _ (HC [426279; 308525; 58213; 30332; 931; 608; 77; 35; 20; 0] 1523947 14897636 2 ((1, 1) :: repeat (1, 2) 29403094 ++ w) 1)).
  {
    rewrite NUM59ta1. rewrite NUM59ta2. rewrite NUM59ta3.
    replace ((1, 1) :: repeat (1, 2) 29403094 ++ w)
      with ((1, 1) :: (1, 2) :: (1, 2) :: repeat (1, 2) 29403092 ++ w)
      by (apply REP59a).
    exact (hsteps_step _ _ _ (hPX2A 14897635 1523947 [426279; 308525; 58213; 30332; 931; 608; 77; 35; 20; 0] (repeat (1, 2) 29403092 ++ w) 1) (hsteps_refl _)).
  }
  (* step 2: P PUSH *)
  apply (hsteps_trans _ (HC [426279; 308525; 58213; 30332; 931; 608; 77; 35; 20; 0] 1523946 1 2 ((14897634, 2) :: (1, 1) :: repeat (1, 2) 29403094 ++ w) 1)).
  {
    rewrite NUM59X1.
    rewrite NUM59X2.
    apply (sPUSH [426279; 308525; 58213; 30332; 931; 608; 77; 35; 20; 0] 1523946 14897636 ((1, 1) :: repeat (1, 2) 29403094 ++ w) 1); closearith.
  }
  (* step 3: P TDN *)
  apply (hsteps_trans _ (HB [426279; 308525; 58213; 30332; 931; 608; 77; 35; 20; 0] 1523946 1 4 ((14897634, 2) :: (1, 1) :: repeat (1, 2) 29403094 ++ w) 1)).
  {
    apply (sTDN [426279; 308525; 58213; 30332; 931; 608; 77; 35; 20; 0] 1523946 ((14897634, 2) :: (1, 1) :: repeat (1, 2) 29403094 ++ w) 1).
  }
  (* step 4: sTUP *)
  apply (hsteps_trans _ (HC [426279; 308525; 58213; 30332; 931; 608; 77; 35; 20; 0] 1523946 3 2 ((14897632, 2) :: (1, 1) :: repeat (1, 2) 29403094 ++ w) 1)).
  {
    rewrite NUM59X3.
    apply (sTUP [426279; 308525; 58213; 30332; 931; 608; 77; 35; 20; 0] 1523946 4 14897634 2 ((1, 1) :: repeat (1, 2) 29403094 ++ w) 1); closearith.
  }
  (* step 5: DIPGRIND 1523946 11849740 *)
  apply (hsteps_trans _ (HC [426279; 308525; 58213; 30332; 931; 608; 77; 35; 20; 0] 0 3 2 (repeat (1, 2) 1523946 ++ (11849740, 2) :: (1, 1) :: repeat (1, 2) 29403094 ++ w) 1)).
  {
    rewrite NUM59X4.
    apply (DIPGRIND 1523946 11849740 [426279; 308525; 58213; 30332; 931; 608; 77; 35; 20; 0] ((1, 1) :: repeat (1, 2) 29403094 ++ w) 1); closearith.
  }
  (* step 6: P PX2A *)
  apply (hsteps_trans _ (HC [58213; 30332; 931; 608; 77; 35; 20; 0] 308524 426277 2 ((1, 1) :: repeat (1, 2) 1523948 ++ (11849740, 2) :: (1, 1) :: repeat (1, 2) 29403094 ++ w) 1)).
  {
    rewrite NUM59tb1. rewrite NUM59tb2. rewrite NUM59tb3.
    replace ((1, 1) :: repeat (1, 2) 1523948 ++ (11849740, 2) :: (1, 1) :: repeat (1, 2) 29403094 ++ w)
      with ((1, 1) :: (1, 2) :: (1, 2) :: repeat (1, 2) 1523946 ++ (11849740, 2) :: (1, 1) :: repeat (1, 2) 29403094 ++ w)
      by (apply REP59b).
    exact (hsteps_step _ _ _ (hPX2A 426276 308524 [58213; 30332; 931; 608; 77; 35; 20; 0] (repeat (1, 2) 1523946 ++ (11849740, 2) :: (1, 1) :: repeat (1, 2) 29403094 ++ w) 1) (hsteps_refl _)).
  }
  (* step 7: hGRIND 213137 *)
  apply (hsteps_trans _ (HB [58213; 30332; 931; 608; 77; 35; 20; 0] 308524 1 426280 ((1, 1) :: repeat (1, 2) 1523948 ++ (11849740, 2) :: (1, 1) :: repeat (1, 2) 29403094 ++ w) 1)).
  {
    rewrite NUM59X5.
    rewrite NUM59X6.
    apply (hGRIND 213137 [58213; 30332; 931; 608; 77; 35; 20; 0] 308524 ((1, 1) :: repeat (1, 2) 1523948 ++ (11849740, 2) :: (1, 1) :: repeat (1, 2) 29403094 ++ w) 1); closearith.
  }
  (* step 8: P POP *)
  rewrite NUM59X7.
  rewrite NUM59X8.
  apply (sPOP1 [58213; 30332; 931; 608; 77; 35; 20; 0] 308524 426280 (repeat (1, 2) 1523948 ++ (11849740, 2) :: (1, 1) :: repeat (1, 2) 29403094 ++ w) 1); closearith.
Qed.

(* CASCADE59b: steps 9-9 of the CASCADE59 chain. *)
Lemma CASCADE59b : forall w,
  hsteps (HB [58213; 30332; 931; 608; 77; 35; 20; 0] 308525 1 426281 (repeat (1, 2) 1523948 ++ (11849740, 2) :: (1, 1) :: repeat (1, 2) 29403094 ++ w) 1)
         (HB [58213; 30332; 931; 608; 77; 35; 20; 0] 1832473 1 3474177 ((11849740, 2) :: (1, 1) :: repeat (1, 2) 29403094 ++ w) 1).
Proof.
  intro w.
  replace 1832473 with (308525 + 1523948)
    by (apply Nat.eqb_eq; vm_compute; reflexivity).
  replace 3474177 with (426281 + 2 * 1523948)
    by (apply Nat.eqb_eq; vm_compute; reflexivity).
  (* step 9: M pop12 (1523948,) *)
  apply (pop12 1523948 [58213; 30332; 931; 608; 77; 35; 20; 0] 308525 426281 ((11849740, 2) :: (1, 1) :: repeat (1, 2) 29403094 ++ w) 1); closearith.
Qed.

(* CASCADE59c: steps 10-65 of the CASCADE59 chain. *)
Lemma CASCADE59c : forall w,
  hsteps (HB [58213; 30332; 931; 608; 77; 35; 20; 0] 1832473 1 3474177 ((11849740, 2) :: (1, 1) :: repeat (1, 2) 29403094 ++ w) 1)
         (HC [20; 0] 34 1 2 ((47, 2) :: (1, 1) :: repeat (1, 2) 192 ++ (66, 2) :: (1, 1) :: repeat (1, 2) 931 ++ (28468, 2) :: (1, 1) :: repeat (1, 2) 58213 ++ (1716045, 2) :: (1, 1) :: repeat (1, 2) 3474178 ++ (4901382, 2) :: (1, 1) :: repeat (1, 2) 29403094 ++ w) 1).
Proof.
  intro w.
  (* step 10: sTUP *)
  apply (hsteps_trans _ (HC [58213; 30332; 931; 608; 77; 35; 20; 0] 1832473 3474176 2 ((11849738, 2) :: (1, 1) :: repeat (1, 2) 29403094 ++ w) 1)).
  {
    rewrite NUM59X9.
    rewrite NUM59X10.
    apply (sTUP [58213; 30332; 931; 608; 77; 35; 20; 0] 1832473 3474177 11849740 2 ((1, 1) :: repeat (1, 2) 29403094 ++ w) 1); closearith.
  }
  (* step 11: hGRIND_even 1737086 *)
  apply (hsteps_trans _ (HB [58213; 30332; 931; 608; 77; 35; 20; 0] 1832472 1 3474176 ((2, 2) :: (11849738, 2) :: (1, 1) :: repeat (1, 2) 29403094 ++ w) 1)).
  {
    rewrite NUM59X11.
    rewrite NUM59X12.
    apply (hGRIND_even 1737086 [58213; 30332; 931; 608; 77; 35; 20; 0] 1832472 ((11849738, 2) :: (1, 1) :: repeat (1, 2) 29403094 ++ w) 1); closearith.
  }
  (* step 12: P TUP2_1 *)
  apply (hsteps_trans _ (HC [1832473; 58213; 30332; 931; 608; 77; 35; 20; 0] 3474176 1 2 ((11849736, 2) :: (1, 1) :: repeat (1, 2) 29403094 ++ w) 1)).
  {
    rewrite NUM59X13.
    rewrite NUM59X14.
    rewrite NUM59X15.
    apply (sTUP2_1 [58213; 30332; 931; 608; 77; 35; 20; 0] 1832472 3474175 11849738 ((1, 1) :: repeat (1, 2) 29403094 ++ w) 1); closearith.
  }
  (* step 13: P TDN *)
  apply (hsteps_trans _ (HB [1832473; 58213; 30332; 931; 608; 77; 35; 20; 0] 3474176 1 4 ((11849736, 2) :: (1, 1) :: repeat (1, 2) 29403094 ++ w) 1)).
  {
    apply (sTDN [1832473; 58213; 30332; 931; 608; 77; 35; 20; 0] 3474176 ((11849736, 2) :: (1, 1) :: repeat (1, 2) 29403094 ++ w) 1).
  }
  (* step 14: sTUP *)
  apply (hsteps_trans _ (HC [1832473; 58213; 30332; 931; 608; 77; 35; 20; 0] 3474176 3 2 ((11849734, 2) :: (1, 1) :: repeat (1, 2) 29403094 ++ w) 1)).
  {
    rewrite NUM59X16.
    apply (sTUP [1832473; 58213; 30332; 931; 608; 77; 35; 20; 0] 3474176 4 11849736 2 ((1, 1) :: repeat (1, 2) 29403094 ++ w) 1); closearith.
  }
  (* step 15: DIPGRIND 3474176 4901382 *)
  apply (hsteps_trans _ (HC [1832473; 58213; 30332; 931; 608; 77; 35; 20; 0] 0 3 2 (repeat (1, 2) 3474176 ++ (4901382, 2) :: (1, 1) :: repeat (1, 2) 29403094 ++ w) 1)).
  {
    rewrite NUM59X17.
    apply (DIPGRIND 3474176 4901382 [1832473; 58213; 30332; 931; 608; 77; 35; 20; 0] ((1, 1) :: repeat (1, 2) 29403094 ++ w) 1); closearith.
  }
  (* step 16: P PX2A *)
  apply (hsteps_trans _ (HC [30332; 931; 608; 77; 35; 20; 0] 58212 1832471 2 ((1, 1) :: repeat (1, 2) 3474178 ++ (4901382, 2) :: (1, 1) :: repeat (1, 2) 29403094 ++ w) 1)).
  {
    rewrite NUM59tc1. rewrite NUM59tc2. rewrite NUM59tc3.
    replace ((1, 1) :: repeat (1, 2) 3474178 ++ (4901382, 2) :: (1, 1) :: repeat (1, 2) 29403094 ++ w)
      with ((1, 1) :: (1, 2) :: (1, 2) :: repeat (1, 2) 3474176 ++ (4901382, 2) :: (1, 1) :: repeat (1, 2) 29403094 ++ w)
      by (apply REP59c).
    exact (hsteps_step _ _ _ (hPX2A 1832470 58212 [30332; 931; 608; 77; 35; 20; 0] (repeat (1, 2) 3474176 ++ (4901382, 2) :: (1, 1) :: repeat (1, 2) 29403094 ++ w) 1) (hsteps_refl _)).
  }
  (* step 17: P PUSH *)
  apply (hsteps_trans _ (HC [30332; 931; 608; 77; 35; 20; 0] 58211 1 2 ((1832469, 2) :: (1, 1) :: repeat (1, 2) 3474178 ++ (4901382, 2) :: (1, 1) :: repeat (1, 2) 29403094 ++ w) 1)).
  {
    rewrite NUM59X18.
    apply (sPUSH [30332; 931; 608; 77; 35; 20; 0] 58211 1832471 ((1, 1) :: repeat (1, 2) 3474178 ++ (4901382, 2) :: (1, 1) :: repeat (1, 2) 29403094 ++ w) 1); closearith.
  }
  (* step 18: P TDN *)
  apply (hsteps_trans _ (HB [30332; 931; 608; 77; 35; 20; 0] 58211 1 4 ((1832469, 2) :: (1, 1) :: repeat (1, 2) 3474178 ++ (4901382, 2) :: (1, 1) :: repeat (1, 2) 29403094 ++ w) 1)).
  {
    apply (sTDN [30332; 931; 608; 77; 35; 20; 0] 58211 ((1832469, 2) :: (1, 1) :: repeat (1, 2) 3474178 ++ (4901382, 2) :: (1, 1) :: repeat (1, 2) 29403094 ++ w) 1).
  }
  (* step 19: sTUP *)
  apply (hsteps_trans _ (HC [30332; 931; 608; 77; 35; 20; 0] 58211 3 2 ((1832467, 2) :: (1, 1) :: repeat (1, 2) 3474178 ++ (4901382, 2) :: (1, 1) :: repeat (1, 2) 29403094 ++ w) 1)).
  {
    rewrite NUM59X19.
    apply (sTUP [30332; 931; 608; 77; 35; 20; 0] 58211 4 1832469 2 ((1, 1) :: repeat (1, 2) 3474178 ++ (4901382, 2) :: (1, 1) :: repeat (1, 2) 29403094 ++ w) 1); closearith.
  }
  (* step 20: DIPGRIND 58211 1716045 *)
  apply (hsteps_trans _ (HC [30332; 931; 608; 77; 35; 20; 0] 0 3 2 (repeat (1, 2) 58211 ++ (1716045, 2) :: (1, 1) :: repeat (1, 2) 3474178 ++ (4901382, 2) :: (1, 1) :: repeat (1, 2) 29403094 ++ w) 1)).
  {
    rewrite NUM59X20.
    apply (DIPGRIND 58211 1716045 [30332; 931; 608; 77; 35; 20; 0] ((1, 1) :: repeat (1, 2) 3474178 ++ (4901382, 2) :: (1, 1) :: repeat (1, 2) 29403094 ++ w) 1); closearith.
  }
  (* step 21: P PX2A *)
  apply (hsteps_trans _ (HC [608; 77; 35; 20; 0] 930 30330 2 ((1, 1) :: repeat (1, 2) 58213 ++ (1716045, 2) :: (1, 1) :: repeat (1, 2) 3474178 ++ (4901382, 2) :: (1, 1) :: repeat (1, 2) 29403094 ++ w) 1)).
  {
    exact (hsteps_step _ _ _ (hPX2A 30329 930 [608; 77; 35; 20; 0] (repeat (1, 2) 58211 ++ (1716045, 2) :: (1, 1) :: repeat (1, 2) 3474178 ++ (4901382, 2) :: (1, 1) :: repeat (1, 2) 29403094 ++ w) 1) (hsteps_refl _)).
  }
  (* step 22: P PUSH *)
  apply (hsteps_trans _ (HC [608; 77; 35; 20; 0] 929 1 2 ((30328, 2) :: (1, 1) :: repeat (1, 2) 58213 ++ (1716045, 2) :: (1, 1) :: repeat (1, 2) 3474178 ++ (4901382, 2) :: (1, 1) :: repeat (1, 2) 29403094 ++ w) 1)).
  {
    replace ((30328, 2) :: (1, 1) :: repeat (1, 2) 58213 ++ (1716045, 2) :: (1, 1) :: repeat (1, 2) 3474178 ++ (4901382, 2) :: (1, 1) :: repeat (1, 2) 29403094 ++ w) with ((30330 - 2, 2) :: (1, 1) :: repeat (1, 2) 58213 ++ (1716045, 2) :: (1, 1) :: repeat (1, 2) 3474178 ++ (4901382, 2) :: (1, 1) :: repeat (1, 2) 29403094 ++ w) by sec_eq.
    apply (sPUSH [608; 77; 35; 20; 0] 929 30330 ((1, 1) :: repeat (1, 2) 58213 ++ (1716045, 2) :: (1, 1) :: repeat (1, 2) 3474178 ++ (4901382, 2) :: (1, 1) :: repeat (1, 2) 29403094 ++ w) 1); closearith.
  }
  (* step 23: P TDN *)
  apply (hsteps_trans _ (HB [608; 77; 35; 20; 0] 929 1 4 ((30328, 2) :: (1, 1) :: repeat (1, 2) 58213 ++ (1716045, 2) :: (1, 1) :: repeat (1, 2) 3474178 ++ (4901382, 2) :: (1, 1) :: repeat (1, 2) 29403094 ++ w) 1)).
  {
    apply (sTDN [608; 77; 35; 20; 0] 929 ((30328, 2) :: (1, 1) :: repeat (1, 2) 58213 ++ (1716045, 2) :: (1, 1) :: repeat (1, 2) 3474178 ++ (4901382, 2) :: (1, 1) :: repeat (1, 2) 29403094 ++ w) 1).
  }
  (* step 24: sTUP *)
  apply (hsteps_trans _ (HC [608; 77; 35; 20; 0] 929 3 2 ((30326, 2) :: (1, 1) :: repeat (1, 2) 58213 ++ (1716045, 2) :: (1, 1) :: repeat (1, 2) 3474178 ++ (4901382, 2) :: (1, 1) :: repeat (1, 2) 29403094 ++ w) 1)).
  {
    replace ((30326, 2) :: (1, 1) :: repeat (1, 2) 58213 ++ (1716045, 2) :: (1, 1) :: repeat (1, 2) 3474178 ++ (4901382, 2) :: (1, 1) :: repeat (1, 2) 29403094 ++ w) with ((30328 - 2, 2) :: (1, 1) :: repeat (1, 2) 58213 ++ (1716045, 2) :: (1, 1) :: repeat (1, 2) 3474178 ++ (4901382, 2) :: (1, 1) :: repeat (1, 2) 29403094 ++ w) by sec_eq.
    apply (sTUP [608; 77; 35; 20; 0] 929 4 30328 2 ((1, 1) :: repeat (1, 2) 58213 ++ (1716045, 2) :: (1, 1) :: repeat (1, 2) 3474178 ++ (4901382, 2) :: (1, 1) :: repeat (1, 2) 29403094 ++ w) 1); closearith.
  }
  (* step 25: DIPGRIND 929 28468 *)
  apply (hsteps_trans _ (HC [608; 77; 35; 20; 0] 0 3 2 (repeat (1, 2) 929 ++ (28468, 2) :: (1, 1) :: repeat (1, 2) 58213 ++ (1716045, 2) :: (1, 1) :: repeat (1, 2) 3474178 ++ (4901382, 2) :: (1, 1) :: repeat (1, 2) 29403094 ++ w) 1)).
  {
    apply (DIPGRIND 929 28468 [608; 77; 35; 20; 0] ((1, 1) :: repeat (1, 2) 58213 ++ (1716045, 2) :: (1, 1) :: repeat (1, 2) 3474178 ++ (4901382, 2) :: (1, 1) :: repeat (1, 2) 29403094 ++ w) 1); closearith.
  }
  (* step 26: P PX2A *)
  apply (hsteps_trans _ (HC [35; 20; 0] 76 606 2 ((1, 1) :: repeat (1, 2) 931 ++ (28468, 2) :: (1, 1) :: repeat (1, 2) 58213 ++ (1716045, 2) :: (1, 1) :: repeat (1, 2) 3474178 ++ (4901382, 2) :: (1, 1) :: repeat (1, 2) 29403094 ++ w) 1)).
  {
    exact (hsteps_step _ _ _ (hPX2A 605 76 [35; 20; 0] (repeat (1, 2) 929 ++ (28468, 2) :: (1, 1) :: repeat (1, 2) 58213 ++ (1716045, 2) :: (1, 1) :: repeat (1, 2) 3474178 ++ (4901382, 2) :: (1, 1) :: repeat (1, 2) 29403094 ++ w) 1) (hsteps_refl _)).
  }
  (* step 27: P PUSH *)
  apply (hsteps_trans _ (HC [35; 20; 0] 75 1 2 ((604, 2) :: (1, 1) :: repeat (1, 2) 931 ++ (28468, 2) :: (1, 1) :: repeat (1, 2) 58213 ++ (1716045, 2) :: (1, 1) :: repeat (1, 2) 3474178 ++ (4901382, 2) :: (1, 1) :: repeat (1, 2) 29403094 ++ w) 1)).
  {
    replace ((604, 2) :: (1, 1) :: repeat (1, 2) 931 ++ (28468, 2) :: (1, 1) :: repeat (1, 2) 58213 ++ (1716045, 2) :: (1, 1) :: repeat (1, 2) 3474178 ++ (4901382, 2) :: (1, 1) :: repeat (1, 2) 29403094 ++ w) with ((606 - 2, 2) :: (1, 1) :: repeat (1, 2) 931 ++ (28468, 2) :: (1, 1) :: repeat (1, 2) 58213 ++ (1716045, 2) :: (1, 1) :: repeat (1, 2) 3474178 ++ (4901382, 2) :: (1, 1) :: repeat (1, 2) 29403094 ++ w) by sec_eq.
    apply (sPUSH [35; 20; 0] 75 606 ((1, 1) :: repeat (1, 2) 931 ++ (28468, 2) :: (1, 1) :: repeat (1, 2) 58213 ++ (1716045, 2) :: (1, 1) :: repeat (1, 2) 3474178 ++ (4901382, 2) :: (1, 1) :: repeat (1, 2) 29403094 ++ w) 1); closearith.
  }
  (* step 28: P TDN *)
  apply (hsteps_trans _ (HB [35; 20; 0] 75 1 4 ((604, 2) :: (1, 1) :: repeat (1, 2) 931 ++ (28468, 2) :: (1, 1) :: repeat (1, 2) 58213 ++ (1716045, 2) :: (1, 1) :: repeat (1, 2) 3474178 ++ (4901382, 2) :: (1, 1) :: repeat (1, 2) 29403094 ++ w) 1)).
  {
    apply (sTDN [35; 20; 0] 75 ((604, 2) :: (1, 1) :: repeat (1, 2) 931 ++ (28468, 2) :: (1, 1) :: repeat (1, 2) 58213 ++ (1716045, 2) :: (1, 1) :: repeat (1, 2) 3474178 ++ (4901382, 2) :: (1, 1) :: repeat (1, 2) 29403094 ++ w) 1).
  }
  (* step 29: sTUP *)
  apply (hsteps_trans _ (HC [35; 20; 0] 75 3 2 ((602, 2) :: (1, 1) :: repeat (1, 2) 931 ++ (28468, 2) :: (1, 1) :: repeat (1, 2) 58213 ++ (1716045, 2) :: (1, 1) :: repeat (1, 2) 3474178 ++ (4901382, 2) :: (1, 1) :: repeat (1, 2) 29403094 ++ w) 1)).
  {
    replace ((602, 2) :: (1, 1) :: repeat (1, 2) 931 ++ (28468, 2) :: (1, 1) :: repeat (1, 2) 58213 ++ (1716045, 2) :: (1, 1) :: repeat (1, 2) 3474178 ++ (4901382, 2) :: (1, 1) :: repeat (1, 2) 29403094 ++ w) with ((604 - 2, 2) :: (1, 1) :: repeat (1, 2) 931 ++ (28468, 2) :: (1, 1) :: repeat (1, 2) 58213 ++ (1716045, 2) :: (1, 1) :: repeat (1, 2) 3474178 ++ (4901382, 2) :: (1, 1) :: repeat (1, 2) 29403094 ++ w) by sec_eq.
    apply (sTUP [35; 20; 0] 75 4 604 2 ((1, 1) :: repeat (1, 2) 931 ++ (28468, 2) :: (1, 1) :: repeat (1, 2) 58213 ++ (1716045, 2) :: (1, 1) :: repeat (1, 2) 3474178 ++ (4901382, 2) :: (1, 1) :: repeat (1, 2) 29403094 ++ w) 1); closearith.
  }
  (* step 30: DIPGRIND 75 452 *)
  apply (hsteps_trans _ (HC [35; 20; 0] 0 3 2 (repeat (1, 2) 75 ++ (452, 2) :: (1, 1) :: repeat (1, 2) 931 ++ (28468, 2) :: (1, 1) :: repeat (1, 2) 58213 ++ (1716045, 2) :: (1, 1) :: repeat (1, 2) 3474178 ++ (4901382, 2) :: (1, 1) :: repeat (1, 2) 29403094 ++ w) 1)).
  {
    apply (DIPGRIND 75 452 [35; 20; 0] ((1, 1) :: repeat (1, 2) 931 ++ (28468, 2) :: (1, 1) :: repeat (1, 2) 58213 ++ (1716045, 2) :: (1, 1) :: repeat (1, 2) 3474178 ++ (4901382, 2) :: (1, 1) :: repeat (1, 2) 29403094 ++ w) 1); closearith.
  }
  (* step 31: P PX2A *)
  apply (hsteps_trans _ (HC [0] 19 33 2 ((1, 1) :: repeat (1, 2) 77 ++ (452, 2) :: (1, 1) :: repeat (1, 2) 931 ++ (28468, 2) :: (1, 1) :: repeat (1, 2) 58213 ++ (1716045, 2) :: (1, 1) :: repeat (1, 2) 3474178 ++ (4901382, 2) :: (1, 1) :: repeat (1, 2) 29403094 ++ w) 1)).
  {
    exact (hsteps_step _ _ _ (hPX2A 32 19 [0] (repeat (1, 2) 75 ++ (452, 2) :: (1, 1) :: repeat (1, 2) 931 ++ (28468, 2) :: (1, 1) :: repeat (1, 2) 58213 ++ (1716045, 2) :: (1, 1) :: repeat (1, 2) 3474178 ++ (4901382, 2) :: (1, 1) :: repeat (1, 2) 29403094 ++ w) 1) (hsteps_refl _)).
  }
  (* step 32: hGRIND 15 *)
  apply (hsteps_trans _ (HB [0] 19 1 36 ((1, 1) :: repeat (1, 2) 77 ++ (452, 2) :: (1, 1) :: repeat (1, 2) 931 ++ (28468, 2) :: (1, 1) :: repeat (1, 2) 58213 ++ (1716045, 2) :: (1, 1) :: repeat (1, 2) 3474178 ++ (4901382, 2) :: (1, 1) :: repeat (1, 2) 29403094 ++ w) 1)).
  {
    apply (hGRIND 15 [0] 19 ((1, 1) :: repeat (1, 2) 77 ++ (452, 2) :: (1, 1) :: repeat (1, 2) 931 ++ (28468, 2) :: (1, 1) :: repeat (1, 2) 58213 ++ (1716045, 2) :: (1, 1) :: repeat (1, 2) 3474178 ++ (4901382, 2) :: (1, 1) :: repeat (1, 2) 29403094 ++ w) 1); closearith.
  }
  (* step 33: P POP *)
  apply (hsteps_trans _ (HB [0] 20 1 37 (repeat (1, 2) 77 ++ (452, 2) :: (1, 1) :: repeat (1, 2) 931 ++ (28468, 2) :: (1, 1) :: repeat (1, 2) 58213 ++ (1716045, 2) :: (1, 1) :: repeat (1, 2) 3474178 ++ (4901382, 2) :: (1, 1) :: repeat (1, 2) 29403094 ++ w) 1)).
  {
    apply (sPOP1 [0] 19 36 (repeat (1, 2) 77 ++ (452, 2) :: (1, 1) :: repeat (1, 2) 931 ++ (28468, 2) :: (1, 1) :: repeat (1, 2) 58213 ++ (1716045, 2) :: (1, 1) :: repeat (1, 2) 3474178 ++ (4901382, 2) :: (1, 1) :: repeat (1, 2) 29403094 ++ w) 1); closearith.
  }
  (* step 34: M pop12 (77,) *)
  apply (hsteps_trans _ (HB [0] 97 1 191 ((452, 2) :: (1, 1) :: repeat (1, 2) 931 ++ (28468, 2) :: (1, 1) :: repeat (1, 2) 58213 ++ (1716045, 2) :: (1, 1) :: repeat (1, 2) 3474178 ++ (4901382, 2) :: (1, 1) :: repeat (1, 2) 29403094 ++ w) 1)).
  {
    apply (pop12 77 [0] 20 37 ((452, 2) :: (1, 1) :: repeat (1, 2) 931 ++ (28468, 2) :: (1, 1) :: repeat (1, 2) 58213 ++ (1716045, 2) :: (1, 1) :: repeat (1, 2) 3474178 ++ (4901382, 2) :: (1, 1) :: repeat (1, 2) 29403094 ++ w) 1); closearith.
  }
  (* step 35: sTUP *)
  apply (hsteps_trans _ (HC [0] 97 190 2 ((450, 2) :: (1, 1) :: repeat (1, 2) 931 ++ (28468, 2) :: (1, 1) :: repeat (1, 2) 58213 ++ (1716045, 2) :: (1, 1) :: repeat (1, 2) 3474178 ++ (4901382, 2) :: (1, 1) :: repeat (1, 2) 29403094 ++ w) 1)).
  {
    replace ((450, 2) :: (1, 1) :: repeat (1, 2) 931 ++ (28468, 2) :: (1, 1) :: repeat (1, 2) 58213 ++ (1716045, 2) :: (1, 1) :: repeat (1, 2) 3474178 ++ (4901382, 2) :: (1, 1) :: repeat (1, 2) 29403094 ++ w) with ((452 - 2, 2) :: (1, 1) :: repeat (1, 2) 931 ++ (28468, 2) :: (1, 1) :: repeat (1, 2) 58213 ++ (1716045, 2) :: (1, 1) :: repeat (1, 2) 3474178 ++ (4901382, 2) :: (1, 1) :: repeat (1, 2) 29403094 ++ w) by sec_eq.
    apply (sTUP [0] 97 191 452 2 ((1, 1) :: repeat (1, 2) 931 ++ (28468, 2) :: (1, 1) :: repeat (1, 2) 58213 ++ (1716045, 2) :: (1, 1) :: repeat (1, 2) 3474178 ++ (4901382, 2) :: (1, 1) :: repeat (1, 2) 29403094 ++ w) 1); closearith.
  }
  (* step 36: hGRIND_even 93 *)
  apply (hsteps_trans _ (HB [0] 96 1 190 ((2, 2) :: (450, 2) :: (1, 1) :: repeat (1, 2) 931 ++ (28468, 2) :: (1, 1) :: repeat (1, 2) 58213 ++ (1716045, 2) :: (1, 1) :: repeat (1, 2) 3474178 ++ (4901382, 2) :: (1, 1) :: repeat (1, 2) 29403094 ++ w) 1)).
  {
    apply (hGRIND_even 93 [0] 96 ((450, 2) :: (1, 1) :: repeat (1, 2) 931 ++ (28468, 2) :: (1, 1) :: repeat (1, 2) 58213 ++ (1716045, 2) :: (1, 1) :: repeat (1, 2) 3474178 ++ (4901382, 2) :: (1, 1) :: repeat (1, 2) 29403094 ++ w) 1); closearith.
  }
  (* step 37: P TUP2_1 *)
  apply (hsteps_trans _ (HC [97; 0] 190 1 2 ((448, 2) :: (1, 1) :: repeat (1, 2) 931 ++ (28468, 2) :: (1, 1) :: repeat (1, 2) 58213 ++ (1716045, 2) :: (1, 1) :: repeat (1, 2) 3474178 ++ (4901382, 2) :: (1, 1) :: repeat (1, 2) 29403094 ++ w) 1)).
  {
    replace ((448, 2) :: (1, 1) :: repeat (1, 2) 931 ++ (28468, 2) :: (1, 1) :: repeat (1, 2) 58213 ++ (1716045, 2) :: (1, 1) :: repeat (1, 2) 3474178 ++ (4901382, 2) :: (1, 1) :: repeat (1, 2) 29403094 ++ w) with ((450 - 2, 2) :: (1, 1) :: repeat (1, 2) 931 ++ (28468, 2) :: (1, 1) :: repeat (1, 2) 58213 ++ (1716045, 2) :: (1, 1) :: repeat (1, 2) 3474178 ++ (4901382, 2) :: (1, 1) :: repeat (1, 2) 29403094 ++ w) by sec_eq.
    apply (sTUP2_1 [0] 96 189 450 ((1, 1) :: repeat (1, 2) 931 ++ (28468, 2) :: (1, 1) :: repeat (1, 2) 58213 ++ (1716045, 2) :: (1, 1) :: repeat (1, 2) 3474178 ++ (4901382, 2) :: (1, 1) :: repeat (1, 2) 29403094 ++ w) 1); closearith.
  }
  (* step 38: P TDN *)
  apply (hsteps_trans _ (HB [97; 0] 190 1 4 ((448, 2) :: (1, 1) :: repeat (1, 2) 931 ++ (28468, 2) :: (1, 1) :: repeat (1, 2) 58213 ++ (1716045, 2) :: (1, 1) :: repeat (1, 2) 3474178 ++ (4901382, 2) :: (1, 1) :: repeat (1, 2) 29403094 ++ w) 1)).
  {
    apply (sTDN [97; 0] 190 ((448, 2) :: (1, 1) :: repeat (1, 2) 931 ++ (28468, 2) :: (1, 1) :: repeat (1, 2) 58213 ++ (1716045, 2) :: (1, 1) :: repeat (1, 2) 3474178 ++ (4901382, 2) :: (1, 1) :: repeat (1, 2) 29403094 ++ w) 1).
  }
  (* step 39: sTUP *)
  apply (hsteps_trans _ (HC [97; 0] 190 3 2 ((446, 2) :: (1, 1) :: repeat (1, 2) 931 ++ (28468, 2) :: (1, 1) :: repeat (1, 2) 58213 ++ (1716045, 2) :: (1, 1) :: repeat (1, 2) 3474178 ++ (4901382, 2) :: (1, 1) :: repeat (1, 2) 29403094 ++ w) 1)).
  {
    replace ((446, 2) :: (1, 1) :: repeat (1, 2) 931 ++ (28468, 2) :: (1, 1) :: repeat (1, 2) 58213 ++ (1716045, 2) :: (1, 1) :: repeat (1, 2) 3474178 ++ (4901382, 2) :: (1, 1) :: repeat (1, 2) 29403094 ++ w) with ((448 - 2, 2) :: (1, 1) :: repeat (1, 2) 931 ++ (28468, 2) :: (1, 1) :: repeat (1, 2) 58213 ++ (1716045, 2) :: (1, 1) :: repeat (1, 2) 3474178 ++ (4901382, 2) :: (1, 1) :: repeat (1, 2) 29403094 ++ w) by sec_eq.
    apply (sTUP [97; 0] 190 4 448 2 ((1, 1) :: repeat (1, 2) 931 ++ (28468, 2) :: (1, 1) :: repeat (1, 2) 58213 ++ (1716045, 2) :: (1, 1) :: repeat (1, 2) 3474178 ++ (4901382, 2) :: (1, 1) :: repeat (1, 2) 29403094 ++ w) 1); closearith.
  }
  (* step 40: DIPGRIND 190 66 *)
  apply (hsteps_trans _ (HC [97; 0] 0 3 2 (repeat (1, 2) 190 ++ (66, 2) :: (1, 1) :: repeat (1, 2) 931 ++ (28468, 2) :: (1, 1) :: repeat (1, 2) 58213 ++ (1716045, 2) :: (1, 1) :: repeat (1, 2) 3474178 ++ (4901382, 2) :: (1, 1) :: repeat (1, 2) 29403094 ++ w) 1)).
  {
    apply (DIPGRIND 190 66 [97; 0] ((1, 1) :: repeat (1, 2) 931 ++ (28468, 2) :: (1, 1) :: repeat (1, 2) 58213 ++ (1716045, 2) :: (1, 1) :: repeat (1, 2) 3474178 ++ (4901382, 2) :: (1, 1) :: repeat (1, 2) 29403094 ++ w) 1); closearith.
  }
  (* step 41: P PX2A0 *)
  apply (hsteps_trans _ (HB [0] 3 1 2 ((93, 2) :: (1, 1) :: repeat (1, 2) 192 ++ (66, 2) :: (1, 1) :: repeat (1, 2) 931 ++ (28468, 2) :: (1, 1) :: repeat (1, 2) 58213 ++ (1716045, 2) :: (1, 1) :: repeat (1, 2) 3474178 ++ (4901382, 2) :: (1, 1) :: repeat (1, 2) 29403094 ++ w) 1)).
  {
    exact (hsteps_step _ _ _ (hPX2A0 92 (repeat (1, 2) 190 ++ (66, 2) :: (1, 1) :: repeat (1, 2) 931 ++ (28468, 2) :: (1, 1) :: repeat (1, 2) 58213 ++ (1716045, 2) :: (1, 1) :: repeat (1, 2) 3474178 ++ (4901382, 2) :: (1, 1) :: repeat (1, 2) 29403094 ++ w) 1) (hsteps_refl _)).
  }
  (* step 42: sTUP *)
  apply (hsteps_trans _ (HC [0] 3 1 2 ((91, 2) :: (1, 1) :: repeat (1, 2) 192 ++ (66, 2) :: (1, 1) :: repeat (1, 2) 931 ++ (28468, 2) :: (1, 1) :: repeat (1, 2) 58213 ++ (1716045, 2) :: (1, 1) :: repeat (1, 2) 3474178 ++ (4901382, 2) :: (1, 1) :: repeat (1, 2) 29403094 ++ w) 1)).
  {
    replace ((91, 2) :: (1, 1) :: repeat (1, 2) 192 ++ (66, 2) :: (1, 1) :: repeat (1, 2) 931 ++ (28468, 2) :: (1, 1) :: repeat (1, 2) 58213 ++ (1716045, 2) :: (1, 1) :: repeat (1, 2) 3474178 ++ (4901382, 2) :: (1, 1) :: repeat (1, 2) 29403094 ++ w) with ((93 - 2, 2) :: (1, 1) :: repeat (1, 2) 192 ++ (66, 2) :: (1, 1) :: repeat (1, 2) 931 ++ (28468, 2) :: (1, 1) :: repeat (1, 2) 58213 ++ (1716045, 2) :: (1, 1) :: repeat (1, 2) 3474178 ++ (4901382, 2) :: (1, 1) :: repeat (1, 2) 29403094 ++ w) by sec_eq.
    apply (sTUP [0] 3 2 93 2 ((1, 1) :: repeat (1, 2) 192 ++ (66, 2) :: (1, 1) :: repeat (1, 2) 931 ++ (28468, 2) :: (1, 1) :: repeat (1, 2) 58213 ++ (1716045, 2) :: (1, 1) :: repeat (1, 2) 3474178 ++ (4901382, 2) :: (1, 1) :: repeat (1, 2) 29403094 ++ w) 1); closearith.
  }
  (* step 43: P TDN *)
  apply (hsteps_trans _ (HB [0] 3 1 4 ((91, 2) :: (1, 1) :: repeat (1, 2) 192 ++ (66, 2) :: (1, 1) :: repeat (1, 2) 931 ++ (28468, 2) :: (1, 1) :: repeat (1, 2) 58213 ++ (1716045, 2) :: (1, 1) :: repeat (1, 2) 3474178 ++ (4901382, 2) :: (1, 1) :: repeat (1, 2) 29403094 ++ w) 1)).
  {
    apply (sTDN [0] 3 ((91, 2) :: (1, 1) :: repeat (1, 2) 192 ++ (66, 2) :: (1, 1) :: repeat (1, 2) 931 ++ (28468, 2) :: (1, 1) :: repeat (1, 2) 58213 ++ (1716045, 2) :: (1, 1) :: repeat (1, 2) 3474178 ++ (4901382, 2) :: (1, 1) :: repeat (1, 2) 29403094 ++ w) 1).
  }
  (* step 44: sTUP *)
  apply (hsteps_trans _ (HC [0] 3 3 2 ((89, 2) :: (1, 1) :: repeat (1, 2) 192 ++ (66, 2) :: (1, 1) :: repeat (1, 2) 931 ++ (28468, 2) :: (1, 1) :: repeat (1, 2) 58213 ++ (1716045, 2) :: (1, 1) :: repeat (1, 2) 3474178 ++ (4901382, 2) :: (1, 1) :: repeat (1, 2) 29403094 ++ w) 1)).
  {
    replace ((89, 2) :: (1, 1) :: repeat (1, 2) 192 ++ (66, 2) :: (1, 1) :: repeat (1, 2) 931 ++ (28468, 2) :: (1, 1) :: repeat (1, 2) 58213 ++ (1716045, 2) :: (1, 1) :: repeat (1, 2) 3474178 ++ (4901382, 2) :: (1, 1) :: repeat (1, 2) 29403094 ++ w) with ((91 - 2, 2) :: (1, 1) :: repeat (1, 2) 192 ++ (66, 2) :: (1, 1) :: repeat (1, 2) 931 ++ (28468, 2) :: (1, 1) :: repeat (1, 2) 58213 ++ (1716045, 2) :: (1, 1) :: repeat (1, 2) 3474178 ++ (4901382, 2) :: (1, 1) :: repeat (1, 2) 29403094 ++ w) by sec_eq.
    apply (sTUP [0] 3 4 91 2 ((1, 1) :: repeat (1, 2) 192 ++ (66, 2) :: (1, 1) :: repeat (1, 2) 931 ++ (28468, 2) :: (1, 1) :: repeat (1, 2) 58213 ++ (1716045, 2) :: (1, 1) :: repeat (1, 2) 3474178 ++ (4901382, 2) :: (1, 1) :: repeat (1, 2) 29403094 ++ w) 1); closearith.
  }
  (* step 45: DIPGRIND 3 83 *)
  apply (hsteps_trans _ (HC [0] 0 3 2 (repeat (1, 2) 3 ++ (83, 2) :: (1, 1) :: repeat (1, 2) 192 ++ (66, 2) :: (1, 1) :: repeat (1, 2) 931 ++ (28468, 2) :: (1, 1) :: repeat (1, 2) 58213 ++ (1716045, 2) :: (1, 1) :: repeat (1, 2) 3474178 ++ (4901382, 2) :: (1, 1) :: repeat (1, 2) 29403094 ++ w) 1)).
  {
    apply (DIPGRIND 3 83 [0] ((1, 1) :: repeat (1, 2) 192 ++ (66, 2) :: (1, 1) :: repeat (1, 2) 931 ++ (28468, 2) :: (1, 1) :: repeat (1, 2) 58213 ++ (1716045, 2) :: (1, 1) :: repeat (1, 2) 3474178 ++ (4901382, 2) :: (1, 1) :: repeat (1, 2) 29403094 ++ w) 1); closearith.
  }
  (* step 46: P PX2B0 *)
  apply (hsteps_trans _ (HB [] 0 1 5 (repeat (1, 2) 4 ++ (83, 2) :: (1, 1) :: repeat (1, 2) 192 ++ (66, 2) :: (1, 1) :: repeat (1, 2) 931 ++ (28468, 2) :: (1, 1) :: repeat (1, 2) 58213 ++ (1716045, 2) :: (1, 1) :: repeat (1, 2) 3474178 ++ (4901382, 2) :: (1, 1) :: repeat (1, 2) 29403094 ++ w) 1)).
  {
    exact (hsteps_step _ _ _ (hPX2B0 (repeat (1, 2) 3 ++ (83, 2) :: (1, 1) :: repeat (1, 2) 192 ++ (66, 2) :: (1, 1) :: repeat (1, 2) 931 ++ (28468, 2) :: (1, 1) :: repeat (1, 2) 58213 ++ (1716045, 2) :: (1, 1) :: repeat (1, 2) 3474178 ++ (4901382, 2) :: (1, 1) :: repeat (1, 2) 29403094 ++ w) 1) (hsteps_refl _)).
  }
  (* step 47: M pop12 (4,) *)
  apply (hsteps_trans _ (HB [] 4 1 13 ((83, 2) :: (1, 1) :: repeat (1, 2) 192 ++ (66, 2) :: (1, 1) :: repeat (1, 2) 931 ++ (28468, 2) :: (1, 1) :: repeat (1, 2) 58213 ++ (1716045, 2) :: (1, 1) :: repeat (1, 2) 3474178 ++ (4901382, 2) :: (1, 1) :: repeat (1, 2) 29403094 ++ w) 1)).
  {
    apply (pop12 4 [] 0 5 ((83, 2) :: (1, 1) :: repeat (1, 2) 192 ++ (66, 2) :: (1, 1) :: repeat (1, 2) 931 ++ (28468, 2) :: (1, 1) :: repeat (1, 2) 58213 ++ (1716045, 2) :: (1, 1) :: repeat (1, 2) 3474178 ++ (4901382, 2) :: (1, 1) :: repeat (1, 2) 29403094 ++ w) 1); closearith.
  }
  (* step 48: sTUP *)
  apply (hsteps_trans _ (HC [] 4 12 2 ((81, 2) :: (1, 1) :: repeat (1, 2) 192 ++ (66, 2) :: (1, 1) :: repeat (1, 2) 931 ++ (28468, 2) :: (1, 1) :: repeat (1, 2) 58213 ++ (1716045, 2) :: (1, 1) :: repeat (1, 2) 3474178 ++ (4901382, 2) :: (1, 1) :: repeat (1, 2) 29403094 ++ w) 1)).
  {
    replace ((81, 2) :: (1, 1) :: repeat (1, 2) 192 ++ (66, 2) :: (1, 1) :: repeat (1, 2) 931 ++ (28468, 2) :: (1, 1) :: repeat (1, 2) 58213 ++ (1716045, 2) :: (1, 1) :: repeat (1, 2) 3474178 ++ (4901382, 2) :: (1, 1) :: repeat (1, 2) 29403094 ++ w) with ((83 - 2, 2) :: (1, 1) :: repeat (1, 2) 192 ++ (66, 2) :: (1, 1) :: repeat (1, 2) 931 ++ (28468, 2) :: (1, 1) :: repeat (1, 2) 58213 ++ (1716045, 2) :: (1, 1) :: repeat (1, 2) 3474178 ++ (4901382, 2) :: (1, 1) :: repeat (1, 2) 29403094 ++ w) by sec_eq.
    apply (sTUP [] 4 13 83 2 ((1, 1) :: repeat (1, 2) 192 ++ (66, 2) :: (1, 1) :: repeat (1, 2) 931 ++ (28468, 2) :: (1, 1) :: repeat (1, 2) 58213 ++ (1716045, 2) :: (1, 1) :: repeat (1, 2) 3474178 ++ (4901382, 2) :: (1, 1) :: repeat (1, 2) 29403094 ++ w) 1); closearith.
  }
  (* step 49: P PUSH *)
  apply (hsteps_trans _ (HC [] 3 1 2 ((10, 2) :: (81, 2) :: (1, 1) :: repeat (1, 2) 192 ++ (66, 2) :: (1, 1) :: repeat (1, 2) 931 ++ (28468, 2) :: (1, 1) :: repeat (1, 2) 58213 ++ (1716045, 2) :: (1, 1) :: repeat (1, 2) 3474178 ++ (4901382, 2) :: (1, 1) :: repeat (1, 2) 29403094 ++ w) 1)).
  {
    replace ((10, 2) :: (81, 2) :: (1, 1) :: repeat (1, 2) 192 ++ (66, 2) :: (1, 1) :: repeat (1, 2) 931 ++ (28468, 2) :: (1, 1) :: repeat (1, 2) 58213 ++ (1716045, 2) :: (1, 1) :: repeat (1, 2) 3474178 ++ (4901382, 2) :: (1, 1) :: repeat (1, 2) 29403094 ++ w) with ((12 - 2, 2) :: (81, 2) :: (1, 1) :: repeat (1, 2) 192 ++ (66, 2) :: (1, 1) :: repeat (1, 2) 931 ++ (28468, 2) :: (1, 1) :: repeat (1, 2) 58213 ++ (1716045, 2) :: (1, 1) :: repeat (1, 2) 3474178 ++ (4901382, 2) :: (1, 1) :: repeat (1, 2) 29403094 ++ w) by sec_eq.
    apply (sPUSH [] 3 12 ((81, 2) :: (1, 1) :: repeat (1, 2) 192 ++ (66, 2) :: (1, 1) :: repeat (1, 2) 931 ++ (28468, 2) :: (1, 1) :: repeat (1, 2) 58213 ++ (1716045, 2) :: (1, 1) :: repeat (1, 2) 3474178 ++ (4901382, 2) :: (1, 1) :: repeat (1, 2) 29403094 ++ w) 1); closearith.
  }
  (* step 50: P TDN *)
  apply (hsteps_trans _ (HB [] 3 1 4 ((10, 2) :: (81, 2) :: (1, 1) :: repeat (1, 2) 192 ++ (66, 2) :: (1, 1) :: repeat (1, 2) 931 ++ (28468, 2) :: (1, 1) :: repeat (1, 2) 58213 ++ (1716045, 2) :: (1, 1) :: repeat (1, 2) 3474178 ++ (4901382, 2) :: (1, 1) :: repeat (1, 2) 29403094 ++ w) 1)).
  {
    apply (sTDN [] 3 ((10, 2) :: (81, 2) :: (1, 1) :: repeat (1, 2) 192 ++ (66, 2) :: (1, 1) :: repeat (1, 2) 931 ++ (28468, 2) :: (1, 1) :: repeat (1, 2) 58213 ++ (1716045, 2) :: (1, 1) :: repeat (1, 2) 3474178 ++ (4901382, 2) :: (1, 1) :: repeat (1, 2) 29403094 ++ w) 1).
  }
  (* step 51: sTUP *)
  apply (hsteps_trans _ (HC [] 3 3 2 ((8, 2) :: (81, 2) :: (1, 1) :: repeat (1, 2) 192 ++ (66, 2) :: (1, 1) :: repeat (1, 2) 931 ++ (28468, 2) :: (1, 1) :: repeat (1, 2) 58213 ++ (1716045, 2) :: (1, 1) :: repeat (1, 2) 3474178 ++ (4901382, 2) :: (1, 1) :: repeat (1, 2) 29403094 ++ w) 1)).
  {
    replace ((8, 2) :: (81, 2) :: (1, 1) :: repeat (1, 2) 192 ++ (66, 2) :: (1, 1) :: repeat (1, 2) 931 ++ (28468, 2) :: (1, 1) :: repeat (1, 2) 58213 ++ (1716045, 2) :: (1, 1) :: repeat (1, 2) 3474178 ++ (4901382, 2) :: (1, 1) :: repeat (1, 2) 29403094 ++ w) with ((10 - 2, 2) :: (81, 2) :: (1, 1) :: repeat (1, 2) 192 ++ (66, 2) :: (1, 1) :: repeat (1, 2) 931 ++ (28468, 2) :: (1, 1) :: repeat (1, 2) 58213 ++ (1716045, 2) :: (1, 1) :: repeat (1, 2) 3474178 ++ (4901382, 2) :: (1, 1) :: repeat (1, 2) 29403094 ++ w) by sec_eq.
    apply (sTUP [] 3 4 10 2 ((81, 2) :: (1, 1) :: repeat (1, 2) 192 ++ (66, 2) :: (1, 1) :: repeat (1, 2) 931 ++ (28468, 2) :: (1, 1) :: repeat (1, 2) 58213 ++ (1716045, 2) :: (1, 1) :: repeat (1, 2) 3474178 ++ (4901382, 2) :: (1, 1) :: repeat (1, 2) 29403094 ++ w) 1); closearith.
  }
  (* step 52: DIPGRIND 3 2 *)
  apply (hsteps_trans _ (HC [] 0 3 2 (repeat (1, 2) 3 ++ (2, 2) :: (81, 2) :: (1, 1) :: repeat (1, 2) 192 ++ (66, 2) :: (1, 1) :: repeat (1, 2) 931 ++ (28468, 2) :: (1, 1) :: repeat (1, 2) 58213 ++ (1716045, 2) :: (1, 1) :: repeat (1, 2) 3474178 ++ (4901382, 2) :: (1, 1) :: repeat (1, 2) 29403094 ++ w) 1)).
  {
    apply (DIPGRIND 3 2 [] ((81, 2) :: (1, 1) :: repeat (1, 2) 192 ++ (66, 2) :: (1, 1) :: repeat (1, 2) 931 ++ (28468, 2) :: (1, 1) :: repeat (1, 2) 58213 ++ (1716045, 2) :: (1, 1) :: repeat (1, 2) 3474178 ++ (4901382, 2) :: (1, 1) :: repeat (1, 2) 29403094 ++ w) 1); closearith.
  }
  (* step 53: P PUSHX *)
  apply (hsteps_trans _ (HB [] 1 1 7 (repeat (1, 2) 3 ++ (2, 2) :: (81, 2) :: (1, 1) :: repeat (1, 2) 192 ++ (66, 2) :: (1, 1) :: repeat (1, 2) 931 ++ (28468, 2) :: (1, 1) :: repeat (1, 2) 58213 ++ (1716045, 2) :: (1, 1) :: repeat (1, 2) 3474178 ++ (4901382, 2) :: (1, 1) :: repeat (1, 2) 29403094 ++ w) 1)).
  {
    exact (hsteps_step _ _ _ (hPUSHX (repeat (1, 2) 3 ++ (2, 2) :: (81, 2) :: (1, 1) :: repeat (1, 2) 192 ++ (66, 2) :: (1, 1) :: repeat (1, 2) 931 ++ (28468, 2) :: (1, 1) :: repeat (1, 2) 58213 ++ (1716045, 2) :: (1, 1) :: repeat (1, 2) 3474178 ++ (4901382, 2) :: (1, 1) :: repeat (1, 2) 29403094 ++ w) 1) (hsteps_refl _)).
  }
  (* step 54: M pop12 (3,) *)
  apply (hsteps_trans _ (HB [] 4 1 13 ((2, 2) :: (81, 2) :: (1, 1) :: repeat (1, 2) 192 ++ (66, 2) :: (1, 1) :: repeat (1, 2) 931 ++ (28468, 2) :: (1, 1) :: repeat (1, 2) 58213 ++ (1716045, 2) :: (1, 1) :: repeat (1, 2) 3474178 ++ (4901382, 2) :: (1, 1) :: repeat (1, 2) 29403094 ++ w) 1)).
  {
    apply (pop12 3 [] 1 7 ((2, 2) :: (81, 2) :: (1, 1) :: repeat (1, 2) 192 ++ (66, 2) :: (1, 1) :: repeat (1, 2) 931 ++ (28468, 2) :: (1, 1) :: repeat (1, 2) 58213 ++ (1716045, 2) :: (1, 1) :: repeat (1, 2) 3474178 ++ (4901382, 2) :: (1, 1) :: repeat (1, 2) 29403094 ++ w) 1); closearith.
  }
  (* step 55: P TUP2_1 *)
  apply (hsteps_trans _ (HC [5] 13 1 2 ((79, 2) :: (1, 1) :: repeat (1, 2) 192 ++ (66, 2) :: (1, 1) :: repeat (1, 2) 931 ++ (28468, 2) :: (1, 1) :: repeat (1, 2) 58213 ++ (1716045, 2) :: (1, 1) :: repeat (1, 2) 3474178 ++ (4901382, 2) :: (1, 1) :: repeat (1, 2) 29403094 ++ w) 1)).
  {
    replace ((79, 2) :: (1, 1) :: repeat (1, 2) 192 ++ (66, 2) :: (1, 1) :: repeat (1, 2) 931 ++ (28468, 2) :: (1, 1) :: repeat (1, 2) 58213 ++ (1716045, 2) :: (1, 1) :: repeat (1, 2) 3474178 ++ (4901382, 2) :: (1, 1) :: repeat (1, 2) 29403094 ++ w) with ((81 - 2, 2) :: (1, 1) :: repeat (1, 2) 192 ++ (66, 2) :: (1, 1) :: repeat (1, 2) 931 ++ (28468, 2) :: (1, 1) :: repeat (1, 2) 58213 ++ (1716045, 2) :: (1, 1) :: repeat (1, 2) 3474178 ++ (4901382, 2) :: (1, 1) :: repeat (1, 2) 29403094 ++ w) by sec_eq.
    apply (sTUP2_1 [] 4 12 81 ((1, 1) :: repeat (1, 2) 192 ++ (66, 2) :: (1, 1) :: repeat (1, 2) 931 ++ (28468, 2) :: (1, 1) :: repeat (1, 2) 58213 ++ (1716045, 2) :: (1, 1) :: repeat (1, 2) 3474178 ++ (4901382, 2) :: (1, 1) :: repeat (1, 2) 29403094 ++ w) 1); closearith.
  }
  (* step 56: P TDN *)
  apply (hsteps_trans _ (HB [5] 13 1 4 ((79, 2) :: (1, 1) :: repeat (1, 2) 192 ++ (66, 2) :: (1, 1) :: repeat (1, 2) 931 ++ (28468, 2) :: (1, 1) :: repeat (1, 2) 58213 ++ (1716045, 2) :: (1, 1) :: repeat (1, 2) 3474178 ++ (4901382, 2) :: (1, 1) :: repeat (1, 2) 29403094 ++ w) 1)).
  {
    apply (sTDN [5] 13 ((79, 2) :: (1, 1) :: repeat (1, 2) 192 ++ (66, 2) :: (1, 1) :: repeat (1, 2) 931 ++ (28468, 2) :: (1, 1) :: repeat (1, 2) 58213 ++ (1716045, 2) :: (1, 1) :: repeat (1, 2) 3474178 ++ (4901382, 2) :: (1, 1) :: repeat (1, 2) 29403094 ++ w) 1).
  }
  (* step 57: sTUP *)
  apply (hsteps_trans _ (HC [5] 13 3 2 ((77, 2) :: (1, 1) :: repeat (1, 2) 192 ++ (66, 2) :: (1, 1) :: repeat (1, 2) 931 ++ (28468, 2) :: (1, 1) :: repeat (1, 2) 58213 ++ (1716045, 2) :: (1, 1) :: repeat (1, 2) 3474178 ++ (4901382, 2) :: (1, 1) :: repeat (1, 2) 29403094 ++ w) 1)).
  {
    replace ((77, 2) :: (1, 1) :: repeat (1, 2) 192 ++ (66, 2) :: (1, 1) :: repeat (1, 2) 931 ++ (28468, 2) :: (1, 1) :: repeat (1, 2) 58213 ++ (1716045, 2) :: (1, 1) :: repeat (1, 2) 3474178 ++ (4901382, 2) :: (1, 1) :: repeat (1, 2) 29403094 ++ w) with ((79 - 2, 2) :: (1, 1) :: repeat (1, 2) 192 ++ (66, 2) :: (1, 1) :: repeat (1, 2) 931 ++ (28468, 2) :: (1, 1) :: repeat (1, 2) 58213 ++ (1716045, 2) :: (1, 1) :: repeat (1, 2) 3474178 ++ (4901382, 2) :: (1, 1) :: repeat (1, 2) 29403094 ++ w) by sec_eq.
    apply (sTUP [5] 13 4 79 2 ((1, 1) :: repeat (1, 2) 192 ++ (66, 2) :: (1, 1) :: repeat (1, 2) 931 ++ (28468, 2) :: (1, 1) :: repeat (1, 2) 58213 ++ (1716045, 2) :: (1, 1) :: repeat (1, 2) 3474178 ++ (4901382, 2) :: (1, 1) :: repeat (1, 2) 29403094 ++ w) 1); closearith.
  }
  (* step 58: DIPGRIND 13 51 *)
  apply (hsteps_trans _ (HC [5] 0 3 2 (repeat (1, 2) 13 ++ (51, 2) :: (1, 1) :: repeat (1, 2) 192 ++ (66, 2) :: (1, 1) :: repeat (1, 2) 931 ++ (28468, 2) :: (1, 1) :: repeat (1, 2) 58213 ++ (1716045, 2) :: (1, 1) :: repeat (1, 2) 3474178 ++ (4901382, 2) :: (1, 1) :: repeat (1, 2) 29403094 ++ w) 1)).
  {
    apply (DIPGRIND 13 51 [5] ((1, 1) :: repeat (1, 2) 192 ++ (66, 2) :: (1, 1) :: repeat (1, 2) 931 ++ (28468, 2) :: (1, 1) :: repeat (1, 2) 58213 ++ (1716045, 2) :: (1, 1) :: repeat (1, 2) 3474178 ++ (4901382, 2) :: (1, 1) :: repeat (1, 2) 29403094 ++ w) 1); closearith.
  }
  (* step 59: P PX2Bgen *)
  apply (hsteps_trans _ (HB [0] 3 1 2 (repeat (1, 2) 1 ++ (1, 1) :: repeat (1, 2) 15 ++ (51, 2) :: (1, 1) :: repeat (1, 2) 192 ++ (66, 2) :: (1, 1) :: repeat (1, 2) 931 ++ (28468, 2) :: (1, 1) :: repeat (1, 2) 58213 ++ (1716045, 2) :: (1, 1) :: repeat (1, 2) 3474178 ++ (4901382, 2) :: (1, 1) :: repeat (1, 2) 29403094 ++ w) 1)).
  {
    exact (hsteps_step _ _ _ (hPX2Bgen 0 (repeat (1, 2) 13 ++ (51, 2) :: (1, 1) :: repeat (1, 2) 192 ++ (66, 2) :: (1, 1) :: repeat (1, 2) 931 ++ (28468, 2) :: (1, 1) :: repeat (1, 2) 58213 ++ (1716045, 2) :: (1, 1) :: repeat (1, 2) 3474178 ++ (4901382, 2) :: (1, 1) :: repeat (1, 2) 29403094 ++ w) 1) (hsteps_refl _)).
  }
  (* step 60: M pop12 (1,) *)
  apply (hsteps_trans _ (HB [0] 4 1 4 ((1, 1) :: repeat (1, 2) 15 ++ (51, 2) :: (1, 1) :: repeat (1, 2) 192 ++ (66, 2) :: (1, 1) :: repeat (1, 2) 931 ++ (28468, 2) :: (1, 1) :: repeat (1, 2) 58213 ++ (1716045, 2) :: (1, 1) :: repeat (1, 2) 3474178 ++ (4901382, 2) :: (1, 1) :: repeat (1, 2) 29403094 ++ w) 1)).
  {
    apply (pop12 1 [0] 3 2 ((1, 1) :: repeat (1, 2) 15 ++ (51, 2) :: (1, 1) :: repeat (1, 2) 192 ++ (66, 2) :: (1, 1) :: repeat (1, 2) 931 ++ (28468, 2) :: (1, 1) :: repeat (1, 2) 58213 ++ (1716045, 2) :: (1, 1) :: repeat (1, 2) 3474178 ++ (4901382, 2) :: (1, 1) :: repeat (1, 2) 29403094 ++ w) 1); closearith.
  }
  (* step 61: P POP *)
  apply (hsteps_trans _ (HB [0] 5 1 5 (repeat (1, 2) 15 ++ (51, 2) :: (1, 1) :: repeat (1, 2) 192 ++ (66, 2) :: (1, 1) :: repeat (1, 2) 931 ++ (28468, 2) :: (1, 1) :: repeat (1, 2) 58213 ++ (1716045, 2) :: (1, 1) :: repeat (1, 2) 3474178 ++ (4901382, 2) :: (1, 1) :: repeat (1, 2) 29403094 ++ w) 1)).
  {
    apply (sPOP1 [0] 4 4 (repeat (1, 2) 15 ++ (51, 2) :: (1, 1) :: repeat (1, 2) 192 ++ (66, 2) :: (1, 1) :: repeat (1, 2) 931 ++ (28468, 2) :: (1, 1) :: repeat (1, 2) 58213 ++ (1716045, 2) :: (1, 1) :: repeat (1, 2) 3474178 ++ (4901382, 2) :: (1, 1) :: repeat (1, 2) 29403094 ++ w) 1); closearith.
  }
  (* step 62: M pop12 (15,) *)
  apply (hsteps_trans _ (HB [0] 20 1 35 ((51, 2) :: (1, 1) :: repeat (1, 2) 192 ++ (66, 2) :: (1, 1) :: repeat (1, 2) 931 ++ (28468, 2) :: (1, 1) :: repeat (1, 2) 58213 ++ (1716045, 2) :: (1, 1) :: repeat (1, 2) 3474178 ++ (4901382, 2) :: (1, 1) :: repeat (1, 2) 29403094 ++ w) 1)).
  {
    apply (pop12 15 [0] 5 5 ((51, 2) :: (1, 1) :: repeat (1, 2) 192 ++ (66, 2) :: (1, 1) :: repeat (1, 2) 931 ++ (28468, 2) :: (1, 1) :: repeat (1, 2) 58213 ++ (1716045, 2) :: (1, 1) :: repeat (1, 2) 3474178 ++ (4901382, 2) :: (1, 1) :: repeat (1, 2) 29403094 ++ w) 1); closearith.
  }
  (* step 63: sTUP *)
  apply (hsteps_trans _ (HC [0] 20 34 2 ((49, 2) :: (1, 1) :: repeat (1, 2) 192 ++ (66, 2) :: (1, 1) :: repeat (1, 2) 931 ++ (28468, 2) :: (1, 1) :: repeat (1, 2) 58213 ++ (1716045, 2) :: (1, 1) :: repeat (1, 2) 3474178 ++ (4901382, 2) :: (1, 1) :: repeat (1, 2) 29403094 ++ w) 1)).
  {
    replace ((49, 2) :: (1, 1) :: repeat (1, 2) 192 ++ (66, 2) :: (1, 1) :: repeat (1, 2) 931 ++ (28468, 2) :: (1, 1) :: repeat (1, 2) 58213 ++ (1716045, 2) :: (1, 1) :: repeat (1, 2) 3474178 ++ (4901382, 2) :: (1, 1) :: repeat (1, 2) 29403094 ++ w) with ((51 - 2, 2) :: (1, 1) :: repeat (1, 2) 192 ++ (66, 2) :: (1, 1) :: repeat (1, 2) 931 ++ (28468, 2) :: (1, 1) :: repeat (1, 2) 58213 ++ (1716045, 2) :: (1, 1) :: repeat (1, 2) 3474178 ++ (4901382, 2) :: (1, 1) :: repeat (1, 2) 29403094 ++ w) by sec_eq.
    apply (sTUP [0] 20 35 51 2 ((1, 1) :: repeat (1, 2) 192 ++ (66, 2) :: (1, 1) :: repeat (1, 2) 931 ++ (28468, 2) :: (1, 1) :: repeat (1, 2) 58213 ++ (1716045, 2) :: (1, 1) :: repeat (1, 2) 3474178 ++ (4901382, 2) :: (1, 1) :: repeat (1, 2) 29403094 ++ w) 1); closearith.
  }
  (* step 64: hGRIND_even 15 *)
  apply (hsteps_trans _ (HB [0] 19 1 34 ((2, 2) :: (49, 2) :: (1, 1) :: repeat (1, 2) 192 ++ (66, 2) :: (1, 1) :: repeat (1, 2) 931 ++ (28468, 2) :: (1, 1) :: repeat (1, 2) 58213 ++ (1716045, 2) :: (1, 1) :: repeat (1, 2) 3474178 ++ (4901382, 2) :: (1, 1) :: repeat (1, 2) 29403094 ++ w) 1)).
  {
    apply (hGRIND_even 15 [0] 19 ((49, 2) :: (1, 1) :: repeat (1, 2) 192 ++ (66, 2) :: (1, 1) :: repeat (1, 2) 931 ++ (28468, 2) :: (1, 1) :: repeat (1, 2) 58213 ++ (1716045, 2) :: (1, 1) :: repeat (1, 2) 3474178 ++ (4901382, 2) :: (1, 1) :: repeat (1, 2) 29403094 ++ w) 1); closearith.
  }
  (* step 65: P TUP2_1 *)
  replace ((47, 2) :: (1, 1) :: repeat (1, 2) 192 ++ (66, 2) :: (1, 1) :: repeat (1, 2) 931 ++ (28468, 2) :: (1, 1) :: repeat (1, 2) 58213 ++ (1716045, 2) :: (1, 1) :: repeat (1, 2) 3474178 ++ (4901382, 2) :: (1, 1) :: repeat (1, 2) 29403094 ++ w) with ((49 - 2, 2) :: (1, 1) :: repeat (1, 2) 192 ++ (66, 2) :: (1, 1) :: repeat (1, 2) 931 ++ (28468, 2) :: (1, 1) :: repeat (1, 2) 58213 ++ (1716045, 2) :: (1, 1) :: repeat (1, 2) 3474178 ++ (4901382, 2) :: (1, 1) :: repeat (1, 2) 29403094 ++ w) by sec_eq.
  apply (sTUP2_1 [0] 19 33 49 ((1, 1) :: repeat (1, 2) 192 ++ (66, 2) :: (1, 1) :: repeat (1, 2) 931 ++ (28468, 2) :: (1, 1) :: repeat (1, 2) 58213 ++ (1716045, 2) :: (1, 1) :: repeat (1, 2) 3474178 ++ (4901382, 2) :: (1, 1) :: repeat (1, 2) 29403094 ++ w) 1); closearith.
Qed.

(* CASCADE59d: steps 66-121 of the CASCADE59 chain. *)
Lemma CASCADE59d : forall w,
  hsteps (HC [20; 0] 34 1 2 ((47, 2) :: (1, 1) :: repeat (1, 2) 192 ++ (66, 2) :: (1, 1) :: repeat (1, 2) 931 ++ (28468, 2) :: (1, 1) :: repeat (1, 2) 58213 ++ (1716045, 2) :: (1, 1) :: repeat (1, 2) 3474178 ++ (4901382, 2) :: (1, 1) :: repeat (1, 2) 29403094 ++ w) 1)
         (HB [] 1 1 7 (repeat (1, 2) 3 ++ (2, 2) :: (4, 2) :: (1, 1) :: repeat (1, 2) 45 ++ (94, 2) :: (1, 1) :: repeat (1, 2) 437 ++ (120, 2) :: (1, 1) :: repeat (1, 2) 1866 ++ (24734, 2) :: (1, 1) :: repeat (1, 2) 58213 ++ (1716045, 2) :: (1, 1) :: repeat (1, 2) 3474178 ++ (4901382, 2) :: (1, 1) :: repeat (1, 2) 29403094 ++ w) 1).
Proof.
  intro w.
  (* step 66: P TDN *)
  apply (hsteps_trans _ (HB [20; 0] 34 1 4 ((47, 2) :: (1, 1) :: repeat (1, 2) 192 ++ (66, 2) :: (1, 1) :: repeat (1, 2) 931 ++ (28468, 2) :: (1, 1) :: repeat (1, 2) 58213 ++ (1716045, 2) :: (1, 1) :: repeat (1, 2) 3474178 ++ (4901382, 2) :: (1, 1) :: repeat (1, 2) 29403094 ++ w) 1)).
  {
    apply (sTDN [20; 0] 34 ((47, 2) :: (1, 1) :: repeat (1, 2) 192 ++ (66, 2) :: (1, 1) :: repeat (1, 2) 931 ++ (28468, 2) :: (1, 1) :: repeat (1, 2) 58213 ++ (1716045, 2) :: (1, 1) :: repeat (1, 2) 3474178 ++ (4901382, 2) :: (1, 1) :: repeat (1, 2) 29403094 ++ w) 1).
  }
  (* step 67: sTUP *)
  apply (hsteps_trans _ (HC [20; 0] 34 3 2 ((45, 2) :: (1, 1) :: repeat (1, 2) 192 ++ (66, 2) :: (1, 1) :: repeat (1, 2) 931 ++ (28468, 2) :: (1, 1) :: repeat (1, 2) 58213 ++ (1716045, 2) :: (1, 1) :: repeat (1, 2) 3474178 ++ (4901382, 2) :: (1, 1) :: repeat (1, 2) 29403094 ++ w) 1)).
  {
    replace ((45, 2) :: (1, 1) :: repeat (1, 2) 192 ++ (66, 2) :: (1, 1) :: repeat (1, 2) 931 ++ (28468, 2) :: (1, 1) :: repeat (1, 2) 58213 ++ (1716045, 2) :: (1, 1) :: repeat (1, 2) 3474178 ++ (4901382, 2) :: (1, 1) :: repeat (1, 2) 29403094 ++ w) with ((47 - 2, 2) :: (1, 1) :: repeat (1, 2) 192 ++ (66, 2) :: (1, 1) :: repeat (1, 2) 931 ++ (28468, 2) :: (1, 1) :: repeat (1, 2) 58213 ++ (1716045, 2) :: (1, 1) :: repeat (1, 2) 3474178 ++ (4901382, 2) :: (1, 1) :: repeat (1, 2) 29403094 ++ w) by sec_eq.
    apply (sTUP [20; 0] 34 4 47 2 ((1, 1) :: repeat (1, 2) 192 ++ (66, 2) :: (1, 1) :: repeat (1, 2) 931 ++ (28468, 2) :: (1, 1) :: repeat (1, 2) 58213 ++ (1716045, 2) :: (1, 1) :: repeat (1, 2) 3474178 ++ (4901382, 2) :: (1, 1) :: repeat (1, 2) 29403094 ++ w) 1); closearith.
  }
  (* step 68: CLEANG_odd 21 *)
  apply (hsteps_trans _ (HB [20; 0] 34 1 50 (repeat (1, 2) 1 ++ (1, 1) :: repeat (1, 2) 192 ++ (66, 2) :: (1, 1) :: repeat (1, 2) 931 ++ (28468, 2) :: (1, 1) :: repeat (1, 2) 58213 ++ (1716045, 2) :: (1, 1) :: repeat (1, 2) 3474178 ++ (4901382, 2) :: (1, 1) :: repeat (1, 2) 29403094 ++ w) 1)).
  {
    replace (repeat (1, 2) 1 ++ (1, 1) :: repeat (1, 2) 192 ++ (66, 2) :: (1, 1) :: repeat (1, 2) 931 ++ (28468, 2) :: (1, 1) :: repeat (1, 2) 58213 ++ (1716045, 2) :: (1, 1) :: repeat (1, 2) 3474178 ++ (4901382, 2) :: (1, 1) :: repeat (1, 2) 29403094 ++ w) with ((1, 2) :: (1, 1) :: repeat (1, 2) 192 ++ (66, 2) :: (1, 1) :: repeat (1, 2) 931 ++ (28468, 2) :: (1, 1) :: repeat (1, 2) 58213 ++ (1716045, 2) :: (1, 1) :: repeat (1, 2) 3474178 ++ (4901382, 2) :: (1, 1) :: repeat (1, 2) 29403094 ++ w) by sec_eq.
    apply (CLEANG_odd 21 [20; 0] 34 ((1, 1) :: repeat (1, 2) 192 ++ (66, 2) :: (1, 1) :: repeat (1, 2) 931 ++ (28468, 2) :: (1, 1) :: repeat (1, 2) 58213 ++ (1716045, 2) :: (1, 1) :: repeat (1, 2) 3474178 ++ (4901382, 2) :: (1, 1) :: repeat (1, 2) 29403094 ++ w) 1); closearith.
  }
  (* step 69: M pop12 (1,) *)
  apply (hsteps_trans _ (HB [20; 0] 35 1 52 ((1, 1) :: repeat (1, 2) 192 ++ (66, 2) :: (1, 1) :: repeat (1, 2) 931 ++ (28468, 2) :: (1, 1) :: repeat (1, 2) 58213 ++ (1716045, 2) :: (1, 1) :: repeat (1, 2) 3474178 ++ (4901382, 2) :: (1, 1) :: repeat (1, 2) 29403094 ++ w) 1)).
  {
    apply (pop12 1 [20; 0] 34 50 ((1, 1) :: repeat (1, 2) 192 ++ (66, 2) :: (1, 1) :: repeat (1, 2) 931 ++ (28468, 2) :: (1, 1) :: repeat (1, 2) 58213 ++ (1716045, 2) :: (1, 1) :: repeat (1, 2) 3474178 ++ (4901382, 2) :: (1, 1) :: repeat (1, 2) 29403094 ++ w) 1); closearith.
  }
  (* step 70: P POP *)
  apply (hsteps_trans _ (HB [20; 0] 36 1 53 (repeat (1, 2) 192 ++ (66, 2) :: (1, 1) :: repeat (1, 2) 931 ++ (28468, 2) :: (1, 1) :: repeat (1, 2) 58213 ++ (1716045, 2) :: (1, 1) :: repeat (1, 2) 3474178 ++ (4901382, 2) :: (1, 1) :: repeat (1, 2) 29403094 ++ w) 1)).
  {
    apply (sPOP1 [20; 0] 35 52 (repeat (1, 2) 192 ++ (66, 2) :: (1, 1) :: repeat (1, 2) 931 ++ (28468, 2) :: (1, 1) :: repeat (1, 2) 58213 ++ (1716045, 2) :: (1, 1) :: repeat (1, 2) 3474178 ++ (4901382, 2) :: (1, 1) :: repeat (1, 2) 29403094 ++ w) 1); closearith.
  }
  (* step 71: M pop12 (192,) *)
  apply (hsteps_trans _ (HB [20; 0] 228 1 437 ((66, 2) :: (1, 1) :: repeat (1, 2) 931 ++ (28468, 2) :: (1, 1) :: repeat (1, 2) 58213 ++ (1716045, 2) :: (1, 1) :: repeat (1, 2) 3474178 ++ (4901382, 2) :: (1, 1) :: repeat (1, 2) 29403094 ++ w) 1)).
  {
    apply (pop12 192 [20; 0] 36 53 ((66, 2) :: (1, 1) :: repeat (1, 2) 931 ++ (28468, 2) :: (1, 1) :: repeat (1, 2) 58213 ++ (1716045, 2) :: (1, 1) :: repeat (1, 2) 3474178 ++ (4901382, 2) :: (1, 1) :: repeat (1, 2) 29403094 ++ w) 1); closearith.
  }
  (* step 72: sTUP *)
  apply (hsteps_trans _ (HC [20; 0] 228 436 2 ((64, 2) :: (1, 1) :: repeat (1, 2) 931 ++ (28468, 2) :: (1, 1) :: repeat (1, 2) 58213 ++ (1716045, 2) :: (1, 1) :: repeat (1, 2) 3474178 ++ (4901382, 2) :: (1, 1) :: repeat (1, 2) 29403094 ++ w) 1)).
  {
    replace ((64, 2) :: (1, 1) :: repeat (1, 2) 931 ++ (28468, 2) :: (1, 1) :: repeat (1, 2) 58213 ++ (1716045, 2) :: (1, 1) :: repeat (1, 2) 3474178 ++ (4901382, 2) :: (1, 1) :: repeat (1, 2) 29403094 ++ w) with ((66 - 2, 2) :: (1, 1) :: repeat (1, 2) 931 ++ (28468, 2) :: (1, 1) :: repeat (1, 2) 58213 ++ (1716045, 2) :: (1, 1) :: repeat (1, 2) 3474178 ++ (4901382, 2) :: (1, 1) :: repeat (1, 2) 29403094 ++ w) by sec_eq.
    apply (sTUP [20; 0] 228 437 66 2 ((1, 1) :: repeat (1, 2) 931 ++ (28468, 2) :: (1, 1) :: repeat (1, 2) 58213 ++ (1716045, 2) :: (1, 1) :: repeat (1, 2) 3474178 ++ (4901382, 2) :: (1, 1) :: repeat (1, 2) 29403094 ++ w) 1); closearith.
  }
  (* step 73: hGRIND_even 216 *)
  apply (hsteps_trans _ (HB [20; 0] 227 1 436 ((2, 2) :: (64, 2) :: (1, 1) :: repeat (1, 2) 931 ++ (28468, 2) :: (1, 1) :: repeat (1, 2) 58213 ++ (1716045, 2) :: (1, 1) :: repeat (1, 2) 3474178 ++ (4901382, 2) :: (1, 1) :: repeat (1, 2) 29403094 ++ w) 1)).
  {
    apply (hGRIND_even 216 [20; 0] 227 ((64, 2) :: (1, 1) :: repeat (1, 2) 931 ++ (28468, 2) :: (1, 1) :: repeat (1, 2) 58213 ++ (1716045, 2) :: (1, 1) :: repeat (1, 2) 3474178 ++ (4901382, 2) :: (1, 1) :: repeat (1, 2) 29403094 ++ w) 1); closearith.
  }
  (* step 74: P TUP2_1 *)
  apply (hsteps_trans _ (HC [228; 20; 0] 436 1 2 ((62, 2) :: (1, 1) :: repeat (1, 2) 931 ++ (28468, 2) :: (1, 1) :: repeat (1, 2) 58213 ++ (1716045, 2) :: (1, 1) :: repeat (1, 2) 3474178 ++ (4901382, 2) :: (1, 1) :: repeat (1, 2) 29403094 ++ w) 1)).
  {
    replace ((62, 2) :: (1, 1) :: repeat (1, 2) 931 ++ (28468, 2) :: (1, 1) :: repeat (1, 2) 58213 ++ (1716045, 2) :: (1, 1) :: repeat (1, 2) 3474178 ++ (4901382, 2) :: (1, 1) :: repeat (1, 2) 29403094 ++ w) with ((64 - 2, 2) :: (1, 1) :: repeat (1, 2) 931 ++ (28468, 2) :: (1, 1) :: repeat (1, 2) 58213 ++ (1716045, 2) :: (1, 1) :: repeat (1, 2) 3474178 ++ (4901382, 2) :: (1, 1) :: repeat (1, 2) 29403094 ++ w) by sec_eq.
    apply (sTUP2_1 [20; 0] 227 435 64 ((1, 1) :: repeat (1, 2) 931 ++ (28468, 2) :: (1, 1) :: repeat (1, 2) 58213 ++ (1716045, 2) :: (1, 1) :: repeat (1, 2) 3474178 ++ (4901382, 2) :: (1, 1) :: repeat (1, 2) 29403094 ++ w) 1); closearith.
  }
  (* step 75: P TDN *)
  apply (hsteps_trans _ (HB [228; 20; 0] 436 1 4 ((62, 2) :: (1, 1) :: repeat (1, 2) 931 ++ (28468, 2) :: (1, 1) :: repeat (1, 2) 58213 ++ (1716045, 2) :: (1, 1) :: repeat (1, 2) 3474178 ++ (4901382, 2) :: (1, 1) :: repeat (1, 2) 29403094 ++ w) 1)).
  {
    apply (sTDN [228; 20; 0] 436 ((62, 2) :: (1, 1) :: repeat (1, 2) 931 ++ (28468, 2) :: (1, 1) :: repeat (1, 2) 58213 ++ (1716045, 2) :: (1, 1) :: repeat (1, 2) 3474178 ++ (4901382, 2) :: (1, 1) :: repeat (1, 2) 29403094 ++ w) 1).
  }
  (* step 76: sTUP *)
  apply (hsteps_trans _ (HC [228; 20; 0] 436 3 2 ((60, 2) :: (1, 1) :: repeat (1, 2) 931 ++ (28468, 2) :: (1, 1) :: repeat (1, 2) 58213 ++ (1716045, 2) :: (1, 1) :: repeat (1, 2) 3474178 ++ (4901382, 2) :: (1, 1) :: repeat (1, 2) 29403094 ++ w) 1)).
  {
    replace ((60, 2) :: (1, 1) :: repeat (1, 2) 931 ++ (28468, 2) :: (1, 1) :: repeat (1, 2) 58213 ++ (1716045, 2) :: (1, 1) :: repeat (1, 2) 3474178 ++ (4901382, 2) :: (1, 1) :: repeat (1, 2) 29403094 ++ w) with ((62 - 2, 2) :: (1, 1) :: repeat (1, 2) 931 ++ (28468, 2) :: (1, 1) :: repeat (1, 2) 58213 ++ (1716045, 2) :: (1, 1) :: repeat (1, 2) 3474178 ++ (4901382, 2) :: (1, 1) :: repeat (1, 2) 29403094 ++ w) by sec_eq.
    apply (sTUP [228; 20; 0] 436 4 62 2 ((1, 1) :: repeat (1, 2) 931 ++ (28468, 2) :: (1, 1) :: repeat (1, 2) 58213 ++ (1716045, 2) :: (1, 1) :: repeat (1, 2) 3474178 ++ (4901382, 2) :: (1, 1) :: repeat (1, 2) 29403094 ++ w) 1); closearith.
  }
  (* step 77: CLEANG_even 29 *)
  apply (hsteps_trans _ (HB [228; 20; 0] 436 1 64 ((2, 2) :: (1, 1) :: repeat (1, 2) 931 ++ (28468, 2) :: (1, 1) :: repeat (1, 2) 58213 ++ (1716045, 2) :: (1, 1) :: repeat (1, 2) 3474178 ++ (4901382, 2) :: (1, 1) :: repeat (1, 2) 29403094 ++ w) 1)).
  {
    apply (CLEANG_even 29 [228; 20; 0] 436 ((1, 1) :: repeat (1, 2) 931 ++ (28468, 2) :: (1, 1) :: repeat (1, 2) 58213 ++ (1716045, 2) :: (1, 1) :: repeat (1, 2) 3474178 ++ (4901382, 2) :: (1, 1) :: repeat (1, 2) 29403094 ++ w) 1); closearith.
  }
  (* step 78: P TRANS2_1 *)
  apply (hsteps_trans _ (HB [437; 228; 20; 0] 65 1 3 (repeat (1, 2) 931 ++ (28468, 2) :: (1, 1) :: repeat (1, 2) 58213 ++ (1716045, 2) :: (1, 1) :: repeat (1, 2) 3474178 ++ (4901382, 2) :: (1, 1) :: repeat (1, 2) 29403094 ++ w) 1)).
  {
    apply (sTRANS2_1 [228; 20; 0] 436 63 1 (repeat (1, 2) 931 ++ (28468, 2) :: (1, 1) :: repeat (1, 2) 58213 ++ (1716045, 2) :: (1, 1) :: repeat (1, 2) 3474178 ++ (4901382, 2) :: (1, 1) :: repeat (1, 2) 29403094 ++ w) 1); closearith.
  }
  (* step 79: M pop12 (931,) *)
  apply (hsteps_trans _ (HB [437; 228; 20; 0] 996 1 1865 ((28468, 2) :: (1, 1) :: repeat (1, 2) 58213 ++ (1716045, 2) :: (1, 1) :: repeat (1, 2) 3474178 ++ (4901382, 2) :: (1, 1) :: repeat (1, 2) 29403094 ++ w) 1)).
  {
    apply (pop12 931 [437; 228; 20; 0] 65 3 ((28468, 2) :: (1, 1) :: repeat (1, 2) 58213 ++ (1716045, 2) :: (1, 1) :: repeat (1, 2) 3474178 ++ (4901382, 2) :: (1, 1) :: repeat (1, 2) 29403094 ++ w) 1); closearith.
  }
  (* step 80: sTUP *)
  apply (hsteps_trans _ (HC [437; 228; 20; 0] 996 1864 2 ((28466, 2) :: (1, 1) :: repeat (1, 2) 58213 ++ (1716045, 2) :: (1, 1) :: repeat (1, 2) 3474178 ++ (4901382, 2) :: (1, 1) :: repeat (1, 2) 29403094 ++ w) 1)).
  {
    replace ((28466, 2) :: (1, 1) :: repeat (1, 2) 58213 ++ (1716045, 2) :: (1, 1) :: repeat (1, 2) 3474178 ++ (4901382, 2) :: (1, 1) :: repeat (1, 2) 29403094 ++ w) with ((28468 - 2, 2) :: (1, 1) :: repeat (1, 2) 58213 ++ (1716045, 2) :: (1, 1) :: repeat (1, 2) 3474178 ++ (4901382, 2) :: (1, 1) :: repeat (1, 2) 29403094 ++ w) by sec_eq.
    apply (sTUP [437; 228; 20; 0] 996 1865 28468 2 ((1, 1) :: repeat (1, 2) 58213 ++ (1716045, 2) :: (1, 1) :: repeat (1, 2) 3474178 ++ (4901382, 2) :: (1, 1) :: repeat (1, 2) 29403094 ++ w) 1); closearith.
  }
  (* step 81: hGRIND_even 930 *)
  apply (hsteps_trans _ (HB [437; 228; 20; 0] 995 1 1864 ((2, 2) :: (28466, 2) :: (1, 1) :: repeat (1, 2) 58213 ++ (1716045, 2) :: (1, 1) :: repeat (1, 2) 3474178 ++ (4901382, 2) :: (1, 1) :: repeat (1, 2) 29403094 ++ w) 1)).
  {
    apply (hGRIND_even 930 [437; 228; 20; 0] 995 ((28466, 2) :: (1, 1) :: repeat (1, 2) 58213 ++ (1716045, 2) :: (1, 1) :: repeat (1, 2) 3474178 ++ (4901382, 2) :: (1, 1) :: repeat (1, 2) 29403094 ++ w) 1); closearith.
  }
  (* step 82: P TUP2_1 *)
  apply (hsteps_trans _ (HC [996; 437; 228; 20; 0] 1864 1 2 ((28464, 2) :: (1, 1) :: repeat (1, 2) 58213 ++ (1716045, 2) :: (1, 1) :: repeat (1, 2) 3474178 ++ (4901382, 2) :: (1, 1) :: repeat (1, 2) 29403094 ++ w) 1)).
  {
    replace ((28464, 2) :: (1, 1) :: repeat (1, 2) 58213 ++ (1716045, 2) :: (1, 1) :: repeat (1, 2) 3474178 ++ (4901382, 2) :: (1, 1) :: repeat (1, 2) 29403094 ++ w) with ((28466 - 2, 2) :: (1, 1) :: repeat (1, 2) 58213 ++ (1716045, 2) :: (1, 1) :: repeat (1, 2) 3474178 ++ (4901382, 2) :: (1, 1) :: repeat (1, 2) 29403094 ++ w) by sec_eq.
    apply (sTUP2_1 [437; 228; 20; 0] 995 1863 28466 ((1, 1) :: repeat (1, 2) 58213 ++ (1716045, 2) :: (1, 1) :: repeat (1, 2) 3474178 ++ (4901382, 2) :: (1, 1) :: repeat (1, 2) 29403094 ++ w) 1); closearith.
  }
  (* step 83: P TDN *)
  apply (hsteps_trans _ (HB [996; 437; 228; 20; 0] 1864 1 4 ((28464, 2) :: (1, 1) :: repeat (1, 2) 58213 ++ (1716045, 2) :: (1, 1) :: repeat (1, 2) 3474178 ++ (4901382, 2) :: (1, 1) :: repeat (1, 2) 29403094 ++ w) 1)).
  {
    apply (sTDN [996; 437; 228; 20; 0] 1864 ((28464, 2) :: (1, 1) :: repeat (1, 2) 58213 ++ (1716045, 2) :: (1, 1) :: repeat (1, 2) 3474178 ++ (4901382, 2) :: (1, 1) :: repeat (1, 2) 29403094 ++ w) 1).
  }
  (* step 84: sTUP *)
  apply (hsteps_trans _ (HC [996; 437; 228; 20; 0] 1864 3 2 ((28462, 2) :: (1, 1) :: repeat (1, 2) 58213 ++ (1716045, 2) :: (1, 1) :: repeat (1, 2) 3474178 ++ (4901382, 2) :: (1, 1) :: repeat (1, 2) 29403094 ++ w) 1)).
  {
    replace ((28462, 2) :: (1, 1) :: repeat (1, 2) 58213 ++ (1716045, 2) :: (1, 1) :: repeat (1, 2) 3474178 ++ (4901382, 2) :: (1, 1) :: repeat (1, 2) 29403094 ++ w) with ((28464 - 2, 2) :: (1, 1) :: repeat (1, 2) 58213 ++ (1716045, 2) :: (1, 1) :: repeat (1, 2) 3474178 ++ (4901382, 2) :: (1, 1) :: repeat (1, 2) 29403094 ++ w) by sec_eq.
    apply (sTUP [996; 437; 228; 20; 0] 1864 4 28464 2 ((1, 1) :: repeat (1, 2) 58213 ++ (1716045, 2) :: (1, 1) :: repeat (1, 2) 3474178 ++ (4901382, 2) :: (1, 1) :: repeat (1, 2) 29403094 ++ w) 1); closearith.
  }
  (* step 85: DIPGRIND 1864 24734 *)
  apply (hsteps_trans _ (HC [996; 437; 228; 20; 0] 0 3 2 (repeat (1, 2) 1864 ++ (24734, 2) :: (1, 1) :: repeat (1, 2) 58213 ++ (1716045, 2) :: (1, 1) :: repeat (1, 2) 3474178 ++ (4901382, 2) :: (1, 1) :: repeat (1, 2) 29403094 ++ w) 1)).
  {
    apply (DIPGRIND 1864 24734 [996; 437; 228; 20; 0] ((1, 1) :: repeat (1, 2) 58213 ++ (1716045, 2) :: (1, 1) :: repeat (1, 2) 3474178 ++ (4901382, 2) :: (1, 1) :: repeat (1, 2) 29403094 ++ w) 1); closearith.
  }
  (* step 86: P PX2A *)
  apply (hsteps_trans _ (HC [228; 20; 0] 436 994 2 ((1, 1) :: repeat (1, 2) 1866 ++ (24734, 2) :: (1, 1) :: repeat (1, 2) 58213 ++ (1716045, 2) :: (1, 1) :: repeat (1, 2) 3474178 ++ (4901382, 2) :: (1, 1) :: repeat (1, 2) 29403094 ++ w) 1)).
  {
    exact (hsteps_step _ _ _ (hPX2A 993 436 [228; 20; 0] (repeat (1, 2) 1864 ++ (24734, 2) :: (1, 1) :: repeat (1, 2) 58213 ++ (1716045, 2) :: (1, 1) :: repeat (1, 2) 3474178 ++ (4901382, 2) :: (1, 1) :: repeat (1, 2) 29403094 ++ w) 1) (hsteps_refl _)).
  }
  (* step 87: P PUSH *)
  apply (hsteps_trans _ (HC [228; 20; 0] 435 1 2 ((992, 2) :: (1, 1) :: repeat (1, 2) 1866 ++ (24734, 2) :: (1, 1) :: repeat (1, 2) 58213 ++ (1716045, 2) :: (1, 1) :: repeat (1, 2) 3474178 ++ (4901382, 2) :: (1, 1) :: repeat (1, 2) 29403094 ++ w) 1)).
  {
    replace ((992, 2) :: (1, 1) :: repeat (1, 2) 1866 ++ (24734, 2) :: (1, 1) :: repeat (1, 2) 58213 ++ (1716045, 2) :: (1, 1) :: repeat (1, 2) 3474178 ++ (4901382, 2) :: (1, 1) :: repeat (1, 2) 29403094 ++ w) with ((994 - 2, 2) :: (1, 1) :: repeat (1, 2) 1866 ++ (24734, 2) :: (1, 1) :: repeat (1, 2) 58213 ++ (1716045, 2) :: (1, 1) :: repeat (1, 2) 3474178 ++ (4901382, 2) :: (1, 1) :: repeat (1, 2) 29403094 ++ w) by sec_eq.
    apply (sPUSH [228; 20; 0] 435 994 ((1, 1) :: repeat (1, 2) 1866 ++ (24734, 2) :: (1, 1) :: repeat (1, 2) 58213 ++ (1716045, 2) :: (1, 1) :: repeat (1, 2) 3474178 ++ (4901382, 2) :: (1, 1) :: repeat (1, 2) 29403094 ++ w) 1); closearith.
  }
  (* step 88: P TDN *)
  apply (hsteps_trans _ (HB [228; 20; 0] 435 1 4 ((992, 2) :: (1, 1) :: repeat (1, 2) 1866 ++ (24734, 2) :: (1, 1) :: repeat (1, 2) 58213 ++ (1716045, 2) :: (1, 1) :: repeat (1, 2) 3474178 ++ (4901382, 2) :: (1, 1) :: repeat (1, 2) 29403094 ++ w) 1)).
  {
    apply (sTDN [228; 20; 0] 435 ((992, 2) :: (1, 1) :: repeat (1, 2) 1866 ++ (24734, 2) :: (1, 1) :: repeat (1, 2) 58213 ++ (1716045, 2) :: (1, 1) :: repeat (1, 2) 3474178 ++ (4901382, 2) :: (1, 1) :: repeat (1, 2) 29403094 ++ w) 1).
  }
  (* step 89: sTUP *)
  apply (hsteps_trans _ (HC [228; 20; 0] 435 3 2 ((990, 2) :: (1, 1) :: repeat (1, 2) 1866 ++ (24734, 2) :: (1, 1) :: repeat (1, 2) 58213 ++ (1716045, 2) :: (1, 1) :: repeat (1, 2) 3474178 ++ (4901382, 2) :: (1, 1) :: repeat (1, 2) 29403094 ++ w) 1)).
  {
    replace ((990, 2) :: (1, 1) :: repeat (1, 2) 1866 ++ (24734, 2) :: (1, 1) :: repeat (1, 2) 58213 ++ (1716045, 2) :: (1, 1) :: repeat (1, 2) 3474178 ++ (4901382, 2) :: (1, 1) :: repeat (1, 2) 29403094 ++ w) with ((992 - 2, 2) :: (1, 1) :: repeat (1, 2) 1866 ++ (24734, 2) :: (1, 1) :: repeat (1, 2) 58213 ++ (1716045, 2) :: (1, 1) :: repeat (1, 2) 3474178 ++ (4901382, 2) :: (1, 1) :: repeat (1, 2) 29403094 ++ w) by sec_eq.
    apply (sTUP [228; 20; 0] 435 4 992 2 ((1, 1) :: repeat (1, 2) 1866 ++ (24734, 2) :: (1, 1) :: repeat (1, 2) 58213 ++ (1716045, 2) :: (1, 1) :: repeat (1, 2) 3474178 ++ (4901382, 2) :: (1, 1) :: repeat (1, 2) 29403094 ++ w) 1); closearith.
  }
  (* step 90: DIPGRIND 435 120 *)
  apply (hsteps_trans _ (HC [228; 20; 0] 0 3 2 (repeat (1, 2) 435 ++ (120, 2) :: (1, 1) :: repeat (1, 2) 1866 ++ (24734, 2) :: (1, 1) :: repeat (1, 2) 58213 ++ (1716045, 2) :: (1, 1) :: repeat (1, 2) 3474178 ++ (4901382, 2) :: (1, 1) :: repeat (1, 2) 29403094 ++ w) 1)).
  {
    apply (DIPGRIND 435 120 [228; 20; 0] ((1, 1) :: repeat (1, 2) 1866 ++ (24734, 2) :: (1, 1) :: repeat (1, 2) 58213 ++ (1716045, 2) :: (1, 1) :: repeat (1, 2) 3474178 ++ (4901382, 2) :: (1, 1) :: repeat (1, 2) 29403094 ++ w) 1); closearith.
  }
  (* step 91: P PX2A *)
  apply (hsteps_trans _ (HC [0] 19 226 2 ((1, 1) :: repeat (1, 2) 437 ++ (120, 2) :: (1, 1) :: repeat (1, 2) 1866 ++ (24734, 2) :: (1, 1) :: repeat (1, 2) 58213 ++ (1716045, 2) :: (1, 1) :: repeat (1, 2) 3474178 ++ (4901382, 2) :: (1, 1) :: repeat (1, 2) 29403094 ++ w) 1)).
  {
    exact (hsteps_step _ _ _ (hPX2A 225 19 [0] (repeat (1, 2) 435 ++ (120, 2) :: (1, 1) :: repeat (1, 2) 1866 ++ (24734, 2) :: (1, 1) :: repeat (1, 2) 58213 ++ (1716045, 2) :: (1, 1) :: repeat (1, 2) 3474178 ++ (4901382, 2) :: (1, 1) :: repeat (1, 2) 29403094 ++ w) 1) (hsteps_refl _)).
  }
  (* step 92: P PUSH *)
  apply (hsteps_trans _ (HC [0] 18 1 2 ((224, 2) :: (1, 1) :: repeat (1, 2) 437 ++ (120, 2) :: (1, 1) :: repeat (1, 2) 1866 ++ (24734, 2) :: (1, 1) :: repeat (1, 2) 58213 ++ (1716045, 2) :: (1, 1) :: repeat (1, 2) 3474178 ++ (4901382, 2) :: (1, 1) :: repeat (1, 2) 29403094 ++ w) 1)).
  {
    replace ((224, 2) :: (1, 1) :: repeat (1, 2) 437 ++ (120, 2) :: (1, 1) :: repeat (1, 2) 1866 ++ (24734, 2) :: (1, 1) :: repeat (1, 2) 58213 ++ (1716045, 2) :: (1, 1) :: repeat (1, 2) 3474178 ++ (4901382, 2) :: (1, 1) :: repeat (1, 2) 29403094 ++ w) with ((226 - 2, 2) :: (1, 1) :: repeat (1, 2) 437 ++ (120, 2) :: (1, 1) :: repeat (1, 2) 1866 ++ (24734, 2) :: (1, 1) :: repeat (1, 2) 58213 ++ (1716045, 2) :: (1, 1) :: repeat (1, 2) 3474178 ++ (4901382, 2) :: (1, 1) :: repeat (1, 2) 29403094 ++ w) by sec_eq.
    apply (sPUSH [0] 18 226 ((1, 1) :: repeat (1, 2) 437 ++ (120, 2) :: (1, 1) :: repeat (1, 2) 1866 ++ (24734, 2) :: (1, 1) :: repeat (1, 2) 58213 ++ (1716045, 2) :: (1, 1) :: repeat (1, 2) 3474178 ++ (4901382, 2) :: (1, 1) :: repeat (1, 2) 29403094 ++ w) 1); closearith.
  }
  (* step 93: P TDN *)
  apply (hsteps_trans _ (HB [0] 18 1 4 ((224, 2) :: (1, 1) :: repeat (1, 2) 437 ++ (120, 2) :: (1, 1) :: repeat (1, 2) 1866 ++ (24734, 2) :: (1, 1) :: repeat (1, 2) 58213 ++ (1716045, 2) :: (1, 1) :: repeat (1, 2) 3474178 ++ (4901382, 2) :: (1, 1) :: repeat (1, 2) 29403094 ++ w) 1)).
  {
    apply (sTDN [0] 18 ((224, 2) :: (1, 1) :: repeat (1, 2) 437 ++ (120, 2) :: (1, 1) :: repeat (1, 2) 1866 ++ (24734, 2) :: (1, 1) :: repeat (1, 2) 58213 ++ (1716045, 2) :: (1, 1) :: repeat (1, 2) 3474178 ++ (4901382, 2) :: (1, 1) :: repeat (1, 2) 29403094 ++ w) 1).
  }
  (* step 94: sTUP *)
  apply (hsteps_trans _ (HC [0] 18 3 2 ((222, 2) :: (1, 1) :: repeat (1, 2) 437 ++ (120, 2) :: (1, 1) :: repeat (1, 2) 1866 ++ (24734, 2) :: (1, 1) :: repeat (1, 2) 58213 ++ (1716045, 2) :: (1, 1) :: repeat (1, 2) 3474178 ++ (4901382, 2) :: (1, 1) :: repeat (1, 2) 29403094 ++ w) 1)).
  {
    replace ((222, 2) :: (1, 1) :: repeat (1, 2) 437 ++ (120, 2) :: (1, 1) :: repeat (1, 2) 1866 ++ (24734, 2) :: (1, 1) :: repeat (1, 2) 58213 ++ (1716045, 2) :: (1, 1) :: repeat (1, 2) 3474178 ++ (4901382, 2) :: (1, 1) :: repeat (1, 2) 29403094 ++ w) with ((224 - 2, 2) :: (1, 1) :: repeat (1, 2) 437 ++ (120, 2) :: (1, 1) :: repeat (1, 2) 1866 ++ (24734, 2) :: (1, 1) :: repeat (1, 2) 58213 ++ (1716045, 2) :: (1, 1) :: repeat (1, 2) 3474178 ++ (4901382, 2) :: (1, 1) :: repeat (1, 2) 29403094 ++ w) by sec_eq.
    apply (sTUP [0] 18 4 224 2 ((1, 1) :: repeat (1, 2) 437 ++ (120, 2) :: (1, 1) :: repeat (1, 2) 1866 ++ (24734, 2) :: (1, 1) :: repeat (1, 2) 58213 ++ (1716045, 2) :: (1, 1) :: repeat (1, 2) 3474178 ++ (4901382, 2) :: (1, 1) :: repeat (1, 2) 29403094 ++ w) 1); closearith.
  }
  (* step 95: DIPGRIND 18 186 *)
  apply (hsteps_trans _ (HC [0] 0 3 2 (repeat (1, 2) 18 ++ (186, 2) :: (1, 1) :: repeat (1, 2) 437 ++ (120, 2) :: (1, 1) :: repeat (1, 2) 1866 ++ (24734, 2) :: (1, 1) :: repeat (1, 2) 58213 ++ (1716045, 2) :: (1, 1) :: repeat (1, 2) 3474178 ++ (4901382, 2) :: (1, 1) :: repeat (1, 2) 29403094 ++ w) 1)).
  {
    apply (DIPGRIND 18 186 [0] ((1, 1) :: repeat (1, 2) 437 ++ (120, 2) :: (1, 1) :: repeat (1, 2) 1866 ++ (24734, 2) :: (1, 1) :: repeat (1, 2) 58213 ++ (1716045, 2) :: (1, 1) :: repeat (1, 2) 3474178 ++ (4901382, 2) :: (1, 1) :: repeat (1, 2) 29403094 ++ w) 1); closearith.
  }
  (* step 96: P PX2B0 *)
  apply (hsteps_trans _ (HB [] 0 1 5 (repeat (1, 2) 19 ++ (186, 2) :: (1, 1) :: repeat (1, 2) 437 ++ (120, 2) :: (1, 1) :: repeat (1, 2) 1866 ++ (24734, 2) :: (1, 1) :: repeat (1, 2) 58213 ++ (1716045, 2) :: (1, 1) :: repeat (1, 2) 3474178 ++ (4901382, 2) :: (1, 1) :: repeat (1, 2) 29403094 ++ w) 1)).
  {
    exact (hsteps_step _ _ _ (hPX2B0 (repeat (1, 2) 18 ++ (186, 2) :: (1, 1) :: repeat (1, 2) 437 ++ (120, 2) :: (1, 1) :: repeat (1, 2) 1866 ++ (24734, 2) :: (1, 1) :: repeat (1, 2) 58213 ++ (1716045, 2) :: (1, 1) :: repeat (1, 2) 3474178 ++ (4901382, 2) :: (1, 1) :: repeat (1, 2) 29403094 ++ w) 1) (hsteps_refl _)).
  }
  (* step 97: M pop12 (19,) *)
  apply (hsteps_trans _ (HB [] 19 1 43 ((186, 2) :: (1, 1) :: repeat (1, 2) 437 ++ (120, 2) :: (1, 1) :: repeat (1, 2) 1866 ++ (24734, 2) :: (1, 1) :: repeat (1, 2) 58213 ++ (1716045, 2) :: (1, 1) :: repeat (1, 2) 3474178 ++ (4901382, 2) :: (1, 1) :: repeat (1, 2) 29403094 ++ w) 1)).
  {
    apply (pop12 19 [] 0 5 ((186, 2) :: (1, 1) :: repeat (1, 2) 437 ++ (120, 2) :: (1, 1) :: repeat (1, 2) 1866 ++ (24734, 2) :: (1, 1) :: repeat (1, 2) 58213 ++ (1716045, 2) :: (1, 1) :: repeat (1, 2) 3474178 ++ (4901382, 2) :: (1, 1) :: repeat (1, 2) 29403094 ++ w) 1); closearith.
  }
  (* step 98: sTUP *)
  apply (hsteps_trans _ (HC [] 19 42 2 ((184, 2) :: (1, 1) :: repeat (1, 2) 437 ++ (120, 2) :: (1, 1) :: repeat (1, 2) 1866 ++ (24734, 2) :: (1, 1) :: repeat (1, 2) 58213 ++ (1716045, 2) :: (1, 1) :: repeat (1, 2) 3474178 ++ (4901382, 2) :: (1, 1) :: repeat (1, 2) 29403094 ++ w) 1)).
  {
    replace ((184, 2) :: (1, 1) :: repeat (1, 2) 437 ++ (120, 2) :: (1, 1) :: repeat (1, 2) 1866 ++ (24734, 2) :: (1, 1) :: repeat (1, 2) 58213 ++ (1716045, 2) :: (1, 1) :: repeat (1, 2) 3474178 ++ (4901382, 2) :: (1, 1) :: repeat (1, 2) 29403094 ++ w) with ((186 - 2, 2) :: (1, 1) :: repeat (1, 2) 437 ++ (120, 2) :: (1, 1) :: repeat (1, 2) 1866 ++ (24734, 2) :: (1, 1) :: repeat (1, 2) 58213 ++ (1716045, 2) :: (1, 1) :: repeat (1, 2) 3474178 ++ (4901382, 2) :: (1, 1) :: repeat (1, 2) 29403094 ++ w) by sec_eq.
    apply (sTUP [] 19 43 186 2 ((1, 1) :: repeat (1, 2) 437 ++ (120, 2) :: (1, 1) :: repeat (1, 2) 1866 ++ (24734, 2) :: (1, 1) :: repeat (1, 2) 58213 ++ (1716045, 2) :: (1, 1) :: repeat (1, 2) 3474178 ++ (4901382, 2) :: (1, 1) :: repeat (1, 2) 29403094 ++ w) 1); closearith.
  }
  (* step 99: P PUSH *)
  apply (hsteps_trans _ (HC [] 18 1 2 ((40, 2) :: (184, 2) :: (1, 1) :: repeat (1, 2) 437 ++ (120, 2) :: (1, 1) :: repeat (1, 2) 1866 ++ (24734, 2) :: (1, 1) :: repeat (1, 2) 58213 ++ (1716045, 2) :: (1, 1) :: repeat (1, 2) 3474178 ++ (4901382, 2) :: (1, 1) :: repeat (1, 2) 29403094 ++ w) 1)).
  {
    replace ((40, 2) :: (184, 2) :: (1, 1) :: repeat (1, 2) 437 ++ (120, 2) :: (1, 1) :: repeat (1, 2) 1866 ++ (24734, 2) :: (1, 1) :: repeat (1, 2) 58213 ++ (1716045, 2) :: (1, 1) :: repeat (1, 2) 3474178 ++ (4901382, 2) :: (1, 1) :: repeat (1, 2) 29403094 ++ w) with ((42 - 2, 2) :: (184, 2) :: (1, 1) :: repeat (1, 2) 437 ++ (120, 2) :: (1, 1) :: repeat (1, 2) 1866 ++ (24734, 2) :: (1, 1) :: repeat (1, 2) 58213 ++ (1716045, 2) :: (1, 1) :: repeat (1, 2) 3474178 ++ (4901382, 2) :: (1, 1) :: repeat (1, 2) 29403094 ++ w) by sec_eq.
    apply (sPUSH [] 18 42 ((184, 2) :: (1, 1) :: repeat (1, 2) 437 ++ (120, 2) :: (1, 1) :: repeat (1, 2) 1866 ++ (24734, 2) :: (1, 1) :: repeat (1, 2) 58213 ++ (1716045, 2) :: (1, 1) :: repeat (1, 2) 3474178 ++ (4901382, 2) :: (1, 1) :: repeat (1, 2) 29403094 ++ w) 1); closearith.
  }
  (* step 100: P TDN *)
  apply (hsteps_trans _ (HB [] 18 1 4 ((40, 2) :: (184, 2) :: (1, 1) :: repeat (1, 2) 437 ++ (120, 2) :: (1, 1) :: repeat (1, 2) 1866 ++ (24734, 2) :: (1, 1) :: repeat (1, 2) 58213 ++ (1716045, 2) :: (1, 1) :: repeat (1, 2) 3474178 ++ (4901382, 2) :: (1, 1) :: repeat (1, 2) 29403094 ++ w) 1)).
  {
    apply (sTDN [] 18 ((40, 2) :: (184, 2) :: (1, 1) :: repeat (1, 2) 437 ++ (120, 2) :: (1, 1) :: repeat (1, 2) 1866 ++ (24734, 2) :: (1, 1) :: repeat (1, 2) 58213 ++ (1716045, 2) :: (1, 1) :: repeat (1, 2) 3474178 ++ (4901382, 2) :: (1, 1) :: repeat (1, 2) 29403094 ++ w) 1).
  }
  (* step 101: sTUP *)
  apply (hsteps_trans _ (HC [] 18 3 2 ((38, 2) :: (184, 2) :: (1, 1) :: repeat (1, 2) 437 ++ (120, 2) :: (1, 1) :: repeat (1, 2) 1866 ++ (24734, 2) :: (1, 1) :: repeat (1, 2) 58213 ++ (1716045, 2) :: (1, 1) :: repeat (1, 2) 3474178 ++ (4901382, 2) :: (1, 1) :: repeat (1, 2) 29403094 ++ w) 1)).
  {
    replace ((38, 2) :: (184, 2) :: (1, 1) :: repeat (1, 2) 437 ++ (120, 2) :: (1, 1) :: repeat (1, 2) 1866 ++ (24734, 2) :: (1, 1) :: repeat (1, 2) 58213 ++ (1716045, 2) :: (1, 1) :: repeat (1, 2) 3474178 ++ (4901382, 2) :: (1, 1) :: repeat (1, 2) 29403094 ++ w) with ((40 - 2, 2) :: (184, 2) :: (1, 1) :: repeat (1, 2) 437 ++ (120, 2) :: (1, 1) :: repeat (1, 2) 1866 ++ (24734, 2) :: (1, 1) :: repeat (1, 2) 58213 ++ (1716045, 2) :: (1, 1) :: repeat (1, 2) 3474178 ++ (4901382, 2) :: (1, 1) :: repeat (1, 2) 29403094 ++ w) by sec_eq.
    apply (sTUP [] 18 4 40 2 ((184, 2) :: (1, 1) :: repeat (1, 2) 437 ++ (120, 2) :: (1, 1) :: repeat (1, 2) 1866 ++ (24734, 2) :: (1, 1) :: repeat (1, 2) 58213 ++ (1716045, 2) :: (1, 1) :: repeat (1, 2) 3474178 ++ (4901382, 2) :: (1, 1) :: repeat (1, 2) 29403094 ++ w) 1); closearith.
  }
  (* step 102: DIPGRIND 18 2 *)
  apply (hsteps_trans _ (HC [] 0 3 2 (repeat (1, 2) 18 ++ (2, 2) :: (184, 2) :: (1, 1) :: repeat (1, 2) 437 ++ (120, 2) :: (1, 1) :: repeat (1, 2) 1866 ++ (24734, 2) :: (1, 1) :: repeat (1, 2) 58213 ++ (1716045, 2) :: (1, 1) :: repeat (1, 2) 3474178 ++ (4901382, 2) :: (1, 1) :: repeat (1, 2) 29403094 ++ w) 1)).
  {
    apply (DIPGRIND 18 2 [] ((184, 2) :: (1, 1) :: repeat (1, 2) 437 ++ (120, 2) :: (1, 1) :: repeat (1, 2) 1866 ++ (24734, 2) :: (1, 1) :: repeat (1, 2) 58213 ++ (1716045, 2) :: (1, 1) :: repeat (1, 2) 3474178 ++ (4901382, 2) :: (1, 1) :: repeat (1, 2) 29403094 ++ w) 1); closearith.
  }
  (* step 103: P PUSHX *)
  apply (hsteps_trans _ (HB [] 1 1 7 (repeat (1, 2) 18 ++ (2, 2) :: (184, 2) :: (1, 1) :: repeat (1, 2) 437 ++ (120, 2) :: (1, 1) :: repeat (1, 2) 1866 ++ (24734, 2) :: (1, 1) :: repeat (1, 2) 58213 ++ (1716045, 2) :: (1, 1) :: repeat (1, 2) 3474178 ++ (4901382, 2) :: (1, 1) :: repeat (1, 2) 29403094 ++ w) 1)).
  {
    exact (hsteps_step _ _ _ (hPUSHX (repeat (1, 2) 18 ++ (2, 2) :: (184, 2) :: (1, 1) :: repeat (1, 2) 437 ++ (120, 2) :: (1, 1) :: repeat (1, 2) 1866 ++ (24734, 2) :: (1, 1) :: repeat (1, 2) 58213 ++ (1716045, 2) :: (1, 1) :: repeat (1, 2) 3474178 ++ (4901382, 2) :: (1, 1) :: repeat (1, 2) 29403094 ++ w) 1) (hsteps_refl _)).
  }
  (* step 104: M pop12 (18,) *)
  apply (hsteps_trans _ (HB [] 19 1 43 ((2, 2) :: (184, 2) :: (1, 1) :: repeat (1, 2) 437 ++ (120, 2) :: (1, 1) :: repeat (1, 2) 1866 ++ (24734, 2) :: (1, 1) :: repeat (1, 2) 58213 ++ (1716045, 2) :: (1, 1) :: repeat (1, 2) 3474178 ++ (4901382, 2) :: (1, 1) :: repeat (1, 2) 29403094 ++ w) 1)).
  {
    apply (pop12 18 [] 1 7 ((2, 2) :: (184, 2) :: (1, 1) :: repeat (1, 2) 437 ++ (120, 2) :: (1, 1) :: repeat (1, 2) 1866 ++ (24734, 2) :: (1, 1) :: repeat (1, 2) 58213 ++ (1716045, 2) :: (1, 1) :: repeat (1, 2) 3474178 ++ (4901382, 2) :: (1, 1) :: repeat (1, 2) 29403094 ++ w) 1); closearith.
  }
  (* step 105: P TUP2_1 *)
  apply (hsteps_trans _ (HC [20] 43 1 2 ((182, 2) :: (1, 1) :: repeat (1, 2) 437 ++ (120, 2) :: (1, 1) :: repeat (1, 2) 1866 ++ (24734, 2) :: (1, 1) :: repeat (1, 2) 58213 ++ (1716045, 2) :: (1, 1) :: repeat (1, 2) 3474178 ++ (4901382, 2) :: (1, 1) :: repeat (1, 2) 29403094 ++ w) 1)).
  {
    replace ((182, 2) :: (1, 1) :: repeat (1, 2) 437 ++ (120, 2) :: (1, 1) :: repeat (1, 2) 1866 ++ (24734, 2) :: (1, 1) :: repeat (1, 2) 58213 ++ (1716045, 2) :: (1, 1) :: repeat (1, 2) 3474178 ++ (4901382, 2) :: (1, 1) :: repeat (1, 2) 29403094 ++ w) with ((184 - 2, 2) :: (1, 1) :: repeat (1, 2) 437 ++ (120, 2) :: (1, 1) :: repeat (1, 2) 1866 ++ (24734, 2) :: (1, 1) :: repeat (1, 2) 58213 ++ (1716045, 2) :: (1, 1) :: repeat (1, 2) 3474178 ++ (4901382, 2) :: (1, 1) :: repeat (1, 2) 29403094 ++ w) by sec_eq.
    apply (sTUP2_1 [] 19 42 184 ((1, 1) :: repeat (1, 2) 437 ++ (120, 2) :: (1, 1) :: repeat (1, 2) 1866 ++ (24734, 2) :: (1, 1) :: repeat (1, 2) 58213 ++ (1716045, 2) :: (1, 1) :: repeat (1, 2) 3474178 ++ (4901382, 2) :: (1, 1) :: repeat (1, 2) 29403094 ++ w) 1); closearith.
  }
  (* step 106: P TDN *)
  apply (hsteps_trans _ (HB [20] 43 1 4 ((182, 2) :: (1, 1) :: repeat (1, 2) 437 ++ (120, 2) :: (1, 1) :: repeat (1, 2) 1866 ++ (24734, 2) :: (1, 1) :: repeat (1, 2) 58213 ++ (1716045, 2) :: (1, 1) :: repeat (1, 2) 3474178 ++ (4901382, 2) :: (1, 1) :: repeat (1, 2) 29403094 ++ w) 1)).
  {
    apply (sTDN [20] 43 ((182, 2) :: (1, 1) :: repeat (1, 2) 437 ++ (120, 2) :: (1, 1) :: repeat (1, 2) 1866 ++ (24734, 2) :: (1, 1) :: repeat (1, 2) 58213 ++ (1716045, 2) :: (1, 1) :: repeat (1, 2) 3474178 ++ (4901382, 2) :: (1, 1) :: repeat (1, 2) 29403094 ++ w) 1).
  }
  (* step 107: sTUP *)
  apply (hsteps_trans _ (HC [20] 43 3 2 ((180, 2) :: (1, 1) :: repeat (1, 2) 437 ++ (120, 2) :: (1, 1) :: repeat (1, 2) 1866 ++ (24734, 2) :: (1, 1) :: repeat (1, 2) 58213 ++ (1716045, 2) :: (1, 1) :: repeat (1, 2) 3474178 ++ (4901382, 2) :: (1, 1) :: repeat (1, 2) 29403094 ++ w) 1)).
  {
    replace ((180, 2) :: (1, 1) :: repeat (1, 2) 437 ++ (120, 2) :: (1, 1) :: repeat (1, 2) 1866 ++ (24734, 2) :: (1, 1) :: repeat (1, 2) 58213 ++ (1716045, 2) :: (1, 1) :: repeat (1, 2) 3474178 ++ (4901382, 2) :: (1, 1) :: repeat (1, 2) 29403094 ++ w) with ((182 - 2, 2) :: (1, 1) :: repeat (1, 2) 437 ++ (120, 2) :: (1, 1) :: repeat (1, 2) 1866 ++ (24734, 2) :: (1, 1) :: repeat (1, 2) 58213 ++ (1716045, 2) :: (1, 1) :: repeat (1, 2) 3474178 ++ (4901382, 2) :: (1, 1) :: repeat (1, 2) 29403094 ++ w) by sec_eq.
    apply (sTUP [20] 43 4 182 2 ((1, 1) :: repeat (1, 2) 437 ++ (120, 2) :: (1, 1) :: repeat (1, 2) 1866 ++ (24734, 2) :: (1, 1) :: repeat (1, 2) 58213 ++ (1716045, 2) :: (1, 1) :: repeat (1, 2) 3474178 ++ (4901382, 2) :: (1, 1) :: repeat (1, 2) 29403094 ++ w) 1); closearith.
  }
  (* step 108: DIPGRIND 43 94 *)
  apply (hsteps_trans _ (HC [20] 0 3 2 (repeat (1, 2) 43 ++ (94, 2) :: (1, 1) :: repeat (1, 2) 437 ++ (120, 2) :: (1, 1) :: repeat (1, 2) 1866 ++ (24734, 2) :: (1, 1) :: repeat (1, 2) 58213 ++ (1716045, 2) :: (1, 1) :: repeat (1, 2) 3474178 ++ (4901382, 2) :: (1, 1) :: repeat (1, 2) 29403094 ++ w) 1)).
  {
    apply (DIPGRIND 43 94 [20] ((1, 1) :: repeat (1, 2) 437 ++ (120, 2) :: (1, 1) :: repeat (1, 2) 1866 ++ (24734, 2) :: (1, 1) :: repeat (1, 2) 58213 ++ (1716045, 2) :: (1, 1) :: repeat (1, 2) 3474178 ++ (4901382, 2) :: (1, 1) :: repeat (1, 2) 29403094 ++ w) 1); closearith.
  }
  (* step 109: P PX2Bgen *)
  apply (hsteps_trans _ (HB [0] 3 1 2 ((16, 2) :: (1, 1) :: repeat (1, 2) 45 ++ (94, 2) :: (1, 1) :: repeat (1, 2) 437 ++ (120, 2) :: (1, 1) :: repeat (1, 2) 1866 ++ (24734, 2) :: (1, 1) :: repeat (1, 2) 58213 ++ (1716045, 2) :: (1, 1) :: repeat (1, 2) 3474178 ++ (4901382, 2) :: (1, 1) :: repeat (1, 2) 29403094 ++ w) 1)).
  {
    exact (hsteps_step _ _ _ (hPX2Bgen 15 (repeat (1, 2) 43 ++ (94, 2) :: (1, 1) :: repeat (1, 2) 437 ++ (120, 2) :: (1, 1) :: repeat (1, 2) 1866 ++ (24734, 2) :: (1, 1) :: repeat (1, 2) 58213 ++ (1716045, 2) :: (1, 1) :: repeat (1, 2) 3474178 ++ (4901382, 2) :: (1, 1) :: repeat (1, 2) 29403094 ++ w) 1) (hsteps_refl _)).
  }
  (* step 110: sTUP *)
  apply (hsteps_trans _ (HC [0] 3 1 2 ((14, 2) :: (1, 1) :: repeat (1, 2) 45 ++ (94, 2) :: (1, 1) :: repeat (1, 2) 437 ++ (120, 2) :: (1, 1) :: repeat (1, 2) 1866 ++ (24734, 2) :: (1, 1) :: repeat (1, 2) 58213 ++ (1716045, 2) :: (1, 1) :: repeat (1, 2) 3474178 ++ (4901382, 2) :: (1, 1) :: repeat (1, 2) 29403094 ++ w) 1)).
  {
    replace ((14, 2) :: (1, 1) :: repeat (1, 2) 45 ++ (94, 2) :: (1, 1) :: repeat (1, 2) 437 ++ (120, 2) :: (1, 1) :: repeat (1, 2) 1866 ++ (24734, 2) :: (1, 1) :: repeat (1, 2) 58213 ++ (1716045, 2) :: (1, 1) :: repeat (1, 2) 3474178 ++ (4901382, 2) :: (1, 1) :: repeat (1, 2) 29403094 ++ w) with ((16 - 2, 2) :: (1, 1) :: repeat (1, 2) 45 ++ (94, 2) :: (1, 1) :: repeat (1, 2) 437 ++ (120, 2) :: (1, 1) :: repeat (1, 2) 1866 ++ (24734, 2) :: (1, 1) :: repeat (1, 2) 58213 ++ (1716045, 2) :: (1, 1) :: repeat (1, 2) 3474178 ++ (4901382, 2) :: (1, 1) :: repeat (1, 2) 29403094 ++ w) by sec_eq.
    apply (sTUP [0] 3 2 16 2 ((1, 1) :: repeat (1, 2) 45 ++ (94, 2) :: (1, 1) :: repeat (1, 2) 437 ++ (120, 2) :: (1, 1) :: repeat (1, 2) 1866 ++ (24734, 2) :: (1, 1) :: repeat (1, 2) 58213 ++ (1716045, 2) :: (1, 1) :: repeat (1, 2) 3474178 ++ (4901382, 2) :: (1, 1) :: repeat (1, 2) 29403094 ++ w) 1); closearith.
  }
  (* step 111: P TDN *)
  apply (hsteps_trans _ (HB [0] 3 1 4 ((14, 2) :: (1, 1) :: repeat (1, 2) 45 ++ (94, 2) :: (1, 1) :: repeat (1, 2) 437 ++ (120, 2) :: (1, 1) :: repeat (1, 2) 1866 ++ (24734, 2) :: (1, 1) :: repeat (1, 2) 58213 ++ (1716045, 2) :: (1, 1) :: repeat (1, 2) 3474178 ++ (4901382, 2) :: (1, 1) :: repeat (1, 2) 29403094 ++ w) 1)).
  {
    apply (sTDN [0] 3 ((14, 2) :: (1, 1) :: repeat (1, 2) 45 ++ (94, 2) :: (1, 1) :: repeat (1, 2) 437 ++ (120, 2) :: (1, 1) :: repeat (1, 2) 1866 ++ (24734, 2) :: (1, 1) :: repeat (1, 2) 58213 ++ (1716045, 2) :: (1, 1) :: repeat (1, 2) 3474178 ++ (4901382, 2) :: (1, 1) :: repeat (1, 2) 29403094 ++ w) 1).
  }
  (* step 112: sTUP *)
  apply (hsteps_trans _ (HC [0] 3 3 2 ((12, 2) :: (1, 1) :: repeat (1, 2) 45 ++ (94, 2) :: (1, 1) :: repeat (1, 2) 437 ++ (120, 2) :: (1, 1) :: repeat (1, 2) 1866 ++ (24734, 2) :: (1, 1) :: repeat (1, 2) 58213 ++ (1716045, 2) :: (1, 1) :: repeat (1, 2) 3474178 ++ (4901382, 2) :: (1, 1) :: repeat (1, 2) 29403094 ++ w) 1)).
  {
    replace ((12, 2) :: (1, 1) :: repeat (1, 2) 45 ++ (94, 2) :: (1, 1) :: repeat (1, 2) 437 ++ (120, 2) :: (1, 1) :: repeat (1, 2) 1866 ++ (24734, 2) :: (1, 1) :: repeat (1, 2) 58213 ++ (1716045, 2) :: (1, 1) :: repeat (1, 2) 3474178 ++ (4901382, 2) :: (1, 1) :: repeat (1, 2) 29403094 ++ w) with ((14 - 2, 2) :: (1, 1) :: repeat (1, 2) 45 ++ (94, 2) :: (1, 1) :: repeat (1, 2) 437 ++ (120, 2) :: (1, 1) :: repeat (1, 2) 1866 ++ (24734, 2) :: (1, 1) :: repeat (1, 2) 58213 ++ (1716045, 2) :: (1, 1) :: repeat (1, 2) 3474178 ++ (4901382, 2) :: (1, 1) :: repeat (1, 2) 29403094 ++ w) by sec_eq.
    apply (sTUP [0] 3 4 14 2 ((1, 1) :: repeat (1, 2) 45 ++ (94, 2) :: (1, 1) :: repeat (1, 2) 437 ++ (120, 2) :: (1, 1) :: repeat (1, 2) 1866 ++ (24734, 2) :: (1, 1) :: repeat (1, 2) 58213 ++ (1716045, 2) :: (1, 1) :: repeat (1, 2) 3474178 ++ (4901382, 2) :: (1, 1) :: repeat (1, 2) 29403094 ++ w) 1); closearith.
  }
  (* step 113: DIPGRIND 3 6 *)
  apply (hsteps_trans _ (HC [0] 0 3 2 (repeat (1, 2) 3 ++ (6, 2) :: (1, 1) :: repeat (1, 2) 45 ++ (94, 2) :: (1, 1) :: repeat (1, 2) 437 ++ (120, 2) :: (1, 1) :: repeat (1, 2) 1866 ++ (24734, 2) :: (1, 1) :: repeat (1, 2) 58213 ++ (1716045, 2) :: (1, 1) :: repeat (1, 2) 3474178 ++ (4901382, 2) :: (1, 1) :: repeat (1, 2) 29403094 ++ w) 1)).
  {
    apply (DIPGRIND 3 6 [0] ((1, 1) :: repeat (1, 2) 45 ++ (94, 2) :: (1, 1) :: repeat (1, 2) 437 ++ (120, 2) :: (1, 1) :: repeat (1, 2) 1866 ++ (24734, 2) :: (1, 1) :: repeat (1, 2) 58213 ++ (1716045, 2) :: (1, 1) :: repeat (1, 2) 3474178 ++ (4901382, 2) :: (1, 1) :: repeat (1, 2) 29403094 ++ w) 1); closearith.
  }
  (* step 114: P PX2B0 *)
  apply (hsteps_trans _ (HB [] 0 1 5 (repeat (1, 2) 4 ++ (6, 2) :: (1, 1) :: repeat (1, 2) 45 ++ (94, 2) :: (1, 1) :: repeat (1, 2) 437 ++ (120, 2) :: (1, 1) :: repeat (1, 2) 1866 ++ (24734, 2) :: (1, 1) :: repeat (1, 2) 58213 ++ (1716045, 2) :: (1, 1) :: repeat (1, 2) 3474178 ++ (4901382, 2) :: (1, 1) :: repeat (1, 2) 29403094 ++ w) 1)).
  {
    exact (hsteps_step _ _ _ (hPX2B0 (repeat (1, 2) 3 ++ (6, 2) :: (1, 1) :: repeat (1, 2) 45 ++ (94, 2) :: (1, 1) :: repeat (1, 2) 437 ++ (120, 2) :: (1, 1) :: repeat (1, 2) 1866 ++ (24734, 2) :: (1, 1) :: repeat (1, 2) 58213 ++ (1716045, 2) :: (1, 1) :: repeat (1, 2) 3474178 ++ (4901382, 2) :: (1, 1) :: repeat (1, 2) 29403094 ++ w) 1) (hsteps_refl _)).
  }
  (* step 115: M pop12 (4,) *)
  apply (hsteps_trans _ (HB [] 4 1 13 ((6, 2) :: (1, 1) :: repeat (1, 2) 45 ++ (94, 2) :: (1, 1) :: repeat (1, 2) 437 ++ (120, 2) :: (1, 1) :: repeat (1, 2) 1866 ++ (24734, 2) :: (1, 1) :: repeat (1, 2) 58213 ++ (1716045, 2) :: (1, 1) :: repeat (1, 2) 3474178 ++ (4901382, 2) :: (1, 1) :: repeat (1, 2) 29403094 ++ w) 1)).
  {
    apply (pop12 4 [] 0 5 ((6, 2) :: (1, 1) :: repeat (1, 2) 45 ++ (94, 2) :: (1, 1) :: repeat (1, 2) 437 ++ (120, 2) :: (1, 1) :: repeat (1, 2) 1866 ++ (24734, 2) :: (1, 1) :: repeat (1, 2) 58213 ++ (1716045, 2) :: (1, 1) :: repeat (1, 2) 3474178 ++ (4901382, 2) :: (1, 1) :: repeat (1, 2) 29403094 ++ w) 1); closearith.
  }
  (* step 116: sTUP *)
  apply (hsteps_trans _ (HC [] 4 12 2 ((4, 2) :: (1, 1) :: repeat (1, 2) 45 ++ (94, 2) :: (1, 1) :: repeat (1, 2) 437 ++ (120, 2) :: (1, 1) :: repeat (1, 2) 1866 ++ (24734, 2) :: (1, 1) :: repeat (1, 2) 58213 ++ (1716045, 2) :: (1, 1) :: repeat (1, 2) 3474178 ++ (4901382, 2) :: (1, 1) :: repeat (1, 2) 29403094 ++ w) 1)).
  {
    replace ((4, 2) :: (1, 1) :: repeat (1, 2) 45 ++ (94, 2) :: (1, 1) :: repeat (1, 2) 437 ++ (120, 2) :: (1, 1) :: repeat (1, 2) 1866 ++ (24734, 2) :: (1, 1) :: repeat (1, 2) 58213 ++ (1716045, 2) :: (1, 1) :: repeat (1, 2) 3474178 ++ (4901382, 2) :: (1, 1) :: repeat (1, 2) 29403094 ++ w) with ((6 - 2, 2) :: (1, 1) :: repeat (1, 2) 45 ++ (94, 2) :: (1, 1) :: repeat (1, 2) 437 ++ (120, 2) :: (1, 1) :: repeat (1, 2) 1866 ++ (24734, 2) :: (1, 1) :: repeat (1, 2) 58213 ++ (1716045, 2) :: (1, 1) :: repeat (1, 2) 3474178 ++ (4901382, 2) :: (1, 1) :: repeat (1, 2) 29403094 ++ w) by sec_eq.
    apply (sTUP [] 4 13 6 2 ((1, 1) :: repeat (1, 2) 45 ++ (94, 2) :: (1, 1) :: repeat (1, 2) 437 ++ (120, 2) :: (1, 1) :: repeat (1, 2) 1866 ++ (24734, 2) :: (1, 1) :: repeat (1, 2) 58213 ++ (1716045, 2) :: (1, 1) :: repeat (1, 2) 3474178 ++ (4901382, 2) :: (1, 1) :: repeat (1, 2) 29403094 ++ w) 1); closearith.
  }
  (* step 117: P PUSH *)
  apply (hsteps_trans _ (HC [] 3 1 2 ((10, 2) :: (4, 2) :: (1, 1) :: repeat (1, 2) 45 ++ (94, 2) :: (1, 1) :: repeat (1, 2) 437 ++ (120, 2) :: (1, 1) :: repeat (1, 2) 1866 ++ (24734, 2) :: (1, 1) :: repeat (1, 2) 58213 ++ (1716045, 2) :: (1, 1) :: repeat (1, 2) 3474178 ++ (4901382, 2) :: (1, 1) :: repeat (1, 2) 29403094 ++ w) 1)).
  {
    replace ((10, 2) :: (4, 2) :: (1, 1) :: repeat (1, 2) 45 ++ (94, 2) :: (1, 1) :: repeat (1, 2) 437 ++ (120, 2) :: (1, 1) :: repeat (1, 2) 1866 ++ (24734, 2) :: (1, 1) :: repeat (1, 2) 58213 ++ (1716045, 2) :: (1, 1) :: repeat (1, 2) 3474178 ++ (4901382, 2) :: (1, 1) :: repeat (1, 2) 29403094 ++ w) with ((12 - 2, 2) :: (4, 2) :: (1, 1) :: repeat (1, 2) 45 ++ (94, 2) :: (1, 1) :: repeat (1, 2) 437 ++ (120, 2) :: (1, 1) :: repeat (1, 2) 1866 ++ (24734, 2) :: (1, 1) :: repeat (1, 2) 58213 ++ (1716045, 2) :: (1, 1) :: repeat (1, 2) 3474178 ++ (4901382, 2) :: (1, 1) :: repeat (1, 2) 29403094 ++ w) by sec_eq.
    apply (sPUSH [] 3 12 ((4, 2) :: (1, 1) :: repeat (1, 2) 45 ++ (94, 2) :: (1, 1) :: repeat (1, 2) 437 ++ (120, 2) :: (1, 1) :: repeat (1, 2) 1866 ++ (24734, 2) :: (1, 1) :: repeat (1, 2) 58213 ++ (1716045, 2) :: (1, 1) :: repeat (1, 2) 3474178 ++ (4901382, 2) :: (1, 1) :: repeat (1, 2) 29403094 ++ w) 1); closearith.
  }
  (* step 118: P TDN *)
  apply (hsteps_trans _ (HB [] 3 1 4 ((10, 2) :: (4, 2) :: (1, 1) :: repeat (1, 2) 45 ++ (94, 2) :: (1, 1) :: repeat (1, 2) 437 ++ (120, 2) :: (1, 1) :: repeat (1, 2) 1866 ++ (24734, 2) :: (1, 1) :: repeat (1, 2) 58213 ++ (1716045, 2) :: (1, 1) :: repeat (1, 2) 3474178 ++ (4901382, 2) :: (1, 1) :: repeat (1, 2) 29403094 ++ w) 1)).
  {
    apply (sTDN [] 3 ((10, 2) :: (4, 2) :: (1, 1) :: repeat (1, 2) 45 ++ (94, 2) :: (1, 1) :: repeat (1, 2) 437 ++ (120, 2) :: (1, 1) :: repeat (1, 2) 1866 ++ (24734, 2) :: (1, 1) :: repeat (1, 2) 58213 ++ (1716045, 2) :: (1, 1) :: repeat (1, 2) 3474178 ++ (4901382, 2) :: (1, 1) :: repeat (1, 2) 29403094 ++ w) 1).
  }
  (* step 119: sTUP *)
  apply (hsteps_trans _ (HC [] 3 3 2 ((8, 2) :: (4, 2) :: (1, 1) :: repeat (1, 2) 45 ++ (94, 2) :: (1, 1) :: repeat (1, 2) 437 ++ (120, 2) :: (1, 1) :: repeat (1, 2) 1866 ++ (24734, 2) :: (1, 1) :: repeat (1, 2) 58213 ++ (1716045, 2) :: (1, 1) :: repeat (1, 2) 3474178 ++ (4901382, 2) :: (1, 1) :: repeat (1, 2) 29403094 ++ w) 1)).
  {
    replace ((8, 2) :: (4, 2) :: (1, 1) :: repeat (1, 2) 45 ++ (94, 2) :: (1, 1) :: repeat (1, 2) 437 ++ (120, 2) :: (1, 1) :: repeat (1, 2) 1866 ++ (24734, 2) :: (1, 1) :: repeat (1, 2) 58213 ++ (1716045, 2) :: (1, 1) :: repeat (1, 2) 3474178 ++ (4901382, 2) :: (1, 1) :: repeat (1, 2) 29403094 ++ w) with ((10 - 2, 2) :: (4, 2) :: (1, 1) :: repeat (1, 2) 45 ++ (94, 2) :: (1, 1) :: repeat (1, 2) 437 ++ (120, 2) :: (1, 1) :: repeat (1, 2) 1866 ++ (24734, 2) :: (1, 1) :: repeat (1, 2) 58213 ++ (1716045, 2) :: (1, 1) :: repeat (1, 2) 3474178 ++ (4901382, 2) :: (1, 1) :: repeat (1, 2) 29403094 ++ w) by sec_eq.
    apply (sTUP [] 3 4 10 2 ((4, 2) :: (1, 1) :: repeat (1, 2) 45 ++ (94, 2) :: (1, 1) :: repeat (1, 2) 437 ++ (120, 2) :: (1, 1) :: repeat (1, 2) 1866 ++ (24734, 2) :: (1, 1) :: repeat (1, 2) 58213 ++ (1716045, 2) :: (1, 1) :: repeat (1, 2) 3474178 ++ (4901382, 2) :: (1, 1) :: repeat (1, 2) 29403094 ++ w) 1); closearith.
  }
  (* step 120: DIPGRIND 3 2 *)
  apply (hsteps_trans _ (HC [] 0 3 2 (repeat (1, 2) 3 ++ (2, 2) :: (4, 2) :: (1, 1) :: repeat (1, 2) 45 ++ (94, 2) :: (1, 1) :: repeat (1, 2) 437 ++ (120, 2) :: (1, 1) :: repeat (1, 2) 1866 ++ (24734, 2) :: (1, 1) :: repeat (1, 2) 58213 ++ (1716045, 2) :: (1, 1) :: repeat (1, 2) 3474178 ++ (4901382, 2) :: (1, 1) :: repeat (1, 2) 29403094 ++ w) 1)).
  {
    apply (DIPGRIND 3 2 [] ((4, 2) :: (1, 1) :: repeat (1, 2) 45 ++ (94, 2) :: (1, 1) :: repeat (1, 2) 437 ++ (120, 2) :: (1, 1) :: repeat (1, 2) 1866 ++ (24734, 2) :: (1, 1) :: repeat (1, 2) 58213 ++ (1716045, 2) :: (1, 1) :: repeat (1, 2) 3474178 ++ (4901382, 2) :: (1, 1) :: repeat (1, 2) 29403094 ++ w) 1); closearith.
  }
  (* step 121: P PUSHX *)
  exact (hsteps_step _ _ _ (hPUSHX (repeat (1, 2) 3 ++ (2, 2) :: (4, 2) :: (1, 1) :: repeat (1, 2) 45 ++ (94, 2) :: (1, 1) :: repeat (1, 2) 437 ++ (120, 2) :: (1, 1) :: repeat (1, 2) 1866 ++ (24734, 2) :: (1, 1) :: repeat (1, 2) 58213 ++ (1716045, 2) :: (1, 1) :: repeat (1, 2) 3474178 ++ (4901382, 2) :: (1, 1) :: repeat (1, 2) 29403094 ++ w) 1) (hsteps_refl _)).
Qed.

(* CASCADE59e: steps 122-177 of the CASCADE59 chain. *)
Lemma CASCADE59e : forall w,
  hsteps (HB [] 1 1 7 (repeat (1, 2) 3 ++ (2, 2) :: (4, 2) :: (1, 1) :: repeat (1, 2) 45 ++ (94, 2) :: (1, 1) :: repeat (1, 2) 437 ++ (120, 2) :: (1, 1) :: repeat (1, 2) 1866 ++ (24734, 2) :: (1, 1) :: repeat (1, 2) 58213 ++ (1716045, 2) :: (1, 1) :: repeat (1, 2) 3474178 ++ (4901382, 2) :: (1, 1) :: repeat (1, 2) 29403094 ++ w) 1)
         (HB [33; 19; 0] 111 1 188 ((2, 2) :: (340, 2) :: (1, 1) :: repeat (1, 2) 877 ++ (229, 2) :: (1, 1) :: repeat (1, 2) 3736 ++ (17260, 2) :: (1, 1) :: repeat (1, 2) 58213 ++ (1716045, 2) :: (1, 1) :: repeat (1, 2) 3474178 ++ (4901382, 2) :: (1, 1) :: repeat (1, 2) 29403094 ++ w) 1).
Proof.
  intro w.
  (* step 122: M pop12 (3,) *)
  apply (hsteps_trans _ (HB [] 4 1 13 ((2, 2) :: (4, 2) :: (1, 1) :: repeat (1, 2) 45 ++ (94, 2) :: (1, 1) :: repeat (1, 2) 437 ++ (120, 2) :: (1, 1) :: repeat (1, 2) 1866 ++ (24734, 2) :: (1, 1) :: repeat (1, 2) 58213 ++ (1716045, 2) :: (1, 1) :: repeat (1, 2) 3474178 ++ (4901382, 2) :: (1, 1) :: repeat (1, 2) 29403094 ++ w) 1)).
  {
    apply (pop12 3 [] 1 7 ((2, 2) :: (4, 2) :: (1, 1) :: repeat (1, 2) 45 ++ (94, 2) :: (1, 1) :: repeat (1, 2) 437 ++ (120, 2) :: (1, 1) :: repeat (1, 2) 1866 ++ (24734, 2) :: (1, 1) :: repeat (1, 2) 58213 ++ (1716045, 2) :: (1, 1) :: repeat (1, 2) 3474178 ++ (4901382, 2) :: (1, 1) :: repeat (1, 2) 29403094 ++ w) 1); closearith.
  }
  (* step 123: P TUP2_1 *)
  apply (hsteps_trans _ (HC [5] 13 1 2 ((2, 2) :: (1, 1) :: repeat (1, 2) 45 ++ (94, 2) :: (1, 1) :: repeat (1, 2) 437 ++ (120, 2) :: (1, 1) :: repeat (1, 2) 1866 ++ (24734, 2) :: (1, 1) :: repeat (1, 2) 58213 ++ (1716045, 2) :: (1, 1) :: repeat (1, 2) 3474178 ++ (4901382, 2) :: (1, 1) :: repeat (1, 2) 29403094 ++ w) 1)).
  {
    replace ((2, 2) :: (1, 1) :: repeat (1, 2) 45 ++ (94, 2) :: (1, 1) :: repeat (1, 2) 437 ++ (120, 2) :: (1, 1) :: repeat (1, 2) 1866 ++ (24734, 2) :: (1, 1) :: repeat (1, 2) 58213 ++ (1716045, 2) :: (1, 1) :: repeat (1, 2) 3474178 ++ (4901382, 2) :: (1, 1) :: repeat (1, 2) 29403094 ++ w) with ((4 - 2, 2) :: (1, 1) :: repeat (1, 2) 45 ++ (94, 2) :: (1, 1) :: repeat (1, 2) 437 ++ (120, 2) :: (1, 1) :: repeat (1, 2) 1866 ++ (24734, 2) :: (1, 1) :: repeat (1, 2) 58213 ++ (1716045, 2) :: (1, 1) :: repeat (1, 2) 3474178 ++ (4901382, 2) :: (1, 1) :: repeat (1, 2) 29403094 ++ w) by sec_eq.
    apply (sTUP2_1 [] 4 12 4 ((1, 1) :: repeat (1, 2) 45 ++ (94, 2) :: (1, 1) :: repeat (1, 2) 437 ++ (120, 2) :: (1, 1) :: repeat (1, 2) 1866 ++ (24734, 2) :: (1, 1) :: repeat (1, 2) 58213 ++ (1716045, 2) :: (1, 1) :: repeat (1, 2) 3474178 ++ (4901382, 2) :: (1, 1) :: repeat (1, 2) 29403094 ++ w) 1); closearith.
  }
  (* step 124: P TDN *)
  apply (hsteps_trans _ (HB [5] 13 1 4 ((2, 2) :: (1, 1) :: repeat (1, 2) 45 ++ (94, 2) :: (1, 1) :: repeat (1, 2) 437 ++ (120, 2) :: (1, 1) :: repeat (1, 2) 1866 ++ (24734, 2) :: (1, 1) :: repeat (1, 2) 58213 ++ (1716045, 2) :: (1, 1) :: repeat (1, 2) 3474178 ++ (4901382, 2) :: (1, 1) :: repeat (1, 2) 29403094 ++ w) 1)).
  {
    apply (sTDN [5] 13 ((2, 2) :: (1, 1) :: repeat (1, 2) 45 ++ (94, 2) :: (1, 1) :: repeat (1, 2) 437 ++ (120, 2) :: (1, 1) :: repeat (1, 2) 1866 ++ (24734, 2) :: (1, 1) :: repeat (1, 2) 58213 ++ (1716045, 2) :: (1, 1) :: repeat (1, 2) 3474178 ++ (4901382, 2) :: (1, 1) :: repeat (1, 2) 29403094 ++ w) 1).
  }
  (* step 125: P TRANS2_1 *)
  apply (hsteps_trans _ (HB [14; 5] 5 1 3 (repeat (1, 2) 45 ++ (94, 2) :: (1, 1) :: repeat (1, 2) 437 ++ (120, 2) :: (1, 1) :: repeat (1, 2) 1866 ++ (24734, 2) :: (1, 1) :: repeat (1, 2) 58213 ++ (1716045, 2) :: (1, 1) :: repeat (1, 2) 3474178 ++ (4901382, 2) :: (1, 1) :: repeat (1, 2) 29403094 ++ w) 1)).
  {
    apply (sTRANS2_1 [5] 13 3 1 (repeat (1, 2) 45 ++ (94, 2) :: (1, 1) :: repeat (1, 2) 437 ++ (120, 2) :: (1, 1) :: repeat (1, 2) 1866 ++ (24734, 2) :: (1, 1) :: repeat (1, 2) 58213 ++ (1716045, 2) :: (1, 1) :: repeat (1, 2) 3474178 ++ (4901382, 2) :: (1, 1) :: repeat (1, 2) 29403094 ++ w) 1); closearith.
  }
  (* step 126: M pop12 (45,) *)
  apply (hsteps_trans _ (HB [14; 5] 50 1 93 ((94, 2) :: (1, 1) :: repeat (1, 2) 437 ++ (120, 2) :: (1, 1) :: repeat (1, 2) 1866 ++ (24734, 2) :: (1, 1) :: repeat (1, 2) 58213 ++ (1716045, 2) :: (1, 1) :: repeat (1, 2) 3474178 ++ (4901382, 2) :: (1, 1) :: repeat (1, 2) 29403094 ++ w) 1)).
  {
    apply (pop12 45 [14; 5] 5 3 ((94, 2) :: (1, 1) :: repeat (1, 2) 437 ++ (120, 2) :: (1, 1) :: repeat (1, 2) 1866 ++ (24734, 2) :: (1, 1) :: repeat (1, 2) 58213 ++ (1716045, 2) :: (1, 1) :: repeat (1, 2) 3474178 ++ (4901382, 2) :: (1, 1) :: repeat (1, 2) 29403094 ++ w) 1); closearith.
  }
  (* step 127: sTUP *)
  apply (hsteps_trans _ (HC [14; 5] 50 92 2 ((92, 2) :: (1, 1) :: repeat (1, 2) 437 ++ (120, 2) :: (1, 1) :: repeat (1, 2) 1866 ++ (24734, 2) :: (1, 1) :: repeat (1, 2) 58213 ++ (1716045, 2) :: (1, 1) :: repeat (1, 2) 3474178 ++ (4901382, 2) :: (1, 1) :: repeat (1, 2) 29403094 ++ w) 1)).
  {
    replace ((92, 2) :: (1, 1) :: repeat (1, 2) 437 ++ (120, 2) :: (1, 1) :: repeat (1, 2) 1866 ++ (24734, 2) :: (1, 1) :: repeat (1, 2) 58213 ++ (1716045, 2) :: (1, 1) :: repeat (1, 2) 3474178 ++ (4901382, 2) :: (1, 1) :: repeat (1, 2) 29403094 ++ w) with ((94 - 2, 2) :: (1, 1) :: repeat (1, 2) 437 ++ (120, 2) :: (1, 1) :: repeat (1, 2) 1866 ++ (24734, 2) :: (1, 1) :: repeat (1, 2) 58213 ++ (1716045, 2) :: (1, 1) :: repeat (1, 2) 3474178 ++ (4901382, 2) :: (1, 1) :: repeat (1, 2) 29403094 ++ w) by sec_eq.
    apply (sTUP [14; 5] 50 93 94 2 ((1, 1) :: repeat (1, 2) 437 ++ (120, 2) :: (1, 1) :: repeat (1, 2) 1866 ++ (24734, 2) :: (1, 1) :: repeat (1, 2) 58213 ++ (1716045, 2) :: (1, 1) :: repeat (1, 2) 3474178 ++ (4901382, 2) :: (1, 1) :: repeat (1, 2) 29403094 ++ w) 1); closearith.
  }
  (* step 128: hGRIND_even 44 *)
  apply (hsteps_trans _ (HB [14; 5] 49 1 92 ((2, 2) :: (92, 2) :: (1, 1) :: repeat (1, 2) 437 ++ (120, 2) :: (1, 1) :: repeat (1, 2) 1866 ++ (24734, 2) :: (1, 1) :: repeat (1, 2) 58213 ++ (1716045, 2) :: (1, 1) :: repeat (1, 2) 3474178 ++ (4901382, 2) :: (1, 1) :: repeat (1, 2) 29403094 ++ w) 1)).
  {
    apply (hGRIND_even 44 [14; 5] 49 ((92, 2) :: (1, 1) :: repeat (1, 2) 437 ++ (120, 2) :: (1, 1) :: repeat (1, 2) 1866 ++ (24734, 2) :: (1, 1) :: repeat (1, 2) 58213 ++ (1716045, 2) :: (1, 1) :: repeat (1, 2) 3474178 ++ (4901382, 2) :: (1, 1) :: repeat (1, 2) 29403094 ++ w) 1); closearith.
  }
  (* step 129: P TUP2_1 *)
  apply (hsteps_trans _ (HC [50; 14; 5] 92 1 2 ((90, 2) :: (1, 1) :: repeat (1, 2) 437 ++ (120, 2) :: (1, 1) :: repeat (1, 2) 1866 ++ (24734, 2) :: (1, 1) :: repeat (1, 2) 58213 ++ (1716045, 2) :: (1, 1) :: repeat (1, 2) 3474178 ++ (4901382, 2) :: (1, 1) :: repeat (1, 2) 29403094 ++ w) 1)).
  {
    replace ((90, 2) :: (1, 1) :: repeat (1, 2) 437 ++ (120, 2) :: (1, 1) :: repeat (1, 2) 1866 ++ (24734, 2) :: (1, 1) :: repeat (1, 2) 58213 ++ (1716045, 2) :: (1, 1) :: repeat (1, 2) 3474178 ++ (4901382, 2) :: (1, 1) :: repeat (1, 2) 29403094 ++ w) with ((92 - 2, 2) :: (1, 1) :: repeat (1, 2) 437 ++ (120, 2) :: (1, 1) :: repeat (1, 2) 1866 ++ (24734, 2) :: (1, 1) :: repeat (1, 2) 58213 ++ (1716045, 2) :: (1, 1) :: repeat (1, 2) 3474178 ++ (4901382, 2) :: (1, 1) :: repeat (1, 2) 29403094 ++ w) by sec_eq.
    apply (sTUP2_1 [14; 5] 49 91 92 ((1, 1) :: repeat (1, 2) 437 ++ (120, 2) :: (1, 1) :: repeat (1, 2) 1866 ++ (24734, 2) :: (1, 1) :: repeat (1, 2) 58213 ++ (1716045, 2) :: (1, 1) :: repeat (1, 2) 3474178 ++ (4901382, 2) :: (1, 1) :: repeat (1, 2) 29403094 ++ w) 1); closearith.
  }
  (* step 130: P TDN *)
  apply (hsteps_trans _ (HB [50; 14; 5] 92 1 4 ((90, 2) :: (1, 1) :: repeat (1, 2) 437 ++ (120, 2) :: (1, 1) :: repeat (1, 2) 1866 ++ (24734, 2) :: (1, 1) :: repeat (1, 2) 58213 ++ (1716045, 2) :: (1, 1) :: repeat (1, 2) 3474178 ++ (4901382, 2) :: (1, 1) :: repeat (1, 2) 29403094 ++ w) 1)).
  {
    apply (sTDN [50; 14; 5] 92 ((90, 2) :: (1, 1) :: repeat (1, 2) 437 ++ (120, 2) :: (1, 1) :: repeat (1, 2) 1866 ++ (24734, 2) :: (1, 1) :: repeat (1, 2) 58213 ++ (1716045, 2) :: (1, 1) :: repeat (1, 2) 3474178 ++ (4901382, 2) :: (1, 1) :: repeat (1, 2) 29403094 ++ w) 1).
  }
  (* step 131: sTUP *)
  apply (hsteps_trans _ (HC [50; 14; 5] 92 3 2 ((88, 2) :: (1, 1) :: repeat (1, 2) 437 ++ (120, 2) :: (1, 1) :: repeat (1, 2) 1866 ++ (24734, 2) :: (1, 1) :: repeat (1, 2) 58213 ++ (1716045, 2) :: (1, 1) :: repeat (1, 2) 3474178 ++ (4901382, 2) :: (1, 1) :: repeat (1, 2) 29403094 ++ w) 1)).
  {
    replace ((88, 2) :: (1, 1) :: repeat (1, 2) 437 ++ (120, 2) :: (1, 1) :: repeat (1, 2) 1866 ++ (24734, 2) :: (1, 1) :: repeat (1, 2) 58213 ++ (1716045, 2) :: (1, 1) :: repeat (1, 2) 3474178 ++ (4901382, 2) :: (1, 1) :: repeat (1, 2) 29403094 ++ w) with ((90 - 2, 2) :: (1, 1) :: repeat (1, 2) 437 ++ (120, 2) :: (1, 1) :: repeat (1, 2) 1866 ++ (24734, 2) :: (1, 1) :: repeat (1, 2) 58213 ++ (1716045, 2) :: (1, 1) :: repeat (1, 2) 3474178 ++ (4901382, 2) :: (1, 1) :: repeat (1, 2) 29403094 ++ w) by sec_eq.
    apply (sTUP [50; 14; 5] 92 4 90 2 ((1, 1) :: repeat (1, 2) 437 ++ (120, 2) :: (1, 1) :: repeat (1, 2) 1866 ++ (24734, 2) :: (1, 1) :: repeat (1, 2) 58213 ++ (1716045, 2) :: (1, 1) :: repeat (1, 2) 3474178 ++ (4901382, 2) :: (1, 1) :: repeat (1, 2) 29403094 ++ w) 1); closearith.
  }
  (* step 132: CLEANG_even 43 *)
  apply (hsteps_trans _ (HB [50; 14; 5] 92 1 92 ((2, 2) :: (1, 1) :: repeat (1, 2) 437 ++ (120, 2) :: (1, 1) :: repeat (1, 2) 1866 ++ (24734, 2) :: (1, 1) :: repeat (1, 2) 58213 ++ (1716045, 2) :: (1, 1) :: repeat (1, 2) 3474178 ++ (4901382, 2) :: (1, 1) :: repeat (1, 2) 29403094 ++ w) 1)).
  {
    apply (CLEANG_even 43 [50; 14; 5] 92 ((1, 1) :: repeat (1, 2) 437 ++ (120, 2) :: (1, 1) :: repeat (1, 2) 1866 ++ (24734, 2) :: (1, 1) :: repeat (1, 2) 58213 ++ (1716045, 2) :: (1, 1) :: repeat (1, 2) 3474178 ++ (4901382, 2) :: (1, 1) :: repeat (1, 2) 29403094 ++ w) 1); closearith.
  }
  (* step 133: P TRANS2_1 *)
  apply (hsteps_trans _ (HB [93; 50; 14; 5] 93 1 3 (repeat (1, 2) 437 ++ (120, 2) :: (1, 1) :: repeat (1, 2) 1866 ++ (24734, 2) :: (1, 1) :: repeat (1, 2) 58213 ++ (1716045, 2) :: (1, 1) :: repeat (1, 2) 3474178 ++ (4901382, 2) :: (1, 1) :: repeat (1, 2) 29403094 ++ w) 1)).
  {
    apply (sTRANS2_1 [50; 14; 5] 92 91 1 (repeat (1, 2) 437 ++ (120, 2) :: (1, 1) :: repeat (1, 2) 1866 ++ (24734, 2) :: (1, 1) :: repeat (1, 2) 58213 ++ (1716045, 2) :: (1, 1) :: repeat (1, 2) 3474178 ++ (4901382, 2) :: (1, 1) :: repeat (1, 2) 29403094 ++ w) 1); closearith.
  }
  (* step 134: M pop12 (437,) *)
  apply (hsteps_trans _ (HB [93; 50; 14; 5] 530 1 877 ((120, 2) :: (1, 1) :: repeat (1, 2) 1866 ++ (24734, 2) :: (1, 1) :: repeat (1, 2) 58213 ++ (1716045, 2) :: (1, 1) :: repeat (1, 2) 3474178 ++ (4901382, 2) :: (1, 1) :: repeat (1, 2) 29403094 ++ w) 1)).
  {
    apply (pop12 437 [93; 50; 14; 5] 93 3 ((120, 2) :: (1, 1) :: repeat (1, 2) 1866 ++ (24734, 2) :: (1, 1) :: repeat (1, 2) 58213 ++ (1716045, 2) :: (1, 1) :: repeat (1, 2) 3474178 ++ (4901382, 2) :: (1, 1) :: repeat (1, 2) 29403094 ++ w) 1); closearith.
  }
  (* step 135: sTUP *)
  apply (hsteps_trans _ (HC [93; 50; 14; 5] 530 876 2 ((118, 2) :: (1, 1) :: repeat (1, 2) 1866 ++ (24734, 2) :: (1, 1) :: repeat (1, 2) 58213 ++ (1716045, 2) :: (1, 1) :: repeat (1, 2) 3474178 ++ (4901382, 2) :: (1, 1) :: repeat (1, 2) 29403094 ++ w) 1)).
  {
    replace ((118, 2) :: (1, 1) :: repeat (1, 2) 1866 ++ (24734, 2) :: (1, 1) :: repeat (1, 2) 58213 ++ (1716045, 2) :: (1, 1) :: repeat (1, 2) 3474178 ++ (4901382, 2) :: (1, 1) :: repeat (1, 2) 29403094 ++ w) with ((120 - 2, 2) :: (1, 1) :: repeat (1, 2) 1866 ++ (24734, 2) :: (1, 1) :: repeat (1, 2) 58213 ++ (1716045, 2) :: (1, 1) :: repeat (1, 2) 3474178 ++ (4901382, 2) :: (1, 1) :: repeat (1, 2) 29403094 ++ w) by sec_eq.
    apply (sTUP [93; 50; 14; 5] 530 877 120 2 ((1, 1) :: repeat (1, 2) 1866 ++ (24734, 2) :: (1, 1) :: repeat (1, 2) 58213 ++ (1716045, 2) :: (1, 1) :: repeat (1, 2) 3474178 ++ (4901382, 2) :: (1, 1) :: repeat (1, 2) 29403094 ++ w) 1); closearith.
  }
  (* step 136: hGRIND_even 436 *)
  apply (hsteps_trans _ (HB [93; 50; 14; 5] 529 1 876 ((2, 2) :: (118, 2) :: (1, 1) :: repeat (1, 2) 1866 ++ (24734, 2) :: (1, 1) :: repeat (1, 2) 58213 ++ (1716045, 2) :: (1, 1) :: repeat (1, 2) 3474178 ++ (4901382, 2) :: (1, 1) :: repeat (1, 2) 29403094 ++ w) 1)).
  {
    apply (hGRIND_even 436 [93; 50; 14; 5] 529 ((118, 2) :: (1, 1) :: repeat (1, 2) 1866 ++ (24734, 2) :: (1, 1) :: repeat (1, 2) 58213 ++ (1716045, 2) :: (1, 1) :: repeat (1, 2) 3474178 ++ (4901382, 2) :: (1, 1) :: repeat (1, 2) 29403094 ++ w) 1); closearith.
  }
  (* step 137: P TUP2_1 *)
  apply (hsteps_trans _ (HC [530; 93; 50; 14; 5] 876 1 2 ((116, 2) :: (1, 1) :: repeat (1, 2) 1866 ++ (24734, 2) :: (1, 1) :: repeat (1, 2) 58213 ++ (1716045, 2) :: (1, 1) :: repeat (1, 2) 3474178 ++ (4901382, 2) :: (1, 1) :: repeat (1, 2) 29403094 ++ w) 1)).
  {
    replace ((116, 2) :: (1, 1) :: repeat (1, 2) 1866 ++ (24734, 2) :: (1, 1) :: repeat (1, 2) 58213 ++ (1716045, 2) :: (1, 1) :: repeat (1, 2) 3474178 ++ (4901382, 2) :: (1, 1) :: repeat (1, 2) 29403094 ++ w) with ((118 - 2, 2) :: (1, 1) :: repeat (1, 2) 1866 ++ (24734, 2) :: (1, 1) :: repeat (1, 2) 58213 ++ (1716045, 2) :: (1, 1) :: repeat (1, 2) 3474178 ++ (4901382, 2) :: (1, 1) :: repeat (1, 2) 29403094 ++ w) by sec_eq.
    apply (sTUP2_1 [93; 50; 14; 5] 529 875 118 ((1, 1) :: repeat (1, 2) 1866 ++ (24734, 2) :: (1, 1) :: repeat (1, 2) 58213 ++ (1716045, 2) :: (1, 1) :: repeat (1, 2) 3474178 ++ (4901382, 2) :: (1, 1) :: repeat (1, 2) 29403094 ++ w) 1); closearith.
  }
  (* step 138: P TDN *)
  apply (hsteps_trans _ (HB [530; 93; 50; 14; 5] 876 1 4 ((116, 2) :: (1, 1) :: repeat (1, 2) 1866 ++ (24734, 2) :: (1, 1) :: repeat (1, 2) 58213 ++ (1716045, 2) :: (1, 1) :: repeat (1, 2) 3474178 ++ (4901382, 2) :: (1, 1) :: repeat (1, 2) 29403094 ++ w) 1)).
  {
    apply (sTDN [530; 93; 50; 14; 5] 876 ((116, 2) :: (1, 1) :: repeat (1, 2) 1866 ++ (24734, 2) :: (1, 1) :: repeat (1, 2) 58213 ++ (1716045, 2) :: (1, 1) :: repeat (1, 2) 3474178 ++ (4901382, 2) :: (1, 1) :: repeat (1, 2) 29403094 ++ w) 1).
  }
  (* step 139: sTUP *)
  apply (hsteps_trans _ (HC [530; 93; 50; 14; 5] 876 3 2 ((114, 2) :: (1, 1) :: repeat (1, 2) 1866 ++ (24734, 2) :: (1, 1) :: repeat (1, 2) 58213 ++ (1716045, 2) :: (1, 1) :: repeat (1, 2) 3474178 ++ (4901382, 2) :: (1, 1) :: repeat (1, 2) 29403094 ++ w) 1)).
  {
    replace ((114, 2) :: (1, 1) :: repeat (1, 2) 1866 ++ (24734, 2) :: (1, 1) :: repeat (1, 2) 58213 ++ (1716045, 2) :: (1, 1) :: repeat (1, 2) 3474178 ++ (4901382, 2) :: (1, 1) :: repeat (1, 2) 29403094 ++ w) with ((116 - 2, 2) :: (1, 1) :: repeat (1, 2) 1866 ++ (24734, 2) :: (1, 1) :: repeat (1, 2) 58213 ++ (1716045, 2) :: (1, 1) :: repeat (1, 2) 3474178 ++ (4901382, 2) :: (1, 1) :: repeat (1, 2) 29403094 ++ w) by sec_eq.
    apply (sTUP [530; 93; 50; 14; 5] 876 4 116 2 ((1, 1) :: repeat (1, 2) 1866 ++ (24734, 2) :: (1, 1) :: repeat (1, 2) 58213 ++ (1716045, 2) :: (1, 1) :: repeat (1, 2) 3474178 ++ (4901382, 2) :: (1, 1) :: repeat (1, 2) 29403094 ++ w) 1); closearith.
  }
  (* step 140: CLEANG_even 56 *)
  apply (hsteps_trans _ (HB [530; 93; 50; 14; 5] 876 1 118 ((2, 2) :: (1, 1) :: repeat (1, 2) 1866 ++ (24734, 2) :: (1, 1) :: repeat (1, 2) 58213 ++ (1716045, 2) :: (1, 1) :: repeat (1, 2) 3474178 ++ (4901382, 2) :: (1, 1) :: repeat (1, 2) 29403094 ++ w) 1)).
  {
    apply (CLEANG_even 56 [530; 93; 50; 14; 5] 876 ((1, 1) :: repeat (1, 2) 1866 ++ (24734, 2) :: (1, 1) :: repeat (1, 2) 58213 ++ (1716045, 2) :: (1, 1) :: repeat (1, 2) 3474178 ++ (4901382, 2) :: (1, 1) :: repeat (1, 2) 29403094 ++ w) 1); closearith.
  }
  (* step 141: P TRANS2_1 *)
  apply (hsteps_trans _ (HB [877; 530; 93; 50; 14; 5] 119 1 3 (repeat (1, 2) 1866 ++ (24734, 2) :: (1, 1) :: repeat (1, 2) 58213 ++ (1716045, 2) :: (1, 1) :: repeat (1, 2) 3474178 ++ (4901382, 2) :: (1, 1) :: repeat (1, 2) 29403094 ++ w) 1)).
  {
    apply (sTRANS2_1 [530; 93; 50; 14; 5] 876 117 1 (repeat (1, 2) 1866 ++ (24734, 2) :: (1, 1) :: repeat (1, 2) 58213 ++ (1716045, 2) :: (1, 1) :: repeat (1, 2) 3474178 ++ (4901382, 2) :: (1, 1) :: repeat (1, 2) 29403094 ++ w) 1); closearith.
  }
  (* step 142: M pop12 (1866,) *)
  apply (hsteps_trans _ (HB [877; 530; 93; 50; 14; 5] 1985 1 3735 ((24734, 2) :: (1, 1) :: repeat (1, 2) 58213 ++ (1716045, 2) :: (1, 1) :: repeat (1, 2) 3474178 ++ (4901382, 2) :: (1, 1) :: repeat (1, 2) 29403094 ++ w) 1)).
  {
    apply (pop12 1866 [877; 530; 93; 50; 14; 5] 119 3 ((24734, 2) :: (1, 1) :: repeat (1, 2) 58213 ++ (1716045, 2) :: (1, 1) :: repeat (1, 2) 3474178 ++ (4901382, 2) :: (1, 1) :: repeat (1, 2) 29403094 ++ w) 1); closearith.
  }
  (* step 143: sTUP *)
  apply (hsteps_trans _ (HC [877; 530; 93; 50; 14; 5] 1985 3734 2 ((24732, 2) :: (1, 1) :: repeat (1, 2) 58213 ++ (1716045, 2) :: (1, 1) :: repeat (1, 2) 3474178 ++ (4901382, 2) :: (1, 1) :: repeat (1, 2) 29403094 ++ w) 1)).
  {
    replace ((24732, 2) :: (1, 1) :: repeat (1, 2) 58213 ++ (1716045, 2) :: (1, 1) :: repeat (1, 2) 3474178 ++ (4901382, 2) :: (1, 1) :: repeat (1, 2) 29403094 ++ w) with ((24734 - 2, 2) :: (1, 1) :: repeat (1, 2) 58213 ++ (1716045, 2) :: (1, 1) :: repeat (1, 2) 3474178 ++ (4901382, 2) :: (1, 1) :: repeat (1, 2) 29403094 ++ w) by sec_eq.
    apply (sTUP [877; 530; 93; 50; 14; 5] 1985 3735 24734 2 ((1, 1) :: repeat (1, 2) 58213 ++ (1716045, 2) :: (1, 1) :: repeat (1, 2) 3474178 ++ (4901382, 2) :: (1, 1) :: repeat (1, 2) 29403094 ++ w) 1); closearith.
  }
  (* step 144: hGRIND_even 1865 *)
  apply (hsteps_trans _ (HB [877; 530; 93; 50; 14; 5] 1984 1 3734 ((2, 2) :: (24732, 2) :: (1, 1) :: repeat (1, 2) 58213 ++ (1716045, 2) :: (1, 1) :: repeat (1, 2) 3474178 ++ (4901382, 2) :: (1, 1) :: repeat (1, 2) 29403094 ++ w) 1)).
  {
    apply (hGRIND_even 1865 [877; 530; 93; 50; 14; 5] 1984 ((24732, 2) :: (1, 1) :: repeat (1, 2) 58213 ++ (1716045, 2) :: (1, 1) :: repeat (1, 2) 3474178 ++ (4901382, 2) :: (1, 1) :: repeat (1, 2) 29403094 ++ w) 1); closearith.
  }
  (* step 145: P TUP2_1 *)
  apply (hsteps_trans _ (HC [1985; 877; 530; 93; 50; 14; 5] 3734 1 2 ((24730, 2) :: (1, 1) :: repeat (1, 2) 58213 ++ (1716045, 2) :: (1, 1) :: repeat (1, 2) 3474178 ++ (4901382, 2) :: (1, 1) :: repeat (1, 2) 29403094 ++ w) 1)).
  {
    replace ((24730, 2) :: (1, 1) :: repeat (1, 2) 58213 ++ (1716045, 2) :: (1, 1) :: repeat (1, 2) 3474178 ++ (4901382, 2) :: (1, 1) :: repeat (1, 2) 29403094 ++ w) with ((24732 - 2, 2) :: (1, 1) :: repeat (1, 2) 58213 ++ (1716045, 2) :: (1, 1) :: repeat (1, 2) 3474178 ++ (4901382, 2) :: (1, 1) :: repeat (1, 2) 29403094 ++ w) by sec_eq.
    apply (sTUP2_1 [877; 530; 93; 50; 14; 5] 1984 3733 24732 ((1, 1) :: repeat (1, 2) 58213 ++ (1716045, 2) :: (1, 1) :: repeat (1, 2) 3474178 ++ (4901382, 2) :: (1, 1) :: repeat (1, 2) 29403094 ++ w) 1); closearith.
  }
  (* step 146: P TDN *)
  apply (hsteps_trans _ (HB [1985; 877; 530; 93; 50; 14; 5] 3734 1 4 ((24730, 2) :: (1, 1) :: repeat (1, 2) 58213 ++ (1716045, 2) :: (1, 1) :: repeat (1, 2) 3474178 ++ (4901382, 2) :: (1, 1) :: repeat (1, 2) 29403094 ++ w) 1)).
  {
    apply (sTDN [1985; 877; 530; 93; 50; 14; 5] 3734 ((24730, 2) :: (1, 1) :: repeat (1, 2) 58213 ++ (1716045, 2) :: (1, 1) :: repeat (1, 2) 3474178 ++ (4901382, 2) :: (1, 1) :: repeat (1, 2) 29403094 ++ w) 1).
  }
  (* step 147: sTUP *)
  apply (hsteps_trans _ (HC [1985; 877; 530; 93; 50; 14; 5] 3734 3 2 ((24728, 2) :: (1, 1) :: repeat (1, 2) 58213 ++ (1716045, 2) :: (1, 1) :: repeat (1, 2) 3474178 ++ (4901382, 2) :: (1, 1) :: repeat (1, 2) 29403094 ++ w) 1)).
  {
    replace ((24728, 2) :: (1, 1) :: repeat (1, 2) 58213 ++ (1716045, 2) :: (1, 1) :: repeat (1, 2) 3474178 ++ (4901382, 2) :: (1, 1) :: repeat (1, 2) 29403094 ++ w) with ((24730 - 2, 2) :: (1, 1) :: repeat (1, 2) 58213 ++ (1716045, 2) :: (1, 1) :: repeat (1, 2) 3474178 ++ (4901382, 2) :: (1, 1) :: repeat (1, 2) 29403094 ++ w) by sec_eq.
    apply (sTUP [1985; 877; 530; 93; 50; 14; 5] 3734 4 24730 2 ((1, 1) :: repeat (1, 2) 58213 ++ (1716045, 2) :: (1, 1) :: repeat (1, 2) 3474178 ++ (4901382, 2) :: (1, 1) :: repeat (1, 2) 29403094 ++ w) 1); closearith.
  }
  (* step 148: DIPGRIND 3734 17260 *)
  apply (hsteps_trans _ (HC [1985; 877; 530; 93; 50; 14; 5] 0 3 2 (repeat (1, 2) 3734 ++ (17260, 2) :: (1, 1) :: repeat (1, 2) 58213 ++ (1716045, 2) :: (1, 1) :: repeat (1, 2) 3474178 ++ (4901382, 2) :: (1, 1) :: repeat (1, 2) 29403094 ++ w) 1)).
  {
    apply (DIPGRIND 3734 17260 [1985; 877; 530; 93; 50; 14; 5] ((1, 1) :: repeat (1, 2) 58213 ++ (1716045, 2) :: (1, 1) :: repeat (1, 2) 3474178 ++ (4901382, 2) :: (1, 1) :: repeat (1, 2) 29403094 ++ w) 1); closearith.
  }
  (* step 149: P PX2A *)
  apply (hsteps_trans _ (HC [530; 93; 50; 14; 5] 876 1983 2 ((1, 1) :: repeat (1, 2) 3736 ++ (17260, 2) :: (1, 1) :: repeat (1, 2) 58213 ++ (1716045, 2) :: (1, 1) :: repeat (1, 2) 3474178 ++ (4901382, 2) :: (1, 1) :: repeat (1, 2) 29403094 ++ w) 1)).
  {
    exact (hsteps_step _ _ _ (hPX2A 1982 876 [530; 93; 50; 14; 5] (repeat (1, 2) 3734 ++ (17260, 2) :: (1, 1) :: repeat (1, 2) 58213 ++ (1716045, 2) :: (1, 1) :: repeat (1, 2) 3474178 ++ (4901382, 2) :: (1, 1) :: repeat (1, 2) 29403094 ++ w) 1) (hsteps_refl _)).
  }
  (* step 150: P PUSH *)
  apply (hsteps_trans _ (HC [530; 93; 50; 14; 5] 875 1 2 ((1981, 2) :: (1, 1) :: repeat (1, 2) 3736 ++ (17260, 2) :: (1, 1) :: repeat (1, 2) 58213 ++ (1716045, 2) :: (1, 1) :: repeat (1, 2) 3474178 ++ (4901382, 2) :: (1, 1) :: repeat (1, 2) 29403094 ++ w) 1)).
  {
    replace ((1981, 2) :: (1, 1) :: repeat (1, 2) 3736 ++ (17260, 2) :: (1, 1) :: repeat (1, 2) 58213 ++ (1716045, 2) :: (1, 1) :: repeat (1, 2) 3474178 ++ (4901382, 2) :: (1, 1) :: repeat (1, 2) 29403094 ++ w) with ((1983 - 2, 2) :: (1, 1) :: repeat (1, 2) 3736 ++ (17260, 2) :: (1, 1) :: repeat (1, 2) 58213 ++ (1716045, 2) :: (1, 1) :: repeat (1, 2) 3474178 ++ (4901382, 2) :: (1, 1) :: repeat (1, 2) 29403094 ++ w) by sec_eq.
    apply (sPUSH [530; 93; 50; 14; 5] 875 1983 ((1, 1) :: repeat (1, 2) 3736 ++ (17260, 2) :: (1, 1) :: repeat (1, 2) 58213 ++ (1716045, 2) :: (1, 1) :: repeat (1, 2) 3474178 ++ (4901382, 2) :: (1, 1) :: repeat (1, 2) 29403094 ++ w) 1); closearith.
  }
  (* step 151: P TDN *)
  apply (hsteps_trans _ (HB [530; 93; 50; 14; 5] 875 1 4 ((1981, 2) :: (1, 1) :: repeat (1, 2) 3736 ++ (17260, 2) :: (1, 1) :: repeat (1, 2) 58213 ++ (1716045, 2) :: (1, 1) :: repeat (1, 2) 3474178 ++ (4901382, 2) :: (1, 1) :: repeat (1, 2) 29403094 ++ w) 1)).
  {
    apply (sTDN [530; 93; 50; 14; 5] 875 ((1981, 2) :: (1, 1) :: repeat (1, 2) 3736 ++ (17260, 2) :: (1, 1) :: repeat (1, 2) 58213 ++ (1716045, 2) :: (1, 1) :: repeat (1, 2) 3474178 ++ (4901382, 2) :: (1, 1) :: repeat (1, 2) 29403094 ++ w) 1).
  }
  (* step 152: sTUP *)
  apply (hsteps_trans _ (HC [530; 93; 50; 14; 5] 875 3 2 ((1979, 2) :: (1, 1) :: repeat (1, 2) 3736 ++ (17260, 2) :: (1, 1) :: repeat (1, 2) 58213 ++ (1716045, 2) :: (1, 1) :: repeat (1, 2) 3474178 ++ (4901382, 2) :: (1, 1) :: repeat (1, 2) 29403094 ++ w) 1)).
  {
    replace ((1979, 2) :: (1, 1) :: repeat (1, 2) 3736 ++ (17260, 2) :: (1, 1) :: repeat (1, 2) 58213 ++ (1716045, 2) :: (1, 1) :: repeat (1, 2) 3474178 ++ (4901382, 2) :: (1, 1) :: repeat (1, 2) 29403094 ++ w) with ((1981 - 2, 2) :: (1, 1) :: repeat (1, 2) 3736 ++ (17260, 2) :: (1, 1) :: repeat (1, 2) 58213 ++ (1716045, 2) :: (1, 1) :: repeat (1, 2) 3474178 ++ (4901382, 2) :: (1, 1) :: repeat (1, 2) 29403094 ++ w) by sec_eq.
    apply (sTUP [530; 93; 50; 14; 5] 875 4 1981 2 ((1, 1) :: repeat (1, 2) 3736 ++ (17260, 2) :: (1, 1) :: repeat (1, 2) 58213 ++ (1716045, 2) :: (1, 1) :: repeat (1, 2) 3474178 ++ (4901382, 2) :: (1, 1) :: repeat (1, 2) 29403094 ++ w) 1); closearith.
  }
  (* step 153: DIPGRIND 875 229 *)
  apply (hsteps_trans _ (HC [530; 93; 50; 14; 5] 0 3 2 (repeat (1, 2) 875 ++ (229, 2) :: (1, 1) :: repeat (1, 2) 3736 ++ (17260, 2) :: (1, 1) :: repeat (1, 2) 58213 ++ (1716045, 2) :: (1, 1) :: repeat (1, 2) 3474178 ++ (4901382, 2) :: (1, 1) :: repeat (1, 2) 29403094 ++ w) 1)).
  {
    apply (DIPGRIND 875 229 [530; 93; 50; 14; 5] ((1, 1) :: repeat (1, 2) 3736 ++ (17260, 2) :: (1, 1) :: repeat (1, 2) 58213 ++ (1716045, 2) :: (1, 1) :: repeat (1, 2) 3474178 ++ (4901382, 2) :: (1, 1) :: repeat (1, 2) 29403094 ++ w) 1); closearith.
  }
  (* step 154: P PX2A *)
  apply (hsteps_trans _ (HC [50; 14; 5] 92 528 2 ((1, 1) :: repeat (1, 2) 877 ++ (229, 2) :: (1, 1) :: repeat (1, 2) 3736 ++ (17260, 2) :: (1, 1) :: repeat (1, 2) 58213 ++ (1716045, 2) :: (1, 1) :: repeat (1, 2) 3474178 ++ (4901382, 2) :: (1, 1) :: repeat (1, 2) 29403094 ++ w) 1)).
  {
    exact (hsteps_step _ _ _ (hPX2A 527 92 [50; 14; 5] (repeat (1, 2) 875 ++ (229, 2) :: (1, 1) :: repeat (1, 2) 3736 ++ (17260, 2) :: (1, 1) :: repeat (1, 2) 58213 ++ (1716045, 2) :: (1, 1) :: repeat (1, 2) 3474178 ++ (4901382, 2) :: (1, 1) :: repeat (1, 2) 29403094 ++ w) 1) (hsteps_refl _)).
  }
  (* step 155: P PUSH *)
  apply (hsteps_trans _ (HC [50; 14; 5] 91 1 2 ((526, 2) :: (1, 1) :: repeat (1, 2) 877 ++ (229, 2) :: (1, 1) :: repeat (1, 2) 3736 ++ (17260, 2) :: (1, 1) :: repeat (1, 2) 58213 ++ (1716045, 2) :: (1, 1) :: repeat (1, 2) 3474178 ++ (4901382, 2) :: (1, 1) :: repeat (1, 2) 29403094 ++ w) 1)).
  {
    replace ((526, 2) :: (1, 1) :: repeat (1, 2) 877 ++ (229, 2) :: (1, 1) :: repeat (1, 2) 3736 ++ (17260, 2) :: (1, 1) :: repeat (1, 2) 58213 ++ (1716045, 2) :: (1, 1) :: repeat (1, 2) 3474178 ++ (4901382, 2) :: (1, 1) :: repeat (1, 2) 29403094 ++ w) with ((528 - 2, 2) :: (1, 1) :: repeat (1, 2) 877 ++ (229, 2) :: (1, 1) :: repeat (1, 2) 3736 ++ (17260, 2) :: (1, 1) :: repeat (1, 2) 58213 ++ (1716045, 2) :: (1, 1) :: repeat (1, 2) 3474178 ++ (4901382, 2) :: (1, 1) :: repeat (1, 2) 29403094 ++ w) by sec_eq.
    apply (sPUSH [50; 14; 5] 91 528 ((1, 1) :: repeat (1, 2) 877 ++ (229, 2) :: (1, 1) :: repeat (1, 2) 3736 ++ (17260, 2) :: (1, 1) :: repeat (1, 2) 58213 ++ (1716045, 2) :: (1, 1) :: repeat (1, 2) 3474178 ++ (4901382, 2) :: (1, 1) :: repeat (1, 2) 29403094 ++ w) 1); closearith.
  }
  (* step 156: P TDN *)
  apply (hsteps_trans _ (HB [50; 14; 5] 91 1 4 ((526, 2) :: (1, 1) :: repeat (1, 2) 877 ++ (229, 2) :: (1, 1) :: repeat (1, 2) 3736 ++ (17260, 2) :: (1, 1) :: repeat (1, 2) 58213 ++ (1716045, 2) :: (1, 1) :: repeat (1, 2) 3474178 ++ (4901382, 2) :: (1, 1) :: repeat (1, 2) 29403094 ++ w) 1)).
  {
    apply (sTDN [50; 14; 5] 91 ((526, 2) :: (1, 1) :: repeat (1, 2) 877 ++ (229, 2) :: (1, 1) :: repeat (1, 2) 3736 ++ (17260, 2) :: (1, 1) :: repeat (1, 2) 58213 ++ (1716045, 2) :: (1, 1) :: repeat (1, 2) 3474178 ++ (4901382, 2) :: (1, 1) :: repeat (1, 2) 29403094 ++ w) 1).
  }
  (* step 157: sTUP *)
  apply (hsteps_trans _ (HC [50; 14; 5] 91 3 2 ((524, 2) :: (1, 1) :: repeat (1, 2) 877 ++ (229, 2) :: (1, 1) :: repeat (1, 2) 3736 ++ (17260, 2) :: (1, 1) :: repeat (1, 2) 58213 ++ (1716045, 2) :: (1, 1) :: repeat (1, 2) 3474178 ++ (4901382, 2) :: (1, 1) :: repeat (1, 2) 29403094 ++ w) 1)).
  {
    replace ((524, 2) :: (1, 1) :: repeat (1, 2) 877 ++ (229, 2) :: (1, 1) :: repeat (1, 2) 3736 ++ (17260, 2) :: (1, 1) :: repeat (1, 2) 58213 ++ (1716045, 2) :: (1, 1) :: repeat (1, 2) 3474178 ++ (4901382, 2) :: (1, 1) :: repeat (1, 2) 29403094 ++ w) with ((526 - 2, 2) :: (1, 1) :: repeat (1, 2) 877 ++ (229, 2) :: (1, 1) :: repeat (1, 2) 3736 ++ (17260, 2) :: (1, 1) :: repeat (1, 2) 58213 ++ (1716045, 2) :: (1, 1) :: repeat (1, 2) 3474178 ++ (4901382, 2) :: (1, 1) :: repeat (1, 2) 29403094 ++ w) by sec_eq.
    apply (sTUP [50; 14; 5] 91 4 526 2 ((1, 1) :: repeat (1, 2) 877 ++ (229, 2) :: (1, 1) :: repeat (1, 2) 3736 ++ (17260, 2) :: (1, 1) :: repeat (1, 2) 58213 ++ (1716045, 2) :: (1, 1) :: repeat (1, 2) 3474178 ++ (4901382, 2) :: (1, 1) :: repeat (1, 2) 29403094 ++ w) 1); closearith.
  }
  (* step 158: DIPGRIND 91 342 *)
  apply (hsteps_trans _ (HC [50; 14; 5] 0 3 2 (repeat (1, 2) 91 ++ (342, 2) :: (1, 1) :: repeat (1, 2) 877 ++ (229, 2) :: (1, 1) :: repeat (1, 2) 3736 ++ (17260, 2) :: (1, 1) :: repeat (1, 2) 58213 ++ (1716045, 2) :: (1, 1) :: repeat (1, 2) 3474178 ++ (4901382, 2) :: (1, 1) :: repeat (1, 2) 29403094 ++ w) 1)).
  {
    apply (DIPGRIND 91 342 [50; 14; 5] ((1, 1) :: repeat (1, 2) 877 ++ (229, 2) :: (1, 1) :: repeat (1, 2) 3736 ++ (17260, 2) :: (1, 1) :: repeat (1, 2) 58213 ++ (1716045, 2) :: (1, 1) :: repeat (1, 2) 3474178 ++ (4901382, 2) :: (1, 1) :: repeat (1, 2) 29403094 ++ w) 1); closearith.
  }
  (* step 159: P PX2A *)
  apply (hsteps_trans _ (HC [5] 13 48 2 ((1, 1) :: repeat (1, 2) 93 ++ (342, 2) :: (1, 1) :: repeat (1, 2) 877 ++ (229, 2) :: (1, 1) :: repeat (1, 2) 3736 ++ (17260, 2) :: (1, 1) :: repeat (1, 2) 58213 ++ (1716045, 2) :: (1, 1) :: repeat (1, 2) 3474178 ++ (4901382, 2) :: (1, 1) :: repeat (1, 2) 29403094 ++ w) 1)).
  {
    exact (hsteps_step _ _ _ (hPX2A 47 13 [5] (repeat (1, 2) 91 ++ (342, 2) :: (1, 1) :: repeat (1, 2) 877 ++ (229, 2) :: (1, 1) :: repeat (1, 2) 3736 ++ (17260, 2) :: (1, 1) :: repeat (1, 2) 58213 ++ (1716045, 2) :: (1, 1) :: repeat (1, 2) 3474178 ++ (4901382, 2) :: (1, 1) :: repeat (1, 2) 29403094 ++ w) 1) (hsteps_refl _)).
  }
  (* step 160: P PUSH *)
  apply (hsteps_trans _ (HC [5] 12 1 2 ((46, 2) :: (1, 1) :: repeat (1, 2) 93 ++ (342, 2) :: (1, 1) :: repeat (1, 2) 877 ++ (229, 2) :: (1, 1) :: repeat (1, 2) 3736 ++ (17260, 2) :: (1, 1) :: repeat (1, 2) 58213 ++ (1716045, 2) :: (1, 1) :: repeat (1, 2) 3474178 ++ (4901382, 2) :: (1, 1) :: repeat (1, 2) 29403094 ++ w) 1)).
  {
    replace ((46, 2) :: (1, 1) :: repeat (1, 2) 93 ++ (342, 2) :: (1, 1) :: repeat (1, 2) 877 ++ (229, 2) :: (1, 1) :: repeat (1, 2) 3736 ++ (17260, 2) :: (1, 1) :: repeat (1, 2) 58213 ++ (1716045, 2) :: (1, 1) :: repeat (1, 2) 3474178 ++ (4901382, 2) :: (1, 1) :: repeat (1, 2) 29403094 ++ w) with ((48 - 2, 2) :: (1, 1) :: repeat (1, 2) 93 ++ (342, 2) :: (1, 1) :: repeat (1, 2) 877 ++ (229, 2) :: (1, 1) :: repeat (1, 2) 3736 ++ (17260, 2) :: (1, 1) :: repeat (1, 2) 58213 ++ (1716045, 2) :: (1, 1) :: repeat (1, 2) 3474178 ++ (4901382, 2) :: (1, 1) :: repeat (1, 2) 29403094 ++ w) by sec_eq.
    apply (sPUSH [5] 12 48 ((1, 1) :: repeat (1, 2) 93 ++ (342, 2) :: (1, 1) :: repeat (1, 2) 877 ++ (229, 2) :: (1, 1) :: repeat (1, 2) 3736 ++ (17260, 2) :: (1, 1) :: repeat (1, 2) 58213 ++ (1716045, 2) :: (1, 1) :: repeat (1, 2) 3474178 ++ (4901382, 2) :: (1, 1) :: repeat (1, 2) 29403094 ++ w) 1); closearith.
  }
  (* step 161: P TDN *)
  apply (hsteps_trans _ (HB [5] 12 1 4 ((46, 2) :: (1, 1) :: repeat (1, 2) 93 ++ (342, 2) :: (1, 1) :: repeat (1, 2) 877 ++ (229, 2) :: (1, 1) :: repeat (1, 2) 3736 ++ (17260, 2) :: (1, 1) :: repeat (1, 2) 58213 ++ (1716045, 2) :: (1, 1) :: repeat (1, 2) 3474178 ++ (4901382, 2) :: (1, 1) :: repeat (1, 2) 29403094 ++ w) 1)).
  {
    apply (sTDN [5] 12 ((46, 2) :: (1, 1) :: repeat (1, 2) 93 ++ (342, 2) :: (1, 1) :: repeat (1, 2) 877 ++ (229, 2) :: (1, 1) :: repeat (1, 2) 3736 ++ (17260, 2) :: (1, 1) :: repeat (1, 2) 58213 ++ (1716045, 2) :: (1, 1) :: repeat (1, 2) 3474178 ++ (4901382, 2) :: (1, 1) :: repeat (1, 2) 29403094 ++ w) 1).
  }
  (* step 162: sTUP *)
  apply (hsteps_trans _ (HC [5] 12 3 2 ((44, 2) :: (1, 1) :: repeat (1, 2) 93 ++ (342, 2) :: (1, 1) :: repeat (1, 2) 877 ++ (229, 2) :: (1, 1) :: repeat (1, 2) 3736 ++ (17260, 2) :: (1, 1) :: repeat (1, 2) 58213 ++ (1716045, 2) :: (1, 1) :: repeat (1, 2) 3474178 ++ (4901382, 2) :: (1, 1) :: repeat (1, 2) 29403094 ++ w) 1)).
  {
    replace ((44, 2) :: (1, 1) :: repeat (1, 2) 93 ++ (342, 2) :: (1, 1) :: repeat (1, 2) 877 ++ (229, 2) :: (1, 1) :: repeat (1, 2) 3736 ++ (17260, 2) :: (1, 1) :: repeat (1, 2) 58213 ++ (1716045, 2) :: (1, 1) :: repeat (1, 2) 3474178 ++ (4901382, 2) :: (1, 1) :: repeat (1, 2) 29403094 ++ w) with ((46 - 2, 2) :: (1, 1) :: repeat (1, 2) 93 ++ (342, 2) :: (1, 1) :: repeat (1, 2) 877 ++ (229, 2) :: (1, 1) :: repeat (1, 2) 3736 ++ (17260, 2) :: (1, 1) :: repeat (1, 2) 58213 ++ (1716045, 2) :: (1, 1) :: repeat (1, 2) 3474178 ++ (4901382, 2) :: (1, 1) :: repeat (1, 2) 29403094 ++ w) by sec_eq.
    apply (sTUP [5] 12 4 46 2 ((1, 1) :: repeat (1, 2) 93 ++ (342, 2) :: (1, 1) :: repeat (1, 2) 877 ++ (229, 2) :: (1, 1) :: repeat (1, 2) 3736 ++ (17260, 2) :: (1, 1) :: repeat (1, 2) 58213 ++ (1716045, 2) :: (1, 1) :: repeat (1, 2) 3474178 ++ (4901382, 2) :: (1, 1) :: repeat (1, 2) 29403094 ++ w) 1); closearith.
  }
  (* step 163: DIPGRIND 12 20 *)
  apply (hsteps_trans _ (HC [5] 0 3 2 (repeat (1, 2) 12 ++ (20, 2) :: (1, 1) :: repeat (1, 2) 93 ++ (342, 2) :: (1, 1) :: repeat (1, 2) 877 ++ (229, 2) :: (1, 1) :: repeat (1, 2) 3736 ++ (17260, 2) :: (1, 1) :: repeat (1, 2) 58213 ++ (1716045, 2) :: (1, 1) :: repeat (1, 2) 3474178 ++ (4901382, 2) :: (1, 1) :: repeat (1, 2) 29403094 ++ w) 1)).
  {
    apply (DIPGRIND 12 20 [5] ((1, 1) :: repeat (1, 2) 93 ++ (342, 2) :: (1, 1) :: repeat (1, 2) 877 ++ (229, 2) :: (1, 1) :: repeat (1, 2) 3736 ++ (17260, 2) :: (1, 1) :: repeat (1, 2) 58213 ++ (1716045, 2) :: (1, 1) :: repeat (1, 2) 3474178 ++ (4901382, 2) :: (1, 1) :: repeat (1, 2) 29403094 ++ w) 1); closearith.
  }
  (* step 164: P PX2Bgen *)
  apply (hsteps_trans _ (HB [0] 3 1 2 (repeat (1, 2) 1 ++ (1, 1) :: repeat (1, 2) 14 ++ (20, 2) :: (1, 1) :: repeat (1, 2) 93 ++ (342, 2) :: (1, 1) :: repeat (1, 2) 877 ++ (229, 2) :: (1, 1) :: repeat (1, 2) 3736 ++ (17260, 2) :: (1, 1) :: repeat (1, 2) 58213 ++ (1716045, 2) :: (1, 1) :: repeat (1, 2) 3474178 ++ (4901382, 2) :: (1, 1) :: repeat (1, 2) 29403094 ++ w) 1)).
  {
    exact (hsteps_step _ _ _ (hPX2Bgen 0 (repeat (1, 2) 12 ++ (20, 2) :: (1, 1) :: repeat (1, 2) 93 ++ (342, 2) :: (1, 1) :: repeat (1, 2) 877 ++ (229, 2) :: (1, 1) :: repeat (1, 2) 3736 ++ (17260, 2) :: (1, 1) :: repeat (1, 2) 58213 ++ (1716045, 2) :: (1, 1) :: repeat (1, 2) 3474178 ++ (4901382, 2) :: (1, 1) :: repeat (1, 2) 29403094 ++ w) 1) (hsteps_refl _)).
  }
  (* step 165: M pop12 (1,) *)
  apply (hsteps_trans _ (HB [0] 4 1 4 ((1, 1) :: repeat (1, 2) 14 ++ (20, 2) :: (1, 1) :: repeat (1, 2) 93 ++ (342, 2) :: (1, 1) :: repeat (1, 2) 877 ++ (229, 2) :: (1, 1) :: repeat (1, 2) 3736 ++ (17260, 2) :: (1, 1) :: repeat (1, 2) 58213 ++ (1716045, 2) :: (1, 1) :: repeat (1, 2) 3474178 ++ (4901382, 2) :: (1, 1) :: repeat (1, 2) 29403094 ++ w) 1)).
  {
    apply (pop12 1 [0] 3 2 ((1, 1) :: repeat (1, 2) 14 ++ (20, 2) :: (1, 1) :: repeat (1, 2) 93 ++ (342, 2) :: (1, 1) :: repeat (1, 2) 877 ++ (229, 2) :: (1, 1) :: repeat (1, 2) 3736 ++ (17260, 2) :: (1, 1) :: repeat (1, 2) 58213 ++ (1716045, 2) :: (1, 1) :: repeat (1, 2) 3474178 ++ (4901382, 2) :: (1, 1) :: repeat (1, 2) 29403094 ++ w) 1); closearith.
  }
  (* step 166: P POP *)
  apply (hsteps_trans _ (HB [0] 5 1 5 (repeat (1, 2) 14 ++ (20, 2) :: (1, 1) :: repeat (1, 2) 93 ++ (342, 2) :: (1, 1) :: repeat (1, 2) 877 ++ (229, 2) :: (1, 1) :: repeat (1, 2) 3736 ++ (17260, 2) :: (1, 1) :: repeat (1, 2) 58213 ++ (1716045, 2) :: (1, 1) :: repeat (1, 2) 3474178 ++ (4901382, 2) :: (1, 1) :: repeat (1, 2) 29403094 ++ w) 1)).
  {
    apply (sPOP1 [0] 4 4 (repeat (1, 2) 14 ++ (20, 2) :: (1, 1) :: repeat (1, 2) 93 ++ (342, 2) :: (1, 1) :: repeat (1, 2) 877 ++ (229, 2) :: (1, 1) :: repeat (1, 2) 3736 ++ (17260, 2) :: (1, 1) :: repeat (1, 2) 58213 ++ (1716045, 2) :: (1, 1) :: repeat (1, 2) 3474178 ++ (4901382, 2) :: (1, 1) :: repeat (1, 2) 29403094 ++ w) 1); closearith.
  }
  (* step 167: M pop12 (14,) *)
  apply (hsteps_trans _ (HB [0] 19 1 33 ((20, 2) :: (1, 1) :: repeat (1, 2) 93 ++ (342, 2) :: (1, 1) :: repeat (1, 2) 877 ++ (229, 2) :: (1, 1) :: repeat (1, 2) 3736 ++ (17260, 2) :: (1, 1) :: repeat (1, 2) 58213 ++ (1716045, 2) :: (1, 1) :: repeat (1, 2) 3474178 ++ (4901382, 2) :: (1, 1) :: repeat (1, 2) 29403094 ++ w) 1)).
  {
    apply (pop12 14 [0] 5 5 ((20, 2) :: (1, 1) :: repeat (1, 2) 93 ++ (342, 2) :: (1, 1) :: repeat (1, 2) 877 ++ (229, 2) :: (1, 1) :: repeat (1, 2) 3736 ++ (17260, 2) :: (1, 1) :: repeat (1, 2) 58213 ++ (1716045, 2) :: (1, 1) :: repeat (1, 2) 3474178 ++ (4901382, 2) :: (1, 1) :: repeat (1, 2) 29403094 ++ w) 1); closearith.
  }
  (* step 168: sTUP *)
  apply (hsteps_trans _ (HC [0] 19 32 2 ((18, 2) :: (1, 1) :: repeat (1, 2) 93 ++ (342, 2) :: (1, 1) :: repeat (1, 2) 877 ++ (229, 2) :: (1, 1) :: repeat (1, 2) 3736 ++ (17260, 2) :: (1, 1) :: repeat (1, 2) 58213 ++ (1716045, 2) :: (1, 1) :: repeat (1, 2) 3474178 ++ (4901382, 2) :: (1, 1) :: repeat (1, 2) 29403094 ++ w) 1)).
  {
    replace ((18, 2) :: (1, 1) :: repeat (1, 2) 93 ++ (342, 2) :: (1, 1) :: repeat (1, 2) 877 ++ (229, 2) :: (1, 1) :: repeat (1, 2) 3736 ++ (17260, 2) :: (1, 1) :: repeat (1, 2) 58213 ++ (1716045, 2) :: (1, 1) :: repeat (1, 2) 3474178 ++ (4901382, 2) :: (1, 1) :: repeat (1, 2) 29403094 ++ w) with ((20 - 2, 2) :: (1, 1) :: repeat (1, 2) 93 ++ (342, 2) :: (1, 1) :: repeat (1, 2) 877 ++ (229, 2) :: (1, 1) :: repeat (1, 2) 3736 ++ (17260, 2) :: (1, 1) :: repeat (1, 2) 58213 ++ (1716045, 2) :: (1, 1) :: repeat (1, 2) 3474178 ++ (4901382, 2) :: (1, 1) :: repeat (1, 2) 29403094 ++ w) by sec_eq.
    apply (sTUP [0] 19 33 20 2 ((1, 1) :: repeat (1, 2) 93 ++ (342, 2) :: (1, 1) :: repeat (1, 2) 877 ++ (229, 2) :: (1, 1) :: repeat (1, 2) 3736 ++ (17260, 2) :: (1, 1) :: repeat (1, 2) 58213 ++ (1716045, 2) :: (1, 1) :: repeat (1, 2) 3474178 ++ (4901382, 2) :: (1, 1) :: repeat (1, 2) 29403094 ++ w) 1); closearith.
  }
  (* step 169: hGRIND_even 14 *)
  apply (hsteps_trans _ (HB [0] 18 1 32 ((2, 2) :: (18, 2) :: (1, 1) :: repeat (1, 2) 93 ++ (342, 2) :: (1, 1) :: repeat (1, 2) 877 ++ (229, 2) :: (1, 1) :: repeat (1, 2) 3736 ++ (17260, 2) :: (1, 1) :: repeat (1, 2) 58213 ++ (1716045, 2) :: (1, 1) :: repeat (1, 2) 3474178 ++ (4901382, 2) :: (1, 1) :: repeat (1, 2) 29403094 ++ w) 1)).
  {
    apply (hGRIND_even 14 [0] 18 ((18, 2) :: (1, 1) :: repeat (1, 2) 93 ++ (342, 2) :: (1, 1) :: repeat (1, 2) 877 ++ (229, 2) :: (1, 1) :: repeat (1, 2) 3736 ++ (17260, 2) :: (1, 1) :: repeat (1, 2) 58213 ++ (1716045, 2) :: (1, 1) :: repeat (1, 2) 3474178 ++ (4901382, 2) :: (1, 1) :: repeat (1, 2) 29403094 ++ w) 1); closearith.
  }
  (* step 170: P TUP2_1 *)
  apply (hsteps_trans _ (HC [19; 0] 32 1 2 ((16, 2) :: (1, 1) :: repeat (1, 2) 93 ++ (342, 2) :: (1, 1) :: repeat (1, 2) 877 ++ (229, 2) :: (1, 1) :: repeat (1, 2) 3736 ++ (17260, 2) :: (1, 1) :: repeat (1, 2) 58213 ++ (1716045, 2) :: (1, 1) :: repeat (1, 2) 3474178 ++ (4901382, 2) :: (1, 1) :: repeat (1, 2) 29403094 ++ w) 1)).
  {
    replace ((16, 2) :: (1, 1) :: repeat (1, 2) 93 ++ (342, 2) :: (1, 1) :: repeat (1, 2) 877 ++ (229, 2) :: (1, 1) :: repeat (1, 2) 3736 ++ (17260, 2) :: (1, 1) :: repeat (1, 2) 58213 ++ (1716045, 2) :: (1, 1) :: repeat (1, 2) 3474178 ++ (4901382, 2) :: (1, 1) :: repeat (1, 2) 29403094 ++ w) with ((18 - 2, 2) :: (1, 1) :: repeat (1, 2) 93 ++ (342, 2) :: (1, 1) :: repeat (1, 2) 877 ++ (229, 2) :: (1, 1) :: repeat (1, 2) 3736 ++ (17260, 2) :: (1, 1) :: repeat (1, 2) 58213 ++ (1716045, 2) :: (1, 1) :: repeat (1, 2) 3474178 ++ (4901382, 2) :: (1, 1) :: repeat (1, 2) 29403094 ++ w) by sec_eq.
    apply (sTUP2_1 [0] 18 31 18 ((1, 1) :: repeat (1, 2) 93 ++ (342, 2) :: (1, 1) :: repeat (1, 2) 877 ++ (229, 2) :: (1, 1) :: repeat (1, 2) 3736 ++ (17260, 2) :: (1, 1) :: repeat (1, 2) 58213 ++ (1716045, 2) :: (1, 1) :: repeat (1, 2) 3474178 ++ (4901382, 2) :: (1, 1) :: repeat (1, 2) 29403094 ++ w) 1); closearith.
  }
  (* step 171: P TDN *)
  apply (hsteps_trans _ (HB [19; 0] 32 1 4 ((16, 2) :: (1, 1) :: repeat (1, 2) 93 ++ (342, 2) :: (1, 1) :: repeat (1, 2) 877 ++ (229, 2) :: (1, 1) :: repeat (1, 2) 3736 ++ (17260, 2) :: (1, 1) :: repeat (1, 2) 58213 ++ (1716045, 2) :: (1, 1) :: repeat (1, 2) 3474178 ++ (4901382, 2) :: (1, 1) :: repeat (1, 2) 29403094 ++ w) 1)).
  {
    apply (sTDN [19; 0] 32 ((16, 2) :: (1, 1) :: repeat (1, 2) 93 ++ (342, 2) :: (1, 1) :: repeat (1, 2) 877 ++ (229, 2) :: (1, 1) :: repeat (1, 2) 3736 ++ (17260, 2) :: (1, 1) :: repeat (1, 2) 58213 ++ (1716045, 2) :: (1, 1) :: repeat (1, 2) 3474178 ++ (4901382, 2) :: (1, 1) :: repeat (1, 2) 29403094 ++ w) 1).
  }
  (* step 172: sTUP *)
  apply (hsteps_trans _ (HC [19; 0] 32 3 2 ((14, 2) :: (1, 1) :: repeat (1, 2) 93 ++ (342, 2) :: (1, 1) :: repeat (1, 2) 877 ++ (229, 2) :: (1, 1) :: repeat (1, 2) 3736 ++ (17260, 2) :: (1, 1) :: repeat (1, 2) 58213 ++ (1716045, 2) :: (1, 1) :: repeat (1, 2) 3474178 ++ (4901382, 2) :: (1, 1) :: repeat (1, 2) 29403094 ++ w) 1)).
  {
    replace ((14, 2) :: (1, 1) :: repeat (1, 2) 93 ++ (342, 2) :: (1, 1) :: repeat (1, 2) 877 ++ (229, 2) :: (1, 1) :: repeat (1, 2) 3736 ++ (17260, 2) :: (1, 1) :: repeat (1, 2) 58213 ++ (1716045, 2) :: (1, 1) :: repeat (1, 2) 3474178 ++ (4901382, 2) :: (1, 1) :: repeat (1, 2) 29403094 ++ w) with ((16 - 2, 2) :: (1, 1) :: repeat (1, 2) 93 ++ (342, 2) :: (1, 1) :: repeat (1, 2) 877 ++ (229, 2) :: (1, 1) :: repeat (1, 2) 3736 ++ (17260, 2) :: (1, 1) :: repeat (1, 2) 58213 ++ (1716045, 2) :: (1, 1) :: repeat (1, 2) 3474178 ++ (4901382, 2) :: (1, 1) :: repeat (1, 2) 29403094 ++ w) by sec_eq.
    apply (sTUP [19; 0] 32 4 16 2 ((1, 1) :: repeat (1, 2) 93 ++ (342, 2) :: (1, 1) :: repeat (1, 2) 877 ++ (229, 2) :: (1, 1) :: repeat (1, 2) 3736 ++ (17260, 2) :: (1, 1) :: repeat (1, 2) 58213 ++ (1716045, 2) :: (1, 1) :: repeat (1, 2) 3474178 ++ (4901382, 2) :: (1, 1) :: repeat (1, 2) 29403094 ++ w) 1); closearith.
  }
  (* step 173: CLEANG_even 6 *)
  apply (hsteps_trans _ (HB [19; 0] 32 1 18 ((2, 2) :: (1, 1) :: repeat (1, 2) 93 ++ (342, 2) :: (1, 1) :: repeat (1, 2) 877 ++ (229, 2) :: (1, 1) :: repeat (1, 2) 3736 ++ (17260, 2) :: (1, 1) :: repeat (1, 2) 58213 ++ (1716045, 2) :: (1, 1) :: repeat (1, 2) 3474178 ++ (4901382, 2) :: (1, 1) :: repeat (1, 2) 29403094 ++ w) 1)).
  {
    apply (CLEANG_even 6 [19; 0] 32 ((1, 1) :: repeat (1, 2) 93 ++ (342, 2) :: (1, 1) :: repeat (1, 2) 877 ++ (229, 2) :: (1, 1) :: repeat (1, 2) 3736 ++ (17260, 2) :: (1, 1) :: repeat (1, 2) 58213 ++ (1716045, 2) :: (1, 1) :: repeat (1, 2) 3474178 ++ (4901382, 2) :: (1, 1) :: repeat (1, 2) 29403094 ++ w) 1); closearith.
  }
  (* step 174: P TRANS2_1 *)
  apply (hsteps_trans _ (HB [33; 19; 0] 19 1 3 (repeat (1, 2) 93 ++ (342, 2) :: (1, 1) :: repeat (1, 2) 877 ++ (229, 2) :: (1, 1) :: repeat (1, 2) 3736 ++ (17260, 2) :: (1, 1) :: repeat (1, 2) 58213 ++ (1716045, 2) :: (1, 1) :: repeat (1, 2) 3474178 ++ (4901382, 2) :: (1, 1) :: repeat (1, 2) 29403094 ++ w) 1)).
  {
    apply (sTRANS2_1 [19; 0] 32 17 1 (repeat (1, 2) 93 ++ (342, 2) :: (1, 1) :: repeat (1, 2) 877 ++ (229, 2) :: (1, 1) :: repeat (1, 2) 3736 ++ (17260, 2) :: (1, 1) :: repeat (1, 2) 58213 ++ (1716045, 2) :: (1, 1) :: repeat (1, 2) 3474178 ++ (4901382, 2) :: (1, 1) :: repeat (1, 2) 29403094 ++ w) 1); closearith.
  }
  (* step 175: M pop12 (93,) *)
  apply (hsteps_trans _ (HB [33; 19; 0] 112 1 189 ((342, 2) :: (1, 1) :: repeat (1, 2) 877 ++ (229, 2) :: (1, 1) :: repeat (1, 2) 3736 ++ (17260, 2) :: (1, 1) :: repeat (1, 2) 58213 ++ (1716045, 2) :: (1, 1) :: repeat (1, 2) 3474178 ++ (4901382, 2) :: (1, 1) :: repeat (1, 2) 29403094 ++ w) 1)).
  {
    apply (pop12 93 [33; 19; 0] 19 3 ((342, 2) :: (1, 1) :: repeat (1, 2) 877 ++ (229, 2) :: (1, 1) :: repeat (1, 2) 3736 ++ (17260, 2) :: (1, 1) :: repeat (1, 2) 58213 ++ (1716045, 2) :: (1, 1) :: repeat (1, 2) 3474178 ++ (4901382, 2) :: (1, 1) :: repeat (1, 2) 29403094 ++ w) 1); closearith.
  }
  (* step 176: sTUP *)
  apply (hsteps_trans _ (HC [33; 19; 0] 112 188 2 ((340, 2) :: (1, 1) :: repeat (1, 2) 877 ++ (229, 2) :: (1, 1) :: repeat (1, 2) 3736 ++ (17260, 2) :: (1, 1) :: repeat (1, 2) 58213 ++ (1716045, 2) :: (1, 1) :: repeat (1, 2) 3474178 ++ (4901382, 2) :: (1, 1) :: repeat (1, 2) 29403094 ++ w) 1)).
  {
    replace ((340, 2) :: (1, 1) :: repeat (1, 2) 877 ++ (229, 2) :: (1, 1) :: repeat (1, 2) 3736 ++ (17260, 2) :: (1, 1) :: repeat (1, 2) 58213 ++ (1716045, 2) :: (1, 1) :: repeat (1, 2) 3474178 ++ (4901382, 2) :: (1, 1) :: repeat (1, 2) 29403094 ++ w) with ((342 - 2, 2) :: (1, 1) :: repeat (1, 2) 877 ++ (229, 2) :: (1, 1) :: repeat (1, 2) 3736 ++ (17260, 2) :: (1, 1) :: repeat (1, 2) 58213 ++ (1716045, 2) :: (1, 1) :: repeat (1, 2) 3474178 ++ (4901382, 2) :: (1, 1) :: repeat (1, 2) 29403094 ++ w) by sec_eq.
    apply (sTUP [33; 19; 0] 112 189 342 2 ((1, 1) :: repeat (1, 2) 877 ++ (229, 2) :: (1, 1) :: repeat (1, 2) 3736 ++ (17260, 2) :: (1, 1) :: repeat (1, 2) 58213 ++ (1716045, 2) :: (1, 1) :: repeat (1, 2) 3474178 ++ (4901382, 2) :: (1, 1) :: repeat (1, 2) 29403094 ++ w) 1); closearith.
  }
  (* step 177: hGRIND_even 92 *)
  apply (hGRIND_even 92 [33; 19; 0] 111 ((340, 2) :: (1, 1) :: repeat (1, 2) 877 ++ (229, 2) :: (1, 1) :: repeat (1, 2) 3736 ++ (17260, 2) :: (1, 1) :: repeat (1, 2) 58213 ++ (1716045, 2) :: (1, 1) :: repeat (1, 2) 3474178 ++ (4901382, 2) :: (1, 1) :: repeat (1, 2) 29403094 ++ w) 1); closearith.
Qed.

(* CASCADE59f: steps 178-233 of the CASCADE59 chain. *)
Lemma CASCADE59f : forall w,
  hsteps (HB [33; 19; 0] 111 1 188 ((2, 2) :: (340, 2) :: (1, 1) :: repeat (1, 2) 877 ++ (229, 2) :: (1, 1) :: repeat (1, 2) 3736 ++ (17260, 2) :: (1, 1) :: repeat (1, 2) 58213 ++ (1716045, 2) :: (1, 1) :: repeat (1, 2) 3474178 ++ (4901382, 2) :: (1, 1) :: repeat (1, 2) 29403094 ++ w) 1)
         (HC [10759; 2627; 1330; 33; 19; 0] 15409 3 2 ((60056, 2) :: (1, 1) :: repeat (1, 2) 116430 ++ (1483183, 2) :: (1, 1) :: repeat (1, 2) 3474178 ++ (4901382, 2) :: (1, 1) :: repeat (1, 2) 29403094 ++ w) 1).
Proof.
  intro w.
  (* step 178: P TUP2_1 *)
  apply (hsteps_trans _ (HC [112; 33; 19; 0] 188 1 2 ((338, 2) :: (1, 1) :: repeat (1, 2) 877 ++ (229, 2) :: (1, 1) :: repeat (1, 2) 3736 ++ (17260, 2) :: (1, 1) :: repeat (1, 2) 58213 ++ (1716045, 2) :: (1, 1) :: repeat (1, 2) 3474178 ++ (4901382, 2) :: (1, 1) :: repeat (1, 2) 29403094 ++ w) 1)).
  {
    replace ((338, 2) :: (1, 1) :: repeat (1, 2) 877 ++ (229, 2) :: (1, 1) :: repeat (1, 2) 3736 ++ (17260, 2) :: (1, 1) :: repeat (1, 2) 58213 ++ (1716045, 2) :: (1, 1) :: repeat (1, 2) 3474178 ++ (4901382, 2) :: (1, 1) :: repeat (1, 2) 29403094 ++ w) with ((340 - 2, 2) :: (1, 1) :: repeat (1, 2) 877 ++ (229, 2) :: (1, 1) :: repeat (1, 2) 3736 ++ (17260, 2) :: (1, 1) :: repeat (1, 2) 58213 ++ (1716045, 2) :: (1, 1) :: repeat (1, 2) 3474178 ++ (4901382, 2) :: (1, 1) :: repeat (1, 2) 29403094 ++ w) by sec_eq.
    apply (sTUP2_1 [33; 19; 0] 111 187 340 ((1, 1) :: repeat (1, 2) 877 ++ (229, 2) :: (1, 1) :: repeat (1, 2) 3736 ++ (17260, 2) :: (1, 1) :: repeat (1, 2) 58213 ++ (1716045, 2) :: (1, 1) :: repeat (1, 2) 3474178 ++ (4901382, 2) :: (1, 1) :: repeat (1, 2) 29403094 ++ w) 1); closearith.
  }
  (* step 179: P TDN *)
  apply (hsteps_trans _ (HB [112; 33; 19; 0] 188 1 4 ((338, 2) :: (1, 1) :: repeat (1, 2) 877 ++ (229, 2) :: (1, 1) :: repeat (1, 2) 3736 ++ (17260, 2) :: (1, 1) :: repeat (1, 2) 58213 ++ (1716045, 2) :: (1, 1) :: repeat (1, 2) 3474178 ++ (4901382, 2) :: (1, 1) :: repeat (1, 2) 29403094 ++ w) 1)).
  {
    apply (sTDN [112; 33; 19; 0] 188 ((338, 2) :: (1, 1) :: repeat (1, 2) 877 ++ (229, 2) :: (1, 1) :: repeat (1, 2) 3736 ++ (17260, 2) :: (1, 1) :: repeat (1, 2) 58213 ++ (1716045, 2) :: (1, 1) :: repeat (1, 2) 3474178 ++ (4901382, 2) :: (1, 1) :: repeat (1, 2) 29403094 ++ w) 1).
  }
  (* step 180: sTUP *)
  apply (hsteps_trans _ (HC [112; 33; 19; 0] 188 3 2 ((336, 2) :: (1, 1) :: repeat (1, 2) 877 ++ (229, 2) :: (1, 1) :: repeat (1, 2) 3736 ++ (17260, 2) :: (1, 1) :: repeat (1, 2) 58213 ++ (1716045, 2) :: (1, 1) :: repeat (1, 2) 3474178 ++ (4901382, 2) :: (1, 1) :: repeat (1, 2) 29403094 ++ w) 1)).
  {
    replace ((336, 2) :: (1, 1) :: repeat (1, 2) 877 ++ (229, 2) :: (1, 1) :: repeat (1, 2) 3736 ++ (17260, 2) :: (1, 1) :: repeat (1, 2) 58213 ++ (1716045, 2) :: (1, 1) :: repeat (1, 2) 3474178 ++ (4901382, 2) :: (1, 1) :: repeat (1, 2) 29403094 ++ w) with ((338 - 2, 2) :: (1, 1) :: repeat (1, 2) 877 ++ (229, 2) :: (1, 1) :: repeat (1, 2) 3736 ++ (17260, 2) :: (1, 1) :: repeat (1, 2) 58213 ++ (1716045, 2) :: (1, 1) :: repeat (1, 2) 3474178 ++ (4901382, 2) :: (1, 1) :: repeat (1, 2) 29403094 ++ w) by sec_eq.
    apply (sTUP [112; 33; 19; 0] 188 4 338 2 ((1, 1) :: repeat (1, 2) 877 ++ (229, 2) :: (1, 1) :: repeat (1, 2) 3736 ++ (17260, 2) :: (1, 1) :: repeat (1, 2) 58213 ++ (1716045, 2) :: (1, 1) :: repeat (1, 2) 3474178 ++ (4901382, 2) :: (1, 1) :: repeat (1, 2) 29403094 ++ w) 1); closearith.
  }
  (* step 181: CLEANG_even 167 *)
  apply (hsteps_trans _ (HB [112; 33; 19; 0] 188 1 340 ((2, 2) :: (1, 1) :: repeat (1, 2) 877 ++ (229, 2) :: (1, 1) :: repeat (1, 2) 3736 ++ (17260, 2) :: (1, 1) :: repeat (1, 2) 58213 ++ (1716045, 2) :: (1, 1) :: repeat (1, 2) 3474178 ++ (4901382, 2) :: (1, 1) :: repeat (1, 2) 29403094 ++ w) 1)).
  {
    apply (CLEANG_even 167 [112; 33; 19; 0] 188 ((1, 1) :: repeat (1, 2) 877 ++ (229, 2) :: (1, 1) :: repeat (1, 2) 3736 ++ (17260, 2) :: (1, 1) :: repeat (1, 2) 58213 ++ (1716045, 2) :: (1, 1) :: repeat (1, 2) 3474178 ++ (4901382, 2) :: (1, 1) :: repeat (1, 2) 29403094 ++ w) 1); closearith.
  }
  (* step 182: P TRANS2_1 *)
  apply (hsteps_trans _ (HB [189; 112; 33; 19; 0] 341 1 3 (repeat (1, 2) 877 ++ (229, 2) :: (1, 1) :: repeat (1, 2) 3736 ++ (17260, 2) :: (1, 1) :: repeat (1, 2) 58213 ++ (1716045, 2) :: (1, 1) :: repeat (1, 2) 3474178 ++ (4901382, 2) :: (1, 1) :: repeat (1, 2) 29403094 ++ w) 1)).
  {
    apply (sTRANS2_1 [112; 33; 19; 0] 188 339 1 (repeat (1, 2) 877 ++ (229, 2) :: (1, 1) :: repeat (1, 2) 3736 ++ (17260, 2) :: (1, 1) :: repeat (1, 2) 58213 ++ (1716045, 2) :: (1, 1) :: repeat (1, 2) 3474178 ++ (4901382, 2) :: (1, 1) :: repeat (1, 2) 29403094 ++ w) 1); closearith.
  }
  (* step 183: M pop12 (877,) *)
  apply (hsteps_trans _ (HB [189; 112; 33; 19; 0] 1218 1 1757 ((229, 2) :: (1, 1) :: repeat (1, 2) 3736 ++ (17260, 2) :: (1, 1) :: repeat (1, 2) 58213 ++ (1716045, 2) :: (1, 1) :: repeat (1, 2) 3474178 ++ (4901382, 2) :: (1, 1) :: repeat (1, 2) 29403094 ++ w) 1)).
  {
    apply (pop12 877 [189; 112; 33; 19; 0] 341 3 ((229, 2) :: (1, 1) :: repeat (1, 2) 3736 ++ (17260, 2) :: (1, 1) :: repeat (1, 2) 58213 ++ (1716045, 2) :: (1, 1) :: repeat (1, 2) 3474178 ++ (4901382, 2) :: (1, 1) :: repeat (1, 2) 29403094 ++ w) 1); closearith.
  }
  (* step 184: sTUP *)
  apply (hsteps_trans _ (HC [189; 112; 33; 19; 0] 1218 1756 2 ((227, 2) :: (1, 1) :: repeat (1, 2) 3736 ++ (17260, 2) :: (1, 1) :: repeat (1, 2) 58213 ++ (1716045, 2) :: (1, 1) :: repeat (1, 2) 3474178 ++ (4901382, 2) :: (1, 1) :: repeat (1, 2) 29403094 ++ w) 1)).
  {
    replace ((227, 2) :: (1, 1) :: repeat (1, 2) 3736 ++ (17260, 2) :: (1, 1) :: repeat (1, 2) 58213 ++ (1716045, 2) :: (1, 1) :: repeat (1, 2) 3474178 ++ (4901382, 2) :: (1, 1) :: repeat (1, 2) 29403094 ++ w) with ((229 - 2, 2) :: (1, 1) :: repeat (1, 2) 3736 ++ (17260, 2) :: (1, 1) :: repeat (1, 2) 58213 ++ (1716045, 2) :: (1, 1) :: repeat (1, 2) 3474178 ++ (4901382, 2) :: (1, 1) :: repeat (1, 2) 29403094 ++ w) by sec_eq.
    apply (sTUP [189; 112; 33; 19; 0] 1218 1757 229 2 ((1, 1) :: repeat (1, 2) 3736 ++ (17260, 2) :: (1, 1) :: repeat (1, 2) 58213 ++ (1716045, 2) :: (1, 1) :: repeat (1, 2) 3474178 ++ (4901382, 2) :: (1, 1) :: repeat (1, 2) 29403094 ++ w) 1); closearith.
  }
  (* step 185: hGRIND_even 876 *)
  apply (hsteps_trans _ (HB [189; 112; 33; 19; 0] 1217 1 1756 ((2, 2) :: (227, 2) :: (1, 1) :: repeat (1, 2) 3736 ++ (17260, 2) :: (1, 1) :: repeat (1, 2) 58213 ++ (1716045, 2) :: (1, 1) :: repeat (1, 2) 3474178 ++ (4901382, 2) :: (1, 1) :: repeat (1, 2) 29403094 ++ w) 1)).
  {
    apply (hGRIND_even 876 [189; 112; 33; 19; 0] 1217 ((227, 2) :: (1, 1) :: repeat (1, 2) 3736 ++ (17260, 2) :: (1, 1) :: repeat (1, 2) 58213 ++ (1716045, 2) :: (1, 1) :: repeat (1, 2) 3474178 ++ (4901382, 2) :: (1, 1) :: repeat (1, 2) 29403094 ++ w) 1); closearith.
  }
  (* step 186: P TUP2_1 *)
  apply (hsteps_trans _ (HC [1218; 189; 112; 33; 19; 0] 1756 1 2 ((225, 2) :: (1, 1) :: repeat (1, 2) 3736 ++ (17260, 2) :: (1, 1) :: repeat (1, 2) 58213 ++ (1716045, 2) :: (1, 1) :: repeat (1, 2) 3474178 ++ (4901382, 2) :: (1, 1) :: repeat (1, 2) 29403094 ++ w) 1)).
  {
    replace ((225, 2) :: (1, 1) :: repeat (1, 2) 3736 ++ (17260, 2) :: (1, 1) :: repeat (1, 2) 58213 ++ (1716045, 2) :: (1, 1) :: repeat (1, 2) 3474178 ++ (4901382, 2) :: (1, 1) :: repeat (1, 2) 29403094 ++ w) with ((227 - 2, 2) :: (1, 1) :: repeat (1, 2) 3736 ++ (17260, 2) :: (1, 1) :: repeat (1, 2) 58213 ++ (1716045, 2) :: (1, 1) :: repeat (1, 2) 3474178 ++ (4901382, 2) :: (1, 1) :: repeat (1, 2) 29403094 ++ w) by sec_eq.
    apply (sTUP2_1 [189; 112; 33; 19; 0] 1217 1755 227 ((1, 1) :: repeat (1, 2) 3736 ++ (17260, 2) :: (1, 1) :: repeat (1, 2) 58213 ++ (1716045, 2) :: (1, 1) :: repeat (1, 2) 3474178 ++ (4901382, 2) :: (1, 1) :: repeat (1, 2) 29403094 ++ w) 1); closearith.
  }
  (* step 187: P TDN *)
  apply (hsteps_trans _ (HB [1218; 189; 112; 33; 19; 0] 1756 1 4 ((225, 2) :: (1, 1) :: repeat (1, 2) 3736 ++ (17260, 2) :: (1, 1) :: repeat (1, 2) 58213 ++ (1716045, 2) :: (1, 1) :: repeat (1, 2) 3474178 ++ (4901382, 2) :: (1, 1) :: repeat (1, 2) 29403094 ++ w) 1)).
  {
    apply (sTDN [1218; 189; 112; 33; 19; 0] 1756 ((225, 2) :: (1, 1) :: repeat (1, 2) 3736 ++ (17260, 2) :: (1, 1) :: repeat (1, 2) 58213 ++ (1716045, 2) :: (1, 1) :: repeat (1, 2) 3474178 ++ (4901382, 2) :: (1, 1) :: repeat (1, 2) 29403094 ++ w) 1).
  }
  (* step 188: sTUP *)
  apply (hsteps_trans _ (HC [1218; 189; 112; 33; 19; 0] 1756 3 2 ((223, 2) :: (1, 1) :: repeat (1, 2) 3736 ++ (17260, 2) :: (1, 1) :: repeat (1, 2) 58213 ++ (1716045, 2) :: (1, 1) :: repeat (1, 2) 3474178 ++ (4901382, 2) :: (1, 1) :: repeat (1, 2) 29403094 ++ w) 1)).
  {
    replace ((223, 2) :: (1, 1) :: repeat (1, 2) 3736 ++ (17260, 2) :: (1, 1) :: repeat (1, 2) 58213 ++ (1716045, 2) :: (1, 1) :: repeat (1, 2) 3474178 ++ (4901382, 2) :: (1, 1) :: repeat (1, 2) 29403094 ++ w) with ((225 - 2, 2) :: (1, 1) :: repeat (1, 2) 3736 ++ (17260, 2) :: (1, 1) :: repeat (1, 2) 58213 ++ (1716045, 2) :: (1, 1) :: repeat (1, 2) 3474178 ++ (4901382, 2) :: (1, 1) :: repeat (1, 2) 29403094 ++ w) by sec_eq.
    apply (sTUP [1218; 189; 112; 33; 19; 0] 1756 4 225 2 ((1, 1) :: repeat (1, 2) 3736 ++ (17260, 2) :: (1, 1) :: repeat (1, 2) 58213 ++ (1716045, 2) :: (1, 1) :: repeat (1, 2) 3474178 ++ (4901382, 2) :: (1, 1) :: repeat (1, 2) 29403094 ++ w) 1); closearith.
  }
  (* step 189: CLEANG_odd 110 *)
  apply (hsteps_trans _ (HB [1218; 189; 112; 33; 19; 0] 1756 1 228 (repeat (1, 2) 1 ++ (1, 1) :: repeat (1, 2) 3736 ++ (17260, 2) :: (1, 1) :: repeat (1, 2) 58213 ++ (1716045, 2) :: (1, 1) :: repeat (1, 2) 3474178 ++ (4901382, 2) :: (1, 1) :: repeat (1, 2) 29403094 ++ w) 1)).
  {
    replace (repeat (1, 2) 1 ++ (1, 1) :: repeat (1, 2) 3736 ++ (17260, 2) :: (1, 1) :: repeat (1, 2) 58213 ++ (1716045, 2) :: (1, 1) :: repeat (1, 2) 3474178 ++ (4901382, 2) :: (1, 1) :: repeat (1, 2) 29403094 ++ w) with ((1, 2) :: (1, 1) :: repeat (1, 2) 3736 ++ (17260, 2) :: (1, 1) :: repeat (1, 2) 58213 ++ (1716045, 2) :: (1, 1) :: repeat (1, 2) 3474178 ++ (4901382, 2) :: (1, 1) :: repeat (1, 2) 29403094 ++ w) by sec_eq.
    apply (CLEANG_odd 110 [1218; 189; 112; 33; 19; 0] 1756 ((1, 1) :: repeat (1, 2) 3736 ++ (17260, 2) :: (1, 1) :: repeat (1, 2) 58213 ++ (1716045, 2) :: (1, 1) :: repeat (1, 2) 3474178 ++ (4901382, 2) :: (1, 1) :: repeat (1, 2) 29403094 ++ w) 1); closearith.
  }
  (* step 190: M pop12 (1,) *)
  apply (hsteps_trans _ (HB [1218; 189; 112; 33; 19; 0] 1757 1 230 ((1, 1) :: repeat (1, 2) 3736 ++ (17260, 2) :: (1, 1) :: repeat (1, 2) 58213 ++ (1716045, 2) :: (1, 1) :: repeat (1, 2) 3474178 ++ (4901382, 2) :: (1, 1) :: repeat (1, 2) 29403094 ++ w) 1)).
  {
    apply (pop12 1 [1218; 189; 112; 33; 19; 0] 1756 228 ((1, 1) :: repeat (1, 2) 3736 ++ (17260, 2) :: (1, 1) :: repeat (1, 2) 58213 ++ (1716045, 2) :: (1, 1) :: repeat (1, 2) 3474178 ++ (4901382, 2) :: (1, 1) :: repeat (1, 2) 29403094 ++ w) 1); closearith.
  }
  (* step 191: P POP *)
  apply (hsteps_trans _ (HB [1218; 189; 112; 33; 19; 0] 1758 1 231 (repeat (1, 2) 3736 ++ (17260, 2) :: (1, 1) :: repeat (1, 2) 58213 ++ (1716045, 2) :: (1, 1) :: repeat (1, 2) 3474178 ++ (4901382, 2) :: (1, 1) :: repeat (1, 2) 29403094 ++ w) 1)).
  {
    apply (sPOP1 [1218; 189; 112; 33; 19; 0] 1757 230 (repeat (1, 2) 3736 ++ (17260, 2) :: (1, 1) :: repeat (1, 2) 58213 ++ (1716045, 2) :: (1, 1) :: repeat (1, 2) 3474178 ++ (4901382, 2) :: (1, 1) :: repeat (1, 2) 29403094 ++ w) 1); closearith.
  }
  (* step 192: M pop12 (3736,) *)
  apply (hsteps_trans _ (HB [1218; 189; 112; 33; 19; 0] 5494 1 7703 ((17260, 2) :: (1, 1) :: repeat (1, 2) 58213 ++ (1716045, 2) :: (1, 1) :: repeat (1, 2) 3474178 ++ (4901382, 2) :: (1, 1) :: repeat (1, 2) 29403094 ++ w) 1)).
  {
    apply (pop12 3736 [1218; 189; 112; 33; 19; 0] 1758 231 ((17260, 2) :: (1, 1) :: repeat (1, 2) 58213 ++ (1716045, 2) :: (1, 1) :: repeat (1, 2) 3474178 ++ (4901382, 2) :: (1, 1) :: repeat (1, 2) 29403094 ++ w) 1); closearith.
  }
  (* step 193: sTUP *)
  apply (hsteps_trans _ (HC [1218; 189; 112; 33; 19; 0] 5494 7702 2 ((17258, 2) :: (1, 1) :: repeat (1, 2) 58213 ++ (1716045, 2) :: (1, 1) :: repeat (1, 2) 3474178 ++ (4901382, 2) :: (1, 1) :: repeat (1, 2) 29403094 ++ w) 1)).
  {
    replace ((17258, 2) :: (1, 1) :: repeat (1, 2) 58213 ++ (1716045, 2) :: (1, 1) :: repeat (1, 2) 3474178 ++ (4901382, 2) :: (1, 1) :: repeat (1, 2) 29403094 ++ w) with ((17260 - 2, 2) :: (1, 1) :: repeat (1, 2) 58213 ++ (1716045, 2) :: (1, 1) :: repeat (1, 2) 3474178 ++ (4901382, 2) :: (1, 1) :: repeat (1, 2) 29403094 ++ w) by sec_eq.
    apply (sTUP [1218; 189; 112; 33; 19; 0] 5494 7703 17260 2 ((1, 1) :: repeat (1, 2) 58213 ++ (1716045, 2) :: (1, 1) :: repeat (1, 2) 3474178 ++ (4901382, 2) :: (1, 1) :: repeat (1, 2) 29403094 ++ w) 1); closearith.
  }
  (* step 194: hGRIND_even 3849 *)
  apply (hsteps_trans _ (HB [1218; 189; 112; 33; 19; 0] 5493 1 7702 ((2, 2) :: (17258, 2) :: (1, 1) :: repeat (1, 2) 58213 ++ (1716045, 2) :: (1, 1) :: repeat (1, 2) 3474178 ++ (4901382, 2) :: (1, 1) :: repeat (1, 2) 29403094 ++ w) 1)).
  {
    apply (hGRIND_even 3849 [1218; 189; 112; 33; 19; 0] 5493 ((17258, 2) :: (1, 1) :: repeat (1, 2) 58213 ++ (1716045, 2) :: (1, 1) :: repeat (1, 2) 3474178 ++ (4901382, 2) :: (1, 1) :: repeat (1, 2) 29403094 ++ w) 1); closearith.
  }
  (* step 195: P TUP2_1 *)
  apply (hsteps_trans _ (HC [5494; 1218; 189; 112; 33; 19; 0] 7702 1 2 ((17256, 2) :: (1, 1) :: repeat (1, 2) 58213 ++ (1716045, 2) :: (1, 1) :: repeat (1, 2) 3474178 ++ (4901382, 2) :: (1, 1) :: repeat (1, 2) 29403094 ++ w) 1)).
  {
    replace ((17256, 2) :: (1, 1) :: repeat (1, 2) 58213 ++ (1716045, 2) :: (1, 1) :: repeat (1, 2) 3474178 ++ (4901382, 2) :: (1, 1) :: repeat (1, 2) 29403094 ++ w) with ((17258 - 2, 2) :: (1, 1) :: repeat (1, 2) 58213 ++ (1716045, 2) :: (1, 1) :: repeat (1, 2) 3474178 ++ (4901382, 2) :: (1, 1) :: repeat (1, 2) 29403094 ++ w) by sec_eq.
    apply (sTUP2_1 [1218; 189; 112; 33; 19; 0] 5493 7701 17258 ((1, 1) :: repeat (1, 2) 58213 ++ (1716045, 2) :: (1, 1) :: repeat (1, 2) 3474178 ++ (4901382, 2) :: (1, 1) :: repeat (1, 2) 29403094 ++ w) 1); closearith.
  }
  (* step 196: P TDN *)
  apply (hsteps_trans _ (HB [5494; 1218; 189; 112; 33; 19; 0] 7702 1 4 ((17256, 2) :: (1, 1) :: repeat (1, 2) 58213 ++ (1716045, 2) :: (1, 1) :: repeat (1, 2) 3474178 ++ (4901382, 2) :: (1, 1) :: repeat (1, 2) 29403094 ++ w) 1)).
  {
    apply (sTDN [5494; 1218; 189; 112; 33; 19; 0] 7702 ((17256, 2) :: (1, 1) :: repeat (1, 2) 58213 ++ (1716045, 2) :: (1, 1) :: repeat (1, 2) 3474178 ++ (4901382, 2) :: (1, 1) :: repeat (1, 2) 29403094 ++ w) 1).
  }
  (* step 197: sTUP *)
  apply (hsteps_trans _ (HC [5494; 1218; 189; 112; 33; 19; 0] 7702 3 2 ((17254, 2) :: (1, 1) :: repeat (1, 2) 58213 ++ (1716045, 2) :: (1, 1) :: repeat (1, 2) 3474178 ++ (4901382, 2) :: (1, 1) :: repeat (1, 2) 29403094 ++ w) 1)).
  {
    replace ((17254, 2) :: (1, 1) :: repeat (1, 2) 58213 ++ (1716045, 2) :: (1, 1) :: repeat (1, 2) 3474178 ++ (4901382, 2) :: (1, 1) :: repeat (1, 2) 29403094 ++ w) with ((17256 - 2, 2) :: (1, 1) :: repeat (1, 2) 58213 ++ (1716045, 2) :: (1, 1) :: repeat (1, 2) 3474178 ++ (4901382, 2) :: (1, 1) :: repeat (1, 2) 29403094 ++ w) by sec_eq.
    apply (sTUP [5494; 1218; 189; 112; 33; 19; 0] 7702 4 17256 2 ((1, 1) :: repeat (1, 2) 58213 ++ (1716045, 2) :: (1, 1) :: repeat (1, 2) 3474178 ++ (4901382, 2) :: (1, 1) :: repeat (1, 2) 29403094 ++ w) 1); closearith.
  }
  (* step 198: DIPGRIND 7702 1850 *)
  apply (hsteps_trans _ (HC [5494; 1218; 189; 112; 33; 19; 0] 0 3 2 (repeat (1, 2) 7702 ++ (1850, 2) :: (1, 1) :: repeat (1, 2) 58213 ++ (1716045, 2) :: (1, 1) :: repeat (1, 2) 3474178 ++ (4901382, 2) :: (1, 1) :: repeat (1, 2) 29403094 ++ w) 1)).
  {
    apply (DIPGRIND 7702 1850 [5494; 1218; 189; 112; 33; 19; 0] ((1, 1) :: repeat (1, 2) 58213 ++ (1716045, 2) :: (1, 1) :: repeat (1, 2) 3474178 ++ (4901382, 2) :: (1, 1) :: repeat (1, 2) 29403094 ++ w) 1); closearith.
  }
  (* step 199: P PX2A *)
  apply (hsteps_trans _ (HC [189; 112; 33; 19; 0] 1217 5492 2 ((1, 1) :: repeat (1, 2) 7704 ++ (1850, 2) :: (1, 1) :: repeat (1, 2) 58213 ++ (1716045, 2) :: (1, 1) :: repeat (1, 2) 3474178 ++ (4901382, 2) :: (1, 1) :: repeat (1, 2) 29403094 ++ w) 1)).
  {
    exact (hsteps_step _ _ _ (hPX2A 5491 1217 [189; 112; 33; 19; 0] (repeat (1, 2) 7702 ++ (1850, 2) :: (1, 1) :: repeat (1, 2) 58213 ++ (1716045, 2) :: (1, 1) :: repeat (1, 2) 3474178 ++ (4901382, 2) :: (1, 1) :: repeat (1, 2) 29403094 ++ w) 1) (hsteps_refl _)).
  }
  (* step 200: P PUSH *)
  apply (hsteps_trans _ (HC [189; 112; 33; 19; 0] 1216 1 2 ((5490, 2) :: (1, 1) :: repeat (1, 2) 7704 ++ (1850, 2) :: (1, 1) :: repeat (1, 2) 58213 ++ (1716045, 2) :: (1, 1) :: repeat (1, 2) 3474178 ++ (4901382, 2) :: (1, 1) :: repeat (1, 2) 29403094 ++ w) 1)).
  {
    replace ((5490, 2) :: (1, 1) :: repeat (1, 2) 7704 ++ (1850, 2) :: (1, 1) :: repeat (1, 2) 58213 ++ (1716045, 2) :: (1, 1) :: repeat (1, 2) 3474178 ++ (4901382, 2) :: (1, 1) :: repeat (1, 2) 29403094 ++ w) with ((5492 - 2, 2) :: (1, 1) :: repeat (1, 2) 7704 ++ (1850, 2) :: (1, 1) :: repeat (1, 2) 58213 ++ (1716045, 2) :: (1, 1) :: repeat (1, 2) 3474178 ++ (4901382, 2) :: (1, 1) :: repeat (1, 2) 29403094 ++ w) by sec_eq.
    apply (sPUSH [189; 112; 33; 19; 0] 1216 5492 ((1, 1) :: repeat (1, 2) 7704 ++ (1850, 2) :: (1, 1) :: repeat (1, 2) 58213 ++ (1716045, 2) :: (1, 1) :: repeat (1, 2) 3474178 ++ (4901382, 2) :: (1, 1) :: repeat (1, 2) 29403094 ++ w) 1); closearith.
  }
  (* step 201: P TDN *)
  apply (hsteps_trans _ (HB [189; 112; 33; 19; 0] 1216 1 4 ((5490, 2) :: (1, 1) :: repeat (1, 2) 7704 ++ (1850, 2) :: (1, 1) :: repeat (1, 2) 58213 ++ (1716045, 2) :: (1, 1) :: repeat (1, 2) 3474178 ++ (4901382, 2) :: (1, 1) :: repeat (1, 2) 29403094 ++ w) 1)).
  {
    apply (sTDN [189; 112; 33; 19; 0] 1216 ((5490, 2) :: (1, 1) :: repeat (1, 2) 7704 ++ (1850, 2) :: (1, 1) :: repeat (1, 2) 58213 ++ (1716045, 2) :: (1, 1) :: repeat (1, 2) 3474178 ++ (4901382, 2) :: (1, 1) :: repeat (1, 2) 29403094 ++ w) 1).
  }
  (* step 202: sTUP *)
  apply (hsteps_trans _ (HC [189; 112; 33; 19; 0] 1216 3 2 ((5488, 2) :: (1, 1) :: repeat (1, 2) 7704 ++ (1850, 2) :: (1, 1) :: repeat (1, 2) 58213 ++ (1716045, 2) :: (1, 1) :: repeat (1, 2) 3474178 ++ (4901382, 2) :: (1, 1) :: repeat (1, 2) 29403094 ++ w) 1)).
  {
    replace ((5488, 2) :: (1, 1) :: repeat (1, 2) 7704 ++ (1850, 2) :: (1, 1) :: repeat (1, 2) 58213 ++ (1716045, 2) :: (1, 1) :: repeat (1, 2) 3474178 ++ (4901382, 2) :: (1, 1) :: repeat (1, 2) 29403094 ++ w) with ((5490 - 2, 2) :: (1, 1) :: repeat (1, 2) 7704 ++ (1850, 2) :: (1, 1) :: repeat (1, 2) 58213 ++ (1716045, 2) :: (1, 1) :: repeat (1, 2) 3474178 ++ (4901382, 2) :: (1, 1) :: repeat (1, 2) 29403094 ++ w) by sec_eq.
    apply (sTUP [189; 112; 33; 19; 0] 1216 4 5490 2 ((1, 1) :: repeat (1, 2) 7704 ++ (1850, 2) :: (1, 1) :: repeat (1, 2) 58213 ++ (1716045, 2) :: (1, 1) :: repeat (1, 2) 3474178 ++ (4901382, 2) :: (1, 1) :: repeat (1, 2) 29403094 ++ w) 1); closearith.
  }
  (* step 203: DIPGRIND 1216 3056 *)
  apply (hsteps_trans _ (HC [189; 112; 33; 19; 0] 0 3 2 (repeat (1, 2) 1216 ++ (3056, 2) :: (1, 1) :: repeat (1, 2) 7704 ++ (1850, 2) :: (1, 1) :: repeat (1, 2) 58213 ++ (1716045, 2) :: (1, 1) :: repeat (1, 2) 3474178 ++ (4901382, 2) :: (1, 1) :: repeat (1, 2) 29403094 ++ w) 1)).
  {
    apply (DIPGRIND 1216 3056 [189; 112; 33; 19; 0] ((1, 1) :: repeat (1, 2) 7704 ++ (1850, 2) :: (1, 1) :: repeat (1, 2) 58213 ++ (1716045, 2) :: (1, 1) :: repeat (1, 2) 3474178 ++ (4901382, 2) :: (1, 1) :: repeat (1, 2) 29403094 ++ w) 1); closearith.
  }
  (* step 204: P PX2A *)
  apply (hsteps_trans _ (HC [33; 19; 0] 111 187 2 ((1, 1) :: repeat (1, 2) 1218 ++ (3056, 2) :: (1, 1) :: repeat (1, 2) 7704 ++ (1850, 2) :: (1, 1) :: repeat (1, 2) 58213 ++ (1716045, 2) :: (1, 1) :: repeat (1, 2) 3474178 ++ (4901382, 2) :: (1, 1) :: repeat (1, 2) 29403094 ++ w) 1)).
  {
    exact (hsteps_step _ _ _ (hPX2A 186 111 [33; 19; 0] (repeat (1, 2) 1216 ++ (3056, 2) :: (1, 1) :: repeat (1, 2) 7704 ++ (1850, 2) :: (1, 1) :: repeat (1, 2) 58213 ++ (1716045, 2) :: (1, 1) :: repeat (1, 2) 3474178 ++ (4901382, 2) :: (1, 1) :: repeat (1, 2) 29403094 ++ w) 1) (hsteps_refl _)).
  }
  (* step 205: hGRIND 92 *)
  apply (hsteps_trans _ (HB [33; 19; 0] 111 1 190 ((1, 1) :: repeat (1, 2) 1218 ++ (3056, 2) :: (1, 1) :: repeat (1, 2) 7704 ++ (1850, 2) :: (1, 1) :: repeat (1, 2) 58213 ++ (1716045, 2) :: (1, 1) :: repeat (1, 2) 3474178 ++ (4901382, 2) :: (1, 1) :: repeat (1, 2) 29403094 ++ w) 1)).
  {
    apply (hGRIND 92 [33; 19; 0] 111 ((1, 1) :: repeat (1, 2) 1218 ++ (3056, 2) :: (1, 1) :: repeat (1, 2) 7704 ++ (1850, 2) :: (1, 1) :: repeat (1, 2) 58213 ++ (1716045, 2) :: (1, 1) :: repeat (1, 2) 3474178 ++ (4901382, 2) :: (1, 1) :: repeat (1, 2) 29403094 ++ w) 1); closearith.
  }
  (* step 206: P POP *)
  apply (hsteps_trans _ (HB [33; 19; 0] 112 1 191 (repeat (1, 2) 1218 ++ (3056, 2) :: (1, 1) :: repeat (1, 2) 7704 ++ (1850, 2) :: (1, 1) :: repeat (1, 2) 58213 ++ (1716045, 2) :: (1, 1) :: repeat (1, 2) 3474178 ++ (4901382, 2) :: (1, 1) :: repeat (1, 2) 29403094 ++ w) 1)).
  {
    apply (sPOP1 [33; 19; 0] 111 190 (repeat (1, 2) 1218 ++ (3056, 2) :: (1, 1) :: repeat (1, 2) 7704 ++ (1850, 2) :: (1, 1) :: repeat (1, 2) 58213 ++ (1716045, 2) :: (1, 1) :: repeat (1, 2) 3474178 ++ (4901382, 2) :: (1, 1) :: repeat (1, 2) 29403094 ++ w) 1); closearith.
  }
  (* step 207: M pop12 (1218,) *)
  apply (hsteps_trans _ (HB [33; 19; 0] 1330 1 2627 ((3056, 2) :: (1, 1) :: repeat (1, 2) 7704 ++ (1850, 2) :: (1, 1) :: repeat (1, 2) 58213 ++ (1716045, 2) :: (1, 1) :: repeat (1, 2) 3474178 ++ (4901382, 2) :: (1, 1) :: repeat (1, 2) 29403094 ++ w) 1)).
  {
    apply (pop12 1218 [33; 19; 0] 112 191 ((3056, 2) :: (1, 1) :: repeat (1, 2) 7704 ++ (1850, 2) :: (1, 1) :: repeat (1, 2) 58213 ++ (1716045, 2) :: (1, 1) :: repeat (1, 2) 3474178 ++ (4901382, 2) :: (1, 1) :: repeat (1, 2) 29403094 ++ w) 1); closearith.
  }
  (* step 208: sTUP *)
  apply (hsteps_trans _ (HC [33; 19; 0] 1330 2626 2 ((3054, 2) :: (1, 1) :: repeat (1, 2) 7704 ++ (1850, 2) :: (1, 1) :: repeat (1, 2) 58213 ++ (1716045, 2) :: (1, 1) :: repeat (1, 2) 3474178 ++ (4901382, 2) :: (1, 1) :: repeat (1, 2) 29403094 ++ w) 1)).
  {
    replace ((3054, 2) :: (1, 1) :: repeat (1, 2) 7704 ++ (1850, 2) :: (1, 1) :: repeat (1, 2) 58213 ++ (1716045, 2) :: (1, 1) :: repeat (1, 2) 3474178 ++ (4901382, 2) :: (1, 1) :: repeat (1, 2) 29403094 ++ w) with ((3056 - 2, 2) :: (1, 1) :: repeat (1, 2) 7704 ++ (1850, 2) :: (1, 1) :: repeat (1, 2) 58213 ++ (1716045, 2) :: (1, 1) :: repeat (1, 2) 3474178 ++ (4901382, 2) :: (1, 1) :: repeat (1, 2) 29403094 ++ w) by sec_eq.
    apply (sTUP [33; 19; 0] 1330 2627 3056 2 ((1, 1) :: repeat (1, 2) 7704 ++ (1850, 2) :: (1, 1) :: repeat (1, 2) 58213 ++ (1716045, 2) :: (1, 1) :: repeat (1, 2) 3474178 ++ (4901382, 2) :: (1, 1) :: repeat (1, 2) 29403094 ++ w) 1); closearith.
  }
  (* step 209: hGRIND_even 1311 *)
  apply (hsteps_trans _ (HB [33; 19; 0] 1329 1 2626 ((2, 2) :: (3054, 2) :: (1, 1) :: repeat (1, 2) 7704 ++ (1850, 2) :: (1, 1) :: repeat (1, 2) 58213 ++ (1716045, 2) :: (1, 1) :: repeat (1, 2) 3474178 ++ (4901382, 2) :: (1, 1) :: repeat (1, 2) 29403094 ++ w) 1)).
  {
    apply (hGRIND_even 1311 [33; 19; 0] 1329 ((3054, 2) :: (1, 1) :: repeat (1, 2) 7704 ++ (1850, 2) :: (1, 1) :: repeat (1, 2) 58213 ++ (1716045, 2) :: (1, 1) :: repeat (1, 2) 3474178 ++ (4901382, 2) :: (1, 1) :: repeat (1, 2) 29403094 ++ w) 1); closearith.
  }
  (* step 210: P TUP2_1 *)
  apply (hsteps_trans _ (HC [1330; 33; 19; 0] 2626 1 2 ((3052, 2) :: (1, 1) :: repeat (1, 2) 7704 ++ (1850, 2) :: (1, 1) :: repeat (1, 2) 58213 ++ (1716045, 2) :: (1, 1) :: repeat (1, 2) 3474178 ++ (4901382, 2) :: (1, 1) :: repeat (1, 2) 29403094 ++ w) 1)).
  {
    replace ((3052, 2) :: (1, 1) :: repeat (1, 2) 7704 ++ (1850, 2) :: (1, 1) :: repeat (1, 2) 58213 ++ (1716045, 2) :: (1, 1) :: repeat (1, 2) 3474178 ++ (4901382, 2) :: (1, 1) :: repeat (1, 2) 29403094 ++ w) with ((3054 - 2, 2) :: (1, 1) :: repeat (1, 2) 7704 ++ (1850, 2) :: (1, 1) :: repeat (1, 2) 58213 ++ (1716045, 2) :: (1, 1) :: repeat (1, 2) 3474178 ++ (4901382, 2) :: (1, 1) :: repeat (1, 2) 29403094 ++ w) by sec_eq.
    apply (sTUP2_1 [33; 19; 0] 1329 2625 3054 ((1, 1) :: repeat (1, 2) 7704 ++ (1850, 2) :: (1, 1) :: repeat (1, 2) 58213 ++ (1716045, 2) :: (1, 1) :: repeat (1, 2) 3474178 ++ (4901382, 2) :: (1, 1) :: repeat (1, 2) 29403094 ++ w) 1); closearith.
  }
  (* step 211: P TDN *)
  apply (hsteps_trans _ (HB [1330; 33; 19; 0] 2626 1 4 ((3052, 2) :: (1, 1) :: repeat (1, 2) 7704 ++ (1850, 2) :: (1, 1) :: repeat (1, 2) 58213 ++ (1716045, 2) :: (1, 1) :: repeat (1, 2) 3474178 ++ (4901382, 2) :: (1, 1) :: repeat (1, 2) 29403094 ++ w) 1)).
  {
    apply (sTDN [1330; 33; 19; 0] 2626 ((3052, 2) :: (1, 1) :: repeat (1, 2) 7704 ++ (1850, 2) :: (1, 1) :: repeat (1, 2) 58213 ++ (1716045, 2) :: (1, 1) :: repeat (1, 2) 3474178 ++ (4901382, 2) :: (1, 1) :: repeat (1, 2) 29403094 ++ w) 1).
  }
  (* step 212: sTUP *)
  apply (hsteps_trans _ (HC [1330; 33; 19; 0] 2626 3 2 ((3050, 2) :: (1, 1) :: repeat (1, 2) 7704 ++ (1850, 2) :: (1, 1) :: repeat (1, 2) 58213 ++ (1716045, 2) :: (1, 1) :: repeat (1, 2) 3474178 ++ (4901382, 2) :: (1, 1) :: repeat (1, 2) 29403094 ++ w) 1)).
  {
    replace ((3050, 2) :: (1, 1) :: repeat (1, 2) 7704 ++ (1850, 2) :: (1, 1) :: repeat (1, 2) 58213 ++ (1716045, 2) :: (1, 1) :: repeat (1, 2) 3474178 ++ (4901382, 2) :: (1, 1) :: repeat (1, 2) 29403094 ++ w) with ((3052 - 2, 2) :: (1, 1) :: repeat (1, 2) 7704 ++ (1850, 2) :: (1, 1) :: repeat (1, 2) 58213 ++ (1716045, 2) :: (1, 1) :: repeat (1, 2) 3474178 ++ (4901382, 2) :: (1, 1) :: repeat (1, 2) 29403094 ++ w) by sec_eq.
    apply (sTUP [1330; 33; 19; 0] 2626 4 3052 2 ((1, 1) :: repeat (1, 2) 7704 ++ (1850, 2) :: (1, 1) :: repeat (1, 2) 58213 ++ (1716045, 2) :: (1, 1) :: repeat (1, 2) 3474178 ++ (4901382, 2) :: (1, 1) :: repeat (1, 2) 29403094 ++ w) 1); closearith.
  }
  (* step 213: CLEANG_even 1524 *)
  apply (hsteps_trans _ (HB [1330; 33; 19; 0] 2626 1 3054 ((2, 2) :: (1, 1) :: repeat (1, 2) 7704 ++ (1850, 2) :: (1, 1) :: repeat (1, 2) 58213 ++ (1716045, 2) :: (1, 1) :: repeat (1, 2) 3474178 ++ (4901382, 2) :: (1, 1) :: repeat (1, 2) 29403094 ++ w) 1)).
  {
    apply (CLEANG_even 1524 [1330; 33; 19; 0] 2626 ((1, 1) :: repeat (1, 2) 7704 ++ (1850, 2) :: (1, 1) :: repeat (1, 2) 58213 ++ (1716045, 2) :: (1, 1) :: repeat (1, 2) 3474178 ++ (4901382, 2) :: (1, 1) :: repeat (1, 2) 29403094 ++ w) 1); closearith.
  }
  (* step 214: P TRANS2_1 *)
  apply (hsteps_trans _ (HB [2627; 1330; 33; 19; 0] 3055 1 3 (repeat (1, 2) 7704 ++ (1850, 2) :: (1, 1) :: repeat (1, 2) 58213 ++ (1716045, 2) :: (1, 1) :: repeat (1, 2) 3474178 ++ (4901382, 2) :: (1, 1) :: repeat (1, 2) 29403094 ++ w) 1)).
  {
    apply (sTRANS2_1 [1330; 33; 19; 0] 2626 3053 1 (repeat (1, 2) 7704 ++ (1850, 2) :: (1, 1) :: repeat (1, 2) 58213 ++ (1716045, 2) :: (1, 1) :: repeat (1, 2) 3474178 ++ (4901382, 2) :: (1, 1) :: repeat (1, 2) 29403094 ++ w) 1); closearith.
  }
  (* step 215: M pop12 (7704,) *)
  apply (hsteps_trans _ (HB [2627; 1330; 33; 19; 0] 10759 1 15411 ((1850, 2) :: (1, 1) :: repeat (1, 2) 58213 ++ (1716045, 2) :: (1, 1) :: repeat (1, 2) 3474178 ++ (4901382, 2) :: (1, 1) :: repeat (1, 2) 29403094 ++ w) 1)).
  {
    apply (pop12 7704 [2627; 1330; 33; 19; 0] 3055 3 ((1850, 2) :: (1, 1) :: repeat (1, 2) 58213 ++ (1716045, 2) :: (1, 1) :: repeat (1, 2) 3474178 ++ (4901382, 2) :: (1, 1) :: repeat (1, 2) 29403094 ++ w) 1); closearith.
  }
  (* step 216: sTUP *)
  apply (hsteps_trans _ (HC [2627; 1330; 33; 19; 0] 10759 15410 2 ((1848, 2) :: (1, 1) :: repeat (1, 2) 58213 ++ (1716045, 2) :: (1, 1) :: repeat (1, 2) 3474178 ++ (4901382, 2) :: (1, 1) :: repeat (1, 2) 29403094 ++ w) 1)).
  {
    replace ((1848, 2) :: (1, 1) :: repeat (1, 2) 58213 ++ (1716045, 2) :: (1, 1) :: repeat (1, 2) 3474178 ++ (4901382, 2) :: (1, 1) :: repeat (1, 2) 29403094 ++ w) with ((1850 - 2, 2) :: (1, 1) :: repeat (1, 2) 58213 ++ (1716045, 2) :: (1, 1) :: repeat (1, 2) 3474178 ++ (4901382, 2) :: (1, 1) :: repeat (1, 2) 29403094 ++ w) by sec_eq.
    apply (sTUP [2627; 1330; 33; 19; 0] 10759 15411 1850 2 ((1, 1) :: repeat (1, 2) 58213 ++ (1716045, 2) :: (1, 1) :: repeat (1, 2) 3474178 ++ (4901382, 2) :: (1, 1) :: repeat (1, 2) 29403094 ++ w) 1); closearith.
  }
  (* step 217: hGRIND_even 7703 *)
  apply (hsteps_trans _ (HB [2627; 1330; 33; 19; 0] 10758 1 15410 ((2, 2) :: (1848, 2) :: (1, 1) :: repeat (1, 2) 58213 ++ (1716045, 2) :: (1, 1) :: repeat (1, 2) 3474178 ++ (4901382, 2) :: (1, 1) :: repeat (1, 2) 29403094 ++ w) 1)).
  {
    rewrite NUM59X21.
    apply (hGRIND_even 7703 [2627; 1330; 33; 19; 0] 10758 ((1848, 2) :: (1, 1) :: repeat (1, 2) 58213 ++ (1716045, 2) :: (1, 1) :: repeat (1, 2) 3474178 ++ (4901382, 2) :: (1, 1) :: repeat (1, 2) 29403094 ++ w) 1); closearith.
  }
  (* step 218: P TUP2_1 *)
  apply (hsteps_trans _ (HC [10759; 2627; 1330; 33; 19; 0] 15410 1 2 ((1846, 2) :: (1, 1) :: repeat (1, 2) 58213 ++ (1716045, 2) :: (1, 1) :: repeat (1, 2) 3474178 ++ (4901382, 2) :: (1, 1) :: repeat (1, 2) 29403094 ++ w) 1)).
  {
    replace ((1846, 2) :: (1, 1) :: repeat (1, 2) 58213 ++ (1716045, 2) :: (1, 1) :: repeat (1, 2) 3474178 ++ (4901382, 2) :: (1, 1) :: repeat (1, 2) 29403094 ++ w) with ((1848 - 2, 2) :: (1, 1) :: repeat (1, 2) 58213 ++ (1716045, 2) :: (1, 1) :: repeat (1, 2) 3474178 ++ (4901382, 2) :: (1, 1) :: repeat (1, 2) 29403094 ++ w) by sec_eq.
    apply (sTUP2_1 [2627; 1330; 33; 19; 0] 10758 15409 1848 ((1, 1) :: repeat (1, 2) 58213 ++ (1716045, 2) :: (1, 1) :: repeat (1, 2) 3474178 ++ (4901382, 2) :: (1, 1) :: repeat (1, 2) 29403094 ++ w) 1); closearith.
  }
  (* step 219: P TDN *)
  apply (hsteps_trans _ (HB [10759; 2627; 1330; 33; 19; 0] 15410 1 4 ((1846, 2) :: (1, 1) :: repeat (1, 2) 58213 ++ (1716045, 2) :: (1, 1) :: repeat (1, 2) 3474178 ++ (4901382, 2) :: (1, 1) :: repeat (1, 2) 29403094 ++ w) 1)).
  {
    apply (sTDN [10759; 2627; 1330; 33; 19; 0] 15410 ((1846, 2) :: (1, 1) :: repeat (1, 2) 58213 ++ (1716045, 2) :: (1, 1) :: repeat (1, 2) 3474178 ++ (4901382, 2) :: (1, 1) :: repeat (1, 2) 29403094 ++ w) 1).
  }
  (* step 220: sTUP *)
  apply (hsteps_trans _ (HC [10759; 2627; 1330; 33; 19; 0] 15410 3 2 ((1844, 2) :: (1, 1) :: repeat (1, 2) 58213 ++ (1716045, 2) :: (1, 1) :: repeat (1, 2) 3474178 ++ (4901382, 2) :: (1, 1) :: repeat (1, 2) 29403094 ++ w) 1)).
  {
    replace ((1844, 2) :: (1, 1) :: repeat (1, 2) 58213 ++ (1716045, 2) :: (1, 1) :: repeat (1, 2) 3474178 ++ (4901382, 2) :: (1, 1) :: repeat (1, 2) 29403094 ++ w) with ((1846 - 2, 2) :: (1, 1) :: repeat (1, 2) 58213 ++ (1716045, 2) :: (1, 1) :: repeat (1, 2) 3474178 ++ (4901382, 2) :: (1, 1) :: repeat (1, 2) 29403094 ++ w) by sec_eq.
    apply (sTUP [10759; 2627; 1330; 33; 19; 0] 15410 4 1846 2 ((1, 1) :: repeat (1, 2) 58213 ++ (1716045, 2) :: (1, 1) :: repeat (1, 2) 3474178 ++ (4901382, 2) :: (1, 1) :: repeat (1, 2) 29403094 ++ w) 1); closearith.
  }
  (* step 221: CLEANG_even 921 *)
  apply (hsteps_trans _ (HB [10759; 2627; 1330; 33; 19; 0] 15410 1 1848 ((2, 2) :: (1, 1) :: repeat (1, 2) 58213 ++ (1716045, 2) :: (1, 1) :: repeat (1, 2) 3474178 ++ (4901382, 2) :: (1, 1) :: repeat (1, 2) 29403094 ++ w) 1)).
  {
    apply (CLEANG_even 921 [10759; 2627; 1330; 33; 19; 0] 15410 ((1, 1) :: repeat (1, 2) 58213 ++ (1716045, 2) :: (1, 1) :: repeat (1, 2) 3474178 ++ (4901382, 2) :: (1, 1) :: repeat (1, 2) 29403094 ++ w) 1); closearith.
  }
  (* step 222: P TRANS2_1 *)
  apply (hsteps_trans _ (HB [15411; 10759; 2627; 1330; 33; 19; 0] 1849 1 3 (repeat (1, 2) 58213 ++ (1716045, 2) :: (1, 1) :: repeat (1, 2) 3474178 ++ (4901382, 2) :: (1, 1) :: repeat (1, 2) 29403094 ++ w) 1)).
  {
    apply (sTRANS2_1 [10759; 2627; 1330; 33; 19; 0] 15410 1847 1 (repeat (1, 2) 58213 ++ (1716045, 2) :: (1, 1) :: repeat (1, 2) 3474178 ++ (4901382, 2) :: (1, 1) :: repeat (1, 2) 29403094 ++ w) 1); closearith.
  }
  (* step 223: M pop12 (58213,) *)
  apply (hsteps_trans _ (HB [15411; 10759; 2627; 1330; 33; 19; 0] 60062 1 116429 ((1716045, 2) :: (1, 1) :: repeat (1, 2) 3474178 ++ (4901382, 2) :: (1, 1) :: repeat (1, 2) 29403094 ++ w) 1)).
  {
    apply (pop12 58213 [15411; 10759; 2627; 1330; 33; 19; 0] 1849 3 ((1716045, 2) :: (1, 1) :: repeat (1, 2) 3474178 ++ (4901382, 2) :: (1, 1) :: repeat (1, 2) 29403094 ++ w) 1); closearith.
  }
  (* step 224: sTUP *)
  apply (hsteps_trans _ (HC [15411; 10759; 2627; 1330; 33; 19; 0] 60062 116428 2 ((1716043, 2) :: (1, 1) :: repeat (1, 2) 3474178 ++ (4901382, 2) :: (1, 1) :: repeat (1, 2) 29403094 ++ w) 1)).
  {
    rewrite NUM59X22.
    rewrite NUM59X23.
    apply (sTUP [15411; 10759; 2627; 1330; 33; 19; 0] 60062 116429 1716045 2 ((1, 1) :: repeat (1, 2) 3474178 ++ (4901382, 2) :: (1, 1) :: repeat (1, 2) 29403094 ++ w) 1); closearith.
  }
  (* step 225: hGRIND_even 58212 *)
  apply (hsteps_trans _ (HB [15411; 10759; 2627; 1330; 33; 19; 0] 60061 1 116428 ((2, 2) :: (1716043, 2) :: (1, 1) :: repeat (1, 2) 3474178 ++ (4901382, 2) :: (1, 1) :: repeat (1, 2) 29403094 ++ w) 1)).
  {
    rewrite NUM59X24.
    rewrite NUM59X25.
    apply (hGRIND_even 58212 [15411; 10759; 2627; 1330; 33; 19; 0] 60061 ((1716043, 2) :: (1, 1) :: repeat (1, 2) 3474178 ++ (4901382, 2) :: (1, 1) :: repeat (1, 2) 29403094 ++ w) 1); closearith.
  }
  (* step 226: P TUP2_1 *)
  apply (hsteps_trans _ (HC [60062; 15411; 10759; 2627; 1330; 33; 19; 0] 116428 1 2 ((1716041, 2) :: (1, 1) :: repeat (1, 2) 3474178 ++ (4901382, 2) :: (1, 1) :: repeat (1, 2) 29403094 ++ w) 1)).
  {
    rewrite NUM59X26.
    rewrite NUM59X27.
    apply (sTUP2_1 [15411; 10759; 2627; 1330; 33; 19; 0] 60061 116427 1716043 ((1, 1) :: repeat (1, 2) 3474178 ++ (4901382, 2) :: (1, 1) :: repeat (1, 2) 29403094 ++ w) 1); closearith.
  }
  (* step 227: P TDN *)
  apply (hsteps_trans _ (HB [60062; 15411; 10759; 2627; 1330; 33; 19; 0] 116428 1 4 ((1716041, 2) :: (1, 1) :: repeat (1, 2) 3474178 ++ (4901382, 2) :: (1, 1) :: repeat (1, 2) 29403094 ++ w) 1)).
  {
    apply (sTDN [60062; 15411; 10759; 2627; 1330; 33; 19; 0] 116428 ((1716041, 2) :: (1, 1) :: repeat (1, 2) 3474178 ++ (4901382, 2) :: (1, 1) :: repeat (1, 2) 29403094 ++ w) 1).
  }
  (* step 228: sTUP *)
  apply (hsteps_trans _ (HC [60062; 15411; 10759; 2627; 1330; 33; 19; 0] 116428 3 2 ((1716039, 2) :: (1, 1) :: repeat (1, 2) 3474178 ++ (4901382, 2) :: (1, 1) :: repeat (1, 2) 29403094 ++ w) 1)).
  {
    rewrite NUM59X28.
    apply (sTUP [60062; 15411; 10759; 2627; 1330; 33; 19; 0] 116428 4 1716041 2 ((1, 1) :: repeat (1, 2) 3474178 ++ (4901382, 2) :: (1, 1) :: repeat (1, 2) 29403094 ++ w) 1); closearith.
  }
  (* step 229: DIPGRIND 116428 1483183 *)
  apply (hsteps_trans _ (HC [60062; 15411; 10759; 2627; 1330; 33; 19; 0] 0 3 2 (repeat (1, 2) 116428 ++ (1483183, 2) :: (1, 1) :: repeat (1, 2) 3474178 ++ (4901382, 2) :: (1, 1) :: repeat (1, 2) 29403094 ++ w) 1)).
  {
    rewrite NUM59X29.
    apply (DIPGRIND 116428 1483183 [60062; 15411; 10759; 2627; 1330; 33; 19; 0] ((1, 1) :: repeat (1, 2) 3474178 ++ (4901382, 2) :: (1, 1) :: repeat (1, 2) 29403094 ++ w) 1); closearith.
  }
  (* step 230: P PX2A *)
  apply (hsteps_trans _ (HC [10759; 2627; 1330; 33; 19; 0] 15410 60060 2 ((1, 1) :: repeat (1, 2) 116430 ++ (1483183, 2) :: (1, 1) :: repeat (1, 2) 3474178 ++ (4901382, 2) :: (1, 1) :: repeat (1, 2) 29403094 ++ w) 1)).
  {
    exact (hsteps_step _ _ _ (hPX2A 60059 15410 [10759; 2627; 1330; 33; 19; 0] (repeat (1, 2) 116428 ++ (1483183, 2) :: (1, 1) :: repeat (1, 2) 3474178 ++ (4901382, 2) :: (1, 1) :: repeat (1, 2) 29403094 ++ w) 1) (hsteps_refl _)).
  }
  (* step 231: P PUSH *)
  apply (hsteps_trans _ (HC [10759; 2627; 1330; 33; 19; 0] 15409 1 2 ((60058, 2) :: (1, 1) :: repeat (1, 2) 116430 ++ (1483183, 2) :: (1, 1) :: repeat (1, 2) 3474178 ++ (4901382, 2) :: (1, 1) :: repeat (1, 2) 29403094 ++ w) 1)).
  {
    replace ((60058, 2) :: (1, 1) :: repeat (1, 2) 116430 ++ (1483183, 2) :: (1, 1) :: repeat (1, 2) 3474178 ++ (4901382, 2) :: (1, 1) :: repeat (1, 2) 29403094 ++ w) with ((60060 - 2, 2) :: (1, 1) :: repeat (1, 2) 116430 ++ (1483183, 2) :: (1, 1) :: repeat (1, 2) 3474178 ++ (4901382, 2) :: (1, 1) :: repeat (1, 2) 29403094 ++ w) by sec_eq.
    apply (sPUSH [10759; 2627; 1330; 33; 19; 0] 15409 60060 ((1, 1) :: repeat (1, 2) 116430 ++ (1483183, 2) :: (1, 1) :: repeat (1, 2) 3474178 ++ (4901382, 2) :: (1, 1) :: repeat (1, 2) 29403094 ++ w) 1); closearith.
  }
  (* step 232: P TDN *)
  apply (hsteps_trans _ (HB [10759; 2627; 1330; 33; 19; 0] 15409 1 4 ((60058, 2) :: (1, 1) :: repeat (1, 2) 116430 ++ (1483183, 2) :: (1, 1) :: repeat (1, 2) 3474178 ++ (4901382, 2) :: (1, 1) :: repeat (1, 2) 29403094 ++ w) 1)).
  {
    apply (sTDN [10759; 2627; 1330; 33; 19; 0] 15409 ((60058, 2) :: (1, 1) :: repeat (1, 2) 116430 ++ (1483183, 2) :: (1, 1) :: repeat (1, 2) 3474178 ++ (4901382, 2) :: (1, 1) :: repeat (1, 2) 29403094 ++ w) 1).
  }
  (* step 233: sTUP *)
  replace ((60056, 2) :: (1, 1) :: repeat (1, 2) 116430 ++ (1483183, 2) :: (1, 1) :: repeat (1, 2) 3474178 ++ (4901382, 2) :: (1, 1) :: repeat (1, 2) 29403094 ++ w) with ((60058 - 2, 2) :: (1, 1) :: repeat (1, 2) 116430 ++ (1483183, 2) :: (1, 1) :: repeat (1, 2) 3474178 ++ (4901382, 2) :: (1, 1) :: repeat (1, 2) 29403094 ++ w) by sec_eq.
  apply (sTUP [10759; 2627; 1330; 33; 19; 0] 15409 4 60058 2 ((1, 1) :: repeat (1, 2) 116430 ++ (1483183, 2) :: (1, 1) :: repeat (1, 2) 3474178 ++ (4901382, 2) :: (1, 1) :: repeat (1, 2) 29403094 ++ w) 1); closearith.
Qed.

(* CASCADE59g: steps 234-289 of the CASCADE59 chain. *)
Lemma CASCADE59g : forall w,
  hsteps (HC [10759; 2627; 1330; 33; 19; 0] 15409 3 2 ((60056, 2) :: (1, 1) :: repeat (1, 2) 116430 ++ (1483183, 2) :: (1, 1) :: repeat (1, 2) 3474178 ++ (4901382, 2) :: (1, 1) :: repeat (1, 2) 29403094 ++ w) 1)
         (HB [0] 4 1 4 ((1, 1) :: repeat (1, 2) 15 ++ (4, 2) :: (1, 1) :: repeat (1, 2) 74 ++ (1112, 2) :: (1, 1) :: repeat (1, 2) 2627 ++ (5503, 2) :: (1, 1) :: repeat (1, 2) 15411 ++ (29238, 2) :: (1, 1) :: repeat (1, 2) 116430 ++ (1483183, 2) :: (1, 1) :: repeat (1, 2) 3474178 ++ (4901382, 2) :: (1, 1) :: repeat (1, 2) 29403094 ++ w) 1).
Proof.
  intro w.
  (* step 234: DIPGRIND 15409 29238 *)
  apply (hsteps_trans _ (HC [10759; 2627; 1330; 33; 19; 0] 0 3 2 (repeat (1, 2) 15409 ++ (29238, 2) :: (1, 1) :: repeat (1, 2) 116430 ++ (1483183, 2) :: (1, 1) :: repeat (1, 2) 3474178 ++ (4901382, 2) :: (1, 1) :: repeat (1, 2) 29403094 ++ w) 1)).
  {
    apply (DIPGRIND 15409 29238 [10759; 2627; 1330; 33; 19; 0] ((1, 1) :: repeat (1, 2) 116430 ++ (1483183, 2) :: (1, 1) :: repeat (1, 2) 3474178 ++ (4901382, 2) :: (1, 1) :: repeat (1, 2) 29403094 ++ w) 1); closearith.
  }
  (* step 235: P PX2A *)
  apply (hsteps_trans _ (HC [1330; 33; 19; 0] 2626 10757 2 ((1, 1) :: repeat (1, 2) 15411 ++ (29238, 2) :: (1, 1) :: repeat (1, 2) 116430 ++ (1483183, 2) :: (1, 1) :: repeat (1, 2) 3474178 ++ (4901382, 2) :: (1, 1) :: repeat (1, 2) 29403094 ++ w) 1)).
  {
    exact (hsteps_step _ _ _ (hPX2A 10756 2626 [1330; 33; 19; 0] (repeat (1, 2) 15409 ++ (29238, 2) :: (1, 1) :: repeat (1, 2) 116430 ++ (1483183, 2) :: (1, 1) :: repeat (1, 2) 3474178 ++ (4901382, 2) :: (1, 1) :: repeat (1, 2) 29403094 ++ w) 1) (hsteps_refl _)).
  }
  (* step 236: P PUSH *)
  apply (hsteps_trans _ (HC [1330; 33; 19; 0] 2625 1 2 ((10755, 2) :: (1, 1) :: repeat (1, 2) 15411 ++ (29238, 2) :: (1, 1) :: repeat (1, 2) 116430 ++ (1483183, 2) :: (1, 1) :: repeat (1, 2) 3474178 ++ (4901382, 2) :: (1, 1) :: repeat (1, 2) 29403094 ++ w) 1)).
  {
    replace ((10755, 2) :: (1, 1) :: repeat (1, 2) 15411 ++ (29238, 2) :: (1, 1) :: repeat (1, 2) 116430 ++ (1483183, 2) :: (1, 1) :: repeat (1, 2) 3474178 ++ (4901382, 2) :: (1, 1) :: repeat (1, 2) 29403094 ++ w) with ((10757 - 2, 2) :: (1, 1) :: repeat (1, 2) 15411 ++ (29238, 2) :: (1, 1) :: repeat (1, 2) 116430 ++ (1483183, 2) :: (1, 1) :: repeat (1, 2) 3474178 ++ (4901382, 2) :: (1, 1) :: repeat (1, 2) 29403094 ++ w) by sec_eq.
    apply (sPUSH [1330; 33; 19; 0] 2625 10757 ((1, 1) :: repeat (1, 2) 15411 ++ (29238, 2) :: (1, 1) :: repeat (1, 2) 116430 ++ (1483183, 2) :: (1, 1) :: repeat (1, 2) 3474178 ++ (4901382, 2) :: (1, 1) :: repeat (1, 2) 29403094 ++ w) 1); closearith.
  }
  (* step 237: P TDN *)
  apply (hsteps_trans _ (HB [1330; 33; 19; 0] 2625 1 4 ((10755, 2) :: (1, 1) :: repeat (1, 2) 15411 ++ (29238, 2) :: (1, 1) :: repeat (1, 2) 116430 ++ (1483183, 2) :: (1, 1) :: repeat (1, 2) 3474178 ++ (4901382, 2) :: (1, 1) :: repeat (1, 2) 29403094 ++ w) 1)).
  {
    apply (sTDN [1330; 33; 19; 0] 2625 ((10755, 2) :: (1, 1) :: repeat (1, 2) 15411 ++ (29238, 2) :: (1, 1) :: repeat (1, 2) 116430 ++ (1483183, 2) :: (1, 1) :: repeat (1, 2) 3474178 ++ (4901382, 2) :: (1, 1) :: repeat (1, 2) 29403094 ++ w) 1).
  }
  (* step 238: sTUP *)
  apply (hsteps_trans _ (HC [1330; 33; 19; 0] 2625 3 2 ((10753, 2) :: (1, 1) :: repeat (1, 2) 15411 ++ (29238, 2) :: (1, 1) :: repeat (1, 2) 116430 ++ (1483183, 2) :: (1, 1) :: repeat (1, 2) 3474178 ++ (4901382, 2) :: (1, 1) :: repeat (1, 2) 29403094 ++ w) 1)).
  {
    replace ((10753, 2) :: (1, 1) :: repeat (1, 2) 15411 ++ (29238, 2) :: (1, 1) :: repeat (1, 2) 116430 ++ (1483183, 2) :: (1, 1) :: repeat (1, 2) 3474178 ++ (4901382, 2) :: (1, 1) :: repeat (1, 2) 29403094 ++ w) with ((10755 - 2, 2) :: (1, 1) :: repeat (1, 2) 15411 ++ (29238, 2) :: (1, 1) :: repeat (1, 2) 116430 ++ (1483183, 2) :: (1, 1) :: repeat (1, 2) 3474178 ++ (4901382, 2) :: (1, 1) :: repeat (1, 2) 29403094 ++ w) by sec_eq.
    apply (sTUP [1330; 33; 19; 0] 2625 4 10755 2 ((1, 1) :: repeat (1, 2) 15411 ++ (29238, 2) :: (1, 1) :: repeat (1, 2) 116430 ++ (1483183, 2) :: (1, 1) :: repeat (1, 2) 3474178 ++ (4901382, 2) :: (1, 1) :: repeat (1, 2) 29403094 ++ w) 1); closearith.
  }
  (* step 239: DIPGRIND 2625 5503 *)
  apply (hsteps_trans _ (HC [1330; 33; 19; 0] 0 3 2 (repeat (1, 2) 2625 ++ (5503, 2) :: (1, 1) :: repeat (1, 2) 15411 ++ (29238, 2) :: (1, 1) :: repeat (1, 2) 116430 ++ (1483183, 2) :: (1, 1) :: repeat (1, 2) 3474178 ++ (4901382, 2) :: (1, 1) :: repeat (1, 2) 29403094 ++ w) 1)).
  {
    apply (DIPGRIND 2625 5503 [1330; 33; 19; 0] ((1, 1) :: repeat (1, 2) 15411 ++ (29238, 2) :: (1, 1) :: repeat (1, 2) 116430 ++ (1483183, 2) :: (1, 1) :: repeat (1, 2) 3474178 ++ (4901382, 2) :: (1, 1) :: repeat (1, 2) 29403094 ++ w) 1); closearith.
  }
  (* step 240: P PX2A *)
  apply (hsteps_trans _ (HC [19; 0] 32 1328 2 ((1, 1) :: repeat (1, 2) 2627 ++ (5503, 2) :: (1, 1) :: repeat (1, 2) 15411 ++ (29238, 2) :: (1, 1) :: repeat (1, 2) 116430 ++ (1483183, 2) :: (1, 1) :: repeat (1, 2) 3474178 ++ (4901382, 2) :: (1, 1) :: repeat (1, 2) 29403094 ++ w) 1)).
  {
    exact (hsteps_step _ _ _ (hPX2A 1327 32 [19; 0] (repeat (1, 2) 2625 ++ (5503, 2) :: (1, 1) :: repeat (1, 2) 15411 ++ (29238, 2) :: (1, 1) :: repeat (1, 2) 116430 ++ (1483183, 2) :: (1, 1) :: repeat (1, 2) 3474178 ++ (4901382, 2) :: (1, 1) :: repeat (1, 2) 29403094 ++ w) 1) (hsteps_refl _)).
  }
  (* step 241: P PUSH *)
  apply (hsteps_trans _ (HC [19; 0] 31 1 2 ((1326, 2) :: (1, 1) :: repeat (1, 2) 2627 ++ (5503, 2) :: (1, 1) :: repeat (1, 2) 15411 ++ (29238, 2) :: (1, 1) :: repeat (1, 2) 116430 ++ (1483183, 2) :: (1, 1) :: repeat (1, 2) 3474178 ++ (4901382, 2) :: (1, 1) :: repeat (1, 2) 29403094 ++ w) 1)).
  {
    replace ((1326, 2) :: (1, 1) :: repeat (1, 2) 2627 ++ (5503, 2) :: (1, 1) :: repeat (1, 2) 15411 ++ (29238, 2) :: (1, 1) :: repeat (1, 2) 116430 ++ (1483183, 2) :: (1, 1) :: repeat (1, 2) 3474178 ++ (4901382, 2) :: (1, 1) :: repeat (1, 2) 29403094 ++ w) with ((1328 - 2, 2) :: (1, 1) :: repeat (1, 2) 2627 ++ (5503, 2) :: (1, 1) :: repeat (1, 2) 15411 ++ (29238, 2) :: (1, 1) :: repeat (1, 2) 116430 ++ (1483183, 2) :: (1, 1) :: repeat (1, 2) 3474178 ++ (4901382, 2) :: (1, 1) :: repeat (1, 2) 29403094 ++ w) by sec_eq.
    apply (sPUSH [19; 0] 31 1328 ((1, 1) :: repeat (1, 2) 2627 ++ (5503, 2) :: (1, 1) :: repeat (1, 2) 15411 ++ (29238, 2) :: (1, 1) :: repeat (1, 2) 116430 ++ (1483183, 2) :: (1, 1) :: repeat (1, 2) 3474178 ++ (4901382, 2) :: (1, 1) :: repeat (1, 2) 29403094 ++ w) 1); closearith.
  }
  (* step 242: P TDN *)
  apply (hsteps_trans _ (HB [19; 0] 31 1 4 ((1326, 2) :: (1, 1) :: repeat (1, 2) 2627 ++ (5503, 2) :: (1, 1) :: repeat (1, 2) 15411 ++ (29238, 2) :: (1, 1) :: repeat (1, 2) 116430 ++ (1483183, 2) :: (1, 1) :: repeat (1, 2) 3474178 ++ (4901382, 2) :: (1, 1) :: repeat (1, 2) 29403094 ++ w) 1)).
  {
    apply (sTDN [19; 0] 31 ((1326, 2) :: (1, 1) :: repeat (1, 2) 2627 ++ (5503, 2) :: (1, 1) :: repeat (1, 2) 15411 ++ (29238, 2) :: (1, 1) :: repeat (1, 2) 116430 ++ (1483183, 2) :: (1, 1) :: repeat (1, 2) 3474178 ++ (4901382, 2) :: (1, 1) :: repeat (1, 2) 29403094 ++ w) 1).
  }
  (* step 243: sTUP *)
  apply (hsteps_trans _ (HC [19; 0] 31 3 2 ((1324, 2) :: (1, 1) :: repeat (1, 2) 2627 ++ (5503, 2) :: (1, 1) :: repeat (1, 2) 15411 ++ (29238, 2) :: (1, 1) :: repeat (1, 2) 116430 ++ (1483183, 2) :: (1, 1) :: repeat (1, 2) 3474178 ++ (4901382, 2) :: (1, 1) :: repeat (1, 2) 29403094 ++ w) 1)).
  {
    replace ((1324, 2) :: (1, 1) :: repeat (1, 2) 2627 ++ (5503, 2) :: (1, 1) :: repeat (1, 2) 15411 ++ (29238, 2) :: (1, 1) :: repeat (1, 2) 116430 ++ (1483183, 2) :: (1, 1) :: repeat (1, 2) 3474178 ++ (4901382, 2) :: (1, 1) :: repeat (1, 2) 29403094 ++ w) with ((1326 - 2, 2) :: (1, 1) :: repeat (1, 2) 2627 ++ (5503, 2) :: (1, 1) :: repeat (1, 2) 15411 ++ (29238, 2) :: (1, 1) :: repeat (1, 2) 116430 ++ (1483183, 2) :: (1, 1) :: repeat (1, 2) 3474178 ++ (4901382, 2) :: (1, 1) :: repeat (1, 2) 29403094 ++ w) by sec_eq.
    apply (sTUP [19; 0] 31 4 1326 2 ((1, 1) :: repeat (1, 2) 2627 ++ (5503, 2) :: (1, 1) :: repeat (1, 2) 15411 ++ (29238, 2) :: (1, 1) :: repeat (1, 2) 116430 ++ (1483183, 2) :: (1, 1) :: repeat (1, 2) 3474178 ++ (4901382, 2) :: (1, 1) :: repeat (1, 2) 29403094 ++ w) 1); closearith.
  }
  (* step 244: DIPGRIND 31 1262 *)
  apply (hsteps_trans _ (HC [19; 0] 0 3 2 (repeat (1, 2) 31 ++ (1262, 2) :: (1, 1) :: repeat (1, 2) 2627 ++ (5503, 2) :: (1, 1) :: repeat (1, 2) 15411 ++ (29238, 2) :: (1, 1) :: repeat (1, 2) 116430 ++ (1483183, 2) :: (1, 1) :: repeat (1, 2) 3474178 ++ (4901382, 2) :: (1, 1) :: repeat (1, 2) 29403094 ++ w) 1)).
  {
    apply (DIPGRIND 31 1262 [19; 0] ((1, 1) :: repeat (1, 2) 2627 ++ (5503, 2) :: (1, 1) :: repeat (1, 2) 15411 ++ (29238, 2) :: (1, 1) :: repeat (1, 2) 116430 ++ (1483183, 2) :: (1, 1) :: repeat (1, 2) 3474178 ++ (4901382, 2) :: (1, 1) :: repeat (1, 2) 29403094 ++ w) 1); closearith.
  }
  (* step 245: P PX2A0 *)
  apply (hsteps_trans _ (HB [0] 3 1 2 ((15, 2) :: (1, 1) :: repeat (1, 2) 33 ++ (1262, 2) :: (1, 1) :: repeat (1, 2) 2627 ++ (5503, 2) :: (1, 1) :: repeat (1, 2) 15411 ++ (29238, 2) :: (1, 1) :: repeat (1, 2) 116430 ++ (1483183, 2) :: (1, 1) :: repeat (1, 2) 3474178 ++ (4901382, 2) :: (1, 1) :: repeat (1, 2) 29403094 ++ w) 1)).
  {
    exact (hsteps_step _ _ _ (hPX2A0 14 (repeat (1, 2) 31 ++ (1262, 2) :: (1, 1) :: repeat (1, 2) 2627 ++ (5503, 2) :: (1, 1) :: repeat (1, 2) 15411 ++ (29238, 2) :: (1, 1) :: repeat (1, 2) 116430 ++ (1483183, 2) :: (1, 1) :: repeat (1, 2) 3474178 ++ (4901382, 2) :: (1, 1) :: repeat (1, 2) 29403094 ++ w) 1) (hsteps_refl _)).
  }
  (* step 246: sTUP *)
  apply (hsteps_trans _ (HC [0] 3 1 2 ((13, 2) :: (1, 1) :: repeat (1, 2) 33 ++ (1262, 2) :: (1, 1) :: repeat (1, 2) 2627 ++ (5503, 2) :: (1, 1) :: repeat (1, 2) 15411 ++ (29238, 2) :: (1, 1) :: repeat (1, 2) 116430 ++ (1483183, 2) :: (1, 1) :: repeat (1, 2) 3474178 ++ (4901382, 2) :: (1, 1) :: repeat (1, 2) 29403094 ++ w) 1)).
  {
    replace ((13, 2) :: (1, 1) :: repeat (1, 2) 33 ++ (1262, 2) :: (1, 1) :: repeat (1, 2) 2627 ++ (5503, 2) :: (1, 1) :: repeat (1, 2) 15411 ++ (29238, 2) :: (1, 1) :: repeat (1, 2) 116430 ++ (1483183, 2) :: (1, 1) :: repeat (1, 2) 3474178 ++ (4901382, 2) :: (1, 1) :: repeat (1, 2) 29403094 ++ w) with ((15 - 2, 2) :: (1, 1) :: repeat (1, 2) 33 ++ (1262, 2) :: (1, 1) :: repeat (1, 2) 2627 ++ (5503, 2) :: (1, 1) :: repeat (1, 2) 15411 ++ (29238, 2) :: (1, 1) :: repeat (1, 2) 116430 ++ (1483183, 2) :: (1, 1) :: repeat (1, 2) 3474178 ++ (4901382, 2) :: (1, 1) :: repeat (1, 2) 29403094 ++ w) by sec_eq.
    apply (sTUP [0] 3 2 15 2 ((1, 1) :: repeat (1, 2) 33 ++ (1262, 2) :: (1, 1) :: repeat (1, 2) 2627 ++ (5503, 2) :: (1, 1) :: repeat (1, 2) 15411 ++ (29238, 2) :: (1, 1) :: repeat (1, 2) 116430 ++ (1483183, 2) :: (1, 1) :: repeat (1, 2) 3474178 ++ (4901382, 2) :: (1, 1) :: repeat (1, 2) 29403094 ++ w) 1); closearith.
  }
  (* step 247: P TDN *)
  apply (hsteps_trans _ (HB [0] 3 1 4 ((13, 2) :: (1, 1) :: repeat (1, 2) 33 ++ (1262, 2) :: (1, 1) :: repeat (1, 2) 2627 ++ (5503, 2) :: (1, 1) :: repeat (1, 2) 15411 ++ (29238, 2) :: (1, 1) :: repeat (1, 2) 116430 ++ (1483183, 2) :: (1, 1) :: repeat (1, 2) 3474178 ++ (4901382, 2) :: (1, 1) :: repeat (1, 2) 29403094 ++ w) 1)).
  {
    apply (sTDN [0] 3 ((13, 2) :: (1, 1) :: repeat (1, 2) 33 ++ (1262, 2) :: (1, 1) :: repeat (1, 2) 2627 ++ (5503, 2) :: (1, 1) :: repeat (1, 2) 15411 ++ (29238, 2) :: (1, 1) :: repeat (1, 2) 116430 ++ (1483183, 2) :: (1, 1) :: repeat (1, 2) 3474178 ++ (4901382, 2) :: (1, 1) :: repeat (1, 2) 29403094 ++ w) 1).
  }
  (* step 248: sTUP *)
  apply (hsteps_trans _ (HC [0] 3 3 2 ((11, 2) :: (1, 1) :: repeat (1, 2) 33 ++ (1262, 2) :: (1, 1) :: repeat (1, 2) 2627 ++ (5503, 2) :: (1, 1) :: repeat (1, 2) 15411 ++ (29238, 2) :: (1, 1) :: repeat (1, 2) 116430 ++ (1483183, 2) :: (1, 1) :: repeat (1, 2) 3474178 ++ (4901382, 2) :: (1, 1) :: repeat (1, 2) 29403094 ++ w) 1)).
  {
    replace ((11, 2) :: (1, 1) :: repeat (1, 2) 33 ++ (1262, 2) :: (1, 1) :: repeat (1, 2) 2627 ++ (5503, 2) :: (1, 1) :: repeat (1, 2) 15411 ++ (29238, 2) :: (1, 1) :: repeat (1, 2) 116430 ++ (1483183, 2) :: (1, 1) :: repeat (1, 2) 3474178 ++ (4901382, 2) :: (1, 1) :: repeat (1, 2) 29403094 ++ w) with ((13 - 2, 2) :: (1, 1) :: repeat (1, 2) 33 ++ (1262, 2) :: (1, 1) :: repeat (1, 2) 2627 ++ (5503, 2) :: (1, 1) :: repeat (1, 2) 15411 ++ (29238, 2) :: (1, 1) :: repeat (1, 2) 116430 ++ (1483183, 2) :: (1, 1) :: repeat (1, 2) 3474178 ++ (4901382, 2) :: (1, 1) :: repeat (1, 2) 29403094 ++ w) by sec_eq.
    apply (sTUP [0] 3 4 13 2 ((1, 1) :: repeat (1, 2) 33 ++ (1262, 2) :: (1, 1) :: repeat (1, 2) 2627 ++ (5503, 2) :: (1, 1) :: repeat (1, 2) 15411 ++ (29238, 2) :: (1, 1) :: repeat (1, 2) 116430 ++ (1483183, 2) :: (1, 1) :: repeat (1, 2) 3474178 ++ (4901382, 2) :: (1, 1) :: repeat (1, 2) 29403094 ++ w) 1); closearith.
  }
  (* step 249: DIPGRIND 3 5 *)
  apply (hsteps_trans _ (HC [0] 0 3 2 (repeat (1, 2) 3 ++ (5, 2) :: (1, 1) :: repeat (1, 2) 33 ++ (1262, 2) :: (1, 1) :: repeat (1, 2) 2627 ++ (5503, 2) :: (1, 1) :: repeat (1, 2) 15411 ++ (29238, 2) :: (1, 1) :: repeat (1, 2) 116430 ++ (1483183, 2) :: (1, 1) :: repeat (1, 2) 3474178 ++ (4901382, 2) :: (1, 1) :: repeat (1, 2) 29403094 ++ w) 1)).
  {
    apply (DIPGRIND 3 5 [0] ((1, 1) :: repeat (1, 2) 33 ++ (1262, 2) :: (1, 1) :: repeat (1, 2) 2627 ++ (5503, 2) :: (1, 1) :: repeat (1, 2) 15411 ++ (29238, 2) :: (1, 1) :: repeat (1, 2) 116430 ++ (1483183, 2) :: (1, 1) :: repeat (1, 2) 3474178 ++ (4901382, 2) :: (1, 1) :: repeat (1, 2) 29403094 ++ w) 1); closearith.
  }
  (* step 250: P PX2B0 *)
  apply (hsteps_trans _ (HB [] 0 1 5 (repeat (1, 2) 4 ++ (5, 2) :: (1, 1) :: repeat (1, 2) 33 ++ (1262, 2) :: (1, 1) :: repeat (1, 2) 2627 ++ (5503, 2) :: (1, 1) :: repeat (1, 2) 15411 ++ (29238, 2) :: (1, 1) :: repeat (1, 2) 116430 ++ (1483183, 2) :: (1, 1) :: repeat (1, 2) 3474178 ++ (4901382, 2) :: (1, 1) :: repeat (1, 2) 29403094 ++ w) 1)).
  {
    exact (hsteps_step _ _ _ (hPX2B0 (repeat (1, 2) 3 ++ (5, 2) :: (1, 1) :: repeat (1, 2) 33 ++ (1262, 2) :: (1, 1) :: repeat (1, 2) 2627 ++ (5503, 2) :: (1, 1) :: repeat (1, 2) 15411 ++ (29238, 2) :: (1, 1) :: repeat (1, 2) 116430 ++ (1483183, 2) :: (1, 1) :: repeat (1, 2) 3474178 ++ (4901382, 2) :: (1, 1) :: repeat (1, 2) 29403094 ++ w) 1) (hsteps_refl _)).
  }
  (* step 251: M pop12 (4,) *)
  apply (hsteps_trans _ (HB [] 4 1 13 ((5, 2) :: (1, 1) :: repeat (1, 2) 33 ++ (1262, 2) :: (1, 1) :: repeat (1, 2) 2627 ++ (5503, 2) :: (1, 1) :: repeat (1, 2) 15411 ++ (29238, 2) :: (1, 1) :: repeat (1, 2) 116430 ++ (1483183, 2) :: (1, 1) :: repeat (1, 2) 3474178 ++ (4901382, 2) :: (1, 1) :: repeat (1, 2) 29403094 ++ w) 1)).
  {
    apply (pop12 4 [] 0 5 ((5, 2) :: (1, 1) :: repeat (1, 2) 33 ++ (1262, 2) :: (1, 1) :: repeat (1, 2) 2627 ++ (5503, 2) :: (1, 1) :: repeat (1, 2) 15411 ++ (29238, 2) :: (1, 1) :: repeat (1, 2) 116430 ++ (1483183, 2) :: (1, 1) :: repeat (1, 2) 3474178 ++ (4901382, 2) :: (1, 1) :: repeat (1, 2) 29403094 ++ w) 1); closearith.
  }
  (* step 252: sTUP *)
  apply (hsteps_trans _ (HC [] 4 12 2 ((3, 2) :: (1, 1) :: repeat (1, 2) 33 ++ (1262, 2) :: (1, 1) :: repeat (1, 2) 2627 ++ (5503, 2) :: (1, 1) :: repeat (1, 2) 15411 ++ (29238, 2) :: (1, 1) :: repeat (1, 2) 116430 ++ (1483183, 2) :: (1, 1) :: repeat (1, 2) 3474178 ++ (4901382, 2) :: (1, 1) :: repeat (1, 2) 29403094 ++ w) 1)).
  {
    replace ((3, 2) :: (1, 1) :: repeat (1, 2) 33 ++ (1262, 2) :: (1, 1) :: repeat (1, 2) 2627 ++ (5503, 2) :: (1, 1) :: repeat (1, 2) 15411 ++ (29238, 2) :: (1, 1) :: repeat (1, 2) 116430 ++ (1483183, 2) :: (1, 1) :: repeat (1, 2) 3474178 ++ (4901382, 2) :: (1, 1) :: repeat (1, 2) 29403094 ++ w) with ((5 - 2, 2) :: (1, 1) :: repeat (1, 2) 33 ++ (1262, 2) :: (1, 1) :: repeat (1, 2) 2627 ++ (5503, 2) :: (1, 1) :: repeat (1, 2) 15411 ++ (29238, 2) :: (1, 1) :: repeat (1, 2) 116430 ++ (1483183, 2) :: (1, 1) :: repeat (1, 2) 3474178 ++ (4901382, 2) :: (1, 1) :: repeat (1, 2) 29403094 ++ w) by sec_eq.
    apply (sTUP [] 4 13 5 2 ((1, 1) :: repeat (1, 2) 33 ++ (1262, 2) :: (1, 1) :: repeat (1, 2) 2627 ++ (5503, 2) :: (1, 1) :: repeat (1, 2) 15411 ++ (29238, 2) :: (1, 1) :: repeat (1, 2) 116430 ++ (1483183, 2) :: (1, 1) :: repeat (1, 2) 3474178 ++ (4901382, 2) :: (1, 1) :: repeat (1, 2) 29403094 ++ w) 1); closearith.
  }
  (* step 253: P PUSH *)
  apply (hsteps_trans _ (HC [] 3 1 2 ((10, 2) :: (3, 2) :: (1, 1) :: repeat (1, 2) 33 ++ (1262, 2) :: (1, 1) :: repeat (1, 2) 2627 ++ (5503, 2) :: (1, 1) :: repeat (1, 2) 15411 ++ (29238, 2) :: (1, 1) :: repeat (1, 2) 116430 ++ (1483183, 2) :: (1, 1) :: repeat (1, 2) 3474178 ++ (4901382, 2) :: (1, 1) :: repeat (1, 2) 29403094 ++ w) 1)).
  {
    replace ((10, 2) :: (3, 2) :: (1, 1) :: repeat (1, 2) 33 ++ (1262, 2) :: (1, 1) :: repeat (1, 2) 2627 ++ (5503, 2) :: (1, 1) :: repeat (1, 2) 15411 ++ (29238, 2) :: (1, 1) :: repeat (1, 2) 116430 ++ (1483183, 2) :: (1, 1) :: repeat (1, 2) 3474178 ++ (4901382, 2) :: (1, 1) :: repeat (1, 2) 29403094 ++ w) with ((12 - 2, 2) :: (3, 2) :: (1, 1) :: repeat (1, 2) 33 ++ (1262, 2) :: (1, 1) :: repeat (1, 2) 2627 ++ (5503, 2) :: (1, 1) :: repeat (1, 2) 15411 ++ (29238, 2) :: (1, 1) :: repeat (1, 2) 116430 ++ (1483183, 2) :: (1, 1) :: repeat (1, 2) 3474178 ++ (4901382, 2) :: (1, 1) :: repeat (1, 2) 29403094 ++ w) by sec_eq.
    apply (sPUSH [] 3 12 ((3, 2) :: (1, 1) :: repeat (1, 2) 33 ++ (1262, 2) :: (1, 1) :: repeat (1, 2) 2627 ++ (5503, 2) :: (1, 1) :: repeat (1, 2) 15411 ++ (29238, 2) :: (1, 1) :: repeat (1, 2) 116430 ++ (1483183, 2) :: (1, 1) :: repeat (1, 2) 3474178 ++ (4901382, 2) :: (1, 1) :: repeat (1, 2) 29403094 ++ w) 1); closearith.
  }
  (* step 254: P TDN *)
  apply (hsteps_trans _ (HB [] 3 1 4 ((10, 2) :: (3, 2) :: (1, 1) :: repeat (1, 2) 33 ++ (1262, 2) :: (1, 1) :: repeat (1, 2) 2627 ++ (5503, 2) :: (1, 1) :: repeat (1, 2) 15411 ++ (29238, 2) :: (1, 1) :: repeat (1, 2) 116430 ++ (1483183, 2) :: (1, 1) :: repeat (1, 2) 3474178 ++ (4901382, 2) :: (1, 1) :: repeat (1, 2) 29403094 ++ w) 1)).
  {
    apply (sTDN [] 3 ((10, 2) :: (3, 2) :: (1, 1) :: repeat (1, 2) 33 ++ (1262, 2) :: (1, 1) :: repeat (1, 2) 2627 ++ (5503, 2) :: (1, 1) :: repeat (1, 2) 15411 ++ (29238, 2) :: (1, 1) :: repeat (1, 2) 116430 ++ (1483183, 2) :: (1, 1) :: repeat (1, 2) 3474178 ++ (4901382, 2) :: (1, 1) :: repeat (1, 2) 29403094 ++ w) 1).
  }
  (* step 255: sTUP *)
  apply (hsteps_trans _ (HC [] 3 3 2 ((8, 2) :: (3, 2) :: (1, 1) :: repeat (1, 2) 33 ++ (1262, 2) :: (1, 1) :: repeat (1, 2) 2627 ++ (5503, 2) :: (1, 1) :: repeat (1, 2) 15411 ++ (29238, 2) :: (1, 1) :: repeat (1, 2) 116430 ++ (1483183, 2) :: (1, 1) :: repeat (1, 2) 3474178 ++ (4901382, 2) :: (1, 1) :: repeat (1, 2) 29403094 ++ w) 1)).
  {
    replace ((8, 2) :: (3, 2) :: (1, 1) :: repeat (1, 2) 33 ++ (1262, 2) :: (1, 1) :: repeat (1, 2) 2627 ++ (5503, 2) :: (1, 1) :: repeat (1, 2) 15411 ++ (29238, 2) :: (1, 1) :: repeat (1, 2) 116430 ++ (1483183, 2) :: (1, 1) :: repeat (1, 2) 3474178 ++ (4901382, 2) :: (1, 1) :: repeat (1, 2) 29403094 ++ w) with ((10 - 2, 2) :: (3, 2) :: (1, 1) :: repeat (1, 2) 33 ++ (1262, 2) :: (1, 1) :: repeat (1, 2) 2627 ++ (5503, 2) :: (1, 1) :: repeat (1, 2) 15411 ++ (29238, 2) :: (1, 1) :: repeat (1, 2) 116430 ++ (1483183, 2) :: (1, 1) :: repeat (1, 2) 3474178 ++ (4901382, 2) :: (1, 1) :: repeat (1, 2) 29403094 ++ w) by sec_eq.
    apply (sTUP [] 3 4 10 2 ((3, 2) :: (1, 1) :: repeat (1, 2) 33 ++ (1262, 2) :: (1, 1) :: repeat (1, 2) 2627 ++ (5503, 2) :: (1, 1) :: repeat (1, 2) 15411 ++ (29238, 2) :: (1, 1) :: repeat (1, 2) 116430 ++ (1483183, 2) :: (1, 1) :: repeat (1, 2) 3474178 ++ (4901382, 2) :: (1, 1) :: repeat (1, 2) 29403094 ++ w) 1); closearith.
  }
  (* step 256: DIPGRIND 3 2 *)
  apply (hsteps_trans _ (HC [] 0 3 2 (repeat (1, 2) 3 ++ (2, 2) :: (3, 2) :: (1, 1) :: repeat (1, 2) 33 ++ (1262, 2) :: (1, 1) :: repeat (1, 2) 2627 ++ (5503, 2) :: (1, 1) :: repeat (1, 2) 15411 ++ (29238, 2) :: (1, 1) :: repeat (1, 2) 116430 ++ (1483183, 2) :: (1, 1) :: repeat (1, 2) 3474178 ++ (4901382, 2) :: (1, 1) :: repeat (1, 2) 29403094 ++ w) 1)).
  {
    apply (DIPGRIND 3 2 [] ((3, 2) :: (1, 1) :: repeat (1, 2) 33 ++ (1262, 2) :: (1, 1) :: repeat (1, 2) 2627 ++ (5503, 2) :: (1, 1) :: repeat (1, 2) 15411 ++ (29238, 2) :: (1, 1) :: repeat (1, 2) 116430 ++ (1483183, 2) :: (1, 1) :: repeat (1, 2) 3474178 ++ (4901382, 2) :: (1, 1) :: repeat (1, 2) 29403094 ++ w) 1); closearith.
  }
  (* step 257: P PUSHX *)
  apply (hsteps_trans _ (HB [] 1 1 7 (repeat (1, 2) 3 ++ (2, 2) :: (3, 2) :: (1, 1) :: repeat (1, 2) 33 ++ (1262, 2) :: (1, 1) :: repeat (1, 2) 2627 ++ (5503, 2) :: (1, 1) :: repeat (1, 2) 15411 ++ (29238, 2) :: (1, 1) :: repeat (1, 2) 116430 ++ (1483183, 2) :: (1, 1) :: repeat (1, 2) 3474178 ++ (4901382, 2) :: (1, 1) :: repeat (1, 2) 29403094 ++ w) 1)).
  {
    exact (hsteps_step _ _ _ (hPUSHX (repeat (1, 2) 3 ++ (2, 2) :: (3, 2) :: (1, 1) :: repeat (1, 2) 33 ++ (1262, 2) :: (1, 1) :: repeat (1, 2) 2627 ++ (5503, 2) :: (1, 1) :: repeat (1, 2) 15411 ++ (29238, 2) :: (1, 1) :: repeat (1, 2) 116430 ++ (1483183, 2) :: (1, 1) :: repeat (1, 2) 3474178 ++ (4901382, 2) :: (1, 1) :: repeat (1, 2) 29403094 ++ w) 1) (hsteps_refl _)).
  }
  (* step 258: M pop12 (3,) *)
  apply (hsteps_trans _ (HB [] 4 1 13 ((2, 2) :: (3, 2) :: (1, 1) :: repeat (1, 2) 33 ++ (1262, 2) :: (1, 1) :: repeat (1, 2) 2627 ++ (5503, 2) :: (1, 1) :: repeat (1, 2) 15411 ++ (29238, 2) :: (1, 1) :: repeat (1, 2) 116430 ++ (1483183, 2) :: (1, 1) :: repeat (1, 2) 3474178 ++ (4901382, 2) :: (1, 1) :: repeat (1, 2) 29403094 ++ w) 1)).
  {
    apply (pop12 3 [] 1 7 ((2, 2) :: (3, 2) :: (1, 1) :: repeat (1, 2) 33 ++ (1262, 2) :: (1, 1) :: repeat (1, 2) 2627 ++ (5503, 2) :: (1, 1) :: repeat (1, 2) 15411 ++ (29238, 2) :: (1, 1) :: repeat (1, 2) 116430 ++ (1483183, 2) :: (1, 1) :: repeat (1, 2) 3474178 ++ (4901382, 2) :: (1, 1) :: repeat (1, 2) 29403094 ++ w) 1); closearith.
  }
  (* step 259: P TUP2_1 *)
  apply (hsteps_trans _ (HC [5] 13 1 2 (repeat (1, 2) 1 ++ (1, 1) :: repeat (1, 2) 33 ++ (1262, 2) :: (1, 1) :: repeat (1, 2) 2627 ++ (5503, 2) :: (1, 1) :: repeat (1, 2) 15411 ++ (29238, 2) :: (1, 1) :: repeat (1, 2) 116430 ++ (1483183, 2) :: (1, 1) :: repeat (1, 2) 3474178 ++ (4901382, 2) :: (1, 1) :: repeat (1, 2) 29403094 ++ w) 1)).
  {
    replace (repeat (1, 2) 1 ++ (1, 1) :: repeat (1, 2) 33 ++ (1262, 2) :: (1, 1) :: repeat (1, 2) 2627 ++ (5503, 2) :: (1, 1) :: repeat (1, 2) 15411 ++ (29238, 2) :: (1, 1) :: repeat (1, 2) 116430 ++ (1483183, 2) :: (1, 1) :: repeat (1, 2) 3474178 ++ (4901382, 2) :: (1, 1) :: repeat (1, 2) 29403094 ++ w) with ((3 - 2, 2) :: (1, 1) :: repeat (1, 2) 33 ++ (1262, 2) :: (1, 1) :: repeat (1, 2) 2627 ++ (5503, 2) :: (1, 1) :: repeat (1, 2) 15411 ++ (29238, 2) :: (1, 1) :: repeat (1, 2) 116430 ++ (1483183, 2) :: (1, 1) :: repeat (1, 2) 3474178 ++ (4901382, 2) :: (1, 1) :: repeat (1, 2) 29403094 ++ w) by sec_eq.
    apply (sTUP2_1 [] 4 12 3 ((1, 1) :: repeat (1, 2) 33 ++ (1262, 2) :: (1, 1) :: repeat (1, 2) 2627 ++ (5503, 2) :: (1, 1) :: repeat (1, 2) 15411 ++ (29238, 2) :: (1, 1) :: repeat (1, 2) 116430 ++ (1483183, 2) :: (1, 1) :: repeat (1, 2) 3474178 ++ (4901382, 2) :: (1, 1) :: repeat (1, 2) 29403094 ++ w) 1); closearith.
  }
  (* step 260: P TDN *)
  apply (hsteps_trans _ (HB [5] 13 1 4 (repeat (1, 2) 1 ++ (1, 1) :: repeat (1, 2) 33 ++ (1262, 2) :: (1, 1) :: repeat (1, 2) 2627 ++ (5503, 2) :: (1, 1) :: repeat (1, 2) 15411 ++ (29238, 2) :: (1, 1) :: repeat (1, 2) 116430 ++ (1483183, 2) :: (1, 1) :: repeat (1, 2) 3474178 ++ (4901382, 2) :: (1, 1) :: repeat (1, 2) 29403094 ++ w) 1)).
  {
    apply (sTDN [5] 13 (repeat (1, 2) 1 ++ (1, 1) :: repeat (1, 2) 33 ++ (1262, 2) :: (1, 1) :: repeat (1, 2) 2627 ++ (5503, 2) :: (1, 1) :: repeat (1, 2) 15411 ++ (29238, 2) :: (1, 1) :: repeat (1, 2) 116430 ++ (1483183, 2) :: (1, 1) :: repeat (1, 2) 3474178 ++ (4901382, 2) :: (1, 1) :: repeat (1, 2) 29403094 ++ w) 1).
  }
  (* step 261: M pop12 (1,) *)
  apply (hsteps_trans _ (HB [5] 14 1 6 ((1, 1) :: repeat (1, 2) 33 ++ (1262, 2) :: (1, 1) :: repeat (1, 2) 2627 ++ (5503, 2) :: (1, 1) :: repeat (1, 2) 15411 ++ (29238, 2) :: (1, 1) :: repeat (1, 2) 116430 ++ (1483183, 2) :: (1, 1) :: repeat (1, 2) 3474178 ++ (4901382, 2) :: (1, 1) :: repeat (1, 2) 29403094 ++ w) 1)).
  {
    apply (pop12 1 [5] 13 4 ((1, 1) :: repeat (1, 2) 33 ++ (1262, 2) :: (1, 1) :: repeat (1, 2) 2627 ++ (5503, 2) :: (1, 1) :: repeat (1, 2) 15411 ++ (29238, 2) :: (1, 1) :: repeat (1, 2) 116430 ++ (1483183, 2) :: (1, 1) :: repeat (1, 2) 3474178 ++ (4901382, 2) :: (1, 1) :: repeat (1, 2) 29403094 ++ w) 1); closearith.
  }
  (* step 262: P POP *)
  apply (hsteps_trans _ (HB [5] 15 1 7 (repeat (1, 2) 33 ++ (1262, 2) :: (1, 1) :: repeat (1, 2) 2627 ++ (5503, 2) :: (1, 1) :: repeat (1, 2) 15411 ++ (29238, 2) :: (1, 1) :: repeat (1, 2) 116430 ++ (1483183, 2) :: (1, 1) :: repeat (1, 2) 3474178 ++ (4901382, 2) :: (1, 1) :: repeat (1, 2) 29403094 ++ w) 1)).
  {
    apply (sPOP1 [5] 14 6 (repeat (1, 2) 33 ++ (1262, 2) :: (1, 1) :: repeat (1, 2) 2627 ++ (5503, 2) :: (1, 1) :: repeat (1, 2) 15411 ++ (29238, 2) :: (1, 1) :: repeat (1, 2) 116430 ++ (1483183, 2) :: (1, 1) :: repeat (1, 2) 3474178 ++ (4901382, 2) :: (1, 1) :: repeat (1, 2) 29403094 ++ w) 1); closearith.
  }
  (* step 263: M pop12 (33,) *)
  apply (hsteps_trans _ (HB [5] 48 1 73 ((1262, 2) :: (1, 1) :: repeat (1, 2) 2627 ++ (5503, 2) :: (1, 1) :: repeat (1, 2) 15411 ++ (29238, 2) :: (1, 1) :: repeat (1, 2) 116430 ++ (1483183, 2) :: (1, 1) :: repeat (1, 2) 3474178 ++ (4901382, 2) :: (1, 1) :: repeat (1, 2) 29403094 ++ w) 1)).
  {
    apply (pop12 33 [5] 15 7 ((1262, 2) :: (1, 1) :: repeat (1, 2) 2627 ++ (5503, 2) :: (1, 1) :: repeat (1, 2) 15411 ++ (29238, 2) :: (1, 1) :: repeat (1, 2) 116430 ++ (1483183, 2) :: (1, 1) :: repeat (1, 2) 3474178 ++ (4901382, 2) :: (1, 1) :: repeat (1, 2) 29403094 ++ w) 1); closearith.
  }
  (* step 264: sTUP *)
  apply (hsteps_trans _ (HC [5] 48 72 2 ((1260, 2) :: (1, 1) :: repeat (1, 2) 2627 ++ (5503, 2) :: (1, 1) :: repeat (1, 2) 15411 ++ (29238, 2) :: (1, 1) :: repeat (1, 2) 116430 ++ (1483183, 2) :: (1, 1) :: repeat (1, 2) 3474178 ++ (4901382, 2) :: (1, 1) :: repeat (1, 2) 29403094 ++ w) 1)).
  {
    replace ((1260, 2) :: (1, 1) :: repeat (1, 2) 2627 ++ (5503, 2) :: (1, 1) :: repeat (1, 2) 15411 ++ (29238, 2) :: (1, 1) :: repeat (1, 2) 116430 ++ (1483183, 2) :: (1, 1) :: repeat (1, 2) 3474178 ++ (4901382, 2) :: (1, 1) :: repeat (1, 2) 29403094 ++ w) with ((1262 - 2, 2) :: (1, 1) :: repeat (1, 2) 2627 ++ (5503, 2) :: (1, 1) :: repeat (1, 2) 15411 ++ (29238, 2) :: (1, 1) :: repeat (1, 2) 116430 ++ (1483183, 2) :: (1, 1) :: repeat (1, 2) 3474178 ++ (4901382, 2) :: (1, 1) :: repeat (1, 2) 29403094 ++ w) by sec_eq.
    apply (sTUP [5] 48 73 1262 2 ((1, 1) :: repeat (1, 2) 2627 ++ (5503, 2) :: (1, 1) :: repeat (1, 2) 15411 ++ (29238, 2) :: (1, 1) :: repeat (1, 2) 116430 ++ (1483183, 2) :: (1, 1) :: repeat (1, 2) 3474178 ++ (4901382, 2) :: (1, 1) :: repeat (1, 2) 29403094 ++ w) 1); closearith.
  }
  (* step 265: hGRIND_even 34 *)
  apply (hsteps_trans _ (HB [5] 47 1 72 ((2, 2) :: (1260, 2) :: (1, 1) :: repeat (1, 2) 2627 ++ (5503, 2) :: (1, 1) :: repeat (1, 2) 15411 ++ (29238, 2) :: (1, 1) :: repeat (1, 2) 116430 ++ (1483183, 2) :: (1, 1) :: repeat (1, 2) 3474178 ++ (4901382, 2) :: (1, 1) :: repeat (1, 2) 29403094 ++ w) 1)).
  {
    apply (hGRIND_even 34 [5] 47 ((1260, 2) :: (1, 1) :: repeat (1, 2) 2627 ++ (5503, 2) :: (1, 1) :: repeat (1, 2) 15411 ++ (29238, 2) :: (1, 1) :: repeat (1, 2) 116430 ++ (1483183, 2) :: (1, 1) :: repeat (1, 2) 3474178 ++ (4901382, 2) :: (1, 1) :: repeat (1, 2) 29403094 ++ w) 1); closearith.
  }
  (* step 266: P TUP2_1 *)
  apply (hsteps_trans _ (HC [48; 5] 72 1 2 ((1258, 2) :: (1, 1) :: repeat (1, 2) 2627 ++ (5503, 2) :: (1, 1) :: repeat (1, 2) 15411 ++ (29238, 2) :: (1, 1) :: repeat (1, 2) 116430 ++ (1483183, 2) :: (1, 1) :: repeat (1, 2) 3474178 ++ (4901382, 2) :: (1, 1) :: repeat (1, 2) 29403094 ++ w) 1)).
  {
    replace ((1258, 2) :: (1, 1) :: repeat (1, 2) 2627 ++ (5503, 2) :: (1, 1) :: repeat (1, 2) 15411 ++ (29238, 2) :: (1, 1) :: repeat (1, 2) 116430 ++ (1483183, 2) :: (1, 1) :: repeat (1, 2) 3474178 ++ (4901382, 2) :: (1, 1) :: repeat (1, 2) 29403094 ++ w) with ((1260 - 2, 2) :: (1, 1) :: repeat (1, 2) 2627 ++ (5503, 2) :: (1, 1) :: repeat (1, 2) 15411 ++ (29238, 2) :: (1, 1) :: repeat (1, 2) 116430 ++ (1483183, 2) :: (1, 1) :: repeat (1, 2) 3474178 ++ (4901382, 2) :: (1, 1) :: repeat (1, 2) 29403094 ++ w) by sec_eq.
    apply (sTUP2_1 [5] 47 71 1260 ((1, 1) :: repeat (1, 2) 2627 ++ (5503, 2) :: (1, 1) :: repeat (1, 2) 15411 ++ (29238, 2) :: (1, 1) :: repeat (1, 2) 116430 ++ (1483183, 2) :: (1, 1) :: repeat (1, 2) 3474178 ++ (4901382, 2) :: (1, 1) :: repeat (1, 2) 29403094 ++ w) 1); closearith.
  }
  (* step 267: P TDN *)
  apply (hsteps_trans _ (HB [48; 5] 72 1 4 ((1258, 2) :: (1, 1) :: repeat (1, 2) 2627 ++ (5503, 2) :: (1, 1) :: repeat (1, 2) 15411 ++ (29238, 2) :: (1, 1) :: repeat (1, 2) 116430 ++ (1483183, 2) :: (1, 1) :: repeat (1, 2) 3474178 ++ (4901382, 2) :: (1, 1) :: repeat (1, 2) 29403094 ++ w) 1)).
  {
    apply (sTDN [48; 5] 72 ((1258, 2) :: (1, 1) :: repeat (1, 2) 2627 ++ (5503, 2) :: (1, 1) :: repeat (1, 2) 15411 ++ (29238, 2) :: (1, 1) :: repeat (1, 2) 116430 ++ (1483183, 2) :: (1, 1) :: repeat (1, 2) 3474178 ++ (4901382, 2) :: (1, 1) :: repeat (1, 2) 29403094 ++ w) 1).
  }
  (* step 268: sTUP *)
  apply (hsteps_trans _ (HC [48; 5] 72 3 2 ((1256, 2) :: (1, 1) :: repeat (1, 2) 2627 ++ (5503, 2) :: (1, 1) :: repeat (1, 2) 15411 ++ (29238, 2) :: (1, 1) :: repeat (1, 2) 116430 ++ (1483183, 2) :: (1, 1) :: repeat (1, 2) 3474178 ++ (4901382, 2) :: (1, 1) :: repeat (1, 2) 29403094 ++ w) 1)).
  {
    replace ((1256, 2) :: (1, 1) :: repeat (1, 2) 2627 ++ (5503, 2) :: (1, 1) :: repeat (1, 2) 15411 ++ (29238, 2) :: (1, 1) :: repeat (1, 2) 116430 ++ (1483183, 2) :: (1, 1) :: repeat (1, 2) 3474178 ++ (4901382, 2) :: (1, 1) :: repeat (1, 2) 29403094 ++ w) with ((1258 - 2, 2) :: (1, 1) :: repeat (1, 2) 2627 ++ (5503, 2) :: (1, 1) :: repeat (1, 2) 15411 ++ (29238, 2) :: (1, 1) :: repeat (1, 2) 116430 ++ (1483183, 2) :: (1, 1) :: repeat (1, 2) 3474178 ++ (4901382, 2) :: (1, 1) :: repeat (1, 2) 29403094 ++ w) by sec_eq.
    apply (sTUP [48; 5] 72 4 1258 2 ((1, 1) :: repeat (1, 2) 2627 ++ (5503, 2) :: (1, 1) :: repeat (1, 2) 15411 ++ (29238, 2) :: (1, 1) :: repeat (1, 2) 116430 ++ (1483183, 2) :: (1, 1) :: repeat (1, 2) 3474178 ++ (4901382, 2) :: (1, 1) :: repeat (1, 2) 29403094 ++ w) 1); closearith.
  }
  (* step 269: DIPGRIND 72 1112 *)
  apply (hsteps_trans _ (HC [48; 5] 0 3 2 (repeat (1, 2) 72 ++ (1112, 2) :: (1, 1) :: repeat (1, 2) 2627 ++ (5503, 2) :: (1, 1) :: repeat (1, 2) 15411 ++ (29238, 2) :: (1, 1) :: repeat (1, 2) 116430 ++ (1483183, 2) :: (1, 1) :: repeat (1, 2) 3474178 ++ (4901382, 2) :: (1, 1) :: repeat (1, 2) 29403094 ++ w) 1)).
  {
    apply (DIPGRIND 72 1112 [48; 5] ((1, 1) :: repeat (1, 2) 2627 ++ (5503, 2) :: (1, 1) :: repeat (1, 2) 15411 ++ (29238, 2) :: (1, 1) :: repeat (1, 2) 116430 ++ (1483183, 2) :: (1, 1) :: repeat (1, 2) 3474178 ++ (4901382, 2) :: (1, 1) :: repeat (1, 2) 29403094 ++ w) 1); closearith.
  }
  (* step 270: P PX2A *)
  apply (hsteps_trans _ (HC [] 4 46 2 ((1, 1) :: repeat (1, 2) 74 ++ (1112, 2) :: (1, 1) :: repeat (1, 2) 2627 ++ (5503, 2) :: (1, 1) :: repeat (1, 2) 15411 ++ (29238, 2) :: (1, 1) :: repeat (1, 2) 116430 ++ (1483183, 2) :: (1, 1) :: repeat (1, 2) 3474178 ++ (4901382, 2) :: (1, 1) :: repeat (1, 2) 29403094 ++ w) 1)).
  {
    exact (hsteps_step _ _ _ (hPX2A 45 4 [] (repeat (1, 2) 72 ++ (1112, 2) :: (1, 1) :: repeat (1, 2) 2627 ++ (5503, 2) :: (1, 1) :: repeat (1, 2) 15411 ++ (29238, 2) :: (1, 1) :: repeat (1, 2) 116430 ++ (1483183, 2) :: (1, 1) :: repeat (1, 2) 3474178 ++ (4901382, 2) :: (1, 1) :: repeat (1, 2) 29403094 ++ w) 1) (hsteps_refl _)).
  }
  (* step 271: P PUSH *)
  apply (hsteps_trans _ (HC [] 3 1 2 ((44, 2) :: (1, 1) :: repeat (1, 2) 74 ++ (1112, 2) :: (1, 1) :: repeat (1, 2) 2627 ++ (5503, 2) :: (1, 1) :: repeat (1, 2) 15411 ++ (29238, 2) :: (1, 1) :: repeat (1, 2) 116430 ++ (1483183, 2) :: (1, 1) :: repeat (1, 2) 3474178 ++ (4901382, 2) :: (1, 1) :: repeat (1, 2) 29403094 ++ w) 1)).
  {
    replace ((44, 2) :: (1, 1) :: repeat (1, 2) 74 ++ (1112, 2) :: (1, 1) :: repeat (1, 2) 2627 ++ (5503, 2) :: (1, 1) :: repeat (1, 2) 15411 ++ (29238, 2) :: (1, 1) :: repeat (1, 2) 116430 ++ (1483183, 2) :: (1, 1) :: repeat (1, 2) 3474178 ++ (4901382, 2) :: (1, 1) :: repeat (1, 2) 29403094 ++ w) with ((46 - 2, 2) :: (1, 1) :: repeat (1, 2) 74 ++ (1112, 2) :: (1, 1) :: repeat (1, 2) 2627 ++ (5503, 2) :: (1, 1) :: repeat (1, 2) 15411 ++ (29238, 2) :: (1, 1) :: repeat (1, 2) 116430 ++ (1483183, 2) :: (1, 1) :: repeat (1, 2) 3474178 ++ (4901382, 2) :: (1, 1) :: repeat (1, 2) 29403094 ++ w) by sec_eq.
    apply (sPUSH [] 3 46 ((1, 1) :: repeat (1, 2) 74 ++ (1112, 2) :: (1, 1) :: repeat (1, 2) 2627 ++ (5503, 2) :: (1, 1) :: repeat (1, 2) 15411 ++ (29238, 2) :: (1, 1) :: repeat (1, 2) 116430 ++ (1483183, 2) :: (1, 1) :: repeat (1, 2) 3474178 ++ (4901382, 2) :: (1, 1) :: repeat (1, 2) 29403094 ++ w) 1); closearith.
  }
  (* step 272: P TDN *)
  apply (hsteps_trans _ (HB [] 3 1 4 ((44, 2) :: (1, 1) :: repeat (1, 2) 74 ++ (1112, 2) :: (1, 1) :: repeat (1, 2) 2627 ++ (5503, 2) :: (1, 1) :: repeat (1, 2) 15411 ++ (29238, 2) :: (1, 1) :: repeat (1, 2) 116430 ++ (1483183, 2) :: (1, 1) :: repeat (1, 2) 3474178 ++ (4901382, 2) :: (1, 1) :: repeat (1, 2) 29403094 ++ w) 1)).
  {
    apply (sTDN [] 3 ((44, 2) :: (1, 1) :: repeat (1, 2) 74 ++ (1112, 2) :: (1, 1) :: repeat (1, 2) 2627 ++ (5503, 2) :: (1, 1) :: repeat (1, 2) 15411 ++ (29238, 2) :: (1, 1) :: repeat (1, 2) 116430 ++ (1483183, 2) :: (1, 1) :: repeat (1, 2) 3474178 ++ (4901382, 2) :: (1, 1) :: repeat (1, 2) 29403094 ++ w) 1).
  }
  (* step 273: sTUP *)
  apply (hsteps_trans _ (HC [] 3 3 2 ((42, 2) :: (1, 1) :: repeat (1, 2) 74 ++ (1112, 2) :: (1, 1) :: repeat (1, 2) 2627 ++ (5503, 2) :: (1, 1) :: repeat (1, 2) 15411 ++ (29238, 2) :: (1, 1) :: repeat (1, 2) 116430 ++ (1483183, 2) :: (1, 1) :: repeat (1, 2) 3474178 ++ (4901382, 2) :: (1, 1) :: repeat (1, 2) 29403094 ++ w) 1)).
  {
    replace ((42, 2) :: (1, 1) :: repeat (1, 2) 74 ++ (1112, 2) :: (1, 1) :: repeat (1, 2) 2627 ++ (5503, 2) :: (1, 1) :: repeat (1, 2) 15411 ++ (29238, 2) :: (1, 1) :: repeat (1, 2) 116430 ++ (1483183, 2) :: (1, 1) :: repeat (1, 2) 3474178 ++ (4901382, 2) :: (1, 1) :: repeat (1, 2) 29403094 ++ w) with ((44 - 2, 2) :: (1, 1) :: repeat (1, 2) 74 ++ (1112, 2) :: (1, 1) :: repeat (1, 2) 2627 ++ (5503, 2) :: (1, 1) :: repeat (1, 2) 15411 ++ (29238, 2) :: (1, 1) :: repeat (1, 2) 116430 ++ (1483183, 2) :: (1, 1) :: repeat (1, 2) 3474178 ++ (4901382, 2) :: (1, 1) :: repeat (1, 2) 29403094 ++ w) by sec_eq.
    apply (sTUP [] 3 4 44 2 ((1, 1) :: repeat (1, 2) 74 ++ (1112, 2) :: (1, 1) :: repeat (1, 2) 2627 ++ (5503, 2) :: (1, 1) :: repeat (1, 2) 15411 ++ (29238, 2) :: (1, 1) :: repeat (1, 2) 116430 ++ (1483183, 2) :: (1, 1) :: repeat (1, 2) 3474178 ++ (4901382, 2) :: (1, 1) :: repeat (1, 2) 29403094 ++ w) 1); closearith.
  }
  (* step 274: DIPGRIND 3 36 *)
  apply (hsteps_trans _ (HC [] 0 3 2 (repeat (1, 2) 3 ++ (36, 2) :: (1, 1) :: repeat (1, 2) 74 ++ (1112, 2) :: (1, 1) :: repeat (1, 2) 2627 ++ (5503, 2) :: (1, 1) :: repeat (1, 2) 15411 ++ (29238, 2) :: (1, 1) :: repeat (1, 2) 116430 ++ (1483183, 2) :: (1, 1) :: repeat (1, 2) 3474178 ++ (4901382, 2) :: (1, 1) :: repeat (1, 2) 29403094 ++ w) 1)).
  {
    apply (DIPGRIND 3 36 [] ((1, 1) :: repeat (1, 2) 74 ++ (1112, 2) :: (1, 1) :: repeat (1, 2) 2627 ++ (5503, 2) :: (1, 1) :: repeat (1, 2) 15411 ++ (29238, 2) :: (1, 1) :: repeat (1, 2) 116430 ++ (1483183, 2) :: (1, 1) :: repeat (1, 2) 3474178 ++ (4901382, 2) :: (1, 1) :: repeat (1, 2) 29403094 ++ w) 1); closearith.
  }
  (* step 275: P PUSHX *)
  apply (hsteps_trans _ (HB [] 1 1 7 (repeat (1, 2) 3 ++ (36, 2) :: (1, 1) :: repeat (1, 2) 74 ++ (1112, 2) :: (1, 1) :: repeat (1, 2) 2627 ++ (5503, 2) :: (1, 1) :: repeat (1, 2) 15411 ++ (29238, 2) :: (1, 1) :: repeat (1, 2) 116430 ++ (1483183, 2) :: (1, 1) :: repeat (1, 2) 3474178 ++ (4901382, 2) :: (1, 1) :: repeat (1, 2) 29403094 ++ w) 1)).
  {
    exact (hsteps_step _ _ _ (hPUSHX (repeat (1, 2) 3 ++ (36, 2) :: (1, 1) :: repeat (1, 2) 74 ++ (1112, 2) :: (1, 1) :: repeat (1, 2) 2627 ++ (5503, 2) :: (1, 1) :: repeat (1, 2) 15411 ++ (29238, 2) :: (1, 1) :: repeat (1, 2) 116430 ++ (1483183, 2) :: (1, 1) :: repeat (1, 2) 3474178 ++ (4901382, 2) :: (1, 1) :: repeat (1, 2) 29403094 ++ w) 1) (hsteps_refl _)).
  }
  (* step 276: M pop12 (3,) *)
  apply (hsteps_trans _ (HB [] 4 1 13 ((36, 2) :: (1, 1) :: repeat (1, 2) 74 ++ (1112, 2) :: (1, 1) :: repeat (1, 2) 2627 ++ (5503, 2) :: (1, 1) :: repeat (1, 2) 15411 ++ (29238, 2) :: (1, 1) :: repeat (1, 2) 116430 ++ (1483183, 2) :: (1, 1) :: repeat (1, 2) 3474178 ++ (4901382, 2) :: (1, 1) :: repeat (1, 2) 29403094 ++ w) 1)).
  {
    apply (pop12 3 [] 1 7 ((36, 2) :: (1, 1) :: repeat (1, 2) 74 ++ (1112, 2) :: (1, 1) :: repeat (1, 2) 2627 ++ (5503, 2) :: (1, 1) :: repeat (1, 2) 15411 ++ (29238, 2) :: (1, 1) :: repeat (1, 2) 116430 ++ (1483183, 2) :: (1, 1) :: repeat (1, 2) 3474178 ++ (4901382, 2) :: (1, 1) :: repeat (1, 2) 29403094 ++ w) 1); closearith.
  }
  (* step 277: sTUP *)
  apply (hsteps_trans _ (HC [] 4 12 2 ((34, 2) :: (1, 1) :: repeat (1, 2) 74 ++ (1112, 2) :: (1, 1) :: repeat (1, 2) 2627 ++ (5503, 2) :: (1, 1) :: repeat (1, 2) 15411 ++ (29238, 2) :: (1, 1) :: repeat (1, 2) 116430 ++ (1483183, 2) :: (1, 1) :: repeat (1, 2) 3474178 ++ (4901382, 2) :: (1, 1) :: repeat (1, 2) 29403094 ++ w) 1)).
  {
    replace ((34, 2) :: (1, 1) :: repeat (1, 2) 74 ++ (1112, 2) :: (1, 1) :: repeat (1, 2) 2627 ++ (5503, 2) :: (1, 1) :: repeat (1, 2) 15411 ++ (29238, 2) :: (1, 1) :: repeat (1, 2) 116430 ++ (1483183, 2) :: (1, 1) :: repeat (1, 2) 3474178 ++ (4901382, 2) :: (1, 1) :: repeat (1, 2) 29403094 ++ w) with ((36 - 2, 2) :: (1, 1) :: repeat (1, 2) 74 ++ (1112, 2) :: (1, 1) :: repeat (1, 2) 2627 ++ (5503, 2) :: (1, 1) :: repeat (1, 2) 15411 ++ (29238, 2) :: (1, 1) :: repeat (1, 2) 116430 ++ (1483183, 2) :: (1, 1) :: repeat (1, 2) 3474178 ++ (4901382, 2) :: (1, 1) :: repeat (1, 2) 29403094 ++ w) by sec_eq.
    apply (sTUP [] 4 13 36 2 ((1, 1) :: repeat (1, 2) 74 ++ (1112, 2) :: (1, 1) :: repeat (1, 2) 2627 ++ (5503, 2) :: (1, 1) :: repeat (1, 2) 15411 ++ (29238, 2) :: (1, 1) :: repeat (1, 2) 116430 ++ (1483183, 2) :: (1, 1) :: repeat (1, 2) 3474178 ++ (4901382, 2) :: (1, 1) :: repeat (1, 2) 29403094 ++ w) 1); closearith.
  }
  (* step 278: P PUSH *)
  apply (hsteps_trans _ (HC [] 3 1 2 ((10, 2) :: (34, 2) :: (1, 1) :: repeat (1, 2) 74 ++ (1112, 2) :: (1, 1) :: repeat (1, 2) 2627 ++ (5503, 2) :: (1, 1) :: repeat (1, 2) 15411 ++ (29238, 2) :: (1, 1) :: repeat (1, 2) 116430 ++ (1483183, 2) :: (1, 1) :: repeat (1, 2) 3474178 ++ (4901382, 2) :: (1, 1) :: repeat (1, 2) 29403094 ++ w) 1)).
  {
    replace ((10, 2) :: (34, 2) :: (1, 1) :: repeat (1, 2) 74 ++ (1112, 2) :: (1, 1) :: repeat (1, 2) 2627 ++ (5503, 2) :: (1, 1) :: repeat (1, 2) 15411 ++ (29238, 2) :: (1, 1) :: repeat (1, 2) 116430 ++ (1483183, 2) :: (1, 1) :: repeat (1, 2) 3474178 ++ (4901382, 2) :: (1, 1) :: repeat (1, 2) 29403094 ++ w) with ((12 - 2, 2) :: (34, 2) :: (1, 1) :: repeat (1, 2) 74 ++ (1112, 2) :: (1, 1) :: repeat (1, 2) 2627 ++ (5503, 2) :: (1, 1) :: repeat (1, 2) 15411 ++ (29238, 2) :: (1, 1) :: repeat (1, 2) 116430 ++ (1483183, 2) :: (1, 1) :: repeat (1, 2) 3474178 ++ (4901382, 2) :: (1, 1) :: repeat (1, 2) 29403094 ++ w) by sec_eq.
    apply (sPUSH [] 3 12 ((34, 2) :: (1, 1) :: repeat (1, 2) 74 ++ (1112, 2) :: (1, 1) :: repeat (1, 2) 2627 ++ (5503, 2) :: (1, 1) :: repeat (1, 2) 15411 ++ (29238, 2) :: (1, 1) :: repeat (1, 2) 116430 ++ (1483183, 2) :: (1, 1) :: repeat (1, 2) 3474178 ++ (4901382, 2) :: (1, 1) :: repeat (1, 2) 29403094 ++ w) 1); closearith.
  }
  (* step 279: P TDN *)
  apply (hsteps_trans _ (HB [] 3 1 4 ((10, 2) :: (34, 2) :: (1, 1) :: repeat (1, 2) 74 ++ (1112, 2) :: (1, 1) :: repeat (1, 2) 2627 ++ (5503, 2) :: (1, 1) :: repeat (1, 2) 15411 ++ (29238, 2) :: (1, 1) :: repeat (1, 2) 116430 ++ (1483183, 2) :: (1, 1) :: repeat (1, 2) 3474178 ++ (4901382, 2) :: (1, 1) :: repeat (1, 2) 29403094 ++ w) 1)).
  {
    apply (sTDN [] 3 ((10, 2) :: (34, 2) :: (1, 1) :: repeat (1, 2) 74 ++ (1112, 2) :: (1, 1) :: repeat (1, 2) 2627 ++ (5503, 2) :: (1, 1) :: repeat (1, 2) 15411 ++ (29238, 2) :: (1, 1) :: repeat (1, 2) 116430 ++ (1483183, 2) :: (1, 1) :: repeat (1, 2) 3474178 ++ (4901382, 2) :: (1, 1) :: repeat (1, 2) 29403094 ++ w) 1).
  }
  (* step 280: sTUP *)
  apply (hsteps_trans _ (HC [] 3 3 2 ((8, 2) :: (34, 2) :: (1, 1) :: repeat (1, 2) 74 ++ (1112, 2) :: (1, 1) :: repeat (1, 2) 2627 ++ (5503, 2) :: (1, 1) :: repeat (1, 2) 15411 ++ (29238, 2) :: (1, 1) :: repeat (1, 2) 116430 ++ (1483183, 2) :: (1, 1) :: repeat (1, 2) 3474178 ++ (4901382, 2) :: (1, 1) :: repeat (1, 2) 29403094 ++ w) 1)).
  {
    replace ((8, 2) :: (34, 2) :: (1, 1) :: repeat (1, 2) 74 ++ (1112, 2) :: (1, 1) :: repeat (1, 2) 2627 ++ (5503, 2) :: (1, 1) :: repeat (1, 2) 15411 ++ (29238, 2) :: (1, 1) :: repeat (1, 2) 116430 ++ (1483183, 2) :: (1, 1) :: repeat (1, 2) 3474178 ++ (4901382, 2) :: (1, 1) :: repeat (1, 2) 29403094 ++ w) with ((10 - 2, 2) :: (34, 2) :: (1, 1) :: repeat (1, 2) 74 ++ (1112, 2) :: (1, 1) :: repeat (1, 2) 2627 ++ (5503, 2) :: (1, 1) :: repeat (1, 2) 15411 ++ (29238, 2) :: (1, 1) :: repeat (1, 2) 116430 ++ (1483183, 2) :: (1, 1) :: repeat (1, 2) 3474178 ++ (4901382, 2) :: (1, 1) :: repeat (1, 2) 29403094 ++ w) by sec_eq.
    apply (sTUP [] 3 4 10 2 ((34, 2) :: (1, 1) :: repeat (1, 2) 74 ++ (1112, 2) :: (1, 1) :: repeat (1, 2) 2627 ++ (5503, 2) :: (1, 1) :: repeat (1, 2) 15411 ++ (29238, 2) :: (1, 1) :: repeat (1, 2) 116430 ++ (1483183, 2) :: (1, 1) :: repeat (1, 2) 3474178 ++ (4901382, 2) :: (1, 1) :: repeat (1, 2) 29403094 ++ w) 1); closearith.
  }
  (* step 281: DIPGRIND 3 2 *)
  apply (hsteps_trans _ (HC [] 0 3 2 (repeat (1, 2) 3 ++ (2, 2) :: (34, 2) :: (1, 1) :: repeat (1, 2) 74 ++ (1112, 2) :: (1, 1) :: repeat (1, 2) 2627 ++ (5503, 2) :: (1, 1) :: repeat (1, 2) 15411 ++ (29238, 2) :: (1, 1) :: repeat (1, 2) 116430 ++ (1483183, 2) :: (1, 1) :: repeat (1, 2) 3474178 ++ (4901382, 2) :: (1, 1) :: repeat (1, 2) 29403094 ++ w) 1)).
  {
    apply (DIPGRIND 3 2 [] ((34, 2) :: (1, 1) :: repeat (1, 2) 74 ++ (1112, 2) :: (1, 1) :: repeat (1, 2) 2627 ++ (5503, 2) :: (1, 1) :: repeat (1, 2) 15411 ++ (29238, 2) :: (1, 1) :: repeat (1, 2) 116430 ++ (1483183, 2) :: (1, 1) :: repeat (1, 2) 3474178 ++ (4901382, 2) :: (1, 1) :: repeat (1, 2) 29403094 ++ w) 1); closearith.
  }
  (* step 282: P PUSHX *)
  apply (hsteps_trans _ (HB [] 1 1 7 (repeat (1, 2) 3 ++ (2, 2) :: (34, 2) :: (1, 1) :: repeat (1, 2) 74 ++ (1112, 2) :: (1, 1) :: repeat (1, 2) 2627 ++ (5503, 2) :: (1, 1) :: repeat (1, 2) 15411 ++ (29238, 2) :: (1, 1) :: repeat (1, 2) 116430 ++ (1483183, 2) :: (1, 1) :: repeat (1, 2) 3474178 ++ (4901382, 2) :: (1, 1) :: repeat (1, 2) 29403094 ++ w) 1)).
  {
    exact (hsteps_step _ _ _ (hPUSHX (repeat (1, 2) 3 ++ (2, 2) :: (34, 2) :: (1, 1) :: repeat (1, 2) 74 ++ (1112, 2) :: (1, 1) :: repeat (1, 2) 2627 ++ (5503, 2) :: (1, 1) :: repeat (1, 2) 15411 ++ (29238, 2) :: (1, 1) :: repeat (1, 2) 116430 ++ (1483183, 2) :: (1, 1) :: repeat (1, 2) 3474178 ++ (4901382, 2) :: (1, 1) :: repeat (1, 2) 29403094 ++ w) 1) (hsteps_refl _)).
  }
  (* step 283: M pop12 (3,) *)
  apply (hsteps_trans _ (HB [] 4 1 13 ((2, 2) :: (34, 2) :: (1, 1) :: repeat (1, 2) 74 ++ (1112, 2) :: (1, 1) :: repeat (1, 2) 2627 ++ (5503, 2) :: (1, 1) :: repeat (1, 2) 15411 ++ (29238, 2) :: (1, 1) :: repeat (1, 2) 116430 ++ (1483183, 2) :: (1, 1) :: repeat (1, 2) 3474178 ++ (4901382, 2) :: (1, 1) :: repeat (1, 2) 29403094 ++ w) 1)).
  {
    apply (pop12 3 [] 1 7 ((2, 2) :: (34, 2) :: (1, 1) :: repeat (1, 2) 74 ++ (1112, 2) :: (1, 1) :: repeat (1, 2) 2627 ++ (5503, 2) :: (1, 1) :: repeat (1, 2) 15411 ++ (29238, 2) :: (1, 1) :: repeat (1, 2) 116430 ++ (1483183, 2) :: (1, 1) :: repeat (1, 2) 3474178 ++ (4901382, 2) :: (1, 1) :: repeat (1, 2) 29403094 ++ w) 1); closearith.
  }
  (* step 284: P TUP2_1 *)
  apply (hsteps_trans _ (HC [5] 13 1 2 ((32, 2) :: (1, 1) :: repeat (1, 2) 74 ++ (1112, 2) :: (1, 1) :: repeat (1, 2) 2627 ++ (5503, 2) :: (1, 1) :: repeat (1, 2) 15411 ++ (29238, 2) :: (1, 1) :: repeat (1, 2) 116430 ++ (1483183, 2) :: (1, 1) :: repeat (1, 2) 3474178 ++ (4901382, 2) :: (1, 1) :: repeat (1, 2) 29403094 ++ w) 1)).
  {
    replace ((32, 2) :: (1, 1) :: repeat (1, 2) 74 ++ (1112, 2) :: (1, 1) :: repeat (1, 2) 2627 ++ (5503, 2) :: (1, 1) :: repeat (1, 2) 15411 ++ (29238, 2) :: (1, 1) :: repeat (1, 2) 116430 ++ (1483183, 2) :: (1, 1) :: repeat (1, 2) 3474178 ++ (4901382, 2) :: (1, 1) :: repeat (1, 2) 29403094 ++ w) with ((34 - 2, 2) :: (1, 1) :: repeat (1, 2) 74 ++ (1112, 2) :: (1, 1) :: repeat (1, 2) 2627 ++ (5503, 2) :: (1, 1) :: repeat (1, 2) 15411 ++ (29238, 2) :: (1, 1) :: repeat (1, 2) 116430 ++ (1483183, 2) :: (1, 1) :: repeat (1, 2) 3474178 ++ (4901382, 2) :: (1, 1) :: repeat (1, 2) 29403094 ++ w) by sec_eq.
    apply (sTUP2_1 [] 4 12 34 ((1, 1) :: repeat (1, 2) 74 ++ (1112, 2) :: (1, 1) :: repeat (1, 2) 2627 ++ (5503, 2) :: (1, 1) :: repeat (1, 2) 15411 ++ (29238, 2) :: (1, 1) :: repeat (1, 2) 116430 ++ (1483183, 2) :: (1, 1) :: repeat (1, 2) 3474178 ++ (4901382, 2) :: (1, 1) :: repeat (1, 2) 29403094 ++ w) 1); closearith.
  }
  (* step 285: P TDN *)
  apply (hsteps_trans _ (HB [5] 13 1 4 ((32, 2) :: (1, 1) :: repeat (1, 2) 74 ++ (1112, 2) :: (1, 1) :: repeat (1, 2) 2627 ++ (5503, 2) :: (1, 1) :: repeat (1, 2) 15411 ++ (29238, 2) :: (1, 1) :: repeat (1, 2) 116430 ++ (1483183, 2) :: (1, 1) :: repeat (1, 2) 3474178 ++ (4901382, 2) :: (1, 1) :: repeat (1, 2) 29403094 ++ w) 1)).
  {
    apply (sTDN [5] 13 ((32, 2) :: (1, 1) :: repeat (1, 2) 74 ++ (1112, 2) :: (1, 1) :: repeat (1, 2) 2627 ++ (5503, 2) :: (1, 1) :: repeat (1, 2) 15411 ++ (29238, 2) :: (1, 1) :: repeat (1, 2) 116430 ++ (1483183, 2) :: (1, 1) :: repeat (1, 2) 3474178 ++ (4901382, 2) :: (1, 1) :: repeat (1, 2) 29403094 ++ w) 1).
  }
  (* step 286: sTUP *)
  apply (hsteps_trans _ (HC [5] 13 3 2 ((30, 2) :: (1, 1) :: repeat (1, 2) 74 ++ (1112, 2) :: (1, 1) :: repeat (1, 2) 2627 ++ (5503, 2) :: (1, 1) :: repeat (1, 2) 15411 ++ (29238, 2) :: (1, 1) :: repeat (1, 2) 116430 ++ (1483183, 2) :: (1, 1) :: repeat (1, 2) 3474178 ++ (4901382, 2) :: (1, 1) :: repeat (1, 2) 29403094 ++ w) 1)).
  {
    replace ((30, 2) :: (1, 1) :: repeat (1, 2) 74 ++ (1112, 2) :: (1, 1) :: repeat (1, 2) 2627 ++ (5503, 2) :: (1, 1) :: repeat (1, 2) 15411 ++ (29238, 2) :: (1, 1) :: repeat (1, 2) 116430 ++ (1483183, 2) :: (1, 1) :: repeat (1, 2) 3474178 ++ (4901382, 2) :: (1, 1) :: repeat (1, 2) 29403094 ++ w) with ((32 - 2, 2) :: (1, 1) :: repeat (1, 2) 74 ++ (1112, 2) :: (1, 1) :: repeat (1, 2) 2627 ++ (5503, 2) :: (1, 1) :: repeat (1, 2) 15411 ++ (29238, 2) :: (1, 1) :: repeat (1, 2) 116430 ++ (1483183, 2) :: (1, 1) :: repeat (1, 2) 3474178 ++ (4901382, 2) :: (1, 1) :: repeat (1, 2) 29403094 ++ w) by sec_eq.
    apply (sTUP [5] 13 4 32 2 ((1, 1) :: repeat (1, 2) 74 ++ (1112, 2) :: (1, 1) :: repeat (1, 2) 2627 ++ (5503, 2) :: (1, 1) :: repeat (1, 2) 15411 ++ (29238, 2) :: (1, 1) :: repeat (1, 2) 116430 ++ (1483183, 2) :: (1, 1) :: repeat (1, 2) 3474178 ++ (4901382, 2) :: (1, 1) :: repeat (1, 2) 29403094 ++ w) 1); closearith.
  }
  (* step 287: DIPGRIND 13 4 *)
  apply (hsteps_trans _ (HC [5] 0 3 2 (repeat (1, 2) 13 ++ (4, 2) :: (1, 1) :: repeat (1, 2) 74 ++ (1112, 2) :: (1, 1) :: repeat (1, 2) 2627 ++ (5503, 2) :: (1, 1) :: repeat (1, 2) 15411 ++ (29238, 2) :: (1, 1) :: repeat (1, 2) 116430 ++ (1483183, 2) :: (1, 1) :: repeat (1, 2) 3474178 ++ (4901382, 2) :: (1, 1) :: repeat (1, 2) 29403094 ++ w) 1)).
  {
    apply (DIPGRIND 13 4 [5] ((1, 1) :: repeat (1, 2) 74 ++ (1112, 2) :: (1, 1) :: repeat (1, 2) 2627 ++ (5503, 2) :: (1, 1) :: repeat (1, 2) 15411 ++ (29238, 2) :: (1, 1) :: repeat (1, 2) 116430 ++ (1483183, 2) :: (1, 1) :: repeat (1, 2) 3474178 ++ (4901382, 2) :: (1, 1) :: repeat (1, 2) 29403094 ++ w) 1); closearith.
  }
  (* step 288: P PX2Bgen *)
  apply (hsteps_trans _ (HB [0] 3 1 2 (repeat (1, 2) 1 ++ (1, 1) :: repeat (1, 2) 15 ++ (4, 2) :: (1, 1) :: repeat (1, 2) 74 ++ (1112, 2) :: (1, 1) :: repeat (1, 2) 2627 ++ (5503, 2) :: (1, 1) :: repeat (1, 2) 15411 ++ (29238, 2) :: (1, 1) :: repeat (1, 2) 116430 ++ (1483183, 2) :: (1, 1) :: repeat (1, 2) 3474178 ++ (4901382, 2) :: (1, 1) :: repeat (1, 2) 29403094 ++ w) 1)).
  {
    exact (hsteps_step _ _ _ (hPX2Bgen 0 (repeat (1, 2) 13 ++ (4, 2) :: (1, 1) :: repeat (1, 2) 74 ++ (1112, 2) :: (1, 1) :: repeat (1, 2) 2627 ++ (5503, 2) :: (1, 1) :: repeat (1, 2) 15411 ++ (29238, 2) :: (1, 1) :: repeat (1, 2) 116430 ++ (1483183, 2) :: (1, 1) :: repeat (1, 2) 3474178 ++ (4901382, 2) :: (1, 1) :: repeat (1, 2) 29403094 ++ w) 1) (hsteps_refl _)).
  }
  (* step 289: M pop12 (1,) *)
  apply (pop12 1 [0] 3 2 ((1, 1) :: repeat (1, 2) 15 ++ (4, 2) :: (1, 1) :: repeat (1, 2) 74 ++ (1112, 2) :: (1, 1) :: repeat (1, 2) 2627 ++ (5503, 2) :: (1, 1) :: repeat (1, 2) 15411 ++ (29238, 2) :: (1, 1) :: repeat (1, 2) 116430 ++ (1483183, 2) :: (1, 1) :: repeat (1, 2) 3474178 ++ (4901382, 2) :: (1, 1) :: repeat (1, 2) 29403094 ++ w) 1); closearith.
Qed.

(* CASCADE59h: steps 290-345 of the CASCADE59 chain. *)
Lemma CASCADE59h : forall w,
  hsteps (HB [0] 4 1 4 ((1, 1) :: repeat (1, 2) 15 ++ (4, 2) :: (1, 1) :: repeat (1, 2) 74 ++ (1112, 2) :: (1, 1) :: repeat (1, 2) 2627 ++ (5503, 2) :: (1, 1) :: repeat (1, 2) 15411 ++ (29238, 2) :: (1, 1) :: repeat (1, 2) 116430 ++ (1483183, 2) :: (1, 1) :: repeat (1, 2) 3474178 ++ (4901382, 2) :: (1, 1) :: repeat (1, 2) 29403094 ++ w) 1)
         (HB [] 3 1 4 ((10, 2) :: (1, 1) :: repeat (1, 2) 40 ++ (144, 2) :: (1, 1) :: repeat (1, 2) 312 ++ (180, 2) :: (1, 1) :: repeat (1, 2) 2627 ++ (5503, 2) :: (1, 1) :: repeat (1, 2) 15411 ++ (29238, 2) :: (1, 1) :: repeat (1, 2) 116430 ++ (1483183, 2) :: (1, 1) :: repeat (1, 2) 3474178 ++ (4901382, 2) :: (1, 1) :: repeat (1, 2) 29403094 ++ w) 1).
Proof.
  intro w.
  (* step 290: P POP *)
  apply (hsteps_trans _ (HB [0] 5 1 5 (repeat (1, 2) 15 ++ (4, 2) :: (1, 1) :: repeat (1, 2) 74 ++ (1112, 2) :: (1, 1) :: repeat (1, 2) 2627 ++ (5503, 2) :: (1, 1) :: repeat (1, 2) 15411 ++ (29238, 2) :: (1, 1) :: repeat (1, 2) 116430 ++ (1483183, 2) :: (1, 1) :: repeat (1, 2) 3474178 ++ (4901382, 2) :: (1, 1) :: repeat (1, 2) 29403094 ++ w) 1)).
  {
    apply (sPOP1 [0] 4 4 (repeat (1, 2) 15 ++ (4, 2) :: (1, 1) :: repeat (1, 2) 74 ++ (1112, 2) :: (1, 1) :: repeat (1, 2) 2627 ++ (5503, 2) :: (1, 1) :: repeat (1, 2) 15411 ++ (29238, 2) :: (1, 1) :: repeat (1, 2) 116430 ++ (1483183, 2) :: (1, 1) :: repeat (1, 2) 3474178 ++ (4901382, 2) :: (1, 1) :: repeat (1, 2) 29403094 ++ w) 1); closearith.
  }
  (* step 291: M pop12 (15,) *)
  apply (hsteps_trans _ (HB [0] 20 1 35 ((4, 2) :: (1, 1) :: repeat (1, 2) 74 ++ (1112, 2) :: (1, 1) :: repeat (1, 2) 2627 ++ (5503, 2) :: (1, 1) :: repeat (1, 2) 15411 ++ (29238, 2) :: (1, 1) :: repeat (1, 2) 116430 ++ (1483183, 2) :: (1, 1) :: repeat (1, 2) 3474178 ++ (4901382, 2) :: (1, 1) :: repeat (1, 2) 29403094 ++ w) 1)).
  {
    apply (pop12 15 [0] 5 5 ((4, 2) :: (1, 1) :: repeat (1, 2) 74 ++ (1112, 2) :: (1, 1) :: repeat (1, 2) 2627 ++ (5503, 2) :: (1, 1) :: repeat (1, 2) 15411 ++ (29238, 2) :: (1, 1) :: repeat (1, 2) 116430 ++ (1483183, 2) :: (1, 1) :: repeat (1, 2) 3474178 ++ (4901382, 2) :: (1, 1) :: repeat (1, 2) 29403094 ++ w) 1); closearith.
  }
  (* step 292: sTUP *)
  apply (hsteps_trans _ (HC [0] 20 34 2 ((2, 2) :: (1, 1) :: repeat (1, 2) 74 ++ (1112, 2) :: (1, 1) :: repeat (1, 2) 2627 ++ (5503, 2) :: (1, 1) :: repeat (1, 2) 15411 ++ (29238, 2) :: (1, 1) :: repeat (1, 2) 116430 ++ (1483183, 2) :: (1, 1) :: repeat (1, 2) 3474178 ++ (4901382, 2) :: (1, 1) :: repeat (1, 2) 29403094 ++ w) 1)).
  {
    replace ((2, 2) :: (1, 1) :: repeat (1, 2) 74 ++ (1112, 2) :: (1, 1) :: repeat (1, 2) 2627 ++ (5503, 2) :: (1, 1) :: repeat (1, 2) 15411 ++ (29238, 2) :: (1, 1) :: repeat (1, 2) 116430 ++ (1483183, 2) :: (1, 1) :: repeat (1, 2) 3474178 ++ (4901382, 2) :: (1, 1) :: repeat (1, 2) 29403094 ++ w) with ((4 - 2, 2) :: (1, 1) :: repeat (1, 2) 74 ++ (1112, 2) :: (1, 1) :: repeat (1, 2) 2627 ++ (5503, 2) :: (1, 1) :: repeat (1, 2) 15411 ++ (29238, 2) :: (1, 1) :: repeat (1, 2) 116430 ++ (1483183, 2) :: (1, 1) :: repeat (1, 2) 3474178 ++ (4901382, 2) :: (1, 1) :: repeat (1, 2) 29403094 ++ w) by sec_eq.
    apply (sTUP [0] 20 35 4 2 ((1, 1) :: repeat (1, 2) 74 ++ (1112, 2) :: (1, 1) :: repeat (1, 2) 2627 ++ (5503, 2) :: (1, 1) :: repeat (1, 2) 15411 ++ (29238, 2) :: (1, 1) :: repeat (1, 2) 116430 ++ (1483183, 2) :: (1, 1) :: repeat (1, 2) 3474178 ++ (4901382, 2) :: (1, 1) :: repeat (1, 2) 29403094 ++ w) 1); closearith.
  }
  (* step 293: hGRIND_even 15 *)
  apply (hsteps_trans _ (HB [0] 19 1 34 ((2, 2) :: (2, 2) :: (1, 1) :: repeat (1, 2) 74 ++ (1112, 2) :: (1, 1) :: repeat (1, 2) 2627 ++ (5503, 2) :: (1, 1) :: repeat (1, 2) 15411 ++ (29238, 2) :: (1, 1) :: repeat (1, 2) 116430 ++ (1483183, 2) :: (1, 1) :: repeat (1, 2) 3474178 ++ (4901382, 2) :: (1, 1) :: repeat (1, 2) 29403094 ++ w) 1)).
  {
    apply (hGRIND_even 15 [0] 19 ((2, 2) :: (1, 1) :: repeat (1, 2) 74 ++ (1112, 2) :: (1, 1) :: repeat (1, 2) 2627 ++ (5503, 2) :: (1, 1) :: repeat (1, 2) 15411 ++ (29238, 2) :: (1, 1) :: repeat (1, 2) 116430 ++ (1483183, 2) :: (1, 1) :: repeat (1, 2) 3474178 ++ (4901382, 2) :: (1, 1) :: repeat (1, 2) 29403094 ++ w) 1); closearith.
  }
  (* step 294: P TRANS2_2 *)
  apply (hsteps_trans _ (HB [35; 20; 0] 3 1 3 (repeat (1, 2) 74 ++ (1112, 2) :: (1, 1) :: repeat (1, 2) 2627 ++ (5503, 2) :: (1, 1) :: repeat (1, 2) 15411 ++ (29238, 2) :: (1, 1) :: repeat (1, 2) 116430 ++ (1483183, 2) :: (1, 1) :: repeat (1, 2) 3474178 ++ (4901382, 2) :: (1, 1) :: repeat (1, 2) 29403094 ++ w) 1)).
  {
    apply (hsteps_step _ (HB [35; 20; 0] 3 1 3 (repeat (1, 2) 74 ++ (1112, 2) :: (1, 1) :: repeat (1, 2) 2627 ++ (5503, 2) :: (1, 1) :: repeat (1, 2) 15411 ++ (29238, 2) :: (1, 1) :: repeat (1, 2) 116430 ++ (1483183, 2) :: (1, 1) :: repeat (1, 2) 3474178 ++ (4901382, 2) :: (1, 1) :: repeat (1, 2) 29403094 ++ w) 1)); [apply hTRANS2_2; closearith | apply hsteps_refl].
  }
  (* step 295: M pop12 (74,) *)
  apply (hsteps_trans _ (HB [35; 20; 0] 77 1 151 ((1112, 2) :: (1, 1) :: repeat (1, 2) 2627 ++ (5503, 2) :: (1, 1) :: repeat (1, 2) 15411 ++ (29238, 2) :: (1, 1) :: repeat (1, 2) 116430 ++ (1483183, 2) :: (1, 1) :: repeat (1, 2) 3474178 ++ (4901382, 2) :: (1, 1) :: repeat (1, 2) 29403094 ++ w) 1)).
  {
    apply (pop12 74 [35; 20; 0] 3 3 ((1112, 2) :: (1, 1) :: repeat (1, 2) 2627 ++ (5503, 2) :: (1, 1) :: repeat (1, 2) 15411 ++ (29238, 2) :: (1, 1) :: repeat (1, 2) 116430 ++ (1483183, 2) :: (1, 1) :: repeat (1, 2) 3474178 ++ (4901382, 2) :: (1, 1) :: repeat (1, 2) 29403094 ++ w) 1); closearith.
  }
  (* step 296: sTUP *)
  apply (hsteps_trans _ (HC [35; 20; 0] 77 150 2 ((1110, 2) :: (1, 1) :: repeat (1, 2) 2627 ++ (5503, 2) :: (1, 1) :: repeat (1, 2) 15411 ++ (29238, 2) :: (1, 1) :: repeat (1, 2) 116430 ++ (1483183, 2) :: (1, 1) :: repeat (1, 2) 3474178 ++ (4901382, 2) :: (1, 1) :: repeat (1, 2) 29403094 ++ w) 1)).
  {
    replace ((1110, 2) :: (1, 1) :: repeat (1, 2) 2627 ++ (5503, 2) :: (1, 1) :: repeat (1, 2) 15411 ++ (29238, 2) :: (1, 1) :: repeat (1, 2) 116430 ++ (1483183, 2) :: (1, 1) :: repeat (1, 2) 3474178 ++ (4901382, 2) :: (1, 1) :: repeat (1, 2) 29403094 ++ w) with ((1112 - 2, 2) :: (1, 1) :: repeat (1, 2) 2627 ++ (5503, 2) :: (1, 1) :: repeat (1, 2) 15411 ++ (29238, 2) :: (1, 1) :: repeat (1, 2) 116430 ++ (1483183, 2) :: (1, 1) :: repeat (1, 2) 3474178 ++ (4901382, 2) :: (1, 1) :: repeat (1, 2) 29403094 ++ w) by sec_eq.
    apply (sTUP [35; 20; 0] 77 151 1112 2 ((1, 1) :: repeat (1, 2) 2627 ++ (5503, 2) :: (1, 1) :: repeat (1, 2) 15411 ++ (29238, 2) :: (1, 1) :: repeat (1, 2) 116430 ++ (1483183, 2) :: (1, 1) :: repeat (1, 2) 3474178 ++ (4901382, 2) :: (1, 1) :: repeat (1, 2) 29403094 ++ w) 1); closearith.
  }
  (* step 297: hGRIND_even 73 *)
  apply (hsteps_trans _ (HB [35; 20; 0] 76 1 150 ((2, 2) :: (1110, 2) :: (1, 1) :: repeat (1, 2) 2627 ++ (5503, 2) :: (1, 1) :: repeat (1, 2) 15411 ++ (29238, 2) :: (1, 1) :: repeat (1, 2) 116430 ++ (1483183, 2) :: (1, 1) :: repeat (1, 2) 3474178 ++ (4901382, 2) :: (1, 1) :: repeat (1, 2) 29403094 ++ w) 1)).
  {
    apply (hGRIND_even 73 [35; 20; 0] 76 ((1110, 2) :: (1, 1) :: repeat (1, 2) 2627 ++ (5503, 2) :: (1, 1) :: repeat (1, 2) 15411 ++ (29238, 2) :: (1, 1) :: repeat (1, 2) 116430 ++ (1483183, 2) :: (1, 1) :: repeat (1, 2) 3474178 ++ (4901382, 2) :: (1, 1) :: repeat (1, 2) 29403094 ++ w) 1); closearith.
  }
  (* step 298: P TUP2_1 *)
  apply (hsteps_trans _ (HC [77; 35; 20; 0] 150 1 2 ((1108, 2) :: (1, 1) :: repeat (1, 2) 2627 ++ (5503, 2) :: (1, 1) :: repeat (1, 2) 15411 ++ (29238, 2) :: (1, 1) :: repeat (1, 2) 116430 ++ (1483183, 2) :: (1, 1) :: repeat (1, 2) 3474178 ++ (4901382, 2) :: (1, 1) :: repeat (1, 2) 29403094 ++ w) 1)).
  {
    replace ((1108, 2) :: (1, 1) :: repeat (1, 2) 2627 ++ (5503, 2) :: (1, 1) :: repeat (1, 2) 15411 ++ (29238, 2) :: (1, 1) :: repeat (1, 2) 116430 ++ (1483183, 2) :: (1, 1) :: repeat (1, 2) 3474178 ++ (4901382, 2) :: (1, 1) :: repeat (1, 2) 29403094 ++ w) with ((1110 - 2, 2) :: (1, 1) :: repeat (1, 2) 2627 ++ (5503, 2) :: (1, 1) :: repeat (1, 2) 15411 ++ (29238, 2) :: (1, 1) :: repeat (1, 2) 116430 ++ (1483183, 2) :: (1, 1) :: repeat (1, 2) 3474178 ++ (4901382, 2) :: (1, 1) :: repeat (1, 2) 29403094 ++ w) by sec_eq.
    apply (sTUP2_1 [35; 20; 0] 76 149 1110 ((1, 1) :: repeat (1, 2) 2627 ++ (5503, 2) :: (1, 1) :: repeat (1, 2) 15411 ++ (29238, 2) :: (1, 1) :: repeat (1, 2) 116430 ++ (1483183, 2) :: (1, 1) :: repeat (1, 2) 3474178 ++ (4901382, 2) :: (1, 1) :: repeat (1, 2) 29403094 ++ w) 1); closearith.
  }
  (* step 299: P TDN *)
  apply (hsteps_trans _ (HB [77; 35; 20; 0] 150 1 4 ((1108, 2) :: (1, 1) :: repeat (1, 2) 2627 ++ (5503, 2) :: (1, 1) :: repeat (1, 2) 15411 ++ (29238, 2) :: (1, 1) :: repeat (1, 2) 116430 ++ (1483183, 2) :: (1, 1) :: repeat (1, 2) 3474178 ++ (4901382, 2) :: (1, 1) :: repeat (1, 2) 29403094 ++ w) 1)).
  {
    apply (sTDN [77; 35; 20; 0] 150 ((1108, 2) :: (1, 1) :: repeat (1, 2) 2627 ++ (5503, 2) :: (1, 1) :: repeat (1, 2) 15411 ++ (29238, 2) :: (1, 1) :: repeat (1, 2) 116430 ++ (1483183, 2) :: (1, 1) :: repeat (1, 2) 3474178 ++ (4901382, 2) :: (1, 1) :: repeat (1, 2) 29403094 ++ w) 1).
  }
  (* step 300: sTUP *)
  apply (hsteps_trans _ (HC [77; 35; 20; 0] 150 3 2 ((1106, 2) :: (1, 1) :: repeat (1, 2) 2627 ++ (5503, 2) :: (1, 1) :: repeat (1, 2) 15411 ++ (29238, 2) :: (1, 1) :: repeat (1, 2) 116430 ++ (1483183, 2) :: (1, 1) :: repeat (1, 2) 3474178 ++ (4901382, 2) :: (1, 1) :: repeat (1, 2) 29403094 ++ w) 1)).
  {
    replace ((1106, 2) :: (1, 1) :: repeat (1, 2) 2627 ++ (5503, 2) :: (1, 1) :: repeat (1, 2) 15411 ++ (29238, 2) :: (1, 1) :: repeat (1, 2) 116430 ++ (1483183, 2) :: (1, 1) :: repeat (1, 2) 3474178 ++ (4901382, 2) :: (1, 1) :: repeat (1, 2) 29403094 ++ w) with ((1108 - 2, 2) :: (1, 1) :: repeat (1, 2) 2627 ++ (5503, 2) :: (1, 1) :: repeat (1, 2) 15411 ++ (29238, 2) :: (1, 1) :: repeat (1, 2) 116430 ++ (1483183, 2) :: (1, 1) :: repeat (1, 2) 3474178 ++ (4901382, 2) :: (1, 1) :: repeat (1, 2) 29403094 ++ w) by sec_eq.
    apply (sTUP [77; 35; 20; 0] 150 4 1108 2 ((1, 1) :: repeat (1, 2) 2627 ++ (5503, 2) :: (1, 1) :: repeat (1, 2) 15411 ++ (29238, 2) :: (1, 1) :: repeat (1, 2) 116430 ++ (1483183, 2) :: (1, 1) :: repeat (1, 2) 3474178 ++ (4901382, 2) :: (1, 1) :: repeat (1, 2) 29403094 ++ w) 1); closearith.
  }
  (* step 301: DIPGRIND 150 806 *)
  apply (hsteps_trans _ (HC [77; 35; 20; 0] 0 3 2 (repeat (1, 2) 150 ++ (806, 2) :: (1, 1) :: repeat (1, 2) 2627 ++ (5503, 2) :: (1, 1) :: repeat (1, 2) 15411 ++ (29238, 2) :: (1, 1) :: repeat (1, 2) 116430 ++ (1483183, 2) :: (1, 1) :: repeat (1, 2) 3474178 ++ (4901382, 2) :: (1, 1) :: repeat (1, 2) 29403094 ++ w) 1)).
  {
    apply (DIPGRIND 150 806 [77; 35; 20; 0] ((1, 1) :: repeat (1, 2) 2627 ++ (5503, 2) :: (1, 1) :: repeat (1, 2) 15411 ++ (29238, 2) :: (1, 1) :: repeat (1, 2) 116430 ++ (1483183, 2) :: (1, 1) :: repeat (1, 2) 3474178 ++ (4901382, 2) :: (1, 1) :: repeat (1, 2) 29403094 ++ w) 1); closearith.
  }
  (* step 302: P PX2A *)
  apply (hsteps_trans _ (HC [20; 0] 34 75 2 ((1, 1) :: repeat (1, 2) 152 ++ (806, 2) :: (1, 1) :: repeat (1, 2) 2627 ++ (5503, 2) :: (1, 1) :: repeat (1, 2) 15411 ++ (29238, 2) :: (1, 1) :: repeat (1, 2) 116430 ++ (1483183, 2) :: (1, 1) :: repeat (1, 2) 3474178 ++ (4901382, 2) :: (1, 1) :: repeat (1, 2) 29403094 ++ w) 1)).
  {
    exact (hsteps_step _ _ _ (hPX2A 74 34 [20; 0] (repeat (1, 2) 150 ++ (806, 2) :: (1, 1) :: repeat (1, 2) 2627 ++ (5503, 2) :: (1, 1) :: repeat (1, 2) 15411 ++ (29238, 2) :: (1, 1) :: repeat (1, 2) 116430 ++ (1483183, 2) :: (1, 1) :: repeat (1, 2) 3474178 ++ (4901382, 2) :: (1, 1) :: repeat (1, 2) 29403094 ++ w) 1) (hsteps_refl _)).
  }
  (* step 303: P PUSH *)
  apply (hsteps_trans _ (HC [20; 0] 33 1 2 ((73, 2) :: (1, 1) :: repeat (1, 2) 152 ++ (806, 2) :: (1, 1) :: repeat (1, 2) 2627 ++ (5503, 2) :: (1, 1) :: repeat (1, 2) 15411 ++ (29238, 2) :: (1, 1) :: repeat (1, 2) 116430 ++ (1483183, 2) :: (1, 1) :: repeat (1, 2) 3474178 ++ (4901382, 2) :: (1, 1) :: repeat (1, 2) 29403094 ++ w) 1)).
  {
    replace ((73, 2) :: (1, 1) :: repeat (1, 2) 152 ++ (806, 2) :: (1, 1) :: repeat (1, 2) 2627 ++ (5503, 2) :: (1, 1) :: repeat (1, 2) 15411 ++ (29238, 2) :: (1, 1) :: repeat (1, 2) 116430 ++ (1483183, 2) :: (1, 1) :: repeat (1, 2) 3474178 ++ (4901382, 2) :: (1, 1) :: repeat (1, 2) 29403094 ++ w) with ((75 - 2, 2) :: (1, 1) :: repeat (1, 2) 152 ++ (806, 2) :: (1, 1) :: repeat (1, 2) 2627 ++ (5503, 2) :: (1, 1) :: repeat (1, 2) 15411 ++ (29238, 2) :: (1, 1) :: repeat (1, 2) 116430 ++ (1483183, 2) :: (1, 1) :: repeat (1, 2) 3474178 ++ (4901382, 2) :: (1, 1) :: repeat (1, 2) 29403094 ++ w) by sec_eq.
    apply (sPUSH [20; 0] 33 75 ((1, 1) :: repeat (1, 2) 152 ++ (806, 2) :: (1, 1) :: repeat (1, 2) 2627 ++ (5503, 2) :: (1, 1) :: repeat (1, 2) 15411 ++ (29238, 2) :: (1, 1) :: repeat (1, 2) 116430 ++ (1483183, 2) :: (1, 1) :: repeat (1, 2) 3474178 ++ (4901382, 2) :: (1, 1) :: repeat (1, 2) 29403094 ++ w) 1); closearith.
  }
  (* step 304: P TDN *)
  apply (hsteps_trans _ (HB [20; 0] 33 1 4 ((73, 2) :: (1, 1) :: repeat (1, 2) 152 ++ (806, 2) :: (1, 1) :: repeat (1, 2) 2627 ++ (5503, 2) :: (1, 1) :: repeat (1, 2) 15411 ++ (29238, 2) :: (1, 1) :: repeat (1, 2) 116430 ++ (1483183, 2) :: (1, 1) :: repeat (1, 2) 3474178 ++ (4901382, 2) :: (1, 1) :: repeat (1, 2) 29403094 ++ w) 1)).
  {
    apply (sTDN [20; 0] 33 ((73, 2) :: (1, 1) :: repeat (1, 2) 152 ++ (806, 2) :: (1, 1) :: repeat (1, 2) 2627 ++ (5503, 2) :: (1, 1) :: repeat (1, 2) 15411 ++ (29238, 2) :: (1, 1) :: repeat (1, 2) 116430 ++ (1483183, 2) :: (1, 1) :: repeat (1, 2) 3474178 ++ (4901382, 2) :: (1, 1) :: repeat (1, 2) 29403094 ++ w) 1).
  }
  (* step 305: sTUP *)
  apply (hsteps_trans _ (HC [20; 0] 33 3 2 ((71, 2) :: (1, 1) :: repeat (1, 2) 152 ++ (806, 2) :: (1, 1) :: repeat (1, 2) 2627 ++ (5503, 2) :: (1, 1) :: repeat (1, 2) 15411 ++ (29238, 2) :: (1, 1) :: repeat (1, 2) 116430 ++ (1483183, 2) :: (1, 1) :: repeat (1, 2) 3474178 ++ (4901382, 2) :: (1, 1) :: repeat (1, 2) 29403094 ++ w) 1)).
  {
    replace ((71, 2) :: (1, 1) :: repeat (1, 2) 152 ++ (806, 2) :: (1, 1) :: repeat (1, 2) 2627 ++ (5503, 2) :: (1, 1) :: repeat (1, 2) 15411 ++ (29238, 2) :: (1, 1) :: repeat (1, 2) 116430 ++ (1483183, 2) :: (1, 1) :: repeat (1, 2) 3474178 ++ (4901382, 2) :: (1, 1) :: repeat (1, 2) 29403094 ++ w) with ((73 - 2, 2) :: (1, 1) :: repeat (1, 2) 152 ++ (806, 2) :: (1, 1) :: repeat (1, 2) 2627 ++ (5503, 2) :: (1, 1) :: repeat (1, 2) 15411 ++ (29238, 2) :: (1, 1) :: repeat (1, 2) 116430 ++ (1483183, 2) :: (1, 1) :: repeat (1, 2) 3474178 ++ (4901382, 2) :: (1, 1) :: repeat (1, 2) 29403094 ++ w) by sec_eq.
    apply (sTUP [20; 0] 33 4 73 2 ((1, 1) :: repeat (1, 2) 152 ++ (806, 2) :: (1, 1) :: repeat (1, 2) 2627 ++ (5503, 2) :: (1, 1) :: repeat (1, 2) 15411 ++ (29238, 2) :: (1, 1) :: repeat (1, 2) 116430 ++ (1483183, 2) :: (1, 1) :: repeat (1, 2) 3474178 ++ (4901382, 2) :: (1, 1) :: repeat (1, 2) 29403094 ++ w) 1); closearith.
  }
  (* step 306: DIPGRIND 33 5 *)
  apply (hsteps_trans _ (HC [20; 0] 0 3 2 (repeat (1, 2) 33 ++ (5, 2) :: (1, 1) :: repeat (1, 2) 152 ++ (806, 2) :: (1, 1) :: repeat (1, 2) 2627 ++ (5503, 2) :: (1, 1) :: repeat (1, 2) 15411 ++ (29238, 2) :: (1, 1) :: repeat (1, 2) 116430 ++ (1483183, 2) :: (1, 1) :: repeat (1, 2) 3474178 ++ (4901382, 2) :: (1, 1) :: repeat (1, 2) 29403094 ++ w) 1)).
  {
    apply (DIPGRIND 33 5 [20; 0] ((1, 1) :: repeat (1, 2) 152 ++ (806, 2) :: (1, 1) :: repeat (1, 2) 2627 ++ (5503, 2) :: (1, 1) :: repeat (1, 2) 15411 ++ (29238, 2) :: (1, 1) :: repeat (1, 2) 116430 ++ (1483183, 2) :: (1, 1) :: repeat (1, 2) 3474178 ++ (4901382, 2) :: (1, 1) :: repeat (1, 2) 29403094 ++ w) 1); closearith.
  }
  (* step 307: P PX2A0 *)
  apply (hsteps_trans _ (HB [0] 3 1 2 ((16, 2) :: (1, 1) :: repeat (1, 2) 35 ++ (5, 2) :: (1, 1) :: repeat (1, 2) 152 ++ (806, 2) :: (1, 1) :: repeat (1, 2) 2627 ++ (5503, 2) :: (1, 1) :: repeat (1, 2) 15411 ++ (29238, 2) :: (1, 1) :: repeat (1, 2) 116430 ++ (1483183, 2) :: (1, 1) :: repeat (1, 2) 3474178 ++ (4901382, 2) :: (1, 1) :: repeat (1, 2) 29403094 ++ w) 1)).
  {
    exact (hsteps_step _ _ _ (hPX2A0 15 (repeat (1, 2) 33 ++ (5, 2) :: (1, 1) :: repeat (1, 2) 152 ++ (806, 2) :: (1, 1) :: repeat (1, 2) 2627 ++ (5503, 2) :: (1, 1) :: repeat (1, 2) 15411 ++ (29238, 2) :: (1, 1) :: repeat (1, 2) 116430 ++ (1483183, 2) :: (1, 1) :: repeat (1, 2) 3474178 ++ (4901382, 2) :: (1, 1) :: repeat (1, 2) 29403094 ++ w) 1) (hsteps_refl _)).
  }
  (* step 308: sTUP *)
  apply (hsteps_trans _ (HC [0] 3 1 2 ((14, 2) :: (1, 1) :: repeat (1, 2) 35 ++ (5, 2) :: (1, 1) :: repeat (1, 2) 152 ++ (806, 2) :: (1, 1) :: repeat (1, 2) 2627 ++ (5503, 2) :: (1, 1) :: repeat (1, 2) 15411 ++ (29238, 2) :: (1, 1) :: repeat (1, 2) 116430 ++ (1483183, 2) :: (1, 1) :: repeat (1, 2) 3474178 ++ (4901382, 2) :: (1, 1) :: repeat (1, 2) 29403094 ++ w) 1)).
  {
    replace ((14, 2) :: (1, 1) :: repeat (1, 2) 35 ++ (5, 2) :: (1, 1) :: repeat (1, 2) 152 ++ (806, 2) :: (1, 1) :: repeat (1, 2) 2627 ++ (5503, 2) :: (1, 1) :: repeat (1, 2) 15411 ++ (29238, 2) :: (1, 1) :: repeat (1, 2) 116430 ++ (1483183, 2) :: (1, 1) :: repeat (1, 2) 3474178 ++ (4901382, 2) :: (1, 1) :: repeat (1, 2) 29403094 ++ w) with ((16 - 2, 2) :: (1, 1) :: repeat (1, 2) 35 ++ (5, 2) :: (1, 1) :: repeat (1, 2) 152 ++ (806, 2) :: (1, 1) :: repeat (1, 2) 2627 ++ (5503, 2) :: (1, 1) :: repeat (1, 2) 15411 ++ (29238, 2) :: (1, 1) :: repeat (1, 2) 116430 ++ (1483183, 2) :: (1, 1) :: repeat (1, 2) 3474178 ++ (4901382, 2) :: (1, 1) :: repeat (1, 2) 29403094 ++ w) by sec_eq.
    apply (sTUP [0] 3 2 16 2 ((1, 1) :: repeat (1, 2) 35 ++ (5, 2) :: (1, 1) :: repeat (1, 2) 152 ++ (806, 2) :: (1, 1) :: repeat (1, 2) 2627 ++ (5503, 2) :: (1, 1) :: repeat (1, 2) 15411 ++ (29238, 2) :: (1, 1) :: repeat (1, 2) 116430 ++ (1483183, 2) :: (1, 1) :: repeat (1, 2) 3474178 ++ (4901382, 2) :: (1, 1) :: repeat (1, 2) 29403094 ++ w) 1); closearith.
  }
  (* step 309: P TDN *)
  apply (hsteps_trans _ (HB [0] 3 1 4 ((14, 2) :: (1, 1) :: repeat (1, 2) 35 ++ (5, 2) :: (1, 1) :: repeat (1, 2) 152 ++ (806, 2) :: (1, 1) :: repeat (1, 2) 2627 ++ (5503, 2) :: (1, 1) :: repeat (1, 2) 15411 ++ (29238, 2) :: (1, 1) :: repeat (1, 2) 116430 ++ (1483183, 2) :: (1, 1) :: repeat (1, 2) 3474178 ++ (4901382, 2) :: (1, 1) :: repeat (1, 2) 29403094 ++ w) 1)).
  {
    apply (sTDN [0] 3 ((14, 2) :: (1, 1) :: repeat (1, 2) 35 ++ (5, 2) :: (1, 1) :: repeat (1, 2) 152 ++ (806, 2) :: (1, 1) :: repeat (1, 2) 2627 ++ (5503, 2) :: (1, 1) :: repeat (1, 2) 15411 ++ (29238, 2) :: (1, 1) :: repeat (1, 2) 116430 ++ (1483183, 2) :: (1, 1) :: repeat (1, 2) 3474178 ++ (4901382, 2) :: (1, 1) :: repeat (1, 2) 29403094 ++ w) 1).
  }
  (* step 310: sTUP *)
  apply (hsteps_trans _ (HC [0] 3 3 2 ((12, 2) :: (1, 1) :: repeat (1, 2) 35 ++ (5, 2) :: (1, 1) :: repeat (1, 2) 152 ++ (806, 2) :: (1, 1) :: repeat (1, 2) 2627 ++ (5503, 2) :: (1, 1) :: repeat (1, 2) 15411 ++ (29238, 2) :: (1, 1) :: repeat (1, 2) 116430 ++ (1483183, 2) :: (1, 1) :: repeat (1, 2) 3474178 ++ (4901382, 2) :: (1, 1) :: repeat (1, 2) 29403094 ++ w) 1)).
  {
    replace ((12, 2) :: (1, 1) :: repeat (1, 2) 35 ++ (5, 2) :: (1, 1) :: repeat (1, 2) 152 ++ (806, 2) :: (1, 1) :: repeat (1, 2) 2627 ++ (5503, 2) :: (1, 1) :: repeat (1, 2) 15411 ++ (29238, 2) :: (1, 1) :: repeat (1, 2) 116430 ++ (1483183, 2) :: (1, 1) :: repeat (1, 2) 3474178 ++ (4901382, 2) :: (1, 1) :: repeat (1, 2) 29403094 ++ w) with ((14 - 2, 2) :: (1, 1) :: repeat (1, 2) 35 ++ (5, 2) :: (1, 1) :: repeat (1, 2) 152 ++ (806, 2) :: (1, 1) :: repeat (1, 2) 2627 ++ (5503, 2) :: (1, 1) :: repeat (1, 2) 15411 ++ (29238, 2) :: (1, 1) :: repeat (1, 2) 116430 ++ (1483183, 2) :: (1, 1) :: repeat (1, 2) 3474178 ++ (4901382, 2) :: (1, 1) :: repeat (1, 2) 29403094 ++ w) by sec_eq.
    apply (sTUP [0] 3 4 14 2 ((1, 1) :: repeat (1, 2) 35 ++ (5, 2) :: (1, 1) :: repeat (1, 2) 152 ++ (806, 2) :: (1, 1) :: repeat (1, 2) 2627 ++ (5503, 2) :: (1, 1) :: repeat (1, 2) 15411 ++ (29238, 2) :: (1, 1) :: repeat (1, 2) 116430 ++ (1483183, 2) :: (1, 1) :: repeat (1, 2) 3474178 ++ (4901382, 2) :: (1, 1) :: repeat (1, 2) 29403094 ++ w) 1); closearith.
  }
  (* step 311: DIPGRIND 3 6 *)
  apply (hsteps_trans _ (HC [0] 0 3 2 (repeat (1, 2) 3 ++ (6, 2) :: (1, 1) :: repeat (1, 2) 35 ++ (5, 2) :: (1, 1) :: repeat (1, 2) 152 ++ (806, 2) :: (1, 1) :: repeat (1, 2) 2627 ++ (5503, 2) :: (1, 1) :: repeat (1, 2) 15411 ++ (29238, 2) :: (1, 1) :: repeat (1, 2) 116430 ++ (1483183, 2) :: (1, 1) :: repeat (1, 2) 3474178 ++ (4901382, 2) :: (1, 1) :: repeat (1, 2) 29403094 ++ w) 1)).
  {
    apply (DIPGRIND 3 6 [0] ((1, 1) :: repeat (1, 2) 35 ++ (5, 2) :: (1, 1) :: repeat (1, 2) 152 ++ (806, 2) :: (1, 1) :: repeat (1, 2) 2627 ++ (5503, 2) :: (1, 1) :: repeat (1, 2) 15411 ++ (29238, 2) :: (1, 1) :: repeat (1, 2) 116430 ++ (1483183, 2) :: (1, 1) :: repeat (1, 2) 3474178 ++ (4901382, 2) :: (1, 1) :: repeat (1, 2) 29403094 ++ w) 1); closearith.
  }
  (* step 312: P PX2B0 *)
  apply (hsteps_trans _ (HB [] 0 1 5 (repeat (1, 2) 4 ++ (6, 2) :: (1, 1) :: repeat (1, 2) 35 ++ (5, 2) :: (1, 1) :: repeat (1, 2) 152 ++ (806, 2) :: (1, 1) :: repeat (1, 2) 2627 ++ (5503, 2) :: (1, 1) :: repeat (1, 2) 15411 ++ (29238, 2) :: (1, 1) :: repeat (1, 2) 116430 ++ (1483183, 2) :: (1, 1) :: repeat (1, 2) 3474178 ++ (4901382, 2) :: (1, 1) :: repeat (1, 2) 29403094 ++ w) 1)).
  {
    exact (hsteps_step _ _ _ (hPX2B0 (repeat (1, 2) 3 ++ (6, 2) :: (1, 1) :: repeat (1, 2) 35 ++ (5, 2) :: (1, 1) :: repeat (1, 2) 152 ++ (806, 2) :: (1, 1) :: repeat (1, 2) 2627 ++ (5503, 2) :: (1, 1) :: repeat (1, 2) 15411 ++ (29238, 2) :: (1, 1) :: repeat (1, 2) 116430 ++ (1483183, 2) :: (1, 1) :: repeat (1, 2) 3474178 ++ (4901382, 2) :: (1, 1) :: repeat (1, 2) 29403094 ++ w) 1) (hsteps_refl _)).
  }
  (* step 313: M pop12 (4,) *)
  apply (hsteps_trans _ (HB [] 4 1 13 ((6, 2) :: (1, 1) :: repeat (1, 2) 35 ++ (5, 2) :: (1, 1) :: repeat (1, 2) 152 ++ (806, 2) :: (1, 1) :: repeat (1, 2) 2627 ++ (5503, 2) :: (1, 1) :: repeat (1, 2) 15411 ++ (29238, 2) :: (1, 1) :: repeat (1, 2) 116430 ++ (1483183, 2) :: (1, 1) :: repeat (1, 2) 3474178 ++ (4901382, 2) :: (1, 1) :: repeat (1, 2) 29403094 ++ w) 1)).
  {
    apply (pop12 4 [] 0 5 ((6, 2) :: (1, 1) :: repeat (1, 2) 35 ++ (5, 2) :: (1, 1) :: repeat (1, 2) 152 ++ (806, 2) :: (1, 1) :: repeat (1, 2) 2627 ++ (5503, 2) :: (1, 1) :: repeat (1, 2) 15411 ++ (29238, 2) :: (1, 1) :: repeat (1, 2) 116430 ++ (1483183, 2) :: (1, 1) :: repeat (1, 2) 3474178 ++ (4901382, 2) :: (1, 1) :: repeat (1, 2) 29403094 ++ w) 1); closearith.
  }
  (* step 314: sTUP *)
  apply (hsteps_trans _ (HC [] 4 12 2 ((4, 2) :: (1, 1) :: repeat (1, 2) 35 ++ (5, 2) :: (1, 1) :: repeat (1, 2) 152 ++ (806, 2) :: (1, 1) :: repeat (1, 2) 2627 ++ (5503, 2) :: (1, 1) :: repeat (1, 2) 15411 ++ (29238, 2) :: (1, 1) :: repeat (1, 2) 116430 ++ (1483183, 2) :: (1, 1) :: repeat (1, 2) 3474178 ++ (4901382, 2) :: (1, 1) :: repeat (1, 2) 29403094 ++ w) 1)).
  {
    replace ((4, 2) :: (1, 1) :: repeat (1, 2) 35 ++ (5, 2) :: (1, 1) :: repeat (1, 2) 152 ++ (806, 2) :: (1, 1) :: repeat (1, 2) 2627 ++ (5503, 2) :: (1, 1) :: repeat (1, 2) 15411 ++ (29238, 2) :: (1, 1) :: repeat (1, 2) 116430 ++ (1483183, 2) :: (1, 1) :: repeat (1, 2) 3474178 ++ (4901382, 2) :: (1, 1) :: repeat (1, 2) 29403094 ++ w) with ((6 - 2, 2) :: (1, 1) :: repeat (1, 2) 35 ++ (5, 2) :: (1, 1) :: repeat (1, 2) 152 ++ (806, 2) :: (1, 1) :: repeat (1, 2) 2627 ++ (5503, 2) :: (1, 1) :: repeat (1, 2) 15411 ++ (29238, 2) :: (1, 1) :: repeat (1, 2) 116430 ++ (1483183, 2) :: (1, 1) :: repeat (1, 2) 3474178 ++ (4901382, 2) :: (1, 1) :: repeat (1, 2) 29403094 ++ w) by sec_eq.
    apply (sTUP [] 4 13 6 2 ((1, 1) :: repeat (1, 2) 35 ++ (5, 2) :: (1, 1) :: repeat (1, 2) 152 ++ (806, 2) :: (1, 1) :: repeat (1, 2) 2627 ++ (5503, 2) :: (1, 1) :: repeat (1, 2) 15411 ++ (29238, 2) :: (1, 1) :: repeat (1, 2) 116430 ++ (1483183, 2) :: (1, 1) :: repeat (1, 2) 3474178 ++ (4901382, 2) :: (1, 1) :: repeat (1, 2) 29403094 ++ w) 1); closearith.
  }
  (* step 315: P PUSH *)
  apply (hsteps_trans _ (HC [] 3 1 2 ((10, 2) :: (4, 2) :: (1, 1) :: repeat (1, 2) 35 ++ (5, 2) :: (1, 1) :: repeat (1, 2) 152 ++ (806, 2) :: (1, 1) :: repeat (1, 2) 2627 ++ (5503, 2) :: (1, 1) :: repeat (1, 2) 15411 ++ (29238, 2) :: (1, 1) :: repeat (1, 2) 116430 ++ (1483183, 2) :: (1, 1) :: repeat (1, 2) 3474178 ++ (4901382, 2) :: (1, 1) :: repeat (1, 2) 29403094 ++ w) 1)).
  {
    replace ((10, 2) :: (4, 2) :: (1, 1) :: repeat (1, 2) 35 ++ (5, 2) :: (1, 1) :: repeat (1, 2) 152 ++ (806, 2) :: (1, 1) :: repeat (1, 2) 2627 ++ (5503, 2) :: (1, 1) :: repeat (1, 2) 15411 ++ (29238, 2) :: (1, 1) :: repeat (1, 2) 116430 ++ (1483183, 2) :: (1, 1) :: repeat (1, 2) 3474178 ++ (4901382, 2) :: (1, 1) :: repeat (1, 2) 29403094 ++ w) with ((12 - 2, 2) :: (4, 2) :: (1, 1) :: repeat (1, 2) 35 ++ (5, 2) :: (1, 1) :: repeat (1, 2) 152 ++ (806, 2) :: (1, 1) :: repeat (1, 2) 2627 ++ (5503, 2) :: (1, 1) :: repeat (1, 2) 15411 ++ (29238, 2) :: (1, 1) :: repeat (1, 2) 116430 ++ (1483183, 2) :: (1, 1) :: repeat (1, 2) 3474178 ++ (4901382, 2) :: (1, 1) :: repeat (1, 2) 29403094 ++ w) by sec_eq.
    apply (sPUSH [] 3 12 ((4, 2) :: (1, 1) :: repeat (1, 2) 35 ++ (5, 2) :: (1, 1) :: repeat (1, 2) 152 ++ (806, 2) :: (1, 1) :: repeat (1, 2) 2627 ++ (5503, 2) :: (1, 1) :: repeat (1, 2) 15411 ++ (29238, 2) :: (1, 1) :: repeat (1, 2) 116430 ++ (1483183, 2) :: (1, 1) :: repeat (1, 2) 3474178 ++ (4901382, 2) :: (1, 1) :: repeat (1, 2) 29403094 ++ w) 1); closearith.
  }
  (* step 316: P TDN *)
  apply (hsteps_trans _ (HB [] 3 1 4 ((10, 2) :: (4, 2) :: (1, 1) :: repeat (1, 2) 35 ++ (5, 2) :: (1, 1) :: repeat (1, 2) 152 ++ (806, 2) :: (1, 1) :: repeat (1, 2) 2627 ++ (5503, 2) :: (1, 1) :: repeat (1, 2) 15411 ++ (29238, 2) :: (1, 1) :: repeat (1, 2) 116430 ++ (1483183, 2) :: (1, 1) :: repeat (1, 2) 3474178 ++ (4901382, 2) :: (1, 1) :: repeat (1, 2) 29403094 ++ w) 1)).
  {
    apply (sTDN [] 3 ((10, 2) :: (4, 2) :: (1, 1) :: repeat (1, 2) 35 ++ (5, 2) :: (1, 1) :: repeat (1, 2) 152 ++ (806, 2) :: (1, 1) :: repeat (1, 2) 2627 ++ (5503, 2) :: (1, 1) :: repeat (1, 2) 15411 ++ (29238, 2) :: (1, 1) :: repeat (1, 2) 116430 ++ (1483183, 2) :: (1, 1) :: repeat (1, 2) 3474178 ++ (4901382, 2) :: (1, 1) :: repeat (1, 2) 29403094 ++ w) 1).
  }
  (* step 317: sTUP *)
  apply (hsteps_trans _ (HC [] 3 3 2 ((8, 2) :: (4, 2) :: (1, 1) :: repeat (1, 2) 35 ++ (5, 2) :: (1, 1) :: repeat (1, 2) 152 ++ (806, 2) :: (1, 1) :: repeat (1, 2) 2627 ++ (5503, 2) :: (1, 1) :: repeat (1, 2) 15411 ++ (29238, 2) :: (1, 1) :: repeat (1, 2) 116430 ++ (1483183, 2) :: (1, 1) :: repeat (1, 2) 3474178 ++ (4901382, 2) :: (1, 1) :: repeat (1, 2) 29403094 ++ w) 1)).
  {
    replace ((8, 2) :: (4, 2) :: (1, 1) :: repeat (1, 2) 35 ++ (5, 2) :: (1, 1) :: repeat (1, 2) 152 ++ (806, 2) :: (1, 1) :: repeat (1, 2) 2627 ++ (5503, 2) :: (1, 1) :: repeat (1, 2) 15411 ++ (29238, 2) :: (1, 1) :: repeat (1, 2) 116430 ++ (1483183, 2) :: (1, 1) :: repeat (1, 2) 3474178 ++ (4901382, 2) :: (1, 1) :: repeat (1, 2) 29403094 ++ w) with ((10 - 2, 2) :: (4, 2) :: (1, 1) :: repeat (1, 2) 35 ++ (5, 2) :: (1, 1) :: repeat (1, 2) 152 ++ (806, 2) :: (1, 1) :: repeat (1, 2) 2627 ++ (5503, 2) :: (1, 1) :: repeat (1, 2) 15411 ++ (29238, 2) :: (1, 1) :: repeat (1, 2) 116430 ++ (1483183, 2) :: (1, 1) :: repeat (1, 2) 3474178 ++ (4901382, 2) :: (1, 1) :: repeat (1, 2) 29403094 ++ w) by sec_eq.
    apply (sTUP [] 3 4 10 2 ((4, 2) :: (1, 1) :: repeat (1, 2) 35 ++ (5, 2) :: (1, 1) :: repeat (1, 2) 152 ++ (806, 2) :: (1, 1) :: repeat (1, 2) 2627 ++ (5503, 2) :: (1, 1) :: repeat (1, 2) 15411 ++ (29238, 2) :: (1, 1) :: repeat (1, 2) 116430 ++ (1483183, 2) :: (1, 1) :: repeat (1, 2) 3474178 ++ (4901382, 2) :: (1, 1) :: repeat (1, 2) 29403094 ++ w) 1); closearith.
  }
  (* step 318: DIPGRIND 3 2 *)
  apply (hsteps_trans _ (HC [] 0 3 2 (repeat (1, 2) 3 ++ (2, 2) :: (4, 2) :: (1, 1) :: repeat (1, 2) 35 ++ (5, 2) :: (1, 1) :: repeat (1, 2) 152 ++ (806, 2) :: (1, 1) :: repeat (1, 2) 2627 ++ (5503, 2) :: (1, 1) :: repeat (1, 2) 15411 ++ (29238, 2) :: (1, 1) :: repeat (1, 2) 116430 ++ (1483183, 2) :: (1, 1) :: repeat (1, 2) 3474178 ++ (4901382, 2) :: (1, 1) :: repeat (1, 2) 29403094 ++ w) 1)).
  {
    apply (DIPGRIND 3 2 [] ((4, 2) :: (1, 1) :: repeat (1, 2) 35 ++ (5, 2) :: (1, 1) :: repeat (1, 2) 152 ++ (806, 2) :: (1, 1) :: repeat (1, 2) 2627 ++ (5503, 2) :: (1, 1) :: repeat (1, 2) 15411 ++ (29238, 2) :: (1, 1) :: repeat (1, 2) 116430 ++ (1483183, 2) :: (1, 1) :: repeat (1, 2) 3474178 ++ (4901382, 2) :: (1, 1) :: repeat (1, 2) 29403094 ++ w) 1); closearith.
  }
  (* step 319: P PUSHX *)
  apply (hsteps_trans _ (HB [] 1 1 7 (repeat (1, 2) 3 ++ (2, 2) :: (4, 2) :: (1, 1) :: repeat (1, 2) 35 ++ (5, 2) :: (1, 1) :: repeat (1, 2) 152 ++ (806, 2) :: (1, 1) :: repeat (1, 2) 2627 ++ (5503, 2) :: (1, 1) :: repeat (1, 2) 15411 ++ (29238, 2) :: (1, 1) :: repeat (1, 2) 116430 ++ (1483183, 2) :: (1, 1) :: repeat (1, 2) 3474178 ++ (4901382, 2) :: (1, 1) :: repeat (1, 2) 29403094 ++ w) 1)).
  {
    exact (hsteps_step _ _ _ (hPUSHX (repeat (1, 2) 3 ++ (2, 2) :: (4, 2) :: (1, 1) :: repeat (1, 2) 35 ++ (5, 2) :: (1, 1) :: repeat (1, 2) 152 ++ (806, 2) :: (1, 1) :: repeat (1, 2) 2627 ++ (5503, 2) :: (1, 1) :: repeat (1, 2) 15411 ++ (29238, 2) :: (1, 1) :: repeat (1, 2) 116430 ++ (1483183, 2) :: (1, 1) :: repeat (1, 2) 3474178 ++ (4901382, 2) :: (1, 1) :: repeat (1, 2) 29403094 ++ w) 1) (hsteps_refl _)).
  }
  (* step 320: M pop12 (3,) *)
  apply (hsteps_trans _ (HB [] 4 1 13 ((2, 2) :: (4, 2) :: (1, 1) :: repeat (1, 2) 35 ++ (5, 2) :: (1, 1) :: repeat (1, 2) 152 ++ (806, 2) :: (1, 1) :: repeat (1, 2) 2627 ++ (5503, 2) :: (1, 1) :: repeat (1, 2) 15411 ++ (29238, 2) :: (1, 1) :: repeat (1, 2) 116430 ++ (1483183, 2) :: (1, 1) :: repeat (1, 2) 3474178 ++ (4901382, 2) :: (1, 1) :: repeat (1, 2) 29403094 ++ w) 1)).
  {
    apply (pop12 3 [] 1 7 ((2, 2) :: (4, 2) :: (1, 1) :: repeat (1, 2) 35 ++ (5, 2) :: (1, 1) :: repeat (1, 2) 152 ++ (806, 2) :: (1, 1) :: repeat (1, 2) 2627 ++ (5503, 2) :: (1, 1) :: repeat (1, 2) 15411 ++ (29238, 2) :: (1, 1) :: repeat (1, 2) 116430 ++ (1483183, 2) :: (1, 1) :: repeat (1, 2) 3474178 ++ (4901382, 2) :: (1, 1) :: repeat (1, 2) 29403094 ++ w) 1); closearith.
  }
  (* step 321: P TUP2_1 *)
  apply (hsteps_trans _ (HC [5] 13 1 2 ((2, 2) :: (1, 1) :: repeat (1, 2) 35 ++ (5, 2) :: (1, 1) :: repeat (1, 2) 152 ++ (806, 2) :: (1, 1) :: repeat (1, 2) 2627 ++ (5503, 2) :: (1, 1) :: repeat (1, 2) 15411 ++ (29238, 2) :: (1, 1) :: repeat (1, 2) 116430 ++ (1483183, 2) :: (1, 1) :: repeat (1, 2) 3474178 ++ (4901382, 2) :: (1, 1) :: repeat (1, 2) 29403094 ++ w) 1)).
  {
    replace ((2, 2) :: (1, 1) :: repeat (1, 2) 35 ++ (5, 2) :: (1, 1) :: repeat (1, 2) 152 ++ (806, 2) :: (1, 1) :: repeat (1, 2) 2627 ++ (5503, 2) :: (1, 1) :: repeat (1, 2) 15411 ++ (29238, 2) :: (1, 1) :: repeat (1, 2) 116430 ++ (1483183, 2) :: (1, 1) :: repeat (1, 2) 3474178 ++ (4901382, 2) :: (1, 1) :: repeat (1, 2) 29403094 ++ w) with ((4 - 2, 2) :: (1, 1) :: repeat (1, 2) 35 ++ (5, 2) :: (1, 1) :: repeat (1, 2) 152 ++ (806, 2) :: (1, 1) :: repeat (1, 2) 2627 ++ (5503, 2) :: (1, 1) :: repeat (1, 2) 15411 ++ (29238, 2) :: (1, 1) :: repeat (1, 2) 116430 ++ (1483183, 2) :: (1, 1) :: repeat (1, 2) 3474178 ++ (4901382, 2) :: (1, 1) :: repeat (1, 2) 29403094 ++ w) by sec_eq.
    apply (sTUP2_1 [] 4 12 4 ((1, 1) :: repeat (1, 2) 35 ++ (5, 2) :: (1, 1) :: repeat (1, 2) 152 ++ (806, 2) :: (1, 1) :: repeat (1, 2) 2627 ++ (5503, 2) :: (1, 1) :: repeat (1, 2) 15411 ++ (29238, 2) :: (1, 1) :: repeat (1, 2) 116430 ++ (1483183, 2) :: (1, 1) :: repeat (1, 2) 3474178 ++ (4901382, 2) :: (1, 1) :: repeat (1, 2) 29403094 ++ w) 1); closearith.
  }
  (* step 322: P TDN *)
  apply (hsteps_trans _ (HB [5] 13 1 4 ((2, 2) :: (1, 1) :: repeat (1, 2) 35 ++ (5, 2) :: (1, 1) :: repeat (1, 2) 152 ++ (806, 2) :: (1, 1) :: repeat (1, 2) 2627 ++ (5503, 2) :: (1, 1) :: repeat (1, 2) 15411 ++ (29238, 2) :: (1, 1) :: repeat (1, 2) 116430 ++ (1483183, 2) :: (1, 1) :: repeat (1, 2) 3474178 ++ (4901382, 2) :: (1, 1) :: repeat (1, 2) 29403094 ++ w) 1)).
  {
    apply (sTDN [5] 13 ((2, 2) :: (1, 1) :: repeat (1, 2) 35 ++ (5, 2) :: (1, 1) :: repeat (1, 2) 152 ++ (806, 2) :: (1, 1) :: repeat (1, 2) 2627 ++ (5503, 2) :: (1, 1) :: repeat (1, 2) 15411 ++ (29238, 2) :: (1, 1) :: repeat (1, 2) 116430 ++ (1483183, 2) :: (1, 1) :: repeat (1, 2) 3474178 ++ (4901382, 2) :: (1, 1) :: repeat (1, 2) 29403094 ++ w) 1).
  }
  (* step 323: P TRANS2_1 *)
  apply (hsteps_trans _ (HB [14; 5] 5 1 3 (repeat (1, 2) 35 ++ (5, 2) :: (1, 1) :: repeat (1, 2) 152 ++ (806, 2) :: (1, 1) :: repeat (1, 2) 2627 ++ (5503, 2) :: (1, 1) :: repeat (1, 2) 15411 ++ (29238, 2) :: (1, 1) :: repeat (1, 2) 116430 ++ (1483183, 2) :: (1, 1) :: repeat (1, 2) 3474178 ++ (4901382, 2) :: (1, 1) :: repeat (1, 2) 29403094 ++ w) 1)).
  {
    apply (sTRANS2_1 [5] 13 3 1 (repeat (1, 2) 35 ++ (5, 2) :: (1, 1) :: repeat (1, 2) 152 ++ (806, 2) :: (1, 1) :: repeat (1, 2) 2627 ++ (5503, 2) :: (1, 1) :: repeat (1, 2) 15411 ++ (29238, 2) :: (1, 1) :: repeat (1, 2) 116430 ++ (1483183, 2) :: (1, 1) :: repeat (1, 2) 3474178 ++ (4901382, 2) :: (1, 1) :: repeat (1, 2) 29403094 ++ w) 1); closearith.
  }
  (* step 324: M pop12 (35,) *)
  apply (hsteps_trans _ (HB [14; 5] 40 1 73 ((5, 2) :: (1, 1) :: repeat (1, 2) 152 ++ (806, 2) :: (1, 1) :: repeat (1, 2) 2627 ++ (5503, 2) :: (1, 1) :: repeat (1, 2) 15411 ++ (29238, 2) :: (1, 1) :: repeat (1, 2) 116430 ++ (1483183, 2) :: (1, 1) :: repeat (1, 2) 3474178 ++ (4901382, 2) :: (1, 1) :: repeat (1, 2) 29403094 ++ w) 1)).
  {
    apply (pop12 35 [14; 5] 5 3 ((5, 2) :: (1, 1) :: repeat (1, 2) 152 ++ (806, 2) :: (1, 1) :: repeat (1, 2) 2627 ++ (5503, 2) :: (1, 1) :: repeat (1, 2) 15411 ++ (29238, 2) :: (1, 1) :: repeat (1, 2) 116430 ++ (1483183, 2) :: (1, 1) :: repeat (1, 2) 3474178 ++ (4901382, 2) :: (1, 1) :: repeat (1, 2) 29403094 ++ w) 1); closearith.
  }
  (* step 325: sTUP *)
  apply (hsteps_trans _ (HC [14; 5] 40 72 2 ((3, 2) :: (1, 1) :: repeat (1, 2) 152 ++ (806, 2) :: (1, 1) :: repeat (1, 2) 2627 ++ (5503, 2) :: (1, 1) :: repeat (1, 2) 15411 ++ (29238, 2) :: (1, 1) :: repeat (1, 2) 116430 ++ (1483183, 2) :: (1, 1) :: repeat (1, 2) 3474178 ++ (4901382, 2) :: (1, 1) :: repeat (1, 2) 29403094 ++ w) 1)).
  {
    replace ((3, 2) :: (1, 1) :: repeat (1, 2) 152 ++ (806, 2) :: (1, 1) :: repeat (1, 2) 2627 ++ (5503, 2) :: (1, 1) :: repeat (1, 2) 15411 ++ (29238, 2) :: (1, 1) :: repeat (1, 2) 116430 ++ (1483183, 2) :: (1, 1) :: repeat (1, 2) 3474178 ++ (4901382, 2) :: (1, 1) :: repeat (1, 2) 29403094 ++ w) with ((5 - 2, 2) :: (1, 1) :: repeat (1, 2) 152 ++ (806, 2) :: (1, 1) :: repeat (1, 2) 2627 ++ (5503, 2) :: (1, 1) :: repeat (1, 2) 15411 ++ (29238, 2) :: (1, 1) :: repeat (1, 2) 116430 ++ (1483183, 2) :: (1, 1) :: repeat (1, 2) 3474178 ++ (4901382, 2) :: (1, 1) :: repeat (1, 2) 29403094 ++ w) by sec_eq.
    apply (sTUP [14; 5] 40 73 5 2 ((1, 1) :: repeat (1, 2) 152 ++ (806, 2) :: (1, 1) :: repeat (1, 2) 2627 ++ (5503, 2) :: (1, 1) :: repeat (1, 2) 15411 ++ (29238, 2) :: (1, 1) :: repeat (1, 2) 116430 ++ (1483183, 2) :: (1, 1) :: repeat (1, 2) 3474178 ++ (4901382, 2) :: (1, 1) :: repeat (1, 2) 29403094 ++ w) 1); closearith.
  }
  (* step 326: hGRIND_even 34 *)
  apply (hsteps_trans _ (HB [14; 5] 39 1 72 ((2, 2) :: (3, 2) :: (1, 1) :: repeat (1, 2) 152 ++ (806, 2) :: (1, 1) :: repeat (1, 2) 2627 ++ (5503, 2) :: (1, 1) :: repeat (1, 2) 15411 ++ (29238, 2) :: (1, 1) :: repeat (1, 2) 116430 ++ (1483183, 2) :: (1, 1) :: repeat (1, 2) 3474178 ++ (4901382, 2) :: (1, 1) :: repeat (1, 2) 29403094 ++ w) 1)).
  {
    apply (hGRIND_even 34 [14; 5] 39 ((3, 2) :: (1, 1) :: repeat (1, 2) 152 ++ (806, 2) :: (1, 1) :: repeat (1, 2) 2627 ++ (5503, 2) :: (1, 1) :: repeat (1, 2) 15411 ++ (29238, 2) :: (1, 1) :: repeat (1, 2) 116430 ++ (1483183, 2) :: (1, 1) :: repeat (1, 2) 3474178 ++ (4901382, 2) :: (1, 1) :: repeat (1, 2) 29403094 ++ w) 1); closearith.
  }
  (* step 327: P TUP2_1 *)
  apply (hsteps_trans _ (HC [40; 14; 5] 72 1 2 (repeat (1, 2) 1 ++ (1, 1) :: repeat (1, 2) 152 ++ (806, 2) :: (1, 1) :: repeat (1, 2) 2627 ++ (5503, 2) :: (1, 1) :: repeat (1, 2) 15411 ++ (29238, 2) :: (1, 1) :: repeat (1, 2) 116430 ++ (1483183, 2) :: (1, 1) :: repeat (1, 2) 3474178 ++ (4901382, 2) :: (1, 1) :: repeat (1, 2) 29403094 ++ w) 1)).
  {
    replace (repeat (1, 2) 1 ++ (1, 1) :: repeat (1, 2) 152 ++ (806, 2) :: (1, 1) :: repeat (1, 2) 2627 ++ (5503, 2) :: (1, 1) :: repeat (1, 2) 15411 ++ (29238, 2) :: (1, 1) :: repeat (1, 2) 116430 ++ (1483183, 2) :: (1, 1) :: repeat (1, 2) 3474178 ++ (4901382, 2) :: (1, 1) :: repeat (1, 2) 29403094 ++ w) with ((3 - 2, 2) :: (1, 1) :: repeat (1, 2) 152 ++ (806, 2) :: (1, 1) :: repeat (1, 2) 2627 ++ (5503, 2) :: (1, 1) :: repeat (1, 2) 15411 ++ (29238, 2) :: (1, 1) :: repeat (1, 2) 116430 ++ (1483183, 2) :: (1, 1) :: repeat (1, 2) 3474178 ++ (4901382, 2) :: (1, 1) :: repeat (1, 2) 29403094 ++ w) by sec_eq.
    apply (sTUP2_1 [14; 5] 39 71 3 ((1, 1) :: repeat (1, 2) 152 ++ (806, 2) :: (1, 1) :: repeat (1, 2) 2627 ++ (5503, 2) :: (1, 1) :: repeat (1, 2) 15411 ++ (29238, 2) :: (1, 1) :: repeat (1, 2) 116430 ++ (1483183, 2) :: (1, 1) :: repeat (1, 2) 3474178 ++ (4901382, 2) :: (1, 1) :: repeat (1, 2) 29403094 ++ w) 1); closearith.
  }
  (* step 328: P TDN *)
  apply (hsteps_trans _ (HB [40; 14; 5] 72 1 4 (repeat (1, 2) 1 ++ (1, 1) :: repeat (1, 2) 152 ++ (806, 2) :: (1, 1) :: repeat (1, 2) 2627 ++ (5503, 2) :: (1, 1) :: repeat (1, 2) 15411 ++ (29238, 2) :: (1, 1) :: repeat (1, 2) 116430 ++ (1483183, 2) :: (1, 1) :: repeat (1, 2) 3474178 ++ (4901382, 2) :: (1, 1) :: repeat (1, 2) 29403094 ++ w) 1)).
  {
    apply (sTDN [40; 14; 5] 72 (repeat (1, 2) 1 ++ (1, 1) :: repeat (1, 2) 152 ++ (806, 2) :: (1, 1) :: repeat (1, 2) 2627 ++ (5503, 2) :: (1, 1) :: repeat (1, 2) 15411 ++ (29238, 2) :: (1, 1) :: repeat (1, 2) 116430 ++ (1483183, 2) :: (1, 1) :: repeat (1, 2) 3474178 ++ (4901382, 2) :: (1, 1) :: repeat (1, 2) 29403094 ++ w) 1).
  }
  (* step 329: M pop12 (1,) *)
  apply (hsteps_trans _ (HB [40; 14; 5] 73 1 6 ((1, 1) :: repeat (1, 2) 152 ++ (806, 2) :: (1, 1) :: repeat (1, 2) 2627 ++ (5503, 2) :: (1, 1) :: repeat (1, 2) 15411 ++ (29238, 2) :: (1, 1) :: repeat (1, 2) 116430 ++ (1483183, 2) :: (1, 1) :: repeat (1, 2) 3474178 ++ (4901382, 2) :: (1, 1) :: repeat (1, 2) 29403094 ++ w) 1)).
  {
    apply (pop12 1 [40; 14; 5] 72 4 ((1, 1) :: repeat (1, 2) 152 ++ (806, 2) :: (1, 1) :: repeat (1, 2) 2627 ++ (5503, 2) :: (1, 1) :: repeat (1, 2) 15411 ++ (29238, 2) :: (1, 1) :: repeat (1, 2) 116430 ++ (1483183, 2) :: (1, 1) :: repeat (1, 2) 3474178 ++ (4901382, 2) :: (1, 1) :: repeat (1, 2) 29403094 ++ w) 1); closearith.
  }
  (* step 330: P POP *)
  apply (hsteps_trans _ (HB [40; 14; 5] 74 1 7 (repeat (1, 2) 152 ++ (806, 2) :: (1, 1) :: repeat (1, 2) 2627 ++ (5503, 2) :: (1, 1) :: repeat (1, 2) 15411 ++ (29238, 2) :: (1, 1) :: repeat (1, 2) 116430 ++ (1483183, 2) :: (1, 1) :: repeat (1, 2) 3474178 ++ (4901382, 2) :: (1, 1) :: repeat (1, 2) 29403094 ++ w) 1)).
  {
    apply (sPOP1 [40; 14; 5] 73 6 (repeat (1, 2) 152 ++ (806, 2) :: (1, 1) :: repeat (1, 2) 2627 ++ (5503, 2) :: (1, 1) :: repeat (1, 2) 15411 ++ (29238, 2) :: (1, 1) :: repeat (1, 2) 116430 ++ (1483183, 2) :: (1, 1) :: repeat (1, 2) 3474178 ++ (4901382, 2) :: (1, 1) :: repeat (1, 2) 29403094 ++ w) 1); closearith.
  }
  (* step 331: M pop12 (152,) *)
  apply (hsteps_trans _ (HB [40; 14; 5] 226 1 311 ((806, 2) :: (1, 1) :: repeat (1, 2) 2627 ++ (5503, 2) :: (1, 1) :: repeat (1, 2) 15411 ++ (29238, 2) :: (1, 1) :: repeat (1, 2) 116430 ++ (1483183, 2) :: (1, 1) :: repeat (1, 2) 3474178 ++ (4901382, 2) :: (1, 1) :: repeat (1, 2) 29403094 ++ w) 1)).
  {
    apply (pop12 152 [40; 14; 5] 74 7 ((806, 2) :: (1, 1) :: repeat (1, 2) 2627 ++ (5503, 2) :: (1, 1) :: repeat (1, 2) 15411 ++ (29238, 2) :: (1, 1) :: repeat (1, 2) 116430 ++ (1483183, 2) :: (1, 1) :: repeat (1, 2) 3474178 ++ (4901382, 2) :: (1, 1) :: repeat (1, 2) 29403094 ++ w) 1); closearith.
  }
  (* step 332: sTUP *)
  apply (hsteps_trans _ (HC [40; 14; 5] 226 310 2 ((804, 2) :: (1, 1) :: repeat (1, 2) 2627 ++ (5503, 2) :: (1, 1) :: repeat (1, 2) 15411 ++ (29238, 2) :: (1, 1) :: repeat (1, 2) 116430 ++ (1483183, 2) :: (1, 1) :: repeat (1, 2) 3474178 ++ (4901382, 2) :: (1, 1) :: repeat (1, 2) 29403094 ++ w) 1)).
  {
    replace ((804, 2) :: (1, 1) :: repeat (1, 2) 2627 ++ (5503, 2) :: (1, 1) :: repeat (1, 2) 15411 ++ (29238, 2) :: (1, 1) :: repeat (1, 2) 116430 ++ (1483183, 2) :: (1, 1) :: repeat (1, 2) 3474178 ++ (4901382, 2) :: (1, 1) :: repeat (1, 2) 29403094 ++ w) with ((806 - 2, 2) :: (1, 1) :: repeat (1, 2) 2627 ++ (5503, 2) :: (1, 1) :: repeat (1, 2) 15411 ++ (29238, 2) :: (1, 1) :: repeat (1, 2) 116430 ++ (1483183, 2) :: (1, 1) :: repeat (1, 2) 3474178 ++ (4901382, 2) :: (1, 1) :: repeat (1, 2) 29403094 ++ w) by sec_eq.
    apply (sTUP [40; 14; 5] 226 311 806 2 ((1, 1) :: repeat (1, 2) 2627 ++ (5503, 2) :: (1, 1) :: repeat (1, 2) 15411 ++ (29238, 2) :: (1, 1) :: repeat (1, 2) 116430 ++ (1483183, 2) :: (1, 1) :: repeat (1, 2) 3474178 ++ (4901382, 2) :: (1, 1) :: repeat (1, 2) 29403094 ++ w) 1); closearith.
  }
  (* step 333: hGRIND_even 153 *)
  apply (hsteps_trans _ (HB [40; 14; 5] 225 1 310 ((2, 2) :: (804, 2) :: (1, 1) :: repeat (1, 2) 2627 ++ (5503, 2) :: (1, 1) :: repeat (1, 2) 15411 ++ (29238, 2) :: (1, 1) :: repeat (1, 2) 116430 ++ (1483183, 2) :: (1, 1) :: repeat (1, 2) 3474178 ++ (4901382, 2) :: (1, 1) :: repeat (1, 2) 29403094 ++ w) 1)).
  {
    apply (hGRIND_even 153 [40; 14; 5] 225 ((804, 2) :: (1, 1) :: repeat (1, 2) 2627 ++ (5503, 2) :: (1, 1) :: repeat (1, 2) 15411 ++ (29238, 2) :: (1, 1) :: repeat (1, 2) 116430 ++ (1483183, 2) :: (1, 1) :: repeat (1, 2) 3474178 ++ (4901382, 2) :: (1, 1) :: repeat (1, 2) 29403094 ++ w) 1); closearith.
  }
  (* step 334: P TUP2_1 *)
  apply (hsteps_trans _ (HC [226; 40; 14; 5] 310 1 2 ((802, 2) :: (1, 1) :: repeat (1, 2) 2627 ++ (5503, 2) :: (1, 1) :: repeat (1, 2) 15411 ++ (29238, 2) :: (1, 1) :: repeat (1, 2) 116430 ++ (1483183, 2) :: (1, 1) :: repeat (1, 2) 3474178 ++ (4901382, 2) :: (1, 1) :: repeat (1, 2) 29403094 ++ w) 1)).
  {
    replace ((802, 2) :: (1, 1) :: repeat (1, 2) 2627 ++ (5503, 2) :: (1, 1) :: repeat (1, 2) 15411 ++ (29238, 2) :: (1, 1) :: repeat (1, 2) 116430 ++ (1483183, 2) :: (1, 1) :: repeat (1, 2) 3474178 ++ (4901382, 2) :: (1, 1) :: repeat (1, 2) 29403094 ++ w) with ((804 - 2, 2) :: (1, 1) :: repeat (1, 2) 2627 ++ (5503, 2) :: (1, 1) :: repeat (1, 2) 15411 ++ (29238, 2) :: (1, 1) :: repeat (1, 2) 116430 ++ (1483183, 2) :: (1, 1) :: repeat (1, 2) 3474178 ++ (4901382, 2) :: (1, 1) :: repeat (1, 2) 29403094 ++ w) by sec_eq.
    apply (sTUP2_1 [40; 14; 5] 225 309 804 ((1, 1) :: repeat (1, 2) 2627 ++ (5503, 2) :: (1, 1) :: repeat (1, 2) 15411 ++ (29238, 2) :: (1, 1) :: repeat (1, 2) 116430 ++ (1483183, 2) :: (1, 1) :: repeat (1, 2) 3474178 ++ (4901382, 2) :: (1, 1) :: repeat (1, 2) 29403094 ++ w) 1); closearith.
  }
  (* step 335: P TDN *)
  apply (hsteps_trans _ (HB [226; 40; 14; 5] 310 1 4 ((802, 2) :: (1, 1) :: repeat (1, 2) 2627 ++ (5503, 2) :: (1, 1) :: repeat (1, 2) 15411 ++ (29238, 2) :: (1, 1) :: repeat (1, 2) 116430 ++ (1483183, 2) :: (1, 1) :: repeat (1, 2) 3474178 ++ (4901382, 2) :: (1, 1) :: repeat (1, 2) 29403094 ++ w) 1)).
  {
    apply (sTDN [226; 40; 14; 5] 310 ((802, 2) :: (1, 1) :: repeat (1, 2) 2627 ++ (5503, 2) :: (1, 1) :: repeat (1, 2) 15411 ++ (29238, 2) :: (1, 1) :: repeat (1, 2) 116430 ++ (1483183, 2) :: (1, 1) :: repeat (1, 2) 3474178 ++ (4901382, 2) :: (1, 1) :: repeat (1, 2) 29403094 ++ w) 1).
  }
  (* step 336: sTUP *)
  apply (hsteps_trans _ (HC [226; 40; 14; 5] 310 3 2 ((800, 2) :: (1, 1) :: repeat (1, 2) 2627 ++ (5503, 2) :: (1, 1) :: repeat (1, 2) 15411 ++ (29238, 2) :: (1, 1) :: repeat (1, 2) 116430 ++ (1483183, 2) :: (1, 1) :: repeat (1, 2) 3474178 ++ (4901382, 2) :: (1, 1) :: repeat (1, 2) 29403094 ++ w) 1)).
  {
    replace ((800, 2) :: (1, 1) :: repeat (1, 2) 2627 ++ (5503, 2) :: (1, 1) :: repeat (1, 2) 15411 ++ (29238, 2) :: (1, 1) :: repeat (1, 2) 116430 ++ (1483183, 2) :: (1, 1) :: repeat (1, 2) 3474178 ++ (4901382, 2) :: (1, 1) :: repeat (1, 2) 29403094 ++ w) with ((802 - 2, 2) :: (1, 1) :: repeat (1, 2) 2627 ++ (5503, 2) :: (1, 1) :: repeat (1, 2) 15411 ++ (29238, 2) :: (1, 1) :: repeat (1, 2) 116430 ++ (1483183, 2) :: (1, 1) :: repeat (1, 2) 3474178 ++ (4901382, 2) :: (1, 1) :: repeat (1, 2) 29403094 ++ w) by sec_eq.
    apply (sTUP [226; 40; 14; 5] 310 4 802 2 ((1, 1) :: repeat (1, 2) 2627 ++ (5503, 2) :: (1, 1) :: repeat (1, 2) 15411 ++ (29238, 2) :: (1, 1) :: repeat (1, 2) 116430 ++ (1483183, 2) :: (1, 1) :: repeat (1, 2) 3474178 ++ (4901382, 2) :: (1, 1) :: repeat (1, 2) 29403094 ++ w) 1); closearith.
  }
  (* step 337: DIPGRIND 310 180 *)
  apply (hsteps_trans _ (HC [226; 40; 14; 5] 0 3 2 (repeat (1, 2) 310 ++ (180, 2) :: (1, 1) :: repeat (1, 2) 2627 ++ (5503, 2) :: (1, 1) :: repeat (1, 2) 15411 ++ (29238, 2) :: (1, 1) :: repeat (1, 2) 116430 ++ (1483183, 2) :: (1, 1) :: repeat (1, 2) 3474178 ++ (4901382, 2) :: (1, 1) :: repeat (1, 2) 29403094 ++ w) 1)).
  {
    apply (DIPGRIND 310 180 [226; 40; 14; 5] ((1, 1) :: repeat (1, 2) 2627 ++ (5503, 2) :: (1, 1) :: repeat (1, 2) 15411 ++ (29238, 2) :: (1, 1) :: repeat (1, 2) 116430 ++ (1483183, 2) :: (1, 1) :: repeat (1, 2) 3474178 ++ (4901382, 2) :: (1, 1) :: repeat (1, 2) 29403094 ++ w) 1); closearith.
  }
  (* step 338: P PX2A *)
  apply (hsteps_trans _ (HC [14; 5] 39 224 2 ((1, 1) :: repeat (1, 2) 312 ++ (180, 2) :: (1, 1) :: repeat (1, 2) 2627 ++ (5503, 2) :: (1, 1) :: repeat (1, 2) 15411 ++ (29238, 2) :: (1, 1) :: repeat (1, 2) 116430 ++ (1483183, 2) :: (1, 1) :: repeat (1, 2) 3474178 ++ (4901382, 2) :: (1, 1) :: repeat (1, 2) 29403094 ++ w) 1)).
  {
    exact (hsteps_step _ _ _ (hPX2A 223 39 [14; 5] (repeat (1, 2) 310 ++ (180, 2) :: (1, 1) :: repeat (1, 2) 2627 ++ (5503, 2) :: (1, 1) :: repeat (1, 2) 15411 ++ (29238, 2) :: (1, 1) :: repeat (1, 2) 116430 ++ (1483183, 2) :: (1, 1) :: repeat (1, 2) 3474178 ++ (4901382, 2) :: (1, 1) :: repeat (1, 2) 29403094 ++ w) 1) (hsteps_refl _)).
  }
  (* step 339: P PUSH *)
  apply (hsteps_trans _ (HC [14; 5] 38 1 2 ((222, 2) :: (1, 1) :: repeat (1, 2) 312 ++ (180, 2) :: (1, 1) :: repeat (1, 2) 2627 ++ (5503, 2) :: (1, 1) :: repeat (1, 2) 15411 ++ (29238, 2) :: (1, 1) :: repeat (1, 2) 116430 ++ (1483183, 2) :: (1, 1) :: repeat (1, 2) 3474178 ++ (4901382, 2) :: (1, 1) :: repeat (1, 2) 29403094 ++ w) 1)).
  {
    replace ((222, 2) :: (1, 1) :: repeat (1, 2) 312 ++ (180, 2) :: (1, 1) :: repeat (1, 2) 2627 ++ (5503, 2) :: (1, 1) :: repeat (1, 2) 15411 ++ (29238, 2) :: (1, 1) :: repeat (1, 2) 116430 ++ (1483183, 2) :: (1, 1) :: repeat (1, 2) 3474178 ++ (4901382, 2) :: (1, 1) :: repeat (1, 2) 29403094 ++ w) with ((224 - 2, 2) :: (1, 1) :: repeat (1, 2) 312 ++ (180, 2) :: (1, 1) :: repeat (1, 2) 2627 ++ (5503, 2) :: (1, 1) :: repeat (1, 2) 15411 ++ (29238, 2) :: (1, 1) :: repeat (1, 2) 116430 ++ (1483183, 2) :: (1, 1) :: repeat (1, 2) 3474178 ++ (4901382, 2) :: (1, 1) :: repeat (1, 2) 29403094 ++ w) by sec_eq.
    apply (sPUSH [14; 5] 38 224 ((1, 1) :: repeat (1, 2) 312 ++ (180, 2) :: (1, 1) :: repeat (1, 2) 2627 ++ (5503, 2) :: (1, 1) :: repeat (1, 2) 15411 ++ (29238, 2) :: (1, 1) :: repeat (1, 2) 116430 ++ (1483183, 2) :: (1, 1) :: repeat (1, 2) 3474178 ++ (4901382, 2) :: (1, 1) :: repeat (1, 2) 29403094 ++ w) 1); closearith.
  }
  (* step 340: P TDN *)
  apply (hsteps_trans _ (HB [14; 5] 38 1 4 ((222, 2) :: (1, 1) :: repeat (1, 2) 312 ++ (180, 2) :: (1, 1) :: repeat (1, 2) 2627 ++ (5503, 2) :: (1, 1) :: repeat (1, 2) 15411 ++ (29238, 2) :: (1, 1) :: repeat (1, 2) 116430 ++ (1483183, 2) :: (1, 1) :: repeat (1, 2) 3474178 ++ (4901382, 2) :: (1, 1) :: repeat (1, 2) 29403094 ++ w) 1)).
  {
    apply (sTDN [14; 5] 38 ((222, 2) :: (1, 1) :: repeat (1, 2) 312 ++ (180, 2) :: (1, 1) :: repeat (1, 2) 2627 ++ (5503, 2) :: (1, 1) :: repeat (1, 2) 15411 ++ (29238, 2) :: (1, 1) :: repeat (1, 2) 116430 ++ (1483183, 2) :: (1, 1) :: repeat (1, 2) 3474178 ++ (4901382, 2) :: (1, 1) :: repeat (1, 2) 29403094 ++ w) 1).
  }
  (* step 341: sTUP *)
  apply (hsteps_trans _ (HC [14; 5] 38 3 2 ((220, 2) :: (1, 1) :: repeat (1, 2) 312 ++ (180, 2) :: (1, 1) :: repeat (1, 2) 2627 ++ (5503, 2) :: (1, 1) :: repeat (1, 2) 15411 ++ (29238, 2) :: (1, 1) :: repeat (1, 2) 116430 ++ (1483183, 2) :: (1, 1) :: repeat (1, 2) 3474178 ++ (4901382, 2) :: (1, 1) :: repeat (1, 2) 29403094 ++ w) 1)).
  {
    replace ((220, 2) :: (1, 1) :: repeat (1, 2) 312 ++ (180, 2) :: (1, 1) :: repeat (1, 2) 2627 ++ (5503, 2) :: (1, 1) :: repeat (1, 2) 15411 ++ (29238, 2) :: (1, 1) :: repeat (1, 2) 116430 ++ (1483183, 2) :: (1, 1) :: repeat (1, 2) 3474178 ++ (4901382, 2) :: (1, 1) :: repeat (1, 2) 29403094 ++ w) with ((222 - 2, 2) :: (1, 1) :: repeat (1, 2) 312 ++ (180, 2) :: (1, 1) :: repeat (1, 2) 2627 ++ (5503, 2) :: (1, 1) :: repeat (1, 2) 15411 ++ (29238, 2) :: (1, 1) :: repeat (1, 2) 116430 ++ (1483183, 2) :: (1, 1) :: repeat (1, 2) 3474178 ++ (4901382, 2) :: (1, 1) :: repeat (1, 2) 29403094 ++ w) by sec_eq.
    apply (sTUP [14; 5] 38 4 222 2 ((1, 1) :: repeat (1, 2) 312 ++ (180, 2) :: (1, 1) :: repeat (1, 2) 2627 ++ (5503, 2) :: (1, 1) :: repeat (1, 2) 15411 ++ (29238, 2) :: (1, 1) :: repeat (1, 2) 116430 ++ (1483183, 2) :: (1, 1) :: repeat (1, 2) 3474178 ++ (4901382, 2) :: (1, 1) :: repeat (1, 2) 29403094 ++ w) 1); closearith.
  }
  (* step 342: DIPGRIND 38 144 *)
  apply (hsteps_trans _ (HC [14; 5] 0 3 2 (repeat (1, 2) 38 ++ (144, 2) :: (1, 1) :: repeat (1, 2) 312 ++ (180, 2) :: (1, 1) :: repeat (1, 2) 2627 ++ (5503, 2) :: (1, 1) :: repeat (1, 2) 15411 ++ (29238, 2) :: (1, 1) :: repeat (1, 2) 116430 ++ (1483183, 2) :: (1, 1) :: repeat (1, 2) 3474178 ++ (4901382, 2) :: (1, 1) :: repeat (1, 2) 29403094 ++ w) 1)).
  {
    apply (DIPGRIND 38 144 [14; 5] ((1, 1) :: repeat (1, 2) 312 ++ (180, 2) :: (1, 1) :: repeat (1, 2) 2627 ++ (5503, 2) :: (1, 1) :: repeat (1, 2) 15411 ++ (29238, 2) :: (1, 1) :: repeat (1, 2) 116430 ++ (1483183, 2) :: (1, 1) :: repeat (1, 2) 3474178 ++ (4901382, 2) :: (1, 1) :: repeat (1, 2) 29403094 ++ w) 1); closearith.
  }
  (* step 343: P PX2A *)
  apply (hsteps_trans _ (HC [] 4 12 2 ((1, 1) :: repeat (1, 2) 40 ++ (144, 2) :: (1, 1) :: repeat (1, 2) 312 ++ (180, 2) :: (1, 1) :: repeat (1, 2) 2627 ++ (5503, 2) :: (1, 1) :: repeat (1, 2) 15411 ++ (29238, 2) :: (1, 1) :: repeat (1, 2) 116430 ++ (1483183, 2) :: (1, 1) :: repeat (1, 2) 3474178 ++ (4901382, 2) :: (1, 1) :: repeat (1, 2) 29403094 ++ w) 1)).
  {
    exact (hsteps_step _ _ _ (hPX2A 11 4 [] (repeat (1, 2) 38 ++ (144, 2) :: (1, 1) :: repeat (1, 2) 312 ++ (180, 2) :: (1, 1) :: repeat (1, 2) 2627 ++ (5503, 2) :: (1, 1) :: repeat (1, 2) 15411 ++ (29238, 2) :: (1, 1) :: repeat (1, 2) 116430 ++ (1483183, 2) :: (1, 1) :: repeat (1, 2) 3474178 ++ (4901382, 2) :: (1, 1) :: repeat (1, 2) 29403094 ++ w) 1) (hsteps_refl _)).
  }
  (* step 344: P PUSH *)
  apply (hsteps_trans _ (HC [] 3 1 2 ((10, 2) :: (1, 1) :: repeat (1, 2) 40 ++ (144, 2) :: (1, 1) :: repeat (1, 2) 312 ++ (180, 2) :: (1, 1) :: repeat (1, 2) 2627 ++ (5503, 2) :: (1, 1) :: repeat (1, 2) 15411 ++ (29238, 2) :: (1, 1) :: repeat (1, 2) 116430 ++ (1483183, 2) :: (1, 1) :: repeat (1, 2) 3474178 ++ (4901382, 2) :: (1, 1) :: repeat (1, 2) 29403094 ++ w) 1)).
  {
    replace ((10, 2) :: (1, 1) :: repeat (1, 2) 40 ++ (144, 2) :: (1, 1) :: repeat (1, 2) 312 ++ (180, 2) :: (1, 1) :: repeat (1, 2) 2627 ++ (5503, 2) :: (1, 1) :: repeat (1, 2) 15411 ++ (29238, 2) :: (1, 1) :: repeat (1, 2) 116430 ++ (1483183, 2) :: (1, 1) :: repeat (1, 2) 3474178 ++ (4901382, 2) :: (1, 1) :: repeat (1, 2) 29403094 ++ w) with ((12 - 2, 2) :: (1, 1) :: repeat (1, 2) 40 ++ (144, 2) :: (1, 1) :: repeat (1, 2) 312 ++ (180, 2) :: (1, 1) :: repeat (1, 2) 2627 ++ (5503, 2) :: (1, 1) :: repeat (1, 2) 15411 ++ (29238, 2) :: (1, 1) :: repeat (1, 2) 116430 ++ (1483183, 2) :: (1, 1) :: repeat (1, 2) 3474178 ++ (4901382, 2) :: (1, 1) :: repeat (1, 2) 29403094 ++ w) by sec_eq.
    apply (sPUSH [] 3 12 ((1, 1) :: repeat (1, 2) 40 ++ (144, 2) :: (1, 1) :: repeat (1, 2) 312 ++ (180, 2) :: (1, 1) :: repeat (1, 2) 2627 ++ (5503, 2) :: (1, 1) :: repeat (1, 2) 15411 ++ (29238, 2) :: (1, 1) :: repeat (1, 2) 116430 ++ (1483183, 2) :: (1, 1) :: repeat (1, 2) 3474178 ++ (4901382, 2) :: (1, 1) :: repeat (1, 2) 29403094 ++ w) 1); closearith.
  }
  (* step 345: P TDN *)
  apply (sTDN [] 3 ((10, 2) :: (1, 1) :: repeat (1, 2) 40 ++ (144, 2) :: (1, 1) :: repeat (1, 2) 312 ++ (180, 2) :: (1, 1) :: repeat (1, 2) 2627 ++ (5503, 2) :: (1, 1) :: repeat (1, 2) 15411 ++ (29238, 2) :: (1, 1) :: repeat (1, 2) 116430 ++ (1483183, 2) :: (1, 1) :: repeat (1, 2) 3474178 ++ (4901382, 2) :: (1, 1) :: repeat (1, 2) 29403094 ++ w) 1).
Qed.

(* CASCADE59i: steps 346-383 of the CASCADE59 chain. *)
Lemma CASCADE59i : forall w,
  hsteps (HB [] 3 1 4 ((10, 2) :: (1, 1) :: repeat (1, 2) 40 ++ (144, 2) :: (1, 1) :: repeat (1, 2) 312 ++ (180, 2) :: (1, 1) :: repeat (1, 2) 2627 ++ (5503, 2) :: (1, 1) :: repeat (1, 2) 15411 ++ (29238, 2) :: (1, 1) :: repeat (1, 2) 116430 ++ (1483183, 2) :: (1, 1) :: repeat (1, 2) 3474178 ++ (4901382, 2) :: (1, 1) :: repeat (1, 2) 29403094 ++ w) 1)
         (HB [36327; 20669; 2806; 627; 455; 83; 54; 5] 29237 1 3 (repeat (1, 2) 116430 ++ (1483183, 2) :: (1, 1) :: repeat (1, 2) 3474178 ++ (4901382, 2) :: (1, 1) :: repeat (1, 2) 29403094 ++ w) 1).
Proof.
  intro w.
  (* step 346: sTUP *)
  apply (hsteps_trans _ (HC [] 3 3 2 ((8, 2) :: (1, 1) :: repeat (1, 2) 40 ++ (144, 2) :: (1, 1) :: repeat (1, 2) 312 ++ (180, 2) :: (1, 1) :: repeat (1, 2) 2627 ++ (5503, 2) :: (1, 1) :: repeat (1, 2) 15411 ++ (29238, 2) :: (1, 1) :: repeat (1, 2) 116430 ++ (1483183, 2) :: (1, 1) :: repeat (1, 2) 3474178 ++ (4901382, 2) :: (1, 1) :: repeat (1, 2) 29403094 ++ w) 1)).
  {
    replace ((8, 2) :: (1, 1) :: repeat (1, 2) 40 ++ (144, 2) :: (1, 1) :: repeat (1, 2) 312 ++ (180, 2) :: (1, 1) :: repeat (1, 2) 2627 ++ (5503, 2) :: (1, 1) :: repeat (1, 2) 15411 ++ (29238, 2) :: (1, 1) :: repeat (1, 2) 116430 ++ (1483183, 2) :: (1, 1) :: repeat (1, 2) 3474178 ++ (4901382, 2) :: (1, 1) :: repeat (1, 2) 29403094 ++ w) with ((10 - 2, 2) :: (1, 1) :: repeat (1, 2) 40 ++ (144, 2) :: (1, 1) :: repeat (1, 2) 312 ++ (180, 2) :: (1, 1) :: repeat (1, 2) 2627 ++ (5503, 2) :: (1, 1) :: repeat (1, 2) 15411 ++ (29238, 2) :: (1, 1) :: repeat (1, 2) 116430 ++ (1483183, 2) :: (1, 1) :: repeat (1, 2) 3474178 ++ (4901382, 2) :: (1, 1) :: repeat (1, 2) 29403094 ++ w) by sec_eq.
    apply (sTUP [] 3 4 10 2 ((1, 1) :: repeat (1, 2) 40 ++ (144, 2) :: (1, 1) :: repeat (1, 2) 312 ++ (180, 2) :: (1, 1) :: repeat (1, 2) 2627 ++ (5503, 2) :: (1, 1) :: repeat (1, 2) 15411 ++ (29238, 2) :: (1, 1) :: repeat (1, 2) 116430 ++ (1483183, 2) :: (1, 1) :: repeat (1, 2) 3474178 ++ (4901382, 2) :: (1, 1) :: repeat (1, 2) 29403094 ++ w) 1); closearith.
  }
  (* step 347: DIPGRIND 3 2 *)
  apply (hsteps_trans _ (HC [] 0 3 2 (repeat (1, 2) 3 ++ (2, 2) :: (1, 1) :: repeat (1, 2) 40 ++ (144, 2) :: (1, 1) :: repeat (1, 2) 312 ++ (180, 2) :: (1, 1) :: repeat (1, 2) 2627 ++ (5503, 2) :: (1, 1) :: repeat (1, 2) 15411 ++ (29238, 2) :: (1, 1) :: repeat (1, 2) 116430 ++ (1483183, 2) :: (1, 1) :: repeat (1, 2) 3474178 ++ (4901382, 2) :: (1, 1) :: repeat (1, 2) 29403094 ++ w) 1)).
  {
    apply (DIPGRIND 3 2 [] ((1, 1) :: repeat (1, 2) 40 ++ (144, 2) :: (1, 1) :: repeat (1, 2) 312 ++ (180, 2) :: (1, 1) :: repeat (1, 2) 2627 ++ (5503, 2) :: (1, 1) :: repeat (1, 2) 15411 ++ (29238, 2) :: (1, 1) :: repeat (1, 2) 116430 ++ (1483183, 2) :: (1, 1) :: repeat (1, 2) 3474178 ++ (4901382, 2) :: (1, 1) :: repeat (1, 2) 29403094 ++ w) 1); closearith.
  }
  (* step 348: P PUSHX *)
  apply (hsteps_trans _ (HB [] 1 1 7 (repeat (1, 2) 3 ++ (2, 2) :: (1, 1) :: repeat (1, 2) 40 ++ (144, 2) :: (1, 1) :: repeat (1, 2) 312 ++ (180, 2) :: (1, 1) :: repeat (1, 2) 2627 ++ (5503, 2) :: (1, 1) :: repeat (1, 2) 15411 ++ (29238, 2) :: (1, 1) :: repeat (1, 2) 116430 ++ (1483183, 2) :: (1, 1) :: repeat (1, 2) 3474178 ++ (4901382, 2) :: (1, 1) :: repeat (1, 2) 29403094 ++ w) 1)).
  {
    exact (hsteps_step _ _ _ (hPUSHX (repeat (1, 2) 3 ++ (2, 2) :: (1, 1) :: repeat (1, 2) 40 ++ (144, 2) :: (1, 1) :: repeat (1, 2) 312 ++ (180, 2) :: (1, 1) :: repeat (1, 2) 2627 ++ (5503, 2) :: (1, 1) :: repeat (1, 2) 15411 ++ (29238, 2) :: (1, 1) :: repeat (1, 2) 116430 ++ (1483183, 2) :: (1, 1) :: repeat (1, 2) 3474178 ++ (4901382, 2) :: (1, 1) :: repeat (1, 2) 29403094 ++ w) 1) (hsteps_refl _)).
  }
  (* step 349: M pop12 (3,) *)
  apply (hsteps_trans _ (HB [] 4 1 13 ((2, 2) :: (1, 1) :: repeat (1, 2) 40 ++ (144, 2) :: (1, 1) :: repeat (1, 2) 312 ++ (180, 2) :: (1, 1) :: repeat (1, 2) 2627 ++ (5503, 2) :: (1, 1) :: repeat (1, 2) 15411 ++ (29238, 2) :: (1, 1) :: repeat (1, 2) 116430 ++ (1483183, 2) :: (1, 1) :: repeat (1, 2) 3474178 ++ (4901382, 2) :: (1, 1) :: repeat (1, 2) 29403094 ++ w) 1)).
  {
    apply (pop12 3 [] 1 7 ((2, 2) :: (1, 1) :: repeat (1, 2) 40 ++ (144, 2) :: (1, 1) :: repeat (1, 2) 312 ++ (180, 2) :: (1, 1) :: repeat (1, 2) 2627 ++ (5503, 2) :: (1, 1) :: repeat (1, 2) 15411 ++ (29238, 2) :: (1, 1) :: repeat (1, 2) 116430 ++ (1483183, 2) :: (1, 1) :: repeat (1, 2) 3474178 ++ (4901382, 2) :: (1, 1) :: repeat (1, 2) 29403094 ++ w) 1); closearith.
  }
  (* step 350: P TRANS2_1 *)
  apply (hsteps_trans _ (HB [5] 14 1 3 (repeat (1, 2) 40 ++ (144, 2) :: (1, 1) :: repeat (1, 2) 312 ++ (180, 2) :: (1, 1) :: repeat (1, 2) 2627 ++ (5503, 2) :: (1, 1) :: repeat (1, 2) 15411 ++ (29238, 2) :: (1, 1) :: repeat (1, 2) 116430 ++ (1483183, 2) :: (1, 1) :: repeat (1, 2) 3474178 ++ (4901382, 2) :: (1, 1) :: repeat (1, 2) 29403094 ++ w) 1)).
  {
    apply (sTRANS2_1 [] 4 12 1 (repeat (1, 2) 40 ++ (144, 2) :: (1, 1) :: repeat (1, 2) 312 ++ (180, 2) :: (1, 1) :: repeat (1, 2) 2627 ++ (5503, 2) :: (1, 1) :: repeat (1, 2) 15411 ++ (29238, 2) :: (1, 1) :: repeat (1, 2) 116430 ++ (1483183, 2) :: (1, 1) :: repeat (1, 2) 3474178 ++ (4901382, 2) :: (1, 1) :: repeat (1, 2) 29403094 ++ w) 1); closearith.
  }
  (* step 351: M pop12 (40,) *)
  apply (hsteps_trans _ (HB [5] 54 1 83 ((144, 2) :: (1, 1) :: repeat (1, 2) 312 ++ (180, 2) :: (1, 1) :: repeat (1, 2) 2627 ++ (5503, 2) :: (1, 1) :: repeat (1, 2) 15411 ++ (29238, 2) :: (1, 1) :: repeat (1, 2) 116430 ++ (1483183, 2) :: (1, 1) :: repeat (1, 2) 3474178 ++ (4901382, 2) :: (1, 1) :: repeat (1, 2) 29403094 ++ w) 1)).
  {
    apply (pop12 40 [5] 14 3 ((144, 2) :: (1, 1) :: repeat (1, 2) 312 ++ (180, 2) :: (1, 1) :: repeat (1, 2) 2627 ++ (5503, 2) :: (1, 1) :: repeat (1, 2) 15411 ++ (29238, 2) :: (1, 1) :: repeat (1, 2) 116430 ++ (1483183, 2) :: (1, 1) :: repeat (1, 2) 3474178 ++ (4901382, 2) :: (1, 1) :: repeat (1, 2) 29403094 ++ w) 1); closearith.
  }
  (* step 352: sTUP *)
  apply (hsteps_trans _ (HC [5] 54 82 2 ((142, 2) :: (1, 1) :: repeat (1, 2) 312 ++ (180, 2) :: (1, 1) :: repeat (1, 2) 2627 ++ (5503, 2) :: (1, 1) :: repeat (1, 2) 15411 ++ (29238, 2) :: (1, 1) :: repeat (1, 2) 116430 ++ (1483183, 2) :: (1, 1) :: repeat (1, 2) 3474178 ++ (4901382, 2) :: (1, 1) :: repeat (1, 2) 29403094 ++ w) 1)).
  {
    replace ((142, 2) :: (1, 1) :: repeat (1, 2) 312 ++ (180, 2) :: (1, 1) :: repeat (1, 2) 2627 ++ (5503, 2) :: (1, 1) :: repeat (1, 2) 15411 ++ (29238, 2) :: (1, 1) :: repeat (1, 2) 116430 ++ (1483183, 2) :: (1, 1) :: repeat (1, 2) 3474178 ++ (4901382, 2) :: (1, 1) :: repeat (1, 2) 29403094 ++ w) with ((144 - 2, 2) :: (1, 1) :: repeat (1, 2) 312 ++ (180, 2) :: (1, 1) :: repeat (1, 2) 2627 ++ (5503, 2) :: (1, 1) :: repeat (1, 2) 15411 ++ (29238, 2) :: (1, 1) :: repeat (1, 2) 116430 ++ (1483183, 2) :: (1, 1) :: repeat (1, 2) 3474178 ++ (4901382, 2) :: (1, 1) :: repeat (1, 2) 29403094 ++ w) by sec_eq.
    apply (sTUP [5] 54 83 144 2 ((1, 1) :: repeat (1, 2) 312 ++ (180, 2) :: (1, 1) :: repeat (1, 2) 2627 ++ (5503, 2) :: (1, 1) :: repeat (1, 2) 15411 ++ (29238, 2) :: (1, 1) :: repeat (1, 2) 116430 ++ (1483183, 2) :: (1, 1) :: repeat (1, 2) 3474178 ++ (4901382, 2) :: (1, 1) :: repeat (1, 2) 29403094 ++ w) 1); closearith.
  }
  (* step 353: hGRIND_even 39 *)
  apply (hsteps_trans _ (HB [5] 53 1 82 ((2, 2) :: (142, 2) :: (1, 1) :: repeat (1, 2) 312 ++ (180, 2) :: (1, 1) :: repeat (1, 2) 2627 ++ (5503, 2) :: (1, 1) :: repeat (1, 2) 15411 ++ (29238, 2) :: (1, 1) :: repeat (1, 2) 116430 ++ (1483183, 2) :: (1, 1) :: repeat (1, 2) 3474178 ++ (4901382, 2) :: (1, 1) :: repeat (1, 2) 29403094 ++ w) 1)).
  {
    apply (hGRIND_even 39 [5] 53 ((142, 2) :: (1, 1) :: repeat (1, 2) 312 ++ (180, 2) :: (1, 1) :: repeat (1, 2) 2627 ++ (5503, 2) :: (1, 1) :: repeat (1, 2) 15411 ++ (29238, 2) :: (1, 1) :: repeat (1, 2) 116430 ++ (1483183, 2) :: (1, 1) :: repeat (1, 2) 3474178 ++ (4901382, 2) :: (1, 1) :: repeat (1, 2) 29403094 ++ w) 1); closearith.
  }
  (* step 354: P TUP2_1 *)
  apply (hsteps_trans _ (HC [54; 5] 82 1 2 ((140, 2) :: (1, 1) :: repeat (1, 2) 312 ++ (180, 2) :: (1, 1) :: repeat (1, 2) 2627 ++ (5503, 2) :: (1, 1) :: repeat (1, 2) 15411 ++ (29238, 2) :: (1, 1) :: repeat (1, 2) 116430 ++ (1483183, 2) :: (1, 1) :: repeat (1, 2) 3474178 ++ (4901382, 2) :: (1, 1) :: repeat (1, 2) 29403094 ++ w) 1)).
  {
    replace ((140, 2) :: (1, 1) :: repeat (1, 2) 312 ++ (180, 2) :: (1, 1) :: repeat (1, 2) 2627 ++ (5503, 2) :: (1, 1) :: repeat (1, 2) 15411 ++ (29238, 2) :: (1, 1) :: repeat (1, 2) 116430 ++ (1483183, 2) :: (1, 1) :: repeat (1, 2) 3474178 ++ (4901382, 2) :: (1, 1) :: repeat (1, 2) 29403094 ++ w) with ((142 - 2, 2) :: (1, 1) :: repeat (1, 2) 312 ++ (180, 2) :: (1, 1) :: repeat (1, 2) 2627 ++ (5503, 2) :: (1, 1) :: repeat (1, 2) 15411 ++ (29238, 2) :: (1, 1) :: repeat (1, 2) 116430 ++ (1483183, 2) :: (1, 1) :: repeat (1, 2) 3474178 ++ (4901382, 2) :: (1, 1) :: repeat (1, 2) 29403094 ++ w) by sec_eq.
    apply (sTUP2_1 [5] 53 81 142 ((1, 1) :: repeat (1, 2) 312 ++ (180, 2) :: (1, 1) :: repeat (1, 2) 2627 ++ (5503, 2) :: (1, 1) :: repeat (1, 2) 15411 ++ (29238, 2) :: (1, 1) :: repeat (1, 2) 116430 ++ (1483183, 2) :: (1, 1) :: repeat (1, 2) 3474178 ++ (4901382, 2) :: (1, 1) :: repeat (1, 2) 29403094 ++ w) 1); closearith.
  }
  (* step 355: P TDN *)
  apply (hsteps_trans _ (HB [54; 5] 82 1 4 ((140, 2) :: (1, 1) :: repeat (1, 2) 312 ++ (180, 2) :: (1, 1) :: repeat (1, 2) 2627 ++ (5503, 2) :: (1, 1) :: repeat (1, 2) 15411 ++ (29238, 2) :: (1, 1) :: repeat (1, 2) 116430 ++ (1483183, 2) :: (1, 1) :: repeat (1, 2) 3474178 ++ (4901382, 2) :: (1, 1) :: repeat (1, 2) 29403094 ++ w) 1)).
  {
    apply (sTDN [54; 5] 82 ((140, 2) :: (1, 1) :: repeat (1, 2) 312 ++ (180, 2) :: (1, 1) :: repeat (1, 2) 2627 ++ (5503, 2) :: (1, 1) :: repeat (1, 2) 15411 ++ (29238, 2) :: (1, 1) :: repeat (1, 2) 116430 ++ (1483183, 2) :: (1, 1) :: repeat (1, 2) 3474178 ++ (4901382, 2) :: (1, 1) :: repeat (1, 2) 29403094 ++ w) 1).
  }
  (* step 356: sTUP *)
  apply (hsteps_trans _ (HC [54; 5] 82 3 2 ((138, 2) :: (1, 1) :: repeat (1, 2) 312 ++ (180, 2) :: (1, 1) :: repeat (1, 2) 2627 ++ (5503, 2) :: (1, 1) :: repeat (1, 2) 15411 ++ (29238, 2) :: (1, 1) :: repeat (1, 2) 116430 ++ (1483183, 2) :: (1, 1) :: repeat (1, 2) 3474178 ++ (4901382, 2) :: (1, 1) :: repeat (1, 2) 29403094 ++ w) 1)).
  {
    replace ((138, 2) :: (1, 1) :: repeat (1, 2) 312 ++ (180, 2) :: (1, 1) :: repeat (1, 2) 2627 ++ (5503, 2) :: (1, 1) :: repeat (1, 2) 15411 ++ (29238, 2) :: (1, 1) :: repeat (1, 2) 116430 ++ (1483183, 2) :: (1, 1) :: repeat (1, 2) 3474178 ++ (4901382, 2) :: (1, 1) :: repeat (1, 2) 29403094 ++ w) with ((140 - 2, 2) :: (1, 1) :: repeat (1, 2) 312 ++ (180, 2) :: (1, 1) :: repeat (1, 2) 2627 ++ (5503, 2) :: (1, 1) :: repeat (1, 2) 15411 ++ (29238, 2) :: (1, 1) :: repeat (1, 2) 116430 ++ (1483183, 2) :: (1, 1) :: repeat (1, 2) 3474178 ++ (4901382, 2) :: (1, 1) :: repeat (1, 2) 29403094 ++ w) by sec_eq.
    apply (sTUP [54; 5] 82 4 140 2 ((1, 1) :: repeat (1, 2) 312 ++ (180, 2) :: (1, 1) :: repeat (1, 2) 2627 ++ (5503, 2) :: (1, 1) :: repeat (1, 2) 15411 ++ (29238, 2) :: (1, 1) :: repeat (1, 2) 116430 ++ (1483183, 2) :: (1, 1) :: repeat (1, 2) 3474178 ++ (4901382, 2) :: (1, 1) :: repeat (1, 2) 29403094 ++ w) 1); closearith.
  }
  (* step 357: CLEANG_even 68 *)
  apply (hsteps_trans _ (HB [54; 5] 82 1 142 ((2, 2) :: (1, 1) :: repeat (1, 2) 312 ++ (180, 2) :: (1, 1) :: repeat (1, 2) 2627 ++ (5503, 2) :: (1, 1) :: repeat (1, 2) 15411 ++ (29238, 2) :: (1, 1) :: repeat (1, 2) 116430 ++ (1483183, 2) :: (1, 1) :: repeat (1, 2) 3474178 ++ (4901382, 2) :: (1, 1) :: repeat (1, 2) 29403094 ++ w) 1)).
  {
    apply (CLEANG_even 68 [54; 5] 82 ((1, 1) :: repeat (1, 2) 312 ++ (180, 2) :: (1, 1) :: repeat (1, 2) 2627 ++ (5503, 2) :: (1, 1) :: repeat (1, 2) 15411 ++ (29238, 2) :: (1, 1) :: repeat (1, 2) 116430 ++ (1483183, 2) :: (1, 1) :: repeat (1, 2) 3474178 ++ (4901382, 2) :: (1, 1) :: repeat (1, 2) 29403094 ++ w) 1); closearith.
  }
  (* step 358: P TRANS2_1 *)
  apply (hsteps_trans _ (HB [83; 54; 5] 143 1 3 (repeat (1, 2) 312 ++ (180, 2) :: (1, 1) :: repeat (1, 2) 2627 ++ (5503, 2) :: (1, 1) :: repeat (1, 2) 15411 ++ (29238, 2) :: (1, 1) :: repeat (1, 2) 116430 ++ (1483183, 2) :: (1, 1) :: repeat (1, 2) 3474178 ++ (4901382, 2) :: (1, 1) :: repeat (1, 2) 29403094 ++ w) 1)).
  {
    apply (sTRANS2_1 [54; 5] 82 141 1 (repeat (1, 2) 312 ++ (180, 2) :: (1, 1) :: repeat (1, 2) 2627 ++ (5503, 2) :: (1, 1) :: repeat (1, 2) 15411 ++ (29238, 2) :: (1, 1) :: repeat (1, 2) 116430 ++ (1483183, 2) :: (1, 1) :: repeat (1, 2) 3474178 ++ (4901382, 2) :: (1, 1) :: repeat (1, 2) 29403094 ++ w) 1); closearith.
  }
  (* step 359: M pop12 (312,) *)
  apply (hsteps_trans _ (HB [83; 54; 5] 455 1 627 ((180, 2) :: (1, 1) :: repeat (1, 2) 2627 ++ (5503, 2) :: (1, 1) :: repeat (1, 2) 15411 ++ (29238, 2) :: (1, 1) :: repeat (1, 2) 116430 ++ (1483183, 2) :: (1, 1) :: repeat (1, 2) 3474178 ++ (4901382, 2) :: (1, 1) :: repeat (1, 2) 29403094 ++ w) 1)).
  {
    apply (pop12 312 [83; 54; 5] 143 3 ((180, 2) :: (1, 1) :: repeat (1, 2) 2627 ++ (5503, 2) :: (1, 1) :: repeat (1, 2) 15411 ++ (29238, 2) :: (1, 1) :: repeat (1, 2) 116430 ++ (1483183, 2) :: (1, 1) :: repeat (1, 2) 3474178 ++ (4901382, 2) :: (1, 1) :: repeat (1, 2) 29403094 ++ w) 1); closearith.
  }
  (* step 360: sTUP *)
  apply (hsteps_trans _ (HC [83; 54; 5] 455 626 2 ((178, 2) :: (1, 1) :: repeat (1, 2) 2627 ++ (5503, 2) :: (1, 1) :: repeat (1, 2) 15411 ++ (29238, 2) :: (1, 1) :: repeat (1, 2) 116430 ++ (1483183, 2) :: (1, 1) :: repeat (1, 2) 3474178 ++ (4901382, 2) :: (1, 1) :: repeat (1, 2) 29403094 ++ w) 1)).
  {
    replace ((178, 2) :: (1, 1) :: repeat (1, 2) 2627 ++ (5503, 2) :: (1, 1) :: repeat (1, 2) 15411 ++ (29238, 2) :: (1, 1) :: repeat (1, 2) 116430 ++ (1483183, 2) :: (1, 1) :: repeat (1, 2) 3474178 ++ (4901382, 2) :: (1, 1) :: repeat (1, 2) 29403094 ++ w) with ((180 - 2, 2) :: (1, 1) :: repeat (1, 2) 2627 ++ (5503, 2) :: (1, 1) :: repeat (1, 2) 15411 ++ (29238, 2) :: (1, 1) :: repeat (1, 2) 116430 ++ (1483183, 2) :: (1, 1) :: repeat (1, 2) 3474178 ++ (4901382, 2) :: (1, 1) :: repeat (1, 2) 29403094 ++ w) by sec_eq.
    apply (sTUP [83; 54; 5] 455 627 180 2 ((1, 1) :: repeat (1, 2) 2627 ++ (5503, 2) :: (1, 1) :: repeat (1, 2) 15411 ++ (29238, 2) :: (1, 1) :: repeat (1, 2) 116430 ++ (1483183, 2) :: (1, 1) :: repeat (1, 2) 3474178 ++ (4901382, 2) :: (1, 1) :: repeat (1, 2) 29403094 ++ w) 1); closearith.
  }
  (* step 361: hGRIND_even 311 *)
  apply (hsteps_trans _ (HB [83; 54; 5] 454 1 626 ((2, 2) :: (178, 2) :: (1, 1) :: repeat (1, 2) 2627 ++ (5503, 2) :: (1, 1) :: repeat (1, 2) 15411 ++ (29238, 2) :: (1, 1) :: repeat (1, 2) 116430 ++ (1483183, 2) :: (1, 1) :: repeat (1, 2) 3474178 ++ (4901382, 2) :: (1, 1) :: repeat (1, 2) 29403094 ++ w) 1)).
  {
    apply (hGRIND_even 311 [83; 54; 5] 454 ((178, 2) :: (1, 1) :: repeat (1, 2) 2627 ++ (5503, 2) :: (1, 1) :: repeat (1, 2) 15411 ++ (29238, 2) :: (1, 1) :: repeat (1, 2) 116430 ++ (1483183, 2) :: (1, 1) :: repeat (1, 2) 3474178 ++ (4901382, 2) :: (1, 1) :: repeat (1, 2) 29403094 ++ w) 1); closearith.
  }
  (* step 362: P TUP2_1 *)
  apply (hsteps_trans _ (HC [455; 83; 54; 5] 626 1 2 ((176, 2) :: (1, 1) :: repeat (1, 2) 2627 ++ (5503, 2) :: (1, 1) :: repeat (1, 2) 15411 ++ (29238, 2) :: (1, 1) :: repeat (1, 2) 116430 ++ (1483183, 2) :: (1, 1) :: repeat (1, 2) 3474178 ++ (4901382, 2) :: (1, 1) :: repeat (1, 2) 29403094 ++ w) 1)).
  {
    replace ((176, 2) :: (1, 1) :: repeat (1, 2) 2627 ++ (5503, 2) :: (1, 1) :: repeat (1, 2) 15411 ++ (29238, 2) :: (1, 1) :: repeat (1, 2) 116430 ++ (1483183, 2) :: (1, 1) :: repeat (1, 2) 3474178 ++ (4901382, 2) :: (1, 1) :: repeat (1, 2) 29403094 ++ w) with ((178 - 2, 2) :: (1, 1) :: repeat (1, 2) 2627 ++ (5503, 2) :: (1, 1) :: repeat (1, 2) 15411 ++ (29238, 2) :: (1, 1) :: repeat (1, 2) 116430 ++ (1483183, 2) :: (1, 1) :: repeat (1, 2) 3474178 ++ (4901382, 2) :: (1, 1) :: repeat (1, 2) 29403094 ++ w) by sec_eq.
    apply (sTUP2_1 [83; 54; 5] 454 625 178 ((1, 1) :: repeat (1, 2) 2627 ++ (5503, 2) :: (1, 1) :: repeat (1, 2) 15411 ++ (29238, 2) :: (1, 1) :: repeat (1, 2) 116430 ++ (1483183, 2) :: (1, 1) :: repeat (1, 2) 3474178 ++ (4901382, 2) :: (1, 1) :: repeat (1, 2) 29403094 ++ w) 1); closearith.
  }
  (* step 363: P TDN *)
  apply (hsteps_trans _ (HB [455; 83; 54; 5] 626 1 4 ((176, 2) :: (1, 1) :: repeat (1, 2) 2627 ++ (5503, 2) :: (1, 1) :: repeat (1, 2) 15411 ++ (29238, 2) :: (1, 1) :: repeat (1, 2) 116430 ++ (1483183, 2) :: (1, 1) :: repeat (1, 2) 3474178 ++ (4901382, 2) :: (1, 1) :: repeat (1, 2) 29403094 ++ w) 1)).
  {
    apply (sTDN [455; 83; 54; 5] 626 ((176, 2) :: (1, 1) :: repeat (1, 2) 2627 ++ (5503, 2) :: (1, 1) :: repeat (1, 2) 15411 ++ (29238, 2) :: (1, 1) :: repeat (1, 2) 116430 ++ (1483183, 2) :: (1, 1) :: repeat (1, 2) 3474178 ++ (4901382, 2) :: (1, 1) :: repeat (1, 2) 29403094 ++ w) 1).
  }
  (* step 364: sTUP *)
  apply (hsteps_trans _ (HC [455; 83; 54; 5] 626 3 2 ((174, 2) :: (1, 1) :: repeat (1, 2) 2627 ++ (5503, 2) :: (1, 1) :: repeat (1, 2) 15411 ++ (29238, 2) :: (1, 1) :: repeat (1, 2) 116430 ++ (1483183, 2) :: (1, 1) :: repeat (1, 2) 3474178 ++ (4901382, 2) :: (1, 1) :: repeat (1, 2) 29403094 ++ w) 1)).
  {
    replace ((174, 2) :: (1, 1) :: repeat (1, 2) 2627 ++ (5503, 2) :: (1, 1) :: repeat (1, 2) 15411 ++ (29238, 2) :: (1, 1) :: repeat (1, 2) 116430 ++ (1483183, 2) :: (1, 1) :: repeat (1, 2) 3474178 ++ (4901382, 2) :: (1, 1) :: repeat (1, 2) 29403094 ++ w) with ((176 - 2, 2) :: (1, 1) :: repeat (1, 2) 2627 ++ (5503, 2) :: (1, 1) :: repeat (1, 2) 15411 ++ (29238, 2) :: (1, 1) :: repeat (1, 2) 116430 ++ (1483183, 2) :: (1, 1) :: repeat (1, 2) 3474178 ++ (4901382, 2) :: (1, 1) :: repeat (1, 2) 29403094 ++ w) by sec_eq.
    apply (sTUP [455; 83; 54; 5] 626 4 176 2 ((1, 1) :: repeat (1, 2) 2627 ++ (5503, 2) :: (1, 1) :: repeat (1, 2) 15411 ++ (29238, 2) :: (1, 1) :: repeat (1, 2) 116430 ++ (1483183, 2) :: (1, 1) :: repeat (1, 2) 3474178 ++ (4901382, 2) :: (1, 1) :: repeat (1, 2) 29403094 ++ w) 1); closearith.
  }
  (* step 365: CLEANG_even 86 *)
  apply (hsteps_trans _ (HB [455; 83; 54; 5] 626 1 178 ((2, 2) :: (1, 1) :: repeat (1, 2) 2627 ++ (5503, 2) :: (1, 1) :: repeat (1, 2) 15411 ++ (29238, 2) :: (1, 1) :: repeat (1, 2) 116430 ++ (1483183, 2) :: (1, 1) :: repeat (1, 2) 3474178 ++ (4901382, 2) :: (1, 1) :: repeat (1, 2) 29403094 ++ w) 1)).
  {
    apply (CLEANG_even 86 [455; 83; 54; 5] 626 ((1, 1) :: repeat (1, 2) 2627 ++ (5503, 2) :: (1, 1) :: repeat (1, 2) 15411 ++ (29238, 2) :: (1, 1) :: repeat (1, 2) 116430 ++ (1483183, 2) :: (1, 1) :: repeat (1, 2) 3474178 ++ (4901382, 2) :: (1, 1) :: repeat (1, 2) 29403094 ++ w) 1); closearith.
  }
  (* step 366: P TRANS2_1 *)
  apply (hsteps_trans _ (HB [627; 455; 83; 54; 5] 179 1 3 (repeat (1, 2) 2627 ++ (5503, 2) :: (1, 1) :: repeat (1, 2) 15411 ++ (29238, 2) :: (1, 1) :: repeat (1, 2) 116430 ++ (1483183, 2) :: (1, 1) :: repeat (1, 2) 3474178 ++ (4901382, 2) :: (1, 1) :: repeat (1, 2) 29403094 ++ w) 1)).
  {
    apply (sTRANS2_1 [455; 83; 54; 5] 626 177 1 (repeat (1, 2) 2627 ++ (5503, 2) :: (1, 1) :: repeat (1, 2) 15411 ++ (29238, 2) :: (1, 1) :: repeat (1, 2) 116430 ++ (1483183, 2) :: (1, 1) :: repeat (1, 2) 3474178 ++ (4901382, 2) :: (1, 1) :: repeat (1, 2) 29403094 ++ w) 1); closearith.
  }
  (* step 367: M pop12 (2627,) *)
  apply (hsteps_trans _ (HB [627; 455; 83; 54; 5] 2806 1 5257 ((5503, 2) :: (1, 1) :: repeat (1, 2) 15411 ++ (29238, 2) :: (1, 1) :: repeat (1, 2) 116430 ++ (1483183, 2) :: (1, 1) :: repeat (1, 2) 3474178 ++ (4901382, 2) :: (1, 1) :: repeat (1, 2) 29403094 ++ w) 1)).
  {
    apply (pop12 2627 [627; 455; 83; 54; 5] 179 3 ((5503, 2) :: (1, 1) :: repeat (1, 2) 15411 ++ (29238, 2) :: (1, 1) :: repeat (1, 2) 116430 ++ (1483183, 2) :: (1, 1) :: repeat (1, 2) 3474178 ++ (4901382, 2) :: (1, 1) :: repeat (1, 2) 29403094 ++ w) 1); closearith.
  }
  (* step 368: sTUP *)
  apply (hsteps_trans _ (HC [627; 455; 83; 54; 5] 2806 5256 2 ((5501, 2) :: (1, 1) :: repeat (1, 2) 15411 ++ (29238, 2) :: (1, 1) :: repeat (1, 2) 116430 ++ (1483183, 2) :: (1, 1) :: repeat (1, 2) 3474178 ++ (4901382, 2) :: (1, 1) :: repeat (1, 2) 29403094 ++ w) 1)).
  {
    replace ((5501, 2) :: (1, 1) :: repeat (1, 2) 15411 ++ (29238, 2) :: (1, 1) :: repeat (1, 2) 116430 ++ (1483183, 2) :: (1, 1) :: repeat (1, 2) 3474178 ++ (4901382, 2) :: (1, 1) :: repeat (1, 2) 29403094 ++ w) with ((5503 - 2, 2) :: (1, 1) :: repeat (1, 2) 15411 ++ (29238, 2) :: (1, 1) :: repeat (1, 2) 116430 ++ (1483183, 2) :: (1, 1) :: repeat (1, 2) 3474178 ++ (4901382, 2) :: (1, 1) :: repeat (1, 2) 29403094 ++ w) by sec_eq.
    apply (sTUP [627; 455; 83; 54; 5] 2806 5257 5503 2 ((1, 1) :: repeat (1, 2) 15411 ++ (29238, 2) :: (1, 1) :: repeat (1, 2) 116430 ++ (1483183, 2) :: (1, 1) :: repeat (1, 2) 3474178 ++ (4901382, 2) :: (1, 1) :: repeat (1, 2) 29403094 ++ w) 1); closearith.
  }
  (* step 369: hGRIND_even 2626 *)
  apply (hsteps_trans _ (HB [627; 455; 83; 54; 5] 2805 1 5256 ((2, 2) :: (5501, 2) :: (1, 1) :: repeat (1, 2) 15411 ++ (29238, 2) :: (1, 1) :: repeat (1, 2) 116430 ++ (1483183, 2) :: (1, 1) :: repeat (1, 2) 3474178 ++ (4901382, 2) :: (1, 1) :: repeat (1, 2) 29403094 ++ w) 1)).
  {
    apply (hGRIND_even 2626 [627; 455; 83; 54; 5] 2805 ((5501, 2) :: (1, 1) :: repeat (1, 2) 15411 ++ (29238, 2) :: (1, 1) :: repeat (1, 2) 116430 ++ (1483183, 2) :: (1, 1) :: repeat (1, 2) 3474178 ++ (4901382, 2) :: (1, 1) :: repeat (1, 2) 29403094 ++ w) 1); closearith.
  }
  (* step 370: P TUP2_1 *)
  apply (hsteps_trans _ (HC [2806; 627; 455; 83; 54; 5] 5256 1 2 ((5499, 2) :: (1, 1) :: repeat (1, 2) 15411 ++ (29238, 2) :: (1, 1) :: repeat (1, 2) 116430 ++ (1483183, 2) :: (1, 1) :: repeat (1, 2) 3474178 ++ (4901382, 2) :: (1, 1) :: repeat (1, 2) 29403094 ++ w) 1)).
  {
    replace ((5499, 2) :: (1, 1) :: repeat (1, 2) 15411 ++ (29238, 2) :: (1, 1) :: repeat (1, 2) 116430 ++ (1483183, 2) :: (1, 1) :: repeat (1, 2) 3474178 ++ (4901382, 2) :: (1, 1) :: repeat (1, 2) 29403094 ++ w) with ((5501 - 2, 2) :: (1, 1) :: repeat (1, 2) 15411 ++ (29238, 2) :: (1, 1) :: repeat (1, 2) 116430 ++ (1483183, 2) :: (1, 1) :: repeat (1, 2) 3474178 ++ (4901382, 2) :: (1, 1) :: repeat (1, 2) 29403094 ++ w) by sec_eq.
    apply (sTUP2_1 [627; 455; 83; 54; 5] 2805 5255 5501 ((1, 1) :: repeat (1, 2) 15411 ++ (29238, 2) :: (1, 1) :: repeat (1, 2) 116430 ++ (1483183, 2) :: (1, 1) :: repeat (1, 2) 3474178 ++ (4901382, 2) :: (1, 1) :: repeat (1, 2) 29403094 ++ w) 1); closearith.
  }
  (* step 371: P TDN *)
  apply (hsteps_trans _ (HB [2806; 627; 455; 83; 54; 5] 5256 1 4 ((5499, 2) :: (1, 1) :: repeat (1, 2) 15411 ++ (29238, 2) :: (1, 1) :: repeat (1, 2) 116430 ++ (1483183, 2) :: (1, 1) :: repeat (1, 2) 3474178 ++ (4901382, 2) :: (1, 1) :: repeat (1, 2) 29403094 ++ w) 1)).
  {
    apply (sTDN [2806; 627; 455; 83; 54; 5] 5256 ((5499, 2) :: (1, 1) :: repeat (1, 2) 15411 ++ (29238, 2) :: (1, 1) :: repeat (1, 2) 116430 ++ (1483183, 2) :: (1, 1) :: repeat (1, 2) 3474178 ++ (4901382, 2) :: (1, 1) :: repeat (1, 2) 29403094 ++ w) 1).
  }
  (* step 372: sTUP *)
  apply (hsteps_trans _ (HC [2806; 627; 455; 83; 54; 5] 5256 3 2 ((5497, 2) :: (1, 1) :: repeat (1, 2) 15411 ++ (29238, 2) :: (1, 1) :: repeat (1, 2) 116430 ++ (1483183, 2) :: (1, 1) :: repeat (1, 2) 3474178 ++ (4901382, 2) :: (1, 1) :: repeat (1, 2) 29403094 ++ w) 1)).
  {
    replace ((5497, 2) :: (1, 1) :: repeat (1, 2) 15411 ++ (29238, 2) :: (1, 1) :: repeat (1, 2) 116430 ++ (1483183, 2) :: (1, 1) :: repeat (1, 2) 3474178 ++ (4901382, 2) :: (1, 1) :: repeat (1, 2) 29403094 ++ w) with ((5499 - 2, 2) :: (1, 1) :: repeat (1, 2) 15411 ++ (29238, 2) :: (1, 1) :: repeat (1, 2) 116430 ++ (1483183, 2) :: (1, 1) :: repeat (1, 2) 3474178 ++ (4901382, 2) :: (1, 1) :: repeat (1, 2) 29403094 ++ w) by sec_eq.
    apply (sTUP [2806; 627; 455; 83; 54; 5] 5256 4 5499 2 ((1, 1) :: repeat (1, 2) 15411 ++ (29238, 2) :: (1, 1) :: repeat (1, 2) 116430 ++ (1483183, 2) :: (1, 1) :: repeat (1, 2) 3474178 ++ (4901382, 2) :: (1, 1) :: repeat (1, 2) 29403094 ++ w) 1); closearith.
  }
  (* step 373: CLEANG_odd 2747 *)
  apply (hsteps_trans _ (HB [2806; 627; 455; 83; 54; 5] 5256 1 5502 (repeat (1, 2) 1 ++ (1, 1) :: repeat (1, 2) 15411 ++ (29238, 2) :: (1, 1) :: repeat (1, 2) 116430 ++ (1483183, 2) :: (1, 1) :: repeat (1, 2) 3474178 ++ (4901382, 2) :: (1, 1) :: repeat (1, 2) 29403094 ++ w) 1)).
  {
    replace (repeat (1, 2) 1 ++ (1, 1) :: repeat (1, 2) 15411 ++ (29238, 2) :: (1, 1) :: repeat (1, 2) 116430 ++ (1483183, 2) :: (1, 1) :: repeat (1, 2) 3474178 ++ (4901382, 2) :: (1, 1) :: repeat (1, 2) 29403094 ++ w) with ((1, 2) :: (1, 1) :: repeat (1, 2) 15411 ++ (29238, 2) :: (1, 1) :: repeat (1, 2) 116430 ++ (1483183, 2) :: (1, 1) :: repeat (1, 2) 3474178 ++ (4901382, 2) :: (1, 1) :: repeat (1, 2) 29403094 ++ w) by sec_eq.
    apply (CLEANG_odd 2747 [2806; 627; 455; 83; 54; 5] 5256 ((1, 1) :: repeat (1, 2) 15411 ++ (29238, 2) :: (1, 1) :: repeat (1, 2) 116430 ++ (1483183, 2) :: (1, 1) :: repeat (1, 2) 3474178 ++ (4901382, 2) :: (1, 1) :: repeat (1, 2) 29403094 ++ w) 1); closearith.
  }
  (* step 374: M pop12 (1,) *)
  apply (hsteps_trans _ (HB [2806; 627; 455; 83; 54; 5] 5257 1 5504 ((1, 1) :: repeat (1, 2) 15411 ++ (29238, 2) :: (1, 1) :: repeat (1, 2) 116430 ++ (1483183, 2) :: (1, 1) :: repeat (1, 2) 3474178 ++ (4901382, 2) :: (1, 1) :: repeat (1, 2) 29403094 ++ w) 1)).
  {
    apply (pop12 1 [2806; 627; 455; 83; 54; 5] 5256 5502 ((1, 1) :: repeat (1, 2) 15411 ++ (29238, 2) :: (1, 1) :: repeat (1, 2) 116430 ++ (1483183, 2) :: (1, 1) :: repeat (1, 2) 3474178 ++ (4901382, 2) :: (1, 1) :: repeat (1, 2) 29403094 ++ w) 1); closearith.
  }
  (* step 375: P POP *)
  apply (hsteps_trans _ (HB [2806; 627; 455; 83; 54; 5] 5258 1 5505 (repeat (1, 2) 15411 ++ (29238, 2) :: (1, 1) :: repeat (1, 2) 116430 ++ (1483183, 2) :: (1, 1) :: repeat (1, 2) 3474178 ++ (4901382, 2) :: (1, 1) :: repeat (1, 2) 29403094 ++ w) 1)).
  {
    apply (sPOP1 [2806; 627; 455; 83; 54; 5] 5257 5504 (repeat (1, 2) 15411 ++ (29238, 2) :: (1, 1) :: repeat (1, 2) 116430 ++ (1483183, 2) :: (1, 1) :: repeat (1, 2) 3474178 ++ (4901382, 2) :: (1, 1) :: repeat (1, 2) 29403094 ++ w) 1); closearith.
  }
  (* step 376: M pop12 (15411,) *)
  apply (hsteps_trans _ (HB [2806; 627; 455; 83; 54; 5] 20669 1 36327 ((29238, 2) :: (1, 1) :: repeat (1, 2) 116430 ++ (1483183, 2) :: (1, 1) :: repeat (1, 2) 3474178 ++ (4901382, 2) :: (1, 1) :: repeat (1, 2) 29403094 ++ w) 1)).
  {
    apply (pop12 15411 [2806; 627; 455; 83; 54; 5] 5258 5505 ((29238, 2) :: (1, 1) :: repeat (1, 2) 116430 ++ (1483183, 2) :: (1, 1) :: repeat (1, 2) 3474178 ++ (4901382, 2) :: (1, 1) :: repeat (1, 2) 29403094 ++ w) 1); closearith.
  }
  (* step 377: sTUP *)
  apply (hsteps_trans _ (HC [2806; 627; 455; 83; 54; 5] 20669 36326 2 ((29236, 2) :: (1, 1) :: repeat (1, 2) 116430 ++ (1483183, 2) :: (1, 1) :: repeat (1, 2) 3474178 ++ (4901382, 2) :: (1, 1) :: repeat (1, 2) 29403094 ++ w) 1)).
  {
    replace ((29236, 2) :: (1, 1) :: repeat (1, 2) 116430 ++ (1483183, 2) :: (1, 1) :: repeat (1, 2) 3474178 ++ (4901382, 2) :: (1, 1) :: repeat (1, 2) 29403094 ++ w) with ((29238 - 2, 2) :: (1, 1) :: repeat (1, 2) 116430 ++ (1483183, 2) :: (1, 1) :: repeat (1, 2) 3474178 ++ (4901382, 2) :: (1, 1) :: repeat (1, 2) 29403094 ++ w) by sec_eq.
    apply (sTUP [2806; 627; 455; 83; 54; 5] 20669 36327 29238 2 ((1, 1) :: repeat (1, 2) 116430 ++ (1483183, 2) :: (1, 1) :: repeat (1, 2) 3474178 ++ (4901382, 2) :: (1, 1) :: repeat (1, 2) 29403094 ++ w) 1); closearith.
  }
  (* step 378: hGRIND_even 18161 *)
  apply (hsteps_trans _ (HB [2806; 627; 455; 83; 54; 5] 20668 1 36326 ((2, 2) :: (29236, 2) :: (1, 1) :: repeat (1, 2) 116430 ++ (1483183, 2) :: (1, 1) :: repeat (1, 2) 3474178 ++ (4901382, 2) :: (1, 1) :: repeat (1, 2) 29403094 ++ w) 1)).
  {
    rewrite NUM59X30.
    apply (hGRIND_even 18161 [2806; 627; 455; 83; 54; 5] 20668 ((29236, 2) :: (1, 1) :: repeat (1, 2) 116430 ++ (1483183, 2) :: (1, 1) :: repeat (1, 2) 3474178 ++ (4901382, 2) :: (1, 1) :: repeat (1, 2) 29403094 ++ w) 1); closearith.
  }
  (* step 379: P TUP2_1 *)
  apply (hsteps_trans _ (HC [20669; 2806; 627; 455; 83; 54; 5] 36326 1 2 ((29234, 2) :: (1, 1) :: repeat (1, 2) 116430 ++ (1483183, 2) :: (1, 1) :: repeat (1, 2) 3474178 ++ (4901382, 2) :: (1, 1) :: repeat (1, 2) 29403094 ++ w) 1)).
  {
    replace ((29234, 2) :: (1, 1) :: repeat (1, 2) 116430 ++ (1483183, 2) :: (1, 1) :: repeat (1, 2) 3474178 ++ (4901382, 2) :: (1, 1) :: repeat (1, 2) 29403094 ++ w) with ((29236 - 2, 2) :: (1, 1) :: repeat (1, 2) 116430 ++ (1483183, 2) :: (1, 1) :: repeat (1, 2) 3474178 ++ (4901382, 2) :: (1, 1) :: repeat (1, 2) 29403094 ++ w) by sec_eq.
    apply (sTUP2_1 [2806; 627; 455; 83; 54; 5] 20668 36325 29236 ((1, 1) :: repeat (1, 2) 116430 ++ (1483183, 2) :: (1, 1) :: repeat (1, 2) 3474178 ++ (4901382, 2) :: (1, 1) :: repeat (1, 2) 29403094 ++ w) 1); closearith.
  }
  (* step 380: P TDN *)
  apply (hsteps_trans _ (HB [20669; 2806; 627; 455; 83; 54; 5] 36326 1 4 ((29234, 2) :: (1, 1) :: repeat (1, 2) 116430 ++ (1483183, 2) :: (1, 1) :: repeat (1, 2) 3474178 ++ (4901382, 2) :: (1, 1) :: repeat (1, 2) 29403094 ++ w) 1)).
  {
    apply (sTDN [20669; 2806; 627; 455; 83; 54; 5] 36326 ((29234, 2) :: (1, 1) :: repeat (1, 2) 116430 ++ (1483183, 2) :: (1, 1) :: repeat (1, 2) 3474178 ++ (4901382, 2) :: (1, 1) :: repeat (1, 2) 29403094 ++ w) 1).
  }
  (* step 381: sTUP *)
  apply (hsteps_trans _ (HC [20669; 2806; 627; 455; 83; 54; 5] 36326 3 2 ((29232, 2) :: (1, 1) :: repeat (1, 2) 116430 ++ (1483183, 2) :: (1, 1) :: repeat (1, 2) 3474178 ++ (4901382, 2) :: (1, 1) :: repeat (1, 2) 29403094 ++ w) 1)).
  {
    replace ((29232, 2) :: (1, 1) :: repeat (1, 2) 116430 ++ (1483183, 2) :: (1, 1) :: repeat (1, 2) 3474178 ++ (4901382, 2) :: (1, 1) :: repeat (1, 2) 29403094 ++ w) with ((29234 - 2, 2) :: (1, 1) :: repeat (1, 2) 116430 ++ (1483183, 2) :: (1, 1) :: repeat (1, 2) 3474178 ++ (4901382, 2) :: (1, 1) :: repeat (1, 2) 29403094 ++ w) by sec_eq.
    apply (sTUP [20669; 2806; 627; 455; 83; 54; 5] 36326 4 29234 2 ((1, 1) :: repeat (1, 2) 116430 ++ (1483183, 2) :: (1, 1) :: repeat (1, 2) 3474178 ++ (4901382, 2) :: (1, 1) :: repeat (1, 2) 29403094 ++ w) 1); closearith.
  }
  (* step 382: CLEANG_even 14615 *)
  apply (hsteps_trans _ (HB [20669; 2806; 627; 455; 83; 54; 5] 36326 1 29236 ((2, 2) :: (1, 1) :: repeat (1, 2) 116430 ++ (1483183, 2) :: (1, 1) :: repeat (1, 2) 3474178 ++ (4901382, 2) :: (1, 1) :: repeat (1, 2) 29403094 ++ w) 1)).
  {
    apply (CLEANG_even 14615 [20669; 2806; 627; 455; 83; 54; 5] 36326 ((1, 1) :: repeat (1, 2) 116430 ++ (1483183, 2) :: (1, 1) :: repeat (1, 2) 3474178 ++ (4901382, 2) :: (1, 1) :: repeat (1, 2) 29403094 ++ w) 1); closearith.
  }
  (* step 383: P TRANS2_1 *)
  apply (sTRANS2_1 [20669; 2806; 627; 455; 83; 54; 5] 36326 29235 1 (repeat (1, 2) 116430 ++ (1483183, 2) :: (1, 1) :: repeat (1, 2) 3474178 ++ (4901382, 2) :: (1, 1) :: repeat (1, 2) 29403094 ++ w) 1); closearith.
Qed.

(* CASCADE59j: steps 384-384 of the CASCADE59 chain. *)
Lemma CASCADE59j : forall w,
  hsteps (HB [36327; 20669; 2806; 627; 455; 83; 54; 5] 29237 1 3 (repeat (1, 2) 116430 ++ (1483183, 2) :: (1, 1) :: repeat (1, 2) 3474178 ++ (4901382, 2) :: (1, 1) :: repeat (1, 2) 29403094 ++ w) 1)
         (HB [36327; 20669; 2806; 627; 455; 83; 54; 5] 145667 1 232863 ((1483183, 2) :: (1, 1) :: repeat (1, 2) 3474178 ++ (4901382, 2) :: (1, 1) :: repeat (1, 2) 29403094 ++ w) 1).
Proof.
  intro w.
  replace 145667 with (29237 + 116430)
    by (apply Nat.eqb_eq; vm_compute; reflexivity).
  replace 232863 with (3 + 2 * 116430)
    by (apply Nat.eqb_eq; vm_compute; reflexivity).
  (* step 384: M pop12 (116430,) *)
  apply (pop12 116430 [36327; 20669; 2806; 627; 455; 83; 54; 5] 29237 3 ((1483183, 2) :: (1, 1) :: repeat (1, 2) 3474178 ++ (4901382, 2) :: (1, 1) :: repeat (1, 2) 29403094 ++ w) 1); closearith.
Qed.

