(* ================================================================= *)
(* Phase 57: the ELEVENTH descent -- TAIL2_END11 modulo              *)
(* TAIL2_END12.                                                      *)
(*                                                                   *)
(* The TOP10 state (frame [652285; 206767; 138671; 25145; 13306;    *)
(* 4643; 2871; 335; 235; 42; 19], counter 4042956, shuttle 5937475)  *)
(* at pair (2j, 2), j >= 5937478, beta >= 2, is mechanised by the    *)
(* same fixed-parse pattern as Phases 47-56:                         *)
(*                                                                   *)
(*  1. FRONT (identical in shape to the Phase 56 front): TUP,        *)
(*     hGRIND_even 2968735, TUP2_1, TDN, TUP                         *)
(*     -> GRIND11 = HC [4042956; 652285; 206767; 138671; 25145;      *)
(*        13306; 4643; 2871; 335; 235; 42; 19]                       *)
(*        5937474 3 2 ((2j - 6, 2) :: tail(beta)).                   *)
(*  2. DIPGRIND (5937474, r11), r11 = 2j - 11874954 >= 2:            *)
(*     -> HC [4042956; 652285; ...] 0 3 2 (spine 5937474 ++ W),      *)
(*        W = ((r11, 2) :: (1, 1) :: (1, 2)^(beta-1)).               *)
(*  3. CASCADE57: a FIXED parse of only 17 lemma steps from the      *)
(*     spine to TOP11 (hsim57: the 25-step classified chain at      *)
(*     (5937478, 2) reaches the era landing, and the cascade's       *)
(*     label sequence and abstracted targets are identical at       *)
(*     beta = 3; the classifier was first validated by exact         *)
(*     reproduction of the Phase 56 classified chain, 807 steps,     *)
(*     0 mismatches).  After the long CASCADE56 (799 steps), the     *)
(*     eleventh descent is again SHORT (the CASCADE55 pattern):      *)
(*     2 PX2A, 1 PUSH, 2 TDN, 3 TUP, a SINGLE DIPGRIND level         *)
(*     (652283, 2738384), 1 hGRIND 103381, 1 POP, pop12 652285,      *)
(*     hGRIND_even 755667, TUP2_1, CLEANG_even 1369188, TRANS2_1,    *)
(*     pop12 5937476.  The frame SHRINKS from eleven blocks to       *)
(*     ten:                                                          *)
(*                                                                   *)
(*       TOP11 = HB [1511339; 790956; 25145; 13306; 4643; 2871;      *)
(*                   335; 235; 42; 19]                               *)
(*               8675859 1 11874955 W.                               *)
(*                                                                   *)
(*  4. TOP11 closings by r11' = 2 * j11, j11 = j - 5937477:          *)
(*    r11' = 2:       TRANS2_1 + CASCADE_POPFIN, A = 11874955 + beta,*)
(*                    frame [8675860; 1511339; 790956; ...];         *)
(*    r11' = 4:       TUP + hGRIND_even 5937475 + TRANS2_2           *)
(*                    + CASCADE_POPFIN, A = beta + 2;                *)
(*    r11' = 6:       TUP + hGRIND_even 5937475 + TUP2_1 + TDN       *)
(*                    + TRANS2_1 + CASCADE_POPFIN, A = beta + 4;     *)
(*    8 <= r11' <= 23749914 (band 11): TUP + hGRIND_even 5937475     *)
(*      + TUP2_1 + TDN + TUP onto GRIND12 = HC [8675859; 1511339;    *)
(*      ...] 11874954 3 2 ((r11' - 6, 2) :: tail), whose pair        *)
(*      grinds CLEANLY by CLEANG_even (floor (r11' - 8)/2 + 1 <=     *)
(*      11874954, exactly r11' <= 23749914), then TRANS2_1 +         *)
(*      CASCADE_POPFIN, A = r11' + beta - 2, frame [11874955;       *)
(*      8675859; 1511339; ...].  (The band counter is again the      *)
(*      shuttle moved into the counter slot by TUP2_1: 11874954,     *)
(*      not 8675859.)                                                *)
(*                                                                   *)
(*  For r11' >= 23749916 (j11 >= 11874958, i.e. TOP10-parameter      *)
(*  j >= 17812435) the pair (r11' - 6, 2) at counter 11874954        *)
(*  exceeds the CLEANG_even floor and the rounds take the DIPDESC    *)
(*  boundary a TWELFTH time (hsim57 Part 3: the GRIND12 state and    *)
(*  the DIPGRIND (11874954, r11' - 23749914) landing both occur at   *)
(*  j11 = 11874958, 11874959, 12500000).  The twelfth descent is     *)
(*  expected to be a NEW cascade with different constants, so no     *)
(*  cycle induction in the current vocabulary closes it; what        *)
(*  remains is the strictly smaller core                             *)
(*                                                                   *)
(*    TAIL2_END12: the totality of the ONE pair (2j, 2) at the ONE   *)
(*    fixed TOP11 state HB [1511339; 790956; 25145; 13306; 4643;     *)
(*    2871; 335; 235; 42; 19] 8675859 1 11874955, for                *)
(*    j >= 11874958 (r11' = 2j >= 23749916), beta >= 2.              *)
(*                                                                   *)
(*  The core's range shrank from [5937478, infty) to [17812435,      *)
(*  infty) in TOP10 parameters; the band width roughly doubled       *)
(*  again (5937478 -> 17812434).  Via TAIL2_END11_of57 +              *)
(*  TAIL2_END10_of56 + ESC_ERA_LAW_56 the ESC instances at every     *)
(*  even R >= 1278 now rest on TAIL2_END12 alone                     *)
(*  (ESC_ERA_LAW_57 below; Loop.v Part 4r).                          *)
(* ================================================================= *)

Require Import List Bool Arith Lia ZArith.
Import ListNotations.
Require Import TM Sections Mirror TokenPass Recoord Era Esc Dev
               Grind Grind2 Grind3 Grind4 Grind5 Grind6 Grind7 Grind8
               Grind9 Grind10 Grind11 Grind12 Grind13 Grind14 Grind15
               Grind16 Grind17 Grind18 Grind19 Grind20 Grind21 Grind22
               Grind23 Grind24.

(* Section equality: componentwise, arithmetic leaves by lia.      *)
Ltac sec_eq :=
  repeat (first [ solve [reflexivity] | solve [lia] | f_equal ]).

(* Closed-numeral arithmetic: literals >= 7426 are parsed as       *)
(* Nat.of_num_uint atoms, which lia cannot relate to variables;    *)
(* for purely closed <= goals the boolean check decides them.      *)
Ltac closearith :=
  first [ lia | apply Nat.leb_le; reflexivity ].

(* Numeral identities for the TOP11 closings and the               *)
(* TAIL2_END11_of57 case split, factored into standalone lemmas    *)
(* proved by Nat.eqb_eq + vm_compute (the Phase 52-56 pattern).    *)
(* The TOP11 front reuses Grind24's NUM56h / NUM56a / NUM56b /     *)
(* NUM56i verbatim (same constants).                               *)
(* hGRIND_even 5937475 in the TOP11 closings:                       *)
Lemma NUM57a : 11874954 = 2 * 5937475 + 4.
Proof. apply Nat.eqb_eq; vm_compute; reflexivity. Qed.
Lemma NUM57a3 : 2 * 5937475 + 4 = S 11874953.
Proof. apply Nat.eqb_eq; vm_compute; reflexivity. Qed.
Lemma NUM57b : 8675859 = S 8675858.
Proof. apply Nat.eqb_eq; vm_compute; reflexivity. Qed.
(* The r11' = 2 closing (TRANS2_1 at TOP11):                        *)
Lemma NUM57e : 11874955 = S 11874954.
Proof. apply Nat.eqb_eq; vm_compute; reflexivity. Qed.
Lemma NUM57f : 11874956 = S (S 11874954).
Proof. apply Nat.eqb_eq; vm_compute; reflexivity. Qed.
Lemma NUM57g : 8675860 = S 8675859.
Proof. apply Nat.eqb_eq; vm_compute; reflexivity. Qed.
(* The r11' = 4 / 6 / band first TUP (shuttle form):                *)
Lemma NUM57h : 11874954 = 11874955 - 1.
Proof. apply Nat.eqb_eq; vm_compute; reflexivity. Qed.
(* The r11' = 4 TRANS2_2 step and the TUP2_1 steps:                 *)
Lemma NUM57i : 11874954 = S 11874953.
Proof. apply Nat.eqb_eq; vm_compute; reflexivity. Qed.
Lemma NUM57j : 11874955 = S (S 11874953).
Proof. apply Nat.eqb_eq; vm_compute; reflexivity. Qed.
(* The band CLEANG_even floor:                                      *)
Lemma NUM57k : 11874954 = 11874957 - 3.
Proof. apply Nat.eqb_eq; vm_compute; reflexivity. Qed.
(* The TAIL2_END11_of57 case split:                                 *)
Lemma NUM57m : 11874958 = S 11874957.
Proof. apply Nat.eqb_eq; vm_compute; reflexivity. Qed.
Lemma NUM57n : 11874956 = S 11874955.
Proof. apply Nat.eqb_eq; vm_compute; reflexivity. Qed.
Lemma NUM57p : 5937478 = S 5937477.
Proof. apply Nat.eqb_eq; vm_compute; reflexivity. Qed.

(* Factored list identities for the three PX2A steps of     *)
(* CASCADE57 whose produced (1, 2)s merge into a spine      *)
(* repeat of length > 175000 (cascade steps 1, 6, 468):     *)
(* the goal's stated target is first rewritten to the       *)
(* constructor's unmerged form via REP57a-c (whose proofs   *)
(* rewrite the run length to S-form and close by            *)
(* reflexivity), and the frame atoms are put in S-form via  *)
(* NUM57ta1-3 / tb1-3 / tc1-3, since hPX2A's frame pattern   *)
(* is S (S (S b')) :: S p' :: pb and its target counter is  *)
(* S b' (the CASCADE55 step-1 pattern, generalised).       *)
Lemma NUM57ssa : 5937476 = S (S 5937474).
Proof. apply Nat.eqb_eq; vm_compute; reflexivity. Qed.
Lemma REP57a : forall w,
  (1, 1) :: (1, 2) :: (1, 2) :: repeat (1, 2) 5937474 ++ w
  = (1, 1) :: repeat (1, 2) 5937476 ++ w.
Proof. intro w. rewrite NUM57ssa. reflexivity. Qed.
Lemma NUM57ta1 : 4042956 = S (S (S 4042953)).
Proof. apply Nat.eqb_eq; vm_compute; reflexivity. Qed.
Lemma NUM57ta2 : 652285 = S 652284.
Proof. apply Nat.eqb_eq; vm_compute; reflexivity. Qed.
Lemma NUM57ta3 : 4042954 = S 4042953.
Proof. apply Nat.eqb_eq; vm_compute; reflexivity. Qed.
Lemma NUM57ssb : 652285 = S (S 652283).
Proof. apply Nat.eqb_eq; vm_compute; reflexivity. Qed.
Lemma REP57b : forall w,
  (1, 1) :: (1, 2) :: (1, 2) :: repeat (1, 2) 652283 ++ w
  = (1, 1) :: repeat (1, 2) 652285 ++ w.
Proof. intro w. rewrite NUM57ssb. reflexivity. Qed.
Lemma NUM57tb1 : 206767 = S (S (S 206764)).
Proof. apply Nat.eqb_eq; vm_compute; reflexivity. Qed.
Lemma NUM57tb2 : 138671 = S 138670.
Proof. apply Nat.eqb_eq; vm_compute; reflexivity. Qed.
Lemma NUM57tb3 : 206765 = S 206764.
Proof. apply Nat.eqb_eq; vm_compute; reflexivity. Qed.

(* Closed arithmetic identities for the large DIPGRIND /   *)
(* hGRIND_even / CLEANG steps and the head-pair             *)
(* normalisations of CASCADE57, factored into standalone    *)
(* lemmas (eqb/vm proofs) and rewritten in the step blocks, *)
(* so the applies meet the lemmas' arithmetic forms        *)
(* syntactically instead of by a closed multiplication or   *)
(* subtraction conversion at depth >= 100000                *)
(* (cf. NUM57ss / REP57a-c).                                *)
Lemma NUM57X1 : 652284 = S 652283.
Proof. apply Nat.eqb_eq; vm_compute; reflexivity. Qed.
Lemma NUM57X2 : 4042952 = 4042954 - 2.
Proof. apply Nat.eqb_eq; vm_compute; reflexivity. Qed.
Lemma NUM57X3 : 4042950 = 4042952 - 2.
Proof. apply Nat.eqb_eq; vm_compute; reflexivity. Qed.
Lemma NUM57X4 : 4042950 = 2 * 652283 + 2738384.
Proof. apply Nat.eqb_eq; vm_compute; reflexivity. Qed.
Lemma NUM57X5 : 138671 = S 138670.
Proof. apply Nat.eqb_eq; vm_compute; reflexivity. Qed.
Lemma NUM57X6 : 206769 = 206768 + 1.
Proof. apply Nat.eqb_eq; vm_compute; reflexivity. Qed.
Lemma NUM57X7 : 1511338 = 1511339 - 1.
Proof. apply Nat.eqb_eq; vm_compute; reflexivity. Qed.
Lemma NUM57X8 : 2738382 = 2738384 - 2.
Proof. apply Nat.eqb_eq; vm_compute; reflexivity. Qed.
Lemma NUM57X9 : 1511338 = 2 * 755667 + 4.
Proof. apply Nat.eqb_eq; vm_compute; reflexivity. Qed.
Lemma NUM57X10 : 1511338 = S 1511337.
Proof. apply Nat.eqb_eq; vm_compute; reflexivity. Qed.
Lemma NUM57X11 : 790956 = S 790955.
Proof. apply Nat.eqb_eq; vm_compute; reflexivity. Qed.
Lemma NUM57X12 : 2738380 = 2738382 - 2.
Proof. apply Nat.eqb_eq; vm_compute; reflexivity. Qed.
Lemma NUM57X13 : 2738378 = 2738380 - 2.
Proof. apply Nat.eqb_eq; vm_compute; reflexivity. Qed.
Lemma NUM57X14 : 2738378 = 2 * 1369188 + 2.
Proof. apply Nat.eqb_eq; vm_compute; reflexivity. Qed.
Lemma NUM57X15 : 2738382 = 2 * 1369188 + 6.
Proof. apply Nat.eqb_eq; vm_compute; reflexivity. Qed.
Lemma NUM57X16 : 2738382 = S 2738381.
Proof. apply Nat.eqb_eq; vm_compute; reflexivity. Qed.
Lemma NUM57X17 : 2738383 = S (S 2738381).
Proof. apply Nat.eqb_eq; vm_compute; reflexivity. Qed.
Lemma NUM57X18 : 1511339 = S 1511338.
Proof. apply Nat.eqb_eq; vm_compute; reflexivity. Qed.

(* CASCADE57a: steps 1-8 of the CASCADE57 chain. *)
Lemma CASCADE57a : forall w,
  hsteps (HC [4042956; 652285; 206767; 138671; 25145; 13306; 4643; 2871; 335; 235; 42; 19] 0 3 2 (repeat (1, 2) 5937474 ++ w) 1)
         (HB [25145; 13306; 4643; 2871; 335; 235; 42; 19] 138671 1 206769 (repeat (1, 2) 652285 ++ (2738384, 2) :: (1, 1) :: repeat (1, 2) 5937476 ++ w) 1).
Proof.
  intro w.
  (* step 1: P PX2A *)
  apply (hsteps_trans _ (HC [206767; 138671; 25145; 13306; 4643; 2871; 335; 235; 42; 19] 652284 4042954 2 ((1, 1) :: repeat (1, 2) 5937476 ++ w) 1)).
  {
    rewrite NUM57ta1. rewrite NUM57ta2. rewrite NUM57ta3.
    replace ((1, 1) :: repeat (1, 2) 5937476 ++ w)
      with ((1, 1) :: (1, 2) :: (1, 2) :: repeat (1, 2) 5937474 ++ w)
      by (apply REP57a).
    exact (hsteps_step _ _ _ (hPX2A 4042953 652284 [206767; 138671; 25145; 13306; 4643; 2871; 335; 235; 42; 19] (repeat (1, 2) 5937474 ++ w) 1) (hsteps_refl _)).
  }
  (* step 2: P PUSH *)
  apply (hsteps_trans _ (HC [206767; 138671; 25145; 13306; 4643; 2871; 335; 235; 42; 19] 652283 1 2 ((4042952, 2) :: (1, 1) :: repeat (1, 2) 5937476 ++ w) 1)).
  {
    rewrite NUM57X1.
    rewrite NUM57X2.
    apply (sPUSH [206767; 138671; 25145; 13306; 4643; 2871; 335; 235; 42; 19] 652283 4042954 ((1, 1) :: repeat (1, 2) 5937476 ++ w) 1); closearith.
  }
  (* step 3: P TDN *)
  apply (hsteps_trans _ (HB [206767; 138671; 25145; 13306; 4643; 2871; 335; 235; 42; 19] 652283 1 4 ((4042952, 2) :: (1, 1) :: repeat (1, 2) 5937476 ++ w) 1)).
  {
    apply (sTDN [206767; 138671; 25145; 13306; 4643; 2871; 335; 235; 42; 19] 652283 ((4042952, 2) :: (1, 1) :: repeat (1, 2) 5937476 ++ w) 1).
  }
  (* step 4: sTUP *)
  apply (hsteps_trans _ (HC [206767; 138671; 25145; 13306; 4643; 2871; 335; 235; 42; 19] 652283 3 2 ((4042950, 2) :: (1, 1) :: repeat (1, 2) 5937476 ++ w) 1)).
  {
    rewrite NUM57X3.
    apply (sTUP [206767; 138671; 25145; 13306; 4643; 2871; 335; 235; 42; 19] 652283 4 4042952 2 ((1, 1) :: repeat (1, 2) 5937476 ++ w) 1); closearith.
  }
  (* step 5: DIPGRIND 652283 2738384 *)
  apply (hsteps_trans _ (HC [206767; 138671; 25145; 13306; 4643; 2871; 335; 235; 42; 19] 0 3 2 (repeat (1, 2) 652283 ++ (2738384, 2) :: (1, 1) :: repeat (1, 2) 5937476 ++ w) 1)).
  {
    rewrite NUM57X4.
    apply (DIPGRIND 652283 2738384 [206767; 138671; 25145; 13306; 4643; 2871; 335; 235; 42; 19] ((1, 1) :: repeat (1, 2) 5937476 ++ w) 1); closearith.
  }
  (* step 6: P PX2A *)
  apply (hsteps_trans _ (HC [25145; 13306; 4643; 2871; 335; 235; 42; 19] 138670 206765 2 ((1, 1) :: repeat (1, 2) 652285 ++ (2738384, 2) :: (1, 1) :: repeat (1, 2) 5937476 ++ w) 1)).
  {
    rewrite NUM57tb1. rewrite NUM57tb2. rewrite NUM57tb3.
    replace ((1, 1) :: repeat (1, 2) 652285 ++ (2738384, 2) :: (1, 1) :: repeat (1, 2) 5937476 ++ w)
      with ((1, 1) :: (1, 2) :: (1, 2) :: repeat (1, 2) 652283 ++ (2738384, 2) :: (1, 1) :: repeat (1, 2) 5937476 ++ w)
      by (apply REP57b).
    exact (hsteps_step _ _ _ (hPX2A 206764 138670 [25145; 13306; 4643; 2871; 335; 235; 42; 19] (repeat (1, 2) 652283 ++ (2738384, 2) :: (1, 1) :: repeat (1, 2) 5937476 ++ w) 1) (hsteps_refl _)).
  }
  (* step 7: hGRIND 103381 *)
  apply (hsteps_trans _ (HB [25145; 13306; 4643; 2871; 335; 235; 42; 19] 138670 1 206768 ((1, 1) :: repeat (1, 2) 652285 ++ (2738384, 2) :: (1, 1) :: repeat (1, 2) 5937476 ++ w) 1)).
  {
    apply (hGRIND 103381 [25145; 13306; 4643; 2871; 335; 235; 42; 19] 138670 ((1, 1) :: repeat (1, 2) 652285 ++ (2738384, 2) :: (1, 1) :: repeat (1, 2) 5937476 ++ w) 1); closearith.
  }
  (* step 8: P POP *)
  rewrite NUM57X5.
  rewrite NUM57X6.
  apply (sPOP1 [25145; 13306; 4643; 2871; 335; 235; 42; 19] 138670 206768 (repeat (1, 2) 652285 ++ (2738384, 2) :: (1, 1) :: repeat (1, 2) 5937476 ++ w) 1); closearith.
Qed.

(* CASCADE57b: steps 9-9 of the CASCADE57 chain. *)
Lemma CASCADE57b : forall w,
  hsteps (HB [25145; 13306; 4643; 2871; 335; 235; 42; 19] 138671 1 206769 (repeat (1, 2) 652285 ++ (2738384, 2) :: (1, 1) :: repeat (1, 2) 5937476 ++ w) 1)
         (HB [25145; 13306; 4643; 2871; 335; 235; 42; 19] 790956 1 1511339 ((2738384, 2) :: (1, 1) :: repeat (1, 2) 5937476 ++ w) 1).
Proof.
  intro w.
  replace 790956 with (138671 + 652285)
    by (apply Nat.eqb_eq; vm_compute; reflexivity).
  replace 1511339 with (206769 + 2 * 652285)
    by (apply Nat.eqb_eq; vm_compute; reflexivity).
  (* step 9: M pop12 (652285,) *)
  apply (pop12 652285 [25145; 13306; 4643; 2871; 335; 235; 42; 19] 138671 206769 ((2738384, 2) :: (1, 1) :: repeat (1, 2) 5937476 ++ w) 1); closearith.
Qed.

(* CASCADE57c: steps 10-16 of the CASCADE57 chain. *)
Lemma CASCADE57c : forall w,
  hsteps (HB [25145; 13306; 4643; 2871; 335; 235; 42; 19] 790956 1 1511339 ((2738384, 2) :: (1, 1) :: repeat (1, 2) 5937476 ++ w) 1)
         (HB [1511339; 790956; 25145; 13306; 4643; 2871; 335; 235; 42; 19] 2738383 1 3 (repeat (1, 2) 5937476 ++ w) 1).
Proof.
  intro w.
  (* step 10: sTUP *)
  apply (hsteps_trans _ (HC [25145; 13306; 4643; 2871; 335; 235; 42; 19] 790956 1511338 2 ((2738382, 2) :: (1, 1) :: repeat (1, 2) 5937476 ++ w) 1)).
  {
    rewrite NUM57X7.
    rewrite NUM57X8.
    apply (sTUP [25145; 13306; 4643; 2871; 335; 235; 42; 19] 790956 1511339 2738384 2 ((1, 1) :: repeat (1, 2) 5937476 ++ w) 1); closearith.
  }
  (* step 11: hGRIND_even 755667 *)
  apply (hsteps_trans _ (HB [25145; 13306; 4643; 2871; 335; 235; 42; 19] 790955 1 1511338 ((2, 2) :: (2738382, 2) :: (1, 1) :: repeat (1, 2) 5937476 ++ w) 1)).
  {
    rewrite NUM57X9.
    apply (hGRIND_even 755667 [25145; 13306; 4643; 2871; 335; 235; 42; 19] 790955 ((2738382, 2) :: (1, 1) :: repeat (1, 2) 5937476 ++ w) 1); closearith.
  }
  (* step 12: P TUP2_1 *)
  apply (hsteps_trans _ (HC [790956; 25145; 13306; 4643; 2871; 335; 235; 42; 19] 1511338 1 2 ((2738380, 2) :: (1, 1) :: repeat (1, 2) 5937476 ++ w) 1)).
  {
    rewrite NUM57X10.
    rewrite NUM57X11.
    rewrite NUM57X12.
    apply (sTUP2_1 [25145; 13306; 4643; 2871; 335; 235; 42; 19] 790955 1511337 2738382 ((1, 1) :: repeat (1, 2) 5937476 ++ w) 1); closearith.
  }
  (* step 13: P TDN *)
  apply (hsteps_trans _ (HB [790956; 25145; 13306; 4643; 2871; 335; 235; 42; 19] 1511338 1 4 ((2738380, 2) :: (1, 1) :: repeat (1, 2) 5937476 ++ w) 1)).
  {
    apply (sTDN [790956; 25145; 13306; 4643; 2871; 335; 235; 42; 19] 1511338 ((2738380, 2) :: (1, 1) :: repeat (1, 2) 5937476 ++ w) 1).
  }
  (* step 14: sTUP *)
  apply (hsteps_trans _ (HC [790956; 25145; 13306; 4643; 2871; 335; 235; 42; 19] 1511338 3 2 ((2738378, 2) :: (1, 1) :: repeat (1, 2) 5937476 ++ w) 1)).
  {
    rewrite NUM57X13.
    apply (sTUP [790956; 25145; 13306; 4643; 2871; 335; 235; 42; 19] 1511338 4 2738380 2 ((1, 1) :: repeat (1, 2) 5937476 ++ w) 1); closearith.
  }
  (* step 15: CLEANG_even 1369188 *)
  apply (hsteps_trans _ (HB [790956; 25145; 13306; 4643; 2871; 335; 235; 42; 19] 1511338 1 2738382 ((2, 2) :: (1, 1) :: repeat (1, 2) 5937476 ++ w) 1)).
  {
    rewrite NUM57X14.
    rewrite NUM57X15.
    apply (CLEANG_even 1369188 [790956; 25145; 13306; 4643; 2871; 335; 235; 42; 19] 1511338 ((1, 1) :: repeat (1, 2) 5937476 ++ w) 1); closearith.
  }
  (* step 16: P TRANS2_1 *)
  rewrite NUM57X16.
  rewrite NUM57X17.
  rewrite NUM57X18.
  apply (sTRANS2_1 [790956; 25145; 13306; 4643; 2871; 335; 235; 42; 19] 1511338 2738381 1 (repeat (1, 2) 5937476 ++ w) 1); closearith.
Qed.

(* CASCADE57d: steps 17-17 of the CASCADE57 chain. *)
Lemma CASCADE57d : forall w,
  hsteps (HB [1511339; 790956; 25145; 13306; 4643; 2871; 335; 235; 42; 19] 2738383 1 3 (repeat (1, 2) 5937476 ++ w) 1)
         (HB [1511339; 790956; 25145; 13306; 4643; 2871; 335; 235; 42; 19] 8675859 1 11874955 (w) 1).
Proof.
  intro w.
  replace 8675859 with (2738383 + 5937476)
    by (apply Nat.eqb_eq; vm_compute; reflexivity).
  replace 11874955 with (3 + 2 * 5937476)
    by (apply Nat.eqb_eq; vm_compute; reflexivity).
  (* step 17: M pop12 (5937476,) *)
  apply (pop12 5937476 [1511339; 790956; 25145; 13306; 4643; 2871; 335; 235; 42; 19] 2738383 3 (w) 1); closearith.
Qed.

Lemma CASCADE57 : forall w,
  hsteps (HC [4042956; 652285; 206767; 138671; 25145; 13306; 4643; 2871; 335; 235; 42; 19] 0 3 2 (repeat (1, 2) 5937474 ++ w) 1)
         (HB [1511339; 790956; 25145; 13306; 4643; 2871; 335; 235; 42; 19] 8675859 1 11874955 (w) 1).
Proof.
  intro w.
  apply (hsteps_trans _ (HB [25145; 13306; 4643; 2871; 335; 235; 42; 19] 138671 1 206769 (repeat (1, 2) 652285 ++ (2738384, 2) :: (1, 1) :: repeat (1, 2) 5937476 ++ w) 1)).
  { apply (CASCADE57a w). }
  apply (hsteps_trans _ (HB [25145; 13306; 4643; 2871; 335; 235; 42; 19] 790956 1 1511339 ((2738384, 2) :: (1, 1) :: repeat (1, 2) 5937476 ++ w) 1)).
  { apply (CASCADE57b w). }
  apply (hsteps_trans _ (HB [1511339; 790956; 25145; 13306; 4643; 2871; 335; 235; 42; 19] 2738383 1 3 (repeat (1, 2) 5937476 ++ w) 1)).
  { apply (CASCADE57c w). }
  apply (CASCADE57d w).
Qed.

(* ----------------------------------------------------------------- *)
(* TOP57_TO_TOP11: the TOP10 state at (2j, 2) reaches TOP11 at the   *)
(* pair (2 * (j - 5937477), 2).  The front is the Phase 56 front      *)
(* verbatim at the new constants: the first TUP rewrites via         *)
(* NUM56h (5937474 = 5937475 - 1, inherited from Grind24.v), the     *)
(* hGRIND_even 2968735 step rewrites the goal by NUM56a / NUM56b     *)
(* (5937474 = 2 * 2968735 + 4, 4042956 = S 4042955), and the         *)
(* TUP2_1 step rewrites via NUM56i (5937474 = S 5937473) / NUM56b.   *)
(* ----------------------------------------------------------------- *)

Lemma TOP57_TO_TOP11 : forall j beta, 5937478 <= j -> 2 <= beta ->
  hsteps (HB [652285; 206767; 138671; 25145; 13306; 4643; 2871; 335; 235; 42; 19] 4042956 1 5937475
            ((2 * j, 2) :: (1, 1) :: repeat (1, 2) (beta - 1)) 1)
         (HB [1511339; 790956; 25145; 13306; 4643; 2871; 335; 235; 42; 19] 8675859 1 11874955
            ((2 * (j - 5937477), 2) :: (1, 1)
             :: repeat (1, 2) (beta - 1)) 1).
Proof.
  intros j beta Hj Hb.
  assert (Hj4 : 4 <= j).
  { apply Nat.le_trans with 5937478; [closearith | exact Hj]. }
  assert (Hr : 1 <= j - 5937477).
  { assert (E : 5937477 = 5937478 - 1)
      by (apply Nat.eqb_eq; vm_compute; reflexivity).
    rewrite E. lia. }
  assert (Heq : 2 * j - 6 = 2 * 5937474 + 2 * (j - 5937477)).
  { assert (E1 : 5937477 = 5937474 + 3)
      by (apply Nat.eqb_eq; vm_compute; reflexivity).
    assert (E2 : 5937478 = 5937474 + 4)
      by (apply Nat.eqb_eq; vm_compute; reflexivity).
    rewrite E1. rewrite E2 in Hj. lia. }
  apply (hsteps_trans _ (HC [652285; 206767; 138671; 25145; 13306; 4643; 2871; 335; 235; 42; 19] 4042956
    5937474 2 ((2 * j - 2, 2) :: (1, 1) :: repeat (1, 2) (beta - 1)) 1)).
  { rewrite NUM56h.
    apply (sTUP [652285; 206767; 138671; 25145; 13306; 4643; 2871; 335; 235; 42; 19] 4042956 5937475 (2 * j) 2
           ((1, 1) :: repeat (1, 2) (beta - 1)) 1); closearith. }
  apply (hsteps_trans _ (HB [652285; 206767; 138671; 25145; 13306; 4643; 2871; 335; 235; 42; 19]
    4042955 1 5937474 ((2, 2) :: (2 * j - 2, 2) :: (1, 1)
            :: repeat (1, 2) (beta - 1)) 1)).
  { rewrite NUM56a. rewrite NUM56b.
    apply (hGRIND_even 2968735 [652285; 206767; 138671; 25145; 13306; 4643; 2871; 335; 235; 42; 19]
           4042955 ((2 * j - 2, 2) :: (1, 1) :: repeat (1, 2) (beta - 1))
           1); closearith. }
  apply (hsteps_trans _ (HC [4042956; 652285; 206767; 138671; 25145; 13306; 4643; 2871; 335; 235; 42; 19] 5937474 1 2 ((2 * j - 4, 2) :: (1, 1)
            :: repeat (1, 2) (beta - 1)) 1)).
  { rewrite NUM56i. rewrite NUM56b.
    replace ((2 * j - 4, 2) :: (1, 1) :: repeat (1, 2) (beta - 1))
      with ((2 * j - 2 - 2, 2) :: (1, 1) :: repeat (1, 2) (beta - 1))
      by sec_eq.
    apply (sTUP2_1 [652285; 206767; 138671; 25145; 13306; 4643; 2871; 335; 235; 42; 19] 4042955
           5937473 (2 * j - 2) ((1, 1) :: repeat (1, 2) (beta - 1)) 1); lia. }
  apply (hsteps_trans _ (HB [4042956; 652285; 206767; 138671; 25145; 13306; 4643; 2871; 335; 235; 42; 19] 5937474 1 4 ((2 * j - 4, 2) :: (1, 1)
            :: repeat (1, 2) (beta - 1)) 1)).
  { apply (sTDN [4042956; 652285; 206767; 138671; 25145; 13306; 4643; 2871; 335; 235; 42; 19] 5937474
           ((2 * j - 4, 2) :: (1, 1) :: repeat (1, 2) (beta - 1))
           1). }
  apply (hsteps_trans _ (HC [4042956; 652285; 206767; 138671; 25145; 13306; 4643; 2871; 335; 235; 42; 19] 5937474 3 2 ((2 * j - 6, 2) :: (1, 1)
            :: repeat (1, 2) (beta - 1)) 1)).
  { replace ((2 * j - 6, 2) :: (1, 1) :: repeat (1, 2) (beta - 1))
      with ((2 * j - 4 - 2, 2) :: (1, 1) :: repeat (1, 2) (beta - 1))
      by sec_eq.
    apply (sTUP [4042956; 652285; 206767; 138671; 25145; 13306; 4643; 2871; 335; 235; 42; 19] 5937474
           4 (2 * j - 4) 2 ((1, 1) :: repeat (1, 2) (beta - 1)) 1);
      lia. }
  apply (hsteps_trans _ (HC [4042956; 652285; 206767; 138671; 25145; 13306; 4643; 2871; 335; 235; 42; 19]
    0 3 2 (repeat (1, 2) 5937474
     ++ ((2 * (j - 5937477), 2) :: (1, 1)
         :: repeat (1, 2) (beta - 1))) 1)).
  { rewrite Heq.
    apply (DIPGRIND 5937474 (2 * (j - 5937477))
           [4042956; 652285; 206767; 138671; 25145; 13306; 4643; 2871; 335; 235; 42; 19]
           ((1, 1) :: repeat (1, 2) (beta - 1)) 1);
      [closearith | lia]. }
  apply (CASCADE57 ((2 * (j - 5937477), 2) :: (1, 1)
                    :: repeat (1, 2) (beta - 1))).
Qed.

(* ----------------------------------------------------------------- *)
(* The TOP11 closings: r11' = 2, 4, 6 and band 11                    *)
(* (8 <= r11' <= 23749914).                                          *)
(* ----------------------------------------------------------------- *)

Lemma TOP57_2 : forall beta, 2 <= beta ->
  hsteps (HB [1511339; 790956; 25145; 13306; 4643; 2871; 335; 235; 42; 19] 8675859 1 11874955
            ((2, 2) :: (1, 1) :: repeat (1, 2) (beta - 1)) 1)
         (HB [8675860; 1511339; 790956; 25145; 13306; 4643; 2871; 335; 235; 42; 19]
            (11874956 + (beta - 1)) 1 (2 * beta + 1) [] 1).
Proof.
  intros beta Hb.
  apply (hsteps_trans _ (HB [8675860; 1511339; 790956; 25145; 13306; 4643; 2871; 335; 235; 42; 19] 11874956 1 3 (repeat (1, 2) (beta - 1)) 1)).
  { rewrite NUM57e. rewrite NUM57f. rewrite NUM57g.
    apply (sTRANS2_1 [1511339; 790956; 25145; 13306; 4643; 2871; 335; 235; 42; 19] 8675859
           11874954 1 (repeat (1, 2) (beta - 1)) 1); lia. }
  apply (CASCADE_POPFIN [8675860; 1511339; 790956; 25145; 13306; 4643; 2871; 335; 235; 42; 19] 11874956 beta); lia.
Qed.

Lemma TOP57_4 : forall beta, 2 <= beta ->
  hsteps (HB [1511339; 790956; 25145; 13306; 4643; 2871; 335; 235; 42; 19] 8675859 1 11874955
            ((4, 2) :: (1, 1) :: repeat (1, 2) (beta - 1)) 1)
         (HB [11874955; 8675859; 1511339; 790956; 25145; 13306; 4643; 2871; 335; 235; 42; 19]
            (beta + 2) 1 (2 * beta + 1) [] 1).
Proof.
  intros beta Hb.
  apply (hsteps_trans _ (HC [1511339; 790956; 25145; 13306; 4643; 2871; 335; 235; 42; 19]
    8675859 11874954 2
    ((2, 2) :: (1, 1) :: repeat (1, 2) (beta - 1)) 1)).
  { rewrite NUM57h.
    apply (sTUP [1511339; 790956; 25145; 13306; 4643; 2871; 335; 235; 42; 19] 8675859 11874955
           4 2 ((1, 1) :: repeat (1, 2) (beta - 1)) 1); closearith. }
  apply (hsteps_trans _ (HB [1511339; 790956; 25145; 13306; 4643; 2871; 335; 235; 42; 19]
    8675858 1 (2 * 5937475 + 4) ((2, 2) :: (2, 2) :: (1, 1)
            :: repeat (1, 2) (beta - 1)) 1)).
  { rewrite NUM57a. rewrite NUM57b.
    apply (hGRIND_even 5937475 [1511339; 790956; 25145; 13306; 4643; 2871; 335; 235; 42; 19]
           8675858 ((2, 2) :: (1, 1) :: repeat (1, 2) (beta - 1)) 1);
      closearith. }
  apply (hsteps_trans _ (HB [11874955; 8675859; 1511339; 790956; 25145; 13306; 4643; 2871; 335; 235; 42; 19] 3 1 3 (repeat (1, 2) (beta - 1)) 1)).
  { rewrite NUM57a3. rewrite NUM57j. rewrite NUM57b.
    apply (hsteps_step _ (HB [S (S 11874953); S 8675858; 1511339; 790956; 25145; 13306; 4643; 2871; 335; 235; 42; 19] 3 1 3 (repeat (1, 2) (beta - 1)) 1));
      [apply hTRANS2_2; closearith | apply hsteps_refl]. }
  replace (beta + 2) with (3 + (beta - 1)) by lia.
  apply (CASCADE_POPFIN [11874955; 8675859; 1511339; 790956; 25145; 13306; 4643; 2871; 335; 235; 42; 19] 3 beta); lia.
Qed.

Lemma TOP57_6 : forall beta, 2 <= beta ->
  hsteps (HB [1511339; 790956; 25145; 13306; 4643; 2871; 335; 235; 42; 19] 8675859 1 11874955
            ((6, 2) :: (1, 1) :: repeat (1, 2) (beta - 1)) 1)
         (HB [11874955; 8675859; 1511339; 790956; 25145; 13306; 4643; 2871; 335; 235; 42; 19]
            (beta + 4) 1 (2 * beta + 1) [] 1).
Proof.
  intros beta Hb.
  apply (hsteps_trans _ (HC [1511339; 790956; 25145; 13306; 4643; 2871; 335; 235; 42; 19]
    8675859 11874954 2
    ((4, 2) :: (1, 1) :: repeat (1, 2) (beta - 1)) 1)).
  { rewrite NUM57h.
    apply (sTUP [1511339; 790956; 25145; 13306; 4643; 2871; 335; 235; 42; 19] 8675859 11874955
           6 2 ((1, 1) :: repeat (1, 2) (beta - 1)) 1); closearith. }
  apply (hsteps_trans _ (HB [1511339; 790956; 25145; 13306; 4643; 2871; 335; 235; 42; 19]
    8675858 1 (2 * 5937475 + 4) ((2, 2) :: (4, 2) :: (1, 1)
            :: repeat (1, 2) (beta - 1)) 1)).
  { rewrite NUM57a. rewrite NUM57b.
    apply (hGRIND_even 5937475 [1511339; 790956; 25145; 13306; 4643; 2871; 335; 235; 42; 19]
           8675858 ((4, 2) :: (1, 1) :: repeat (1, 2) (beta - 1)) 1);
      closearith. }
  apply (hsteps_trans _ (HC [8675859; 1511339; 790956; 25145; 13306; 4643; 2871; 335; 235; 42; 19] 11874954 1 2
    ((2, 2) :: (1, 1) :: repeat (1, 2) (beta - 1)) 1)).
  { rewrite NUM57a3. rewrite NUM57b.
    replace ((2, 2) :: (1, 1) :: repeat (1, 2) (beta - 1))
      with ((4 - 2, 2) :: (1, 1) :: repeat (1, 2) (beta - 1))
      by sec_eq.
    apply (sTUP2_1 [1511339; 790956; 25145; 13306; 4643; 2871; 335; 235; 42; 19] 8675858
           11874953 4 ((1, 1) :: repeat (1, 2) (beta - 1)) 1); lia. }
  apply (hsteps_trans _ (HB [8675859; 1511339; 790956; 25145; 13306; 4643; 2871; 335; 235; 42; 19] 11874954 1 4
    ((2, 2) :: (1, 1) :: repeat (1, 2) (beta - 1)) 1)).
  { apply (sTDN [8675859; 1511339; 790956; 25145; 13306; 4643; 2871; 335; 235; 42; 19] 11874954
           ((2, 2) :: (1, 1) :: repeat (1, 2) (beta - 1))
           1). }
  apply (hsteps_trans _ (HB [11874955; 8675859; 1511339; 790956; 25145; 13306; 4643; 2871; 335; 235; 42; 19] 5 1 3 (repeat (1, 2) (beta - 1)) 1)).
  { rewrite NUM57e.
    apply (sTRANS2_1 [8675859; 1511339; 790956; 25145; 13306; 4643; 2871; 335; 235; 42; 19]
           11874954 3 1 (repeat (1, 2) (beta - 1)) 1); lia. }
  replace (beta + 4) with (5 + (beta - 1)) by lia.
  apply (CASCADE_POPFIN [11874955; 8675859; 1511339; 790956; 25145; 13306; 4643; 2871; 335; 235; 42; 19] 5 beta); lia.
Qed.

Lemma TOP57_BAND : forall j beta, 4 <= j -> j <= 11874957 -> 2 <= beta ->
  hsteps (HB [1511339; 790956; 25145; 13306; 4643; 2871; 335; 235; 42; 19] 8675859 1 11874955
            ((2 * j, 2) :: (1, 1) :: repeat (1, 2) (beta - 1)) 1)
         (HB [11874955; 8675859; 1511339; 790956; 25145; 13306; 4643; 2871; 335; 235; 42; 19]
            (2 * j + beta - 2) 1 (2 * beta + 1) [] 1).
Proof.
  intros j beta Hj1 Hj2 Hb.
  apply (hsteps_trans _ (HC [1511339; 790956; 25145; 13306; 4643; 2871; 335; 235; 42; 19]
    8675859 11874954 2 ((2 * j - 2, 2) :: (1, 1)
            :: repeat (1, 2) (beta - 1)) 1)).
  { rewrite NUM57h.
    apply (sTUP [1511339; 790956; 25145; 13306; 4643; 2871; 335; 235; 42; 19] 8675859 11874955
           (2 * j) 2 ((1, 1) :: repeat (1, 2) (beta - 1)) 1);
      closearith. }
  apply (hsteps_trans _ (HB [1511339; 790956; 25145; 13306; 4643; 2871; 335; 235; 42; 19]
    8675858 1 (2 * 5937475 + 4) ((2, 2) :: (2 * j - 2, 2) :: (1, 1)
            :: repeat (1, 2) (beta - 1)) 1)).
  { rewrite NUM57a. rewrite NUM57b.
    apply (hGRIND_even 5937475 [1511339; 790956; 25145; 13306; 4643; 2871; 335; 235; 42; 19]
           8675858 ((2 * j - 2, 2) :: (1, 1)
           :: repeat (1, 2) (beta - 1)) 1); closearith. }
  apply (hsteps_trans _ (HC [8675859; 1511339; 790956; 25145; 13306; 4643; 2871; 335; 235; 42; 19] 11874954 1 2 ((2 * j - 4, 2) :: (1, 1)
            :: repeat (1, 2) (beta - 1)) 1)).
  { rewrite NUM57a3. rewrite NUM57b.
    replace ((2 * j - 4, 2) :: (1, 1) :: repeat (1, 2) (beta - 1))
      with ((2 * j - 2 - 2, 2) :: (1, 1)
            :: repeat (1, 2) (beta - 1)) by sec_eq.
    apply (sTUP2_1 [1511339; 790956; 25145; 13306; 4643; 2871; 335; 235; 42; 19] 8675858
           11874953 (2 * j - 2) ((1, 1) :: repeat (1, 2) (beta - 1))
           1); lia. }
  apply (hsteps_trans _ (HB [8675859; 1511339; 790956; 25145; 13306; 4643; 2871; 335; 235; 42; 19] 11874954 1 4 ((2 * j - 4, 2) :: (1, 1)
            :: repeat (1, 2) (beta - 1)) 1)).
  { apply (sTDN [8675859; 1511339; 790956; 25145; 13306; 4643; 2871; 335; 235; 42; 19] 11874954
           ((2 * j - 4, 2) :: (1, 1) :: repeat (1, 2) (beta - 1))
           1). }
  apply (hsteps_trans _ (HC [8675859; 1511339; 790956; 25145; 13306; 4643; 2871; 335; 235; 42; 19] 11874954 3 2 ((2 * j - 6, 2) :: (1, 1)
            :: repeat (1, 2) (beta - 1)) 1)).
  { replace ((2 * j - 6, 2) :: (1, 1) :: repeat (1, 2) (beta - 1))
      with ((2 * j - 4 - 2, 2) :: (1, 1)
            :: repeat (1, 2) (beta - 1)) by sec_eq.
    apply (sTUP [8675859; 1511339; 790956; 25145; 13306; 4643; 2871; 335; 235; 42; 19] 11874954
           4 (2 * j - 4) 2 ((1, 1) :: repeat (1, 2) (beta - 1)) 1);
      lia. }
  apply (hsteps_trans _ (HB [8675859; 1511339; 790956; 25145; 13306; 4643; 2871; 335; 235; 42; 19] 11874954 1 (2 * j - 2)
    ((2, 2) :: (1, 1) :: repeat (1, 2) (beta - 1)) 1)).
  { replace (2 * j - 6) with (2 * (j - 4) + 2) by lia.
    replace (2 * j - 2) with (2 * (j - 4) + 6) by lia.
    apply (CLEANG_even (j - 4) [8675859; 1511339; 790956; 25145; 13306; 4643; 2871; 335; 235; 42; 19] 11874954 ((1, 1) :: repeat (1, 2) (beta - 1))
           1).
    (* the floor (j - 4) + 1 <= 11874954: route via j <= 11874957 *)
    apply Nat.le_trans with (j - 3).
    - lia.
    - rewrite NUM57k.
      apply Nat.sub_le_mono_r. exact Hj2. }
  apply (hsteps_trans _ (HB [11874955; 8675859; 1511339; 790956; 25145; 13306; 4643; 2871; 335; 235; 42; 19] (2 * j - 1) 1 3 (repeat (1, 2) (beta - 1)) 1)).
  { replace (2 * j - 2) with (S (2 * j - 3)) by lia.
    replace (2 * j - 1) with (S (S (2 * j - 3))) by lia.
    rewrite NUM57e.
    apply (sTRANS2_1 [8675859; 1511339; 790956; 25145; 13306; 4643; 2871; 335; 235; 42; 19]
           11874954 (2 * j - 3) 1 (repeat (1, 2) (beta - 1)) 1); lia. }
  replace (2 * j + beta - 2) with (2 * j - 1 + (beta - 1)) by lia.
  apply (CASCADE_POPFIN [11874955; 8675859; 1511339; 790956; 25145; 13306; 4643; 2871; 335; 235; 42; 19] (2 * j - 1) beta); lia.
Qed.

(* ----------------------------------------------------------------- *)
(* TAIL2_END12: the strictly smaller residual core -- the totality  *)
(* of the TOP11 state for r11' = 2 * j, j >= 11874958                *)
(* (r11' >= 23749916), where the GRIND12 pair (r11' - 6, 2) at       *)
(* counter 11874954 takes the DIPDESC boundary a twelfth time.       *)
(* A Definition (lemma parameter), never an axiom.                   *)
(* ----------------------------------------------------------------- *)

Definition TAIL2_END12 : Prop :=
  forall j beta, 11874958 <= j -> 2 <= beta ->
  exists pb A, beta <= A /\
    hsteps (HB [1511339; 790956; 25145; 13306; 4643; 2871; 335; 235; 42; 19] 8675859 1 11874955
              ((2 * j, 2) :: (1, 1) :: repeat (1, 2) (beta - 1)) 1)
           (HB pb A 1 (2 * beta + 1) [] 1).

(* ----------------------------------------------------------------- *)
(* TAIL2_END11_of57: TAIL2_END11, modulo TAIL2_END12.  The j-range  *)
(* splits at r11' = 2 * (j - 5937477): the three small cases and     *)
(* band 11 are proved above; j - 5937477 >= 11874958 is the core.    *)
(* (Numeral hygiene: all S-conversions at these depths are          *)
(* eqb/vm-proved equality rewrites, per the Phase 53-56 pattern.)    *)
(* ----------------------------------------------------------------- *)

Lemma TAIL2_END11_of57 : TAIL2_END12 -> TAIL2_END11.
Proof.
  intros H12 j beta Hj Hb.
  pose proof (TOP57_TO_TOP11 j beta Hj Hb) as Htop.
  destruct (le_lt_dec 11874958 (j - 5937477)) as [Hbig | Hsmall].
  - (* j11 = j - 5937477 >= 11874958: the core *)
    destruct (H12 (j - 5937477) beta Hbig Hb)
      as [pb [A [Ha Hsteps]]].
    exists pb, A. split; [exact Ha |].
    exact (hsteps_trans _ _ _ Htop Hsteps).
  - destruct (le_lt_dec 4 (j - 5937477)) as [Hband | Htiny].
    + (* band 11: j11 = j - 5937477, 4 <= j11 <= 11874957 *)
      exists [11874955; 8675859; 1511339; 790956; 25145; 13306; 4643; 2871; 335; 235; 42; 19],
        (2 * (j - 5937477) + beta - 2).
      split; [lia |].
      assert (Hj2 : j - 5937477 <= 11874957).
      { rewrite NUM57m in Hsmall.
        apply (proj1 (Nat.lt_succ_r _ _) Hsmall). }
      exact (hsteps_trans _ _ _ Htop
               (TOP57_BAND (j - 5937477) beta Hband Hj2 Hb)).
    + (* tiny: j11 = j - 5937477 <= 3; j11 >= 1 since 5937478 <= j *)
      destruct (Nat.eq_dec (j - 5937477) 1) as [He | Hne].
      * (* r11' = 2 *)
        rewrite He in Htop.
        exists [8675860; 1511339; 790956; 25145; 13306; 4643; 2871; 335; 235; 42; 19],
          (11874956 + (beta - 1)).
        split; [rewrite NUM57n; lia |].
        exact (hsteps_trans _ _ _ Htop (TOP57_2 beta Hb)).
      * destruct (Nat.eq_dec (j - 5937477) 2) as [He | Hne'].
        -- (* r11' = 4 *)
           rewrite He in Htop.
           exists [11874955; 8675859; 1511339; 790956; 25145; 13306; 4643; 2871; 335; 235; 42; 19], (beta + 2).
           split; [lia |].
           exact (hsteps_trans _ _ _ Htop (TOP57_4 beta Hb)).
        -- destruct (Nat.eq_dec (j - 5937477) 3) as [He | Hne''].
           ++ (* r11' = 6 *)
              rewrite He in Htop.
              exists [11874955; 8675859; 1511339; 790956; 25145; 13306; 4643; 2871; 335; 235; 42; 19], (beta + 4).
              split; [lia |].
              exact (hsteps_trans _ _ _ Htop (TOP57_6 beta Hb)).
           ++ (* j11 = 0, contradicting 5937478 <= j *)
              exfalso.
              assert (H0 : j - 5937477 = 0) by lia.
              rewrite NUM57p in Hj.
              lia.
Qed.

(* ----------------------------------------------------------------- *)
(* ESC_ERA_LAW_57: the phase-8 ESC era law at every even            *)
(* R >= 1278 (M >= 616), modulo TAIL2_END12 alone.                  *)
(* ----------------------------------------------------------------- *)

Lemma ESC_ERA_LAW_57 : TAIL2_END12 ->
  forall M beta, 616 <= M -> 2 <= beta ->
  exists n c pb a,
    run n (esc_src (2 * M + 52) (beta - 2)) = Some c
    /\ cfg_sim c (rcsec (false :: repeat true (S a) ++ enc pb)
                        (2 * beta + 2) [(1, 2)])
    /\ beta <= a.
Proof.
  intros H M beta HM Hb.
  apply (ESC_ERA_LAW_56 (TAIL2_END11_of57 H) M beta HM Hb).
Qed.

(* ----------------------------------------------------------------- *)
(* Assumption audit                                                  *)
(* ----------------------------------------------------------------- *)

Print Assumptions CASCADE57.
Print Assumptions TOP57_TO_TOP11.
Print Assumptions TOP57_2.
Print Assumptions TOP57_4.
Print Assumptions TOP57_6.
Print Assumptions TOP57_BAND.
Print Assumptions TAIL2_END11_of57.
Print Assumptions ESC_ERA_LAW_57.
