(* ================================================================= *)
(* Phase 58: the TWELFTH descent -- TAIL2_END12 modulo              *)
(* TAIL2_END13.                                                      *)
(*                                                                   *)
(* The TOP11 state (frame [1511339; 790956; 25145; 13306; 4643;     *)
(* 2871; 335; 235; 42; 19], counter 8675859, shuttle 11874955) at    *)
(* pair (2j, 2), j >= 11874958, beta >= 2, is mechanised by the      *)
(* same fixed-parse pattern as Phases 47-57:                         *)
(*                                                                   *)
(*  1. FRONT (identical in shape to the Phase 57 front): TUP,        *)
(*     hGRIND_even 5937475, TUP2_1, TDN, TUP                         *)
(*     -> GRIND12 = HC [8675859; 1511339; 790956; 25145; 13306;      *)
(*        4643; 2871; 335; 235; 42; 19]                              *)
(*        11874954 3 2 ((2j - 6, 2) :: tail(beta)).                  *)
(*  2. DIPGRIND (11874954, r12), r12 = 2j - 23749908 >= 2:           *)
(*     -> HC [8675859; 1511339; ...] 0 3 2 (spine 11874954 ++ W),    *)
(*        W = ((r12, 2) :: (1, 1) :: (1, 2)^(beta-1)).               *)
(*  3. CASCADE58: a FIXED parse of 490 lemma steps from the spine    *)
(*     to TOP12 (hsim58: the 498-step classified chain at            *)
(*     (11874958, 2) reaches the era landing, and the cascade's      *)
(*     label sequence and abstracted targets are identical at        *)
(*     beta = 3; the classifier was first validated by exact         *)
(*     reproduction of the Phase 57 classified chain, 25 steps,      *)
(*     0 mismatches).  After CASCADE57's 17 steps, the twelfth       *)
(*     descent is LONG again (the CASCADE56 pattern): 110 TUP,       *)
(*     71 TDN, 68 pop12, 47 DIPGRIND, 37 TUP2_1, 31 hGRIND_even,     *)
(*     28 PUSH, 20 PX2A, 20 POP, 10 CLEANG_odd, 10 TRANS2_1,         *)
(*     10 PUSHX, 8 CLEANG_even, 7 PX2Bgen, 6 PX2B0, 5 PX2A0,         *)
(*     2 TRANS2_2.  The frame GROWS from ten blocks to eleven:       *)
(*                                                                   *)
(*       TOP12 = HB [1523948; 426279; 308525; 58213; 30332; 931;     *)
(*                   608; 77; 35; 20; 0]                             *)
(*               14897638 1 29403093 W.                              *)
(*                                                                   *)
(*  4. TOP12 closings by r12' = 2 * j12, j12 = j - 11874957:         *)
(*    r12' = 2:       TRANS2_1 + CASCADE_POPFIN, A = 29403093 + beta,*)
(*                    frame [14897639; 1523948; 426279; ...];        *)
(*    r12' = 4:       TUP + hGRIND_even 14701544 + TRANS2_2          *)
(*                    + CASCADE_POPFIN, A = beta + 2;                *)
(*    r12' = 6:       TUP + hGRIND_even 14701544 + TUP2_1 + TDN      *)
(*                    + TRANS2_1 + CASCADE_POPFIN, A = beta + 4;     *)
(*    8 <= r12' <= 58806190 (band 12): TUP + hGRIND_even 14701544    *)
(*      + TUP2_1 + TDN + TUP onto GRIND13 = HC [14897638; 1523948;   *)
(*      ...] 29403092 3 2 ((r12' - 6, 2) :: tail), whose pair        *)
(*      grinds CLEANLY by CLEANG_even (floor (r12' - 8)/2 + 1 <=     *)
(*      29403092, exactly r12' <= 58806190), then TRANS2_1 +         *)
(*      CASCADE_POPFIN, A = r12' + beta - 2, frame [29403093;       *)
(*      14897638; 1523948; ...].  (The band counter is again the     *)
(*      shuttle moved into the counter slot by TUP2_1: 29403092,     *)
(*      not 14897638.)                                               *)
(*                                                                   *)
(*  For r12' >= 58806192 (j12 >= 29403096, i.e. TOP11-parameter      *)
(*  j >= 41278053) the pair (r12' - 6, 2) at counter 29403092        *)
(*  exceeds the CLEANG_even floor and the rounds take the DIPDESC    *)
(*  boundary a THIRTEENTH time (hsim58 Part 3: the GRIND13 state     *)
(*  and the DIPGRIND (29403092, r12' - 58806190) landing both occur  *)
(*  at j12 = 29403096, 29403097, 30000000).  The thirteenth descent  *)
(*  is expected to be a NEW cascade with different constants, so no  *)
(*  cycle induction in the current vocabulary closes it; what        *)
(*  remains is the strictly smaller core                             *)
(*                                                                   *)
(*    TAIL2_END13: the totality of the ONE pair (2j, 2) at the ONE   *)
(*    fixed TOP12 state HB [1523948; 426279; 308525; 58213; 30332;  *)
(*    931; 608; 77; 35; 20; 0] 14897638 1 29403093, for              *)
(*    j >= 29403096 (r12' = 2j >= 58806192), beta >= 2.              *)
(*                                                                   *)
(*  The core's range shrank from [11874958, infty) to [41278053,     *)
(*  infty) in TOP11 parameters; the band width roughly doubled       *)
(*  again (11874958 -> 41278052).  Via TAIL2_END12_of58 +             *)
(*  TAIL2_END11_of57 + ESC_ERA_LAW_57 the ESC instances at every     *)
(*  even R >= 1278 now rest on TAIL2_END13 alone                     *)
(*  (ESC_ERA_LAW_58 below; Loop.v Part 4s).                          *)
(* ================================================================= *)

Require Import List Bool Arith Lia ZArith.
Import ListNotations.
Require Import TM Sections Mirror TokenPass Recoord Era Esc Dev
               Grind Grind2 Grind3 Grind4 Grind5 Grind6 Grind7 Grind8
               Grind9 Grind10 Grind11 Grind12 Grind13 Grind14 Grind15
               Grind16 Grind17 Grind18 Grind19 Grind20 Grind21 Grind22
               Grind23 Grind24 Grind25.

(* Section equality: componentwise, arithmetic leaves by lia.      *)
Ltac sec_eq :=
  repeat (first [ solve [reflexivity] | solve [lia] | f_equal ]).

(* Closed-numeral arithmetic: literals >= 7426 are parsed as       *)
(* Nat.of_num_uint atoms, which lia cannot relate to variables;    *)
(* for purely closed <= goals the boolean check decides them.      *)
Ltac closearith :=
  first [ lia | apply Nat.leb_le; reflexivity ].

(* Numeral identities for the TOP12 closings and the               *)
(* TAIL2_END12_of58 case split, factored into standalone lemmas    *)
(* proved by Nat.eqb_eq + vm_compute (the Phase 52-57 pattern).    *)
(* The TOP12 front reuses Grind25's NUM57h / NUM57a / NUM57b /     *)
(* NUM57i verbatim (same constants).                               *)
(* hGRIND_even 14701544 in the TOP12 closings:                      *)
Lemma NUM58a : 29403092 = 2 * 14701544 + 4.
Proof. apply Nat.eqb_eq; vm_compute; reflexivity. Qed.
Lemma NUM58b : 14897638 = S 14897637.
Proof. apply Nat.eqb_eq; vm_compute; reflexivity. Qed.
(* The r12' = 2 closing (TRANS2_1 at TOP12):                        *)
Lemma NUM58e : 29403093 = S 29403092.
Proof. apply Nat.eqb_eq; vm_compute; reflexivity. Qed.
Lemma NUM58f : 29403094 = S (S 29403092).
Proof. apply Nat.eqb_eq; vm_compute; reflexivity. Qed.
Lemma NUM58g : 14897639 = S 14897638.
Proof. apply Nat.eqb_eq; vm_compute; reflexivity. Qed.
(* The r12' = 4 / 6 / band first TUP (shuttle form):                *)
Lemma NUM58h : 29403092 = 29403093 - 1.
Proof. apply Nat.eqb_eq; vm_compute; reflexivity. Qed.
(* The r12' = 4 TRANS2_2 step and the TUP2_1 steps:                 *)
Lemma NUM58i : 29403092 = S 29403091.
Proof. apply Nat.eqb_eq; vm_compute; reflexivity. Qed.
Lemma NUM58j : 29403093 = S (S 29403091).
Proof. apply Nat.eqb_eq; vm_compute; reflexivity. Qed.
(* The band CLEANG_even floor:                                      *)
Lemma NUM58k : 29403092 = 29403095 - 3.
Proof. apply Nat.eqb_eq; vm_compute; reflexivity. Qed.
(* The TAIL2_END12_of58 case split:                                 *)
Lemma NUM58m : 29403096 = S 29403095.
Proof. apply Nat.eqb_eq; vm_compute; reflexivity. Qed.
Lemma NUM58n : 29403094 = S 29403093.
Proof. apply Nat.eqb_eq; vm_compute; reflexivity. Qed.
Lemma NUM58p : 11874958 = S 11874957.
Proof. apply Nat.eqb_eq; vm_compute; reflexivity. Qed.

(* Factored list identities for the three PX2A steps of     *)
(* CASCADE58 whose produced (1, 2)s merge into a spine      *)
(* repeat of length > 175000 (cascade steps 1, 6, 360):     *)
(* the goal's stated target is first rewritten to the       *)
(* constructor's unmerged form via REP58a-c (whose proofs   *)
(* rewrite the run length to S-form and close by            *)
(* reflexivity), and the frame atoms are put in S-form via  *)
(* NUM58ta1-3 / tb1-3 / tc1-3, since hPX2A's frame pattern   *)
(* is S (S (S b')) :: S p' :: pb and its target counter is  *)
(* S b' (the CASCADE55 step-1 pattern, generalised).       *)
Lemma NUM58ssa : 11874956 = S (S 11874954).
Proof. apply Nat.eqb_eq; vm_compute; reflexivity. Qed.
Lemma REP58a : forall w,
  (1, 1) :: (1, 2) :: (1, 2) :: repeat (1, 2) 11874954 ++ w
  = (1, 1) :: repeat (1, 2) 11874956 ++ w.
Proof. intro w. rewrite NUM58ssa. reflexivity. Qed.
Lemma NUM58ta1 : 8675859 = S (S (S 8675856)).
Proof. apply Nat.eqb_eq; vm_compute; reflexivity. Qed.
Lemma NUM58ta2 : 1511339 = S 1511338.
Proof. apply Nat.eqb_eq; vm_compute; reflexivity. Qed.
Lemma NUM58ta3 : 8675857 = S 8675856.
Proof. apply Nat.eqb_eq; vm_compute; reflexivity. Qed.
Lemma NUM58ssb : 1511339 = S (S 1511337).
Proof. apply Nat.eqb_eq; vm_compute; reflexivity. Qed.
Lemma REP58b : forall w,
  (1, 1) :: (1, 2) :: (1, 2) :: repeat (1, 2) 1511337 ++ w
  = (1, 1) :: repeat (1, 2) 1511339 ++ w.
Proof. intro w. rewrite NUM58ssb. reflexivity. Qed.
Lemma NUM58tb1 : 790956 = S (S (S 790953)).
Proof. apply Nat.eqb_eq; vm_compute; reflexivity. Qed.
Lemma NUM58tb2 : 25145 = S 25144.
Proof. apply Nat.eqb_eq; vm_compute; reflexivity. Qed.
Lemma NUM58tb3 : 790954 = S 790953.
Proof. apply Nat.eqb_eq; vm_compute; reflexivity. Qed.
Lemma NUM58ssc : 213138 = S (S 213136).
Proof. apply Nat.eqb_eq; vm_compute; reflexivity. Qed.
Lemma REP58c : forall w,
  (1, 1) :: (1, 2) :: (1, 2) :: repeat (1, 2) 213136 ++ w
  = (1, 1) :: repeat (1, 2) 213138 ++ w.
Proof. intro w. rewrite NUM58ssc. reflexivity. Qed.
Lemma NUM58tc1 : 153600 = S (S (S 153597)).
Proof. apply Nat.eqb_eq; vm_compute; reflexivity. Qed.
Lemma NUM58tc2 : 29105 = S 29104.
Proof. apply Nat.eqb_eq; vm_compute; reflexivity. Qed.
Lemma NUM58tc3 : 153598 = S 153597.
Proof. apply Nat.eqb_eq; vm_compute; reflexivity. Qed.

(* Closed arithmetic identities for the large DIPGRIND /   *)
(* hGRIND_even / CLEANG steps and the head-pair             *)
(* normalisations of CASCADE57, factored into standalone    *)
(* lemmas (eqb/vm proofs) and rewritten in the step blocks, *)
(* so the applies meet the lemmas' arithmetic forms        *)
(* syntactically instead of by a closed multiplication or   *)
(* subtraction conversion at depth >= 100000                *)
(* (cf. NUM58ss / REP58a-c).                                *)
Lemma NUM58X1 : 1511338 = S 1511337.
Proof. apply Nat.eqb_eq; vm_compute; reflexivity. Qed.
Lemma NUM58X2 : 8675855 = 8675857 - 2.
Proof. apply Nat.eqb_eq; vm_compute; reflexivity. Qed.
Lemma NUM58X3 : 8675853 = 8675855 - 2.
Proof. apply Nat.eqb_eq; vm_compute; reflexivity. Qed.
Lemma NUM58X4 : 8675853 = 2 * 1511337 + 5653179.
Proof. apply Nat.eqb_eq; vm_compute; reflexivity. Qed.
Lemma NUM58X5 : 790952 = 790954 - 2.
Proof. apply Nat.eqb_eq; vm_compute; reflexivity. Qed.
Lemma NUM58X6 : 790950 = 790952 - 2.
Proof. apply Nat.eqb_eq; vm_compute; reflexivity. Qed.
Lemma NUM58X7 : 790950 = 2 * 25143 + 740664.
Proof. apply Nat.eqb_eq; vm_compute; reflexivity. Qed.
Lemma NUM58X8 : 740662 = 740664 - 2.
Proof. apply Nat.eqb_eq; vm_compute; reflexivity. Qed.
Lemma NUM58X9 : 50292 = 2 * 25144 + 4.
Proof. apply Nat.eqb_eq; vm_compute; reflexivity. Qed.
Lemma NUM58X10 : 740660 = 740662 - 2.
Proof. apply Nat.eqb_eq; vm_compute; reflexivity. Qed.
Lemma NUM58X11 : 740658 = 740660 - 2.
Proof. apply Nat.eqb_eq; vm_compute; reflexivity. Qed.
Lemma NUM58X12 : 740658 = 2 * 50292 + 640074.
Proof. apply Nat.eqb_eq; vm_compute; reflexivity. Qed.
Lemma NUM58X13 : 100590 = 100591 - 1.
Proof. apply Nat.eqb_eq; vm_compute; reflexivity. Qed.
Lemma NUM58X14 : 640072 = 640074 - 2.
Proof. apply Nat.eqb_eq; vm_compute; reflexivity. Qed.
Lemma NUM58X15 : 100590 = 2 * 50293 + 4.
Proof. apply Nat.eqb_eq; vm_compute; reflexivity. Qed.
Lemma NUM58X16 : 100590 = S 100589.
Proof. apply Nat.eqb_eq; vm_compute; reflexivity. Qed.
Lemma NUM58X17 : 640070 = 640072 - 2.
Proof. apply Nat.eqb_eq; vm_compute; reflexivity. Qed.
Lemma NUM58X18 : 640068 = 640070 - 2.
Proof. apply Nat.eqb_eq; vm_compute; reflexivity. Qed.
Lemma NUM58X19 : 640068 = 2 * 100590 + 438888.
Proof. apply Nat.eqb_eq; vm_compute; reflexivity. Qed.
Lemma NUM58X20 : 53006 = 2 * 26501 + 4.
Proof. apply Nat.eqb_eq; vm_compute; reflexivity. Qed.
Lemma NUM58X21 : 213136 = 213137 - 1.
Proof. apply Nat.eqb_eq; vm_compute; reflexivity. Qed.
Lemma NUM58X22 : 438886 = 438888 - 2.
Proof. apply Nat.eqb_eq; vm_compute; reflexivity. Qed.
Lemma NUM58X23 : 213136 = 2 * 106566 + 4.
Proof. apply Nat.eqb_eq; vm_compute; reflexivity. Qed.
Lemma NUM58X24 : 213136 = S 213135.
Proof. apply Nat.eqb_eq; vm_compute; reflexivity. Qed.
Lemma NUM58X25 : 153600 = S 153599.
Proof. apply Nat.eqb_eq; vm_compute; reflexivity. Qed.
Lemma NUM58X26 : 438884 = 438886 - 2.
Proof. apply Nat.eqb_eq; vm_compute; reflexivity. Qed.
Lemma NUM58X27 : 438882 = 438884 - 2.
Proof. apply Nat.eqb_eq; vm_compute; reflexivity. Qed.
Lemma NUM58X28 : 438882 = 2 * 213136 + 12610.
Proof. apply Nat.eqb_eq; vm_compute; reflexivity. Qed.
Lemma NUM58X29 : 153594 = 2 * 29103 + 95388.
Proof. apply Nat.eqb_eq; vm_compute; reflexivity. Qed.
Lemma NUM58X30 : 58212 = 2 * 29104 + 4.
Proof. apply Nat.eqb_eq; vm_compute; reflexivity. Qed.
Lemma NUM58X31 : 95382 = 2 * 47690 + 2.
Proof. apply Nat.eqb_eq; vm_compute; reflexivity. Qed.
Lemma NUM58X32 : 95386 = 2 * 47690 + 6.
Proof. apply Nat.eqb_eq; vm_compute; reflexivity. Qed.
Lemma NUM58X33 : 426278 = 426279 - 1.
Proof. apply Nat.eqb_eq; vm_compute; reflexivity. Qed.
Lemma NUM58X34 : 426278 = 2 * 213137 + 4.
Proof. apply Nat.eqb_eq; vm_compute; reflexivity. Qed.
Lemma NUM58X35 : 426278 = S 426277.
Proof. apply Nat.eqb_eq; vm_compute; reflexivity. Qed.
Lemma NUM58X36 : 308525 = S 308524.
Proof. apply Nat.eqb_eq; vm_compute; reflexivity. Qed.
Lemma NUM58X37 : 426279 = S 426278.
Proof. apply Nat.eqb_eq; vm_compute; reflexivity. Qed.
Lemma NUM58X38 : 3022680 = 3022681 - 1.
Proof. apply Nat.eqb_eq; vm_compute; reflexivity. Qed.
Lemma NUM58X39 : 5653177 = 5653179 - 2.
Proof. apply Nat.eqb_eq; vm_compute; reflexivity. Qed.
Lemma NUM58X40 : 3022680 = 2 * 1511338 + 4.
Proof. apply Nat.eqb_eq; vm_compute; reflexivity. Qed.
Lemma NUM58X41 : 3022680 = S 3022679.
Proof. apply Nat.eqb_eq; vm_compute; reflexivity. Qed.
Lemma NUM58X42 : 1523948 = S 1523947.
Proof. apply Nat.eqb_eq; vm_compute; reflexivity. Qed.
Lemma NUM58X43 : 5653175 = 5653177 - 2.
Proof. apply Nat.eqb_eq; vm_compute; reflexivity. Qed.
Lemma NUM58X44 : 5653173 = 5653175 - 2.
Proof. apply Nat.eqb_eq; vm_compute; reflexivity. Qed.
Lemma NUM58X45 : 5653173 = 2 * 2826585 + 3.
Proof. apply Nat.eqb_eq; vm_compute; reflexivity. Qed.
Lemma NUM58X46 : 5653178 = 2 * 2826585 + 8.
Proof. apply Nat.eqb_eq; vm_compute; reflexivity. Qed.
Lemma NUM58X47 : 3022682 = S 3022681.
Proof. apply Nat.eqb_eq; vm_compute; reflexivity. Qed.
Lemma NUM58X48 : 5653181 = 5653180 + 1.
Proof. apply Nat.eqb_eq; vm_compute; reflexivity. Qed.

(* CASCADE58a: steps 1-56 of the CASCADE58 chain. *)
Lemma CASCADE58a : forall w,
  hsteps (HC [8675859; 1511339; 790956; 25145; 13306; 4643; 2871; 335; 235; 42; 19] 0 3 2 (repeat (1, 2) 11874954 ++ w) 1)
         (HC [427; 57; 5] 820 1 2 ((2195, 2) :: (1, 1) :: repeat (1, 2) 4643 ++ (4018, 2) :: (1, 1) :: repeat (1, 2) 25145 ++ (740664, 2) :: (1, 1) :: repeat (1, 2) 1511339 ++ (5653179, 2) :: (1, 1) :: repeat (1, 2) 11874956 ++ w) 1).
Proof.
  intro w.
  (* step 1: P PX2A *)
  apply (hsteps_trans _ (HC [790956; 25145; 13306; 4643; 2871; 335; 235; 42; 19] 1511338 8675857 2 ((1, 1) :: repeat (1, 2) 11874956 ++ w) 1)).
  {
    rewrite NUM58ta1. rewrite NUM58ta2. rewrite NUM58ta3.
    replace ((1, 1) :: repeat (1, 2) 11874956 ++ w)
      with ((1, 1) :: (1, 2) :: (1, 2) :: repeat (1, 2) 11874954 ++ w)
      by (apply REP58a).
    exact (hsteps_step _ _ _ (hPX2A 8675856 1511338 [790956; 25145; 13306; 4643; 2871; 335; 235; 42; 19] (repeat (1, 2) 11874954 ++ w) 1) (hsteps_refl _)).
  }
  (* step 2: P PUSH *)
  apply (hsteps_trans _ (HC [790956; 25145; 13306; 4643; 2871; 335; 235; 42; 19] 1511337 1 2 ((8675855, 2) :: (1, 1) :: repeat (1, 2) 11874956 ++ w) 1)).
  {
    rewrite NUM58X1.
    rewrite NUM58X2.
    apply (sPUSH [790956; 25145; 13306; 4643; 2871; 335; 235; 42; 19] 1511337 8675857 ((1, 1) :: repeat (1, 2) 11874956 ++ w) 1); closearith.
  }
  (* step 3: P TDN *)
  apply (hsteps_trans _ (HB [790956; 25145; 13306; 4643; 2871; 335; 235; 42; 19] 1511337 1 4 ((8675855, 2) :: (1, 1) :: repeat (1, 2) 11874956 ++ w) 1)).
  {
    apply (sTDN [790956; 25145; 13306; 4643; 2871; 335; 235; 42; 19] 1511337 ((8675855, 2) :: (1, 1) :: repeat (1, 2) 11874956 ++ w) 1).
  }
  (* step 4: sTUP *)
  apply (hsteps_trans _ (HC [790956; 25145; 13306; 4643; 2871; 335; 235; 42; 19] 1511337 3 2 ((8675853, 2) :: (1, 1) :: repeat (1, 2) 11874956 ++ w) 1)).
  {
    rewrite NUM58X3.
    apply (sTUP [790956; 25145; 13306; 4643; 2871; 335; 235; 42; 19] 1511337 4 8675855 2 ((1, 1) :: repeat (1, 2) 11874956 ++ w) 1); closearith.
  }
  (* step 5: DIPGRIND 1511337 5653179 *)
  apply (hsteps_trans _ (HC [790956; 25145; 13306; 4643; 2871; 335; 235; 42; 19] 0 3 2 (repeat (1, 2) 1511337 ++ (5653179, 2) :: (1, 1) :: repeat (1, 2) 11874956 ++ w) 1)).
  {
    rewrite NUM58X4.
    apply (DIPGRIND 1511337 5653179 [790956; 25145; 13306; 4643; 2871; 335; 235; 42; 19] ((1, 1) :: repeat (1, 2) 11874956 ++ w) 1); closearith.
  }
  (* step 6: P PX2A *)
  apply (hsteps_trans _ (HC [13306; 4643; 2871; 335; 235; 42; 19] 25144 790954 2 ((1, 1) :: repeat (1, 2) 1511339 ++ (5653179, 2) :: (1, 1) :: repeat (1, 2) 11874956 ++ w) 1)).
  {
    rewrite NUM58tb1. rewrite NUM58tb2. rewrite NUM58tb3.
    replace ((1, 1) :: repeat (1, 2) 1511339 ++ (5653179, 2) :: (1, 1) :: repeat (1, 2) 11874956 ++ w)
      with ((1, 1) :: (1, 2) :: (1, 2) :: repeat (1, 2) 1511337 ++ (5653179, 2) :: (1, 1) :: repeat (1, 2) 11874956 ++ w)
      by (apply REP58b).
    exact (hsteps_step _ _ _ (hPX2A 790953 25144 [13306; 4643; 2871; 335; 235; 42; 19] (repeat (1, 2) 1511337 ++ (5653179, 2) :: (1, 1) :: repeat (1, 2) 11874956 ++ w) 1) (hsteps_refl _)).
  }
  (* step 7: P PUSH *)
  apply (hsteps_trans _ (HC [13306; 4643; 2871; 335; 235; 42; 19] 25143 1 2 ((790952, 2) :: (1, 1) :: repeat (1, 2) 1511339 ++ (5653179, 2) :: (1, 1) :: repeat (1, 2) 11874956 ++ w) 1)).
  {
    rewrite NUM58X5.
    apply (sPUSH [13306; 4643; 2871; 335; 235; 42; 19] 25143 790954 ((1, 1) :: repeat (1, 2) 1511339 ++ (5653179, 2) :: (1, 1) :: repeat (1, 2) 11874956 ++ w) 1); closearith.
  }
  (* step 8: P TDN *)
  apply (hsteps_trans _ (HB [13306; 4643; 2871; 335; 235; 42; 19] 25143 1 4 ((790952, 2) :: (1, 1) :: repeat (1, 2) 1511339 ++ (5653179, 2) :: (1, 1) :: repeat (1, 2) 11874956 ++ w) 1)).
  {
    apply (sTDN [13306; 4643; 2871; 335; 235; 42; 19] 25143 ((790952, 2) :: (1, 1) :: repeat (1, 2) 1511339 ++ (5653179, 2) :: (1, 1) :: repeat (1, 2) 11874956 ++ w) 1).
  }
  (* step 9: sTUP *)
  apply (hsteps_trans _ (HC [13306; 4643; 2871; 335; 235; 42; 19] 25143 3 2 ((790950, 2) :: (1, 1) :: repeat (1, 2) 1511339 ++ (5653179, 2) :: (1, 1) :: repeat (1, 2) 11874956 ++ w) 1)).
  {
    rewrite NUM58X6.
    apply (sTUP [13306; 4643; 2871; 335; 235; 42; 19] 25143 4 790952 2 ((1, 1) :: repeat (1, 2) 1511339 ++ (5653179, 2) :: (1, 1) :: repeat (1, 2) 11874956 ++ w) 1); closearith.
  }
  (* step 10: DIPGRIND 25143 740664 *)
  apply (hsteps_trans _ (HC [13306; 4643; 2871; 335; 235; 42; 19] 0 3 2 (repeat (1, 2) 25143 ++ (740664, 2) :: (1, 1) :: repeat (1, 2) 1511339 ++ (5653179, 2) :: (1, 1) :: repeat (1, 2) 11874956 ++ w) 1)).
  {
    rewrite NUM58X7.
    apply (DIPGRIND 25143 740664 [13306; 4643; 2871; 335; 235; 42; 19] ((1, 1) :: repeat (1, 2) 1511339 ++ (5653179, 2) :: (1, 1) :: repeat (1, 2) 11874956 ++ w) 1); closearith.
  }
  (* step 11: P PX2A *)
  apply (hsteps_trans _ (HC [2871; 335; 235; 42; 19] 4642 13304 2 ((1, 1) :: repeat (1, 2) 25145 ++ (740664, 2) :: (1, 1) :: repeat (1, 2) 1511339 ++ (5653179, 2) :: (1, 1) :: repeat (1, 2) 11874956 ++ w) 1)).
  {
    exact (hsteps_step _ _ _ (hPX2A 13303 4642 [2871; 335; 235; 42; 19] (repeat (1, 2) 25143 ++ (740664, 2) :: (1, 1) :: repeat (1, 2) 1511339 ++ (5653179, 2) :: (1, 1) :: repeat (1, 2) 11874956 ++ w) 1) (hsteps_refl _)).
  }
  (* step 12: P PUSH *)
  apply (hsteps_trans _ (HC [2871; 335; 235; 42; 19] 4641 1 2 ((13302, 2) :: (1, 1) :: repeat (1, 2) 25145 ++ (740664, 2) :: (1, 1) :: repeat (1, 2) 1511339 ++ (5653179, 2) :: (1, 1) :: repeat (1, 2) 11874956 ++ w) 1)).
  {
    replace ((13302, 2) :: (1, 1) :: repeat (1, 2) 25145 ++ (740664, 2) :: (1, 1) :: repeat (1, 2) 1511339 ++ (5653179, 2) :: (1, 1) :: repeat (1, 2) 11874956 ++ w) with ((13304 - 2, 2) :: (1, 1) :: repeat (1, 2) 25145 ++ (740664, 2) :: (1, 1) :: repeat (1, 2) 1511339 ++ (5653179, 2) :: (1, 1) :: repeat (1, 2) 11874956 ++ w) by sec_eq.
    apply (sPUSH [2871; 335; 235; 42; 19] 4641 13304 ((1, 1) :: repeat (1, 2) 25145 ++ (740664, 2) :: (1, 1) :: repeat (1, 2) 1511339 ++ (5653179, 2) :: (1, 1) :: repeat (1, 2) 11874956 ++ w) 1); closearith.
  }
  (* step 13: P TDN *)
  apply (hsteps_trans _ (HB [2871; 335; 235; 42; 19] 4641 1 4 ((13302, 2) :: (1, 1) :: repeat (1, 2) 25145 ++ (740664, 2) :: (1, 1) :: repeat (1, 2) 1511339 ++ (5653179, 2) :: (1, 1) :: repeat (1, 2) 11874956 ++ w) 1)).
  {
    apply (sTDN [2871; 335; 235; 42; 19] 4641 ((13302, 2) :: (1, 1) :: repeat (1, 2) 25145 ++ (740664, 2) :: (1, 1) :: repeat (1, 2) 1511339 ++ (5653179, 2) :: (1, 1) :: repeat (1, 2) 11874956 ++ w) 1).
  }
  (* step 14: sTUP *)
  apply (hsteps_trans _ (HC [2871; 335; 235; 42; 19] 4641 3 2 ((13300, 2) :: (1, 1) :: repeat (1, 2) 25145 ++ (740664, 2) :: (1, 1) :: repeat (1, 2) 1511339 ++ (5653179, 2) :: (1, 1) :: repeat (1, 2) 11874956 ++ w) 1)).
  {
    replace ((13300, 2) :: (1, 1) :: repeat (1, 2) 25145 ++ (740664, 2) :: (1, 1) :: repeat (1, 2) 1511339 ++ (5653179, 2) :: (1, 1) :: repeat (1, 2) 11874956 ++ w) with ((13302 - 2, 2) :: (1, 1) :: repeat (1, 2) 25145 ++ (740664, 2) :: (1, 1) :: repeat (1, 2) 1511339 ++ (5653179, 2) :: (1, 1) :: repeat (1, 2) 11874956 ++ w) by sec_eq.
    apply (sTUP [2871; 335; 235; 42; 19] 4641 4 13302 2 ((1, 1) :: repeat (1, 2) 25145 ++ (740664, 2) :: (1, 1) :: repeat (1, 2) 1511339 ++ (5653179, 2) :: (1, 1) :: repeat (1, 2) 11874956 ++ w) 1); closearith.
  }
  (* step 15: DIPGRIND 4641 4018 *)
  apply (hsteps_trans _ (HC [2871; 335; 235; 42; 19] 0 3 2 (repeat (1, 2) 4641 ++ (4018, 2) :: (1, 1) :: repeat (1, 2) 25145 ++ (740664, 2) :: (1, 1) :: repeat (1, 2) 1511339 ++ (5653179, 2) :: (1, 1) :: repeat (1, 2) 11874956 ++ w) 1)).
  {
    apply (DIPGRIND 4641 4018 [2871; 335; 235; 42; 19] ((1, 1) :: repeat (1, 2) 25145 ++ (740664, 2) :: (1, 1) :: repeat (1, 2) 1511339 ++ (5653179, 2) :: (1, 1) :: repeat (1, 2) 11874956 ++ w) 1); closearith.
  }
  (* step 16: P PX2A *)
  apply (hsteps_trans _ (HC [235; 42; 19] 334 2869 2 ((1, 1) :: repeat (1, 2) 4643 ++ (4018, 2) :: (1, 1) :: repeat (1, 2) 25145 ++ (740664, 2) :: (1, 1) :: repeat (1, 2) 1511339 ++ (5653179, 2) :: (1, 1) :: repeat (1, 2) 11874956 ++ w) 1)).
  {
    exact (hsteps_step _ _ _ (hPX2A 2868 334 [235; 42; 19] (repeat (1, 2) 4641 ++ (4018, 2) :: (1, 1) :: repeat (1, 2) 25145 ++ (740664, 2) :: (1, 1) :: repeat (1, 2) 1511339 ++ (5653179, 2) :: (1, 1) :: repeat (1, 2) 11874956 ++ w) 1) (hsteps_refl _)).
  }
  (* step 17: P PUSH *)
  apply (hsteps_trans _ (HC [235; 42; 19] 333 1 2 ((2867, 2) :: (1, 1) :: repeat (1, 2) 4643 ++ (4018, 2) :: (1, 1) :: repeat (1, 2) 25145 ++ (740664, 2) :: (1, 1) :: repeat (1, 2) 1511339 ++ (5653179, 2) :: (1, 1) :: repeat (1, 2) 11874956 ++ w) 1)).
  {
    replace ((2867, 2) :: (1, 1) :: repeat (1, 2) 4643 ++ (4018, 2) :: (1, 1) :: repeat (1, 2) 25145 ++ (740664, 2) :: (1, 1) :: repeat (1, 2) 1511339 ++ (5653179, 2) :: (1, 1) :: repeat (1, 2) 11874956 ++ w) with ((2869 - 2, 2) :: (1, 1) :: repeat (1, 2) 4643 ++ (4018, 2) :: (1, 1) :: repeat (1, 2) 25145 ++ (740664, 2) :: (1, 1) :: repeat (1, 2) 1511339 ++ (5653179, 2) :: (1, 1) :: repeat (1, 2) 11874956 ++ w) by sec_eq.
    apply (sPUSH [235; 42; 19] 333 2869 ((1, 1) :: repeat (1, 2) 4643 ++ (4018, 2) :: (1, 1) :: repeat (1, 2) 25145 ++ (740664, 2) :: (1, 1) :: repeat (1, 2) 1511339 ++ (5653179, 2) :: (1, 1) :: repeat (1, 2) 11874956 ++ w) 1); closearith.
  }
  (* step 18: P TDN *)
  apply (hsteps_trans _ (HB [235; 42; 19] 333 1 4 ((2867, 2) :: (1, 1) :: repeat (1, 2) 4643 ++ (4018, 2) :: (1, 1) :: repeat (1, 2) 25145 ++ (740664, 2) :: (1, 1) :: repeat (1, 2) 1511339 ++ (5653179, 2) :: (1, 1) :: repeat (1, 2) 11874956 ++ w) 1)).
  {
    apply (sTDN [235; 42; 19] 333 ((2867, 2) :: (1, 1) :: repeat (1, 2) 4643 ++ (4018, 2) :: (1, 1) :: repeat (1, 2) 25145 ++ (740664, 2) :: (1, 1) :: repeat (1, 2) 1511339 ++ (5653179, 2) :: (1, 1) :: repeat (1, 2) 11874956 ++ w) 1).
  }
  (* step 19: sTUP *)
  apply (hsteps_trans _ (HC [235; 42; 19] 333 3 2 ((2865, 2) :: (1, 1) :: repeat (1, 2) 4643 ++ (4018, 2) :: (1, 1) :: repeat (1, 2) 25145 ++ (740664, 2) :: (1, 1) :: repeat (1, 2) 1511339 ++ (5653179, 2) :: (1, 1) :: repeat (1, 2) 11874956 ++ w) 1)).
  {
    replace ((2865, 2) :: (1, 1) :: repeat (1, 2) 4643 ++ (4018, 2) :: (1, 1) :: repeat (1, 2) 25145 ++ (740664, 2) :: (1, 1) :: repeat (1, 2) 1511339 ++ (5653179, 2) :: (1, 1) :: repeat (1, 2) 11874956 ++ w) with ((2867 - 2, 2) :: (1, 1) :: repeat (1, 2) 4643 ++ (4018, 2) :: (1, 1) :: repeat (1, 2) 25145 ++ (740664, 2) :: (1, 1) :: repeat (1, 2) 1511339 ++ (5653179, 2) :: (1, 1) :: repeat (1, 2) 11874956 ++ w) by sec_eq.
    apply (sTUP [235; 42; 19] 333 4 2867 2 ((1, 1) :: repeat (1, 2) 4643 ++ (4018, 2) :: (1, 1) :: repeat (1, 2) 25145 ++ (740664, 2) :: (1, 1) :: repeat (1, 2) 1511339 ++ (5653179, 2) :: (1, 1) :: repeat (1, 2) 11874956 ++ w) 1); closearith.
  }
  (* step 20: DIPGRIND 333 2199 *)
  apply (hsteps_trans _ (HC [235; 42; 19] 0 3 2 (repeat (1, 2) 333 ++ (2199, 2) :: (1, 1) :: repeat (1, 2) 4643 ++ (4018, 2) :: (1, 1) :: repeat (1, 2) 25145 ++ (740664, 2) :: (1, 1) :: repeat (1, 2) 1511339 ++ (5653179, 2) :: (1, 1) :: repeat (1, 2) 11874956 ++ w) 1)).
  {
    apply (DIPGRIND 333 2199 [235; 42; 19] ((1, 1) :: repeat (1, 2) 4643 ++ (4018, 2) :: (1, 1) :: repeat (1, 2) 25145 ++ (740664, 2) :: (1, 1) :: repeat (1, 2) 1511339 ++ (5653179, 2) :: (1, 1) :: repeat (1, 2) 11874956 ++ w) 1); closearith.
  }
  (* step 21: P PX2A *)
  apply (hsteps_trans _ (HC [19] 41 233 2 ((1, 1) :: repeat (1, 2) 335 ++ (2199, 2) :: (1, 1) :: repeat (1, 2) 4643 ++ (4018, 2) :: (1, 1) :: repeat (1, 2) 25145 ++ (740664, 2) :: (1, 1) :: repeat (1, 2) 1511339 ++ (5653179, 2) :: (1, 1) :: repeat (1, 2) 11874956 ++ w) 1)).
  {
    exact (hsteps_step _ _ _ (hPX2A 232 41 [19] (repeat (1, 2) 333 ++ (2199, 2) :: (1, 1) :: repeat (1, 2) 4643 ++ (4018, 2) :: (1, 1) :: repeat (1, 2) 25145 ++ (740664, 2) :: (1, 1) :: repeat (1, 2) 1511339 ++ (5653179, 2) :: (1, 1) :: repeat (1, 2) 11874956 ++ w) 1) (hsteps_refl _)).
  }
  (* step 22: P PUSH *)
  apply (hsteps_trans _ (HC [19] 40 1 2 ((231, 2) :: (1, 1) :: repeat (1, 2) 335 ++ (2199, 2) :: (1, 1) :: repeat (1, 2) 4643 ++ (4018, 2) :: (1, 1) :: repeat (1, 2) 25145 ++ (740664, 2) :: (1, 1) :: repeat (1, 2) 1511339 ++ (5653179, 2) :: (1, 1) :: repeat (1, 2) 11874956 ++ w) 1)).
  {
    replace ((231, 2) :: (1, 1) :: repeat (1, 2) 335 ++ (2199, 2) :: (1, 1) :: repeat (1, 2) 4643 ++ (4018, 2) :: (1, 1) :: repeat (1, 2) 25145 ++ (740664, 2) :: (1, 1) :: repeat (1, 2) 1511339 ++ (5653179, 2) :: (1, 1) :: repeat (1, 2) 11874956 ++ w) with ((233 - 2, 2) :: (1, 1) :: repeat (1, 2) 335 ++ (2199, 2) :: (1, 1) :: repeat (1, 2) 4643 ++ (4018, 2) :: (1, 1) :: repeat (1, 2) 25145 ++ (740664, 2) :: (1, 1) :: repeat (1, 2) 1511339 ++ (5653179, 2) :: (1, 1) :: repeat (1, 2) 11874956 ++ w) by sec_eq.
    apply (sPUSH [19] 40 233 ((1, 1) :: repeat (1, 2) 335 ++ (2199, 2) :: (1, 1) :: repeat (1, 2) 4643 ++ (4018, 2) :: (1, 1) :: repeat (1, 2) 25145 ++ (740664, 2) :: (1, 1) :: repeat (1, 2) 1511339 ++ (5653179, 2) :: (1, 1) :: repeat (1, 2) 11874956 ++ w) 1); closearith.
  }
  (* step 23: P TDN *)
  apply (hsteps_trans _ (HB [19] 40 1 4 ((231, 2) :: (1, 1) :: repeat (1, 2) 335 ++ (2199, 2) :: (1, 1) :: repeat (1, 2) 4643 ++ (4018, 2) :: (1, 1) :: repeat (1, 2) 25145 ++ (740664, 2) :: (1, 1) :: repeat (1, 2) 1511339 ++ (5653179, 2) :: (1, 1) :: repeat (1, 2) 11874956 ++ w) 1)).
  {
    apply (sTDN [19] 40 ((231, 2) :: (1, 1) :: repeat (1, 2) 335 ++ (2199, 2) :: (1, 1) :: repeat (1, 2) 4643 ++ (4018, 2) :: (1, 1) :: repeat (1, 2) 25145 ++ (740664, 2) :: (1, 1) :: repeat (1, 2) 1511339 ++ (5653179, 2) :: (1, 1) :: repeat (1, 2) 11874956 ++ w) 1).
  }
  (* step 24: sTUP *)
  apply (hsteps_trans _ (HC [19] 40 3 2 ((229, 2) :: (1, 1) :: repeat (1, 2) 335 ++ (2199, 2) :: (1, 1) :: repeat (1, 2) 4643 ++ (4018, 2) :: (1, 1) :: repeat (1, 2) 25145 ++ (740664, 2) :: (1, 1) :: repeat (1, 2) 1511339 ++ (5653179, 2) :: (1, 1) :: repeat (1, 2) 11874956 ++ w) 1)).
  {
    replace ((229, 2) :: (1, 1) :: repeat (1, 2) 335 ++ (2199, 2) :: (1, 1) :: repeat (1, 2) 4643 ++ (4018, 2) :: (1, 1) :: repeat (1, 2) 25145 ++ (740664, 2) :: (1, 1) :: repeat (1, 2) 1511339 ++ (5653179, 2) :: (1, 1) :: repeat (1, 2) 11874956 ++ w) with ((231 - 2, 2) :: (1, 1) :: repeat (1, 2) 335 ++ (2199, 2) :: (1, 1) :: repeat (1, 2) 4643 ++ (4018, 2) :: (1, 1) :: repeat (1, 2) 25145 ++ (740664, 2) :: (1, 1) :: repeat (1, 2) 1511339 ++ (5653179, 2) :: (1, 1) :: repeat (1, 2) 11874956 ++ w) by sec_eq.
    apply (sTUP [19] 40 4 231 2 ((1, 1) :: repeat (1, 2) 335 ++ (2199, 2) :: (1, 1) :: repeat (1, 2) 4643 ++ (4018, 2) :: (1, 1) :: repeat (1, 2) 25145 ++ (740664, 2) :: (1, 1) :: repeat (1, 2) 1511339 ++ (5653179, 2) :: (1, 1) :: repeat (1, 2) 11874956 ++ w) 1); closearith.
  }
  (* step 25: DIPGRIND 40 149 *)
  apply (hsteps_trans _ (HC [19] 0 3 2 (repeat (1, 2) 40 ++ (149, 2) :: (1, 1) :: repeat (1, 2) 335 ++ (2199, 2) :: (1, 1) :: repeat (1, 2) 4643 ++ (4018, 2) :: (1, 1) :: repeat (1, 2) 25145 ++ (740664, 2) :: (1, 1) :: repeat (1, 2) 1511339 ++ (5653179, 2) :: (1, 1) :: repeat (1, 2) 11874956 ++ w) 1)).
  {
    apply (DIPGRIND 40 149 [19] ((1, 1) :: repeat (1, 2) 335 ++ (2199, 2) :: (1, 1) :: repeat (1, 2) 4643 ++ (4018, 2) :: (1, 1) :: repeat (1, 2) 25145 ++ (740664, 2) :: (1, 1) :: repeat (1, 2) 1511339 ++ (5653179, 2) :: (1, 1) :: repeat (1, 2) 11874956 ++ w) 1); closearith.
  }
  (* step 26: P PX2Bgen *)
  apply (hsteps_trans _ (HB [0] 3 1 2 ((15, 2) :: (1, 1) :: repeat (1, 2) 42 ++ (149, 2) :: (1, 1) :: repeat (1, 2) 335 ++ (2199, 2) :: (1, 1) :: repeat (1, 2) 4643 ++ (4018, 2) :: (1, 1) :: repeat (1, 2) 25145 ++ (740664, 2) :: (1, 1) :: repeat (1, 2) 1511339 ++ (5653179, 2) :: (1, 1) :: repeat (1, 2) 11874956 ++ w) 1)).
  {
    exact (hsteps_step _ _ _ (hPX2Bgen 14 (repeat (1, 2) 40 ++ (149, 2) :: (1, 1) :: repeat (1, 2) 335 ++ (2199, 2) :: (1, 1) :: repeat (1, 2) 4643 ++ (4018, 2) :: (1, 1) :: repeat (1, 2) 25145 ++ (740664, 2) :: (1, 1) :: repeat (1, 2) 1511339 ++ (5653179, 2) :: (1, 1) :: repeat (1, 2) 11874956 ++ w) 1) (hsteps_refl _)).
  }
  (* step 27: sTUP *)
  apply (hsteps_trans _ (HC [0] 3 1 2 ((13, 2) :: (1, 1) :: repeat (1, 2) 42 ++ (149, 2) :: (1, 1) :: repeat (1, 2) 335 ++ (2199, 2) :: (1, 1) :: repeat (1, 2) 4643 ++ (4018, 2) :: (1, 1) :: repeat (1, 2) 25145 ++ (740664, 2) :: (1, 1) :: repeat (1, 2) 1511339 ++ (5653179, 2) :: (1, 1) :: repeat (1, 2) 11874956 ++ w) 1)).
  {
    replace ((13, 2) :: (1, 1) :: repeat (1, 2) 42 ++ (149, 2) :: (1, 1) :: repeat (1, 2) 335 ++ (2199, 2) :: (1, 1) :: repeat (1, 2) 4643 ++ (4018, 2) :: (1, 1) :: repeat (1, 2) 25145 ++ (740664, 2) :: (1, 1) :: repeat (1, 2) 1511339 ++ (5653179, 2) :: (1, 1) :: repeat (1, 2) 11874956 ++ w) with ((15 - 2, 2) :: (1, 1) :: repeat (1, 2) 42 ++ (149, 2) :: (1, 1) :: repeat (1, 2) 335 ++ (2199, 2) :: (1, 1) :: repeat (1, 2) 4643 ++ (4018, 2) :: (1, 1) :: repeat (1, 2) 25145 ++ (740664, 2) :: (1, 1) :: repeat (1, 2) 1511339 ++ (5653179, 2) :: (1, 1) :: repeat (1, 2) 11874956 ++ w) by sec_eq.
    apply (sTUP [0] 3 2 15 2 ((1, 1) :: repeat (1, 2) 42 ++ (149, 2) :: (1, 1) :: repeat (1, 2) 335 ++ (2199, 2) :: (1, 1) :: repeat (1, 2) 4643 ++ (4018, 2) :: (1, 1) :: repeat (1, 2) 25145 ++ (740664, 2) :: (1, 1) :: repeat (1, 2) 1511339 ++ (5653179, 2) :: (1, 1) :: repeat (1, 2) 11874956 ++ w) 1); closearith.
  }
  (* step 28: P TDN *)
  apply (hsteps_trans _ (HB [0] 3 1 4 ((13, 2) :: (1, 1) :: repeat (1, 2) 42 ++ (149, 2) :: (1, 1) :: repeat (1, 2) 335 ++ (2199, 2) :: (1, 1) :: repeat (1, 2) 4643 ++ (4018, 2) :: (1, 1) :: repeat (1, 2) 25145 ++ (740664, 2) :: (1, 1) :: repeat (1, 2) 1511339 ++ (5653179, 2) :: (1, 1) :: repeat (1, 2) 11874956 ++ w) 1)).
  {
    apply (sTDN [0] 3 ((13, 2) :: (1, 1) :: repeat (1, 2) 42 ++ (149, 2) :: (1, 1) :: repeat (1, 2) 335 ++ (2199, 2) :: (1, 1) :: repeat (1, 2) 4643 ++ (4018, 2) :: (1, 1) :: repeat (1, 2) 25145 ++ (740664, 2) :: (1, 1) :: repeat (1, 2) 1511339 ++ (5653179, 2) :: (1, 1) :: repeat (1, 2) 11874956 ++ w) 1).
  }
  (* step 29: sTUP *)
  apply (hsteps_trans _ (HC [0] 3 3 2 ((11, 2) :: (1, 1) :: repeat (1, 2) 42 ++ (149, 2) :: (1, 1) :: repeat (1, 2) 335 ++ (2199, 2) :: (1, 1) :: repeat (1, 2) 4643 ++ (4018, 2) :: (1, 1) :: repeat (1, 2) 25145 ++ (740664, 2) :: (1, 1) :: repeat (1, 2) 1511339 ++ (5653179, 2) :: (1, 1) :: repeat (1, 2) 11874956 ++ w) 1)).
  {
    replace ((11, 2) :: (1, 1) :: repeat (1, 2) 42 ++ (149, 2) :: (1, 1) :: repeat (1, 2) 335 ++ (2199, 2) :: (1, 1) :: repeat (1, 2) 4643 ++ (4018, 2) :: (1, 1) :: repeat (1, 2) 25145 ++ (740664, 2) :: (1, 1) :: repeat (1, 2) 1511339 ++ (5653179, 2) :: (1, 1) :: repeat (1, 2) 11874956 ++ w) with ((13 - 2, 2) :: (1, 1) :: repeat (1, 2) 42 ++ (149, 2) :: (1, 1) :: repeat (1, 2) 335 ++ (2199, 2) :: (1, 1) :: repeat (1, 2) 4643 ++ (4018, 2) :: (1, 1) :: repeat (1, 2) 25145 ++ (740664, 2) :: (1, 1) :: repeat (1, 2) 1511339 ++ (5653179, 2) :: (1, 1) :: repeat (1, 2) 11874956 ++ w) by sec_eq.
    apply (sTUP [0] 3 4 13 2 ((1, 1) :: repeat (1, 2) 42 ++ (149, 2) :: (1, 1) :: repeat (1, 2) 335 ++ (2199, 2) :: (1, 1) :: repeat (1, 2) 4643 ++ (4018, 2) :: (1, 1) :: repeat (1, 2) 25145 ++ (740664, 2) :: (1, 1) :: repeat (1, 2) 1511339 ++ (5653179, 2) :: (1, 1) :: repeat (1, 2) 11874956 ++ w) 1); closearith.
  }
  (* step 30: DIPGRIND 3 5 *)
  apply (hsteps_trans _ (HC [0] 0 3 2 (repeat (1, 2) 3 ++ (5, 2) :: (1, 1) :: repeat (1, 2) 42 ++ (149, 2) :: (1, 1) :: repeat (1, 2) 335 ++ (2199, 2) :: (1, 1) :: repeat (1, 2) 4643 ++ (4018, 2) :: (1, 1) :: repeat (1, 2) 25145 ++ (740664, 2) :: (1, 1) :: repeat (1, 2) 1511339 ++ (5653179, 2) :: (1, 1) :: repeat (1, 2) 11874956 ++ w) 1)).
  {
    apply (DIPGRIND 3 5 [0] ((1, 1) :: repeat (1, 2) 42 ++ (149, 2) :: (1, 1) :: repeat (1, 2) 335 ++ (2199, 2) :: (1, 1) :: repeat (1, 2) 4643 ++ (4018, 2) :: (1, 1) :: repeat (1, 2) 25145 ++ (740664, 2) :: (1, 1) :: repeat (1, 2) 1511339 ++ (5653179, 2) :: (1, 1) :: repeat (1, 2) 11874956 ++ w) 1); closearith.
  }
  (* step 31: P PX2B0 *)
  apply (hsteps_trans _ (HB [] 0 1 5 (repeat (1, 2) 4 ++ (5, 2) :: (1, 1) :: repeat (1, 2) 42 ++ (149, 2) :: (1, 1) :: repeat (1, 2) 335 ++ (2199, 2) :: (1, 1) :: repeat (1, 2) 4643 ++ (4018, 2) :: (1, 1) :: repeat (1, 2) 25145 ++ (740664, 2) :: (1, 1) :: repeat (1, 2) 1511339 ++ (5653179, 2) :: (1, 1) :: repeat (1, 2) 11874956 ++ w) 1)).
  {
    exact (hsteps_step _ _ _ (hPX2B0 (repeat (1, 2) 3 ++ (5, 2) :: (1, 1) :: repeat (1, 2) 42 ++ (149, 2) :: (1, 1) :: repeat (1, 2) 335 ++ (2199, 2) :: (1, 1) :: repeat (1, 2) 4643 ++ (4018, 2) :: (1, 1) :: repeat (1, 2) 25145 ++ (740664, 2) :: (1, 1) :: repeat (1, 2) 1511339 ++ (5653179, 2) :: (1, 1) :: repeat (1, 2) 11874956 ++ w) 1) (hsteps_refl _)).
  }
  (* step 32: M pop12 (4,) *)
  apply (hsteps_trans _ (HB [] 4 1 13 ((5, 2) :: (1, 1) :: repeat (1, 2) 42 ++ (149, 2) :: (1, 1) :: repeat (1, 2) 335 ++ (2199, 2) :: (1, 1) :: repeat (1, 2) 4643 ++ (4018, 2) :: (1, 1) :: repeat (1, 2) 25145 ++ (740664, 2) :: (1, 1) :: repeat (1, 2) 1511339 ++ (5653179, 2) :: (1, 1) :: repeat (1, 2) 11874956 ++ w) 1)).
  {
    apply (pop12 4 [] 0 5 ((5, 2) :: (1, 1) :: repeat (1, 2) 42 ++ (149, 2) :: (1, 1) :: repeat (1, 2) 335 ++ (2199, 2) :: (1, 1) :: repeat (1, 2) 4643 ++ (4018, 2) :: (1, 1) :: repeat (1, 2) 25145 ++ (740664, 2) :: (1, 1) :: repeat (1, 2) 1511339 ++ (5653179, 2) :: (1, 1) :: repeat (1, 2) 11874956 ++ w) 1); closearith.
  }
  (* step 33: sTUP *)
  apply (hsteps_trans _ (HC [] 4 12 2 ((3, 2) :: (1, 1) :: repeat (1, 2) 42 ++ (149, 2) :: (1, 1) :: repeat (1, 2) 335 ++ (2199, 2) :: (1, 1) :: repeat (1, 2) 4643 ++ (4018, 2) :: (1, 1) :: repeat (1, 2) 25145 ++ (740664, 2) :: (1, 1) :: repeat (1, 2) 1511339 ++ (5653179, 2) :: (1, 1) :: repeat (1, 2) 11874956 ++ w) 1)).
  {
    replace ((3, 2) :: (1, 1) :: repeat (1, 2) 42 ++ (149, 2) :: (1, 1) :: repeat (1, 2) 335 ++ (2199, 2) :: (1, 1) :: repeat (1, 2) 4643 ++ (4018, 2) :: (1, 1) :: repeat (1, 2) 25145 ++ (740664, 2) :: (1, 1) :: repeat (1, 2) 1511339 ++ (5653179, 2) :: (1, 1) :: repeat (1, 2) 11874956 ++ w) with ((5 - 2, 2) :: (1, 1) :: repeat (1, 2) 42 ++ (149, 2) :: (1, 1) :: repeat (1, 2) 335 ++ (2199, 2) :: (1, 1) :: repeat (1, 2) 4643 ++ (4018, 2) :: (1, 1) :: repeat (1, 2) 25145 ++ (740664, 2) :: (1, 1) :: repeat (1, 2) 1511339 ++ (5653179, 2) :: (1, 1) :: repeat (1, 2) 11874956 ++ w) by sec_eq.
    apply (sTUP [] 4 13 5 2 ((1, 1) :: repeat (1, 2) 42 ++ (149, 2) :: (1, 1) :: repeat (1, 2) 335 ++ (2199, 2) :: (1, 1) :: repeat (1, 2) 4643 ++ (4018, 2) :: (1, 1) :: repeat (1, 2) 25145 ++ (740664, 2) :: (1, 1) :: repeat (1, 2) 1511339 ++ (5653179, 2) :: (1, 1) :: repeat (1, 2) 11874956 ++ w) 1); closearith.
  }
  (* step 34: P PUSH *)
  apply (hsteps_trans _ (HC [] 3 1 2 ((10, 2) :: (3, 2) :: (1, 1) :: repeat (1, 2) 42 ++ (149, 2) :: (1, 1) :: repeat (1, 2) 335 ++ (2199, 2) :: (1, 1) :: repeat (1, 2) 4643 ++ (4018, 2) :: (1, 1) :: repeat (1, 2) 25145 ++ (740664, 2) :: (1, 1) :: repeat (1, 2) 1511339 ++ (5653179, 2) :: (1, 1) :: repeat (1, 2) 11874956 ++ w) 1)).
  {
    replace ((10, 2) :: (3, 2) :: (1, 1) :: repeat (1, 2) 42 ++ (149, 2) :: (1, 1) :: repeat (1, 2) 335 ++ (2199, 2) :: (1, 1) :: repeat (1, 2) 4643 ++ (4018, 2) :: (1, 1) :: repeat (1, 2) 25145 ++ (740664, 2) :: (1, 1) :: repeat (1, 2) 1511339 ++ (5653179, 2) :: (1, 1) :: repeat (1, 2) 11874956 ++ w) with ((12 - 2, 2) :: (3, 2) :: (1, 1) :: repeat (1, 2) 42 ++ (149, 2) :: (1, 1) :: repeat (1, 2) 335 ++ (2199, 2) :: (1, 1) :: repeat (1, 2) 4643 ++ (4018, 2) :: (1, 1) :: repeat (1, 2) 25145 ++ (740664, 2) :: (1, 1) :: repeat (1, 2) 1511339 ++ (5653179, 2) :: (1, 1) :: repeat (1, 2) 11874956 ++ w) by sec_eq.
    apply (sPUSH [] 3 12 ((3, 2) :: (1, 1) :: repeat (1, 2) 42 ++ (149, 2) :: (1, 1) :: repeat (1, 2) 335 ++ (2199, 2) :: (1, 1) :: repeat (1, 2) 4643 ++ (4018, 2) :: (1, 1) :: repeat (1, 2) 25145 ++ (740664, 2) :: (1, 1) :: repeat (1, 2) 1511339 ++ (5653179, 2) :: (1, 1) :: repeat (1, 2) 11874956 ++ w) 1); closearith.
  }
  (* step 35: P TDN *)
  apply (hsteps_trans _ (HB [] 3 1 4 ((10, 2) :: (3, 2) :: (1, 1) :: repeat (1, 2) 42 ++ (149, 2) :: (1, 1) :: repeat (1, 2) 335 ++ (2199, 2) :: (1, 1) :: repeat (1, 2) 4643 ++ (4018, 2) :: (1, 1) :: repeat (1, 2) 25145 ++ (740664, 2) :: (1, 1) :: repeat (1, 2) 1511339 ++ (5653179, 2) :: (1, 1) :: repeat (1, 2) 11874956 ++ w) 1)).
  {
    apply (sTDN [] 3 ((10, 2) :: (3, 2) :: (1, 1) :: repeat (1, 2) 42 ++ (149, 2) :: (1, 1) :: repeat (1, 2) 335 ++ (2199, 2) :: (1, 1) :: repeat (1, 2) 4643 ++ (4018, 2) :: (1, 1) :: repeat (1, 2) 25145 ++ (740664, 2) :: (1, 1) :: repeat (1, 2) 1511339 ++ (5653179, 2) :: (1, 1) :: repeat (1, 2) 11874956 ++ w) 1).
  }
  (* step 36: sTUP *)
  apply (hsteps_trans _ (HC [] 3 3 2 ((8, 2) :: (3, 2) :: (1, 1) :: repeat (1, 2) 42 ++ (149, 2) :: (1, 1) :: repeat (1, 2) 335 ++ (2199, 2) :: (1, 1) :: repeat (1, 2) 4643 ++ (4018, 2) :: (1, 1) :: repeat (1, 2) 25145 ++ (740664, 2) :: (1, 1) :: repeat (1, 2) 1511339 ++ (5653179, 2) :: (1, 1) :: repeat (1, 2) 11874956 ++ w) 1)).
  {
    replace ((8, 2) :: (3, 2) :: (1, 1) :: repeat (1, 2) 42 ++ (149, 2) :: (1, 1) :: repeat (1, 2) 335 ++ (2199, 2) :: (1, 1) :: repeat (1, 2) 4643 ++ (4018, 2) :: (1, 1) :: repeat (1, 2) 25145 ++ (740664, 2) :: (1, 1) :: repeat (1, 2) 1511339 ++ (5653179, 2) :: (1, 1) :: repeat (1, 2) 11874956 ++ w) with ((10 - 2, 2) :: (3, 2) :: (1, 1) :: repeat (1, 2) 42 ++ (149, 2) :: (1, 1) :: repeat (1, 2) 335 ++ (2199, 2) :: (1, 1) :: repeat (1, 2) 4643 ++ (4018, 2) :: (1, 1) :: repeat (1, 2) 25145 ++ (740664, 2) :: (1, 1) :: repeat (1, 2) 1511339 ++ (5653179, 2) :: (1, 1) :: repeat (1, 2) 11874956 ++ w) by sec_eq.
    apply (sTUP [] 3 4 10 2 ((3, 2) :: (1, 1) :: repeat (1, 2) 42 ++ (149, 2) :: (1, 1) :: repeat (1, 2) 335 ++ (2199, 2) :: (1, 1) :: repeat (1, 2) 4643 ++ (4018, 2) :: (1, 1) :: repeat (1, 2) 25145 ++ (740664, 2) :: (1, 1) :: repeat (1, 2) 1511339 ++ (5653179, 2) :: (1, 1) :: repeat (1, 2) 11874956 ++ w) 1); closearith.
  }
  (* step 37: DIPGRIND 3 2 *)
  apply (hsteps_trans _ (HC [] 0 3 2 (repeat (1, 2) 3 ++ (2, 2) :: (3, 2) :: (1, 1) :: repeat (1, 2) 42 ++ (149, 2) :: (1, 1) :: repeat (1, 2) 335 ++ (2199, 2) :: (1, 1) :: repeat (1, 2) 4643 ++ (4018, 2) :: (1, 1) :: repeat (1, 2) 25145 ++ (740664, 2) :: (1, 1) :: repeat (1, 2) 1511339 ++ (5653179, 2) :: (1, 1) :: repeat (1, 2) 11874956 ++ w) 1)).
  {
    apply (DIPGRIND 3 2 [] ((3, 2) :: (1, 1) :: repeat (1, 2) 42 ++ (149, 2) :: (1, 1) :: repeat (1, 2) 335 ++ (2199, 2) :: (1, 1) :: repeat (1, 2) 4643 ++ (4018, 2) :: (1, 1) :: repeat (1, 2) 25145 ++ (740664, 2) :: (1, 1) :: repeat (1, 2) 1511339 ++ (5653179, 2) :: (1, 1) :: repeat (1, 2) 11874956 ++ w) 1); closearith.
  }
  (* step 38: P PUSHX *)
  apply (hsteps_trans _ (HB [] 1 1 7 (repeat (1, 2) 3 ++ (2, 2) :: (3, 2) :: (1, 1) :: repeat (1, 2) 42 ++ (149, 2) :: (1, 1) :: repeat (1, 2) 335 ++ (2199, 2) :: (1, 1) :: repeat (1, 2) 4643 ++ (4018, 2) :: (1, 1) :: repeat (1, 2) 25145 ++ (740664, 2) :: (1, 1) :: repeat (1, 2) 1511339 ++ (5653179, 2) :: (1, 1) :: repeat (1, 2) 11874956 ++ w) 1)).
  {
    exact (hsteps_step _ _ _ (hPUSHX (repeat (1, 2) 3 ++ (2, 2) :: (3, 2) :: (1, 1) :: repeat (1, 2) 42 ++ (149, 2) :: (1, 1) :: repeat (1, 2) 335 ++ (2199, 2) :: (1, 1) :: repeat (1, 2) 4643 ++ (4018, 2) :: (1, 1) :: repeat (1, 2) 25145 ++ (740664, 2) :: (1, 1) :: repeat (1, 2) 1511339 ++ (5653179, 2) :: (1, 1) :: repeat (1, 2) 11874956 ++ w) 1) (hsteps_refl _)).
  }
  (* step 39: M pop12 (3,) *)
  apply (hsteps_trans _ (HB [] 4 1 13 ((2, 2) :: (3, 2) :: (1, 1) :: repeat (1, 2) 42 ++ (149, 2) :: (1, 1) :: repeat (1, 2) 335 ++ (2199, 2) :: (1, 1) :: repeat (1, 2) 4643 ++ (4018, 2) :: (1, 1) :: repeat (1, 2) 25145 ++ (740664, 2) :: (1, 1) :: repeat (1, 2) 1511339 ++ (5653179, 2) :: (1, 1) :: repeat (1, 2) 11874956 ++ w) 1)).
  {
    apply (pop12 3 [] 1 7 ((2, 2) :: (3, 2) :: (1, 1) :: repeat (1, 2) 42 ++ (149, 2) :: (1, 1) :: repeat (1, 2) 335 ++ (2199, 2) :: (1, 1) :: repeat (1, 2) 4643 ++ (4018, 2) :: (1, 1) :: repeat (1, 2) 25145 ++ (740664, 2) :: (1, 1) :: repeat (1, 2) 1511339 ++ (5653179, 2) :: (1, 1) :: repeat (1, 2) 11874956 ++ w) 1); closearith.
  }
  (* step 40: P TUP2_1 *)
  apply (hsteps_trans _ (HC [5] 13 1 2 (repeat (1, 2) 1 ++ (1, 1) :: repeat (1, 2) 42 ++ (149, 2) :: (1, 1) :: repeat (1, 2) 335 ++ (2199, 2) :: (1, 1) :: repeat (1, 2) 4643 ++ (4018, 2) :: (1, 1) :: repeat (1, 2) 25145 ++ (740664, 2) :: (1, 1) :: repeat (1, 2) 1511339 ++ (5653179, 2) :: (1, 1) :: repeat (1, 2) 11874956 ++ w) 1)).
  {
    replace (repeat (1, 2) 1 ++ (1, 1) :: repeat (1, 2) 42 ++ (149, 2) :: (1, 1) :: repeat (1, 2) 335 ++ (2199, 2) :: (1, 1) :: repeat (1, 2) 4643 ++ (4018, 2) :: (1, 1) :: repeat (1, 2) 25145 ++ (740664, 2) :: (1, 1) :: repeat (1, 2) 1511339 ++ (5653179, 2) :: (1, 1) :: repeat (1, 2) 11874956 ++ w) with ((3 - 2, 2) :: (1, 1) :: repeat (1, 2) 42 ++ (149, 2) :: (1, 1) :: repeat (1, 2) 335 ++ (2199, 2) :: (1, 1) :: repeat (1, 2) 4643 ++ (4018, 2) :: (1, 1) :: repeat (1, 2) 25145 ++ (740664, 2) :: (1, 1) :: repeat (1, 2) 1511339 ++ (5653179, 2) :: (1, 1) :: repeat (1, 2) 11874956 ++ w) by sec_eq.
    apply (sTUP2_1 [] 4 12 3 ((1, 1) :: repeat (1, 2) 42 ++ (149, 2) :: (1, 1) :: repeat (1, 2) 335 ++ (2199, 2) :: (1, 1) :: repeat (1, 2) 4643 ++ (4018, 2) :: (1, 1) :: repeat (1, 2) 25145 ++ (740664, 2) :: (1, 1) :: repeat (1, 2) 1511339 ++ (5653179, 2) :: (1, 1) :: repeat (1, 2) 11874956 ++ w) 1); closearith.
  }
  (* step 41: P TDN *)
  apply (hsteps_trans _ (HB [5] 13 1 4 (repeat (1, 2) 1 ++ (1, 1) :: repeat (1, 2) 42 ++ (149, 2) :: (1, 1) :: repeat (1, 2) 335 ++ (2199, 2) :: (1, 1) :: repeat (1, 2) 4643 ++ (4018, 2) :: (1, 1) :: repeat (1, 2) 25145 ++ (740664, 2) :: (1, 1) :: repeat (1, 2) 1511339 ++ (5653179, 2) :: (1, 1) :: repeat (1, 2) 11874956 ++ w) 1)).
  {
    apply (sTDN [5] 13 (repeat (1, 2) 1 ++ (1, 1) :: repeat (1, 2) 42 ++ (149, 2) :: (1, 1) :: repeat (1, 2) 335 ++ (2199, 2) :: (1, 1) :: repeat (1, 2) 4643 ++ (4018, 2) :: (1, 1) :: repeat (1, 2) 25145 ++ (740664, 2) :: (1, 1) :: repeat (1, 2) 1511339 ++ (5653179, 2) :: (1, 1) :: repeat (1, 2) 11874956 ++ w) 1).
  }
  (* step 42: M pop12 (1,) *)
  apply (hsteps_trans _ (HB [5] 14 1 6 ((1, 1) :: repeat (1, 2) 42 ++ (149, 2) :: (1, 1) :: repeat (1, 2) 335 ++ (2199, 2) :: (1, 1) :: repeat (1, 2) 4643 ++ (4018, 2) :: (1, 1) :: repeat (1, 2) 25145 ++ (740664, 2) :: (1, 1) :: repeat (1, 2) 1511339 ++ (5653179, 2) :: (1, 1) :: repeat (1, 2) 11874956 ++ w) 1)).
  {
    apply (pop12 1 [5] 13 4 ((1, 1) :: repeat (1, 2) 42 ++ (149, 2) :: (1, 1) :: repeat (1, 2) 335 ++ (2199, 2) :: (1, 1) :: repeat (1, 2) 4643 ++ (4018, 2) :: (1, 1) :: repeat (1, 2) 25145 ++ (740664, 2) :: (1, 1) :: repeat (1, 2) 1511339 ++ (5653179, 2) :: (1, 1) :: repeat (1, 2) 11874956 ++ w) 1); closearith.
  }
  (* step 43: P POP *)
  apply (hsteps_trans _ (HB [5] 15 1 7 (repeat (1, 2) 42 ++ (149, 2) :: (1, 1) :: repeat (1, 2) 335 ++ (2199, 2) :: (1, 1) :: repeat (1, 2) 4643 ++ (4018, 2) :: (1, 1) :: repeat (1, 2) 25145 ++ (740664, 2) :: (1, 1) :: repeat (1, 2) 1511339 ++ (5653179, 2) :: (1, 1) :: repeat (1, 2) 11874956 ++ w) 1)).
  {
    apply (sPOP1 [5] 14 6 (repeat (1, 2) 42 ++ (149, 2) :: (1, 1) :: repeat (1, 2) 335 ++ (2199, 2) :: (1, 1) :: repeat (1, 2) 4643 ++ (4018, 2) :: (1, 1) :: repeat (1, 2) 25145 ++ (740664, 2) :: (1, 1) :: repeat (1, 2) 1511339 ++ (5653179, 2) :: (1, 1) :: repeat (1, 2) 11874956 ++ w) 1); closearith.
  }
  (* step 44: M pop12 (42,) *)
  apply (hsteps_trans _ (HB [5] 57 1 91 ((149, 2) :: (1, 1) :: repeat (1, 2) 335 ++ (2199, 2) :: (1, 1) :: repeat (1, 2) 4643 ++ (4018, 2) :: (1, 1) :: repeat (1, 2) 25145 ++ (740664, 2) :: (1, 1) :: repeat (1, 2) 1511339 ++ (5653179, 2) :: (1, 1) :: repeat (1, 2) 11874956 ++ w) 1)).
  {
    apply (pop12 42 [5] 15 7 ((149, 2) :: (1, 1) :: repeat (1, 2) 335 ++ (2199, 2) :: (1, 1) :: repeat (1, 2) 4643 ++ (4018, 2) :: (1, 1) :: repeat (1, 2) 25145 ++ (740664, 2) :: (1, 1) :: repeat (1, 2) 1511339 ++ (5653179, 2) :: (1, 1) :: repeat (1, 2) 11874956 ++ w) 1); closearith.
  }
  (* step 45: sTUP *)
  apply (hsteps_trans _ (HC [5] 57 90 2 ((147, 2) :: (1, 1) :: repeat (1, 2) 335 ++ (2199, 2) :: (1, 1) :: repeat (1, 2) 4643 ++ (4018, 2) :: (1, 1) :: repeat (1, 2) 25145 ++ (740664, 2) :: (1, 1) :: repeat (1, 2) 1511339 ++ (5653179, 2) :: (1, 1) :: repeat (1, 2) 11874956 ++ w) 1)).
  {
    replace ((147, 2) :: (1, 1) :: repeat (1, 2) 335 ++ (2199, 2) :: (1, 1) :: repeat (1, 2) 4643 ++ (4018, 2) :: (1, 1) :: repeat (1, 2) 25145 ++ (740664, 2) :: (1, 1) :: repeat (1, 2) 1511339 ++ (5653179, 2) :: (1, 1) :: repeat (1, 2) 11874956 ++ w) with ((149 - 2, 2) :: (1, 1) :: repeat (1, 2) 335 ++ (2199, 2) :: (1, 1) :: repeat (1, 2) 4643 ++ (4018, 2) :: (1, 1) :: repeat (1, 2) 25145 ++ (740664, 2) :: (1, 1) :: repeat (1, 2) 1511339 ++ (5653179, 2) :: (1, 1) :: repeat (1, 2) 11874956 ++ w) by sec_eq.
    apply (sTUP [5] 57 91 149 2 ((1, 1) :: repeat (1, 2) 335 ++ (2199, 2) :: (1, 1) :: repeat (1, 2) 4643 ++ (4018, 2) :: (1, 1) :: repeat (1, 2) 25145 ++ (740664, 2) :: (1, 1) :: repeat (1, 2) 1511339 ++ (5653179, 2) :: (1, 1) :: repeat (1, 2) 11874956 ++ w) 1); closearith.
  }
  (* step 46: hGRIND_even 43 *)
  apply (hsteps_trans _ (HB [5] 56 1 90 ((2, 2) :: (147, 2) :: (1, 1) :: repeat (1, 2) 335 ++ (2199, 2) :: (1, 1) :: repeat (1, 2) 4643 ++ (4018, 2) :: (1, 1) :: repeat (1, 2) 25145 ++ (740664, 2) :: (1, 1) :: repeat (1, 2) 1511339 ++ (5653179, 2) :: (1, 1) :: repeat (1, 2) 11874956 ++ w) 1)).
  {
    apply (hGRIND_even 43 [5] 56 ((147, 2) :: (1, 1) :: repeat (1, 2) 335 ++ (2199, 2) :: (1, 1) :: repeat (1, 2) 4643 ++ (4018, 2) :: (1, 1) :: repeat (1, 2) 25145 ++ (740664, 2) :: (1, 1) :: repeat (1, 2) 1511339 ++ (5653179, 2) :: (1, 1) :: repeat (1, 2) 11874956 ++ w) 1); closearith.
  }
  (* step 47: P TUP2_1 *)
  apply (hsteps_trans _ (HC [57; 5] 90 1 2 ((145, 2) :: (1, 1) :: repeat (1, 2) 335 ++ (2199, 2) :: (1, 1) :: repeat (1, 2) 4643 ++ (4018, 2) :: (1, 1) :: repeat (1, 2) 25145 ++ (740664, 2) :: (1, 1) :: repeat (1, 2) 1511339 ++ (5653179, 2) :: (1, 1) :: repeat (1, 2) 11874956 ++ w) 1)).
  {
    replace ((145, 2) :: (1, 1) :: repeat (1, 2) 335 ++ (2199, 2) :: (1, 1) :: repeat (1, 2) 4643 ++ (4018, 2) :: (1, 1) :: repeat (1, 2) 25145 ++ (740664, 2) :: (1, 1) :: repeat (1, 2) 1511339 ++ (5653179, 2) :: (1, 1) :: repeat (1, 2) 11874956 ++ w) with ((147 - 2, 2) :: (1, 1) :: repeat (1, 2) 335 ++ (2199, 2) :: (1, 1) :: repeat (1, 2) 4643 ++ (4018, 2) :: (1, 1) :: repeat (1, 2) 25145 ++ (740664, 2) :: (1, 1) :: repeat (1, 2) 1511339 ++ (5653179, 2) :: (1, 1) :: repeat (1, 2) 11874956 ++ w) by sec_eq.
    apply (sTUP2_1 [5] 56 89 147 ((1, 1) :: repeat (1, 2) 335 ++ (2199, 2) :: (1, 1) :: repeat (1, 2) 4643 ++ (4018, 2) :: (1, 1) :: repeat (1, 2) 25145 ++ (740664, 2) :: (1, 1) :: repeat (1, 2) 1511339 ++ (5653179, 2) :: (1, 1) :: repeat (1, 2) 11874956 ++ w) 1); closearith.
  }
  (* step 48: P TDN *)
  apply (hsteps_trans _ (HB [57; 5] 90 1 4 ((145, 2) :: (1, 1) :: repeat (1, 2) 335 ++ (2199, 2) :: (1, 1) :: repeat (1, 2) 4643 ++ (4018, 2) :: (1, 1) :: repeat (1, 2) 25145 ++ (740664, 2) :: (1, 1) :: repeat (1, 2) 1511339 ++ (5653179, 2) :: (1, 1) :: repeat (1, 2) 11874956 ++ w) 1)).
  {
    apply (sTDN [57; 5] 90 ((145, 2) :: (1, 1) :: repeat (1, 2) 335 ++ (2199, 2) :: (1, 1) :: repeat (1, 2) 4643 ++ (4018, 2) :: (1, 1) :: repeat (1, 2) 25145 ++ (740664, 2) :: (1, 1) :: repeat (1, 2) 1511339 ++ (5653179, 2) :: (1, 1) :: repeat (1, 2) 11874956 ++ w) 1).
  }
  (* step 49: sTUP *)
  apply (hsteps_trans _ (HC [57; 5] 90 3 2 ((143, 2) :: (1, 1) :: repeat (1, 2) 335 ++ (2199, 2) :: (1, 1) :: repeat (1, 2) 4643 ++ (4018, 2) :: (1, 1) :: repeat (1, 2) 25145 ++ (740664, 2) :: (1, 1) :: repeat (1, 2) 1511339 ++ (5653179, 2) :: (1, 1) :: repeat (1, 2) 11874956 ++ w) 1)).
  {
    replace ((143, 2) :: (1, 1) :: repeat (1, 2) 335 ++ (2199, 2) :: (1, 1) :: repeat (1, 2) 4643 ++ (4018, 2) :: (1, 1) :: repeat (1, 2) 25145 ++ (740664, 2) :: (1, 1) :: repeat (1, 2) 1511339 ++ (5653179, 2) :: (1, 1) :: repeat (1, 2) 11874956 ++ w) with ((145 - 2, 2) :: (1, 1) :: repeat (1, 2) 335 ++ (2199, 2) :: (1, 1) :: repeat (1, 2) 4643 ++ (4018, 2) :: (1, 1) :: repeat (1, 2) 25145 ++ (740664, 2) :: (1, 1) :: repeat (1, 2) 1511339 ++ (5653179, 2) :: (1, 1) :: repeat (1, 2) 11874956 ++ w) by sec_eq.
    apply (sTUP [57; 5] 90 4 145 2 ((1, 1) :: repeat (1, 2) 335 ++ (2199, 2) :: (1, 1) :: repeat (1, 2) 4643 ++ (4018, 2) :: (1, 1) :: repeat (1, 2) 25145 ++ (740664, 2) :: (1, 1) :: repeat (1, 2) 1511339 ++ (5653179, 2) :: (1, 1) :: repeat (1, 2) 11874956 ++ w) 1); closearith.
  }
  (* step 50: CLEANG_odd 70 *)
  apply (hsteps_trans _ (HB [57; 5] 90 1 148 (repeat (1, 2) 1 ++ (1, 1) :: repeat (1, 2) 335 ++ (2199, 2) :: (1, 1) :: repeat (1, 2) 4643 ++ (4018, 2) :: (1, 1) :: repeat (1, 2) 25145 ++ (740664, 2) :: (1, 1) :: repeat (1, 2) 1511339 ++ (5653179, 2) :: (1, 1) :: repeat (1, 2) 11874956 ++ w) 1)).
  {
    replace (repeat (1, 2) 1 ++ (1, 1) :: repeat (1, 2) 335 ++ (2199, 2) :: (1, 1) :: repeat (1, 2) 4643 ++ (4018, 2) :: (1, 1) :: repeat (1, 2) 25145 ++ (740664, 2) :: (1, 1) :: repeat (1, 2) 1511339 ++ (5653179, 2) :: (1, 1) :: repeat (1, 2) 11874956 ++ w) with ((1, 2) :: (1, 1) :: repeat (1, 2) 335 ++ (2199, 2) :: (1, 1) :: repeat (1, 2) 4643 ++ (4018, 2) :: (1, 1) :: repeat (1, 2) 25145 ++ (740664, 2) :: (1, 1) :: repeat (1, 2) 1511339 ++ (5653179, 2) :: (1, 1) :: repeat (1, 2) 11874956 ++ w) by sec_eq.
    apply (CLEANG_odd 70 [57; 5] 90 ((1, 1) :: repeat (1, 2) 335 ++ (2199, 2) :: (1, 1) :: repeat (1, 2) 4643 ++ (4018, 2) :: (1, 1) :: repeat (1, 2) 25145 ++ (740664, 2) :: (1, 1) :: repeat (1, 2) 1511339 ++ (5653179, 2) :: (1, 1) :: repeat (1, 2) 11874956 ++ w) 1); closearith.
  }
  (* step 51: M pop12 (1,) *)
  apply (hsteps_trans _ (HB [57; 5] 91 1 150 ((1, 1) :: repeat (1, 2) 335 ++ (2199, 2) :: (1, 1) :: repeat (1, 2) 4643 ++ (4018, 2) :: (1, 1) :: repeat (1, 2) 25145 ++ (740664, 2) :: (1, 1) :: repeat (1, 2) 1511339 ++ (5653179, 2) :: (1, 1) :: repeat (1, 2) 11874956 ++ w) 1)).
  {
    apply (pop12 1 [57; 5] 90 148 ((1, 1) :: repeat (1, 2) 335 ++ (2199, 2) :: (1, 1) :: repeat (1, 2) 4643 ++ (4018, 2) :: (1, 1) :: repeat (1, 2) 25145 ++ (740664, 2) :: (1, 1) :: repeat (1, 2) 1511339 ++ (5653179, 2) :: (1, 1) :: repeat (1, 2) 11874956 ++ w) 1); closearith.
  }
  (* step 52: P POP *)
  apply (hsteps_trans _ (HB [57; 5] 92 1 151 (repeat (1, 2) 335 ++ (2199, 2) :: (1, 1) :: repeat (1, 2) 4643 ++ (4018, 2) :: (1, 1) :: repeat (1, 2) 25145 ++ (740664, 2) :: (1, 1) :: repeat (1, 2) 1511339 ++ (5653179, 2) :: (1, 1) :: repeat (1, 2) 11874956 ++ w) 1)).
  {
    apply (sPOP1 [57; 5] 91 150 (repeat (1, 2) 335 ++ (2199, 2) :: (1, 1) :: repeat (1, 2) 4643 ++ (4018, 2) :: (1, 1) :: repeat (1, 2) 25145 ++ (740664, 2) :: (1, 1) :: repeat (1, 2) 1511339 ++ (5653179, 2) :: (1, 1) :: repeat (1, 2) 11874956 ++ w) 1); closearith.
  }
  (* step 53: M pop12 (335,) *)
  apply (hsteps_trans _ (HB [57; 5] 427 1 821 ((2199, 2) :: (1, 1) :: repeat (1, 2) 4643 ++ (4018, 2) :: (1, 1) :: repeat (1, 2) 25145 ++ (740664, 2) :: (1, 1) :: repeat (1, 2) 1511339 ++ (5653179, 2) :: (1, 1) :: repeat (1, 2) 11874956 ++ w) 1)).
  {
    apply (pop12 335 [57; 5] 92 151 ((2199, 2) :: (1, 1) :: repeat (1, 2) 4643 ++ (4018, 2) :: (1, 1) :: repeat (1, 2) 25145 ++ (740664, 2) :: (1, 1) :: repeat (1, 2) 1511339 ++ (5653179, 2) :: (1, 1) :: repeat (1, 2) 11874956 ++ w) 1); closearith.
  }
  (* step 54: sTUP *)
  apply (hsteps_trans _ (HC [57; 5] 427 820 2 ((2197, 2) :: (1, 1) :: repeat (1, 2) 4643 ++ (4018, 2) :: (1, 1) :: repeat (1, 2) 25145 ++ (740664, 2) :: (1, 1) :: repeat (1, 2) 1511339 ++ (5653179, 2) :: (1, 1) :: repeat (1, 2) 11874956 ++ w) 1)).
  {
    replace ((2197, 2) :: (1, 1) :: repeat (1, 2) 4643 ++ (4018, 2) :: (1, 1) :: repeat (1, 2) 25145 ++ (740664, 2) :: (1, 1) :: repeat (1, 2) 1511339 ++ (5653179, 2) :: (1, 1) :: repeat (1, 2) 11874956 ++ w) with ((2199 - 2, 2) :: (1, 1) :: repeat (1, 2) 4643 ++ (4018, 2) :: (1, 1) :: repeat (1, 2) 25145 ++ (740664, 2) :: (1, 1) :: repeat (1, 2) 1511339 ++ (5653179, 2) :: (1, 1) :: repeat (1, 2) 11874956 ++ w) by sec_eq.
    apply (sTUP [57; 5] 427 821 2199 2 ((1, 1) :: repeat (1, 2) 4643 ++ (4018, 2) :: (1, 1) :: repeat (1, 2) 25145 ++ (740664, 2) :: (1, 1) :: repeat (1, 2) 1511339 ++ (5653179, 2) :: (1, 1) :: repeat (1, 2) 11874956 ++ w) 1); closearith.
  }
  (* step 55: hGRIND_even 408 *)
  apply (hsteps_trans _ (HB [57; 5] 426 1 820 ((2, 2) :: (2197, 2) :: (1, 1) :: repeat (1, 2) 4643 ++ (4018, 2) :: (1, 1) :: repeat (1, 2) 25145 ++ (740664, 2) :: (1, 1) :: repeat (1, 2) 1511339 ++ (5653179, 2) :: (1, 1) :: repeat (1, 2) 11874956 ++ w) 1)).
  {
    apply (hGRIND_even 408 [57; 5] 426 ((2197, 2) :: (1, 1) :: repeat (1, 2) 4643 ++ (4018, 2) :: (1, 1) :: repeat (1, 2) 25145 ++ (740664, 2) :: (1, 1) :: repeat (1, 2) 1511339 ++ (5653179, 2) :: (1, 1) :: repeat (1, 2) 11874956 ++ w) 1); closearith.
  }
  (* step 56: P TUP2_1 *)
  replace ((2195, 2) :: (1, 1) :: repeat (1, 2) 4643 ++ (4018, 2) :: (1, 1) :: repeat (1, 2) 25145 ++ (740664, 2) :: (1, 1) :: repeat (1, 2) 1511339 ++ (5653179, 2) :: (1, 1) :: repeat (1, 2) 11874956 ++ w) with ((2197 - 2, 2) :: (1, 1) :: repeat (1, 2) 4643 ++ (4018, 2) :: (1, 1) :: repeat (1, 2) 25145 ++ (740664, 2) :: (1, 1) :: repeat (1, 2) 1511339 ++ (5653179, 2) :: (1, 1) :: repeat (1, 2) 11874956 ++ w) by sec_eq.
  apply (sTUP2_1 [57; 5] 426 819 2197 ((1, 1) :: repeat (1, 2) 4643 ++ (4018, 2) :: (1, 1) :: repeat (1, 2) 25145 ++ (740664, 2) :: (1, 1) :: repeat (1, 2) 1511339 ++ (5653179, 2) :: (1, 1) :: repeat (1, 2) 11874956 ++ w) 1); closearith.
Qed.

(* CASCADE58b: steps 57-112 of the CASCADE58 chain. *)
Lemma CASCADE58b : forall w,
  hsteps (HC [427; 57; 5] 820 1 2 ((2195, 2) :: (1, 1) :: repeat (1, 2) 4643 ++ (4018, 2) :: (1, 1) :: repeat (1, 2) 25145 ++ (740664, 2) :: (1, 1) :: repeat (1, 2) 1511339 ++ (5653179, 2) :: (1, 1) :: repeat (1, 2) 11874956 ++ w) 1)
         (HB [135; 35; 20; 0] 244 1 71 (repeat (1, 2) 822 ++ (553, 2) :: (1, 1) :: repeat (1, 2) 4643 ++ (4018, 2) :: (1, 1) :: repeat (1, 2) 25145 ++ (740664, 2) :: (1, 1) :: repeat (1, 2) 1511339 ++ (5653179, 2) :: (1, 1) :: repeat (1, 2) 11874956 ++ w) 1).
Proof.
  intro w.
  (* step 57: P TDN *)
  apply (hsteps_trans _ (HB [427; 57; 5] 820 1 4 ((2195, 2) :: (1, 1) :: repeat (1, 2) 4643 ++ (4018, 2) :: (1, 1) :: repeat (1, 2) 25145 ++ (740664, 2) :: (1, 1) :: repeat (1, 2) 1511339 ++ (5653179, 2) :: (1, 1) :: repeat (1, 2) 11874956 ++ w) 1)).
  {
    apply (sTDN [427; 57; 5] 820 ((2195, 2) :: (1, 1) :: repeat (1, 2) 4643 ++ (4018, 2) :: (1, 1) :: repeat (1, 2) 25145 ++ (740664, 2) :: (1, 1) :: repeat (1, 2) 1511339 ++ (5653179, 2) :: (1, 1) :: repeat (1, 2) 11874956 ++ w) 1).
  }
  (* step 58: sTUP *)
  apply (hsteps_trans _ (HC [427; 57; 5] 820 3 2 ((2193, 2) :: (1, 1) :: repeat (1, 2) 4643 ++ (4018, 2) :: (1, 1) :: repeat (1, 2) 25145 ++ (740664, 2) :: (1, 1) :: repeat (1, 2) 1511339 ++ (5653179, 2) :: (1, 1) :: repeat (1, 2) 11874956 ++ w) 1)).
  {
    replace ((2193, 2) :: (1, 1) :: repeat (1, 2) 4643 ++ (4018, 2) :: (1, 1) :: repeat (1, 2) 25145 ++ (740664, 2) :: (1, 1) :: repeat (1, 2) 1511339 ++ (5653179, 2) :: (1, 1) :: repeat (1, 2) 11874956 ++ w) with ((2195 - 2, 2) :: (1, 1) :: repeat (1, 2) 4643 ++ (4018, 2) :: (1, 1) :: repeat (1, 2) 25145 ++ (740664, 2) :: (1, 1) :: repeat (1, 2) 1511339 ++ (5653179, 2) :: (1, 1) :: repeat (1, 2) 11874956 ++ w) by sec_eq.
    apply (sTUP [427; 57; 5] 820 4 2195 2 ((1, 1) :: repeat (1, 2) 4643 ++ (4018, 2) :: (1, 1) :: repeat (1, 2) 25145 ++ (740664, 2) :: (1, 1) :: repeat (1, 2) 1511339 ++ (5653179, 2) :: (1, 1) :: repeat (1, 2) 11874956 ++ w) 1); closearith.
  }
  (* step 59: DIPGRIND 820 553 *)
  apply (hsteps_trans _ (HC [427; 57; 5] 0 3 2 (repeat (1, 2) 820 ++ (553, 2) :: (1, 1) :: repeat (1, 2) 4643 ++ (4018, 2) :: (1, 1) :: repeat (1, 2) 25145 ++ (740664, 2) :: (1, 1) :: repeat (1, 2) 1511339 ++ (5653179, 2) :: (1, 1) :: repeat (1, 2) 11874956 ++ w) 1)).
  {
    apply (DIPGRIND 820 553 [427; 57; 5] ((1, 1) :: repeat (1, 2) 4643 ++ (4018, 2) :: (1, 1) :: repeat (1, 2) 25145 ++ (740664, 2) :: (1, 1) :: repeat (1, 2) 1511339 ++ (5653179, 2) :: (1, 1) :: repeat (1, 2) 11874956 ++ w) 1); closearith.
  }
  (* step 60: P PX2A *)
  apply (hsteps_trans _ (HC [5] 56 425 2 ((1, 1) :: repeat (1, 2) 822 ++ (553, 2) :: (1, 1) :: repeat (1, 2) 4643 ++ (4018, 2) :: (1, 1) :: repeat (1, 2) 25145 ++ (740664, 2) :: (1, 1) :: repeat (1, 2) 1511339 ++ (5653179, 2) :: (1, 1) :: repeat (1, 2) 11874956 ++ w) 1)).
  {
    exact (hsteps_step _ _ _ (hPX2A 424 56 [5] (repeat (1, 2) 820 ++ (553, 2) :: (1, 1) :: repeat (1, 2) 4643 ++ (4018, 2) :: (1, 1) :: repeat (1, 2) 25145 ++ (740664, 2) :: (1, 1) :: repeat (1, 2) 1511339 ++ (5653179, 2) :: (1, 1) :: repeat (1, 2) 11874956 ++ w) 1) (hsteps_refl _)).
  }
  (* step 61: P PUSH *)
  apply (hsteps_trans _ (HC [5] 55 1 2 ((423, 2) :: (1, 1) :: repeat (1, 2) 822 ++ (553, 2) :: (1, 1) :: repeat (1, 2) 4643 ++ (4018, 2) :: (1, 1) :: repeat (1, 2) 25145 ++ (740664, 2) :: (1, 1) :: repeat (1, 2) 1511339 ++ (5653179, 2) :: (1, 1) :: repeat (1, 2) 11874956 ++ w) 1)).
  {
    replace ((423, 2) :: (1, 1) :: repeat (1, 2) 822 ++ (553, 2) :: (1, 1) :: repeat (1, 2) 4643 ++ (4018, 2) :: (1, 1) :: repeat (1, 2) 25145 ++ (740664, 2) :: (1, 1) :: repeat (1, 2) 1511339 ++ (5653179, 2) :: (1, 1) :: repeat (1, 2) 11874956 ++ w) with ((425 - 2, 2) :: (1, 1) :: repeat (1, 2) 822 ++ (553, 2) :: (1, 1) :: repeat (1, 2) 4643 ++ (4018, 2) :: (1, 1) :: repeat (1, 2) 25145 ++ (740664, 2) :: (1, 1) :: repeat (1, 2) 1511339 ++ (5653179, 2) :: (1, 1) :: repeat (1, 2) 11874956 ++ w) by sec_eq.
    apply (sPUSH [5] 55 425 ((1, 1) :: repeat (1, 2) 822 ++ (553, 2) :: (1, 1) :: repeat (1, 2) 4643 ++ (4018, 2) :: (1, 1) :: repeat (1, 2) 25145 ++ (740664, 2) :: (1, 1) :: repeat (1, 2) 1511339 ++ (5653179, 2) :: (1, 1) :: repeat (1, 2) 11874956 ++ w) 1); closearith.
  }
  (* step 62: P TDN *)
  apply (hsteps_trans _ (HB [5] 55 1 4 ((423, 2) :: (1, 1) :: repeat (1, 2) 822 ++ (553, 2) :: (1, 1) :: repeat (1, 2) 4643 ++ (4018, 2) :: (1, 1) :: repeat (1, 2) 25145 ++ (740664, 2) :: (1, 1) :: repeat (1, 2) 1511339 ++ (5653179, 2) :: (1, 1) :: repeat (1, 2) 11874956 ++ w) 1)).
  {
    apply (sTDN [5] 55 ((423, 2) :: (1, 1) :: repeat (1, 2) 822 ++ (553, 2) :: (1, 1) :: repeat (1, 2) 4643 ++ (4018, 2) :: (1, 1) :: repeat (1, 2) 25145 ++ (740664, 2) :: (1, 1) :: repeat (1, 2) 1511339 ++ (5653179, 2) :: (1, 1) :: repeat (1, 2) 11874956 ++ w) 1).
  }
  (* step 63: sTUP *)
  apply (hsteps_trans _ (HC [5] 55 3 2 ((421, 2) :: (1, 1) :: repeat (1, 2) 822 ++ (553, 2) :: (1, 1) :: repeat (1, 2) 4643 ++ (4018, 2) :: (1, 1) :: repeat (1, 2) 25145 ++ (740664, 2) :: (1, 1) :: repeat (1, 2) 1511339 ++ (5653179, 2) :: (1, 1) :: repeat (1, 2) 11874956 ++ w) 1)).
  {
    replace ((421, 2) :: (1, 1) :: repeat (1, 2) 822 ++ (553, 2) :: (1, 1) :: repeat (1, 2) 4643 ++ (4018, 2) :: (1, 1) :: repeat (1, 2) 25145 ++ (740664, 2) :: (1, 1) :: repeat (1, 2) 1511339 ++ (5653179, 2) :: (1, 1) :: repeat (1, 2) 11874956 ++ w) with ((423 - 2, 2) :: (1, 1) :: repeat (1, 2) 822 ++ (553, 2) :: (1, 1) :: repeat (1, 2) 4643 ++ (4018, 2) :: (1, 1) :: repeat (1, 2) 25145 ++ (740664, 2) :: (1, 1) :: repeat (1, 2) 1511339 ++ (5653179, 2) :: (1, 1) :: repeat (1, 2) 11874956 ++ w) by sec_eq.
    apply (sTUP [5] 55 4 423 2 ((1, 1) :: repeat (1, 2) 822 ++ (553, 2) :: (1, 1) :: repeat (1, 2) 4643 ++ (4018, 2) :: (1, 1) :: repeat (1, 2) 25145 ++ (740664, 2) :: (1, 1) :: repeat (1, 2) 1511339 ++ (5653179, 2) :: (1, 1) :: repeat (1, 2) 11874956 ++ w) 1); closearith.
  }
  (* step 64: DIPGRIND 55 311 *)
  apply (hsteps_trans _ (HC [5] 0 3 2 (repeat (1, 2) 55 ++ (311, 2) :: (1, 1) :: repeat (1, 2) 822 ++ (553, 2) :: (1, 1) :: repeat (1, 2) 4643 ++ (4018, 2) :: (1, 1) :: repeat (1, 2) 25145 ++ (740664, 2) :: (1, 1) :: repeat (1, 2) 1511339 ++ (5653179, 2) :: (1, 1) :: repeat (1, 2) 11874956 ++ w) 1)).
  {
    apply (DIPGRIND 55 311 [5] ((1, 1) :: repeat (1, 2) 822 ++ (553, 2) :: (1, 1) :: repeat (1, 2) 4643 ++ (4018, 2) :: (1, 1) :: repeat (1, 2) 25145 ++ (740664, 2) :: (1, 1) :: repeat (1, 2) 1511339 ++ (5653179, 2) :: (1, 1) :: repeat (1, 2) 11874956 ++ w) 1); closearith.
  }
  (* step 65: P PX2Bgen *)
  apply (hsteps_trans _ (HB [0] 3 1 2 (repeat (1, 2) 1 ++ (1, 1) :: repeat (1, 2) 57 ++ (311, 2) :: (1, 1) :: repeat (1, 2) 822 ++ (553, 2) :: (1, 1) :: repeat (1, 2) 4643 ++ (4018, 2) :: (1, 1) :: repeat (1, 2) 25145 ++ (740664, 2) :: (1, 1) :: repeat (1, 2) 1511339 ++ (5653179, 2) :: (1, 1) :: repeat (1, 2) 11874956 ++ w) 1)).
  {
    exact (hsteps_step _ _ _ (hPX2Bgen 0 (repeat (1, 2) 55 ++ (311, 2) :: (1, 1) :: repeat (1, 2) 822 ++ (553, 2) :: (1, 1) :: repeat (1, 2) 4643 ++ (4018, 2) :: (1, 1) :: repeat (1, 2) 25145 ++ (740664, 2) :: (1, 1) :: repeat (1, 2) 1511339 ++ (5653179, 2) :: (1, 1) :: repeat (1, 2) 11874956 ++ w) 1) (hsteps_refl _)).
  }
  (* step 66: M pop12 (1,) *)
  apply (hsteps_trans _ (HB [0] 4 1 4 ((1, 1) :: repeat (1, 2) 57 ++ (311, 2) :: (1, 1) :: repeat (1, 2) 822 ++ (553, 2) :: (1, 1) :: repeat (1, 2) 4643 ++ (4018, 2) :: (1, 1) :: repeat (1, 2) 25145 ++ (740664, 2) :: (1, 1) :: repeat (1, 2) 1511339 ++ (5653179, 2) :: (1, 1) :: repeat (1, 2) 11874956 ++ w) 1)).
  {
    apply (pop12 1 [0] 3 2 ((1, 1) :: repeat (1, 2) 57 ++ (311, 2) :: (1, 1) :: repeat (1, 2) 822 ++ (553, 2) :: (1, 1) :: repeat (1, 2) 4643 ++ (4018, 2) :: (1, 1) :: repeat (1, 2) 25145 ++ (740664, 2) :: (1, 1) :: repeat (1, 2) 1511339 ++ (5653179, 2) :: (1, 1) :: repeat (1, 2) 11874956 ++ w) 1); closearith.
  }
  (* step 67: P POP *)
  apply (hsteps_trans _ (HB [0] 5 1 5 (repeat (1, 2) 57 ++ (311, 2) :: (1, 1) :: repeat (1, 2) 822 ++ (553, 2) :: (1, 1) :: repeat (1, 2) 4643 ++ (4018, 2) :: (1, 1) :: repeat (1, 2) 25145 ++ (740664, 2) :: (1, 1) :: repeat (1, 2) 1511339 ++ (5653179, 2) :: (1, 1) :: repeat (1, 2) 11874956 ++ w) 1)).
  {
    apply (sPOP1 [0] 4 4 (repeat (1, 2) 57 ++ (311, 2) :: (1, 1) :: repeat (1, 2) 822 ++ (553, 2) :: (1, 1) :: repeat (1, 2) 4643 ++ (4018, 2) :: (1, 1) :: repeat (1, 2) 25145 ++ (740664, 2) :: (1, 1) :: repeat (1, 2) 1511339 ++ (5653179, 2) :: (1, 1) :: repeat (1, 2) 11874956 ++ w) 1); closearith.
  }
  (* step 68: M pop12 (57,) *)
  apply (hsteps_trans _ (HB [0] 62 1 119 ((311, 2) :: (1, 1) :: repeat (1, 2) 822 ++ (553, 2) :: (1, 1) :: repeat (1, 2) 4643 ++ (4018, 2) :: (1, 1) :: repeat (1, 2) 25145 ++ (740664, 2) :: (1, 1) :: repeat (1, 2) 1511339 ++ (5653179, 2) :: (1, 1) :: repeat (1, 2) 11874956 ++ w) 1)).
  {
    apply (pop12 57 [0] 5 5 ((311, 2) :: (1, 1) :: repeat (1, 2) 822 ++ (553, 2) :: (1, 1) :: repeat (1, 2) 4643 ++ (4018, 2) :: (1, 1) :: repeat (1, 2) 25145 ++ (740664, 2) :: (1, 1) :: repeat (1, 2) 1511339 ++ (5653179, 2) :: (1, 1) :: repeat (1, 2) 11874956 ++ w) 1); closearith.
  }
  (* step 69: sTUP *)
  apply (hsteps_trans _ (HC [0] 62 118 2 ((309, 2) :: (1, 1) :: repeat (1, 2) 822 ++ (553, 2) :: (1, 1) :: repeat (1, 2) 4643 ++ (4018, 2) :: (1, 1) :: repeat (1, 2) 25145 ++ (740664, 2) :: (1, 1) :: repeat (1, 2) 1511339 ++ (5653179, 2) :: (1, 1) :: repeat (1, 2) 11874956 ++ w) 1)).
  {
    replace ((309, 2) :: (1, 1) :: repeat (1, 2) 822 ++ (553, 2) :: (1, 1) :: repeat (1, 2) 4643 ++ (4018, 2) :: (1, 1) :: repeat (1, 2) 25145 ++ (740664, 2) :: (1, 1) :: repeat (1, 2) 1511339 ++ (5653179, 2) :: (1, 1) :: repeat (1, 2) 11874956 ++ w) with ((311 - 2, 2) :: (1, 1) :: repeat (1, 2) 822 ++ (553, 2) :: (1, 1) :: repeat (1, 2) 4643 ++ (4018, 2) :: (1, 1) :: repeat (1, 2) 25145 ++ (740664, 2) :: (1, 1) :: repeat (1, 2) 1511339 ++ (5653179, 2) :: (1, 1) :: repeat (1, 2) 11874956 ++ w) by sec_eq.
    apply (sTUP [0] 62 119 311 2 ((1, 1) :: repeat (1, 2) 822 ++ (553, 2) :: (1, 1) :: repeat (1, 2) 4643 ++ (4018, 2) :: (1, 1) :: repeat (1, 2) 25145 ++ (740664, 2) :: (1, 1) :: repeat (1, 2) 1511339 ++ (5653179, 2) :: (1, 1) :: repeat (1, 2) 11874956 ++ w) 1); closearith.
  }
  (* step 70: hGRIND_even 57 *)
  apply (hsteps_trans _ (HB [0] 61 1 118 ((2, 2) :: (309, 2) :: (1, 1) :: repeat (1, 2) 822 ++ (553, 2) :: (1, 1) :: repeat (1, 2) 4643 ++ (4018, 2) :: (1, 1) :: repeat (1, 2) 25145 ++ (740664, 2) :: (1, 1) :: repeat (1, 2) 1511339 ++ (5653179, 2) :: (1, 1) :: repeat (1, 2) 11874956 ++ w) 1)).
  {
    apply (hGRIND_even 57 [0] 61 ((309, 2) :: (1, 1) :: repeat (1, 2) 822 ++ (553, 2) :: (1, 1) :: repeat (1, 2) 4643 ++ (4018, 2) :: (1, 1) :: repeat (1, 2) 25145 ++ (740664, 2) :: (1, 1) :: repeat (1, 2) 1511339 ++ (5653179, 2) :: (1, 1) :: repeat (1, 2) 11874956 ++ w) 1); closearith.
  }
  (* step 71: P TUP2_1 *)
  apply (hsteps_trans _ (HC [62; 0] 118 1 2 ((307, 2) :: (1, 1) :: repeat (1, 2) 822 ++ (553, 2) :: (1, 1) :: repeat (1, 2) 4643 ++ (4018, 2) :: (1, 1) :: repeat (1, 2) 25145 ++ (740664, 2) :: (1, 1) :: repeat (1, 2) 1511339 ++ (5653179, 2) :: (1, 1) :: repeat (1, 2) 11874956 ++ w) 1)).
  {
    replace ((307, 2) :: (1, 1) :: repeat (1, 2) 822 ++ (553, 2) :: (1, 1) :: repeat (1, 2) 4643 ++ (4018, 2) :: (1, 1) :: repeat (1, 2) 25145 ++ (740664, 2) :: (1, 1) :: repeat (1, 2) 1511339 ++ (5653179, 2) :: (1, 1) :: repeat (1, 2) 11874956 ++ w) with ((309 - 2, 2) :: (1, 1) :: repeat (1, 2) 822 ++ (553, 2) :: (1, 1) :: repeat (1, 2) 4643 ++ (4018, 2) :: (1, 1) :: repeat (1, 2) 25145 ++ (740664, 2) :: (1, 1) :: repeat (1, 2) 1511339 ++ (5653179, 2) :: (1, 1) :: repeat (1, 2) 11874956 ++ w) by sec_eq.
    apply (sTUP2_1 [0] 61 117 309 ((1, 1) :: repeat (1, 2) 822 ++ (553, 2) :: (1, 1) :: repeat (1, 2) 4643 ++ (4018, 2) :: (1, 1) :: repeat (1, 2) 25145 ++ (740664, 2) :: (1, 1) :: repeat (1, 2) 1511339 ++ (5653179, 2) :: (1, 1) :: repeat (1, 2) 11874956 ++ w) 1); closearith.
  }
  (* step 72: P TDN *)
  apply (hsteps_trans _ (HB [62; 0] 118 1 4 ((307, 2) :: (1, 1) :: repeat (1, 2) 822 ++ (553, 2) :: (1, 1) :: repeat (1, 2) 4643 ++ (4018, 2) :: (1, 1) :: repeat (1, 2) 25145 ++ (740664, 2) :: (1, 1) :: repeat (1, 2) 1511339 ++ (5653179, 2) :: (1, 1) :: repeat (1, 2) 11874956 ++ w) 1)).
  {
    apply (sTDN [62; 0] 118 ((307, 2) :: (1, 1) :: repeat (1, 2) 822 ++ (553, 2) :: (1, 1) :: repeat (1, 2) 4643 ++ (4018, 2) :: (1, 1) :: repeat (1, 2) 25145 ++ (740664, 2) :: (1, 1) :: repeat (1, 2) 1511339 ++ (5653179, 2) :: (1, 1) :: repeat (1, 2) 11874956 ++ w) 1).
  }
  (* step 73: sTUP *)
  apply (hsteps_trans _ (HC [62; 0] 118 3 2 ((305, 2) :: (1, 1) :: repeat (1, 2) 822 ++ (553, 2) :: (1, 1) :: repeat (1, 2) 4643 ++ (4018, 2) :: (1, 1) :: repeat (1, 2) 25145 ++ (740664, 2) :: (1, 1) :: repeat (1, 2) 1511339 ++ (5653179, 2) :: (1, 1) :: repeat (1, 2) 11874956 ++ w) 1)).
  {
    replace ((305, 2) :: (1, 1) :: repeat (1, 2) 822 ++ (553, 2) :: (1, 1) :: repeat (1, 2) 4643 ++ (4018, 2) :: (1, 1) :: repeat (1, 2) 25145 ++ (740664, 2) :: (1, 1) :: repeat (1, 2) 1511339 ++ (5653179, 2) :: (1, 1) :: repeat (1, 2) 11874956 ++ w) with ((307 - 2, 2) :: (1, 1) :: repeat (1, 2) 822 ++ (553, 2) :: (1, 1) :: repeat (1, 2) 4643 ++ (4018, 2) :: (1, 1) :: repeat (1, 2) 25145 ++ (740664, 2) :: (1, 1) :: repeat (1, 2) 1511339 ++ (5653179, 2) :: (1, 1) :: repeat (1, 2) 11874956 ++ w) by sec_eq.
    apply (sTUP [62; 0] 118 4 307 2 ((1, 1) :: repeat (1, 2) 822 ++ (553, 2) :: (1, 1) :: repeat (1, 2) 4643 ++ (4018, 2) :: (1, 1) :: repeat (1, 2) 25145 ++ (740664, 2) :: (1, 1) :: repeat (1, 2) 1511339 ++ (5653179, 2) :: (1, 1) :: repeat (1, 2) 11874956 ++ w) 1); closearith.
  }
  (* step 74: DIPGRIND 118 69 *)
  apply (hsteps_trans _ (HC [62; 0] 0 3 2 (repeat (1, 2) 118 ++ (69, 2) :: (1, 1) :: repeat (1, 2) 822 ++ (553, 2) :: (1, 1) :: repeat (1, 2) 4643 ++ (4018, 2) :: (1, 1) :: repeat (1, 2) 25145 ++ (740664, 2) :: (1, 1) :: repeat (1, 2) 1511339 ++ (5653179, 2) :: (1, 1) :: repeat (1, 2) 11874956 ++ w) 1)).
  {
    apply (DIPGRIND 118 69 [62; 0] ((1, 1) :: repeat (1, 2) 822 ++ (553, 2) :: (1, 1) :: repeat (1, 2) 4643 ++ (4018, 2) :: (1, 1) :: repeat (1, 2) 25145 ++ (740664, 2) :: (1, 1) :: repeat (1, 2) 1511339 ++ (5653179, 2) :: (1, 1) :: repeat (1, 2) 11874956 ++ w) 1); closearith.
  }
  (* step 75: P PX2A0 *)
  apply (hsteps_trans _ (HB [0] 3 1 2 ((58, 2) :: (1, 1) :: repeat (1, 2) 120 ++ (69, 2) :: (1, 1) :: repeat (1, 2) 822 ++ (553, 2) :: (1, 1) :: repeat (1, 2) 4643 ++ (4018, 2) :: (1, 1) :: repeat (1, 2) 25145 ++ (740664, 2) :: (1, 1) :: repeat (1, 2) 1511339 ++ (5653179, 2) :: (1, 1) :: repeat (1, 2) 11874956 ++ w) 1)).
  {
    exact (hsteps_step _ _ _ (hPX2A0 57 (repeat (1, 2) 118 ++ (69, 2) :: (1, 1) :: repeat (1, 2) 822 ++ (553, 2) :: (1, 1) :: repeat (1, 2) 4643 ++ (4018, 2) :: (1, 1) :: repeat (1, 2) 25145 ++ (740664, 2) :: (1, 1) :: repeat (1, 2) 1511339 ++ (5653179, 2) :: (1, 1) :: repeat (1, 2) 11874956 ++ w) 1) (hsteps_refl _)).
  }
  (* step 76: sTUP *)
  apply (hsteps_trans _ (HC [0] 3 1 2 ((56, 2) :: (1, 1) :: repeat (1, 2) 120 ++ (69, 2) :: (1, 1) :: repeat (1, 2) 822 ++ (553, 2) :: (1, 1) :: repeat (1, 2) 4643 ++ (4018, 2) :: (1, 1) :: repeat (1, 2) 25145 ++ (740664, 2) :: (1, 1) :: repeat (1, 2) 1511339 ++ (5653179, 2) :: (1, 1) :: repeat (1, 2) 11874956 ++ w) 1)).
  {
    replace ((56, 2) :: (1, 1) :: repeat (1, 2) 120 ++ (69, 2) :: (1, 1) :: repeat (1, 2) 822 ++ (553, 2) :: (1, 1) :: repeat (1, 2) 4643 ++ (4018, 2) :: (1, 1) :: repeat (1, 2) 25145 ++ (740664, 2) :: (1, 1) :: repeat (1, 2) 1511339 ++ (5653179, 2) :: (1, 1) :: repeat (1, 2) 11874956 ++ w) with ((58 - 2, 2) :: (1, 1) :: repeat (1, 2) 120 ++ (69, 2) :: (1, 1) :: repeat (1, 2) 822 ++ (553, 2) :: (1, 1) :: repeat (1, 2) 4643 ++ (4018, 2) :: (1, 1) :: repeat (1, 2) 25145 ++ (740664, 2) :: (1, 1) :: repeat (1, 2) 1511339 ++ (5653179, 2) :: (1, 1) :: repeat (1, 2) 11874956 ++ w) by sec_eq.
    apply (sTUP [0] 3 2 58 2 ((1, 1) :: repeat (1, 2) 120 ++ (69, 2) :: (1, 1) :: repeat (1, 2) 822 ++ (553, 2) :: (1, 1) :: repeat (1, 2) 4643 ++ (4018, 2) :: (1, 1) :: repeat (1, 2) 25145 ++ (740664, 2) :: (1, 1) :: repeat (1, 2) 1511339 ++ (5653179, 2) :: (1, 1) :: repeat (1, 2) 11874956 ++ w) 1); closearith.
  }
  (* step 77: P TDN *)
  apply (hsteps_trans _ (HB [0] 3 1 4 ((56, 2) :: (1, 1) :: repeat (1, 2) 120 ++ (69, 2) :: (1, 1) :: repeat (1, 2) 822 ++ (553, 2) :: (1, 1) :: repeat (1, 2) 4643 ++ (4018, 2) :: (1, 1) :: repeat (1, 2) 25145 ++ (740664, 2) :: (1, 1) :: repeat (1, 2) 1511339 ++ (5653179, 2) :: (1, 1) :: repeat (1, 2) 11874956 ++ w) 1)).
  {
    apply (sTDN [0] 3 ((56, 2) :: (1, 1) :: repeat (1, 2) 120 ++ (69, 2) :: (1, 1) :: repeat (1, 2) 822 ++ (553, 2) :: (1, 1) :: repeat (1, 2) 4643 ++ (4018, 2) :: (1, 1) :: repeat (1, 2) 25145 ++ (740664, 2) :: (1, 1) :: repeat (1, 2) 1511339 ++ (5653179, 2) :: (1, 1) :: repeat (1, 2) 11874956 ++ w) 1).
  }
  (* step 78: sTUP *)
  apply (hsteps_trans _ (HC [0] 3 3 2 ((54, 2) :: (1, 1) :: repeat (1, 2) 120 ++ (69, 2) :: (1, 1) :: repeat (1, 2) 822 ++ (553, 2) :: (1, 1) :: repeat (1, 2) 4643 ++ (4018, 2) :: (1, 1) :: repeat (1, 2) 25145 ++ (740664, 2) :: (1, 1) :: repeat (1, 2) 1511339 ++ (5653179, 2) :: (1, 1) :: repeat (1, 2) 11874956 ++ w) 1)).
  {
    replace ((54, 2) :: (1, 1) :: repeat (1, 2) 120 ++ (69, 2) :: (1, 1) :: repeat (1, 2) 822 ++ (553, 2) :: (1, 1) :: repeat (1, 2) 4643 ++ (4018, 2) :: (1, 1) :: repeat (1, 2) 25145 ++ (740664, 2) :: (1, 1) :: repeat (1, 2) 1511339 ++ (5653179, 2) :: (1, 1) :: repeat (1, 2) 11874956 ++ w) with ((56 - 2, 2) :: (1, 1) :: repeat (1, 2) 120 ++ (69, 2) :: (1, 1) :: repeat (1, 2) 822 ++ (553, 2) :: (1, 1) :: repeat (1, 2) 4643 ++ (4018, 2) :: (1, 1) :: repeat (1, 2) 25145 ++ (740664, 2) :: (1, 1) :: repeat (1, 2) 1511339 ++ (5653179, 2) :: (1, 1) :: repeat (1, 2) 11874956 ++ w) by sec_eq.
    apply (sTUP [0] 3 4 56 2 ((1, 1) :: repeat (1, 2) 120 ++ (69, 2) :: (1, 1) :: repeat (1, 2) 822 ++ (553, 2) :: (1, 1) :: repeat (1, 2) 4643 ++ (4018, 2) :: (1, 1) :: repeat (1, 2) 25145 ++ (740664, 2) :: (1, 1) :: repeat (1, 2) 1511339 ++ (5653179, 2) :: (1, 1) :: repeat (1, 2) 11874956 ++ w) 1); closearith.
  }
  (* step 79: DIPGRIND 3 48 *)
  apply (hsteps_trans _ (HC [0] 0 3 2 (repeat (1, 2) 3 ++ (48, 2) :: (1, 1) :: repeat (1, 2) 120 ++ (69, 2) :: (1, 1) :: repeat (1, 2) 822 ++ (553, 2) :: (1, 1) :: repeat (1, 2) 4643 ++ (4018, 2) :: (1, 1) :: repeat (1, 2) 25145 ++ (740664, 2) :: (1, 1) :: repeat (1, 2) 1511339 ++ (5653179, 2) :: (1, 1) :: repeat (1, 2) 11874956 ++ w) 1)).
  {
    apply (DIPGRIND 3 48 [0] ((1, 1) :: repeat (1, 2) 120 ++ (69, 2) :: (1, 1) :: repeat (1, 2) 822 ++ (553, 2) :: (1, 1) :: repeat (1, 2) 4643 ++ (4018, 2) :: (1, 1) :: repeat (1, 2) 25145 ++ (740664, 2) :: (1, 1) :: repeat (1, 2) 1511339 ++ (5653179, 2) :: (1, 1) :: repeat (1, 2) 11874956 ++ w) 1); closearith.
  }
  (* step 80: P PX2B0 *)
  apply (hsteps_trans _ (HB [] 0 1 5 (repeat (1, 2) 4 ++ (48, 2) :: (1, 1) :: repeat (1, 2) 120 ++ (69, 2) :: (1, 1) :: repeat (1, 2) 822 ++ (553, 2) :: (1, 1) :: repeat (1, 2) 4643 ++ (4018, 2) :: (1, 1) :: repeat (1, 2) 25145 ++ (740664, 2) :: (1, 1) :: repeat (1, 2) 1511339 ++ (5653179, 2) :: (1, 1) :: repeat (1, 2) 11874956 ++ w) 1)).
  {
    exact (hsteps_step _ _ _ (hPX2B0 (repeat (1, 2) 3 ++ (48, 2) :: (1, 1) :: repeat (1, 2) 120 ++ (69, 2) :: (1, 1) :: repeat (1, 2) 822 ++ (553, 2) :: (1, 1) :: repeat (1, 2) 4643 ++ (4018, 2) :: (1, 1) :: repeat (1, 2) 25145 ++ (740664, 2) :: (1, 1) :: repeat (1, 2) 1511339 ++ (5653179, 2) :: (1, 1) :: repeat (1, 2) 11874956 ++ w) 1) (hsteps_refl _)).
  }
  (* step 81: M pop12 (4,) *)
  apply (hsteps_trans _ (HB [] 4 1 13 ((48, 2) :: (1, 1) :: repeat (1, 2) 120 ++ (69, 2) :: (1, 1) :: repeat (1, 2) 822 ++ (553, 2) :: (1, 1) :: repeat (1, 2) 4643 ++ (4018, 2) :: (1, 1) :: repeat (1, 2) 25145 ++ (740664, 2) :: (1, 1) :: repeat (1, 2) 1511339 ++ (5653179, 2) :: (1, 1) :: repeat (1, 2) 11874956 ++ w) 1)).
  {
    apply (pop12 4 [] 0 5 ((48, 2) :: (1, 1) :: repeat (1, 2) 120 ++ (69, 2) :: (1, 1) :: repeat (1, 2) 822 ++ (553, 2) :: (1, 1) :: repeat (1, 2) 4643 ++ (4018, 2) :: (1, 1) :: repeat (1, 2) 25145 ++ (740664, 2) :: (1, 1) :: repeat (1, 2) 1511339 ++ (5653179, 2) :: (1, 1) :: repeat (1, 2) 11874956 ++ w) 1); closearith.
  }
  (* step 82: sTUP *)
  apply (hsteps_trans _ (HC [] 4 12 2 ((46, 2) :: (1, 1) :: repeat (1, 2) 120 ++ (69, 2) :: (1, 1) :: repeat (1, 2) 822 ++ (553, 2) :: (1, 1) :: repeat (1, 2) 4643 ++ (4018, 2) :: (1, 1) :: repeat (1, 2) 25145 ++ (740664, 2) :: (1, 1) :: repeat (1, 2) 1511339 ++ (5653179, 2) :: (1, 1) :: repeat (1, 2) 11874956 ++ w) 1)).
  {
    replace ((46, 2) :: (1, 1) :: repeat (1, 2) 120 ++ (69, 2) :: (1, 1) :: repeat (1, 2) 822 ++ (553, 2) :: (1, 1) :: repeat (1, 2) 4643 ++ (4018, 2) :: (1, 1) :: repeat (1, 2) 25145 ++ (740664, 2) :: (1, 1) :: repeat (1, 2) 1511339 ++ (5653179, 2) :: (1, 1) :: repeat (1, 2) 11874956 ++ w) with ((48 - 2, 2) :: (1, 1) :: repeat (1, 2) 120 ++ (69, 2) :: (1, 1) :: repeat (1, 2) 822 ++ (553, 2) :: (1, 1) :: repeat (1, 2) 4643 ++ (4018, 2) :: (1, 1) :: repeat (1, 2) 25145 ++ (740664, 2) :: (1, 1) :: repeat (1, 2) 1511339 ++ (5653179, 2) :: (1, 1) :: repeat (1, 2) 11874956 ++ w) by sec_eq.
    apply (sTUP [] 4 13 48 2 ((1, 1) :: repeat (1, 2) 120 ++ (69, 2) :: (1, 1) :: repeat (1, 2) 822 ++ (553, 2) :: (1, 1) :: repeat (1, 2) 4643 ++ (4018, 2) :: (1, 1) :: repeat (1, 2) 25145 ++ (740664, 2) :: (1, 1) :: repeat (1, 2) 1511339 ++ (5653179, 2) :: (1, 1) :: repeat (1, 2) 11874956 ++ w) 1); closearith.
  }
  (* step 83: P PUSH *)
  apply (hsteps_trans _ (HC [] 3 1 2 ((10, 2) :: (46, 2) :: (1, 1) :: repeat (1, 2) 120 ++ (69, 2) :: (1, 1) :: repeat (1, 2) 822 ++ (553, 2) :: (1, 1) :: repeat (1, 2) 4643 ++ (4018, 2) :: (1, 1) :: repeat (1, 2) 25145 ++ (740664, 2) :: (1, 1) :: repeat (1, 2) 1511339 ++ (5653179, 2) :: (1, 1) :: repeat (1, 2) 11874956 ++ w) 1)).
  {
    replace ((10, 2) :: (46, 2) :: (1, 1) :: repeat (1, 2) 120 ++ (69, 2) :: (1, 1) :: repeat (1, 2) 822 ++ (553, 2) :: (1, 1) :: repeat (1, 2) 4643 ++ (4018, 2) :: (1, 1) :: repeat (1, 2) 25145 ++ (740664, 2) :: (1, 1) :: repeat (1, 2) 1511339 ++ (5653179, 2) :: (1, 1) :: repeat (1, 2) 11874956 ++ w) with ((12 - 2, 2) :: (46, 2) :: (1, 1) :: repeat (1, 2) 120 ++ (69, 2) :: (1, 1) :: repeat (1, 2) 822 ++ (553, 2) :: (1, 1) :: repeat (1, 2) 4643 ++ (4018, 2) :: (1, 1) :: repeat (1, 2) 25145 ++ (740664, 2) :: (1, 1) :: repeat (1, 2) 1511339 ++ (5653179, 2) :: (1, 1) :: repeat (1, 2) 11874956 ++ w) by sec_eq.
    apply (sPUSH [] 3 12 ((46, 2) :: (1, 1) :: repeat (1, 2) 120 ++ (69, 2) :: (1, 1) :: repeat (1, 2) 822 ++ (553, 2) :: (1, 1) :: repeat (1, 2) 4643 ++ (4018, 2) :: (1, 1) :: repeat (1, 2) 25145 ++ (740664, 2) :: (1, 1) :: repeat (1, 2) 1511339 ++ (5653179, 2) :: (1, 1) :: repeat (1, 2) 11874956 ++ w) 1); closearith.
  }
  (* step 84: P TDN *)
  apply (hsteps_trans _ (HB [] 3 1 4 ((10, 2) :: (46, 2) :: (1, 1) :: repeat (1, 2) 120 ++ (69, 2) :: (1, 1) :: repeat (1, 2) 822 ++ (553, 2) :: (1, 1) :: repeat (1, 2) 4643 ++ (4018, 2) :: (1, 1) :: repeat (1, 2) 25145 ++ (740664, 2) :: (1, 1) :: repeat (1, 2) 1511339 ++ (5653179, 2) :: (1, 1) :: repeat (1, 2) 11874956 ++ w) 1)).
  {
    apply (sTDN [] 3 ((10, 2) :: (46, 2) :: (1, 1) :: repeat (1, 2) 120 ++ (69, 2) :: (1, 1) :: repeat (1, 2) 822 ++ (553, 2) :: (1, 1) :: repeat (1, 2) 4643 ++ (4018, 2) :: (1, 1) :: repeat (1, 2) 25145 ++ (740664, 2) :: (1, 1) :: repeat (1, 2) 1511339 ++ (5653179, 2) :: (1, 1) :: repeat (1, 2) 11874956 ++ w) 1).
  }
  (* step 85: sTUP *)
  apply (hsteps_trans _ (HC [] 3 3 2 ((8, 2) :: (46, 2) :: (1, 1) :: repeat (1, 2) 120 ++ (69, 2) :: (1, 1) :: repeat (1, 2) 822 ++ (553, 2) :: (1, 1) :: repeat (1, 2) 4643 ++ (4018, 2) :: (1, 1) :: repeat (1, 2) 25145 ++ (740664, 2) :: (1, 1) :: repeat (1, 2) 1511339 ++ (5653179, 2) :: (1, 1) :: repeat (1, 2) 11874956 ++ w) 1)).
  {
    replace ((8, 2) :: (46, 2) :: (1, 1) :: repeat (1, 2) 120 ++ (69, 2) :: (1, 1) :: repeat (1, 2) 822 ++ (553, 2) :: (1, 1) :: repeat (1, 2) 4643 ++ (4018, 2) :: (1, 1) :: repeat (1, 2) 25145 ++ (740664, 2) :: (1, 1) :: repeat (1, 2) 1511339 ++ (5653179, 2) :: (1, 1) :: repeat (1, 2) 11874956 ++ w) with ((10 - 2, 2) :: (46, 2) :: (1, 1) :: repeat (1, 2) 120 ++ (69, 2) :: (1, 1) :: repeat (1, 2) 822 ++ (553, 2) :: (1, 1) :: repeat (1, 2) 4643 ++ (4018, 2) :: (1, 1) :: repeat (1, 2) 25145 ++ (740664, 2) :: (1, 1) :: repeat (1, 2) 1511339 ++ (5653179, 2) :: (1, 1) :: repeat (1, 2) 11874956 ++ w) by sec_eq.
    apply (sTUP [] 3 4 10 2 ((46, 2) :: (1, 1) :: repeat (1, 2) 120 ++ (69, 2) :: (1, 1) :: repeat (1, 2) 822 ++ (553, 2) :: (1, 1) :: repeat (1, 2) 4643 ++ (4018, 2) :: (1, 1) :: repeat (1, 2) 25145 ++ (740664, 2) :: (1, 1) :: repeat (1, 2) 1511339 ++ (5653179, 2) :: (1, 1) :: repeat (1, 2) 11874956 ++ w) 1); closearith.
  }
  (* step 86: DIPGRIND 3 2 *)
  apply (hsteps_trans _ (HC [] 0 3 2 (repeat (1, 2) 3 ++ (2, 2) :: (46, 2) :: (1, 1) :: repeat (1, 2) 120 ++ (69, 2) :: (1, 1) :: repeat (1, 2) 822 ++ (553, 2) :: (1, 1) :: repeat (1, 2) 4643 ++ (4018, 2) :: (1, 1) :: repeat (1, 2) 25145 ++ (740664, 2) :: (1, 1) :: repeat (1, 2) 1511339 ++ (5653179, 2) :: (1, 1) :: repeat (1, 2) 11874956 ++ w) 1)).
  {
    apply (DIPGRIND 3 2 [] ((46, 2) :: (1, 1) :: repeat (1, 2) 120 ++ (69, 2) :: (1, 1) :: repeat (1, 2) 822 ++ (553, 2) :: (1, 1) :: repeat (1, 2) 4643 ++ (4018, 2) :: (1, 1) :: repeat (1, 2) 25145 ++ (740664, 2) :: (1, 1) :: repeat (1, 2) 1511339 ++ (5653179, 2) :: (1, 1) :: repeat (1, 2) 11874956 ++ w) 1); closearith.
  }
  (* step 87: P PUSHX *)
  apply (hsteps_trans _ (HB [] 1 1 7 (repeat (1, 2) 3 ++ (2, 2) :: (46, 2) :: (1, 1) :: repeat (1, 2) 120 ++ (69, 2) :: (1, 1) :: repeat (1, 2) 822 ++ (553, 2) :: (1, 1) :: repeat (1, 2) 4643 ++ (4018, 2) :: (1, 1) :: repeat (1, 2) 25145 ++ (740664, 2) :: (1, 1) :: repeat (1, 2) 1511339 ++ (5653179, 2) :: (1, 1) :: repeat (1, 2) 11874956 ++ w) 1)).
  {
    exact (hsteps_step _ _ _ (hPUSHX (repeat (1, 2) 3 ++ (2, 2) :: (46, 2) :: (1, 1) :: repeat (1, 2) 120 ++ (69, 2) :: (1, 1) :: repeat (1, 2) 822 ++ (553, 2) :: (1, 1) :: repeat (1, 2) 4643 ++ (4018, 2) :: (1, 1) :: repeat (1, 2) 25145 ++ (740664, 2) :: (1, 1) :: repeat (1, 2) 1511339 ++ (5653179, 2) :: (1, 1) :: repeat (1, 2) 11874956 ++ w) 1) (hsteps_refl _)).
  }
  (* step 88: M pop12 (3,) *)
  apply (hsteps_trans _ (HB [] 4 1 13 ((2, 2) :: (46, 2) :: (1, 1) :: repeat (1, 2) 120 ++ (69, 2) :: (1, 1) :: repeat (1, 2) 822 ++ (553, 2) :: (1, 1) :: repeat (1, 2) 4643 ++ (4018, 2) :: (1, 1) :: repeat (1, 2) 25145 ++ (740664, 2) :: (1, 1) :: repeat (1, 2) 1511339 ++ (5653179, 2) :: (1, 1) :: repeat (1, 2) 11874956 ++ w) 1)).
  {
    apply (pop12 3 [] 1 7 ((2, 2) :: (46, 2) :: (1, 1) :: repeat (1, 2) 120 ++ (69, 2) :: (1, 1) :: repeat (1, 2) 822 ++ (553, 2) :: (1, 1) :: repeat (1, 2) 4643 ++ (4018, 2) :: (1, 1) :: repeat (1, 2) 25145 ++ (740664, 2) :: (1, 1) :: repeat (1, 2) 1511339 ++ (5653179, 2) :: (1, 1) :: repeat (1, 2) 11874956 ++ w) 1); closearith.
  }
  (* step 89: P TUP2_1 *)
  apply (hsteps_trans _ (HC [5] 13 1 2 ((44, 2) :: (1, 1) :: repeat (1, 2) 120 ++ (69, 2) :: (1, 1) :: repeat (1, 2) 822 ++ (553, 2) :: (1, 1) :: repeat (1, 2) 4643 ++ (4018, 2) :: (1, 1) :: repeat (1, 2) 25145 ++ (740664, 2) :: (1, 1) :: repeat (1, 2) 1511339 ++ (5653179, 2) :: (1, 1) :: repeat (1, 2) 11874956 ++ w) 1)).
  {
    replace ((44, 2) :: (1, 1) :: repeat (1, 2) 120 ++ (69, 2) :: (1, 1) :: repeat (1, 2) 822 ++ (553, 2) :: (1, 1) :: repeat (1, 2) 4643 ++ (4018, 2) :: (1, 1) :: repeat (1, 2) 25145 ++ (740664, 2) :: (1, 1) :: repeat (1, 2) 1511339 ++ (5653179, 2) :: (1, 1) :: repeat (1, 2) 11874956 ++ w) with ((46 - 2, 2) :: (1, 1) :: repeat (1, 2) 120 ++ (69, 2) :: (1, 1) :: repeat (1, 2) 822 ++ (553, 2) :: (1, 1) :: repeat (1, 2) 4643 ++ (4018, 2) :: (1, 1) :: repeat (1, 2) 25145 ++ (740664, 2) :: (1, 1) :: repeat (1, 2) 1511339 ++ (5653179, 2) :: (1, 1) :: repeat (1, 2) 11874956 ++ w) by sec_eq.
    apply (sTUP2_1 [] 4 12 46 ((1, 1) :: repeat (1, 2) 120 ++ (69, 2) :: (1, 1) :: repeat (1, 2) 822 ++ (553, 2) :: (1, 1) :: repeat (1, 2) 4643 ++ (4018, 2) :: (1, 1) :: repeat (1, 2) 25145 ++ (740664, 2) :: (1, 1) :: repeat (1, 2) 1511339 ++ (5653179, 2) :: (1, 1) :: repeat (1, 2) 11874956 ++ w) 1); closearith.
  }
  (* step 90: P TDN *)
  apply (hsteps_trans _ (HB [5] 13 1 4 ((44, 2) :: (1, 1) :: repeat (1, 2) 120 ++ (69, 2) :: (1, 1) :: repeat (1, 2) 822 ++ (553, 2) :: (1, 1) :: repeat (1, 2) 4643 ++ (4018, 2) :: (1, 1) :: repeat (1, 2) 25145 ++ (740664, 2) :: (1, 1) :: repeat (1, 2) 1511339 ++ (5653179, 2) :: (1, 1) :: repeat (1, 2) 11874956 ++ w) 1)).
  {
    apply (sTDN [5] 13 ((44, 2) :: (1, 1) :: repeat (1, 2) 120 ++ (69, 2) :: (1, 1) :: repeat (1, 2) 822 ++ (553, 2) :: (1, 1) :: repeat (1, 2) 4643 ++ (4018, 2) :: (1, 1) :: repeat (1, 2) 25145 ++ (740664, 2) :: (1, 1) :: repeat (1, 2) 1511339 ++ (5653179, 2) :: (1, 1) :: repeat (1, 2) 11874956 ++ w) 1).
  }
  (* step 91: sTUP *)
  apply (hsteps_trans _ (HC [5] 13 3 2 ((42, 2) :: (1, 1) :: repeat (1, 2) 120 ++ (69, 2) :: (1, 1) :: repeat (1, 2) 822 ++ (553, 2) :: (1, 1) :: repeat (1, 2) 4643 ++ (4018, 2) :: (1, 1) :: repeat (1, 2) 25145 ++ (740664, 2) :: (1, 1) :: repeat (1, 2) 1511339 ++ (5653179, 2) :: (1, 1) :: repeat (1, 2) 11874956 ++ w) 1)).
  {
    replace ((42, 2) :: (1, 1) :: repeat (1, 2) 120 ++ (69, 2) :: (1, 1) :: repeat (1, 2) 822 ++ (553, 2) :: (1, 1) :: repeat (1, 2) 4643 ++ (4018, 2) :: (1, 1) :: repeat (1, 2) 25145 ++ (740664, 2) :: (1, 1) :: repeat (1, 2) 1511339 ++ (5653179, 2) :: (1, 1) :: repeat (1, 2) 11874956 ++ w) with ((44 - 2, 2) :: (1, 1) :: repeat (1, 2) 120 ++ (69, 2) :: (1, 1) :: repeat (1, 2) 822 ++ (553, 2) :: (1, 1) :: repeat (1, 2) 4643 ++ (4018, 2) :: (1, 1) :: repeat (1, 2) 25145 ++ (740664, 2) :: (1, 1) :: repeat (1, 2) 1511339 ++ (5653179, 2) :: (1, 1) :: repeat (1, 2) 11874956 ++ w) by sec_eq.
    apply (sTUP [5] 13 4 44 2 ((1, 1) :: repeat (1, 2) 120 ++ (69, 2) :: (1, 1) :: repeat (1, 2) 822 ++ (553, 2) :: (1, 1) :: repeat (1, 2) 4643 ++ (4018, 2) :: (1, 1) :: repeat (1, 2) 25145 ++ (740664, 2) :: (1, 1) :: repeat (1, 2) 1511339 ++ (5653179, 2) :: (1, 1) :: repeat (1, 2) 11874956 ++ w) 1); closearith.
  }
  (* step 92: DIPGRIND 13 16 *)
  apply (hsteps_trans _ (HC [5] 0 3 2 (repeat (1, 2) 13 ++ (16, 2) :: (1, 1) :: repeat (1, 2) 120 ++ (69, 2) :: (1, 1) :: repeat (1, 2) 822 ++ (553, 2) :: (1, 1) :: repeat (1, 2) 4643 ++ (4018, 2) :: (1, 1) :: repeat (1, 2) 25145 ++ (740664, 2) :: (1, 1) :: repeat (1, 2) 1511339 ++ (5653179, 2) :: (1, 1) :: repeat (1, 2) 11874956 ++ w) 1)).
  {
    apply (DIPGRIND 13 16 [5] ((1, 1) :: repeat (1, 2) 120 ++ (69, 2) :: (1, 1) :: repeat (1, 2) 822 ++ (553, 2) :: (1, 1) :: repeat (1, 2) 4643 ++ (4018, 2) :: (1, 1) :: repeat (1, 2) 25145 ++ (740664, 2) :: (1, 1) :: repeat (1, 2) 1511339 ++ (5653179, 2) :: (1, 1) :: repeat (1, 2) 11874956 ++ w) 1); closearith.
  }
  (* step 93: P PX2Bgen *)
  apply (hsteps_trans _ (HB [0] 3 1 2 (repeat (1, 2) 1 ++ (1, 1) :: repeat (1, 2) 15 ++ (16, 2) :: (1, 1) :: repeat (1, 2) 120 ++ (69, 2) :: (1, 1) :: repeat (1, 2) 822 ++ (553, 2) :: (1, 1) :: repeat (1, 2) 4643 ++ (4018, 2) :: (1, 1) :: repeat (1, 2) 25145 ++ (740664, 2) :: (1, 1) :: repeat (1, 2) 1511339 ++ (5653179, 2) :: (1, 1) :: repeat (1, 2) 11874956 ++ w) 1)).
  {
    exact (hsteps_step _ _ _ (hPX2Bgen 0 (repeat (1, 2) 13 ++ (16, 2) :: (1, 1) :: repeat (1, 2) 120 ++ (69, 2) :: (1, 1) :: repeat (1, 2) 822 ++ (553, 2) :: (1, 1) :: repeat (1, 2) 4643 ++ (4018, 2) :: (1, 1) :: repeat (1, 2) 25145 ++ (740664, 2) :: (1, 1) :: repeat (1, 2) 1511339 ++ (5653179, 2) :: (1, 1) :: repeat (1, 2) 11874956 ++ w) 1) (hsteps_refl _)).
  }
  (* step 94: M pop12 (1,) *)
  apply (hsteps_trans _ (HB [0] 4 1 4 ((1, 1) :: repeat (1, 2) 15 ++ (16, 2) :: (1, 1) :: repeat (1, 2) 120 ++ (69, 2) :: (1, 1) :: repeat (1, 2) 822 ++ (553, 2) :: (1, 1) :: repeat (1, 2) 4643 ++ (4018, 2) :: (1, 1) :: repeat (1, 2) 25145 ++ (740664, 2) :: (1, 1) :: repeat (1, 2) 1511339 ++ (5653179, 2) :: (1, 1) :: repeat (1, 2) 11874956 ++ w) 1)).
  {
    apply (pop12 1 [0] 3 2 ((1, 1) :: repeat (1, 2) 15 ++ (16, 2) :: (1, 1) :: repeat (1, 2) 120 ++ (69, 2) :: (1, 1) :: repeat (1, 2) 822 ++ (553, 2) :: (1, 1) :: repeat (1, 2) 4643 ++ (4018, 2) :: (1, 1) :: repeat (1, 2) 25145 ++ (740664, 2) :: (1, 1) :: repeat (1, 2) 1511339 ++ (5653179, 2) :: (1, 1) :: repeat (1, 2) 11874956 ++ w) 1); closearith.
  }
  (* step 95: P POP *)
  apply (hsteps_trans _ (HB [0] 5 1 5 (repeat (1, 2) 15 ++ (16, 2) :: (1, 1) :: repeat (1, 2) 120 ++ (69, 2) :: (1, 1) :: repeat (1, 2) 822 ++ (553, 2) :: (1, 1) :: repeat (1, 2) 4643 ++ (4018, 2) :: (1, 1) :: repeat (1, 2) 25145 ++ (740664, 2) :: (1, 1) :: repeat (1, 2) 1511339 ++ (5653179, 2) :: (1, 1) :: repeat (1, 2) 11874956 ++ w) 1)).
  {
    apply (sPOP1 [0] 4 4 (repeat (1, 2) 15 ++ (16, 2) :: (1, 1) :: repeat (1, 2) 120 ++ (69, 2) :: (1, 1) :: repeat (1, 2) 822 ++ (553, 2) :: (1, 1) :: repeat (1, 2) 4643 ++ (4018, 2) :: (1, 1) :: repeat (1, 2) 25145 ++ (740664, 2) :: (1, 1) :: repeat (1, 2) 1511339 ++ (5653179, 2) :: (1, 1) :: repeat (1, 2) 11874956 ++ w) 1); closearith.
  }
  (* step 96: M pop12 (15,) *)
  apply (hsteps_trans _ (HB [0] 20 1 35 ((16, 2) :: (1, 1) :: repeat (1, 2) 120 ++ (69, 2) :: (1, 1) :: repeat (1, 2) 822 ++ (553, 2) :: (1, 1) :: repeat (1, 2) 4643 ++ (4018, 2) :: (1, 1) :: repeat (1, 2) 25145 ++ (740664, 2) :: (1, 1) :: repeat (1, 2) 1511339 ++ (5653179, 2) :: (1, 1) :: repeat (1, 2) 11874956 ++ w) 1)).
  {
    apply (pop12 15 [0] 5 5 ((16, 2) :: (1, 1) :: repeat (1, 2) 120 ++ (69, 2) :: (1, 1) :: repeat (1, 2) 822 ++ (553, 2) :: (1, 1) :: repeat (1, 2) 4643 ++ (4018, 2) :: (1, 1) :: repeat (1, 2) 25145 ++ (740664, 2) :: (1, 1) :: repeat (1, 2) 1511339 ++ (5653179, 2) :: (1, 1) :: repeat (1, 2) 11874956 ++ w) 1); closearith.
  }
  (* step 97: sTUP *)
  apply (hsteps_trans _ (HC [0] 20 34 2 ((14, 2) :: (1, 1) :: repeat (1, 2) 120 ++ (69, 2) :: (1, 1) :: repeat (1, 2) 822 ++ (553, 2) :: (1, 1) :: repeat (1, 2) 4643 ++ (4018, 2) :: (1, 1) :: repeat (1, 2) 25145 ++ (740664, 2) :: (1, 1) :: repeat (1, 2) 1511339 ++ (5653179, 2) :: (1, 1) :: repeat (1, 2) 11874956 ++ w) 1)).
  {
    replace ((14, 2) :: (1, 1) :: repeat (1, 2) 120 ++ (69, 2) :: (1, 1) :: repeat (1, 2) 822 ++ (553, 2) :: (1, 1) :: repeat (1, 2) 4643 ++ (4018, 2) :: (1, 1) :: repeat (1, 2) 25145 ++ (740664, 2) :: (1, 1) :: repeat (1, 2) 1511339 ++ (5653179, 2) :: (1, 1) :: repeat (1, 2) 11874956 ++ w) with ((16 - 2, 2) :: (1, 1) :: repeat (1, 2) 120 ++ (69, 2) :: (1, 1) :: repeat (1, 2) 822 ++ (553, 2) :: (1, 1) :: repeat (1, 2) 4643 ++ (4018, 2) :: (1, 1) :: repeat (1, 2) 25145 ++ (740664, 2) :: (1, 1) :: repeat (1, 2) 1511339 ++ (5653179, 2) :: (1, 1) :: repeat (1, 2) 11874956 ++ w) by sec_eq.
    apply (sTUP [0] 20 35 16 2 ((1, 1) :: repeat (1, 2) 120 ++ (69, 2) :: (1, 1) :: repeat (1, 2) 822 ++ (553, 2) :: (1, 1) :: repeat (1, 2) 4643 ++ (4018, 2) :: (1, 1) :: repeat (1, 2) 25145 ++ (740664, 2) :: (1, 1) :: repeat (1, 2) 1511339 ++ (5653179, 2) :: (1, 1) :: repeat (1, 2) 11874956 ++ w) 1); closearith.
  }
  (* step 98: hGRIND_even 15 *)
  apply (hsteps_trans _ (HB [0] 19 1 34 ((2, 2) :: (14, 2) :: (1, 1) :: repeat (1, 2) 120 ++ (69, 2) :: (1, 1) :: repeat (1, 2) 822 ++ (553, 2) :: (1, 1) :: repeat (1, 2) 4643 ++ (4018, 2) :: (1, 1) :: repeat (1, 2) 25145 ++ (740664, 2) :: (1, 1) :: repeat (1, 2) 1511339 ++ (5653179, 2) :: (1, 1) :: repeat (1, 2) 11874956 ++ w) 1)).
  {
    apply (hGRIND_even 15 [0] 19 ((14, 2) :: (1, 1) :: repeat (1, 2) 120 ++ (69, 2) :: (1, 1) :: repeat (1, 2) 822 ++ (553, 2) :: (1, 1) :: repeat (1, 2) 4643 ++ (4018, 2) :: (1, 1) :: repeat (1, 2) 25145 ++ (740664, 2) :: (1, 1) :: repeat (1, 2) 1511339 ++ (5653179, 2) :: (1, 1) :: repeat (1, 2) 11874956 ++ w) 1); closearith.
  }
  (* step 99: P TUP2_1 *)
  apply (hsteps_trans _ (HC [20; 0] 34 1 2 ((12, 2) :: (1, 1) :: repeat (1, 2) 120 ++ (69, 2) :: (1, 1) :: repeat (1, 2) 822 ++ (553, 2) :: (1, 1) :: repeat (1, 2) 4643 ++ (4018, 2) :: (1, 1) :: repeat (1, 2) 25145 ++ (740664, 2) :: (1, 1) :: repeat (1, 2) 1511339 ++ (5653179, 2) :: (1, 1) :: repeat (1, 2) 11874956 ++ w) 1)).
  {
    replace ((12, 2) :: (1, 1) :: repeat (1, 2) 120 ++ (69, 2) :: (1, 1) :: repeat (1, 2) 822 ++ (553, 2) :: (1, 1) :: repeat (1, 2) 4643 ++ (4018, 2) :: (1, 1) :: repeat (1, 2) 25145 ++ (740664, 2) :: (1, 1) :: repeat (1, 2) 1511339 ++ (5653179, 2) :: (1, 1) :: repeat (1, 2) 11874956 ++ w) with ((14 - 2, 2) :: (1, 1) :: repeat (1, 2) 120 ++ (69, 2) :: (1, 1) :: repeat (1, 2) 822 ++ (553, 2) :: (1, 1) :: repeat (1, 2) 4643 ++ (4018, 2) :: (1, 1) :: repeat (1, 2) 25145 ++ (740664, 2) :: (1, 1) :: repeat (1, 2) 1511339 ++ (5653179, 2) :: (1, 1) :: repeat (1, 2) 11874956 ++ w) by sec_eq.
    apply (sTUP2_1 [0] 19 33 14 ((1, 1) :: repeat (1, 2) 120 ++ (69, 2) :: (1, 1) :: repeat (1, 2) 822 ++ (553, 2) :: (1, 1) :: repeat (1, 2) 4643 ++ (4018, 2) :: (1, 1) :: repeat (1, 2) 25145 ++ (740664, 2) :: (1, 1) :: repeat (1, 2) 1511339 ++ (5653179, 2) :: (1, 1) :: repeat (1, 2) 11874956 ++ w) 1); closearith.
  }
  (* step 100: P TDN *)
  apply (hsteps_trans _ (HB [20; 0] 34 1 4 ((12, 2) :: (1, 1) :: repeat (1, 2) 120 ++ (69, 2) :: (1, 1) :: repeat (1, 2) 822 ++ (553, 2) :: (1, 1) :: repeat (1, 2) 4643 ++ (4018, 2) :: (1, 1) :: repeat (1, 2) 25145 ++ (740664, 2) :: (1, 1) :: repeat (1, 2) 1511339 ++ (5653179, 2) :: (1, 1) :: repeat (1, 2) 11874956 ++ w) 1)).
  {
    apply (sTDN [20; 0] 34 ((12, 2) :: (1, 1) :: repeat (1, 2) 120 ++ (69, 2) :: (1, 1) :: repeat (1, 2) 822 ++ (553, 2) :: (1, 1) :: repeat (1, 2) 4643 ++ (4018, 2) :: (1, 1) :: repeat (1, 2) 25145 ++ (740664, 2) :: (1, 1) :: repeat (1, 2) 1511339 ++ (5653179, 2) :: (1, 1) :: repeat (1, 2) 11874956 ++ w) 1).
  }
  (* step 101: sTUP *)
  apply (hsteps_trans _ (HC [20; 0] 34 3 2 ((10, 2) :: (1, 1) :: repeat (1, 2) 120 ++ (69, 2) :: (1, 1) :: repeat (1, 2) 822 ++ (553, 2) :: (1, 1) :: repeat (1, 2) 4643 ++ (4018, 2) :: (1, 1) :: repeat (1, 2) 25145 ++ (740664, 2) :: (1, 1) :: repeat (1, 2) 1511339 ++ (5653179, 2) :: (1, 1) :: repeat (1, 2) 11874956 ++ w) 1)).
  {
    replace ((10, 2) :: (1, 1) :: repeat (1, 2) 120 ++ (69, 2) :: (1, 1) :: repeat (1, 2) 822 ++ (553, 2) :: (1, 1) :: repeat (1, 2) 4643 ++ (4018, 2) :: (1, 1) :: repeat (1, 2) 25145 ++ (740664, 2) :: (1, 1) :: repeat (1, 2) 1511339 ++ (5653179, 2) :: (1, 1) :: repeat (1, 2) 11874956 ++ w) with ((12 - 2, 2) :: (1, 1) :: repeat (1, 2) 120 ++ (69, 2) :: (1, 1) :: repeat (1, 2) 822 ++ (553, 2) :: (1, 1) :: repeat (1, 2) 4643 ++ (4018, 2) :: (1, 1) :: repeat (1, 2) 25145 ++ (740664, 2) :: (1, 1) :: repeat (1, 2) 1511339 ++ (5653179, 2) :: (1, 1) :: repeat (1, 2) 11874956 ++ w) by sec_eq.
    apply (sTUP [20; 0] 34 4 12 2 ((1, 1) :: repeat (1, 2) 120 ++ (69, 2) :: (1, 1) :: repeat (1, 2) 822 ++ (553, 2) :: (1, 1) :: repeat (1, 2) 4643 ++ (4018, 2) :: (1, 1) :: repeat (1, 2) 25145 ++ (740664, 2) :: (1, 1) :: repeat (1, 2) 1511339 ++ (5653179, 2) :: (1, 1) :: repeat (1, 2) 11874956 ++ w) 1); closearith.
  }
  (* step 102: CLEANG_even 4 *)
  apply (hsteps_trans _ (HB [20; 0] 34 1 14 ((2, 2) :: (1, 1) :: repeat (1, 2) 120 ++ (69, 2) :: (1, 1) :: repeat (1, 2) 822 ++ (553, 2) :: (1, 1) :: repeat (1, 2) 4643 ++ (4018, 2) :: (1, 1) :: repeat (1, 2) 25145 ++ (740664, 2) :: (1, 1) :: repeat (1, 2) 1511339 ++ (5653179, 2) :: (1, 1) :: repeat (1, 2) 11874956 ++ w) 1)).
  {
    apply (CLEANG_even 4 [20; 0] 34 ((1, 1) :: repeat (1, 2) 120 ++ (69, 2) :: (1, 1) :: repeat (1, 2) 822 ++ (553, 2) :: (1, 1) :: repeat (1, 2) 4643 ++ (4018, 2) :: (1, 1) :: repeat (1, 2) 25145 ++ (740664, 2) :: (1, 1) :: repeat (1, 2) 1511339 ++ (5653179, 2) :: (1, 1) :: repeat (1, 2) 11874956 ++ w) 1); closearith.
  }
  (* step 103: P TRANS2_1 *)
  apply (hsteps_trans _ (HB [35; 20; 0] 15 1 3 (repeat (1, 2) 120 ++ (69, 2) :: (1, 1) :: repeat (1, 2) 822 ++ (553, 2) :: (1, 1) :: repeat (1, 2) 4643 ++ (4018, 2) :: (1, 1) :: repeat (1, 2) 25145 ++ (740664, 2) :: (1, 1) :: repeat (1, 2) 1511339 ++ (5653179, 2) :: (1, 1) :: repeat (1, 2) 11874956 ++ w) 1)).
  {
    apply (sTRANS2_1 [20; 0] 34 13 1 (repeat (1, 2) 120 ++ (69, 2) :: (1, 1) :: repeat (1, 2) 822 ++ (553, 2) :: (1, 1) :: repeat (1, 2) 4643 ++ (4018, 2) :: (1, 1) :: repeat (1, 2) 25145 ++ (740664, 2) :: (1, 1) :: repeat (1, 2) 1511339 ++ (5653179, 2) :: (1, 1) :: repeat (1, 2) 11874956 ++ w) 1); closearith.
  }
  (* step 104: M pop12 (120,) *)
  apply (hsteps_trans _ (HB [35; 20; 0] 135 1 243 ((69, 2) :: (1, 1) :: repeat (1, 2) 822 ++ (553, 2) :: (1, 1) :: repeat (1, 2) 4643 ++ (4018, 2) :: (1, 1) :: repeat (1, 2) 25145 ++ (740664, 2) :: (1, 1) :: repeat (1, 2) 1511339 ++ (5653179, 2) :: (1, 1) :: repeat (1, 2) 11874956 ++ w) 1)).
  {
    apply (pop12 120 [35; 20; 0] 15 3 ((69, 2) :: (1, 1) :: repeat (1, 2) 822 ++ (553, 2) :: (1, 1) :: repeat (1, 2) 4643 ++ (4018, 2) :: (1, 1) :: repeat (1, 2) 25145 ++ (740664, 2) :: (1, 1) :: repeat (1, 2) 1511339 ++ (5653179, 2) :: (1, 1) :: repeat (1, 2) 11874956 ++ w) 1); closearith.
  }
  (* step 105: sTUP *)
  apply (hsteps_trans _ (HC [35; 20; 0] 135 242 2 ((67, 2) :: (1, 1) :: repeat (1, 2) 822 ++ (553, 2) :: (1, 1) :: repeat (1, 2) 4643 ++ (4018, 2) :: (1, 1) :: repeat (1, 2) 25145 ++ (740664, 2) :: (1, 1) :: repeat (1, 2) 1511339 ++ (5653179, 2) :: (1, 1) :: repeat (1, 2) 11874956 ++ w) 1)).
  {
    replace ((67, 2) :: (1, 1) :: repeat (1, 2) 822 ++ (553, 2) :: (1, 1) :: repeat (1, 2) 4643 ++ (4018, 2) :: (1, 1) :: repeat (1, 2) 25145 ++ (740664, 2) :: (1, 1) :: repeat (1, 2) 1511339 ++ (5653179, 2) :: (1, 1) :: repeat (1, 2) 11874956 ++ w) with ((69 - 2, 2) :: (1, 1) :: repeat (1, 2) 822 ++ (553, 2) :: (1, 1) :: repeat (1, 2) 4643 ++ (4018, 2) :: (1, 1) :: repeat (1, 2) 25145 ++ (740664, 2) :: (1, 1) :: repeat (1, 2) 1511339 ++ (5653179, 2) :: (1, 1) :: repeat (1, 2) 11874956 ++ w) by sec_eq.
    apply (sTUP [35; 20; 0] 135 243 69 2 ((1, 1) :: repeat (1, 2) 822 ++ (553, 2) :: (1, 1) :: repeat (1, 2) 4643 ++ (4018, 2) :: (1, 1) :: repeat (1, 2) 25145 ++ (740664, 2) :: (1, 1) :: repeat (1, 2) 1511339 ++ (5653179, 2) :: (1, 1) :: repeat (1, 2) 11874956 ++ w) 1); closearith.
  }
  (* step 106: hGRIND_even 119 *)
  apply (hsteps_trans _ (HB [35; 20; 0] 134 1 242 ((2, 2) :: (67, 2) :: (1, 1) :: repeat (1, 2) 822 ++ (553, 2) :: (1, 1) :: repeat (1, 2) 4643 ++ (4018, 2) :: (1, 1) :: repeat (1, 2) 25145 ++ (740664, 2) :: (1, 1) :: repeat (1, 2) 1511339 ++ (5653179, 2) :: (1, 1) :: repeat (1, 2) 11874956 ++ w) 1)).
  {
    apply (hGRIND_even 119 [35; 20; 0] 134 ((67, 2) :: (1, 1) :: repeat (1, 2) 822 ++ (553, 2) :: (1, 1) :: repeat (1, 2) 4643 ++ (4018, 2) :: (1, 1) :: repeat (1, 2) 25145 ++ (740664, 2) :: (1, 1) :: repeat (1, 2) 1511339 ++ (5653179, 2) :: (1, 1) :: repeat (1, 2) 11874956 ++ w) 1); closearith.
  }
  (* step 107: P TUP2_1 *)
  apply (hsteps_trans _ (HC [135; 35; 20; 0] 242 1 2 ((65, 2) :: (1, 1) :: repeat (1, 2) 822 ++ (553, 2) :: (1, 1) :: repeat (1, 2) 4643 ++ (4018, 2) :: (1, 1) :: repeat (1, 2) 25145 ++ (740664, 2) :: (1, 1) :: repeat (1, 2) 1511339 ++ (5653179, 2) :: (1, 1) :: repeat (1, 2) 11874956 ++ w) 1)).
  {
    replace ((65, 2) :: (1, 1) :: repeat (1, 2) 822 ++ (553, 2) :: (1, 1) :: repeat (1, 2) 4643 ++ (4018, 2) :: (1, 1) :: repeat (1, 2) 25145 ++ (740664, 2) :: (1, 1) :: repeat (1, 2) 1511339 ++ (5653179, 2) :: (1, 1) :: repeat (1, 2) 11874956 ++ w) with ((67 - 2, 2) :: (1, 1) :: repeat (1, 2) 822 ++ (553, 2) :: (1, 1) :: repeat (1, 2) 4643 ++ (4018, 2) :: (1, 1) :: repeat (1, 2) 25145 ++ (740664, 2) :: (1, 1) :: repeat (1, 2) 1511339 ++ (5653179, 2) :: (1, 1) :: repeat (1, 2) 11874956 ++ w) by sec_eq.
    apply (sTUP2_1 [35; 20; 0] 134 241 67 ((1, 1) :: repeat (1, 2) 822 ++ (553, 2) :: (1, 1) :: repeat (1, 2) 4643 ++ (4018, 2) :: (1, 1) :: repeat (1, 2) 25145 ++ (740664, 2) :: (1, 1) :: repeat (1, 2) 1511339 ++ (5653179, 2) :: (1, 1) :: repeat (1, 2) 11874956 ++ w) 1); closearith.
  }
  (* step 108: P TDN *)
  apply (hsteps_trans _ (HB [135; 35; 20; 0] 242 1 4 ((65, 2) :: (1, 1) :: repeat (1, 2) 822 ++ (553, 2) :: (1, 1) :: repeat (1, 2) 4643 ++ (4018, 2) :: (1, 1) :: repeat (1, 2) 25145 ++ (740664, 2) :: (1, 1) :: repeat (1, 2) 1511339 ++ (5653179, 2) :: (1, 1) :: repeat (1, 2) 11874956 ++ w) 1)).
  {
    apply (sTDN [135; 35; 20; 0] 242 ((65, 2) :: (1, 1) :: repeat (1, 2) 822 ++ (553, 2) :: (1, 1) :: repeat (1, 2) 4643 ++ (4018, 2) :: (1, 1) :: repeat (1, 2) 25145 ++ (740664, 2) :: (1, 1) :: repeat (1, 2) 1511339 ++ (5653179, 2) :: (1, 1) :: repeat (1, 2) 11874956 ++ w) 1).
  }
  (* step 109: sTUP *)
  apply (hsteps_trans _ (HC [135; 35; 20; 0] 242 3 2 ((63, 2) :: (1, 1) :: repeat (1, 2) 822 ++ (553, 2) :: (1, 1) :: repeat (1, 2) 4643 ++ (4018, 2) :: (1, 1) :: repeat (1, 2) 25145 ++ (740664, 2) :: (1, 1) :: repeat (1, 2) 1511339 ++ (5653179, 2) :: (1, 1) :: repeat (1, 2) 11874956 ++ w) 1)).
  {
    replace ((63, 2) :: (1, 1) :: repeat (1, 2) 822 ++ (553, 2) :: (1, 1) :: repeat (1, 2) 4643 ++ (4018, 2) :: (1, 1) :: repeat (1, 2) 25145 ++ (740664, 2) :: (1, 1) :: repeat (1, 2) 1511339 ++ (5653179, 2) :: (1, 1) :: repeat (1, 2) 11874956 ++ w) with ((65 - 2, 2) :: (1, 1) :: repeat (1, 2) 822 ++ (553, 2) :: (1, 1) :: repeat (1, 2) 4643 ++ (4018, 2) :: (1, 1) :: repeat (1, 2) 25145 ++ (740664, 2) :: (1, 1) :: repeat (1, 2) 1511339 ++ (5653179, 2) :: (1, 1) :: repeat (1, 2) 11874956 ++ w) by sec_eq.
    apply (sTUP [135; 35; 20; 0] 242 4 65 2 ((1, 1) :: repeat (1, 2) 822 ++ (553, 2) :: (1, 1) :: repeat (1, 2) 4643 ++ (4018, 2) :: (1, 1) :: repeat (1, 2) 25145 ++ (740664, 2) :: (1, 1) :: repeat (1, 2) 1511339 ++ (5653179, 2) :: (1, 1) :: repeat (1, 2) 11874956 ++ w) 1); closearith.
  }
  (* step 110: CLEANG_odd 30 *)
  apply (hsteps_trans _ (HB [135; 35; 20; 0] 242 1 68 (repeat (1, 2) 1 ++ (1, 1) :: repeat (1, 2) 822 ++ (553, 2) :: (1, 1) :: repeat (1, 2) 4643 ++ (4018, 2) :: (1, 1) :: repeat (1, 2) 25145 ++ (740664, 2) :: (1, 1) :: repeat (1, 2) 1511339 ++ (5653179, 2) :: (1, 1) :: repeat (1, 2) 11874956 ++ w) 1)).
  {
    replace (repeat (1, 2) 1 ++ (1, 1) :: repeat (1, 2) 822 ++ (553, 2) :: (1, 1) :: repeat (1, 2) 4643 ++ (4018, 2) :: (1, 1) :: repeat (1, 2) 25145 ++ (740664, 2) :: (1, 1) :: repeat (1, 2) 1511339 ++ (5653179, 2) :: (1, 1) :: repeat (1, 2) 11874956 ++ w) with ((1, 2) :: (1, 1) :: repeat (1, 2) 822 ++ (553, 2) :: (1, 1) :: repeat (1, 2) 4643 ++ (4018, 2) :: (1, 1) :: repeat (1, 2) 25145 ++ (740664, 2) :: (1, 1) :: repeat (1, 2) 1511339 ++ (5653179, 2) :: (1, 1) :: repeat (1, 2) 11874956 ++ w) by sec_eq.
    apply (CLEANG_odd 30 [135; 35; 20; 0] 242 ((1, 1) :: repeat (1, 2) 822 ++ (553, 2) :: (1, 1) :: repeat (1, 2) 4643 ++ (4018, 2) :: (1, 1) :: repeat (1, 2) 25145 ++ (740664, 2) :: (1, 1) :: repeat (1, 2) 1511339 ++ (5653179, 2) :: (1, 1) :: repeat (1, 2) 11874956 ++ w) 1); closearith.
  }
  (* step 111: M pop12 (1,) *)
  apply (hsteps_trans _ (HB [135; 35; 20; 0] 243 1 70 ((1, 1) :: repeat (1, 2) 822 ++ (553, 2) :: (1, 1) :: repeat (1, 2) 4643 ++ (4018, 2) :: (1, 1) :: repeat (1, 2) 25145 ++ (740664, 2) :: (1, 1) :: repeat (1, 2) 1511339 ++ (5653179, 2) :: (1, 1) :: repeat (1, 2) 11874956 ++ w) 1)).
  {
    apply (pop12 1 [135; 35; 20; 0] 242 68 ((1, 1) :: repeat (1, 2) 822 ++ (553, 2) :: (1, 1) :: repeat (1, 2) 4643 ++ (4018, 2) :: (1, 1) :: repeat (1, 2) 25145 ++ (740664, 2) :: (1, 1) :: repeat (1, 2) 1511339 ++ (5653179, 2) :: (1, 1) :: repeat (1, 2) 11874956 ++ w) 1); closearith.
  }
  (* step 112: P POP *)
  apply (sPOP1 [135; 35; 20; 0] 243 70 (repeat (1, 2) 822 ++ (553, 2) :: (1, 1) :: repeat (1, 2) 4643 ++ (4018, 2) :: (1, 1) :: repeat (1, 2) 25145 ++ (740664, 2) :: (1, 1) :: repeat (1, 2) 1511339 ++ (5653179, 2) :: (1, 1) :: repeat (1, 2) 11874956 ++ w) 1); closearith.
Qed.

(* CASCADE58c: steps 113-168 of the CASCADE58 chain. *)
Lemma CASCADE58c : forall w,
  hsteps (HB [135; 35; 20; 0] 244 1 71 (repeat (1, 2) 822 ++ (553, 2) :: (1, 1) :: repeat (1, 2) 4643 ++ (4018, 2) :: (1, 1) :: repeat (1, 2) 25145 ++ (740664, 2) :: (1, 1) :: repeat (1, 2) 1511339 ++ (5653179, 2) :: (1, 1) :: repeat (1, 2) 11874956 ++ w) 1)
         (HB [14; 5] 5 1 3 (repeat (1, 2) 35 ++ (63, 2) :: (1, 1) :: repeat (1, 2) 1066 ++ (4225, 2) :: (1, 1) :: repeat (1, 2) 9841 ++ (9478, 2) :: (1, 1) :: repeat (1, 2) 50294 ++ (640074, 2) :: (1, 1) :: repeat (1, 2) 1511339 ++ (5653179, 2) :: (1, 1) :: repeat (1, 2) 11874956 ++ w) 1).
Proof.
  intro w.
  (* step 113: M pop12 (822,) *)
  apply (hsteps_trans _ (HB [135; 35; 20; 0] 1066 1 1715 ((553, 2) :: (1, 1) :: repeat (1, 2) 4643 ++ (4018, 2) :: (1, 1) :: repeat (1, 2) 25145 ++ (740664, 2) :: (1, 1) :: repeat (1, 2) 1511339 ++ (5653179, 2) :: (1, 1) :: repeat (1, 2) 11874956 ++ w) 1)).
  {
    apply (pop12 822 [135; 35; 20; 0] 244 71 ((553, 2) :: (1, 1) :: repeat (1, 2) 4643 ++ (4018, 2) :: (1, 1) :: repeat (1, 2) 25145 ++ (740664, 2) :: (1, 1) :: repeat (1, 2) 1511339 ++ (5653179, 2) :: (1, 1) :: repeat (1, 2) 11874956 ++ w) 1); closearith.
  }
  (* step 114: sTUP *)
  apply (hsteps_trans _ (HC [135; 35; 20; 0] 1066 1714 2 ((551, 2) :: (1, 1) :: repeat (1, 2) 4643 ++ (4018, 2) :: (1, 1) :: repeat (1, 2) 25145 ++ (740664, 2) :: (1, 1) :: repeat (1, 2) 1511339 ++ (5653179, 2) :: (1, 1) :: repeat (1, 2) 11874956 ++ w) 1)).
  {
    replace ((551, 2) :: (1, 1) :: repeat (1, 2) 4643 ++ (4018, 2) :: (1, 1) :: repeat (1, 2) 25145 ++ (740664, 2) :: (1, 1) :: repeat (1, 2) 1511339 ++ (5653179, 2) :: (1, 1) :: repeat (1, 2) 11874956 ++ w) with ((553 - 2, 2) :: (1, 1) :: repeat (1, 2) 4643 ++ (4018, 2) :: (1, 1) :: repeat (1, 2) 25145 ++ (740664, 2) :: (1, 1) :: repeat (1, 2) 1511339 ++ (5653179, 2) :: (1, 1) :: repeat (1, 2) 11874956 ++ w) by sec_eq.
    apply (sTUP [135; 35; 20; 0] 1066 1715 553 2 ((1, 1) :: repeat (1, 2) 4643 ++ (4018, 2) :: (1, 1) :: repeat (1, 2) 25145 ++ (740664, 2) :: (1, 1) :: repeat (1, 2) 1511339 ++ (5653179, 2) :: (1, 1) :: repeat (1, 2) 11874956 ++ w) 1); closearith.
  }
  (* step 115: hGRIND_even 855 *)
  apply (hsteps_trans _ (HB [135; 35; 20; 0] 1065 1 1714 ((2, 2) :: (551, 2) :: (1, 1) :: repeat (1, 2) 4643 ++ (4018, 2) :: (1, 1) :: repeat (1, 2) 25145 ++ (740664, 2) :: (1, 1) :: repeat (1, 2) 1511339 ++ (5653179, 2) :: (1, 1) :: repeat (1, 2) 11874956 ++ w) 1)).
  {
    apply (hGRIND_even 855 [135; 35; 20; 0] 1065 ((551, 2) :: (1, 1) :: repeat (1, 2) 4643 ++ (4018, 2) :: (1, 1) :: repeat (1, 2) 25145 ++ (740664, 2) :: (1, 1) :: repeat (1, 2) 1511339 ++ (5653179, 2) :: (1, 1) :: repeat (1, 2) 11874956 ++ w) 1); closearith.
  }
  (* step 116: P TUP2_1 *)
  apply (hsteps_trans _ (HC [1066; 135; 35; 20; 0] 1714 1 2 ((549, 2) :: (1, 1) :: repeat (1, 2) 4643 ++ (4018, 2) :: (1, 1) :: repeat (1, 2) 25145 ++ (740664, 2) :: (1, 1) :: repeat (1, 2) 1511339 ++ (5653179, 2) :: (1, 1) :: repeat (1, 2) 11874956 ++ w) 1)).
  {
    replace ((549, 2) :: (1, 1) :: repeat (1, 2) 4643 ++ (4018, 2) :: (1, 1) :: repeat (1, 2) 25145 ++ (740664, 2) :: (1, 1) :: repeat (1, 2) 1511339 ++ (5653179, 2) :: (1, 1) :: repeat (1, 2) 11874956 ++ w) with ((551 - 2, 2) :: (1, 1) :: repeat (1, 2) 4643 ++ (4018, 2) :: (1, 1) :: repeat (1, 2) 25145 ++ (740664, 2) :: (1, 1) :: repeat (1, 2) 1511339 ++ (5653179, 2) :: (1, 1) :: repeat (1, 2) 11874956 ++ w) by sec_eq.
    apply (sTUP2_1 [135; 35; 20; 0] 1065 1713 551 ((1, 1) :: repeat (1, 2) 4643 ++ (4018, 2) :: (1, 1) :: repeat (1, 2) 25145 ++ (740664, 2) :: (1, 1) :: repeat (1, 2) 1511339 ++ (5653179, 2) :: (1, 1) :: repeat (1, 2) 11874956 ++ w) 1); closearith.
  }
  (* step 117: P TDN *)
  apply (hsteps_trans _ (HB [1066; 135; 35; 20; 0] 1714 1 4 ((549, 2) :: (1, 1) :: repeat (1, 2) 4643 ++ (4018, 2) :: (1, 1) :: repeat (1, 2) 25145 ++ (740664, 2) :: (1, 1) :: repeat (1, 2) 1511339 ++ (5653179, 2) :: (1, 1) :: repeat (1, 2) 11874956 ++ w) 1)).
  {
    apply (sTDN [1066; 135; 35; 20; 0] 1714 ((549, 2) :: (1, 1) :: repeat (1, 2) 4643 ++ (4018, 2) :: (1, 1) :: repeat (1, 2) 25145 ++ (740664, 2) :: (1, 1) :: repeat (1, 2) 1511339 ++ (5653179, 2) :: (1, 1) :: repeat (1, 2) 11874956 ++ w) 1).
  }
  (* step 118: sTUP *)
  apply (hsteps_trans _ (HC [1066; 135; 35; 20; 0] 1714 3 2 ((547, 2) :: (1, 1) :: repeat (1, 2) 4643 ++ (4018, 2) :: (1, 1) :: repeat (1, 2) 25145 ++ (740664, 2) :: (1, 1) :: repeat (1, 2) 1511339 ++ (5653179, 2) :: (1, 1) :: repeat (1, 2) 11874956 ++ w) 1)).
  {
    replace ((547, 2) :: (1, 1) :: repeat (1, 2) 4643 ++ (4018, 2) :: (1, 1) :: repeat (1, 2) 25145 ++ (740664, 2) :: (1, 1) :: repeat (1, 2) 1511339 ++ (5653179, 2) :: (1, 1) :: repeat (1, 2) 11874956 ++ w) with ((549 - 2, 2) :: (1, 1) :: repeat (1, 2) 4643 ++ (4018, 2) :: (1, 1) :: repeat (1, 2) 25145 ++ (740664, 2) :: (1, 1) :: repeat (1, 2) 1511339 ++ (5653179, 2) :: (1, 1) :: repeat (1, 2) 11874956 ++ w) by sec_eq.
    apply (sTUP [1066; 135; 35; 20; 0] 1714 4 549 2 ((1, 1) :: repeat (1, 2) 4643 ++ (4018, 2) :: (1, 1) :: repeat (1, 2) 25145 ++ (740664, 2) :: (1, 1) :: repeat (1, 2) 1511339 ++ (5653179, 2) :: (1, 1) :: repeat (1, 2) 11874956 ++ w) 1); closearith.
  }
  (* step 119: CLEANG_odd 272 *)
  apply (hsteps_trans _ (HB [1066; 135; 35; 20; 0] 1714 1 552 (repeat (1, 2) 1 ++ (1, 1) :: repeat (1, 2) 4643 ++ (4018, 2) :: (1, 1) :: repeat (1, 2) 25145 ++ (740664, 2) :: (1, 1) :: repeat (1, 2) 1511339 ++ (5653179, 2) :: (1, 1) :: repeat (1, 2) 11874956 ++ w) 1)).
  {
    replace (repeat (1, 2) 1 ++ (1, 1) :: repeat (1, 2) 4643 ++ (4018, 2) :: (1, 1) :: repeat (1, 2) 25145 ++ (740664, 2) :: (1, 1) :: repeat (1, 2) 1511339 ++ (5653179, 2) :: (1, 1) :: repeat (1, 2) 11874956 ++ w) with ((1, 2) :: (1, 1) :: repeat (1, 2) 4643 ++ (4018, 2) :: (1, 1) :: repeat (1, 2) 25145 ++ (740664, 2) :: (1, 1) :: repeat (1, 2) 1511339 ++ (5653179, 2) :: (1, 1) :: repeat (1, 2) 11874956 ++ w) by sec_eq.
    apply (CLEANG_odd 272 [1066; 135; 35; 20; 0] 1714 ((1, 1) :: repeat (1, 2) 4643 ++ (4018, 2) :: (1, 1) :: repeat (1, 2) 25145 ++ (740664, 2) :: (1, 1) :: repeat (1, 2) 1511339 ++ (5653179, 2) :: (1, 1) :: repeat (1, 2) 11874956 ++ w) 1); closearith.
  }
  (* step 120: M pop12 (1,) *)
  apply (hsteps_trans _ (HB [1066; 135; 35; 20; 0] 1715 1 554 ((1, 1) :: repeat (1, 2) 4643 ++ (4018, 2) :: (1, 1) :: repeat (1, 2) 25145 ++ (740664, 2) :: (1, 1) :: repeat (1, 2) 1511339 ++ (5653179, 2) :: (1, 1) :: repeat (1, 2) 11874956 ++ w) 1)).
  {
    apply (pop12 1 [1066; 135; 35; 20; 0] 1714 552 ((1, 1) :: repeat (1, 2) 4643 ++ (4018, 2) :: (1, 1) :: repeat (1, 2) 25145 ++ (740664, 2) :: (1, 1) :: repeat (1, 2) 1511339 ++ (5653179, 2) :: (1, 1) :: repeat (1, 2) 11874956 ++ w) 1); closearith.
  }
  (* step 121: P POP *)
  apply (hsteps_trans _ (HB [1066; 135; 35; 20; 0] 1716 1 555 (repeat (1, 2) 4643 ++ (4018, 2) :: (1, 1) :: repeat (1, 2) 25145 ++ (740664, 2) :: (1, 1) :: repeat (1, 2) 1511339 ++ (5653179, 2) :: (1, 1) :: repeat (1, 2) 11874956 ++ w) 1)).
  {
    apply (sPOP1 [1066; 135; 35; 20; 0] 1715 554 (repeat (1, 2) 4643 ++ (4018, 2) :: (1, 1) :: repeat (1, 2) 25145 ++ (740664, 2) :: (1, 1) :: repeat (1, 2) 1511339 ++ (5653179, 2) :: (1, 1) :: repeat (1, 2) 11874956 ++ w) 1); closearith.
  }
  (* step 122: M pop12 (4643,) *)
  apply (hsteps_trans _ (HB [1066; 135; 35; 20; 0] 6359 1 9841 ((4018, 2) :: (1, 1) :: repeat (1, 2) 25145 ++ (740664, 2) :: (1, 1) :: repeat (1, 2) 1511339 ++ (5653179, 2) :: (1, 1) :: repeat (1, 2) 11874956 ++ w) 1)).
  {
    apply (pop12 4643 [1066; 135; 35; 20; 0] 1716 555 ((4018, 2) :: (1, 1) :: repeat (1, 2) 25145 ++ (740664, 2) :: (1, 1) :: repeat (1, 2) 1511339 ++ (5653179, 2) :: (1, 1) :: repeat (1, 2) 11874956 ++ w) 1); closearith.
  }
  (* step 123: sTUP *)
  apply (hsteps_trans _ (HC [1066; 135; 35; 20; 0] 6359 9840 2 ((4016, 2) :: (1, 1) :: repeat (1, 2) 25145 ++ (740664, 2) :: (1, 1) :: repeat (1, 2) 1511339 ++ (5653179, 2) :: (1, 1) :: repeat (1, 2) 11874956 ++ w) 1)).
  {
    replace ((4016, 2) :: (1, 1) :: repeat (1, 2) 25145 ++ (740664, 2) :: (1, 1) :: repeat (1, 2) 1511339 ++ (5653179, 2) :: (1, 1) :: repeat (1, 2) 11874956 ++ w) with ((4018 - 2, 2) :: (1, 1) :: repeat (1, 2) 25145 ++ (740664, 2) :: (1, 1) :: repeat (1, 2) 1511339 ++ (5653179, 2) :: (1, 1) :: repeat (1, 2) 11874956 ++ w) by sec_eq.
    apply (sTUP [1066; 135; 35; 20; 0] 6359 9841 4018 2 ((1, 1) :: repeat (1, 2) 25145 ++ (740664, 2) :: (1, 1) :: repeat (1, 2) 1511339 ++ (5653179, 2) :: (1, 1) :: repeat (1, 2) 11874956 ++ w) 1); closearith.
  }
  (* step 124: hGRIND_even 4918 *)
  apply (hsteps_trans _ (HB [1066; 135; 35; 20; 0] 6358 1 9840 ((2, 2) :: (4016, 2) :: (1, 1) :: repeat (1, 2) 25145 ++ (740664, 2) :: (1, 1) :: repeat (1, 2) 1511339 ++ (5653179, 2) :: (1, 1) :: repeat (1, 2) 11874956 ++ w) 1)).
  {
    apply (hGRIND_even 4918 [1066; 135; 35; 20; 0] 6358 ((4016, 2) :: (1, 1) :: repeat (1, 2) 25145 ++ (740664, 2) :: (1, 1) :: repeat (1, 2) 1511339 ++ (5653179, 2) :: (1, 1) :: repeat (1, 2) 11874956 ++ w) 1); closearith.
  }
  (* step 125: P TUP2_1 *)
  apply (hsteps_trans _ (HC [6359; 1066; 135; 35; 20; 0] 9840 1 2 ((4014, 2) :: (1, 1) :: repeat (1, 2) 25145 ++ (740664, 2) :: (1, 1) :: repeat (1, 2) 1511339 ++ (5653179, 2) :: (1, 1) :: repeat (1, 2) 11874956 ++ w) 1)).
  {
    replace ((4014, 2) :: (1, 1) :: repeat (1, 2) 25145 ++ (740664, 2) :: (1, 1) :: repeat (1, 2) 1511339 ++ (5653179, 2) :: (1, 1) :: repeat (1, 2) 11874956 ++ w) with ((4016 - 2, 2) :: (1, 1) :: repeat (1, 2) 25145 ++ (740664, 2) :: (1, 1) :: repeat (1, 2) 1511339 ++ (5653179, 2) :: (1, 1) :: repeat (1, 2) 11874956 ++ w) by sec_eq.
    apply (sTUP2_1 [1066; 135; 35; 20; 0] 6358 9839 4016 ((1, 1) :: repeat (1, 2) 25145 ++ (740664, 2) :: (1, 1) :: repeat (1, 2) 1511339 ++ (5653179, 2) :: (1, 1) :: repeat (1, 2) 11874956 ++ w) 1); closearith.
  }
  (* step 126: P TDN *)
  apply (hsteps_trans _ (HB [6359; 1066; 135; 35; 20; 0] 9840 1 4 ((4014, 2) :: (1, 1) :: repeat (1, 2) 25145 ++ (740664, 2) :: (1, 1) :: repeat (1, 2) 1511339 ++ (5653179, 2) :: (1, 1) :: repeat (1, 2) 11874956 ++ w) 1)).
  {
    apply (sTDN [6359; 1066; 135; 35; 20; 0] 9840 ((4014, 2) :: (1, 1) :: repeat (1, 2) 25145 ++ (740664, 2) :: (1, 1) :: repeat (1, 2) 1511339 ++ (5653179, 2) :: (1, 1) :: repeat (1, 2) 11874956 ++ w) 1).
  }
  (* step 127: sTUP *)
  apply (hsteps_trans _ (HC [6359; 1066; 135; 35; 20; 0] 9840 3 2 ((4012, 2) :: (1, 1) :: repeat (1, 2) 25145 ++ (740664, 2) :: (1, 1) :: repeat (1, 2) 1511339 ++ (5653179, 2) :: (1, 1) :: repeat (1, 2) 11874956 ++ w) 1)).
  {
    replace ((4012, 2) :: (1, 1) :: repeat (1, 2) 25145 ++ (740664, 2) :: (1, 1) :: repeat (1, 2) 1511339 ++ (5653179, 2) :: (1, 1) :: repeat (1, 2) 11874956 ++ w) with ((4014 - 2, 2) :: (1, 1) :: repeat (1, 2) 25145 ++ (740664, 2) :: (1, 1) :: repeat (1, 2) 1511339 ++ (5653179, 2) :: (1, 1) :: repeat (1, 2) 11874956 ++ w) by sec_eq.
    apply (sTUP [6359; 1066; 135; 35; 20; 0] 9840 4 4014 2 ((1, 1) :: repeat (1, 2) 25145 ++ (740664, 2) :: (1, 1) :: repeat (1, 2) 1511339 ++ (5653179, 2) :: (1, 1) :: repeat (1, 2) 11874956 ++ w) 1); closearith.
  }
  (* step 128: CLEANG_even 2005 *)
  apply (hsteps_trans _ (HB [6359; 1066; 135; 35; 20; 0] 9840 1 4016 ((2, 2) :: (1, 1) :: repeat (1, 2) 25145 ++ (740664, 2) :: (1, 1) :: repeat (1, 2) 1511339 ++ (5653179, 2) :: (1, 1) :: repeat (1, 2) 11874956 ++ w) 1)).
  {
    apply (CLEANG_even 2005 [6359; 1066; 135; 35; 20; 0] 9840 ((1, 1) :: repeat (1, 2) 25145 ++ (740664, 2) :: (1, 1) :: repeat (1, 2) 1511339 ++ (5653179, 2) :: (1, 1) :: repeat (1, 2) 11874956 ++ w) 1); closearith.
  }
  (* step 129: P TRANS2_1 *)
  apply (hsteps_trans _ (HB [9841; 6359; 1066; 135; 35; 20; 0] 4017 1 3 (repeat (1, 2) 25145 ++ (740664, 2) :: (1, 1) :: repeat (1, 2) 1511339 ++ (5653179, 2) :: (1, 1) :: repeat (1, 2) 11874956 ++ w) 1)).
  {
    apply (sTRANS2_1 [6359; 1066; 135; 35; 20; 0] 9840 4015 1 (repeat (1, 2) 25145 ++ (740664, 2) :: (1, 1) :: repeat (1, 2) 1511339 ++ (5653179, 2) :: (1, 1) :: repeat (1, 2) 11874956 ++ w) 1); closearith.
  }
  (* step 130: M pop12 (25145,) *)
  apply (hsteps_trans _ (HB [9841; 6359; 1066; 135; 35; 20; 0] 29162 1 50293 ((740664, 2) :: (1, 1) :: repeat (1, 2) 1511339 ++ (5653179, 2) :: (1, 1) :: repeat (1, 2) 11874956 ++ w) 1)).
  {
    apply (pop12 25145 [9841; 6359; 1066; 135; 35; 20; 0] 4017 3 ((740664, 2) :: (1, 1) :: repeat (1, 2) 1511339 ++ (5653179, 2) :: (1, 1) :: repeat (1, 2) 11874956 ++ w) 1); closearith.
  }
  (* step 131: sTUP *)
  apply (hsteps_trans _ (HC [9841; 6359; 1066; 135; 35; 20; 0] 29162 50292 2 ((740662, 2) :: (1, 1) :: repeat (1, 2) 1511339 ++ (5653179, 2) :: (1, 1) :: repeat (1, 2) 11874956 ++ w) 1)).
  {
    rewrite NUM58X8.
    apply (sTUP [9841; 6359; 1066; 135; 35; 20; 0] 29162 50293 740664 2 ((1, 1) :: repeat (1, 2) 1511339 ++ (5653179, 2) :: (1, 1) :: repeat (1, 2) 11874956 ++ w) 1); closearith.
  }
  (* step 132: hGRIND_even 25144 *)
  apply (hsteps_trans _ (HB [9841; 6359; 1066; 135; 35; 20; 0] 29161 1 50292 ((2, 2) :: (740662, 2) :: (1, 1) :: repeat (1, 2) 1511339 ++ (5653179, 2) :: (1, 1) :: repeat (1, 2) 11874956 ++ w) 1)).
  {
    rewrite NUM58X9.
    apply (hGRIND_even 25144 [9841; 6359; 1066; 135; 35; 20; 0] 29161 ((740662, 2) :: (1, 1) :: repeat (1, 2) 1511339 ++ (5653179, 2) :: (1, 1) :: repeat (1, 2) 11874956 ++ w) 1); closearith.
  }
  (* step 133: P TUP2_1 *)
  apply (hsteps_trans _ (HC [29162; 9841; 6359; 1066; 135; 35; 20; 0] 50292 1 2 ((740660, 2) :: (1, 1) :: repeat (1, 2) 1511339 ++ (5653179, 2) :: (1, 1) :: repeat (1, 2) 11874956 ++ w) 1)).
  {
    rewrite NUM58X10.
    apply (sTUP2_1 [9841; 6359; 1066; 135; 35; 20; 0] 29161 50291 740662 ((1, 1) :: repeat (1, 2) 1511339 ++ (5653179, 2) :: (1, 1) :: repeat (1, 2) 11874956 ++ w) 1); closearith.
  }
  (* step 134: P TDN *)
  apply (hsteps_trans _ (HB [29162; 9841; 6359; 1066; 135; 35; 20; 0] 50292 1 4 ((740660, 2) :: (1, 1) :: repeat (1, 2) 1511339 ++ (5653179, 2) :: (1, 1) :: repeat (1, 2) 11874956 ++ w) 1)).
  {
    apply (sTDN [29162; 9841; 6359; 1066; 135; 35; 20; 0] 50292 ((740660, 2) :: (1, 1) :: repeat (1, 2) 1511339 ++ (5653179, 2) :: (1, 1) :: repeat (1, 2) 11874956 ++ w) 1).
  }
  (* step 135: sTUP *)
  apply (hsteps_trans _ (HC [29162; 9841; 6359; 1066; 135; 35; 20; 0] 50292 3 2 ((740658, 2) :: (1, 1) :: repeat (1, 2) 1511339 ++ (5653179, 2) :: (1, 1) :: repeat (1, 2) 11874956 ++ w) 1)).
  {
    rewrite NUM58X11.
    apply (sTUP [29162; 9841; 6359; 1066; 135; 35; 20; 0] 50292 4 740660 2 ((1, 1) :: repeat (1, 2) 1511339 ++ (5653179, 2) :: (1, 1) :: repeat (1, 2) 11874956 ++ w) 1); closearith.
  }
  (* step 136: DIPGRIND 50292 640074 *)
  apply (hsteps_trans _ (HC [29162; 9841; 6359; 1066; 135; 35; 20; 0] 0 3 2 (repeat (1, 2) 50292 ++ (640074, 2) :: (1, 1) :: repeat (1, 2) 1511339 ++ (5653179, 2) :: (1, 1) :: repeat (1, 2) 11874956 ++ w) 1)).
  {
    rewrite NUM58X12.
    apply (DIPGRIND 50292 640074 [29162; 9841; 6359; 1066; 135; 35; 20; 0] ((1, 1) :: repeat (1, 2) 1511339 ++ (5653179, 2) :: (1, 1) :: repeat (1, 2) 11874956 ++ w) 1); closearith.
  }
  (* step 137: P PX2A *)
  apply (hsteps_trans _ (HC [6359; 1066; 135; 35; 20; 0] 9840 29160 2 ((1, 1) :: repeat (1, 2) 50294 ++ (640074, 2) :: (1, 1) :: repeat (1, 2) 1511339 ++ (5653179, 2) :: (1, 1) :: repeat (1, 2) 11874956 ++ w) 1)).
  {
    exact (hsteps_step _ _ _ (hPX2A 29159 9840 [6359; 1066; 135; 35; 20; 0] (repeat (1, 2) 50292 ++ (640074, 2) :: (1, 1) :: repeat (1, 2) 1511339 ++ (5653179, 2) :: (1, 1) :: repeat (1, 2) 11874956 ++ w) 1) (hsteps_refl _)).
  }
  (* step 138: P PUSH *)
  apply (hsteps_trans _ (HC [6359; 1066; 135; 35; 20; 0] 9839 1 2 ((29158, 2) :: (1, 1) :: repeat (1, 2) 50294 ++ (640074, 2) :: (1, 1) :: repeat (1, 2) 1511339 ++ (5653179, 2) :: (1, 1) :: repeat (1, 2) 11874956 ++ w) 1)).
  {
    replace ((29158, 2) :: (1, 1) :: repeat (1, 2) 50294 ++ (640074, 2) :: (1, 1) :: repeat (1, 2) 1511339 ++ (5653179, 2) :: (1, 1) :: repeat (1, 2) 11874956 ++ w) with ((29160 - 2, 2) :: (1, 1) :: repeat (1, 2) 50294 ++ (640074, 2) :: (1, 1) :: repeat (1, 2) 1511339 ++ (5653179, 2) :: (1, 1) :: repeat (1, 2) 11874956 ++ w) by sec_eq.
    apply (sPUSH [6359; 1066; 135; 35; 20; 0] 9839 29160 ((1, 1) :: repeat (1, 2) 50294 ++ (640074, 2) :: (1, 1) :: repeat (1, 2) 1511339 ++ (5653179, 2) :: (1, 1) :: repeat (1, 2) 11874956 ++ w) 1); closearith.
  }
  (* step 139: P TDN *)
  apply (hsteps_trans _ (HB [6359; 1066; 135; 35; 20; 0] 9839 1 4 ((29158, 2) :: (1, 1) :: repeat (1, 2) 50294 ++ (640074, 2) :: (1, 1) :: repeat (1, 2) 1511339 ++ (5653179, 2) :: (1, 1) :: repeat (1, 2) 11874956 ++ w) 1)).
  {
    apply (sTDN [6359; 1066; 135; 35; 20; 0] 9839 ((29158, 2) :: (1, 1) :: repeat (1, 2) 50294 ++ (640074, 2) :: (1, 1) :: repeat (1, 2) 1511339 ++ (5653179, 2) :: (1, 1) :: repeat (1, 2) 11874956 ++ w) 1).
  }
  (* step 140: sTUP *)
  apply (hsteps_trans _ (HC [6359; 1066; 135; 35; 20; 0] 9839 3 2 ((29156, 2) :: (1, 1) :: repeat (1, 2) 50294 ++ (640074, 2) :: (1, 1) :: repeat (1, 2) 1511339 ++ (5653179, 2) :: (1, 1) :: repeat (1, 2) 11874956 ++ w) 1)).
  {
    replace ((29156, 2) :: (1, 1) :: repeat (1, 2) 50294 ++ (640074, 2) :: (1, 1) :: repeat (1, 2) 1511339 ++ (5653179, 2) :: (1, 1) :: repeat (1, 2) 11874956 ++ w) with ((29158 - 2, 2) :: (1, 1) :: repeat (1, 2) 50294 ++ (640074, 2) :: (1, 1) :: repeat (1, 2) 1511339 ++ (5653179, 2) :: (1, 1) :: repeat (1, 2) 11874956 ++ w) by sec_eq.
    apply (sTUP [6359; 1066; 135; 35; 20; 0] 9839 4 29158 2 ((1, 1) :: repeat (1, 2) 50294 ++ (640074, 2) :: (1, 1) :: repeat (1, 2) 1511339 ++ (5653179, 2) :: (1, 1) :: repeat (1, 2) 11874956 ++ w) 1); closearith.
  }
  (* step 141: DIPGRIND 9839 9478 *)
  apply (hsteps_trans _ (HC [6359; 1066; 135; 35; 20; 0] 0 3 2 (repeat (1, 2) 9839 ++ (9478, 2) :: (1, 1) :: repeat (1, 2) 50294 ++ (640074, 2) :: (1, 1) :: repeat (1, 2) 1511339 ++ (5653179, 2) :: (1, 1) :: repeat (1, 2) 11874956 ++ w) 1)).
  {
    apply (DIPGRIND 9839 9478 [6359; 1066; 135; 35; 20; 0] ((1, 1) :: repeat (1, 2) 50294 ++ (640074, 2) :: (1, 1) :: repeat (1, 2) 1511339 ++ (5653179, 2) :: (1, 1) :: repeat (1, 2) 11874956 ++ w) 1); closearith.
  }
  (* step 142: P PX2A *)
  apply (hsteps_trans _ (HC [135; 35; 20; 0] 1065 6357 2 ((1, 1) :: repeat (1, 2) 9841 ++ (9478, 2) :: (1, 1) :: repeat (1, 2) 50294 ++ (640074, 2) :: (1, 1) :: repeat (1, 2) 1511339 ++ (5653179, 2) :: (1, 1) :: repeat (1, 2) 11874956 ++ w) 1)).
  {
    exact (hsteps_step _ _ _ (hPX2A 6356 1065 [135; 35; 20; 0] (repeat (1, 2) 9839 ++ (9478, 2) :: (1, 1) :: repeat (1, 2) 50294 ++ (640074, 2) :: (1, 1) :: repeat (1, 2) 1511339 ++ (5653179, 2) :: (1, 1) :: repeat (1, 2) 11874956 ++ w) 1) (hsteps_refl _)).
  }
  (* step 143: P PUSH *)
  apply (hsteps_trans _ (HC [135; 35; 20; 0] 1064 1 2 ((6355, 2) :: (1, 1) :: repeat (1, 2) 9841 ++ (9478, 2) :: (1, 1) :: repeat (1, 2) 50294 ++ (640074, 2) :: (1, 1) :: repeat (1, 2) 1511339 ++ (5653179, 2) :: (1, 1) :: repeat (1, 2) 11874956 ++ w) 1)).
  {
    replace ((6355, 2) :: (1, 1) :: repeat (1, 2) 9841 ++ (9478, 2) :: (1, 1) :: repeat (1, 2) 50294 ++ (640074, 2) :: (1, 1) :: repeat (1, 2) 1511339 ++ (5653179, 2) :: (1, 1) :: repeat (1, 2) 11874956 ++ w) with ((6357 - 2, 2) :: (1, 1) :: repeat (1, 2) 9841 ++ (9478, 2) :: (1, 1) :: repeat (1, 2) 50294 ++ (640074, 2) :: (1, 1) :: repeat (1, 2) 1511339 ++ (5653179, 2) :: (1, 1) :: repeat (1, 2) 11874956 ++ w) by sec_eq.
    apply (sPUSH [135; 35; 20; 0] 1064 6357 ((1, 1) :: repeat (1, 2) 9841 ++ (9478, 2) :: (1, 1) :: repeat (1, 2) 50294 ++ (640074, 2) :: (1, 1) :: repeat (1, 2) 1511339 ++ (5653179, 2) :: (1, 1) :: repeat (1, 2) 11874956 ++ w) 1); closearith.
  }
  (* step 144: P TDN *)
  apply (hsteps_trans _ (HB [135; 35; 20; 0] 1064 1 4 ((6355, 2) :: (1, 1) :: repeat (1, 2) 9841 ++ (9478, 2) :: (1, 1) :: repeat (1, 2) 50294 ++ (640074, 2) :: (1, 1) :: repeat (1, 2) 1511339 ++ (5653179, 2) :: (1, 1) :: repeat (1, 2) 11874956 ++ w) 1)).
  {
    apply (sTDN [135; 35; 20; 0] 1064 ((6355, 2) :: (1, 1) :: repeat (1, 2) 9841 ++ (9478, 2) :: (1, 1) :: repeat (1, 2) 50294 ++ (640074, 2) :: (1, 1) :: repeat (1, 2) 1511339 ++ (5653179, 2) :: (1, 1) :: repeat (1, 2) 11874956 ++ w) 1).
  }
  (* step 145: sTUP *)
  apply (hsteps_trans _ (HC [135; 35; 20; 0] 1064 3 2 ((6353, 2) :: (1, 1) :: repeat (1, 2) 9841 ++ (9478, 2) :: (1, 1) :: repeat (1, 2) 50294 ++ (640074, 2) :: (1, 1) :: repeat (1, 2) 1511339 ++ (5653179, 2) :: (1, 1) :: repeat (1, 2) 11874956 ++ w) 1)).
  {
    replace ((6353, 2) :: (1, 1) :: repeat (1, 2) 9841 ++ (9478, 2) :: (1, 1) :: repeat (1, 2) 50294 ++ (640074, 2) :: (1, 1) :: repeat (1, 2) 1511339 ++ (5653179, 2) :: (1, 1) :: repeat (1, 2) 11874956 ++ w) with ((6355 - 2, 2) :: (1, 1) :: repeat (1, 2) 9841 ++ (9478, 2) :: (1, 1) :: repeat (1, 2) 50294 ++ (640074, 2) :: (1, 1) :: repeat (1, 2) 1511339 ++ (5653179, 2) :: (1, 1) :: repeat (1, 2) 11874956 ++ w) by sec_eq.
    apply (sTUP [135; 35; 20; 0] 1064 4 6355 2 ((1, 1) :: repeat (1, 2) 9841 ++ (9478, 2) :: (1, 1) :: repeat (1, 2) 50294 ++ (640074, 2) :: (1, 1) :: repeat (1, 2) 1511339 ++ (5653179, 2) :: (1, 1) :: repeat (1, 2) 11874956 ++ w) 1); closearith.
  }
  (* step 146: DIPGRIND 1064 4225 *)
  apply (hsteps_trans _ (HC [135; 35; 20; 0] 0 3 2 (repeat (1, 2) 1064 ++ (4225, 2) :: (1, 1) :: repeat (1, 2) 9841 ++ (9478, 2) :: (1, 1) :: repeat (1, 2) 50294 ++ (640074, 2) :: (1, 1) :: repeat (1, 2) 1511339 ++ (5653179, 2) :: (1, 1) :: repeat (1, 2) 11874956 ++ w) 1)).
  {
    apply (DIPGRIND 1064 4225 [135; 35; 20; 0] ((1, 1) :: repeat (1, 2) 9841 ++ (9478, 2) :: (1, 1) :: repeat (1, 2) 50294 ++ (640074, 2) :: (1, 1) :: repeat (1, 2) 1511339 ++ (5653179, 2) :: (1, 1) :: repeat (1, 2) 11874956 ++ w) 1); closearith.
  }
  (* step 147: P PX2A *)
  apply (hsteps_trans _ (HC [20; 0] 34 133 2 ((1, 1) :: repeat (1, 2) 1066 ++ (4225, 2) :: (1, 1) :: repeat (1, 2) 9841 ++ (9478, 2) :: (1, 1) :: repeat (1, 2) 50294 ++ (640074, 2) :: (1, 1) :: repeat (1, 2) 1511339 ++ (5653179, 2) :: (1, 1) :: repeat (1, 2) 11874956 ++ w) 1)).
  {
    exact (hsteps_step _ _ _ (hPX2A 132 34 [20; 0] (repeat (1, 2) 1064 ++ (4225, 2) :: (1, 1) :: repeat (1, 2) 9841 ++ (9478, 2) :: (1, 1) :: repeat (1, 2) 50294 ++ (640074, 2) :: (1, 1) :: repeat (1, 2) 1511339 ++ (5653179, 2) :: (1, 1) :: repeat (1, 2) 11874956 ++ w) 1) (hsteps_refl _)).
  }
  (* step 148: P PUSH *)
  apply (hsteps_trans _ (HC [20; 0] 33 1 2 ((131, 2) :: (1, 1) :: repeat (1, 2) 1066 ++ (4225, 2) :: (1, 1) :: repeat (1, 2) 9841 ++ (9478, 2) :: (1, 1) :: repeat (1, 2) 50294 ++ (640074, 2) :: (1, 1) :: repeat (1, 2) 1511339 ++ (5653179, 2) :: (1, 1) :: repeat (1, 2) 11874956 ++ w) 1)).
  {
    replace ((131, 2) :: (1, 1) :: repeat (1, 2) 1066 ++ (4225, 2) :: (1, 1) :: repeat (1, 2) 9841 ++ (9478, 2) :: (1, 1) :: repeat (1, 2) 50294 ++ (640074, 2) :: (1, 1) :: repeat (1, 2) 1511339 ++ (5653179, 2) :: (1, 1) :: repeat (1, 2) 11874956 ++ w) with ((133 - 2, 2) :: (1, 1) :: repeat (1, 2) 1066 ++ (4225, 2) :: (1, 1) :: repeat (1, 2) 9841 ++ (9478, 2) :: (1, 1) :: repeat (1, 2) 50294 ++ (640074, 2) :: (1, 1) :: repeat (1, 2) 1511339 ++ (5653179, 2) :: (1, 1) :: repeat (1, 2) 11874956 ++ w) by sec_eq.
    apply (sPUSH [20; 0] 33 133 ((1, 1) :: repeat (1, 2) 1066 ++ (4225, 2) :: (1, 1) :: repeat (1, 2) 9841 ++ (9478, 2) :: (1, 1) :: repeat (1, 2) 50294 ++ (640074, 2) :: (1, 1) :: repeat (1, 2) 1511339 ++ (5653179, 2) :: (1, 1) :: repeat (1, 2) 11874956 ++ w) 1); closearith.
  }
  (* step 149: P TDN *)
  apply (hsteps_trans _ (HB [20; 0] 33 1 4 ((131, 2) :: (1, 1) :: repeat (1, 2) 1066 ++ (4225, 2) :: (1, 1) :: repeat (1, 2) 9841 ++ (9478, 2) :: (1, 1) :: repeat (1, 2) 50294 ++ (640074, 2) :: (1, 1) :: repeat (1, 2) 1511339 ++ (5653179, 2) :: (1, 1) :: repeat (1, 2) 11874956 ++ w) 1)).
  {
    apply (sTDN [20; 0] 33 ((131, 2) :: (1, 1) :: repeat (1, 2) 1066 ++ (4225, 2) :: (1, 1) :: repeat (1, 2) 9841 ++ (9478, 2) :: (1, 1) :: repeat (1, 2) 50294 ++ (640074, 2) :: (1, 1) :: repeat (1, 2) 1511339 ++ (5653179, 2) :: (1, 1) :: repeat (1, 2) 11874956 ++ w) 1).
  }
  (* step 150: sTUP *)
  apply (hsteps_trans _ (HC [20; 0] 33 3 2 ((129, 2) :: (1, 1) :: repeat (1, 2) 1066 ++ (4225, 2) :: (1, 1) :: repeat (1, 2) 9841 ++ (9478, 2) :: (1, 1) :: repeat (1, 2) 50294 ++ (640074, 2) :: (1, 1) :: repeat (1, 2) 1511339 ++ (5653179, 2) :: (1, 1) :: repeat (1, 2) 11874956 ++ w) 1)).
  {
    replace ((129, 2) :: (1, 1) :: repeat (1, 2) 1066 ++ (4225, 2) :: (1, 1) :: repeat (1, 2) 9841 ++ (9478, 2) :: (1, 1) :: repeat (1, 2) 50294 ++ (640074, 2) :: (1, 1) :: repeat (1, 2) 1511339 ++ (5653179, 2) :: (1, 1) :: repeat (1, 2) 11874956 ++ w) with ((131 - 2, 2) :: (1, 1) :: repeat (1, 2) 1066 ++ (4225, 2) :: (1, 1) :: repeat (1, 2) 9841 ++ (9478, 2) :: (1, 1) :: repeat (1, 2) 50294 ++ (640074, 2) :: (1, 1) :: repeat (1, 2) 1511339 ++ (5653179, 2) :: (1, 1) :: repeat (1, 2) 11874956 ++ w) by sec_eq.
    apply (sTUP [20; 0] 33 4 131 2 ((1, 1) :: repeat (1, 2) 1066 ++ (4225, 2) :: (1, 1) :: repeat (1, 2) 9841 ++ (9478, 2) :: (1, 1) :: repeat (1, 2) 50294 ++ (640074, 2) :: (1, 1) :: repeat (1, 2) 1511339 ++ (5653179, 2) :: (1, 1) :: repeat (1, 2) 11874956 ++ w) 1); closearith.
  }
  (* step 151: DIPGRIND 33 63 *)
  apply (hsteps_trans _ (HC [20; 0] 0 3 2 (repeat (1, 2) 33 ++ (63, 2) :: (1, 1) :: repeat (1, 2) 1066 ++ (4225, 2) :: (1, 1) :: repeat (1, 2) 9841 ++ (9478, 2) :: (1, 1) :: repeat (1, 2) 50294 ++ (640074, 2) :: (1, 1) :: repeat (1, 2) 1511339 ++ (5653179, 2) :: (1, 1) :: repeat (1, 2) 11874956 ++ w) 1)).
  {
    apply (DIPGRIND 33 63 [20; 0] ((1, 1) :: repeat (1, 2) 1066 ++ (4225, 2) :: (1, 1) :: repeat (1, 2) 9841 ++ (9478, 2) :: (1, 1) :: repeat (1, 2) 50294 ++ (640074, 2) :: (1, 1) :: repeat (1, 2) 1511339 ++ (5653179, 2) :: (1, 1) :: repeat (1, 2) 11874956 ++ w) 1); closearith.
  }
  (* step 152: P PX2A0 *)
  apply (hsteps_trans _ (HB [0] 3 1 2 ((16, 2) :: (1, 1) :: repeat (1, 2) 35 ++ (63, 2) :: (1, 1) :: repeat (1, 2) 1066 ++ (4225, 2) :: (1, 1) :: repeat (1, 2) 9841 ++ (9478, 2) :: (1, 1) :: repeat (1, 2) 50294 ++ (640074, 2) :: (1, 1) :: repeat (1, 2) 1511339 ++ (5653179, 2) :: (1, 1) :: repeat (1, 2) 11874956 ++ w) 1)).
  {
    exact (hsteps_step _ _ _ (hPX2A0 15 (repeat (1, 2) 33 ++ (63, 2) :: (1, 1) :: repeat (1, 2) 1066 ++ (4225, 2) :: (1, 1) :: repeat (1, 2) 9841 ++ (9478, 2) :: (1, 1) :: repeat (1, 2) 50294 ++ (640074, 2) :: (1, 1) :: repeat (1, 2) 1511339 ++ (5653179, 2) :: (1, 1) :: repeat (1, 2) 11874956 ++ w) 1) (hsteps_refl _)).
  }
  (* step 153: sTUP *)
  apply (hsteps_trans _ (HC [0] 3 1 2 ((14, 2) :: (1, 1) :: repeat (1, 2) 35 ++ (63, 2) :: (1, 1) :: repeat (1, 2) 1066 ++ (4225, 2) :: (1, 1) :: repeat (1, 2) 9841 ++ (9478, 2) :: (1, 1) :: repeat (1, 2) 50294 ++ (640074, 2) :: (1, 1) :: repeat (1, 2) 1511339 ++ (5653179, 2) :: (1, 1) :: repeat (1, 2) 11874956 ++ w) 1)).
  {
    replace ((14, 2) :: (1, 1) :: repeat (1, 2) 35 ++ (63, 2) :: (1, 1) :: repeat (1, 2) 1066 ++ (4225, 2) :: (1, 1) :: repeat (1, 2) 9841 ++ (9478, 2) :: (1, 1) :: repeat (1, 2) 50294 ++ (640074, 2) :: (1, 1) :: repeat (1, 2) 1511339 ++ (5653179, 2) :: (1, 1) :: repeat (1, 2) 11874956 ++ w) with ((16 - 2, 2) :: (1, 1) :: repeat (1, 2) 35 ++ (63, 2) :: (1, 1) :: repeat (1, 2) 1066 ++ (4225, 2) :: (1, 1) :: repeat (1, 2) 9841 ++ (9478, 2) :: (1, 1) :: repeat (1, 2) 50294 ++ (640074, 2) :: (1, 1) :: repeat (1, 2) 1511339 ++ (5653179, 2) :: (1, 1) :: repeat (1, 2) 11874956 ++ w) by sec_eq.
    apply (sTUP [0] 3 2 16 2 ((1, 1) :: repeat (1, 2) 35 ++ (63, 2) :: (1, 1) :: repeat (1, 2) 1066 ++ (4225, 2) :: (1, 1) :: repeat (1, 2) 9841 ++ (9478, 2) :: (1, 1) :: repeat (1, 2) 50294 ++ (640074, 2) :: (1, 1) :: repeat (1, 2) 1511339 ++ (5653179, 2) :: (1, 1) :: repeat (1, 2) 11874956 ++ w) 1); closearith.
  }
  (* step 154: P TDN *)
  apply (hsteps_trans _ (HB [0] 3 1 4 ((14, 2) :: (1, 1) :: repeat (1, 2) 35 ++ (63, 2) :: (1, 1) :: repeat (1, 2) 1066 ++ (4225, 2) :: (1, 1) :: repeat (1, 2) 9841 ++ (9478, 2) :: (1, 1) :: repeat (1, 2) 50294 ++ (640074, 2) :: (1, 1) :: repeat (1, 2) 1511339 ++ (5653179, 2) :: (1, 1) :: repeat (1, 2) 11874956 ++ w) 1)).
  {
    apply (sTDN [0] 3 ((14, 2) :: (1, 1) :: repeat (1, 2) 35 ++ (63, 2) :: (1, 1) :: repeat (1, 2) 1066 ++ (4225, 2) :: (1, 1) :: repeat (1, 2) 9841 ++ (9478, 2) :: (1, 1) :: repeat (1, 2) 50294 ++ (640074, 2) :: (1, 1) :: repeat (1, 2) 1511339 ++ (5653179, 2) :: (1, 1) :: repeat (1, 2) 11874956 ++ w) 1).
  }
  (* step 155: sTUP *)
  apply (hsteps_trans _ (HC [0] 3 3 2 ((12, 2) :: (1, 1) :: repeat (1, 2) 35 ++ (63, 2) :: (1, 1) :: repeat (1, 2) 1066 ++ (4225, 2) :: (1, 1) :: repeat (1, 2) 9841 ++ (9478, 2) :: (1, 1) :: repeat (1, 2) 50294 ++ (640074, 2) :: (1, 1) :: repeat (1, 2) 1511339 ++ (5653179, 2) :: (1, 1) :: repeat (1, 2) 11874956 ++ w) 1)).
  {
    replace ((12, 2) :: (1, 1) :: repeat (1, 2) 35 ++ (63, 2) :: (1, 1) :: repeat (1, 2) 1066 ++ (4225, 2) :: (1, 1) :: repeat (1, 2) 9841 ++ (9478, 2) :: (1, 1) :: repeat (1, 2) 50294 ++ (640074, 2) :: (1, 1) :: repeat (1, 2) 1511339 ++ (5653179, 2) :: (1, 1) :: repeat (1, 2) 11874956 ++ w) with ((14 - 2, 2) :: (1, 1) :: repeat (1, 2) 35 ++ (63, 2) :: (1, 1) :: repeat (1, 2) 1066 ++ (4225, 2) :: (1, 1) :: repeat (1, 2) 9841 ++ (9478, 2) :: (1, 1) :: repeat (1, 2) 50294 ++ (640074, 2) :: (1, 1) :: repeat (1, 2) 1511339 ++ (5653179, 2) :: (1, 1) :: repeat (1, 2) 11874956 ++ w) by sec_eq.
    apply (sTUP [0] 3 4 14 2 ((1, 1) :: repeat (1, 2) 35 ++ (63, 2) :: (1, 1) :: repeat (1, 2) 1066 ++ (4225, 2) :: (1, 1) :: repeat (1, 2) 9841 ++ (9478, 2) :: (1, 1) :: repeat (1, 2) 50294 ++ (640074, 2) :: (1, 1) :: repeat (1, 2) 1511339 ++ (5653179, 2) :: (1, 1) :: repeat (1, 2) 11874956 ++ w) 1); closearith.
  }
  (* step 156: DIPGRIND 3 6 *)
  apply (hsteps_trans _ (HC [0] 0 3 2 (repeat (1, 2) 3 ++ (6, 2) :: (1, 1) :: repeat (1, 2) 35 ++ (63, 2) :: (1, 1) :: repeat (1, 2) 1066 ++ (4225, 2) :: (1, 1) :: repeat (1, 2) 9841 ++ (9478, 2) :: (1, 1) :: repeat (1, 2) 50294 ++ (640074, 2) :: (1, 1) :: repeat (1, 2) 1511339 ++ (5653179, 2) :: (1, 1) :: repeat (1, 2) 11874956 ++ w) 1)).
  {
    apply (DIPGRIND 3 6 [0] ((1, 1) :: repeat (1, 2) 35 ++ (63, 2) :: (1, 1) :: repeat (1, 2) 1066 ++ (4225, 2) :: (1, 1) :: repeat (1, 2) 9841 ++ (9478, 2) :: (1, 1) :: repeat (1, 2) 50294 ++ (640074, 2) :: (1, 1) :: repeat (1, 2) 1511339 ++ (5653179, 2) :: (1, 1) :: repeat (1, 2) 11874956 ++ w) 1); closearith.
  }
  (* step 157: P PX2B0 *)
  apply (hsteps_trans _ (HB [] 0 1 5 (repeat (1, 2) 4 ++ (6, 2) :: (1, 1) :: repeat (1, 2) 35 ++ (63, 2) :: (1, 1) :: repeat (1, 2) 1066 ++ (4225, 2) :: (1, 1) :: repeat (1, 2) 9841 ++ (9478, 2) :: (1, 1) :: repeat (1, 2) 50294 ++ (640074, 2) :: (1, 1) :: repeat (1, 2) 1511339 ++ (5653179, 2) :: (1, 1) :: repeat (1, 2) 11874956 ++ w) 1)).
  {
    exact (hsteps_step _ _ _ (hPX2B0 (repeat (1, 2) 3 ++ (6, 2) :: (1, 1) :: repeat (1, 2) 35 ++ (63, 2) :: (1, 1) :: repeat (1, 2) 1066 ++ (4225, 2) :: (1, 1) :: repeat (1, 2) 9841 ++ (9478, 2) :: (1, 1) :: repeat (1, 2) 50294 ++ (640074, 2) :: (1, 1) :: repeat (1, 2) 1511339 ++ (5653179, 2) :: (1, 1) :: repeat (1, 2) 11874956 ++ w) 1) (hsteps_refl _)).
  }
  (* step 158: M pop12 (4,) *)
  apply (hsteps_trans _ (HB [] 4 1 13 ((6, 2) :: (1, 1) :: repeat (1, 2) 35 ++ (63, 2) :: (1, 1) :: repeat (1, 2) 1066 ++ (4225, 2) :: (1, 1) :: repeat (1, 2) 9841 ++ (9478, 2) :: (1, 1) :: repeat (1, 2) 50294 ++ (640074, 2) :: (1, 1) :: repeat (1, 2) 1511339 ++ (5653179, 2) :: (1, 1) :: repeat (1, 2) 11874956 ++ w) 1)).
  {
    apply (pop12 4 [] 0 5 ((6, 2) :: (1, 1) :: repeat (1, 2) 35 ++ (63, 2) :: (1, 1) :: repeat (1, 2) 1066 ++ (4225, 2) :: (1, 1) :: repeat (1, 2) 9841 ++ (9478, 2) :: (1, 1) :: repeat (1, 2) 50294 ++ (640074, 2) :: (1, 1) :: repeat (1, 2) 1511339 ++ (5653179, 2) :: (1, 1) :: repeat (1, 2) 11874956 ++ w) 1); closearith.
  }
  (* step 159: sTUP *)
  apply (hsteps_trans _ (HC [] 4 12 2 ((4, 2) :: (1, 1) :: repeat (1, 2) 35 ++ (63, 2) :: (1, 1) :: repeat (1, 2) 1066 ++ (4225, 2) :: (1, 1) :: repeat (1, 2) 9841 ++ (9478, 2) :: (1, 1) :: repeat (1, 2) 50294 ++ (640074, 2) :: (1, 1) :: repeat (1, 2) 1511339 ++ (5653179, 2) :: (1, 1) :: repeat (1, 2) 11874956 ++ w) 1)).
  {
    replace ((4, 2) :: (1, 1) :: repeat (1, 2) 35 ++ (63, 2) :: (1, 1) :: repeat (1, 2) 1066 ++ (4225, 2) :: (1, 1) :: repeat (1, 2) 9841 ++ (9478, 2) :: (1, 1) :: repeat (1, 2) 50294 ++ (640074, 2) :: (1, 1) :: repeat (1, 2) 1511339 ++ (5653179, 2) :: (1, 1) :: repeat (1, 2) 11874956 ++ w) with ((6 - 2, 2) :: (1, 1) :: repeat (1, 2) 35 ++ (63, 2) :: (1, 1) :: repeat (1, 2) 1066 ++ (4225, 2) :: (1, 1) :: repeat (1, 2) 9841 ++ (9478, 2) :: (1, 1) :: repeat (1, 2) 50294 ++ (640074, 2) :: (1, 1) :: repeat (1, 2) 1511339 ++ (5653179, 2) :: (1, 1) :: repeat (1, 2) 11874956 ++ w) by sec_eq.
    apply (sTUP [] 4 13 6 2 ((1, 1) :: repeat (1, 2) 35 ++ (63, 2) :: (1, 1) :: repeat (1, 2) 1066 ++ (4225, 2) :: (1, 1) :: repeat (1, 2) 9841 ++ (9478, 2) :: (1, 1) :: repeat (1, 2) 50294 ++ (640074, 2) :: (1, 1) :: repeat (1, 2) 1511339 ++ (5653179, 2) :: (1, 1) :: repeat (1, 2) 11874956 ++ w) 1); closearith.
  }
  (* step 160: P PUSH *)
  apply (hsteps_trans _ (HC [] 3 1 2 ((10, 2) :: (4, 2) :: (1, 1) :: repeat (1, 2) 35 ++ (63, 2) :: (1, 1) :: repeat (1, 2) 1066 ++ (4225, 2) :: (1, 1) :: repeat (1, 2) 9841 ++ (9478, 2) :: (1, 1) :: repeat (1, 2) 50294 ++ (640074, 2) :: (1, 1) :: repeat (1, 2) 1511339 ++ (5653179, 2) :: (1, 1) :: repeat (1, 2) 11874956 ++ w) 1)).
  {
    replace ((10, 2) :: (4, 2) :: (1, 1) :: repeat (1, 2) 35 ++ (63, 2) :: (1, 1) :: repeat (1, 2) 1066 ++ (4225, 2) :: (1, 1) :: repeat (1, 2) 9841 ++ (9478, 2) :: (1, 1) :: repeat (1, 2) 50294 ++ (640074, 2) :: (1, 1) :: repeat (1, 2) 1511339 ++ (5653179, 2) :: (1, 1) :: repeat (1, 2) 11874956 ++ w) with ((12 - 2, 2) :: (4, 2) :: (1, 1) :: repeat (1, 2) 35 ++ (63, 2) :: (1, 1) :: repeat (1, 2) 1066 ++ (4225, 2) :: (1, 1) :: repeat (1, 2) 9841 ++ (9478, 2) :: (1, 1) :: repeat (1, 2) 50294 ++ (640074, 2) :: (1, 1) :: repeat (1, 2) 1511339 ++ (5653179, 2) :: (1, 1) :: repeat (1, 2) 11874956 ++ w) by sec_eq.
    apply (sPUSH [] 3 12 ((4, 2) :: (1, 1) :: repeat (1, 2) 35 ++ (63, 2) :: (1, 1) :: repeat (1, 2) 1066 ++ (4225, 2) :: (1, 1) :: repeat (1, 2) 9841 ++ (9478, 2) :: (1, 1) :: repeat (1, 2) 50294 ++ (640074, 2) :: (1, 1) :: repeat (1, 2) 1511339 ++ (5653179, 2) :: (1, 1) :: repeat (1, 2) 11874956 ++ w) 1); closearith.
  }
  (* step 161: P TDN *)
  apply (hsteps_trans _ (HB [] 3 1 4 ((10, 2) :: (4, 2) :: (1, 1) :: repeat (1, 2) 35 ++ (63, 2) :: (1, 1) :: repeat (1, 2) 1066 ++ (4225, 2) :: (1, 1) :: repeat (1, 2) 9841 ++ (9478, 2) :: (1, 1) :: repeat (1, 2) 50294 ++ (640074, 2) :: (1, 1) :: repeat (1, 2) 1511339 ++ (5653179, 2) :: (1, 1) :: repeat (1, 2) 11874956 ++ w) 1)).
  {
    apply (sTDN [] 3 ((10, 2) :: (4, 2) :: (1, 1) :: repeat (1, 2) 35 ++ (63, 2) :: (1, 1) :: repeat (1, 2) 1066 ++ (4225, 2) :: (1, 1) :: repeat (1, 2) 9841 ++ (9478, 2) :: (1, 1) :: repeat (1, 2) 50294 ++ (640074, 2) :: (1, 1) :: repeat (1, 2) 1511339 ++ (5653179, 2) :: (1, 1) :: repeat (1, 2) 11874956 ++ w) 1).
  }
  (* step 162: sTUP *)
  apply (hsteps_trans _ (HC [] 3 3 2 ((8, 2) :: (4, 2) :: (1, 1) :: repeat (1, 2) 35 ++ (63, 2) :: (1, 1) :: repeat (1, 2) 1066 ++ (4225, 2) :: (1, 1) :: repeat (1, 2) 9841 ++ (9478, 2) :: (1, 1) :: repeat (1, 2) 50294 ++ (640074, 2) :: (1, 1) :: repeat (1, 2) 1511339 ++ (5653179, 2) :: (1, 1) :: repeat (1, 2) 11874956 ++ w) 1)).
  {
    replace ((8, 2) :: (4, 2) :: (1, 1) :: repeat (1, 2) 35 ++ (63, 2) :: (1, 1) :: repeat (1, 2) 1066 ++ (4225, 2) :: (1, 1) :: repeat (1, 2) 9841 ++ (9478, 2) :: (1, 1) :: repeat (1, 2) 50294 ++ (640074, 2) :: (1, 1) :: repeat (1, 2) 1511339 ++ (5653179, 2) :: (1, 1) :: repeat (1, 2) 11874956 ++ w) with ((10 - 2, 2) :: (4, 2) :: (1, 1) :: repeat (1, 2) 35 ++ (63, 2) :: (1, 1) :: repeat (1, 2) 1066 ++ (4225, 2) :: (1, 1) :: repeat (1, 2) 9841 ++ (9478, 2) :: (1, 1) :: repeat (1, 2) 50294 ++ (640074, 2) :: (1, 1) :: repeat (1, 2) 1511339 ++ (5653179, 2) :: (1, 1) :: repeat (1, 2) 11874956 ++ w) by sec_eq.
    apply (sTUP [] 3 4 10 2 ((4, 2) :: (1, 1) :: repeat (1, 2) 35 ++ (63, 2) :: (1, 1) :: repeat (1, 2) 1066 ++ (4225, 2) :: (1, 1) :: repeat (1, 2) 9841 ++ (9478, 2) :: (1, 1) :: repeat (1, 2) 50294 ++ (640074, 2) :: (1, 1) :: repeat (1, 2) 1511339 ++ (5653179, 2) :: (1, 1) :: repeat (1, 2) 11874956 ++ w) 1); closearith.
  }
  (* step 163: DIPGRIND 3 2 *)
  apply (hsteps_trans _ (HC [] 0 3 2 (repeat (1, 2) 3 ++ (2, 2) :: (4, 2) :: (1, 1) :: repeat (1, 2) 35 ++ (63, 2) :: (1, 1) :: repeat (1, 2) 1066 ++ (4225, 2) :: (1, 1) :: repeat (1, 2) 9841 ++ (9478, 2) :: (1, 1) :: repeat (1, 2) 50294 ++ (640074, 2) :: (1, 1) :: repeat (1, 2) 1511339 ++ (5653179, 2) :: (1, 1) :: repeat (1, 2) 11874956 ++ w) 1)).
  {
    apply (DIPGRIND 3 2 [] ((4, 2) :: (1, 1) :: repeat (1, 2) 35 ++ (63, 2) :: (1, 1) :: repeat (1, 2) 1066 ++ (4225, 2) :: (1, 1) :: repeat (1, 2) 9841 ++ (9478, 2) :: (1, 1) :: repeat (1, 2) 50294 ++ (640074, 2) :: (1, 1) :: repeat (1, 2) 1511339 ++ (5653179, 2) :: (1, 1) :: repeat (1, 2) 11874956 ++ w) 1); closearith.
  }
  (* step 164: P PUSHX *)
  apply (hsteps_trans _ (HB [] 1 1 7 (repeat (1, 2) 3 ++ (2, 2) :: (4, 2) :: (1, 1) :: repeat (1, 2) 35 ++ (63, 2) :: (1, 1) :: repeat (1, 2) 1066 ++ (4225, 2) :: (1, 1) :: repeat (1, 2) 9841 ++ (9478, 2) :: (1, 1) :: repeat (1, 2) 50294 ++ (640074, 2) :: (1, 1) :: repeat (1, 2) 1511339 ++ (5653179, 2) :: (1, 1) :: repeat (1, 2) 11874956 ++ w) 1)).
  {
    exact (hsteps_step _ _ _ (hPUSHX (repeat (1, 2) 3 ++ (2, 2) :: (4, 2) :: (1, 1) :: repeat (1, 2) 35 ++ (63, 2) :: (1, 1) :: repeat (1, 2) 1066 ++ (4225, 2) :: (1, 1) :: repeat (1, 2) 9841 ++ (9478, 2) :: (1, 1) :: repeat (1, 2) 50294 ++ (640074, 2) :: (1, 1) :: repeat (1, 2) 1511339 ++ (5653179, 2) :: (1, 1) :: repeat (1, 2) 11874956 ++ w) 1) (hsteps_refl _)).
  }
  (* step 165: M pop12 (3,) *)
  apply (hsteps_trans _ (HB [] 4 1 13 ((2, 2) :: (4, 2) :: (1, 1) :: repeat (1, 2) 35 ++ (63, 2) :: (1, 1) :: repeat (1, 2) 1066 ++ (4225, 2) :: (1, 1) :: repeat (1, 2) 9841 ++ (9478, 2) :: (1, 1) :: repeat (1, 2) 50294 ++ (640074, 2) :: (1, 1) :: repeat (1, 2) 1511339 ++ (5653179, 2) :: (1, 1) :: repeat (1, 2) 11874956 ++ w) 1)).
  {
    apply (pop12 3 [] 1 7 ((2, 2) :: (4, 2) :: (1, 1) :: repeat (1, 2) 35 ++ (63, 2) :: (1, 1) :: repeat (1, 2) 1066 ++ (4225, 2) :: (1, 1) :: repeat (1, 2) 9841 ++ (9478, 2) :: (1, 1) :: repeat (1, 2) 50294 ++ (640074, 2) :: (1, 1) :: repeat (1, 2) 1511339 ++ (5653179, 2) :: (1, 1) :: repeat (1, 2) 11874956 ++ w) 1); closearith.
  }
  (* step 166: P TUP2_1 *)
  apply (hsteps_trans _ (HC [5] 13 1 2 ((2, 2) :: (1, 1) :: repeat (1, 2) 35 ++ (63, 2) :: (1, 1) :: repeat (1, 2) 1066 ++ (4225, 2) :: (1, 1) :: repeat (1, 2) 9841 ++ (9478, 2) :: (1, 1) :: repeat (1, 2) 50294 ++ (640074, 2) :: (1, 1) :: repeat (1, 2) 1511339 ++ (5653179, 2) :: (1, 1) :: repeat (1, 2) 11874956 ++ w) 1)).
  {
    replace ((2, 2) :: (1, 1) :: repeat (1, 2) 35 ++ (63, 2) :: (1, 1) :: repeat (1, 2) 1066 ++ (4225, 2) :: (1, 1) :: repeat (1, 2) 9841 ++ (9478, 2) :: (1, 1) :: repeat (1, 2) 50294 ++ (640074, 2) :: (1, 1) :: repeat (1, 2) 1511339 ++ (5653179, 2) :: (1, 1) :: repeat (1, 2) 11874956 ++ w) with ((4 - 2, 2) :: (1, 1) :: repeat (1, 2) 35 ++ (63, 2) :: (1, 1) :: repeat (1, 2) 1066 ++ (4225, 2) :: (1, 1) :: repeat (1, 2) 9841 ++ (9478, 2) :: (1, 1) :: repeat (1, 2) 50294 ++ (640074, 2) :: (1, 1) :: repeat (1, 2) 1511339 ++ (5653179, 2) :: (1, 1) :: repeat (1, 2) 11874956 ++ w) by sec_eq.
    apply (sTUP2_1 [] 4 12 4 ((1, 1) :: repeat (1, 2) 35 ++ (63, 2) :: (1, 1) :: repeat (1, 2) 1066 ++ (4225, 2) :: (1, 1) :: repeat (1, 2) 9841 ++ (9478, 2) :: (1, 1) :: repeat (1, 2) 50294 ++ (640074, 2) :: (1, 1) :: repeat (1, 2) 1511339 ++ (5653179, 2) :: (1, 1) :: repeat (1, 2) 11874956 ++ w) 1); closearith.
  }
  (* step 167: P TDN *)
  apply (hsteps_trans _ (HB [5] 13 1 4 ((2, 2) :: (1, 1) :: repeat (1, 2) 35 ++ (63, 2) :: (1, 1) :: repeat (1, 2) 1066 ++ (4225, 2) :: (1, 1) :: repeat (1, 2) 9841 ++ (9478, 2) :: (1, 1) :: repeat (1, 2) 50294 ++ (640074, 2) :: (1, 1) :: repeat (1, 2) 1511339 ++ (5653179, 2) :: (1, 1) :: repeat (1, 2) 11874956 ++ w) 1)).
  {
    apply (sTDN [5] 13 ((2, 2) :: (1, 1) :: repeat (1, 2) 35 ++ (63, 2) :: (1, 1) :: repeat (1, 2) 1066 ++ (4225, 2) :: (1, 1) :: repeat (1, 2) 9841 ++ (9478, 2) :: (1, 1) :: repeat (1, 2) 50294 ++ (640074, 2) :: (1, 1) :: repeat (1, 2) 1511339 ++ (5653179, 2) :: (1, 1) :: repeat (1, 2) 11874956 ++ w) 1).
  }
  (* step 168: P TRANS2_1 *)
  apply (sTRANS2_1 [5] 13 3 1 (repeat (1, 2) 35 ++ (63, 2) :: (1, 1) :: repeat (1, 2) 1066 ++ (4225, 2) :: (1, 1) :: repeat (1, 2) 9841 ++ (9478, 2) :: (1, 1) :: repeat (1, 2) 50294 ++ (640074, 2) :: (1, 1) :: repeat (1, 2) 1511339 ++ (5653179, 2) :: (1, 1) :: repeat (1, 2) 11874956 ++ w) 1); closearith.
Qed.

(* CASCADE58d: steps 169-224 of the CASCADE58 chain. *)
Lemma CASCADE58d : forall w,
  hsteps (HB [14; 5] 5 1 3 (repeat (1, 2) 35 ++ (63, 2) :: (1, 1) :: repeat (1, 2) 1066 ++ (4225, 2) :: (1, 1) :: repeat (1, 2) 9841 ++ (9478, 2) :: (1, 1) :: repeat (1, 2) 50294 ++ (640074, 2) :: (1, 1) :: repeat (1, 2) 1511339 ++ (5653179, 2) :: (1, 1) :: repeat (1, 2) 11874956 ++ w) 1)
         (HB [19; 0] 32 1 4 ((6, 2) :: (1, 1) :: repeat (1, 2) 1140 ++ (9757, 2) :: (1, 1) :: repeat (1, 2) 23909 ++ (11951, 2) :: (1, 1) :: repeat (1, 2) 100592 ++ (438888, 2) :: (1, 1) :: repeat (1, 2) 1511339 ++ (5653179, 2) :: (1, 1) :: repeat (1, 2) 11874956 ++ w) 1).
Proof.
  intro w.
  (* step 169: M pop12 (35,) *)
  apply (hsteps_trans _ (HB [14; 5] 40 1 73 ((63, 2) :: (1, 1) :: repeat (1, 2) 1066 ++ (4225, 2) :: (1, 1) :: repeat (1, 2) 9841 ++ (9478, 2) :: (1, 1) :: repeat (1, 2) 50294 ++ (640074, 2) :: (1, 1) :: repeat (1, 2) 1511339 ++ (5653179, 2) :: (1, 1) :: repeat (1, 2) 11874956 ++ w) 1)).
  {
    apply (pop12 35 [14; 5] 5 3 ((63, 2) :: (1, 1) :: repeat (1, 2) 1066 ++ (4225, 2) :: (1, 1) :: repeat (1, 2) 9841 ++ (9478, 2) :: (1, 1) :: repeat (1, 2) 50294 ++ (640074, 2) :: (1, 1) :: repeat (1, 2) 1511339 ++ (5653179, 2) :: (1, 1) :: repeat (1, 2) 11874956 ++ w) 1); closearith.
  }
  (* step 170: sTUP *)
  apply (hsteps_trans _ (HC [14; 5] 40 72 2 ((61, 2) :: (1, 1) :: repeat (1, 2) 1066 ++ (4225, 2) :: (1, 1) :: repeat (1, 2) 9841 ++ (9478, 2) :: (1, 1) :: repeat (1, 2) 50294 ++ (640074, 2) :: (1, 1) :: repeat (1, 2) 1511339 ++ (5653179, 2) :: (1, 1) :: repeat (1, 2) 11874956 ++ w) 1)).
  {
    replace ((61, 2) :: (1, 1) :: repeat (1, 2) 1066 ++ (4225, 2) :: (1, 1) :: repeat (1, 2) 9841 ++ (9478, 2) :: (1, 1) :: repeat (1, 2) 50294 ++ (640074, 2) :: (1, 1) :: repeat (1, 2) 1511339 ++ (5653179, 2) :: (1, 1) :: repeat (1, 2) 11874956 ++ w) with ((63 - 2, 2) :: (1, 1) :: repeat (1, 2) 1066 ++ (4225, 2) :: (1, 1) :: repeat (1, 2) 9841 ++ (9478, 2) :: (1, 1) :: repeat (1, 2) 50294 ++ (640074, 2) :: (1, 1) :: repeat (1, 2) 1511339 ++ (5653179, 2) :: (1, 1) :: repeat (1, 2) 11874956 ++ w) by sec_eq.
    apply (sTUP [14; 5] 40 73 63 2 ((1, 1) :: repeat (1, 2) 1066 ++ (4225, 2) :: (1, 1) :: repeat (1, 2) 9841 ++ (9478, 2) :: (1, 1) :: repeat (1, 2) 50294 ++ (640074, 2) :: (1, 1) :: repeat (1, 2) 1511339 ++ (5653179, 2) :: (1, 1) :: repeat (1, 2) 11874956 ++ w) 1); closearith.
  }
  (* step 171: hGRIND_even 34 *)
  apply (hsteps_trans _ (HB [14; 5] 39 1 72 ((2, 2) :: (61, 2) :: (1, 1) :: repeat (1, 2) 1066 ++ (4225, 2) :: (1, 1) :: repeat (1, 2) 9841 ++ (9478, 2) :: (1, 1) :: repeat (1, 2) 50294 ++ (640074, 2) :: (1, 1) :: repeat (1, 2) 1511339 ++ (5653179, 2) :: (1, 1) :: repeat (1, 2) 11874956 ++ w) 1)).
  {
    apply (hGRIND_even 34 [14; 5] 39 ((61, 2) :: (1, 1) :: repeat (1, 2) 1066 ++ (4225, 2) :: (1, 1) :: repeat (1, 2) 9841 ++ (9478, 2) :: (1, 1) :: repeat (1, 2) 50294 ++ (640074, 2) :: (1, 1) :: repeat (1, 2) 1511339 ++ (5653179, 2) :: (1, 1) :: repeat (1, 2) 11874956 ++ w) 1); closearith.
  }
  (* step 172: P TUP2_1 *)
  apply (hsteps_trans _ (HC [40; 14; 5] 72 1 2 ((59, 2) :: (1, 1) :: repeat (1, 2) 1066 ++ (4225, 2) :: (1, 1) :: repeat (1, 2) 9841 ++ (9478, 2) :: (1, 1) :: repeat (1, 2) 50294 ++ (640074, 2) :: (1, 1) :: repeat (1, 2) 1511339 ++ (5653179, 2) :: (1, 1) :: repeat (1, 2) 11874956 ++ w) 1)).
  {
    replace ((59, 2) :: (1, 1) :: repeat (1, 2) 1066 ++ (4225, 2) :: (1, 1) :: repeat (1, 2) 9841 ++ (9478, 2) :: (1, 1) :: repeat (1, 2) 50294 ++ (640074, 2) :: (1, 1) :: repeat (1, 2) 1511339 ++ (5653179, 2) :: (1, 1) :: repeat (1, 2) 11874956 ++ w) with ((61 - 2, 2) :: (1, 1) :: repeat (1, 2) 1066 ++ (4225, 2) :: (1, 1) :: repeat (1, 2) 9841 ++ (9478, 2) :: (1, 1) :: repeat (1, 2) 50294 ++ (640074, 2) :: (1, 1) :: repeat (1, 2) 1511339 ++ (5653179, 2) :: (1, 1) :: repeat (1, 2) 11874956 ++ w) by sec_eq.
    apply (sTUP2_1 [14; 5] 39 71 61 ((1, 1) :: repeat (1, 2) 1066 ++ (4225, 2) :: (1, 1) :: repeat (1, 2) 9841 ++ (9478, 2) :: (1, 1) :: repeat (1, 2) 50294 ++ (640074, 2) :: (1, 1) :: repeat (1, 2) 1511339 ++ (5653179, 2) :: (1, 1) :: repeat (1, 2) 11874956 ++ w) 1); closearith.
  }
  (* step 173: P TDN *)
  apply (hsteps_trans _ (HB [40; 14; 5] 72 1 4 ((59, 2) :: (1, 1) :: repeat (1, 2) 1066 ++ (4225, 2) :: (1, 1) :: repeat (1, 2) 9841 ++ (9478, 2) :: (1, 1) :: repeat (1, 2) 50294 ++ (640074, 2) :: (1, 1) :: repeat (1, 2) 1511339 ++ (5653179, 2) :: (1, 1) :: repeat (1, 2) 11874956 ++ w) 1)).
  {
    apply (sTDN [40; 14; 5] 72 ((59, 2) :: (1, 1) :: repeat (1, 2) 1066 ++ (4225, 2) :: (1, 1) :: repeat (1, 2) 9841 ++ (9478, 2) :: (1, 1) :: repeat (1, 2) 50294 ++ (640074, 2) :: (1, 1) :: repeat (1, 2) 1511339 ++ (5653179, 2) :: (1, 1) :: repeat (1, 2) 11874956 ++ w) 1).
  }
  (* step 174: sTUP *)
  apply (hsteps_trans _ (HC [40; 14; 5] 72 3 2 ((57, 2) :: (1, 1) :: repeat (1, 2) 1066 ++ (4225, 2) :: (1, 1) :: repeat (1, 2) 9841 ++ (9478, 2) :: (1, 1) :: repeat (1, 2) 50294 ++ (640074, 2) :: (1, 1) :: repeat (1, 2) 1511339 ++ (5653179, 2) :: (1, 1) :: repeat (1, 2) 11874956 ++ w) 1)).
  {
    replace ((57, 2) :: (1, 1) :: repeat (1, 2) 1066 ++ (4225, 2) :: (1, 1) :: repeat (1, 2) 9841 ++ (9478, 2) :: (1, 1) :: repeat (1, 2) 50294 ++ (640074, 2) :: (1, 1) :: repeat (1, 2) 1511339 ++ (5653179, 2) :: (1, 1) :: repeat (1, 2) 11874956 ++ w) with ((59 - 2, 2) :: (1, 1) :: repeat (1, 2) 1066 ++ (4225, 2) :: (1, 1) :: repeat (1, 2) 9841 ++ (9478, 2) :: (1, 1) :: repeat (1, 2) 50294 ++ (640074, 2) :: (1, 1) :: repeat (1, 2) 1511339 ++ (5653179, 2) :: (1, 1) :: repeat (1, 2) 11874956 ++ w) by sec_eq.
    apply (sTUP [40; 14; 5] 72 4 59 2 ((1, 1) :: repeat (1, 2) 1066 ++ (4225, 2) :: (1, 1) :: repeat (1, 2) 9841 ++ (9478, 2) :: (1, 1) :: repeat (1, 2) 50294 ++ (640074, 2) :: (1, 1) :: repeat (1, 2) 1511339 ++ (5653179, 2) :: (1, 1) :: repeat (1, 2) 11874956 ++ w) 1); closearith.
  }
  (* step 175: CLEANG_odd 27 *)
  apply (hsteps_trans _ (HB [40; 14; 5] 72 1 62 (repeat (1, 2) 1 ++ (1, 1) :: repeat (1, 2) 1066 ++ (4225, 2) :: (1, 1) :: repeat (1, 2) 9841 ++ (9478, 2) :: (1, 1) :: repeat (1, 2) 50294 ++ (640074, 2) :: (1, 1) :: repeat (1, 2) 1511339 ++ (5653179, 2) :: (1, 1) :: repeat (1, 2) 11874956 ++ w) 1)).
  {
    replace (repeat (1, 2) 1 ++ (1, 1) :: repeat (1, 2) 1066 ++ (4225, 2) :: (1, 1) :: repeat (1, 2) 9841 ++ (9478, 2) :: (1, 1) :: repeat (1, 2) 50294 ++ (640074, 2) :: (1, 1) :: repeat (1, 2) 1511339 ++ (5653179, 2) :: (1, 1) :: repeat (1, 2) 11874956 ++ w) with ((1, 2) :: (1, 1) :: repeat (1, 2) 1066 ++ (4225, 2) :: (1, 1) :: repeat (1, 2) 9841 ++ (9478, 2) :: (1, 1) :: repeat (1, 2) 50294 ++ (640074, 2) :: (1, 1) :: repeat (1, 2) 1511339 ++ (5653179, 2) :: (1, 1) :: repeat (1, 2) 11874956 ++ w) by sec_eq.
    apply (CLEANG_odd 27 [40; 14; 5] 72 ((1, 1) :: repeat (1, 2) 1066 ++ (4225, 2) :: (1, 1) :: repeat (1, 2) 9841 ++ (9478, 2) :: (1, 1) :: repeat (1, 2) 50294 ++ (640074, 2) :: (1, 1) :: repeat (1, 2) 1511339 ++ (5653179, 2) :: (1, 1) :: repeat (1, 2) 11874956 ++ w) 1); closearith.
  }
  (* step 176: M pop12 (1,) *)
  apply (hsteps_trans _ (HB [40; 14; 5] 73 1 64 ((1, 1) :: repeat (1, 2) 1066 ++ (4225, 2) :: (1, 1) :: repeat (1, 2) 9841 ++ (9478, 2) :: (1, 1) :: repeat (1, 2) 50294 ++ (640074, 2) :: (1, 1) :: repeat (1, 2) 1511339 ++ (5653179, 2) :: (1, 1) :: repeat (1, 2) 11874956 ++ w) 1)).
  {
    apply (pop12 1 [40; 14; 5] 72 62 ((1, 1) :: repeat (1, 2) 1066 ++ (4225, 2) :: (1, 1) :: repeat (1, 2) 9841 ++ (9478, 2) :: (1, 1) :: repeat (1, 2) 50294 ++ (640074, 2) :: (1, 1) :: repeat (1, 2) 1511339 ++ (5653179, 2) :: (1, 1) :: repeat (1, 2) 11874956 ++ w) 1); closearith.
  }
  (* step 177: P POP *)
  apply (hsteps_trans _ (HB [40; 14; 5] 74 1 65 (repeat (1, 2) 1066 ++ (4225, 2) :: (1, 1) :: repeat (1, 2) 9841 ++ (9478, 2) :: (1, 1) :: repeat (1, 2) 50294 ++ (640074, 2) :: (1, 1) :: repeat (1, 2) 1511339 ++ (5653179, 2) :: (1, 1) :: repeat (1, 2) 11874956 ++ w) 1)).
  {
    apply (sPOP1 [40; 14; 5] 73 64 (repeat (1, 2) 1066 ++ (4225, 2) :: (1, 1) :: repeat (1, 2) 9841 ++ (9478, 2) :: (1, 1) :: repeat (1, 2) 50294 ++ (640074, 2) :: (1, 1) :: repeat (1, 2) 1511339 ++ (5653179, 2) :: (1, 1) :: repeat (1, 2) 11874956 ++ w) 1); closearith.
  }
  (* step 178: M pop12 (1066,) *)
  apply (hsteps_trans _ (HB [40; 14; 5] 1140 1 2197 ((4225, 2) :: (1, 1) :: repeat (1, 2) 9841 ++ (9478, 2) :: (1, 1) :: repeat (1, 2) 50294 ++ (640074, 2) :: (1, 1) :: repeat (1, 2) 1511339 ++ (5653179, 2) :: (1, 1) :: repeat (1, 2) 11874956 ++ w) 1)).
  {
    apply (pop12 1066 [40; 14; 5] 74 65 ((4225, 2) :: (1, 1) :: repeat (1, 2) 9841 ++ (9478, 2) :: (1, 1) :: repeat (1, 2) 50294 ++ (640074, 2) :: (1, 1) :: repeat (1, 2) 1511339 ++ (5653179, 2) :: (1, 1) :: repeat (1, 2) 11874956 ++ w) 1); closearith.
  }
  (* step 179: sTUP *)
  apply (hsteps_trans _ (HC [40; 14; 5] 1140 2196 2 ((4223, 2) :: (1, 1) :: repeat (1, 2) 9841 ++ (9478, 2) :: (1, 1) :: repeat (1, 2) 50294 ++ (640074, 2) :: (1, 1) :: repeat (1, 2) 1511339 ++ (5653179, 2) :: (1, 1) :: repeat (1, 2) 11874956 ++ w) 1)).
  {
    replace ((4223, 2) :: (1, 1) :: repeat (1, 2) 9841 ++ (9478, 2) :: (1, 1) :: repeat (1, 2) 50294 ++ (640074, 2) :: (1, 1) :: repeat (1, 2) 1511339 ++ (5653179, 2) :: (1, 1) :: repeat (1, 2) 11874956 ++ w) with ((4225 - 2, 2) :: (1, 1) :: repeat (1, 2) 9841 ++ (9478, 2) :: (1, 1) :: repeat (1, 2) 50294 ++ (640074, 2) :: (1, 1) :: repeat (1, 2) 1511339 ++ (5653179, 2) :: (1, 1) :: repeat (1, 2) 11874956 ++ w) by sec_eq.
    apply (sTUP [40; 14; 5] 1140 2197 4225 2 ((1, 1) :: repeat (1, 2) 9841 ++ (9478, 2) :: (1, 1) :: repeat (1, 2) 50294 ++ (640074, 2) :: (1, 1) :: repeat (1, 2) 1511339 ++ (5653179, 2) :: (1, 1) :: repeat (1, 2) 11874956 ++ w) 1); closearith.
  }
  (* step 180: hGRIND_even 1096 *)
  apply (hsteps_trans _ (HB [40; 14; 5] 1139 1 2196 ((2, 2) :: (4223, 2) :: (1, 1) :: repeat (1, 2) 9841 ++ (9478, 2) :: (1, 1) :: repeat (1, 2) 50294 ++ (640074, 2) :: (1, 1) :: repeat (1, 2) 1511339 ++ (5653179, 2) :: (1, 1) :: repeat (1, 2) 11874956 ++ w) 1)).
  {
    apply (hGRIND_even 1096 [40; 14; 5] 1139 ((4223, 2) :: (1, 1) :: repeat (1, 2) 9841 ++ (9478, 2) :: (1, 1) :: repeat (1, 2) 50294 ++ (640074, 2) :: (1, 1) :: repeat (1, 2) 1511339 ++ (5653179, 2) :: (1, 1) :: repeat (1, 2) 11874956 ++ w) 1); closearith.
  }
  (* step 181: P TUP2_1 *)
  apply (hsteps_trans _ (HC [1140; 40; 14; 5] 2196 1 2 ((4221, 2) :: (1, 1) :: repeat (1, 2) 9841 ++ (9478, 2) :: (1, 1) :: repeat (1, 2) 50294 ++ (640074, 2) :: (1, 1) :: repeat (1, 2) 1511339 ++ (5653179, 2) :: (1, 1) :: repeat (1, 2) 11874956 ++ w) 1)).
  {
    replace ((4221, 2) :: (1, 1) :: repeat (1, 2) 9841 ++ (9478, 2) :: (1, 1) :: repeat (1, 2) 50294 ++ (640074, 2) :: (1, 1) :: repeat (1, 2) 1511339 ++ (5653179, 2) :: (1, 1) :: repeat (1, 2) 11874956 ++ w) with ((4223 - 2, 2) :: (1, 1) :: repeat (1, 2) 9841 ++ (9478, 2) :: (1, 1) :: repeat (1, 2) 50294 ++ (640074, 2) :: (1, 1) :: repeat (1, 2) 1511339 ++ (5653179, 2) :: (1, 1) :: repeat (1, 2) 11874956 ++ w) by sec_eq.
    apply (sTUP2_1 [40; 14; 5] 1139 2195 4223 ((1, 1) :: repeat (1, 2) 9841 ++ (9478, 2) :: (1, 1) :: repeat (1, 2) 50294 ++ (640074, 2) :: (1, 1) :: repeat (1, 2) 1511339 ++ (5653179, 2) :: (1, 1) :: repeat (1, 2) 11874956 ++ w) 1); closearith.
  }
  (* step 182: P TDN *)
  apply (hsteps_trans _ (HB [1140; 40; 14; 5] 2196 1 4 ((4221, 2) :: (1, 1) :: repeat (1, 2) 9841 ++ (9478, 2) :: (1, 1) :: repeat (1, 2) 50294 ++ (640074, 2) :: (1, 1) :: repeat (1, 2) 1511339 ++ (5653179, 2) :: (1, 1) :: repeat (1, 2) 11874956 ++ w) 1)).
  {
    apply (sTDN [1140; 40; 14; 5] 2196 ((4221, 2) :: (1, 1) :: repeat (1, 2) 9841 ++ (9478, 2) :: (1, 1) :: repeat (1, 2) 50294 ++ (640074, 2) :: (1, 1) :: repeat (1, 2) 1511339 ++ (5653179, 2) :: (1, 1) :: repeat (1, 2) 11874956 ++ w) 1).
  }
  (* step 183: sTUP *)
  apply (hsteps_trans _ (HC [1140; 40; 14; 5] 2196 3 2 ((4219, 2) :: (1, 1) :: repeat (1, 2) 9841 ++ (9478, 2) :: (1, 1) :: repeat (1, 2) 50294 ++ (640074, 2) :: (1, 1) :: repeat (1, 2) 1511339 ++ (5653179, 2) :: (1, 1) :: repeat (1, 2) 11874956 ++ w) 1)).
  {
    replace ((4219, 2) :: (1, 1) :: repeat (1, 2) 9841 ++ (9478, 2) :: (1, 1) :: repeat (1, 2) 50294 ++ (640074, 2) :: (1, 1) :: repeat (1, 2) 1511339 ++ (5653179, 2) :: (1, 1) :: repeat (1, 2) 11874956 ++ w) with ((4221 - 2, 2) :: (1, 1) :: repeat (1, 2) 9841 ++ (9478, 2) :: (1, 1) :: repeat (1, 2) 50294 ++ (640074, 2) :: (1, 1) :: repeat (1, 2) 1511339 ++ (5653179, 2) :: (1, 1) :: repeat (1, 2) 11874956 ++ w) by sec_eq.
    apply (sTUP [1140; 40; 14; 5] 2196 4 4221 2 ((1, 1) :: repeat (1, 2) 9841 ++ (9478, 2) :: (1, 1) :: repeat (1, 2) 50294 ++ (640074, 2) :: (1, 1) :: repeat (1, 2) 1511339 ++ (5653179, 2) :: (1, 1) :: repeat (1, 2) 11874956 ++ w) 1); closearith.
  }
  (* step 184: CLEANG_odd 2108 *)
  apply (hsteps_trans _ (HB [1140; 40; 14; 5] 2196 1 4224 (repeat (1, 2) 1 ++ (1, 1) :: repeat (1, 2) 9841 ++ (9478, 2) :: (1, 1) :: repeat (1, 2) 50294 ++ (640074, 2) :: (1, 1) :: repeat (1, 2) 1511339 ++ (5653179, 2) :: (1, 1) :: repeat (1, 2) 11874956 ++ w) 1)).
  {
    replace (repeat (1, 2) 1 ++ (1, 1) :: repeat (1, 2) 9841 ++ (9478, 2) :: (1, 1) :: repeat (1, 2) 50294 ++ (640074, 2) :: (1, 1) :: repeat (1, 2) 1511339 ++ (5653179, 2) :: (1, 1) :: repeat (1, 2) 11874956 ++ w) with ((1, 2) :: (1, 1) :: repeat (1, 2) 9841 ++ (9478, 2) :: (1, 1) :: repeat (1, 2) 50294 ++ (640074, 2) :: (1, 1) :: repeat (1, 2) 1511339 ++ (5653179, 2) :: (1, 1) :: repeat (1, 2) 11874956 ++ w) by sec_eq.
    apply (CLEANG_odd 2108 [1140; 40; 14; 5] 2196 ((1, 1) :: repeat (1, 2) 9841 ++ (9478, 2) :: (1, 1) :: repeat (1, 2) 50294 ++ (640074, 2) :: (1, 1) :: repeat (1, 2) 1511339 ++ (5653179, 2) :: (1, 1) :: repeat (1, 2) 11874956 ++ w) 1); closearith.
  }
  (* step 185: M pop12 (1,) *)
  apply (hsteps_trans _ (HB [1140; 40; 14; 5] 2197 1 4226 ((1, 1) :: repeat (1, 2) 9841 ++ (9478, 2) :: (1, 1) :: repeat (1, 2) 50294 ++ (640074, 2) :: (1, 1) :: repeat (1, 2) 1511339 ++ (5653179, 2) :: (1, 1) :: repeat (1, 2) 11874956 ++ w) 1)).
  {
    apply (pop12 1 [1140; 40; 14; 5] 2196 4224 ((1, 1) :: repeat (1, 2) 9841 ++ (9478, 2) :: (1, 1) :: repeat (1, 2) 50294 ++ (640074, 2) :: (1, 1) :: repeat (1, 2) 1511339 ++ (5653179, 2) :: (1, 1) :: repeat (1, 2) 11874956 ++ w) 1); closearith.
  }
  (* step 186: P POP *)
  apply (hsteps_trans _ (HB [1140; 40; 14; 5] 2198 1 4227 (repeat (1, 2) 9841 ++ (9478, 2) :: (1, 1) :: repeat (1, 2) 50294 ++ (640074, 2) :: (1, 1) :: repeat (1, 2) 1511339 ++ (5653179, 2) :: (1, 1) :: repeat (1, 2) 11874956 ++ w) 1)).
  {
    apply (sPOP1 [1140; 40; 14; 5] 2197 4226 (repeat (1, 2) 9841 ++ (9478, 2) :: (1, 1) :: repeat (1, 2) 50294 ++ (640074, 2) :: (1, 1) :: repeat (1, 2) 1511339 ++ (5653179, 2) :: (1, 1) :: repeat (1, 2) 11874956 ++ w) 1); closearith.
  }
  (* step 187: M pop12 (9841,) *)
  apply (hsteps_trans _ (HB [1140; 40; 14; 5] 12039 1 23909 ((9478, 2) :: (1, 1) :: repeat (1, 2) 50294 ++ (640074, 2) :: (1, 1) :: repeat (1, 2) 1511339 ++ (5653179, 2) :: (1, 1) :: repeat (1, 2) 11874956 ++ w) 1)).
  {
    apply (pop12 9841 [1140; 40; 14; 5] 2198 4227 ((9478, 2) :: (1, 1) :: repeat (1, 2) 50294 ++ (640074, 2) :: (1, 1) :: repeat (1, 2) 1511339 ++ (5653179, 2) :: (1, 1) :: repeat (1, 2) 11874956 ++ w) 1); closearith.
  }
  (* step 188: sTUP *)
  apply (hsteps_trans _ (HC [1140; 40; 14; 5] 12039 23908 2 ((9476, 2) :: (1, 1) :: repeat (1, 2) 50294 ++ (640074, 2) :: (1, 1) :: repeat (1, 2) 1511339 ++ (5653179, 2) :: (1, 1) :: repeat (1, 2) 11874956 ++ w) 1)).
  {
    replace ((9476, 2) :: (1, 1) :: repeat (1, 2) 50294 ++ (640074, 2) :: (1, 1) :: repeat (1, 2) 1511339 ++ (5653179, 2) :: (1, 1) :: repeat (1, 2) 11874956 ++ w) with ((9478 - 2, 2) :: (1, 1) :: repeat (1, 2) 50294 ++ (640074, 2) :: (1, 1) :: repeat (1, 2) 1511339 ++ (5653179, 2) :: (1, 1) :: repeat (1, 2) 11874956 ++ w) by sec_eq.
    apply (sTUP [1140; 40; 14; 5] 12039 23909 9478 2 ((1, 1) :: repeat (1, 2) 50294 ++ (640074, 2) :: (1, 1) :: repeat (1, 2) 1511339 ++ (5653179, 2) :: (1, 1) :: repeat (1, 2) 11874956 ++ w) 1); closearith.
  }
  (* step 189: hGRIND_even 11952 *)
  apply (hsteps_trans _ (HB [1140; 40; 14; 5] 12038 1 23908 ((2, 2) :: (9476, 2) :: (1, 1) :: repeat (1, 2) 50294 ++ (640074, 2) :: (1, 1) :: repeat (1, 2) 1511339 ++ (5653179, 2) :: (1, 1) :: repeat (1, 2) 11874956 ++ w) 1)).
  {
    apply (hGRIND_even 11952 [1140; 40; 14; 5] 12038 ((9476, 2) :: (1, 1) :: repeat (1, 2) 50294 ++ (640074, 2) :: (1, 1) :: repeat (1, 2) 1511339 ++ (5653179, 2) :: (1, 1) :: repeat (1, 2) 11874956 ++ w) 1); closearith.
  }
  (* step 190: P TUP2_1 *)
  apply (hsteps_trans _ (HC [12039; 1140; 40; 14; 5] 23908 1 2 ((9474, 2) :: (1, 1) :: repeat (1, 2) 50294 ++ (640074, 2) :: (1, 1) :: repeat (1, 2) 1511339 ++ (5653179, 2) :: (1, 1) :: repeat (1, 2) 11874956 ++ w) 1)).
  {
    replace ((9474, 2) :: (1, 1) :: repeat (1, 2) 50294 ++ (640074, 2) :: (1, 1) :: repeat (1, 2) 1511339 ++ (5653179, 2) :: (1, 1) :: repeat (1, 2) 11874956 ++ w) with ((9476 - 2, 2) :: (1, 1) :: repeat (1, 2) 50294 ++ (640074, 2) :: (1, 1) :: repeat (1, 2) 1511339 ++ (5653179, 2) :: (1, 1) :: repeat (1, 2) 11874956 ++ w) by sec_eq.
    apply (sTUP2_1 [1140; 40; 14; 5] 12038 23907 9476 ((1, 1) :: repeat (1, 2) 50294 ++ (640074, 2) :: (1, 1) :: repeat (1, 2) 1511339 ++ (5653179, 2) :: (1, 1) :: repeat (1, 2) 11874956 ++ w) 1); closearith.
  }
  (* step 191: P TDN *)
  apply (hsteps_trans _ (HB [12039; 1140; 40; 14; 5] 23908 1 4 ((9474, 2) :: (1, 1) :: repeat (1, 2) 50294 ++ (640074, 2) :: (1, 1) :: repeat (1, 2) 1511339 ++ (5653179, 2) :: (1, 1) :: repeat (1, 2) 11874956 ++ w) 1)).
  {
    apply (sTDN [12039; 1140; 40; 14; 5] 23908 ((9474, 2) :: (1, 1) :: repeat (1, 2) 50294 ++ (640074, 2) :: (1, 1) :: repeat (1, 2) 1511339 ++ (5653179, 2) :: (1, 1) :: repeat (1, 2) 11874956 ++ w) 1).
  }
  (* step 192: sTUP *)
  apply (hsteps_trans _ (HC [12039; 1140; 40; 14; 5] 23908 3 2 ((9472, 2) :: (1, 1) :: repeat (1, 2) 50294 ++ (640074, 2) :: (1, 1) :: repeat (1, 2) 1511339 ++ (5653179, 2) :: (1, 1) :: repeat (1, 2) 11874956 ++ w) 1)).
  {
    replace ((9472, 2) :: (1, 1) :: repeat (1, 2) 50294 ++ (640074, 2) :: (1, 1) :: repeat (1, 2) 1511339 ++ (5653179, 2) :: (1, 1) :: repeat (1, 2) 11874956 ++ w) with ((9474 - 2, 2) :: (1, 1) :: repeat (1, 2) 50294 ++ (640074, 2) :: (1, 1) :: repeat (1, 2) 1511339 ++ (5653179, 2) :: (1, 1) :: repeat (1, 2) 11874956 ++ w) by sec_eq.
    apply (sTUP [12039; 1140; 40; 14; 5] 23908 4 9474 2 ((1, 1) :: repeat (1, 2) 50294 ++ (640074, 2) :: (1, 1) :: repeat (1, 2) 1511339 ++ (5653179, 2) :: (1, 1) :: repeat (1, 2) 11874956 ++ w) 1); closearith.
  }
  (* step 193: CLEANG_even 4735 *)
  apply (hsteps_trans _ (HB [12039; 1140; 40; 14; 5] 23908 1 9476 ((2, 2) :: (1, 1) :: repeat (1, 2) 50294 ++ (640074, 2) :: (1, 1) :: repeat (1, 2) 1511339 ++ (5653179, 2) :: (1, 1) :: repeat (1, 2) 11874956 ++ w) 1)).
  {
    apply (CLEANG_even 4735 [12039; 1140; 40; 14; 5] 23908 ((1, 1) :: repeat (1, 2) 50294 ++ (640074, 2) :: (1, 1) :: repeat (1, 2) 1511339 ++ (5653179, 2) :: (1, 1) :: repeat (1, 2) 11874956 ++ w) 1); closearith.
  }
  (* step 194: P TRANS2_1 *)
  apply (hsteps_trans _ (HB [23909; 12039; 1140; 40; 14; 5] 9477 1 3 (repeat (1, 2) 50294 ++ (640074, 2) :: (1, 1) :: repeat (1, 2) 1511339 ++ (5653179, 2) :: (1, 1) :: repeat (1, 2) 11874956 ++ w) 1)).
  {
    apply (sTRANS2_1 [12039; 1140; 40; 14; 5] 23908 9475 1 (repeat (1, 2) 50294 ++ (640074, 2) :: (1, 1) :: repeat (1, 2) 1511339 ++ (5653179, 2) :: (1, 1) :: repeat (1, 2) 11874956 ++ w) 1); closearith.
  }
  (* step 195: M pop12 (50294,) *)
  apply (hsteps_trans _ (HB [23909; 12039; 1140; 40; 14; 5] 59771 1 100591 ((640074, 2) :: (1, 1) :: repeat (1, 2) 1511339 ++ (5653179, 2) :: (1, 1) :: repeat (1, 2) 11874956 ++ w) 1)).
  {
    apply (pop12 50294 [23909; 12039; 1140; 40; 14; 5] 9477 3 ((640074, 2) :: (1, 1) :: repeat (1, 2) 1511339 ++ (5653179, 2) :: (1, 1) :: repeat (1, 2) 11874956 ++ w) 1); closearith.
  }
  (* step 196: sTUP *)
  apply (hsteps_trans _ (HC [23909; 12039; 1140; 40; 14; 5] 59771 100590 2 ((640072, 2) :: (1, 1) :: repeat (1, 2) 1511339 ++ (5653179, 2) :: (1, 1) :: repeat (1, 2) 11874956 ++ w) 1)).
  {
    rewrite NUM58X13.
    rewrite NUM58X14.
    apply (sTUP [23909; 12039; 1140; 40; 14; 5] 59771 100591 640074 2 ((1, 1) :: repeat (1, 2) 1511339 ++ (5653179, 2) :: (1, 1) :: repeat (1, 2) 11874956 ++ w) 1); closearith.
  }
  (* step 197: hGRIND_even 50293 *)
  apply (hsteps_trans _ (HB [23909; 12039; 1140; 40; 14; 5] 59770 1 100590 ((2, 2) :: (640072, 2) :: (1, 1) :: repeat (1, 2) 1511339 ++ (5653179, 2) :: (1, 1) :: repeat (1, 2) 11874956 ++ w) 1)).
  {
    rewrite NUM58X15.
    apply (hGRIND_even 50293 [23909; 12039; 1140; 40; 14; 5] 59770 ((640072, 2) :: (1, 1) :: repeat (1, 2) 1511339 ++ (5653179, 2) :: (1, 1) :: repeat (1, 2) 11874956 ++ w) 1); closearith.
  }
  (* step 198: P TUP2_1 *)
  apply (hsteps_trans _ (HC [59771; 23909; 12039; 1140; 40; 14; 5] 100590 1 2 ((640070, 2) :: (1, 1) :: repeat (1, 2) 1511339 ++ (5653179, 2) :: (1, 1) :: repeat (1, 2) 11874956 ++ w) 1)).
  {
    rewrite NUM58X16.
    rewrite NUM58X17.
    apply (sTUP2_1 [23909; 12039; 1140; 40; 14; 5] 59770 100589 640072 ((1, 1) :: repeat (1, 2) 1511339 ++ (5653179, 2) :: (1, 1) :: repeat (1, 2) 11874956 ++ w) 1); closearith.
  }
  (* step 199: P TDN *)
  apply (hsteps_trans _ (HB [59771; 23909; 12039; 1140; 40; 14; 5] 100590 1 4 ((640070, 2) :: (1, 1) :: repeat (1, 2) 1511339 ++ (5653179, 2) :: (1, 1) :: repeat (1, 2) 11874956 ++ w) 1)).
  {
    apply (sTDN [59771; 23909; 12039; 1140; 40; 14; 5] 100590 ((640070, 2) :: (1, 1) :: repeat (1, 2) 1511339 ++ (5653179, 2) :: (1, 1) :: repeat (1, 2) 11874956 ++ w) 1).
  }
  (* step 200: sTUP *)
  apply (hsteps_trans _ (HC [59771; 23909; 12039; 1140; 40; 14; 5] 100590 3 2 ((640068, 2) :: (1, 1) :: repeat (1, 2) 1511339 ++ (5653179, 2) :: (1, 1) :: repeat (1, 2) 11874956 ++ w) 1)).
  {
    rewrite NUM58X18.
    apply (sTUP [59771; 23909; 12039; 1140; 40; 14; 5] 100590 4 640070 2 ((1, 1) :: repeat (1, 2) 1511339 ++ (5653179, 2) :: (1, 1) :: repeat (1, 2) 11874956 ++ w) 1); closearith.
  }
  (* step 201: DIPGRIND 100590 438888 *)
  apply (hsteps_trans _ (HC [59771; 23909; 12039; 1140; 40; 14; 5] 0 3 2 (repeat (1, 2) 100590 ++ (438888, 2) :: (1, 1) :: repeat (1, 2) 1511339 ++ (5653179, 2) :: (1, 1) :: repeat (1, 2) 11874956 ++ w) 1)).
  {
    rewrite NUM58X19.
    apply (DIPGRIND 100590 438888 [59771; 23909; 12039; 1140; 40; 14; 5] ((1, 1) :: repeat (1, 2) 1511339 ++ (5653179, 2) :: (1, 1) :: repeat (1, 2) 11874956 ++ w) 1); closearith.
  }
  (* step 202: P PX2A *)
  apply (hsteps_trans _ (HC [12039; 1140; 40; 14; 5] 23908 59769 2 ((1, 1) :: repeat (1, 2) 100592 ++ (438888, 2) :: (1, 1) :: repeat (1, 2) 1511339 ++ (5653179, 2) :: (1, 1) :: repeat (1, 2) 11874956 ++ w) 1)).
  {
    exact (hsteps_step _ _ _ (hPX2A 59768 23908 [12039; 1140; 40; 14; 5] (repeat (1, 2) 100590 ++ (438888, 2) :: (1, 1) :: repeat (1, 2) 1511339 ++ (5653179, 2) :: (1, 1) :: repeat (1, 2) 11874956 ++ w) 1) (hsteps_refl _)).
  }
  (* step 203: P PUSH *)
  apply (hsteps_trans _ (HC [12039; 1140; 40; 14; 5] 23907 1 2 ((59767, 2) :: (1, 1) :: repeat (1, 2) 100592 ++ (438888, 2) :: (1, 1) :: repeat (1, 2) 1511339 ++ (5653179, 2) :: (1, 1) :: repeat (1, 2) 11874956 ++ w) 1)).
  {
    replace ((59767, 2) :: (1, 1) :: repeat (1, 2) 100592 ++ (438888, 2) :: (1, 1) :: repeat (1, 2) 1511339 ++ (5653179, 2) :: (1, 1) :: repeat (1, 2) 11874956 ++ w) with ((59769 - 2, 2) :: (1, 1) :: repeat (1, 2) 100592 ++ (438888, 2) :: (1, 1) :: repeat (1, 2) 1511339 ++ (5653179, 2) :: (1, 1) :: repeat (1, 2) 11874956 ++ w) by sec_eq.
    apply (sPUSH [12039; 1140; 40; 14; 5] 23907 59769 ((1, 1) :: repeat (1, 2) 100592 ++ (438888, 2) :: (1, 1) :: repeat (1, 2) 1511339 ++ (5653179, 2) :: (1, 1) :: repeat (1, 2) 11874956 ++ w) 1); closearith.
  }
  (* step 204: P TDN *)
  apply (hsteps_trans _ (HB [12039; 1140; 40; 14; 5] 23907 1 4 ((59767, 2) :: (1, 1) :: repeat (1, 2) 100592 ++ (438888, 2) :: (1, 1) :: repeat (1, 2) 1511339 ++ (5653179, 2) :: (1, 1) :: repeat (1, 2) 11874956 ++ w) 1)).
  {
    apply (sTDN [12039; 1140; 40; 14; 5] 23907 ((59767, 2) :: (1, 1) :: repeat (1, 2) 100592 ++ (438888, 2) :: (1, 1) :: repeat (1, 2) 1511339 ++ (5653179, 2) :: (1, 1) :: repeat (1, 2) 11874956 ++ w) 1).
  }
  (* step 205: sTUP *)
  apply (hsteps_trans _ (HC [12039; 1140; 40; 14; 5] 23907 3 2 ((59765, 2) :: (1, 1) :: repeat (1, 2) 100592 ++ (438888, 2) :: (1, 1) :: repeat (1, 2) 1511339 ++ (5653179, 2) :: (1, 1) :: repeat (1, 2) 11874956 ++ w) 1)).
  {
    replace ((59765, 2) :: (1, 1) :: repeat (1, 2) 100592 ++ (438888, 2) :: (1, 1) :: repeat (1, 2) 1511339 ++ (5653179, 2) :: (1, 1) :: repeat (1, 2) 11874956 ++ w) with ((59767 - 2, 2) :: (1, 1) :: repeat (1, 2) 100592 ++ (438888, 2) :: (1, 1) :: repeat (1, 2) 1511339 ++ (5653179, 2) :: (1, 1) :: repeat (1, 2) 11874956 ++ w) by sec_eq.
    apply (sTUP [12039; 1140; 40; 14; 5] 23907 4 59767 2 ((1, 1) :: repeat (1, 2) 100592 ++ (438888, 2) :: (1, 1) :: repeat (1, 2) 1511339 ++ (5653179, 2) :: (1, 1) :: repeat (1, 2) 11874956 ++ w) 1); closearith.
  }
  (* step 206: DIPGRIND 23907 11951 *)
  apply (hsteps_trans _ (HC [12039; 1140; 40; 14; 5] 0 3 2 (repeat (1, 2) 23907 ++ (11951, 2) :: (1, 1) :: repeat (1, 2) 100592 ++ (438888, 2) :: (1, 1) :: repeat (1, 2) 1511339 ++ (5653179, 2) :: (1, 1) :: repeat (1, 2) 11874956 ++ w) 1)).
  {
    apply (DIPGRIND 23907 11951 [12039; 1140; 40; 14; 5] ((1, 1) :: repeat (1, 2) 100592 ++ (438888, 2) :: (1, 1) :: repeat (1, 2) 1511339 ++ (5653179, 2) :: (1, 1) :: repeat (1, 2) 11874956 ++ w) 1); closearith.
  }
  (* step 207: P PX2A *)
  apply (hsteps_trans _ (HC [40; 14; 5] 1139 12037 2 ((1, 1) :: repeat (1, 2) 23909 ++ (11951, 2) :: (1, 1) :: repeat (1, 2) 100592 ++ (438888, 2) :: (1, 1) :: repeat (1, 2) 1511339 ++ (5653179, 2) :: (1, 1) :: repeat (1, 2) 11874956 ++ w) 1)).
  {
    exact (hsteps_step _ _ _ (hPX2A 12036 1139 [40; 14; 5] (repeat (1, 2) 23907 ++ (11951, 2) :: (1, 1) :: repeat (1, 2) 100592 ++ (438888, 2) :: (1, 1) :: repeat (1, 2) 1511339 ++ (5653179, 2) :: (1, 1) :: repeat (1, 2) 11874956 ++ w) 1) (hsteps_refl _)).
  }
  (* step 208: P PUSH *)
  apply (hsteps_trans _ (HC [40; 14; 5] 1138 1 2 ((12035, 2) :: (1, 1) :: repeat (1, 2) 23909 ++ (11951, 2) :: (1, 1) :: repeat (1, 2) 100592 ++ (438888, 2) :: (1, 1) :: repeat (1, 2) 1511339 ++ (5653179, 2) :: (1, 1) :: repeat (1, 2) 11874956 ++ w) 1)).
  {
    replace ((12035, 2) :: (1, 1) :: repeat (1, 2) 23909 ++ (11951, 2) :: (1, 1) :: repeat (1, 2) 100592 ++ (438888, 2) :: (1, 1) :: repeat (1, 2) 1511339 ++ (5653179, 2) :: (1, 1) :: repeat (1, 2) 11874956 ++ w) with ((12037 - 2, 2) :: (1, 1) :: repeat (1, 2) 23909 ++ (11951, 2) :: (1, 1) :: repeat (1, 2) 100592 ++ (438888, 2) :: (1, 1) :: repeat (1, 2) 1511339 ++ (5653179, 2) :: (1, 1) :: repeat (1, 2) 11874956 ++ w) by sec_eq.
    apply (sPUSH [40; 14; 5] 1138 12037 ((1, 1) :: repeat (1, 2) 23909 ++ (11951, 2) :: (1, 1) :: repeat (1, 2) 100592 ++ (438888, 2) :: (1, 1) :: repeat (1, 2) 1511339 ++ (5653179, 2) :: (1, 1) :: repeat (1, 2) 11874956 ++ w) 1); closearith.
  }
  (* step 209: P TDN *)
  apply (hsteps_trans _ (HB [40; 14; 5] 1138 1 4 ((12035, 2) :: (1, 1) :: repeat (1, 2) 23909 ++ (11951, 2) :: (1, 1) :: repeat (1, 2) 100592 ++ (438888, 2) :: (1, 1) :: repeat (1, 2) 1511339 ++ (5653179, 2) :: (1, 1) :: repeat (1, 2) 11874956 ++ w) 1)).
  {
    apply (sTDN [40; 14; 5] 1138 ((12035, 2) :: (1, 1) :: repeat (1, 2) 23909 ++ (11951, 2) :: (1, 1) :: repeat (1, 2) 100592 ++ (438888, 2) :: (1, 1) :: repeat (1, 2) 1511339 ++ (5653179, 2) :: (1, 1) :: repeat (1, 2) 11874956 ++ w) 1).
  }
  (* step 210: sTUP *)
  apply (hsteps_trans _ (HC [40; 14; 5] 1138 3 2 ((12033, 2) :: (1, 1) :: repeat (1, 2) 23909 ++ (11951, 2) :: (1, 1) :: repeat (1, 2) 100592 ++ (438888, 2) :: (1, 1) :: repeat (1, 2) 1511339 ++ (5653179, 2) :: (1, 1) :: repeat (1, 2) 11874956 ++ w) 1)).
  {
    replace ((12033, 2) :: (1, 1) :: repeat (1, 2) 23909 ++ (11951, 2) :: (1, 1) :: repeat (1, 2) 100592 ++ (438888, 2) :: (1, 1) :: repeat (1, 2) 1511339 ++ (5653179, 2) :: (1, 1) :: repeat (1, 2) 11874956 ++ w) with ((12035 - 2, 2) :: (1, 1) :: repeat (1, 2) 23909 ++ (11951, 2) :: (1, 1) :: repeat (1, 2) 100592 ++ (438888, 2) :: (1, 1) :: repeat (1, 2) 1511339 ++ (5653179, 2) :: (1, 1) :: repeat (1, 2) 11874956 ++ w) by sec_eq.
    apply (sTUP [40; 14; 5] 1138 4 12035 2 ((1, 1) :: repeat (1, 2) 23909 ++ (11951, 2) :: (1, 1) :: repeat (1, 2) 100592 ++ (438888, 2) :: (1, 1) :: repeat (1, 2) 1511339 ++ (5653179, 2) :: (1, 1) :: repeat (1, 2) 11874956 ++ w) 1); closearith.
  }
  (* step 211: DIPGRIND 1138 9757 *)
  apply (hsteps_trans _ (HC [40; 14; 5] 0 3 2 (repeat (1, 2) 1138 ++ (9757, 2) :: (1, 1) :: repeat (1, 2) 23909 ++ (11951, 2) :: (1, 1) :: repeat (1, 2) 100592 ++ (438888, 2) :: (1, 1) :: repeat (1, 2) 1511339 ++ (5653179, 2) :: (1, 1) :: repeat (1, 2) 11874956 ++ w) 1)).
  {
    apply (DIPGRIND 1138 9757 [40; 14; 5] ((1, 1) :: repeat (1, 2) 23909 ++ (11951, 2) :: (1, 1) :: repeat (1, 2) 100592 ++ (438888, 2) :: (1, 1) :: repeat (1, 2) 1511339 ++ (5653179, 2) :: (1, 1) :: repeat (1, 2) 11874956 ++ w) 1); closearith.
  }
  (* step 212: P PX2A *)
  apply (hsteps_trans _ (HC [5] 13 38 2 ((1, 1) :: repeat (1, 2) 1140 ++ (9757, 2) :: (1, 1) :: repeat (1, 2) 23909 ++ (11951, 2) :: (1, 1) :: repeat (1, 2) 100592 ++ (438888, 2) :: (1, 1) :: repeat (1, 2) 1511339 ++ (5653179, 2) :: (1, 1) :: repeat (1, 2) 11874956 ++ w) 1)).
  {
    exact (hsteps_step _ _ _ (hPX2A 37 13 [5] (repeat (1, 2) 1138 ++ (9757, 2) :: (1, 1) :: repeat (1, 2) 23909 ++ (11951, 2) :: (1, 1) :: repeat (1, 2) 100592 ++ (438888, 2) :: (1, 1) :: repeat (1, 2) 1511339 ++ (5653179, 2) :: (1, 1) :: repeat (1, 2) 11874956 ++ w) 1) (hsteps_refl _)).
  }
  (* step 213: P PUSH *)
  apply (hsteps_trans _ (HC [5] 12 1 2 ((36, 2) :: (1, 1) :: repeat (1, 2) 1140 ++ (9757, 2) :: (1, 1) :: repeat (1, 2) 23909 ++ (11951, 2) :: (1, 1) :: repeat (1, 2) 100592 ++ (438888, 2) :: (1, 1) :: repeat (1, 2) 1511339 ++ (5653179, 2) :: (1, 1) :: repeat (1, 2) 11874956 ++ w) 1)).
  {
    replace ((36, 2) :: (1, 1) :: repeat (1, 2) 1140 ++ (9757, 2) :: (1, 1) :: repeat (1, 2) 23909 ++ (11951, 2) :: (1, 1) :: repeat (1, 2) 100592 ++ (438888, 2) :: (1, 1) :: repeat (1, 2) 1511339 ++ (5653179, 2) :: (1, 1) :: repeat (1, 2) 11874956 ++ w) with ((38 - 2, 2) :: (1, 1) :: repeat (1, 2) 1140 ++ (9757, 2) :: (1, 1) :: repeat (1, 2) 23909 ++ (11951, 2) :: (1, 1) :: repeat (1, 2) 100592 ++ (438888, 2) :: (1, 1) :: repeat (1, 2) 1511339 ++ (5653179, 2) :: (1, 1) :: repeat (1, 2) 11874956 ++ w) by sec_eq.
    apply (sPUSH [5] 12 38 ((1, 1) :: repeat (1, 2) 1140 ++ (9757, 2) :: (1, 1) :: repeat (1, 2) 23909 ++ (11951, 2) :: (1, 1) :: repeat (1, 2) 100592 ++ (438888, 2) :: (1, 1) :: repeat (1, 2) 1511339 ++ (5653179, 2) :: (1, 1) :: repeat (1, 2) 11874956 ++ w) 1); closearith.
  }
  (* step 214: P TDN *)
  apply (hsteps_trans _ (HB [5] 12 1 4 ((36, 2) :: (1, 1) :: repeat (1, 2) 1140 ++ (9757, 2) :: (1, 1) :: repeat (1, 2) 23909 ++ (11951, 2) :: (1, 1) :: repeat (1, 2) 100592 ++ (438888, 2) :: (1, 1) :: repeat (1, 2) 1511339 ++ (5653179, 2) :: (1, 1) :: repeat (1, 2) 11874956 ++ w) 1)).
  {
    apply (sTDN [5] 12 ((36, 2) :: (1, 1) :: repeat (1, 2) 1140 ++ (9757, 2) :: (1, 1) :: repeat (1, 2) 23909 ++ (11951, 2) :: (1, 1) :: repeat (1, 2) 100592 ++ (438888, 2) :: (1, 1) :: repeat (1, 2) 1511339 ++ (5653179, 2) :: (1, 1) :: repeat (1, 2) 11874956 ++ w) 1).
  }
  (* step 215: sTUP *)
  apply (hsteps_trans _ (HC [5] 12 3 2 ((34, 2) :: (1, 1) :: repeat (1, 2) 1140 ++ (9757, 2) :: (1, 1) :: repeat (1, 2) 23909 ++ (11951, 2) :: (1, 1) :: repeat (1, 2) 100592 ++ (438888, 2) :: (1, 1) :: repeat (1, 2) 1511339 ++ (5653179, 2) :: (1, 1) :: repeat (1, 2) 11874956 ++ w) 1)).
  {
    replace ((34, 2) :: (1, 1) :: repeat (1, 2) 1140 ++ (9757, 2) :: (1, 1) :: repeat (1, 2) 23909 ++ (11951, 2) :: (1, 1) :: repeat (1, 2) 100592 ++ (438888, 2) :: (1, 1) :: repeat (1, 2) 1511339 ++ (5653179, 2) :: (1, 1) :: repeat (1, 2) 11874956 ++ w) with ((36 - 2, 2) :: (1, 1) :: repeat (1, 2) 1140 ++ (9757, 2) :: (1, 1) :: repeat (1, 2) 23909 ++ (11951, 2) :: (1, 1) :: repeat (1, 2) 100592 ++ (438888, 2) :: (1, 1) :: repeat (1, 2) 1511339 ++ (5653179, 2) :: (1, 1) :: repeat (1, 2) 11874956 ++ w) by sec_eq.
    apply (sTUP [5] 12 4 36 2 ((1, 1) :: repeat (1, 2) 1140 ++ (9757, 2) :: (1, 1) :: repeat (1, 2) 23909 ++ (11951, 2) :: (1, 1) :: repeat (1, 2) 100592 ++ (438888, 2) :: (1, 1) :: repeat (1, 2) 1511339 ++ (5653179, 2) :: (1, 1) :: repeat (1, 2) 11874956 ++ w) 1); closearith.
  }
  (* step 216: DIPGRIND 12 10 *)
  apply (hsteps_trans _ (HC [5] 0 3 2 (repeat (1, 2) 12 ++ (10, 2) :: (1, 1) :: repeat (1, 2) 1140 ++ (9757, 2) :: (1, 1) :: repeat (1, 2) 23909 ++ (11951, 2) :: (1, 1) :: repeat (1, 2) 100592 ++ (438888, 2) :: (1, 1) :: repeat (1, 2) 1511339 ++ (5653179, 2) :: (1, 1) :: repeat (1, 2) 11874956 ++ w) 1)).
  {
    apply (DIPGRIND 12 10 [5] ((1, 1) :: repeat (1, 2) 1140 ++ (9757, 2) :: (1, 1) :: repeat (1, 2) 23909 ++ (11951, 2) :: (1, 1) :: repeat (1, 2) 100592 ++ (438888, 2) :: (1, 1) :: repeat (1, 2) 1511339 ++ (5653179, 2) :: (1, 1) :: repeat (1, 2) 11874956 ++ w) 1); closearith.
  }
  (* step 217: P PX2Bgen *)
  apply (hsteps_trans _ (HB [0] 3 1 2 (repeat (1, 2) 1 ++ (1, 1) :: repeat (1, 2) 14 ++ (10, 2) :: (1, 1) :: repeat (1, 2) 1140 ++ (9757, 2) :: (1, 1) :: repeat (1, 2) 23909 ++ (11951, 2) :: (1, 1) :: repeat (1, 2) 100592 ++ (438888, 2) :: (1, 1) :: repeat (1, 2) 1511339 ++ (5653179, 2) :: (1, 1) :: repeat (1, 2) 11874956 ++ w) 1)).
  {
    exact (hsteps_step _ _ _ (hPX2Bgen 0 (repeat (1, 2) 12 ++ (10, 2) :: (1, 1) :: repeat (1, 2) 1140 ++ (9757, 2) :: (1, 1) :: repeat (1, 2) 23909 ++ (11951, 2) :: (1, 1) :: repeat (1, 2) 100592 ++ (438888, 2) :: (1, 1) :: repeat (1, 2) 1511339 ++ (5653179, 2) :: (1, 1) :: repeat (1, 2) 11874956 ++ w) 1) (hsteps_refl _)).
  }
  (* step 218: M pop12 (1,) *)
  apply (hsteps_trans _ (HB [0] 4 1 4 ((1, 1) :: repeat (1, 2) 14 ++ (10, 2) :: (1, 1) :: repeat (1, 2) 1140 ++ (9757, 2) :: (1, 1) :: repeat (1, 2) 23909 ++ (11951, 2) :: (1, 1) :: repeat (1, 2) 100592 ++ (438888, 2) :: (1, 1) :: repeat (1, 2) 1511339 ++ (5653179, 2) :: (1, 1) :: repeat (1, 2) 11874956 ++ w) 1)).
  {
    apply (pop12 1 [0] 3 2 ((1, 1) :: repeat (1, 2) 14 ++ (10, 2) :: (1, 1) :: repeat (1, 2) 1140 ++ (9757, 2) :: (1, 1) :: repeat (1, 2) 23909 ++ (11951, 2) :: (1, 1) :: repeat (1, 2) 100592 ++ (438888, 2) :: (1, 1) :: repeat (1, 2) 1511339 ++ (5653179, 2) :: (1, 1) :: repeat (1, 2) 11874956 ++ w) 1); closearith.
  }
  (* step 219: P POP *)
  apply (hsteps_trans _ (HB [0] 5 1 5 (repeat (1, 2) 14 ++ (10, 2) :: (1, 1) :: repeat (1, 2) 1140 ++ (9757, 2) :: (1, 1) :: repeat (1, 2) 23909 ++ (11951, 2) :: (1, 1) :: repeat (1, 2) 100592 ++ (438888, 2) :: (1, 1) :: repeat (1, 2) 1511339 ++ (5653179, 2) :: (1, 1) :: repeat (1, 2) 11874956 ++ w) 1)).
  {
    apply (sPOP1 [0] 4 4 (repeat (1, 2) 14 ++ (10, 2) :: (1, 1) :: repeat (1, 2) 1140 ++ (9757, 2) :: (1, 1) :: repeat (1, 2) 23909 ++ (11951, 2) :: (1, 1) :: repeat (1, 2) 100592 ++ (438888, 2) :: (1, 1) :: repeat (1, 2) 1511339 ++ (5653179, 2) :: (1, 1) :: repeat (1, 2) 11874956 ++ w) 1); closearith.
  }
  (* step 220: M pop12 (14,) *)
  apply (hsteps_trans _ (HB [0] 19 1 33 ((10, 2) :: (1, 1) :: repeat (1, 2) 1140 ++ (9757, 2) :: (1, 1) :: repeat (1, 2) 23909 ++ (11951, 2) :: (1, 1) :: repeat (1, 2) 100592 ++ (438888, 2) :: (1, 1) :: repeat (1, 2) 1511339 ++ (5653179, 2) :: (1, 1) :: repeat (1, 2) 11874956 ++ w) 1)).
  {
    apply (pop12 14 [0] 5 5 ((10, 2) :: (1, 1) :: repeat (1, 2) 1140 ++ (9757, 2) :: (1, 1) :: repeat (1, 2) 23909 ++ (11951, 2) :: (1, 1) :: repeat (1, 2) 100592 ++ (438888, 2) :: (1, 1) :: repeat (1, 2) 1511339 ++ (5653179, 2) :: (1, 1) :: repeat (1, 2) 11874956 ++ w) 1); closearith.
  }
  (* step 221: sTUP *)
  apply (hsteps_trans _ (HC [0] 19 32 2 ((8, 2) :: (1, 1) :: repeat (1, 2) 1140 ++ (9757, 2) :: (1, 1) :: repeat (1, 2) 23909 ++ (11951, 2) :: (1, 1) :: repeat (1, 2) 100592 ++ (438888, 2) :: (1, 1) :: repeat (1, 2) 1511339 ++ (5653179, 2) :: (1, 1) :: repeat (1, 2) 11874956 ++ w) 1)).
  {
    replace ((8, 2) :: (1, 1) :: repeat (1, 2) 1140 ++ (9757, 2) :: (1, 1) :: repeat (1, 2) 23909 ++ (11951, 2) :: (1, 1) :: repeat (1, 2) 100592 ++ (438888, 2) :: (1, 1) :: repeat (1, 2) 1511339 ++ (5653179, 2) :: (1, 1) :: repeat (1, 2) 11874956 ++ w) with ((10 - 2, 2) :: (1, 1) :: repeat (1, 2) 1140 ++ (9757, 2) :: (1, 1) :: repeat (1, 2) 23909 ++ (11951, 2) :: (1, 1) :: repeat (1, 2) 100592 ++ (438888, 2) :: (1, 1) :: repeat (1, 2) 1511339 ++ (5653179, 2) :: (1, 1) :: repeat (1, 2) 11874956 ++ w) by sec_eq.
    apply (sTUP [0] 19 33 10 2 ((1, 1) :: repeat (1, 2) 1140 ++ (9757, 2) :: (1, 1) :: repeat (1, 2) 23909 ++ (11951, 2) :: (1, 1) :: repeat (1, 2) 100592 ++ (438888, 2) :: (1, 1) :: repeat (1, 2) 1511339 ++ (5653179, 2) :: (1, 1) :: repeat (1, 2) 11874956 ++ w) 1); closearith.
  }
  (* step 222: hGRIND_even 14 *)
  apply (hsteps_trans _ (HB [0] 18 1 32 ((2, 2) :: (8, 2) :: (1, 1) :: repeat (1, 2) 1140 ++ (9757, 2) :: (1, 1) :: repeat (1, 2) 23909 ++ (11951, 2) :: (1, 1) :: repeat (1, 2) 100592 ++ (438888, 2) :: (1, 1) :: repeat (1, 2) 1511339 ++ (5653179, 2) :: (1, 1) :: repeat (1, 2) 11874956 ++ w) 1)).
  {
    apply (hGRIND_even 14 [0] 18 ((8, 2) :: (1, 1) :: repeat (1, 2) 1140 ++ (9757, 2) :: (1, 1) :: repeat (1, 2) 23909 ++ (11951, 2) :: (1, 1) :: repeat (1, 2) 100592 ++ (438888, 2) :: (1, 1) :: repeat (1, 2) 1511339 ++ (5653179, 2) :: (1, 1) :: repeat (1, 2) 11874956 ++ w) 1); closearith.
  }
  (* step 223: P TUP2_1 *)
  apply (hsteps_trans _ (HC [19; 0] 32 1 2 ((6, 2) :: (1, 1) :: repeat (1, 2) 1140 ++ (9757, 2) :: (1, 1) :: repeat (1, 2) 23909 ++ (11951, 2) :: (1, 1) :: repeat (1, 2) 100592 ++ (438888, 2) :: (1, 1) :: repeat (1, 2) 1511339 ++ (5653179, 2) :: (1, 1) :: repeat (1, 2) 11874956 ++ w) 1)).
  {
    replace ((6, 2) :: (1, 1) :: repeat (1, 2) 1140 ++ (9757, 2) :: (1, 1) :: repeat (1, 2) 23909 ++ (11951, 2) :: (1, 1) :: repeat (1, 2) 100592 ++ (438888, 2) :: (1, 1) :: repeat (1, 2) 1511339 ++ (5653179, 2) :: (1, 1) :: repeat (1, 2) 11874956 ++ w) with ((8 - 2, 2) :: (1, 1) :: repeat (1, 2) 1140 ++ (9757, 2) :: (1, 1) :: repeat (1, 2) 23909 ++ (11951, 2) :: (1, 1) :: repeat (1, 2) 100592 ++ (438888, 2) :: (1, 1) :: repeat (1, 2) 1511339 ++ (5653179, 2) :: (1, 1) :: repeat (1, 2) 11874956 ++ w) by sec_eq.
    apply (sTUP2_1 [0] 18 31 8 ((1, 1) :: repeat (1, 2) 1140 ++ (9757, 2) :: (1, 1) :: repeat (1, 2) 23909 ++ (11951, 2) :: (1, 1) :: repeat (1, 2) 100592 ++ (438888, 2) :: (1, 1) :: repeat (1, 2) 1511339 ++ (5653179, 2) :: (1, 1) :: repeat (1, 2) 11874956 ++ w) 1); closearith.
  }
  (* step 224: P TDN *)
  apply (sTDN [19; 0] 32 ((6, 2) :: (1, 1) :: repeat (1, 2) 1140 ++ (9757, 2) :: (1, 1) :: repeat (1, 2) 23909 ++ (11951, 2) :: (1, 1) :: repeat (1, 2) 100592 ++ (438888, 2) :: (1, 1) :: repeat (1, 2) 1511339 ++ (5653179, 2) :: (1, 1) :: repeat (1, 2) 11874956 ++ w) 1).
Qed.

(* CASCADE58e: steps 225-280 of the CASCADE58 chain. *)
Lemma CASCADE58e : forall w,
  hsteps (HB [19; 0] 32 1 4 ((6, 2) :: (1, 1) :: repeat (1, 2) 1140 ++ (9757, 2) :: (1, 1) :: repeat (1, 2) 23909 ++ (11951, 2) :: (1, 1) :: repeat (1, 2) 100592 ++ (438888, 2) :: (1, 1) :: repeat (1, 2) 1511339 ++ (5653179, 2) :: (1, 1) :: repeat (1, 2) 11874956 ++ w) 1)
         (HB [5] 13 1 4 ((32, 2) :: (1, 1) :: repeat (1, 2) 74 ++ (931, 2) :: (1, 1) :: repeat (1, 2) 2284 ++ (5187, 2) :: (1, 1) :: repeat (1, 2) 23909 ++ (11951, 2) :: (1, 1) :: repeat (1, 2) 100592 ++ (438888, 2) :: (1, 1) :: repeat (1, 2) 1511339 ++ (5653179, 2) :: (1, 1) :: repeat (1, 2) 11874956 ++ w) 1).
Proof.
  intro w.
  (* step 225: sTUP *)
  apply (hsteps_trans _ (HC [19; 0] 32 3 2 ((4, 2) :: (1, 1) :: repeat (1, 2) 1140 ++ (9757, 2) :: (1, 1) :: repeat (1, 2) 23909 ++ (11951, 2) :: (1, 1) :: repeat (1, 2) 100592 ++ (438888, 2) :: (1, 1) :: repeat (1, 2) 1511339 ++ (5653179, 2) :: (1, 1) :: repeat (1, 2) 11874956 ++ w) 1)).
  {
    replace ((4, 2) :: (1, 1) :: repeat (1, 2) 1140 ++ (9757, 2) :: (1, 1) :: repeat (1, 2) 23909 ++ (11951, 2) :: (1, 1) :: repeat (1, 2) 100592 ++ (438888, 2) :: (1, 1) :: repeat (1, 2) 1511339 ++ (5653179, 2) :: (1, 1) :: repeat (1, 2) 11874956 ++ w) with ((6 - 2, 2) :: (1, 1) :: repeat (1, 2) 1140 ++ (9757, 2) :: (1, 1) :: repeat (1, 2) 23909 ++ (11951, 2) :: (1, 1) :: repeat (1, 2) 100592 ++ (438888, 2) :: (1, 1) :: repeat (1, 2) 1511339 ++ (5653179, 2) :: (1, 1) :: repeat (1, 2) 11874956 ++ w) by sec_eq.
    apply (sTUP [19; 0] 32 4 6 2 ((1, 1) :: repeat (1, 2) 1140 ++ (9757, 2) :: (1, 1) :: repeat (1, 2) 23909 ++ (11951, 2) :: (1, 1) :: repeat (1, 2) 100592 ++ (438888, 2) :: (1, 1) :: repeat (1, 2) 1511339 ++ (5653179, 2) :: (1, 1) :: repeat (1, 2) 11874956 ++ w) 1); closearith.
  }
  (* step 226: CLEANG_even 1 *)
  apply (hsteps_trans _ (HB [19; 0] 32 1 8 ((2, 2) :: (1, 1) :: repeat (1, 2) 1140 ++ (9757, 2) :: (1, 1) :: repeat (1, 2) 23909 ++ (11951, 2) :: (1, 1) :: repeat (1, 2) 100592 ++ (438888, 2) :: (1, 1) :: repeat (1, 2) 1511339 ++ (5653179, 2) :: (1, 1) :: repeat (1, 2) 11874956 ++ w) 1)).
  {
    apply (CLEANG_even 1 [19; 0] 32 ((1, 1) :: repeat (1, 2) 1140 ++ (9757, 2) :: (1, 1) :: repeat (1, 2) 23909 ++ (11951, 2) :: (1, 1) :: repeat (1, 2) 100592 ++ (438888, 2) :: (1, 1) :: repeat (1, 2) 1511339 ++ (5653179, 2) :: (1, 1) :: repeat (1, 2) 11874956 ++ w) 1); closearith.
  }
  (* step 227: P TRANS2_1 *)
  apply (hsteps_trans _ (HB [33; 19; 0] 9 1 3 (repeat (1, 2) 1140 ++ (9757, 2) :: (1, 1) :: repeat (1, 2) 23909 ++ (11951, 2) :: (1, 1) :: repeat (1, 2) 100592 ++ (438888, 2) :: (1, 1) :: repeat (1, 2) 1511339 ++ (5653179, 2) :: (1, 1) :: repeat (1, 2) 11874956 ++ w) 1)).
  {
    apply (sTRANS2_1 [19; 0] 32 7 1 (repeat (1, 2) 1140 ++ (9757, 2) :: (1, 1) :: repeat (1, 2) 23909 ++ (11951, 2) :: (1, 1) :: repeat (1, 2) 100592 ++ (438888, 2) :: (1, 1) :: repeat (1, 2) 1511339 ++ (5653179, 2) :: (1, 1) :: repeat (1, 2) 11874956 ++ w) 1); closearith.
  }
  (* step 228: M pop12 (1140,) *)
  apply (hsteps_trans _ (HB [33; 19; 0] 1149 1 2283 ((9757, 2) :: (1, 1) :: repeat (1, 2) 23909 ++ (11951, 2) :: (1, 1) :: repeat (1, 2) 100592 ++ (438888, 2) :: (1, 1) :: repeat (1, 2) 1511339 ++ (5653179, 2) :: (1, 1) :: repeat (1, 2) 11874956 ++ w) 1)).
  {
    apply (pop12 1140 [33; 19; 0] 9 3 ((9757, 2) :: (1, 1) :: repeat (1, 2) 23909 ++ (11951, 2) :: (1, 1) :: repeat (1, 2) 100592 ++ (438888, 2) :: (1, 1) :: repeat (1, 2) 1511339 ++ (5653179, 2) :: (1, 1) :: repeat (1, 2) 11874956 ++ w) 1); closearith.
  }
  (* step 229: sTUP *)
  apply (hsteps_trans _ (HC [33; 19; 0] 1149 2282 2 ((9755, 2) :: (1, 1) :: repeat (1, 2) 23909 ++ (11951, 2) :: (1, 1) :: repeat (1, 2) 100592 ++ (438888, 2) :: (1, 1) :: repeat (1, 2) 1511339 ++ (5653179, 2) :: (1, 1) :: repeat (1, 2) 11874956 ++ w) 1)).
  {
    replace ((9755, 2) :: (1, 1) :: repeat (1, 2) 23909 ++ (11951, 2) :: (1, 1) :: repeat (1, 2) 100592 ++ (438888, 2) :: (1, 1) :: repeat (1, 2) 1511339 ++ (5653179, 2) :: (1, 1) :: repeat (1, 2) 11874956 ++ w) with ((9757 - 2, 2) :: (1, 1) :: repeat (1, 2) 23909 ++ (11951, 2) :: (1, 1) :: repeat (1, 2) 100592 ++ (438888, 2) :: (1, 1) :: repeat (1, 2) 1511339 ++ (5653179, 2) :: (1, 1) :: repeat (1, 2) 11874956 ++ w) by sec_eq.
    apply (sTUP [33; 19; 0] 1149 2283 9757 2 ((1, 1) :: repeat (1, 2) 23909 ++ (11951, 2) :: (1, 1) :: repeat (1, 2) 100592 ++ (438888, 2) :: (1, 1) :: repeat (1, 2) 1511339 ++ (5653179, 2) :: (1, 1) :: repeat (1, 2) 11874956 ++ w) 1); closearith.
  }
  (* step 230: hGRIND_even 1139 *)
  apply (hsteps_trans _ (HB [33; 19; 0] 1148 1 2282 ((2, 2) :: (9755, 2) :: (1, 1) :: repeat (1, 2) 23909 ++ (11951, 2) :: (1, 1) :: repeat (1, 2) 100592 ++ (438888, 2) :: (1, 1) :: repeat (1, 2) 1511339 ++ (5653179, 2) :: (1, 1) :: repeat (1, 2) 11874956 ++ w) 1)).
  {
    apply (hGRIND_even 1139 [33; 19; 0] 1148 ((9755, 2) :: (1, 1) :: repeat (1, 2) 23909 ++ (11951, 2) :: (1, 1) :: repeat (1, 2) 100592 ++ (438888, 2) :: (1, 1) :: repeat (1, 2) 1511339 ++ (5653179, 2) :: (1, 1) :: repeat (1, 2) 11874956 ++ w) 1); closearith.
  }
  (* step 231: P TUP2_1 *)
  apply (hsteps_trans _ (HC [1149; 33; 19; 0] 2282 1 2 ((9753, 2) :: (1, 1) :: repeat (1, 2) 23909 ++ (11951, 2) :: (1, 1) :: repeat (1, 2) 100592 ++ (438888, 2) :: (1, 1) :: repeat (1, 2) 1511339 ++ (5653179, 2) :: (1, 1) :: repeat (1, 2) 11874956 ++ w) 1)).
  {
    replace ((9753, 2) :: (1, 1) :: repeat (1, 2) 23909 ++ (11951, 2) :: (1, 1) :: repeat (1, 2) 100592 ++ (438888, 2) :: (1, 1) :: repeat (1, 2) 1511339 ++ (5653179, 2) :: (1, 1) :: repeat (1, 2) 11874956 ++ w) with ((9755 - 2, 2) :: (1, 1) :: repeat (1, 2) 23909 ++ (11951, 2) :: (1, 1) :: repeat (1, 2) 100592 ++ (438888, 2) :: (1, 1) :: repeat (1, 2) 1511339 ++ (5653179, 2) :: (1, 1) :: repeat (1, 2) 11874956 ++ w) by sec_eq.
    apply (sTUP2_1 [33; 19; 0] 1148 2281 9755 ((1, 1) :: repeat (1, 2) 23909 ++ (11951, 2) :: (1, 1) :: repeat (1, 2) 100592 ++ (438888, 2) :: (1, 1) :: repeat (1, 2) 1511339 ++ (5653179, 2) :: (1, 1) :: repeat (1, 2) 11874956 ++ w) 1); closearith.
  }
  (* step 232: P TDN *)
  apply (hsteps_trans _ (HB [1149; 33; 19; 0] 2282 1 4 ((9753, 2) :: (1, 1) :: repeat (1, 2) 23909 ++ (11951, 2) :: (1, 1) :: repeat (1, 2) 100592 ++ (438888, 2) :: (1, 1) :: repeat (1, 2) 1511339 ++ (5653179, 2) :: (1, 1) :: repeat (1, 2) 11874956 ++ w) 1)).
  {
    apply (sTDN [1149; 33; 19; 0] 2282 ((9753, 2) :: (1, 1) :: repeat (1, 2) 23909 ++ (11951, 2) :: (1, 1) :: repeat (1, 2) 100592 ++ (438888, 2) :: (1, 1) :: repeat (1, 2) 1511339 ++ (5653179, 2) :: (1, 1) :: repeat (1, 2) 11874956 ++ w) 1).
  }
  (* step 233: sTUP *)
  apply (hsteps_trans _ (HC [1149; 33; 19; 0] 2282 3 2 ((9751, 2) :: (1, 1) :: repeat (1, 2) 23909 ++ (11951, 2) :: (1, 1) :: repeat (1, 2) 100592 ++ (438888, 2) :: (1, 1) :: repeat (1, 2) 1511339 ++ (5653179, 2) :: (1, 1) :: repeat (1, 2) 11874956 ++ w) 1)).
  {
    replace ((9751, 2) :: (1, 1) :: repeat (1, 2) 23909 ++ (11951, 2) :: (1, 1) :: repeat (1, 2) 100592 ++ (438888, 2) :: (1, 1) :: repeat (1, 2) 1511339 ++ (5653179, 2) :: (1, 1) :: repeat (1, 2) 11874956 ++ w) with ((9753 - 2, 2) :: (1, 1) :: repeat (1, 2) 23909 ++ (11951, 2) :: (1, 1) :: repeat (1, 2) 100592 ++ (438888, 2) :: (1, 1) :: repeat (1, 2) 1511339 ++ (5653179, 2) :: (1, 1) :: repeat (1, 2) 11874956 ++ w) by sec_eq.
    apply (sTUP [1149; 33; 19; 0] 2282 4 9753 2 ((1, 1) :: repeat (1, 2) 23909 ++ (11951, 2) :: (1, 1) :: repeat (1, 2) 100592 ++ (438888, 2) :: (1, 1) :: repeat (1, 2) 1511339 ++ (5653179, 2) :: (1, 1) :: repeat (1, 2) 11874956 ++ w) 1); closearith.
  }
  (* step 234: DIPGRIND 2282 5187 *)
  apply (hsteps_trans _ (HC [1149; 33; 19; 0] 0 3 2 (repeat (1, 2) 2282 ++ (5187, 2) :: (1, 1) :: repeat (1, 2) 23909 ++ (11951, 2) :: (1, 1) :: repeat (1, 2) 100592 ++ (438888, 2) :: (1, 1) :: repeat (1, 2) 1511339 ++ (5653179, 2) :: (1, 1) :: repeat (1, 2) 11874956 ++ w) 1)).
  {
    apply (DIPGRIND 2282 5187 [1149; 33; 19; 0] ((1, 1) :: repeat (1, 2) 23909 ++ (11951, 2) :: (1, 1) :: repeat (1, 2) 100592 ++ (438888, 2) :: (1, 1) :: repeat (1, 2) 1511339 ++ (5653179, 2) :: (1, 1) :: repeat (1, 2) 11874956 ++ w) 1); closearith.
  }
  (* step 235: P PX2A *)
  apply (hsteps_trans _ (HC [19; 0] 32 1147 2 ((1, 1) :: repeat (1, 2) 2284 ++ (5187, 2) :: (1, 1) :: repeat (1, 2) 23909 ++ (11951, 2) :: (1, 1) :: repeat (1, 2) 100592 ++ (438888, 2) :: (1, 1) :: repeat (1, 2) 1511339 ++ (5653179, 2) :: (1, 1) :: repeat (1, 2) 11874956 ++ w) 1)).
  {
    exact (hsteps_step _ _ _ (hPX2A 1146 32 [19; 0] (repeat (1, 2) 2282 ++ (5187, 2) :: (1, 1) :: repeat (1, 2) 23909 ++ (11951, 2) :: (1, 1) :: repeat (1, 2) 100592 ++ (438888, 2) :: (1, 1) :: repeat (1, 2) 1511339 ++ (5653179, 2) :: (1, 1) :: repeat (1, 2) 11874956 ++ w) 1) (hsteps_refl _)).
  }
  (* step 236: P PUSH *)
  apply (hsteps_trans _ (HC [19; 0] 31 1 2 ((1145, 2) :: (1, 1) :: repeat (1, 2) 2284 ++ (5187, 2) :: (1, 1) :: repeat (1, 2) 23909 ++ (11951, 2) :: (1, 1) :: repeat (1, 2) 100592 ++ (438888, 2) :: (1, 1) :: repeat (1, 2) 1511339 ++ (5653179, 2) :: (1, 1) :: repeat (1, 2) 11874956 ++ w) 1)).
  {
    replace ((1145, 2) :: (1, 1) :: repeat (1, 2) 2284 ++ (5187, 2) :: (1, 1) :: repeat (1, 2) 23909 ++ (11951, 2) :: (1, 1) :: repeat (1, 2) 100592 ++ (438888, 2) :: (1, 1) :: repeat (1, 2) 1511339 ++ (5653179, 2) :: (1, 1) :: repeat (1, 2) 11874956 ++ w) with ((1147 - 2, 2) :: (1, 1) :: repeat (1, 2) 2284 ++ (5187, 2) :: (1, 1) :: repeat (1, 2) 23909 ++ (11951, 2) :: (1, 1) :: repeat (1, 2) 100592 ++ (438888, 2) :: (1, 1) :: repeat (1, 2) 1511339 ++ (5653179, 2) :: (1, 1) :: repeat (1, 2) 11874956 ++ w) by sec_eq.
    apply (sPUSH [19; 0] 31 1147 ((1, 1) :: repeat (1, 2) 2284 ++ (5187, 2) :: (1, 1) :: repeat (1, 2) 23909 ++ (11951, 2) :: (1, 1) :: repeat (1, 2) 100592 ++ (438888, 2) :: (1, 1) :: repeat (1, 2) 1511339 ++ (5653179, 2) :: (1, 1) :: repeat (1, 2) 11874956 ++ w) 1); closearith.
  }
  (* step 237: P TDN *)
  apply (hsteps_trans _ (HB [19; 0] 31 1 4 ((1145, 2) :: (1, 1) :: repeat (1, 2) 2284 ++ (5187, 2) :: (1, 1) :: repeat (1, 2) 23909 ++ (11951, 2) :: (1, 1) :: repeat (1, 2) 100592 ++ (438888, 2) :: (1, 1) :: repeat (1, 2) 1511339 ++ (5653179, 2) :: (1, 1) :: repeat (1, 2) 11874956 ++ w) 1)).
  {
    apply (sTDN [19; 0] 31 ((1145, 2) :: (1, 1) :: repeat (1, 2) 2284 ++ (5187, 2) :: (1, 1) :: repeat (1, 2) 23909 ++ (11951, 2) :: (1, 1) :: repeat (1, 2) 100592 ++ (438888, 2) :: (1, 1) :: repeat (1, 2) 1511339 ++ (5653179, 2) :: (1, 1) :: repeat (1, 2) 11874956 ++ w) 1).
  }
  (* step 238: sTUP *)
  apply (hsteps_trans _ (HC [19; 0] 31 3 2 ((1143, 2) :: (1, 1) :: repeat (1, 2) 2284 ++ (5187, 2) :: (1, 1) :: repeat (1, 2) 23909 ++ (11951, 2) :: (1, 1) :: repeat (1, 2) 100592 ++ (438888, 2) :: (1, 1) :: repeat (1, 2) 1511339 ++ (5653179, 2) :: (1, 1) :: repeat (1, 2) 11874956 ++ w) 1)).
  {
    replace ((1143, 2) :: (1, 1) :: repeat (1, 2) 2284 ++ (5187, 2) :: (1, 1) :: repeat (1, 2) 23909 ++ (11951, 2) :: (1, 1) :: repeat (1, 2) 100592 ++ (438888, 2) :: (1, 1) :: repeat (1, 2) 1511339 ++ (5653179, 2) :: (1, 1) :: repeat (1, 2) 11874956 ++ w) with ((1145 - 2, 2) :: (1, 1) :: repeat (1, 2) 2284 ++ (5187, 2) :: (1, 1) :: repeat (1, 2) 23909 ++ (11951, 2) :: (1, 1) :: repeat (1, 2) 100592 ++ (438888, 2) :: (1, 1) :: repeat (1, 2) 1511339 ++ (5653179, 2) :: (1, 1) :: repeat (1, 2) 11874956 ++ w) by sec_eq.
    apply (sTUP [19; 0] 31 4 1145 2 ((1, 1) :: repeat (1, 2) 2284 ++ (5187, 2) :: (1, 1) :: repeat (1, 2) 23909 ++ (11951, 2) :: (1, 1) :: repeat (1, 2) 100592 ++ (438888, 2) :: (1, 1) :: repeat (1, 2) 1511339 ++ (5653179, 2) :: (1, 1) :: repeat (1, 2) 11874956 ++ w) 1); closearith.
  }
  (* step 239: DIPGRIND 31 1081 *)
  apply (hsteps_trans _ (HC [19; 0] 0 3 2 (repeat (1, 2) 31 ++ (1081, 2) :: (1, 1) :: repeat (1, 2) 2284 ++ (5187, 2) :: (1, 1) :: repeat (1, 2) 23909 ++ (11951, 2) :: (1, 1) :: repeat (1, 2) 100592 ++ (438888, 2) :: (1, 1) :: repeat (1, 2) 1511339 ++ (5653179, 2) :: (1, 1) :: repeat (1, 2) 11874956 ++ w) 1)).
  {
    apply (DIPGRIND 31 1081 [19; 0] ((1, 1) :: repeat (1, 2) 2284 ++ (5187, 2) :: (1, 1) :: repeat (1, 2) 23909 ++ (11951, 2) :: (1, 1) :: repeat (1, 2) 100592 ++ (438888, 2) :: (1, 1) :: repeat (1, 2) 1511339 ++ (5653179, 2) :: (1, 1) :: repeat (1, 2) 11874956 ++ w) 1); closearith.
  }
  (* step 240: P PX2A0 *)
  apply (hsteps_trans _ (HB [0] 3 1 2 ((15, 2) :: (1, 1) :: repeat (1, 2) 33 ++ (1081, 2) :: (1, 1) :: repeat (1, 2) 2284 ++ (5187, 2) :: (1, 1) :: repeat (1, 2) 23909 ++ (11951, 2) :: (1, 1) :: repeat (1, 2) 100592 ++ (438888, 2) :: (1, 1) :: repeat (1, 2) 1511339 ++ (5653179, 2) :: (1, 1) :: repeat (1, 2) 11874956 ++ w) 1)).
  {
    exact (hsteps_step _ _ _ (hPX2A0 14 (repeat (1, 2) 31 ++ (1081, 2) :: (1, 1) :: repeat (1, 2) 2284 ++ (5187, 2) :: (1, 1) :: repeat (1, 2) 23909 ++ (11951, 2) :: (1, 1) :: repeat (1, 2) 100592 ++ (438888, 2) :: (1, 1) :: repeat (1, 2) 1511339 ++ (5653179, 2) :: (1, 1) :: repeat (1, 2) 11874956 ++ w) 1) (hsteps_refl _)).
  }
  (* step 241: sTUP *)
  apply (hsteps_trans _ (HC [0] 3 1 2 ((13, 2) :: (1, 1) :: repeat (1, 2) 33 ++ (1081, 2) :: (1, 1) :: repeat (1, 2) 2284 ++ (5187, 2) :: (1, 1) :: repeat (1, 2) 23909 ++ (11951, 2) :: (1, 1) :: repeat (1, 2) 100592 ++ (438888, 2) :: (1, 1) :: repeat (1, 2) 1511339 ++ (5653179, 2) :: (1, 1) :: repeat (1, 2) 11874956 ++ w) 1)).
  {
    replace ((13, 2) :: (1, 1) :: repeat (1, 2) 33 ++ (1081, 2) :: (1, 1) :: repeat (1, 2) 2284 ++ (5187, 2) :: (1, 1) :: repeat (1, 2) 23909 ++ (11951, 2) :: (1, 1) :: repeat (1, 2) 100592 ++ (438888, 2) :: (1, 1) :: repeat (1, 2) 1511339 ++ (5653179, 2) :: (1, 1) :: repeat (1, 2) 11874956 ++ w) with ((15 - 2, 2) :: (1, 1) :: repeat (1, 2) 33 ++ (1081, 2) :: (1, 1) :: repeat (1, 2) 2284 ++ (5187, 2) :: (1, 1) :: repeat (1, 2) 23909 ++ (11951, 2) :: (1, 1) :: repeat (1, 2) 100592 ++ (438888, 2) :: (1, 1) :: repeat (1, 2) 1511339 ++ (5653179, 2) :: (1, 1) :: repeat (1, 2) 11874956 ++ w) by sec_eq.
    apply (sTUP [0] 3 2 15 2 ((1, 1) :: repeat (1, 2) 33 ++ (1081, 2) :: (1, 1) :: repeat (1, 2) 2284 ++ (5187, 2) :: (1, 1) :: repeat (1, 2) 23909 ++ (11951, 2) :: (1, 1) :: repeat (1, 2) 100592 ++ (438888, 2) :: (1, 1) :: repeat (1, 2) 1511339 ++ (5653179, 2) :: (1, 1) :: repeat (1, 2) 11874956 ++ w) 1); closearith.
  }
  (* step 242: P TDN *)
  apply (hsteps_trans _ (HB [0] 3 1 4 ((13, 2) :: (1, 1) :: repeat (1, 2) 33 ++ (1081, 2) :: (1, 1) :: repeat (1, 2) 2284 ++ (5187, 2) :: (1, 1) :: repeat (1, 2) 23909 ++ (11951, 2) :: (1, 1) :: repeat (1, 2) 100592 ++ (438888, 2) :: (1, 1) :: repeat (1, 2) 1511339 ++ (5653179, 2) :: (1, 1) :: repeat (1, 2) 11874956 ++ w) 1)).
  {
    apply (sTDN [0] 3 ((13, 2) :: (1, 1) :: repeat (1, 2) 33 ++ (1081, 2) :: (1, 1) :: repeat (1, 2) 2284 ++ (5187, 2) :: (1, 1) :: repeat (1, 2) 23909 ++ (11951, 2) :: (1, 1) :: repeat (1, 2) 100592 ++ (438888, 2) :: (1, 1) :: repeat (1, 2) 1511339 ++ (5653179, 2) :: (1, 1) :: repeat (1, 2) 11874956 ++ w) 1).
  }
  (* step 243: sTUP *)
  apply (hsteps_trans _ (HC [0] 3 3 2 ((11, 2) :: (1, 1) :: repeat (1, 2) 33 ++ (1081, 2) :: (1, 1) :: repeat (1, 2) 2284 ++ (5187, 2) :: (1, 1) :: repeat (1, 2) 23909 ++ (11951, 2) :: (1, 1) :: repeat (1, 2) 100592 ++ (438888, 2) :: (1, 1) :: repeat (1, 2) 1511339 ++ (5653179, 2) :: (1, 1) :: repeat (1, 2) 11874956 ++ w) 1)).
  {
    replace ((11, 2) :: (1, 1) :: repeat (1, 2) 33 ++ (1081, 2) :: (1, 1) :: repeat (1, 2) 2284 ++ (5187, 2) :: (1, 1) :: repeat (1, 2) 23909 ++ (11951, 2) :: (1, 1) :: repeat (1, 2) 100592 ++ (438888, 2) :: (1, 1) :: repeat (1, 2) 1511339 ++ (5653179, 2) :: (1, 1) :: repeat (1, 2) 11874956 ++ w) with ((13 - 2, 2) :: (1, 1) :: repeat (1, 2) 33 ++ (1081, 2) :: (1, 1) :: repeat (1, 2) 2284 ++ (5187, 2) :: (1, 1) :: repeat (1, 2) 23909 ++ (11951, 2) :: (1, 1) :: repeat (1, 2) 100592 ++ (438888, 2) :: (1, 1) :: repeat (1, 2) 1511339 ++ (5653179, 2) :: (1, 1) :: repeat (1, 2) 11874956 ++ w) by sec_eq.
    apply (sTUP [0] 3 4 13 2 ((1, 1) :: repeat (1, 2) 33 ++ (1081, 2) :: (1, 1) :: repeat (1, 2) 2284 ++ (5187, 2) :: (1, 1) :: repeat (1, 2) 23909 ++ (11951, 2) :: (1, 1) :: repeat (1, 2) 100592 ++ (438888, 2) :: (1, 1) :: repeat (1, 2) 1511339 ++ (5653179, 2) :: (1, 1) :: repeat (1, 2) 11874956 ++ w) 1); closearith.
  }
  (* step 244: DIPGRIND 3 5 *)
  apply (hsteps_trans _ (HC [0] 0 3 2 (repeat (1, 2) 3 ++ (5, 2) :: (1, 1) :: repeat (1, 2) 33 ++ (1081, 2) :: (1, 1) :: repeat (1, 2) 2284 ++ (5187, 2) :: (1, 1) :: repeat (1, 2) 23909 ++ (11951, 2) :: (1, 1) :: repeat (1, 2) 100592 ++ (438888, 2) :: (1, 1) :: repeat (1, 2) 1511339 ++ (5653179, 2) :: (1, 1) :: repeat (1, 2) 11874956 ++ w) 1)).
  {
    apply (DIPGRIND 3 5 [0] ((1, 1) :: repeat (1, 2) 33 ++ (1081, 2) :: (1, 1) :: repeat (1, 2) 2284 ++ (5187, 2) :: (1, 1) :: repeat (1, 2) 23909 ++ (11951, 2) :: (1, 1) :: repeat (1, 2) 100592 ++ (438888, 2) :: (1, 1) :: repeat (1, 2) 1511339 ++ (5653179, 2) :: (1, 1) :: repeat (1, 2) 11874956 ++ w) 1); closearith.
  }
  (* step 245: P PX2B0 *)
  apply (hsteps_trans _ (HB [] 0 1 5 (repeat (1, 2) 4 ++ (5, 2) :: (1, 1) :: repeat (1, 2) 33 ++ (1081, 2) :: (1, 1) :: repeat (1, 2) 2284 ++ (5187, 2) :: (1, 1) :: repeat (1, 2) 23909 ++ (11951, 2) :: (1, 1) :: repeat (1, 2) 100592 ++ (438888, 2) :: (1, 1) :: repeat (1, 2) 1511339 ++ (5653179, 2) :: (1, 1) :: repeat (1, 2) 11874956 ++ w) 1)).
  {
    exact (hsteps_step _ _ _ (hPX2B0 (repeat (1, 2) 3 ++ (5, 2) :: (1, 1) :: repeat (1, 2) 33 ++ (1081, 2) :: (1, 1) :: repeat (1, 2) 2284 ++ (5187, 2) :: (1, 1) :: repeat (1, 2) 23909 ++ (11951, 2) :: (1, 1) :: repeat (1, 2) 100592 ++ (438888, 2) :: (1, 1) :: repeat (1, 2) 1511339 ++ (5653179, 2) :: (1, 1) :: repeat (1, 2) 11874956 ++ w) 1) (hsteps_refl _)).
  }
  (* step 246: M pop12 (4,) *)
  apply (hsteps_trans _ (HB [] 4 1 13 ((5, 2) :: (1, 1) :: repeat (1, 2) 33 ++ (1081, 2) :: (1, 1) :: repeat (1, 2) 2284 ++ (5187, 2) :: (1, 1) :: repeat (1, 2) 23909 ++ (11951, 2) :: (1, 1) :: repeat (1, 2) 100592 ++ (438888, 2) :: (1, 1) :: repeat (1, 2) 1511339 ++ (5653179, 2) :: (1, 1) :: repeat (1, 2) 11874956 ++ w) 1)).
  {
    apply (pop12 4 [] 0 5 ((5, 2) :: (1, 1) :: repeat (1, 2) 33 ++ (1081, 2) :: (1, 1) :: repeat (1, 2) 2284 ++ (5187, 2) :: (1, 1) :: repeat (1, 2) 23909 ++ (11951, 2) :: (1, 1) :: repeat (1, 2) 100592 ++ (438888, 2) :: (1, 1) :: repeat (1, 2) 1511339 ++ (5653179, 2) :: (1, 1) :: repeat (1, 2) 11874956 ++ w) 1); closearith.
  }
  (* step 247: sTUP *)
  apply (hsteps_trans _ (HC [] 4 12 2 ((3, 2) :: (1, 1) :: repeat (1, 2) 33 ++ (1081, 2) :: (1, 1) :: repeat (1, 2) 2284 ++ (5187, 2) :: (1, 1) :: repeat (1, 2) 23909 ++ (11951, 2) :: (1, 1) :: repeat (1, 2) 100592 ++ (438888, 2) :: (1, 1) :: repeat (1, 2) 1511339 ++ (5653179, 2) :: (1, 1) :: repeat (1, 2) 11874956 ++ w) 1)).
  {
    replace ((3, 2) :: (1, 1) :: repeat (1, 2) 33 ++ (1081, 2) :: (1, 1) :: repeat (1, 2) 2284 ++ (5187, 2) :: (1, 1) :: repeat (1, 2) 23909 ++ (11951, 2) :: (1, 1) :: repeat (1, 2) 100592 ++ (438888, 2) :: (1, 1) :: repeat (1, 2) 1511339 ++ (5653179, 2) :: (1, 1) :: repeat (1, 2) 11874956 ++ w) with ((5 - 2, 2) :: (1, 1) :: repeat (1, 2) 33 ++ (1081, 2) :: (1, 1) :: repeat (1, 2) 2284 ++ (5187, 2) :: (1, 1) :: repeat (1, 2) 23909 ++ (11951, 2) :: (1, 1) :: repeat (1, 2) 100592 ++ (438888, 2) :: (1, 1) :: repeat (1, 2) 1511339 ++ (5653179, 2) :: (1, 1) :: repeat (1, 2) 11874956 ++ w) by sec_eq.
    apply (sTUP [] 4 13 5 2 ((1, 1) :: repeat (1, 2) 33 ++ (1081, 2) :: (1, 1) :: repeat (1, 2) 2284 ++ (5187, 2) :: (1, 1) :: repeat (1, 2) 23909 ++ (11951, 2) :: (1, 1) :: repeat (1, 2) 100592 ++ (438888, 2) :: (1, 1) :: repeat (1, 2) 1511339 ++ (5653179, 2) :: (1, 1) :: repeat (1, 2) 11874956 ++ w) 1); closearith.
  }
  (* step 248: P PUSH *)
  apply (hsteps_trans _ (HC [] 3 1 2 ((10, 2) :: (3, 2) :: (1, 1) :: repeat (1, 2) 33 ++ (1081, 2) :: (1, 1) :: repeat (1, 2) 2284 ++ (5187, 2) :: (1, 1) :: repeat (1, 2) 23909 ++ (11951, 2) :: (1, 1) :: repeat (1, 2) 100592 ++ (438888, 2) :: (1, 1) :: repeat (1, 2) 1511339 ++ (5653179, 2) :: (1, 1) :: repeat (1, 2) 11874956 ++ w) 1)).
  {
    replace ((10, 2) :: (3, 2) :: (1, 1) :: repeat (1, 2) 33 ++ (1081, 2) :: (1, 1) :: repeat (1, 2) 2284 ++ (5187, 2) :: (1, 1) :: repeat (1, 2) 23909 ++ (11951, 2) :: (1, 1) :: repeat (1, 2) 100592 ++ (438888, 2) :: (1, 1) :: repeat (1, 2) 1511339 ++ (5653179, 2) :: (1, 1) :: repeat (1, 2) 11874956 ++ w) with ((12 - 2, 2) :: (3, 2) :: (1, 1) :: repeat (1, 2) 33 ++ (1081, 2) :: (1, 1) :: repeat (1, 2) 2284 ++ (5187, 2) :: (1, 1) :: repeat (1, 2) 23909 ++ (11951, 2) :: (1, 1) :: repeat (1, 2) 100592 ++ (438888, 2) :: (1, 1) :: repeat (1, 2) 1511339 ++ (5653179, 2) :: (1, 1) :: repeat (1, 2) 11874956 ++ w) by sec_eq.
    apply (sPUSH [] 3 12 ((3, 2) :: (1, 1) :: repeat (1, 2) 33 ++ (1081, 2) :: (1, 1) :: repeat (1, 2) 2284 ++ (5187, 2) :: (1, 1) :: repeat (1, 2) 23909 ++ (11951, 2) :: (1, 1) :: repeat (1, 2) 100592 ++ (438888, 2) :: (1, 1) :: repeat (1, 2) 1511339 ++ (5653179, 2) :: (1, 1) :: repeat (1, 2) 11874956 ++ w) 1); closearith.
  }
  (* step 249: P TDN *)
  apply (hsteps_trans _ (HB [] 3 1 4 ((10, 2) :: (3, 2) :: (1, 1) :: repeat (1, 2) 33 ++ (1081, 2) :: (1, 1) :: repeat (1, 2) 2284 ++ (5187, 2) :: (1, 1) :: repeat (1, 2) 23909 ++ (11951, 2) :: (1, 1) :: repeat (1, 2) 100592 ++ (438888, 2) :: (1, 1) :: repeat (1, 2) 1511339 ++ (5653179, 2) :: (1, 1) :: repeat (1, 2) 11874956 ++ w) 1)).
  {
    apply (sTDN [] 3 ((10, 2) :: (3, 2) :: (1, 1) :: repeat (1, 2) 33 ++ (1081, 2) :: (1, 1) :: repeat (1, 2) 2284 ++ (5187, 2) :: (1, 1) :: repeat (1, 2) 23909 ++ (11951, 2) :: (1, 1) :: repeat (1, 2) 100592 ++ (438888, 2) :: (1, 1) :: repeat (1, 2) 1511339 ++ (5653179, 2) :: (1, 1) :: repeat (1, 2) 11874956 ++ w) 1).
  }
  (* step 250: sTUP *)
  apply (hsteps_trans _ (HC [] 3 3 2 ((8, 2) :: (3, 2) :: (1, 1) :: repeat (1, 2) 33 ++ (1081, 2) :: (1, 1) :: repeat (1, 2) 2284 ++ (5187, 2) :: (1, 1) :: repeat (1, 2) 23909 ++ (11951, 2) :: (1, 1) :: repeat (1, 2) 100592 ++ (438888, 2) :: (1, 1) :: repeat (1, 2) 1511339 ++ (5653179, 2) :: (1, 1) :: repeat (1, 2) 11874956 ++ w) 1)).
  {
    replace ((8, 2) :: (3, 2) :: (1, 1) :: repeat (1, 2) 33 ++ (1081, 2) :: (1, 1) :: repeat (1, 2) 2284 ++ (5187, 2) :: (1, 1) :: repeat (1, 2) 23909 ++ (11951, 2) :: (1, 1) :: repeat (1, 2) 100592 ++ (438888, 2) :: (1, 1) :: repeat (1, 2) 1511339 ++ (5653179, 2) :: (1, 1) :: repeat (1, 2) 11874956 ++ w) with ((10 - 2, 2) :: (3, 2) :: (1, 1) :: repeat (1, 2) 33 ++ (1081, 2) :: (1, 1) :: repeat (1, 2) 2284 ++ (5187, 2) :: (1, 1) :: repeat (1, 2) 23909 ++ (11951, 2) :: (1, 1) :: repeat (1, 2) 100592 ++ (438888, 2) :: (1, 1) :: repeat (1, 2) 1511339 ++ (5653179, 2) :: (1, 1) :: repeat (1, 2) 11874956 ++ w) by sec_eq.
    apply (sTUP [] 3 4 10 2 ((3, 2) :: (1, 1) :: repeat (1, 2) 33 ++ (1081, 2) :: (1, 1) :: repeat (1, 2) 2284 ++ (5187, 2) :: (1, 1) :: repeat (1, 2) 23909 ++ (11951, 2) :: (1, 1) :: repeat (1, 2) 100592 ++ (438888, 2) :: (1, 1) :: repeat (1, 2) 1511339 ++ (5653179, 2) :: (1, 1) :: repeat (1, 2) 11874956 ++ w) 1); closearith.
  }
  (* step 251: DIPGRIND 3 2 *)
  apply (hsteps_trans _ (HC [] 0 3 2 (repeat (1, 2) 3 ++ (2, 2) :: (3, 2) :: (1, 1) :: repeat (1, 2) 33 ++ (1081, 2) :: (1, 1) :: repeat (1, 2) 2284 ++ (5187, 2) :: (1, 1) :: repeat (1, 2) 23909 ++ (11951, 2) :: (1, 1) :: repeat (1, 2) 100592 ++ (438888, 2) :: (1, 1) :: repeat (1, 2) 1511339 ++ (5653179, 2) :: (1, 1) :: repeat (1, 2) 11874956 ++ w) 1)).
  {
    apply (DIPGRIND 3 2 [] ((3, 2) :: (1, 1) :: repeat (1, 2) 33 ++ (1081, 2) :: (1, 1) :: repeat (1, 2) 2284 ++ (5187, 2) :: (1, 1) :: repeat (1, 2) 23909 ++ (11951, 2) :: (1, 1) :: repeat (1, 2) 100592 ++ (438888, 2) :: (1, 1) :: repeat (1, 2) 1511339 ++ (5653179, 2) :: (1, 1) :: repeat (1, 2) 11874956 ++ w) 1); closearith.
  }
  (* step 252: P PUSHX *)
  apply (hsteps_trans _ (HB [] 1 1 7 (repeat (1, 2) 3 ++ (2, 2) :: (3, 2) :: (1, 1) :: repeat (1, 2) 33 ++ (1081, 2) :: (1, 1) :: repeat (1, 2) 2284 ++ (5187, 2) :: (1, 1) :: repeat (1, 2) 23909 ++ (11951, 2) :: (1, 1) :: repeat (1, 2) 100592 ++ (438888, 2) :: (1, 1) :: repeat (1, 2) 1511339 ++ (5653179, 2) :: (1, 1) :: repeat (1, 2) 11874956 ++ w) 1)).
  {
    exact (hsteps_step _ _ _ (hPUSHX (repeat (1, 2) 3 ++ (2, 2) :: (3, 2) :: (1, 1) :: repeat (1, 2) 33 ++ (1081, 2) :: (1, 1) :: repeat (1, 2) 2284 ++ (5187, 2) :: (1, 1) :: repeat (1, 2) 23909 ++ (11951, 2) :: (1, 1) :: repeat (1, 2) 100592 ++ (438888, 2) :: (1, 1) :: repeat (1, 2) 1511339 ++ (5653179, 2) :: (1, 1) :: repeat (1, 2) 11874956 ++ w) 1) (hsteps_refl _)).
  }
  (* step 253: M pop12 (3,) *)
  apply (hsteps_trans _ (HB [] 4 1 13 ((2, 2) :: (3, 2) :: (1, 1) :: repeat (1, 2) 33 ++ (1081, 2) :: (1, 1) :: repeat (1, 2) 2284 ++ (5187, 2) :: (1, 1) :: repeat (1, 2) 23909 ++ (11951, 2) :: (1, 1) :: repeat (1, 2) 100592 ++ (438888, 2) :: (1, 1) :: repeat (1, 2) 1511339 ++ (5653179, 2) :: (1, 1) :: repeat (1, 2) 11874956 ++ w) 1)).
  {
    apply (pop12 3 [] 1 7 ((2, 2) :: (3, 2) :: (1, 1) :: repeat (1, 2) 33 ++ (1081, 2) :: (1, 1) :: repeat (1, 2) 2284 ++ (5187, 2) :: (1, 1) :: repeat (1, 2) 23909 ++ (11951, 2) :: (1, 1) :: repeat (1, 2) 100592 ++ (438888, 2) :: (1, 1) :: repeat (1, 2) 1511339 ++ (5653179, 2) :: (1, 1) :: repeat (1, 2) 11874956 ++ w) 1); closearith.
  }
  (* step 254: P TUP2_1 *)
  apply (hsteps_trans _ (HC [5] 13 1 2 (repeat (1, 2) 1 ++ (1, 1) :: repeat (1, 2) 33 ++ (1081, 2) :: (1, 1) :: repeat (1, 2) 2284 ++ (5187, 2) :: (1, 1) :: repeat (1, 2) 23909 ++ (11951, 2) :: (1, 1) :: repeat (1, 2) 100592 ++ (438888, 2) :: (1, 1) :: repeat (1, 2) 1511339 ++ (5653179, 2) :: (1, 1) :: repeat (1, 2) 11874956 ++ w) 1)).
  {
    replace (repeat (1, 2) 1 ++ (1, 1) :: repeat (1, 2) 33 ++ (1081, 2) :: (1, 1) :: repeat (1, 2) 2284 ++ (5187, 2) :: (1, 1) :: repeat (1, 2) 23909 ++ (11951, 2) :: (1, 1) :: repeat (1, 2) 100592 ++ (438888, 2) :: (1, 1) :: repeat (1, 2) 1511339 ++ (5653179, 2) :: (1, 1) :: repeat (1, 2) 11874956 ++ w) with ((3 - 2, 2) :: (1, 1) :: repeat (1, 2) 33 ++ (1081, 2) :: (1, 1) :: repeat (1, 2) 2284 ++ (5187, 2) :: (1, 1) :: repeat (1, 2) 23909 ++ (11951, 2) :: (1, 1) :: repeat (1, 2) 100592 ++ (438888, 2) :: (1, 1) :: repeat (1, 2) 1511339 ++ (5653179, 2) :: (1, 1) :: repeat (1, 2) 11874956 ++ w) by sec_eq.
    apply (sTUP2_1 [] 4 12 3 ((1, 1) :: repeat (1, 2) 33 ++ (1081, 2) :: (1, 1) :: repeat (1, 2) 2284 ++ (5187, 2) :: (1, 1) :: repeat (1, 2) 23909 ++ (11951, 2) :: (1, 1) :: repeat (1, 2) 100592 ++ (438888, 2) :: (1, 1) :: repeat (1, 2) 1511339 ++ (5653179, 2) :: (1, 1) :: repeat (1, 2) 11874956 ++ w) 1); closearith.
  }
  (* step 255: P TDN *)
  apply (hsteps_trans _ (HB [5] 13 1 4 (repeat (1, 2) 1 ++ (1, 1) :: repeat (1, 2) 33 ++ (1081, 2) :: (1, 1) :: repeat (1, 2) 2284 ++ (5187, 2) :: (1, 1) :: repeat (1, 2) 23909 ++ (11951, 2) :: (1, 1) :: repeat (1, 2) 100592 ++ (438888, 2) :: (1, 1) :: repeat (1, 2) 1511339 ++ (5653179, 2) :: (1, 1) :: repeat (1, 2) 11874956 ++ w) 1)).
  {
    apply (sTDN [5] 13 (repeat (1, 2) 1 ++ (1, 1) :: repeat (1, 2) 33 ++ (1081, 2) :: (1, 1) :: repeat (1, 2) 2284 ++ (5187, 2) :: (1, 1) :: repeat (1, 2) 23909 ++ (11951, 2) :: (1, 1) :: repeat (1, 2) 100592 ++ (438888, 2) :: (1, 1) :: repeat (1, 2) 1511339 ++ (5653179, 2) :: (1, 1) :: repeat (1, 2) 11874956 ++ w) 1).
  }
  (* step 256: M pop12 (1,) *)
  apply (hsteps_trans _ (HB [5] 14 1 6 ((1, 1) :: repeat (1, 2) 33 ++ (1081, 2) :: (1, 1) :: repeat (1, 2) 2284 ++ (5187, 2) :: (1, 1) :: repeat (1, 2) 23909 ++ (11951, 2) :: (1, 1) :: repeat (1, 2) 100592 ++ (438888, 2) :: (1, 1) :: repeat (1, 2) 1511339 ++ (5653179, 2) :: (1, 1) :: repeat (1, 2) 11874956 ++ w) 1)).
  {
    apply (pop12 1 [5] 13 4 ((1, 1) :: repeat (1, 2) 33 ++ (1081, 2) :: (1, 1) :: repeat (1, 2) 2284 ++ (5187, 2) :: (1, 1) :: repeat (1, 2) 23909 ++ (11951, 2) :: (1, 1) :: repeat (1, 2) 100592 ++ (438888, 2) :: (1, 1) :: repeat (1, 2) 1511339 ++ (5653179, 2) :: (1, 1) :: repeat (1, 2) 11874956 ++ w) 1); closearith.
  }
  (* step 257: P POP *)
  apply (hsteps_trans _ (HB [5] 15 1 7 (repeat (1, 2) 33 ++ (1081, 2) :: (1, 1) :: repeat (1, 2) 2284 ++ (5187, 2) :: (1, 1) :: repeat (1, 2) 23909 ++ (11951, 2) :: (1, 1) :: repeat (1, 2) 100592 ++ (438888, 2) :: (1, 1) :: repeat (1, 2) 1511339 ++ (5653179, 2) :: (1, 1) :: repeat (1, 2) 11874956 ++ w) 1)).
  {
    apply (sPOP1 [5] 14 6 (repeat (1, 2) 33 ++ (1081, 2) :: (1, 1) :: repeat (1, 2) 2284 ++ (5187, 2) :: (1, 1) :: repeat (1, 2) 23909 ++ (11951, 2) :: (1, 1) :: repeat (1, 2) 100592 ++ (438888, 2) :: (1, 1) :: repeat (1, 2) 1511339 ++ (5653179, 2) :: (1, 1) :: repeat (1, 2) 11874956 ++ w) 1); closearith.
  }
  (* step 258: M pop12 (33,) *)
  apply (hsteps_trans _ (HB [5] 48 1 73 ((1081, 2) :: (1, 1) :: repeat (1, 2) 2284 ++ (5187, 2) :: (1, 1) :: repeat (1, 2) 23909 ++ (11951, 2) :: (1, 1) :: repeat (1, 2) 100592 ++ (438888, 2) :: (1, 1) :: repeat (1, 2) 1511339 ++ (5653179, 2) :: (1, 1) :: repeat (1, 2) 11874956 ++ w) 1)).
  {
    apply (pop12 33 [5] 15 7 ((1081, 2) :: (1, 1) :: repeat (1, 2) 2284 ++ (5187, 2) :: (1, 1) :: repeat (1, 2) 23909 ++ (11951, 2) :: (1, 1) :: repeat (1, 2) 100592 ++ (438888, 2) :: (1, 1) :: repeat (1, 2) 1511339 ++ (5653179, 2) :: (1, 1) :: repeat (1, 2) 11874956 ++ w) 1); closearith.
  }
  (* step 259: sTUP *)
  apply (hsteps_trans _ (HC [5] 48 72 2 ((1079, 2) :: (1, 1) :: repeat (1, 2) 2284 ++ (5187, 2) :: (1, 1) :: repeat (1, 2) 23909 ++ (11951, 2) :: (1, 1) :: repeat (1, 2) 100592 ++ (438888, 2) :: (1, 1) :: repeat (1, 2) 1511339 ++ (5653179, 2) :: (1, 1) :: repeat (1, 2) 11874956 ++ w) 1)).
  {
    replace ((1079, 2) :: (1, 1) :: repeat (1, 2) 2284 ++ (5187, 2) :: (1, 1) :: repeat (1, 2) 23909 ++ (11951, 2) :: (1, 1) :: repeat (1, 2) 100592 ++ (438888, 2) :: (1, 1) :: repeat (1, 2) 1511339 ++ (5653179, 2) :: (1, 1) :: repeat (1, 2) 11874956 ++ w) with ((1081 - 2, 2) :: (1, 1) :: repeat (1, 2) 2284 ++ (5187, 2) :: (1, 1) :: repeat (1, 2) 23909 ++ (11951, 2) :: (1, 1) :: repeat (1, 2) 100592 ++ (438888, 2) :: (1, 1) :: repeat (1, 2) 1511339 ++ (5653179, 2) :: (1, 1) :: repeat (1, 2) 11874956 ++ w) by sec_eq.
    apply (sTUP [5] 48 73 1081 2 ((1, 1) :: repeat (1, 2) 2284 ++ (5187, 2) :: (1, 1) :: repeat (1, 2) 23909 ++ (11951, 2) :: (1, 1) :: repeat (1, 2) 100592 ++ (438888, 2) :: (1, 1) :: repeat (1, 2) 1511339 ++ (5653179, 2) :: (1, 1) :: repeat (1, 2) 11874956 ++ w) 1); closearith.
  }
  (* step 260: hGRIND_even 34 *)
  apply (hsteps_trans _ (HB [5] 47 1 72 ((2, 2) :: (1079, 2) :: (1, 1) :: repeat (1, 2) 2284 ++ (5187, 2) :: (1, 1) :: repeat (1, 2) 23909 ++ (11951, 2) :: (1, 1) :: repeat (1, 2) 100592 ++ (438888, 2) :: (1, 1) :: repeat (1, 2) 1511339 ++ (5653179, 2) :: (1, 1) :: repeat (1, 2) 11874956 ++ w) 1)).
  {
    apply (hGRIND_even 34 [5] 47 ((1079, 2) :: (1, 1) :: repeat (1, 2) 2284 ++ (5187, 2) :: (1, 1) :: repeat (1, 2) 23909 ++ (11951, 2) :: (1, 1) :: repeat (1, 2) 100592 ++ (438888, 2) :: (1, 1) :: repeat (1, 2) 1511339 ++ (5653179, 2) :: (1, 1) :: repeat (1, 2) 11874956 ++ w) 1); closearith.
  }
  (* step 261: P TUP2_1 *)
  apply (hsteps_trans _ (HC [48; 5] 72 1 2 ((1077, 2) :: (1, 1) :: repeat (1, 2) 2284 ++ (5187, 2) :: (1, 1) :: repeat (1, 2) 23909 ++ (11951, 2) :: (1, 1) :: repeat (1, 2) 100592 ++ (438888, 2) :: (1, 1) :: repeat (1, 2) 1511339 ++ (5653179, 2) :: (1, 1) :: repeat (1, 2) 11874956 ++ w) 1)).
  {
    replace ((1077, 2) :: (1, 1) :: repeat (1, 2) 2284 ++ (5187, 2) :: (1, 1) :: repeat (1, 2) 23909 ++ (11951, 2) :: (1, 1) :: repeat (1, 2) 100592 ++ (438888, 2) :: (1, 1) :: repeat (1, 2) 1511339 ++ (5653179, 2) :: (1, 1) :: repeat (1, 2) 11874956 ++ w) with ((1079 - 2, 2) :: (1, 1) :: repeat (1, 2) 2284 ++ (5187, 2) :: (1, 1) :: repeat (1, 2) 23909 ++ (11951, 2) :: (1, 1) :: repeat (1, 2) 100592 ++ (438888, 2) :: (1, 1) :: repeat (1, 2) 1511339 ++ (5653179, 2) :: (1, 1) :: repeat (1, 2) 11874956 ++ w) by sec_eq.
    apply (sTUP2_1 [5] 47 71 1079 ((1, 1) :: repeat (1, 2) 2284 ++ (5187, 2) :: (1, 1) :: repeat (1, 2) 23909 ++ (11951, 2) :: (1, 1) :: repeat (1, 2) 100592 ++ (438888, 2) :: (1, 1) :: repeat (1, 2) 1511339 ++ (5653179, 2) :: (1, 1) :: repeat (1, 2) 11874956 ++ w) 1); closearith.
  }
  (* step 262: P TDN *)
  apply (hsteps_trans _ (HB [48; 5] 72 1 4 ((1077, 2) :: (1, 1) :: repeat (1, 2) 2284 ++ (5187, 2) :: (1, 1) :: repeat (1, 2) 23909 ++ (11951, 2) :: (1, 1) :: repeat (1, 2) 100592 ++ (438888, 2) :: (1, 1) :: repeat (1, 2) 1511339 ++ (5653179, 2) :: (1, 1) :: repeat (1, 2) 11874956 ++ w) 1)).
  {
    apply (sTDN [48; 5] 72 ((1077, 2) :: (1, 1) :: repeat (1, 2) 2284 ++ (5187, 2) :: (1, 1) :: repeat (1, 2) 23909 ++ (11951, 2) :: (1, 1) :: repeat (1, 2) 100592 ++ (438888, 2) :: (1, 1) :: repeat (1, 2) 1511339 ++ (5653179, 2) :: (1, 1) :: repeat (1, 2) 11874956 ++ w) 1).
  }
  (* step 263: sTUP *)
  apply (hsteps_trans _ (HC [48; 5] 72 3 2 ((1075, 2) :: (1, 1) :: repeat (1, 2) 2284 ++ (5187, 2) :: (1, 1) :: repeat (1, 2) 23909 ++ (11951, 2) :: (1, 1) :: repeat (1, 2) 100592 ++ (438888, 2) :: (1, 1) :: repeat (1, 2) 1511339 ++ (5653179, 2) :: (1, 1) :: repeat (1, 2) 11874956 ++ w) 1)).
  {
    replace ((1075, 2) :: (1, 1) :: repeat (1, 2) 2284 ++ (5187, 2) :: (1, 1) :: repeat (1, 2) 23909 ++ (11951, 2) :: (1, 1) :: repeat (1, 2) 100592 ++ (438888, 2) :: (1, 1) :: repeat (1, 2) 1511339 ++ (5653179, 2) :: (1, 1) :: repeat (1, 2) 11874956 ++ w) with ((1077 - 2, 2) :: (1, 1) :: repeat (1, 2) 2284 ++ (5187, 2) :: (1, 1) :: repeat (1, 2) 23909 ++ (11951, 2) :: (1, 1) :: repeat (1, 2) 100592 ++ (438888, 2) :: (1, 1) :: repeat (1, 2) 1511339 ++ (5653179, 2) :: (1, 1) :: repeat (1, 2) 11874956 ++ w) by sec_eq.
    apply (sTUP [48; 5] 72 4 1077 2 ((1, 1) :: repeat (1, 2) 2284 ++ (5187, 2) :: (1, 1) :: repeat (1, 2) 23909 ++ (11951, 2) :: (1, 1) :: repeat (1, 2) 100592 ++ (438888, 2) :: (1, 1) :: repeat (1, 2) 1511339 ++ (5653179, 2) :: (1, 1) :: repeat (1, 2) 11874956 ++ w) 1); closearith.
  }
  (* step 264: DIPGRIND 72 931 *)
  apply (hsteps_trans _ (HC [48; 5] 0 3 2 (repeat (1, 2) 72 ++ (931, 2) :: (1, 1) :: repeat (1, 2) 2284 ++ (5187, 2) :: (1, 1) :: repeat (1, 2) 23909 ++ (11951, 2) :: (1, 1) :: repeat (1, 2) 100592 ++ (438888, 2) :: (1, 1) :: repeat (1, 2) 1511339 ++ (5653179, 2) :: (1, 1) :: repeat (1, 2) 11874956 ++ w) 1)).
  {
    apply (DIPGRIND 72 931 [48; 5] ((1, 1) :: repeat (1, 2) 2284 ++ (5187, 2) :: (1, 1) :: repeat (1, 2) 23909 ++ (11951, 2) :: (1, 1) :: repeat (1, 2) 100592 ++ (438888, 2) :: (1, 1) :: repeat (1, 2) 1511339 ++ (5653179, 2) :: (1, 1) :: repeat (1, 2) 11874956 ++ w) 1); closearith.
  }
  (* step 265: P PX2A *)
  apply (hsteps_trans _ (HC [] 4 46 2 ((1, 1) :: repeat (1, 2) 74 ++ (931, 2) :: (1, 1) :: repeat (1, 2) 2284 ++ (5187, 2) :: (1, 1) :: repeat (1, 2) 23909 ++ (11951, 2) :: (1, 1) :: repeat (1, 2) 100592 ++ (438888, 2) :: (1, 1) :: repeat (1, 2) 1511339 ++ (5653179, 2) :: (1, 1) :: repeat (1, 2) 11874956 ++ w) 1)).
  {
    exact (hsteps_step _ _ _ (hPX2A 45 4 [] (repeat (1, 2) 72 ++ (931, 2) :: (1, 1) :: repeat (1, 2) 2284 ++ (5187, 2) :: (1, 1) :: repeat (1, 2) 23909 ++ (11951, 2) :: (1, 1) :: repeat (1, 2) 100592 ++ (438888, 2) :: (1, 1) :: repeat (1, 2) 1511339 ++ (5653179, 2) :: (1, 1) :: repeat (1, 2) 11874956 ++ w) 1) (hsteps_refl _)).
  }
  (* step 266: P PUSH *)
  apply (hsteps_trans _ (HC [] 3 1 2 ((44, 2) :: (1, 1) :: repeat (1, 2) 74 ++ (931, 2) :: (1, 1) :: repeat (1, 2) 2284 ++ (5187, 2) :: (1, 1) :: repeat (1, 2) 23909 ++ (11951, 2) :: (1, 1) :: repeat (1, 2) 100592 ++ (438888, 2) :: (1, 1) :: repeat (1, 2) 1511339 ++ (5653179, 2) :: (1, 1) :: repeat (1, 2) 11874956 ++ w) 1)).
  {
    replace ((44, 2) :: (1, 1) :: repeat (1, 2) 74 ++ (931, 2) :: (1, 1) :: repeat (1, 2) 2284 ++ (5187, 2) :: (1, 1) :: repeat (1, 2) 23909 ++ (11951, 2) :: (1, 1) :: repeat (1, 2) 100592 ++ (438888, 2) :: (1, 1) :: repeat (1, 2) 1511339 ++ (5653179, 2) :: (1, 1) :: repeat (1, 2) 11874956 ++ w) with ((46 - 2, 2) :: (1, 1) :: repeat (1, 2) 74 ++ (931, 2) :: (1, 1) :: repeat (1, 2) 2284 ++ (5187, 2) :: (1, 1) :: repeat (1, 2) 23909 ++ (11951, 2) :: (1, 1) :: repeat (1, 2) 100592 ++ (438888, 2) :: (1, 1) :: repeat (1, 2) 1511339 ++ (5653179, 2) :: (1, 1) :: repeat (1, 2) 11874956 ++ w) by sec_eq.
    apply (sPUSH [] 3 46 ((1, 1) :: repeat (1, 2) 74 ++ (931, 2) :: (1, 1) :: repeat (1, 2) 2284 ++ (5187, 2) :: (1, 1) :: repeat (1, 2) 23909 ++ (11951, 2) :: (1, 1) :: repeat (1, 2) 100592 ++ (438888, 2) :: (1, 1) :: repeat (1, 2) 1511339 ++ (5653179, 2) :: (1, 1) :: repeat (1, 2) 11874956 ++ w) 1); closearith.
  }
  (* step 267: P TDN *)
  apply (hsteps_trans _ (HB [] 3 1 4 ((44, 2) :: (1, 1) :: repeat (1, 2) 74 ++ (931, 2) :: (1, 1) :: repeat (1, 2) 2284 ++ (5187, 2) :: (1, 1) :: repeat (1, 2) 23909 ++ (11951, 2) :: (1, 1) :: repeat (1, 2) 100592 ++ (438888, 2) :: (1, 1) :: repeat (1, 2) 1511339 ++ (5653179, 2) :: (1, 1) :: repeat (1, 2) 11874956 ++ w) 1)).
  {
    apply (sTDN [] 3 ((44, 2) :: (1, 1) :: repeat (1, 2) 74 ++ (931, 2) :: (1, 1) :: repeat (1, 2) 2284 ++ (5187, 2) :: (1, 1) :: repeat (1, 2) 23909 ++ (11951, 2) :: (1, 1) :: repeat (1, 2) 100592 ++ (438888, 2) :: (1, 1) :: repeat (1, 2) 1511339 ++ (5653179, 2) :: (1, 1) :: repeat (1, 2) 11874956 ++ w) 1).
  }
  (* step 268: sTUP *)
  apply (hsteps_trans _ (HC [] 3 3 2 ((42, 2) :: (1, 1) :: repeat (1, 2) 74 ++ (931, 2) :: (1, 1) :: repeat (1, 2) 2284 ++ (5187, 2) :: (1, 1) :: repeat (1, 2) 23909 ++ (11951, 2) :: (1, 1) :: repeat (1, 2) 100592 ++ (438888, 2) :: (1, 1) :: repeat (1, 2) 1511339 ++ (5653179, 2) :: (1, 1) :: repeat (1, 2) 11874956 ++ w) 1)).
  {
    replace ((42, 2) :: (1, 1) :: repeat (1, 2) 74 ++ (931, 2) :: (1, 1) :: repeat (1, 2) 2284 ++ (5187, 2) :: (1, 1) :: repeat (1, 2) 23909 ++ (11951, 2) :: (1, 1) :: repeat (1, 2) 100592 ++ (438888, 2) :: (1, 1) :: repeat (1, 2) 1511339 ++ (5653179, 2) :: (1, 1) :: repeat (1, 2) 11874956 ++ w) with ((44 - 2, 2) :: (1, 1) :: repeat (1, 2) 74 ++ (931, 2) :: (1, 1) :: repeat (1, 2) 2284 ++ (5187, 2) :: (1, 1) :: repeat (1, 2) 23909 ++ (11951, 2) :: (1, 1) :: repeat (1, 2) 100592 ++ (438888, 2) :: (1, 1) :: repeat (1, 2) 1511339 ++ (5653179, 2) :: (1, 1) :: repeat (1, 2) 11874956 ++ w) by sec_eq.
    apply (sTUP [] 3 4 44 2 ((1, 1) :: repeat (1, 2) 74 ++ (931, 2) :: (1, 1) :: repeat (1, 2) 2284 ++ (5187, 2) :: (1, 1) :: repeat (1, 2) 23909 ++ (11951, 2) :: (1, 1) :: repeat (1, 2) 100592 ++ (438888, 2) :: (1, 1) :: repeat (1, 2) 1511339 ++ (5653179, 2) :: (1, 1) :: repeat (1, 2) 11874956 ++ w) 1); closearith.
  }
  (* step 269: DIPGRIND 3 36 *)
  apply (hsteps_trans _ (HC [] 0 3 2 (repeat (1, 2) 3 ++ (36, 2) :: (1, 1) :: repeat (1, 2) 74 ++ (931, 2) :: (1, 1) :: repeat (1, 2) 2284 ++ (5187, 2) :: (1, 1) :: repeat (1, 2) 23909 ++ (11951, 2) :: (1, 1) :: repeat (1, 2) 100592 ++ (438888, 2) :: (1, 1) :: repeat (1, 2) 1511339 ++ (5653179, 2) :: (1, 1) :: repeat (1, 2) 11874956 ++ w) 1)).
  {
    apply (DIPGRIND 3 36 [] ((1, 1) :: repeat (1, 2) 74 ++ (931, 2) :: (1, 1) :: repeat (1, 2) 2284 ++ (5187, 2) :: (1, 1) :: repeat (1, 2) 23909 ++ (11951, 2) :: (1, 1) :: repeat (1, 2) 100592 ++ (438888, 2) :: (1, 1) :: repeat (1, 2) 1511339 ++ (5653179, 2) :: (1, 1) :: repeat (1, 2) 11874956 ++ w) 1); closearith.
  }
  (* step 270: P PUSHX *)
  apply (hsteps_trans _ (HB [] 1 1 7 (repeat (1, 2) 3 ++ (36, 2) :: (1, 1) :: repeat (1, 2) 74 ++ (931, 2) :: (1, 1) :: repeat (1, 2) 2284 ++ (5187, 2) :: (1, 1) :: repeat (1, 2) 23909 ++ (11951, 2) :: (1, 1) :: repeat (1, 2) 100592 ++ (438888, 2) :: (1, 1) :: repeat (1, 2) 1511339 ++ (5653179, 2) :: (1, 1) :: repeat (1, 2) 11874956 ++ w) 1)).
  {
    exact (hsteps_step _ _ _ (hPUSHX (repeat (1, 2) 3 ++ (36, 2) :: (1, 1) :: repeat (1, 2) 74 ++ (931, 2) :: (1, 1) :: repeat (1, 2) 2284 ++ (5187, 2) :: (1, 1) :: repeat (1, 2) 23909 ++ (11951, 2) :: (1, 1) :: repeat (1, 2) 100592 ++ (438888, 2) :: (1, 1) :: repeat (1, 2) 1511339 ++ (5653179, 2) :: (1, 1) :: repeat (1, 2) 11874956 ++ w) 1) (hsteps_refl _)).
  }
  (* step 271: M pop12 (3,) *)
  apply (hsteps_trans _ (HB [] 4 1 13 ((36, 2) :: (1, 1) :: repeat (1, 2) 74 ++ (931, 2) :: (1, 1) :: repeat (1, 2) 2284 ++ (5187, 2) :: (1, 1) :: repeat (1, 2) 23909 ++ (11951, 2) :: (1, 1) :: repeat (1, 2) 100592 ++ (438888, 2) :: (1, 1) :: repeat (1, 2) 1511339 ++ (5653179, 2) :: (1, 1) :: repeat (1, 2) 11874956 ++ w) 1)).
  {
    apply (pop12 3 [] 1 7 ((36, 2) :: (1, 1) :: repeat (1, 2) 74 ++ (931, 2) :: (1, 1) :: repeat (1, 2) 2284 ++ (5187, 2) :: (1, 1) :: repeat (1, 2) 23909 ++ (11951, 2) :: (1, 1) :: repeat (1, 2) 100592 ++ (438888, 2) :: (1, 1) :: repeat (1, 2) 1511339 ++ (5653179, 2) :: (1, 1) :: repeat (1, 2) 11874956 ++ w) 1); closearith.
  }
  (* step 272: sTUP *)
  apply (hsteps_trans _ (HC [] 4 12 2 ((34, 2) :: (1, 1) :: repeat (1, 2) 74 ++ (931, 2) :: (1, 1) :: repeat (1, 2) 2284 ++ (5187, 2) :: (1, 1) :: repeat (1, 2) 23909 ++ (11951, 2) :: (1, 1) :: repeat (1, 2) 100592 ++ (438888, 2) :: (1, 1) :: repeat (1, 2) 1511339 ++ (5653179, 2) :: (1, 1) :: repeat (1, 2) 11874956 ++ w) 1)).
  {
    replace ((34, 2) :: (1, 1) :: repeat (1, 2) 74 ++ (931, 2) :: (1, 1) :: repeat (1, 2) 2284 ++ (5187, 2) :: (1, 1) :: repeat (1, 2) 23909 ++ (11951, 2) :: (1, 1) :: repeat (1, 2) 100592 ++ (438888, 2) :: (1, 1) :: repeat (1, 2) 1511339 ++ (5653179, 2) :: (1, 1) :: repeat (1, 2) 11874956 ++ w) with ((36 - 2, 2) :: (1, 1) :: repeat (1, 2) 74 ++ (931, 2) :: (1, 1) :: repeat (1, 2) 2284 ++ (5187, 2) :: (1, 1) :: repeat (1, 2) 23909 ++ (11951, 2) :: (1, 1) :: repeat (1, 2) 100592 ++ (438888, 2) :: (1, 1) :: repeat (1, 2) 1511339 ++ (5653179, 2) :: (1, 1) :: repeat (1, 2) 11874956 ++ w) by sec_eq.
    apply (sTUP [] 4 13 36 2 ((1, 1) :: repeat (1, 2) 74 ++ (931, 2) :: (1, 1) :: repeat (1, 2) 2284 ++ (5187, 2) :: (1, 1) :: repeat (1, 2) 23909 ++ (11951, 2) :: (1, 1) :: repeat (1, 2) 100592 ++ (438888, 2) :: (1, 1) :: repeat (1, 2) 1511339 ++ (5653179, 2) :: (1, 1) :: repeat (1, 2) 11874956 ++ w) 1); closearith.
  }
  (* step 273: P PUSH *)
  apply (hsteps_trans _ (HC [] 3 1 2 ((10, 2) :: (34, 2) :: (1, 1) :: repeat (1, 2) 74 ++ (931, 2) :: (1, 1) :: repeat (1, 2) 2284 ++ (5187, 2) :: (1, 1) :: repeat (1, 2) 23909 ++ (11951, 2) :: (1, 1) :: repeat (1, 2) 100592 ++ (438888, 2) :: (1, 1) :: repeat (1, 2) 1511339 ++ (5653179, 2) :: (1, 1) :: repeat (1, 2) 11874956 ++ w) 1)).
  {
    replace ((10, 2) :: (34, 2) :: (1, 1) :: repeat (1, 2) 74 ++ (931, 2) :: (1, 1) :: repeat (1, 2) 2284 ++ (5187, 2) :: (1, 1) :: repeat (1, 2) 23909 ++ (11951, 2) :: (1, 1) :: repeat (1, 2) 100592 ++ (438888, 2) :: (1, 1) :: repeat (1, 2) 1511339 ++ (5653179, 2) :: (1, 1) :: repeat (1, 2) 11874956 ++ w) with ((12 - 2, 2) :: (34, 2) :: (1, 1) :: repeat (1, 2) 74 ++ (931, 2) :: (1, 1) :: repeat (1, 2) 2284 ++ (5187, 2) :: (1, 1) :: repeat (1, 2) 23909 ++ (11951, 2) :: (1, 1) :: repeat (1, 2) 100592 ++ (438888, 2) :: (1, 1) :: repeat (1, 2) 1511339 ++ (5653179, 2) :: (1, 1) :: repeat (1, 2) 11874956 ++ w) by sec_eq.
    apply (sPUSH [] 3 12 ((34, 2) :: (1, 1) :: repeat (1, 2) 74 ++ (931, 2) :: (1, 1) :: repeat (1, 2) 2284 ++ (5187, 2) :: (1, 1) :: repeat (1, 2) 23909 ++ (11951, 2) :: (1, 1) :: repeat (1, 2) 100592 ++ (438888, 2) :: (1, 1) :: repeat (1, 2) 1511339 ++ (5653179, 2) :: (1, 1) :: repeat (1, 2) 11874956 ++ w) 1); closearith.
  }
  (* step 274: P TDN *)
  apply (hsteps_trans _ (HB [] 3 1 4 ((10, 2) :: (34, 2) :: (1, 1) :: repeat (1, 2) 74 ++ (931, 2) :: (1, 1) :: repeat (1, 2) 2284 ++ (5187, 2) :: (1, 1) :: repeat (1, 2) 23909 ++ (11951, 2) :: (1, 1) :: repeat (1, 2) 100592 ++ (438888, 2) :: (1, 1) :: repeat (1, 2) 1511339 ++ (5653179, 2) :: (1, 1) :: repeat (1, 2) 11874956 ++ w) 1)).
  {
    apply (sTDN [] 3 ((10, 2) :: (34, 2) :: (1, 1) :: repeat (1, 2) 74 ++ (931, 2) :: (1, 1) :: repeat (1, 2) 2284 ++ (5187, 2) :: (1, 1) :: repeat (1, 2) 23909 ++ (11951, 2) :: (1, 1) :: repeat (1, 2) 100592 ++ (438888, 2) :: (1, 1) :: repeat (1, 2) 1511339 ++ (5653179, 2) :: (1, 1) :: repeat (1, 2) 11874956 ++ w) 1).
  }
  (* step 275: sTUP *)
  apply (hsteps_trans _ (HC [] 3 3 2 ((8, 2) :: (34, 2) :: (1, 1) :: repeat (1, 2) 74 ++ (931, 2) :: (1, 1) :: repeat (1, 2) 2284 ++ (5187, 2) :: (1, 1) :: repeat (1, 2) 23909 ++ (11951, 2) :: (1, 1) :: repeat (1, 2) 100592 ++ (438888, 2) :: (1, 1) :: repeat (1, 2) 1511339 ++ (5653179, 2) :: (1, 1) :: repeat (1, 2) 11874956 ++ w) 1)).
  {
    replace ((8, 2) :: (34, 2) :: (1, 1) :: repeat (1, 2) 74 ++ (931, 2) :: (1, 1) :: repeat (1, 2) 2284 ++ (5187, 2) :: (1, 1) :: repeat (1, 2) 23909 ++ (11951, 2) :: (1, 1) :: repeat (1, 2) 100592 ++ (438888, 2) :: (1, 1) :: repeat (1, 2) 1511339 ++ (5653179, 2) :: (1, 1) :: repeat (1, 2) 11874956 ++ w) with ((10 - 2, 2) :: (34, 2) :: (1, 1) :: repeat (1, 2) 74 ++ (931, 2) :: (1, 1) :: repeat (1, 2) 2284 ++ (5187, 2) :: (1, 1) :: repeat (1, 2) 23909 ++ (11951, 2) :: (1, 1) :: repeat (1, 2) 100592 ++ (438888, 2) :: (1, 1) :: repeat (1, 2) 1511339 ++ (5653179, 2) :: (1, 1) :: repeat (1, 2) 11874956 ++ w) by sec_eq.
    apply (sTUP [] 3 4 10 2 ((34, 2) :: (1, 1) :: repeat (1, 2) 74 ++ (931, 2) :: (1, 1) :: repeat (1, 2) 2284 ++ (5187, 2) :: (1, 1) :: repeat (1, 2) 23909 ++ (11951, 2) :: (1, 1) :: repeat (1, 2) 100592 ++ (438888, 2) :: (1, 1) :: repeat (1, 2) 1511339 ++ (5653179, 2) :: (1, 1) :: repeat (1, 2) 11874956 ++ w) 1); closearith.
  }
  (* step 276: DIPGRIND 3 2 *)
  apply (hsteps_trans _ (HC [] 0 3 2 (repeat (1, 2) 3 ++ (2, 2) :: (34, 2) :: (1, 1) :: repeat (1, 2) 74 ++ (931, 2) :: (1, 1) :: repeat (1, 2) 2284 ++ (5187, 2) :: (1, 1) :: repeat (1, 2) 23909 ++ (11951, 2) :: (1, 1) :: repeat (1, 2) 100592 ++ (438888, 2) :: (1, 1) :: repeat (1, 2) 1511339 ++ (5653179, 2) :: (1, 1) :: repeat (1, 2) 11874956 ++ w) 1)).
  {
    apply (DIPGRIND 3 2 [] ((34, 2) :: (1, 1) :: repeat (1, 2) 74 ++ (931, 2) :: (1, 1) :: repeat (1, 2) 2284 ++ (5187, 2) :: (1, 1) :: repeat (1, 2) 23909 ++ (11951, 2) :: (1, 1) :: repeat (1, 2) 100592 ++ (438888, 2) :: (1, 1) :: repeat (1, 2) 1511339 ++ (5653179, 2) :: (1, 1) :: repeat (1, 2) 11874956 ++ w) 1); closearith.
  }
  (* step 277: P PUSHX *)
  apply (hsteps_trans _ (HB [] 1 1 7 (repeat (1, 2) 3 ++ (2, 2) :: (34, 2) :: (1, 1) :: repeat (1, 2) 74 ++ (931, 2) :: (1, 1) :: repeat (1, 2) 2284 ++ (5187, 2) :: (1, 1) :: repeat (1, 2) 23909 ++ (11951, 2) :: (1, 1) :: repeat (1, 2) 100592 ++ (438888, 2) :: (1, 1) :: repeat (1, 2) 1511339 ++ (5653179, 2) :: (1, 1) :: repeat (1, 2) 11874956 ++ w) 1)).
  {
    exact (hsteps_step _ _ _ (hPUSHX (repeat (1, 2) 3 ++ (2, 2) :: (34, 2) :: (1, 1) :: repeat (1, 2) 74 ++ (931, 2) :: (1, 1) :: repeat (1, 2) 2284 ++ (5187, 2) :: (1, 1) :: repeat (1, 2) 23909 ++ (11951, 2) :: (1, 1) :: repeat (1, 2) 100592 ++ (438888, 2) :: (1, 1) :: repeat (1, 2) 1511339 ++ (5653179, 2) :: (1, 1) :: repeat (1, 2) 11874956 ++ w) 1) (hsteps_refl _)).
  }
  (* step 278: M pop12 (3,) *)
  apply (hsteps_trans _ (HB [] 4 1 13 ((2, 2) :: (34, 2) :: (1, 1) :: repeat (1, 2) 74 ++ (931, 2) :: (1, 1) :: repeat (1, 2) 2284 ++ (5187, 2) :: (1, 1) :: repeat (1, 2) 23909 ++ (11951, 2) :: (1, 1) :: repeat (1, 2) 100592 ++ (438888, 2) :: (1, 1) :: repeat (1, 2) 1511339 ++ (5653179, 2) :: (1, 1) :: repeat (1, 2) 11874956 ++ w) 1)).
  {
    apply (pop12 3 [] 1 7 ((2, 2) :: (34, 2) :: (1, 1) :: repeat (1, 2) 74 ++ (931, 2) :: (1, 1) :: repeat (1, 2) 2284 ++ (5187, 2) :: (1, 1) :: repeat (1, 2) 23909 ++ (11951, 2) :: (1, 1) :: repeat (1, 2) 100592 ++ (438888, 2) :: (1, 1) :: repeat (1, 2) 1511339 ++ (5653179, 2) :: (1, 1) :: repeat (1, 2) 11874956 ++ w) 1); closearith.
  }
  (* step 279: P TUP2_1 *)
  apply (hsteps_trans _ (HC [5] 13 1 2 ((32, 2) :: (1, 1) :: repeat (1, 2) 74 ++ (931, 2) :: (1, 1) :: repeat (1, 2) 2284 ++ (5187, 2) :: (1, 1) :: repeat (1, 2) 23909 ++ (11951, 2) :: (1, 1) :: repeat (1, 2) 100592 ++ (438888, 2) :: (1, 1) :: repeat (1, 2) 1511339 ++ (5653179, 2) :: (1, 1) :: repeat (1, 2) 11874956 ++ w) 1)).
  {
    replace ((32, 2) :: (1, 1) :: repeat (1, 2) 74 ++ (931, 2) :: (1, 1) :: repeat (1, 2) 2284 ++ (5187, 2) :: (1, 1) :: repeat (1, 2) 23909 ++ (11951, 2) :: (1, 1) :: repeat (1, 2) 100592 ++ (438888, 2) :: (1, 1) :: repeat (1, 2) 1511339 ++ (5653179, 2) :: (1, 1) :: repeat (1, 2) 11874956 ++ w) with ((34 - 2, 2) :: (1, 1) :: repeat (1, 2) 74 ++ (931, 2) :: (1, 1) :: repeat (1, 2) 2284 ++ (5187, 2) :: (1, 1) :: repeat (1, 2) 23909 ++ (11951, 2) :: (1, 1) :: repeat (1, 2) 100592 ++ (438888, 2) :: (1, 1) :: repeat (1, 2) 1511339 ++ (5653179, 2) :: (1, 1) :: repeat (1, 2) 11874956 ++ w) by sec_eq.
    apply (sTUP2_1 [] 4 12 34 ((1, 1) :: repeat (1, 2) 74 ++ (931, 2) :: (1, 1) :: repeat (1, 2) 2284 ++ (5187, 2) :: (1, 1) :: repeat (1, 2) 23909 ++ (11951, 2) :: (1, 1) :: repeat (1, 2) 100592 ++ (438888, 2) :: (1, 1) :: repeat (1, 2) 1511339 ++ (5653179, 2) :: (1, 1) :: repeat (1, 2) 11874956 ++ w) 1); closearith.
  }
  (* step 280: P TDN *)
  apply (sTDN [5] 13 ((32, 2) :: (1, 1) :: repeat (1, 2) 74 ++ (931, 2) :: (1, 1) :: repeat (1, 2) 2284 ++ (5187, 2) :: (1, 1) :: repeat (1, 2) 23909 ++ (11951, 2) :: (1, 1) :: repeat (1, 2) 100592 ++ (438888, 2) :: (1, 1) :: repeat (1, 2) 1511339 ++ (5653179, 2) :: (1, 1) :: repeat (1, 2) 11874956 ++ w) 1).
Qed.

(* CASCADE58f: steps 281-336 of the CASCADE58 chain. *)
Lemma CASCADE58f : forall w,
  hsteps (HB [5] 13 1 4 ((32, 2) :: (1, 1) :: repeat (1, 2) 74 ++ (931, 2) :: (1, 1) :: repeat (1, 2) 2284 ++ (5187, 2) :: (1, 1) :: repeat (1, 2) 23909 ++ (11951, 2) :: (1, 1) :: repeat (1, 2) 100592 ++ (438888, 2) :: (1, 1) :: repeat (1, 2) 1511339 ++ (5653179, 2) :: (1, 1) :: repeat (1, 2) 11874956 ++ w) 1)
         (HC [226; 40; 14; 5] 2596 5194 2 ((5185, 2) :: (1, 1) :: repeat (1, 2) 23909 ++ (11951, 2) :: (1, 1) :: repeat (1, 2) 100592 ++ (438888, 2) :: (1, 1) :: repeat (1, 2) 1511339 ++ (5653179, 2) :: (1, 1) :: repeat (1, 2) 11874956 ++ w) 1).
Proof.
  intro w.
  (* step 281: sTUP *)
  apply (hsteps_trans _ (HC [5] 13 3 2 ((30, 2) :: (1, 1) :: repeat (1, 2) 74 ++ (931, 2) :: (1, 1) :: repeat (1, 2) 2284 ++ (5187, 2) :: (1, 1) :: repeat (1, 2) 23909 ++ (11951, 2) :: (1, 1) :: repeat (1, 2) 100592 ++ (438888, 2) :: (1, 1) :: repeat (1, 2) 1511339 ++ (5653179, 2) :: (1, 1) :: repeat (1, 2) 11874956 ++ w) 1)).
  {
    replace ((30, 2) :: (1, 1) :: repeat (1, 2) 74 ++ (931, 2) :: (1, 1) :: repeat (1, 2) 2284 ++ (5187, 2) :: (1, 1) :: repeat (1, 2) 23909 ++ (11951, 2) :: (1, 1) :: repeat (1, 2) 100592 ++ (438888, 2) :: (1, 1) :: repeat (1, 2) 1511339 ++ (5653179, 2) :: (1, 1) :: repeat (1, 2) 11874956 ++ w) with ((32 - 2, 2) :: (1, 1) :: repeat (1, 2) 74 ++ (931, 2) :: (1, 1) :: repeat (1, 2) 2284 ++ (5187, 2) :: (1, 1) :: repeat (1, 2) 23909 ++ (11951, 2) :: (1, 1) :: repeat (1, 2) 100592 ++ (438888, 2) :: (1, 1) :: repeat (1, 2) 1511339 ++ (5653179, 2) :: (1, 1) :: repeat (1, 2) 11874956 ++ w) by sec_eq.
    apply (sTUP [5] 13 4 32 2 ((1, 1) :: repeat (1, 2) 74 ++ (931, 2) :: (1, 1) :: repeat (1, 2) 2284 ++ (5187, 2) :: (1, 1) :: repeat (1, 2) 23909 ++ (11951, 2) :: (1, 1) :: repeat (1, 2) 100592 ++ (438888, 2) :: (1, 1) :: repeat (1, 2) 1511339 ++ (5653179, 2) :: (1, 1) :: repeat (1, 2) 11874956 ++ w) 1); closearith.
  }
  (* step 282: DIPGRIND 13 4 *)
  apply (hsteps_trans _ (HC [5] 0 3 2 (repeat (1, 2) 13 ++ (4, 2) :: (1, 1) :: repeat (1, 2) 74 ++ (931, 2) :: (1, 1) :: repeat (1, 2) 2284 ++ (5187, 2) :: (1, 1) :: repeat (1, 2) 23909 ++ (11951, 2) :: (1, 1) :: repeat (1, 2) 100592 ++ (438888, 2) :: (1, 1) :: repeat (1, 2) 1511339 ++ (5653179, 2) :: (1, 1) :: repeat (1, 2) 11874956 ++ w) 1)).
  {
    apply (DIPGRIND 13 4 [5] ((1, 1) :: repeat (1, 2) 74 ++ (931, 2) :: (1, 1) :: repeat (1, 2) 2284 ++ (5187, 2) :: (1, 1) :: repeat (1, 2) 23909 ++ (11951, 2) :: (1, 1) :: repeat (1, 2) 100592 ++ (438888, 2) :: (1, 1) :: repeat (1, 2) 1511339 ++ (5653179, 2) :: (1, 1) :: repeat (1, 2) 11874956 ++ w) 1); closearith.
  }
  (* step 283: P PX2Bgen *)
  apply (hsteps_trans _ (HB [0] 3 1 2 (repeat (1, 2) 1 ++ (1, 1) :: repeat (1, 2) 15 ++ (4, 2) :: (1, 1) :: repeat (1, 2) 74 ++ (931, 2) :: (1, 1) :: repeat (1, 2) 2284 ++ (5187, 2) :: (1, 1) :: repeat (1, 2) 23909 ++ (11951, 2) :: (1, 1) :: repeat (1, 2) 100592 ++ (438888, 2) :: (1, 1) :: repeat (1, 2) 1511339 ++ (5653179, 2) :: (1, 1) :: repeat (1, 2) 11874956 ++ w) 1)).
  {
    exact (hsteps_step _ _ _ (hPX2Bgen 0 (repeat (1, 2) 13 ++ (4, 2) :: (1, 1) :: repeat (1, 2) 74 ++ (931, 2) :: (1, 1) :: repeat (1, 2) 2284 ++ (5187, 2) :: (1, 1) :: repeat (1, 2) 23909 ++ (11951, 2) :: (1, 1) :: repeat (1, 2) 100592 ++ (438888, 2) :: (1, 1) :: repeat (1, 2) 1511339 ++ (5653179, 2) :: (1, 1) :: repeat (1, 2) 11874956 ++ w) 1) (hsteps_refl _)).
  }
  (* step 284: M pop12 (1,) *)
  apply (hsteps_trans _ (HB [0] 4 1 4 ((1, 1) :: repeat (1, 2) 15 ++ (4, 2) :: (1, 1) :: repeat (1, 2) 74 ++ (931, 2) :: (1, 1) :: repeat (1, 2) 2284 ++ (5187, 2) :: (1, 1) :: repeat (1, 2) 23909 ++ (11951, 2) :: (1, 1) :: repeat (1, 2) 100592 ++ (438888, 2) :: (1, 1) :: repeat (1, 2) 1511339 ++ (5653179, 2) :: (1, 1) :: repeat (1, 2) 11874956 ++ w) 1)).
  {
    apply (pop12 1 [0] 3 2 ((1, 1) :: repeat (1, 2) 15 ++ (4, 2) :: (1, 1) :: repeat (1, 2) 74 ++ (931, 2) :: (1, 1) :: repeat (1, 2) 2284 ++ (5187, 2) :: (1, 1) :: repeat (1, 2) 23909 ++ (11951, 2) :: (1, 1) :: repeat (1, 2) 100592 ++ (438888, 2) :: (1, 1) :: repeat (1, 2) 1511339 ++ (5653179, 2) :: (1, 1) :: repeat (1, 2) 11874956 ++ w) 1); closearith.
  }
  (* step 285: P POP *)
  apply (hsteps_trans _ (HB [0] 5 1 5 (repeat (1, 2) 15 ++ (4, 2) :: (1, 1) :: repeat (1, 2) 74 ++ (931, 2) :: (1, 1) :: repeat (1, 2) 2284 ++ (5187, 2) :: (1, 1) :: repeat (1, 2) 23909 ++ (11951, 2) :: (1, 1) :: repeat (1, 2) 100592 ++ (438888, 2) :: (1, 1) :: repeat (1, 2) 1511339 ++ (5653179, 2) :: (1, 1) :: repeat (1, 2) 11874956 ++ w) 1)).
  {
    apply (sPOP1 [0] 4 4 (repeat (1, 2) 15 ++ (4, 2) :: (1, 1) :: repeat (1, 2) 74 ++ (931, 2) :: (1, 1) :: repeat (1, 2) 2284 ++ (5187, 2) :: (1, 1) :: repeat (1, 2) 23909 ++ (11951, 2) :: (1, 1) :: repeat (1, 2) 100592 ++ (438888, 2) :: (1, 1) :: repeat (1, 2) 1511339 ++ (5653179, 2) :: (1, 1) :: repeat (1, 2) 11874956 ++ w) 1); closearith.
  }
  (* step 286: M pop12 (15,) *)
  apply (hsteps_trans _ (HB [0] 20 1 35 ((4, 2) :: (1, 1) :: repeat (1, 2) 74 ++ (931, 2) :: (1, 1) :: repeat (1, 2) 2284 ++ (5187, 2) :: (1, 1) :: repeat (1, 2) 23909 ++ (11951, 2) :: (1, 1) :: repeat (1, 2) 100592 ++ (438888, 2) :: (1, 1) :: repeat (1, 2) 1511339 ++ (5653179, 2) :: (1, 1) :: repeat (1, 2) 11874956 ++ w) 1)).
  {
    apply (pop12 15 [0] 5 5 ((4, 2) :: (1, 1) :: repeat (1, 2) 74 ++ (931, 2) :: (1, 1) :: repeat (1, 2) 2284 ++ (5187, 2) :: (1, 1) :: repeat (1, 2) 23909 ++ (11951, 2) :: (1, 1) :: repeat (1, 2) 100592 ++ (438888, 2) :: (1, 1) :: repeat (1, 2) 1511339 ++ (5653179, 2) :: (1, 1) :: repeat (1, 2) 11874956 ++ w) 1); closearith.
  }
  (* step 287: sTUP *)
  apply (hsteps_trans _ (HC [0] 20 34 2 ((2, 2) :: (1, 1) :: repeat (1, 2) 74 ++ (931, 2) :: (1, 1) :: repeat (1, 2) 2284 ++ (5187, 2) :: (1, 1) :: repeat (1, 2) 23909 ++ (11951, 2) :: (1, 1) :: repeat (1, 2) 100592 ++ (438888, 2) :: (1, 1) :: repeat (1, 2) 1511339 ++ (5653179, 2) :: (1, 1) :: repeat (1, 2) 11874956 ++ w) 1)).
  {
    replace ((2, 2) :: (1, 1) :: repeat (1, 2) 74 ++ (931, 2) :: (1, 1) :: repeat (1, 2) 2284 ++ (5187, 2) :: (1, 1) :: repeat (1, 2) 23909 ++ (11951, 2) :: (1, 1) :: repeat (1, 2) 100592 ++ (438888, 2) :: (1, 1) :: repeat (1, 2) 1511339 ++ (5653179, 2) :: (1, 1) :: repeat (1, 2) 11874956 ++ w) with ((4 - 2, 2) :: (1, 1) :: repeat (1, 2) 74 ++ (931, 2) :: (1, 1) :: repeat (1, 2) 2284 ++ (5187, 2) :: (1, 1) :: repeat (1, 2) 23909 ++ (11951, 2) :: (1, 1) :: repeat (1, 2) 100592 ++ (438888, 2) :: (1, 1) :: repeat (1, 2) 1511339 ++ (5653179, 2) :: (1, 1) :: repeat (1, 2) 11874956 ++ w) by sec_eq.
    apply (sTUP [0] 20 35 4 2 ((1, 1) :: repeat (1, 2) 74 ++ (931, 2) :: (1, 1) :: repeat (1, 2) 2284 ++ (5187, 2) :: (1, 1) :: repeat (1, 2) 23909 ++ (11951, 2) :: (1, 1) :: repeat (1, 2) 100592 ++ (438888, 2) :: (1, 1) :: repeat (1, 2) 1511339 ++ (5653179, 2) :: (1, 1) :: repeat (1, 2) 11874956 ++ w) 1); closearith.
  }
  (* step 288: hGRIND_even 15 *)
  apply (hsteps_trans _ (HB [0] 19 1 34 ((2, 2) :: (2, 2) :: (1, 1) :: repeat (1, 2) 74 ++ (931, 2) :: (1, 1) :: repeat (1, 2) 2284 ++ (5187, 2) :: (1, 1) :: repeat (1, 2) 23909 ++ (11951, 2) :: (1, 1) :: repeat (1, 2) 100592 ++ (438888, 2) :: (1, 1) :: repeat (1, 2) 1511339 ++ (5653179, 2) :: (1, 1) :: repeat (1, 2) 11874956 ++ w) 1)).
  {
    apply (hGRIND_even 15 [0] 19 ((2, 2) :: (1, 1) :: repeat (1, 2) 74 ++ (931, 2) :: (1, 1) :: repeat (1, 2) 2284 ++ (5187, 2) :: (1, 1) :: repeat (1, 2) 23909 ++ (11951, 2) :: (1, 1) :: repeat (1, 2) 100592 ++ (438888, 2) :: (1, 1) :: repeat (1, 2) 1511339 ++ (5653179, 2) :: (1, 1) :: repeat (1, 2) 11874956 ++ w) 1); closearith.
  }
  (* step 289: P TRANS2_2 *)
  apply (hsteps_trans _ (HB [35; 20; 0] 3 1 3 (repeat (1, 2) 74 ++ (931, 2) :: (1, 1) :: repeat (1, 2) 2284 ++ (5187, 2) :: (1, 1) :: repeat (1, 2) 23909 ++ (11951, 2) :: (1, 1) :: repeat (1, 2) 100592 ++ (438888, 2) :: (1, 1) :: repeat (1, 2) 1511339 ++ (5653179, 2) :: (1, 1) :: repeat (1, 2) 11874956 ++ w) 1)).
  {
    apply (hsteps_step _ (HB [35; 20; 0] 3 1 3 (repeat (1, 2) 74 ++ (931, 2) :: (1, 1) :: repeat (1, 2) 2284 ++ (5187, 2) :: (1, 1) :: repeat (1, 2) 23909 ++ (11951, 2) :: (1, 1) :: repeat (1, 2) 100592 ++ (438888, 2) :: (1, 1) :: repeat (1, 2) 1511339 ++ (5653179, 2) :: (1, 1) :: repeat (1, 2) 11874956 ++ w) 1)); [apply hTRANS2_2; closearith | apply hsteps_refl].
  }
  (* step 290: M pop12 (74,) *)
  apply (hsteps_trans _ (HB [35; 20; 0] 77 1 151 ((931, 2) :: (1, 1) :: repeat (1, 2) 2284 ++ (5187, 2) :: (1, 1) :: repeat (1, 2) 23909 ++ (11951, 2) :: (1, 1) :: repeat (1, 2) 100592 ++ (438888, 2) :: (1, 1) :: repeat (1, 2) 1511339 ++ (5653179, 2) :: (1, 1) :: repeat (1, 2) 11874956 ++ w) 1)).
  {
    apply (pop12 74 [35; 20; 0] 3 3 ((931, 2) :: (1, 1) :: repeat (1, 2) 2284 ++ (5187, 2) :: (1, 1) :: repeat (1, 2) 23909 ++ (11951, 2) :: (1, 1) :: repeat (1, 2) 100592 ++ (438888, 2) :: (1, 1) :: repeat (1, 2) 1511339 ++ (5653179, 2) :: (1, 1) :: repeat (1, 2) 11874956 ++ w) 1); closearith.
  }
  (* step 291: sTUP *)
  apply (hsteps_trans _ (HC [35; 20; 0] 77 150 2 ((929, 2) :: (1, 1) :: repeat (1, 2) 2284 ++ (5187, 2) :: (1, 1) :: repeat (1, 2) 23909 ++ (11951, 2) :: (1, 1) :: repeat (1, 2) 100592 ++ (438888, 2) :: (1, 1) :: repeat (1, 2) 1511339 ++ (5653179, 2) :: (1, 1) :: repeat (1, 2) 11874956 ++ w) 1)).
  {
    replace ((929, 2) :: (1, 1) :: repeat (1, 2) 2284 ++ (5187, 2) :: (1, 1) :: repeat (1, 2) 23909 ++ (11951, 2) :: (1, 1) :: repeat (1, 2) 100592 ++ (438888, 2) :: (1, 1) :: repeat (1, 2) 1511339 ++ (5653179, 2) :: (1, 1) :: repeat (1, 2) 11874956 ++ w) with ((931 - 2, 2) :: (1, 1) :: repeat (1, 2) 2284 ++ (5187, 2) :: (1, 1) :: repeat (1, 2) 23909 ++ (11951, 2) :: (1, 1) :: repeat (1, 2) 100592 ++ (438888, 2) :: (1, 1) :: repeat (1, 2) 1511339 ++ (5653179, 2) :: (1, 1) :: repeat (1, 2) 11874956 ++ w) by sec_eq.
    apply (sTUP [35; 20; 0] 77 151 931 2 ((1, 1) :: repeat (1, 2) 2284 ++ (5187, 2) :: (1, 1) :: repeat (1, 2) 23909 ++ (11951, 2) :: (1, 1) :: repeat (1, 2) 100592 ++ (438888, 2) :: (1, 1) :: repeat (1, 2) 1511339 ++ (5653179, 2) :: (1, 1) :: repeat (1, 2) 11874956 ++ w) 1); closearith.
  }
  (* step 292: hGRIND_even 73 *)
  apply (hsteps_trans _ (HB [35; 20; 0] 76 1 150 ((2, 2) :: (929, 2) :: (1, 1) :: repeat (1, 2) 2284 ++ (5187, 2) :: (1, 1) :: repeat (1, 2) 23909 ++ (11951, 2) :: (1, 1) :: repeat (1, 2) 100592 ++ (438888, 2) :: (1, 1) :: repeat (1, 2) 1511339 ++ (5653179, 2) :: (1, 1) :: repeat (1, 2) 11874956 ++ w) 1)).
  {
    apply (hGRIND_even 73 [35; 20; 0] 76 ((929, 2) :: (1, 1) :: repeat (1, 2) 2284 ++ (5187, 2) :: (1, 1) :: repeat (1, 2) 23909 ++ (11951, 2) :: (1, 1) :: repeat (1, 2) 100592 ++ (438888, 2) :: (1, 1) :: repeat (1, 2) 1511339 ++ (5653179, 2) :: (1, 1) :: repeat (1, 2) 11874956 ++ w) 1); closearith.
  }
  (* step 293: P TUP2_1 *)
  apply (hsteps_trans _ (HC [77; 35; 20; 0] 150 1 2 ((927, 2) :: (1, 1) :: repeat (1, 2) 2284 ++ (5187, 2) :: (1, 1) :: repeat (1, 2) 23909 ++ (11951, 2) :: (1, 1) :: repeat (1, 2) 100592 ++ (438888, 2) :: (1, 1) :: repeat (1, 2) 1511339 ++ (5653179, 2) :: (1, 1) :: repeat (1, 2) 11874956 ++ w) 1)).
  {
    replace ((927, 2) :: (1, 1) :: repeat (1, 2) 2284 ++ (5187, 2) :: (1, 1) :: repeat (1, 2) 23909 ++ (11951, 2) :: (1, 1) :: repeat (1, 2) 100592 ++ (438888, 2) :: (1, 1) :: repeat (1, 2) 1511339 ++ (5653179, 2) :: (1, 1) :: repeat (1, 2) 11874956 ++ w) with ((929 - 2, 2) :: (1, 1) :: repeat (1, 2) 2284 ++ (5187, 2) :: (1, 1) :: repeat (1, 2) 23909 ++ (11951, 2) :: (1, 1) :: repeat (1, 2) 100592 ++ (438888, 2) :: (1, 1) :: repeat (1, 2) 1511339 ++ (5653179, 2) :: (1, 1) :: repeat (1, 2) 11874956 ++ w) by sec_eq.
    apply (sTUP2_1 [35; 20; 0] 76 149 929 ((1, 1) :: repeat (1, 2) 2284 ++ (5187, 2) :: (1, 1) :: repeat (1, 2) 23909 ++ (11951, 2) :: (1, 1) :: repeat (1, 2) 100592 ++ (438888, 2) :: (1, 1) :: repeat (1, 2) 1511339 ++ (5653179, 2) :: (1, 1) :: repeat (1, 2) 11874956 ++ w) 1); closearith.
  }
  (* step 294: P TDN *)
  apply (hsteps_trans _ (HB [77; 35; 20; 0] 150 1 4 ((927, 2) :: (1, 1) :: repeat (1, 2) 2284 ++ (5187, 2) :: (1, 1) :: repeat (1, 2) 23909 ++ (11951, 2) :: (1, 1) :: repeat (1, 2) 100592 ++ (438888, 2) :: (1, 1) :: repeat (1, 2) 1511339 ++ (5653179, 2) :: (1, 1) :: repeat (1, 2) 11874956 ++ w) 1)).
  {
    apply (sTDN [77; 35; 20; 0] 150 ((927, 2) :: (1, 1) :: repeat (1, 2) 2284 ++ (5187, 2) :: (1, 1) :: repeat (1, 2) 23909 ++ (11951, 2) :: (1, 1) :: repeat (1, 2) 100592 ++ (438888, 2) :: (1, 1) :: repeat (1, 2) 1511339 ++ (5653179, 2) :: (1, 1) :: repeat (1, 2) 11874956 ++ w) 1).
  }
  (* step 295: sTUP *)
  apply (hsteps_trans _ (HC [77; 35; 20; 0] 150 3 2 ((925, 2) :: (1, 1) :: repeat (1, 2) 2284 ++ (5187, 2) :: (1, 1) :: repeat (1, 2) 23909 ++ (11951, 2) :: (1, 1) :: repeat (1, 2) 100592 ++ (438888, 2) :: (1, 1) :: repeat (1, 2) 1511339 ++ (5653179, 2) :: (1, 1) :: repeat (1, 2) 11874956 ++ w) 1)).
  {
    replace ((925, 2) :: (1, 1) :: repeat (1, 2) 2284 ++ (5187, 2) :: (1, 1) :: repeat (1, 2) 23909 ++ (11951, 2) :: (1, 1) :: repeat (1, 2) 100592 ++ (438888, 2) :: (1, 1) :: repeat (1, 2) 1511339 ++ (5653179, 2) :: (1, 1) :: repeat (1, 2) 11874956 ++ w) with ((927 - 2, 2) :: (1, 1) :: repeat (1, 2) 2284 ++ (5187, 2) :: (1, 1) :: repeat (1, 2) 23909 ++ (11951, 2) :: (1, 1) :: repeat (1, 2) 100592 ++ (438888, 2) :: (1, 1) :: repeat (1, 2) 1511339 ++ (5653179, 2) :: (1, 1) :: repeat (1, 2) 11874956 ++ w) by sec_eq.
    apply (sTUP [77; 35; 20; 0] 150 4 927 2 ((1, 1) :: repeat (1, 2) 2284 ++ (5187, 2) :: (1, 1) :: repeat (1, 2) 23909 ++ (11951, 2) :: (1, 1) :: repeat (1, 2) 100592 ++ (438888, 2) :: (1, 1) :: repeat (1, 2) 1511339 ++ (5653179, 2) :: (1, 1) :: repeat (1, 2) 11874956 ++ w) 1); closearith.
  }
  (* step 296: DIPGRIND 150 625 *)
  apply (hsteps_trans _ (HC [77; 35; 20; 0] 0 3 2 (repeat (1, 2) 150 ++ (625, 2) :: (1, 1) :: repeat (1, 2) 2284 ++ (5187, 2) :: (1, 1) :: repeat (1, 2) 23909 ++ (11951, 2) :: (1, 1) :: repeat (1, 2) 100592 ++ (438888, 2) :: (1, 1) :: repeat (1, 2) 1511339 ++ (5653179, 2) :: (1, 1) :: repeat (1, 2) 11874956 ++ w) 1)).
  {
    apply (DIPGRIND 150 625 [77; 35; 20; 0] ((1, 1) :: repeat (1, 2) 2284 ++ (5187, 2) :: (1, 1) :: repeat (1, 2) 23909 ++ (11951, 2) :: (1, 1) :: repeat (1, 2) 100592 ++ (438888, 2) :: (1, 1) :: repeat (1, 2) 1511339 ++ (5653179, 2) :: (1, 1) :: repeat (1, 2) 11874956 ++ w) 1); closearith.
  }
  (* step 297: P PX2A *)
  apply (hsteps_trans _ (HC [20; 0] 34 75 2 ((1, 1) :: repeat (1, 2) 152 ++ (625, 2) :: (1, 1) :: repeat (1, 2) 2284 ++ (5187, 2) :: (1, 1) :: repeat (1, 2) 23909 ++ (11951, 2) :: (1, 1) :: repeat (1, 2) 100592 ++ (438888, 2) :: (1, 1) :: repeat (1, 2) 1511339 ++ (5653179, 2) :: (1, 1) :: repeat (1, 2) 11874956 ++ w) 1)).
  {
    exact (hsteps_step _ _ _ (hPX2A 74 34 [20; 0] (repeat (1, 2) 150 ++ (625, 2) :: (1, 1) :: repeat (1, 2) 2284 ++ (5187, 2) :: (1, 1) :: repeat (1, 2) 23909 ++ (11951, 2) :: (1, 1) :: repeat (1, 2) 100592 ++ (438888, 2) :: (1, 1) :: repeat (1, 2) 1511339 ++ (5653179, 2) :: (1, 1) :: repeat (1, 2) 11874956 ++ w) 1) (hsteps_refl _)).
  }
  (* step 298: P PUSH *)
  apply (hsteps_trans _ (HC [20; 0] 33 1 2 ((73, 2) :: (1, 1) :: repeat (1, 2) 152 ++ (625, 2) :: (1, 1) :: repeat (1, 2) 2284 ++ (5187, 2) :: (1, 1) :: repeat (1, 2) 23909 ++ (11951, 2) :: (1, 1) :: repeat (1, 2) 100592 ++ (438888, 2) :: (1, 1) :: repeat (1, 2) 1511339 ++ (5653179, 2) :: (1, 1) :: repeat (1, 2) 11874956 ++ w) 1)).
  {
    replace ((73, 2) :: (1, 1) :: repeat (1, 2) 152 ++ (625, 2) :: (1, 1) :: repeat (1, 2) 2284 ++ (5187, 2) :: (1, 1) :: repeat (1, 2) 23909 ++ (11951, 2) :: (1, 1) :: repeat (1, 2) 100592 ++ (438888, 2) :: (1, 1) :: repeat (1, 2) 1511339 ++ (5653179, 2) :: (1, 1) :: repeat (1, 2) 11874956 ++ w) with ((75 - 2, 2) :: (1, 1) :: repeat (1, 2) 152 ++ (625, 2) :: (1, 1) :: repeat (1, 2) 2284 ++ (5187, 2) :: (1, 1) :: repeat (1, 2) 23909 ++ (11951, 2) :: (1, 1) :: repeat (1, 2) 100592 ++ (438888, 2) :: (1, 1) :: repeat (1, 2) 1511339 ++ (5653179, 2) :: (1, 1) :: repeat (1, 2) 11874956 ++ w) by sec_eq.
    apply (sPUSH [20; 0] 33 75 ((1, 1) :: repeat (1, 2) 152 ++ (625, 2) :: (1, 1) :: repeat (1, 2) 2284 ++ (5187, 2) :: (1, 1) :: repeat (1, 2) 23909 ++ (11951, 2) :: (1, 1) :: repeat (1, 2) 100592 ++ (438888, 2) :: (1, 1) :: repeat (1, 2) 1511339 ++ (5653179, 2) :: (1, 1) :: repeat (1, 2) 11874956 ++ w) 1); closearith.
  }
  (* step 299: P TDN *)
  apply (hsteps_trans _ (HB [20; 0] 33 1 4 ((73, 2) :: (1, 1) :: repeat (1, 2) 152 ++ (625, 2) :: (1, 1) :: repeat (1, 2) 2284 ++ (5187, 2) :: (1, 1) :: repeat (1, 2) 23909 ++ (11951, 2) :: (1, 1) :: repeat (1, 2) 100592 ++ (438888, 2) :: (1, 1) :: repeat (1, 2) 1511339 ++ (5653179, 2) :: (1, 1) :: repeat (1, 2) 11874956 ++ w) 1)).
  {
    apply (sTDN [20; 0] 33 ((73, 2) :: (1, 1) :: repeat (1, 2) 152 ++ (625, 2) :: (1, 1) :: repeat (1, 2) 2284 ++ (5187, 2) :: (1, 1) :: repeat (1, 2) 23909 ++ (11951, 2) :: (1, 1) :: repeat (1, 2) 100592 ++ (438888, 2) :: (1, 1) :: repeat (1, 2) 1511339 ++ (5653179, 2) :: (1, 1) :: repeat (1, 2) 11874956 ++ w) 1).
  }
  (* step 300: sTUP *)
  apply (hsteps_trans _ (HC [20; 0] 33 3 2 ((71, 2) :: (1, 1) :: repeat (1, 2) 152 ++ (625, 2) :: (1, 1) :: repeat (1, 2) 2284 ++ (5187, 2) :: (1, 1) :: repeat (1, 2) 23909 ++ (11951, 2) :: (1, 1) :: repeat (1, 2) 100592 ++ (438888, 2) :: (1, 1) :: repeat (1, 2) 1511339 ++ (5653179, 2) :: (1, 1) :: repeat (1, 2) 11874956 ++ w) 1)).
  {
    replace ((71, 2) :: (1, 1) :: repeat (1, 2) 152 ++ (625, 2) :: (1, 1) :: repeat (1, 2) 2284 ++ (5187, 2) :: (1, 1) :: repeat (1, 2) 23909 ++ (11951, 2) :: (1, 1) :: repeat (1, 2) 100592 ++ (438888, 2) :: (1, 1) :: repeat (1, 2) 1511339 ++ (5653179, 2) :: (1, 1) :: repeat (1, 2) 11874956 ++ w) with ((73 - 2, 2) :: (1, 1) :: repeat (1, 2) 152 ++ (625, 2) :: (1, 1) :: repeat (1, 2) 2284 ++ (5187, 2) :: (1, 1) :: repeat (1, 2) 23909 ++ (11951, 2) :: (1, 1) :: repeat (1, 2) 100592 ++ (438888, 2) :: (1, 1) :: repeat (1, 2) 1511339 ++ (5653179, 2) :: (1, 1) :: repeat (1, 2) 11874956 ++ w) by sec_eq.
    apply (sTUP [20; 0] 33 4 73 2 ((1, 1) :: repeat (1, 2) 152 ++ (625, 2) :: (1, 1) :: repeat (1, 2) 2284 ++ (5187, 2) :: (1, 1) :: repeat (1, 2) 23909 ++ (11951, 2) :: (1, 1) :: repeat (1, 2) 100592 ++ (438888, 2) :: (1, 1) :: repeat (1, 2) 1511339 ++ (5653179, 2) :: (1, 1) :: repeat (1, 2) 11874956 ++ w) 1); closearith.
  }
  (* step 301: DIPGRIND 33 5 *)
  apply (hsteps_trans _ (HC [20; 0] 0 3 2 (repeat (1, 2) 33 ++ (5, 2) :: (1, 1) :: repeat (1, 2) 152 ++ (625, 2) :: (1, 1) :: repeat (1, 2) 2284 ++ (5187, 2) :: (1, 1) :: repeat (1, 2) 23909 ++ (11951, 2) :: (1, 1) :: repeat (1, 2) 100592 ++ (438888, 2) :: (1, 1) :: repeat (1, 2) 1511339 ++ (5653179, 2) :: (1, 1) :: repeat (1, 2) 11874956 ++ w) 1)).
  {
    apply (DIPGRIND 33 5 [20; 0] ((1, 1) :: repeat (1, 2) 152 ++ (625, 2) :: (1, 1) :: repeat (1, 2) 2284 ++ (5187, 2) :: (1, 1) :: repeat (1, 2) 23909 ++ (11951, 2) :: (1, 1) :: repeat (1, 2) 100592 ++ (438888, 2) :: (1, 1) :: repeat (1, 2) 1511339 ++ (5653179, 2) :: (1, 1) :: repeat (1, 2) 11874956 ++ w) 1); closearith.
  }
  (* step 302: P PX2A0 *)
  apply (hsteps_trans _ (HB [0] 3 1 2 ((16, 2) :: (1, 1) :: repeat (1, 2) 35 ++ (5, 2) :: (1, 1) :: repeat (1, 2) 152 ++ (625, 2) :: (1, 1) :: repeat (1, 2) 2284 ++ (5187, 2) :: (1, 1) :: repeat (1, 2) 23909 ++ (11951, 2) :: (1, 1) :: repeat (1, 2) 100592 ++ (438888, 2) :: (1, 1) :: repeat (1, 2) 1511339 ++ (5653179, 2) :: (1, 1) :: repeat (1, 2) 11874956 ++ w) 1)).
  {
    exact (hsteps_step _ _ _ (hPX2A0 15 (repeat (1, 2) 33 ++ (5, 2) :: (1, 1) :: repeat (1, 2) 152 ++ (625, 2) :: (1, 1) :: repeat (1, 2) 2284 ++ (5187, 2) :: (1, 1) :: repeat (1, 2) 23909 ++ (11951, 2) :: (1, 1) :: repeat (1, 2) 100592 ++ (438888, 2) :: (1, 1) :: repeat (1, 2) 1511339 ++ (5653179, 2) :: (1, 1) :: repeat (1, 2) 11874956 ++ w) 1) (hsteps_refl _)).
  }
  (* step 303: sTUP *)
  apply (hsteps_trans _ (HC [0] 3 1 2 ((14, 2) :: (1, 1) :: repeat (1, 2) 35 ++ (5, 2) :: (1, 1) :: repeat (1, 2) 152 ++ (625, 2) :: (1, 1) :: repeat (1, 2) 2284 ++ (5187, 2) :: (1, 1) :: repeat (1, 2) 23909 ++ (11951, 2) :: (1, 1) :: repeat (1, 2) 100592 ++ (438888, 2) :: (1, 1) :: repeat (1, 2) 1511339 ++ (5653179, 2) :: (1, 1) :: repeat (1, 2) 11874956 ++ w) 1)).
  {
    replace ((14, 2) :: (1, 1) :: repeat (1, 2) 35 ++ (5, 2) :: (1, 1) :: repeat (1, 2) 152 ++ (625, 2) :: (1, 1) :: repeat (1, 2) 2284 ++ (5187, 2) :: (1, 1) :: repeat (1, 2) 23909 ++ (11951, 2) :: (1, 1) :: repeat (1, 2) 100592 ++ (438888, 2) :: (1, 1) :: repeat (1, 2) 1511339 ++ (5653179, 2) :: (1, 1) :: repeat (1, 2) 11874956 ++ w) with ((16 - 2, 2) :: (1, 1) :: repeat (1, 2) 35 ++ (5, 2) :: (1, 1) :: repeat (1, 2) 152 ++ (625, 2) :: (1, 1) :: repeat (1, 2) 2284 ++ (5187, 2) :: (1, 1) :: repeat (1, 2) 23909 ++ (11951, 2) :: (1, 1) :: repeat (1, 2) 100592 ++ (438888, 2) :: (1, 1) :: repeat (1, 2) 1511339 ++ (5653179, 2) :: (1, 1) :: repeat (1, 2) 11874956 ++ w) by sec_eq.
    apply (sTUP [0] 3 2 16 2 ((1, 1) :: repeat (1, 2) 35 ++ (5, 2) :: (1, 1) :: repeat (1, 2) 152 ++ (625, 2) :: (1, 1) :: repeat (1, 2) 2284 ++ (5187, 2) :: (1, 1) :: repeat (1, 2) 23909 ++ (11951, 2) :: (1, 1) :: repeat (1, 2) 100592 ++ (438888, 2) :: (1, 1) :: repeat (1, 2) 1511339 ++ (5653179, 2) :: (1, 1) :: repeat (1, 2) 11874956 ++ w) 1); closearith.
  }
  (* step 304: P TDN *)
  apply (hsteps_trans _ (HB [0] 3 1 4 ((14, 2) :: (1, 1) :: repeat (1, 2) 35 ++ (5, 2) :: (1, 1) :: repeat (1, 2) 152 ++ (625, 2) :: (1, 1) :: repeat (1, 2) 2284 ++ (5187, 2) :: (1, 1) :: repeat (1, 2) 23909 ++ (11951, 2) :: (1, 1) :: repeat (1, 2) 100592 ++ (438888, 2) :: (1, 1) :: repeat (1, 2) 1511339 ++ (5653179, 2) :: (1, 1) :: repeat (1, 2) 11874956 ++ w) 1)).
  {
    apply (sTDN [0] 3 ((14, 2) :: (1, 1) :: repeat (1, 2) 35 ++ (5, 2) :: (1, 1) :: repeat (1, 2) 152 ++ (625, 2) :: (1, 1) :: repeat (1, 2) 2284 ++ (5187, 2) :: (1, 1) :: repeat (1, 2) 23909 ++ (11951, 2) :: (1, 1) :: repeat (1, 2) 100592 ++ (438888, 2) :: (1, 1) :: repeat (1, 2) 1511339 ++ (5653179, 2) :: (1, 1) :: repeat (1, 2) 11874956 ++ w) 1).
  }
  (* step 305: sTUP *)
  apply (hsteps_trans _ (HC [0] 3 3 2 ((12, 2) :: (1, 1) :: repeat (1, 2) 35 ++ (5, 2) :: (1, 1) :: repeat (1, 2) 152 ++ (625, 2) :: (1, 1) :: repeat (1, 2) 2284 ++ (5187, 2) :: (1, 1) :: repeat (1, 2) 23909 ++ (11951, 2) :: (1, 1) :: repeat (1, 2) 100592 ++ (438888, 2) :: (1, 1) :: repeat (1, 2) 1511339 ++ (5653179, 2) :: (1, 1) :: repeat (1, 2) 11874956 ++ w) 1)).
  {
    replace ((12, 2) :: (1, 1) :: repeat (1, 2) 35 ++ (5, 2) :: (1, 1) :: repeat (1, 2) 152 ++ (625, 2) :: (1, 1) :: repeat (1, 2) 2284 ++ (5187, 2) :: (1, 1) :: repeat (1, 2) 23909 ++ (11951, 2) :: (1, 1) :: repeat (1, 2) 100592 ++ (438888, 2) :: (1, 1) :: repeat (1, 2) 1511339 ++ (5653179, 2) :: (1, 1) :: repeat (1, 2) 11874956 ++ w) with ((14 - 2, 2) :: (1, 1) :: repeat (1, 2) 35 ++ (5, 2) :: (1, 1) :: repeat (1, 2) 152 ++ (625, 2) :: (1, 1) :: repeat (1, 2) 2284 ++ (5187, 2) :: (1, 1) :: repeat (1, 2) 23909 ++ (11951, 2) :: (1, 1) :: repeat (1, 2) 100592 ++ (438888, 2) :: (1, 1) :: repeat (1, 2) 1511339 ++ (5653179, 2) :: (1, 1) :: repeat (1, 2) 11874956 ++ w) by sec_eq.
    apply (sTUP [0] 3 4 14 2 ((1, 1) :: repeat (1, 2) 35 ++ (5, 2) :: (1, 1) :: repeat (1, 2) 152 ++ (625, 2) :: (1, 1) :: repeat (1, 2) 2284 ++ (5187, 2) :: (1, 1) :: repeat (1, 2) 23909 ++ (11951, 2) :: (1, 1) :: repeat (1, 2) 100592 ++ (438888, 2) :: (1, 1) :: repeat (1, 2) 1511339 ++ (5653179, 2) :: (1, 1) :: repeat (1, 2) 11874956 ++ w) 1); closearith.
  }
  (* step 306: DIPGRIND 3 6 *)
  apply (hsteps_trans _ (HC [0] 0 3 2 (repeat (1, 2) 3 ++ (6, 2) :: (1, 1) :: repeat (1, 2) 35 ++ (5, 2) :: (1, 1) :: repeat (1, 2) 152 ++ (625, 2) :: (1, 1) :: repeat (1, 2) 2284 ++ (5187, 2) :: (1, 1) :: repeat (1, 2) 23909 ++ (11951, 2) :: (1, 1) :: repeat (1, 2) 100592 ++ (438888, 2) :: (1, 1) :: repeat (1, 2) 1511339 ++ (5653179, 2) :: (1, 1) :: repeat (1, 2) 11874956 ++ w) 1)).
  {
    apply (DIPGRIND 3 6 [0] ((1, 1) :: repeat (1, 2) 35 ++ (5, 2) :: (1, 1) :: repeat (1, 2) 152 ++ (625, 2) :: (1, 1) :: repeat (1, 2) 2284 ++ (5187, 2) :: (1, 1) :: repeat (1, 2) 23909 ++ (11951, 2) :: (1, 1) :: repeat (1, 2) 100592 ++ (438888, 2) :: (1, 1) :: repeat (1, 2) 1511339 ++ (5653179, 2) :: (1, 1) :: repeat (1, 2) 11874956 ++ w) 1); closearith.
  }
  (* step 307: P PX2B0 *)
  apply (hsteps_trans _ (HB [] 0 1 5 (repeat (1, 2) 4 ++ (6, 2) :: (1, 1) :: repeat (1, 2) 35 ++ (5, 2) :: (1, 1) :: repeat (1, 2) 152 ++ (625, 2) :: (1, 1) :: repeat (1, 2) 2284 ++ (5187, 2) :: (1, 1) :: repeat (1, 2) 23909 ++ (11951, 2) :: (1, 1) :: repeat (1, 2) 100592 ++ (438888, 2) :: (1, 1) :: repeat (1, 2) 1511339 ++ (5653179, 2) :: (1, 1) :: repeat (1, 2) 11874956 ++ w) 1)).
  {
    exact (hsteps_step _ _ _ (hPX2B0 (repeat (1, 2) 3 ++ (6, 2) :: (1, 1) :: repeat (1, 2) 35 ++ (5, 2) :: (1, 1) :: repeat (1, 2) 152 ++ (625, 2) :: (1, 1) :: repeat (1, 2) 2284 ++ (5187, 2) :: (1, 1) :: repeat (1, 2) 23909 ++ (11951, 2) :: (1, 1) :: repeat (1, 2) 100592 ++ (438888, 2) :: (1, 1) :: repeat (1, 2) 1511339 ++ (5653179, 2) :: (1, 1) :: repeat (1, 2) 11874956 ++ w) 1) (hsteps_refl _)).
  }
  (* step 308: M pop12 (4,) *)
  apply (hsteps_trans _ (HB [] 4 1 13 ((6, 2) :: (1, 1) :: repeat (1, 2) 35 ++ (5, 2) :: (1, 1) :: repeat (1, 2) 152 ++ (625, 2) :: (1, 1) :: repeat (1, 2) 2284 ++ (5187, 2) :: (1, 1) :: repeat (1, 2) 23909 ++ (11951, 2) :: (1, 1) :: repeat (1, 2) 100592 ++ (438888, 2) :: (1, 1) :: repeat (1, 2) 1511339 ++ (5653179, 2) :: (1, 1) :: repeat (1, 2) 11874956 ++ w) 1)).
  {
    apply (pop12 4 [] 0 5 ((6, 2) :: (1, 1) :: repeat (1, 2) 35 ++ (5, 2) :: (1, 1) :: repeat (1, 2) 152 ++ (625, 2) :: (1, 1) :: repeat (1, 2) 2284 ++ (5187, 2) :: (1, 1) :: repeat (1, 2) 23909 ++ (11951, 2) :: (1, 1) :: repeat (1, 2) 100592 ++ (438888, 2) :: (1, 1) :: repeat (1, 2) 1511339 ++ (5653179, 2) :: (1, 1) :: repeat (1, 2) 11874956 ++ w) 1); closearith.
  }
  (* step 309: sTUP *)
  apply (hsteps_trans _ (HC [] 4 12 2 ((4, 2) :: (1, 1) :: repeat (1, 2) 35 ++ (5, 2) :: (1, 1) :: repeat (1, 2) 152 ++ (625, 2) :: (1, 1) :: repeat (1, 2) 2284 ++ (5187, 2) :: (1, 1) :: repeat (1, 2) 23909 ++ (11951, 2) :: (1, 1) :: repeat (1, 2) 100592 ++ (438888, 2) :: (1, 1) :: repeat (1, 2) 1511339 ++ (5653179, 2) :: (1, 1) :: repeat (1, 2) 11874956 ++ w) 1)).
  {
    replace ((4, 2) :: (1, 1) :: repeat (1, 2) 35 ++ (5, 2) :: (1, 1) :: repeat (1, 2) 152 ++ (625, 2) :: (1, 1) :: repeat (1, 2) 2284 ++ (5187, 2) :: (1, 1) :: repeat (1, 2) 23909 ++ (11951, 2) :: (1, 1) :: repeat (1, 2) 100592 ++ (438888, 2) :: (1, 1) :: repeat (1, 2) 1511339 ++ (5653179, 2) :: (1, 1) :: repeat (1, 2) 11874956 ++ w) with ((6 - 2, 2) :: (1, 1) :: repeat (1, 2) 35 ++ (5, 2) :: (1, 1) :: repeat (1, 2) 152 ++ (625, 2) :: (1, 1) :: repeat (1, 2) 2284 ++ (5187, 2) :: (1, 1) :: repeat (1, 2) 23909 ++ (11951, 2) :: (1, 1) :: repeat (1, 2) 100592 ++ (438888, 2) :: (1, 1) :: repeat (1, 2) 1511339 ++ (5653179, 2) :: (1, 1) :: repeat (1, 2) 11874956 ++ w) by sec_eq.
    apply (sTUP [] 4 13 6 2 ((1, 1) :: repeat (1, 2) 35 ++ (5, 2) :: (1, 1) :: repeat (1, 2) 152 ++ (625, 2) :: (1, 1) :: repeat (1, 2) 2284 ++ (5187, 2) :: (1, 1) :: repeat (1, 2) 23909 ++ (11951, 2) :: (1, 1) :: repeat (1, 2) 100592 ++ (438888, 2) :: (1, 1) :: repeat (1, 2) 1511339 ++ (5653179, 2) :: (1, 1) :: repeat (1, 2) 11874956 ++ w) 1); closearith.
  }
  (* step 310: P PUSH *)
  apply (hsteps_trans _ (HC [] 3 1 2 ((10, 2) :: (4, 2) :: (1, 1) :: repeat (1, 2) 35 ++ (5, 2) :: (1, 1) :: repeat (1, 2) 152 ++ (625, 2) :: (1, 1) :: repeat (1, 2) 2284 ++ (5187, 2) :: (1, 1) :: repeat (1, 2) 23909 ++ (11951, 2) :: (1, 1) :: repeat (1, 2) 100592 ++ (438888, 2) :: (1, 1) :: repeat (1, 2) 1511339 ++ (5653179, 2) :: (1, 1) :: repeat (1, 2) 11874956 ++ w) 1)).
  {
    replace ((10, 2) :: (4, 2) :: (1, 1) :: repeat (1, 2) 35 ++ (5, 2) :: (1, 1) :: repeat (1, 2) 152 ++ (625, 2) :: (1, 1) :: repeat (1, 2) 2284 ++ (5187, 2) :: (1, 1) :: repeat (1, 2) 23909 ++ (11951, 2) :: (1, 1) :: repeat (1, 2) 100592 ++ (438888, 2) :: (1, 1) :: repeat (1, 2) 1511339 ++ (5653179, 2) :: (1, 1) :: repeat (1, 2) 11874956 ++ w) with ((12 - 2, 2) :: (4, 2) :: (1, 1) :: repeat (1, 2) 35 ++ (5, 2) :: (1, 1) :: repeat (1, 2) 152 ++ (625, 2) :: (1, 1) :: repeat (1, 2) 2284 ++ (5187, 2) :: (1, 1) :: repeat (1, 2) 23909 ++ (11951, 2) :: (1, 1) :: repeat (1, 2) 100592 ++ (438888, 2) :: (1, 1) :: repeat (1, 2) 1511339 ++ (5653179, 2) :: (1, 1) :: repeat (1, 2) 11874956 ++ w) by sec_eq.
    apply (sPUSH [] 3 12 ((4, 2) :: (1, 1) :: repeat (1, 2) 35 ++ (5, 2) :: (1, 1) :: repeat (1, 2) 152 ++ (625, 2) :: (1, 1) :: repeat (1, 2) 2284 ++ (5187, 2) :: (1, 1) :: repeat (1, 2) 23909 ++ (11951, 2) :: (1, 1) :: repeat (1, 2) 100592 ++ (438888, 2) :: (1, 1) :: repeat (1, 2) 1511339 ++ (5653179, 2) :: (1, 1) :: repeat (1, 2) 11874956 ++ w) 1); closearith.
  }
  (* step 311: P TDN *)
  apply (hsteps_trans _ (HB [] 3 1 4 ((10, 2) :: (4, 2) :: (1, 1) :: repeat (1, 2) 35 ++ (5, 2) :: (1, 1) :: repeat (1, 2) 152 ++ (625, 2) :: (1, 1) :: repeat (1, 2) 2284 ++ (5187, 2) :: (1, 1) :: repeat (1, 2) 23909 ++ (11951, 2) :: (1, 1) :: repeat (1, 2) 100592 ++ (438888, 2) :: (1, 1) :: repeat (1, 2) 1511339 ++ (5653179, 2) :: (1, 1) :: repeat (1, 2) 11874956 ++ w) 1)).
  {
    apply (sTDN [] 3 ((10, 2) :: (4, 2) :: (1, 1) :: repeat (1, 2) 35 ++ (5, 2) :: (1, 1) :: repeat (1, 2) 152 ++ (625, 2) :: (1, 1) :: repeat (1, 2) 2284 ++ (5187, 2) :: (1, 1) :: repeat (1, 2) 23909 ++ (11951, 2) :: (1, 1) :: repeat (1, 2) 100592 ++ (438888, 2) :: (1, 1) :: repeat (1, 2) 1511339 ++ (5653179, 2) :: (1, 1) :: repeat (1, 2) 11874956 ++ w) 1).
  }
  (* step 312: sTUP *)
  apply (hsteps_trans _ (HC [] 3 3 2 ((8, 2) :: (4, 2) :: (1, 1) :: repeat (1, 2) 35 ++ (5, 2) :: (1, 1) :: repeat (1, 2) 152 ++ (625, 2) :: (1, 1) :: repeat (1, 2) 2284 ++ (5187, 2) :: (1, 1) :: repeat (1, 2) 23909 ++ (11951, 2) :: (1, 1) :: repeat (1, 2) 100592 ++ (438888, 2) :: (1, 1) :: repeat (1, 2) 1511339 ++ (5653179, 2) :: (1, 1) :: repeat (1, 2) 11874956 ++ w) 1)).
  {
    replace ((8, 2) :: (4, 2) :: (1, 1) :: repeat (1, 2) 35 ++ (5, 2) :: (1, 1) :: repeat (1, 2) 152 ++ (625, 2) :: (1, 1) :: repeat (1, 2) 2284 ++ (5187, 2) :: (1, 1) :: repeat (1, 2) 23909 ++ (11951, 2) :: (1, 1) :: repeat (1, 2) 100592 ++ (438888, 2) :: (1, 1) :: repeat (1, 2) 1511339 ++ (5653179, 2) :: (1, 1) :: repeat (1, 2) 11874956 ++ w) with ((10 - 2, 2) :: (4, 2) :: (1, 1) :: repeat (1, 2) 35 ++ (5, 2) :: (1, 1) :: repeat (1, 2) 152 ++ (625, 2) :: (1, 1) :: repeat (1, 2) 2284 ++ (5187, 2) :: (1, 1) :: repeat (1, 2) 23909 ++ (11951, 2) :: (1, 1) :: repeat (1, 2) 100592 ++ (438888, 2) :: (1, 1) :: repeat (1, 2) 1511339 ++ (5653179, 2) :: (1, 1) :: repeat (1, 2) 11874956 ++ w) by sec_eq.
    apply (sTUP [] 3 4 10 2 ((4, 2) :: (1, 1) :: repeat (1, 2) 35 ++ (5, 2) :: (1, 1) :: repeat (1, 2) 152 ++ (625, 2) :: (1, 1) :: repeat (1, 2) 2284 ++ (5187, 2) :: (1, 1) :: repeat (1, 2) 23909 ++ (11951, 2) :: (1, 1) :: repeat (1, 2) 100592 ++ (438888, 2) :: (1, 1) :: repeat (1, 2) 1511339 ++ (5653179, 2) :: (1, 1) :: repeat (1, 2) 11874956 ++ w) 1); closearith.
  }
  (* step 313: DIPGRIND 3 2 *)
  apply (hsteps_trans _ (HC [] 0 3 2 (repeat (1, 2) 3 ++ (2, 2) :: (4, 2) :: (1, 1) :: repeat (1, 2) 35 ++ (5, 2) :: (1, 1) :: repeat (1, 2) 152 ++ (625, 2) :: (1, 1) :: repeat (1, 2) 2284 ++ (5187, 2) :: (1, 1) :: repeat (1, 2) 23909 ++ (11951, 2) :: (1, 1) :: repeat (1, 2) 100592 ++ (438888, 2) :: (1, 1) :: repeat (1, 2) 1511339 ++ (5653179, 2) :: (1, 1) :: repeat (1, 2) 11874956 ++ w) 1)).
  {
    apply (DIPGRIND 3 2 [] ((4, 2) :: (1, 1) :: repeat (1, 2) 35 ++ (5, 2) :: (1, 1) :: repeat (1, 2) 152 ++ (625, 2) :: (1, 1) :: repeat (1, 2) 2284 ++ (5187, 2) :: (1, 1) :: repeat (1, 2) 23909 ++ (11951, 2) :: (1, 1) :: repeat (1, 2) 100592 ++ (438888, 2) :: (1, 1) :: repeat (1, 2) 1511339 ++ (5653179, 2) :: (1, 1) :: repeat (1, 2) 11874956 ++ w) 1); closearith.
  }
  (* step 314: P PUSHX *)
  apply (hsteps_trans _ (HB [] 1 1 7 (repeat (1, 2) 3 ++ (2, 2) :: (4, 2) :: (1, 1) :: repeat (1, 2) 35 ++ (5, 2) :: (1, 1) :: repeat (1, 2) 152 ++ (625, 2) :: (1, 1) :: repeat (1, 2) 2284 ++ (5187, 2) :: (1, 1) :: repeat (1, 2) 23909 ++ (11951, 2) :: (1, 1) :: repeat (1, 2) 100592 ++ (438888, 2) :: (1, 1) :: repeat (1, 2) 1511339 ++ (5653179, 2) :: (1, 1) :: repeat (1, 2) 11874956 ++ w) 1)).
  {
    exact (hsteps_step _ _ _ (hPUSHX (repeat (1, 2) 3 ++ (2, 2) :: (4, 2) :: (1, 1) :: repeat (1, 2) 35 ++ (5, 2) :: (1, 1) :: repeat (1, 2) 152 ++ (625, 2) :: (1, 1) :: repeat (1, 2) 2284 ++ (5187, 2) :: (1, 1) :: repeat (1, 2) 23909 ++ (11951, 2) :: (1, 1) :: repeat (1, 2) 100592 ++ (438888, 2) :: (1, 1) :: repeat (1, 2) 1511339 ++ (5653179, 2) :: (1, 1) :: repeat (1, 2) 11874956 ++ w) 1) (hsteps_refl _)).
  }
  (* step 315: M pop12 (3,) *)
  apply (hsteps_trans _ (HB [] 4 1 13 ((2, 2) :: (4, 2) :: (1, 1) :: repeat (1, 2) 35 ++ (5, 2) :: (1, 1) :: repeat (1, 2) 152 ++ (625, 2) :: (1, 1) :: repeat (1, 2) 2284 ++ (5187, 2) :: (1, 1) :: repeat (1, 2) 23909 ++ (11951, 2) :: (1, 1) :: repeat (1, 2) 100592 ++ (438888, 2) :: (1, 1) :: repeat (1, 2) 1511339 ++ (5653179, 2) :: (1, 1) :: repeat (1, 2) 11874956 ++ w) 1)).
  {
    apply (pop12 3 [] 1 7 ((2, 2) :: (4, 2) :: (1, 1) :: repeat (1, 2) 35 ++ (5, 2) :: (1, 1) :: repeat (1, 2) 152 ++ (625, 2) :: (1, 1) :: repeat (1, 2) 2284 ++ (5187, 2) :: (1, 1) :: repeat (1, 2) 23909 ++ (11951, 2) :: (1, 1) :: repeat (1, 2) 100592 ++ (438888, 2) :: (1, 1) :: repeat (1, 2) 1511339 ++ (5653179, 2) :: (1, 1) :: repeat (1, 2) 11874956 ++ w) 1); closearith.
  }
  (* step 316: P TUP2_1 *)
  apply (hsteps_trans _ (HC [5] 13 1 2 ((2, 2) :: (1, 1) :: repeat (1, 2) 35 ++ (5, 2) :: (1, 1) :: repeat (1, 2) 152 ++ (625, 2) :: (1, 1) :: repeat (1, 2) 2284 ++ (5187, 2) :: (1, 1) :: repeat (1, 2) 23909 ++ (11951, 2) :: (1, 1) :: repeat (1, 2) 100592 ++ (438888, 2) :: (1, 1) :: repeat (1, 2) 1511339 ++ (5653179, 2) :: (1, 1) :: repeat (1, 2) 11874956 ++ w) 1)).
  {
    replace ((2, 2) :: (1, 1) :: repeat (1, 2) 35 ++ (5, 2) :: (1, 1) :: repeat (1, 2) 152 ++ (625, 2) :: (1, 1) :: repeat (1, 2) 2284 ++ (5187, 2) :: (1, 1) :: repeat (1, 2) 23909 ++ (11951, 2) :: (1, 1) :: repeat (1, 2) 100592 ++ (438888, 2) :: (1, 1) :: repeat (1, 2) 1511339 ++ (5653179, 2) :: (1, 1) :: repeat (1, 2) 11874956 ++ w) with ((4 - 2, 2) :: (1, 1) :: repeat (1, 2) 35 ++ (5, 2) :: (1, 1) :: repeat (1, 2) 152 ++ (625, 2) :: (1, 1) :: repeat (1, 2) 2284 ++ (5187, 2) :: (1, 1) :: repeat (1, 2) 23909 ++ (11951, 2) :: (1, 1) :: repeat (1, 2) 100592 ++ (438888, 2) :: (1, 1) :: repeat (1, 2) 1511339 ++ (5653179, 2) :: (1, 1) :: repeat (1, 2) 11874956 ++ w) by sec_eq.
    apply (sTUP2_1 [] 4 12 4 ((1, 1) :: repeat (1, 2) 35 ++ (5, 2) :: (1, 1) :: repeat (1, 2) 152 ++ (625, 2) :: (1, 1) :: repeat (1, 2) 2284 ++ (5187, 2) :: (1, 1) :: repeat (1, 2) 23909 ++ (11951, 2) :: (1, 1) :: repeat (1, 2) 100592 ++ (438888, 2) :: (1, 1) :: repeat (1, 2) 1511339 ++ (5653179, 2) :: (1, 1) :: repeat (1, 2) 11874956 ++ w) 1); closearith.
  }
  (* step 317: P TDN *)
  apply (hsteps_trans _ (HB [5] 13 1 4 ((2, 2) :: (1, 1) :: repeat (1, 2) 35 ++ (5, 2) :: (1, 1) :: repeat (1, 2) 152 ++ (625, 2) :: (1, 1) :: repeat (1, 2) 2284 ++ (5187, 2) :: (1, 1) :: repeat (1, 2) 23909 ++ (11951, 2) :: (1, 1) :: repeat (1, 2) 100592 ++ (438888, 2) :: (1, 1) :: repeat (1, 2) 1511339 ++ (5653179, 2) :: (1, 1) :: repeat (1, 2) 11874956 ++ w) 1)).
  {
    apply (sTDN [5] 13 ((2, 2) :: (1, 1) :: repeat (1, 2) 35 ++ (5, 2) :: (1, 1) :: repeat (1, 2) 152 ++ (625, 2) :: (1, 1) :: repeat (1, 2) 2284 ++ (5187, 2) :: (1, 1) :: repeat (1, 2) 23909 ++ (11951, 2) :: (1, 1) :: repeat (1, 2) 100592 ++ (438888, 2) :: (1, 1) :: repeat (1, 2) 1511339 ++ (5653179, 2) :: (1, 1) :: repeat (1, 2) 11874956 ++ w) 1).
  }
  (* step 318: P TRANS2_1 *)
  apply (hsteps_trans _ (HB [14; 5] 5 1 3 (repeat (1, 2) 35 ++ (5, 2) :: (1, 1) :: repeat (1, 2) 152 ++ (625, 2) :: (1, 1) :: repeat (1, 2) 2284 ++ (5187, 2) :: (1, 1) :: repeat (1, 2) 23909 ++ (11951, 2) :: (1, 1) :: repeat (1, 2) 100592 ++ (438888, 2) :: (1, 1) :: repeat (1, 2) 1511339 ++ (5653179, 2) :: (1, 1) :: repeat (1, 2) 11874956 ++ w) 1)).
  {
    apply (sTRANS2_1 [5] 13 3 1 (repeat (1, 2) 35 ++ (5, 2) :: (1, 1) :: repeat (1, 2) 152 ++ (625, 2) :: (1, 1) :: repeat (1, 2) 2284 ++ (5187, 2) :: (1, 1) :: repeat (1, 2) 23909 ++ (11951, 2) :: (1, 1) :: repeat (1, 2) 100592 ++ (438888, 2) :: (1, 1) :: repeat (1, 2) 1511339 ++ (5653179, 2) :: (1, 1) :: repeat (1, 2) 11874956 ++ w) 1); closearith.
  }
  (* step 319: M pop12 (35,) *)
  apply (hsteps_trans _ (HB [14; 5] 40 1 73 ((5, 2) :: (1, 1) :: repeat (1, 2) 152 ++ (625, 2) :: (1, 1) :: repeat (1, 2) 2284 ++ (5187, 2) :: (1, 1) :: repeat (1, 2) 23909 ++ (11951, 2) :: (1, 1) :: repeat (1, 2) 100592 ++ (438888, 2) :: (1, 1) :: repeat (1, 2) 1511339 ++ (5653179, 2) :: (1, 1) :: repeat (1, 2) 11874956 ++ w) 1)).
  {
    apply (pop12 35 [14; 5] 5 3 ((5, 2) :: (1, 1) :: repeat (1, 2) 152 ++ (625, 2) :: (1, 1) :: repeat (1, 2) 2284 ++ (5187, 2) :: (1, 1) :: repeat (1, 2) 23909 ++ (11951, 2) :: (1, 1) :: repeat (1, 2) 100592 ++ (438888, 2) :: (1, 1) :: repeat (1, 2) 1511339 ++ (5653179, 2) :: (1, 1) :: repeat (1, 2) 11874956 ++ w) 1); closearith.
  }
  (* step 320: sTUP *)
  apply (hsteps_trans _ (HC [14; 5] 40 72 2 ((3, 2) :: (1, 1) :: repeat (1, 2) 152 ++ (625, 2) :: (1, 1) :: repeat (1, 2) 2284 ++ (5187, 2) :: (1, 1) :: repeat (1, 2) 23909 ++ (11951, 2) :: (1, 1) :: repeat (1, 2) 100592 ++ (438888, 2) :: (1, 1) :: repeat (1, 2) 1511339 ++ (5653179, 2) :: (1, 1) :: repeat (1, 2) 11874956 ++ w) 1)).
  {
    replace ((3, 2) :: (1, 1) :: repeat (1, 2) 152 ++ (625, 2) :: (1, 1) :: repeat (1, 2) 2284 ++ (5187, 2) :: (1, 1) :: repeat (1, 2) 23909 ++ (11951, 2) :: (1, 1) :: repeat (1, 2) 100592 ++ (438888, 2) :: (1, 1) :: repeat (1, 2) 1511339 ++ (5653179, 2) :: (1, 1) :: repeat (1, 2) 11874956 ++ w) with ((5 - 2, 2) :: (1, 1) :: repeat (1, 2) 152 ++ (625, 2) :: (1, 1) :: repeat (1, 2) 2284 ++ (5187, 2) :: (1, 1) :: repeat (1, 2) 23909 ++ (11951, 2) :: (1, 1) :: repeat (1, 2) 100592 ++ (438888, 2) :: (1, 1) :: repeat (1, 2) 1511339 ++ (5653179, 2) :: (1, 1) :: repeat (1, 2) 11874956 ++ w) by sec_eq.
    apply (sTUP [14; 5] 40 73 5 2 ((1, 1) :: repeat (1, 2) 152 ++ (625, 2) :: (1, 1) :: repeat (1, 2) 2284 ++ (5187, 2) :: (1, 1) :: repeat (1, 2) 23909 ++ (11951, 2) :: (1, 1) :: repeat (1, 2) 100592 ++ (438888, 2) :: (1, 1) :: repeat (1, 2) 1511339 ++ (5653179, 2) :: (1, 1) :: repeat (1, 2) 11874956 ++ w) 1); closearith.
  }
  (* step 321: hGRIND_even 34 *)
  apply (hsteps_trans _ (HB [14; 5] 39 1 72 ((2, 2) :: (3, 2) :: (1, 1) :: repeat (1, 2) 152 ++ (625, 2) :: (1, 1) :: repeat (1, 2) 2284 ++ (5187, 2) :: (1, 1) :: repeat (1, 2) 23909 ++ (11951, 2) :: (1, 1) :: repeat (1, 2) 100592 ++ (438888, 2) :: (1, 1) :: repeat (1, 2) 1511339 ++ (5653179, 2) :: (1, 1) :: repeat (1, 2) 11874956 ++ w) 1)).
  {
    apply (hGRIND_even 34 [14; 5] 39 ((3, 2) :: (1, 1) :: repeat (1, 2) 152 ++ (625, 2) :: (1, 1) :: repeat (1, 2) 2284 ++ (5187, 2) :: (1, 1) :: repeat (1, 2) 23909 ++ (11951, 2) :: (1, 1) :: repeat (1, 2) 100592 ++ (438888, 2) :: (1, 1) :: repeat (1, 2) 1511339 ++ (5653179, 2) :: (1, 1) :: repeat (1, 2) 11874956 ++ w) 1); closearith.
  }
  (* step 322: P TUP2_1 *)
  apply (hsteps_trans _ (HC [40; 14; 5] 72 1 2 (repeat (1, 2) 1 ++ (1, 1) :: repeat (1, 2) 152 ++ (625, 2) :: (1, 1) :: repeat (1, 2) 2284 ++ (5187, 2) :: (1, 1) :: repeat (1, 2) 23909 ++ (11951, 2) :: (1, 1) :: repeat (1, 2) 100592 ++ (438888, 2) :: (1, 1) :: repeat (1, 2) 1511339 ++ (5653179, 2) :: (1, 1) :: repeat (1, 2) 11874956 ++ w) 1)).
  {
    replace (repeat (1, 2) 1 ++ (1, 1) :: repeat (1, 2) 152 ++ (625, 2) :: (1, 1) :: repeat (1, 2) 2284 ++ (5187, 2) :: (1, 1) :: repeat (1, 2) 23909 ++ (11951, 2) :: (1, 1) :: repeat (1, 2) 100592 ++ (438888, 2) :: (1, 1) :: repeat (1, 2) 1511339 ++ (5653179, 2) :: (1, 1) :: repeat (1, 2) 11874956 ++ w) with ((3 - 2, 2) :: (1, 1) :: repeat (1, 2) 152 ++ (625, 2) :: (1, 1) :: repeat (1, 2) 2284 ++ (5187, 2) :: (1, 1) :: repeat (1, 2) 23909 ++ (11951, 2) :: (1, 1) :: repeat (1, 2) 100592 ++ (438888, 2) :: (1, 1) :: repeat (1, 2) 1511339 ++ (5653179, 2) :: (1, 1) :: repeat (1, 2) 11874956 ++ w) by sec_eq.
    apply (sTUP2_1 [14; 5] 39 71 3 ((1, 1) :: repeat (1, 2) 152 ++ (625, 2) :: (1, 1) :: repeat (1, 2) 2284 ++ (5187, 2) :: (1, 1) :: repeat (1, 2) 23909 ++ (11951, 2) :: (1, 1) :: repeat (1, 2) 100592 ++ (438888, 2) :: (1, 1) :: repeat (1, 2) 1511339 ++ (5653179, 2) :: (1, 1) :: repeat (1, 2) 11874956 ++ w) 1); closearith.
  }
  (* step 323: P TDN *)
  apply (hsteps_trans _ (HB [40; 14; 5] 72 1 4 (repeat (1, 2) 1 ++ (1, 1) :: repeat (1, 2) 152 ++ (625, 2) :: (1, 1) :: repeat (1, 2) 2284 ++ (5187, 2) :: (1, 1) :: repeat (1, 2) 23909 ++ (11951, 2) :: (1, 1) :: repeat (1, 2) 100592 ++ (438888, 2) :: (1, 1) :: repeat (1, 2) 1511339 ++ (5653179, 2) :: (1, 1) :: repeat (1, 2) 11874956 ++ w) 1)).
  {
    apply (sTDN [40; 14; 5] 72 (repeat (1, 2) 1 ++ (1, 1) :: repeat (1, 2) 152 ++ (625, 2) :: (1, 1) :: repeat (1, 2) 2284 ++ (5187, 2) :: (1, 1) :: repeat (1, 2) 23909 ++ (11951, 2) :: (1, 1) :: repeat (1, 2) 100592 ++ (438888, 2) :: (1, 1) :: repeat (1, 2) 1511339 ++ (5653179, 2) :: (1, 1) :: repeat (1, 2) 11874956 ++ w) 1).
  }
  (* step 324: M pop12 (1,) *)
  apply (hsteps_trans _ (HB [40; 14; 5] 73 1 6 ((1, 1) :: repeat (1, 2) 152 ++ (625, 2) :: (1, 1) :: repeat (1, 2) 2284 ++ (5187, 2) :: (1, 1) :: repeat (1, 2) 23909 ++ (11951, 2) :: (1, 1) :: repeat (1, 2) 100592 ++ (438888, 2) :: (1, 1) :: repeat (1, 2) 1511339 ++ (5653179, 2) :: (1, 1) :: repeat (1, 2) 11874956 ++ w) 1)).
  {
    apply (pop12 1 [40; 14; 5] 72 4 ((1, 1) :: repeat (1, 2) 152 ++ (625, 2) :: (1, 1) :: repeat (1, 2) 2284 ++ (5187, 2) :: (1, 1) :: repeat (1, 2) 23909 ++ (11951, 2) :: (1, 1) :: repeat (1, 2) 100592 ++ (438888, 2) :: (1, 1) :: repeat (1, 2) 1511339 ++ (5653179, 2) :: (1, 1) :: repeat (1, 2) 11874956 ++ w) 1); closearith.
  }
  (* step 325: P POP *)
  apply (hsteps_trans _ (HB [40; 14; 5] 74 1 7 (repeat (1, 2) 152 ++ (625, 2) :: (1, 1) :: repeat (1, 2) 2284 ++ (5187, 2) :: (1, 1) :: repeat (1, 2) 23909 ++ (11951, 2) :: (1, 1) :: repeat (1, 2) 100592 ++ (438888, 2) :: (1, 1) :: repeat (1, 2) 1511339 ++ (5653179, 2) :: (1, 1) :: repeat (1, 2) 11874956 ++ w) 1)).
  {
    apply (sPOP1 [40; 14; 5] 73 6 (repeat (1, 2) 152 ++ (625, 2) :: (1, 1) :: repeat (1, 2) 2284 ++ (5187, 2) :: (1, 1) :: repeat (1, 2) 23909 ++ (11951, 2) :: (1, 1) :: repeat (1, 2) 100592 ++ (438888, 2) :: (1, 1) :: repeat (1, 2) 1511339 ++ (5653179, 2) :: (1, 1) :: repeat (1, 2) 11874956 ++ w) 1); closearith.
  }
  (* step 326: M pop12 (152,) *)
  apply (hsteps_trans _ (HB [40; 14; 5] 226 1 311 ((625, 2) :: (1, 1) :: repeat (1, 2) 2284 ++ (5187, 2) :: (1, 1) :: repeat (1, 2) 23909 ++ (11951, 2) :: (1, 1) :: repeat (1, 2) 100592 ++ (438888, 2) :: (1, 1) :: repeat (1, 2) 1511339 ++ (5653179, 2) :: (1, 1) :: repeat (1, 2) 11874956 ++ w) 1)).
  {
    apply (pop12 152 [40; 14; 5] 74 7 ((625, 2) :: (1, 1) :: repeat (1, 2) 2284 ++ (5187, 2) :: (1, 1) :: repeat (1, 2) 23909 ++ (11951, 2) :: (1, 1) :: repeat (1, 2) 100592 ++ (438888, 2) :: (1, 1) :: repeat (1, 2) 1511339 ++ (5653179, 2) :: (1, 1) :: repeat (1, 2) 11874956 ++ w) 1); closearith.
  }
  (* step 327: sTUP *)
  apply (hsteps_trans _ (HC [40; 14; 5] 226 310 2 ((623, 2) :: (1, 1) :: repeat (1, 2) 2284 ++ (5187, 2) :: (1, 1) :: repeat (1, 2) 23909 ++ (11951, 2) :: (1, 1) :: repeat (1, 2) 100592 ++ (438888, 2) :: (1, 1) :: repeat (1, 2) 1511339 ++ (5653179, 2) :: (1, 1) :: repeat (1, 2) 11874956 ++ w) 1)).
  {
    replace ((623, 2) :: (1, 1) :: repeat (1, 2) 2284 ++ (5187, 2) :: (1, 1) :: repeat (1, 2) 23909 ++ (11951, 2) :: (1, 1) :: repeat (1, 2) 100592 ++ (438888, 2) :: (1, 1) :: repeat (1, 2) 1511339 ++ (5653179, 2) :: (1, 1) :: repeat (1, 2) 11874956 ++ w) with ((625 - 2, 2) :: (1, 1) :: repeat (1, 2) 2284 ++ (5187, 2) :: (1, 1) :: repeat (1, 2) 23909 ++ (11951, 2) :: (1, 1) :: repeat (1, 2) 100592 ++ (438888, 2) :: (1, 1) :: repeat (1, 2) 1511339 ++ (5653179, 2) :: (1, 1) :: repeat (1, 2) 11874956 ++ w) by sec_eq.
    apply (sTUP [40; 14; 5] 226 311 625 2 ((1, 1) :: repeat (1, 2) 2284 ++ (5187, 2) :: (1, 1) :: repeat (1, 2) 23909 ++ (11951, 2) :: (1, 1) :: repeat (1, 2) 100592 ++ (438888, 2) :: (1, 1) :: repeat (1, 2) 1511339 ++ (5653179, 2) :: (1, 1) :: repeat (1, 2) 11874956 ++ w) 1); closearith.
  }
  (* step 328: hGRIND_even 153 *)
  apply (hsteps_trans _ (HB [40; 14; 5] 225 1 310 ((2, 2) :: (623, 2) :: (1, 1) :: repeat (1, 2) 2284 ++ (5187, 2) :: (1, 1) :: repeat (1, 2) 23909 ++ (11951, 2) :: (1, 1) :: repeat (1, 2) 100592 ++ (438888, 2) :: (1, 1) :: repeat (1, 2) 1511339 ++ (5653179, 2) :: (1, 1) :: repeat (1, 2) 11874956 ++ w) 1)).
  {
    apply (hGRIND_even 153 [40; 14; 5] 225 ((623, 2) :: (1, 1) :: repeat (1, 2) 2284 ++ (5187, 2) :: (1, 1) :: repeat (1, 2) 23909 ++ (11951, 2) :: (1, 1) :: repeat (1, 2) 100592 ++ (438888, 2) :: (1, 1) :: repeat (1, 2) 1511339 ++ (5653179, 2) :: (1, 1) :: repeat (1, 2) 11874956 ++ w) 1); closearith.
  }
  (* step 329: P TUP2_1 *)
  apply (hsteps_trans _ (HC [226; 40; 14; 5] 310 1 2 ((621, 2) :: (1, 1) :: repeat (1, 2) 2284 ++ (5187, 2) :: (1, 1) :: repeat (1, 2) 23909 ++ (11951, 2) :: (1, 1) :: repeat (1, 2) 100592 ++ (438888, 2) :: (1, 1) :: repeat (1, 2) 1511339 ++ (5653179, 2) :: (1, 1) :: repeat (1, 2) 11874956 ++ w) 1)).
  {
    replace ((621, 2) :: (1, 1) :: repeat (1, 2) 2284 ++ (5187, 2) :: (1, 1) :: repeat (1, 2) 23909 ++ (11951, 2) :: (1, 1) :: repeat (1, 2) 100592 ++ (438888, 2) :: (1, 1) :: repeat (1, 2) 1511339 ++ (5653179, 2) :: (1, 1) :: repeat (1, 2) 11874956 ++ w) with ((623 - 2, 2) :: (1, 1) :: repeat (1, 2) 2284 ++ (5187, 2) :: (1, 1) :: repeat (1, 2) 23909 ++ (11951, 2) :: (1, 1) :: repeat (1, 2) 100592 ++ (438888, 2) :: (1, 1) :: repeat (1, 2) 1511339 ++ (5653179, 2) :: (1, 1) :: repeat (1, 2) 11874956 ++ w) by sec_eq.
    apply (sTUP2_1 [40; 14; 5] 225 309 623 ((1, 1) :: repeat (1, 2) 2284 ++ (5187, 2) :: (1, 1) :: repeat (1, 2) 23909 ++ (11951, 2) :: (1, 1) :: repeat (1, 2) 100592 ++ (438888, 2) :: (1, 1) :: repeat (1, 2) 1511339 ++ (5653179, 2) :: (1, 1) :: repeat (1, 2) 11874956 ++ w) 1); closearith.
  }
  (* step 330: P TDN *)
  apply (hsteps_trans _ (HB [226; 40; 14; 5] 310 1 4 ((621, 2) :: (1, 1) :: repeat (1, 2) 2284 ++ (5187, 2) :: (1, 1) :: repeat (1, 2) 23909 ++ (11951, 2) :: (1, 1) :: repeat (1, 2) 100592 ++ (438888, 2) :: (1, 1) :: repeat (1, 2) 1511339 ++ (5653179, 2) :: (1, 1) :: repeat (1, 2) 11874956 ++ w) 1)).
  {
    apply (sTDN [226; 40; 14; 5] 310 ((621, 2) :: (1, 1) :: repeat (1, 2) 2284 ++ (5187, 2) :: (1, 1) :: repeat (1, 2) 23909 ++ (11951, 2) :: (1, 1) :: repeat (1, 2) 100592 ++ (438888, 2) :: (1, 1) :: repeat (1, 2) 1511339 ++ (5653179, 2) :: (1, 1) :: repeat (1, 2) 11874956 ++ w) 1).
  }
  (* step 331: sTUP *)
  apply (hsteps_trans _ (HC [226; 40; 14; 5] 310 3 2 ((619, 2) :: (1, 1) :: repeat (1, 2) 2284 ++ (5187, 2) :: (1, 1) :: repeat (1, 2) 23909 ++ (11951, 2) :: (1, 1) :: repeat (1, 2) 100592 ++ (438888, 2) :: (1, 1) :: repeat (1, 2) 1511339 ++ (5653179, 2) :: (1, 1) :: repeat (1, 2) 11874956 ++ w) 1)).
  {
    replace ((619, 2) :: (1, 1) :: repeat (1, 2) 2284 ++ (5187, 2) :: (1, 1) :: repeat (1, 2) 23909 ++ (11951, 2) :: (1, 1) :: repeat (1, 2) 100592 ++ (438888, 2) :: (1, 1) :: repeat (1, 2) 1511339 ++ (5653179, 2) :: (1, 1) :: repeat (1, 2) 11874956 ++ w) with ((621 - 2, 2) :: (1, 1) :: repeat (1, 2) 2284 ++ (5187, 2) :: (1, 1) :: repeat (1, 2) 23909 ++ (11951, 2) :: (1, 1) :: repeat (1, 2) 100592 ++ (438888, 2) :: (1, 1) :: repeat (1, 2) 1511339 ++ (5653179, 2) :: (1, 1) :: repeat (1, 2) 11874956 ++ w) by sec_eq.
    apply (sTUP [226; 40; 14; 5] 310 4 621 2 ((1, 1) :: repeat (1, 2) 2284 ++ (5187, 2) :: (1, 1) :: repeat (1, 2) 23909 ++ (11951, 2) :: (1, 1) :: repeat (1, 2) 100592 ++ (438888, 2) :: (1, 1) :: repeat (1, 2) 1511339 ++ (5653179, 2) :: (1, 1) :: repeat (1, 2) 11874956 ++ w) 1); closearith.
  }
  (* step 332: CLEANG_odd 308 *)
  apply (hsteps_trans _ (HB [226; 40; 14; 5] 310 1 624 (repeat (1, 2) 1 ++ (1, 1) :: repeat (1, 2) 2284 ++ (5187, 2) :: (1, 1) :: repeat (1, 2) 23909 ++ (11951, 2) :: (1, 1) :: repeat (1, 2) 100592 ++ (438888, 2) :: (1, 1) :: repeat (1, 2) 1511339 ++ (5653179, 2) :: (1, 1) :: repeat (1, 2) 11874956 ++ w) 1)).
  {
    replace (repeat (1, 2) 1 ++ (1, 1) :: repeat (1, 2) 2284 ++ (5187, 2) :: (1, 1) :: repeat (1, 2) 23909 ++ (11951, 2) :: (1, 1) :: repeat (1, 2) 100592 ++ (438888, 2) :: (1, 1) :: repeat (1, 2) 1511339 ++ (5653179, 2) :: (1, 1) :: repeat (1, 2) 11874956 ++ w) with ((1, 2) :: (1, 1) :: repeat (1, 2) 2284 ++ (5187, 2) :: (1, 1) :: repeat (1, 2) 23909 ++ (11951, 2) :: (1, 1) :: repeat (1, 2) 100592 ++ (438888, 2) :: (1, 1) :: repeat (1, 2) 1511339 ++ (5653179, 2) :: (1, 1) :: repeat (1, 2) 11874956 ++ w) by sec_eq.
    apply (CLEANG_odd 308 [226; 40; 14; 5] 310 ((1, 1) :: repeat (1, 2) 2284 ++ (5187, 2) :: (1, 1) :: repeat (1, 2) 23909 ++ (11951, 2) :: (1, 1) :: repeat (1, 2) 100592 ++ (438888, 2) :: (1, 1) :: repeat (1, 2) 1511339 ++ (5653179, 2) :: (1, 1) :: repeat (1, 2) 11874956 ++ w) 1); closearith.
  }
  (* step 333: M pop12 (1,) *)
  apply (hsteps_trans _ (HB [226; 40; 14; 5] 311 1 626 ((1, 1) :: repeat (1, 2) 2284 ++ (5187, 2) :: (1, 1) :: repeat (1, 2) 23909 ++ (11951, 2) :: (1, 1) :: repeat (1, 2) 100592 ++ (438888, 2) :: (1, 1) :: repeat (1, 2) 1511339 ++ (5653179, 2) :: (1, 1) :: repeat (1, 2) 11874956 ++ w) 1)).
  {
    apply (pop12 1 [226; 40; 14; 5] 310 624 ((1, 1) :: repeat (1, 2) 2284 ++ (5187, 2) :: (1, 1) :: repeat (1, 2) 23909 ++ (11951, 2) :: (1, 1) :: repeat (1, 2) 100592 ++ (438888, 2) :: (1, 1) :: repeat (1, 2) 1511339 ++ (5653179, 2) :: (1, 1) :: repeat (1, 2) 11874956 ++ w) 1); closearith.
  }
  (* step 334: P POP *)
  apply (hsteps_trans _ (HB [226; 40; 14; 5] 312 1 627 (repeat (1, 2) 2284 ++ (5187, 2) :: (1, 1) :: repeat (1, 2) 23909 ++ (11951, 2) :: (1, 1) :: repeat (1, 2) 100592 ++ (438888, 2) :: (1, 1) :: repeat (1, 2) 1511339 ++ (5653179, 2) :: (1, 1) :: repeat (1, 2) 11874956 ++ w) 1)).
  {
    apply (sPOP1 [226; 40; 14; 5] 311 626 (repeat (1, 2) 2284 ++ (5187, 2) :: (1, 1) :: repeat (1, 2) 23909 ++ (11951, 2) :: (1, 1) :: repeat (1, 2) 100592 ++ (438888, 2) :: (1, 1) :: repeat (1, 2) 1511339 ++ (5653179, 2) :: (1, 1) :: repeat (1, 2) 11874956 ++ w) 1); closearith.
  }
  (* step 335: M pop12 (2284,) *)
  apply (hsteps_trans _ (HB [226; 40; 14; 5] 2596 1 5195 ((5187, 2) :: (1, 1) :: repeat (1, 2) 23909 ++ (11951, 2) :: (1, 1) :: repeat (1, 2) 100592 ++ (438888, 2) :: (1, 1) :: repeat (1, 2) 1511339 ++ (5653179, 2) :: (1, 1) :: repeat (1, 2) 11874956 ++ w) 1)).
  {
    apply (pop12 2284 [226; 40; 14; 5] 312 627 ((5187, 2) :: (1, 1) :: repeat (1, 2) 23909 ++ (11951, 2) :: (1, 1) :: repeat (1, 2) 100592 ++ (438888, 2) :: (1, 1) :: repeat (1, 2) 1511339 ++ (5653179, 2) :: (1, 1) :: repeat (1, 2) 11874956 ++ w) 1); closearith.
  }
  (* step 336: sTUP *)
  replace ((5185, 2) :: (1, 1) :: repeat (1, 2) 23909 ++ (11951, 2) :: (1, 1) :: repeat (1, 2) 100592 ++ (438888, 2) :: (1, 1) :: repeat (1, 2) 1511339 ++ (5653179, 2) :: (1, 1) :: repeat (1, 2) 11874956 ++ w) with ((5187 - 2, 2) :: (1, 1) :: repeat (1, 2) 23909 ++ (11951, 2) :: (1, 1) :: repeat (1, 2) 100592 ++ (438888, 2) :: (1, 1) :: repeat (1, 2) 1511339 ++ (5653179, 2) :: (1, 1) :: repeat (1, 2) 11874956 ++ w) by sec_eq.
  apply (sTUP [226; 40; 14; 5] 2596 5195 5187 2 ((1, 1) :: repeat (1, 2) 23909 ++ (11951, 2) :: (1, 1) :: repeat (1, 2) 100592 ++ (438888, 2) :: (1, 1) :: repeat (1, 2) 1511339 ++ (5653179, 2) :: (1, 1) :: repeat (1, 2) 11874956 ++ w) 1); closearith.
Qed.

(* CASCADE58g: steps 337-352 of the CASCADE58 chain. *)
Lemma CASCADE58g : forall w,
  hsteps (HC [226; 40; 14; 5] 2596 5194 2 ((5185, 2) :: (1, 1) :: repeat (1, 2) 23909 ++ (11951, 2) :: (1, 1) :: repeat (1, 2) 100592 ++ (438888, 2) :: (1, 1) :: repeat (1, 2) 1511339 ++ (5653179, 2) :: (1, 1) :: repeat (1, 2) 11874956 ++ w) 1)
         (HB [29105; 2596; 226; 40; 14; 5] 53008 1 11953 (repeat (1, 2) 100592 ++ (438888, 2) :: (1, 1) :: repeat (1, 2) 1511339 ++ (5653179, 2) :: (1, 1) :: repeat (1, 2) 11874956 ++ w) 1).
Proof.
  intro w.
  (* step 337: hGRIND_even 2595 *)
  apply (hsteps_trans _ (HB [226; 40; 14; 5] 2595 1 5194 ((2, 2) :: (5185, 2) :: (1, 1) :: repeat (1, 2) 23909 ++ (11951, 2) :: (1, 1) :: repeat (1, 2) 100592 ++ (438888, 2) :: (1, 1) :: repeat (1, 2) 1511339 ++ (5653179, 2) :: (1, 1) :: repeat (1, 2) 11874956 ++ w) 1)).
  {
    apply (hGRIND_even 2595 [226; 40; 14; 5] 2595 ((5185, 2) :: (1, 1) :: repeat (1, 2) 23909 ++ (11951, 2) :: (1, 1) :: repeat (1, 2) 100592 ++ (438888, 2) :: (1, 1) :: repeat (1, 2) 1511339 ++ (5653179, 2) :: (1, 1) :: repeat (1, 2) 11874956 ++ w) 1); closearith.
  }
  (* step 338: P TUP2_1 *)
  apply (hsteps_trans _ (HC [2596; 226; 40; 14; 5] 5194 1 2 ((5183, 2) :: (1, 1) :: repeat (1, 2) 23909 ++ (11951, 2) :: (1, 1) :: repeat (1, 2) 100592 ++ (438888, 2) :: (1, 1) :: repeat (1, 2) 1511339 ++ (5653179, 2) :: (1, 1) :: repeat (1, 2) 11874956 ++ w) 1)).
  {
    replace ((5183, 2) :: (1, 1) :: repeat (1, 2) 23909 ++ (11951, 2) :: (1, 1) :: repeat (1, 2) 100592 ++ (438888, 2) :: (1, 1) :: repeat (1, 2) 1511339 ++ (5653179, 2) :: (1, 1) :: repeat (1, 2) 11874956 ++ w) with ((5185 - 2, 2) :: (1, 1) :: repeat (1, 2) 23909 ++ (11951, 2) :: (1, 1) :: repeat (1, 2) 100592 ++ (438888, 2) :: (1, 1) :: repeat (1, 2) 1511339 ++ (5653179, 2) :: (1, 1) :: repeat (1, 2) 11874956 ++ w) by sec_eq.
    apply (sTUP2_1 [226; 40; 14; 5] 2595 5193 5185 ((1, 1) :: repeat (1, 2) 23909 ++ (11951, 2) :: (1, 1) :: repeat (1, 2) 100592 ++ (438888, 2) :: (1, 1) :: repeat (1, 2) 1511339 ++ (5653179, 2) :: (1, 1) :: repeat (1, 2) 11874956 ++ w) 1); closearith.
  }
  (* step 339: P TDN *)
  apply (hsteps_trans _ (HB [2596; 226; 40; 14; 5] 5194 1 4 ((5183, 2) :: (1, 1) :: repeat (1, 2) 23909 ++ (11951, 2) :: (1, 1) :: repeat (1, 2) 100592 ++ (438888, 2) :: (1, 1) :: repeat (1, 2) 1511339 ++ (5653179, 2) :: (1, 1) :: repeat (1, 2) 11874956 ++ w) 1)).
  {
    apply (sTDN [2596; 226; 40; 14; 5] 5194 ((5183, 2) :: (1, 1) :: repeat (1, 2) 23909 ++ (11951, 2) :: (1, 1) :: repeat (1, 2) 100592 ++ (438888, 2) :: (1, 1) :: repeat (1, 2) 1511339 ++ (5653179, 2) :: (1, 1) :: repeat (1, 2) 11874956 ++ w) 1).
  }
  (* step 340: sTUP *)
  apply (hsteps_trans _ (HC [2596; 226; 40; 14; 5] 5194 3 2 ((5181, 2) :: (1, 1) :: repeat (1, 2) 23909 ++ (11951, 2) :: (1, 1) :: repeat (1, 2) 100592 ++ (438888, 2) :: (1, 1) :: repeat (1, 2) 1511339 ++ (5653179, 2) :: (1, 1) :: repeat (1, 2) 11874956 ++ w) 1)).
  {
    replace ((5181, 2) :: (1, 1) :: repeat (1, 2) 23909 ++ (11951, 2) :: (1, 1) :: repeat (1, 2) 100592 ++ (438888, 2) :: (1, 1) :: repeat (1, 2) 1511339 ++ (5653179, 2) :: (1, 1) :: repeat (1, 2) 11874956 ++ w) with ((5183 - 2, 2) :: (1, 1) :: repeat (1, 2) 23909 ++ (11951, 2) :: (1, 1) :: repeat (1, 2) 100592 ++ (438888, 2) :: (1, 1) :: repeat (1, 2) 1511339 ++ (5653179, 2) :: (1, 1) :: repeat (1, 2) 11874956 ++ w) by sec_eq.
    apply (sTUP [2596; 226; 40; 14; 5] 5194 4 5183 2 ((1, 1) :: repeat (1, 2) 23909 ++ (11951, 2) :: (1, 1) :: repeat (1, 2) 100592 ++ (438888, 2) :: (1, 1) :: repeat (1, 2) 1511339 ++ (5653179, 2) :: (1, 1) :: repeat (1, 2) 11874956 ++ w) 1); closearith.
  }
  (* step 341: CLEANG_odd 2589 *)
  apply (hsteps_trans _ (HB [2596; 226; 40; 14; 5] 5194 1 5186 (repeat (1, 2) 1 ++ (1, 1) :: repeat (1, 2) 23909 ++ (11951, 2) :: (1, 1) :: repeat (1, 2) 100592 ++ (438888, 2) :: (1, 1) :: repeat (1, 2) 1511339 ++ (5653179, 2) :: (1, 1) :: repeat (1, 2) 11874956 ++ w) 1)).
  {
    replace (repeat (1, 2) 1 ++ (1, 1) :: repeat (1, 2) 23909 ++ (11951, 2) :: (1, 1) :: repeat (1, 2) 100592 ++ (438888, 2) :: (1, 1) :: repeat (1, 2) 1511339 ++ (5653179, 2) :: (1, 1) :: repeat (1, 2) 11874956 ++ w) with ((1, 2) :: (1, 1) :: repeat (1, 2) 23909 ++ (11951, 2) :: (1, 1) :: repeat (1, 2) 100592 ++ (438888, 2) :: (1, 1) :: repeat (1, 2) 1511339 ++ (5653179, 2) :: (1, 1) :: repeat (1, 2) 11874956 ++ w) by sec_eq.
    apply (CLEANG_odd 2589 [2596; 226; 40; 14; 5] 5194 ((1, 1) :: repeat (1, 2) 23909 ++ (11951, 2) :: (1, 1) :: repeat (1, 2) 100592 ++ (438888, 2) :: (1, 1) :: repeat (1, 2) 1511339 ++ (5653179, 2) :: (1, 1) :: repeat (1, 2) 11874956 ++ w) 1); closearith.
  }
  (* step 342: M pop12 (1,) *)
  apply (hsteps_trans _ (HB [2596; 226; 40; 14; 5] 5195 1 5188 ((1, 1) :: repeat (1, 2) 23909 ++ (11951, 2) :: (1, 1) :: repeat (1, 2) 100592 ++ (438888, 2) :: (1, 1) :: repeat (1, 2) 1511339 ++ (5653179, 2) :: (1, 1) :: repeat (1, 2) 11874956 ++ w) 1)).
  {
    apply (pop12 1 [2596; 226; 40; 14; 5] 5194 5186 ((1, 1) :: repeat (1, 2) 23909 ++ (11951, 2) :: (1, 1) :: repeat (1, 2) 100592 ++ (438888, 2) :: (1, 1) :: repeat (1, 2) 1511339 ++ (5653179, 2) :: (1, 1) :: repeat (1, 2) 11874956 ++ w) 1); closearith.
  }
  (* step 343: P POP *)
  apply (hsteps_trans _ (HB [2596; 226; 40; 14; 5] 5196 1 5189 (repeat (1, 2) 23909 ++ (11951, 2) :: (1, 1) :: repeat (1, 2) 100592 ++ (438888, 2) :: (1, 1) :: repeat (1, 2) 1511339 ++ (5653179, 2) :: (1, 1) :: repeat (1, 2) 11874956 ++ w) 1)).
  {
    apply (sPOP1 [2596; 226; 40; 14; 5] 5195 5188 (repeat (1, 2) 23909 ++ (11951, 2) :: (1, 1) :: repeat (1, 2) 100592 ++ (438888, 2) :: (1, 1) :: repeat (1, 2) 1511339 ++ (5653179, 2) :: (1, 1) :: repeat (1, 2) 11874956 ++ w) 1); closearith.
  }
  (* step 344: M pop12 (23909,) *)
  apply (hsteps_trans _ (HB [2596; 226; 40; 14; 5] 29105 1 53007 ((11951, 2) :: (1, 1) :: repeat (1, 2) 100592 ++ (438888, 2) :: (1, 1) :: repeat (1, 2) 1511339 ++ (5653179, 2) :: (1, 1) :: repeat (1, 2) 11874956 ++ w) 1)).
  {
    apply (pop12 23909 [2596; 226; 40; 14; 5] 5196 5189 ((11951, 2) :: (1, 1) :: repeat (1, 2) 100592 ++ (438888, 2) :: (1, 1) :: repeat (1, 2) 1511339 ++ (5653179, 2) :: (1, 1) :: repeat (1, 2) 11874956 ++ w) 1); closearith.
  }
  (* step 345: sTUP *)
  apply (hsteps_trans _ (HC [2596; 226; 40; 14; 5] 29105 53006 2 ((11949, 2) :: (1, 1) :: repeat (1, 2) 100592 ++ (438888, 2) :: (1, 1) :: repeat (1, 2) 1511339 ++ (5653179, 2) :: (1, 1) :: repeat (1, 2) 11874956 ++ w) 1)).
  {
    replace ((11949, 2) :: (1, 1) :: repeat (1, 2) 100592 ++ (438888, 2) :: (1, 1) :: repeat (1, 2) 1511339 ++ (5653179, 2) :: (1, 1) :: repeat (1, 2) 11874956 ++ w) with ((11951 - 2, 2) :: (1, 1) :: repeat (1, 2) 100592 ++ (438888, 2) :: (1, 1) :: repeat (1, 2) 1511339 ++ (5653179, 2) :: (1, 1) :: repeat (1, 2) 11874956 ++ w) by sec_eq.
    apply (sTUP [2596; 226; 40; 14; 5] 29105 53007 11951 2 ((1, 1) :: repeat (1, 2) 100592 ++ (438888, 2) :: (1, 1) :: repeat (1, 2) 1511339 ++ (5653179, 2) :: (1, 1) :: repeat (1, 2) 11874956 ++ w) 1); closearith.
  }
  (* step 346: hGRIND_even 26501 *)
  apply (hsteps_trans _ (HB [2596; 226; 40; 14; 5] 29104 1 53006 ((2, 2) :: (11949, 2) :: (1, 1) :: repeat (1, 2) 100592 ++ (438888, 2) :: (1, 1) :: repeat (1, 2) 1511339 ++ (5653179, 2) :: (1, 1) :: repeat (1, 2) 11874956 ++ w) 1)).
  {
    rewrite NUM58X20.
    apply (hGRIND_even 26501 [2596; 226; 40; 14; 5] 29104 ((11949, 2) :: (1, 1) :: repeat (1, 2) 100592 ++ (438888, 2) :: (1, 1) :: repeat (1, 2) 1511339 ++ (5653179, 2) :: (1, 1) :: repeat (1, 2) 11874956 ++ w) 1); closearith.
  }
  (* step 347: P TUP2_1 *)
  apply (hsteps_trans _ (HC [29105; 2596; 226; 40; 14; 5] 53006 1 2 ((11947, 2) :: (1, 1) :: repeat (1, 2) 100592 ++ (438888, 2) :: (1, 1) :: repeat (1, 2) 1511339 ++ (5653179, 2) :: (1, 1) :: repeat (1, 2) 11874956 ++ w) 1)).
  {
    replace ((11947, 2) :: (1, 1) :: repeat (1, 2) 100592 ++ (438888, 2) :: (1, 1) :: repeat (1, 2) 1511339 ++ (5653179, 2) :: (1, 1) :: repeat (1, 2) 11874956 ++ w) with ((11949 - 2, 2) :: (1, 1) :: repeat (1, 2) 100592 ++ (438888, 2) :: (1, 1) :: repeat (1, 2) 1511339 ++ (5653179, 2) :: (1, 1) :: repeat (1, 2) 11874956 ++ w) by sec_eq.
    apply (sTUP2_1 [2596; 226; 40; 14; 5] 29104 53005 11949 ((1, 1) :: repeat (1, 2) 100592 ++ (438888, 2) :: (1, 1) :: repeat (1, 2) 1511339 ++ (5653179, 2) :: (1, 1) :: repeat (1, 2) 11874956 ++ w) 1); closearith.
  }
  (* step 348: P TDN *)
  apply (hsteps_trans _ (HB [29105; 2596; 226; 40; 14; 5] 53006 1 4 ((11947, 2) :: (1, 1) :: repeat (1, 2) 100592 ++ (438888, 2) :: (1, 1) :: repeat (1, 2) 1511339 ++ (5653179, 2) :: (1, 1) :: repeat (1, 2) 11874956 ++ w) 1)).
  {
    apply (sTDN [29105; 2596; 226; 40; 14; 5] 53006 ((11947, 2) :: (1, 1) :: repeat (1, 2) 100592 ++ (438888, 2) :: (1, 1) :: repeat (1, 2) 1511339 ++ (5653179, 2) :: (1, 1) :: repeat (1, 2) 11874956 ++ w) 1).
  }
  (* step 349: sTUP *)
  apply (hsteps_trans _ (HC [29105; 2596; 226; 40; 14; 5] 53006 3 2 ((11945, 2) :: (1, 1) :: repeat (1, 2) 100592 ++ (438888, 2) :: (1, 1) :: repeat (1, 2) 1511339 ++ (5653179, 2) :: (1, 1) :: repeat (1, 2) 11874956 ++ w) 1)).
  {
    replace ((11945, 2) :: (1, 1) :: repeat (1, 2) 100592 ++ (438888, 2) :: (1, 1) :: repeat (1, 2) 1511339 ++ (5653179, 2) :: (1, 1) :: repeat (1, 2) 11874956 ++ w) with ((11947 - 2, 2) :: (1, 1) :: repeat (1, 2) 100592 ++ (438888, 2) :: (1, 1) :: repeat (1, 2) 1511339 ++ (5653179, 2) :: (1, 1) :: repeat (1, 2) 11874956 ++ w) by sec_eq.
    apply (sTUP [29105; 2596; 226; 40; 14; 5] 53006 4 11947 2 ((1, 1) :: repeat (1, 2) 100592 ++ (438888, 2) :: (1, 1) :: repeat (1, 2) 1511339 ++ (5653179, 2) :: (1, 1) :: repeat (1, 2) 11874956 ++ w) 1); closearith.
  }
  (* step 350: CLEANG_odd 5971 *)
  apply (hsteps_trans _ (HB [29105; 2596; 226; 40; 14; 5] 53006 1 11950 (repeat (1, 2) 1 ++ (1, 1) :: repeat (1, 2) 100592 ++ (438888, 2) :: (1, 1) :: repeat (1, 2) 1511339 ++ (5653179, 2) :: (1, 1) :: repeat (1, 2) 11874956 ++ w) 1)).
  {
    replace (repeat (1, 2) 1 ++ (1, 1) :: repeat (1, 2) 100592 ++ (438888, 2) :: (1, 1) :: repeat (1, 2) 1511339 ++ (5653179, 2) :: (1, 1) :: repeat (1, 2) 11874956 ++ w) with ((1, 2) :: (1, 1) :: repeat (1, 2) 100592 ++ (438888, 2) :: (1, 1) :: repeat (1, 2) 1511339 ++ (5653179, 2) :: (1, 1) :: repeat (1, 2) 11874956 ++ w) by sec_eq.
    apply (CLEANG_odd 5971 [29105; 2596; 226; 40; 14; 5] 53006 ((1, 1) :: repeat (1, 2) 100592 ++ (438888, 2) :: (1, 1) :: repeat (1, 2) 1511339 ++ (5653179, 2) :: (1, 1) :: repeat (1, 2) 11874956 ++ w) 1); closearith.
  }
  (* step 351: M pop12 (1,) *)
  apply (hsteps_trans _ (HB [29105; 2596; 226; 40; 14; 5] 53007 1 11952 ((1, 1) :: repeat (1, 2) 100592 ++ (438888, 2) :: (1, 1) :: repeat (1, 2) 1511339 ++ (5653179, 2) :: (1, 1) :: repeat (1, 2) 11874956 ++ w) 1)).
  {
    apply (pop12 1 [29105; 2596; 226; 40; 14; 5] 53006 11950 ((1, 1) :: repeat (1, 2) 100592 ++ (438888, 2) :: (1, 1) :: repeat (1, 2) 1511339 ++ (5653179, 2) :: (1, 1) :: repeat (1, 2) 11874956 ++ w) 1); closearith.
  }
  (* step 352: P POP *)
  apply (sPOP1 [29105; 2596; 226; 40; 14; 5] 53007 11952 (repeat (1, 2) 100592 ++ (438888, 2) :: (1, 1) :: repeat (1, 2) 1511339 ++ (5653179, 2) :: (1, 1) :: repeat (1, 2) 11874956 ++ w) 1); closearith.
Qed.

