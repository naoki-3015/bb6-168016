(* ================================================================= *)
(*  Grind23.v -- Phase 55: the ninth re-descent cascade of the      *)
(*  TOP8 state, mechanised as a fixed parse, closing TAIL2_END9     *)
(*  for the whole first j-band 1425926 <= j <= 4277778 (TOP8        *)
(*  parameters) and reducing the rest to a strictly smaller core    *)
(*  at the TOP9 state.                                              *)
(*                                                                  *)
(*  Phase 54 left the ESC side of H_LOOP resting on TAIL2_END9      *)
(*  (Grind22.v): the totality of the TOP8 state                     *)
(*                                                                  *)
(*    TOP8(j, beta) = HB [135142; 27487; 14322; 1260; 147; 20;      *)
(*                    0] 864782 1 1425923 ((2j, 2) :: (1, 1)        *)
(*                    :: (1, 2)^(beta-1))                            *)
(*                                                                  *)
(*  for j >= 1425926.  There the GRIND9 pair (2j - 6, 2) at counter *)
(*  1425922 exceeds the CLEANG_even floor and takes the DIPDESC     *)
(*  boundary a ninth time.  Phase 55 traces the walk                *)
(*  (rocq/hsim55.py, ALL PASS: the 24-waypoint chain below          *)
(*  asserted verbatim at (j, beta) in {(1425926, 2), (1425926, 3),  *)
(*  (1425927, 2), (2000000, 2), (4277778, 2)}; TOP9 finals and the  *)
(*  cycle-10 fence asserted too; a junk-tail probe confirms         *)
(*  CASCADE55 is stated for an arbitrary tail; the full             *)
(*  (1425926, 2) walk was also replayed step by step through the    *)
(*  walker's own macro/prim functions and classified into 25        *)
(*  lemma applications with 0 unclassified runs -- the classifier   *)
(*  itself was first validated by exact reproduction of the         *)
(*  Phase 54 classified chain (184 steps, 0 mismatches) -- and      *)
(*  the CASCADE55 proof script below is generated from that         *)
(*  classification).                                                *)
(*                                                                  *)
(*  FINDING: the ninth descent is again a FIXED parse, uniform      *)
(*  in (j, beta) -- not a return to TOP8, TOP7, ..., or TOP.        *)
(*  Writing r9 = 2j - 2851850 >= 2 for the DIPGRIND residue at      *)
(*  GRIND9:                                                         *)
(*                                                                  *)
(*    TOP8 --front (TUP, hGRIND_even 712959, TUP2_1, TDN, TUP)-->   *)
(*      GRIND9 = HC [864782; 135142; 27487; 14322; 1260; 147;       *)
(*                 20; 0] 1425922 3 2 ((2j - 6, 2) :: tail)         *)
(*    --DIPGRIND (1425922, r9)-->                                   *)
(*      HC [864782; 135142; ...] 0 3 2 ((1, 2)^1425922 ++ W),       *)
(*        W = ((r9, 2) :: (1, 1) :: (1, 2)^(beta - 1))              *)
(*    --CASCADE55 (fixed parse, arbitrary tail)-->                  *)
(*      TOP9 = HB [297773; 149464; 1260; 147; 20; 0]                *)
(*             2020419 1 2851851 W.                                 *)
(*                                                                  *)
(*  CASCADE55 is a MUCH SHORTER parse (17 lemma steps from the      *)
(*  spine: 3 TUP, 2 TDN, 2 pop12, 2 PX2A, 1 DIPGRIND level          *)
(*  (135140, 594496), 1 hGRIND 13741, 1 hGRIND_even 148884,          *)
(*  1 CLEANG_even 297244, 1 PUSH, 1 POP, 1 TUP2_1, 1 TRANS2_1) --   *)
(*  far shorter than CASCADE54 (176 steps): the frame SHRINKS       *)
(*  from seven blocks to six.                                       *)
(*                                                                  *)
(*  TOP9 then closes by the size of r9' = 2 * j9 (j9 = j - 1425925  *)
(*  in TOP9's own parameter):                                       *)
(*    r9' = 2:       TRANS2_1 + CASCADE_POPFIN, A = 2851851 + beta, *)
(*                    frame [2020420; 297773; 149464; ...];         *)
(*    r9' = 4:       TUP + hGRIND_even 1425923 + TRANS2_2           *)
(*                    + CASCADE_POPFIN, A = beta + 2;               *)
(*    r9' = 6:       TUP + hGRIND_even 1425923 + TUP2_1 + TDN       *)
(*                    + TRANS2_1 + CASCADE_POPFIN, A = beta + 4;    *)
(*    8 <= r9' <= 5703706 (band 9): TUP + hGRIND_even 1425923       *)
(*      + TUP2_1 + TDN + TUP onto GRIND10 = HC [2020419; 297773;    *)
(*      ...] 2851850 3 2 ((r9' - 6, 2) :: tail), whose pair grinds  *)
(*      CLEANLY by CLEANG_even (floor (r9' - 8)/2 + 1 <= 2851850,   *)
(*      exactly r9' <= 5703706), then TRANS2_1 + CASCADE_POPFIN,    *)
(*      A = r9' + beta - 2, frame [2851851; 2020419; 297773; ...].  *)
(*      (The band counter is again the shuttle moved into the       *)
(*      counter slot by TUP2_1: 2851850, not 2020419.)              *)
(*                                                                  *)
(*  For r9' >= 5703708 (j9 >= 2851854, i.e. TOP8-parameter          *)
(*  j >= 4277779) the pair (r9' - 6, 2) at counter 2851850 exceeds  *)
(*  the CLEANG_even floor and the rounds take the DIPDESC           *)
(*  boundary a TENTH time (hsim55 Part 3: the GRIND10 state and     *)
(*  the DIPGRIND (2851850, r9' - 5703706) landing both occur at     *)
(*  j = 4277779, 4277780, 4500000).  The tenth descent is expected  *)
(*  to be a NEW cascade with different constants, so no cycle       *)
(*  induction in the current vocabulary closes it; what remains     *)
(*  is the strictly smaller core                                    *)
(*                                                                  *)
(*    TAIL2_END10: the totality of the ONE pair (2j, 2) at the ONE  *)
(*    fixed TOP9 state HB [297773; 149464; 1260; 147; 20; 0]       *)
(*    2020419 1 2851851, for j >= 2851854 (r9' = 2j                 *)
(*    >= 5703708), beta >= 2.                                       *)
(*                                                                  *)
(*  The core's range shrank from [1425926, infty) to [4277779,      *)
(*  infty) in TOP8 parameters; the band width roughly doubled       *)
(*  again (1425926 -> 4277778).  Via TAIL2_END9_of55 +              *)
(*  TAIL2_END8_of54 + ESC_ERA_LAW_54 the ESC instances at every     *)
(*  even R >= 1278 now rest on TAIL2_END10 alone                    *)
(*  (ESC_ERA_LAW_55 below; Loop.v Part 4p).                         *)
(* ================================================================= *)

Require Import List Bool Arith Lia ZArith.
Import ListNotations.
Require Import TM Sections Mirror TokenPass Recoord Era Esc Dev
               Grind Grind2 Grind3 Grind4 Grind5 Grind6 Grind7 Grind8
               Grind9 Grind10 Grind11 Grind12 Grind13 Grind14 Grind15
               Grind16 Grind17 Grind18 Grind19 Grind20 Grind21 Grind22.

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
(* Phase 52-54 pattern, applied from the start at this phase's      *)
(* scale (constants to ~2851851).                                   *)
(* hGRIND_even 1425923 in the TOP9 closings:                        *)
Lemma NUM55a : 2851850 = 2 * 1425923 + 4.
Proof. apply Nat.eqb_eq; vm_compute; reflexivity. Qed.
Lemma NUM55b : 2020419 = S 2020418.
Proof. apply Nat.eqb_eq; vm_compute; reflexivity. Qed.
(* S-form / subtraction identities for the TOP9 closings: the      *)
(* sTRANS2_1, sTUP2_1, sTUP and hTRANS2_2 applies at shuttle        *)
(* 2851851 otherwise force S/subtraction conversions of unary       *)
(* depth ~2851851, which overflow the conversion stack; rewriting   *)
(* the goal's numerals to the lemmas' computed forms first makes    *)
(* the applies syntactic.                                           *)
Lemma NUM55e : 2851851 = S 2851850.
Proof. apply Nat.eqb_eq; vm_compute; reflexivity. Qed.
Lemma NUM55f : 2851852 = S (S 2851850).
Proof. apply Nat.eqb_eq; vm_compute; reflexivity. Qed.
Lemma NUM55g : 2020420 = S 2020419.
Proof. apply Nat.eqb_eq; vm_compute; reflexivity. Qed.
Lemma NUM55h : 2851850 = 2851851 - 1.
Proof. apply Nat.eqb_eq; vm_compute; reflexivity. Qed.
Lemma NUM55i : 2851850 = S 2851849.
Proof. apply Nat.eqb_eq; vm_compute; reflexivity. Qed.
Lemma NUM55j : 2851851 = S (S 2851849).
Proof. apply Nat.eqb_eq; vm_compute; reflexivity. Qed.
Lemma NUM55k : 2851850 = 2851853 - 3.
Proof. apply Nat.eqb_eq; vm_compute; reflexivity. Qed.
Lemma NUM55m : 2851854 = S 2851853.
Proof. apply Nat.eqb_eq; vm_compute; reflexivity. Qed.
Lemma NUM55n : 2851852 = S 2851851.
Proof. apply Nat.eqb_eq; vm_compute; reflexivity. Qed.
(* S-form identities for CASCADE55c step 16 (the closing           *)
(* TRANS2_1 at counter 297772 / shuttle 594494):                    *)
Lemma NUM55u1 : 594494 = S 594493.
Proof. apply Nat.eqb_eq; vm_compute; reflexivity. Qed.
Lemma NUM55u2 : 594495 = S (S 594493).
Proof. apply Nat.eqb_eq; vm_compute; reflexivity. Qed.
Lemma NUM55u3 : 297773 = S 297772.
Proof. apply Nat.eqb_eq; vm_compute; reflexivity. Qed.
(* List identity for CASCADE55a step 1: hPX2A produces the pair   *)
(* list (1, 1) :: (1, 2) :: (1, 2) :: spine, while the stated      *)
(* step target merges the two (1, 2)s into the spine repeat as     *)
(* repeat (1, 2) 1425924.  Unifying the two forms directly makes   *)
(* the conversion recursion run the full 1425922-deep repeat and   *)
(* stack-overflows; the identity is therefore factored here, and   *)
(* step 1 first rewrites its goal with it.  Even the factored      *)
(* identity does not prove by bare reflexivity in this file's      *)
(* environment (the repeat's whnf at the literal 1425924           *)
(* recurses too deep); rewriting the literal to S (S 1425922)      *)
(* first -- via the eqb/vm numeral identity NUM55ss -- keeps the   *)
(* remaining unfoldings shallow.                                   *)
Lemma NUM55ss : 1425924 = S (S 1425922).
Proof. apply Nat.eqb_eq; vm_compute; reflexivity. Qed.
(* S-form identities for CASCADE55a step 1's exact term:          *)
(* hPX2A's frame pattern S (S (S b')) :: S p' :: pb and its        *)
(* target shuttle S b' must convert against the goal's atoms      *)
(* 864782 / 135142 / 864780; atom-vs-S conversion recurses to the   *)
(* atom's depth and overflows at 864782 (Phase 54's identical      *)
(* step at 350961 already needed this treatment).  Step 1 first    *)
(* rewrites the goal's three atoms to S-form via these             *)
(* identities, making the exact term's conversion syntactic.       *)
Lemma NUM55t1 : 864782 = S (S (S 864779)).
Proof. apply Nat.eqb_eq; vm_compute; reflexivity. Qed.
Lemma NUM55t2 : 135142 = S 135141.
Proof. apply Nat.eqb_eq; vm_compute; reflexivity. Qed.
Lemma NUM55t3 : 864780 = S 864779.
Proof. apply Nat.eqb_eq; vm_compute; reflexivity. Qed.
Lemma REP55a : forall w : list (nat * nat),
  (1, 1) :: (1, 2) :: (1, 2) :: repeat (1, 2) 1425922 ++ w
  = (1, 1) :: repeat (1, 2) 1425924 ++ w.
Proof. intro w. rewrite NUM55ss. reflexivity. Qed.
(* ----------------------------------------------------------------- *)
(* CASCADE55: the DIP9 spine over frame [864782; 135142; 27487;    *)
(* 14322; 1260; 147; 20; 0] regrows onto TOP9, for an ARBITRARY     *)
(* tail w.  The proof is an hsteps_trans chain of 17 classified     *)
(* steps (waypoints asserted verbatim in hsim55.py); step kinds     *)
(* are annotated per step.  NOTE (Phase 55, applying the            *)
(* Phase 52-54 lessons proactively): kernel conversion over         *)
(* of_num_uint numerals overflows the default stack at unary depth  *)
(* ~175000, and this phase's constants reach ~2851851, so the chain *)
(* is split from the start into four consecutive sub-lemmas:        *)
(* CASCADE55a (steps 1-8), CASCADE55b (step 9 alone), CASCADE55c    *)
(* (steps 10-16) and CASCADE55d (step 17 alone); CASCADE55 below    *)
(* is their composition, its statement the spine-to-TOP9 step.      *)
(* Steps 9 and 17 are isolated because their pop12 landings         *)
(* (pop12 135142 and pop12 1425924) force the kernel conversions    *)
(* 14322 + 135142 = 149464 / 27489 + 2 * 135142 = 297773 and        *)
(* 594495 + 1425924 = 2020419 / 3 + 2 * 1425924 = 2851851, whose    *)
(* unary depth overflows the conversion stack; the sub-lemmas       *)
(* first rewrite the goal's numerals to pop12's computed form,      *)
(* the equalities being discharged by Nat.eqb_eq + vm_compute       *)
(* (VM-cast conversion).  The two hstep-constructor steps (PX2A     *)
(* at steps 1 and 6) are given as fully explicit                    *)
(* `exact (hsteps_step _ _ _ (hPX2A ...) (hsteps_refl _))` terms    *)
(* rather than `apply hPX2A`: with all constructor arguments left   *)
(* as evars, evarconv thrashes on the 1425922-deep spine repeat     *)
(* (minutes, then stack overflow), while the explicit form checks   *)
(* by plain conversion in seconds.  The head-pair normalisations    *)
(* for the PUSH / TUP / TUP2_1 steps at atoms >= 200000 are         *)
(* factored NUM55X rewrites (atom = g - 2), not `replace ... by     *)
(* sec_eq`: lia cannot reify of_num_uint atoms >= ~646578.  The     *)
(* lemma statements are unchanged; only these proof terms differ    *)
(* in shape from the generated Phase 46-53 pattern.                 *)
(* ----------------------------------------------------------------- *)

(* Closed arithmetic identities for the large DIPGRIND /   *)
(* hGRIND_even / CLEANG steps and the head-pair             *)
(* normalisations of CASCADE55, factored into standalone    *)
(* lemmas (eqb/vm proofs) and rewritten in the step blocks, *)
(* so the applies meet the lemmas' arithmetic forms        *)
(* syntactically instead of by a closed multiplication or   *)
(* subtraction conversion at depth >= 20000                 *)
(* (cf. NUM55ss / REP55a).                                  *)
Lemma NUM55X1 : 864778 = 864780 - 2.
Proof. apply Nat.eqb_eq; vm_compute; reflexivity. Qed.
Lemma NUM55X2 : 864776 = 864778 - 2.
Proof. apply Nat.eqb_eq; vm_compute; reflexivity. Qed.
Lemma NUM55X3 : 864776 = 2 * 135140 + 594496.
Proof. apply Nat.eqb_eq; vm_compute; reflexivity. Qed.
Lemma NUM55X4 : 594494 = 594496 - 2.
Proof. apply Nat.eqb_eq; vm_compute; reflexivity. Qed.
Lemma NUM55X5 : 297772 = 2 * 148884 + 4.
Proof. apply Nat.eqb_eq; vm_compute; reflexivity. Qed.
Lemma NUM55X6 : 594492 = 594494 - 2.
Proof. apply Nat.eqb_eq; vm_compute; reflexivity. Qed.
Lemma NUM55X7 : 594490 = 594492 - 2.
Proof. apply Nat.eqb_eq; vm_compute; reflexivity. Qed.
Lemma NUM55X8 : 594490 = 2 * 297244 + 2.
Proof. apply Nat.eqb_eq; vm_compute; reflexivity. Qed.
Lemma NUM55X9 : 594494 = 2 * 297244 + 6.
Proof. apply Nat.eqb_eq; vm_compute; reflexivity. Qed.

(* CASCADE55a: steps 1-8 of the CASCADE55 chain. *)
Lemma CASCADE55a : forall w,
  hsteps (HC [864782; 135142; 27487; 14322; 1260; 147; 20; 0] 0 3 2 (repeat (1, 2) 1425922 ++ w) 1)
         (HB [1260; 147; 20; 0] 14322 1 27489 (repeat (1, 2) 135142 ++ (594496, 2) :: (1, 1) :: repeat (1, 2) 1425924 ++ w) 1).
Proof.
  intro w.
  (* step 1: P PX2A *)
  apply (hsteps_trans _ (HC [27487; 14322; 1260; 147; 20; 0] 135141 864780 2 ((1, 1) :: repeat (1, 2) 1425924 ++ w) 1)).
  {
    rewrite NUM55t1. rewrite NUM55t2. rewrite NUM55t3.
    replace ((1, 1) :: repeat (1, 2) 1425924 ++ w)
      with ((1, 1) :: (1, 2) :: (1, 2) :: repeat (1, 2) 1425922 ++ w)
      by (apply REP55a).
    exact (hsteps_step _ _ _ (hPX2A 864779 135141 [27487; 14322; 1260; 147; 20; 0] (repeat (1, 2) 1425922 ++ w) 1) (hsteps_refl _)).
  }
  (* step 2: P PUSH *)
  apply (hsteps_trans _ (HC [27487; 14322; 1260; 147; 20; 0] 135140 1 2 ((864778, 2) :: (1, 1) :: repeat (1, 2) 1425924 ++ w) 1)).
  {
    rewrite NUM55X1.
    apply (sPUSH [27487; 14322; 1260; 147; 20; 0] 135140 864780 ((1, 1) :: repeat (1, 2) 1425924 ++ w) 1); closearith.
  }
  (* step 3: P TDN *)
  apply (hsteps_trans _ (HB [27487; 14322; 1260; 147; 20; 0] 135140 1 4 ((864778, 2) :: (1, 1) :: repeat (1, 2) 1425924 ++ w) 1)).
  {
    apply (sTDN [27487; 14322; 1260; 147; 20; 0] 135140 ((864778, 2) :: (1, 1) :: repeat (1, 2) 1425924 ++ w) 1).
  }
  (* step 4: sTUP *)
  apply (hsteps_trans _ (HC [27487; 14322; 1260; 147; 20; 0] 135140 3 2 ((864776, 2) :: (1, 1) :: repeat (1, 2) 1425924 ++ w) 1)).
  {
    rewrite NUM55X2.
    apply (sTUP [27487; 14322; 1260; 147; 20; 0] 135140 4 864778 2 ((1, 1) :: repeat (1, 2) 1425924 ++ w) 1); closearith.
  }
  (* step 5: DIPGRIND 135140 594496 *)
  apply (hsteps_trans _ (HC [27487; 14322; 1260; 147; 20; 0] 0 3 2 (repeat (1, 2) 135140 ++ (594496, 2) :: (1, 1) :: repeat (1, 2) 1425924 ++ w) 1)).
  {
    rewrite NUM55X3.
    apply (DIPGRIND 135140 594496 [27487; 14322; 1260; 147; 20; 0] ((1, 1) :: repeat (1, 2) 1425924 ++ w) 1); closearith.
  }
  (* step 6: P PX2A *)
  apply (hsteps_trans _ (HC [1260; 147; 20; 0] 14321 27485 2 ((1, 1) :: repeat (1, 2) 135142 ++ (594496, 2) :: (1, 1) :: repeat (1, 2) 1425924 ++ w) 1)).
  {
    exact (hsteps_step _ _ _ (hPX2A 27484 14321 [1260; 147; 20; 0] (repeat (1, 2) 135140 ++ (594496, 2) :: (1, 1) :: repeat (1, 2) 1425924 ++ w) 1) (hsteps_refl _)).
  }
  (* step 7: hGRIND 13741 *)
  apply (hsteps_trans _ (HB [1260; 147; 20; 0] 14321 1 27488 ((1, 1) :: repeat (1, 2) 135142 ++ (594496, 2) :: (1, 1) :: repeat (1, 2) 1425924 ++ w) 1)).
  {
    apply (hGRIND 13741 [1260; 147; 20; 0] 14321 ((1, 1) :: repeat (1, 2) 135142 ++ (594496, 2) :: (1, 1) :: repeat (1, 2) 1425924 ++ w) 1); closearith.
  }
  (* step 8: P POP *)
  apply (sPOP1 [1260; 147; 20; 0] 14321 27488 (repeat (1, 2) 135142 ++ (594496, 2) :: (1, 1) :: repeat (1, 2) 1425924 ++ w) 1); closearith.
Qed.

(* CASCADE55b: steps 9-9 of the CASCADE55 chain. *)
Lemma CASCADE55b : forall w,
  hsteps (HB [1260; 147; 20; 0] 14322 1 27489 (repeat (1, 2) 135142 ++ (594496, 2) :: (1, 1) :: repeat (1, 2) 1425924 ++ w) 1)
         (HB [1260; 147; 20; 0] 149464 1 297773 ((594496, 2) :: (1, 1) :: repeat (1, 2) 1425924 ++ w) 1).
Proof.
  intro w.
  replace 149464 with (14322 + 135142)
    by (apply Nat.eqb_eq; vm_compute; reflexivity).
  replace 297773 with (27489 + 2 * 135142)
    by (apply Nat.eqb_eq; vm_compute; reflexivity).
  (* step 9: M pop12 (135142,) *)
  apply (pop12 135142 [1260; 147; 20; 0] 14322 27489 ((594496, 2) :: (1, 1) :: repeat (1, 2) 1425924 ++ w) 1); closearith.
Qed.

(* CASCADE55c: steps 10-16 of the CASCADE55 chain. *)
Lemma CASCADE55c : forall w,
  hsteps (HB [1260; 147; 20; 0] 149464 1 297773 ((594496, 2) :: (1, 1) :: repeat (1, 2) 1425924 ++ w) 1)
         (HB [297773; 149464; 1260; 147; 20; 0] 594495 1 3 (repeat (1, 2) 1425924 ++ w) 1).
Proof.
  intro w.
  (* step 10: sTUP *)
  apply (hsteps_trans _ (HC [1260; 147; 20; 0] 149464 297772 2 ((594494, 2) :: (1, 1) :: repeat (1, 2) 1425924 ++ w) 1)).
  {
    rewrite NUM55X4.
    apply (sTUP [1260; 147; 20; 0] 149464 297773 594496 2 ((1, 1) :: repeat (1, 2) 1425924 ++ w) 1); closearith.
  }
  (* step 11: hGRIND_even 148884 *)
  apply (hsteps_trans _ (HB [1260; 147; 20; 0] 149463 1 297772 ((2, 2) :: (594494, 2) :: (1, 1) :: repeat (1, 2) 1425924 ++ w) 1)).
  {
    rewrite NUM55X5.
    apply (hGRIND_even 148884 [1260; 147; 20; 0] 149463 ((594494, 2) :: (1, 1) :: repeat (1, 2) 1425924 ++ w) 1); closearith.
  }
  (* step 12: P TUP2_1 *)
  apply (hsteps_trans _ (HC [149464; 1260; 147; 20; 0] 297772 1 2 ((594492, 2) :: (1, 1) :: repeat (1, 2) 1425924 ++ w) 1)).
  {
    rewrite NUM55X6.
    apply (sTUP2_1 [1260; 147; 20; 0] 149463 297771 594494 ((1, 1) :: repeat (1, 2) 1425924 ++ w) 1); closearith.
  }
  (* step 13: P TDN *)
  apply (hsteps_trans _ (HB [149464; 1260; 147; 20; 0] 297772 1 4 ((594492, 2) :: (1, 1) :: repeat (1, 2) 1425924 ++ w) 1)).
  {
    apply (sTDN [149464; 1260; 147; 20; 0] 297772 ((594492, 2) :: (1, 1) :: repeat (1, 2) 1425924 ++ w) 1).
  }
  (* step 14: sTUP *)
  apply (hsteps_trans _ (HC [149464; 1260; 147; 20; 0] 297772 3 2 ((594490, 2) :: (1, 1) :: repeat (1, 2) 1425924 ++ w) 1)).
  {
    rewrite NUM55X7.
    apply (sTUP [149464; 1260; 147; 20; 0] 297772 4 594492 2 ((1, 1) :: repeat (1, 2) 1425924 ++ w) 1); closearith.
  }
  (* step 15: CLEANG_even 297244 *)
  apply (hsteps_trans _ (HB [149464; 1260; 147; 20; 0] 297772 1 594494 ((2, 2) :: (1, 1) :: repeat (1, 2) 1425924 ++ w) 1)).
  {
    rewrite NUM55X8.
    rewrite NUM55X9.
    apply (CLEANG_even 297244 [149464; 1260; 147; 20; 0] 297772 ((1, 1) :: repeat (1, 2) 1425924 ++ w) 1); closearith.
  }
  (* step 16: P TRANS2_1 *)
  rewrite NUM55u1. rewrite NUM55u2. rewrite NUM55u3.
  apply (sTRANS2_1 [149464; 1260; 147; 20; 0] 297772 594493 1 (repeat (1, 2) 1425924 ++ w) 1); closearith.
Qed.

(* CASCADE55d: steps 17-17 of the CASCADE55 chain. *)
Lemma CASCADE55d : forall w,
  hsteps (HB [297773; 149464; 1260; 147; 20; 0] 594495 1 3 (repeat (1, 2) 1425924 ++ w) 1)
         (HB [297773; 149464; 1260; 147; 20; 0] 2020419 1 2851851 (w) 1).
Proof.
  intro w.
  replace 2020419 with (594495 + 1425924)
    by (apply Nat.eqb_eq; vm_compute; reflexivity).
  replace 2851851 with (3 + 2 * 1425924)
    by (apply Nat.eqb_eq; vm_compute; reflexivity).
  (* step 17: M pop12 (1425924,) *)
  apply (pop12 1425924 [297773; 149464; 1260; 147; 20; 0] 594495 3 (w) 1); closearith.
Qed.

Lemma CASCADE55 : forall w,
  hsteps (HC [864782; 135142; 27487; 14322; 1260; 147; 20; 0] 0 3 2 (repeat (1, 2) 1425922 ++ w) 1)
         (HB [297773; 149464; 1260; 147; 20; 0] 2020419 1 2851851 (w) 1).
Proof.
  intro w.
  apply (hsteps_trans _ (HB [1260; 147; 20; 0] 14322 1 27489 (repeat (1, 2) 135142 ++ (594496, 2) :: (1, 1) :: repeat (1, 2) 1425924 ++ w) 1)).
  { apply (CASCADE55a w). }
  apply (hsteps_trans _ (HB [1260; 147; 20; 0] 149464 1 297773 ((594496, 2) :: (1, 1) :: repeat (1, 2) 1425924 ++ w) 1)).
  { apply (CASCADE55b w). }
  apply (hsteps_trans _ (HB [297773; 149464; 1260; 147; 20; 0] 594495 1 3 (repeat (1, 2) 1425924 ++ w) 1)).
  { apply (CASCADE55c w). }
  apply (CASCADE55d w).
Qed.
(* ----------------------------------------------------------------- *)
(* TOP55_TO_TOP9: TOP8's front (TUP + hGRIND_even 712959 +         *)
(* TUP2_1 + TDN + TUP) reaches GRIND9, DIPGRIND (1425922,          *)
(* 2 * (j - 1425925)) lands on the DIP9 spine, and CASCADE55        *)
(* regrows the stack onto TOP9.  Numeral hygiene (Phase 52          *)
(* lesson, applied proactively at this phase's doubled scale):     *)
(* the 1425925/1425926 atoms are normalised onto the single atom    *)
(* 1425922 by eqb/vm-proved rewrites, not `change` (the             *)
(* S/subtraction conversions at depth ~1425926 overflow the         *)
(* conversion stack, cf. the TAIL2_END6_of52 fix-up in              *)
(* Grind20.v); the hGRIND_even step rewrites the goal by the        *)
(* standalone identities NUM54c / NUM54d (1425922 = 2 * 712959 + 4, *)
(* 864782 = S 864781, both inherited from Grind22.v), and the       *)
(* first TUP / TUP2_1 steps rewrite via NUM54h / NUM54k.            *)
(* ----------------------------------------------------------------- *)

Lemma TOP55_TO_TOP9 : forall j beta, 1425926 <= j -> 2 <= beta ->
  hsteps (HB [135142; 27487; 14322; 1260; 147; 20; 0] 864782 1 1425923
            ((2 * j, 2) :: (1, 1) :: repeat (1, 2) (beta - 1)) 1)
         (HB [297773; 149464; 1260; 147; 20; 0] 2020419 1 2851851
            ((2 * (j - 1425925), 2) :: (1, 1)
             :: repeat (1, 2) (beta - 1)) 1).
Proof.
  intros j beta Hj Hb.
  assert (Hj4 : 4 <= j).
  { apply Nat.le_trans with 1425926; [closearith | exact Hj]. }
  assert (Hr : 1 <= j - 1425925).
  { assert (E : 1425925 = 1425926 - 1)
      by (apply Nat.eqb_eq; vm_compute; reflexivity).
    rewrite E. lia. }
  assert (Heq : 2 * j - 6 = 2 * 1425922 + 2 * (j - 1425925)).
  { assert (E1 : 1425925 = 1425922 + 3)
      by (apply Nat.eqb_eq; vm_compute; reflexivity).
    assert (E2 : 1425926 = 1425922 + 4)
      by (apply Nat.eqb_eq; vm_compute; reflexivity).
    rewrite E1. rewrite E2 in Hj. lia. }
  apply (hsteps_trans _ (HC [135142; 27487; 14322; 1260; 147; 20; 0] 864782
    1425922 2 ((2 * j - 2, 2) :: (1, 1) :: repeat (1, 2) (beta - 1)) 1)).
  { rewrite NUM54h.
    apply (sTUP [135142; 27487; 14322; 1260; 147; 20; 0] 864782 1425923 (2 * j) 2
           ((1, 1) :: repeat (1, 2) (beta - 1)) 1); closearith. }
  apply (hsteps_trans _ (HB [135142; 27487; 14322; 1260; 147; 20; 0] 864781
    1 1425922 ((2, 2) :: (2 * j - 2, 2) :: (1, 1)
            :: repeat (1, 2) (beta - 1)) 1)).
  { rewrite NUM54c. rewrite NUM54d.
    apply (hGRIND_even 712959 [135142; 27487; 14322; 1260; 147; 20; 0]
           864781 ((2 * j - 2, 2) :: (1, 1) :: repeat (1, 2) (beta - 1))
           1); closearith. }
  apply (hsteps_trans _ (HC [864782; 135142; 27487; 14322; 1260; 147; 20; 0] 1425922 1 2 ((2 * j - 4, 2) :: (1, 1)
            :: repeat (1, 2) (beta - 1)) 1)).
  { rewrite NUM54k. rewrite NUM54d.
    replace ((2 * j - 4, 2) :: (1, 1) :: repeat (1, 2) (beta - 1))
      with ((2 * j - 2 - 2, 2) :: (1, 1) :: repeat (1, 2) (beta - 1))
      by sec_eq.
    apply (sTUP2_1 [135142; 27487; 14322; 1260; 147; 20; 0] 864781
           1425921 (2 * j - 2) ((1, 1) :: repeat (1, 2) (beta - 1)) 1); lia. }
  apply (hsteps_trans _ (HB [864782; 135142; 27487; 14322; 1260; 147; 20; 0] 1425922 1 4 ((2 * j - 4, 2) :: (1, 1)
            :: repeat (1, 2) (beta - 1)) 1)).
  { apply (sTDN [864782; 135142; 27487; 14322; 1260; 147; 20; 0] 1425922
           ((2 * j - 4, 2) :: (1, 1) :: repeat (1, 2) (beta - 1))
           1). }
  apply (hsteps_trans _ (HC [864782; 135142; 27487; 14322; 1260; 147; 20; 0] 1425922 3 2 ((2 * j - 6, 2) :: (1, 1)
            :: repeat (1, 2) (beta - 1)) 1)).
  { replace ((2 * j - 6, 2) :: (1, 1) :: repeat (1, 2) (beta - 1))
      with ((2 * j - 4 - 2, 2) :: (1, 1) :: repeat (1, 2) (beta - 1))
      by sec_eq.
    apply (sTUP [864782; 135142; 27487; 14322; 1260; 147; 20; 0] 1425922 4
           (2 * j - 4) 2 ((1, 1) :: repeat (1, 2) (beta - 1)) 1);
      lia. }
  apply (hsteps_trans _ (HC [864782; 135142; 27487; 14322; 1260; 147; 20; 0]
    0 3 2 (repeat (1, 2) 1425922
     ++ ((2 * (j - 1425925), 2) :: (1, 1)
         :: repeat (1, 2) (beta - 1))) 1)).
  { rewrite Heq.
    apply (DIPGRIND 1425922 (2 * (j - 1425925))
           [864782; 135142; 27487; 14322; 1260; 147; 20; 0]
           ((1, 1) :: repeat (1, 2) (beta - 1)) 1);
      [closearith | lia]. }
  apply (CASCADE55 ((2 * (j - 1425925), 2) :: (1, 1)
                    :: repeat (1, 2) (beta - 1))).
Qed.

(* ----------------------------------------------------------------- *)
(* The TOP9 closings: r9' = 2, 4, 6 and band 9 (8 <= r9' <= 5703706). *)
(* ----------------------------------------------------------------- *)

Lemma TOP55_2 : forall beta, 2 <= beta ->
  hsteps (HB [297773; 149464; 1260; 147; 20; 0] 2020419 1 2851851
            ((2, 2) :: (1, 1) :: repeat (1, 2) (beta - 1)) 1)
         (HB [2020420; 297773; 149464; 1260; 147; 20; 0]
            (2851852 + (beta - 1)) 1 (2 * beta + 1) [] 1).
Proof.
  intros beta Hb.
  apply (hsteps_trans _ (HB [2020420; 297773; 149464; 1260; 147; 20; 0] 2851852 1 3 (repeat (1, 2) (beta - 1)) 1)).
  { rewrite NUM55e. rewrite NUM55f. rewrite NUM55g.
    apply (sTRANS2_1 [297773; 149464; 1260; 147; 20; 0] 2020419
           2851850 1 (repeat (1, 2) (beta - 1)) 1); lia. }
  apply (CASCADE_POPFIN [2020420; 297773; 149464; 1260; 147; 20; 0] 2851852 beta); lia.
Qed.

(* NOTE (Phase 55, proactive): in TOP55_4, TOP55_6 and TOP55_BAND  *)
(* the hGRIND_even 1425923 step is preceded by two goal rewrites     *)
(* via the standalone identities NUM55a (2851850 = 2 * 1425923 + 4)  *)
(* and NUM55b (2020419 = S 2020418) -- the Phase 52 fix-up pattern   *)
(* for TOP54_4/6/BAND's hGRIND_even 712959 step, applied from the    *)
(* start at this phase's doubled scale, with the identities          *)
(* factored into lemmas because the inline `replace ... by           *)
(* (eqb/vm ...)` form stack-overflows in this file's long            *)
(* hsteps_trans chains (see the NUM55 note in the header).  The      *)
(* step applies themselves are unchanged.                            *)

Lemma TOP55_4 : forall beta, 2 <= beta ->
  hsteps (HB [297773; 149464; 1260; 147; 20; 0] 2020419 1 2851851
            ((4, 2) :: (1, 1) :: repeat (1, 2) (beta - 1)) 1)
         (HB [2851851; 2020419; 297773; 149464; 1260; 147; 20; 0]
            (beta + 2) 1 (2 * beta + 1) [] 1).
Proof.
  intros beta Hb.
  apply (hsteps_trans _ (HC [297773; 149464; 1260; 147; 20; 0]
    2020419 2851850 2
    ((2, 2) :: (1, 1) :: repeat (1, 2) (beta - 1)) 1)).
  { rewrite NUM55h.
    apply (sTUP [297773; 149464; 1260; 147; 20; 0] 2020419 2851851
           4 2 ((1, 1) :: repeat (1, 2) (beta - 1)) 1); closearith. }
  apply (hsteps_trans _ (HB [297773; 149464; 1260; 147; 20; 0]
    2020418 1 2851850 ((2, 2) :: (2, 2) :: (1, 1)
            :: repeat (1, 2) (beta - 1)) 1)).
  { rewrite NUM55a. rewrite NUM55b.
    apply (hGRIND_even 1425923 [297773; 149464; 1260; 147; 20; 0]
           2020418 ((2, 2) :: (1, 1) :: repeat (1, 2) (beta - 1)) 1);
      closearith. }
  apply (hsteps_trans _ (HB [2851851; 2020419; 297773; 149464; 1260; 147; 20; 0] 3 1 3 (repeat (1, 2) (beta - 1)) 1)).
  { rewrite NUM55i. rewrite NUM55j. rewrite NUM55b.
    apply (hsteps_step _ (HB [S (S 2851849); S 2020418; 297773; 149464; 1260; 147; 20; 0] 3 1 3 (repeat (1, 2) (beta - 1)) 1));
      [apply hTRANS2_2; closearith | apply hsteps_refl]. }
  replace (beta + 2) with (3 + (beta - 1)) by lia.
  apply (CASCADE_POPFIN [2851851; 2020419; 297773; 149464; 1260; 147; 20; 0] 3 beta); lia.
Qed.

Lemma TOP55_6 : forall beta, 2 <= beta ->
  hsteps (HB [297773; 149464; 1260; 147; 20; 0] 2020419 1 2851851
            ((6, 2) :: (1, 1) :: repeat (1, 2) (beta - 1)) 1)
         (HB [2851851; 2020419; 297773; 149464; 1260; 147; 20; 0]
            (beta + 4) 1 (2 * beta + 1) [] 1).
Proof.
  intros beta Hb.
  apply (hsteps_trans _ (HC [297773; 149464; 1260; 147; 20; 0]
    2020419 2851850 2
    ((4, 2) :: (1, 1) :: repeat (1, 2) (beta - 1)) 1)).
  { rewrite NUM55h.
    apply (sTUP [297773; 149464; 1260; 147; 20; 0] 2020419 2851851
           6 2 ((1, 1) :: repeat (1, 2) (beta - 1)) 1); closearith. }
  apply (hsteps_trans _ (HB [297773; 149464; 1260; 147; 20; 0]
    2020418 1 2851850 ((2, 2) :: (4, 2) :: (1, 1)
            :: repeat (1, 2) (beta - 1)) 1)).
  { rewrite NUM55a. rewrite NUM55b.
    apply (hGRIND_even 1425923 [297773; 149464; 1260; 147; 20; 0]
           2020418 ((4, 2) :: (1, 1) :: repeat (1, 2) (beta - 1)) 1);
      closearith. }
  apply (hsteps_trans _ (HC [2020419; 297773; 149464; 1260; 147; 20; 0] 2851850 1 2
    ((2, 2) :: (1, 1) :: repeat (1, 2) (beta - 1)) 1)).
  { rewrite NUM55i. rewrite NUM55b.
    replace ((2, 2) :: (1, 1) :: repeat (1, 2) (beta - 1))
      with ((4 - 2, 2) :: (1, 1) :: repeat (1, 2) (beta - 1))
      by sec_eq.
    apply (sTUP2_1 [297773; 149464; 1260; 147; 20; 0] 2020418
           2851849 4 ((1, 1) :: repeat (1, 2) (beta - 1)) 1); lia. }
  apply (hsteps_trans _ (HB [2020419; 297773; 149464; 1260; 147; 20; 0] 2851850 1 4
    ((2, 2) :: (1, 1) :: repeat (1, 2) (beta - 1)) 1)).
  { apply (sTDN [2020419; 297773; 149464; 1260; 147; 20; 0] 2851850
           ((2, 2) :: (1, 1) :: repeat (1, 2) (beta - 1))
           1). }
  apply (hsteps_trans _ (HB [2851851; 2020419; 297773; 149464; 1260; 147; 20; 0] 5 1 3 (repeat (1, 2) (beta - 1)) 1)).
  { rewrite NUM55e.
    apply (sTRANS2_1 [2020419; 297773; 149464; 1260; 147; 20; 0]
           2851850 3 1 (repeat (1, 2) (beta - 1)) 1); lia. }
  replace (beta + 4) with (5 + (beta - 1)) by lia.
  apply (CASCADE_POPFIN [2851851; 2020419; 297773; 149464; 1260; 147; 20; 0] 5 beta); lia.
Qed.

Lemma TOP55_BAND : forall j beta, 4 <= j -> j <= 2851853 -> 2 <= beta ->
  hsteps (HB [297773; 149464; 1260; 147; 20; 0] 2020419 1 2851851
            ((2 * j, 2) :: (1, 1) :: repeat (1, 2) (beta - 1)) 1)
         (HB [2851851; 2020419; 297773; 149464; 1260; 147; 20; 0]
            (2 * j + beta - 2) 1 (2 * beta + 1) [] 1).
Proof.
  intros j beta Hj1 Hj2 Hb.
  apply (hsteps_trans _ (HC [297773; 149464; 1260; 147; 20; 0]
    2020419 2851850 2 ((2 * j - 2, 2) :: (1, 1)
            :: repeat (1, 2) (beta - 1)) 1)).
  { rewrite NUM55h.
    apply (sTUP [297773; 149464; 1260; 147; 20; 0] 2020419 2851851
           (2 * j) 2 ((1, 1) :: repeat (1, 2) (beta - 1)) 1);
      closearith. }
  apply (hsteps_trans _ (HB [297773; 149464; 1260; 147; 20; 0]
    2020418 1 2851850 ((2, 2) :: (2 * j - 2, 2) :: (1, 1)
            :: repeat (1, 2) (beta - 1)) 1)).
  { rewrite NUM55a. rewrite NUM55b.
    apply (hGRIND_even 1425923 [297773; 149464; 1260; 147; 20; 0]
           2020418 ((2 * j - 2, 2) :: (1, 1)
           :: repeat (1, 2) (beta - 1)) 1); closearith. }
  apply (hsteps_trans _ (HC [2020419; 297773; 149464; 1260; 147; 20; 0] 2851850 1 2 ((2 * j - 4, 2) :: (1, 1)
            :: repeat (1, 2) (beta - 1)) 1)).
  { rewrite NUM55i. rewrite NUM55b.
    replace ((2 * j - 4, 2) :: (1, 1) :: repeat (1, 2) (beta - 1))
      with ((2 * j - 2 - 2, 2) :: (1, 1)
            :: repeat (1, 2) (beta - 1)) by sec_eq.
    apply (sTUP2_1 [297773; 149464; 1260; 147; 20; 0] 2020418
           2851849 (2 * j - 2) ((1, 1) :: repeat (1, 2) (beta - 1))
           1); lia. }
  apply (hsteps_trans _ (HB [2020419; 297773; 149464; 1260; 147; 20; 0] 2851850 1 4 ((2 * j - 4, 2) :: (1, 1)
            :: repeat (1, 2) (beta - 1)) 1)).
  { apply (sTDN [2020419; 297773; 149464; 1260; 147; 20; 0] 2851850
           ((2 * j - 4, 2) :: (1, 1) :: repeat (1, 2) (beta - 1))
           1). }
  apply (hsteps_trans _ (HC [2020419; 297773; 149464; 1260; 147; 20; 0] 2851850 3 2 ((2 * j - 6, 2) :: (1, 1)
            :: repeat (1, 2) (beta - 1)) 1)).
  { replace ((2 * j - 6, 2) :: (1, 1) :: repeat (1, 2) (beta - 1))
      with ((2 * j - 4 - 2, 2) :: (1, 1)
            :: repeat (1, 2) (beta - 1)) by sec_eq.
    apply (sTUP [2020419; 297773; 149464; 1260; 147; 20; 0] 2851850
           4 (2 * j - 4) 2 ((1, 1) :: repeat (1, 2) (beta - 1)) 1);
      lia. }
  apply (hsteps_trans _ (HB [2020419; 297773; 149464; 1260; 147; 20; 0] 2851850 1 (2 * j - 2)
    ((2, 2) :: (1, 1) :: repeat (1, 2) (beta - 1)) 1)).
  { replace (2 * j - 6) with (2 * (j - 4) + 2) by lia.
    replace (2 * j - 2) with (2 * (j - 4) + 6) by lia.
    apply (CLEANG_even (j - 4) [2020419; 297773; 149464; 1260; 147; 20; 0] 2851850 ((1, 1) :: repeat (1, 2) (beta - 1))
           1).
    (* the floor (j - 4) + 1 <= 2851850: route via j <= 2851853 *)
    apply Nat.le_trans with (j - 3).
    - lia.
    - rewrite NUM55k.
      apply Nat.sub_le_mono_r. exact Hj2. }
  apply (hsteps_trans _ (HB [2851851; 2020419; 297773; 149464; 1260; 147; 20; 0] (2 * j - 1) 1 3 (repeat (1, 2) (beta - 1)) 1)).
  { replace (2 * j - 2) with (S (2 * j - 3)) by lia.
    replace (2 * j - 1) with (S (S (2 * j - 3))) by lia.
    rewrite NUM55e.
    apply (sTRANS2_1 [2020419; 297773; 149464; 1260; 147; 20; 0]
           2851850 (2 * j - 3) 1 (repeat (1, 2) (beta - 1)) 1); lia. }
  replace (2 * j + beta - 2) with (2 * j - 1 + (beta - 1)) by lia.
  apply (CASCADE_POPFIN [2851851; 2020419; 297773; 149464; 1260; 147; 20; 0] (2 * j - 1) beta); lia.
Qed.

(* ----------------------------------------------------------------- *)
(* TAIL2_END10: the strictly smaller residual core -- the totality  *)
(* of the TOP9 state for r9' = 2 * j, j >= 2851854 (r9' >= 5703708), *)
(* where the GRIND10 pair (r9' - 6, 2) at counter 2851850 takes the  *)
(* DIPDESC boundary a tenth time.  A Definition (lemma              *)
(* parameter), never an axiom.                                      *)
(* ----------------------------------------------------------------- *)

Definition TAIL2_END10 : Prop :=
  forall j beta, 2851854 <= j -> 2 <= beta ->
  exists pb A, beta <= A /\
    hsteps (HB [297773; 149464; 1260; 147; 20; 0] 2020419 1 2851851
              ((2 * j, 2) :: (1, 1) :: repeat (1, 2) (beta - 1)) 1)
           (HB pb A 1 (2 * beta + 1) [] 1).

(* ----------------------------------------------------------------- *)
(* TAIL2_END9_of55: TAIL2_END9, modulo TAIL2_END10.  The j-range    *)
(* splits at r9' = 2 * (j - 1425925): the three small cases and      *)
(* band 9 are proved above; j - 1425925 >= 2851854 is the core.      *)
(* (Numeral hygiene: the `change N with (S (N-1))` steps of the     *)
(* Phase 52 analogue at N = 323290 / 323288 are here at             *)
(* N = 2851854 / 2851852 / 1425926 -- all replaced by eqb/vm-proved  *)
(* equality rewrites, since the S-conversions at these depths       *)
(* overflow the conversion stack.)                                  *)
(* ----------------------------------------------------------------- *)

Lemma TAIL2_END9_of55 : TAIL2_END10 -> TAIL2_END9.
Proof.
  intros H10 j beta Hj Hb.
  pose proof (TOP55_TO_TOP9 j beta Hj Hb) as Htop.
  destruct (le_lt_dec 2851854 (j - 1425925)) as [Hbig | Hsmall].
  - (* j9 = j - 1425925 >= 2851854: the core *)
    destruct (H10 (j - 1425925) beta Hbig Hb)
      as [pb [A [Ha Hsteps]]].
    exists pb, A. split; [exact Ha |].
    exact (hsteps_trans _ _ _ Htop Hsteps).
  - destruct (le_lt_dec 4 (j - 1425925)) as [Hband | Htiny].
    + (* band 9: j9 = j - 1425925, 4 <= j9 <= 2851853 *)
      exists [2851851; 2020419; 297773; 149464; 1260; 147; 20; 0],
        (2 * (j - 1425925) + beta - 2).
      split; [lia |].
      assert (Hj2 : j - 1425925 <= 2851853).
      { rewrite NUM55m in Hsmall.
        apply (proj1 (Nat.lt_succ_r _ _) Hsmall). }
      exact (hsteps_trans _ _ _ Htop
               (TOP55_BAND (j - 1425925) beta Hband Hj2 Hb)).
    + (* tiny: j9 = j - 1425925 <= 3; j9 >= 1 since 1425926 <= j *)
      destruct (Nat.eq_dec (j - 1425925) 1) as [He | Hne].
      * (* r9' = 2 *)
        rewrite He in Htop.
        exists [2020420; 297773; 149464; 1260; 147; 20; 0],
          (2851852 + (beta - 1)).
        split; [rewrite NUM55n; lia |].
        exact (hsteps_trans _ _ _ Htop (TOP55_2 beta Hb)).
      * destruct (Nat.eq_dec (j - 1425925) 2) as [He | Hne'].
        -- (* r9' = 4 *)
           rewrite He in Htop.
           exists [2851851; 2020419; 297773; 149464; 1260; 147; 20; 0], (beta + 2).
           split; [lia |].
           exact (hsteps_trans _ _ _ Htop (TOP55_4 beta Hb)).
        -- destruct (Nat.eq_dec (j - 1425925) 3) as [He | Hne''].
           ++ (* r9' = 6 *)
              rewrite He in Htop.
              exists [2851851; 2020419; 297773; 149464; 1260; 147; 20; 0], (beta + 4).
              split; [lia |].
              exact (hsteps_trans _ _ _ Htop (TOP55_6 beta Hb)).
           ++ (* j9 = 0, contradicting 1425926 <= j *)
              exfalso.
              assert (H0 : j - 1425925 = 0) by lia.
              rewrite NUM54q in Hj.
              lia.
Qed.

(* ----------------------------------------------------------------- *)
(* ESC_ERA_LAW_55: the phase-8 ESC era law at every even            *)
(* R >= 1278 (M >= 616), modulo TAIL2_END10 alone.                  *)
(* ----------------------------------------------------------------- *)

Lemma ESC_ERA_LAW_55 : TAIL2_END10 ->
  forall M beta, 616 <= M -> 2 <= beta ->
  exists n c pb a,
    run n (esc_src (2 * M + 52) (beta - 2)) = Some c
    /\ cfg_sim c (rcsec (false :: repeat true (S a) ++ enc pb)
                        (2 * beta + 2) [(1, 2)])
    /\ beta <= a.
Proof.
  intros H M beta HM Hb.
  apply (ESC_ERA_LAW_54 (TAIL2_END9_of55 H) M beta HM Hb).
Qed.

(* ----------------------------------------------------------------- *)
(* Assumption audit                                                  *)
(* ----------------------------------------------------------------- *)

Print Assumptions CASCADE55.
Print Assumptions TOP55_TO_TOP9.
Print Assumptions TOP55_2.
Print Assumptions TOP55_4.
Print Assumptions TOP55_6.
Print Assumptions TOP55_BAND.
Print Assumptions TAIL2_END9_of55.
Print Assumptions ESC_ERA_LAW_55.
