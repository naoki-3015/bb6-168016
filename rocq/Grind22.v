(* ================================================================= *)
(*  Grind22.v -- Phase 54: the eighth re-descent cascade of the     *)
(*  TOP7 state, mechanised as a fixed parse, closing TAIL2_END8     *)
(*  for the whole first j-band 646582 <= j <= 2072506 (TOP7         *)
(*  parameters) and reducing the rest to a strictly smaller core    *)
(*  at the TOP8 state.                                              *)
(*                                                                  *)
(*  Phase 53 left the ESC side of H_LOOP resting on TAIL2_END8      *)
(*  (Grind21.v): the totality of the TOP7 state                     *)
(*                                                                  *)
(*    TOP7(j, beta) = HB [109099; 62236; 6030; 630; 191; 113;       *)
(*                    33; 19; 0] 350961 1 646579 ((2j, 2) :: (1, 1) *)
(*                    :: (1, 2)^(beta-1))                            *)
(*                                                                  *)
(*  for j >= 646582.  There the GRIND8 pair (2j - 6, 2) at counter  *)
(*  646578 exceeds the CLEANG_even floor and takes the DIPDESC      *)
(*  boundary an eighth time.  Phase 54 traces the walk              *)
(*  (rocq/hsim54.py, ALL PASS: the 182-waypoint chain below         *)
(*  asserted verbatim at (j, beta) in {(646582, 2), (646582, 3),    *)
(*  (646583, 2), (800000, 2), (2072506, 2)}; TOP8 finals and the     *)
(*  cycle-9 fence asserted too; a junk-tail probe confirms          *)
(*  CASCADE54 is stated for an arbitrary tail; the full             *)
(*  (646582, 2) walk was also replayed step by step through the     *)
(*  walker's own macro/prim functions and classified into 184       *)
(*  lemma applications with 0 unclassified runs -- the classifier   *)
(*  itself was first validated by exact reproduction of the         *)
(*  Phase 53 classified chain (345 steps, 0 mismatches) -- and      *)
(*  the CASCADE54 proof script below is generated from that         *)
(*  classification).                                                *)
(*                                                                  *)
(*  FINDING: the eighth descent is again a FIXED parse, uniform     *)
(*  in (j, beta) -- not a return to TOP7, TOP6, ..., or TOP.        *)
(*  Writing r8 = 2j - 1293162 >= 2 for the DIPGRIND residue at      *)
(*  GRIND8:                                                         *)
(*                                                                  *)
(*    TOP7 --front (TUP, hGRIND_even 323287, TUP2_1, TDN, TUP)-->   *)
(*      GRIND8 = HC [350961; 109099; 62236; 6030; 630; 191;         *)
(*                 113; 33; 19; 0] 646578 3 2 ((2j - 6, 2) :: tail) *)
(*    --DIPGRIND (646578, r8)-->                                    *)
(*      HC [350961; 109099; ...] 0 3 2 ((1, 2)^646578 ++ W),        *)
(*        W = ((r8, 2) :: (1, 1) :: (1, 2)^(beta - 1))              *)
(*    --CASCADE54 (fixed parse, arbitrary tail)-->                  *)
(*      TOP8 = HB [135142; 27487; 14322; 1260; 147; 20; 0]          *)
(*             864782 1 1425923 W.                                  *)
(*                                                                  *)
(*  CASCADE54 is a SHORTER parse (176 lemma steps from the spine:   *)
(*  39 TUP, 26 TDN, 26 pop12, 16 DIPGRIND levels, 13 TUP2_1,        *)
(*  11 PUSH, 10 hGRIND_even, 9 POP, 7 PX2A, 5 CLEANG_odd,           *)
(*  3 PX2B0, 3 PX2Bgen, 3 PUSHX, 2 CLEANG_even, 2 TRANS2_1,         *)
(*  1 PX2A0) -- shorter than CASCADE53 (337 steps): the frame       *)
(*  SHRINKS from nine blocks to seven.  DIPGRIND sub-levels         *)
(*  (A, r): (109097, 132761), (6028, 50174), (189, 246),            *)
(*  (31, 45), (3, 5), (3, 2), (12062, 26044), (427, 5415),          *)
(*  (46, 167), (1026, 3357), (51, 423), (51, 2), (109, 199),        *)
(*  (3, 39), (3, 2), (13, 7).  Clean exits: CLEANG_even 119,        *)
(*  13018 and CLEANG_odd 18, 79, 95, 1674, 66376; the largest       *)
(*  hGRIND_even steps are 6029, 13741, 109098.                      *)
(*                                                                  *)
(*  TOP8 then closes by the size of r8 = 2 * j8 (j8 = j - 646581    *)
(*  in TOP8's own parameter):                                       *)
(*    r8 = 2:       TRANS2_1 + CASCADE_POPFIN, A = 1425923 + beta,  *)
(*                    frame [864783; 135142; 27487; ...];           *)
(*    r8 = 4:       TUP + hGRIND_even 712959 + TRANS2_2             *)
(*                    + CASCADE_POPFIN, A = beta + 2;               *)
(*    r8 = 6:       TUP + hGRIND_even 712959 + TUP2_1 + TDN         *)
(*                    + TRANS2_1 + CASCADE_POPFIN, A = beta + 4;    *)
(*    8 <= r8 <= 2851850 (band 8): TUP + hGRIND_even 712959         *)
(*      + TUP2_1 + TDN + TUP onto GRIND9 = HC [864782; 135142;      *)
(*      ...] 1425922 3 2 ((r8 - 6, 2) :: tail), whose pair grinds   *)
(*      CLEANLY by CLEANG_even (floor (r8 - 8)/2 + 1 <= 1425922,    *)
(*      exactly r8 <= 2851850), then TRANS2_1 + CASCADE_POPFIN,     *)
(*      A = r8 + beta - 2, frame [1425923; 864782; 135142; ...].    *)
(*      (The band counter is again the shuttle moved into the       *)
(*      counter slot by TUP2_1: 1425922, not 864782.)               *)
(*                                                                  *)
(*  For r8 >= 2851852 (j8 >= 1425926, i.e. TOP7-parameter           *)
(*  j >= 2072507) the pair (r8 - 6, 2) at counter 1425922 exceeds   *)
(*  the CLEANG_even floor and the rounds take the DIPDESC           *)
(*  boundary a NINTH time (hsim54 Part 3: the GRIND9 state and      *)
(*  the DIPGRIND (1425922, r8 - 2851850) landing both occur at      *)
(*  j = 2072507, 2072508, 2200000).  The ninth descent is expected  *)
(*  to be a NEW cascade with different constants, so no cycle       *)
(*  induction in the current vocabulary closes it; what remains     *)
(*  is the strictly smaller core                                    *)
(*                                                                  *)
(*    TAIL2_END9: the totality of the ONE pair (2j, 2) at the ONE   *)
(*    fixed TOP8 state HB [135142; 27487; 14322; 1260; 147;        *)
(*    20; 0] 864782 1 1425923, for j >= 1425926 (r8 = 2j            *)
(*    >= 2851852), beta >= 2.                                       *)
(*                                                                  *)
(*  The core's range shrank from [646582, infty) to [2072507,       *)
(*  infty) in TOP7 parameters; the band width roughly doubled       *)
(*  again (646582 -> 2072506).  Via TAIL2_END8_of54 +               *)
(*  TAIL2_END7_of53 + ESC_ERA_LAW_53 the ESC instances at every     *)
(*  even R >= 1278 now rest on TAIL2_END9 alone                     *)
(*  (ESC_ERA_LAW_54 below; Loop.v Part 4o).                         *)
(* ================================================================= *)

Require Import List Bool Arith Lia ZArith.
Import ListNotations.
Require Import TM Sections Mirror TokenPass Recoord Era Esc Dev
               Grind Grind2 Grind3 Grind4 Grind5 Grind6 Grind7 Grind8
               Grind9 Grind10 Grind11 Grind12 Grind13 Grind14 Grind15
               Grind16 Grind17 Grind18 Grind19 Grind20 Grind21.

(* Section equality: componentwise, arithmetic leaves by lia.      *)
Ltac sec_eq :=
  repeat (first [ solve [reflexivity] | solve [lia] | f_equal ]).

(* Closed-numeral arithmetic: literals >= 7426 are parsed as       *)
(* Nat.of_num_uint atoms, which lia cannot relate to variables;    *)
(* for purely closed <= goals the boolean check decides them.      *)
Ltac closearith :=
  first [ lia | apply Nat.leb_le; reflexivity ].

(* Numeral identities for the hGRIND_even steps below, factored    *)
(* into standalone lemmas proved by Nat.eqb_eq + vm_compute        *)
(* (VM-cast conversion).  In the Phase 52 file the same identities  *)
(* were discharged inline by `replace ... by (eqb/vm ...)` inside  *)
(* the step blocks; at Phase 53 scale that inline form              *)
(* stack-overflows inside the long hsteps_trans chains, while the   *)
(* standalone lemma form compiles -- so the identities live here,   *)
(* in a small context, and the step blocks use plain `rewrite`.     *)
Lemma NUM54a : 646578 = 2 * 323287 + 4.
Proof. apply Nat.eqb_eq; vm_compute; reflexivity. Qed.
Lemma NUM54b : 350961 = S 350960.
Proof. apply Nat.eqb_eq; vm_compute; reflexivity. Qed.
Lemma NUM54c : 1425922 = 2 * 712959 + 4.
Proof. apply Nat.eqb_eq; vm_compute; reflexivity. Qed.
Lemma NUM54d : 864782 = S 864781.
Proof. apply Nat.eqb_eq; vm_compute; reflexivity. Qed.
(* S-form / subtraction identities for the TOP8 closings: the      *)
(* sTRANS2_1, sTUP2_1, sTUP and hTRANS2_2 applies at shuttle        *)
(* 1425923 otherwise force S/subtraction conversions of unary       *)
(* depth ~1425923, which overflow the conversion stack; rewriting   *)
(* the goal's numerals to the lemmas' computed forms first makes    *)
(* the applies syntactic.                                           *)
Lemma NUM54e : 1425923 = S 1425922.
Proof. apply Nat.eqb_eq; vm_compute; reflexivity. Qed.
Lemma NUM54f : 1425924 = S (S 1425922).
Proof. apply Nat.eqb_eq; vm_compute; reflexivity. Qed.
Lemma NUM54g : 864783 = S 864782.
Proof. apply Nat.eqb_eq; vm_compute; reflexivity. Qed.
Lemma NUM54h : 1425922 = 1425923 - 1.
Proof. apply Nat.eqb_eq; vm_compute; reflexivity. Qed.
Lemma NUM54k : 1425922 = S 1425921.
Proof. apply Nat.eqb_eq; vm_compute; reflexivity. Qed.
Lemma NUM54m : 1425923 = S (S 1425921).
Proof. apply Nat.eqb_eq; vm_compute; reflexivity. Qed.
Lemma NUM54n : 1425924 = S 1425923.
Proof. apply Nat.eqb_eq; vm_compute; reflexivity. Qed.
Lemma NUM54p : 646582 = S 646581.
Proof. apply Nat.eqb_eq; vm_compute; reflexivity. Qed.
Lemma NUM54q : 1425926 = S 1425925.
Proof. apply Nat.eqb_eq; vm_compute; reflexivity. Qed.
Lemma NUM54r : 1425922 = 1425925 - 3.
Proof. apply Nat.eqb_eq; vm_compute; reflexivity. Qed.
(* List identity for CASCADE54a step 1: hPX2A produces the pair   *)
(* list (1, 1) :: (1, 2) :: (1, 2) :: spine, while the stated      *)
(* step target merges the two (1, 2)s into the spine repeat as     *)
(* repeat (1, 2) 646580.  Unifying the two forms directly makes    *)
(* the conversion recursion run the full 646580-deep repeat and    *)
(* stack-overflows (Phase 53's identical step at repeat 323288     *)
(* stayed under the limit); the identity is therefore factored     *)
(* here, and step 1 first rewrites its goal with it.  Even the     *)
(* factored identity does not prove by bare reflexivity in this    *)
(* file's environment (the repeat's whnf at the literal 646580     *)
(* recurses too deep); rewriting the literal to S (S 646578)       *)
(* first -- via the eqb/vm numeral identity NUM54ss -- keeps the   *)
(* remaining unfoldings shallow.                                   *)
Lemma NUM54ss : 646580 = S (S 646578).
Proof. apply Nat.eqb_eq; vm_compute; reflexivity. Qed.
(* S-form identities for CASCADE54a step 1's exact term:          *)
(* hPX2A's frame pattern S (S (S b')) :: S p' :: pb and its        *)
(* target shuttle S b' must convert against the goal's atoms      *)
(* 350961 / 109099 / 350959; atom-vs-S conversion recurses to the   *)
(* atom's depth and overflows at 350961 (Phase 53's identical      *)
(* step at 175058 stayed under the limit).  Step 1 first rewrites  *)
(* the goal's three atoms to S-form via these identities, making   *)
(* the exact term's conversion syntactic.                          *)
Lemma NUM54t1 : 350961 = S (S (S 350958)).
Proof. apply Nat.eqb_eq; vm_compute; reflexivity. Qed.
Lemma NUM54t2 : 109099 = S 109098.
Proof. apply Nat.eqb_eq; vm_compute; reflexivity. Qed.
Lemma NUM54t3 : 350959 = S 350958.
Proof. apply Nat.eqb_eq; vm_compute; reflexivity. Qed.
Lemma REP54a : forall w : list (nat * nat),
  (1, 1) :: (1, 2) :: (1, 2) :: repeat (1, 2) 646578 ++ w
  = (1, 1) :: repeat (1, 2) 646580 ++ w.
Proof. intro w. rewrite NUM54ss. reflexivity. Qed.
(* ----------------------------------------------------------------- *)
(* CASCADE54: the DIP8 spine over frame [350961; 109099; 62236;    *)
(* 6030; 630; 191; 113; 33; 19; 0] regrows onto TOP8, for an        *)
(* ARBITRARY tail w.  The proof is an hsteps_trans chain of 176     *)
(* classified steps (waypoints asserted verbatim in hsim54.py);     *)
(* step kinds are annotated per step.  NOTE (Phase 54, applying     *)
(* the Phase 52/53 lessons proactively): kernel conversion over     *)
(* of_num_uint numerals overflows the default stack at unary depth  *)
(* ~175000, and this phase's constants reach ~1425923, so the chain *)
(* is split from the start into five consecutive sub-lemmas:        *)
(* CASCADE54a (steps 1-44), CASCADE54b (45-88), CASCADE54c          *)
(* (89-132), CASCADE54d (133-175) and CASCADE54e (step 176 alone);  *)
(* CASCADE54 below is their composition, its statement the          *)
(* spine-to-TOP8 step.  Step 176 is isolated because its            *)
(* pop12 646580 landing forces the kernel conversions               *)
(* 218202 + 646580 = 864782 and 132763 + 2 * 646580 = 1425923,      *)
(* whose unary depth overflows the conversion stack; CASCADE54e     *)
(* first rewrites the goal's numerals to pop12's computed form,     *)
(* the two equalities being discharged by Nat.eqb_eq + vm_compute   *)
(* (VM-cast conversion).  The hGRIND_even steps in the TOP8         *)
(* closings below are preceded by rewrites via the standalone       *)
(* NUM54 numeral identities (the Phase 52 fix-up pattern, with      *)
(* the identities factored into lemmas -- see the NUM54 note).      *)
(* One further scale fix (Phase 54): the five hstep-constructor     *)
(* steps (PX2A / PX2A0 / PX2B0 / PX2Bgen / PUSHX) are given as       *)
(* fully explicit `exact (hsteps_step _ _ _ (hXXX ...)              *)
(* (hsteps_refl _))` terms rather than `apply hXXX`: with all       *)
(* constructor arguments left as evars, evarconv thrashes on the    *)
(* 646578-deep spine repeat (minutes, then stack overflow), while   *)
(* the explicit form checks by plain conversion in seconds.  The    *)
(* lemma statements are unchanged; only these proof terms differ    *)
(* in shape from the generated Phase 46-53 pattern.                 *)
(* ----------------------------------------------------------------- *)

(* Closed arithmetic identities for the large DIPGRIND /   *)
(* hGRIND_even / CLEANG steps of CASCADE54, factored into   *)
(* standalone lemmas (eqb/vm proofs) and rewritten in the   *)
(* step blocks, so the applies meet the lemmas' arithmetic  *)
(* forms syntactically instead of by a closed multiplication*)
(* conversion at depth >= 20000 (cf. NUM54ss / REP54a).     *)
Lemma NUM54X1 : 350955 = 2 * 109097 + 132761.
Proof. apply Nat.eqb_eq; vm_compute; reflexivity. Qed.
Lemma NUM54X2 : 218200 = 2 * 109098 + 4.
Proof. apply Nat.eqb_eq; vm_compute; reflexivity. Qed.
Lemma NUM54X3 : 132755 = 2 * 66376 + 3.
Proof. apply Nat.eqb_eq; vm_compute; reflexivity. Qed.
Lemma NUM54X4 : 132760 = 2 * 66376 + 8.
Proof. apply Nat.eqb_eq; vm_compute; reflexivity. Qed.

(* CASCADE54a: steps 1-44 of the CASCADE54 chain. *)
Lemma CASCADE54a : forall w,
  hsteps (HC [350961; 109099; 62236; 6030; 630; 191; 113; 33; 19; 0] 0 3 2 (repeat (1, 2) 646578 ++ w) 1)
         (HC [48; 5] 72 3 2 ((39, 2) :: (1, 1) :: repeat (1, 2) 191 ++ (246, 2) :: (1, 1) :: repeat (1, 2) 6030 ++ (50174, 2) :: (1, 1) :: repeat (1, 2) 109099 ++ (132761, 2) :: (1, 1) :: repeat (1, 2) 646580 ++ w) 1).
Proof.
  intro w.
  (* step 1: P PX2A *)
  apply (hsteps_trans _ (HC [62236; 6030; 630; 191; 113; 33; 19; 0] 109098 350959 2 ((1, 1) :: repeat (1, 2) 646580 ++ w) 1)).
  {
    rewrite NUM54t1. rewrite NUM54t2. rewrite NUM54t3.
    replace ((1, 1) :: repeat (1, 2) 646580 ++ w)
      with ((1, 1) :: (1, 2) :: (1, 2) :: repeat (1, 2) 646578 ++ w)
      by (apply REP54a).
    exact (hsteps_step _ _ _ (hPX2A 350958 109098 [62236; 6030; 630; 191; 113; 33; 19; 0] (repeat (1, 2) 646578 ++ w) 1) (hsteps_refl _)).
  }
  (* step 2: P PUSH *)
  apply (hsteps_trans _ (HC [62236; 6030; 630; 191; 113; 33; 19; 0] 109097 1 2 ((350957, 2) :: (1, 1) :: repeat (1, 2) 646580 ++ w) 1)).
  {
    replace ((350957, 2) :: (1, 1) :: repeat (1, 2) 646580 ++ w) with ((350959 - 2, 2) :: (1, 1) :: repeat (1, 2) 646580 ++ w) by sec_eq.
    apply (sPUSH [62236; 6030; 630; 191; 113; 33; 19; 0] 109097 350959 ((1, 1) :: repeat (1, 2) 646580 ++ w) 1); closearith.
  }
  (* step 3: P TDN *)
  apply (hsteps_trans _ (HB [62236; 6030; 630; 191; 113; 33; 19; 0] 109097 1 4 ((350957, 2) :: (1, 1) :: repeat (1, 2) 646580 ++ w) 1)).
  {
    apply (sTDN [62236; 6030; 630; 191; 113; 33; 19; 0] 109097 ((350957, 2) :: (1, 1) :: repeat (1, 2) 646580 ++ w) 1).
  }
  (* step 4: sTUP *)
  apply (hsteps_trans _ (HC [62236; 6030; 630; 191; 113; 33; 19; 0] 109097 3 2 ((350955, 2) :: (1, 1) :: repeat (1, 2) 646580 ++ w) 1)).
  {
    replace ((350955, 2) :: (1, 1) :: repeat (1, 2) 646580 ++ w) with ((350957 - 2, 2) :: (1, 1) :: repeat (1, 2) 646580 ++ w) by sec_eq.
    apply (sTUP [62236; 6030; 630; 191; 113; 33; 19; 0] 109097 4 350957 2 ((1, 1) :: repeat (1, 2) 646580 ++ w) 1); closearith.
  }
  (* step 5: DIPGRIND 109097 132761 *)
  apply (hsteps_trans _ (HC [62236; 6030; 630; 191; 113; 33; 19; 0] 0 3 2 (repeat (1, 2) 109097 ++ (132761, 2) :: (1, 1) :: repeat (1, 2) 646580 ++ w) 1)).
  {
    rewrite NUM54X1.
    apply (DIPGRIND 109097 132761 [62236; 6030; 630; 191; 113; 33; 19; 0] ((1, 1) :: repeat (1, 2) 646580 ++ w) 1); closearith.
  }
  (* step 6: P PX2A *)
  apply (hsteps_trans _ (HC [630; 191; 113; 33; 19; 0] 6029 62234 2 ((1, 1) :: repeat (1, 2) 109099 ++ (132761, 2) :: (1, 1) :: repeat (1, 2) 646580 ++ w) 1)).
  {
    exact (hsteps_step _ _ _ (hPX2A 62233 6029 [630; 191; 113; 33; 19; 0] (repeat (1, 2) 109097 ++ (132761, 2) :: (1, 1) :: repeat (1, 2) 646580 ++ w) 1) (hsteps_refl _)).
  }
  (* step 7: P PUSH *)
  apply (hsteps_trans _ (HC [630; 191; 113; 33; 19; 0] 6028 1 2 ((62232, 2) :: (1, 1) :: repeat (1, 2) 109099 ++ (132761, 2) :: (1, 1) :: repeat (1, 2) 646580 ++ w) 1)).
  {
    replace ((62232, 2) :: (1, 1) :: repeat (1, 2) 109099 ++ (132761, 2) :: (1, 1) :: repeat (1, 2) 646580 ++ w) with ((62234 - 2, 2) :: (1, 1) :: repeat (1, 2) 109099 ++ (132761, 2) :: (1, 1) :: repeat (1, 2) 646580 ++ w) by sec_eq.
    apply (sPUSH [630; 191; 113; 33; 19; 0] 6028 62234 ((1, 1) :: repeat (1, 2) 109099 ++ (132761, 2) :: (1, 1) :: repeat (1, 2) 646580 ++ w) 1); closearith.
  }
  (* step 8: P TDN *)
  apply (hsteps_trans _ (HB [630; 191; 113; 33; 19; 0] 6028 1 4 ((62232, 2) :: (1, 1) :: repeat (1, 2) 109099 ++ (132761, 2) :: (1, 1) :: repeat (1, 2) 646580 ++ w) 1)).
  {
    apply (sTDN [630; 191; 113; 33; 19; 0] 6028 ((62232, 2) :: (1, 1) :: repeat (1, 2) 109099 ++ (132761, 2) :: (1, 1) :: repeat (1, 2) 646580 ++ w) 1).
  }
  (* step 9: sTUP *)
  apply (hsteps_trans _ (HC [630; 191; 113; 33; 19; 0] 6028 3 2 ((62230, 2) :: (1, 1) :: repeat (1, 2) 109099 ++ (132761, 2) :: (1, 1) :: repeat (1, 2) 646580 ++ w) 1)).
  {
    replace ((62230, 2) :: (1, 1) :: repeat (1, 2) 109099 ++ (132761, 2) :: (1, 1) :: repeat (1, 2) 646580 ++ w) with ((62232 - 2, 2) :: (1, 1) :: repeat (1, 2) 109099 ++ (132761, 2) :: (1, 1) :: repeat (1, 2) 646580 ++ w) by sec_eq.
    apply (sTUP [630; 191; 113; 33; 19; 0] 6028 4 62232 2 ((1, 1) :: repeat (1, 2) 109099 ++ (132761, 2) :: (1, 1) :: repeat (1, 2) 646580 ++ w) 1); closearith.
  }
  (* step 10: DIPGRIND 6028 50174 *)
  apply (hsteps_trans _ (HC [630; 191; 113; 33; 19; 0] 0 3 2 (repeat (1, 2) 6028 ++ (50174, 2) :: (1, 1) :: repeat (1, 2) 109099 ++ (132761, 2) :: (1, 1) :: repeat (1, 2) 646580 ++ w) 1)).
  {
    apply (DIPGRIND 6028 50174 [630; 191; 113; 33; 19; 0] ((1, 1) :: repeat (1, 2) 109099 ++ (132761, 2) :: (1, 1) :: repeat (1, 2) 646580 ++ w) 1); closearith.
  }
  (* step 11: P PX2A *)
  apply (hsteps_trans _ (HC [113; 33; 19; 0] 190 628 2 ((1, 1) :: repeat (1, 2) 6030 ++ (50174, 2) :: (1, 1) :: repeat (1, 2) 109099 ++ (132761, 2) :: (1, 1) :: repeat (1, 2) 646580 ++ w) 1)).
  {
    exact (hsteps_step _ _ _ (hPX2A 627 190 [113; 33; 19; 0] (repeat (1, 2) 6028 ++ (50174, 2) :: (1, 1) :: repeat (1, 2) 109099 ++ (132761, 2) :: (1, 1) :: repeat (1, 2) 646580 ++ w) 1) (hsteps_refl _)).
  }
  (* step 12: P PUSH *)
  apply (hsteps_trans _ (HC [113; 33; 19; 0] 189 1 2 ((626, 2) :: (1, 1) :: repeat (1, 2) 6030 ++ (50174, 2) :: (1, 1) :: repeat (1, 2) 109099 ++ (132761, 2) :: (1, 1) :: repeat (1, 2) 646580 ++ w) 1)).
  {
    replace ((626, 2) :: (1, 1) :: repeat (1, 2) 6030 ++ (50174, 2) :: (1, 1) :: repeat (1, 2) 109099 ++ (132761, 2) :: (1, 1) :: repeat (1, 2) 646580 ++ w) with ((628 - 2, 2) :: (1, 1) :: repeat (1, 2) 6030 ++ (50174, 2) :: (1, 1) :: repeat (1, 2) 109099 ++ (132761, 2) :: (1, 1) :: repeat (1, 2) 646580 ++ w) by sec_eq.
    apply (sPUSH [113; 33; 19; 0] 189 628 ((1, 1) :: repeat (1, 2) 6030 ++ (50174, 2) :: (1, 1) :: repeat (1, 2) 109099 ++ (132761, 2) :: (1, 1) :: repeat (1, 2) 646580 ++ w) 1); closearith.
  }
  (* step 13: P TDN *)
  apply (hsteps_trans _ (HB [113; 33; 19; 0] 189 1 4 ((626, 2) :: (1, 1) :: repeat (1, 2) 6030 ++ (50174, 2) :: (1, 1) :: repeat (1, 2) 109099 ++ (132761, 2) :: (1, 1) :: repeat (1, 2) 646580 ++ w) 1)).
  {
    apply (sTDN [113; 33; 19; 0] 189 ((626, 2) :: (1, 1) :: repeat (1, 2) 6030 ++ (50174, 2) :: (1, 1) :: repeat (1, 2) 109099 ++ (132761, 2) :: (1, 1) :: repeat (1, 2) 646580 ++ w) 1).
  }
  (* step 14: sTUP *)
  apply (hsteps_trans _ (HC [113; 33; 19; 0] 189 3 2 ((624, 2) :: (1, 1) :: repeat (1, 2) 6030 ++ (50174, 2) :: (1, 1) :: repeat (1, 2) 109099 ++ (132761, 2) :: (1, 1) :: repeat (1, 2) 646580 ++ w) 1)).
  {
    replace ((624, 2) :: (1, 1) :: repeat (1, 2) 6030 ++ (50174, 2) :: (1, 1) :: repeat (1, 2) 109099 ++ (132761, 2) :: (1, 1) :: repeat (1, 2) 646580 ++ w) with ((626 - 2, 2) :: (1, 1) :: repeat (1, 2) 6030 ++ (50174, 2) :: (1, 1) :: repeat (1, 2) 109099 ++ (132761, 2) :: (1, 1) :: repeat (1, 2) 646580 ++ w) by sec_eq.
    apply (sTUP [113; 33; 19; 0] 189 4 626 2 ((1, 1) :: repeat (1, 2) 6030 ++ (50174, 2) :: (1, 1) :: repeat (1, 2) 109099 ++ (132761, 2) :: (1, 1) :: repeat (1, 2) 646580 ++ w) 1); closearith.
  }
  (* step 15: DIPGRIND 189 246 *)
  apply (hsteps_trans _ (HC [113; 33; 19; 0] 0 3 2 (repeat (1, 2) 189 ++ (246, 2) :: (1, 1) :: repeat (1, 2) 6030 ++ (50174, 2) :: (1, 1) :: repeat (1, 2) 109099 ++ (132761, 2) :: (1, 1) :: repeat (1, 2) 646580 ++ w) 1)).
  {
    apply (DIPGRIND 189 246 [113; 33; 19; 0] ((1, 1) :: repeat (1, 2) 6030 ++ (50174, 2) :: (1, 1) :: repeat (1, 2) 109099 ++ (132761, 2) :: (1, 1) :: repeat (1, 2) 646580 ++ w) 1); closearith.
  }
  (* step 16: P PX2A *)
  apply (hsteps_trans _ (HC [19; 0] 32 111 2 ((1, 1) :: repeat (1, 2) 191 ++ (246, 2) :: (1, 1) :: repeat (1, 2) 6030 ++ (50174, 2) :: (1, 1) :: repeat (1, 2) 109099 ++ (132761, 2) :: (1, 1) :: repeat (1, 2) 646580 ++ w) 1)).
  {
    exact (hsteps_step _ _ _ (hPX2A 110 32 [19; 0] (repeat (1, 2) 189 ++ (246, 2) :: (1, 1) :: repeat (1, 2) 6030 ++ (50174, 2) :: (1, 1) :: repeat (1, 2) 109099 ++ (132761, 2) :: (1, 1) :: repeat (1, 2) 646580 ++ w) 1) (hsteps_refl _)).
  }
  (* step 17: P PUSH *)
  apply (hsteps_trans _ (HC [19; 0] 31 1 2 ((109, 2) :: (1, 1) :: repeat (1, 2) 191 ++ (246, 2) :: (1, 1) :: repeat (1, 2) 6030 ++ (50174, 2) :: (1, 1) :: repeat (1, 2) 109099 ++ (132761, 2) :: (1, 1) :: repeat (1, 2) 646580 ++ w) 1)).
  {
    replace ((109, 2) :: (1, 1) :: repeat (1, 2) 191 ++ (246, 2) :: (1, 1) :: repeat (1, 2) 6030 ++ (50174, 2) :: (1, 1) :: repeat (1, 2) 109099 ++ (132761, 2) :: (1, 1) :: repeat (1, 2) 646580 ++ w) with ((111 - 2, 2) :: (1, 1) :: repeat (1, 2) 191 ++ (246, 2) :: (1, 1) :: repeat (1, 2) 6030 ++ (50174, 2) :: (1, 1) :: repeat (1, 2) 109099 ++ (132761, 2) :: (1, 1) :: repeat (1, 2) 646580 ++ w) by sec_eq.
    apply (sPUSH [19; 0] 31 111 ((1, 1) :: repeat (1, 2) 191 ++ (246, 2) :: (1, 1) :: repeat (1, 2) 6030 ++ (50174, 2) :: (1, 1) :: repeat (1, 2) 109099 ++ (132761, 2) :: (1, 1) :: repeat (1, 2) 646580 ++ w) 1); closearith.
  }
  (* step 18: P TDN *)
  apply (hsteps_trans _ (HB [19; 0] 31 1 4 ((109, 2) :: (1, 1) :: repeat (1, 2) 191 ++ (246, 2) :: (1, 1) :: repeat (1, 2) 6030 ++ (50174, 2) :: (1, 1) :: repeat (1, 2) 109099 ++ (132761, 2) :: (1, 1) :: repeat (1, 2) 646580 ++ w) 1)).
  {
    apply (sTDN [19; 0] 31 ((109, 2) :: (1, 1) :: repeat (1, 2) 191 ++ (246, 2) :: (1, 1) :: repeat (1, 2) 6030 ++ (50174, 2) :: (1, 1) :: repeat (1, 2) 109099 ++ (132761, 2) :: (1, 1) :: repeat (1, 2) 646580 ++ w) 1).
  }
  (* step 19: sTUP *)
  apply (hsteps_trans _ (HC [19; 0] 31 3 2 ((107, 2) :: (1, 1) :: repeat (1, 2) 191 ++ (246, 2) :: (1, 1) :: repeat (1, 2) 6030 ++ (50174, 2) :: (1, 1) :: repeat (1, 2) 109099 ++ (132761, 2) :: (1, 1) :: repeat (1, 2) 646580 ++ w) 1)).
  {
    replace ((107, 2) :: (1, 1) :: repeat (1, 2) 191 ++ (246, 2) :: (1, 1) :: repeat (1, 2) 6030 ++ (50174, 2) :: (1, 1) :: repeat (1, 2) 109099 ++ (132761, 2) :: (1, 1) :: repeat (1, 2) 646580 ++ w) with ((109 - 2, 2) :: (1, 1) :: repeat (1, 2) 191 ++ (246, 2) :: (1, 1) :: repeat (1, 2) 6030 ++ (50174, 2) :: (1, 1) :: repeat (1, 2) 109099 ++ (132761, 2) :: (1, 1) :: repeat (1, 2) 646580 ++ w) by sec_eq.
    apply (sTUP [19; 0] 31 4 109 2 ((1, 1) :: repeat (1, 2) 191 ++ (246, 2) :: (1, 1) :: repeat (1, 2) 6030 ++ (50174, 2) :: (1, 1) :: repeat (1, 2) 109099 ++ (132761, 2) :: (1, 1) :: repeat (1, 2) 646580 ++ w) 1); closearith.
  }
  (* step 20: DIPGRIND 31 45 *)
  apply (hsteps_trans _ (HC [19; 0] 0 3 2 (repeat (1, 2) 31 ++ (45, 2) :: (1, 1) :: repeat (1, 2) 191 ++ (246, 2) :: (1, 1) :: repeat (1, 2) 6030 ++ (50174, 2) :: (1, 1) :: repeat (1, 2) 109099 ++ (132761, 2) :: (1, 1) :: repeat (1, 2) 646580 ++ w) 1)).
  {
    apply (DIPGRIND 31 45 [19; 0] ((1, 1) :: repeat (1, 2) 191 ++ (246, 2) :: (1, 1) :: repeat (1, 2) 6030 ++ (50174, 2) :: (1, 1) :: repeat (1, 2) 109099 ++ (132761, 2) :: (1, 1) :: repeat (1, 2) 646580 ++ w) 1); closearith.
  }
  (* step 21: P PX2A0 *)
  apply (hsteps_trans _ (HB [0] 3 1 2 ((15, 2) :: (1, 1) :: repeat (1, 2) 33 ++ (45, 2) :: (1, 1) :: repeat (1, 2) 191 ++ (246, 2) :: (1, 1) :: repeat (1, 2) 6030 ++ (50174, 2) :: (1, 1) :: repeat (1, 2) 109099 ++ (132761, 2) :: (1, 1) :: repeat (1, 2) 646580 ++ w) 1)).
  {
    exact (hsteps_step _ _ _ (hPX2A0 14 (repeat (1, 2) 31 ++ (45, 2) :: (1, 1) :: repeat (1, 2) 191 ++ (246, 2) :: (1, 1) :: repeat (1, 2) 6030 ++ (50174, 2) :: (1, 1) :: repeat (1, 2) 109099 ++ (132761, 2) :: (1, 1) :: repeat (1, 2) 646580 ++ w) 1) (hsteps_refl _)).
  }
  (* step 22: sTUP *)
  apply (hsteps_trans _ (HC [0] 3 1 2 ((13, 2) :: (1, 1) :: repeat (1, 2) 33 ++ (45, 2) :: (1, 1) :: repeat (1, 2) 191 ++ (246, 2) :: (1, 1) :: repeat (1, 2) 6030 ++ (50174, 2) :: (1, 1) :: repeat (1, 2) 109099 ++ (132761, 2) :: (1, 1) :: repeat (1, 2) 646580 ++ w) 1)).
  {
    replace ((13, 2) :: (1, 1) :: repeat (1, 2) 33 ++ (45, 2) :: (1, 1) :: repeat (1, 2) 191 ++ (246, 2) :: (1, 1) :: repeat (1, 2) 6030 ++ (50174, 2) :: (1, 1) :: repeat (1, 2) 109099 ++ (132761, 2) :: (1, 1) :: repeat (1, 2) 646580 ++ w) with ((15 - 2, 2) :: (1, 1) :: repeat (1, 2) 33 ++ (45, 2) :: (1, 1) :: repeat (1, 2) 191 ++ (246, 2) :: (1, 1) :: repeat (1, 2) 6030 ++ (50174, 2) :: (1, 1) :: repeat (1, 2) 109099 ++ (132761, 2) :: (1, 1) :: repeat (1, 2) 646580 ++ w) by sec_eq.
    apply (sTUP [0] 3 2 15 2 ((1, 1) :: repeat (1, 2) 33 ++ (45, 2) :: (1, 1) :: repeat (1, 2) 191 ++ (246, 2) :: (1, 1) :: repeat (1, 2) 6030 ++ (50174, 2) :: (1, 1) :: repeat (1, 2) 109099 ++ (132761, 2) :: (1, 1) :: repeat (1, 2) 646580 ++ w) 1); closearith.
  }
  (* step 23: P TDN *)
  apply (hsteps_trans _ (HB [0] 3 1 4 ((13, 2) :: (1, 1) :: repeat (1, 2) 33 ++ (45, 2) :: (1, 1) :: repeat (1, 2) 191 ++ (246, 2) :: (1, 1) :: repeat (1, 2) 6030 ++ (50174, 2) :: (1, 1) :: repeat (1, 2) 109099 ++ (132761, 2) :: (1, 1) :: repeat (1, 2) 646580 ++ w) 1)).
  {
    apply (sTDN [0] 3 ((13, 2) :: (1, 1) :: repeat (1, 2) 33 ++ (45, 2) :: (1, 1) :: repeat (1, 2) 191 ++ (246, 2) :: (1, 1) :: repeat (1, 2) 6030 ++ (50174, 2) :: (1, 1) :: repeat (1, 2) 109099 ++ (132761, 2) :: (1, 1) :: repeat (1, 2) 646580 ++ w) 1).
  }
  (* step 24: sTUP *)
  apply (hsteps_trans _ (HC [0] 3 3 2 ((11, 2) :: (1, 1) :: repeat (1, 2) 33 ++ (45, 2) :: (1, 1) :: repeat (1, 2) 191 ++ (246, 2) :: (1, 1) :: repeat (1, 2) 6030 ++ (50174, 2) :: (1, 1) :: repeat (1, 2) 109099 ++ (132761, 2) :: (1, 1) :: repeat (1, 2) 646580 ++ w) 1)).
  {
    replace ((11, 2) :: (1, 1) :: repeat (1, 2) 33 ++ (45, 2) :: (1, 1) :: repeat (1, 2) 191 ++ (246, 2) :: (1, 1) :: repeat (1, 2) 6030 ++ (50174, 2) :: (1, 1) :: repeat (1, 2) 109099 ++ (132761, 2) :: (1, 1) :: repeat (1, 2) 646580 ++ w) with ((13 - 2, 2) :: (1, 1) :: repeat (1, 2) 33 ++ (45, 2) :: (1, 1) :: repeat (1, 2) 191 ++ (246, 2) :: (1, 1) :: repeat (1, 2) 6030 ++ (50174, 2) :: (1, 1) :: repeat (1, 2) 109099 ++ (132761, 2) :: (1, 1) :: repeat (1, 2) 646580 ++ w) by sec_eq.
    apply (sTUP [0] 3 4 13 2 ((1, 1) :: repeat (1, 2) 33 ++ (45, 2) :: (1, 1) :: repeat (1, 2) 191 ++ (246, 2) :: (1, 1) :: repeat (1, 2) 6030 ++ (50174, 2) :: (1, 1) :: repeat (1, 2) 109099 ++ (132761, 2) :: (1, 1) :: repeat (1, 2) 646580 ++ w) 1); closearith.
  }
  (* step 25: DIPGRIND 3 5 *)
  apply (hsteps_trans _ (HC [0] 0 3 2 (repeat (1, 2) 3 ++ (5, 2) :: (1, 1) :: repeat (1, 2) 33 ++ (45, 2) :: (1, 1) :: repeat (1, 2) 191 ++ (246, 2) :: (1, 1) :: repeat (1, 2) 6030 ++ (50174, 2) :: (1, 1) :: repeat (1, 2) 109099 ++ (132761, 2) :: (1, 1) :: repeat (1, 2) 646580 ++ w) 1)).
  {
    apply (DIPGRIND 3 5 [0] ((1, 1) :: repeat (1, 2) 33 ++ (45, 2) :: (1, 1) :: repeat (1, 2) 191 ++ (246, 2) :: (1, 1) :: repeat (1, 2) 6030 ++ (50174, 2) :: (1, 1) :: repeat (1, 2) 109099 ++ (132761, 2) :: (1, 1) :: repeat (1, 2) 646580 ++ w) 1); closearith.
  }
  (* step 26: P PX2B0 *)
  apply (hsteps_trans _ (HB [] 0 1 5 (repeat (1, 2) 4 ++ (5, 2) :: (1, 1) :: repeat (1, 2) 33 ++ (45, 2) :: (1, 1) :: repeat (1, 2) 191 ++ (246, 2) :: (1, 1) :: repeat (1, 2) 6030 ++ (50174, 2) :: (1, 1) :: repeat (1, 2) 109099 ++ (132761, 2) :: (1, 1) :: repeat (1, 2) 646580 ++ w) 1)).
  {
    exact (hsteps_step _ _ _ (hPX2B0 (repeat (1, 2) 3 ++ (5, 2) :: (1, 1) :: repeat (1, 2) 33 ++ (45, 2) :: (1, 1) :: repeat (1, 2) 191 ++ (246, 2) :: (1, 1) :: repeat (1, 2) 6030 ++ (50174, 2) :: (1, 1) :: repeat (1, 2) 109099 ++ (132761, 2) :: (1, 1) :: repeat (1, 2) 646580 ++ w) 1) (hsteps_refl _)).
  }
  (* step 27: M pop12 (4,) *)
  apply (hsteps_trans _ (HB [] 4 1 13 ((5, 2) :: (1, 1) :: repeat (1, 2) 33 ++ (45, 2) :: (1, 1) :: repeat (1, 2) 191 ++ (246, 2) :: (1, 1) :: repeat (1, 2) 6030 ++ (50174, 2) :: (1, 1) :: repeat (1, 2) 109099 ++ (132761, 2) :: (1, 1) :: repeat (1, 2) 646580 ++ w) 1)).
  {
    apply (pop12 4 [] 0 5 ((5, 2) :: (1, 1) :: repeat (1, 2) 33 ++ (45, 2) :: (1, 1) :: repeat (1, 2) 191 ++ (246, 2) :: (1, 1) :: repeat (1, 2) 6030 ++ (50174, 2) :: (1, 1) :: repeat (1, 2) 109099 ++ (132761, 2) :: (1, 1) :: repeat (1, 2) 646580 ++ w) 1); closearith.
  }
  (* step 28: sTUP *)
  apply (hsteps_trans _ (HC [] 4 12 2 ((3, 2) :: (1, 1) :: repeat (1, 2) 33 ++ (45, 2) :: (1, 1) :: repeat (1, 2) 191 ++ (246, 2) :: (1, 1) :: repeat (1, 2) 6030 ++ (50174, 2) :: (1, 1) :: repeat (1, 2) 109099 ++ (132761, 2) :: (1, 1) :: repeat (1, 2) 646580 ++ w) 1)).
  {
    replace ((3, 2) :: (1, 1) :: repeat (1, 2) 33 ++ (45, 2) :: (1, 1) :: repeat (1, 2) 191 ++ (246, 2) :: (1, 1) :: repeat (1, 2) 6030 ++ (50174, 2) :: (1, 1) :: repeat (1, 2) 109099 ++ (132761, 2) :: (1, 1) :: repeat (1, 2) 646580 ++ w) with ((5 - 2, 2) :: (1, 1) :: repeat (1, 2) 33 ++ (45, 2) :: (1, 1) :: repeat (1, 2) 191 ++ (246, 2) :: (1, 1) :: repeat (1, 2) 6030 ++ (50174, 2) :: (1, 1) :: repeat (1, 2) 109099 ++ (132761, 2) :: (1, 1) :: repeat (1, 2) 646580 ++ w) by sec_eq.
    apply (sTUP [] 4 13 5 2 ((1, 1) :: repeat (1, 2) 33 ++ (45, 2) :: (1, 1) :: repeat (1, 2) 191 ++ (246, 2) :: (1, 1) :: repeat (1, 2) 6030 ++ (50174, 2) :: (1, 1) :: repeat (1, 2) 109099 ++ (132761, 2) :: (1, 1) :: repeat (1, 2) 646580 ++ w) 1); closearith.
  }
  (* step 29: P PUSH *)
  apply (hsteps_trans _ (HC [] 3 1 2 ((10, 2) :: (3, 2) :: (1, 1) :: repeat (1, 2) 33 ++ (45, 2) :: (1, 1) :: repeat (1, 2) 191 ++ (246, 2) :: (1, 1) :: repeat (1, 2) 6030 ++ (50174, 2) :: (1, 1) :: repeat (1, 2) 109099 ++ (132761, 2) :: (1, 1) :: repeat (1, 2) 646580 ++ w) 1)).
  {
    replace ((10, 2) :: (3, 2) :: (1, 1) :: repeat (1, 2) 33 ++ (45, 2) :: (1, 1) :: repeat (1, 2) 191 ++ (246, 2) :: (1, 1) :: repeat (1, 2) 6030 ++ (50174, 2) :: (1, 1) :: repeat (1, 2) 109099 ++ (132761, 2) :: (1, 1) :: repeat (1, 2) 646580 ++ w) with ((12 - 2, 2) :: (3, 2) :: (1, 1) :: repeat (1, 2) 33 ++ (45, 2) :: (1, 1) :: repeat (1, 2) 191 ++ (246, 2) :: (1, 1) :: repeat (1, 2) 6030 ++ (50174, 2) :: (1, 1) :: repeat (1, 2) 109099 ++ (132761, 2) :: (1, 1) :: repeat (1, 2) 646580 ++ w) by sec_eq.
    apply (sPUSH [] 3 12 ((3, 2) :: (1, 1) :: repeat (1, 2) 33 ++ (45, 2) :: (1, 1) :: repeat (1, 2) 191 ++ (246, 2) :: (1, 1) :: repeat (1, 2) 6030 ++ (50174, 2) :: (1, 1) :: repeat (1, 2) 109099 ++ (132761, 2) :: (1, 1) :: repeat (1, 2) 646580 ++ w) 1); closearith.
  }
  (* step 30: P TDN *)
  apply (hsteps_trans _ (HB [] 3 1 4 ((10, 2) :: (3, 2) :: (1, 1) :: repeat (1, 2) 33 ++ (45, 2) :: (1, 1) :: repeat (1, 2) 191 ++ (246, 2) :: (1, 1) :: repeat (1, 2) 6030 ++ (50174, 2) :: (1, 1) :: repeat (1, 2) 109099 ++ (132761, 2) :: (1, 1) :: repeat (1, 2) 646580 ++ w) 1)).
  {
    apply (sTDN [] 3 ((10, 2) :: (3, 2) :: (1, 1) :: repeat (1, 2) 33 ++ (45, 2) :: (1, 1) :: repeat (1, 2) 191 ++ (246, 2) :: (1, 1) :: repeat (1, 2) 6030 ++ (50174, 2) :: (1, 1) :: repeat (1, 2) 109099 ++ (132761, 2) :: (1, 1) :: repeat (1, 2) 646580 ++ w) 1).
  }
  (* step 31: sTUP *)
  apply (hsteps_trans _ (HC [] 3 3 2 ((8, 2) :: (3, 2) :: (1, 1) :: repeat (1, 2) 33 ++ (45, 2) :: (1, 1) :: repeat (1, 2) 191 ++ (246, 2) :: (1, 1) :: repeat (1, 2) 6030 ++ (50174, 2) :: (1, 1) :: repeat (1, 2) 109099 ++ (132761, 2) :: (1, 1) :: repeat (1, 2) 646580 ++ w) 1)).
  {
    replace ((8, 2) :: (3, 2) :: (1, 1) :: repeat (1, 2) 33 ++ (45, 2) :: (1, 1) :: repeat (1, 2) 191 ++ (246, 2) :: (1, 1) :: repeat (1, 2) 6030 ++ (50174, 2) :: (1, 1) :: repeat (1, 2) 109099 ++ (132761, 2) :: (1, 1) :: repeat (1, 2) 646580 ++ w) with ((10 - 2, 2) :: (3, 2) :: (1, 1) :: repeat (1, 2) 33 ++ (45, 2) :: (1, 1) :: repeat (1, 2) 191 ++ (246, 2) :: (1, 1) :: repeat (1, 2) 6030 ++ (50174, 2) :: (1, 1) :: repeat (1, 2) 109099 ++ (132761, 2) :: (1, 1) :: repeat (1, 2) 646580 ++ w) by sec_eq.
    apply (sTUP [] 3 4 10 2 ((3, 2) :: (1, 1) :: repeat (1, 2) 33 ++ (45, 2) :: (1, 1) :: repeat (1, 2) 191 ++ (246, 2) :: (1, 1) :: repeat (1, 2) 6030 ++ (50174, 2) :: (1, 1) :: repeat (1, 2) 109099 ++ (132761, 2) :: (1, 1) :: repeat (1, 2) 646580 ++ w) 1); closearith.
  }
  (* step 32: DIPGRIND 3 2 *)
  apply (hsteps_trans _ (HC [] 0 3 2 (repeat (1, 2) 3 ++ (2, 2) :: (3, 2) :: (1, 1) :: repeat (1, 2) 33 ++ (45, 2) :: (1, 1) :: repeat (1, 2) 191 ++ (246, 2) :: (1, 1) :: repeat (1, 2) 6030 ++ (50174, 2) :: (1, 1) :: repeat (1, 2) 109099 ++ (132761, 2) :: (1, 1) :: repeat (1, 2) 646580 ++ w) 1)).
  {
    apply (DIPGRIND 3 2 [] ((3, 2) :: (1, 1) :: repeat (1, 2) 33 ++ (45, 2) :: (1, 1) :: repeat (1, 2) 191 ++ (246, 2) :: (1, 1) :: repeat (1, 2) 6030 ++ (50174, 2) :: (1, 1) :: repeat (1, 2) 109099 ++ (132761, 2) :: (1, 1) :: repeat (1, 2) 646580 ++ w) 1); closearith.
  }
  (* step 33: P PUSHX *)
  apply (hsteps_trans _ (HB [] 1 1 7 (repeat (1, 2) 3 ++ (2, 2) :: (3, 2) :: (1, 1) :: repeat (1, 2) 33 ++ (45, 2) :: (1, 1) :: repeat (1, 2) 191 ++ (246, 2) :: (1, 1) :: repeat (1, 2) 6030 ++ (50174, 2) :: (1, 1) :: repeat (1, 2) 109099 ++ (132761, 2) :: (1, 1) :: repeat (1, 2) 646580 ++ w) 1)).
  {
    exact (hsteps_step _ _ _ (hPUSHX (repeat (1, 2) 3 ++ (2, 2) :: (3, 2) :: (1, 1) :: repeat (1, 2) 33 ++ (45, 2) :: (1, 1) :: repeat (1, 2) 191 ++ (246, 2) :: (1, 1) :: repeat (1, 2) 6030 ++ (50174, 2) :: (1, 1) :: repeat (1, 2) 109099 ++ (132761, 2) :: (1, 1) :: repeat (1, 2) 646580 ++ w) 1) (hsteps_refl _)).
  }
  (* step 34: M pop12 (3,) *)
  apply (hsteps_trans _ (HB [] 4 1 13 ((2, 2) :: (3, 2) :: (1, 1) :: repeat (1, 2) 33 ++ (45, 2) :: (1, 1) :: repeat (1, 2) 191 ++ (246, 2) :: (1, 1) :: repeat (1, 2) 6030 ++ (50174, 2) :: (1, 1) :: repeat (1, 2) 109099 ++ (132761, 2) :: (1, 1) :: repeat (1, 2) 646580 ++ w) 1)).
  {
    apply (pop12 3 [] 1 7 ((2, 2) :: (3, 2) :: (1, 1) :: repeat (1, 2) 33 ++ (45, 2) :: (1, 1) :: repeat (1, 2) 191 ++ (246, 2) :: (1, 1) :: repeat (1, 2) 6030 ++ (50174, 2) :: (1, 1) :: repeat (1, 2) 109099 ++ (132761, 2) :: (1, 1) :: repeat (1, 2) 646580 ++ w) 1); closearith.
  }
  (* step 35: P TUP2_1 *)
  apply (hsteps_trans _ (HC [5] 13 1 2 (repeat (1, 2) 1 ++ (1, 1) :: repeat (1, 2) 33 ++ (45, 2) :: (1, 1) :: repeat (1, 2) 191 ++ (246, 2) :: (1, 1) :: repeat (1, 2) 6030 ++ (50174, 2) :: (1, 1) :: repeat (1, 2) 109099 ++ (132761, 2) :: (1, 1) :: repeat (1, 2) 646580 ++ w) 1)).
  {
    replace (repeat (1, 2) 1 ++ (1, 1) :: repeat (1, 2) 33 ++ (45, 2) :: (1, 1) :: repeat (1, 2) 191 ++ (246, 2) :: (1, 1) :: repeat (1, 2) 6030 ++ (50174, 2) :: (1, 1) :: repeat (1, 2) 109099 ++ (132761, 2) :: (1, 1) :: repeat (1, 2) 646580 ++ w) with ((3 - 2, 2) :: (1, 1) :: repeat (1, 2) 33 ++ (45, 2) :: (1, 1) :: repeat (1, 2) 191 ++ (246, 2) :: (1, 1) :: repeat (1, 2) 6030 ++ (50174, 2) :: (1, 1) :: repeat (1, 2) 109099 ++ (132761, 2) :: (1, 1) :: repeat (1, 2) 646580 ++ w) by sec_eq.
    apply (sTUP2_1 [] 4 12 3 ((1, 1) :: repeat (1, 2) 33 ++ (45, 2) :: (1, 1) :: repeat (1, 2) 191 ++ (246, 2) :: (1, 1) :: repeat (1, 2) 6030 ++ (50174, 2) :: (1, 1) :: repeat (1, 2) 109099 ++ (132761, 2) :: (1, 1) :: repeat (1, 2) 646580 ++ w) 1); closearith.
  }
  (* step 36: P TDN *)
  apply (hsteps_trans _ (HB [5] 13 1 4 (repeat (1, 2) 1 ++ (1, 1) :: repeat (1, 2) 33 ++ (45, 2) :: (1, 1) :: repeat (1, 2) 191 ++ (246, 2) :: (1, 1) :: repeat (1, 2) 6030 ++ (50174, 2) :: (1, 1) :: repeat (1, 2) 109099 ++ (132761, 2) :: (1, 1) :: repeat (1, 2) 646580 ++ w) 1)).
  {
    apply (sTDN [5] 13 (repeat (1, 2) 1 ++ (1, 1) :: repeat (1, 2) 33 ++ (45, 2) :: (1, 1) :: repeat (1, 2) 191 ++ (246, 2) :: (1, 1) :: repeat (1, 2) 6030 ++ (50174, 2) :: (1, 1) :: repeat (1, 2) 109099 ++ (132761, 2) :: (1, 1) :: repeat (1, 2) 646580 ++ w) 1).
  }
  (* step 37: M pop12 (1,) *)
  apply (hsteps_trans _ (HB [5] 14 1 6 ((1, 1) :: repeat (1, 2) 33 ++ (45, 2) :: (1, 1) :: repeat (1, 2) 191 ++ (246, 2) :: (1, 1) :: repeat (1, 2) 6030 ++ (50174, 2) :: (1, 1) :: repeat (1, 2) 109099 ++ (132761, 2) :: (1, 1) :: repeat (1, 2) 646580 ++ w) 1)).
  {
    apply (pop12 1 [5] 13 4 ((1, 1) :: repeat (1, 2) 33 ++ (45, 2) :: (1, 1) :: repeat (1, 2) 191 ++ (246, 2) :: (1, 1) :: repeat (1, 2) 6030 ++ (50174, 2) :: (1, 1) :: repeat (1, 2) 109099 ++ (132761, 2) :: (1, 1) :: repeat (1, 2) 646580 ++ w) 1); closearith.
  }
  (* step 38: P POP *)
  apply (hsteps_trans _ (HB [5] 15 1 7 (repeat (1, 2) 33 ++ (45, 2) :: (1, 1) :: repeat (1, 2) 191 ++ (246, 2) :: (1, 1) :: repeat (1, 2) 6030 ++ (50174, 2) :: (1, 1) :: repeat (1, 2) 109099 ++ (132761, 2) :: (1, 1) :: repeat (1, 2) 646580 ++ w) 1)).
  {
    apply (sPOP1 [5] 14 6 (repeat (1, 2) 33 ++ (45, 2) :: (1, 1) :: repeat (1, 2) 191 ++ (246, 2) :: (1, 1) :: repeat (1, 2) 6030 ++ (50174, 2) :: (1, 1) :: repeat (1, 2) 109099 ++ (132761, 2) :: (1, 1) :: repeat (1, 2) 646580 ++ w) 1); closearith.
  }
  (* step 39: M pop12 (33,) *)
  apply (hsteps_trans _ (HB [5] 48 1 73 ((45, 2) :: (1, 1) :: repeat (1, 2) 191 ++ (246, 2) :: (1, 1) :: repeat (1, 2) 6030 ++ (50174, 2) :: (1, 1) :: repeat (1, 2) 109099 ++ (132761, 2) :: (1, 1) :: repeat (1, 2) 646580 ++ w) 1)).
  {
    apply (pop12 33 [5] 15 7 ((45, 2) :: (1, 1) :: repeat (1, 2) 191 ++ (246, 2) :: (1, 1) :: repeat (1, 2) 6030 ++ (50174, 2) :: (1, 1) :: repeat (1, 2) 109099 ++ (132761, 2) :: (1, 1) :: repeat (1, 2) 646580 ++ w) 1); closearith.
  }
  (* step 40: sTUP *)
  apply (hsteps_trans _ (HC [5] 48 72 2 ((43, 2) :: (1, 1) :: repeat (1, 2) 191 ++ (246, 2) :: (1, 1) :: repeat (1, 2) 6030 ++ (50174, 2) :: (1, 1) :: repeat (1, 2) 109099 ++ (132761, 2) :: (1, 1) :: repeat (1, 2) 646580 ++ w) 1)).
  {
    replace ((43, 2) :: (1, 1) :: repeat (1, 2) 191 ++ (246, 2) :: (1, 1) :: repeat (1, 2) 6030 ++ (50174, 2) :: (1, 1) :: repeat (1, 2) 109099 ++ (132761, 2) :: (1, 1) :: repeat (1, 2) 646580 ++ w) with ((45 - 2, 2) :: (1, 1) :: repeat (1, 2) 191 ++ (246, 2) :: (1, 1) :: repeat (1, 2) 6030 ++ (50174, 2) :: (1, 1) :: repeat (1, 2) 109099 ++ (132761, 2) :: (1, 1) :: repeat (1, 2) 646580 ++ w) by sec_eq.
    apply (sTUP [5] 48 73 45 2 ((1, 1) :: repeat (1, 2) 191 ++ (246, 2) :: (1, 1) :: repeat (1, 2) 6030 ++ (50174, 2) :: (1, 1) :: repeat (1, 2) 109099 ++ (132761, 2) :: (1, 1) :: repeat (1, 2) 646580 ++ w) 1); closearith.
  }
  (* step 41: hGRIND_even 34 *)
  apply (hsteps_trans _ (HB [5] 47 1 72 ((2, 2) :: (43, 2) :: (1, 1) :: repeat (1, 2) 191 ++ (246, 2) :: (1, 1) :: repeat (1, 2) 6030 ++ (50174, 2) :: (1, 1) :: repeat (1, 2) 109099 ++ (132761, 2) :: (1, 1) :: repeat (1, 2) 646580 ++ w) 1)).
  {
    apply (hGRIND_even 34 [5] 47 ((43, 2) :: (1, 1) :: repeat (1, 2) 191 ++ (246, 2) :: (1, 1) :: repeat (1, 2) 6030 ++ (50174, 2) :: (1, 1) :: repeat (1, 2) 109099 ++ (132761, 2) :: (1, 1) :: repeat (1, 2) 646580 ++ w) 1); closearith.
  }
  (* step 42: P TUP2_1 *)
  apply (hsteps_trans _ (HC [48; 5] 72 1 2 ((41, 2) :: (1, 1) :: repeat (1, 2) 191 ++ (246, 2) :: (1, 1) :: repeat (1, 2) 6030 ++ (50174, 2) :: (1, 1) :: repeat (1, 2) 109099 ++ (132761, 2) :: (1, 1) :: repeat (1, 2) 646580 ++ w) 1)).
  {
    replace ((41, 2) :: (1, 1) :: repeat (1, 2) 191 ++ (246, 2) :: (1, 1) :: repeat (1, 2) 6030 ++ (50174, 2) :: (1, 1) :: repeat (1, 2) 109099 ++ (132761, 2) :: (1, 1) :: repeat (1, 2) 646580 ++ w) with ((43 - 2, 2) :: (1, 1) :: repeat (1, 2) 191 ++ (246, 2) :: (1, 1) :: repeat (1, 2) 6030 ++ (50174, 2) :: (1, 1) :: repeat (1, 2) 109099 ++ (132761, 2) :: (1, 1) :: repeat (1, 2) 646580 ++ w) by sec_eq.
    apply (sTUP2_1 [5] 47 71 43 ((1, 1) :: repeat (1, 2) 191 ++ (246, 2) :: (1, 1) :: repeat (1, 2) 6030 ++ (50174, 2) :: (1, 1) :: repeat (1, 2) 109099 ++ (132761, 2) :: (1, 1) :: repeat (1, 2) 646580 ++ w) 1); closearith.
  }
  (* step 43: P TDN *)
  apply (hsteps_trans _ (HB [48; 5] 72 1 4 ((41, 2) :: (1, 1) :: repeat (1, 2) 191 ++ (246, 2) :: (1, 1) :: repeat (1, 2) 6030 ++ (50174, 2) :: (1, 1) :: repeat (1, 2) 109099 ++ (132761, 2) :: (1, 1) :: repeat (1, 2) 646580 ++ w) 1)).
  {
    apply (sTDN [48; 5] 72 ((41, 2) :: (1, 1) :: repeat (1, 2) 191 ++ (246, 2) :: (1, 1) :: repeat (1, 2) 6030 ++ (50174, 2) :: (1, 1) :: repeat (1, 2) 109099 ++ (132761, 2) :: (1, 1) :: repeat (1, 2) 646580 ++ w) 1).
  }
  (* step 44: sTUP *)
  replace ((39, 2) :: (1, 1) :: repeat (1, 2) 191 ++ (246, 2) :: (1, 1) :: repeat (1, 2) 6030 ++ (50174, 2) :: (1, 1) :: repeat (1, 2) 109099 ++ (132761, 2) :: (1, 1) :: repeat (1, 2) 646580 ++ w) with ((41 - 2, 2) :: (1, 1) :: repeat (1, 2) 191 ++ (246, 2) :: (1, 1) :: repeat (1, 2) 6030 ++ (50174, 2) :: (1, 1) :: repeat (1, 2) 109099 ++ (132761, 2) :: (1, 1) :: repeat (1, 2) 646580 ++ w) by sec_eq.
  apply (sTUP [48; 5] 72 4 41 2 ((1, 1) :: repeat (1, 2) 191 ++ (246, 2) :: (1, 1) :: repeat (1, 2) 6030 ++ (50174, 2) :: (1, 1) :: repeat (1, 2) 109099 ++ (132761, 2) :: (1, 1) :: repeat (1, 2) 646580 ++ w) 1); closearith.
Qed.

(* CASCADE54b: steps 45-88 of the CASCADE54 chain. *)
Lemma CASCADE54b : forall w,
  hsteps (HC [48; 5] 72 3 2 ((39, 2) :: (1, 1) :: repeat (1, 2) 191 ++ (246, 2) :: (1, 1) :: repeat (1, 2) 6030 ++ (50174, 2) :: (1, 1) :: repeat (1, 2) 109099 ++ (132761, 2) :: (1, 1) :: repeat (1, 2) 646580 ++ w) 1)
         (HC [531; 53; 0] 1026 1 2 ((5411, 2) :: (1, 1) :: repeat (1, 2) 12064 ++ (26044, 2) :: (1, 1) :: repeat (1, 2) 109099 ++ (132761, 2) :: (1, 1) :: repeat (1, 2) 646580 ++ w) 1).
Proof.
  intro w.
  (* step 45: CLEANG_odd 18 *)
  apply (hsteps_trans _ (HB [48; 5] 72 1 44 (repeat (1, 2) 1 ++ (1, 1) :: repeat (1, 2) 191 ++ (246, 2) :: (1, 1) :: repeat (1, 2) 6030 ++ (50174, 2) :: (1, 1) :: repeat (1, 2) 109099 ++ (132761, 2) :: (1, 1) :: repeat (1, 2) 646580 ++ w) 1)).
  {
    replace (repeat (1, 2) 1 ++ (1, 1) :: repeat (1, 2) 191 ++ (246, 2) :: (1, 1) :: repeat (1, 2) 6030 ++ (50174, 2) :: (1, 1) :: repeat (1, 2) 109099 ++ (132761, 2) :: (1, 1) :: repeat (1, 2) 646580 ++ w) with ((1, 2) :: (1, 1) :: repeat (1, 2) 191 ++ (246, 2) :: (1, 1) :: repeat (1, 2) 6030 ++ (50174, 2) :: (1, 1) :: repeat (1, 2) 109099 ++ (132761, 2) :: (1, 1) :: repeat (1, 2) 646580 ++ w) by sec_eq.
    apply (CLEANG_odd 18 [48; 5] 72 ((1, 1) :: repeat (1, 2) 191 ++ (246, 2) :: (1, 1) :: repeat (1, 2) 6030 ++ (50174, 2) :: (1, 1) :: repeat (1, 2) 109099 ++ (132761, 2) :: (1, 1) :: repeat (1, 2) 646580 ++ w) 1); closearith.
  }
  (* step 46: M pop12 (1,) *)
  apply (hsteps_trans _ (HB [48; 5] 73 1 46 ((1, 1) :: repeat (1, 2) 191 ++ (246, 2) :: (1, 1) :: repeat (1, 2) 6030 ++ (50174, 2) :: (1, 1) :: repeat (1, 2) 109099 ++ (132761, 2) :: (1, 1) :: repeat (1, 2) 646580 ++ w) 1)).
  {
    apply (pop12 1 [48; 5] 72 44 ((1, 1) :: repeat (1, 2) 191 ++ (246, 2) :: (1, 1) :: repeat (1, 2) 6030 ++ (50174, 2) :: (1, 1) :: repeat (1, 2) 109099 ++ (132761, 2) :: (1, 1) :: repeat (1, 2) 646580 ++ w) 1); closearith.
  }
  (* step 47: P POP *)
  apply (hsteps_trans _ (HB [48; 5] 74 1 47 (repeat (1, 2) 191 ++ (246, 2) :: (1, 1) :: repeat (1, 2) 6030 ++ (50174, 2) :: (1, 1) :: repeat (1, 2) 109099 ++ (132761, 2) :: (1, 1) :: repeat (1, 2) 646580 ++ w) 1)).
  {
    apply (sPOP1 [48; 5] 73 46 (repeat (1, 2) 191 ++ (246, 2) :: (1, 1) :: repeat (1, 2) 6030 ++ (50174, 2) :: (1, 1) :: repeat (1, 2) 109099 ++ (132761, 2) :: (1, 1) :: repeat (1, 2) 646580 ++ w) 1); closearith.
  }
  (* step 48: M pop12 (191,) *)
  apply (hsteps_trans _ (HB [48; 5] 265 1 429 ((246, 2) :: (1, 1) :: repeat (1, 2) 6030 ++ (50174, 2) :: (1, 1) :: repeat (1, 2) 109099 ++ (132761, 2) :: (1, 1) :: repeat (1, 2) 646580 ++ w) 1)).
  {
    apply (pop12 191 [48; 5] 74 47 ((246, 2) :: (1, 1) :: repeat (1, 2) 6030 ++ (50174, 2) :: (1, 1) :: repeat (1, 2) 109099 ++ (132761, 2) :: (1, 1) :: repeat (1, 2) 646580 ++ w) 1); closearith.
  }
  (* step 49: sTUP *)
  apply (hsteps_trans _ (HC [48; 5] 265 428 2 ((244, 2) :: (1, 1) :: repeat (1, 2) 6030 ++ (50174, 2) :: (1, 1) :: repeat (1, 2) 109099 ++ (132761, 2) :: (1, 1) :: repeat (1, 2) 646580 ++ w) 1)).
  {
    replace ((244, 2) :: (1, 1) :: repeat (1, 2) 6030 ++ (50174, 2) :: (1, 1) :: repeat (1, 2) 109099 ++ (132761, 2) :: (1, 1) :: repeat (1, 2) 646580 ++ w) with ((246 - 2, 2) :: (1, 1) :: repeat (1, 2) 6030 ++ (50174, 2) :: (1, 1) :: repeat (1, 2) 109099 ++ (132761, 2) :: (1, 1) :: repeat (1, 2) 646580 ++ w) by sec_eq.
    apply (sTUP [48; 5] 265 429 246 2 ((1, 1) :: repeat (1, 2) 6030 ++ (50174, 2) :: (1, 1) :: repeat (1, 2) 109099 ++ (132761, 2) :: (1, 1) :: repeat (1, 2) 646580 ++ w) 1); closearith.
  }
  (* step 50: hGRIND_even 212 *)
  apply (hsteps_trans _ (HB [48; 5] 264 1 428 ((2, 2) :: (244, 2) :: (1, 1) :: repeat (1, 2) 6030 ++ (50174, 2) :: (1, 1) :: repeat (1, 2) 109099 ++ (132761, 2) :: (1, 1) :: repeat (1, 2) 646580 ++ w) 1)).
  {
    apply (hGRIND_even 212 [48; 5] 264 ((244, 2) :: (1, 1) :: repeat (1, 2) 6030 ++ (50174, 2) :: (1, 1) :: repeat (1, 2) 109099 ++ (132761, 2) :: (1, 1) :: repeat (1, 2) 646580 ++ w) 1); closearith.
  }
  (* step 51: P TUP2_1 *)
  apply (hsteps_trans _ (HC [265; 48; 5] 428 1 2 ((242, 2) :: (1, 1) :: repeat (1, 2) 6030 ++ (50174, 2) :: (1, 1) :: repeat (1, 2) 109099 ++ (132761, 2) :: (1, 1) :: repeat (1, 2) 646580 ++ w) 1)).
  {
    replace ((242, 2) :: (1, 1) :: repeat (1, 2) 6030 ++ (50174, 2) :: (1, 1) :: repeat (1, 2) 109099 ++ (132761, 2) :: (1, 1) :: repeat (1, 2) 646580 ++ w) with ((244 - 2, 2) :: (1, 1) :: repeat (1, 2) 6030 ++ (50174, 2) :: (1, 1) :: repeat (1, 2) 109099 ++ (132761, 2) :: (1, 1) :: repeat (1, 2) 646580 ++ w) by sec_eq.
    apply (sTUP2_1 [48; 5] 264 427 244 ((1, 1) :: repeat (1, 2) 6030 ++ (50174, 2) :: (1, 1) :: repeat (1, 2) 109099 ++ (132761, 2) :: (1, 1) :: repeat (1, 2) 646580 ++ w) 1); closearith.
  }
  (* step 52: P TDN *)
  apply (hsteps_trans _ (HB [265; 48; 5] 428 1 4 ((242, 2) :: (1, 1) :: repeat (1, 2) 6030 ++ (50174, 2) :: (1, 1) :: repeat (1, 2) 109099 ++ (132761, 2) :: (1, 1) :: repeat (1, 2) 646580 ++ w) 1)).
  {
    apply (sTDN [265; 48; 5] 428 ((242, 2) :: (1, 1) :: repeat (1, 2) 6030 ++ (50174, 2) :: (1, 1) :: repeat (1, 2) 109099 ++ (132761, 2) :: (1, 1) :: repeat (1, 2) 646580 ++ w) 1).
  }
  (* step 53: sTUP *)
  apply (hsteps_trans _ (HC [265; 48; 5] 428 3 2 ((240, 2) :: (1, 1) :: repeat (1, 2) 6030 ++ (50174, 2) :: (1, 1) :: repeat (1, 2) 109099 ++ (132761, 2) :: (1, 1) :: repeat (1, 2) 646580 ++ w) 1)).
  {
    replace ((240, 2) :: (1, 1) :: repeat (1, 2) 6030 ++ (50174, 2) :: (1, 1) :: repeat (1, 2) 109099 ++ (132761, 2) :: (1, 1) :: repeat (1, 2) 646580 ++ w) with ((242 - 2, 2) :: (1, 1) :: repeat (1, 2) 6030 ++ (50174, 2) :: (1, 1) :: repeat (1, 2) 109099 ++ (132761, 2) :: (1, 1) :: repeat (1, 2) 646580 ++ w) by sec_eq.
    apply (sTUP [265; 48; 5] 428 4 242 2 ((1, 1) :: repeat (1, 2) 6030 ++ (50174, 2) :: (1, 1) :: repeat (1, 2) 109099 ++ (132761, 2) :: (1, 1) :: repeat (1, 2) 646580 ++ w) 1); closearith.
  }
  (* step 54: CLEANG_even 119 *)
  apply (hsteps_trans _ (HB [265; 48; 5] 428 1 244 ((2, 2) :: (1, 1) :: repeat (1, 2) 6030 ++ (50174, 2) :: (1, 1) :: repeat (1, 2) 109099 ++ (132761, 2) :: (1, 1) :: repeat (1, 2) 646580 ++ w) 1)).
  {
    apply (CLEANG_even 119 [265; 48; 5] 428 ((1, 1) :: repeat (1, 2) 6030 ++ (50174, 2) :: (1, 1) :: repeat (1, 2) 109099 ++ (132761, 2) :: (1, 1) :: repeat (1, 2) 646580 ++ w) 1); closearith.
  }
  (* step 55: P TRANS2_1 *)
  apply (hsteps_trans _ (HB [429; 265; 48; 5] 245 1 3 (repeat (1, 2) 6030 ++ (50174, 2) :: (1, 1) :: repeat (1, 2) 109099 ++ (132761, 2) :: (1, 1) :: repeat (1, 2) 646580 ++ w) 1)).
  {
    apply (sTRANS2_1 [265; 48; 5] 428 243 1 (repeat (1, 2) 6030 ++ (50174, 2) :: (1, 1) :: repeat (1, 2) 109099 ++ (132761, 2) :: (1, 1) :: repeat (1, 2) 646580 ++ w) 1); closearith.
  }
  (* step 56: M pop12 (6030,) *)
  apply (hsteps_trans _ (HB [429; 265; 48; 5] 6275 1 12063 ((50174, 2) :: (1, 1) :: repeat (1, 2) 109099 ++ (132761, 2) :: (1, 1) :: repeat (1, 2) 646580 ++ w) 1)).
  {
    apply (pop12 6030 [429; 265; 48; 5] 245 3 ((50174, 2) :: (1, 1) :: repeat (1, 2) 109099 ++ (132761, 2) :: (1, 1) :: repeat (1, 2) 646580 ++ w) 1); closearith.
  }
  (* step 57: sTUP *)
  apply (hsteps_trans _ (HC [429; 265; 48; 5] 6275 12062 2 ((50172, 2) :: (1, 1) :: repeat (1, 2) 109099 ++ (132761, 2) :: (1, 1) :: repeat (1, 2) 646580 ++ w) 1)).
  {
    replace ((50172, 2) :: (1, 1) :: repeat (1, 2) 109099 ++ (132761, 2) :: (1, 1) :: repeat (1, 2) 646580 ++ w) with ((50174 - 2, 2) :: (1, 1) :: repeat (1, 2) 109099 ++ (132761, 2) :: (1, 1) :: repeat (1, 2) 646580 ++ w) by sec_eq.
    apply (sTUP [429; 265; 48; 5] 6275 12063 50174 2 ((1, 1) :: repeat (1, 2) 109099 ++ (132761, 2) :: (1, 1) :: repeat (1, 2) 646580 ++ w) 1); closearith.
  }
  (* step 58: hGRIND_even 6029 *)
  apply (hsteps_trans _ (HB [429; 265; 48; 5] 6274 1 12062 ((2, 2) :: (50172, 2) :: (1, 1) :: repeat (1, 2) 109099 ++ (132761, 2) :: (1, 1) :: repeat (1, 2) 646580 ++ w) 1)).
  {
    apply (hGRIND_even 6029 [429; 265; 48; 5] 6274 ((50172, 2) :: (1, 1) :: repeat (1, 2) 109099 ++ (132761, 2) :: (1, 1) :: repeat (1, 2) 646580 ++ w) 1); closearith.
  }
  (* step 59: P TUP2_1 *)
  apply (hsteps_trans _ (HC [6275; 429; 265; 48; 5] 12062 1 2 ((50170, 2) :: (1, 1) :: repeat (1, 2) 109099 ++ (132761, 2) :: (1, 1) :: repeat (1, 2) 646580 ++ w) 1)).
  {
    replace ((50170, 2) :: (1, 1) :: repeat (1, 2) 109099 ++ (132761, 2) :: (1, 1) :: repeat (1, 2) 646580 ++ w) with ((50172 - 2, 2) :: (1, 1) :: repeat (1, 2) 109099 ++ (132761, 2) :: (1, 1) :: repeat (1, 2) 646580 ++ w) by sec_eq.
    apply (sTUP2_1 [429; 265; 48; 5] 6274 12061 50172 ((1, 1) :: repeat (1, 2) 109099 ++ (132761, 2) :: (1, 1) :: repeat (1, 2) 646580 ++ w) 1); closearith.
  }
  (* step 60: P TDN *)
  apply (hsteps_trans _ (HB [6275; 429; 265; 48; 5] 12062 1 4 ((50170, 2) :: (1, 1) :: repeat (1, 2) 109099 ++ (132761, 2) :: (1, 1) :: repeat (1, 2) 646580 ++ w) 1)).
  {
    apply (sTDN [6275; 429; 265; 48; 5] 12062 ((50170, 2) :: (1, 1) :: repeat (1, 2) 109099 ++ (132761, 2) :: (1, 1) :: repeat (1, 2) 646580 ++ w) 1).
  }
  (* step 61: sTUP *)
  apply (hsteps_trans _ (HC [6275; 429; 265; 48; 5] 12062 3 2 ((50168, 2) :: (1, 1) :: repeat (1, 2) 109099 ++ (132761, 2) :: (1, 1) :: repeat (1, 2) 646580 ++ w) 1)).
  {
    replace ((50168, 2) :: (1, 1) :: repeat (1, 2) 109099 ++ (132761, 2) :: (1, 1) :: repeat (1, 2) 646580 ++ w) with ((50170 - 2, 2) :: (1, 1) :: repeat (1, 2) 109099 ++ (132761, 2) :: (1, 1) :: repeat (1, 2) 646580 ++ w) by sec_eq.
    apply (sTUP [6275; 429; 265; 48; 5] 12062 4 50170 2 ((1, 1) :: repeat (1, 2) 109099 ++ (132761, 2) :: (1, 1) :: repeat (1, 2) 646580 ++ w) 1); closearith.
  }
  (* step 62: DIPGRIND 12062 26044 *)
  apply (hsteps_trans _ (HC [6275; 429; 265; 48; 5] 0 3 2 (repeat (1, 2) 12062 ++ (26044, 2) :: (1, 1) :: repeat (1, 2) 109099 ++ (132761, 2) :: (1, 1) :: repeat (1, 2) 646580 ++ w) 1)).
  {
    apply (DIPGRIND 12062 26044 [6275; 429; 265; 48; 5] ((1, 1) :: repeat (1, 2) 109099 ++ (132761, 2) :: (1, 1) :: repeat (1, 2) 646580 ++ w) 1); closearith.
  }
  (* step 63: P PX2A *)
  apply (hsteps_trans _ (HC [265; 48; 5] 428 6273 2 ((1, 1) :: repeat (1, 2) 12064 ++ (26044, 2) :: (1, 1) :: repeat (1, 2) 109099 ++ (132761, 2) :: (1, 1) :: repeat (1, 2) 646580 ++ w) 1)).
  {
    exact (hsteps_step _ _ _ (hPX2A 6272 428 [265; 48; 5] (repeat (1, 2) 12062 ++ (26044, 2) :: (1, 1) :: repeat (1, 2) 109099 ++ (132761, 2) :: (1, 1) :: repeat (1, 2) 646580 ++ w) 1) (hsteps_refl _)).
  }
  (* step 64: P PUSH *)
  apply (hsteps_trans _ (HC [265; 48; 5] 427 1 2 ((6271, 2) :: (1, 1) :: repeat (1, 2) 12064 ++ (26044, 2) :: (1, 1) :: repeat (1, 2) 109099 ++ (132761, 2) :: (1, 1) :: repeat (1, 2) 646580 ++ w) 1)).
  {
    replace ((6271, 2) :: (1, 1) :: repeat (1, 2) 12064 ++ (26044, 2) :: (1, 1) :: repeat (1, 2) 109099 ++ (132761, 2) :: (1, 1) :: repeat (1, 2) 646580 ++ w) with ((6273 - 2, 2) :: (1, 1) :: repeat (1, 2) 12064 ++ (26044, 2) :: (1, 1) :: repeat (1, 2) 109099 ++ (132761, 2) :: (1, 1) :: repeat (1, 2) 646580 ++ w) by sec_eq.
    apply (sPUSH [265; 48; 5] 427 6273 ((1, 1) :: repeat (1, 2) 12064 ++ (26044, 2) :: (1, 1) :: repeat (1, 2) 109099 ++ (132761, 2) :: (1, 1) :: repeat (1, 2) 646580 ++ w) 1); closearith.
  }
  (* step 65: P TDN *)
  apply (hsteps_trans _ (HB [265; 48; 5] 427 1 4 ((6271, 2) :: (1, 1) :: repeat (1, 2) 12064 ++ (26044, 2) :: (1, 1) :: repeat (1, 2) 109099 ++ (132761, 2) :: (1, 1) :: repeat (1, 2) 646580 ++ w) 1)).
  {
    apply (sTDN [265; 48; 5] 427 ((6271, 2) :: (1, 1) :: repeat (1, 2) 12064 ++ (26044, 2) :: (1, 1) :: repeat (1, 2) 109099 ++ (132761, 2) :: (1, 1) :: repeat (1, 2) 646580 ++ w) 1).
  }
  (* step 66: sTUP *)
  apply (hsteps_trans _ (HC [265; 48; 5] 427 3 2 ((6269, 2) :: (1, 1) :: repeat (1, 2) 12064 ++ (26044, 2) :: (1, 1) :: repeat (1, 2) 109099 ++ (132761, 2) :: (1, 1) :: repeat (1, 2) 646580 ++ w) 1)).
  {
    replace ((6269, 2) :: (1, 1) :: repeat (1, 2) 12064 ++ (26044, 2) :: (1, 1) :: repeat (1, 2) 109099 ++ (132761, 2) :: (1, 1) :: repeat (1, 2) 646580 ++ w) with ((6271 - 2, 2) :: (1, 1) :: repeat (1, 2) 12064 ++ (26044, 2) :: (1, 1) :: repeat (1, 2) 109099 ++ (132761, 2) :: (1, 1) :: repeat (1, 2) 646580 ++ w) by sec_eq.
    apply (sTUP [265; 48; 5] 427 4 6271 2 ((1, 1) :: repeat (1, 2) 12064 ++ (26044, 2) :: (1, 1) :: repeat (1, 2) 109099 ++ (132761, 2) :: (1, 1) :: repeat (1, 2) 646580 ++ w) 1); closearith.
  }
  (* step 67: DIPGRIND 427 5415 *)
  apply (hsteps_trans _ (HC [265; 48; 5] 0 3 2 (repeat (1, 2) 427 ++ (5415, 2) :: (1, 1) :: repeat (1, 2) 12064 ++ (26044, 2) :: (1, 1) :: repeat (1, 2) 109099 ++ (132761, 2) :: (1, 1) :: repeat (1, 2) 646580 ++ w) 1)).
  {
    apply (DIPGRIND 427 5415 [265; 48; 5] ((1, 1) :: repeat (1, 2) 12064 ++ (26044, 2) :: (1, 1) :: repeat (1, 2) 109099 ++ (132761, 2) :: (1, 1) :: repeat (1, 2) 646580 ++ w) 1); closearith.
  }
  (* step 68: P PX2A *)
  apply (hsteps_trans _ (HC [5] 47 263 2 ((1, 1) :: repeat (1, 2) 429 ++ (5415, 2) :: (1, 1) :: repeat (1, 2) 12064 ++ (26044, 2) :: (1, 1) :: repeat (1, 2) 109099 ++ (132761, 2) :: (1, 1) :: repeat (1, 2) 646580 ++ w) 1)).
  {
    exact (hsteps_step _ _ _ (hPX2A 262 47 [5] (repeat (1, 2) 427 ++ (5415, 2) :: (1, 1) :: repeat (1, 2) 12064 ++ (26044, 2) :: (1, 1) :: repeat (1, 2) 109099 ++ (132761, 2) :: (1, 1) :: repeat (1, 2) 646580 ++ w) 1) (hsteps_refl _)).
  }
  (* step 69: P PUSH *)
  apply (hsteps_trans _ (HC [5] 46 1 2 ((261, 2) :: (1, 1) :: repeat (1, 2) 429 ++ (5415, 2) :: (1, 1) :: repeat (1, 2) 12064 ++ (26044, 2) :: (1, 1) :: repeat (1, 2) 109099 ++ (132761, 2) :: (1, 1) :: repeat (1, 2) 646580 ++ w) 1)).
  {
    replace ((261, 2) :: (1, 1) :: repeat (1, 2) 429 ++ (5415, 2) :: (1, 1) :: repeat (1, 2) 12064 ++ (26044, 2) :: (1, 1) :: repeat (1, 2) 109099 ++ (132761, 2) :: (1, 1) :: repeat (1, 2) 646580 ++ w) with ((263 - 2, 2) :: (1, 1) :: repeat (1, 2) 429 ++ (5415, 2) :: (1, 1) :: repeat (1, 2) 12064 ++ (26044, 2) :: (1, 1) :: repeat (1, 2) 109099 ++ (132761, 2) :: (1, 1) :: repeat (1, 2) 646580 ++ w) by sec_eq.
    apply (sPUSH [5] 46 263 ((1, 1) :: repeat (1, 2) 429 ++ (5415, 2) :: (1, 1) :: repeat (1, 2) 12064 ++ (26044, 2) :: (1, 1) :: repeat (1, 2) 109099 ++ (132761, 2) :: (1, 1) :: repeat (1, 2) 646580 ++ w) 1); closearith.
  }
  (* step 70: P TDN *)
  apply (hsteps_trans _ (HB [5] 46 1 4 ((261, 2) :: (1, 1) :: repeat (1, 2) 429 ++ (5415, 2) :: (1, 1) :: repeat (1, 2) 12064 ++ (26044, 2) :: (1, 1) :: repeat (1, 2) 109099 ++ (132761, 2) :: (1, 1) :: repeat (1, 2) 646580 ++ w) 1)).
  {
    apply (sTDN [5] 46 ((261, 2) :: (1, 1) :: repeat (1, 2) 429 ++ (5415, 2) :: (1, 1) :: repeat (1, 2) 12064 ++ (26044, 2) :: (1, 1) :: repeat (1, 2) 109099 ++ (132761, 2) :: (1, 1) :: repeat (1, 2) 646580 ++ w) 1).
  }
  (* step 71: sTUP *)
  apply (hsteps_trans _ (HC [5] 46 3 2 ((259, 2) :: (1, 1) :: repeat (1, 2) 429 ++ (5415, 2) :: (1, 1) :: repeat (1, 2) 12064 ++ (26044, 2) :: (1, 1) :: repeat (1, 2) 109099 ++ (132761, 2) :: (1, 1) :: repeat (1, 2) 646580 ++ w) 1)).
  {
    replace ((259, 2) :: (1, 1) :: repeat (1, 2) 429 ++ (5415, 2) :: (1, 1) :: repeat (1, 2) 12064 ++ (26044, 2) :: (1, 1) :: repeat (1, 2) 109099 ++ (132761, 2) :: (1, 1) :: repeat (1, 2) 646580 ++ w) with ((261 - 2, 2) :: (1, 1) :: repeat (1, 2) 429 ++ (5415, 2) :: (1, 1) :: repeat (1, 2) 12064 ++ (26044, 2) :: (1, 1) :: repeat (1, 2) 109099 ++ (132761, 2) :: (1, 1) :: repeat (1, 2) 646580 ++ w) by sec_eq.
    apply (sTUP [5] 46 4 261 2 ((1, 1) :: repeat (1, 2) 429 ++ (5415, 2) :: (1, 1) :: repeat (1, 2) 12064 ++ (26044, 2) :: (1, 1) :: repeat (1, 2) 109099 ++ (132761, 2) :: (1, 1) :: repeat (1, 2) 646580 ++ w) 1); closearith.
  }
  (* step 72: DIPGRIND 46 167 *)
  apply (hsteps_trans _ (HC [5] 0 3 2 (repeat (1, 2) 46 ++ (167, 2) :: (1, 1) :: repeat (1, 2) 429 ++ (5415, 2) :: (1, 1) :: repeat (1, 2) 12064 ++ (26044, 2) :: (1, 1) :: repeat (1, 2) 109099 ++ (132761, 2) :: (1, 1) :: repeat (1, 2) 646580 ++ w) 1)).
  {
    apply (DIPGRIND 46 167 [5] ((1, 1) :: repeat (1, 2) 429 ++ (5415, 2) :: (1, 1) :: repeat (1, 2) 12064 ++ (26044, 2) :: (1, 1) :: repeat (1, 2) 109099 ++ (132761, 2) :: (1, 1) :: repeat (1, 2) 646580 ++ w) 1); closearith.
  }
  (* step 73: P PX2Bgen *)
  apply (hsteps_trans _ (HB [0] 3 1 2 (repeat (1, 2) 1 ++ (1, 1) :: repeat (1, 2) 48 ++ (167, 2) :: (1, 1) :: repeat (1, 2) 429 ++ (5415, 2) :: (1, 1) :: repeat (1, 2) 12064 ++ (26044, 2) :: (1, 1) :: repeat (1, 2) 109099 ++ (132761, 2) :: (1, 1) :: repeat (1, 2) 646580 ++ w) 1)).
  {
    exact (hsteps_step _ _ _ (hPX2Bgen 0 (repeat (1, 2) 46 ++ (167, 2) :: (1, 1) :: repeat (1, 2) 429 ++ (5415, 2) :: (1, 1) :: repeat (1, 2) 12064 ++ (26044, 2) :: (1, 1) :: repeat (1, 2) 109099 ++ (132761, 2) :: (1, 1) :: repeat (1, 2) 646580 ++ w) 1) (hsteps_refl _)).
  }
  (* step 74: M pop12 (1,) *)
  apply (hsteps_trans _ (HB [0] 4 1 4 ((1, 1) :: repeat (1, 2) 48 ++ (167, 2) :: (1, 1) :: repeat (1, 2) 429 ++ (5415, 2) :: (1, 1) :: repeat (1, 2) 12064 ++ (26044, 2) :: (1, 1) :: repeat (1, 2) 109099 ++ (132761, 2) :: (1, 1) :: repeat (1, 2) 646580 ++ w) 1)).
  {
    apply (pop12 1 [0] 3 2 ((1, 1) :: repeat (1, 2) 48 ++ (167, 2) :: (1, 1) :: repeat (1, 2) 429 ++ (5415, 2) :: (1, 1) :: repeat (1, 2) 12064 ++ (26044, 2) :: (1, 1) :: repeat (1, 2) 109099 ++ (132761, 2) :: (1, 1) :: repeat (1, 2) 646580 ++ w) 1); closearith.
  }
  (* step 75: P POP *)
  apply (hsteps_trans _ (HB [0] 5 1 5 (repeat (1, 2) 48 ++ (167, 2) :: (1, 1) :: repeat (1, 2) 429 ++ (5415, 2) :: (1, 1) :: repeat (1, 2) 12064 ++ (26044, 2) :: (1, 1) :: repeat (1, 2) 109099 ++ (132761, 2) :: (1, 1) :: repeat (1, 2) 646580 ++ w) 1)).
  {
    apply (sPOP1 [0] 4 4 (repeat (1, 2) 48 ++ (167, 2) :: (1, 1) :: repeat (1, 2) 429 ++ (5415, 2) :: (1, 1) :: repeat (1, 2) 12064 ++ (26044, 2) :: (1, 1) :: repeat (1, 2) 109099 ++ (132761, 2) :: (1, 1) :: repeat (1, 2) 646580 ++ w) 1); closearith.
  }
  (* step 76: M pop12 (48,) *)
  apply (hsteps_trans _ (HB [0] 53 1 101 ((167, 2) :: (1, 1) :: repeat (1, 2) 429 ++ (5415, 2) :: (1, 1) :: repeat (1, 2) 12064 ++ (26044, 2) :: (1, 1) :: repeat (1, 2) 109099 ++ (132761, 2) :: (1, 1) :: repeat (1, 2) 646580 ++ w) 1)).
  {
    apply (pop12 48 [0] 5 5 ((167, 2) :: (1, 1) :: repeat (1, 2) 429 ++ (5415, 2) :: (1, 1) :: repeat (1, 2) 12064 ++ (26044, 2) :: (1, 1) :: repeat (1, 2) 109099 ++ (132761, 2) :: (1, 1) :: repeat (1, 2) 646580 ++ w) 1); closearith.
  }
  (* step 77: sTUP *)
  apply (hsteps_trans _ (HC [0] 53 100 2 ((165, 2) :: (1, 1) :: repeat (1, 2) 429 ++ (5415, 2) :: (1, 1) :: repeat (1, 2) 12064 ++ (26044, 2) :: (1, 1) :: repeat (1, 2) 109099 ++ (132761, 2) :: (1, 1) :: repeat (1, 2) 646580 ++ w) 1)).
  {
    replace ((165, 2) :: (1, 1) :: repeat (1, 2) 429 ++ (5415, 2) :: (1, 1) :: repeat (1, 2) 12064 ++ (26044, 2) :: (1, 1) :: repeat (1, 2) 109099 ++ (132761, 2) :: (1, 1) :: repeat (1, 2) 646580 ++ w) with ((167 - 2, 2) :: (1, 1) :: repeat (1, 2) 429 ++ (5415, 2) :: (1, 1) :: repeat (1, 2) 12064 ++ (26044, 2) :: (1, 1) :: repeat (1, 2) 109099 ++ (132761, 2) :: (1, 1) :: repeat (1, 2) 646580 ++ w) by sec_eq.
    apply (sTUP [0] 53 101 167 2 ((1, 1) :: repeat (1, 2) 429 ++ (5415, 2) :: (1, 1) :: repeat (1, 2) 12064 ++ (26044, 2) :: (1, 1) :: repeat (1, 2) 109099 ++ (132761, 2) :: (1, 1) :: repeat (1, 2) 646580 ++ w) 1); closearith.
  }
  (* step 78: hGRIND_even 48 *)
  apply (hsteps_trans _ (HB [0] 52 1 100 ((2, 2) :: (165, 2) :: (1, 1) :: repeat (1, 2) 429 ++ (5415, 2) :: (1, 1) :: repeat (1, 2) 12064 ++ (26044, 2) :: (1, 1) :: repeat (1, 2) 109099 ++ (132761, 2) :: (1, 1) :: repeat (1, 2) 646580 ++ w) 1)).
  {
    apply (hGRIND_even 48 [0] 52 ((165, 2) :: (1, 1) :: repeat (1, 2) 429 ++ (5415, 2) :: (1, 1) :: repeat (1, 2) 12064 ++ (26044, 2) :: (1, 1) :: repeat (1, 2) 109099 ++ (132761, 2) :: (1, 1) :: repeat (1, 2) 646580 ++ w) 1); closearith.
  }
  (* step 79: P TUP2_1 *)
  apply (hsteps_trans _ (HC [53; 0] 100 1 2 ((163, 2) :: (1, 1) :: repeat (1, 2) 429 ++ (5415, 2) :: (1, 1) :: repeat (1, 2) 12064 ++ (26044, 2) :: (1, 1) :: repeat (1, 2) 109099 ++ (132761, 2) :: (1, 1) :: repeat (1, 2) 646580 ++ w) 1)).
  {
    replace ((163, 2) :: (1, 1) :: repeat (1, 2) 429 ++ (5415, 2) :: (1, 1) :: repeat (1, 2) 12064 ++ (26044, 2) :: (1, 1) :: repeat (1, 2) 109099 ++ (132761, 2) :: (1, 1) :: repeat (1, 2) 646580 ++ w) with ((165 - 2, 2) :: (1, 1) :: repeat (1, 2) 429 ++ (5415, 2) :: (1, 1) :: repeat (1, 2) 12064 ++ (26044, 2) :: (1, 1) :: repeat (1, 2) 109099 ++ (132761, 2) :: (1, 1) :: repeat (1, 2) 646580 ++ w) by sec_eq.
    apply (sTUP2_1 [0] 52 99 165 ((1, 1) :: repeat (1, 2) 429 ++ (5415, 2) :: (1, 1) :: repeat (1, 2) 12064 ++ (26044, 2) :: (1, 1) :: repeat (1, 2) 109099 ++ (132761, 2) :: (1, 1) :: repeat (1, 2) 646580 ++ w) 1); closearith.
  }
  (* step 80: P TDN *)
  apply (hsteps_trans _ (HB [53; 0] 100 1 4 ((163, 2) :: (1, 1) :: repeat (1, 2) 429 ++ (5415, 2) :: (1, 1) :: repeat (1, 2) 12064 ++ (26044, 2) :: (1, 1) :: repeat (1, 2) 109099 ++ (132761, 2) :: (1, 1) :: repeat (1, 2) 646580 ++ w) 1)).
  {
    apply (sTDN [53; 0] 100 ((163, 2) :: (1, 1) :: repeat (1, 2) 429 ++ (5415, 2) :: (1, 1) :: repeat (1, 2) 12064 ++ (26044, 2) :: (1, 1) :: repeat (1, 2) 109099 ++ (132761, 2) :: (1, 1) :: repeat (1, 2) 646580 ++ w) 1).
  }
  (* step 81: sTUP *)
  apply (hsteps_trans _ (HC [53; 0] 100 3 2 ((161, 2) :: (1, 1) :: repeat (1, 2) 429 ++ (5415, 2) :: (1, 1) :: repeat (1, 2) 12064 ++ (26044, 2) :: (1, 1) :: repeat (1, 2) 109099 ++ (132761, 2) :: (1, 1) :: repeat (1, 2) 646580 ++ w) 1)).
  {
    replace ((161, 2) :: (1, 1) :: repeat (1, 2) 429 ++ (5415, 2) :: (1, 1) :: repeat (1, 2) 12064 ++ (26044, 2) :: (1, 1) :: repeat (1, 2) 109099 ++ (132761, 2) :: (1, 1) :: repeat (1, 2) 646580 ++ w) with ((163 - 2, 2) :: (1, 1) :: repeat (1, 2) 429 ++ (5415, 2) :: (1, 1) :: repeat (1, 2) 12064 ++ (26044, 2) :: (1, 1) :: repeat (1, 2) 109099 ++ (132761, 2) :: (1, 1) :: repeat (1, 2) 646580 ++ w) by sec_eq.
    apply (sTUP [53; 0] 100 4 163 2 ((1, 1) :: repeat (1, 2) 429 ++ (5415, 2) :: (1, 1) :: repeat (1, 2) 12064 ++ (26044, 2) :: (1, 1) :: repeat (1, 2) 109099 ++ (132761, 2) :: (1, 1) :: repeat (1, 2) 646580 ++ w) 1); closearith.
  }
  (* step 82: CLEANG_odd 79 *)
  apply (hsteps_trans _ (HB [53; 0] 100 1 166 (repeat (1, 2) 1 ++ (1, 1) :: repeat (1, 2) 429 ++ (5415, 2) :: (1, 1) :: repeat (1, 2) 12064 ++ (26044, 2) :: (1, 1) :: repeat (1, 2) 109099 ++ (132761, 2) :: (1, 1) :: repeat (1, 2) 646580 ++ w) 1)).
  {
    replace (repeat (1, 2) 1 ++ (1, 1) :: repeat (1, 2) 429 ++ (5415, 2) :: (1, 1) :: repeat (1, 2) 12064 ++ (26044, 2) :: (1, 1) :: repeat (1, 2) 109099 ++ (132761, 2) :: (1, 1) :: repeat (1, 2) 646580 ++ w) with ((1, 2) :: (1, 1) :: repeat (1, 2) 429 ++ (5415, 2) :: (1, 1) :: repeat (1, 2) 12064 ++ (26044, 2) :: (1, 1) :: repeat (1, 2) 109099 ++ (132761, 2) :: (1, 1) :: repeat (1, 2) 646580 ++ w) by sec_eq.
    apply (CLEANG_odd 79 [53; 0] 100 ((1, 1) :: repeat (1, 2) 429 ++ (5415, 2) :: (1, 1) :: repeat (1, 2) 12064 ++ (26044, 2) :: (1, 1) :: repeat (1, 2) 109099 ++ (132761, 2) :: (1, 1) :: repeat (1, 2) 646580 ++ w) 1); closearith.
  }
  (* step 83: M pop12 (1,) *)
  apply (hsteps_trans _ (HB [53; 0] 101 1 168 ((1, 1) :: repeat (1, 2) 429 ++ (5415, 2) :: (1, 1) :: repeat (1, 2) 12064 ++ (26044, 2) :: (1, 1) :: repeat (1, 2) 109099 ++ (132761, 2) :: (1, 1) :: repeat (1, 2) 646580 ++ w) 1)).
  {
    apply (pop12 1 [53; 0] 100 166 ((1, 1) :: repeat (1, 2) 429 ++ (5415, 2) :: (1, 1) :: repeat (1, 2) 12064 ++ (26044, 2) :: (1, 1) :: repeat (1, 2) 109099 ++ (132761, 2) :: (1, 1) :: repeat (1, 2) 646580 ++ w) 1); closearith.
  }
  (* step 84: P POP *)
  apply (hsteps_trans _ (HB [53; 0] 102 1 169 (repeat (1, 2) 429 ++ (5415, 2) :: (1, 1) :: repeat (1, 2) 12064 ++ (26044, 2) :: (1, 1) :: repeat (1, 2) 109099 ++ (132761, 2) :: (1, 1) :: repeat (1, 2) 646580 ++ w) 1)).
  {
    apply (sPOP1 [53; 0] 101 168 (repeat (1, 2) 429 ++ (5415, 2) :: (1, 1) :: repeat (1, 2) 12064 ++ (26044, 2) :: (1, 1) :: repeat (1, 2) 109099 ++ (132761, 2) :: (1, 1) :: repeat (1, 2) 646580 ++ w) 1); closearith.
  }
  (* step 85: M pop12 (429,) *)
  apply (hsteps_trans _ (HB [53; 0] 531 1 1027 ((5415, 2) :: (1, 1) :: repeat (1, 2) 12064 ++ (26044, 2) :: (1, 1) :: repeat (1, 2) 109099 ++ (132761, 2) :: (1, 1) :: repeat (1, 2) 646580 ++ w) 1)).
  {
    apply (pop12 429 [53; 0] 102 169 ((5415, 2) :: (1, 1) :: repeat (1, 2) 12064 ++ (26044, 2) :: (1, 1) :: repeat (1, 2) 109099 ++ (132761, 2) :: (1, 1) :: repeat (1, 2) 646580 ++ w) 1); closearith.
  }
  (* step 86: sTUP *)
  apply (hsteps_trans _ (HC [53; 0] 531 1026 2 ((5413, 2) :: (1, 1) :: repeat (1, 2) 12064 ++ (26044, 2) :: (1, 1) :: repeat (1, 2) 109099 ++ (132761, 2) :: (1, 1) :: repeat (1, 2) 646580 ++ w) 1)).
  {
    replace ((5413, 2) :: (1, 1) :: repeat (1, 2) 12064 ++ (26044, 2) :: (1, 1) :: repeat (1, 2) 109099 ++ (132761, 2) :: (1, 1) :: repeat (1, 2) 646580 ++ w) with ((5415 - 2, 2) :: (1, 1) :: repeat (1, 2) 12064 ++ (26044, 2) :: (1, 1) :: repeat (1, 2) 109099 ++ (132761, 2) :: (1, 1) :: repeat (1, 2) 646580 ++ w) by sec_eq.
    apply (sTUP [53; 0] 531 1027 5415 2 ((1, 1) :: repeat (1, 2) 12064 ++ (26044, 2) :: (1, 1) :: repeat (1, 2) 109099 ++ (132761, 2) :: (1, 1) :: repeat (1, 2) 646580 ++ w) 1); closearith.
  }
  (* step 87: hGRIND_even 511 *)
  apply (hsteps_trans _ (HB [53; 0] 530 1 1026 ((2, 2) :: (5413, 2) :: (1, 1) :: repeat (1, 2) 12064 ++ (26044, 2) :: (1, 1) :: repeat (1, 2) 109099 ++ (132761, 2) :: (1, 1) :: repeat (1, 2) 646580 ++ w) 1)).
  {
    apply (hGRIND_even 511 [53; 0] 530 ((5413, 2) :: (1, 1) :: repeat (1, 2) 12064 ++ (26044, 2) :: (1, 1) :: repeat (1, 2) 109099 ++ (132761, 2) :: (1, 1) :: repeat (1, 2) 646580 ++ w) 1); closearith.
  }
  (* step 88: P TUP2_1 *)
  replace ((5411, 2) :: (1, 1) :: repeat (1, 2) 12064 ++ (26044, 2) :: (1, 1) :: repeat (1, 2) 109099 ++ (132761, 2) :: (1, 1) :: repeat (1, 2) 646580 ++ w) with ((5413 - 2, 2) :: (1, 1) :: repeat (1, 2) 12064 ++ (26044, 2) :: (1, 1) :: repeat (1, 2) 109099 ++ (132761, 2) :: (1, 1) :: repeat (1, 2) 646580 ++ w) by sec_eq.
  apply (sTUP2_1 [53; 0] 530 1025 5413 ((1, 1) :: repeat (1, 2) 12064 ++ (26044, 2) :: (1, 1) :: repeat (1, 2) 109099 ++ (132761, 2) :: (1, 1) :: repeat (1, 2) 646580 ++ w) 1); closearith.
Qed.

(* CASCADE54c: steps 89-132 of the CASCADE54 chain. *)
Lemma CASCADE54c : forall w,
  hsteps (HC [531; 53; 0] 1026 1 2 ((5411, 2) :: (1, 1) :: repeat (1, 2) 12064 ++ (26044, 2) :: (1, 1) :: repeat (1, 2) 109099 ++ (132761, 2) :: (1, 1) :: repeat (1, 2) 646580 ++ w) 1)
         (HC [0] 20 34 2 ((5, 2) :: (1, 1) :: repeat (1, 2) 111 ++ (199, 2) :: (1, 1) :: repeat (1, 2) 1028 ++ (3357, 2) :: (1, 1) :: repeat (1, 2) 12064 ++ (26044, 2) :: (1, 1) :: repeat (1, 2) 109099 ++ (132761, 2) :: (1, 1) :: repeat (1, 2) 646580 ++ w) 1).
Proof.
  intro w.
  (* step 89: P TDN *)
  apply (hsteps_trans _ (HB [531; 53; 0] 1026 1 4 ((5411, 2) :: (1, 1) :: repeat (1, 2) 12064 ++ (26044, 2) :: (1, 1) :: repeat (1, 2) 109099 ++ (132761, 2) :: (1, 1) :: repeat (1, 2) 646580 ++ w) 1)).
  {
    apply (sTDN [531; 53; 0] 1026 ((5411, 2) :: (1, 1) :: repeat (1, 2) 12064 ++ (26044, 2) :: (1, 1) :: repeat (1, 2) 109099 ++ (132761, 2) :: (1, 1) :: repeat (1, 2) 646580 ++ w) 1).
  }
  (* step 90: sTUP *)
  apply (hsteps_trans _ (HC [531; 53; 0] 1026 3 2 ((5409, 2) :: (1, 1) :: repeat (1, 2) 12064 ++ (26044, 2) :: (1, 1) :: repeat (1, 2) 109099 ++ (132761, 2) :: (1, 1) :: repeat (1, 2) 646580 ++ w) 1)).
  {
    replace ((5409, 2) :: (1, 1) :: repeat (1, 2) 12064 ++ (26044, 2) :: (1, 1) :: repeat (1, 2) 109099 ++ (132761, 2) :: (1, 1) :: repeat (1, 2) 646580 ++ w) with ((5411 - 2, 2) :: (1, 1) :: repeat (1, 2) 12064 ++ (26044, 2) :: (1, 1) :: repeat (1, 2) 109099 ++ (132761, 2) :: (1, 1) :: repeat (1, 2) 646580 ++ w) by sec_eq.
    apply (sTUP [531; 53; 0] 1026 4 5411 2 ((1, 1) :: repeat (1, 2) 12064 ++ (26044, 2) :: (1, 1) :: repeat (1, 2) 109099 ++ (132761, 2) :: (1, 1) :: repeat (1, 2) 646580 ++ w) 1); closearith.
  }
  (* step 91: DIPGRIND 1026 3357 *)
  apply (hsteps_trans _ (HC [531; 53; 0] 0 3 2 (repeat (1, 2) 1026 ++ (3357, 2) :: (1, 1) :: repeat (1, 2) 12064 ++ (26044, 2) :: (1, 1) :: repeat (1, 2) 109099 ++ (132761, 2) :: (1, 1) :: repeat (1, 2) 646580 ++ w) 1)).
  {
    apply (DIPGRIND 1026 3357 [531; 53; 0] ((1, 1) :: repeat (1, 2) 12064 ++ (26044, 2) :: (1, 1) :: repeat (1, 2) 109099 ++ (132761, 2) :: (1, 1) :: repeat (1, 2) 646580 ++ w) 1); closearith.
  }
  (* step 92: P PX2A *)
  apply (hsteps_trans _ (HC [0] 52 529 2 ((1, 1) :: repeat (1, 2) 1028 ++ (3357, 2) :: (1, 1) :: repeat (1, 2) 12064 ++ (26044, 2) :: (1, 1) :: repeat (1, 2) 109099 ++ (132761, 2) :: (1, 1) :: repeat (1, 2) 646580 ++ w) 1)).
  {
    exact (hsteps_step _ _ _ (hPX2A 528 52 [0] (repeat (1, 2) 1026 ++ (3357, 2) :: (1, 1) :: repeat (1, 2) 12064 ++ (26044, 2) :: (1, 1) :: repeat (1, 2) 109099 ++ (132761, 2) :: (1, 1) :: repeat (1, 2) 646580 ++ w) 1) (hsteps_refl _)).
  }
  (* step 93: P PUSH *)
  apply (hsteps_trans _ (HC [0] 51 1 2 ((527, 2) :: (1, 1) :: repeat (1, 2) 1028 ++ (3357, 2) :: (1, 1) :: repeat (1, 2) 12064 ++ (26044, 2) :: (1, 1) :: repeat (1, 2) 109099 ++ (132761, 2) :: (1, 1) :: repeat (1, 2) 646580 ++ w) 1)).
  {
    replace ((527, 2) :: (1, 1) :: repeat (1, 2) 1028 ++ (3357, 2) :: (1, 1) :: repeat (1, 2) 12064 ++ (26044, 2) :: (1, 1) :: repeat (1, 2) 109099 ++ (132761, 2) :: (1, 1) :: repeat (1, 2) 646580 ++ w) with ((529 - 2, 2) :: (1, 1) :: repeat (1, 2) 1028 ++ (3357, 2) :: (1, 1) :: repeat (1, 2) 12064 ++ (26044, 2) :: (1, 1) :: repeat (1, 2) 109099 ++ (132761, 2) :: (1, 1) :: repeat (1, 2) 646580 ++ w) by sec_eq.
    apply (sPUSH [0] 51 529 ((1, 1) :: repeat (1, 2) 1028 ++ (3357, 2) :: (1, 1) :: repeat (1, 2) 12064 ++ (26044, 2) :: (1, 1) :: repeat (1, 2) 109099 ++ (132761, 2) :: (1, 1) :: repeat (1, 2) 646580 ++ w) 1); closearith.
  }
  (* step 94: P TDN *)
  apply (hsteps_trans _ (HB [0] 51 1 4 ((527, 2) :: (1, 1) :: repeat (1, 2) 1028 ++ (3357, 2) :: (1, 1) :: repeat (1, 2) 12064 ++ (26044, 2) :: (1, 1) :: repeat (1, 2) 109099 ++ (132761, 2) :: (1, 1) :: repeat (1, 2) 646580 ++ w) 1)).
  {
    apply (sTDN [0] 51 ((527, 2) :: (1, 1) :: repeat (1, 2) 1028 ++ (3357, 2) :: (1, 1) :: repeat (1, 2) 12064 ++ (26044, 2) :: (1, 1) :: repeat (1, 2) 109099 ++ (132761, 2) :: (1, 1) :: repeat (1, 2) 646580 ++ w) 1).
  }
  (* step 95: sTUP *)
  apply (hsteps_trans _ (HC [0] 51 3 2 ((525, 2) :: (1, 1) :: repeat (1, 2) 1028 ++ (3357, 2) :: (1, 1) :: repeat (1, 2) 12064 ++ (26044, 2) :: (1, 1) :: repeat (1, 2) 109099 ++ (132761, 2) :: (1, 1) :: repeat (1, 2) 646580 ++ w) 1)).
  {
    replace ((525, 2) :: (1, 1) :: repeat (1, 2) 1028 ++ (3357, 2) :: (1, 1) :: repeat (1, 2) 12064 ++ (26044, 2) :: (1, 1) :: repeat (1, 2) 109099 ++ (132761, 2) :: (1, 1) :: repeat (1, 2) 646580 ++ w) with ((527 - 2, 2) :: (1, 1) :: repeat (1, 2) 1028 ++ (3357, 2) :: (1, 1) :: repeat (1, 2) 12064 ++ (26044, 2) :: (1, 1) :: repeat (1, 2) 109099 ++ (132761, 2) :: (1, 1) :: repeat (1, 2) 646580 ++ w) by sec_eq.
    apply (sTUP [0] 51 4 527 2 ((1, 1) :: repeat (1, 2) 1028 ++ (3357, 2) :: (1, 1) :: repeat (1, 2) 12064 ++ (26044, 2) :: (1, 1) :: repeat (1, 2) 109099 ++ (132761, 2) :: (1, 1) :: repeat (1, 2) 646580 ++ w) 1); closearith.
  }
  (* step 96: DIPGRIND 51 423 *)
  apply (hsteps_trans _ (HC [0] 0 3 2 (repeat (1, 2) 51 ++ (423, 2) :: (1, 1) :: repeat (1, 2) 1028 ++ (3357, 2) :: (1, 1) :: repeat (1, 2) 12064 ++ (26044, 2) :: (1, 1) :: repeat (1, 2) 109099 ++ (132761, 2) :: (1, 1) :: repeat (1, 2) 646580 ++ w) 1)).
  {
    apply (DIPGRIND 51 423 [0] ((1, 1) :: repeat (1, 2) 1028 ++ (3357, 2) :: (1, 1) :: repeat (1, 2) 12064 ++ (26044, 2) :: (1, 1) :: repeat (1, 2) 109099 ++ (132761, 2) :: (1, 1) :: repeat (1, 2) 646580 ++ w) 1); closearith.
  }
  (* step 97: P PX2B0 *)
  apply (hsteps_trans _ (HB [] 0 1 5 (repeat (1, 2) 52 ++ (423, 2) :: (1, 1) :: repeat (1, 2) 1028 ++ (3357, 2) :: (1, 1) :: repeat (1, 2) 12064 ++ (26044, 2) :: (1, 1) :: repeat (1, 2) 109099 ++ (132761, 2) :: (1, 1) :: repeat (1, 2) 646580 ++ w) 1)).
  {
    exact (hsteps_step _ _ _ (hPX2B0 (repeat (1, 2) 51 ++ (423, 2) :: (1, 1) :: repeat (1, 2) 1028 ++ (3357, 2) :: (1, 1) :: repeat (1, 2) 12064 ++ (26044, 2) :: (1, 1) :: repeat (1, 2) 109099 ++ (132761, 2) :: (1, 1) :: repeat (1, 2) 646580 ++ w) 1) (hsteps_refl _)).
  }
  (* step 98: M pop12 (52,) *)
  apply (hsteps_trans _ (HB [] 52 1 109 ((423, 2) :: (1, 1) :: repeat (1, 2) 1028 ++ (3357, 2) :: (1, 1) :: repeat (1, 2) 12064 ++ (26044, 2) :: (1, 1) :: repeat (1, 2) 109099 ++ (132761, 2) :: (1, 1) :: repeat (1, 2) 646580 ++ w) 1)).
  {
    apply (pop12 52 [] 0 5 ((423, 2) :: (1, 1) :: repeat (1, 2) 1028 ++ (3357, 2) :: (1, 1) :: repeat (1, 2) 12064 ++ (26044, 2) :: (1, 1) :: repeat (1, 2) 109099 ++ (132761, 2) :: (1, 1) :: repeat (1, 2) 646580 ++ w) 1); closearith.
  }
  (* step 99: sTUP *)
  apply (hsteps_trans _ (HC [] 52 108 2 ((421, 2) :: (1, 1) :: repeat (1, 2) 1028 ++ (3357, 2) :: (1, 1) :: repeat (1, 2) 12064 ++ (26044, 2) :: (1, 1) :: repeat (1, 2) 109099 ++ (132761, 2) :: (1, 1) :: repeat (1, 2) 646580 ++ w) 1)).
  {
    replace ((421, 2) :: (1, 1) :: repeat (1, 2) 1028 ++ (3357, 2) :: (1, 1) :: repeat (1, 2) 12064 ++ (26044, 2) :: (1, 1) :: repeat (1, 2) 109099 ++ (132761, 2) :: (1, 1) :: repeat (1, 2) 646580 ++ w) with ((423 - 2, 2) :: (1, 1) :: repeat (1, 2) 1028 ++ (3357, 2) :: (1, 1) :: repeat (1, 2) 12064 ++ (26044, 2) :: (1, 1) :: repeat (1, 2) 109099 ++ (132761, 2) :: (1, 1) :: repeat (1, 2) 646580 ++ w) by sec_eq.
    apply (sTUP [] 52 109 423 2 ((1, 1) :: repeat (1, 2) 1028 ++ (3357, 2) :: (1, 1) :: repeat (1, 2) 12064 ++ (26044, 2) :: (1, 1) :: repeat (1, 2) 109099 ++ (132761, 2) :: (1, 1) :: repeat (1, 2) 646580 ++ w) 1); closearith.
  }
  (* step 100: P PUSH *)
  apply (hsteps_trans _ (HC [] 51 1 2 ((106, 2) :: (421, 2) :: (1, 1) :: repeat (1, 2) 1028 ++ (3357, 2) :: (1, 1) :: repeat (1, 2) 12064 ++ (26044, 2) :: (1, 1) :: repeat (1, 2) 109099 ++ (132761, 2) :: (1, 1) :: repeat (1, 2) 646580 ++ w) 1)).
  {
    replace ((106, 2) :: (421, 2) :: (1, 1) :: repeat (1, 2) 1028 ++ (3357, 2) :: (1, 1) :: repeat (1, 2) 12064 ++ (26044, 2) :: (1, 1) :: repeat (1, 2) 109099 ++ (132761, 2) :: (1, 1) :: repeat (1, 2) 646580 ++ w) with ((108 - 2, 2) :: (421, 2) :: (1, 1) :: repeat (1, 2) 1028 ++ (3357, 2) :: (1, 1) :: repeat (1, 2) 12064 ++ (26044, 2) :: (1, 1) :: repeat (1, 2) 109099 ++ (132761, 2) :: (1, 1) :: repeat (1, 2) 646580 ++ w) by sec_eq.
    apply (sPUSH [] 51 108 ((421, 2) :: (1, 1) :: repeat (1, 2) 1028 ++ (3357, 2) :: (1, 1) :: repeat (1, 2) 12064 ++ (26044, 2) :: (1, 1) :: repeat (1, 2) 109099 ++ (132761, 2) :: (1, 1) :: repeat (1, 2) 646580 ++ w) 1); closearith.
  }
  (* step 101: P TDN *)
  apply (hsteps_trans _ (HB [] 51 1 4 ((106, 2) :: (421, 2) :: (1, 1) :: repeat (1, 2) 1028 ++ (3357, 2) :: (1, 1) :: repeat (1, 2) 12064 ++ (26044, 2) :: (1, 1) :: repeat (1, 2) 109099 ++ (132761, 2) :: (1, 1) :: repeat (1, 2) 646580 ++ w) 1)).
  {
    apply (sTDN [] 51 ((106, 2) :: (421, 2) :: (1, 1) :: repeat (1, 2) 1028 ++ (3357, 2) :: (1, 1) :: repeat (1, 2) 12064 ++ (26044, 2) :: (1, 1) :: repeat (1, 2) 109099 ++ (132761, 2) :: (1, 1) :: repeat (1, 2) 646580 ++ w) 1).
  }
  (* step 102: sTUP *)
  apply (hsteps_trans _ (HC [] 51 3 2 ((104, 2) :: (421, 2) :: (1, 1) :: repeat (1, 2) 1028 ++ (3357, 2) :: (1, 1) :: repeat (1, 2) 12064 ++ (26044, 2) :: (1, 1) :: repeat (1, 2) 109099 ++ (132761, 2) :: (1, 1) :: repeat (1, 2) 646580 ++ w) 1)).
  {
    replace ((104, 2) :: (421, 2) :: (1, 1) :: repeat (1, 2) 1028 ++ (3357, 2) :: (1, 1) :: repeat (1, 2) 12064 ++ (26044, 2) :: (1, 1) :: repeat (1, 2) 109099 ++ (132761, 2) :: (1, 1) :: repeat (1, 2) 646580 ++ w) with ((106 - 2, 2) :: (421, 2) :: (1, 1) :: repeat (1, 2) 1028 ++ (3357, 2) :: (1, 1) :: repeat (1, 2) 12064 ++ (26044, 2) :: (1, 1) :: repeat (1, 2) 109099 ++ (132761, 2) :: (1, 1) :: repeat (1, 2) 646580 ++ w) by sec_eq.
    apply (sTUP [] 51 4 106 2 ((421, 2) :: (1, 1) :: repeat (1, 2) 1028 ++ (3357, 2) :: (1, 1) :: repeat (1, 2) 12064 ++ (26044, 2) :: (1, 1) :: repeat (1, 2) 109099 ++ (132761, 2) :: (1, 1) :: repeat (1, 2) 646580 ++ w) 1); closearith.
  }
  (* step 103: DIPGRIND 51 2 *)
  apply (hsteps_trans _ (HC [] 0 3 2 (repeat (1, 2) 51 ++ (2, 2) :: (421, 2) :: (1, 1) :: repeat (1, 2) 1028 ++ (3357, 2) :: (1, 1) :: repeat (1, 2) 12064 ++ (26044, 2) :: (1, 1) :: repeat (1, 2) 109099 ++ (132761, 2) :: (1, 1) :: repeat (1, 2) 646580 ++ w) 1)).
  {
    apply (DIPGRIND 51 2 [] ((421, 2) :: (1, 1) :: repeat (1, 2) 1028 ++ (3357, 2) :: (1, 1) :: repeat (1, 2) 12064 ++ (26044, 2) :: (1, 1) :: repeat (1, 2) 109099 ++ (132761, 2) :: (1, 1) :: repeat (1, 2) 646580 ++ w) 1); closearith.
  }
  (* step 104: P PUSHX *)
  apply (hsteps_trans _ (HB [] 1 1 7 (repeat (1, 2) 51 ++ (2, 2) :: (421, 2) :: (1, 1) :: repeat (1, 2) 1028 ++ (3357, 2) :: (1, 1) :: repeat (1, 2) 12064 ++ (26044, 2) :: (1, 1) :: repeat (1, 2) 109099 ++ (132761, 2) :: (1, 1) :: repeat (1, 2) 646580 ++ w) 1)).
  {
    exact (hsteps_step _ _ _ (hPUSHX (repeat (1, 2) 51 ++ (2, 2) :: (421, 2) :: (1, 1) :: repeat (1, 2) 1028 ++ (3357, 2) :: (1, 1) :: repeat (1, 2) 12064 ++ (26044, 2) :: (1, 1) :: repeat (1, 2) 109099 ++ (132761, 2) :: (1, 1) :: repeat (1, 2) 646580 ++ w) 1) (hsteps_refl _)).
  }
  (* step 105: M pop12 (51,) *)
  apply (hsteps_trans _ (HB [] 52 1 109 ((2, 2) :: (421, 2) :: (1, 1) :: repeat (1, 2) 1028 ++ (3357, 2) :: (1, 1) :: repeat (1, 2) 12064 ++ (26044, 2) :: (1, 1) :: repeat (1, 2) 109099 ++ (132761, 2) :: (1, 1) :: repeat (1, 2) 646580 ++ w) 1)).
  {
    apply (pop12 51 [] 1 7 ((2, 2) :: (421, 2) :: (1, 1) :: repeat (1, 2) 1028 ++ (3357, 2) :: (1, 1) :: repeat (1, 2) 12064 ++ (26044, 2) :: (1, 1) :: repeat (1, 2) 109099 ++ (132761, 2) :: (1, 1) :: repeat (1, 2) 646580 ++ w) 1); closearith.
  }
  (* step 106: P TUP2_1 *)
  apply (hsteps_trans _ (HC [53] 109 1 2 ((419, 2) :: (1, 1) :: repeat (1, 2) 1028 ++ (3357, 2) :: (1, 1) :: repeat (1, 2) 12064 ++ (26044, 2) :: (1, 1) :: repeat (1, 2) 109099 ++ (132761, 2) :: (1, 1) :: repeat (1, 2) 646580 ++ w) 1)).
  {
    replace ((419, 2) :: (1, 1) :: repeat (1, 2) 1028 ++ (3357, 2) :: (1, 1) :: repeat (1, 2) 12064 ++ (26044, 2) :: (1, 1) :: repeat (1, 2) 109099 ++ (132761, 2) :: (1, 1) :: repeat (1, 2) 646580 ++ w) with ((421 - 2, 2) :: (1, 1) :: repeat (1, 2) 1028 ++ (3357, 2) :: (1, 1) :: repeat (1, 2) 12064 ++ (26044, 2) :: (1, 1) :: repeat (1, 2) 109099 ++ (132761, 2) :: (1, 1) :: repeat (1, 2) 646580 ++ w) by sec_eq.
    apply (sTUP2_1 [] 52 108 421 ((1, 1) :: repeat (1, 2) 1028 ++ (3357, 2) :: (1, 1) :: repeat (1, 2) 12064 ++ (26044, 2) :: (1, 1) :: repeat (1, 2) 109099 ++ (132761, 2) :: (1, 1) :: repeat (1, 2) 646580 ++ w) 1); closearith.
  }
  (* step 107: P TDN *)
  apply (hsteps_trans _ (HB [53] 109 1 4 ((419, 2) :: (1, 1) :: repeat (1, 2) 1028 ++ (3357, 2) :: (1, 1) :: repeat (1, 2) 12064 ++ (26044, 2) :: (1, 1) :: repeat (1, 2) 109099 ++ (132761, 2) :: (1, 1) :: repeat (1, 2) 646580 ++ w) 1)).
  {
    apply (sTDN [53] 109 ((419, 2) :: (1, 1) :: repeat (1, 2) 1028 ++ (3357, 2) :: (1, 1) :: repeat (1, 2) 12064 ++ (26044, 2) :: (1, 1) :: repeat (1, 2) 109099 ++ (132761, 2) :: (1, 1) :: repeat (1, 2) 646580 ++ w) 1).
  }
  (* step 108: sTUP *)
  apply (hsteps_trans _ (HC [53] 109 3 2 ((417, 2) :: (1, 1) :: repeat (1, 2) 1028 ++ (3357, 2) :: (1, 1) :: repeat (1, 2) 12064 ++ (26044, 2) :: (1, 1) :: repeat (1, 2) 109099 ++ (132761, 2) :: (1, 1) :: repeat (1, 2) 646580 ++ w) 1)).
  {
    replace ((417, 2) :: (1, 1) :: repeat (1, 2) 1028 ++ (3357, 2) :: (1, 1) :: repeat (1, 2) 12064 ++ (26044, 2) :: (1, 1) :: repeat (1, 2) 109099 ++ (132761, 2) :: (1, 1) :: repeat (1, 2) 646580 ++ w) with ((419 - 2, 2) :: (1, 1) :: repeat (1, 2) 1028 ++ (3357, 2) :: (1, 1) :: repeat (1, 2) 12064 ++ (26044, 2) :: (1, 1) :: repeat (1, 2) 109099 ++ (132761, 2) :: (1, 1) :: repeat (1, 2) 646580 ++ w) by sec_eq.
    apply (sTUP [53] 109 4 419 2 ((1, 1) :: repeat (1, 2) 1028 ++ (3357, 2) :: (1, 1) :: repeat (1, 2) 12064 ++ (26044, 2) :: (1, 1) :: repeat (1, 2) 109099 ++ (132761, 2) :: (1, 1) :: repeat (1, 2) 646580 ++ w) 1); closearith.
  }
  (* step 109: DIPGRIND 109 199 *)
  apply (hsteps_trans _ (HC [53] 0 3 2 (repeat (1, 2) 109 ++ (199, 2) :: (1, 1) :: repeat (1, 2) 1028 ++ (3357, 2) :: (1, 1) :: repeat (1, 2) 12064 ++ (26044, 2) :: (1, 1) :: repeat (1, 2) 109099 ++ (132761, 2) :: (1, 1) :: repeat (1, 2) 646580 ++ w) 1)).
  {
    apply (DIPGRIND 109 199 [53] ((1, 1) :: repeat (1, 2) 1028 ++ (3357, 2) :: (1, 1) :: repeat (1, 2) 12064 ++ (26044, 2) :: (1, 1) :: repeat (1, 2) 109099 ++ (132761, 2) :: (1, 1) :: repeat (1, 2) 646580 ++ w) 1); closearith.
  }
  (* step 110: P PX2Bgen *)
  apply (hsteps_trans _ (HB [0] 3 1 2 ((49, 2) :: (1, 1) :: repeat (1, 2) 111 ++ (199, 2) :: (1, 1) :: repeat (1, 2) 1028 ++ (3357, 2) :: (1, 1) :: repeat (1, 2) 12064 ++ (26044, 2) :: (1, 1) :: repeat (1, 2) 109099 ++ (132761, 2) :: (1, 1) :: repeat (1, 2) 646580 ++ w) 1)).
  {
    exact (hsteps_step _ _ _ (hPX2Bgen 48 (repeat (1, 2) 109 ++ (199, 2) :: (1, 1) :: repeat (1, 2) 1028 ++ (3357, 2) :: (1, 1) :: repeat (1, 2) 12064 ++ (26044, 2) :: (1, 1) :: repeat (1, 2) 109099 ++ (132761, 2) :: (1, 1) :: repeat (1, 2) 646580 ++ w) 1) (hsteps_refl _)).
  }
  (* step 111: sTUP *)
  apply (hsteps_trans _ (HC [0] 3 1 2 ((47, 2) :: (1, 1) :: repeat (1, 2) 111 ++ (199, 2) :: (1, 1) :: repeat (1, 2) 1028 ++ (3357, 2) :: (1, 1) :: repeat (1, 2) 12064 ++ (26044, 2) :: (1, 1) :: repeat (1, 2) 109099 ++ (132761, 2) :: (1, 1) :: repeat (1, 2) 646580 ++ w) 1)).
  {
    replace ((47, 2) :: (1, 1) :: repeat (1, 2) 111 ++ (199, 2) :: (1, 1) :: repeat (1, 2) 1028 ++ (3357, 2) :: (1, 1) :: repeat (1, 2) 12064 ++ (26044, 2) :: (1, 1) :: repeat (1, 2) 109099 ++ (132761, 2) :: (1, 1) :: repeat (1, 2) 646580 ++ w) with ((49 - 2, 2) :: (1, 1) :: repeat (1, 2) 111 ++ (199, 2) :: (1, 1) :: repeat (1, 2) 1028 ++ (3357, 2) :: (1, 1) :: repeat (1, 2) 12064 ++ (26044, 2) :: (1, 1) :: repeat (1, 2) 109099 ++ (132761, 2) :: (1, 1) :: repeat (1, 2) 646580 ++ w) by sec_eq.
    apply (sTUP [0] 3 2 49 2 ((1, 1) :: repeat (1, 2) 111 ++ (199, 2) :: (1, 1) :: repeat (1, 2) 1028 ++ (3357, 2) :: (1, 1) :: repeat (1, 2) 12064 ++ (26044, 2) :: (1, 1) :: repeat (1, 2) 109099 ++ (132761, 2) :: (1, 1) :: repeat (1, 2) 646580 ++ w) 1); closearith.
  }
  (* step 112: P TDN *)
  apply (hsteps_trans _ (HB [0] 3 1 4 ((47, 2) :: (1, 1) :: repeat (1, 2) 111 ++ (199, 2) :: (1, 1) :: repeat (1, 2) 1028 ++ (3357, 2) :: (1, 1) :: repeat (1, 2) 12064 ++ (26044, 2) :: (1, 1) :: repeat (1, 2) 109099 ++ (132761, 2) :: (1, 1) :: repeat (1, 2) 646580 ++ w) 1)).
  {
    apply (sTDN [0] 3 ((47, 2) :: (1, 1) :: repeat (1, 2) 111 ++ (199, 2) :: (1, 1) :: repeat (1, 2) 1028 ++ (3357, 2) :: (1, 1) :: repeat (1, 2) 12064 ++ (26044, 2) :: (1, 1) :: repeat (1, 2) 109099 ++ (132761, 2) :: (1, 1) :: repeat (1, 2) 646580 ++ w) 1).
  }
  (* step 113: sTUP *)
  apply (hsteps_trans _ (HC [0] 3 3 2 ((45, 2) :: (1, 1) :: repeat (1, 2) 111 ++ (199, 2) :: (1, 1) :: repeat (1, 2) 1028 ++ (3357, 2) :: (1, 1) :: repeat (1, 2) 12064 ++ (26044, 2) :: (1, 1) :: repeat (1, 2) 109099 ++ (132761, 2) :: (1, 1) :: repeat (1, 2) 646580 ++ w) 1)).
  {
    replace ((45, 2) :: (1, 1) :: repeat (1, 2) 111 ++ (199, 2) :: (1, 1) :: repeat (1, 2) 1028 ++ (3357, 2) :: (1, 1) :: repeat (1, 2) 12064 ++ (26044, 2) :: (1, 1) :: repeat (1, 2) 109099 ++ (132761, 2) :: (1, 1) :: repeat (1, 2) 646580 ++ w) with ((47 - 2, 2) :: (1, 1) :: repeat (1, 2) 111 ++ (199, 2) :: (1, 1) :: repeat (1, 2) 1028 ++ (3357, 2) :: (1, 1) :: repeat (1, 2) 12064 ++ (26044, 2) :: (1, 1) :: repeat (1, 2) 109099 ++ (132761, 2) :: (1, 1) :: repeat (1, 2) 646580 ++ w) by sec_eq.
    apply (sTUP [0] 3 4 47 2 ((1, 1) :: repeat (1, 2) 111 ++ (199, 2) :: (1, 1) :: repeat (1, 2) 1028 ++ (3357, 2) :: (1, 1) :: repeat (1, 2) 12064 ++ (26044, 2) :: (1, 1) :: repeat (1, 2) 109099 ++ (132761, 2) :: (1, 1) :: repeat (1, 2) 646580 ++ w) 1); closearith.
  }
  (* step 114: DIPGRIND 3 39 *)
  apply (hsteps_trans _ (HC [0] 0 3 2 (repeat (1, 2) 3 ++ (39, 2) :: (1, 1) :: repeat (1, 2) 111 ++ (199, 2) :: (1, 1) :: repeat (1, 2) 1028 ++ (3357, 2) :: (1, 1) :: repeat (1, 2) 12064 ++ (26044, 2) :: (1, 1) :: repeat (1, 2) 109099 ++ (132761, 2) :: (1, 1) :: repeat (1, 2) 646580 ++ w) 1)).
  {
    apply (DIPGRIND 3 39 [0] ((1, 1) :: repeat (1, 2) 111 ++ (199, 2) :: (1, 1) :: repeat (1, 2) 1028 ++ (3357, 2) :: (1, 1) :: repeat (1, 2) 12064 ++ (26044, 2) :: (1, 1) :: repeat (1, 2) 109099 ++ (132761, 2) :: (1, 1) :: repeat (1, 2) 646580 ++ w) 1); closearith.
  }
  (* step 115: P PX2B0 *)
  apply (hsteps_trans _ (HB [] 0 1 5 (repeat (1, 2) 4 ++ (39, 2) :: (1, 1) :: repeat (1, 2) 111 ++ (199, 2) :: (1, 1) :: repeat (1, 2) 1028 ++ (3357, 2) :: (1, 1) :: repeat (1, 2) 12064 ++ (26044, 2) :: (1, 1) :: repeat (1, 2) 109099 ++ (132761, 2) :: (1, 1) :: repeat (1, 2) 646580 ++ w) 1)).
  {
    exact (hsteps_step _ _ _ (hPX2B0 (repeat (1, 2) 3 ++ (39, 2) :: (1, 1) :: repeat (1, 2) 111 ++ (199, 2) :: (1, 1) :: repeat (1, 2) 1028 ++ (3357, 2) :: (1, 1) :: repeat (1, 2) 12064 ++ (26044, 2) :: (1, 1) :: repeat (1, 2) 109099 ++ (132761, 2) :: (1, 1) :: repeat (1, 2) 646580 ++ w) 1) (hsteps_refl _)).
  }
  (* step 116: M pop12 (4,) *)
  apply (hsteps_trans _ (HB [] 4 1 13 ((39, 2) :: (1, 1) :: repeat (1, 2) 111 ++ (199, 2) :: (1, 1) :: repeat (1, 2) 1028 ++ (3357, 2) :: (1, 1) :: repeat (1, 2) 12064 ++ (26044, 2) :: (1, 1) :: repeat (1, 2) 109099 ++ (132761, 2) :: (1, 1) :: repeat (1, 2) 646580 ++ w) 1)).
  {
    apply (pop12 4 [] 0 5 ((39, 2) :: (1, 1) :: repeat (1, 2) 111 ++ (199, 2) :: (1, 1) :: repeat (1, 2) 1028 ++ (3357, 2) :: (1, 1) :: repeat (1, 2) 12064 ++ (26044, 2) :: (1, 1) :: repeat (1, 2) 109099 ++ (132761, 2) :: (1, 1) :: repeat (1, 2) 646580 ++ w) 1); closearith.
  }
  (* step 117: sTUP *)
  apply (hsteps_trans _ (HC [] 4 12 2 ((37, 2) :: (1, 1) :: repeat (1, 2) 111 ++ (199, 2) :: (1, 1) :: repeat (1, 2) 1028 ++ (3357, 2) :: (1, 1) :: repeat (1, 2) 12064 ++ (26044, 2) :: (1, 1) :: repeat (1, 2) 109099 ++ (132761, 2) :: (1, 1) :: repeat (1, 2) 646580 ++ w) 1)).
  {
    replace ((37, 2) :: (1, 1) :: repeat (1, 2) 111 ++ (199, 2) :: (1, 1) :: repeat (1, 2) 1028 ++ (3357, 2) :: (1, 1) :: repeat (1, 2) 12064 ++ (26044, 2) :: (1, 1) :: repeat (1, 2) 109099 ++ (132761, 2) :: (1, 1) :: repeat (1, 2) 646580 ++ w) with ((39 - 2, 2) :: (1, 1) :: repeat (1, 2) 111 ++ (199, 2) :: (1, 1) :: repeat (1, 2) 1028 ++ (3357, 2) :: (1, 1) :: repeat (1, 2) 12064 ++ (26044, 2) :: (1, 1) :: repeat (1, 2) 109099 ++ (132761, 2) :: (1, 1) :: repeat (1, 2) 646580 ++ w) by sec_eq.
    apply (sTUP [] 4 13 39 2 ((1, 1) :: repeat (1, 2) 111 ++ (199, 2) :: (1, 1) :: repeat (1, 2) 1028 ++ (3357, 2) :: (1, 1) :: repeat (1, 2) 12064 ++ (26044, 2) :: (1, 1) :: repeat (1, 2) 109099 ++ (132761, 2) :: (1, 1) :: repeat (1, 2) 646580 ++ w) 1); closearith.
  }
  (* step 118: P PUSH *)
  apply (hsteps_trans _ (HC [] 3 1 2 ((10, 2) :: (37, 2) :: (1, 1) :: repeat (1, 2) 111 ++ (199, 2) :: (1, 1) :: repeat (1, 2) 1028 ++ (3357, 2) :: (1, 1) :: repeat (1, 2) 12064 ++ (26044, 2) :: (1, 1) :: repeat (1, 2) 109099 ++ (132761, 2) :: (1, 1) :: repeat (1, 2) 646580 ++ w) 1)).
  {
    replace ((10, 2) :: (37, 2) :: (1, 1) :: repeat (1, 2) 111 ++ (199, 2) :: (1, 1) :: repeat (1, 2) 1028 ++ (3357, 2) :: (1, 1) :: repeat (1, 2) 12064 ++ (26044, 2) :: (1, 1) :: repeat (1, 2) 109099 ++ (132761, 2) :: (1, 1) :: repeat (1, 2) 646580 ++ w) with ((12 - 2, 2) :: (37, 2) :: (1, 1) :: repeat (1, 2) 111 ++ (199, 2) :: (1, 1) :: repeat (1, 2) 1028 ++ (3357, 2) :: (1, 1) :: repeat (1, 2) 12064 ++ (26044, 2) :: (1, 1) :: repeat (1, 2) 109099 ++ (132761, 2) :: (1, 1) :: repeat (1, 2) 646580 ++ w) by sec_eq.
    apply (sPUSH [] 3 12 ((37, 2) :: (1, 1) :: repeat (1, 2) 111 ++ (199, 2) :: (1, 1) :: repeat (1, 2) 1028 ++ (3357, 2) :: (1, 1) :: repeat (1, 2) 12064 ++ (26044, 2) :: (1, 1) :: repeat (1, 2) 109099 ++ (132761, 2) :: (1, 1) :: repeat (1, 2) 646580 ++ w) 1); closearith.
  }
  (* step 119: P TDN *)
  apply (hsteps_trans _ (HB [] 3 1 4 ((10, 2) :: (37, 2) :: (1, 1) :: repeat (1, 2) 111 ++ (199, 2) :: (1, 1) :: repeat (1, 2) 1028 ++ (3357, 2) :: (1, 1) :: repeat (1, 2) 12064 ++ (26044, 2) :: (1, 1) :: repeat (1, 2) 109099 ++ (132761, 2) :: (1, 1) :: repeat (1, 2) 646580 ++ w) 1)).
  {
    apply (sTDN [] 3 ((10, 2) :: (37, 2) :: (1, 1) :: repeat (1, 2) 111 ++ (199, 2) :: (1, 1) :: repeat (1, 2) 1028 ++ (3357, 2) :: (1, 1) :: repeat (1, 2) 12064 ++ (26044, 2) :: (1, 1) :: repeat (1, 2) 109099 ++ (132761, 2) :: (1, 1) :: repeat (1, 2) 646580 ++ w) 1).
  }
  (* step 120: sTUP *)
  apply (hsteps_trans _ (HC [] 3 3 2 ((8, 2) :: (37, 2) :: (1, 1) :: repeat (1, 2) 111 ++ (199, 2) :: (1, 1) :: repeat (1, 2) 1028 ++ (3357, 2) :: (1, 1) :: repeat (1, 2) 12064 ++ (26044, 2) :: (1, 1) :: repeat (1, 2) 109099 ++ (132761, 2) :: (1, 1) :: repeat (1, 2) 646580 ++ w) 1)).
  {
    replace ((8, 2) :: (37, 2) :: (1, 1) :: repeat (1, 2) 111 ++ (199, 2) :: (1, 1) :: repeat (1, 2) 1028 ++ (3357, 2) :: (1, 1) :: repeat (1, 2) 12064 ++ (26044, 2) :: (1, 1) :: repeat (1, 2) 109099 ++ (132761, 2) :: (1, 1) :: repeat (1, 2) 646580 ++ w) with ((10 - 2, 2) :: (37, 2) :: (1, 1) :: repeat (1, 2) 111 ++ (199, 2) :: (1, 1) :: repeat (1, 2) 1028 ++ (3357, 2) :: (1, 1) :: repeat (1, 2) 12064 ++ (26044, 2) :: (1, 1) :: repeat (1, 2) 109099 ++ (132761, 2) :: (1, 1) :: repeat (1, 2) 646580 ++ w) by sec_eq.
    apply (sTUP [] 3 4 10 2 ((37, 2) :: (1, 1) :: repeat (1, 2) 111 ++ (199, 2) :: (1, 1) :: repeat (1, 2) 1028 ++ (3357, 2) :: (1, 1) :: repeat (1, 2) 12064 ++ (26044, 2) :: (1, 1) :: repeat (1, 2) 109099 ++ (132761, 2) :: (1, 1) :: repeat (1, 2) 646580 ++ w) 1); closearith.
  }
  (* step 121: DIPGRIND 3 2 *)
  apply (hsteps_trans _ (HC [] 0 3 2 (repeat (1, 2) 3 ++ (2, 2) :: (37, 2) :: (1, 1) :: repeat (1, 2) 111 ++ (199, 2) :: (1, 1) :: repeat (1, 2) 1028 ++ (3357, 2) :: (1, 1) :: repeat (1, 2) 12064 ++ (26044, 2) :: (1, 1) :: repeat (1, 2) 109099 ++ (132761, 2) :: (1, 1) :: repeat (1, 2) 646580 ++ w) 1)).
  {
    apply (DIPGRIND 3 2 [] ((37, 2) :: (1, 1) :: repeat (1, 2) 111 ++ (199, 2) :: (1, 1) :: repeat (1, 2) 1028 ++ (3357, 2) :: (1, 1) :: repeat (1, 2) 12064 ++ (26044, 2) :: (1, 1) :: repeat (1, 2) 109099 ++ (132761, 2) :: (1, 1) :: repeat (1, 2) 646580 ++ w) 1); closearith.
  }
  (* step 122: P PUSHX *)
  apply (hsteps_trans _ (HB [] 1 1 7 (repeat (1, 2) 3 ++ (2, 2) :: (37, 2) :: (1, 1) :: repeat (1, 2) 111 ++ (199, 2) :: (1, 1) :: repeat (1, 2) 1028 ++ (3357, 2) :: (1, 1) :: repeat (1, 2) 12064 ++ (26044, 2) :: (1, 1) :: repeat (1, 2) 109099 ++ (132761, 2) :: (1, 1) :: repeat (1, 2) 646580 ++ w) 1)).
  {
    exact (hsteps_step _ _ _ (hPUSHX (repeat (1, 2) 3 ++ (2, 2) :: (37, 2) :: (1, 1) :: repeat (1, 2) 111 ++ (199, 2) :: (1, 1) :: repeat (1, 2) 1028 ++ (3357, 2) :: (1, 1) :: repeat (1, 2) 12064 ++ (26044, 2) :: (1, 1) :: repeat (1, 2) 109099 ++ (132761, 2) :: (1, 1) :: repeat (1, 2) 646580 ++ w) 1) (hsteps_refl _)).
  }
  (* step 123: M pop12 (3,) *)
  apply (hsteps_trans _ (HB [] 4 1 13 ((2, 2) :: (37, 2) :: (1, 1) :: repeat (1, 2) 111 ++ (199, 2) :: (1, 1) :: repeat (1, 2) 1028 ++ (3357, 2) :: (1, 1) :: repeat (1, 2) 12064 ++ (26044, 2) :: (1, 1) :: repeat (1, 2) 109099 ++ (132761, 2) :: (1, 1) :: repeat (1, 2) 646580 ++ w) 1)).
  {
    apply (pop12 3 [] 1 7 ((2, 2) :: (37, 2) :: (1, 1) :: repeat (1, 2) 111 ++ (199, 2) :: (1, 1) :: repeat (1, 2) 1028 ++ (3357, 2) :: (1, 1) :: repeat (1, 2) 12064 ++ (26044, 2) :: (1, 1) :: repeat (1, 2) 109099 ++ (132761, 2) :: (1, 1) :: repeat (1, 2) 646580 ++ w) 1); closearith.
  }
  (* step 124: P TUP2_1 *)
  apply (hsteps_trans _ (HC [5] 13 1 2 ((35, 2) :: (1, 1) :: repeat (1, 2) 111 ++ (199, 2) :: (1, 1) :: repeat (1, 2) 1028 ++ (3357, 2) :: (1, 1) :: repeat (1, 2) 12064 ++ (26044, 2) :: (1, 1) :: repeat (1, 2) 109099 ++ (132761, 2) :: (1, 1) :: repeat (1, 2) 646580 ++ w) 1)).
  {
    replace ((35, 2) :: (1, 1) :: repeat (1, 2) 111 ++ (199, 2) :: (1, 1) :: repeat (1, 2) 1028 ++ (3357, 2) :: (1, 1) :: repeat (1, 2) 12064 ++ (26044, 2) :: (1, 1) :: repeat (1, 2) 109099 ++ (132761, 2) :: (1, 1) :: repeat (1, 2) 646580 ++ w) with ((37 - 2, 2) :: (1, 1) :: repeat (1, 2) 111 ++ (199, 2) :: (1, 1) :: repeat (1, 2) 1028 ++ (3357, 2) :: (1, 1) :: repeat (1, 2) 12064 ++ (26044, 2) :: (1, 1) :: repeat (1, 2) 109099 ++ (132761, 2) :: (1, 1) :: repeat (1, 2) 646580 ++ w) by sec_eq.
    apply (sTUP2_1 [] 4 12 37 ((1, 1) :: repeat (1, 2) 111 ++ (199, 2) :: (1, 1) :: repeat (1, 2) 1028 ++ (3357, 2) :: (1, 1) :: repeat (1, 2) 12064 ++ (26044, 2) :: (1, 1) :: repeat (1, 2) 109099 ++ (132761, 2) :: (1, 1) :: repeat (1, 2) 646580 ++ w) 1); closearith.
  }
  (* step 125: P TDN *)
  apply (hsteps_trans _ (HB [5] 13 1 4 ((35, 2) :: (1, 1) :: repeat (1, 2) 111 ++ (199, 2) :: (1, 1) :: repeat (1, 2) 1028 ++ (3357, 2) :: (1, 1) :: repeat (1, 2) 12064 ++ (26044, 2) :: (1, 1) :: repeat (1, 2) 109099 ++ (132761, 2) :: (1, 1) :: repeat (1, 2) 646580 ++ w) 1)).
  {
    apply (sTDN [5] 13 ((35, 2) :: (1, 1) :: repeat (1, 2) 111 ++ (199, 2) :: (1, 1) :: repeat (1, 2) 1028 ++ (3357, 2) :: (1, 1) :: repeat (1, 2) 12064 ++ (26044, 2) :: (1, 1) :: repeat (1, 2) 109099 ++ (132761, 2) :: (1, 1) :: repeat (1, 2) 646580 ++ w) 1).
  }
  (* step 126: sTUP *)
  apply (hsteps_trans _ (HC [5] 13 3 2 ((33, 2) :: (1, 1) :: repeat (1, 2) 111 ++ (199, 2) :: (1, 1) :: repeat (1, 2) 1028 ++ (3357, 2) :: (1, 1) :: repeat (1, 2) 12064 ++ (26044, 2) :: (1, 1) :: repeat (1, 2) 109099 ++ (132761, 2) :: (1, 1) :: repeat (1, 2) 646580 ++ w) 1)).
  {
    replace ((33, 2) :: (1, 1) :: repeat (1, 2) 111 ++ (199, 2) :: (1, 1) :: repeat (1, 2) 1028 ++ (3357, 2) :: (1, 1) :: repeat (1, 2) 12064 ++ (26044, 2) :: (1, 1) :: repeat (1, 2) 109099 ++ (132761, 2) :: (1, 1) :: repeat (1, 2) 646580 ++ w) with ((35 - 2, 2) :: (1, 1) :: repeat (1, 2) 111 ++ (199, 2) :: (1, 1) :: repeat (1, 2) 1028 ++ (3357, 2) :: (1, 1) :: repeat (1, 2) 12064 ++ (26044, 2) :: (1, 1) :: repeat (1, 2) 109099 ++ (132761, 2) :: (1, 1) :: repeat (1, 2) 646580 ++ w) by sec_eq.
    apply (sTUP [5] 13 4 35 2 ((1, 1) :: repeat (1, 2) 111 ++ (199, 2) :: (1, 1) :: repeat (1, 2) 1028 ++ (3357, 2) :: (1, 1) :: repeat (1, 2) 12064 ++ (26044, 2) :: (1, 1) :: repeat (1, 2) 109099 ++ (132761, 2) :: (1, 1) :: repeat (1, 2) 646580 ++ w) 1); closearith.
  }
  (* step 127: DIPGRIND 13 7 *)
  apply (hsteps_trans _ (HC [5] 0 3 2 (repeat (1, 2) 13 ++ (7, 2) :: (1, 1) :: repeat (1, 2) 111 ++ (199, 2) :: (1, 1) :: repeat (1, 2) 1028 ++ (3357, 2) :: (1, 1) :: repeat (1, 2) 12064 ++ (26044, 2) :: (1, 1) :: repeat (1, 2) 109099 ++ (132761, 2) :: (1, 1) :: repeat (1, 2) 646580 ++ w) 1)).
  {
    apply (DIPGRIND 13 7 [5] ((1, 1) :: repeat (1, 2) 111 ++ (199, 2) :: (1, 1) :: repeat (1, 2) 1028 ++ (3357, 2) :: (1, 1) :: repeat (1, 2) 12064 ++ (26044, 2) :: (1, 1) :: repeat (1, 2) 109099 ++ (132761, 2) :: (1, 1) :: repeat (1, 2) 646580 ++ w) 1); closearith.
  }
  (* step 128: P PX2Bgen *)
  apply (hsteps_trans _ (HB [0] 3 1 2 (repeat (1, 2) 1 ++ (1, 1) :: repeat (1, 2) 15 ++ (7, 2) :: (1, 1) :: repeat (1, 2) 111 ++ (199, 2) :: (1, 1) :: repeat (1, 2) 1028 ++ (3357, 2) :: (1, 1) :: repeat (1, 2) 12064 ++ (26044, 2) :: (1, 1) :: repeat (1, 2) 109099 ++ (132761, 2) :: (1, 1) :: repeat (1, 2) 646580 ++ w) 1)).
  {
    exact (hsteps_step _ _ _ (hPX2Bgen 0 (repeat (1, 2) 13 ++ (7, 2) :: (1, 1) :: repeat (1, 2) 111 ++ (199, 2) :: (1, 1) :: repeat (1, 2) 1028 ++ (3357, 2) :: (1, 1) :: repeat (1, 2) 12064 ++ (26044, 2) :: (1, 1) :: repeat (1, 2) 109099 ++ (132761, 2) :: (1, 1) :: repeat (1, 2) 646580 ++ w) 1) (hsteps_refl _)).
  }
  (* step 129: M pop12 (1,) *)
  apply (hsteps_trans _ (HB [0] 4 1 4 ((1, 1) :: repeat (1, 2) 15 ++ (7, 2) :: (1, 1) :: repeat (1, 2) 111 ++ (199, 2) :: (1, 1) :: repeat (1, 2) 1028 ++ (3357, 2) :: (1, 1) :: repeat (1, 2) 12064 ++ (26044, 2) :: (1, 1) :: repeat (1, 2) 109099 ++ (132761, 2) :: (1, 1) :: repeat (1, 2) 646580 ++ w) 1)).
  {
    apply (pop12 1 [0] 3 2 ((1, 1) :: repeat (1, 2) 15 ++ (7, 2) :: (1, 1) :: repeat (1, 2) 111 ++ (199, 2) :: (1, 1) :: repeat (1, 2) 1028 ++ (3357, 2) :: (1, 1) :: repeat (1, 2) 12064 ++ (26044, 2) :: (1, 1) :: repeat (1, 2) 109099 ++ (132761, 2) :: (1, 1) :: repeat (1, 2) 646580 ++ w) 1); closearith.
  }
  (* step 130: P POP *)
  apply (hsteps_trans _ (HB [0] 5 1 5 (repeat (1, 2) 15 ++ (7, 2) :: (1, 1) :: repeat (1, 2) 111 ++ (199, 2) :: (1, 1) :: repeat (1, 2) 1028 ++ (3357, 2) :: (1, 1) :: repeat (1, 2) 12064 ++ (26044, 2) :: (1, 1) :: repeat (1, 2) 109099 ++ (132761, 2) :: (1, 1) :: repeat (1, 2) 646580 ++ w) 1)).
  {
    apply (sPOP1 [0] 4 4 (repeat (1, 2) 15 ++ (7, 2) :: (1, 1) :: repeat (1, 2) 111 ++ (199, 2) :: (1, 1) :: repeat (1, 2) 1028 ++ (3357, 2) :: (1, 1) :: repeat (1, 2) 12064 ++ (26044, 2) :: (1, 1) :: repeat (1, 2) 109099 ++ (132761, 2) :: (1, 1) :: repeat (1, 2) 646580 ++ w) 1); closearith.
  }
  (* step 131: M pop12 (15,) *)
  apply (hsteps_trans _ (HB [0] 20 1 35 ((7, 2) :: (1, 1) :: repeat (1, 2) 111 ++ (199, 2) :: (1, 1) :: repeat (1, 2) 1028 ++ (3357, 2) :: (1, 1) :: repeat (1, 2) 12064 ++ (26044, 2) :: (1, 1) :: repeat (1, 2) 109099 ++ (132761, 2) :: (1, 1) :: repeat (1, 2) 646580 ++ w) 1)).
  {
    apply (pop12 15 [0] 5 5 ((7, 2) :: (1, 1) :: repeat (1, 2) 111 ++ (199, 2) :: (1, 1) :: repeat (1, 2) 1028 ++ (3357, 2) :: (1, 1) :: repeat (1, 2) 12064 ++ (26044, 2) :: (1, 1) :: repeat (1, 2) 109099 ++ (132761, 2) :: (1, 1) :: repeat (1, 2) 646580 ++ w) 1); closearith.
  }
  (* step 132: sTUP *)
  replace ((5, 2) :: (1, 1) :: repeat (1, 2) 111 ++ (199, 2) :: (1, 1) :: repeat (1, 2) 1028 ++ (3357, 2) :: (1, 1) :: repeat (1, 2) 12064 ++ (26044, 2) :: (1, 1) :: repeat (1, 2) 109099 ++ (132761, 2) :: (1, 1) :: repeat (1, 2) 646580 ++ w) with ((7 - 2, 2) :: (1, 1) :: repeat (1, 2) 111 ++ (199, 2) :: (1, 1) :: repeat (1, 2) 1028 ++ (3357, 2) :: (1, 1) :: repeat (1, 2) 12064 ++ (26044, 2) :: (1, 1) :: repeat (1, 2) 109099 ++ (132761, 2) :: (1, 1) :: repeat (1, 2) 646580 ++ w) by sec_eq.
  apply (sTUP [0] 20 35 7 2 ((1, 1) :: repeat (1, 2) 111 ++ (199, 2) :: (1, 1) :: repeat (1, 2) 1028 ++ (3357, 2) :: (1, 1) :: repeat (1, 2) 12064 ++ (26044, 2) :: (1, 1) :: repeat (1, 2) 109099 ++ (132761, 2) :: (1, 1) :: repeat (1, 2) 646580 ++ w) 1); closearith.
Qed.

(* CASCADE54d: steps 133-175 of the CASCADE54 chain. *)
Lemma CASCADE54d : forall w,
  hsteps (HC [0] 20 34 2 ((5, 2) :: (1, 1) :: repeat (1, 2) 111 ++ (199, 2) :: (1, 1) :: repeat (1, 2) 1028 ++ (3357, 2) :: (1, 1) :: repeat (1, 2) 12064 ++ (26044, 2) :: (1, 1) :: repeat (1, 2) 109099 ++ (132761, 2) :: (1, 1) :: repeat (1, 2) 646580 ++ w) 1)
         (HB [135142; 27487; 14322; 1260; 147; 20; 0] 218202 1 132763 (repeat (1, 2) 646580 ++ w) 1).
Proof.
  intro w.
  (* step 133: hGRIND_even 15 *)
  apply (hsteps_trans _ (HB [0] 19 1 34 ((2, 2) :: (5, 2) :: (1, 1) :: repeat (1, 2) 111 ++ (199, 2) :: (1, 1) :: repeat (1, 2) 1028 ++ (3357, 2) :: (1, 1) :: repeat (1, 2) 12064 ++ (26044, 2) :: (1, 1) :: repeat (1, 2) 109099 ++ (132761, 2) :: (1, 1) :: repeat (1, 2) 646580 ++ w) 1)).
  {
    apply (hGRIND_even 15 [0] 19 ((5, 2) :: (1, 1) :: repeat (1, 2) 111 ++ (199, 2) :: (1, 1) :: repeat (1, 2) 1028 ++ (3357, 2) :: (1, 1) :: repeat (1, 2) 12064 ++ (26044, 2) :: (1, 1) :: repeat (1, 2) 109099 ++ (132761, 2) :: (1, 1) :: repeat (1, 2) 646580 ++ w) 1); closearith.
  }
  (* step 134: P TUP2_1 *)
  apply (hsteps_trans _ (HC [20; 0] 34 1 2 ((3, 2) :: (1, 1) :: repeat (1, 2) 111 ++ (199, 2) :: (1, 1) :: repeat (1, 2) 1028 ++ (3357, 2) :: (1, 1) :: repeat (1, 2) 12064 ++ (26044, 2) :: (1, 1) :: repeat (1, 2) 109099 ++ (132761, 2) :: (1, 1) :: repeat (1, 2) 646580 ++ w) 1)).
  {
    replace ((3, 2) :: (1, 1) :: repeat (1, 2) 111 ++ (199, 2) :: (1, 1) :: repeat (1, 2) 1028 ++ (3357, 2) :: (1, 1) :: repeat (1, 2) 12064 ++ (26044, 2) :: (1, 1) :: repeat (1, 2) 109099 ++ (132761, 2) :: (1, 1) :: repeat (1, 2) 646580 ++ w) with ((5 - 2, 2) :: (1, 1) :: repeat (1, 2) 111 ++ (199, 2) :: (1, 1) :: repeat (1, 2) 1028 ++ (3357, 2) :: (1, 1) :: repeat (1, 2) 12064 ++ (26044, 2) :: (1, 1) :: repeat (1, 2) 109099 ++ (132761, 2) :: (1, 1) :: repeat (1, 2) 646580 ++ w) by sec_eq.
    apply (sTUP2_1 [0] 19 33 5 ((1, 1) :: repeat (1, 2) 111 ++ (199, 2) :: (1, 1) :: repeat (1, 2) 1028 ++ (3357, 2) :: (1, 1) :: repeat (1, 2) 12064 ++ (26044, 2) :: (1, 1) :: repeat (1, 2) 109099 ++ (132761, 2) :: (1, 1) :: repeat (1, 2) 646580 ++ w) 1); closearith.
  }
  (* step 135: P TDN *)
  apply (hsteps_trans _ (HB [20; 0] 34 1 4 ((3, 2) :: (1, 1) :: repeat (1, 2) 111 ++ (199, 2) :: (1, 1) :: repeat (1, 2) 1028 ++ (3357, 2) :: (1, 1) :: repeat (1, 2) 12064 ++ (26044, 2) :: (1, 1) :: repeat (1, 2) 109099 ++ (132761, 2) :: (1, 1) :: repeat (1, 2) 646580 ++ w) 1)).
  {
    apply (sTDN [20; 0] 34 ((3, 2) :: (1, 1) :: repeat (1, 2) 111 ++ (199, 2) :: (1, 1) :: repeat (1, 2) 1028 ++ (3357, 2) :: (1, 1) :: repeat (1, 2) 12064 ++ (26044, 2) :: (1, 1) :: repeat (1, 2) 109099 ++ (132761, 2) :: (1, 1) :: repeat (1, 2) 646580 ++ w) 1).
  }
  (* step 136: sTUP *)
  apply (hsteps_trans _ (HC [20; 0] 34 3 2 (repeat (1, 2) 1 ++ (1, 1) :: repeat (1, 2) 111 ++ (199, 2) :: (1, 1) :: repeat (1, 2) 1028 ++ (3357, 2) :: (1, 1) :: repeat (1, 2) 12064 ++ (26044, 2) :: (1, 1) :: repeat (1, 2) 109099 ++ (132761, 2) :: (1, 1) :: repeat (1, 2) 646580 ++ w) 1)).
  {
    replace (repeat (1, 2) 1 ++ (1, 1) :: repeat (1, 2) 111 ++ (199, 2) :: (1, 1) :: repeat (1, 2) 1028 ++ (3357, 2) :: (1, 1) :: repeat (1, 2) 12064 ++ (26044, 2) :: (1, 1) :: repeat (1, 2) 109099 ++ (132761, 2) :: (1, 1) :: repeat (1, 2) 646580 ++ w) with ((3 - 2, 2) :: (1, 1) :: repeat (1, 2) 111 ++ (199, 2) :: (1, 1) :: repeat (1, 2) 1028 ++ (3357, 2) :: (1, 1) :: repeat (1, 2) 12064 ++ (26044, 2) :: (1, 1) :: repeat (1, 2) 109099 ++ (132761, 2) :: (1, 1) :: repeat (1, 2) 646580 ++ w) by sec_eq.
    apply (sTUP [20; 0] 34 4 3 2 ((1, 1) :: repeat (1, 2) 111 ++ (199, 2) :: (1, 1) :: repeat (1, 2) 1028 ++ (3357, 2) :: (1, 1) :: repeat (1, 2) 12064 ++ (26044, 2) :: (1, 1) :: repeat (1, 2) 109099 ++ (132761, 2) :: (1, 1) :: repeat (1, 2) 646580 ++ w) 1); closearith.
  }
  (* step 137: P PUSH *)
  apply (hsteps_trans _ (HC [20; 0] 33 1 2 (repeat (1, 2) 2 ++ (1, 1) :: repeat (1, 2) 111 ++ (199, 2) :: (1, 1) :: repeat (1, 2) 1028 ++ (3357, 2) :: (1, 1) :: repeat (1, 2) 12064 ++ (26044, 2) :: (1, 1) :: repeat (1, 2) 109099 ++ (132761, 2) :: (1, 1) :: repeat (1, 2) 646580 ++ w) 1)).
  {
    replace (repeat (1, 2) 2 ++ (1, 1) :: repeat (1, 2) 111 ++ (199, 2) :: (1, 1) :: repeat (1, 2) 1028 ++ (3357, 2) :: (1, 1) :: repeat (1, 2) 12064 ++ (26044, 2) :: (1, 1) :: repeat (1, 2) 109099 ++ (132761, 2) :: (1, 1) :: repeat (1, 2) 646580 ++ w) with ((3 - 2, 2) :: repeat (1, 2) 1 ++ (1, 1) :: repeat (1, 2) 111 ++ (199, 2) :: (1, 1) :: repeat (1, 2) 1028 ++ (3357, 2) :: (1, 1) :: repeat (1, 2) 12064 ++ (26044, 2) :: (1, 1) :: repeat (1, 2) 109099 ++ (132761, 2) :: (1, 1) :: repeat (1, 2) 646580 ++ w) by sec_eq.
    apply (sPUSH [20; 0] 33 3 (repeat (1, 2) 1 ++ (1, 1) :: repeat (1, 2) 111 ++ (199, 2) :: (1, 1) :: repeat (1, 2) 1028 ++ (3357, 2) :: (1, 1) :: repeat (1, 2) 12064 ++ (26044, 2) :: (1, 1) :: repeat (1, 2) 109099 ++ (132761, 2) :: (1, 1) :: repeat (1, 2) 646580 ++ w) 1); closearith.
  }
  (* step 138: P TDN *)
  apply (hsteps_trans _ (HB [20; 0] 33 1 4 (repeat (1, 2) 2 ++ (1, 1) :: repeat (1, 2) 111 ++ (199, 2) :: (1, 1) :: repeat (1, 2) 1028 ++ (3357, 2) :: (1, 1) :: repeat (1, 2) 12064 ++ (26044, 2) :: (1, 1) :: repeat (1, 2) 109099 ++ (132761, 2) :: (1, 1) :: repeat (1, 2) 646580 ++ w) 1)).
  {
    apply (sTDN [20; 0] 33 (repeat (1, 2) 2 ++ (1, 1) :: repeat (1, 2) 111 ++ (199, 2) :: (1, 1) :: repeat (1, 2) 1028 ++ (3357, 2) :: (1, 1) :: repeat (1, 2) 12064 ++ (26044, 2) :: (1, 1) :: repeat (1, 2) 109099 ++ (132761, 2) :: (1, 1) :: repeat (1, 2) 646580 ++ w) 1).
  }
  (* step 139: M pop12 (2,) *)
  apply (hsteps_trans _ (HB [20; 0] 35 1 8 ((1, 1) :: repeat (1, 2) 111 ++ (199, 2) :: (1, 1) :: repeat (1, 2) 1028 ++ (3357, 2) :: (1, 1) :: repeat (1, 2) 12064 ++ (26044, 2) :: (1, 1) :: repeat (1, 2) 109099 ++ (132761, 2) :: (1, 1) :: repeat (1, 2) 646580 ++ w) 1)).
  {
    apply (pop12 2 [20; 0] 33 4 ((1, 1) :: repeat (1, 2) 111 ++ (199, 2) :: (1, 1) :: repeat (1, 2) 1028 ++ (3357, 2) :: (1, 1) :: repeat (1, 2) 12064 ++ (26044, 2) :: (1, 1) :: repeat (1, 2) 109099 ++ (132761, 2) :: (1, 1) :: repeat (1, 2) 646580 ++ w) 1); closearith.
  }
  (* step 140: P POP *)
  apply (hsteps_trans _ (HB [20; 0] 36 1 9 (repeat (1, 2) 111 ++ (199, 2) :: (1, 1) :: repeat (1, 2) 1028 ++ (3357, 2) :: (1, 1) :: repeat (1, 2) 12064 ++ (26044, 2) :: (1, 1) :: repeat (1, 2) 109099 ++ (132761, 2) :: (1, 1) :: repeat (1, 2) 646580 ++ w) 1)).
  {
    apply (sPOP1 [20; 0] 35 8 (repeat (1, 2) 111 ++ (199, 2) :: (1, 1) :: repeat (1, 2) 1028 ++ (3357, 2) :: (1, 1) :: repeat (1, 2) 12064 ++ (26044, 2) :: (1, 1) :: repeat (1, 2) 109099 ++ (132761, 2) :: (1, 1) :: repeat (1, 2) 646580 ++ w) 1); closearith.
  }
  (* step 141: M pop12 (111,) *)
  apply (hsteps_trans _ (HB [20; 0] 147 1 231 ((199, 2) :: (1, 1) :: repeat (1, 2) 1028 ++ (3357, 2) :: (1, 1) :: repeat (1, 2) 12064 ++ (26044, 2) :: (1, 1) :: repeat (1, 2) 109099 ++ (132761, 2) :: (1, 1) :: repeat (1, 2) 646580 ++ w) 1)).
  {
    apply (pop12 111 [20; 0] 36 9 ((199, 2) :: (1, 1) :: repeat (1, 2) 1028 ++ (3357, 2) :: (1, 1) :: repeat (1, 2) 12064 ++ (26044, 2) :: (1, 1) :: repeat (1, 2) 109099 ++ (132761, 2) :: (1, 1) :: repeat (1, 2) 646580 ++ w) 1); closearith.
  }
  (* step 142: sTUP *)
  apply (hsteps_trans _ (HC [20; 0] 147 230 2 ((197, 2) :: (1, 1) :: repeat (1, 2) 1028 ++ (3357, 2) :: (1, 1) :: repeat (1, 2) 12064 ++ (26044, 2) :: (1, 1) :: repeat (1, 2) 109099 ++ (132761, 2) :: (1, 1) :: repeat (1, 2) 646580 ++ w) 1)).
  {
    replace ((197, 2) :: (1, 1) :: repeat (1, 2) 1028 ++ (3357, 2) :: (1, 1) :: repeat (1, 2) 12064 ++ (26044, 2) :: (1, 1) :: repeat (1, 2) 109099 ++ (132761, 2) :: (1, 1) :: repeat (1, 2) 646580 ++ w) with ((199 - 2, 2) :: (1, 1) :: repeat (1, 2) 1028 ++ (3357, 2) :: (1, 1) :: repeat (1, 2) 12064 ++ (26044, 2) :: (1, 1) :: repeat (1, 2) 109099 ++ (132761, 2) :: (1, 1) :: repeat (1, 2) 646580 ++ w) by sec_eq.
    apply (sTUP [20; 0] 147 231 199 2 ((1, 1) :: repeat (1, 2) 1028 ++ (3357, 2) :: (1, 1) :: repeat (1, 2) 12064 ++ (26044, 2) :: (1, 1) :: repeat (1, 2) 109099 ++ (132761, 2) :: (1, 1) :: repeat (1, 2) 646580 ++ w) 1); closearith.
  }
  (* step 143: hGRIND_even 113 *)
  apply (hsteps_trans _ (HB [20; 0] 146 1 230 ((2, 2) :: (197, 2) :: (1, 1) :: repeat (1, 2) 1028 ++ (3357, 2) :: (1, 1) :: repeat (1, 2) 12064 ++ (26044, 2) :: (1, 1) :: repeat (1, 2) 109099 ++ (132761, 2) :: (1, 1) :: repeat (1, 2) 646580 ++ w) 1)).
  {
    apply (hGRIND_even 113 [20; 0] 146 ((197, 2) :: (1, 1) :: repeat (1, 2) 1028 ++ (3357, 2) :: (1, 1) :: repeat (1, 2) 12064 ++ (26044, 2) :: (1, 1) :: repeat (1, 2) 109099 ++ (132761, 2) :: (1, 1) :: repeat (1, 2) 646580 ++ w) 1); closearith.
  }
  (* step 144: P TUP2_1 *)
  apply (hsteps_trans _ (HC [147; 20; 0] 230 1 2 ((195, 2) :: (1, 1) :: repeat (1, 2) 1028 ++ (3357, 2) :: (1, 1) :: repeat (1, 2) 12064 ++ (26044, 2) :: (1, 1) :: repeat (1, 2) 109099 ++ (132761, 2) :: (1, 1) :: repeat (1, 2) 646580 ++ w) 1)).
  {
    replace ((195, 2) :: (1, 1) :: repeat (1, 2) 1028 ++ (3357, 2) :: (1, 1) :: repeat (1, 2) 12064 ++ (26044, 2) :: (1, 1) :: repeat (1, 2) 109099 ++ (132761, 2) :: (1, 1) :: repeat (1, 2) 646580 ++ w) with ((197 - 2, 2) :: (1, 1) :: repeat (1, 2) 1028 ++ (3357, 2) :: (1, 1) :: repeat (1, 2) 12064 ++ (26044, 2) :: (1, 1) :: repeat (1, 2) 109099 ++ (132761, 2) :: (1, 1) :: repeat (1, 2) 646580 ++ w) by sec_eq.
    apply (sTUP2_1 [20; 0] 146 229 197 ((1, 1) :: repeat (1, 2) 1028 ++ (3357, 2) :: (1, 1) :: repeat (1, 2) 12064 ++ (26044, 2) :: (1, 1) :: repeat (1, 2) 109099 ++ (132761, 2) :: (1, 1) :: repeat (1, 2) 646580 ++ w) 1); closearith.
  }
  (* step 145: P TDN *)
  apply (hsteps_trans _ (HB [147; 20; 0] 230 1 4 ((195, 2) :: (1, 1) :: repeat (1, 2) 1028 ++ (3357, 2) :: (1, 1) :: repeat (1, 2) 12064 ++ (26044, 2) :: (1, 1) :: repeat (1, 2) 109099 ++ (132761, 2) :: (1, 1) :: repeat (1, 2) 646580 ++ w) 1)).
  {
    apply (sTDN [147; 20; 0] 230 ((195, 2) :: (1, 1) :: repeat (1, 2) 1028 ++ (3357, 2) :: (1, 1) :: repeat (1, 2) 12064 ++ (26044, 2) :: (1, 1) :: repeat (1, 2) 109099 ++ (132761, 2) :: (1, 1) :: repeat (1, 2) 646580 ++ w) 1).
  }
  (* step 146: sTUP *)
  apply (hsteps_trans _ (HC [147; 20; 0] 230 3 2 ((193, 2) :: (1, 1) :: repeat (1, 2) 1028 ++ (3357, 2) :: (1, 1) :: repeat (1, 2) 12064 ++ (26044, 2) :: (1, 1) :: repeat (1, 2) 109099 ++ (132761, 2) :: (1, 1) :: repeat (1, 2) 646580 ++ w) 1)).
  {
    replace ((193, 2) :: (1, 1) :: repeat (1, 2) 1028 ++ (3357, 2) :: (1, 1) :: repeat (1, 2) 12064 ++ (26044, 2) :: (1, 1) :: repeat (1, 2) 109099 ++ (132761, 2) :: (1, 1) :: repeat (1, 2) 646580 ++ w) with ((195 - 2, 2) :: (1, 1) :: repeat (1, 2) 1028 ++ (3357, 2) :: (1, 1) :: repeat (1, 2) 12064 ++ (26044, 2) :: (1, 1) :: repeat (1, 2) 109099 ++ (132761, 2) :: (1, 1) :: repeat (1, 2) 646580 ++ w) by sec_eq.
    apply (sTUP [147; 20; 0] 230 4 195 2 ((1, 1) :: repeat (1, 2) 1028 ++ (3357, 2) :: (1, 1) :: repeat (1, 2) 12064 ++ (26044, 2) :: (1, 1) :: repeat (1, 2) 109099 ++ (132761, 2) :: (1, 1) :: repeat (1, 2) 646580 ++ w) 1); closearith.
  }
  (* step 147: CLEANG_odd 95 *)
  apply (hsteps_trans _ (HB [147; 20; 0] 230 1 198 (repeat (1, 2) 1 ++ (1, 1) :: repeat (1, 2) 1028 ++ (3357, 2) :: (1, 1) :: repeat (1, 2) 12064 ++ (26044, 2) :: (1, 1) :: repeat (1, 2) 109099 ++ (132761, 2) :: (1, 1) :: repeat (1, 2) 646580 ++ w) 1)).
  {
    replace (repeat (1, 2) 1 ++ (1, 1) :: repeat (1, 2) 1028 ++ (3357, 2) :: (1, 1) :: repeat (1, 2) 12064 ++ (26044, 2) :: (1, 1) :: repeat (1, 2) 109099 ++ (132761, 2) :: (1, 1) :: repeat (1, 2) 646580 ++ w) with ((1, 2) :: (1, 1) :: repeat (1, 2) 1028 ++ (3357, 2) :: (1, 1) :: repeat (1, 2) 12064 ++ (26044, 2) :: (1, 1) :: repeat (1, 2) 109099 ++ (132761, 2) :: (1, 1) :: repeat (1, 2) 646580 ++ w) by sec_eq.
    apply (CLEANG_odd 95 [147; 20; 0] 230 ((1, 1) :: repeat (1, 2) 1028 ++ (3357, 2) :: (1, 1) :: repeat (1, 2) 12064 ++ (26044, 2) :: (1, 1) :: repeat (1, 2) 109099 ++ (132761, 2) :: (1, 1) :: repeat (1, 2) 646580 ++ w) 1); closearith.
  }
  (* step 148: M pop12 (1,) *)
  apply (hsteps_trans _ (HB [147; 20; 0] 231 1 200 ((1, 1) :: repeat (1, 2) 1028 ++ (3357, 2) :: (1, 1) :: repeat (1, 2) 12064 ++ (26044, 2) :: (1, 1) :: repeat (1, 2) 109099 ++ (132761, 2) :: (1, 1) :: repeat (1, 2) 646580 ++ w) 1)).
  {
    apply (pop12 1 [147; 20; 0] 230 198 ((1, 1) :: repeat (1, 2) 1028 ++ (3357, 2) :: (1, 1) :: repeat (1, 2) 12064 ++ (26044, 2) :: (1, 1) :: repeat (1, 2) 109099 ++ (132761, 2) :: (1, 1) :: repeat (1, 2) 646580 ++ w) 1); closearith.
  }
  (* step 149: P POP *)
  apply (hsteps_trans _ (HB [147; 20; 0] 232 1 201 (repeat (1, 2) 1028 ++ (3357, 2) :: (1, 1) :: repeat (1, 2) 12064 ++ (26044, 2) :: (1, 1) :: repeat (1, 2) 109099 ++ (132761, 2) :: (1, 1) :: repeat (1, 2) 646580 ++ w) 1)).
  {
    apply (sPOP1 [147; 20; 0] 231 200 (repeat (1, 2) 1028 ++ (3357, 2) :: (1, 1) :: repeat (1, 2) 12064 ++ (26044, 2) :: (1, 1) :: repeat (1, 2) 109099 ++ (132761, 2) :: (1, 1) :: repeat (1, 2) 646580 ++ w) 1); closearith.
  }
  (* step 150: M pop12 (1028,) *)
  apply (hsteps_trans _ (HB [147; 20; 0] 1260 1 2257 ((3357, 2) :: (1, 1) :: repeat (1, 2) 12064 ++ (26044, 2) :: (1, 1) :: repeat (1, 2) 109099 ++ (132761, 2) :: (1, 1) :: repeat (1, 2) 646580 ++ w) 1)).
  {
    apply (pop12 1028 [147; 20; 0] 232 201 ((3357, 2) :: (1, 1) :: repeat (1, 2) 12064 ++ (26044, 2) :: (1, 1) :: repeat (1, 2) 109099 ++ (132761, 2) :: (1, 1) :: repeat (1, 2) 646580 ++ w) 1); closearith.
  }
  (* step 151: sTUP *)
  apply (hsteps_trans _ (HC [147; 20; 0] 1260 2256 2 ((3355, 2) :: (1, 1) :: repeat (1, 2) 12064 ++ (26044, 2) :: (1, 1) :: repeat (1, 2) 109099 ++ (132761, 2) :: (1, 1) :: repeat (1, 2) 646580 ++ w) 1)).
  {
    replace ((3355, 2) :: (1, 1) :: repeat (1, 2) 12064 ++ (26044, 2) :: (1, 1) :: repeat (1, 2) 109099 ++ (132761, 2) :: (1, 1) :: repeat (1, 2) 646580 ++ w) with ((3357 - 2, 2) :: (1, 1) :: repeat (1, 2) 12064 ++ (26044, 2) :: (1, 1) :: repeat (1, 2) 109099 ++ (132761, 2) :: (1, 1) :: repeat (1, 2) 646580 ++ w) by sec_eq.
    apply (sTUP [147; 20; 0] 1260 2257 3357 2 ((1, 1) :: repeat (1, 2) 12064 ++ (26044, 2) :: (1, 1) :: repeat (1, 2) 109099 ++ (132761, 2) :: (1, 1) :: repeat (1, 2) 646580 ++ w) 1); closearith.
  }
  (* step 152: hGRIND_even 1126 *)
  apply (hsteps_trans _ (HB [147; 20; 0] 1259 1 2256 ((2, 2) :: (3355, 2) :: (1, 1) :: repeat (1, 2) 12064 ++ (26044, 2) :: (1, 1) :: repeat (1, 2) 109099 ++ (132761, 2) :: (1, 1) :: repeat (1, 2) 646580 ++ w) 1)).
  {
    apply (hGRIND_even 1126 [147; 20; 0] 1259 ((3355, 2) :: (1, 1) :: repeat (1, 2) 12064 ++ (26044, 2) :: (1, 1) :: repeat (1, 2) 109099 ++ (132761, 2) :: (1, 1) :: repeat (1, 2) 646580 ++ w) 1); closearith.
  }
  (* step 153: P TUP2_1 *)
  apply (hsteps_trans _ (HC [1260; 147; 20; 0] 2256 1 2 ((3353, 2) :: (1, 1) :: repeat (1, 2) 12064 ++ (26044, 2) :: (1, 1) :: repeat (1, 2) 109099 ++ (132761, 2) :: (1, 1) :: repeat (1, 2) 646580 ++ w) 1)).
  {
    replace ((3353, 2) :: (1, 1) :: repeat (1, 2) 12064 ++ (26044, 2) :: (1, 1) :: repeat (1, 2) 109099 ++ (132761, 2) :: (1, 1) :: repeat (1, 2) 646580 ++ w) with ((3355 - 2, 2) :: (1, 1) :: repeat (1, 2) 12064 ++ (26044, 2) :: (1, 1) :: repeat (1, 2) 109099 ++ (132761, 2) :: (1, 1) :: repeat (1, 2) 646580 ++ w) by sec_eq.
    apply (sTUP2_1 [147; 20; 0] 1259 2255 3355 ((1, 1) :: repeat (1, 2) 12064 ++ (26044, 2) :: (1, 1) :: repeat (1, 2) 109099 ++ (132761, 2) :: (1, 1) :: repeat (1, 2) 646580 ++ w) 1); closearith.
  }
  (* step 154: P TDN *)
  apply (hsteps_trans _ (HB [1260; 147; 20; 0] 2256 1 4 ((3353, 2) :: (1, 1) :: repeat (1, 2) 12064 ++ (26044, 2) :: (1, 1) :: repeat (1, 2) 109099 ++ (132761, 2) :: (1, 1) :: repeat (1, 2) 646580 ++ w) 1)).
  {
    apply (sTDN [1260; 147; 20; 0] 2256 ((3353, 2) :: (1, 1) :: repeat (1, 2) 12064 ++ (26044, 2) :: (1, 1) :: repeat (1, 2) 109099 ++ (132761, 2) :: (1, 1) :: repeat (1, 2) 646580 ++ w) 1).
  }
  (* step 155: sTUP *)
  apply (hsteps_trans _ (HC [1260; 147; 20; 0] 2256 3 2 ((3351, 2) :: (1, 1) :: repeat (1, 2) 12064 ++ (26044, 2) :: (1, 1) :: repeat (1, 2) 109099 ++ (132761, 2) :: (1, 1) :: repeat (1, 2) 646580 ++ w) 1)).
  {
    replace ((3351, 2) :: (1, 1) :: repeat (1, 2) 12064 ++ (26044, 2) :: (1, 1) :: repeat (1, 2) 109099 ++ (132761, 2) :: (1, 1) :: repeat (1, 2) 646580 ++ w) with ((3353 - 2, 2) :: (1, 1) :: repeat (1, 2) 12064 ++ (26044, 2) :: (1, 1) :: repeat (1, 2) 109099 ++ (132761, 2) :: (1, 1) :: repeat (1, 2) 646580 ++ w) by sec_eq.
    apply (sTUP [1260; 147; 20; 0] 2256 4 3353 2 ((1, 1) :: repeat (1, 2) 12064 ++ (26044, 2) :: (1, 1) :: repeat (1, 2) 109099 ++ (132761, 2) :: (1, 1) :: repeat (1, 2) 646580 ++ w) 1); closearith.
  }
  (* step 156: CLEANG_odd 1674 *)
  apply (hsteps_trans _ (HB [1260; 147; 20; 0] 2256 1 3356 (repeat (1, 2) 1 ++ (1, 1) :: repeat (1, 2) 12064 ++ (26044, 2) :: (1, 1) :: repeat (1, 2) 109099 ++ (132761, 2) :: (1, 1) :: repeat (1, 2) 646580 ++ w) 1)).
  {
    replace (repeat (1, 2) 1 ++ (1, 1) :: repeat (1, 2) 12064 ++ (26044, 2) :: (1, 1) :: repeat (1, 2) 109099 ++ (132761, 2) :: (1, 1) :: repeat (1, 2) 646580 ++ w) with ((1, 2) :: (1, 1) :: repeat (1, 2) 12064 ++ (26044, 2) :: (1, 1) :: repeat (1, 2) 109099 ++ (132761, 2) :: (1, 1) :: repeat (1, 2) 646580 ++ w) by sec_eq.
    apply (CLEANG_odd 1674 [1260; 147; 20; 0] 2256 ((1, 1) :: repeat (1, 2) 12064 ++ (26044, 2) :: (1, 1) :: repeat (1, 2) 109099 ++ (132761, 2) :: (1, 1) :: repeat (1, 2) 646580 ++ w) 1); closearith.
  }
  (* step 157: M pop12 (1,) *)
  apply (hsteps_trans _ (HB [1260; 147; 20; 0] 2257 1 3358 ((1, 1) :: repeat (1, 2) 12064 ++ (26044, 2) :: (1, 1) :: repeat (1, 2) 109099 ++ (132761, 2) :: (1, 1) :: repeat (1, 2) 646580 ++ w) 1)).
  {
    apply (pop12 1 [1260; 147; 20; 0] 2256 3356 ((1, 1) :: repeat (1, 2) 12064 ++ (26044, 2) :: (1, 1) :: repeat (1, 2) 109099 ++ (132761, 2) :: (1, 1) :: repeat (1, 2) 646580 ++ w) 1); closearith.
  }
  (* step 158: P POP *)
  apply (hsteps_trans _ (HB [1260; 147; 20; 0] 2258 1 3359 (repeat (1, 2) 12064 ++ (26044, 2) :: (1, 1) :: repeat (1, 2) 109099 ++ (132761, 2) :: (1, 1) :: repeat (1, 2) 646580 ++ w) 1)).
  {
    apply (sPOP1 [1260; 147; 20; 0] 2257 3358 (repeat (1, 2) 12064 ++ (26044, 2) :: (1, 1) :: repeat (1, 2) 109099 ++ (132761, 2) :: (1, 1) :: repeat (1, 2) 646580 ++ w) 1); closearith.
  }
  (* step 159: M pop12 (12064,) *)
  apply (hsteps_trans _ (HB [1260; 147; 20; 0] 14322 1 27487 ((26044, 2) :: (1, 1) :: repeat (1, 2) 109099 ++ (132761, 2) :: (1, 1) :: repeat (1, 2) 646580 ++ w) 1)).
  {
    apply (pop12 12064 [1260; 147; 20; 0] 2258 3359 ((26044, 2) :: (1, 1) :: repeat (1, 2) 109099 ++ (132761, 2) :: (1, 1) :: repeat (1, 2) 646580 ++ w) 1); closearith.
  }
  (* step 160: sTUP *)
  apply (hsteps_trans _ (HC [1260; 147; 20; 0] 14322 27486 2 ((26042, 2) :: (1, 1) :: repeat (1, 2) 109099 ++ (132761, 2) :: (1, 1) :: repeat (1, 2) 646580 ++ w) 1)).
  {
    replace ((26042, 2) :: (1, 1) :: repeat (1, 2) 109099 ++ (132761, 2) :: (1, 1) :: repeat (1, 2) 646580 ++ w) with ((26044 - 2, 2) :: (1, 1) :: repeat (1, 2) 109099 ++ (132761, 2) :: (1, 1) :: repeat (1, 2) 646580 ++ w) by sec_eq.
    apply (sTUP [1260; 147; 20; 0] 14322 27487 26044 2 ((1, 1) :: repeat (1, 2) 109099 ++ (132761, 2) :: (1, 1) :: repeat (1, 2) 646580 ++ w) 1); closearith.
  }
  (* step 161: hGRIND_even 13741 *)
  apply (hsteps_trans _ (HB [1260; 147; 20; 0] 14321 1 27486 ((2, 2) :: (26042, 2) :: (1, 1) :: repeat (1, 2) 109099 ++ (132761, 2) :: (1, 1) :: repeat (1, 2) 646580 ++ w) 1)).
  {
    apply (hGRIND_even 13741 [1260; 147; 20; 0] 14321 ((26042, 2) :: (1, 1) :: repeat (1, 2) 109099 ++ (132761, 2) :: (1, 1) :: repeat (1, 2) 646580 ++ w) 1); closearith.
  }
  (* step 162: P TUP2_1 *)
  apply (hsteps_trans _ (HC [14322; 1260; 147; 20; 0] 27486 1 2 ((26040, 2) :: (1, 1) :: repeat (1, 2) 109099 ++ (132761, 2) :: (1, 1) :: repeat (1, 2) 646580 ++ w) 1)).
  {
    replace ((26040, 2) :: (1, 1) :: repeat (1, 2) 109099 ++ (132761, 2) :: (1, 1) :: repeat (1, 2) 646580 ++ w) with ((26042 - 2, 2) :: (1, 1) :: repeat (1, 2) 109099 ++ (132761, 2) :: (1, 1) :: repeat (1, 2) 646580 ++ w) by sec_eq.
    apply (sTUP2_1 [1260; 147; 20; 0] 14321 27485 26042 ((1, 1) :: repeat (1, 2) 109099 ++ (132761, 2) :: (1, 1) :: repeat (1, 2) 646580 ++ w) 1); closearith.
  }
  (* step 163: P TDN *)
  apply (hsteps_trans _ (HB [14322; 1260; 147; 20; 0] 27486 1 4 ((26040, 2) :: (1, 1) :: repeat (1, 2) 109099 ++ (132761, 2) :: (1, 1) :: repeat (1, 2) 646580 ++ w) 1)).
  {
    apply (sTDN [14322; 1260; 147; 20; 0] 27486 ((26040, 2) :: (1, 1) :: repeat (1, 2) 109099 ++ (132761, 2) :: (1, 1) :: repeat (1, 2) 646580 ++ w) 1).
  }
  (* step 164: sTUP *)
  apply (hsteps_trans _ (HC [14322; 1260; 147; 20; 0] 27486 3 2 ((26038, 2) :: (1, 1) :: repeat (1, 2) 109099 ++ (132761, 2) :: (1, 1) :: repeat (1, 2) 646580 ++ w) 1)).
  {
    replace ((26038, 2) :: (1, 1) :: repeat (1, 2) 109099 ++ (132761, 2) :: (1, 1) :: repeat (1, 2) 646580 ++ w) with ((26040 - 2, 2) :: (1, 1) :: repeat (1, 2) 109099 ++ (132761, 2) :: (1, 1) :: repeat (1, 2) 646580 ++ w) by sec_eq.
    apply (sTUP [14322; 1260; 147; 20; 0] 27486 4 26040 2 ((1, 1) :: repeat (1, 2) 109099 ++ (132761, 2) :: (1, 1) :: repeat (1, 2) 646580 ++ w) 1); closearith.
  }
  (* step 165: CLEANG_even 13018 *)
  apply (hsteps_trans _ (HB [14322; 1260; 147; 20; 0] 27486 1 26042 ((2, 2) :: (1, 1) :: repeat (1, 2) 109099 ++ (132761, 2) :: (1, 1) :: repeat (1, 2) 646580 ++ w) 1)).
  {
    apply (CLEANG_even 13018 [14322; 1260; 147; 20; 0] 27486 ((1, 1) :: repeat (1, 2) 109099 ++ (132761, 2) :: (1, 1) :: repeat (1, 2) 646580 ++ w) 1); closearith.
  }
  (* step 166: P TRANS2_1 *)
  apply (hsteps_trans _ (HB [27487; 14322; 1260; 147; 20; 0] 26043 1 3 (repeat (1, 2) 109099 ++ (132761, 2) :: (1, 1) :: repeat (1, 2) 646580 ++ w) 1)).
  {
    apply (sTRANS2_1 [14322; 1260; 147; 20; 0] 27486 26041 1 (repeat (1, 2) 109099 ++ (132761, 2) :: (1, 1) :: repeat (1, 2) 646580 ++ w) 1); closearith.
  }
  (* step 167: M pop12 (109099,) *)
  apply (hsteps_trans _ (HB [27487; 14322; 1260; 147; 20; 0] 135142 1 218201 ((132761, 2) :: (1, 1) :: repeat (1, 2) 646580 ++ w) 1)).
  {
    apply (pop12 109099 [27487; 14322; 1260; 147; 20; 0] 26043 3 ((132761, 2) :: (1, 1) :: repeat (1, 2) 646580 ++ w) 1); closearith.
  }
  (* step 168: sTUP *)
  apply (hsteps_trans _ (HC [27487; 14322; 1260; 147; 20; 0] 135142 218200 2 ((132759, 2) :: (1, 1) :: repeat (1, 2) 646580 ++ w) 1)).
  {
    replace ((132759, 2) :: (1, 1) :: repeat (1, 2) 646580 ++ w) with ((132761 - 2, 2) :: (1, 1) :: repeat (1, 2) 646580 ++ w) by sec_eq.
    apply (sTUP [27487; 14322; 1260; 147; 20; 0] 135142 218201 132761 2 ((1, 1) :: repeat (1, 2) 646580 ++ w) 1); closearith.
  }
  (* step 169: hGRIND_even 109098 *)
  apply (hsteps_trans _ (HB [27487; 14322; 1260; 147; 20; 0] 135141 1 218200 ((2, 2) :: (132759, 2) :: (1, 1) :: repeat (1, 2) 646580 ++ w) 1)).
  {
    rewrite NUM54X2.
    apply (hGRIND_even 109098 [27487; 14322; 1260; 147; 20; 0] 135141 ((132759, 2) :: (1, 1) :: repeat (1, 2) 646580 ++ w) 1); closearith.
  }
  (* step 170: P TUP2_1 *)
  apply (hsteps_trans _ (HC [135142; 27487; 14322; 1260; 147; 20; 0] 218200 1 2 ((132757, 2) :: (1, 1) :: repeat (1, 2) 646580 ++ w) 1)).
  {
    replace ((132757, 2) :: (1, 1) :: repeat (1, 2) 646580 ++ w) with ((132759 - 2, 2) :: (1, 1) :: repeat (1, 2) 646580 ++ w) by sec_eq.
    apply (sTUP2_1 [27487; 14322; 1260; 147; 20; 0] 135141 218199 132759 ((1, 1) :: repeat (1, 2) 646580 ++ w) 1); closearith.
  }
  (* step 171: P TDN *)
  apply (hsteps_trans _ (HB [135142; 27487; 14322; 1260; 147; 20; 0] 218200 1 4 ((132757, 2) :: (1, 1) :: repeat (1, 2) 646580 ++ w) 1)).
  {
    apply (sTDN [135142; 27487; 14322; 1260; 147; 20; 0] 218200 ((132757, 2) :: (1, 1) :: repeat (1, 2) 646580 ++ w) 1).
  }
  (* step 172: sTUP *)
  apply (hsteps_trans _ (HC [135142; 27487; 14322; 1260; 147; 20; 0] 218200 3 2 ((132755, 2) :: (1, 1) :: repeat (1, 2) 646580 ++ w) 1)).
  {
    replace ((132755, 2) :: (1, 1) :: repeat (1, 2) 646580 ++ w) with ((132757 - 2, 2) :: (1, 1) :: repeat (1, 2) 646580 ++ w) by sec_eq.
    apply (sTUP [135142; 27487; 14322; 1260; 147; 20; 0] 218200 4 132757 2 ((1, 1) :: repeat (1, 2) 646580 ++ w) 1); closearith.
  }
  (* step 173: CLEANG_odd 66376 *)
  apply (hsteps_trans _ (HB [135142; 27487; 14322; 1260; 147; 20; 0] 218200 1 132760 (repeat (1, 2) 1 ++ (1, 1) :: repeat (1, 2) 646580 ++ w) 1)).
  {
    rewrite NUM54X3.
    rewrite NUM54X4.
    replace (repeat (1, 2) 1 ++ (1, 1) :: repeat (1, 2) 646580 ++ w) with ((1, 2) :: (1, 1) :: repeat (1, 2) 646580 ++ w) by sec_eq.
    apply (CLEANG_odd 66376 [135142; 27487; 14322; 1260; 147; 20; 0] 218200 ((1, 1) :: repeat (1, 2) 646580 ++ w) 1); closearith.
  }
  (* step 174: M pop12 (1,) *)
  apply (hsteps_trans _ (HB [135142; 27487; 14322; 1260; 147; 20; 0] 218201 1 132762 ((1, 1) :: repeat (1, 2) 646580 ++ w) 1)).
  {
    apply (pop12 1 [135142; 27487; 14322; 1260; 147; 20; 0] 218200 132760 ((1, 1) :: repeat (1, 2) 646580 ++ w) 1); closearith.
  }
  (* step 175: P POP *)
  apply (sPOP1 [135142; 27487; 14322; 1260; 147; 20; 0] 218201 132762 (repeat (1, 2) 646580 ++ w) 1); closearith.
Qed.

(* CASCADE54e: steps 176-176 of the CASCADE54 chain. *)
Lemma CASCADE54e : forall w,
  hsteps (HB [135142; 27487; 14322; 1260; 147; 20; 0] 218202 1 132763 (repeat (1, 2) 646580 ++ w) 1)
         (HB [135142; 27487; 14322; 1260; 147; 20; 0] 864782 1 1425923 (w) 1).
Proof.
  intro w.
  replace 864782 with (218202 + 646580)
    by (apply Nat.eqb_eq; vm_compute; reflexivity).
  replace 1425923 with (132763 + 2 * 646580)
    by (apply Nat.eqb_eq; vm_compute; reflexivity).
  (* step 176: M pop12 (646580,) *)
  apply (pop12 646580 [135142; 27487; 14322; 1260; 147; 20; 0] 218202 132763 (w) 1); closearith.
Qed.

Lemma CASCADE54 : forall w,
  hsteps (HC [350961; 109099; 62236; 6030; 630; 191; 113; 33; 19; 0] 0 3 2 (repeat (1, 2) 646578 ++ w) 1)
         (HB [135142; 27487; 14322; 1260; 147; 20; 0] 864782 1 1425923 (w) 1).
Proof.
  intro w.
  apply (hsteps_trans _ (HC [48; 5] 72 3 2 ((39, 2) :: (1, 1) :: repeat (1, 2) 191 ++ (246, 2) :: (1, 1) :: repeat (1, 2) 6030 ++ (50174, 2) :: (1, 1) :: repeat (1, 2) 109099 ++ (132761, 2) :: (1, 1) :: repeat (1, 2) 646580 ++ w) 1)).
  { apply (CASCADE54a w). }
  apply (hsteps_trans _ (HC [531; 53; 0] 1026 1 2 ((5411, 2) :: (1, 1) :: repeat (1, 2) 12064 ++ (26044, 2) :: (1, 1) :: repeat (1, 2) 109099 ++ (132761, 2) :: (1, 1) :: repeat (1, 2) 646580 ++ w) 1)).
  { apply (CASCADE54b w). }
  apply (hsteps_trans _ (HC [0] 20 34 2 ((5, 2) :: (1, 1) :: repeat (1, 2) 111 ++ (199, 2) :: (1, 1) :: repeat (1, 2) 1028 ++ (3357, 2) :: (1, 1) :: repeat (1, 2) 12064 ++ (26044, 2) :: (1, 1) :: repeat (1, 2) 109099 ++ (132761, 2) :: (1, 1) :: repeat (1, 2) 646580 ++ w) 1)).
  { apply (CASCADE54c w). }
  apply (hsteps_trans _ (HB [135142; 27487; 14322; 1260; 147; 20; 0] 218202 1 132763 (repeat (1, 2) 646580 ++ w) 1)).
  { apply (CASCADE54d w). }
  apply (CASCADE54e w).
Qed.

(* ----------------------------------------------------------------- *)
(* TOP54_TO_TOP8: TOP7's front (TUP + hGRIND_even 323287 +         *)
(* TUP2_1 + TDN + TUP) reaches GRIND8, DIPGRIND (646578,            *)
(* 2 * (j - 646581)) lands on the DIP8 spine, and CASCADE54        *)
(* regrows the stack onto TOP8.  Numeral hygiene (Phase 52          *)
(* lesson, applied proactively at this phase's doubled scale):     *)
(* the 646581/646582 atoms are normalised onto the single atom      *)
(* 646578 by eqb/vm-proved rewrites, not `change` (the              *)
(* S/subtraction conversions at depth ~646582 overflow the          *)
(* conversion stack, cf. the TAIL2_END6_of52 fix-up in              *)
(* Grind20.v); the hGRIND_even step rewrites the goal by the        *)
(* standalone identities NUM54a / NUM54b (646578 = 2 * 323287 + 4,  *)
(* 350961 = S 350960).                                              *)
(* ----------------------------------------------------------------- *)

Lemma TOP54_TO_TOP8 : forall j beta, 646582 <= j -> 2 <= beta ->
  hsteps (HB [109099; 62236; 6030; 630; 191; 113; 33; 19; 0] 350961 1 646579
            ((2 * j, 2) :: (1, 1) :: repeat (1, 2) (beta - 1)) 1)
         (HB [135142; 27487; 14322; 1260; 147; 20; 0] 864782 1 1425923
            ((2 * (j - 646581), 2) :: (1, 1)
             :: repeat (1, 2) (beta - 1)) 1).
Proof.
  intros j beta Hj Hb.
  assert (Hj4 : 4 <= j).
  { apply Nat.le_trans with 646582; [closearith | exact Hj]. }
  assert (Hr : 1 <= j - 646581).
  { assert (E : 646581 = 646582 - 1)
      by (apply Nat.eqb_eq; vm_compute; reflexivity).
    rewrite E. lia. }
  assert (Heq : 2 * j - 6 = 2 * 646578 + 2 * (j - 646581)).
  { assert (E1 : 646581 = 646578 + 3)
      by (apply Nat.eqb_eq; vm_compute; reflexivity).
    assert (E2 : 646582 = 646578 + 4)
      by (apply Nat.eqb_eq; vm_compute; reflexivity).
    rewrite E1. rewrite E2 in Hj. lia. }
  apply (hsteps_trans _ (HC [109099; 62236; 6030; 630; 191; 113; 33; 19; 0] 350961
    646578 2 ((2 * j - 2, 2) :: (1, 1) :: repeat (1, 2) (beta - 1)) 1)).
  { apply (sTUP [109099; 62236; 6030; 630; 191; 113; 33; 19; 0] 350961 646579 (2 * j) 2
           ((1, 1) :: repeat (1, 2) (beta - 1)) 1); closearith. }
  apply (hsteps_trans _ (HB [109099; 62236; 6030; 630; 191; 113; 33; 19; 0] 350960
    1 646578 ((2, 2) :: (2 * j - 2, 2) :: (1, 1)
            :: repeat (1, 2) (beta - 1)) 1)).
  { rewrite NUM54a. rewrite NUM54b.
    apply (hGRIND_even 323287 [109099; 62236; 6030; 630; 191; 113; 33; 19; 0]
           350960 ((2 * j - 2, 2) :: (1, 1) :: repeat (1, 2) (beta - 1))
           1); closearith. }
  apply (hsteps_trans _ (HC [350961; 109099; 62236; 6030; 630; 191; 113; 33; 19; 0] 646578 1 2 ((2 * j - 4, 2) :: (1, 1)
            :: repeat (1, 2) (beta - 1)) 1)).
  { replace ((2 * j - 4, 2) :: (1, 1) :: repeat (1, 2) (beta - 1))
      with ((2 * j - 2 - 2, 2) :: (1, 1) :: repeat (1, 2) (beta - 1))
      by sec_eq.
    apply (sTUP2_1 [109099; 62236; 6030; 630; 191; 113; 33; 19; 0] 350960
           646577 (2 * j - 2) ((1, 1) :: repeat (1, 2) (beta - 1)) 1); lia. }
  apply (hsteps_trans _ (HB [350961; 109099; 62236; 6030; 630; 191; 113; 33; 19; 0] 646578 1 4 ((2 * j - 4, 2) :: (1, 1)
            :: repeat (1, 2) (beta - 1)) 1)).
  { apply (sTDN [350961; 109099; 62236; 6030; 630; 191; 113; 33; 19; 0] 646578
           ((2 * j - 4, 2) :: (1, 1) :: repeat (1, 2) (beta - 1))
           1). }
  apply (hsteps_trans _ (HC [350961; 109099; 62236; 6030; 630; 191; 113; 33; 19; 0] 646578 3 2 ((2 * j - 6, 2) :: (1, 1)
            :: repeat (1, 2) (beta - 1)) 1)).
  { replace ((2 * j - 6, 2) :: (1, 1) :: repeat (1, 2) (beta - 1))
      with ((2 * j - 4 - 2, 2) :: (1, 1) :: repeat (1, 2) (beta - 1))
      by sec_eq.
    apply (sTUP [350961; 109099; 62236; 6030; 630; 191; 113; 33; 19; 0] 646578 4
           (2 * j - 4) 2 ((1, 1) :: repeat (1, 2) (beta - 1)) 1);
      lia. }
  apply (hsteps_trans _ (HC [350961; 109099; 62236; 6030; 630; 191; 113; 33; 19; 0]
    0 3 2 (repeat (1, 2) 646578
     ++ ((2 * (j - 646581), 2) :: (1, 1)
         :: repeat (1, 2) (beta - 1))) 1)).
  { rewrite Heq.
    apply (DIPGRIND 646578 (2 * (j - 646581))
           [350961; 109099; 62236; 6030; 630; 191; 113; 33; 19; 0]
           ((1, 1) :: repeat (1, 2) (beta - 1)) 1);
      [closearith | lia]. }
  apply (CASCADE54 ((2 * (j - 646581), 2) :: (1, 1)
                    :: repeat (1, 2) (beta - 1))).
Qed.

(* ----------------------------------------------------------------- *)
(* The TOP8 closings: r8 = 2, 4, 6 and band 8 (8 <= r8 <= 2851850). *)
(* ----------------------------------------------------------------- *)

Lemma TOP54_2 : forall beta, 2 <= beta ->
  hsteps (HB [135142; 27487; 14322; 1260; 147; 20; 0] 864782 1 1425923
            ((2, 2) :: (1, 1) :: repeat (1, 2) (beta - 1)) 1)
         (HB [864783; 135142; 27487; 14322; 1260; 147; 20; 0]
            (1425924 + (beta - 1)) 1 (2 * beta + 1) [] 1).
Proof.
  intros beta Hb.
  apply (hsteps_trans _ (HB [864783; 135142; 27487; 14322; 1260; 147; 20; 0] 1425924 1 3 (repeat (1, 2) (beta - 1)) 1)).
  { rewrite NUM54e. rewrite NUM54f. rewrite NUM54g.
    apply (sTRANS2_1 [135142; 27487; 14322; 1260; 147; 20; 0] 864782
           1425922 1 (repeat (1, 2) (beta - 1)) 1); lia. }
  apply (CASCADE_POPFIN [864783; 135142; 27487; 14322; 1260; 147; 20; 0] 1425924 beta); lia.
Qed.

(* NOTE (Phase 54, proactive): in TOP54_4, TOP54_6 and TOP54_BAND  *)
(* the hGRIND_even 712959 step is preceded by two goal rewrites     *)
(* via the standalone identities NUM54c (1425922 = 2 * 712959 + 4)   *)
(* and NUM54d (864782 = S 864781) -- the Phase 52 fix-up pattern     *)
(* for TOP53_4/6/BAND's hGRIND_even 323287 step, applied from the   *)
(* start at this phase's doubled scale, with the identities         *)
(* factored into lemmas because the inline `replace ... by          *)
(* (eqb/vm ...)` form stack-overflows in this file's long           *)
(* hsteps_trans chains (see the NUM54 note in the header).  The     *)
(* step applies themselves are unchanged.                           *)

Lemma TOP54_4 : forall beta, 2 <= beta ->
  hsteps (HB [135142; 27487; 14322; 1260; 147; 20; 0] 864782 1 1425923
            ((4, 2) :: (1, 1) :: repeat (1, 2) (beta - 1)) 1)
         (HB [1425923; 864782; 135142; 27487; 14322; 1260; 147; 20; 0]
            (beta + 2) 1 (2 * beta + 1) [] 1).
Proof.
  intros beta Hb.
  apply (hsteps_trans _ (HC [135142; 27487; 14322; 1260; 147; 20; 0]
    864782 1425922 2
    ((2, 2) :: (1, 1) :: repeat (1, 2) (beta - 1)) 1)).
  { rewrite NUM54h.
    apply (sTUP [135142; 27487; 14322; 1260; 147; 20; 0] 864782 1425923
           4 2 ((1, 1) :: repeat (1, 2) (beta - 1)) 1); closearith. }
  apply (hsteps_trans _ (HB [135142; 27487; 14322; 1260; 147; 20; 0]
    864781 1 1425922 ((2, 2) :: (2, 2) :: (1, 1)
            :: repeat (1, 2) (beta - 1)) 1)).
  { rewrite NUM54c. rewrite NUM54d.
    apply (hGRIND_even 712959 [135142; 27487; 14322; 1260; 147; 20; 0]
           864781 ((2, 2) :: (1, 1) :: repeat (1, 2) (beta - 1)) 1);
      closearith. }
  apply (hsteps_trans _ (HB [1425923; 864782; 135142; 27487; 14322; 1260; 147; 20; 0] 3 1 3 (repeat (1, 2) (beta - 1)) 1)).
  { rewrite NUM54k. rewrite NUM54m. rewrite NUM54d.
    apply (hsteps_step _ (HB [1425923; 864782; 135142; 27487; 14322; 1260; 147; 20; 0] 3 1 3 (repeat (1, 2) (beta - 1)) 1));
      [apply hTRANS2_2; closearith | apply hsteps_refl]. }
  replace (beta + 2) with (3 + (beta - 1)) by lia.
  apply (CASCADE_POPFIN [1425923; 864782; 135142; 27487; 14322; 1260; 147; 20; 0] 3 beta); lia.
Qed.

Lemma TOP54_6 : forall beta, 2 <= beta ->
  hsteps (HB [135142; 27487; 14322; 1260; 147; 20; 0] 864782 1 1425923
            ((6, 2) :: (1, 1) :: repeat (1, 2) (beta - 1)) 1)
         (HB [1425923; 864782; 135142; 27487; 14322; 1260; 147; 20; 0]
            (beta + 4) 1 (2 * beta + 1) [] 1).
Proof.
  intros beta Hb.
  apply (hsteps_trans _ (HC [135142; 27487; 14322; 1260; 147; 20; 0]
    864782 1425922 2
    ((4, 2) :: (1, 1) :: repeat (1, 2) (beta - 1)) 1)).
  { rewrite NUM54h.
    apply (sTUP [135142; 27487; 14322; 1260; 147; 20; 0] 864782 1425923
           6 2 ((1, 1) :: repeat (1, 2) (beta - 1)) 1); closearith. }
  apply (hsteps_trans _ (HB [135142; 27487; 14322; 1260; 147; 20; 0]
    864781 1 1425922 ((2, 2) :: (4, 2) :: (1, 1)
            :: repeat (1, 2) (beta - 1)) 1)).
  { rewrite NUM54c. rewrite NUM54d.
    apply (hGRIND_even 712959 [135142; 27487; 14322; 1260; 147; 20; 0]
           864781 ((4, 2) :: (1, 1) :: repeat (1, 2) (beta - 1)) 1);
      closearith. }
  apply (hsteps_trans _ (HC [864782; 135142; 27487; 14322; 1260; 147; 20; 0] 1425922 1 2
    ((2, 2) :: (1, 1) :: repeat (1, 2) (beta - 1)) 1)).
  { rewrite NUM54k. rewrite NUM54d.
    replace ((2, 2) :: (1, 1) :: repeat (1, 2) (beta - 1))
      with ((4 - 2, 2) :: (1, 1) :: repeat (1, 2) (beta - 1))
      by sec_eq.
    apply (sTUP2_1 [135142; 27487; 14322; 1260; 147; 20; 0] 864781
           1425921 4 ((1, 1) :: repeat (1, 2) (beta - 1)) 1); lia. }
  apply (hsteps_trans _ (HB [864782; 135142; 27487; 14322; 1260; 147; 20; 0] 1425922 1 4
    ((2, 2) :: (1, 1) :: repeat (1, 2) (beta - 1)) 1)).
  { apply (sTDN [864782; 135142; 27487; 14322; 1260; 147; 20; 0] 1425922
           ((2, 2) :: (1, 1) :: repeat (1, 2) (beta - 1)) 1). }
  apply (hsteps_trans _ (HB [1425923; 864782; 135142; 27487; 14322; 1260; 147; 20; 0] 5 1 3 (repeat (1, 2) (beta - 1)) 1)).
  { rewrite NUM54e.
    apply (sTRANS2_1 [864782; 135142; 27487; 14322; 1260; 147; 20; 0]
           1425922 3 1 (repeat (1, 2) (beta - 1)) 1); lia. }
  replace (beta + 4) with (5 + (beta - 1)) by lia.
  apply (CASCADE_POPFIN [1425923; 864782; 135142; 27487; 14322; 1260; 147; 20; 0] 5 beta); lia.
Qed.

Lemma TOP54_BAND : forall j beta, 4 <= j -> j <= 1425925 -> 2 <= beta ->
  hsteps (HB [135142; 27487; 14322; 1260; 147; 20; 0] 864782 1 1425923
            ((2 * j, 2) :: (1, 1) :: repeat (1, 2) (beta - 1)) 1)
         (HB [1425923; 864782; 135142; 27487; 14322; 1260; 147; 20; 0]
            (2 * j + beta - 2) 1 (2 * beta + 1) [] 1).
Proof.
  intros j beta Hj1 Hj2 Hb.
  apply (hsteps_trans _ (HC [135142; 27487; 14322; 1260; 147; 20; 0]
    864782 1425922 2 ((2 * j - 2, 2) :: (1, 1)
            :: repeat (1, 2) (beta - 1)) 1)).
  { rewrite NUM54h.
    apply (sTUP [135142; 27487; 14322; 1260; 147; 20; 0] 864782 1425923
           (2 * j) 2 ((1, 1) :: repeat (1, 2) (beta - 1)) 1);
      closearith. }
  apply (hsteps_trans _ (HB [135142; 27487; 14322; 1260; 147; 20; 0]
    864781 1 1425922 ((2, 2) :: (2 * j - 2, 2) :: (1, 1)
            :: repeat (1, 2) (beta - 1)) 1)).
  { rewrite NUM54c. rewrite NUM54d.
    apply (hGRIND_even 712959 [135142; 27487; 14322; 1260; 147; 20; 0]
           864781 ((2 * j - 2, 2) :: (1, 1)
           :: repeat (1, 2) (beta - 1)) 1); closearith. }
  apply (hsteps_trans _ (HC [864782; 135142; 27487; 14322; 1260; 147; 20; 0] 1425922 1 2 ((2 * j - 4, 2) :: (1, 1)
            :: repeat (1, 2) (beta - 1)) 1)).
  { rewrite NUM54k. rewrite NUM54d.
    replace ((2 * j - 4, 2) :: (1, 1) :: repeat (1, 2) (beta - 1))
      with ((2 * j - 2 - 2, 2) :: (1, 1)
            :: repeat (1, 2) (beta - 1)) by sec_eq.
    apply (sTUP2_1 [135142; 27487; 14322; 1260; 147; 20; 0] 864781
           1425921 (2 * j - 2) ((1, 1) :: repeat (1, 2) (beta - 1))
           1); lia. }
  apply (hsteps_trans _ (HB [864782; 135142; 27487; 14322; 1260; 147; 20; 0] 1425922 1 4 ((2 * j - 4, 2) :: (1, 1)
            :: repeat (1, 2) (beta - 1)) 1)).
  { apply (sTDN [864782; 135142; 27487; 14322; 1260; 147; 20; 0] 1425922
           ((2 * j - 4, 2) :: (1, 1) :: repeat (1, 2) (beta - 1))
           1). }
  apply (hsteps_trans _ (HC [864782; 135142; 27487; 14322; 1260; 147; 20; 0] 1425922 3 2 ((2 * j - 6, 2) :: (1, 1)
            :: repeat (1, 2) (beta - 1)) 1)).
  { replace ((2 * j - 6, 2) :: (1, 1) :: repeat (1, 2) (beta - 1))
      with ((2 * j - 4 - 2, 2) :: (1, 1)
            :: repeat (1, 2) (beta - 1)) by sec_eq.
    apply (sTUP [864782; 135142; 27487; 14322; 1260; 147; 20; 0] 1425922
           4 (2 * j - 4) 2 ((1, 1) :: repeat (1, 2) (beta - 1)) 1);
      lia. }
  apply (hsteps_trans _ (HB [864782; 135142; 27487; 14322; 1260; 147; 20; 0] 1425922 1 (2 * j - 2)
    ((2, 2) :: (1, 1) :: repeat (1, 2) (beta - 1)) 1)).
  { replace (2 * j - 6) with (2 * (j - 4) + 2) by lia.
    replace (2 * j - 2) with (2 * (j - 4) + 6) by lia.
    apply (CLEANG_even (j - 4) [864782; 135142; 27487; 14322; 1260; 147; 20; 0] 1425922 ((1, 1) :: repeat (1, 2) (beta - 1))
           1).
    (* the floor (j - 4) + 1 <= 1425922: route via j <= 1425925 *)
    apply Nat.le_trans with (j - 3).
    - lia.
    - rewrite NUM54r.
      apply Nat.sub_le_mono_r. exact Hj2. }
  apply (hsteps_trans _ (HB [1425923; 864782; 135142; 27487; 14322; 1260; 147; 20; 0] (2 * j - 1) 1 3 (repeat (1, 2) (beta - 1)) 1)).
  { replace (2 * j - 2) with (S (2 * j - 3)) by lia.
    replace (2 * j - 1) with (S (S (2 * j - 3))) by lia.
    rewrite NUM54e.
    apply (sTRANS2_1 [864782; 135142; 27487; 14322; 1260; 147; 20; 0]
           1425922 (2 * j - 3) 1 (repeat (1, 2) (beta - 1)) 1); lia. }
  replace (2 * j + beta - 2) with (2 * j - 1 + (beta - 1)) by lia.
  apply (CASCADE_POPFIN [1425923; 864782; 135142; 27487; 14322; 1260; 147; 20; 0] (2 * j - 1) beta); lia.
Qed.

(* ----------------------------------------------------------------- *)
(* TAIL2_END9: the strictly smaller residual core -- the totality   *)
(* of the TOP8 state for r8 = 2 * j, j >= 1425926 (r8 >= 2851852),   *)
(* where the GRIND9 pair (r8 - 6, 2) at counter 1425922 takes the    *)
(* DIPDESC boundary a ninth time.  A Definition (lemma              *)
(* parameter), never an axiom.                                      *)
(* ----------------------------------------------------------------- *)

Definition TAIL2_END9 : Prop :=
  forall j beta, 1425926 <= j -> 2 <= beta ->
  exists pb A, beta <= A /\
    hsteps (HB [135142; 27487; 14322; 1260; 147; 20; 0] 864782 1 1425923
              ((2 * j, 2) :: (1, 1) :: repeat (1, 2) (beta - 1)) 1)
           (HB pb A 1 (2 * beta + 1) [] 1).

(* ----------------------------------------------------------------- *)
(* TAIL2_END8_of54: TAIL2_END8, modulo TAIL2_END9.  The j-range     *)
(* splits at r8 = 2 * (j - 646581): the three small cases and       *)
(* band 8 are proved above; j - 646581 >= 1425926 is the core.       *)
(* (Numeral hygiene: the `change N with (S (N-1))` steps of the     *)
(* Phase 52 analogue at N = 323290 / 323288 are here at             *)
(* N = 1425926 / 1425924 / 646582 -- all replaced by eqb/vm-proved    *)
(* equality rewrites, since the S-conversions at these depths       *)
(* overflow the conversion stack.)                                  *)
(* ----------------------------------------------------------------- *)

Lemma TAIL2_END8_of54 : TAIL2_END9 -> TAIL2_END8.
Proof.
  intros H9 j beta Hj Hb.
  pose proof (TOP54_TO_TOP8 j beta Hj Hb) as Htop.
  destruct (le_lt_dec 1425926 (j - 646581)) as [Hbig | Hsmall].
  - (* j7 = j - 646581 >= 1425926: the core *)
    destruct (H9 (j - 646581) beta Hbig Hb)
      as [pb [A [Ha Hsteps]]].
    exists pb, A. split; [exact Ha |].
    exact (hsteps_trans _ _ _ Htop Hsteps).
  - destruct (le_lt_dec 4 (j - 646581)) as [Hband | Htiny].
    + (* band 7: j7 = j - 646581, 4 <= j7 <= 1425925 *)
      exists [1425923; 864782; 135142; 27487; 14322; 1260; 147; 20; 0],
        (2 * (j - 646581) + beta - 2).
      split; [lia |].
      assert (Hj2 : j - 646581 <= 1425925).
      { rewrite NUM54q in Hsmall.
        apply (proj1 (Nat.lt_succ_r _ _) Hsmall). }
      exact (hsteps_trans _ _ _ Htop
               (TOP54_BAND (j - 646581) beta Hband Hj2 Hb)).
    + (* tiny: j7 = j - 646581 <= 3; j7 >= 1 since 646582 <= j *)
      destruct (Nat.eq_dec (j - 646581) 1) as [He | Hne].
      * (* r7 = 2 *)
        rewrite He in Htop.
        exists [864783; 135142; 27487; 14322; 1260; 147; 20; 0],
          (1425924 + (beta - 1)).
        split; [rewrite NUM54n; lia |].
        exact (hsteps_trans _ _ _ Htop (TOP54_2 beta Hb)).
      * destruct (Nat.eq_dec (j - 646581) 2) as [He | Hne'].
        -- (* r7 = 4 *)
           rewrite He in Htop.
           exists [1425923; 864782; 135142; 27487; 14322; 1260; 147; 20; 0], (beta + 2).
           split; [lia |].
           exact (hsteps_trans _ _ _ Htop (TOP54_4 beta Hb)).
        -- destruct (Nat.eq_dec (j - 646581) 3) as [He | Hne''].
           ++ (* r7 = 6 *)
              rewrite He in Htop.
              exists [1425923; 864782; 135142; 27487; 14322; 1260; 147; 20; 0], (beta + 4).
              split; [lia |].
              exact (hsteps_trans _ _ _ Htop (TOP54_6 beta Hb)).
           ++ (* j7 = 0, contradicting 646582 <= j *)
              exfalso.
              assert (H0 : j - 646581 = 0) by lia.
              rewrite NUM54p in Hj.
              lia.
Qed.

(* ----------------------------------------------------------------- *)
(* ESC_ERA_LAW_54: the phase-8 ESC era law at every even            *)
(* R >= 1278 (M >= 616), modulo TAIL2_END9 alone.                   *)
(* ----------------------------------------------------------------- *)

Lemma ESC_ERA_LAW_54 : TAIL2_END9 ->
  forall M beta, 616 <= M -> 2 <= beta ->
  exists n c pb a,
    run n (esc_src (2 * M + 52) (beta - 2)) = Some c
    /\ cfg_sim c (rcsec (false :: repeat true (S a) ++ enc pb)
                        (2 * beta + 2) [(1, 2)])
    /\ beta <= a.
Proof.
  intros H M beta HM Hb.
  apply (ESC_ERA_LAW_53 (TAIL2_END8_of54 H) M beta HM Hb).
Qed.

(* ----------------------------------------------------------------- *)
(* Assumption audit                                                  *)
(* ----------------------------------------------------------------- *)

Print Assumptions CASCADE54.
Print Assumptions TOP54_TO_TOP8.
Print Assumptions TOP54_2.
Print Assumptions TOP54_4.
Print Assumptions TOP54_6.
Print Assumptions TOP54_BAND.
Print Assumptions TAIL2_END8_of54.
Print Assumptions ESC_ERA_LAW_54.
