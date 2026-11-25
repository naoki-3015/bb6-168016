(* ================================================================= *)
(*  Grind21.v -- Phase 53: the seventh re-descent cascade of the    *)
(*  TOP6 state, mechanised as a fixed parse, closing TAIL2_END7     *)
(*  for the whole first j-band 323290 <= j <= 969870 (TOP6          *)
(*  parameters) and reducing the rest to a strictly smaller core    *)
(*  at the TOP7 state.                                              *)
(*                                                                  *)
(*  Phase 52 left the ESC side of H_LOOP resting on TAIL2_END7      *)
(*  (Grind20.v): the totality of the TOP6 state                     *)
(*                                                                  *)
(*    TOP6(j, beta) = HB [23252; 3931; 2847; 569; 287; 14; 5]       *)
(*                    175058 1 323287 ((2j, 2) :: (1, 1)            *)
(*                    :: (1, 2)^(beta-1))                            *)
(*                                                                  *)
(*  for j >= 323290.  There the GRIND7 pair (2j - 6, 2) at counter  *)
(*  323286 exceeds the CLEANG_even floor and takes the DIPDESC      *)
(*  boundary a seventh time.  Phase 53 traces the walk              *)
(*  (rocq/hsim53.py, ALL PASS: the 344-waypoint chain below         *)
(*  asserted verbatim at (j, beta) in {(323290, 2), (323290, 3),    *)
(*  (323291, 2), (400000, 2), (969870, 2)}; TOP7 finals and the     *)
(*  cycle-8 fence asserted too; a junk-tail probe confirms          *)
(*  CASCADE53 is stated for an arbitrary tail; the full             *)
(*  (323290, 2) walk was also replayed step by step through the     *)
(*  walker's own macro/prim functions and classified into 345       *)
(*  lemma applications with 0 unclassified runs -- the classifier   *)
(*  itself was first validated by exact reproduction of the         *)
(*  Phase 52 classified chain (229 steps, 0 mismatches) -- and      *)
(*  the CASCADE53 proof script below is generated from that         *)
(*  classification).                                                *)
(*                                                                  *)
(*  FINDING: the seventh descent is again a FIXED parse, uniform    *)
(*  in (j, beta) -- not a return to TOP6, TOP5, ..., or TOP.        *)
(*  Writing r7 = 2j - 646578 >= 2 for the DIPGRIND residue at       *)
(*  GRIND7:                                                         *)
(*                                                                  *)
(*    TOP6 --front (TUP, hGRIND_even 161641, TUP2_1, TDN, TUP)-->   *)
(*      GRIND7 = HC [175058; 23252; 3931; 2847; 569; 287;           *)
(*                 14; 5] 323286 3 2 ((2j - 6, 2) :: tail)          *)
(*    --DIPGRIND (323286, r7)-->                                    *)
(*      HC [175058; 23252; ...] 0 3 2 ((1, 2)^323286 ++ W),         *)
(*        W = ((r7, 2) :: (1, 1) :: (1, 2)^(beta - 1))              *)
(*    --CASCADE53 (fixed parse, arbitrary tail)-->                  *)
(*      TOP7 = HB [109099; 62236; 6030; 630; 191; 113; 33;          *)
(*             19; 0] 350961 1 646579 W.                            *)
(*                                                                  *)
(*  CASCADE53 is a LONG parse (337 lemma steps from the spine:      *)
(*  74 TUP, 49 TDN, 49 pop12, 34 DIPGRIND levels, 27 TUP2_1,        *)
(*  20 hGRIND_even, 18 PUSH, 15 POP, 12 PX2A, 9 PUSHX, 6 PX2Bgen,   *)
(*  6 TRANS2_1, 5 PX2B0, 5 CLEANG_odd, 4 CLEANG_even, 3 PX2A0,      *)
(*  1 hGRIND) -- longer than CASCADE52 (227 steps): it regrows      *)
(*  a nine-block frame.  DIPGRIND sub-levels (A, r):                *)
(*  (23250, 128552), (50436, 27674), (567, 24959), (12, 257),       *)
(*  (32, 187), (3, 5), (3, 2), (74, 33), (3, 37), (3, 2),           *)
(*  (13, 5), (1172, 22609), (110, 503), (3, 6), (3, 2), (226, 45),  *)
(*  (12, 87), (32, 17), (3, 5), (3, 2), (2394, 17815),              *)
(*  (302, 1040), (3, 37), (3, 2), (13, 5), (4794, 8221),            *)
(*  (613, 2203), (18, 298), (18, 2), (43, 206), (3, 6), (3, 2),     *)
(*  (92, 16), (12, 20).  The two largest sub-levels,                *)
(*  (23250, 128552) and (50436, 27674), sit near the stack          *)
(*  bottom for long stretches; clean exits: CLEANG_even             *)
(*  516, 6, 4, 13833 and CLEANG_odd 12, 4, 18, 1097, 4106.          *)
(*                                                                  *)
(*  TOP7 then closes by the size of r7 = 2 * j7 (j7 = j - 323289    *)
(*  in TOP7's own parameter):                                       *)
(*    r7 = 2:       TRANS2_1 + CASCADE_POPFIN, A = 646579 + beta,   *)
(*                    frame [350962; 109099; 62236; ...];           *)
(*    r7 = 4:       TUP + hGRIND_even 323287 + TRANS2_2             *)
(*                    + CASCADE_POPFIN, A = beta + 2;               *)
(*    r7 = 6:       TUP + hGRIND_even 323287 + TUP2_1 + TDN         *)
(*                    + TRANS2_1 + CASCADE_POPFIN, A = beta + 4;    *)
(*    8 <= r7 <= 1293162 (band 7): TUP + hGRIND_even 323287         *)
(*      + TUP2_1 + TDN + TUP onto GRIND8 = HC [350961; 109099;      *)
(*      ...] 646578 3 2 ((r7 - 6, 2) :: tail), whose pair grinds    *)
(*      CLEANLY by CLEANG_even (floor (r7 - 8)/2 + 1 <= 646578,     *)
(*      exactly r7 <= 1293162), then TRANS2_1 + CASCADE_POPFIN,    *)
(*      A = r7 + beta - 2, frame [646579; 350961; 109099; ...].     *)
(*      (The band counter is again the shuttle moved into the       *)
(*      counter slot by TUP2_1: 646578, not 350961.)                *)
(*                                                                  *)
(*  For r7 >= 1293164 (j7 >= 646582, i.e. TOP6-parameter            *)
(*  j >= 969871) the pair (r7 - 6, 2) at counter 646578 exceeds     *)
(*  the CLEANG_even floor and the rounds take the DIPDESC           *)
(*  boundary an EIGHTH time (hsim53 Part 3: the GRIND8 state and    *)
(*  the DIPGRIND (646578, r7 - 1293162) landing both occur at       *)
(*  j = 969871, 969872, 1000000).  The eighth descent is expected   *)
(*  to be a NEW cascade with different constants, so no cycle       *)
(*  induction in the current vocabulary closes it; what remains     *)
(*  is the strictly smaller core                                    *)
(*                                                                  *)
(*    TAIL2_END8: the totality of the ONE pair (2j, 2) at the ONE   *)
(*    fixed TOP7 state HB [109099; 62236; 6030; 630; 191; 113;      *)
(*    33; 19; 0] 350961 1 646579, for j >= 646582 (r7 = 2j          *)
(*    >= 1293164), beta >= 2.                                       *)
(*                                                                  *)
(*  The core's range shrank from [323290, infty) to [969871, infty) *)
(*  in TOP6 parameters; the band width roughly doubled again        *)
(*  (323290 -> 969870).  Via TAIL2_END7_of53 + TAIL2_END6_of52 +    *)
(*  ESC_ERA_LAW_52 the ESC instances at every even R >= 1278 now    *)
(*  rest on TAIL2_END8 alone (ESC_ERA_LAW_53 below; Loop.v          *)
(*  Part 4n).                                                       *)
(* ================================================================= *)

Require Import List Bool Arith Lia ZArith.
Import ListNotations.
Require Import TM Sections Mirror TokenPass Recoord Era Esc Dev
               Grind Grind2 Grind3 Grind4 Grind5 Grind6 Grind7 Grind8
               Grind9 Grind10 Grind11 Grind12 Grind13 Grind14 Grind15
               Grind16 Grind17 Grind18 Grind19 Grind20.

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
(* the step blocks; in this file that inline form stack-overflows  *)
(* inside the long hsteps_trans chains (deterministic at            *)
(* TOP53_TO_TOP7 step 2), while the standalone assert/rewrite form  *)
(* compiles -- so the identities live here, in a small context,     *)
(* and the step blocks use plain `rewrite`.                         *)
Lemma NUM53a : 323286 = 2 * 161641 + 4.
Proof. apply Nat.eqb_eq; vm_compute; reflexivity. Qed.
Lemma NUM53b : 175058 = S 175057.
Proof. apply Nat.eqb_eq; vm_compute; reflexivity. Qed.
Lemma NUM53c : 646578 = 2 * 323287 + 4.
Proof. apply Nat.eqb_eq; vm_compute; reflexivity. Qed.
Lemma NUM53d : 350961 = S 350960.
Proof. apply Nat.eqb_eq; vm_compute; reflexivity. Qed.
(* S-form / subtraction identities for the TOP7 closings: the      *)
(* sTRANS2_1, sTUP2_1, sTUP and hTRANS2_2 applies at shuttle        *)
(* 646579 otherwise force S/subtraction conversions of unary        *)
(* depth ~646579, which overflow the conversion stack (the          *)
(* sTRANS2_1 apply in TOP53_2 is the witnessed failure); rewriting  *)
(* the goal's numerals to the lemmas' computed forms first makes    *)
(* the applies syntactic.                                           *)
Lemma NUM53e : 646579 = S 646578.
Proof. apply Nat.eqb_eq; vm_compute; reflexivity. Qed.
Lemma NUM53f : 646580 = S (S 646578).
Proof. apply Nat.eqb_eq; vm_compute; reflexivity. Qed.
Lemma NUM53g : 350962 = S 350961.
Proof. apply Nat.eqb_eq; vm_compute; reflexivity. Qed.
Lemma NUM53h : 646578 = 646579 - 1.
Proof. apply Nat.eqb_eq; vm_compute; reflexivity. Qed.
Lemma NUM53k : 646578 = S 646577.
Proof. apply Nat.eqb_eq; vm_compute; reflexivity. Qed.
Lemma NUM53m : 646579 = S (S 646577).
Proof. apply Nat.eqb_eq; vm_compute; reflexivity. Qed.
Lemma NUM53n : 646580 = S 646579.
Proof. apply Nat.eqb_eq; vm_compute; reflexivity. Qed.
Lemma NUM53p : 323290 = S 323289.
Proof. apply Nat.eqb_eq; vm_compute; reflexivity. Qed.
Lemma NUM53q : 646582 = S 646581.
Proof. apply Nat.eqb_eq; vm_compute; reflexivity. Qed.
Lemma NUM53r : 646578 = 646581 - 3.
Proof. apply Nat.eqb_eq; vm_compute; reflexivity. Qed.
(* ----------------------------------------------------------------- *)
(* CASCADE53: the DIP7 spine over frame [175058; 23252; 3931;      *)
(* 2847; 569; 287; 14; 5] regrows onto TOP7, for an ARBITRARY       *)
(* tail w.  The proof is an hsteps_trans chain of 337 classified    *)
(* steps (waypoints asserted verbatim in hsim53.py); step kinds     *)
(* are annotated per step.  NOTE (Phase 53, applying the Phase 52   *)
(* lesson proactively): kernel conversion over of_num_uint          *)
(* numerals overflows the default stack at unary depth ~175000,     *)
(* and this phase's constants reach ~646579, so the chain is        *)
(* split from the start into seven consecutive sub-lemmas:          *)
(* CASCADE53a (steps 1-56), CASCADE53b (57-112), CASCADE53c         *)
(* (113-168), CASCADE53d (169-224), CASCADE53e (225-280),           *)
(* CASCADE53f (281-336) and CASCADE53g (step 337 alone);            *)
(* CASCADE53 below is their composition, its statement the          *)
(* spine-to-TOP7 step.  Step 337 is isolated because its            *)
(* pop12 323288 landing forces the kernel conversions              *)
(* 27673 + 323288 = 350961 and 3 + 2 * 323288 = 646579, whose       *)
(* unary depth overflows the conversion stack; CASCADE53g first    *)
(* rewrites the goal's numerals to pop12's computed form, the two   *)
(* equalities being discharged by Nat.eqb_eq + vm_compute           *)
(* (VM-cast conversion).  The hGRIND_even steps in the TOP7         *)
(* closings below are preceded by rewrites via the standalone       *)
(* NUM53 numeral identities (the Phase 52 fix-up pattern, with      *)
(* the identities factored into lemmas -- see the NUM53 note).      *)
(* No step script was otherwise altered.                            *)
(* ----------------------------------------------------------------- *)

(* CASCADE53a: steps 1-56 of the CASCADE53 chain. *)
Lemma CASCADE53a : forall w,
  hsteps (HC [175058; 23252; 3931; 2847; 569; 287; 14; 5] 0 3 2 (repeat (1, 2) 323286 ++ w) 1)
         (HB [5] 48 1 74 ((2, 2) :: (185, 2) :: (1, 1) :: repeat (1, 2) 569 ++ (24959, 2) :: (1, 1) :: repeat (1, 2) 50438 ++ (27674, 2) :: (1, 1) :: repeat (1, 2) 323288 ++ w) 1).
Proof.
  intro w.
  (* step 1: P PX2A *)
  apply (hsteps_trans _ (HC [3931; 2847; 569; 287; 14; 5] 23251 175056 2 ((1, 1) :: repeat (1, 2) 323288 ++ w) 1)).
  {
    apply (hsteps_step _ (HC [3931; 2847; 569; 287; 14; 5] 23251 175056 2 ((1, 1) :: repeat (1, 2) 323288 ++ w) 1)); [apply hPX2A | apply hsteps_refl].
  }
  (* step 2: P PUSH *)
  apply (hsteps_trans _ (HC [3931; 2847; 569; 287; 14; 5] 23250 1 2 ((175054, 2) :: (1, 1) :: repeat (1, 2) 323288 ++ w) 1)).
  {
    replace ((175054, 2) :: (1, 1) :: repeat (1, 2) 323288 ++ w) with ((175056 - 2, 2) :: (1, 1) :: repeat (1, 2) 323288 ++ w) by sec_eq.
    apply (sPUSH [3931; 2847; 569; 287; 14; 5] 23250 175056 ((1, 1) :: repeat (1, 2) 323288 ++ w) 1); closearith.
  }
  (* step 3: P TDN *)
  apply (hsteps_trans _ (HB [3931; 2847; 569; 287; 14; 5] 23250 1 4 ((175054, 2) :: (1, 1) :: repeat (1, 2) 323288 ++ w) 1)).
  {
    apply (sTDN [3931; 2847; 569; 287; 14; 5] 23250 ((175054, 2) :: (1, 1) :: repeat (1, 2) 323288 ++ w) 1).
  }
  (* step 4: sTUP *)
  apply (hsteps_trans _ (HC [3931; 2847; 569; 287; 14; 5] 23250 3 2 ((175052, 2) :: (1, 1) :: repeat (1, 2) 323288 ++ w) 1)).
  {
    replace ((175052, 2) :: (1, 1) :: repeat (1, 2) 323288 ++ w) with ((175054 - 2, 2) :: (1, 1) :: repeat (1, 2) 323288 ++ w) by sec_eq.
    apply (sTUP [3931; 2847; 569; 287; 14; 5] 23250 4 175054 2 ((1, 1) :: repeat (1, 2) 323288 ++ w) 1); closearith.
  }
  (* step 5: DIPGRIND 23250 128552 *)
  apply (hsteps_trans _ (HC [3931; 2847; 569; 287; 14; 5] 0 3 2 (repeat (1, 2) 23250 ++ (128552, 2) :: (1, 1) :: repeat (1, 2) 323288 ++ w) 1)).
  {
    apply (DIPGRIND 23250 128552 [3931; 2847; 569; 287; 14; 5] ((1, 1) :: repeat (1, 2) 323288 ++ w) 1); closearith.
  }
  (* step 6: P PX2A *)
  apply (hsteps_trans _ (HC [569; 287; 14; 5] 2846 3929 2 ((1, 1) :: repeat (1, 2) 23252 ++ (128552, 2) :: (1, 1) :: repeat (1, 2) 323288 ++ w) 1)).
  {
    apply (hsteps_step _ (HC [569; 287; 14; 5] 2846 3929 2 ((1, 1) :: repeat (1, 2) 23252 ++ (128552, 2) :: (1, 1) :: repeat (1, 2) 323288 ++ w) 1)); [apply hPX2A | apply hsteps_refl].
  }
  (* step 7: hGRIND 1963 *)
  apply (hsteps_trans _ (HB [569; 287; 14; 5] 2846 1 3932 ((1, 1) :: repeat (1, 2) 23252 ++ (128552, 2) :: (1, 1) :: repeat (1, 2) 323288 ++ w) 1)).
  {
    apply (hGRIND 1963 [569; 287; 14; 5] 2846 ((1, 1) :: repeat (1, 2) 23252 ++ (128552, 2) :: (1, 1) :: repeat (1, 2) 323288 ++ w) 1); closearith.
  }
  (* step 8: P POP *)
  apply (hsteps_trans _ (HB [569; 287; 14; 5] 2847 1 3933 (repeat (1, 2) 23252 ++ (128552, 2) :: (1, 1) :: repeat (1, 2) 323288 ++ w) 1)).
  {
    apply (sPOP1 [569; 287; 14; 5] 2846 3932 (repeat (1, 2) 23252 ++ (128552, 2) :: (1, 1) :: repeat (1, 2) 323288 ++ w) 1); closearith.
  }
  (* step 9: M pop12 (23252,) *)
  apply (hsteps_trans _ (HB [569; 287; 14; 5] 26099 1 50437 ((128552, 2) :: (1, 1) :: repeat (1, 2) 323288 ++ w) 1)).
  {
    apply (pop12 23252 [569; 287; 14; 5] 2847 3933 ((128552, 2) :: (1, 1) :: repeat (1, 2) 323288 ++ w) 1); closearith.
  }
  (* step 10: sTUP *)
  apply (hsteps_trans _ (HC [569; 287; 14; 5] 26099 50436 2 ((128550, 2) :: (1, 1) :: repeat (1, 2) 323288 ++ w) 1)).
  {
    replace ((128550, 2) :: (1, 1) :: repeat (1, 2) 323288 ++ w) with ((128552 - 2, 2) :: (1, 1) :: repeat (1, 2) 323288 ++ w) by sec_eq.
    apply (sTUP [569; 287; 14; 5] 26099 50437 128552 2 ((1, 1) :: repeat (1, 2) 323288 ++ w) 1); closearith.
  }
  (* step 11: hGRIND_even 25216 *)
  apply (hsteps_trans _ (HB [569; 287; 14; 5] 26098 1 50436 ((2, 2) :: (128550, 2) :: (1, 1) :: repeat (1, 2) 323288 ++ w) 1)).
  {
    apply (hGRIND_even 25216 [569; 287; 14; 5] 26098 ((128550, 2) :: (1, 1) :: repeat (1, 2) 323288 ++ w) 1); closearith.
  }
  (* step 12: P TUP2_1 *)
  apply (hsteps_trans _ (HC [26099; 569; 287; 14; 5] 50436 1 2 ((128548, 2) :: (1, 1) :: repeat (1, 2) 323288 ++ w) 1)).
  {
    replace ((128548, 2) :: (1, 1) :: repeat (1, 2) 323288 ++ w) with ((128550 - 2, 2) :: (1, 1) :: repeat (1, 2) 323288 ++ w) by sec_eq.
    apply (sTUP2_1 [569; 287; 14; 5] 26098 50435 128550 ((1, 1) :: repeat (1, 2) 323288 ++ w) 1); closearith.
  }
  (* step 13: P TDN *)
  apply (hsteps_trans _ (HB [26099; 569; 287; 14; 5] 50436 1 4 ((128548, 2) :: (1, 1) :: repeat (1, 2) 323288 ++ w) 1)).
  {
    apply (sTDN [26099; 569; 287; 14; 5] 50436 ((128548, 2) :: (1, 1) :: repeat (1, 2) 323288 ++ w) 1).
  }
  (* step 14: sTUP *)
  apply (hsteps_trans _ (HC [26099; 569; 287; 14; 5] 50436 3 2 ((128546, 2) :: (1, 1) :: repeat (1, 2) 323288 ++ w) 1)).
  {
    replace ((128546, 2) :: (1, 1) :: repeat (1, 2) 323288 ++ w) with ((128548 - 2, 2) :: (1, 1) :: repeat (1, 2) 323288 ++ w) by sec_eq.
    apply (sTUP [26099; 569; 287; 14; 5] 50436 4 128548 2 ((1, 1) :: repeat (1, 2) 323288 ++ w) 1); closearith.
  }
  (* step 15: DIPGRIND 50436 27674 *)
  apply (hsteps_trans _ (HC [26099; 569; 287; 14; 5] 0 3 2 (repeat (1, 2) 50436 ++ (27674, 2) :: (1, 1) :: repeat (1, 2) 323288 ++ w) 1)).
  {
    apply (DIPGRIND 50436 27674 [26099; 569; 287; 14; 5] ((1, 1) :: repeat (1, 2) 323288 ++ w) 1); closearith.
  }
  (* step 16: P PX2A *)
  apply (hsteps_trans _ (HC [287; 14; 5] 568 26097 2 ((1, 1) :: repeat (1, 2) 50438 ++ (27674, 2) :: (1, 1) :: repeat (1, 2) 323288 ++ w) 1)).
  {
    apply (hsteps_step _ (HC [287; 14; 5] 568 26097 2 ((1, 1) :: repeat (1, 2) 50438 ++ (27674, 2) :: (1, 1) :: repeat (1, 2) 323288 ++ w) 1)); [apply hPX2A | apply hsteps_refl].
  }
  (* step 17: P PUSH *)
  apply (hsteps_trans _ (HC [287; 14; 5] 567 1 2 ((26095, 2) :: (1, 1) :: repeat (1, 2) 50438 ++ (27674, 2) :: (1, 1) :: repeat (1, 2) 323288 ++ w) 1)).
  {
    replace ((26095, 2) :: (1, 1) :: repeat (1, 2) 50438 ++ (27674, 2) :: (1, 1) :: repeat (1, 2) 323288 ++ w) with ((26097 - 2, 2) :: (1, 1) :: repeat (1, 2) 50438 ++ (27674, 2) :: (1, 1) :: repeat (1, 2) 323288 ++ w) by sec_eq.
    apply (sPUSH [287; 14; 5] 567 26097 ((1, 1) :: repeat (1, 2) 50438 ++ (27674, 2) :: (1, 1) :: repeat (1, 2) 323288 ++ w) 1); closearith.
  }
  (* step 18: P TDN *)
  apply (hsteps_trans _ (HB [287; 14; 5] 567 1 4 ((26095, 2) :: (1, 1) :: repeat (1, 2) 50438 ++ (27674, 2) :: (1, 1) :: repeat (1, 2) 323288 ++ w) 1)).
  {
    apply (sTDN [287; 14; 5] 567 ((26095, 2) :: (1, 1) :: repeat (1, 2) 50438 ++ (27674, 2) :: (1, 1) :: repeat (1, 2) 323288 ++ w) 1).
  }
  (* step 19: sTUP *)
  apply (hsteps_trans _ (HC [287; 14; 5] 567 3 2 ((26093, 2) :: (1, 1) :: repeat (1, 2) 50438 ++ (27674, 2) :: (1, 1) :: repeat (1, 2) 323288 ++ w) 1)).
  {
    replace ((26093, 2) :: (1, 1) :: repeat (1, 2) 50438 ++ (27674, 2) :: (1, 1) :: repeat (1, 2) 323288 ++ w) with ((26095 - 2, 2) :: (1, 1) :: repeat (1, 2) 50438 ++ (27674, 2) :: (1, 1) :: repeat (1, 2) 323288 ++ w) by sec_eq.
    apply (sTUP [287; 14; 5] 567 4 26095 2 ((1, 1) :: repeat (1, 2) 50438 ++ (27674, 2) :: (1, 1) :: repeat (1, 2) 323288 ++ w) 1); closearith.
  }
  (* step 20: DIPGRIND 567 24959 *)
  apply (hsteps_trans _ (HC [287; 14; 5] 0 3 2 (repeat (1, 2) 567 ++ (24959, 2) :: (1, 1) :: repeat (1, 2) 50438 ++ (27674, 2) :: (1, 1) :: repeat (1, 2) 323288 ++ w) 1)).
  {
    apply (DIPGRIND 567 24959 [287; 14; 5] ((1, 1) :: repeat (1, 2) 50438 ++ (27674, 2) :: (1, 1) :: repeat (1, 2) 323288 ++ w) 1); closearith.
  }
  (* step 21: P PX2A *)
  apply (hsteps_trans _ (HC [5] 13 285 2 ((1, 1) :: repeat (1, 2) 569 ++ (24959, 2) :: (1, 1) :: repeat (1, 2) 50438 ++ (27674, 2) :: (1, 1) :: repeat (1, 2) 323288 ++ w) 1)).
  {
    apply (hsteps_step _ (HC [5] 13 285 2 ((1, 1) :: repeat (1, 2) 569 ++ (24959, 2) :: (1, 1) :: repeat (1, 2) 50438 ++ (27674, 2) :: (1, 1) :: repeat (1, 2) 323288 ++ w) 1)); [apply hPX2A | apply hsteps_refl].
  }
  (* step 22: P PUSH *)
  apply (hsteps_trans _ (HC [5] 12 1 2 ((283, 2) :: (1, 1) :: repeat (1, 2) 569 ++ (24959, 2) :: (1, 1) :: repeat (1, 2) 50438 ++ (27674, 2) :: (1, 1) :: repeat (1, 2) 323288 ++ w) 1)).
  {
    replace ((283, 2) :: (1, 1) :: repeat (1, 2) 569 ++ (24959, 2) :: (1, 1) :: repeat (1, 2) 50438 ++ (27674, 2) :: (1, 1) :: repeat (1, 2) 323288 ++ w) with ((285 - 2, 2) :: (1, 1) :: repeat (1, 2) 569 ++ (24959, 2) :: (1, 1) :: repeat (1, 2) 50438 ++ (27674, 2) :: (1, 1) :: repeat (1, 2) 323288 ++ w) by sec_eq.
    apply (sPUSH [5] 12 285 ((1, 1) :: repeat (1, 2) 569 ++ (24959, 2) :: (1, 1) :: repeat (1, 2) 50438 ++ (27674, 2) :: (1, 1) :: repeat (1, 2) 323288 ++ w) 1); closearith.
  }
  (* step 23: P TDN *)
  apply (hsteps_trans _ (HB [5] 12 1 4 ((283, 2) :: (1, 1) :: repeat (1, 2) 569 ++ (24959, 2) :: (1, 1) :: repeat (1, 2) 50438 ++ (27674, 2) :: (1, 1) :: repeat (1, 2) 323288 ++ w) 1)).
  {
    apply (sTDN [5] 12 ((283, 2) :: (1, 1) :: repeat (1, 2) 569 ++ (24959, 2) :: (1, 1) :: repeat (1, 2) 50438 ++ (27674, 2) :: (1, 1) :: repeat (1, 2) 323288 ++ w) 1).
  }
  (* step 24: sTUP *)
  apply (hsteps_trans _ (HC [5] 12 3 2 ((281, 2) :: (1, 1) :: repeat (1, 2) 569 ++ (24959, 2) :: (1, 1) :: repeat (1, 2) 50438 ++ (27674, 2) :: (1, 1) :: repeat (1, 2) 323288 ++ w) 1)).
  {
    replace ((281, 2) :: (1, 1) :: repeat (1, 2) 569 ++ (24959, 2) :: (1, 1) :: repeat (1, 2) 50438 ++ (27674, 2) :: (1, 1) :: repeat (1, 2) 323288 ++ w) with ((283 - 2, 2) :: (1, 1) :: repeat (1, 2) 569 ++ (24959, 2) :: (1, 1) :: repeat (1, 2) 50438 ++ (27674, 2) :: (1, 1) :: repeat (1, 2) 323288 ++ w) by sec_eq.
    apply (sTUP [5] 12 4 283 2 ((1, 1) :: repeat (1, 2) 569 ++ (24959, 2) :: (1, 1) :: repeat (1, 2) 50438 ++ (27674, 2) :: (1, 1) :: repeat (1, 2) 323288 ++ w) 1); closearith.
  }
  (* step 25: DIPGRIND 12 257 *)
  apply (hsteps_trans _ (HC [5] 0 3 2 (repeat (1, 2) 12 ++ (257, 2) :: (1, 1) :: repeat (1, 2) 569 ++ (24959, 2) :: (1, 1) :: repeat (1, 2) 50438 ++ (27674, 2) :: (1, 1) :: repeat (1, 2) 323288 ++ w) 1)).
  {
    apply (DIPGRIND 12 257 [5] ((1, 1) :: repeat (1, 2) 569 ++ (24959, 2) :: (1, 1) :: repeat (1, 2) 50438 ++ (27674, 2) :: (1, 1) :: repeat (1, 2) 323288 ++ w) 1); closearith.
  }
  (* step 26: P PX2Bgen *)
  apply (hsteps_trans _ (HB [0] 3 1 2 (repeat (1, 2) 1 ++ (1, 1) :: repeat (1, 2) 14 ++ (257, 2) :: (1, 1) :: repeat (1, 2) 569 ++ (24959, 2) :: (1, 1) :: repeat (1, 2) 50438 ++ (27674, 2) :: (1, 1) :: repeat (1, 2) 323288 ++ w) 1)).
  {
    apply (hsteps_step _ (HB [0] 3 1 2 (repeat (1, 2) 1 ++ (1, 1) :: repeat (1, 2) 14 ++ (257, 2) :: (1, 1) :: repeat (1, 2) 569 ++ (24959, 2) :: (1, 1) :: repeat (1, 2) 50438 ++ (27674, 2) :: (1, 1) :: repeat (1, 2) 323288 ++ w) 1)); [apply hPX2Bgen | apply hsteps_refl].
  }
  (* step 27: M pop12 (1,) *)
  apply (hsteps_trans _ (HB [0] 4 1 4 ((1, 1) :: repeat (1, 2) 14 ++ (257, 2) :: (1, 1) :: repeat (1, 2) 569 ++ (24959, 2) :: (1, 1) :: repeat (1, 2) 50438 ++ (27674, 2) :: (1, 1) :: repeat (1, 2) 323288 ++ w) 1)).
  {
    apply (pop12 1 [0] 3 2 ((1, 1) :: repeat (1, 2) 14 ++ (257, 2) :: (1, 1) :: repeat (1, 2) 569 ++ (24959, 2) :: (1, 1) :: repeat (1, 2) 50438 ++ (27674, 2) :: (1, 1) :: repeat (1, 2) 323288 ++ w) 1); closearith.
  }
  (* step 28: P POP *)
  apply (hsteps_trans _ (HB [0] 5 1 5 (repeat (1, 2) 14 ++ (257, 2) :: (1, 1) :: repeat (1, 2) 569 ++ (24959, 2) :: (1, 1) :: repeat (1, 2) 50438 ++ (27674, 2) :: (1, 1) :: repeat (1, 2) 323288 ++ w) 1)).
  {
    apply (sPOP1 [0] 4 4 (repeat (1, 2) 14 ++ (257, 2) :: (1, 1) :: repeat (1, 2) 569 ++ (24959, 2) :: (1, 1) :: repeat (1, 2) 50438 ++ (27674, 2) :: (1, 1) :: repeat (1, 2) 323288 ++ w) 1); closearith.
  }
  (* step 29: M pop12 (14,) *)
  apply (hsteps_trans _ (HB [0] 19 1 33 ((257, 2) :: (1, 1) :: repeat (1, 2) 569 ++ (24959, 2) :: (1, 1) :: repeat (1, 2) 50438 ++ (27674, 2) :: (1, 1) :: repeat (1, 2) 323288 ++ w) 1)).
  {
    apply (pop12 14 [0] 5 5 ((257, 2) :: (1, 1) :: repeat (1, 2) 569 ++ (24959, 2) :: (1, 1) :: repeat (1, 2) 50438 ++ (27674, 2) :: (1, 1) :: repeat (1, 2) 323288 ++ w) 1); closearith.
  }
  (* step 30: sTUP *)
  apply (hsteps_trans _ (HC [0] 19 32 2 ((255, 2) :: (1, 1) :: repeat (1, 2) 569 ++ (24959, 2) :: (1, 1) :: repeat (1, 2) 50438 ++ (27674, 2) :: (1, 1) :: repeat (1, 2) 323288 ++ w) 1)).
  {
    replace ((255, 2) :: (1, 1) :: repeat (1, 2) 569 ++ (24959, 2) :: (1, 1) :: repeat (1, 2) 50438 ++ (27674, 2) :: (1, 1) :: repeat (1, 2) 323288 ++ w) with ((257 - 2, 2) :: (1, 1) :: repeat (1, 2) 569 ++ (24959, 2) :: (1, 1) :: repeat (1, 2) 50438 ++ (27674, 2) :: (1, 1) :: repeat (1, 2) 323288 ++ w) by sec_eq.
    apply (sTUP [0] 19 33 257 2 ((1, 1) :: repeat (1, 2) 569 ++ (24959, 2) :: (1, 1) :: repeat (1, 2) 50438 ++ (27674, 2) :: (1, 1) :: repeat (1, 2) 323288 ++ w) 1); closearith.
  }
  (* step 31: hGRIND_even 14 *)
  apply (hsteps_trans _ (HB [0] 18 1 32 ((2, 2) :: (255, 2) :: (1, 1) :: repeat (1, 2) 569 ++ (24959, 2) :: (1, 1) :: repeat (1, 2) 50438 ++ (27674, 2) :: (1, 1) :: repeat (1, 2) 323288 ++ w) 1)).
  {
    apply (hGRIND_even 14 [0] 18 ((255, 2) :: (1, 1) :: repeat (1, 2) 569 ++ (24959, 2) :: (1, 1) :: repeat (1, 2) 50438 ++ (27674, 2) :: (1, 1) :: repeat (1, 2) 323288 ++ w) 1); closearith.
  }
  (* step 32: P TUP2_1 *)
  apply (hsteps_trans _ (HC [19; 0] 32 1 2 ((253, 2) :: (1, 1) :: repeat (1, 2) 569 ++ (24959, 2) :: (1, 1) :: repeat (1, 2) 50438 ++ (27674, 2) :: (1, 1) :: repeat (1, 2) 323288 ++ w) 1)).
  {
    replace ((253, 2) :: (1, 1) :: repeat (1, 2) 569 ++ (24959, 2) :: (1, 1) :: repeat (1, 2) 50438 ++ (27674, 2) :: (1, 1) :: repeat (1, 2) 323288 ++ w) with ((255 - 2, 2) :: (1, 1) :: repeat (1, 2) 569 ++ (24959, 2) :: (1, 1) :: repeat (1, 2) 50438 ++ (27674, 2) :: (1, 1) :: repeat (1, 2) 323288 ++ w) by sec_eq.
    apply (sTUP2_1 [0] 18 31 255 ((1, 1) :: repeat (1, 2) 569 ++ (24959, 2) :: (1, 1) :: repeat (1, 2) 50438 ++ (27674, 2) :: (1, 1) :: repeat (1, 2) 323288 ++ w) 1); closearith.
  }
  (* step 33: P TDN *)
  apply (hsteps_trans _ (HB [19; 0] 32 1 4 ((253, 2) :: (1, 1) :: repeat (1, 2) 569 ++ (24959, 2) :: (1, 1) :: repeat (1, 2) 50438 ++ (27674, 2) :: (1, 1) :: repeat (1, 2) 323288 ++ w) 1)).
  {
    apply (sTDN [19; 0] 32 ((253, 2) :: (1, 1) :: repeat (1, 2) 569 ++ (24959, 2) :: (1, 1) :: repeat (1, 2) 50438 ++ (27674, 2) :: (1, 1) :: repeat (1, 2) 323288 ++ w) 1).
  }
  (* step 34: sTUP *)
  apply (hsteps_trans _ (HC [19; 0] 32 3 2 ((251, 2) :: (1, 1) :: repeat (1, 2) 569 ++ (24959, 2) :: (1, 1) :: repeat (1, 2) 50438 ++ (27674, 2) :: (1, 1) :: repeat (1, 2) 323288 ++ w) 1)).
  {
    replace ((251, 2) :: (1, 1) :: repeat (1, 2) 569 ++ (24959, 2) :: (1, 1) :: repeat (1, 2) 50438 ++ (27674, 2) :: (1, 1) :: repeat (1, 2) 323288 ++ w) with ((253 - 2, 2) :: (1, 1) :: repeat (1, 2) 569 ++ (24959, 2) :: (1, 1) :: repeat (1, 2) 50438 ++ (27674, 2) :: (1, 1) :: repeat (1, 2) 323288 ++ w) by sec_eq.
    apply (sTUP [19; 0] 32 4 253 2 ((1, 1) :: repeat (1, 2) 569 ++ (24959, 2) :: (1, 1) :: repeat (1, 2) 50438 ++ (27674, 2) :: (1, 1) :: repeat (1, 2) 323288 ++ w) 1); closearith.
  }
  (* step 35: DIPGRIND 32 187 *)
  apply (hsteps_trans _ (HC [19; 0] 0 3 2 (repeat (1, 2) 32 ++ (187, 2) :: (1, 1) :: repeat (1, 2) 569 ++ (24959, 2) :: (1, 1) :: repeat (1, 2) 50438 ++ (27674, 2) :: (1, 1) :: repeat (1, 2) 323288 ++ w) 1)).
  {
    apply (DIPGRIND 32 187 [19; 0] ((1, 1) :: repeat (1, 2) 569 ++ (24959, 2) :: (1, 1) :: repeat (1, 2) 50438 ++ (27674, 2) :: (1, 1) :: repeat (1, 2) 323288 ++ w) 1); closearith.
  }
  (* step 36: P PX2A0 *)
  apply (hsteps_trans _ (HB [0] 3 1 2 ((15, 2) :: (1, 1) :: repeat (1, 2) 34 ++ (187, 2) :: (1, 1) :: repeat (1, 2) 569 ++ (24959, 2) :: (1, 1) :: repeat (1, 2) 50438 ++ (27674, 2) :: (1, 1) :: repeat (1, 2) 323288 ++ w) 1)).
  {
    apply (hsteps_step _ (HB [0] 3 1 2 ((15, 2) :: (1, 1) :: repeat (1, 2) 34 ++ (187, 2) :: (1, 1) :: repeat (1, 2) 569 ++ (24959, 2) :: (1, 1) :: repeat (1, 2) 50438 ++ (27674, 2) :: (1, 1) :: repeat (1, 2) 323288 ++ w) 1)); [apply hPX2A0 | apply hsteps_refl].
  }
  (* step 37: sTUP *)
  apply (hsteps_trans _ (HC [0] 3 1 2 ((13, 2) :: (1, 1) :: repeat (1, 2) 34 ++ (187, 2) :: (1, 1) :: repeat (1, 2) 569 ++ (24959, 2) :: (1, 1) :: repeat (1, 2) 50438 ++ (27674, 2) :: (1, 1) :: repeat (1, 2) 323288 ++ w) 1)).
  {
    replace ((13, 2) :: (1, 1) :: repeat (1, 2) 34 ++ (187, 2) :: (1, 1) :: repeat (1, 2) 569 ++ (24959, 2) :: (1, 1) :: repeat (1, 2) 50438 ++ (27674, 2) :: (1, 1) :: repeat (1, 2) 323288 ++ w) with ((15 - 2, 2) :: (1, 1) :: repeat (1, 2) 34 ++ (187, 2) :: (1, 1) :: repeat (1, 2) 569 ++ (24959, 2) :: (1, 1) :: repeat (1, 2) 50438 ++ (27674, 2) :: (1, 1) :: repeat (1, 2) 323288 ++ w) by sec_eq.
    apply (sTUP [0] 3 2 15 2 ((1, 1) :: repeat (1, 2) 34 ++ (187, 2) :: (1, 1) :: repeat (1, 2) 569 ++ (24959, 2) :: (1, 1) :: repeat (1, 2) 50438 ++ (27674, 2) :: (1, 1) :: repeat (1, 2) 323288 ++ w) 1); closearith.
  }
  (* step 38: P TDN *)
  apply (hsteps_trans _ (HB [0] 3 1 4 ((13, 2) :: (1, 1) :: repeat (1, 2) 34 ++ (187, 2) :: (1, 1) :: repeat (1, 2) 569 ++ (24959, 2) :: (1, 1) :: repeat (1, 2) 50438 ++ (27674, 2) :: (1, 1) :: repeat (1, 2) 323288 ++ w) 1)).
  {
    apply (sTDN [0] 3 ((13, 2) :: (1, 1) :: repeat (1, 2) 34 ++ (187, 2) :: (1, 1) :: repeat (1, 2) 569 ++ (24959, 2) :: (1, 1) :: repeat (1, 2) 50438 ++ (27674, 2) :: (1, 1) :: repeat (1, 2) 323288 ++ w) 1).
  }
  (* step 39: sTUP *)
  apply (hsteps_trans _ (HC [0] 3 3 2 ((11, 2) :: (1, 1) :: repeat (1, 2) 34 ++ (187, 2) :: (1, 1) :: repeat (1, 2) 569 ++ (24959, 2) :: (1, 1) :: repeat (1, 2) 50438 ++ (27674, 2) :: (1, 1) :: repeat (1, 2) 323288 ++ w) 1)).
  {
    replace ((11, 2) :: (1, 1) :: repeat (1, 2) 34 ++ (187, 2) :: (1, 1) :: repeat (1, 2) 569 ++ (24959, 2) :: (1, 1) :: repeat (1, 2) 50438 ++ (27674, 2) :: (1, 1) :: repeat (1, 2) 323288 ++ w) with ((13 - 2, 2) :: (1, 1) :: repeat (1, 2) 34 ++ (187, 2) :: (1, 1) :: repeat (1, 2) 569 ++ (24959, 2) :: (1, 1) :: repeat (1, 2) 50438 ++ (27674, 2) :: (1, 1) :: repeat (1, 2) 323288 ++ w) by sec_eq.
    apply (sTUP [0] 3 4 13 2 ((1, 1) :: repeat (1, 2) 34 ++ (187, 2) :: (1, 1) :: repeat (1, 2) 569 ++ (24959, 2) :: (1, 1) :: repeat (1, 2) 50438 ++ (27674, 2) :: (1, 1) :: repeat (1, 2) 323288 ++ w) 1); closearith.
  }
  (* step 40: DIPGRIND 3 5 *)
  apply (hsteps_trans _ (HC [0] 0 3 2 (repeat (1, 2) 3 ++ (5, 2) :: (1, 1) :: repeat (1, 2) 34 ++ (187, 2) :: (1, 1) :: repeat (1, 2) 569 ++ (24959, 2) :: (1, 1) :: repeat (1, 2) 50438 ++ (27674, 2) :: (1, 1) :: repeat (1, 2) 323288 ++ w) 1)).
  {
    apply (DIPGRIND 3 5 [0] ((1, 1) :: repeat (1, 2) 34 ++ (187, 2) :: (1, 1) :: repeat (1, 2) 569 ++ (24959, 2) :: (1, 1) :: repeat (1, 2) 50438 ++ (27674, 2) :: (1, 1) :: repeat (1, 2) 323288 ++ w) 1); closearith.
  }
  (* step 41: P PX2B0 *)
  apply (hsteps_trans _ (HB [] 0 1 5 (repeat (1, 2) 4 ++ (5, 2) :: (1, 1) :: repeat (1, 2) 34 ++ (187, 2) :: (1, 1) :: repeat (1, 2) 569 ++ (24959, 2) :: (1, 1) :: repeat (1, 2) 50438 ++ (27674, 2) :: (1, 1) :: repeat (1, 2) 323288 ++ w) 1)).
  {
    apply (hsteps_step _ (HB [] 0 1 5 (repeat (1, 2) 4 ++ (5, 2) :: (1, 1) :: repeat (1, 2) 34 ++ (187, 2) :: (1, 1) :: repeat (1, 2) 569 ++ (24959, 2) :: (1, 1) :: repeat (1, 2) 50438 ++ (27674, 2) :: (1, 1) :: repeat (1, 2) 323288 ++ w) 1)); [apply hPX2B0 | apply hsteps_refl].
  }
  (* step 42: M pop12 (4,) *)
  apply (hsteps_trans _ (HB [] 4 1 13 ((5, 2) :: (1, 1) :: repeat (1, 2) 34 ++ (187, 2) :: (1, 1) :: repeat (1, 2) 569 ++ (24959, 2) :: (1, 1) :: repeat (1, 2) 50438 ++ (27674, 2) :: (1, 1) :: repeat (1, 2) 323288 ++ w) 1)).
  {
    apply (pop12 4 [] 0 5 ((5, 2) :: (1, 1) :: repeat (1, 2) 34 ++ (187, 2) :: (1, 1) :: repeat (1, 2) 569 ++ (24959, 2) :: (1, 1) :: repeat (1, 2) 50438 ++ (27674, 2) :: (1, 1) :: repeat (1, 2) 323288 ++ w) 1); closearith.
  }
  (* step 43: sTUP *)
  apply (hsteps_trans _ (HC [] 4 12 2 ((3, 2) :: (1, 1) :: repeat (1, 2) 34 ++ (187, 2) :: (1, 1) :: repeat (1, 2) 569 ++ (24959, 2) :: (1, 1) :: repeat (1, 2) 50438 ++ (27674, 2) :: (1, 1) :: repeat (1, 2) 323288 ++ w) 1)).
  {
    replace ((3, 2) :: (1, 1) :: repeat (1, 2) 34 ++ (187, 2) :: (1, 1) :: repeat (1, 2) 569 ++ (24959, 2) :: (1, 1) :: repeat (1, 2) 50438 ++ (27674, 2) :: (1, 1) :: repeat (1, 2) 323288 ++ w) with ((5 - 2, 2) :: (1, 1) :: repeat (1, 2) 34 ++ (187, 2) :: (1, 1) :: repeat (1, 2) 569 ++ (24959, 2) :: (1, 1) :: repeat (1, 2) 50438 ++ (27674, 2) :: (1, 1) :: repeat (1, 2) 323288 ++ w) by sec_eq.
    apply (sTUP [] 4 13 5 2 ((1, 1) :: repeat (1, 2) 34 ++ (187, 2) :: (1, 1) :: repeat (1, 2) 569 ++ (24959, 2) :: (1, 1) :: repeat (1, 2) 50438 ++ (27674, 2) :: (1, 1) :: repeat (1, 2) 323288 ++ w) 1); closearith.
  }
  (* step 44: P PUSH *)
  apply (hsteps_trans _ (HC [] 3 1 2 ((10, 2) :: (3, 2) :: (1, 1) :: repeat (1, 2) 34 ++ (187, 2) :: (1, 1) :: repeat (1, 2) 569 ++ (24959, 2) :: (1, 1) :: repeat (1, 2) 50438 ++ (27674, 2) :: (1, 1) :: repeat (1, 2) 323288 ++ w) 1)).
  {
    replace ((10, 2) :: (3, 2) :: (1, 1) :: repeat (1, 2) 34 ++ (187, 2) :: (1, 1) :: repeat (1, 2) 569 ++ (24959, 2) :: (1, 1) :: repeat (1, 2) 50438 ++ (27674, 2) :: (1, 1) :: repeat (1, 2) 323288 ++ w) with ((12 - 2, 2) :: (3, 2) :: (1, 1) :: repeat (1, 2) 34 ++ (187, 2) :: (1, 1) :: repeat (1, 2) 569 ++ (24959, 2) :: (1, 1) :: repeat (1, 2) 50438 ++ (27674, 2) :: (1, 1) :: repeat (1, 2) 323288 ++ w) by sec_eq.
    apply (sPUSH [] 3 12 ((3, 2) :: (1, 1) :: repeat (1, 2) 34 ++ (187, 2) :: (1, 1) :: repeat (1, 2) 569 ++ (24959, 2) :: (1, 1) :: repeat (1, 2) 50438 ++ (27674, 2) :: (1, 1) :: repeat (1, 2) 323288 ++ w) 1); closearith.
  }
  (* step 45: P TDN *)
  apply (hsteps_trans _ (HB [] 3 1 4 ((10, 2) :: (3, 2) :: (1, 1) :: repeat (1, 2) 34 ++ (187, 2) :: (1, 1) :: repeat (1, 2) 569 ++ (24959, 2) :: (1, 1) :: repeat (1, 2) 50438 ++ (27674, 2) :: (1, 1) :: repeat (1, 2) 323288 ++ w) 1)).
  {
    apply (sTDN [] 3 ((10, 2) :: (3, 2) :: (1, 1) :: repeat (1, 2) 34 ++ (187, 2) :: (1, 1) :: repeat (1, 2) 569 ++ (24959, 2) :: (1, 1) :: repeat (1, 2) 50438 ++ (27674, 2) :: (1, 1) :: repeat (1, 2) 323288 ++ w) 1).
  }
  (* step 46: sTUP *)
  apply (hsteps_trans _ (HC [] 3 3 2 ((8, 2) :: (3, 2) :: (1, 1) :: repeat (1, 2) 34 ++ (187, 2) :: (1, 1) :: repeat (1, 2) 569 ++ (24959, 2) :: (1, 1) :: repeat (1, 2) 50438 ++ (27674, 2) :: (1, 1) :: repeat (1, 2) 323288 ++ w) 1)).
  {
    replace ((8, 2) :: (3, 2) :: (1, 1) :: repeat (1, 2) 34 ++ (187, 2) :: (1, 1) :: repeat (1, 2) 569 ++ (24959, 2) :: (1, 1) :: repeat (1, 2) 50438 ++ (27674, 2) :: (1, 1) :: repeat (1, 2) 323288 ++ w) with ((10 - 2, 2) :: (3, 2) :: (1, 1) :: repeat (1, 2) 34 ++ (187, 2) :: (1, 1) :: repeat (1, 2) 569 ++ (24959, 2) :: (1, 1) :: repeat (1, 2) 50438 ++ (27674, 2) :: (1, 1) :: repeat (1, 2) 323288 ++ w) by sec_eq.
    apply (sTUP [] 3 4 10 2 ((3, 2) :: (1, 1) :: repeat (1, 2) 34 ++ (187, 2) :: (1, 1) :: repeat (1, 2) 569 ++ (24959, 2) :: (1, 1) :: repeat (1, 2) 50438 ++ (27674, 2) :: (1, 1) :: repeat (1, 2) 323288 ++ w) 1); closearith.
  }
  (* step 47: DIPGRIND 3 2 *)
  apply (hsteps_trans _ (HC [] 0 3 2 (repeat (1, 2) 3 ++ (2, 2) :: (3, 2) :: (1, 1) :: repeat (1, 2) 34 ++ (187, 2) :: (1, 1) :: repeat (1, 2) 569 ++ (24959, 2) :: (1, 1) :: repeat (1, 2) 50438 ++ (27674, 2) :: (1, 1) :: repeat (1, 2) 323288 ++ w) 1)).
  {
    apply (DIPGRIND 3 2 [] ((3, 2) :: (1, 1) :: repeat (1, 2) 34 ++ (187, 2) :: (1, 1) :: repeat (1, 2) 569 ++ (24959, 2) :: (1, 1) :: repeat (1, 2) 50438 ++ (27674, 2) :: (1, 1) :: repeat (1, 2) 323288 ++ w) 1); closearith.
  }
  (* step 48: P PUSHX *)
  apply (hsteps_trans _ (HB [] 1 1 7 (repeat (1, 2) 3 ++ (2, 2) :: (3, 2) :: (1, 1) :: repeat (1, 2) 34 ++ (187, 2) :: (1, 1) :: repeat (1, 2) 569 ++ (24959, 2) :: (1, 1) :: repeat (1, 2) 50438 ++ (27674, 2) :: (1, 1) :: repeat (1, 2) 323288 ++ w) 1)).
  {
    apply (hsteps_step _ (HB [] 1 1 7 (repeat (1, 2) 3 ++ (2, 2) :: (3, 2) :: (1, 1) :: repeat (1, 2) 34 ++ (187, 2) :: (1, 1) :: repeat (1, 2) 569 ++ (24959, 2) :: (1, 1) :: repeat (1, 2) 50438 ++ (27674, 2) :: (1, 1) :: repeat (1, 2) 323288 ++ w) 1)); [apply hPUSHX | apply hsteps_refl].
  }
  (* step 49: M pop12 (3,) *)
  apply (hsteps_trans _ (HB [] 4 1 13 ((2, 2) :: (3, 2) :: (1, 1) :: repeat (1, 2) 34 ++ (187, 2) :: (1, 1) :: repeat (1, 2) 569 ++ (24959, 2) :: (1, 1) :: repeat (1, 2) 50438 ++ (27674, 2) :: (1, 1) :: repeat (1, 2) 323288 ++ w) 1)).
  {
    apply (pop12 3 [] 1 7 ((2, 2) :: (3, 2) :: (1, 1) :: repeat (1, 2) 34 ++ (187, 2) :: (1, 1) :: repeat (1, 2) 569 ++ (24959, 2) :: (1, 1) :: repeat (1, 2) 50438 ++ (27674, 2) :: (1, 1) :: repeat (1, 2) 323288 ++ w) 1); closearith.
  }
  (* step 50: P TUP2_1 *)
  apply (hsteps_trans _ (HC [5] 13 1 2 (repeat (1, 2) 1 ++ (1, 1) :: repeat (1, 2) 34 ++ (187, 2) :: (1, 1) :: repeat (1, 2) 569 ++ (24959, 2) :: (1, 1) :: repeat (1, 2) 50438 ++ (27674, 2) :: (1, 1) :: repeat (1, 2) 323288 ++ w) 1)).
  {
    replace (repeat (1, 2) 1 ++ (1, 1) :: repeat (1, 2) 34 ++ (187, 2) :: (1, 1) :: repeat (1, 2) 569 ++ (24959, 2) :: (1, 1) :: repeat (1, 2) 50438 ++ (27674, 2) :: (1, 1) :: repeat (1, 2) 323288 ++ w) with ((3 - 2, 2) :: (1, 1) :: repeat (1, 2) 34 ++ (187, 2) :: (1, 1) :: repeat (1, 2) 569 ++ (24959, 2) :: (1, 1) :: repeat (1, 2) 50438 ++ (27674, 2) :: (1, 1) :: repeat (1, 2) 323288 ++ w) by sec_eq.
    apply (sTUP2_1 [] 4 12 3 ((1, 1) :: repeat (1, 2) 34 ++ (187, 2) :: (1, 1) :: repeat (1, 2) 569 ++ (24959, 2) :: (1, 1) :: repeat (1, 2) 50438 ++ (27674, 2) :: (1, 1) :: repeat (1, 2) 323288 ++ w) 1); closearith.
  }
  (* step 51: P TDN *)
  apply (hsteps_trans _ (HB [5] 13 1 4 (repeat (1, 2) 1 ++ (1, 1) :: repeat (1, 2) 34 ++ (187, 2) :: (1, 1) :: repeat (1, 2) 569 ++ (24959, 2) :: (1, 1) :: repeat (1, 2) 50438 ++ (27674, 2) :: (1, 1) :: repeat (1, 2) 323288 ++ w) 1)).
  {
    apply (sTDN [5] 13 (repeat (1, 2) 1 ++ (1, 1) :: repeat (1, 2) 34 ++ (187, 2) :: (1, 1) :: repeat (1, 2) 569 ++ (24959, 2) :: (1, 1) :: repeat (1, 2) 50438 ++ (27674, 2) :: (1, 1) :: repeat (1, 2) 323288 ++ w) 1).
  }
  (* step 52: M pop12 (1,) *)
  apply (hsteps_trans _ (HB [5] 14 1 6 ((1, 1) :: repeat (1, 2) 34 ++ (187, 2) :: (1, 1) :: repeat (1, 2) 569 ++ (24959, 2) :: (1, 1) :: repeat (1, 2) 50438 ++ (27674, 2) :: (1, 1) :: repeat (1, 2) 323288 ++ w) 1)).
  {
    apply (pop12 1 [5] 13 4 ((1, 1) :: repeat (1, 2) 34 ++ (187, 2) :: (1, 1) :: repeat (1, 2) 569 ++ (24959, 2) :: (1, 1) :: repeat (1, 2) 50438 ++ (27674, 2) :: (1, 1) :: repeat (1, 2) 323288 ++ w) 1); closearith.
  }
  (* step 53: P POP *)
  apply (hsteps_trans _ (HB [5] 15 1 7 (repeat (1, 2) 34 ++ (187, 2) :: (1, 1) :: repeat (1, 2) 569 ++ (24959, 2) :: (1, 1) :: repeat (1, 2) 50438 ++ (27674, 2) :: (1, 1) :: repeat (1, 2) 323288 ++ w) 1)).
  {
    apply (sPOP1 [5] 14 6 (repeat (1, 2) 34 ++ (187, 2) :: (1, 1) :: repeat (1, 2) 569 ++ (24959, 2) :: (1, 1) :: repeat (1, 2) 50438 ++ (27674, 2) :: (1, 1) :: repeat (1, 2) 323288 ++ w) 1); closearith.
  }
  (* step 54: M pop12 (34,) *)
  apply (hsteps_trans _ (HB [5] 49 1 75 ((187, 2) :: (1, 1) :: repeat (1, 2) 569 ++ (24959, 2) :: (1, 1) :: repeat (1, 2) 50438 ++ (27674, 2) :: (1, 1) :: repeat (1, 2) 323288 ++ w) 1)).
  {
    apply (pop12 34 [5] 15 7 ((187, 2) :: (1, 1) :: repeat (1, 2) 569 ++ (24959, 2) :: (1, 1) :: repeat (1, 2) 50438 ++ (27674, 2) :: (1, 1) :: repeat (1, 2) 323288 ++ w) 1); closearith.
  }
  (* step 55: sTUP *)
  apply (hsteps_trans _ (HC [5] 49 74 2 ((185, 2) :: (1, 1) :: repeat (1, 2) 569 ++ (24959, 2) :: (1, 1) :: repeat (1, 2) 50438 ++ (27674, 2) :: (1, 1) :: repeat (1, 2) 323288 ++ w) 1)).
  {
    replace ((185, 2) :: (1, 1) :: repeat (1, 2) 569 ++ (24959, 2) :: (1, 1) :: repeat (1, 2) 50438 ++ (27674, 2) :: (1, 1) :: repeat (1, 2) 323288 ++ w) with ((187 - 2, 2) :: (1, 1) :: repeat (1, 2) 569 ++ (24959, 2) :: (1, 1) :: repeat (1, 2) 50438 ++ (27674, 2) :: (1, 1) :: repeat (1, 2) 323288 ++ w) by sec_eq.
    apply (sTUP [5] 49 75 187 2 ((1, 1) :: repeat (1, 2) 569 ++ (24959, 2) :: (1, 1) :: repeat (1, 2) 50438 ++ (27674, 2) :: (1, 1) :: repeat (1, 2) 323288 ++ w) 1); closearith.
  }
  (* step 56: hGRIND_even 35 *)
  apply (hGRIND_even 35 [5] 48 ((185, 2) :: (1, 1) :: repeat (1, 2) 569 ++ (24959, 2) :: (1, 1) :: repeat (1, 2) 50438 ++ (27674, 2) :: (1, 1) :: repeat (1, 2) 323288 ++ w) 1); closearith.
Qed.

(* CASCADE53b: steps 57-112 of the CASCADE53 chain. *)
Lemma CASCADE53b : forall w,
  hsteps (HB [5] 48 1 74 ((2, 2) :: (185, 2) :: (1, 1) :: repeat (1, 2) 569 ++ (24959, 2) :: (1, 1) :: repeat (1, 2) 50438 ++ (27674, 2) :: (1, 1) :: repeat (1, 2) 323288 ++ w) 1)
         (HB [0] 3 1 4 ((14, 2) :: (1, 1) :: repeat (1, 2) 112 ++ (503, 2) :: (1, 1) :: repeat (1, 2) 1174 ++ (22609, 2) :: (1, 1) :: repeat (1, 2) 50438 ++ (27674, 2) :: (1, 1) :: repeat (1, 2) 323288 ++ w) 1).
Proof.
  intro w.
  (* step 57: P TUP2_1 *)
  apply (hsteps_trans _ (HC [49; 5] 74 1 2 ((183, 2) :: (1, 1) :: repeat (1, 2) 569 ++ (24959, 2) :: (1, 1) :: repeat (1, 2) 50438 ++ (27674, 2) :: (1, 1) :: repeat (1, 2) 323288 ++ w) 1)).
  {
    replace ((183, 2) :: (1, 1) :: repeat (1, 2) 569 ++ (24959, 2) :: (1, 1) :: repeat (1, 2) 50438 ++ (27674, 2) :: (1, 1) :: repeat (1, 2) 323288 ++ w) with ((185 - 2, 2) :: (1, 1) :: repeat (1, 2) 569 ++ (24959, 2) :: (1, 1) :: repeat (1, 2) 50438 ++ (27674, 2) :: (1, 1) :: repeat (1, 2) 323288 ++ w) by sec_eq.
    apply (sTUP2_1 [5] 48 73 185 ((1, 1) :: repeat (1, 2) 569 ++ (24959, 2) :: (1, 1) :: repeat (1, 2) 50438 ++ (27674, 2) :: (1, 1) :: repeat (1, 2) 323288 ++ w) 1); closearith.
  }
  (* step 58: P TDN *)
  apply (hsteps_trans _ (HB [49; 5] 74 1 4 ((183, 2) :: (1, 1) :: repeat (1, 2) 569 ++ (24959, 2) :: (1, 1) :: repeat (1, 2) 50438 ++ (27674, 2) :: (1, 1) :: repeat (1, 2) 323288 ++ w) 1)).
  {
    apply (sTDN [49; 5] 74 ((183, 2) :: (1, 1) :: repeat (1, 2) 569 ++ (24959, 2) :: (1, 1) :: repeat (1, 2) 50438 ++ (27674, 2) :: (1, 1) :: repeat (1, 2) 323288 ++ w) 1).
  }
  (* step 59: sTUP *)
  apply (hsteps_trans _ (HC [49; 5] 74 3 2 ((181, 2) :: (1, 1) :: repeat (1, 2) 569 ++ (24959, 2) :: (1, 1) :: repeat (1, 2) 50438 ++ (27674, 2) :: (1, 1) :: repeat (1, 2) 323288 ++ w) 1)).
  {
    replace ((181, 2) :: (1, 1) :: repeat (1, 2) 569 ++ (24959, 2) :: (1, 1) :: repeat (1, 2) 50438 ++ (27674, 2) :: (1, 1) :: repeat (1, 2) 323288 ++ w) with ((183 - 2, 2) :: (1, 1) :: repeat (1, 2) 569 ++ (24959, 2) :: (1, 1) :: repeat (1, 2) 50438 ++ (27674, 2) :: (1, 1) :: repeat (1, 2) 323288 ++ w) by sec_eq.
    apply (sTUP [49; 5] 74 4 183 2 ((1, 1) :: repeat (1, 2) 569 ++ (24959, 2) :: (1, 1) :: repeat (1, 2) 50438 ++ (27674, 2) :: (1, 1) :: repeat (1, 2) 323288 ++ w) 1); closearith.
  }
  (* step 60: DIPGRIND 74 33 *)
  apply (hsteps_trans _ (HC [49; 5] 0 3 2 (repeat (1, 2) 74 ++ (33, 2) :: (1, 1) :: repeat (1, 2) 569 ++ (24959, 2) :: (1, 1) :: repeat (1, 2) 50438 ++ (27674, 2) :: (1, 1) :: repeat (1, 2) 323288 ++ w) 1)).
  {
    apply (DIPGRIND 74 33 [49; 5] ((1, 1) :: repeat (1, 2) 569 ++ (24959, 2) :: (1, 1) :: repeat (1, 2) 50438 ++ (27674, 2) :: (1, 1) :: repeat (1, 2) 323288 ++ w) 1); closearith.
  }
  (* step 61: P PX2A *)
  apply (hsteps_trans _ (HC [] 4 47 2 ((1, 1) :: repeat (1, 2) 76 ++ (33, 2) :: (1, 1) :: repeat (1, 2) 569 ++ (24959, 2) :: (1, 1) :: repeat (1, 2) 50438 ++ (27674, 2) :: (1, 1) :: repeat (1, 2) 323288 ++ w) 1)).
  {
    apply (hsteps_step _ (HC [] 4 47 2 ((1, 1) :: repeat (1, 2) 76 ++ (33, 2) :: (1, 1) :: repeat (1, 2) 569 ++ (24959, 2) :: (1, 1) :: repeat (1, 2) 50438 ++ (27674, 2) :: (1, 1) :: repeat (1, 2) 323288 ++ w) 1)); [apply hPX2A | apply hsteps_refl].
  }
  (* step 62: P PUSH *)
  apply (hsteps_trans _ (HC [] 3 1 2 ((45, 2) :: (1, 1) :: repeat (1, 2) 76 ++ (33, 2) :: (1, 1) :: repeat (1, 2) 569 ++ (24959, 2) :: (1, 1) :: repeat (1, 2) 50438 ++ (27674, 2) :: (1, 1) :: repeat (1, 2) 323288 ++ w) 1)).
  {
    replace ((45, 2) :: (1, 1) :: repeat (1, 2) 76 ++ (33, 2) :: (1, 1) :: repeat (1, 2) 569 ++ (24959, 2) :: (1, 1) :: repeat (1, 2) 50438 ++ (27674, 2) :: (1, 1) :: repeat (1, 2) 323288 ++ w) with ((47 - 2, 2) :: (1, 1) :: repeat (1, 2) 76 ++ (33, 2) :: (1, 1) :: repeat (1, 2) 569 ++ (24959, 2) :: (1, 1) :: repeat (1, 2) 50438 ++ (27674, 2) :: (1, 1) :: repeat (1, 2) 323288 ++ w) by sec_eq.
    apply (sPUSH [] 3 47 ((1, 1) :: repeat (1, 2) 76 ++ (33, 2) :: (1, 1) :: repeat (1, 2) 569 ++ (24959, 2) :: (1, 1) :: repeat (1, 2) 50438 ++ (27674, 2) :: (1, 1) :: repeat (1, 2) 323288 ++ w) 1); closearith.
  }
  (* step 63: P TDN *)
  apply (hsteps_trans _ (HB [] 3 1 4 ((45, 2) :: (1, 1) :: repeat (1, 2) 76 ++ (33, 2) :: (1, 1) :: repeat (1, 2) 569 ++ (24959, 2) :: (1, 1) :: repeat (1, 2) 50438 ++ (27674, 2) :: (1, 1) :: repeat (1, 2) 323288 ++ w) 1)).
  {
    apply (sTDN [] 3 ((45, 2) :: (1, 1) :: repeat (1, 2) 76 ++ (33, 2) :: (1, 1) :: repeat (1, 2) 569 ++ (24959, 2) :: (1, 1) :: repeat (1, 2) 50438 ++ (27674, 2) :: (1, 1) :: repeat (1, 2) 323288 ++ w) 1).
  }
  (* step 64: sTUP *)
  apply (hsteps_trans _ (HC [] 3 3 2 ((43, 2) :: (1, 1) :: repeat (1, 2) 76 ++ (33, 2) :: (1, 1) :: repeat (1, 2) 569 ++ (24959, 2) :: (1, 1) :: repeat (1, 2) 50438 ++ (27674, 2) :: (1, 1) :: repeat (1, 2) 323288 ++ w) 1)).
  {
    replace ((43, 2) :: (1, 1) :: repeat (1, 2) 76 ++ (33, 2) :: (1, 1) :: repeat (1, 2) 569 ++ (24959, 2) :: (1, 1) :: repeat (1, 2) 50438 ++ (27674, 2) :: (1, 1) :: repeat (1, 2) 323288 ++ w) with ((45 - 2, 2) :: (1, 1) :: repeat (1, 2) 76 ++ (33, 2) :: (1, 1) :: repeat (1, 2) 569 ++ (24959, 2) :: (1, 1) :: repeat (1, 2) 50438 ++ (27674, 2) :: (1, 1) :: repeat (1, 2) 323288 ++ w) by sec_eq.
    apply (sTUP [] 3 4 45 2 ((1, 1) :: repeat (1, 2) 76 ++ (33, 2) :: (1, 1) :: repeat (1, 2) 569 ++ (24959, 2) :: (1, 1) :: repeat (1, 2) 50438 ++ (27674, 2) :: (1, 1) :: repeat (1, 2) 323288 ++ w) 1); closearith.
  }
  (* step 65: DIPGRIND 3 37 *)
  apply (hsteps_trans _ (HC [] 0 3 2 (repeat (1, 2) 3 ++ (37, 2) :: (1, 1) :: repeat (1, 2) 76 ++ (33, 2) :: (1, 1) :: repeat (1, 2) 569 ++ (24959, 2) :: (1, 1) :: repeat (1, 2) 50438 ++ (27674, 2) :: (1, 1) :: repeat (1, 2) 323288 ++ w) 1)).
  {
    apply (DIPGRIND 3 37 [] ((1, 1) :: repeat (1, 2) 76 ++ (33, 2) :: (1, 1) :: repeat (1, 2) 569 ++ (24959, 2) :: (1, 1) :: repeat (1, 2) 50438 ++ (27674, 2) :: (1, 1) :: repeat (1, 2) 323288 ++ w) 1); closearith.
  }
  (* step 66: P PUSHX *)
  apply (hsteps_trans _ (HB [] 1 1 7 (repeat (1, 2) 3 ++ (37, 2) :: (1, 1) :: repeat (1, 2) 76 ++ (33, 2) :: (1, 1) :: repeat (1, 2) 569 ++ (24959, 2) :: (1, 1) :: repeat (1, 2) 50438 ++ (27674, 2) :: (1, 1) :: repeat (1, 2) 323288 ++ w) 1)).
  {
    apply (hsteps_step _ (HB [] 1 1 7 (repeat (1, 2) 3 ++ (37, 2) :: (1, 1) :: repeat (1, 2) 76 ++ (33, 2) :: (1, 1) :: repeat (1, 2) 569 ++ (24959, 2) :: (1, 1) :: repeat (1, 2) 50438 ++ (27674, 2) :: (1, 1) :: repeat (1, 2) 323288 ++ w) 1)); [apply hPUSHX | apply hsteps_refl].
  }
  (* step 67: M pop12 (3,) *)
  apply (hsteps_trans _ (HB [] 4 1 13 ((37, 2) :: (1, 1) :: repeat (1, 2) 76 ++ (33, 2) :: (1, 1) :: repeat (1, 2) 569 ++ (24959, 2) :: (1, 1) :: repeat (1, 2) 50438 ++ (27674, 2) :: (1, 1) :: repeat (1, 2) 323288 ++ w) 1)).
  {
    apply (pop12 3 [] 1 7 ((37, 2) :: (1, 1) :: repeat (1, 2) 76 ++ (33, 2) :: (1, 1) :: repeat (1, 2) 569 ++ (24959, 2) :: (1, 1) :: repeat (1, 2) 50438 ++ (27674, 2) :: (1, 1) :: repeat (1, 2) 323288 ++ w) 1); closearith.
  }
  (* step 68: sTUP *)
  apply (hsteps_trans _ (HC [] 4 12 2 ((35, 2) :: (1, 1) :: repeat (1, 2) 76 ++ (33, 2) :: (1, 1) :: repeat (1, 2) 569 ++ (24959, 2) :: (1, 1) :: repeat (1, 2) 50438 ++ (27674, 2) :: (1, 1) :: repeat (1, 2) 323288 ++ w) 1)).
  {
    replace ((35, 2) :: (1, 1) :: repeat (1, 2) 76 ++ (33, 2) :: (1, 1) :: repeat (1, 2) 569 ++ (24959, 2) :: (1, 1) :: repeat (1, 2) 50438 ++ (27674, 2) :: (1, 1) :: repeat (1, 2) 323288 ++ w) with ((37 - 2, 2) :: (1, 1) :: repeat (1, 2) 76 ++ (33, 2) :: (1, 1) :: repeat (1, 2) 569 ++ (24959, 2) :: (1, 1) :: repeat (1, 2) 50438 ++ (27674, 2) :: (1, 1) :: repeat (1, 2) 323288 ++ w) by sec_eq.
    apply (sTUP [] 4 13 37 2 ((1, 1) :: repeat (1, 2) 76 ++ (33, 2) :: (1, 1) :: repeat (1, 2) 569 ++ (24959, 2) :: (1, 1) :: repeat (1, 2) 50438 ++ (27674, 2) :: (1, 1) :: repeat (1, 2) 323288 ++ w) 1); closearith.
  }
  (* step 69: P PUSH *)
  apply (hsteps_trans _ (HC [] 3 1 2 ((10, 2) :: (35, 2) :: (1, 1) :: repeat (1, 2) 76 ++ (33, 2) :: (1, 1) :: repeat (1, 2) 569 ++ (24959, 2) :: (1, 1) :: repeat (1, 2) 50438 ++ (27674, 2) :: (1, 1) :: repeat (1, 2) 323288 ++ w) 1)).
  {
    replace ((10, 2) :: (35, 2) :: (1, 1) :: repeat (1, 2) 76 ++ (33, 2) :: (1, 1) :: repeat (1, 2) 569 ++ (24959, 2) :: (1, 1) :: repeat (1, 2) 50438 ++ (27674, 2) :: (1, 1) :: repeat (1, 2) 323288 ++ w) with ((12 - 2, 2) :: (35, 2) :: (1, 1) :: repeat (1, 2) 76 ++ (33, 2) :: (1, 1) :: repeat (1, 2) 569 ++ (24959, 2) :: (1, 1) :: repeat (1, 2) 50438 ++ (27674, 2) :: (1, 1) :: repeat (1, 2) 323288 ++ w) by sec_eq.
    apply (sPUSH [] 3 12 ((35, 2) :: (1, 1) :: repeat (1, 2) 76 ++ (33, 2) :: (1, 1) :: repeat (1, 2) 569 ++ (24959, 2) :: (1, 1) :: repeat (1, 2) 50438 ++ (27674, 2) :: (1, 1) :: repeat (1, 2) 323288 ++ w) 1); closearith.
  }
  (* step 70: P TDN *)
  apply (hsteps_trans _ (HB [] 3 1 4 ((10, 2) :: (35, 2) :: (1, 1) :: repeat (1, 2) 76 ++ (33, 2) :: (1, 1) :: repeat (1, 2) 569 ++ (24959, 2) :: (1, 1) :: repeat (1, 2) 50438 ++ (27674, 2) :: (1, 1) :: repeat (1, 2) 323288 ++ w) 1)).
  {
    apply (sTDN [] 3 ((10, 2) :: (35, 2) :: (1, 1) :: repeat (1, 2) 76 ++ (33, 2) :: (1, 1) :: repeat (1, 2) 569 ++ (24959, 2) :: (1, 1) :: repeat (1, 2) 50438 ++ (27674, 2) :: (1, 1) :: repeat (1, 2) 323288 ++ w) 1).
  }
  (* step 71: sTUP *)
  apply (hsteps_trans _ (HC [] 3 3 2 ((8, 2) :: (35, 2) :: (1, 1) :: repeat (1, 2) 76 ++ (33, 2) :: (1, 1) :: repeat (1, 2) 569 ++ (24959, 2) :: (1, 1) :: repeat (1, 2) 50438 ++ (27674, 2) :: (1, 1) :: repeat (1, 2) 323288 ++ w) 1)).
  {
    replace ((8, 2) :: (35, 2) :: (1, 1) :: repeat (1, 2) 76 ++ (33, 2) :: (1, 1) :: repeat (1, 2) 569 ++ (24959, 2) :: (1, 1) :: repeat (1, 2) 50438 ++ (27674, 2) :: (1, 1) :: repeat (1, 2) 323288 ++ w) with ((10 - 2, 2) :: (35, 2) :: (1, 1) :: repeat (1, 2) 76 ++ (33, 2) :: (1, 1) :: repeat (1, 2) 569 ++ (24959, 2) :: (1, 1) :: repeat (1, 2) 50438 ++ (27674, 2) :: (1, 1) :: repeat (1, 2) 323288 ++ w) by sec_eq.
    apply (sTUP [] 3 4 10 2 ((35, 2) :: (1, 1) :: repeat (1, 2) 76 ++ (33, 2) :: (1, 1) :: repeat (1, 2) 569 ++ (24959, 2) :: (1, 1) :: repeat (1, 2) 50438 ++ (27674, 2) :: (1, 1) :: repeat (1, 2) 323288 ++ w) 1); closearith.
  }
  (* step 72: DIPGRIND 3 2 *)
  apply (hsteps_trans _ (HC [] 0 3 2 (repeat (1, 2) 3 ++ (2, 2) :: (35, 2) :: (1, 1) :: repeat (1, 2) 76 ++ (33, 2) :: (1, 1) :: repeat (1, 2) 569 ++ (24959, 2) :: (1, 1) :: repeat (1, 2) 50438 ++ (27674, 2) :: (1, 1) :: repeat (1, 2) 323288 ++ w) 1)).
  {
    apply (DIPGRIND 3 2 [] ((35, 2) :: (1, 1) :: repeat (1, 2) 76 ++ (33, 2) :: (1, 1) :: repeat (1, 2) 569 ++ (24959, 2) :: (1, 1) :: repeat (1, 2) 50438 ++ (27674, 2) :: (1, 1) :: repeat (1, 2) 323288 ++ w) 1); closearith.
  }
  (* step 73: P PUSHX *)
  apply (hsteps_trans _ (HB [] 1 1 7 (repeat (1, 2) 3 ++ (2, 2) :: (35, 2) :: (1, 1) :: repeat (1, 2) 76 ++ (33, 2) :: (1, 1) :: repeat (1, 2) 569 ++ (24959, 2) :: (1, 1) :: repeat (1, 2) 50438 ++ (27674, 2) :: (1, 1) :: repeat (1, 2) 323288 ++ w) 1)).
  {
    apply (hsteps_step _ (HB [] 1 1 7 (repeat (1, 2) 3 ++ (2, 2) :: (35, 2) :: (1, 1) :: repeat (1, 2) 76 ++ (33, 2) :: (1, 1) :: repeat (1, 2) 569 ++ (24959, 2) :: (1, 1) :: repeat (1, 2) 50438 ++ (27674, 2) :: (1, 1) :: repeat (1, 2) 323288 ++ w) 1)); [apply hPUSHX | apply hsteps_refl].
  }
  (* step 74: M pop12 (3,) *)
  apply (hsteps_trans _ (HB [] 4 1 13 ((2, 2) :: (35, 2) :: (1, 1) :: repeat (1, 2) 76 ++ (33, 2) :: (1, 1) :: repeat (1, 2) 569 ++ (24959, 2) :: (1, 1) :: repeat (1, 2) 50438 ++ (27674, 2) :: (1, 1) :: repeat (1, 2) 323288 ++ w) 1)).
  {
    apply (pop12 3 [] 1 7 ((2, 2) :: (35, 2) :: (1, 1) :: repeat (1, 2) 76 ++ (33, 2) :: (1, 1) :: repeat (1, 2) 569 ++ (24959, 2) :: (1, 1) :: repeat (1, 2) 50438 ++ (27674, 2) :: (1, 1) :: repeat (1, 2) 323288 ++ w) 1); closearith.
  }
  (* step 75: P TUP2_1 *)
  apply (hsteps_trans _ (HC [5] 13 1 2 ((33, 2) :: (1, 1) :: repeat (1, 2) 76 ++ (33, 2) :: (1, 1) :: repeat (1, 2) 569 ++ (24959, 2) :: (1, 1) :: repeat (1, 2) 50438 ++ (27674, 2) :: (1, 1) :: repeat (1, 2) 323288 ++ w) 1)).
  {
    replace ((33, 2) :: (1, 1) :: repeat (1, 2) 76 ++ (33, 2) :: (1, 1) :: repeat (1, 2) 569 ++ (24959, 2) :: (1, 1) :: repeat (1, 2) 50438 ++ (27674, 2) :: (1, 1) :: repeat (1, 2) 323288 ++ w) with ((35 - 2, 2) :: (1, 1) :: repeat (1, 2) 76 ++ (33, 2) :: (1, 1) :: repeat (1, 2) 569 ++ (24959, 2) :: (1, 1) :: repeat (1, 2) 50438 ++ (27674, 2) :: (1, 1) :: repeat (1, 2) 323288 ++ w) by sec_eq.
    apply (sTUP2_1 [] 4 12 35 ((1, 1) :: repeat (1, 2) 76 ++ (33, 2) :: (1, 1) :: repeat (1, 2) 569 ++ (24959, 2) :: (1, 1) :: repeat (1, 2) 50438 ++ (27674, 2) :: (1, 1) :: repeat (1, 2) 323288 ++ w) 1); closearith.
  }
  (* step 76: P TDN *)
  apply (hsteps_trans _ (HB [5] 13 1 4 ((33, 2) :: (1, 1) :: repeat (1, 2) 76 ++ (33, 2) :: (1, 1) :: repeat (1, 2) 569 ++ (24959, 2) :: (1, 1) :: repeat (1, 2) 50438 ++ (27674, 2) :: (1, 1) :: repeat (1, 2) 323288 ++ w) 1)).
  {
    apply (sTDN [5] 13 ((33, 2) :: (1, 1) :: repeat (1, 2) 76 ++ (33, 2) :: (1, 1) :: repeat (1, 2) 569 ++ (24959, 2) :: (1, 1) :: repeat (1, 2) 50438 ++ (27674, 2) :: (1, 1) :: repeat (1, 2) 323288 ++ w) 1).
  }
  (* step 77: sTUP *)
  apply (hsteps_trans _ (HC [5] 13 3 2 ((31, 2) :: (1, 1) :: repeat (1, 2) 76 ++ (33, 2) :: (1, 1) :: repeat (1, 2) 569 ++ (24959, 2) :: (1, 1) :: repeat (1, 2) 50438 ++ (27674, 2) :: (1, 1) :: repeat (1, 2) 323288 ++ w) 1)).
  {
    replace ((31, 2) :: (1, 1) :: repeat (1, 2) 76 ++ (33, 2) :: (1, 1) :: repeat (1, 2) 569 ++ (24959, 2) :: (1, 1) :: repeat (1, 2) 50438 ++ (27674, 2) :: (1, 1) :: repeat (1, 2) 323288 ++ w) with ((33 - 2, 2) :: (1, 1) :: repeat (1, 2) 76 ++ (33, 2) :: (1, 1) :: repeat (1, 2) 569 ++ (24959, 2) :: (1, 1) :: repeat (1, 2) 50438 ++ (27674, 2) :: (1, 1) :: repeat (1, 2) 323288 ++ w) by sec_eq.
    apply (sTUP [5] 13 4 33 2 ((1, 1) :: repeat (1, 2) 76 ++ (33, 2) :: (1, 1) :: repeat (1, 2) 569 ++ (24959, 2) :: (1, 1) :: repeat (1, 2) 50438 ++ (27674, 2) :: (1, 1) :: repeat (1, 2) 323288 ++ w) 1); closearith.
  }
  (* step 78: DIPGRIND 13 5 *)
  apply (hsteps_trans _ (HC [5] 0 3 2 (repeat (1, 2) 13 ++ (5, 2) :: (1, 1) :: repeat (1, 2) 76 ++ (33, 2) :: (1, 1) :: repeat (1, 2) 569 ++ (24959, 2) :: (1, 1) :: repeat (1, 2) 50438 ++ (27674, 2) :: (1, 1) :: repeat (1, 2) 323288 ++ w) 1)).
  {
    apply (DIPGRIND 13 5 [5] ((1, 1) :: repeat (1, 2) 76 ++ (33, 2) :: (1, 1) :: repeat (1, 2) 569 ++ (24959, 2) :: (1, 1) :: repeat (1, 2) 50438 ++ (27674, 2) :: (1, 1) :: repeat (1, 2) 323288 ++ w) 1); closearith.
  }
  (* step 79: P PX2Bgen *)
  apply (hsteps_trans _ (HB [0] 3 1 2 (repeat (1, 2) 1 ++ (1, 1) :: repeat (1, 2) 15 ++ (5, 2) :: (1, 1) :: repeat (1, 2) 76 ++ (33, 2) :: (1, 1) :: repeat (1, 2) 569 ++ (24959, 2) :: (1, 1) :: repeat (1, 2) 50438 ++ (27674, 2) :: (1, 1) :: repeat (1, 2) 323288 ++ w) 1)).
  {
    apply (hsteps_step _ (HB [0] 3 1 2 (repeat (1, 2) 1 ++ (1, 1) :: repeat (1, 2) 15 ++ (5, 2) :: (1, 1) :: repeat (1, 2) 76 ++ (33, 2) :: (1, 1) :: repeat (1, 2) 569 ++ (24959, 2) :: (1, 1) :: repeat (1, 2) 50438 ++ (27674, 2) :: (1, 1) :: repeat (1, 2) 323288 ++ w) 1)); [apply hPX2Bgen | apply hsteps_refl].
  }
  (* step 80: M pop12 (1,) *)
  apply (hsteps_trans _ (HB [0] 4 1 4 ((1, 1) :: repeat (1, 2) 15 ++ (5, 2) :: (1, 1) :: repeat (1, 2) 76 ++ (33, 2) :: (1, 1) :: repeat (1, 2) 569 ++ (24959, 2) :: (1, 1) :: repeat (1, 2) 50438 ++ (27674, 2) :: (1, 1) :: repeat (1, 2) 323288 ++ w) 1)).
  {
    apply (pop12 1 [0] 3 2 ((1, 1) :: repeat (1, 2) 15 ++ (5, 2) :: (1, 1) :: repeat (1, 2) 76 ++ (33, 2) :: (1, 1) :: repeat (1, 2) 569 ++ (24959, 2) :: (1, 1) :: repeat (1, 2) 50438 ++ (27674, 2) :: (1, 1) :: repeat (1, 2) 323288 ++ w) 1); closearith.
  }
  (* step 81: P POP *)
  apply (hsteps_trans _ (HB [0] 5 1 5 (repeat (1, 2) 15 ++ (5, 2) :: (1, 1) :: repeat (1, 2) 76 ++ (33, 2) :: (1, 1) :: repeat (1, 2) 569 ++ (24959, 2) :: (1, 1) :: repeat (1, 2) 50438 ++ (27674, 2) :: (1, 1) :: repeat (1, 2) 323288 ++ w) 1)).
  {
    apply (sPOP1 [0] 4 4 (repeat (1, 2) 15 ++ (5, 2) :: (1, 1) :: repeat (1, 2) 76 ++ (33, 2) :: (1, 1) :: repeat (1, 2) 569 ++ (24959, 2) :: (1, 1) :: repeat (1, 2) 50438 ++ (27674, 2) :: (1, 1) :: repeat (1, 2) 323288 ++ w) 1); closearith.
  }
  (* step 82: M pop12 (15,) *)
  apply (hsteps_trans _ (HB [0] 20 1 35 ((5, 2) :: (1, 1) :: repeat (1, 2) 76 ++ (33, 2) :: (1, 1) :: repeat (1, 2) 569 ++ (24959, 2) :: (1, 1) :: repeat (1, 2) 50438 ++ (27674, 2) :: (1, 1) :: repeat (1, 2) 323288 ++ w) 1)).
  {
    apply (pop12 15 [0] 5 5 ((5, 2) :: (1, 1) :: repeat (1, 2) 76 ++ (33, 2) :: (1, 1) :: repeat (1, 2) 569 ++ (24959, 2) :: (1, 1) :: repeat (1, 2) 50438 ++ (27674, 2) :: (1, 1) :: repeat (1, 2) 323288 ++ w) 1); closearith.
  }
  (* step 83: sTUP *)
  apply (hsteps_trans _ (HC [0] 20 34 2 ((3, 2) :: (1, 1) :: repeat (1, 2) 76 ++ (33, 2) :: (1, 1) :: repeat (1, 2) 569 ++ (24959, 2) :: (1, 1) :: repeat (1, 2) 50438 ++ (27674, 2) :: (1, 1) :: repeat (1, 2) 323288 ++ w) 1)).
  {
    replace ((3, 2) :: (1, 1) :: repeat (1, 2) 76 ++ (33, 2) :: (1, 1) :: repeat (1, 2) 569 ++ (24959, 2) :: (1, 1) :: repeat (1, 2) 50438 ++ (27674, 2) :: (1, 1) :: repeat (1, 2) 323288 ++ w) with ((5 - 2, 2) :: (1, 1) :: repeat (1, 2) 76 ++ (33, 2) :: (1, 1) :: repeat (1, 2) 569 ++ (24959, 2) :: (1, 1) :: repeat (1, 2) 50438 ++ (27674, 2) :: (1, 1) :: repeat (1, 2) 323288 ++ w) by sec_eq.
    apply (sTUP [0] 20 35 5 2 ((1, 1) :: repeat (1, 2) 76 ++ (33, 2) :: (1, 1) :: repeat (1, 2) 569 ++ (24959, 2) :: (1, 1) :: repeat (1, 2) 50438 ++ (27674, 2) :: (1, 1) :: repeat (1, 2) 323288 ++ w) 1); closearith.
  }
  (* step 84: hGRIND_even 15 *)
  apply (hsteps_trans _ (HB [0] 19 1 34 ((2, 2) :: (3, 2) :: (1, 1) :: repeat (1, 2) 76 ++ (33, 2) :: (1, 1) :: repeat (1, 2) 569 ++ (24959, 2) :: (1, 1) :: repeat (1, 2) 50438 ++ (27674, 2) :: (1, 1) :: repeat (1, 2) 323288 ++ w) 1)).
  {
    apply (hGRIND_even 15 [0] 19 ((3, 2) :: (1, 1) :: repeat (1, 2) 76 ++ (33, 2) :: (1, 1) :: repeat (1, 2) 569 ++ (24959, 2) :: (1, 1) :: repeat (1, 2) 50438 ++ (27674, 2) :: (1, 1) :: repeat (1, 2) 323288 ++ w) 1); closearith.
  }
  (* step 85: P TUP2_1 *)
  apply (hsteps_trans _ (HC [20; 0] 34 1 2 (repeat (1, 2) 1 ++ (1, 1) :: repeat (1, 2) 76 ++ (33, 2) :: (1, 1) :: repeat (1, 2) 569 ++ (24959, 2) :: (1, 1) :: repeat (1, 2) 50438 ++ (27674, 2) :: (1, 1) :: repeat (1, 2) 323288 ++ w) 1)).
  {
    replace (repeat (1, 2) 1 ++ (1, 1) :: repeat (1, 2) 76 ++ (33, 2) :: (1, 1) :: repeat (1, 2) 569 ++ (24959, 2) :: (1, 1) :: repeat (1, 2) 50438 ++ (27674, 2) :: (1, 1) :: repeat (1, 2) 323288 ++ w) with ((3 - 2, 2) :: (1, 1) :: repeat (1, 2) 76 ++ (33, 2) :: (1, 1) :: repeat (1, 2) 569 ++ (24959, 2) :: (1, 1) :: repeat (1, 2) 50438 ++ (27674, 2) :: (1, 1) :: repeat (1, 2) 323288 ++ w) by sec_eq.
    apply (sTUP2_1 [0] 19 33 3 ((1, 1) :: repeat (1, 2) 76 ++ (33, 2) :: (1, 1) :: repeat (1, 2) 569 ++ (24959, 2) :: (1, 1) :: repeat (1, 2) 50438 ++ (27674, 2) :: (1, 1) :: repeat (1, 2) 323288 ++ w) 1); closearith.
  }
  (* step 86: P TDN *)
  apply (hsteps_trans _ (HB [20; 0] 34 1 4 (repeat (1, 2) 1 ++ (1, 1) :: repeat (1, 2) 76 ++ (33, 2) :: (1, 1) :: repeat (1, 2) 569 ++ (24959, 2) :: (1, 1) :: repeat (1, 2) 50438 ++ (27674, 2) :: (1, 1) :: repeat (1, 2) 323288 ++ w) 1)).
  {
    apply (sTDN [20; 0] 34 (repeat (1, 2) 1 ++ (1, 1) :: repeat (1, 2) 76 ++ (33, 2) :: (1, 1) :: repeat (1, 2) 569 ++ (24959, 2) :: (1, 1) :: repeat (1, 2) 50438 ++ (27674, 2) :: (1, 1) :: repeat (1, 2) 323288 ++ w) 1).
  }
  (* step 87: M pop12 (1,) *)
  apply (hsteps_trans _ (HB [20; 0] 35 1 6 ((1, 1) :: repeat (1, 2) 76 ++ (33, 2) :: (1, 1) :: repeat (1, 2) 569 ++ (24959, 2) :: (1, 1) :: repeat (1, 2) 50438 ++ (27674, 2) :: (1, 1) :: repeat (1, 2) 323288 ++ w) 1)).
  {
    apply (pop12 1 [20; 0] 34 4 ((1, 1) :: repeat (1, 2) 76 ++ (33, 2) :: (1, 1) :: repeat (1, 2) 569 ++ (24959, 2) :: (1, 1) :: repeat (1, 2) 50438 ++ (27674, 2) :: (1, 1) :: repeat (1, 2) 323288 ++ w) 1); closearith.
  }
  (* step 88: P POP *)
  apply (hsteps_trans _ (HB [20; 0] 36 1 7 (repeat (1, 2) 76 ++ (33, 2) :: (1, 1) :: repeat (1, 2) 569 ++ (24959, 2) :: (1, 1) :: repeat (1, 2) 50438 ++ (27674, 2) :: (1, 1) :: repeat (1, 2) 323288 ++ w) 1)).
  {
    apply (sPOP1 [20; 0] 35 6 (repeat (1, 2) 76 ++ (33, 2) :: (1, 1) :: repeat (1, 2) 569 ++ (24959, 2) :: (1, 1) :: repeat (1, 2) 50438 ++ (27674, 2) :: (1, 1) :: repeat (1, 2) 323288 ++ w) 1); closearith.
  }
  (* step 89: M pop12 (76,) *)
  apply (hsteps_trans _ (HB [20; 0] 112 1 159 ((33, 2) :: (1, 1) :: repeat (1, 2) 569 ++ (24959, 2) :: (1, 1) :: repeat (1, 2) 50438 ++ (27674, 2) :: (1, 1) :: repeat (1, 2) 323288 ++ w) 1)).
  {
    apply (pop12 76 [20; 0] 36 7 ((33, 2) :: (1, 1) :: repeat (1, 2) 569 ++ (24959, 2) :: (1, 1) :: repeat (1, 2) 50438 ++ (27674, 2) :: (1, 1) :: repeat (1, 2) 323288 ++ w) 1); closearith.
  }
  (* step 90: sTUP *)
  apply (hsteps_trans _ (HC [20; 0] 112 158 2 ((31, 2) :: (1, 1) :: repeat (1, 2) 569 ++ (24959, 2) :: (1, 1) :: repeat (1, 2) 50438 ++ (27674, 2) :: (1, 1) :: repeat (1, 2) 323288 ++ w) 1)).
  {
    replace ((31, 2) :: (1, 1) :: repeat (1, 2) 569 ++ (24959, 2) :: (1, 1) :: repeat (1, 2) 50438 ++ (27674, 2) :: (1, 1) :: repeat (1, 2) 323288 ++ w) with ((33 - 2, 2) :: (1, 1) :: repeat (1, 2) 569 ++ (24959, 2) :: (1, 1) :: repeat (1, 2) 50438 ++ (27674, 2) :: (1, 1) :: repeat (1, 2) 323288 ++ w) by sec_eq.
    apply (sTUP [20; 0] 112 159 33 2 ((1, 1) :: repeat (1, 2) 569 ++ (24959, 2) :: (1, 1) :: repeat (1, 2) 50438 ++ (27674, 2) :: (1, 1) :: repeat (1, 2) 323288 ++ w) 1); closearith.
  }
  (* step 91: hGRIND_even 77 *)
  apply (hsteps_trans _ (HB [20; 0] 111 1 158 ((2, 2) :: (31, 2) :: (1, 1) :: repeat (1, 2) 569 ++ (24959, 2) :: (1, 1) :: repeat (1, 2) 50438 ++ (27674, 2) :: (1, 1) :: repeat (1, 2) 323288 ++ w) 1)).
  {
    apply (hGRIND_even 77 [20; 0] 111 ((31, 2) :: (1, 1) :: repeat (1, 2) 569 ++ (24959, 2) :: (1, 1) :: repeat (1, 2) 50438 ++ (27674, 2) :: (1, 1) :: repeat (1, 2) 323288 ++ w) 1); closearith.
  }
  (* step 92: P TUP2_1 *)
  apply (hsteps_trans _ (HC [112; 20; 0] 158 1 2 ((29, 2) :: (1, 1) :: repeat (1, 2) 569 ++ (24959, 2) :: (1, 1) :: repeat (1, 2) 50438 ++ (27674, 2) :: (1, 1) :: repeat (1, 2) 323288 ++ w) 1)).
  {
    replace ((29, 2) :: (1, 1) :: repeat (1, 2) 569 ++ (24959, 2) :: (1, 1) :: repeat (1, 2) 50438 ++ (27674, 2) :: (1, 1) :: repeat (1, 2) 323288 ++ w) with ((31 - 2, 2) :: (1, 1) :: repeat (1, 2) 569 ++ (24959, 2) :: (1, 1) :: repeat (1, 2) 50438 ++ (27674, 2) :: (1, 1) :: repeat (1, 2) 323288 ++ w) by sec_eq.
    apply (sTUP2_1 [20; 0] 111 157 31 ((1, 1) :: repeat (1, 2) 569 ++ (24959, 2) :: (1, 1) :: repeat (1, 2) 50438 ++ (27674, 2) :: (1, 1) :: repeat (1, 2) 323288 ++ w) 1); closearith.
  }
  (* step 93: P TDN *)
  apply (hsteps_trans _ (HB [112; 20; 0] 158 1 4 ((29, 2) :: (1, 1) :: repeat (1, 2) 569 ++ (24959, 2) :: (1, 1) :: repeat (1, 2) 50438 ++ (27674, 2) :: (1, 1) :: repeat (1, 2) 323288 ++ w) 1)).
  {
    apply (sTDN [112; 20; 0] 158 ((29, 2) :: (1, 1) :: repeat (1, 2) 569 ++ (24959, 2) :: (1, 1) :: repeat (1, 2) 50438 ++ (27674, 2) :: (1, 1) :: repeat (1, 2) 323288 ++ w) 1).
  }
  (* step 94: sTUP *)
  apply (hsteps_trans _ (HC [112; 20; 0] 158 3 2 ((27, 2) :: (1, 1) :: repeat (1, 2) 569 ++ (24959, 2) :: (1, 1) :: repeat (1, 2) 50438 ++ (27674, 2) :: (1, 1) :: repeat (1, 2) 323288 ++ w) 1)).
  {
    replace ((27, 2) :: (1, 1) :: repeat (1, 2) 569 ++ (24959, 2) :: (1, 1) :: repeat (1, 2) 50438 ++ (27674, 2) :: (1, 1) :: repeat (1, 2) 323288 ++ w) with ((29 - 2, 2) :: (1, 1) :: repeat (1, 2) 569 ++ (24959, 2) :: (1, 1) :: repeat (1, 2) 50438 ++ (27674, 2) :: (1, 1) :: repeat (1, 2) 323288 ++ w) by sec_eq.
    apply (sTUP [112; 20; 0] 158 4 29 2 ((1, 1) :: repeat (1, 2) 569 ++ (24959, 2) :: (1, 1) :: repeat (1, 2) 50438 ++ (27674, 2) :: (1, 1) :: repeat (1, 2) 323288 ++ w) 1); closearith.
  }
  (* step 95: CLEANG_odd 12 *)
  apply (hsteps_trans _ (HB [112; 20; 0] 158 1 32 (repeat (1, 2) 1 ++ (1, 1) :: repeat (1, 2) 569 ++ (24959, 2) :: (1, 1) :: repeat (1, 2) 50438 ++ (27674, 2) :: (1, 1) :: repeat (1, 2) 323288 ++ w) 1)).
  {
    replace (repeat (1, 2) 1 ++ (1, 1) :: repeat (1, 2) 569 ++ (24959, 2) :: (1, 1) :: repeat (1, 2) 50438 ++ (27674, 2) :: (1, 1) :: repeat (1, 2) 323288 ++ w) with ((1, 2) :: (1, 1) :: repeat (1, 2) 569 ++ (24959, 2) :: (1, 1) :: repeat (1, 2) 50438 ++ (27674, 2) :: (1, 1) :: repeat (1, 2) 323288 ++ w) by sec_eq.
    apply (CLEANG_odd 12 [112; 20; 0] 158 ((1, 1) :: repeat (1, 2) 569 ++ (24959, 2) :: (1, 1) :: repeat (1, 2) 50438 ++ (27674, 2) :: (1, 1) :: repeat (1, 2) 323288 ++ w) 1); closearith.
  }
  (* step 96: M pop12 (1,) *)
  apply (hsteps_trans _ (HB [112; 20; 0] 159 1 34 ((1, 1) :: repeat (1, 2) 569 ++ (24959, 2) :: (1, 1) :: repeat (1, 2) 50438 ++ (27674, 2) :: (1, 1) :: repeat (1, 2) 323288 ++ w) 1)).
  {
    apply (pop12 1 [112; 20; 0] 158 32 ((1, 1) :: repeat (1, 2) 569 ++ (24959, 2) :: (1, 1) :: repeat (1, 2) 50438 ++ (27674, 2) :: (1, 1) :: repeat (1, 2) 323288 ++ w) 1); closearith.
  }
  (* step 97: P POP *)
  apply (hsteps_trans _ (HB [112; 20; 0] 160 1 35 (repeat (1, 2) 569 ++ (24959, 2) :: (1, 1) :: repeat (1, 2) 50438 ++ (27674, 2) :: (1, 1) :: repeat (1, 2) 323288 ++ w) 1)).
  {
    apply (sPOP1 [112; 20; 0] 159 34 (repeat (1, 2) 569 ++ (24959, 2) :: (1, 1) :: repeat (1, 2) 50438 ++ (27674, 2) :: (1, 1) :: repeat (1, 2) 323288 ++ w) 1); closearith.
  }
  (* step 98: M pop12 (569,) *)
  apply (hsteps_trans _ (HB [112; 20; 0] 729 1 1173 ((24959, 2) :: (1, 1) :: repeat (1, 2) 50438 ++ (27674, 2) :: (1, 1) :: repeat (1, 2) 323288 ++ w) 1)).
  {
    apply (pop12 569 [112; 20; 0] 160 35 ((24959, 2) :: (1, 1) :: repeat (1, 2) 50438 ++ (27674, 2) :: (1, 1) :: repeat (1, 2) 323288 ++ w) 1); closearith.
  }
  (* step 99: sTUP *)
  apply (hsteps_trans _ (HC [112; 20; 0] 729 1172 2 ((24957, 2) :: (1, 1) :: repeat (1, 2) 50438 ++ (27674, 2) :: (1, 1) :: repeat (1, 2) 323288 ++ w) 1)).
  {
    replace ((24957, 2) :: (1, 1) :: repeat (1, 2) 50438 ++ (27674, 2) :: (1, 1) :: repeat (1, 2) 323288 ++ w) with ((24959 - 2, 2) :: (1, 1) :: repeat (1, 2) 50438 ++ (27674, 2) :: (1, 1) :: repeat (1, 2) 323288 ++ w) by sec_eq.
    apply (sTUP [112; 20; 0] 729 1173 24959 2 ((1, 1) :: repeat (1, 2) 50438 ++ (27674, 2) :: (1, 1) :: repeat (1, 2) 323288 ++ w) 1); closearith.
  }
  (* step 100: hGRIND_even 584 *)
  apply (hsteps_trans _ (HB [112; 20; 0] 728 1 1172 ((2, 2) :: (24957, 2) :: (1, 1) :: repeat (1, 2) 50438 ++ (27674, 2) :: (1, 1) :: repeat (1, 2) 323288 ++ w) 1)).
  {
    apply (hGRIND_even 584 [112; 20; 0] 728 ((24957, 2) :: (1, 1) :: repeat (1, 2) 50438 ++ (27674, 2) :: (1, 1) :: repeat (1, 2) 323288 ++ w) 1); closearith.
  }
  (* step 101: P TUP2_1 *)
  apply (hsteps_trans _ (HC [729; 112; 20; 0] 1172 1 2 ((24955, 2) :: (1, 1) :: repeat (1, 2) 50438 ++ (27674, 2) :: (1, 1) :: repeat (1, 2) 323288 ++ w) 1)).
  {
    replace ((24955, 2) :: (1, 1) :: repeat (1, 2) 50438 ++ (27674, 2) :: (1, 1) :: repeat (1, 2) 323288 ++ w) with ((24957 - 2, 2) :: (1, 1) :: repeat (1, 2) 50438 ++ (27674, 2) :: (1, 1) :: repeat (1, 2) 323288 ++ w) by sec_eq.
    apply (sTUP2_1 [112; 20; 0] 728 1171 24957 ((1, 1) :: repeat (1, 2) 50438 ++ (27674, 2) :: (1, 1) :: repeat (1, 2) 323288 ++ w) 1); closearith.
  }
  (* step 102: P TDN *)
  apply (hsteps_trans _ (HB [729; 112; 20; 0] 1172 1 4 ((24955, 2) :: (1, 1) :: repeat (1, 2) 50438 ++ (27674, 2) :: (1, 1) :: repeat (1, 2) 323288 ++ w) 1)).
  {
    apply (sTDN [729; 112; 20; 0] 1172 ((24955, 2) :: (1, 1) :: repeat (1, 2) 50438 ++ (27674, 2) :: (1, 1) :: repeat (1, 2) 323288 ++ w) 1).
  }
  (* step 103: sTUP *)
  apply (hsteps_trans _ (HC [729; 112; 20; 0] 1172 3 2 ((24953, 2) :: (1, 1) :: repeat (1, 2) 50438 ++ (27674, 2) :: (1, 1) :: repeat (1, 2) 323288 ++ w) 1)).
  {
    replace ((24953, 2) :: (1, 1) :: repeat (1, 2) 50438 ++ (27674, 2) :: (1, 1) :: repeat (1, 2) 323288 ++ w) with ((24955 - 2, 2) :: (1, 1) :: repeat (1, 2) 50438 ++ (27674, 2) :: (1, 1) :: repeat (1, 2) 323288 ++ w) by sec_eq.
    apply (sTUP [729; 112; 20; 0] 1172 4 24955 2 ((1, 1) :: repeat (1, 2) 50438 ++ (27674, 2) :: (1, 1) :: repeat (1, 2) 323288 ++ w) 1); closearith.
  }
  (* step 104: DIPGRIND 1172 22609 *)
  apply (hsteps_trans _ (HC [729; 112; 20; 0] 0 3 2 (repeat (1, 2) 1172 ++ (22609, 2) :: (1, 1) :: repeat (1, 2) 50438 ++ (27674, 2) :: (1, 1) :: repeat (1, 2) 323288 ++ w) 1)).
  {
    apply (DIPGRIND 1172 22609 [729; 112; 20; 0] ((1, 1) :: repeat (1, 2) 50438 ++ (27674, 2) :: (1, 1) :: repeat (1, 2) 323288 ++ w) 1); closearith.
  }
  (* step 105: P PX2A *)
  apply (hsteps_trans _ (HC [20; 0] 111 727 2 ((1, 1) :: repeat (1, 2) 1174 ++ (22609, 2) :: (1, 1) :: repeat (1, 2) 50438 ++ (27674, 2) :: (1, 1) :: repeat (1, 2) 323288 ++ w) 1)).
  {
    apply (hsteps_step _ (HC [20; 0] 111 727 2 ((1, 1) :: repeat (1, 2) 1174 ++ (22609, 2) :: (1, 1) :: repeat (1, 2) 50438 ++ (27674, 2) :: (1, 1) :: repeat (1, 2) 323288 ++ w) 1)); [apply hPX2A | apply hsteps_refl].
  }
  (* step 106: P PUSH *)
  apply (hsteps_trans _ (HC [20; 0] 110 1 2 ((725, 2) :: (1, 1) :: repeat (1, 2) 1174 ++ (22609, 2) :: (1, 1) :: repeat (1, 2) 50438 ++ (27674, 2) :: (1, 1) :: repeat (1, 2) 323288 ++ w) 1)).
  {
    replace ((725, 2) :: (1, 1) :: repeat (1, 2) 1174 ++ (22609, 2) :: (1, 1) :: repeat (1, 2) 50438 ++ (27674, 2) :: (1, 1) :: repeat (1, 2) 323288 ++ w) with ((727 - 2, 2) :: (1, 1) :: repeat (1, 2) 1174 ++ (22609, 2) :: (1, 1) :: repeat (1, 2) 50438 ++ (27674, 2) :: (1, 1) :: repeat (1, 2) 323288 ++ w) by sec_eq.
    apply (sPUSH [20; 0] 110 727 ((1, 1) :: repeat (1, 2) 1174 ++ (22609, 2) :: (1, 1) :: repeat (1, 2) 50438 ++ (27674, 2) :: (1, 1) :: repeat (1, 2) 323288 ++ w) 1); closearith.
  }
  (* step 107: P TDN *)
  apply (hsteps_trans _ (HB [20; 0] 110 1 4 ((725, 2) :: (1, 1) :: repeat (1, 2) 1174 ++ (22609, 2) :: (1, 1) :: repeat (1, 2) 50438 ++ (27674, 2) :: (1, 1) :: repeat (1, 2) 323288 ++ w) 1)).
  {
    apply (sTDN [20; 0] 110 ((725, 2) :: (1, 1) :: repeat (1, 2) 1174 ++ (22609, 2) :: (1, 1) :: repeat (1, 2) 50438 ++ (27674, 2) :: (1, 1) :: repeat (1, 2) 323288 ++ w) 1).
  }
  (* step 108: sTUP *)
  apply (hsteps_trans _ (HC [20; 0] 110 3 2 ((723, 2) :: (1, 1) :: repeat (1, 2) 1174 ++ (22609, 2) :: (1, 1) :: repeat (1, 2) 50438 ++ (27674, 2) :: (1, 1) :: repeat (1, 2) 323288 ++ w) 1)).
  {
    replace ((723, 2) :: (1, 1) :: repeat (1, 2) 1174 ++ (22609, 2) :: (1, 1) :: repeat (1, 2) 50438 ++ (27674, 2) :: (1, 1) :: repeat (1, 2) 323288 ++ w) with ((725 - 2, 2) :: (1, 1) :: repeat (1, 2) 1174 ++ (22609, 2) :: (1, 1) :: repeat (1, 2) 50438 ++ (27674, 2) :: (1, 1) :: repeat (1, 2) 323288 ++ w) by sec_eq.
    apply (sTUP [20; 0] 110 4 725 2 ((1, 1) :: repeat (1, 2) 1174 ++ (22609, 2) :: (1, 1) :: repeat (1, 2) 50438 ++ (27674, 2) :: (1, 1) :: repeat (1, 2) 323288 ++ w) 1); closearith.
  }
  (* step 109: DIPGRIND 110 503 *)
  apply (hsteps_trans _ (HC [20; 0] 0 3 2 (repeat (1, 2) 110 ++ (503, 2) :: (1, 1) :: repeat (1, 2) 1174 ++ (22609, 2) :: (1, 1) :: repeat (1, 2) 50438 ++ (27674, 2) :: (1, 1) :: repeat (1, 2) 323288 ++ w) 1)).
  {
    apply (DIPGRIND 110 503 [20; 0] ((1, 1) :: repeat (1, 2) 1174 ++ (22609, 2) :: (1, 1) :: repeat (1, 2) 50438 ++ (27674, 2) :: (1, 1) :: repeat (1, 2) 323288 ++ w) 1); closearith.
  }
  (* step 110: P PX2A0 *)
  apply (hsteps_trans _ (HB [0] 3 1 2 ((16, 2) :: (1, 1) :: repeat (1, 2) 112 ++ (503, 2) :: (1, 1) :: repeat (1, 2) 1174 ++ (22609, 2) :: (1, 1) :: repeat (1, 2) 50438 ++ (27674, 2) :: (1, 1) :: repeat (1, 2) 323288 ++ w) 1)).
  {
    apply (hsteps_step _ (HB [0] 3 1 2 ((16, 2) :: (1, 1) :: repeat (1, 2) 112 ++ (503, 2) :: (1, 1) :: repeat (1, 2) 1174 ++ (22609, 2) :: (1, 1) :: repeat (1, 2) 50438 ++ (27674, 2) :: (1, 1) :: repeat (1, 2) 323288 ++ w) 1)); [apply hPX2A0 | apply hsteps_refl].
  }
  (* step 111: sTUP *)
  apply (hsteps_trans _ (HC [0] 3 1 2 ((14, 2) :: (1, 1) :: repeat (1, 2) 112 ++ (503, 2) :: (1, 1) :: repeat (1, 2) 1174 ++ (22609, 2) :: (1, 1) :: repeat (1, 2) 50438 ++ (27674, 2) :: (1, 1) :: repeat (1, 2) 323288 ++ w) 1)).
  {
    replace ((14, 2) :: (1, 1) :: repeat (1, 2) 112 ++ (503, 2) :: (1, 1) :: repeat (1, 2) 1174 ++ (22609, 2) :: (1, 1) :: repeat (1, 2) 50438 ++ (27674, 2) :: (1, 1) :: repeat (1, 2) 323288 ++ w) with ((16 - 2, 2) :: (1, 1) :: repeat (1, 2) 112 ++ (503, 2) :: (1, 1) :: repeat (1, 2) 1174 ++ (22609, 2) :: (1, 1) :: repeat (1, 2) 50438 ++ (27674, 2) :: (1, 1) :: repeat (1, 2) 323288 ++ w) by sec_eq.
    apply (sTUP [0] 3 2 16 2 ((1, 1) :: repeat (1, 2) 112 ++ (503, 2) :: (1, 1) :: repeat (1, 2) 1174 ++ (22609, 2) :: (1, 1) :: repeat (1, 2) 50438 ++ (27674, 2) :: (1, 1) :: repeat (1, 2) 323288 ++ w) 1); closearith.
  }
  (* step 112: P TDN *)
  apply (sTDN [0] 3 ((14, 2) :: (1, 1) :: repeat (1, 2) 112 ++ (503, 2) :: (1, 1) :: repeat (1, 2) 1174 ++ (22609, 2) :: (1, 1) :: repeat (1, 2) 50438 ++ (27674, 2) :: (1, 1) :: repeat (1, 2) 323288 ++ w) 1).
Qed.

(* CASCADE53c: steps 113-168 of the CASCADE53 chain. *)
Lemma CASCADE53c : forall w,
  hsteps (HB [0] 3 1 4 ((14, 2) :: (1, 1) :: repeat (1, 2) 112 ++ (503, 2) :: (1, 1) :: repeat (1, 2) 1174 ++ (22609, 2) :: (1, 1) :: repeat (1, 2) 50438 ++ (27674, 2) :: (1, 1) :: repeat (1, 2) 323288 ++ w) 1)
         (HC [5] 49 74 2 ((15, 2) :: (1, 1) :: repeat (1, 2) 228 ++ (45, 2) :: (1, 1) :: repeat (1, 2) 1174 ++ (22609, 2) :: (1, 1) :: repeat (1, 2) 50438 ++ (27674, 2) :: (1, 1) :: repeat (1, 2) 323288 ++ w) 1).
Proof.
  intro w.
  (* step 113: sTUP *)
  apply (hsteps_trans _ (HC [0] 3 3 2 ((12, 2) :: (1, 1) :: repeat (1, 2) 112 ++ (503, 2) :: (1, 1) :: repeat (1, 2) 1174 ++ (22609, 2) :: (1, 1) :: repeat (1, 2) 50438 ++ (27674, 2) :: (1, 1) :: repeat (1, 2) 323288 ++ w) 1)).
  {
    replace ((12, 2) :: (1, 1) :: repeat (1, 2) 112 ++ (503, 2) :: (1, 1) :: repeat (1, 2) 1174 ++ (22609, 2) :: (1, 1) :: repeat (1, 2) 50438 ++ (27674, 2) :: (1, 1) :: repeat (1, 2) 323288 ++ w) with ((14 - 2, 2) :: (1, 1) :: repeat (1, 2) 112 ++ (503, 2) :: (1, 1) :: repeat (1, 2) 1174 ++ (22609, 2) :: (1, 1) :: repeat (1, 2) 50438 ++ (27674, 2) :: (1, 1) :: repeat (1, 2) 323288 ++ w) by sec_eq.
    apply (sTUP [0] 3 4 14 2 ((1, 1) :: repeat (1, 2) 112 ++ (503, 2) :: (1, 1) :: repeat (1, 2) 1174 ++ (22609, 2) :: (1, 1) :: repeat (1, 2) 50438 ++ (27674, 2) :: (1, 1) :: repeat (1, 2) 323288 ++ w) 1); closearith.
  }
  (* step 114: DIPGRIND 3 6 *)
  apply (hsteps_trans _ (HC [0] 0 3 2 (repeat (1, 2) 3 ++ (6, 2) :: (1, 1) :: repeat (1, 2) 112 ++ (503, 2) :: (1, 1) :: repeat (1, 2) 1174 ++ (22609, 2) :: (1, 1) :: repeat (1, 2) 50438 ++ (27674, 2) :: (1, 1) :: repeat (1, 2) 323288 ++ w) 1)).
  {
    apply (DIPGRIND 3 6 [0] ((1, 1) :: repeat (1, 2) 112 ++ (503, 2) :: (1, 1) :: repeat (1, 2) 1174 ++ (22609, 2) :: (1, 1) :: repeat (1, 2) 50438 ++ (27674, 2) :: (1, 1) :: repeat (1, 2) 323288 ++ w) 1); closearith.
  }
  (* step 115: P PX2B0 *)
  apply (hsteps_trans _ (HB [] 0 1 5 (repeat (1, 2) 4 ++ (6, 2) :: (1, 1) :: repeat (1, 2) 112 ++ (503, 2) :: (1, 1) :: repeat (1, 2) 1174 ++ (22609, 2) :: (1, 1) :: repeat (1, 2) 50438 ++ (27674, 2) :: (1, 1) :: repeat (1, 2) 323288 ++ w) 1)).
  {
    apply (hsteps_step _ (HB [] 0 1 5 (repeat (1, 2) 4 ++ (6, 2) :: (1, 1) :: repeat (1, 2) 112 ++ (503, 2) :: (1, 1) :: repeat (1, 2) 1174 ++ (22609, 2) :: (1, 1) :: repeat (1, 2) 50438 ++ (27674, 2) :: (1, 1) :: repeat (1, 2) 323288 ++ w) 1)); [apply hPX2B0 | apply hsteps_refl].
  }
  (* step 116: M pop12 (4,) *)
  apply (hsteps_trans _ (HB [] 4 1 13 ((6, 2) :: (1, 1) :: repeat (1, 2) 112 ++ (503, 2) :: (1, 1) :: repeat (1, 2) 1174 ++ (22609, 2) :: (1, 1) :: repeat (1, 2) 50438 ++ (27674, 2) :: (1, 1) :: repeat (1, 2) 323288 ++ w) 1)).
  {
    apply (pop12 4 [] 0 5 ((6, 2) :: (1, 1) :: repeat (1, 2) 112 ++ (503, 2) :: (1, 1) :: repeat (1, 2) 1174 ++ (22609, 2) :: (1, 1) :: repeat (1, 2) 50438 ++ (27674, 2) :: (1, 1) :: repeat (1, 2) 323288 ++ w) 1); closearith.
  }
  (* step 117: sTUP *)
  apply (hsteps_trans _ (HC [] 4 12 2 ((4, 2) :: (1, 1) :: repeat (1, 2) 112 ++ (503, 2) :: (1, 1) :: repeat (1, 2) 1174 ++ (22609, 2) :: (1, 1) :: repeat (1, 2) 50438 ++ (27674, 2) :: (1, 1) :: repeat (1, 2) 323288 ++ w) 1)).
  {
    replace ((4, 2) :: (1, 1) :: repeat (1, 2) 112 ++ (503, 2) :: (1, 1) :: repeat (1, 2) 1174 ++ (22609, 2) :: (1, 1) :: repeat (1, 2) 50438 ++ (27674, 2) :: (1, 1) :: repeat (1, 2) 323288 ++ w) with ((6 - 2, 2) :: (1, 1) :: repeat (1, 2) 112 ++ (503, 2) :: (1, 1) :: repeat (1, 2) 1174 ++ (22609, 2) :: (1, 1) :: repeat (1, 2) 50438 ++ (27674, 2) :: (1, 1) :: repeat (1, 2) 323288 ++ w) by sec_eq.
    apply (sTUP [] 4 13 6 2 ((1, 1) :: repeat (1, 2) 112 ++ (503, 2) :: (1, 1) :: repeat (1, 2) 1174 ++ (22609, 2) :: (1, 1) :: repeat (1, 2) 50438 ++ (27674, 2) :: (1, 1) :: repeat (1, 2) 323288 ++ w) 1); closearith.
  }
  (* step 118: P PUSH *)
  apply (hsteps_trans _ (HC [] 3 1 2 ((10, 2) :: (4, 2) :: (1, 1) :: repeat (1, 2) 112 ++ (503, 2) :: (1, 1) :: repeat (1, 2) 1174 ++ (22609, 2) :: (1, 1) :: repeat (1, 2) 50438 ++ (27674, 2) :: (1, 1) :: repeat (1, 2) 323288 ++ w) 1)).
  {
    replace ((10, 2) :: (4, 2) :: (1, 1) :: repeat (1, 2) 112 ++ (503, 2) :: (1, 1) :: repeat (1, 2) 1174 ++ (22609, 2) :: (1, 1) :: repeat (1, 2) 50438 ++ (27674, 2) :: (1, 1) :: repeat (1, 2) 323288 ++ w) with ((12 - 2, 2) :: (4, 2) :: (1, 1) :: repeat (1, 2) 112 ++ (503, 2) :: (1, 1) :: repeat (1, 2) 1174 ++ (22609, 2) :: (1, 1) :: repeat (1, 2) 50438 ++ (27674, 2) :: (1, 1) :: repeat (1, 2) 323288 ++ w) by sec_eq.
    apply (sPUSH [] 3 12 ((4, 2) :: (1, 1) :: repeat (1, 2) 112 ++ (503, 2) :: (1, 1) :: repeat (1, 2) 1174 ++ (22609, 2) :: (1, 1) :: repeat (1, 2) 50438 ++ (27674, 2) :: (1, 1) :: repeat (1, 2) 323288 ++ w) 1); closearith.
  }
  (* step 119: P TDN *)
  apply (hsteps_trans _ (HB [] 3 1 4 ((10, 2) :: (4, 2) :: (1, 1) :: repeat (1, 2) 112 ++ (503, 2) :: (1, 1) :: repeat (1, 2) 1174 ++ (22609, 2) :: (1, 1) :: repeat (1, 2) 50438 ++ (27674, 2) :: (1, 1) :: repeat (1, 2) 323288 ++ w) 1)).
  {
    apply (sTDN [] 3 ((10, 2) :: (4, 2) :: (1, 1) :: repeat (1, 2) 112 ++ (503, 2) :: (1, 1) :: repeat (1, 2) 1174 ++ (22609, 2) :: (1, 1) :: repeat (1, 2) 50438 ++ (27674, 2) :: (1, 1) :: repeat (1, 2) 323288 ++ w) 1).
  }
  (* step 120: sTUP *)
  apply (hsteps_trans _ (HC [] 3 3 2 ((8, 2) :: (4, 2) :: (1, 1) :: repeat (1, 2) 112 ++ (503, 2) :: (1, 1) :: repeat (1, 2) 1174 ++ (22609, 2) :: (1, 1) :: repeat (1, 2) 50438 ++ (27674, 2) :: (1, 1) :: repeat (1, 2) 323288 ++ w) 1)).
  {
    replace ((8, 2) :: (4, 2) :: (1, 1) :: repeat (1, 2) 112 ++ (503, 2) :: (1, 1) :: repeat (1, 2) 1174 ++ (22609, 2) :: (1, 1) :: repeat (1, 2) 50438 ++ (27674, 2) :: (1, 1) :: repeat (1, 2) 323288 ++ w) with ((10 - 2, 2) :: (4, 2) :: (1, 1) :: repeat (1, 2) 112 ++ (503, 2) :: (1, 1) :: repeat (1, 2) 1174 ++ (22609, 2) :: (1, 1) :: repeat (1, 2) 50438 ++ (27674, 2) :: (1, 1) :: repeat (1, 2) 323288 ++ w) by sec_eq.
    apply (sTUP [] 3 4 10 2 ((4, 2) :: (1, 1) :: repeat (1, 2) 112 ++ (503, 2) :: (1, 1) :: repeat (1, 2) 1174 ++ (22609, 2) :: (1, 1) :: repeat (1, 2) 50438 ++ (27674, 2) :: (1, 1) :: repeat (1, 2) 323288 ++ w) 1); closearith.
  }
  (* step 121: DIPGRIND 3 2 *)
  apply (hsteps_trans _ (HC [] 0 3 2 (repeat (1, 2) 3 ++ (2, 2) :: (4, 2) :: (1, 1) :: repeat (1, 2) 112 ++ (503, 2) :: (1, 1) :: repeat (1, 2) 1174 ++ (22609, 2) :: (1, 1) :: repeat (1, 2) 50438 ++ (27674, 2) :: (1, 1) :: repeat (1, 2) 323288 ++ w) 1)).
  {
    apply (DIPGRIND 3 2 [] ((4, 2) :: (1, 1) :: repeat (1, 2) 112 ++ (503, 2) :: (1, 1) :: repeat (1, 2) 1174 ++ (22609, 2) :: (1, 1) :: repeat (1, 2) 50438 ++ (27674, 2) :: (1, 1) :: repeat (1, 2) 323288 ++ w) 1); closearith.
  }
  (* step 122: P PUSHX *)
  apply (hsteps_trans _ (HB [] 1 1 7 (repeat (1, 2) 3 ++ (2, 2) :: (4, 2) :: (1, 1) :: repeat (1, 2) 112 ++ (503, 2) :: (1, 1) :: repeat (1, 2) 1174 ++ (22609, 2) :: (1, 1) :: repeat (1, 2) 50438 ++ (27674, 2) :: (1, 1) :: repeat (1, 2) 323288 ++ w) 1)).
  {
    apply (hsteps_step _ (HB [] 1 1 7 (repeat (1, 2) 3 ++ (2, 2) :: (4, 2) :: (1, 1) :: repeat (1, 2) 112 ++ (503, 2) :: (1, 1) :: repeat (1, 2) 1174 ++ (22609, 2) :: (1, 1) :: repeat (1, 2) 50438 ++ (27674, 2) :: (1, 1) :: repeat (1, 2) 323288 ++ w) 1)); [apply hPUSHX | apply hsteps_refl].
  }
  (* step 123: M pop12 (3,) *)
  apply (hsteps_trans _ (HB [] 4 1 13 ((2, 2) :: (4, 2) :: (1, 1) :: repeat (1, 2) 112 ++ (503, 2) :: (1, 1) :: repeat (1, 2) 1174 ++ (22609, 2) :: (1, 1) :: repeat (1, 2) 50438 ++ (27674, 2) :: (1, 1) :: repeat (1, 2) 323288 ++ w) 1)).
  {
    apply (pop12 3 [] 1 7 ((2, 2) :: (4, 2) :: (1, 1) :: repeat (1, 2) 112 ++ (503, 2) :: (1, 1) :: repeat (1, 2) 1174 ++ (22609, 2) :: (1, 1) :: repeat (1, 2) 50438 ++ (27674, 2) :: (1, 1) :: repeat (1, 2) 323288 ++ w) 1); closearith.
  }
  (* step 124: P TUP2_1 *)
  apply (hsteps_trans _ (HC [5] 13 1 2 ((2, 2) :: (1, 1) :: repeat (1, 2) 112 ++ (503, 2) :: (1, 1) :: repeat (1, 2) 1174 ++ (22609, 2) :: (1, 1) :: repeat (1, 2) 50438 ++ (27674, 2) :: (1, 1) :: repeat (1, 2) 323288 ++ w) 1)).
  {
    replace ((2, 2) :: (1, 1) :: repeat (1, 2) 112 ++ (503, 2) :: (1, 1) :: repeat (1, 2) 1174 ++ (22609, 2) :: (1, 1) :: repeat (1, 2) 50438 ++ (27674, 2) :: (1, 1) :: repeat (1, 2) 323288 ++ w) with ((4 - 2, 2) :: (1, 1) :: repeat (1, 2) 112 ++ (503, 2) :: (1, 1) :: repeat (1, 2) 1174 ++ (22609, 2) :: (1, 1) :: repeat (1, 2) 50438 ++ (27674, 2) :: (1, 1) :: repeat (1, 2) 323288 ++ w) by sec_eq.
    apply (sTUP2_1 [] 4 12 4 ((1, 1) :: repeat (1, 2) 112 ++ (503, 2) :: (1, 1) :: repeat (1, 2) 1174 ++ (22609, 2) :: (1, 1) :: repeat (1, 2) 50438 ++ (27674, 2) :: (1, 1) :: repeat (1, 2) 323288 ++ w) 1); closearith.
  }
  (* step 125: P TDN *)
  apply (hsteps_trans _ (HB [5] 13 1 4 ((2, 2) :: (1, 1) :: repeat (1, 2) 112 ++ (503, 2) :: (1, 1) :: repeat (1, 2) 1174 ++ (22609, 2) :: (1, 1) :: repeat (1, 2) 50438 ++ (27674, 2) :: (1, 1) :: repeat (1, 2) 323288 ++ w) 1)).
  {
    apply (sTDN [5] 13 ((2, 2) :: (1, 1) :: repeat (1, 2) 112 ++ (503, 2) :: (1, 1) :: repeat (1, 2) 1174 ++ (22609, 2) :: (1, 1) :: repeat (1, 2) 50438 ++ (27674, 2) :: (1, 1) :: repeat (1, 2) 323288 ++ w) 1).
  }
  (* step 126: P TRANS2_1 *)
  apply (hsteps_trans _ (HB [14; 5] 5 1 3 (repeat (1, 2) 112 ++ (503, 2) :: (1, 1) :: repeat (1, 2) 1174 ++ (22609, 2) :: (1, 1) :: repeat (1, 2) 50438 ++ (27674, 2) :: (1, 1) :: repeat (1, 2) 323288 ++ w) 1)).
  {
    apply (sTRANS2_1 [5] 13 3 1 (repeat (1, 2) 112 ++ (503, 2) :: (1, 1) :: repeat (1, 2) 1174 ++ (22609, 2) :: (1, 1) :: repeat (1, 2) 50438 ++ (27674, 2) :: (1, 1) :: repeat (1, 2) 323288 ++ w) 1); closearith.
  }
  (* step 127: M pop12 (112,) *)
  apply (hsteps_trans _ (HB [14; 5] 117 1 227 ((503, 2) :: (1, 1) :: repeat (1, 2) 1174 ++ (22609, 2) :: (1, 1) :: repeat (1, 2) 50438 ++ (27674, 2) :: (1, 1) :: repeat (1, 2) 323288 ++ w) 1)).
  {
    apply (pop12 112 [14; 5] 5 3 ((503, 2) :: (1, 1) :: repeat (1, 2) 1174 ++ (22609, 2) :: (1, 1) :: repeat (1, 2) 50438 ++ (27674, 2) :: (1, 1) :: repeat (1, 2) 323288 ++ w) 1); closearith.
  }
  (* step 128: sTUP *)
  apply (hsteps_trans _ (HC [14; 5] 117 226 2 ((501, 2) :: (1, 1) :: repeat (1, 2) 1174 ++ (22609, 2) :: (1, 1) :: repeat (1, 2) 50438 ++ (27674, 2) :: (1, 1) :: repeat (1, 2) 323288 ++ w) 1)).
  {
    replace ((501, 2) :: (1, 1) :: repeat (1, 2) 1174 ++ (22609, 2) :: (1, 1) :: repeat (1, 2) 50438 ++ (27674, 2) :: (1, 1) :: repeat (1, 2) 323288 ++ w) with ((503 - 2, 2) :: (1, 1) :: repeat (1, 2) 1174 ++ (22609, 2) :: (1, 1) :: repeat (1, 2) 50438 ++ (27674, 2) :: (1, 1) :: repeat (1, 2) 323288 ++ w) by sec_eq.
    apply (sTUP [14; 5] 117 227 503 2 ((1, 1) :: repeat (1, 2) 1174 ++ (22609, 2) :: (1, 1) :: repeat (1, 2) 50438 ++ (27674, 2) :: (1, 1) :: repeat (1, 2) 323288 ++ w) 1); closearith.
  }
  (* step 129: hGRIND_even 111 *)
  apply (hsteps_trans _ (HB [14; 5] 116 1 226 ((2, 2) :: (501, 2) :: (1, 1) :: repeat (1, 2) 1174 ++ (22609, 2) :: (1, 1) :: repeat (1, 2) 50438 ++ (27674, 2) :: (1, 1) :: repeat (1, 2) 323288 ++ w) 1)).
  {
    apply (hGRIND_even 111 [14; 5] 116 ((501, 2) :: (1, 1) :: repeat (1, 2) 1174 ++ (22609, 2) :: (1, 1) :: repeat (1, 2) 50438 ++ (27674, 2) :: (1, 1) :: repeat (1, 2) 323288 ++ w) 1); closearith.
  }
  (* step 130: P TUP2_1 *)
  apply (hsteps_trans _ (HC [117; 14; 5] 226 1 2 ((499, 2) :: (1, 1) :: repeat (1, 2) 1174 ++ (22609, 2) :: (1, 1) :: repeat (1, 2) 50438 ++ (27674, 2) :: (1, 1) :: repeat (1, 2) 323288 ++ w) 1)).
  {
    replace ((499, 2) :: (1, 1) :: repeat (1, 2) 1174 ++ (22609, 2) :: (1, 1) :: repeat (1, 2) 50438 ++ (27674, 2) :: (1, 1) :: repeat (1, 2) 323288 ++ w) with ((501 - 2, 2) :: (1, 1) :: repeat (1, 2) 1174 ++ (22609, 2) :: (1, 1) :: repeat (1, 2) 50438 ++ (27674, 2) :: (1, 1) :: repeat (1, 2) 323288 ++ w) by sec_eq.
    apply (sTUP2_1 [14; 5] 116 225 501 ((1, 1) :: repeat (1, 2) 1174 ++ (22609, 2) :: (1, 1) :: repeat (1, 2) 50438 ++ (27674, 2) :: (1, 1) :: repeat (1, 2) 323288 ++ w) 1); closearith.
  }
  (* step 131: P TDN *)
  apply (hsteps_trans _ (HB [117; 14; 5] 226 1 4 ((499, 2) :: (1, 1) :: repeat (1, 2) 1174 ++ (22609, 2) :: (1, 1) :: repeat (1, 2) 50438 ++ (27674, 2) :: (1, 1) :: repeat (1, 2) 323288 ++ w) 1)).
  {
    apply (sTDN [117; 14; 5] 226 ((499, 2) :: (1, 1) :: repeat (1, 2) 1174 ++ (22609, 2) :: (1, 1) :: repeat (1, 2) 50438 ++ (27674, 2) :: (1, 1) :: repeat (1, 2) 323288 ++ w) 1).
  }
  (* step 132: sTUP *)
  apply (hsteps_trans _ (HC [117; 14; 5] 226 3 2 ((497, 2) :: (1, 1) :: repeat (1, 2) 1174 ++ (22609, 2) :: (1, 1) :: repeat (1, 2) 50438 ++ (27674, 2) :: (1, 1) :: repeat (1, 2) 323288 ++ w) 1)).
  {
    replace ((497, 2) :: (1, 1) :: repeat (1, 2) 1174 ++ (22609, 2) :: (1, 1) :: repeat (1, 2) 50438 ++ (27674, 2) :: (1, 1) :: repeat (1, 2) 323288 ++ w) with ((499 - 2, 2) :: (1, 1) :: repeat (1, 2) 1174 ++ (22609, 2) :: (1, 1) :: repeat (1, 2) 50438 ++ (27674, 2) :: (1, 1) :: repeat (1, 2) 323288 ++ w) by sec_eq.
    apply (sTUP [117; 14; 5] 226 4 499 2 ((1, 1) :: repeat (1, 2) 1174 ++ (22609, 2) :: (1, 1) :: repeat (1, 2) 50438 ++ (27674, 2) :: (1, 1) :: repeat (1, 2) 323288 ++ w) 1); closearith.
  }
  (* step 133: DIPGRIND 226 45 *)
  apply (hsteps_trans _ (HC [117; 14; 5] 0 3 2 (repeat (1, 2) 226 ++ (45, 2) :: (1, 1) :: repeat (1, 2) 1174 ++ (22609, 2) :: (1, 1) :: repeat (1, 2) 50438 ++ (27674, 2) :: (1, 1) :: repeat (1, 2) 323288 ++ w) 1)).
  {
    apply (DIPGRIND 226 45 [117; 14; 5] ((1, 1) :: repeat (1, 2) 1174 ++ (22609, 2) :: (1, 1) :: repeat (1, 2) 50438 ++ (27674, 2) :: (1, 1) :: repeat (1, 2) 323288 ++ w) 1); closearith.
  }
  (* step 134: P PX2A *)
  apply (hsteps_trans _ (HC [5] 13 115 2 ((1, 1) :: repeat (1, 2) 228 ++ (45, 2) :: (1, 1) :: repeat (1, 2) 1174 ++ (22609, 2) :: (1, 1) :: repeat (1, 2) 50438 ++ (27674, 2) :: (1, 1) :: repeat (1, 2) 323288 ++ w) 1)).
  {
    apply (hsteps_step _ (HC [5] 13 115 2 ((1, 1) :: repeat (1, 2) 228 ++ (45, 2) :: (1, 1) :: repeat (1, 2) 1174 ++ (22609, 2) :: (1, 1) :: repeat (1, 2) 50438 ++ (27674, 2) :: (1, 1) :: repeat (1, 2) 323288 ++ w) 1)); [apply hPX2A | apply hsteps_refl].
  }
  (* step 135: P PUSH *)
  apply (hsteps_trans _ (HC [5] 12 1 2 ((113, 2) :: (1, 1) :: repeat (1, 2) 228 ++ (45, 2) :: (1, 1) :: repeat (1, 2) 1174 ++ (22609, 2) :: (1, 1) :: repeat (1, 2) 50438 ++ (27674, 2) :: (1, 1) :: repeat (1, 2) 323288 ++ w) 1)).
  {
    replace ((113, 2) :: (1, 1) :: repeat (1, 2) 228 ++ (45, 2) :: (1, 1) :: repeat (1, 2) 1174 ++ (22609, 2) :: (1, 1) :: repeat (1, 2) 50438 ++ (27674, 2) :: (1, 1) :: repeat (1, 2) 323288 ++ w) with ((115 - 2, 2) :: (1, 1) :: repeat (1, 2) 228 ++ (45, 2) :: (1, 1) :: repeat (1, 2) 1174 ++ (22609, 2) :: (1, 1) :: repeat (1, 2) 50438 ++ (27674, 2) :: (1, 1) :: repeat (1, 2) 323288 ++ w) by sec_eq.
    apply (sPUSH [5] 12 115 ((1, 1) :: repeat (1, 2) 228 ++ (45, 2) :: (1, 1) :: repeat (1, 2) 1174 ++ (22609, 2) :: (1, 1) :: repeat (1, 2) 50438 ++ (27674, 2) :: (1, 1) :: repeat (1, 2) 323288 ++ w) 1); closearith.
  }
  (* step 136: P TDN *)
  apply (hsteps_trans _ (HB [5] 12 1 4 ((113, 2) :: (1, 1) :: repeat (1, 2) 228 ++ (45, 2) :: (1, 1) :: repeat (1, 2) 1174 ++ (22609, 2) :: (1, 1) :: repeat (1, 2) 50438 ++ (27674, 2) :: (1, 1) :: repeat (1, 2) 323288 ++ w) 1)).
  {
    apply (sTDN [5] 12 ((113, 2) :: (1, 1) :: repeat (1, 2) 228 ++ (45, 2) :: (1, 1) :: repeat (1, 2) 1174 ++ (22609, 2) :: (1, 1) :: repeat (1, 2) 50438 ++ (27674, 2) :: (1, 1) :: repeat (1, 2) 323288 ++ w) 1).
  }
  (* step 137: sTUP *)
  apply (hsteps_trans _ (HC [5] 12 3 2 ((111, 2) :: (1, 1) :: repeat (1, 2) 228 ++ (45, 2) :: (1, 1) :: repeat (1, 2) 1174 ++ (22609, 2) :: (1, 1) :: repeat (1, 2) 50438 ++ (27674, 2) :: (1, 1) :: repeat (1, 2) 323288 ++ w) 1)).
  {
    replace ((111, 2) :: (1, 1) :: repeat (1, 2) 228 ++ (45, 2) :: (1, 1) :: repeat (1, 2) 1174 ++ (22609, 2) :: (1, 1) :: repeat (1, 2) 50438 ++ (27674, 2) :: (1, 1) :: repeat (1, 2) 323288 ++ w) with ((113 - 2, 2) :: (1, 1) :: repeat (1, 2) 228 ++ (45, 2) :: (1, 1) :: repeat (1, 2) 1174 ++ (22609, 2) :: (1, 1) :: repeat (1, 2) 50438 ++ (27674, 2) :: (1, 1) :: repeat (1, 2) 323288 ++ w) by sec_eq.
    apply (sTUP [5] 12 4 113 2 ((1, 1) :: repeat (1, 2) 228 ++ (45, 2) :: (1, 1) :: repeat (1, 2) 1174 ++ (22609, 2) :: (1, 1) :: repeat (1, 2) 50438 ++ (27674, 2) :: (1, 1) :: repeat (1, 2) 323288 ++ w) 1); closearith.
  }
  (* step 138: DIPGRIND 12 87 *)
  apply (hsteps_trans _ (HC [5] 0 3 2 (repeat (1, 2) 12 ++ (87, 2) :: (1, 1) :: repeat (1, 2) 228 ++ (45, 2) :: (1, 1) :: repeat (1, 2) 1174 ++ (22609, 2) :: (1, 1) :: repeat (1, 2) 50438 ++ (27674, 2) :: (1, 1) :: repeat (1, 2) 323288 ++ w) 1)).
  {
    apply (DIPGRIND 12 87 [5] ((1, 1) :: repeat (1, 2) 228 ++ (45, 2) :: (1, 1) :: repeat (1, 2) 1174 ++ (22609, 2) :: (1, 1) :: repeat (1, 2) 50438 ++ (27674, 2) :: (1, 1) :: repeat (1, 2) 323288 ++ w) 1); closearith.
  }
  (* step 139: P PX2Bgen *)
  apply (hsteps_trans _ (HB [0] 3 1 2 (repeat (1, 2) 1 ++ (1, 1) :: repeat (1, 2) 14 ++ (87, 2) :: (1, 1) :: repeat (1, 2) 228 ++ (45, 2) :: (1, 1) :: repeat (1, 2) 1174 ++ (22609, 2) :: (1, 1) :: repeat (1, 2) 50438 ++ (27674, 2) :: (1, 1) :: repeat (1, 2) 323288 ++ w) 1)).
  {
    apply (hsteps_step _ (HB [0] 3 1 2 (repeat (1, 2) 1 ++ (1, 1) :: repeat (1, 2) 14 ++ (87, 2) :: (1, 1) :: repeat (1, 2) 228 ++ (45, 2) :: (1, 1) :: repeat (1, 2) 1174 ++ (22609, 2) :: (1, 1) :: repeat (1, 2) 50438 ++ (27674, 2) :: (1, 1) :: repeat (1, 2) 323288 ++ w) 1)); [apply hPX2Bgen | apply hsteps_refl].
  }
  (* step 140: M pop12 (1,) *)
  apply (hsteps_trans _ (HB [0] 4 1 4 ((1, 1) :: repeat (1, 2) 14 ++ (87, 2) :: (1, 1) :: repeat (1, 2) 228 ++ (45, 2) :: (1, 1) :: repeat (1, 2) 1174 ++ (22609, 2) :: (1, 1) :: repeat (1, 2) 50438 ++ (27674, 2) :: (1, 1) :: repeat (1, 2) 323288 ++ w) 1)).
  {
    apply (pop12 1 [0] 3 2 ((1, 1) :: repeat (1, 2) 14 ++ (87, 2) :: (1, 1) :: repeat (1, 2) 228 ++ (45, 2) :: (1, 1) :: repeat (1, 2) 1174 ++ (22609, 2) :: (1, 1) :: repeat (1, 2) 50438 ++ (27674, 2) :: (1, 1) :: repeat (1, 2) 323288 ++ w) 1); closearith.
  }
  (* step 141: P POP *)
  apply (hsteps_trans _ (HB [0] 5 1 5 (repeat (1, 2) 14 ++ (87, 2) :: (1, 1) :: repeat (1, 2) 228 ++ (45, 2) :: (1, 1) :: repeat (1, 2) 1174 ++ (22609, 2) :: (1, 1) :: repeat (1, 2) 50438 ++ (27674, 2) :: (1, 1) :: repeat (1, 2) 323288 ++ w) 1)).
  {
    apply (sPOP1 [0] 4 4 (repeat (1, 2) 14 ++ (87, 2) :: (1, 1) :: repeat (1, 2) 228 ++ (45, 2) :: (1, 1) :: repeat (1, 2) 1174 ++ (22609, 2) :: (1, 1) :: repeat (1, 2) 50438 ++ (27674, 2) :: (1, 1) :: repeat (1, 2) 323288 ++ w) 1); closearith.
  }
  (* step 142: M pop12 (14,) *)
  apply (hsteps_trans _ (HB [0] 19 1 33 ((87, 2) :: (1, 1) :: repeat (1, 2) 228 ++ (45, 2) :: (1, 1) :: repeat (1, 2) 1174 ++ (22609, 2) :: (1, 1) :: repeat (1, 2) 50438 ++ (27674, 2) :: (1, 1) :: repeat (1, 2) 323288 ++ w) 1)).
  {
    apply (pop12 14 [0] 5 5 ((87, 2) :: (1, 1) :: repeat (1, 2) 228 ++ (45, 2) :: (1, 1) :: repeat (1, 2) 1174 ++ (22609, 2) :: (1, 1) :: repeat (1, 2) 50438 ++ (27674, 2) :: (1, 1) :: repeat (1, 2) 323288 ++ w) 1); closearith.
  }
  (* step 143: sTUP *)
  apply (hsteps_trans _ (HC [0] 19 32 2 ((85, 2) :: (1, 1) :: repeat (1, 2) 228 ++ (45, 2) :: (1, 1) :: repeat (1, 2) 1174 ++ (22609, 2) :: (1, 1) :: repeat (1, 2) 50438 ++ (27674, 2) :: (1, 1) :: repeat (1, 2) 323288 ++ w) 1)).
  {
    replace ((85, 2) :: (1, 1) :: repeat (1, 2) 228 ++ (45, 2) :: (1, 1) :: repeat (1, 2) 1174 ++ (22609, 2) :: (1, 1) :: repeat (1, 2) 50438 ++ (27674, 2) :: (1, 1) :: repeat (1, 2) 323288 ++ w) with ((87 - 2, 2) :: (1, 1) :: repeat (1, 2) 228 ++ (45, 2) :: (1, 1) :: repeat (1, 2) 1174 ++ (22609, 2) :: (1, 1) :: repeat (1, 2) 50438 ++ (27674, 2) :: (1, 1) :: repeat (1, 2) 323288 ++ w) by sec_eq.
    apply (sTUP [0] 19 33 87 2 ((1, 1) :: repeat (1, 2) 228 ++ (45, 2) :: (1, 1) :: repeat (1, 2) 1174 ++ (22609, 2) :: (1, 1) :: repeat (1, 2) 50438 ++ (27674, 2) :: (1, 1) :: repeat (1, 2) 323288 ++ w) 1); closearith.
  }
  (* step 144: hGRIND_even 14 *)
  apply (hsteps_trans _ (HB [0] 18 1 32 ((2, 2) :: (85, 2) :: (1, 1) :: repeat (1, 2) 228 ++ (45, 2) :: (1, 1) :: repeat (1, 2) 1174 ++ (22609, 2) :: (1, 1) :: repeat (1, 2) 50438 ++ (27674, 2) :: (1, 1) :: repeat (1, 2) 323288 ++ w) 1)).
  {
    apply (hGRIND_even 14 [0] 18 ((85, 2) :: (1, 1) :: repeat (1, 2) 228 ++ (45, 2) :: (1, 1) :: repeat (1, 2) 1174 ++ (22609, 2) :: (1, 1) :: repeat (1, 2) 50438 ++ (27674, 2) :: (1, 1) :: repeat (1, 2) 323288 ++ w) 1); closearith.
  }
  (* step 145: P TUP2_1 *)
  apply (hsteps_trans _ (HC [19; 0] 32 1 2 ((83, 2) :: (1, 1) :: repeat (1, 2) 228 ++ (45, 2) :: (1, 1) :: repeat (1, 2) 1174 ++ (22609, 2) :: (1, 1) :: repeat (1, 2) 50438 ++ (27674, 2) :: (1, 1) :: repeat (1, 2) 323288 ++ w) 1)).
  {
    replace ((83, 2) :: (1, 1) :: repeat (1, 2) 228 ++ (45, 2) :: (1, 1) :: repeat (1, 2) 1174 ++ (22609, 2) :: (1, 1) :: repeat (1, 2) 50438 ++ (27674, 2) :: (1, 1) :: repeat (1, 2) 323288 ++ w) with ((85 - 2, 2) :: (1, 1) :: repeat (1, 2) 228 ++ (45, 2) :: (1, 1) :: repeat (1, 2) 1174 ++ (22609, 2) :: (1, 1) :: repeat (1, 2) 50438 ++ (27674, 2) :: (1, 1) :: repeat (1, 2) 323288 ++ w) by sec_eq.
    apply (sTUP2_1 [0] 18 31 85 ((1, 1) :: repeat (1, 2) 228 ++ (45, 2) :: (1, 1) :: repeat (1, 2) 1174 ++ (22609, 2) :: (1, 1) :: repeat (1, 2) 50438 ++ (27674, 2) :: (1, 1) :: repeat (1, 2) 323288 ++ w) 1); closearith.
  }
  (* step 146: P TDN *)
  apply (hsteps_trans _ (HB [19; 0] 32 1 4 ((83, 2) :: (1, 1) :: repeat (1, 2) 228 ++ (45, 2) :: (1, 1) :: repeat (1, 2) 1174 ++ (22609, 2) :: (1, 1) :: repeat (1, 2) 50438 ++ (27674, 2) :: (1, 1) :: repeat (1, 2) 323288 ++ w) 1)).
  {
    apply (sTDN [19; 0] 32 ((83, 2) :: (1, 1) :: repeat (1, 2) 228 ++ (45, 2) :: (1, 1) :: repeat (1, 2) 1174 ++ (22609, 2) :: (1, 1) :: repeat (1, 2) 50438 ++ (27674, 2) :: (1, 1) :: repeat (1, 2) 323288 ++ w) 1).
  }
  (* step 147: sTUP *)
  apply (hsteps_trans _ (HC [19; 0] 32 3 2 ((81, 2) :: (1, 1) :: repeat (1, 2) 228 ++ (45, 2) :: (1, 1) :: repeat (1, 2) 1174 ++ (22609, 2) :: (1, 1) :: repeat (1, 2) 50438 ++ (27674, 2) :: (1, 1) :: repeat (1, 2) 323288 ++ w) 1)).
  {
    replace ((81, 2) :: (1, 1) :: repeat (1, 2) 228 ++ (45, 2) :: (1, 1) :: repeat (1, 2) 1174 ++ (22609, 2) :: (1, 1) :: repeat (1, 2) 50438 ++ (27674, 2) :: (1, 1) :: repeat (1, 2) 323288 ++ w) with ((83 - 2, 2) :: (1, 1) :: repeat (1, 2) 228 ++ (45, 2) :: (1, 1) :: repeat (1, 2) 1174 ++ (22609, 2) :: (1, 1) :: repeat (1, 2) 50438 ++ (27674, 2) :: (1, 1) :: repeat (1, 2) 323288 ++ w) by sec_eq.
    apply (sTUP [19; 0] 32 4 83 2 ((1, 1) :: repeat (1, 2) 228 ++ (45, 2) :: (1, 1) :: repeat (1, 2) 1174 ++ (22609, 2) :: (1, 1) :: repeat (1, 2) 50438 ++ (27674, 2) :: (1, 1) :: repeat (1, 2) 323288 ++ w) 1); closearith.
  }
  (* step 148: DIPGRIND 32 17 *)
  apply (hsteps_trans _ (HC [19; 0] 0 3 2 (repeat (1, 2) 32 ++ (17, 2) :: (1, 1) :: repeat (1, 2) 228 ++ (45, 2) :: (1, 1) :: repeat (1, 2) 1174 ++ (22609, 2) :: (1, 1) :: repeat (1, 2) 50438 ++ (27674, 2) :: (1, 1) :: repeat (1, 2) 323288 ++ w) 1)).
  {
    apply (DIPGRIND 32 17 [19; 0] ((1, 1) :: repeat (1, 2) 228 ++ (45, 2) :: (1, 1) :: repeat (1, 2) 1174 ++ (22609, 2) :: (1, 1) :: repeat (1, 2) 50438 ++ (27674, 2) :: (1, 1) :: repeat (1, 2) 323288 ++ w) 1); closearith.
  }
  (* step 149: P PX2A0 *)
  apply (hsteps_trans _ (HB [0] 3 1 2 ((15, 2) :: (1, 1) :: repeat (1, 2) 34 ++ (17, 2) :: (1, 1) :: repeat (1, 2) 228 ++ (45, 2) :: (1, 1) :: repeat (1, 2) 1174 ++ (22609, 2) :: (1, 1) :: repeat (1, 2) 50438 ++ (27674, 2) :: (1, 1) :: repeat (1, 2) 323288 ++ w) 1)).
  {
    apply (hsteps_step _ (HB [0] 3 1 2 ((15, 2) :: (1, 1) :: repeat (1, 2) 34 ++ (17, 2) :: (1, 1) :: repeat (1, 2) 228 ++ (45, 2) :: (1, 1) :: repeat (1, 2) 1174 ++ (22609, 2) :: (1, 1) :: repeat (1, 2) 50438 ++ (27674, 2) :: (1, 1) :: repeat (1, 2) 323288 ++ w) 1)); [apply hPX2A0 | apply hsteps_refl].
  }
  (* step 150: sTUP *)
  apply (hsteps_trans _ (HC [0] 3 1 2 ((13, 2) :: (1, 1) :: repeat (1, 2) 34 ++ (17, 2) :: (1, 1) :: repeat (1, 2) 228 ++ (45, 2) :: (1, 1) :: repeat (1, 2) 1174 ++ (22609, 2) :: (1, 1) :: repeat (1, 2) 50438 ++ (27674, 2) :: (1, 1) :: repeat (1, 2) 323288 ++ w) 1)).
  {
    replace ((13, 2) :: (1, 1) :: repeat (1, 2) 34 ++ (17, 2) :: (1, 1) :: repeat (1, 2) 228 ++ (45, 2) :: (1, 1) :: repeat (1, 2) 1174 ++ (22609, 2) :: (1, 1) :: repeat (1, 2) 50438 ++ (27674, 2) :: (1, 1) :: repeat (1, 2) 323288 ++ w) with ((15 - 2, 2) :: (1, 1) :: repeat (1, 2) 34 ++ (17, 2) :: (1, 1) :: repeat (1, 2) 228 ++ (45, 2) :: (1, 1) :: repeat (1, 2) 1174 ++ (22609, 2) :: (1, 1) :: repeat (1, 2) 50438 ++ (27674, 2) :: (1, 1) :: repeat (1, 2) 323288 ++ w) by sec_eq.
    apply (sTUP [0] 3 2 15 2 ((1, 1) :: repeat (1, 2) 34 ++ (17, 2) :: (1, 1) :: repeat (1, 2) 228 ++ (45, 2) :: (1, 1) :: repeat (1, 2) 1174 ++ (22609, 2) :: (1, 1) :: repeat (1, 2) 50438 ++ (27674, 2) :: (1, 1) :: repeat (1, 2) 323288 ++ w) 1); closearith.
  }
  (* step 151: P TDN *)
  apply (hsteps_trans _ (HB [0] 3 1 4 ((13, 2) :: (1, 1) :: repeat (1, 2) 34 ++ (17, 2) :: (1, 1) :: repeat (1, 2) 228 ++ (45, 2) :: (1, 1) :: repeat (1, 2) 1174 ++ (22609, 2) :: (1, 1) :: repeat (1, 2) 50438 ++ (27674, 2) :: (1, 1) :: repeat (1, 2) 323288 ++ w) 1)).
  {
    apply (sTDN [0] 3 ((13, 2) :: (1, 1) :: repeat (1, 2) 34 ++ (17, 2) :: (1, 1) :: repeat (1, 2) 228 ++ (45, 2) :: (1, 1) :: repeat (1, 2) 1174 ++ (22609, 2) :: (1, 1) :: repeat (1, 2) 50438 ++ (27674, 2) :: (1, 1) :: repeat (1, 2) 323288 ++ w) 1).
  }
  (* step 152: sTUP *)
  apply (hsteps_trans _ (HC [0] 3 3 2 ((11, 2) :: (1, 1) :: repeat (1, 2) 34 ++ (17, 2) :: (1, 1) :: repeat (1, 2) 228 ++ (45, 2) :: (1, 1) :: repeat (1, 2) 1174 ++ (22609, 2) :: (1, 1) :: repeat (1, 2) 50438 ++ (27674, 2) :: (1, 1) :: repeat (1, 2) 323288 ++ w) 1)).
  {
    replace ((11, 2) :: (1, 1) :: repeat (1, 2) 34 ++ (17, 2) :: (1, 1) :: repeat (1, 2) 228 ++ (45, 2) :: (1, 1) :: repeat (1, 2) 1174 ++ (22609, 2) :: (1, 1) :: repeat (1, 2) 50438 ++ (27674, 2) :: (1, 1) :: repeat (1, 2) 323288 ++ w) with ((13 - 2, 2) :: (1, 1) :: repeat (1, 2) 34 ++ (17, 2) :: (1, 1) :: repeat (1, 2) 228 ++ (45, 2) :: (1, 1) :: repeat (1, 2) 1174 ++ (22609, 2) :: (1, 1) :: repeat (1, 2) 50438 ++ (27674, 2) :: (1, 1) :: repeat (1, 2) 323288 ++ w) by sec_eq.
    apply (sTUP [0] 3 4 13 2 ((1, 1) :: repeat (1, 2) 34 ++ (17, 2) :: (1, 1) :: repeat (1, 2) 228 ++ (45, 2) :: (1, 1) :: repeat (1, 2) 1174 ++ (22609, 2) :: (1, 1) :: repeat (1, 2) 50438 ++ (27674, 2) :: (1, 1) :: repeat (1, 2) 323288 ++ w) 1); closearith.
  }
  (* step 153: DIPGRIND 3 5 *)
  apply (hsteps_trans _ (HC [0] 0 3 2 (repeat (1, 2) 3 ++ (5, 2) :: (1, 1) :: repeat (1, 2) 34 ++ (17, 2) :: (1, 1) :: repeat (1, 2) 228 ++ (45, 2) :: (1, 1) :: repeat (1, 2) 1174 ++ (22609, 2) :: (1, 1) :: repeat (1, 2) 50438 ++ (27674, 2) :: (1, 1) :: repeat (1, 2) 323288 ++ w) 1)).
  {
    apply (DIPGRIND 3 5 [0] ((1, 1) :: repeat (1, 2) 34 ++ (17, 2) :: (1, 1) :: repeat (1, 2) 228 ++ (45, 2) :: (1, 1) :: repeat (1, 2) 1174 ++ (22609, 2) :: (1, 1) :: repeat (1, 2) 50438 ++ (27674, 2) :: (1, 1) :: repeat (1, 2) 323288 ++ w) 1); closearith.
  }
  (* step 154: P PX2B0 *)
  apply (hsteps_trans _ (HB [] 0 1 5 (repeat (1, 2) 4 ++ (5, 2) :: (1, 1) :: repeat (1, 2) 34 ++ (17, 2) :: (1, 1) :: repeat (1, 2) 228 ++ (45, 2) :: (1, 1) :: repeat (1, 2) 1174 ++ (22609, 2) :: (1, 1) :: repeat (1, 2) 50438 ++ (27674, 2) :: (1, 1) :: repeat (1, 2) 323288 ++ w) 1)).
  {
    apply (hsteps_step _ (HB [] 0 1 5 (repeat (1, 2) 4 ++ (5, 2) :: (1, 1) :: repeat (1, 2) 34 ++ (17, 2) :: (1, 1) :: repeat (1, 2) 228 ++ (45, 2) :: (1, 1) :: repeat (1, 2) 1174 ++ (22609, 2) :: (1, 1) :: repeat (1, 2) 50438 ++ (27674, 2) :: (1, 1) :: repeat (1, 2) 323288 ++ w) 1)); [apply hPX2B0 | apply hsteps_refl].
  }
  (* step 155: M pop12 (4,) *)
  apply (hsteps_trans _ (HB [] 4 1 13 ((5, 2) :: (1, 1) :: repeat (1, 2) 34 ++ (17, 2) :: (1, 1) :: repeat (1, 2) 228 ++ (45, 2) :: (1, 1) :: repeat (1, 2) 1174 ++ (22609, 2) :: (1, 1) :: repeat (1, 2) 50438 ++ (27674, 2) :: (1, 1) :: repeat (1, 2) 323288 ++ w) 1)).
  {
    apply (pop12 4 [] 0 5 ((5, 2) :: (1, 1) :: repeat (1, 2) 34 ++ (17, 2) :: (1, 1) :: repeat (1, 2) 228 ++ (45, 2) :: (1, 1) :: repeat (1, 2) 1174 ++ (22609, 2) :: (1, 1) :: repeat (1, 2) 50438 ++ (27674, 2) :: (1, 1) :: repeat (1, 2) 323288 ++ w) 1); closearith.
  }
  (* step 156: sTUP *)
  apply (hsteps_trans _ (HC [] 4 12 2 ((3, 2) :: (1, 1) :: repeat (1, 2) 34 ++ (17, 2) :: (1, 1) :: repeat (1, 2) 228 ++ (45, 2) :: (1, 1) :: repeat (1, 2) 1174 ++ (22609, 2) :: (1, 1) :: repeat (1, 2) 50438 ++ (27674, 2) :: (1, 1) :: repeat (1, 2) 323288 ++ w) 1)).
  {
    replace ((3, 2) :: (1, 1) :: repeat (1, 2) 34 ++ (17, 2) :: (1, 1) :: repeat (1, 2) 228 ++ (45, 2) :: (1, 1) :: repeat (1, 2) 1174 ++ (22609, 2) :: (1, 1) :: repeat (1, 2) 50438 ++ (27674, 2) :: (1, 1) :: repeat (1, 2) 323288 ++ w) with ((5 - 2, 2) :: (1, 1) :: repeat (1, 2) 34 ++ (17, 2) :: (1, 1) :: repeat (1, 2) 228 ++ (45, 2) :: (1, 1) :: repeat (1, 2) 1174 ++ (22609, 2) :: (1, 1) :: repeat (1, 2) 50438 ++ (27674, 2) :: (1, 1) :: repeat (1, 2) 323288 ++ w) by sec_eq.
    apply (sTUP [] 4 13 5 2 ((1, 1) :: repeat (1, 2) 34 ++ (17, 2) :: (1, 1) :: repeat (1, 2) 228 ++ (45, 2) :: (1, 1) :: repeat (1, 2) 1174 ++ (22609, 2) :: (1, 1) :: repeat (1, 2) 50438 ++ (27674, 2) :: (1, 1) :: repeat (1, 2) 323288 ++ w) 1); closearith.
  }
  (* step 157: P PUSH *)
  apply (hsteps_trans _ (HC [] 3 1 2 ((10, 2) :: (3, 2) :: (1, 1) :: repeat (1, 2) 34 ++ (17, 2) :: (1, 1) :: repeat (1, 2) 228 ++ (45, 2) :: (1, 1) :: repeat (1, 2) 1174 ++ (22609, 2) :: (1, 1) :: repeat (1, 2) 50438 ++ (27674, 2) :: (1, 1) :: repeat (1, 2) 323288 ++ w) 1)).
  {
    replace ((10, 2) :: (3, 2) :: (1, 1) :: repeat (1, 2) 34 ++ (17, 2) :: (1, 1) :: repeat (1, 2) 228 ++ (45, 2) :: (1, 1) :: repeat (1, 2) 1174 ++ (22609, 2) :: (1, 1) :: repeat (1, 2) 50438 ++ (27674, 2) :: (1, 1) :: repeat (1, 2) 323288 ++ w) with ((12 - 2, 2) :: (3, 2) :: (1, 1) :: repeat (1, 2) 34 ++ (17, 2) :: (1, 1) :: repeat (1, 2) 228 ++ (45, 2) :: (1, 1) :: repeat (1, 2) 1174 ++ (22609, 2) :: (1, 1) :: repeat (1, 2) 50438 ++ (27674, 2) :: (1, 1) :: repeat (1, 2) 323288 ++ w) by sec_eq.
    apply (sPUSH [] 3 12 ((3, 2) :: (1, 1) :: repeat (1, 2) 34 ++ (17, 2) :: (1, 1) :: repeat (1, 2) 228 ++ (45, 2) :: (1, 1) :: repeat (1, 2) 1174 ++ (22609, 2) :: (1, 1) :: repeat (1, 2) 50438 ++ (27674, 2) :: (1, 1) :: repeat (1, 2) 323288 ++ w) 1); closearith.
  }
  (* step 158: P TDN *)
  apply (hsteps_trans _ (HB [] 3 1 4 ((10, 2) :: (3, 2) :: (1, 1) :: repeat (1, 2) 34 ++ (17, 2) :: (1, 1) :: repeat (1, 2) 228 ++ (45, 2) :: (1, 1) :: repeat (1, 2) 1174 ++ (22609, 2) :: (1, 1) :: repeat (1, 2) 50438 ++ (27674, 2) :: (1, 1) :: repeat (1, 2) 323288 ++ w) 1)).
  {
    apply (sTDN [] 3 ((10, 2) :: (3, 2) :: (1, 1) :: repeat (1, 2) 34 ++ (17, 2) :: (1, 1) :: repeat (1, 2) 228 ++ (45, 2) :: (1, 1) :: repeat (1, 2) 1174 ++ (22609, 2) :: (1, 1) :: repeat (1, 2) 50438 ++ (27674, 2) :: (1, 1) :: repeat (1, 2) 323288 ++ w) 1).
  }
  (* step 159: sTUP *)
  apply (hsteps_trans _ (HC [] 3 3 2 ((8, 2) :: (3, 2) :: (1, 1) :: repeat (1, 2) 34 ++ (17, 2) :: (1, 1) :: repeat (1, 2) 228 ++ (45, 2) :: (1, 1) :: repeat (1, 2) 1174 ++ (22609, 2) :: (1, 1) :: repeat (1, 2) 50438 ++ (27674, 2) :: (1, 1) :: repeat (1, 2) 323288 ++ w) 1)).
  {
    replace ((8, 2) :: (3, 2) :: (1, 1) :: repeat (1, 2) 34 ++ (17, 2) :: (1, 1) :: repeat (1, 2) 228 ++ (45, 2) :: (1, 1) :: repeat (1, 2) 1174 ++ (22609, 2) :: (1, 1) :: repeat (1, 2) 50438 ++ (27674, 2) :: (1, 1) :: repeat (1, 2) 323288 ++ w) with ((10 - 2, 2) :: (3, 2) :: (1, 1) :: repeat (1, 2) 34 ++ (17, 2) :: (1, 1) :: repeat (1, 2) 228 ++ (45, 2) :: (1, 1) :: repeat (1, 2) 1174 ++ (22609, 2) :: (1, 1) :: repeat (1, 2) 50438 ++ (27674, 2) :: (1, 1) :: repeat (1, 2) 323288 ++ w) by sec_eq.
    apply (sTUP [] 3 4 10 2 ((3, 2) :: (1, 1) :: repeat (1, 2) 34 ++ (17, 2) :: (1, 1) :: repeat (1, 2) 228 ++ (45, 2) :: (1, 1) :: repeat (1, 2) 1174 ++ (22609, 2) :: (1, 1) :: repeat (1, 2) 50438 ++ (27674, 2) :: (1, 1) :: repeat (1, 2) 323288 ++ w) 1); closearith.
  }
  (* step 160: DIPGRIND 3 2 *)
  apply (hsteps_trans _ (HC [] 0 3 2 (repeat (1, 2) 3 ++ (2, 2) :: (3, 2) :: (1, 1) :: repeat (1, 2) 34 ++ (17, 2) :: (1, 1) :: repeat (1, 2) 228 ++ (45, 2) :: (1, 1) :: repeat (1, 2) 1174 ++ (22609, 2) :: (1, 1) :: repeat (1, 2) 50438 ++ (27674, 2) :: (1, 1) :: repeat (1, 2) 323288 ++ w) 1)).
  {
    apply (DIPGRIND 3 2 [] ((3, 2) :: (1, 1) :: repeat (1, 2) 34 ++ (17, 2) :: (1, 1) :: repeat (1, 2) 228 ++ (45, 2) :: (1, 1) :: repeat (1, 2) 1174 ++ (22609, 2) :: (1, 1) :: repeat (1, 2) 50438 ++ (27674, 2) :: (1, 1) :: repeat (1, 2) 323288 ++ w) 1); closearith.
  }
  (* step 161: P PUSHX *)
  apply (hsteps_trans _ (HB [] 1 1 7 (repeat (1, 2) 3 ++ (2, 2) :: (3, 2) :: (1, 1) :: repeat (1, 2) 34 ++ (17, 2) :: (1, 1) :: repeat (1, 2) 228 ++ (45, 2) :: (1, 1) :: repeat (1, 2) 1174 ++ (22609, 2) :: (1, 1) :: repeat (1, 2) 50438 ++ (27674, 2) :: (1, 1) :: repeat (1, 2) 323288 ++ w) 1)).
  {
    apply (hsteps_step _ (HB [] 1 1 7 (repeat (1, 2) 3 ++ (2, 2) :: (3, 2) :: (1, 1) :: repeat (1, 2) 34 ++ (17, 2) :: (1, 1) :: repeat (1, 2) 228 ++ (45, 2) :: (1, 1) :: repeat (1, 2) 1174 ++ (22609, 2) :: (1, 1) :: repeat (1, 2) 50438 ++ (27674, 2) :: (1, 1) :: repeat (1, 2) 323288 ++ w) 1)); [apply hPUSHX | apply hsteps_refl].
  }
  (* step 162: M pop12 (3,) *)
  apply (hsteps_trans _ (HB [] 4 1 13 ((2, 2) :: (3, 2) :: (1, 1) :: repeat (1, 2) 34 ++ (17, 2) :: (1, 1) :: repeat (1, 2) 228 ++ (45, 2) :: (1, 1) :: repeat (1, 2) 1174 ++ (22609, 2) :: (1, 1) :: repeat (1, 2) 50438 ++ (27674, 2) :: (1, 1) :: repeat (1, 2) 323288 ++ w) 1)).
  {
    apply (pop12 3 [] 1 7 ((2, 2) :: (3, 2) :: (1, 1) :: repeat (1, 2) 34 ++ (17, 2) :: (1, 1) :: repeat (1, 2) 228 ++ (45, 2) :: (1, 1) :: repeat (1, 2) 1174 ++ (22609, 2) :: (1, 1) :: repeat (1, 2) 50438 ++ (27674, 2) :: (1, 1) :: repeat (1, 2) 323288 ++ w) 1); closearith.
  }
  (* step 163: P TUP2_1 *)
  apply (hsteps_trans _ (HC [5] 13 1 2 (repeat (1, 2) 1 ++ (1, 1) :: repeat (1, 2) 34 ++ (17, 2) :: (1, 1) :: repeat (1, 2) 228 ++ (45, 2) :: (1, 1) :: repeat (1, 2) 1174 ++ (22609, 2) :: (1, 1) :: repeat (1, 2) 50438 ++ (27674, 2) :: (1, 1) :: repeat (1, 2) 323288 ++ w) 1)).
  {
    replace (repeat (1, 2) 1 ++ (1, 1) :: repeat (1, 2) 34 ++ (17, 2) :: (1, 1) :: repeat (1, 2) 228 ++ (45, 2) :: (1, 1) :: repeat (1, 2) 1174 ++ (22609, 2) :: (1, 1) :: repeat (1, 2) 50438 ++ (27674, 2) :: (1, 1) :: repeat (1, 2) 323288 ++ w) with ((3 - 2, 2) :: (1, 1) :: repeat (1, 2) 34 ++ (17, 2) :: (1, 1) :: repeat (1, 2) 228 ++ (45, 2) :: (1, 1) :: repeat (1, 2) 1174 ++ (22609, 2) :: (1, 1) :: repeat (1, 2) 50438 ++ (27674, 2) :: (1, 1) :: repeat (1, 2) 323288 ++ w) by sec_eq.
    apply (sTUP2_1 [] 4 12 3 ((1, 1) :: repeat (1, 2) 34 ++ (17, 2) :: (1, 1) :: repeat (1, 2) 228 ++ (45, 2) :: (1, 1) :: repeat (1, 2) 1174 ++ (22609, 2) :: (1, 1) :: repeat (1, 2) 50438 ++ (27674, 2) :: (1, 1) :: repeat (1, 2) 323288 ++ w) 1); closearith.
  }
  (* step 164: P TDN *)
  apply (hsteps_trans _ (HB [5] 13 1 4 (repeat (1, 2) 1 ++ (1, 1) :: repeat (1, 2) 34 ++ (17, 2) :: (1, 1) :: repeat (1, 2) 228 ++ (45, 2) :: (1, 1) :: repeat (1, 2) 1174 ++ (22609, 2) :: (1, 1) :: repeat (1, 2) 50438 ++ (27674, 2) :: (1, 1) :: repeat (1, 2) 323288 ++ w) 1)).
  {
    apply (sTDN [5] 13 (repeat (1, 2) 1 ++ (1, 1) :: repeat (1, 2) 34 ++ (17, 2) :: (1, 1) :: repeat (1, 2) 228 ++ (45, 2) :: (1, 1) :: repeat (1, 2) 1174 ++ (22609, 2) :: (1, 1) :: repeat (1, 2) 50438 ++ (27674, 2) :: (1, 1) :: repeat (1, 2) 323288 ++ w) 1).
  }
  (* step 165: M pop12 (1,) *)
  apply (hsteps_trans _ (HB [5] 14 1 6 ((1, 1) :: repeat (1, 2) 34 ++ (17, 2) :: (1, 1) :: repeat (1, 2) 228 ++ (45, 2) :: (1, 1) :: repeat (1, 2) 1174 ++ (22609, 2) :: (1, 1) :: repeat (1, 2) 50438 ++ (27674, 2) :: (1, 1) :: repeat (1, 2) 323288 ++ w) 1)).
  {
    apply (pop12 1 [5] 13 4 ((1, 1) :: repeat (1, 2) 34 ++ (17, 2) :: (1, 1) :: repeat (1, 2) 228 ++ (45, 2) :: (1, 1) :: repeat (1, 2) 1174 ++ (22609, 2) :: (1, 1) :: repeat (1, 2) 50438 ++ (27674, 2) :: (1, 1) :: repeat (1, 2) 323288 ++ w) 1); closearith.
  }
  (* step 166: P POP *)
  apply (hsteps_trans _ (HB [5] 15 1 7 (repeat (1, 2) 34 ++ (17, 2) :: (1, 1) :: repeat (1, 2) 228 ++ (45, 2) :: (1, 1) :: repeat (1, 2) 1174 ++ (22609, 2) :: (1, 1) :: repeat (1, 2) 50438 ++ (27674, 2) :: (1, 1) :: repeat (1, 2) 323288 ++ w) 1)).
  {
    apply (sPOP1 [5] 14 6 (repeat (1, 2) 34 ++ (17, 2) :: (1, 1) :: repeat (1, 2) 228 ++ (45, 2) :: (1, 1) :: repeat (1, 2) 1174 ++ (22609, 2) :: (1, 1) :: repeat (1, 2) 50438 ++ (27674, 2) :: (1, 1) :: repeat (1, 2) 323288 ++ w) 1); closearith.
  }
  (* step 167: M pop12 (34,) *)
  apply (hsteps_trans _ (HB [5] 49 1 75 ((17, 2) :: (1, 1) :: repeat (1, 2) 228 ++ (45, 2) :: (1, 1) :: repeat (1, 2) 1174 ++ (22609, 2) :: (1, 1) :: repeat (1, 2) 50438 ++ (27674, 2) :: (1, 1) :: repeat (1, 2) 323288 ++ w) 1)).
  {
    apply (pop12 34 [5] 15 7 ((17, 2) :: (1, 1) :: repeat (1, 2) 228 ++ (45, 2) :: (1, 1) :: repeat (1, 2) 1174 ++ (22609, 2) :: (1, 1) :: repeat (1, 2) 50438 ++ (27674, 2) :: (1, 1) :: repeat (1, 2) 323288 ++ w) 1); closearith.
  }
  (* step 168: sTUP *)
  replace ((15, 2) :: (1, 1) :: repeat (1, 2) 228 ++ (45, 2) :: (1, 1) :: repeat (1, 2) 1174 ++ (22609, 2) :: (1, 1) :: repeat (1, 2) 50438 ++ (27674, 2) :: (1, 1) :: repeat (1, 2) 323288 ++ w) with ((17 - 2, 2) :: (1, 1) :: repeat (1, 2) 228 ++ (45, 2) :: (1, 1) :: repeat (1, 2) 1174 ++ (22609, 2) :: (1, 1) :: repeat (1, 2) 50438 ++ (27674, 2) :: (1, 1) :: repeat (1, 2) 323288 ++ w) by sec_eq.
  apply (sTUP [5] 49 75 17 2 ((1, 1) :: repeat (1, 2) 228 ++ (45, 2) :: (1, 1) :: repeat (1, 2) 1174 ++ (22609, 2) :: (1, 1) :: repeat (1, 2) 50438 ++ (27674, 2) :: (1, 1) :: repeat (1, 2) 323288 ++ w) 1); closearith.
Qed.

(* CASCADE53d: steps 169-224 of the CASCADE53 chain. *)
Lemma CASCADE53d : forall w,
  hsteps (HC [5] 49 74 2 ((15, 2) :: (1, 1) :: repeat (1, 2) 228 ++ (45, 2) :: (1, 1) :: repeat (1, 2) 1174 ++ (22609, 2) :: (1, 1) :: repeat (1, 2) 50438 ++ (27674, 2) :: (1, 1) :: repeat (1, 2) 323288 ++ w) 1)
         (HB [20; 0] 36 1 7 (repeat (1, 2) 304 ++ (1040, 2) :: (1, 1) :: repeat (1, 2) 2396 ++ (17815, 2) :: (1, 1) :: repeat (1, 2) 50438 ++ (27674, 2) :: (1, 1) :: repeat (1, 2) 323288 ++ w) 1).
Proof.
  intro w.
  (* step 169: hGRIND_even 35 *)
  apply (hsteps_trans _ (HB [5] 48 1 74 ((2, 2) :: (15, 2) :: (1, 1) :: repeat (1, 2) 228 ++ (45, 2) :: (1, 1) :: repeat (1, 2) 1174 ++ (22609, 2) :: (1, 1) :: repeat (1, 2) 50438 ++ (27674, 2) :: (1, 1) :: repeat (1, 2) 323288 ++ w) 1)).
  {
    apply (hGRIND_even 35 [5] 48 ((15, 2) :: (1, 1) :: repeat (1, 2) 228 ++ (45, 2) :: (1, 1) :: repeat (1, 2) 1174 ++ (22609, 2) :: (1, 1) :: repeat (1, 2) 50438 ++ (27674, 2) :: (1, 1) :: repeat (1, 2) 323288 ++ w) 1); closearith.
  }
  (* step 170: P TUP2_1 *)
  apply (hsteps_trans _ (HC [49; 5] 74 1 2 ((13, 2) :: (1, 1) :: repeat (1, 2) 228 ++ (45, 2) :: (1, 1) :: repeat (1, 2) 1174 ++ (22609, 2) :: (1, 1) :: repeat (1, 2) 50438 ++ (27674, 2) :: (1, 1) :: repeat (1, 2) 323288 ++ w) 1)).
  {
    replace ((13, 2) :: (1, 1) :: repeat (1, 2) 228 ++ (45, 2) :: (1, 1) :: repeat (1, 2) 1174 ++ (22609, 2) :: (1, 1) :: repeat (1, 2) 50438 ++ (27674, 2) :: (1, 1) :: repeat (1, 2) 323288 ++ w) with ((15 - 2, 2) :: (1, 1) :: repeat (1, 2) 228 ++ (45, 2) :: (1, 1) :: repeat (1, 2) 1174 ++ (22609, 2) :: (1, 1) :: repeat (1, 2) 50438 ++ (27674, 2) :: (1, 1) :: repeat (1, 2) 323288 ++ w) by sec_eq.
    apply (sTUP2_1 [5] 48 73 15 ((1, 1) :: repeat (1, 2) 228 ++ (45, 2) :: (1, 1) :: repeat (1, 2) 1174 ++ (22609, 2) :: (1, 1) :: repeat (1, 2) 50438 ++ (27674, 2) :: (1, 1) :: repeat (1, 2) 323288 ++ w) 1); closearith.
  }
  (* step 171: P TDN *)
  apply (hsteps_trans _ (HB [49; 5] 74 1 4 ((13, 2) :: (1, 1) :: repeat (1, 2) 228 ++ (45, 2) :: (1, 1) :: repeat (1, 2) 1174 ++ (22609, 2) :: (1, 1) :: repeat (1, 2) 50438 ++ (27674, 2) :: (1, 1) :: repeat (1, 2) 323288 ++ w) 1)).
  {
    apply (sTDN [49; 5] 74 ((13, 2) :: (1, 1) :: repeat (1, 2) 228 ++ (45, 2) :: (1, 1) :: repeat (1, 2) 1174 ++ (22609, 2) :: (1, 1) :: repeat (1, 2) 50438 ++ (27674, 2) :: (1, 1) :: repeat (1, 2) 323288 ++ w) 1).
  }
  (* step 172: sTUP *)
  apply (hsteps_trans _ (HC [49; 5] 74 3 2 ((11, 2) :: (1, 1) :: repeat (1, 2) 228 ++ (45, 2) :: (1, 1) :: repeat (1, 2) 1174 ++ (22609, 2) :: (1, 1) :: repeat (1, 2) 50438 ++ (27674, 2) :: (1, 1) :: repeat (1, 2) 323288 ++ w) 1)).
  {
    replace ((11, 2) :: (1, 1) :: repeat (1, 2) 228 ++ (45, 2) :: (1, 1) :: repeat (1, 2) 1174 ++ (22609, 2) :: (1, 1) :: repeat (1, 2) 50438 ++ (27674, 2) :: (1, 1) :: repeat (1, 2) 323288 ++ w) with ((13 - 2, 2) :: (1, 1) :: repeat (1, 2) 228 ++ (45, 2) :: (1, 1) :: repeat (1, 2) 1174 ++ (22609, 2) :: (1, 1) :: repeat (1, 2) 50438 ++ (27674, 2) :: (1, 1) :: repeat (1, 2) 323288 ++ w) by sec_eq.
    apply (sTUP [49; 5] 74 4 13 2 ((1, 1) :: repeat (1, 2) 228 ++ (45, 2) :: (1, 1) :: repeat (1, 2) 1174 ++ (22609, 2) :: (1, 1) :: repeat (1, 2) 50438 ++ (27674, 2) :: (1, 1) :: repeat (1, 2) 323288 ++ w) 1); closearith.
  }
  (* step 173: CLEANG_odd 4 *)
  apply (hsteps_trans _ (HB [49; 5] 74 1 16 (repeat (1, 2) 1 ++ (1, 1) :: repeat (1, 2) 228 ++ (45, 2) :: (1, 1) :: repeat (1, 2) 1174 ++ (22609, 2) :: (1, 1) :: repeat (1, 2) 50438 ++ (27674, 2) :: (1, 1) :: repeat (1, 2) 323288 ++ w) 1)).
  {
    replace (repeat (1, 2) 1 ++ (1, 1) :: repeat (1, 2) 228 ++ (45, 2) :: (1, 1) :: repeat (1, 2) 1174 ++ (22609, 2) :: (1, 1) :: repeat (1, 2) 50438 ++ (27674, 2) :: (1, 1) :: repeat (1, 2) 323288 ++ w) with ((1, 2) :: (1, 1) :: repeat (1, 2) 228 ++ (45, 2) :: (1, 1) :: repeat (1, 2) 1174 ++ (22609, 2) :: (1, 1) :: repeat (1, 2) 50438 ++ (27674, 2) :: (1, 1) :: repeat (1, 2) 323288 ++ w) by sec_eq.
    apply (CLEANG_odd 4 [49; 5] 74 ((1, 1) :: repeat (1, 2) 228 ++ (45, 2) :: (1, 1) :: repeat (1, 2) 1174 ++ (22609, 2) :: (1, 1) :: repeat (1, 2) 50438 ++ (27674, 2) :: (1, 1) :: repeat (1, 2) 323288 ++ w) 1); closearith.
  }
  (* step 174: M pop12 (1,) *)
  apply (hsteps_trans _ (HB [49; 5] 75 1 18 ((1, 1) :: repeat (1, 2) 228 ++ (45, 2) :: (1, 1) :: repeat (1, 2) 1174 ++ (22609, 2) :: (1, 1) :: repeat (1, 2) 50438 ++ (27674, 2) :: (1, 1) :: repeat (1, 2) 323288 ++ w) 1)).
  {
    apply (pop12 1 [49; 5] 74 16 ((1, 1) :: repeat (1, 2) 228 ++ (45, 2) :: (1, 1) :: repeat (1, 2) 1174 ++ (22609, 2) :: (1, 1) :: repeat (1, 2) 50438 ++ (27674, 2) :: (1, 1) :: repeat (1, 2) 323288 ++ w) 1); closearith.
  }
  (* step 175: P POP *)
  apply (hsteps_trans _ (HB [49; 5] 76 1 19 (repeat (1, 2) 228 ++ (45, 2) :: (1, 1) :: repeat (1, 2) 1174 ++ (22609, 2) :: (1, 1) :: repeat (1, 2) 50438 ++ (27674, 2) :: (1, 1) :: repeat (1, 2) 323288 ++ w) 1)).
  {
    apply (sPOP1 [49; 5] 75 18 (repeat (1, 2) 228 ++ (45, 2) :: (1, 1) :: repeat (1, 2) 1174 ++ (22609, 2) :: (1, 1) :: repeat (1, 2) 50438 ++ (27674, 2) :: (1, 1) :: repeat (1, 2) 323288 ++ w) 1); closearith.
  }
  (* step 176: M pop12 (228,) *)
  apply (hsteps_trans _ (HB [49; 5] 304 1 475 ((45, 2) :: (1, 1) :: repeat (1, 2) 1174 ++ (22609, 2) :: (1, 1) :: repeat (1, 2) 50438 ++ (27674, 2) :: (1, 1) :: repeat (1, 2) 323288 ++ w) 1)).
  {
    apply (pop12 228 [49; 5] 76 19 ((45, 2) :: (1, 1) :: repeat (1, 2) 1174 ++ (22609, 2) :: (1, 1) :: repeat (1, 2) 50438 ++ (27674, 2) :: (1, 1) :: repeat (1, 2) 323288 ++ w) 1); closearith.
  }
  (* step 177: sTUP *)
  apply (hsteps_trans _ (HC [49; 5] 304 474 2 ((43, 2) :: (1, 1) :: repeat (1, 2) 1174 ++ (22609, 2) :: (1, 1) :: repeat (1, 2) 50438 ++ (27674, 2) :: (1, 1) :: repeat (1, 2) 323288 ++ w) 1)).
  {
    replace ((43, 2) :: (1, 1) :: repeat (1, 2) 1174 ++ (22609, 2) :: (1, 1) :: repeat (1, 2) 50438 ++ (27674, 2) :: (1, 1) :: repeat (1, 2) 323288 ++ w) with ((45 - 2, 2) :: (1, 1) :: repeat (1, 2) 1174 ++ (22609, 2) :: (1, 1) :: repeat (1, 2) 50438 ++ (27674, 2) :: (1, 1) :: repeat (1, 2) 323288 ++ w) by sec_eq.
    apply (sTUP [49; 5] 304 475 45 2 ((1, 1) :: repeat (1, 2) 1174 ++ (22609, 2) :: (1, 1) :: repeat (1, 2) 50438 ++ (27674, 2) :: (1, 1) :: repeat (1, 2) 323288 ++ w) 1); closearith.
  }
  (* step 178: hGRIND_even 235 *)
  apply (hsteps_trans _ (HB [49; 5] 303 1 474 ((2, 2) :: (43, 2) :: (1, 1) :: repeat (1, 2) 1174 ++ (22609, 2) :: (1, 1) :: repeat (1, 2) 50438 ++ (27674, 2) :: (1, 1) :: repeat (1, 2) 323288 ++ w) 1)).
  {
    apply (hGRIND_even 235 [49; 5] 303 ((43, 2) :: (1, 1) :: repeat (1, 2) 1174 ++ (22609, 2) :: (1, 1) :: repeat (1, 2) 50438 ++ (27674, 2) :: (1, 1) :: repeat (1, 2) 323288 ++ w) 1); closearith.
  }
  (* step 179: P TUP2_1 *)
  apply (hsteps_trans _ (HC [304; 49; 5] 474 1 2 ((41, 2) :: (1, 1) :: repeat (1, 2) 1174 ++ (22609, 2) :: (1, 1) :: repeat (1, 2) 50438 ++ (27674, 2) :: (1, 1) :: repeat (1, 2) 323288 ++ w) 1)).
  {
    replace ((41, 2) :: (1, 1) :: repeat (1, 2) 1174 ++ (22609, 2) :: (1, 1) :: repeat (1, 2) 50438 ++ (27674, 2) :: (1, 1) :: repeat (1, 2) 323288 ++ w) with ((43 - 2, 2) :: (1, 1) :: repeat (1, 2) 1174 ++ (22609, 2) :: (1, 1) :: repeat (1, 2) 50438 ++ (27674, 2) :: (1, 1) :: repeat (1, 2) 323288 ++ w) by sec_eq.
    apply (sTUP2_1 [49; 5] 303 473 43 ((1, 1) :: repeat (1, 2) 1174 ++ (22609, 2) :: (1, 1) :: repeat (1, 2) 50438 ++ (27674, 2) :: (1, 1) :: repeat (1, 2) 323288 ++ w) 1); closearith.
  }
  (* step 180: P TDN *)
  apply (hsteps_trans _ (HB [304; 49; 5] 474 1 4 ((41, 2) :: (1, 1) :: repeat (1, 2) 1174 ++ (22609, 2) :: (1, 1) :: repeat (1, 2) 50438 ++ (27674, 2) :: (1, 1) :: repeat (1, 2) 323288 ++ w) 1)).
  {
    apply (sTDN [304; 49; 5] 474 ((41, 2) :: (1, 1) :: repeat (1, 2) 1174 ++ (22609, 2) :: (1, 1) :: repeat (1, 2) 50438 ++ (27674, 2) :: (1, 1) :: repeat (1, 2) 323288 ++ w) 1).
  }
  (* step 181: sTUP *)
  apply (hsteps_trans _ (HC [304; 49; 5] 474 3 2 ((39, 2) :: (1, 1) :: repeat (1, 2) 1174 ++ (22609, 2) :: (1, 1) :: repeat (1, 2) 50438 ++ (27674, 2) :: (1, 1) :: repeat (1, 2) 323288 ++ w) 1)).
  {
    replace ((39, 2) :: (1, 1) :: repeat (1, 2) 1174 ++ (22609, 2) :: (1, 1) :: repeat (1, 2) 50438 ++ (27674, 2) :: (1, 1) :: repeat (1, 2) 323288 ++ w) with ((41 - 2, 2) :: (1, 1) :: repeat (1, 2) 1174 ++ (22609, 2) :: (1, 1) :: repeat (1, 2) 50438 ++ (27674, 2) :: (1, 1) :: repeat (1, 2) 323288 ++ w) by sec_eq.
    apply (sTUP [304; 49; 5] 474 4 41 2 ((1, 1) :: repeat (1, 2) 1174 ++ (22609, 2) :: (1, 1) :: repeat (1, 2) 50438 ++ (27674, 2) :: (1, 1) :: repeat (1, 2) 323288 ++ w) 1); closearith.
  }
  (* step 182: CLEANG_odd 18 *)
  apply (hsteps_trans _ (HB [304; 49; 5] 474 1 44 (repeat (1, 2) 1 ++ (1, 1) :: repeat (1, 2) 1174 ++ (22609, 2) :: (1, 1) :: repeat (1, 2) 50438 ++ (27674, 2) :: (1, 1) :: repeat (1, 2) 323288 ++ w) 1)).
  {
    replace (repeat (1, 2) 1 ++ (1, 1) :: repeat (1, 2) 1174 ++ (22609, 2) :: (1, 1) :: repeat (1, 2) 50438 ++ (27674, 2) :: (1, 1) :: repeat (1, 2) 323288 ++ w) with ((1, 2) :: (1, 1) :: repeat (1, 2) 1174 ++ (22609, 2) :: (1, 1) :: repeat (1, 2) 50438 ++ (27674, 2) :: (1, 1) :: repeat (1, 2) 323288 ++ w) by sec_eq.
    apply (CLEANG_odd 18 [304; 49; 5] 474 ((1, 1) :: repeat (1, 2) 1174 ++ (22609, 2) :: (1, 1) :: repeat (1, 2) 50438 ++ (27674, 2) :: (1, 1) :: repeat (1, 2) 323288 ++ w) 1); closearith.
  }
  (* step 183: M pop12 (1,) *)
  apply (hsteps_trans _ (HB [304; 49; 5] 475 1 46 ((1, 1) :: repeat (1, 2) 1174 ++ (22609, 2) :: (1, 1) :: repeat (1, 2) 50438 ++ (27674, 2) :: (1, 1) :: repeat (1, 2) 323288 ++ w) 1)).
  {
    apply (pop12 1 [304; 49; 5] 474 44 ((1, 1) :: repeat (1, 2) 1174 ++ (22609, 2) :: (1, 1) :: repeat (1, 2) 50438 ++ (27674, 2) :: (1, 1) :: repeat (1, 2) 323288 ++ w) 1); closearith.
  }
  (* step 184: P POP *)
  apply (hsteps_trans _ (HB [304; 49; 5] 476 1 47 (repeat (1, 2) 1174 ++ (22609, 2) :: (1, 1) :: repeat (1, 2) 50438 ++ (27674, 2) :: (1, 1) :: repeat (1, 2) 323288 ++ w) 1)).
  {
    apply (sPOP1 [304; 49; 5] 475 46 (repeat (1, 2) 1174 ++ (22609, 2) :: (1, 1) :: repeat (1, 2) 50438 ++ (27674, 2) :: (1, 1) :: repeat (1, 2) 323288 ++ w) 1); closearith.
  }
  (* step 185: M pop12 (1174,) *)
  apply (hsteps_trans _ (HB [304; 49; 5] 1650 1 2395 ((22609, 2) :: (1, 1) :: repeat (1, 2) 50438 ++ (27674, 2) :: (1, 1) :: repeat (1, 2) 323288 ++ w) 1)).
  {
    apply (pop12 1174 [304; 49; 5] 476 47 ((22609, 2) :: (1, 1) :: repeat (1, 2) 50438 ++ (27674, 2) :: (1, 1) :: repeat (1, 2) 323288 ++ w) 1); closearith.
  }
  (* step 186: sTUP *)
  apply (hsteps_trans _ (HC [304; 49; 5] 1650 2394 2 ((22607, 2) :: (1, 1) :: repeat (1, 2) 50438 ++ (27674, 2) :: (1, 1) :: repeat (1, 2) 323288 ++ w) 1)).
  {
    replace ((22607, 2) :: (1, 1) :: repeat (1, 2) 50438 ++ (27674, 2) :: (1, 1) :: repeat (1, 2) 323288 ++ w) with ((22609 - 2, 2) :: (1, 1) :: repeat (1, 2) 50438 ++ (27674, 2) :: (1, 1) :: repeat (1, 2) 323288 ++ w) by sec_eq.
    apply (sTUP [304; 49; 5] 1650 2395 22609 2 ((1, 1) :: repeat (1, 2) 50438 ++ (27674, 2) :: (1, 1) :: repeat (1, 2) 323288 ++ w) 1); closearith.
  }
  (* step 187: hGRIND_even 1195 *)
  apply (hsteps_trans _ (HB [304; 49; 5] 1649 1 2394 ((2, 2) :: (22607, 2) :: (1, 1) :: repeat (1, 2) 50438 ++ (27674, 2) :: (1, 1) :: repeat (1, 2) 323288 ++ w) 1)).
  {
    apply (hGRIND_even 1195 [304; 49; 5] 1649 ((22607, 2) :: (1, 1) :: repeat (1, 2) 50438 ++ (27674, 2) :: (1, 1) :: repeat (1, 2) 323288 ++ w) 1); closearith.
  }
  (* step 188: P TUP2_1 *)
  apply (hsteps_trans _ (HC [1650; 304; 49; 5] 2394 1 2 ((22605, 2) :: (1, 1) :: repeat (1, 2) 50438 ++ (27674, 2) :: (1, 1) :: repeat (1, 2) 323288 ++ w) 1)).
  {
    replace ((22605, 2) :: (1, 1) :: repeat (1, 2) 50438 ++ (27674, 2) :: (1, 1) :: repeat (1, 2) 323288 ++ w) with ((22607 - 2, 2) :: (1, 1) :: repeat (1, 2) 50438 ++ (27674, 2) :: (1, 1) :: repeat (1, 2) 323288 ++ w) by sec_eq.
    apply (sTUP2_1 [304; 49; 5] 1649 2393 22607 ((1, 1) :: repeat (1, 2) 50438 ++ (27674, 2) :: (1, 1) :: repeat (1, 2) 323288 ++ w) 1); closearith.
  }
  (* step 189: P TDN *)
  apply (hsteps_trans _ (HB [1650; 304; 49; 5] 2394 1 4 ((22605, 2) :: (1, 1) :: repeat (1, 2) 50438 ++ (27674, 2) :: (1, 1) :: repeat (1, 2) 323288 ++ w) 1)).
  {
    apply (sTDN [1650; 304; 49; 5] 2394 ((22605, 2) :: (1, 1) :: repeat (1, 2) 50438 ++ (27674, 2) :: (1, 1) :: repeat (1, 2) 323288 ++ w) 1).
  }
  (* step 190: sTUP *)
  apply (hsteps_trans _ (HC [1650; 304; 49; 5] 2394 3 2 ((22603, 2) :: (1, 1) :: repeat (1, 2) 50438 ++ (27674, 2) :: (1, 1) :: repeat (1, 2) 323288 ++ w) 1)).
  {
    replace ((22603, 2) :: (1, 1) :: repeat (1, 2) 50438 ++ (27674, 2) :: (1, 1) :: repeat (1, 2) 323288 ++ w) with ((22605 - 2, 2) :: (1, 1) :: repeat (1, 2) 50438 ++ (27674, 2) :: (1, 1) :: repeat (1, 2) 323288 ++ w) by sec_eq.
    apply (sTUP [1650; 304; 49; 5] 2394 4 22605 2 ((1, 1) :: repeat (1, 2) 50438 ++ (27674, 2) :: (1, 1) :: repeat (1, 2) 323288 ++ w) 1); closearith.
  }
  (* step 191: DIPGRIND 2394 17815 *)
  apply (hsteps_trans _ (HC [1650; 304; 49; 5] 0 3 2 (repeat (1, 2) 2394 ++ (17815, 2) :: (1, 1) :: repeat (1, 2) 50438 ++ (27674, 2) :: (1, 1) :: repeat (1, 2) 323288 ++ w) 1)).
  {
    apply (DIPGRIND 2394 17815 [1650; 304; 49; 5] ((1, 1) :: repeat (1, 2) 50438 ++ (27674, 2) :: (1, 1) :: repeat (1, 2) 323288 ++ w) 1); closearith.
  }
  (* step 192: P PX2A *)
  apply (hsteps_trans _ (HC [49; 5] 303 1648 2 ((1, 1) :: repeat (1, 2) 2396 ++ (17815, 2) :: (1, 1) :: repeat (1, 2) 50438 ++ (27674, 2) :: (1, 1) :: repeat (1, 2) 323288 ++ w) 1)).
  {
    apply (hsteps_step _ (HC [49; 5] 303 1648 2 ((1, 1) :: repeat (1, 2) 2396 ++ (17815, 2) :: (1, 1) :: repeat (1, 2) 50438 ++ (27674, 2) :: (1, 1) :: repeat (1, 2) 323288 ++ w) 1)); [apply hPX2A | apply hsteps_refl].
  }
  (* step 193: P PUSH *)
  apply (hsteps_trans _ (HC [49; 5] 302 1 2 ((1646, 2) :: (1, 1) :: repeat (1, 2) 2396 ++ (17815, 2) :: (1, 1) :: repeat (1, 2) 50438 ++ (27674, 2) :: (1, 1) :: repeat (1, 2) 323288 ++ w) 1)).
  {
    replace ((1646, 2) :: (1, 1) :: repeat (1, 2) 2396 ++ (17815, 2) :: (1, 1) :: repeat (1, 2) 50438 ++ (27674, 2) :: (1, 1) :: repeat (1, 2) 323288 ++ w) with ((1648 - 2, 2) :: (1, 1) :: repeat (1, 2) 2396 ++ (17815, 2) :: (1, 1) :: repeat (1, 2) 50438 ++ (27674, 2) :: (1, 1) :: repeat (1, 2) 323288 ++ w) by sec_eq.
    apply (sPUSH [49; 5] 302 1648 ((1, 1) :: repeat (1, 2) 2396 ++ (17815, 2) :: (1, 1) :: repeat (1, 2) 50438 ++ (27674, 2) :: (1, 1) :: repeat (1, 2) 323288 ++ w) 1); closearith.
  }
  (* step 194: P TDN *)
  apply (hsteps_trans _ (HB [49; 5] 302 1 4 ((1646, 2) :: (1, 1) :: repeat (1, 2) 2396 ++ (17815, 2) :: (1, 1) :: repeat (1, 2) 50438 ++ (27674, 2) :: (1, 1) :: repeat (1, 2) 323288 ++ w) 1)).
  {
    apply (sTDN [49; 5] 302 ((1646, 2) :: (1, 1) :: repeat (1, 2) 2396 ++ (17815, 2) :: (1, 1) :: repeat (1, 2) 50438 ++ (27674, 2) :: (1, 1) :: repeat (1, 2) 323288 ++ w) 1).
  }
  (* step 195: sTUP *)
  apply (hsteps_trans _ (HC [49; 5] 302 3 2 ((1644, 2) :: (1, 1) :: repeat (1, 2) 2396 ++ (17815, 2) :: (1, 1) :: repeat (1, 2) 50438 ++ (27674, 2) :: (1, 1) :: repeat (1, 2) 323288 ++ w) 1)).
  {
    replace ((1644, 2) :: (1, 1) :: repeat (1, 2) 2396 ++ (17815, 2) :: (1, 1) :: repeat (1, 2) 50438 ++ (27674, 2) :: (1, 1) :: repeat (1, 2) 323288 ++ w) with ((1646 - 2, 2) :: (1, 1) :: repeat (1, 2) 2396 ++ (17815, 2) :: (1, 1) :: repeat (1, 2) 50438 ++ (27674, 2) :: (1, 1) :: repeat (1, 2) 323288 ++ w) by sec_eq.
    apply (sTUP [49; 5] 302 4 1646 2 ((1, 1) :: repeat (1, 2) 2396 ++ (17815, 2) :: (1, 1) :: repeat (1, 2) 50438 ++ (27674, 2) :: (1, 1) :: repeat (1, 2) 323288 ++ w) 1); closearith.
  }
  (* step 196: DIPGRIND 302 1040 *)
  apply (hsteps_trans _ (HC [49; 5] 0 3 2 (repeat (1, 2) 302 ++ (1040, 2) :: (1, 1) :: repeat (1, 2) 2396 ++ (17815, 2) :: (1, 1) :: repeat (1, 2) 50438 ++ (27674, 2) :: (1, 1) :: repeat (1, 2) 323288 ++ w) 1)).
  {
    apply (DIPGRIND 302 1040 [49; 5] ((1, 1) :: repeat (1, 2) 2396 ++ (17815, 2) :: (1, 1) :: repeat (1, 2) 50438 ++ (27674, 2) :: (1, 1) :: repeat (1, 2) 323288 ++ w) 1); closearith.
  }
  (* step 197: P PX2A *)
  apply (hsteps_trans _ (HC [] 4 47 2 ((1, 1) :: repeat (1, 2) 304 ++ (1040, 2) :: (1, 1) :: repeat (1, 2) 2396 ++ (17815, 2) :: (1, 1) :: repeat (1, 2) 50438 ++ (27674, 2) :: (1, 1) :: repeat (1, 2) 323288 ++ w) 1)).
  {
    apply (hsteps_step _ (HC [] 4 47 2 ((1, 1) :: repeat (1, 2) 304 ++ (1040, 2) :: (1, 1) :: repeat (1, 2) 2396 ++ (17815, 2) :: (1, 1) :: repeat (1, 2) 50438 ++ (27674, 2) :: (1, 1) :: repeat (1, 2) 323288 ++ w) 1)); [apply hPX2A | apply hsteps_refl].
  }
  (* step 198: P PUSH *)
  apply (hsteps_trans _ (HC [] 3 1 2 ((45, 2) :: (1, 1) :: repeat (1, 2) 304 ++ (1040, 2) :: (1, 1) :: repeat (1, 2) 2396 ++ (17815, 2) :: (1, 1) :: repeat (1, 2) 50438 ++ (27674, 2) :: (1, 1) :: repeat (1, 2) 323288 ++ w) 1)).
  {
    replace ((45, 2) :: (1, 1) :: repeat (1, 2) 304 ++ (1040, 2) :: (1, 1) :: repeat (1, 2) 2396 ++ (17815, 2) :: (1, 1) :: repeat (1, 2) 50438 ++ (27674, 2) :: (1, 1) :: repeat (1, 2) 323288 ++ w) with ((47 - 2, 2) :: (1, 1) :: repeat (1, 2) 304 ++ (1040, 2) :: (1, 1) :: repeat (1, 2) 2396 ++ (17815, 2) :: (1, 1) :: repeat (1, 2) 50438 ++ (27674, 2) :: (1, 1) :: repeat (1, 2) 323288 ++ w) by sec_eq.
    apply (sPUSH [] 3 47 ((1, 1) :: repeat (1, 2) 304 ++ (1040, 2) :: (1, 1) :: repeat (1, 2) 2396 ++ (17815, 2) :: (1, 1) :: repeat (1, 2) 50438 ++ (27674, 2) :: (1, 1) :: repeat (1, 2) 323288 ++ w) 1); closearith.
  }
  (* step 199: P TDN *)
  apply (hsteps_trans _ (HB [] 3 1 4 ((45, 2) :: (1, 1) :: repeat (1, 2) 304 ++ (1040, 2) :: (1, 1) :: repeat (1, 2) 2396 ++ (17815, 2) :: (1, 1) :: repeat (1, 2) 50438 ++ (27674, 2) :: (1, 1) :: repeat (1, 2) 323288 ++ w) 1)).
  {
    apply (sTDN [] 3 ((45, 2) :: (1, 1) :: repeat (1, 2) 304 ++ (1040, 2) :: (1, 1) :: repeat (1, 2) 2396 ++ (17815, 2) :: (1, 1) :: repeat (1, 2) 50438 ++ (27674, 2) :: (1, 1) :: repeat (1, 2) 323288 ++ w) 1).
  }
  (* step 200: sTUP *)
  apply (hsteps_trans _ (HC [] 3 3 2 ((43, 2) :: (1, 1) :: repeat (1, 2) 304 ++ (1040, 2) :: (1, 1) :: repeat (1, 2) 2396 ++ (17815, 2) :: (1, 1) :: repeat (1, 2) 50438 ++ (27674, 2) :: (1, 1) :: repeat (1, 2) 323288 ++ w) 1)).
  {
    replace ((43, 2) :: (1, 1) :: repeat (1, 2) 304 ++ (1040, 2) :: (1, 1) :: repeat (1, 2) 2396 ++ (17815, 2) :: (1, 1) :: repeat (1, 2) 50438 ++ (27674, 2) :: (1, 1) :: repeat (1, 2) 323288 ++ w) with ((45 - 2, 2) :: (1, 1) :: repeat (1, 2) 304 ++ (1040, 2) :: (1, 1) :: repeat (1, 2) 2396 ++ (17815, 2) :: (1, 1) :: repeat (1, 2) 50438 ++ (27674, 2) :: (1, 1) :: repeat (1, 2) 323288 ++ w) by sec_eq.
    apply (sTUP [] 3 4 45 2 ((1, 1) :: repeat (1, 2) 304 ++ (1040, 2) :: (1, 1) :: repeat (1, 2) 2396 ++ (17815, 2) :: (1, 1) :: repeat (1, 2) 50438 ++ (27674, 2) :: (1, 1) :: repeat (1, 2) 323288 ++ w) 1); closearith.
  }
  (* step 201: DIPGRIND 3 37 *)
  apply (hsteps_trans _ (HC [] 0 3 2 (repeat (1, 2) 3 ++ (37, 2) :: (1, 1) :: repeat (1, 2) 304 ++ (1040, 2) :: (1, 1) :: repeat (1, 2) 2396 ++ (17815, 2) :: (1, 1) :: repeat (1, 2) 50438 ++ (27674, 2) :: (1, 1) :: repeat (1, 2) 323288 ++ w) 1)).
  {
    apply (DIPGRIND 3 37 [] ((1, 1) :: repeat (1, 2) 304 ++ (1040, 2) :: (1, 1) :: repeat (1, 2) 2396 ++ (17815, 2) :: (1, 1) :: repeat (1, 2) 50438 ++ (27674, 2) :: (1, 1) :: repeat (1, 2) 323288 ++ w) 1); closearith.
  }
  (* step 202: P PUSHX *)
  apply (hsteps_trans _ (HB [] 1 1 7 (repeat (1, 2) 3 ++ (37, 2) :: (1, 1) :: repeat (1, 2) 304 ++ (1040, 2) :: (1, 1) :: repeat (1, 2) 2396 ++ (17815, 2) :: (1, 1) :: repeat (1, 2) 50438 ++ (27674, 2) :: (1, 1) :: repeat (1, 2) 323288 ++ w) 1)).
  {
    apply (hsteps_step _ (HB [] 1 1 7 (repeat (1, 2) 3 ++ (37, 2) :: (1, 1) :: repeat (1, 2) 304 ++ (1040, 2) :: (1, 1) :: repeat (1, 2) 2396 ++ (17815, 2) :: (1, 1) :: repeat (1, 2) 50438 ++ (27674, 2) :: (1, 1) :: repeat (1, 2) 323288 ++ w) 1)); [apply hPUSHX | apply hsteps_refl].
  }
  (* step 203: M pop12 (3,) *)
  apply (hsteps_trans _ (HB [] 4 1 13 ((37, 2) :: (1, 1) :: repeat (1, 2) 304 ++ (1040, 2) :: (1, 1) :: repeat (1, 2) 2396 ++ (17815, 2) :: (1, 1) :: repeat (1, 2) 50438 ++ (27674, 2) :: (1, 1) :: repeat (1, 2) 323288 ++ w) 1)).
  {
    apply (pop12 3 [] 1 7 ((37, 2) :: (1, 1) :: repeat (1, 2) 304 ++ (1040, 2) :: (1, 1) :: repeat (1, 2) 2396 ++ (17815, 2) :: (1, 1) :: repeat (1, 2) 50438 ++ (27674, 2) :: (1, 1) :: repeat (1, 2) 323288 ++ w) 1); closearith.
  }
  (* step 204: sTUP *)
  apply (hsteps_trans _ (HC [] 4 12 2 ((35, 2) :: (1, 1) :: repeat (1, 2) 304 ++ (1040, 2) :: (1, 1) :: repeat (1, 2) 2396 ++ (17815, 2) :: (1, 1) :: repeat (1, 2) 50438 ++ (27674, 2) :: (1, 1) :: repeat (1, 2) 323288 ++ w) 1)).
  {
    replace ((35, 2) :: (1, 1) :: repeat (1, 2) 304 ++ (1040, 2) :: (1, 1) :: repeat (1, 2) 2396 ++ (17815, 2) :: (1, 1) :: repeat (1, 2) 50438 ++ (27674, 2) :: (1, 1) :: repeat (1, 2) 323288 ++ w) with ((37 - 2, 2) :: (1, 1) :: repeat (1, 2) 304 ++ (1040, 2) :: (1, 1) :: repeat (1, 2) 2396 ++ (17815, 2) :: (1, 1) :: repeat (1, 2) 50438 ++ (27674, 2) :: (1, 1) :: repeat (1, 2) 323288 ++ w) by sec_eq.
    apply (sTUP [] 4 13 37 2 ((1, 1) :: repeat (1, 2) 304 ++ (1040, 2) :: (1, 1) :: repeat (1, 2) 2396 ++ (17815, 2) :: (1, 1) :: repeat (1, 2) 50438 ++ (27674, 2) :: (1, 1) :: repeat (1, 2) 323288 ++ w) 1); closearith.
  }
  (* step 205: P PUSH *)
  apply (hsteps_trans _ (HC [] 3 1 2 ((10, 2) :: (35, 2) :: (1, 1) :: repeat (1, 2) 304 ++ (1040, 2) :: (1, 1) :: repeat (1, 2) 2396 ++ (17815, 2) :: (1, 1) :: repeat (1, 2) 50438 ++ (27674, 2) :: (1, 1) :: repeat (1, 2) 323288 ++ w) 1)).
  {
    replace ((10, 2) :: (35, 2) :: (1, 1) :: repeat (1, 2) 304 ++ (1040, 2) :: (1, 1) :: repeat (1, 2) 2396 ++ (17815, 2) :: (1, 1) :: repeat (1, 2) 50438 ++ (27674, 2) :: (1, 1) :: repeat (1, 2) 323288 ++ w) with ((12 - 2, 2) :: (35, 2) :: (1, 1) :: repeat (1, 2) 304 ++ (1040, 2) :: (1, 1) :: repeat (1, 2) 2396 ++ (17815, 2) :: (1, 1) :: repeat (1, 2) 50438 ++ (27674, 2) :: (1, 1) :: repeat (1, 2) 323288 ++ w) by sec_eq.
    apply (sPUSH [] 3 12 ((35, 2) :: (1, 1) :: repeat (1, 2) 304 ++ (1040, 2) :: (1, 1) :: repeat (1, 2) 2396 ++ (17815, 2) :: (1, 1) :: repeat (1, 2) 50438 ++ (27674, 2) :: (1, 1) :: repeat (1, 2) 323288 ++ w) 1); closearith.
  }
  (* step 206: P TDN *)
  apply (hsteps_trans _ (HB [] 3 1 4 ((10, 2) :: (35, 2) :: (1, 1) :: repeat (1, 2) 304 ++ (1040, 2) :: (1, 1) :: repeat (1, 2) 2396 ++ (17815, 2) :: (1, 1) :: repeat (1, 2) 50438 ++ (27674, 2) :: (1, 1) :: repeat (1, 2) 323288 ++ w) 1)).
  {
    apply (sTDN [] 3 ((10, 2) :: (35, 2) :: (1, 1) :: repeat (1, 2) 304 ++ (1040, 2) :: (1, 1) :: repeat (1, 2) 2396 ++ (17815, 2) :: (1, 1) :: repeat (1, 2) 50438 ++ (27674, 2) :: (1, 1) :: repeat (1, 2) 323288 ++ w) 1).
  }
  (* step 207: sTUP *)
  apply (hsteps_trans _ (HC [] 3 3 2 ((8, 2) :: (35, 2) :: (1, 1) :: repeat (1, 2) 304 ++ (1040, 2) :: (1, 1) :: repeat (1, 2) 2396 ++ (17815, 2) :: (1, 1) :: repeat (1, 2) 50438 ++ (27674, 2) :: (1, 1) :: repeat (1, 2) 323288 ++ w) 1)).
  {
    replace ((8, 2) :: (35, 2) :: (1, 1) :: repeat (1, 2) 304 ++ (1040, 2) :: (1, 1) :: repeat (1, 2) 2396 ++ (17815, 2) :: (1, 1) :: repeat (1, 2) 50438 ++ (27674, 2) :: (1, 1) :: repeat (1, 2) 323288 ++ w) with ((10 - 2, 2) :: (35, 2) :: (1, 1) :: repeat (1, 2) 304 ++ (1040, 2) :: (1, 1) :: repeat (1, 2) 2396 ++ (17815, 2) :: (1, 1) :: repeat (1, 2) 50438 ++ (27674, 2) :: (1, 1) :: repeat (1, 2) 323288 ++ w) by sec_eq.
    apply (sTUP [] 3 4 10 2 ((35, 2) :: (1, 1) :: repeat (1, 2) 304 ++ (1040, 2) :: (1, 1) :: repeat (1, 2) 2396 ++ (17815, 2) :: (1, 1) :: repeat (1, 2) 50438 ++ (27674, 2) :: (1, 1) :: repeat (1, 2) 323288 ++ w) 1); closearith.
  }
  (* step 208: DIPGRIND 3 2 *)
  apply (hsteps_trans _ (HC [] 0 3 2 (repeat (1, 2) 3 ++ (2, 2) :: (35, 2) :: (1, 1) :: repeat (1, 2) 304 ++ (1040, 2) :: (1, 1) :: repeat (1, 2) 2396 ++ (17815, 2) :: (1, 1) :: repeat (1, 2) 50438 ++ (27674, 2) :: (1, 1) :: repeat (1, 2) 323288 ++ w) 1)).
  {
    apply (DIPGRIND 3 2 [] ((35, 2) :: (1, 1) :: repeat (1, 2) 304 ++ (1040, 2) :: (1, 1) :: repeat (1, 2) 2396 ++ (17815, 2) :: (1, 1) :: repeat (1, 2) 50438 ++ (27674, 2) :: (1, 1) :: repeat (1, 2) 323288 ++ w) 1); closearith.
  }
  (* step 209: P PUSHX *)
  apply (hsteps_trans _ (HB [] 1 1 7 (repeat (1, 2) 3 ++ (2, 2) :: (35, 2) :: (1, 1) :: repeat (1, 2) 304 ++ (1040, 2) :: (1, 1) :: repeat (1, 2) 2396 ++ (17815, 2) :: (1, 1) :: repeat (1, 2) 50438 ++ (27674, 2) :: (1, 1) :: repeat (1, 2) 323288 ++ w) 1)).
  {
    apply (hsteps_step _ (HB [] 1 1 7 (repeat (1, 2) 3 ++ (2, 2) :: (35, 2) :: (1, 1) :: repeat (1, 2) 304 ++ (1040, 2) :: (1, 1) :: repeat (1, 2) 2396 ++ (17815, 2) :: (1, 1) :: repeat (1, 2) 50438 ++ (27674, 2) :: (1, 1) :: repeat (1, 2) 323288 ++ w) 1)); [apply hPUSHX | apply hsteps_refl].
  }
  (* step 210: M pop12 (3,) *)
  apply (hsteps_trans _ (HB [] 4 1 13 ((2, 2) :: (35, 2) :: (1, 1) :: repeat (1, 2) 304 ++ (1040, 2) :: (1, 1) :: repeat (1, 2) 2396 ++ (17815, 2) :: (1, 1) :: repeat (1, 2) 50438 ++ (27674, 2) :: (1, 1) :: repeat (1, 2) 323288 ++ w) 1)).
  {
    apply (pop12 3 [] 1 7 ((2, 2) :: (35, 2) :: (1, 1) :: repeat (1, 2) 304 ++ (1040, 2) :: (1, 1) :: repeat (1, 2) 2396 ++ (17815, 2) :: (1, 1) :: repeat (1, 2) 50438 ++ (27674, 2) :: (1, 1) :: repeat (1, 2) 323288 ++ w) 1); closearith.
  }
  (* step 211: P TUP2_1 *)
  apply (hsteps_trans _ (HC [5] 13 1 2 ((33, 2) :: (1, 1) :: repeat (1, 2) 304 ++ (1040, 2) :: (1, 1) :: repeat (1, 2) 2396 ++ (17815, 2) :: (1, 1) :: repeat (1, 2) 50438 ++ (27674, 2) :: (1, 1) :: repeat (1, 2) 323288 ++ w) 1)).
  {
    replace ((33, 2) :: (1, 1) :: repeat (1, 2) 304 ++ (1040, 2) :: (1, 1) :: repeat (1, 2) 2396 ++ (17815, 2) :: (1, 1) :: repeat (1, 2) 50438 ++ (27674, 2) :: (1, 1) :: repeat (1, 2) 323288 ++ w) with ((35 - 2, 2) :: (1, 1) :: repeat (1, 2) 304 ++ (1040, 2) :: (1, 1) :: repeat (1, 2) 2396 ++ (17815, 2) :: (1, 1) :: repeat (1, 2) 50438 ++ (27674, 2) :: (1, 1) :: repeat (1, 2) 323288 ++ w) by sec_eq.
    apply (sTUP2_1 [] 4 12 35 ((1, 1) :: repeat (1, 2) 304 ++ (1040, 2) :: (1, 1) :: repeat (1, 2) 2396 ++ (17815, 2) :: (1, 1) :: repeat (1, 2) 50438 ++ (27674, 2) :: (1, 1) :: repeat (1, 2) 323288 ++ w) 1); closearith.
  }
  (* step 212: P TDN *)
  apply (hsteps_trans _ (HB [5] 13 1 4 ((33, 2) :: (1, 1) :: repeat (1, 2) 304 ++ (1040, 2) :: (1, 1) :: repeat (1, 2) 2396 ++ (17815, 2) :: (1, 1) :: repeat (1, 2) 50438 ++ (27674, 2) :: (1, 1) :: repeat (1, 2) 323288 ++ w) 1)).
  {
    apply (sTDN [5] 13 ((33, 2) :: (1, 1) :: repeat (1, 2) 304 ++ (1040, 2) :: (1, 1) :: repeat (1, 2) 2396 ++ (17815, 2) :: (1, 1) :: repeat (1, 2) 50438 ++ (27674, 2) :: (1, 1) :: repeat (1, 2) 323288 ++ w) 1).
  }
  (* step 213: sTUP *)
  apply (hsteps_trans _ (HC [5] 13 3 2 ((31, 2) :: (1, 1) :: repeat (1, 2) 304 ++ (1040, 2) :: (1, 1) :: repeat (1, 2) 2396 ++ (17815, 2) :: (1, 1) :: repeat (1, 2) 50438 ++ (27674, 2) :: (1, 1) :: repeat (1, 2) 323288 ++ w) 1)).
  {
    replace ((31, 2) :: (1, 1) :: repeat (1, 2) 304 ++ (1040, 2) :: (1, 1) :: repeat (1, 2) 2396 ++ (17815, 2) :: (1, 1) :: repeat (1, 2) 50438 ++ (27674, 2) :: (1, 1) :: repeat (1, 2) 323288 ++ w) with ((33 - 2, 2) :: (1, 1) :: repeat (1, 2) 304 ++ (1040, 2) :: (1, 1) :: repeat (1, 2) 2396 ++ (17815, 2) :: (1, 1) :: repeat (1, 2) 50438 ++ (27674, 2) :: (1, 1) :: repeat (1, 2) 323288 ++ w) by sec_eq.
    apply (sTUP [5] 13 4 33 2 ((1, 1) :: repeat (1, 2) 304 ++ (1040, 2) :: (1, 1) :: repeat (1, 2) 2396 ++ (17815, 2) :: (1, 1) :: repeat (1, 2) 50438 ++ (27674, 2) :: (1, 1) :: repeat (1, 2) 323288 ++ w) 1); closearith.
  }
  (* step 214: DIPGRIND 13 5 *)
  apply (hsteps_trans _ (HC [5] 0 3 2 (repeat (1, 2) 13 ++ (5, 2) :: (1, 1) :: repeat (1, 2) 304 ++ (1040, 2) :: (1, 1) :: repeat (1, 2) 2396 ++ (17815, 2) :: (1, 1) :: repeat (1, 2) 50438 ++ (27674, 2) :: (1, 1) :: repeat (1, 2) 323288 ++ w) 1)).
  {
    apply (DIPGRIND 13 5 [5] ((1, 1) :: repeat (1, 2) 304 ++ (1040, 2) :: (1, 1) :: repeat (1, 2) 2396 ++ (17815, 2) :: (1, 1) :: repeat (1, 2) 50438 ++ (27674, 2) :: (1, 1) :: repeat (1, 2) 323288 ++ w) 1); closearith.
  }
  (* step 215: P PX2Bgen *)
  apply (hsteps_trans _ (HB [0] 3 1 2 (repeat (1, 2) 1 ++ (1, 1) :: repeat (1, 2) 15 ++ (5, 2) :: (1, 1) :: repeat (1, 2) 304 ++ (1040, 2) :: (1, 1) :: repeat (1, 2) 2396 ++ (17815, 2) :: (1, 1) :: repeat (1, 2) 50438 ++ (27674, 2) :: (1, 1) :: repeat (1, 2) 323288 ++ w) 1)).
  {
    apply (hsteps_step _ (HB [0] 3 1 2 (repeat (1, 2) 1 ++ (1, 1) :: repeat (1, 2) 15 ++ (5, 2) :: (1, 1) :: repeat (1, 2) 304 ++ (1040, 2) :: (1, 1) :: repeat (1, 2) 2396 ++ (17815, 2) :: (1, 1) :: repeat (1, 2) 50438 ++ (27674, 2) :: (1, 1) :: repeat (1, 2) 323288 ++ w) 1)); [apply hPX2Bgen | apply hsteps_refl].
  }
  (* step 216: M pop12 (1,) *)
  apply (hsteps_trans _ (HB [0] 4 1 4 ((1, 1) :: repeat (1, 2) 15 ++ (5, 2) :: (1, 1) :: repeat (1, 2) 304 ++ (1040, 2) :: (1, 1) :: repeat (1, 2) 2396 ++ (17815, 2) :: (1, 1) :: repeat (1, 2) 50438 ++ (27674, 2) :: (1, 1) :: repeat (1, 2) 323288 ++ w) 1)).
  {
    apply (pop12 1 [0] 3 2 ((1, 1) :: repeat (1, 2) 15 ++ (5, 2) :: (1, 1) :: repeat (1, 2) 304 ++ (1040, 2) :: (1, 1) :: repeat (1, 2) 2396 ++ (17815, 2) :: (1, 1) :: repeat (1, 2) 50438 ++ (27674, 2) :: (1, 1) :: repeat (1, 2) 323288 ++ w) 1); closearith.
  }
  (* step 217: P POP *)
  apply (hsteps_trans _ (HB [0] 5 1 5 (repeat (1, 2) 15 ++ (5, 2) :: (1, 1) :: repeat (1, 2) 304 ++ (1040, 2) :: (1, 1) :: repeat (1, 2) 2396 ++ (17815, 2) :: (1, 1) :: repeat (1, 2) 50438 ++ (27674, 2) :: (1, 1) :: repeat (1, 2) 323288 ++ w) 1)).
  {
    apply (sPOP1 [0] 4 4 (repeat (1, 2) 15 ++ (5, 2) :: (1, 1) :: repeat (1, 2) 304 ++ (1040, 2) :: (1, 1) :: repeat (1, 2) 2396 ++ (17815, 2) :: (1, 1) :: repeat (1, 2) 50438 ++ (27674, 2) :: (1, 1) :: repeat (1, 2) 323288 ++ w) 1); closearith.
  }
  (* step 218: M pop12 (15,) *)
  apply (hsteps_trans _ (HB [0] 20 1 35 ((5, 2) :: (1, 1) :: repeat (1, 2) 304 ++ (1040, 2) :: (1, 1) :: repeat (1, 2) 2396 ++ (17815, 2) :: (1, 1) :: repeat (1, 2) 50438 ++ (27674, 2) :: (1, 1) :: repeat (1, 2) 323288 ++ w) 1)).
  {
    apply (pop12 15 [0] 5 5 ((5, 2) :: (1, 1) :: repeat (1, 2) 304 ++ (1040, 2) :: (1, 1) :: repeat (1, 2) 2396 ++ (17815, 2) :: (1, 1) :: repeat (1, 2) 50438 ++ (27674, 2) :: (1, 1) :: repeat (1, 2) 323288 ++ w) 1); closearith.
  }
  (* step 219: sTUP *)
  apply (hsteps_trans _ (HC [0] 20 34 2 ((3, 2) :: (1, 1) :: repeat (1, 2) 304 ++ (1040, 2) :: (1, 1) :: repeat (1, 2) 2396 ++ (17815, 2) :: (1, 1) :: repeat (1, 2) 50438 ++ (27674, 2) :: (1, 1) :: repeat (1, 2) 323288 ++ w) 1)).
  {
    replace ((3, 2) :: (1, 1) :: repeat (1, 2) 304 ++ (1040, 2) :: (1, 1) :: repeat (1, 2) 2396 ++ (17815, 2) :: (1, 1) :: repeat (1, 2) 50438 ++ (27674, 2) :: (1, 1) :: repeat (1, 2) 323288 ++ w) with ((5 - 2, 2) :: (1, 1) :: repeat (1, 2) 304 ++ (1040, 2) :: (1, 1) :: repeat (1, 2) 2396 ++ (17815, 2) :: (1, 1) :: repeat (1, 2) 50438 ++ (27674, 2) :: (1, 1) :: repeat (1, 2) 323288 ++ w) by sec_eq.
    apply (sTUP [0] 20 35 5 2 ((1, 1) :: repeat (1, 2) 304 ++ (1040, 2) :: (1, 1) :: repeat (1, 2) 2396 ++ (17815, 2) :: (1, 1) :: repeat (1, 2) 50438 ++ (27674, 2) :: (1, 1) :: repeat (1, 2) 323288 ++ w) 1); closearith.
  }
  (* step 220: hGRIND_even 15 *)
  apply (hsteps_trans _ (HB [0] 19 1 34 ((2, 2) :: (3, 2) :: (1, 1) :: repeat (1, 2) 304 ++ (1040, 2) :: (1, 1) :: repeat (1, 2) 2396 ++ (17815, 2) :: (1, 1) :: repeat (1, 2) 50438 ++ (27674, 2) :: (1, 1) :: repeat (1, 2) 323288 ++ w) 1)).
  {
    apply (hGRIND_even 15 [0] 19 ((3, 2) :: (1, 1) :: repeat (1, 2) 304 ++ (1040, 2) :: (1, 1) :: repeat (1, 2) 2396 ++ (17815, 2) :: (1, 1) :: repeat (1, 2) 50438 ++ (27674, 2) :: (1, 1) :: repeat (1, 2) 323288 ++ w) 1); closearith.
  }
  (* step 221: P TUP2_1 *)
  apply (hsteps_trans _ (HC [20; 0] 34 1 2 (repeat (1, 2) 1 ++ (1, 1) :: repeat (1, 2) 304 ++ (1040, 2) :: (1, 1) :: repeat (1, 2) 2396 ++ (17815, 2) :: (1, 1) :: repeat (1, 2) 50438 ++ (27674, 2) :: (1, 1) :: repeat (1, 2) 323288 ++ w) 1)).
  {
    replace (repeat (1, 2) 1 ++ (1, 1) :: repeat (1, 2) 304 ++ (1040, 2) :: (1, 1) :: repeat (1, 2) 2396 ++ (17815, 2) :: (1, 1) :: repeat (1, 2) 50438 ++ (27674, 2) :: (1, 1) :: repeat (1, 2) 323288 ++ w) with ((3 - 2, 2) :: (1, 1) :: repeat (1, 2) 304 ++ (1040, 2) :: (1, 1) :: repeat (1, 2) 2396 ++ (17815, 2) :: (1, 1) :: repeat (1, 2) 50438 ++ (27674, 2) :: (1, 1) :: repeat (1, 2) 323288 ++ w) by sec_eq.
    apply (sTUP2_1 [0] 19 33 3 ((1, 1) :: repeat (1, 2) 304 ++ (1040, 2) :: (1, 1) :: repeat (1, 2) 2396 ++ (17815, 2) :: (1, 1) :: repeat (1, 2) 50438 ++ (27674, 2) :: (1, 1) :: repeat (1, 2) 323288 ++ w) 1); closearith.
  }
  (* step 222: P TDN *)
  apply (hsteps_trans _ (HB [20; 0] 34 1 4 (repeat (1, 2) 1 ++ (1, 1) :: repeat (1, 2) 304 ++ (1040, 2) :: (1, 1) :: repeat (1, 2) 2396 ++ (17815, 2) :: (1, 1) :: repeat (1, 2) 50438 ++ (27674, 2) :: (1, 1) :: repeat (1, 2) 323288 ++ w) 1)).
  {
    apply (sTDN [20; 0] 34 (repeat (1, 2) 1 ++ (1, 1) :: repeat (1, 2) 304 ++ (1040, 2) :: (1, 1) :: repeat (1, 2) 2396 ++ (17815, 2) :: (1, 1) :: repeat (1, 2) 50438 ++ (27674, 2) :: (1, 1) :: repeat (1, 2) 323288 ++ w) 1).
  }
  (* step 223: M pop12 (1,) *)
  apply (hsteps_trans _ (HB [20; 0] 35 1 6 ((1, 1) :: repeat (1, 2) 304 ++ (1040, 2) :: (1, 1) :: repeat (1, 2) 2396 ++ (17815, 2) :: (1, 1) :: repeat (1, 2) 50438 ++ (27674, 2) :: (1, 1) :: repeat (1, 2) 323288 ++ w) 1)).
  {
    apply (pop12 1 [20; 0] 34 4 ((1, 1) :: repeat (1, 2) 304 ++ (1040, 2) :: (1, 1) :: repeat (1, 2) 2396 ++ (17815, 2) :: (1, 1) :: repeat (1, 2) 50438 ++ (27674, 2) :: (1, 1) :: repeat (1, 2) 323288 ++ w) 1); closearith.
  }
  (* step 224: P POP *)
  apply (sPOP1 [20; 0] 35 6 (repeat (1, 2) 304 ++ (1040, 2) :: (1, 1) :: repeat (1, 2) 2396 ++ (17815, 2) :: (1, 1) :: repeat (1, 2) 50438 ++ (27674, 2) :: (1, 1) :: repeat (1, 2) 323288 ++ w) 1); closearith.
Qed.

(* CASCADE53e: steps 225-280 of the CASCADE53 chain. *)
Lemma CASCADE53e : forall w,
  hsteps (HB [20; 0] 36 1 7 (repeat (1, 2) 304 ++ (1040, 2) :: (1, 1) :: repeat (1, 2) 2396 ++ (17815, 2) :: (1, 1) :: repeat (1, 2) 50438 ++ (27674, 2) :: (1, 1) :: repeat (1, 2) 323288 ++ w) 1)
         (HB [14; 5] 50 1 93 ((206, 2) :: (1, 1) :: repeat (1, 2) 615 ++ (2203, 2) :: (1, 1) :: repeat (1, 2) 4796 ++ (8221, 2) :: (1, 1) :: repeat (1, 2) 50438 ++ (27674, 2) :: (1, 1) :: repeat (1, 2) 323288 ++ w) 1).
Proof.
  intro w.
  (* step 225: M pop12 (304,) *)
  apply (hsteps_trans _ (HB [20; 0] 340 1 615 ((1040, 2) :: (1, 1) :: repeat (1, 2) 2396 ++ (17815, 2) :: (1, 1) :: repeat (1, 2) 50438 ++ (27674, 2) :: (1, 1) :: repeat (1, 2) 323288 ++ w) 1)).
  {
    apply (pop12 304 [20; 0] 36 7 ((1040, 2) :: (1, 1) :: repeat (1, 2) 2396 ++ (17815, 2) :: (1, 1) :: repeat (1, 2) 50438 ++ (27674, 2) :: (1, 1) :: repeat (1, 2) 323288 ++ w) 1); closearith.
  }
  (* step 226: sTUP *)
  apply (hsteps_trans _ (HC [20; 0] 340 614 2 ((1038, 2) :: (1, 1) :: repeat (1, 2) 2396 ++ (17815, 2) :: (1, 1) :: repeat (1, 2) 50438 ++ (27674, 2) :: (1, 1) :: repeat (1, 2) 323288 ++ w) 1)).
  {
    replace ((1038, 2) :: (1, 1) :: repeat (1, 2) 2396 ++ (17815, 2) :: (1, 1) :: repeat (1, 2) 50438 ++ (27674, 2) :: (1, 1) :: repeat (1, 2) 323288 ++ w) with ((1040 - 2, 2) :: (1, 1) :: repeat (1, 2) 2396 ++ (17815, 2) :: (1, 1) :: repeat (1, 2) 50438 ++ (27674, 2) :: (1, 1) :: repeat (1, 2) 323288 ++ w) by sec_eq.
    apply (sTUP [20; 0] 340 615 1040 2 ((1, 1) :: repeat (1, 2) 2396 ++ (17815, 2) :: (1, 1) :: repeat (1, 2) 50438 ++ (27674, 2) :: (1, 1) :: repeat (1, 2) 323288 ++ w) 1); closearith.
  }
  (* step 227: hGRIND_even 305 *)
  apply (hsteps_trans _ (HB [20; 0] 339 1 614 ((2, 2) :: (1038, 2) :: (1, 1) :: repeat (1, 2) 2396 ++ (17815, 2) :: (1, 1) :: repeat (1, 2) 50438 ++ (27674, 2) :: (1, 1) :: repeat (1, 2) 323288 ++ w) 1)).
  {
    apply (hGRIND_even 305 [20; 0] 339 ((1038, 2) :: (1, 1) :: repeat (1, 2) 2396 ++ (17815, 2) :: (1, 1) :: repeat (1, 2) 50438 ++ (27674, 2) :: (1, 1) :: repeat (1, 2) 323288 ++ w) 1); closearith.
  }
  (* step 228: P TUP2_1 *)
  apply (hsteps_trans _ (HC [340; 20; 0] 614 1 2 ((1036, 2) :: (1, 1) :: repeat (1, 2) 2396 ++ (17815, 2) :: (1, 1) :: repeat (1, 2) 50438 ++ (27674, 2) :: (1, 1) :: repeat (1, 2) 323288 ++ w) 1)).
  {
    replace ((1036, 2) :: (1, 1) :: repeat (1, 2) 2396 ++ (17815, 2) :: (1, 1) :: repeat (1, 2) 50438 ++ (27674, 2) :: (1, 1) :: repeat (1, 2) 323288 ++ w) with ((1038 - 2, 2) :: (1, 1) :: repeat (1, 2) 2396 ++ (17815, 2) :: (1, 1) :: repeat (1, 2) 50438 ++ (27674, 2) :: (1, 1) :: repeat (1, 2) 323288 ++ w) by sec_eq.
    apply (sTUP2_1 [20; 0] 339 613 1038 ((1, 1) :: repeat (1, 2) 2396 ++ (17815, 2) :: (1, 1) :: repeat (1, 2) 50438 ++ (27674, 2) :: (1, 1) :: repeat (1, 2) 323288 ++ w) 1); closearith.
  }
  (* step 229: P TDN *)
  apply (hsteps_trans _ (HB [340; 20; 0] 614 1 4 ((1036, 2) :: (1, 1) :: repeat (1, 2) 2396 ++ (17815, 2) :: (1, 1) :: repeat (1, 2) 50438 ++ (27674, 2) :: (1, 1) :: repeat (1, 2) 323288 ++ w) 1)).
  {
    apply (sTDN [340; 20; 0] 614 ((1036, 2) :: (1, 1) :: repeat (1, 2) 2396 ++ (17815, 2) :: (1, 1) :: repeat (1, 2) 50438 ++ (27674, 2) :: (1, 1) :: repeat (1, 2) 323288 ++ w) 1).
  }
  (* step 230: sTUP *)
  apply (hsteps_trans _ (HC [340; 20; 0] 614 3 2 ((1034, 2) :: (1, 1) :: repeat (1, 2) 2396 ++ (17815, 2) :: (1, 1) :: repeat (1, 2) 50438 ++ (27674, 2) :: (1, 1) :: repeat (1, 2) 323288 ++ w) 1)).
  {
    replace ((1034, 2) :: (1, 1) :: repeat (1, 2) 2396 ++ (17815, 2) :: (1, 1) :: repeat (1, 2) 50438 ++ (27674, 2) :: (1, 1) :: repeat (1, 2) 323288 ++ w) with ((1036 - 2, 2) :: (1, 1) :: repeat (1, 2) 2396 ++ (17815, 2) :: (1, 1) :: repeat (1, 2) 50438 ++ (27674, 2) :: (1, 1) :: repeat (1, 2) 323288 ++ w) by sec_eq.
    apply (sTUP [340; 20; 0] 614 4 1036 2 ((1, 1) :: repeat (1, 2) 2396 ++ (17815, 2) :: (1, 1) :: repeat (1, 2) 50438 ++ (27674, 2) :: (1, 1) :: repeat (1, 2) 323288 ++ w) 1); closearith.
  }
  (* step 231: CLEANG_even 516 *)
  apply (hsteps_trans _ (HB [340; 20; 0] 614 1 1038 ((2, 2) :: (1, 1) :: repeat (1, 2) 2396 ++ (17815, 2) :: (1, 1) :: repeat (1, 2) 50438 ++ (27674, 2) :: (1, 1) :: repeat (1, 2) 323288 ++ w) 1)).
  {
    apply (CLEANG_even 516 [340; 20; 0] 614 ((1, 1) :: repeat (1, 2) 2396 ++ (17815, 2) :: (1, 1) :: repeat (1, 2) 50438 ++ (27674, 2) :: (1, 1) :: repeat (1, 2) 323288 ++ w) 1); closearith.
  }
  (* step 232: P TRANS2_1 *)
  apply (hsteps_trans _ (HB [615; 340; 20; 0] 1039 1 3 (repeat (1, 2) 2396 ++ (17815, 2) :: (1, 1) :: repeat (1, 2) 50438 ++ (27674, 2) :: (1, 1) :: repeat (1, 2) 323288 ++ w) 1)).
  {
    apply (sTRANS2_1 [340; 20; 0] 614 1037 1 (repeat (1, 2) 2396 ++ (17815, 2) :: (1, 1) :: repeat (1, 2) 50438 ++ (27674, 2) :: (1, 1) :: repeat (1, 2) 323288 ++ w) 1); closearith.
  }
  (* step 233: M pop12 (2396,) *)
  apply (hsteps_trans _ (HB [615; 340; 20; 0] 3435 1 4795 ((17815, 2) :: (1, 1) :: repeat (1, 2) 50438 ++ (27674, 2) :: (1, 1) :: repeat (1, 2) 323288 ++ w) 1)).
  {
    apply (pop12 2396 [615; 340; 20; 0] 1039 3 ((17815, 2) :: (1, 1) :: repeat (1, 2) 50438 ++ (27674, 2) :: (1, 1) :: repeat (1, 2) 323288 ++ w) 1); closearith.
  }
  (* step 234: sTUP *)
  apply (hsteps_trans _ (HC [615; 340; 20; 0] 3435 4794 2 ((17813, 2) :: (1, 1) :: repeat (1, 2) 50438 ++ (27674, 2) :: (1, 1) :: repeat (1, 2) 323288 ++ w) 1)).
  {
    replace ((17813, 2) :: (1, 1) :: repeat (1, 2) 50438 ++ (27674, 2) :: (1, 1) :: repeat (1, 2) 323288 ++ w) with ((17815 - 2, 2) :: (1, 1) :: repeat (1, 2) 50438 ++ (27674, 2) :: (1, 1) :: repeat (1, 2) 323288 ++ w) by sec_eq.
    apply (sTUP [615; 340; 20; 0] 3435 4795 17815 2 ((1, 1) :: repeat (1, 2) 50438 ++ (27674, 2) :: (1, 1) :: repeat (1, 2) 323288 ++ w) 1); closearith.
  }
  (* step 235: hGRIND_even 2395 *)
  apply (hsteps_trans _ (HB [615; 340; 20; 0] 3434 1 4794 ((2, 2) :: (17813, 2) :: (1, 1) :: repeat (1, 2) 50438 ++ (27674, 2) :: (1, 1) :: repeat (1, 2) 323288 ++ w) 1)).
  {
    apply (hGRIND_even 2395 [615; 340; 20; 0] 3434 ((17813, 2) :: (1, 1) :: repeat (1, 2) 50438 ++ (27674, 2) :: (1, 1) :: repeat (1, 2) 323288 ++ w) 1); closearith.
  }
  (* step 236: P TUP2_1 *)
  apply (hsteps_trans _ (HC [3435; 615; 340; 20; 0] 4794 1 2 ((17811, 2) :: (1, 1) :: repeat (1, 2) 50438 ++ (27674, 2) :: (1, 1) :: repeat (1, 2) 323288 ++ w) 1)).
  {
    replace ((17811, 2) :: (1, 1) :: repeat (1, 2) 50438 ++ (27674, 2) :: (1, 1) :: repeat (1, 2) 323288 ++ w) with ((17813 - 2, 2) :: (1, 1) :: repeat (1, 2) 50438 ++ (27674, 2) :: (1, 1) :: repeat (1, 2) 323288 ++ w) by sec_eq.
    apply (sTUP2_1 [615; 340; 20; 0] 3434 4793 17813 ((1, 1) :: repeat (1, 2) 50438 ++ (27674, 2) :: (1, 1) :: repeat (1, 2) 323288 ++ w) 1); closearith.
  }
  (* step 237: P TDN *)
  apply (hsteps_trans _ (HB [3435; 615; 340; 20; 0] 4794 1 4 ((17811, 2) :: (1, 1) :: repeat (1, 2) 50438 ++ (27674, 2) :: (1, 1) :: repeat (1, 2) 323288 ++ w) 1)).
  {
    apply (sTDN [3435; 615; 340; 20; 0] 4794 ((17811, 2) :: (1, 1) :: repeat (1, 2) 50438 ++ (27674, 2) :: (1, 1) :: repeat (1, 2) 323288 ++ w) 1).
  }
  (* step 238: sTUP *)
  apply (hsteps_trans _ (HC [3435; 615; 340; 20; 0] 4794 3 2 ((17809, 2) :: (1, 1) :: repeat (1, 2) 50438 ++ (27674, 2) :: (1, 1) :: repeat (1, 2) 323288 ++ w) 1)).
  {
    replace ((17809, 2) :: (1, 1) :: repeat (1, 2) 50438 ++ (27674, 2) :: (1, 1) :: repeat (1, 2) 323288 ++ w) with ((17811 - 2, 2) :: (1, 1) :: repeat (1, 2) 50438 ++ (27674, 2) :: (1, 1) :: repeat (1, 2) 323288 ++ w) by sec_eq.
    apply (sTUP [3435; 615; 340; 20; 0] 4794 4 17811 2 ((1, 1) :: repeat (1, 2) 50438 ++ (27674, 2) :: (1, 1) :: repeat (1, 2) 323288 ++ w) 1); closearith.
  }
  (* step 239: DIPGRIND 4794 8221 *)
  apply (hsteps_trans _ (HC [3435; 615; 340; 20; 0] 0 3 2 (repeat (1, 2) 4794 ++ (8221, 2) :: (1, 1) :: repeat (1, 2) 50438 ++ (27674, 2) :: (1, 1) :: repeat (1, 2) 323288 ++ w) 1)).
  {
    apply (DIPGRIND 4794 8221 [3435; 615; 340; 20; 0] ((1, 1) :: repeat (1, 2) 50438 ++ (27674, 2) :: (1, 1) :: repeat (1, 2) 323288 ++ w) 1); closearith.
  }
  (* step 240: P PX2A *)
  apply (hsteps_trans _ (HC [340; 20; 0] 614 3433 2 ((1, 1) :: repeat (1, 2) 4796 ++ (8221, 2) :: (1, 1) :: repeat (1, 2) 50438 ++ (27674, 2) :: (1, 1) :: repeat (1, 2) 323288 ++ w) 1)).
  {
    apply (hsteps_step _ (HC [340; 20; 0] 614 3433 2 ((1, 1) :: repeat (1, 2) 4796 ++ (8221, 2) :: (1, 1) :: repeat (1, 2) 50438 ++ (27674, 2) :: (1, 1) :: repeat (1, 2) 323288 ++ w) 1)); [apply hPX2A | apply hsteps_refl].
  }
  (* step 241: P PUSH *)
  apply (hsteps_trans _ (HC [340; 20; 0] 613 1 2 ((3431, 2) :: (1, 1) :: repeat (1, 2) 4796 ++ (8221, 2) :: (1, 1) :: repeat (1, 2) 50438 ++ (27674, 2) :: (1, 1) :: repeat (1, 2) 323288 ++ w) 1)).
  {
    replace ((3431, 2) :: (1, 1) :: repeat (1, 2) 4796 ++ (8221, 2) :: (1, 1) :: repeat (1, 2) 50438 ++ (27674, 2) :: (1, 1) :: repeat (1, 2) 323288 ++ w) with ((3433 - 2, 2) :: (1, 1) :: repeat (1, 2) 4796 ++ (8221, 2) :: (1, 1) :: repeat (1, 2) 50438 ++ (27674, 2) :: (1, 1) :: repeat (1, 2) 323288 ++ w) by sec_eq.
    apply (sPUSH [340; 20; 0] 613 3433 ((1, 1) :: repeat (1, 2) 4796 ++ (8221, 2) :: (1, 1) :: repeat (1, 2) 50438 ++ (27674, 2) :: (1, 1) :: repeat (1, 2) 323288 ++ w) 1); closearith.
  }
  (* step 242: P TDN *)
  apply (hsteps_trans _ (HB [340; 20; 0] 613 1 4 ((3431, 2) :: (1, 1) :: repeat (1, 2) 4796 ++ (8221, 2) :: (1, 1) :: repeat (1, 2) 50438 ++ (27674, 2) :: (1, 1) :: repeat (1, 2) 323288 ++ w) 1)).
  {
    apply (sTDN [340; 20; 0] 613 ((3431, 2) :: (1, 1) :: repeat (1, 2) 4796 ++ (8221, 2) :: (1, 1) :: repeat (1, 2) 50438 ++ (27674, 2) :: (1, 1) :: repeat (1, 2) 323288 ++ w) 1).
  }
  (* step 243: sTUP *)
  apply (hsteps_trans _ (HC [340; 20; 0] 613 3 2 ((3429, 2) :: (1, 1) :: repeat (1, 2) 4796 ++ (8221, 2) :: (1, 1) :: repeat (1, 2) 50438 ++ (27674, 2) :: (1, 1) :: repeat (1, 2) 323288 ++ w) 1)).
  {
    replace ((3429, 2) :: (1, 1) :: repeat (1, 2) 4796 ++ (8221, 2) :: (1, 1) :: repeat (1, 2) 50438 ++ (27674, 2) :: (1, 1) :: repeat (1, 2) 323288 ++ w) with ((3431 - 2, 2) :: (1, 1) :: repeat (1, 2) 4796 ++ (8221, 2) :: (1, 1) :: repeat (1, 2) 50438 ++ (27674, 2) :: (1, 1) :: repeat (1, 2) 323288 ++ w) by sec_eq.
    apply (sTUP [340; 20; 0] 613 4 3431 2 ((1, 1) :: repeat (1, 2) 4796 ++ (8221, 2) :: (1, 1) :: repeat (1, 2) 50438 ++ (27674, 2) :: (1, 1) :: repeat (1, 2) 323288 ++ w) 1); closearith.
  }
  (* step 244: DIPGRIND 613 2203 *)
  apply (hsteps_trans _ (HC [340; 20; 0] 0 3 2 (repeat (1, 2) 613 ++ (2203, 2) :: (1, 1) :: repeat (1, 2) 4796 ++ (8221, 2) :: (1, 1) :: repeat (1, 2) 50438 ++ (27674, 2) :: (1, 1) :: repeat (1, 2) 323288 ++ w) 1)).
  {
    apply (DIPGRIND 613 2203 [340; 20; 0] ((1, 1) :: repeat (1, 2) 4796 ++ (8221, 2) :: (1, 1) :: repeat (1, 2) 50438 ++ (27674, 2) :: (1, 1) :: repeat (1, 2) 323288 ++ w) 1); closearith.
  }
  (* step 245: P PX2A *)
  apply (hsteps_trans _ (HC [0] 19 338 2 ((1, 1) :: repeat (1, 2) 615 ++ (2203, 2) :: (1, 1) :: repeat (1, 2) 4796 ++ (8221, 2) :: (1, 1) :: repeat (1, 2) 50438 ++ (27674, 2) :: (1, 1) :: repeat (1, 2) 323288 ++ w) 1)).
  {
    apply (hsteps_step _ (HC [0] 19 338 2 ((1, 1) :: repeat (1, 2) 615 ++ (2203, 2) :: (1, 1) :: repeat (1, 2) 4796 ++ (8221, 2) :: (1, 1) :: repeat (1, 2) 50438 ++ (27674, 2) :: (1, 1) :: repeat (1, 2) 323288 ++ w) 1)); [apply hPX2A | apply hsteps_refl].
  }
  (* step 246: P PUSH *)
  apply (hsteps_trans _ (HC [0] 18 1 2 ((336, 2) :: (1, 1) :: repeat (1, 2) 615 ++ (2203, 2) :: (1, 1) :: repeat (1, 2) 4796 ++ (8221, 2) :: (1, 1) :: repeat (1, 2) 50438 ++ (27674, 2) :: (1, 1) :: repeat (1, 2) 323288 ++ w) 1)).
  {
    replace ((336, 2) :: (1, 1) :: repeat (1, 2) 615 ++ (2203, 2) :: (1, 1) :: repeat (1, 2) 4796 ++ (8221, 2) :: (1, 1) :: repeat (1, 2) 50438 ++ (27674, 2) :: (1, 1) :: repeat (1, 2) 323288 ++ w) with ((338 - 2, 2) :: (1, 1) :: repeat (1, 2) 615 ++ (2203, 2) :: (1, 1) :: repeat (1, 2) 4796 ++ (8221, 2) :: (1, 1) :: repeat (1, 2) 50438 ++ (27674, 2) :: (1, 1) :: repeat (1, 2) 323288 ++ w) by sec_eq.
    apply (sPUSH [0] 18 338 ((1, 1) :: repeat (1, 2) 615 ++ (2203, 2) :: (1, 1) :: repeat (1, 2) 4796 ++ (8221, 2) :: (1, 1) :: repeat (1, 2) 50438 ++ (27674, 2) :: (1, 1) :: repeat (1, 2) 323288 ++ w) 1); closearith.
  }
  (* step 247: P TDN *)
  apply (hsteps_trans _ (HB [0] 18 1 4 ((336, 2) :: (1, 1) :: repeat (1, 2) 615 ++ (2203, 2) :: (1, 1) :: repeat (1, 2) 4796 ++ (8221, 2) :: (1, 1) :: repeat (1, 2) 50438 ++ (27674, 2) :: (1, 1) :: repeat (1, 2) 323288 ++ w) 1)).
  {
    apply (sTDN [0] 18 ((336, 2) :: (1, 1) :: repeat (1, 2) 615 ++ (2203, 2) :: (1, 1) :: repeat (1, 2) 4796 ++ (8221, 2) :: (1, 1) :: repeat (1, 2) 50438 ++ (27674, 2) :: (1, 1) :: repeat (1, 2) 323288 ++ w) 1).
  }
  (* step 248: sTUP *)
  apply (hsteps_trans _ (HC [0] 18 3 2 ((334, 2) :: (1, 1) :: repeat (1, 2) 615 ++ (2203, 2) :: (1, 1) :: repeat (1, 2) 4796 ++ (8221, 2) :: (1, 1) :: repeat (1, 2) 50438 ++ (27674, 2) :: (1, 1) :: repeat (1, 2) 323288 ++ w) 1)).
  {
    replace ((334, 2) :: (1, 1) :: repeat (1, 2) 615 ++ (2203, 2) :: (1, 1) :: repeat (1, 2) 4796 ++ (8221, 2) :: (1, 1) :: repeat (1, 2) 50438 ++ (27674, 2) :: (1, 1) :: repeat (1, 2) 323288 ++ w) with ((336 - 2, 2) :: (1, 1) :: repeat (1, 2) 615 ++ (2203, 2) :: (1, 1) :: repeat (1, 2) 4796 ++ (8221, 2) :: (1, 1) :: repeat (1, 2) 50438 ++ (27674, 2) :: (1, 1) :: repeat (1, 2) 323288 ++ w) by sec_eq.
    apply (sTUP [0] 18 4 336 2 ((1, 1) :: repeat (1, 2) 615 ++ (2203, 2) :: (1, 1) :: repeat (1, 2) 4796 ++ (8221, 2) :: (1, 1) :: repeat (1, 2) 50438 ++ (27674, 2) :: (1, 1) :: repeat (1, 2) 323288 ++ w) 1); closearith.
  }
  (* step 249: DIPGRIND 18 298 *)
  apply (hsteps_trans _ (HC [0] 0 3 2 (repeat (1, 2) 18 ++ (298, 2) :: (1, 1) :: repeat (1, 2) 615 ++ (2203, 2) :: (1, 1) :: repeat (1, 2) 4796 ++ (8221, 2) :: (1, 1) :: repeat (1, 2) 50438 ++ (27674, 2) :: (1, 1) :: repeat (1, 2) 323288 ++ w) 1)).
  {
    apply (DIPGRIND 18 298 [0] ((1, 1) :: repeat (1, 2) 615 ++ (2203, 2) :: (1, 1) :: repeat (1, 2) 4796 ++ (8221, 2) :: (1, 1) :: repeat (1, 2) 50438 ++ (27674, 2) :: (1, 1) :: repeat (1, 2) 323288 ++ w) 1); closearith.
  }
  (* step 250: P PX2B0 *)
  apply (hsteps_trans _ (HB [] 0 1 5 (repeat (1, 2) 19 ++ (298, 2) :: (1, 1) :: repeat (1, 2) 615 ++ (2203, 2) :: (1, 1) :: repeat (1, 2) 4796 ++ (8221, 2) :: (1, 1) :: repeat (1, 2) 50438 ++ (27674, 2) :: (1, 1) :: repeat (1, 2) 323288 ++ w) 1)).
  {
    apply (hsteps_step _ (HB [] 0 1 5 (repeat (1, 2) 19 ++ (298, 2) :: (1, 1) :: repeat (1, 2) 615 ++ (2203, 2) :: (1, 1) :: repeat (1, 2) 4796 ++ (8221, 2) :: (1, 1) :: repeat (1, 2) 50438 ++ (27674, 2) :: (1, 1) :: repeat (1, 2) 323288 ++ w) 1)); [apply hPX2B0 | apply hsteps_refl].
  }
  (* step 251: M pop12 (19,) *)
  apply (hsteps_trans _ (HB [] 19 1 43 ((298, 2) :: (1, 1) :: repeat (1, 2) 615 ++ (2203, 2) :: (1, 1) :: repeat (1, 2) 4796 ++ (8221, 2) :: (1, 1) :: repeat (1, 2) 50438 ++ (27674, 2) :: (1, 1) :: repeat (1, 2) 323288 ++ w) 1)).
  {
    apply (pop12 19 [] 0 5 ((298, 2) :: (1, 1) :: repeat (1, 2) 615 ++ (2203, 2) :: (1, 1) :: repeat (1, 2) 4796 ++ (8221, 2) :: (1, 1) :: repeat (1, 2) 50438 ++ (27674, 2) :: (1, 1) :: repeat (1, 2) 323288 ++ w) 1); closearith.
  }
  (* step 252: sTUP *)
  apply (hsteps_trans _ (HC [] 19 42 2 ((296, 2) :: (1, 1) :: repeat (1, 2) 615 ++ (2203, 2) :: (1, 1) :: repeat (1, 2) 4796 ++ (8221, 2) :: (1, 1) :: repeat (1, 2) 50438 ++ (27674, 2) :: (1, 1) :: repeat (1, 2) 323288 ++ w) 1)).
  {
    replace ((296, 2) :: (1, 1) :: repeat (1, 2) 615 ++ (2203, 2) :: (1, 1) :: repeat (1, 2) 4796 ++ (8221, 2) :: (1, 1) :: repeat (1, 2) 50438 ++ (27674, 2) :: (1, 1) :: repeat (1, 2) 323288 ++ w) with ((298 - 2, 2) :: (1, 1) :: repeat (1, 2) 615 ++ (2203, 2) :: (1, 1) :: repeat (1, 2) 4796 ++ (8221, 2) :: (1, 1) :: repeat (1, 2) 50438 ++ (27674, 2) :: (1, 1) :: repeat (1, 2) 323288 ++ w) by sec_eq.
    apply (sTUP [] 19 43 298 2 ((1, 1) :: repeat (1, 2) 615 ++ (2203, 2) :: (1, 1) :: repeat (1, 2) 4796 ++ (8221, 2) :: (1, 1) :: repeat (1, 2) 50438 ++ (27674, 2) :: (1, 1) :: repeat (1, 2) 323288 ++ w) 1); closearith.
  }
  (* step 253: P PUSH *)
  apply (hsteps_trans _ (HC [] 18 1 2 ((40, 2) :: (296, 2) :: (1, 1) :: repeat (1, 2) 615 ++ (2203, 2) :: (1, 1) :: repeat (1, 2) 4796 ++ (8221, 2) :: (1, 1) :: repeat (1, 2) 50438 ++ (27674, 2) :: (1, 1) :: repeat (1, 2) 323288 ++ w) 1)).
  {
    replace ((40, 2) :: (296, 2) :: (1, 1) :: repeat (1, 2) 615 ++ (2203, 2) :: (1, 1) :: repeat (1, 2) 4796 ++ (8221, 2) :: (1, 1) :: repeat (1, 2) 50438 ++ (27674, 2) :: (1, 1) :: repeat (1, 2) 323288 ++ w) with ((42 - 2, 2) :: (296, 2) :: (1, 1) :: repeat (1, 2) 615 ++ (2203, 2) :: (1, 1) :: repeat (1, 2) 4796 ++ (8221, 2) :: (1, 1) :: repeat (1, 2) 50438 ++ (27674, 2) :: (1, 1) :: repeat (1, 2) 323288 ++ w) by sec_eq.
    apply (sPUSH [] 18 42 ((296, 2) :: (1, 1) :: repeat (1, 2) 615 ++ (2203, 2) :: (1, 1) :: repeat (1, 2) 4796 ++ (8221, 2) :: (1, 1) :: repeat (1, 2) 50438 ++ (27674, 2) :: (1, 1) :: repeat (1, 2) 323288 ++ w) 1); closearith.
  }
  (* step 254: P TDN *)
  apply (hsteps_trans _ (HB [] 18 1 4 ((40, 2) :: (296, 2) :: (1, 1) :: repeat (1, 2) 615 ++ (2203, 2) :: (1, 1) :: repeat (1, 2) 4796 ++ (8221, 2) :: (1, 1) :: repeat (1, 2) 50438 ++ (27674, 2) :: (1, 1) :: repeat (1, 2) 323288 ++ w) 1)).
  {
    apply (sTDN [] 18 ((40, 2) :: (296, 2) :: (1, 1) :: repeat (1, 2) 615 ++ (2203, 2) :: (1, 1) :: repeat (1, 2) 4796 ++ (8221, 2) :: (1, 1) :: repeat (1, 2) 50438 ++ (27674, 2) :: (1, 1) :: repeat (1, 2) 323288 ++ w) 1).
  }
  (* step 255: sTUP *)
  apply (hsteps_trans _ (HC [] 18 3 2 ((38, 2) :: (296, 2) :: (1, 1) :: repeat (1, 2) 615 ++ (2203, 2) :: (1, 1) :: repeat (1, 2) 4796 ++ (8221, 2) :: (1, 1) :: repeat (1, 2) 50438 ++ (27674, 2) :: (1, 1) :: repeat (1, 2) 323288 ++ w) 1)).
  {
    replace ((38, 2) :: (296, 2) :: (1, 1) :: repeat (1, 2) 615 ++ (2203, 2) :: (1, 1) :: repeat (1, 2) 4796 ++ (8221, 2) :: (1, 1) :: repeat (1, 2) 50438 ++ (27674, 2) :: (1, 1) :: repeat (1, 2) 323288 ++ w) with ((40 - 2, 2) :: (296, 2) :: (1, 1) :: repeat (1, 2) 615 ++ (2203, 2) :: (1, 1) :: repeat (1, 2) 4796 ++ (8221, 2) :: (1, 1) :: repeat (1, 2) 50438 ++ (27674, 2) :: (1, 1) :: repeat (1, 2) 323288 ++ w) by sec_eq.
    apply (sTUP [] 18 4 40 2 ((296, 2) :: (1, 1) :: repeat (1, 2) 615 ++ (2203, 2) :: (1, 1) :: repeat (1, 2) 4796 ++ (8221, 2) :: (1, 1) :: repeat (1, 2) 50438 ++ (27674, 2) :: (1, 1) :: repeat (1, 2) 323288 ++ w) 1); closearith.
  }
  (* step 256: DIPGRIND 18 2 *)
  apply (hsteps_trans _ (HC [] 0 3 2 (repeat (1, 2) 18 ++ (2, 2) :: (296, 2) :: (1, 1) :: repeat (1, 2) 615 ++ (2203, 2) :: (1, 1) :: repeat (1, 2) 4796 ++ (8221, 2) :: (1, 1) :: repeat (1, 2) 50438 ++ (27674, 2) :: (1, 1) :: repeat (1, 2) 323288 ++ w) 1)).
  {
    apply (DIPGRIND 18 2 [] ((296, 2) :: (1, 1) :: repeat (1, 2) 615 ++ (2203, 2) :: (1, 1) :: repeat (1, 2) 4796 ++ (8221, 2) :: (1, 1) :: repeat (1, 2) 50438 ++ (27674, 2) :: (1, 1) :: repeat (1, 2) 323288 ++ w) 1); closearith.
  }
  (* step 257: P PUSHX *)
  apply (hsteps_trans _ (HB [] 1 1 7 (repeat (1, 2) 18 ++ (2, 2) :: (296, 2) :: (1, 1) :: repeat (1, 2) 615 ++ (2203, 2) :: (1, 1) :: repeat (1, 2) 4796 ++ (8221, 2) :: (1, 1) :: repeat (1, 2) 50438 ++ (27674, 2) :: (1, 1) :: repeat (1, 2) 323288 ++ w) 1)).
  {
    apply (hsteps_step _ (HB [] 1 1 7 (repeat (1, 2) 18 ++ (2, 2) :: (296, 2) :: (1, 1) :: repeat (1, 2) 615 ++ (2203, 2) :: (1, 1) :: repeat (1, 2) 4796 ++ (8221, 2) :: (1, 1) :: repeat (1, 2) 50438 ++ (27674, 2) :: (1, 1) :: repeat (1, 2) 323288 ++ w) 1)); [apply hPUSHX | apply hsteps_refl].
  }
  (* step 258: M pop12 (18,) *)
  apply (hsteps_trans _ (HB [] 19 1 43 ((2, 2) :: (296, 2) :: (1, 1) :: repeat (1, 2) 615 ++ (2203, 2) :: (1, 1) :: repeat (1, 2) 4796 ++ (8221, 2) :: (1, 1) :: repeat (1, 2) 50438 ++ (27674, 2) :: (1, 1) :: repeat (1, 2) 323288 ++ w) 1)).
  {
    apply (pop12 18 [] 1 7 ((2, 2) :: (296, 2) :: (1, 1) :: repeat (1, 2) 615 ++ (2203, 2) :: (1, 1) :: repeat (1, 2) 4796 ++ (8221, 2) :: (1, 1) :: repeat (1, 2) 50438 ++ (27674, 2) :: (1, 1) :: repeat (1, 2) 323288 ++ w) 1); closearith.
  }
  (* step 259: P TUP2_1 *)
  apply (hsteps_trans _ (HC [20] 43 1 2 ((294, 2) :: (1, 1) :: repeat (1, 2) 615 ++ (2203, 2) :: (1, 1) :: repeat (1, 2) 4796 ++ (8221, 2) :: (1, 1) :: repeat (1, 2) 50438 ++ (27674, 2) :: (1, 1) :: repeat (1, 2) 323288 ++ w) 1)).
  {
    replace ((294, 2) :: (1, 1) :: repeat (1, 2) 615 ++ (2203, 2) :: (1, 1) :: repeat (1, 2) 4796 ++ (8221, 2) :: (1, 1) :: repeat (1, 2) 50438 ++ (27674, 2) :: (1, 1) :: repeat (1, 2) 323288 ++ w) with ((296 - 2, 2) :: (1, 1) :: repeat (1, 2) 615 ++ (2203, 2) :: (1, 1) :: repeat (1, 2) 4796 ++ (8221, 2) :: (1, 1) :: repeat (1, 2) 50438 ++ (27674, 2) :: (1, 1) :: repeat (1, 2) 323288 ++ w) by sec_eq.
    apply (sTUP2_1 [] 19 42 296 ((1, 1) :: repeat (1, 2) 615 ++ (2203, 2) :: (1, 1) :: repeat (1, 2) 4796 ++ (8221, 2) :: (1, 1) :: repeat (1, 2) 50438 ++ (27674, 2) :: (1, 1) :: repeat (1, 2) 323288 ++ w) 1); closearith.
  }
  (* step 260: P TDN *)
  apply (hsteps_trans _ (HB [20] 43 1 4 ((294, 2) :: (1, 1) :: repeat (1, 2) 615 ++ (2203, 2) :: (1, 1) :: repeat (1, 2) 4796 ++ (8221, 2) :: (1, 1) :: repeat (1, 2) 50438 ++ (27674, 2) :: (1, 1) :: repeat (1, 2) 323288 ++ w) 1)).
  {
    apply (sTDN [20] 43 ((294, 2) :: (1, 1) :: repeat (1, 2) 615 ++ (2203, 2) :: (1, 1) :: repeat (1, 2) 4796 ++ (8221, 2) :: (1, 1) :: repeat (1, 2) 50438 ++ (27674, 2) :: (1, 1) :: repeat (1, 2) 323288 ++ w) 1).
  }
  (* step 261: sTUP *)
  apply (hsteps_trans _ (HC [20] 43 3 2 ((292, 2) :: (1, 1) :: repeat (1, 2) 615 ++ (2203, 2) :: (1, 1) :: repeat (1, 2) 4796 ++ (8221, 2) :: (1, 1) :: repeat (1, 2) 50438 ++ (27674, 2) :: (1, 1) :: repeat (1, 2) 323288 ++ w) 1)).
  {
    replace ((292, 2) :: (1, 1) :: repeat (1, 2) 615 ++ (2203, 2) :: (1, 1) :: repeat (1, 2) 4796 ++ (8221, 2) :: (1, 1) :: repeat (1, 2) 50438 ++ (27674, 2) :: (1, 1) :: repeat (1, 2) 323288 ++ w) with ((294 - 2, 2) :: (1, 1) :: repeat (1, 2) 615 ++ (2203, 2) :: (1, 1) :: repeat (1, 2) 4796 ++ (8221, 2) :: (1, 1) :: repeat (1, 2) 50438 ++ (27674, 2) :: (1, 1) :: repeat (1, 2) 323288 ++ w) by sec_eq.
    apply (sTUP [20] 43 4 294 2 ((1, 1) :: repeat (1, 2) 615 ++ (2203, 2) :: (1, 1) :: repeat (1, 2) 4796 ++ (8221, 2) :: (1, 1) :: repeat (1, 2) 50438 ++ (27674, 2) :: (1, 1) :: repeat (1, 2) 323288 ++ w) 1); closearith.
  }
  (* step 262: DIPGRIND 43 206 *)
  apply (hsteps_trans _ (HC [20] 0 3 2 (repeat (1, 2) 43 ++ (206, 2) :: (1, 1) :: repeat (1, 2) 615 ++ (2203, 2) :: (1, 1) :: repeat (1, 2) 4796 ++ (8221, 2) :: (1, 1) :: repeat (1, 2) 50438 ++ (27674, 2) :: (1, 1) :: repeat (1, 2) 323288 ++ w) 1)).
  {
    apply (DIPGRIND 43 206 [20] ((1, 1) :: repeat (1, 2) 615 ++ (2203, 2) :: (1, 1) :: repeat (1, 2) 4796 ++ (8221, 2) :: (1, 1) :: repeat (1, 2) 50438 ++ (27674, 2) :: (1, 1) :: repeat (1, 2) 323288 ++ w) 1); closearith.
  }
  (* step 263: P PX2Bgen *)
  apply (hsteps_trans _ (HB [0] 3 1 2 ((16, 2) :: (1, 1) :: repeat (1, 2) 45 ++ (206, 2) :: (1, 1) :: repeat (1, 2) 615 ++ (2203, 2) :: (1, 1) :: repeat (1, 2) 4796 ++ (8221, 2) :: (1, 1) :: repeat (1, 2) 50438 ++ (27674, 2) :: (1, 1) :: repeat (1, 2) 323288 ++ w) 1)).
  {
    apply (hsteps_step _ (HB [0] 3 1 2 ((16, 2) :: (1, 1) :: repeat (1, 2) 45 ++ (206, 2) :: (1, 1) :: repeat (1, 2) 615 ++ (2203, 2) :: (1, 1) :: repeat (1, 2) 4796 ++ (8221, 2) :: (1, 1) :: repeat (1, 2) 50438 ++ (27674, 2) :: (1, 1) :: repeat (1, 2) 323288 ++ w) 1)); [apply hPX2Bgen | apply hsteps_refl].
  }
  (* step 264: sTUP *)
  apply (hsteps_trans _ (HC [0] 3 1 2 ((14, 2) :: (1, 1) :: repeat (1, 2) 45 ++ (206, 2) :: (1, 1) :: repeat (1, 2) 615 ++ (2203, 2) :: (1, 1) :: repeat (1, 2) 4796 ++ (8221, 2) :: (1, 1) :: repeat (1, 2) 50438 ++ (27674, 2) :: (1, 1) :: repeat (1, 2) 323288 ++ w) 1)).
  {
    replace ((14, 2) :: (1, 1) :: repeat (1, 2) 45 ++ (206, 2) :: (1, 1) :: repeat (1, 2) 615 ++ (2203, 2) :: (1, 1) :: repeat (1, 2) 4796 ++ (8221, 2) :: (1, 1) :: repeat (1, 2) 50438 ++ (27674, 2) :: (1, 1) :: repeat (1, 2) 323288 ++ w) with ((16 - 2, 2) :: (1, 1) :: repeat (1, 2) 45 ++ (206, 2) :: (1, 1) :: repeat (1, 2) 615 ++ (2203, 2) :: (1, 1) :: repeat (1, 2) 4796 ++ (8221, 2) :: (1, 1) :: repeat (1, 2) 50438 ++ (27674, 2) :: (1, 1) :: repeat (1, 2) 323288 ++ w) by sec_eq.
    apply (sTUP [0] 3 2 16 2 ((1, 1) :: repeat (1, 2) 45 ++ (206, 2) :: (1, 1) :: repeat (1, 2) 615 ++ (2203, 2) :: (1, 1) :: repeat (1, 2) 4796 ++ (8221, 2) :: (1, 1) :: repeat (1, 2) 50438 ++ (27674, 2) :: (1, 1) :: repeat (1, 2) 323288 ++ w) 1); closearith.
  }
  (* step 265: P TDN *)
  apply (hsteps_trans _ (HB [0] 3 1 4 ((14, 2) :: (1, 1) :: repeat (1, 2) 45 ++ (206, 2) :: (1, 1) :: repeat (1, 2) 615 ++ (2203, 2) :: (1, 1) :: repeat (1, 2) 4796 ++ (8221, 2) :: (1, 1) :: repeat (1, 2) 50438 ++ (27674, 2) :: (1, 1) :: repeat (1, 2) 323288 ++ w) 1)).
  {
    apply (sTDN [0] 3 ((14, 2) :: (1, 1) :: repeat (1, 2) 45 ++ (206, 2) :: (1, 1) :: repeat (1, 2) 615 ++ (2203, 2) :: (1, 1) :: repeat (1, 2) 4796 ++ (8221, 2) :: (1, 1) :: repeat (1, 2) 50438 ++ (27674, 2) :: (1, 1) :: repeat (1, 2) 323288 ++ w) 1).
  }
  (* step 266: sTUP *)
  apply (hsteps_trans _ (HC [0] 3 3 2 ((12, 2) :: (1, 1) :: repeat (1, 2) 45 ++ (206, 2) :: (1, 1) :: repeat (1, 2) 615 ++ (2203, 2) :: (1, 1) :: repeat (1, 2) 4796 ++ (8221, 2) :: (1, 1) :: repeat (1, 2) 50438 ++ (27674, 2) :: (1, 1) :: repeat (1, 2) 323288 ++ w) 1)).
  {
    replace ((12, 2) :: (1, 1) :: repeat (1, 2) 45 ++ (206, 2) :: (1, 1) :: repeat (1, 2) 615 ++ (2203, 2) :: (1, 1) :: repeat (1, 2) 4796 ++ (8221, 2) :: (1, 1) :: repeat (1, 2) 50438 ++ (27674, 2) :: (1, 1) :: repeat (1, 2) 323288 ++ w) with ((14 - 2, 2) :: (1, 1) :: repeat (1, 2) 45 ++ (206, 2) :: (1, 1) :: repeat (1, 2) 615 ++ (2203, 2) :: (1, 1) :: repeat (1, 2) 4796 ++ (8221, 2) :: (1, 1) :: repeat (1, 2) 50438 ++ (27674, 2) :: (1, 1) :: repeat (1, 2) 323288 ++ w) by sec_eq.
    apply (sTUP [0] 3 4 14 2 ((1, 1) :: repeat (1, 2) 45 ++ (206, 2) :: (1, 1) :: repeat (1, 2) 615 ++ (2203, 2) :: (1, 1) :: repeat (1, 2) 4796 ++ (8221, 2) :: (1, 1) :: repeat (1, 2) 50438 ++ (27674, 2) :: (1, 1) :: repeat (1, 2) 323288 ++ w) 1); closearith.
  }
  (* step 267: DIPGRIND 3 6 *)
  apply (hsteps_trans _ (HC [0] 0 3 2 (repeat (1, 2) 3 ++ (6, 2) :: (1, 1) :: repeat (1, 2) 45 ++ (206, 2) :: (1, 1) :: repeat (1, 2) 615 ++ (2203, 2) :: (1, 1) :: repeat (1, 2) 4796 ++ (8221, 2) :: (1, 1) :: repeat (1, 2) 50438 ++ (27674, 2) :: (1, 1) :: repeat (1, 2) 323288 ++ w) 1)).
  {
    apply (DIPGRIND 3 6 [0] ((1, 1) :: repeat (1, 2) 45 ++ (206, 2) :: (1, 1) :: repeat (1, 2) 615 ++ (2203, 2) :: (1, 1) :: repeat (1, 2) 4796 ++ (8221, 2) :: (1, 1) :: repeat (1, 2) 50438 ++ (27674, 2) :: (1, 1) :: repeat (1, 2) 323288 ++ w) 1); closearith.
  }
  (* step 268: P PX2B0 *)
  apply (hsteps_trans _ (HB [] 0 1 5 (repeat (1, 2) 4 ++ (6, 2) :: (1, 1) :: repeat (1, 2) 45 ++ (206, 2) :: (1, 1) :: repeat (1, 2) 615 ++ (2203, 2) :: (1, 1) :: repeat (1, 2) 4796 ++ (8221, 2) :: (1, 1) :: repeat (1, 2) 50438 ++ (27674, 2) :: (1, 1) :: repeat (1, 2) 323288 ++ w) 1)).
  {
    apply (hsteps_step _ (HB [] 0 1 5 (repeat (1, 2) 4 ++ (6, 2) :: (1, 1) :: repeat (1, 2) 45 ++ (206, 2) :: (1, 1) :: repeat (1, 2) 615 ++ (2203, 2) :: (1, 1) :: repeat (1, 2) 4796 ++ (8221, 2) :: (1, 1) :: repeat (1, 2) 50438 ++ (27674, 2) :: (1, 1) :: repeat (1, 2) 323288 ++ w) 1)); [apply hPX2B0 | apply hsteps_refl].
  }
  (* step 269: M pop12 (4,) *)
  apply (hsteps_trans _ (HB [] 4 1 13 ((6, 2) :: (1, 1) :: repeat (1, 2) 45 ++ (206, 2) :: (1, 1) :: repeat (1, 2) 615 ++ (2203, 2) :: (1, 1) :: repeat (1, 2) 4796 ++ (8221, 2) :: (1, 1) :: repeat (1, 2) 50438 ++ (27674, 2) :: (1, 1) :: repeat (1, 2) 323288 ++ w) 1)).
  {
    apply (pop12 4 [] 0 5 ((6, 2) :: (1, 1) :: repeat (1, 2) 45 ++ (206, 2) :: (1, 1) :: repeat (1, 2) 615 ++ (2203, 2) :: (1, 1) :: repeat (1, 2) 4796 ++ (8221, 2) :: (1, 1) :: repeat (1, 2) 50438 ++ (27674, 2) :: (1, 1) :: repeat (1, 2) 323288 ++ w) 1); closearith.
  }
  (* step 270: sTUP *)
  apply (hsteps_trans _ (HC [] 4 12 2 ((4, 2) :: (1, 1) :: repeat (1, 2) 45 ++ (206, 2) :: (1, 1) :: repeat (1, 2) 615 ++ (2203, 2) :: (1, 1) :: repeat (1, 2) 4796 ++ (8221, 2) :: (1, 1) :: repeat (1, 2) 50438 ++ (27674, 2) :: (1, 1) :: repeat (1, 2) 323288 ++ w) 1)).
  {
    replace ((4, 2) :: (1, 1) :: repeat (1, 2) 45 ++ (206, 2) :: (1, 1) :: repeat (1, 2) 615 ++ (2203, 2) :: (1, 1) :: repeat (1, 2) 4796 ++ (8221, 2) :: (1, 1) :: repeat (1, 2) 50438 ++ (27674, 2) :: (1, 1) :: repeat (1, 2) 323288 ++ w) with ((6 - 2, 2) :: (1, 1) :: repeat (1, 2) 45 ++ (206, 2) :: (1, 1) :: repeat (1, 2) 615 ++ (2203, 2) :: (1, 1) :: repeat (1, 2) 4796 ++ (8221, 2) :: (1, 1) :: repeat (1, 2) 50438 ++ (27674, 2) :: (1, 1) :: repeat (1, 2) 323288 ++ w) by sec_eq.
    apply (sTUP [] 4 13 6 2 ((1, 1) :: repeat (1, 2) 45 ++ (206, 2) :: (1, 1) :: repeat (1, 2) 615 ++ (2203, 2) :: (1, 1) :: repeat (1, 2) 4796 ++ (8221, 2) :: (1, 1) :: repeat (1, 2) 50438 ++ (27674, 2) :: (1, 1) :: repeat (1, 2) 323288 ++ w) 1); closearith.
  }
  (* step 271: P PUSH *)
  apply (hsteps_trans _ (HC [] 3 1 2 ((10, 2) :: (4, 2) :: (1, 1) :: repeat (1, 2) 45 ++ (206, 2) :: (1, 1) :: repeat (1, 2) 615 ++ (2203, 2) :: (1, 1) :: repeat (1, 2) 4796 ++ (8221, 2) :: (1, 1) :: repeat (1, 2) 50438 ++ (27674, 2) :: (1, 1) :: repeat (1, 2) 323288 ++ w) 1)).
  {
    replace ((10, 2) :: (4, 2) :: (1, 1) :: repeat (1, 2) 45 ++ (206, 2) :: (1, 1) :: repeat (1, 2) 615 ++ (2203, 2) :: (1, 1) :: repeat (1, 2) 4796 ++ (8221, 2) :: (1, 1) :: repeat (1, 2) 50438 ++ (27674, 2) :: (1, 1) :: repeat (1, 2) 323288 ++ w) with ((12 - 2, 2) :: (4, 2) :: (1, 1) :: repeat (1, 2) 45 ++ (206, 2) :: (1, 1) :: repeat (1, 2) 615 ++ (2203, 2) :: (1, 1) :: repeat (1, 2) 4796 ++ (8221, 2) :: (1, 1) :: repeat (1, 2) 50438 ++ (27674, 2) :: (1, 1) :: repeat (1, 2) 323288 ++ w) by sec_eq.
    apply (sPUSH [] 3 12 ((4, 2) :: (1, 1) :: repeat (1, 2) 45 ++ (206, 2) :: (1, 1) :: repeat (1, 2) 615 ++ (2203, 2) :: (1, 1) :: repeat (1, 2) 4796 ++ (8221, 2) :: (1, 1) :: repeat (1, 2) 50438 ++ (27674, 2) :: (1, 1) :: repeat (1, 2) 323288 ++ w) 1); closearith.
  }
  (* step 272: P TDN *)
  apply (hsteps_trans _ (HB [] 3 1 4 ((10, 2) :: (4, 2) :: (1, 1) :: repeat (1, 2) 45 ++ (206, 2) :: (1, 1) :: repeat (1, 2) 615 ++ (2203, 2) :: (1, 1) :: repeat (1, 2) 4796 ++ (8221, 2) :: (1, 1) :: repeat (1, 2) 50438 ++ (27674, 2) :: (1, 1) :: repeat (1, 2) 323288 ++ w) 1)).
  {
    apply (sTDN [] 3 ((10, 2) :: (4, 2) :: (1, 1) :: repeat (1, 2) 45 ++ (206, 2) :: (1, 1) :: repeat (1, 2) 615 ++ (2203, 2) :: (1, 1) :: repeat (1, 2) 4796 ++ (8221, 2) :: (1, 1) :: repeat (1, 2) 50438 ++ (27674, 2) :: (1, 1) :: repeat (1, 2) 323288 ++ w) 1).
  }
  (* step 273: sTUP *)
  apply (hsteps_trans _ (HC [] 3 3 2 ((8, 2) :: (4, 2) :: (1, 1) :: repeat (1, 2) 45 ++ (206, 2) :: (1, 1) :: repeat (1, 2) 615 ++ (2203, 2) :: (1, 1) :: repeat (1, 2) 4796 ++ (8221, 2) :: (1, 1) :: repeat (1, 2) 50438 ++ (27674, 2) :: (1, 1) :: repeat (1, 2) 323288 ++ w) 1)).
  {
    replace ((8, 2) :: (4, 2) :: (1, 1) :: repeat (1, 2) 45 ++ (206, 2) :: (1, 1) :: repeat (1, 2) 615 ++ (2203, 2) :: (1, 1) :: repeat (1, 2) 4796 ++ (8221, 2) :: (1, 1) :: repeat (1, 2) 50438 ++ (27674, 2) :: (1, 1) :: repeat (1, 2) 323288 ++ w) with ((10 - 2, 2) :: (4, 2) :: (1, 1) :: repeat (1, 2) 45 ++ (206, 2) :: (1, 1) :: repeat (1, 2) 615 ++ (2203, 2) :: (1, 1) :: repeat (1, 2) 4796 ++ (8221, 2) :: (1, 1) :: repeat (1, 2) 50438 ++ (27674, 2) :: (1, 1) :: repeat (1, 2) 323288 ++ w) by sec_eq.
    apply (sTUP [] 3 4 10 2 ((4, 2) :: (1, 1) :: repeat (1, 2) 45 ++ (206, 2) :: (1, 1) :: repeat (1, 2) 615 ++ (2203, 2) :: (1, 1) :: repeat (1, 2) 4796 ++ (8221, 2) :: (1, 1) :: repeat (1, 2) 50438 ++ (27674, 2) :: (1, 1) :: repeat (1, 2) 323288 ++ w) 1); closearith.
  }
  (* step 274: DIPGRIND 3 2 *)
  apply (hsteps_trans _ (HC [] 0 3 2 (repeat (1, 2) 3 ++ (2, 2) :: (4, 2) :: (1, 1) :: repeat (1, 2) 45 ++ (206, 2) :: (1, 1) :: repeat (1, 2) 615 ++ (2203, 2) :: (1, 1) :: repeat (1, 2) 4796 ++ (8221, 2) :: (1, 1) :: repeat (1, 2) 50438 ++ (27674, 2) :: (1, 1) :: repeat (1, 2) 323288 ++ w) 1)).
  {
    apply (DIPGRIND 3 2 [] ((4, 2) :: (1, 1) :: repeat (1, 2) 45 ++ (206, 2) :: (1, 1) :: repeat (1, 2) 615 ++ (2203, 2) :: (1, 1) :: repeat (1, 2) 4796 ++ (8221, 2) :: (1, 1) :: repeat (1, 2) 50438 ++ (27674, 2) :: (1, 1) :: repeat (1, 2) 323288 ++ w) 1); closearith.
  }
  (* step 275: P PUSHX *)
  apply (hsteps_trans _ (HB [] 1 1 7 (repeat (1, 2) 3 ++ (2, 2) :: (4, 2) :: (1, 1) :: repeat (1, 2) 45 ++ (206, 2) :: (1, 1) :: repeat (1, 2) 615 ++ (2203, 2) :: (1, 1) :: repeat (1, 2) 4796 ++ (8221, 2) :: (1, 1) :: repeat (1, 2) 50438 ++ (27674, 2) :: (1, 1) :: repeat (1, 2) 323288 ++ w) 1)).
  {
    apply (hsteps_step _ (HB [] 1 1 7 (repeat (1, 2) 3 ++ (2, 2) :: (4, 2) :: (1, 1) :: repeat (1, 2) 45 ++ (206, 2) :: (1, 1) :: repeat (1, 2) 615 ++ (2203, 2) :: (1, 1) :: repeat (1, 2) 4796 ++ (8221, 2) :: (1, 1) :: repeat (1, 2) 50438 ++ (27674, 2) :: (1, 1) :: repeat (1, 2) 323288 ++ w) 1)); [apply hPUSHX | apply hsteps_refl].
  }
  (* step 276: M pop12 (3,) *)
  apply (hsteps_trans _ (HB [] 4 1 13 ((2, 2) :: (4, 2) :: (1, 1) :: repeat (1, 2) 45 ++ (206, 2) :: (1, 1) :: repeat (1, 2) 615 ++ (2203, 2) :: (1, 1) :: repeat (1, 2) 4796 ++ (8221, 2) :: (1, 1) :: repeat (1, 2) 50438 ++ (27674, 2) :: (1, 1) :: repeat (1, 2) 323288 ++ w) 1)).
  {
    apply (pop12 3 [] 1 7 ((2, 2) :: (4, 2) :: (1, 1) :: repeat (1, 2) 45 ++ (206, 2) :: (1, 1) :: repeat (1, 2) 615 ++ (2203, 2) :: (1, 1) :: repeat (1, 2) 4796 ++ (8221, 2) :: (1, 1) :: repeat (1, 2) 50438 ++ (27674, 2) :: (1, 1) :: repeat (1, 2) 323288 ++ w) 1); closearith.
  }
  (* step 277: P TUP2_1 *)
  apply (hsteps_trans _ (HC [5] 13 1 2 ((2, 2) :: (1, 1) :: repeat (1, 2) 45 ++ (206, 2) :: (1, 1) :: repeat (1, 2) 615 ++ (2203, 2) :: (1, 1) :: repeat (1, 2) 4796 ++ (8221, 2) :: (1, 1) :: repeat (1, 2) 50438 ++ (27674, 2) :: (1, 1) :: repeat (1, 2) 323288 ++ w) 1)).
  {
    replace ((2, 2) :: (1, 1) :: repeat (1, 2) 45 ++ (206, 2) :: (1, 1) :: repeat (1, 2) 615 ++ (2203, 2) :: (1, 1) :: repeat (1, 2) 4796 ++ (8221, 2) :: (1, 1) :: repeat (1, 2) 50438 ++ (27674, 2) :: (1, 1) :: repeat (1, 2) 323288 ++ w) with ((4 - 2, 2) :: (1, 1) :: repeat (1, 2) 45 ++ (206, 2) :: (1, 1) :: repeat (1, 2) 615 ++ (2203, 2) :: (1, 1) :: repeat (1, 2) 4796 ++ (8221, 2) :: (1, 1) :: repeat (1, 2) 50438 ++ (27674, 2) :: (1, 1) :: repeat (1, 2) 323288 ++ w) by sec_eq.
    apply (sTUP2_1 [] 4 12 4 ((1, 1) :: repeat (1, 2) 45 ++ (206, 2) :: (1, 1) :: repeat (1, 2) 615 ++ (2203, 2) :: (1, 1) :: repeat (1, 2) 4796 ++ (8221, 2) :: (1, 1) :: repeat (1, 2) 50438 ++ (27674, 2) :: (1, 1) :: repeat (1, 2) 323288 ++ w) 1); closearith.
  }
  (* step 278: P TDN *)
  apply (hsteps_trans _ (HB [5] 13 1 4 ((2, 2) :: (1, 1) :: repeat (1, 2) 45 ++ (206, 2) :: (1, 1) :: repeat (1, 2) 615 ++ (2203, 2) :: (1, 1) :: repeat (1, 2) 4796 ++ (8221, 2) :: (1, 1) :: repeat (1, 2) 50438 ++ (27674, 2) :: (1, 1) :: repeat (1, 2) 323288 ++ w) 1)).
  {
    apply (sTDN [5] 13 ((2, 2) :: (1, 1) :: repeat (1, 2) 45 ++ (206, 2) :: (1, 1) :: repeat (1, 2) 615 ++ (2203, 2) :: (1, 1) :: repeat (1, 2) 4796 ++ (8221, 2) :: (1, 1) :: repeat (1, 2) 50438 ++ (27674, 2) :: (1, 1) :: repeat (1, 2) 323288 ++ w) 1).
  }
  (* step 279: P TRANS2_1 *)
  apply (hsteps_trans _ (HB [14; 5] 5 1 3 (repeat (1, 2) 45 ++ (206, 2) :: (1, 1) :: repeat (1, 2) 615 ++ (2203, 2) :: (1, 1) :: repeat (1, 2) 4796 ++ (8221, 2) :: (1, 1) :: repeat (1, 2) 50438 ++ (27674, 2) :: (1, 1) :: repeat (1, 2) 323288 ++ w) 1)).
  {
    apply (sTRANS2_1 [5] 13 3 1 (repeat (1, 2) 45 ++ (206, 2) :: (1, 1) :: repeat (1, 2) 615 ++ (2203, 2) :: (1, 1) :: repeat (1, 2) 4796 ++ (8221, 2) :: (1, 1) :: repeat (1, 2) 50438 ++ (27674, 2) :: (1, 1) :: repeat (1, 2) 323288 ++ w) 1); closearith.
  }
  (* step 280: M pop12 (45,) *)
  apply (pop12 45 [14; 5] 5 3 ((206, 2) :: (1, 1) :: repeat (1, 2) 615 ++ (2203, 2) :: (1, 1) :: repeat (1, 2) 4796 ++ (8221, 2) :: (1, 1) :: repeat (1, 2) 50438 ++ (27674, 2) :: (1, 1) :: repeat (1, 2) 323288 ++ w) 1); closearith.
Qed.

(* CASCADE53f: steps 281-336 of the CASCADE53 chain. *)
Lemma CASCADE53f : forall w,
  hsteps (HB [14; 5] 50 1 93 ((206, 2) :: (1, 1) :: repeat (1, 2) 615 ++ (2203, 2) :: (1, 1) :: repeat (1, 2) 4796 ++ (8221, 2) :: (1, 1) :: repeat (1, 2) 50438 ++ (27674, 2) :: (1, 1) :: repeat (1, 2) 323288 ++ w) 1)
         (HB [109099; 62236; 6030; 630; 191; 113; 33; 19; 0] 27673 1 3 (repeat (1, 2) 323288 ++ w) 1).
Proof.
  intro w.
  (* step 281: sTUP *)
  apply (hsteps_trans _ (HC [14; 5] 50 92 2 ((204, 2) :: (1, 1) :: repeat (1, 2) 615 ++ (2203, 2) :: (1, 1) :: repeat (1, 2) 4796 ++ (8221, 2) :: (1, 1) :: repeat (1, 2) 50438 ++ (27674, 2) :: (1, 1) :: repeat (1, 2) 323288 ++ w) 1)).
  {
    replace ((204, 2) :: (1, 1) :: repeat (1, 2) 615 ++ (2203, 2) :: (1, 1) :: repeat (1, 2) 4796 ++ (8221, 2) :: (1, 1) :: repeat (1, 2) 50438 ++ (27674, 2) :: (1, 1) :: repeat (1, 2) 323288 ++ w) with ((206 - 2, 2) :: (1, 1) :: repeat (1, 2) 615 ++ (2203, 2) :: (1, 1) :: repeat (1, 2) 4796 ++ (8221, 2) :: (1, 1) :: repeat (1, 2) 50438 ++ (27674, 2) :: (1, 1) :: repeat (1, 2) 323288 ++ w) by sec_eq.
    apply (sTUP [14; 5] 50 93 206 2 ((1, 1) :: repeat (1, 2) 615 ++ (2203, 2) :: (1, 1) :: repeat (1, 2) 4796 ++ (8221, 2) :: (1, 1) :: repeat (1, 2) 50438 ++ (27674, 2) :: (1, 1) :: repeat (1, 2) 323288 ++ w) 1); closearith.
  }
  (* step 282: hGRIND_even 44 *)
  apply (hsteps_trans _ (HB [14; 5] 49 1 92 ((2, 2) :: (204, 2) :: (1, 1) :: repeat (1, 2) 615 ++ (2203, 2) :: (1, 1) :: repeat (1, 2) 4796 ++ (8221, 2) :: (1, 1) :: repeat (1, 2) 50438 ++ (27674, 2) :: (1, 1) :: repeat (1, 2) 323288 ++ w) 1)).
  {
    apply (hGRIND_even 44 [14; 5] 49 ((204, 2) :: (1, 1) :: repeat (1, 2) 615 ++ (2203, 2) :: (1, 1) :: repeat (1, 2) 4796 ++ (8221, 2) :: (1, 1) :: repeat (1, 2) 50438 ++ (27674, 2) :: (1, 1) :: repeat (1, 2) 323288 ++ w) 1); closearith.
  }
  (* step 283: P TUP2_1 *)
  apply (hsteps_trans _ (HC [50; 14; 5] 92 1 2 ((202, 2) :: (1, 1) :: repeat (1, 2) 615 ++ (2203, 2) :: (1, 1) :: repeat (1, 2) 4796 ++ (8221, 2) :: (1, 1) :: repeat (1, 2) 50438 ++ (27674, 2) :: (1, 1) :: repeat (1, 2) 323288 ++ w) 1)).
  {
    replace ((202, 2) :: (1, 1) :: repeat (1, 2) 615 ++ (2203, 2) :: (1, 1) :: repeat (1, 2) 4796 ++ (8221, 2) :: (1, 1) :: repeat (1, 2) 50438 ++ (27674, 2) :: (1, 1) :: repeat (1, 2) 323288 ++ w) with ((204 - 2, 2) :: (1, 1) :: repeat (1, 2) 615 ++ (2203, 2) :: (1, 1) :: repeat (1, 2) 4796 ++ (8221, 2) :: (1, 1) :: repeat (1, 2) 50438 ++ (27674, 2) :: (1, 1) :: repeat (1, 2) 323288 ++ w) by sec_eq.
    apply (sTUP2_1 [14; 5] 49 91 204 ((1, 1) :: repeat (1, 2) 615 ++ (2203, 2) :: (1, 1) :: repeat (1, 2) 4796 ++ (8221, 2) :: (1, 1) :: repeat (1, 2) 50438 ++ (27674, 2) :: (1, 1) :: repeat (1, 2) 323288 ++ w) 1); closearith.
  }
  (* step 284: P TDN *)
  apply (hsteps_trans _ (HB [50; 14; 5] 92 1 4 ((202, 2) :: (1, 1) :: repeat (1, 2) 615 ++ (2203, 2) :: (1, 1) :: repeat (1, 2) 4796 ++ (8221, 2) :: (1, 1) :: repeat (1, 2) 50438 ++ (27674, 2) :: (1, 1) :: repeat (1, 2) 323288 ++ w) 1)).
  {
    apply (sTDN [50; 14; 5] 92 ((202, 2) :: (1, 1) :: repeat (1, 2) 615 ++ (2203, 2) :: (1, 1) :: repeat (1, 2) 4796 ++ (8221, 2) :: (1, 1) :: repeat (1, 2) 50438 ++ (27674, 2) :: (1, 1) :: repeat (1, 2) 323288 ++ w) 1).
  }
  (* step 285: sTUP *)
  apply (hsteps_trans _ (HC [50; 14; 5] 92 3 2 ((200, 2) :: (1, 1) :: repeat (1, 2) 615 ++ (2203, 2) :: (1, 1) :: repeat (1, 2) 4796 ++ (8221, 2) :: (1, 1) :: repeat (1, 2) 50438 ++ (27674, 2) :: (1, 1) :: repeat (1, 2) 323288 ++ w) 1)).
  {
    replace ((200, 2) :: (1, 1) :: repeat (1, 2) 615 ++ (2203, 2) :: (1, 1) :: repeat (1, 2) 4796 ++ (8221, 2) :: (1, 1) :: repeat (1, 2) 50438 ++ (27674, 2) :: (1, 1) :: repeat (1, 2) 323288 ++ w) with ((202 - 2, 2) :: (1, 1) :: repeat (1, 2) 615 ++ (2203, 2) :: (1, 1) :: repeat (1, 2) 4796 ++ (8221, 2) :: (1, 1) :: repeat (1, 2) 50438 ++ (27674, 2) :: (1, 1) :: repeat (1, 2) 323288 ++ w) by sec_eq.
    apply (sTUP [50; 14; 5] 92 4 202 2 ((1, 1) :: repeat (1, 2) 615 ++ (2203, 2) :: (1, 1) :: repeat (1, 2) 4796 ++ (8221, 2) :: (1, 1) :: repeat (1, 2) 50438 ++ (27674, 2) :: (1, 1) :: repeat (1, 2) 323288 ++ w) 1); closearith.
  }
  (* step 286: DIPGRIND 92 16 *)
  apply (hsteps_trans _ (HC [50; 14; 5] 0 3 2 (repeat (1, 2) 92 ++ (16, 2) :: (1, 1) :: repeat (1, 2) 615 ++ (2203, 2) :: (1, 1) :: repeat (1, 2) 4796 ++ (8221, 2) :: (1, 1) :: repeat (1, 2) 50438 ++ (27674, 2) :: (1, 1) :: repeat (1, 2) 323288 ++ w) 1)).
  {
    apply (DIPGRIND 92 16 [50; 14; 5] ((1, 1) :: repeat (1, 2) 615 ++ (2203, 2) :: (1, 1) :: repeat (1, 2) 4796 ++ (8221, 2) :: (1, 1) :: repeat (1, 2) 50438 ++ (27674, 2) :: (1, 1) :: repeat (1, 2) 323288 ++ w) 1); closearith.
  }
  (* step 287: P PX2A *)
  apply (hsteps_trans _ (HC [5] 13 48 2 ((1, 1) :: repeat (1, 2) 94 ++ (16, 2) :: (1, 1) :: repeat (1, 2) 615 ++ (2203, 2) :: (1, 1) :: repeat (1, 2) 4796 ++ (8221, 2) :: (1, 1) :: repeat (1, 2) 50438 ++ (27674, 2) :: (1, 1) :: repeat (1, 2) 323288 ++ w) 1)).
  {
    apply (hsteps_step _ (HC [5] 13 48 2 ((1, 1) :: repeat (1, 2) 94 ++ (16, 2) :: (1, 1) :: repeat (1, 2) 615 ++ (2203, 2) :: (1, 1) :: repeat (1, 2) 4796 ++ (8221, 2) :: (1, 1) :: repeat (1, 2) 50438 ++ (27674, 2) :: (1, 1) :: repeat (1, 2) 323288 ++ w) 1)); [apply hPX2A | apply hsteps_refl].
  }
  (* step 288: P PUSH *)
  apply (hsteps_trans _ (HC [5] 12 1 2 ((46, 2) :: (1, 1) :: repeat (1, 2) 94 ++ (16, 2) :: (1, 1) :: repeat (1, 2) 615 ++ (2203, 2) :: (1, 1) :: repeat (1, 2) 4796 ++ (8221, 2) :: (1, 1) :: repeat (1, 2) 50438 ++ (27674, 2) :: (1, 1) :: repeat (1, 2) 323288 ++ w) 1)).
  {
    replace ((46, 2) :: (1, 1) :: repeat (1, 2) 94 ++ (16, 2) :: (1, 1) :: repeat (1, 2) 615 ++ (2203, 2) :: (1, 1) :: repeat (1, 2) 4796 ++ (8221, 2) :: (1, 1) :: repeat (1, 2) 50438 ++ (27674, 2) :: (1, 1) :: repeat (1, 2) 323288 ++ w) with ((48 - 2, 2) :: (1, 1) :: repeat (1, 2) 94 ++ (16, 2) :: (1, 1) :: repeat (1, 2) 615 ++ (2203, 2) :: (1, 1) :: repeat (1, 2) 4796 ++ (8221, 2) :: (1, 1) :: repeat (1, 2) 50438 ++ (27674, 2) :: (1, 1) :: repeat (1, 2) 323288 ++ w) by sec_eq.
    apply (sPUSH [5] 12 48 ((1, 1) :: repeat (1, 2) 94 ++ (16, 2) :: (1, 1) :: repeat (1, 2) 615 ++ (2203, 2) :: (1, 1) :: repeat (1, 2) 4796 ++ (8221, 2) :: (1, 1) :: repeat (1, 2) 50438 ++ (27674, 2) :: (1, 1) :: repeat (1, 2) 323288 ++ w) 1); closearith.
  }
  (* step 289: P TDN *)
  apply (hsteps_trans _ (HB [5] 12 1 4 ((46, 2) :: (1, 1) :: repeat (1, 2) 94 ++ (16, 2) :: (1, 1) :: repeat (1, 2) 615 ++ (2203, 2) :: (1, 1) :: repeat (1, 2) 4796 ++ (8221, 2) :: (1, 1) :: repeat (1, 2) 50438 ++ (27674, 2) :: (1, 1) :: repeat (1, 2) 323288 ++ w) 1)).
  {
    apply (sTDN [5] 12 ((46, 2) :: (1, 1) :: repeat (1, 2) 94 ++ (16, 2) :: (1, 1) :: repeat (1, 2) 615 ++ (2203, 2) :: (1, 1) :: repeat (1, 2) 4796 ++ (8221, 2) :: (1, 1) :: repeat (1, 2) 50438 ++ (27674, 2) :: (1, 1) :: repeat (1, 2) 323288 ++ w) 1).
  }
  (* step 290: sTUP *)
  apply (hsteps_trans _ (HC [5] 12 3 2 ((44, 2) :: (1, 1) :: repeat (1, 2) 94 ++ (16, 2) :: (1, 1) :: repeat (1, 2) 615 ++ (2203, 2) :: (1, 1) :: repeat (1, 2) 4796 ++ (8221, 2) :: (1, 1) :: repeat (1, 2) 50438 ++ (27674, 2) :: (1, 1) :: repeat (1, 2) 323288 ++ w) 1)).
  {
    replace ((44, 2) :: (1, 1) :: repeat (1, 2) 94 ++ (16, 2) :: (1, 1) :: repeat (1, 2) 615 ++ (2203, 2) :: (1, 1) :: repeat (1, 2) 4796 ++ (8221, 2) :: (1, 1) :: repeat (1, 2) 50438 ++ (27674, 2) :: (1, 1) :: repeat (1, 2) 323288 ++ w) with ((46 - 2, 2) :: (1, 1) :: repeat (1, 2) 94 ++ (16, 2) :: (1, 1) :: repeat (1, 2) 615 ++ (2203, 2) :: (1, 1) :: repeat (1, 2) 4796 ++ (8221, 2) :: (1, 1) :: repeat (1, 2) 50438 ++ (27674, 2) :: (1, 1) :: repeat (1, 2) 323288 ++ w) by sec_eq.
    apply (sTUP [5] 12 4 46 2 ((1, 1) :: repeat (1, 2) 94 ++ (16, 2) :: (1, 1) :: repeat (1, 2) 615 ++ (2203, 2) :: (1, 1) :: repeat (1, 2) 4796 ++ (8221, 2) :: (1, 1) :: repeat (1, 2) 50438 ++ (27674, 2) :: (1, 1) :: repeat (1, 2) 323288 ++ w) 1); closearith.
  }
  (* step 291: DIPGRIND 12 20 *)
  apply (hsteps_trans _ (HC [5] 0 3 2 (repeat (1, 2) 12 ++ (20, 2) :: (1, 1) :: repeat (1, 2) 94 ++ (16, 2) :: (1, 1) :: repeat (1, 2) 615 ++ (2203, 2) :: (1, 1) :: repeat (1, 2) 4796 ++ (8221, 2) :: (1, 1) :: repeat (1, 2) 50438 ++ (27674, 2) :: (1, 1) :: repeat (1, 2) 323288 ++ w) 1)).
  {
    apply (DIPGRIND 12 20 [5] ((1, 1) :: repeat (1, 2) 94 ++ (16, 2) :: (1, 1) :: repeat (1, 2) 615 ++ (2203, 2) :: (1, 1) :: repeat (1, 2) 4796 ++ (8221, 2) :: (1, 1) :: repeat (1, 2) 50438 ++ (27674, 2) :: (1, 1) :: repeat (1, 2) 323288 ++ w) 1); closearith.
  }
  (* step 292: P PX2Bgen *)
  apply (hsteps_trans _ (HB [0] 3 1 2 (repeat (1, 2) 1 ++ (1, 1) :: repeat (1, 2) 14 ++ (20, 2) :: (1, 1) :: repeat (1, 2) 94 ++ (16, 2) :: (1, 1) :: repeat (1, 2) 615 ++ (2203, 2) :: (1, 1) :: repeat (1, 2) 4796 ++ (8221, 2) :: (1, 1) :: repeat (1, 2) 50438 ++ (27674, 2) :: (1, 1) :: repeat (1, 2) 323288 ++ w) 1)).
  {
    apply (hsteps_step _ (HB [0] 3 1 2 (repeat (1, 2) 1 ++ (1, 1) :: repeat (1, 2) 14 ++ (20, 2) :: (1, 1) :: repeat (1, 2) 94 ++ (16, 2) :: (1, 1) :: repeat (1, 2) 615 ++ (2203, 2) :: (1, 1) :: repeat (1, 2) 4796 ++ (8221, 2) :: (1, 1) :: repeat (1, 2) 50438 ++ (27674, 2) :: (1, 1) :: repeat (1, 2) 323288 ++ w) 1)); [apply hPX2Bgen | apply hsteps_refl].
  }
  (* step 293: M pop12 (1,) *)
  apply (hsteps_trans _ (HB [0] 4 1 4 ((1, 1) :: repeat (1, 2) 14 ++ (20, 2) :: (1, 1) :: repeat (1, 2) 94 ++ (16, 2) :: (1, 1) :: repeat (1, 2) 615 ++ (2203, 2) :: (1, 1) :: repeat (1, 2) 4796 ++ (8221, 2) :: (1, 1) :: repeat (1, 2) 50438 ++ (27674, 2) :: (1, 1) :: repeat (1, 2) 323288 ++ w) 1)).
  {
    apply (pop12 1 [0] 3 2 ((1, 1) :: repeat (1, 2) 14 ++ (20, 2) :: (1, 1) :: repeat (1, 2) 94 ++ (16, 2) :: (1, 1) :: repeat (1, 2) 615 ++ (2203, 2) :: (1, 1) :: repeat (1, 2) 4796 ++ (8221, 2) :: (1, 1) :: repeat (1, 2) 50438 ++ (27674, 2) :: (1, 1) :: repeat (1, 2) 323288 ++ w) 1); closearith.
  }
  (* step 294: P POP *)
  apply (hsteps_trans _ (HB [0] 5 1 5 (repeat (1, 2) 14 ++ (20, 2) :: (1, 1) :: repeat (1, 2) 94 ++ (16, 2) :: (1, 1) :: repeat (1, 2) 615 ++ (2203, 2) :: (1, 1) :: repeat (1, 2) 4796 ++ (8221, 2) :: (1, 1) :: repeat (1, 2) 50438 ++ (27674, 2) :: (1, 1) :: repeat (1, 2) 323288 ++ w) 1)).
  {
    apply (sPOP1 [0] 4 4 (repeat (1, 2) 14 ++ (20, 2) :: (1, 1) :: repeat (1, 2) 94 ++ (16, 2) :: (1, 1) :: repeat (1, 2) 615 ++ (2203, 2) :: (1, 1) :: repeat (1, 2) 4796 ++ (8221, 2) :: (1, 1) :: repeat (1, 2) 50438 ++ (27674, 2) :: (1, 1) :: repeat (1, 2) 323288 ++ w) 1); closearith.
  }
  (* step 295: M pop12 (14,) *)
  apply (hsteps_trans _ (HB [0] 19 1 33 ((20, 2) :: (1, 1) :: repeat (1, 2) 94 ++ (16, 2) :: (1, 1) :: repeat (1, 2) 615 ++ (2203, 2) :: (1, 1) :: repeat (1, 2) 4796 ++ (8221, 2) :: (1, 1) :: repeat (1, 2) 50438 ++ (27674, 2) :: (1, 1) :: repeat (1, 2) 323288 ++ w) 1)).
  {
    apply (pop12 14 [0] 5 5 ((20, 2) :: (1, 1) :: repeat (1, 2) 94 ++ (16, 2) :: (1, 1) :: repeat (1, 2) 615 ++ (2203, 2) :: (1, 1) :: repeat (1, 2) 4796 ++ (8221, 2) :: (1, 1) :: repeat (1, 2) 50438 ++ (27674, 2) :: (1, 1) :: repeat (1, 2) 323288 ++ w) 1); closearith.
  }
  (* step 296: sTUP *)
  apply (hsteps_trans _ (HC [0] 19 32 2 ((18, 2) :: (1, 1) :: repeat (1, 2) 94 ++ (16, 2) :: (1, 1) :: repeat (1, 2) 615 ++ (2203, 2) :: (1, 1) :: repeat (1, 2) 4796 ++ (8221, 2) :: (1, 1) :: repeat (1, 2) 50438 ++ (27674, 2) :: (1, 1) :: repeat (1, 2) 323288 ++ w) 1)).
  {
    replace ((18, 2) :: (1, 1) :: repeat (1, 2) 94 ++ (16, 2) :: (1, 1) :: repeat (1, 2) 615 ++ (2203, 2) :: (1, 1) :: repeat (1, 2) 4796 ++ (8221, 2) :: (1, 1) :: repeat (1, 2) 50438 ++ (27674, 2) :: (1, 1) :: repeat (1, 2) 323288 ++ w) with ((20 - 2, 2) :: (1, 1) :: repeat (1, 2) 94 ++ (16, 2) :: (1, 1) :: repeat (1, 2) 615 ++ (2203, 2) :: (1, 1) :: repeat (1, 2) 4796 ++ (8221, 2) :: (1, 1) :: repeat (1, 2) 50438 ++ (27674, 2) :: (1, 1) :: repeat (1, 2) 323288 ++ w) by sec_eq.
    apply (sTUP [0] 19 33 20 2 ((1, 1) :: repeat (1, 2) 94 ++ (16, 2) :: (1, 1) :: repeat (1, 2) 615 ++ (2203, 2) :: (1, 1) :: repeat (1, 2) 4796 ++ (8221, 2) :: (1, 1) :: repeat (1, 2) 50438 ++ (27674, 2) :: (1, 1) :: repeat (1, 2) 323288 ++ w) 1); closearith.
  }
  (* step 297: hGRIND_even 14 *)
  apply (hsteps_trans _ (HB [0] 18 1 32 ((2, 2) :: (18, 2) :: (1, 1) :: repeat (1, 2) 94 ++ (16, 2) :: (1, 1) :: repeat (1, 2) 615 ++ (2203, 2) :: (1, 1) :: repeat (1, 2) 4796 ++ (8221, 2) :: (1, 1) :: repeat (1, 2) 50438 ++ (27674, 2) :: (1, 1) :: repeat (1, 2) 323288 ++ w) 1)).
  {
    apply (hGRIND_even 14 [0] 18 ((18, 2) :: (1, 1) :: repeat (1, 2) 94 ++ (16, 2) :: (1, 1) :: repeat (1, 2) 615 ++ (2203, 2) :: (1, 1) :: repeat (1, 2) 4796 ++ (8221, 2) :: (1, 1) :: repeat (1, 2) 50438 ++ (27674, 2) :: (1, 1) :: repeat (1, 2) 323288 ++ w) 1); closearith.
  }
  (* step 298: P TUP2_1 *)
  apply (hsteps_trans _ (HC [19; 0] 32 1 2 ((16, 2) :: (1, 1) :: repeat (1, 2) 94 ++ (16, 2) :: (1, 1) :: repeat (1, 2) 615 ++ (2203, 2) :: (1, 1) :: repeat (1, 2) 4796 ++ (8221, 2) :: (1, 1) :: repeat (1, 2) 50438 ++ (27674, 2) :: (1, 1) :: repeat (1, 2) 323288 ++ w) 1)).
  {
    replace ((16, 2) :: (1, 1) :: repeat (1, 2) 94 ++ (16, 2) :: (1, 1) :: repeat (1, 2) 615 ++ (2203, 2) :: (1, 1) :: repeat (1, 2) 4796 ++ (8221, 2) :: (1, 1) :: repeat (1, 2) 50438 ++ (27674, 2) :: (1, 1) :: repeat (1, 2) 323288 ++ w) with ((18 - 2, 2) :: (1, 1) :: repeat (1, 2) 94 ++ (16, 2) :: (1, 1) :: repeat (1, 2) 615 ++ (2203, 2) :: (1, 1) :: repeat (1, 2) 4796 ++ (8221, 2) :: (1, 1) :: repeat (1, 2) 50438 ++ (27674, 2) :: (1, 1) :: repeat (1, 2) 323288 ++ w) by sec_eq.
    apply (sTUP2_1 [0] 18 31 18 ((1, 1) :: repeat (1, 2) 94 ++ (16, 2) :: (1, 1) :: repeat (1, 2) 615 ++ (2203, 2) :: (1, 1) :: repeat (1, 2) 4796 ++ (8221, 2) :: (1, 1) :: repeat (1, 2) 50438 ++ (27674, 2) :: (1, 1) :: repeat (1, 2) 323288 ++ w) 1); closearith.
  }
  (* step 299: P TDN *)
  apply (hsteps_trans _ (HB [19; 0] 32 1 4 ((16, 2) :: (1, 1) :: repeat (1, 2) 94 ++ (16, 2) :: (1, 1) :: repeat (1, 2) 615 ++ (2203, 2) :: (1, 1) :: repeat (1, 2) 4796 ++ (8221, 2) :: (1, 1) :: repeat (1, 2) 50438 ++ (27674, 2) :: (1, 1) :: repeat (1, 2) 323288 ++ w) 1)).
  {
    apply (sTDN [19; 0] 32 ((16, 2) :: (1, 1) :: repeat (1, 2) 94 ++ (16, 2) :: (1, 1) :: repeat (1, 2) 615 ++ (2203, 2) :: (1, 1) :: repeat (1, 2) 4796 ++ (8221, 2) :: (1, 1) :: repeat (1, 2) 50438 ++ (27674, 2) :: (1, 1) :: repeat (1, 2) 323288 ++ w) 1).
  }
  (* step 300: sTUP *)
  apply (hsteps_trans _ (HC [19; 0] 32 3 2 ((14, 2) :: (1, 1) :: repeat (1, 2) 94 ++ (16, 2) :: (1, 1) :: repeat (1, 2) 615 ++ (2203, 2) :: (1, 1) :: repeat (1, 2) 4796 ++ (8221, 2) :: (1, 1) :: repeat (1, 2) 50438 ++ (27674, 2) :: (1, 1) :: repeat (1, 2) 323288 ++ w) 1)).
  {
    replace ((14, 2) :: (1, 1) :: repeat (1, 2) 94 ++ (16, 2) :: (1, 1) :: repeat (1, 2) 615 ++ (2203, 2) :: (1, 1) :: repeat (1, 2) 4796 ++ (8221, 2) :: (1, 1) :: repeat (1, 2) 50438 ++ (27674, 2) :: (1, 1) :: repeat (1, 2) 323288 ++ w) with ((16 - 2, 2) :: (1, 1) :: repeat (1, 2) 94 ++ (16, 2) :: (1, 1) :: repeat (1, 2) 615 ++ (2203, 2) :: (1, 1) :: repeat (1, 2) 4796 ++ (8221, 2) :: (1, 1) :: repeat (1, 2) 50438 ++ (27674, 2) :: (1, 1) :: repeat (1, 2) 323288 ++ w) by sec_eq.
    apply (sTUP [19; 0] 32 4 16 2 ((1, 1) :: repeat (1, 2) 94 ++ (16, 2) :: (1, 1) :: repeat (1, 2) 615 ++ (2203, 2) :: (1, 1) :: repeat (1, 2) 4796 ++ (8221, 2) :: (1, 1) :: repeat (1, 2) 50438 ++ (27674, 2) :: (1, 1) :: repeat (1, 2) 323288 ++ w) 1); closearith.
  }
  (* step 301: CLEANG_even 6 *)
  apply (hsteps_trans _ (HB [19; 0] 32 1 18 ((2, 2) :: (1, 1) :: repeat (1, 2) 94 ++ (16, 2) :: (1, 1) :: repeat (1, 2) 615 ++ (2203, 2) :: (1, 1) :: repeat (1, 2) 4796 ++ (8221, 2) :: (1, 1) :: repeat (1, 2) 50438 ++ (27674, 2) :: (1, 1) :: repeat (1, 2) 323288 ++ w) 1)).
  {
    apply (CLEANG_even 6 [19; 0] 32 ((1, 1) :: repeat (1, 2) 94 ++ (16, 2) :: (1, 1) :: repeat (1, 2) 615 ++ (2203, 2) :: (1, 1) :: repeat (1, 2) 4796 ++ (8221, 2) :: (1, 1) :: repeat (1, 2) 50438 ++ (27674, 2) :: (1, 1) :: repeat (1, 2) 323288 ++ w) 1); closearith.
  }
  (* step 302: P TRANS2_1 *)
  apply (hsteps_trans _ (HB [33; 19; 0] 19 1 3 (repeat (1, 2) 94 ++ (16, 2) :: (1, 1) :: repeat (1, 2) 615 ++ (2203, 2) :: (1, 1) :: repeat (1, 2) 4796 ++ (8221, 2) :: (1, 1) :: repeat (1, 2) 50438 ++ (27674, 2) :: (1, 1) :: repeat (1, 2) 323288 ++ w) 1)).
  {
    apply (sTRANS2_1 [19; 0] 32 17 1 (repeat (1, 2) 94 ++ (16, 2) :: (1, 1) :: repeat (1, 2) 615 ++ (2203, 2) :: (1, 1) :: repeat (1, 2) 4796 ++ (8221, 2) :: (1, 1) :: repeat (1, 2) 50438 ++ (27674, 2) :: (1, 1) :: repeat (1, 2) 323288 ++ w) 1); closearith.
  }
  (* step 303: M pop12 (94,) *)
  apply (hsteps_trans _ (HB [33; 19; 0] 113 1 191 ((16, 2) :: (1, 1) :: repeat (1, 2) 615 ++ (2203, 2) :: (1, 1) :: repeat (1, 2) 4796 ++ (8221, 2) :: (1, 1) :: repeat (1, 2) 50438 ++ (27674, 2) :: (1, 1) :: repeat (1, 2) 323288 ++ w) 1)).
  {
    apply (pop12 94 [33; 19; 0] 19 3 ((16, 2) :: (1, 1) :: repeat (1, 2) 615 ++ (2203, 2) :: (1, 1) :: repeat (1, 2) 4796 ++ (8221, 2) :: (1, 1) :: repeat (1, 2) 50438 ++ (27674, 2) :: (1, 1) :: repeat (1, 2) 323288 ++ w) 1); closearith.
  }
  (* step 304: sTUP *)
  apply (hsteps_trans _ (HC [33; 19; 0] 113 190 2 ((14, 2) :: (1, 1) :: repeat (1, 2) 615 ++ (2203, 2) :: (1, 1) :: repeat (1, 2) 4796 ++ (8221, 2) :: (1, 1) :: repeat (1, 2) 50438 ++ (27674, 2) :: (1, 1) :: repeat (1, 2) 323288 ++ w) 1)).
  {
    replace ((14, 2) :: (1, 1) :: repeat (1, 2) 615 ++ (2203, 2) :: (1, 1) :: repeat (1, 2) 4796 ++ (8221, 2) :: (1, 1) :: repeat (1, 2) 50438 ++ (27674, 2) :: (1, 1) :: repeat (1, 2) 323288 ++ w) with ((16 - 2, 2) :: (1, 1) :: repeat (1, 2) 615 ++ (2203, 2) :: (1, 1) :: repeat (1, 2) 4796 ++ (8221, 2) :: (1, 1) :: repeat (1, 2) 50438 ++ (27674, 2) :: (1, 1) :: repeat (1, 2) 323288 ++ w) by sec_eq.
    apply (sTUP [33; 19; 0] 113 191 16 2 ((1, 1) :: repeat (1, 2) 615 ++ (2203, 2) :: (1, 1) :: repeat (1, 2) 4796 ++ (8221, 2) :: (1, 1) :: repeat (1, 2) 50438 ++ (27674, 2) :: (1, 1) :: repeat (1, 2) 323288 ++ w) 1); closearith.
  }
  (* step 305: hGRIND_even 93 *)
  apply (hsteps_trans _ (HB [33; 19; 0] 112 1 190 ((2, 2) :: (14, 2) :: (1, 1) :: repeat (1, 2) 615 ++ (2203, 2) :: (1, 1) :: repeat (1, 2) 4796 ++ (8221, 2) :: (1, 1) :: repeat (1, 2) 50438 ++ (27674, 2) :: (1, 1) :: repeat (1, 2) 323288 ++ w) 1)).
  {
    apply (hGRIND_even 93 [33; 19; 0] 112 ((14, 2) :: (1, 1) :: repeat (1, 2) 615 ++ (2203, 2) :: (1, 1) :: repeat (1, 2) 4796 ++ (8221, 2) :: (1, 1) :: repeat (1, 2) 50438 ++ (27674, 2) :: (1, 1) :: repeat (1, 2) 323288 ++ w) 1); closearith.
  }
  (* step 306: P TUP2_1 *)
  apply (hsteps_trans _ (HC [113; 33; 19; 0] 190 1 2 ((12, 2) :: (1, 1) :: repeat (1, 2) 615 ++ (2203, 2) :: (1, 1) :: repeat (1, 2) 4796 ++ (8221, 2) :: (1, 1) :: repeat (1, 2) 50438 ++ (27674, 2) :: (1, 1) :: repeat (1, 2) 323288 ++ w) 1)).
  {
    replace ((12, 2) :: (1, 1) :: repeat (1, 2) 615 ++ (2203, 2) :: (1, 1) :: repeat (1, 2) 4796 ++ (8221, 2) :: (1, 1) :: repeat (1, 2) 50438 ++ (27674, 2) :: (1, 1) :: repeat (1, 2) 323288 ++ w) with ((14 - 2, 2) :: (1, 1) :: repeat (1, 2) 615 ++ (2203, 2) :: (1, 1) :: repeat (1, 2) 4796 ++ (8221, 2) :: (1, 1) :: repeat (1, 2) 50438 ++ (27674, 2) :: (1, 1) :: repeat (1, 2) 323288 ++ w) by sec_eq.
    apply (sTUP2_1 [33; 19; 0] 112 189 14 ((1, 1) :: repeat (1, 2) 615 ++ (2203, 2) :: (1, 1) :: repeat (1, 2) 4796 ++ (8221, 2) :: (1, 1) :: repeat (1, 2) 50438 ++ (27674, 2) :: (1, 1) :: repeat (1, 2) 323288 ++ w) 1); closearith.
  }
  (* step 307: P TDN *)
  apply (hsteps_trans _ (HB [113; 33; 19; 0] 190 1 4 ((12, 2) :: (1, 1) :: repeat (1, 2) 615 ++ (2203, 2) :: (1, 1) :: repeat (1, 2) 4796 ++ (8221, 2) :: (1, 1) :: repeat (1, 2) 50438 ++ (27674, 2) :: (1, 1) :: repeat (1, 2) 323288 ++ w) 1)).
  {
    apply (sTDN [113; 33; 19; 0] 190 ((12, 2) :: (1, 1) :: repeat (1, 2) 615 ++ (2203, 2) :: (1, 1) :: repeat (1, 2) 4796 ++ (8221, 2) :: (1, 1) :: repeat (1, 2) 50438 ++ (27674, 2) :: (1, 1) :: repeat (1, 2) 323288 ++ w) 1).
  }
  (* step 308: sTUP *)
  apply (hsteps_trans _ (HC [113; 33; 19; 0] 190 3 2 ((10, 2) :: (1, 1) :: repeat (1, 2) 615 ++ (2203, 2) :: (1, 1) :: repeat (1, 2) 4796 ++ (8221, 2) :: (1, 1) :: repeat (1, 2) 50438 ++ (27674, 2) :: (1, 1) :: repeat (1, 2) 323288 ++ w) 1)).
  {
    replace ((10, 2) :: (1, 1) :: repeat (1, 2) 615 ++ (2203, 2) :: (1, 1) :: repeat (1, 2) 4796 ++ (8221, 2) :: (1, 1) :: repeat (1, 2) 50438 ++ (27674, 2) :: (1, 1) :: repeat (1, 2) 323288 ++ w) with ((12 - 2, 2) :: (1, 1) :: repeat (1, 2) 615 ++ (2203, 2) :: (1, 1) :: repeat (1, 2) 4796 ++ (8221, 2) :: (1, 1) :: repeat (1, 2) 50438 ++ (27674, 2) :: (1, 1) :: repeat (1, 2) 323288 ++ w) by sec_eq.
    apply (sTUP [113; 33; 19; 0] 190 4 12 2 ((1, 1) :: repeat (1, 2) 615 ++ (2203, 2) :: (1, 1) :: repeat (1, 2) 4796 ++ (8221, 2) :: (1, 1) :: repeat (1, 2) 50438 ++ (27674, 2) :: (1, 1) :: repeat (1, 2) 323288 ++ w) 1); closearith.
  }
  (* step 309: CLEANG_even 4 *)
  apply (hsteps_trans _ (HB [113; 33; 19; 0] 190 1 14 ((2, 2) :: (1, 1) :: repeat (1, 2) 615 ++ (2203, 2) :: (1, 1) :: repeat (1, 2) 4796 ++ (8221, 2) :: (1, 1) :: repeat (1, 2) 50438 ++ (27674, 2) :: (1, 1) :: repeat (1, 2) 323288 ++ w) 1)).
  {
    apply (CLEANG_even 4 [113; 33; 19; 0] 190 ((1, 1) :: repeat (1, 2) 615 ++ (2203, 2) :: (1, 1) :: repeat (1, 2) 4796 ++ (8221, 2) :: (1, 1) :: repeat (1, 2) 50438 ++ (27674, 2) :: (1, 1) :: repeat (1, 2) 323288 ++ w) 1); closearith.
  }
  (* step 310: P TRANS2_1 *)
  apply (hsteps_trans _ (HB [191; 113; 33; 19; 0] 15 1 3 (repeat (1, 2) 615 ++ (2203, 2) :: (1, 1) :: repeat (1, 2) 4796 ++ (8221, 2) :: (1, 1) :: repeat (1, 2) 50438 ++ (27674, 2) :: (1, 1) :: repeat (1, 2) 323288 ++ w) 1)).
  {
    apply (sTRANS2_1 [113; 33; 19; 0] 190 13 1 (repeat (1, 2) 615 ++ (2203, 2) :: (1, 1) :: repeat (1, 2) 4796 ++ (8221, 2) :: (1, 1) :: repeat (1, 2) 50438 ++ (27674, 2) :: (1, 1) :: repeat (1, 2) 323288 ++ w) 1); closearith.
  }
  (* step 311: M pop12 (615,) *)
  apply (hsteps_trans _ (HB [191; 113; 33; 19; 0] 630 1 1233 ((2203, 2) :: (1, 1) :: repeat (1, 2) 4796 ++ (8221, 2) :: (1, 1) :: repeat (1, 2) 50438 ++ (27674, 2) :: (1, 1) :: repeat (1, 2) 323288 ++ w) 1)).
  {
    apply (pop12 615 [191; 113; 33; 19; 0] 15 3 ((2203, 2) :: (1, 1) :: repeat (1, 2) 4796 ++ (8221, 2) :: (1, 1) :: repeat (1, 2) 50438 ++ (27674, 2) :: (1, 1) :: repeat (1, 2) 323288 ++ w) 1); closearith.
  }
  (* step 312: sTUP *)
  apply (hsteps_trans _ (HC [191; 113; 33; 19; 0] 630 1232 2 ((2201, 2) :: (1, 1) :: repeat (1, 2) 4796 ++ (8221, 2) :: (1, 1) :: repeat (1, 2) 50438 ++ (27674, 2) :: (1, 1) :: repeat (1, 2) 323288 ++ w) 1)).
  {
    replace ((2201, 2) :: (1, 1) :: repeat (1, 2) 4796 ++ (8221, 2) :: (1, 1) :: repeat (1, 2) 50438 ++ (27674, 2) :: (1, 1) :: repeat (1, 2) 323288 ++ w) with ((2203 - 2, 2) :: (1, 1) :: repeat (1, 2) 4796 ++ (8221, 2) :: (1, 1) :: repeat (1, 2) 50438 ++ (27674, 2) :: (1, 1) :: repeat (1, 2) 323288 ++ w) by sec_eq.
    apply (sTUP [191; 113; 33; 19; 0] 630 1233 2203 2 ((1, 1) :: repeat (1, 2) 4796 ++ (8221, 2) :: (1, 1) :: repeat (1, 2) 50438 ++ (27674, 2) :: (1, 1) :: repeat (1, 2) 323288 ++ w) 1); closearith.
  }
  (* step 313: hGRIND_even 614 *)
  apply (hsteps_trans _ (HB [191; 113; 33; 19; 0] 629 1 1232 ((2, 2) :: (2201, 2) :: (1, 1) :: repeat (1, 2) 4796 ++ (8221, 2) :: (1, 1) :: repeat (1, 2) 50438 ++ (27674, 2) :: (1, 1) :: repeat (1, 2) 323288 ++ w) 1)).
  {
    apply (hGRIND_even 614 [191; 113; 33; 19; 0] 629 ((2201, 2) :: (1, 1) :: repeat (1, 2) 4796 ++ (8221, 2) :: (1, 1) :: repeat (1, 2) 50438 ++ (27674, 2) :: (1, 1) :: repeat (1, 2) 323288 ++ w) 1); closearith.
  }
  (* step 314: P TUP2_1 *)
  apply (hsteps_trans _ (HC [630; 191; 113; 33; 19; 0] 1232 1 2 ((2199, 2) :: (1, 1) :: repeat (1, 2) 4796 ++ (8221, 2) :: (1, 1) :: repeat (1, 2) 50438 ++ (27674, 2) :: (1, 1) :: repeat (1, 2) 323288 ++ w) 1)).
  {
    replace ((2199, 2) :: (1, 1) :: repeat (1, 2) 4796 ++ (8221, 2) :: (1, 1) :: repeat (1, 2) 50438 ++ (27674, 2) :: (1, 1) :: repeat (1, 2) 323288 ++ w) with ((2201 - 2, 2) :: (1, 1) :: repeat (1, 2) 4796 ++ (8221, 2) :: (1, 1) :: repeat (1, 2) 50438 ++ (27674, 2) :: (1, 1) :: repeat (1, 2) 323288 ++ w) by sec_eq.
    apply (sTUP2_1 [191; 113; 33; 19; 0] 629 1231 2201 ((1, 1) :: repeat (1, 2) 4796 ++ (8221, 2) :: (1, 1) :: repeat (1, 2) 50438 ++ (27674, 2) :: (1, 1) :: repeat (1, 2) 323288 ++ w) 1); closearith.
  }
  (* step 315: P TDN *)
  apply (hsteps_trans _ (HB [630; 191; 113; 33; 19; 0] 1232 1 4 ((2199, 2) :: (1, 1) :: repeat (1, 2) 4796 ++ (8221, 2) :: (1, 1) :: repeat (1, 2) 50438 ++ (27674, 2) :: (1, 1) :: repeat (1, 2) 323288 ++ w) 1)).
  {
    apply (sTDN [630; 191; 113; 33; 19; 0] 1232 ((2199, 2) :: (1, 1) :: repeat (1, 2) 4796 ++ (8221, 2) :: (1, 1) :: repeat (1, 2) 50438 ++ (27674, 2) :: (1, 1) :: repeat (1, 2) 323288 ++ w) 1).
  }
  (* step 316: sTUP *)
  apply (hsteps_trans _ (HC [630; 191; 113; 33; 19; 0] 1232 3 2 ((2197, 2) :: (1, 1) :: repeat (1, 2) 4796 ++ (8221, 2) :: (1, 1) :: repeat (1, 2) 50438 ++ (27674, 2) :: (1, 1) :: repeat (1, 2) 323288 ++ w) 1)).
  {
    replace ((2197, 2) :: (1, 1) :: repeat (1, 2) 4796 ++ (8221, 2) :: (1, 1) :: repeat (1, 2) 50438 ++ (27674, 2) :: (1, 1) :: repeat (1, 2) 323288 ++ w) with ((2199 - 2, 2) :: (1, 1) :: repeat (1, 2) 4796 ++ (8221, 2) :: (1, 1) :: repeat (1, 2) 50438 ++ (27674, 2) :: (1, 1) :: repeat (1, 2) 323288 ++ w) by sec_eq.
    apply (sTUP [630; 191; 113; 33; 19; 0] 1232 4 2199 2 ((1, 1) :: repeat (1, 2) 4796 ++ (8221, 2) :: (1, 1) :: repeat (1, 2) 50438 ++ (27674, 2) :: (1, 1) :: repeat (1, 2) 323288 ++ w) 1); closearith.
  }
  (* step 317: CLEANG_odd 1097 *)
  apply (hsteps_trans _ (HB [630; 191; 113; 33; 19; 0] 1232 1 2202 (repeat (1, 2) 1 ++ (1, 1) :: repeat (1, 2) 4796 ++ (8221, 2) :: (1, 1) :: repeat (1, 2) 50438 ++ (27674, 2) :: (1, 1) :: repeat (1, 2) 323288 ++ w) 1)).
  {
    replace (repeat (1, 2) 1 ++ (1, 1) :: repeat (1, 2) 4796 ++ (8221, 2) :: (1, 1) :: repeat (1, 2) 50438 ++ (27674, 2) :: (1, 1) :: repeat (1, 2) 323288 ++ w) with ((1, 2) :: (1, 1) :: repeat (1, 2) 4796 ++ (8221, 2) :: (1, 1) :: repeat (1, 2) 50438 ++ (27674, 2) :: (1, 1) :: repeat (1, 2) 323288 ++ w) by sec_eq.
    apply (CLEANG_odd 1097 [630; 191; 113; 33; 19; 0] 1232 ((1, 1) :: repeat (1, 2) 4796 ++ (8221, 2) :: (1, 1) :: repeat (1, 2) 50438 ++ (27674, 2) :: (1, 1) :: repeat (1, 2) 323288 ++ w) 1); closearith.
  }
  (* step 318: M pop12 (1,) *)
  apply (hsteps_trans _ (HB [630; 191; 113; 33; 19; 0] 1233 1 2204 ((1, 1) :: repeat (1, 2) 4796 ++ (8221, 2) :: (1, 1) :: repeat (1, 2) 50438 ++ (27674, 2) :: (1, 1) :: repeat (1, 2) 323288 ++ w) 1)).
  {
    apply (pop12 1 [630; 191; 113; 33; 19; 0] 1232 2202 ((1, 1) :: repeat (1, 2) 4796 ++ (8221, 2) :: (1, 1) :: repeat (1, 2) 50438 ++ (27674, 2) :: (1, 1) :: repeat (1, 2) 323288 ++ w) 1); closearith.
  }
  (* step 319: P POP *)
  apply (hsteps_trans _ (HB [630; 191; 113; 33; 19; 0] 1234 1 2205 (repeat (1, 2) 4796 ++ (8221, 2) :: (1, 1) :: repeat (1, 2) 50438 ++ (27674, 2) :: (1, 1) :: repeat (1, 2) 323288 ++ w) 1)).
  {
    apply (sPOP1 [630; 191; 113; 33; 19; 0] 1233 2204 (repeat (1, 2) 4796 ++ (8221, 2) :: (1, 1) :: repeat (1, 2) 50438 ++ (27674, 2) :: (1, 1) :: repeat (1, 2) 323288 ++ w) 1); closearith.
  }
  (* step 320: M pop12 (4796,) *)
  apply (hsteps_trans _ (HB [630; 191; 113; 33; 19; 0] 6030 1 11797 ((8221, 2) :: (1, 1) :: repeat (1, 2) 50438 ++ (27674, 2) :: (1, 1) :: repeat (1, 2) 323288 ++ w) 1)).
  {
    apply (pop12 4796 [630; 191; 113; 33; 19; 0] 1234 2205 ((8221, 2) :: (1, 1) :: repeat (1, 2) 50438 ++ (27674, 2) :: (1, 1) :: repeat (1, 2) 323288 ++ w) 1); closearith.
  }
  (* step 321: sTUP *)
  apply (hsteps_trans _ (HC [630; 191; 113; 33; 19; 0] 6030 11796 2 ((8219, 2) :: (1, 1) :: repeat (1, 2) 50438 ++ (27674, 2) :: (1, 1) :: repeat (1, 2) 323288 ++ w) 1)).
  {
    replace ((8219, 2) :: (1, 1) :: repeat (1, 2) 50438 ++ (27674, 2) :: (1, 1) :: repeat (1, 2) 323288 ++ w) with ((8221 - 2, 2) :: (1, 1) :: repeat (1, 2) 50438 ++ (27674, 2) :: (1, 1) :: repeat (1, 2) 323288 ++ w) by sec_eq.
    apply (sTUP [630; 191; 113; 33; 19; 0] 6030 11797 8221 2 ((1, 1) :: repeat (1, 2) 50438 ++ (27674, 2) :: (1, 1) :: repeat (1, 2) 323288 ++ w) 1); closearith.
  }
  (* step 322: hGRIND_even 5896 *)
  apply (hsteps_trans _ (HB [630; 191; 113; 33; 19; 0] 6029 1 11796 ((2, 2) :: (8219, 2) :: (1, 1) :: repeat (1, 2) 50438 ++ (27674, 2) :: (1, 1) :: repeat (1, 2) 323288 ++ w) 1)).
  {
    apply (hGRIND_even 5896 [630; 191; 113; 33; 19; 0] 6029 ((8219, 2) :: (1, 1) :: repeat (1, 2) 50438 ++ (27674, 2) :: (1, 1) :: repeat (1, 2) 323288 ++ w) 1); closearith.
  }
  (* step 323: P TUP2_1 *)
  apply (hsteps_trans _ (HC [6030; 630; 191; 113; 33; 19; 0] 11796 1 2 ((8217, 2) :: (1, 1) :: repeat (1, 2) 50438 ++ (27674, 2) :: (1, 1) :: repeat (1, 2) 323288 ++ w) 1)).
  {
    replace ((8217, 2) :: (1, 1) :: repeat (1, 2) 50438 ++ (27674, 2) :: (1, 1) :: repeat (1, 2) 323288 ++ w) with ((8219 - 2, 2) :: (1, 1) :: repeat (1, 2) 50438 ++ (27674, 2) :: (1, 1) :: repeat (1, 2) 323288 ++ w) by sec_eq.
    apply (sTUP2_1 [630; 191; 113; 33; 19; 0] 6029 11795 8219 ((1, 1) :: repeat (1, 2) 50438 ++ (27674, 2) :: (1, 1) :: repeat (1, 2) 323288 ++ w) 1); closearith.
  }
  (* step 324: P TDN *)
  apply (hsteps_trans _ (HB [6030; 630; 191; 113; 33; 19; 0] 11796 1 4 ((8217, 2) :: (1, 1) :: repeat (1, 2) 50438 ++ (27674, 2) :: (1, 1) :: repeat (1, 2) 323288 ++ w) 1)).
  {
    apply (sTDN [6030; 630; 191; 113; 33; 19; 0] 11796 ((8217, 2) :: (1, 1) :: repeat (1, 2) 50438 ++ (27674, 2) :: (1, 1) :: repeat (1, 2) 323288 ++ w) 1).
  }
  (* step 325: sTUP *)
  apply (hsteps_trans _ (HC [6030; 630; 191; 113; 33; 19; 0] 11796 3 2 ((8215, 2) :: (1, 1) :: repeat (1, 2) 50438 ++ (27674, 2) :: (1, 1) :: repeat (1, 2) 323288 ++ w) 1)).
  {
    replace ((8215, 2) :: (1, 1) :: repeat (1, 2) 50438 ++ (27674, 2) :: (1, 1) :: repeat (1, 2) 323288 ++ w) with ((8217 - 2, 2) :: (1, 1) :: repeat (1, 2) 50438 ++ (27674, 2) :: (1, 1) :: repeat (1, 2) 323288 ++ w) by sec_eq.
    apply (sTUP [6030; 630; 191; 113; 33; 19; 0] 11796 4 8217 2 ((1, 1) :: repeat (1, 2) 50438 ++ (27674, 2) :: (1, 1) :: repeat (1, 2) 323288 ++ w) 1); closearith.
  }
  (* step 326: CLEANG_odd 4106 *)
  apply (hsteps_trans _ (HB [6030; 630; 191; 113; 33; 19; 0] 11796 1 8220 (repeat (1, 2) 1 ++ (1, 1) :: repeat (1, 2) 50438 ++ (27674, 2) :: (1, 1) :: repeat (1, 2) 323288 ++ w) 1)).
  {
    replace (repeat (1, 2) 1 ++ (1, 1) :: repeat (1, 2) 50438 ++ (27674, 2) :: (1, 1) :: repeat (1, 2) 323288 ++ w) with ((1, 2) :: (1, 1) :: repeat (1, 2) 50438 ++ (27674, 2) :: (1, 1) :: repeat (1, 2) 323288 ++ w) by sec_eq.
    apply (CLEANG_odd 4106 [6030; 630; 191; 113; 33; 19; 0] 11796 ((1, 1) :: repeat (1, 2) 50438 ++ (27674, 2) :: (1, 1) :: repeat (1, 2) 323288 ++ w) 1); closearith.
  }
  (* step 327: M pop12 (1,) *)
  apply (hsteps_trans _ (HB [6030; 630; 191; 113; 33; 19; 0] 11797 1 8222 ((1, 1) :: repeat (1, 2) 50438 ++ (27674, 2) :: (1, 1) :: repeat (1, 2) 323288 ++ w) 1)).
  {
    apply (pop12 1 [6030; 630; 191; 113; 33; 19; 0] 11796 8220 ((1, 1) :: repeat (1, 2) 50438 ++ (27674, 2) :: (1, 1) :: repeat (1, 2) 323288 ++ w) 1); closearith.
  }
  (* step 328: P POP *)
  apply (hsteps_trans _ (HB [6030; 630; 191; 113; 33; 19; 0] 11798 1 8223 (repeat (1, 2) 50438 ++ (27674, 2) :: (1, 1) :: repeat (1, 2) 323288 ++ w) 1)).
  {
    apply (sPOP1 [6030; 630; 191; 113; 33; 19; 0] 11797 8222 (repeat (1, 2) 50438 ++ (27674, 2) :: (1, 1) :: repeat (1, 2) 323288 ++ w) 1); closearith.
  }
  (* step 329: M pop12 (50438,) *)
  apply (hsteps_trans _ (HB [6030; 630; 191; 113; 33; 19; 0] 62236 1 109099 ((27674, 2) :: (1, 1) :: repeat (1, 2) 323288 ++ w) 1)).
  {
    apply (pop12 50438 [6030; 630; 191; 113; 33; 19; 0] 11798 8223 ((27674, 2) :: (1, 1) :: repeat (1, 2) 323288 ++ w) 1); closearith.
  }
  (* step 330: sTUP *)
  apply (hsteps_trans _ (HC [6030; 630; 191; 113; 33; 19; 0] 62236 109098 2 ((27672, 2) :: (1, 1) :: repeat (1, 2) 323288 ++ w) 1)).
  {
    replace ((27672, 2) :: (1, 1) :: repeat (1, 2) 323288 ++ w) with ((27674 - 2, 2) :: (1, 1) :: repeat (1, 2) 323288 ++ w) by sec_eq.
    apply (sTUP [6030; 630; 191; 113; 33; 19; 0] 62236 109099 27674 2 ((1, 1) :: repeat (1, 2) 323288 ++ w) 1); closearith.
  }
  (* step 331: hGRIND_even 54547 *)
  apply (hsteps_trans _ (HB [6030; 630; 191; 113; 33; 19; 0] 62235 1 109098 ((2, 2) :: (27672, 2) :: (1, 1) :: repeat (1, 2) 323288 ++ w) 1)).
  {
    apply (hGRIND_even 54547 [6030; 630; 191; 113; 33; 19; 0] 62235 ((27672, 2) :: (1, 1) :: repeat (1, 2) 323288 ++ w) 1); closearith.
  }
  (* step 332: P TUP2_1 *)
  apply (hsteps_trans _ (HC [62236; 6030; 630; 191; 113; 33; 19; 0] 109098 1 2 ((27670, 2) :: (1, 1) :: repeat (1, 2) 323288 ++ w) 1)).
  {
    replace ((27670, 2) :: (1, 1) :: repeat (1, 2) 323288 ++ w) with ((27672 - 2, 2) :: (1, 1) :: repeat (1, 2) 323288 ++ w) by sec_eq.
    apply (sTUP2_1 [6030; 630; 191; 113; 33; 19; 0] 62235 109097 27672 ((1, 1) :: repeat (1, 2) 323288 ++ w) 1); closearith.
  }
  (* step 333: P TDN *)
  apply (hsteps_trans _ (HB [62236; 6030; 630; 191; 113; 33; 19; 0] 109098 1 4 ((27670, 2) :: (1, 1) :: repeat (1, 2) 323288 ++ w) 1)).
  {
    apply (sTDN [62236; 6030; 630; 191; 113; 33; 19; 0] 109098 ((27670, 2) :: (1, 1) :: repeat (1, 2) 323288 ++ w) 1).
  }
  (* step 334: sTUP *)
  apply (hsteps_trans _ (HC [62236; 6030; 630; 191; 113; 33; 19; 0] 109098 3 2 ((27668, 2) :: (1, 1) :: repeat (1, 2) 323288 ++ w) 1)).
  {
    replace ((27668, 2) :: (1, 1) :: repeat (1, 2) 323288 ++ w) with ((27670 - 2, 2) :: (1, 1) :: repeat (1, 2) 323288 ++ w) by sec_eq.
    apply (sTUP [62236; 6030; 630; 191; 113; 33; 19; 0] 109098 4 27670 2 ((1, 1) :: repeat (1, 2) 323288 ++ w) 1); closearith.
  }
  (* step 335: CLEANG_even 13833 *)
  apply (hsteps_trans _ (HB [62236; 6030; 630; 191; 113; 33; 19; 0] 109098 1 27672 ((2, 2) :: (1, 1) :: repeat (1, 2) 323288 ++ w) 1)).
  {
    apply (CLEANG_even 13833 [62236; 6030; 630; 191; 113; 33; 19; 0] 109098 ((1, 1) :: repeat (1, 2) 323288 ++ w) 1); closearith.
  }
  (* step 336: P TRANS2_1 *)
  apply (sTRANS2_1 [62236; 6030; 630; 191; 113; 33; 19; 0] 109098 27671 1 (repeat (1, 2) 323288 ++ w) 1); closearith.
Qed.

(* CASCADE53g: steps 337-337 of the CASCADE53 chain. *)
Lemma CASCADE53g : forall w,
  hsteps (HB [109099; 62236; 6030; 630; 191; 113; 33; 19; 0] 27673 1 3 (repeat (1, 2) 323288 ++ w) 1)
         (HB [109099; 62236; 6030; 630; 191; 113; 33; 19; 0] 350961 1 646579 (w) 1).
Proof.
  intro w.
  replace 350961 with (27673 + 323288)
    by (apply Nat.eqb_eq; vm_compute; reflexivity).
  replace 646579 with (3 + 2 * 323288)
    by (apply Nat.eqb_eq; vm_compute; reflexivity).
  (* step 337: M pop12 (323288,) *)
  apply (pop12 323288 [109099; 62236; 6030; 630; 191; 113; 33; 19; 0] 27673 3 (w) 1); closearith.
Qed.

Lemma CASCADE53 : forall w,
  hsteps (HC [175058; 23252; 3931; 2847; 569; 287; 14; 5] 0 3 2 (repeat (1, 2) 323286 ++ w) 1)
         (HB [109099; 62236; 6030; 630; 191; 113; 33; 19; 0] 350961 1 646579 (w) 1).
Proof.
  intro w.
  apply (hsteps_trans _ (HB [5] 48 1 74 ((2, 2) :: (185, 2) :: (1, 1) :: repeat (1, 2) 569 ++ (24959, 2) :: (1, 1) :: repeat (1, 2) 50438 ++ (27674, 2) :: (1, 1) :: repeat (1, 2) 323288 ++ w) 1)).
  { apply (CASCADE53a w). }
  apply (hsteps_trans _ (HB [0] 3 1 4 ((14, 2) :: (1, 1) :: repeat (1, 2) 112 ++ (503, 2) :: (1, 1) :: repeat (1, 2) 1174 ++ (22609, 2) :: (1, 1) :: repeat (1, 2) 50438 ++ (27674, 2) :: (1, 1) :: repeat (1, 2) 323288 ++ w) 1)).
  { apply (CASCADE53b w). }
  apply (hsteps_trans _ (HC [5] 49 74 2 ((15, 2) :: (1, 1) :: repeat (1, 2) 228 ++ (45, 2) :: (1, 1) :: repeat (1, 2) 1174 ++ (22609, 2) :: (1, 1) :: repeat (1, 2) 50438 ++ (27674, 2) :: (1, 1) :: repeat (1, 2) 323288 ++ w) 1)).
  { apply (CASCADE53c w). }
  apply (hsteps_trans _ (HB [20; 0] 36 1 7 (repeat (1, 2) 304 ++ (1040, 2) :: (1, 1) :: repeat (1, 2) 2396 ++ (17815, 2) :: (1, 1) :: repeat (1, 2) 50438 ++ (27674, 2) :: (1, 1) :: repeat (1, 2) 323288 ++ w) 1)).
  { apply (CASCADE53d w). }
  apply (hsteps_trans _ (HB [14; 5] 50 1 93 ((206, 2) :: (1, 1) :: repeat (1, 2) 615 ++ (2203, 2) :: (1, 1) :: repeat (1, 2) 4796 ++ (8221, 2) :: (1, 1) :: repeat (1, 2) 50438 ++ (27674, 2) :: (1, 1) :: repeat (1, 2) 323288 ++ w) 1)).
  { apply (CASCADE53e w). }
  apply (hsteps_trans _ (HB [109099; 62236; 6030; 630; 191; 113; 33; 19; 0] 27673 1 3 (repeat (1, 2) 323288 ++ w) 1)).
  { apply (CASCADE53f w). }
  apply (CASCADE53g w).
Qed.

(* ----------------------------------------------------------------- *)
(* TOP53_TO_TOP7: TOP6's front (TUP + hGRIND_even 161641 +         *)
(* TUP2_1 + TDN + TUP) reaches GRIND7, DIPGRIND (323286,            *)
(* 2 * (j - 323289)) lands on the DIP7 spine, and CASCADE53        *)
(* regrows the stack onto TOP7.  Numeral hygiene (Phase 52          *)
(* lesson, applied proactively at this phase's doubled scale):     *)
(* the 323289/323290 atoms are normalised onto the single atom      *)
(* 323286 by eqb/vm-proved rewrites, not `change` (the              *)
(* S/subtraction conversions at depth ~323290 overflow the          *)
(* conversion stack, cf. the TAIL2_END6_of52 fix-up in              *)
(* Grind20.v); the hGRIND_even step rewrites the goal by the        *)
(* standalone identities NUM53a / NUM53b (identical numerals to     *)
(* TOP52_4/6/BAND: 323286 = 2 * 161641 + 4, 175058 = S 175057).      *)
(* ----------------------------------------------------------------- *)

Lemma TOP53_TO_TOP7 : forall j beta, 323290 <= j -> 2 <= beta ->
  hsteps (HB [23252; 3931; 2847; 569; 287; 14; 5] 175058 1 323287
            ((2 * j, 2) :: (1, 1) :: repeat (1, 2) (beta - 1)) 1)
         (HB [109099; 62236; 6030; 630; 191; 113; 33; 19; 0] 350961 1 646579
            ((2 * (j - 323289), 2) :: (1, 1)
             :: repeat (1, 2) (beta - 1)) 1).
Proof.
  intros j beta Hj Hb.
  assert (Hj4 : 4 <= j).
  { apply Nat.le_trans with 323290; [closearith | exact Hj]. }
  assert (Hr : 1 <= j - 323289).
  { assert (E : 323289 = 323290 - 1)
      by (apply Nat.eqb_eq; vm_compute; reflexivity).
    rewrite E. lia. }
  assert (Heq : 2 * j - 6 = 2 * 323286 + 2 * (j - 323289)).
  { assert (E1 : 323289 = 323286 + 3)
      by (apply Nat.eqb_eq; vm_compute; reflexivity).
    assert (E2 : 323290 = 323286 + 4)
      by (apply Nat.eqb_eq; vm_compute; reflexivity).
    rewrite E1. rewrite E2 in Hj. lia. }
  apply (hsteps_trans _ (HC [23252; 3931; 2847; 569; 287; 14; 5] 175058
    323286 2 ((2 * j - 2, 2) :: (1, 1) :: repeat (1, 2) (beta - 1)) 1)).
  { apply (sTUP [23252; 3931; 2847; 569; 287; 14; 5] 175058 323287 (2 * j) 2
           ((1, 1) :: repeat (1, 2) (beta - 1)) 1); closearith. }
  apply (hsteps_trans _ (HB [23252; 3931; 2847; 569; 287; 14; 5] 175057
    1 323286 ((2, 2) :: (2 * j - 2, 2) :: (1, 1)
            :: repeat (1, 2) (beta - 1)) 1)).
  { rewrite NUM53a. rewrite NUM53b.
    apply (hGRIND_even 161641 [23252; 3931; 2847; 569; 287; 14; 5]
           175057 ((2 * j - 2, 2) :: (1, 1) :: repeat (1, 2) (beta - 1))
           1); closearith. }
  apply (hsteps_trans _ (HC [175058; 23252; 3931; 2847; 569; 287;
    14; 5] 323286 1 2 ((2 * j - 4, 2) :: (1, 1)
            :: repeat (1, 2) (beta - 1)) 1)).
  { replace ((2 * j - 4, 2) :: (1, 1) :: repeat (1, 2) (beta - 1))
      with ((2 * j - 2 - 2, 2) :: (1, 1) :: repeat (1, 2) (beta - 1))
      by sec_eq.
    apply (sTUP2_1 [23252; 3931; 2847; 569; 287; 14; 5] 175057
           323285 (2 * j - 2) ((1, 1) :: repeat (1, 2) (beta - 1)) 1); lia. }
  apply (hsteps_trans _ (HB [175058; 23252; 3931; 2847; 569; 287;
    14; 5] 323286 1 4 ((2 * j - 4, 2) :: (1, 1)
            :: repeat (1, 2) (beta - 1)) 1)).
  { apply (sTDN [175058; 23252; 3931; 2847; 569; 287; 14; 5] 323286
           ((2 * j - 4, 2) :: (1, 1) :: repeat (1, 2) (beta - 1))
           1). }
  apply (hsteps_trans _ (HC [175058; 23252; 3931; 2847; 569; 287;
    14; 5] 323286 3 2 ((2 * j - 6, 2) :: (1, 1)
            :: repeat (1, 2) (beta - 1)) 1)).
  { replace ((2 * j - 6, 2) :: (1, 1) :: repeat (1, 2) (beta - 1))
      with ((2 * j - 4 - 2, 2) :: (1, 1) :: repeat (1, 2) (beta - 1))
      by sec_eq.
    apply (sTUP [175058; 23252; 3931; 2847; 569; 287; 14; 5] 323286 4
           (2 * j - 4) 2 ((1, 1) :: repeat (1, 2) (beta - 1)) 1);
      lia. }
  apply (hsteps_trans _ (HC [175058; 23252; 3931; 2847; 569; 287;
    14; 5]
    0 3 2 (repeat (1, 2) 323286
     ++ ((2 * (j - 323289), 2) :: (1, 1)
         :: repeat (1, 2) (beta - 1))) 1)).
  { rewrite Heq.
    apply (DIPGRIND 323286 (2 * (j - 323289))
           [175058; 23252; 3931; 2847; 569; 287; 14; 5]
           ((1, 1) :: repeat (1, 2) (beta - 1)) 1);
      [closearith | lia]. }
  apply (CASCADE53 ((2 * (j - 323289), 2) :: (1, 1)
                    :: repeat (1, 2) (beta - 1))).
Qed.

(* ----------------------------------------------------------------- *)
(* The TOP7 closings: r7 = 2, 4, 6 and band 7 (8 <= r7 <= 1293162). *)
(* ----------------------------------------------------------------- *)

Lemma TOP53_2 : forall beta, 2 <= beta ->
  hsteps (HB [109099; 62236; 6030; 630; 191; 113; 33; 19; 0] 350961 1 646579
            ((2, 2) :: (1, 1) :: repeat (1, 2) (beta - 1)) 1)
         (HB [350962; 109099; 62236; 6030; 630; 191; 113; 33; 19; 0]
            (646580 + (beta - 1)) 1 (2 * beta + 1) [] 1).
Proof.
  intros beta Hb.
  apply (hsteps_trans _ (HB [350962; 109099; 62236; 6030; 630; 191;
    113; 33; 19; 0] 646580 1 3 (repeat (1, 2) (beta - 1)) 1)).
  { rewrite NUM53e. rewrite NUM53f. rewrite NUM53g.
    apply (sTRANS2_1 [109099; 62236; 6030; 630; 191; 113; 33; 19; 0] 350961
           646578 1 (repeat (1, 2) (beta - 1)) 1); lia. }
  apply (CASCADE_POPFIN [350962; 109099; 62236; 6030; 630; 191; 113;
         33; 19; 0] 646580 beta); lia.
Qed.

(* NOTE (Phase 53, proactive): in TOP53_4, TOP53_6 and TOP53_BAND  *)
(* the hGRIND_even 323287 step is preceded by two goal rewrites     *)
(* via the standalone identities NUM53c (646578 = 2 * 323287 + 4)   *)
(* and NUM53d (350961 = S 350960) -- the Phase 52 fix-up pattern     *)
(* for TOP52_4/6/BAND's hGRIND_even 161641 step, applied from the   *)
(* start at this phase's doubled scale, with the identities         *)
(* factored into lemmas because the inline `replace ... by          *)
(* (eqb/vm ...)` form stack-overflows in this file's long           *)
(* hsteps_trans chains (see the NUM53 note in the header).  The     *)
(* step applies themselves are unchanged.                           *)

Lemma TOP53_4 : forall beta, 2 <= beta ->
  hsteps (HB [109099; 62236; 6030; 630; 191; 113; 33; 19; 0] 350961 1 646579
            ((4, 2) :: (1, 1) :: repeat (1, 2) (beta - 1)) 1)
         (HB [646579; 350961; 109099; 62236; 6030; 630; 191; 113; 33; 19; 0]
            (beta + 2) 1 (2 * beta + 1) [] 1).
Proof.
  intros beta Hb.
  apply (hsteps_trans _ (HC [109099; 62236; 6030; 630; 191; 113; 33; 19; 0]
    350961 646578 2
    ((2, 2) :: (1, 1) :: repeat (1, 2) (beta - 1)) 1)).
  { rewrite NUM53h.
    apply (sTUP [109099; 62236; 6030; 630; 191; 113; 33; 19; 0] 350961 646579
           4 2 ((1, 1) :: repeat (1, 2) (beta - 1)) 1); closearith. }
  apply (hsteps_trans _ (HB [109099; 62236; 6030; 630; 191; 113; 33; 19; 0]
    350960 1 646578 ((2, 2) :: (2, 2) :: (1, 1)
            :: repeat (1, 2) (beta - 1)) 1)).
  { rewrite NUM53c. rewrite NUM53d.
    apply (hGRIND_even 323287 [109099; 62236; 6030; 630; 191; 113; 33; 19; 0]
           350960 ((2, 2) :: (1, 1) :: repeat (1, 2) (beta - 1)) 1);
      closearith. }
  apply (hsteps_trans _ (HB [646579; 350961; 109099; 62236; 6030;
    630; 191; 113; 33; 19; 0] 3 1 3 (repeat (1, 2) (beta - 1)) 1)).
  { rewrite NUM53k. rewrite NUM53m. rewrite NUM53d.
    apply (hsteps_step _ (HB [646579; 350961; 109099; 62236; 6030;
      630; 191; 113; 33; 19; 0] 3 1 3 (repeat (1, 2) (beta - 1)) 1));
      [apply hTRANS2_2; closearith | apply hsteps_refl]. }
  replace (beta + 2) with (3 + (beta - 1)) by lia.
  apply (CASCADE_POPFIN [646579; 350961; 109099; 62236; 6030; 630;
         191; 113; 33; 19; 0] 3 beta); lia.
Qed.

Lemma TOP53_6 : forall beta, 2 <= beta ->
  hsteps (HB [109099; 62236; 6030; 630; 191; 113; 33; 19; 0] 350961 1 646579
            ((6, 2) :: (1, 1) :: repeat (1, 2) (beta - 1)) 1)
         (HB [646579; 350961; 109099; 62236; 6030; 630; 191; 113; 33; 19; 0]
            (beta + 4) 1 (2 * beta + 1) [] 1).
Proof.
  intros beta Hb.
  apply (hsteps_trans _ (HC [109099; 62236; 6030; 630; 191; 113; 33; 19; 0]
    350961 646578 2
    ((4, 2) :: (1, 1) :: repeat (1, 2) (beta - 1)) 1)).
  { rewrite NUM53h.
    apply (sTUP [109099; 62236; 6030; 630; 191; 113; 33; 19; 0] 350961 646579
           6 2 ((1, 1) :: repeat (1, 2) (beta - 1)) 1); closearith. }
  apply (hsteps_trans _ (HB [109099; 62236; 6030; 630; 191; 113; 33; 19; 0]
    350960 1 646578 ((2, 2) :: (4, 2) :: (1, 1)
            :: repeat (1, 2) (beta - 1)) 1)).
  { rewrite NUM53c. rewrite NUM53d.
    apply (hGRIND_even 323287 [109099; 62236; 6030; 630; 191; 113; 33; 19; 0]
           350960 ((4, 2) :: (1, 1) :: repeat (1, 2) (beta - 1)) 1);
      closearith. }
  apply (hsteps_trans _ (HC [350961; 109099; 62236; 6030; 630; 191;
    113; 33; 19; 0] 646578 1 2
    ((2, 2) :: (1, 1) :: repeat (1, 2) (beta - 1)) 1)).
  { rewrite NUM53k. rewrite NUM53d.
    replace ((2, 2) :: (1, 1) :: repeat (1, 2) (beta - 1))
      with ((4 - 2, 2) :: (1, 1) :: repeat (1, 2) (beta - 1))
      by sec_eq.
    apply (sTUP2_1 [109099; 62236; 6030; 630; 191; 113; 33; 19; 0] 350960
           646577 4 ((1, 1) :: repeat (1, 2) (beta - 1)) 1); lia. }
  apply (hsteps_trans _ (HB [350961; 109099; 62236; 6030; 630; 191;
    113; 33; 19; 0] 646578 1 4
    ((2, 2) :: (1, 1) :: repeat (1, 2) (beta - 1)) 1)).
  { apply (sTDN [350961; 109099; 62236; 6030; 630; 191; 113; 33; 19; 0] 646578
           ((2, 2) :: (1, 1) :: repeat (1, 2) (beta - 1)) 1). }
  apply (hsteps_trans _ (HB [646579; 350961; 109099; 62236; 6030;
    630; 191; 113; 33; 19; 0] 5 1 3 (repeat (1, 2) (beta - 1)) 1)).
  { rewrite NUM53e.
    apply (sTRANS2_1 [350961; 109099; 62236; 6030; 630; 191; 113;
           33; 19; 0]
           646578 3 1 (repeat (1, 2) (beta - 1)) 1); lia. }
  replace (beta + 4) with (5 + (beta - 1)) by lia.
  apply (CASCADE_POPFIN [646579; 350961; 109099; 62236; 6030; 630;
         191; 113; 33; 19; 0] 5 beta); lia.
Qed.

Lemma TOP53_BAND : forall j beta, 4 <= j -> j <= 646581 -> 2 <= beta ->
  hsteps (HB [109099; 62236; 6030; 630; 191; 113; 33; 19; 0] 350961 1 646579
            ((2 * j, 2) :: (1, 1) :: repeat (1, 2) (beta - 1)) 1)
         (HB [646579; 350961; 109099; 62236; 6030; 630; 191; 113; 33; 19; 0]
            (2 * j + beta - 2) 1 (2 * beta + 1) [] 1).
Proof.
  intros j beta Hj1 Hj2 Hb.
  apply (hsteps_trans _ (HC [109099; 62236; 6030; 630; 191; 113; 33; 19; 0]
    350961 646578 2 ((2 * j - 2, 2) :: (1, 1)
            :: repeat (1, 2) (beta - 1)) 1)).
  { rewrite NUM53h.
    apply (sTUP [109099; 62236; 6030; 630; 191; 113; 33; 19; 0] 350961 646579
           (2 * j) 2 ((1, 1) :: repeat (1, 2) (beta - 1)) 1);
      closearith. }
  apply (hsteps_trans _ (HB [109099; 62236; 6030; 630; 191; 113; 33; 19; 0]
    350960 1 646578 ((2, 2) :: (2 * j - 2, 2) :: (1, 1)
            :: repeat (1, 2) (beta - 1)) 1)).
  { rewrite NUM53c. rewrite NUM53d.
    apply (hGRIND_even 323287 [109099; 62236; 6030; 630; 191; 113; 33; 19; 0]
           350960 ((2 * j - 2, 2) :: (1, 1)
           :: repeat (1, 2) (beta - 1)) 1); closearith. }
  apply (hsteps_trans _ (HC [350961; 109099; 62236; 6030; 630; 191;
    113; 33; 19; 0] 646578 1 2 ((2 * j - 4, 2) :: (1, 1)
            :: repeat (1, 2) (beta - 1)) 1)).
  { rewrite NUM53k. rewrite NUM53d.
    replace ((2 * j - 4, 2) :: (1, 1) :: repeat (1, 2) (beta - 1))
      with ((2 * j - 2 - 2, 2) :: (1, 1)
            :: repeat (1, 2) (beta - 1)) by sec_eq.
    apply (sTUP2_1 [109099; 62236; 6030; 630; 191; 113; 33; 19; 0] 350960
           646577 (2 * j - 2) ((1, 1) :: repeat (1, 2) (beta - 1))
           1); lia. }
  apply (hsteps_trans _ (HB [350961; 109099; 62236; 6030; 630; 191;
    113; 33; 19; 0] 646578 1 4 ((2 * j - 4, 2) :: (1, 1)
            :: repeat (1, 2) (beta - 1)) 1)).
  { apply (sTDN [350961; 109099; 62236; 6030; 630; 191; 113; 33; 19; 0] 646578
           ((2 * j - 4, 2) :: (1, 1) :: repeat (1, 2) (beta - 1))
           1). }
  apply (hsteps_trans _ (HC [350961; 109099; 62236; 6030; 630; 191;
    113; 33; 19; 0] 646578 3 2 ((2 * j - 6, 2) :: (1, 1)
            :: repeat (1, 2) (beta - 1)) 1)).
  { replace ((2 * j - 6, 2) :: (1, 1) :: repeat (1, 2) (beta - 1))
      with ((2 * j - 4 - 2, 2) :: (1, 1)
            :: repeat (1, 2) (beta - 1)) by sec_eq.
    apply (sTUP [350961; 109099; 62236; 6030; 630; 191; 113; 33; 19; 0] 646578
           4 (2 * j - 4) 2 ((1, 1) :: repeat (1, 2) (beta - 1)) 1);
      lia. }
  apply (hsteps_trans _ (HB [350961; 109099; 62236; 6030; 630; 191;
    113; 33; 19; 0] 646578 1 (2 * j - 2)
    ((2, 2) :: (1, 1) :: repeat (1, 2) (beta - 1)) 1)).
  { replace (2 * j - 6) with (2 * (j - 4) + 2) by lia.
    replace (2 * j - 2) with (2 * (j - 4) + 6) by lia.
    apply (CLEANG_even (j - 4) [350961; 109099; 62236; 6030; 630; 191;
           113; 33; 19; 0] 646578 ((1, 1) :: repeat (1, 2) (beta - 1))
           1).
    (* the floor (j - 4) + 1 <= 646578: route via j <= 646581 *)
    apply Nat.le_trans with (j - 3).
    - lia.
    - rewrite NUM53r.
      apply Nat.sub_le_mono_r. exact Hj2. }
  apply (hsteps_trans _ (HB [646579; 350961; 109099; 62236; 6030;
    630; 191; 113; 33; 19; 0] (2 * j - 1) 1 3 (repeat (1, 2) (beta - 1)) 1)).
  { replace (2 * j - 2) with (S (2 * j - 3)) by lia.
    replace (2 * j - 1) with (S (S (2 * j - 3))) by lia.
    rewrite NUM53e.
    apply (sTRANS2_1 [350961; 109099; 62236; 6030; 630; 191; 113;
           33; 19; 0]
           646578 (2 * j - 3) 1 (repeat (1, 2) (beta - 1)) 1); lia. }
  replace (2 * j + beta - 2) with (2 * j - 1 + (beta - 1)) by lia.
  apply (CASCADE_POPFIN [646579; 350961; 109099; 62236; 6030; 630;
         191; 113; 33; 19; 0] (2 * j - 1) beta); lia.
Qed.

(* ----------------------------------------------------------------- *)
(* TAIL2_END8: the strictly smaller residual core -- the totality   *)
(* of the TOP7 state for r7 = 2 * j, j >= 646582 (r7 >= 1293164),   *)
(* where the GRIND8 pair (r7 - 6, 2) at counter 646578 takes the    *)
(* DIPDESC boundary an eighth time.  A Definition (lemma            *)
(* parameter), never an axiom.                                      *)
(* ----------------------------------------------------------------- *)

Definition TAIL2_END8 : Prop :=
  forall j beta, 646582 <= j -> 2 <= beta ->
  exists pb A, beta <= A /\
    hsteps (HB [109099; 62236; 6030; 630; 191; 113; 33; 19; 0] 350961 1 646579
              ((2 * j, 2) :: (1, 1) :: repeat (1, 2) (beta - 1)) 1)
           (HB pb A 1 (2 * beta + 1) [] 1).

(* ----------------------------------------------------------------- *)
(* TAIL2_END7_of53: TAIL2_END7, modulo TAIL2_END8.  The j-range     *)
(* splits at r7 = 2 * (j - 323289): the three small cases and       *)
(* band 7 are proved above; j - 323289 >= 646582 is the core.       *)
(* (Numeral hygiene: the `change N with (S (N-1))` steps of the     *)
(* Phase 52 analogue at N = 323290 / 323288 are here at             *)
(* N = 646582 / 646580 / 323290 -- all replaced by eqb/vm-proved    *)
(* equality rewrites, since the S-conversions at these depths       *)
(* overflow the conversion stack.)                                  *)
(* ----------------------------------------------------------------- *)

Lemma TAIL2_END7_of53 : TAIL2_END8 -> TAIL2_END7.
Proof.
  intros H8 j beta Hj Hb.
  pose proof (TOP53_TO_TOP7 j beta Hj Hb) as Htop.
  destruct (le_lt_dec 646582 (j - 323289)) as [Hbig | Hsmall].
  - (* j7 = j - 323289 >= 646582: the core *)
    destruct (H8 (j - 323289) beta Hbig Hb)
      as [pb [A [Ha Hsteps]]].
    exists pb, A. split; [exact Ha |].
    exact (hsteps_trans _ _ _ Htop Hsteps).
  - destruct (le_lt_dec 4 (j - 323289)) as [Hband | Htiny].
    + (* band 7: j7 = j - 323289, 4 <= j7 <= 646581 *)
      exists [646579; 350961; 109099; 62236; 6030; 630; 191; 113; 33; 19; 0],
        (2 * (j - 323289) + beta - 2).
      split; [lia |].
      assert (Hj2 : j - 323289 <= 646581).
      { rewrite NUM53q in Hsmall.
        apply (proj1 (Nat.lt_succ_r _ _) Hsmall). }
      exact (hsteps_trans _ _ _ Htop
               (TOP53_BAND (j - 323289) beta Hband Hj2 Hb)).
    + (* tiny: j7 = j - 323289 <= 3; j7 >= 1 since 323290 <= j *)
      destruct (Nat.eq_dec (j - 323289) 1) as [He | Hne].
      * (* r7 = 2 *)
        rewrite He in Htop.
        exists [350962; 109099; 62236; 6030; 630; 191; 113; 33; 19; 0],
          (646580 + (beta - 1)).
        split; [rewrite NUM53n; lia |].
        exact (hsteps_trans _ _ _ Htop (TOP53_2 beta Hb)).
      * destruct (Nat.eq_dec (j - 323289) 2) as [He | Hne'].
        -- (* r7 = 4 *)
           rewrite He in Htop.
           exists [646579; 350961; 109099; 62236; 6030; 630; 191;
             113; 33; 19; 0], (beta + 2).
           split; [lia |].
           exact (hsteps_trans _ _ _ Htop (TOP53_4 beta Hb)).
        -- destruct (Nat.eq_dec (j - 323289) 3) as [He | Hne''].
           ++ (* r7 = 6 *)
              rewrite He in Htop.
              exists [646579; 350961; 109099; 62236; 6030; 630; 191;
                113; 33; 19; 0], (beta + 4).
              split; [lia |].
              exact (hsteps_trans _ _ _ Htop (TOP53_6 beta Hb)).
           ++ (* j7 = 0, contradicting 323290 <= j *)
              exfalso.
              assert (H0 : j - 323289 = 0) by lia.
              rewrite NUM53p in Hj.
              lia.
Qed.

(* ----------------------------------------------------------------- *)
(* ESC_ERA_LAW_53: the phase-8 ESC era law at every even            *)
(* R >= 1278, modulo TAIL2_END8 alone.                              *)
(* ----------------------------------------------------------------- *)

Lemma ESC_ERA_LAW_53 : TAIL2_END8 ->
  forall M beta, 616 <= M -> 2 <= beta ->
  exists n c pb a,
    run n (esc_src (2 * M + 52) (beta - 2)) = Some c
    /\ cfg_sim c (rcsec (false :: repeat true (S a) ++ enc pb)
                        (2 * beta + 2) [(1, 2)])
    /\ beta <= a.
Proof.
  intros H M beta HM Hb.
  apply (ESC_ERA_LAW_52 (TAIL2_END7_of53 H) M beta HM Hb).
Qed.

(* ----------------------------------------------------------------- *)
(* Assumption audit                                                  *)
(* ----------------------------------------------------------------- *)

Print Assumptions CASCADE53.
Print Assumptions TOP53_TO_TOP7.
Print Assumptions TOP53_2.
Print Assumptions TOP53_4.
Print Assumptions TOP53_6.
Print Assumptions TOP53_BAND.
Print Assumptions TAIL2_END7_of53.
Print Assumptions ESC_ERA_LAW_53.
