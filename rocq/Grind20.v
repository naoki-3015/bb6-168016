(* ================================================================= *)
(*  Grind20.v -- Phase 52: the sixth re-descent cascade of the      *)
(*  TOP5 state, mechanised as a fixed parse, closing TAIL2_END6     *)
(*  for the whole first j-band 134250 <= j <= 457538 (TOP5          *)
(*  parameters) and reducing the rest to a strictly smaller core    *)
(*  at the TOP6 state.                                              *)
(*                                                                  *)
(*  Phase 51 left the ESC side of H_LOOP resting on TAIL2_END6      *)
(*  (Grind19.v): the totality of the TOP5 state                     *)
(*                                                                  *)
(*    TOP5(j, beta) = HB [20403; 10332; 112; 20; 0] 95597           *)
(*                    1 134247 ((2j, 2) :: (1, 1) :: (1, 2)^(beta-1)) *)
(*                                                                  *)
(*  for j >= 134250.  There the GRIND6 pair (2j - 6, 2) at counter  *)
(*  134246 exceeds the CLEANG_even floor and takes the DIPDESC      *)
(*  boundary a sixth time.  Phase 52 traces the walk                *)
(*  (rocq/hsim52.py, ALL PASS: the 232-waypoint chain below          *)
(*  asserted verbatim at (j, beta) in {(134250, 2), (134250, 3),    *)
(*  (134251, 2), (200000, 2), (457538, 2)}; TOP6 finals and the     *)
(*  cycle-7 fence asserted too; a junk-tail probe confirms          *)
(*  CASCADE52 is stated for an arbitrary tail; the full             *)
(*  (134250, 2) walk was also replayed step by step through the     *)
(*  walker's own macro/prim functions and classified into 229       *)
(*  lemma applications with 0 unclassified runs, and the            *)
(*  CASCADE52 proof script below is generated from that             *)
(*  classification).                                                *)
(*                                                                  *)
(*  FINDING: the sixth descent is again a FIXED parse, uniform      *)
(*  in (j, beta) -- not a return to TOP5, TOP4, ..., or TOP.        *)
(*  Writing r6 = 2j - 268498 >= 2 for the DIPGRIND residue at       *)
(*  GRIND6:                                                         *)
(*                                                                  *)
(*    TOP5 --front (TUP, hGRIND_even 67121, TUP2_1, TDN, TUP)-->    *)
(*      GRIND6 = HC [95597; 20403; 10332; 112; 20; 0]               *)
(*                 134246 3 2 ((2j - 6, 2) :: tail)                 *)
(*    --DIPGRIND (134246, r6)-->                                    *)
(*      HC [95597; 20403; ...] 0 3 2 ((1, 2)^134246 ++ W),          *)
(*        W = ((r6, 2) :: (1, 1) :: (1, 2)^(beta - 1))              *)
(*    --CASCADE52 (fixed parse, arbitrary tail)-->                  *)
(*      TOP6 = HB [23252; 3931; 2847; 569; 287; 14; 5] 175058       *)
(*             1 323287 W.                                          *)
(*                                                                  *)
(*  CASCADE52 is a LONG parse (227 lemma steps from the spine:      *)
(*  52 TUP, 33 TDN, 30 pop12, 22 DIPGRIND levels, 18 TUP2_1,         *)
(*  14 hGRIND_even, 11 PUSH, 8 POP, 7 TRANS2_1, 4 CLEANG_even,       *)
(*  3 CLEANG_odd, 2 hGRIND, 23 raw h-steps) -- comparable to         *)
(*  CASCADE50, much longer than CASCADE51: it descends through      *)
(*  the empty frame (four PX2B0 + PUSHX bottom excursions) and      *)
(*  regrows a seven-block frame.  DIPGRIND sub-levels (A, r):       *)
(*  (20401, 54789), (110, 10106), (3, 6), (3, 2), (226, 9648),      *)
(*  (12, 87), (32, 17), (3, 5), (3, 2), (474, 8694), (47, 204),     *)
(*  (954, 6780), (101, 471), (3, 40), (3, 2), (13, 8), (208, 49),   *)
(*  (33, 38), (3, 6), (3, 2), (1962, 2850), (245, 884).  The        *)
(*  (20401, 54789) residue rides near the stack bottom through      *)
(*  the whole parse and is consumed by the final CLEANG_odd         *)
(*  27390; other clean exits: CLEANG_even 98, 15, 438, 1421 and     *)
(*  CLEANG_odd 4, 20.                                               *)
(*                                                                  *)
(*  TOP6 then closes by the size of r6 = 2 * j6 (j6 = j - 134249    *)
(*  in TOP6's own parameter):                                       *)
(*    r6 = 2:       TRANS2_1 + CASCADE_POPFIN, A = 323287 + beta;   *)
(*    r6 = 4:       TUP + hGRIND_even 161641 + TRANS2_2             *)
(*                    + CASCADE_POPFIN, A = beta + 2;               *)
(*    r6 = 6:       TUP + hGRIND_even 161641 + TUP2_1 + TDN         *)
(*                    + TRANS2_1 + CASCADE_POPFIN, A = beta + 4;    *)
(*    8 <= r6 <= 646578 (band 6): TUP + hGRIND_even 161641 + TUP2_1 *)
(*      + TDN + TUP onto GRIND7 = HC [175058; 23252; ...] 323286    *)
(*      3 2 ((r6 - 6, 2) :: tail), whose pair grinds CLEANLY by     *)
(*      CLEANG_even (floor (r6 - 8)/2 + 1 <= 323286, exactly         *)
(*      r6 <= 646578), then TRANS2_1 + CASCADE_POPFIN,              *)
(*      A = r6 + beta - 2, frame [323287; 175058; 23252; ...].      *)
(*      (The band counter is again the shuttle moved into the       *)
(*      counter slot by TUP2_1: 323286, not 175058.)                *)
(*                                                                  *)
(*  For r6 >= 646580 (j6 >= 323290, i.e. TOP5-parameter             *)
(*  j >= 457539) the pair (r6 - 6, 2) at counter 323286 exceeds     *)
(*  the CLEANG_even floor and the rounds take the DIPDESC           *)
(*  boundary a SEVENTH time (hsim52 Part 3: the GRIND7 state and    *)
(*  the DIPGRIND (323286, r6 - 646578) landing both occur at         *)
(*  j = 457539, 457540, 500000).  The seventh descent is expected   *)
(*  to be a NEW cascade with different constants, so no cycle       *)
(*  induction in the current vocabulary closes it; what remains     *)
(*  is the strictly smaller core                                    *)
(*                                                                  *)
(*    TAIL2_END7: the totality of the ONE pair (2j, 2) at the ONE   *)
(*    fixed TOP6 state HB [23252; 3931; 2847; 569; 287; 14; 5]      *)
(*    175058 1 323287, for j >= 323290 (r6 = 2j >= 646580),         *)
(*    beta >= 2.                                                    *)
(*                                                                  *)
(*  The core's range shrank from [134250, infty) to [457539, infty) *)
(*  in TOP5 parameters; the band width roughly doubled again        *)
(*  (134250 -> 457538).  Via TAIL2_END6_of52 + TAIL2_END5_of51 +    *)
(*  ESC_ERA_LAW_51 the ESC instances at every even R >= 1278 now    *)
(*  rest on TAIL2_END7 alone (ESC_ERA_LAW_52 below; Loop.v          *)
(*  Part 4m).                                                       *)
(* ================================================================= *)

Require Import List Bool Arith Lia ZArith.
Import ListNotations.
Require Import TM Sections Mirror TokenPass Recoord Era Esc Dev
               Grind Grind2 Grind3 Grind4 Grind5 Grind6 Grind7 Grind8
               Grind9 Grind10 Grind11 Grind12 Grind13 Grind14 Grind15
               Grind16 Grind17 Grind18 Grind19.

(* Section equality: componentwise, arithmetic leaves by lia.      *)
Ltac sec_eq :=
  repeat (first [ solve [reflexivity] | solve [lia] | f_equal ]).

(* Closed-numeral arithmetic: literals >= 7426 are parsed as       *)
(* Nat.of_num_uint atoms, which lia cannot relate to variables;    *)
(* for purely closed <= goals the boolean check decides them.      *)
Ltac closearith :=
  first [ lia | apply Nat.leb_le; reflexivity ].
(* ----------------------------------------------------------------- *)
(* CASCADE52: the DIP6 spine over frame [95597; 20403; 10332; 112;  *)
(* 20; 0] regrows onto TOP6, for an ARBITRARY tail w.  The proof    *)
(* is an hsteps_trans chain of 227 classified steps (waypoints      *)
(* asserted verbatim in hsim52.py); step kinds are annotated per    *)
(* step.  NOTE (Phase 52 fix-up): the flat 227-step chain in one    *)
(* lemma overflowed the Coq stack near its final steps, so the     *)
(* SAME step script is split into four consecutive sub-lemmas:     *)
(* CASCADE52a (steps 1-76), CASCADE52b (steps 77-152),             *)
(* CASCADE52c (steps 153-226) and CASCADE52d (step 227 alone);     *)
(* CASCADE52 below is their composition, its statement unchanged.  *)
(* Step 227 is isolated because its pop12 134248 landing forces    *)
(* the kernel conversions 40810 + 134248 = 175058 and              *)
(* 54791 + 2 * 134248 = 323287, whose unary depth overflows the    *)
(* conversion stack; CASCADE52d first rewrites the goal's          *)
(* numerals to pop12's computed form, the two equalities being     *)
(* discharged by Nat.eqb_eq + vm_compute (VM-cast conversion).     *)
(* No step script was otherwise altered.                           *)
(* ----------------------------------------------------------------- *)

(* CASCADE52a: steps 1-76 of the CASCADE52 chain. *)
Lemma CASCADE52a : forall w,
  hsteps (HC [95597; 20403; 10332; 112; 20; 0] 0 3 2
            (repeat (1, 2) 134246 ++ w) 1)
         (HB [49; 5] 76 1 19 (repeat (1, 2) 228 ++ (9648, 2) :: (1, 1) :: repeat (1, 2) 20403 ++ (54789, 2) :: (1, 1) :: repeat (1, 2) 134248 ++ w) 1).
Proof.
  intro w.
  (* step 1: P PX2A *)
  apply (hsteps_trans _ (HC [10332; 112; 20; 0] 20402 95595 2 ((1, 1) :: repeat (1, 2) 134248 ++ w) 1)).
  {
    apply (hsteps_step _ (HC [10332; 112; 20; 0] 20402 95595 2 ((1, 1) :: repeat (1, 2) 134248 ++ w) 1)); [apply hPX2A | apply hsteps_refl].
  }
  (* step 2: P PUSH *)
  apply (hsteps_trans _ (HC [10332; 112; 20; 0] 20401 1 2 ((95593, 2) :: (1, 1) :: repeat (1, 2) 134248 ++ w) 1)).
  {
    replace ((95593, 2) :: (1, 1) :: repeat (1, 2) 134248 ++ w) with ((95595 - 2, 2) :: (1, 1) :: repeat (1, 2) 134248 ++ w) by sec_eq.
    apply (sPUSH [10332; 112; 20; 0] 20401 95595 ((1, 1) :: repeat (1, 2) 134248 ++ w) 1); closearith.
  }
  (* step 3: P TDN *)
  apply (hsteps_trans _ (HB [10332; 112; 20; 0] 20401 1 4 ((95593, 2) :: (1, 1) :: repeat (1, 2) 134248 ++ w) 1)).
  {
    apply (sTDN [10332; 112; 20; 0] 20401 ((95593, 2) :: (1, 1) :: repeat (1, 2) 134248 ++ w) 1).
  }
  (* step 4: sTUP *)
  apply (hsteps_trans _ (HC [10332; 112; 20; 0] 20401 3 2 ((95591, 2) :: (1, 1) :: repeat (1, 2) 134248 ++ w) 1)).
  {
    replace ((95591, 2) :: (1, 1) :: repeat (1, 2) 134248 ++ w) with ((95593 - 2, 2) :: (1, 1) :: repeat (1, 2) 134248 ++ w) by sec_eq.
    apply (sTUP [10332; 112; 20; 0] 20401 4 95593 2 ((1, 1) :: repeat (1, 2) 134248 ++ w) 1); closearith.
  }
  (* step 5: DIPGRIND 20401 54789 *)
  apply (hsteps_trans _ (HC [10332; 112; 20; 0] 0 3 2 (repeat (1, 2) 20401 ++ (54789, 2) :: (1, 1) :: repeat (1, 2) 134248 ++ w) 1)).
  {
    apply (DIPGRIND 20401 54789 [10332; 112; 20; 0] ((1, 1) :: repeat (1, 2) 134248 ++ w) 1); closearith.
  }
  (* step 6: P PX2A *)
  apply (hsteps_trans _ (HC [20; 0] 111 10330 2 ((1, 1) :: repeat (1, 2) 20403 ++ (54789, 2) :: (1, 1) :: repeat (1, 2) 134248 ++ w) 1)).
  {
    apply (hsteps_step _ (HC [20; 0] 111 10330 2 ((1, 1) :: repeat (1, 2) 20403 ++ (54789, 2) :: (1, 1) :: repeat (1, 2) 134248 ++ w) 1)); [apply hPX2A | apply hsteps_refl].
  }
  (* step 7: P PUSH *)
  apply (hsteps_trans _ (HC [20; 0] 110 1 2 ((10328, 2) :: (1, 1) :: repeat (1, 2) 20403 ++ (54789, 2) :: (1, 1) :: repeat (1, 2) 134248 ++ w) 1)).
  {
    replace ((10328, 2) :: (1, 1) :: repeat (1, 2) 20403 ++ (54789, 2) :: (1, 1) :: repeat (1, 2) 134248 ++ w) with ((10330 - 2, 2) :: (1, 1) :: repeat (1, 2) 20403 ++ (54789, 2) :: (1, 1) :: repeat (1, 2) 134248 ++ w) by sec_eq.
    apply (sPUSH [20; 0] 110 10330 ((1, 1) :: repeat (1, 2) 20403 ++ (54789, 2) :: (1, 1) :: repeat (1, 2) 134248 ++ w) 1); closearith.
  }
  (* step 8: P TDN *)
  apply (hsteps_trans _ (HB [20; 0] 110 1 4 ((10328, 2) :: (1, 1) :: repeat (1, 2) 20403 ++ (54789, 2) :: (1, 1) :: repeat (1, 2) 134248 ++ w) 1)).
  {
    apply (sTDN [20; 0] 110 ((10328, 2) :: (1, 1) :: repeat (1, 2) 20403 ++ (54789, 2) :: (1, 1) :: repeat (1, 2) 134248 ++ w) 1).
  }
  (* step 9: sTUP *)
  apply (hsteps_trans _ (HC [20; 0] 110 3 2 ((10326, 2) :: (1, 1) :: repeat (1, 2) 20403 ++ (54789, 2) :: (1, 1) :: repeat (1, 2) 134248 ++ w) 1)).
  {
    replace ((10326, 2) :: (1, 1) :: repeat (1, 2) 20403 ++ (54789, 2) :: (1, 1) :: repeat (1, 2) 134248 ++ w) with ((10328 - 2, 2) :: (1, 1) :: repeat (1, 2) 20403 ++ (54789, 2) :: (1, 1) :: repeat (1, 2) 134248 ++ w) by sec_eq.
    apply (sTUP [20; 0] 110 4 10328 2 ((1, 1) :: repeat (1, 2) 20403 ++ (54789, 2) :: (1, 1) :: repeat (1, 2) 134248 ++ w) 1); closearith.
  }
  (* step 10: DIPGRIND 110 10106 *)
  apply (hsteps_trans _ (HC [20; 0] 0 3 2 (repeat (1, 2) 110 ++ (10106, 2) :: (1, 1) :: repeat (1, 2) 20403 ++ (54789, 2) :: (1, 1) :: repeat (1, 2) 134248 ++ w) 1)).
  {
    apply (DIPGRIND 110 10106 [20; 0] ((1, 1) :: repeat (1, 2) 20403 ++ (54789, 2) :: (1, 1) :: repeat (1, 2) 134248 ++ w) 1); closearith.
  }
  (* step 11: P PX2A0 *)
  apply (hsteps_trans _ (HB [0] 3 1 2 ((16, 2) :: (1, 1) :: repeat (1, 2) 112 ++ (10106, 2) :: (1, 1) :: repeat (1, 2) 20403 ++ (54789, 2) :: (1, 1) :: repeat (1, 2) 134248 ++ w) 1)).
  {
    apply (hsteps_step _ (HB [0] 3 1 2 ((16, 2) :: (1, 1) :: repeat (1, 2) 112 ++ (10106, 2) :: (1, 1) :: repeat (1, 2) 20403 ++ (54789, 2) :: (1, 1) :: repeat (1, 2) 134248 ++ w) 1)); [apply hPX2A0 | apply hsteps_refl].
  }
  (* step 12: sTUP *)
  apply (hsteps_trans _ (HC [0] 3 1 2 ((14, 2) :: (1, 1) :: repeat (1, 2) 112 ++ (10106, 2) :: (1, 1) :: repeat (1, 2) 20403 ++ (54789, 2) :: (1, 1) :: repeat (1, 2) 134248 ++ w) 1)).
  {
    replace ((14, 2) :: (1, 1) :: repeat (1, 2) 112 ++ (10106, 2) :: (1, 1) :: repeat (1, 2) 20403 ++ (54789, 2) :: (1, 1) :: repeat (1, 2) 134248 ++ w) with ((16 - 2, 2) :: (1, 1) :: repeat (1, 2) 112 ++ (10106, 2) :: (1, 1) :: repeat (1, 2) 20403 ++ (54789, 2) :: (1, 1) :: repeat (1, 2) 134248 ++ w) by sec_eq.
    apply (sTUP [0] 3 2 16 2 ((1, 1) :: repeat (1, 2) 112 ++ (10106, 2) :: (1, 1) :: repeat (1, 2) 20403 ++ (54789, 2) :: (1, 1) :: repeat (1, 2) 134248 ++ w) 1); closearith.
  }
  (* step 13: P TDN *)
  apply (hsteps_trans _ (HB [0] 3 1 4 ((14, 2) :: (1, 1) :: repeat (1, 2) 112 ++ (10106, 2) :: (1, 1) :: repeat (1, 2) 20403 ++ (54789, 2) :: (1, 1) :: repeat (1, 2) 134248 ++ w) 1)).
  {
    apply (sTDN [0] 3 ((14, 2) :: (1, 1) :: repeat (1, 2) 112 ++ (10106, 2) :: (1, 1) :: repeat (1, 2) 20403 ++ (54789, 2) :: (1, 1) :: repeat (1, 2) 134248 ++ w) 1).
  }
  (* step 14: sTUP *)
  apply (hsteps_trans _ (HC [0] 3 3 2 ((12, 2) :: (1, 1) :: repeat (1, 2) 112 ++ (10106, 2) :: (1, 1) :: repeat (1, 2) 20403 ++ (54789, 2) :: (1, 1) :: repeat (1, 2) 134248 ++ w) 1)).
  {
    replace ((12, 2) :: (1, 1) :: repeat (1, 2) 112 ++ (10106, 2) :: (1, 1) :: repeat (1, 2) 20403 ++ (54789, 2) :: (1, 1) :: repeat (1, 2) 134248 ++ w) with ((14 - 2, 2) :: (1, 1) :: repeat (1, 2) 112 ++ (10106, 2) :: (1, 1) :: repeat (1, 2) 20403 ++ (54789, 2) :: (1, 1) :: repeat (1, 2) 134248 ++ w) by sec_eq.
    apply (sTUP [0] 3 4 14 2 ((1, 1) :: repeat (1, 2) 112 ++ (10106, 2) :: (1, 1) :: repeat (1, 2) 20403 ++ (54789, 2) :: (1, 1) :: repeat (1, 2) 134248 ++ w) 1); closearith.
  }
  (* step 15: DIPGRIND 3 6 *)
  apply (hsteps_trans _ (HC [0] 0 3 2 (repeat (1, 2) 3 ++ (6, 2) :: (1, 1) :: repeat (1, 2) 112 ++ (10106, 2) :: (1, 1) :: repeat (1, 2) 20403 ++ (54789, 2) :: (1, 1) :: repeat (1, 2) 134248 ++ w) 1)).
  {
    apply (DIPGRIND 3 6 [0] ((1, 1) :: repeat (1, 2) 112 ++ (10106, 2) :: (1, 1) :: repeat (1, 2) 20403 ++ (54789, 2) :: (1, 1) :: repeat (1, 2) 134248 ++ w) 1); closearith.
  }
  (* step 16: P PX2B0 *)
  apply (hsteps_trans _ (HB [] 0 1 5 (repeat (1, 2) 4 ++ (6, 2) :: (1, 1) :: repeat (1, 2) 112 ++ (10106, 2) :: (1, 1) :: repeat (1, 2) 20403 ++ (54789, 2) :: (1, 1) :: repeat (1, 2) 134248 ++ w) 1)).
  {
    apply (hsteps_step _ (HB [] 0 1 5 (repeat (1, 2) 4 ++ (6, 2) :: (1, 1) :: repeat (1, 2) 112 ++ (10106, 2) :: (1, 1) :: repeat (1, 2) 20403 ++ (54789, 2) :: (1, 1) :: repeat (1, 2) 134248 ++ w) 1)); [apply hPX2B0 | apply hsteps_refl].
  }
  (* step 17: M pop12 (4,) *)
  apply (hsteps_trans _ (HB [] 4 1 13 ((6, 2) :: (1, 1) :: repeat (1, 2) 112 ++ (10106, 2) :: (1, 1) :: repeat (1, 2) 20403 ++ (54789, 2) :: (1, 1) :: repeat (1, 2) 134248 ++ w) 1)).
  {
    apply (pop12 4 [] 0 5 ((6, 2) :: (1, 1) :: repeat (1, 2) 112 ++ (10106, 2) :: (1, 1) :: repeat (1, 2) 20403 ++ (54789, 2) :: (1, 1) :: repeat (1, 2) 134248 ++ w) 1); closearith.
  }
  (* step 18: sTUP *)
  apply (hsteps_trans _ (HC [] 4 12 2 ((4, 2) :: (1, 1) :: repeat (1, 2) 112 ++ (10106, 2) :: (1, 1) :: repeat (1, 2) 20403 ++ (54789, 2) :: (1, 1) :: repeat (1, 2) 134248 ++ w) 1)).
  {
    replace ((4, 2) :: (1, 1) :: repeat (1, 2) 112 ++ (10106, 2) :: (1, 1) :: repeat (1, 2) 20403 ++ (54789, 2) :: (1, 1) :: repeat (1, 2) 134248 ++ w) with ((6 - 2, 2) :: (1, 1) :: repeat (1, 2) 112 ++ (10106, 2) :: (1, 1) :: repeat (1, 2) 20403 ++ (54789, 2) :: (1, 1) :: repeat (1, 2) 134248 ++ w) by sec_eq.
    apply (sTUP [] 4 13 6 2 ((1, 1) :: repeat (1, 2) 112 ++ (10106, 2) :: (1, 1) :: repeat (1, 2) 20403 ++ (54789, 2) :: (1, 1) :: repeat (1, 2) 134248 ++ w) 1); closearith.
  }
  (* step 19: P PUSH *)
  apply (hsteps_trans _ (HC [] 3 1 2 ((10, 2) :: (4, 2) :: (1, 1) :: repeat (1, 2) 112 ++ (10106, 2) :: (1, 1) :: repeat (1, 2) 20403 ++ (54789, 2) :: (1, 1) :: repeat (1, 2) 134248 ++ w) 1)).
  {
    replace ((10, 2) :: (4, 2) :: (1, 1) :: repeat (1, 2) 112 ++ (10106, 2) :: (1, 1) :: repeat (1, 2) 20403 ++ (54789, 2) :: (1, 1) :: repeat (1, 2) 134248 ++ w) with ((12 - 2, 2) :: (4, 2) :: (1, 1) :: repeat (1, 2) 112 ++ (10106, 2) :: (1, 1) :: repeat (1, 2) 20403 ++ (54789, 2) :: (1, 1) :: repeat (1, 2) 134248 ++ w) by sec_eq.
    apply (sPUSH [] 3 12 ((4, 2) :: (1, 1) :: repeat (1, 2) 112 ++ (10106, 2) :: (1, 1) :: repeat (1, 2) 20403 ++ (54789, 2) :: (1, 1) :: repeat (1, 2) 134248 ++ w) 1); closearith.
  }
  (* step 20: P TDN *)
  apply (hsteps_trans _ (HB [] 3 1 4 ((10, 2) :: (4, 2) :: (1, 1) :: repeat (1, 2) 112 ++ (10106, 2) :: (1, 1) :: repeat (1, 2) 20403 ++ (54789, 2) :: (1, 1) :: repeat (1, 2) 134248 ++ w) 1)).
  {
    apply (sTDN [] 3 ((10, 2) :: (4, 2) :: (1, 1) :: repeat (1, 2) 112 ++ (10106, 2) :: (1, 1) :: repeat (1, 2) 20403 ++ (54789, 2) :: (1, 1) :: repeat (1, 2) 134248 ++ w) 1).
  }
  (* step 21: sTUP *)
  apply (hsteps_trans _ (HC [] 3 3 2 ((8, 2) :: (4, 2) :: (1, 1) :: repeat (1, 2) 112 ++ (10106, 2) :: (1, 1) :: repeat (1, 2) 20403 ++ (54789, 2) :: (1, 1) :: repeat (1, 2) 134248 ++ w) 1)).
  {
    replace ((8, 2) :: (4, 2) :: (1, 1) :: repeat (1, 2) 112 ++ (10106, 2) :: (1, 1) :: repeat (1, 2) 20403 ++ (54789, 2) :: (1, 1) :: repeat (1, 2) 134248 ++ w) with ((10 - 2, 2) :: (4, 2) :: (1, 1) :: repeat (1, 2) 112 ++ (10106, 2) :: (1, 1) :: repeat (1, 2) 20403 ++ (54789, 2) :: (1, 1) :: repeat (1, 2) 134248 ++ w) by sec_eq.
    apply (sTUP [] 3 4 10 2 ((4, 2) :: (1, 1) :: repeat (1, 2) 112 ++ (10106, 2) :: (1, 1) :: repeat (1, 2) 20403 ++ (54789, 2) :: (1, 1) :: repeat (1, 2) 134248 ++ w) 1); closearith.
  }
  (* step 22: DIPGRIND 3 2 *)
  apply (hsteps_trans _ (HC [] 0 3 2 (repeat (1, 2) 3 ++ (2, 2) :: (4, 2) :: (1, 1) :: repeat (1, 2) 112 ++ (10106, 2) :: (1, 1) :: repeat (1, 2) 20403 ++ (54789, 2) :: (1, 1) :: repeat (1, 2) 134248 ++ w) 1)).
  {
    apply (DIPGRIND 3 2 [] ((4, 2) :: (1, 1) :: repeat (1, 2) 112 ++ (10106, 2) :: (1, 1) :: repeat (1, 2) 20403 ++ (54789, 2) :: (1, 1) :: repeat (1, 2) 134248 ++ w) 1); closearith.
  }
  (* step 23: P PUSHX *)
  apply (hsteps_trans _ (HB [] 1 1 7 (repeat (1, 2) 3 ++ (2, 2) :: (4, 2) :: (1, 1) :: repeat (1, 2) 112 ++ (10106, 2) :: (1, 1) :: repeat (1, 2) 20403 ++ (54789, 2) :: (1, 1) :: repeat (1, 2) 134248 ++ w) 1)).
  {
    apply (hsteps_step _ (HB [] 1 1 7 (repeat (1, 2) 3 ++ (2, 2) :: (4, 2) :: (1, 1) :: repeat (1, 2) 112 ++ (10106, 2) :: (1, 1) :: repeat (1, 2) 20403 ++ (54789, 2) :: (1, 1) :: repeat (1, 2) 134248 ++ w) 1)); [apply hPUSHX | apply hsteps_refl].
  }
  (* step 24: M pop12 (3,) *)
  apply (hsteps_trans _ (HB [] 4 1 13 ((2, 2) :: (4, 2) :: (1, 1) :: repeat (1, 2) 112 ++ (10106, 2) :: (1, 1) :: repeat (1, 2) 20403 ++ (54789, 2) :: (1, 1) :: repeat (1, 2) 134248 ++ w) 1)).
  {
    apply (pop12 3 [] 1 7 ((2, 2) :: (4, 2) :: (1, 1) :: repeat (1, 2) 112 ++ (10106, 2) :: (1, 1) :: repeat (1, 2) 20403 ++ (54789, 2) :: (1, 1) :: repeat (1, 2) 134248 ++ w) 1); closearith.
  }
  (* step 25: P TUP2_1 *)
  apply (hsteps_trans _ (HC [5] 13 1 2 ((2, 2) :: (1, 1) :: repeat (1, 2) 112 ++ (10106, 2) :: (1, 1) :: repeat (1, 2) 20403 ++ (54789, 2) :: (1, 1) :: repeat (1, 2) 134248 ++ w) 1)).
  {
    replace ((2, 2) :: (1, 1) :: repeat (1, 2) 112 ++ (10106, 2) :: (1, 1) :: repeat (1, 2) 20403 ++ (54789, 2) :: (1, 1) :: repeat (1, 2) 134248 ++ w) with ((4 - 2, 2) :: (1, 1) :: repeat (1, 2) 112 ++ (10106, 2) :: (1, 1) :: repeat (1, 2) 20403 ++ (54789, 2) :: (1, 1) :: repeat (1, 2) 134248 ++ w) by sec_eq.
    apply (sTUP2_1 [] 4 12 4 ((1, 1) :: repeat (1, 2) 112 ++ (10106, 2) :: (1, 1) :: repeat (1, 2) 20403 ++ (54789, 2) :: (1, 1) :: repeat (1, 2) 134248 ++ w) 1); closearith.
  }
  (* step 26: P TDN *)
  apply (hsteps_trans _ (HB [5] 13 1 4 ((2, 2) :: (1, 1) :: repeat (1, 2) 112 ++ (10106, 2) :: (1, 1) :: repeat (1, 2) 20403 ++ (54789, 2) :: (1, 1) :: repeat (1, 2) 134248 ++ w) 1)).
  {
    apply (sTDN [5] 13 ((2, 2) :: (1, 1) :: repeat (1, 2) 112 ++ (10106, 2) :: (1, 1) :: repeat (1, 2) 20403 ++ (54789, 2) :: (1, 1) :: repeat (1, 2) 134248 ++ w) 1).
  }
  (* step 27: P TRANS2_1 *)
  apply (hsteps_trans _ (HB [14; 5] 5 1 3 (repeat (1, 2) 112 ++ (10106, 2) :: (1, 1) :: repeat (1, 2) 20403 ++ (54789, 2) :: (1, 1) :: repeat (1, 2) 134248 ++ w) 1)).
  {
    apply (sTRANS2_1 [5] 13 3 1 (repeat (1, 2) 112 ++ (10106, 2) :: (1, 1) :: repeat (1, 2) 20403 ++ (54789, 2) :: (1, 1) :: repeat (1, 2) 134248 ++ w) 1); closearith.
  }
  (* step 28: M pop12 (112,) *)
  apply (hsteps_trans _ (HB [14; 5] 117 1 227 ((10106, 2) :: (1, 1) :: repeat (1, 2) 20403 ++ (54789, 2) :: (1, 1) :: repeat (1, 2) 134248 ++ w) 1)).
  {
    apply (pop12 112 [14; 5] 5 3 ((10106, 2) :: (1, 1) :: repeat (1, 2) 20403 ++ (54789, 2) :: (1, 1) :: repeat (1, 2) 134248 ++ w) 1); closearith.
  }
  (* step 29: sTUP *)
  apply (hsteps_trans _ (HC [14; 5] 117 226 2 ((10104, 2) :: (1, 1) :: repeat (1, 2) 20403 ++ (54789, 2) :: (1, 1) :: repeat (1, 2) 134248 ++ w) 1)).
  {
    replace ((10104, 2) :: (1, 1) :: repeat (1, 2) 20403 ++ (54789, 2) :: (1, 1) :: repeat (1, 2) 134248 ++ w) with ((10106 - 2, 2) :: (1, 1) :: repeat (1, 2) 20403 ++ (54789, 2) :: (1, 1) :: repeat (1, 2) 134248 ++ w) by sec_eq.
    apply (sTUP [14; 5] 117 227 10106 2 ((1, 1) :: repeat (1, 2) 20403 ++ (54789, 2) :: (1, 1) :: repeat (1, 2) 134248 ++ w) 1); closearith.
  }
  (* step 30: hGRIND_even 111 *)
  apply (hsteps_trans _ (HB [14; 5] 116 1 226 ((2, 2) :: (10104, 2) :: (1, 1) :: repeat (1, 2) 20403 ++ (54789, 2) :: (1, 1) :: repeat (1, 2) 134248 ++ w) 1)).
  {
    apply (hGRIND_even 111 [14; 5] 116 ((10104, 2) :: (1, 1) :: repeat (1, 2) 20403 ++ (54789, 2) :: (1, 1) :: repeat (1, 2) 134248 ++ w) 1); closearith.
  }
  (* step 31: P TUP2_1 *)
  apply (hsteps_trans _ (HC [117; 14; 5] 226 1 2 ((10102, 2) :: (1, 1) :: repeat (1, 2) 20403 ++ (54789, 2) :: (1, 1) :: repeat (1, 2) 134248 ++ w) 1)).
  {
    replace ((10102, 2) :: (1, 1) :: repeat (1, 2) 20403 ++ (54789, 2) :: (1, 1) :: repeat (1, 2) 134248 ++ w) with ((10104 - 2, 2) :: (1, 1) :: repeat (1, 2) 20403 ++ (54789, 2) :: (1, 1) :: repeat (1, 2) 134248 ++ w) by sec_eq.
    apply (sTUP2_1 [14; 5] 116 225 10104 ((1, 1) :: repeat (1, 2) 20403 ++ (54789, 2) :: (1, 1) :: repeat (1, 2) 134248 ++ w) 1); closearith.
  }
  (* step 32: P TDN *)
  apply (hsteps_trans _ (HB [117; 14; 5] 226 1 4 ((10102, 2) :: (1, 1) :: repeat (1, 2) 20403 ++ (54789, 2) :: (1, 1) :: repeat (1, 2) 134248 ++ w) 1)).
  {
    apply (sTDN [117; 14; 5] 226 ((10102, 2) :: (1, 1) :: repeat (1, 2) 20403 ++ (54789, 2) :: (1, 1) :: repeat (1, 2) 134248 ++ w) 1).
  }
  (* step 33: sTUP *)
  apply (hsteps_trans _ (HC [117; 14; 5] 226 3 2 ((10100, 2) :: (1, 1) :: repeat (1, 2) 20403 ++ (54789, 2) :: (1, 1) :: repeat (1, 2) 134248 ++ w) 1)).
  {
    replace ((10100, 2) :: (1, 1) :: repeat (1, 2) 20403 ++ (54789, 2) :: (1, 1) :: repeat (1, 2) 134248 ++ w) with ((10102 - 2, 2) :: (1, 1) :: repeat (1, 2) 20403 ++ (54789, 2) :: (1, 1) :: repeat (1, 2) 134248 ++ w) by sec_eq.
    apply (sTUP [117; 14; 5] 226 4 10102 2 ((1, 1) :: repeat (1, 2) 20403 ++ (54789, 2) :: (1, 1) :: repeat (1, 2) 134248 ++ w) 1); closearith.
  }
  (* step 34: DIPGRIND 226 9648 *)
  apply (hsteps_trans _ (HC [117; 14; 5] 0 3 2 (repeat (1, 2) 226 ++ (9648, 2) :: (1, 1) :: repeat (1, 2) 20403 ++ (54789, 2) :: (1, 1) :: repeat (1, 2) 134248 ++ w) 1)).
  {
    apply (DIPGRIND 226 9648 [117; 14; 5] ((1, 1) :: repeat (1, 2) 20403 ++ (54789, 2) :: (1, 1) :: repeat (1, 2) 134248 ++ w) 1); closearith.
  }
  (* step 35: P PX2A *)
  apply (hsteps_trans _ (HC [5] 13 115 2 ((1, 1) :: repeat (1, 2) 228 ++ (9648, 2) :: (1, 1) :: repeat (1, 2) 20403 ++ (54789, 2) :: (1, 1) :: repeat (1, 2) 134248 ++ w) 1)).
  {
    apply (hsteps_step _ (HC [5] 13 115 2 ((1, 1) :: repeat (1, 2) 228 ++ (9648, 2) :: (1, 1) :: repeat (1, 2) 20403 ++ (54789, 2) :: (1, 1) :: repeat (1, 2) 134248 ++ w) 1)); [apply hPX2A | apply hsteps_refl].
  }
  (* step 36: P PUSH *)
  apply (hsteps_trans _ (HC [5] 12 1 2 ((113, 2) :: (1, 1) :: repeat (1, 2) 228 ++ (9648, 2) :: (1, 1) :: repeat (1, 2) 20403 ++ (54789, 2) :: (1, 1) :: repeat (1, 2) 134248 ++ w) 1)).
  {
    replace ((113, 2) :: (1, 1) :: repeat (1, 2) 228 ++ (9648, 2) :: (1, 1) :: repeat (1, 2) 20403 ++ (54789, 2) :: (1, 1) :: repeat (1, 2) 134248 ++ w) with ((115 - 2, 2) :: (1, 1) :: repeat (1, 2) 228 ++ (9648, 2) :: (1, 1) :: repeat (1, 2) 20403 ++ (54789, 2) :: (1, 1) :: repeat (1, 2) 134248 ++ w) by sec_eq.
    apply (sPUSH [5] 12 115 ((1, 1) :: repeat (1, 2) 228 ++ (9648, 2) :: (1, 1) :: repeat (1, 2) 20403 ++ (54789, 2) :: (1, 1) :: repeat (1, 2) 134248 ++ w) 1); closearith.
  }
  (* step 37: P TDN *)
  apply (hsteps_trans _ (HB [5] 12 1 4 ((113, 2) :: (1, 1) :: repeat (1, 2) 228 ++ (9648, 2) :: (1, 1) :: repeat (1, 2) 20403 ++ (54789, 2) :: (1, 1) :: repeat (1, 2) 134248 ++ w) 1)).
  {
    apply (sTDN [5] 12 ((113, 2) :: (1, 1) :: repeat (1, 2) 228 ++ (9648, 2) :: (1, 1) :: repeat (1, 2) 20403 ++ (54789, 2) :: (1, 1) :: repeat (1, 2) 134248 ++ w) 1).
  }
  (* step 38: sTUP *)
  apply (hsteps_trans _ (HC [5] 12 3 2 ((111, 2) :: (1, 1) :: repeat (1, 2) 228 ++ (9648, 2) :: (1, 1) :: repeat (1, 2) 20403 ++ (54789, 2) :: (1, 1) :: repeat (1, 2) 134248 ++ w) 1)).
  {
    replace ((111, 2) :: (1, 1) :: repeat (1, 2) 228 ++ (9648, 2) :: (1, 1) :: repeat (1, 2) 20403 ++ (54789, 2) :: (1, 1) :: repeat (1, 2) 134248 ++ w) with ((113 - 2, 2) :: (1, 1) :: repeat (1, 2) 228 ++ (9648, 2) :: (1, 1) :: repeat (1, 2) 20403 ++ (54789, 2) :: (1, 1) :: repeat (1, 2) 134248 ++ w) by sec_eq.
    apply (sTUP [5] 12 4 113 2 ((1, 1) :: repeat (1, 2) 228 ++ (9648, 2) :: (1, 1) :: repeat (1, 2) 20403 ++ (54789, 2) :: (1, 1) :: repeat (1, 2) 134248 ++ w) 1); closearith.
  }
  (* step 39: DIPGRIND 12 87 *)
  apply (hsteps_trans _ (HC [5] 0 3 2 (repeat (1, 2) 12 ++ (87, 2) :: (1, 1) :: repeat (1, 2) 228 ++ (9648, 2) :: (1, 1) :: repeat (1, 2) 20403 ++ (54789, 2) :: (1, 1) :: repeat (1, 2) 134248 ++ w) 1)).
  {
    apply (DIPGRIND 12 87 [5] ((1, 1) :: repeat (1, 2) 228 ++ (9648, 2) :: (1, 1) :: repeat (1, 2) 20403 ++ (54789, 2) :: (1, 1) :: repeat (1, 2) 134248 ++ w) 1); closearith.
  }
  (* step 40: P PX2Bgen *)
  apply (hsteps_trans _ (HB [0] 3 1 2 (repeat (1, 2) 1 ++ (1, 1) :: repeat (1, 2) 14 ++ (87, 2) :: (1, 1) :: repeat (1, 2) 228 ++ (9648, 2) :: (1, 1) :: repeat (1, 2) 20403 ++ (54789, 2) :: (1, 1) :: repeat (1, 2) 134248 ++ w) 1)).
  {
    apply (hsteps_step _ (HB [0] 3 1 2 (repeat (1, 2) 1 ++ (1, 1) :: repeat (1, 2) 14 ++ (87, 2) :: (1, 1) :: repeat (1, 2) 228 ++ (9648, 2) :: (1, 1) :: repeat (1, 2) 20403 ++ (54789, 2) :: (1, 1) :: repeat (1, 2) 134248 ++ w) 1)); [apply hPX2Bgen | apply hsteps_refl].
  }
  (* step 41: M pop12 (1,) *)
  apply (hsteps_trans _ (HB [0] 4 1 4 ((1, 1) :: repeat (1, 2) 14 ++ (87, 2) :: (1, 1) :: repeat (1, 2) 228 ++ (9648, 2) :: (1, 1) :: repeat (1, 2) 20403 ++ (54789, 2) :: (1, 1) :: repeat (1, 2) 134248 ++ w) 1)).
  {
    apply (pop12 1 [0] 3 2 ((1, 1) :: repeat (1, 2) 14 ++ (87, 2) :: (1, 1) :: repeat (1, 2) 228 ++ (9648, 2) :: (1, 1) :: repeat (1, 2) 20403 ++ (54789, 2) :: (1, 1) :: repeat (1, 2) 134248 ++ w) 1); closearith.
  }
  (* step 42: P POP *)
  apply (hsteps_trans _ (HB [0] 5 1 5 (repeat (1, 2) 14 ++ (87, 2) :: (1, 1) :: repeat (1, 2) 228 ++ (9648, 2) :: (1, 1) :: repeat (1, 2) 20403 ++ (54789, 2) :: (1, 1) :: repeat (1, 2) 134248 ++ w) 1)).
  {
    apply (sPOP1 [0] 4 4 (repeat (1, 2) 14 ++ (87, 2) :: (1, 1) :: repeat (1, 2) 228 ++ (9648, 2) :: (1, 1) :: repeat (1, 2) 20403 ++ (54789, 2) :: (1, 1) :: repeat (1, 2) 134248 ++ w) 1); closearith.
  }
  (* step 43: M pop12 (14,) *)
  apply (hsteps_trans _ (HB [0] 19 1 33 ((87, 2) :: (1, 1) :: repeat (1, 2) 228 ++ (9648, 2) :: (1, 1) :: repeat (1, 2) 20403 ++ (54789, 2) :: (1, 1) :: repeat (1, 2) 134248 ++ w) 1)).
  {
    apply (pop12 14 [0] 5 5 ((87, 2) :: (1, 1) :: repeat (1, 2) 228 ++ (9648, 2) :: (1, 1) :: repeat (1, 2) 20403 ++ (54789, 2) :: (1, 1) :: repeat (1, 2) 134248 ++ w) 1); closearith.
  }
  (* step 44: sTUP *)
  apply (hsteps_trans _ (HC [0] 19 32 2 ((85, 2) :: (1, 1) :: repeat (1, 2) 228 ++ (9648, 2) :: (1, 1) :: repeat (1, 2) 20403 ++ (54789, 2) :: (1, 1) :: repeat (1, 2) 134248 ++ w) 1)).
  {
    replace ((85, 2) :: (1, 1) :: repeat (1, 2) 228 ++ (9648, 2) :: (1, 1) :: repeat (1, 2) 20403 ++ (54789, 2) :: (1, 1) :: repeat (1, 2) 134248 ++ w) with ((87 - 2, 2) :: (1, 1) :: repeat (1, 2) 228 ++ (9648, 2) :: (1, 1) :: repeat (1, 2) 20403 ++ (54789, 2) :: (1, 1) :: repeat (1, 2) 134248 ++ w) by sec_eq.
    apply (sTUP [0] 19 33 87 2 ((1, 1) :: repeat (1, 2) 228 ++ (9648, 2) :: (1, 1) :: repeat (1, 2) 20403 ++ (54789, 2) :: (1, 1) :: repeat (1, 2) 134248 ++ w) 1); closearith.
  }
  (* step 45: hGRIND_even 14 *)
  apply (hsteps_trans _ (HB [0] 18 1 32 ((2, 2) :: (85, 2) :: (1, 1) :: repeat (1, 2) 228 ++ (9648, 2) :: (1, 1) :: repeat (1, 2) 20403 ++ (54789, 2) :: (1, 1) :: repeat (1, 2) 134248 ++ w) 1)).
  {
    apply (hGRIND_even 14 [0] 18 ((85, 2) :: (1, 1) :: repeat (1, 2) 228 ++ (9648, 2) :: (1, 1) :: repeat (1, 2) 20403 ++ (54789, 2) :: (1, 1) :: repeat (1, 2) 134248 ++ w) 1); closearith.
  }
  (* step 46: P TUP2_1 *)
  apply (hsteps_trans _ (HC [19; 0] 32 1 2 ((83, 2) :: (1, 1) :: repeat (1, 2) 228 ++ (9648, 2) :: (1, 1) :: repeat (1, 2) 20403 ++ (54789, 2) :: (1, 1) :: repeat (1, 2) 134248 ++ w) 1)).
  {
    replace ((83, 2) :: (1, 1) :: repeat (1, 2) 228 ++ (9648, 2) :: (1, 1) :: repeat (1, 2) 20403 ++ (54789, 2) :: (1, 1) :: repeat (1, 2) 134248 ++ w) with ((85 - 2, 2) :: (1, 1) :: repeat (1, 2) 228 ++ (9648, 2) :: (1, 1) :: repeat (1, 2) 20403 ++ (54789, 2) :: (1, 1) :: repeat (1, 2) 134248 ++ w) by sec_eq.
    apply (sTUP2_1 [0] 18 31 85 ((1, 1) :: repeat (1, 2) 228 ++ (9648, 2) :: (1, 1) :: repeat (1, 2) 20403 ++ (54789, 2) :: (1, 1) :: repeat (1, 2) 134248 ++ w) 1); closearith.
  }
  (* step 47: P TDN *)
  apply (hsteps_trans _ (HB [19; 0] 32 1 4 ((83, 2) :: (1, 1) :: repeat (1, 2) 228 ++ (9648, 2) :: (1, 1) :: repeat (1, 2) 20403 ++ (54789, 2) :: (1, 1) :: repeat (1, 2) 134248 ++ w) 1)).
  {
    apply (sTDN [19; 0] 32 ((83, 2) :: (1, 1) :: repeat (1, 2) 228 ++ (9648, 2) :: (1, 1) :: repeat (1, 2) 20403 ++ (54789, 2) :: (1, 1) :: repeat (1, 2) 134248 ++ w) 1).
  }
  (* step 48: sTUP *)
  apply (hsteps_trans _ (HC [19; 0] 32 3 2 ((81, 2) :: (1, 1) :: repeat (1, 2) 228 ++ (9648, 2) :: (1, 1) :: repeat (1, 2) 20403 ++ (54789, 2) :: (1, 1) :: repeat (1, 2) 134248 ++ w) 1)).
  {
    replace ((81, 2) :: (1, 1) :: repeat (1, 2) 228 ++ (9648, 2) :: (1, 1) :: repeat (1, 2) 20403 ++ (54789, 2) :: (1, 1) :: repeat (1, 2) 134248 ++ w) with ((83 - 2, 2) :: (1, 1) :: repeat (1, 2) 228 ++ (9648, 2) :: (1, 1) :: repeat (1, 2) 20403 ++ (54789, 2) :: (1, 1) :: repeat (1, 2) 134248 ++ w) by sec_eq.
    apply (sTUP [19; 0] 32 4 83 2 ((1, 1) :: repeat (1, 2) 228 ++ (9648, 2) :: (1, 1) :: repeat (1, 2) 20403 ++ (54789, 2) :: (1, 1) :: repeat (1, 2) 134248 ++ w) 1); closearith.
  }
  (* step 49: DIPGRIND 32 17 *)
  apply (hsteps_trans _ (HC [19; 0] 0 3 2 (repeat (1, 2) 32 ++ (17, 2) :: (1, 1) :: repeat (1, 2) 228 ++ (9648, 2) :: (1, 1) :: repeat (1, 2) 20403 ++ (54789, 2) :: (1, 1) :: repeat (1, 2) 134248 ++ w) 1)).
  {
    apply (DIPGRIND 32 17 [19; 0] ((1, 1) :: repeat (1, 2) 228 ++ (9648, 2) :: (1, 1) :: repeat (1, 2) 20403 ++ (54789, 2) :: (1, 1) :: repeat (1, 2) 134248 ++ w) 1); closearith.
  }
  (* step 50: P PX2A0 *)
  apply (hsteps_trans _ (HB [0] 3 1 2 ((15, 2) :: (1, 1) :: repeat (1, 2) 34 ++ (17, 2) :: (1, 1) :: repeat (1, 2) 228 ++ (9648, 2) :: (1, 1) :: repeat (1, 2) 20403 ++ (54789, 2) :: (1, 1) :: repeat (1, 2) 134248 ++ w) 1)).
  {
    apply (hsteps_step _ (HB [0] 3 1 2 ((15, 2) :: (1, 1) :: repeat (1, 2) 34 ++ (17, 2) :: (1, 1) :: repeat (1, 2) 228 ++ (9648, 2) :: (1, 1) :: repeat (1, 2) 20403 ++ (54789, 2) :: (1, 1) :: repeat (1, 2) 134248 ++ w) 1)); [apply hPX2A0 | apply hsteps_refl].
  }
  (* step 51: sTUP *)
  apply (hsteps_trans _ (HC [0] 3 1 2 ((13, 2) :: (1, 1) :: repeat (1, 2) 34 ++ (17, 2) :: (1, 1) :: repeat (1, 2) 228 ++ (9648, 2) :: (1, 1) :: repeat (1, 2) 20403 ++ (54789, 2) :: (1, 1) :: repeat (1, 2) 134248 ++ w) 1)).
  {
    replace ((13, 2) :: (1, 1) :: repeat (1, 2) 34 ++ (17, 2) :: (1, 1) :: repeat (1, 2) 228 ++ (9648, 2) :: (1, 1) :: repeat (1, 2) 20403 ++ (54789, 2) :: (1, 1) :: repeat (1, 2) 134248 ++ w) with ((15 - 2, 2) :: (1, 1) :: repeat (1, 2) 34 ++ (17, 2) :: (1, 1) :: repeat (1, 2) 228 ++ (9648, 2) :: (1, 1) :: repeat (1, 2) 20403 ++ (54789, 2) :: (1, 1) :: repeat (1, 2) 134248 ++ w) by sec_eq.
    apply (sTUP [0] 3 2 15 2 ((1, 1) :: repeat (1, 2) 34 ++ (17, 2) :: (1, 1) :: repeat (1, 2) 228 ++ (9648, 2) :: (1, 1) :: repeat (1, 2) 20403 ++ (54789, 2) :: (1, 1) :: repeat (1, 2) 134248 ++ w) 1); closearith.
  }
  (* step 52: P TDN *)
  apply (hsteps_trans _ (HB [0] 3 1 4 ((13, 2) :: (1, 1) :: repeat (1, 2) 34 ++ (17, 2) :: (1, 1) :: repeat (1, 2) 228 ++ (9648, 2) :: (1, 1) :: repeat (1, 2) 20403 ++ (54789, 2) :: (1, 1) :: repeat (1, 2) 134248 ++ w) 1)).
  {
    apply (sTDN [0] 3 ((13, 2) :: (1, 1) :: repeat (1, 2) 34 ++ (17, 2) :: (1, 1) :: repeat (1, 2) 228 ++ (9648, 2) :: (1, 1) :: repeat (1, 2) 20403 ++ (54789, 2) :: (1, 1) :: repeat (1, 2) 134248 ++ w) 1).
  }
  (* step 53: sTUP *)
  apply (hsteps_trans _ (HC [0] 3 3 2 ((11, 2) :: (1, 1) :: repeat (1, 2) 34 ++ (17, 2) :: (1, 1) :: repeat (1, 2) 228 ++ (9648, 2) :: (1, 1) :: repeat (1, 2) 20403 ++ (54789, 2) :: (1, 1) :: repeat (1, 2) 134248 ++ w) 1)).
  {
    replace ((11, 2) :: (1, 1) :: repeat (1, 2) 34 ++ (17, 2) :: (1, 1) :: repeat (1, 2) 228 ++ (9648, 2) :: (1, 1) :: repeat (1, 2) 20403 ++ (54789, 2) :: (1, 1) :: repeat (1, 2) 134248 ++ w) with ((13 - 2, 2) :: (1, 1) :: repeat (1, 2) 34 ++ (17, 2) :: (1, 1) :: repeat (1, 2) 228 ++ (9648, 2) :: (1, 1) :: repeat (1, 2) 20403 ++ (54789, 2) :: (1, 1) :: repeat (1, 2) 134248 ++ w) by sec_eq.
    apply (sTUP [0] 3 4 13 2 ((1, 1) :: repeat (1, 2) 34 ++ (17, 2) :: (1, 1) :: repeat (1, 2) 228 ++ (9648, 2) :: (1, 1) :: repeat (1, 2) 20403 ++ (54789, 2) :: (1, 1) :: repeat (1, 2) 134248 ++ w) 1); closearith.
  }
  (* step 54: DIPGRIND 3 5 *)
  apply (hsteps_trans _ (HC [0] 0 3 2 (repeat (1, 2) 3 ++ (5, 2) :: (1, 1) :: repeat (1, 2) 34 ++ (17, 2) :: (1, 1) :: repeat (1, 2) 228 ++ (9648, 2) :: (1, 1) :: repeat (1, 2) 20403 ++ (54789, 2) :: (1, 1) :: repeat (1, 2) 134248 ++ w) 1)).
  {
    apply (DIPGRIND 3 5 [0] ((1, 1) :: repeat (1, 2) 34 ++ (17, 2) :: (1, 1) :: repeat (1, 2) 228 ++ (9648, 2) :: (1, 1) :: repeat (1, 2) 20403 ++ (54789, 2) :: (1, 1) :: repeat (1, 2) 134248 ++ w) 1); closearith.
  }
  (* step 55: P PX2B0 *)
  apply (hsteps_trans _ (HB [] 0 1 5 (repeat (1, 2) 4 ++ (5, 2) :: (1, 1) :: repeat (1, 2) 34 ++ (17, 2) :: (1, 1) :: repeat (1, 2) 228 ++ (9648, 2) :: (1, 1) :: repeat (1, 2) 20403 ++ (54789, 2) :: (1, 1) :: repeat (1, 2) 134248 ++ w) 1)).
  {
    apply (hsteps_step _ (HB [] 0 1 5 (repeat (1, 2) 4 ++ (5, 2) :: (1, 1) :: repeat (1, 2) 34 ++ (17, 2) :: (1, 1) :: repeat (1, 2) 228 ++ (9648, 2) :: (1, 1) :: repeat (1, 2) 20403 ++ (54789, 2) :: (1, 1) :: repeat (1, 2) 134248 ++ w) 1)); [apply hPX2B0 | apply hsteps_refl].
  }
  (* step 56: M pop12 (4,) *)
  apply (hsteps_trans _ (HB [] 4 1 13 ((5, 2) :: (1, 1) :: repeat (1, 2) 34 ++ (17, 2) :: (1, 1) :: repeat (1, 2) 228 ++ (9648, 2) :: (1, 1) :: repeat (1, 2) 20403 ++ (54789, 2) :: (1, 1) :: repeat (1, 2) 134248 ++ w) 1)).
  {
    apply (pop12 4 [] 0 5 ((5, 2) :: (1, 1) :: repeat (1, 2) 34 ++ (17, 2) :: (1, 1) :: repeat (1, 2) 228 ++ (9648, 2) :: (1, 1) :: repeat (1, 2) 20403 ++ (54789, 2) :: (1, 1) :: repeat (1, 2) 134248 ++ w) 1); closearith.
  }
  (* step 57: sTUP *)
  apply (hsteps_trans _ (HC [] 4 12 2 ((3, 2) :: (1, 1) :: repeat (1, 2) 34 ++ (17, 2) :: (1, 1) :: repeat (1, 2) 228 ++ (9648, 2) :: (1, 1) :: repeat (1, 2) 20403 ++ (54789, 2) :: (1, 1) :: repeat (1, 2) 134248 ++ w) 1)).
  {
    replace ((3, 2) :: (1, 1) :: repeat (1, 2) 34 ++ (17, 2) :: (1, 1) :: repeat (1, 2) 228 ++ (9648, 2) :: (1, 1) :: repeat (1, 2) 20403 ++ (54789, 2) :: (1, 1) :: repeat (1, 2) 134248 ++ w) with ((5 - 2, 2) :: (1, 1) :: repeat (1, 2) 34 ++ (17, 2) :: (1, 1) :: repeat (1, 2) 228 ++ (9648, 2) :: (1, 1) :: repeat (1, 2) 20403 ++ (54789, 2) :: (1, 1) :: repeat (1, 2) 134248 ++ w) by sec_eq.
    apply (sTUP [] 4 13 5 2 ((1, 1) :: repeat (1, 2) 34 ++ (17, 2) :: (1, 1) :: repeat (1, 2) 228 ++ (9648, 2) :: (1, 1) :: repeat (1, 2) 20403 ++ (54789, 2) :: (1, 1) :: repeat (1, 2) 134248 ++ w) 1); closearith.
  }
  (* step 58: P PUSH *)
  apply (hsteps_trans _ (HC [] 3 1 2 ((10, 2) :: (3, 2) :: (1, 1) :: repeat (1, 2) 34 ++ (17, 2) :: (1, 1) :: repeat (1, 2) 228 ++ (9648, 2) :: (1, 1) :: repeat (1, 2) 20403 ++ (54789, 2) :: (1, 1) :: repeat (1, 2) 134248 ++ w) 1)).
  {
    replace ((10, 2) :: (3, 2) :: (1, 1) :: repeat (1, 2) 34 ++ (17, 2) :: (1, 1) :: repeat (1, 2) 228 ++ (9648, 2) :: (1, 1) :: repeat (1, 2) 20403 ++ (54789, 2) :: (1, 1) :: repeat (1, 2) 134248 ++ w) with ((12 - 2, 2) :: (3, 2) :: (1, 1) :: repeat (1, 2) 34 ++ (17, 2) :: (1, 1) :: repeat (1, 2) 228 ++ (9648, 2) :: (1, 1) :: repeat (1, 2) 20403 ++ (54789, 2) :: (1, 1) :: repeat (1, 2) 134248 ++ w) by sec_eq.
    apply (sPUSH [] 3 12 ((3, 2) :: (1, 1) :: repeat (1, 2) 34 ++ (17, 2) :: (1, 1) :: repeat (1, 2) 228 ++ (9648, 2) :: (1, 1) :: repeat (1, 2) 20403 ++ (54789, 2) :: (1, 1) :: repeat (1, 2) 134248 ++ w) 1); closearith.
  }
  (* step 59: P TDN *)
  apply (hsteps_trans _ (HB [] 3 1 4 ((10, 2) :: (3, 2) :: (1, 1) :: repeat (1, 2) 34 ++ (17, 2) :: (1, 1) :: repeat (1, 2) 228 ++ (9648, 2) :: (1, 1) :: repeat (1, 2) 20403 ++ (54789, 2) :: (1, 1) :: repeat (1, 2) 134248 ++ w) 1)).
  {
    apply (sTDN [] 3 ((10, 2) :: (3, 2) :: (1, 1) :: repeat (1, 2) 34 ++ (17, 2) :: (1, 1) :: repeat (1, 2) 228 ++ (9648, 2) :: (1, 1) :: repeat (1, 2) 20403 ++ (54789, 2) :: (1, 1) :: repeat (1, 2) 134248 ++ w) 1).
  }
  (* step 60: sTUP *)
  apply (hsteps_trans _ (HC [] 3 3 2 ((8, 2) :: (3, 2) :: (1, 1) :: repeat (1, 2) 34 ++ (17, 2) :: (1, 1) :: repeat (1, 2) 228 ++ (9648, 2) :: (1, 1) :: repeat (1, 2) 20403 ++ (54789, 2) :: (1, 1) :: repeat (1, 2) 134248 ++ w) 1)).
  {
    replace ((8, 2) :: (3, 2) :: (1, 1) :: repeat (1, 2) 34 ++ (17, 2) :: (1, 1) :: repeat (1, 2) 228 ++ (9648, 2) :: (1, 1) :: repeat (1, 2) 20403 ++ (54789, 2) :: (1, 1) :: repeat (1, 2) 134248 ++ w) with ((10 - 2, 2) :: (3, 2) :: (1, 1) :: repeat (1, 2) 34 ++ (17, 2) :: (1, 1) :: repeat (1, 2) 228 ++ (9648, 2) :: (1, 1) :: repeat (1, 2) 20403 ++ (54789, 2) :: (1, 1) :: repeat (1, 2) 134248 ++ w) by sec_eq.
    apply (sTUP [] 3 4 10 2 ((3, 2) :: (1, 1) :: repeat (1, 2) 34 ++ (17, 2) :: (1, 1) :: repeat (1, 2) 228 ++ (9648, 2) :: (1, 1) :: repeat (1, 2) 20403 ++ (54789, 2) :: (1, 1) :: repeat (1, 2) 134248 ++ w) 1); closearith.
  }
  (* step 61: DIPGRIND 3 2 *)
  apply (hsteps_trans _ (HC [] 0 3 2 (repeat (1, 2) 3 ++ (2, 2) :: (3, 2) :: (1, 1) :: repeat (1, 2) 34 ++ (17, 2) :: (1, 1) :: repeat (1, 2) 228 ++ (9648, 2) :: (1, 1) :: repeat (1, 2) 20403 ++ (54789, 2) :: (1, 1) :: repeat (1, 2) 134248 ++ w) 1)).
  {
    apply (DIPGRIND 3 2 [] ((3, 2) :: (1, 1) :: repeat (1, 2) 34 ++ (17, 2) :: (1, 1) :: repeat (1, 2) 228 ++ (9648, 2) :: (1, 1) :: repeat (1, 2) 20403 ++ (54789, 2) :: (1, 1) :: repeat (1, 2) 134248 ++ w) 1); closearith.
  }
  (* step 62: P PUSHX *)
  apply (hsteps_trans _ (HB [] 1 1 7 (repeat (1, 2) 3 ++ (2, 2) :: (3, 2) :: (1, 1) :: repeat (1, 2) 34 ++ (17, 2) :: (1, 1) :: repeat (1, 2) 228 ++ (9648, 2) :: (1, 1) :: repeat (1, 2) 20403 ++ (54789, 2) :: (1, 1) :: repeat (1, 2) 134248 ++ w) 1)).
  {
    apply (hsteps_step _ (HB [] 1 1 7 (repeat (1, 2) 3 ++ (2, 2) :: (3, 2) :: (1, 1) :: repeat (1, 2) 34 ++ (17, 2) :: (1, 1) :: repeat (1, 2) 228 ++ (9648, 2) :: (1, 1) :: repeat (1, 2) 20403 ++ (54789, 2) :: (1, 1) :: repeat (1, 2) 134248 ++ w) 1)); [apply hPUSHX | apply hsteps_refl].
  }
  (* step 63: M pop12 (3,) *)
  apply (hsteps_trans _ (HB [] 4 1 13 ((2, 2) :: (3, 2) :: (1, 1) :: repeat (1, 2) 34 ++ (17, 2) :: (1, 1) :: repeat (1, 2) 228 ++ (9648, 2) :: (1, 1) :: repeat (1, 2) 20403 ++ (54789, 2) :: (1, 1) :: repeat (1, 2) 134248 ++ w) 1)).
  {
    apply (pop12 3 [] 1 7 ((2, 2) :: (3, 2) :: (1, 1) :: repeat (1, 2) 34 ++ (17, 2) :: (1, 1) :: repeat (1, 2) 228 ++ (9648, 2) :: (1, 1) :: repeat (1, 2) 20403 ++ (54789, 2) :: (1, 1) :: repeat (1, 2) 134248 ++ w) 1); closearith.
  }
  (* step 64: P TUP2_1 *)
  apply (hsteps_trans _ (HC [5] 13 1 2 (repeat (1, 2) 1 ++ (1, 1) :: repeat (1, 2) 34 ++ (17, 2) :: (1, 1) :: repeat (1, 2) 228 ++ (9648, 2) :: (1, 1) :: repeat (1, 2) 20403 ++ (54789, 2) :: (1, 1) :: repeat (1, 2) 134248 ++ w) 1)).
  {
    replace (repeat (1, 2) 1 ++ (1, 1) :: repeat (1, 2) 34 ++ (17, 2) :: (1, 1) :: repeat (1, 2) 228 ++ (9648, 2) :: (1, 1) :: repeat (1, 2) 20403 ++ (54789, 2) :: (1, 1) :: repeat (1, 2) 134248 ++ w) with ((3 - 2, 2) :: (1, 1) :: repeat (1, 2) 34 ++ (17, 2) :: (1, 1) :: repeat (1, 2) 228 ++ (9648, 2) :: (1, 1) :: repeat (1, 2) 20403 ++ (54789, 2) :: (1, 1) :: repeat (1, 2) 134248 ++ w) by sec_eq.
    apply (sTUP2_1 [] 4 12 3 ((1, 1) :: repeat (1, 2) 34 ++ (17, 2) :: (1, 1) :: repeat (1, 2) 228 ++ (9648, 2) :: (1, 1) :: repeat (1, 2) 20403 ++ (54789, 2) :: (1, 1) :: repeat (1, 2) 134248 ++ w) 1); closearith.
  }
  (* step 65: P TDN *)
  apply (hsteps_trans _ (HB [5] 13 1 4 (repeat (1, 2) 1 ++ (1, 1) :: repeat (1, 2) 34 ++ (17, 2) :: (1, 1) :: repeat (1, 2) 228 ++ (9648, 2) :: (1, 1) :: repeat (1, 2) 20403 ++ (54789, 2) :: (1, 1) :: repeat (1, 2) 134248 ++ w) 1)).
  {
    apply (sTDN [5] 13 (repeat (1, 2) 1 ++ (1, 1) :: repeat (1, 2) 34 ++ (17, 2) :: (1, 1) :: repeat (1, 2) 228 ++ (9648, 2) :: (1, 1) :: repeat (1, 2) 20403 ++ (54789, 2) :: (1, 1) :: repeat (1, 2) 134248 ++ w) 1).
  }
  (* step 66: M pop12 (1,) *)
  apply (hsteps_trans _ (HB [5] 14 1 6 ((1, 1) :: repeat (1, 2) 34 ++ (17, 2) :: (1, 1) :: repeat (1, 2) 228 ++ (9648, 2) :: (1, 1) :: repeat (1, 2) 20403 ++ (54789, 2) :: (1, 1) :: repeat (1, 2) 134248 ++ w) 1)).
  {
    apply (pop12 1 [5] 13 4 ((1, 1) :: repeat (1, 2) 34 ++ (17, 2) :: (1, 1) :: repeat (1, 2) 228 ++ (9648, 2) :: (1, 1) :: repeat (1, 2) 20403 ++ (54789, 2) :: (1, 1) :: repeat (1, 2) 134248 ++ w) 1); closearith.
  }
  (* step 67: P POP *)
  apply (hsteps_trans _ (HB [5] 15 1 7 (repeat (1, 2) 34 ++ (17, 2) :: (1, 1) :: repeat (1, 2) 228 ++ (9648, 2) :: (1, 1) :: repeat (1, 2) 20403 ++ (54789, 2) :: (1, 1) :: repeat (1, 2) 134248 ++ w) 1)).
  {
    apply (sPOP1 [5] 14 6 (repeat (1, 2) 34 ++ (17, 2) :: (1, 1) :: repeat (1, 2) 228 ++ (9648, 2) :: (1, 1) :: repeat (1, 2) 20403 ++ (54789, 2) :: (1, 1) :: repeat (1, 2) 134248 ++ w) 1); closearith.
  }
  (* step 68: M pop12 (34,) *)
  apply (hsteps_trans _ (HB [5] 49 1 75 ((17, 2) :: (1, 1) :: repeat (1, 2) 228 ++ (9648, 2) :: (1, 1) :: repeat (1, 2) 20403 ++ (54789, 2) :: (1, 1) :: repeat (1, 2) 134248 ++ w) 1)).
  {
    apply (pop12 34 [5] 15 7 ((17, 2) :: (1, 1) :: repeat (1, 2) 228 ++ (9648, 2) :: (1, 1) :: repeat (1, 2) 20403 ++ (54789, 2) :: (1, 1) :: repeat (1, 2) 134248 ++ w) 1); closearith.
  }
  (* step 69: sTUP *)
  apply (hsteps_trans _ (HC [5] 49 74 2 ((15, 2) :: (1, 1) :: repeat (1, 2) 228 ++ (9648, 2) :: (1, 1) :: repeat (1, 2) 20403 ++ (54789, 2) :: (1, 1) :: repeat (1, 2) 134248 ++ w) 1)).
  {
    replace ((15, 2) :: (1, 1) :: repeat (1, 2) 228 ++ (9648, 2) :: (1, 1) :: repeat (1, 2) 20403 ++ (54789, 2) :: (1, 1) :: repeat (1, 2) 134248 ++ w) with ((17 - 2, 2) :: (1, 1) :: repeat (1, 2) 228 ++ (9648, 2) :: (1, 1) :: repeat (1, 2) 20403 ++ (54789, 2) :: (1, 1) :: repeat (1, 2) 134248 ++ w) by sec_eq.
    apply (sTUP [5] 49 75 17 2 ((1, 1) :: repeat (1, 2) 228 ++ (9648, 2) :: (1, 1) :: repeat (1, 2) 20403 ++ (54789, 2) :: (1, 1) :: repeat (1, 2) 134248 ++ w) 1); closearith.
  }
  (* step 70: hGRIND_even 35 *)
  apply (hsteps_trans _ (HB [5] 48 1 74 ((2, 2) :: (15, 2) :: (1, 1) :: repeat (1, 2) 228 ++ (9648, 2) :: (1, 1) :: repeat (1, 2) 20403 ++ (54789, 2) :: (1, 1) :: repeat (1, 2) 134248 ++ w) 1)).
  {
    apply (hGRIND_even 35 [5] 48 ((15, 2) :: (1, 1) :: repeat (1, 2) 228 ++ (9648, 2) :: (1, 1) :: repeat (1, 2) 20403 ++ (54789, 2) :: (1, 1) :: repeat (1, 2) 134248 ++ w) 1); closearith.
  }
  (* step 71: P TUP2_1 *)
  apply (hsteps_trans _ (HC [49; 5] 74 1 2 ((13, 2) :: (1, 1) :: repeat (1, 2) 228 ++ (9648, 2) :: (1, 1) :: repeat (1, 2) 20403 ++ (54789, 2) :: (1, 1) :: repeat (1, 2) 134248 ++ w) 1)).
  {
    replace ((13, 2) :: (1, 1) :: repeat (1, 2) 228 ++ (9648, 2) :: (1, 1) :: repeat (1, 2) 20403 ++ (54789, 2) :: (1, 1) :: repeat (1, 2) 134248 ++ w) with ((15 - 2, 2) :: (1, 1) :: repeat (1, 2) 228 ++ (9648, 2) :: (1, 1) :: repeat (1, 2) 20403 ++ (54789, 2) :: (1, 1) :: repeat (1, 2) 134248 ++ w) by sec_eq.
    apply (sTUP2_1 [5] 48 73 15 ((1, 1) :: repeat (1, 2) 228 ++ (9648, 2) :: (1, 1) :: repeat (1, 2) 20403 ++ (54789, 2) :: (1, 1) :: repeat (1, 2) 134248 ++ w) 1); closearith.
  }
  (* step 72: P TDN *)
  apply (hsteps_trans _ (HB [49; 5] 74 1 4 ((13, 2) :: (1, 1) :: repeat (1, 2) 228 ++ (9648, 2) :: (1, 1) :: repeat (1, 2) 20403 ++ (54789, 2) :: (1, 1) :: repeat (1, 2) 134248 ++ w) 1)).
  {
    apply (sTDN [49; 5] 74 ((13, 2) :: (1, 1) :: repeat (1, 2) 228 ++ (9648, 2) :: (1, 1) :: repeat (1, 2) 20403 ++ (54789, 2) :: (1, 1) :: repeat (1, 2) 134248 ++ w) 1).
  }
  (* step 73: sTUP *)
  apply (hsteps_trans _ (HC [49; 5] 74 3 2 ((11, 2) :: (1, 1) :: repeat (1, 2) 228 ++ (9648, 2) :: (1, 1) :: repeat (1, 2) 20403 ++ (54789, 2) :: (1, 1) :: repeat (1, 2) 134248 ++ w) 1)).
  {
    replace ((11, 2) :: (1, 1) :: repeat (1, 2) 228 ++ (9648, 2) :: (1, 1) :: repeat (1, 2) 20403 ++ (54789, 2) :: (1, 1) :: repeat (1, 2) 134248 ++ w) with ((13 - 2, 2) :: (1, 1) :: repeat (1, 2) 228 ++ (9648, 2) :: (1, 1) :: repeat (1, 2) 20403 ++ (54789, 2) :: (1, 1) :: repeat (1, 2) 134248 ++ w) by sec_eq.
    apply (sTUP [49; 5] 74 4 13 2 ((1, 1) :: repeat (1, 2) 228 ++ (9648, 2) :: (1, 1) :: repeat (1, 2) 20403 ++ (54789, 2) :: (1, 1) :: repeat (1, 2) 134248 ++ w) 1); closearith.
  }
  (* step 74: CLEANG_odd 4 *)
  apply (hsteps_trans _ (HB [49; 5] 74 1 16 (repeat (1, 2) 1 ++ (1, 1) :: repeat (1, 2) 228 ++ (9648, 2) :: (1, 1) :: repeat (1, 2) 20403 ++ (54789, 2) :: (1, 1) :: repeat (1, 2) 134248 ++ w) 1)).
  {
    replace (repeat (1, 2) 1 ++ (1, 1) :: repeat (1, 2) 228 ++ (9648, 2) :: (1, 1) :: repeat (1, 2) 20403 ++ (54789, 2) :: (1, 1) :: repeat (1, 2) 134248 ++ w) with ((1, 2) :: (1, 1) :: repeat (1, 2) 228 ++ (9648, 2) :: (1, 1) :: repeat (1, 2) 20403 ++ (54789, 2) :: (1, 1) :: repeat (1, 2) 134248 ++ w) by sec_eq.
    apply (CLEANG_odd 4 [49; 5] 74 ((1, 1) :: repeat (1, 2) 228 ++ (9648, 2) :: (1, 1) :: repeat (1, 2) 20403 ++ (54789, 2) :: (1, 1) :: repeat (1, 2) 134248 ++ w) 1); closearith.
  }
  (* step 75: M pop12 (1,) *)
  apply (hsteps_trans _ (HB [49; 5] 75 1 18 ((1, 1) :: repeat (1, 2) 228 ++ (9648, 2) :: (1, 1) :: repeat (1, 2) 20403 ++ (54789, 2) :: (1, 1) :: repeat (1, 2) 134248 ++ w) 1)).
  {
    apply (pop12 1 [49; 5] 74 16 ((1, 1) :: repeat (1, 2) 228 ++ (9648, 2) :: (1, 1) :: repeat (1, 2) 20403 ++ (54789, 2) :: (1, 1) :: repeat (1, 2) 134248 ++ w) 1); closearith.
  }
  (* step 76: P POP *)
    apply (sPOP1 [49; 5] 75 18 (repeat (1, 2) 228 ++ (9648, 2) :: (1, 1) :: repeat (1, 2) 20403 ++ (54789, 2) :: (1, 1) :: repeat (1, 2) 134248 ++ w) 1); closearith.
Qed.

(* CASCADE52b: steps 77-152 of the CASCADE52 chain. *)
Lemma CASCADE52b : forall w,
  hsteps (HB [49; 5] 76 1 19 (repeat (1, 2) 228 ++ (9648, 2) :: (1, 1) :: repeat (1, 2) 20403 ++ (54789, 2) :: (1, 1) :: repeat (1, 2) 134248 ++ w) 1)
         (HC [20; 0] 0 3 2 (repeat (1, 2) 33 ++ (38, 2) :: (1, 1) :: repeat (1, 2) 210 ++ (49, 2) :: (1, 1) :: repeat (1, 2) 956 ++ (6780, 2) :: (1, 1) :: repeat (1, 2) 20403 ++ (54789, 2) :: (1, 1) :: repeat (1, 2) 134248 ++ w) 1).
Proof.
  intro w.
  (* step 77: M pop12 (228,) *)
  apply (hsteps_trans _ (HB [49; 5] 304 1 475 ((9648, 2) :: (1, 1) :: repeat (1, 2) 20403 ++ (54789, 2) :: (1, 1) :: repeat (1, 2) 134248 ++ w) 1)).
  {
    apply (pop12 228 [49; 5] 76 19 ((9648, 2) :: (1, 1) :: repeat (1, 2) 20403 ++ (54789, 2) :: (1, 1) :: repeat (1, 2) 134248 ++ w) 1); closearith.
  }
  (* step 78: sTUP *)
  apply (hsteps_trans _ (HC [49; 5] 304 474 2 ((9646, 2) :: (1, 1) :: repeat (1, 2) 20403 ++ (54789, 2) :: (1, 1) :: repeat (1, 2) 134248 ++ w) 1)).
  {
    replace ((9646, 2) :: (1, 1) :: repeat (1, 2) 20403 ++ (54789, 2) :: (1, 1) :: repeat (1, 2) 134248 ++ w) with ((9648 - 2, 2) :: (1, 1) :: repeat (1, 2) 20403 ++ (54789, 2) :: (1, 1) :: repeat (1, 2) 134248 ++ w) by sec_eq.
    apply (sTUP [49; 5] 304 475 9648 2 ((1, 1) :: repeat (1, 2) 20403 ++ (54789, 2) :: (1, 1) :: repeat (1, 2) 134248 ++ w) 1); closearith.
  }
  (* step 79: hGRIND_even 235 *)
  apply (hsteps_trans _ (HB [49; 5] 303 1 474 ((2, 2) :: (9646, 2) :: (1, 1) :: repeat (1, 2) 20403 ++ (54789, 2) :: (1, 1) :: repeat (1, 2) 134248 ++ w) 1)).
  {
    apply (hGRIND_even 235 [49; 5] 303 ((9646, 2) :: (1, 1) :: repeat (1, 2) 20403 ++ (54789, 2) :: (1, 1) :: repeat (1, 2) 134248 ++ w) 1); closearith.
  }
  (* step 80: P TUP2_1 *)
  apply (hsteps_trans _ (HC [304; 49; 5] 474 1 2 ((9644, 2) :: (1, 1) :: repeat (1, 2) 20403 ++ (54789, 2) :: (1, 1) :: repeat (1, 2) 134248 ++ w) 1)).
  {
    replace ((9644, 2) :: (1, 1) :: repeat (1, 2) 20403 ++ (54789, 2) :: (1, 1) :: repeat (1, 2) 134248 ++ w) with ((9646 - 2, 2) :: (1, 1) :: repeat (1, 2) 20403 ++ (54789, 2) :: (1, 1) :: repeat (1, 2) 134248 ++ w) by sec_eq.
    apply (sTUP2_1 [49; 5] 303 473 9646 ((1, 1) :: repeat (1, 2) 20403 ++ (54789, 2) :: (1, 1) :: repeat (1, 2) 134248 ++ w) 1); closearith.
  }
  (* step 81: P TDN *)
  apply (hsteps_trans _ (HB [304; 49; 5] 474 1 4 ((9644, 2) :: (1, 1) :: repeat (1, 2) 20403 ++ (54789, 2) :: (1, 1) :: repeat (1, 2) 134248 ++ w) 1)).
  {
    apply (sTDN [304; 49; 5] 474 ((9644, 2) :: (1, 1) :: repeat (1, 2) 20403 ++ (54789, 2) :: (1, 1) :: repeat (1, 2) 134248 ++ w) 1).
  }
  (* step 82: sTUP *)
  apply (hsteps_trans _ (HC [304; 49; 5] 474 3 2 ((9642, 2) :: (1, 1) :: repeat (1, 2) 20403 ++ (54789, 2) :: (1, 1) :: repeat (1, 2) 134248 ++ w) 1)).
  {
    replace ((9642, 2) :: (1, 1) :: repeat (1, 2) 20403 ++ (54789, 2) :: (1, 1) :: repeat (1, 2) 134248 ++ w) with ((9644 - 2, 2) :: (1, 1) :: repeat (1, 2) 20403 ++ (54789, 2) :: (1, 1) :: repeat (1, 2) 134248 ++ w) by sec_eq.
    apply (sTUP [304; 49; 5] 474 4 9644 2 ((1, 1) :: repeat (1, 2) 20403 ++ (54789, 2) :: (1, 1) :: repeat (1, 2) 134248 ++ w) 1); closearith.
  }
  (* step 83: DIPGRIND 474 8694 *)
  apply (hsteps_trans _ (HC [304; 49; 5] 0 3 2 (repeat (1, 2) 474 ++ (8694, 2) :: (1, 1) :: repeat (1, 2) 20403 ++ (54789, 2) :: (1, 1) :: repeat (1, 2) 134248 ++ w) 1)).
  {
    apply (DIPGRIND 474 8694 [304; 49; 5] ((1, 1) :: repeat (1, 2) 20403 ++ (54789, 2) :: (1, 1) :: repeat (1, 2) 134248 ++ w) 1); closearith.
  }
  (* step 84: P PX2A *)
  apply (hsteps_trans _ (HC [5] 48 302 2 ((1, 1) :: repeat (1, 2) 476 ++ (8694, 2) :: (1, 1) :: repeat (1, 2) 20403 ++ (54789, 2) :: (1, 1) :: repeat (1, 2) 134248 ++ w) 1)).
  {
    apply (hsteps_step _ (HC [5] 48 302 2 ((1, 1) :: repeat (1, 2) 476 ++ (8694, 2) :: (1, 1) :: repeat (1, 2) 20403 ++ (54789, 2) :: (1, 1) :: repeat (1, 2) 134248 ++ w) 1)); [apply hPX2A | apply hsteps_refl].
  }
  (* step 85: P PUSH *)
  apply (hsteps_trans _ (HC [5] 47 1 2 ((300, 2) :: (1, 1) :: repeat (1, 2) 476 ++ (8694, 2) :: (1, 1) :: repeat (1, 2) 20403 ++ (54789, 2) :: (1, 1) :: repeat (1, 2) 134248 ++ w) 1)).
  {
    replace ((300, 2) :: (1, 1) :: repeat (1, 2) 476 ++ (8694, 2) :: (1, 1) :: repeat (1, 2) 20403 ++ (54789, 2) :: (1, 1) :: repeat (1, 2) 134248 ++ w) with ((302 - 2, 2) :: (1, 1) :: repeat (1, 2) 476 ++ (8694, 2) :: (1, 1) :: repeat (1, 2) 20403 ++ (54789, 2) :: (1, 1) :: repeat (1, 2) 134248 ++ w) by sec_eq.
    apply (sPUSH [5] 47 302 ((1, 1) :: repeat (1, 2) 476 ++ (8694, 2) :: (1, 1) :: repeat (1, 2) 20403 ++ (54789, 2) :: (1, 1) :: repeat (1, 2) 134248 ++ w) 1); closearith.
  }
  (* step 86: P TDN *)
  apply (hsteps_trans _ (HB [5] 47 1 4 ((300, 2) :: (1, 1) :: repeat (1, 2) 476 ++ (8694, 2) :: (1, 1) :: repeat (1, 2) 20403 ++ (54789, 2) :: (1, 1) :: repeat (1, 2) 134248 ++ w) 1)).
  {
    apply (sTDN [5] 47 ((300, 2) :: (1, 1) :: repeat (1, 2) 476 ++ (8694, 2) :: (1, 1) :: repeat (1, 2) 20403 ++ (54789, 2) :: (1, 1) :: repeat (1, 2) 134248 ++ w) 1).
  }
  (* step 87: sTUP *)
  apply (hsteps_trans _ (HC [5] 47 3 2 ((298, 2) :: (1, 1) :: repeat (1, 2) 476 ++ (8694, 2) :: (1, 1) :: repeat (1, 2) 20403 ++ (54789, 2) :: (1, 1) :: repeat (1, 2) 134248 ++ w) 1)).
  {
    replace ((298, 2) :: (1, 1) :: repeat (1, 2) 476 ++ (8694, 2) :: (1, 1) :: repeat (1, 2) 20403 ++ (54789, 2) :: (1, 1) :: repeat (1, 2) 134248 ++ w) with ((300 - 2, 2) :: (1, 1) :: repeat (1, 2) 476 ++ (8694, 2) :: (1, 1) :: repeat (1, 2) 20403 ++ (54789, 2) :: (1, 1) :: repeat (1, 2) 134248 ++ w) by sec_eq.
    apply (sTUP [5] 47 4 300 2 ((1, 1) :: repeat (1, 2) 476 ++ (8694, 2) :: (1, 1) :: repeat (1, 2) 20403 ++ (54789, 2) :: (1, 1) :: repeat (1, 2) 134248 ++ w) 1); closearith.
  }
  (* step 88: DIPGRIND 47 204 *)
  apply (hsteps_trans _ (HC [5] 0 3 2 (repeat (1, 2) 47 ++ (204, 2) :: (1, 1) :: repeat (1, 2) 476 ++ (8694, 2) :: (1, 1) :: repeat (1, 2) 20403 ++ (54789, 2) :: (1, 1) :: repeat (1, 2) 134248 ++ w) 1)).
  {
    apply (DIPGRIND 47 204 [5] ((1, 1) :: repeat (1, 2) 476 ++ (8694, 2) :: (1, 1) :: repeat (1, 2) 20403 ++ (54789, 2) :: (1, 1) :: repeat (1, 2) 134248 ++ w) 1); closearith.
  }
  (* step 89: P PX2Bgen *)
  apply (hsteps_trans _ (HB [0] 3 1 2 (repeat (1, 2) 1 ++ (1, 1) :: repeat (1, 2) 49 ++ (204, 2) :: (1, 1) :: repeat (1, 2) 476 ++ (8694, 2) :: (1, 1) :: repeat (1, 2) 20403 ++ (54789, 2) :: (1, 1) :: repeat (1, 2) 134248 ++ w) 1)).
  {
    apply (hsteps_step _ (HB [0] 3 1 2 (repeat (1, 2) 1 ++ (1, 1) :: repeat (1, 2) 49 ++ (204, 2) :: (1, 1) :: repeat (1, 2) 476 ++ (8694, 2) :: (1, 1) :: repeat (1, 2) 20403 ++ (54789, 2) :: (1, 1) :: repeat (1, 2) 134248 ++ w) 1)); [apply hPX2Bgen | apply hsteps_refl].
  }
  (* step 90: M pop12 (1,) *)
  apply (hsteps_trans _ (HB [0] 4 1 4 ((1, 1) :: repeat (1, 2) 49 ++ (204, 2) :: (1, 1) :: repeat (1, 2) 476 ++ (8694, 2) :: (1, 1) :: repeat (1, 2) 20403 ++ (54789, 2) :: (1, 1) :: repeat (1, 2) 134248 ++ w) 1)).
  {
    apply (pop12 1 [0] 3 2 ((1, 1) :: repeat (1, 2) 49 ++ (204, 2) :: (1, 1) :: repeat (1, 2) 476 ++ (8694, 2) :: (1, 1) :: repeat (1, 2) 20403 ++ (54789, 2) :: (1, 1) :: repeat (1, 2) 134248 ++ w) 1); closearith.
  }
  (* step 91: P POP *)
  apply (hsteps_trans _ (HB [0] 5 1 5 (repeat (1, 2) 49 ++ (204, 2) :: (1, 1) :: repeat (1, 2) 476 ++ (8694, 2) :: (1, 1) :: repeat (1, 2) 20403 ++ (54789, 2) :: (1, 1) :: repeat (1, 2) 134248 ++ w) 1)).
  {
    apply (sPOP1 [0] 4 4 (repeat (1, 2) 49 ++ (204, 2) :: (1, 1) :: repeat (1, 2) 476 ++ (8694, 2) :: (1, 1) :: repeat (1, 2) 20403 ++ (54789, 2) :: (1, 1) :: repeat (1, 2) 134248 ++ w) 1); closearith.
  }
  (* step 92: M pop12 (49,) *)
  apply (hsteps_trans _ (HB [0] 54 1 103 ((204, 2) :: (1, 1) :: repeat (1, 2) 476 ++ (8694, 2) :: (1, 1) :: repeat (1, 2) 20403 ++ (54789, 2) :: (1, 1) :: repeat (1, 2) 134248 ++ w) 1)).
  {
    apply (pop12 49 [0] 5 5 ((204, 2) :: (1, 1) :: repeat (1, 2) 476 ++ (8694, 2) :: (1, 1) :: repeat (1, 2) 20403 ++ (54789, 2) :: (1, 1) :: repeat (1, 2) 134248 ++ w) 1); closearith.
  }
  (* step 93: sTUP *)
  apply (hsteps_trans _ (HC [0] 54 102 2 ((202, 2) :: (1, 1) :: repeat (1, 2) 476 ++ (8694, 2) :: (1, 1) :: repeat (1, 2) 20403 ++ (54789, 2) :: (1, 1) :: repeat (1, 2) 134248 ++ w) 1)).
  {
    replace ((202, 2) :: (1, 1) :: repeat (1, 2) 476 ++ (8694, 2) :: (1, 1) :: repeat (1, 2) 20403 ++ (54789, 2) :: (1, 1) :: repeat (1, 2) 134248 ++ w) with ((204 - 2, 2) :: (1, 1) :: repeat (1, 2) 476 ++ (8694, 2) :: (1, 1) :: repeat (1, 2) 20403 ++ (54789, 2) :: (1, 1) :: repeat (1, 2) 134248 ++ w) by sec_eq.
    apply (sTUP [0] 54 103 204 2 ((1, 1) :: repeat (1, 2) 476 ++ (8694, 2) :: (1, 1) :: repeat (1, 2) 20403 ++ (54789, 2) :: (1, 1) :: repeat (1, 2) 134248 ++ w) 1); closearith.
  }
  (* step 94: hGRIND_even 49 *)
  apply (hsteps_trans _ (HB [0] 53 1 102 ((2, 2) :: (202, 2) :: (1, 1) :: repeat (1, 2) 476 ++ (8694, 2) :: (1, 1) :: repeat (1, 2) 20403 ++ (54789, 2) :: (1, 1) :: repeat (1, 2) 134248 ++ w) 1)).
  {
    apply (hGRIND_even 49 [0] 53 ((202, 2) :: (1, 1) :: repeat (1, 2) 476 ++ (8694, 2) :: (1, 1) :: repeat (1, 2) 20403 ++ (54789, 2) :: (1, 1) :: repeat (1, 2) 134248 ++ w) 1); closearith.
  }
  (* step 95: P TUP2_1 *)
  apply (hsteps_trans _ (HC [54; 0] 102 1 2 ((200, 2) :: (1, 1) :: repeat (1, 2) 476 ++ (8694, 2) :: (1, 1) :: repeat (1, 2) 20403 ++ (54789, 2) :: (1, 1) :: repeat (1, 2) 134248 ++ w) 1)).
  {
    replace ((200, 2) :: (1, 1) :: repeat (1, 2) 476 ++ (8694, 2) :: (1, 1) :: repeat (1, 2) 20403 ++ (54789, 2) :: (1, 1) :: repeat (1, 2) 134248 ++ w) with ((202 - 2, 2) :: (1, 1) :: repeat (1, 2) 476 ++ (8694, 2) :: (1, 1) :: repeat (1, 2) 20403 ++ (54789, 2) :: (1, 1) :: repeat (1, 2) 134248 ++ w) by sec_eq.
    apply (sTUP2_1 [0] 53 101 202 ((1, 1) :: repeat (1, 2) 476 ++ (8694, 2) :: (1, 1) :: repeat (1, 2) 20403 ++ (54789, 2) :: (1, 1) :: repeat (1, 2) 134248 ++ w) 1); closearith.
  }
  (* step 96: P TDN *)
  apply (hsteps_trans _ (HB [54; 0] 102 1 4 ((200, 2) :: (1, 1) :: repeat (1, 2) 476 ++ (8694, 2) :: (1, 1) :: repeat (1, 2) 20403 ++ (54789, 2) :: (1, 1) :: repeat (1, 2) 134248 ++ w) 1)).
  {
    apply (sTDN [54; 0] 102 ((200, 2) :: (1, 1) :: repeat (1, 2) 476 ++ (8694, 2) :: (1, 1) :: repeat (1, 2) 20403 ++ (54789, 2) :: (1, 1) :: repeat (1, 2) 134248 ++ w) 1).
  }
  (* step 97: sTUP *)
  apply (hsteps_trans _ (HC [54; 0] 102 3 2 ((198, 2) :: (1, 1) :: repeat (1, 2) 476 ++ (8694, 2) :: (1, 1) :: repeat (1, 2) 20403 ++ (54789, 2) :: (1, 1) :: repeat (1, 2) 134248 ++ w) 1)).
  {
    replace ((198, 2) :: (1, 1) :: repeat (1, 2) 476 ++ (8694, 2) :: (1, 1) :: repeat (1, 2) 20403 ++ (54789, 2) :: (1, 1) :: repeat (1, 2) 134248 ++ w) with ((200 - 2, 2) :: (1, 1) :: repeat (1, 2) 476 ++ (8694, 2) :: (1, 1) :: repeat (1, 2) 20403 ++ (54789, 2) :: (1, 1) :: repeat (1, 2) 134248 ++ w) by sec_eq.
    apply (sTUP [54; 0] 102 4 200 2 ((1, 1) :: repeat (1, 2) 476 ++ (8694, 2) :: (1, 1) :: repeat (1, 2) 20403 ++ (54789, 2) :: (1, 1) :: repeat (1, 2) 134248 ++ w) 1); closearith.
  }
  (* step 98: CLEANG_even 98 *)
  apply (hsteps_trans _ (HB [54; 0] 102 1 202 ((2, 2) :: (1, 1) :: repeat (1, 2) 476 ++ (8694, 2) :: (1, 1) :: repeat (1, 2) 20403 ++ (54789, 2) :: (1, 1) :: repeat (1, 2) 134248 ++ w) 1)).
  {
    apply (CLEANG_even 98 [54; 0] 102 ((1, 1) :: repeat (1, 2) 476 ++ (8694, 2) :: (1, 1) :: repeat (1, 2) 20403 ++ (54789, 2) :: (1, 1) :: repeat (1, 2) 134248 ++ w) 1); closearith.
  }
  (* step 99: P TRANS2_1 *)
  apply (hsteps_trans _ (HB [103; 54; 0] 203 1 3 (repeat (1, 2) 476 ++ (8694, 2) :: (1, 1) :: repeat (1, 2) 20403 ++ (54789, 2) :: (1, 1) :: repeat (1, 2) 134248 ++ w) 1)).
  {
    apply (sTRANS2_1 [54; 0] 102 201 1 (repeat (1, 2) 476 ++ (8694, 2) :: (1, 1) :: repeat (1, 2) 20403 ++ (54789, 2) :: (1, 1) :: repeat (1, 2) 134248 ++ w) 1); closearith.
  }
  (* step 100: M pop12 (476,) *)
  apply (hsteps_trans _ (HB [103; 54; 0] 679 1 955 ((8694, 2) :: (1, 1) :: repeat (1, 2) 20403 ++ (54789, 2) :: (1, 1) :: repeat (1, 2) 134248 ++ w) 1)).
  {
    apply (pop12 476 [103; 54; 0] 203 3 ((8694, 2) :: (1, 1) :: repeat (1, 2) 20403 ++ (54789, 2) :: (1, 1) :: repeat (1, 2) 134248 ++ w) 1); closearith.
  }
  (* step 101: sTUP *)
  apply (hsteps_trans _ (HC [103; 54; 0] 679 954 2 ((8692, 2) :: (1, 1) :: repeat (1, 2) 20403 ++ (54789, 2) :: (1, 1) :: repeat (1, 2) 134248 ++ w) 1)).
  {
    replace ((8692, 2) :: (1, 1) :: repeat (1, 2) 20403 ++ (54789, 2) :: (1, 1) :: repeat (1, 2) 134248 ++ w) with ((8694 - 2, 2) :: (1, 1) :: repeat (1, 2) 20403 ++ (54789, 2) :: (1, 1) :: repeat (1, 2) 134248 ++ w) by sec_eq.
    apply (sTUP [103; 54; 0] 679 955 8694 2 ((1, 1) :: repeat (1, 2) 20403 ++ (54789, 2) :: (1, 1) :: repeat (1, 2) 134248 ++ w) 1); closearith.
  }
  (* step 102: hGRIND_even 475 *)
  apply (hsteps_trans _ (HB [103; 54; 0] 678 1 954 ((2, 2) :: (8692, 2) :: (1, 1) :: repeat (1, 2) 20403 ++ (54789, 2) :: (1, 1) :: repeat (1, 2) 134248 ++ w) 1)).
  {
    apply (hGRIND_even 475 [103; 54; 0] 678 ((8692, 2) :: (1, 1) :: repeat (1, 2) 20403 ++ (54789, 2) :: (1, 1) :: repeat (1, 2) 134248 ++ w) 1); closearith.
  }
  (* step 103: P TUP2_1 *)
  apply (hsteps_trans _ (HC [679; 103; 54; 0] 954 1 2 ((8690, 2) :: (1, 1) :: repeat (1, 2) 20403 ++ (54789, 2) :: (1, 1) :: repeat (1, 2) 134248 ++ w) 1)).
  {
    replace ((8690, 2) :: (1, 1) :: repeat (1, 2) 20403 ++ (54789, 2) :: (1, 1) :: repeat (1, 2) 134248 ++ w) with ((8692 - 2, 2) :: (1, 1) :: repeat (1, 2) 20403 ++ (54789, 2) :: (1, 1) :: repeat (1, 2) 134248 ++ w) by sec_eq.
    apply (sTUP2_1 [103; 54; 0] 678 953 8692 ((1, 1) :: repeat (1, 2) 20403 ++ (54789, 2) :: (1, 1) :: repeat (1, 2) 134248 ++ w) 1); closearith.
  }
  (* step 104: P TDN *)
  apply (hsteps_trans _ (HB [679; 103; 54; 0] 954 1 4 ((8690, 2) :: (1, 1) :: repeat (1, 2) 20403 ++ (54789, 2) :: (1, 1) :: repeat (1, 2) 134248 ++ w) 1)).
  {
    apply (sTDN [679; 103; 54; 0] 954 ((8690, 2) :: (1, 1) :: repeat (1, 2) 20403 ++ (54789, 2) :: (1, 1) :: repeat (1, 2) 134248 ++ w) 1).
  }
  (* step 105: sTUP *)
  apply (hsteps_trans _ (HC [679; 103; 54; 0] 954 3 2 ((8688, 2) :: (1, 1) :: repeat (1, 2) 20403 ++ (54789, 2) :: (1, 1) :: repeat (1, 2) 134248 ++ w) 1)).
  {
    replace ((8688, 2) :: (1, 1) :: repeat (1, 2) 20403 ++ (54789, 2) :: (1, 1) :: repeat (1, 2) 134248 ++ w) with ((8690 - 2, 2) :: (1, 1) :: repeat (1, 2) 20403 ++ (54789, 2) :: (1, 1) :: repeat (1, 2) 134248 ++ w) by sec_eq.
    apply (sTUP [679; 103; 54; 0] 954 4 8690 2 ((1, 1) :: repeat (1, 2) 20403 ++ (54789, 2) :: (1, 1) :: repeat (1, 2) 134248 ++ w) 1); closearith.
  }
  (* step 106: DIPGRIND 954 6780 *)
  apply (hsteps_trans _ (HC [679; 103; 54; 0] 0 3 2 (repeat (1, 2) 954 ++ (6780, 2) :: (1, 1) :: repeat (1, 2) 20403 ++ (54789, 2) :: (1, 1) :: repeat (1, 2) 134248 ++ w) 1)).
  {
    apply (DIPGRIND 954 6780 [679; 103; 54; 0] ((1, 1) :: repeat (1, 2) 20403 ++ (54789, 2) :: (1, 1) :: repeat (1, 2) 134248 ++ w) 1); closearith.
  }
  (* step 107: P PX2A *)
  apply (hsteps_trans _ (HC [54; 0] 102 677 2 ((1, 1) :: repeat (1, 2) 956 ++ (6780, 2) :: (1, 1) :: repeat (1, 2) 20403 ++ (54789, 2) :: (1, 1) :: repeat (1, 2) 134248 ++ w) 1)).
  {
    apply (hsteps_step _ (HC [54; 0] 102 677 2 ((1, 1) :: repeat (1, 2) 956 ++ (6780, 2) :: (1, 1) :: repeat (1, 2) 20403 ++ (54789, 2) :: (1, 1) :: repeat (1, 2) 134248 ++ w) 1)); [apply hPX2A | apply hsteps_refl].
  }
  (* step 108: P PUSH *)
  apply (hsteps_trans _ (HC [54; 0] 101 1 2 ((675, 2) :: (1, 1) :: repeat (1, 2) 956 ++ (6780, 2) :: (1, 1) :: repeat (1, 2) 20403 ++ (54789, 2) :: (1, 1) :: repeat (1, 2) 134248 ++ w) 1)).
  {
    replace ((675, 2) :: (1, 1) :: repeat (1, 2) 956 ++ (6780, 2) :: (1, 1) :: repeat (1, 2) 20403 ++ (54789, 2) :: (1, 1) :: repeat (1, 2) 134248 ++ w) with ((677 - 2, 2) :: (1, 1) :: repeat (1, 2) 956 ++ (6780, 2) :: (1, 1) :: repeat (1, 2) 20403 ++ (54789, 2) :: (1, 1) :: repeat (1, 2) 134248 ++ w) by sec_eq.
    apply (sPUSH [54; 0] 101 677 ((1, 1) :: repeat (1, 2) 956 ++ (6780, 2) :: (1, 1) :: repeat (1, 2) 20403 ++ (54789, 2) :: (1, 1) :: repeat (1, 2) 134248 ++ w) 1); closearith.
  }
  (* step 109: P TDN *)
  apply (hsteps_trans _ (HB [54; 0] 101 1 4 ((675, 2) :: (1, 1) :: repeat (1, 2) 956 ++ (6780, 2) :: (1, 1) :: repeat (1, 2) 20403 ++ (54789, 2) :: (1, 1) :: repeat (1, 2) 134248 ++ w) 1)).
  {
    apply (sTDN [54; 0] 101 ((675, 2) :: (1, 1) :: repeat (1, 2) 956 ++ (6780, 2) :: (1, 1) :: repeat (1, 2) 20403 ++ (54789, 2) :: (1, 1) :: repeat (1, 2) 134248 ++ w) 1).
  }
  (* step 110: sTUP *)
  apply (hsteps_trans _ (HC [54; 0] 101 3 2 ((673, 2) :: (1, 1) :: repeat (1, 2) 956 ++ (6780, 2) :: (1, 1) :: repeat (1, 2) 20403 ++ (54789, 2) :: (1, 1) :: repeat (1, 2) 134248 ++ w) 1)).
  {
    replace ((673, 2) :: (1, 1) :: repeat (1, 2) 956 ++ (6780, 2) :: (1, 1) :: repeat (1, 2) 20403 ++ (54789, 2) :: (1, 1) :: repeat (1, 2) 134248 ++ w) with ((675 - 2, 2) :: (1, 1) :: repeat (1, 2) 956 ++ (6780, 2) :: (1, 1) :: repeat (1, 2) 20403 ++ (54789, 2) :: (1, 1) :: repeat (1, 2) 134248 ++ w) by sec_eq.
    apply (sTUP [54; 0] 101 4 675 2 ((1, 1) :: repeat (1, 2) 956 ++ (6780, 2) :: (1, 1) :: repeat (1, 2) 20403 ++ (54789, 2) :: (1, 1) :: repeat (1, 2) 134248 ++ w) 1); closearith.
  }
  (* step 111: DIPGRIND 101 471 *)
  apply (hsteps_trans _ (HC [54; 0] 0 3 2 (repeat (1, 2) 101 ++ (471, 2) :: (1, 1) :: repeat (1, 2) 956 ++ (6780, 2) :: (1, 1) :: repeat (1, 2) 20403 ++ (54789, 2) :: (1, 1) :: repeat (1, 2) 134248 ++ w) 1)).
  {
    apply (DIPGRIND 101 471 [54; 0] ((1, 1) :: repeat (1, 2) 956 ++ (6780, 2) :: (1, 1) :: repeat (1, 2) 20403 ++ (54789, 2) :: (1, 1) :: repeat (1, 2) 134248 ++ w) 1); closearith.
  }
  (* step 112: P PX2A0 *)
  apply (hsteps_trans _ (HB [0] 3 1 2 ((50, 2) :: (1, 1) :: repeat (1, 2) 103 ++ (471, 2) :: (1, 1) :: repeat (1, 2) 956 ++ (6780, 2) :: (1, 1) :: repeat (1, 2) 20403 ++ (54789, 2) :: (1, 1) :: repeat (1, 2) 134248 ++ w) 1)).
  {
    apply (hsteps_step _ (HB [0] 3 1 2 ((50, 2) :: (1, 1) :: repeat (1, 2) 103 ++ (471, 2) :: (1, 1) :: repeat (1, 2) 956 ++ (6780, 2) :: (1, 1) :: repeat (1, 2) 20403 ++ (54789, 2) :: (1, 1) :: repeat (1, 2) 134248 ++ w) 1)); [apply hPX2A0 | apply hsteps_refl].
  }
  (* step 113: sTUP *)
  apply (hsteps_trans _ (HC [0] 3 1 2 ((48, 2) :: (1, 1) :: repeat (1, 2) 103 ++ (471, 2) :: (1, 1) :: repeat (1, 2) 956 ++ (6780, 2) :: (1, 1) :: repeat (1, 2) 20403 ++ (54789, 2) :: (1, 1) :: repeat (1, 2) 134248 ++ w) 1)).
  {
    replace ((48, 2) :: (1, 1) :: repeat (1, 2) 103 ++ (471, 2) :: (1, 1) :: repeat (1, 2) 956 ++ (6780, 2) :: (1, 1) :: repeat (1, 2) 20403 ++ (54789, 2) :: (1, 1) :: repeat (1, 2) 134248 ++ w) with ((50 - 2, 2) :: (1, 1) :: repeat (1, 2) 103 ++ (471, 2) :: (1, 1) :: repeat (1, 2) 956 ++ (6780, 2) :: (1, 1) :: repeat (1, 2) 20403 ++ (54789, 2) :: (1, 1) :: repeat (1, 2) 134248 ++ w) by sec_eq.
    apply (sTUP [0] 3 2 50 2 ((1, 1) :: repeat (1, 2) 103 ++ (471, 2) :: (1, 1) :: repeat (1, 2) 956 ++ (6780, 2) :: (1, 1) :: repeat (1, 2) 20403 ++ (54789, 2) :: (1, 1) :: repeat (1, 2) 134248 ++ w) 1); closearith.
  }
  (* step 114: P TDN *)
  apply (hsteps_trans _ (HB [0] 3 1 4 ((48, 2) :: (1, 1) :: repeat (1, 2) 103 ++ (471, 2) :: (1, 1) :: repeat (1, 2) 956 ++ (6780, 2) :: (1, 1) :: repeat (1, 2) 20403 ++ (54789, 2) :: (1, 1) :: repeat (1, 2) 134248 ++ w) 1)).
  {
    apply (sTDN [0] 3 ((48, 2) :: (1, 1) :: repeat (1, 2) 103 ++ (471, 2) :: (1, 1) :: repeat (1, 2) 956 ++ (6780, 2) :: (1, 1) :: repeat (1, 2) 20403 ++ (54789, 2) :: (1, 1) :: repeat (1, 2) 134248 ++ w) 1).
  }
  (* step 115: sTUP *)
  apply (hsteps_trans _ (HC [0] 3 3 2 ((46, 2) :: (1, 1) :: repeat (1, 2) 103 ++ (471, 2) :: (1, 1) :: repeat (1, 2) 956 ++ (6780, 2) :: (1, 1) :: repeat (1, 2) 20403 ++ (54789, 2) :: (1, 1) :: repeat (1, 2) 134248 ++ w) 1)).
  {
    replace ((46, 2) :: (1, 1) :: repeat (1, 2) 103 ++ (471, 2) :: (1, 1) :: repeat (1, 2) 956 ++ (6780, 2) :: (1, 1) :: repeat (1, 2) 20403 ++ (54789, 2) :: (1, 1) :: repeat (1, 2) 134248 ++ w) with ((48 - 2, 2) :: (1, 1) :: repeat (1, 2) 103 ++ (471, 2) :: (1, 1) :: repeat (1, 2) 956 ++ (6780, 2) :: (1, 1) :: repeat (1, 2) 20403 ++ (54789, 2) :: (1, 1) :: repeat (1, 2) 134248 ++ w) by sec_eq.
    apply (sTUP [0] 3 4 48 2 ((1, 1) :: repeat (1, 2) 103 ++ (471, 2) :: (1, 1) :: repeat (1, 2) 956 ++ (6780, 2) :: (1, 1) :: repeat (1, 2) 20403 ++ (54789, 2) :: (1, 1) :: repeat (1, 2) 134248 ++ w) 1); closearith.
  }
  (* step 116: DIPGRIND 3 40 *)
  apply (hsteps_trans _ (HC [0] 0 3 2 (repeat (1, 2) 3 ++ (40, 2) :: (1, 1) :: repeat (1, 2) 103 ++ (471, 2) :: (1, 1) :: repeat (1, 2) 956 ++ (6780, 2) :: (1, 1) :: repeat (1, 2) 20403 ++ (54789, 2) :: (1, 1) :: repeat (1, 2) 134248 ++ w) 1)).
  {
    apply (DIPGRIND 3 40 [0] ((1, 1) :: repeat (1, 2) 103 ++ (471, 2) :: (1, 1) :: repeat (1, 2) 956 ++ (6780, 2) :: (1, 1) :: repeat (1, 2) 20403 ++ (54789, 2) :: (1, 1) :: repeat (1, 2) 134248 ++ w) 1); closearith.
  }
  (* step 117: P PX2B0 *)
  apply (hsteps_trans _ (HB [] 0 1 5 (repeat (1, 2) 4 ++ (40, 2) :: (1, 1) :: repeat (1, 2) 103 ++ (471, 2) :: (1, 1) :: repeat (1, 2) 956 ++ (6780, 2) :: (1, 1) :: repeat (1, 2) 20403 ++ (54789, 2) :: (1, 1) :: repeat (1, 2) 134248 ++ w) 1)).
  {
    apply (hsteps_step _ (HB [] 0 1 5 (repeat (1, 2) 4 ++ (40, 2) :: (1, 1) :: repeat (1, 2) 103 ++ (471, 2) :: (1, 1) :: repeat (1, 2) 956 ++ (6780, 2) :: (1, 1) :: repeat (1, 2) 20403 ++ (54789, 2) :: (1, 1) :: repeat (1, 2) 134248 ++ w) 1)); [apply hPX2B0 | apply hsteps_refl].
  }
  (* step 118: M pop12 (4,) *)
  apply (hsteps_trans _ (HB [] 4 1 13 ((40, 2) :: (1, 1) :: repeat (1, 2) 103 ++ (471, 2) :: (1, 1) :: repeat (1, 2) 956 ++ (6780, 2) :: (1, 1) :: repeat (1, 2) 20403 ++ (54789, 2) :: (1, 1) :: repeat (1, 2) 134248 ++ w) 1)).
  {
    apply (pop12 4 [] 0 5 ((40, 2) :: (1, 1) :: repeat (1, 2) 103 ++ (471, 2) :: (1, 1) :: repeat (1, 2) 956 ++ (6780, 2) :: (1, 1) :: repeat (1, 2) 20403 ++ (54789, 2) :: (1, 1) :: repeat (1, 2) 134248 ++ w) 1); closearith.
  }
  (* step 119: sTUP *)
  apply (hsteps_trans _ (HC [] 4 12 2 ((38, 2) :: (1, 1) :: repeat (1, 2) 103 ++ (471, 2) :: (1, 1) :: repeat (1, 2) 956 ++ (6780, 2) :: (1, 1) :: repeat (1, 2) 20403 ++ (54789, 2) :: (1, 1) :: repeat (1, 2) 134248 ++ w) 1)).
  {
    replace ((38, 2) :: (1, 1) :: repeat (1, 2) 103 ++ (471, 2) :: (1, 1) :: repeat (1, 2) 956 ++ (6780, 2) :: (1, 1) :: repeat (1, 2) 20403 ++ (54789, 2) :: (1, 1) :: repeat (1, 2) 134248 ++ w) with ((40 - 2, 2) :: (1, 1) :: repeat (1, 2) 103 ++ (471, 2) :: (1, 1) :: repeat (1, 2) 956 ++ (6780, 2) :: (1, 1) :: repeat (1, 2) 20403 ++ (54789, 2) :: (1, 1) :: repeat (1, 2) 134248 ++ w) by sec_eq.
    apply (sTUP [] 4 13 40 2 ((1, 1) :: repeat (1, 2) 103 ++ (471, 2) :: (1, 1) :: repeat (1, 2) 956 ++ (6780, 2) :: (1, 1) :: repeat (1, 2) 20403 ++ (54789, 2) :: (1, 1) :: repeat (1, 2) 134248 ++ w) 1); closearith.
  }
  (* step 120: P PUSH *)
  apply (hsteps_trans _ (HC [] 3 1 2 ((10, 2) :: (38, 2) :: (1, 1) :: repeat (1, 2) 103 ++ (471, 2) :: (1, 1) :: repeat (1, 2) 956 ++ (6780, 2) :: (1, 1) :: repeat (1, 2) 20403 ++ (54789, 2) :: (1, 1) :: repeat (1, 2) 134248 ++ w) 1)).
  {
    replace ((10, 2) :: (38, 2) :: (1, 1) :: repeat (1, 2) 103 ++ (471, 2) :: (1, 1) :: repeat (1, 2) 956 ++ (6780, 2) :: (1, 1) :: repeat (1, 2) 20403 ++ (54789, 2) :: (1, 1) :: repeat (1, 2) 134248 ++ w) with ((12 - 2, 2) :: (38, 2) :: (1, 1) :: repeat (1, 2) 103 ++ (471, 2) :: (1, 1) :: repeat (1, 2) 956 ++ (6780, 2) :: (1, 1) :: repeat (1, 2) 20403 ++ (54789, 2) :: (1, 1) :: repeat (1, 2) 134248 ++ w) by sec_eq.
    apply (sPUSH [] 3 12 ((38, 2) :: (1, 1) :: repeat (1, 2) 103 ++ (471, 2) :: (1, 1) :: repeat (1, 2) 956 ++ (6780, 2) :: (1, 1) :: repeat (1, 2) 20403 ++ (54789, 2) :: (1, 1) :: repeat (1, 2) 134248 ++ w) 1); closearith.
  }
  (* step 121: P TDN *)
  apply (hsteps_trans _ (HB [] 3 1 4 ((10, 2) :: (38, 2) :: (1, 1) :: repeat (1, 2) 103 ++ (471, 2) :: (1, 1) :: repeat (1, 2) 956 ++ (6780, 2) :: (1, 1) :: repeat (1, 2) 20403 ++ (54789, 2) :: (1, 1) :: repeat (1, 2) 134248 ++ w) 1)).
  {
    apply (sTDN [] 3 ((10, 2) :: (38, 2) :: (1, 1) :: repeat (1, 2) 103 ++ (471, 2) :: (1, 1) :: repeat (1, 2) 956 ++ (6780, 2) :: (1, 1) :: repeat (1, 2) 20403 ++ (54789, 2) :: (1, 1) :: repeat (1, 2) 134248 ++ w) 1).
  }
  (* step 122: sTUP *)
  apply (hsteps_trans _ (HC [] 3 3 2 ((8, 2) :: (38, 2) :: (1, 1) :: repeat (1, 2) 103 ++ (471, 2) :: (1, 1) :: repeat (1, 2) 956 ++ (6780, 2) :: (1, 1) :: repeat (1, 2) 20403 ++ (54789, 2) :: (1, 1) :: repeat (1, 2) 134248 ++ w) 1)).
  {
    replace ((8, 2) :: (38, 2) :: (1, 1) :: repeat (1, 2) 103 ++ (471, 2) :: (1, 1) :: repeat (1, 2) 956 ++ (6780, 2) :: (1, 1) :: repeat (1, 2) 20403 ++ (54789, 2) :: (1, 1) :: repeat (1, 2) 134248 ++ w) with ((10 - 2, 2) :: (38, 2) :: (1, 1) :: repeat (1, 2) 103 ++ (471, 2) :: (1, 1) :: repeat (1, 2) 956 ++ (6780, 2) :: (1, 1) :: repeat (1, 2) 20403 ++ (54789, 2) :: (1, 1) :: repeat (1, 2) 134248 ++ w) by sec_eq.
    apply (sTUP [] 3 4 10 2 ((38, 2) :: (1, 1) :: repeat (1, 2) 103 ++ (471, 2) :: (1, 1) :: repeat (1, 2) 956 ++ (6780, 2) :: (1, 1) :: repeat (1, 2) 20403 ++ (54789, 2) :: (1, 1) :: repeat (1, 2) 134248 ++ w) 1); closearith.
  }
  (* step 123: DIPGRIND 3 2 *)
  apply (hsteps_trans _ (HC [] 0 3 2 (repeat (1, 2) 3 ++ (2, 2) :: (38, 2) :: (1, 1) :: repeat (1, 2) 103 ++ (471, 2) :: (1, 1) :: repeat (1, 2) 956 ++ (6780, 2) :: (1, 1) :: repeat (1, 2) 20403 ++ (54789, 2) :: (1, 1) :: repeat (1, 2) 134248 ++ w) 1)).
  {
    apply (DIPGRIND 3 2 [] ((38, 2) :: (1, 1) :: repeat (1, 2) 103 ++ (471, 2) :: (1, 1) :: repeat (1, 2) 956 ++ (6780, 2) :: (1, 1) :: repeat (1, 2) 20403 ++ (54789, 2) :: (1, 1) :: repeat (1, 2) 134248 ++ w) 1); closearith.
  }
  (* step 124: P PUSHX *)
  apply (hsteps_trans _ (HB [] 1 1 7 (repeat (1, 2) 3 ++ (2, 2) :: (38, 2) :: (1, 1) :: repeat (1, 2) 103 ++ (471, 2) :: (1, 1) :: repeat (1, 2) 956 ++ (6780, 2) :: (1, 1) :: repeat (1, 2) 20403 ++ (54789, 2) :: (1, 1) :: repeat (1, 2) 134248 ++ w) 1)).
  {
    apply (hsteps_step _ (HB [] 1 1 7 (repeat (1, 2) 3 ++ (2, 2) :: (38, 2) :: (1, 1) :: repeat (1, 2) 103 ++ (471, 2) :: (1, 1) :: repeat (1, 2) 956 ++ (6780, 2) :: (1, 1) :: repeat (1, 2) 20403 ++ (54789, 2) :: (1, 1) :: repeat (1, 2) 134248 ++ w) 1)); [apply hPUSHX | apply hsteps_refl].
  }
  (* step 125: M pop12 (3,) *)
  apply (hsteps_trans _ (HB [] 4 1 13 ((2, 2) :: (38, 2) :: (1, 1) :: repeat (1, 2) 103 ++ (471, 2) :: (1, 1) :: repeat (1, 2) 956 ++ (6780, 2) :: (1, 1) :: repeat (1, 2) 20403 ++ (54789, 2) :: (1, 1) :: repeat (1, 2) 134248 ++ w) 1)).
  {
    apply (pop12 3 [] 1 7 ((2, 2) :: (38, 2) :: (1, 1) :: repeat (1, 2) 103 ++ (471, 2) :: (1, 1) :: repeat (1, 2) 956 ++ (6780, 2) :: (1, 1) :: repeat (1, 2) 20403 ++ (54789, 2) :: (1, 1) :: repeat (1, 2) 134248 ++ w) 1); closearith.
  }
  (* step 126: P TUP2_1 *)
  apply (hsteps_trans _ (HC [5] 13 1 2 ((36, 2) :: (1, 1) :: repeat (1, 2) 103 ++ (471, 2) :: (1, 1) :: repeat (1, 2) 956 ++ (6780, 2) :: (1, 1) :: repeat (1, 2) 20403 ++ (54789, 2) :: (1, 1) :: repeat (1, 2) 134248 ++ w) 1)).
  {
    replace ((36, 2) :: (1, 1) :: repeat (1, 2) 103 ++ (471, 2) :: (1, 1) :: repeat (1, 2) 956 ++ (6780, 2) :: (1, 1) :: repeat (1, 2) 20403 ++ (54789, 2) :: (1, 1) :: repeat (1, 2) 134248 ++ w) with ((38 - 2, 2) :: (1, 1) :: repeat (1, 2) 103 ++ (471, 2) :: (1, 1) :: repeat (1, 2) 956 ++ (6780, 2) :: (1, 1) :: repeat (1, 2) 20403 ++ (54789, 2) :: (1, 1) :: repeat (1, 2) 134248 ++ w) by sec_eq.
    apply (sTUP2_1 [] 4 12 38 ((1, 1) :: repeat (1, 2) 103 ++ (471, 2) :: (1, 1) :: repeat (1, 2) 956 ++ (6780, 2) :: (1, 1) :: repeat (1, 2) 20403 ++ (54789, 2) :: (1, 1) :: repeat (1, 2) 134248 ++ w) 1); closearith.
  }
  (* step 127: P TDN *)
  apply (hsteps_trans _ (HB [5] 13 1 4 ((36, 2) :: (1, 1) :: repeat (1, 2) 103 ++ (471, 2) :: (1, 1) :: repeat (1, 2) 956 ++ (6780, 2) :: (1, 1) :: repeat (1, 2) 20403 ++ (54789, 2) :: (1, 1) :: repeat (1, 2) 134248 ++ w) 1)).
  {
    apply (sTDN [5] 13 ((36, 2) :: (1, 1) :: repeat (1, 2) 103 ++ (471, 2) :: (1, 1) :: repeat (1, 2) 956 ++ (6780, 2) :: (1, 1) :: repeat (1, 2) 20403 ++ (54789, 2) :: (1, 1) :: repeat (1, 2) 134248 ++ w) 1).
  }
  (* step 128: sTUP *)
  apply (hsteps_trans _ (HC [5] 13 3 2 ((34, 2) :: (1, 1) :: repeat (1, 2) 103 ++ (471, 2) :: (1, 1) :: repeat (1, 2) 956 ++ (6780, 2) :: (1, 1) :: repeat (1, 2) 20403 ++ (54789, 2) :: (1, 1) :: repeat (1, 2) 134248 ++ w) 1)).
  {
    replace ((34, 2) :: (1, 1) :: repeat (1, 2) 103 ++ (471, 2) :: (1, 1) :: repeat (1, 2) 956 ++ (6780, 2) :: (1, 1) :: repeat (1, 2) 20403 ++ (54789, 2) :: (1, 1) :: repeat (1, 2) 134248 ++ w) with ((36 - 2, 2) :: (1, 1) :: repeat (1, 2) 103 ++ (471, 2) :: (1, 1) :: repeat (1, 2) 956 ++ (6780, 2) :: (1, 1) :: repeat (1, 2) 20403 ++ (54789, 2) :: (1, 1) :: repeat (1, 2) 134248 ++ w) by sec_eq.
    apply (sTUP [5] 13 4 36 2 ((1, 1) :: repeat (1, 2) 103 ++ (471, 2) :: (1, 1) :: repeat (1, 2) 956 ++ (6780, 2) :: (1, 1) :: repeat (1, 2) 20403 ++ (54789, 2) :: (1, 1) :: repeat (1, 2) 134248 ++ w) 1); closearith.
  }
  (* step 129: DIPGRIND 13 8 *)
  apply (hsteps_trans _ (HC [5] 0 3 2 (repeat (1, 2) 13 ++ (8, 2) :: (1, 1) :: repeat (1, 2) 103 ++ (471, 2) :: (1, 1) :: repeat (1, 2) 956 ++ (6780, 2) :: (1, 1) :: repeat (1, 2) 20403 ++ (54789, 2) :: (1, 1) :: repeat (1, 2) 134248 ++ w) 1)).
  {
    apply (DIPGRIND 13 8 [5] ((1, 1) :: repeat (1, 2) 103 ++ (471, 2) :: (1, 1) :: repeat (1, 2) 956 ++ (6780, 2) :: (1, 1) :: repeat (1, 2) 20403 ++ (54789, 2) :: (1, 1) :: repeat (1, 2) 134248 ++ w) 1); closearith.
  }
  (* step 130: P PX2Bgen *)
  apply (hsteps_trans _ (HB [0] 3 1 2 (repeat (1, 2) 1 ++ (1, 1) :: repeat (1, 2) 15 ++ (8, 2) :: (1, 1) :: repeat (1, 2) 103 ++ (471, 2) :: (1, 1) :: repeat (1, 2) 956 ++ (6780, 2) :: (1, 1) :: repeat (1, 2) 20403 ++ (54789, 2) :: (1, 1) :: repeat (1, 2) 134248 ++ w) 1)).
  {
    apply (hsteps_step _ (HB [0] 3 1 2 (repeat (1, 2) 1 ++ (1, 1) :: repeat (1, 2) 15 ++ (8, 2) :: (1, 1) :: repeat (1, 2) 103 ++ (471, 2) :: (1, 1) :: repeat (1, 2) 956 ++ (6780, 2) :: (1, 1) :: repeat (1, 2) 20403 ++ (54789, 2) :: (1, 1) :: repeat (1, 2) 134248 ++ w) 1)); [apply hPX2Bgen | apply hsteps_refl].
  }
  (* step 131: M pop12 (1,) *)
  apply (hsteps_trans _ (HB [0] 4 1 4 ((1, 1) :: repeat (1, 2) 15 ++ (8, 2) :: (1, 1) :: repeat (1, 2) 103 ++ (471, 2) :: (1, 1) :: repeat (1, 2) 956 ++ (6780, 2) :: (1, 1) :: repeat (1, 2) 20403 ++ (54789, 2) :: (1, 1) :: repeat (1, 2) 134248 ++ w) 1)).
  {
    apply (pop12 1 [0] 3 2 ((1, 1) :: repeat (1, 2) 15 ++ (8, 2) :: (1, 1) :: repeat (1, 2) 103 ++ (471, 2) :: (1, 1) :: repeat (1, 2) 956 ++ (6780, 2) :: (1, 1) :: repeat (1, 2) 20403 ++ (54789, 2) :: (1, 1) :: repeat (1, 2) 134248 ++ w) 1); closearith.
  }
  (* step 132: P POP *)
  apply (hsteps_trans _ (HB [0] 5 1 5 (repeat (1, 2) 15 ++ (8, 2) :: (1, 1) :: repeat (1, 2) 103 ++ (471, 2) :: (1, 1) :: repeat (1, 2) 956 ++ (6780, 2) :: (1, 1) :: repeat (1, 2) 20403 ++ (54789, 2) :: (1, 1) :: repeat (1, 2) 134248 ++ w) 1)).
  {
    apply (sPOP1 [0] 4 4 (repeat (1, 2) 15 ++ (8, 2) :: (1, 1) :: repeat (1, 2) 103 ++ (471, 2) :: (1, 1) :: repeat (1, 2) 956 ++ (6780, 2) :: (1, 1) :: repeat (1, 2) 20403 ++ (54789, 2) :: (1, 1) :: repeat (1, 2) 134248 ++ w) 1); closearith.
  }
  (* step 133: M pop12 (15,) *)
  apply (hsteps_trans _ (HB [0] 20 1 35 ((8, 2) :: (1, 1) :: repeat (1, 2) 103 ++ (471, 2) :: (1, 1) :: repeat (1, 2) 956 ++ (6780, 2) :: (1, 1) :: repeat (1, 2) 20403 ++ (54789, 2) :: (1, 1) :: repeat (1, 2) 134248 ++ w) 1)).
  {
    apply (pop12 15 [0] 5 5 ((8, 2) :: (1, 1) :: repeat (1, 2) 103 ++ (471, 2) :: (1, 1) :: repeat (1, 2) 956 ++ (6780, 2) :: (1, 1) :: repeat (1, 2) 20403 ++ (54789, 2) :: (1, 1) :: repeat (1, 2) 134248 ++ w) 1); closearith.
  }
  (* step 134: sTUP *)
  apply (hsteps_trans _ (HC [0] 20 34 2 ((6, 2) :: (1, 1) :: repeat (1, 2) 103 ++ (471, 2) :: (1, 1) :: repeat (1, 2) 956 ++ (6780, 2) :: (1, 1) :: repeat (1, 2) 20403 ++ (54789, 2) :: (1, 1) :: repeat (1, 2) 134248 ++ w) 1)).
  {
    replace ((6, 2) :: (1, 1) :: repeat (1, 2) 103 ++ (471, 2) :: (1, 1) :: repeat (1, 2) 956 ++ (6780, 2) :: (1, 1) :: repeat (1, 2) 20403 ++ (54789, 2) :: (1, 1) :: repeat (1, 2) 134248 ++ w) with ((8 - 2, 2) :: (1, 1) :: repeat (1, 2) 103 ++ (471, 2) :: (1, 1) :: repeat (1, 2) 956 ++ (6780, 2) :: (1, 1) :: repeat (1, 2) 20403 ++ (54789, 2) :: (1, 1) :: repeat (1, 2) 134248 ++ w) by sec_eq.
    apply (sTUP [0] 20 35 8 2 ((1, 1) :: repeat (1, 2) 103 ++ (471, 2) :: (1, 1) :: repeat (1, 2) 956 ++ (6780, 2) :: (1, 1) :: repeat (1, 2) 20403 ++ (54789, 2) :: (1, 1) :: repeat (1, 2) 134248 ++ w) 1); closearith.
  }
  (* step 135: hGRIND_even 15 *)
  apply (hsteps_trans _ (HB [0] 19 1 34 ((2, 2) :: (6, 2) :: (1, 1) :: repeat (1, 2) 103 ++ (471, 2) :: (1, 1) :: repeat (1, 2) 956 ++ (6780, 2) :: (1, 1) :: repeat (1, 2) 20403 ++ (54789, 2) :: (1, 1) :: repeat (1, 2) 134248 ++ w) 1)).
  {
    apply (hGRIND_even 15 [0] 19 ((6, 2) :: (1, 1) :: repeat (1, 2) 103 ++ (471, 2) :: (1, 1) :: repeat (1, 2) 956 ++ (6780, 2) :: (1, 1) :: repeat (1, 2) 20403 ++ (54789, 2) :: (1, 1) :: repeat (1, 2) 134248 ++ w) 1); closearith.
  }
  (* step 136: P TUP2_1 *)
  apply (hsteps_trans _ (HC [20; 0] 34 1 2 ((4, 2) :: (1, 1) :: repeat (1, 2) 103 ++ (471, 2) :: (1, 1) :: repeat (1, 2) 956 ++ (6780, 2) :: (1, 1) :: repeat (1, 2) 20403 ++ (54789, 2) :: (1, 1) :: repeat (1, 2) 134248 ++ w) 1)).
  {
    replace ((4, 2) :: (1, 1) :: repeat (1, 2) 103 ++ (471, 2) :: (1, 1) :: repeat (1, 2) 956 ++ (6780, 2) :: (1, 1) :: repeat (1, 2) 20403 ++ (54789, 2) :: (1, 1) :: repeat (1, 2) 134248 ++ w) with ((6 - 2, 2) :: (1, 1) :: repeat (1, 2) 103 ++ (471, 2) :: (1, 1) :: repeat (1, 2) 956 ++ (6780, 2) :: (1, 1) :: repeat (1, 2) 20403 ++ (54789, 2) :: (1, 1) :: repeat (1, 2) 134248 ++ w) by sec_eq.
    apply (sTUP2_1 [0] 19 33 6 ((1, 1) :: repeat (1, 2) 103 ++ (471, 2) :: (1, 1) :: repeat (1, 2) 956 ++ (6780, 2) :: (1, 1) :: repeat (1, 2) 20403 ++ (54789, 2) :: (1, 1) :: repeat (1, 2) 134248 ++ w) 1); closearith.
  }
  (* step 137: P TDN *)
  apply (hsteps_trans _ (HB [20; 0] 34 1 4 ((4, 2) :: (1, 1) :: repeat (1, 2) 103 ++ (471, 2) :: (1, 1) :: repeat (1, 2) 956 ++ (6780, 2) :: (1, 1) :: repeat (1, 2) 20403 ++ (54789, 2) :: (1, 1) :: repeat (1, 2) 134248 ++ w) 1)).
  {
    apply (sTDN [20; 0] 34 ((4, 2) :: (1, 1) :: repeat (1, 2) 103 ++ (471, 2) :: (1, 1) :: repeat (1, 2) 956 ++ (6780, 2) :: (1, 1) :: repeat (1, 2) 20403 ++ (54789, 2) :: (1, 1) :: repeat (1, 2) 134248 ++ w) 1).
  }
  (* step 138: sTUP *)
  apply (hsteps_trans _ (HC [20; 0] 34 3 2 ((2, 2) :: (1, 1) :: repeat (1, 2) 103 ++ (471, 2) :: (1, 1) :: repeat (1, 2) 956 ++ (6780, 2) :: (1, 1) :: repeat (1, 2) 20403 ++ (54789, 2) :: (1, 1) :: repeat (1, 2) 134248 ++ w) 1)).
  {
    replace ((2, 2) :: (1, 1) :: repeat (1, 2) 103 ++ (471, 2) :: (1, 1) :: repeat (1, 2) 956 ++ (6780, 2) :: (1, 1) :: repeat (1, 2) 20403 ++ (54789, 2) :: (1, 1) :: repeat (1, 2) 134248 ++ w) with ((4 - 2, 2) :: (1, 1) :: repeat (1, 2) 103 ++ (471, 2) :: (1, 1) :: repeat (1, 2) 956 ++ (6780, 2) :: (1, 1) :: repeat (1, 2) 20403 ++ (54789, 2) :: (1, 1) :: repeat (1, 2) 134248 ++ w) by sec_eq.
    apply (sTUP [20; 0] 34 4 4 2 ((1, 1) :: repeat (1, 2) 103 ++ (471, 2) :: (1, 1) :: repeat (1, 2) 956 ++ (6780, 2) :: (1, 1) :: repeat (1, 2) 20403 ++ (54789, 2) :: (1, 1) :: repeat (1, 2) 134248 ++ w) 1); closearith.
  }
  (* step 139: hGRIND 0 *)
  apply (hsteps_trans _ (HB [20; 0] 34 1 6 ((2, 2) :: (1, 1) :: repeat (1, 2) 103 ++ (471, 2) :: (1, 1) :: repeat (1, 2) 956 ++ (6780, 2) :: (1, 1) :: repeat (1, 2) 20403 ++ (54789, 2) :: (1, 1) :: repeat (1, 2) 134248 ++ w) 1)).
  {
    apply (hGRIND 0 [20; 0] 34 ((2, 2) :: (1, 1) :: repeat (1, 2) 103 ++ (471, 2) :: (1, 1) :: repeat (1, 2) 956 ++ (6780, 2) :: (1, 1) :: repeat (1, 2) 20403 ++ (54789, 2) :: (1, 1) :: repeat (1, 2) 134248 ++ w) 1); closearith.
  }
  (* step 140: P TRANS2_1 *)
  apply (hsteps_trans _ (HB [35; 20; 0] 7 1 3 (repeat (1, 2) 103 ++ (471, 2) :: (1, 1) :: repeat (1, 2) 956 ++ (6780, 2) :: (1, 1) :: repeat (1, 2) 20403 ++ (54789, 2) :: (1, 1) :: repeat (1, 2) 134248 ++ w) 1)).
  {
    apply (sTRANS2_1 [20; 0] 34 5 1 (repeat (1, 2) 103 ++ (471, 2) :: (1, 1) :: repeat (1, 2) 956 ++ (6780, 2) :: (1, 1) :: repeat (1, 2) 20403 ++ (54789, 2) :: (1, 1) :: repeat (1, 2) 134248 ++ w) 1); closearith.
  }
  (* step 141: M pop12 (103,) *)
  apply (hsteps_trans _ (HB [35; 20; 0] 110 1 209 ((471, 2) :: (1, 1) :: repeat (1, 2) 956 ++ (6780, 2) :: (1, 1) :: repeat (1, 2) 20403 ++ (54789, 2) :: (1, 1) :: repeat (1, 2) 134248 ++ w) 1)).
  {
    apply (pop12 103 [35; 20; 0] 7 3 ((471, 2) :: (1, 1) :: repeat (1, 2) 956 ++ (6780, 2) :: (1, 1) :: repeat (1, 2) 20403 ++ (54789, 2) :: (1, 1) :: repeat (1, 2) 134248 ++ w) 1); closearith.
  }
  (* step 142: sTUP *)
  apply (hsteps_trans _ (HC [35; 20; 0] 110 208 2 ((469, 2) :: (1, 1) :: repeat (1, 2) 956 ++ (6780, 2) :: (1, 1) :: repeat (1, 2) 20403 ++ (54789, 2) :: (1, 1) :: repeat (1, 2) 134248 ++ w) 1)).
  {
    replace ((469, 2) :: (1, 1) :: repeat (1, 2) 956 ++ (6780, 2) :: (1, 1) :: repeat (1, 2) 20403 ++ (54789, 2) :: (1, 1) :: repeat (1, 2) 134248 ++ w) with ((471 - 2, 2) :: (1, 1) :: repeat (1, 2) 956 ++ (6780, 2) :: (1, 1) :: repeat (1, 2) 20403 ++ (54789, 2) :: (1, 1) :: repeat (1, 2) 134248 ++ w) by sec_eq.
    apply (sTUP [35; 20; 0] 110 209 471 2 ((1, 1) :: repeat (1, 2) 956 ++ (6780, 2) :: (1, 1) :: repeat (1, 2) 20403 ++ (54789, 2) :: (1, 1) :: repeat (1, 2) 134248 ++ w) 1); closearith.
  }
  (* step 143: hGRIND_even 102 *)
  apply (hsteps_trans _ (HB [35; 20; 0] 109 1 208 ((2, 2) :: (469, 2) :: (1, 1) :: repeat (1, 2) 956 ++ (6780, 2) :: (1, 1) :: repeat (1, 2) 20403 ++ (54789, 2) :: (1, 1) :: repeat (1, 2) 134248 ++ w) 1)).
  {
    apply (hGRIND_even 102 [35; 20; 0] 109 ((469, 2) :: (1, 1) :: repeat (1, 2) 956 ++ (6780, 2) :: (1, 1) :: repeat (1, 2) 20403 ++ (54789, 2) :: (1, 1) :: repeat (1, 2) 134248 ++ w) 1); closearith.
  }
  (* step 144: P TUP2_1 *)
  apply (hsteps_trans _ (HC [110; 35; 20; 0] 208 1 2 ((467, 2) :: (1, 1) :: repeat (1, 2) 956 ++ (6780, 2) :: (1, 1) :: repeat (1, 2) 20403 ++ (54789, 2) :: (1, 1) :: repeat (1, 2) 134248 ++ w) 1)).
  {
    replace ((467, 2) :: (1, 1) :: repeat (1, 2) 956 ++ (6780, 2) :: (1, 1) :: repeat (1, 2) 20403 ++ (54789, 2) :: (1, 1) :: repeat (1, 2) 134248 ++ w) with ((469 - 2, 2) :: (1, 1) :: repeat (1, 2) 956 ++ (6780, 2) :: (1, 1) :: repeat (1, 2) 20403 ++ (54789, 2) :: (1, 1) :: repeat (1, 2) 134248 ++ w) by sec_eq.
    apply (sTUP2_1 [35; 20; 0] 109 207 469 ((1, 1) :: repeat (1, 2) 956 ++ (6780, 2) :: (1, 1) :: repeat (1, 2) 20403 ++ (54789, 2) :: (1, 1) :: repeat (1, 2) 134248 ++ w) 1); closearith.
  }
  (* step 145: P TDN *)
  apply (hsteps_trans _ (HB [110; 35; 20; 0] 208 1 4 ((467, 2) :: (1, 1) :: repeat (1, 2) 956 ++ (6780, 2) :: (1, 1) :: repeat (1, 2) 20403 ++ (54789, 2) :: (1, 1) :: repeat (1, 2) 134248 ++ w) 1)).
  {
    apply (sTDN [110; 35; 20; 0] 208 ((467, 2) :: (1, 1) :: repeat (1, 2) 956 ++ (6780, 2) :: (1, 1) :: repeat (1, 2) 20403 ++ (54789, 2) :: (1, 1) :: repeat (1, 2) 134248 ++ w) 1).
  }
  (* step 146: sTUP *)
  apply (hsteps_trans _ (HC [110; 35; 20; 0] 208 3 2 ((465, 2) :: (1, 1) :: repeat (1, 2) 956 ++ (6780, 2) :: (1, 1) :: repeat (1, 2) 20403 ++ (54789, 2) :: (1, 1) :: repeat (1, 2) 134248 ++ w) 1)).
  {
    replace ((465, 2) :: (1, 1) :: repeat (1, 2) 956 ++ (6780, 2) :: (1, 1) :: repeat (1, 2) 20403 ++ (54789, 2) :: (1, 1) :: repeat (1, 2) 134248 ++ w) with ((467 - 2, 2) :: (1, 1) :: repeat (1, 2) 956 ++ (6780, 2) :: (1, 1) :: repeat (1, 2) 20403 ++ (54789, 2) :: (1, 1) :: repeat (1, 2) 134248 ++ w) by sec_eq.
    apply (sTUP [110; 35; 20; 0] 208 4 467 2 ((1, 1) :: repeat (1, 2) 956 ++ (6780, 2) :: (1, 1) :: repeat (1, 2) 20403 ++ (54789, 2) :: (1, 1) :: repeat (1, 2) 134248 ++ w) 1); closearith.
  }
  (* step 147: DIPGRIND 208 49 *)
  apply (hsteps_trans _ (HC [110; 35; 20; 0] 0 3 2 (repeat (1, 2) 208 ++ (49, 2) :: (1, 1) :: repeat (1, 2) 956 ++ (6780, 2) :: (1, 1) :: repeat (1, 2) 20403 ++ (54789, 2) :: (1, 1) :: repeat (1, 2) 134248 ++ w) 1)).
  {
    apply (DIPGRIND 208 49 [110; 35; 20; 0] ((1, 1) :: repeat (1, 2) 956 ++ (6780, 2) :: (1, 1) :: repeat (1, 2) 20403 ++ (54789, 2) :: (1, 1) :: repeat (1, 2) 134248 ++ w) 1); closearith.
  }
  (* step 148: P PX2A *)
  apply (hsteps_trans _ (HC [20; 0] 34 108 2 ((1, 1) :: repeat (1, 2) 210 ++ (49, 2) :: (1, 1) :: repeat (1, 2) 956 ++ (6780, 2) :: (1, 1) :: repeat (1, 2) 20403 ++ (54789, 2) :: (1, 1) :: repeat (1, 2) 134248 ++ w) 1)).
  {
    apply (hsteps_step _ (HC [20; 0] 34 108 2 ((1, 1) :: repeat (1, 2) 210 ++ (49, 2) :: (1, 1) :: repeat (1, 2) 956 ++ (6780, 2) :: (1, 1) :: repeat (1, 2) 20403 ++ (54789, 2) :: (1, 1) :: repeat (1, 2) 134248 ++ w) 1)); [apply hPX2A | apply hsteps_refl].
  }
  (* step 149: P PUSH *)
  apply (hsteps_trans _ (HC [20; 0] 33 1 2 ((106, 2) :: (1, 1) :: repeat (1, 2) 210 ++ (49, 2) :: (1, 1) :: repeat (1, 2) 956 ++ (6780, 2) :: (1, 1) :: repeat (1, 2) 20403 ++ (54789, 2) :: (1, 1) :: repeat (1, 2) 134248 ++ w) 1)).
  {
    replace ((106, 2) :: (1, 1) :: repeat (1, 2) 210 ++ (49, 2) :: (1, 1) :: repeat (1, 2) 956 ++ (6780, 2) :: (1, 1) :: repeat (1, 2) 20403 ++ (54789, 2) :: (1, 1) :: repeat (1, 2) 134248 ++ w) with ((108 - 2, 2) :: (1, 1) :: repeat (1, 2) 210 ++ (49, 2) :: (1, 1) :: repeat (1, 2) 956 ++ (6780, 2) :: (1, 1) :: repeat (1, 2) 20403 ++ (54789, 2) :: (1, 1) :: repeat (1, 2) 134248 ++ w) by sec_eq.
    apply (sPUSH [20; 0] 33 108 ((1, 1) :: repeat (1, 2) 210 ++ (49, 2) :: (1, 1) :: repeat (1, 2) 956 ++ (6780, 2) :: (1, 1) :: repeat (1, 2) 20403 ++ (54789, 2) :: (1, 1) :: repeat (1, 2) 134248 ++ w) 1); closearith.
  }
  (* step 150: P TDN *)
  apply (hsteps_trans _ (HB [20; 0] 33 1 4 ((106, 2) :: (1, 1) :: repeat (1, 2) 210 ++ (49, 2) :: (1, 1) :: repeat (1, 2) 956 ++ (6780, 2) :: (1, 1) :: repeat (1, 2) 20403 ++ (54789, 2) :: (1, 1) :: repeat (1, 2) 134248 ++ w) 1)).
  {
    apply (sTDN [20; 0] 33 ((106, 2) :: (1, 1) :: repeat (1, 2) 210 ++ (49, 2) :: (1, 1) :: repeat (1, 2) 956 ++ (6780, 2) :: (1, 1) :: repeat (1, 2) 20403 ++ (54789, 2) :: (1, 1) :: repeat (1, 2) 134248 ++ w) 1).
  }
  (* step 151: sTUP *)
  apply (hsteps_trans _ (HC [20; 0] 33 3 2 ((104, 2) :: (1, 1) :: repeat (1, 2) 210 ++ (49, 2) :: (1, 1) :: repeat (1, 2) 956 ++ (6780, 2) :: (1, 1) :: repeat (1, 2) 20403 ++ (54789, 2) :: (1, 1) :: repeat (1, 2) 134248 ++ w) 1)).
  {
    replace ((104, 2) :: (1, 1) :: repeat (1, 2) 210 ++ (49, 2) :: (1, 1) :: repeat (1, 2) 956 ++ (6780, 2) :: (1, 1) :: repeat (1, 2) 20403 ++ (54789, 2) :: (1, 1) :: repeat (1, 2) 134248 ++ w) with ((106 - 2, 2) :: (1, 1) :: repeat (1, 2) 210 ++ (49, 2) :: (1, 1) :: repeat (1, 2) 956 ++ (6780, 2) :: (1, 1) :: repeat (1, 2) 20403 ++ (54789, 2) :: (1, 1) :: repeat (1, 2) 134248 ++ w) by sec_eq.
    apply (sTUP [20; 0] 33 4 106 2 ((1, 1) :: repeat (1, 2) 210 ++ (49, 2) :: (1, 1) :: repeat (1, 2) 956 ++ (6780, 2) :: (1, 1) :: repeat (1, 2) 20403 ++ (54789, 2) :: (1, 1) :: repeat (1, 2) 134248 ++ w) 1); closearith.
  }
  (* step 152: DIPGRIND 33 38 *)
    apply (DIPGRIND 33 38 [20; 0] ((1, 1) :: repeat (1, 2) 210 ++ (49, 2) :: (1, 1) :: repeat (1, 2) 956 ++ (6780, 2) :: (1, 1) :: repeat (1, 2) 20403 ++ (54789, 2) :: (1, 1) :: repeat (1, 2) 134248 ++ w) 1); closearith.
Qed.

(* CASCADE52c: steps 153-226 of the CASCADE52 chain. *)
Lemma CASCADE52c : forall w,
  hsteps (HC [20; 0] 0 3 2 (repeat (1, 2) 33 ++ (38, 2) :: (1, 1) :: repeat (1, 2) 210 ++ (49, 2) :: (1, 1) :: repeat (1, 2) 956 ++ (6780, 2) :: (1, 1) :: repeat (1, 2) 20403 ++ (54789, 2) :: (1, 1) :: repeat (1, 2) 134248 ++ w) 1)
         (HB [23252; 3931; 2847; 569; 287; 14; 5] 40810 1 54791 (repeat (1, 2) 134248 ++ w) 1).
Proof.
  intro w.
  (* step 153: P PX2A0 *)
  apply (hsteps_trans _ (HB [0] 3 1 2 ((16, 2) :: (1, 1) :: repeat (1, 2) 35 ++ (38, 2) :: (1, 1) :: repeat (1, 2) 210 ++ (49, 2) :: (1, 1) :: repeat (1, 2) 956 ++ (6780, 2) :: (1, 1) :: repeat (1, 2) 20403 ++ (54789, 2) :: (1, 1) :: repeat (1, 2) 134248 ++ w) 1)).
  {
    apply (hsteps_step _ (HB [0] 3 1 2 ((16, 2) :: (1, 1) :: repeat (1, 2) 35 ++ (38, 2) :: (1, 1) :: repeat (1, 2) 210 ++ (49, 2) :: (1, 1) :: repeat (1, 2) 956 ++ (6780, 2) :: (1, 1) :: repeat (1, 2) 20403 ++ (54789, 2) :: (1, 1) :: repeat (1, 2) 134248 ++ w) 1)); [apply hPX2A0 | apply hsteps_refl].
  }
  (* step 154: sTUP *)
  apply (hsteps_trans _ (HC [0] 3 1 2 ((14, 2) :: (1, 1) :: repeat (1, 2) 35 ++ (38, 2) :: (1, 1) :: repeat (1, 2) 210 ++ (49, 2) :: (1, 1) :: repeat (1, 2) 956 ++ (6780, 2) :: (1, 1) :: repeat (1, 2) 20403 ++ (54789, 2) :: (1, 1) :: repeat (1, 2) 134248 ++ w) 1)).
  {
    replace ((14, 2) :: (1, 1) :: repeat (1, 2) 35 ++ (38, 2) :: (1, 1) :: repeat (1, 2) 210 ++ (49, 2) :: (1, 1) :: repeat (1, 2) 956 ++ (6780, 2) :: (1, 1) :: repeat (1, 2) 20403 ++ (54789, 2) :: (1, 1) :: repeat (1, 2) 134248 ++ w) with ((16 - 2, 2) :: (1, 1) :: repeat (1, 2) 35 ++ (38, 2) :: (1, 1) :: repeat (1, 2) 210 ++ (49, 2) :: (1, 1) :: repeat (1, 2) 956 ++ (6780, 2) :: (1, 1) :: repeat (1, 2) 20403 ++ (54789, 2) :: (1, 1) :: repeat (1, 2) 134248 ++ w) by sec_eq.
    apply (sTUP [0] 3 2 16 2 ((1, 1) :: repeat (1, 2) 35 ++ (38, 2) :: (1, 1) :: repeat (1, 2) 210 ++ (49, 2) :: (1, 1) :: repeat (1, 2) 956 ++ (6780, 2) :: (1, 1) :: repeat (1, 2) 20403 ++ (54789, 2) :: (1, 1) :: repeat (1, 2) 134248 ++ w) 1); closearith.
  }
  (* step 155: P TDN *)
  apply (hsteps_trans _ (HB [0] 3 1 4 ((14, 2) :: (1, 1) :: repeat (1, 2) 35 ++ (38, 2) :: (1, 1) :: repeat (1, 2) 210 ++ (49, 2) :: (1, 1) :: repeat (1, 2) 956 ++ (6780, 2) :: (1, 1) :: repeat (1, 2) 20403 ++ (54789, 2) :: (1, 1) :: repeat (1, 2) 134248 ++ w) 1)).
  {
    apply (sTDN [0] 3 ((14, 2) :: (1, 1) :: repeat (1, 2) 35 ++ (38, 2) :: (1, 1) :: repeat (1, 2) 210 ++ (49, 2) :: (1, 1) :: repeat (1, 2) 956 ++ (6780, 2) :: (1, 1) :: repeat (1, 2) 20403 ++ (54789, 2) :: (1, 1) :: repeat (1, 2) 134248 ++ w) 1).
  }
  (* step 156: sTUP *)
  apply (hsteps_trans _ (HC [0] 3 3 2 ((12, 2) :: (1, 1) :: repeat (1, 2) 35 ++ (38, 2) :: (1, 1) :: repeat (1, 2) 210 ++ (49, 2) :: (1, 1) :: repeat (1, 2) 956 ++ (6780, 2) :: (1, 1) :: repeat (1, 2) 20403 ++ (54789, 2) :: (1, 1) :: repeat (1, 2) 134248 ++ w) 1)).
  {
    replace ((12, 2) :: (1, 1) :: repeat (1, 2) 35 ++ (38, 2) :: (1, 1) :: repeat (1, 2) 210 ++ (49, 2) :: (1, 1) :: repeat (1, 2) 956 ++ (6780, 2) :: (1, 1) :: repeat (1, 2) 20403 ++ (54789, 2) :: (1, 1) :: repeat (1, 2) 134248 ++ w) with ((14 - 2, 2) :: (1, 1) :: repeat (1, 2) 35 ++ (38, 2) :: (1, 1) :: repeat (1, 2) 210 ++ (49, 2) :: (1, 1) :: repeat (1, 2) 956 ++ (6780, 2) :: (1, 1) :: repeat (1, 2) 20403 ++ (54789, 2) :: (1, 1) :: repeat (1, 2) 134248 ++ w) by sec_eq.
    apply (sTUP [0] 3 4 14 2 ((1, 1) :: repeat (1, 2) 35 ++ (38, 2) :: (1, 1) :: repeat (1, 2) 210 ++ (49, 2) :: (1, 1) :: repeat (1, 2) 956 ++ (6780, 2) :: (1, 1) :: repeat (1, 2) 20403 ++ (54789, 2) :: (1, 1) :: repeat (1, 2) 134248 ++ w) 1); closearith.
  }
  (* step 157: DIPGRIND 3 6 *)
  apply (hsteps_trans _ (HC [0] 0 3 2 (repeat (1, 2) 3 ++ (6, 2) :: (1, 1) :: repeat (1, 2) 35 ++ (38, 2) :: (1, 1) :: repeat (1, 2) 210 ++ (49, 2) :: (1, 1) :: repeat (1, 2) 956 ++ (6780, 2) :: (1, 1) :: repeat (1, 2) 20403 ++ (54789, 2) :: (1, 1) :: repeat (1, 2) 134248 ++ w) 1)).
  {
    apply (DIPGRIND 3 6 [0] ((1, 1) :: repeat (1, 2) 35 ++ (38, 2) :: (1, 1) :: repeat (1, 2) 210 ++ (49, 2) :: (1, 1) :: repeat (1, 2) 956 ++ (6780, 2) :: (1, 1) :: repeat (1, 2) 20403 ++ (54789, 2) :: (1, 1) :: repeat (1, 2) 134248 ++ w) 1); closearith.
  }
  (* step 158: P PX2B0 *)
  apply (hsteps_trans _ (HB [] 0 1 5 (repeat (1, 2) 4 ++ (6, 2) :: (1, 1) :: repeat (1, 2) 35 ++ (38, 2) :: (1, 1) :: repeat (1, 2) 210 ++ (49, 2) :: (1, 1) :: repeat (1, 2) 956 ++ (6780, 2) :: (1, 1) :: repeat (1, 2) 20403 ++ (54789, 2) :: (1, 1) :: repeat (1, 2) 134248 ++ w) 1)).
  {
    apply (hsteps_step _ (HB [] 0 1 5 (repeat (1, 2) 4 ++ (6, 2) :: (1, 1) :: repeat (1, 2) 35 ++ (38, 2) :: (1, 1) :: repeat (1, 2) 210 ++ (49, 2) :: (1, 1) :: repeat (1, 2) 956 ++ (6780, 2) :: (1, 1) :: repeat (1, 2) 20403 ++ (54789, 2) :: (1, 1) :: repeat (1, 2) 134248 ++ w) 1)); [apply hPX2B0 | apply hsteps_refl].
  }
  (* step 159: M pop12 (4,) *)
  apply (hsteps_trans _ (HB [] 4 1 13 ((6, 2) :: (1, 1) :: repeat (1, 2) 35 ++ (38, 2) :: (1, 1) :: repeat (1, 2) 210 ++ (49, 2) :: (1, 1) :: repeat (1, 2) 956 ++ (6780, 2) :: (1, 1) :: repeat (1, 2) 20403 ++ (54789, 2) :: (1, 1) :: repeat (1, 2) 134248 ++ w) 1)).
  {
    apply (pop12 4 [] 0 5 ((6, 2) :: (1, 1) :: repeat (1, 2) 35 ++ (38, 2) :: (1, 1) :: repeat (1, 2) 210 ++ (49, 2) :: (1, 1) :: repeat (1, 2) 956 ++ (6780, 2) :: (1, 1) :: repeat (1, 2) 20403 ++ (54789, 2) :: (1, 1) :: repeat (1, 2) 134248 ++ w) 1); closearith.
  }
  (* step 160: sTUP *)
  apply (hsteps_trans _ (HC [] 4 12 2 ((4, 2) :: (1, 1) :: repeat (1, 2) 35 ++ (38, 2) :: (1, 1) :: repeat (1, 2) 210 ++ (49, 2) :: (1, 1) :: repeat (1, 2) 956 ++ (6780, 2) :: (1, 1) :: repeat (1, 2) 20403 ++ (54789, 2) :: (1, 1) :: repeat (1, 2) 134248 ++ w) 1)).
  {
    replace ((4, 2) :: (1, 1) :: repeat (1, 2) 35 ++ (38, 2) :: (1, 1) :: repeat (1, 2) 210 ++ (49, 2) :: (1, 1) :: repeat (1, 2) 956 ++ (6780, 2) :: (1, 1) :: repeat (1, 2) 20403 ++ (54789, 2) :: (1, 1) :: repeat (1, 2) 134248 ++ w) with ((6 - 2, 2) :: (1, 1) :: repeat (1, 2) 35 ++ (38, 2) :: (1, 1) :: repeat (1, 2) 210 ++ (49, 2) :: (1, 1) :: repeat (1, 2) 956 ++ (6780, 2) :: (1, 1) :: repeat (1, 2) 20403 ++ (54789, 2) :: (1, 1) :: repeat (1, 2) 134248 ++ w) by sec_eq.
    apply (sTUP [] 4 13 6 2 ((1, 1) :: repeat (1, 2) 35 ++ (38, 2) :: (1, 1) :: repeat (1, 2) 210 ++ (49, 2) :: (1, 1) :: repeat (1, 2) 956 ++ (6780, 2) :: (1, 1) :: repeat (1, 2) 20403 ++ (54789, 2) :: (1, 1) :: repeat (1, 2) 134248 ++ w) 1); closearith.
  }
  (* step 161: P PUSH *)
  apply (hsteps_trans _ (HC [] 3 1 2 ((10, 2) :: (4, 2) :: (1, 1) :: repeat (1, 2) 35 ++ (38, 2) :: (1, 1) :: repeat (1, 2) 210 ++ (49, 2) :: (1, 1) :: repeat (1, 2) 956 ++ (6780, 2) :: (1, 1) :: repeat (1, 2) 20403 ++ (54789, 2) :: (1, 1) :: repeat (1, 2) 134248 ++ w) 1)).
  {
    replace ((10, 2) :: (4, 2) :: (1, 1) :: repeat (1, 2) 35 ++ (38, 2) :: (1, 1) :: repeat (1, 2) 210 ++ (49, 2) :: (1, 1) :: repeat (1, 2) 956 ++ (6780, 2) :: (1, 1) :: repeat (1, 2) 20403 ++ (54789, 2) :: (1, 1) :: repeat (1, 2) 134248 ++ w) with ((12 - 2, 2) :: (4, 2) :: (1, 1) :: repeat (1, 2) 35 ++ (38, 2) :: (1, 1) :: repeat (1, 2) 210 ++ (49, 2) :: (1, 1) :: repeat (1, 2) 956 ++ (6780, 2) :: (1, 1) :: repeat (1, 2) 20403 ++ (54789, 2) :: (1, 1) :: repeat (1, 2) 134248 ++ w) by sec_eq.
    apply (sPUSH [] 3 12 ((4, 2) :: (1, 1) :: repeat (1, 2) 35 ++ (38, 2) :: (1, 1) :: repeat (1, 2) 210 ++ (49, 2) :: (1, 1) :: repeat (1, 2) 956 ++ (6780, 2) :: (1, 1) :: repeat (1, 2) 20403 ++ (54789, 2) :: (1, 1) :: repeat (1, 2) 134248 ++ w) 1); closearith.
  }
  (* step 162: P TDN *)
  apply (hsteps_trans _ (HB [] 3 1 4 ((10, 2) :: (4, 2) :: (1, 1) :: repeat (1, 2) 35 ++ (38, 2) :: (1, 1) :: repeat (1, 2) 210 ++ (49, 2) :: (1, 1) :: repeat (1, 2) 956 ++ (6780, 2) :: (1, 1) :: repeat (1, 2) 20403 ++ (54789, 2) :: (1, 1) :: repeat (1, 2) 134248 ++ w) 1)).
  {
    apply (sTDN [] 3 ((10, 2) :: (4, 2) :: (1, 1) :: repeat (1, 2) 35 ++ (38, 2) :: (1, 1) :: repeat (1, 2) 210 ++ (49, 2) :: (1, 1) :: repeat (1, 2) 956 ++ (6780, 2) :: (1, 1) :: repeat (1, 2) 20403 ++ (54789, 2) :: (1, 1) :: repeat (1, 2) 134248 ++ w) 1).
  }
  (* step 163: sTUP *)
  apply (hsteps_trans _ (HC [] 3 3 2 ((8, 2) :: (4, 2) :: (1, 1) :: repeat (1, 2) 35 ++ (38, 2) :: (1, 1) :: repeat (1, 2) 210 ++ (49, 2) :: (1, 1) :: repeat (1, 2) 956 ++ (6780, 2) :: (1, 1) :: repeat (1, 2) 20403 ++ (54789, 2) :: (1, 1) :: repeat (1, 2) 134248 ++ w) 1)).
  {
    replace ((8, 2) :: (4, 2) :: (1, 1) :: repeat (1, 2) 35 ++ (38, 2) :: (1, 1) :: repeat (1, 2) 210 ++ (49, 2) :: (1, 1) :: repeat (1, 2) 956 ++ (6780, 2) :: (1, 1) :: repeat (1, 2) 20403 ++ (54789, 2) :: (1, 1) :: repeat (1, 2) 134248 ++ w) with ((10 - 2, 2) :: (4, 2) :: (1, 1) :: repeat (1, 2) 35 ++ (38, 2) :: (1, 1) :: repeat (1, 2) 210 ++ (49, 2) :: (1, 1) :: repeat (1, 2) 956 ++ (6780, 2) :: (1, 1) :: repeat (1, 2) 20403 ++ (54789, 2) :: (1, 1) :: repeat (1, 2) 134248 ++ w) by sec_eq.
    apply (sTUP [] 3 4 10 2 ((4, 2) :: (1, 1) :: repeat (1, 2) 35 ++ (38, 2) :: (1, 1) :: repeat (1, 2) 210 ++ (49, 2) :: (1, 1) :: repeat (1, 2) 956 ++ (6780, 2) :: (1, 1) :: repeat (1, 2) 20403 ++ (54789, 2) :: (1, 1) :: repeat (1, 2) 134248 ++ w) 1); closearith.
  }
  (* step 164: DIPGRIND 3 2 *)
  apply (hsteps_trans _ (HC [] 0 3 2 (repeat (1, 2) 3 ++ (2, 2) :: (4, 2) :: (1, 1) :: repeat (1, 2) 35 ++ (38, 2) :: (1, 1) :: repeat (1, 2) 210 ++ (49, 2) :: (1, 1) :: repeat (1, 2) 956 ++ (6780, 2) :: (1, 1) :: repeat (1, 2) 20403 ++ (54789, 2) :: (1, 1) :: repeat (1, 2) 134248 ++ w) 1)).
  {
    apply (DIPGRIND 3 2 [] ((4, 2) :: (1, 1) :: repeat (1, 2) 35 ++ (38, 2) :: (1, 1) :: repeat (1, 2) 210 ++ (49, 2) :: (1, 1) :: repeat (1, 2) 956 ++ (6780, 2) :: (1, 1) :: repeat (1, 2) 20403 ++ (54789, 2) :: (1, 1) :: repeat (1, 2) 134248 ++ w) 1); closearith.
  }
  (* step 165: P PUSHX *)
  apply (hsteps_trans _ (HB [] 1 1 7 (repeat (1, 2) 3 ++ (2, 2) :: (4, 2) :: (1, 1) :: repeat (1, 2) 35 ++ (38, 2) :: (1, 1) :: repeat (1, 2) 210 ++ (49, 2) :: (1, 1) :: repeat (1, 2) 956 ++ (6780, 2) :: (1, 1) :: repeat (1, 2) 20403 ++ (54789, 2) :: (1, 1) :: repeat (1, 2) 134248 ++ w) 1)).
  {
    apply (hsteps_step _ (HB [] 1 1 7 (repeat (1, 2) 3 ++ (2, 2) :: (4, 2) :: (1, 1) :: repeat (1, 2) 35 ++ (38, 2) :: (1, 1) :: repeat (1, 2) 210 ++ (49, 2) :: (1, 1) :: repeat (1, 2) 956 ++ (6780, 2) :: (1, 1) :: repeat (1, 2) 20403 ++ (54789, 2) :: (1, 1) :: repeat (1, 2) 134248 ++ w) 1)); [apply hPUSHX | apply hsteps_refl].
  }
  (* step 166: M pop12 (3,) *)
  apply (hsteps_trans _ (HB [] 4 1 13 ((2, 2) :: (4, 2) :: (1, 1) :: repeat (1, 2) 35 ++ (38, 2) :: (1, 1) :: repeat (1, 2) 210 ++ (49, 2) :: (1, 1) :: repeat (1, 2) 956 ++ (6780, 2) :: (1, 1) :: repeat (1, 2) 20403 ++ (54789, 2) :: (1, 1) :: repeat (1, 2) 134248 ++ w) 1)).
  {
    apply (pop12 3 [] 1 7 ((2, 2) :: (4, 2) :: (1, 1) :: repeat (1, 2) 35 ++ (38, 2) :: (1, 1) :: repeat (1, 2) 210 ++ (49, 2) :: (1, 1) :: repeat (1, 2) 956 ++ (6780, 2) :: (1, 1) :: repeat (1, 2) 20403 ++ (54789, 2) :: (1, 1) :: repeat (1, 2) 134248 ++ w) 1); closearith.
  }
  (* step 167: P TUP2_1 *)
  apply (hsteps_trans _ (HC [5] 13 1 2 ((2, 2) :: (1, 1) :: repeat (1, 2) 35 ++ (38, 2) :: (1, 1) :: repeat (1, 2) 210 ++ (49, 2) :: (1, 1) :: repeat (1, 2) 956 ++ (6780, 2) :: (1, 1) :: repeat (1, 2) 20403 ++ (54789, 2) :: (1, 1) :: repeat (1, 2) 134248 ++ w) 1)).
  {
    replace ((2, 2) :: (1, 1) :: repeat (1, 2) 35 ++ (38, 2) :: (1, 1) :: repeat (1, 2) 210 ++ (49, 2) :: (1, 1) :: repeat (1, 2) 956 ++ (6780, 2) :: (1, 1) :: repeat (1, 2) 20403 ++ (54789, 2) :: (1, 1) :: repeat (1, 2) 134248 ++ w) with ((4 - 2, 2) :: (1, 1) :: repeat (1, 2) 35 ++ (38, 2) :: (1, 1) :: repeat (1, 2) 210 ++ (49, 2) :: (1, 1) :: repeat (1, 2) 956 ++ (6780, 2) :: (1, 1) :: repeat (1, 2) 20403 ++ (54789, 2) :: (1, 1) :: repeat (1, 2) 134248 ++ w) by sec_eq.
    apply (sTUP2_1 [] 4 12 4 ((1, 1) :: repeat (1, 2) 35 ++ (38, 2) :: (1, 1) :: repeat (1, 2) 210 ++ (49, 2) :: (1, 1) :: repeat (1, 2) 956 ++ (6780, 2) :: (1, 1) :: repeat (1, 2) 20403 ++ (54789, 2) :: (1, 1) :: repeat (1, 2) 134248 ++ w) 1); closearith.
  }
  (* step 168: P TDN *)
  apply (hsteps_trans _ (HB [5] 13 1 4 ((2, 2) :: (1, 1) :: repeat (1, 2) 35 ++ (38, 2) :: (1, 1) :: repeat (1, 2) 210 ++ (49, 2) :: (1, 1) :: repeat (1, 2) 956 ++ (6780, 2) :: (1, 1) :: repeat (1, 2) 20403 ++ (54789, 2) :: (1, 1) :: repeat (1, 2) 134248 ++ w) 1)).
  {
    apply (sTDN [5] 13 ((2, 2) :: (1, 1) :: repeat (1, 2) 35 ++ (38, 2) :: (1, 1) :: repeat (1, 2) 210 ++ (49, 2) :: (1, 1) :: repeat (1, 2) 956 ++ (6780, 2) :: (1, 1) :: repeat (1, 2) 20403 ++ (54789, 2) :: (1, 1) :: repeat (1, 2) 134248 ++ w) 1).
  }
  (* step 169: P TRANS2_1 *)
  apply (hsteps_trans _ (HB [14; 5] 5 1 3 (repeat (1, 2) 35 ++ (38, 2) :: (1, 1) :: repeat (1, 2) 210 ++ (49, 2) :: (1, 1) :: repeat (1, 2) 956 ++ (6780, 2) :: (1, 1) :: repeat (1, 2) 20403 ++ (54789, 2) :: (1, 1) :: repeat (1, 2) 134248 ++ w) 1)).
  {
    apply (sTRANS2_1 [5] 13 3 1 (repeat (1, 2) 35 ++ (38, 2) :: (1, 1) :: repeat (1, 2) 210 ++ (49, 2) :: (1, 1) :: repeat (1, 2) 956 ++ (6780, 2) :: (1, 1) :: repeat (1, 2) 20403 ++ (54789, 2) :: (1, 1) :: repeat (1, 2) 134248 ++ w) 1); closearith.
  }
  (* step 170: M pop12 (35,) *)
  apply (hsteps_trans _ (HB [14; 5] 40 1 73 ((38, 2) :: (1, 1) :: repeat (1, 2) 210 ++ (49, 2) :: (1, 1) :: repeat (1, 2) 956 ++ (6780, 2) :: (1, 1) :: repeat (1, 2) 20403 ++ (54789, 2) :: (1, 1) :: repeat (1, 2) 134248 ++ w) 1)).
  {
    apply (pop12 35 [14; 5] 5 3 ((38, 2) :: (1, 1) :: repeat (1, 2) 210 ++ (49, 2) :: (1, 1) :: repeat (1, 2) 956 ++ (6780, 2) :: (1, 1) :: repeat (1, 2) 20403 ++ (54789, 2) :: (1, 1) :: repeat (1, 2) 134248 ++ w) 1); closearith.
  }
  (* step 171: sTUP *)
  apply (hsteps_trans _ (HC [14; 5] 40 72 2 ((36, 2) :: (1, 1) :: repeat (1, 2) 210 ++ (49, 2) :: (1, 1) :: repeat (1, 2) 956 ++ (6780, 2) :: (1, 1) :: repeat (1, 2) 20403 ++ (54789, 2) :: (1, 1) :: repeat (1, 2) 134248 ++ w) 1)).
  {
    replace ((36, 2) :: (1, 1) :: repeat (1, 2) 210 ++ (49, 2) :: (1, 1) :: repeat (1, 2) 956 ++ (6780, 2) :: (1, 1) :: repeat (1, 2) 20403 ++ (54789, 2) :: (1, 1) :: repeat (1, 2) 134248 ++ w) with ((38 - 2, 2) :: (1, 1) :: repeat (1, 2) 210 ++ (49, 2) :: (1, 1) :: repeat (1, 2) 956 ++ (6780, 2) :: (1, 1) :: repeat (1, 2) 20403 ++ (54789, 2) :: (1, 1) :: repeat (1, 2) 134248 ++ w) by sec_eq.
    apply (sTUP [14; 5] 40 73 38 2 ((1, 1) :: repeat (1, 2) 210 ++ (49, 2) :: (1, 1) :: repeat (1, 2) 956 ++ (6780, 2) :: (1, 1) :: repeat (1, 2) 20403 ++ (54789, 2) :: (1, 1) :: repeat (1, 2) 134248 ++ w) 1); closearith.
  }
  (* step 172: hGRIND_even 34 *)
  apply (hsteps_trans _ (HB [14; 5] 39 1 72 ((2, 2) :: (36, 2) :: (1, 1) :: repeat (1, 2) 210 ++ (49, 2) :: (1, 1) :: repeat (1, 2) 956 ++ (6780, 2) :: (1, 1) :: repeat (1, 2) 20403 ++ (54789, 2) :: (1, 1) :: repeat (1, 2) 134248 ++ w) 1)).
  {
    apply (hGRIND_even 34 [14; 5] 39 ((36, 2) :: (1, 1) :: repeat (1, 2) 210 ++ (49, 2) :: (1, 1) :: repeat (1, 2) 956 ++ (6780, 2) :: (1, 1) :: repeat (1, 2) 20403 ++ (54789, 2) :: (1, 1) :: repeat (1, 2) 134248 ++ w) 1); closearith.
  }
  (* step 173: P TUP2_1 *)
  apply (hsteps_trans _ (HC [40; 14; 5] 72 1 2 ((34, 2) :: (1, 1) :: repeat (1, 2) 210 ++ (49, 2) :: (1, 1) :: repeat (1, 2) 956 ++ (6780, 2) :: (1, 1) :: repeat (1, 2) 20403 ++ (54789, 2) :: (1, 1) :: repeat (1, 2) 134248 ++ w) 1)).
  {
    replace ((34, 2) :: (1, 1) :: repeat (1, 2) 210 ++ (49, 2) :: (1, 1) :: repeat (1, 2) 956 ++ (6780, 2) :: (1, 1) :: repeat (1, 2) 20403 ++ (54789, 2) :: (1, 1) :: repeat (1, 2) 134248 ++ w) with ((36 - 2, 2) :: (1, 1) :: repeat (1, 2) 210 ++ (49, 2) :: (1, 1) :: repeat (1, 2) 956 ++ (6780, 2) :: (1, 1) :: repeat (1, 2) 20403 ++ (54789, 2) :: (1, 1) :: repeat (1, 2) 134248 ++ w) by sec_eq.
    apply (sTUP2_1 [14; 5] 39 71 36 ((1, 1) :: repeat (1, 2) 210 ++ (49, 2) :: (1, 1) :: repeat (1, 2) 956 ++ (6780, 2) :: (1, 1) :: repeat (1, 2) 20403 ++ (54789, 2) :: (1, 1) :: repeat (1, 2) 134248 ++ w) 1); closearith.
  }
  (* step 174: P TDN *)
  apply (hsteps_trans _ (HB [40; 14; 5] 72 1 4 ((34, 2) :: (1, 1) :: repeat (1, 2) 210 ++ (49, 2) :: (1, 1) :: repeat (1, 2) 956 ++ (6780, 2) :: (1, 1) :: repeat (1, 2) 20403 ++ (54789, 2) :: (1, 1) :: repeat (1, 2) 134248 ++ w) 1)).
  {
    apply (sTDN [40; 14; 5] 72 ((34, 2) :: (1, 1) :: repeat (1, 2) 210 ++ (49, 2) :: (1, 1) :: repeat (1, 2) 956 ++ (6780, 2) :: (1, 1) :: repeat (1, 2) 20403 ++ (54789, 2) :: (1, 1) :: repeat (1, 2) 134248 ++ w) 1).
  }
  (* step 175: sTUP *)
  apply (hsteps_trans _ (HC [40; 14; 5] 72 3 2 ((32, 2) :: (1, 1) :: repeat (1, 2) 210 ++ (49, 2) :: (1, 1) :: repeat (1, 2) 956 ++ (6780, 2) :: (1, 1) :: repeat (1, 2) 20403 ++ (54789, 2) :: (1, 1) :: repeat (1, 2) 134248 ++ w) 1)).
  {
    replace ((32, 2) :: (1, 1) :: repeat (1, 2) 210 ++ (49, 2) :: (1, 1) :: repeat (1, 2) 956 ++ (6780, 2) :: (1, 1) :: repeat (1, 2) 20403 ++ (54789, 2) :: (1, 1) :: repeat (1, 2) 134248 ++ w) with ((34 - 2, 2) :: (1, 1) :: repeat (1, 2) 210 ++ (49, 2) :: (1, 1) :: repeat (1, 2) 956 ++ (6780, 2) :: (1, 1) :: repeat (1, 2) 20403 ++ (54789, 2) :: (1, 1) :: repeat (1, 2) 134248 ++ w) by sec_eq.
    apply (sTUP [40; 14; 5] 72 4 34 2 ((1, 1) :: repeat (1, 2) 210 ++ (49, 2) :: (1, 1) :: repeat (1, 2) 956 ++ (6780, 2) :: (1, 1) :: repeat (1, 2) 20403 ++ (54789, 2) :: (1, 1) :: repeat (1, 2) 134248 ++ w) 1); closearith.
  }
  (* step 176: CLEANG_even 15 *)
  apply (hsteps_trans _ (HB [40; 14; 5] 72 1 36 ((2, 2) :: (1, 1) :: repeat (1, 2) 210 ++ (49, 2) :: (1, 1) :: repeat (1, 2) 956 ++ (6780, 2) :: (1, 1) :: repeat (1, 2) 20403 ++ (54789, 2) :: (1, 1) :: repeat (1, 2) 134248 ++ w) 1)).
  {
    apply (CLEANG_even 15 [40; 14; 5] 72 ((1, 1) :: repeat (1, 2) 210 ++ (49, 2) :: (1, 1) :: repeat (1, 2) 956 ++ (6780, 2) :: (1, 1) :: repeat (1, 2) 20403 ++ (54789, 2) :: (1, 1) :: repeat (1, 2) 134248 ++ w) 1); closearith.
  }
  (* step 177: P TRANS2_1 *)
  apply (hsteps_trans _ (HB [73; 40; 14; 5] 37 1 3 (repeat (1, 2) 210 ++ (49, 2) :: (1, 1) :: repeat (1, 2) 956 ++ (6780, 2) :: (1, 1) :: repeat (1, 2) 20403 ++ (54789, 2) :: (1, 1) :: repeat (1, 2) 134248 ++ w) 1)).
  {
    apply (sTRANS2_1 [40; 14; 5] 72 35 1 (repeat (1, 2) 210 ++ (49, 2) :: (1, 1) :: repeat (1, 2) 956 ++ (6780, 2) :: (1, 1) :: repeat (1, 2) 20403 ++ (54789, 2) :: (1, 1) :: repeat (1, 2) 134248 ++ w) 1); closearith.
  }
  (* step 178: M pop12 (210,) *)
  apply (hsteps_trans _ (HB [73; 40; 14; 5] 247 1 423 ((49, 2) :: (1, 1) :: repeat (1, 2) 956 ++ (6780, 2) :: (1, 1) :: repeat (1, 2) 20403 ++ (54789, 2) :: (1, 1) :: repeat (1, 2) 134248 ++ w) 1)).
  {
    apply (pop12 210 [73; 40; 14; 5] 37 3 ((49, 2) :: (1, 1) :: repeat (1, 2) 956 ++ (6780, 2) :: (1, 1) :: repeat (1, 2) 20403 ++ (54789, 2) :: (1, 1) :: repeat (1, 2) 134248 ++ w) 1); closearith.
  }
  (* step 179: sTUP *)
  apply (hsteps_trans _ (HC [73; 40; 14; 5] 247 422 2 ((47, 2) :: (1, 1) :: repeat (1, 2) 956 ++ (6780, 2) :: (1, 1) :: repeat (1, 2) 20403 ++ (54789, 2) :: (1, 1) :: repeat (1, 2) 134248 ++ w) 1)).
  {
    replace ((47, 2) :: (1, 1) :: repeat (1, 2) 956 ++ (6780, 2) :: (1, 1) :: repeat (1, 2) 20403 ++ (54789, 2) :: (1, 1) :: repeat (1, 2) 134248 ++ w) with ((49 - 2, 2) :: (1, 1) :: repeat (1, 2) 956 ++ (6780, 2) :: (1, 1) :: repeat (1, 2) 20403 ++ (54789, 2) :: (1, 1) :: repeat (1, 2) 134248 ++ w) by sec_eq.
    apply (sTUP [73; 40; 14; 5] 247 423 49 2 ((1, 1) :: repeat (1, 2) 956 ++ (6780, 2) :: (1, 1) :: repeat (1, 2) 20403 ++ (54789, 2) :: (1, 1) :: repeat (1, 2) 134248 ++ w) 1); closearith.
  }
  (* step 180: hGRIND_even 209 *)
  apply (hsteps_trans _ (HB [73; 40; 14; 5] 246 1 422 ((2, 2) :: (47, 2) :: (1, 1) :: repeat (1, 2) 956 ++ (6780, 2) :: (1, 1) :: repeat (1, 2) 20403 ++ (54789, 2) :: (1, 1) :: repeat (1, 2) 134248 ++ w) 1)).
  {
    apply (hGRIND_even 209 [73; 40; 14; 5] 246 ((47, 2) :: (1, 1) :: repeat (1, 2) 956 ++ (6780, 2) :: (1, 1) :: repeat (1, 2) 20403 ++ (54789, 2) :: (1, 1) :: repeat (1, 2) 134248 ++ w) 1); closearith.
  }
  (* step 181: P TUP2_1 *)
  apply (hsteps_trans _ (HC [247; 73; 40; 14; 5] 422 1 2 ((45, 2) :: (1, 1) :: repeat (1, 2) 956 ++ (6780, 2) :: (1, 1) :: repeat (1, 2) 20403 ++ (54789, 2) :: (1, 1) :: repeat (1, 2) 134248 ++ w) 1)).
  {
    replace ((45, 2) :: (1, 1) :: repeat (1, 2) 956 ++ (6780, 2) :: (1, 1) :: repeat (1, 2) 20403 ++ (54789, 2) :: (1, 1) :: repeat (1, 2) 134248 ++ w) with ((47 - 2, 2) :: (1, 1) :: repeat (1, 2) 956 ++ (6780, 2) :: (1, 1) :: repeat (1, 2) 20403 ++ (54789, 2) :: (1, 1) :: repeat (1, 2) 134248 ++ w) by sec_eq.
    apply (sTUP2_1 [73; 40; 14; 5] 246 421 47 ((1, 1) :: repeat (1, 2) 956 ++ (6780, 2) :: (1, 1) :: repeat (1, 2) 20403 ++ (54789, 2) :: (1, 1) :: repeat (1, 2) 134248 ++ w) 1); closearith.
  }
  (* step 182: P TDN *)
  apply (hsteps_trans _ (HB [247; 73; 40; 14; 5] 422 1 4 ((45, 2) :: (1, 1) :: repeat (1, 2) 956 ++ (6780, 2) :: (1, 1) :: repeat (1, 2) 20403 ++ (54789, 2) :: (1, 1) :: repeat (1, 2) 134248 ++ w) 1)).
  {
    apply (sTDN [247; 73; 40; 14; 5] 422 ((45, 2) :: (1, 1) :: repeat (1, 2) 956 ++ (6780, 2) :: (1, 1) :: repeat (1, 2) 20403 ++ (54789, 2) :: (1, 1) :: repeat (1, 2) 134248 ++ w) 1).
  }
  (* step 183: sTUP *)
  apply (hsteps_trans _ (HC [247; 73; 40; 14; 5] 422 3 2 ((43, 2) :: (1, 1) :: repeat (1, 2) 956 ++ (6780, 2) :: (1, 1) :: repeat (1, 2) 20403 ++ (54789, 2) :: (1, 1) :: repeat (1, 2) 134248 ++ w) 1)).
  {
    replace ((43, 2) :: (1, 1) :: repeat (1, 2) 956 ++ (6780, 2) :: (1, 1) :: repeat (1, 2) 20403 ++ (54789, 2) :: (1, 1) :: repeat (1, 2) 134248 ++ w) with ((45 - 2, 2) :: (1, 1) :: repeat (1, 2) 956 ++ (6780, 2) :: (1, 1) :: repeat (1, 2) 20403 ++ (54789, 2) :: (1, 1) :: repeat (1, 2) 134248 ++ w) by sec_eq.
    apply (sTUP [247; 73; 40; 14; 5] 422 4 45 2 ((1, 1) :: repeat (1, 2) 956 ++ (6780, 2) :: (1, 1) :: repeat (1, 2) 20403 ++ (54789, 2) :: (1, 1) :: repeat (1, 2) 134248 ++ w) 1); closearith.
  }
  (* step 184: CLEANG_odd 20 *)
  apply (hsteps_trans _ (HB [247; 73; 40; 14; 5] 422 1 48 (repeat (1, 2) 1 ++ (1, 1) :: repeat (1, 2) 956 ++ (6780, 2) :: (1, 1) :: repeat (1, 2) 20403 ++ (54789, 2) :: (1, 1) :: repeat (1, 2) 134248 ++ w) 1)).
  {
    replace (repeat (1, 2) 1 ++ (1, 1) :: repeat (1, 2) 956 ++ (6780, 2) :: (1, 1) :: repeat (1, 2) 20403 ++ (54789, 2) :: (1, 1) :: repeat (1, 2) 134248 ++ w) with ((1, 2) :: (1, 1) :: repeat (1, 2) 956 ++ (6780, 2) :: (1, 1) :: repeat (1, 2) 20403 ++ (54789, 2) :: (1, 1) :: repeat (1, 2) 134248 ++ w) by sec_eq.
    apply (CLEANG_odd 20 [247; 73; 40; 14; 5] 422 ((1, 1) :: repeat (1, 2) 956 ++ (6780, 2) :: (1, 1) :: repeat (1, 2) 20403 ++ (54789, 2) :: (1, 1) :: repeat (1, 2) 134248 ++ w) 1); closearith.
  }
  (* step 185: M pop12 (1,) *)
  apply (hsteps_trans _ (HB [247; 73; 40; 14; 5] 423 1 50 ((1, 1) :: repeat (1, 2) 956 ++ (6780, 2) :: (1, 1) :: repeat (1, 2) 20403 ++ (54789, 2) :: (1, 1) :: repeat (1, 2) 134248 ++ w) 1)).
  {
    apply (pop12 1 [247; 73; 40; 14; 5] 422 48 ((1, 1) :: repeat (1, 2) 956 ++ (6780, 2) :: (1, 1) :: repeat (1, 2) 20403 ++ (54789, 2) :: (1, 1) :: repeat (1, 2) 134248 ++ w) 1); closearith.
  }
  (* step 186: P POP *)
  apply (hsteps_trans _ (HB [247; 73; 40; 14; 5] 424 1 51 (repeat (1, 2) 956 ++ (6780, 2) :: (1, 1) :: repeat (1, 2) 20403 ++ (54789, 2) :: (1, 1) :: repeat (1, 2) 134248 ++ w) 1)).
  {
    apply (sPOP1 [247; 73; 40; 14; 5] 423 50 (repeat (1, 2) 956 ++ (6780, 2) :: (1, 1) :: repeat (1, 2) 20403 ++ (54789, 2) :: (1, 1) :: repeat (1, 2) 134248 ++ w) 1); closearith.
  }
  (* step 187: M pop12 (956,) *)
  apply (hsteps_trans _ (HB [247; 73; 40; 14; 5] 1380 1 1963 ((6780, 2) :: (1, 1) :: repeat (1, 2) 20403 ++ (54789, 2) :: (1, 1) :: repeat (1, 2) 134248 ++ w) 1)).
  {
    apply (pop12 956 [247; 73; 40; 14; 5] 424 51 ((6780, 2) :: (1, 1) :: repeat (1, 2) 20403 ++ (54789, 2) :: (1, 1) :: repeat (1, 2) 134248 ++ w) 1); closearith.
  }
  (* step 188: sTUP *)
  apply (hsteps_trans _ (HC [247; 73; 40; 14; 5] 1380 1962 2 ((6778, 2) :: (1, 1) :: repeat (1, 2) 20403 ++ (54789, 2) :: (1, 1) :: repeat (1, 2) 134248 ++ w) 1)).
  {
    replace ((6778, 2) :: (1, 1) :: repeat (1, 2) 20403 ++ (54789, 2) :: (1, 1) :: repeat (1, 2) 134248 ++ w) with ((6780 - 2, 2) :: (1, 1) :: repeat (1, 2) 20403 ++ (54789, 2) :: (1, 1) :: repeat (1, 2) 134248 ++ w) by sec_eq.
    apply (sTUP [247; 73; 40; 14; 5] 1380 1963 6780 2 ((1, 1) :: repeat (1, 2) 20403 ++ (54789, 2) :: (1, 1) :: repeat (1, 2) 134248 ++ w) 1); closearith.
  }
  (* step 189: hGRIND_even 979 *)
  apply (hsteps_trans _ (HB [247; 73; 40; 14; 5] 1379 1 1962 ((2, 2) :: (6778, 2) :: (1, 1) :: repeat (1, 2) 20403 ++ (54789, 2) :: (1, 1) :: repeat (1, 2) 134248 ++ w) 1)).
  {
    apply (hGRIND_even 979 [247; 73; 40; 14; 5] 1379 ((6778, 2) :: (1, 1) :: repeat (1, 2) 20403 ++ (54789, 2) :: (1, 1) :: repeat (1, 2) 134248 ++ w) 1); closearith.
  }
  (* step 190: P TUP2_1 *)
  apply (hsteps_trans _ (HC [1380; 247; 73; 40; 14; 5] 1962 1 2 ((6776, 2) :: (1, 1) :: repeat (1, 2) 20403 ++ (54789, 2) :: (1, 1) :: repeat (1, 2) 134248 ++ w) 1)).
  {
    replace ((6776, 2) :: (1, 1) :: repeat (1, 2) 20403 ++ (54789, 2) :: (1, 1) :: repeat (1, 2) 134248 ++ w) with ((6778 - 2, 2) :: (1, 1) :: repeat (1, 2) 20403 ++ (54789, 2) :: (1, 1) :: repeat (1, 2) 134248 ++ w) by sec_eq.
    apply (sTUP2_1 [247; 73; 40; 14; 5] 1379 1961 6778 ((1, 1) :: repeat (1, 2) 20403 ++ (54789, 2) :: (1, 1) :: repeat (1, 2) 134248 ++ w) 1); closearith.
  }
  (* step 191: P TDN *)
  apply (hsteps_trans _ (HB [1380; 247; 73; 40; 14; 5] 1962 1 4 ((6776, 2) :: (1, 1) :: repeat (1, 2) 20403 ++ (54789, 2) :: (1, 1) :: repeat (1, 2) 134248 ++ w) 1)).
  {
    apply (sTDN [1380; 247; 73; 40; 14; 5] 1962 ((6776, 2) :: (1, 1) :: repeat (1, 2) 20403 ++ (54789, 2) :: (1, 1) :: repeat (1, 2) 134248 ++ w) 1).
  }
  (* step 192: sTUP *)
  apply (hsteps_trans _ (HC [1380; 247; 73; 40; 14; 5] 1962 3 2 ((6774, 2) :: (1, 1) :: repeat (1, 2) 20403 ++ (54789, 2) :: (1, 1) :: repeat (1, 2) 134248 ++ w) 1)).
  {
    replace ((6774, 2) :: (1, 1) :: repeat (1, 2) 20403 ++ (54789, 2) :: (1, 1) :: repeat (1, 2) 134248 ++ w) with ((6776 - 2, 2) :: (1, 1) :: repeat (1, 2) 20403 ++ (54789, 2) :: (1, 1) :: repeat (1, 2) 134248 ++ w) by sec_eq.
    apply (sTUP [1380; 247; 73; 40; 14; 5] 1962 4 6776 2 ((1, 1) :: repeat (1, 2) 20403 ++ (54789, 2) :: (1, 1) :: repeat (1, 2) 134248 ++ w) 1); closearith.
  }
  (* step 193: DIPGRIND 1962 2850 *)
  apply (hsteps_trans _ (HC [1380; 247; 73; 40; 14; 5] 0 3 2 (repeat (1, 2) 1962 ++ (2850, 2) :: (1, 1) :: repeat (1, 2) 20403 ++ (54789, 2) :: (1, 1) :: repeat (1, 2) 134248 ++ w) 1)).
  {
    apply (DIPGRIND 1962 2850 [1380; 247; 73; 40; 14; 5] ((1, 1) :: repeat (1, 2) 20403 ++ (54789, 2) :: (1, 1) :: repeat (1, 2) 134248 ++ w) 1); closearith.
  }
  (* step 194: P PX2A *)
  apply (hsteps_trans _ (HC [73; 40; 14; 5] 246 1378 2 ((1, 1) :: repeat (1, 2) 1964 ++ (2850, 2) :: (1, 1) :: repeat (1, 2) 20403 ++ (54789, 2) :: (1, 1) :: repeat (1, 2) 134248 ++ w) 1)).
  {
    apply (hsteps_step _ (HC [73; 40; 14; 5] 246 1378 2 ((1, 1) :: repeat (1, 2) 1964 ++ (2850, 2) :: (1, 1) :: repeat (1, 2) 20403 ++ (54789, 2) :: (1, 1) :: repeat (1, 2) 134248 ++ w) 1)); [apply hPX2A | apply hsteps_refl].
  }
  (* step 195: P PUSH *)
  apply (hsteps_trans _ (HC [73; 40; 14; 5] 245 1 2 ((1376, 2) :: (1, 1) :: repeat (1, 2) 1964 ++ (2850, 2) :: (1, 1) :: repeat (1, 2) 20403 ++ (54789, 2) :: (1, 1) :: repeat (1, 2) 134248 ++ w) 1)).
  {
    replace ((1376, 2) :: (1, 1) :: repeat (1, 2) 1964 ++ (2850, 2) :: (1, 1) :: repeat (1, 2) 20403 ++ (54789, 2) :: (1, 1) :: repeat (1, 2) 134248 ++ w) with ((1378 - 2, 2) :: (1, 1) :: repeat (1, 2) 1964 ++ (2850, 2) :: (1, 1) :: repeat (1, 2) 20403 ++ (54789, 2) :: (1, 1) :: repeat (1, 2) 134248 ++ w) by sec_eq.
    apply (sPUSH [73; 40; 14; 5] 245 1378 ((1, 1) :: repeat (1, 2) 1964 ++ (2850, 2) :: (1, 1) :: repeat (1, 2) 20403 ++ (54789, 2) :: (1, 1) :: repeat (1, 2) 134248 ++ w) 1); closearith.
  }
  (* step 196: P TDN *)
  apply (hsteps_trans _ (HB [73; 40; 14; 5] 245 1 4 ((1376, 2) :: (1, 1) :: repeat (1, 2) 1964 ++ (2850, 2) :: (1, 1) :: repeat (1, 2) 20403 ++ (54789, 2) :: (1, 1) :: repeat (1, 2) 134248 ++ w) 1)).
  {
    apply (sTDN [73; 40; 14; 5] 245 ((1376, 2) :: (1, 1) :: repeat (1, 2) 1964 ++ (2850, 2) :: (1, 1) :: repeat (1, 2) 20403 ++ (54789, 2) :: (1, 1) :: repeat (1, 2) 134248 ++ w) 1).
  }
  (* step 197: sTUP *)
  apply (hsteps_trans _ (HC [73; 40; 14; 5] 245 3 2 ((1374, 2) :: (1, 1) :: repeat (1, 2) 1964 ++ (2850, 2) :: (1, 1) :: repeat (1, 2) 20403 ++ (54789, 2) :: (1, 1) :: repeat (1, 2) 134248 ++ w) 1)).
  {
    replace ((1374, 2) :: (1, 1) :: repeat (1, 2) 1964 ++ (2850, 2) :: (1, 1) :: repeat (1, 2) 20403 ++ (54789, 2) :: (1, 1) :: repeat (1, 2) 134248 ++ w) with ((1376 - 2, 2) :: (1, 1) :: repeat (1, 2) 1964 ++ (2850, 2) :: (1, 1) :: repeat (1, 2) 20403 ++ (54789, 2) :: (1, 1) :: repeat (1, 2) 134248 ++ w) by sec_eq.
    apply (sTUP [73; 40; 14; 5] 245 4 1376 2 ((1, 1) :: repeat (1, 2) 1964 ++ (2850, 2) :: (1, 1) :: repeat (1, 2) 20403 ++ (54789, 2) :: (1, 1) :: repeat (1, 2) 134248 ++ w) 1); closearith.
  }
  (* step 198: DIPGRIND 245 884 *)
  apply (hsteps_trans _ (HC [73; 40; 14; 5] 0 3 2 (repeat (1, 2) 245 ++ (884, 2) :: (1, 1) :: repeat (1, 2) 1964 ++ (2850, 2) :: (1, 1) :: repeat (1, 2) 20403 ++ (54789, 2) :: (1, 1) :: repeat (1, 2) 134248 ++ w) 1)).
  {
    apply (DIPGRIND 245 884 [73; 40; 14; 5] ((1, 1) :: repeat (1, 2) 1964 ++ (2850, 2) :: (1, 1) :: repeat (1, 2) 20403 ++ (54789, 2) :: (1, 1) :: repeat (1, 2) 134248 ++ w) 1); closearith.
  }
  (* step 199: P PX2A *)
  apply (hsteps_trans _ (HC [14; 5] 39 71 2 ((1, 1) :: repeat (1, 2) 247 ++ (884, 2) :: (1, 1) :: repeat (1, 2) 1964 ++ (2850, 2) :: (1, 1) :: repeat (1, 2) 20403 ++ (54789, 2) :: (1, 1) :: repeat (1, 2) 134248 ++ w) 1)).
  {
    apply (hsteps_step _ (HC [14; 5] 39 71 2 ((1, 1) :: repeat (1, 2) 247 ++ (884, 2) :: (1, 1) :: repeat (1, 2) 1964 ++ (2850, 2) :: (1, 1) :: repeat (1, 2) 20403 ++ (54789, 2) :: (1, 1) :: repeat (1, 2) 134248 ++ w) 1)); [apply hPX2A | apply hsteps_refl].
  }
  (* step 200: hGRIND 34 *)
  apply (hsteps_trans _ (HB [14; 5] 39 1 74 ((1, 1) :: repeat (1, 2) 247 ++ (884, 2) :: (1, 1) :: repeat (1, 2) 1964 ++ (2850, 2) :: (1, 1) :: repeat (1, 2) 20403 ++ (54789, 2) :: (1, 1) :: repeat (1, 2) 134248 ++ w) 1)).
  {
    apply (hGRIND 34 [14; 5] 39 ((1, 1) :: repeat (1, 2) 247 ++ (884, 2) :: (1, 1) :: repeat (1, 2) 1964 ++ (2850, 2) :: (1, 1) :: repeat (1, 2) 20403 ++ (54789, 2) :: (1, 1) :: repeat (1, 2) 134248 ++ w) 1); closearith.
  }
  (* step 201: P POP *)
  apply (hsteps_trans _ (HB [14; 5] 40 1 75 (repeat (1, 2) 247 ++ (884, 2) :: (1, 1) :: repeat (1, 2) 1964 ++ (2850, 2) :: (1, 1) :: repeat (1, 2) 20403 ++ (54789, 2) :: (1, 1) :: repeat (1, 2) 134248 ++ w) 1)).
  {
    apply (sPOP1 [14; 5] 39 74 (repeat (1, 2) 247 ++ (884, 2) :: (1, 1) :: repeat (1, 2) 1964 ++ (2850, 2) :: (1, 1) :: repeat (1, 2) 20403 ++ (54789, 2) :: (1, 1) :: repeat (1, 2) 134248 ++ w) 1); closearith.
  }
  (* step 202: M pop12 (247,) *)
  apply (hsteps_trans _ (HB [14; 5] 287 1 569 ((884, 2) :: (1, 1) :: repeat (1, 2) 1964 ++ (2850, 2) :: (1, 1) :: repeat (1, 2) 20403 ++ (54789, 2) :: (1, 1) :: repeat (1, 2) 134248 ++ w) 1)).
  {
    apply (pop12 247 [14; 5] 40 75 ((884, 2) :: (1, 1) :: repeat (1, 2) 1964 ++ (2850, 2) :: (1, 1) :: repeat (1, 2) 20403 ++ (54789, 2) :: (1, 1) :: repeat (1, 2) 134248 ++ w) 1); closearith.
  }
  (* step 203: sTUP *)
  apply (hsteps_trans _ (HC [14; 5] 287 568 2 ((882, 2) :: (1, 1) :: repeat (1, 2) 1964 ++ (2850, 2) :: (1, 1) :: repeat (1, 2) 20403 ++ (54789, 2) :: (1, 1) :: repeat (1, 2) 134248 ++ w) 1)).
  {
    replace ((882, 2) :: (1, 1) :: repeat (1, 2) 1964 ++ (2850, 2) :: (1, 1) :: repeat (1, 2) 20403 ++ (54789, 2) :: (1, 1) :: repeat (1, 2) 134248 ++ w) with ((884 - 2, 2) :: (1, 1) :: repeat (1, 2) 1964 ++ (2850, 2) :: (1, 1) :: repeat (1, 2) 20403 ++ (54789, 2) :: (1, 1) :: repeat (1, 2) 134248 ++ w) by sec_eq.
    apply (sTUP [14; 5] 287 569 884 2 ((1, 1) :: repeat (1, 2) 1964 ++ (2850, 2) :: (1, 1) :: repeat (1, 2) 20403 ++ (54789, 2) :: (1, 1) :: repeat (1, 2) 134248 ++ w) 1); closearith.
  }
  (* step 204: hGRIND_even 282 *)
  apply (hsteps_trans _ (HB [14; 5] 286 1 568 ((2, 2) :: (882, 2) :: (1, 1) :: repeat (1, 2) 1964 ++ (2850, 2) :: (1, 1) :: repeat (1, 2) 20403 ++ (54789, 2) :: (1, 1) :: repeat (1, 2) 134248 ++ w) 1)).
  {
    apply (hGRIND_even 282 [14; 5] 286 ((882, 2) :: (1, 1) :: repeat (1, 2) 1964 ++ (2850, 2) :: (1, 1) :: repeat (1, 2) 20403 ++ (54789, 2) :: (1, 1) :: repeat (1, 2) 134248 ++ w) 1); closearith.
  }
  (* step 205: P TUP2_1 *)
  apply (hsteps_trans _ (HC [287; 14; 5] 568 1 2 ((880, 2) :: (1, 1) :: repeat (1, 2) 1964 ++ (2850, 2) :: (1, 1) :: repeat (1, 2) 20403 ++ (54789, 2) :: (1, 1) :: repeat (1, 2) 134248 ++ w) 1)).
  {
    replace ((880, 2) :: (1, 1) :: repeat (1, 2) 1964 ++ (2850, 2) :: (1, 1) :: repeat (1, 2) 20403 ++ (54789, 2) :: (1, 1) :: repeat (1, 2) 134248 ++ w) with ((882 - 2, 2) :: (1, 1) :: repeat (1, 2) 1964 ++ (2850, 2) :: (1, 1) :: repeat (1, 2) 20403 ++ (54789, 2) :: (1, 1) :: repeat (1, 2) 134248 ++ w) by sec_eq.
    apply (sTUP2_1 [14; 5] 286 567 882 ((1, 1) :: repeat (1, 2) 1964 ++ (2850, 2) :: (1, 1) :: repeat (1, 2) 20403 ++ (54789, 2) :: (1, 1) :: repeat (1, 2) 134248 ++ w) 1); closearith.
  }
  (* step 206: P TDN *)
  apply (hsteps_trans _ (HB [287; 14; 5] 568 1 4 ((880, 2) :: (1, 1) :: repeat (1, 2) 1964 ++ (2850, 2) :: (1, 1) :: repeat (1, 2) 20403 ++ (54789, 2) :: (1, 1) :: repeat (1, 2) 134248 ++ w) 1)).
  {
    apply (sTDN [287; 14; 5] 568 ((880, 2) :: (1, 1) :: repeat (1, 2) 1964 ++ (2850, 2) :: (1, 1) :: repeat (1, 2) 20403 ++ (54789, 2) :: (1, 1) :: repeat (1, 2) 134248 ++ w) 1).
  }
  (* step 207: sTUP *)
  apply (hsteps_trans _ (HC [287; 14; 5] 568 3 2 ((878, 2) :: (1, 1) :: repeat (1, 2) 1964 ++ (2850, 2) :: (1, 1) :: repeat (1, 2) 20403 ++ (54789, 2) :: (1, 1) :: repeat (1, 2) 134248 ++ w) 1)).
  {
    replace ((878, 2) :: (1, 1) :: repeat (1, 2) 1964 ++ (2850, 2) :: (1, 1) :: repeat (1, 2) 20403 ++ (54789, 2) :: (1, 1) :: repeat (1, 2) 134248 ++ w) with ((880 - 2, 2) :: (1, 1) :: repeat (1, 2) 1964 ++ (2850, 2) :: (1, 1) :: repeat (1, 2) 20403 ++ (54789, 2) :: (1, 1) :: repeat (1, 2) 134248 ++ w) by sec_eq.
    apply (sTUP [287; 14; 5] 568 4 880 2 ((1, 1) :: repeat (1, 2) 1964 ++ (2850, 2) :: (1, 1) :: repeat (1, 2) 20403 ++ (54789, 2) :: (1, 1) :: repeat (1, 2) 134248 ++ w) 1); closearith.
  }
  (* step 208: CLEANG_even 438 *)
  apply (hsteps_trans _ (HB [287; 14; 5] 568 1 882 ((2, 2) :: (1, 1) :: repeat (1, 2) 1964 ++ (2850, 2) :: (1, 1) :: repeat (1, 2) 20403 ++ (54789, 2) :: (1, 1) :: repeat (1, 2) 134248 ++ w) 1)).
  {
    apply (CLEANG_even 438 [287; 14; 5] 568 ((1, 1) :: repeat (1, 2) 1964 ++ (2850, 2) :: (1, 1) :: repeat (1, 2) 20403 ++ (54789, 2) :: (1, 1) :: repeat (1, 2) 134248 ++ w) 1); closearith.
  }
  (* step 209: P TRANS2_1 *)
  apply (hsteps_trans _ (HB [569; 287; 14; 5] 883 1 3 (repeat (1, 2) 1964 ++ (2850, 2) :: (1, 1) :: repeat (1, 2) 20403 ++ (54789, 2) :: (1, 1) :: repeat (1, 2) 134248 ++ w) 1)).
  {
    apply (sTRANS2_1 [287; 14; 5] 568 881 1 (repeat (1, 2) 1964 ++ (2850, 2) :: (1, 1) :: repeat (1, 2) 20403 ++ (54789, 2) :: (1, 1) :: repeat (1, 2) 134248 ++ w) 1); closearith.
  }
  (* step 210: M pop12 (1964,) *)
  apply (hsteps_trans _ (HB [569; 287; 14; 5] 2847 1 3931 ((2850, 2) :: (1, 1) :: repeat (1, 2) 20403 ++ (54789, 2) :: (1, 1) :: repeat (1, 2) 134248 ++ w) 1)).
  {
    apply (pop12 1964 [569; 287; 14; 5] 883 3 ((2850, 2) :: (1, 1) :: repeat (1, 2) 20403 ++ (54789, 2) :: (1, 1) :: repeat (1, 2) 134248 ++ w) 1); closearith.
  }
  (* step 211: sTUP *)
  apply (hsteps_trans _ (HC [569; 287; 14; 5] 2847 3930 2 ((2848, 2) :: (1, 1) :: repeat (1, 2) 20403 ++ (54789, 2) :: (1, 1) :: repeat (1, 2) 134248 ++ w) 1)).
  {
    replace ((2848, 2) :: (1, 1) :: repeat (1, 2) 20403 ++ (54789, 2) :: (1, 1) :: repeat (1, 2) 134248 ++ w) with ((2850 - 2, 2) :: (1, 1) :: repeat (1, 2) 20403 ++ (54789, 2) :: (1, 1) :: repeat (1, 2) 134248 ++ w) by sec_eq.
    apply (sTUP [569; 287; 14; 5] 2847 3931 2850 2 ((1, 1) :: repeat (1, 2) 20403 ++ (54789, 2) :: (1, 1) :: repeat (1, 2) 134248 ++ w) 1); closearith.
  }
  (* step 212: hGRIND_even 1963 *)
  apply (hsteps_trans _ (HB [569; 287; 14; 5] 2846 1 3930 ((2, 2) :: (2848, 2) :: (1, 1) :: repeat (1, 2) 20403 ++ (54789, 2) :: (1, 1) :: repeat (1, 2) 134248 ++ w) 1)).
  {
    apply (hGRIND_even 1963 [569; 287; 14; 5] 2846 ((2848, 2) :: (1, 1) :: repeat (1, 2) 20403 ++ (54789, 2) :: (1, 1) :: repeat (1, 2) 134248 ++ w) 1); closearith.
  }
  (* step 213: P TUP2_1 *)
  apply (hsteps_trans _ (HC [2847; 569; 287; 14; 5] 3930 1 2 ((2846, 2) :: (1, 1) :: repeat (1, 2) 20403 ++ (54789, 2) :: (1, 1) :: repeat (1, 2) 134248 ++ w) 1)).
  {
    replace ((2846, 2) :: (1, 1) :: repeat (1, 2) 20403 ++ (54789, 2) :: (1, 1) :: repeat (1, 2) 134248 ++ w) with ((2848 - 2, 2) :: (1, 1) :: repeat (1, 2) 20403 ++ (54789, 2) :: (1, 1) :: repeat (1, 2) 134248 ++ w) by sec_eq.
    apply (sTUP2_1 [569; 287; 14; 5] 2846 3929 2848 ((1, 1) :: repeat (1, 2) 20403 ++ (54789, 2) :: (1, 1) :: repeat (1, 2) 134248 ++ w) 1); closearith.
  }
  (* step 214: P TDN *)
  apply (hsteps_trans _ (HB [2847; 569; 287; 14; 5] 3930 1 4 ((2846, 2) :: (1, 1) :: repeat (1, 2) 20403 ++ (54789, 2) :: (1, 1) :: repeat (1, 2) 134248 ++ w) 1)).
  {
    apply (sTDN [2847; 569; 287; 14; 5] 3930 ((2846, 2) :: (1, 1) :: repeat (1, 2) 20403 ++ (54789, 2) :: (1, 1) :: repeat (1, 2) 134248 ++ w) 1).
  }
  (* step 215: sTUP *)
  apply (hsteps_trans _ (HC [2847; 569; 287; 14; 5] 3930 3 2 ((2844, 2) :: (1, 1) :: repeat (1, 2) 20403 ++ (54789, 2) :: (1, 1) :: repeat (1, 2) 134248 ++ w) 1)).
  {
    replace ((2844, 2) :: (1, 1) :: repeat (1, 2) 20403 ++ (54789, 2) :: (1, 1) :: repeat (1, 2) 134248 ++ w) with ((2846 - 2, 2) :: (1, 1) :: repeat (1, 2) 20403 ++ (54789, 2) :: (1, 1) :: repeat (1, 2) 134248 ++ w) by sec_eq.
    apply (sTUP [2847; 569; 287; 14; 5] 3930 4 2846 2 ((1, 1) :: repeat (1, 2) 20403 ++ (54789, 2) :: (1, 1) :: repeat (1, 2) 134248 ++ w) 1); closearith.
  }
  (* step 216: CLEANG_even 1421 *)
  apply (hsteps_trans _ (HB [2847; 569; 287; 14; 5] 3930 1 2848 ((2, 2) :: (1, 1) :: repeat (1, 2) 20403 ++ (54789, 2) :: (1, 1) :: repeat (1, 2) 134248 ++ w) 1)).
  {
    apply (CLEANG_even 1421 [2847; 569; 287; 14; 5] 3930 ((1, 1) :: repeat (1, 2) 20403 ++ (54789, 2) :: (1, 1) :: repeat (1, 2) 134248 ++ w) 1); closearith.
  }
  (* step 217: P TRANS2_1 *)
  apply (hsteps_trans _ (HB [3931; 2847; 569; 287; 14; 5] 2849 1 3 (repeat (1, 2) 20403 ++ (54789, 2) :: (1, 1) :: repeat (1, 2) 134248 ++ w) 1)).
  {
    apply (sTRANS2_1 [2847; 569; 287; 14; 5] 3930 2847 1 (repeat (1, 2) 20403 ++ (54789, 2) :: (1, 1) :: repeat (1, 2) 134248 ++ w) 1); closearith.
  }
  (* step 218: M pop12 (20403,) *)
  apply (hsteps_trans _ (HB [3931; 2847; 569; 287; 14; 5] 23252 1 40809 ((54789, 2) :: (1, 1) :: repeat (1, 2) 134248 ++ w) 1)).
  {
    apply (pop12 20403 [3931; 2847; 569; 287; 14; 5] 2849 3 ((54789, 2) :: (1, 1) :: repeat (1, 2) 134248 ++ w) 1); closearith.
  }
  (* step 219: sTUP *)
  apply (hsteps_trans _ (HC [3931; 2847; 569; 287; 14; 5] 23252 40808 2 ((54787, 2) :: (1, 1) :: repeat (1, 2) 134248 ++ w) 1)).
  {
    replace ((54787, 2) :: (1, 1) :: repeat (1, 2) 134248 ++ w) with ((54789 - 2, 2) :: (1, 1) :: repeat (1, 2) 134248 ++ w) by sec_eq.
    apply (sTUP [3931; 2847; 569; 287; 14; 5] 23252 40809 54789 2 ((1, 1) :: repeat (1, 2) 134248 ++ w) 1); closearith.
  }
  (* step 220: hGRIND_even 20402 *)
  apply (hsteps_trans _ (HB [3931; 2847; 569; 287; 14; 5] 23251 1 40808 ((2, 2) :: (54787, 2) :: (1, 1) :: repeat (1, 2) 134248 ++ w) 1)).
  {
    apply (hGRIND_even 20402 [3931; 2847; 569; 287; 14; 5] 23251 ((54787, 2) :: (1, 1) :: repeat (1, 2) 134248 ++ w) 1); closearith.
  }
  (* step 221: P TUP2_1 *)
  apply (hsteps_trans _ (HC [23252; 3931; 2847; 569; 287; 14; 5] 40808 1 2 ((54785, 2) :: (1, 1) :: repeat (1, 2) 134248 ++ w) 1)).
  {
    replace ((54785, 2) :: (1, 1) :: repeat (1, 2) 134248 ++ w) with ((54787 - 2, 2) :: (1, 1) :: repeat (1, 2) 134248 ++ w) by sec_eq.
    apply (sTUP2_1 [3931; 2847; 569; 287; 14; 5] 23251 40807 54787 ((1, 1) :: repeat (1, 2) 134248 ++ w) 1); closearith.
  }
  (* step 222: P TDN *)
  apply (hsteps_trans _ (HB [23252; 3931; 2847; 569; 287; 14; 5] 40808 1 4 ((54785, 2) :: (1, 1) :: repeat (1, 2) 134248 ++ w) 1)).
  {
    apply (sTDN [23252; 3931; 2847; 569; 287; 14; 5] 40808 ((54785, 2) :: (1, 1) :: repeat (1, 2) 134248 ++ w) 1).
  }
  (* step 223: sTUP *)
  apply (hsteps_trans _ (HC [23252; 3931; 2847; 569; 287; 14; 5] 40808 3 2 ((54783, 2) :: (1, 1) :: repeat (1, 2) 134248 ++ w) 1)).
  {
    replace ((54783, 2) :: (1, 1) :: repeat (1, 2) 134248 ++ w) with ((54785 - 2, 2) :: (1, 1) :: repeat (1, 2) 134248 ++ w) by sec_eq.
    apply (sTUP [23252; 3931; 2847; 569; 287; 14; 5] 40808 4 54785 2 ((1, 1) :: repeat (1, 2) 134248 ++ w) 1); closearith.
  }
  (* step 224: CLEANG_odd 27390 *)
  apply (hsteps_trans _ (HB [23252; 3931; 2847; 569; 287; 14; 5] 40808 1 54788 (repeat (1, 2) 1 ++ (1, 1) :: repeat (1, 2) 134248 ++ w) 1)).
  {
    replace (repeat (1, 2) 1 ++ (1, 1) :: repeat (1, 2) 134248 ++ w) with ((1, 2) :: (1, 1) :: repeat (1, 2) 134248 ++ w) by sec_eq.
    apply (CLEANG_odd 27390 [23252; 3931; 2847; 569; 287; 14; 5] 40808 ((1, 1) :: repeat (1, 2) 134248 ++ w) 1); closearith.
  }
  (* step 225: M pop12 (1,) *)
  apply (hsteps_trans _ (HB [23252; 3931; 2847; 569; 287; 14; 5] 40809 1 54790 ((1, 1) :: repeat (1, 2) 134248 ++ w) 1)).
  {
    apply (pop12 1 [23252; 3931; 2847; 569; 287; 14; 5] 40808 54788 ((1, 1) :: repeat (1, 2) 134248 ++ w) 1); closearith.
  }
  (* step 226: P POP *)
    apply (sPOP1 [23252; 3931; 2847; 569; 287; 14; 5] 40809 54790 (repeat (1, 2) 134248 ++ w) 1); closearith.
Qed.

(* CASCADE52d: step 227 of the CASCADE52 chain, isolated (see the
   header note): the goal numerals are rewritten to pop12's
   computed form before the verbatim step-227 apply. *)
Lemma CASCADE52d : forall w,
  hsteps (HB [23252; 3931; 2847; 569; 287; 14; 5] 40810 1 54791 (repeat (1, 2) 134248 ++ w) 1)
         (HB [23252; 3931; 2847; 569; 287; 14; 5] 175058 1 323287 w 1).
Proof.
  intro w.
  replace 175058 with (40810 + 134248)
    by (apply Nat.eqb_eq; vm_compute; reflexivity).
  replace 323287 with (54791 + 2 * 134248)
    by (apply Nat.eqb_eq; vm_compute; reflexivity).
  (* step 227: M pop12 (134248,) *)
  apply (pop12 134248 [23252; 3931; 2847; 569; 287; 14; 5] 40810 54791 (w) 1); closearith.
Qed.

Lemma CASCADE52 : forall w,
  hsteps (HC [95597; 20403; 10332; 112; 20; 0] 0 3 2
            (repeat (1, 2) 134246 ++ w) 1)
         (HB [23252; 3931; 2847; 569; 287; 14; 5] 175058 1 323287 w 1).
Proof.
  intro w.
  apply (hsteps_trans _ (HB [49; 5] 76 1 19 (repeat (1, 2) 228 ++ (9648, 2) :: (1, 1) :: repeat (1, 2) 20403 ++ (54789, 2) :: (1, 1) :: repeat (1, 2) 134248 ++ w) 1)).
  { exact (CASCADE52a w). }
  apply (hsteps_trans _ (HC [20; 0] 0 3 2 (repeat (1, 2) 33 ++ (38, 2) :: (1, 1) :: repeat (1, 2) 210 ++ (49, 2) :: (1, 1) :: repeat (1, 2) 956 ++ (6780, 2) :: (1, 1) :: repeat (1, 2) 20403 ++ (54789, 2) :: (1, 1) :: repeat (1, 2) 134248 ++ w) 1)).
  { exact (CASCADE52b w). }
  apply (hsteps_trans _ (HB [23252; 3931; 2847; 569; 287; 14; 5] 40810 1 54791 (repeat (1, 2) 134248 ++ w) 1)).
  { exact (CASCADE52c w). }
  exact (CASCADE52d w).
Qed.

(* ----------------------------------------------------------------- *)
(* TOP52_TO_TOP6: the TOP5 front + DIPGRIND (134246, r6) +          *)
(* CASCADE52, landing on TOP6 with the pair (2 * (j - 134249), 2).  *)
(* ----------------------------------------------------------------- *)

Lemma TOP52_TO_TOP6 : forall j beta, 134250 <= j -> 2 <= beta ->
  hsteps (HB [20403; 10332; 112; 20; 0] 95597 1 134247
            ((2 * j, 2) :: (1, 1) :: repeat (1, 2) (beta - 1)) 1)
         (HB [23252; 3931; 2847; 569; 287; 14; 5] 175058 1 323287
            ((2 * (j - 134249), 2) :: (1, 1)
             :: repeat (1, 2) (beta - 1)) 1).
Proof.
  intros j beta Hj Hb.
  (* lia cannot use Hj directly: 134250 is an of_num_uint atom,     *)
  (* unrelated in lia's eyes to the numerals below.  Derive a      *)
  (* numeral lower bound on j, and normalise the 134249/134250     *)
  (* atoms onto the single atom 134246 where an identity needs     *)
  (* them.                                                         *)
  assert (Hj4 : 4 <= j).
  { apply Nat.le_trans with 134250; [closearith | exact Hj]. }
  assert (Hr : 1 <= j - 134249).
  { change 134249 with (134250 - 1). lia. }
  assert (Heq : 2 * j - 6 = 2 * 134246 + 2 * (j - 134249)).
  { change 134249 with (134246 + 3).
    change 134250 with (134246 + 4) in Hj. lia. }
  apply (hsteps_trans _ (HC [20403; 10332; 112; 20; 0] 95597
    134246 2 ((2 * j - 2, 2) :: (1, 1) :: repeat (1, 2) (beta - 1)) 1)).
  { apply (sTUP [20403; 10332; 112; 20; 0] 95597 134247 (2 * j) 2
           ((1, 1) :: repeat (1, 2) (beta - 1)) 1); closearith. }
  apply (hsteps_trans _ (HB [20403; 10332; 112; 20; 0] 95596
    1 134246 ((2, 2) :: (2 * j - 2, 2) :: (1, 1)
            :: repeat (1, 2) (beta - 1)) 1)).
  { apply (hGRIND_even 67121 [20403; 10332; 112; 20; 0] 95596
           ((2 * j - 2, 2) :: (1, 1) :: repeat (1, 2) (beta - 1))
           1); closearith. }
  apply (hsteps_trans _ (HC [95597; 20403; 10332; 112; 20; 0]
    134246 1 2 ((2 * j - 4, 2) :: (1, 1) :: repeat (1, 2) (beta - 1)) 1)).
  { replace ((2 * j - 4, 2) :: (1, 1) :: repeat (1, 2) (beta - 1))
      with ((2 * j - 2 - 2, 2) :: (1, 1) :: repeat (1, 2) (beta - 1))
      by sec_eq.
    apply (sTUP2_1 [20403; 10332; 112; 20; 0] 95596 134245
           (2 * j - 2) ((1, 1) :: repeat (1, 2) (beta - 1)) 1); lia. }
  apply (hsteps_trans _ (HB [95597; 20403; 10332; 112; 20; 0]
    134246 1 4 ((2 * j - 4, 2) :: (1, 1) :: repeat (1, 2) (beta - 1)) 1)).
  { apply (sTDN [95597; 20403; 10332; 112; 20; 0] 134246
           ((2 * j - 4, 2) :: (1, 1) :: repeat (1, 2) (beta - 1))
           1). }
  apply (hsteps_trans _ (HC [95597; 20403; 10332; 112; 20; 0]
    134246 3 2 ((2 * j - 6, 2) :: (1, 1) :: repeat (1, 2) (beta - 1)) 1)).
  { replace ((2 * j - 6, 2) :: (1, 1) :: repeat (1, 2) (beta - 1))
      with ((2 * j - 4 - 2, 2) :: (1, 1) :: repeat (1, 2) (beta - 1))
      by sec_eq.
    apply (sTUP [95597; 20403; 10332; 112; 20; 0] 134246 4
           (2 * j - 4) 2 ((1, 1) :: repeat (1, 2) (beta - 1)) 1);
      lia. }
  apply (hsteps_trans _ (HC [95597; 20403; 10332; 112; 20; 0]
    0 3 2 (repeat (1, 2) 134246
     ++ ((2 * (j - 134249), 2) :: (1, 1)
         :: repeat (1, 2) (beta - 1))) 1)).
  { rewrite Heq.
    apply (DIPGRIND 134246 (2 * (j - 134249))
           [95597; 20403; 10332; 112; 20; 0]
           ((1, 1) :: repeat (1, 2) (beta - 1)) 1);
      [closearith | lia]. }
  apply (CASCADE52 ((2 * (j - 134249), 2) :: (1, 1)
                    :: repeat (1, 2) (beta - 1))).
Qed.

(* ----------------------------------------------------------------- *)
(* The TOP6 closings: r6 = 2, 4, 6 and band 6 (8 <= r6 <= 646578).  *)
(* ----------------------------------------------------------------- *)

Lemma TOP52_2 : forall beta, 2 <= beta ->
  hsteps (HB [23252; 3931; 2847; 569; 287; 14; 5] 175058 1 323287
            ((2, 2) :: (1, 1) :: repeat (1, 2) (beta - 1)) 1)
         (HB [175059; 23252; 3931; 2847; 569; 287; 14; 5]
            (323288 + (beta - 1)) 1 (2 * beta + 1) [] 1).
Proof.
  intros beta Hb.
  apply (hsteps_trans _ (HB [175059; 23252; 3931; 2847; 569; 287;
    14; 5] 323288 1 3 (repeat (1, 2) (beta - 1)) 1)).
  { apply (sTRANS2_1 [23252; 3931; 2847; 569; 287; 14; 5] 175058
           323286 1 (repeat (1, 2) (beta - 1)) 1); lia. }
  apply (CASCADE_POPFIN [175059; 23252; 3931; 2847; 569; 287; 14; 5]
         323288 beta); lia.
Qed.

(* NOTE (Phase 52 fix-up): in TOP52_4, TOP52_6 and TOP52_BAND the  *)
(* hGRIND_even 161641 step is preceded by two goal rewrites,        *)
(* 323286 -> (2 * 161641 + 4) and 175058 -> (S 175057), discharged  *)
(* by Nat.eqb_eq + vm_compute.  Without them, unifying             *)
(* hGRIND_even's (2 * t + 4) and (S a2) slots against the literal   *)
(* goal numerals forces unary conversions of depth ~323286 that    *)
(* overflow the conversion stack (the same phenomenon as step 227  *)
(* in CASCADE52d above).  The step applies themselves are           *)
(* unchanged.                                                       *)

Lemma TOP52_4 : forall beta, 2 <= beta ->
  hsteps (HB [23252; 3931; 2847; 569; 287; 14; 5] 175058 1 323287
            ((4, 2) :: (1, 1) :: repeat (1, 2) (beta - 1)) 1)
         (HB [323287; 175058; 23252; 3931; 2847; 569; 287; 14; 5]
            (beta + 2) 1 (2 * beta + 1) [] 1).
Proof.
  intros beta Hb.
  apply (hsteps_trans _ (HC [23252; 3931; 2847; 569; 287; 14; 5]
    175058 323286 2
    ((2, 2) :: (1, 1) :: repeat (1, 2) (beta - 1)) 1)).
  { apply (sTUP [23252; 3931; 2847; 569; 287; 14; 5] 175058 323287
           4 2 ((1, 1) :: repeat (1, 2) (beta - 1)) 1); closearith. }
  apply (hsteps_trans _ (HB [23252; 3931; 2847; 569; 287; 14; 5]
    175057 1 323286 ((2, 2) :: (2, 2) :: (1, 1)
            :: repeat (1, 2) (beta - 1)) 1)).
  { replace 323286 with (2 * 161641 + 4)
      by (apply Nat.eqb_eq; vm_compute; reflexivity).
    replace 175058 with (S 175057)
      by (apply Nat.eqb_eq; vm_compute; reflexivity).
    apply (hGRIND_even 161641 [23252; 3931; 2847; 569; 287; 14; 5]
           175057 ((2, 2) :: (1, 1) :: repeat (1, 2) (beta - 1)) 1);
      closearith. }
  apply (hsteps_trans _ (HB [323287; 175058; 23252; 3931; 2847;
    569; 287; 14; 5] 3 1 3 (repeat (1, 2) (beta - 1)) 1)).
  { apply (hsteps_step _ (HB [323287; 175058; 23252; 3931; 2847;
      569; 287; 14; 5] 3 1 3 (repeat (1, 2) (beta - 1)) 1));
      [apply hTRANS2_2; closearith | apply hsteps_refl]. }
  replace (beta + 2) with (3 + (beta - 1)) by lia.
  apply (CASCADE_POPFIN [323287; 175058; 23252; 3931; 2847; 569;
         287; 14; 5] 3 beta); lia.
Qed.

Lemma TOP52_6 : forall beta, 2 <= beta ->
  hsteps (HB [23252; 3931; 2847; 569; 287; 14; 5] 175058 1 323287
            ((6, 2) :: (1, 1) :: repeat (1, 2) (beta - 1)) 1)
         (HB [323287; 175058; 23252; 3931; 2847; 569; 287; 14; 5]
            (beta + 4) 1 (2 * beta + 1) [] 1).
Proof.
  intros beta Hb.
  apply (hsteps_trans _ (HC [23252; 3931; 2847; 569; 287; 14; 5]
    175058 323286 2
    ((4, 2) :: (1, 1) :: repeat (1, 2) (beta - 1)) 1)).
  { apply (sTUP [23252; 3931; 2847; 569; 287; 14; 5] 175058 323287
           6 2 ((1, 1) :: repeat (1, 2) (beta - 1)) 1); closearith. }
  apply (hsteps_trans _ (HB [23252; 3931; 2847; 569; 287; 14; 5]
    175057 1 323286 ((2, 2) :: (4, 2) :: (1, 1)
            :: repeat (1, 2) (beta - 1)) 1)).
  { replace 323286 with (2 * 161641 + 4)
      by (apply Nat.eqb_eq; vm_compute; reflexivity).
    replace 175058 with (S 175057)
      by (apply Nat.eqb_eq; vm_compute; reflexivity).
    apply (hGRIND_even 161641 [23252; 3931; 2847; 569; 287; 14; 5]
           175057 ((4, 2) :: (1, 1) :: repeat (1, 2) (beta - 1)) 1);
      closearith. }
  apply (hsteps_trans _ (HC [175058; 23252; 3931; 2847; 569; 287;
    14; 5] 323286 1 2
    ((2, 2) :: (1, 1) :: repeat (1, 2) (beta - 1)) 1)).
  { replace ((2, 2) :: (1, 1) :: repeat (1, 2) (beta - 1))
      with ((4 - 2, 2) :: (1, 1) :: repeat (1, 2) (beta - 1))
      by sec_eq.
    apply (sTUP2_1 [23252; 3931; 2847; 569; 287; 14; 5] 175057
           323285 4 ((1, 1) :: repeat (1, 2) (beta - 1)) 1); lia. }
  apply (hsteps_trans _ (HB [175058; 23252; 3931; 2847; 569; 287;
    14; 5] 323286 1 4
    ((2, 2) :: (1, 1) :: repeat (1, 2) (beta - 1)) 1)).
  { apply (sTDN [175058; 23252; 3931; 2847; 569; 287; 14; 5] 323286
           ((2, 2) :: (1, 1) :: repeat (1, 2) (beta - 1)) 1). }
  apply (hsteps_trans _ (HB [323287; 175058; 23252; 3931; 2847;
    569; 287; 14; 5] 5 1 3 (repeat (1, 2) (beta - 1)) 1)).
  { apply (sTRANS2_1 [175058; 23252; 3931; 2847; 569; 287; 14; 5]
           323286 3 1 (repeat (1, 2) (beta - 1)) 1); lia. }
  replace (beta + 4) with (5 + (beta - 1)) by lia.
  apply (CASCADE_POPFIN [323287; 175058; 23252; 3931; 2847; 569;
         287; 14; 5] 5 beta); lia.
Qed.

Lemma TOP52_BAND : forall j beta, 4 <= j -> j <= 323289 -> 2 <= beta ->
  hsteps (HB [23252; 3931; 2847; 569; 287; 14; 5] 175058 1 323287
            ((2 * j, 2) :: (1, 1) :: repeat (1, 2) (beta - 1)) 1)
         (HB [323287; 175058; 23252; 3931; 2847; 569; 287; 14; 5]
            (2 * j + beta - 2) 1 (2 * beta + 1) [] 1).
Proof.
  intros j beta Hj1 Hj2 Hb.
  apply (hsteps_trans _ (HC [23252; 3931; 2847; 569; 287; 14; 5]
    175058 323286 2 ((2 * j - 2, 2) :: (1, 1)
            :: repeat (1, 2) (beta - 1)) 1)).
  { apply (sTUP [23252; 3931; 2847; 569; 287; 14; 5] 175058 323287
           (2 * j) 2 ((1, 1) :: repeat (1, 2) (beta - 1)) 1);
      closearith. }
  apply (hsteps_trans _ (HB [23252; 3931; 2847; 569; 287; 14; 5]
    175057 1 323286 ((2, 2) :: (2 * j - 2, 2) :: (1, 1)
            :: repeat (1, 2) (beta - 1)) 1)).
  { replace 323286 with (2 * 161641 + 4)
      by (apply Nat.eqb_eq; vm_compute; reflexivity).
    replace 175058 with (S 175057)
      by (apply Nat.eqb_eq; vm_compute; reflexivity).
    apply (hGRIND_even 161641 [23252; 3931; 2847; 569; 287; 14; 5]
           175057 ((2 * j - 2, 2) :: (1, 1)
           :: repeat (1, 2) (beta - 1)) 1); closearith. }
  apply (hsteps_trans _ (HC [175058; 23252; 3931; 2847; 569; 287;
    14; 5] 323286 1 2 ((2 * j - 4, 2) :: (1, 1)
            :: repeat (1, 2) (beta - 1)) 1)).
  { replace ((2 * j - 4, 2) :: (1, 1) :: repeat (1, 2) (beta - 1))
      with ((2 * j - 2 - 2, 2) :: (1, 1)
            :: repeat (1, 2) (beta - 1)) by sec_eq.
    apply (sTUP2_1 [23252; 3931; 2847; 569; 287; 14; 5] 175057
           323285 (2 * j - 2) ((1, 1) :: repeat (1, 2) (beta - 1))
           1); lia. }
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
      with ((2 * j - 4 - 2, 2) :: (1, 1)
            :: repeat (1, 2) (beta - 1)) by sec_eq.
    apply (sTUP [175058; 23252; 3931; 2847; 569; 287; 14; 5] 323286
           4 (2 * j - 4) 2 ((1, 1) :: repeat (1, 2) (beta - 1)) 1);
      lia. }
  apply (hsteps_trans _ (HB [175058; 23252; 3931; 2847; 569; 287;
    14; 5] 323286 1 (2 * j - 2)
    ((2, 2) :: (1, 1) :: repeat (1, 2) (beta - 1)) 1)).
  { replace (2 * j - 6) with (2 * (j - 4) + 2) by lia.
    replace (2 * j - 2) with (2 * (j - 4) + 6) by lia.
    apply (CLEANG_even (j - 4) [175058; 23252; 3931; 2847; 569;
           287; 14; 5] 323286 ((1, 1) :: repeat (1, 2) (beta - 1))
           1).
    (* the floor (j - 4) + 1 <= 323286: route via j <= 323289 *)
    apply Nat.le_trans with (j - 3).
    - lia.
    - change 323286 with (323289 - 3).
      apply Nat.sub_le_mono_r. exact Hj2. }
  apply (hsteps_trans _ (HB [323287; 175058; 23252; 3931; 2847;
    569; 287; 14; 5] (2 * j - 1) 1 3 (repeat (1, 2) (beta - 1)) 1)).
  { replace (2 * j - 2) with (S (2 * j - 3)) by lia.
    replace (2 * j - 1) with (S (S (2 * j - 3))) by lia.
    apply (sTRANS2_1 [175058; 23252; 3931; 2847; 569; 287; 14; 5]
           323286 (2 * j - 3) 1 (repeat (1, 2) (beta - 1)) 1); lia. }
  replace (2 * j + beta - 2) with (2 * j - 1 + (beta - 1)) by lia.
  apply (CASCADE_POPFIN [323287; 175058; 23252; 3931; 2847; 569;
         287; 14; 5] (2 * j - 1) beta); lia.
Qed.

(* ----------------------------------------------------------------- *)
(* TAIL2_END7: the strictly smaller residual core -- the totality   *)
(* of the TOP6 state for r6 = 2 * j, j >= 323290 (r6 >= 646580),    *)
(* where the GRIND7 pair (r6 - 6, 2) at counter 323286 takes the    *)
(* DIPDESC boundary a seventh time.  A Definition (lemma            *)
(* parameter), never an axiom.                                      *)
(* ----------------------------------------------------------------- *)

Definition TAIL2_END7 : Prop :=
  forall j beta, 323290 <= j -> 2 <= beta ->
  exists pb A, beta <= A /\
    hsteps (HB [23252; 3931; 2847; 569; 287; 14; 5] 175058 1 323287
              ((2 * j, 2) :: (1, 1) :: repeat (1, 2) (beta - 1)) 1)
           (HB pb A 1 (2 * beta + 1) [] 1).

(* ----------------------------------------------------------------- *)
(* TAIL2_END6_of52: TAIL2_END6, modulo TAIL2_END7.  The j-range     *)
(* splits at r6 = 2 * (j - 134249): the three small cases and       *)
(* band 6 are proved above; j - 134249 >= 323290 is the core.       *)
(* (Phase 52 fix-up: the two `change N with (S (N-1))` steps at     *)
(* N = 323290 / 323288 are replaced by eqb/vm-proved equality       *)
(* rewrites -- the S-conversions at depth ~323290 overflow the      *)
(* conversion stack, cf. the CASCADE52d note.  The 134250 change    *)
(* in the last branch is below the overflow threshold and stays.)   *)
(* ----------------------------------------------------------------- *)

Lemma TAIL2_END6_of52 : TAIL2_END7 -> TAIL2_END6.
Proof.
  intros H7 j beta Hj Hb.
  pose proof (TOP52_TO_TOP6 j beta Hj Hb) as Htop.
  destruct (le_lt_dec 323290 (j - 134249)) as [Hbig | Hsmall].
  - (* j6 = j - 134249 >= 323290: the core *)
    destruct (H7 (j - 134249) beta Hbig Hb)
      as [pb [A [Ha Hsteps]]].
    exists pb, A. split; [exact Ha |].
    exact (hsteps_trans _ _ _ Htop Hsteps).
  - destruct (le_lt_dec 4 (j - 134249)) as [Hband | Htiny].
    + (* band 6: j6 = j - 134249, 4 <= j6 <= 323289 *)
      exists [323287; 175058; 23252; 3931; 2847; 569; 287; 14; 5],
        (2 * (j - 134249) + beta - 2).
      split; [lia |].
      assert (Hj2 : j - 134249 <= 323289).
      { assert (E : 323290 = S 323289)
          by (apply Nat.eqb_eq; vm_compute; reflexivity).
        rewrite E in Hsmall.
        apply (proj1 (Nat.lt_succ_r _ _) Hsmall). }
      exact (hsteps_trans _ _ _ Htop
               (TOP52_BAND (j - 134249) beta Hband Hj2 Hb)).
    + (* tiny: j6 = j - 134249 <= 3; j6 >= 1 since 134250 <= j *)
      destruct (Nat.eq_dec (j - 134249) 1) as [He | Hne].
      * (* r6 = 2 *)
        rewrite He in Htop.
        exists [175059; 23252; 3931; 2847; 569; 287; 14; 5],
          (323288 + (beta - 1)).
        split; [replace 323288 with (S 323287)
                  by (apply Nat.eqb_eq; vm_compute; reflexivity); lia |].
        exact (hsteps_trans _ _ _ Htop (TOP52_2 beta Hb)).
      * destruct (Nat.eq_dec (j - 134249) 2) as [He | Hne'].
        -- (* r6 = 4 *)
           rewrite He in Htop.
           exists [323287; 175058; 23252; 3931; 2847; 569; 287;
             14; 5], (beta + 2).
           split; [lia |].
           exact (hsteps_trans _ _ _ Htop (TOP52_4 beta Hb)).
        -- destruct (Nat.eq_dec (j - 134249) 3) as [He | Hne''].
           ++ (* r6 = 6 *)
              rewrite He in Htop.
              exists [323287; 175058; 23252; 3931; 2847; 569; 287;
                14; 5], (beta + 4).
              split; [lia |].
              exact (hsteps_trans _ _ _ Htop (TOP52_6 beta Hb)).
           ++ (* j6 = 0, contradicting 134250 <= j *)
              exfalso.
              assert (H0 : j - 134249 = 0) by lia.
              change 134250 with (S 134249) in Hj.
              lia.
Qed.

(* ----------------------------------------------------------------- *)
(* ESC_ERA_LAW_52: the phase-8 ESC era law at every even            *)
(* R >= 1278, modulo TAIL2_END7 alone.                              *)
(* ----------------------------------------------------------------- *)

Lemma ESC_ERA_LAW_52 : TAIL2_END7 ->
  forall M beta, 616 <= M -> 2 <= beta ->
  exists n c pb a,
    run n (esc_src (2 * M + 52) (beta - 2)) = Some c
    /\ cfg_sim c (rcsec (false :: repeat true (S a) ++ enc pb)
                        (2 * beta + 2) [(1, 2)])
    /\ beta <= a.
Proof.
  intros H M beta HM Hb.
  apply (ESC_ERA_LAW_51 (TAIL2_END6_of52 H) M beta HM Hb).
Qed.

(* ----------------------------------------------------------------- *)
(* Assumption audit                                                  *)
(* ----------------------------------------------------------------- *)

Print Assumptions CASCADE52.
Print Assumptions TOP52_TO_TOP6.
Print Assumptions TOP52_2.
Print Assumptions TOP52_4.
Print Assumptions TOP52_6.
Print Assumptions TOP52_BAND.
Print Assumptions TAIL2_END6_of52.
Print Assumptions ESC_ERA_LAW_52.
