(* ================================================================= *)
(* Phase 58 (tail): the TOP12 closings, the residual core          *)
(* TAIL2_END13, TAIL2_END12_of58 and ESC_ERA_LAW_58.  Split from    *)
(* Grind26.v / Grind26b.v for the operational reason recorded in    *)
(* Grind26b.v's header (compile resident set at Phase 58 numeral    *)
(* depths); every lemma statement is the one the phase's single-    *)
(* file draft carried.  The phase narrative lives in Grind26.v's    *)
(* header.                                                          *)
(* ================================================================= *)

Require Import List Bool Arith Lia ZArith.
Import ListNotations.
Require Import TM Sections Mirror TokenPass Recoord Era Esc Dev
               Grind Grind2 Grind3 Grind4 Grind5 Grind6 Grind7 Grind8
               Grind9 Grind10 Grind11 Grind12 Grind13 Grind14 Grind15
               Grind16 Grind17 Grind18 Grind19 Grind20 Grind21 Grind22
               Grind23 Grind24 Grind25 Grind26 Grind26a Grind26b.

(* Section equality: componentwise, arithmetic leaves by lia.      *)
Ltac sec_eq :=
  repeat (first [ solve [reflexivity] | solve [lia] | f_equal ]).

(* Closed-numeral arithmetic: literals >= 7426 are parsed as       *)
(* Nat.of_num_uint atoms, which lia cannot relate to variables;    *)
(* for purely closed <= goals the boolean check decides them.      *)
Ltac closearith :=
  first [ lia | apply Nat.leb_le; reflexivity ].


(* ----------------------------------------------------------------- *)
(* TOP58_TO_TOP12: the TOP11 state at (2j, 2) reaches TOP12 at the   *)
(* pair (2 * (j - 11874957), 2).  The front is the Phase 57 front     *)
(* verbatim at the new constants: the first TUP rewrites via         *)
(* NUM57h (11874954 = 11874955 - 1, inherited from Grind25.v), the   *)
(* hGRIND_even 5937475 step rewrites the goal by NUM57a / NUM57b     *)
(* (11874954 = 2 * 5937475 + 4, 8675859 = S 8675858), and the         *)
(* TUP2_1 step rewrites via NUM57i (11874954 = S 11874953) / NUM57b. *)
(* ----------------------------------------------------------------- *)

Lemma TOP58_TO_TOP12 : forall j beta, 11874958 <= j -> 2 <= beta ->
  hsteps (HB [1511339; 790956; 25145; 13306; 4643; 2871; 335; 235; 42; 19] 8675859 1 11874955
            ((2 * j, 2) :: (1, 1) :: repeat (1, 2) (beta - 1)) 1)
         (HB [1523948; 426279; 308525; 58213; 30332; 931; 608; 77; 35; 20; 0] 14897638 1 29403093
            ((2 * (j - 11874957), 2) :: (1, 1)
             :: repeat (1, 2) (beta - 1)) 1).
Proof.
  intros j beta Hj Hb.
  assert (Hj4 : 4 <= j).
  { apply Nat.le_trans with 11874958; [closearith | exact Hj]. }
  assert (Hr : 1 <= j - 11874957).
  { assert (E : 11874957 = 11874958 - 1)
      by (exact S58f1).
    rewrite E. lia. }
  assert (Heq : 2 * j - 6 = 2 * 11874954 + 2 * (j - 11874957)).
  { assert (E1 : 11874957 = 11874954 + 3)
      by (exact S58f2).
    assert (E2 : 11874958 = 11874954 + 4)
      by (exact S58f3).
    rewrite E1. rewrite E2 in Hj. lia. }
  apply (hsteps_trans _ (HC [1511339; 790956; 25145; 13306; 4643; 2871; 335; 235; 42; 19] 8675859
    11874954 2 ((2 * j - 2, 2) :: (1, 1) :: repeat (1, 2) (beta - 1)) 1)).
  { rewrite NUM57h.
    apply (sTUP [1511339; 790956; 25145; 13306; 4643; 2871; 335; 235; 42; 19] 8675859 11874955 (2 * j) 2
           ((1, 1) :: repeat (1, 2) (beta - 1)) 1); closearith. }
  apply (hsteps_trans _ (HB [1511339; 790956; 25145; 13306; 4643; 2871; 335; 235; 42; 19]
    8675858 1 11874954 ((2, 2) :: (2 * j - 2, 2) :: (1, 1)
            :: repeat (1, 2) (beta - 1)) 1)).
  { rewrite NUM57a. rewrite NUM57b.
    apply (hGRIND_even 5937475 [1511339; 790956; 25145; 13306; 4643; 2871; 335; 235; 42; 19]
           8675858 ((2 * j - 2, 2) :: (1, 1) :: repeat (1, 2) (beta - 1))
           1); closearith. }
  apply (hsteps_trans _ (HC [8675859; 1511339; 790956; 25145; 13306; 4643; 2871; 335; 235; 42; 19] 11874954 1 2 ((2 * j - 4, 2) :: (1, 1)
            :: repeat (1, 2) (beta - 1)) 1)).
  { rewrite NUM57i. rewrite NUM57b.
    replace ((2 * j - 4, 2) :: (1, 1) :: repeat (1, 2) (beta - 1))
      with ((2 * j - 2 - 2, 2) :: (1, 1) :: repeat (1, 2) (beta - 1))
      by sec_eq.
    apply (sTUP2_1 [1511339; 790956; 25145; 13306; 4643; 2871; 335; 235; 42; 19] 8675858
           11874953 (2 * j - 2) ((1, 1) :: repeat (1, 2) (beta - 1)) 1); lia. }
  apply (hsteps_trans _ (HB [8675859; 1511339; 790956; 25145; 13306; 4643; 2871; 335; 235; 42; 19] 11874954 1 4 ((2 * j - 4, 2) :: (1, 1)
            :: repeat (1, 2) (beta - 1)) 1)).
  { apply (sTDN [8675859; 1511339; 790956; 25145; 13306; 4643; 2871; 335; 235; 42; 19] 11874954
           ((2 * j - 4, 2) :: (1, 1) :: repeat (1, 2) (beta - 1))
           1). }
  apply (hsteps_trans _ (HC [8675859; 1511339; 790956; 25145; 13306; 4643; 2871; 335; 235; 42; 19] 11874954 3 2 ((2 * j - 6, 2) :: (1, 1)
            :: repeat (1, 2) (beta - 1)) 1)).
  { replace ((2 * j - 6, 2) :: (1, 1) :: repeat (1, 2) (beta - 1))
      with ((2 * j - 4 - 2, 2) :: (1, 1) :: repeat (1, 2) (beta - 1))
      by sec_eq.
    apply (sTUP [8675859; 1511339; 790956; 25145; 13306; 4643; 2871; 335; 235; 42; 19] 11874954
           4 (2 * j - 4) 2 ((1, 1) :: repeat (1, 2) (beta - 1)) 1);
      lia. }
  apply (hsteps_trans _ (HC [8675859; 1511339; 790956; 25145; 13306; 4643; 2871; 335; 235; 42; 19]
    0 3 2 (repeat (1, 2) 11874954
     ++ ((2 * (j - 11874957), 2) :: (1, 1)
         :: repeat (1, 2) (beta - 1))) 1)).
  { rewrite Heq.
    apply (DIPGRIND 11874954 (2 * (j - 11874957))
           [8675859; 1511339; 790956; 25145; 13306; 4643; 2871; 335; 235; 42; 19]
           ((1, 1) :: repeat (1, 2) (beta - 1)) 1);
      [closearith | lia]. }
  apply (CASCADE58 ((2 * (j - 11874957), 2) :: (1, 1)
                    :: repeat (1, 2) (beta - 1))).
Qed.

(* ----------------------------------------------------------------- *)
(* The TOP12 closings: r12' = 2, 4, 6 and band 12                    *)
(* (8 <= r12' <= 58806190).                                          *)
(* ----------------------------------------------------------------- *)

Print Assumptions TOP58_TO_TOP12.
