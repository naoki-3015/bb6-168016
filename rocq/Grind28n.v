(* ================================================================= *)
(* Phase 60 (tail): the r14' = 4 closing (TOP60_4).  Split from    *)
(* Grind28.v / Grind28j.v for the operational reason recorded in   *)
(* Grind28.v's header (compile resident set at Phase 60 numeral    *)
(* depths); every lemma statement is the one the phase's single-   *)
(* file draft carried.  The phase narrative lives in Grind28.v's   *)
(* header.                                                         *)
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
               Grind28aa Grind28ab Grind28ae Grind28af Grind28b
               Grind28d Grind28f
               Grind28g Grind28h Grind28r.
(* Section equality: componentwise, arithmetic leaves by lia.      *)
Ltac sec_eq :=
  repeat (first [ solve [reflexivity] | solve [lia] | f_equal ]).

(* Closed-numeral arithmetic: literals >= 7426 are parsed as       *)
(* Nat.of_num_uint atoms, which lia cannot relate to variables;    *)
(* for purely closed <= goals the boolean check decides them.      *)
Ltac closearith :=
  first [ lia | apply Nat.leb_le; reflexivity ].

Lemma TOP60_4 : forall beta, 2 <= beta ->
  hsteps (HB [10126538; 1236011; 698173; 177445; 95640; 10129; 1243; 207; 19] 74737818 1 135985237
            ((4, 2) :: (1, 1) :: repeat (1, 2) (beta - 1)) 1)
         (HB [135985237; 74737818; 10126538; 1236011; 698173; 177445; 95640; 10129; 1243; 207; 19]
            (beta + 2) 1 (2 * beta + 1) [] 1).
Proof.
  intros beta Hb.
  apply (hsteps_trans _ (HC [10126538; 1236011; 698173; 177445; 95640; 10129; 1243; 207; 19]
    74737818 135985236 2
    ((2, 2) :: (1, 1) :: repeat (1, 2) (beta - 1)) 1)).
  { rewrite NUM60h.
    apply (sTUP [10126538; 1236011; 698173; 177445; 95640; 10129; 1243; 207; 19] 74737818 135985237
           4 2 ((1, 1) :: repeat (1, 2) (beta - 1)) 1);
      [exact S60h0 | lia]. }
  apply (hsteps_trans _ (HB [10126538; 1236011; 698173; 177445; 95640; 10129; 1243; 207; 19]
    74737817 1 135985236 ((2, 2) :: (2, 2) :: (1, 1)
            :: repeat (1, 2) (beta - 1)) 1)).
  { rewrite NUM60a. rewrite NUM60b.
    apply (hGRIND_even 67992616 [10126538; 1236011; 698173; 177445; 95640; 10129; 1243; 207; 19]
           74737817 ((2, 2) :: (1, 1) :: repeat (1, 2) (beta - 1)) 1);
      [exact S60g1 | exact S60g2]. }
  apply (hsteps_trans _ (HB [135985237; 74737818; 10126538; 1236011; 698173; 177445; 95640; 10129; 1243; 207; 19] 3 1 3 (repeat (1, 2) (beta - 1)) 1)).
  { rewrite NUM60i'. rewrite NUM60j'. rewrite NUM60b.
    apply (hsteps_step _ (HB [S (S (135985236 - 1)); S 74737817; 10126538; 1236011; 698173; 177445; 95640; 10129; 1243; 207; 19] 3 1 3 (repeat (1, 2) (beta - 1)) 1));
      [apply hTRANS2_2; closearith | apply hsteps_refl]. }
  replace (beta + 2) with (3 + (beta - 1)) by lia.
  apply (CASCADE_POPFIN [135985237; 74737818; 10126538; 1236011; 698173; 177445; 95640; 10129; 1243; 207; 19] 3 beta); lia.
Qed.

Print Assumptions TOP60_4.
