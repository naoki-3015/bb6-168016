(* ================================================================= *)
(* Phase 60 (tail): the r14' = 2 closing (TOP60_2).  Split from    *)
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
               Grind28ad Grind28e Grind28k Grind28q.
(* Section equality: componentwise, arithmetic leaves by lia.      *)
Ltac sec_eq :=
  repeat (first [ solve [reflexivity] | solve [lia] | f_equal ]).

(* Closed-numeral arithmetic: literals >= 7426 are parsed as       *)
(* Nat.of_num_uint atoms, which lia cannot relate to variables;    *)
(* for purely closed <= goals the boolean check decides them.      *)
Ltac closearith :=
  first [ lia | apply Nat.leb_le; reflexivity ].

Lemma TOP60_2 : forall beta, 2 <= beta ->
  hsteps (HB [10126538; 1236011; 698173; 177445; 95640; 10129; 1243; 207; 19] 74737818 1 135985237
            ((2, 2) :: (1, 1) :: repeat (1, 2) (beta - 1)) 1)
         (HB [74737819; 10126538; 1236011; 698173; 177445; 95640; 10129; 1243; 207; 19]
            (135985238 + (beta - 1)) 1 (2 * beta + 1) [] 1).
Proof.
  intros beta Hb.
  apply (hsteps_trans _ (HB [74737819; 10126538; 1236011; 698173; 177445; 95640; 10129; 1243; 207; 19] 135985238 1 3 (repeat (1, 2) (beta - 1)) 1)).
  { rewrite NUM60e'. rewrite NUM60f'. rewrite NUM60g.
    apply (sTRANS2_1 [10126538; 1236011; 698173; 177445; 95640; 10129; 1243; 207; 19] 74737818
           (135985237 - 1) 1 (repeat (1, 2) (beta - 1)) 1); lia. }
  apply (CASCADE_POPFIN [74737819; 10126538; 1236011; 698173; 177445; 95640; 10129; 1243; 207; 19] 135985238 beta); lia.
Qed.

Print Assumptions TOP60_2.
