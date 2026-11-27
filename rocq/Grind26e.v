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
               Grind23 Grind24 Grind25 Grind26 Grind26a Grind26b Grind26c Grind26d.

(* Section equality: componentwise, arithmetic leaves by lia.      *)
Ltac sec_eq :=
  repeat (first [ solve [reflexivity] | solve [lia] | f_equal ]).

(* Closed-numeral arithmetic: literals >= 7426 are parsed as       *)
(* Nat.of_num_uint atoms, which lia cannot relate to variables;    *)
(* for purely closed <= goals the boolean check decides them.      *)
Ltac closearith :=
  first [ lia | apply Nat.leb_le; reflexivity ].

Lemma TOP58_4 : forall beta, 2 <= beta ->
  hsteps (HB [1523948; 426279; 308525; 58213; 30332; 931; 608; 77; 35; 20; 0] 14897638 1 29403093
            ((4, 2) :: (1, 1) :: repeat (1, 2) (beta - 1)) 1)
         (HB [29403093; 14897638; 1523948; 426279; 308525; 58213; 30332; 931; 608; 77; 35; 20; 0]
            (beta + 2) 1 (2 * beta + 1) [] 1).
Proof.
  intros beta Hb.
  apply (hsteps_trans _ (HC [1523948; 426279; 308525; 58213; 30332; 931; 608; 77; 35; 20; 0]
    14897638 29403092 2
    ((2, 2) :: (1, 1) :: repeat (1, 2) (beta - 1)) 1)).
  { rewrite NUM58h.
    apply (sTUP [1523948; 426279; 308525; 58213; 30332; 931; 608; 77; 35; 20; 0] 14897638 29403093
           4 2 ((1, 1) :: repeat (1, 2) (beta - 1)) 1); closearith. }
  apply (hsteps_trans _ (HB [1523948; 426279; 308525; 58213; 30332; 931; 608; 77; 35; 20; 0]
    14897637 1 29403092 ((2, 2) :: (2, 2) :: (1, 1)
            :: repeat (1, 2) (beta - 1)) 1)).
  { rewrite NUM58a. rewrite NUM58b.
    apply (hGRIND_even 14701544 [1523948; 426279; 308525; 58213; 30332; 931; 608; 77; 35; 20; 0]
           14897637 ((2, 2) :: (1, 1) :: repeat (1, 2) (beta - 1)) 1);
      [exact S58g1 | exact S58g2]. }
  apply (hsteps_trans _ (HB [29403093; 14897638; 1523948; 426279; 308525; 58213; 30332; 931; 608; 77; 35; 20; 0] 3 1 3 (repeat (1, 2) (beta - 1)) 1)).
  { rewrite NUM58i. rewrite NUM58j. rewrite NUM58b.
    apply (hsteps_step _ (HB [S (S 29403091); S 14897637; 1523948; 426279; 308525; 58213; 30332; 931; 608; 77; 35; 20; 0] 3 1 3 (repeat (1, 2) (beta - 1)) 1));
      [apply hTRANS2_2; closearith | apply hsteps_refl]. }
  replace (beta + 2) with (3 + (beta - 1)) by lia.
  apply (CASCADE_POPFIN [29403093; 14897638; 1523948; 426279; 308525; 58213; 30332; 931; 608; 77; 35; 20; 0] 3 beta); lia.
Qed.

Print Assumptions TOP58_4.
