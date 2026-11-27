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
               Grind23 Grind24 Grind25 Grind26 Grind26a Grind26b Grind26c.

(* Section equality: componentwise, arithmetic leaves by lia.      *)
Ltac sec_eq :=
  repeat (first [ solve [reflexivity] | solve [lia] | f_equal ]).

(* Closed-numeral arithmetic: literals >= 7426 are parsed as       *)
(* Nat.of_num_uint atoms, which lia cannot relate to variables;    *)
(* for purely closed <= goals the boolean check decides them.      *)
Ltac closearith :=
  first [ lia | apply Nat.leb_le; reflexivity ].

Lemma TOP58_2 : forall beta, 2 <= beta ->
  hsteps (HB [1523948; 426279; 308525; 58213; 30332; 931; 608; 77; 35; 20; 0] 14897638 1 29403093
            ((2, 2) :: (1, 1) :: repeat (1, 2) (beta - 1)) 1)
         (HB [14897639; 1523948; 426279; 308525; 58213; 30332; 931; 608; 77; 35; 20; 0]
            (29403094 + (beta - 1)) 1 (2 * beta + 1) [] 1).
Proof.
  intros beta Hb.
  apply (hsteps_trans _ (HB [14897639; 1523948; 426279; 308525; 58213; 30332; 931; 608; 77; 35; 20; 0] 29403094 1 3 (repeat (1, 2) (beta - 1)) 1)).
  { rewrite NUM58e. rewrite NUM58f. rewrite NUM58g.
    apply (sTRANS2_1 [1523948; 426279; 308525; 58213; 30332; 931; 608; 77; 35; 20; 0] 14897638
           29403092 1 (repeat (1, 2) (beta - 1)) 1); lia. }
  apply (CASCADE_POPFIN [14897639; 1523948; 426279; 308525; 58213; 30332; 931; 608; 77; 35; 20; 0] 29403094 beta); lia.
Qed.

Print Assumptions TOP58_2.
