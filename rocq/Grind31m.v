(* ================================================================= *)
(* Phase 63 (tail): the r17 = 2 closing (TOP63_2). *)
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
               Grind31a.
(* Section equality: componentwise, arithmetic leaves by lia.      *)
Ltac sec_eq :=
  repeat (first [ solve [reflexivity] | solve [lia] | f_equal ]).

(* Closed-numeral arithmetic: literals >= 7426 are parsed as       *)
(* Nat.of_num_uint atoms, which lia cannot relate to variables;    *)
(* for purely closed <= goals the boolean check decides them.      *)
Ltac closearith :=
  first [ lia
        | cbn [Nat.of_num_uint Nat.of_uint Nat.of_uint_acc];
          try (rewrite !Nat.tail_mul_spec); nia ].

Lemma TOP63_2 : forall beta, 2 <= beta ->
  hsteps (HB [130856035; 65515088; 349423; 101323; 57668; 5526; 626; 189; 112; 33; 19; 0] 842094153 1 1191297119
            ((2, 2) :: (1, 1) :: repeat (1, 2) (beta - 1)) 1)
         (HB [842094154; 130856035; 65515088; 349423; 101323; 57668; 5526; 626; 189; 112; 33; 19; 0]
            (1191297120 + (beta - 1)) 1 (2 * beta + 1) [] 1).
Proof.
  intros beta Hb.
  apply (hsteps_trans _ (HB [842094154; 130856035; 65515088; 349423; 101323; 57668; 5526; 626; 189; 112; 33; 19; 0] 1191297120 1 3 (repeat (1, 2) (beta - 1)) 1)).
  { rewrite NUM63e'. rewrite NUM63f'. rewrite NUM63g.
    apply (sTRANS2_1 [130856035; 65515088; 349423; 101323; 57668; 5526; 626; 189; 112; 33; 19; 0] 842094153
           (1191297119 - 1) 1 (repeat (1, 2) (beta - 1)) 1); lia. }
  apply (CASCADE_POPFIN [842094154; 130856035; 65515088; 349423; 101323; 57668; 5526; 626; 189; 112; 33; 19; 0] 1191297120 beta); lia.
Qed.

Print Assumptions TOP63_2.
