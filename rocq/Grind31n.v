(* ================================================================= *)
(* Phase 63 (tail): the r17 = 4 closing (TOP63_4). *)
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
               Grind31a Grind31ab Grind31h.
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

Lemma TOP63_4 : forall beta, 2 <= beta ->
  hsteps (HB [130856035; 65515088; 349423; 101323; 57668; 5526; 626; 189; 112; 33; 19; 0] 842094153 1 1191297119
            ((4, 2) :: (1, 1) :: repeat (1, 2) (beta - 1)) 1)
         (HB [1191297119; 842094153; 130856035; 65515088; 349423; 101323; 57668; 5526; 626; 189; 112; 33; 19; 0]
            (beta + 2) 1 (2 * beta + 1) [] 1).
Proof.
  intros beta Hb.
  apply (hsteps_trans _ (HC [130856035; 65515088; 349423; 101323; 57668; 5526; 626; 189; 112; 33; 19; 0]
    842094153 1191297118 2
    ((2, 2) :: (1, 1) :: repeat (1, 2) (beta - 1)) 1)).
  { rewrite NUM63h.
    apply (sTUP [130856035; 65515088; 349423; 101323; 57668; 5526; 626; 189; 112; 33; 19; 0] 842094153 1191297119
           4 2 ((1, 1) :: repeat (1, 2) (beta - 1)) 1);
      [exact S63h0 | lia]. }
  apply (hsteps_trans _ (HB [130856035; 65515088; 349423; 101323; 57668; 5526; 626; 189; 112; 33; 19; 0]
    842094152 1 1191297118 ((2, 2) :: (2, 2) :: (1, 1)
            :: repeat (1, 2) (beta - 1)) 1)).
  { rewrite NUM63a. rewrite NUM63b.
    apply (hGRIND_even 595648557 [130856035; 65515088; 349423; 101323; 57668; 5526; 626; 189; 112; 33; 19; 0]
           842094152 ((2, 2) :: (1, 1) :: repeat (1, 2) (beta - 1)) 1);
      [exact S63g1 | exact S63g2]. }
  apply (hsteps_trans _ (HB [1191297119; 842094153; 130856035; 65515088; 349423; 101323; 57668; 5526; 626; 189; 112; 33; 19; 0] 3 1 3 (repeat (1, 2) (beta - 1)) 1)).
  { rewrite NUM63i'. rewrite NUM63j'. rewrite NUM63b.
    apply (hsteps_step _ (HB [S (S (1191297119 - 1 - 1)); S (842094153 - 1); 130856035; 65515088; 349423; 101323; 57668; 5526; 626; 189; 112; 33; 19; 0] 3 1 3 (repeat (1, 2) (beta - 1)) 1));
      [apply hTRANS2_2; closearith | apply hsteps_refl]. }
  replace (beta + 2) with (3 + (beta - 1)) by lia.
  apply (CASCADE_POPFIN [1191297119; 842094153; 130856035; 65515088; 349423; 101323; 57668; 5526; 626; 189; 112; 33; 19; 0] 3 beta); lia.
Qed.

Print Assumptions TOP63_4.
