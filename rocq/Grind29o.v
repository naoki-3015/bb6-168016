(* ================================================================= *)
(* Phase 61 (tail): the r15' = 6 closing (TOP61_6). *)
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
               Grind29a Grind29ab Grind29h.
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

Lemma TOP61_6 : forall beta, 2 <= beta ->
  hsteps (HB [47892099; 24915618; 1835911; 568849; 317482; 29175; 9907; 6375; 799; 475; 93; 58; 5] 147491795 1 271970479
            ((6, 2) :: (1, 1) :: repeat (1, 2) (beta - 1)) 1)
         (HB [271970479; 147491795; 47892099; 24915618; 1835911; 568849; 317482; 29175; 9907; 6375; 799; 475; 93; 58; 5]
            (beta + 4) 1 (2 * beta + 1) [] 1).
Proof.
  intros beta Hb.
  apply (hsteps_trans _ (HC [47892099; 24915618; 1835911; 568849; 317482; 29175; 9907; 6375; 799; 475; 93; 58; 5]
    147491795 271970478 2
    ((4, 2) :: (1, 1) :: repeat (1, 2) (beta - 1)) 1)).
  { rewrite NUM61h.
    apply (sTUP [47892099; 24915618; 1835911; 568849; 317482; 29175; 9907; 6375; 799; 475; 93; 58; 5] 147491795 271970479
           6 2 ((1, 1) :: repeat (1, 2) (beta - 1)) 1);
      [exact S61h0 | lia]. }
  apply (hsteps_trans _ (HB [47892099; 24915618; 1835911; 568849; 317482; 29175; 9907; 6375; 799; 475; 93; 58; 5]
    147491794 1 271970478 ((2, 2) :: (4, 2) :: (1, 1)
            :: repeat (1, 2) (beta - 1)) 1)).
  { rewrite NUM61a. rewrite NUM61b.
    apply (hGRIND_even 135985237 [47892099; 24915618; 1835911; 568849; 317482; 29175; 9907; 6375; 799; 475; 93; 58; 5]
           147491794 ((4, 2) :: (1, 1) :: repeat (1, 2) (beta - 1)) 1);
      [exact S61g1 | exact S61g2]. }
  apply (hsteps_trans _ (HC [147491795; 47892099; 24915618; 1835911; 568849; 317482; 29175; 9907; 6375; 799; 475; 93; 58; 5] 271970478 1 2
    ((2, 2) :: (1, 1) :: repeat (1, 2) (beta - 1)) 1)).
  { rewrite NUM61i'. rewrite NUM61b.
    assert (E : ((4 - 2, 2) :: (1, 1) :: repeat (1, 2) (beta - 1))
              = ((2, 2) :: (1, 1) :: repeat (1, 2) (beta - 1)))
      by sec_eq.
    rewrite <- E.
    apply (sTUP2_1 [47892099; 24915618; 1835911; 568849; 317482; 29175; 9907; 6375; 799; 475; 93; 58; 5] 147491794
           (271970479 - 1 - 1) 4 ((1, 1) :: repeat (1, 2) (beta - 1)) 1); lia. }
  apply (hsteps_trans _ (HB [147491795; 47892099; 24915618; 1835911; 568849; 317482; 29175; 9907; 6375; 799; 475; 93; 58; 5] 271970478 1 4
    ((2, 2) :: (1, 1) :: repeat (1, 2) (beta - 1)) 1)).
  { apply (sTDN [147491795; 47892099; 24915618; 1835911; 568849; 317482; 29175; 9907; 6375; 799; 475; 93; 58; 5] 271970478
           ((2, 2) :: (1, 1) :: repeat (1, 2) (beta - 1))
           1). }
  apply (hsteps_trans _ (HB [271970479; 147491795; 47892099; 24915618; 1835911; 568849; 317482; 29175; 9907; 6375; 799; 475; 93; 58; 5] 5 1 3 (repeat (1, 2) (beta - 1)) 1)).
  { rewrite NUM61e'.
    apply (sTRANS2_1 [147491795; 47892099; 24915618; 1835911; 568849; 317482; 29175; 9907; 6375; 799; 475; 93; 58; 5]
           (271970479 - 1) 3 1 (repeat (1, 2) (beta - 1)) 1); lia. }
  replace (beta + 4) with (5 + (beta - 1)) by lia.
  apply (CASCADE_POPFIN [271970479; 147491795; 47892099; 24915618; 1835911; 568849; 317482; 29175; 9907; 6375; 799; 475; 93; 58; 5] 5 beta); lia.
Qed.

Print Assumptions TOP61_6.
