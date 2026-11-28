(* ================================================================= *)
(* Phase 62 (tail): the TOP16 front (TOP62_TO_TOP16). *)
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
               Grind29a Grind29ab Grind29h
               Grind30a Grind30h Grind30j.
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

(* ----------------------------------------------------------------- *)
(* TOP62_TO_TOP16: the TOP15 state at (2j, 2) reaches TOP16 at     *)
(* the pair (2 * (j - 271970481), 2).  The front is the Phase 61   *)
(* front verbatim at the new constants: the first TUP rewrites     *)
(* via NUM61h (271970478 = 271970479 - 1, inherited from           *)
(* Grind29a.v), the hGRIND_even 135985237 step rewrites the goal   *)
(* by NUM61a / NUM61b, and the TUP2_1 step rewrites via NUM61i' /  *)
(* NUM61b.  The two closed <= premises of the front steps are      *)
(* discharged by the leb lemmas S61h0 / S61g1 / S61g2 / S62a1,     *)
(* never by lia on the 272M atoms.                                 *)
(* ----------------------------------------------------------------- *)

Lemma TOP62_TO_TOP16 : forall j beta, 271970482 <= j -> 2 <= beta ->
  hsteps (HB [47892099; 24915618; 1835911; 568849; 317482; 29175; 9907; 6375; 799; 475; 93; 58; 5] 147491795 1 271970479
            ((2 * j, 2) :: (1, 1) :: repeat (1, 2) (beta - 1)) 1)
         (HB [60654542; 9546949; 4860546; 349423; 101323; 57668; 5526; 626; 189; 112; 33; 19; 0] 367754682 1 595648557
            ((2 * (j - 271970481), 2) :: (1, 1)
             :: repeat (1, 2) (beta - 1)) 1).
Proof.
  intros j beta Hj Hb.
  assert (Hj4 : 4 <= j).
  { apply Nat.le_trans with 271970482; [closearith | exact Hj]. }
  assert (Hr : 1 <= j - 271970481).
  { assert (E : 271970481 = 271970482 - 1)
      by (exact S62f1).
    rewrite E. lia. }
  assert (Heq : 2 * j - 6 = 2 * 271970478 + 2 * (j - 271970481)).
  { assert (E1 : 271970481 = S (S (S 271970478)))
      by (exact S62f2).
    assert (E2 : 271970482 = S (S (S (S 271970478))))
      by (exact S62f3).
    rewrite E1. rewrite E2 in Hj. lia. }
  apply (hsteps_trans _ (HC [47892099; 24915618; 1835911; 568849; 317482; 29175; 9907; 6375; 799; 475; 93; 58; 5] 147491795
    271970478 2 ((2 * j - 2, 2) :: (1, 1) :: repeat (1, 2) (beta - 1)) 1)).
  { rewrite NUM61h.
    apply (sTUP [47892099; 24915618; 1835911; 568849; 317482; 29175; 9907; 6375; 799; 475; 93; 58; 5] 147491795 271970479 (2 * j) 2
           ((1, 1) :: repeat (1, 2) (beta - 1)) 1);
      [exact S61h0 | lia]. }
  apply (hsteps_trans _ (HB [47892099; 24915618; 1835911; 568849; 317482; 29175; 9907; 6375; 799; 475; 93; 58; 5]
    147491794 1 271970478 ((2, 2) :: (2 * j - 2, 2) :: (1, 1)
            :: repeat (1, 2) (beta - 1)) 1)).
  { rewrite NUM61a. rewrite NUM61b.
    apply (hGRIND_even 135985237 [47892099; 24915618; 1835911; 568849; 317482; 29175; 9907; 6375; 799; 475; 93; 58; 5]
           147491794 ((2 * j - 2, 2) :: (1, 1) :: repeat (1, 2) (beta - 1))
           1); [exact S61g1 | exact S61g2]. }
  apply (hsteps_trans _ (HC [147491795; 47892099; 24915618; 1835911; 568849; 317482; 29175; 9907; 6375; 799; 475; 93; 58; 5] 271970478 1 2 ((2 * j - 4, 2) :: (1, 1)
            :: repeat (1, 2) (beta - 1)) 1)).
  { rewrite NUM61i'. rewrite NUM61b.
    assert (E : ((2 * j - 2 - 2, 2) :: (1, 1) :: repeat (1, 2) (beta - 1))
              = ((2 * j - 4, 2) :: (1, 1) :: repeat (1, 2) (beta - 1)))
      by sec_eq.
    rewrite <- E.
    apply (sTUP2_1 [47892099; 24915618; 1835911; 568849; 317482; 29175; 9907; 6375; 799; 475; 93; 58; 5] 147491794
           (271970478 - 1) (2 * j - 2) ((1, 1) :: repeat (1, 2) (beta - 1))
           1); lia. }
  apply (hsteps_trans _ (HB [147491795; 47892099; 24915618; 1835911; 568849; 317482; 29175; 9907; 6375; 799; 475; 93; 58; 5] 271970478 1 4 ((2 * j - 4, 2) :: (1, 1)
            :: repeat (1, 2) (beta - 1)) 1)).
  { apply (sTDN [147491795; 47892099; 24915618; 1835911; 568849; 317482; 29175; 9907; 6375; 799; 475; 93; 58; 5] 271970478
           ((2 * j - 4, 2) :: (1, 1) :: repeat (1, 2) (beta - 1))
           1). }
  apply (hsteps_trans _ (HC [147491795; 47892099; 24915618; 1835911; 568849; 317482; 29175; 9907; 6375; 799; 475; 93; 58; 5] 271970478 3 2 ((2 * j - 6, 2) :: (1, 1)
            :: repeat (1, 2) (beta - 1)) 1)).
  { assert (E : ((2 * j - 4 - 2, 2) :: (1, 1) :: repeat (1, 2) (beta - 1))
              = ((2 * j - 6, 2) :: (1, 1) :: repeat (1, 2) (beta - 1)))
      by sec_eq.
    rewrite <- E.
    apply (sTUP [147491795; 47892099; 24915618; 1835911; 568849; 317482; 29175; 9907; 6375; 799; 475; 93; 58; 5] 271970478
           4 (2 * j - 4) 2 ((1, 1) :: repeat (1, 2) (beta - 1)) 1);
      lia. }
  apply (hsteps_trans _ (HC [147491795; 47892099; 24915618; 1835911; 568849; 317482; 29175; 9907; 6375; 799; 475; 93; 58; 5]
    0 3 2 (repeat (1, 2) 271970478
     ++ ((2 * (j - 271970481), 2) :: (1, 1)
         :: repeat (1, 2) (beta - 1))) 1)).
  { rewrite Heq.
    apply (DIPGRIND 271970478 (2 * (j - 271970481))
           [147491795; 47892099; 24915618; 1835911; 568849; 317482; 29175; 9907; 6375; 799; 475; 93; 58; 5]
           ((1, 1) :: repeat (1, 2) (beta - 1)) 1);
      [exact S62a1 | lia]. }
  apply (CASCADE62 ((2 * (j - 271970481), 2) :: (1, 1)
                    :: repeat (1, 2) (beta - 1))).
Qed.

Print Assumptions TOP62_TO_TOP16.
