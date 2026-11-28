(* ================================================================= *)
(* Phase 63 (tail): the TOP17 front (TOP63_TO_TOP17). *)
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
               Grind30a Grind30ab Grind30h
               Grind31a Grind31h Grind31j.
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
(* TOP63_TO_TOP17: the TOP16 state at (2j, 2) reaches TOP17 at     *)
(* the pair (2 * (j - 595648559), 2).  The front is the Phase 62   *)
(* front verbatim at the new constants: the first TUP rewrites     *)
(* via NUM62h (595648556 = 595648557 - 1, inherited from           *)
(* Grind30a.v), the hGRIND_even 297824276 step rewrites the goal   *)
(* by NUM62a / NUM62b, and the TUP2_1 step rewrites via NUM62i' /  *)
(* NUM62b.  The two closed <= premises of the front steps are      *)
(* discharged by the leb lemmas S62h0 / S62g1 / S62g2 / S63a1,     *)
(* never by lia on the 595M atoms.                                 *)
(* ----------------------------------------------------------------- *)

Lemma TOP63_TO_TOP17 : forall j beta, 595648560 <= j -> 2 <= beta ->
  hsteps (HB [60654542; 9546949; 4860546; 349423; 101323; 57668; 5526; 626; 189; 112; 33; 19; 0] 367754682 1 595648557
            ((2 * j, 2) :: (1, 1) :: repeat (1, 2) (beta - 1)) 1)
         (HB [130856035; 65515088; 349423; 101323; 57668; 5526; 626; 189; 112; 33; 19; 0] 842094153 1 1191297119
            ((2 * (j - 595648559), 2) :: (1, 1)
             :: repeat (1, 2) (beta - 1)) 1).
Proof.
  intros j beta Hj Hb.
  assert (Hj4 : 4 <= j).
  { apply Nat.le_trans with 595648560; [closearith | exact Hj]. }
  assert (Hr : 1 <= j - 595648559).
  { assert (E : 595648559 = 595648560 - 1)
      by (exact S63f1).
    rewrite E. lia. }
  assert (Heq : 2 * j - 6 = 2 * 595648556 + 2 * (j - 595648559)).
  { assert (E1 : 595648559 = S (S (S 595648556)))
      by (exact S63f2).
    assert (E2 : 595648560 = S (S (S (S 595648556))))
      by (exact S63f3).
    rewrite E1. rewrite E2 in Hj. lia. }
  apply (hsteps_trans _ (HC [60654542; 9546949; 4860546; 349423; 101323; 57668; 5526; 626; 189; 112; 33; 19; 0] 367754682
    595648556 2 ((2 * j - 2, 2) :: (1, 1) :: repeat (1, 2) (beta - 1)) 1)).
  { rewrite NUM62h.
    apply (sTUP [60654542; 9546949; 4860546; 349423; 101323; 57668; 5526; 626; 189; 112; 33; 19; 0] 367754682 595648557 (2 * j) 2
           ((1, 1) :: repeat (1, 2) (beta - 1)) 1);
      [exact S62h0 | lia]. }
  apply (hsteps_trans _ (HB [60654542; 9546949; 4860546; 349423; 101323; 57668; 5526; 626; 189; 112; 33; 19; 0]
    367754681 1 595648556 ((2, 2) :: (2 * j - 2, 2) :: (1, 1)
            :: repeat (1, 2) (beta - 1)) 1)).
  { rewrite NUM62a. rewrite NUM62b.
    apply (hGRIND_even 297824276 [60654542; 9546949; 4860546; 349423; 101323; 57668; 5526; 626; 189; 112; 33; 19; 0]
           367754681 ((2 * j - 2, 2) :: (1, 1) :: repeat (1, 2) (beta - 1))
           1); [exact S62g1 | exact S62g2]. }
  apply (hsteps_trans _ (HC [367754682; 60654542; 9546949; 4860546; 349423; 101323; 57668; 5526; 626; 189; 112; 33; 19; 0] 595648556 1 2 ((2 * j - 4, 2) :: (1, 1)
            :: repeat (1, 2) (beta - 1)) 1)).
  { rewrite NUM62i'. rewrite NUM62b.
    assert (E : ((2 * j - 2 - 2, 2) :: (1, 1) :: repeat (1, 2) (beta - 1))
              = ((2 * j - 4, 2) :: (1, 1) :: repeat (1, 2) (beta - 1)))
      by sec_eq.
    rewrite <- E.
    apply (sTUP2_1 [60654542; 9546949; 4860546; 349423; 101323; 57668; 5526; 626; 189; 112; 33; 19; 0] 367754681
           (595648556 - 1) (2 * j - 2) ((1, 1) :: repeat (1, 2) (beta - 1))
           1); lia. }
  apply (hsteps_trans _ (HB [367754682; 60654542; 9546949; 4860546; 349423; 101323; 57668; 5526; 626; 189; 112; 33; 19; 0] 595648556 1 4 ((2 * j - 4, 2) :: (1, 1)
            :: repeat (1, 2) (beta - 1)) 1)).
  { apply (sTDN [367754682; 60654542; 9546949; 4860546; 349423; 101323; 57668; 5526; 626; 189; 112; 33; 19; 0] 595648556
           ((2 * j - 4, 2) :: (1, 1) :: repeat (1, 2) (beta - 1))
           1). }
  apply (hsteps_trans _ (HC [367754682; 60654542; 9546949; 4860546; 349423; 101323; 57668; 5526; 626; 189; 112; 33; 19; 0] 595648556 3 2 ((2 * j - 6, 2) :: (1, 1)
            :: repeat (1, 2) (beta - 1)) 1)).
  { assert (E : ((2 * j - 4 - 2, 2) :: (1, 1) :: repeat (1, 2) (beta - 1))
              = ((2 * j - 6, 2) :: (1, 1) :: repeat (1, 2) (beta - 1)))
      by sec_eq.
    rewrite <- E.
    apply (sTUP [367754682; 60654542; 9546949; 4860546; 349423; 101323; 57668; 5526; 626; 189; 112; 33; 19; 0] 595648556
           4 (2 * j - 4) 2 ((1, 1) :: repeat (1, 2) (beta - 1)) 1);
      lia. }
  apply (hsteps_trans _ (HC [367754682; 60654542; 9546949; 4860546; 349423; 101323; 57668; 5526; 626; 189; 112; 33; 19; 0]
    0 3 2 (repeat (1, 2) 595648556
     ++ ((2 * (j - 595648559), 2) :: (1, 1)
         :: repeat (1, 2) (beta - 1))) 1)).
  { rewrite Heq.
    apply (DIPGRIND 595648556 (2 * (j - 595648559))
           [367754682; 60654542; 9546949; 4860546; 349423; 101323; 57668; 5526; 626; 189; 112; 33; 19; 0]
           ((1, 1) :: repeat (1, 2) (beta - 1)) 1);
      [exact S63a1 | lia]. }
  apply (CASCADE63 ((2 * (j - 595648559), 2) :: (1, 1)
                    :: repeat (1, 2) (beta - 1))).
Qed.

Print Assumptions TOP63_TO_TOP17.
