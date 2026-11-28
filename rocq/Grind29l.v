(* ================================================================= *)
(* Phase 61 (tail): the TOP15 front (TOP61_TO_TOP15). *)
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
               Grind28ab Grind28ae Grind28af Grind28b
               Grind28h Grind28r Grind29a Grind29h Grind29j.
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
(* TOP61_TO_TOP15: the TOP14 state at (2j, 2) reaches TOP15 at     *)
(* the pair (2 * (j - 135985239), 2).  The front is the Phase 60   *)
(* front verbatim at the new constants: the first TUP rewrites     *)
(* via NUM60h (135985236 = 135985237 - 1, inherited from           *)
(* Grind28h.v), the hGRIND_even 67992616 step rewrites the goal    *)
(* by NUM60a / NUM60b, and the TUP2_1 step rewrites via NUM60i' /  *)
(* NUM60b.  The two closed <= premises of the front steps are      *)
(* discharged by the leb lemmas S60h0 / S60g1 / S60g2 / S61a1,     *)
(* never by lia on the 136M atoms.                                 *)
(* ----------------------------------------------------------------- *)

Lemma TOP61_TO_TOP15 : forall j beta, 135985240 <= j -> 2 <= beta ->
  hsteps (HB [10126538; 1236011; 698173; 177445; 95640; 10129; 1243; 207; 19] 74737818 1 135985237
            ((2 * j, 2) :: (1, 1) :: repeat (1, 2) (beta - 1)) 1)
         (HB [47892099; 24915618; 1835911; 568849; 317482; 29175; 9907; 6375; 799; 475; 93; 58; 5] 147491795 1 271970479
            ((2 * (j - 135985239), 2) :: (1, 1)
             :: repeat (1, 2) (beta - 1)) 1).
Proof.
  intros j beta Hj Hb.
  assert (Hj4 : 4 <= j).
  { apply Nat.le_trans with 135985240; [closearith | exact Hj]. }
  assert (Hr : 1 <= j - 135985239).
  { assert (E : 135985239 = 135985240 - 1)
      by (exact S61f1).
    rewrite E. lia. }
  assert (Heq : 2 * j - 6 = 2 * 135985236 + 2 * (j - 135985239)).
  { assert (E1 : 135985239 = S (S (S 135985236)))
      by (exact S61f2).
    assert (E2 : 135985240 = S (S (S (S 135985236))))
      by (exact S61f3).
    rewrite E1. rewrite E2 in Hj. lia. }
  apply (hsteps_trans _ (HC [10126538; 1236011; 698173; 177445; 95640; 10129; 1243; 207; 19] 74737818
    135985236 2 ((2 * j - 2, 2) :: (1, 1) :: repeat (1, 2) (beta - 1)) 1)).
  { rewrite NUM60h.
    apply (sTUP [10126538; 1236011; 698173; 177445; 95640; 10129; 1243; 207; 19] 74737818 135985237 (2 * j) 2
           ((1, 1) :: repeat (1, 2) (beta - 1)) 1);
      [exact S60h0 | lia]. }
  apply (hsteps_trans _ (HB [10126538; 1236011; 698173; 177445; 95640; 10129; 1243; 207; 19]
    74737817 1 135985236 ((2, 2) :: (2 * j - 2, 2) :: (1, 1)
            :: repeat (1, 2) (beta - 1)) 1)).
  { rewrite NUM60a. rewrite NUM60b.
    apply (hGRIND_even 67992616 [10126538; 1236011; 698173; 177445; 95640; 10129; 1243; 207; 19]
           74737817 ((2 * j - 2, 2) :: (1, 1) :: repeat (1, 2) (beta - 1))
           1); [exact S60g1 | exact S60g2]. }
  apply (hsteps_trans _ (HC [74737818; 10126538; 1236011; 698173; 177445; 95640; 10129; 1243; 207; 19] 135985236 1 2 ((2 * j - 4, 2) :: (1, 1)
            :: repeat (1, 2) (beta - 1)) 1)).
  { rewrite NUM60i'. rewrite NUM60b.
    assert (E : ((2 * j - 2 - 2, 2) :: (1, 1) :: repeat (1, 2) (beta - 1))
              = ((2 * j - 4, 2) :: (1, 1) :: repeat (1, 2) (beta - 1)))
      by sec_eq.
    rewrite <- E.
    apply (sTUP2_1 [10126538; 1236011; 698173; 177445; 95640; 10129; 1243; 207; 19] 74737817
           (135985236 - 1) (2 * j - 2) ((1, 1) :: repeat (1, 2) (beta - 1))
           1); lia. }
  apply (hsteps_trans _ (HB [74737818; 10126538; 1236011; 698173; 177445; 95640; 10129; 1243; 207; 19] 135985236 1 4 ((2 * j - 4, 2) :: (1, 1)
            :: repeat (1, 2) (beta - 1)) 1)).
  { apply (sTDN [74737818; 10126538; 1236011; 698173; 177445; 95640; 10129; 1243; 207; 19] 135985236
           ((2 * j - 4, 2) :: (1, 1) :: repeat (1, 2) (beta - 1))
           1). }
  apply (hsteps_trans _ (HC [74737818; 10126538; 1236011; 698173; 177445; 95640; 10129; 1243; 207; 19] 135985236 3 2 ((2 * j - 6, 2) :: (1, 1)
            :: repeat (1, 2) (beta - 1)) 1)).
  { assert (E : ((2 * j - 4 - 2, 2) :: (1, 1) :: repeat (1, 2) (beta - 1))
              = ((2 * j - 6, 2) :: (1, 1) :: repeat (1, 2) (beta - 1)))
      by sec_eq.
    rewrite <- E.
    apply (sTUP [74737818; 10126538; 1236011; 698173; 177445; 95640; 10129; 1243; 207; 19] 135985236
           4 (2 * j - 4) 2 ((1, 1) :: repeat (1, 2) (beta - 1)) 1);
      lia. }
  apply (hsteps_trans _ (HC [74737818; 10126538; 1236011; 698173; 177445; 95640; 10129; 1243; 207; 19]
    0 3 2 (repeat (1, 2) 135985236
     ++ ((2 * (j - 135985239), 2) :: (1, 1)
         :: repeat (1, 2) (beta - 1))) 1)).
  { rewrite Heq.
    apply (DIPGRIND 135985236 (2 * (j - 135985239))
           [74737818; 10126538; 1236011; 698173; 177445; 95640; 10129; 1243; 207; 19]
           ((1, 1) :: repeat (1, 2) (beta - 1)) 1);
      [exact S61a1 | lia]. }
  apply (CASCADE61 ((2 * (j - 135985239), 2) :: (1, 1)
                    :: repeat (1, 2) (beta - 1))).
Qed.

Print Assumptions TOP61_TO_TOP15.
