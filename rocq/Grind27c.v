(* ================================================================= *)
(* Phase 59 (tail): the TOP13 closings, the residual core          *)
(* TAIL2_END14, TAIL2_END13_of59 and ESC_ERA_LAW_59.  Split from    *)
(* Grind27.v / Grind27b.v for the operational reason recorded in    *)
(* Grind27b.v's header (compile resident set at Phase 59 numeral    *)
(* depths); every lemma statement is the one the phase's single-    *)
(* file draft carried.  The phase narrative lives in Grind27.v's    *)
(* header.                                                          *)
(* ================================================================= *)

Require Import List Bool Arith Lia ZArith.
Import ListNotations.
Require Import TM Sections Mirror TokenPass Recoord Era Esc Dev
               Grind Grind2 Grind3 Grind4 Grind5 Grind6 Grind7 Grind8
               Grind9 Grind10 Grind11 Grind12 Grind13 Grind14 Grind15
               Grind16 Grind17 Grind18 Grind19 Grind20 Grind21 Grind22
               Grind23 Grind24 Grind25 Grind26 Grind26a Grind26b
               Grind26c Grind26d Grind26e Grind26f Grind26g Grind27a
               Grind27b.

(* Section equality: componentwise, arithmetic leaves by lia.      *)
Ltac sec_eq :=
  repeat (first [ solve [reflexivity] | solve [lia] | f_equal ]).

(* Closed-numeral arithmetic: literals >= 7426 are parsed as       *)
(* Nat.of_num_uint atoms, which lia cannot relate to variables;    *)
(* for purely closed <= goals the boolean check decides them.      *)
Ltac closearith :=
  first [ lia | apply Nat.leb_le; reflexivity ].


(* ----------------------------------------------------------------- *)
(* TOP59_TO_TOP13: the TOP12 state at (2j, 2) reaches TOP13 at the   *)
(* pair (2 * (j - 29403095), 2).  The front is the Phase 58 front     *)
(* verbatim at the new constants: the first TUP rewrites via         *)
(* NUM58h (29403092 = 29403093 - 1, inherited from Grind26.v), the   *)
(* hGRIND_even 14701544 step rewrites the goal by NUM58a / NUM58b    *)
(* (29403092 = 2 * 14701544 + 4, 14897638 = S 14897637), and the      *)
(* TUP2_1 step rewrites via NUM58i (29403092 = S 29403091) / NUM58b. *)
(* The two closed <= premises of the front steps are discharged by  *)
(* the leb lemmas S59g0 / S58g1 / S58g2 / S59a1, never by lia on the  *)
(* 29.4M atoms.                                                      *)
(* ----------------------------------------------------------------- *)

Lemma TOP59_TO_TOP13 : forall j beta, 29403096 <= j -> 2 <= beta ->
  hsteps (HB [1523948; 426279; 308525; 58213; 30332; 931; 608; 77; 35; 20; 0] 14897638 1 29403093
            ((2 * j, 2) :: (1, 1) :: repeat (1, 2) (beta - 1)) 1)
         (HB [7965811; 4012920; 308090; 49409; 7710; 1059; 199; 101; 0] 34304475 1 58806191
            ((2 * (j - 29403095), 2) :: (1, 1)
             :: repeat (1, 2) (beta - 1)) 1).
Proof.
  intros j beta Hj Hb.
  assert (Hj4 : 4 <= j).
  { apply Nat.le_trans with 29403096; [closearith | exact Hj]. }
  assert (Hr : 1 <= j - 29403095).
  { assert (E : 29403095 = 29403096 - 1)
      by (exact S59f1).
    rewrite E. lia. }
  assert (Heq : 2 * j - 6 = 2 * 29403092 + 2 * (j - 29403095)).
  { assert (E1 : 29403095 = 29403092 + 3)
      by (exact S59f2).
    assert (E2 : 29403096 = 29403092 + 4)
      by (exact S59f3).
    rewrite E1. rewrite E2 in Hj. lia. }
  apply (hsteps_trans _ (HC [1523948; 426279; 308525; 58213; 30332; 931; 608; 77; 35; 20; 0] 14897638
    29403092 2 ((2 * j - 2, 2) :: (1, 1) :: repeat (1, 2) (beta - 1)) 1)).
  { rewrite NUM58h.
    apply (sTUP [1523948; 426279; 308525; 58213; 30332; 931; 608; 77; 35; 20; 0] 14897638 29403093 (2 * j) 2
           ((1, 1) :: repeat (1, 2) (beta - 1)) 1);
      [exact S59g0 | lia]. }
  apply (hsteps_trans _ (HB [1523948; 426279; 308525; 58213; 30332; 931; 608; 77; 35; 20; 0]
    14897637 1 29403092 ((2, 2) :: (2 * j - 2, 2) :: (1, 1)
            :: repeat (1, 2) (beta - 1)) 1)).
  { rewrite NUM58a. rewrite NUM58b.
    apply (hGRIND_even 14701544 [1523948; 426279; 308525; 58213; 30332; 931; 608; 77; 35; 20; 0]
           14897637 ((2 * j - 2, 2) :: (1, 1) :: repeat (1, 2) (beta - 1))
           1); [exact S58g1 | exact S58g2]. }
  apply (hsteps_trans _ (HC [14897638; 1523948; 426279; 308525; 58213; 30332; 931; 608; 77; 35; 20; 0] 29403092 1 2 ((2 * j - 4, 2) :: (1, 1)
            :: repeat (1, 2) (beta - 1)) 1)).
  { rewrite NUM58i. rewrite NUM58b.
    replace ((2 * j - 4, 2) :: (1, 1) :: repeat (1, 2) (beta - 1))
      with ((2 * j - 2 - 2, 2) :: (1, 1) :: repeat (1, 2) (beta - 1))
      by sec_eq.
    apply (sTUP2_1 [1523948; 426279; 308525; 58213; 30332; 931; 608; 77; 35; 20; 0] 14897637
           29403091 (2 * j - 2) ((1, 1) :: repeat (1, 2) (beta - 1)) 1); lia. }
  apply (hsteps_trans _ (HB [14897638; 1523948; 426279; 308525; 58213; 30332; 931; 608; 77; 35; 20; 0] 29403092 1 4 ((2 * j - 4, 2) :: (1, 1)
            :: repeat (1, 2) (beta - 1)) 1)).
  { apply (sTDN [14897638; 1523948; 426279; 308525; 58213; 30332; 931; 608; 77; 35; 20; 0] 29403092
           ((2 * j - 4, 2) :: (1, 1) :: repeat (1, 2) (beta - 1))
           1). }
  apply (hsteps_trans _ (HC [14897638; 1523948; 426279; 308525; 58213; 30332; 931; 608; 77; 35; 20; 0] 29403092 3 2 ((2 * j - 6, 2) :: (1, 1)
            :: repeat (1, 2) (beta - 1)) 1)).
  { replace ((2 * j - 6, 2) :: (1, 1) :: repeat (1, 2) (beta - 1))
      with ((2 * j - 4 - 2, 2) :: (1, 1) :: repeat (1, 2) (beta - 1))
      by sec_eq.
    apply (sTUP [14897638; 1523948; 426279; 308525; 58213; 30332; 931; 608; 77; 35; 20; 0] 29403092
           4 (2 * j - 4) 2 ((1, 1) :: repeat (1, 2) (beta - 1)) 1);
      lia. }
  apply (hsteps_trans _ (HC [14897638; 1523948; 426279; 308525; 58213; 30332; 931; 608; 77; 35; 20; 0]
    0 3 2 (repeat (1, 2) 29403092
     ++ ((2 * (j - 29403095), 2) :: (1, 1)
         :: repeat (1, 2) (beta - 1))) 1)).
  { rewrite Heq.
    apply (DIPGRIND 29403092 (2 * (j - 29403095))
           [14897638; 1523948; 426279; 308525; 58213; 30332; 931; 608; 77; 35; 20; 0]
           ((1, 1) :: repeat (1, 2) (beta - 1)) 1);
      [exact S59a1 | lia]. }
  apply (CASCADE59 ((2 * (j - 29403095), 2) :: (1, 1)
                    :: repeat (1, 2) (beta - 1))).
Qed.

(* ----------------------------------------------------------------- *)
(* The TOP13 closings: r13' = 2, 4, 6 and band 13                    *)
(* (8 <= r13' <= 117612386).                                         *)
(* ----------------------------------------------------------------- *)

Print Assumptions TOP59_TO_TOP13.
