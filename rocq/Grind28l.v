(* ================================================================= *)
(* Phase 60 (tail): the TOP14 front (TOP60_TO_TOP14).  Split from    *)
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
               Grind27h Grind27i Grind27j Grind27k Grind27l Grind27m
               Grind28a Grind28ai Grind28aj Grind28j.
(* Section equality: componentwise, arithmetic leaves by lia.      *)
Ltac sec_eq :=
  repeat (first [ solve [reflexivity] | solve [lia] | f_equal ]).

(* Closed-numeral arithmetic: literals >= 7426 are parsed as       *)
(* Nat.of_num_uint atoms, which lia cannot relate to variables;    *)
(* for purely closed <= goals the boolean check decides them.      *)
Ltac closearith :=
  first [ lia | apply Nat.leb_le; reflexivity ].

(* ----------------------------------------------------------------- *)
(* TOP60_TO_TOP14: the TOP13 state at (2j, 2) reaches TOP14 at the *)
(* pair (2 * (j - 58806193), 2).  The front is the Phase 59 front  *)
(* verbatim at the new constants: the first TUP rewrites via       *)
(* NUM59h (58806190 = 58806191 - 1, inherited from Grind27l.v),    *)
(* the hGRIND_even 29403093 step rewrites the goal by NUM59a /     *)
(* NUM59b (58806190 = 2 * 29403093 + 4, 34304475 = S 34304474),    *)
(* and the TUP2_1 step rewrites via NUM59i (58806190 =             *)
(* S 58806189) / NUM59b.  The two closed <= premises of the front  *)
(* steps are discharged by the leb lemmas S59h0 / S59g1 / S59g2 /  *)
(* S60a1, never by lia on the 58.8M atoms.                         *)
(* ----------------------------------------------------------------- *)

Lemma TOP60_TO_TOP14 : forall j beta, 58806194 <= j -> 2 <= beta ->
  hsteps (HB [7965811; 4012920; 308090; 49409; 7710; 1059; 199; 101; 0] 34304475 1 58806191
            ((2 * j, 2) :: (1, 1) :: repeat (1, 2) (beta - 1)) 1)
         (HB [10126538; 1236011; 698173; 177445; 95640; 10129; 1243; 207; 19] 74737818 1 135985237
            ((2 * (j - 58806193), 2) :: (1, 1)
             :: repeat (1, 2) (beta - 1)) 1).
Proof.
  intros j beta Hj Hb.
  assert (Hj4 : 4 <= j).
  { apply Nat.le_trans with 58806194; [closearith | exact Hj]. }
  assert (Hr : 1 <= j - 58806193).
  { assert (E : 58806193 = 58806194 - 1)
      by (exact S60f1).
    rewrite E. lia. }
  assert (Heq : 2 * j - 6 = 2 * 58806190 + 2 * (j - 58806193)).
  { assert (E1 : 58806193 = S (S (S 58806190)))
      by (exact S60f2).
    assert (E2 : 58806194 = S (S (S (S 58806190))))
      by (exact S60f3).
    rewrite E1. rewrite E2 in Hj. lia. }
  apply (hsteps_trans _ (HC [7965811; 4012920; 308090; 49409; 7710; 1059; 199; 101; 0] 34304475
    58806190 2 ((2 * j - 2, 2) :: (1, 1) :: repeat (1, 2) (beta - 1)) 1)).
  { rewrite NUM59h.
    apply (sTUP [7965811; 4012920; 308090; 49409; 7710; 1059; 199; 101; 0] 34304475 58806191 (2 * j) 2
           ((1, 1) :: repeat (1, 2) (beta - 1)) 1);
      [exact S59h0 | lia]. }
  apply (hsteps_trans _ (HB [7965811; 4012920; 308090; 49409; 7710; 1059; 199; 101; 0]
    34304474 1 58806190 ((2, 2) :: (2 * j - 2, 2) :: (1, 1)
            :: repeat (1, 2) (beta - 1)) 1)).
  { rewrite NUM59a. rewrite NUM59b.
    apply (hGRIND_even 29403093 [7965811; 4012920; 308090; 49409; 7710; 1059; 199; 101; 0]
           34304474 ((2 * j - 2, 2) :: (1, 1) :: repeat (1, 2) (beta - 1))
           1); [exact S59g1 | exact S59g2]. }
  apply (hsteps_trans _ (HC [34304475; 7965811; 4012920; 308090; 49409; 7710; 1059; 199; 101; 0] 58806190 1 2 ((2 * j - 4, 2) :: (1, 1)
            :: repeat (1, 2) (beta - 1)) 1)).
  { rewrite NUM59i. rewrite NUM59b.
    assert (E : ((2 * j - 2 - 2, 2) :: (1, 1) :: repeat (1, 2) (beta - 1))
              = ((2 * j - 4, 2) :: (1, 1) :: repeat (1, 2) (beta - 1)))
      by sec_eq.
    rewrite <- E.
    apply (sTUP2_1 [7965811; 4012920; 308090; 49409; 7710; 1059; 199; 101; 0] 34304474
           58806189 (2 * j - 2) ((1, 1) :: repeat (1, 2) (beta - 1))
           1); lia. }
  apply (hsteps_trans _ (HB [34304475; 7965811; 4012920; 308090; 49409; 7710; 1059; 199; 101; 0] 58806190 1 4 ((2 * j - 4, 2) :: (1, 1)
            :: repeat (1, 2) (beta - 1)) 1)).
  { apply (sTDN [34304475; 7965811; 4012920; 308090; 49409; 7710; 1059; 199; 101; 0] 58806190
           ((2 * j - 4, 2) :: (1, 1) :: repeat (1, 2) (beta - 1))
           1). }
  apply (hsteps_trans _ (HC [34304475; 7965811; 4012920; 308090; 49409; 7710; 1059; 199; 101; 0] 58806190 3 2 ((2 * j - 6, 2) :: (1, 1)
            :: repeat (1, 2) (beta - 1)) 1)).
  { assert (E : ((2 * j - 4 - 2, 2) :: (1, 1) :: repeat (1, 2) (beta - 1))
              = ((2 * j - 6, 2) :: (1, 1) :: repeat (1, 2) (beta - 1)))
      by sec_eq.
    rewrite <- E.
    apply (sTUP [34304475; 7965811; 4012920; 308090; 49409; 7710; 1059; 199; 101; 0] 58806190
           4 (2 * j - 4) 2 ((1, 1) :: repeat (1, 2) (beta - 1)) 1);
      lia. }
  apply (hsteps_trans _ (HC [34304475; 7965811; 4012920; 308090; 49409; 7710; 1059; 199; 101; 0]
    0 3 2 (repeat (1, 2) 58806190
     ++ ((2 * (j - 58806193), 2) :: (1, 1)
         :: repeat (1, 2) (beta - 1))) 1)).
  { rewrite Heq.
    apply (DIPGRIND 58806190 (2 * (j - 58806193))
           [34304475; 7965811; 4012920; 308090; 49409; 7710; 1059; 199; 101; 0]
           ((1, 1) :: repeat (1, 2) (beta - 1)) 1);
      [exact S60a1 | lia]. }
  apply (CASCADE60 ((2 * (j - 58806193), 2) :: (1, 1)
                    :: repeat (1, 2) (beta - 1))).
Qed.

Print Assumptions TOP60_TO_TOP14.
