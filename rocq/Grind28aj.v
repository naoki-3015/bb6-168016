(* ================================================================= *)
(* Phase 60 (cascade, part 2): CASCADE60k-v and CASCADE60, the     *)
(* assembly of the 22 segments.  Split from Grind28.v for the      *)
(* operational reason recorded in Grind28.v's header (compile      *)
(* resident set at Phase 60 numeral depths); every lemma           *)
(* statement is the one the phase's single-file draft carried.     *)
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
               Grind28a Grind28ac Grind28ag Grind28ah Grind28ai
               Grind28ak Grind28al Grind28c Grind28i Grind28j
               Grind28.

(* Section equality: componentwise, arithmetic leaves by lia.      *)
Ltac sec_eq :=
  repeat (first [ solve [reflexivity] | solve [lia] | f_equal ]).

(* Closed-numeral arithmetic: literals >= 7426 are parsed as       *)
(* Nat.of_num_uint atoms, which lia cannot relate to variables;    *)
(* for purely closed <= goals the boolean check decides them.      *)
Ltac closearith :=
  first [ lia | apply Nat.leb_le; reflexivity ].


(* Split from Grind28j.v: CASCADE60 segments r-v and the CASCADE60 *)
(* assembly, for the resident-set reason in Grind28ag.v's header. *)


(* Split from Grind28ai.v: CASCADE60 segments t-v and the CASCADE60 *)
(* assembly, for the resident-set reason in Grind28ag.v's header. *)

(* CASCADE60t: steps 661-661 of the CASCADE60 chain. *)
Lemma CASCADE60t : forall w,
  hsteps (HB [10126538; 1236011; 698173; 177445; 95640; 10129; 1243; 207; 19] 15931624 1 18372850 (repeat (1, 2) 1 ++ (1, 1) :: repeat (1, 2) 58806192 ++ w) 1)
         (HB [10126538; 1236011; 698173; 177445; 95640; 10129; 1243; 207; 19] 15931625 1 18372852 ((1, 1) :: repeat (1, 2) 58806192 ++ w) 1).
Proof.
  intro w.
  rewrite S60rt1.
  rewrite S60rt2.
  (* step 661: M pop12 (1,) *)
  apply (pop12 1 [10126538; 1236011; 698173; 177445; 95640; 10129; 1243; 207; 19] 15931624 18372850 ((1, 1) :: repeat (1, 2) 58806192 ++ w) 1); exact S60rt3.
Qed.

(* CASCADE60u: steps 662-662 of the CASCADE60 chain. *)
Lemma CASCADE60u : forall w,
  hsteps (HB [10126538; 1236011; 698173; 177445; 95640; 10129; 1243; 207; 19] 15931625 1 18372852 ((1, 1) :: repeat (1, 2) 58806192 ++ w) 1)
         (HB [10126538; 1236011; 698173; 177445; 95640; 10129; 1243; 207; 19] 15931626 1 18372853 (repeat (1, 2) 58806192 ++ w) 1).
Proof.
  intro w.
  (* step 662: P POP *)
  rewrite NUM60X65.
  rewrite NUM60X66.
  apply (sPOP1 [10126538; 1236011; 698173; 177445; 95640; 10129; 1243; 207; 19] 15931625 18372852 (repeat (1, 2) 58806192 ++ w) 1); closearith.
Qed.

(* CASCADE60v: steps 663-663 of the CASCADE60 chain. *)
Lemma CASCADE60v : forall w,
  hsteps (HB [10126538; 1236011; 698173; 177445; 95640; 10129; 1243; 207; 19] 15931626 1 18372853 (repeat (1, 2) 58806192 ++ w) 1)
         (HB [10126538; 1236011; 698173; 177445; 95640; 10129; 1243; 207; 19] 74737818 1 135985237 (w) 1).
Proof.
  intro w.
  rewrite S60rv1.
  rewrite S60rv2.
  (* step 663: M pop12 (58806192,) *)
  apply (pop12 58806192 [10126538; 1236011; 698173; 177445; 95640; 10129; 1243; 207; 19] 15931626 18372853 (w) 1); exact S60rv3.
Qed.

Lemma CASCADE60 : forall w,
  hsteps (HC [34304475; 7965811; 4012920; 308090; 49409; 7710; 1059; 199; 101; 0] 0 3 2 (repeat (1, 2) 58806190 ++ w) 1)
         (HB [10126538; 1236011; 698173; 177445; 95640; 10129; 1243; 207; 19] 74737818 1 135985237 (w) 1).
Proof.
  intro w.
  apply (hsteps_trans _ (HC [235; 20; 0] 454 3 2 ((653, 2) :: (1, 1) :: repeat (1, 2) 7710 ++ (33987, 2) :: (1, 1) :: repeat (1, 2) 308090 ++ (3396738, 2) :: (1, 1) :: repeat (1, 2) 7965811 ++ (18372851, 2) :: (1, 1) :: repeat (1, 2) 58806192 ++ w) 1)).
  { apply (CASCADE60a w). }
  apply (hsteps_trans _ (HC [0] 3 1 2 ((13, 2) :: (1, 1) :: repeat (1, 2) 34 ++ (140, 2) :: (1, 1) :: repeat (1, 2) 474 ++ (6744, 2) :: (1, 1) :: repeat (1, 2) 16082 ++ (1821, 2) :: (1, 1) :: repeat (1, 2) 308090 ++ (3396738, 2) :: (1, 1) :: repeat (1, 2) 7965811 ++ (18372851, 2) :: (1, 1) :: repeat (1, 2) 58806192 ++ w) 1)).
  { apply (CASCADE60b w). }
  apply (hsteps_trans _ (HB [0] 4 1 4 ((1, 1) :: repeat (1, 2) 15 ++ (5, 2) :: (1, 1) :: repeat (1, 2) 75 ++ (461, 2) :: (1, 1) :: repeat (1, 2) 952 ++ (4838, 2) :: (1, 1) :: repeat (1, 2) 16082 ++ (1821, 2) :: (1, 1) :: repeat (1, 2) 308090 ++ (3396738, 2) :: (1, 1) :: repeat (1, 2) 7965811 ++ (18372851, 2) :: (1, 1) :: repeat (1, 2) 58806192 ++ w) 1)).
  { apply (CASCADE60c w). }
  apply (hsteps_trans _ (HC [20] 0 3 2 (repeat (1, 2) 201 ++ (932, 2) :: (1, 1) :: repeat (1, 2) 2050 ++ (736, 2) :: (1, 1) :: repeat (1, 2) 16082 ++ (1821, 2) :: (1, 1) :: repeat (1, 2) 308090 ++ (3396738, 2) :: (1, 1) :: repeat (1, 2) 7965811 ++ (18372851, 2) :: (1, 1) :: repeat (1, 2) 58806192 ++ w) 1)).
  { apply (CASCADE60d w). }
  apply (hsteps_trans _ (HB [5] 14 1 6 ((1, 1) :: repeat (1, 2) 34 ++ (108, 2) :: (1, 1) :: repeat (1, 2) 410 ++ (110, 2) :: (1, 1) :: repeat (1, 2) 2050 ++ (736, 2) :: (1, 1) :: repeat (1, 2) 16082 ++ (1821, 2) :: (1, 1) :: repeat (1, 2) 308090 ++ (3396738, 2) :: (1, 1) :: repeat (1, 2) 7965811 ++ (18372851, 2) :: (1, 1) :: repeat (1, 2) 58806192 ++ w) 1)).
  { apply (CASCADE60e w). }
  apply (hsteps_trans _ (HB [16817; 4103; 2159; 823; 517; 75; 49; 5] 32168 1 1823 (repeat (1, 2) 308090 ++ (3396738, 2) :: (1, 1) :: repeat (1, 2) 7965811 ++ (18372851, 2) :: (1, 1) :: repeat (1, 2) 58806192 ++ w) 1)).
  { apply (CASCADE60f w). }
  apply (hsteps_trans _ (HB [16817; 4103; 2159; 823; 517; 75; 49; 5] 340258 1 618003 ((3396738, 2) :: (1, 1) :: repeat (1, 2) 7965811 ++ (18372851, 2) :: (1, 1) :: repeat (1, 2) 58806192 ++ w) 1)).
  { apply (CASCADE60g w). }
  apply (hsteps_trans _ (HC [20; 0] 34 1 2 (repeat (1, 2) 1 ++ (1, 1) :: repeat (1, 2) 75 ++ (365, 2) :: (1, 1) :: repeat (1, 2) 823 ++ (17328, 2) :: (1, 1) :: repeat (1, 2) 37740 ++ (231140, 2) :: (1, 1) :: repeat (1, 2) 618004 ++ (2160728, 2) :: (1, 1) :: repeat (1, 2) 7965811 ++ (18372851, 2) :: (1, 1) :: repeat (1, 2) 58806192 ++ w) 1)).
  { apply (CASCADE60h w). }
  apply (hsteps_trans _ (HC [0] 0 3 2 (repeat (1, 2) 3 ++ (6, 2) :: (1, 1) :: repeat (1, 2) 203 ++ (803, 2) :: (1, 1) :: repeat (1, 2) 1696 ++ (13934, 2) :: (1, 1) :: repeat (1, 2) 37740 ++ (231140, 2) :: (1, 1) :: repeat (1, 2) 618004 ++ (2160728, 2) :: (1, 1) :: repeat (1, 2) 7965811 ++ (18372851, 2) :: (1, 1) :: repeat (1, 2) 58806192 ++ w) 1)).
  { apply (CASCADE60i w). }
  apply (hsteps_trans _ (HC [] 4 12 2 ((208, 2) :: (1, 1) :: repeat (1, 2) 420 ++ (846, 2) :: (1, 1) :: repeat (1, 2) 4198 ++ (5536, 2) :: (1, 1) :: repeat (1, 2) 37740 ++ (231140, 2) :: (1, 1) :: repeat (1, 2) 618004 ++ (2160728, 2) :: (1, 1) :: repeat (1, 2) 7965811 ++ (18372851, 2) :: (1, 1) :: repeat (1, 2) 58806192 ++ w) 1)).
  { apply (CASCADE60j w). }
  apply (hsteps_trans _ (HB [843; 523; 75; 41; 14; 5] 5042 1 8398 ((2, 2) :: (5534, 2) :: (1, 1) :: repeat (1, 2) 37740 ++ (231140, 2) :: (1, 1) :: repeat (1, 2) 618004 ++ (2160728, 2) :: (1, 1) :: repeat (1, 2) 7965811 ++ (18372851, 2) :: (1, 1) :: repeat (1, 2) 58806192 ++ w) 1)).
  { apply (CASCADE60k w). }
  apply (hsteps_trans _ (HC [0] 0 3 2 (repeat (1, 2) 17 ++ (69, 2) :: (1, 1) :: repeat (1, 2) 164 ++ (41, 2) :: (1, 1) :: repeat (1, 2) 843 ++ (3355, 2) :: (1, 1) :: repeat (1, 2) 8399 ++ (26475, 2) :: (1, 1) :: repeat (1, 2) 75484 ++ (80170, 2) :: (1, 1) :: repeat (1, 2) 618004 ++ (2160728, 2) :: (1, 1) :: repeat (1, 2) 7965811 ++ (18372851, 2) :: (1, 1) :: repeat (1, 2) 58806192 ++ w) 1)).
  { apply (CASCADE60l w). }
  apply (hsteps_trans _ (HB [10129; 1243; 207; 19] 20156 1 26477 (repeat (1, 2) 75484 ++ (80170, 2) :: (1, 1) :: repeat (1, 2) 618004 ++ (2160728, 2) :: (1, 1) :: repeat (1, 2) 7965811 ++ (18372851, 2) :: (1, 1) :: repeat (1, 2) 58806192 ++ w) 1)).
  { apply (CASCADE60m w). }
  apply (hsteps_trans _ (HB [10129; 1243; 207; 19] 95640 1 177445 ((80170, 2) :: (1, 1) :: repeat (1, 2) 618004 ++ (2160728, 2) :: (1, 1) :: repeat (1, 2) 7965811 ++ (18372851, 2) :: (1, 1) :: repeat (1, 2) 58806192 ++ w) 1)).
  { apply (CASCADE60n w). }
  apply (hsteps_trans _ (HB [177445; 95640; 10129; 1243; 207; 19] 80169 1 3 (repeat (1, 2) 618004 ++ (2160728, 2) :: (1, 1) :: repeat (1, 2) 7965811 ++ (18372851, 2) :: (1, 1) :: repeat (1, 2) 58806192 ++ w) 1)).
  { apply (CASCADE60o w). }
  apply (hsteps_trans _ (HB [177445; 95640; 10129; 1243; 207; 19] 698173 1 1236011 ((2160728, 2) :: (1, 1) :: repeat (1, 2) 7965811 ++ (18372851, 2) :: (1, 1) :: repeat (1, 2) 58806192 ++ w) 1)).
  { apply (CASCADE60p w). }
  apply (hsteps_trans _ (HB [1236011; 698173; 177445; 95640; 10129; 1243; 207; 19] 2160727 1 3 (repeat (1, 2) 7965811 ++ (18372851, 2) :: (1, 1) :: repeat (1, 2) 58806192 ++ w) 1)).
  { apply (CASCADE60q w). }
  apply (hsteps_trans _ (HB [1236011; 698173; 177445; 95640; 10129; 1243; 207; 19] 10126538 1 15931625 ((18372851, 2) :: (1, 1) :: repeat (1, 2) 58806192 ++ w) 1)).
  { apply (CASCADE60r w). }
  apply (hsteps_trans _ (HC [10126538; 1236011; 698173; 177445; 95640; 10129; 1243; 207; 19] 15931624 1 2 ((18372847, 2) :: (1, 1) :: repeat (1, 2) 58806192 ++ w) 1)).
  { apply (CASCADE60s1 w). }
  apply (hsteps_trans _ (HB [10126538; 1236011; 698173; 177445; 95640; 10129; 1243; 207; 19] 15931624 1 18372850 (repeat (1, 2) 1 ++ (1, 1) :: repeat (1, 2) 58806192 ++ w) 1)).
  { apply (CASCADE60s2 w). }
  apply (hsteps_trans _ (HB [10126538; 1236011; 698173; 177445; 95640; 10129; 1243; 207; 19] 15931625 1 18372852 ((1, 1) :: repeat (1, 2) 58806192 ++ w) 1)).
  { apply (CASCADE60t w). }
  apply (hsteps_trans _ (HB [10126538; 1236011; 698173; 177445; 95640; 10129; 1243; 207; 19] 15931626 1 18372853 (repeat (1, 2) 58806192 ++ w) 1)).
  { apply (CASCADE60u w). }
  apply (CASCADE60v w).
Qed.

Print Assumptions CASCADE60.


