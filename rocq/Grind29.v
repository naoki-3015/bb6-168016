(* ================================================================= *)
(* Phase 61: CASCADE61 segments CASCADE61a. *)
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
               Grind29e1 Grind29e11 Grind29e12 Grind29e7 Grind29e8 Grind29rep.

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

Lemma CASCADE61a : forall w,
  hsteps (HC [74737818; 10126538; 1236011; 698173; 177445; 95640; 10129; 1243; 207; 19] 0 3 2 (repeat (1, 2) 135985236 ++ w) 1)
         (HB [177445; 95640; 10129; 1243; 207; 19] 698173 1 1236013 (repeat (1, 2) 10126538 ++ (54484740, 2) :: (1, 1) :: repeat (1, 2) 135985238 ++ w) 1).
Proof.
  intro w.
  (* step 1: P PX2A *)
  apply (hsteps_trans _ (HC [1236011; 698173; 177445; 95640; 10129; 1243; 207; 19] 10126537 74737816 2 ((1, 1) :: repeat (1, 2) 135985238 ++ w) 1)).
  {
    rewrite NUM61ta1. rewrite NUM61ta2. rewrite NUM61ta3.
    replace ((1, 1) :: repeat (1, 2) 135985238 ++ w)
      with ((1, 1) :: (1, 2) :: (1, 2) :: repeat (1, 2) 135985236 ++ w)
      by (apply REP61a).
    exact (hsteps_step _ _ _ (hPX2A 74737815 10126537 [1236011; 698173; 177445; 95640; 10129; 1243; 207; 19] (repeat (1, 2) 135985236 ++ w) 1) (hsteps_refl _)).
  }
  (* step 2: P PUSH *)
  apply (hsteps_trans _ (HC [1236011; 698173; 177445; 95640; 10129; 1243; 207; 19] 10126536 1 2 ((74737814, 2) :: (1, 1) :: repeat (1, 2) 135985238 ++ w) 1)).
  {
    rewrite NUM61X1.
    rewrite NUM61X2.
    apply (sPUSH [1236011; 698173; 177445; 95640; 10129; 1243; 207; 19] 10126536 74737816 ((1, 1) :: repeat (1, 2) 135985238 ++ w) 1); closearith.
  }
  (* step 3: P TDN *)
  apply (hsteps_trans _ (HB [1236011; 698173; 177445; 95640; 10129; 1243; 207; 19] 10126536 1 4 ((74737814, 2) :: (1, 1) :: repeat (1, 2) 135985238 ++ w) 1)).
  {
    apply (sTDN [1236011; 698173; 177445; 95640; 10129; 1243; 207; 19] 10126536 ((74737814, 2) :: (1, 1) :: repeat (1, 2) 135985238 ++ w) 1).
  }
  (* step 4: sTUP *)
  apply (hsteps_trans _ (HC [1236011; 698173; 177445; 95640; 10129; 1243; 207; 19] 10126536 3 2 ((74737812, 2) :: (1, 1) :: repeat (1, 2) 135985238 ++ w) 1)).
  {
    rewrite NUM61X3.
    apply (sTUP [1236011; 698173; 177445; 95640; 10129; 1243; 207; 19] 10126536 4 74737814 2 ((1, 1) :: repeat (1, 2) 135985238 ++ w) 1); closearith.
  }
  (* step 5: DIPGRIND 10126536 54484740 *)
  apply (hsteps_trans _ (HC [1236011; 698173; 177445; 95640; 10129; 1243; 207; 19] 0 3 2 (repeat (1, 2) 10126536 ++ (54484740, 2) :: (1, 1) :: repeat (1, 2) 135985238 ++ w) 1)).
  {
    rewrite NUM61X4.
    apply (DIPGRIND 10126536 54484740 [1236011; 698173; 177445; 95640; 10129; 1243; 207; 19] ((1, 1) :: repeat (1, 2) 135985238 ++ w) 1); closearith.
  }
  (* step 6: P PX2A *)
  apply (hsteps_trans _ (HC [177445; 95640; 10129; 1243; 207; 19] 698172 1236009 2 ((1, 1) :: repeat (1, 2) 10126538 ++ (54484740, 2) :: (1, 1) :: repeat (1, 2) 135985238 ++ w) 1)).
  {
    rewrite NUM61tb1. rewrite NUM61tb2. rewrite NUM61tb3.
    replace ((1, 1) :: repeat (1, 2) 10126538 ++ (54484740, 2) :: (1, 1) :: repeat (1, 2) 135985238 ++ w)
      with ((1, 1) :: (1, 2) :: (1, 2) :: repeat (1, 2) 10126536 ++ (54484740, 2) :: (1, 1) :: repeat (1, 2) 135985238 ++ w)
      by (apply REP61b).
    exact (hsteps_step _ _ _ (hPX2A 1236008 698172 [177445; 95640; 10129; 1243; 207; 19] (repeat (1, 2) 10126536 ++ (54484740, 2) :: (1, 1) :: repeat (1, 2) 135985238 ++ w) 1) (hsteps_refl _)).
  }
  (* step 7: hGRIND 618003 *)
  apply (hsteps_trans _ (HB [177445; 95640; 10129; 1243; 207; 19] 698172 1 1236012 ((1, 1) :: repeat (1, 2) 10126538 ++ (54484740, 2) :: (1, 1) :: repeat (1, 2) 135985238 ++ w) 1)).
  {
    rewrite NUM61X5.
    rewrite NUM61X6.
    apply (hGRIND 618003 [177445; 95640; 10129; 1243; 207; 19] 698172 ((1, 1) :: repeat (1, 2) 10126538 ++ (54484740, 2) :: (1, 1) :: repeat (1, 2) 135985238 ++ w) 1); closearith.
  }
  (* step 8: P POP *)
  rewrite NUM61X7.
  rewrite NUM61X8.
  apply (sPOP1 [177445; 95640; 10129; 1243; 207; 19] 698172 1236012 (repeat (1, 2) 10126538 ++ (54484740, 2) :: (1, 1) :: repeat (1, 2) 135985238 ++ w) 1); closearith.
Qed.

(* CASCADE61b: steps 9-9 of the CASCADE61 chain. *)
