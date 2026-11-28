(* ================================================================= *)
(* Phase 63: CASCADE63 segments CASCADE63a. *)
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
               Grind31e1 Grind31e10 Grind31e11 Grind31e9 Grind31m1 Grind31rep.

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

Lemma CASCADE63a : forall w,
  hsteps (HC [367754682; 60654542; 9546949; 4860546; 349423; 101323; 57668; 5526; 626; 189; 112; 33; 19; 0] 0 3 2 (repeat (1, 2) 595648556 ++ w) 1)
         (HB [349423; 101323; 57668; 5526; 626; 189; 112; 33; 19; 0] 4860546 1 9546951 (repeat (1, 2) 60654542 ++ (246445596, 2) :: (1, 1) :: repeat (1, 2) 595648558 ++ w) 1).
Proof.
  intro w.
  (* step 1: P PX2A *)
  apply (hsteps_trans _ (HC [9546949; 4860546; 349423; 101323; 57668; 5526; 626; 189; 112; 33; 19; 0] 60654541 367754680 2 ((1, 1) :: repeat (1, 2) 595648558 ++ w) 1)).
  {
    rewrite NUM63ta1. rewrite NUM63ta2. rewrite NUM63ta3.
    replace ((1, 1) :: repeat (1, 2) 595648558 ++ w)
      with ((1, 1) :: (1, 2) :: (1, 2) :: repeat (1, 2) 595648556 ++ w)
      by (apply REP63a).
    exact (hsteps_step _ _ _ (hPX2A 367754679 60654541 [9546949; 4860546; 349423; 101323; 57668; 5526; 626; 189; 112; 33; 19; 0] (repeat (1, 2) 595648556 ++ w) 1) (hsteps_refl _)).
  }
  (* step 2: P PUSH *)
  apply (hsteps_trans _ (HC [9546949; 4860546; 349423; 101323; 57668; 5526; 626; 189; 112; 33; 19; 0] 60654540 1 2 ((367754678, 2) :: (1, 1) :: repeat (1, 2) 595648558 ++ w) 1)).
  {
    rewrite NUM63X1.
    rewrite NUM63X2.
    apply (sPUSH [9546949; 4860546; 349423; 101323; 57668; 5526; 626; 189; 112; 33; 19; 0] 60654540 367754680 ((1, 1) :: repeat (1, 2) 595648558 ++ w) 1); closearith.
  }
  (* step 3: P TDN *)
  apply (hsteps_trans _ (HB [9546949; 4860546; 349423; 101323; 57668; 5526; 626; 189; 112; 33; 19; 0] 60654540 1 4 ((367754678, 2) :: (1, 1) :: repeat (1, 2) 595648558 ++ w) 1)).
  {
    apply (sTDN [9546949; 4860546; 349423; 101323; 57668; 5526; 626; 189; 112; 33; 19; 0] 60654540 ((367754678, 2) :: (1, 1) :: repeat (1, 2) 595648558 ++ w) 1).
  }
  (* step 4: sTUP *)
  apply (hsteps_trans _ (HC [9546949; 4860546; 349423; 101323; 57668; 5526; 626; 189; 112; 33; 19; 0] 60654540 3 2 ((367754676, 2) :: (1, 1) :: repeat (1, 2) 595648558 ++ w) 1)).
  {
    rewrite NUM63X3.
    apply (sTUP [9546949; 4860546; 349423; 101323; 57668; 5526; 626; 189; 112; 33; 19; 0] 60654540 4 367754678 2 ((1, 1) :: repeat (1, 2) 595648558 ++ w) 1); closearith.
  }
  (* step 5: DIPGRIND 60654540 246445596 *)
  apply (hsteps_trans _ (HC [9546949; 4860546; 349423; 101323; 57668; 5526; 626; 189; 112; 33; 19; 0] 0 3 2 (repeat (1, 2) 60654540 ++ (246445596, 2) :: (1, 1) :: repeat (1, 2) 595648558 ++ w) 1)).
  {
    rewrite NUM63X4.
    apply (DIPGRIND 60654540 246445596 [9546949; 4860546; 349423; 101323; 57668; 5526; 626; 189; 112; 33; 19; 0] ((1, 1) :: repeat (1, 2) 595648558 ++ w) 1); closearith.
  }
  (* step 6: P PX2A *)
  apply (hsteps_trans _ (HC [349423; 101323; 57668; 5526; 626; 189; 112; 33; 19; 0] 4860545 9546947 2 ((1, 1) :: repeat (1, 2) 60654542 ++ (246445596, 2) :: (1, 1) :: repeat (1, 2) 595648558 ++ w) 1)).
  {
    rewrite NUM63tb1. rewrite NUM63tb2. rewrite NUM63tb3.
    replace ((1, 1) :: repeat (1, 2) 60654542 ++ (246445596, 2) :: (1, 1) :: repeat (1, 2) 595648558 ++ w)
      with ((1, 1) :: (1, 2) :: (1, 2) :: repeat (1, 2) 60654540 ++ (246445596, 2) :: (1, 1) :: repeat (1, 2) 595648558 ++ w)
      by (apply REP63b).
    exact (hsteps_step _ _ _ (hPX2A 9546946 4860545 [349423; 101323; 57668; 5526; 626; 189; 112; 33; 19; 0] (repeat (1, 2) 60654540 ++ (246445596, 2) :: (1, 1) :: repeat (1, 2) 595648558 ++ w) 1) (hsteps_refl _)).
  }
  (* step 7: hGRIND 4773472 *)
  apply (hsteps_trans _ (HB [349423; 101323; 57668; 5526; 626; 189; 112; 33; 19; 0] 4860545 1 9546950 ((1, 1) :: repeat (1, 2) 60654542 ++ (246445596, 2) :: (1, 1) :: repeat (1, 2) 595648558 ++ w) 1)).
  {
    rewrite NUM63X5.
    rewrite NUM63X6.
    apply (hGRIND 4773472 [349423; 101323; 57668; 5526; 626; 189; 112; 33; 19; 0] 4860545 ((1, 1) :: repeat (1, 2) 60654542 ++ (246445596, 2) :: (1, 1) :: repeat (1, 2) 595648558 ++ w) 1); exact P63s7.
  }
  (* step 8: P POP *)
  rewrite NUM63X7.
  rewrite NUM63X8.
  apply (sPOP1 [349423; 101323; 57668; 5526; 626; 189; 112; 33; 19; 0] 4860545 9546950 (repeat (1, 2) 60654542 ++ (246445596, 2) :: (1, 1) :: repeat (1, 2) 595648558 ++ w) 1); closearith.
Qed.

(* CASCADE63b: steps 9-9 of the CASCADE63 chain. *)
