(* ================================================================= *)
(* Phase 63: CASCADE63 segments CASCADE63c. *)
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
               Grind31e12 Grind31e13 Grind31e14 Grind31e15 Grind31e16 Grind31e17 Grind31e2 Grind31e3 Grind31e4 Grind31e5 Grind31e6 Grind31e7 Grind31e8 Grind31m1 Grind31m2 Grind31m3 Grind31g1.

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

Lemma CASCADE63c : forall w,
  hsteps (HB [349423; 101323; 57668; 5526; 626; 189; 112; 33; 19; 0] 65515088 1 130856035 ((246445596, 2) :: (1, 1) :: repeat (1, 2) 595648558 ++ w) 1)
         (HB [130856035; 65515088; 349423; 101323; 57668; 5526; 626; 189; 112; 33; 19; 0] 246445595 1 3 (repeat (1, 2) 595648558 ++ w) 1).
Proof.
  intro w.
  (* step 10: sTUP *)
  apply (hsteps_trans _ (HC [349423; 101323; 57668; 5526; 626; 189; 112; 33; 19; 0] 65515088 130856034 2 ((246445594, 2) :: (1, 1) :: repeat (1, 2) 595648558 ++ w) 1)).
  {
    rewrite NUM63X9.
    rewrite NUM63X10.
    apply (sTUP [349423; 101323; 57668; 5526; 626; 189; 112; 33; 19; 0] 65515088 130856035 246445596 2 ((1, 1) :: repeat (1, 2) 595648558 ++ w) 1); closearith.
  }
  (* step 11: hGRIND_even 65428015 *)
  apply (hsteps_trans _ (HB [349423; 101323; 57668; 5526; 626; 189; 112; 33; 19; 0] 65515087 1 130856034 ((2, 2) :: (246445594, 2) :: (1, 1) :: repeat (1, 2) 595648558 ++ w) 1)).
  {
    rewrite NUM63X11.
    rewrite NUM63X12.
    apply (hGRIND_even 65428015 [349423; 101323; 57668; 5526; 626; 189; 112; 33; 19; 0] 65515087 ((246445594, 2) :: (1, 1) :: repeat (1, 2) 595648558 ++ w) 1); [exact P63u11 | exact P63s11].
  }
  (* step 12: P TUP2_1 *)
  apply (hsteps_trans _ (HC [65515088; 349423; 101323; 57668; 5526; 626; 189; 112; 33; 19; 0] 130856034 1 2 ((246445592, 2) :: (1, 1) :: repeat (1, 2) 595648558 ++ w) 1)).
  {
    rewrite NUM63X13.
    rewrite NUM63X14.
    rewrite NUM63X15.
    apply (sTUP2_1 [349423; 101323; 57668; 5526; 626; 189; 112; 33; 19; 0] 65515087 130856033 246445594 ((1, 1) :: repeat (1, 2) 595648558 ++ w) 1); closearith.
  }
  (* step 13: P TDN *)
  apply (hsteps_trans _ (HB [65515088; 349423; 101323; 57668; 5526; 626; 189; 112; 33; 19; 0] 130856034 1 4 ((246445592, 2) :: (1, 1) :: repeat (1, 2) 595648558 ++ w) 1)).
  {
    apply (sTDN [65515088; 349423; 101323; 57668; 5526; 626; 189; 112; 33; 19; 0] 130856034 ((246445592, 2) :: (1, 1) :: repeat (1, 2) 595648558 ++ w) 1).
  }
  (* step 14: sTUP *)
  apply (hsteps_trans _ (HC [65515088; 349423; 101323; 57668; 5526; 626; 189; 112; 33; 19; 0] 130856034 3 2 ((246445590, 2) :: (1, 1) :: repeat (1, 2) 595648558 ++ w) 1)).
  {
    rewrite NUM63X16.
    apply (sTUP [65515088; 349423; 101323; 57668; 5526; 626; 189; 112; 33; 19; 0] 130856034 4 246445592 2 ((1, 1) :: repeat (1, 2) 595648558 ++ w) 1); closearith.
  }
  (* step 15: CLEANG_even 123222794 *)
  apply (hsteps_trans _ (HB [65515088; 349423; 101323; 57668; 5526; 626; 189; 112; 33; 19; 0] 130856034 1 246445594 ((2, 2) :: (1, 1) :: repeat (1, 2) 595648558 ++ w) 1)).
  {
    rewrite NUM63X17.
    rewrite NUM63X18.
    apply (CLEANG_even 123222794 [65515088; 349423; 101323; 57668; 5526; 626; 189; 112; 33; 19; 0] 130856034 ((1, 1) :: repeat (1, 2) 595648558 ++ w) 1); exact P63s15.
  }
  (* step 16: P TRANS2_1 *)
  rewrite NUM63X19.
  rewrite NUM63X20.
  rewrite NUM63X21.
  apply (sTRANS2_1 [65515088; 349423; 101323; 57668; 5526; 626; 189; 112; 33; 19; 0] 130856034 246445593 1 (repeat (1, 2) 595648558 ++ w) 1); closearith.
Qed.

(* CASCADE63d: steps 17-17 of the CASCADE63 chain. *)
