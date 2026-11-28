(* ================================================================= *)
(* Phase 62: CASCADE62 segments CASCADE62r. *)
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
               Grind30e12 Grind30e13 Grind30e14 Grind30g6.

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

Lemma CASCADE62r : forall w,
  hsteps (HB [101323; 57668; 5526; 626; 189; 112; 33; 19; 0] 349423 1 619871 ((1065599, 2) :: (1, 1) :: repeat (1, 2) 4240674 ++ (12762444, 2) :: (1, 1) :: repeat (1, 2) 47892099 ++ (51707595, 2) :: (1, 1) :: repeat (1, 2) 271970480 ++ w) 1)
         (HB [349423; 101323; 57668; 5526; 626; 189; 112; 33; 19; 0] 619870 1 1065598 (repeat (1, 2) 1 ++ (1, 1) :: repeat (1, 2) 4240674 ++ (12762444, 2) :: (1, 1) :: repeat (1, 2) 47892099 ++ (51707595, 2) :: (1, 1) :: repeat (1, 2) 271970480 ++ w) 1).
Proof.
  intro w.
  (* step 725: sTUP *)
  apply (hsteps_trans _ (HC [101323; 57668; 5526; 626; 189; 112; 33; 19; 0] 349423 619870 2 ((1065597, 2) :: (1, 1) :: repeat (1, 2) 4240674 ++ (12762444, 2) :: (1, 1) :: repeat (1, 2) 47892099 ++ (51707595, 2) :: (1, 1) :: repeat (1, 2) 271970480 ++ w) 1)).
  {
    rewrite NUM62X59.
    rewrite NUM62X60.
    apply (sTUP [101323; 57668; 5526; 626; 189; 112; 33; 19; 0] 349423 619871 1065599 2 ((1, 1) :: repeat (1, 2) 4240674 ++ (12762444, 2) :: (1, 1) :: repeat (1, 2) 47892099 ++ (51707595, 2) :: (1, 1) :: repeat (1, 2) 271970480 ++ w) 1); closearith.
  }
  (* step 726: hGRIND_even 309933 *)
  apply (hsteps_trans _ (HB [101323; 57668; 5526; 626; 189; 112; 33; 19; 0] 349422 1 619870 ((2, 2) :: (1065597, 2) :: (1, 1) :: repeat (1, 2) 4240674 ++ (12762444, 2) :: (1, 1) :: repeat (1, 2) 47892099 ++ (51707595, 2) :: (1, 1) :: repeat (1, 2) 271970480 ++ w) 1)).
  {
    rewrite NUM62X61.
    rewrite NUM62X62.
    apply (hGRIND_even 309933 [101323; 57668; 5526; 626; 189; 112; 33; 19; 0] 349422 ((1065597, 2) :: (1, 1) :: repeat (1, 2) 4240674 ++ (12762444, 2) :: (1, 1) :: repeat (1, 2) 47892099 ++ (51707595, 2) :: (1, 1) :: repeat (1, 2) 271970480 ++ w) 1); closearith.
  }
  (* step 727: P TUP2_1 *)
  apply (hsteps_trans _ (HC [349423; 101323; 57668; 5526; 626; 189; 112; 33; 19; 0] 619870 1 2 ((1065595, 2) :: (1, 1) :: repeat (1, 2) 4240674 ++ (12762444, 2) :: (1, 1) :: repeat (1, 2) 47892099 ++ (51707595, 2) :: (1, 1) :: repeat (1, 2) 271970480 ++ w) 1)).
  {
    rewrite NUM62X63.
    rewrite NUM62X64.
    rewrite NUM62X65.
    apply (sTUP2_1 [101323; 57668; 5526; 626; 189; 112; 33; 19; 0] 349422 619869 1065597 ((1, 1) :: repeat (1, 2) 4240674 ++ (12762444, 2) :: (1, 1) :: repeat (1, 2) 47892099 ++ (51707595, 2) :: (1, 1) :: repeat (1, 2) 271970480 ++ w) 1); closearith.
  }
  (* step 728: P TDN *)
  apply (hsteps_trans _ (HB [349423; 101323; 57668; 5526; 626; 189; 112; 33; 19; 0] 619870 1 4 ((1065595, 2) :: (1, 1) :: repeat (1, 2) 4240674 ++ (12762444, 2) :: (1, 1) :: repeat (1, 2) 47892099 ++ (51707595, 2) :: (1, 1) :: repeat (1, 2) 271970480 ++ w) 1)).
  {
    apply (sTDN [349423; 101323; 57668; 5526; 626; 189; 112; 33; 19; 0] 619870 ((1065595, 2) :: (1, 1) :: repeat (1, 2) 4240674 ++ (12762444, 2) :: (1, 1) :: repeat (1, 2) 47892099 ++ (51707595, 2) :: (1, 1) :: repeat (1, 2) 271970480 ++ w) 1).
  }
  (* step 729: sTUP *)
  apply (hsteps_trans _ (HC [349423; 101323; 57668; 5526; 626; 189; 112; 33; 19; 0] 619870 3 2 ((1065593, 2) :: (1, 1) :: repeat (1, 2) 4240674 ++ (12762444, 2) :: (1, 1) :: repeat (1, 2) 47892099 ++ (51707595, 2) :: (1, 1) :: repeat (1, 2) 271970480 ++ w) 1)).
  {
    rewrite NUM62X66.
    apply (sTUP [349423; 101323; 57668; 5526; 626; 189; 112; 33; 19; 0] 619870 4 1065595 2 ((1, 1) :: repeat (1, 2) 4240674 ++ (12762444, 2) :: (1, 1) :: repeat (1, 2) 47892099 ++ (51707595, 2) :: (1, 1) :: repeat (1, 2) 271970480 ++ w) 1); closearith.
  }
  (* step 730: CLEANG_odd 532795 *)
  rewrite NUM62X67.
  rewrite NUM62X68.
  replace (repeat (1, 2) 1 ++ (1, 1) :: repeat (1, 2) 4240674 ++ (12762444, 2) :: (1, 1) :: repeat (1, 2) 47892099 ++ (51707595, 2) :: (1, 1) :: repeat (1, 2) 271970480 ++ w) with ((1, 2) :: (1, 1) :: repeat (1, 2) 4240674 ++ (12762444, 2) :: (1, 1) :: repeat (1, 2) 47892099 ++ (51707595, 2) :: (1, 1) :: repeat (1, 2) 271970480 ++ w) by sec_eq.
  apply (CLEANG_odd 532795 [349423; 101323; 57668; 5526; 626; 189; 112; 33; 19; 0] 619870 ((1, 1) :: repeat (1, 2) 4240674 ++ (12762444, 2) :: (1, 1) :: repeat (1, 2) 47892099 ++ (51707595, 2) :: (1, 1) :: repeat (1, 2) 271970480 ++ w) 1); closearith.
Qed.

(* CASCADE62s: steps 731-731 of the CASCADE62 chain. *)
