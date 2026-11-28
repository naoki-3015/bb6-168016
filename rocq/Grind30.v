(* ================================================================= *)
(* Phase 62: CASCADE62 segments CASCADE62a. *)
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
               Grind30e1 Grind30e10 Grind30e11 Grind30e13 Grind30e14 Grind30e8 Grind30e9 Grind30rep.

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

Lemma CASCADE62a : forall w,
  hsteps (HC [147491795; 47892099; 24915618; 1835911; 568849; 317482; 29175; 9907; 6375; 799; 475; 93; 58; 5] 0 3 2 (repeat (1, 2) 271970478 ++ w) 1)
         (HB [29175; 9907; 6375; 799; 475; 93; 58; 5] 317482 1 568851 (repeat (1, 2) 1835911 ++ (21243794, 2) :: (1, 1) :: repeat (1, 2) 47892099 ++ (51707595, 2) :: (1, 1) :: repeat (1, 2) 271970480 ++ w) 1).
Proof.
  intro w.
  (* step 1: P PX2A *)
  apply (hsteps_trans _ (HC [24915618; 1835911; 568849; 317482; 29175; 9907; 6375; 799; 475; 93; 58; 5] 47892098 147491793 2 ((1, 1) :: repeat (1, 2) 271970480 ++ w) 1)).
  {
    rewrite NUM62ta1. rewrite NUM62ta2. rewrite NUM62ta3.
    replace ((1, 1) :: repeat (1, 2) 271970480 ++ w)
      with ((1, 1) :: (1, 2) :: (1, 2) :: repeat (1, 2) 271970478 ++ w)
      by (apply REP62a).
    exact (hsteps_step _ _ _ (hPX2A 147491792 47892098 [24915618; 1835911; 568849; 317482; 29175; 9907; 6375; 799; 475; 93; 58; 5] (repeat (1, 2) 271970478 ++ w) 1) (hsteps_refl _)).
  }
  (* step 2: P PUSH *)
  apply (hsteps_trans _ (HC [24915618; 1835911; 568849; 317482; 29175; 9907; 6375; 799; 475; 93; 58; 5] 47892097 1 2 ((147491791, 2) :: (1, 1) :: repeat (1, 2) 271970480 ++ w) 1)).
  {
    rewrite NUM62X1.
    rewrite NUM62X2.
    apply (sPUSH [24915618; 1835911; 568849; 317482; 29175; 9907; 6375; 799; 475; 93; 58; 5] 47892097 147491793 ((1, 1) :: repeat (1, 2) 271970480 ++ w) 1); closearith.
  }
  (* step 3: P TDN *)
  apply (hsteps_trans _ (HB [24915618; 1835911; 568849; 317482; 29175; 9907; 6375; 799; 475; 93; 58; 5] 47892097 1 4 ((147491791, 2) :: (1, 1) :: repeat (1, 2) 271970480 ++ w) 1)).
  {
    apply (sTDN [24915618; 1835911; 568849; 317482; 29175; 9907; 6375; 799; 475; 93; 58; 5] 47892097 ((147491791, 2) :: (1, 1) :: repeat (1, 2) 271970480 ++ w) 1).
  }
  (* step 4: sTUP *)
  apply (hsteps_trans _ (HC [24915618; 1835911; 568849; 317482; 29175; 9907; 6375; 799; 475; 93; 58; 5] 47892097 3 2 ((147491789, 2) :: (1, 1) :: repeat (1, 2) 271970480 ++ w) 1)).
  {
    rewrite NUM62X3.
    apply (sTUP [24915618; 1835911; 568849; 317482; 29175; 9907; 6375; 799; 475; 93; 58; 5] 47892097 4 147491791 2 ((1, 1) :: repeat (1, 2) 271970480 ++ w) 1); closearith.
  }
  (* step 5: DIPGRIND 47892097 51707595 *)
  apply (hsteps_trans _ (HC [24915618; 1835911; 568849; 317482; 29175; 9907; 6375; 799; 475; 93; 58; 5] 0 3 2 (repeat (1, 2) 47892097 ++ (51707595, 2) :: (1, 1) :: repeat (1, 2) 271970480 ++ w) 1)).
  {
    rewrite NUM62X4.
    apply (DIPGRIND 47892097 51707595 [24915618; 1835911; 568849; 317482; 29175; 9907; 6375; 799; 475; 93; 58; 5] ((1, 1) :: repeat (1, 2) 271970480 ++ w) 1); closearith.
  }
  (* step 6: P PX2A *)
  apply (hsteps_trans _ (HC [568849; 317482; 29175; 9907; 6375; 799; 475; 93; 58; 5] 1835910 24915616 2 ((1, 1) :: repeat (1, 2) 47892099 ++ (51707595, 2) :: (1, 1) :: repeat (1, 2) 271970480 ++ w) 1)).
  {
    rewrite NUM62tb1. rewrite NUM62tb2. rewrite NUM62tb3.
    replace ((1, 1) :: repeat (1, 2) 47892099 ++ (51707595, 2) :: (1, 1) :: repeat (1, 2) 271970480 ++ w)
      with ((1, 1) :: (1, 2) :: (1, 2) :: repeat (1, 2) 47892097 ++ (51707595, 2) :: (1, 1) :: repeat (1, 2) 271970480 ++ w)
      by (apply REP62b).
    exact (hsteps_step _ _ _ (hPX2A 24915615 1835910 [568849; 317482; 29175; 9907; 6375; 799; 475; 93; 58; 5] (repeat (1, 2) 47892097 ++ (51707595, 2) :: (1, 1) :: repeat (1, 2) 271970480 ++ w) 1) (hsteps_refl _)).
  }
  (* step 7: P PUSH *)
  apply (hsteps_trans _ (HC [568849; 317482; 29175; 9907; 6375; 799; 475; 93; 58; 5] 1835909 1 2 ((24915614, 2) :: (1, 1) :: repeat (1, 2) 47892099 ++ (51707595, 2) :: (1, 1) :: repeat (1, 2) 271970480 ++ w) 1)).
  {
    rewrite NUM62X5.
    rewrite NUM62X6.
    apply (sPUSH [568849; 317482; 29175; 9907; 6375; 799; 475; 93; 58; 5] 1835909 24915616 ((1, 1) :: repeat (1, 2) 47892099 ++ (51707595, 2) :: (1, 1) :: repeat (1, 2) 271970480 ++ w) 1); closearith.
  }
  (* step 8: P TDN *)
  apply (hsteps_trans _ (HB [568849; 317482; 29175; 9907; 6375; 799; 475; 93; 58; 5] 1835909 1 4 ((24915614, 2) :: (1, 1) :: repeat (1, 2) 47892099 ++ (51707595, 2) :: (1, 1) :: repeat (1, 2) 271970480 ++ w) 1)).
  {
    apply (sTDN [568849; 317482; 29175; 9907; 6375; 799; 475; 93; 58; 5] 1835909 ((24915614, 2) :: (1, 1) :: repeat (1, 2) 47892099 ++ (51707595, 2) :: (1, 1) :: repeat (1, 2) 271970480 ++ w) 1).
  }
  (* step 9: sTUP *)
  apply (hsteps_trans _ (HC [568849; 317482; 29175; 9907; 6375; 799; 475; 93; 58; 5] 1835909 3 2 ((24915612, 2) :: (1, 1) :: repeat (1, 2) 47892099 ++ (51707595, 2) :: (1, 1) :: repeat (1, 2) 271970480 ++ w) 1)).
  {
    rewrite NUM62X7.
    apply (sTUP [568849; 317482; 29175; 9907; 6375; 799; 475; 93; 58; 5] 1835909 4 24915614 2 ((1, 1) :: repeat (1, 2) 47892099 ++ (51707595, 2) :: (1, 1) :: repeat (1, 2) 271970480 ++ w) 1); closearith.
  }
  (* step 10: DIPGRIND 1835909 21243794 *)
  apply (hsteps_trans _ (HC [568849; 317482; 29175; 9907; 6375; 799; 475; 93; 58; 5] 0 3 2 (repeat (1, 2) 1835909 ++ (21243794, 2) :: (1, 1) :: repeat (1, 2) 47892099 ++ (51707595, 2) :: (1, 1) :: repeat (1, 2) 271970480 ++ w) 1)).
  {
    rewrite NUM62X8.
    apply (DIPGRIND 1835909 21243794 [568849; 317482; 29175; 9907; 6375; 799; 475; 93; 58; 5] ((1, 1) :: repeat (1, 2) 47892099 ++ (51707595, 2) :: (1, 1) :: repeat (1, 2) 271970480 ++ w) 1); closearith.
  }
  (* step 11: P PX2A *)
  apply (hsteps_trans _ (HC [29175; 9907; 6375; 799; 475; 93; 58; 5] 317481 568847 2 ((1, 1) :: repeat (1, 2) 1835911 ++ (21243794, 2) :: (1, 1) :: repeat (1, 2) 47892099 ++ (51707595, 2) :: (1, 1) :: repeat (1, 2) 271970480 ++ w) 1)).
  {
    rewrite NUM62tc1. rewrite NUM62tc2. rewrite NUM62tc3.
    replace ((1, 1) :: repeat (1, 2) 1835911 ++ (21243794, 2) :: (1, 1) :: repeat (1, 2) 47892099 ++ (51707595, 2) :: (1, 1) :: repeat (1, 2) 271970480 ++ w)
      with ((1, 1) :: (1, 2) :: (1, 2) :: repeat (1, 2) 1835909 ++ (21243794, 2) :: (1, 1) :: repeat (1, 2) 47892099 ++ (51707595, 2) :: (1, 1) :: repeat (1, 2) 271970480 ++ w)
      by (apply REP62c).
    exact (hsteps_step _ _ _ (hPX2A 568846 317481 [29175; 9907; 6375; 799; 475; 93; 58; 5] (repeat (1, 2) 1835909 ++ (21243794, 2) :: (1, 1) :: repeat (1, 2) 47892099 ++ (51707595, 2) :: (1, 1) :: repeat (1, 2) 271970480 ++ w) 1) (hsteps_refl _)).
  }
  (* step 12: hGRIND 284422 *)
  apply (hsteps_trans _ (HB [29175; 9907; 6375; 799; 475; 93; 58; 5] 317481 1 568850 ((1, 1) :: repeat (1, 2) 1835911 ++ (21243794, 2) :: (1, 1) :: repeat (1, 2) 47892099 ++ (51707595, 2) :: (1, 1) :: repeat (1, 2) 271970480 ++ w) 1)).
  {
    rewrite NUM62X9.
    rewrite NUM62X10.
    apply (hGRIND 284422 [29175; 9907; 6375; 799; 475; 93; 58; 5] 317481 ((1, 1) :: repeat (1, 2) 1835911 ++ (21243794, 2) :: (1, 1) :: repeat (1, 2) 47892099 ++ (51707595, 2) :: (1, 1) :: repeat (1, 2) 271970480 ++ w) 1); closearith.
  }
  (* step 13: P POP *)
  rewrite NUM62X11.
  rewrite NUM62X12.
  apply (sPOP1 [29175; 9907; 6375; 799; 475; 93; 58; 5] 317481 568850 (repeat (1, 2) 1835911 ++ (21243794, 2) :: (1, 1) :: repeat (1, 2) 47892099 ++ (51707595, 2) :: (1, 1) :: repeat (1, 2) 271970480 ++ w) 1); closearith.
Qed.

(* CASCADE62b: steps 14-14 of the CASCADE62 chain. *)
