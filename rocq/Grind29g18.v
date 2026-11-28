(* ================================================================= *)
(* Phase 61: CASCADE61 segments CASCADE61ai. *)
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
               Grind29e12 Grind29e13 Grind29e14 Grind29e3 Grind29e4 Grind29g17.

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

Lemma CASCADE61ai : forall w,
  hsteps (HB [29175; 9907; 6375; 799; 475; 93; 58; 5] 317482 1 568849 ((122650, 2) :: (1, 1) :: repeat (1, 2) 1713262 ++ (4913917, 2) :: (1, 1) :: repeat (1, 2) 21489090 ++ (11506558, 2) :: (1, 1) :: repeat (1, 2) 135985238 ++ w) 1)
         (HB [568849; 317482; 29175; 9907; 6375; 799; 475; 93; 58; 5] 122649 1 3 (repeat (1, 2) 1713262 ++ (4913917, 2) :: (1, 1) :: repeat (1, 2) 21489090 ++ (11506558, 2) :: (1, 1) :: repeat (1, 2) 135985238 ++ w) 1).
Proof.
  intro w.
  (* step 1129: sTUP *)
  apply (hsteps_trans _ (HC [29175; 9907; 6375; 799; 475; 93; 58; 5] 317482 568848 2 ((122648, 2) :: (1, 1) :: repeat (1, 2) 1713262 ++ (4913917, 2) :: (1, 1) :: repeat (1, 2) 21489090 ++ (11506558, 2) :: (1, 1) :: repeat (1, 2) 135985238 ++ w) 1)).
  {
    rewrite NUM61X99.
    replace ((122648, 2) :: (1, 1) :: repeat (1, 2) 1713262 ++ (4913917, 2) :: (1, 1) :: repeat (1, 2) 21489090 ++ (11506558, 2) :: (1, 1) :: repeat (1, 2) 135985238 ++ w) with ((122650 - 2, 2) :: (1, 1) :: repeat (1, 2) 1713262 ++ (4913917, 2) :: (1, 1) :: repeat (1, 2) 21489090 ++ (11506558, 2) :: (1, 1) :: repeat (1, 2) 135985238 ++ w) by sec_eq.
    apply (sTUP [29175; 9907; 6375; 799; 475; 93; 58; 5] 317482 568849 122650 2 ((1, 1) :: repeat (1, 2) 1713262 ++ (4913917, 2) :: (1, 1) :: repeat (1, 2) 21489090 ++ (11506558, 2) :: (1, 1) :: repeat (1, 2) 135985238 ++ w) 1); closearith.
  }
  (* step 1130: hGRIND_even 284422 *)
  apply (hsteps_trans _ (HB [29175; 9907; 6375; 799; 475; 93; 58; 5] 317481 1 568848 ((2, 2) :: (122648, 2) :: (1, 1) :: repeat (1, 2) 1713262 ++ (4913917, 2) :: (1, 1) :: repeat (1, 2) 21489090 ++ (11506558, 2) :: (1, 1) :: repeat (1, 2) 135985238 ++ w) 1)).
  {
    rewrite NUM61X100.
    rewrite NUM61X101.
    apply (hGRIND_even 284422 [29175; 9907; 6375; 799; 475; 93; 58; 5] 317481 ((122648, 2) :: (1, 1) :: repeat (1, 2) 1713262 ++ (4913917, 2) :: (1, 1) :: repeat (1, 2) 21489090 ++ (11506558, 2) :: (1, 1) :: repeat (1, 2) 135985238 ++ w) 1); closearith.
  }
  (* step 1131: P TUP2_1 *)
  apply (hsteps_trans _ (HC [317482; 29175; 9907; 6375; 799; 475; 93; 58; 5] 568848 1 2 ((122646, 2) :: (1, 1) :: repeat (1, 2) 1713262 ++ (4913917, 2) :: (1, 1) :: repeat (1, 2) 21489090 ++ (11506558, 2) :: (1, 1) :: repeat (1, 2) 135985238 ++ w) 1)).
  {
    rewrite NUM61X102.
    rewrite NUM61X103.
    replace ((122646, 2) :: (1, 1) :: repeat (1, 2) 1713262 ++ (4913917, 2) :: (1, 1) :: repeat (1, 2) 21489090 ++ (11506558, 2) :: (1, 1) :: repeat (1, 2) 135985238 ++ w) with ((122648 - 2, 2) :: (1, 1) :: repeat (1, 2) 1713262 ++ (4913917, 2) :: (1, 1) :: repeat (1, 2) 21489090 ++ (11506558, 2) :: (1, 1) :: repeat (1, 2) 135985238 ++ w) by sec_eq.
    apply (sTUP2_1 [29175; 9907; 6375; 799; 475; 93; 58; 5] 317481 568847 122648 ((1, 1) :: repeat (1, 2) 1713262 ++ (4913917, 2) :: (1, 1) :: repeat (1, 2) 21489090 ++ (11506558, 2) :: (1, 1) :: repeat (1, 2) 135985238 ++ w) 1); closearith.
  }
  (* step 1132: P TDN *)
  apply (hsteps_trans _ (HB [317482; 29175; 9907; 6375; 799; 475; 93; 58; 5] 568848 1 4 ((122646, 2) :: (1, 1) :: repeat (1, 2) 1713262 ++ (4913917, 2) :: (1, 1) :: repeat (1, 2) 21489090 ++ (11506558, 2) :: (1, 1) :: repeat (1, 2) 135985238 ++ w) 1)).
  {
    apply (sTDN [317482; 29175; 9907; 6375; 799; 475; 93; 58; 5] 568848 ((122646, 2) :: (1, 1) :: repeat (1, 2) 1713262 ++ (4913917, 2) :: (1, 1) :: repeat (1, 2) 21489090 ++ (11506558, 2) :: (1, 1) :: repeat (1, 2) 135985238 ++ w) 1).
  }
  (* step 1133: sTUP *)
  apply (hsteps_trans _ (HC [317482; 29175; 9907; 6375; 799; 475; 93; 58; 5] 568848 3 2 ((122644, 2) :: (1, 1) :: repeat (1, 2) 1713262 ++ (4913917, 2) :: (1, 1) :: repeat (1, 2) 21489090 ++ (11506558, 2) :: (1, 1) :: repeat (1, 2) 135985238 ++ w) 1)).
  {
    replace ((122644, 2) :: (1, 1) :: repeat (1, 2) 1713262 ++ (4913917, 2) :: (1, 1) :: repeat (1, 2) 21489090 ++ (11506558, 2) :: (1, 1) :: repeat (1, 2) 135985238 ++ w) with ((122646 - 2, 2) :: (1, 1) :: repeat (1, 2) 1713262 ++ (4913917, 2) :: (1, 1) :: repeat (1, 2) 21489090 ++ (11506558, 2) :: (1, 1) :: repeat (1, 2) 135985238 ++ w) by sec_eq.
    apply (sTUP [317482; 29175; 9907; 6375; 799; 475; 93; 58; 5] 568848 4 122646 2 ((1, 1) :: repeat (1, 2) 1713262 ++ (4913917, 2) :: (1, 1) :: repeat (1, 2) 21489090 ++ (11506558, 2) :: (1, 1) :: repeat (1, 2) 135985238 ++ w) 1); closearith.
  }
  (* step 1134: CLEANG_even 61321 *)
  apply (hsteps_trans _ (HB [317482; 29175; 9907; 6375; 799; 475; 93; 58; 5] 568848 1 122648 ((2, 2) :: (1, 1) :: repeat (1, 2) 1713262 ++ (4913917, 2) :: (1, 1) :: repeat (1, 2) 21489090 ++ (11506558, 2) :: (1, 1) :: repeat (1, 2) 135985238 ++ w) 1)).
  {
    rewrite NUM61X104.
    rewrite NUM61X105.
    apply (CLEANG_even 61321 [317482; 29175; 9907; 6375; 799; 475; 93; 58; 5] 568848 ((1, 1) :: repeat (1, 2) 1713262 ++ (4913917, 2) :: (1, 1) :: repeat (1, 2) 21489090 ++ (11506558, 2) :: (1, 1) :: repeat (1, 2) 135985238 ++ w) 1); closearith.
  }
  (* step 1135: P TRANS2_1 *)
  rewrite NUM61X106.
  rewrite NUM61X107.
  rewrite NUM61X108.
  apply (sTRANS2_1 [317482; 29175; 9907; 6375; 799; 475; 93; 58; 5] 568848 122647 1 (repeat (1, 2) 1713262 ++ (4913917, 2) :: (1, 1) :: repeat (1, 2) 21489090 ++ (11506558, 2) :: (1, 1) :: repeat (1, 2) 135985238 ++ w) 1); closearith.
Qed.

(* CASCADE61aj: steps 1136-1136 of the CASCADE61 chain. *)
