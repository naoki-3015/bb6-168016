(* ================================================================= *)
(* Phase 61: CASCADE61 segments CASCADE61ak. *)
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
               Grind29e10 Grind29e9 Grind29m1 Grind29g19.

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

Lemma CASCADE61ak : forall w,
  hsteps (HB [568849; 317482; 29175; 9907; 6375; 799; 475; 93; 58; 5] 1835911 1 3426527 ((4913917, 2) :: (1, 1) :: repeat (1, 2) 21489090 ++ (11506558, 2) :: (1, 1) :: repeat (1, 2) 135985238 ++ w) 1)
         (HB [1835911; 568849; 317482; 29175; 9907; 6375; 799; 475; 93; 58; 5] 3426526 1 4913916 (repeat (1, 2) 1 ++ (1, 1) :: repeat (1, 2) 21489090 ++ (11506558, 2) :: (1, 1) :: repeat (1, 2) 135985238 ++ w) 1).
Proof.
  intro w.
  (* step 1137: sTUP *)
  apply (hsteps_trans _ (HC [568849; 317482; 29175; 9907; 6375; 799; 475; 93; 58; 5] 1835911 3426526 2 ((4913915, 2) :: (1, 1) :: repeat (1, 2) 21489090 ++ (11506558, 2) :: (1, 1) :: repeat (1, 2) 135985238 ++ w) 1)).
  {
    rewrite NUM61X109.
    rewrite NUM61X110.
    apply (sTUP [568849; 317482; 29175; 9907; 6375; 799; 475; 93; 58; 5] 1835911 3426527 4913917 2 ((1, 1) :: repeat (1, 2) 21489090 ++ (11506558, 2) :: (1, 1) :: repeat (1, 2) 135985238 ++ w) 1); closearith.
  }
  (* step 1138: hGRIND_even 1713261 *)
  apply (hsteps_trans _ (HB [568849; 317482; 29175; 9907; 6375; 799; 475; 93; 58; 5] 1835910 1 3426526 ((2, 2) :: (4913915, 2) :: (1, 1) :: repeat (1, 2) 21489090 ++ (11506558, 2) :: (1, 1) :: repeat (1, 2) 135985238 ++ w) 1)).
  {
    rewrite NUM61X111.
    rewrite NUM61X112.
    apply (hGRIND_even 1713261 [568849; 317482; 29175; 9907; 6375; 799; 475; 93; 58; 5] 1835910 ((4913915, 2) :: (1, 1) :: repeat (1, 2) 21489090 ++ (11506558, 2) :: (1, 1) :: repeat (1, 2) 135985238 ++ w) 1); [exact P61u1138 | exact P61s1138].
  }
  (* step 1139: P TUP2_1 *)
  apply (hsteps_trans _ (HC [1835911; 568849; 317482; 29175; 9907; 6375; 799; 475; 93; 58; 5] 3426526 1 2 ((4913913, 2) :: (1, 1) :: repeat (1, 2) 21489090 ++ (11506558, 2) :: (1, 1) :: repeat (1, 2) 135985238 ++ w) 1)).
  {
    rewrite NUM61X113.
    rewrite NUM61X114.
    rewrite NUM61X115.
    apply (sTUP2_1 [568849; 317482; 29175; 9907; 6375; 799; 475; 93; 58; 5] 1835910 3426525 4913915 ((1, 1) :: repeat (1, 2) 21489090 ++ (11506558, 2) :: (1, 1) :: repeat (1, 2) 135985238 ++ w) 1); closearith.
  }
  (* step 1140: P TDN *)
  apply (hsteps_trans _ (HB [1835911; 568849; 317482; 29175; 9907; 6375; 799; 475; 93; 58; 5] 3426526 1 4 ((4913913, 2) :: (1, 1) :: repeat (1, 2) 21489090 ++ (11506558, 2) :: (1, 1) :: repeat (1, 2) 135985238 ++ w) 1)).
  {
    apply (sTDN [1835911; 568849; 317482; 29175; 9907; 6375; 799; 475; 93; 58; 5] 3426526 ((4913913, 2) :: (1, 1) :: repeat (1, 2) 21489090 ++ (11506558, 2) :: (1, 1) :: repeat (1, 2) 135985238 ++ w) 1).
  }
  (* step 1141: sTUP *)
  apply (hsteps_trans _ (HC [1835911; 568849; 317482; 29175; 9907; 6375; 799; 475; 93; 58; 5] 3426526 3 2 ((4913911, 2) :: (1, 1) :: repeat (1, 2) 21489090 ++ (11506558, 2) :: (1, 1) :: repeat (1, 2) 135985238 ++ w) 1)).
  {
    rewrite NUM61X116.
    apply (sTUP [1835911; 568849; 317482; 29175; 9907; 6375; 799; 475; 93; 58; 5] 3426526 4 4913913 2 ((1, 1) :: repeat (1, 2) 21489090 ++ (11506558, 2) :: (1, 1) :: repeat (1, 2) 135985238 ++ w) 1); closearith.
  }
  (* step 1142: CLEANG_odd 2456954 *)
  rewrite NUM61X117.
  rewrite NUM61X118.
  replace (repeat (1, 2) 1 ++ (1, 1) :: repeat (1, 2) 21489090 ++ (11506558, 2) :: (1, 1) :: repeat (1, 2) 135985238 ++ w) with ((1, 2) :: (1, 1) :: repeat (1, 2) 21489090 ++ (11506558, 2) :: (1, 1) :: repeat (1, 2) 135985238 ++ w) by sec_eq.
  apply (CLEANG_odd 2456954 [1835911; 568849; 317482; 29175; 9907; 6375; 799; 475; 93; 58; 5] 3426526 ((1, 1) :: repeat (1, 2) 21489090 ++ (11506558, 2) :: (1, 1) :: repeat (1, 2) 135985238 ++ w) 1); exact P61s1142.
Qed.

(* CASCADE61al: steps 1143-1143 of the CASCADE61 chain. *)
