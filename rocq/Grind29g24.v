(* ================================================================= *)
(* Phase 61: CASCADE61 segments CASCADE61ao. *)
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
               Grind29e1 Grind29e13 Grind29e14 Grind29e2 Grind29e3 Grind29e7 Grind29m1 Grind29m2 Grind29g23.

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

Lemma CASCADE61ao : forall w,
  hsteps (HB [1835911; 568849; 317482; 29175; 9907; 6375; 799; 475; 93; 58; 5] 24915618 1 47892099 ((11506558, 2) :: (1, 1) :: repeat (1, 2) 135985238 ++ w) 1)
         (HB [47892099; 24915618; 1835911; 568849; 317482; 29175; 9907; 6375; 799; 475; 93; 58; 5] 11506557 1 3 (repeat (1, 2) 135985238 ++ w) 1).
Proof.
  intro w.
  (* step 1146: sTUP *)
  apply (hsteps_trans _ (HC [1835911; 568849; 317482; 29175; 9907; 6375; 799; 475; 93; 58; 5] 24915618 47892098 2 ((11506556, 2) :: (1, 1) :: repeat (1, 2) 135985238 ++ w) 1)).
  {
    rewrite NUM61X121.
    rewrite NUM61X122.
    apply (sTUP [1835911; 568849; 317482; 29175; 9907; 6375; 799; 475; 93; 58; 5] 24915618 47892099 11506558 2 ((1, 1) :: repeat (1, 2) 135985238 ++ w) 1); closearith.
  }
  (* step 1147: hGRIND_even 23946047 *)
  apply (hsteps_trans _ (HB [1835911; 568849; 317482; 29175; 9907; 6375; 799; 475; 93; 58; 5] 24915617 1 47892098 ((2, 2) :: (11506556, 2) :: (1, 1) :: repeat (1, 2) 135985238 ++ w) 1)).
  {
    rewrite NUM61X123.
    rewrite NUM61X124.
    apply (hGRIND_even 23946047 [1835911; 568849; 317482; 29175; 9907; 6375; 799; 475; 93; 58; 5] 24915617 ((11506556, 2) :: (1, 1) :: repeat (1, 2) 135985238 ++ w) 1); [exact P61u1147 | exact P61s1147].
  }
  (* step 1148: P TUP2_1 *)
  apply (hsteps_trans _ (HC [24915618; 1835911; 568849; 317482; 29175; 9907; 6375; 799; 475; 93; 58; 5] 47892098 1 2 ((11506554, 2) :: (1, 1) :: repeat (1, 2) 135985238 ++ w) 1)).
  {
    rewrite NUM61X125.
    rewrite NUM61X126.
    rewrite NUM61X127.
    apply (sTUP2_1 [1835911; 568849; 317482; 29175; 9907; 6375; 799; 475; 93; 58; 5] 24915617 47892097 11506556 ((1, 1) :: repeat (1, 2) 135985238 ++ w) 1); closearith.
  }
  (* step 1149: P TDN *)
  apply (hsteps_trans _ (HB [24915618; 1835911; 568849; 317482; 29175; 9907; 6375; 799; 475; 93; 58; 5] 47892098 1 4 ((11506554, 2) :: (1, 1) :: repeat (1, 2) 135985238 ++ w) 1)).
  {
    apply (sTDN [24915618; 1835911; 568849; 317482; 29175; 9907; 6375; 799; 475; 93; 58; 5] 47892098 ((11506554, 2) :: (1, 1) :: repeat (1, 2) 135985238 ++ w) 1).
  }
  (* step 1150: sTUP *)
  apply (hsteps_trans _ (HC [24915618; 1835911; 568849; 317482; 29175; 9907; 6375; 799; 475; 93; 58; 5] 47892098 3 2 ((11506552, 2) :: (1, 1) :: repeat (1, 2) 135985238 ++ w) 1)).
  {
    rewrite NUM61X128.
    apply (sTUP [24915618; 1835911; 568849; 317482; 29175; 9907; 6375; 799; 475; 93; 58; 5] 47892098 4 11506554 2 ((1, 1) :: repeat (1, 2) 135985238 ++ w) 1); closearith.
  }
  (* step 1151: CLEANG_even 5753275 *)
  apply (hsteps_trans _ (HB [24915618; 1835911; 568849; 317482; 29175; 9907; 6375; 799; 475; 93; 58; 5] 47892098 1 11506556 ((2, 2) :: (1, 1) :: repeat (1, 2) 135985238 ++ w) 1)).
  {
    rewrite NUM61X129.
    rewrite NUM61X130.
    apply (CLEANG_even 5753275 [24915618; 1835911; 568849; 317482; 29175; 9907; 6375; 799; 475; 93; 58; 5] 47892098 ((1, 1) :: repeat (1, 2) 135985238 ++ w) 1); exact P61s1151.
  }
  (* step 1152: P TRANS2_1 *)
  rewrite NUM61X131.
  rewrite NUM61X132.
  rewrite NUM61X133.
  apply (sTRANS2_1 [24915618; 1835911; 568849; 317482; 29175; 9907; 6375; 799; 475; 93; 58; 5] 47892098 11506555 1 (repeat (1, 2) 135985238 ++ w) 1); closearith.
Qed.

(* CASCADE61ap: steps 1153-1153 of the CASCADE61 chain. *)
