(* ================================================================= *)
(* Phase 61: CASCADE61 segments CASCADE61h. *)
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
               Grind29g2.

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

Lemma CASCADE61h : forall w,
  hsteps (HB [25294; 2776; 547; 91; 49; 14; 5] 45308 1 4 ((33198, 2) :: (1, 1) :: repeat (1, 2) 177445 ++ (10469819, 2) :: (1, 1) :: repeat (1, 2) 21489090 ++ (11506558, 2) :: (1, 1) :: repeat (1, 2) 135985238 ++ w) 1)
         (HB [45309; 25294; 2776; 547; 91; 49; 14; 5] 33201 1 3 (repeat (1, 2) 177445 ++ (10469819, 2) :: (1, 1) :: repeat (1, 2) 21489090 ++ (11506558, 2) :: (1, 1) :: repeat (1, 2) 135985238 ++ w) 1).
Proof.
  intro w.
  (* step 290: sTUP *)
  apply (hsteps_trans _ (HC [25294; 2776; 547; 91; 49; 14; 5] 45308 3 2 ((33196, 2) :: (1, 1) :: repeat (1, 2) 177445 ++ (10469819, 2) :: (1, 1) :: repeat (1, 2) 21489090 ++ (11506558, 2) :: (1, 1) :: repeat (1, 2) 135985238 ++ w) 1)).
  {
    replace ((33196, 2) :: (1, 1) :: repeat (1, 2) 177445 ++ (10469819, 2) :: (1, 1) :: repeat (1, 2) 21489090 ++ (11506558, 2) :: (1, 1) :: repeat (1, 2) 135985238 ++ w) with ((33198 - 2, 2) :: (1, 1) :: repeat (1, 2) 177445 ++ (10469819, 2) :: (1, 1) :: repeat (1, 2) 21489090 ++ (11506558, 2) :: (1, 1) :: repeat (1, 2) 135985238 ++ w) by sec_eq.
    apply (sTUP [25294; 2776; 547; 91; 49; 14; 5] 45308 4 33198 2 ((1, 1) :: repeat (1, 2) 177445 ++ (10469819, 2) :: (1, 1) :: repeat (1, 2) 21489090 ++ (11506558, 2) :: (1, 1) :: repeat (1, 2) 135985238 ++ w) 1); closearith.
  }
  (* step 291: CLEANG_even 16597 *)
  apply (hsteps_trans _ (HB [25294; 2776; 547; 91; 49; 14; 5] 45308 1 33200 ((2, 2) :: (1, 1) :: repeat (1, 2) 177445 ++ (10469819, 2) :: (1, 1) :: repeat (1, 2) 21489090 ++ (11506558, 2) :: (1, 1) :: repeat (1, 2) 135985238 ++ w) 1)).
  {
    apply (CLEANG_even 16597 [25294; 2776; 547; 91; 49; 14; 5] 45308 ((1, 1) :: repeat (1, 2) 177445 ++ (10469819, 2) :: (1, 1) :: repeat (1, 2) 21489090 ++ (11506558, 2) :: (1, 1) :: repeat (1, 2) 135985238 ++ w) 1); closearith.
  }
  (* step 292: P TRANS2_1 *)
  apply (sTRANS2_1 [25294; 2776; 547; 91; 49; 14; 5] 45308 33199 1 (repeat (1, 2) 177445 ++ (10469819, 2) :: (1, 1) :: repeat (1, 2) 21489090 ++ (11506558, 2) :: (1, 1) :: repeat (1, 2) 135985238 ++ w) 1); closearith.
Qed.

(* CASCADE61i: steps 293-293 of the CASCADE61 chain. *)
