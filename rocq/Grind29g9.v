(* ================================================================= *)
(* Phase 61: CASCADE61 segments CASCADE61t. *)
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
               Grind29e14 Grind29e3 Grind29e4 Grind29g8.

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

Lemma CASCADE61t : forall w,
  hsteps (HB [23739; 16527; 2607; 991; 619; 109; 19; 0] 120150 1 181245 ((293675, 2) :: (1, 1) :: repeat (1, 2) 709792 ++ (8340443, 2) :: (1, 1) :: repeat (1, 2) 21489090 ++ (11506558, 2) :: (1, 1) :: repeat (1, 2) 135985238 ++ w) 1)
         (HB [120150; 23739; 16527; 2607; 991; 619; 109; 19; 0] 181244 1 293674 (repeat (1, 2) 1 ++ (1, 1) :: repeat (1, 2) 709792 ++ (8340443, 2) :: (1, 1) :: repeat (1, 2) 21489090 ++ (11506558, 2) :: (1, 1) :: repeat (1, 2) 135985238 ++ w) 1).
Proof.
  intro w.
  (* step 673: sTUP *)
  apply (hsteps_trans _ (HC [23739; 16527; 2607; 991; 619; 109; 19; 0] 120150 181244 2 ((293673, 2) :: (1, 1) :: repeat (1, 2) 709792 ++ (8340443, 2) :: (1, 1) :: repeat (1, 2) 21489090 ++ (11506558, 2) :: (1, 1) :: repeat (1, 2) 135985238 ++ w) 1)).
  {
    rewrite NUM61X56.
    rewrite NUM61X57.
    apply (sTUP [23739; 16527; 2607; 991; 619; 109; 19; 0] 120150 181245 293675 2 ((1, 1) :: repeat (1, 2) 709792 ++ (8340443, 2) :: (1, 1) :: repeat (1, 2) 21489090 ++ (11506558, 2) :: (1, 1) :: repeat (1, 2) 135985238 ++ w) 1); closearith.
  }
  (* step 674: hGRIND_even 90620 *)
  apply (hsteps_trans _ (HB [23739; 16527; 2607; 991; 619; 109; 19; 0] 120149 1 181244 ((2, 2) :: (293673, 2) :: (1, 1) :: repeat (1, 2) 709792 ++ (8340443, 2) :: (1, 1) :: repeat (1, 2) 21489090 ++ (11506558, 2) :: (1, 1) :: repeat (1, 2) 135985238 ++ w) 1)).
  {
    rewrite NUM61X58.
    rewrite NUM61X59.
    apply (hGRIND_even 90620 [23739; 16527; 2607; 991; 619; 109; 19; 0] 120149 ((293673, 2) :: (1, 1) :: repeat (1, 2) 709792 ++ (8340443, 2) :: (1, 1) :: repeat (1, 2) 21489090 ++ (11506558, 2) :: (1, 1) :: repeat (1, 2) 135985238 ++ w) 1); closearith.
  }
  (* step 675: P TUP2_1 *)
  apply (hsteps_trans _ (HC [120150; 23739; 16527; 2607; 991; 619; 109; 19; 0] 181244 1 2 ((293671, 2) :: (1, 1) :: repeat (1, 2) 709792 ++ (8340443, 2) :: (1, 1) :: repeat (1, 2) 21489090 ++ (11506558, 2) :: (1, 1) :: repeat (1, 2) 135985238 ++ w) 1)).
  {
    rewrite NUM61X60.
    rewrite NUM61X61.
    rewrite NUM61X62.
    apply (sTUP2_1 [23739; 16527; 2607; 991; 619; 109; 19; 0] 120149 181243 293673 ((1, 1) :: repeat (1, 2) 709792 ++ (8340443, 2) :: (1, 1) :: repeat (1, 2) 21489090 ++ (11506558, 2) :: (1, 1) :: repeat (1, 2) 135985238 ++ w) 1); closearith.
  }
  (* step 676: P TDN *)
  apply (hsteps_trans _ (HB [120150; 23739; 16527; 2607; 991; 619; 109; 19; 0] 181244 1 4 ((293671, 2) :: (1, 1) :: repeat (1, 2) 709792 ++ (8340443, 2) :: (1, 1) :: repeat (1, 2) 21489090 ++ (11506558, 2) :: (1, 1) :: repeat (1, 2) 135985238 ++ w) 1)).
  {
    apply (sTDN [120150; 23739; 16527; 2607; 991; 619; 109; 19; 0] 181244 ((293671, 2) :: (1, 1) :: repeat (1, 2) 709792 ++ (8340443, 2) :: (1, 1) :: repeat (1, 2) 21489090 ++ (11506558, 2) :: (1, 1) :: repeat (1, 2) 135985238 ++ w) 1).
  }
  (* step 677: sTUP *)
  apply (hsteps_trans _ (HC [120150; 23739; 16527; 2607; 991; 619; 109; 19; 0] 181244 3 2 ((293669, 2) :: (1, 1) :: repeat (1, 2) 709792 ++ (8340443, 2) :: (1, 1) :: repeat (1, 2) 21489090 ++ (11506558, 2) :: (1, 1) :: repeat (1, 2) 135985238 ++ w) 1)).
  {
    rewrite NUM61X63.
    apply (sTUP [120150; 23739; 16527; 2607; 991; 619; 109; 19; 0] 181244 4 293671 2 ((1, 1) :: repeat (1, 2) 709792 ++ (8340443, 2) :: (1, 1) :: repeat (1, 2) 21489090 ++ (11506558, 2) :: (1, 1) :: repeat (1, 2) 135985238 ++ w) 1); closearith.
  }
  (* step 678: CLEANG_odd 146833 *)
  rewrite NUM61X64.
  rewrite NUM61X65.
  replace (repeat (1, 2) 1 ++ (1, 1) :: repeat (1, 2) 709792 ++ (8340443, 2) :: (1, 1) :: repeat (1, 2) 21489090 ++ (11506558, 2) :: (1, 1) :: repeat (1, 2) 135985238 ++ w) with ((1, 2) :: (1, 1) :: repeat (1, 2) 709792 ++ (8340443, 2) :: (1, 1) :: repeat (1, 2) 21489090 ++ (11506558, 2) :: (1, 1) :: repeat (1, 2) 135985238 ++ w) by sec_eq.
  apply (CLEANG_odd 146833 [120150; 23739; 16527; 2607; 991; 619; 109; 19; 0] 181244 ((1, 1) :: repeat (1, 2) 709792 ++ (8340443, 2) :: (1, 1) :: repeat (1, 2) 21489090 ++ (11506558, 2) :: (1, 1) :: repeat (1, 2) 135985238 ++ w) 1); closearith.
Qed.

(* CASCADE61u: steps 679-679 of the CASCADE61 chain. *)
