(* ================================================================= *)
(* Phase 61: CASCADE61 segments CASCADE61y. *)
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
               Grind29g13.

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

Lemma CASCADE61y : forall w,
  hsteps (HB [2607; 991; 619; 109; 19; 0] 16527 1 23741 (repeat (1, 2) 120150 ++ (650736, 2) :: (1, 1) :: repeat (1, 2) 1713262 ++ (4913917, 2) :: (1, 1) :: repeat (1, 2) 21489090 ++ (11506558, 2) :: (1, 1) :: repeat (1, 2) 135985238 ++ w) 1)
         (HB [2607; 991; 619; 109; 19; 0] 136677 1 264041 ((650736, 2) :: (1, 1) :: repeat (1, 2) 1713262 ++ (4913917, 2) :: (1, 1) :: repeat (1, 2) 21489090 ++ (11506558, 2) :: (1, 1) :: repeat (1, 2) 135985238 ++ w) 1).
Proof.
  intro w.
  replace 136677 with (16527 + 120150)
    by (apply Nat.eqb_eq; vm_compute; reflexivity).
  replace 264041 with (23741 + 2 * 120150)
    by (apply Nat.eqb_eq; vm_compute; reflexivity).
  (* step 696: M pop12 (120150,) *)
  apply (pop12 120150 [2607; 991; 619; 109; 19; 0] 16527 23741 ((650736, 2) :: (1, 1) :: repeat (1, 2) 1713262 ++ (4913917, 2) :: (1, 1) :: repeat (1, 2) 21489090 ++ (11506558, 2) :: (1, 1) :: repeat (1, 2) 135985238 ++ w) 1); closearith.
Qed.

(* CASCADE61z: steps 697-752 of the CASCADE61 chain. *)
