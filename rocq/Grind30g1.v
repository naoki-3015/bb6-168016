(* ================================================================= *)
(* Phase 62: CASCADE62 segments CASCADE62b. *)
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
               Grind30.

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

Lemma CASCADE62b : forall w,
  hsteps (HB [29175; 9907; 6375; 799; 475; 93; 58; 5] 317482 1 568851 (repeat (1, 2) 1835911 ++ (21243794, 2) :: (1, 1) :: repeat (1, 2) 47892099 ++ (51707595, 2) :: (1, 1) :: repeat (1, 2) 271970480 ++ w) 1)
         (HB [29175; 9907; 6375; 799; 475; 93; 58; 5] 2153393 1 4240673 ((21243794, 2) :: (1, 1) :: repeat (1, 2) 47892099 ++ (51707595, 2) :: (1, 1) :: repeat (1, 2) 271970480 ++ w) 1).
Proof.
  intro w.
  replace 2153393 with (317482 + 1835911)
    by (apply Nat.eqb_eq; vm_compute; reflexivity).
  replace 4240673 with (568851 + 2 * 1835911)
    by (apply Nat.eqb_eq; vm_compute; reflexivity).
  (* step 14: M pop12 (1835911,) *)
  apply (pop12 1835911 [29175; 9907; 6375; 799; 475; 93; 58; 5] 317482 568851 ((21243794, 2) :: (1, 1) :: repeat (1, 2) 47892099 ++ (51707595, 2) :: (1, 1) :: repeat (1, 2) 271970480 ++ w) 1); closearith.
Qed.

(* CASCADE62c: steps 15-70 of the CASCADE62 chain. *)
