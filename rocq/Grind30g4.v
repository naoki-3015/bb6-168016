(* ================================================================= *)
(* Phase 62: CASCADE62 segments CASCADE62l. *)
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
               Grind30g3.

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

Lemma CASCADE62l : forall w,
  hsteps (HB [20370; 6015; 3055; 1113; 590; 58; 5] 37226 1 36885 (repeat (1, 2) 136524 ++ (1685469, 2) :: (1, 1) :: repeat (1, 2) 4240674 ++ (12762444, 2) :: (1, 1) :: repeat (1, 2) 47892099 ++ (51707595, 2) :: (1, 1) :: repeat (1, 2) 271970480 ++ w) 1)
         (HB [20370; 6015; 3055; 1113; 590; 58; 5] 173750 1 309933 ((1685469, 2) :: (1, 1) :: repeat (1, 2) 4240674 ++ (12762444, 2) :: (1, 1) :: repeat (1, 2) 47892099 ++ (51707595, 2) :: (1, 1) :: repeat (1, 2) 271970480 ++ w) 1).
Proof.
  intro w.
  replace 173750 with (37226 + 136524)
    by (apply Nat.eqb_eq; vm_compute; reflexivity).
  replace 309933 with (36885 + 2 * 136524)
    by (apply Nat.eqb_eq; vm_compute; reflexivity).
  (* step 514: M pop12 (136524,) *)
  apply (pop12 136524 [20370; 6015; 3055; 1113; 590; 58; 5] 37226 36885 ((1685469, 2) :: (1, 1) :: repeat (1, 2) 4240674 ++ (12762444, 2) :: (1, 1) :: repeat (1, 2) 47892099 ++ (51707595, 2) :: (1, 1) :: repeat (1, 2) 271970480 ++ w) 1); closearith.
Qed.

(* CASCADE62m: steps 515-570 of the CASCADE62 chain. *)
