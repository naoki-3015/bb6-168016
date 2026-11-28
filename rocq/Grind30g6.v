(* ================================================================= *)
(* Phase 62: CASCADE62 segments CASCADE62q. *)
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
               Grind30g5.

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

Lemma CASCADE62q : forall w,
  hsteps (HB [101323; 57668; 5526; 626; 189; 112; 33; 19; 0] 39489 1 3 (repeat (1, 2) 309934 ++ (1065599, 2) :: (1, 1) :: repeat (1, 2) 4240674 ++ (12762444, 2) :: (1, 1) :: repeat (1, 2) 47892099 ++ (51707595, 2) :: (1, 1) :: repeat (1, 2) 271970480 ++ w) 1)
         (HB [101323; 57668; 5526; 626; 189; 112; 33; 19; 0] 349423 1 619871 ((1065599, 2) :: (1, 1) :: repeat (1, 2) 4240674 ++ (12762444, 2) :: (1, 1) :: repeat (1, 2) 47892099 ++ (51707595, 2) :: (1, 1) :: repeat (1, 2) 271970480 ++ w) 1).
Proof.
  intro w.
  replace 349423 with (39489 + 309934)
    by (apply Nat.eqb_eq; vm_compute; reflexivity).
  replace 619871 with (3 + 2 * 309934)
    by (apply Nat.eqb_eq; vm_compute; reflexivity).
  (* step 724: M pop12 (309934,) *)
  apply (pop12 309934 [101323; 57668; 5526; 626; 189; 112; 33; 19; 0] 39489 3 ((1065599, 2) :: (1, 1) :: repeat (1, 2) 4240674 ++ (12762444, 2) :: (1, 1) :: repeat (1, 2) 47892099 ++ (51707595, 2) :: (1, 1) :: repeat (1, 2) 271970480 ++ w) 1); closearith.
Qed.

(* CASCADE62r: steps 725-730 of the CASCADE62 chain. *)
