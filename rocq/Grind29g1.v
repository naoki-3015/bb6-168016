(* ================================================================= *)
(* Phase 61: CASCADE61 segments CASCADE61b. *)
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
               Grind29s Grind29.

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

Lemma CASCADE61b : forall w,
  hsteps (HB [177445; 95640; 10129; 1243; 207; 19] 698173 1 1236013 (repeat (1, 2) 10126538 ++ (54484740, 2) :: (1, 1) :: repeat (1, 2) 135985238 ++ w) 1)
         (HB [177445; 95640; 10129; 1243; 207; 19] 10824711 1 21489089 ((54484740, 2) :: (1, 1) :: repeat (1, 2) 135985238 ++ w) 1).
Proof.
  intro w.
  rewrite S61rb1.
  rewrite S61rb2.
  (* step 9: M pop12 (10126538,) *)
  apply (pop12 10126538 [177445; 95640; 10129; 1243; 207; 19] 698173 1236013 ((54484740, 2) :: (1, 1) :: repeat (1, 2) 135985238 ++ w) 1); exact S61rb3.
Qed.

(* CASCADE61c: steps 10-65 of the CASCADE61 chain. *)
