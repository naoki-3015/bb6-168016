(* ================================================================= *)
(* Phase 62: CASCADE62 segments CASCADE62y. *)
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
               Grind30s Grind30g13.

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

Lemma CASCADE62y : forall w,
  hsteps (HB [60654542; 9546949; 4860546; 349423; 101323; 57668; 5526; 626; 189; 112; 33; 19; 0] 95784200 1 51707594 (repeat (1, 2) 1 ++ (1, 1) :: repeat (1, 2) 271970480 ++ w) 1)
         (HB [60654542; 9546949; 4860546; 349423; 101323; 57668; 5526; 626; 189; 112; 33; 19; 0] 95784201 1 51707596 ((1, 1) :: repeat (1, 2) 271970480 ++ w) 1).
Proof.
  intro w.
  rewrite S62ry1.
  rewrite S62ry2.
  (* step 748: M pop12 (1,) *)
  apply (pop12 1 [60654542; 9546949; 4860546; 349423; 101323; 57668; 5526; 626; 189; 112; 33; 19; 0] 95784200 51707594 ((1, 1) :: repeat (1, 2) 271970480 ++ w) 1); exact S62ry3.
Qed.

(* CASCADE62z: steps 749-749 of the CASCADE62 chain. *)
