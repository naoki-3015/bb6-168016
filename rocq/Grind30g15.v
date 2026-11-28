(* ================================================================= *)
(* Phase 62: CASCADE62 segments CASCADE62z. *)
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
               Grind30e11 Grind30e2 Grind30g14.

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

Lemma CASCADE62z : forall w,
  hsteps (HB [60654542; 9546949; 4860546; 349423; 101323; 57668; 5526; 626; 189; 112; 33; 19; 0] 95784201 1 51707596 ((1, 1) :: repeat (1, 2) 271970480 ++ w) 1)
         (HB [60654542; 9546949; 4860546; 349423; 101323; 57668; 5526; 626; 189; 112; 33; 19; 0] 95784202 1 51707597 (repeat (1, 2) 271970480 ++ w) 1).
Proof.
  intro w.
  (* step 749: P POP *)
  rewrite NUM62X94.
  rewrite NUM62X95.
  apply (sPOP1 [60654542; 9546949; 4860546; 349423; 101323; 57668; 5526; 626; 189; 112; 33; 19; 0] 95784201 51707596 (repeat (1, 2) 271970480 ++ w) 1); closearith.
Qed.

(* CASCADE62aa: steps 750-750 of the CASCADE62 chain. *)
