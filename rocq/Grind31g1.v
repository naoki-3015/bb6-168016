(* ================================================================= *)
(* Phase 63: CASCADE63 segments CASCADE63b. *)
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
               Grind31s Grind31.

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

Lemma CASCADE63b : forall w,
  hsteps (HB [349423; 101323; 57668; 5526; 626; 189; 112; 33; 19; 0] 4860546 1 9546951 (repeat (1, 2) 60654542 ++ (246445596, 2) :: (1, 1) :: repeat (1, 2) 595648558 ++ w) 1)
         (HB [349423; 101323; 57668; 5526; 626; 189; 112; 33; 19; 0] 65515088 1 130856035 ((246445596, 2) :: (1, 1) :: repeat (1, 2) 595648558 ++ w) 1).
Proof.
  intro w.
  rewrite S63rb1.
  rewrite S63rb2.
  (* step 9: M pop12 (60654542,) *)
  apply (pop12 60654542 [349423; 101323; 57668; 5526; 626; 189; 112; 33; 19; 0] 4860546 9546951 ((246445596, 2) :: (1, 1) :: repeat (1, 2) 595648558 ++ w) 1); exact S63rb3.
Qed.

(* CASCADE63c: steps 10-16 of the CASCADE63 chain. *)
