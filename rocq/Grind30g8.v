(* ================================================================= *)
(* Phase 62: CASCADE62 segments CASCADE62s. *)
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
               Grind30g7.

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

Lemma CASCADE62s : forall w,
  hsteps (HB [349423; 101323; 57668; 5526; 626; 189; 112; 33; 19; 0] 619870 1 1065598 (repeat (1, 2) 1 ++ (1, 1) :: repeat (1, 2) 4240674 ++ (12762444, 2) :: (1, 1) :: repeat (1, 2) 47892099 ++ (51707595, 2) :: (1, 1) :: repeat (1, 2) 271970480 ++ w) 1)
         (HB [349423; 101323; 57668; 5526; 626; 189; 112; 33; 19; 0] 619871 1 1065600 ((1, 1) :: repeat (1, 2) 4240674 ++ (12762444, 2) :: (1, 1) :: repeat (1, 2) 47892099 ++ (51707595, 2) :: (1, 1) :: repeat (1, 2) 271970480 ++ w) 1).
Proof.
  intro w.
  replace 619871 with (619870 + 1)
    by (apply Nat.eqb_eq; vm_compute; reflexivity).
  replace 1065600 with (1065598 + 2 * 1)
    by (apply Nat.eqb_eq; vm_compute; reflexivity).
  (* step 731: M pop12 (1,) *)
  apply (pop12 1 [349423; 101323; 57668; 5526; 626; 189; 112; 33; 19; 0] 619870 1065598 ((1, 1) :: repeat (1, 2) 4240674 ++ (12762444, 2) :: (1, 1) :: repeat (1, 2) 47892099 ++ (51707595, 2) :: (1, 1) :: repeat (1, 2) 271970480 ++ w) 1); closearith.
Qed.

(* CASCADE62t: steps 732-732 of the CASCADE62 chain. *)
