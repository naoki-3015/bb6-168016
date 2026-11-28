(* ================================================================= *)
(* Phase 63: CASCADE63 segments CASCADE63d and the CASCADE63 assembly. *)
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
               Grind31 Grind31g1 Grind31g2 Grind31s.

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

Lemma CASCADE63d : forall w,
  hsteps (HB [130856035; 65515088; 349423; 101323; 57668; 5526; 626; 189; 112; 33; 19; 0] 246445595 1 3 (repeat (1, 2) 595648558 ++ w) 1)
         (HB [130856035; 65515088; 349423; 101323; 57668; 5526; 626; 189; 112; 33; 19; 0] 842094153 1 1191297119 (w) 1).
Proof.
  intro w.
  rewrite S63rd1.
  rewrite S63rd2.
  (* step 17: M pop12 (595648558,) *)
  apply (pop12 595648558 [130856035; 65515088; 349423; 101323; 57668; 5526; 626; 189; 112; 33; 19; 0] 246445595 3 (w) 1); exact S63rd3.
Qed.

Lemma CASCADE63 : forall w,
  hsteps (HC [367754682; 60654542; 9546949; 4860546; 349423; 101323; 57668; 5526; 626; 189; 112; 33; 19; 0] 0 3 2 (repeat (1, 2) 595648556 ++ w) 1)
         (HB [130856035; 65515088; 349423; 101323; 57668; 5526; 626; 189; 112; 33; 19; 0] 842094153 1 1191297119 (w) 1).
Proof.
  intro w.
  apply (hsteps_trans _ (HB [349423; 101323; 57668; 5526; 626; 189; 112; 33; 19; 0] 4860546 1 9546951 (repeat (1, 2) 60654542 ++ (246445596, 2) :: (1, 1) :: repeat (1, 2) 595648558 ++ w) 1)).
  { apply (CASCADE63a w). }
  apply (hsteps_trans _ (HB [349423; 101323; 57668; 5526; 626; 189; 112; 33; 19; 0] 65515088 1 130856035 ((246445596, 2) :: (1, 1) :: repeat (1, 2) 595648558 ++ w) 1)).
  { apply (CASCADE63b w). }
  apply (hsteps_trans _ (HB [130856035; 65515088; 349423; 101323; 57668; 5526; 626; 189; 112; 33; 19; 0] 246445595 1 3 (repeat (1, 2) 595648558 ++ w) 1)).
  { apply (CASCADE63c w). }
  apply (CASCADE63d w).
Qed.
