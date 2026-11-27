(* ================================================================= *)
(* Phase 60 (cascade, part 2): CASCADE60k-v and CASCADE60, the     *)
(* assembly of the 22 segments.  Split from Grind28.v for the      *)
(* operational reason recorded in Grind28.v's header (compile      *)
(* resident set at Phase 60 numeral depths); every lemma           *)
(* statement is the one the phase's single-file draft carried.     *)
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
               Grind28a Grind28ac Grind28ag Grind28ah Grind28c
               Grind28i Grind28.

(* Section equality: componentwise, arithmetic leaves by lia.      *)
Ltac sec_eq :=
  repeat (first [ solve [reflexivity] | solve [lia] | f_equal ]).

(* Closed-numeral arithmetic: literals >= 7426 are parsed as       *)
(* Nat.of_num_uint atoms, which lia cannot relate to variables;    *)
(* for purely closed <= goals the boolean check decides them.      *)
Ltac closearith :=
  first [ lia | apply Nat.leb_le; reflexivity ].


(* Split from Grind28j.v: CASCADE60 segments r-v and the CASCADE60 *)
(* assembly, for the resident-set reason in Grind28ag.v's header. *)

(* CASCADE60r: steps 654-654 of the CASCADE60 chain. *)
Lemma CASCADE60r : forall w,
  hsteps (HB [1236011; 698173; 177445; 95640; 10129; 1243; 207; 19] 2160727 1 3 (repeat (1, 2) 7965811 ++ (18372851, 2) :: (1, 1) :: repeat (1, 2) 58806192 ++ w) 1)
         (HB [1236011; 698173; 177445; 95640; 10129; 1243; 207; 19] 10126538 1 15931625 ((18372851, 2) :: (1, 1) :: repeat (1, 2) 58806192 ++ w) 1).
Proof.
  intro w.
  rewrite S60rr1.
  rewrite S60rr2.
  (* step 654: M pop12 (7965811,) *)
  apply (pop12 7965811 [1236011; 698173; 177445; 95640; 10129; 1243; 207; 19] 2160727 3 ((18372851, 2) :: (1, 1) :: repeat (1, 2) 58806192 ++ w) 1); exact S60rr3.
Qed.

