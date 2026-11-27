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
               Grind28a Grind28ac Grind28ag Grind28ah Grind28am
               Grind28c Grind28i Grind28.

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


(* Split from Grind28ai.v: CASCADE60 segment s alone, for the *)
(* resident-set reason in Grind28ag.v's header. *)

(* CASCADE60s: steps 655-660 of the CASCADE60 chain. *)

(* Split from Grind28ak.v: CASCADE60 segment s, second half alone, *)
(* for the resident-set reason in Grind28ag.v's header. *)

(* CASCADE60s2: steps 658-660 of the CASCADE60 chain (segment s,
   second half). *)
Lemma CASCADE60s2 : forall w,
  hsteps (HC [10126538; 1236011; 698173; 177445; 95640; 10129; 1243; 207; 19] 15931624 1 2 ((18372847, 2) :: (1, 1) :: repeat (1, 2) 58806192 ++ w) 1)
         (HB [10126538; 1236011; 698173; 177445; 95640; 10129; 1243; 207; 19] 15931624 1 18372850 (repeat (1, 2) 1 ++ (1, 1) :: repeat (1, 2) 58806192 ++ w) 1).
Proof.
  intro w.
  (* step 658: P TDN *)
  apply (hsteps_trans _ (HB [10126538; 1236011; 698173; 177445; 95640; 10129; 1243; 207; 19] 15931624 1 4 ((18372847, 2) :: (1, 1) :: repeat (1, 2) 58806192 ++ w) 1)).
  {
    apply (sTDN [10126538; 1236011; 698173; 177445; 95640; 10129; 1243; 207; 19] 15931624 ((18372847, 2) :: (1, 1) :: repeat (1, 2) 58806192 ++ w) 1).
  }
  (* step 659: sTUP *)
  apply (hsteps_trans _ (HC [10126538; 1236011; 698173; 177445; 95640; 10129; 1243; 207; 19] 15931624 3 2 ((18372845, 2) :: (1, 1) :: repeat (1, 2) 58806192 ++ w) 1)).
  {
    rewrite NUM60X62.
    apply (sTUP [10126538; 1236011; 698173; 177445; 95640; 10129; 1243; 207; 19] 15931624 4 18372847 2 ((1, 1) :: repeat (1, 2) 58806192 ++ w) 1); closearith.
  }
  (* step 660: CLEANG_odd 9186421 *)
  rewrite NUM60X63.
  rewrite NUM60X64.
  replace (repeat (1, 2) 1 ++ (1, 1) :: repeat (1, 2) 58806192 ++ w) with ((1, 2) :: (1, 1) :: repeat (1, 2) 58806192 ++ w) by sec_eq.
  apply (CLEANG_odd 9186421 [10126538; 1236011; 698173; 177445; 95640; 10129; 1243; 207; 19] 15931624 ((1, 1) :: repeat (1, 2) 58806192 ++ w) 1); exact P660.
Qed.

