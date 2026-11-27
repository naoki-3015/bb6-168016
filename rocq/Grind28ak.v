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


(* Split from Grind28ai.v: CASCADE60 segment s alone, for the *)
(* resident-set reason in Grind28ag.v's header. *)

(* CASCADE60s: steps 655-660 of the CASCADE60 chain. *)
(* CASCADE60s1: steps 655-657 of the CASCADE60 chain (segment s,
   first half; the whole segment in one lemma OOMs at Phase 60
   depths -- see Grind28ag.v's header). *)
Lemma CASCADE60s1 : forall w,
  hsteps (HB [1236011; 698173; 177445; 95640; 10129; 1243; 207; 19] 10126538 1 15931625 ((18372851, 2) :: (1, 1) :: repeat (1, 2) 58806192 ++ w) 1)
         (HC [10126538; 1236011; 698173; 177445; 95640; 10129; 1243; 207; 19] 15931624 1 2 ((18372847, 2) :: (1, 1) :: repeat (1, 2) 58806192 ++ w) 1).
Proof.
  intro w.
  (* step 655: sTUP *)
  apply (hsteps_trans _ (HC [1236011; 698173; 177445; 95640; 10129; 1243; 207; 19] 10126538 15931624 2 ((18372849, 2) :: (1, 1) :: repeat (1, 2) 58806192 ++ w) 1)).
  {
    rewrite NUM60X55.
    rewrite NUM60X56.
    apply (sTUP [1236011; 698173; 177445; 95640; 10129; 1243; 207; 19] 10126538 15931625 18372851 2 ((1, 1) :: repeat (1, 2) 58806192 ++ w) 1); closearith.
  }
  (* step 656: hGRIND_even 7965810 *)
  apply (hsteps_trans _ (HB [1236011; 698173; 177445; 95640; 10129; 1243; 207; 19] 10126537 1 15931624 ((2, 2) :: (18372849, 2) :: (1, 1) :: repeat (1, 2) 58806192 ++ w) 1)).
  {
    rewrite NUM60X57.
    rewrite NUM60X58.
    apply (hGRIND_even 7965810 [1236011; 698173; 177445; 95640; 10129; 1243; 207; 19] 10126537 ((18372849, 2) :: (1, 1) :: repeat (1, 2) 58806192 ++ w) 1); closearith.
  }
  (* step 657: P TUP2_1 *)
  apply (hsteps_trans _ (HC [10126538; 1236011; 698173; 177445; 95640; 10129; 1243; 207; 19] 15931624 1 2 ((18372847, 2) :: (1, 1) :: repeat (1, 2) 58806192 ++ w) 1)).
  {
    rewrite NUM60X59.
    rewrite NUM60X60.
    rewrite NUM60X61.
    apply (sTUP2_1 [1236011; 698173; 177445; 95640; 10129; 1243; 207; 19] 10126537 15931623 18372849 ((1, 1) :: repeat (1, 2) 58806192 ++ w) 1); closearith.
  }
  apply hsteps_refl.
Qed.
