(* ================================================================= *)
(* Phase 59 (tail): the TOP13 closings, the residual core          *)
(* TAIL2_END14, TAIL2_END13_of59 and ESC_ERA_LAW_59.  Split from    *)
(* Grind27.v / Grind27b.v for the operational reason recorded in    *)
(* Grind27b.v's header (compile resident set at Phase 59 numeral    *)
(* depths); every lemma statement is the one the phase's single-    *)
(* file draft carried.  The phase narrative lives in Grind27.v's    *)
(* header.                                                          *)
(* ================================================================= *)

Require Import List Bool Arith Lia ZArith.
Import ListNotations.
Require Import TM Sections Mirror TokenPass Recoord Era Esc Dev
               Grind Grind2 Grind3 Grind4 Grind5 Grind6 Grind7 Grind8
               Grind9 Grind10 Grind11 Grind12 Grind13 Grind14 Grind15
               Grind16 Grind17 Grind18 Grind19 Grind20 Grind21 Grind22
               Grind23 Grind24 Grind25 Grind26 Grind26a Grind26b
               Grind26c Grind26d Grind26e Grind26f Grind26g Grind27a
               Grind27b Grind27c Grind27h Grind27k.

(* Section equality: componentwise, arithmetic leaves by lia.      *)
Ltac sec_eq :=
  repeat (first [ solve [reflexivity] | solve [lia] | f_equal ]).

(* Closed-numeral arithmetic: literals >= 7426 are parsed as       *)
(* Nat.of_num_uint atoms, which lia cannot relate to variables;    *)
(* for purely closed <= goals the boolean check decides them.      *)
Ltac closearith :=
  first [ lia | apply Nat.leb_le; reflexivity ].

Lemma TOP59_2 : forall beta, 2 <= beta ->
  hsteps (HB [7965811; 4012920; 308090; 49409; 7710; 1059; 199; 101; 0] 34304475 1 58806191
            ((2, 2) :: (1, 1) :: repeat (1, 2) (beta - 1)) 1)
         (HB [34304476; 7965811; 4012920; 308090; 49409; 7710; 1059; 199; 101; 0]
            (58806192 + (beta - 1)) 1 (2 * beta + 1) [] 1).
Proof.
  intros beta Hb.
  apply (hsteps_trans _ (HB [34304476; 7965811; 4012920; 308090; 49409; 7710; 1059; 199; 101; 0] 58806192 1 3 (repeat (1, 2) (beta - 1)) 1)).
  { rewrite NUM59e. rewrite NUM59f. rewrite NUM59g.
    apply (sTRANS2_1 [7965811; 4012920; 308090; 49409; 7710; 1059; 199; 101; 0] 34304475
           58806190 1 (repeat (1, 2) (beta - 1)) 1); lia. }
  apply (CASCADE_POPFIN [34304476; 7965811; 4012920; 308090; 49409; 7710; 1059; 199; 101; 0] 58806192 beta); lia.
Qed.

Print Assumptions TOP59_2.
