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
               Grind27b Grind27c Grind27d Grind27e Grind27h Grind27j
               Grind27l.

(* Section equality: componentwise, arithmetic leaves by lia.      *)
Ltac sec_eq :=
  repeat (first [ solve [reflexivity] | solve [lia] | f_equal ]).

(* Closed-numeral arithmetic: literals >= 7426 are parsed as       *)
(* Nat.of_num_uint atoms, which lia cannot relate to variables;    *)
(* for purely closed <= goals the boolean check decides them.      *)
Ltac closearith :=
  first [ lia | apply Nat.leb_le; reflexivity ].

Lemma TOP59_6 : forall beta, 2 <= beta ->
  hsteps (HB [7965811; 4012920; 308090; 49409; 7710; 1059; 199; 101; 0] 34304475 1 58806191
            ((6, 2) :: (1, 1) :: repeat (1, 2) (beta - 1)) 1)
         (HB [58806191; 34304475; 7965811; 4012920; 308090; 49409; 7710; 1059; 199; 101; 0]
            (beta + 4) 1 (2 * beta + 1) [] 1).
Proof.
  intros beta Hb.
  apply (hsteps_trans _ (HC [7965811; 4012920; 308090; 49409; 7710; 1059; 199; 101; 0]
    34304475 58806190 2
    ((4, 2) :: (1, 1) :: repeat (1, 2) (beta - 1)) 1)).
  { rewrite NUM59h.
    apply (sTUP [7965811; 4012920; 308090; 49409; 7710; 1059; 199; 101; 0] 34304475 58806191
           6 2 ((1, 1) :: repeat (1, 2) (beta - 1)) 1);
      [exact S59h0 | lia]. }
  apply (hsteps_trans _ (HB [7965811; 4012920; 308090; 49409; 7710; 1059; 199; 101; 0]
    34304474 1 58806190 ((2, 2) :: (4, 2) :: (1, 1)
            :: repeat (1, 2) (beta - 1)) 1)).
  { rewrite NUM59a. rewrite NUM59b.
    apply (hGRIND_even 29403093 [7965811; 4012920; 308090; 49409; 7710; 1059; 199; 101; 0]
           34304474 ((4, 2) :: (1, 1) :: repeat (1, 2) (beta - 1)) 1);
      [exact S59g1 | exact S59g2]. }
  apply (hsteps_trans _ (HC [34304475; 7965811; 4012920; 308090; 49409; 7710; 1059; 199; 101; 0] 58806190 1 2
    ((2, 2) :: (1, 1) :: repeat (1, 2) (beta - 1)) 1)).
  { rewrite NUM59i. rewrite NUM59b.
    replace ((2, 2) :: (1, 1) :: repeat (1, 2) (beta - 1))
      with ((4 - 2, 2) :: (1, 1) :: repeat (1, 2) (beta - 1))
      by sec_eq.
    apply (sTUP2_1 [7965811; 4012920; 308090; 49409; 7710; 1059; 199; 101; 0] 34304474
           58806189 4 ((1, 1) :: repeat (1, 2) (beta - 1)) 1); lia. }
  apply (hsteps_trans _ (HB [34304475; 7965811; 4012920; 308090; 49409; 7710; 1059; 199; 101; 0] 58806190 1 4
    ((2, 2) :: (1, 1) :: repeat (1, 2) (beta - 1)) 1)).
  { apply (sTDN [34304475; 7965811; 4012920; 308090; 49409; 7710; 1059; 199; 101; 0] 58806190
           ((2, 2) :: (1, 1) :: repeat (1, 2) (beta - 1))
           1). }
  apply (hsteps_trans _ (HB [58806191; 34304475; 7965811; 4012920; 308090; 49409; 7710; 1059; 199; 101; 0] 5 1 3 (repeat (1, 2) (beta - 1)) 1)).
  { rewrite NUM59e.
    apply (sTRANS2_1 [34304475; 7965811; 4012920; 308090; 49409; 7710; 1059; 199; 101; 0]
           58806190 3 1 (repeat (1, 2) (beta - 1)) 1); lia. }
  replace (beta + 4) with (5 + (beta - 1)) by lia.
  apply (CASCADE_POPFIN [58806191; 34304475; 7965811; 4012920; 308090; 49409; 7710; 1059; 199; 101; 0] 5 beta); lia.
Qed.

Print Assumptions TOP59_6.
