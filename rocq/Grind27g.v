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
               Grind27b Grind27c Grind27d Grind27e Grind27f Grind27h
               Grind27j Grind27l Grind27m Grind27n.

(* Section equality: componentwise, arithmetic leaves by lia.      *)
Ltac sec_eq :=
  repeat (first [ solve [reflexivity] | solve [lia] | f_equal ]).

(* Closed-numeral arithmetic: literals >= 7426 are parsed as       *)
(* Nat.of_num_uint atoms, which lia cannot relate to variables;    *)
(* for purely closed <= goals the boolean check decides them.      *)
Ltac closearith :=
  first [ lia | apply Nat.leb_le; reflexivity ].

Lemma TOP59_BAND : forall j beta, 4 <= j -> j <= 58806193 -> 2 <= beta ->
  hsteps (HB [7965811; 4012920; 308090; 49409; 7710; 1059; 199; 101; 0] 34304475 1 58806191
            ((2 * j, 2) :: (1, 1) :: repeat (1, 2) (beta - 1)) 1)
         (HB [58806191; 34304475; 7965811; 4012920; 308090; 49409; 7710; 1059; 199; 101; 0]
            (2 * j + beta - 2) 1 (2 * beta + 1) [] 1).
Proof.
  intros j beta Hj1 Hj2 Hb.
  apply (hsteps_trans _ (HC [7965811; 4012920; 308090; 49409; 7710; 1059; 199; 101; 0]
    34304475 58806190 2 ((2 * j - 2, 2) :: (1, 1)
            :: repeat (1, 2) (beta - 1)) 1)).
  { rewrite NUM59h.
    apply (sTUP [7965811; 4012920; 308090; 49409; 7710; 1059; 199; 101; 0] 34304475 58806191
           (2 * j) 2 ((1, 1) :: repeat (1, 2) (beta - 1)) 1);
      [exact S59h0 | lia]. }
  apply (hsteps_trans _ (HB [7965811; 4012920; 308090; 49409; 7710; 1059; 199; 101; 0]
    34304474 1 58806190 ((2, 2) :: (2 * j - 2, 2) :: (1, 1)
            :: repeat (1, 2) (beta - 1)) 1)).
  { rewrite NUM59a. rewrite NUM59b.
    apply (hGRIND_even 29403093 [7965811; 4012920; 308090; 49409; 7710; 1059; 199; 101; 0]
           34304474 ((2 * j - 2, 2) :: (1, 1)
           :: repeat (1, 2) (beta - 1)) 1);
      [exact S59g1 | exact S59g2]. }
  apply (hsteps_trans _ (HC [34304475; 7965811; 4012920; 308090; 49409; 7710; 1059; 199; 101; 0] 58806190 1 2 ((2 * j - 4, 2) :: (1, 1)
            :: repeat (1, 2) (beta - 1)) 1)).
  { rewrite NUM59i. rewrite NUM59b.
    replace ((2 * j - 4, 2) :: (1, 1) :: repeat (1, 2) (beta - 1))
      with ((2 * j - 2 - 2, 2) :: (1, 1)
            :: repeat (1, 2) (beta - 1)) by sec_eq.
    apply (sTUP2_1 [7965811; 4012920; 308090; 49409; 7710; 1059; 199; 101; 0] 34304474
           58806189 (2 * j - 2) ((1, 1) :: repeat (1, 2) (beta - 1))
           1); lia. }
  apply (hsteps_trans _ (HB [34304475; 7965811; 4012920; 308090; 49409; 7710; 1059; 199; 101; 0] 58806190 1 4 ((2 * j - 4, 2) :: (1, 1)
            :: repeat (1, 2) (beta - 1)) 1)).
  { apply (sTDN [34304475; 7965811; 4012920; 308090; 49409; 7710; 1059; 199; 101; 0] 58806190
           ((2 * j - 4, 2) :: (1, 1) :: repeat (1, 2) (beta - 1))
           1). }
  apply (hsteps_trans _ (HC [34304475; 7965811; 4012920; 308090; 49409; 7710; 1059; 199; 101; 0] 58806190 3 2 ((2 * j - 6, 2) :: (1, 1)
            :: repeat (1, 2) (beta - 1)) 1)).
  { replace ((2 * j - 6, 2) :: (1, 1) :: repeat (1, 2) (beta - 1))
      with ((2 * j - 4 - 2, 2) :: (1, 1)
            :: repeat (1, 2) (beta - 1)) by sec_eq.
    apply (sTUP [34304475; 7965811; 4012920; 308090; 49409; 7710; 1059; 199; 101; 0] 58806190
           4 (2 * j - 4) 2 ((1, 1) :: repeat (1, 2) (beta - 1)) 1);
      lia. }
  apply (hsteps_trans _ (HB [34304475; 7965811; 4012920; 308090; 49409; 7710; 1059; 199; 101; 0] 58806190 1 (2 * j - 2)
    ((2, 2) :: (1, 1) :: repeat (1, 2) (beta - 1)) 1)).
  { replace (2 * j - 6) with (2 * (j - 4) + 2) by lia.
    replace (2 * j - 2) with (2 * (j - 4) + 6) by lia.
    apply (CLEANG_even (j - 4) [34304475; 7965811; 4012920; 308090; 49409; 7710; 1059; 199; 101; 0] 58806190 ((1, 1) :: repeat (1, 2) (beta - 1))
           1).
    (* the floor (j - 4) + 1 <= 58806190: route via j <= 58806193 *)
    apply Nat.le_trans with (j - 3).
    - lia.
    - rewrite NUM59k.
      apply Nat.sub_le_mono_r. exact Hj2. }
  apply (hsteps_trans _ (HB [58806191; 34304475; 7965811; 4012920; 308090; 49409; 7710; 1059; 199; 101; 0] (2 * j - 1) 1 3 (repeat (1, 2) (beta - 1)) 1)).
  { replace (2 * j - 2) with (S (2 * j - 3)) by lia.
    replace (2 * j - 1) with (S (S (2 * j - 3))) by lia.
    rewrite NUM59e.
    apply (sTRANS2_1 [34304475; 7965811; 4012920; 308090; 49409; 7710; 1059; 199; 101; 0]
           58806190 (2 * j - 3) 1 (repeat (1, 2) (beta - 1)) 1); lia. }
  replace (2 * j + beta - 2) with (2 * j - 1 + (beta - 1)) by lia.
  apply (CASCADE_POPFIN [58806191; 34304475; 7965811; 4012920; 308090; 49409; 7710; 1059; 199; 101; 0] (2 * j - 1) beta); lia.
Qed.

(* ----------------------------------------------------------------- *)
(* TAIL2_END14: the strictly smaller residual core -- the totality  *)
(* of the TOP13 state for r13' = 2 * j, j >= 58806194                *)
(* (r13' >= 117612388), where the GRIND14 pair (r13' - 6, 2) at      *)
(* counter 58806190 takes the DIPDESC boundary a fourteenth time.    *)
(* A Definition (lemma parameter), never an axiom.                   *)
(* ----------------------------------------------------------------- *)

Definition TAIL2_END14 : Prop :=
  forall j beta, 58806194 <= j -> 2 <= beta ->
  exists pb A, beta <= A /\
    hsteps (HB [7965811; 4012920; 308090; 49409; 7710; 1059; 199; 101; 0] 34304475 1 58806191
              ((2 * j, 2) :: (1, 1) :: repeat (1, 2) (beta - 1)) 1)
           (HB pb A 1 (2 * beta + 1) [] 1).

(* ----------------------------------------------------------------- *)
(* TAIL2_END13_of59: TAIL2_END13, modulo TAIL2_END14.  The j-range  *)
(* splits at r13' = 2 * (j - 29403095): the three small cases and    *)
(* band 13 are proved above; j - 29403095 >= 58806194 is the core.   *)
(* (Numeral hygiene: all S-conversions at these depths are          *)
(* eqb/vm-proved equality rewrites, per the Phase 53-57 pattern.)    *)
(* ----------------------------------------------------------------- *)

Lemma TAIL2_END13_of59 : TAIL2_END14 -> TAIL2_END13.
Proof.
  intros H14 j beta Hj Hb.
  pose proof (TOP59_TO_TOP13 j beta Hj Hb) as Htop.
  destruct (le_lt_dec 58806194 (j - 29403095)) as [Hbig | Hsmall].
  - (* j13 = j - 29403095 >= 58806194: the core *)
    destruct (H14 (j - 29403095) beta Hbig Hb)
      as [pb [A [Ha Hsteps]]].
    exists pb, A. split; [exact Ha |].
    exact (hsteps_trans _ _ _ Htop Hsteps).
  - destruct (le_lt_dec 4 (j - 29403095)) as [Hband | Htiny].
    + (* band 13: j13 = j - 29403095, 4 <= j13 <= 58806193 *)
      exists [58806191; 34304475; 7965811; 4012920; 308090; 49409; 7710; 1059; 199; 101; 0],
        (2 * (j - 29403095) + beta - 2).
      split; [lia |].
      assert (Hj2 : j - 29403095 <= 58806193).
      { rewrite NUM59m in Hsmall.
        apply (proj1 (Nat.lt_succ_r _ _) Hsmall). }
      exact (hsteps_trans _ _ _ Htop
               (TOP59_BAND (j - 29403095) beta Hband Hj2 Hb)).
    + (* tiny: j13 = j - 29403095 <= 3; j13 >= 1 since 29403096 <= j *)
      destruct (Nat.eq_dec (j - 29403095) 1) as [He | Hne].
      * (* r13' = 2 *)
        rewrite He in Htop.
        exists [34304476; 7965811; 4012920; 308090; 49409; 7710; 1059; 199; 101; 0],
          (58806192 + (beta - 1)).
        split; [rewrite NUM59n; lia |].
        exact (hsteps_trans _ _ _ Htop (TOP59_2 beta Hb)).
      * destruct (Nat.eq_dec (j - 29403095) 2) as [He | Hne'].
        -- (* r13' = 4 *)
           rewrite He in Htop.
           exists [58806191; 34304475; 7965811; 4012920; 308090; 49409; 7710; 1059; 199; 101; 0], (beta + 2).
           split; [lia |].
           exact (hsteps_trans _ _ _ Htop (TOP59_4 beta Hb)).
        -- destruct (Nat.eq_dec (j - 29403095) 3) as [He | Hne''].
           ++ (* r13' = 6 *)
              rewrite He in Htop.
              exists [58806191; 34304475; 7965811; 4012920; 308090; 49409; 7710; 1059; 199; 101; 0], (beta + 4).
              split; [lia |].
              exact (hsteps_trans _ _ _ Htop (TOP59_6 beta Hb)).
           ++ (* j13 = 0, contradicting 29403096 <= j *)
              exfalso.
              assert (H0 : j - 29403095 = 0) by lia.
              rewrite NUM58m in Hj.
              lia.
Qed.

(* ----------------------------------------------------------------- *)
(* ESC_ERA_LAW_59: the phase-8 ESC era law at every even            *)
(* R >= 1278 (M >= 616), modulo TAIL2_END14 alone.                  *)
(* ----------------------------------------------------------------- *)

Lemma ESC_ERA_LAW_59 : TAIL2_END14 ->
  forall M beta, 616 <= M -> 2 <= beta ->
  exists n c pb a,
    run n (esc_src (2 * M + 52) (beta - 2)) = Some c
    /\ cfg_sim c (rcsec (false :: repeat true (S a) ++ enc pb)
                        (2 * beta + 2) [(1, 2)])
    /\ beta <= a.
Proof.
  intros H M beta HM Hb.
  apply (ESC_ERA_LAW_58 (TAIL2_END13_of59 H) M beta HM Hb).
Qed.

(* ----------------------------------------------------------------- *)
(* Assumption audit                                                  *)
(* ----------------------------------------------------------------- *)
Print Assumptions TOP59_BAND.
Print Assumptions TAIL2_END13_of59.
Print Assumptions ESC_ERA_LAW_59.
