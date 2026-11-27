(* ================================================================= *)
(* Phase 58 (tail): the TOP12 closings, the residual core          *)
(* TAIL2_END13, TAIL2_END12_of58 and ESC_ERA_LAW_58.  Split from    *)
(* Grind26.v / Grind26b.v for the operational reason recorded in    *)
(* Grind26b.v's header (compile resident set at Phase 58 numeral    *)
(* depths); every lemma statement is the one the phase's single-    *)
(* file draft carried.  The phase narrative lives in Grind26.v's    *)
(* header.                                                          *)
(* ================================================================= *)

Require Import List Bool Arith Lia ZArith.
Import ListNotations.
Require Import TM Sections Mirror TokenPass Recoord Era Esc Dev
               Grind Grind2 Grind3 Grind4 Grind5 Grind6 Grind7 Grind8
               Grind9 Grind10 Grind11 Grind12 Grind13 Grind14 Grind15
               Grind16 Grind17 Grind18 Grind19 Grind20 Grind21 Grind22
               Grind23 Grind24 Grind25 Grind26 Grind26a Grind26b Grind26c Grind26d Grind26e Grind26f.

(* Section equality: componentwise, arithmetic leaves by lia.      *)
Ltac sec_eq :=
  repeat (first [ solve [reflexivity] | solve [lia] | f_equal ]).

(* Closed-numeral arithmetic: literals >= 7426 are parsed as       *)
(* Nat.of_num_uint atoms, which lia cannot relate to variables;    *)
(* for purely closed <= goals the boolean check decides them.      *)
Ltac closearith :=
  first [ lia | apply Nat.leb_le; reflexivity ].

Lemma TOP58_BAND : forall j beta, 4 <= j -> j <= 29403095 -> 2 <= beta ->
  hsteps (HB [1523948; 426279; 308525; 58213; 30332; 931; 608; 77; 35; 20; 0] 14897638 1 29403093
            ((2 * j, 2) :: (1, 1) :: repeat (1, 2) (beta - 1)) 1)
         (HB [29403093; 14897638; 1523948; 426279; 308525; 58213; 30332; 931; 608; 77; 35; 20; 0]
            (2 * j + beta - 2) 1 (2 * beta + 1) [] 1).
Proof.
  intros j beta Hj1 Hj2 Hb.
  apply (hsteps_trans _ (HC [1523948; 426279; 308525; 58213; 30332; 931; 608; 77; 35; 20; 0]
    14897638 29403092 2 ((2 * j - 2, 2) :: (1, 1)
            :: repeat (1, 2) (beta - 1)) 1)).
  { rewrite NUM58h.
    apply (sTUP [1523948; 426279; 308525; 58213; 30332; 931; 608; 77; 35; 20; 0] 14897638 29403093
           (2 * j) 2 ((1, 1) :: repeat (1, 2) (beta - 1)) 1);
      closearith. }
  apply (hsteps_trans _ (HB [1523948; 426279; 308525; 58213; 30332; 931; 608; 77; 35; 20; 0]
    14897637 1 29403092 ((2, 2) :: (2 * j - 2, 2) :: (1, 1)
            :: repeat (1, 2) (beta - 1)) 1)).
  { rewrite NUM58a. rewrite NUM58b.
    apply (hGRIND_even 14701544 [1523948; 426279; 308525; 58213; 30332; 931; 608; 77; 35; 20; 0]
           14897637 ((2 * j - 2, 2) :: (1, 1)
           :: repeat (1, 2) (beta - 1)) 1);
      [exact S58g1 | exact S58g2]. }
  apply (hsteps_trans _ (HC [14897638; 1523948; 426279; 308525; 58213; 30332; 931; 608; 77; 35; 20; 0] 29403092 1 2 ((2 * j - 4, 2) :: (1, 1)
            :: repeat (1, 2) (beta - 1)) 1)).
  { rewrite NUM58i. rewrite NUM58b.
    replace ((2 * j - 4, 2) :: (1, 1) :: repeat (1, 2) (beta - 1))
      with ((2 * j - 2 - 2, 2) :: (1, 1)
            :: repeat (1, 2) (beta - 1)) by sec_eq.
    apply (sTUP2_1 [1523948; 426279; 308525; 58213; 30332; 931; 608; 77; 35; 20; 0] 14897637
           29403091 (2 * j - 2) ((1, 1) :: repeat (1, 2) (beta - 1))
           1); lia. }
  apply (hsteps_trans _ (HB [14897638; 1523948; 426279; 308525; 58213; 30332; 931; 608; 77; 35; 20; 0] 29403092 1 4 ((2 * j - 4, 2) :: (1, 1)
            :: repeat (1, 2) (beta - 1)) 1)).
  { apply (sTDN [14897638; 1523948; 426279; 308525; 58213; 30332; 931; 608; 77; 35; 20; 0] 29403092
           ((2 * j - 4, 2) :: (1, 1) :: repeat (1, 2) (beta - 1))
           1). }
  apply (hsteps_trans _ (HC [14897638; 1523948; 426279; 308525; 58213; 30332; 931; 608; 77; 35; 20; 0] 29403092 3 2 ((2 * j - 6, 2) :: (1, 1)
            :: repeat (1, 2) (beta - 1)) 1)).
  { replace ((2 * j - 6, 2) :: (1, 1) :: repeat (1, 2) (beta - 1))
      with ((2 * j - 4 - 2, 2) :: (1, 1)
            :: repeat (1, 2) (beta - 1)) by sec_eq.
    apply (sTUP [14897638; 1523948; 426279; 308525; 58213; 30332; 931; 608; 77; 35; 20; 0] 29403092
           4 (2 * j - 4) 2 ((1, 1) :: repeat (1, 2) (beta - 1)) 1);
      lia. }
  apply (hsteps_trans _ (HB [14897638; 1523948; 426279; 308525; 58213; 30332; 931; 608; 77; 35; 20; 0] 29403092 1 (2 * j - 2)
    ((2, 2) :: (1, 1) :: repeat (1, 2) (beta - 1)) 1)).
  { replace (2 * j - 6) with (2 * (j - 4) + 2) by lia.
    replace (2 * j - 2) with (2 * (j - 4) + 6) by lia.
    apply (CLEANG_even (j - 4) [14897638; 1523948; 426279; 308525; 58213; 30332; 931; 608; 77; 35; 20; 0] 29403092 ((1, 1) :: repeat (1, 2) (beta - 1))
           1).
    (* the floor (j - 4) + 1 <= 29403092: route via j <= 29403095 *)
    apply Nat.le_trans with (j - 3).
    - lia.
    - rewrite NUM58k.
      apply Nat.sub_le_mono_r. exact Hj2. }
  apply (hsteps_trans _ (HB [29403093; 14897638; 1523948; 426279; 308525; 58213; 30332; 931; 608; 77; 35; 20; 0] (2 * j - 1) 1 3 (repeat (1, 2) (beta - 1)) 1)).
  { replace (2 * j - 2) with (S (2 * j - 3)) by lia.
    replace (2 * j - 1) with (S (S (2 * j - 3))) by lia.
    rewrite NUM58e.
    apply (sTRANS2_1 [14897638; 1523948; 426279; 308525; 58213; 30332; 931; 608; 77; 35; 20; 0]
           29403092 (2 * j - 3) 1 (repeat (1, 2) (beta - 1)) 1); lia. }
  replace (2 * j + beta - 2) with (2 * j - 1 + (beta - 1)) by lia.
  apply (CASCADE_POPFIN [29403093; 14897638; 1523948; 426279; 308525; 58213; 30332; 931; 608; 77; 35; 20; 0] (2 * j - 1) beta); lia.
Qed.

(* ----------------------------------------------------------------- *)
(* TAIL2_END13: the strictly smaller residual core -- the totality  *)
(* of the TOP12 state for r12' = 2 * j, j >= 29403096                *)
(* (r12' >= 58806192), where the GRIND13 pair (r12' - 6, 2) at       *)
(* counter 29403092 takes the DIPDESC boundary a thirteenth time.    *)
(* A Definition (lemma parameter), never an axiom.                   *)
(* ----------------------------------------------------------------- *)

Definition TAIL2_END13 : Prop :=
  forall j beta, 29403096 <= j -> 2 <= beta ->
  exists pb A, beta <= A /\
    hsteps (HB [1523948; 426279; 308525; 58213; 30332; 931; 608; 77; 35; 20; 0] 14897638 1 29403093
              ((2 * j, 2) :: (1, 1) :: repeat (1, 2) (beta - 1)) 1)
           (HB pb A 1 (2 * beta + 1) [] 1).

(* ----------------------------------------------------------------- *)
(* TAIL2_END12_of58: TAIL2_END12, modulo TAIL2_END13.  The j-range  *)
(* splits at r12' = 2 * (j - 11874957): the three small cases and    *)
(* band 12 are proved above; j - 11874957 >= 29403096 is the core.   *)
(* (Numeral hygiene: all S-conversions at these depths are          *)
(* eqb/vm-proved equality rewrites, per the Phase 53-57 pattern.)    *)
(* ----------------------------------------------------------------- *)

Lemma TAIL2_END12_of58 : TAIL2_END13 -> TAIL2_END12.
Proof.
  intros H13 j beta Hj Hb.
  pose proof (TOP58_TO_TOP12 j beta Hj Hb) as Htop.
  destruct (le_lt_dec 29403096 (j - 11874957)) as [Hbig | Hsmall].
  - (* j12 = j - 11874957 >= 29403096: the core *)
    destruct (H13 (j - 11874957) beta Hbig Hb)
      as [pb [A [Ha Hsteps]]].
    exists pb, A. split; [exact Ha |].
    exact (hsteps_trans _ _ _ Htop Hsteps).
  - destruct (le_lt_dec 4 (j - 11874957)) as [Hband | Htiny].
    + (* band 12: j12 = j - 11874957, 4 <= j12 <= 29403095 *)
      exists [29403093; 14897638; 1523948; 426279; 308525; 58213; 30332; 931; 608; 77; 35; 20; 0],
        (2 * (j - 11874957) + beta - 2).
      split; [lia |].
      assert (Hj2 : j - 11874957 <= 29403095).
      { rewrite NUM58m in Hsmall.
        apply (proj1 (Nat.lt_succ_r _ _) Hsmall). }
      exact (hsteps_trans _ _ _ Htop
               (TOP58_BAND (j - 11874957) beta Hband Hj2 Hb)).
    + (* tiny: j12 = j - 11874957 <= 3; j12 >= 1 since 11874958 <= j *)
      destruct (Nat.eq_dec (j - 11874957) 1) as [He | Hne].
      * (* r12' = 2 *)
        rewrite He in Htop.
        exists [14897639; 1523948; 426279; 308525; 58213; 30332; 931; 608; 77; 35; 20; 0],
          (29403094 + (beta - 1)).
        split; [rewrite NUM58n; lia |].
        exact (hsteps_trans _ _ _ Htop (TOP58_2 beta Hb)).
      * destruct (Nat.eq_dec (j - 11874957) 2) as [He | Hne'].
        -- (* r12' = 4 *)
           rewrite He in Htop.
           exists [29403093; 14897638; 1523948; 426279; 308525; 58213; 30332; 931; 608; 77; 35; 20; 0], (beta + 2).
           split; [lia |].
           exact (hsteps_trans _ _ _ Htop (TOP58_4 beta Hb)).
        -- destruct (Nat.eq_dec (j - 11874957) 3) as [He | Hne''].
           ++ (* r12' = 6 *)
              rewrite He in Htop.
              exists [29403093; 14897638; 1523948; 426279; 308525; 58213; 30332; 931; 608; 77; 35; 20; 0], (beta + 4).
              split; [lia |].
              exact (hsteps_trans _ _ _ Htop (TOP58_6 beta Hb)).
           ++ (* j12 = 0, contradicting 11874958 <= j *)
              exfalso.
              assert (H0 : j - 11874957 = 0) by lia.
              rewrite NUM58p in Hj.
              lia.
Qed.

(* ----------------------------------------------------------------- *)
(* ESC_ERA_LAW_58: the phase-8 ESC era law at every even            *)
(* R >= 1278 (M >= 616), modulo TAIL2_END13 alone.                  *)
(* ----------------------------------------------------------------- *)

Lemma ESC_ERA_LAW_58 : TAIL2_END13 ->
  forall M beta, 616 <= M -> 2 <= beta ->
  exists n c pb a,
    run n (esc_src (2 * M + 52) (beta - 2)) = Some c
    /\ cfg_sim c (rcsec (false :: repeat true (S a) ++ enc pb)
                        (2 * beta + 2) [(1, 2)])
    /\ beta <= a.
Proof.
  intros H M beta HM Hb.
  apply (ESC_ERA_LAW_57 (TAIL2_END12_of58 H) M beta HM Hb).
Qed.

(* ----------------------------------------------------------------- *)
(* Assumption audit                                                  *)
(* ----------------------------------------------------------------- *)
Print Assumptions TOP58_BAND.
Print Assumptions TAIL2_END12_of58.
Print Assumptions ESC_ERA_LAW_58.
