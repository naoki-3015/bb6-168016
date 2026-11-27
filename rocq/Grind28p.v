(* ================================================================= *)
(* Phase 60 (tail): the TOP14 closings, the residual core          *)
(* TAIL2_END15, TAIL2_END14_of60 and ESC_ERA_LAW_60.  Split from   *)
(* Grind28.v / Grind28j.v for the operational reason recorded in   *)
(* Grind28.v's header (compile resident set at Phase 60 numeral    *)
(* depths); every lemma statement is the one the phase's single-   *)
(* file draft carried.  The phase narrative lives in Grind28.v's   *)
(* header.                                                         *)
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
               Grind28a Grind28ab Grind28ae Grind28af Grind28b
               Grind28d Grind28f
               Grind28g Grind28h Grind28l Grind28m Grind28n
               Grind28o Grind28q Grind28r Grind28s Grind28u
               Grind28w Grind28y Grind28z.
(* Section equality: componentwise, arithmetic leaves by lia.      *)
Ltac sec_eq :=
  repeat (first [ solve [reflexivity] | solve [lia] | f_equal ]).

(* Closed-numeral arithmetic: literals >= 7426 are parsed as       *)
(* Nat.of_num_uint atoms, which lia cannot relate to variables;    *)
(* for purely closed <= goals the boolean check decides them.      *)
Ltac closearith :=
  first [ lia | apply Nat.leb_le; reflexivity ].

Lemma TOP60_BAND : forall j beta, 4 <= j -> j <= 135985239 -> 2 <= beta ->
  hsteps (HB [10126538; 1236011; 698173; 177445; 95640; 10129; 1243; 207; 19] 74737818 1 135985237
            ((2 * j, 2) :: (1, 1) :: repeat (1, 2) (beta - 1)) 1)
         (HB [135985237; 74737818; 10126538; 1236011; 698173; 177445; 95640; 10129; 1243; 207; 19]
            (2 * j + beta - 2) 1 (2 * beta + 1) [] 1).
Proof.
  intros j beta Hj1 Hj2 Hb.
  apply (hsteps_trans _ (HC [10126538; 1236011; 698173; 177445; 95640; 10129; 1243; 207; 19]
    74737818 135985236 2 ((2 * j - 2, 2) :: (1, 1)
            :: repeat (1, 2) (beta - 1)) 1)).
  { rewrite NUM60h.
    apply (sTUP [10126538; 1236011; 698173; 177445; 95640; 10129; 1243; 207; 19] 74737818 135985237
           (2 * j) 2 ((1, 1) :: repeat (1, 2) (beta - 1)) 1);
      [exact S60h0 | lia]. }
  apply (hsteps_trans _ (HB [10126538; 1236011; 698173; 177445; 95640; 10129; 1243; 207; 19]
    74737817 1 135985236 ((2, 2) :: (2 * j - 2, 2) :: (1, 1)
            :: repeat (1, 2) (beta - 1)) 1)).
  { rewrite NUM60a. rewrite NUM60b.
    apply (hGRIND_even 67992616 [10126538; 1236011; 698173; 177445; 95640; 10129; 1243; 207; 19]
           74737817 ((2 * j - 2, 2) :: (1, 1)
           :: repeat (1, 2) (beta - 1)) 1);
      [exact S60g1 | exact S60g2]. }
  apply (hsteps_trans _ (HC [74737818; 10126538; 1236011; 698173; 177445; 95640; 10129; 1243; 207; 19] 135985236 1 2 ((2 * j - 4, 2) :: (1, 1)
            :: repeat (1, 2) (beta - 1)) 1)).
  { rewrite NUM60i'. rewrite NUM60b.
    assert (E : ((2 * j - 2 - 2, 2) :: (1, 1)
              :: repeat (1, 2) (beta - 1))
              = ((2 * j - 4, 2) :: (1, 1) :: repeat (1, 2) (beta - 1)))
      by sec_eq.
    rewrite <- E.
    apply (sTUP2_1 [10126538; 1236011; 698173; 177445; 95640; 10129; 1243; 207; 19] 74737817
           (135985236 - 1) (2 * j - 2) ((1, 1) :: repeat (1, 2) (beta - 1))
           1); lia. }
  apply (hsteps_trans _ (HB [74737818; 10126538; 1236011; 698173; 177445; 95640; 10129; 1243; 207; 19] 135985236 1 4 ((2 * j - 4, 2) :: (1, 1)
            :: repeat (1, 2) (beta - 1)) 1)).
  { apply (sTDN [74737818; 10126538; 1236011; 698173; 177445; 95640; 10129; 1243; 207; 19] 135985236
           ((2 * j - 4, 2) :: (1, 1) :: repeat (1, 2) (beta - 1))
           1). }
  apply (hsteps_trans _ (HC [74737818; 10126538; 1236011; 698173; 177445; 95640; 10129; 1243; 207; 19] 135985236 3 2 ((2 * j - 6, 2) :: (1, 1)
            :: repeat (1, 2) (beta - 1)) 1)).
  { assert (E : ((2 * j - 4 - 2, 2) :: (1, 1)
              :: repeat (1, 2) (beta - 1))
              = ((2 * j - 6, 2) :: (1, 1) :: repeat (1, 2) (beta - 1)))
      by sec_eq.
    rewrite <- E.
    apply (sTUP [74737818; 10126538; 1236011; 698173; 177445; 95640; 10129; 1243; 207; 19] 135985236
           4 (2 * j - 4) 2 ((1, 1) :: repeat (1, 2) (beta - 1)) 1);
      lia. }
  apply (hsteps_trans _ (HB [74737818; 10126538; 1236011; 698173; 177445; 95640; 10129; 1243; 207; 19] 135985236 1 (2 * j - 2)
    ((2, 2) :: (1, 1) :: repeat (1, 2) (beta - 1)) 1)).
  { replace (2 * j - 6) with (2 * (j - 4) + 2) by lia.
    replace (2 * j - 2) with (2 * (j - 4) + 6) by lia.
    apply (CLEANG_even (j - 4) [74737818; 10126538; 1236011; 698173; 177445; 95640; 10129; 1243; 207; 19] 135985236 ((1, 1) :: repeat (1, 2) (beta - 1))
           1).
    (* the floor (j - 4) + 1 <= 135985236: route via j <= 135985239 *)
    apply Nat.le_trans with (j - 3).
    - lia.
    - rewrite NUM60k.
      apply Nat.sub_le_mono_r. exact Hj2. }
  apply (hsteps_trans _ (HB [135985237; 74737818; 10126538; 1236011; 698173; 177445; 95640; 10129; 1243; 207; 19] (2 * j - 1) 1 3 (repeat (1, 2) (beta - 1)) 1)).
  { replace (2 * j - 2) with (S (2 * j - 3)) by lia.
    replace (2 * j - 1) with (S (S (2 * j - 3))) by lia.
    rewrite NUM60e'.
    apply (sTRANS2_1 [74737818; 10126538; 1236011; 698173; 177445; 95640; 10129; 1243; 207; 19]
           (135985237 - 1) (2 * j - 3) 1 (repeat (1, 2) (beta - 1)) 1); lia. }
  replace (2 * j + beta - 2) with (2 * j - 1 + (beta - 1)) by lia.
  apply (CASCADE_POPFIN [135985237; 74737818; 10126538; 1236011; 698173; 177445; 95640; 10129; 1243; 207; 19] (2 * j - 1) beta); lia.
Qed.

(* ----------------------------------------------------------------- *)
(* TAIL2_END15: the strictly smaller residual core -- the totality  *)
(* of the TOP14 state for r14' = 2 * j, j >= 135985240              *)
(* (r14' >= 271970480), where the GRIND15 pair (r14' - 6, 2) at     *)
(* counter 135985236 takes the DIPDESC boundary a fifteenth time.   *)
(* A Definition (lemma parameter), never an axiom.                  *)
(* ----------------------------------------------------------------- *)

Definition TAIL2_END15 : Prop :=
  forall j beta, 135985240 <= j -> 2 <= beta ->
  exists pb A, beta <= A /\
    hsteps (HB [10126538; 1236011; 698173; 177445; 95640; 10129; 1243; 207; 19] 74737818 1 135985237
              ((2 * j, 2) :: (1, 1) :: repeat (1, 2) (beta - 1)) 1)
           (HB pb A 1 (2 * beta + 1) [] 1).

(* ----------------------------------------------------------------- *)
(* TAIL2_END14_of60: TAIL2_END14, modulo TAIL2_END15.  The j-range *)
(* splits at r14' = 2 * (j - 58806193): the three small cases and   *)
(* band 14 are proved above; j - 58806193 >= 135985240 is the core. *)
(* (Numeral hygiene: all S-conversions at these depths are          *)
(* eqb/vm-proved equality rewrites, per the Phase 53-57 pattern.)   *)
(* ----------------------------------------------------------------- *)

Lemma TAIL2_END14_of60 : TAIL2_END15 -> TAIL2_END14.
Proof.
  intros H15 j beta Hj Hb.
  pose proof (TOP60_TO_TOP14 j beta Hj Hb) as Htop.
  destruct (le_lt_dec 135985240 (j - 58806193)) as [Hbig | Hsmall].
  - (* j14 = j - 58806193 >= 135985240: the core *)
    destruct (H15 (j - 58806193) beta Hbig Hb)
      as [pb [A [Ha Hsteps]]].
    exists pb, A. split; [exact Ha |].
    exact (hsteps_trans _ _ _ Htop Hsteps).
  - destruct (le_lt_dec 4 (j - 58806193)) as [Hband | Htiny].
    + (* band 14: j14 = j - 58806193, 4 <= j14 <= 135985239 *)
      exists [135985237; 74737818; 10126538; 1236011; 698173; 177445; 95640; 10129; 1243; 207; 19],
        (2 * (j - 58806193) + beta - 2).
      split; [lia |].
      assert (Hj2 : j - 58806193 <= 135985239).
      { rewrite NUM60m in Hsmall.
        apply (proj1 (Nat.lt_succ_r _ _) Hsmall). }
      exact (hsteps_trans _ _ _ Htop
               (TOP60_BAND (j - 58806193) beta Hband Hj2 Hb)).
    + (* tiny: j14 = j - 58806193 <= 3; j14 >= 1 since 58806194 <= j *)
      destruct (Nat.eq_dec (j - 58806193) 1) as [He | Hne].
      * (* r14' = 2 *)
        rewrite He in Htop.
        exists [74737819; 10126538; 1236011; 698173; 177445; 95640; 10129; 1243; 207; 19],
          (135985238 + (beta - 1)).
        split; [rewrite NUM60n; lia |].
        exact (hsteps_trans _ _ _ Htop (TOP60_2 beta Hb)).
      * destruct (Nat.eq_dec (j - 58806193) 2) as [He | Hne'].
        -- (* r14' = 4 *)
           rewrite He in Htop.
           exists [135985237; 74737818; 10126538; 1236011; 698173; 177445; 95640; 10129; 1243; 207; 19], (beta + 2).
           split; [lia |].
           exact (hsteps_trans _ _ _ Htop (TOP60_4 beta Hb)).
        -- destruct (Nat.eq_dec (j - 58806193) 3) as [He | Hne''].
           ++ (* r14' = 6 *)
              rewrite He in Htop.
              exists [135985237; 74737818; 10126538; 1236011; 698173; 177445; 95640; 10129; 1243; 207; 19], (beta + 4).
              split; [lia |].
              exact (hsteps_trans _ _ _ Htop (TOP60_6 beta Hb)).
           ++ (* j14 = 0, contradicting 58806194 <= j *)
              exfalso.
              assert (H0 : j - 58806193 = 0) by lia.
              rewrite S60f4 in Hj.
              lia.
Qed.

(* ----------------------------------------------------------------- *)
(* ESC_ERA_LAW_60: the phase-8 ESC era law at every even            *)
(* R >= 1278 (M >= 616), modulo TAIL2_END15 alone.                  *)
(* ----------------------------------------------------------------- *)

Lemma ESC_ERA_LAW_60 : TAIL2_END15 ->
  forall M beta, 616 <= M -> 2 <= beta ->
  exists n c pb a,
    run n (esc_src (2 * M + 52) (beta - 2)) = Some c
    /\ cfg_sim c (rcsec (false :: repeat true (S a) ++ enc pb)
                        (2 * beta + 2) [(1, 2)])
    /\ beta <= a.
Proof.
  intros H M beta HM Hb.
  apply (ESC_ERA_LAW_59 (TAIL2_END14_of60 H) M beta HM Hb).
Qed.

(* ----------------------------------------------------------------- *)
(* Assumption audit                                                  *)
(* ----------------------------------------------------------------- *)
Print Assumptions TOP60_BAND.
Print Assumptions TAIL2_END14_of60.
Print Assumptions ESC_ERA_LAW_60.
