(* ================================================================= *)
(* Phase 61 (tail): the TOP15 closings, the residual core          *)
(* TAIL2_END16, TAIL2_END15_of61 and ESC_ERA_LAW_61.  Split from   *)
(* Grind29.v / Grind29j.v for the operational reason recorded in   *)
(* Grind29.v's header (compile resident set at Phase 61 numeral    *)
(* depths); every lemma statement is the one the phase's single-   *)
(* file draft carried.  The phase narrative lives in Grind29.v's   *)
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
               Grind28p Grind28y Grind29a Grind29ab Grind29h Grind29l
               Grind29m Grind29n Grind29o.
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

Lemma TOP61_BAND : forall j beta, 4 <= j -> j <= (271970479 + 2) -> 2 <= beta ->
  hsteps (HB [47892099; 24915618; 1835911; 568849; 317482; 29175; 9907; 6375; 799; 475; 93; 58; 5] 147491795 1 271970479
            ((2 * j, 2) :: (1, 1) :: repeat (1, 2) (beta - 1)) 1)
         (HB [271970479; 147491795; 47892099; 24915618; 1835911; 568849; 317482; 29175; 9907; 6375; 799; 475; 93; 58; 5]
            (2 * j + beta - 2) 1 (2 * beta + 1) [] 1).
Proof.
  intros j beta Hj1 Hj2 Hb.
  apply (hsteps_trans _ (HC [47892099; 24915618; 1835911; 568849; 317482; 29175; 9907; 6375; 799; 475; 93; 58; 5]
    147491795 271970478 2 ((2 * j - 2, 2) :: (1, 1)
            :: repeat (1, 2) (beta - 1)) 1)).
  { rewrite NUM61h.
    apply (sTUP [47892099; 24915618; 1835911; 568849; 317482; 29175; 9907; 6375; 799; 475; 93; 58; 5] 147491795 271970479
           (2 * j) 2 ((1, 1) :: repeat (1, 2) (beta - 1)) 1);
      [exact S61h0 | lia]. }
  apply (hsteps_trans _ (HB [47892099; 24915618; 1835911; 568849; 317482; 29175; 9907; 6375; 799; 475; 93; 58; 5]
    147491794 1 271970478 ((2, 2) :: (2 * j - 2, 2) :: (1, 1)
            :: repeat (1, 2) (beta - 1)) 1)).
  { rewrite NUM61a. rewrite NUM61b.
    apply (hGRIND_even 135985237 [47892099; 24915618; 1835911; 568849; 317482; 29175; 9907; 6375; 799; 475; 93; 58; 5]
           147491794 ((2 * j - 2, 2) :: (1, 1)
           :: repeat (1, 2) (beta - 1)) 1);
      [exact S61g1 | exact S61g2]. }
  apply (hsteps_trans _ (HC [147491795; 47892099; 24915618; 1835911; 568849; 317482; 29175; 9907; 6375; 799; 475; 93; 58; 5] 271970478 1 2 ((2 * j - 4, 2) :: (1, 1)
            :: repeat (1, 2) (beta - 1)) 1)).
  { rewrite NUM61i'. rewrite NUM61b.
    assert (E : ((2 * j - 2 - 2, 2) :: (1, 1)
              :: repeat (1, 2) (beta - 1))
              = ((2 * j - 4, 2) :: (1, 1) :: repeat (1, 2) (beta - 1)))
      by sec_eq.
    rewrite <- E.
    apply (sTUP2_1 [47892099; 24915618; 1835911; 568849; 317482; 29175; 9907; 6375; 799; 475; 93; 58; 5] 147491794
           (271970479 - 1 - 1) (2 * j - 2) ((1, 1) :: repeat (1, 2) (beta - 1))
           1); lia. }
  apply (hsteps_trans _ (HB [147491795; 47892099; 24915618; 1835911; 568849; 317482; 29175; 9907; 6375; 799; 475; 93; 58; 5] 271970478 1 4 ((2 * j - 4, 2) :: (1, 1)
            :: repeat (1, 2) (beta - 1)) 1)).
  { apply (sTDN [147491795; 47892099; 24915618; 1835911; 568849; 317482; 29175; 9907; 6375; 799; 475; 93; 58; 5] 271970478
           ((2 * j - 4, 2) :: (1, 1) :: repeat (1, 2) (beta - 1))
           1). }
  apply (hsteps_trans _ (HC [147491795; 47892099; 24915618; 1835911; 568849; 317482; 29175; 9907; 6375; 799; 475; 93; 58; 5] 271970478 3 2 ((2 * j - 6, 2) :: (1, 1)
            :: repeat (1, 2) (beta - 1)) 1)).
  { assert (E : ((2 * j - 4 - 2, 2) :: (1, 1)
              :: repeat (1, 2) (beta - 1))
              = ((2 * j - 6, 2) :: (1, 1) :: repeat (1, 2) (beta - 1)))
      by sec_eq.
    rewrite <- E.
    apply (sTUP [147491795; 47892099; 24915618; 1835911; 568849; 317482; 29175; 9907; 6375; 799; 475; 93; 58; 5] 271970478
           4 (2 * j - 4) 2 ((1, 1) :: repeat (1, 2) (beta - 1)) 1);
      lia. }
  apply (hsteps_trans _ (HB [147491795; 47892099; 24915618; 1835911; 568849; 317482; 29175; 9907; 6375; 799; 475; 93; 58; 5] 271970478 1 (2 * j - 2)
    ((2, 2) :: (1, 1) :: repeat (1, 2) (beta - 1)) 1)).
  { replace (2 * j - 6) with (2 * (j - 4) + 2) by lia.
    replace (2 * j - 2) with (2 * (j - 4) + 6) by lia.
    apply (CLEANG_even (j - 4) [147491795; 47892099; 24915618; 1835911; 568849; 317482; 29175; 9907; 6375; 799; 475; 93; 58; 5] 271970478 ((1, 1) :: repeat (1, 2) (beta - 1))
           1).
    (* the floor (j - 4) + 1 <= 271970478: route via j <= (271970479 + 2) *)
    apply Nat.le_trans with (j - 3).
    - lia.
    - rewrite NUM61k.
      apply Nat.sub_le_mono_r. exact Hj2. }
  apply (hsteps_trans _ (HB [271970479; 147491795; 47892099; 24915618; 1835911; 568849; 317482; 29175; 9907; 6375; 799; 475; 93; 58; 5] (2 * j - 1) 1 3 (repeat (1, 2) (beta - 1)) 1)).
  { replace (2 * j - 2) with (S (2 * j - 3)) by lia.
    replace (2 * j - 1) with (S (S (2 * j - 3))) by lia.
    rewrite NUM61e'.
    apply (sTRANS2_1 [147491795; 47892099; 24915618; 1835911; 568849; 317482; 29175; 9907; 6375; 799; 475; 93; 58; 5]
           (271970479 - 1) (2 * j - 3) 1 (repeat (1, 2) (beta - 1)) 1); lia. }
  replace (2 * j + beta - 2) with (2 * j - 1 + (beta - 1)) by lia.
  apply (CASCADE_POPFIN [271970479; 147491795; 47892099; 24915618; 1835911; 568849; 317482; 29175; 9907; 6375; 799; 475; 93; 58; 5] (2 * j - 1) beta); lia.
Qed.

(* ----------------------------------------------------------------- *)
(* TAIL2_END16: the strictly smaller residual core -- the totality  *)
(* of the TOP15 state for r15' = 2 * j, j >= 271970482               *)
(* (r15' >= 543940964), where the GRIND16 pair (r15' - 6, 2) at        *)
(* counter 271970478 takes the DIPDESC boundary a sixteenth time.    *)
(* A Definition (lemma parameter), never an axiom.                  *)
(* ----------------------------------------------------------------- *)

Definition TAIL2_END16 : Prop :=
  forall j beta, 271970482 <= j -> 2 <= beta ->
  exists pb A, beta <= A /\
    hsteps (HB [47892099; 24915618; 1835911; 568849; 317482; 29175; 9907; 6375; 799; 475; 93; 58; 5] 147491795 1 271970479
              ((2 * j, 2) :: (1, 1) :: repeat (1, 2) (beta - 1)) 1)
           (HB pb A 1 (2 * beta + 1) [] 1).

(* ----------------------------------------------------------------- *)
(* TAIL2_END15_of61: TAIL2_END15, modulo TAIL2_END16.  The j-range *)
(* splits at r15' = 2 * (j - 135985239): the three small cases     *)
(* and band 15 are proved above; j - 135985239 >= 271970482 is the  *)
(* core.                                                            *)
(* ----------------------------------------------------------------- *)

Lemma TAIL2_END15_of61 : TAIL2_END16 -> TAIL2_END15.
Proof.
  intros H16 j beta Hj Hb.
  pose proof (TOP61_TO_TOP15 j beta Hj Hb) as Htop.
  destruct (le_lt_dec 271970482 (j - 135985239)) as [Hbig | Hsmall].
  - (* j15 = j - 135985239 >= 271970482: the core *)
    destruct (H16 (j - 135985239) beta Hbig Hb)
      as [pb [A [Ha Hsteps]]].
    exists pb, A. split; [exact Ha |].
    exact (hsteps_trans _ _ _ Htop Hsteps).
  - destruct (le_lt_dec 4 (j - 135985239)) as [Hband | Htiny].
    + (* band 15: j15 = j - 135985239, 4 <= j15 <= (271970479 + 2) *)
      exists [271970479; 147491795; 47892099; 24915618; 1835911; 568849; 317482; 29175; 9907; 6375; 799; 475; 93; 58; 5],
        (2 * (j - 135985239) + beta - 2).
      split; [lia |].
      assert (Hj2 : j - 135985239 <= (271970479 + 2)).
      { rewrite NUM61m in Hsmall.
        apply (proj1 (Nat.lt_succ_r _ _) Hsmall). }
      exact (hsteps_trans _ _ _ Htop
               (TOP61_BAND (j - 135985239) beta Hband Hj2 Hb)).
    + (* tiny: j15 = j - 135985239 <= 3; j15 >= 1 since 135985240 <= j *)
      destruct (Nat.eq_dec (j - 135985239) 1) as [He | Hne].
      * (* r15' = 2 *)
        rewrite He in Htop.
        exists [147491796; 47892099; 24915618; 1835911; 568849; 317482; 29175; 9907; 6375; 799; 475; 93; 58; 5],
          (271970480 + (beta - 1)).
        split; [rewrite NUM61n; lia |].
        exact (hsteps_trans _ _ _ Htop (TOP61_2 beta Hb)).
      * destruct (Nat.eq_dec (j - 135985239) 2) as [He | Hne'].
        -- (* r15' = 4 *)
           rewrite He in Htop.
           exists [271970479; 147491795; 47892099; 24915618; 1835911; 568849; 317482; 29175; 9907; 6375; 799; 475; 93; 58; 5], (beta + 2).
           split; [lia |].
           exact (hsteps_trans _ _ _ Htop (TOP61_4 beta Hb)).
        -- destruct (Nat.eq_dec (j - 135985239) 3) as [He | Hne''].
           ++ (* r15' = 6 *)
              rewrite He in Htop.
              exists [271970479; 147491795; 47892099; 24915618; 1835911; 568849; 317482; 29175; 9907; 6375; 799; 475; 93; 58; 5], (beta + 4).
              split; [lia |].
              exact (hsteps_trans _ _ _ Htop (TOP61_6 beta Hb)).
           ++ (* j15 = 0, contradicting 135985240 <= j *)
              exfalso.
              assert (H0 : j - 135985239 = 0) by lia.
              rewrite NUM60m in Hj.
              lia.
Qed.

(* ----------------------------------------------------------------- *)
(* ESC_ERA_LAW_61: the phase-8 ESC era law at every even            *)
(* R >= 1278 (M >= 616), modulo TAIL2_END16 alone.                  *)
(* ----------------------------------------------------------------- *)

Lemma ESC_ERA_LAW_61 : TAIL2_END16 ->
  forall M beta, 616 <= M -> 2 <= beta ->
  exists n c pb a,
    run n (esc_src (2 * M + 52) (beta - 2)) = Some c
    /\ cfg_sim c (rcsec (false :: repeat true (S a) ++ enc pb)
                        (2 * beta + 2) [(1, 2)])
    /\ beta <= a.
Proof.
  intros H M beta HM Hb.
  apply (ESC_ERA_LAW_60 (TAIL2_END15_of61 H) M beta HM Hb).
Qed.

(* ----------------------------------------------------------------- *)
(* Assumption audit                                                  *)
(* ----------------------------------------------------------------- *)
Print Assumptions TOP61_BAND.
Print Assumptions TAIL2_END15_of61.
Print Assumptions ESC_ERA_LAW_61.
