(* ================================================================= *)
(* Phase 63 (tail): the TOP17 closings, the residual core          *)
(* TAIL2_END18, TAIL2_END17_of63 and ESC_ERA_LAW_63.  Mirrors      *)
(* Grind30p.v at the TOP17 constants.                              *)
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
               Grind29m Grind29n Grind29o Grind29p Grind30a Grind30ab
               Grind30h Grind30l Grind30m Grind30n Grind30o Grind30p
               Grind31a Grind31ab Grind31h Grind31l Grind31m Grind31n
               Grind31o.
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

Lemma TOP63_BAND : forall j beta, 4 <= j -> j <= (1191297119 + 2) -> 2 <= beta ->
  hsteps (HB [130856035; 65515088; 349423; 101323; 57668; 5526; 626; 189; 112; 33; 19; 0] 842094153 1 1191297119
            ((2 * j, 2) :: (1, 1) :: repeat (1, 2) (beta - 1)) 1)
         (HB [1191297119; 842094153; 130856035; 65515088; 349423; 101323; 57668; 5526; 626; 189; 112; 33; 19; 0]
            (2 * j + beta - 2) 1 (2 * beta + 1) [] 1).
Proof.
  intros j beta Hj1 Hj2 Hb.
  apply (hsteps_trans _ (HC [130856035; 65515088; 349423; 101323; 57668; 5526; 626; 189; 112; 33; 19; 0]
    842094153 1191297118 2 ((2 * j - 2, 2) :: (1, 1)
            :: repeat (1, 2) (beta - 1)) 1)).
  { rewrite NUM63h.
    apply (sTUP [130856035; 65515088; 349423; 101323; 57668; 5526; 626; 189; 112; 33; 19; 0] 842094153 1191297119
           (2 * j) 2 ((1, 1) :: repeat (1, 2) (beta - 1)) 1);
      [exact S63h0 | lia]. }
  apply (hsteps_trans _ (HB [130856035; 65515088; 349423; 101323; 57668; 5526; 626; 189; 112; 33; 19; 0]
    842094152 1 1191297118 ((2, 2) :: (2 * j - 2, 2) :: (1, 1)
            :: repeat (1, 2) (beta - 1)) 1)).
  { rewrite NUM63a. rewrite NUM63b.
    apply (hGRIND_even 595648557 [130856035; 65515088; 349423; 101323; 57668; 5526; 626; 189; 112; 33; 19; 0]
           842094152 ((2 * j - 2, 2) :: (1, 1)
           :: repeat (1, 2) (beta - 1)) 1);
      [exact S63g1 | exact S63g2]. }
  apply (hsteps_trans _ (HC [842094153; 130856035; 65515088; 349423; 101323; 57668; 5526; 626; 189; 112; 33; 19; 0] 1191297118 1 2 ((2 * j - 4, 2) :: (1, 1)
            :: repeat (1, 2) (beta - 1)) 1)).
  { rewrite NUM63i'. rewrite NUM63b.
    assert (E : ((2 * j - 2 - 2, 2) :: (1, 1)
              :: repeat (1, 2) (beta - 1))
              = ((2 * j - 4, 2) :: (1, 1) :: repeat (1, 2) (beta - 1)))
      by sec_eq.
    rewrite <- E.
    apply (sTUP2_1 [130856035; 65515088; 349423; 101323; 57668; 5526; 626; 189; 112; 33; 19; 0] 842094152
           (1191297119 - 1 - 1) (2 * j - 2) ((1, 1) :: repeat (1, 2) (beta - 1))
           1); lia. }
  apply (hsteps_trans _ (HB [842094153; 130856035; 65515088; 349423; 101323; 57668; 5526; 626; 189; 112; 33; 19; 0] 1191297118 1 4 ((2 * j - 4, 2) :: (1, 1)
            :: repeat (1, 2) (beta - 1)) 1)).
  { apply (sTDN [842094153; 130856035; 65515088; 349423; 101323; 57668; 5526; 626; 189; 112; 33; 19; 0] 1191297118
           ((2 * j - 4, 2) :: (1, 1) :: repeat (1, 2) (beta - 1))
           1). }
  apply (hsteps_trans _ (HC [842094153; 130856035; 65515088; 349423; 101323; 57668; 5526; 626; 189; 112; 33; 19; 0] 1191297118 3 2 ((2 * j - 6, 2) :: (1, 1)
            :: repeat (1, 2) (beta - 1)) 1)).
  { assert (E : ((2 * j - 4 - 2, 2) :: (1, 1)
              :: repeat (1, 2) (beta - 1))
              = ((2 * j - 6, 2) :: (1, 1) :: repeat (1, 2) (beta - 1)))
      by sec_eq.
    rewrite <- E.
    apply (sTUP [842094153; 130856035; 65515088; 349423; 101323; 57668; 5526; 626; 189; 112; 33; 19; 0] 1191297118
           4 (2 * j - 4) 2 ((1, 1) :: repeat (1, 2) (beta - 1)) 1);
      lia. }
  apply (hsteps_trans _ (HB [842094153; 130856035; 65515088; 349423; 101323; 57668; 5526; 626; 189; 112; 33; 19; 0] 1191297118 1 (2 * j - 2)
    ((2, 2) :: (1, 1) :: repeat (1, 2) (beta - 1)) 1)).
  { replace (2 * j - 6) with (2 * (j - 4) + 2) by lia.
    replace (2 * j - 2) with (2 * (j - 4) + 6) by lia.
    apply (CLEANG_even (j - 4) [842094153; 130856035; 65515088; 349423; 101323; 57668; 5526; 626; 189; 112; 33; 19; 0] 1191297118 ((1, 1) :: repeat (1, 2) (beta - 1))
           1).
    (* the floor (j - 4) + 1 <= SH17 - 1: route via j <= (SH17 + 2) *)
    apply Nat.le_trans with (j - 3).
    - lia.
    - rewrite NUM63k.
      apply Nat.sub_le_mono_r. exact Hj2. }
  apply (hsteps_trans _ (HB [1191297119; 842094153; 130856035; 65515088; 349423; 101323; 57668; 5526; 626; 189; 112; 33; 19; 0] (2 * j - 1) 1 3 (repeat (1, 2) (beta - 1)) 1)).
  { replace (2 * j - 2) with (S (2 * j - 3)) by lia.
    replace (2 * j - 1) with (S (S (2 * j - 3))) by lia.
    rewrite NUM63e'.
    apply (sTRANS2_1 [842094153; 130856035; 65515088; 349423; 101323; 57668; 5526; 626; 189; 112; 33; 19; 0]
           (1191297119 - 1) (2 * j - 3) 1 (repeat (1, 2) (beta - 1)) 1); lia. }
  replace (2 * j + beta - 2) with (2 * j - 1 + (beta - 1)) by lia.
  apply (CASCADE_POPFIN [1191297119; 842094153; 130856035; 65515088; 349423; 101323; 57668; 5526; 626; 189; 112; 33; 19; 0] (2 * j - 1) beta); lia.
Qed.

(* ----------------------------------------------------------------- *)
(* TAIL2_END18: the strictly smaller residual core -- the totality  *)
(* of the TOP17 state for r17 = 2 * j, j >= 1191297122                *)
(* (r17 >= 2382594242), where the GRIND18 pair (r17 - 6, 2) at       *)
(* counter 1191297118 takes the DIPDESC boundary an eighteenth time.  *)
(* A Definition (lemma parameter), never an axiom.                  *)
(* ----------------------------------------------------------------- *)

Definition TAIL2_END18 : Prop :=
  forall j beta, 1191297122 <= j -> 2 <= beta ->
  exists pb A, beta <= A /\
    hsteps (HB [130856035; 65515088; 349423; 101323; 57668; 5526; 626; 189; 112; 33; 19; 0] 842094153 1 1191297119
              ((2 * j, 2) :: (1, 1) :: repeat (1, 2) (beta - 1)) 1)
           (HB pb A 1 (2 * beta + 1) [] 1).

(* ----------------------------------------------------------------- *)
(* TAIL2_END17_of63: TAIL2_END17, modulo TAIL2_END18.  The j-range *)
(* splits at r17 = 2 * (j - 595648559): the three small cases      *)
(* and band 17 are proved above; j - 595648559 >= 1191297122 is the  *)
(* core.                                                            *)
(* ----------------------------------------------------------------- *)

Lemma TAIL2_END17_of63 : TAIL2_END18 -> TAIL2_END17.
Proof.
  intros H18 j beta Hj Hb.
  pose proof (TOP63_TO_TOP17 j beta Hj Hb) as Htop.
  destruct (le_lt_dec 1191297122 (j - 595648559)) as [Hbig | Hsmall].
  - (* j17 = j - 595648559 >= 1191297122: the core *)
    destruct (H18 (j - 595648559) beta Hbig Hb)
      as [pb [A [Ha Hsteps]]].
    exists pb, A. split; [exact Ha |].
    exact (hsteps_trans _ _ _ Htop Hsteps).
  - destruct (le_lt_dec 4 (j - 595648559)) as [Hband | Htiny].
    + (* band 17: j17 = j - 595648559, 4 <= j17 <= (SH17 + 2) *)
      exists [1191297119; 842094153; 130856035; 65515088; 349423; 101323; 57668; 5526; 626; 189; 112; 33; 19; 0],
        (2 * (j - 595648559) + beta - 2).
      split; [lia |].
      assert (Hj2 : j - 595648559 <= (1191297119 + 2)).
      { rewrite NUM63m in Hsmall.
        apply (proj1 (Nat.lt_succ_r _ _) Hsmall). }
      exact (hsteps_trans _ _ _ Htop
               (TOP63_BAND (j - 595648559) beta Hband Hj2 Hb)).
    + (* tiny: j17 = j - 595648559 <= 3; j17 >= 1 since 595648560 <= j *)
      destruct (Nat.eq_dec (j - 595648559) 1) as [He | Hne].
      * (* r17 = 2 *)
        rewrite He in Htop.
        exists [842094154; 130856035; 65515088; 349423; 101323; 57668; 5526; 626; 189; 112; 33; 19; 0],
          (1191297120 + (beta - 1)).
        split; [rewrite NUM63n; lia |].
        exact (hsteps_trans _ _ _ Htop (TOP63_2 beta Hb)).
      * destruct (Nat.eq_dec (j - 595648559) 2) as [He | Hne'].
        -- (* r17 = 4 *)
           rewrite He in Htop.
           exists [1191297119; 842094153; 130856035; 65515088; 349423; 101323; 57668; 5526; 626; 189; 112; 33; 19; 0], (beta + 2).
           split; [lia |].
           exact (hsteps_trans _ _ _ Htop (TOP63_4 beta Hb)).
        -- destruct (Nat.eq_dec (j - 595648559) 3) as [He | Hne''].
           ++ (* r17 = 6 *)
              rewrite He in Htop.
              exists [1191297119; 842094153; 130856035; 65515088; 349423; 101323; 57668; 5526; 626; 189; 112; 33; 19; 0], (beta + 4).
              split; [lia |].
              exact (hsteps_trans _ _ _ Htop (TOP63_6 beta Hb)).
           ++ (* j17 = 0, contradicting 595648560 <= j *)
              exfalso.
              assert (H0 : j - 595648559 = 0) by lia.
              rewrite NUM63m2 in Hj.
              lia.
Qed.

(* ----------------------------------------------------------------- *)
(* ESC_ERA_LAW_63: the phase-8 ESC era law at every even            *)
(* R >= 1278 (M >= 616), modulo TAIL2_END18 alone.                  *)
(* ----------------------------------------------------------------- *)

Lemma ESC_ERA_LAW_63 : TAIL2_END18 ->
  forall M beta, 616 <= M -> 2 <= beta ->
  exists n c pb a,
    run n (esc_src (2 * M + 52) (beta - 2)) = Some c
    /\ cfg_sim c (rcsec (false :: repeat true (S a) ++ enc pb)
                        (2 * beta + 2) [(1, 2)])
    /\ beta <= a.
Proof.
  intros H M beta HM Hb.
  apply (ESC_ERA_LAW_62 (TAIL2_END17_of63 H) M beta HM Hb).
Qed.

(* ----------------------------------------------------------------- *)
(* Assumption audit                                                  *)
(* ----------------------------------------------------------------- *)
Print Assumptions TOP63_BAND.
Print Assumptions TAIL2_END17_of63.
Print Assumptions ESC_ERA_LAW_63.
