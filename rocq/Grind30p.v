(* ================================================================= *)
(* Phase 62 (tail): the TOP16 closings, the residual core          *)
(* TAIL2_END17, TAIL2_END16_of62 and ESC_ERA_LAW_62.  Mirrors      *)
(* Grind29p.v at the TOP16 constants.                              *)
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
               Grind30h Grind30l Grind30m Grind30n Grind30o.
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

Lemma TOP62_BAND : forall j beta, 4 <= j -> j <= (595648557 + 2) -> 2 <= beta ->
  hsteps (HB [60654542; 9546949; 4860546; 349423; 101323; 57668; 5526; 626; 189; 112; 33; 19; 0] 367754682 1 595648557
            ((2 * j, 2) :: (1, 1) :: repeat (1, 2) (beta - 1)) 1)
         (HB [595648557; 367754682; 60654542; 9546949; 4860546; 349423; 101323; 57668; 5526; 626; 189; 112; 33; 19; 0]
            (2 * j + beta - 2) 1 (2 * beta + 1) [] 1).
Proof.
  intros j beta Hj1 Hj2 Hb.
  apply (hsteps_trans _ (HC [60654542; 9546949; 4860546; 349423; 101323; 57668; 5526; 626; 189; 112; 33; 19; 0]
    367754682 595648556 2 ((2 * j - 2, 2) :: (1, 1)
            :: repeat (1, 2) (beta - 1)) 1)).
  { rewrite NUM62h.
    apply (sTUP [60654542; 9546949; 4860546; 349423; 101323; 57668; 5526; 626; 189; 112; 33; 19; 0] 367754682 595648557
           (2 * j) 2 ((1, 1) :: repeat (1, 2) (beta - 1)) 1);
      [exact S62h0 | lia]. }
  apply (hsteps_trans _ (HB [60654542; 9546949; 4860546; 349423; 101323; 57668; 5526; 626; 189; 112; 33; 19; 0]
    367754681 1 595648556 ((2, 2) :: (2 * j - 2, 2) :: (1, 1)
            :: repeat (1, 2) (beta - 1)) 1)).
  { rewrite NUM62a. rewrite NUM62b.
    apply (hGRIND_even 297824276 [60654542; 9546949; 4860546; 349423; 101323; 57668; 5526; 626; 189; 112; 33; 19; 0]
           367754681 ((2 * j - 2, 2) :: (1, 1)
           :: repeat (1, 2) (beta - 1)) 1);
      [exact S62g1 | exact S62g2]. }
  apply (hsteps_trans _ (HC [367754682; 60654542; 9546949; 4860546; 349423; 101323; 57668; 5526; 626; 189; 112; 33; 19; 0] 595648556 1 2 ((2 * j - 4, 2) :: (1, 1)
            :: repeat (1, 2) (beta - 1)) 1)).
  { rewrite NUM62i'. rewrite NUM62b.
    assert (E : ((2 * j - 2 - 2, 2) :: (1, 1)
              :: repeat (1, 2) (beta - 1))
              = ((2 * j - 4, 2) :: (1, 1) :: repeat (1, 2) (beta - 1)))
      by sec_eq.
    rewrite <- E.
    apply (sTUP2_1 [60654542; 9546949; 4860546; 349423; 101323; 57668; 5526; 626; 189; 112; 33; 19; 0] 367754681
           (595648557 - 1 - 1) (2 * j - 2) ((1, 1) :: repeat (1, 2) (beta - 1))
           1); lia. }
  apply (hsteps_trans _ (HB [367754682; 60654542; 9546949; 4860546; 349423; 101323; 57668; 5526; 626; 189; 112; 33; 19; 0] 595648556 1 4 ((2 * j - 4, 2) :: (1, 1)
            :: repeat (1, 2) (beta - 1)) 1)).
  { apply (sTDN [367754682; 60654542; 9546949; 4860546; 349423; 101323; 57668; 5526; 626; 189; 112; 33; 19; 0] 595648556
           ((2 * j - 4, 2) :: (1, 1) :: repeat (1, 2) (beta - 1))
           1). }
  apply (hsteps_trans _ (HC [367754682; 60654542; 9546949; 4860546; 349423; 101323; 57668; 5526; 626; 189; 112; 33; 19; 0] 595648556 3 2 ((2 * j - 6, 2) :: (1, 1)
            :: repeat (1, 2) (beta - 1)) 1)).
  { assert (E : ((2 * j - 4 - 2, 2) :: (1, 1)
              :: repeat (1, 2) (beta - 1))
              = ((2 * j - 6, 2) :: (1, 1) :: repeat (1, 2) (beta - 1)))
      by sec_eq.
    rewrite <- E.
    apply (sTUP [367754682; 60654542; 9546949; 4860546; 349423; 101323; 57668; 5526; 626; 189; 112; 33; 19; 0] 595648556
           4 (2 * j - 4) 2 ((1, 1) :: repeat (1, 2) (beta - 1)) 1);
      lia. }
  apply (hsteps_trans _ (HB [367754682; 60654542; 9546949; 4860546; 349423; 101323; 57668; 5526; 626; 189; 112; 33; 19; 0] 595648556 1 (2 * j - 2)
    ((2, 2) :: (1, 1) :: repeat (1, 2) (beta - 1)) 1)).
  { replace (2 * j - 6) with (2 * (j - 4) + 2) by lia.
    replace (2 * j - 2) with (2 * (j - 4) + 6) by lia.
    apply (CLEANG_even (j - 4) [367754682; 60654542; 9546949; 4860546; 349423; 101323; 57668; 5526; 626; 189; 112; 33; 19; 0] 595648556 ((1, 1) :: repeat (1, 2) (beta - 1))
           1).
    (* the floor (j - 4) + 1 <= SH16 - 1: route via j <= (SH16 + 2) *)
    apply Nat.le_trans with (j - 3).
    - lia.
    - rewrite NUM62k.
      apply Nat.sub_le_mono_r. exact Hj2. }
  apply (hsteps_trans _ (HB [595648557; 367754682; 60654542; 9546949; 4860546; 349423; 101323; 57668; 5526; 626; 189; 112; 33; 19; 0] (2 * j - 1) 1 3 (repeat (1, 2) (beta - 1)) 1)).
  { replace (2 * j - 2) with (S (2 * j - 3)) by lia.
    replace (2 * j - 1) with (S (S (2 * j - 3))) by lia.
    rewrite NUM62e'.
    apply (sTRANS2_1 [367754682; 60654542; 9546949; 4860546; 349423; 101323; 57668; 5526; 626; 189; 112; 33; 19; 0]
           (595648557 - 1) (2 * j - 3) 1 (repeat (1, 2) (beta - 1)) 1); lia. }
  replace (2 * j + beta - 2) with (2 * j - 1 + (beta - 1)) by lia.
  apply (CASCADE_POPFIN [595648557; 367754682; 60654542; 9546949; 4860546; 349423; 101323; 57668; 5526; 626; 189; 112; 33; 19; 0] (2 * j - 1) beta); lia.
Qed.

(* ----------------------------------------------------------------- *)
(* TAIL2_END17: the strictly smaller residual core -- the totality  *)
(* of the TOP16 state for r16' = 2 * j, j >= 595648560               *)
(* (r16' >= 1191297118), where the GRIND17 pair (r16' - 6, 2) at     *)
(* counter 595648556 takes the DIPDESC boundary a seventeenth time.  *)
(* A Definition (lemma parameter), never an axiom.                  *)
(* ----------------------------------------------------------------- *)

Definition TAIL2_END17 : Prop :=
  forall j beta, 595648560 <= j -> 2 <= beta ->
  exists pb A, beta <= A /\
    hsteps (HB [60654542; 9546949; 4860546; 349423; 101323; 57668; 5526; 626; 189; 112; 33; 19; 0] 367754682 1 595648557
              ((2 * j, 2) :: (1, 1) :: repeat (1, 2) (beta - 1)) 1)
           (HB pb A 1 (2 * beta + 1) [] 1).

(* ----------------------------------------------------------------- *)
(* TAIL2_END16_of62: TAIL2_END16, modulo TAIL2_END17.  The j-range *)
(* splits at r16' = 2 * (j - 271970481): the three small cases     *)
(* and band 16 are proved above; j - 271970481 >= 595648560 is the  *)
(* core.                                                            *)
(* ----------------------------------------------------------------- *)

Lemma TAIL2_END16_of62 : TAIL2_END17 -> TAIL2_END16.
Proof.
  intros H17 j beta Hj Hb.
  pose proof (TOP62_TO_TOP16 j beta Hj Hb) as Htop.
  destruct (le_lt_dec 595648560 (j - 271970481)) as [Hbig | Hsmall].
  - (* j16 = j - 271970481 >= 595648560: the core *)
    destruct (H17 (j - 271970481) beta Hbig Hb)
      as [pb [A [Ha Hsteps]]].
    exists pb, A. split; [exact Ha |].
    exact (hsteps_trans _ _ _ Htop Hsteps).
  - destruct (le_lt_dec 4 (j - 271970481)) as [Hband | Htiny].
    + (* band 16: j16 = j - 271970481, 4 <= j16 <= (SH16 + 2) *)
      exists [595648557; 367754682; 60654542; 9546949; 4860546; 349423; 101323; 57668; 5526; 626; 189; 112; 33; 19; 0],
        (2 * (j - 271970481) + beta - 2).
      split; [lia |].
      assert (Hj2 : j - 271970481 <= (595648557 + 2)).
      { rewrite NUM62m in Hsmall.
        apply (proj1 (Nat.lt_succ_r _ _) Hsmall). }
      exact (hsteps_trans _ _ _ Htop
               (TOP62_BAND (j - 271970481) beta Hband Hj2 Hb)).
    + (* tiny: j16 = j - 271970481 <= 3; j16 >= 1 since 271970482 <= j *)
      destruct (Nat.eq_dec (j - 271970481) 1) as [He | Hne].
      * (* r16' = 2 *)
        rewrite He in Htop.
        exists [367754683; 60654542; 9546949; 4860546; 349423; 101323; 57668; 5526; 626; 189; 112; 33; 19; 0],
          (595648558 + (beta - 1)).
        split; [rewrite NUM62n; lia |].
        exact (hsteps_trans _ _ _ Htop (TOP62_2 beta Hb)).
      * destruct (Nat.eq_dec (j - 271970481) 2) as [He | Hne'].
        -- (* r16' = 4 *)
           rewrite He in Htop.
           exists [595648557; 367754682; 60654542; 9546949; 4860546; 349423; 101323; 57668; 5526; 626; 189; 112; 33; 19; 0], (beta + 2).
           split; [lia |].
           exact (hsteps_trans _ _ _ Htop (TOP62_4 beta Hb)).
        -- destruct (Nat.eq_dec (j - 271970481) 3) as [He | Hne''].
           ++ (* r16' = 6 *)
              rewrite He in Htop.
              exists [595648557; 367754682; 60654542; 9546949; 4860546; 349423; 101323; 57668; 5526; 626; 189; 112; 33; 19; 0], (beta + 4).
              split; [lia |].
              exact (hsteps_trans _ _ _ Htop (TOP62_6 beta Hb)).
           ++ (* j16 = 0, contradicting 271970482 <= j *)
              exfalso.
              assert (H0 : j - 271970481 = 0) by lia.
              rewrite NUM62m2 in Hj.
              lia.
Qed.

(* ----------------------------------------------------------------- *)
(* ESC_ERA_LAW_62: the phase-8 ESC era law at every even            *)
(* R >= 1278 (M >= 616), modulo TAIL2_END17 alone.                  *)
(* ----------------------------------------------------------------- *)

Lemma ESC_ERA_LAW_62 : TAIL2_END17 ->
  forall M beta, 616 <= M -> 2 <= beta ->
  exists n c pb a,
    run n (esc_src (2 * M + 52) (beta - 2)) = Some c
    /\ cfg_sim c (rcsec (false :: repeat true (S a) ++ enc pb)
                        (2 * beta + 2) [(1, 2)])
    /\ beta <= a.
Proof.
  intros H M beta HM Hb.
  apply (ESC_ERA_LAW_61 (TAIL2_END16_of62 H) M beta HM Hb).
Qed.

(* ----------------------------------------------------------------- *)
(* Assumption audit                                                  *)
(* ----------------------------------------------------------------- *)
Print Assumptions TOP62_BAND.
Print Assumptions TAIL2_END16_of62.
Print Assumptions ESC_ERA_LAW_62.
