(* ================================================================= *)
(*  Grind.v -- Phase 28: frame-general step lists + the hybrid word  *)
(*  model of phase21 sec.7 (component #19, word level).              *)
(*                                                                   *)
(*  Part 1: gcsec/gbsec generalisations of the Sections.v rules      *)
(*  (TDN, PUSH, POP, TUP, Stage A) and of the CGAP2 dispatches --    *)
(*  the frozen prefix is carried untouched.                          *)
(*  Part 2: hsec/hstep, the word-level rule relation (phase21 sec.1  *)
(*  dispatch), with hcfg encoding prefix blocks via `enc`;           *)
(*  hstep_sound: every word step is realised by a machine run        *)
(*  (up to cfg_sim for REGEN, whose machine form lands on the        *)
(*  tape-equal blank-end section csecR).  PUSHX and REGEN are        *)
(*  pb = [] rules: PUSHX's excursion reads the prefix (that is what  *)
(*  PX2A/PX2B are for), and REGEN's gbsec generalisation is open     *)
(*  (see mechanisation-status.md).                                   *)
(* ================================================================= *)

Require Import List Bool Arith Lia ZArith.
Import ListNotations.
Require Import TM Sections Mirror TokenPass Recoord Era Esc Dev.

Lemma gTDN : forall Q a2 pairs G,
  run 6 (gcsec Q a2 1 2 pairs G) = Some (gbsec Q a2 1 4 pairs G).
Proof. intros. reflexivity. Qed.

Lemma gPUSH : forall Q a2' g'' pairs G,
  run 9 (gcsec Q (S a2') (S (S (S g''))) 2 pairs G) =
  Some (gcsec Q a2' 1 2 ((S g'', 2) :: pairs) G).
Proof. intros. reflexivity. Qed.

Lemma gstageA_prefix : forall P a s' G,
  run 2 (gbsec P a 1 (S s') [] G) =
  Some (mkCfg SA (false :: true :: (repeat true a ++ P))
         (repeat true s' ++ tail [] G)).
Proof. intros. reflexivity. Qed.

Lemma gSTGA : forall P a s G, 2 <= s -> 3 <= G ->
  run (2 * s + 6) (gbsec P a 1 s [] G) =
  Some (gcsec P a (s - 1) 2 [] (G - 2)).
Proof.
  intros P a s G Hs HG.
  destruct s as [| [| s'']]; try lia.
  destruct G as [| [| [| G']]]; try lia.
  replace (2 * S (S s'') + 6) with (2 + (S s'' + (5 + (s'' + 2))))
    by lia.
  rewrite run_split.
  rewrite gstageA_prefix. cbv beta iota.
  rewrite run_split.
  rewrite sweepA. cbv beta iota.
  assert (Hprobe : run 5
    (mkCfg SA (repeat true (S s'') ++ (false :: true :: (repeat true a ++ P)))
       (tail [] (S (S (S G'))))) =
    Some (mkCfg SF (repeat true s'' ++ (false :: true :: (repeat true a ++ P)))
           (true :: true :: true :: false ::
             (repeat false G' ++ [true; true])))).
  { reflexivity. }
  rewrite run_split.
  rewrite Hprobe. cbv beta iota.
  rewrite run_split.
  rewrite sweepF. cbv beta iota.
  reflexivity.
Qed.

Lemma gpop_prefix : forall P a s r1 rest G, 1 <= s ->
  run (s + 2) (gbsec P a 1 s ((1, r1) :: rest) G) =
  Some (mkCfg SB (repeat true s ++ (false :: repeat true (S a) ++ P))
                 (repeat true r1 ++ tail rest G)).
Proof.
  intros P a s r1 rest G Hs. destruct s as [| s']; [lia |].
  replace (S s' + 2) with (2 + (s' + 1)) by lia.
  rewrite run_split.
  assert (H2 : run 2 (gbsec P a 1 (S s') ((1, r1) :: rest) G) =
    Some (mkCfg SA (false :: true :: (repeat true a ++ P))
           (repeat true s' ++
             (false :: (repeat true r1 ++ tail rest G))))).
  { reflexivity. }
  rewrite H2. cbv beta iota.
  rewrite run_split.
  rewrite sweepA. cbv beta iota.
  reflexivity.
Qed.

Lemma gpop_sweep : forall P a s r1 rest G, 1 <= s -> 1 <= r1 ->
  run (s + 1) (mkCfg SB (repeat true s ++ (false :: repeat true (S a) ++ P))
                 (repeat true r1 ++ tail rest G)) =
  Some (gbsec P (S a) 1 (s + r1) rest G).
Proof.
  intros P a s r1 rest G Hs Hr1.
  destruct s as [| s'']; [lia |]. destruct r1 as [| r1']; [lia |].
  rewrite run_split.
  change (repeat true (S r1') ++ tail rest G)
    with (true :: (repeat true r1' ++ tail rest G)).
  rewrite sweepB. cbv beta iota.
  unfold gbsec. rewrite rep_app. rewrite <- !app_assoc.
  reflexivity.
Qed.

Lemma gPOP : forall P a s r1 rest G, 2 <= s -> 1 <= r1 ->
  run (2 * s + 3) (gbsec P a 1 s ((1, r1) :: rest) G) =
  Some (gbsec P (S a) 1 (s + r1) rest G).
Proof.
  intros P a s r1 rest G Hs Hr1.
  assert (Hs1 : 1 <= s) by lia.
  replace (2 * s + 3) with ((s + 2) + (s + 1)) by lia.
  rewrite run_split.
  rewrite (gpop_prefix P a s r1 rest G Hs1).
  exact (gpop_sweep P a s r1 rest G Hs1 Hr1).
Qed.

Lemma gtup_prefix3 : forall P a s' g1' r1 rest G,
  run (S s' + 2) (gbsec P a 1 (S s') ((S g1', r1) :: rest) G) =
  Some (mkCfg SB (repeat true (S s') ++ (false :: repeat true (S a) ++ P))
                 (repeat false g1' ++ (repeat true r1 ++ tail rest G))).
Proof.
  intros P a s' g1' r1 rest G.
  replace (S s' + 2) with (2 + (s' + 1)) by lia.
  rewrite run_split.
  assert (H2 : run 2 (gbsec P a 1 (S s') ((S g1', r1) :: rest) G) =
    Some (mkCfg SA (false :: repeat true (S a) ++ P)
           (repeat true s' ++
             (repeat false (S g1') ++ (repeat true r1 ++ tail rest G))))).
  { reflexivity. }
  rewrite H2. cbv beta iota.
  rewrite run_split.
  rewrite sweepA. cbv beta iota.
  reflexivity.
Qed.

Lemma gTUP : forall P a s'' g1'' r1 rest G,
  run (2 * S (S s'') + 6)
    (gbsec P a 1 (S (S s'')) ((S (S (S g1'')), r1) :: rest) G) =
  Some (gcsec P a (S s'') 2 ((S g1'', r1) :: rest) G).
Proof.
  intros P a s'' g1'' r1 rest G.
  replace (2 * S (S s'') + 6) with ((S (S s'') + 2) + (S s'' + 5)) by lia.
  rewrite run_split.
  rewrite (gtup_prefix3 P a (S s'') (S (S g1'')) r1 rest G).
  assert (H4 : run 4
    (mkCfg SB (repeat true (S (S s'')) ++ (false :: repeat true (S a) ++ P))
       (repeat false (S (S g1'')) ++ (repeat true r1 ++ tail rest G))) =
    Some (mkCfg SF (repeat true s'' ++ (false :: repeat true (S a) ++ P))
       (true :: true :: true :: false ::
         (repeat false g1'' ++ (repeat true r1 ++ tail rest G))))).
  { reflexivity. }
  replace (S s'' + 5) with (4 + (s'' + 2)) by lia.
  rewrite run_split.
  rewrite H4. cbv beta iota.
  rewrite run_split.
  rewrite sweepF. cbv beta iota.
  reflexivity.
Qed.

Lemma gCGAP2_probe : forall Q a2 w1 r1 rest G,
  run 4 (gcsec Q a2 2 2 ((w1, r1) :: rest) G) =
  Some (gcsec ((false :: repeat true a2) ++ Q) 3 w1 r1 rest G).
Proof. intros. reflexivity. Qed.

Lemma gCGAP2_pop : forall Q a2 r1' rest G,
  run 6 (gcsec ((false :: repeat true a2) ++ Q) 3 1 (S r1') rest G) =
  Some (gbsec ((false :: repeat true a2) ++ Q) 3 1 (2 + S r1') rest G).
Proof. intros. reflexivity. Qed.

Lemma gCGAP2_push : forall Q a2 w1' r1 rest G,
  run 9 (gcsec ((false :: repeat true a2) ++ Q) 3 (S (S (S w1'))) r1 rest G) =
  Some (gcsec ((false :: repeat true a2) ++ Q) 2 1 2 ((S w1', r1) :: rest) G).
Proof. intros. reflexivity. Qed.

Lemma gCGAP2_pop_total : forall Q a2 r1' rest G,
  run 10 (gcsec Q a2 2 2 ((1, S r1') :: rest) G) =
  Some (gbsec ((false :: repeat true a2) ++ Q) 3 1 (2 + S r1') rest G).
Proof.
  intros Q a2 r1' rest G.
  replace 10 with (4 + 6) by lia.
  rewrite run_split.
  rewrite gCGAP2_probe.
  apply gCGAP2_pop.
Qed.

Lemma gCGAP2_push_total : forall Q a2 w1' r1 rest G,
  run 13 (gcsec Q a2 2 2 ((S (S (S w1')), r1) :: rest) G) =
  Some (gcsec ((false :: repeat true a2) ++ Q) 2 1 2 ((S w1', r1) :: rest) G).
Proof.
  intros Q a2 w1' r1 rest G.
  replace 13 with (4 + 9) by lia.
  rewrite run_split.
  rewrite gCGAP2_probe.
  apply gCGAP2_push.
Qed.
(* ================================================================= *)
(*  Part 2: the word model.                                          *)
(* ================================================================= *)

Fixpoint enc (pb : list nat) : list sym :=
  match pb with
  | [] => []
  | b :: pb' => (false :: repeat true b) ++ enc pb'
  end.

Inductive hsec :=
| HC : list nat -> nat -> nat -> nat -> list (nat * nat) -> nat -> hsec
| HB : list nat -> nat -> nat -> nat -> list (nat * nat) -> nat -> hsec.

Definition hcfg (x : hsec) : config :=
  match x with
  | HC pb a2 g0 s pairs G => gcsec (enc pb) a2 g0 s pairs G
  | HB pb a g0 s pairs G => gbsec (enc pb) a g0 s pairs G
  end.

Lemma gbsec_nil : forall a g0 s pairs G,
  gbsec [] a g0 s pairs G = bsec a g0 s pairs G.
Proof. intros. unfold gbsec, bsec. rewrite app_nil_r. reflexivity. Qed.

Inductive hstep : hsec -> hsec -> Prop :=
| hTDN : forall pb a2 pairs G,
    hstep (HC pb a2 1 2 pairs G) (HB pb a2 1 4 pairs G)
| hPUSH : forall pb a2' g'' pairs G,
    hstep (HC pb (S a2') (S (S (S g''))) 2 pairs G)
          (HC pb a2' 1 2 ((S g'', 2) :: pairs) G)
| hPUSHX : forall pairs G,
    hstep (HC [] 0 3 2 pairs G) (HB [] 1 1 7 pairs G)
| hPX2A : forall b' p' pb pairs G,
    hstep (HC (S (S (S b')) :: S p' :: pb) 0 3 2 pairs G)
          (HC pb p' (S b') 2 ((1, 1) :: (1, 2) :: (1, 2) :: pairs) G)
| hPX2A2 : forall p' pb pairs G,
    hstep (HC (2 :: S p' :: pb) 0 3 2 pairs G)
          (HB pb p' 1 5 ((1, 2) :: (1, 2) :: pairs) G)
| hPX2B2 : forall pairs G,
    hstep (HC [2] 0 3 2 pairs G) (HB [] 1 1 8 ((1, 2) :: pairs) G)
| hPX2B3 : forall pairs G,
    hstep (HC [3] 0 3 2 pairs G)
          (HB [] 1 1 6 ((1, 2) :: (1, 2) :: pairs) G)
| hPX2B4 : forall pairs G,
    hstep (HC [4] 0 3 2 pairs G)
          (HB [0] 4 1 3 ((1, 2) :: (1, 2) :: pairs) G)
| hPX2B5 : forall pairs G,
    hstep (HC [5] 0 3 2 pairs G)
          (HB [0] 4 1 4 ((1, 1) :: (1, 2) :: (1, 2) :: pairs) G)
| hPX2B6 : forall pairs G,
    hstep (HC [6] 0 3 2 pairs G)
          (HB [4; 0] 3 1 3 ((1, 2) :: (1, 2) :: pairs) G)
| hCGAP2pop : forall pb a2 r1' rest G,
    hstep (HC pb a2 2 2 ((1, S r1') :: rest) G)
          (HB (a2 :: pb) 3 1 (2 + S r1') rest G)
| hCGAP2push : forall pb a2 w1' r1 rest G,
    hstep (HC pb a2 2 2 ((S (S (S w1')), r1) :: rest) G)
          (HC (a2 :: pb) 2 1 2 ((S w1', r1) :: rest) G)
| hPOP : forall pb a s r1 rest G, 2 <= s -> 1 <= r1 ->
    hstep (HB pb a 1 s ((1, r1) :: rest) G)
          (HB pb (S a) 1 (s + r1) rest G)
| hTUP : forall pb a s'' g1'' r1 rest G,
    hstep (HB pb a 1 (S (S s'')) ((S (S (S g1'')), r1) :: rest) G)
          (HC pb a (S s'') 2 ((S g1'', r1) :: rest) G)
| hSTGA : forall pb a s G, 2 <= s -> 3 <= G ->
    hstep (HB pb a 1 s [] G) (HC pb a (s - 1) 2 [] (G - 2))
| hREGEN : forall a s, 2 <= s ->
    hstep (HB [] a 1 s [] 1) (HC [] a 1 2 [] (s - 1))
| hTRANS2_1 : forall pb a s' r1' r2 rest G, 1 <= r2 ->
    hstep (HB pb a 1 (S s') ((2, S r1') :: (1, r2) :: rest) G)
          (HB (S a :: pb) (S (S s')) 1 (S r1' + r2) rest G)
| hTRANS2_2 : forall pb a s0 r1 r2 r3 rest G, 1 <= r3 ->
    hstep (HB pb a 1 (S s0) ((2, S r1) :: (2, S r2) :: (1, r3) :: rest) G)
          (HB (S (S s0) :: S a :: pb) (S (S r1)) 1 (S r2 + r3) rest G)
| hTUP2_1 : forall pb a s' r1'' w2'' r2 rest G,
    hstep (HB pb a 1 (S s') ((2, S (S r1'')) :: (S (S (S w2'')), r2) :: rest) G)
          (HC (S a :: pb) (S s') (S r1'') 2 ((S w2'', r2) :: rest) G)
| hTUP2def : forall pb a s' w3' r2' rest G,
    hstep (HB pb a 1 (S s') ((2, 1) :: (S (S (S (S (S w3')))), S r2') :: rest) G)
          (HC (S a :: pb) s' 3 2 ((S w3', S r2') :: rest) G)
(* Phase 36: the third re-basing's dip bottoms.  hPX2A0 is the      *)
(* PX2A dispatch at a two-block prefix whose second block is 0      *)
(* (hPX2A needs S p', hPX2A2 needs b = 2); hPX2B0 is the PX2B       *)
(* dispatch at the empty single block [0].                          *)
| hPX2A0 : forall b'' pairs G,
    hstep (HC (S (S (S (S (S b'')))) :: 0 :: nil) 0 3 2 pairs G)
          (HB [0] 3 1 2
             ((S b'', 2) :: (1, 1) :: (1, 2) :: (1, 2) :: pairs) G)
| hPX2B0 : forall pairs G,
    hstep (HC [0] 0 3 2 pairs G) (HB [] 0 1 5 ((1, 2) :: pairs) G)
(* Phase 41: hPX2Bgen -- the PX2B dispatch at a single-block       *)
(* prefix [b], b >= 5 (the phase-8 dip at [19]); Dev.v's uniform    *)
(* PX2Bgen family, same landing shape and cost as hPX2A0.           *)
| hPX2Bgen : forall b'' pairs G,
    hstep (HC [S (S (S (S (S b''))))] 0 3 2 pairs G)
          (HB [0] 3 1 2
             ((S b'', 2) :: (1, 1) :: (1, 2) :: (1, 2) :: pairs) G).

Theorem hstep_sound : forall x y, hstep x y ->
  exists n c, run n (hcfg x) = Some c /\ cfg_sim c (hcfg y).
Proof.
  intros x y H. induction H; unfold hcfg; cbn [enc].
  - exists 6, (gbsec (enc pb) a2 1 4 pairs G). split; [apply gTDN | apply cfg_sim_refl].
  - exists 9, (gcsec (enc pb) a2' 1 2 ((S g'', 2) :: pairs) G).
    split; [apply gPUSH | apply cfg_sim_refl].
  - exists 33, (bsec 1 1 7 pairs G).
    split; [rewrite gcsec_nil; apply PUSHX |].
    rewrite gbsec_nil. apply cfg_sim_refl.
  - exists (b' + 14), (gcsec (enc pb) p' (S b') 2 ((1, 1) :: (1, 2) :: (1, 2) :: pairs) G).
    split; [apply PX2A | apply cfg_sim_refl].
  - exists 23, (gbsec (enc pb) p' 1 5 ((1, 2) :: (1, 2) :: pairs) G).
    split; [apply PX2A_b2 | apply cfg_sim_refl].
  - exists 43, (bsec 1 1 8 ((1, 2) :: pairs) G).
    split; [rewrite app_nil_r; apply PX2B_b2 |].
    rewrite gbsec_nil. apply cfg_sim_refl.
  - exists 38, (bsec 1 1 6 ((1, 2) :: (1, 2) :: pairs) G).
    split; [rewrite app_nil_r; apply PX2B_b3 |].
    rewrite gbsec_nil. apply cfg_sim_refl.
  - exists 29, (gbsec [false] 4 1 3 ((1, 2) :: (1, 2) :: pairs) G).
    split; [rewrite app_nil_r; apply PX2B_b4' | apply cfg_sim_refl].
  - exists 44, (gbsec [false] 4 1 4 ((1, 1) :: (1, 2) :: (1, 2) :: pairs) G).
    split; [rewrite app_nil_r; apply PX2B_b5' | apply cfg_sim_refl].
  - exists 49, (gbsec ((false :: repeat true 4) ++ [false]) 3 1 3
               ((1, 2) :: (1, 2) :: pairs) G).
    split; [rewrite app_nil_r; apply PX2B_b6' | apply cfg_sim_refl].
  - exists 10, (gbsec ((false :: repeat true a2) ++ enc pb) 3 1 (2 + S r1') rest G).
    split; [apply gCGAP2_pop_total | apply cfg_sim_refl].
  - exists 13, (gcsec ((false :: repeat true a2) ++ enc pb) 2 1 2
                 ((S w1', r1) :: rest) G).
    split; [apply gCGAP2_push_total | apply cfg_sim_refl].
  - exists (2 * s + 3), (gbsec (enc pb) (S a) 1 (s + r1) rest G).
    split; [apply gPOP; assumption | apply cfg_sim_refl].
  - exists (2 * S (S s'') + 6), (gcsec (enc pb) a (S s'') 2 ((S g1'', r1) :: rest) G).
    split; [apply gTUP | apply cfg_sim_refl].
  - exists (2 * s + 6), (gcsec (enc pb) a (s - 1) 2 [] (G - 2)).
    split; [apply gSTGA; assumption | apply cfg_sim_refl].
  - (* REGEN: machine lands on csecR, tape-equal to the csec form. *)
    destruct s as [| [| s2]]; try lia.
    exists (4 * S (S s2) + 22), (csecR a (S s2) [false]).
    split.
    + rewrite gbsec_nil. replace (S (S s2) - 1) with (S s2) by lia.
      apply REGEN. lia.
    + rewrite gcsec_nil. unfold cfg_sim. split; [reflexivity |].
      intros p. apply REGEN_tape.
  - exists ((S s' + 2) + ((S r1' + 2) + (S r1' + 1))),
      (gbsec (enc (S a :: pb)) (S (S s')) 1 (S r1' + r2) rest G).
    split; [apply TRANS2_1; assumption | apply cfg_sim_refl].
  - exists ((S s0 + 2) + ((S r1 + 2) + ((S r2 + 2) + (S r2 + 1)))),
      (gbsec (enc (S (S s0) :: S a :: pb)) (S (S r1)) 1 (S r2 + r3) rest G).
    split; [apply TRANS2_2; assumption | apply cfg_sim_refl].
  - exists (S s' + 2 * S (S r1'') + 8),
      (gcsec (enc (S a :: pb)) (S s') (S r1'') 2 ((S w2'', r2) :: rest) G).
    split; [apply TUP2_1 | apply cfg_sim_refl].
  - exists (S s' + 23), (gcsec (enc (S a :: pb)) s' 3 2 ((S w3', S r2') :: rest) G).
    split; [apply TUP2_defect | apply cfg_sim_refl].
  - exists (b'' + 37), (hcfg (HB [0] 3 1 2
      ((S b'', 2) :: (1, 1) :: (1, 2) :: (1, 2) :: pairs) G)).
    split; [| apply cfg_sim_refl].
    unfold hcfg. cbn [enc]. rewrite !app_nil_r. apply PX2A0.
  - exists 20, (hcfg (HB [] 0 1 5 ((1, 2) :: pairs) G)).
    split; [| apply cfg_sim_refl].
    unfold hcfg. cbn [enc]. rewrite app_nil_r. apply PX2B0.
  - exists (b'' + 37), (hcfg (HB [0] 3 1 2
      ((S b'', 2) :: (1, 1) :: (1, 2) :: (1, 2) :: pairs) G)).
    split; [| apply cfg_sim_refl].
    unfold hcfg. cbn [enc]. rewrite !app_nil_r. apply PX2Bgen.
Qed.

(* ================================================================= *)
(*  Part 3: step sequences, the grind prefix, predecessor analysis.  *)
(* ================================================================= *)

Inductive hsteps : hsec -> hsec -> Prop :=
| hsteps_refl : forall x, hsteps x x
| hsteps_step : forall x y z, hstep x y -> hsteps y z -> hsteps x z.

Lemma hsteps_trans : forall x y z, hsteps x y -> hsteps y z -> hsteps x z.
Proof.
  intros x y z H1. induction H1 as [| u v w Hstep Hsteps IH]; intros H2.
  - exact H2.
  - apply (hsteps_step _ v z); [exact Hstep | apply IH; exact H2].
Qed.

Lemma hsteps_sound : forall x y, hsteps x y ->
  exists n c, run n (hcfg x) = Some c /\ cfg_sim c (hcfg y).
Proof.
  intros x y H. induction H as [| u v w Hstep Hsteps IH].
  - exists 0, (hcfg x). split; [reflexivity | apply cfg_sim_refl].
  - destruct (hstep_sound _ _ Hstep) as [n1 [c1 [Hr1 Hs1]]].
    destruct IH as [n2 [c2 [Hr2 Hs2]]].
    destruct (run_sim_transfer n2 c1 (hcfg v) c2 Hs1 Hr2)
      as [c1' [Hr1' Hs1']].
    exists (n1 + n2), c1'. split.
    + rewrite run_split, Hr1. exact Hr1'.
    + apply (cfg_sim_trans _ _ _ Hs1' Hs2).
  Qed.

(* The forced prefix of the G'' recursion (phase21 sec.7):           *)
(* [TDN, TUP, PUSH, TDN, POP] reduces the grind C-section with the   *)
(* residue pair (R, 2) to the B-section with residue (R - 2, 2),     *)
(* at every frame pb and every a2 >= 1.                              *)
Lemma grind_prefix : forall pb a2' r' W G,
  hsteps (HC pb (S a2') 1 2 ((S (S (S r')), 2) :: W) G)
         (HB pb (S a2') 1 6 ((S r', 2) :: W) G).
Proof.
  intros pb a2' r' W G.
  apply (hsteps_step _ (HB pb (S a2') 1 4 ((S (S (S r')), 2) :: W) G)).
  { apply hTDN. }
  apply (hsteps_step _ (HC pb (S a2') 3 2 ((S r', 2) :: W) G)).
  { apply (hTUP pb (S a2') 2 r' 2 W G). }
  apply (hsteps_step _ (HC pb a2' 1 2 ((1, 2) :: (S r', 2) :: W) G)).
  { apply (hPUSH pb a2' 0 ((S r', 2) :: W) G). }
  apply (hsteps_step _ (HB pb a2' 1 4 ((1, 2) :: (S r', 2) :: W) G)).
  { apply hTDN. }
  apply (hsteps_step _ (HB pb (S a2') 1 6 ((S r', 2) :: W) G)).
  { apply hPOP; lia. }
  apply hsteps_refl.
Qed.

(* The deviation at the bottom of the dip (a2 = 0, pb = []): the     *)
(* PUSH node is PUSHX instead, landing on the B-section (a = 1,      *)
(* s = 7).  This is the excursion whose continuation the human       *)
(* proof re-bases by a finite check (phase21 sec.7); the word-level  *)
(* reduction itself is exact.                                        *)
Lemma grind_prefix_dev : forall r' W G,
  hsteps (HC [] 0 1 2 ((S (S (S r')), 2) :: W) G)
         (HB [] 1 1 7 ((S r', 2) :: W) G).
Proof.
  intros r' W G.
  apply (hsteps_step _ (HB [] 0 1 4 ((S (S (S r')), 2) :: W) G)).
  { apply hTDN. }
  apply (hsteps_step _ (HC [] 0 3 2 ((S r', 2) :: W) G)).
  { apply (hTUP [] 0 2 r' 2 W G). }
  apply (hsteps_step _ (HB [] 1 1 7 ((S r', 2) :: W) G)).
  { apply hPUSHX. }
  apply hsteps_refl.
Qed.

(* Predecessor analysis (word level): the producers of a             *)
(* PUSH-at-a=2 source -- an HC section with a2 = 0, s = 2, g0 >= 3.  *)
(* Only four rules can land on such a section: TUP (source shuttle   *)
(* g0 + 2), STGA (source shuttle g0 + 1, empty pairs), PX2A (frame   *)
(* block b' = g0 - 1 over a 0-block), and the TUP2 defect at g0 = 3.  *)
(* The Predecessor Lemma of phase21 sec.2 is the statement that, in  *)
(* an era grind, the first two producers have source shuttle         *)
(* exactly 4 (so g0 = 3) and PX2A does not occur; those are the      *)
(* invariant obligations recorded in mechanisation-status.md.        *)
Lemma pred_cases : forall x y pb g pairs G,
  hstep x y -> y = HC pb 0 (S (S (S g))) 2 pairs G ->
  (exists s'' g1'' r1 W, x = HB pb 0 1 (S (S s'')) ((S (S (S g1'')), r1) :: W) G
                    /\ S s'' = S (S (S g)) /\ pairs = (S g1'', r1) :: W) \/
  (exists s G', x = HB pb 0 1 s [] G' /\ pairs = [] /\ s - 1 = S (S (S g))
                /\ G = G' - 2) \/
  (exists b' pb' W, x = HC (S (S (S b')) :: 1 :: pb') 0 3 2 W G
                    /\ pb = pb' /\ S b' = S (S (S g))
                    /\ pairs = (1, 1) :: (1, 2) :: (1, 2) :: W) \/
  (exists a pb0 s' w3' r2' W, x = HB pb0 a 1 (S s') ((2, 1) ::
                    (S (S (S (S (S w3')))), S r2') :: W) G
                    /\ pb = S a :: pb0 /\ s' = 0 /\ g = 0
                    /\ pairs = (S w3', S r2') :: W).
Proof.
  intros x y pb g pairs G H Hy. subst y.
  inversion H; subst; try discriminate;
  solve [ left; eexists; eexists; eexists; eexists;
          repeat split; first [reflexivity | assumption]
        | right; left; eexists; eexists;
          repeat split; first [reflexivity | assumption]
        | right; right; left; eexists; eexists; eexists;
          repeat split; first [reflexivity | assumption]
        | right; right; right; eexists; eexists; eexists; eexists;
          eexists; eexists;
          repeat split; first [reflexivity | assumption] ].
Qed.
