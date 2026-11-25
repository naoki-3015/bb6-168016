(* ================================================================= *)
(* Era.v -- component #18: the era law (phase18 section 5,         *)
(* phase19 section 2), deviation-free assembly.                    *)
(*                                                                 *)
(* Contents:                                                       *)
(*  - ENTRY_gen: the right-edge entry excursion over an abstract   *)
(*    frozen tail P0 (Mirror.ENTRY is the case P0 = [0] ++ 1^17    *)
(*    with a two-block frame; the era frame has P0 = []).           *)
(*  - GRIND: the Grind Lemma G' -- a C-section with odd gap        *)
(*    m = 2t + 3 grinds through the five rules to a B-section      *)
(*    with s' = m + 3, the pair word and G unchanged, under the    *)
(*    frame floor t + 1 <= a2 (the dip clause: during the grind    *)
(*    a_C dips by exactly (m - 1)/2, attained at w0 = 1 sections;  *)
(*    the floor hypothesis is exactly what each application        *)
(*    discharges -- see mechanisation-status.md for the fenced     *)
(*    sequence-level formulation of the dip clause).               *)
(*  - POP_CHAIN: a B-section pops a whole chain of gap-1 pairs.    *)
(*  - ERA_LAW: the settled era.  From the canonical section        *)
(*      (C, a = 18, s = 2, w = [rho] ++ [1^(beta_E - 1)]-pairs,    *)
(*       G = rho = 29)                                             *)
(*    the era runs: GRIND(29) -> POP_CHAIN (defect pair first)     *)
(*    -> s1 = 2 * beta_E + 31 -> REGEN -> Stage-A era with          *)
(*    s + G = s1 + 3 invariant and G even throughout (so the       *)
(*    odd-G case never arises) -> ENTRY_gen with                   *)
(*    beta' = 2 * beta_E + 34 > beta_E.                            *)
(*                                                                 *)
(* The ESC-family era law (beta_next = 2 * beta + 4) belongs to    *)
(* component #19: its grind is G'' with the PUSHX deviations.      *)
(* The pieces of that grind that are deviation-free (the probe     *)
(* prefix and the transfer POP2) are in Esc.v.                     *)
(* ================================================================= *)

Require Import List Bool Arith Lia ZArith Wf_nat.
Import ListNotations.
Require Import TM Sections Mirror TokenPass Recoord.

(* ----------------------------------------------------------------- *)
(* ENTRY over an abstract tail                                       *)
(* ----------------------------------------------------------------- *)

Definition entry_src_gen (P0 : list sym) (a s : nat) : config :=
  mkCfg SB (repeat true a ++ P0)
    (false :: (repeat true s ++ (repeat false 2 ++ [true; true]))).

Definition entry_tgt_gen (P0 : list sym) (a s : nat) : config :=
  mkCfg SC (repeat true s ++ (false :: repeat true (S a) ++ P0))
    [true; true; false; true; true; false].

Lemma bsec_entry_src : forall a s,
  entry_src_gen [] a s = bsec a 1 s [] 2.
Proof. intros. unfold entry_src_gen, bsec. rewrite app_nil_r.
       reflexivity. Qed.

Lemma entry_prefix_gen : forall P0 a s',
  run (S s' + 2) (entry_src_gen P0 a (S s')) =
  Some (mkCfg SB (repeat true (S s') ++
                   (false :: repeat true (S a) ++ P0))
                 [false; true; true]).
Proof.
  intros P0 a s'.
  replace (S s' + 2) with (2 + (s' + 1)) by lia.
  rewrite run_split.
  assert (H2 : run 2 (entry_src_gen P0 a (S s')) =
    Some (mkCfg SA (false :: repeat true (S a) ++ P0)
           (repeat true s' ++ [false; false; true; true]))).
  { reflexivity. }
  rewrite H2. cbv beta iota.
  rewrite run_split.
  rewrite sweepA. cbv beta iota.
  reflexivity.
Qed.

Lemma ENTRY_gen : forall P0 a s',
  run (S s' + 12) (entry_src_gen P0 a (S s'))
  = Some (entry_tgt_gen P0 a (S s')).
Proof.
  intros P0 a s'.
  replace (S s' + 12) with ((S s' + 2) + 10) by lia.
  rewrite run_split.
  rewrite entry_prefix_gen.
  set (P' := false :: repeat true (S a) ++ P0).
  assert (H3 : run 3
    (mkCfg SB (repeat true (S s') ++ P') [false; true; true]) =
    Some (mkCfg SA (true :: false :: true ::
                      (repeat true (S s') ++ P')) [])).
  { reflexivity. }
  assert (Hprobe : run 5
    (mkCfg SA (true :: false :: true ::
                 (repeat true (S s') ++ P')) []) =
    Some (mkCfg SF (false :: true :: (repeat true (S s') ++ P'))
           [true; true; true; false])).
  { rewrite probe_blank. reflexivity. }
  replace 10 with (3 + (5 + 2)) by lia.
  rewrite run_split.
  rewrite H3. cbv beta iota.
  rewrite run_split.
  rewrite Hprobe. cbv beta iota.
  unfold entry_tgt_gen. reflexivity.
Qed.

Lemma ENTRY_gen_tape : forall P0 a s p,
  tape_of (entry_tgt_gen P0 a s) p =
  tape_of (rcsec (false :: repeat true (S a) ++ P0) s [(1, 2)]) p.
Proof.
  intros P0 a s p. unfold tape_of, entry_tgt_gen, rcsec. cbn [rtail].
  destruct (Z_le_dec 0 p) as [_ | _]; [| reflexivity].
  destruct (Z.to_nat p) as [| [| [| [| [| [| i]]]]]]; try reflexivity.
  destruct i; reflexivity.
Qed.

Lemma entry_gen_sim : forall P0 a s,
  cfg_sim (entry_tgt_gen P0 a s)
          (rcsec (false :: repeat true (S a) ++ P0) s [(1, 2)]).
Proof.
  intros P0 a s. split; [reflexivity |].
  intros p. apply ENTRY_gen_tape.
Qed.

(* ----------------------------------------------------------------- *)
(* GRIND: the Grind Lemma G' (endpoint form)                         *)
(* ----------------------------------------------------------------- *)

Lemma GRIND : forall t a2 P G, t + 1 <= a2 ->
  exists c, run c (csec a2 (2*t + 3) 2 P G)
    = Some (bsec a2 1 (2*t + 6) P G).
Proof.
  induction t as [t IH] using lt_wf_ind.
  intros a2 P G Hfloor.
  destruct t as [|u].
  - (* base: m = 3: PUSH + TDN + POP *)
    destruct a2 as [|a2']; try lia.
    assert (H1 : run 9 (csec (S a2') 3 2 P G)
                 = Some (csec a2' 1 2 ((1, 2) :: P) G)) by apply PUSH.
    assert (H2 : run 6 (csec a2' 1 2 ((1, 2) :: P) G)
                 = Some (bsec a2' 1 4 ((1, 2) :: P) G)) by apply TDN.
    assert (H3 : run 11 (bsec a2' 1 4 ((1, 2) :: P) G)
                 = Some (bsec (S a2') 1 6 P G)).
    { replace 11 with (2 * 4 + 3) by lia.
      replace 6 with (4 + 2) by lia. apply POP; lia. }
    exists (9 + (6 + 11)).
    replace (2 * 0 + 3) with 3 by lia.
    replace (2 * 0 + 6) with 6 by lia.
    rewrite run_split. rewrite H1.
    rewrite run_split. rewrite H2. exact H3.
  - (* step: prefix PUSH + TDN + TUP, loop of (GRIND; TUP),          *)
    (* final GRIND + POP                                             *)
    destruct a2 as [|a2']; try lia.
    assert (Ht : S u + 1 <= S a2') by exact Hfloor.
    (* the loop over the descending gap word *)
    assert (Hloop : forall k i,
      2*i + 3 + 2*k = 2 * S u + 1 -> i + 1 <= a2' ->
      exists c, run c (csec a2' (2*i + 3) 2
                          ((2 * S u + 2 - (2*i + 3), 2) :: P) G)
        = Some (csec a2' (2 * S u + 1) 2 ((1, 2) :: P) G)).
    { induction k as [|k IHk]; intros i Hk Hi.
      - exists 0.
        replace (2 * S u + 2 - (2*i + 3)) with 1 by lia.
        replace (2*i + 3) with (2 * S u + 1) by lia.
        reflexivity.
      - destruct (IH (i) ltac:(lia) a2' ((2 * S u + 2 - (2*i + 3), 2) :: P) G
                      ltac:(lia))
          as [c1 Hc1].
        assert (H2 : exists c, run c
          (bsec a2' 1 (2*i + 6) ((2 * S u + 2 - (2*i + 3), 2) :: P) G)
          = Some (csec a2' (2*(i + 1) + 3) 2
                       ((2 * S u + 2 - (2*(i + 1) + 3), 2) :: P) G)).
        { exists (2 * S (S (2*i + 4)) + 6).
          replace (bsec a2' 1 (2*i + 6) ((2 * S u + 2 - (2*i + 3), 2) :: P) G)
            with (bsec a2' 1 (S (S (2*i + 4)))
                       ((S (S (S (2*u - 2*i - 2))), 2) :: P) G)
            by (repeat f_equal; try reflexivity; lia).
          replace (csec a2' (2*(i + 1) + 3) 2
                       ((2 * S u + 2 - (2*(i + 1) + 3), 2) :: P) G)
            with (csec a2' (S (2*i + 4)) 2 ((S (2*u - 2*i - 2), 2) :: P) G)
            by (repeat f_equal; try reflexivity; lia).
          apply TUP. }
        destruct H2 as [c2 Hc2].
        destruct (IHk (i + 1) ltac:(lia) ltac:(lia)) as [c3 Hc3].
        exists (c1 + (c2 + c3)).
        rewrite run_split. rewrite Hc1.
        rewrite run_split. rewrite Hc2. exact Hc3. }
    (* prefix *)
    assert (H1 : run 9 (csec (S a2') (2 * S u + 3) 2 P G)
                 = Some (csec a2' 1 2 ((2 * S u + 1, 2) :: P) G)).
    { replace (2 * S u + 3) with (S (S (S (2 * S u)))) by lia.
      replace (2 * S u + 1) with (S (2 * S u)) by lia.
      apply PUSH. }
    assert (H2 : run 6 (csec a2' 1 2 ((2 * S u + 1, 2) :: P) G)
                 = Some (bsec a2' 1 4 ((2 * S u + 1, 2) :: P) G))
      by apply TDN.
    assert (H3 : run 14 (bsec a2' 1 4 ((2 * S u + 1, 2) :: P) G)
                 = Some (csec a2' 3 2 ((2 * S u - 1, 2) :: P) G)).
    { replace (bsec a2' 1 4 ((2 * S u + 1, 2) :: P) G)
        with (bsec a2' 1 (S (S 2)) ((S (S (S (2 * u))), 2) :: P) G)
        by (repeat f_equal; try reflexivity; lia).
      replace (csec a2' 3 2 ((2 * S u - 1, 2) :: P) G)
        with (csec a2' (S 2) 2 ((S (2 * u), 2) :: P) G)
        by (repeat f_equal; try reflexivity; lia).
      replace 14 with (2 * S (S 2) + 6) by lia.
      apply TUP. }
    destruct (Hloop u 0 ltac:(lia) ltac:(lia)) as [c4 Hc4].
    replace (2 * S u + 2 - (2*0 + 3)) with (2 * S u - 1) in Hc4 by lia.
    replace (2*0 + 3) with 3 in Hc4 by lia.
    destruct (IH u ltac:(lia) a2' ((1, 2) :: P) G ltac:(lia)) as [c5 Hc5].
    replace (2*u + 3) with (2 * S u + 1) in Hc5 by lia.
    replace (2*u + 6) with (2 * S u + 4) in Hc5 by lia.
    assert (H6 : run (2 * (2 * S u + 4) + 3)
                 (bsec a2' 1 (2 * S u + 4) ((1, 2) :: P) G)
                 = Some (bsec (S a2') 1 (2 * S u + 6) P G)).
    { replace (2 * S u + 6) with ((2 * S u + 4) + 2) by lia.
      apply POP; lia. }
    exists (9 + (6 + (14 + (c4 + (c5 + (2 * (2 * S u + 4) + 3)))))).
    rewrite run_split. rewrite H1.
    rewrite run_split. rewrite H2.
    rewrite run_split. rewrite H3.
    rewrite run_split. rewrite Hc4.
    rewrite run_split. rewrite Hc5. exact H6.
Qed.

(* ----------------------------------------------------------------- *)
(* POP_CHAIN                                                         *)
(* ----------------------------------------------------------------- *)

Fixpoint rsum (rs : list nat) : nat :=
  match rs with
  | [] => 0
  | r :: rs' => r + rsum rs'
  end.

Lemma POP_CHAIN : forall rs a s G,
  (forall r, In r rs -> 1 <= r) -> 2 <= s ->
  exists c, run c (bsec a 1 s (map (fun r => (1, r)) rs) G)
    = Some (bsec (a + length rs) 1 (s + rsum rs) [] G).
Proof.
  induction rs as [|r rs IH]; intros a s G Hr Hs.
  - exists 0. cbn [map length rsum].
    replace (a + 0) with a by lia.
    replace (s + 0) with s by lia.
    reflexivity.
  - assert (H1 : run (2 * s + 3)
                 (bsec a 1 s ((1, r) :: map (fun r0 => (1, r0)) rs) G)
                 = Some (bsec (S a) 1 (s + r) (map (fun r0 => (1, r0)) rs) G))
      by (apply POP; [exact Hs | apply Hr; left; reflexivity]).
    destruct (IH (S a) (s + r) G) as [c2 Hc2].
    { intros r0 Hin. apply Hr. right. exact Hin. }
    { lia. }
    exists ((2 * s + 3) + c2).
    cbn [map length rsum].
    replace (a + S (length rs)) with (S a + length rs) by lia.
    replace (s + (r + rsum rs)) with ((s + r) + rsum rs) by lia.
    rewrite run_split. rewrite H1. exact Hc2.
Qed.

Lemma map_repeat_2 : forall m,
  map (fun r => (1, r)) (repeat 2 m) = repeat (1, 2) m.
Proof.
  induction m as [|m IH]; [reflexivity |].
  cbn [repeat map]. rewrite IH. reflexivity.
Qed.

Lemma rsum_repeat_2 : forall m, rsum (repeat 2 m) = 2 * m.
Proof.
  induction m as [|m IH]; [reflexivity |].
  cbn [repeat rsum]. rewrite IH. lia.
Qed.

(* ----------------------------------------------------------------- *)
(* ERA_LAW: the settled era (rho = 29)                               *)
(* ----------------------------------------------------------------- *)

Lemma ERA_LAW : forall n, 1 <= n -> exists (cost : nat) (c : config),
  run cost (csec 16 29 2 ((1, 1) :: repeat (1, 2) (n - 1)) 1) = Some c
  /\ cfg_sim c (rcsec (false :: repeat true (n + 17) ++ []) (2*n + 32)
                     [(1, 2)]).
Proof.
  intros n Hn.
  (* 1. GRIND(29): the opening grind *)
  destruct (GRIND 13 16 ((1, 1) :: repeat (1, 2) (n - 1)) 1 ltac:(lia))
    as [c1 Hc1].
  replace (2 * 13 + 3) with 29 in Hc1 by lia.
  replace (2 * 13 + 6) with 32 in Hc1 by lia.
  (* 2. POP_CHAIN over the canonical stack: s1 = 2n + 31 *)
  assert (Hpairs : (1, 1) :: repeat (1, 2) (n - 1)
                   = map (fun r => (1, r)) (1 :: repeat 2 (n - 1))).
  { cbn [map]. rewrite map_repeat_2. reflexivity. }
  rewrite Hpairs in Hc1.
  assert (Hin : forall r, In r (1 :: repeat 2 (n - 1)) -> 1 <= r).
  { intros r [-> | Hin]; [lia |].
    apply repeat_spec in Hin. lia. }
  destruct (POP_CHAIN (1 :: repeat 2 (n - 1)) 16 32 1 Hin ltac:(lia))
    as [c2 Hc2].
  cbn [length] in Hc2.
  rewrite repeat_length in Hc2.
  cbn [rsum] in Hc2. rewrite rsum_repeat_2 in Hc2.
  replace (16 + S (n - 1)) with (n + 16) in Hc2 by lia.
  replace (32 + (1 + 2 * (n - 1))) with (2*n + 31) in Hc2 by lia.
  (* 3. REGEN *)
  pose proof (REGEN (n + 16) (2*n + 31) ltac:(lia)) as Hc3eq.
  (* the REGEN landing, transferred to the clean csec form *)
  assert (Hsim3 : cfg_sim (csecR (n + 16) (2*n + 31 - 1) [false])
                          (csec (n + 16) 1 2 [] (2*n + 30))).
  { split; [reflexivity |].
    intros p.
    replace (2*n + 31 - 1) with (S (2*n + 29)) by lia.
    replace (2*n + 30) with (S (2*n + 29)) by lia.
    apply REGEN_tape. }
  (* 4. TDN into the Stage-A era *)
  assert (H4 : run 6 (csec (n + 16) 1 2 [] (2*n + 30))
               = Some (bsec (n + 16) 1 4 [] (2*n + 30))) by apply TDN.
  destruct (run_sim_transfer _ _ _ _ Hsim3 H4) as [c4 [Hc4 Hs4]].
  (* 5. the Stage-A era: s + G = 2n + 34, G even, down to G = 2 *)
  assert (Hiter : forall j k, k + j = n + 14 ->
    exists c, run c (bsec (n + 16) 1 (4 + 2*k) [] (2*n + 30 - 2*k))
      = Some (bsec (n + 16) 1 (2*n + 32) [] 2)).
  { induction j as [|j IHj]; intros k Hk.
    - exists 0.
      replace (4 + 2*k) with (2*n + 32) by lia.
      replace (2*n + 30 - 2*k) with 2 by lia.
      reflexivity.
    - assert (Hsa : run (2 * (4 + 2*k) + 6)
                    (bsec (n + 16) 1 (4 + 2*k) [] (2*n + 30 - 2*k))
                    = Some (csec (n + 16) (4 + 2*k - 1) 2 []
                                 (2*n + 30 - 2*k - 2))).
      { apply StageA; lia. }
      replace (4 + 2*k - 1) with (2*k + 3) in Hsa by lia.
      replace (2*n + 30 - 2*k - 2) with (2*n + 28 - 2*k) in Hsa by lia.
      destruct (GRIND k (n + 16) [] (2*n + 28 - 2*k) ltac:(lia))
        as [cg Hg].
      destruct (IHj (k + 1) ltac:(lia)) as [c5 Hc5].
      replace (4 + 2*(k + 1)) with (2*k + 6) in Hc5 by lia.
      replace (2*n + 30 - 2*(k + 1)) with (2*n + 28 - 2*k) in Hc5 by lia.
      exists ((2 * (4 + 2*k) + 6) + (cg + c5)).
      rewrite run_split. rewrite Hsa.
      rewrite run_split. rewrite Hg. exact Hc5. }
  destruct (Hiter (n + 14) 0 ltac:(lia)) as [c6 Hc6].
  replace (4 + 2*0) with 4 in Hc6 by lia.
  replace (2*n + 30 - 2*0) with (2*n + 30) in Hc6 by lia.
  (* compose 4+5 across the sim Hs4 *)
  destruct (run_sim_transfer _ _ _ _ Hs4 Hc6) as [c7 [Hc7 Hs7]].
  (* 6. ENTRY_gen at P0 = [] *)
  assert (H8 : run (2*n + 44) (entry_src_gen [] (n + 16) (2*n + 32))
               = Some (entry_tgt_gen [] (n + 16) (2*n + 32))).
  { replace (2*n + 44) with (S (2*n + 31) + 12) by lia.
    replace (2*n + 32) with (S (2*n + 31)) by lia.
    apply ENTRY_gen. }
  rewrite bsec_entry_src in H8.
  destruct (run_sim_transfer _ _ _ _ Hs7 H8) as [c8 [Hc8 Hs8]].
  (* the TDN + era segment as one run from the REGEN landing *)
  assert (Hc47 : run (6 + c6) (csecR (n + 16) (2*n + 31 - 1) [false])
                 = Some c7).
  { rewrite run_split. rewrite Hc4. exact Hc7. }
  (* compose everything *)
  exists (c1 + (c2 + (4 * (2*n + 31) + 22 + ((6 + c6) + (2*n + 44))))).
  exists c8. split.
  - rewrite Hpairs.
    rewrite (run_split c1 (c2 + (4 * (2*n + 31) + 22 + ((6 + c6) + (2*n + 44))))).
    rewrite Hc1.
    rewrite (run_split c2 (4 * (2*n + 31) + 22 + ((6 + c6) + (2*n + 44)))).
    rewrite Hc2.
    rewrite (run_split (4 * (2*n + 31) + 22) ((6 + c6) + (2*n + 44))).
    rewrite Hc3eq.
    rewrite (run_split (6 + c6) (2*n + 44)).
    rewrite Hc47. exact Hc8.
  - replace (n + 17) with (S (n + 16)) by lia.
    eapply cfg_sim_trans; [exact Hs8 |].
    apply entry_gen_sim.
Qed.

(* ----------------------------------------------------------------- *)
(* Axiom audit                                                       *)
(* ----------------------------------------------------------------- *)

Print Assumptions ENTRY_gen.
Print Assumptions GRIND.
Print Assumptions POP_CHAIN.
Print Assumptions ERA_LAW.
