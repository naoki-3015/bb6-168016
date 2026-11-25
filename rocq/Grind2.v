(* ================================================================= *)
(*  Grind2.v -- Phase 29: the G'' endpoint induction (clean and     *)
(*  deviated regimes), the ESC grind endpoint for R <= 10, the      *)
(*  frame-general REGEN, the era tail over an abstract frame, and   *)
(*  the ESC-era law beta_next = 2*beta + 4 for R in {2,4,6,8,10}.   *)
(*                                                                  *)
(*  Obligation map (mechanisation-status.md, Phase 28):             *)
(*   (b) iterating the grind prefix through the B-phase to the      *)
(*       transfer source: GG_clean (clean regime, any frame),       *)
(*       ESC_GRIND_10 (the deviated round at a2 = 3).               *)
(*   (c) the post-PUSHX re-basing: inside the proved regime the     *)
(*       only PUSHX is hGRIND_dev's base step; its continuation     *)
(*       is the deviated grind itself (hGRIND_dev), NOT a finite    *)
(*       check -- the R >= 12 re-basing segment stays fenced.       *)
(*   (a) era stack-invariant preservation / Predecessor Lemma:      *)
(*       grind_inv + PRED_inv + PUSHX_only below, with the          *)
(*       invariant threaded through the grind chains (Part 6).      *)
(*                                                                  *)
(*  All section forms were pre-verified against phase21_model.py    *)
(*  and phase20_grind.py before proving (Phase 29 exploration):     *)
(*  the round decomposition of the clean grind, GRIND_dev(t)'s      *)
(*  (+1,+1)-shifted landing at the boundary frame a2 = t, and the   *)
(*  transfer/tail bookkeeping s_regen = 2*beta + 1.                 *)
(* ================================================================= *)

Require Import List Bool Arith Lia ZArith.
Import ListNotations.
Require Import TM Sections Mirror TokenPass Recoord Era Esc Grind Dev.

(* Section-equality tactic: decompose constructors with f_equal,   *)
(* but always try lia/reflexivity first so arithmetic subterms     *)
(* are closed by lia instead of being peeled apart.                *)
Ltac sec_eq := repeat (first [ solve [reflexivity] | solve [lia] | f_equal ]).

(* ================================================================= *)
(*  Part 1: hGRIND -- the word-level Grind Lemma G'                  *)
(*  (transplant of Era.GRIND to the hybrid word model).              *)
(*  Floor t + 1 <= a2: the dip of GRIND(t) reaches PUSH at           *)
(*  a = a2 - t >= 2, so no deviation fires.                          *)
(* ================================================================= *)

Lemma hGRIND : forall t pb a2 P G, t + 1 <= a2 ->
  hsteps (HC pb a2 (2*t + 3) 2 P G) (HB pb a2 1 (2*t + 6) P G).
Proof.
  induction t as [t IH] using lt_wf_ind.
  intros pb a2 P G Hfloor.
  destruct t as [|u].
  - destruct a2 as [|a2']; try lia.
    replace (2 * 0 + 3) with 3 by lia.
    replace (2 * 0 + 6) with 6 by lia.
    apply (hsteps_step _ (HC pb a2' 1 2 ((1, 2) :: P) G)).
    { apply (hPUSH pb a2' 0 P G). }
    apply (hsteps_step _ (HB pb a2' 1 4 ((1, 2) :: P) G)).
    { apply hTDN. }
    apply (hsteps_step _ (HB pb (S a2') 1 6 P G)).
    { apply hPOP; lia. }
    apply hsteps_refl.
  - destruct a2 as [|a2']; try lia.
    assert (Hloop : forall k i,
      2*i + 3 + 2*k = 2 * S u + 1 -> i + 1 <= a2' ->
      hsteps (HC pb a2' (2*i + 3) 2
                 ((2 * S u + 2 - (2*i + 3), 2) :: P) G)
             (HC pb a2' (2 * S u + 1) 2 ((1, 2) :: P) G)).
    { induction k as [|k IHk]; intros i Hk Hi.
      - replace (2 * S u + 2 - (2*i + 3)) with 1 by lia.
        replace (2*i + 3) with (2 * S u + 1) by lia.
        apply hsteps_refl.
      - apply (hsteps_trans _
          (HB pb a2' 1 (2*i + 6)
              ((2 * S u + 2 - (2*i + 3), 2) :: P) G)).
        { apply (IH i ltac:(lia) pb a2'
                   ((2 * S u + 2 - (2*i + 3), 2) :: P) G Hi). }
        apply (hsteps_trans _
          (HC pb a2' (2*(i + 1) + 3) 2
              ((2 * S u + 2 - (2*(i + 1) + 3), 2) :: P) G)).
        + apply (hsteps_step _
            (HC pb a2' (2*(i + 1) + 3) 2
                ((2 * S u + 2 - (2*(i + 1) + 3), 2) :: P) G)).
          { replace (HB pb a2' 1 (2*i + 6)
                ((2 * S u + 2 - (2*i + 3), 2) :: P) G)
              with (HB pb a2' 1 (S (S (2*i + 4)))
                ((S (S (S (2*u - 2*i - 2))), 2) :: P) G)
              by sec_eq.
            replace (HC pb a2' (2*(i + 1) + 3) 2
                ((2 * S u + 2 - (2*(i + 1) + 3), 2) :: P) G)
              with (HC pb a2' (S (2*i + 4)) 2
                ((S (2*u - 2*i - 2), 2) :: P) G)
              by sec_eq.
            apply hTUP. }
          apply hsteps_refl.
        + apply IHk; lia. }
    apply (hsteps_trans _ (HC pb a2' 1 2 ((2 * S u + 1, 2) :: P) G)).
    { replace (HC pb (S a2') (2 * S u + 3) 2 P G)
        with (HC pb (S a2') (S (S (S (2 * S u)))) 2 P G)
        by sec_eq.
      replace (HC pb a2' 1 2 ((2 * S u + 1, 2) :: P) G)
        with (HC pb a2' 1 2 ((S (2 * S u), 2) :: P) G)
        by sec_eq.
      apply (hsteps_step _ (HC pb a2' 1 2 ((S (2 * S u), 2) :: P) G)).
      { apply hPUSH. }
      apply hsteps_refl. }
    apply (hsteps_trans _ (HB pb a2' 1 4 ((2 * S u + 1, 2) :: P) G)).
    { apply (hsteps_step _ (HB pb a2' 1 4 ((2 * S u + 1, 2) :: P) G)).
      { apply hTDN. }
      apply hsteps_refl. }
    apply (hsteps_trans _ (HC pb a2' 3 2 ((2 * S u - 1, 2) :: P) G)).
    { apply (hsteps_step _ (HC pb a2' 3 2 ((2 * S u - 1, 2) :: P) G)).
      { replace (HB pb a2' 1 4 ((2 * S u + 1, 2) :: P) G)
          with (HB pb a2' 1 (S (S 2)) ((S (S (S (2 * u))), 2) :: P) G)
          by sec_eq.
        replace (HC pb a2' 3 2 ((2 * S u - 1, 2) :: P) G)
          with (HC pb a2' (S 2) 2 ((S (2 * u), 2) :: P) G)
          by sec_eq.
        apply hTUP. }
      apply hsteps_refl. }
    apply (hsteps_trans _ (HC pb a2' (2 * S u + 1) 2 ((1, 2) :: P) G)).
    { pose proof (Hloop u 0 ltac:(lia) ltac:(lia)) as Hc4.
      replace (2 * S u + 2 - (2*0 + 3)) with (2 * S u - 1) in Hc4 by lia.
      replace (2*0 + 3) with 3 in Hc4 by lia.
      exact Hc4. }
    apply (hsteps_trans _ (HB pb a2' 1 (2 * S u + 4) ((1, 2) :: P) G)).
    { pose proof (IH u ltac:(lia) pb a2' ((1, 2) :: P) G ltac:(lia))
        as Hc5.
      replace (2*u + 3) with (2 * S u + 1) in Hc5 by lia.
      replace (2*u + 6) with (2 * S u + 4) in Hc5 by lia.
      exact Hc5. }
    apply (hsteps_step _ (HB pb (S a2') 1 (2 * S u + 6) P G)).
    { replace (2 * S u + 6) with ((2 * S u + 4) + 2) by lia.
      apply hPOP; lia. }
    replace (2 * S u + 6) with (2 * S u + 6) by lia.
    apply hsteps_refl.
Qed.

(* ================================================================= *)
(*  Part 2: hGRIND_dev -- the deviated Grind Lemma G' at the         *)
(*  boundary frame a2 = t (pb = []).  The recursion mirrors hGRIND   *)
(*  exactly, except the final spine call is GRIND_dev(t-1) instead   *)
(*  of GRIND(t-1); the base case is the single PUSHX step.  The      *)
(*  landing is shifted by (+1, +1) against the clean landing:       *)
(*    HC [] t (2t+3) 2 P G  ->  HB [] (t+1) 1 (2t+7) P G.            *)
(*  Verified against phase21_model.py at t = 0..3 (rule counts      *)
(*  1, 5, 13, 29 = 2^(t+2) - 3, exactly one PUSHX, on the final      *)
(*  spine, produced by a TUP at shuttle 4).                          *)
(* ================================================================= *)

Lemma hGRIND_dev : forall t P G,
  hsteps (HC [] t (2*t + 3) 2 P G) (HB [] (S t) 1 (2*t + 7) P G).
Proof.
  induction t as [t IH] using lt_wf_ind.
  intros P G.
  destruct t as [|u].
  - replace (2 * 0 + 3) with 3 by lia.
    replace (2 * 0 + 7) with 7 by lia.
    apply (hsteps_step _ (HB [] 1 1 7 P G)).
    { apply hPUSHX. }
    apply hsteps_refl.
  - assert (Hloop : forall k i,
      2*i + 3 + 2*k = 2 * S u + 1 -> i <= u ->
      hsteps (HC [] u (2*i + 3) 2
                 ((2 * S u + 2 - (2*i + 3), 2) :: P) G)
             (HC [] u (2 * S u + 1) 2 ((1, 2) :: P) G)).
    { induction k as [|k IHk]; intros i Hk Hi.
      - replace (2 * S u + 2 - (2*i + 3)) with 1 by lia.
        replace (2*i + 3) with (2 * S u + 1) by lia.
        apply hsteps_refl.
      - apply (hsteps_trans _
          (HB [] u 1 (2*i + 6)
              ((2 * S u + 2 - (2*i + 3), 2) :: P) G)).
        { apply (hGRIND i [] u
                   ((2 * S u + 2 - (2*i + 3), 2) :: P) G).
          lia. }
        apply (hsteps_trans _
          (HC [] u (2*(i + 1) + 3) 2
              ((2 * S u + 2 - (2*(i + 1) + 3), 2) :: P) G)).
        + apply (hsteps_step _
            (HC [] u (2*(i + 1) + 3) 2
                ((2 * S u + 2 - (2*(i + 1) + 3), 2) :: P) G)).
          { replace (HB [] u 1 (2*i + 6)
                ((2 * S u + 2 - (2*i + 3), 2) :: P) G)
              with (HB [] u 1 (S (S (2*i + 4)))
                ((S (S (S (2*u - 2*i - 2))), 2) :: P) G)
              by sec_eq.
            replace (HC [] u (2*(i + 1) + 3) 2
                ((2 * S u + 2 - (2*(i + 1) + 3), 2) :: P) G)
              with (HC [] u (S (2*i + 4)) 2
                ((S (2*u - 2*i - 2), 2) :: P) G)
              by sec_eq.
            apply hTUP. }
          apply hsteps_refl.
        + apply IHk; lia. }
    apply (hsteps_trans _ (HC [] u 1 2 ((2 * S u + 1, 2) :: P) G)).
    { replace (HC [] (S u) (2 * S u + 3) 2 P G)
        with (HC [] (S u) (S (S (S (2 * S u)))) 2 P G)
        by sec_eq.
      replace (HC [] u 1 2 ((2 * S u + 1, 2) :: P) G)
        with (HC [] u 1 2 ((S (2 * S u), 2) :: P) G)
        by sec_eq.
      apply (hsteps_step _ (HC [] u 1 2 ((S (2 * S u), 2) :: P) G)).
      { apply hPUSH. }
      apply hsteps_refl. }
    apply (hsteps_trans _ (HB [] u 1 4 ((2 * S u + 1, 2) :: P) G)).
    { apply (hsteps_step _ (HB [] u 1 4 ((2 * S u + 1, 2) :: P) G)).
      { apply hTDN. }
      apply hsteps_refl. }
    apply (hsteps_trans _ (HC [] u 3 2 ((2 * S u - 1, 2) :: P) G)).
    { apply (hsteps_step _ (HC [] u 3 2 ((2 * S u - 1, 2) :: P) G)).
      { replace (HB [] u 1 4 ((2 * S u + 1, 2) :: P) G)
          with (HB [] u 1 (S (S 2)) ((S (S (S (2 * u))), 2) :: P) G)
          by sec_eq.
        replace (HC [] u 3 2 ((2 * S u - 1, 2) :: P) G)
          with (HC [] u (S 2) 2 ((S (2 * u), 2) :: P) G)
          by sec_eq.
        apply hTUP. }
      apply hsteps_refl. }
    apply (hsteps_trans _ (HC [] u (2 * S u + 1) 2 ((1, 2) :: P) G)).
    { pose proof (Hloop u 0 ltac:(lia) ltac:(lia)) as Hc4.
      replace (2 * S u + 2 - (2*0 + 3)) with (2 * S u - 1) in Hc4 by lia.
      replace (2*0 + 3) with 3 in Hc4 by lia.
      exact Hc4. }
    apply (hsteps_trans _ (HB [] (S u) 1 (2*u + 7) ((1, 2) :: P) G)).
    { pose proof (IH u ltac:(lia) ((1, 2) :: P) G) as Hc5.
      replace (2*u + 3) with (2 * S u + 1) in Hc5 by lia.
      exact Hc5. }
    apply (hsteps_step _ (HB [] (S (S u)) 1 (2 * S u + 7) P G)).
    { replace (2 * S u + 7) with ((2*u + 7) + 2) by lia.
      apply hPOP; lia. }
    apply hsteps_refl.
Qed.

(* ================================================================= *)
(*  Part 3: the clean G'' endpoint (obligation (b), clean regime).   *)
(*  Round j+1 = TUP + GRIND(j+1) on the residue pair; the prefix     *)
(*  is Grind.v's grind_prefix.  Floor: rounds j <= m need            *)
(*  j + 1 <= a2, i.e. m + 1 <= a2 for GG_clean (R = 2m + 4).          *)
(* ================================================================= *)

Lemma grind_round : forall j pb a2 g P G, j + 1 <= a2 -> 3 <= g ->
  hsteps (HB pb a2 1 (2*j + 4) ((g, 2) :: P) G)
         (HB pb a2 1 (2*j + 6) ((g - 2, 2) :: P) G).
Proof.
  intros j pb a2 g P G Hj Hg.
  apply (hsteps_trans _ (HC pb a2 (2*j + 3) 2 ((g - 2, 2) :: P) G)).
  - apply (hsteps_step _ (HC pb a2 (2*j + 3) 2 ((g - 2, 2) :: P) G)).
    { replace (HB pb a2 1 (2*j + 4) ((g, 2) :: P) G)
        with (HB pb a2 1 (S (S (2*j + 2)))
                 ((S (S (S (g - 3))), 2) :: P) G)
        by sec_eq.
      replace (HC pb a2 (2*j + 3) 2 ((g - 2, 2) :: P) G)
        with (HC pb a2 (S (2*j + 2)) 2 ((S (g - 3), 2) :: P) G)
        by sec_eq.
      apply hTUP. }
    apply hsteps_refl.
  - apply hGRIND; exact Hj.
Qed.

Lemma GG_rounds : forall m j0 pb a2 P G, j0 + m + 1 <= a2 ->
  hsteps (HB pb a2 1 (2*j0 + 6) ((2*m + 2, 2) :: P) G)
         (HB pb a2 1 (2*(j0 + m) + 6) ((2, 2) :: P) G).
Proof.
  induction m as [|m IH]; intros j0 pb a2 P G Hf.
  - replace (2 * (j0 + 0) + 6) with (2*j0 + 6) by lia.
    replace (2 * 0 + 2) with 2 by lia.
    apply hsteps_refl.
  - apply (hsteps_trans _
      (HB pb a2 1 (2*(j0 + 1) + 6) ((2*m + 2, 2) :: P) G)).
    + replace (HB pb a2 1 (2*j0 + 6) ((2 * S m + 2, 2) :: P) G)
        with (HB pb a2 1 (2*(j0 + 1) + 4) ((2*m + 4, 2) :: P) G)
        by sec_eq.
      replace (HB pb a2 1 (2*(j0 + 1) + 6) ((2*m + 2, 2) :: P) G)
        with (HB pb a2 1 (2*(j0 + 1) + 6) ((2*m + 4 - 2, 2) :: P) G)
        by sec_eq.
      apply grind_round; lia.
    + replace (HB pb a2 1 (2*(j0 + S m) + 6) ((2, 2) :: P) G)
        with (HB pb a2 1 (2*((j0 + 1) + m) + 6) ((2, 2) :: P) G)
        by sec_eq.
      apply IH. lia.
Qed.

Lemma GG_clean : forall m pb a2 P G, m + 1 <= a2 ->
  hsteps (HC pb a2 1 2 ((2*m + 4, 2) :: P) G)
         (HB pb a2 1 (2*m + 6) ((2, 2) :: P) G).
Proof.
  intros m pb a2 P G Hf. destruct a2 as [|a2']; try lia.
  apply (hsteps_trans _ (HB pb (S a2') 1 6 ((2*m + 2, 2) :: P) G)).
  - replace (HC pb (S a2') 1 2 ((2*m + 4, 2) :: P) G)
      with (HC pb (S a2') 1 2 ((S (S (S (2*m + 1))), 2) :: P) G)
      by sec_eq.
    replace (HB pb (S a2') 1 6 ((2*m + 2, 2) :: P) G)
      with (HB pb (S a2') 1 6 ((S (2*m + 1), 2) :: P) G)
      by sec_eq.
    apply grind_prefix.
  - replace (HB pb (S a2') 1 6 ((2*m + 2, 2) :: P) G)
      with (HB pb (S a2') 1 (2*0 + 6) ((2*m + 2, 2) :: P) G)
      by sec_eq.
    replace (HB pb (S a2') 1 (2*m + 6) ((2, 2) :: P) G)
      with (HB pb (S a2') 1 (2*(0 + m) + 6) ((2, 2) :: P) G)
      by sec_eq.
    apply GG_rounds. lia.
Qed.

(* ================================================================= *)
(*  Part 4: the R = 10 ESC grind (a2 = 3): rounds 1-2 clean,         *)
(*  round 3 = TUP + GRIND_dev(3); the (+1,+1) shift of the           *)
(*  deviated landing is absorbed by the tail (Part 5).               *)
(* ================================================================= *)

Lemma ESC_GRIND_10 : forall P G,
  hsteps (HC [] 3 1 2 ((10, 2) :: P) G)
         (HB [] 4 1 13 ((2, 2) :: P) G).
Proof.
  intros P G.
  apply (hsteps_trans _ (HB [] 3 1 10 ((4, 2) :: P) G)).
  - apply (hsteps_trans _ (HB [] 3 1 6 ((8, 2) :: P) G)).
    + replace (HC [] 3 1 2 ((10, 2) :: P) G)
        with (HC [] 3 1 2 ((S (S (S 7)), 2) :: P) G)
        by sec_eq.
      replace (HB [] 3 1 6 ((8, 2) :: P) G)
        with (HB [] 3 1 6 ((S 7, 2) :: P) G)
        by sec_eq.
      apply grind_prefix.
    + apply (hsteps_trans _ (HB [] 3 1 8 ((6, 2) :: P) G)).
      * replace (HB [] 3 1 6 ((8, 2) :: P) G)
          with (HB [] 3 1 (2*1 + 4) ((8, 2) :: P) G)
          by sec_eq.
        replace (HB [] 3 1 8 ((6, 2) :: P) G)
          with (HB [] 3 1 (2*1 + 6) ((8 - 2, 2) :: P) G)
          by sec_eq.
        apply grind_round; lia.
      * replace (HB [] 3 1 8 ((6, 2) :: P) G)
          with (HB [] 3 1 (2*2 + 4) ((6, 2) :: P) G)
          by sec_eq.
        replace (HB [] 3 1 10 ((4, 2) :: P) G)
          with (HB [] 3 1 (2*2 + 6) ((6 - 2, 2) :: P) G)
          by sec_eq.
        apply grind_round; lia.
  - apply (hsteps_trans _ (HC [] 3 9 2 ((2, 2) :: P) G)).
    + apply (hsteps_step _ (HC [] 3 9 2 ((2, 2) :: P) G)).
      { replace (HB [] 3 1 10 ((4, 2) :: P) G)
          with (HB [] 3 1 (S (S 8)) ((S (S (S 1)), 2) :: P) G)
          by sec_eq.
        replace (HC [] 3 9 2 ((2, 2) :: P) G)
          with (HC [] 3 (S 8) 2 ((S 1, 2) :: P) G)
          by sec_eq.
        apply hTUP. }
      apply hsteps_refl.
    + replace (HC [] 3 9 2 ((2, 2) :: P) G)
        with (HC [] 3 (2*3 + 3) 2 ((2, 2) :: P) G)
        by sec_eq.
      replace (HB [] 4 1 13 ((2, 2) :: P) G)
        with (HB [] (S 3) 1 (2*3 + 7) ((2, 2) :: P) G)
        by sec_eq.
      apply hGRIND_dev.
Qed.

(* ================================================================= *)
(*  Part 5: the transfer tail and the ESC grind endpoint.            *)
(*  POP2 (word form hTRANS2_1) consumes ((2,2),(1,1)); the POP       *)
(*  chain over (1,2)^(beta-1) lands on the REGEN source with         *)
(*  s_regen = 2*beta + 1 at frame (S a :: pb), a_final = s + beta.   *)
(* ================================================================= *)

Lemma pop_chain_h : forall m pb a s G, 2 <= s ->
  hsteps (HB pb a 1 s (repeat (1, 2) m) G)
         (HB pb (a + m) 1 (s + 2*m) [] G).
Proof.
  induction m as [|m IH]; intros pb a s G Hs.
  - cbn [repeat].
    replace (a + 0) with a by lia.
    replace (s + 2 * 0) with s by lia.
    apply hsteps_refl.
  - cbn [repeat].
    apply (hsteps_trans _ (HB pb (S a) 1 (s + 2) (repeat (1, 2) m) G)).
    + apply (hsteps_step _ (HB pb (S a) 1 (s + 2) (repeat (1, 2) m) G)).
      { apply hPOP; lia. }
      apply hsteps_refl.
    + replace (HB pb (a + S m) 1 (s + 2 * S m) [] G)
        with (HB pb (S a + m) 1 (s + 2 + 2 * m) [] G)
        by sec_eq.
      apply IH. lia.
Qed.

Lemma TAIL : forall pb a s beta, 1 <= beta -> 1 <= s ->
  hsteps (HB pb a 1 s ((2, 2) :: (1, 1) :: repeat (1, 2) (beta - 1)) 1)
         (HB (S a :: pb) (s + beta) 1 (2 * beta + 1) [] 1).
Proof.
  intros pb a s beta Hb Hs.
  apply (hsteps_trans _
    (HB (S a :: pb) (s + 1) 1 3 (repeat (1, 2) (beta - 1)) 1)).
  - apply (hsteps_step _
      (HB (S a :: pb) (s + 1) 1 3 (repeat (1, 2) (beta - 1)) 1)).
    { replace (HB pb a 1 s ((2, 2) :: (1, 1) :: repeat (1, 2) (beta - 1)) 1)
        with (HB pb a 1 (S (s - 1))
                 ((2, S 1) :: (1, 1) :: repeat (1, 2) (beta - 1)) 1)
        by sec_eq.
      replace (HB (S a :: pb) (s + 1) 1 3 (repeat (1, 2) (beta - 1)) 1)
        with (HB (S a :: pb) (S (S (s - 1))) 1 (S 1 + 1)
                 (repeat (1, 2) (beta - 1)) 1)
        by sec_eq.
      apply hTRANS2_1; lia. }
    apply hsteps_refl.
  - replace (HB (S a :: pb) (s + beta) 1 (2 * beta + 1) [] 1)
      with (HB (S a :: pb) (s + 1 + (beta - 1)) 1
               (3 + 2 * (beta - 1)) [] 1)
      by sec_eq.
    apply pop_chain_h; lia.
Qed.

Lemma ESC_TO_REGEN : forall R beta,
  (R = 2 \/ R = 4 \/ R = 6 \/ R = 8 \/ R = 10) -> 2 <= beta ->
  exists pb a,
    hsteps (HC [] 3 1 2 ((R, 2) :: (1, 1) :: repeat (1, 2) (beta - 1)) 1)
           (HB pb a 1 (2 * beta + 1) [] 1)
    /\ beta <= a.
Proof.
  intros R beta HR Hb.
  destruct HR as [E|[E|[E|[E|E]]]]; subst R.
  - exists [4], (4 + beta). split; [| lia].
    apply (hsteps_trans _
      (HB [] 3 1 4 ((2, 2) :: (1, 1) :: repeat (1, 2) (beta - 1)) 1)).
    + apply (hsteps_step _
        (HB [] 3 1 4 ((2, 2) :: (1, 1) :: repeat (1, 2) (beta - 1)) 1)).
      { apply hTDN. }
      apply hsteps_refl.
    + apply TAIL; lia.
  - exists [4], (6 + beta). split; [| lia].
    apply (hsteps_trans _
      (HB [] 3 1 6 ((2, 2) :: (1, 1) :: repeat (1, 2) (beta - 1)) 1)).
    + replace (HC [] 3 1 2 ((4, 2) :: (1, 1) :: repeat (1, 2) (beta - 1)) 1)
        with (HC [] 3 1 2 ((2*0 + 4, 2) :: (1, 1) :: repeat (1, 2) (beta - 1)) 1)
        by sec_eq.
      replace (HB [] 3 1 6 ((2, 2) :: (1, 1) :: repeat (1, 2) (beta - 1)) 1)
        with (HB [] 3 1 (2*0 + 6) ((2, 2) :: (1, 1) :: repeat (1, 2) (beta - 1)) 1)
        by sec_eq.
      apply GG_clean; lia.
    + apply TAIL; lia.
  - exists [4], (8 + beta). split; [| lia].
    apply (hsteps_trans _
      (HB [] 3 1 8 ((2, 2) :: (1, 1) :: repeat (1, 2) (beta - 1)) 1)).
    + replace (HC [] 3 1 2 ((6, 2) :: (1, 1) :: repeat (1, 2) (beta - 1)) 1)
        with (HC [] 3 1 2 ((2*1 + 4, 2) :: (1, 1) :: repeat (1, 2) (beta - 1)) 1)
        by sec_eq.
      replace (HB [] 3 1 8 ((2, 2) :: (1, 1) :: repeat (1, 2) (beta - 1)) 1)
        with (HB [] 3 1 (2*1 + 6) ((2, 2) :: (1, 1) :: repeat (1, 2) (beta - 1)) 1)
        by sec_eq.
      apply GG_clean; lia.
    + apply TAIL; lia.
  - exists [4], (10 + beta). split; [| lia].
    apply (hsteps_trans _
      (HB [] 3 1 10 ((2, 2) :: (1, 1) :: repeat (1, 2) (beta - 1)) 1)).
    + replace (HC [] 3 1 2 ((8, 2) :: (1, 1) :: repeat (1, 2) (beta - 1)) 1)
        with (HC [] 3 1 2 ((2*2 + 4, 2) :: (1, 1) :: repeat (1, 2) (beta - 1)) 1)
        by sec_eq.
      replace (HB [] 3 1 10 ((2, 2) :: (1, 1) :: repeat (1, 2) (beta - 1)) 1)
        with (HB [] 3 1 (2*2 + 6) ((2, 2) :: (1, 1) :: repeat (1, 2) (beta - 1)) 1)
        by sec_eq.
      apply GG_clean; lia.
    + apply TAIL; lia.
  - exists [5], (13 + beta). split; [| lia].
    apply (hsteps_trans _
      (HB [] 4 1 13 ((2, 2) :: (1, 1) :: repeat (1, 2) (beta - 1)) 1)).
    + apply ESC_GRIND_10.
    + apply TAIL; lia.
Qed.

(* ================================================================= *)
(*  Part 6: REGEN over an abstract frozen prefix (gbsec forms).      *)
(*  Sections.REGEN is the pb = [] case; the ESC era tail needs the   *)
(*  same step list over gbsec P (POP_terminal + StageA_blank +       *)
(*  PUSH_T, each ported).  The landing gcsecR carries one            *)
(*  materialised trailing blank, exactly as in Sections.             *)
(* ================================================================= *)

Definition gbsec_open (P : list sym) (a g0 s : nat) : config :=
  mkCfg SB (repeat true a ++ P) (repeat false g0 ++ repeat true s).

Definition gcsecT (P : list sym) (a2 g0 : nat) (r : list sym) : config :=
  mkCfg SC (repeat true a2 ++ P)
    (true :: true :: (repeat false g0 ++ (true :: true :: r))).

Definition gcsecR (P : list sym) (a2 G : nat) (r : list sym) : config :=
  mkCfg SC (repeat true a2 ++ P)
    (true :: true :: (repeat false 1 ++
       (repeat true 2 ++ (repeat false G ++ (true :: true :: r))))).

Lemma popT_prefix_gen : forall P a s',
  run (S s' + 2) (gbsec P a 1 (S s') [] 1) =
  Some (mkCfg SB (repeat true (S s') ++ (false :: repeat true (S a) ++ P))
                 [true; true]).
Proof.
  intros P a s'.
  replace (S s' + 2) with (2 + (s' + 1)) by lia.
  rewrite run_split.
  assert (H2 : run 2 (gbsec P a 1 (S s') [] 1) =
    Some (mkCfg SA (false :: repeat true (S a) ++ P)
           (repeat true s' ++ [false; true; true]))).
  { reflexivity. }
  rewrite H2. cbv beta iota.
  rewrite run_split.
  rewrite sweepA. cbv beta iota.
  reflexivity.
Qed.

Lemma popT_sweep_gen : forall P a s'',
  run (S (S s'') + 1)
    (mkCfg SB (repeat true (S (S s'')) ++ (false :: repeat true (S a) ++ P))
              [true; true]) =
  Some (gbsec_open P (S a) 1 (S (S s'') + 2)).
Proof.
  intros P a s''.
  replace (S (S s'') + 1) with (1 + (S s'' + 1)) by lia.
  rewrite run_split.
  assert (H1 : run 1
    (mkCfg SB (repeat true (S (S s'')) ++ (false :: repeat true (S a) ++ P))
              [true; true]) =
    Some (mkCfg SB (repeat true (S s'') ++ (false :: repeat true (S a) ++ P))
              [true; true; true])).
  { reflexivity. }
  rewrite H1. cbv beta iota.
  rewrite run_split.
  rewrite sweepB. cbv beta iota.
  rewrite run_1.
  assert (Hstep : step (mkCfg SB (false :: repeat true (S a) ++ P)
                        (repeat true (S s'') ++ [true; true; true])) =
    Some (mkCfg SB (repeat true (S a) ++ P)
           (false :: true :: (repeat true s'' ++ [true; true; true])))).
  { reflexivity. }
  rewrite Hstep.
  unfold gbsec_open.
  replace (S (S s'') + 2) with (S (s'' + 3)) by lia.
  change (repeat true (S (s'' + 3)))
    with (true :: repeat true (s'' + 3)).
  rewrite repT_snoc3. reflexivity.
Qed.

Lemma POP_terminal_gen : forall P a s, 2 <= s ->
  run (2 * s + 3) (gbsec P a 1 s [] 1) =
  Some (gbsec_open P (S a) 1 (s + 2)).
Proof.
  intros P a s Hs. destruct s as [| [| s'']]; try lia.
  replace (2 * S (S s'') + 3) with ((S (S s'') + 2) + (S (S s'') + 1))
    by lia.
  rewrite run_split.
  rewrite popT_prefix_gen.
  exact (popT_sweep_gen P a s'').
Qed.

Lemma stageAblank_prefix_gen : forall P A L',
  run 2 (gbsec_open P A 1 (S L')) =
  Some (mkCfg SA (false :: repeat true (S A) ++ P) (repeat true L')).
Proof. intros. reflexivity. Qed.

Lemma StageA_blank_gen : forall P A L, 2 <= L ->
  run (2 * L + 6) (gbsec_open P A 1 L) =
  Some (gcsecT P A (L - 1) [false]).
Proof.
  intros P A L HL. destruct L as [| [| L'']]; try lia.
  replace (2 * S (S L'') + 6) with (2 + (S L'' + (5 + (L'' + 2))))
    by lia.
  replace (S (S L'') - 1) with (S L'') by lia.
  rewrite run_split.
  rewrite stageAblank_prefix_gen. cbv beta iota.
  rewrite <- (app_nil_r (repeat true (S L''))).
  rewrite run_split.
  rewrite sweepA. cbv beta iota.
  rewrite run_split.
  change (run 5
    (mkCfg SA (repeat true (S L'') ++ (false :: repeat true (S A) ++ P)) []))
    with (Some (mkCfg SF (repeat true L'' ++ (false :: repeat true (S A) ++ P))
                 [true; true; true; false])).
  cbv beta iota.
  rewrite run_split.
  rewrite sweepF. cbv beta iota.
  reflexivity.
Qed.

Lemma PUSH_T_gen : forall P a2' g'' r,
  run 9 (gcsecT P (S a2') (S (S (S g''))) r) =
  Some (gcsecR P a2' (S g'') r).
Proof. intros. reflexivity. Qed.

Lemma REGEN_gen : forall P a s, 2 <= s ->
  run (4 * s + 22) (gbsec P a 1 s [] 1) =
  Some (gcsecR P a (s - 1) [false]).
Proof.
  intros P a s Hs. destruct s as [| [| s2]]; try lia.
  replace (4 * S (S s2) + 22)
    with ((2 * S (S s2) + 3) + ((2 * (S (S s2) + 2) + 6) + 9)) by lia.
  rewrite run_split.
  rewrite (POP_terminal_gen P a (S (S s2)) Hs).
  rewrite run_split.
  rewrite (StageA_blank_gen P (S a) (S (S s2) + 2)).
  - replace (S (S s2) + 2 - 1) with (S (S (S s2))) by lia.
    replace (S (S s2) - 1) with (S s2) by lia.
    exact (PUSH_T_gen P a s2 [false]).
  - lia.
Qed.

Lemma nth_app_false_g : forall (l : list sym) i,
  nth i (l ++ [false]) false = nth i l false.
Proof.
  induction l as [| x t IH]; intros i.
  - destruct i as [| [| i']]; reflexivity.
  - destruct i; simpl; [reflexivity | apply IH].
Qed.

Lemma REGEN_gen_sim : forall P a G,
  cfg_sim (gcsecR P a G [false]) (gcsec P a 1 2 [] G).
Proof.
  intros P a G. split; [reflexivity |].
  intros p. unfold tape_of.
  assert (E : cright (gcsecR P a G [false]) =
              cright (gcsec P a 1 2 [] G) ++ [false]).
  { unfold gcsecR, gcsec, tail. simpl. rewrite <- !app_assoc.
    reflexivity. }
  destruct (Z_le_dec 0 p).
  - rewrite E. apply nth_app_false_g.
  - reflexivity.
Qed.

(* ================================================================= *)
(*  Part 7: the era tail over an abstract frame, and the ESC-era     *)
(*  law.  From the REGEN source HB pb a 1 (2*beta+1) [] 1 with       *)
(*  beta - 1 <= a (the era grinds' floor), REGEN_gen + TDN + the     *)
(*  Stage-A era loop (era_cycle: STGA + hGRIND) reach the ENTRY      *)
(*  source at s = 2*beta + 2; ENTRY_gen lands on the mirror          *)
(*  section with b2 = 2*beta + 2, i.e. beta_next = 2*beta + 4 in     *)
(*  the rcsec convention (beta = b2 + 2), mirroring Era.ERA_LAW.     *)
(* ================================================================= *)

Lemma entry_src_gen_hcfg : forall pb a s,
  entry_src_gen (enc pb) a s = hcfg (HB pb a 1 s [] 2).
Proof.
  intros pb a s. unfold entry_src_gen, hcfg, gbsec, tail.
  reflexivity.
Qed.

Lemma era_cycle : forall j pb a G, j + 1 <= a -> 1 <= G ->
  hsteps (HB pb a 1 (2*j + 4) [] (G + 2)) (HB pb a 1 (2*j + 6) [] G).
Proof.
  intros j pb a G Hj HG.
  apply (hsteps_trans _ (HC pb a (2*j + 4 - 1) 2 [] (G + 2 - 2))).
  - apply (hsteps_step _ (HC pb a (2*j + 4 - 1) 2 [] (G + 2 - 2))).
    { apply hSTGA; lia. }
    apply hsteps_refl.
  - replace (HC pb a (2*j + 4 - 1) 2 [] (G + 2 - 2))
      with (HC pb a (2*j + 3) 2 [] G) by sec_eq.
    apply hGRIND; exact Hj.
Qed.

Lemma era_loop : forall m pb a beta, m <= beta - 1 -> beta - 1 <= a ->
  hsteps (HB pb a 1 4 [] (2 * beta))
         (HB pb a 1 (2*m + 4) [] (2 * beta - 2 * m)).
Proof.
  induction m as [|m IH]; intros pb a beta Hm Ha.
  - replace (2 * 0 + 4) with 4 by lia.
    replace (2 * beta - 2 * 0) with (2 * beta) by lia.
    apply hsteps_refl.
  - apply (hsteps_trans _ (HB pb a 1 (2*m + 4) [] (2 * beta - 2 * m))).
    + apply IH; lia.
    + replace (HB pb a 1 (2*m + 4) [] (2 * beta - 2 * m))
        with (HB pb a 1 (2*m + 4) [] ((2 * beta - 2 * S m) + 2)) by sec_eq.
      replace (HB pb a 1 (2 * S m + 4) [] (2 * beta - 2 * S m))
        with (HB pb a 1 (2*m + 6) [] (2 * beta - 2 * S m)) by sec_eq.
      apply era_cycle; lia.
Qed.

Lemma ERA_TAIL : forall pb a beta, 2 <= beta -> beta - 1 <= a ->
  exists n c, run n (hcfg (HB pb a 1 (2 * beta + 1) [] 1)) = Some c
    /\ cfg_sim c (rcsec (false :: repeat true (S a) ++ enc pb)
                        (2 * beta + 2) [(1, 2)]).
Proof.
  intros pb a beta Hb Ha.
  pose proof (REGEN_gen (enc pb) a (2 * beta + 1) ltac:(lia)) as Hregen.
  replace (2 * beta + 1 - 1) with (2 * beta) in Hregen by lia.
  assert (Hchain : hsteps (HC pb a 1 2 [] (2 * beta))
                          (HB pb a 1 (2 * beta + 2) [] 2)).
  { apply (hsteps_trans _ (HB pb a 1 4 [] (2 * beta))).
    - apply (hsteps_step _ (HB pb a 1 4 [] (2 * beta))).
      { apply hTDN. }
      apply hsteps_refl.
    - replace (HB pb a 1 (2 * beta + 2) [] 2)
        with (HB pb a 1 (2 * (beta - 1) + 4) []
                 (2 * beta - 2 * (beta - 1)))
        by sec_eq.
      apply era_loop; lia. }
  destruct (hsteps_sound _ _ Hchain) as [n2 [c2 [Hr2 Hs2]]].
  pose proof (REGEN_gen_sim (enc pb) a (2 * beta)) as Hsim1.
  destruct (run_sim_transfer n2 (gcsecR (enc pb) a (2 * beta) [false])
              (hcfg (HC pb a 1 2 [] (2 * beta))) c2 Hsim1 Hr2)
    as [c2' [Hr2' Hs2']].
  pose proof (ENTRY_gen (enc pb) a (2 * beta + 1)) as Hentry.
  rewrite entry_src_gen_hcfg in Hentry.
  replace (S (2 * beta + 1)) with (2 * beta + 2) in Hentry by lia.
  assert (Hsim2 : cfg_sim c2' (hcfg (HB pb a 1 (2 * beta + 2) [] 2))).
  { apply (cfg_sim_trans _ _ _ Hs2' Hs2). }
  destruct (run_sim_transfer (2 * beta + 2 + 12) c2'
              (hcfg (HB pb a 1 (2 * beta + 2) [] 2))
              (entry_tgt_gen (enc pb) a (2 * beta + 2)) Hsim2 Hentry)
    as [c3 [Hr3 Hs3]].
  exists ((4 * (2 * beta + 1) + 22) + (n2 + (2 * beta + 2 + 12))), c3.
  split.
  - change (hcfg (HB pb a 1 (2 * beta + 1) [] 1))
      with (gbsec (enc pb) a 1 (2 * beta + 1) [] 1).
    rewrite run_split. rewrite Hregen.
    rewrite run_split. rewrite Hr2'. exact Hr3.
  - apply (cfg_sim_trans _ _ _ Hs3).
    apply entry_gen_sim.
Qed.

(* The ESC-era law for the proved residue range R <= 10: from the   *)
(* ESC source esc_src (R + 6) (beta - 2) (Esc.v's form: L = R + 6,   *)
(* tail pairs beta - 2), the machine reaches a mirror section        *)
(* with b2 = 2*beta + 2 -- the next era's beta is 2*beta + 4.        *)
Lemma ESC_ERA_LAW : forall R beta,
  (R = 2 \/ R = 4 \/ R = 6 \/ R = 8 \/ R = 10) -> 2 <= beta ->
  exists n c pb a,
    run n (esc_src (R + 6) (beta - 2)) = Some c
    /\ cfg_sim c (rcsec (false :: repeat true (S a) ++ enc pb)
                        (2 * beta + 2) [(1, 2)])
    /\ beta <= a.
Proof.
  intros R beta HR Hb.
  assert (HRge : 1 <= R).
  { destruct HR as [E|[E|[E|[E|E]]]]; lia. }
  destruct (ESC_TO_REGEN R beta HR Hb) as [pb [a [Hchain Hfloor]]].
  destruct (hsteps_sound _ _ Hchain) as [n2 [c2 [Hr2 Hs2]]].
  destruct (ERA_TAIL pb a beta Hb ltac:(lia)) as [n3 [c3 [Hr3 Hs3]]].
  pose proof (PROBE_PREFIX (R - 1) (beta - 2)) as Hprobe.
  replace (R - 1 + 7) with (R + 6) in Hprobe by lia.
  replace (S (R - 1)) with R in Hprobe by lia.
  pose proof (PROBE_PREFIX_sim R (beta - 2)) as Hsim0.
  replace (S (beta - 2)) with (beta - 1) in Hsim0 by lia.
  rewrite <- (gcsec_nil 3 1 2
    ((R, 2) :: (1, 1) :: repeat (1, 2) (beta - 1)) 1) in Hsim0.
  change (hcfg (HC [] 3 1 2 ((R, 2) :: (1, 1) :: repeat (1, 2) (beta - 1)) 1))
    with (gcsec (enc []) 3 1 2 ((R, 2) :: (1, 1) :: repeat (1, 2) (beta - 1)) 1)
    in Hr2.
  change (enc []) with ([] : list sym) in Hr2.
  destruct (run_sim_transfer n2 (e5form R (beta - 2))
              (gcsec [] 3 1 2 ((R, 2) :: (1, 1) :: repeat (1, 2) (beta - 1)) 1)
              c2 Hsim0 Hr2)
    as [c2' [Hr2' Hs2']].
  assert (Hsim2 : cfg_sim c2' (hcfg (HB pb a 1 (2 * beta + 1) [] 1))).
  { apply (cfg_sim_trans _ _ _ Hs2' Hs2). }
  destruct (run_sim_transfer n3 c2'
              (hcfg (HB pb a 1 (2 * beta + 1) [] 1)) c3 Hsim2 Hr3)
    as [c3' [Hr3' Hs3']].
  exists ((R - 1 + 49) + (n2 + n3)), c3', pb, a.
  split; [| split].
  - rewrite run_split. rewrite Hprobe.
    rewrite run_split. rewrite Hr2'. exact Hr3'.
  - apply (cfg_sim_trans _ _ _ Hs3' Hs3).
  - exact Hfloor.
Qed.

(* ================================================================= *)
(*  Part 8: obligation (a) -- the era stack invariant and the        *)
(*  Predecessor Lemma discharge.                                     *)
(*                                                                   *)
(*  grind_inv constrains exactly the sections the predecessor        *)
(*  analysis looks at:                                               *)
(*   - B-sections at a = 0: the head pair (w, r) satisfies           *)
(*     s + w <= 7 (the dip budget: inside GRIND(t) at frame a2       *)
(*     with t + 1 <= a2, a B-section at depth d has                  *)
(*     s + headgap = 2t + 5 <= 2(a2 - d) + 5, and the deviated       *)
(*     spine of GRIND_dev saturates the bound at 2a + 7);            *)
(*     a head pair of gap 2 has run 2; the empty stack has s <= 3.   *)
(*   - C-sections at a2 = 0 with g0 >= 3 (PUSH-at-a=2 sources):      *)
(*     the frame is empty (pb = []).                                 *)
(*  PRED_inv then discharges pred_cases' two obligations: an         *)
(*  invariant-respecting step onto a PUSH-at-a=2 source forces       *)
(*  g0 = 3, pb = [], and a TUP producer at shuttle exactly 4;        *)
(*  the STGA / PX2A / TUP2-defect producers are excluded.  At the    *)
(*  source itself only hPUSHX can fire (PUSHX_only).  The invariant  *)
(*  is threaded through the grind chains below (hstepsP versions    *)
(*  of hGRIND, grind_prefix, grind_round, GG_rounds, GG_clean,       *)
(*  hGRIND_dev, ESC_GRIND_10), so every step of those chains         *)
(*  satisfies the discharge's hypotheses.                            *)
(* ================================================================= *)

Definition grind_inv (x : hsec) : Prop :=
  match x with
  | HB pb a g0 s pairs G =>
      a = 0 -> (forall w r rest, pairs = (w, r) :: rest -> s + w <= 7)
             /\ (forall r rest, pairs = (2, r) :: rest -> r = 2)
             /\ (pairs = [] -> s <= 3)
  | HC pb a2 g0 s pairs G =>
      a2 = 0 -> 3 <= g0 -> pb = []
  end.

Lemma inv_HB_pos : forall pb a g0 s pairs G, 1 <= a ->
  grind_inv (HB pb a g0 s pairs G).
Proof.
  intros pb a g0 s pairs G Ha. unfold grind_inv.
  destruct a as [|a']; [lia |]. intros H. discriminate H.
Qed.

Lemma inv_HC_pos : forall pb a2 g0 s pairs G, 1 <= a2 ->
  grind_inv (HC pb a2 g0 s pairs G).
Proof.
  intros pb a2 g0 s pairs G Ha. unfold grind_inv.
  destruct a2 as [|a2']; [lia |]. intros H. discriminate H.
Qed.

Lemma inv_HC_low : forall pb a2 s pairs G,
  grind_inv (HC pb a2 1 s pairs G).
Proof.
  intros pb a2 s pairs G. unfold grind_inv. intros _ H. lia.
Qed.

Lemma inv_HC_0 : forall g0 s pairs G,
  grind_inv (HC [] 0 g0 s pairs G).
Proof.
  intros g0 s pairs G. unfold grind_inv. intros _ _. reflexivity.
Qed.

Lemma inv_HB_head0 : forall pb s w r rest G,
  s + w <= 7 -> (w = 2 -> r = 2) ->
  grind_inv (HB pb 0 1 s ((w, r) :: rest) G).
Proof.
  intros pb s w r rest G H1 H2. unfold grind_inv.
  split; [| split].
  + intros w' r' rest' E. injection E as E1 E2. lia.
  + intros r' rest' E. injection E as E1 E2.
    assert (r = 2) by (apply H2; lia). lia.
  + intros E. discriminate E.
Qed.

(* Invariant at a B-section with head pair (w, r): case on a = 0.   *)
(* At a = 0 the arithmetic closes from the floors in context;       *)
(* at a >= 1 the invariant is vacuous.                              *)
(* Invariant at a C-section: case on a2 = 0 (frame is [] there     *)
(* in the deviated family) vs a2 >= 1 (vacuous).                    *)
Ltac inv_c :=
  match goal with
  | |- grind_inv (HC _ ?a2 _ _ _ _) =>
      first [ apply inv_HC_pos; lia
            | apply inv_HC_0
            | destruct a2 as [|?a2'];
              [ apply inv_HC_0 | apply inv_HC_pos; lia ] ]
  end.

Ltac inv_head :=
  match goal with
  | |- grind_inv (HB _ ?a _ _ _ _) =>
      first [ apply inv_HB_pos; lia
            | apply inv_HB_head0; lia
            | destruct a as [|?a'];
              [ apply inv_HB_head0; lia | apply inv_HB_pos; lia ] ]
  end.

Lemma PRED_inv : forall x y pb g pairs G,
  grind_inv x -> grind_inv y ->
  hstep x y -> y = HC pb 0 (S (S (S g))) 2 pairs G ->
  g = 0 /\ pb = [] /\
  (exists g1'' r1 W, x = HB pb 0 1 4 ((S (S (S g1'')), r1) :: W) G
                     /\ pairs = (S g1'', r1) :: W).
Proof.
  intros x y pb g pairs G Hx Hy Hstep HyEq. subst y.
  assert (Hpb : pb = []).
  { unfold grind_inv in Hy. apply Hy; [reflexivity | lia]. }
  destruct (pred_cases x (HC pb 0 (S (S (S g))) 2 pairs G) pb g pairs G
              Hstep eq_refl)
    as [C1 | [C2 | [C3 | C4]]].
  - destruct C1 as [s'' [g1'' [r1 [W [HxEq [Hs Hp]]]]]].
    subst x. subst pairs.
    unfold grind_inv in Hx.
    destruct (Hx eq_refl) as [Hc1 _].
    specialize (Hc1 (S (S (S g1''))) r1 W eq_refl).
    split; [| split].
    + lia.
    + exact Hpb.
    + exists g1'', r1, W. split; [| reflexivity].
      replace (S (S s'')) with 4 by lia. reflexivity.
  - destruct C2 as [s [G' [HxEq [Hp [Hs HG]]]]]. subst x. subst pairs.
    unfold grind_inv in Hx.
    destruct (Hx eq_refl) as [_ [_ Hc3]].
    specialize (Hc3 eq_refl). lia.
  - destruct C3 as [b' [pb' [W [HxEq [Hp [Hs Hpr]]]]]]. subst x.
    unfold grind_inv in Hx.
    specialize (Hx eq_refl ltac:(lia)). discriminate Hx.
  - destruct C4 as [a [pb0 [s' [w3' [r2' [W [HxEq [Hp [Hs [Hg Hpr]]]]]]]]]].
    rewrite Hpb in Hp. discriminate Hp.
Qed.

Lemma PUSHX_only : forall y z pairs G,
  y = HC [] 0 3 2 pairs G -> hstep y z -> z = HB [] 1 1 7 pairs G.
Proof.
  intros y z pairs G Hy H. subst y. inversion H. reflexivity.
Qed.

(* Invariant-respecting step sequences. *)
Inductive hstepsP (P : hsec -> Prop) : hsec -> hsec -> Prop :=
| hstepsP_refl : forall x, P x -> hstepsP P x x
| hstepsP_step : forall x y z, P x -> hstep x y ->
    hstepsP P y z -> hstepsP P x z.

Lemma hstepsP_forget : forall P x y, hstepsP P x y -> hsteps x y.
Proof.
  intros P x y H. induction H as [x HP | x y z HP Hstep Hsteps IH].
  - apply hsteps_refl.
  - apply (hsteps_step _ y z); assumption.
Qed.

Lemma hstepsP_trans : forall P x y z,
  hstepsP P x y -> hstepsP P y z -> hstepsP P x z.
Proof.
  intros P x y z H1. induction H1 as [x HP | x y0 z0 HP Hstep Hsteps IH];
    intros H2.
  - exact H2.
  - refine (hstepsP_step _ _ _ _ HP Hstep _).
    apply IH. exact H2.
Qed.

Lemma hGRIND_P : forall t pb a2 P G, t + 1 <= a2 ->
  hstepsP grind_inv (HC pb a2 (2*t + 3) 2 P G) (HB pb a2 1 (2*t + 6) P G).
Proof.
  induction t as [t IH] using lt_wf_ind.
  intros pb a2 P G Hfloor.
  destruct t as [|u].
  - destruct a2 as [|a2']; try lia.
    replace (2 * 0 + 3) with 3 by lia.
    replace (2 * 0 + 6) with 6 by lia.
    apply (hstepsP_step _ _ (HC pb a2' 1 2 ((1, 2) :: P) G)).
    { apply inv_HC_pos. lia. }
    { apply (hPUSH pb a2' 0 P G). }
    apply (hstepsP_step _ _ (HB pb a2' 1 4 ((1, 2) :: P) G)).
    { apply inv_HC_low. }
    { apply hTDN. }
    apply (hstepsP_step _ _ (HB pb (S a2') 1 6 P G)).
    { inv_head. }
    { apply hPOP; lia. }
    apply hstepsP_refl.
    apply inv_HB_pos. lia.
  - destruct a2 as [|a2']; try lia.
    assert (Hloop : forall k i,
      2*i + 3 + 2*k = 2 * S u + 1 -> i + 1 <= a2' ->
      hstepsP grind_inv (HC pb a2' (2*i + 3) 2
                 ((2 * S u + 2 - (2*i + 3), 2) :: P) G)
             (HC pb a2' (2 * S u + 1) 2 ((1, 2) :: P) G)).
    { induction k as [|k IHk]; intros i Hk Hi.
      - replace (2 * S u + 2 - (2*i + 3)) with 1 by lia.
        replace (2*i + 3) with (2 * S u + 1) by lia.
        apply hstepsP_refl.
        destruct a2' as [|a2'']; [lia |].
        apply inv_HC_pos. lia.
      - apply (hstepsP_trans _ _ (HB pb a2' 1 (2*i + 6)
              ((2 * S u + 2 - (2*i + 3), 2) :: P) G)).
        { apply (IH i ltac:(lia) pb a2'
                   ((2 * S u + 2 - (2*i + 3), 2) :: P) G Hi). }
        apply (hstepsP_trans _ _ (HC pb a2' (2*(i + 1) + 3) 2
              ((2 * S u + 2 - (2*(i + 1) + 3), 2) :: P) G)).
        + apply (hstepsP_step _ _ (HC pb a2' (2*(i + 1) + 3) 2
                ((2 * S u + 2 - (2*(i + 1) + 3), 2) :: P) G)).
          { inv_head. }
          { replace (HB pb a2' 1 (2*i + 6)
                ((2 * S u + 2 - (2*i + 3), 2) :: P) G)
              with (HB pb a2' 1 (S (S (2*i + 4)))
                ((S (S (S (2*u - 2*i - 2))), 2) :: P) G)
              by sec_eq.
            replace (HC pb a2' (2*(i + 1) + 3) 2
                ((2 * S u + 2 - (2*(i + 1) + 3), 2) :: P) G)
              with (HC pb a2' (S (2*i + 4)) 2
                ((S (2*u - 2*i - 2), 2) :: P) G)
              by sec_eq.
            apply hTUP. }
          apply hstepsP_refl.
          destruct a2' as [|a2'']; [lia |].
          apply inv_HC_pos. lia.
        + apply IHk; lia. }
    apply (hstepsP_trans _ _ (HC pb a2' 1 2 ((2 * S u + 1, 2) :: P) G)).
    { apply (hstepsP_step _ _ (HC pb a2' 1 2 ((2 * S u + 1, 2) :: P) G)).
      { apply inv_HC_pos. lia. }
      { replace (HC pb (S a2') (2 * S u + 3) 2 P G)
          with (HC pb (S a2') (S (S (S (2 * S u)))) 2 P G)
          by sec_eq.
        replace (HC pb a2' 1 2 ((2 * S u + 1, 2) :: P) G)
          with (HC pb a2' 1 2 ((S (2 * S u), 2) :: P) G)
          by sec_eq.
        apply hPUSH. }
      apply hstepsP_refl. apply inv_HC_low. }
    apply (hstepsP_trans _ _ (HB pb a2' 1 4 ((2 * S u + 1, 2) :: P) G)).
    { apply (hstepsP_step _ _ (HB pb a2' 1 4 ((2 * S u + 1, 2) :: P) G)).
      { apply inv_HC_low. }
      { apply hTDN. }
      apply hstepsP_refl.
      inv_head. }
    apply (hstepsP_trans _ _ (HC pb a2' 3 2 ((2 * S u - 1, 2) :: P) G)).
    { apply (hstepsP_step _ _ (HC pb a2' 3 2 ((2 * S u - 1, 2) :: P) G)).
      { inv_head. }
      { replace (HB pb a2' 1 4 ((2 * S u + 1, 2) :: P) G)
          with (HB pb a2' 1 (S (S 2)) ((S (S (S (2 * u))), 2) :: P) G)
          by sec_eq.
        replace (HC pb a2' 3 2 ((2 * S u - 1, 2) :: P) G)
          with (HC pb a2' (S 2) 2 ((S (2 * u), 2) :: P) G)
          by sec_eq.
        apply hTUP. }
      apply hstepsP_refl.
      destruct a2' as [|a2'']; [lia |]. apply inv_HC_pos. lia. }
    apply (hstepsP_trans _ _ (HC pb a2' (2 * S u + 1) 2 ((1, 2) :: P) G)).
    { pose proof (Hloop u 0 ltac:(lia) ltac:(lia)) as Hc4.
      replace (2 * S u + 2 - (2*0 + 3)) with (2 * S u - 1) in Hc4 by lia.
      replace (2*0 + 3) with 3 in Hc4 by lia.
      exact Hc4. }
    apply (hstepsP_trans _ _ (HB pb a2' 1 (2 * S u + 4) ((1, 2) :: P) G)).
    { pose proof (IH u ltac:(lia) pb a2' ((1, 2) :: P) G ltac:(lia))
        as Hc5.
      replace (2*u + 3) with (2 * S u + 1) in Hc5 by lia.
      replace (2*u + 6) with (2 * S u + 4) in Hc5 by lia.
      exact Hc5. }
    apply (hstepsP_step _ _ (HB pb (S a2') 1 (2 * S u + 6) P G)).
    { inv_head. }
    { replace (2 * S u + 6) with ((2 * S u + 4) + 2) by lia.
      apply hPOP; lia. }
    apply hstepsP_refl.
    apply inv_HB_pos. lia.
Qed.

Lemma grind_prefix_P : forall pb a2' r' W G,
  hstepsP grind_inv (HC pb (S a2') 1 2 ((S (S (S r')), 2) :: W) G)
         (HB pb (S a2') 1 6 ((S r', 2) :: W) G).
Proof.
  intros pb a2' r' W G.
  apply (hstepsP_step _ _ (HB pb (S a2') 1 4 ((S (S (S r')), 2) :: W) G)).
  { apply inv_HC_pos. lia. }
  { apply hTDN. }
  apply (hstepsP_step _ _ (HC pb (S a2') 3 2 ((S r', 2) :: W) G)).
  { apply inv_HB_pos. lia. }
  { apply (hTUP pb (S a2') 2 r' 2 W G). }
  apply (hstepsP_step _ _ (HC pb a2' 1 2 ((1, 2) :: (S r', 2) :: W) G)).
  { apply inv_HC_pos. lia. }
  { apply (hPUSH pb a2' 0 ((S r', 2) :: W) G). }
  apply (hstepsP_step _ _ (HB pb a2' 1 4 ((1, 2) :: (S r', 2) :: W) G)).
  { apply inv_HC_low. }
  { apply hTDN. }
  apply (hstepsP_step _ _ (HB pb (S a2') 1 6 ((S r', 2) :: W) G)).
  { inv_head. }
  { apply hPOP; lia. }
  apply hstepsP_refl.
  apply inv_HB_pos. lia.
Qed.

Lemma grind_round_P : forall j pb a2 g P G, j + 1 <= a2 -> 3 <= g ->
  hstepsP grind_inv (HB pb a2 1 (2*j + 4) ((g, 2) :: P) G)
         (HB pb a2 1 (2*j + 6) ((g - 2, 2) :: P) G).
Proof.
  intros j pb a2 g P G Hj Hg.
  apply (hstepsP_trans _ _ (HC pb a2 (2*j + 3) 2 ((g - 2, 2) :: P) G)).
  - apply (hstepsP_step _ _ (HC pb a2 (2*j + 3) 2 ((g - 2, 2) :: P) G)).
    { inv_head. }
    { replace (HB pb a2 1 (2*j + 4) ((g, 2) :: P) G)
        with (HB pb a2 1 (S (S (2*j + 2)))
                 ((S (S (S (g - 3))), 2) :: P) G)
        by sec_eq.
      replace (HC pb a2 (2*j + 3) 2 ((g - 2, 2) :: P) G)
        with (HC pb a2 (S (2*j + 2)) 2 ((S (g - 3), 2) :: P) G)
        by sec_eq.
      apply hTUP. }
    apply hstepsP_refl.
    apply inv_HC_pos. lia.
  - apply hGRIND_P; exact Hj.
Qed.

Lemma GG_rounds_P : forall m j0 pb a2 P G, j0 + m + 1 <= a2 ->
  hstepsP grind_inv (HB pb a2 1 (2*j0 + 6) ((2*m + 2, 2) :: P) G)
         (HB pb a2 1 (2*(j0 + m) + 6) ((2, 2) :: P) G).
Proof.
  induction m as [|m IH]; intros j0 pb a2 P G Hf.
  - replace (2 * (j0 + 0) + 6) with (2*j0 + 6) by lia.
    replace (2 * 0 + 2) with 2 by lia.
    apply hstepsP_refl.
    inv_head.
  - apply (hstepsP_trans _ _ (HB pb a2 1 (2*(j0 + 1) + 6) ((2*m + 2, 2) :: P) G)).
    + replace (HB pb a2 1 (2*j0 + 6) ((2 * S m + 2, 2) :: P) G)
        with (HB pb a2 1 (2*(j0 + 1) + 4) ((2*m + 4, 2) :: P) G)
        by sec_eq.
      replace (HB pb a2 1 (2*(j0 + 1) + 6) ((2*m + 2, 2) :: P) G)
        with (HB pb a2 1 (2*(j0 + 1) + 6) ((2*m + 4 - 2, 2) :: P) G)
        by sec_eq.
      apply grind_round_P; lia.
    + replace (HB pb a2 1 (2*(j0 + S m) + 6) ((2, 2) :: P) G)
        with (HB pb a2 1 (2*((j0 + 1) + m) + 6) ((2, 2) :: P) G)
        by sec_eq.
      apply IH. lia.
Qed.

Lemma GG_clean_P : forall m pb a2 P G, m + 1 <= a2 ->
  hstepsP grind_inv (HC pb a2 1 2 ((2*m + 4, 2) :: P) G)
         (HB pb a2 1 (2*m + 6) ((2, 2) :: P) G).
Proof.
  intros m pb a2 P G Hf. destruct a2 as [|a2']; try lia.
  apply (hstepsP_trans _ _ (HB pb (S a2') 1 6 ((2*m + 2, 2) :: P) G)).
  - replace (HC pb (S a2') 1 2 ((2*m + 4, 2) :: P) G)
      with (HC pb (S a2') 1 2 ((S (S (S (2*m + 1))), 2) :: P) G)
      by sec_eq.
    replace (HB pb (S a2') 1 6 ((2*m + 2, 2) :: P) G)
      with (HB pb (S a2') 1 6 ((S (2*m + 1), 2) :: P) G)
      by sec_eq.
    apply grind_prefix_P.
  - replace (HB pb (S a2') 1 6 ((2*m + 2, 2) :: P) G)
      with (HB pb (S a2') 1 (2*0 + 6) ((2*m + 2, 2) :: P) G)
      by sec_eq.
    replace (HB pb (S a2') 1 (2*m + 6) ((2, 2) :: P) G)
      with (HB pb (S a2') 1 (2*(0 + m) + 6) ((2, 2) :: P) G)
      by sec_eq.
    apply GG_rounds_P. lia.
Qed.

Lemma hGRIND_dev_P : forall t P G,
  hstepsP grind_inv (HC [] t (2*t + 3) 2 P G) (HB [] (S t) 1 (2*t + 7) P G).
Proof.
  induction t as [t IH] using lt_wf_ind.
  intros P G.
  destruct t as [|u].
  - replace (2 * 0 + 3) with 3 by lia.
    replace (2 * 0 + 7) with 7 by lia.
    apply (hstepsP_step _ _ (HB [] 1 1 7 P G)).
    { apply inv_HC_0. }
    { apply hPUSHX. }
    apply hstepsP_refl.
    apply inv_HB_pos. lia.
  - assert (Hloop : forall k i,
      2*i + 3 + 2*k = 2 * S u + 1 -> i <= u ->
      hstepsP grind_inv (HC [] u (2*i + 3) 2
                 ((2 * S u + 2 - (2*i + 3), 2) :: P) G)
             (HC [] u (2 * S u + 1) 2 ((1, 2) :: P) G)).
    { induction k as [|k IHk]; intros i Hk Hi.
      - replace (2 * S u + 2 - (2*i + 3)) with 1 by lia.
        replace (2*i + 3) with (2 * S u + 1) by lia.
        apply hstepsP_refl.
        inv_c.
      - apply (hstepsP_trans _ _ (HB [] u 1 (2*i + 6)
              ((2 * S u + 2 - (2*i + 3), 2) :: P) G)).
        { apply (hGRIND_P i [] u
                   ((2 * S u + 2 - (2*i + 3), 2) :: P) G).
          lia. }
        apply (hstepsP_trans _ _ (HC [] u (2*(i + 1) + 3) 2
              ((2 * S u + 2 - (2*(i + 1) + 3), 2) :: P) G)).
        + apply (hstepsP_step _ _ (HC [] u (2*(i + 1) + 3) 2
                ((2 * S u + 2 - (2*(i + 1) + 3), 2) :: P) G)).
          { inv_head. }
          { replace (HB [] u 1 (2*i + 6)
                ((2 * S u + 2 - (2*i + 3), 2) :: P) G)
              with (HB [] u 1 (S (S (2*i + 4)))
                ((S (S (S (2*u - 2*i - 2))), 2) :: P) G)
              by sec_eq.
            replace (HC [] u (2*(i + 1) + 3) 2
                ((2 * S u + 2 - (2*(i + 1) + 3), 2) :: P) G)
              with (HC [] u (S (2*i + 4)) 2
                ((S (2*u - 2*i - 2), 2) :: P) G)
              by sec_eq.
            apply hTUP. }
          apply hstepsP_refl.
          inv_c.
        + apply IHk; lia. }
    apply (hstepsP_trans _ _ (HC [] u 1 2 ((2 * S u + 1, 2) :: P) G)).
    { apply (hstepsP_step _ _ (HC [] u 1 2 ((2 * S u + 1, 2) :: P) G)).
      { apply inv_HC_pos. lia. }
      { replace (HC [] (S u) (2 * S u + 3) 2 P G)
          with (HC [] (S u) (S (S (S (2 * S u)))) 2 P G)
          by sec_eq.
        replace (HC [] u 1 2 ((2 * S u + 1, 2) :: P) G)
          with (HC [] u 1 2 ((S (2 * S u), 2) :: P) G)
          by sec_eq.
        apply hPUSH. }
      apply hstepsP_refl. apply inv_HC_low. }
    apply (hstepsP_trans _ _ (HB [] u 1 4 ((2 * S u + 1, 2) :: P) G)).
    { apply (hstepsP_step _ _ (HB [] u 1 4 ((2 * S u + 1, 2) :: P) G)).
      { apply inv_HC_low. }
      { apply hTDN. }
      apply hstepsP_refl.
      inv_head. }
    apply (hstepsP_trans _ _ (HC [] u 3 2 ((2 * S u - 1, 2) :: P) G)).
    { apply (hstepsP_step _ _ (HC [] u 3 2 ((2 * S u - 1, 2) :: P) G)).
      { inv_head. }
      { replace (HB [] u 1 4 ((2 * S u + 1, 2) :: P) G)
          with (HB [] u 1 (S (S 2)) ((S (S (S (2 * u))), 2) :: P) G)
          by sec_eq.
        replace (HC [] u 3 2 ((2 * S u - 1, 2) :: P) G)
          with (HC [] u (S 2) 2 ((S (2 * u), 2) :: P) G)
          by sec_eq.
        apply hTUP. }
      apply hstepsP_refl.
      inv_c. }
    apply (hstepsP_trans _ _ (HC [] u (2 * S u + 1) 2 ((1, 2) :: P) G)).
    { pose proof (Hloop u 0 ltac:(lia) ltac:(lia)) as Hc4.
      replace (2 * S u + 2 - (2*0 + 3)) with (2 * S u - 1) in Hc4 by lia.
      replace (2*0 + 3) with 3 in Hc4 by lia.
      exact Hc4. }
    apply (hstepsP_trans _ _ (HB [] (S u) 1 (2*u + 7) ((1, 2) :: P) G)).
    { pose proof (IH u ltac:(lia) ((1, 2) :: P) G) as Hc5.
      replace (2*u + 3) with (2 * S u + 1) in Hc5 by lia.
      exact Hc5. }
    apply (hstepsP_step _ _ (HB [] (S (S u)) 1 (2 * S u + 7) P G)).
    { inv_head. }
    { replace (2 * S u + 7) with ((2*u + 7) + 2) by lia.
      apply hPOP; lia. }
    apply hstepsP_refl.
    apply inv_HB_pos. lia.
Qed.

Lemma ESC_GRIND_10_P : forall P G,
  hstepsP grind_inv (HC [] 3 1 2 ((10, 2) :: P) G)
         (HB [] 4 1 13 ((2, 2) :: P) G).
Proof.
  intros P G.
  apply (hstepsP_trans _ _ (HB [] 3 1 10 ((4, 2) :: P) G)).
  - apply (hstepsP_trans _ _ (HB [] 3 1 6 ((8, 2) :: P) G)).
    + replace (HC [] 3 1 2 ((10, 2) :: P) G)
        with (HC [] 3 1 2 ((S (S (S 7)), 2) :: P) G)
        by sec_eq.
      replace (HB [] 3 1 6 ((8, 2) :: P) G)
        with (HB [] 3 1 6 ((S 7, 2) :: P) G)
        by sec_eq.
      apply grind_prefix_P.
    + apply (hstepsP_trans _ _ (HB [] 3 1 8 ((6, 2) :: P) G)).
      * replace (HB [] 3 1 6 ((8, 2) :: P) G)
          with (HB [] 3 1 (2*1 + 4) ((8, 2) :: P) G)
          by sec_eq.
        replace (HB [] 3 1 8 ((6, 2) :: P) G)
          with (HB [] 3 1 (2*1 + 6) ((8 - 2, 2) :: P) G)
          by sec_eq.
        apply grind_round_P; lia.
      * replace (HB [] 3 1 8 ((6, 2) :: P) G)
          with (HB [] 3 1 (2*2 + 4) ((6, 2) :: P) G)
          by sec_eq.
        replace (HB [] 3 1 10 ((4, 2) :: P) G)
          with (HB [] 3 1 (2*2 + 6) ((6 - 2, 2) :: P) G)
          by sec_eq.
        apply grind_round_P; lia.
  - apply (hstepsP_trans _ _ (HC [] 3 9 2 ((2, 2) :: P) G)).
    + apply (hstepsP_step _ _ (HC [] 3 9 2 ((2, 2) :: P) G)).
      { inv_head. }
      { replace (HB [] 3 1 10 ((4, 2) :: P) G)
          with (HB [] 3 1 (S (S 8)) ((S (S (S 1)), 2) :: P) G)
          by sec_eq.
        replace (HC [] 3 9 2 ((2, 2) :: P) G)
          with (HC [] 3 (S 8) 2 ((S 1, 2) :: P) G)
          by sec_eq.
        apply hTUP. }
      apply hstepsP_refl.
      apply inv_HC_pos. lia.
    + replace (HC [] 3 9 2 ((2, 2) :: P) G)
        with (HC [] 3 (2*3 + 3) 2 ((2, 2) :: P) G)
        by sec_eq.
      replace (HB [] 4 1 13 ((2, 2) :: P) G)
        with (HB [] (S 3) 1 (2*3 + 7) ((2, 2) :: P) G)
        by sec_eq.
      apply hGRIND_dev_P.
Qed.

(* Axiom audit for this file's headline lemmas. *)
Print Assumptions hGRIND.
Print Assumptions hGRIND_dev.
Print Assumptions GG_clean.
Print Assumptions ESC_GRIND_10.
Print Assumptions ESC_TO_REGEN.
Print Assumptions REGEN_gen.
Print Assumptions ERA_TAIL.
Print Assumptions ESC_ERA_LAW.
Print Assumptions PRED_inv.
Print Assumptions PUSHX_only.
Print Assumptions GG_clean_P.
Print Assumptions hGRIND_dev_P.
Print Assumptions ESC_GRIND_10_P.
