(* ================================================================= *)
(*  Grind6.v -- Phase 37: the merged unwind at R = 116, and the      *)
(*  phase-4 / phase-5 continuations covering every even R <= 268.    *)
(*                                                                   *)
(*  The Phase 36 fence: the deviated grind at pb = [20; 0] (grind    *)
(*  34 at frame 34, R = 116) has no uniform landing -- its base      *)
(*  step hPX2A0 consumes the prefix and leaves the residue pair      *)
(*  (16, 2), so the grind's closing is the whole (16, 2) grind at    *)
(*  ([0], 3), merged with the consumption of the (1, 2)^34 spine     *)
(*  and of the era stack below it.  This file assembles that         *)
(*  merged unwind explicitly:                                        *)
(*                                                                   *)
(*  - DEV20_step / DEV20_DESCEND: the descent of the [20; 0] grind   *)
(*    to its dip bottom HC [20; 0] 0 3 2 ((1, 2)^t :: P) (the        *)
(*    PUSH/TDN/TUP/loop part of hGRIND_dev's recursion, at           *)
(*    pb = [20; 0]);                                                 *)
(*  - GRIND16_A..E + GRIND16_MID: the (16, 2) grind at ([0], 3)      *)
(*    over an arbitrary carried rest: TUP + grind_prefix + clean     *)
(*    rounds 1-2, TUP + hGRIND_dev0 3 (the boundary round, pb         *)
(*    becomes []), a second G'' grind (PUSH + grind_prefix +         *)
(*    rounds 1-2), TUP + hGRIND_dev 3, then TUP2_1 + TDN +           *)
(*    TRANS2_1 + a POP chain over the spine, landing at              *)
(*    HB [14; 5] (n+7) 1 (2n+7) Rest 1 for spine length n;           *)
(*  - PHASE3_DEEP: the common chain for R = 2m + 46, m >= 35,        *)
(*    from the ESC grind source to HB [14; 5] 41 1 75                *)
(*    ((2m - 68, 2) :: Pe) (BIG2's chain with 34 phase-3 rounds,     *)
(*    the final round's TUP, the descent, hPX2A0, GRIND16_MID);      *)
(*  - the finishes: m = 35 is TAIL itself (R = 116); m = 36 runs     *)
(*    TUP + hGRIND_even 35 + TRANS2_2 + pop_chain_h (R = 118,        *)
(*    phase 4); m = 37 runs TUP + hGRIND_even 35 + TUP2_1 + TDN +    *)
(*    TAIL (R = 120); 38 <= m <= 111 (phase 5) continues with        *)
(*    rounds at ([41; 14; 5], 74) and a final clean hGRIND           *)
(*    (m - 38) + TAIL.  Hence ESC_ERA_LAW_268: the ESC-era law       *)
(*    beta_next = 2 beta + 4 for every even R <= 268.                *)
(*                                                                   *)
(*  The new fence is at m >= 112 (R >= 270): phase 5's final grind   *)
(*  (t = m - 38 at frame 74) reaches its floor at m = 112            *)
(*  (m - 37 <= 74 fails), i.e. the grind becomes a boundary          *)
(*  (deviated) grind at the three-block prefix [41; 14; 5] -- a      *)
(*  phase-6 deviation whose dip bottom has not been derived.         *)
(*                                                                   *)
(*  All forms pre-verified in rocq/hsim37.py: GRIND16_TAIL word      *)
(*  boundaries at (spine, beta) in {(0,2), (2,2), (3,3), (5,2)},     *)
(*  word/machine boundary agreement at (2, 2) (131 rules, 1598       *)
(*  machine steps), DEV20_DESCEND boundaries at t = 1, 2, 3, the     *)
(*  rounds_from4g analogue, and frame-10 analogues of the phase-4    *)
(*  and phase-5 finishes.                                            *)
(* ================================================================= *)

Require Import List Bool Arith Lia ZArith.
Import ListNotations.
Require Import TM Sections Mirror TokenPass Recoord Era Esc Dev Grind Grind2 Grind3 Grind4 Grind5.

Ltac sec_eq := repeat (first [ solve [reflexivity] | solve [lia] | f_equal ]).

(* ================================================================= *)
(*  Part 1: two round/pop helpers.                                   *)
(* ================================================================= *)

(* Phase-3/5 rounds with a general residue: grind_round j0 ..        *)
(* j0 + m - 1 (floors j0 + m <= a2), residue g |-> g - 2m.           *)
Lemma rounds_from4g : forall m j0 pb a2 g P G,
  j0 + m <= a2 -> 2*m + 3 <= g ->
  hsteps (HB pb a2 1 (2*j0 + 4) ((g, 2) :: P) G)
         (HB pb a2 1 (2*(j0 + m) + 4) ((g - 2*m, 2) :: P) G).
Proof.
  induction m as [|m IH]; intros j0 pb a2 g P G Hf Hg.
  - replace (2 * (j0 + 0) + 4) with (2*j0 + 4) by lia.
    replace (g - 2 * 0) with g by lia.
    apply hsteps_refl.
  - apply (hsteps_trans _
      (HB pb a2 1 (2*(j0 + 1) + 4) ((g - 2, 2) :: P) G)).
    + replace (HB pb a2 1 (2*(j0 + 1) + 4) ((g - 2, 2) :: P) G)
        with (HB pb a2 1 (2*j0 + 6) ((g - 2, 2) :: P) G)
        by sec_eq.
      apply grind_round; lia.
    + replace (HB pb a2 1 (2*(j0 + S m) + 4) ((g - 2 * S m, 2) :: P) G)
        with (HB pb a2 1 (2*((j0 + 1) + m) + 4) (((g - 2) - 2*m, 2) :: P) G)
        by sec_eq.
      apply IH; lia.
Qed.

(* The POP chain over a (1, 2) prefix with a carried rest. *)
Lemma pop_chain_h_app : forall m pb a s rest G, 2 <= s ->
  hsteps (HB pb a 1 s (repeat (1, 2) m ++ rest) G)
         (HB pb (a + m) 1 (s + 2*m) rest G).
Proof.
  induction m as [|m IH]; intros pb a s rest G Hs.
  - cbn [repeat app].
    replace (a + 0) with a by lia.
    replace (s + 2 * 0) with s by lia.
    apply hsteps_refl.
  - cbn [repeat app].
    apply (hsteps_trans _ (HB pb (S a) 1 (s + 2) (repeat (1, 2) m ++ rest) G)).
    + apply (hsteps_step _ (HB pb (S a) 1 (s + 2) (repeat (1, 2) m ++ rest) G)).
      { apply hPOP; lia. }
      apply hsteps_refl.
    + replace (HB pb (a + S m) 1 (s + 2 * S m) rest G)
        with (HB pb (S a + m) 1 (s + 2 + 2 * m) rest G)
        by sec_eq.
      apply IH. lia.
Qed.

(* ================================================================= *)
(*  Part 2: the descent of the deviated grind at pb = [20; 0].       *)
(*  One level (PUSH + TDN + TUP + the clean loop), then induction.   *)
(* ================================================================= *)

Lemma DEV20_step : forall u P G,
  hsteps (HC [20; 0] (S u) (2 * S u + 3) 2 P G)
         (HC [20; 0] u (2*u + 3) 2 ((1, 2) :: P) G).
Proof.
  intros u P G.
  assert (Hloop : forall k i,
    2*i + 3 + 2*k = 2 * S u + 1 -> i <= u ->
    hsteps (HC [20; 0] u (2*i + 3) 2
               ((2 * S u + 2 - (2*i + 3), 2) :: P) G)
           (HC [20; 0] u (2 * S u + 1) 2 ((1, 2) :: P) G)).
  { induction k as [|k IHk]; intros i Hk Hi.
    - replace (2 * S u + 2 - (2*i + 3)) with 1 by lia.
      replace (2*i + 3) with (2 * S u + 1) by lia.
      apply hsteps_refl.
    - apply (hsteps_trans _
        (HB [20; 0] u 1 (2*i + 6)
            ((2 * S u + 2 - (2*i + 3), 2) :: P) G)).
      { apply (hGRIND i [20; 0] u
                 ((2 * S u + 2 - (2*i + 3), 2) :: P) G).
        lia. }
      apply (hsteps_trans _
        (HC [20; 0] u (2*(i + 1) + 3) 2
            ((2 * S u + 2 - (2*(i + 1) + 3), 2) :: P) G)).
      + apply (hsteps_step _
          (HC [20; 0] u (2*(i + 1) + 3) 2
              ((2 * S u + 2 - (2*(i + 1) + 3), 2) :: P) G)).
        { replace (HB [20; 0] u 1 (2*i + 6)
              ((2 * S u + 2 - (2*i + 3), 2) :: P) G)
            with (HB [20; 0] u 1 (S (S (2*i + 4)))
              ((S (S (S (2*u - 2*i - 2))), 2) :: P) G)
            by sec_eq.
          replace (HC [20; 0] u (2*(i + 1) + 3) 2
              ((2 * S u + 2 - (2*(i + 1) + 3), 2) :: P) G)
            with (HC [20; 0] u (S (2*i + 4)) 2
              ((S (2*u - 2*i - 2), 2) :: P) G)
            by sec_eq.
          apply hTUP. }
        apply hsteps_refl.
      + apply IHk; lia. }
  apply (hsteps_trans _ (HC [20; 0] u 1 2 ((2 * S u + 1, 2) :: P) G)).
  { replace (HC [20; 0] (S u) (2 * S u + 3) 2 P G)
      with (HC [20; 0] (S u) (S (S (S (2 * S u)))) 2 P G)
      by sec_eq.
    replace (HC [20; 0] u 1 2 ((2 * S u + 1, 2) :: P) G)
      with (HC [20; 0] u 1 2 ((S (2 * S u), 2) :: P) G)
      by sec_eq.
    apply (hsteps_step _ (HC [20; 0] u 1 2 ((S (2 * S u), 2) :: P) G)).
    { apply hPUSH. }
    apply hsteps_refl. }
  apply (hsteps_trans _ (HB [20; 0] u 1 4 ((2 * S u + 1, 2) :: P) G)).
  { apply (hsteps_step _ (HB [20; 0] u 1 4 ((2 * S u + 1, 2) :: P) G)).
    { apply hTDN. }
    apply hsteps_refl. }
  apply (hsteps_trans _ (HC [20; 0] u 3 2 ((2 * S u - 1, 2) :: P) G)).
  { apply (hsteps_step _ (HC [20; 0] u 3 2 ((2 * S u - 1, 2) :: P) G)).
    { replace (HB [20; 0] u 1 4 ((2 * S u + 1, 2) :: P) G)
        with (HB [20; 0] u 1 (S (S 2)) ((S (S (S (2 * u))), 2) :: P) G)
        by sec_eq.
      replace (HC [20; 0] u 3 2 ((2 * S u - 1, 2) :: P) G)
        with (HC [20; 0] u (S 2) 2 ((S (2 * u), 2) :: P) G)
        by sec_eq.
      apply hTUP. }
    apply hsteps_refl. }
  pose proof (Hloop u 0 ltac:(lia) ltac:(lia)) as Hc4.
  replace (2 * S u + 2 - (2*0 + 3)) with (2 * S u - 1) in Hc4 by lia.
  replace (2*0 + 3) with 3 in Hc4 by lia.
  replace (HC [20; 0] u (2*u + 3) 2 ((1, 2) :: P) G)
    with (HC [20; 0] u (2 * S u + 1) 2 ((1, 2) :: P) G)
    by sec_eq.
  exact Hc4.
Qed.

Lemma repeat_cons_app : forall n (x : nat * nat) (l : list (nat * nat)),
  repeat x n ++ (x :: l) = x :: (repeat x n ++ l).
Proof.
  induction n as [|n IH]; intros x l.
  - cbn [repeat app]. reflexivity.
  - cbn [repeat app]. rewrite IH. reflexivity.
Qed.

Lemma DEV20_DESCEND : forall t P G,
  hsteps (HC [20; 0] t (2*t + 3) 2 P G)
         (HC [20; 0] 0 3 2 (repeat (1, 2) t ++ P) G).
Proof.
  induction t as [|u IH]; intros P G.
  - cbn [repeat app]. replace (2 * 0 + 3) with 3 by lia.
    apply hsteps_refl.
  - apply (hsteps_trans _ (HC [20; 0] u (2*u + 3) 2 ((1, 2) :: P) G)).
    { apply DEV20_step. }
    assert (Heq : repeat (1, 2) (S u) ++ P
                  = repeat (1, 2) u ++ ((1, 2) :: P)).
    { cbn [repeat app]. symmetry. apply repeat_cons_app. }
    rewrite Heq. apply IH.
Qed.

(* ================================================================= *)
(*  Part 3: the (16, 2) grind at ([0], 3) over a carried rest Q.     *)
(* ================================================================= *)

(* Segment A: TUP + grind_prefix + clean rounds 1-2. *)
Lemma GRIND16_A : forall Q G,
  hsteps (HB [0] 3 1 2 ((16, 2) :: Q) G)
         (HB [0] 3 1 10 ((8, 2) :: Q) G).
Proof.
  intros Q G.
  apply (hsteps_trans _ (HC [0] 3 1 2 ((14, 2) :: Q) G)).
  { apply (hsteps_step _ (HC [0] 3 1 2 ((14, 2) :: Q) G)).
    { replace (HB [0] 3 1 2 ((16, 2) :: Q) G)
        with (HB [0] 3 1 (S (S 0)) ((S (S (S 13)), 2) :: Q) G)
        by sec_eq.
      replace (HC [0] 3 1 2 ((14, 2) :: Q) G)
        with (HC [0] 3 (S 0) 2 ((S 13, 2) :: Q) G) by sec_eq.
      apply hTUP. }
    apply hsteps_refl. }
  apply (hsteps_trans _ (HB [0] 3 1 6 ((12, 2) :: Q) G)).
  { replace (HC [0] 3 1 2 ((14, 2) :: Q) G)
      with (HC [0] (S 2) 1 2 ((S (S (S 11)), 2) :: Q) G)
      by sec_eq.
    replace (HB [0] 3 1 6 ((12, 2) :: Q) G)
      with (HB [0] (S 2) 1 6 ((S 11, 2) :: Q) G) by sec_eq.
    apply grind_prefix. }
  apply (hsteps_trans _ (HB [0] 3 1 8 ((10, 2) :: Q) G)).
  { replace (HB [0] 3 1 6 ((12, 2) :: Q) G)
      with (HB [0] 3 1 (2*1 + 4) ((12, 2) :: Q) G) by sec_eq.
    replace (HB [0] 3 1 8 ((10, 2) :: Q) G)
      with (HB [0] 3 1 (2*1 + 6) ((12 - 2, 2) :: Q) G) by sec_eq.
    apply grind_round; lia. }
  replace (HB [0] 3 1 8 ((10, 2) :: Q) G)
    with (HB [0] 3 1 (2*2 + 4) ((10, 2) :: Q) G) by sec_eq.
  replace (HB [0] 3 1 10 ((8, 2) :: Q) G)
    with (HB [0] 3 1 (2*2 + 6) ((10 - 2, 2) :: Q) G) by sec_eq.
  apply grind_round; lia.
Qed.

(* Segment B: TUP + the boundary round hGRIND_dev0 3 (pb [0] -> []). *)
Lemma GRIND16_B : forall Q G,
  hsteps (HB [0] 3 1 10 ((8, 2) :: Q) G)
         (HB [] 4 1 13 ((6, 2) :: Q) G).
Proof.
  intros Q G.
  apply (hsteps_trans _ (HC [0] 3 9 2 ((6, 2) :: Q) G)).
  { apply (hsteps_step _ (HC [0] 3 9 2 ((6, 2) :: Q) G)).
    { replace (HB [0] 3 1 10 ((8, 2) :: Q) G)
        with (HB [0] 3 1 (S (S 8)) ((S (S (S 5)), 2) :: Q) G)
        by sec_eq.
      replace (HC [0] 3 9 2 ((6, 2) :: Q) G)
        with (HC [0] 3 (S 8) 2 ((S 5, 2) :: Q) G) by sec_eq.
      apply hTUP. }
    apply hsteps_refl. }
  replace (HC [0] 3 9 2 ((6, 2) :: Q) G)
    with (HC [0] 3 (2*3 + 3) 2 ((6, 2) :: Q) G) by sec_eq.
  replace (HB [] 4 1 13 ((6, 2) :: Q) G)
    with (HB [] (S 3) 1 (2*3 + 7) ((6, 2) :: Q) G) by sec_eq.
  apply hGRIND_dev0.
Qed.

(* Segment C: TUP + PUSH + grind_prefix + clean rounds 1-2 (the      *)
(* second G'' grind, residue 10 over the carried (4, 2)).            *)
Lemma GRIND16_C : forall Q G,
  hsteps (HB [] 4 1 13 ((6, 2) :: Q) G)
         (HB [] 3 1 10 ((4, 2) :: (4, 2) :: Q) G).
Proof.
  intros Q G.
  apply (hsteps_trans _ (HC [] 4 12 2 ((4, 2) :: Q) G)).
  { apply (hsteps_step _ (HC [] 4 12 2 ((4, 2) :: Q) G)).
    { replace (HB [] 4 1 13 ((6, 2) :: Q) G)
        with (HB [] 4 1 (S (S 11)) ((S (S (S 3)), 2) :: Q) G)
        by sec_eq.
      replace (HC [] 4 12 2 ((4, 2) :: Q) G)
        with (HC [] 4 (S 11) 2 ((S 3, 2) :: Q) G) by sec_eq.
      apply hTUP. }
    apply hsteps_refl. }
  apply (hsteps_trans _ (HC [] 3 1 2 ((10, 2) :: (4, 2) :: Q) G)).
  { apply (hsteps_step _ (HC [] 3 1 2 ((10, 2) :: (4, 2) :: Q) G)).
    { replace (HC [] 4 12 2 ((4, 2) :: Q) G)
        with (HC [] (S 3) (S (S (S 9))) 2 ((4, 2) :: Q) G)
        by sec_eq.
      replace (HC [] 3 1 2 ((10, 2) :: (4, 2) :: Q) G)
        with (HC [] 3 1 2 ((S 9, 2) :: (4, 2) :: Q) G) by sec_eq.
      apply hPUSH. }
    apply hsteps_refl. }
  apply (hsteps_trans _ (HB [] 3 1 6 ((8, 2) :: (4, 2) :: Q) G)).
  { replace (HC [] 3 1 2 ((10, 2) :: (4, 2) :: Q) G)
      with (HC [] (S 2) 1 2 ((S (S (S 7)), 2) :: (4, 2) :: Q) G)
      by sec_eq.
    replace (HB [] 3 1 6 ((8, 2) :: (4, 2) :: Q) G)
      with (HB [] (S 2) 1 6 ((S 7, 2) :: (4, 2) :: Q) G) by sec_eq.
    apply grind_prefix. }
  apply (hsteps_trans _ (HB [] 3 1 8 ((6, 2) :: (4, 2) :: Q) G)).
  { replace (HB [] 3 1 6 ((8, 2) :: (4, 2) :: Q) G)
      with (HB [] 3 1 (2*1 + 4) ((8, 2) :: (4, 2) :: Q) G) by sec_eq.
    replace (HB [] 3 1 8 ((6, 2) :: (4, 2) :: Q) G)
      with (HB [] 3 1 (2*1 + 6) ((8 - 2, 2) :: (4, 2) :: Q) G) by sec_eq.
    apply grind_round; lia. }
  replace (HB [] 3 1 8 ((6, 2) :: (4, 2) :: Q) G)
    with (HB [] 3 1 (2*2 + 4) ((6, 2) :: (4, 2) :: Q) G) by sec_eq.
  replace (HB [] 3 1 10 ((4, 2) :: (4, 2) :: Q) G)
    with (HB [] 3 1 (2*2 + 6) ((6 - 2, 2) :: (4, 2) :: Q) G) by sec_eq.
  apply grind_round; lia.
Qed.

(* Segment D: TUP + hGRIND_dev 3 at pb = []. *)
Lemma GRIND16_D : forall Q G,
  hsteps (HB [] 3 1 10 ((4, 2) :: (4, 2) :: Q) G)
         (HB [] 4 1 13 ((2, 2) :: (4, 2) :: Q) G).
Proof.
  intros Q G.
  apply (hsteps_trans _ (HC [] 3 9 2 ((2, 2) :: (4, 2) :: Q) G)).
  { apply (hsteps_step _ (HC [] 3 9 2 ((2, 2) :: (4, 2) :: Q) G)).
    { replace (HB [] 3 1 10 ((4, 2) :: (4, 2) :: Q) G)
        with (HB [] 3 1 (S (S 8)) ((S (S (S 1)), 2) :: (4, 2) :: Q) G)
        by sec_eq.
      replace (HC [] 3 9 2 ((2, 2) :: (4, 2) :: Q) G)
        with (HC [] 3 (S 8) 2 ((S 1, 2) :: (4, 2) :: Q) G) by sec_eq.
      apply hTUP. }
    apply hsteps_refl. }
  replace (HC [] 3 9 2 ((2, 2) :: (4, 2) :: Q) G)
    with (HC [] 3 (2*3 + 3) 2 ((2, 2) :: (4, 2) :: Q) G) by sec_eq.
  replace (HB [] 4 1 13 ((2, 2) :: (4, 2) :: Q) G)
    with (HB [] (S 3) 1 (2*3 + 7) ((2, 2) :: (4, 2) :: Q) G) by sec_eq.
  apply hGRIND_dev.
Qed.

(* Segment E: TUP2_1 re-bases to pb = [5], then TDN. *)
Lemma GRIND16_E : forall Q G,
  hsteps (HB [] 4 1 13 ((2, 2) :: (4, 2) :: Q) G)
         (HB [5] 13 1 4 ((2, 2) :: Q) G).
Proof.
  intros Q G.
  apply (hsteps_trans _ (HC [5] 13 1 2 ((2, 2) :: Q) G)).
  { apply (hsteps_step _ (HC [5] 13 1 2 ((2, 2) :: Q) G)).
    { replace (HB [] 4 1 13 ((2, 2) :: (4, 2) :: Q) G)
        with (HB [] 4 1 (S 12)
                ((2, S (S 0)) :: (S (S (S 1)), 2) :: Q) G)
        by sec_eq.
      replace (HC [5] 13 1 2 ((2, 2) :: Q) G)
        with (HC (S 4 :: []) (S 12) (S 0) 2 ((S 1, 2) :: Q) G)
        by sec_eq.
      apply hTUP2_1. }
    apply hsteps_refl. }
  apply (hsteps_step _ (HB [5] 13 1 4 ((2, 2) :: Q) G)).
  { apply hTDN. }
  apply hsteps_refl.
Qed.

(* The merged (16, 2) grind: segments A-E, then TRANS2_1 over the    *)
(* head of Rest's prefix (the (1, 1) :: (1, 2) :: (1, 2) extras and   *)
(* the spine), and the POP chain over the spine.  Rest itself is     *)
(* carried verbatim.                                                 *)
Lemma GRIND16_MID : forall n Rest,
  hsteps (HB [0] 3 1 2
            ((16, 2) :: (1, 1) :: (1, 2) :: (1, 2)
             :: (repeat (1, 2) n ++ Rest)) 1)
         (HB [14; 5] (n + 7) 1 (2*n + 7) Rest 1).
Proof.
  intros n Rest.
  apply (hsteps_trans _ (HB [0] 3 1 10 ((8, 2) :: (1, 1) :: (1, 2)
      :: (1, 2) :: (repeat (1, 2) n ++ Rest)) 1)).
  { apply GRIND16_A. }
  apply (hsteps_trans _ (HB [] 4 1 13 ((6, 2) :: (1, 1) :: (1, 2)
      :: (1, 2) :: (repeat (1, 2) n ++ Rest)) 1)).
  { apply GRIND16_B. }
  apply (hsteps_trans _ (HB [] 3 1 10 ((4, 2) :: (4, 2) :: (1, 1)
      :: (1, 2) :: (1, 2) :: (repeat (1, 2) n ++ Rest)) 1)).
  { apply GRIND16_C. }
  apply (hsteps_trans _ (HB [] 4 1 13 ((2, 2) :: (4, 2) :: (1, 1)
      :: (1, 2) :: (1, 2) :: (repeat (1, 2) n ++ Rest)) 1)).
  { apply GRIND16_D. }
  apply (hsteps_trans _ (HB [5] 13 1 4 ((2, 2) :: (1, 1) :: (1, 2)
      :: (1, 2) :: (repeat (1, 2) n ++ Rest)) 1)).
  { apply GRIND16_E. }
  apply (hsteps_trans _
    (HB [14; 5] 5 1 3 (repeat (1, 2) (S (S n)) ++ Rest) 1)).
  { apply (hsteps_step _
      (HB [14; 5] 5 1 3 (repeat (1, 2) (S (S n)) ++ Rest) 1)).
    { replace (HB [5] 13 1 4 ((2, 2) :: (1, 1) :: (1, 2) :: (1, 2)
                  :: (repeat (1, 2) n ++ Rest)) 1)
        with (HB [5] 13 1 (S 3)
                ((2, S 1) :: (1, 1) :: (1, 2) :: (1, 2)
                 :: (repeat (1, 2) n ++ Rest)) 1)
        by sec_eq.
      replace (HB [14; 5] 5 1 3 (repeat (1, 2) (S (S n)) ++ Rest) 1)
        with (HB (S 13 :: [5]) (S (S 3)) 1 (S 1 + 1)
                ((1, 2) :: (1, 2) :: (repeat (1, 2) n ++ Rest)) 1)
        by sec_eq.
      apply hTRANS2_1. lia. }
    apply hsteps_refl. }
  replace (HB [14; 5] (n + 7) 1 (2*n + 7) Rest 1)
    with (HB [14; 5] (5 + S (S n)) 1 (3 + 2 * S (S n)) Rest 1)
    by sec_eq.
  apply pop_chain_h_app. lia.
Qed.

(* ================================================================= *)
(*  Part 4: the common phase-3 chain, R = 2m + 46, m >= 35.          *)
(*  BIG2's prefix (ESC_GRIND_BIG, REBASE, grind_prefix, 12 clean     *)
(*  rounds, round13_dev5, pop3_12, TUP, hGRIND_even 15, TUP2_1,      *)
(*  TDN), then 34 phase-3 rounds (rounds_from4g), the final TUP,     *)
(*  DEV20_DESCEND 34, hPX2A0, and GRIND16_MID at spine 34.           *)
(* ================================================================= *)

Lemma PHASE3_DEEP : forall m beta, 35 <= m -> 2 <= beta ->
  hsteps (HC [] 3 1 2
            ((2*m + 46, 2) :: (1, 1) :: repeat (1, 2) (beta - 1)) 1)
         (HB [14; 5] 41 1 75
            ((2*m - 68, 2) :: (1, 1) :: repeat (1, 2) (beta - 1)) 1).
Proof.
  intros m beta Hm Hb.
  set (Pe := (1, 1) :: repeat (1, 2) (beta - 1)).
  apply (hsteps_trans _ (HC [] 4 12 2 ((2*m + 36, 2) :: Pe) 1)).
  { replace ((2*m + 46, 2) :: Pe)
      with ((2*m + 46, 2) :: Pe) by reflexivity.
    replace (2*m + 36) with (2*m + 46 - 10) by lia.
    apply ESC_GRIND_BIG. lia. }
  apply (hsteps_trans _ (HC [5] 13 1 2 ((2*m + 34, 2) :: Pe) 1)).
  { replace (2*m + 34) with (2*m + 36 - 2) by lia.
    apply REBASE. lia. }
  apply (hsteps_trans _ (HB [5] 13 1 6 ((2*m + 32, 2) :: Pe) 1)).
  { replace (HC [5] 13 1 2 ((2*m + 34, 2) :: Pe) 1)
      with (HC [5] (S 12) 1 2 ((S (S (S (2*m + 31))), 2) :: Pe) 1)
      by sec_eq.
    replace (HB [5] 13 1 6 ((2*m + 32, 2) :: Pe) 1)
      with (HB [5] (S 12) 1 6 ((S (2*m + 31), 2) :: Pe) 1)
      by sec_eq.
    apply grind_prefix. }
  apply (hsteps_trans _ (HB [5] 13 1 30 ((2*m + 8, 2) :: Pe) 1)).
  { replace (HB [5] 13 1 6 ((2*m + 32, 2) :: Pe) 1)
      with (HB [5] 13 1 (2*0 + 6) ((2*m + 32, 2) :: Pe) 1) by sec_eq.
    replace (HB [5] 13 1 30 ((2*m + 8, 2) :: Pe) 1)
      with (HB [5] 13 1 (2*(0 + 12) + 6) ((2*m + 32 - 2*12, 2) :: Pe) 1)
      by sec_eq.
    apply rounds_from6; lia. }
  apply (hsteps_trans _
    (HB [0] 17 1 29 ((1, 2) :: (1, 2) :: (1, 2)
        :: (2*m + 6, 2) :: Pe) 1)).
  { replace (HB [0] 17 1 29 ((1, 2) :: (1, 2) :: (1, 2)
        :: (2*m + 6, 2) :: Pe) 1)
      with (HB [0] 17 1 29 ((1, 2) :: (1, 2) :: (1, 2)
              :: (2*m + 8 - 2, 2) :: Pe) 1)
      by sec_eq.
    apply round13_dev5. lia. }
  apply (hsteps_trans _ (HB [0] 20 1 35 ((2*m + 6, 2) :: Pe) 1)).
  { replace (HB [0] 17 1 29 ((1, 2) :: (1, 2) :: (1, 2)
        :: (2*m + 6, 2) :: Pe) 1)
      with (HB [0] 17 1 29
              (repeat (1, 2) 3 ++ ((2*m + 6, 2) :: Pe)) 1)
      by sec_eq.
    replace (HB [0] 20 1 35 ((2*m + 6, 2) :: Pe) 1)
      with (HB [0] (17 + 3) 1 (29 + 2*3) ((2*m + 6, 2) :: Pe) 1)
      by sec_eq.
    apply pop_chain_h_app. lia. }
  apply (hsteps_trans _ (HC [0] 20 34 2 ((2*m + 4, 2) :: Pe) 1)).
  { apply (hsteps_step _ (HC [0] 20 34 2 ((2*m + 4, 2) :: Pe) 1)).
    { replace (HB [0] 20 1 35 ((2*m + 6, 2) :: Pe) 1)
        with (HB [0] 20 1 (S (S 33)) ((S (S (S (2*m + 3))), 2) :: Pe) 1)
        by sec_eq.
      replace (HC [0] 20 34 2 ((2*m + 4, 2) :: Pe) 1)
        with (HC [0] 20 (S 33) 2 ((S (2*m + 3), 2) :: Pe) 1) by sec_eq.
      apply hTUP. }
    apply hsteps_refl. }
  apply (hsteps_trans _ (HB [0] 19 1 34 ((2, 2) :: (2*m + 4, 2) :: Pe) 1)).
  { replace (HC [0] 20 34 2 ((2*m + 4, 2) :: Pe) 1)
      with (HC [0] (S 19) (2*15 + 4) 2 ((2*m + 4, 2) :: Pe) 1)
      by sec_eq.
    replace (HB [0] 19 1 34 ((2, 2) :: (2*m + 4, 2) :: Pe) 1)
      with (HB [0] 19 1 (2*15 + 4) ((2, 2) :: (2*m + 4, 2) :: Pe) 1)
      by sec_eq.
    apply hGRIND_even; lia. }
  apply (hsteps_trans _ (HC [20; 0] 34 1 2 ((2*m + 2, 2) :: Pe) 1)).
  { apply (hsteps_step _ (HC [20; 0] 34 1 2 ((2*m + 2, 2) :: Pe) 1)).
    { replace (HB [0] 19 1 34 ((2, 2) :: (2*m + 4, 2) :: Pe) 1)
        with (HB [0] 19 1 (S 33)
                ((2, S (S 0)) :: (S (S (S (2*m + 1))), 2) :: Pe) 1)
        by sec_eq.
      replace (HC [20; 0] 34 1 2 ((2*m + 2, 2) :: Pe) 1)
        with (HC (S 19 :: [0]) (S 33) (S 0) 2 ((S (2*m + 1), 2) :: Pe) 1)
        by sec_eq.
      apply hTUP2_1. }
    apply hsteps_refl. }
  apply (hsteps_trans _ (HB [20; 0] 34 1 4 ((2*m + 2, 2) :: Pe) 1)).
  { apply (hsteps_step _ (HB [20; 0] 34 1 4 ((2*m + 2, 2) :: Pe) 1)).
    { apply hTDN. }
    apply hsteps_refl. }
  apply (hsteps_trans _ (HB [20; 0] 34 1 72 ((2*m - 66, 2) :: Pe) 1)).
  { replace (HB [20; 0] 34 1 4 ((2*m + 2, 2) :: Pe) 1)
      with (HB [20; 0] 34 1 (2*0 + 4) ((2*m + 2, 2) :: Pe) 1)
      by sec_eq.
    replace (HB [20; 0] 34 1 72 ((2*m - 66, 2) :: Pe) 1)
      with (HB [20; 0] 34 1 (2*(0 + 34) + 4)
              ((2*m + 2 - 2*34, 2) :: Pe) 1) by sec_eq.
    apply rounds_from4g; lia. }
  apply (hsteps_trans _ (HC [20; 0] 34 71 2 ((2*m - 68, 2) :: Pe) 1)).
  { apply (hsteps_step _ (HC [20; 0] 34 71 2 ((2*m - 68, 2) :: Pe) 1)).
    { replace (HB [20; 0] 34 1 72 ((2*m - 66, 2) :: Pe) 1)
        with (HB [20; 0] 34 1 (S (S 70)) ((S (S (S (2*m - 69))), 2) :: Pe) 1)
        by sec_eq.
      replace (HC [20; 0] 34 71 2 ((2*m - 68, 2) :: Pe) 1)
        with (HC [20; 0] 34 (S 70) 2 ((S (2*m - 69), 2) :: Pe) 1)
        by sec_eq.
      apply hTUP. }
    apply hsteps_refl. }
  apply (hsteps_trans _
    (HC [20; 0] 0 3 2
        (repeat (1, 2) 34 ++ ((2*m - 68, 2) :: Pe)) 1)).
  { replace (HC [20; 0] 34 71 2 ((2*m - 68, 2) :: Pe) 1)
      with (HC [20; 0] 34 (2*34 + 3) 2 ((2*m - 68, 2) :: Pe) 1)
      by sec_eq.
    apply DEV20_DESCEND. }
  apply (hsteps_trans _
    (HB [0] 3 1 2 ((16, 2) :: (1, 1) :: (1, 2) :: (1, 2)
        :: (repeat (1, 2) 34 ++ ((2*m - 68, 2) :: Pe))) 1)).
  { apply (hsteps_step _
      (HB [0] 3 1 2 ((16, 2) :: (1, 1) :: (1, 2) :: (1, 2)
          :: (repeat (1, 2) 34 ++ ((2*m - 68, 2) :: Pe))) 1)).
    { replace (HC [20; 0] 0 3 2
          (repeat (1, 2) 34 ++ ((2*m - 68, 2) :: Pe)) 1)
        with (HC [20; 0] 0 3 2
                ((1, 2) :: (1, 2) :: (1, 2) :: (1, 2)
                 :: (repeat (1, 2) 30
                     ++ ((2*m - 68, 2) :: Pe))) 1)
        by sec_eq.
      replace (HB [0] 3 1 2 ((16, 2) :: (1, 1) :: (1, 2) :: (1, 2)
          :: (repeat (1, 2) 34 ++ ((2*m - 68, 2) :: Pe))) 1)
        with (HB [0] 3 1 2
                ((S 15, 2) :: (1, 1) :: (1, 2) :: (1, 2)
                 :: ((1, 2) :: (1, 2) :: (1, 2) :: (1, 2)
                     :: (repeat (1, 2) 30
                         ++ ((2*m - 68, 2) :: Pe)))) 1)
        by sec_eq.
      apply (hPX2A0 15 ((1, 2) :: (1, 2) :: (1, 2) :: (1, 2)
                     :: (repeat (1, 2) 30
                         ++ ((2*m - 68, 2) :: Pe)))
                    1). }
    apply hsteps_refl. }
  replace (HB [14; 5] 41 1 75 ((2*m - 68, 2) :: Pe) 1)
    with (HB [14; 5] (34 + 7) 1 (2*34 + 7) ((2*m - 68, 2) :: Pe) 1)
    by sec_eq.
  apply GRIND16_MID.
Qed.

(* ================================================================= *)
(*  Part 5: the endpoints.                                           *)
(* ================================================================= *)

(* R = 116 (m = 35): the (2, 2) landing is TAIL itself. *)
Lemma ESC_TO_REGEN_116 : forall beta, 2 <= beta ->
  exists pb a,
    hsteps (HC [] 3 1 2
              ((116, 2) :: (1, 1) :: repeat (1, 2) (beta - 1)) 1)
           (HB pb a 1 (2 * beta + 1) [] 1) /\ beta <= a.
Proof.
  intros beta Hb.
  pose proof (PHASE3_DEEP 35 beta ltac:(lia) Hb) as H.
  exists [42; 14; 5], (beta + 75). split; [| lia].
  apply (hsteps_trans _ (HB [14; 5] 41 1 75 ((2, 2)
      :: (1, 1) :: repeat (1, 2) (beta - 1)) 1)).
  { replace (116) with (2*35 + 46) by lia.
    replace ((2*35 - 68, 2) :: (1, 1) :: repeat (1, 2) (beta - 1))
      with ((2, 2) :: (1, 1) :: repeat (1, 2) (beta - 1)) by sec_eq.
    exact H. }
  replace (HB [42; 14; 5] (beta + 75) 1 (2 * beta + 1) [] 1)
    with (HB (S 41 :: [14; 5]) (75 + beta) 1 (2 * beta + 1) [] 1)
    by sec_eq.
  apply TAIL; lia.
Qed.

(* R = 118 (m = 36): TUP + hGRIND_even 35 + TRANS2_2 + pop_chain_h. *)
Lemma ESC_TO_REGEN_118 : forall beta, 2 <= beta ->
  exists pb a,
    hsteps (HC [] 3 1 2
              ((118, 2) :: (1, 1) :: repeat (1, 2) (beta - 1)) 1)
           (HB pb a 1 (2 * beta + 1) [] 1) /\ beta <= a.
Proof.
  intros beta Hb.
  pose proof (PHASE3_DEEP 36 beta ltac:(lia) Hb) as H.
  replace (2*36 + 46) with 118 in H by lia.
  replace (2*36 - 68) with 4 in H by lia.
  exists [75; 41; 14; 5], (beta + 2). split; [| lia].
  apply (hsteps_trans _ (HB [14; 5] 41 1 75 ((4, 2)
      :: (1, 1) :: repeat (1, 2) (beta - 1)) 1)); [exact H |].
  apply (hsteps_trans _ (HC [14; 5] 41 74 2 ((2, 2)
      :: (1, 1) :: repeat (1, 2) (beta - 1)) 1)).
  { apply (hsteps_step _ (HC [14; 5] 41 74 2 ((2, 2)
        :: (1, 1) :: repeat (1, 2) (beta - 1)) 1)).
    { replace (HB [14; 5] 41 1 75 ((4, 2)
          :: (1, 1) :: repeat (1, 2) (beta - 1)) 1)
        with (HB [14; 5] 41 1 (S (S 73)) ((S (S (S 1)), 2)
            :: (1, 1) :: repeat (1, 2) (beta - 1)) 1) by sec_eq.
      replace (HC [14; 5] 41 74 2 ((2, 2)
          :: (1, 1) :: repeat (1, 2) (beta - 1)) 1)
        with (HC [14; 5] 41 (S 73) 2 ((S 1, 2)
            :: (1, 1) :: repeat (1, 2) (beta - 1)) 1) by sec_eq.
      apply hTUP. }
    apply hsteps_refl. }
  apply (hsteps_trans _ (HB [14; 5] 40 1 74 ((2, 2) :: (2, 2)
      :: (1, 1) :: repeat (1, 2) (beta - 1)) 1)).
  { replace (HC [14; 5] 41 74 2 ((2, 2)
        :: (1, 1) :: repeat (1, 2) (beta - 1)) 1)
      with (HC [14; 5] (S 40) (2*35 + 4) 2 ((2, 2)
          :: (1, 1) :: repeat (1, 2) (beta - 1)) 1) by sec_eq.
    replace (HB [14; 5] 40 1 74 ((2, 2) :: (2, 2)
        :: (1, 1) :: repeat (1, 2) (beta - 1)) 1)
      with (HB [14; 5] 40 1 (2*35 + 4) ((2, 2) :: (2, 2)
          :: (1, 1) :: repeat (1, 2) (beta - 1)) 1) by sec_eq.
    apply hGRIND_even; lia. }
  apply (hsteps_trans _ (HB [75; 41; 14; 5] 3 1 3
      (repeat (1, 2) (beta - 1)) 1)).
  { apply (hsteps_step _ (HB [75; 41; 14; 5] 3 1 3
        (repeat (1, 2) (beta - 1)) 1)).
    { replace (HB [14; 5] 40 1 74 ((2, 2) :: (2, 2)
          :: (1, 1) :: repeat (1, 2) (beta - 1)) 1)
        with (HB [14; 5] 40 1 (S 73)
                ((2, S 1) :: (2, S 1) :: (1, 1)
                 :: repeat (1, 2) (beta - 1)) 1) by sec_eq.
      replace (HB [75; 41; 14; 5] 3 1 3 (repeat (1, 2) (beta - 1)) 1)
        with (HB (S (S 73) :: S 40 :: [14; 5]) (S (S 1)) 1 (S 1 + 1)
                (repeat (1, 2) (beta - 1)) 1) by sec_eq.
      apply hTRANS2_2. lia. }
    apply hsteps_refl. }
  replace (HB [75; 41; 14; 5] (beta + 2) 1 (2 * beta + 1) [] 1)
    with (HB [75; 41; 14; 5] (3 + (beta - 1)) 1 (3 + 2*(beta - 1)) [] 1)
    by sec_eq.
  apply pop_chain_h. lia.
Qed.

(* R = 120 (m = 37): TUP + hGRIND_even 35 + TUP2_1 + TDN + TAIL. *)
Lemma ESC_TO_REGEN_120 : forall beta, 2 <= beta ->
  exists pb a,
    hsteps (HC [] 3 1 2
              ((120, 2) :: (1, 1) :: repeat (1, 2) (beta - 1)) 1)
           (HB pb a 1 (2 * beta + 1) [] 1) /\ beta <= a.
Proof.
  intros beta Hb.
  pose proof (PHASE3_DEEP 37 beta ltac:(lia) Hb) as H.
  replace (2*37 + 46) with 120 in H by lia.
  replace (2*37 - 68) with 6 in H by lia.
  exists [75; 41; 14; 5], (beta + 4). split; [| lia].
  apply (hsteps_trans _ (HB [14; 5] 41 1 75 ((6, 2)
      :: (1, 1) :: repeat (1, 2) (beta - 1)) 1)); [exact H |].
  apply (hsteps_trans _ (HC [14; 5] 41 74 2 ((4, 2)
      :: (1, 1) :: repeat (1, 2) (beta - 1)) 1)).
  { apply (hsteps_step _ (HC [14; 5] 41 74 2 ((4, 2)
        :: (1, 1) :: repeat (1, 2) (beta - 1)) 1)).
    { replace (HB [14; 5] 41 1 75 ((6, 2)
          :: (1, 1) :: repeat (1, 2) (beta - 1)) 1)
        with (HB [14; 5] 41 1 (S (S 73)) ((S (S (S 3)), 2)
            :: (1, 1) :: repeat (1, 2) (beta - 1)) 1) by sec_eq.
      replace (HC [14; 5] 41 74 2 ((4, 2)
          :: (1, 1) :: repeat (1, 2) (beta - 1)) 1)
        with (HC [14; 5] 41 (S 73) 2 ((S 3, 2)
            :: (1, 1) :: repeat (1, 2) (beta - 1)) 1) by sec_eq.
      apply hTUP. }
    apply hsteps_refl. }
  apply (hsteps_trans _ (HB [14; 5] 40 1 74 ((2, 2) :: (4, 2)
      :: (1, 1) :: repeat (1, 2) (beta - 1)) 1)).
  { replace (HC [14; 5] 41 74 2 ((4, 2)
        :: (1, 1) :: repeat (1, 2) (beta - 1)) 1)
      with (HC [14; 5] (S 40) (2*35 + 4) 2 ((4, 2)
          :: (1, 1) :: repeat (1, 2) (beta - 1)) 1) by sec_eq.
    replace (HB [14; 5] 40 1 74 ((2, 2) :: (4, 2)
        :: (1, 1) :: repeat (1, 2) (beta - 1)) 1)
      with (HB [14; 5] 40 1 (2*35 + 4) ((2, 2) :: (4, 2)
          :: (1, 1) :: repeat (1, 2) (beta - 1)) 1) by sec_eq.
    apply hGRIND_even; lia. }
  apply (hsteps_trans _ (HC [41; 14; 5] 74 1 2 ((2, 2)
      :: (1, 1) :: repeat (1, 2) (beta - 1)) 1)).
  { apply (hsteps_step _ (HC [41; 14; 5] 74 1 2 ((2, 2)
        :: (1, 1) :: repeat (1, 2) (beta - 1)) 1)).
    { replace (HB [14; 5] 40 1 74 ((2, 2) :: (4, 2)
          :: (1, 1) :: repeat (1, 2) (beta - 1)) 1)
        with (HB [14; 5] 40 1 (S 73)
                ((2, S (S 0)) :: (S (S (S 1)), 2)
                 :: (1, 1) :: repeat (1, 2) (beta - 1)) 1) by sec_eq.
      replace (HC [41; 14; 5] 74 1 2 ((2, 2)
          :: (1, 1) :: repeat (1, 2) (beta - 1)) 1)
        with (HC (S 40 :: [14; 5]) (S 73) (S 0) 2 ((S 1, 2)
            :: (1, 1) :: repeat (1, 2) (beta - 1)) 1) by sec_eq.
      apply hTUP2_1. }
    apply hsteps_refl. }
  apply (hsteps_trans _ (HB [41; 14; 5] 74 1 4 ((2, 2)
      :: (1, 1) :: repeat (1, 2) (beta - 1)) 1)).
  { apply (hsteps_step _ (HB [41; 14; 5] 74 1 4 ((2, 2)
        :: (1, 1) :: repeat (1, 2) (beta - 1)) 1)).
    { apply hTDN. }
    apply hsteps_refl. }
  replace (HB [75; 41; 14; 5] (beta + 4) 1 (2 * beta + 1) [] 1)
    with (HB (S 74 :: [41; 14; 5]) (4 + beta) 1 (2 * beta + 1) [] 1)
    by sec_eq.
  apply TAIL; lia.
Qed.

(* R = 2m + 46, 38 <= m <= 111 (phase 5): after the m = 37 landing    *)
(* shape, rounds at ([41; 14; 5], 74) reduce the residue to (4, 2),   *)
(* TUP, a final clean hGRIND (m - 38) (floor m - 37 <= 74), TAIL.     *)
Lemma ESC_TO_REGEN_BIG3 : forall m beta, 38 <= m -> m <= 111 -> 2 <= beta ->
  exists pb a,
    hsteps (HC [] 3 1 2
              ((2*m + 46, 2) :: (1, 1) :: repeat (1, 2) (beta - 1)) 1)
           (HB pb a 1 (2 * beta + 1) [] 1) /\ beta <= a.
Proof.
  intros m beta Hm1 Hm2 Hb.
  pose proof (PHASE3_DEEP m beta ltac:(lia) Hb) as H.
  exists [75; 41; 14; 5], (2*m - 70 + beta). split; [| lia].
  apply (hsteps_trans _ (HB [14; 5] 41 1 75 ((2*m - 68, 2)
      :: (1, 1) :: repeat (1, 2) (beta - 1)) 1)); [exact H |].
  apply (hsteps_trans _ (HC [14; 5] 41 74 2 ((2*m - 70, 2)
      :: (1, 1) :: repeat (1, 2) (beta - 1)) 1)).
  { apply (hsteps_step _ (HC [14; 5] 41 74 2 ((2*m - 70, 2)
        :: (1, 1) :: repeat (1, 2) (beta - 1)) 1)).
    { replace (HB [14; 5] 41 1 75 ((2*m - 68, 2)
          :: (1, 1) :: repeat (1, 2) (beta - 1)) 1)
        with (HB [14; 5] 41 1 (S (S 73)) ((S (S (S (2*m - 71))), 2)
            :: (1, 1) :: repeat (1, 2) (beta - 1)) 1) by sec_eq.
      replace (HC [14; 5] 41 74 2 ((2*m - 70, 2)
          :: (1, 1) :: repeat (1, 2) (beta - 1)) 1)
        with (HC [14; 5] 41 (S 73) 2 ((S (2*m - 71), 2)
            :: (1, 1) :: repeat (1, 2) (beta - 1)) 1) by sec_eq.
      apply hTUP. }
    apply hsteps_refl. }
  apply (hsteps_trans _ (HB [14; 5] 40 1 74 ((2, 2) :: (2*m - 70, 2)
      :: (1, 1) :: repeat (1, 2) (beta - 1)) 1)).
  { replace (HC [14; 5] 41 74 2 ((2*m - 70, 2)
        :: (1, 1) :: repeat (1, 2) (beta - 1)) 1)
      with (HC [14; 5] (S 40) (2*35 + 4) 2 ((2*m - 70, 2)
          :: (1, 1) :: repeat (1, 2) (beta - 1)) 1) by sec_eq.
    replace (HB [14; 5] 40 1 74 ((2, 2) :: (2*m - 70, 2)
        :: (1, 1) :: repeat (1, 2) (beta - 1)) 1)
      with (HB [14; 5] 40 1 (2*35 + 4) ((2, 2) :: (2*m - 70, 2)
          :: (1, 1) :: repeat (1, 2) (beta - 1)) 1) by sec_eq.
    apply hGRIND_even; lia. }
  apply (hsteps_trans _ (HC [41; 14; 5] 74 1 2 ((2*m - 72, 2)
      :: (1, 1) :: repeat (1, 2) (beta - 1)) 1)).
  { apply (hsteps_step _ (HC [41; 14; 5] 74 1 2 ((2*m - 72, 2)
        :: (1, 1) :: repeat (1, 2) (beta - 1)) 1)).
    { replace (HB [14; 5] 40 1 74 ((2, 2) :: (2*m - 70, 2)
          :: (1, 1) :: repeat (1, 2) (beta - 1)) 1)
        with (HB [14; 5] 40 1 (S 73)
                ((2, S (S 0)) :: (S (S (S (2*m - 73))), 2)
                 :: (1, 1) :: repeat (1, 2) (beta - 1)) 1) by sec_eq.
      replace (HC [41; 14; 5] 74 1 2 ((2*m - 72, 2)
          :: (1, 1) :: repeat (1, 2) (beta - 1)) 1)
        with (HC (S 40 :: [14; 5]) (S 73) (S 0) 2
                ((S (2*m - 73), 2)
                 :: (1, 1) :: repeat (1, 2) (beta - 1)) 1) by sec_eq.
      apply hTUP2_1. }
    apply hsteps_refl. }
  apply (hsteps_trans _ (HB [41; 14; 5] 74 1 4 ((2*m - 72, 2)
      :: (1, 1) :: repeat (1, 2) (beta - 1)) 1)).
  { apply (hsteps_step _ (HB [41; 14; 5] 74 1 4 ((2*m - 72, 2)
        :: (1, 1) :: repeat (1, 2) (beta - 1)) 1)).
    { apply hTDN. }
    apply hsteps_refl. }
  apply (hsteps_trans _ (HB [41; 14; 5] 74 1 (2*m - 72) ((4, 2)
      :: (1, 1) :: repeat (1, 2) (beta - 1)) 1)).
  { replace (HB [41; 14; 5] 74 1 4 ((2*m - 72, 2)
        :: (1, 1) :: repeat (1, 2) (beta - 1)) 1)
      with (HB [41; 14; 5] 74 1 (2*0 + 4) ((2*m - 72, 2)
          :: (1, 1) :: repeat (1, 2) (beta - 1)) 1) by sec_eq.
    replace (HB [41; 14; 5] 74 1 (2*m - 72) ((4, 2)
        :: (1, 1) :: repeat (1, 2) (beta - 1)) 1)
      with (HB [41; 14; 5] 74 1 (2*(0 + (m - 38)) + 4)
              ((2*m - 72 - 2*(m - 38), 2)
               :: (1, 1) :: repeat (1, 2) (beta - 1)) 1) by sec_eq.
    apply rounds_from4g; lia. }
  apply (hsteps_trans _ (HC [41; 14; 5] 74 (2*m - 73) 2 ((2, 2)
      :: (1, 1) :: repeat (1, 2) (beta - 1)) 1)).
  { apply (hsteps_step _ (HC [41; 14; 5] 74 (2*m - 73) 2 ((2, 2)
        :: (1, 1) :: repeat (1, 2) (beta - 1)) 1)).
    { replace (HB [41; 14; 5] 74 1 (2*m - 72) ((4, 2)
          :: (1, 1) :: repeat (1, 2) (beta - 1)) 1)
        with (HB [41; 14; 5] 74 1 (S (S (2*m - 74)))
                ((S (S (S 1)), 2)
                 :: (1, 1) :: repeat (1, 2) (beta - 1)) 1) by sec_eq.
      replace (HC [41; 14; 5] 74 (2*m - 73) 2 ((2, 2)
          :: (1, 1) :: repeat (1, 2) (beta - 1)) 1)
        with (HC [41; 14; 5] 74 (S (2*m - 74)) 2 ((S 1, 2)
            :: (1, 1) :: repeat (1, 2) (beta - 1)) 1) by sec_eq.
      apply hTUP. }
    apply hsteps_refl. }
  apply (hsteps_trans _ (HB [41; 14; 5] 74 1 (2*m - 70) ((2, 2)
      :: (1, 1) :: repeat (1, 2) (beta - 1)) 1)).
  { replace (HC [41; 14; 5] 74 (2*m - 73) 2 ((2, 2)
        :: (1, 1) :: repeat (1, 2) (beta - 1)) 1)
      with (HC [41; 14; 5] 74 (2*(m - 38) + 3) 2 ((2, 2)
          :: (1, 1) :: repeat (1, 2) (beta - 1)) 1) by sec_eq.
    replace (HB [41; 14; 5] 74 1 (2*m - 70) ((2, 2)
        :: (1, 1) :: repeat (1, 2) (beta - 1)) 1)
      with (HB [41; 14; 5] 74 1 (2*(m - 38) + 6) ((2, 2)
          :: (1, 1) :: repeat (1, 2) (beta - 1)) 1) by sec_eq.
    apply hGRIND. lia. }
  replace (HB [75; 41; 14; 5] (2*m - 70 + beta) 1 (2 * beta + 1) [] 1)
    with (HB (S 74 :: [41; 14; 5]) (2*m - 70 + beta) 1 (2 * beta + 1) [] 1)
    by sec_eq.
  apply TAIL; lia.
Qed.

(* ================================================================= *)
(*  Part 6: the ESC-era law at R = 116 and through R = 268.          *)
(* ================================================================= *)

Lemma ESC_ERA_LAW_37 : forall R beta,
  (R = 116 \/ R = 118 \/ R = 120
   \/ (exists m, R = 2 * m + 46 /\ 38 <= m <= 111)) ->
  2 <= beta ->
  exists n c pb a, run n (esc_src (R + 6) (beta - 2)) = Some c
    /\ cfg_sim c (rcsec (false :: repeat true (S a) ++ enc pb)
                        (2 * beta + 2) [(1, 2)])
    /\ beta <= a.
Proof.
  intros R beta HR Hb.
  destruct HR as [E | [E | [E | [m [ER Hm]]]]].
  - subst R.
    destruct (ESC_TO_REGEN_116 beta Hb) as [pb [a [Hc Hf]]].
    apply (ESC_ERA_LAW_of 116 beta pb a);
      [lia | exact Hc | exact Hf | exact Hb].
  - subst R.
    destruct (ESC_TO_REGEN_118 beta Hb) as [pb [a [Hc Hf]]].
    apply (ESC_ERA_LAW_of 118 beta pb a);
      [lia | exact Hc | exact Hf | exact Hb].
  - subst R.
    destruct (ESC_TO_REGEN_120 beta Hb) as [pb [a [Hc Hf]]].
    apply (ESC_ERA_LAW_of 120 beta pb a);
      [lia | exact Hc | exact Hf | exact Hb].
  - subst R.
    destruct (ESC_TO_REGEN_BIG3 m beta ltac:(lia) ltac:(lia) Hb)
      as [pb [a [Hc Hf]]].
    apply (ESC_ERA_LAW_of (2 * m + 46) beta pb a);
      [lia | exact Hc | exact Hf | exact Hb].
Qed.

(* The ESC-era law for every even R <= 268: ESC_ERA_LAW_114's range *)
(* plus Phase 37's.  The new fence is at R >= 270 (m >= 112).       *)
Lemma ESC_ERA_LAW_268 : forall R beta,
  ((R = 2 \/ R = 4 \/ R = 6 \/ R = 8 \/ R = 10 \/ R = 12 \/ R = 14
    \/ (exists m, R = 2 * m + 16 /\ m <= 12)
    \/ R = 42 \/ R = 44 \/ (exists m, R = 2 * m + 46 /\ m <= 34))
   \/ (R = 116 \/ R = 118 \/ R = 120
       \/ (exists m, R = 2 * m + 46 /\ 38 <= m <= 111)))
  -> 2 <= beta ->
  exists n c pb a, run n (esc_src (R + 6) (beta - 2)) = Some c
    /\ cfg_sim c (rcsec (false :: repeat true (S a) ++ enc pb)
                        (2 * beta + 2) [(1, 2)])
    /\ beta <= a.
Proof.
  intros R beta [HOLD | HNEW] Hb.
  - apply (ESC_ERA_LAW_114 R beta); [exact HOLD | exact Hb].
  - apply (ESC_ERA_LAW_37 R beta); [exact HNEW | exact Hb].
Qed.

(* Axiom audit for this file's headline lemmas. *)
Print Assumptions DEV20_DESCEND.
Print Assumptions GRIND16_MID.
Print Assumptions PHASE3_DEEP.
Print Assumptions ESC_TO_REGEN_116.
Print Assumptions ESC_TO_REGEN_118.
Print Assumptions ESC_TO_REGEN_120.
Print Assumptions ESC_TO_REGEN_BIG3.
Print Assumptions ESC_ERA_LAW_37.
Print Assumptions ESC_ERA_LAW_268.
