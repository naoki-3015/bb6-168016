(* ================================================================= *)
(* EraGen.v -- component #18 at a general residue: ERA_GEN, the    *)
(* general-residue era law (phase19 SS2.3-2.4), Phase 35.          *)
(*                                                                 *)
(* Loop.v carries the general-residue era law as the explicit      *)
(* hypothesis ERA_GEN, in exactly ERA_LAW's shape with the         *)
(* residue rho as a parameter:                                     *)
(*                                                                 *)
(*   forall rho m, 1 <= m -> exists P' cost c,                     *)
(*     run cost (csec 16 rho 2 ((1, 1) :: repeat (1, 2) (m - 1)) 1)*)
(*       = Some c                                                  *)
(*     /\ cfg_sim c (rcsec P' (rho + 2 * m + 3) [(1, 2)]).         *)
(*                                                                 *)
(* ERA_LAW (Era.v) is the instance rho = 29.  This file proves     *)
(* the statement on the exact domain the machine requires:         *)
(*                                                                 *)
(*   ** rho odd, 1 <= rho <= 33, era parameter m >= 1. **          *)
(*                                                                 *)
(* The assembly is ERA_LAW's, with rho = 2t + 1 substituted:       *)
(*                                                                 *)
(*  1. Absorption of the residue gap.  For t >= 1 this is GRIND     *)
(*     at t - 1 (gap 2(t-1) + 3 = rho), floor t <= 16 at the fixed  *)
(*     frame a2 = 16 -- i.e. rho <= 33.  For t = 0 (rho = 1) the    *)
(*     absorption is a single TDN: a C-section with g0 = 1, s = 2  *)
(*     goes straight to the B-section with s = 4 = rho + 3.        *)
(*     Landing: bsec 16 1 (rho + 3) pairs 1.                       *)
(*  2. POP_CHAIN over the run list 1 :: 2^(m-1) (the defect pair    *)
(*     first, r1 = 1): s1 = (rho + 3) + 1 + 2(m - 1)               *)
(*     = rho + 2m + 2 (phase19 SS2.3: s1 = rho + 2 beta_E + 2),    *)
(*     frame a_f = m + 16.  The defect is load-bearing: it makes   *)
(*     s1 odd (rho odd), hence G0 = s1 - 1 even.                   *)
(*  3. REGEN (s1 >= 2): G0 = s1 - 1 = rho + 2m + 1                 *)
(*     = 2t + 2m + 2 in the (2t + 1)-parametrisation -- even.      *)
(*  4. TDN + the Stage-A era: s + G = rho + 2m + 5 invariant,      *)
(*     J = t + m cycles of Stage A + GRIND k; the GRIND floors     *)
(*     k + 1 <= m + 16 for k <= t + m - 1 are the same bound       *)
(*     t <= 16 again.  Final B-section:                            *)
(*     bsec (m + 16) 1 (rho + 2m + 3) [] 2 -- the entry source.    *)
(*  5. ENTRY_gen at P0 = []: beta' = rho + 2m + 5, i.e. the        *)
(*     landing rcsec argument is rho + 2m + 3, at the prefix       *)
(*     0 1^(m + 17).                                               *)
(*                                                                 *)
(* The two fences are exact, and both are pre-verified on the      *)
(* real machine (rocq/era_gen_verify.py, TM.v step semantics):     *)
(*                                                                 *)
(*  - rho >= 35 (odd): the residue grind's floor fails -- GRIND     *)
(*    at t - 1 = 16 would need floor 17 <= a2 = 16.  The grind's   *)
(*    dip is (rho - 1)/2 > 16 frame cells: at (rho, m) = (35, 1)   *)
(*    the absorption landing bsec 16 1 38 pairs 1 is NEVER         *)
(*    reached in 20,000,000 simulated steps (the boundary          *)
(*    sequence stalls at the start section).                       *)
(*  - rho even: Lemma G' is odd-only, and the era's parity is      *)
(*    load-bearing -- without the defect bookkeeping G0 would be   *)
(*    odd and the Stage-A era could not land on the G = 2 entry    *)
(*    source.  Numerically the failure is earlier still: at        *)
(*    (rho, m) = (30, 1) the absorption landing bsec 16 1 33       *)
(*    pairs 1 is NEVER reached in 20,000,000 steps.                *)
(*                                                                 *)
(* Positive pre-verification (same script): the full predicted     *)
(* boundary sequence is hit in order, with REGEN / TDN / Stage A   *)
(* / ENTRY deltas equal to the proved costs, at (rho, m) =         *)
(* (29, 2) [the ERA_LAW control], (27, 1), (27, 2), (31, 1),       *)
(* (31, 2), (33, 1) [domain boundary, floors at equality] and      *)
(* (1, 2) [absorption = TDN, delta 6].                             *)
(* ================================================================= *)

Require Import List Bool Arith Lia ZArith.
Import ListNotations.
Require Import TM Sections Mirror TokenPass Era.

(* ----------------------------------------------------------------- *)
(* ERA_GEN on its domain: rho odd, 1 <= rho <= 33.                   *)
(* ----------------------------------------------------------------- *)

Lemma ERA_GEN_proved : forall rho m,
  Nat.Odd rho -> rho <= 33 -> 1 <= m ->
  exists P' cost c,
    run cost (csec 16 rho 2 ((1, 1) :: repeat (1, 2) (m - 1)) 1) = Some c
    /\ cfg_sim c (rcsec P' (rho + 2 * m + 3) [(1, 2)]).
Proof.
  intros rho m Hodd Hrho Hm.
  destruct Hodd as [t Ht]. subst rho.
  assert (Ht16 : t <= 16) by lia.
  (* the canonical stack in POP_CHAIN (map) form *)
  assert (Hpairs : (1, 1) :: repeat (1, 2) (m - 1)
                   = map (fun r => (1, r)) (1 :: repeat 2 (m - 1))).
  { cbn [map]. rewrite map_repeat_2. reflexivity. }
  (* 1. Absorption: TDN at t = 0, GRIND (t - 1) at t >= 1;          *)
  (*    landing bsec 16 1 (2t + 4) pairs 1.                          *)
  assert (Habs : exists c, run c
    (csec 16 (2 * t + 1) 2 ((1, 1) :: repeat (1, 2) (m - 1)) 1)
    = Some (bsec 16 1 (2 * t + 4) ((1, 1) :: repeat (1, 2) (m - 1)) 1)).
  { destruct t as [|t'].
    - exists 6.
      replace (2 * 0 + 1) with 1 by lia.
      replace (2 * 0 + 4) with 4 by lia.
      apply TDN.
    - destruct (GRIND t' 16 ((1, 1) :: repeat (1, 2) (m - 1)) 1
                  ltac:(lia)) as [c1 Hc1].
      replace (2 * t' + 3) with (2 * S t' + 1) in Hc1 by lia.
      replace (2 * t' + 6) with (2 * S t' + 4) in Hc1 by lia.
      exists c1. exact Hc1. }
  destruct Habs as [c1 Hc1].
  (* 2. POP_CHAIN over the canonical stack: s1 = 2t + 2m + 3 *)
  rewrite Hpairs in Hc1.
  assert (Hin : forall r, In r (1 :: repeat 2 (m - 1)) -> 1 <= r).
  { intros r [-> | Hin]; [lia |].
    apply repeat_spec in Hin. lia. }
  destruct (POP_CHAIN (1 :: repeat 2 (m - 1)) 16 (2 * t + 4) 1 Hin
              ltac:(lia)) as [c2 Hc2].
  cbn [length] in Hc2.
  rewrite repeat_length in Hc2.
  cbn [rsum] in Hc2. rewrite rsum_repeat_2 in Hc2.
  replace (16 + S (m - 1)) with (m + 16) in Hc2 by lia.
  replace (2 * t + 4 + (1 + 2 * (m - 1))) with (2 * t + 2 * m + 3) in Hc2
    by lia.
  (* 3. REGEN *)
  pose proof (REGEN (m + 16) (2 * t + 2 * m + 3) ltac:(lia)) as Hc3eq.
  (* the REGEN landing, transferred to the clean csec form *)
  assert (Hsim3 : cfg_sim (csecR (m + 16) (2 * t + 2 * m + 3 - 1) [false])
                          (csec (m + 16) 1 2 [] (2 * t + 2 * m + 2))).
  { split; [reflexivity |].
    intros p.
    replace (2 * t + 2 * m + 3 - 1) with (S (2 * t + 2 * m + 1)) by lia.
    replace (2 * t + 2 * m + 2) with (S (2 * t + 2 * m + 1)) by lia.
    apply REGEN_tape. }
  (* 4. TDN into the Stage-A era *)
  assert (H4 : run 6 (csec (m + 16) 1 2 [] (2 * t + 2 * m + 2))
               = Some (bsec (m + 16) 1 4 [] (2 * t + 2 * m + 2)))
    by apply TDN.
  destruct (run_sim_transfer _ _ _ _ Hsim3 H4) as [c4 [Hc4 Hs4]].
  (* 5. the Stage-A era: s + G = 2t + 2m + 6, G even, down to G = 2 *)
  assert (Hiter : forall j k, k + j = t + m ->
    exists c, run c (bsec (m + 16) 1 (4 + 2 * k) [] (2 * t + 2 * m + 2 - 2 * k))
      = Some (bsec (m + 16) 1 (2 * t + 2 * m + 4) [] 2)).
  { induction j as [|j IHj]; intros k Hk.
    - exists 0.
      replace (4 + 2 * k) with (2 * t + 2 * m + 4) by lia.
      replace (2 * t + 2 * m + 2 - 2 * k) with 2 by lia.
      reflexivity.
    - assert (Hsa : run (2 * (4 + 2 * k) + 6)
                    (bsec (m + 16) 1 (4 + 2 * k) [] (2 * t + 2 * m + 2 - 2 * k))
                    = Some (csec (m + 16) (4 + 2 * k - 1) 2 []
                                 (2 * t + 2 * m + 2 - 2 * k - 2))).
      { apply StageA; lia. }
      replace (4 + 2 * k - 1) with (2 * k + 3) in Hsa by lia.
      replace (2 * t + 2 * m + 2 - 2 * k - 2) with (2 * t + 2 * m - 2 * k)
        in Hsa by lia.
      destruct (GRIND k (m + 16) [] (2 * t + 2 * m - 2 * k) ltac:(lia))
        as [cg Hg].
      destruct (IHj (k + 1) ltac:(lia)) as [c5 Hc5].
      replace (4 + 2 * (k + 1)) with (2 * k + 6) in Hc5 by lia.
      replace (2 * t + 2 * m + 2 - 2 * (k + 1)) with (2 * t + 2 * m - 2 * k)
        in Hc5 by lia.
      exists ((2 * (4 + 2 * k) + 6) + (cg + c5)).
      rewrite run_split. rewrite Hsa.
      rewrite run_split. rewrite Hg. exact Hc5. }
  destruct (Hiter (t + m) 0 ltac:(lia)) as [c6 Hc6].
  replace (4 + 2 * 0) with 4 in Hc6 by lia.
  replace (2 * t + 2 * m + 2 - 2 * 0) with (2 * t + 2 * m + 2) in Hc6
    by lia.
  (* compose 4+5 across the sim Hs4 *)
  destruct (run_sim_transfer _ _ _ _ Hs4 Hc6) as [c7 [Hc7 Hs7]].
  (* 6. ENTRY_gen at P0 = [] *)
  assert (H8 : run (2 * t + 2 * m + 16)
               (entry_src_gen [] (m + 16) (2 * t + 2 * m + 4))
               = Some (entry_tgt_gen [] (m + 16) (2 * t + 2 * m + 4))).
  { replace (2 * t + 2 * m + 16) with (S (2 * t + 2 * m + 3) + 12) by lia.
    replace (2 * t + 2 * m + 4) with (S (2 * t + 2 * m + 3)) by lia.
    apply ENTRY_gen. }
  rewrite bsec_entry_src in H8.
  destruct (run_sim_transfer _ _ _ _ Hs7 H8) as [c8 [Hc8 Hs8]].
  (* the TDN + era segment as one run from the REGEN landing *)
  assert (Hc47 : run (6 + c6) (csecR (m + 16) (2 * t + 2 * m + 3 - 1) [false])
                 = Some c7).
  { rewrite run_split. rewrite Hc4. exact Hc7. }
  (* compose everything *)
  exists (false :: repeat true (m + 17) ++ []).
  exists (c1 + (c2 + (4 * (2 * t + 2 * m + 3) + 22
                      + ((6 + c6) + (2 * t + 2 * m + 16))))).
  exists c8. split.
  - rewrite Hpairs.
    rewrite (run_split c1 (c2 + (4 * (2 * t + 2 * m + 3) + 22
                      + ((6 + c6) + (2 * t + 2 * m + 16))))).
    rewrite Hc1.
    rewrite (run_split c2 (4 * (2 * t + 2 * m + 3) + 22
                      + ((6 + c6) + (2 * t + 2 * m + 16)))).
    rewrite Hc2.
    rewrite (run_split (4 * (2 * t + 2 * m + 3) + 22)
                       ((6 + c6) + (2 * t + 2 * m + 16))).
    rewrite Hc3eq.
    rewrite (run_split (6 + c6) (2 * t + 2 * m + 16)).
    rewrite Hc47. exact Hc8.
  - replace (m + 17) with (S (m + 16)) by lia.
    replace (2 * t + 1 + 2 * m + 3) with (2 * t + 2 * m + 4) by lia.
    eapply cfg_sim_trans; [exact Hs8 |].
    apply entry_gen_sim.
Qed.

(* ----------------------------------------------------------------- *)
(* Axiom audit                                                       *)
(* ----------------------------------------------------------------- *)

Print Assumptions ERA_GEN_proved.
