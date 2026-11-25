(* ================================================================= *)
(* EraEven.v -- component #18 at an even residue: the even era     *)
(* law (Phase 39).                                                 *)
(*                                                                 *)
(* Loop.v's ERA_GEN is proved for odd rho <= 33 (EraGen.v).  This  *)
(* file proves the settled era at EVEN residues rho = B2 - 2, in   *)
(* the form the machine actually supports (derived from the        *)
(* machine, pre-verified in rocq/era_even_verify.py):              *)
(*                                                                 *)
(*   csec 16 rho 2 ((1,1) :: (1,2)^(m-1)) 1,  rho = 2k+2 even      *)
(*     --EVEN_GRIND (absorption)-->                                *)
(*   gbsec P0 rho 1 2 pairs 1,   P0 = [0] ++ 1^16                  *)
(*     --gPOP_CHAIN-->  gbsec P0 (rho+m) 1 (2m+1) [] 1             *)
(*     --REGEN_gen-->   gcsec P0 (rho+m) 1 2 [] (2m)               *)
(*     --gTDN + Stage-A era (gSTGA + gGRIND)-->                    *)
(*   gbsec P0 (rho+m) 1 (2m+2) [] 2                                *)
(*     --ENTRY_gen-->   rcsec P' (2m+2) [(1,2)]                    *)
(*                                                                 *)
(* The odd script cannot be reused: GRIND (Lemma G') is odd-only,  *)
(* and at an even gap the descent's residue pair reaches gap 2,    *)
(* where neither POP (gap 1) nor TUP (gap >= 3) applies.  What     *)
(* fires instead is the TUP-prefix excursion itself (Esc.v's       *)
(* gtup_prefix): a frame rotation that converts the residue gap    *)
(* into frame -- the absorption landing's near block is exactly    *)
(* rho, its s is 2 (not rho + 3).  Hence s1 = 2m + 1 (odd, so       *)
(* G0 = s1 - 1 = 2m is even and the Stage-A era lands on the       *)
(* G = 2 entry source) and beta' = 2m + 4 is INDEPENDENT of rho.   *)
(*                                                                 *)
(* EVEN_GRIND's floor is k <= a2 (the dip reaches a2 = 16 - k;     *)
(* at k = a2 the deepest PUSH lands on a C-section with a2 = 0,    *)
(* which POP -- not PUSH -- consumes).  At the era frame a2 = 16   *)
(* the domain is exactly even rho <= 34.                           *)
(*                                                                 *)
(* The frame-general rules used here already exist: gTDN, gPUSH,   *)
(* gPOP, gTUP, gSTGA (Grind.v Part 1), REGEN_gen / REGEN_gen_sim   *)
(* (Grind2.v), gtup_prefix (Esc.v).  New in this file: gPOP_CHAIN, *)
(* gGRIND (the odd grind over a general frame), gROT2 (the gap-2   *)
(* rotation as a section-to-section rule), ABS2 (the rho = 2       *)
(* absorption), EVEN_GRIND, and the assembly ERA_GEN_even.         *)
(* ================================================================= *)

Require Import List Bool Arith Lia ZArith Wf_nat.
Import ListNotations.
Require Import TM Sections Mirror TokenPass Recoord Era Esc Grind
               Grind2.

(* ----------------------------------------------------------------- *)
(* Conversions                                                       *)
(* ----------------------------------------------------------------- *)

Lemma bsec_gbsec_nil : forall a g0 s pairs G,
  bsec a g0 s pairs G = gbsec [] a g0 s pairs G.
Proof.
  intros. unfold bsec, gbsec. rewrite app_nil_r. reflexivity.
Qed.

Lemma gbsec_entry_src : forall P a s,
  gbsec P a 1 s [] 2 = entry_src_gen P a s.
Proof. intros. reflexivity. Qed.

(* ----------------------------------------------------------------- *)
(* gPOP_CHAIN: the POP chain over a general frame                    *)
(* ----------------------------------------------------------------- *)

Lemma gPOP_CHAIN : forall rs P a s G,
  (forall r, In r rs -> 1 <= r) -> 2 <= s ->
  exists c, run c (gbsec P a 1 s (map (fun r => (1, r)) rs) G)
    = Some (gbsec P (a + length rs) 1 (s + rsum rs) [] G).
Proof.
  induction rs as [|r rs IH]; intros P a s G Hr Hs.
  - exists 0. cbn [map length rsum].
    replace (a + 0) with a by lia.
    replace (s + 0) with s by lia.
    reflexivity.
  - assert (H1 : run (2 * s + 3)
                 (gbsec P a 1 s ((1, r) :: map (fun r0 => (1, r0)) rs) G)
                 = Some (gbsec P (S a) 1 (s + r)
                              (map (fun r0 => (1, r0)) rs) G))
      by (apply gPOP; [exact Hs | apply Hr; left; reflexivity]).
    destruct (IH P (S a) (s + r) G) as [c2 Hc2].
    { intros r0 Hin. apply Hr. right. exact Hin. }
    { lia. }
    exists ((2 * s + 3) + c2).
    cbn [map length rsum].
    replace (a + S (length rs)) with (S a + length rs) by lia.
    replace (s + (r + rsum rs)) with ((s + r) + rsum rs) by lia.
    rewrite run_split. rewrite H1. exact Hc2.
Qed.

(* ----------------------------------------------------------------- *)
(* gROT2: the gap-2 rotation.  From a B-section whose first pair   *)
(* has gap 2, the TUP-prefix excursion (Esc.gtup_prefix) lands on  *)
(* a B-section over the extended frame (0 :: 1^(a+1) ++ P): the    *)
(* shuttle s becomes the new near block, the pair is consumed,     *)
(* and the new shuttle is the pair's run r.                        *)
(* ----------------------------------------------------------------- *)

Lemma gROT2 : forall P a s' r1 rest G,
  run (S s' + 2) (gbsec P a 1 (S s') ((2, r1) :: rest) G)
  = Some (gbsec (false :: repeat true (S a) ++ P) (S s') 1 r1 rest G).
Proof.
  intros P a s' r1 rest G.
  exact (gtup_prefix P a s' r1 rest G).
Qed.

(* ----------------------------------------------------------------- *)
(* ABS2: the rho = 2 absorption.  A C-section with g0 = 2 (neither *)
(* TDN, g0 = 1, nor PUSH, g0 >= 3) runs a 3-step excursion         *)
(* (0RA, 1RA, 1RB) onto the rotated B-section with near block 2.   *)
(* ----------------------------------------------------------------- *)

Lemma ABS2 : forall a2 pairs G,
  run 3 (csec a2 2 2 pairs G)
  = Some (gbsec (false :: repeat true a2) 2 1 2 pairs G).
Proof. intros. reflexivity. Qed.

(* ----------------------------------------------------------------- *)
(* gGRIND: the Grind Lemma G' over a general frame (mirror of      *)
(* Era.GRIND with gPUSH / gTDN / gTUP / gPOP).                       *)
(* ----------------------------------------------------------------- *)

Lemma gGRIND : forall t Q a2 W G, t + 1 <= a2 ->
  exists c, run c (gcsec Q a2 (2*t + 3) 2 W G)
    = Some (gbsec Q a2 1 (2*t + 6) W G).
Proof.
  induction t as [t IH] using lt_wf_ind.
  intros Q a2 W G Hfloor.
  destruct t as [|u].
  - (* base: m = 3: PUSH + TDN + POP *)
    destruct a2 as [|a2']; try lia.
    assert (H1 : run 9 (gcsec Q (S a2') 3 2 W G)
                 = Some (gcsec Q a2' 1 2 ((1, 2) :: W) G)) by apply gPUSH.
    assert (H2 : run 6 (gcsec Q a2' 1 2 ((1, 2) :: W) G)
                 = Some (gbsec Q a2' 1 4 ((1, 2) :: W) G)) by apply gTDN.
    assert (H3 : run 11 (gbsec Q a2' 1 4 ((1, 2) :: W) G)
                 = Some (gbsec Q (S a2') 1 6 W G)).
    { replace 11 with (2 * 4 + 3) by lia.
      replace 6 with (4 + 2) by lia. apply gPOP; lia. }
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
      exists c, run c (gcsec Q a2' (2*i + 3) 2
                          ((2 * S u + 2 - (2*i + 3), 2) :: W) G)
        = Some (gcsec Q a2' (2 * S u + 1) 2 ((1, 2) :: W) G)).
    { induction k as [|k IHk]; intros i Hk Hi.
      - exists 0.
        replace (2 * S u + 2 - (2*i + 3)) with 1 by lia.
        replace (2*i + 3) with (2 * S u + 1) by lia.
        reflexivity.
      - destruct (IH i ltac:(lia) Q a2' ((2 * S u + 2 - (2*i + 3), 2) :: W) G
                      ltac:(lia))
          as [c1 Hc1].
        assert (H2 : exists c, run c
          (gbsec Q a2' 1 (2*i + 6) ((2 * S u + 2 - (2*i + 3), 2) :: W) G)
          = Some (gcsec Q a2' (2*(i + 1) + 3) 2
                       ((2 * S u + 2 - (2*(i + 1) + 3), 2) :: W) G)).
        { exists (2 * S (S (2*i + 4)) + 6).
          replace (gbsec Q a2' 1 (2*i + 6) ((2 * S u + 2 - (2*i + 3), 2) :: W) G)
            with (gbsec Q a2' 1 (S (S (2*i + 4)))
                       ((S (S (S (2*u - 2*i - 2))), 2) :: W) G)
            by (repeat f_equal; try reflexivity; lia).
          replace (gcsec Q a2' (2*(i + 1) + 3) 2
                       ((2 * S u + 2 - (2*(i + 1) + 3), 2) :: W) G)
            with (gcsec Q a2' (S (2*i + 4)) 2 ((S (2*u - 2*i - 2), 2) :: W) G)
            by (repeat f_equal; try reflexivity; lia).
          apply gTUP. }
        destruct H2 as [c2 Hc2].
        destruct (IHk (i + 1) ltac:(lia) ltac:(lia)) as [c3 Hc3].
        exists (c1 + (c2 + c3)).
        rewrite run_split. rewrite Hc1.
        rewrite run_split. rewrite Hc2. exact Hc3. }
    (* prefix *)
    assert (H1 : run 9 (gcsec Q (S a2') (2 * S u + 3) 2 W G)
                 = Some (gcsec Q a2' 1 2 ((2 * S u + 1, 2) :: W) G)).
    { replace (2 * S u + 3) with (S (S (S (2 * S u)))) by lia.
      replace (2 * S u + 1) with (S (2 * S u)) by lia.
      apply gPUSH. }
    assert (H2 : run 6 (gcsec Q a2' 1 2 ((2 * S u + 1, 2) :: W) G)
                 = Some (gbsec Q a2' 1 4 ((2 * S u + 1, 2) :: W) G))
      by apply gTDN.
    assert (H3 : run 14 (gbsec Q a2' 1 4 ((2 * S u + 1, 2) :: W) G)
                 = Some (gcsec Q a2' 3 2 ((2 * S u - 1, 2) :: W) G)).
    { replace (gbsec Q a2' 1 4 ((2 * S u + 1, 2) :: W) G)
        with (gbsec Q a2' 1 (S (S 2)) ((S (S (S (2 * u))), 2) :: W) G)
        by (repeat f_equal; try reflexivity; lia).
      replace (gcsec Q a2' 3 2 ((2 * S u - 1, 2) :: W) G)
        with (gcsec Q a2' (S 2) 2 ((S (2 * u), 2) :: W) G)
        by (repeat f_equal; try reflexivity; lia).
      replace 14 with (2 * S (S 2) + 6) by lia.
      apply gTUP. }
    destruct (Hloop u 0 ltac:(lia) ltac:(lia)) as [c4 Hc4].
    replace (2 * S u + 2 - (2*0 + 3)) with (2 * S u - 1) in Hc4 by lia.
    replace (2*0 + 3) with 3 in Hc4 by lia.
    destruct (IH u ltac:(lia) Q a2' ((1, 2) :: W) G ltac:(lia)) as [c5 Hc5].
    replace (2*u + 3) with (2 * S u + 1) in Hc5 by lia.
    replace (2*u + 6) with (2 * S u + 4) in Hc5 by lia.
    assert (H6 : run (2 * (2 * S u + 4) + 3)
                 (gbsec Q a2' 1 (2 * S u + 4) ((1, 2) :: W) G)
                 = Some (gbsec Q (S a2') 1 (2 * S u + 6) W G)).
    { replace (2 * S u + 6) with ((2 * S u + 4) + 2) by lia.
      apply gPOP; lia. }
    exists (9 + (6 + (14 + (c4 + (c5 + (2 * (2 * S u + 4) + 3)))))).
    rewrite run_split. rewrite H1.
    rewrite run_split. rewrite H2.
    rewrite run_split. rewrite H3.
    rewrite run_split. rewrite Hc4.
    rewrite run_split. rewrite Hc5. exact H6.
Qed.

Lemma gbsec_rot_clean : forall n a g0 s pairs G,
  gbsec (false :: repeat true n ++ []) a g0 s pairs G
  = gbsec (false :: repeat true n) a g0 s pairs G.
Proof.
  intros. unfold gbsec. rewrite app_nil_r. reflexivity.
Qed.

(* ----------------------------------------------------------------- *)
(* EVEN_GRIND: the even absorption.  A C-section with even gap     *)
(* 2k+2 grinds to the rotated B-section over the extended frame    *)
(* (0 :: 1^A): near block 2k+2, s = 2, stack and G unchanged.      *)
(* Floor k <= A (the dip reaches a2 = A - k).                      *)
(*                                                                 *)
(* Structure: k = 0 is ABS2.  For k >= 1: PUSH + TDN; at k = 1     *)
(* the residue pair is already (2, 2) and gROT2 closes.  For       *)
(* k >= 2: TUP, then the climb (GRIND i; TUP) with the residue     *)
(* pair descending 2k-2, 2k-4, ..., 2 -- the odd GRIND's loop      *)
(* with the roles shifted -- and gROT2 at the (2, 2) pair.         *)
(* ----------------------------------------------------------------- *)

Lemma EVEN_GRIND : forall k A W G, k <= A ->
  exists c, run c (csec A (2*k + 2) 2 W G)
    = Some (gbsec (false :: repeat true A) (2*k + 2) 1 2 W G).
Proof.
  intros k A W G HkA.
  destruct k as [|k'].
  - exists 3. replace (2 * 0 + 2) with 2 by lia. apply ABS2.
  - destruct A as [|A']; [lia |].
    (* PUSH: residue pair (2 * S k', 2) pushed *)
    assert (H1 : run 9 (csec (S A') (2 * S k' + 2) 2 W G)
                 = Some (csec A' 1 2 ((2 * S k', 2) :: W) G)).
    { replace (2 * S k' + 2) with (S (S (S (2 * k' + 1)))) by lia.
      replace (2 * S k') with (S (2 * k' + 1)) by lia.
      apply PUSH. }
    assert (H2 : run 6 (csec A' 1 2 ((2 * S k', 2) :: W) G)
                 = Some (bsec A' 1 4 ((2 * S k', 2) :: W) G))
      by apply TDN.
    destruct k' as [|k''].
    + (* k = 1: the residue pair is (2, 2); rotate *)
      assert (Hrot : run (4 + 2) (bsec A' 1 4 ((2, 2) :: W) G)
                     = Some (gbsec (false :: repeat true (S A'))
                                   4 1 2 W G)).
      { rewrite bsec_gbsec_nil.
        replace 4 with (S 3) by lia.
        rewrite <- gbsec_rot_clean.
        apply gROT2. }
      exists (9 + (6 + (4 + 2))).
      rewrite run_split. rewrite H1.
      rewrite run_split. rewrite H2. exact Hrot.
    + (* k >= 2: TUP, the climb, the rotation *)
      assert (H3 : run 14 (bsec A' 1 4 ((2 * S (S k''), 2) :: W) G)
                   = Some (csec A' 3 2 ((2 * k'' + 2, 2) :: W) G)).
      { replace (bsec A' 1 4 ((2 * S (S k''), 2) :: W) G)
          with (bsec A' 1 (S (S 2)) ((S (S (S (2 * k'' + 1))), 2) :: W) G)
          by (repeat f_equal; try reflexivity; lia).
        replace (csec A' 3 2 ((2 * k'' + 2, 2) :: W) G)
          with (csec A' (S 2) 2 ((S (2 * k'' + 1), 2) :: W) G)
          by (repeat f_equal; try reflexivity; lia).
        replace 14 with (2 * S (S 2) + 6) by lia.
        apply TUP. }
      (* the climb: GRIND i + TUP, residue descending to 2 *)
      assert (Hclimb : forall j i,
        2*i + 3 + 2*j = 2 * k'' + 3 -> i + 1 <= A' ->
        exists c, run c (csec A' (2*i + 3) 2
                            ((2 * k'' + 2 - 2*i, 2) :: W) G)
          = Some (bsec A' 1 (2 * k'' + 6) ((2, 2) :: W) G)).
      { induction j as [|j IHj]; intros i Hj Hi.
        - (* i = k'': GRIND k'' lands on the (2, 2) pair *)
          destruct (GRIND i A' ((2 * k'' + 2 - 2*i, 2) :: W) G
                          ltac:(lia)) as [c1 Hc1].
          assert (Hc1' : run c1 (csec A' (2*i + 3) 2
                                   ((2 * k'' + 2 - 2*i, 2) :: W) G)
                         = Some (bsec A' 1 (2 * k'' + 6) ((2, 2) :: W) G)).
          { replace (2 * k'' + 6) with (2*i + 6) by lia.
            replace ((2, 2) :: W) with ((2 * k'' + 2 - 2*i, 2) :: W)
              by (repeat f_equal; lia).
            exact Hc1. }
          exists c1. exact Hc1'.
        - (* GRIND i, then TUP, then continue at i + 1 *)
          destruct (GRIND i A' ((2 * k'' + 2 - 2*i, 2) :: W) G
                          ltac:(lia)) as [c1 Hc1].
          assert (H2' : exists c, run c
            (bsec A' 1 (2*i + 6) ((2 * k'' + 2 - 2*i, 2) :: W) G)
            = Some (csec A' (2*(i + 1) + 3) 2
                         ((2 * k'' + 2 - 2*(i + 1), 2) :: W) G)).
          { exists (2 * S (S (2*i + 4)) + 6).
            replace (bsec A' 1 (2*i + 6) ((2 * k'' + 2 - 2*i, 2) :: W) G)
              with (bsec A' 1 (S (S (2*i + 4)))
                         ((S (S (S (2 * k'' - 2*i - 1))), 2) :: W) G)
              by (repeat f_equal; try reflexivity; lia).
            replace (csec A' (2*(i + 1) + 3) 2
                         ((2 * k'' + 2 - 2*(i + 1), 2) :: W) G)
              with (csec A' (S (2*i + 4)) 2
                         ((S (2 * k'' - 2*i - 1), 2) :: W) G)
              by (repeat f_equal; try reflexivity; lia).
            apply TUP. }
          destruct H2' as [c2 Hc2].
          destruct (IHj (i + 1) ltac:(lia) ltac:(lia)) as [c3 Hc3].
          exists (c1 + (c2 + c3)).
          rewrite run_split. rewrite Hc1.
          rewrite run_split. rewrite Hc2. exact Hc3. }
      destruct (Hclimb k'' 0 ltac:(lia) ltac:(lia)) as [c4 Hc4].
      replace (2 * k'' + 2 - 2 * 0) with (2 * k'' + 2) in Hc4 by lia.
      replace (2 * 0 + 3) with 3 in Hc4 by lia.
      (* the rotation at the (2, 2) pair *)
      assert (Hrot : run (2 * k'' + 6 + 2)
                       (bsec A' 1 (2 * k'' + 6) ((2, 2) :: W) G)
                     = Some (gbsec (false :: repeat true (S A'))
                                   (2 * S (S k'') + 2) 1 2 W G)).
      { replace (2 * S (S k'') + 2) with (2 * k'' + 6) by lia.
        rewrite bsec_gbsec_nil.
        replace (2 * k'' + 6) with (S (2 * k'' + 5)) by lia.
        rewrite <- gbsec_rot_clean.
        apply gROT2. }
      exists (9 + (6 + (14 + (c4 + (2 * k'' + 6 + 2))))).
      rewrite run_split. rewrite H1.
      rewrite run_split. rewrite H2.
      rewrite run_split. rewrite H3.
      rewrite run_split. rewrite Hc4. exact Hrot.
Qed.

Lemma map_repeat_pair2 : forall n,
  map (fun r => (1, r)) (repeat 2 n) = repeat (1, 2) n.
Proof.
  induction n as [|n IHn]; cbn [repeat map];
    [reflexivity | rewrite IHn; reflexivity].
Qed.

(* ----------------------------------------------------------------- *)
(* ERA_GEN_even: the settled era at an even residue.  For every    *)
(* even rho = 2k+2 <= 34 (k <= 16, the era frame) and every        *)
(* m >= 1, the era source runs to a config similar to the mirror   *)
(* section rcsec P' (2m+2) [(1, 2)]: beta' = 2m + 4, independent   *)
(* of rho.  (Loop.v uses it at m = n + 2.)                         *)
(* ----------------------------------------------------------------- *)

Lemma ERA_GEN_even : forall k m, k <= 16 -> 1 <= m ->
  exists P' cost c,
    run cost (csec 16 (2 * k + 2) 2 ((1, 1) :: repeat (1, 2) (m - 1)) 1)
      = Some c /\
    cfg_sim c (rcsec P' (2 * m + 2) [(1, 2)]).
Proof.
  intros k m Hk Hm.
  (* 1. absorption *)
  destruct (EVEN_GRIND k 16 ((1, 1) :: repeat (1, 2) (m - 1)) 1 Hk)
    as [c1 Hc1].
  (* 2. POP chain: s1 = 2m + 1 *)
  assert (Hmap : map (fun r => (1, r)) (1 :: repeat 2 (m - 1))
                 = (1, 1) :: repeat (1, 2) (m - 1)).
  { cbn [map]. rewrite map_repeat_pair2. reflexivity. }
  assert (Hin : forall r, In r (1 :: repeat 2 (m - 1)) -> 1 <= r).
  { intros r [-> | Hin]; [lia |].
    apply repeat_spec in Hin. lia. }
  destruct (gPOP_CHAIN (1 :: repeat 2 (m - 1))
              (false :: repeat true 16) (2 * k + 2) 2 1 Hin ltac:(lia))
    as [c2 Hc2].
  cbn [length] in Hc2.
  rewrite repeat_length in Hc2.
  cbn [rsum] in Hc2. rewrite rsum_repeat_2 in Hc2.
  replace (2 * k + 2 + S (m - 1)) with (2 * k + m + 2) in Hc2 by lia.
  replace (2 + (1 + 2 * (m - 1))) with (2 * m + 1) in Hc2 by lia.
  assert (Hc2' : run c2 (gbsec (false :: repeat true 16) (2 * k + 2)
                              1 2 ((1, 1) :: repeat (1, 2) (m - 1)) 1)
                 = Some (gbsec (false :: repeat true 16) (2 * k + m + 2)
                               1 (2 * m + 1) [] 1)).
  { rewrite <- Hmap. exact Hc2. }
  (* 3. REGEN *)
  pose proof (REGEN_gen (false :: repeat true 16) (2 * k + m + 2)
                (2 * m + 1) ltac:(lia)) as Hc3eq.
  replace (2 * m + 1 - 1) with (2 * m) in Hc3eq by lia.
  pose proof (REGEN_gen_sim (false :: repeat true 16) (2 * k + m + 2)
                (2 * m)) as Hsim3.
  (* 4. gTDN into the Stage-A era *)
  assert (H4 : run 6 (gcsec (false :: repeat true 16) (2 * k + m + 2)
                            1 2 [] (2 * m))
               = Some (gbsec (false :: repeat true 16) (2 * k + m + 2)
                            1 4 [] (2 * m)))
    by apply gTDN.
  destruct (run_sim_transfer _ _ _ _ Hsim3 H4) as [c4 [Hc4 Hs4]].
  (* 5. the Stage-A era: s + G = 2m + 4, G even, down to G = 2 *)
  assert (Hiter : forall j kk, kk + j = m - 1 ->
    exists c, run c (gbsec (false :: repeat true 16) (2 * k + m + 2)
                           1 (4 + 2 * kk) [] (2 * m - 2 * kk))
      = Some (gbsec (false :: repeat true 16) (2 * k + m + 2)
                    1 (2 * m + 2) [] 2)).
  { induction j as [|j IHj]; intros kk Hkk.
    - exists 0.
      replace (4 + 2 * kk) with (2 * m + 2) by lia.
      replace (2 * m - 2 * kk) with 2 by lia.
      reflexivity.
    - assert (Hsa : run (2 * (4 + 2 * kk) + 6)
                    (gbsec (false :: repeat true 16) (2 * k + m + 2)
                           1 (4 + 2 * kk) [] (2 * m - 2 * kk))
                    = Some (gcsec (false :: repeat true 16) (2 * k + m + 2)
                                  (4 + 2 * kk - 1) 2 []
                                  (2 * m - 2 * kk - 2))).
      { apply gSTGA; lia. }
      replace (4 + 2 * kk - 1) with (2 * kk + 3) in Hsa by lia.
      destruct (gGRIND kk (false :: repeat true 16) (2 * k + m + 2) []
                  (2 * m - 2 * kk - 2) ltac:(lia)) as [cg Hg].
      destruct (IHj (kk + 1) ltac:(lia)) as [c5 Hc5].
      replace (4 + 2 * (kk + 1)) with (2 * kk + 6) in Hc5 by lia.
      replace (2 * m - 2 * (kk + 1)) with (2 * m - 2 * kk - 2) in Hc5
        by lia.
      exists ((2 * (4 + 2 * kk) + 6) + (cg + c5)).
      rewrite run_split. rewrite Hsa.
      rewrite run_split. rewrite Hg. exact Hc5. }
  destruct (Hiter (m - 1) 0 ltac:(lia)) as [c6 Hc6].
  replace (4 + 2 * 0) with 4 in Hc6 by lia.
  replace (2 * m - 2 * 0) with (2 * m) in Hc6 by lia.
  (* compose 4+5 across the sim Hs4 *)
  destruct (run_sim_transfer _ _ _ _ Hs4 Hc6) as [c7 [Hc7 Hs7]].
  (* 6. ENTRY_gen *)
  assert (H8 : run (2 * m + 14)
               (gbsec (false :: repeat true 16) (2 * k + m + 2)
                      1 (2 * m + 2) [] 2)
               = Some (entry_tgt_gen (false :: repeat true 16)
                          (2 * k + m + 2) (2 * m + 2))).
  { replace (2 * m + 14) with (S (2 * m + 1) + 12) by lia.
    replace (2 * m + 2) with (S (2 * m + 1)) by lia.
    rewrite gbsec_entry_src.
    apply ENTRY_gen. }
  destruct (run_sim_transfer _ _ _ _ Hs7 H8) as [c8 [Hc8 Hs8]].
  (* the gTDN + era segment as one run from the REGEN landing *)
  assert (Hc47 : run (6 + c6)
                   (gcsecR (false :: repeat true 16) (2 * k + m + 2)
                           (2 * m) [false])
                 = Some c7).
  { rewrite run_split. rewrite Hc4. exact Hc7. }
  (* compose everything *)
  exists (false :: repeat true (S (2 * k + m + 2))
                 ++ (false :: repeat true 16)).
  exists (c1 + (c2 + (4 * (2 * m + 1) + 22
                      + ((6 + c6) + (2 * m + 14))))).
  exists c8. split.
  - rewrite (run_split c1 (c2 + (4 * (2 * m + 1) + 22
                      + ((6 + c6) + (2 * m + 14))))).
    rewrite Hc1.
    rewrite (run_split c2 (4 * (2 * m + 1) + 22
                      + ((6 + c6) + (2 * m + 14)))).
    rewrite Hc2'.
    rewrite (run_split (4 * (2 * m + 1) + 22)
                       ((6 + c6) + (2 * m + 14))).
    rewrite Hc3eq.
    rewrite (run_split (6 + c6) (2 * m + 14)).
    rewrite Hc47. exact Hc8.
  - eapply cfg_sim_trans; [exact Hs8 |].
    apply entry_gen_sim.
Qed.

(* ----------------------------------------------------------------- *)
(* Axiom audit                                                       *)
(* ----------------------------------------------------------------- *)

Print Assumptions gPOP_CHAIN.
Print Assumptions gROT2.
Print Assumptions ABS2.
Print Assumptions gGRIND.
Print Assumptions EVEN_GRIND.
Print Assumptions ERA_GEN_even.
