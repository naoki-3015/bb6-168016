(* ================================================================= *)
(*  Dev.v -- Phase 28: the deviation forms of phase21-derivations    *)
(*  mechanised (component #19).                                      *)
(*                                                                   *)
(*  Contents:                                                        *)
(*  - chain units: rep_turn, gturn, gunit2 (+ _mk folded variants),  *)
(*    gtup_prefix_mk;                                                *)
(*  - PUSHX (core + g = 3 closing + general-g TUP follow-on);        *)
(*  - PX2A (general b >= 3) and PX2A_b2 (the b = 2 special form);    *)
(*  - PX2B rows b = 2..6 (b >= 7 is Esc.PROBE_PREFIX);               *)
(*  - CGAP2 probe + C-POP / C-PUSH dispatches (totals 10 / 13);      *)
(*  - TUP2 chain k = 1 (all r1), TRANS2 turns k = 1, 2;              *)
(*  - TUP2 defect (k = 1, r1 = 1): merge + F-step + TAIL13, with     *)
(*    the MACHINE-corrected landing (see NOTES Phase 28 / F-3).      *)
(*  - Phase 36 additions: PX2A0 (the [b; 0] dip bottom, b >= 5)     *)
(*    and PX2B0 (the [0] dip bottom).                                *)
(*  All lemmas are for all parameters (abstract pairs / G / tails).  *)
(* ================================================================= *)

Require Import List Bool Arith Lia ZArith.
Import ListNotations.
Require Import TM Sections Mirror TokenPass Recoord Era Esc.

Lemma rep_turn : forall r r'' (l : list sym),
  repeat (true : sym) r ++ (true :: repeat true r'' ++ l) =
  repeat (true : sym) (r + S r'') ++ l.
Proof.
  intros r r'' l. rewrite (Sections.rep_app true r (S r'')).
  change (repeat true (S r'')) with (true :: repeat true r'').
  rewrite <- app_assoc. reflexivity.
Qed.

Lemma gturn_step : forall P'' r r'' rest G,
  run 1 (mkCfg SB (false :: P'')
           (repeat true r ++ (true :: repeat true r'' ++ tail rest G))) =
  Some (mkCfg SB P'' (false :: (repeat true (r + S r'') ++ tail rest G))).
Proof.
  intros P'' r r'' rest G. rewrite run_1.
  destruct r as [| r'''].
  - reflexivity.
  - unfold step, read. cbn [cleft cright trans].
    f_equal. f_equal. rewrite rep_turn.
    replace (S r''' + S r'') with (S (r''' + S r'')) by lia.
    reflexivity.
Qed.

Lemma gturn : forall P'' r r' rest G, 1 <= r' ->
  run (r + 1)
    (mkCfg SB (repeat true r ++ (false :: P'')) (repeat true r' ++ tail rest G)) =
  Some (mkCfg SB P'' (false :: (repeat true (r + r') ++ tail rest G))).
Proof.
  intros P'' r r' rest G Hr'.
  rewrite run_split.
  destruct r' as [| r'']; [lia |].
  change (repeat true (S r'') ++ tail rest G)
    with (true :: (repeat true r'' ++ tail rest G)).
  rewrite sweepB. cbv beta iota.
  apply gturn_step.
Qed.

Lemma gunit2 : forall P' s r' r2 rest G,
  run (S r' + 2)
    (mkCfg SB (repeat true s ++ P')
       (false :: (repeat true (S r') ++
         (repeat false 1 ++ (repeat true r2 ++ tail rest G))))) =
  Some (mkCfg SB (repeat true (S r') ++ (false :: repeat true (S s) ++ P'))
                 (repeat true r2 ++ tail rest G)).
Proof.
  intros P' s r' r2 rest G.
  replace (S r' + 2) with (2 + (r' + 1)) by lia.
  rewrite run_split.
  assert (H2 : run 2
    (mkCfg SB (repeat true s ++ P')
       (false :: (repeat true (S r') ++
         (repeat false 1 ++ (repeat true r2 ++ tail rest G))))) =
    Some (mkCfg SA (false :: repeat true (S s) ++ P')
       (repeat true r' ++
         (repeat false 1 ++ (repeat true r2 ++ tail rest G))))).
  { reflexivity. }
  rewrite H2. cbv beta iota.
  rewrite run_split.
  rewrite sweepA. cbv beta iota.
  reflexivity.
Qed.

Lemma gtup_prefix_mk : forall P' a' s' r1 rest G,
  run (S s' + 2)
    (mkCfg SB (repeat true a' ++ P')
       (repeat false 1 ++ (repeat true (S s') ++
         tail ((2, r1) :: rest) G))) =
  Some (mkCfg SB (repeat true (S s') ++ (false :: repeat true (S a') ++ P'))
                 (repeat false 1 ++ (repeat true r1 ++ tail rest G))).
Proof. intros. exact (gtup_prefix _ _ _ _ _ _). Qed.

Lemma gunit2_mk : forall P' s r' r2 rest G,
  run (S r' + 2)
    (mkCfg SB (repeat true s ++ P')
       (repeat false 1 ++ (repeat true (S r') ++
         tail ((1, r2) :: rest) G))) =
  Some (mkCfg SB (repeat true (S r') ++ (false :: repeat true (S s) ++ P'))
                 (repeat true r2 ++ tail rest G)).
Proof.
  intros P' s r' r2 rest G.
  replace (S r' + 2) with (2 + (r' + 1)) by lia.
  rewrite run_split.
  assert (H2 : run 2
    (mkCfg SB (repeat true s ++ P')
       (repeat false 1 ++ (repeat true (S r') ++
         tail ((1, r2) :: rest) G))) =
    Some (mkCfg SA (false :: repeat true (S s) ++ P')
       (repeat true r' ++
         (repeat false 1 ++ (repeat true r2 ++ tail rest G))))).
  { reflexivity. }
  rewrite H2. cbv beta iota.
  rewrite run_split.
  rewrite sweepA. cbv beta iota.
  reflexivity.
Qed.

Lemma tup2_inner : forall P' s r1' w2' r2 rest G,
  run (S r1' + 3)
    (mkCfg SB (repeat true s ++ P')
       (repeat false 1 ++ (repeat true (S r1') ++
         tail ((S (S w2'), r2) :: rest) G))) =
  Some (mkCfg SC (repeat true (S (S r1')) ++ (false :: repeat true (S s) ++ P'))
                 (repeat false w2' ++ (repeat true r2 ++ tail rest G))).
Proof.
  intros P' s r1' w2' r2 rest G.
  replace (S r1' + 3) with (2 + (r1' + 2)) by lia.
  rewrite run_split.
  assert (H2 : run 2
    (mkCfg SB (repeat true s ++ P')
       (repeat false 1 ++ (repeat true (S r1') ++
         tail ((S (S w2'), r2) :: rest) G))) =
    Some (mkCfg SA (false :: repeat true (S s) ++ P')
       (repeat true r1' ++
         (repeat false (S (S w2')) ++ (repeat true r2 ++ tail rest G))))).
  { reflexivity. }
  rewrite H2. cbv beta iota.
  rewrite run_split.
  rewrite sweepA. cbv beta iota.
  reflexivity.
Qed.

Lemma tup2_probe : forall P' s r1'' w2'' r2 rest G,
  run 3 (mkCfg SC (repeat true (S (S (S r1''))) ++
                    (false :: repeat true (S s) ++ P'))
                 (repeat false (S w2'') ++ (repeat true r2 ++ tail rest G))) =
  Some (mkCfg SF (repeat true r1'' ++ (false :: repeat true (S s) ++ P'))
                 (true :: true :: true ::
                   (repeat false (S w2'') ++ (repeat true r2 ++ tail rest G)))).
Proof. intros. reflexivity. Qed.

Lemma TUP2_1 : forall P a s' r1'' w2'' r2 rest G,
  run (S s' + 2 * S (S r1'') + 8)
    (gbsec P a 1 (S s') ((2, S (S r1'')) :: (S (S (S w2'')), r2) :: rest) G) =
  Some (gcsec (false :: repeat true (S a) ++ P) (S s') (S r1'') 2
          ((S w2'', r2) :: rest) G).
Proof.
  intros P a s' r1'' w2'' r2 rest G.
  replace (S s' + 2 * S (S r1'') + 8)
    with ((S s' + 2) + ((S (S r1'') + 3) + (3 + (r1'' + 2)))) by lia.
  rewrite run_split.
  rewrite gtup_prefix.
  rewrite run_split.
  rewrite tup2_inner.
  rewrite run_split.
  rewrite tup2_probe.
  rewrite run_split.
  rewrite sweepF. cbv beta iota.
  reflexivity.
Qed.

Lemma TRANS2_2 : forall P a s0 r1_0 r2_0 r3 rest G, 1 <= r3 ->
  run ((S s0 + 2) + ((S r1_0 + 2) + ((S r2_0 + 2) + (S r2_0 + 1))))
    (gbsec P a 1 (S s0) ((2, S r1_0) :: (2, S r2_0) :: (1, r3) :: rest) G) =
  Some (gbsec (false :: repeat true (S (S s0)) ++
                (false :: repeat true (S a) ++ P))
              (S (S r1_0)) 1 (S r2_0 + r3) rest G).
Proof.
  intros P a s0 r1_0 r2_0 r3 rest G Hr3.
  rewrite run_split.
  rewrite gtup_prefix.
  rewrite run_split.
  rewrite gtup_prefix_mk.
  rewrite run_split.
  rewrite gunit2_mk.
  apply gturn. exact Hr3.
Qed.

Lemma TRANS2_1 : forall P a s' r1' r2 rest G, 1 <= r2 ->
  run ((S s' + 2) + ((S r1' + 2) + (S r1' + 1)))
    (gbsec P a 1 (S s') ((2, S r1') :: (1, r2) :: rest) G) =
  Some (gbsec (false :: repeat true (S a) ++ P) (S (S s')) 1
          (S r1' + r2) rest G).
Proof.
  intros P a s' r1' r2 rest G Hr2.
  rewrite run_split.
  rewrite gtup_prefix.
  rewrite run_split.
  rewrite gunit2_mk.
  apply gturn. exact Hr2.
Qed.

Lemma PUSHX_core : forall g'' pairs G,
  run 20 (csec 0 (S (S (S g''))) 2 pairs G) =
  Some (bsec 0 1 5 ((S g'', 2) :: pairs) G).
Proof. intros. reflexivity. Qed.

Lemma PUSHX : forall pairs G,
  run 33 (csec 0 3 2 pairs G) = Some (bsec 1 1 7 pairs G).
Proof.
  intros pairs G.
  replace 33 with (20 + 13) by lia.
  rewrite run_split.
  replace 3 with (S (S (S 0))) by lia.
  rewrite PUSHX_core.
  replace 13 with (2 * 5 + 3) by lia.
  replace 7 with (5 + 2) by lia.
  apply POP; lia.
Qed.

Lemma PX2A_chunkA : forall b' p Q' pairs G,
  run 12 (gcsec (false :: repeat true (S (S (S b'))) ++
                  (false :: repeat true p ++ Q')) 0 3 2 pairs G) =
  Some (mkCfg SF (repeat true b' ++ (false :: repeat true p ++ Q'))
                 (true :: true :: true ::
                   tail ((1, 1) :: (1, 2) :: (1, 2) :: pairs) G)).
Proof. intros. reflexivity. Qed.

Lemma PX2A : forall b' p' Q' pairs G,
  run (b' + 14)
    (gcsec (false :: repeat true (S (S (S b'))) ++
             (false :: repeat true (S p') ++ Q')) 0 3 2 pairs G) =
  Some (gcsec Q' p' (S b') 2
          ((1, 1) :: (1, 2) :: (1, 2) :: pairs) G).
Proof.
  intros b' p' Q' pairs G.
  replace (b' + 14) with (12 + (b' + 2)) by lia.
  rewrite run_split.
  rewrite PX2A_chunkA.
  rewrite run_split.
  rewrite sweepF. cbv beta iota.
  reflexivity.
Qed.

Lemma PUSHX_TUP : forall g1' pairs G,
  run 16 (bsec 0 1 5 ((S (S (S g1')), 2) :: pairs) G) =
  Some (csec 0 4 2 ((S g1', 2) :: pairs) G).
Proof. intros. exact (TUP 0 3 g1' 2 _ _). Qed.

Lemma PX2A_b2 : forall p' Q' pairs G,
  run 23 (gcsec (false :: repeat true 2 ++
                  (false :: repeat true (S p') ++ Q')) 0 3 2 pairs G) =
  Some (gbsec Q' p' 1 5 ((1, 2) :: (1, 2) :: pairs) G).
Proof. intros. reflexivity. Qed.

Lemma CGAP2_probe : forall a2 w1 r1 rest G,
  run 4 (csec a2 2 2 ((w1, r1) :: rest) G) =
  Some (gcsec (false :: repeat true a2) 3 w1 r1 rest G).
Proof. intros. reflexivity. Qed.

Lemma CGAP2_pop : forall a2 r1' rest G,
  run 6 (gcsec (false :: repeat true a2) 3 1 (S r1') rest G) =
  Some (gbsec (false :: repeat true a2) 3 1 (2 + S r1') rest G).
Proof. intros. reflexivity. Qed.

Lemma CGAP2_push : forall a2 w1' r1 rest G,
  run 9 (gcsec (false :: repeat true a2) 3 (S (S (S w1'))) r1 rest G) =
  Some (gcsec (false :: repeat true a2) 2 1 2 ((S w1', r1) :: rest) G).
Proof. intros. reflexivity. Qed.

Lemma PX2B_b2 : forall pairs G,
  run 43 (gcsec (false :: repeat true 2) 0 3 2 pairs G) =
  Some (bsec 1 1 8 ((1, 2) :: pairs) G).
Proof. intros. reflexivity. Qed.

Lemma PX2B_b3 : forall pairs G,
  run 38 (gcsec (false :: repeat true 3) 0 3 2 pairs G) =
  Some (bsec 1 1 6 ((1, 2) :: (1, 2) :: pairs) G).
Proof. intros. reflexivity. Qed.

Lemma PX2B_b4 : forall pairs G,
  run 29 (gcsec (false :: repeat true 4) 0 3 2 pairs G) =
  Some (mkCfg SB (repeat true 4 ++ [false])
          (repeat false 1 ++ (repeat true 3 ++
            tail ((1, 2) :: (1, 2) :: pairs) G))).
Proof. intros. reflexivity. Qed.

Lemma PX2B_b5 : forall pairs G,
  run 44 (gcsec (false :: repeat true 5) 0 3 2 pairs G) =
  Some (mkCfg SB (repeat true 4 ++ [false])
          (repeat false 1 ++ (repeat true 4 ++
            tail ((1, 1) :: (1, 2) :: (1, 2) :: pairs) G))).
Proof. intros. reflexivity. Qed.

Lemma PX2B_b6 : forall pairs G,
  run 49 (gcsec (false :: repeat true 6) 0 3 2 pairs G) =
  Some (mkCfg SB ((repeat true 3 ++ (false :: repeat true 4)) ++ [false])
          (repeat false 1 ++ (repeat true 3 ++
            tail ((1, 2) :: (1, 2) :: pairs) G))).
Proof. intros. reflexivity. Qed.

Lemma defect_merge : forall P' s' w2''' r2' rest G,
  run 7 (mkCfg SB (repeat true (S s') ++ P')
           (repeat false 1 ++ (repeat true 1 ++
             tail ((S (S (S (S w2'''))), S r2') :: rest) G))) =
  Some (mkCfg SF (repeat true (S (S s')) ++ P')
           (false :: (repeat true 2 ++
             (repeat false (S (S w2''')) ++
               (repeat true (S r2') ++ tail rest G))))).
Proof. intros. reflexivity. Qed.

Lemma TAIL13 : forall P' s' w3 r2' rest G,
  run 13 (gcsec P' (S s') 0 2 ((S (S (S w3)), S r2') :: rest) G) =
  Some (gcsec P' s' 3 2 ((S w3, S r2') :: rest) G).
Proof. intros. reflexivity. Qed.

Lemma defect_fstep : forall P' s' w3' r2' rest G,
  run 1 (mkCfg SF (repeat true (S (S s')) ++ P')
           (false :: (repeat true 2 ++
             (repeat false (S (S (S w3'))) ++
               (repeat true (S r2') ++ tail rest G))))) =
  Some (gcsec P' (S s') 0 2 ((S (S (S w3')), S r2') :: rest) G).
Proof. intros. reflexivity. Qed.

Lemma TUP2_defect : forall P a s' w3' r2' rest G,
  run (S s' + 23)
    (gbsec P a 1 (S s') ((2, 1) :: (S (S (S (S (S w3')))), S r2') :: rest) G) =
  Some (gcsec (false :: repeat true (S a) ++ P) s' 3 2
          ((S w3', S r2') :: rest) G).
Proof.
  intros P a s' w3' r2' rest G.
  replace (S s' + 23) with ((S s' + 2) + (7 + (1 + 13))) by lia.
  rewrite run_split.
  rewrite gtup_prefix.
  rewrite run_split.
  rewrite defect_merge.
  rewrite run_split.
  rewrite defect_fstep.
  apply TAIL13.
Qed.

Lemma CGAP2_pop_total : forall a2 r1' rest G,
  run 10 (csec a2 2 2 ((1, S r1') :: rest) G) =
  Some (gbsec (false :: repeat true a2) 3 1 (2 + S r1') rest G).
Proof.
  intros a2 r1' rest G.
  replace 10 with (4 + 6) by lia.
  rewrite run_split.
  rewrite CGAP2_probe.
  apply CGAP2_pop.
Qed.

Lemma CGAP2_push_total : forall a2 w1' r1 rest G,
  run 13 (csec a2 2 2 ((S (S (S w1')), r1) :: rest) G) =
  Some (gcsec (false :: repeat true a2) 2 1 2 ((S w1', r1) :: rest) G).
Proof.
  intros a2 w1' r1 rest G.
  replace 13 with (4 + 9) by lia.
  rewrite run_split.
  rewrite CGAP2_probe.
  apply CGAP2_push.
Qed.

Lemma PX2B_b4' : forall pairs G,
  run 29 (gcsec (false :: repeat true 4) 0 3 2 pairs G) =
  Some (gbsec [false] 4 1 3 ((1, 2) :: (1, 2) :: pairs) G).
Proof. intros. exact (PX2B_b4 _ _). Qed.

Lemma PX2B_b5' : forall pairs G,
  run 44 (gcsec (false :: repeat true 5) 0 3 2 pairs G) =
  Some (gbsec [false] 4 1 4 ((1, 1) :: (1, 2) :: (1, 2) :: pairs) G).
Proof. intros. exact (PX2B_b5 _ _). Qed.

Lemma PX2B_b6' : forall pairs G,
  run 49 (gcsec (false :: repeat true 6) 0 3 2 pairs G) =
  Some (gbsec ((false :: repeat true 4) ++ [false]) 3 1 3
          ((1, 2) :: (1, 2) :: pairs) G).
Proof. intros. exact (PX2B_b6 _ _). Qed.

(* ---------------------------------------------------------------- *)
(* Phase 36: the third re-basing's dip-bottom step lists.           *)
(* PX2A0: the PX2A dispatch at a two-block prefix [b; 0] whose      *)
(* second block is 0 (PX2A_chunkA is stated for general p, p = 0    *)
(* included, and its F-sweep is unchanged; the 23-step tail after   *)
(* the sweep is the deviation: the sweep overshoots into the blank  *)
(* past the empty block and the landing carries the residue pair    *)
(* (b - 4, 2) over the usual (1, 1) :: (1, 2) :: (1, 2) extras).    *)
(* b = S (S (S (S (S b'')))), cost b + 32 = b'' + 37.  Derived by   *)
(* direct zipper tracing (rocq/hsim36.py), verified at             *)
(* b in {5,6,7,8,10,12,16,20,24,30} and at stack/G variations.      *)
(* ---------------------------------------------------------------- *)

Lemma PX2A0_tail : forall b'' pairs G,
  run 23 (mkCfg SF [false]
            (true :: (repeat false (S (S b'')) ++
              (true :: true ::
                tail ((1, 1) :: (1, 2) :: (1, 2) :: pairs) G)))) =
  Some (gbsec [false] 3 1 2
          ((S b'', 2) :: (1, 1) :: (1, 2) :: (1, 2) :: pairs) G).
Proof. intros. reflexivity. Qed.

Lemma PX2A0 : forall b'' pairs G,
  run (b'' + 37)
    (gcsec (false :: repeat true (S (S (S (S (S b''))))) ++ [false])
       0 3 2 pairs G) =
  Some (gbsec [false] 3 1 2
          ((S b'', 2) :: (1, 1) :: (1, 2) :: (1, 2) :: pairs) G).
Proof.
  intros b'' pairs G.
  replace (b'' + 37) with (12 + (S (S b'') + 23)) by lia.
  rewrite run_split.
  replace (false :: repeat true (S (S (S (S (S b''))))) ++ [false])
    with (false :: repeat true (S (S (S (S (S b''))))) ++
           (false :: repeat true 0 ++ [])) by reflexivity.
  rewrite PX2A_chunkA.
  rewrite run_split.
  rewrite sweepF. cbv beta iota.
  replace (false :: repeat true 0 ++ []) with [false] by reflexivity.
  apply PX2A0_tail.
Qed.

(* PX2B0: the PX2B dispatch at the empty single block [0] -- the    *)
(* dip bottom of the deviated grind at pb = [0] (Phase 36).  The    *)
(* 20-step excursion consumes the [0] prefix entirely and lands on  *)
(* the B-section (a = 0, s = 5) over the pushed pair (1, 2); the    *)
(* following POP (13 steps) gives the PUSHX-shaped landing          *)
(* HB [] 1 1 7 P G, cf. PUSHX_core's 20 + 13 split.                 *)
Lemma PX2B0 : forall pairs G,
  run 20 (gcsec [false] 0 3 2 pairs G) =
  Some (gbsec [] 0 1 5 ((1, 2) :: pairs) G).
Proof. intros. reflexivity. Qed.

Print Assumptions PX2A0.
Print Assumptions PX2B0.

(* ---------------------------------------------------------------- *)
(* Phase 41: PX2Bgen -- the PX2B dispatch at a single-block prefix  *)
(* [b] with b >= 5.  The Phase 40 fence: the phase-8 final grind's  *)
(* DIPDESC descent at frame ([235; 42; 19], 334) fires hPX2A onto   *)
(* frame ([19], 41), whose own boundary grind's dip is at the       *)
(* single block [19] -- the hPX2B rows covered only b <= 6, each    *)
(* as a whole chunk, and no row fired at [19].  Direct zipper       *)
(* tracing (rocq/hsim41.py) shows the dip is a UNIFORM family for   *)
(* b >= 5: the same landing shape and cost b + 32 as PX2A0 at       *)
(* [b; 0].  Decomposition (mirroring PX2A0): a 12-step chunk, the    *)
(* F-sweep over the block (sweepF), and a 23-step tail;             *)
(* b = S (S (S (S (S b'')))), cost b'' + 37.  Verified at            *)
(* b in {5,6,7,8,9,10,12,14,16,19,20,24,30} and at several stack    *)
(* shapes / G values (hsim41.py).  The small blocks are accidents:  *)
(* b = 2, 3, 4 land at costs 28, 25, 22 in other shapes (the        *)
(* existing hPX2B2..6 chunks are those accidents plus a step).      *)
(* ---------------------------------------------------------------- *)

Lemma PX2Bgen_chunk : forall b'' Q pairs G,
  run 12 (gcsec (false :: repeat true (S (S (S (S (S b''))))) ++ Q)
            0 3 2 pairs G) =
  Some (mkCfg SF (repeat true (S (S b'')) ++ Q)
          (true :: true :: true :: false :: true :: false ::
           true :: true :: false :: true :: true ::
           tail pairs G)).
Proof. intros. reflexivity. Qed.

Lemma PX2Bgen_tail : forall b'' pairs G,
  run 23 (mkCfg SF []
            (true :: (repeat false (S (S b'')) ++
              (true :: true :: false :: true :: false ::
               true :: true :: false :: true :: true ::
               tail pairs G)))) =
  Some (gbsec [false] 3 1 2
          ((S b'', 2) :: (1, 1) :: (1, 2) :: (1, 2) :: pairs) G).
Proof. intros. reflexivity. Qed.

Lemma PX2Bgen : forall b'' pairs G,
  run (b'' + 37)
    (gcsec (false :: repeat true (S (S (S (S (S b'')))))) 0 3 2 pairs G) =
  Some (gbsec [false] 3 1 2
          ((S b'', 2) :: (1, 1) :: (1, 2) :: (1, 2) :: pairs) G).
Proof.
  intros b'' pairs G.
  replace (b'' + 37) with (12 + (S (S b'') + 23)) by lia.
  rewrite run_split.
  replace (false :: repeat true (S (S (S (S (S b''))))))
    with (false :: repeat true (S (S (S (S (S b''))))) ++ [])
    by (rewrite app_nil_r; reflexivity).
  rewrite PX2Bgen_chunk.
  rewrite run_split.
  rewrite sweepF. cbv beta iota.
  apply PX2Bgen_tail.
Qed.

Print Assumptions PX2Bgen.
