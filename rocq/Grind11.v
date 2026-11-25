(* ================================================================= *)
(*  Grind11.v -- Phase 43: CASCADE_LANDING's stages 1-3 in the era   *)
(*  regime, and the reduction of the cascade to its stage-4 core.    *)
(*                                                                   *)
(*  Phase 42 (Grind10.v) reduced the phase-8 era law to the single   *)
(*  statement CASCADE_LANDING and proved its last two stages in      *)
(*  general (CASCADE_STAGE4, CASCADE_POPFIN).  Its remaining core    *)
(*  was "stages 1-3: the segment grinds at frames [5], [24; 5],      *)
(*  [25; 24; 5]".  Phase 43 parses those stages on the shrunk        *)
(*  family S(n1, r1, n2, r2, b) of hsim42 -- in the ERA regime,      *)
(*  where r1 = 149 is ODD (the hsim42 base analogue has r1 even and  *)
(*  a different stage-2 parse) -- and mechanises them exactly.       *)
(*  All boundary formulas below are asserted verbatim in             *)
(*  rocq/hsim43.py (ALL PHASE 43 CHECKS PASS) before mechanisation.  *)
(*                                                                   *)
(*  Write x = n1 + 17, A1 = 2*n1 + 10, m1 = (r1 - 7)/2,              *)
(*  A_pre = A1 + n2 + 3, s_pre = 2*m1 + 2*n2 + 12 (= r1 + 2*n2 + 5). *)
(*                                                                   *)
(*  STAGE 1 (CASCADE_STAGE1; parity-free): TDN + POP (1, 2) +        *)
(*  POP (1, 1) + a POP chain over the first spine + TUP +            *)
(*  hGRIND_even (n1 + 3) + hTUP2_1:                                  *)
(*    HC [5] 13 1 2 (stage-D stack)                                  *)
(*      -> HC [x; 5] A1 1 2 ((r1 - 4, 2) :: (1, 1) :: Tail).         *)
(*                                                                   *)
(*  MERGED STAGE 2+3 (CASCADE_STAGE23): the odd pair (r1 - 4, 2) =   *)
(*  (2*m1 + 3, 2) is ground by GG_odd -- grind_prefix + the odd GG   *)
(*  rounds GG_rounds_odd (induction on m1 over Grind2.grind_round)   *)
(*  -- to a (1, 2) head, so the grind runs through (1, 1) and the    *)
(*  whole second spine before TUP on (r2, 2); then                  *)
(*  hGRIND_even (m1 + n2 + 4) and hTUP2_1:                           *)
(*    -> HB [x; 5] A1 1 (2*m1 + 6) ((1, 2) :: (1, 1) :: Rest1)       *)
(*    -> HB [x; 5] (A1 + n2 + 4) 1 (2*m1 + 2*n2 + 13)                *)
(*         ((r2, 2) :: (1, 1) :: Tail)                    [POPs]      *)
(*    -> HC [A_pre + 1; x; 5] s_pre 1 2                              *)
(*         ((r2 - 4, 2) :: (1, 1) :: Tail)              [TUP2_1]     *)
(*  The floors are m1 + 1 <= A1 (GG_odd) and m1 + n2 + 4 <=          *)
(*  A1 + n2 + 3 (hGRIND_even) -- the SAME floor, and M-independent:  *)
(*  the residue r2 enters stages 1-3 only through TUP / hTUP2_1 /    *)
(*  the two dispatch branches below.  Era: 72 <= 90 and 71 <= 89.    *)
(*                                                                   *)
(*  DISPATCH BRANCHES at the merged stage's end:                     *)
(*   - r2 = 4 (M = 617; CASCADE_STAGE23_r2_4): the hGRIND_even       *)
(*     target's second pair is (2, 2), so hTUP2_1 cannot fire;       *)
(*     hTRANS2_2 fires instead, landing on the POPFIN source with    *)
(*     frame counter 3 (terminal A = beta + 2 after POPFIN).         *)
(*   - r2 = 2 (M = 616; CASCADE_STAGE23_r2_2): after the POPs the    *)
(*     head is the residue (2, 2) itself; hTRANS2_1 fires directly   *)
(*     (no TUP, no hGRIND_even; terminal A = s_pre + beta + 1).      *)
(*                                                                   *)
(*  STAGE 4 splits at the CASCADE_STAGE4 floor m4 + 1 <= s_pre      *)
(*  (m4 = (r2 - 8)/2 = M - 619): for 619 <= M <= 1440 the clean      *)
(*  regime is closed by Grind10.CASCADE_STAGE4 + hTRANS2_1 +         *)
(*  CASCADE_POPFIN; at M = 618 (r2 = 6) the stage-4 pair is (2, 2)   *)
(*  itself and the stage degenerates to TDN + hTRANS2_1 + POPFIN     *)
(*  (hsim43 check_stage4_r2_6).  The BOUNDARY regime M >= 1441       *)
(*  re-routes through dips / PX2A (frame                             *)
(*  counters re-base and the grind continues on a larger budget;    *)
(*  hsim43 Part 3: shrunk boundary points land on the era shape,     *)
(*  e.g. S(4, 9, 1, 40, 3) in 527,131 rules via 3 frame growths).    *)
(*  It is the strictly smaller residual core:                        *)
(*                                                                   *)
(*    CASCADE_STAGE4_BIG: the stage-4 source at the era frame        *)
(*    [428; 57; 5], counter 822, reaches HB pb a 1 (2*beta + 1) [] 1 *)
(*    with beta <= a, for M >= 1441, beta >= 2.                      *)
(*                                                                   *)
(*  CASCADE_LANDING_of composes stages 1-3 + the five-way stage-4   *)
(*  dispatch into CASCADE_LANDING modulo CASCADE_STAGE4_BIG, and    *)
(*  ESC_ERA_LAW_43 / Loop.ESC_ITER_BIG8_43 carry it to the era law   *)
(*  and the loop.  H_LOOP's ESC side is therefore NOT closed: it     *)
(*  now rests on CASCADE_STAGE4_BIG alone (one pair, one frame),    *)
(*  in place of the whole three-stage cascade.                       *)
(* ================================================================= *)

Require Import List Bool Arith Lia ZArith.
Import ListNotations.
Require Import TM Sections Mirror TokenPass Recoord Era Esc Dev
               Grind Grind2 Grind3 Grind4 Grind5 Grind6 Grind7 Grind8
               Grind9 Grind10.

Ltac sec_eq := repeat (first [ solve [reflexivity] | solve [lia]
                             | f_equal ]).

(* ----------------------------------------------------------------- *)
(* Helpers.                                                          *)
(* ----------------------------------------------------------------- *)

(* A POP chain over a (1, 2)-spine of length n in front of an        *)
(* arbitrary tail: each POP advances the frame counter by 1 and the  *)
(* shuttle by 2.                                                     *)
Lemma pop12 : forall n pb a s P G, 2 <= s ->
  hsteps (HB pb a 1 s (repeat (1, 2) n ++ P) G)
         (HB pb (a + n) 1 (s + 2 * n) P G).
Proof.
  induction n as [|n IH]; intros pb a s P G Hs.
  - replace (a + 0) with a by lia.
    replace (s + 2 * 0) with s by lia. apply hsteps_refl.
  - apply (hsteps_trans _ (HB pb (S a) 1 (s + 2)
        (repeat (1, 2) n ++ P) G)).
    { apply (hsteps_step _ (HB pb (S a) 1 (s + 2)
          (repeat (1, 2) n ++ P) G)).
      { replace (repeat (1, 2) (S n) ++ P)
          with ((1, 2) :: (repeat (1, 2) n ++ P)) by reflexivity.
        apply (hPOP pb a s 2 (repeat (1, 2) n ++ P) G); lia. }
      apply hsteps_refl. }
    replace (a + S n) with (S a + n) by lia.
    replace (s + 2 * S n) with (s + 2 + 2 * n) by lia.
    apply (IH pb (S a) (s + 2) P G); lia.
Qed.

(* The odd GG rounds: the grind of an odd pair (2*m + 1, 2) at       *)
(* g0 = 1, one grind_round per unit of m (each round: g -= 2,        *)
(* s += 2).  The floor is the round floor j + 1 <= a2 at every       *)
(* round, i.e. j0 + m + 1 <= a2.                                     *)
Lemma GG_rounds_odd : forall m j0 pb a2 P G, j0 + m + 1 <= a2 ->
  hsteps (HB pb a2 1 (2 * j0 + 6) ((2 * m + 1, 2) :: P) G)
         (HB pb a2 1 (2 * (j0 + m) + 6) ((1, 2) :: P) G).
Proof.
  induction m as [|m IH]; intros j0 pb a2 P G Hf.
  - replace (2 * 0 + 1) with 1 by lia.
    replace (2 * (j0 + 0) + 6) with (2 * j0 + 6) by lia.
    apply hsteps_refl.
  - apply (hsteps_trans _ (HB pb a2 1 (2 * (j0 + 1) + 6)
        ((2 * m + 3 - 2, 2) :: P) G)).
    { replace (2 * S m + 1) with (2 * m + 3) by lia.
      replace (2 * j0 + 6) with (2 * (j0 + 1) + 4) by lia.
      apply (grind_round (j0 + 1) pb a2 (2 * m + 3) P G); lia. }
    replace (2 * m + 3 - 2) with (2 * m + 1) by lia.
    replace (2 * (j0 + S m) + 6) with (2 * ((j0 + 1) + m) + 6)
      by lia.
    apply (IH (j0 + 1) pb a2 P G); lia.
Qed.

(* GG_odd: the totality of the odd-pair grind at g0 = 1 --           *)
(* grind_prefix strips the pair to (2*m + 1, 2) at shuttle 6, then   *)
(* the odd rounds finish it to a (1, 2) head.  Floor m + 1 <= a2.    *)
Lemma GG_odd : forall m pb a2 P G, m + 1 <= a2 ->
  hsteps (HC pb a2 1 2 ((2 * m + 3, 2) :: P) G)
         (HB pb a2 1 (2 * m + 6) ((1, 2) :: P) G).
Proof.
  intros m pb a2 P G Hf. destruct a2 as [|a2']; [lia|].
  apply (hsteps_trans _ (HB pb (S a2') 1 6 ((S (2 * m), 2) :: P) G)).
  { replace (2 * m + 3) with (S (S (S (2 * m)))) by lia.
    apply (grind_prefix pb a2' (2 * m) P G). }
  replace (S (2 * m)) with (2 * m + 1) by lia.
  replace (2 * m + 6) with (2 * (0 + m) + 6) by lia.
  apply (GG_rounds_odd m 0 pb (S a2') P G); lia.
Qed.

(* ----------------------------------------------------------------- *)
(* Stage 1 (parity-free).                                            *)
(* ----------------------------------------------------------------- *)

Lemma CASCADE_STAGE1 : forall n1 r1 Tail, 5 <= r1 ->
  hsteps (HC [5] 13 1 2 ((1, 2) :: (1, 1) :: repeat (1, 2) (n1 + 2)
             ++ ((r1, 2) :: (1, 1) :: Tail)) 1)
         (HC [n1 + 17; 5] (2 * n1 + 10) 1 2
             ((r1 - 4, 2) :: (1, 1) :: Tail) 1).
Proof.
  intros n1 r1 Tail Hr1.
  destruct r1 as [|[|[|[|[|r1']]]]]; try lia.
  (* TDN *)
  apply (hsteps_trans _ (HB [5] 13 1 4 ((1, 2) :: (1, 1)
    :: repeat (1, 2) (n1 + 2)
    ++ ((S (S (S (S (S r1')))), 2) :: (1, 1) :: Tail)) 1)).
  { apply (hsteps_step _ (HB [5] 13 1 4 ((1, 2) :: (1, 1)
      :: repeat (1, 2) (n1 + 2)
      ++ ((S (S (S (S (S r1')))), 2) :: (1, 1) :: Tail)) 1)).
    { apply (hTDN [5] 13 ((1, 2) :: (1, 1) :: repeat (1, 2) (n1 + 2)
        ++ ((S (S (S (S (S r1')))), 2) :: (1, 1) :: Tail)) 1). }
    apply hsteps_refl. }
  (* POP (1, 2) *)
  apply (hsteps_trans _ (HB [5] 14 1 6 ((1, 1)
    :: repeat (1, 2) (n1 + 2)
    ++ ((S (S (S (S (S r1')))), 2) :: (1, 1) :: Tail)) 1)).
  { apply (hsteps_step _ (HB [5] 14 1 6 ((1, 1)
      :: repeat (1, 2) (n1 + 2)
      ++ ((S (S (S (S (S r1')))), 2) :: (1, 1) :: Tail)) 1)).
    { apply (hPOP [5] 13 4 2 ((1, 1) :: repeat (1, 2) (n1 + 2)
        ++ ((S (S (S (S (S r1')))), 2) :: (1, 1) :: Tail)) 1); lia. }
    apply hsteps_refl. }
  (* POP (1, 1) *)
  apply (hsteps_trans _ (HB [5] 15 1 7 (repeat (1, 2) (n1 + 2)
    ++ ((S (S (S (S (S r1')))), 2) :: (1, 1) :: Tail)) 1)).
  { apply (hsteps_step _ (HB [5] 15 1 7 (repeat (1, 2) (n1 + 2)
      ++ ((S (S (S (S (S r1')))), 2) :: (1, 1) :: Tail)) 1)).
    { apply (hPOP [5] 14 6 1 (repeat (1, 2) (n1 + 2)
        ++ ((S (S (S (S (S r1')))), 2) :: (1, 1) :: Tail)) 1); lia. }
    apply hsteps_refl. }
  (* POP chain over the first spine *)
  apply (hsteps_trans _ (HB [5] (n1 + 17) 1 (2 * n1 + 11)
    ((S (S (S (S (S r1')))), 2) :: (1, 1) :: Tail) 1)).
  { replace (n1 + 17) with (15 + (n1 + 2)) by lia.
    replace (2 * n1 + 11) with (7 + 2 * (n1 + 2)) by lia.
    apply (pop12 (n1 + 2) [5] 15 7
      ((S (S (S (S (S r1')))), 2) :: (1, 1) :: Tail) 1); lia. }
  (* TUP on the residue pair *)
  apply (hsteps_trans _ (HC [5] (n1 + 17) (2 * n1 + 10) 2
    ((S (S (S r1')), 2) :: (1, 1) :: Tail) 1)).
  { apply (hsteps_step _ (HC [5] (n1 + 17) (2 * n1 + 10) 2
      ((S (S (S r1')), 2) :: (1, 1) :: Tail) 1)).
    { replace (2 * n1 + 11) with (S (S (2 * n1 + 9))) by lia.
      replace (2 * n1 + 10) with (S (2 * n1 + 9)) by lia.
      apply (hTUP [5] (n1 + 17) (2 * n1 + 9) (S (S r1')) 2
        ((1, 1) :: Tail) 1). }
    apply hsteps_refl. }
  (* hGRIND_even (n1 + 3) *)
  apply (hsteps_trans _ (HB [5] (n1 + 16) 1 (2 * n1 + 10)
    ((2, 2) :: (S (S (S r1')), 2) :: (1, 1) :: Tail) 1)).
  { replace (n1 + 17) with (S (n1 + 16)) by lia.
    replace (2 * n1 + 10) with (2 * (n1 + 3) + 4) by lia.
    apply (hGRIND_even (n1 + 3) [5] (n1 + 16)
      ((S (S (S r1')), 2) :: (1, 1) :: Tail) 1); lia. }
  (* hTUP2_1: frame growth onto [n1 + 17; 5] *)
  apply (hsteps_step _ (HC [n1 + 17; 5] (2 * n1 + 10) 1 2
    ((S (S (S (S (S r1')))) - 4, 2) :: (1, 1) :: Tail) 1)).
  { replace (n1 + 17) with (S (n1 + 16)) by lia.
    replace (2 * n1 + 10) with (S (2 * n1 + 9)) by lia.
    apply (hTUP2_1 [5] (n1 + 16) (2 * n1 + 9) 0 r1' 2
      ((1, 1) :: Tail) 1). }
  apply hsteps_refl.
Qed.

(* ----------------------------------------------------------------- *)
(* Merged stage 2+3 (odd r1), and its two dispatch branches.         *)
(* ----------------------------------------------------------------- *)

Lemma CASCADE_STAGE23 : forall m1 n2 r2 x pb A1 Tail,
  m1 + 1 <= A1 -> 6 <= r2 ->
  hsteps (HC (x :: pb) A1 1 2 ((2 * m1 + 3, 2) :: (1, 1)
             :: repeat (1, 2) (n2 + 2) ++ ((r2, 2) :: (1, 1) :: Tail)) 1)
         (HC (A1 + n2 + 4 :: x :: pb) (2 * m1 + 2 * n2 + 12) 1 2
             ((r2 - 4, 2) :: (1, 1) :: Tail) 1).
Proof.
  intros m1 n2 r2 x pb A1 Tail Hf Hr2.
  destruct r2 as [|[|[|[|[|[|r2']]]]]]; try lia.
  (* GG_odd on the odd pair *)
  apply (hsteps_trans _ (HB (x :: pb) A1 1 (2 * m1 + 6)
    ((1, 2) :: (1, 1) :: repeat (1, 2) (n2 + 2)
     ++ ((S (S (S (S (S (S r2'))))), 2) :: (1, 1) :: Tail)) 1)).
  { apply (GG_odd m1 (x :: pb) A1 ((1, 1) :: repeat (1, 2) (n2 + 2)
      ++ ((S (S (S (S (S (S r2'))))), 2) :: (1, 1) :: Tail)) 1); lia. }
  (* POP (1, 2) *)
  apply (hsteps_trans _ (HB (x :: pb) (S A1) 1 (2 * m1 + 8)
    ((1, 1) :: repeat (1, 2) (n2 + 2)
     ++ ((S (S (S (S (S (S r2'))))), 2) :: (1, 1) :: Tail)) 1)).
  { apply (hsteps_step _ (HB (x :: pb) (S A1) 1 (2 * m1 + 8)
      ((1, 1) :: repeat (1, 2) (n2 + 2)
       ++ ((S (S (S (S (S (S r2'))))), 2) :: (1, 1) :: Tail)) 1)).
    { replace (2 * m1 + 8) with (2 * m1 + 6 + 2) by lia.
      apply (hPOP (x :: pb) A1 (2 * m1 + 6) 2 ((1, 1)
        :: repeat (1, 2) (n2 + 2)
        ++ ((S (S (S (S (S (S r2'))))), 2) :: (1, 1) :: Tail)) 1);
      lia. }
    apply hsteps_refl. }
  (* POP (1, 1) *)
  apply (hsteps_trans _ (HB (x :: pb) (S (S A1)) 1 (2 * m1 + 9)
    (repeat (1, 2) (n2 + 2)
     ++ ((S (S (S (S (S (S r2'))))), 2) :: (1, 1) :: Tail)) 1)).
  { apply (hsteps_step _ (HB (x :: pb) (S (S A1)) 1 (2 * m1 + 9)
      (repeat (1, 2) (n2 + 2)
       ++ ((S (S (S (S (S (S r2'))))), 2) :: (1, 1) :: Tail)) 1)).
    { replace (2 * m1 + 9) with (2 * m1 + 8 + 1) by lia.
      apply (hPOP (x :: pb) (S A1) (2 * m1 + 8) 1 (repeat (1, 2) (n2 + 2)
        ++ ((S (S (S (S (S (S r2'))))), 2) :: (1, 1) :: Tail)) 1);
      lia. }
    apply hsteps_refl. }
  (* POP chain over the second spine *)
  apply (hsteps_trans _ (HB (x :: pb) (A1 + n2 + 4) 1
    (2 * m1 + 2 * n2 + 13)
    ((S (S (S (S (S (S r2'))))), 2) :: (1, 1) :: Tail) 1)).
  { replace (A1 + n2 + 4) with (S (S A1) + (n2 + 2)) by lia.
    replace (2 * m1 + 2 * n2 + 13) with (2 * m1 + 9 + 2 * (n2 + 2))
      by lia.
    apply (pop12 (n2 + 2) (x :: pb) (S (S A1)) (2 * m1 + 9)
      ((S (S (S (S (S (S r2'))))), 2) :: (1, 1) :: Tail) 1); lia. }
  (* TUP on (r2, 2) *)
  apply (hsteps_trans _ (HC (x :: pb) (A1 + n2 + 4)
    (2 * m1 + 2 * n2 + 12) 2
    ((S (S (S (S r2'))), 2) :: (1, 1) :: Tail) 1)).
  { apply (hsteps_step _ (HC (x :: pb) (A1 + n2 + 4)
      (2 * m1 + 2 * n2 + 12) 2
      ((S (S (S (S r2'))), 2) :: (1, 1) :: Tail) 1)).
    { replace (2 * m1 + 2 * n2 + 13) with (S (S (2 * m1 + 2 * n2 + 11)))
        by lia.
      replace (2 * m1 + 2 * n2 + 12) with (S (2 * m1 + 2 * n2 + 11))
        by lia.
      apply (hTUP (x :: pb) (A1 + n2 + 4) (2 * m1 + 2 * n2 + 11)
        (S (S (S r2'))) 2 ((1, 1) :: Tail) 1). }
    apply hsteps_refl. }
  (* hGRIND_even (m1 + n2 + 4) *)
  apply (hsteps_trans _ (HB (x :: pb) (A1 + n2 + 3) 1
    (2 * m1 + 2 * n2 + 12)
    ((2, 2) :: (S (S (S (S r2'))), 2) :: (1, 1) :: Tail) 1)).
  { replace (A1 + n2 + 4) with (S (A1 + n2 + 3)) by lia.
    replace (2 * m1 + 2 * n2 + 12) with (2 * (m1 + n2 + 4) + 4)
      by lia.
    apply (hGRIND_even (m1 + n2 + 4) (x :: pb) (A1 + n2 + 3)
      ((S (S (S (S r2'))), 2) :: (1, 1) :: Tail) 1); lia. }
  (* hTUP2_1: frame growth *)
  apply (hsteps_step _ (HC (A1 + n2 + 4 :: x :: pb)
    (2 * m1 + 2 * n2 + 12) 1 2
    ((S (S (S (S (S (S r2'))))) - 4, 2) :: (1, 1) :: Tail) 1)).
  { replace (2 * m1 + 2 * n2 + 12) with (S (2 * m1 + 2 * n2 + 11))
      by lia.
    replace (A1 + n2 + 4) with (S (A1 + n2 + 3)) by lia.
    apply (hTUP2_1 (x :: pb) (A1 + n2 + 3) (2 * m1 + 2 * n2 + 11) 0
      (S r2') 2 ((1, 1) :: Tail) 1). }
  apply hsteps_refl.
Qed.

Lemma CASCADE_STAGE23_r2_4 : forall m1 n2 x pb A1 Tail,
  m1 + 1 <= A1 ->
  hsteps (HC (x :: pb) A1 1 2 ((2 * m1 + 3, 2) :: (1, 1)
             :: repeat (1, 2) (n2 + 2) ++ ((4, 2) :: (1, 1) :: Tail)) 1)
         (HB (2 * m1 + 2 * n2 + 13 :: A1 + n2 + 4 :: x :: pb) 3 1 3
             Tail 1).
Proof.
  intros m1 n2 x pb A1 Tail Hf.
  (* GG_odd on the odd pair *)
  apply (hsteps_trans _ (HB (x :: pb) A1 1 (2 * m1 + 6)
    ((1, 2) :: (1, 1) :: repeat (1, 2) (n2 + 2)
     ++ ((4, 2) :: (1, 1) :: Tail)) 1)).
  { apply (GG_odd m1 (x :: pb) A1 ((1, 1) :: repeat (1, 2) (n2 + 2)
      ++ ((4, 2) :: (1, 1) :: Tail)) 1); lia. }
  (* POP (1, 2) *)
  apply (hsteps_trans _ (HB (x :: pb) (S A1) 1 (2 * m1 + 8)
    ((1, 1) :: repeat (1, 2) (n2 + 2)
     ++ ((4, 2) :: (1, 1) :: Tail)) 1)).
  { apply (hsteps_step _ (HB (x :: pb) (S A1) 1 (2 * m1 + 8)
      ((1, 1) :: repeat (1, 2) (n2 + 2)
       ++ ((4, 2) :: (1, 1) :: Tail)) 1)).
    { replace (2 * m1 + 8) with (2 * m1 + 6 + 2) by lia.
      apply (hPOP (x :: pb) A1 (2 * m1 + 6) 2 ((1, 1)
        :: repeat (1, 2) (n2 + 2)
        ++ ((4, 2) :: (1, 1) :: Tail)) 1); lia. }
    apply hsteps_refl. }
  (* POP (1, 1) *)
  apply (hsteps_trans _ (HB (x :: pb) (S (S A1)) 1 (2 * m1 + 9)
    (repeat (1, 2) (n2 + 2) ++ ((4, 2) :: (1, 1) :: Tail)) 1)).
  { apply (hsteps_step _ (HB (x :: pb) (S (S A1)) 1 (2 * m1 + 9)
      (repeat (1, 2) (n2 + 2) ++ ((4, 2) :: (1, 1) :: Tail)) 1)).
    { replace (2 * m1 + 9) with (2 * m1 + 8 + 1) by lia.
      apply (hPOP (x :: pb) (S A1) (2 * m1 + 8) 1 (repeat (1, 2) (n2 + 2)
        ++ ((4, 2) :: (1, 1) :: Tail)) 1); lia. }
    apply hsteps_refl. }
  (* POP chain over the second spine *)
  apply (hsteps_trans _ (HB (x :: pb) (A1 + n2 + 4) 1
    (2 * m1 + 2 * n2 + 13) ((4, 2) :: (1, 1) :: Tail) 1)).
  { replace (A1 + n2 + 4) with (S (S A1) + (n2 + 2)) by lia.
    replace (2 * m1 + 2 * n2 + 13) with (2 * m1 + 9 + 2 * (n2 + 2))
      by lia.
    apply (pop12 (n2 + 2) (x :: pb) (S (S A1)) (2 * m1 + 9)
      ((4, 2) :: (1, 1) :: Tail) 1); lia. }
  (* TUP on (4, 2) *)
  apply (hsteps_trans _ (HC (x :: pb) (A1 + n2 + 4)
    (2 * m1 + 2 * n2 + 12) 2 ((2, 2) :: (1, 1) :: Tail) 1)).
  { apply (hsteps_step _ (HC (x :: pb) (A1 + n2 + 4)
      (2 * m1 + 2 * n2 + 12) 2 ((2, 2) :: (1, 1) :: Tail) 1)).
    { replace (2 * m1 + 2 * n2 + 13) with (S (S (2 * m1 + 2 * n2 + 11)))
        by lia.
      replace (2 * m1 + 2 * n2 + 12) with (S (2 * m1 + 2 * n2 + 11))
        by lia.
      apply (hTUP (x :: pb) (A1 + n2 + 4) (2 * m1 + 2 * n2 + 11) 1 2
        ((1, 1) :: Tail) 1). }
    apply hsteps_refl. }
  (* hGRIND_even (m1 + n2 + 4) *)
  apply (hsteps_trans _ (HB (x :: pb) (A1 + n2 + 3) 1
    (2 * m1 + 2 * n2 + 12) ((2, 2) :: (2, 2) :: (1, 1) :: Tail) 1)).
  { replace (A1 + n2 + 4) with (S (A1 + n2 + 3)) by lia.
    replace (2 * m1 + 2 * n2 + 12) with (2 * (m1 + n2 + 4) + 4)
      by lia.
    apply (hGRIND_even (m1 + n2 + 4) (x :: pb) (A1 + n2 + 3)
      ((2, 2) :: (1, 1) :: Tail) 1); lia. }
  (* hTRANS2_2 dispatch *)
  apply (hsteps_step _ (HB (2 * m1 + 2 * n2 + 13
    :: A1 + n2 + 4 :: x :: pb) 3 1 3 Tail 1)).
  { replace (2 * m1 + 2 * n2 + 12) with (S (2 * m1 + 2 * n2 + 11))
      by lia.
    replace (2 * m1 + 2 * n2 + 13) with (S (S (2 * m1 + 2 * n2 + 11)))
      by lia.
    replace (A1 + n2 + 4) with (S (A1 + n2 + 3)) by lia.
    apply (hTRANS2_2 (x :: pb) (A1 + n2 + 3) (2 * m1 + 2 * n2 + 11)
      1 1 1 Tail 1); lia. }
  apply hsteps_refl.
Qed.

Lemma CASCADE_STAGE23_r2_2 : forall m1 n2 x pb A1 Tail,
  m1 + 1 <= A1 ->
  hsteps (HC (x :: pb) A1 1 2 ((2 * m1 + 3, 2) :: (1, 1)
             :: repeat (1, 2) (n2 + 2) ++ ((2, 2) :: (1, 1) :: Tail)) 1)
         (HB (A1 + n2 + 5 :: x :: pb) (2 * m1 + 2 * n2 + 14) 1 3
             Tail 1).
Proof.
  intros m1 n2 x pb A1 Tail Hf.
  (* GG_odd on the odd pair *)
  apply (hsteps_trans _ (HB (x :: pb) A1 1 (2 * m1 + 6)
    ((1, 2) :: (1, 1) :: repeat (1, 2) (n2 + 2)
     ++ ((2, 2) :: (1, 1) :: Tail)) 1)).
  { apply (GG_odd m1 (x :: pb) A1 ((1, 1) :: repeat (1, 2) (n2 + 2)
      ++ ((2, 2) :: (1, 1) :: Tail)) 1); lia. }
  (* POP (1, 2) *)
  apply (hsteps_trans _ (HB (x :: pb) (S A1) 1 (2 * m1 + 8)
    ((1, 1) :: repeat (1, 2) (n2 + 2)
     ++ ((2, 2) :: (1, 1) :: Tail)) 1)).
  { apply (hsteps_step _ (HB (x :: pb) (S A1) 1 (2 * m1 + 8)
      ((1, 1) :: repeat (1, 2) (n2 + 2)
       ++ ((2, 2) :: (1, 1) :: Tail)) 1)).
    { replace (2 * m1 + 8) with (2 * m1 + 6 + 2) by lia.
      apply (hPOP (x :: pb) A1 (2 * m1 + 6) 2 ((1, 1)
        :: repeat (1, 2) (n2 + 2)
        ++ ((2, 2) :: (1, 1) :: Tail)) 1); lia. }
    apply hsteps_refl. }
  (* POP (1, 1) *)
  apply (hsteps_trans _ (HB (x :: pb) (S (S A1)) 1 (2 * m1 + 9)
    (repeat (1, 2) (n2 + 2) ++ ((2, 2) :: (1, 1) :: Tail)) 1)).
  { apply (hsteps_step _ (HB (x :: pb) (S (S A1)) 1 (2 * m1 + 9)
      (repeat (1, 2) (n2 + 2) ++ ((2, 2) :: (1, 1) :: Tail)) 1)).
    { replace (2 * m1 + 9) with (2 * m1 + 8 + 1) by lia.
      apply (hPOP (x :: pb) (S A1) (2 * m1 + 8) 1 (repeat (1, 2) (n2 + 2)
        ++ ((2, 2) :: (1, 1) :: Tail)) 1); lia. }
    apply hsteps_refl. }
  (* POP chain over the second spine *)
  apply (hsteps_trans _ (HB (x :: pb) (A1 + n2 + 4) 1
    (2 * m1 + 2 * n2 + 13) ((2, 2) :: (1, 1) :: Tail) 1)).
  { replace (A1 + n2 + 4) with (S (S A1) + (n2 + 2)) by lia.
    replace (2 * m1 + 2 * n2 + 13) with (2 * m1 + 9 + 2 * (n2 + 2))
      by lia.
    apply (pop12 (n2 + 2) (x :: pb) (S (S A1)) (2 * m1 + 9)
      ((2, 2) :: (1, 1) :: Tail) 1); lia. }
  (* hTRANS2_1 dispatch on the residue pair itself *)
  apply (hsteps_step _ (HB (A1 + n2 + 5 :: x :: pb)
    (2 * m1 + 2 * n2 + 14) 1 3 Tail 1)).
  { replace (2 * m1 + 2 * n2 + 13) with (S (2 * m1 + 2 * n2 + 12))
      by lia.
    replace (A1 + n2 + 5) with (S (A1 + n2 + 4)) by lia.
    replace (2 * m1 + 2 * n2 + 14) with (S (S (2 * m1 + 2 * n2 + 12)))
      by lia.
    apply (hTRANS2_1 (x :: pb) (A1 + n2 + 4) (2 * m1 + 2 * n2 + 12)
      1 1 Tail 1); lia. }
  apply hsteps_refl.
Qed.

(* ----------------------------------------------------------------- *)
(* The residual core: the stage-4 boundary grind at the era frame.   *)
(* ----------------------------------------------------------------- *)

(* For M >= 1441 the stage-4 pair (2*M - 1234, 2) at frame           *)
(* [428; 57; 5], counter 822, violates the CASCADE_STAGE4 floor      *)
(* (m4 + 1 = M - 618 > 822 = s_pre): the grind re-routes through     *)
(* dips / PX2A re-basings (hsim43 evidence on the shrunk family).    *)
(* This single statement -- one pair, one fixed frame -- is all of   *)
(* CASCADE_LANDING that remains open.                                *)
Definition CASCADE_STAGE4_BIG : Prop :=
  forall M beta, 1441 <= M -> 2 <= beta ->
  exists pb a, beta <= a /\
    hsteps (HC [428; 57; 5] 822 1 2
              ((2 * M - 1234, 2) :: (1, 1) :: repeat (1, 2) (beta - 1)) 1)
           (HB pb a 1 (2 * beta + 1) [] 1).

(* ----------------------------------------------------------------- *)
(* The composition: CASCADE_LANDING modulo CASCADE_STAGE4_BIG.       *)
(* ----------------------------------------------------------------- *)

Lemma CASCADE_LANDING_of : CASCADE_STAGE4_BIG -> CASCADE_LANDING.
Proof.
  intros Hbig. unfold CASCADE_LANDING. intros M beta HM Hb.
  assert (Hcase : M = 616 \/ M = 617 \/ M = 618
                   \/ (619 <= M /\ M <= 1440) \/ 1441 <= M) by lia.
  destruct Hcase as [HM616|[HM617|[HM618|[[HMlo HMhi]|HMbig]]]].
  - (* M = 616: r2 = 2, the TRANS2_1 dispatch branch. *)
    subst M.
    exists [429; 57; 5], (824 + (beta - 1)). split; [lia|].
    apply (hsteps_trans _ (HC [57; 5] 90 1 2
      ((145, 2) :: (1, 1) :: (1, 2) :: (1, 2) :: repeat (1, 2) 334
       ++ ((2 * 616 - 1230, 2) :: (1, 1) :: repeat (1, 2) (beta - 1))) 1)).
    { apply (CASCADE_STAGE1 40 149 ((1, 2) :: (1, 2)
        :: repeat (1, 2) 334
        ++ ((2 * 616 - 1230, 2) :: (1, 1) :: repeat (1, 2) (beta - 1))));
      lia. }
    apply (hsteps_trans _ (HB [429; 57; 5] 824 1 3
      (repeat (1, 2) (beta - 1)) 1)).
    { apply (CASCADE_STAGE23_r2_2 71 334 57 [5] 90
        (repeat (1, 2) (beta - 1))); lia. }
    apply (CASCADE_POPFIN [429; 57; 5] 824 beta); lia.
  - (* M = 617: r2 = 4, the TRANS2_2 dispatch branch. *)
    subst M.
    exists [823; 428; 57; 5], (3 + (beta - 1)). split; [lia|].
    apply (hsteps_trans _ (HC [57; 5] 90 1 2
      ((145, 2) :: (1, 1) :: (1, 2) :: (1, 2) :: repeat (1, 2) 334
       ++ ((2 * 617 - 1230, 2) :: (1, 1) :: repeat (1, 2) (beta - 1))) 1)).
    { apply (CASCADE_STAGE1 40 149 ((1, 2) :: (1, 2)
        :: repeat (1, 2) 334
        ++ ((2 * 617 - 1230, 2) :: (1, 1) :: repeat (1, 2) (beta - 1))));
      lia. }
    apply (hsteps_trans _ (HB [823; 428; 57; 5] 3 1 3
      (repeat (1, 2) (beta - 1)) 1)).
    { apply (CASCADE_STAGE23_r2_4 71 334 57 [5] 90
        (repeat (1, 2) (beta - 1))); lia. }
    apply (CASCADE_POPFIN [823; 428; 57; 5] 3 beta); lia.
  - (* M = 618: r2 = 6; stage 4 degenerates to TDN + TRANS2_1. *)
    subst M.
    exists [823; 428; 57; 5], (5 + (beta - 1)). split; [lia|].
    apply (hsteps_trans _ (HC [57; 5] 90 1 2
      ((145, 2) :: (1, 1) :: (1, 2) :: (1, 2) :: repeat (1, 2) 334
       ++ ((2 * 618 - 1230, 2) :: (1, 1) :: repeat (1, 2) (beta - 1))) 1)).
    { apply (CASCADE_STAGE1 40 149 ((1, 2) :: (1, 2)
        :: repeat (1, 2) 334
        ++ ((2 * 618 - 1230, 2) :: (1, 1) :: repeat (1, 2) (beta - 1))));
      lia. }
    apply (hsteps_trans _ (HB [823; 428; 57; 5] 5 1 3
      (repeat (1, 2) (beta - 1)) 1)).
    { apply (hsteps_trans _ (HC [428; 57; 5] 822 1 2
        ((2, 2) :: (1, 1) :: repeat (1, 2) (beta - 1)) 1)).
      { apply (CASCADE_STAGE23 71 334 (2 * 618 - 1230) 57 [5] 90
          (repeat (1, 2) (beta - 1))); lia. }
      apply (hsteps_trans _ (HB [428; 57; 5] 822 1 4
        ((2, 2) :: (1, 1) :: repeat (1, 2) (beta - 1)) 1)).
      { apply (hsteps_step _ (HB [428; 57; 5] 822 1 4
          ((2, 2) :: (1, 1) :: repeat (1, 2) (beta - 1)) 1)).
        { apply (hTDN [428; 57; 5] 822
            ((2, 2) :: (1, 1) :: repeat (1, 2) (beta - 1)) 1). }
        apply hsteps_refl. }
      apply (hsteps_step _ (HB [823; 428; 57; 5] 5 1 3
        (repeat (1, 2) (beta - 1)) 1)).
      { apply (hTRANS2_1 [428; 57; 5] 822 3 1 1
          (repeat (1, 2) (beta - 1)) 1); lia. }
      apply hsteps_refl. }
    apply (CASCADE_POPFIN [823; 428; 57; 5] 5 beta); lia.
  - (* 619 <= M <= 1440: the clean stage 4. *)
    exists [823; 428; 57; 5], (S (S (2 * M - 1233)) + (beta - 1)).
    split; [lia|].
    apply (hsteps_trans _ (HC [57; 5] 90 1 2
      ((145, 2) :: (1, 1) :: (1, 2) :: (1, 2) :: repeat (1, 2) 334
       ++ ((2 * M - 1230, 2) :: (1, 1) :: repeat (1, 2) (beta - 1))) 1)).
    { apply (CASCADE_STAGE1 40 149 ((1, 2) :: (1, 2)
        :: repeat (1, 2) 334
        ++ ((2 * M - 1230, 2) :: (1, 1) :: repeat (1, 2) (beta - 1))));
      lia. }
    apply (hsteps_trans _ (HC [428; 57; 5] 822 1 2
      ((2 * M - 1230 - 4, 2) :: (1, 1) :: repeat (1, 2) (beta - 1)) 1)).
    { apply (CASCADE_STAGE23 71 334 (2 * M - 1230) 57 [5] 90
        (repeat (1, 2) (beta - 1))); lia. }
    apply (hsteps_trans _ (HB [823; 428; 57; 5] (S (S (2 * M - 1233)))
      1 3 (repeat (1, 2) (beta - 1)) 1)).
    { apply (hsteps_trans _ (HB [428; 57; 5] 822 1 (2 * (M - 619) + 6)
        ((2, 2) :: (1, 1) :: repeat (1, 2) (beta - 1)) 1)).
      { replace (2 * M - 1230 - 4) with (2 * (M - 619) + 4) by lia.
        apply (CASCADE_STAGE4 (M - 619) [428; 57; 5] 822
          ((1, 1) :: repeat (1, 2) (beta - 1))); lia. }
      apply (hsteps_step _ (HB [823; 428; 57; 5] (S (S (2 * M - 1233)))
        1 3 (repeat (1, 2) (beta - 1)) 1)).
      { replace (2 * (M - 619) + 6) with (S (2 * M - 1233)) by lia.
        apply (hTRANS2_1 [428; 57; 5] 822 (2 * M - 1233) 1 1
          (repeat (1, 2) (beta - 1)) 1); lia. }
      apply hsteps_refl. }
    apply (CASCADE_POPFIN [823; 428; 57; 5] (S (S (2 * M - 1233)))
      beta); lia.
  - (* M >= 1441: the residual core. *)
    destruct (Hbig M beta HMbig Hb) as [pb [a [Ha Hsteps]]].
    exists pb, a. split; [exact Ha|].
    apply (hsteps_trans _ (HC [57; 5] 90 1 2
      ((145, 2) :: (1, 1) :: (1, 2) :: (1, 2) :: repeat (1, 2) 334
       ++ ((2 * M - 1230, 2) :: (1, 1) :: repeat (1, 2) (beta - 1))) 1)).
    { apply (CASCADE_STAGE1 40 149 ((1, 2) :: (1, 2)
        :: repeat (1, 2) 334
        ++ ((2 * M - 1230, 2) :: (1, 1) :: repeat (1, 2) (beta - 1))));
      lia. }
    apply (hsteps_trans _ (HC [428; 57; 5] 822 1 2
      ((2 * M - 1234, 2) :: (1, 1) :: repeat (1, 2) (beta - 1)) 1)).
    { replace (2 * M - 1234) with (2 * M - 1230 - 4) by lia.
      apply (CASCADE_STAGE23 71 334 (2 * M - 1230) 57 [5] 90
        (repeat (1, 2) (beta - 1))); lia. }
    exact Hsteps.
Qed.

(* ----------------------------------------------------------------- *)
(* The phase-8 era law modulo CASCADE_STAGE4_BIG.                    *)
(* ----------------------------------------------------------------- *)

Lemma ESC_ERA_LAW_43 : CASCADE_STAGE4_BIG ->
  forall M beta, 616 <= M -> 2 <= beta ->
  exists n c pb a,
    run n (esc_src (2 * M + 52) (beta - 2)) = Some c
    /\ cfg_sim c (rcsec (false :: repeat true (S a) ++ enc pb)
                        (2 * beta + 2) [(1, 2)])
    /\ beta <= a.
Proof.
  intros Hbig. apply ESC_ERA_LAW_42.
  exact (CASCADE_LANDING_of Hbig).
Qed.

(* ----------------------------------------------------------------- *)
(* Assumption audit                                                  *)
(* ----------------------------------------------------------------- *)

Print Assumptions pop12.
Print Assumptions GG_rounds_odd.
Print Assumptions GG_odd.
Print Assumptions CASCADE_STAGE1.
Print Assumptions CASCADE_STAGE23.
Print Assumptions CASCADE_STAGE23_r2_4.
Print Assumptions CASCADE_STAGE23_r2_2.
Print Assumptions CASCADE_LANDING_of.
Print Assumptions ESC_ERA_LAW_43.
