(* ================================================================= *)
(*  Phase 44: CASCADE_STAGE4_BIG reduced to CASCADE_STAGE4_TAIL.     *)
(*                                                                   *)
(*  Phase 43 reduced the ESC side of H_LOOP to the single core       *)
(*  CASCADE_STAGE4_BIG (Grind11.v): the stage-4 boundary grind of    *)
(*  the pair (2 * M - 1234, 2) at the fixed era frame [428; 57; 5],  *)
(*  counter 822, for M >= 1441.  Phase 44 characterises that grind   *)
(*  at the general 3-block frame [f; p; 5] (rocq/hsim44.py, ALL      *)
(*  PASS: segment boundaries asserted verbatim in the walk           *)
(*  histories at 9 stage-4 points, T4-source walks at 5 points,      *)
(*  one growth probe) and mechanises every segment except the        *)
(*  last:                                                            *)
(*                                                                   *)
(*    SEG1  the boundary grind at [f; p; 5] (pair (2m + 4, 2),       *)
(*          counter a <= m): the clean rounds run until the          *)
(*          counter budget j = a is exhausted, the last round        *)
(*          re-routes through DIPDESC a and the section empties      *)
(*          onto the PX2A-ready form; hPX2A re-bases to [5].         *)
(*          = GG_boundary + hPX2A.                                   *)
(*    SEG2  PUSH, the same boundary grind at [5] (counter            *)
(*          p - 2 <= mp, pair (2 * mp + 4, 2)), hPX2B5 re-basing     *)
(*          to [0].  = hPUSH + GG_boundary + hPX2B5.                 *)
(*    T1    POP (1, 1), pop12 p, hTUP, hGRIND_even p: the (g2, 2)    *)
(*          pair is re-based to (g2 - 2, 2) under a fresh (2, 2).    *)
(*    T2    one hTUP2_1 step: frame [p + 5; 0], pair (2 * m3 + 4, 2) *)
(*          with m3 = mp - p - 1.                                    *)
(*    T3    the era regime m3 >= 2 * p + 4 (equivalently             *)
(*          f > 6 * p + 14 at the era ratios): GG_boundary at        *)
(*          counter 2 * p + 4 + hPX2A0 re-basing to [0].             *)
(*          (The clean regime m3 + 1 <= 2 * p + 4 is GG_clean,       *)
(*          already in Grind2.v; the era point is boundary.)         *)
(*    T4    p = 2 * q + 1 (era q = 28): hTUP, grind_prefix, two      *)
(*          rounds, hTUP, DIPDESC 3, hPX2B0 -- the last re-basing,   *)
(*          landing on the bottom frame [] with shuttle 5.           *)
(*    TAIL  the remaining core CASCADE_STAGE4_TAIL: from             *)
(*          HB [] 0 1 5 (TAILs q v3 vM a b) to the era landing       *)
(*          HB pb A 1 (2 * b + 1) [] 1.  Strictly smaller than       *)
(*          CASCADE_STAGE4_BIG: the frame is the bottom frame,       *)
(*          both PX2A re-basings and the PX2B0 dip are discharged,   *)
(*          and the parameters are the tail's own (q, v3, vM, a, b)  *)
(*          with the era parities baked in (residues 2 * v + 2;      *)
(*          the parity fence of hsim42 forbids odd residues).        *)
(*          hsim44 Part 4 traverses the tail end-to-end at the       *)
(*          minimal points (97-176 rules); at larger parameters      *)
(*          its grind depths compound (Part 5 probe: still           *)
(*          walking at 6,000,000 rules, never stuck, never a         *)
(*          wrong landing) -- its sub-structure re-enters            *)
(*          boundary grinds at regrown frames, the next target.      *)
(*                                                                   *)
(*  GG_boundary is the phase's one new totality: the dip-aware       *)
(*  rounds.  Its proof is CASCADE_STAGE4's clean decomposition       *)
(*  (TDN, TUP, hGRIND 0, rounds) with the last round replaced by     *)
(*  TUP + DIPDESC -- the budget-exhaustion dispatch.  The measure    *)
(*  is the round count a - 1 against the counter a: after a - 1      *)
(*  clean rounds (GG_rounds_part) the shuttle is 2 * a + 4 and       *)
(*  the residue pair is (2 * (m - a) + 4, 2); the boundary round's    *)
(*  section grind is DIPDESC at t = a exactly.                       *)
(* ================================================================= *)

Require Import List Bool Arith Lia ZArith.
Import ListNotations.
Require Import TM Sections Mirror TokenPass Recoord Era Esc Dev
               Grind Grind2 Grind3 Grind4 Grind5 Grind6 Grind7 Grind8
               Grind9 Grind10 Grind11.

Ltac sec_eq := repeat (first [ solve [reflexivity] | solve [lia]
                             | f_equal ]).

(* ----------------------------------------------------------------- *)
(* The stage-4 stack family at a 3-block frame [f; p; 5], counter    *)
(* a, pair (2 * m + 4, 2), tail (1, 1) :: (1, 2)^(b - 1); mp is the   *)
(* seg-2 pair parameter (seg-2 pair (2 * mp + 4, 2) = (f - 4, 2)),   *)
(* m3 = mp - p - 1 the T3 pair parameter, p = 2 * q + 1 at T4.       *)
(* ----------------------------------------------------------------- *)

Definition S1s (a m b : nat) : list (nat * nat) :=
  (1, 1) :: (1, 2) :: (1, 2) :: repeat (1, 2) a ++
  ((2 * (m - a) + 2, 2) :: (1, 1) :: repeat (1, 2) (b - 1)).

Definition S2s (mp p a m b : nat) : list (nat * nat) :=
  (1, 1) :: (1, 2) :: (1, 2) :: repeat (1, 2) (p - 2) ++
  ((2 * (mp - (p - 2)) + 2, 2) :: S1s a m b).

Definition R3s (p m3 a m b : nat) : list (nat * nat) :=
  (1, 1) :: (1, 2) :: (1, 2) :: repeat (1, 2) (2 * p + 4) ++
  ((2 * (m3 - (2 * p + 4)) + 2, 2) :: S1s a m b).

Definition S4s (q m3 a m b : nat) : list (nat * nat) :=
  (1, 2) :: (1, 2) :: (1, 2) :: (1, 2) ::
  ((2 * q - 8, 2) :: R3s (2 * q + 1) m3 a m b).

Definition TAILs (q v3 vM a b : nat) : list (nat * nat) :=
  (1, 2) :: (1, 2) :: (1, 2) :: (1, 2) ::
  ((2 * q - 8, 2) ::
   (1, 1) :: (1, 2) :: (1, 2) :: repeat (1, 2) (4 * q + 6) ++
   ((2 * v3 + 2, 2) ::
    (1, 1) :: (1, 2) :: (1, 2) :: repeat (1, 2) a ++
    ((2 * vM + 2, 2) :: (1, 1) :: repeat (1, 2) (b - 1)))).

(* ----------------------------------------------------------------- *)
(* GG_rounds_part: k clean rounds on an arbitrary even-headed pair   *)
(* (g, 2) -- GG_rounds with the endpoint left symbolic (the rounds   *)
(* of GG_boundary stop early, at the budget boundary).               *)
(* ----------------------------------------------------------------- *)

Lemma GG_rounds_part : forall k j0 pb a2 g P G,
  j0 + k + 1 <= a2 -> 2 * k + 3 <= g ->
  hsteps (HB pb a2 1 (2 * j0 + 6) ((g, 2) :: P) G)
         (HB pb a2 1 (2 * (j0 + k) + 6) ((g - 2 * k, 2) :: P) G).
Proof.
  induction k as [|k IH]; intros j0 pb a2 g P G Hf Hg.
  - replace (2 * (j0 + 0) + 6) with (2 * j0 + 6) by lia.
    replace (g - 2 * 0) with g by lia.
    apply hsteps_refl.
  - apply (hsteps_trans _ (HB pb a2 1 (2 * (j0 + 1) + 6)
        ((g - 2, 2) :: P) G)).
    { replace (2 * j0 + 6) with (2 * (j0 + 1) + 4) by lia.
      apply (grind_round (j0 + 1) pb a2 g P G); lia. }
    replace (2 * (j0 + S k) + 6) with (2 * ((j0 + 1) + k) + 6)
      by lia.
    replace (g - 2 * S k) with (g - 2 - 2 * k) by lia.
    apply (IH (j0 + 1) pb a2 (g - 2) P G); lia.
Qed.

(* ----------------------------------------------------------------- *)
(* GG_boundary: the boundary grind of the pair (2 * m + 4, 2) at     *)
(* counter a <= m.  The clean rounds (GG_rounds_part, a - 1 of       *)
(* them) exhaust the counter budget; the last round's section        *)
(* grind is DIPDESC at t = a, emptying the section onto the          *)
(* PX2A-ready form HC pb 0 3 2 (spine ++ residue).  Frame- and       *)
(* rest-general, G-general.                                          *)
(* ----------------------------------------------------------------- *)

Lemma GG_boundary : forall a m pb w G, 1 <= a -> a <= m ->
  hsteps (HC pb a 1 2 ((2 * m + 4, 2) :: w) G)
         (HC pb 0 3 2 (repeat (1, 2) a ++
                        ((2 * (m - a) + 2, 2) :: w)) G).
Proof.
  intros a m pb w G Ha Ham.
  (* TDN *)
  apply (hsteps_trans _ (HB pb a 1 4 ((2 * m + 4, 2) :: w) G)).
  { apply (hsteps_step _ (HB pb a 1 4 ((2 * m + 4, 2) :: w) G)).
    { apply hTDN. }
    apply hsteps_refl. }
  (* TUP *)
  apply (hsteps_trans _ (HC pb a 3 2 ((2 * m + 2, 2) :: w) G)).
  { apply (hsteps_step _ (HC pb a 3 2 ((2 * m + 2, 2) :: w) G)).
    { replace (HB pb a 1 4 ((2 * m + 4, 2) :: w) G)
        with (HB pb a 1 (S (S 2))
                ((S (S (S (2 * m + 1))), 2) :: w) G) by sec_eq.
      replace (HC pb a 3 2 ((2 * m + 2, 2) :: w) G)
        with (HC pb a (S 2) 2 ((S (2 * m + 1), 2) :: w) G)
        by sec_eq.
      apply hTUP. }
    apply hsteps_refl. }
  (* hGRIND 0 *)
  apply (hsteps_trans _ (HB pb a 1 6 ((2 * m + 2, 2) :: w) G)).
  { replace (HC pb a 3 2 ((2 * m + 2, 2) :: w) G)
      with (HC pb a (2 * 0 + 3) 2 ((2 * m + 2, 2) :: w) G)
      by sec_eq.
    replace (HB pb a 1 6 ((2 * m + 2, 2) :: w) G)
      with (HB pb a 1 (2 * 0 + 6) ((2 * m + 2, 2) :: w) G)
      by sec_eq.
    apply hGRIND; lia. }
  (* a - 1 clean rounds: the budget runs out *)
  apply (hsteps_trans _ (HB pb a 1 (2 * a + 4)
        ((2 * (m - a) + 4, 2) :: w) G)).
  { replace (2 * a + 4) with (2 * (0 + (a - 1)) + 6) by lia.
    replace (2 * (m - a) + 4) with (2 * m + 2 - 2 * (a - 1))
      by lia.
    apply (GG_rounds_part (a - 1) 0 pb a (2 * m + 2) w G); lia. }
  (* the boundary round: TUP *)
  apply (hsteps_trans _ (HC pb a (2 * a + 3) 2
        ((2 * (m - a) + 2, 2) :: w) G)).
  { apply (hsteps_step _ (HC pb a (2 * a + 3) 2
        ((2 * (m - a) + 2, 2) :: w) G)).
    { replace (HB pb a 1 (2 * a + 4) ((2 * (m - a) + 4, 2) :: w) G)
        with (HB pb a 1 (S (S (2 * a + 2)))
                ((S (S (S (2 * (m - a) + 1))), 2) :: w) G) by sec_eq.
      replace (HC pb a (2 * a + 3) 2 ((2 * (m - a) + 2, 2) :: w) G)
        with (HC pb a (S (2 * a + 2)) 2
                ((S (2 * (m - a) + 1), 2) :: w) G) by sec_eq.
      apply hTUP. }
    apply hsteps_refl. }
  (* the boundary round: DIPDESC a *)
  apply (DIPDESC a pb ((2 * (m - a) + 2, 2) :: w) G).
Qed.

(* ----------------------------------------------------------------- *)
(* SEG1: GG_boundary at [f; p; 5] + the hPX2A re-basing to [5].      *)
(* ----------------------------------------------------------------- *)

Lemma STAGE4_SEG1 : forall f p a m b,
  3 <= f -> 1 <= p -> 1 <= a -> a <= m -> 2 <= b ->
  hsteps (HC [f; p; 5] a 1 2
            ((2 * m + 4, 2) :: (1, 1) :: repeat (1, 2) (b - 1)) 1)
         (HC [5] (p - 1) (f - 2) 2 (S1s a m b) 1).
Proof.
  intros f p a m b Hf Hp Ha Ham Hb.
  unfold S1s.
  apply (hsteps_trans _ (HC [f; p; 5] 0 3 2
    (repeat (1, 2) a ++
     ((2 * (m - a) + 2, 2) :: (1, 1) :: repeat (1, 2) (b - 1))) 1)).
  { apply (GG_boundary a m [f; p; 5]
             ((1, 1) :: repeat (1, 2) (b - 1)) 1); lia. }
  apply (hsteps_step _ (HC [5] (p - 1) (f - 2) 2
    ((1, 1) :: (1, 2) :: (1, 2) :: repeat (1, 2) a ++
     ((2 * (m - a) + 2, 2) :: (1, 1) :: repeat (1, 2) (b - 1))) 1)).
  { replace [f; p; 5]
      with (S (S (S (f - 3))) :: S (p - 1) :: [5]) by sec_eq.
    replace (f - 2) with (S (f - 3)) by lia.
    apply hPX2A. }
  apply hsteps_refl.
Qed.

(* ----------------------------------------------------------------- *)
(* SEG2: hPUSH + GG_boundary at [5] (counter p - 2, pair             *)
(* (2 * mp + 4, 2)) + the hPX2B5 re-basing to [0].                   *)
(* ----------------------------------------------------------------- *)

Lemma STAGE4_SEG2 : forall mp p a m b, 3 <= p -> p <= mp ->
  hsteps (HC [5] (p - 1) (2 * mp + 6) 2 (S1s a m b) 1)
         (HB [0] 4 1 4 (S2s mp p a m b) 1).
Proof.
  intros mp p a m b Hp Hmp.
  unfold S2s.
  (* PUSH *)
  apply (hsteps_trans _ (HC [5] (p - 2) 1 2
        ((2 * mp + 4, 2) :: S1s a m b) 1)).
  { apply (hsteps_step _ (HC [5] (p - 2) 1 2
        ((2 * mp + 4, 2) :: S1s a m b) 1)).
    { replace (HC [5] (p - 1) (2 * mp + 6) 2 (S1s a m b) 1)
        with (HC [5] (S (p - 2)) (S (S (S (2 * mp + 3)))) 2
                (S1s a m b) 1) by sec_eq.
      replace (HC [5] (p - 2) 1 2 ((2 * mp + 4, 2) :: S1s a m b) 1)
        with (HC [5] (p - 2) 1 2 ((S (2 * mp + 3), 2)
                :: S1s a m b) 1) by sec_eq.
      apply hPUSH. }
    apply hsteps_refl. }
  (* GG_boundary *)
  apply (hsteps_trans _ (HC [5] 0 3 2
    (repeat (1, 2) (p - 2) ++
     ((2 * (mp - (p - 2)) + 2, 2) :: S1s a m b)) 1)).
  { apply (GG_boundary (p - 2) mp [5] (S1s a m b) 1); lia. }
  (* PX2B5 *)
  apply (hsteps_step _ (HB [0] 4 1 4
    ((1, 1) :: (1, 2) :: (1, 2) :: repeat (1, 2) (p - 2) ++
     ((2 * (mp - (p - 2)) + 2, 2) :: S1s a m b)) 1)).
  { apply hPX2B5. }
  apply hsteps_refl.
Qed.

(* ----------------------------------------------------------------- *)
(* T1: POP (1, 1), pop12 p, hTUP, hGRIND_even p.                     *)
(* ----------------------------------------------------------------- *)

Lemma S2s_head : forall mp p a m b, 2 <= p ->
  S2s mp p a m b =
  (1, 1) :: (repeat (1, 2) p ++
             ((2 * (mp - (p - 2)) + 2, 2) :: S1s a m b)).
Proof.
  intros mp p a m b Hp. unfold S2s.
  destruct p as [|[|p']]; [lia | lia |].
  replace (S (S p') - 2) with p' by lia.
  reflexivity.
Qed.

Lemma STAGE4_T1 : forall mp p a m b, 2 <= p -> p - 1 <= mp ->
  hsteps (HB [0] 4 1 4 (S2s mp p a m b) 1)
         (HB [0] (p + 4) 1 (2 * p + 4)
            ((2, 2) :: (2 * (mp - (p - 2)), 2) :: S1s a m b) 1).
Proof.
  intros mp p a m b Hp Hmp.
  rewrite (S2s_head mp p a m b Hp).
  (* POP (1, 1) *)
  apply (hsteps_trans _ (HB [0] 5 1 5
    (repeat (1, 2) p ++
     ((2 * (mp - (p - 2)) + 2, 2) :: S1s a m b)) 1)).
  { apply (hsteps_step _ (HB [0] 5 1 5
      (repeat (1, 2) p ++
       ((2 * (mp - (p - 2)) + 2, 2) :: S1s a m b)) 1)).
    { apply (hPOP [0] 4 4 1
        (repeat (1, 2) p ++
         ((2 * (mp - (p - 2)) + 2, 2) :: S1s a m b)) 1); lia. }
    apply hsteps_refl. }
  (* pop12 p *)
  apply (hsteps_trans _ (HB [0] (5 + p) 1 (5 + 2 * p)
    ((2 * (mp - (p - 2)) + 2, 2) :: S1s a m b) 1)).
  { apply (pop12 p [0] 5 5
             ((2 * (mp - (p - 2)) + 2, 2) :: S1s a m b) 1); lia. }
  (* TUP *)
  apply (hsteps_trans _ (HC [0] (5 + p) (2 * p + 4) 2
    ((2 * (mp - (p - 2)), 2) :: S1s a m b) 1)).
  { apply (hsteps_step _ (HC [0] (5 + p) (2 * p + 4) 2
      ((2 * (mp - (p - 2)), 2) :: S1s a m b) 1)).
    { replace (HB [0] (5 + p) 1 (5 + 2 * p)
        ((2 * (mp - (p - 2)) + 2, 2) :: S1s a m b) 1)
        with (HB [0] (5 + p) 1 (S (S (2 * p + 3)))
          ((S (S (S (2 * (mp - (p - 2)) - 1))), 2)
           :: S1s a m b) 1) by sec_eq.
      replace (HC [0] (5 + p) (2 * p + 4) 2
        ((2 * (mp - (p - 2)), 2) :: S1s a m b) 1)
        with (HC [0] (5 + p) (S (2 * p + 3)) 2
          ((S (2 * (mp - (p - 2)) - 1), 2) :: S1s a m b) 1)
        by sec_eq.
      apply hTUP. }
    apply hsteps_refl. }
  (* hGRIND_even p *)
  replace (5 + p) with (S (p + 4)) by lia.
  apply (hGRIND_even p [0] (p + 4)
           ((2 * (mp - (p - 2)), 2) :: S1s a m b) 1); lia.
Qed.

(* ----------------------------------------------------------------- *)
(* T2: one hTUP2_1 step onto the two-block frame [p + 5; 0]; the     *)
(* pair becomes (2 * m3 + 4, 2) with m3 = mp - p - 1 (the displayed  *)
(* form needs mp >= p + 1; the era point has mp = 210, p = 57).      *)
(* ----------------------------------------------------------------- *)

Lemma STAGE4_T2 : forall mp p a m b, 2 <= p -> p + 1 <= mp ->
  hsteps (HB [0] (p + 4) 1 (2 * p + 4)
            ((2, 2) :: (2 * (mp - (p - 2)), 2) :: S1s a m b) 1)
         (HC [p + 5; 0] (2 * p + 4) 1 2
            ((2 * (mp - p - 1) + 4, 2) :: S1s a m b) 1).
Proof.
  intros mp p a m b Hp Hmp.
  apply (hsteps_step _ (HC [p + 5; 0] (2 * p + 4) 1 2
    ((2 * (mp - p - 1) + 4, 2) :: S1s a m b) 1)).
  { replace (HB [0] (p + 4) 1 (2 * p + 4)
      ((2, 2) :: (2 * (mp - (p - 2)), 2) :: S1s a m b) 1)
      with (HB [0] (p + 4) 1 (S (2 * p + 3))
        ((2, S (S 0)) ::
         (S (S (S (2 * (mp - (p - 2)) - 3))), 2)
         :: S1s a m b) 1) by sec_eq.
    replace (HC [p + 5; 0] (2 * p + 4) 1 2
      ((2 * (mp - p - 1) + 4, 2) :: S1s a m b) 1)
      with (HC (S (p + 4) :: [0]) (S (2 * p + 3)) (S 0) 2
        ((S (2 * (mp - (p - 2)) - 3), 2) :: S1s a m b) 1)
      by sec_eq.
    apply hTUP2_1. }
  apply hsteps_refl.
Qed.

(* ----------------------------------------------------------------- *)
(* T3, the era (boundary) regime 2 * p + 4 <= m3: GG_boundary at     *)
(* counter 2 * p + 4 + the hPX2A0 re-basing to [0].                  *)
(* ----------------------------------------------------------------- *)

Lemma STAGE4_T3 : forall p m3 a m b, 2 * p + 4 <= m3 ->
  hsteps (HC [p + 5; 0] (2 * p + 4) 1 2
            ((2 * m3 + 4, 2) :: S1s a m b) 1)
         (HB [0] 3 1 2 ((p + 1, 2) :: R3s p m3 a m b) 1).
Proof.
  intros p m3 a m b Hm3. unfold R3s.
  apply (hsteps_trans _ (HC [p + 5; 0] 0 3 2
    (repeat (1, 2) (2 * p + 4) ++
     ((2 * (m3 - (2 * p + 4)) + 2, 2) :: S1s a m b)) 1)).
  { apply (GG_boundary (2 * p + 4) m3 [p + 5; 0] (S1s a m b) 1);
    lia. }
  apply (hsteps_step _ (HB [0] 3 1 2
    ((p + 1, 2) :: (1, 1) :: (1, 2) :: (1, 2) ::
     repeat (1, 2) (2 * p + 4) ++
     ((2 * (m3 - (2 * p + 4)) + 2, 2) :: S1s a m b)) 1)).
  { replace [p + 5; 0]
      with (S (S (S (S (S p)))) :: 0 :: nil) by sec_eq.
    replace (p + 1) with (S p) by lia.
    apply hPX2A0. }
  apply hsteps_refl.
Qed.

(* ----------------------------------------------------------------- *)
(* T4 at p = 2 * q + 1: hTUP, grind_prefix, two rounds, hTUP,        *)
(* DIPDESC 3, and the hPX2B0 dip onto the bottom frame [].           *)
(* ----------------------------------------------------------------- *)

Lemma STAGE4_T4 : forall q m3 a m b, 5 <= q ->
  hsteps (HB [0] 3 1 2 ((2 * q + 2, 2) :: R3s (2 * q + 1) m3 a m b) 1)
         (HB [] 0 1 5 (S4s q m3 a m b) 1).
Proof.
  intros q m3 a m b Hq. unfold S4s.
  (* TUP *)
  apply (hsteps_trans _ (HC [0] 3 1 2
        ((2 * q, 2) :: R3s (2 * q + 1) m3 a m b) 1)).
  { apply (hsteps_step _ (HC [0] 3 1 2
        ((2 * q, 2) :: R3s (2 * q + 1) m3 a m b) 1)).
    { replace (HB [0] 3 1 2 ((2 * q + 2, 2)
                :: R3s (2 * q + 1) m3 a m b) 1)
        with (HB [0] 3 1 (S (S 0))
                ((S (S (S (2 * q - 1))), 2)
                 :: R3s (2 * q + 1) m3 a m b) 1) by sec_eq.
      replace (HC [0] 3 1 2 ((2 * q, 2)
                :: R3s (2 * q + 1) m3 a m b) 1)
        with (HC [0] 3 (S 0) 2 ((S (2 * q - 1), 2)
                :: R3s (2 * q + 1) m3 a m b) 1) by sec_eq.
      apply hTUP. }
    apply hsteps_refl. }
  (* grind_prefix *)
  apply (hsteps_trans _ (HB [0] 3 1 6
        ((2 * q - 2, 2) :: R3s (2 * q + 1) m3 a m b) 1)).
  { replace (HC [0] 3 1 2 ((2 * q, 2)
              :: R3s (2 * q + 1) m3 a m b) 1)
      with (HC [0] (S 2) 1 2 ((S (S (S (2 * q - 3))), 2)
              :: R3s (2 * q + 1) m3 a m b) 1) by sec_eq.
    replace (HB [0] 3 1 6 ((2 * q - 2, 2)
              :: R3s (2 * q + 1) m3 a m b) 1)
      with (HB [0] (S 2) 1 6 ((S (2 * q - 3), 2)
              :: R3s (2 * q + 1) m3 a m b) 1) by sec_eq.
    apply (grind_prefix [0] 2 (2 * q - 3)
             (R3s (2 * q + 1) m3 a m b) 1). }
  (* two rounds *)
  apply (hsteps_trans _ (HB [0] 3 1 10
        ((2 * q - 6, 2) :: R3s (2 * q + 1) m3 a m b) 1)).
  { replace 10 with (2 * (0 + 2) + 6) by lia.
    replace (2 * q - 6) with (2 * q - 2 - 2 * 2) by lia.
    apply (GG_rounds_part 2 0 [0] 3 (2 * q - 2)
             (R3s (2 * q + 1) m3 a m b) 1); lia. }
  (* TUP *)
  apply (hsteps_trans _ (HC [0] 3 9 2
        ((2 * q - 8, 2) :: R3s (2 * q + 1) m3 a m b) 1)).
  { apply (hsteps_step _ (HC [0] 3 9 2
        ((2 * q - 8, 2) :: R3s (2 * q + 1) m3 a m b) 1)).
    { replace (HB [0] 3 1 10 ((2 * q - 6, 2)
                :: R3s (2 * q + 1) m3 a m b) 1)
        with (HB [0] 3 1 (S (S 8))
                ((S (S (S (2 * q - 9))), 2)
                 :: R3s (2 * q + 1) m3 a m b) 1) by sec_eq.
      replace (HC [0] 3 9 2 ((2 * q - 8, 2)
                :: R3s (2 * q + 1) m3 a m b) 1)
        with (HC [0] 3 (S 8) 2 ((S (2 * q - 9), 2)
                :: R3s (2 * q + 1) m3 a m b) 1) by sec_eq.
      apply hTUP. }
    apply hsteps_refl. }
  (* DIPDESC 3 *)
  apply (hsteps_trans _ (HC [0] 0 3 2
    (repeat (1, 2) 3 ++
     ((2 * q - 8, 2) :: R3s (2 * q + 1) m3 a m b)) 1)).
  { replace 9 with (2 * 3 + 3) by lia.
    apply (DIPDESC 3 [0]
             ((2 * q - 8, 2) :: R3s (2 * q + 1) m3 a m b) 1). }
  (* PX2B0 *)
  apply (hsteps_step _ (HB [] 0 1 5
    ((1, 2) :: (1, 2) :: (1, 2) :: (1, 2) ::
     ((2 * q - 8, 2) :: R3s (2 * q + 1) m3 a m b)) 1)).
  { apply hPX2B0. }
  apply hsteps_refl.
Qed.

(* ----------------------------------------------------------------- *)
(* The residual core: the tail at the bottom frame.                  *)
(* ----------------------------------------------------------------- *)

Definition CASCADE_STAGE4_TAIL : Prop :=
  forall q v3 vM a b, 5 <= q -> 2 <= b ->
  exists pb A, b <= A /\
    hsteps (HB [] 0 1 5 (TAILs q v3 vM a b) 1)
           (HB pb A 1 (2 * b + 1) [] 1).

Lemma S4s_era : forall M beta, 1441 <= M ->
  S4s 28 152 822 (M - 619) beta = TAILs 28 34 (M - 1441) 822 beta.
Proof.
  intros M beta HM. unfold S4s, R3s, S1s, TAILs.
  replace ((M - 619) - 822) with (M - 1441) by lia.
  reflexivity.
Qed.

(* ----------------------------------------------------------------- *)
(* The composition: CASCADE_STAGE4_BIG modulo CASCADE_STAGE4_TAIL, *)
(* at the era point f = 428, p = 57, a = 822, mp = 210, m3 = 152,    *)
(* q = 28, m = M - 619.                                              *)
(* ----------------------------------------------------------------- *)

Lemma CASCADE_STAGE4_BIG_of : CASCADE_STAGE4_TAIL ->
  CASCADE_STAGE4_BIG.
Proof.
  intros HT. unfold CASCADE_STAGE4_BIG. intros M beta HM Hb.
  destruct (HT 28 34 (M - 1441) 822 beta ltac:(lia) Hb)
    as [pb [A [HA Htail]]].
  exists pb, A. split; [exact HA |].
  apply (hsteps_trans _ (HC [5] 56 426 2
        (S1s 822 (M - 619) beta) 1)).
  { replace (2 * M - 1234) with (2 * (M - 619) + 4) by lia.
    apply (STAGE4_SEG1 428 57 822 (M - 619) beta); lia. }
  apply (hsteps_trans _ (HB [0] 4 1 4
        (S2s 210 57 822 (M - 619) beta) 1)).
  { apply (STAGE4_SEG2 210 57 822 (M - 619) beta); lia. }
  apply (hsteps_trans _ (HB [0] 61 1 118
        ((2, 2) :: (2 * (210 - (57 - 2)), 2)
         :: S1s 822 (M - 619) beta) 1)).
  { apply (STAGE4_T1 210 57 822 (M - 619) beta); lia. }
  apply (hsteps_trans _ (HC [62; 0] 118 1 2
        ((2 * (210 - 57 - 1) + 4, 2)
         :: S1s 822 (M - 619) beta) 1)).
  { apply (STAGE4_T2 210 57 822 (M - 619) beta); lia. }
  apply (hsteps_trans _ (HB [0] 3 1 2
        ((58, 2) :: R3s 57 152 822 (M - 619) beta) 1)).
  { replace (2 * (210 - 57 - 1) + 4) with (2 * 152 + 4) by lia.
    replace 62 with (57 + 5) by lia.
    apply (STAGE4_T3 57 152 822 (M - 619) beta); lia. }
  apply (hsteps_trans _ (HB [] 0 1 5
        (S4s 28 152 822 (M - 619) beta) 1)).
  { replace 58 with (2 * 28 + 2) by lia.
    replace 57 with (2 * 28 + 1) by lia.
    apply (STAGE4_T4 28 152 822 (M - 619) beta); lia. }
  rewrite (S4s_era M beta HM).
  exact Htail.
Qed.

(* ----------------------------------------------------------------- *)
(* The phase-8 era law, reduced to CASCADE_STAGE4_TAIL.              *)
(* ----------------------------------------------------------------- *)

Lemma ESC_ERA_LAW_44 : CASCADE_STAGE4_TAIL ->
  forall M beta, 616 <= M -> 2 <= beta ->
  exists n c pb a,
    run n (esc_src (2 * M + 52) (beta - 2)) = Some c
    /\ cfg_sim c (rcsec (false :: repeat true (S a) ++ enc pb)
                        (2 * beta + 2) [(1, 2)])
    /\ beta <= a.
Proof.
  intros HT M beta HM Hb.
  apply (ESC_ERA_LAW_43 (CASCADE_STAGE4_BIG_of HT) M beta HM Hb).
Qed.

(* ----------------------------------------------------------------- *)
(* Assumption audit                                                  *)
(* ----------------------------------------------------------------- *)

Print Assumptions GG_rounds_part.
Print Assumptions GG_boundary.
Print Assumptions STAGE4_SEG1.
Print Assumptions STAGE4_SEG2.
Print Assumptions STAGE4_T1.
Print Assumptions STAGE4_T2.
Print Assumptions STAGE4_T3.
Print Assumptions STAGE4_T4.
Print Assumptions CASCADE_STAGE4_BIG_of.
Print Assumptions ESC_ERA_LAW_44.
