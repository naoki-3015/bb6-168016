(* ================================================================= *)
(*  Grind14.v -- Phase 46: the TAIL2_BIG dip descent, mechanised    *)
(*  in the range the current vocabulary closes, and reduced to a    *)
(*  strictly smaller core.                                          *)
(*                                                                  *)
(*  Phase 45 left the ESC side of H_LOOP resting on TAIL2_BIG       *)
(*  (Grind13.v): the layer-2 residue totality at the ONE fixed      *)
(*  state HB [243; 135; 35; 20; 0] 893 1 1651                       *)
(*  ((2 * vM + 2, 2) :: (1, 1) :: (1, 2)^(beta - 1)) for            *)
(*  vM >= 1653.  Its front (TUP, hGRIND_even 823, TUP2_1,           *)
(*  GG_boundary (1650, vM - 3), PX2A) lands at                      *)
(*                                                                  *)
(*    px(k, beta) = HC [135; 35; 20; 0] 242 891 2 (PXs k beta),     *)
(*    k = vM - 1652 >= 1,                                           *)
(*    PXs k beta = (1, 1) :: (1, 2) :: (1, 2) :: (1, 2)^1650        *)
(*                 ++ ((2k, 2) :: (1, 1) :: (1, 2)^(beta - 1)).     *)
(*                                                                  *)
(*  Phase 45 reported the descent from px as frame-dependent with   *)
(*  no uniform cycle.  Phase 46 traces it in full                  *)
(*  (rocq/hsim46.py, ALL PASS: every waypoint below asserted        *)
(*  verbatim at k in {1, 2, 3, 48, 348, 3713} and beta in {2, 3})   *)
(*  and finds a FIXED parse, uniform in (k, beta) -- the four dip    *)
(*  levels of one recursion, each closed by the new DIPGRIND        *)
(*  (the boundary rounds at a general counter: hGRIND 0 +           *)
(*  GG_rounds_part (A - 1) + TUP + DIPDESC A):                      *)
(*                                                                  *)
(*    frame [135; 35; 20; 0], A = 241, pair (887, 2): DIPGRIND to   *)
(*      the dip pair (405, 2), then PX2A;                           *)
(*    frame [20; 0], A = 33, pair (129, 2): DIPGRIND to (63, 2),    *)
(*      then PX2A0 (the second block is 0);                         *)
(*    frame [0], A = 3, pair (12, 2): DIPGRIND to (6, 2), then      *)
(*      PX2B0, pop12 4, TUP + PUSH + TDN + TUP;                     *)
(*    frame [], A = 3, pair (8, 2) over (4, 2): DIPGRIND to         *)
(*      (2, 2), then PUSHX, pop12 3;                                *)
(*    frame regrowth (TUP2_1, TDN, TRANS2_1) onto [14; 5],          *)
(*      pop12 35;                                                   *)
(*    the (63, 2) pair: TUP + hGRIND_even 34 + TUP2_1 + TDN + TUP   *)
(*      onto frame [40; 14; 5] at pair (57, 2);                     *)
(*    the (57, 2) pair grinds CLEANLY (new CLEANG_odd) to (1, 2);   *)
(*      pop12 1, POP, pop12 243;                                    *)
(*    the (405, 2) pair: TUP + hGRIND_even 273 + TUP2_1 + TDN       *)
(*      + TUP onto frame [317; 40; 14; 5] at pair (399, 2);         *)
(*    the (399, 2) pair grinds CLEANLY (CLEANG_odd) to (1, 2);      *)
(*      pop12 1, POP, pop12 1652 -- reaching the END state          *)
(*                                                                  *)
(*    END(k, beta) = HB [317; 40; 14; 5] 2204 1 3711                *)
(*                     ((2k, 2) :: (1, 1) :: (1, 2)^(beta - 1))     *)
(*                                                                  *)
(*  (DESCENT46 below: one hsteps chain, no side condition on k.)    *)
(*                                                                  *)
(*  The END state closes UNIFORMLY for 1 <= k <= 3713 (END46_1,     *)
(*  END46_2, END46_3, END46_big): after TUP + hGRIND_even 1853      *)
(*  + TUP2_1 + TDN + TUP the pair (2k - 6, 2) grinds CLEANLY at     *)
(*  counter 3710 (new CLEANG_even) to (2, 2), then TRANS2_1 +       *)
(*  CASCADE_POPFIN.  The floor of CLEANG_even is exactly            *)
(*  2k - 6 <= 2 * 3710, i.e. k <= 3713.  At k >= 3714 the rounds    *)
(*  hit the DIPDESC boundary instead (hsim46 Part 4: the config     *)
(*  HC [2204; 317; 40; 14; 5] 3710 7423 ((2, 2) :: (1, 1) :: ...)   *)
(*  occurs at k = 3714) and the walk completes only through a       *)
(*  further frame descent whose finals gain a cycle per k-band     *)
(*  (k = 3714: frame [4002; 1279; 745; 151; 77; 35; 20; 0];         *)
(*  k = 5000: frame [7427; 4001; 1279; 745; 151; 77; 35; 20; 0])    *)
(*  -- the Phase 38 wall, one level further down.  The residual    *)
(*  core is therefore the END totality for k >= 3714 alone:         *)
(*                                                                  *)
(*    TAIL2_END (Definition below; a lemma parameter, never an      *)
(*    axiom).                                                       *)
(*                                                                  *)
(*  TAIL2_BIG_of discharges Grind13's TAIL2_BIG from TAIL2_END:     *)
(*  TAIL2_BIG is PROVED for 1653 <= vM <= 5365 (k <= 3713) and      *)
(*  reduced, for vM >= 5366, to the single-pair totality at the     *)
(*  single fixed END state -- strictly smaller than TAIL2_BIG       *)
(*  (one B-section state, one pair, no 1651-counter front, no       *)
(*  four-level descent).  ESC_ERA_LAW_46 carries it to the era      *)
(*  law, and Loop.v's ESC_ITER_BIG8_46 discharges H_LOOP's ESC      *)
(*  instances at every even R >= 1278 modulo TAIL2_END alone.       *)
(* ================================================================= *)

Require Import List Bool Arith Lia ZArith.
Import ListNotations.
Require Import TM Sections Mirror TokenPass Recoord Era Esc Dev
               Grind Grind2 Grind3 Grind4 Grind5 Grind6 Grind7 Grind8
               Grind9 Grind10 Grind11 Grind12 Grind13.

(* ----------------------------------------------------------------- *)
(* Arithmetic-form one-step wrappers for the hstep constructors     *)
(* used below (the constructors are stated in S-form; the segment   *)
(* arithmetic is cleaner in subtraction form).                      *)
(* ----------------------------------------------------------------- *)

Lemma sTUP : forall pb a s g r w G, 2 <= s -> 3 <= g ->
  hsteps (HB pb a 1 s ((g, r) :: w) G)
         (HC pb a (s - 1) 2 ((g - 2, r) :: w) G).
Proof.
  intros pb a s g r w G Hs Hg.
  replace s with (S (S (s - 2))) by lia.
  replace g with (S (S (S (g - 3)))) by lia.
  apply (hsteps_step _ (HC pb a (S (s - 2)) 2 ((S (g - 3), r) :: w) G)).
  - apply hTUP.
  - apply hsteps_refl.
Qed.

Lemma sPUSH : forall pb a g w G, 3 <= g ->
  hsteps (HC pb (S a) g 2 w G) (HC pb a 1 2 ((g - 2, 2) :: w) G).
Proof.
  intros pb a g w G Hg.
  replace g with (S (S (S (g - 3)))) by lia.
  apply (hsteps_step _ (HC pb a 1 2 ((S (g - 3), 2) :: w) G)).
  - apply hPUSH.
  - apply hsteps_refl.
Qed.

Lemma sTDN : forall pb a w G,
  hsteps (HC pb a 1 2 w G) (HB pb a 1 4 w G).
Proof.
  intros pb a w G.
  apply (hsteps_step _ (HB pb a 1 4 w G)).
  - apply hTDN.
  - apply hsteps_refl.
Qed.

Lemma sPOP1 : forall pb a s w G, 2 <= s ->
  hsteps (HB pb a 1 s ((1, 1) :: w) G) (HB pb (S a) 1 (s + 1) w G).
Proof.
  intros pb a s w G Hs.
  apply (hsteps_step _ (HB pb (S a) 1 (s + 1) w G)).
  - apply hPOP; lia.
  - apply hsteps_refl.
Qed.

Lemma sTUP2_1 : forall pb a s g w G, 3 <= g ->
  hsteps (HB pb a 1 (S s) ((2, 2) :: (g, 2) :: w) G)
         (HC (S a :: pb) (S s) 1 2 ((g - 2, 2) :: w) G).
Proof.
  intros pb a s g w G Hg.
  replace g with (S (S (S (g - 3)))) by lia.
  apply (hsteps_step _ (HC (S a :: pb) (S s) 1 2
                          ((S (g - 3), 2) :: w) G)).
  - apply hTUP2_1.
  - apply hsteps_refl.
Qed.

Lemma sTRANS2_1 : forall pb a s' r2 w G, 1 <= r2 ->
  hsteps (HB pb a 1 (S s') ((2, 2) :: (1, r2) :: w) G)
         (HB (S a :: pb) (S (S s')) 1 (S (S r2)) w G).
Proof.
  intros pb a s' r2 w G Hr.
  apply (hsteps_step _ (HB (S a :: pb) (S (S s')) 1 (S (S r2)) w G)).
  - apply hTRANS2_1; lia.
  - apply hsteps_refl.
Qed.

(* ----------------------------------------------------------------- *)
(* DIPGRIND: the boundary rounds at a general counter.              *)
(* HC pb A 3 ((2A + r, 2) :: w) grinds, via hGRIND 0 +              *)
(* GG_rounds_part (A - 1) + TUP, to the DIPDESC source at pair      *)
(* (r + 2, 2) and descends: HC pb 0 3 (spine A ++ ((r, 2) :: w)).   *)
(* The four dip levels of the descent are (A, r) = (241, 405),      *)
(* (33, 63), (3, 6), (3, 2).                                        *)
(* ----------------------------------------------------------------- *)

Lemma DIPGRIND : forall A r pb w G, 1 <= A -> 1 <= r ->
  hsteps (HC pb A 3 2 ((2 * A + r, 2) :: w) G)
         (HC pb 0 3 2 (repeat (1, 2) A ++ ((r, 2) :: w)) G).
Proof.
  intros A r pb w G HA Hr.
  apply (hsteps_trans _ (HB pb A 1 (2 * (0 + (A - 1)) + 6)
    ((2 * A + r - 2 * (A - 1), 2) :: w) G)).
  - apply (hsteps_trans _ (HB pb A 1 6 ((2 * A + r, 2) :: w) G)).
    + apply (hGRIND 0 pb A ((2 * A + r, 2) :: w) G); lia.
    + apply (GG_rounds_part (A - 1) 0 pb A (2 * A + r) w G); lia.
  - replace (HB pb A 1 (2 * (0 + (A - 1)) + 6)
              ((2 * A + r - 2 * (A - 1), 2) :: w) G)
      with (HB pb A 1 (2 * A + 4) ((r + 2, 2) :: w) G) by sec_eq.
    apply (hsteps_trans _ (HC pb A (2 * A + 3) 2 ((r, 2) :: w) G)).
    + replace (2 * A + 3) with (2 * A + 4 - 1) by lia.
      replace ((r, 2) :: w) with ((r + 2 - 2, 2) :: w) by sec_eq.
      apply (sTUP pb A (2 * A + 4) (r + 2) 2 w G); lia.
    + apply (DIPDESC A pb ((r, 2) :: w) G).
Qed.

(* ----------------------------------------------------------------- *)
(* CLEANG_odd: the clean grind of an odd pair (2m + 3, 2) at        *)
(* counter 3: rounds (GG_rounds_part m) to (3, 2), TUP, then        *)
(* hGRIND (m + 1) closes at (1, 2) with shuttle 2m + 8.  Floor:     *)
(* m + 2 <= A.  Instances: (m, A) = (27, 72) [pair 57] and          *)
(* (198, 550) [pair 399].                                           *)
(* ----------------------------------------------------------------- *)

Lemma CLEANG_odd : forall m pb a w G, m + 2 <= a ->
  hsteps (HC pb a 3 2 ((2 * m + 3, 2) :: w) G)
         (HB pb a 1 (2 * m + 8) ((1, 2) :: w) G).
Proof.
  intros m pb a w G Ha.
  apply (hsteps_trans _ (HB pb a 1 (2 * (0 + m) + 6)
    ((2 * m + 3 - 2 * m, 2) :: w) G)).
  - apply (hsteps_trans _ (HB pb a 1 6 ((2 * m + 3, 2) :: w) G)).
    + apply (hGRIND 0 pb a ((2 * m + 3, 2) :: w) G); lia.
    + apply (GG_rounds_part m 0 pb a (2 * m + 3) w G); lia.
  - replace (HB pb a 1 (2 * (0 + m) + 6)
              ((2 * m + 3 - 2 * m, 2) :: w) G)
      with (HB pb a 1 (2 * m + 6) ((3, 2) :: w) G) by sec_eq.
    apply (hsteps_trans _ (HC pb a (2 * m + 5) 2 ((1, 2) :: w) G)).
    + replace (2 * m + 5) with (2 * m + 6 - 1) by lia.
      replace ((1, 2) :: w) with ((3 - 2, 2) :: w) by sec_eq.
      apply (sTUP pb a (2 * m + 6) 3 2 w G); lia.
    + replace (2 * m + 5) with (2 * (m + 1) + 3) by lia.
      replace (2 * m + 8) with (2 * (m + 1) + 6) by lia.
      apply (hGRIND (m + 1) pb a ((1, 2) :: w) G); lia.
Qed.

(* ----------------------------------------------------------------- *)
(* CLEANG_even: the clean grind of an even pair (2m + 2, 2) at      *)
(* counter 3: hGRIND 0, GG_rounds_part (m - 1) to (4, 2), then      *)
(* grind_round m closes at (2, 2) with shuttle 2m + 6.  Floor:      *)
(* m + 1 <= A (the pair fits: 2m + 2 <= 2A).  The m = 0 case is      *)
(* hGRIND 0 alone.  Instance: (m, A) = (k - 4, 3710) at the END     *)
(* state, pair (2k - 6, 2) -- the floor m + 1 <= A is exactly       *)
(* k <= 3713.                                                       *)
(* ----------------------------------------------------------------- *)

Lemma CLEANG_even : forall m pb a w G, m + 1 <= a ->
  hsteps (HC pb a 3 2 ((2 * m + 2, 2) :: w) G)
         (HB pb a 1 (2 * m + 6) ((2, 2) :: w) G).
Proof.
  intros m pb a w G Ha.
  destruct m as [| m'].
  - apply (hGRIND 0 pb a ((2, 2) :: w) G); lia.
  - apply (hsteps_trans _ (HB pb a 1 (2 * (0 + (S m' - 1)) + 6)
      ((2 * S m' + 2 - 2 * (S m' - 1), 2) :: w) G)).
    + apply (hsteps_trans _ (HB pb a 1 6 ((2 * S m' + 2, 2) :: w) G)).
      * apply (hGRIND 0 pb a ((2 * S m' + 2, 2) :: w) G); lia.
      * apply (GG_rounds_part (S m' - 1) 0 pb a (2 * S m' + 2) w G);
          lia.
    + replace (HB pb a 1 (2 * (0 + (S m' - 1)) + 6)
                ((2 * S m' + 2 - 2 * (S m' - 1), 2) :: w) G)
        with (HB pb a 1 (2 * S m' + 4) ((4, 2) :: w) G) by sec_eq.
      apply (grind_round (S m') pb a 4 w G); lia.
Qed.

(* ----------------------------------------------------------------- *)
(* The descent stacks (raw expanded forms, as the PX2A / PX2A0     *)
(* landings produce them).                                          *)
(* ----------------------------------------------------------------- *)

Definition PXs (k b : nat) : list (nat * nat) :=
  (1, 1) :: (1, 2) :: (1, 2) :: repeat (1, 2) 1650
    ++ ((2 * k, 2) :: (1, 1) :: repeat (1, 2) (b - 1)).

Definition W1s (k b : nat) : list (nat * nat) :=
  (1, 1) :: (1, 2) :: (1, 2) :: repeat (1, 2) 241
    ++ ((405, 2) :: PXs k b).

Definition W2s (k b : nat) : list (nat * nat) :=
  (1, 1) :: (1, 2) :: (1, 2) :: repeat (1, 2) 33
    ++ ((63, 2) :: W1s k b).

(* ----------------------------------------------------------------- *)
(* TAIL2_FRONT: the TAIL2_BIG source reaches px(k, beta) with       *)
(* k = vM - 1652 (TUP, hGRIND_even 823, TUP2_1,                     *)
(* GG_boundary (1650, vM - 3), PX2A).                               *)
(* ----------------------------------------------------------------- *)

Lemma TAIL2_FRONT : forall vM beta, 1653 <= vM -> 2 <= beta ->
  hsteps (HB [243; 135; 35; 20; 0] 893 1 1651
            ((2 * vM + 2, 2) :: (1, 1) :: repeat (1, 2) (beta - 1)) 1)
         (HC [135; 35; 20; 0] 242 891 2 (PXs (vM - 1652) beta) 1).
Proof.
  intros vM beta HvM Hb.
  (* TUP *)
  apply (hsteps_trans _ (HC [243; 135; 35; 20; 0] 893 1650 2
    ((2 * vM + 2 - 2, 2) :: (1, 1) :: repeat (1, 2) (beta - 1)) 1)).
  { apply (sTUP [243; 135; 35; 20; 0] 893 1651 (2 * vM + 2) 2
           ((1, 1) :: repeat (1, 2) (beta - 1)) 1); lia. }
  replace (HC [243; 135; 35; 20; 0] 893 1650 2
             ((2 * vM + 2 - 2, 2) :: (1, 1) :: repeat (1, 2) (beta - 1)) 1)
    with (HC [243; 135; 35; 20; 0] 893 1650 2
             ((2 * vM, 2) :: (1, 1) :: repeat (1, 2) (beta - 1)) 1)
    by sec_eq.
  (* hGRIND_even 823 *)
  apply (hsteps_trans _ (HB [243; 135; 35; 20; 0] 892 1 1650
    ((2, 2) :: (2 * vM, 2) :: (1, 1) :: repeat (1, 2) (beta - 1)) 1)).
  { apply (hGRIND_even 823 [243; 135; 35; 20; 0] 892
           ((2 * vM, 2) :: (1, 1) :: repeat (1, 2) (beta - 1)) 1); lia. }
  (* TUP2_1 *)
  apply (hsteps_trans _ (HC [893; 243; 135; 35; 20; 0] 1650 1 2
    ((2 * vM - 2, 2) :: (1, 1) :: repeat (1, 2) (beta - 1)) 1)).
  { apply (sTUP2_1 [243; 135; 35; 20; 0] 892 1649 (2 * vM)
           ((1, 1) :: repeat (1, 2) (beta - 1)) 1); lia. }
  (* GG_boundary (1650, vM - 3) *)
  apply (hsteps_trans _ (HC [893; 243; 135; 35; 20; 0] 0 3 2
    (repeat (1, 2) 1650
     ++ ((2 * ((vM - 3) - 1650) + 2, 2) :: (1, 1)
         :: repeat (1, 2) (beta - 1))) 1)).
  { replace (2 * vM - 2) with (2 * (vM - 3) + 4) by lia.
    apply (GG_boundary 1650 (vM - 3) [893; 243; 135; 35; 20; 0]
           ((1, 1) :: repeat (1, 2) (beta - 1)) 1); lia. }
  replace (HC [893; 243; 135; 35; 20; 0] 0 3 2
             (repeat (1, 2) 1650
              ++ ((2 * ((vM - 3) - 1650) + 2, 2) :: (1, 1)
                  :: repeat (1, 2) (beta - 1))) 1)
    with (HC [893; 243; 135; 35; 20; 0] 0 3 2
             (repeat (1, 2) 1650
              ++ ((2 * (vM - 1652), 2) :: (1, 1)
                  :: repeat (1, 2) (beta - 1))) 1)
    by sec_eq.
  (* PX2A *)
  apply (hsteps_step _ (HC [135; 35; 20; 0] 242 891 2
                          (PXs (vM - 1652) beta) 1)).
  { apply hPX2A. }
  apply hsteps_refl.
Qed.

(* ----------------------------------------------------------------- *)
(* DESCENT46: the dip descent from px(k, beta) to END(k, beta),     *)
(* as ONE hsteps chain, uniform in (k, beta) -- no side             *)
(* conditions.  Waypoints as asserted by hsim46.py Part 1.          *)
(* ----------------------------------------------------------------- *)

Lemma DESCENT46 : forall k b,
  hsteps (HC [135; 35; 20; 0] 242 891 2 (PXs k b) 1)
         (HB [317; 40; 14; 5] 2204 1 3711
            ((2 * k, 2) :: (1, 1) :: repeat (1, 2) (b - 1)) 1).
Proof.
  intros k b.
  (* level [135; 35; 20; 0]: PUSH, TDN, TUP *)
  apply (hsteps_trans _ (HC [135; 35; 20; 0] 241 1 2
    ((889, 2) :: PXs k b) 1)).
  { apply (sPUSH [135; 35; 20; 0] 241 891 (PXs k b) 1); lia. }
  apply (hsteps_trans _ (HB [135; 35; 20; 0] 241 1 4
    ((889, 2) :: PXs k b) 1)).
  { apply (sTDN [135; 35; 20; 0] 241 ((889, 2) :: PXs k b) 1). }
  apply (hsteps_trans _ (HC [135; 35; 20; 0] 241 3 2
    ((887, 2) :: PXs k b) 1)).
  { apply (sTUP [135; 35; 20; 0] 241 4 889 2 (PXs k b) 1); lia. }
  (* DIPGRIND (241, 405) *)
  apply (hsteps_trans _ (HC [135; 35; 20; 0] 0 3 2
    (repeat (1, 2) 241 ++ ((405, 2) :: PXs k b)) 1)).
  { apply (DIPGRIND 241 405 [135; 35; 20; 0] (PXs k b) 1); lia. }
  (* PX2A *)
  apply (hsteps_trans _ (HC [20; 0] 34 133 2
    ((1, 1) :: (1, 2) :: (1, 2) :: repeat (1, 2) 241
     ++ ((405, 2) :: PXs k b)) 1)).
  { apply (hsteps_step _ (HC [20; 0] 34 133 2
      ((1, 1) :: (1, 2) :: (1, 2) :: repeat (1, 2) 241
       ++ ((405, 2) :: PXs k b)) 1)).
    { apply hPX2A. }
    apply hsteps_refl. }
  (* level [20; 0]: PUSH, TDN, TUP *)
  apply (hsteps_trans _ (HC [20; 0] 33 1 2 ((131, 2) :: W1s k b) 1)).
  { apply (sPUSH [20; 0] 33 133 (W1s k b) 1); lia. }
  apply (hsteps_trans _ (HB [20; 0] 33 1 4 ((131, 2) :: W1s k b) 1)).
  { apply (sTDN [20; 0] 33 ((131, 2) :: W1s k b) 1). }
  apply (hsteps_trans _ (HC [20; 0] 33 3 2 ((129, 2) :: W1s k b) 1)).
  { apply (sTUP [20; 0] 33 4 131 2 (W1s k b) 1); lia. }
  (* DIPGRIND (33, 63) *)
  apply (hsteps_trans _ (HC [20; 0] 0 3 2
    (repeat (1, 2) 33 ++ ((63, 2) :: W1s k b)) 1)).
  { apply (DIPGRIND 33 63 [20; 0] (W1s k b) 1); lia. }
  (* PX2A0 *)
  apply (hsteps_trans _ (HB [0] 3 1 2 ((16, 2) :: W2s k b) 1)).
  { apply (hsteps_step _ (HB [0] 3 1 2 ((16, 2) :: W2s k b) 1)).
    { apply hPX2A0. }
    apply hsteps_refl. }
  (* level [0]: TUP, TDN, TUP *)
  apply (hsteps_trans _ (HC [0] 3 1 2 ((14, 2) :: W2s k b) 1)).
  { apply (sTUP [0] 3 2 16 2 (W2s k b) 1); lia. }
  apply (hsteps_trans _ (HB [0] 3 1 4 ((14, 2) :: W2s k b) 1)).
  { apply (sTDN [0] 3 ((14, 2) :: W2s k b) 1). }
  apply (hsteps_trans _ (HC [0] 3 3 2 ((12, 2) :: W2s k b) 1)).
  { apply (sTUP [0] 3 4 14 2 (W2s k b) 1); lia. }
  (* DIPGRIND (3, 6) *)
  apply (hsteps_trans _ (HC [0] 0 3 2
    (repeat (1, 2) 3 ++ ((6, 2) :: W2s k b)) 1)).
  { apply (DIPGRIND 3 6 [0] (W2s k b) 1); lia. }
  (* PX2B0 *)
  apply (hsteps_trans _ (HB [] 0 1 5
    ((1, 2) :: repeat (1, 2) 3 ++ ((6, 2) :: W2s k b)) 1)).
  { apply (hsteps_step _ (HB [] 0 1 5
      ((1, 2) :: repeat (1, 2) 3 ++ ((6, 2) :: W2s k b)) 1)).
    { apply hPX2B0. }
    apply hsteps_refl. }
  (* pop12 4, TUP *)
  apply (hsteps_trans _ (HB [] 4 1 13 ((6, 2) :: W2s k b) 1)).
  { apply (pop12 4 [] 0 5 ((6, 2) :: W2s k b) 1); lia. }
  apply (hsteps_trans _ (HC [] 4 12 2 ((4, 2) :: W2s k b) 1)).
  { apply (sTUP [] 4 13 6 2 (W2s k b) 1); lia. }
  (* level []: PUSH, TDN, TUP *)
  apply (hsteps_trans _ (HC [] 3 1 2 ((10, 2) :: (4, 2) :: W2s k b) 1)).
  { apply (sPUSH [] 3 12 ((4, 2) :: W2s k b) 1); lia. }
  apply (hsteps_trans _ (HB [] 3 1 4 ((10, 2) :: (4, 2) :: W2s k b) 1)).
  { apply (sTDN [] 3 ((10, 2) :: (4, 2) :: W2s k b) 1). }
  apply (hsteps_trans _ (HC [] 3 3 2 ((8, 2) :: (4, 2) :: W2s k b) 1)).
  { apply (sTUP [] 3 4 10 2 ((4, 2) :: W2s k b) 1); lia. }
  (* DIPGRIND (3, 2) over (4, 2) *)
  apply (hsteps_trans _ (HC [] 0 3 2
    (repeat (1, 2) 3 ++ ((2, 2) :: (4, 2) :: W2s k b)) 1)).
  { apply (DIPGRIND 3 2 [] ((4, 2) :: W2s k b) 1); lia. }
  (* PUSHX, pop12 3 *)
  apply (hsteps_trans _ (HB [] 1 1 7
    (repeat (1, 2) 3 ++ ((2, 2) :: (4, 2) :: W2s k b)) 1)).
  { apply (hsteps_step _ (HB [] 1 1 7
      (repeat (1, 2) 3 ++ ((2, 2) :: (4, 2) :: W2s k b)) 1)).
    { apply hPUSHX. }
    apply hsteps_refl. }
  apply (hsteps_trans _ (HB [] 4 1 13 ((2, 2) :: (4, 2) :: W2s k b) 1)).
  { apply (pop12 3 [] 1 7 ((2, 2) :: (4, 2) :: W2s k b) 1); lia. }
  (* regrowth: TUP2_1, TDN, TRANS2_1, pop12 35 *)
  apply (hsteps_trans _ (HC [5] 13 1 2 ((2, 2) :: W2s k b) 1)).
  { apply (sTUP2_1 [] 4 12 4 (W2s k b) 1); lia. }
  apply (hsteps_trans _ (HB [5] 13 1 4 ((2, 2) :: W2s k b) 1)).
  { apply (sTDN [5] 13 ((2, 2) :: W2s k b) 1). }
  apply (hsteps_trans _ (HB [14; 5] 5 1 3
    (repeat (1, 2) 35 ++ ((63, 2) :: W1s k b)) 1)).
  { apply (sTRANS2_1 [5] 13 3 1
           ((1, 2) :: (1, 2) :: repeat (1, 2) 33
            ++ ((63, 2) :: W1s k b)) 1); lia. }
  apply (hsteps_trans _ (HB [14; 5] 40 1 73 ((63, 2) :: W1s k b) 1)).
  { apply (pop12 35 [14; 5] 5 3 ((63, 2) :: W1s k b) 1); lia. }
  (* the (63, 2) pair: TUP, hGRIND_even 34, TUP2_1, TDN, TUP *)
  apply (hsteps_trans _ (HC [14; 5] 40 72 2 ((61, 2) :: W1s k b) 1)).
  { apply (sTUP [14; 5] 40 73 63 2 (W1s k b) 1); lia. }
  apply (hsteps_trans _ (HB [14; 5] 39 1 72
    ((2, 2) :: (61, 2) :: W1s k b) 1)).
  { apply (hGRIND_even 34 [14; 5] 39 ((61, 2) :: W1s k b) 1); lia. }
  apply (hsteps_trans _ (HC [40; 14; 5] 72 1 2 ((59, 2) :: W1s k b) 1)).
  { apply (sTUP2_1 [14; 5] 39 71 61 (W1s k b) 1); lia. }
  apply (hsteps_trans _ (HB [40; 14; 5] 72 1 4 ((59, 2) :: W1s k b) 1)).
  { apply (sTDN [40; 14; 5] 72 ((59, 2) :: W1s k b) 1). }
  apply (hsteps_trans _ (HC [40; 14; 5] 72 3 2 ((57, 2) :: W1s k b) 1)).
  { apply (sTUP [40; 14; 5] 72 4 59 2 (W1s k b) 1); lia. }
  (* the (57, 2) pair grinds cleanly; pop12 1, POP, pop12 243 *)
  apply (hsteps_trans _ (HB [40; 14; 5] 72 1 62 ((1, 2) :: W1s k b) 1)).
  { apply (CLEANG_odd 27 [40; 14; 5] 72 (W1s k b) 1); lia. }
  apply (hsteps_trans _ (HB [40; 14; 5] 73 1 64 (W1s k b) 1)).
  { apply (pop12 1 [40; 14; 5] 72 62 (W1s k b) 1); lia. }
  apply (hsteps_trans _ (HB [40; 14; 5] 74 1 65
    ((1, 2) :: (1, 2) :: repeat (1, 2) 241 ++ ((405, 2) :: PXs k b)) 1)).
  { apply (sPOP1 [40; 14; 5] 73 64
           ((1, 2) :: (1, 2) :: repeat (1, 2) 241
            ++ ((405, 2) :: PXs k b)) 1); lia. }
  apply (hsteps_trans _ (HB [40; 14; 5] 317 1 551
    ((405, 2) :: PXs k b) 1)).
  { apply (pop12 243 [40; 14; 5] 74 65 ((405, 2) :: PXs k b) 1); lia. }
  (* the (405, 2) pair: TUP, hGRIND_even 273, TUP2_1, TDN, TUP *)
  apply (hsteps_trans _ (HC [40; 14; 5] 317 550 2
    ((403, 2) :: PXs k b) 1)).
  { apply (sTUP [40; 14; 5] 317 551 405 2 (PXs k b) 1); lia. }
  apply (hsteps_trans _ (HB [40; 14; 5] 316 1 550
    ((2, 2) :: (403, 2) :: PXs k b) 1)).
  { apply (hGRIND_even 273 [40; 14; 5] 316 ((403, 2) :: PXs k b) 1);
      lia. }
  apply (hsteps_trans _ (HC [317; 40; 14; 5] 550 1 2
    ((401, 2) :: PXs k b) 1)).
  { apply (sTUP2_1 [40; 14; 5] 316 549 403 (PXs k b) 1); lia. }
  apply (hsteps_trans _ (HB [317; 40; 14; 5] 550 1 4
    ((401, 2) :: PXs k b) 1)).
  { apply (sTDN [317; 40; 14; 5] 550 ((401, 2) :: PXs k b) 1). }
  apply (hsteps_trans _ (HC [317; 40; 14; 5] 550 3 2
    ((399, 2) :: PXs k b) 1)).
  { apply (sTUP [317; 40; 14; 5] 550 4 401 2 (PXs k b) 1); lia. }
  (* the (399, 2) pair grinds cleanly; pop12 1, POP, pop12 1652 *)
  apply (hsteps_trans _ (HB [317; 40; 14; 5] 550 1 404
    ((1, 2) :: PXs k b) 1)).
  { apply (CLEANG_odd 198 [317; 40; 14; 5] 550 (PXs k b) 1); lia. }
  apply (hsteps_trans _ (HB [317; 40; 14; 5] 551 1 406 (PXs k b) 1)).
  { apply (pop12 1 [317; 40; 14; 5] 550 404 (PXs k b) 1); lia. }
  apply (hsteps_trans _ (HB [317; 40; 14; 5] 552 1 407
    ((1, 2) :: (1, 2) :: repeat (1, 2) 1650
     ++ ((2 * k, 2) :: (1, 1) :: repeat (1, 2) (b - 1))) 1)).
  { apply (sPOP1 [317; 40; 14; 5] 551 406
           ((1, 2) :: (1, 2) :: repeat (1, 2) 1650
            ++ ((2 * k, 2) :: (1, 1) :: repeat (1, 2) (b - 1))) 1);
      lia. }
  replace ((1, 2) :: (1, 2) :: repeat (1, 2) 1650
           ++ ((2 * k, 2) :: (1, 1) :: repeat (1, 2) (b - 1)))
    with (repeat (1, 2) 1652
          ++ ((2 * k, 2) :: (1, 1) :: repeat (1, 2) (b - 1)))
    by reflexivity.
  apply (pop12 1652 [317; 40; 14; 5] 552 407
         ((2 * k, 2) :: (1, 1) :: repeat (1, 2) (b - 1)) 1); lia.
Qed.

(* ----------------------------------------------------------------- *)
(* The END state, closed uniformly for 1 <= k <= 3713.              *)
(* ----------------------------------------------------------------- *)

Lemma END46_1 : forall b, 2 <= b ->
  hsteps (HB [317; 40; 14; 5] 2204 1 3711
            ((2, 2) :: (1, 1) :: repeat (1, 2) (b - 1)) 1)
         (HB [2205; 317; 40; 14; 5] (3712 + (b - 1)) 1 (2 * b + 1)
            [] 1).
Proof.
  intros b Hb.
  apply (hsteps_trans _ (HB [2205; 317; 40; 14; 5] 3712 1 3
    (repeat (1, 2) (b - 1)) 1)).
  { apply (sTRANS2_1 [317; 40; 14; 5] 2204 3710 1
           (repeat (1, 2) (b - 1)) 1); lia. }
  apply (CASCADE_POPFIN [2205; 317; 40; 14; 5] 3712 b); lia.
Qed.

Lemma END46_2 : forall b, 2 <= b ->
  hsteps (HB [317; 40; 14; 5] 2204 1 3711
            ((4, 2) :: (1, 1) :: repeat (1, 2) (b - 1)) 1)
         (HB [3711; 2204; 317; 40; 14; 5] (3 + (b - 1)) 1 (2 * b + 1)
            [] 1).
Proof.
  intros b Hb.
  apply (hsteps_trans _ (HC [317; 40; 14; 5] 2204 3710 2
    ((2, 2) :: (1, 1) :: repeat (1, 2) (b - 1)) 1)).
  { apply (sTUP [317; 40; 14; 5] 2204 3711 4 2
           ((1, 1) :: repeat (1, 2) (b - 1)) 1); lia. }
  apply (hsteps_trans _ (HB [317; 40; 14; 5] 2203 1 3710
    ((2, 2) :: (2, 2) :: (1, 1) :: repeat (1, 2) (b - 1)) 1)).
  { apply (hGRIND_even 1853 [317; 40; 14; 5] 2203
           ((2, 2) :: (1, 1) :: repeat (1, 2) (b - 1)) 1); lia. }
  apply (hsteps_trans _ (HB [3711; 2204; 317; 40; 14; 5] 3 1 3
    (repeat (1, 2) (b - 1)) 1)).
  { apply (hsteps_step _ (HB [3711; 2204; 317; 40; 14; 5] 3 1 3
      (repeat (1, 2) (b - 1)) 1)).
    { apply hTRANS2_2; lia. }
    apply hsteps_refl. }
  apply (CASCADE_POPFIN [3711; 2204; 317; 40; 14; 5] 3 b); lia.
Qed.

Lemma END46_3 : forall b, 2 <= b ->
  hsteps (HB [317; 40; 14; 5] 2204 1 3711
            ((6, 2) :: (1, 1) :: repeat (1, 2) (b - 1)) 1)
         (HB [3711; 2204; 317; 40; 14; 5] (5 + (b - 1)) 1 (2 * b + 1)
            [] 1).
Proof.
  intros b Hb.
  apply (hsteps_trans _ (HC [317; 40; 14; 5] 2204 3710 2
    ((4, 2) :: (1, 1) :: repeat (1, 2) (b - 1)) 1)).
  { apply (sTUP [317; 40; 14; 5] 2204 3711 6 2
           ((1, 1) :: repeat (1, 2) (b - 1)) 1); lia. }
  apply (hsteps_trans _ (HB [317; 40; 14; 5] 2203 1 3710
    ((2, 2) :: (4, 2) :: (1, 1) :: repeat (1, 2) (b - 1)) 1)).
  { apply (hGRIND_even 1853 [317; 40; 14; 5] 2203
           ((4, 2) :: (1, 1) :: repeat (1, 2) (b - 1)) 1); lia. }
  apply (hsteps_trans _ (HC [2204; 317; 40; 14; 5] 3710 1 2
    ((2, 2) :: (1, 1) :: repeat (1, 2) (b - 1)) 1)).
  { apply (sTUP2_1 [317; 40; 14; 5] 2203 3709 4
           ((1, 1) :: repeat (1, 2) (b - 1)) 1); lia. }
  apply (hsteps_trans _ (HB [2204; 317; 40; 14; 5] 3710 1 4
    ((2, 2) :: (1, 1) :: repeat (1, 2) (b - 1)) 1)).
  { apply (sTDN [2204; 317; 40; 14; 5] 3710
           ((2, 2) :: (1, 1) :: repeat (1, 2) (b - 1)) 1). }
  apply (hsteps_trans _ (HB [3711; 2204; 317; 40; 14; 5] 5 1 3
    (repeat (1, 2) (b - 1)) 1)).
  { apply (sTRANS2_1 [2204; 317; 40; 14; 5] 3710 3 1
           (repeat (1, 2) (b - 1)) 1); lia. }
  apply (CASCADE_POPFIN [3711; 2204; 317; 40; 14; 5] 5 b); lia.
Qed.

Lemma END46_big : forall k b, 4 <= k -> k <= 3713 -> 2 <= b ->
  hsteps (HB [317; 40; 14; 5] 2204 1 3711
            ((2 * k, 2) :: (1, 1) :: repeat (1, 2) (b - 1)) 1)
         (HB [3711; 2204; 317; 40; 14; 5] (2 * k - 2 + 1 + (b - 1)) 1
            (2 * b + 1) [] 1).
Proof.
  intros k b Hk1 Hk2 Hb.
  apply (hsteps_trans _ (HC [317; 40; 14; 5] 2204 3710 2
    ((2 * k - 2, 2) :: (1, 1) :: repeat (1, 2) (b - 1)) 1)).
  { apply (sTUP [317; 40; 14; 5] 2204 3711 (2 * k) 2
           ((1, 1) :: repeat (1, 2) (b - 1)) 1); lia. }
  apply (hsteps_trans _ (HB [317; 40; 14; 5] 2203 1 3710
    ((2, 2) :: (2 * k - 2, 2) :: (1, 1) :: repeat (1, 2) (b - 1)) 1)).
  { apply (hGRIND_even 1853 [317; 40; 14; 5] 2203
           ((2 * k - 2, 2) :: (1, 1) :: repeat (1, 2) (b - 1)) 1);
      lia. }
  apply (hsteps_trans _ (HC [2204; 317; 40; 14; 5] 3710 1 2
    ((2 * k - 4, 2) :: (1, 1) :: repeat (1, 2) (b - 1)) 1)).
  { replace ((2 * k - 4, 2) :: (1, 1) :: repeat (1, 2) (b - 1))
      with ((2 * k - 2 - 2, 2) :: (1, 1) :: repeat (1, 2) (b - 1))
      by sec_eq.
    apply (sTUP2_1 [317; 40; 14; 5] 2203 3709 (2 * k - 2)
           ((1, 1) :: repeat (1, 2) (b - 1)) 1); lia. }
  apply (hsteps_trans _ (HB [2204; 317; 40; 14; 5] 3710 1 4
    ((2 * k - 4, 2) :: (1, 1) :: repeat (1, 2) (b - 1)) 1)).
  { apply (sTDN [2204; 317; 40; 14; 5] 3710
           ((2 * k - 4, 2) :: (1, 1) :: repeat (1, 2) (b - 1)) 1). }
  apply (hsteps_trans _ (HC [2204; 317; 40; 14; 5] 3710 3 2
    ((2 * k - 6, 2) :: (1, 1) :: repeat (1, 2) (b - 1)) 1)).
  { replace ((2 * k - 6, 2) :: (1, 1) :: repeat (1, 2) (b - 1))
      with ((2 * k - 4 - 2, 2) :: (1, 1) :: repeat (1, 2) (b - 1))
      by sec_eq.
    apply (sTUP [2204; 317; 40; 14; 5] 3710 4 (2 * k - 4) 2
           ((1, 1) :: repeat (1, 2) (b - 1)) 1); lia. }
  apply (hsteps_trans _ (HB [2204; 317; 40; 14; 5] 3710 1
    (2 * (k - 4) + 6)
    ((2, 2) :: (1, 1) :: repeat (1, 2) (b - 1)) 1)).
  { replace ((2 * k - 6, 2) :: (1, 1) :: repeat (1, 2) (b - 1))
      with ((2 * (k - 4) + 2, 2) :: (1, 1) :: repeat (1, 2) (b - 1))
      by sec_eq.
    apply (CLEANG_even (k - 4) [2204; 317; 40; 14; 5] 3710
           ((1, 1) :: repeat (1, 2) (b - 1)) 1); lia. }
  apply (hsteps_trans _ (HB [3711; 2204; 317; 40; 14; 5]
    (S (S (2 * k - 3))) 1 3 (repeat (1, 2) (b - 1)) 1)).
  { replace (2 * (k - 4) + 6) with (2 * k - 2) by lia.
    replace (2 * k - 2) with (S (2 * k - 3)) by lia.
    apply (sTRANS2_1 [2204; 317; 40; 14; 5] 3710 (2 * k - 3) 1
           (repeat (1, 2) (b - 1)) 1); lia. }
  replace (S (S (2 * k - 3))) with (2 * k - 2 + 1) by lia.
  apply (CASCADE_POPFIN [3711; 2204; 317; 40; 14; 5] (2 * k - 2 + 1)
           b); lia.
Qed.

(* ----------------------------------------------------------------- *)
(* The residual core: the END totality for k >= 3714 alone.         *)
(* At the END state the rounds over the pair (2k - 6, 2) exceed     *)
(* the CLEANG_even floor 2k - 6 <= 2 * 3710 and take the DIPDESC    *)
(* boundary; the walk then descends again with k-dependent         *)
(* finals (hsim46.py Part 4).  A lemma parameter -- never an        *)
(* axiom.                                                           *)
(* ----------------------------------------------------------------- *)

Definition TAIL2_END : Prop :=
  forall k beta, 3714 <= k -> 2 <= beta ->
  exists pb A, beta <= A /\
    hsteps (HB [317; 40; 14; 5] 2204 1 3711
              ((2 * k, 2) :: (1, 1) :: repeat (1, 2) (beta - 1)) 1)
           (HB pb A 1 (2 * beta + 1) [] 1).

(* ----------------------------------------------------------------- *)
(* TAIL2_BIG_of: Grind13's TAIL2_BIG, discharged from TAIL2_END.    *)
(* For 1653 <= vM <= 5365 (k <= 3713) the proof is complete; the    *)
(* core is used only at vM >= 5366.                                 *)
(* ----------------------------------------------------------------- *)

Lemma TAIL2_BIG_of : TAIL2_END -> TAIL2_BIG.
Proof.
  intros H. unfold TAIL2_BIG. intros vM beta HvM Hb.
  destruct (le_lt_dec (vM - 1652) 3713) as [Hk | Hk].
  - destruct (vM - 1652) as [|[|[|[|k']]]] eqn:Ek.
    + lia.
    + (* k = 1 *)
      exists [2205; 317; 40; 14; 5], (3712 + (beta - 1)).
      split; [lia |].
      apply (hsteps_trans _ (HC [135; 35; 20; 0] 242 891 2
                               (PXs (vM - 1652) beta) 1)).
      { apply (TAIL2_FRONT vM beta HvM Hb). }
      rewrite Ek.
      apply (hsteps_trans _ (HB [317; 40; 14; 5] 2204 1 3711
        ((2 * 1, 2) :: (1, 1) :: repeat (1, 2) (beta - 1)) 1)).
      { apply (DESCENT46 1 beta). }
      replace (2 * 1) with 2 by lia.
      apply (END46_1 beta Hb).
    + (* k = 2 *)
      exists [3711; 2204; 317; 40; 14; 5], (3 + (beta - 1)).
      split; [lia |].
      apply (hsteps_trans _ (HC [135; 35; 20; 0] 242 891 2
                               (PXs (vM - 1652) beta) 1)).
      { apply (TAIL2_FRONT vM beta HvM Hb). }
      rewrite Ek.
      apply (hsteps_trans _ (HB [317; 40; 14; 5] 2204 1 3711
        ((2 * 2, 2) :: (1, 1) :: repeat (1, 2) (beta - 1)) 1)).
      { apply (DESCENT46 2 beta). }
      replace (2 * 2) with 4 by lia.
      apply (END46_2 beta Hb).
    + (* k = 3 *)
      exists [3711; 2204; 317; 40; 14; 5], (5 + (beta - 1)).
      split; [lia |].
      apply (hsteps_trans _ (HC [135; 35; 20; 0] 242 891 2
                               (PXs (vM - 1652) beta) 1)).
      { apply (TAIL2_FRONT vM beta HvM Hb). }
      rewrite Ek.
      apply (hsteps_trans _ (HB [317; 40; 14; 5] 2204 1 3711
        ((2 * 3, 2) :: (1, 1) :: repeat (1, 2) (beta - 1)) 1)).
      { apply (DESCENT46 3 beta). }
      replace (2 * 3) with 6 by lia.
      apply (END46_3 beta Hb).
    + (* k >= 4, k <= 3713 *)
      exists [3711; 2204; 317; 40; 14; 5],
        (2 * S (S (S (S k'))) - 2 + 1 + (beta - 1)).
      split; [lia |].
      apply (hsteps_trans _ (HC [135; 35; 20; 0] 242 891 2
                               (PXs (vM - 1652) beta) 1)).
      { apply (TAIL2_FRONT vM beta HvM Hb). }
      rewrite Ek.
      apply (hsteps_trans _ (HB [317; 40; 14; 5] 2204 1 3711
        ((2 * S (S (S (S k'))), 2) :: (1, 1)
         :: repeat (1, 2) (beta - 1)) 1)).
      { apply (DESCENT46 (S (S (S (S k')))) beta). }
      apply (END46_big (S (S (S (S k')))) beta); lia.
  - (* k >= 3714: the core *)
    destruct (H (vM - 1652) beta ltac:(lia) Hb)
      as [pb [A [HA Hsteps]]].
    exists pb, A. split; [exact HA |].
    apply (hsteps_trans _ (HC [135; 35; 20; 0] 242 891 2
                             (PXs (vM - 1652) beta) 1)).
    { apply (TAIL2_FRONT vM beta HvM Hb). }
    apply (hsteps_trans _ (HB [317; 40; 14; 5] 2204 1 3711
      ((2 * (vM - 1652), 2) :: (1, 1) :: repeat (1, 2) (beta - 1)) 1)).
    { apply (DESCENT46 (vM - 1652) beta). }
    exact Hsteps.
Qed.

(* ----------------------------------------------------------------- *)
(* ESC_ERA_LAW_46: the phase-8 ESC era law at every even            *)
(* R >= 1278, modulo TAIL2_END alone.                               *)
(* ----------------------------------------------------------------- *)

Lemma ESC_ERA_LAW_46 : TAIL2_END ->
  forall M beta, 616 <= M -> 2 <= beta ->
  exists n c pb a,
    run n (esc_src (2 * M + 52) (beta - 2)) = Some c
    /\ cfg_sim c (rcsec (false :: repeat true (S a) ++ enc pb)
                        (2 * beta + 2) [(1, 2)])
    /\ beta <= a.
Proof.
  intros H M beta HM Hb.
  apply (ESC_ERA_LAW_45 (TAIL2_BIG_of H) M beta HM Hb).
Qed.

(* ----------------------------------------------------------------- *)
(* Assumption audit                                                  *)
(* ----------------------------------------------------------------- *)

Print Assumptions DIPGRIND.
Print Assumptions CLEANG_odd.
Print Assumptions CLEANG_even.
Print Assumptions TAIL2_FRONT.
Print Assumptions DESCENT46.
Print Assumptions END46_1.
Print Assumptions END46_2.
Print Assumptions END46_3.
Print Assumptions END46_big.
Print Assumptions TAIL2_BIG_of.
Print Assumptions ESC_ERA_LAW_46.
