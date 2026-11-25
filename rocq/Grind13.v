(* ================================================================= *)
(*  Phase 45: the stage-4 TAIL at the era slice; the ESC side of     *)
(*  H_LOOP reduced to the single residue core TAIL2_BIG.             *)
(*                                                                   *)
(*  Phase 44 reduced CASCADE_STAGE4_BIG to CASCADE_STAGE4_TAIL       *)
(*  (Grind12.v): the tail traversal at the bottom frame, over all    *)
(*  q >= 5, v3, vM, a, b.  Its only use in the whole development     *)
(*  is Grind12.CASCADE_STAGE4_BIG_of, which instantiates the tail    *)
(*  at the ERA SLICE (q, v3, a) = (28, 34, 822) -- S4s_era.  Phase   *)
(*  45 characterises the tail at that slice (rocq/hsim45.py, ALL     *)
(*  PHASE 45 CHECKS PASS) and finds a three-layer parse:             *)
(*                                                                   *)
(*    layer 0 (q = 28): pop12 4, TUP, PUSH, GG_boundary (3, 3),      *)
(*      PUSHX, pop12 3, TUP2_1, GG_boundary (13, 20), PX2Bgen,       *)
(*      pops, TUP, hGRIND_even 15, TUP2_1, GG_clean 4, TRANS2_1      *)
(*      -- TAIL_LAYER0 below, at HB [35; 20; 0] 15 1 3 (TAIL1s).     *)
(*      The parse touches only the (48, 2) residue and its (1, 1)    *)
(*      separator; (v3, vM, a, b) are carried symbolically.          *)
(*    layer 1 (v3 = 34): pop12 120, TUP, hGRIND_even 119, TUP2_1,    *)
(*      GG_clean 31, TRANS2_1 -- TAIL_LAYER1 below, landing at       *)
(*      HB [243; 135; 35; 20; 0] 69 1 3 (TAIL2s).                    *)
(*    layer 2 (a = 822): pop12 824 reaches the residue state         *)
(*        HB [243; 135; 35; 20; 0] 893 1 1651                        *)
(*          ((2 * vM + 2, 2) :: (1, 1) :: (1, 2)^(b - 1)).           *)
(*      For vM <= 1652 the residue closes CLEANLY -- TAIL2_CLEAN:    *)
(*      TUP, hGRIND_even 823, then TRANS2_1 (vM = 0), TRANS2_2       *)
(*      (vM = 1), TDN + TRANS2_1 (vM = 2), or TUP2_1 + GG_clean      *)
(*      (vM - 3) + TRANS2_1 (3 <= vM <= 1652), then the POP chain;   *)
(*      final counters b + 1651 / b + 2 / b + 4 / 2 * vM + b, all    *)
(*      >= b (asserted verbatim in hsim45 Part 2).                   *)
(*      For vM >= 1653 the pair (2 * vM - 2, 2) at counter 1650 is   *)
(*      in the BOUNDARY regime: GG_boundary (1650, vM - 3) lands     *)
(*      at HC [893; 243; 135; 35; 20; 0] 0 3 2 (spine 1650 ++        *)
(*      ((2 * vM - 3304, 2) :: (1, 1) :: spine (b - 1))) and PX2A    *)
(*      pops to [135; 35; 20; 0] with g0 = 891 -- a frame-dependent  *)
(*      dip descent.  The macro walk of hsim45 Part 3 COMPLETES      *)
(*      there (vM = 1653 / 2000 / 5366, finals asserted verbatim),   *)
(*      but its length grows with vM (4473 / 5165 / 14529 macro      *)
(*      steps) and the descent's sub-parses depend on the frame      *)
(*      blocks (the Phase 38 wall): no uniform cycle exists in       *)
(*      the current lemma vocabulary.  That residue totality is      *)
(*      the residual core TAIL2_BIG below -- ONE pair at ONE fixed   *)
(*      state, for vM >= 1653 only.                                  *)
(*                                                                   *)
(*  Net effect: CASCADE_STAGE4_BIG, the phase-8 era law             *)
(*  (ESC_ERA_LAW_45) and Loop's ESC iteration at every even          *)
(*  R >= 1278 now rest on TAIL2_BIG alone.  Grind12's universal      *)
(*  CASCADE_STAGE4_TAIL remains unproved; it is strictly stronger    *)
(*  than the proof needs (arbitrary q, v3, a and the bottom          *)
(*  frame), and the era slice is the only instantiation ever used.   *)
(* ================================================================= *)

Require Import List Bool Arith Lia ZArith.
Import ListNotations.
Require Import TM Sections Mirror TokenPass Recoord Era Esc Dev
               Grind Grind2 Grind3 Grind4 Grind5 Grind6 Grind7 Grind8
               Grind9 Grind10 Grind11 Grind12.

Ltac sec_eq := repeat (first [ solve [reflexivity] | solve [lia]
                             | f_equal ]).

(* ----------------------------------------------------------------- *)
(* The tail stacks after layers 0 and 1 at the era slice.            *)
(* TAIL1s: the stack under the (48, 2) residue's (1, 1) separator    *)
(* once layer 0's TRANS2_1 has consumed both -- (1, 2)^(2 + 118)     *)
(* over the layer-1 residue (2 * v3 + 2, 2).  TAIL2s: the stack at   *)
(* the layer-2 entry -- (1, 2)^824 over the layer-2 residue.         *)
(* ----------------------------------------------------------------- *)

Definition TAIL1s (v3 vM a b : nat) : list (nat * nat) :=
  (1, 2) :: (1, 2) :: repeat (1, 2) 118 ++
  ((2 * v3 + 2, 2) ::
   (1, 1) :: (1, 2) :: (1, 2) :: repeat (1, 2) a ++
   ((2 * vM + 2, 2) :: (1, 1) :: repeat (1, 2) (b - 1))).

Definition TAIL2s (vM b : nat) : list (nat * nat) :=
  repeat (1, 2) 824 ++
  ((2 * vM + 2, 2) :: (1, 1) :: repeat (1, 2) (b - 1)).

(* ----------------------------------------------------------------- *)
(* Layer 0 (q = 28): the parse of hsim45 Part 2, steps 1-17.         *)
(* Only the (48, 2) residue and the head (1, 1) of the carried       *)
(* stack are touched; v3, vM, a, b are symbolic throughout.          *)
(* ----------------------------------------------------------------- *)

Lemma TAIL_LAYER0 : forall v3 vM a b,
  hsteps (HB [] 0 1 5 (TAILs 28 v3 vM a b) 1)
         (HB [35; 20; 0] 15 1 3 (TAIL1s v3 vM a b) 1).
Proof.
  intros v3 vM a b.
  replace (TAILs 28 v3 vM a b)
    with (repeat (1, 2) 4 ++
          ((48, 2) :: (1, 1) :: TAIL1s v3 vM a b))
    by (unfold TAILs, TAIL1s; reflexivity).
  (* pop12 4 *)
  apply (hsteps_trans _ (HB [] 4 1 13
    ((48, 2) :: (1, 1) :: TAIL1s v3 vM a b) 1)).
  { apply (pop12 4 [] 0 5
             ((48, 2) :: (1, 1) :: TAIL1s v3 vM a b) 1); lia. }
  (* TUP *)
  apply (hsteps_trans _ (HC [] 4 12 2
    ((46, 2) :: (1, 1) :: TAIL1s v3 vM a b) 1)).
  { apply (hsteps_step _ (HC [] 4 12 2
      ((46, 2) :: (1, 1) :: TAIL1s v3 vM a b) 1)).
    { apply hTUP. }
    apply hsteps_refl. }
  (* PUSH *)
  apply (hsteps_trans _ (HC [] 3 1 2
    ((10, 2) :: (46, 2) :: (1, 1) :: TAIL1s v3 vM a b) 1)).
  { apply (hsteps_step _ (HC [] 3 1 2
      ((10, 2) :: (46, 2) :: (1, 1) :: TAIL1s v3 vM a b) 1)).
    { apply hPUSH. }
    apply hsteps_refl. }
  (* GG_boundary 3 3 *)
  apply (hsteps_trans _ (HC [] 0 3 2
    (repeat (1, 2) 3 ++
     ((2, 2) :: (46, 2) :: (1, 1) :: TAIL1s v3 vM a b)) 1)).
  { apply (GG_boundary 3 3 []
             ((46, 2) :: (1, 1) :: TAIL1s v3 vM a b) 1); lia. }
  (* PUSHX *)
  apply (hsteps_trans _ (HB [] 1 1 7
    (repeat (1, 2) 3 ++
     ((2, 2) :: (46, 2) :: (1, 1) :: TAIL1s v3 vM a b)) 1)).
  { apply (hsteps_step _ (HB [] 1 1 7
      (repeat (1, 2) 3 ++
       ((2, 2) :: (46, 2) :: (1, 1) :: TAIL1s v3 vM a b)) 1)).
    { apply hPUSHX. }
    apply hsteps_refl. }
  (* pop12 3 *)
  apply (hsteps_trans _ (HB [] 4 1 13
    ((2, 2) :: (46, 2) :: (1, 1) :: TAIL1s v3 vM a b) 1)).
  { apply (pop12 3 [] 1 7
             ((2, 2) :: (46, 2) :: (1, 1) :: TAIL1s v3 vM a b) 1);
      lia. }
  (* TUP2_1 *)
  apply (hsteps_trans _ (HC [5] 13 1 2
    ((44, 2) :: (1, 1) :: TAIL1s v3 vM a b) 1)).
  { apply (hsteps_step _ (HC [5] 13 1 2
      ((44, 2) :: (1, 1) :: TAIL1s v3 vM a b) 1)).
    { apply hTUP2_1. }
    apply hsteps_refl. }
  (* GG_boundary 13 20 *)
  apply (hsteps_trans _ (HC [5] 0 3 2
    (repeat (1, 2) 13 ++
     ((16, 2) :: (1, 1) :: TAIL1s v3 vM a b)) 1)).
  { apply (GG_boundary 13 20 [5]
             ((1, 1) :: TAIL1s v3 vM a b) 1); lia. }
  (* PX2Bgen *)
  apply (hsteps_trans _ (HB [0] 3 1 2
    ((1, 2) :: (1, 1) :: (1, 2) :: (1, 2) ::
     repeat (1, 2) 13 ++
     ((16, 2) :: (1, 1) :: TAIL1s v3 vM a b)) 1)).
  { apply (hsteps_step _ (HB [0] 3 1 2
      ((1, 2) :: (1, 1) :: (1, 2) :: (1, 2) ::
       repeat (1, 2) 13 ++
       ((16, 2) :: (1, 1) :: TAIL1s v3 vM a b)) 1)).
    { apply hPX2Bgen. }
    apply hsteps_refl. }
  (* pop12 1 *)
  apply (hsteps_trans _ (HB [0] 4 1 4
    ((1, 1) :: (1, 2) :: (1, 2) ::
     repeat (1, 2) 13 ++
     ((16, 2) :: (1, 1) :: TAIL1s v3 vM a b)) 1)).
  { apply (pop12 1 [0] 3 2
             ((1, 1) :: (1, 2) :: (1, 2) ::
              repeat (1, 2) 13 ++
              ((16, 2) :: (1, 1) :: TAIL1s v3 vM a b)) 1); lia. }
  (* POP (1, 1) *)
  apply (hsteps_trans _ (HB [0] 5 1 5
    ((1, 2) :: (1, 2) ::
     repeat (1, 2) 13 ++
     ((16, 2) :: (1, 1) :: TAIL1s v3 vM a b)) 1)).
  { apply (hsteps_step _ (HB [0] 5 1 5
      ((1, 2) :: (1, 2) ::
       repeat (1, 2) 13 ++
       ((16, 2) :: (1, 1) :: TAIL1s v3 vM a b)) 1)).
    { apply (hPOP [0] 4 4 1
        ((1, 2) :: (1, 2) ::
         repeat (1, 2) 13 ++
         ((16, 2) :: (1, 1) :: TAIL1s v3 vM a b)) 1); lia. }
    apply hsteps_refl. }
  (* pop12 15 *)
  apply (hsteps_trans _ (HB [0] 20 1 35
    ((16, 2) :: (1, 1) :: TAIL1s v3 vM a b) 1)).
  { apply (pop12 15 [0] 5 5
             ((16, 2) :: (1, 1) :: TAIL1s v3 vM a b) 1); lia. }
  (* TUP *)
  apply (hsteps_trans _ (HC [0] 20 34 2
    ((14, 2) :: (1, 1) :: TAIL1s v3 vM a b) 1)).
  { apply (hsteps_step _ (HC [0] 20 34 2
      ((14, 2) :: (1, 1) :: TAIL1s v3 vM a b) 1)).
    { apply hTUP. }
    apply hsteps_refl. }
  (* hGRIND_even 15 *)
  apply (hsteps_trans _ (HB [0] 19 1 34
    ((2, 2) :: (14, 2) :: (1, 1) :: TAIL1s v3 vM a b) 1)).
  { apply (hGRIND_even 15 [0] 19
             ((14, 2) :: (1, 1) :: TAIL1s v3 vM a b) 1); lia. }
  (* TUP2_1 *)
  apply (hsteps_trans _ (HC [20; 0] 34 1 2
    ((12, 2) :: (1, 1) :: TAIL1s v3 vM a b) 1)).
  { apply (hsteps_step _ (HC [20; 0] 34 1 2
      ((12, 2) :: (1, 1) :: TAIL1s v3 vM a b) 1)).
    { apply hTUP2_1. }
    apply hsteps_refl. }
  (* GG_clean 4 *)
  apply (hsteps_trans _ (HB [20; 0] 34 1 14
    ((2, 2) :: (1, 1) :: TAIL1s v3 vM a b) 1)).
  { apply (GG_clean 4 [20; 0] 34
             ((1, 1) :: TAIL1s v3 vM a b) 1); lia. }
  (* TRANS2_1 *)
  apply (hsteps_step _ (HB [35; 20; 0] 15 1 3
    (TAIL1s v3 vM a b) 1)).
  { apply (hTRANS2_1 [20; 0] 34 13 1 1
             (TAIL1s v3 vM a b) 1); lia. }
  apply hsteps_refl.
Qed.

(* ----------------------------------------------------------------- *)
(* Layer 1 (v3 = 34, a = 822): pop12 120, TUP, hGRIND_even 119,      *)
(* TUP2_1, GG_clean 31, TRANS2_1.  vM and b are symbolic; the        *)
(* layer-2 stack is carried as TAIL2s.                               *)
(* ----------------------------------------------------------------- *)

Lemma TAIL_LAYER1 : forall vM b,
  hsteps (HB [35; 20; 0] 15 1 3 (TAIL1s 34 vM 822 b) 1)
         (HB [243; 135; 35; 20; 0] 69 1 3 (TAIL2s vM b) 1).
Proof.
  intros vM b.
  replace (TAIL1s 34 vM 822 b)
    with (repeat (1, 2) 120 ++
          ((70, 2) :: (1, 1) :: TAIL2s vM b))
    by (unfold TAIL1s, TAIL2s; reflexivity).
  (* pop12 120 *)
  apply (hsteps_trans _ (HB [35; 20; 0] 135 1 243
    ((70, 2) :: (1, 1) :: TAIL2s vM b) 1)).
  { apply (pop12 120 [35; 20; 0] 15 3
             ((70, 2) :: (1, 1) :: TAIL2s vM b) 1); lia. }
  (* TUP *)
  apply (hsteps_trans _ (HC [35; 20; 0] 135 242 2
    ((68, 2) :: (1, 1) :: TAIL2s vM b) 1)).
  { apply (hsteps_step _ (HC [35; 20; 0] 135 242 2
      ((68, 2) :: (1, 1) :: TAIL2s vM b) 1)).
    { apply hTUP. }
    apply hsteps_refl. }
  (* hGRIND_even 119 *)
  apply (hsteps_trans _ (HB [35; 20; 0] 134 1 242
    ((2, 2) :: (68, 2) :: (1, 1) :: TAIL2s vM b) 1)).
  { apply (hGRIND_even 119 [35; 20; 0] 134
             ((68, 2) :: (1, 1) :: TAIL2s vM b) 1); lia. }
  (* TUP2_1 *)
  apply (hsteps_trans _ (HC [135; 35; 20; 0] 242 1 2
    ((66, 2) :: (1, 1) :: TAIL2s vM b) 1)).
  { apply (hsteps_step _ (HC [135; 35; 20; 0] 242 1 2
      ((66, 2) :: (1, 1) :: TAIL2s vM b) 1)).
    { apply hTUP2_1. }
    apply hsteps_refl. }
  (* GG_clean 31 *)
  apply (hsteps_trans _ (HB [135; 35; 20; 0] 242 1 68
    ((2, 2) :: (1, 1) :: TAIL2s vM b) 1)).
  { apply (GG_clean 31 [135; 35; 20; 0] 242
             ((1, 1) :: TAIL2s vM b) 1); lia. }
  (* TRANS2_1 *)
  apply (hsteps_step _ (HB [243; 135; 35; 20; 0] 69 1 3
    (TAIL2s vM b) 1)).
  { apply (hTRANS2_1 [135; 35; 20; 0] 242 67 1 1
             (TAIL2s vM b) 1); lia. }
  apply hsteps_refl.
Qed.

(* ----------------------------------------------------------------- *)
(* The residual core: the layer-2 residue totality in the boundary   *)
(* regime.  ONE pair (2 * vM + 2, 2) at ONE fixed state -- the       *)
(* residue state reached by layers 0-1 and pop12 824 -- for          *)
(* vM >= 1653 only (the clean range vM <= 1652 is TAIL2_CLEAN).      *)
(* hsim45 Part 3: the macro walk completes at the era landing for    *)
(* vM = 1653 / 2000 / 5366, but with vM-growing length and           *)
(* frame-dependent dip descents; no uniform cycle is available in    *)
(* the current lemma vocabulary (cf. the Phase 38 verdict).          *)
(* ----------------------------------------------------------------- *)

Definition TAIL2_BIG : Prop :=
  forall vM beta, 1653 <= vM -> 2 <= beta ->
  exists pb A, beta <= A /\
    hsteps (HB [243; 135; 35; 20; 0] 893 1 1651
              ((2 * vM + 2, 2) :: (1, 1) ::
               repeat (1, 2) (beta - 1)) 1)
           (HB pb A 1 (2 * beta + 1) [] 1).

(* ----------------------------------------------------------------- *)
(* Layer 2, clean range: the residue at counter 1650 grinds clean    *)
(* (GG_clean floor vM - 2 <= 1650).  Four dispatches on vM.          *)
(* ----------------------------------------------------------------- *)

Lemma TAIL2_CLEAN : forall vM beta, vM <= 1652 -> 2 <= beta ->
  exists pb A, beta <= A /\
    hsteps (HB [243; 135; 35; 20; 0] 893 1 1651
              ((2 * vM + 2, 2) :: (1, 1) ::
               repeat (1, 2) (beta - 1)) 1)
           (HB pb A 1 (2 * beta + 1) [] 1).
Proof.
  intros vM beta Hv Hb. destruct vM as [|[|[|vM']]].
  - (* vM = 0: the residue is (2, 2); TRANS2_1, then the POP chain *)
    exists [894; 243; 135; 35; 20; 0], (1652 + (beta - 1)).
    split; [lia|].
    apply (hsteps_trans _ (HB [894; 243; 135; 35; 20; 0] 1652 1 3
      (repeat (1, 2) (beta - 1)) 1)).
    { apply (hsteps_step _ (HB [894; 243; 135; 35; 20; 0] 1652 1 3
        (repeat (1, 2) (beta - 1)) 1)).
      { apply (hTRANS2_1 [243; 135; 35; 20; 0] 893 1650 1 1
                 (repeat (1, 2) (beta - 1)) 1); lia. }
      apply hsteps_refl. }
    apply (CASCADE_POPFIN [894; 243; 135; 35; 20; 0] 1652 beta);
      lia.
  - (* vM = 1: TUP, hGRIND_even 823, TRANS2_2, POP chain *)
    exists [1651; 893; 243; 135; 35; 20; 0], (3 + (beta - 1)).
    split; [lia|].
    apply (hsteps_trans _ (HC [243; 135; 35; 20; 0] 893 1650 2
      ((2, 2) :: (1, 1) :: repeat (1, 2) (beta - 1)) 1)).
    { apply (hsteps_step _ (HC [243; 135; 35; 20; 0] 893 1650 2
        ((2, 2) :: (1, 1) :: repeat (1, 2) (beta - 1)) 1)).
      { apply hTUP. }
      apply hsteps_refl. }
    apply (hsteps_trans _ (HB [243; 135; 35; 20; 0] 892 1 1650
      ((2, 2) :: (2, 2) :: (1, 1) :: repeat (1, 2) (beta - 1)) 1)).
    { apply (hGRIND_even 823 [243; 135; 35; 20; 0] 892
               ((2, 2) :: (1, 1) :: repeat (1, 2) (beta - 1)) 1);
        lia. }
    apply (hsteps_trans _ (HB [1651; 893; 243; 135; 35; 20; 0]
      3 1 3 (repeat (1, 2) (beta - 1)) 1)).
    { apply (hsteps_step _ (HB [1651; 893; 243; 135; 35; 20; 0]
        3 1 3 (repeat (1, 2) (beta - 1)) 1)).
      { apply (hTRANS2_2 [243; 135; 35; 20; 0] 892 1649 1 1 1
                 (repeat (1, 2) (beta - 1)) 1); lia. }
      apply hsteps_refl. }
    apply (CASCADE_POPFIN [1651; 893; 243; 135; 35; 20; 0] 3 beta);
      lia.
  - (* vM = 2: TUP, hGRIND_even 823, TUP2_1, TDN, TRANS2_1, POPs *)
    exists [1651; 893; 243; 135; 35; 20; 0], (5 + (beta - 1)).
    split; [lia|].
    apply (hsteps_trans _ (HC [243; 135; 35; 20; 0] 893 1650 2
      ((4, 2) :: (1, 1) :: repeat (1, 2) (beta - 1)) 1)).
    { apply (hsteps_step _ (HC [243; 135; 35; 20; 0] 893 1650 2
        ((4, 2) :: (1, 1) :: repeat (1, 2) (beta - 1)) 1)).
      { apply hTUP. }
      apply hsteps_refl. }
    apply (hsteps_trans _ (HB [243; 135; 35; 20; 0] 892 1 1650
      ((2, 2) :: (4, 2) :: (1, 1) :: repeat (1, 2) (beta - 1)) 1)).
    { apply (hGRIND_even 823 [243; 135; 35; 20; 0] 892
               ((4, 2) :: (1, 1) :: repeat (1, 2) (beta - 1)) 1);
        lia. }
    apply (hsteps_trans _ (HC [893; 243; 135; 35; 20; 0] 1650 1 2
      ((2, 2) :: (1, 1) :: repeat (1, 2) (beta - 1)) 1)).
    { apply (hsteps_step _ (HC [893; 243; 135; 35; 20; 0] 1650 1 2
        ((2, 2) :: (1, 1) :: repeat (1, 2) (beta - 1)) 1)).
      { apply hTUP2_1. }
      apply hsteps_refl. }
    apply (hsteps_trans _ (HB [893; 243; 135; 35; 20; 0] 1650 1 4
      ((2, 2) :: (1, 1) :: repeat (1, 2) (beta - 1)) 1)).
    { apply (hsteps_step _ (HB [893; 243; 135; 35; 20; 0] 1650 1 4
        ((2, 2) :: (1, 1) :: repeat (1, 2) (beta - 1)) 1)).
      { apply hTDN. }
      apply hsteps_refl. }
    apply (hsteps_trans _ (HB [1651; 893; 243; 135; 35; 20; 0]
      5 1 3 (repeat (1, 2) (beta - 1)) 1)).
    { apply (hsteps_step _ (HB [1651; 893; 243; 135; 35; 20; 0]
        5 1 3 (repeat (1, 2) (beta - 1)) 1)).
      { apply (hTRANS2_1 [893; 243; 135; 35; 20; 0] 1650 3 1 1
                 (repeat (1, 2) (beta - 1)) 1); lia. }
      apply hsteps_refl. }
    apply (CASCADE_POPFIN [1651; 893; 243; 135; 35; 20; 0] 5 beta);
      lia.
  - (* vM = vM' + 3 <= 1652: TUP, hGRIND_even 823, TUP2_1,         *)
    (* GG_clean vM', TRANS2_1, POP chain                            *)
    replace (2 * S (S (S vM')) + 2) with (2 * vM' + 8) by lia.
    exists [1651; 893; 243; 135; 35; 20; 0],
      ((2 * vM' + 7) + (beta - 1)).
    split; [lia|].
    apply (hsteps_trans _ (HC [243; 135; 35; 20; 0] 893 1650 2
      ((2 * vM' + 6, 2) :: (1, 1) :: repeat (1, 2) (beta - 1)) 1)).
    { apply (hsteps_step _ (HC [243; 135; 35; 20; 0] 893 1650 2
        ((2 * vM' + 6, 2) :: (1, 1) :: repeat (1, 2) (beta - 1)) 1)).
      { replace (HB [243; 135; 35; 20; 0] 893 1 1651
          ((2 * vM' + 8, 2) :: (1, 1) ::
           repeat (1, 2) (beta - 1)) 1)
          with (HB [243; 135; 35; 20; 0] 893 1 (S (S 1649))
            ((S (S (S (2 * vM' + 5))), 2) :: (1, 1) ::
             repeat (1, 2) (beta - 1)) 1) by sec_eq.
        replace (HC [243; 135; 35; 20; 0] 893 1650 2
          ((2 * vM' + 6, 2) :: (1, 1) ::
           repeat (1, 2) (beta - 1)) 1)
          with (HC [243; 135; 35; 20; 0] 893 (S 1649) 2
            ((S (2 * vM' + 5), 2) :: (1, 1) ::
             repeat (1, 2) (beta - 1)) 1) by sec_eq.
        apply hTUP. }
      apply hsteps_refl. }
    apply (hsteps_trans _ (HB [243; 135; 35; 20; 0] 892 1 1650
      ((2, 2) :: (2 * vM' + 6, 2) :: (1, 1) ::
       repeat (1, 2) (beta - 1)) 1)).
    { apply (hGRIND_even 823 [243; 135; 35; 20; 0] 892
               ((2 * vM' + 6, 2) :: (1, 1) ::
                repeat (1, 2) (beta - 1)) 1); lia. }
    apply (hsteps_trans _ (HC [893; 243; 135; 35; 20; 0] 1650 1 2
      ((2 * vM' + 4, 2) :: (1, 1) :: repeat (1, 2) (beta - 1)) 1)).
    { apply (hsteps_step _ (HC [893; 243; 135; 35; 20; 0] 1650 1 2
        ((2 * vM' + 4, 2) :: (1, 1) ::
         repeat (1, 2) (beta - 1)) 1)).
      { replace (HB [243; 135; 35; 20; 0] 892 1 1650
          ((2, 2) :: (2 * vM' + 6, 2) :: (1, 1) ::
           repeat (1, 2) (beta - 1)) 1)
          with (HB [243; 135; 35; 20; 0] 892 1 (S 1649)
            ((2, S (S 0)) ::
             (S (S (S (2 * vM' + 3))), 2) :: (1, 1) ::
             repeat (1, 2) (beta - 1)) 1) by sec_eq.
        replace (HC [893; 243; 135; 35; 20; 0] 1650 1 2
          ((2 * vM' + 4, 2) :: (1, 1) ::
           repeat (1, 2) (beta - 1)) 1)
          with (HC (S 892 :: [243; 135; 35; 20; 0]) (S 1649) (S 0) 2
            ((S (2 * vM' + 3), 2) :: (1, 1) ::
             repeat (1, 2) (beta - 1)) 1) by sec_eq.
        apply hTUP2_1. }
      apply hsteps_refl. }
    apply (hsteps_trans _ (HB [893; 243; 135; 35; 20; 0] 1650 1
      (2 * vM' + 6)
      ((2, 2) :: (1, 1) :: repeat (1, 2) (beta - 1)) 1)).
    { apply (GG_clean vM' [893; 243; 135; 35; 20; 0] 1650
               ((1, 1) :: repeat (1, 2) (beta - 1)) 1); lia. }
    apply (hsteps_trans _ (HB [1651; 893; 243; 135; 35; 20; 0]
      (2 * vM' + 7) 1 3 (repeat (1, 2) (beta - 1)) 1)).
    { apply (hsteps_step _ (HB [1651; 893; 243; 135; 35; 20; 0]
        (2 * vM' + 7) 1 3 (repeat (1, 2) (beta - 1)) 1)).
      { replace (HB [893; 243; 135; 35; 20; 0] 1650 1
          (2 * vM' + 6)
          ((2, 2) :: (1, 1) :: repeat (1, 2) (beta - 1)) 1)
          with (HB [893; 243; 135; 35; 20; 0] 1650 1
            (S (2 * vM' + 5))
            ((2, S 1) :: (1, 1) ::
             repeat (1, 2) (beta - 1)) 1) by sec_eq.
        replace (HB [1651; 893; 243; 135; 35; 20; 0]
          (2 * vM' + 7) 1 3 (repeat (1, 2) (beta - 1)) 1)
          with (HB (S 1650 :: [893; 243; 135; 35; 20; 0])
            (S (S (2 * vM' + 5))) 1 (S 1 + 1)
            (repeat (1, 2) (beta - 1)) 1) by sec_eq.
        apply (hTRANS2_1 [893; 243; 135; 35; 20; 0] 1650
                 (2 * vM' + 5) 1 1 (repeat (1, 2) (beta - 1)) 1);
          lia. }
      apply hsteps_refl. }
    apply (CASCADE_POPFIN [1651; 893; 243; 135; 35; 20; 0]
             (2 * vM' + 7) beta); lia.
Qed.

(* ----------------------------------------------------------------- *)
(* The residue state, all vM: clean range proved, boundary range   *)
(* is the core TAIL2_BIG.                                            *)
(* ----------------------------------------------------------------- *)

Lemma TAIL2_ALL : TAIL2_BIG -> forall vM beta, 2 <= beta ->
  exists pb A, beta <= A /\
    hsteps (HB [243; 135; 35; 20; 0] 893 1 1651
              ((2 * vM + 2, 2) :: (1, 1) ::
               repeat (1, 2) (beta - 1)) 1)
           (HB pb A 1 (2 * beta + 1) [] 1).
Proof.
  intros H vM beta Hb. destruct (le_lt_dec vM 1652) as [Hle|Hlt].
  - apply (TAIL2_CLEAN vM beta Hle Hb).
  - unfold TAIL2_BIG in H. apply (H vM beta); lia.
Qed.

(* ----------------------------------------------------------------- *)
(* The era tail: layers 0 and 1, pop12 824, the residue state.       *)
(* This is the (28, 34, M - 1441, 822, beta) instance of             *)
(* Grind12.CASCADE_STAGE4_TAIL that CASCADE_STAGE4_BIG_of uses,      *)
(* proved modulo TAIL2_BIG.                                          *)
(* ----------------------------------------------------------------- *)

Lemma TAIL_ERA_of : TAIL2_BIG -> forall vM beta, 2 <= beta ->
  exists pb A, beta <= A /\
    hsteps (HB [] 0 1 5 (TAILs 28 34 vM 822 beta) 1)
           (HB pb A 1 (2 * beta + 1) [] 1).
Proof.
  intros H vM beta Hb.
  destruct (TAIL2_ALL H vM beta Hb) as [pb [A [HA H2]]].
  exists pb, A. split; [exact HA|].
  apply (hsteps_trans _ (HB [35; 20; 0] 15 1 3
    (TAIL1s 34 vM 822 beta) 1)).
  { apply TAIL_LAYER0. }
  apply (hsteps_trans _ (HB [243; 135; 35; 20; 0] 69 1 3
    (TAIL2s vM beta) 1)).
  { apply TAIL_LAYER1. }
  apply (hsteps_trans _ (HB [243; 135; 35; 20; 0] 893 1 1651
    ((2 * vM + 2, 2) :: (1, 1) :: repeat (1, 2) (beta - 1)) 1)).
  { apply (pop12 824 [243; 135; 35; 20; 0] 69 3
             ((2 * vM + 2, 2) :: (1, 1) ::
              repeat (1, 2) (beta - 1)) 1); lia. }
  exact H2.
Qed.

(* ----------------------------------------------------------------- *)
(* CASCADE_STAGE4_BIG modulo TAIL2_BIG: Grind12's composition       *)
(* (SEG1, SEG2, T1, T2, T3, T4) with the tail instance supplied     *)
(* by TAIL_ERA_of instead of CASCADE_STAGE4_TAIL.                    *)
(* ----------------------------------------------------------------- *)

Lemma CASCADE_STAGE4_BIG_45 : TAIL2_BIG -> CASCADE_STAGE4_BIG.
Proof.
  intros H. unfold CASCADE_STAGE4_BIG. intros M beta HM Hb.
  destruct (TAIL_ERA_of H (M - 1441) beta Hb)
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
(* The phase-8 era law, reduced to TAIL2_BIG.                        *)
(* ----------------------------------------------------------------- *)

Lemma ESC_ERA_LAW_45 : TAIL2_BIG ->
  forall M beta, 616 <= M -> 2 <= beta ->
  exists n c pb a,
    run n (esc_src (2 * M + 52) (beta - 2)) = Some c
    /\ cfg_sim c (rcsec (false :: repeat true (S a) ++ enc pb)
                        (2 * beta + 2) [(1, 2)])
    /\ beta <= a.
Proof.
  intros H M beta HM Hb.
  apply (ESC_ERA_LAW_43 (CASCADE_STAGE4_BIG_45 H) M beta HM Hb).
Qed.

(* ----------------------------------------------------------------- *)
(* Assumption audit                                                  *)
(* ----------------------------------------------------------------- *)

Print Assumptions TAIL_LAYER0.
Print Assumptions TAIL_LAYER1.
Print Assumptions TAIL2_CLEAN.
Print Assumptions TAIL2_ALL.
Print Assumptions TAIL_ERA_of.
Print Assumptions CASCADE_STAGE4_BIG_45.
Print Assumptions ESC_ERA_LAW_45.
