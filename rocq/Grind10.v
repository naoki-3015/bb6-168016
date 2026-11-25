(* ================================================================= *)
(*  Grind10.v -- Phase 42: the totality/landing theorem for the      *)
(*  phase-8 ESC cascade, attacked directly.                          *)
(*                                                                   *)
(*  Phase 41 fenced the phase-8 continuation past stage C's          *)
(*  landing as a full-stack cascade ending "stuck at a B-section     *)
(*  over the empty stack", whose "next recognised sections are       *)
(*  not an era REGEN landing", and concluded that no landing          *)
(*  lemma exists.  Phase 42 re-reads that evidence (hsim42.py):      *)
(*  the cascade's terminal config IS the era-landing shape           *)
(*      HB pb a 1 (2*beta + 1) [] 1,   beta <= a,                    *)
(*  the target of every ESC_TO_REGEN_* lemma since Phase 29 and      *)
(*  the source of Grind2.ERA_TAIL, which closes the era at            *)
(*  machine level for ARBITRARY pb via REGEN_gen.  Phase 41's own     *)
(*  machine trace from the terminal config shows the REGEN_gen       *)
(*  landing HC pb a 1 2 [] (s - 1) at cost 4s + 22 = 74, then TDN     *)
(*  and the era tail -- the modelled era REGEN landing, verbatim.     *)
(*  The word model has no hstep at the terminal only because          *)
(*  hREGEN is stated at pb = [] and hSTGA needs G >= 3; the era       *)
(*  assembly never needed a word step there.  What Phase 41            *)
(*  actually proved is that no continuation lemma over an             *)
(*  ARBITRARY carried rest exists (the cascade reads the whole         *)
(*  stack); the landing over the era-shaped stack family is a         *)
(*  different, and on the evidence true, statement:                    *)
(*                                                                   *)
(*    CASCADE_LANDING (below): for every M >= 616 and beta >= 2,      *)
(*    the stage-D source of Grind9.PHASE8_TO_STAGE_D reaches          *)
(*    HB pb a 1 (2*beta + 1) [] 1 for some pb, a with beta <= a.       *)
(*                                                                   *)
(*  Evidence (rocq/hsim42.py, ALL CHECKS PASS): the shrunk family      *)
(*  S(n1, r1, n2, r2, b) (the hsim41 analogue is S(7, 22, 3, 26, 6))   *)
(*  lands on exactly that shape at ~50 parameter points (one-at-       *)
(*  a-time sweeps of every parameter, both parities of r1, edge        *)
(*  cases n2 = 0/1, r2 = 2, minimal corners), using only proved        *)
(*  hstep constructors; machine-level REGEN from the terminal          *)
(*  confirmed at cost 4s + 22 at three points; real-parameter          *)
(*  directions are beyond primitive walking (nested-grind word         *)
(*  length is exponential) and show CAP -- still walking, never        *)
(*  stuck, never a wrong landing.  One genuine fence the tests        *)
(*  found: for ODD r2 (out of family -- the era residue               *)
(*  2M - 1230 is always even) the walk still lands over the empty      *)
(*  stack with G = 1, but at shuttle s = 2b + r2, not 2b + 1: the      *)
(*  closed form beta' = 2 beta + 4 is an even-residue phenomenon,      *)
(*  and CASCADE_LANDING keeps the era family's parity.                *)
(*                                                                   *)
(*  PROVED HERE (unconditionally): the cascade's last two stages       *)
(*  as general lemmas -- CASCADE_STAGE4 (the rounds stage: a           *)
(*  (2m + 4, 2) pair ground to (2, 2) by TDN + TUP + hGRIND 0 +        *)
(*  GG_rounds, floor m + 1 <= a) and CASCADE_POPFIN (the final         *)
(*  POP chain over the era tail (1, 2)^(beta - 1)); and the            *)
(*  REDUCTION of the whole phase-8 era law to CASCADE_LANDING:         *)
(*  ESC_TO_REGEN_BIG8_of and ESC_ERA_LAW_42 are proved modulo          *)
(*  CASCADE_LANDING (a lemma parameter, like ERA_GEN in               *)
(*  Loop.SETTLED_ITER_GEN -- never an axiom), and Loop.v's             *)
(*  ESC_ITER_BIG8 / _step discharge H_LOOP's ESC instances at          *)
(*  every even R >= 1278 modulo the same parameter.  The              *)
(*  remaining core is exactly CASCADE_LANDING: stages 1-3 of           *)
(*  the cascade (the segment grinds at frames [5], [24; 5],            *)
(*  [25; 24; 5] whose parses are parameter-dependent -- floor           *)
(*  binding inside the segment grinds, as the frame-growth             *)
(*  counts 2..6 across the sweep show).  A proof needs a               *)
(*  totality theorem for the segment grind itself: at each             *)
(*  segment, the grind of a (1, 2)-spine + residue pair at             *)
(*  g0 = 1 over an arbitrary deeper tail, with existential             *)
(*  frame/shuttle values -- the grind analogue of DIPDESC for          *)
(*  the g0 = 1 regime.  That is the precisely-fenced core.             *)
(* ================================================================= *)

Require Import List Bool Arith Lia ZArith.
Import ListNotations.
Require Import TM Sections Mirror TokenPass Recoord Era Esc Dev
               Grind Grind2 Grind3 Grind4 Grind5 Grind6 Grind7 Grind8
               Grind9.

Ltac sec_eq := repeat (first [ solve [reflexivity] | solve [lia]
                             | f_equal ]).

(* ----------------------------------------------------------------- *)
(* Part 1: CASCADE_STAGE4 -- the cascade's rounds stage.             *)
(*                                                                   *)
(* At the hsim41/hsim42 base analogue this is the last grind          *)
(* stage: HC [26; 25; 24; 5] 12 1 2 ((22, 2) :: (1, 1) ::            *)
(* (1, 2)^5) -> HB [26; 25; 24; 5] 12 1 24 ((2, 2) :: (1, 1) ::      *)
(* (1, 2)^5), i.e. m = 9, a = 12, floor m + 1 = 10 <= 12.  The         *)
(* stage is frame- and rest-general: TDN, one TUP, the t = 0          *)
(* clean grind, and GG_rounds (Grind2.v) for the remaining            *)
(* rounds.  The pair (2m + 4, 2) is ground exactly to (2, 2);          *)
(* the shuttle goes 2 -> 2m + 6 = r + 2; the frame counter a is        *)
(* unchanged (rounds are B-level) and is only a floor.                 *)
(* ----------------------------------------------------------------- *)

Lemma CASCADE_STAGE4 : forall m pb a P, m + 1 <= a ->
  hsteps (HC pb a 1 2 ((2*m + 4, 2) :: P) 1)
         (HB pb a 1 (2*m + 6) ((2, 2) :: P) 1).
Proof.
  intros m pb a P Hf.
  (* TDN *)
  apply (hsteps_trans _ (HB pb a 1 4 ((2*m + 4, 2) :: P) 1)).
  { apply (hsteps_step _ (HB pb a 1 4 ((2*m + 4, 2) :: P) 1)).
    { apply hTDN. }
    apply hsteps_refl. }
  (* TUP *)
  apply (hsteps_trans _ (HC pb a 3 2 ((2*m + 2, 2) :: P) 1)).
  { apply (hsteps_step _ (HC pb a 3 2 ((2*m + 2, 2) :: P) 1)).
    { replace (HB pb a 1 4 ((2*m + 4, 2) :: P) 1)
        with (HB pb a 1 (S (S 2))
                ((S (S (S (2*m + 1))), 2) :: P) 1) by sec_eq.
      replace (HC pb a 3 2 ((2*m + 2, 2) :: P) 1)
        with (HC pb a (S 2) 2 ((S (2*m + 1), 2) :: P) 1) by sec_eq.
      apply hTUP. }
    apply hsteps_refl. }
  (* hGRIND 0 *)
  apply (hsteps_trans _ (HB pb a 1 6 ((2*m + 2, 2) :: P) 1)).
  { replace (HC pb a 3 2 ((2*m + 2, 2) :: P) 1)
      with (HC pb a (2*0 + 3) 2 ((2*m + 2, 2) :: P) 1) by sec_eq.
    replace (HB pb a 1 6 ((2*m + 2, 2) :: P) 1)
      with (HB pb a 1 (2*0 + 6) ((2*m + 2, 2) :: P) 1) by sec_eq.
    apply hGRIND; lia. }
  (* GG_rounds m *)
  replace (HB pb a 1 (2*m + 6) ((2, 2) :: P) 1)
    with (HB pb a 1 (2*(0 + m) + 6) ((2, 2) :: P) 1) by sec_eq.
  replace (HB pb a 1 6 ((2*m + 2, 2) :: P) 1)
    with (HB pb a 1 (2*0 + 6) ((2*m + 2, 2) :: P) 1) by sec_eq.
  apply GG_rounds; lia.
Qed.

(* ----------------------------------------------------------------- *)
(* Part 2: CASCADE_POPFIN -- the cascade's final POP chain.          *)
(*                                                                   *)
(* Every completed walk in hsim42 ends with a frame-growth step       *)
(* onto HB F a 1 3 ((1, 2)^(beta - 1)) 1 (the last TRANS2_1 /          *)
(* TUP2_1 landing: shuttle 3 over the era tail), and the walk's        *)
(* remaining steps are the POP chain over that tail, landing on       *)
(* the era shape HB F (a + beta - 1) 1 (2*beta + 1) [] 1.  This        *)
(* is Grind6.pop_chain_h_app at s = 3, stated in era form.             *)
(* ----------------------------------------------------------------- *)

Lemma CASCADE_POPFIN : forall pb a b, 1 <= b ->
  hsteps (HB pb a 1 3 (repeat (1, 2) (b - 1)) 1)
         (HB pb (a + (b - 1)) 1 (2 * b + 1) [] 1).
Proof.
  intros pb a b Hb.
  replace (repeat (1, 2) (b - 1))
    with (repeat (1, 2) (b - 1) ++ [])
    by (rewrite app_nil_r; reflexivity).
  replace (2 * b + 1) with (3 + 2 * (b - 1)) by lia.
  apply pop_chain_h_app; lia.
Qed.

(* ----------------------------------------------------------------- *)
(* Part 3: CASCADE_LANDING -- the remaining core, stated exactly.    *)
(*                                                                   *)
(* The source is Grind9.PHASE8_TO_STAGE_D's target verbatim.         *)
(* The parity of the residue (2 * M - 1230, always even) is load-     *)
(* bearing: for odd residues the landing shuttle is not               *)
(* 2 * beta + 1 (hsim42 Part 2b).                                     *)
(* ----------------------------------------------------------------- *)

Definition CASCADE_LANDING : Prop :=
  forall M beta, 616 <= M -> 2 <= beta ->
  exists pb a, beta <= a /\
    hsteps (HC [5] 13 1 2
      ((1, 2) :: (1, 1) :: (1, 2) :: (1, 2) ::
       repeat (1, 2) 40 ++
       ((149, 2) :: (1, 1) :: (1, 2) :: (1, 2) ::
        repeat (1, 2) 334 ++
        ((2 * M - 1230, 2) :: (1, 1) ::
         repeat (1, 2) (beta - 1)))) 1)
     (HB pb a 1 (2 * beta + 1) [] 1).

(* ----------------------------------------------------------------- *)
(* Part 4: the phase-8 era law, reduced to CASCADE_LANDING.          *)
(* ----------------------------------------------------------------- *)

Lemma ESC_TO_REGEN_BIG8_of : CASCADE_LANDING ->
  forall M beta, 616 <= M -> 2 <= beta ->
  exists pb a,
    hsteps (HC [] 3 1 2
              ((2 * M + 46, 2) :: (1, 1) :: repeat (1, 2) (beta - 1)) 1)
           (HB pb a 1 (2 * beta + 1) [] 1) /\ beta <= a.
Proof.
  intros HCasc M beta HM Hb.
  destruct (HCasc M beta HM Hb) as [pb [a [Ha Hcasc]]].
  exists pb, a. split; [| exact Ha].
  apply (hsteps_trans _ (HB [42; 19] 235 1 335
      ((2 * M - 556, 2) :: (1, 1) :: repeat (1, 2) (beta - 1)) 1)).
  { apply (PHASE7_TO_MID M beta); lia. }
  apply (hsteps_trans _ (HC [5] 13 1 2
      ((1, 2) :: (1, 1) :: (1, 2) :: (1, 2) ::
       repeat (1, 2) 40 ++
       ((149, 2) :: (1, 1) :: (1, 2) :: (1, 2) ::
        repeat (1, 2) 334 ++
        ((2 * M - 1230, 2) :: (1, 1) ::
         repeat (1, 2) (beta - 1)))) 1)).
  { apply (PHASE8_TO_STAGE_D M beta); lia. }
  exact Hcasc.
Qed.

Lemma ESC_ERA_LAW_42 : CASCADE_LANDING ->
  forall M beta, 616 <= M -> 2 <= beta ->
  exists n c pb a,
    run n (esc_src (2 * M + 52) (beta - 2)) = Some c
    /\ cfg_sim c (rcsec (false :: repeat true (S a) ++ enc pb)
                        (2 * beta + 2) [(1, 2)])
    /\ beta <= a.
Proof.
  intros HCasc M beta HM Hb.
  destruct (ESC_TO_REGEN_BIG8_of HCasc M beta HM Hb)
    as [pb [a [Hc Ha]]].
  replace (2 * M + 52) with ((2 * M + 46) + 6) by lia.
  apply (ESC_ERA_LAW_of (2 * M + 46) beta pb a);
    [lia | exact Hc | exact Ha | exact Hb].
Qed.

(* ----------------------------------------------------------------- *)
(* Assumption audit                                                  *)
(* ----------------------------------------------------------------- *)

Print Assumptions CASCADE_STAGE4.
Print Assumptions CASCADE_POPFIN.
Print Assumptions ESC_TO_REGEN_BIG8_of.
Print Assumptions ESC_ERA_LAW_42.
