(* ================================================================= *)
(*  Grind5.v -- Phase 36: the third re-basing (ESC grind at         *)
(*  R >= 116): the dip-bottom step lists PX2A0 / PX2B0 (Dev.v,      *)
(*  Grind.v constructors hPX2A0 / hPX2B0) and the deviated grind    *)
(*  at pb = [0].                                                    *)
(*                                                                  *)
(*  The Phase 33 fence was the dip bottom HC [20; 0] 0 3 2 of the   *)
(*  phase-3 boundary grind (grind 34 at frame 34, R = 116): no      *)
(*  hstep constructor applied there.  hPX2A0 now fires at that      *)
(*  exact shape (PX2A0_dip34 below), landing on                     *)
(*  HB [0] 3 1 2 ((16, 2) :: (1, 1) :: (1, 2) :: (1, 2) :: rest).   *)
(*  The grind's unwind then runs the (16, 2) grind at (pb = [0],    *)
(*  a2 = 3), whose own boundary round (grind 3 at frame 3) dips     *)
(*  to HC [0] 0 3 2 -- the hPX2B0 shape -- and lands in the         *)
(*  pb = [] regime of hGRIND_dev.  hGRIND_dev0 is that boundary     *)
(*  grind at pb = [0]: the hGRIND_dev recursion verbatim, with     *)
(*  base case hPX2B0 + hPOP in place of the single hPUSHX, and      *)
(*  the same (+1, +1)-shifted landing at pb = [].                   *)
(*                                                                  *)
(*  What is NOT closed here (the Phase 37 fence, stated in          *)
(*  mechanisation-status.md): the deviated grind at pb = [20; 0]    *)
(*  itself has no uniform landing -- its base case changes the      *)
(*  prefix and leaves the residue pair (16, 2), so the R = 116      *)
(*  endpoint must be assembled through the merged unwind (the       *)
(*  (16, 2) grind at [0] / [] over the (1, 2)^34 spine and the      *)
(*  era stack), and R >= 118 iterates the pattern (phase 4).        *)
(*  All forms pre-verified against the machine (zipper traces)      *)
(*  and the word-level simulator rocq/hsim36.py: hGRIND_dev0 rule   *)
(*  counts 2, 6, 14, 30, 62 = 2^(t+2) - 2 at t = 0..4, exactly      *)
(*  one PX2B0, no PUSHX.                                            *)
(* ================================================================= *)

Require Import List Bool Arith Lia ZArith.
Import ListNotations.
Require Import TM Sections Mirror TokenPass Recoord Era Esc Dev Grind Grind2.

Ltac sec_eq := repeat (first [ solve [reflexivity] | solve [lia] | f_equal ]).

(* ================================================================= *)
(*  hGRIND_dev0 -- the deviated Grind Lemma G' at the boundary      *)
(*  frame a2 = t, at pb = [0].                                      *)
(*    HC [0] t (2t+3) 2 P G  ->  HB [] (t+1) 1 (2t+7) P G.          *)
(* ================================================================= *)

Lemma hGRIND_dev0 : forall t P G,
  hsteps (HC [0] t (2*t + 3) 2 P G) (HB [] (S t) 1 (2*t + 7) P G).
Proof.
  induction t as [t IH] using lt_wf_ind.
  intros P G.
  destruct t as [|u].
  - replace (2 * 0 + 3) with 3 by lia.
    replace (2 * 0 + 7) with 7 by lia.
    apply (hsteps_step _ (HB [] 0 1 5 ((1, 2) :: P) G)).
    { apply hPX2B0. }
    apply (hsteps_step _ (HB [] 1 1 7 P G)).
    { replace 7 with (5 + 2) by lia. apply hPOP; lia. }
    apply hsteps_refl.
  - assert (Hloop : forall k i,
      2*i + 3 + 2*k = 2 * S u + 1 -> i <= u ->
      hsteps (HC [0] u (2*i + 3) 2
                 ((2 * S u + 2 - (2*i + 3), 2) :: P) G)
             (HC [0] u (2 * S u + 1) 2 ((1, 2) :: P) G)).
    { induction k as [|k IHk]; intros i Hk Hi.
      - replace (2 * S u + 2 - (2*i + 3)) with 1 by lia.
        replace (2*i + 3) with (2 * S u + 1) by lia.
        apply hsteps_refl.
      - apply (hsteps_trans _
          (HB [0] u 1 (2*i + 6)
              ((2 * S u + 2 - (2*i + 3), 2) :: P) G)).
        { apply (hGRIND i [0] u
                   ((2 * S u + 2 - (2*i + 3), 2) :: P) G).
          lia. }
        apply (hsteps_trans _
          (HC [0] u (2*(i + 1) + 3) 2
              ((2 * S u + 2 - (2*(i + 1) + 3), 2) :: P) G)).
        + apply (hsteps_step _
            (HC [0] u (2*(i + 1) + 3) 2
                ((2 * S u + 2 - (2*(i + 1) + 3), 2) :: P) G)).
          { replace (HB [0] u 1 (2*i + 6)
                ((2 * S u + 2 - (2*i + 3), 2) :: P) G)
              with (HB [0] u 1 (S (S (2*i + 4)))
                ((S (S (S (2*u - 2*i - 2))), 2) :: P) G)
              by sec_eq.
            replace (HC [0] u (2*(i + 1) + 3) 2
                ((2 * S u + 2 - (2*(i + 1) + 3), 2) :: P) G)
              with (HC [0] u (S (2*i + 4)) 2
                ((S (2*u - 2*i - 2), 2) :: P) G)
              by sec_eq.
            apply hTUP. }
          apply hsteps_refl.
        + apply IHk; lia. }
    apply (hsteps_trans _ (HC [0] u 1 2 ((2 * S u + 1, 2) :: P) G)).
    { replace (HC [0] (S u) (2 * S u + 3) 2 P G)
        with (HC [0] (S u) (S (S (S (2 * S u)))) 2 P G)
        by sec_eq.
      replace (HC [0] u 1 2 ((2 * S u + 1, 2) :: P) G)
        with (HC [0] u 1 2 ((S (2 * S u), 2) :: P) G)
        by sec_eq.
      apply (hsteps_step _ (HC [0] u 1 2 ((S (2 * S u), 2) :: P) G)).
      { apply hPUSH. }
      apply hsteps_refl. }
    apply (hsteps_trans _ (HB [0] u 1 4 ((2 * S u + 1, 2) :: P) G)).
    { apply (hsteps_step _ (HB [0] u 1 4 ((2 * S u + 1, 2) :: P) G)).
      { apply hTDN. }
      apply hsteps_refl. }
    apply (hsteps_trans _ (HC [0] u 3 2 ((2 * S u - 1, 2) :: P) G)).
    { apply (hsteps_step _ (HC [0] u 3 2 ((2 * S u - 1, 2) :: P) G)).
      { replace (HB [0] u 1 4 ((2 * S u + 1, 2) :: P) G)
          with (HB [0] u 1 (S (S 2)) ((S (S (S (2 * u))), 2) :: P) G)
          by sec_eq.
        replace (HC [0] u 3 2 ((2 * S u - 1, 2) :: P) G)
          with (HC [0] u (S 2) 2 ((S (2 * u), 2) :: P) G)
          by sec_eq.
        apply hTUP. }
      apply hsteps_refl. }
    apply (hsteps_trans _ (HC [0] u (2 * S u + 1) 2 ((1, 2) :: P) G)).
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
(*  The Phase 33 fence shape itself: the dip bottom of the         *)
(*  phase-3 boundary grind at R = 116 (grind 34 at frame 34,       *)
(*  spine (1, 2)^34 over the era stack (2, 2) :: Pe).  hPX2A0      *)
(*  fires there (b = 20, i.e. b'' = 15, cost 52).                   *)
(* ================================================================= *)

Lemma PX2A0_dip34 : forall beta,
  hstep (HC [20; 0] 0 3 2
           (repeat (1, 2) 34 ++ ((2, 2) :: (1, 1)
             :: repeat (1, 2) (beta - 1))) 1)
        (HB [0] 3 1 2
           ((16, 2) :: (1, 1) :: (1, 2) :: (1, 2)
             :: repeat (1, 2) 34 ++ ((2, 2) :: (1, 1)
             :: repeat (1, 2) (beta - 1))) 1).
Proof.
  intros beta. apply (hPX2A0 15).
Qed.

(* ----------------------------------------------------------------- *)
(* Axiom audit                                                       *)
(* ----------------------------------------------------------------- *)

Print Assumptions hGRIND_dev0.
Print Assumptions PX2A0_dip34.
