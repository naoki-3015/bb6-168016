(* ================================================================= *)
(* Recoord.v -- component #16: re-coordinatisation (phase19        *)
(* section 3), mechanised as far as the derived components allow.  *)
(*                                                                 *)
(* After the beta = 2 exit (TokenPass.EXIT), the continuation      *)
(* re-coordinatises into the standard I-system:                    *)
(*   stage 1: RPOP chain + RPROBE  (PROVED, parametric in the      *)
(*            frozen prefix P);                                    *)
(*   stage 2: the Phase 17 suffix recursion on the diagonal        *)
(*            (beta, m) = (beta_E, beta_E - 1) -- same recursion   *)
(*            depth as the Cycle Lemma itself; kernel-verified     *)
(*            here at the trajectory prefix for beta_E = 4, 6, 8,  *)
(*            and carried as an explicit hypothesis STAGE2 in      *)
(*            the composition -- NOT an admit);                    *)
(*   stage 3: RPUSH escape + F-sweep, cost B2 + 11, landing the    *)
(*            canonical I-section with residue rho = B2 - 2        *)
(*            (PROVED for all B2 >= 2, parametric in the tail Q    *)
(*            beyond the L-block).                                 *)
(*                                                                 *)
(* Conventions: entryP B2 is the frozen prefix (nearest-first)     *)
(*   false :: 1^B2 ++ false :: 1^17                                *)
(* of a mirror-frame section whose absolute second block is B2.    *)
(* Mirror.v's ENTRY at parameter b produces prefix entryP (S b);   *)
(* the trajectory's first era enters at b = 30, i.e. entryP 31,    *)
(* matching the verified Phase 18/19 trace configs (block 31).     *)
(* ================================================================= *)

Require Import List Bool Arith Lia ZArith.
Import ListNotations.
Require Import TM Sections Mirror TokenPass Finite DiagPass.

(* ----------------------------------------------------------------- *)
(* Prefix and generalised C-section                                  *)
(* ----------------------------------------------------------------- *)

Definition entryP (B2 : nat) : list sym :=
  false :: repeat true B2 ++ (false :: repeat true 17).

(* C-section over an abstract tail Q beyond the a-block: the landing *)
(* form of stage 3 (Q = [] gives Sections.csec).                     *)
Definition gcsec (Q : list sym) (a2 g0 s : nat)
                 (pairs : list (nat * nat)) (G : nat) : config :=
  mkCfg SC (repeat true a2 ++ Q)
        (true :: true :: (repeat false g0 ++
          (repeat true s ++ tail pairs G))).

Lemma gcsec_nil : forall a2 g0 s pairs G,
  gcsec [] a2 g0 s pairs G = csec a2 g0 s pairs G.
Proof. intros. unfold gcsec, csec. rewrite app_nil_r. reflexivity. Qed.

(* ----------------------------------------------------------------- *)
(* Stage 1: RPOP chain + RPROBE (phase19 3.1)                        *)
(* From the exit successor rbsec P 0 ((1,4) :: (1,2)^n): the chain  *)
(* fires RPOP at r1 = 2j+4 (cost 4j+11), landing at                  *)
(* 2j^2 + 9j on rbsec P j ((1, 2j+4) :: (1,2)^(n-j)); RPROBE then    *)
(* lands (up to cfg_sim) on rcsec P n ((2n+3, 2) :: []).             *)
(* ----------------------------------------------------------------- *)

Lemma stage1_chain : forall P n j, j <= n ->
  run (2*j*j + 9*j) (rbsec P 0 ((1, 4) :: repeat (1, 2) n))
  = Some (rbsec P j ((1, 2*j + 4) :: repeat (1, 2) (n - j))).
Proof.
  intros P n j. induction j as [|j IH]; intros Hj.
  - replace (n - 0) with n by lia. reflexivity.
  - assert (Hjn : j < n) by lia.
    replace (2 * S j * S j + 9 * S j) with ((2*j*j + 9*j) + (4*j + 11)) by nia.
    rewrite run_split.
    rewrite IH by lia.
    replace (n - j) with (S (n - j - 1)) by lia.
    cbn [repeat].
    replace (2 * j + 4) with (S (2 * j + 3)) by lia.
    replace (2 * S j + 4) with (S (2 * j + 3) + 2) by lia.
    replace (4 * j + 11) with (2 * S (2 * j + 3) + 3) by lia.
    replace (n - S j) with (n - j - 1) by lia.
    apply RPOP.
Qed.

Lemma STAGE1 : forall P n, exists c,
  run (2*n*n + 13*n + 14) (rbsec P 0 ((1, 4) :: repeat (1, 2) n)) = Some c
  /\ cfg_sim c (rcsec P n ((2*n + 3, 2) :: [])).
Proof.
  intros P n.
  replace (2*n*n + 13*n + 14) with ((2*n*n + 9*n) + (4*n + 14)) by lia.
  rewrite run_split.
  rewrite (stage1_chain P n n) by lia.
  rewrite Nat.sub_diag. cbn [repeat].
  exists (rcsec_probe P n (2*n + 3)).
  split.
  - replace (2 * n + 4) with (S (S (2 * n + 2))) by lia.
    replace (2 * n + 3) with (S (2 * n + 2)) by lia.
    replace (4 * n + 14) with (2 * S (S (2 * n + 2)) + 6) by lia.
    apply RPROBE.
  - replace (2 * n + 3) with (S (2 * n + 2)) by lia.
    apply sim_rprobe.
Qed.

(* Stage 1 composed with the general exit (TokenPass.EXIT): from    *)
(* the right-edge entry section to S_{beta_E - 1}(beta_E).          *)
Lemma STAGE1_exit : forall P K, 2 <= K -> exists c,
  run ((Tk K + 6) + (2*K*K + 13*K + 14))
      (rcsec P K ((1, 2) :: [])) = Some c
  /\ cfg_sim c (rcsec P K ((2*K + 3, 2) :: [])).
Proof.
  intros P K HK.
  destruct (EXIT P K HK) as [c1 [Hrun1 Hsim1]].
  destruct (STAGE1 P K) as [c2 [Hrun2 Hsim2]].
  destruct (run_sim_transfer _ _ _ _ Hsim1 Hrun2) as [c2' [Hr2' Hs2']].
  exists c2'. split.
  - rewrite run_split. rewrite Hrun1. exact Hr2'.
  - eapply cfg_sim_trans; eassumption.
Qed.

Definition s3R (n : nat) : list sym := rtail (repeat (1, 2) (S n)).

(* ----------------------------------------------------------------- *)
(* List helpers for the stage-3 landing forms                        *)
(* ----------------------------------------------------------------- *)

(* Sections.tail (with its terminal block) vs Mirror.rtail. *)
Lemma tail_rtail : forall ps G,
  tail ps G = rtail ps ++ (repeat false G ++ [true; true]).
Proof.
  induction ps as [|[g r] ps IH]; intros G.
  - reflexivity.
  - cbn [tail rtail]. rewrite IH. rewrite !app_assoc. reflexivity.
Qed.

Lemma s3R_cons : forall n,
  s3R (S n) = [false; true; true] ++ s3R n.
Proof. intros. reflexivity. Qed.

(* The (0,1,1) period of s3R commutes with its own block. *)
Lemma s3R_snoc : forall n,
  s3R n ++ [false; true; true] = [false; true; true] ++ s3R n.
Proof.
  induction n as [|n IH].
  - reflexivity.
  - rewrite s3R_cons. rewrite <- app_assoc. f_equal. exact IH.
Qed.

(* ----------------------------------------------------------------- *)
(* Stage 3: RPUSH escape + F-sweep (phase19 3.3)                     *)
(* Source: rcsec (false :: 1^B2 ++ false :: 1^L ++ Q) 0              *)
(*         ((3, 2) :: (1, 2)^n)   (escape section, beta = 2).        *)
(* Cost B2 + 11; landing gcsec Q (L-1) (B2-2) 2 ((1,1) :: (1,2)^(n+1)) 1. *)
(* ----------------------------------------------------------------- *)

Definition s3form9 (Q : list sym) (L B2 n : nat) : config :=
  mkCfg SC (repeat true B2 ++ (false :: repeat true L ++ Q))
        (false :: true :: false :: true :: true :: s3R n).

Definition s3form12 (Q : list sym) (L b3 n : nat) : config :=
  mkCfg SF (repeat true b3 ++ (false :: repeat true L ++ Q))
        (true :: true :: true :: false :: true :: false :: true :: true
         :: s3R n).

Definition s3form41 (Q : list sym) (L b3 n : nat) : config :=
  mkCfg SF (repeat true L ++ Q)
        (repeat false (S (S b3)) ++
         (true :: true :: false :: true :: false :: true :: true :: s3R n)).

Lemma STAGE3_9 : forall Q L B2 n,
  run 9 (rcsec (false :: repeat true B2 ++ (false :: repeat true L ++ Q)) 0
             ((3, 2) :: repeat (1, 2) n))
  = Some (s3form9 Q L B2 n).
Proof. intros. reflexivity. Qed.

Lemma STAGE3_mid : forall Q L b3 n,
  run 3 (s3form9 Q L (S (S (S b3))) n) = Some (s3form12 Q L b3 n).
Proof. intros. reflexivity. Qed.

Lemma STAGE3_sweep : forall Q L b3 n,
  run (b3 + 1) (s3form12 Q L b3 n) = Some (s3form41 Q L b3 n).
Proof.
  intros Q L b3 n.
  rewrite (run_split b3 1).
  replace (s3form12 Q L b3 n) with
    (mkCfg SF (repeat true b3 ++ (false :: repeat true L ++ Q))
              (true :: (true :: true :: false :: true :: false :: true
                        :: true :: s3R n)))
    by reflexivity.
  rewrite sweepF.
  reflexivity.
Qed.

Lemma STAGE3_final : forall Q l b3 n,
  run 1 (s3form41 Q (S l) b3 n)
  = Some (gcsec Q l (S b3) 2 ((1, 1) :: repeat (1, 2) (S n)) 1).
Proof.
  intros Q l b3 n. rewrite run_1.
  unfold s3form41, gcsec, step, trans, read.
  cbn [repeat app hd tl cleft cright cstate].
  rewrite tail_rtail.
  replace ((1, 2) :: repeat (1, 2) n) with (repeat (1, 2) (S n))
    by reflexivity.
  cbn [rtail].
  change (repeat false 1) with [false].
  change (repeat true 1) with [true].
  fold (s3R n).
  rewrite <- app_assoc. rewrite <- app_assoc.
  change ([false] ++ [true; true]) with [false; true; true].
  rewrite s3R_snoc.
  reflexivity.
Qed.

Lemma STAGE3_ge3 : forall Q L B2 n, 3 <= B2 -> 1 <= L ->
  run (B2 + 11)
    (rcsec (false :: repeat true B2 ++ (false :: repeat true L ++ Q)) 0
           ((3, 2) :: repeat (1, 2) n))
  = Some (gcsec Q (L - 1) (B2 - 2) 2 ((1, 1) :: repeat (1, 2) (S n)) 1).
Proof.
  intros Q L B2 n HB2 HL.
  destruct B2 as [|[|[|b3]]]; try lia.
  destruct L as [|l]; try lia.
  replace (S (S (S b3)) + 11) with (9 + (3 + ((b3 + 1) + 1))) by lia.
  rewrite (run_split 9 (3 + ((b3 + 1) + 1))).
  rewrite STAGE3_9.
  rewrite (run_split 3 ((b3 + 1) + 1)).
  rewrite STAGE3_mid.
  rewrite (run_split (b3 + 1) 1).
  rewrite STAGE3_sweep.
  replace (S l - 1) with l by lia.
  replace (S (S (S b3)) - 2) with (S b3) by lia.
  apply STAGE3_final.
Qed.

(* B2 = 2: the F-sweep erases the whole block; the last four steps  *)
(* of stage 3 go through three exposed intermediate forms.         *)
Definition b2f10 (Q : list sym) (L n : nat) : config :=
  mkCfg SD (true :: false :: repeat true L ++ Q)
        (true :: false :: true :: false :: true :: true :: s3R n).

Definition b2f11 (Q : list sym) (L n : nat) : config :=
  mkCfg SE (false :: repeat true L ++ Q)
        (true :: true :: false :: true :: false :: true :: true :: s3R n).

Definition b2f12 (Q : list sym) (L n : nat) : config :=
  mkCfg SF (repeat true L ++ Q)
        (false :: true :: true :: false :: true :: false :: true :: true
         :: s3R n).

Lemma b2_step10 : forall Q L n,
  run 1 (s3form9 Q L 2 n) = Some (b2f10 Q L n).
Proof. intros. reflexivity. Qed.

Lemma b2_step11 : forall Q L n,
  run 1 (b2f10 Q L n) = Some (b2f11 Q L n).
Proof. intros. reflexivity. Qed.

Lemma b2_step12 : forall Q L n,
  run 1 (b2f11 Q L n) = Some (b2f12 Q L n).
Proof. intros. reflexivity. Qed.

Lemma b2_step13 : forall Q l n,
  run 1 (b2f12 Q (S l) n)
  = Some (gcsec Q l 0 2 ((1, 1) :: repeat (1, 2) (S n)) 1).
Proof.
  intros Q l n. rewrite run_1.
  unfold b2f12, gcsec, step, trans, read.
  cbn [repeat app hd tl cleft cright cstate].
  rewrite tail_rtail.
  replace ((1, 2) :: repeat (1, 2) n) with (repeat (1, 2) (S n))
    by reflexivity.
  cbn [rtail].
  change (repeat false 1) with [false].
  change (repeat true 1) with [true].
  fold (s3R n).
  rewrite <- app_assoc. rewrite <- app_assoc.
  change ([false] ++ [true; true]) with [false; true; true].
  rewrite s3R_snoc.
  reflexivity.
Qed.

Lemma STAGE3_b2_tail : forall Q L n, 1 <= L ->
  run 4 (s3form9 Q L 2 n)
  = Some (gcsec Q (L - 1) 0 2 ((1, 1) :: repeat (1, 2) (S n)) 1).
Proof.
  intros Q L n HL. destruct L as [|l]; try lia.
  replace (S l - 1) with l by lia.
  replace 4 with (1 + (1 + (1 + 1))) by lia.
  rewrite run_split. rewrite b2_step10.
  rewrite run_split. rewrite b2_step11.
  rewrite run_split. rewrite b2_step12.
  apply b2_step13.
Qed.

Lemma STAGE3_b2 : forall Q L n, 1 <= L ->
  run 13 (rcsec (false :: repeat true 2 ++ (false :: repeat true L ++ Q)) 0
             ((3, 2) :: repeat (1, 2) n))
  = Some (gcsec Q (L - 1) 0 2 ((1, 1) :: repeat (1, 2) (S n)) 1).
Proof.
  intros Q L n HL.
  replace 13 with (9 + 4) by lia.
  rewrite run_split. rewrite STAGE3_9.
  apply STAGE3_b2_tail. exact HL.
Qed.

Lemma STAGE3 : forall Q L B2 n, 2 <= B2 -> 1 <= L ->
  run (B2 + 11)
    (rcsec (false :: repeat true B2 ++ (false :: repeat true L ++ Q)) 0
           ((3, 2) :: repeat (1, 2) n))
  = Some (gcsec Q (L - 1) (B2 - 2) 2 ((1, 1) :: repeat (1, 2) (S n)) 1).
Proof.
  intros Q L B2 n HB2 HL.
  destruct B2 as [|[|[|b3]]]; try lia.
  - replace (2 + 11) with 13 by lia. apply STAGE3_b2. exact HL.
  - apply STAGE3_ge3; lia.
Qed.

(* ----------------------------------------------------------------- *)
(* Stage 2: the diagonal suffix recursion (phase19 3.2)              *)
(* S_{beta_E - 1}(beta_E) = rcsec (entryP B2) n ((2n+3, 2) :: [])    *)
(* reaches the escape section esc_cfg in exactly Tk n steps (the     *)
(* Phase 17 exit time).  The general case is the Phase 17 recursion  *)
(* on the diagonal -- a second TokenPass-scale development; it is    *)
(* carried as the explicit hypothesis STAGE2 below.  Instances at    *)
(* the trajectory prefix entryP 31 are kernel-verified.              *)
(* ----------------------------------------------------------------- *)

Definition esc_cfg (B2 n : nat) : config :=
  rcsec (entryP B2) 0 ((3, 2) :: repeat (1, 2) n).

Definition STAGE2 (B2 n : nat) : Prop :=
  exists c, run (Tk n) (rcsec (entryP B2) n ((2*n + 3, 2) :: [])) = Some c
            /\ cfg_sim c (esc_cfg B2 n).

Lemma stage2_inst_2 : STAGE2 31 2.
Proof. unfold STAGE2, esc_cfg, entryP, cfg_sim. apply seg_check_sound.
       vm_compute. reflexivity. Qed.

Lemma stage2_inst_4 : STAGE2 31 4.
Proof. unfold STAGE2, esc_cfg, entryP, cfg_sim. apply seg_check_sound.
       vm_compute. reflexivity. Qed.

Lemma stage2_inst_6 : STAGE2 31 6.
Proof. unfold STAGE2, esc_cfg, entryP, cfg_sim. apply seg_check_sound.
       vm_compute. reflexivity. Qed.

(* ----------------------------------------------------------------- *)
(* RECOORD2: the composed two-block re-coordinatisation.             *)
(* From a right-edge entry section (entry_tgt at B2 - 1, i.e. the    *)
(* frozen prefix entryP B2), conditional on STAGE2 at (B2, n): the   *)
(* exit + stage 1 + stage 2 + stage 3 land on the canonical          *)
(* I-section csec 16 (B2 - 2) 2 ((1,1) :: (1,2)^(n+1)) 1 -- for the   *)
(* trajectory prefix B2 = 31 this is the settled residue rho = 29.   *)
(* ----------------------------------------------------------------- *)

Lemma RECOORD2 : forall B2 n, 3 <= B2 -> 2 <= n -> STAGE2 B2 n ->
  exists c,
  run ((Tk n + 6) + (2*n*n + 13*n + 14) + Tk n + (B2 + 11))
      (entry_tgt (B2 - 1) n) = Some c
  /\ cfg_sim c (csec 16 (B2 - 2) 2 ((1, 1) :: repeat (1, 2) (S n)) 1).
Proof.
  intros B2 n HB2 Hn HS2.
  destruct (EXIT_entry (B2 - 1) n Hn) as [c1 [Hr1 Hs1]].
  replace (S (B2 - 1)) with B2 in Hs1 by lia.
  fold (entryP B2) in Hs1.
  destruct (STAGE1 (entryP B2) n) as [c2 [Hr2 Hs2]].
  destruct (run_sim_transfer _ _ _ _ Hs1 Hr2) as [c2' [Hr2' Hs2']].
  assert (Hs2'' : cfg_sim c2' (rcsec (entryP B2) n ((2*n + 3, 2) :: []))).
  { eapply cfg_sim_trans; eassumption. }
  destruct HS2 as [cs2 [Hrs2 Hss2]].
  destruct (run_sim_transfer _ _ _ _ Hs2'' Hrs2) as [c3 [Hr3 Hs3]].
  assert (Hs3' : cfg_sim c3 (esc_cfg B2 n)).
  { eapply cfg_sim_trans; eassumption. }
  assert (Hst3 : run (B2 + 11) (esc_cfg B2 n)
                 = Some (csec 16 (B2 - 2) 2 ((1, 1) :: repeat (1, 2) (S n)) 1)).
  { unfold esc_cfg, entryP.
    replace (repeat true 17) with (repeat true 17 ++ [])
      by (rewrite app_nil_r; reflexivity).
    rewrite <- (gcsec_nil 16 (B2 - 2) 2 ((1, 1) :: repeat (1, 2) (S n)) 1).
    apply STAGE3; lia. }
  destruct (run_sim_transfer _ _ _ _ Hs3' Hst3) as [c4 [Hr4 Hs4]].
  exists c4. split; [|exact Hs4].
  rewrite (run_split ((Tk n + 6) + (2*n*n + 13*n + 14) + Tk n) (B2 + 11)).
  rewrite (run_split ((Tk n + 6) + (2*n*n + 13*n + 14)) (Tk n)).
  rewrite (run_split (Tk n + 6) (2*n*n + 13*n + 14)).
  rewrite Hr1. rewrite Hr2'. rewrite Hr3. exact Hr4.
Qed.

(* ----------------------------------------------------------------- *)
(* Axiom audit: every headline result must be closed.                *)
(* ----------------------------------------------------------------- *)

Print Assumptions STAGE1.
Print Assumptions STAGE1_exit.
Print Assumptions STAGE3.
Print Assumptions stage2_inst_2.
Print Assumptions stage2_inst_4.
Print Assumptions stage2_inst_6.
Print Assumptions RECOORD2.

(* Phase 28: further kernel-verified STAGE2 instances -- B2-independence *)
(* at n = 2 (B2 = 15, 47) and larger n at the trajectory prefix          *)
(* (n = 8: Tk 8 = 2850 steps; n = 10: Tk 10 = 11976 steps).  The         *)
(* general case remains the explicit hypothesis of RECOORD2.             *)
Lemma stage2_inst_8 : STAGE2 31 8.
Proof. unfold STAGE2, esc_cfg, entryP, cfg_sim. apply seg_check_sound.
       vm_compute. reflexivity. Qed.

Lemma stage2_inst_10 : STAGE2 31 10.
Proof. unfold STAGE2, esc_cfg, entryP, cfg_sim. apply seg_check_sound.
       vm_compute. reflexivity. Qed.

Lemma stage2_inst_15_2 : STAGE2 15 2.
Proof. unfold STAGE2, esc_cfg, entryP, cfg_sim. apply seg_check_sound.
       vm_compute. reflexivity. Qed.

Lemma stage2_inst_47_2 : STAGE2 47 2.
Proof. unfold STAGE2, esc_cfg, entryP, cfg_sim. apply seg_check_sound.
       vm_compute. reflexivity. Qed.

(* ----------------------------------------------------------------- *)
(* Phase 30: STAGE2 in general (DiagPass.v, DSTAGE2 at the frozen    *)
(* prefix entryP B2), discharging RECOORD2 unconditionally.  The     *)
(* two-block re-coordinatisation (component #16) is now fully        *)
(* mechanised: stages 1 and 3 (above), stage 2 (DiagPass.DSTAGE2).   *)
(* ----------------------------------------------------------------- *)

Lemma STAGE2_proved : forall B2 n, 2 <= n -> STAGE2 B2 n.
Proof.
  intros B2 n Hn. unfold STAGE2, esc_cfg.
  apply DSTAGE2. exact Hn.
Qed.

Lemma RECOORD2_uncond : forall B2 n, 3 <= B2 -> 2 <= n ->
  exists c,
  run ((Tk n + 6) + (2*n*n + 13*n + 14) + Tk n + (B2 + 11))
      (entry_tgt (B2 - 1) n) = Some c
  /\ cfg_sim c (csec 16 (B2 - 2) 2 ((1, 1) :: repeat (1, 2) (S n)) 1).
Proof.
  intros B2 n HB2 Hn. apply RECOORD2; [exact HB2 | exact Hn |].
  apply STAGE2_proved. exact Hn.
Qed.

Print Assumptions STAGE2_proved.
Print Assumptions RECOORD2_uncond.
