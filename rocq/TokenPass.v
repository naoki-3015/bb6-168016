(* ================================================================= *)
(* Phase 26 -- TokenPass.v: the token pass and the Cycle Lemma       *)
(* (component #14) and the general beta = 2 exit (component #15)     *)
(* for BB(6) holdout #168016, built on Mirror.v's proved mirror      *)
(* rules.  Source: token-pass-derivation.md (Phase 17).              *)
(*                                                                   *)
(* Contents:                                                         *)
(*  - cfg_sim: same state + same head-relative tape; step/run        *)
(*    congruence, so results proved for the clean section forms      *)
(*    transfer to the materialised forms (ENTRY / RPROBE landings    *)
(*    carry a trailing blank cell).                                  *)
(*  - The phase (RPUSH+RTDN), the B-excursion (iterated RPOP        *)
(*    closing in RTUP / RPROBE) with the recursive cost excR, and    *)
(*    the three round maps (type A, type B/RTUP, type B/RPROBE).     *)
(*  - The word-level Psi map on B-start gap lists, its cost          *)
(*    2u^2 + 17u + 73 (u = leading ones), the Suffix lemmas          *)
(*    (last-gap +2 replay, append-1 replay), and the orbit           *)
(*    predicate borbit with its bound.                               *)
(*  - The Cycle Lemma: from S_k(beta) = (C, beta, (2k+1), (2)) the   *)
(*    machine reaches S_{k+1}(beta) in D_k = 3*2^(k+3) - 4 steps;    *)
(*    the home section H_k = (C, beta-k, (1^(k+1)), (2^(k+1))) is    *)
(*    attained at offset 29 + bcost k + 9 inside the cycle, and      *)
(*    every B-start of the cycle has beta >= beta-k+1.               *)
(*  - The exit (#15): for every beta_E >= 4, from sigma_re(beta_E)   *)
(*    the machine reaches H = (C, 2, (1^(beta_E-1)), (2^(beta_E-1))) *)
(*    at step T(beta_E) (closed form below), and RTDN fires there    *)
(*    (6 more steps, no halting step en route) landing on the        *)
(*    B-section (beta = 0 form of the mirror frame)                  *)
(*    rbsec P 0 ((1, 4) :: (1,2)^(beta_E-2)) -- the mirror frame's   *)
(*    own successor, whose re-parse in shifted coordinates is the    *)
(*    document's X(beta_E) = (B, 4, (1^(beta_E-2)), (2^(beta_E-2))). *)
(* ================================================================= *)

Require Import List Bool Arith Lia ZArith.
Import ListNotations.
Require Import TM.
Require Import Sections.
Require Import Mirror.

(* ================================================================ *)
(* cfg_sim: same state, same head-relative tape.                    *)
(* ================================================================ *)

Definition cfg_sim (c1 c2 : config) : Prop :=
  cstate c1 = cstate c2 /\ (forall p, tape_of c1 p = tape_of c2 p).

Lemma cfg_sim_refl : forall c, cfg_sim c c.
Proof. intros c. split; reflexivity. Qed.

Lemma cfg_sim_sym : forall c1 c2, cfg_sim c1 c2 -> cfg_sim c2 c1.
Proof. intros c1 c2 [Hs Ht]. split; [symmetry; exact Hs |].
  intros p. symmetry. apply Ht. Qed.

Lemma cfg_sim_trans : forall c1 c2 c3,
  cfg_sim c1 c2 -> cfg_sim c2 c3 -> cfg_sim c1 c3.
Proof. intros c1 c2 c3 [Hs1 Ht1] [Hs2 Ht2]. split.
  - transitivity (cstate c2); assumption.
  - intros p. transitivity (tape_of c2 p); auto. Qed.

Lemma read_tape : forall c, read c = tape_of c 0.
Proof. intros c. unfold read, tape_of. simpl.
  destruct (Z_le_dec 0 0) as [_ | Hne]; [| lia].
  destruct (cright c); reflexivity. Qed.

Lemma nth_tl : forall (l : list sym) n,
  nth n (tl l) false = nth (S n) l false.
Proof. intros [| x l] n; [simpl; destruct n |]; reflexivity. Qed.

Lemma Z2Nat_add1 : forall (p : Z), (0 <= p)%Z -> Z.to_nat (p + 1) = S (Z.to_nat p).
Proof. intros p Hp. rewrite Z2Nat.inj_add by lia.
  change (Z.to_nat 1) with 1. lia. Qed.

Lemma Z2Nat_sub1 : forall (p : Z), (p <= -2)%Z ->
  Z.to_nat (- p - 1) = S (Z.to_nat (- p - 2)).
Proof. intros p Hp. replace (- p - 1)%Z with ((- p - 2) + 1)%Z by lia.
  apply Z2Nat_add1. lia. Qed.

Lemma Z2Nat_add2 : forall (p : Z), (0 <= p)%Z ->
  Z.to_nat (p + 2) = S (S (Z.to_nat p)).
Proof. intros p Hp. replace (p + 2)%Z with ((p + 1) + 1)%Z by lia.
  rewrite Z2Nat_add1 by lia. rewrite Z2Nat_add1 by lia. reflexivity. Qed.

Lemma tape_step_DR : forall (c : config) w q' p,
  tape_of (mkCfg q' (w :: cleft c) (tl (cright c))) p =
  (if Z.eq_dec p (-1) then w else tape_of c (p + 1)).
Proof.
  intros c w q' p. unfold tape_of. simpl (cleft (mkCfg _ _ _)).
  simpl (cright (mkCfg _ _ _)).
  destruct (Z.eq_dec p (-1)) as [-> | Hne].
  - destruct (Z_le_dec 0 (-1)) as [Hle | _]; [lia |]. reflexivity.
  - destruct (Z_le_dec 0 p) as [Hp | Hp].
    + destruct (Z_le_dec 0 (p + 1)) as [_ | Hle]; [| lia].
      rewrite nth_tl. rewrite Z2Nat_add1 by lia. reflexivity.
    + destruct (Z_le_dec 0 (p + 1)) as [Hle | _].
      * assert (p = (-1)%Z) by lia. congruence.
      * rewrite Z2Nat_sub1 by lia. simpl.
        replace (- (p + 1) - 1)%Z with (- p - 2)%Z by lia. reflexivity.
Qed.

Lemma tape_step_DL : forall (c : config) w q' p,
  tape_of (mkCfg q' (tl (cleft c))
             (hd false (cleft c) :: w :: tl (cright c))) p =
  (if Z.eq_dec p 0 then tape_of c (-1)
   else if Z.eq_dec p 1 then w else tape_of c (p - 1)).
Proof.
  intros c w q' p. unfold tape_of. simpl (cleft (mkCfg _ _ _)).
  simpl (cright (mkCfg _ _ _)).
  destruct (Z.eq_dec p 0) as [-> | Hne0].
  - destruct (Z_le_dec 0 0) as [_ | Hle]; [| lia]. simpl.
    destruct (Z_le_dec 0 (-1)) as [Hle | _]; [lia |].
    destruct (cleft c); reflexivity.
  - destruct (Z.eq_dec p 1) as [-> | Hne1].
    + destruct (Z_le_dec 0 1) as [_ | Hle]; [| lia]. reflexivity.
    + destruct (Z_le_dec 0 p) as [Hp | Hp].
      * destruct (Z_le_dec 0 (p - 1)) as [_ | Hle]; [| lia].
        replace (Z.to_nat p) with (S (S (Z.to_nat (p - 2)))).
        -- simpl. rewrite nth_tl.
           replace (S (Z.to_nat (p - 2))) with (Z.to_nat (p - 1)).
           ++ reflexivity.
           ++ replace (p - 1)%Z with (p - 2 + 1)%Z by lia.
              rewrite Z2Nat_add1 by lia. reflexivity.
        -- rewrite <- (Z2Nat_add2 (p - 2)%Z) by lia.
           replace (p - 2 + 2)%Z with p by lia. reflexivity.
      * destruct (Z_le_dec 0 (p - 1)) as [Hle | _]; [lia |].
        rewrite nth_tl.
        replace (- (p - 1) - 1)%Z with (- p - 1 + 1)%Z by lia.
        rewrite Z2Nat_add1 by lia. reflexivity.
Qed.

Lemma step_sim_some : forall c1 c2, cfg_sim c1 c2 ->
  forall c1', step c1 = Some c1' ->
  exists c2', step c2 = Some c2' /\ cfg_sim c1' c2'.
Proof.
  intros c1 c2 [Hs Ht] c1' Hstep. unfold step in *.
  rewrite (read_tape c1), (read_tape c2), <- Hs, <- (Ht 0%Z) in *.
  destruct (trans (cstate c1) (tape_of c1 0%Z)) as [[[w d] q'] |] eqn:E.
  - destruct d.
    + (* DL *) injection Hstep as <-.
      eexists. split; [reflexivity |]. split; [reflexivity |].
      intros p. rewrite (tape_step_DL c1), (tape_step_DL c2).
      destruct (Z.eq_dec p 0); [apply Ht |].
      destruct (Z.eq_dec p 1); [reflexivity |]. apply Ht.
    + (* DR *) injection Hstep as <-.
      eexists. split; [reflexivity |]. split; [reflexivity |].
      intros p. rewrite (tape_step_DR c1), (tape_step_DR c2).
      destruct (Z.eq_dec p (-1)%Z); [reflexivity |]. apply Ht.
  - discriminate.
Qed.

Lemma step_sim_none : forall c1 c2, cfg_sim c1 c2 ->
  step c1 = None -> step c2 = None.
Proof.
  intros c1 c2 Hsim Hnone.
  destruct (step c2) as [c2' |] eqn:E2; [| reflexivity].
  destruct (step_sim_some c2 c1 (cfg_sim_sym _ _ Hsim) c2' E2)
    as [c1' [E1 _]].
  rewrite Hnone in E1. discriminate.
Qed.

Lemma run_sim : forall n c1 c2, cfg_sim c1 c2 ->
  match run n c1, run n c2 with
  | Some c1', Some c2' => cfg_sim c1' c2'
  | None, None => True
  | _, _ => False
  end.
Proof.
  induction n; intros c1 c2 Hsim; simpl.
  - exact Hsim.
  - destruct (step c1) as [c1' |] eqn:E1.
    + destruct (step_sim_some c1 c2 Hsim c1' E1) as [c2' [E2 Hs']].
      rewrite E2. apply (IHn c1' c2'). exact Hs'.
    + rewrite (step_sim_none c1 c2 Hsim E1). exact I.
Qed.

Lemma run_sim_transfer : forall n c1 c2 d, cfg_sim c1 c2 ->
  run n c2 = Some d ->
  exists c1', run n c1 = Some c1' /\ cfg_sim c1' d.
Proof.
  intros n c1 c2 d Hsim Hrun.
  pose proof (run_sim n c1 c2 Hsim) as Hr.
  rewrite Hrun in Hr. simpl in Hr.
  destruct (run n c1) as [c1' |] eqn:E1.
  - exists c1'. split; [reflexivity |]. exact Hr.
  - contradiction.
Qed.

(* The materialised landings of Mirror.v are cfg_sim to the clean
   section forms. *)
Lemma sim_rprobe : forall P b r1'',
  cfg_sim (rcsec_probe P b (S r1'')) (rcsec P b ((S r1'', 2) :: [])).
Proof.
  intros P b r1''. split; [reflexivity |].
  intros p. apply RPROBE_tape. Qed.

Lemma sim_entry : forall B2 s,
  cfg_sim (entry_tgt B2 s)
    (rcsec (false :: repeat true (S B2) ++ (false :: repeat true 17))
       s [(1, 2)]).
Proof.
  intros B2 s. split; [reflexivity |].
  intros p. apply ENTRY_tape. Qed.

(* ================================================================ *)
(* Word helpers.  opairs ms codes gap-1 pairs with runs S r (the     *)
(* stored value is run - 1); gpairs xs codes pairs with run 2.       *)
(* excR R ms is the cost of the B-excursion that merges the opairs   *)
(* pairs into the accumulated first run R and closes (RTUP/RPROBE    *)
(* have the same cost form 2R + 6).  excN is the cost of the first   *)
(* j merges only.                                                    *)
(* ================================================================ *)

Fixpoint lsum (l : list nat) : nat :=
  match l with [] => 0 | x :: t => x + lsum t end.

Definition opairs (ms : list nat) : list (nat * nat) :=
  map (fun r => (1, S r)) ms.

Definition gpairs (xs : list nat) : list (nat * nat) :=
  map (fun x => (x, 2)) xs.

Fixpoint excR (R : nat) (ms : list nat) : nat :=
  match ms with
  | [] => 2 * R + 6
  | r :: t => (2 * R + 3) + excR (R + S r) t
  end.

Fixpoint excN (R : nat) (ms : list nat) (j : nat) : nat :=
  match j, ms with
  | 0, _ => 0
  | S j', r :: t => (2 * R + 3) + excN (R + S r) t j'
  | _, [] => 0
  end.

Lemma lsum_app : forall l1 l2, lsum (l1 ++ l2) = lsum l1 + lsum l2.
Proof. induction l1; intros; simpl; [reflexivity | rewrite IHl1; lia]. Qed.

Lemma lsum_repeat : forall x n, lsum (repeat x n) = n * x.
Proof. intros x n. induction n; simpl; [reflexivity | rewrite IHn; lia]. Qed.

Lemma opairs_app : forall l1 l2,
  opairs (l1 ++ l2) = opairs l1 ++ opairs l2.
Proof. intros. unfold opairs. apply map_app. Qed.

Lemma gpairs_app : forall l1 l2,
  gpairs (l1 ++ l2) = gpairs l1 ++ gpairs l2.
Proof. intros. unfold gpairs. apply map_app. Qed.

Lemma opairs_repeat1 : forall n, opairs (repeat 1 n) = repeat (1, 2) n.
Proof. induction n; simpl; [reflexivity | rewrite IHn; reflexivity]. Qed.

Lemma gpairs_repeat1 : forall n, gpairs (repeat 1 n) = repeat (1, 2) n.
Proof. induction n; simpl; [reflexivity | rewrite IHn; reflexivity]. Qed.

Lemma excR_repeat1 : forall R j,
  excR R (repeat 1 j) = 2 * j * j + (2 * R + 5) * j + 2 * R + 6.
Proof.
  intros R j. revert R. induction j; intros R; simpl.
  - lia.
  - rewrite IHj. nia.
Qed.

Lemma excR_split : forall ms R j, j <= length ms ->
  excR R ms = excN R ms j +
    excR (R + length (firstn j ms) + lsum (firstn j ms)) (skipn j ms).
Proof.
  induction ms; intros R j Hj.
  - destruct j; simpl in *; [lia | lia].
  - destruct j.
    + cbn [firstn skipn excN length lsum].
      replace (R + 0 + 0) with R by lia. lia.
    + simpl.
      replace (R + S (length (firstn j ms)) + (a + lsum (firstn j ms)))
        with (R + S a + length (firstn j ms) + lsum (firstn j ms)) by lia.
      rewrite (IHms (R + S a) j) by (simpl in Hj; lia). lia.
Qed.

(* ================================================================ *)
(* The phase: RPUSH then RTDN from a phase start (first run 2,       *)
(* first gap >= 3).  Cost 9 + 6 = 15.                                *)
(* ================================================================ *)

Lemma PHASE : forall P b2' g'' rest,
  run 15 (rcsec P (S b2') ((S (S (S g'')), 2) :: rest)) =
  Some (rbsec P b2' ((1, 4) :: (S g'', 2) :: rest)).
Proof.
  intros P b2' g'' rest.
  replace 15 with (9 + 6) by lia. rewrite run_split.
  rewrite RPUSH. apply RTDN.
Qed.

Lemma PHASE_second : forall P b2' g'' rest,
  run 9 (rcsec P (S b2') ((S (S (S g'')), 2) :: rest)) =
  Some (rcsec P b2' ((1, 2) :: (S g'', 2) :: rest)).
Proof. intros. apply RPUSH. Qed.

(* ================================================================ *)
(* The B-excursion: iterated RPOP over the opairs pairs, closing     *)
(* with RTUP (a further pair with gap >= 3 follows) or RPROBE        *)
(* (no further pair).  First run before the excursion is             *)
(* R = S (S R'') >= 2; the merged run ends at                        *)
(* R + length ms + lsum ms.                                          *)
(* ================================================================ *)

Lemma EXC_TUP : forall ms P b R'' g'' r2 rest,
  run (excR (S (S R'')) ms)
    (rbsec P b ((1, S (S R'')) :: (opairs ms ++ (S (S (S g'')), r2) :: rest))) =
  Some (rcsec P (b + length ms)
          ((S R'' + length ms + lsum ms, 2) :: (S g'', r2) :: rest)).
Proof.
  induction ms; intros P b R'' g'' r2 rest.
  - cbn [excR opairs length lsum app].
    replace (b + 0) with b by lia.
    replace (S R'' + 0 + 0) with (S R'') by lia. apply RTUP.
  - cbn [excR opairs map length lsum app].
    replace (b + S (length ms)) with (S b + length ms) by lia.
    replace (S R'' + S (length ms) + (a + lsum ms))
      with (S (R'' + S a) + length ms + lsum ms) by lia.
    replace (S (S R'') + S a) with (S (S (R'' + S a))) by lia.
    rewrite run_split. rewrite RPOP.
    change (S (S R'') + S a) with (S (S (R'' + S a))).
    apply IHms.
Qed.

Lemma EXC_PROBE : forall ms P b R'',
  run (excR (S (S R'')) ms)
    (rbsec P b ((1, S (S R'')) :: opairs ms)) =
  Some (rcsec_probe P (b + length ms) (S R'' + length ms + lsum ms)).
Proof.
  induction ms; intros P b R''.
  - cbn [excR opairs length lsum].
    replace (b + 0) with b by lia.
    replace (S R'' + 0 + 0) with (S R'') by lia. apply RPROBE.
  - cbn [excR opairs map length lsum app].
    replace (b + S (length ms)) with (S b + length ms) by lia.
    replace (S R'' + S (length ms) + (a + lsum ms))
      with (S (R'' + S a) + length ms + lsum ms) by lia.
    replace (S (S R'') + S a) with (S (S (R'' + S a))) by lia.
    rewrite run_split. rewrite RPOP.
    change (S (S R'') + S a) with (S (S (R'' + S a))).
    apply IHms.
Qed.

(* The excursion's intermediate B-sections: after j merges the
   machine is at rbsec P (b + j) with accumulated first run
   S R' + length (firstn j ms) + lsum (firstn j ms), reached in
   excN (S R') ms j steps. *)
Lemma EXC_prefix : forall ms P b R' fin j, j <= length ms ->
  run (excN (S R') ms j)
    (rbsec P b ((1, S R') :: (opairs ms ++ fin))) =
  Some (rbsec P (b + j)
          ((1, S R' + length (firstn j ms) + lsum (firstn j ms)) ::
             (opairs (skipn j ms) ++ fin))).
Proof.
  induction ms; intros P b R' fin j Hj.
  - destruct j.
    + cbn [excN firstn skipn length lsum opairs app].
      replace (b + 0) with b by lia.
      replace (S R' + 0 + 0) with (S R') by lia. reflexivity.
    + simpl in Hj. lia.
  - destruct j.
    + cbn [excN firstn skipn length lsum opairs map app].
      replace (b + 0) with b by lia.
      replace (S R' + 0 + 0) with (S R') by lia. reflexivity.
    + cbn [excN firstn skipn length lsum opairs map app].
      replace (S R' + S (length (firstn j ms)) + (a + lsum (firstn j ms)))
        with (S (R' + S a) + length (firstn j ms) + lsum (firstn j ms))
        by lia.
      replace (b + S j) with (S b + j) by lia.
      replace (S R' + S a) with (S (R' + S a)) by lia.
      rewrite run_split. rewrite RPOP.
      change (S R' + S a) with (S (R' + S a)).
      apply IHms. simpl in Hj. lia.
Qed.

(* ================================================================ *)
(* Rounds.  A round = phase (15) + excursion.                        *)
(* Type A (first gap >= 5): the excursion is a single RTUP on the    *)
(* phase's (1,4) run; cost 15 + 14 = 29; beta -= 1 (in b2 terms).    *)
(* Type B (first gap 3): the excursion merges the stored list        *)
(* 1 :: ms and closes with RTUP (B_TUP) or RPROBE (B_PROBE).         *)
(* ================================================================ *)

Lemma ROUND_A : forall P b2' g'' rest,
  run 29 (rcsec P (S b2') ((S (S (S (S (S g'')))), 2) :: rest)) =
  Some (rcsec P b2' ((3, 2) :: (S g'', 2) :: rest)).
Proof.
  intros P b2' g'' rest.
  replace 29 with (15 + (2 * S (S 2) + 6)) by lia. rewrite run_split.
  rewrite (PHASE P b2' (S (S g'')) rest).
  apply (RTUP P b2' 2 g'' 2 rest).
Qed.

Lemma ROUND_B_TUP : forall P b2' ms g'' r2 rest,
  run (15 + excR 4 (1 :: ms))
    (rcsec P (S b2') ((3, 2) :: (opairs ms ++ (S (S (S g'')), r2) :: rest))) =
  Some (rcsec P (b2' + length (1 :: ms))
          ((S 2 + length (1 :: ms) + lsum (1 :: ms), 2) ::
             (S g'', r2) :: rest)).
Proof.
  intros P b2' ms g'' r2 rest.
  rewrite run_split.
  rewrite (PHASE P b2' 0 (opairs ms ++ (S (S (S g'')), r2) :: rest)).
  apply (EXC_TUP (1 :: ms) P b2' 2 g'' r2 rest).
Qed.

Lemma ROUND_B_PROBE : forall P b2' ms,
  run (15 + excR 4 (1 :: ms))
    (rcsec P (S b2') ((3, 2) :: opairs ms)) =
  Some (rcsec_probe P (b2' + length (1 :: ms))
          (S 2 + length (1 :: ms) + lsum (1 :: ms))).
Proof.
  intros P b2' ms. rewrite run_split.
  rewrite (PHASE P b2' 0 (opairs ms)).
  apply (EXC_PROBE (1 :: ms) P b2' 2).
Qed.

(* The closing round of cycle k has tail repeat 1 (k-1); its RPUSH
   prefix (9 steps) is the tokenless home section H_k. *)
Lemma CLOSING_H : forall P b2' m,
  run 9 (rcsec P (S b2') ((3, 2) :: opairs (repeat 1 m))) =
  Some (rcsec P b2' ((1, 2) :: (1, 2) :: opairs (repeat 1 m))).
Proof. intros. apply (RPUSH P b2' 0 2). Qed.

(* ================================================================ *)
(* The Psi layer.  lo xs counts the leading 1s of the tail word;     *)
(* wpsi is the composed two-round (B-round + A-round) word map;      *)
(* Jg is the joint invariant (all gaps odd).                         *)
(* ================================================================ *)

Fixpoint lo (xs : list nat) : nat :=
  match xs with
  | [] => 0
  | x :: t => if x =? 1 then S (lo t) else 0
  end.

Definition wpsi (xs : list nat) : list nat :=
  (1 + 2 * lo xs) :: (nth (lo xs) xs 0 - 2) :: skipn (S (lo xs)) xs.

Definition psicost (u : nat) : nat := 2 * u * u + 17 * u + 73.

Definition Jg (xs : list nat) : Prop := Forall Nat.Odd xs.

Lemma lo_firstn : forall xs, firstn (lo xs) xs = repeat 1 (lo xs).
Proof.
  induction xs; simpl; [reflexivity |].
  destruct (a =? 1) eqn:E.
  - apply Nat.eqb_eq in E. subst a. simpl. rewrite IHxs. reflexivity.
  - reflexivity.
Qed.

Lemma lo_max : forall xs n, firstn n xs = repeat 1 n -> n <= lo xs.
Proof.
  induction xs; intros n H.
  - destruct n; simpl in *; [lia | discriminate].
  - destruct n; simpl in *; [lia |].
    injection H as H1 H2. subst a.
    simpl. specialize (IHxs n H2). lia.
Qed.

Lemma firstn_S_nth : forall (xs : list nat) n d, n < length xs ->
  firstn (S n) xs = firstn n xs ++ [nth n xs d].
Proof.
  induction xs; intros n d H; [simpl in H; lia |].
  destruct n.
  - reflexivity.
  - replace (firstn (S (S n)) (a :: xs)) with (a :: firstn (S n) xs)
      by reflexivity.
    replace (firstn (S n) (a :: xs)) with (a :: firstn n xs)
      by reflexivity.
    replace (nth (S n) (a :: xs) d) with (nth n xs d) by reflexivity.
    rewrite (IHxs n d) by (simpl in H; lia). reflexivity.
Qed.

Lemma repeat_snoc : forall (x : nat) n, repeat x n ++ [x] = repeat x (S n).
Proof.
  intros x n. induction n; simpl; [reflexivity |].
  rewrite IHn. reflexivity.
Qed.

Lemma lo_nth_ne1 : forall xs, lo xs < length xs -> nth (lo xs) xs 0 <> 1.
Proof.
  intros xs Hlt Heq.
  assert (Hle : S (lo xs) <= lo xs).
  { apply (lo_max xs (S (lo xs))).
    rewrite firstn_S_nth with (d := 0) by lia.
    rewrite lo_firstn, Heq. apply repeat_snoc. }
  lia.
Qed.

Lemma lo_decomp : forall xs, lo xs < length xs ->
  xs = repeat 1 (lo xs) ++ (nth (lo xs) xs 0 :: skipn (S (lo xs)) xs).
Proof.
  intros xs Hlt.
  rewrite <- (firstn_skipn (S (lo xs)) xs) at 1.
  rewrite firstn_S_nth with (d := 0) by exact Hlt.
  rewrite lo_firstn. rewrite <- app_assoc. reflexivity.
Qed.

Lemma lo_repeat_app : forall n z t, z <> 1 ->
  lo (repeat 1 n ++ (z :: t)) = n.
Proof.
  induction n; intros z t Hz; simpl.
  - destruct (z =? 1) eqn:E.
    + apply Nat.eqb_eq in E. congruence.
    + reflexivity.
  - rewrite IHn by exact Hz. reflexivity.
Qed.

Lemma lo_app_front : forall xs ys, lo xs < length xs ->
  lo (xs ++ ys) = lo xs.
Proof.
  intros xs ys Hlt.
  rewrite (lo_decomp xs Hlt) at 1.
  rewrite <- app_assoc. apply lo_repeat_app. apply lo_nth_ne1. exact Hlt.
Qed.

Lemma skipn_app_front : forall (xs ys : list nat) n, n <= length xs ->
  skipn n (xs ++ ys) = skipn n xs ++ ys.
Proof.
  induction xs; intros ys n Hn.
  - destruct n; simpl in *; [reflexivity | lia].
  - destruct n; simpl in *.
    + reflexivity.
    + rewrite IHxs by lia. reflexivity.
Qed.

Lemma wpsi_app_front : forall xs ys, lo xs < length xs ->
  wpsi (xs ++ ys) = wpsi xs ++ ys.
Proof.
  intros xs ys Hlt. unfold wpsi.
  rewrite lo_app_front by exact Hlt.
  rewrite app_nth1 by exact Hlt.
  rewrite skipn_app_front by lia. reflexivity.
Qed.

Lemma Jg_app_inv : forall xs ys, Jg (xs ++ ys) -> Jg xs /\ Jg ys.
Proof.
  intros xs ys H. unfold Jg in *. rewrite Forall_forall in H.
  split; apply (proj2 (Forall_forall _ _)); intros z Hz; apply H;
    apply in_or_app; auto.
Qed.

Lemma Jg_app_intro : forall xs ys, Jg xs -> Jg ys -> Jg (xs ++ ys).
Proof.
  intros xs ys H1 H2. unfold Jg in *.
  rewrite Forall_forall in H1, H2.
  apply (proj2 (Forall_forall _ _)). intros z Hz.
  apply in_app_or in Hz. destruct Hz; auto.
Qed.

Lemma Jg_nth : forall xs, Jg xs -> forall i, i < length xs ->
  Nat.Odd (nth i xs 0).
Proof.
  intros xs HJg i Hi. unfold Jg in HJg. rewrite Forall_forall in HJg.
  apply HJg. apply nth_In. exact Hi.
Qed.

Lemma Jg_skipn : forall n xs, Jg xs -> Jg (skipn n xs).
Proof.
  induction n; intros xs H; [exact H |].
  destruct xs; [exact H |].
  simpl. apply IHn. unfold Jg in *. eapply Forall_inv_tail. exact H.
Qed.

Lemma Jg_wpsi : forall xs, Jg xs -> lo xs < length xs -> Jg (wpsi xs).
Proof.
  intros xs HJg Hlt. unfold wpsi.
  assert (Hodd : Nat.Odd (nth (lo xs) xs 0)).
  { eapply Jg_nth; [exact HJg | exact Hlt]. }
  assert (Hne : nth (lo xs) xs 0 <> 1) by (apply lo_nth_ne1; exact Hlt).
  constructor.
  - exists (lo xs). lia.
  - constructor.
    + destruct Hodd as [m Hm]. exists (m - 1). lia.
    + eapply Jg_skipn. exact HJg.
Qed.

(* The master Psi step: a B-round (ROUND_B_TUP) followed by an
   A-round (ROUND_A), with an arbitrary untouched suffix fin of
   pairs.  Cost psicost (lo xs); the block grows by lo xs - 1
   (in rcsec b terms: S b2 -> b2 + lo xs). *)
Lemma psi_run_gen : forall P b2 xs fin,
  Jg xs -> lo xs < length xs ->
  run (psicost (lo xs))
    (rcsec P (S b2) ((3, 2) :: (gpairs xs ++ fin))) =
  Some (rcsec P (b2 + lo xs) ((3, 2) :: (gpairs (wpsi xs) ++ fin))).
Proof.
  intros P b2 xs fin HJg Hlt.
  remember (lo xs) as u eqn:Hu.
  remember (nth u xs 0) as x eqn:Hx.
  assert (Hodd : Nat.Odd x).
  { subst x. rewrite Hu. eapply Jg_nth;
      [exact HJg | rewrite <- Hu; exact Hlt]. }
  assert (Hne : x <> 1).
  { subst x. rewrite Hu. apply lo_nth_ne1. rewrite <- Hu. exact Hlt. }
  destruct Hodd as [m Hm].
  assert (Hm1 : 1 <= m) by lia.
  set (g'' := 2 * (m - 1)).
  assert (Hx3 : x = S (S (S g''))) by (unfold g''; lia).
  assert (Hdec : xs = repeat 1 u ++ (x :: skipn (S u) xs)).
  { rewrite Hx, Hu. apply lo_decomp. rewrite <- Hu. exact Hlt. }
  replace (psicost u)
    with ((15 + excR 4 (1 :: repeat 1 u)) + 29).
  2: { unfold psicost.
       replace (1 :: repeat 1 u) with (repeat 1 (S u)) by reflexivity.
       rewrite excR_repeat1. nia. }
  rewrite Hdec at 1. rewrite gpairs_app. rewrite <- app_assoc.
  replace (gpairs (repeat 1 u)) with (opairs (repeat 1 u)).
  2: { rewrite gpairs_repeat1, opairs_repeat1. reflexivity. }
  rewrite Hx3.
  replace (gpairs (S (S (S g'')) :: skipn (S u) xs) ++ fin)
    with ((S (S (S g'')), 2) :: (gpairs (skipn (S u) xs) ++ fin))
    by reflexivity.
  rewrite run_split.
  rewrite (ROUND_B_TUP P b2 (repeat 1 u) g'' 2
             (gpairs (skipn (S u) xs) ++ fin)).
  replace (length (1 :: repeat 1 u)) with (S u).
  2: { simpl. rewrite repeat_length. reflexivity. }
  replace (lsum (1 :: repeat 1 u)) with (S u).
  2: { simpl. rewrite lsum_repeat. lia. }
  replace (S 2 + S u + S u) with (S (S (S (S (S (2 * u)))))) by lia.
  replace (b2 + S u) with (S (b2 + u)) by lia.
  rewrite (ROUND_A P (b2 + u) (2 * u)
             ((S g'', 2) :: (gpairs (skipn (S u) xs) ++ fin))).
  unfold wpsi. rewrite <- Hu, <- Hx, Hx3.
  replace (gpairs ((1 + 2 * u) :: (S (S (S g'')) - 2) :: skipn (S u) xs))
    with ((1 + 2 * u, 2) :: (S g'', 2) :: gpairs (skipn (S u) xs))
    by reflexivity.
  reflexivity.
Qed.

(* psi_step: one Psi step between B-starts, in S-form on both sides
   (valid whenever b2 + lo xs >= 1). *)
Definition psi_step (P : list sym) (b2 : nat) (xs : list nat)
                    (b2' : nat) (xs' : list nat) : Prop :=
  Jg xs /\ lo xs < length xs /\ xs' = wpsi xs /\ b2' = b2 + lo xs - 1 /\
  run (psicost (lo xs)) (rcsec P (S b2) ((3, 2) :: gpairs xs)) =
    Some (rcsec P (S b2') ((3, 2) :: gpairs xs')).

Lemma PSI_RUN : forall P b2 xs,
  Jg xs -> lo xs < length xs -> 1 <= b2 + lo xs ->
  psi_step P b2 xs (b2 + lo xs - 1) (wpsi xs).
Proof.
  intros P b2 xs HJg Hlt Hb.
  unfold psi_step.
  repeat split; try assumption; try reflexivity.
  replace (S (b2 + lo xs - 1)) with (b2 + lo xs) by lia.
  replace (gpairs (wpsi xs)) with (gpairs (wpsi xs) ++ []).
  2: { rewrite app_nil_r. reflexivity. }
  replace ((3, 2) :: (gpairs xs)) with ((3, 2) :: (gpairs xs ++ [])).
  2: { rewrite app_nil_r. reflexivity. }
  apply (psi_run_gen P b2 xs []); assumption.
Qed.

(* ================================================================ *)
(* The B-orbit relation: a chain of Psi steps from (b2, xs) to       *)
(* (b2', xs') of total cost c, with every visited B-start S-arg      *)
(* >= lb.                                                            *)
(* ================================================================ *)

Inductive borbit (P : list sym) (lb : nat) :
    nat -> list nat -> nat -> list nat -> nat -> Prop :=
| borbit_refl : forall b2 xs, lb <= b2 ->
    borbit P lb b2 xs b2 xs 0
| borbit_step : forall b2 xs b2' xs' b2'' xs'' c',
    psi_step P b2 xs b2' xs' -> lb <= b2 -> lb <= b2' ->
    borbit P lb b2' xs' b2'' xs'' c' ->
    borbit P lb b2 xs b2'' xs'' (psicost (lo xs) + c').

Lemma borbit_run : forall P lb b2 xs b2' xs' c,
  borbit P lb b2 xs b2' xs' c ->
  run c (rcsec P (S b2) ((3, 2) :: gpairs xs)) =
  Some (rcsec P (S b2') ((3, 2) :: gpairs xs')).
Proof.
  intros P lb b2 xs b2' xs' c H. induction H.
  - reflexivity.
  - destruct H as [_ [_ [_ [_ Hrun]]]].
    rewrite run_split. rewrite Hrun. exact IHborbit.
Qed.

Lemma borbit_lb : forall P lb b2 xs b2' xs' c,
  borbit P lb b2 xs b2' xs' c -> lb <= b2 /\ lb <= b2'.
Proof.
  intros P lb b2 xs b2' xs' c H. induction H; split; try assumption;
    destruct IHborbit as [_ Hle]; exact Hle.
Qed.

Lemma borbit_weaken : forall P lb lb' b2 xs b2' xs' c,
  lb' <= lb -> borbit P lb b2 xs b2' xs' c ->
  borbit P lb' b2 xs b2' xs' c.
Proof.
  intros P lb lb' b2 xs b2' xs' c Hle H. induction H.
  - apply borbit_refl. lia.
  - eapply borbit_step; eauto; lia.
Qed.

Lemma borbit_trans : forall P lb b2 xs b2' xs' b2'' xs'' c1 c2,
  borbit P lb b2 xs b2' xs' c1 ->
  borbit P lb b2' xs' b2'' xs'' c2 ->
  borbit P lb b2 xs b2'' xs'' (c1 + c2).
Proof.
  intros P lb b2 xs b2' xs' b2'' xs'' c1 c2 H1 H2.
  induction H1.
  - exact H2.
  - replace ((psicost (lo xs) + c') + c2)
      with (psicost (lo xs) + (c' + c2)) by lia.
    eapply borbit_step; eauto.
Qed.

(* The S-form recovery: a Psi step's landing block is forced. *)
Lemma psi_step_Sform : forall P b2 xs b2' xs',
  psi_step P b2 xs b2' xs' -> S b2' = b2 + lo xs.
Proof.
  intros P b2 xs b2' xs' Hstep.
  destruct Hstep as [HJg [Hlo [Hxs' [Hb2' Hrun]]]].
  pose proof (psi_run_gen P b2 xs [] HJg Hlo) as Hgen.
  rewrite <- Hxs' in Hgen. rewrite !app_nil_r in Hgen.
  assert (HeqS : Some (rcsec P (S b2') ((3, 2) :: gpairs xs')) =
                 Some (rcsec P (b2 + lo xs) ((3, 2) :: gpairs xs'))).
  { rewrite <- Hrun. exact Hgen. }
  injection HeqS as Heq.
  pose proof (f_equal (@length sym) Heq) as HeqL.
  cbn [length] in HeqL.
  rewrite !app_length, !repeat_length in HeqL. lia.
Qed.

Lemma Jg_repeat1 : forall n, Jg (repeat 1 n).
Proof.
  induction n; simpl; constructor.
  - exists 0. reflexivity.
  - exact IHn.
Qed.

Lemma lo_le_length : forall xs, lo xs <= length xs.
Proof.
  induction xs; simpl; [lia |].
  destruct (a =? 1); lia.
Qed.

(* Suffix transport 1: appending a fixed odd y to every word. *)
Lemma psi_step_front : forall P b2 xs b2' xs' y,
  psi_step P b2 xs b2' xs' -> Nat.Odd y ->
  psi_step P b2 (xs ++ [y]) b2' (xs' ++ [y]).
Proof.
  intros P b2 xs b2' xs' y Hstep HOdd.
  pose proof Hstep as Hstep0.
  destruct Hstep0 as [HJg [Hlo [Hxs' [Hb2' Hrun]]]].
  assert (HSf : S b2' = b2 + lo xs).
  { apply (psi_step_Sform P b2 xs b2' xs'). exact Hstep. }
  unfold psi_step.
  split; [apply Jg_app_intro; [exact HJg | repeat constructor; exact HOdd] |].
  split; [rewrite lo_app_front by exact Hlo;
          rewrite app_length; simpl; lia |].
  split; [rewrite wpsi_app_front by exact Hlo; rewrite Hxs'; reflexivity |].
  split; [rewrite lo_app_front by exact Hlo; exact Hb2' |].
  rewrite lo_app_front by exact Hlo.
  rewrite !gpairs_app.
  replace (gpairs [y]) with [(y, 2)] by reflexivity.
  pose proof (psi_run_gen P b2 xs [(y, 2)] HJg Hlo) as Hgen.
  rewrite <- Hxs' in Hgen. rewrite <- HSf in Hgen.
  exact Hgen.
Qed.

Lemma borbit_map : forall (F : list nat -> list nat) P lb,
  (forall w, lo w < length w -> lo (F w) = lo w) ->
  (forall b2 w b2' w', psi_step P b2 w b2' w' ->
     psi_step P b2 (F w) b2' (F w')) ->
  forall b2 xs b2' xs' c, borbit P lb b2 xs b2' xs' c ->
  borbit P lb b2 (F xs) b2' (F xs') c.
Proof.
  intros F P lb HFlo HF b2 xs b2' xs' c H. induction H.
  - apply borbit_refl. exact H.
  - assert (Hlo : lo xs < length xs) by (destruct H; intuition).
    rewrite <- (HFlo xs Hlo).
    eapply borbit_step.
    + apply HF. exact H.
    + exact H0.
    + exact H1.
    + exact IHborbit.
Qed.

(* Suffix transport 2: appending 1 to every word, block one less. *)
Lemma psi_step_app1 : forall P lb b2 xs b2' xs',
  psi_step P b2 xs b2' xs' -> lb <= b2 -> lb <= b2' -> 1 <= lb ->
  psi_step P (b2 - 1) (xs ++ [1]) (b2' - 1) (xs' ++ [1]).
Proof.
  intros P lb b2 xs b2' xs' Hstep Hb2 Hb2' Hlb.
  destruct Hstep as [HJg [Hlo [Hxs' [Hb2'eq Hrun]]]].
  unfold psi_step.
  split; [apply Jg_app_intro; [exact HJg | repeat constructor;
          exists 0; reflexivity] |].
  split; [rewrite lo_app_front by exact Hlo;
          rewrite app_length; simpl; lia |].
  split; [rewrite wpsi_app_front by exact Hlo; rewrite Hxs'; reflexivity |].
  split; [rewrite lo_app_front by exact Hlo; lia |].
  rewrite lo_app_front by exact Hlo.
  pose proof (psi_run_gen P (b2 - 1) xs [(1, 2)] HJg Hlo) as Hgen.
  replace ((b2 - 1) + lo xs) with (S (b2' - 1)) in Hgen by lia.
  rewrite <- Hxs' in Hgen.
  replace (gpairs xs ++ [(1, 2)]) with (gpairs (xs ++ [1])) in Hgen.
  2: { rewrite gpairs_app. reflexivity. }
  replace (gpairs xs' ++ [(1, 2)]) with (gpairs (xs' ++ [1])) in Hgen.
  2: { rewrite gpairs_app. reflexivity. }
  exact Hgen.
Qed.

Lemma borbit_app1 : forall P lb b2 xs b2' xs' c,
  borbit P lb b2 xs b2' xs' c -> 1 <= lb ->
  borbit P (lb - 1) (b2 - 1) (xs ++ [1]) (b2' - 1) (xs' ++ [1]) c.
Proof.
  intros P lb b2 xs b2' xs' c H Hlb. induction H.
  - apply borbit_refl. lia.
  - assert (Hlo : lo xs < length xs) by (destruct H; intuition).
    rewrite <- (lo_app_front xs [1] Hlo).
    eapply borbit_step.
    + eapply psi_step_app1; eauto.
    + lia.
    + lia.
    + exact IHborbit.
Qed.

(* ================================================================ *)
(* Suffix transport 3: last gap + 2 (the first replay of the orbit   *)
(* recursion).  last2f is defined via rev for clean app lemmas.      *)
(* ================================================================ *)

Definition last2f (w : list nat) : list nat :=
  match rev w with
  | [] => []
  | z :: t => rev ((z + 2) :: t)
  end.

Lemma last2f_app : forall xs y, last2f (xs ++ [y]) = xs ++ [y + 2].
Proof.
  intros xs y. unfold last2f. rewrite rev_unit.
  replace ((y + 2) :: rev xs) with ([y + 2] ++ rev xs) by reflexivity.
  rewrite rev_app_distr, rev_involutive. reflexivity.
Qed.

Lemma last2f_repeat1 : forall n,
  last2f (repeat 1 (S n)) = repeat 1 n ++ [3].
Proof.
  intros n. rewrite <- (repeat_snoc 1 n). rewrite last2f_app.
  reflexivity.
Qed.

Lemma list_decomp_last : forall (w : list nat), w <> [] ->
  exists xs y, w = xs ++ [y].
Proof.
  induction w as [| a w IH]; intros Hne; [congruence |].
  destruct w as [| b w'].
  - exists [], a. reflexivity.
  - destruct (IH ltac:(discriminate)) as [xs [y Hy]].
    exists (a :: xs), y. simpl. rewrite Hy. reflexivity.
Qed.

Lemma lo_repeat : forall n, lo (repeat 1 n) = n.
Proof.
  induction n; simpl; [reflexivity |].
  rewrite IHn. reflexivity.
Qed.

Lemma lo_app_ones : forall xs z, xs = repeat 1 (length xs) -> z <> 1 ->
  lo (xs ++ [z]) = length xs.
Proof.
  intros xs z Hrep Hz. rewrite Hrep at 1.
  replace [z] with (z :: []) by reflexivity.
  apply lo_repeat_app. exact Hz.
Qed.

Lemma lo_last2f : forall w, lo w < length w -> lo (last2f w) = lo w.
Proof.
  intros w Hlt. destruct w as [| a w'].
  - simpl in Hlt. lia.
  - destruct (list_decomp_last (a :: w') ltac:(discriminate))
      as [xs [y Hw]].
    rewrite Hw in *. rewrite last2f_app.
    destruct (lt_eq_lt_dec (lo xs) (length xs)) as [[Hc | Hc] | Hc].
    + rewrite (lo_app_front xs [y + 2]) by exact Hc.
      rewrite (lo_app_front xs [y]) by exact Hc. reflexivity.
    + assert (Hrep : xs = repeat 1 (length xs)).
      { pose proof (lo_firstn xs) as Hf. rewrite Hc, firstn_all in Hf.
        exact Hf. }
      destruct (Nat.eq_dec y 1) as [Hy | Hy].
      * subst y. exfalso.
        assert (lo (xs ++ [1]) = S (length xs)).
        { replace (xs ++ [1]) with (repeat 1 (S (length xs))).
          - apply lo_repeat.
          - rewrite <- repeat_snoc. rewrite <- Hrep. reflexivity. }
        rewrite app_length in Hlt. simpl in Hlt. lia.
      * rewrite (lo_app_ones xs y Hrep) by exact Hy.
        rewrite (lo_app_ones xs (y + 2) Hrep) by lia. reflexivity.
    + pose proof (lo_le_length xs). lia.
Qed.

Lemma psi_step_last2f : forall P b2 w b2' w',
  psi_step P b2 w b2' w' -> psi_step P b2 (last2f w) b2' (last2f w').
Proof.
  intros P b2 w b2' w' Hstep.
  assert (Hne : w <> []).
  { destruct Hstep as [_ [Hlo _]]. destruct w; simpl in *;
      [lia | discriminate]. }
  destruct (list_decomp_last w Hne) as [xs [y Hw]].
  assert (HOddy : Nat.Odd y).
  { destruct Hstep as [HJg _]. subst w. unfold Jg in HJg.
    rewrite Forall_forall in HJg. apply HJg. apply in_or_app.
    right. simpl. auto. }
  subst w. rewrite last2f_app.
  destruct Hstep as [HJg [Hlo [Hw' [Hb2' Hrun]]]].
  assert (HSf : S b2' = b2 + lo (xs ++ [y])).
  { apply (psi_step_Sform P b2 (xs ++ [y]) b2' w').
    unfold psi_step. repeat split; assumption. }
  assert (HJgF : Jg xs) by (exact (proj1 (Jg_app_inv xs [y] HJg))).
  assert (HJg2 : Jg (xs ++ [y + 2])).
  { apply Jg_app_intro; [exact HJgF |].
    repeat constructor. destruct HOddy as [m Hm]. exists (m + 1). lia. }
  destruct (lt_eq_lt_dec (lo xs) (length xs)) as [[Hc | Hc] | Hc].
  - (* split inside the front *)
    assert (Hlo1 : lo (xs ++ [y]) = lo xs) by (apply lo_app_front; exact Hc).
    assert (Hlo2 : lo (xs ++ [y + 2]) = lo xs)
      by (apply lo_app_front; exact Hc).
    assert (Hword : last2f w' = wpsi (xs ++ [y + 2])).
    { rewrite Hw', (wpsi_app_front xs [y]) by exact Hc.
      rewrite last2f_app.
      rewrite (wpsi_app_front xs [y + 2]) by exact Hc. reflexivity. }
    unfold psi_step.
    split; [exact HJg2 |].
    split; [rewrite Hlo2, app_length; simpl; lia |].
    split; [exact Hword |].
    split; [rewrite Hlo2, <- Hlo1; exact Hb2' |].
    rewrite Hlo2.
    pose proof (psi_run_gen P b2 xs [(y + 2, 2)] HJgF Hc) as Hgen.
    replace (gpairs xs ++ [(y + 2, 2)]) with (gpairs (xs ++ [y + 2]))
      in Hgen by (rewrite gpairs_app; reflexivity).
    replace (gpairs (wpsi xs) ++ [(y + 2, 2)])
      with (gpairs (wpsi xs ++ [y + 2])) in Hgen
      by (rewrite gpairs_app; reflexivity).
    rewrite <- (wpsi_app_front xs [y + 2]) in Hgen by exact Hc.
    rewrite Hlo1 in HSf. rewrite <- HSf in Hgen.
    rewrite <- Hword in Hgen. exact Hgen.
  - (* front all-ones: the carry case *)
    assert (Hrep : xs = repeat 1 (length xs)).
    { pose proof (lo_firstn xs) as Hf. rewrite Hc, firstn_all in Hf.
      exact Hf. }
    destruct (Nat.eq_dec y 1) as [Hy | Hy].
    + subst y. exfalso.
      assert (lo (xs ++ [1]) = S (length xs)).
      { replace (xs ++ [1]) with (repeat 1 (S (length xs))).
        - apply lo_repeat.
        - rewrite <- repeat_snoc. rewrite <- Hrep. reflexivity. }
      rewrite app_length in Hlo. simpl in Hlo. lia.
    + assert (Hloy : lo (xs ++ [y]) = length xs)
        by (apply lo_app_ones; assumption).
      assert (Hloy2 : lo (xs ++ [y + 2]) = length xs)
        by (apply lo_app_ones; [exact Hrep | lia]).
      assert (Hwpsi : wpsi (xs ++ [y]) = (1 + 2 * length xs) :: [y - 2]).
      { unfold wpsi. rewrite Hloy.
        replace (nth (length xs) (xs ++ [y]) 0) with y.
        2: { rewrite app_nth2 by lia. rewrite Nat.sub_diag. reflexivity. }
        replace (skipn (S (length xs)) (xs ++ [y])) with (@nil nat).
        2: { symmetry. apply skipn_all2. rewrite app_length.
             simpl. lia. }
        reflexivity. }
      assert (Hwpsi2 : wpsi (xs ++ [y + 2]) = (1 + 2 * length xs) :: [y]).
      { unfold wpsi. rewrite Hloy2.
        replace (nth (length xs) (xs ++ [y + 2]) 0) with (y + 2).
        2: { rewrite app_nth2 by lia. rewrite Nat.sub_diag. reflexivity. }
        replace (skipn (S (length xs)) (xs ++ [y + 2])) with (@nil nat).
        2: { symmetry. apply skipn_all2. rewrite app_length.
             simpl. lia. }
        replace (y + 2 - 2) with y by lia. reflexivity. }
      assert (Hword : last2f w' = wpsi (xs ++ [y + 2])).
      { rewrite Hw', Hwpsi, Hwpsi2.
        replace ((1 + 2 * length xs) :: [y - 2])
          with ([1 + 2 * length xs] ++ [y - 2]) by reflexivity.
        rewrite last2f_app.
        replace (y - 2 + 2) with y
          by (destruct HOddy as [m Hm]; lia).
        reflexivity. }
      unfold psi_step.
      split; [exact HJg2 |].
      split; [rewrite Hloy2, app_length; simpl; lia |].
      split; [exact Hword |].
      split; [rewrite Hloy2, <- Hloy; exact Hb2' |].
      pose proof (psi_run_gen P b2 (xs ++ [y + 2]) [] HJg2) as Hgen.
      assert (Hlo2' : lo (xs ++ [y + 2]) < length (xs ++ [y + 2])).
      { rewrite Hloy2, app_length. simpl. lia. }
      specialize (Hgen Hlo2').
      rewrite !app_nil_r in Hgen. rewrite Hloy2 in Hgen.
      rewrite Hloy in HSf. rewrite <- HSf in Hgen.
      rewrite <- Hword in Hgen. rewrite Hloy2. exact Hgen.
  - pose proof (lo_le_length xs). lia.
Qed.

(* ================================================================ *)
(* bcost: the total Psi cost of cycle k's orbit.                     *)
(* bcost (k+1) = 2 * bcost k + psicost (k-2) for k >= 2, in the      *)
(* S(S(S j)) form below.  Closed form (k >= 2):                      *)
(* bcost k + 2k^2 + 13k + 62 = 3 * 2^(k+3).                          *)
(* ================================================================ *)

Fixpoint bcost (k : nat) : nat :=
  match k with
  | S k1 => match k1 with
            | S k2 => match k2 with
                      | S k' => 2 * bcost k1
                                  + (2 * k' * k' + 17 * k' + 73)
                      | _ => 0
                      end
            | _ => 0
            end
  | _ => 0
  end.

Lemma bcost_closed : forall j,
  bcost (2 + j) + 2 * (2 + j) * (2 + j) + 13 * (2 + j) + 62
  = 3 * 2 ^ (2 + j + 3).
Proof.
  induction j.
  - reflexivity.
  - replace (bcost (2 + S j))
      with (2 * bcost (2 + j) + (2 * j * j + 17 * j + 73))
      by reflexivity.
    assert (Hpow : 2 ^ (2 + S j + 3) = 2 * 2 ^ (2 + j + 3)).
    { replace (2 + S j + 3) with (S (2 + j + 3)) by lia.
      rewrite Nat.pow_succ_r'. reflexivity. }
    nia.
Qed.

(* The orbit recursion (derivation S5): cycle (2 + S j)'s orbit is
   cycle (2 + j)'s orbit replayed with the last gap + 2, then the
   carry step, then cycle (2 + j)'s orbit at B - 1 with a 1 appended
   to every word. *)
Lemma borbit_cycle : forall P j B, j <= B ->
  borbit P (B - j) B ((2 * (2 + j) - 3) :: [])
    (B - j) (repeat 1 (2 + j - 1)) (bcost (2 + j)).
Proof.
  intros P j. induction j; intros B HjB.
  - replace (B - 0) with B by lia. apply borbit_refl. lia.
  - assert (HjB' : j <= B) by lia.
    assert (HjB'' : j <= B - 1) by lia.
    pose proof (IHj B HjB') as HorbB.
    pose proof (IHj (B - 1) HjB'') as HorbB1.
    (* replay 1: last gap + 2 *)
    pose proof (borbit_map last2f P (B - j) lo_last2f
                  (fun b2 w b2' w' => psi_step_last2f P b2 w b2' w')
                  B ((2 * (2 + j) - 3) :: []) (B - j)
                  (repeat 1 (2 + j - 1)) (bcost (2 + j)) HorbB) as Hrep1.
    replace (2 + j - 1) with (S j) in Hrep1 by lia.
    rewrite last2f_repeat1 in Hrep1.
    replace (last2f ((2 * (2 + j) - 3) :: []))
      with ((2 * (2 + S j) - 3) :: []) in Hrep1.
    2: { replace (2 * (2 + j) - 3) with (2 * j + 1) by lia.
         replace (2 * (2 + S j) - 3) with (2 * j + 3) by lia.
         replace ((2 * j + 1) :: []) with ([] ++ [2 * j + 1])
           by reflexivity.
         rewrite last2f_app.
         replace (2 * j + 1 + 2) with (2 * j + 3) by lia.
         reflexivity. }
    pose proof (borbit_weaken P (B - j) (B - S j) B
                  ((2 * (2 + S j) - 3) :: []) (B - j)
                  (repeat 1 j ++ [3]) (bcost (2 + j))
                  ltac:(lia) Hrep1) as Hrep1w.
    (* the carry step *)
    assert (Hcarry : psi_step P (B - j) (repeat 1 j ++ [3]) (B - 1)
                       ((1 + 2 * j) :: [1])).
    { assert (HJg : Jg (repeat 1 j ++ [3])).
      { apply Jg_app_intro; [apply Jg_repeat1 |].
        repeat constructor. exists 1. reflexivity. }
      assert (Hlo : lo (repeat 1 j ++ [3]) < length (repeat 1 j ++ [3])).
      { rewrite lo_repeat_app by discriminate.
        rewrite app_length, repeat_length. simpl. lia. }
      assert (Hb : 1 <= (B - j) + lo (repeat 1 j ++ [3])).
      { rewrite lo_repeat_app by discriminate. lia. }
      pose proof (PSI_RUN P (B - j) (repeat 1 j ++ [3]) HJg Hlo Hb)
        as Hpsi.
      rewrite lo_repeat_app in Hpsi by discriminate.
      replace ((B - j) + j - 1) with (B - 1) in Hpsi by lia.
      replace (wpsi (repeat 1 j ++ [3])) with ((1 + 2 * j) :: [1])
        in Hpsi.
      2: { unfold wpsi.
           rewrite lo_repeat_app by discriminate.
           replace (nth j (repeat 1 j ++ [3]) 0) with 3.
           2: { rewrite app_nth2 by (rewrite repeat_length; lia).
                rewrite repeat_length, Nat.sub_diag. reflexivity. }
           replace (skipn (S j) (repeat 1 j ++ [3])) with (@nil nat).
           2: { symmetry. apply skipn_all2. rewrite app_length,
                  repeat_length. simpl. lia. }
           reflexivity. }
      exact Hpsi. }
    pose proof (borbit_step P (B - S j) (B - j) (repeat 1 j ++ [3])
                  (B - 1) ((1 + 2 * j) :: [1]) (B - 1)
                  ((1 + 2 * j) :: [1]) 0 Hcarry ltac:(lia) ltac:(lia)
                  (borbit_refl P (B - S j) (B - 1) ((1 + 2 * j) :: [1])
                     ltac:(lia))) as Hmid1.
    rewrite lo_repeat_app in Hmid1 by discriminate.
    replace (psicost j + 0) with (psicost j) in Hmid1 by lia.
    pose proof (borbit_trans P (B - S j) B ((2 * (2 + S j) - 3) :: [])
                  (B - j) (repeat 1 j ++ [3]) (B - 1)
                  ((1 + 2 * j) :: [1])
                  (bcost (2 + j)) (psicost j) Hrep1w Hmid1) as Hmid.
    (* replay 2: IH at B - 1, append 1 *)
    replace ((B - 1) - j) with (B - S j) in HorbB1 by lia.
    rename HorbB1 into IHj0.
    assert (HFlo1 : forall w, lo w < length w -> lo (w ++ [1]) = lo w).
    { intros w Hw. apply lo_app_front. exact Hw. }
    assert (HFstep1 : forall b2 w b2' w', psi_step P b2 w b2' w' ->
               psi_step P b2 (w ++ [1]) b2' (w' ++ [1])).
    { intros b2 w b2' w' H. apply (psi_step_front P b2 w b2' w' 1 H).
      exists 0. reflexivity. }
    pose proof (borbit_map (fun w => w ++ [1]) P (B - S j)
                  HFlo1 HFstep1) as Hmap1.
    specialize (Hmap1 (B - 1) ((2 * (2 + j) - 3) :: []) (B - S j)
                  (repeat 1 (2 + j - 1)) (bcost (2 + j)) IHj0).
    rename Hmap1 into Hrep2. cbv beta in Hrep2.
    assert (Heq : repeat 1 (2 + S j - 1) = repeat 1 (2 + j - 1) ++ [1]).
    { replace (2 + j - 1) with (S j) by lia.
      replace (2 + S j - 1) with (S (S j)) by lia.
      symmetry. apply repeat_snoc. }
    rewrite <- Heq in Hrep2.
    replace (((2 * (2 + j) - 3) :: []) ++ [1])
      with ((1 + 2 * j) :: [1]) in Hrep2
      by (replace (2 * (2 + j) - 3) with (2 * j + 1) by lia;
          replace (1 + 2 * j) with (2 * j + 1) by lia; reflexivity).
    pose proof (borbit_trans P (B - S j) B ((2 * (2 + S j) - 3) :: [])
                  (B - 1) ((1 + 2 * j) :: [1]) (B - S j)
                  (repeat 1 (2 + S j - 1))
                  (bcost (2 + j) + psicost j) (bcost (2 + j))
                  Hmid Hrep2) as Htot.
    replace (bcost (2 + j) + psicost j + bcost (2 + j))
      with (bcost (2 + S j)) in Htot.
    2: { assert (bcost (2 + S j) = 2 * bcost (2 + j) + psicost j)
           by reflexivity. lia. }
    exact Htot.
Qed.

(* ================================================================ *)
(* Part 6: the Cycle Lemma and the exit.                             *)
(* S_k in frame B (beta_E = B + 4): rcsec P (B + 2) ((2k+1, 2)::[]). *)
(* ================================================================ *)

Definition Dk (k : nat) : nat := 3 * 2 ^ (k + 3) - 4.

Lemma CYCLE : forall P B k, 2 <= k -> k - 2 <= B ->
  run (Dk k) (rcsec P (B + 2) ((2 * k + 1, 2) :: [])) =
  Some (rcsec_probe P (B + 2) (2 * k + 3)).
Proof.
  intros P B k Hk HkB.
  (* the A-round *)
  assert (HA : run 29 (rcsec P (B + 2) ((2 * k + 1, 2) :: [])) =
    Some (rcsec P (S B) ((3, 2) :: gpairs ((2 * k - 3) :: [])))).
  { pose proof (ROUND_A P (S B) (2 * k - 4) []) as H.
    replace (S (S (S (S (S (2 * k - 4)))))) with (2 * k + 1) in H
      by lia.
    replace (S (2 * k - 4)) with (2 * k - 3) in H by lia.
    replace (B + 2) with (S (S B)) by lia.
    exact H. }
  (* the orbit *)
  pose proof (borbit_cycle P (k - 2) B HkB) as Horbit.
  replace (2 + (k - 2)) with k in Horbit by lia.
  pose proof (borbit_run P (B - (k - 2)) B ((2 * k - 3) :: [])
                (B - (k - 2)) (repeat 1 (k - 1)) (bcost k) Horbit)
    as Hrun_orbit.
  (* the closing round *)
  assert (Heq1 : 1 :: repeat 1 (k - 1) = repeat 1 k).
  { destruct k as [| [| k']]; [lia | reflexivity | reflexivity]. }
  pose proof (ROUND_B_PROBE P (B - (k - 2)) (repeat 1 (k - 1)))
    as Hclose.
  rewrite Heq1 in Hclose. rewrite opairs_repeat1 in Hclose.
  cbn [length] in Hclose. rewrite repeat_length in Hclose.
  replace (S (k - 1)) with k in Hclose by lia.
  cbn [lsum] in Hclose. rewrite lsum_repeat in Hclose.
  replace ((k - 1) * 1) with (k - 1) in Hclose by lia.
  replace ((B - (k - 2)) + k) with (B + 2) in Hclose by lia.
  replace (S 2 + k + k * 1) with (2 * k + 3) in Hclose by lia.
  (* assemble *)
  replace (Dk k) with (29 + (bcost k + (15 + excR 4 (repeat 1 k)))).
  2: { unfold Dk. pose proof (bcost_closed (k - 2)) as Hbc.
       replace (2 + (k - 2)) with k in Hbc by lia.
       pose proof (excR_repeat1 4 k) as He. nia. }
  rewrite run_split. rewrite HA. rewrite run_split.
  rewrite Hrun_orbit. rewrite gpairs_repeat1. exact Hclose.
Qed.

Lemma CYCLE_sim : forall P B k, 2 <= k -> k - 2 <= B ->
  exists c, run (Dk k) (rcsec P (B + 2) ((2 * k + 1, 2) :: [])) =
    Some c /\ cfg_sim c (rcsec P (B + 2) ((2 * k + 3, 2) :: [])).
Proof.
  intros P B k Hk HkB. exists (rcsec_probe P (B + 2) (2 * k + 3)).
  split; [apply CYCLE; assumption |].
  replace (2 * k + 3) with (S (2 * k + 2)) by lia.
  apply sim_rprobe.
Qed.

(* The tokenless home section H_k, reached 29 + bcost k + 9 steps
   into cycle k: word beta = beta_E - k exactly (rcsec arg
   B - (k - 2), i.e. word beta (B - (k-2)) + 2 = B + 4 - k). *)
Lemma CYCLE_H : forall P B k, 2 <= k -> k - 2 <= B ->
  run (29 + bcost k + 9) (rcsec P (B + 2) ((2 * k + 1, 2) :: [])) =
  Some (rcsec P (B - (k - 2)) (repeat (1, 2) (k + 1))).
Proof.
  intros P B k Hk HkB.
  assert (HA : run 29 (rcsec P (B + 2) ((2 * k + 1, 2) :: [])) =
    Some (rcsec P (S B) ((3, 2) :: gpairs ((2 * k - 3) :: [])))).
  { pose proof (ROUND_A P (S B) (2 * k - 4) []) as H.
    replace (S (S (S (S (S (2 * k - 4)))))) with (2 * k + 1) in H
      by lia.
    replace (S (2 * k - 4)) with (2 * k - 3) in H by lia.
    replace (B + 2) with (S (S B)) by lia.
    exact H. }
  pose proof (borbit_cycle P (k - 2) B HkB) as Horbit.
  replace (2 + (k - 2)) with k in Horbit by lia.
  pose proof (borbit_run P (B - (k - 2)) B ((2 * k - 3) :: [])
                (B - (k - 2)) (repeat 1 (k - 1)) (bcost k) Horbit)
    as Hrun_orbit.
  pose proof (CLOSING_H P (B - (k - 2)) (k - 1)) as Hcl.
  rewrite opairs_repeat1 in Hcl.
  replace (29 + bcost k + 9) with (29 + (bcost k + 9)) by lia.
  rewrite run_split. rewrite HA. rewrite run_split.
  rewrite Hrun_orbit. rewrite gpairs_repeat1.
  replace (k + 1) with (S (S (k - 1))) by lia.
  exact Hcl.
Qed.

(* Cycle 0 (finite): S_0 -> S_1 in 20 = D_0 steps. *)
Lemma CYCLE0 : forall P K,
  run 20 (rcsec P K ((1, 2) :: [])) = Some (rcsec_probe P K 3).
Proof.
  intros P K.
  replace 20 with (6 + (2 * S (S 2) + 6)) by lia.
  rewrite run_split. rewrite (RTDN P K 1 []).
  apply RPROBE.
Qed.

(* Cycle 1 (finite): S_1 -> S_2 in 44 = D_1 steps. *)
Lemma CYCLE1 : forall P K, 1 <= K ->
  run 44 (rcsec P K ((3, 2) :: [])) = Some (rcsec_probe P K 5).
Proof.
  intros P K HK. destruct K as [| b]; [lia |].
  pose proof (ROUND_B_PROBE P b []) as H.
  replace (15 + excR 4 (1 :: [])) with 44 in H by reflexivity.
  cbn [length lsum] in H.
  replace (b + 1) with (S b) in H by lia.
  replace (S 2 + 1 + 1) with 5 in H by lia.
  exact H.
Qed.

Fixpoint Dsum (j : nat) : nat :=
  match j with
  | 0 => 0
  | S j' => Dsum j' + Dk j'
  end.

Lemma Dsum_closed : forall K, Dsum K + 4 * K + 28 = 3 * 2 ^ (K + 3) + 4.
Proof.
  induction K.
  - reflexivity.
  - assert (HDk : Dk K + 4 = 3 * 2 ^ (K + 3)).
    { unfold Dk.
      assert (H1 : 1 <= 2 ^ K).
      { pose proof (Nat.pow_le_mono_r 2 0 K ltac:(lia)
                      (Nat.le_0_l K)) as Hp. simpl in Hp. exact Hp. }
      assert (Hpow : 2 ^ (K + 3) = 8 * 2 ^ K).
      { replace (K + 3) with (3 + K) by lia.
        rewrite Nat.pow_add_r. reflexivity. }
      lia. }
    assert (Hpow : 2 ^ (S K + 3) = 2 * 2 ^ (K + 3)).
    { replace (S K + 3) with (S (K + 3)) by lia.
      rewrite Nat.pow_succ_r'. reflexivity. }
    replace (Dsum (S K)) with (Dsum K + Dk K) by reflexivity.
    lia.
Qed.

Lemma run_compose_sim : forall n m c1 c1' c2 d,
  run n c1 = Some c1' -> cfg_sim c1' c2 -> run m c2 = Some d ->
  exists c, run (n + m) c1 = Some c /\ cfg_sim c d.
Proof.
  intros n m c1 c1' c2 d H1 Hs H2.
  destruct (run_sim_transfer m c1' c2 d Hs H2) as [c [Hc Hsc]].
  exists c. split; [| exact Hsc].
  rewrite run_split. rewrite H1. exact Hc.
Qed.

(* Iterating the cycles from S_0 (frame K = beta_E - 2). *)
Lemma EXIT_iter : forall P K j, j <= K ->
  exists c, run (Dsum j) (rcsec P K ((1, 2) :: [])) = Some c /\
    cfg_sim c (rcsec P K ((2 * j + 1, 2) :: [])).
Proof.
  intros P K j. induction j; intros Hj.
  - exists (rcsec P K ((1, 2) :: [])). split; [reflexivity |].
    replace (2 * 0 + 1) with 1 by lia. apply cfg_sim_refl.
  - destruct (IHj ltac:(lia)) as [c1 [H1 Hs1]].
    assert (Hstep : exists c2, run (Dk j) (rcsec P K ((2 * j + 1, 2) :: []))
             = Some c2 /\
             cfg_sim c2 (rcsec P K ((2 * S j + 1, 2) :: []))).
    { destruct j as [| [| j']].
      - (* cycle 0 *)
        exists (rcsec_probe P K 3). split; [apply CYCLE0 |].
        replace (2 * 1 + 1) with 3 by lia.
        replace 3 with (S 2) by lia. apply sim_rprobe.
      - (* cycle 1 *)
        exists (rcsec_probe P K 5).
        split; [apply CYCLE1; lia |].
        replace (2 * 2 + 1) with 5 by lia.
        replace 5 with (S 4) by lia. apply sim_rprobe.
      - (* cycle >= 2 *)
        replace (2 * S (S j') + 1) with (2 * (S (S j')) + 1) by lia.
        replace K with ((K - 2) + 2) by lia.
        replace (2 * S (S (S j')) + 1) with (2 * S (S j') + 3) by lia.
        apply CYCLE_sim; lia. }
    destruct Hstep as [c2 [H2 Hs2]].
    destruct (run_compose_sim (Dsum j) (Dk j)
                (rcsec P K ((1, 2) :: [])) c1
                (rcsec P K ((2 * j + 1, 2) :: [])) c2 H1 Hs1 H2)
      as [c [Hc Hsc]].
    exists c. split.
    + replace (Dsum (S j)) with (Dsum j + Dk j) by reflexivity.
      exact Hc.
    + apply (cfg_sim_trans c c2); assumption.
Qed.

Definition Tk (K : nat) : nat := Dsum K + 29 + bcost K + 9.

Lemma EXIT_time : forall K, 2 <= K ->
  Tk K + 2 * K * K + 17 * K + 48 = 3 * 2 ^ (K + 4).
Proof.
  intros K HK. unfold Tk.
  pose proof (Dsum_closed K) as Hd.
  pose proof (bcost_closed (K - 2)) as Hb.
  replace (2 + (K - 2)) with K in Hb by lia.
  assert (Hpow : 2 ^ (K + 4) = 2 * 2 ^ (K + 3)).
  { replace (K + 4) with (S (K + 3)) by lia.
    rewrite Nat.pow_succ_r'. reflexivity. }
  nia.
Qed.

(* The exit: at cycle K = beta_E - 2 the home section H_K has word
   beta 2 (rcsec arg 0); RTDN fires event-clean and lands in the
   B-section with first run 4, in coordinates shifted by the frozen
   prefix (component #15). *)
Lemma EXIT : forall P K, 2 <= K ->
  exists c, run (Tk K + 6) (rcsec P K ((1, 2) :: [])) = Some c /\
    cfg_sim c (rbsec P 0 ((1, 4) :: repeat (1, 2) K)).
Proof.
  intros P K HK.
  destruct (EXIT_iter P K K (Nat.le_refl K)) as [c1 [H1 Hs1]].
  pose proof (CYCLE_H P (K - 2) K HK ltac:(lia)) as HH.
  replace ((K - 2) + 2) with K in HH by lia.
  replace ((K - 2) - (K - 2)) with 0 in HH by lia.
  replace (K + 1) with (S K) in HH by lia.
  destruct (run_compose_sim (Dsum K) (29 + bcost K + 9)
              (rcsec P K ((1, 2) :: [])) c1
              (rcsec P K ((2 * K + 1, 2) :: []))
              (rcsec P 0 (repeat (1, 2) (S K))) H1 Hs1 HH)
    as [c2 [H2 Hs2]].
  pose proof (RTDN P 0 1 (repeat (1, 2) K)) as HR.
  destruct (run_sim_transfer 6 c2 (rcsec P 0 (repeat (1, 2) (S K)))
              (rbsec P 0 ((1, S (S (S 1))) :: repeat (1, 2) K))
              Hs2 HR) as [c3 [H3 Hs3]].
  exists c3. split.
  - replace (Tk K + 6) with (Dsum K + (29 + bcost K + 9) + 6)
      by (unfold Tk; lia).
    rewrite run_split. rewrite H2. exact H3.
  - exact Hs3.
Qed.

(* The exit instantiated at the actual entry prefix. *)
Lemma EXIT_entry : forall B2 s, 2 <= s ->
  exists c, run (Tk s + 6) (entry_tgt B2 s) = Some c /\
    cfg_sim c (rbsec (false :: repeat true (S B2) ++
                        (false :: repeat true 17))
                 0 ((1, 4) :: repeat (1, 2) s)).
Proof.
  intros B2 s Hs.
  destruct (EXIT (false :: repeat true (S B2) ++
                    (false :: repeat true 17)) s Hs) as [c [H1 Hs1]].
  destruct (run_sim_transfer (Tk s + 6) (entry_tgt B2 s)
              (rcsec (false :: repeat true (S B2) ++
                        (false :: repeat true 17)) s ((1, 2) :: []))
              c (sim_entry B2 s) H1) as [c' [Hc' Hsc']].
  exists c'. split; [exact Hc' |].
  apply (cfg_sim_trans c' c); assumption.
Qed.

Print Assumptions CYCLE.
Print Assumptions CYCLE_H.
Print Assumptions EXIT.
Print Assumptions EXIT_entry.
