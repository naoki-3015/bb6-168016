(* ================================================================= *)
(* Phase 25 -- Mirror.v: the right-edge regime of #168016            *)
(* (rightedge-derivation.md): the entry excursion (component #12)    *)
(* and the five mirror rules RTDN / RPUSH / RPOP / RTUP / RPROBE     *)
(* (component #13), as soundness lemmas over right-sections.         *)
(*                                                                   *)
(* A right-section has tape  prefix . W  with W = 1^beta (0^g 1^r)*  *)
(* ending in a run (blank beyond), where the frozen prefix is        *)
(* carried as an abstract left list P.  C-form: head C on beta's      *)
(* second-to-last cell (beta = b2 + 2).  B-form: head B on the       *)
(* first gap cell after beta.  The rules that probe the blank        *)
(* (RPROBE, entry) materialise one trailing blank cell at the end    *)
(* of the right list; their landings are stated in the exact         *)
(* computed form, with a tape corollary identifying the landing      *)
(* with the documents' clean section (via nth_app_false).            *)
(* ================================================================= *)

Require Import List Bool Arith Lia ZArith.
Import ListNotations.
Require Import TM.
Require Import Sections.

Fixpoint rtail (pairs : list (nat * nat)) : list sym :=
  match pairs with
  | [] => []
  | (g, r) :: t => repeat false g ++ (repeat true r ++ rtail t)
  end.

Definition rcsec (P : list sym) (b2 : nat) (pairs : list (nat * nat))
  : config :=
  mkCfg SC (repeat true b2 ++ P) (true :: true :: rtail pairs).

Definition rbsec (P : list sym) (b : nat) (pairs : list (nat * nat))
  : config :=
  mkCfg SB (repeat true b ++ P) (rtail pairs).

Lemma nth_app_false_gen : forall (l1 l2 : list sym) i,
  nth i (l1 ++ (l2 ++ [false])) false = nth i (l1 ++ l2) false.
Proof.
  intros l1 l2 i. rewrite app_assoc. apply nth_app_false.
Qed.

(* ---------------------------------------------------------------- *)
(* RTDN: C-form, g1 = 1: beta -= 2, r1 += 2, -> B-form.  Cost 6.     *)
(* ---------------------------------------------------------------- *)

Lemma RTDN : forall P b2 r1' rest,
  run 6 (rcsec P b2 ((1, S r1') :: rest)) =
  Some (rbsec P b2 ((1, S (S (S r1'))) :: rest)).
Proof. intros. reflexivity. Qed.

(* ---------------------------------------------------------------- *)
(* RPUSH: C-form, g1 >= 3: beta -= 1, the pair (1, 2) is pushed      *)
(* and g1 drops by 2.  Cost 9.                                       *)
(* ---------------------------------------------------------------- *)

Lemma RPUSH : forall P b2' g'' r1 rest,
  run 9 (rcsec P (S b2') ((S (S (S g'')), r1) :: rest)) =
  Some (rcsec P b2' ((1, 2) :: (S g'', r1) :: rest)).
Proof. intros. reflexivity. Qed.

(* ---------------------------------------------------------------- *)
(* RPOP: B-form, g1 = 1, g2 = 1: beta += 1, r1 and r2 merge.         *)
(* Cost 2*r1 + 3.  Assembled from the prefix (B, C, Sweep-A,         *)
(* A-fill) and the return (Sweep-B plus the landing step),           *)
(* mirroring POP in Sections.v.                                      *)
(* ---------------------------------------------------------------- *)

Lemma rpop_prefix : forall P b r1' r2 rest,
  run (S r1' + 2) (rbsec P b ((1, S r1') :: (1, r2) :: rest)) =
  Some (mkCfg SB (repeat true (S r1') ++ (false :: repeat true (S b) ++ P))
                 (repeat true r2 ++ rtail rest)).
Proof.
  intros P b r1' r2 rest.
  replace (S r1' + 2) with (2 + (r1' + 1)) by lia.
  rewrite run_split.
  assert (H2 : run 2 (rbsec P b ((1, S r1') :: (1, r2) :: rest)) =
    Some (mkCfg SA (false :: repeat true (S b) ++ P)
           (repeat true r1' ++
             (false :: (repeat true r2 ++ rtail rest))))).
  { reflexivity. }
  rewrite H2. cbv beta iota.
  rewrite run_split.
  rewrite sweepA. cbv beta iota.
  reflexivity.
Qed.

Lemma rpop_sweep : forall P b r1' r2' rest,
  run (S r1' + 1)
    (mkCfg SB (repeat true (S r1') ++ (false :: repeat true (S b) ++ P))
              (repeat true (S r2') ++ rtail rest)) =
  Some (rbsec P (S b) ((1, S r1' + S r2') :: rest)).
Proof.
  intros P b r1' r2' rest.
  rewrite run_split.
  change (repeat true (S r2') ++ rtail rest)
    with (true :: (repeat true r2' ++ rtail rest)).
  rewrite sweepB. cbv beta iota.
  unfold rbsec, rtail. simpl (repeat false 1).
  rewrite rep_app. rewrite <- !app_assoc.
  reflexivity.
Qed.

Lemma RPOP : forall P b r1' r2' rest,
  run (2 * S r1' + 3) (rbsec P b ((1, S r1') :: (1, S r2') :: rest)) =
  Some (rbsec P (S b) ((1, S r1' + S r2') :: rest)).
Proof.
  intros P b r1' r2' rest.
  replace (2 * S r1' + 3) with ((S r1' + 2) + (S r1' + 1)) by lia.
  rewrite run_split.
  rewrite rpop_prefix.
  exact (rpop_sweep P b r1' r2' rest).
Qed.

(* ---------------------------------------------------------------- *)
(* RTUP: B-form, g1 = 1, g2 >= 3: beta += 2, g1 := r1 - 1, a pair    *)
(* (g1' = r1 - 1, 2) is written at g2 and g2 drops by 2.             *)
(* Cost 2*r1 + 6.  Mirrors TUP in Sections.v.                        *)
(* ---------------------------------------------------------------- *)

Lemma rtup_prefix : forall P b r1' g2' r2 rest,
  run (S r1' + 2) (rbsec P b ((1, S r1') :: (S g2', r2) :: rest)) =
  Some (mkCfg SB (repeat true (S r1') ++ (false :: repeat true (S b) ++ P))
                 (repeat false g2' ++ (repeat true r2 ++ rtail rest))).
Proof.
  intros P b r1' g2' r2 rest.
  replace (S r1' + 2) with (2 + (r1' + 1)) by lia.
  rewrite run_split.
  assert (H2 : run 2 (rbsec P b ((1, S r1') :: (S g2', r2) :: rest)) =
    Some (mkCfg SA (false :: repeat true (S b) ++ P)
           (repeat true r1' ++
             (repeat false (S g2') ++ (repeat true r2 ++ rtail rest))))).
  { reflexivity. }
  rewrite H2. cbv beta iota.
  rewrite run_split.
  rewrite sweepA. cbv beta iota.
  reflexivity.
Qed.

Lemma RTUP : forall P b r1'' g2'' r2 rest,
  run (2 * S (S r1'') + 6)
    (rbsec P b ((1, S (S r1'')) :: (S (S (S g2'')), r2) :: rest)) =
  Some (rcsec P b ((S r1'', 2) :: (S g2'', r2) :: rest)).
Proof.
  intros P b r1'' g2'' r2 rest.
  replace (2 * S (S r1'') + 6) with ((S (S r1'') + 2) + (r1'' + 6))
    by lia.
  rewrite run_split.
  rewrite (rtup_prefix P b (S r1'') (S (S g2'')) r2 rest).
  assert (H4 : run 4
    (mkCfg SB (repeat true (S (S r1'')) ++
                (false :: repeat true (S b) ++ P))
       (repeat false (S (S g2'')) ++ (repeat true r2 ++ rtail rest))) =
    Some (mkCfg SF (repeat true r1'' ++
                      (false :: repeat true (S b) ++ P))
       (true :: true :: true :: false ::
         (repeat false g2'' ++ (repeat true r2 ++ rtail rest))))).
  { reflexivity. }
  replace (r1'' + 6) with (4 + (r1'' + 2)) by lia.
  rewrite run_split.
  rewrite H4. cbv beta iota.
  rewrite run_split.
  rewrite sweepF. cbv beta iota.
  reflexivity.
Qed.

(* ---------------------------------------------------------------- *)
(* RPROBE: B-form, k = 1 (r1 is the last run): as RTUP but the       *)
(* probe is in the blank beyond r1; span += 2.  Cost 2*r1 + 6.       *)
(* The landing carries one materialised trailing blank cell.         *)
(* ---------------------------------------------------------------- *)

Lemma rprobe_prefix : forall P b r1',
  run (S r1' + 1) (rbsec P b ((1, S r1') :: [])) =
  Some (mkCfg SA (repeat true r1' ++ (false :: repeat true (S b) ++ P))
                 []).
Proof.
  intros P b r1'.
  replace (S r1' + 1) with (2 + r1') by lia.
  rewrite run_split.
  assert (H2 : run 2 (rbsec P b ((1, S r1') :: [])) =
    Some (mkCfg SA (false :: repeat true (S b) ++ P)
           (repeat true r1' ++ []))).
  { reflexivity. }
  rewrite H2. cbv beta iota.
  rewrite sweepA. cbv beta iota.
  reflexivity.
Qed.

Definition rcsec_probe (P : list sym) (b : nat) (g : nat) : config :=
  mkCfg SC (repeat true b ++ P)
    (true :: true :: (repeat false g ++ [true; true; false])).

Lemma RPROBE : forall P b r1'',
  run (2 * S (S r1'') + 6) (rbsec P b ((1, S (S r1'')) :: [])) =
  Some (rcsec_probe P b (S r1'')).
Proof.
  intros P b r1''.
  replace (2 * S (S r1'') + 6) with ((S (S r1'') + 1) + (S r1'' + 6))
    by lia.
  rewrite run_split.
  rewrite (rprobe_prefix P b (S r1'')).
  assert (Hprobe : run 5
    (mkCfg SA (repeat true (S r1'') ++
                (false :: repeat true (S b) ++ P)) []) =
    Some (mkCfg SF (repeat true r1'' ++
                      (false :: repeat true (S b) ++ P))
           [true; true; true; false])).
  { rewrite probe_blank. reflexivity. }
  replace (S r1'' + 6) with (5 + (r1'' + 2)) by lia.
  rewrite run_split.
  rewrite Hprobe. cbv beta iota.
  rewrite run_split.
  rewrite sweepF. cbv beta iota.
  unfold rcsec_probe. reflexivity.
Qed.

Lemma nth_probe_rtail : forall g n,
  nth n (true :: true :: (repeat false g ++ [true; true; false])) false =
  nth n (true :: true :: (repeat false g ++ (repeat true 2 ++ []))) false.
Proof.
  intros g n. destruct n as [| [| i]]; try reflexivity.
  change (nth (S (S i))
            (true :: true :: (repeat false g ++ [true; true; false])) false)
    with (nth i (repeat false g ++ [true; true; false]) false).
  change (nth (S (S i))
            (true :: true :: (repeat false g ++ (repeat true 2 ++ []))) false)
    with (nth i (repeat false g ++ (repeat true 2 ++ [])) false).
  change (repeat true 2 ++ []) with [true; true].
  change [true; true; false] with ([true; true] ++ [false]).
  apply nth_app_false_gen.
Qed.

(* The RPROBE landing has the tape of the documents' C-section
   (beta + 2, pair (r1 - 1, 2), no further pairs). *)
Lemma RPROBE_tape : forall P b r1'' p,
  tape_of (rcsec_probe P b (S r1'')) p =
  tape_of (rcsec P b ((S r1'', 2) :: [])) p.
Proof.
  intros P b r1'' p. unfold tape_of, rcsec_probe, rcsec. cbn [rtail].
  destruct (Z_le_dec 0 p) as [_ | _]; [| reflexivity].
  apply nth_probe_rtail.
Qed.

(* ---------------------------------------------------------------- *)
(* The entry excursion (component #12, rightedge-derivation.md S1): *)
(* from sigma_entry(B2, s) = 1^17 0 1^B2 0^1 1^s 0^2 1^2 (head B on   *)
(* the g0 cell), the machine reaches sigma_re(B2, s) in exactly      *)
(* s + 12 steps: the first right-section, with beta = s + 2 and      *)
(* the single pair (1, 2).  The landing is stated in its exact       *)
(* computed form (one materialised trailing blank cell);             *)
(* ENTRY_tape identifies its tape with the clean right-section.     *)
(* ---------------------------------------------------------------- *)

Definition entry_src (B2 s : nat) : config :=
  mkCfg SB (repeat true B2 ++ (false :: repeat true 17))
    (false :: (repeat true s ++ (repeat false 2 ++ [true; true]))).

Definition entry_tgt (B2 s : nat) : config :=
  mkCfg SC (repeat true s ++
             (false :: repeat true (S B2) ++ (false :: repeat true 17)))
    [true; true; false; true; true; false].

Lemma entry_prefix : forall B2 s',
  run (S s' + 2) (entry_src B2 (S s')) =
  Some (mkCfg SB (repeat true (S s') ++
                   (false :: repeat true (S B2) ++
                             (false :: repeat true 17)))
                 [false; true; true]).
Proof.
  intros B2 s'.
  replace (S s' + 2) with (2 + (s' + 1)) by lia.
  rewrite run_split.
  assert (H2 : run 2 (entry_src B2 (S s')) =
    Some (mkCfg SA (false :: repeat true (S B2) ++
                             (false :: repeat true 17))
           (repeat true s' ++ [false; false; true; true]))).
  { reflexivity. }
  rewrite H2. cbv beta iota.
  rewrite run_split.
  rewrite sweepA. cbv beta iota.
  reflexivity.
Qed.

Lemma ENTRY : forall B2 s',
  run (S s' + 12) (entry_src B2 (S s')) = Some (entry_tgt B2 (S s')).
Proof.
  intros B2 s'.
  replace (S s' + 12) with ((S s' + 2) + 10) by lia.
  rewrite run_split.
  rewrite entry_prefix.
  set (P' := false :: repeat true (S B2) ++ (false :: repeat true 17)).
  assert (H3 : run 3
    (mkCfg SB (repeat true (S s') ++ P') [false; true; true]) =
    Some (mkCfg SA (true :: false :: true ::
                      (repeat true (S s') ++ P')) [])).
  { reflexivity. }
  assert (Hprobe : run 5
    (mkCfg SA (true :: false :: true ::
                 (repeat true (S s') ++ P')) []) =
    Some (mkCfg SF (false :: true :: (repeat true (S s') ++ P'))
           [true; true; true; false])).
  { rewrite probe_blank. reflexivity. }
  replace 10 with (3 + (5 + 2)) by lia.
  rewrite run_split.
  rewrite H3. cbv beta iota.
  rewrite run_split.
  rewrite Hprobe. cbv beta iota.
  unfold entry_tgt. reflexivity.
Qed.

Lemma ENTRY_tape : forall B2 s p,
  tape_of (entry_tgt B2 s) p =
  tape_of (rcsec (false :: repeat true (S B2) ++
                           (false :: repeat true 17))
                 s [(1, 2)]) p.
Proof.
  intros B2 s p. unfold tape_of, entry_tgt, rcsec. cbn [rtail].
  destruct (Z_le_dec 0 p) as [_ | _]; [| reflexivity].
  destruct (Z.to_nat p) as [| [| [| [| [| [| i]]]]]]; try reflexivity.
  destruct i; reflexivity.
Qed.

(* ============ Invariant RI: parity preservation (#13, bookkeeping) ====
   RI (rightedge-derivation.md section 3): in the mirror frame every
   pair has odd gap and even run, and beta >= 2.  Each rule preserves
   the parity condition on the pair list; the beta side conditions are
   read off the rule statements (RTDN keeps b2, RPUSH needs b2 >= 1 in
   the source encoding, RPOP raises b by 1, RTUP keeps b). *)

Definition RI_pairs (pairs : list (nat * nat)) : Prop :=
  Forall (fun p => Nat.Odd (fst p) /\ Nat.Even (snd p)) pairs.

Lemma RI_rtdn : forall r1' rest,
  RI_pairs ((1, S r1') :: rest) ->
  RI_pairs ((1, S (S (S r1'))) :: rest).
Proof.
  intros r1' rest H. inversion H as [| ? ? [Ho He] Hrest]; subst.
  constructor; [| exact Hrest].
  destruct He as [m Hm]. cbn [fst snd] in *. split.
  - exists 0. reflexivity.
  - exists (S m). lia.
Qed.

Lemma RI_rpush : forall g'' r1 rest,
  RI_pairs ((S (S (S g'')), r1) :: rest) ->
  RI_pairs ((1, 2) :: (S g'', r1) :: rest).
Proof.
  intros g'' r1 rest H. inversion H as [| ? ? [Ho He] Hrest]; subst.
  destruct Ho as [m Hm]. cbn [fst snd] in *.
  constructor; [split; [exists 0; reflexivity | exists 1; reflexivity] |].
  constructor; [| exact Hrest].
  split; [| exact He].
  exists (m - 1). cbn [fst snd]. lia.
Qed.

Lemma RI_rpop : forall r1' r2' rest,
  RI_pairs ((1, S r1') :: (1, S r2') :: rest) ->
  RI_pairs ((1, S r1' + S r2') :: rest).
Proof.
  intros r1' r2' rest H.
  inversion H as [| ? ? [Ho1 He1] H']; subst.
  inversion H' as [| ? ? [Ho2 He2] Hrest]; subst.
  destruct He1 as [m1 Hm1]. destruct He2 as [m2 Hm2].
  cbn [fst snd] in *. constructor; [| exact Hrest].
  split; [exists 0; reflexivity |].
  exists (m1 + m2). cbn [fst snd]. lia.
Qed.

Lemma RI_rtup : forall r1'' g2'' r2 rest,
  RI_pairs ((1, S (S r1'')) :: (S (S (S g2'')), r2) :: rest) ->
  RI_pairs ((S r1'', 2) :: (S g2'', r2) :: rest).
Proof.
  intros r1'' g2'' r2 rest H.
  inversion H as [| ? ? [Ho1 He1] H']; subst.
  inversion H' as [| ? ? [Ho2 He2] Hrest]; subst.
  destruct He1 as [m1 Hm1]. destruct Ho2 as [m2 Hm2].
  cbn [fst snd] in *. constructor.
  - split; [| exists 1; reflexivity].
    exists (m1 - 1). cbn [fst snd]. lia.
  - constructor; [| exact Hrest].
    split; [| exact He2].
    exists (m2 - 1). cbn [fst snd]. lia.
Qed.

Lemma RI_rprobe : forall r1'',
  RI_pairs ((1, S (S r1'')) :: []) ->
  RI_pairs ((S r1'', 2) :: []).
Proof.
  intros r1'' H.
  inversion H as [| ? ? [Ho1 He1] H']; subst.
  destruct He1 as [m1 Hm1]. cbn [fst snd] in *.
  constructor; [| constructor].
  split; [exists (m1 - 1); cbn [fst snd]; lia | exists 1; reflexivity].
Qed.
