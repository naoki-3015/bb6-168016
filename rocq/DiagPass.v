(* ================================================================= *)
(* Phase 30 -- DiagPass.v: the diagonal token pass (stage 2 of       *)
(* component #16), in general.                                       *)
(*                                                                   *)
(* Stage 2 (phase19-derivations.md S3.2, phase21 S6) is a second     *)
(* token pass, run on the diagonal: from the section                 *)
(*   S_{n+1}(n+2) = rcsec P n ((2n+3, 2) :: sfx)                     *)
(* the machine reaches the escape section                            *)
(*   rcsec P 0 ((3, 2) :: (1, 2)^n ++ sfx-pairs)                     *)
(* in exactly Tk n steps (Tk from TokenPass.v), for EVERY frozen     *)
(* prefix P and every odd gap suffix sfx.  The pass decomposes as    *)
(*   DESC(n) : an A-round (29), a Psi-orbit (the descent orbit,      *)
(*             cost bcost n), and a closing RPUSH (9), landing at    *)
(*             the first beta = 2 section W_n;                       *)
(*   WALK(i) : W_i -> W_{i-1} in Dk (i-1) steps (RTDN, an RPOP       *)
(*             chain, RTUP, and a nested descent DESC(i-1) at the    *)
(*             grown suffix), for i = n .. 1.                        *)
(* W_i is the beta = 2 section with gaps (1^i, 3, 1^{n-i}).          *)
(*                                                                   *)
(* The descent orbit D_k (B-starts from (k+1; (2k-1)) to             *)
(* (3; (1^{k-2}, 3)), cost bcost k -- the same recursion as          *)
(* TokenPass's bcost) is built by the orbit recursion                *)
(*   D_{k+1} = T1(D_k) ++ join ++ T2(D_k),                           *)
(*   T1(beta; w) = (beta + 1; last gap + 2),                         *)
(*   T2(beta; w) = (beta; last gap - 2, then a new gap 3 appended),  *)
(* verified numerically for k <= 9 against the Python word model     *)
(* (phase17_model.py / phase19_stage2.py) before formalisation.      *)
(* The T2 transport is the one place needing a source invariant:     *)
(* psi_step commutes with T2 at every word w satisfying wok w        *)
(* (all gaps odd, lo w < length w, last gap >= 3, and the front      *)
(* of w is not all ones unless the last gap is >= 5); the bad case   *)
(* (front all ones, last gap 3) occurs in the descent orbits only    *)
(* as the final word, never as a step source.  fchain is the         *)
(* borbit analogue carrying wok at every source.                     *)
(* ================================================================= *)

Require Import List Bool Arith Lia ZArith.
Import ListNotations.
Require Import TM Sections Mirror TokenPass.

(* ================================================================ *)
(* Part 1: the T2 word map F2, front/last projections, and wok.      *)
(* ================================================================ *)

Definition frontw (w : list nat) : list nat :=
  match rev w with
  | [] => []
  | _ :: t => rev t
  end.

Definition lastw (w : list nat) : nat :=
  match rev w with
  | [] => 0
  | y :: _ => y
  end.

(* F2 (xs ++ [y]) = xs ++ ((y - 2) :: [3]): last gap - 2, gap 3 appended. *)
Definition F2 (w : list nat) : list nat :=
  match rev w with
  | [] => []
  | y :: t => rev (3 :: (y - 2) :: t)
  end.

Lemma frontw_app : forall xs y, frontw (xs ++ [y]) = xs.
Proof.
  intros xs y. unfold frontw. rewrite rev_unit. apply rev_involutive.
Qed.

Lemma lastw_app : forall xs y, lastw (xs ++ [y]) = y.
Proof.
  intros xs y. unfold lastw. rewrite rev_unit. reflexivity.
Qed.

Lemma F2_app : forall xs y, F2 (xs ++ [y]) = xs ++ ((y - 2) :: [3]).
Proof.
  intros xs y. unfold F2. rewrite rev_unit.
  replace (3 :: (y - 2) :: rev xs) with ((3 :: [y - 2]) ++ rev xs)
    by reflexivity.
  rewrite rev_app_distr, rev_involutive. reflexivity.
Qed.

Lemma length_F2_app : forall xs y,
  length (F2 (xs ++ [y])) = S (length (xs ++ [y])).
Proof.
  intros xs y. rewrite F2_app, !app_length. simpl. lia.
Qed.

Lemma frontw_F2_app : forall xs y,
  frontw (F2 (xs ++ [y])) = xs ++ [y - 2].
Proof.
  intros xs y. rewrite F2_app.
  replace (xs ++ ((y - 2) :: [3])) with ((xs ++ [y - 2]) ++ [3])
    by (rewrite <- app_assoc; reflexivity).
  apply frontw_app.
Qed.

Lemma lastw_F2_app : forall xs y, lastw (F2 (xs ++ [y])) = 3.
Proof.
  intros xs y. rewrite F2_app.
  replace (xs ++ ((y - 2) :: [3])) with ((xs ++ [y - 2]) ++ [3])
    by (rewrite <- app_assoc; reflexivity).
  apply lastw_app.
Qed.

Lemma frontw_last2f_app : forall xs y,
  frontw (last2f (xs ++ [y])) = xs.
Proof.
  intros xs y. rewrite last2f_app. apply frontw_app.
Qed.

Lemma lastw_last2f_app : forall xs y,
  lastw (last2f (xs ++ [y])) = y + 2.
Proof.
  intros xs y. rewrite last2f_app. apply lastw_app.
Qed.

Lemma length_last2f_app : forall xs y,
  length (last2f (xs ++ [y])) = length (xs ++ [y]).
Proof.
  intros xs y. rewrite last2f_app, !app_length. reflexivity.
Qed.

(* The T2 source invariant. *)
Definition wok (w : list nat) : Prop :=
  Jg w /\ lo w < length w /\ 3 <= lastw w /\
  (lo (frontw w) < length (frontw w) \/ 5 <= lastw w).

Lemma Jg_last_elem : forall xs y, Jg (xs ++ [y]) -> Nat.Odd y.
Proof.
  intros xs y HJg. unfold Jg in HJg. rewrite Forall_forall in HJg.
  apply HJg. apply in_or_app. right. simpl. auto.
Qed.

Lemma Jg_F2 : forall xs y, Jg (xs ++ [y]) -> 3 <= y ->
  Jg (F2 (xs ++ [y])).
Proof.
  intros xs y HJg Hy.
  assert (HOdd : Nat.Odd y) by (eapply Jg_last_elem; exact HJg).
  destruct (Jg_app_inv xs [y] HJg) as [HJgx _].
  rewrite F2_app. apply Jg_app_intro; [exact HJgx |].
  repeat constructor.
  - destruct HOdd as [m Hm]. exists (m - 1). lia.
  - exists 1. reflexivity.
Qed.

Lemma Jg_last2f : forall xs y, Jg (xs ++ [y]) ->
  Jg (last2f (xs ++ [y])).
Proof.
  intros xs y HJg.
  assert (HOdd : Nat.Odd y) by (eapply Jg_last_elem; exact HJg).
  destruct (Jg_app_inv xs [y] HJg) as [HJgx _].
  rewrite last2f_app. apply Jg_app_intro; [exact HJgx |].
  repeat constructor. destruct HOdd as [m Hm]. exists (S m). lia.
Qed.

Lemma lo_F2 : forall xs y, wok (xs ++ [y]) -> lo (F2 (xs ++ [y])) = lo (xs ++ [y]).
Proof.
  intros xs y Hw. destruct Hw as [HJg [Hlo [Hlast Hfront]]].
  rewrite lastw_app in Hlast. rewrite frontw_app in Hfront. rewrite lastw_app in Hfront.
  destruct (lt_eq_lt_dec (lo xs) (length xs)) as [[Hc | Hc] | Hc].
  - (* front not all ones *)
    rewrite F2_app.
    replace (xs ++ ((y - 2) :: [3])) with ((xs ++ [y - 2]) ++ [3])
      by (rewrite <- app_assoc; reflexivity).
    rewrite (lo_app_front (xs ++ [y - 2]) [3]).
    2: { rewrite (lo_app_front xs [y - 2]) by exact Hc.
         rewrite app_length. simpl. lia. }
    rewrite (lo_app_front xs [y - 2]) by exact Hc.
    rewrite (lo_app_front xs [y]) by exact Hc. reflexivity.
  - (* front all ones: then 5 <= y *)
    assert (Hrep : xs = repeat 1 (length xs)).
    { pose proof (lo_firstn xs) as Hf. rewrite Hc, firstn_all in Hf.
      exact Hf. }
    assert (Hy5 : 5 <= y).
    { destruct Hfront as [Hf | Hf]; [| exact Hf].
      rewrite Hc in Hf. lia. }
    rewrite F2_app.
    replace (xs ++ ((y - 2) :: [3])) with ((xs ++ [y - 2]) ++ [3])
      by (rewrite <- app_assoc; reflexivity).
    rewrite (lo_app_front (xs ++ [y - 2]) [3]).
    2: { rewrite (lo_app_ones xs (y - 2) Hrep) by lia.
         rewrite app_length. simpl. lia. }
    rewrite (lo_app_ones xs (y - 2) Hrep) by lia.
    rewrite (lo_app_ones xs y Hrep) by lia. reflexivity.
  - pose proof (lo_le_length xs). lia.
Qed.

Lemma wok_F2 : forall w, wok w -> wok (F2 w).
Proof.
  intros w Hw.
  destruct w as [| a w']; [destruct Hw as [_ [Hlo _]]; simpl in Hlo; lia |].
  destruct (list_decomp_last (a :: w') ltac:(discriminate))
    as [xs [y Hw']]. rewrite Hw' in Hw |- *.
  pose proof Hw as Hw0.
  destruct Hw as [HJg [Hlo [Hlast Hfront]]].
  rewrite lastw_app in Hlast. rewrite frontw_app in Hfront. rewrite lastw_app in Hfront.
  unfold wok.
  split; [eapply Jg_F2; eassumption |].
  split.
  { rewrite (lo_F2 xs y Hw0). rewrite length_F2_app. lia. }
  split; [rewrite lastw_F2_app; lia |].
  left. rewrite frontw_F2_app.
  destruct (lt_eq_lt_dec (lo xs) (length xs)) as [[Hc | Hc] | Hc].
  - rewrite (lo_app_front xs [y - 2]) by exact Hc.
    rewrite app_length. simpl. lia.
  - rewrite (lo_app_ones xs (y - 2)).
    + rewrite app_length. simpl. lia.
    + pose proof (lo_firstn xs) as Hf. rewrite Hc, firstn_all in Hf.
      exact Hf.
    + destruct Hfront as [Hf | Hf]; [rewrite Hc in Hf; lia | lia].
  - pose proof (lo_le_length xs). lia.
Qed.

Lemma wok_last2f : forall w, wok w -> wok (last2f w).
Proof.
  intros w Hw.
  destruct w as [| a w']; [destruct Hw as [_ [Hlo _]]; simpl in Hlo; lia |].
  destruct (list_decomp_last (a :: w') ltac:(discriminate))
    as [xs [y Hw']]. rewrite Hw' in Hw |- *.
  destruct Hw as [HJg [Hlo [Hlast Hfront]]].
  rewrite lastw_app in Hlast. rewrite frontw_app in Hfront. rewrite lastw_app in Hfront.
  unfold wok.
  split; [eapply Jg_last2f; exact HJg |].
  split.
  { rewrite (length_last2f_app xs y).
    rewrite (lo_last2f (xs ++ [y]) Hlo). exact Hlo. }
  split; [rewrite lastw_last2f_app; lia |].
  rewrite frontw_last2f_app, lastw_last2f_app.
  destruct Hfront as [Hf | Hf]; [left; exact Hf | right; lia].
Qed.

(* ================================================================ *)
(* Part 2: psi_step transports for the descent recursion.            *)
(* ================================================================ *)

Lemma skipn_app2 : forall (xs ys : list nat) n, length xs <= n ->
  skipn n (xs ++ ys) = skipn (n - length xs) ys.
Proof.
  induction xs as [| a xs IH]; intros ys n Hn.
  - simpl. rewrite Nat.sub_0_r. reflexivity.
  - destruct n as [| n']; [simpl in Hn; lia |].
    simpl. rewrite IH by (simpl in Hn; lia). reflexivity.
Qed.

(* Psi steps are invariant under a uniform +1 shift of the block. *)
Lemma psi_step_shift : forall P b2 xs b2' xs',
  psi_step P b2 xs b2' xs' -> psi_step P (S b2) xs (S b2') xs'.
Proof.
  intros P b2 xs b2' xs' Hstep.
  pose proof (psi_step_Sform P b2 xs b2' xs' Hstep) as HSf.
  destruct Hstep as [HJg [Hlo [Hxs' [Hb2' Hrun]]]].
  unfold psi_step.
  split; [exact HJg |]. split; [exact Hlo |]. split; [exact Hxs' |].
  split; [lia |].
  pose proof (psi_run_gen P (S b2) xs [] HJg Hlo) as Hgen.
  rewrite !app_nil_r in Hgen. rewrite <- Hxs' in Hgen.
  replace (S b2 + lo xs) with (S (S b2')) in Hgen by lia.
  exact Hgen.
Qed.

(* T1 transport: last gap + 2 and block + 1. *)
Lemma psi_step_last2f_up : forall P b2 w b2' w',
  psi_step P b2 w b2' w' ->
  psi_step P (S b2) (last2f w) (S b2') (last2f w').
Proof.
  intros P b2 w b2' w' Hstep.
  apply psi_step_shift. apply psi_step_last2f. exact Hstep.
Qed.

Lemma wpsi_app_ones : forall xs y,
  xs = repeat 1 (length xs) -> y <> 1 ->
  wpsi (xs ++ [y]) = (1 + 2 * length xs) :: [y - 2].
Proof.
  intros xs y Hrep Hy. unfold wpsi.
  rewrite (lo_app_ones xs y Hrep Hy).
  replace (nth (length xs) (xs ++ [y]) 0) with y.
  2: { rewrite app_nth2 by lia. rewrite Nat.sub_diag. reflexivity. }
  replace (skipn (S (length xs)) (xs ++ [y])) with (@nil nat).
  2: { symmetry. apply skipn_all2. rewrite app_length. simpl. lia. }
  reflexivity.
Qed.

Lemma wpsi_F2_ones : forall xs y,
  xs = repeat 1 (length xs) -> 5 <= y ->
  wpsi (F2 (xs ++ [y])) =
  (1 + 2 * length xs) :: ((y - 2 - 2) :: [3]).
Proof.
  intros xs y Hrep Hy. rewrite F2_app.
  assert (HloF : lo (xs ++ ((y - 2) :: [3])) = length xs).
  { replace (xs ++ ((y - 2) :: [3])) with ((xs ++ [y - 2]) ++ [3])
      by (rewrite <- app_assoc; reflexivity).
    rewrite (lo_app_front (xs ++ [y - 2]) [3]).
    - apply (lo_app_ones xs (y - 2) Hrep). lia.
    - rewrite (lo_app_ones xs (y - 2) Hrep) by lia.
      rewrite app_length. simpl. lia. }
  assert (Hnth : nth (length xs) (xs ++ ((y - 2) :: [3])) 0 = y - 2).
  { rewrite app_nth2 by lia. rewrite Nat.sub_diag. reflexivity. }
  assert (Hskip : skipn (S (length xs)) (xs ++ ((y - 2) :: [3])) = [3]).
  { rewrite skipn_app2 by lia.
    replace (S (length xs) - length xs) with 1 by lia. reflexivity. }
  unfold wpsi. rewrite HloF, Hnth, Hskip. reflexivity.
Qed.

(* T2 transport: last gap - 2 with a gap 3 appended; needs wok. *)
Lemma psi_step_F2 : forall P b2 w b2' w',
  psi_step P b2 w b2' w' -> wok w -> psi_step P b2 (F2 w) b2' (F2 w').
Proof.
  intros P b2 w b2' w' Hstep Hwok.
  pose proof (psi_step_Sform P b2 w b2' w' Hstep) as HSf.
  destruct w as [| a w0];
    [destruct Hstep as [_ [Hlo _]]; simpl in Hlo; lia |].
  destruct (list_decomp_last (a :: w0) ltac:(discriminate))
    as [xs [y Hw']].
  rewrite Hw' in Hstep, Hwok, HSf. rewrite Hw'.
  destruct Hstep as [HJg [Hlo [Hw'eq [Hb2' Hrun]]]].
  destruct Hwok as [HJg2 [Hlo2 [Hlast Hfront]]].
  rewrite lastw_app in Hlast. rewrite frontw_app in Hfront.
  rewrite lastw_app in Hfront.
  assert (HJgF : Jg (F2 (xs ++ [y]))).
  { eapply Jg_F2; eassumption. }
  assert (Hwok' : wok (xs ++ [y])).
  { unfold wok. rewrite lastw_app, frontw_app.
    split; [exact HJg2 |]. split; [exact Hlo2 |].
    split; [exact Hlast | exact Hfront]. }
  assert (HloF : lo (F2 (xs ++ [y])) < length (F2 (xs ++ [y]))).
  { rewrite (lo_F2 xs y Hwok'), length_F2_app. lia. }
  assert (Hword : F2 w' = wpsi (F2 (xs ++ [y]))).
  { rewrite Hw'eq.
    destruct (lt_eq_lt_dec (lo xs) (length xs)) as [[Hc | Hc] | Hc].
    - (* front not all ones *)
      rewrite (wpsi_app_front xs [y]) by exact Hc.
      rewrite F2_app.
      replace (wpsi xs ++ ((y - 2) :: [3]))
        with ((wpsi xs ++ [y - 2]) ++ [3])
        by (rewrite <- app_assoc; reflexivity).
      rewrite F2_app.
      replace (xs ++ ((y - 2) :: [3])) with ((xs ++ [y - 2]) ++ [3])
        by (rewrite <- app_assoc; reflexivity).
      rewrite (wpsi_app_front (xs ++ [y - 2]) [3]).
      + rewrite (wpsi_app_front xs [y - 2]) by exact Hc.
        rewrite <- app_assoc. reflexivity.
      + rewrite (lo_app_front xs [y - 2]) by exact Hc.
        rewrite app_length. simpl. lia.
    - (* front all ones *)
      assert (Hrep : xs = repeat 1 (length xs)).
      { pose proof (lo_firstn xs) as Hf. rewrite Hc, firstn_all in Hf.
        exact Hf. }
      assert (Hy5 : 5 <= y).
      { destruct Hfront as [Hf | Hf]; [| exact Hf].
        rewrite Hc in Hf. lia. }
      rewrite (wpsi_app_ones xs y Hrep) by lia.
      replace ((1 + 2 * length xs) :: [y - 2])
        with ([1 + 2 * length xs] ++ [y - 2]) by reflexivity.
      rewrite F2_app.
      rewrite (wpsi_F2_ones xs y Hrep Hy5). reflexivity.
    - pose proof (lo_le_length xs). lia. }
  unfold psi_step.
  split; [exact HJgF |]. split; [exact HloF |].
  split; [exact Hword |]. split.
  { rewrite (lo_F2 xs y Hwok'). exact Hb2'. }
  pose proof (psi_run_gen P b2 (F2 (xs ++ [y])) [] HJgF HloF) as Hgen.
  rewrite !app_nil_r in Hgen.
  rewrite (lo_F2 xs y Hwok') in Hgen.
  rewrite <- Hword in Hgen.
  rewrite <- HSf in Hgen.
  rewrite (lo_F2 xs y Hwok'). exact Hgen.
Qed.

(* ================================================================ *)
(* Part 3: fchain -- Psi chains carrying wok at every source.        *)
(* ================================================================ *)

Inductive fchain (P : list sym) :
    nat -> list nat -> nat -> list nat -> nat -> Prop :=
| fchain_refl : forall b2 xs, fchain P b2 xs b2 xs 0
| fchain_step : forall b2 xs b2' xs' b2'' xs'' c',
    psi_step P b2 xs b2' xs' -> wok xs ->
    fchain P b2' xs' b2'' xs'' c' ->
    fchain P b2 xs b2'' xs'' (psicost (lo xs) + c').

Lemma fchain_borbit : forall P b2 xs b2' xs' c,
  fchain P b2 xs b2' xs' c -> borbit P 0 b2 xs b2' xs' c.
Proof.
  intros P b2 xs b2' xs' c H. induction H.
  - apply borbit_refl. lia.
  - eapply borbit_step; eauto; lia.
Qed.

Lemma fchain_trans : forall P b2 xs b2' xs' b2'' xs'' c1 c2,
  fchain P b2 xs b2' xs' c1 ->
  fchain P b2' xs' b2'' xs'' c2 ->
  fchain P b2 xs b2'' xs'' (c1 + c2).
Proof.
  intros P b2 xs b2' xs' b2'' xs'' c1 c2 H1 H2.
  induction H1.
  - exact H2.
  - replace ((psicost (lo xs) + c') + c2)
      with (psicost (lo xs) + (c' + c2)) by lia.
    eapply fchain_step; eauto.
Qed.

Lemma fchain_last2f_up : forall P b2 xs b2' xs' c,
  fchain P b2 xs b2' xs' c ->
  fchain P (S b2) (last2f xs) (S b2') (last2f xs') c.
Proof.
  intros P b2 xs b2' xs' c H. induction H.
  - apply fchain_refl.
  - assert (Hlo2 : lo (last2f xs) = lo xs).
    { apply lo_last2f. destruct H as [_ [Hlo _]]. exact Hlo. }
    rewrite <- Hlo2.
    eapply fchain_step.
    + apply psi_step_last2f_up. exact H.
    + apply wok_last2f. exact H0.
    + exact IHfchain.
Qed.

Lemma fchain_F2 : forall P b2 xs b2' xs' c,
  fchain P b2 xs b2' xs' c ->
  fchain P b2 (F2 xs) b2' (F2 xs') c.
Proof.
  intros P b2 xs b2' xs' c H. induction H.
  - apply fchain_refl.
  - assert (HloF : lo (F2 xs) = lo xs).
    { destruct xs as [| a xs0];
        [destruct H as [_ [Hlo _]]; simpl in Hlo; lia |].
      destruct (list_decomp_last (a :: xs0) ltac:(discriminate))
        as [xs1 [y Hx]].
      rewrite Hx in H0 |- *. apply (lo_F2 xs1 y H0). }
    rewrite <- HloF.
    eapply fchain_step.
    + eapply psi_step_F2; eassumption.
    + apply wok_F2. exact H0.
    + exact IHfchain.
Qed.

(* ================================================================ *)
(* Part 4: the descent orbit recursion.                              *)
(* D_{2+j}: B-starts from (j; [2j+3]) to (0; 1^j ++ [3]),             *)
(* total Psi cost bcost (2 + j) -- the TokenPass bcost recursion.    *)
(* ================================================================ *)

Lemma dorbit_cycle : forall P j,
  fchain P j ((2 * j + 3) :: []) 0 (repeat 1 j ++ [3]) (bcost (2 + j)).
Proof.
  intros P j. induction j.
  - apply fchain_refl.
  - (* T1 replay *)
    pose proof (fchain_last2f_up P j ((2 * j + 3) :: []) 0
                  (repeat 1 j ++ [3]) (bcost (2 + j)) IHj) as HT1.
    replace (last2f ((2 * j + 3) :: [])) with ((2 * S j + 3) :: [])
      in HT1.
    2: { replace ((2 * j + 3) :: []) with ([] ++ [2 * j + 3])
           by reflexivity.
         rewrite last2f_app.
         replace (2 * j + 3 + 2) with (2 * S j + 3) by lia.
         reflexivity. }
    replace (last2f (repeat 1 j ++ [3])) with (repeat 1 j ++ [5])
      in HT1 by (rewrite last2f_app; reflexivity).
    replace (S 0) with 1 in HT1 by reflexivity.
    (* the join step *)
    assert (HJg : Jg (repeat 1 j ++ [5])).
    { apply Jg_app_intro; [apply Jg_repeat1 |].
      repeat constructor. exists 2. reflexivity. }
    assert (Hlo : lo (repeat 1 j ++ [5]) < length (repeat 1 j ++ [5])).
    { rewrite (lo_repeat_app j 5 []) by discriminate.
      rewrite app_length, repeat_length. simpl. lia. }
    assert (Hwok : wok (repeat 1 j ++ [5])).
    { unfold wok. split; [exact HJg |].
      split; [exact Hlo |].
      split; [rewrite lastw_app; lia |].
      right. rewrite lastw_app. lia. }
    pose proof (PSI_RUN P 1 (repeat 1 j ++ [5]) HJg Hlo
                  ltac:(rewrite (lo_repeat_app j 5 []) by discriminate;
                        lia)) as Hjoin.
    rewrite (lo_repeat_app j 5 []) in Hjoin by discriminate.
    replace (1 + j - 1) with j in Hjoin by lia.
    replace (wpsi (repeat 1 j ++ [5])) with ((1 + 2 * j) :: [3])
      in Hjoin.
    2: { unfold wpsi.
         rewrite (lo_repeat_app j 5 []) by discriminate.
         replace (nth j (repeat 1 j ++ [5]) 0) with 5.
         2: { rewrite app_nth2 by (rewrite repeat_length; lia).
              rewrite repeat_length, Nat.sub_diag. reflexivity. }
         replace (skipn (S j) (repeat 1 j ++ [5])) with (@nil nat).
         2: { symmetry. apply skipn_all2. rewrite app_length,
                repeat_length. simpl. lia. }
         reflexivity. }
    (* T2 replay *)
    pose proof (fchain_F2 P j ((2 * j + 3) :: []) 0
                  (repeat 1 j ++ [3]) (bcost (2 + j)) IHj) as HT2.
    replace (F2 ((2 * j + 3) :: [])) with ((1 + 2 * j) :: [3]) in HT2.
    2: { replace ((2 * j + 3) :: []) with ([] ++ [2 * j + 3])
           by reflexivity.
         rewrite F2_app.
         replace (2 * j + 3 - 2) with (1 + 2 * j) by lia.
         reflexivity. }
    replace (F2 (repeat 1 j ++ [3])) with (repeat 1 (S j) ++ [3])
      in HT2.
    2: { rewrite F2_app.
         replace (repeat 1 j ++ ((3 - 2) :: [3]))
           with (repeat 1 (S j) ++ [3]).
         - reflexivity.
         - replace (3 - 2) with 1 by reflexivity.
           replace (repeat 1 j ++ (1 :: [3]))
             with ((repeat 1 j ++ [1]) ++ [3])
             by (rewrite <- app_assoc; reflexivity).
           rewrite repeat_snoc. reflexivity. }
    (* compose *)
    pose proof (fchain_step P 1 (repeat 1 j ++ [5]) j
                  ((1 + 2 * j) :: [3]) 0 (repeat 1 (S j) ++ [3])
                  (bcost (2 + j)) Hjoin Hwok HT2) as Hmid.
    rewrite (lo_repeat_app j 5 []) in Hmid by discriminate.
    pose proof (fchain_trans P (S j) ((2 * S j + 3) :: []) 1
                  (repeat 1 j ++ [5]) 0 (repeat 1 (S j) ++ [3])
                  (bcost (2 + j)) (psicost j + bcost (2 + j))
                  HT1 Hmid) as Htot.
    replace (bcost (2 + j) + (psicost j + bcost (2 + j)))
      with (bcost (2 + S j)) in Htot.
    2: { assert (bcost (2 + S j) = 2 * bcost (2 + j) + psicost j)
           by reflexivity. lia. }
    exact Htot.
Qed.

(* ================================================================ *)
(* Part 5: the descent DESC with an arbitrary odd gap suffix.        *)
(* ================================================================ *)

Lemma psi_step_front_list : forall (P : list sym) b2 xs b2' xs'
    (sfx : list nat),
  Forall Nat.Odd sfx -> psi_step P b2 xs b2' xs' ->
  psi_step P b2 (xs ++ sfx) b2' (xs' ++ sfx).
Proof.
  intros P b2 xs b2' xs' sfx. revert b2 xs b2' xs'.
  induction sfx as [| y sfx IH]; intros b2 xs b2' xs' Hf Hstep.
  - rewrite !app_nil_r. exact Hstep.
  - inversion Hf as [| ? ? HOdd Hf']; subst.
    replace (xs ++ (y :: sfx)) with ((xs ++ [y]) ++ sfx)
      by (rewrite <- app_assoc; reflexivity).
    replace (xs' ++ (y :: sfx)) with ((xs' ++ [y]) ++ sfx)
      by (rewrite <- app_assoc; reflexivity).
    eapply IH; [exact Hf' |].
    eapply psi_step_front; eassumption.
Qed.

(* DESC(k): S_{k+1}(k+2) with suffix sfx reaches W_k with suffix
   sfx, in bcost k + 38 steps (A-round 29, orbit bcost k, RPUSH 9). *)
Lemma DESC : forall P k sfx, 2 <= k -> Forall Nat.Odd sfx ->
  exists c, run (bcost k + 38)
    (rcsec P k ((2 * k + 3, 2) :: gpairs sfx)) = Some c /\
  cfg_sim c (rcsec P 0 (gpairs (repeat 1 k ++ [3]) ++ gpairs sfx)).
Proof.
  intros P k sfx Hk Hsfx.
  (* the A-round *)
  pose proof (ROUND_A P (k - 1) (2 * k - 2) (gpairs sfx)) as HA.
  replace (S (k - 1)) with k in HA by lia.
  replace (S (S (S (S (S (2 * k - 2)))))) with (2 * k + 3) in HA
    by lia.
  replace (S (2 * k - 2)) with (2 * k - 1) in HA by lia.
  (* the descent orbit, suffix appended *)
  pose proof (dorbit_cycle P (k - 2)) as Hch.
  replace (2 + (k - 2)) with k in Hch by lia.
  replace (2 * (k - 2) + 3) with (2 * k - 1) in Hch by lia.
  pose proof (fchain_borbit P (k - 2) ((2 * k - 1) :: []) 0
                (repeat 1 (k - 2) ++ [3]) (bcost k) Hch) as Horb.
  pose proof (borbit_map (fun w => w ++ sfx) P 0
                (fun w Hw => lo_app_front w sfx Hw)
                (fun b2 w b2' w' H =>
                   psi_step_front_list P b2 w b2' w' sfx Hsfx H)
                (k - 2) ((2 * k - 1) :: []) 0
                (repeat 1 (k - 2) ++ [3]) (bcost k) Horb) as HorbS.
  cbv beta in HorbS.
  replace (((2 * k - 1) :: []) ++ sfx) with ((2 * k - 1) :: sfx)
    in HorbS by reflexivity.
  pose proof (borbit_run P 0 (k - 2) ((2 * k - 1) :: sfx) 0
                ((repeat 1 (k - 2) ++ [3]) ++ sfx) (bcost k) HorbS)
    as Hrun.
  replace (S (k - 2)) with (k - 1) in Hrun by lia.
  replace (gpairs ((2 * k - 1) :: sfx))
    with ((2 * k - 1, 2) :: gpairs sfx) in Hrun by reflexivity.
  rewrite gpairs_app in Hrun.
  rewrite gpairs_app in Hrun.
  rewrite gpairs_repeat1 in Hrun.
  replace (gpairs [3]) with [(3, 2)] in Hrun by reflexivity.
  rewrite <- app_assoc in Hrun.
  (* the closing RPUSH *)
  pose proof (PHASE_second P 0 0
                (repeat (1, 2) (k - 2) ++ [(3, 2)] ++ gpairs sfx))
    as Hclose.
  (* assemble *)
  exists (rcsec P 0 ((1, 2) :: (1, 2) ::
             (repeat (1, 2) (k - 2) ++ [(3, 2)] ++ gpairs sfx))).
  split.
  - replace (bcost k + 38) with (29 + (bcost k + 9)) by lia.
    rewrite run_split. rewrite HA.
    rewrite run_split. rewrite Hrun. exact Hclose.
  - assert (Hpair : gpairs (repeat 1 k ++ [3]) ++ gpairs sfx =
      (1, 2) :: (1, 2) ::
        (repeat (1, 2) (k - 2) ++ [(3, 2)] ++ gpairs sfx)).
    { rewrite gpairs_app, gpairs_repeat1.
      replace (gpairs [3]) with [(3, 2)] by reflexivity.
      replace (repeat (1, 2) k) with (repeat (1, 2) (S (S (k - 2))))
        by (f_equal; lia).
      rewrite app_assoc. reflexivity. }
    rewrite Hpair. apply cfg_sim_refl.
Qed.

(* ================================================================ *)
(* Part 6: the RPOP chain of the walk, with a general tail.          *)
(* ================================================================ *)

Lemma rpop_chain : forall P b j r' tail,
  run (2 * S r' * j + 2 * j * j + j)
    (rbsec P b ((1, S r') :: (repeat (1, 2) j ++ tail))) =
  Some (rbsec P (b + j) ((1, S r' + 2 * j) :: tail)).
Proof.
  intros P b j. revert b. induction j as [| j IH]; intros b r' tail.
  - replace (2 * S r' * 0 + 2 * 0 * 0 + 0) with 0 by lia.
    replace (b + 0) with b by lia.
    replace (S r' + 2 * 0) with (S r') by lia. reflexivity.
  - replace (2 * S r' * S j + 2 * S j * S j + S j)
      with ((2 * S r' + 3) +
            (2 * S (S (S r')) * j + 2 * j * j + j)) by nia.
    rewrite run_split.
    assert (Hrep : repeat (1, 2) (S j) ++ tail =
      (1, 2) :: (repeat (1, 2) j ++ tail)) by reflexivity.
    rewrite Hrep.
    rewrite (RPOP P b r' 1 (repeat (1, 2) j ++ tail)).
    replace (S r' + S 1) with (S (S (S r'))) by lia.
    replace (b + S j) with (S b + j) by lia.
    replace (S r' + 2 * S j) with (S (S (S r')) + 2 * j) by lia.
    apply IH.
Qed.

(* ================================================================ *)
(* Part 7: the walk W_i -> W_{i-1} and its iteration.                *)
(* ================================================================ *)

(* WALK: from the beta = 2 section with gaps (1^i, 3) ++ sg to the
   one with gaps (1^(i-1), 3, 1) ++ sg, in Dk (i-1) steps. *)
Lemma WALK : forall P i sg, 1 <= i -> Forall Nat.Odd sg ->
  exists c, run (Dk (i - 1))
    (rcsec P 0 (gpairs (repeat 1 i ++ [3] ++ sg))) = Some c /\
  cfg_sim c (rcsec P 0 (gpairs (repeat 1 (i - 1) ++ [3] ++ (1 :: sg)))).
Proof.
  intros P i sg Hi Hsg. destruct i as [| i']; [lia |].
  replace (S i' - 1) with i' by lia.
  (* RTDN *)
  assert (H1 : run 6 (rcsec P 0 (gpairs (repeat 1 (S i') ++ [3] ++ sg))) =
    Some (rbsec P 0 ((1, 4) :: gpairs (repeat 1 i' ++ [3] ++ sg)))).
  { replace (gpairs (repeat 1 (S i') ++ [3] ++ sg))
      with ((1, 2) :: gpairs (repeat 1 i' ++ [3] ++ sg))
      by reflexivity.
    exact (RTDN P 0 1 (gpairs (repeat 1 i' ++ [3] ++ sg))). }
  (* RPOP chain *)
  assert (Hgp : gpairs (repeat 1 i' ++ [3] ++ sg) =
    repeat (1, 2) i' ++ ((3, 2) :: gpairs sg)).
  { rewrite gpairs_app, gpairs_app, gpairs_repeat1. reflexivity. }
  assert (H2 : run (2 * S 3 * i' + 2 * i' * i' + i')
    (rbsec P 0 ((1, 4) :: gpairs (repeat 1 i' ++ [3] ++ sg))) =
    Some (rbsec P i' ((1, 2 * i' + 4) :: (3, 2) :: gpairs sg))).
  { rewrite Hgp.
    replace (1, 4) with (1, S 3) by reflexivity.
    pose proof (rpop_chain P 0 i' 3 ((3, 2) :: gpairs sg)) as Hc.
    replace (0 + i') with i' in Hc by lia.
    replace (S 3 + 2 * i') with (2 * i' + 4) in Hc by lia.
    exact Hc. }
  (* RTUP *)
  assert (H3 : run (2 * S (S (2 * S i')) + 6)
    (rbsec P i' ((1, 2 * i' + 4) :: (3, 2) :: gpairs sg)) =
    Some (rcsec P i' ((2 * i' + 3, 2) :: (1, 2) :: gpairs sg))).
  { replace (2 * i' + 4) with (S (S (2 * S i'))) by lia.
    replace (2 * i' + 3) with (S (2 * S i')) by lia.
    replace ((3, 2) :: gpairs sg)
      with ((S (S (S 0)), 2) :: gpairs sg) by reflexivity.
    replace ((1, 2) :: gpairs sg)
      with ((S 0, 2) :: gpairs sg) by reflexivity.
    exact (RTUP P i' (2 * S i') 0 2 (gpairs sg)). }
  (* the prefix composition *)
  assert (Hpre : run (2 * i' * i' + 13 * i' + 20)
    (rcsec P 0 (gpairs (repeat 1 (S i') ++ [3] ++ sg))) =
    Some (rcsec P i' ((2 * i' + 3, 2) :: (1, 2) :: gpairs sg))).
  { replace (2 * i' * i' + 13 * i' + 20)
      with (6 + ((2 * S 3 * i' + 2 * i' * i' + i') +
                 (2 * S (S (2 * S i')) + 6))) by nia.
    rewrite run_split. rewrite H1.
    rewrite run_split. rewrite H2. exact H3. }
  destruct i' as [| [| i'']].
  - (* i = 1: RTUP already landed on W_0 *)
    exists (rcsec P 0 ((2 * 0 + 3, 2) :: (1, 2) :: gpairs sg)).
    split.
    + replace (Dk 0) with (2 * 0 * 0 + 13 * 0 + 20) by reflexivity.
      exact Hpre.
    + replace (gpairs (repeat 1 (S 0 - 1) ++ [3] ++ (1 :: sg)))
        with ((3, 2) :: (1, 2) :: gpairs sg) by reflexivity.
      replace (2 * 0 + 3) with 3 by lia. apply cfg_sim_refl.
  - (* i = 2: the nested descent is a single RPUSH *)
    assert (H4 : run 9 (rcsec P 1 ((2 * 1 + 3, 2) :: (1, 2) ::
                    gpairs sg)) =
      Some (rcsec P 0 ((1, 2) :: (3, 2) :: (1, 2) :: gpairs sg))).
    { replace (2 * 1 + 3) with (S (S (S 2))) by reflexivity.
      replace ((3, 2) :: (1, 2) :: gpairs sg)
        with ((S 2, 2) :: (1, 2) :: gpairs sg) by reflexivity.
      exact (PHASE_second P 0 2 ((1, 2) :: gpairs sg)). }
    exists (rcsec P 0 ((1, 2) :: (3, 2) :: (1, 2) :: gpairs sg)).
    split.
    + replace (Dk 1) with ((2 * 1 * 1 + 13 * 1 + 20) + 9)
        by reflexivity.
      rewrite run_split. rewrite Hpre. exact H4.
    + replace (gpairs (repeat 1 (S 1 - 1) ++ [3] ++ (1 :: sg)))
        with ((1, 2) :: (3, 2) :: (1, 2) :: gpairs sg)
        by reflexivity.
      apply cfg_sim_refl.
  - (* i >= 3: the nested descent DESC(i-1) at suffix 1 :: sg *)
    assert (Hi' : 2 <= S (S i'')) by lia.
    assert (Hsg1 : Forall Nat.Odd (1 :: sg)).
    { constructor; [exists 0; reflexivity | exact Hsg]. }
    destruct (DESC P (S (S i'')) (1 :: sg) Hi' Hsg1) as [c [H4 Hs4]].
    destruct (run_compose_sim
                (2 * S (S i'') * S (S i'') + 13 * S (S i'') + 20)
                (bcost (S (S i'')) + 38)
                (rcsec P 0 (gpairs (repeat 1 (S (S (S i''))) ++ [3] ++ sg)))
                (rcsec P (S (S i''))
                   ((2 * S (S i'') + 3, 2) :: (1, 2) :: gpairs sg))
                (rcsec P (S (S i''))
                   ((2 * S (S i'') + 3, 2) :: gpairs (1 :: sg)))
                c Hpre (cfg_sim_refl _) H4) as [c' [Hc' Hsc']].
    exists c'. split.
    + replace (Dk (S (S i''))) with
        (2 * S (S i'') * S (S i'') + 13 * S (S i'') + 20 +
         (bcost (S (S i'')) + 38)).
      * exact Hc'.
      * unfold Dk.
        pose proof (bcost_closed i'') as Hb.
        replace (2 + i'') with (S (S i'')) in Hb by lia.
        nia.
    + apply (cfg_sim_trans c' c); [exact Hsc' |].
      replace (gpairs (repeat 1 (S (S i'')) ++ [3] ++ (1 :: sg)))
        with (gpairs (repeat 1 (S (S i'')) ++ [3]) ++
              gpairs (1 :: sg)).
      * exact Hs4.
      * rewrite !gpairs_app, app_assoc. reflexivity.
Qed.

Lemma WALK_ITER : forall P j sg, Forall Nat.Odd sg ->
  exists c, run (Dsum j)
    (rcsec P 0 (gpairs (repeat 1 j ++ [3] ++ sg))) = Some c /\
  cfg_sim c (rcsec P 0 (gpairs ([3] ++ repeat 1 j ++ sg))).
Proof.
  intros P j. induction j as [| j IH]; intros sg Hsg.
  - exists (rcsec P 0 (gpairs ([3] ++ sg))). split; [reflexivity |].
    apply cfg_sim_refl.
  - destruct (WALK P (S j) sg ltac:(lia) Hsg) as [c1 [H1 Hs1]].
    replace (S j - 1) with j in H1, Hs1 by lia.
    assert (Hsg1 : Forall Nat.Odd (1 :: sg)).
    { constructor; [exists 0; reflexivity | exact Hsg]. }
    destruct (IH (1 :: sg) Hsg1) as [c2 [H2 Hs2]].
    destruct (run_compose_sim (Dk j) (Dsum j)
                (rcsec P 0 (gpairs (repeat 1 (S j) ++ [3] ++ sg))) c1
                (rcsec P 0 (gpairs (repeat 1 j ++ [3] ++ (1 :: sg))))
                c2 H1 Hs1 H2) as [c [Hc Hsc]].
    exists c. split.
    + replace (Dsum (S j)) with (Dk j + Dsum j)
        by (rewrite Nat.add_comm; reflexivity).
      exact Hc.
    + apply (cfg_sim_trans c c2); [exact Hsc |].
      replace (gpairs ([3] ++ repeat 1 (S j) ++ sg))
        with (gpairs ([3] ++ repeat 1 j ++ (1 :: sg))).
      * exact Hs2.
      * replace (repeat 1 (S j)) with (1 :: repeat 1 j) by reflexivity.
        replace (repeat 1 j ++ (1 :: sg))
          with ((repeat 1 j ++ [1]) ++ sg)
          by (rewrite <- app_assoc; reflexivity).
        rewrite repeat_snoc. reflexivity.
Qed.

(* ================================================================ *)
(* Part 8: DSTAGE2 -- stage 2 for an arbitrary frozen prefix.        *)
(* ================================================================ *)

Lemma DSTAGE2 : forall P n, 2 <= n ->
  exists c, run (Tk n) (rcsec P n ((2 * n + 3, 2) :: [])) = Some c /\
  cfg_sim c (rcsec P 0 ((3, 2) :: repeat (1, 2) n)).
Proof.
  intros P n Hn.
  destruct (DESC P n [] Hn (Forall_nil _)) as [c1 [H1 Hs1]].
  replace (gpairs []) with (@nil (nat * nat)) in H1, Hs1
    by reflexivity.
  rewrite app_nil_r in Hs1.
  destruct (WALK_ITER P n [] (Forall_nil _)) as [c2 [H2 Hs2]].
  replace (repeat 1 n ++ [3] ++ []) with (repeat 1 n ++ [3]) in H2
    by (rewrite app_nil_r; reflexivity).
  destruct (run_compose_sim (bcost n + 38) (Dsum n)
              (rcsec P n ((2 * n + 3, 2) :: [])) c1
              (rcsec P 0 (gpairs (repeat 1 n ++ [3]))) c2
              H1 Hs1 H2) as [c [Hc Hsc]].
  exists c. split.
  - replace (Tk n) with (bcost n + 38 + Dsum n) by (unfold Tk; lia).
    exact Hc.
  - apply (cfg_sim_trans c c2); [exact Hsc |].
    replace ((3, 2) :: repeat (1, 2) n)
      with (gpairs ([3] ++ repeat 1 n ++ [])).
    + exact Hs2.
    + rewrite app_nil_r, gpairs_app, gpairs_repeat1. reflexivity.
Qed.

Print Assumptions DESC.
Print Assumptions WALK.
Print Assumptions DSTAGE2.
