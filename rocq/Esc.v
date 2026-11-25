(* ================================================================= *)
(* Esc.v -- component #16 (single-block case) pieces and the       *)
(* deviation-free pieces of #19: phase20 sections 1-2, phase21     *)
(* section 6.                                                      *)
(*                                                                 *)
(*  - gbsec: B-sections over an abstract frozen prefix P.          *)
(*  - gtup_prefix: the TUP prefix over gbsec.                      *)
(*  - POP2: the g1 = 2 transfer (phase20 section 2), proved for    *)
(*    all tails and all G: (B, P, a, s, [(2,2), (1, r2)] + rest)   *)
(*    -> (B, [0] ++ 1^(a+1) ++ P, s + 1, [1], r2 + 2, rest).        *)
(*  - PROBE_PREFIX: the single-block escape's probe prefix         *)
(*    (phase20 theorem P20.1): from ESC(L, beta), L >= 7 here      *)
(*    (the document states L >= 8; the E5 excursion's pattern      *)
(*    needs the e4form zero run >= 3, i.e. L >= 7), the five       *)
(*    excursions E1-E5 (total cost L + 42) land on                 *)
(*    (C, [1,1,1,0], right), cfg_sim to the clean C-section        *)
(*      csec 3 1 2 ((L - 6, 2) :: (1, 1) :: (1, 2)^(beta - 1)) 1.  *)
(*    The remaining ESC-era assembly (the G'' grind with its       *)
(*    PUSHX deviations and the s_regen + 3 > beta inequality) is   *)
(*    component #19 proper and stays fenced -- see                 *)
(*    mechanisation-status.md.                                     *)
(* ================================================================= *)

Require Import List Bool Arith Lia ZArith.
Import ListNotations.
Require Import TM Sections Mirror TokenPass Recoord Era.

(* ----------------------------------------------------------------- *)
(* Generalised B-sections and the TUP prefix                         *)
(* ----------------------------------------------------------------- *)

Definition gbsec (P : list sym) (a g0 s : nat)
                 (pairs : list (nat * nat)) (G : nat) : config :=
  mkCfg SB (repeat true a ++ P)
        (repeat false g0 ++ (repeat true s ++ tail pairs G)).

Lemma gtup_prefix : forall P a s' r1 rest G,
  run (S s' + 2) (gbsec P a 1 (S s') ((2, r1) :: rest) G) =
  Some (mkCfg SB (repeat true (S s') ++ (false :: repeat true (S a) ++ P))
                 (repeat false 1 ++ (repeat true r1 ++ tail rest G))).
Proof.
  intros P a s' r1 rest G.
  replace (S s' + 2) with (2 + (s' + 1)) by lia.
  rewrite run_split.
  assert (H2 : run 2 (gbsec P a 1 (S s') ((2, r1) :: rest) G) =
    Some (mkCfg SA (false :: repeat true (S a) ++ P)
           (repeat true s' ++
             (repeat false 2 ++ (repeat true r1 ++ tail rest G))))).
  { reflexivity. }
  rewrite H2. cbv beta iota.
  rewrite run_split.
  rewrite sweepA. cbv beta iota.
  reflexivity.
Qed.

Lemma POP2 : forall P a s' r2' rest G,
  run (S s' + 9) (gbsec P a 1 (S s') ((2, 2) :: (1, S r2') :: rest) G)
  = Some (gbsec (false :: repeat true (S a) ++ P) (S (S s')) 1
                (S (S (S r2'))) rest G).
Proof.
  intros P a s' r2' rest G.
  replace (S s' + 9) with ((S s' + 2) + 7) by lia.
  rewrite run_split.
  rewrite gtup_prefix.
  reflexivity.
Qed.

(* ----------------------------------------------------------------- *)
(* The probe prefix (phase20 theorem P20.1)                          *)
(* ESC(L, m + 2): C at the separator of a single block 1^L,         *)
(* working word 1^2 0^3 1^2 (0 1^2)^m.                             *)
(* ----------------------------------------------------------------- *)

Definition esc_src (L m : nat) : config :=
  mkCfg SC (false :: repeat true L)
        (true :: true :: false :: false :: false :: true :: true ::
         rtail (repeat (1, 2) m)).

(* E1 intermediate forms; r12 m is E1's invariant tail block. *)
Definition r12 (m : nat) : list sym :=
  true :: true :: false :: true :: false :: true :: true :: s3R m.

Definition e1form9 (L m : nat) : config :=
  mkCfg SC (repeat true L)
        (false :: true :: false :: true :: true :: s3R m).

Definition e1form10 (l m : nat) : config :=
  mkCfg SD (repeat true l)
        (true :: false :: true :: false :: true :: true :: s3R m).

Definition e1form11 (l m : nat) : config :=
  mkCfg SE (repeat true l)
        (true :: true :: false :: true :: false :: true :: true :: s3R m).

Definition e1form12 (l m : nat) : config :=
  mkCfg SF (repeat true l)
        (true :: true :: true :: false :: true :: false :: true :: true
         :: s3R m).

Definition e1formS (l m : nat) : config :=
  mkCfg SF []
        (false :: false :: (repeat false l ++ r12 m)).

Definition e1formC (l m : nat) : config :=
  mkCfg SC []
        (false :: true :: false :: (repeat false l ++ r12 m)).

Definition e1end (l m : nat) : config :=
  mkCfg SD []
        (false :: false :: true :: false :: (repeat false l ++ r12 m)).

Definition e2form (l m : nat) : config :=
  mkCfg SC []
        (true :: true :: true :: false :: (repeat false l ++ r12 m)).

Definition e3form (l m : nat) : config :=
  mkCfg SD []
        (false :: false :: true :: false :: false :: true :: true ::
         (repeat false l ++
          (true :: true :: false :: true :: s3R (S m)))).

Definition e4form (l m : nat) : config :=
  mkCfg SC []
        (true :: true :: true :: false :: false :: true :: true ::
         (repeat false l ++
          (true :: true :: false :: true :: s3R (S m)))).

Definition e5form (l m : nat) : config :=
  mkCfg SC (true :: true :: true :: false :: [])
        (true :: true :: false :: true :: true ::
         (repeat false l ++
          (true :: true :: false :: true :: s3R (S m)))).

Lemma E1_9 : forall L m,
  run 9 (esc_src L m) = Some (e1form9 L m).
Proof. intros. reflexivity. Qed.

Lemma E1_10 : forall l m,
  run 1 (e1form9 (S l) m) = Some (e1form10 l m).
Proof. intros. reflexivity. Qed.

Lemma E1_11 : forall l m,
  run 1 (e1form10 (S l) m) = Some (e1form11 l m).
Proof. intros. reflexivity. Qed.

Lemma E1_12 : forall l m,
  run 1 (e1form11 (S l) m) = Some (e1form12 l m).
Proof. intros. reflexivity. Qed.

Lemma E1_sweep : forall l m,
  run (S l) (e1form12 l m) = Some (e1formS l m).
Proof.
  intros l m.
  replace (S l) with (l + 1) by lia.
  rewrite run_split.
  unfold e1form12.
  rewrite <- (app_nil_r (repeat true l)).
  rewrite sweepF.
  reflexivity.
Qed.

Lemma E1_end1 : forall l m,
  run 1 (e1formS l m) = Some (e1formC l m).
Proof. intros. reflexivity. Qed.

Lemma E1_end2 : forall l m,
  run 1 (e1formC l m) = Some (e1end l m).
Proof. intros. reflexivity. Qed.

(* E1 assembled: cost L + 12 at L = l + 3. *)
Lemma E1 : forall l m,
  run (l + 15) (esc_src (l + 3) m) = Some (e1end l m).
Proof.
  intros l m.
  replace (l + 15) with (9 + (1 + (1 + (1 + ((S l) + (1 + 1)))))) by lia.
  rewrite run_split. rewrite E1_9.
  replace (l + 3) with (S (l + 2)) by lia.
  rewrite run_split. rewrite E1_10.
  replace (l + 2) with (S (l + 1)) by lia.
  rewrite run_split. rewrite E1_11.
  replace (l + 1) with (S l) by lia.
  rewrite run_split. rewrite E1_12.
  rewrite run_split. rewrite E1_sweep.
  rewrite run_split. rewrite E1_end1.
  apply E1_end2.
Qed.

Lemma E2 : forall l m,
  run 2 (e1end l m) = Some (e2form l m).
Proof. intros. reflexivity. Qed.

Lemma E3 : forall l m,
  run 12 (e2form (S (S l)) m) = Some (e3form (S l) m).
Proof. intros. reflexivity. Qed.

Lemma E4 : forall l m,
  run 2 (e3form l m) = Some (e4form l m).
Proof. intros. reflexivity. Qed.

(* E5 needs the zero run in e4form to be at least 3 (at run 2 the   *)
(* excursion leaves the E5 pattern -- checked against the model).  *)
Lemma E5 : forall l m,
  run 14 (e4form (S (S (S l))) m) = Some (e5form (S l) m).
Proof. intros. reflexivity. Qed.

(* The probe prefix assembled: at L = l + 7, cost L + 42. *)
Lemma PROBE_PREFIX : forall l m,
  run (l + 49) (esc_src (l + 7) m) = Some (e5form (S l) m).
Proof.
  intros l m.
  assert (H1 : run (l + 19) (esc_src (l + 7) m) = Some (e1end (l + 4) m)).
  { replace (l + 19) with ((l + 4) + 15) by lia.
    replace (l + 7) with ((l + 4) + 3) by lia.
    apply E1. }
  assert (H2 : run 2 (e1end (l + 4) m) = Some (e2form (l + 4) m))
    by apply E2.
  assert (H3 : run 12 (e2form (l + 4) m) = Some (e3form (l + 3) m)).
  { replace (l + 4) with (S (S (l + 2))) by lia.
    replace (l + 3) with (S (l + 2)) by lia.
    apply E3. }
  assert (H4 : run 2 (e3form (l + 3) m) = Some (e4form (l + 3) m))
    by apply E4.
  assert (H5 : run 14 (e4form (l + 3) m) = Some (e5form (S l) m)).
  { replace (l + 3) with (S (S (S l))) by lia. apply E5. }
  replace (l + 49) with ((l + 19) + (2 + (12 + (2 + 14)))) by lia.
  rewrite run_split. rewrite H1.
  rewrite run_split. rewrite H2.
  rewrite run_split. rewrite H3.
  rewrite run_split. rewrite H4.
  exact H5.
Qed.

(* ----------------------------------------------------------------- *)
(* The landing is the clean C-section, up to cfg_sim                 *)
(* ----------------------------------------------------------------- *)

Lemma nth_app_false : forall (l0 : list sym) k,
  nth k (l0 ++ [false]) false = nth k l0 false.
Proof.
  induction l0 as [|a l0 IH]; intros k.
  - destruct k as [| [| k']]; reflexivity.
  - destruct k as [|k]; [reflexivity |].
    apply IH.
Qed.

Lemma sim_left_snoc_false : forall q (l0 : list sym) r,
  cfg_sim (mkCfg q (l0 ++ [false]) r) (mkCfg q l0 r).
Proof.
  intros q l0 r. split; [reflexivity |].
  intros p. unfold tape_of.
  destruct (Z_le_dec 0 p) as [_ | _]; [reflexivity |].
  apply nth_app_false.
Qed.

Lemma tail_pair2 : forall l m,
  tail ((l, 2) :: (1, 1) :: repeat (1, 2) (S m)) 1
  = repeat false l ++
    (true :: true :: false :: true :: (s3R m ++ [false; true; true])).
Proof.
  intros l m.
  cbn [tail].
  rewrite (tail_rtail (repeat (1, 2) (S m)) 1).
  fold (s3R m).
  cbn [repeat].
  reflexivity.
Qed.

Lemma e5form_right : forall l m,
  cright (e5form l m)
  = cright (csec 3 1 2 ((l, 2) :: (1, 1) :: repeat (1, 2) (S m)) 1).
Proof.
  intros l m. unfold e5form, csec.
  cbn [cright].
  rewrite tail_pair2.
  rewrite s3R_snoc.
  rewrite s3R_cons.
  reflexivity.
Qed.

Lemma PROBE_PREFIX_sim : forall l m,
  cfg_sim (e5form l m)
          (csec 3 1 2 ((l, 2) :: (1, 1) :: repeat (1, 2) (S m)) 1).
Proof.
  intros l m. split.
  - reflexivity.
  - intros p. unfold tape_of.
    destruct (Z_le_dec 0 p) as [_ | _].
    + rewrite e5form_right. reflexivity.
    + unfold e5form, csec. cbn [cleft repeat].
      replace [true; true; true; false]
        with ([true; true; true] ++ [false]) by reflexivity.
      apply nth_app_false.
Qed.

(* ----------------------------------------------------------------- *)
(* Axiom audit                                                       *)
(* ----------------------------------------------------------------- *)

Print Assumptions POP2.
Print Assumptions PROBE_PREFIX.
Print Assumptions PROBE_PREFIX_sim.
