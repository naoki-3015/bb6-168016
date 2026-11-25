(* ================================================================= *)
(* Phase 23 -- Sections.v: section configurations of the standard    *)
(* (single-block) I+ frame and the soundness of the four rules       *)
(* TDN, PUSH, POP (general form) and Stage A, as derived by hand in  *)
(* bounce-derivation.md and reexpansion-derivation.md.               *)
(*                                                                   *)
(* A section is a zipper config whose tape has the form              *)
(*   1^a 0^g0 1^s (0^g 1^r)* 0^G 1^2                                 *)
(* with the head at the left edge of the prefix block (B-section,    *)
(* state B) or two cells into it (C-section, state C, s = 2).  The   *)
(* prefix block 1^a plays the role of 1^B2 in the documents (the     *)
(* 1^17 wall further left is inert in this frame).  Each rule is     *)
(* stated as: from a section satisfying the rule's hypothesis, the   *)
(* execution reaches the predicted successor section in the          *)
(* predicted number of steps; since the run returns Some, no step    *)
(* on the way halts, i.e. no E-on-0 read occurs en route (halt_iff). *)
(*                                                                   *)
(* Two representation choices keep the kernel checks definitional:   *)
(* (i) C-sections are parametrised by a2 = a - 2, the length of      *)
(* the left 1-run, because x - 0 does not reduce for abstract x;     *)
(* (ii) the section tail is a single fixpoint `tail` that consumes   *)
(* the pair list and the terminal gap together, so that prepending   *)
(* a pair is a definitional equality (no app associativity needed). *)
(* ================================================================= *)

Require Import List Bool Arith Lia ZArith.
Import ListNotations.
Require Import TM.

Fixpoint tail (pairs : list (nat * nat)) (G : nat) : list sym :=
  match pairs with
  | [] => repeat false G ++ [true; true]
  | (g, r) :: t => repeat false g ++ (repeat true r ++ tail t G)
  end.

Definition csec (a2 g0 s : nat) (pairs : list (nat * nat)) (G : nat)
  : config :=
  mkCfg SC (repeat true a2)
    (true :: true :: (repeat false g0 ++ (repeat true s ++
       tail pairs G))).

Definition bsec (a g0 s : nat) (pairs : list (nat * nat)) (G : nat)
  : config :=
  mkCfg SB (repeat true a)
    (repeat false g0 ++ (repeat true s ++ tail pairs G)).

(* ---------------------------------------------------------------- *)
(* List helpers and the three sweeps (the only inductions in the     *)
(* rule derivations, exactly as in bounce-derivation.md).            *)
(* ---------------------------------------------------------------- *)

Lemma rep_app : forall (b : sym) n m,
  repeat b (n + m) = repeat b n ++ repeat b m.
Proof.
  intros b n. induction n; intros m; simpl; [reflexivity |].
  rewrite IHn. reflexivity.
Qed.

Lemma rep_snoc : forall (b : sym) n l,
  repeat b n ++ (b :: l) = b :: (repeat b n ++ l).
Proof.
  intros b n. induction n; intros l; simpl; [reflexivity |].
  rewrite IHn. reflexivity.
Qed.

Lemma run_1 : forall c, run 1 c = step c.
Proof. intros c. cbn [run]. destruct (step c); reflexivity. Qed.

(* Sweep-A: A-on-1 = 1RA crosses a 1-run rightward, tape unchanged. *)
Lemma sweepA : forall n l r,
  run n (mkCfg SA l (repeat true n ++ r)) =
  Some (mkCfg SA (repeat true n ++ l) r).
Proof.
  induction n as [| n IH]; intros l r; simpl; [reflexivity |].
  rewrite IH. rewrite rep_snoc. reflexivity.
Qed.

(* Sweep-B: B-on-1 = 1LB crosses a 1-run leftward, tape unchanged. *)
Lemma sweepB : forall n l r,
  run n (mkCfg SB (repeat true n ++ l) (true :: r)) =
  Some (mkCfg SB l (repeat true n ++ (true :: r))).
Proof.
  induction n as [| n IH]; intros l r; simpl; [reflexivity |].
  rewrite IH. rewrite rep_snoc. reflexivity.
Qed.

(* Sweep-F: F-on-1 = 0LF erases a 1-run leftward into 0s. *)
Lemma sweepF : forall n l r,
  run n (mkCfg SF (repeat true n ++ l) (true :: r)) =
  Some (mkCfg SF l (true :: (repeat false n ++ r))).
Proof.
  induction n as [| n IH]; intros l r; simpl; [reflexivity |].
  rewrite IH. rewrite rep_snoc. reflexivity.
Qed.

(* The probe: A on the first cell of a 0-gap of width >= 3 performs
   exactly 5 steps (1RB, 1RC, 0LD, 1LE, 1LF), writes 1s on the first
   two gap cells, and lands in F one cell left of the gap. *)
Lemma probe : forall l r,
  run 5 (mkCfg SA l (false :: false :: false :: r)) =
  Some (mkCfg SF (tl l) (hd false l :: true :: true :: false :: r)).
Proof. intros. reflexivity. Qed.

(* ---------------------------------------------------------------- *)
(* TDN: a C-section with g0 = 1 and s = 2 turns down into the         *)
(* B-section with the same a2 (= a - 2), s' = 4, in exactly 6 steps. *)
(* ---------------------------------------------------------------- *)

Lemma TDN : forall a2 pairs G,
  run 6 (csec a2 1 2 pairs G) = Some (bsec a2 1 4 pairs G).
Proof. intros. reflexivity. Qed.

(* ---------------------------------------------------------------- *)
(* PUSH: a C-section with g0 >= 3 probes the gap and returns to a    *)
(* C-section with a2' = a2 - 1, g0' = 1, and the pair (g0 - 2, 2)    *)
(* pushed onto the word, in exactly 9 steps.  (Stated with           *)
(* a2 = S a2' so that a2 >= 1 is definitional.)                      *)
(* ---------------------------------------------------------------- *)

Lemma PUSH : forall a2' g'' pairs G,
  run 9 (csec (S a2') (S (S (S g''))) 2 pairs G) =
  Some (csec a2' 1 2 ((S g'', 2) :: pairs) G).
Proof.
  intros. reflexivity.
Qed.

(* ---------------------------------------------------------------- *)
(* POP, general form: a B-section with first gap g1 = 1 pops the     *)
(* first pair (1, r1): a' = a + 1, s' = s + r1, in exactly 2s + 3     *)
(* steps.  Assembled from the prefix (B, C, Sweep-A, A-turn) and     *)
(* the return (Sweep-B plus the landing step).                       *)
(* ---------------------------------------------------------------- *)

Lemma pop_prefix : forall a s r1 rest G, 1 <= s ->
  run (s + 2) (bsec a 1 s ((1, r1) :: rest) G) =
  Some (mkCfg SB (repeat true s ++ (false :: repeat true (S a)))
                 (repeat true r1 ++ tail rest G)).
Proof.
  intros a s r1 rest G Hs. destruct s as [| s']; [lia |].
  replace (S s' + 2) with (2 + (s' + 1)) by lia.
  rewrite run_split.
  assert (H2 : run 2 (bsec a 1 (S s') ((1, r1) :: rest) G) =
    Some (mkCfg SA (false :: true :: repeat true a)
           (repeat true s' ++
             (false :: (repeat true r1 ++ tail rest G))))).
  { reflexivity. }
  rewrite H2. cbv beta iota.
  rewrite run_split.
  rewrite sweepA. cbv beta iota.
  reflexivity.
Qed.

Lemma pop_sweep : forall a s r1 rest G, 1 <= s -> 1 <= r1 ->
  run (s + 1) (mkCfg SB (repeat true s ++ (false :: repeat true (S a)))
                 (repeat true r1 ++ tail rest G)) =
  Some (bsec (S a) 1 (s + r1) rest G).
Proof.
  intros a s r1 rest G Hs Hr1.
  destruct s as [| s'']; [lia |]. destruct r1 as [| r1']; [lia |].
  rewrite run_split.
  change (repeat true (S r1') ++ tail rest G)
    with (true :: (repeat true r1' ++ tail rest G)).
  rewrite sweepB. cbv beta iota.
  unfold bsec. rewrite rep_app. rewrite <- !app_assoc.
  reflexivity.
Qed.

Lemma POP : forall a s r1 rest G, 2 <= s -> 1 <= r1 ->
  run (2 * s + 3) (bsec a 1 s ((1, r1) :: rest) G) =
  Some (bsec (S a) 1 (s + r1) rest G).
Proof.
  intros a s r1 rest G Hs Hr1.
  assert (Hs1 : 1 <= s) by lia.
  replace (2 * s + 3) with ((s + 2) + (s + 1)) by lia.
  rewrite run_split.
  rewrite (pop_prefix a s r1 rest G Hs1).
  exact (pop_sweep a s r1 rest G Hs1 Hr1).
Qed.

(* ---------------------------------------------------------------- *)
(* TUP: a B-section with first gap g1 >= 3 probes g1 and lands at    *)
(* a C-section with g0' = s - 1 and the pair (g1 - 2, r1) pushed,    *)
(* in exactly 2s + 6 steps (bounce-derivation.md S4.2).  The prefix  *)
(* is POP's prefix with a general first gap; the return is the       *)
(* probe followed by Sweep-F over the shuttle.                       *)
(* ---------------------------------------------------------------- *)

Lemma tup_prefix : forall a s' g1' r1 rest G,
  run (S s' + 2) (bsec a 1 (S s') ((S g1', r1) :: rest) G) =
  Some (mkCfg SB (repeat true (S s') ++ (false :: repeat true (S a)))
                 (repeat false g1' ++ (repeat true r1 ++ tail rest G))).
Proof.
  intros a s' g1' r1 rest G.
  replace (S s' + 2) with (2 + (s' + 1)) by lia.
  rewrite run_split.
  assert (H2 : run 2 (bsec a 1 (S s') ((S g1', r1) :: rest) G) =
    Some (mkCfg SA (false :: repeat true (S a))
           (repeat true s' ++
             (repeat false (S g1') ++ (repeat true r1 ++ tail rest G))))).
  { reflexivity. }
  rewrite H2. cbv beta iota.
  rewrite run_split.
  rewrite sweepA. cbv beta iota.
  reflexivity.
Qed.

Lemma TUP : forall a s'' g1'' r1 rest G,
  run (2 * S (S s'') + 6)
    (bsec a 1 (S (S s'')) ((S (S (S g1'')), r1) :: rest) G) =
  Some (csec a (S s'') 2 ((S g1'', r1) :: rest) G).
Proof.
  intros a s'' g1'' r1 rest G.
  replace (2 * S (S s'') + 6) with ((S (S s'') + 2) + (S s'' + 5)) by lia.
  rewrite run_split.
  rewrite (tup_prefix a (S s'') (S (S g1'')) r1 rest G).
  (* The probe at g1: 4 steps (B, C, D, E of the Probe Lemma; the
     prefix's A-step was its first step). *)
  assert (H4 : run 4
    (mkCfg SB (repeat true (S (S s'')) ++ (false :: repeat true (S a)))
       (repeat false (S (S g1'')) ++ (repeat true r1 ++ tail rest G))) =
    Some (mkCfg SF (repeat true s'' ++ (false :: repeat true (S a)))
       (true :: true :: true :: false ::
         (repeat false g1'' ++ (repeat true r1 ++ tail rest G))))).
  { reflexivity. }
  replace (S s'' + 5) with (4 + (s'' + 2)) by lia.
  rewrite run_split.
  rewrite H4. cbv beta iota.
  rewrite run_split.
  rewrite sweepF. cbv beta iota.
  reflexivity.
Qed.

(* ---------------------------------------------------------------- *)
(* REGEN (phase19-derivations.md S1): at a B-section with w = [1]    *)
(* and G = 1, Stage A cannot fire; instead the POP list runs with    *)
(* the terminal pair as pair 1, the Stage A list runs at G = blank,  *)
(* and the PUSH list closes at a degenerate C-section:               *)
(* (B, a, s, [1], 1) -> (C, a+2, 2, [1], G = s-1) in 4s + 22 steps.   *)
(* The two intermediate forms are "open" (blank beyond the last      *)
(* run).  The Stage A list at G = blank materialises one trailing    *)
(* blank cell at the end of the right list (the probe's reflection   *)
(* cell); it is carried explicitly in the tail parameter r of        *)
(* csecT / csecR.  With r = [false] the landing has the same tape    *)
(* as the plain csec landing (REGEN_tape below).                     *)
(* ---------------------------------------------------------------- *)

Definition bsec_open (a g0 s : nat) : config :=
  mkCfg SB (repeat true a) (repeat false g0 ++ repeat true s).

Definition csecT (a2 g0 : nat) (r : list sym) : config :=
  mkCfg SC (repeat true a2)
    (true :: true :: (repeat false g0 ++ (true :: true :: r))).

Definition csecR (a2 G : nat) (r : list sym) : config :=
  mkCfg SC (repeat true a2)
    (true :: true :: (repeat false 1 ++
       (repeat true 2 ++ (repeat false G ++ (true :: true :: r))))).

(* Part 1: the POP list with the terminal pair (1, 2) as pair 1. *)
Lemma popT_prefix : forall a s',
  run (S s' + 2) (bsec a 1 (S s') [] 1) =
  Some (mkCfg SB (repeat true (S s') ++ (false :: repeat true (S a)))
                 [true; true]).
Proof.
  intros a s'.
  replace (S s' + 2) with (2 + (s' + 1)) by lia.
  rewrite run_split.
  assert (H2 : run 2 (bsec a 1 (S s') [] 1) =
    Some (mkCfg SA (false :: repeat true (S a))
           (repeat true s' ++ [false; true; true]))).
  { reflexivity. }
  rewrite H2. cbv beta iota.
  rewrite run_split.
  rewrite sweepA. cbv beta iota.
  reflexivity.
Qed.

Lemma repT_snoc3 : forall n,
  repeat true (n + 3) = repeat true n ++ [true; true; true].
Proof. intros n. rewrite rep_app. reflexivity. Qed.

Lemma popT_sweep : forall a s'',
  run (S (S s'') + 1)
    (mkCfg SB (repeat true (S (S s'')) ++ (false :: repeat true (S a)))
              [true; true]) =
  Some (bsec_open (S a) 1 (S (S s'') + 2)).
Proof.
  intros a s''.
  replace (S (S s'') + 1) with (1 + (S s'' + 1)) by lia.
  rewrite run_split.
  assert (H1 : run 1
    (mkCfg SB (repeat true (S (S s'')) ++ (false :: repeat true (S a)))
              [true; true]) =
    Some (mkCfg SB (repeat true (S s'') ++ (false :: repeat true (S a)))
              [true; true; true])).
  { reflexivity. }
  rewrite H1. cbv beta iota.
  rewrite run_split.
  rewrite sweepB. cbv beta iota.
  rewrite run_1.
  assert (Hstep : step (mkCfg SB (false :: repeat true (S a))
                        (repeat true (S s'') ++ [true; true; true])) =
    Some (mkCfg SB (repeat true (S a))
           (false :: true :: (repeat true s'' ++ [true; true; true])))).
  { reflexivity. }
  rewrite Hstep.
  unfold bsec_open.
  replace (S (S s'') + 2) with (S (s'' + 3)) by lia.
  change (repeat true (S (s'' + 3)))
    with (true :: repeat true (s'' + 3)).
  rewrite repT_snoc3. reflexivity.
Qed.

Lemma POP_terminal : forall a s, 2 <= s ->
  run (2 * s + 3) (bsec a 1 s [] 1) =
  Some (bsec_open (S a) 1 (s + 2)).
Proof.
  intros a s Hs. destruct s as [| [| s'']]; try lia.
  replace (2 * S (S s'') + 3) with ((S (S s'') + 2) + (S (S s'') + 1))
    by lia.
  rewrite run_split.
  rewrite popT_prefix.
  exact (popT_sweep a s'').
Qed.

(* Part 2: the Stage A list at G = blank (the probe fires in the
   blank beyond the shuttle; cost 2L + 6, span + 2). *)
Lemma probe_blank : forall l,
  run 5 (mkCfg SA l []) =
  Some (mkCfg SF (tl l) (hd false l :: true :: true :: false :: [])).
Proof. intros. reflexivity. Qed.

Lemma stageAblank_prefix : forall A L',
  run 2 (bsec_open A 1 (S L')) =
  Some (mkCfg SA (false :: repeat true (S A)) (repeat true L')).
Proof. intros. reflexivity. Qed.

Lemma StageA_blank : forall A L, 2 <= L ->
  run (2 * L + 6) (bsec_open A 1 L) =
  Some (csecT A (L - 1) [false]).
Proof.
  intros A L HL. destruct L as [| [| L'']]; try lia.
  replace (2 * S (S L'') + 6) with (2 + (S L'' + (5 + (L'' + 2))))
    by lia.
  replace (S (S L'') - 1) with (S L'') by lia.
  rewrite run_split.
  rewrite stageAblank_prefix. cbv beta iota.
  rewrite <- (app_nil_r (repeat true (S L''))).
  rewrite run_split.
  rewrite sweepA. cbv beta iota.
  rewrite run_split.
  (* The probe in the blank: 5 steps (probe_blank), applied by
     change since the goal's empty right list is @nil bool while a
     stated lemma's would elaborate to @nil sym -- convertible but
     not syntactically equal, so rewrite cannot match it. *)
  change (run 5
    (mkCfg SA (repeat true (S L'') ++ (false :: repeat true (S A))) []))
    with (Some (mkCfg SF (repeat true L'' ++ (false :: repeat true (S A)))
                 [true; true; true; false])).
  cbv beta iota.
  rewrite run_split.
  rewrite sweepF. cbv beta iota.
  reflexivity.
Qed.

(* Part 3: the PUSH list at the degenerate C-section (its only run
   after the gap is the terminal pair). *)
Lemma PUSH_T : forall a2' g'' r,
  run 9 (csecT (S a2') (S (S (S g''))) r) =
  Some (csecR a2' (S g'') r).
Proof. intros. reflexivity. Qed.

Lemma REGEN : forall a s, 2 <= s ->
  run (4 * s + 22) (bsec a 1 s [] 1) =
  Some (csecR a (s - 1) [false]).
Proof.
  intros a s Hs. destruct s as [| [| s2]]; try lia.
  replace (4 * S (S s2) + 22)
    with ((2 * S (S s2) + 3) + ((2 * (S (S s2) + 2) + 6) + 9)) by lia.
  rewrite run_split.
  rewrite (POP_terminal a (S (S s2)) Hs).
  rewrite run_split.
  rewrite (StageA_blank (S a) (S (S s2) + 2)).
  - replace (S (S s2) + 2 - 1) with (S (S (S s2))) by lia.
    replace (S (S s2) - 1) with (S s2) by lia.
    exact (PUSH_T a s2 [false]).
  - lia.
Qed.

Lemma nth_app_false : forall (l : list sym) i,
  nth i (l ++ [false]) false = nth i l false.
Proof.
  induction l as [| x t IH]; intros i.
  - destruct i as [| [| i']]; reflexivity.
  - destruct i; simpl; [reflexivity | apply IH].
Qed.

(* The REGEN landing with its one materialised trailing blank cell
   has exactly the tape of the documents' landing section
   (C, a+2, 2, [1], G = s-1). *)
Lemma REGEN_tape : forall a s2 p,
  tape_of (csecR a (S s2) [false]) p =
  tape_of (csec a 1 2 [] (S s2)) p.
Proof.
  intros a s2 p. unfold tape_of.
  assert (E : cright (csecR a (S s2) [false]) =
              cright (csec a 1 2 [] (S s2)) ++ [false]).
  { unfold csecR, csec, tail. simpl. rewrite <- !app_assoc. reflexivity. }
  destruct (Z_le_dec 0 p).
  - rewrite E. apply nth_app_false.
  - reflexivity.
Qed.

(* ---------------------------------------------------------------- *)
(* Stage A: a B-section with empty word (post-collapse) and G >= 3   *)
(* probes the terminal gap and lands at the C-section with           *)
(* a2' = a (i.e. a' = a + 2), g0' = s - 1, G' = G - 2, in exactly     *)
(* 2s + 6 steps.                                                     *)
(* ---------------------------------------------------------------- *)

Lemma stageA_prefix : forall a s' G,
  run 2 (bsec a 1 (S s') [] G) =
  Some (mkCfg SA (false :: true :: repeat true a)
         (repeat true s' ++ tail [] G)).
Proof. intros. reflexivity. Qed.

Lemma StageA : forall a s G, 2 <= s -> 3 <= G ->
  run (2 * s + 6) (bsec a 1 s [] G) =
  Some (csec a (s - 1) 2 [] (G - 2)).
Proof.
  intros a s G Hs HG.
  destruct s as [| [| s'']]; try lia.
  destruct G as [| [| [| G']]]; try lia.
  replace (2 * S (S s'') + 6) with (2 + (S s'' + (5 + (s'' + 2))))
    by lia.
  rewrite run_split.
  rewrite stageA_prefix. cbv beta iota.
  rewrite run_split.
  rewrite sweepA. cbv beta iota.
  assert (Hprobe : run 5
    (mkCfg SA (repeat true (S s'') ++ (false :: true :: repeat true a))
       (tail [] (S (S (S G'))))) =
    Some (mkCfg SF (repeat true s'' ++ (false :: true :: repeat true a))
           (true :: true :: true :: false ::
             (repeat false G' ++ [true; true])))).
  { reflexivity. }
  rewrite run_split.
  rewrite Hprobe. cbv beta iota.
  rewrite run_split.
  rewrite sweepF. cbv beta iota.
  reflexivity.
Qed.
