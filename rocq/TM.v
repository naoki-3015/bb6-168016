(* ================================================================= *)
(* Phase 23 -- Rocq mechanisation of the non-halting proof of        *)
(* BB(6) holdout #168016:                                            *)
(*   1RB1RA_1RC1LB_0LD0RA_1RF1LE_---1LF_1LC0LF                       *)
(* (halts iff state E reads 0).                                      *)
(*                                                                   *)
(* TM.v: the machine as a total step function on zipper configs,     *)
(* fuel-based execution, the entry (predecessor) lemmas obtained by   *)
(* finite inspection of the transition table, and lemmas M1--M4 of   *)
(* post-R-proof.md S1: halting is equivalent to one tape pattern.    *)
(*                                                                   *)
(* Conventions (zipper): a config (q, l, r) has head on hd r         *)
(* (false if r = []); l is the tape left of the head, nearest first. *)
(* Cells outside the finite lists are false (blank).  This is the    *)
(* list-based style of the bbchallenge Coq developments (Coq-BB5),   *)
(* specialised to this one machine.                                  *)
(* ================================================================= *)

Require Import List Bool Arith Lia ZArith.
Import ListNotations.

Inductive state := SA | SB | SC | SD | SE | SF.
Definition sym := bool.               (* false = 0, true = 1 *)
Inductive dir := DL | DR.

(* The transition function of #168016.  None = undefined = halt. *)
Definition trans (q : state) (b : sym) : option (sym * dir * state) :=
  match q, b with
  | SA, false => Some (true,  DR, SB)   (* A: 1RB *)
  | SA, true  => Some (true,  DR, SA)   (* A: 1RA *)
  | SB, false => Some (true,  DR, SC)   (* B: 1RC *)
  | SB, true  => Some (true,  DL, SB)   (* B: 1LB *)
  | SC, false => Some (false, DL, SD)   (* C: 0LD *)
  | SC, true  => Some (false, DR, SA)   (* C: 0RA *)
  | SD, false => Some (true,  DR, SF)   (* D: 1RF *)
  | SD, true  => Some (true,  DL, SE)   (* D: 1LE *)
  | SE, false => None                   (* E: ---  (halt) *)
  | SE, true  => Some (true,  DL, SF)   (* E: 1LF *)
  | SF, false => Some (true,  DL, SC)   (* F: 1LC *)
  | SF, true  => Some (false, DL, SF)   (* F: 0LF *)
  end.

Record config : Type := mkCfg {
  cstate : state;
  cleft  : list sym;   (* left of head, nearest first *)
  cright : list sym    (* head cell first, then rightward *)
}.

Definition read (c : config) : sym := hd false (cright c).

Definition step (c : config) : option config :=
  match trans (cstate c) (read c) with
  | None => None
  | Some (w, d, q') =>
      match d with
      | DR => Some (mkCfg q' (w :: cleft c) (tl (cright c)))
      | DL => Some (mkCfg q' (tl (cleft c))
                          (hd false (cleft c) :: w :: tl (cright c)))
      end
  end.

Fixpoint run (n : nat) (c : config) : option config :=
  match n with
  | 0 => Some c
  | S n' => match step c with
            | Some c' => run n' c'
            | None => None
            end
  end.

Definition cfg_blank : config := mkCfg SA [] [].

(* The head-relative tape as a function of a Z offset (0 = head). *)
Definition tape_of (c : config) (p : Z) : sym :=
  if Z_le_dec 0 p
  then nth (Z.to_nat p) (cright c) false
  else nth (Z.to_nat (- p - 1)) (cleft c) false.

(* ---------------------------------------------------------------- *)
(* Execution lemmas                                                  *)
(* ---------------------------------------------------------------- *)

Lemma run_split : forall n m c,
  run (n + m) c = match run n c with
                  | Some c' => run m c'
                  | None => None
                  end.
Proof.
  induction n; intros; simpl.
  - reflexivity.
  - destruct (step c) as [c' |]; [apply IHn | reflexivity].
Qed.

Lemma run_some_step_neq : forall n c c',
  run n c = Some c' ->
  forall m, m < n -> exists cm, run m c = Some cm /\ step cm <> None.
Proof.
  intros n c c' H m Hm.
  replace n with (m + (n - m)) in H by lia.
  rewrite run_split in H.
  destruct (run m c) as [cm |] eqn:E; [| discriminate].
  exists cm. split; [reflexivity |].
  destruct (n - m) as [| k] eqn:Ek; [lia |].
  simpl in H.
  destruct (step cm) as [cm' |] eqn:Es; [| discriminate].
  intro Hx. discriminate.
Qed.

(* Halting at a step is exactly an E-on-0 read (the only undefined
   transition of the table). *)
Lemma halt_iff : forall c,
  step c = None <-> (cstate c = SE /\ read c = false).
Proof.
  intros [q l r].
  destruct q; destruct r as [| b r']; try destruct b;
    unfold step, read; simpl;
    split; intros H; try discriminate;
    try (destruct H as [H1 H2]; discriminate);
    repeat split; reflexivity.
Qed.

Lemma step_some_state : forall c c',
  step c = Some c' -> cstate c' <> SE \/ cstate c = SD.
Proof.
  intros c c' H. destruct c as [q l r].
  destruct q; destruct r as [| b r']; try destruct b;
    unfold step in H; simpl in H; try discriminate;
    inversion H; subst; simpl;
    first [ left; discriminate | right; reflexivity ].
Qed.

(* ---------------------------------------------------------------- *)
(* Predecessor (entry) lemmas: finite inspection of the table.       *)
(* E is entered only from D-on-1; D only from C-on-0; C only from    *)
(* B-on-0 or F-on-0; F only from D-on-0, E-on-1 or F-on-1; B only    *)
(* from A-on-0 or B-on-1.  Each lemma also gives the exact shape     *)
(* of the successor config.                                          *)
(* ---------------------------------------------------------------- *)

(* Crush one fully-destructed step equation: reduce the transition,
   substitute the successor, and kill branches whose resulting state
   contradicts the target-state hypothesis. *)
Ltac crush_step H Hst :=
  unfold step in H; simpl in H; try discriminate;
  inversion H; subst; simpl in Hst; try discriminate; simpl.

Lemma pred_E : forall c c', step c = Some c' -> cstate c' = SE ->
  cstate c = SD /\ read c = true /\
  c' = mkCfg SE (tl (cleft c))
                (hd false (cleft c) :: true :: tl (cright c)).
Proof.
  intros [q l r] c' H Hst.
  destruct q; destruct r as [| b r']; try destruct b;
    crush_step H Hst; repeat split; reflexivity.
Qed.

Lemma pred_D : forall c c', step c = Some c' -> cstate c' = SD ->
  cstate c = SC /\ read c = false /\
  c' = mkCfg SD (tl (cleft c))
                (hd false (cleft c) :: false :: tl (cright c)).
Proof.
  intros [q l r] c' H Hst.
  destruct q; destruct r as [| b r']; try destruct b;
    crush_step H Hst; repeat split; reflexivity.
Qed.

Lemma pred_C : forall c c', step c = Some c' -> cstate c' = SC ->
  (cstate c = SB /\ read c = false /\
   c' = mkCfg SC (true :: cleft c) (tl (cright c))) \/
  (cstate c = SF /\ read c = false /\
   c' = mkCfg SC (tl (cleft c))
                (hd false (cleft c) :: true :: tl (cright c))).
Proof.
  intros [q l r] c' H Hst.
  destruct q; destruct r as [| b r']; try destruct b;
    crush_step H Hst;
    [left | left | right | right]; repeat split; reflexivity.
Qed.

Lemma pred_F : forall c c', step c = Some c' -> cstate c' = SF ->
  (cstate c = SD /\ read c = false /\
   c' = mkCfg SF (true :: cleft c) (tl (cright c))) \/
  (cstate c = SE /\ read c = true /\
   c' = mkCfg SF (tl (cleft c))
                (hd false (cleft c) :: true :: tl (cright c))) \/
  (cstate c = SF /\ read c = true /\
   c' = mkCfg SF (tl (cleft c))
                (hd false (cleft c) :: false :: tl (cright c))).
Proof.
  intros [q l r] c' H Hst.
  destruct q; destruct r as [| b r']; try destruct b;
    crush_step H Hst;
    [left | left | right; left | right; right]; repeat split; reflexivity.
Qed.

Lemma pred_B : forall c c', step c = Some c' -> cstate c' = SB ->
  (cstate c = SA /\ read c = false /\
   c' = mkCfg SB (true :: cleft c) (tl (cright c))) \/
  (cstate c = SB /\ read c = true /\
   c' = mkCfg SB (tl (cleft c))
                (hd false (cleft c) :: true :: tl (cright c))).
Proof.
  intros [q l r] c' H Hst.
  destruct q; destruct r as [| b r']; try destruct b;
    crush_step H Hst;
    [left | left | right]; repeat split; reflexivity.
Qed.

(* ---------------------------------------------------------------- *)
(* M1: the halt criterion.  In zipper form, "C reads 0 at p with     *)
(* tape[p-1] = 1 and tape[p-2] = 0" is: the C-config reads false     *)
(* and its left list begins (in nearest-first order) with a true     *)
(* whose next cell is false-or-absent: hd/tl conditions below.       *)
(* ---------------------------------------------------------------- *)

Lemma M1_fwd : forall n c0 ch,
  run (S (S n)) c0 = Some ch -> step ch = None ->
  exists cc, run n c0 = Some cc /\ cstate cc = SC /\ read cc = false /\
             hd false (cleft cc) = true /\
             hd false (tl (cleft cc)) = false.
Proof.
  intros n c0 ch Hrun Hhalt.
  replace (S (S n)) with (n + 2) in Hrun by lia.
  rewrite run_split in Hrun.
  destruct (run n c0) as [cc |] eqn:E; [| discriminate].
  exists cc. split; [reflexivity |].
  simpl in Hrun.
  destruct (step cc) as [c1 |] eqn:E1; [| discriminate].
  destruct (step c1) as [c2 |] eqn:E2; [| discriminate].
  inversion Hrun; subst c2. clear Hrun.
  apply halt_iff in Hhalt. destruct Hhalt as [Hs Hr].
  destruct (pred_E _ _ E2 Hs) as [Hd [Hdr Hch]].
  destruct (pred_D _ _ E1 Hd) as [Hc [Hcr Hc1]].
  split; [exact Hc |]. split; [exact Hcr |].
  rewrite Hc1 in Hdr. simpl in Hdr.
  rewrite Hch in Hr. rewrite Hc1 in Hr. simpl in Hr.
  split; assumption.
Qed.

Lemma M1_rev : forall cc,
  cstate cc = SC -> read cc = false ->
  hd false (cleft cc) = true -> hd false (tl (cleft cc)) = false ->
  exists c1 ch, step cc = Some c1 /\ step c1 = Some ch /\ step ch = None.
Proof.
  intros cc Hq Hr H1 H2.
  destruct cc as [q l r]. simpl in Hq. subst q.
  unfold read in Hr. simpl in Hr.
  destruct r as [| b r']; [| destruct b; [ simpl in Hr; discriminate | ]].
  - (* cright = [] *)
    destruct l as [| x [| y l']].
    + simpl in H1. discriminate.
    + destruct x; [| simpl in H1; discriminate].
      exists (mkCfg SD [] [true; false]),
             (mkCfg SE [] [false; true; false]).
      repeat split; reflexivity.
    + destruct x; [| simpl in H1; discriminate].
      destruct y; [simpl in H2; discriminate |].
      exists (mkCfg SD (false :: l') [true; false]),
             (mkCfg SE l' [false; true; false]).
      repeat split; reflexivity.
  - (* cright = false :: r' *)
    destruct l as [| x [| y l']].
    + simpl in H1. discriminate.
    + destruct x; [| simpl in H1; discriminate].
      exists (mkCfg SD [] (true :: false :: r')),
             (mkCfg SE [] (false :: true :: false :: r')).
      repeat split; reflexivity.
    + destruct x; [| simpl in H1; discriminate].
      destruct y; [simpl in H2; discriminate |].
      exists (mkCfg SD (false :: l') (true :: false :: r')),
             (mkCfg SE l' (false :: true :: false :: r')).
      repeat split; reflexivity.
Qed.


(* ---------------------------------------------------------------- *)

Lemma M2 : forall ca cb cc,
  step ca = Some cb -> step cb = Some cc ->
  cstate cb = SB -> read cb = false ->
  cstate cc = SC -> read cc = false ->
  hd false (tl (cleft cc)) = true.
Proof.
  intros ca cb cc H1 H2 Hb Hrb Hc Hrc.
  destruct (pred_C _ _ H2 Hc) as [[Hb2 [Hrb2 Hcc]] | [Hf2 _]].
  2: { rewrite Hb in Hf2. discriminate. }
  destruct (pred_B _ _ H1 Hb) as [[Ha [Hra Hcb]] | [Hb3 [Hrb3 Hcb]]].
  - (* B entered from A-on-0: cb's left begins with a true written
       by A, so cc's second-left cell is true. *)
    rewrite Hcc. rewrite Hcb. simpl. reflexivity.
  - (* B entered from B-on-1: then cb's head cell came from ca's
       left; cb reads false forces that cell false, and cc reads
       the true that B-on-1 wrote: contradiction with Hrc. *)
    rewrite Hcc in Hrc. rewrite Hcb in Hrc. simpl in Hrc.
    discriminate.
Qed.

(* ---------------------------------------------------------------- *)
(* M3: the D-on-0 route into F is safe: if C was entered from an     *)
(* F-on-0 step and that F was entered from D-on-0, then C reads the  *)
(* 1 that D wrote, so M1 does not apply.                             *)
(* ---------------------------------------------------------------- *)

Lemma M3 : forall cd cf cc,
  step cd = Some cf -> step cf = Some cc ->
  cstate cd = SD -> read cd = false ->
  cstate cf = SF -> read cf = false ->
  cstate cc = SC -> read cc = true.
Proof.
  intros cd cf cc H1 H2 Hd Hrd Hf Hrf Hc.
  destruct (pred_F _ _ H1 Hf) as [[Hd2 [Hrd2 Hcf]] |
                                  [[He2 _] | [Hf2 _]]].
  2: { rewrite Hd in He2. discriminate. }
  2: { rewrite Hd in Hf2. discriminate. }
  destruct (pred_C _ _ H2 Hc) as [[Hb2 _] | [Hf3 [Hrf3 Hcc]]].
  - rewrite Hf in Hb2. discriminate.
  - rewrite Hcc. rewrite Hcf. simpl. reflexivity.
Qed.

(* ---------------------------------------------------------------- *)
(* M4: the dangerous pattern.  Halting (from the blank tape) is      *)
(* equivalent to some F-on-0 step whose left triple, nearest-first   *)
(* (tape[q-1], tape[q-2], tape[q-3]), is (false, true, false): an    *)
(* isolated 1 two cells left of the 0 F reads, with a 0 between.     *)
(* ---------------------------------------------------------------- *)

Definition danger (cf : config) : Prop :=
  cstate cf = SF /\ read cf = false /\
  hd false (cleft cf) = false /\
  hd false (tl (cleft cf)) = true /\
  hd false (tl (tl (cleft cf))) = false.

Lemma M4_rev_local : forall cf, danger cf ->
  exists cc c1 ch, step cf = Some cc /\ step cc = Some c1 /\
                   step c1 = Some ch /\ step ch = None.
Proof.
  intros cf [Hq [Hr [H1 [H2 H3]]]].
  destruct cf as [q l r]. simpl in Hq. subst q.
  unfold read in Hr. simpl in Hr.
  destruct r as [| b r']; [| destruct b; [ simpl in Hr; discriminate | ]].
  - (* cright = [] *)
    destruct l as [| x [| y [| z l']]].
    + simpl in H2. discriminate.
    + simpl in H2. discriminate.
    + destruct x; [simpl in H1; discriminate |].
      destruct y; [| simpl in H2; discriminate].
      exists (mkCfg SC [true] [false; true]),
             (mkCfg SD [] [true; false; true]),
             (mkCfg SE [] [false; true; false; true]).
      repeat split; reflexivity.
    + destruct x; [simpl in H1; discriminate |].
      destruct y; [| simpl in H2; discriminate].
      destruct z; [simpl in H3; discriminate |].
      exists (mkCfg SC (true :: false :: l') [false; true]),
             (mkCfg SD (false :: l') [true; false; true]),
             (mkCfg SE l' [false; true; false; true]).
      repeat split; reflexivity.
  - (* cright = false :: r' *)
    destruct l as [| x [| y [| z l']]].
    + simpl in H2. discriminate.
    + simpl in H2. discriminate.
    + destruct x; [simpl in H1; discriminate |].
      destruct y; [| simpl in H2; discriminate].
      exists (mkCfg SC [true] (false :: true :: r')),
             (mkCfg SD [] (true :: false :: true :: r')),
             (mkCfg SE [] (false :: true :: false :: true :: r')).
      repeat split; reflexivity.
    + destruct x; [simpl in H1; discriminate |].
      destruct y; [| simpl in H2; discriminate].
      destruct z; [simpl in H3; discriminate |].
      exists (mkCfg SC (true :: false :: l') (false :: true :: r')),
             (mkCfg SD (false :: l') (true :: false :: true :: r')),
             (mkCfg SE l' (false :: true :: false :: true :: r')).
      repeat split; reflexivity.
Qed.


Lemma run3 : forall c ch, run 3 c = Some ch ->
  exists c1 c2, step c = Some c1 /\ step c1 = Some c2 /\
                step c2 = Some ch.
Proof.
  intros c ch H. simpl in H.
  destruct (step c) as [c1 |] eqn:E1; [| discriminate].
  destruct (step c1) as [c2 |] eqn:E2; [| discriminate].
  destruct (step c2) as [c3 |] eqn:E3; [| discriminate].
  inversion H; subst c3.
  exists c1, c2. repeat split; assumption.
Qed.

Lemma M4_fwd : forall n ch,
  run (S (S (S n))) cfg_blank = Some ch -> step ch = None ->
  exists cf, run n cfg_blank = Some cf /\ danger cf /\
             exists cc c1, step cf = Some cc /\ step cc = Some c1 /\
                           step c1 = Some ch.
Proof.
  intros n ch Hrun Hhalt.
  destruct (M1_fwd (S n) cfg_blank ch Hrun Hhalt)
    as [cc [Ecc [Hc [Hrc [Hp1 Hp2]]]]].
  replace (S n) with (n + 1) in Ecc by lia.
  rewrite run_split in Ecc.
  destruct (run n cfg_blank) as [cf |] eqn:Ec; [| discriminate].
  simpl in Ecc.
  destruct (step cf) as [cc' |] eqn:Es; [| discriminate].
  injection Ecc as Hcc'. subst cc'.
  exists cf. split; [reflexivity |].
  replace (S (S (S n))) with (n + 3) in Hrun by lia.
  rewrite run_split in Hrun. rewrite Ec in Hrun.
  destruct (run3 _ _ Hrun) as [cc' [c1 [Es' [Ec1' Ec2']]]].
  assert (Hcc' : cc' = cc) by congruence.
  subst cc'.
  assert (Hdanger : danger cf).
  { destruct (pred_C _ _ Es Hc)
      as [[Hb [Hrb Hcc]] | [Hf [Hrf Hcc]]].
    - (* B-entry: excluded by M2, using cf's predecessor in the run
         (or cf = cfg_blank when n = 0, whose state is SA). *)
      destruct n as [| n'].
      + simpl in Ec. injection Ec as Hcf. subst cf.
        simpl in Hb. discriminate.
      + replace (S n') with (n' + 1) in Ec by lia.
        rewrite run_split in Ec.
        destruct (run n' cfg_blank) as [ca |] eqn:Ea;
          [| discriminate].
        simpl in Ec.
        destruct (step ca) as [cf' |] eqn:Esca; [| discriminate].
        injection Ec as Hcf. subst cf'.
        assert (hd false (tl (cleft cc)) = true) as Hcontra.
        { eapply M2; [ exact Esca | exact Es | exact Hb
                     | exact Hrb | exact Hc | exact Hrc ]. }
        rewrite Hp2 in Hcontra. discriminate.
    - (* F-entry: all three danger components are M1's data read
         through the F-step shape: cc's head cell is cf's left
         neighbour (so read cc = tape[q-1]), and cc's left list is
         cf's left list shifted by one.  No entry case analysis is
         needed in the zipper formulation. *)
      unfold danger.
      split; [exact Hf |]. split; [exact Hrf |].
      rewrite Hcc in Hp1. simpl in Hp1.
      rewrite Hcc in Hp2. simpl in Hp2.
      rewrite Hcc in Hrc. simpl in Hrc.
      split; [exact Hrc |]. split; [exact Hp1 |]. exact Hp2. }

  split; [exact Hdanger |].
  exists cc, c1. split; [exact Es |]. split; [exact Ec1' |].
  exact Ec2'.
Qed.


(* M4, global form: from the blank tape, the machine halts iff a
   dangerous F-on-0 configuration occurs in the execution. *)
Lemma M4_halt_iff :
  (exists n ch, run n cfg_blank = Some ch /\ step ch = None) <->
  (exists n cf, run n cfg_blank = Some cf /\ danger cf).
Proof.
  split.
  - intros [n [ch [Hrun Hhalt]]].
    destruct n as [| [| [| n']]].
    + simpl in Hrun. inversion Hrun; subst ch.
      simpl in Hhalt. discriminate.
    + simpl in Hrun. inversion Hrun; subst ch.
      simpl in Hhalt. discriminate.
    + (* n = 2: the halting config would have to be reached in 2
         steps; M1_fwd applies with n := 0 and yields a C-config
         at step 0, but cfg_blank is in state SA. *)
      destruct (M1_fwd 0 cfg_blank ch Hrun Hhalt)
        as [cc [Ecc [Hc _]]].
      simpl in Ecc. inversion Ecc; subst cc.
      simpl in Hc. discriminate.
    + destruct (M4_fwd n' ch Hrun Hhalt)
        as [cf [Ecf [Hdanger _]]].
      exists n', cf. split; assumption.
  - intros [n [cf [Hrun Hdanger]]].
    destruct (M4_rev_local cf Hdanger) as [cc [c1 [ch [S1 [S2 [S3 S4]]]]]].
    exists (n + 3), ch. split; [| exact S4].
    replace (n + 3) with (n + 3) by lia.
    rewrite run_split.
    rewrite Hrun. simpl.
    rewrite S1, S2, S3. reflexivity.
Qed.
