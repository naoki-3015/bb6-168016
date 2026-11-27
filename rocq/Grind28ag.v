(* ================================================================= *)
(* Phase 60 (companion): the CASCADE60 prelude -- the sec_eq /     *)
(* closearith tactics, the NUM60ss repeat identities, the REP60    *)
(* repeat-list identities and the NUM60X factored numeral          *)
(* identities of CASCADE60.  Split out of Grind28.v: proved in a   *)
(* fresh process, the ~70 vm-proved identities peak ~4.8 GB of     *)
(* in-process conversion garbage; loaded as a .vo by the segment   *)
(* files they cost only the ~0.2 GB resident baseline (probes:     *)
(* build-logs-60/probes.txt).                                      *)
(* ================================================================= *)

Require Import List Bool Arith Lia ZArith.
Import ListNotations.
Require Import TM Sections Mirror TokenPass Recoord Era Esc Dev
               Grind Grind2 Grind3 Grind4 Grind5 Grind6 Grind7 Grind8
               Grind9 Grind10 Grind11 Grind12 Grind13 Grind14 Grind15
               Grind16 Grind17 Grind18 Grind19 Grind20 Grind21 Grind22
               Grind23 Grind24 Grind25 Grind26 Grind26a Grind26b
               Grind26c Grind26d Grind26e Grind26f Grind26g Grind27a
               Grind27b Grind27c Grind27d Grind27e Grind27f Grind27g
               Grind28a.

(* Section equality: componentwise, arithmetic leaves by lia.      *)
Ltac sec_eq :=
  repeat (first [ solve [reflexivity] | solve [lia] | f_equal ]).

(* Closed-numeral arithmetic: literals >= 7426 are parsed as       *)
(* Nat.of_num_uint atoms, which lia cannot relate to variables;    *)
(* for purely closed <= goals the boolean check decides them.      *)
Ltac closearith :=
  first [ lia | apply Nat.leb_le; reflexivity ].

(* Factored list identities for the PX2A steps of           *)
(* CASCADE60 whose produced (1, 2)s merge into a spine      *)
(* repeat of length > 175000 (auto-detected by gen59.py):   *)
(* the goal's stated target is first rewritten to the       *)
(* constructor's unmerged form via REP60a-c (whose proofs   *)
(* proofs rewrite the run length to S-form and close by     *)
(* reflexivity), and the frame atoms are put in S-form via  *)
(* the NUM60t<step>1-3 lemmas, since hPX2A's frame pattern *)
(* is S (S (S b')) :: S p' :: pb and its target counter is  *)
(* S b' (the CASCADE55 step-1 pattern, generalised).       *)
Lemma NUM60ssa : 58806192 = S (S 58806190).
Proof. apply Nat.eqb_eq; vm_compute; reflexivity. Qed.
Lemma REP60a : forall w,
  (1, 1) :: (1, 2) :: (1, 2) :: repeat (1, 2) 58806190 ++ w
  = (1, 1) :: repeat (1, 2) 58806192 ++ w.
Proof. intro w. rewrite NUM60ssa. reflexivity. Qed.
Lemma NUM60ta1 : 34304475 = S (S (S 34304472)).
Proof. apply Nat.eqb_eq; vm_compute; reflexivity. Qed.
Lemma NUM60ta2 : 7965811 = S 7965810.
Proof. apply Nat.eqb_eq; vm_compute; reflexivity. Qed.
Lemma NUM60ta3 : 34304473 = S 34304472.
Proof. apply Nat.eqb_eq; vm_compute; reflexivity. Qed.
Lemma NUM60ssb : 7965811 = S (S 7965809).
Proof. apply Nat.eqb_eq; vm_compute; reflexivity. Qed.
Lemma REP60b : forall w,
  (1, 1) :: (1, 2) :: (1, 2) :: repeat (1, 2) 7965809 ++ w
  = (1, 1) :: repeat (1, 2) 7965811 ++ w.
Proof. intro w. rewrite NUM60ssb. reflexivity. Qed.
Lemma NUM60tb1 : 4012920 = S (S (S 4012917)).
Proof. apply Nat.eqb_eq; vm_compute; reflexivity. Qed.
Lemma NUM60tb2 : 308090 = S 308089.
Proof. apply Nat.eqb_eq; vm_compute; reflexivity. Qed.
Lemma NUM60tb3 : 4012918 = S 4012917.
Proof. apply Nat.eqb_eq; vm_compute; reflexivity. Qed.
Lemma NUM60ssc : 308090 = S (S 308088).
Proof. apply Nat.eqb_eq; vm_compute; reflexivity. Qed.
Lemma REP60c : forall w,
  (1, 1) :: (1, 2) :: (1, 2) :: repeat (1, 2) 308088 ++ w
  = (1, 1) :: repeat (1, 2) 308090 ++ w.
Proof. intro w. rewrite NUM60ssc. reflexivity. Qed.
Lemma NUM60tc1 : 49409 = S (S (S 49406)).
Proof. apply Nat.eqb_eq; vm_compute; reflexivity. Qed.
Lemma NUM60tc2 : 7710 = S 7709.
Proof. apply Nat.eqb_eq; vm_compute; reflexivity. Qed.
Lemma NUM60tc3 : 49407 = S 49406.
Proof. apply Nat.eqb_eq; vm_compute; reflexivity. Qed.
Lemma NUM60ssd : 618004 = S (S 618002).
Proof. apply Nat.eqb_eq; vm_compute; reflexivity. Qed.
Lemma REP60d : forall w,
  (1, 1) :: (1, 2) :: (1, 2) :: repeat (1, 2) 618002 ++ w
  = (1, 1) :: repeat (1, 2) 618004 ++ w.
Proof. intro w. rewrite NUM60ssd. reflexivity. Qed.
Lemma NUM60td1 : 340258 = S (S (S 340255)).
Proof. apply Nat.eqb_eq; vm_compute; reflexivity. Qed.
Lemma NUM60td2 : 16817 = S 16816.
Proof. apply Nat.eqb_eq; vm_compute; reflexivity. Qed.
Lemma NUM60td3 : 340256 = S 340255.
Proof. apply Nat.eqb_eq; vm_compute; reflexivity. Qed.


(* Closed arithmetic identities for the large DIPGRIND /   *)
(* hGRIND_even / CLEANG steps and the head-pair             *)
(* normalisations of CASCADE60, factored into standalone    *)
(* lemmas (eqb/vm proofs) and rewritten in the step blocks, *)
(* so the applies meet the lemmas' arithmetic forms        *)
(* syntactically instead of by a closed multiplication or   *)
(* subtraction conversion at depth >= 100000                *)
(* (cf. the NUM60ss / REP60 lemmas).                       *)
Lemma NUM60X1 : 7965810 = S 7965809.
Proof. apply Nat.eqb_eq; vm_compute; reflexivity. Qed.
Lemma NUM60X2 : 34304471 = 34304473 - 2.
Proof. apply Nat.eqb_eq; vm_compute; reflexivity. Qed.
Lemma NUM60X3 : 34304469 = 34304471 - 2.
Proof. apply Nat.eqb_eq; vm_compute; reflexivity. Qed.
Lemma NUM60X4 : 34304469 = 2 * 7965809 + 18372851.
Proof. apply Nat.eqb_eq; vm_compute; reflexivity. Qed.
Lemma NUM60X5 : 308089 = S 308088.
Proof. apply Nat.eqb_eq; vm_compute; reflexivity. Qed.
Lemma NUM60X6 : 4012916 = 4012918 - 2.
Proof. apply Nat.eqb_eq; vm_compute; reflexivity. Qed.
Lemma NUM60X7 : 4012914 = 4012916 - 2.
Proof. apply Nat.eqb_eq; vm_compute; reflexivity. Qed.
Lemma NUM60X8 : 4012914 = 2 * 308088 + 3396738.
Proof. apply Nat.eqb_eq; vm_compute; reflexivity. Qed.
Lemma NUM60X9 : 8166 = S 8165.
Proof. apply Nat.eqb_eq; vm_compute; reflexivity. Qed.
Lemma NUM60X10 : 16817 = S 16816.
Proof. apply Nat.eqb_eq; vm_compute; reflexivity. Qed.
Lemma NUM60X11 : 618002 = 618003 - 1.
Proof. apply Nat.eqb_eq; vm_compute; reflexivity. Qed.
Lemma NUM60X12 : 3396736 = 3396738 - 2.
Proof. apply Nat.eqb_eq; vm_compute; reflexivity. Qed.
Lemma NUM60X13 : 618002 = 2 * 308999 + 4.
Proof. apply Nat.eqb_eq; vm_compute; reflexivity. Qed.
Lemma NUM60X14 : 340258 = S 340257.
Proof. apply Nat.eqb_eq; vm_compute; reflexivity. Qed.
Lemma NUM60X15 : 618002 = S 618001.
Proof. apply Nat.eqb_eq; vm_compute; reflexivity. Qed.
Lemma NUM60X16 : 340258 = S 340257.
Proof. apply Nat.eqb_eq; vm_compute; reflexivity. Qed.
Lemma NUM60X17 : 3396734 = 3396736 - 2.
Proof. apply Nat.eqb_eq; vm_compute; reflexivity. Qed.
Lemma NUM60X18 : 3396732 = 3396734 - 2.
Proof. apply Nat.eqb_eq; vm_compute; reflexivity. Qed.
Lemma NUM60X19 : 3396732 = 2 * 618002 + 2160728.
Proof. apply Nat.eqb_eq; vm_compute; reflexivity. Qed.
Lemma NUM60X20 : 340254 = 340256 - 2.
Proof. apply Nat.eqb_eq; vm_compute; reflexivity. Qed.
Lemma NUM60X21 : 340252 = 340254 - 2.
Proof. apply Nat.eqb_eq; vm_compute; reflexivity. Qed.
Lemma NUM60X22 : 340252 = 2 * 16815 + 306622.
Proof. apply Nat.eqb_eq; vm_compute; reflexivity. Qed.
Lemma NUM60X23 : 306620 = 306622 - 2.
Proof. apply Nat.eqb_eq; vm_compute; reflexivity. Qed.
Lemma NUM60X24 : 18976 = S 18975.
Proof. apply Nat.eqb_eq; vm_compute; reflexivity. Qed.
Lemma NUM60X25 : 306618 = 306620 - 2.
Proof. apply Nat.eqb_eq; vm_compute; reflexivity. Qed.
Lemma NUM60X26 : 306616 = 306618 - 2.
Proof. apply Nat.eqb_eq; vm_compute; reflexivity. Qed.
Lemma NUM60X27 : 306616 = 2 * 37738 + 231140.
Proof. apply Nat.eqb_eq; vm_compute; reflexivity. Qed.
Lemma NUM60X28 : 231138 = 231140 - 2.
Proof. apply Nat.eqb_eq; vm_compute; reflexivity. Qed.
Lemma NUM60X29 : 75482 = 2 * 37739 + 4.
Proof. apply Nat.eqb_eq; vm_compute; reflexivity. Qed.
Lemma NUM60X30 : 43275 = S 43274.
Proof. apply Nat.eqb_eq; vm_compute; reflexivity. Qed.
Lemma NUM60X31 : 231136 = 231138 - 2.
Proof. apply Nat.eqb_eq; vm_compute; reflexivity. Qed.
Lemma NUM60X32 : 231134 = 231136 - 2.
Proof. apply Nat.eqb_eq; vm_compute; reflexivity. Qed.
Lemma NUM60X33 : 231134 = 2 * 75482 + 80170.
Proof. apply Nat.eqb_eq; vm_compute; reflexivity. Qed.
Lemma NUM60X34 : 10129 = S 10128.
Proof. apply Nat.eqb_eq; vm_compute; reflexivity. Qed.
Lemma NUM60X35 : 177444 = 177445 - 1.
Proof. apply Nat.eqb_eq; vm_compute; reflexivity. Qed.
Lemma NUM60X36 : 177444 = 2 * 88720 + 4.
Proof. apply Nat.eqb_eq; vm_compute; reflexivity. Qed.
Lemma NUM60X37 : 95640 = S 95639.
Proof. apply Nat.eqb_eq; vm_compute; reflexivity. Qed.
Lemma NUM60X38 : 177444 = S 177443.
Proof. apply Nat.eqb_eq; vm_compute; reflexivity. Qed.
Lemma NUM60X39 : 80164 = 2 * 40081 + 2.
Proof. apply Nat.eqb_eq; vm_compute; reflexivity. Qed.
Lemma NUM60X40 : 80168 = 2 * 40081 + 6.
Proof. apply Nat.eqb_eq; vm_compute; reflexivity. Qed.
Lemma NUM60X41 : 177445 = S 177444.
Proof. apply Nat.eqb_eq; vm_compute; reflexivity. Qed.
Lemma NUM60X42 : 1236010 = 1236011 - 1.
Proof. apply Nat.eqb_eq; vm_compute; reflexivity. Qed.
Lemma NUM60X43 : 2160726 = 2160728 - 2.
Proof. apply Nat.eqb_eq; vm_compute; reflexivity. Qed.
Lemma NUM60X44 : 1236010 = 2 * 618003 + 4.
Proof. apply Nat.eqb_eq; vm_compute; reflexivity. Qed.
Lemma NUM60X45 : 698173 = S 698172.
Proof. apply Nat.eqb_eq; vm_compute; reflexivity. Qed.
Lemma NUM60X46 : 1236010 = S 1236009.
Proof. apply Nat.eqb_eq; vm_compute; reflexivity. Qed.
Lemma NUM60X47 : 698173 = S 698172.
Proof. apply Nat.eqb_eq; vm_compute; reflexivity. Qed.
Lemma NUM60X48 : 2160724 = 2160726 - 2.
Proof. apply Nat.eqb_eq; vm_compute; reflexivity. Qed.
Lemma NUM60X49 : 2160722 = 2160724 - 2.
Proof. apply Nat.eqb_eq; vm_compute; reflexivity. Qed.
Lemma NUM60X50 : 2160722 = 2 * 1080360 + 2.
Proof. apply Nat.eqb_eq; vm_compute; reflexivity. Qed.
Lemma NUM60X51 : 2160726 = 2 * 1080360 + 6.
Proof. apply Nat.eqb_eq; vm_compute; reflexivity. Qed.
Lemma NUM60X52 : 2160726 = S 2160725.
Proof. apply Nat.eqb_eq; vm_compute; reflexivity. Qed.
Lemma NUM60X53 : 2160727 = S (S 2160725).
Proof. apply Nat.eqb_eq; vm_compute; reflexivity. Qed.
Lemma NUM60X54 : 1236011 = S 1236010.
Proof. apply Nat.eqb_eq; vm_compute; reflexivity. Qed.
Lemma NUM60X55 : 15931624 = 15931625 - 1.
Proof. apply Nat.eqb_eq; vm_compute; reflexivity. Qed.
Lemma NUM60X56 : 18372849 = 18372851 - 2.
Proof. apply Nat.eqb_eq; vm_compute; reflexivity. Qed.
Lemma NUM60X57 : 15931624 = 2 * 7965810 + 4.
Proof. apply Nat.eqb_eq; vm_compute; reflexivity. Qed.
Lemma NUM60X58 : 10126538 = S 10126537.
Proof. apply Nat.eqb_eq; vm_compute; reflexivity. Qed.
Lemma NUM60X59 : 15931624 = S 15931623.
Proof. apply Nat.eqb_eq; vm_compute; reflexivity. Qed.
Lemma NUM60X60 : 10126538 = S 10126537.
Proof. apply Nat.eqb_eq; vm_compute; reflexivity. Qed.
Lemma NUM60X61 : 18372847 = 18372849 - 2.
Proof. apply Nat.eqb_eq; vm_compute; reflexivity. Qed.
Lemma NUM60X62 : 18372845 = 18372847 - 2.
Proof. apply Nat.eqb_eq; vm_compute; reflexivity. Qed.
Lemma NUM60X63 : 18372845 = 2 * 9186421 + 3.
Proof. apply Nat.eqb_eq; vm_compute; reflexivity. Qed.
Lemma NUM60X64 : 18372850 = 2 * 9186421 + 8.
Proof. apply Nat.eqb_eq; vm_compute; reflexivity. Qed.
Lemma NUM60X65 : 15931626 = S 15931625.
Proof. apply Nat.eqb_eq; vm_compute; reflexivity. Qed.
Lemma NUM60X66 : 18372853 = 18372852 + 1.
Proof. apply Nat.eqb_eq; vm_compute; reflexivity. Qed.


