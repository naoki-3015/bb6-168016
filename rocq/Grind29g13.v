(* ================================================================= *)
(* Phase 61: CASCADE61 segments CASCADE61x. *)
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
               Grind29e10 Grind29e11 Grind29e4 Grind29e8 Grind29e9 Grind29rep Grind29g12.

(* Section equality: componentwise, arithmetic leaves by lia.      *)
Ltac sec_eq :=
  repeat (first [ solve [reflexivity] | solve [lia] | f_equal ]).

(* Closed-numeral arithmetic: literals >= 7426 are parsed as       *)
(* Nat.of_num_uint atoms, which lia cannot relate to variables;    *)
(* for purely closed <= goals the boolean check decides them.      *)
Ltac closearith :=
  first [ lia
        | cbn [Nat.of_num_uint Nat.of_uint Nat.of_uint_acc];
          try (rewrite !Nat.tail_mul_spec); nia ].

Lemma CASCADE61x : forall w,
  hsteps (HB [120150; 23739; 16527; 2607; 991; 619; 109; 19; 0] 891038 1 1713261 ((8340443, 2) :: (1, 1) :: repeat (1, 2) 21489090 ++ (11506558, 2) :: (1, 1) :: repeat (1, 2) 135985238 ++ w) 1)
         (HB [2607; 991; 619; 109; 19; 0] 16527 1 23741 (repeat (1, 2) 120150 ++ (650736, 2) :: (1, 1) :: repeat (1, 2) 1713262 ++ (4913917, 2) :: (1, 1) :: repeat (1, 2) 21489090 ++ (11506558, 2) :: (1, 1) :: repeat (1, 2) 135985238 ++ w) 1).
Proof.
  intro w.
  (* step 682: sTUP *)
  apply (hsteps_trans _ (HC [120150; 23739; 16527; 2607; 991; 619; 109; 19; 0] 891038 1713260 2 ((8340441, 2) :: (1, 1) :: repeat (1, 2) 21489090 ++ (11506558, 2) :: (1, 1) :: repeat (1, 2) 135985238 ++ w) 1)).
  {
    rewrite NUM61X68.
    rewrite NUM61X69.
    apply (sTUP [120150; 23739; 16527; 2607; 991; 619; 109; 19; 0] 891038 1713261 8340443 2 ((1, 1) :: repeat (1, 2) 21489090 ++ (11506558, 2) :: (1, 1) :: repeat (1, 2) 135985238 ++ w) 1); closearith.
  }
  (* step 683: hGRIND_even 856628 *)
  apply (hsteps_trans _ (HB [120150; 23739; 16527; 2607; 991; 619; 109; 19; 0] 891037 1 1713260 ((2, 2) :: (8340441, 2) :: (1, 1) :: repeat (1, 2) 21489090 ++ (11506558, 2) :: (1, 1) :: repeat (1, 2) 135985238 ++ w) 1)).
  {
    rewrite NUM61X70.
    rewrite NUM61X71.
    apply (hGRIND_even 856628 [120150; 23739; 16527; 2607; 991; 619; 109; 19; 0] 891037 ((8340441, 2) :: (1, 1) :: repeat (1, 2) 21489090 ++ (11506558, 2) :: (1, 1) :: repeat (1, 2) 135985238 ++ w) 1); closearith.
  }
  (* step 684: P TUP2_1 *)
  apply (hsteps_trans _ (HC [891038; 120150; 23739; 16527; 2607; 991; 619; 109; 19; 0] 1713260 1 2 ((8340439, 2) :: (1, 1) :: repeat (1, 2) 21489090 ++ (11506558, 2) :: (1, 1) :: repeat (1, 2) 135985238 ++ w) 1)).
  {
    rewrite NUM61X72.
    rewrite NUM61X73.
    rewrite NUM61X74.
    apply (sTUP2_1 [120150; 23739; 16527; 2607; 991; 619; 109; 19; 0] 891037 1713259 8340441 ((1, 1) :: repeat (1, 2) 21489090 ++ (11506558, 2) :: (1, 1) :: repeat (1, 2) 135985238 ++ w) 1); closearith.
  }
  (* step 685: P TDN *)
  apply (hsteps_trans _ (HB [891038; 120150; 23739; 16527; 2607; 991; 619; 109; 19; 0] 1713260 1 4 ((8340439, 2) :: (1, 1) :: repeat (1, 2) 21489090 ++ (11506558, 2) :: (1, 1) :: repeat (1, 2) 135985238 ++ w) 1)).
  {
    apply (sTDN [891038; 120150; 23739; 16527; 2607; 991; 619; 109; 19; 0] 1713260 ((8340439, 2) :: (1, 1) :: repeat (1, 2) 21489090 ++ (11506558, 2) :: (1, 1) :: repeat (1, 2) 135985238 ++ w) 1).
  }
  (* step 686: sTUP *)
  apply (hsteps_trans _ (HC [891038; 120150; 23739; 16527; 2607; 991; 619; 109; 19; 0] 1713260 3 2 ((8340437, 2) :: (1, 1) :: repeat (1, 2) 21489090 ++ (11506558, 2) :: (1, 1) :: repeat (1, 2) 135985238 ++ w) 1)).
  {
    rewrite NUM61X75.
    apply (sTUP [891038; 120150; 23739; 16527; 2607; 991; 619; 109; 19; 0] 1713260 4 8340439 2 ((1, 1) :: repeat (1, 2) 21489090 ++ (11506558, 2) :: (1, 1) :: repeat (1, 2) 135985238 ++ w) 1); closearith.
  }
  (* step 687: DIPGRIND 1713260 4913917 *)
  apply (hsteps_trans _ (HC [891038; 120150; 23739; 16527; 2607; 991; 619; 109; 19; 0] 0 3 2 (repeat (1, 2) 1713260 ++ (4913917, 2) :: (1, 1) :: repeat (1, 2) 21489090 ++ (11506558, 2) :: (1, 1) :: repeat (1, 2) 135985238 ++ w) 1)).
  {
    rewrite NUM61X76.
    apply (DIPGRIND 1713260 4913917 [891038; 120150; 23739; 16527; 2607; 991; 619; 109; 19; 0] ((1, 1) :: repeat (1, 2) 21489090 ++ (11506558, 2) :: (1, 1) :: repeat (1, 2) 135985238 ++ w) 1); closearith.
  }
  (* step 688: P PX2A *)
  apply (hsteps_trans _ (HC [23739; 16527; 2607; 991; 619; 109; 19; 0] 120149 891036 2 ((1, 1) :: repeat (1, 2) 1713262 ++ (4913917, 2) :: (1, 1) :: repeat (1, 2) 21489090 ++ (11506558, 2) :: (1, 1) :: repeat (1, 2) 135985238 ++ w) 1)).
  {
    rewrite NUM61tg1. rewrite NUM61tg2. rewrite NUM61tg3.
    replace ((1, 1) :: repeat (1, 2) 1713262 ++ (4913917, 2) :: (1, 1) :: repeat (1, 2) 21489090 ++ (11506558, 2) :: (1, 1) :: repeat (1, 2) 135985238 ++ w)
      with ((1, 1) :: (1, 2) :: (1, 2) :: repeat (1, 2) 1713260 ++ (4913917, 2) :: (1, 1) :: repeat (1, 2) 21489090 ++ (11506558, 2) :: (1, 1) :: repeat (1, 2) 135985238 ++ w)
      by (apply REP61g).
    exact (hsteps_step _ _ _ (hPX2A 891035 120149 [23739; 16527; 2607; 991; 619; 109; 19; 0] (repeat (1, 2) 1713260 ++ (4913917, 2) :: (1, 1) :: repeat (1, 2) 21489090 ++ (11506558, 2) :: (1, 1) :: repeat (1, 2) 135985238 ++ w) 1) (hsteps_refl _)).
  }
  (* step 689: P PUSH *)
  apply (hsteps_trans _ (HC [23739; 16527; 2607; 991; 619; 109; 19; 0] 120148 1 2 ((891034, 2) :: (1, 1) :: repeat (1, 2) 1713262 ++ (4913917, 2) :: (1, 1) :: repeat (1, 2) 21489090 ++ (11506558, 2) :: (1, 1) :: repeat (1, 2) 135985238 ++ w) 1)).
  {
    rewrite NUM61X77.
    rewrite NUM61X78.
    apply (sPUSH [23739; 16527; 2607; 991; 619; 109; 19; 0] 120148 891036 ((1, 1) :: repeat (1, 2) 1713262 ++ (4913917, 2) :: (1, 1) :: repeat (1, 2) 21489090 ++ (11506558, 2) :: (1, 1) :: repeat (1, 2) 135985238 ++ w) 1); closearith.
  }
  (* step 690: P TDN *)
  apply (hsteps_trans _ (HB [23739; 16527; 2607; 991; 619; 109; 19; 0] 120148 1 4 ((891034, 2) :: (1, 1) :: repeat (1, 2) 1713262 ++ (4913917, 2) :: (1, 1) :: repeat (1, 2) 21489090 ++ (11506558, 2) :: (1, 1) :: repeat (1, 2) 135985238 ++ w) 1)).
  {
    apply (sTDN [23739; 16527; 2607; 991; 619; 109; 19; 0] 120148 ((891034, 2) :: (1, 1) :: repeat (1, 2) 1713262 ++ (4913917, 2) :: (1, 1) :: repeat (1, 2) 21489090 ++ (11506558, 2) :: (1, 1) :: repeat (1, 2) 135985238 ++ w) 1).
  }
  (* step 691: sTUP *)
  apply (hsteps_trans _ (HC [23739; 16527; 2607; 991; 619; 109; 19; 0] 120148 3 2 ((891032, 2) :: (1, 1) :: repeat (1, 2) 1713262 ++ (4913917, 2) :: (1, 1) :: repeat (1, 2) 21489090 ++ (11506558, 2) :: (1, 1) :: repeat (1, 2) 135985238 ++ w) 1)).
  {
    rewrite NUM61X79.
    apply (sTUP [23739; 16527; 2607; 991; 619; 109; 19; 0] 120148 4 891034 2 ((1, 1) :: repeat (1, 2) 1713262 ++ (4913917, 2) :: (1, 1) :: repeat (1, 2) 21489090 ++ (11506558, 2) :: (1, 1) :: repeat (1, 2) 135985238 ++ w) 1); closearith.
  }
  (* step 692: DIPGRIND 120148 650736 *)
  apply (hsteps_trans _ (HC [23739; 16527; 2607; 991; 619; 109; 19; 0] 0 3 2 (repeat (1, 2) 120148 ++ (650736, 2) :: (1, 1) :: repeat (1, 2) 1713262 ++ (4913917, 2) :: (1, 1) :: repeat (1, 2) 21489090 ++ (11506558, 2) :: (1, 1) :: repeat (1, 2) 135985238 ++ w) 1)).
  {
    rewrite NUM61X80.
    apply (DIPGRIND 120148 650736 [23739; 16527; 2607; 991; 619; 109; 19; 0] ((1, 1) :: repeat (1, 2) 1713262 ++ (4913917, 2) :: (1, 1) :: repeat (1, 2) 21489090 ++ (11506558, 2) :: (1, 1) :: repeat (1, 2) 135985238 ++ w) 1); closearith.
  }
  (* step 693: P PX2A *)
  apply (hsteps_trans _ (HC [2607; 991; 619; 109; 19; 0] 16526 23737 2 ((1, 1) :: repeat (1, 2) 120150 ++ (650736, 2) :: (1, 1) :: repeat (1, 2) 1713262 ++ (4913917, 2) :: (1, 1) :: repeat (1, 2) 21489090 ++ (11506558, 2) :: (1, 1) :: repeat (1, 2) 135985238 ++ w) 1)).
  {
    exact (hsteps_step _ _ _ (hPX2A 23736 16526 [2607; 991; 619; 109; 19; 0] (repeat (1, 2) 120148 ++ (650736, 2) :: (1, 1) :: repeat (1, 2) 1713262 ++ (4913917, 2) :: (1, 1) :: repeat (1, 2) 21489090 ++ (11506558, 2) :: (1, 1) :: repeat (1, 2) 135985238 ++ w) 1) (hsteps_refl _)).
  }
  (* step 694: hGRIND 11867 *)
  apply (hsteps_trans _ (HB [2607; 991; 619; 109; 19; 0] 16526 1 23740 ((1, 1) :: repeat (1, 2) 120150 ++ (650736, 2) :: (1, 1) :: repeat (1, 2) 1713262 ++ (4913917, 2) :: (1, 1) :: repeat (1, 2) 21489090 ++ (11506558, 2) :: (1, 1) :: repeat (1, 2) 135985238 ++ w) 1)).
  {
    apply (hGRIND 11867 [2607; 991; 619; 109; 19; 0] 16526 ((1, 1) :: repeat (1, 2) 120150 ++ (650736, 2) :: (1, 1) :: repeat (1, 2) 1713262 ++ (4913917, 2) :: (1, 1) :: repeat (1, 2) 21489090 ++ (11506558, 2) :: (1, 1) :: repeat (1, 2) 135985238 ++ w) 1); closearith.
  }
  (* step 695: P POP *)
  apply (sPOP1 [2607; 991; 619; 109; 19; 0] 16526 23740 (repeat (1, 2) 120150 ++ (650736, 2) :: (1, 1) :: repeat (1, 2) 1713262 ++ (4913917, 2) :: (1, 1) :: repeat (1, 2) 21489090 ++ (11506558, 2) :: (1, 1) :: repeat (1, 2) 135985238 ++ w) 1); closearith.
Qed.

(* CASCADE61y: steps 696-696 of the CASCADE61 chain. *)
