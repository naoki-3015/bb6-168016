(* ================================================================= *)
(* Phase 62: CASCADE62 segments CASCADE62x. *)
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
               Grind30e12 Grind30e13 Grind30e14 Grind30e15 Grind30e16 Grind30e3 Grind30e4 Grind30e5 Grind30e6 Grind30e7 Grind30m1 Grind30m2 Grind30m3 Grind30g12.

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

Lemma CASCADE62x : forall w,
  hsteps (HB [9546949; 4860546; 349423; 101323; 57668; 5526; 626; 189; 112; 33; 19; 0] 60654542 1 95784201 ((51707595, 2) :: (1, 1) :: repeat (1, 2) 271970480 ++ w) 1)
         (HB [60654542; 9546949; 4860546; 349423; 101323; 57668; 5526; 626; 189; 112; 33; 19; 0] 95784200 1 51707594 (repeat (1, 2) 1 ++ (1, 1) :: repeat (1, 2) 271970480 ++ w) 1).
Proof.
  intro w.
  (* step 742: sTUP *)
  apply (hsteps_trans _ (HC [9546949; 4860546; 349423; 101323; 57668; 5526; 626; 189; 112; 33; 19; 0] 60654542 95784200 2 ((51707593, 2) :: (1, 1) :: repeat (1, 2) 271970480 ++ w) 1)).
  {
    rewrite NUM62X84.
    rewrite NUM62X85.
    apply (sTUP [9546949; 4860546; 349423; 101323; 57668; 5526; 626; 189; 112; 33; 19; 0] 60654542 95784201 51707595 2 ((1, 1) :: repeat (1, 2) 271970480 ++ w) 1); closearith.
  }
  (* step 743: hGRIND_even 47892098 *)
  apply (hsteps_trans _ (HB [9546949; 4860546; 349423; 101323; 57668; 5526; 626; 189; 112; 33; 19; 0] 60654541 1 95784200 ((2, 2) :: (51707593, 2) :: (1, 1) :: repeat (1, 2) 271970480 ++ w) 1)).
  {
    rewrite NUM62X86.
    rewrite NUM62X87.
    apply (hGRIND_even 47892098 [9546949; 4860546; 349423; 101323; 57668; 5526; 626; 189; 112; 33; 19; 0] 60654541 ((51707593, 2) :: (1, 1) :: repeat (1, 2) 271970480 ++ w) 1); [exact P62u743 | exact P62s743].
  }
  (* step 744: P TUP2_1 *)
  apply (hsteps_trans _ (HC [60654542; 9546949; 4860546; 349423; 101323; 57668; 5526; 626; 189; 112; 33; 19; 0] 95784200 1 2 ((51707591, 2) :: (1, 1) :: repeat (1, 2) 271970480 ++ w) 1)).
  {
    rewrite NUM62X88.
    rewrite NUM62X89.
    rewrite NUM62X90.
    apply (sTUP2_1 [9546949; 4860546; 349423; 101323; 57668; 5526; 626; 189; 112; 33; 19; 0] 60654541 95784199 51707593 ((1, 1) :: repeat (1, 2) 271970480 ++ w) 1); closearith.
  }
  (* step 745: P TDN *)
  apply (hsteps_trans _ (HB [60654542; 9546949; 4860546; 349423; 101323; 57668; 5526; 626; 189; 112; 33; 19; 0] 95784200 1 4 ((51707591, 2) :: (1, 1) :: repeat (1, 2) 271970480 ++ w) 1)).
  {
    apply (sTDN [60654542; 9546949; 4860546; 349423; 101323; 57668; 5526; 626; 189; 112; 33; 19; 0] 95784200 ((51707591, 2) :: (1, 1) :: repeat (1, 2) 271970480 ++ w) 1).
  }
  (* step 746: sTUP *)
  apply (hsteps_trans _ (HC [60654542; 9546949; 4860546; 349423; 101323; 57668; 5526; 626; 189; 112; 33; 19; 0] 95784200 3 2 ((51707589, 2) :: (1, 1) :: repeat (1, 2) 271970480 ++ w) 1)).
  {
    rewrite NUM62X91.
    apply (sTUP [60654542; 9546949; 4860546; 349423; 101323; 57668; 5526; 626; 189; 112; 33; 19; 0] 95784200 4 51707591 2 ((1, 1) :: repeat (1, 2) 271970480 ++ w) 1); closearith.
  }
  (* step 747: CLEANG_odd 25853793 *)
  rewrite NUM62X92.
  rewrite NUM62X93.
  replace (repeat (1, 2) 1 ++ (1, 1) :: repeat (1, 2) 271970480 ++ w) with ((1, 2) :: (1, 1) :: repeat (1, 2) 271970480 ++ w) by sec_eq.
  apply (CLEANG_odd 25853793 [60654542; 9546949; 4860546; 349423; 101323; 57668; 5526; 626; 189; 112; 33; 19; 0] 95784200 ((1, 1) :: repeat (1, 2) 271970480 ++ w) 1); exact P62s747.
Qed.

(* CASCADE62y: steps 748-748 of the CASCADE62 chain. *)
