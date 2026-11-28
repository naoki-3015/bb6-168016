(* ================================================================= *)
(* Phase 62: CASCADE62 segments CASCADE62v. *)
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
               Grind30e1 Grind30e9 Grind30m1 Grind30g10.

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

Lemma CASCADE62v : forall w,
  hsteps (HB [349423; 101323; 57668; 5526; 626; 189; 112; 33; 19; 0] 4860546 1 9546949 ((12762444, 2) :: (1, 1) :: repeat (1, 2) 47892099 ++ (51707595, 2) :: (1, 1) :: repeat (1, 2) 271970480 ++ w) 1)
         (HB [9546949; 4860546; 349423; 101323; 57668; 5526; 626; 189; 112; 33; 19; 0] 12762443 1 3 (repeat (1, 2) 47892099 ++ (51707595, 2) :: (1, 1) :: repeat (1, 2) 271970480 ++ w) 1).
Proof.
  intro w.
  (* step 734: sTUP *)
  apply (hsteps_trans _ (HC [349423; 101323; 57668; 5526; 626; 189; 112; 33; 19; 0] 4860546 9546948 2 ((12762442, 2) :: (1, 1) :: repeat (1, 2) 47892099 ++ (51707595, 2) :: (1, 1) :: repeat (1, 2) 271970480 ++ w) 1)).
  {
    rewrite NUM62X71.
    rewrite NUM62X72.
    apply (sTUP [349423; 101323; 57668; 5526; 626; 189; 112; 33; 19; 0] 4860546 9546949 12762444 2 ((1, 1) :: repeat (1, 2) 47892099 ++ (51707595, 2) :: (1, 1) :: repeat (1, 2) 271970480 ++ w) 1); closearith.
  }
  (* step 735: hGRIND_even 4773472 *)
  apply (hsteps_trans _ (HB [349423; 101323; 57668; 5526; 626; 189; 112; 33; 19; 0] 4860545 1 9546948 ((2, 2) :: (12762442, 2) :: (1, 1) :: repeat (1, 2) 47892099 ++ (51707595, 2) :: (1, 1) :: repeat (1, 2) 271970480 ++ w) 1)).
  {
    rewrite NUM62X73.
    rewrite NUM62X74.
    apply (hGRIND_even 4773472 [349423; 101323; 57668; 5526; 626; 189; 112; 33; 19; 0] 4860545 ((12762442, 2) :: (1, 1) :: repeat (1, 2) 47892099 ++ (51707595, 2) :: (1, 1) :: repeat (1, 2) 271970480 ++ w) 1); [exact P62u735 | exact P62s735].
  }
  (* step 736: P TUP2_1 *)
  apply (hsteps_trans _ (HC [4860546; 349423; 101323; 57668; 5526; 626; 189; 112; 33; 19; 0] 9546948 1 2 ((12762440, 2) :: (1, 1) :: repeat (1, 2) 47892099 ++ (51707595, 2) :: (1, 1) :: repeat (1, 2) 271970480 ++ w) 1)).
  {
    rewrite NUM62X75.
    rewrite NUM62X76.
    rewrite NUM62X77.
    apply (sTUP2_1 [349423; 101323; 57668; 5526; 626; 189; 112; 33; 19; 0] 4860545 9546947 12762442 ((1, 1) :: repeat (1, 2) 47892099 ++ (51707595, 2) :: (1, 1) :: repeat (1, 2) 271970480 ++ w) 1); closearith.
  }
  (* step 737: P TDN *)
  apply (hsteps_trans _ (HB [4860546; 349423; 101323; 57668; 5526; 626; 189; 112; 33; 19; 0] 9546948 1 4 ((12762440, 2) :: (1, 1) :: repeat (1, 2) 47892099 ++ (51707595, 2) :: (1, 1) :: repeat (1, 2) 271970480 ++ w) 1)).
  {
    apply (sTDN [4860546; 349423; 101323; 57668; 5526; 626; 189; 112; 33; 19; 0] 9546948 ((12762440, 2) :: (1, 1) :: repeat (1, 2) 47892099 ++ (51707595, 2) :: (1, 1) :: repeat (1, 2) 271970480 ++ w) 1).
  }
  (* step 738: sTUP *)
  apply (hsteps_trans _ (HC [4860546; 349423; 101323; 57668; 5526; 626; 189; 112; 33; 19; 0] 9546948 3 2 ((12762438, 2) :: (1, 1) :: repeat (1, 2) 47892099 ++ (51707595, 2) :: (1, 1) :: repeat (1, 2) 271970480 ++ w) 1)).
  {
    rewrite NUM62X78.
    apply (sTUP [4860546; 349423; 101323; 57668; 5526; 626; 189; 112; 33; 19; 0] 9546948 4 12762440 2 ((1, 1) :: repeat (1, 2) 47892099 ++ (51707595, 2) :: (1, 1) :: repeat (1, 2) 271970480 ++ w) 1); closearith.
  }
  (* step 739: CLEANG_even 6381218 *)
  apply (hsteps_trans _ (HB [4860546; 349423; 101323; 57668; 5526; 626; 189; 112; 33; 19; 0] 9546948 1 12762442 ((2, 2) :: (1, 1) :: repeat (1, 2) 47892099 ++ (51707595, 2) :: (1, 1) :: repeat (1, 2) 271970480 ++ w) 1)).
  {
    rewrite NUM62X79.
    rewrite NUM62X80.
    apply (CLEANG_even 6381218 [4860546; 349423; 101323; 57668; 5526; 626; 189; 112; 33; 19; 0] 9546948 ((1, 1) :: repeat (1, 2) 47892099 ++ (51707595, 2) :: (1, 1) :: repeat (1, 2) 271970480 ++ w) 1); exact P62s739.
  }
  (* step 740: P TRANS2_1 *)
  rewrite NUM62X81.
  rewrite NUM62X82.
  rewrite NUM62X83.
  apply (sTRANS2_1 [4860546; 349423; 101323; 57668; 5526; 626; 189; 112; 33; 19; 0] 9546948 12762441 1 (repeat (1, 2) 47892099 ++ (51707595, 2) :: (1, 1) :: repeat (1, 2) 271970480 ++ w) 1); closearith.
Qed.

(* CASCADE62w: steps 741-741 of the CASCADE62 chain. *)
