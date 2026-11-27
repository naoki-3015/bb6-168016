(* ================================================================= *)
(* Phase 60 (companion): S60rv2, 135985237 = 18372853 +            *)
(* 2 * 58806192, the factored final-pop identity of CASCADE60,     *)
(* by div/mod decomposition with symbolic summand decomposition    *)
(* (see Grind28ab.v's header for the method).                       *)
(* ================================================================= *)

Require Import Arith.
Require Import Grind28i.

Lemma D60rA : 58806192 / 1048576 = 56.
Proof. apply Nat.eqb_eq; vm_compute; reflexivity. Qed.
Lemma M60rA : 58806192 mod 1048576 = 85936.
Proof. apply Nat.eqb_eq; vm_compute; reflexivity. Qed.
Lemma D60rB : 18372853 / 1048576 = 17.
Proof. apply Nat.eqb_eq; vm_compute; reflexivity. Qed.
Lemma M60rB : 18372853 mod 1048576 = 547061.
Proof. apply Nat.eqb_eq; vm_compute; reflexivity. Qed.

Lemma R60r0 : forall a b, b + 2 * a = (a + a) + b.
Proof. intros a b. ring. Qed.
Lemma R60r1 : forall k a r b s, (k * a + r) + (k * a + r) + (k * b + s)
  = k * (a + a + b) + (r + r + s).
Proof. intros k a r b s. ring. Qed.
Lemma E60r : 85936 + 85936 + 547061 = 718933.
Proof. apply Nat.eqb_eq; vm_compute; reflexivity. Qed.

Lemma S60rv2 : 135985237 = 18372853 + 2 * 58806192.
Proof.
  rewrite (Nat.div_mod_eq 135985237 1048576) at 1.
  rewrite D60rX, M60rX.
  rewrite R60r0.
  rewrite (Nat.div_mod_eq 58806192 1048576).
  rewrite (Nat.div_mod_eq 18372853 1048576).
  rewrite D60rA, M60rA, D60rB, M60rB.
  rewrite R60r1.
  rewrite E60r.
  reflexivity.
Qed.
