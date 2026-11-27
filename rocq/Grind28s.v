(* ================================================================= *)
(* Phase 60 (companion): the div/mod values of 135985238.  At      *)
(* 136M scale every two-chain evaluated comparison OOMs (see       *)
(* build-logs-60/probes.txt), so the plain S-identities of the     *)
(* TOP14 numerals are proved by div/mod decomposition: X = Y       *)
(* follows from X / 2^20 = Y / 2^20 and X mod 2^20 = Y mod 2^20,    *)
(* each a single-chain vm evaluation (probeDM: rc=0), combined     *)
(* symbolically through Nat.div_mod_eq.  At most two vm lemmas     *)
(* per file.                                                       *)
(* ================================================================= *)

Require Import Arith.

Lemma D60nX : 135985238 / 1048576 = 129.
Proof. apply Nat.eqb_eq; vm_compute; reflexivity. Qed.
Lemma M60nX : 135985238 mod 1048576 = 718934.
Proof. apply Nat.eqb_eq; vm_compute; reflexivity. Qed.
