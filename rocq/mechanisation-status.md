# Mechanisation status — BB(6) holdout #168016 in Rocq (Phase 35, 2026-11-25)

Step 2 of the user-approved community sequence (reproduction ✓ Phase 22 →
**mechanisation** → submission prep ✓ Phase 24). This document maps every
component of the dependency table in `168016-proof.md` §1 to its
mechanisation status. **Nothing has been posted or submitted externally.**

Phase 25 (2026-11-25) advanced the mechanisation along the order suggested
at the end of the Phase 23 status: **TUP** (completing the five-rule
standard system, #10, and discharging the G bookkeeping, #11), **REGEN
assembled** (#17 complete), and the **right-edge entry + mirror system**
(#12, #13) in a new file `Mirror.v`.

Phase 26 (2026-11-25) completed the next block in that order: the **token
pass / Cycle Lemma Γ (#14)** and the **general β = 2 exit (#15)**, in a new
file `TokenPass.v` built on Mirror.v.

Phase 27 (2026-11-25) completed the next two blocks: **#16
re-coordinatisation** in a new file `Recoord.v` (stages 1 and 3 proved in
full; stage 2 kernel-verified at instances and carried as the explicit
hypothesis of the proved composition `RECOORD2`), **#18 the era law** in a
new file `Era.v` (the deviation-free assembly: `ENTRY_gen`, the Grind
Lemma G′ in endpoint form, `POP_CHAIN`, and `ERA_LAW` with
s₁ = 2β_E + 31 and β′ = 2β_E + 34), and the **single-block escape pieces**
of #19's re-formation in a new file `Esc.v` (`POP2` fully general, and
the probe prefix E1–E5 as `PROBE_PREFIX`).

Phase 28 (2026-11-25) mechanised **#19's deviation system** in two new
files: `Dev.v` — **every deviation step list proved for all parameters**
(PUSHX with its general-g follow-on, PX2A including the b = 2 special
form, PX2B rows b = 2..6, the CGAP2 probe and both dispatches, the
TUP2 chain k = 1, TRANS2 turns k = 1 and k = 2, and the TUP2 defect
k = 1, r₁ = 1 — the last with a **machine-corrected landing**, finding
F-3 against `phase21-derivations.md` §4, recorded there as a dated
erratum) — and `Grind.v` — the **frame-general step lists** (the five
standard rules and CGAP2 over abstract frozen prefixes), the **hybrid
word model** `hstep` of phase21 §7 with a full **soundness theorem**
(every word step is a machine run, up to `cfg_sim` for REGEN), the
**grind prefix reductions** of the G″ recursion (clean and PUSHX
deviation branches), and the **Predecessor case analysis** (`pred_cases`:
the only four producers of a PUSH-at-a=2 source, with the exact
remaining invariant obligations). Stage 2 of #16 gained further
kernel-verified instances (n = 8, 10 at B2 = 31; B2 = 15, 47 at n = 2)
but its general case remains fenced. The full non-halting theorem is
**not** yet assembled in Rocq; the remaining components are the general
stage 2 of #16, the G″ endpoint induction (with the era stack invariant)
and with it the ESC-era law, and the S/S′ side (#1–#5), each with its
obstruction and route stated below.

Phase 29 (2026-11-25) mechanised the **G″ endpoint induction and the
ESC-era law** in a new file `Grind2.v`, discharging the Phase 28
obligations (a)–(c) in the regime the ESC trajectory at a2 = 3 uses:
**(b)** the grind iteration — `hGRIND` (the word-level Grind Lemma G′,
transplanted from Era.v) composed into rounds (`grind_round`,
`GG_rounds`) over Grind.v's `grind_prefix`, giving the clean-regime
G″ endpoint `GG_clean` for **every** frame pb, a2 and carried stack P
under the floor m + 1 ≤ a2 (R = 2m + 4), plus the deviated round at
a2 = 3 (`ESC_GRIND_10`: rounds 1–2 clean, round 3 = TUP +
`hGRIND_dev`); **(c)** the post-PUSHX continuation — `hGRIND_dev`,
the deviated Grind Lemma G′ at the boundary frame a2 = t (pb = []),
whose recursion mirrors `hGRIND` with the final spine call deviated
and the base case the single PUSHX step, landing shifted by (+1, +1);
the shift is absorbed by the transfer tail, so no finite check is
needed in this regime; **(a)** the era stack invariant `grind_inv`
(the dip budget s + w ≤ 2a + 7 at B-sections, saturated exactly by
the deviated spine) with `PRED_inv` discharging `pred_cases`' two
obligations (a TUP producer at shuttle exactly 4; STGA / PX2A /
TUP2-defect producers excluded) and `PUSHX_only`, the invariant
threaded through all grind chains (`hstepsP` versions of every grind
lemma). The **ESC-era law β_next = 2β + 4 is PROVED** for
R ∈ {2, 4, 6, 8, 10} (`ESC_ERA_LAW`, via `ESC_TO_REGEN` + the
frame-general `REGEN_gen` + `ERA_TAIL` over Era.v's `ENTRY_gen`).
What remains open in #19 is exactly the **R ≥ 12 re-basing segment**
(the nested two-residue recursion inside round 4 of the ESC grind),
fenced with a precise statement below. The full non-halting theorem
is still **not** assembled in Rocq; the other remaining components
are the general stage 2 of #16 and the S/S′ side (#1–#5), as before.

Phase 30 (2026-11-25) mechanised the **general case of stage 2 of
#16** — the diagonal token pass — in a new file `DiagPass.v`,
discharging the one explicit hypothesis of `RECOORD2`. The pass is
proved for **every frozen prefix P** (`DSTAGE2`: from
`rcsec P n ((2n+3, 2)::[])`, run (Tk n) reaches cfg_sim of
`rcsec P 0 ((3, 2):: repeat (1, 2) n)`), decomposed as the documents'
descent + walk: **DESC(k)** (an A-round, a Ψ-orbit — the *descent
orbit*, whose total cost is TokenPass's `bcost k` — and a closing
RPUSH, landing at the first β = 2 section W_k) followed by
**WALK(i)** steps W_i → W_{i−1} of cost Dk (i−1) (RTDN, an RPOP
chain, RTUP, and a nested descent at the grown suffix). The descent
orbit is built by the orbit recursion
𝒟_{k+1} = T₁(𝒟_k) ⧺ join ⧺ T₂(𝒟_k) with
T₁(β; w) = (β + 1; last gap + 2) and
T₂(β; w) = (β; last gap − 2, gap 3 appended), verified numerically
against the Python word models for k ≤ 9 before formalisation. The
T₂ transport is the one place needing a source invariant (`wok`:
the bad word shape — front all ones, last gap 3 — occurs in the
descent orbits only as the final word, never as a step source);
`fchain` is the `borbit` analogue carrying `wok` at every source.
In Recoord.v, **`STAGE2_proved`** instantiates `DSTAGE2` at
`entryP B2` and **`RECOORD2_uncond`** discharges the composition:
**component #16 (two-block landing) is now fully mechanised.**
The seven kernel-verified instances remain as regression checks
(and Tk 2 = 102 agrees). Remaining components: `REBASE` (R ≥ 12),
the cross-era loop assembly, the S/S′ side (#1–#5), and #2/#3.

Phase 31 (2026-11-25) mechanised **`REBASE`** — the R ≥ 12 re-basing
segment of the ESC grind — in a new file `Grind3.v`, and extended the
ESC-era law to **every even R ≤ 40**. Two things came out of the
pre-proof model analysis. First, **finding F-4**: the Phase 29 fence's
source `HC [] 4 11 2 ((R−10, 2) :: P) 1` has an off-by-one in g0 — the
section the grind actually reaches (round 3 deviated, then its TUP) is
`HC [] 4 12 2 ((R−10, 2) :: P) 1`; the g0 = 11 section never occurs in
the grind, and the chain from it does not reach the fenced target
(`phase21_model.py` traces at R = 14, 18). The fence's target was
correct as stated. Second, the corrected segment needs **no
two-residue induction**: `hGRIND` and `hGRIND_dev` quantify over the
whole carried stack, so the second residue pair is a pure passenger —
`REBASE_core` (PUSH + TDN + TUP, then `hGRIND` 0/1/2 interleaved with
TUP, then `hGRIND_dev` 3) lands `HB [] 4 1 13 ((2, 2) :: (u, 2) :: P)`
for **every** u, and one closing `hTUP2_1` gives `REBASE` for u ≥ 3.
The segment's only PUSHX is `hGRIND_dev`'s base step, as the fence
measured. With `ESC_GRIND_BIG` (the R ≥ 12 grind up to the REBASE
source — the `ESC_GRIND_10` pattern at general R), the re-based grind
is `GG_clean` at (pb = [5], a2 = 13) for R ≤ 40; R = 14 closes by
TDN + `TAIL`, R = 12 by `REBASE_core` + `hTRANS2_2` + the POP chain;
the era-law assembly is factored as `ESC_ERA_LAW_of`.
**`ESC_ERA_LAW_31`: β_next = 2β + 4 for every even R ≤ 40.** What
remains open in #19 is the **second re-basing (R ≥ 42)**, fenced
precisely below. Remaining components: the cross-era loop assembly,
the S/S′ side (#1–#5), and #2/#3.

Phase 32 (2026-11-25) assembled the **cross-era loop** in a new
file `Loop.v`: the exit + stages 1–2 composed for an arbitrary
frozen prefix (`PASS`), the settled iteration at the trajectory
prefix (`SETTLED_ITER`: RECOORD2_uncond + ERA_LAW, β = n + 2 ↦
2n + 38, landing on a single-block entry prefix), the settled
iteration at a general two-block prefix conditional on the
explicit hypothesis `ERA_GEN` (the general-residue era law,
mechanised only at ρ = 29), the ESC iteration (`ESC_ITER`: PASS +
the definitional bridge `esc_bridge` to Esc.v's `esc_src` +
ESC_ERA_LAW_31, β ↦ 2β + 4), the first two iterations composed
in full (`TWO_ITERS`, β = n + 2 ↦ 4n + 80 for n = 2j + 3,
j ≤ 12), the abstract ascending-loop engine (`loop_chain`,
`LOOP_NONHALT`: loop_step at every entry section with β ≥ 4
implies the run from any entry section is total), and the
headline **`NONHALT_FROM_R`**: from the record configuration R,
with the formation segment kernel-verified (Finite.v), the run
is total modulo two explicit hypotheses — **H_STD** (component
#10's assembly: the standard regime from the first I-section
reaches an entry landing entry_tgt (B2 − 1) n, B2 ≥ 3, n ≥ 2)
and **H_LOOP** (loop_step at every entry section with β ≥ 4),
of which the settled instances (B2 = 31 fully; general B2
modulo ERA_GEN) and the ESC instances at R ≤ 40 are discharged
in the same file. The undischarged instances of H_LOOP are
exactly the ESC entries at R ≥ 42 (the second re-basing) and
the entry sections whose prefix is an ESC-era landing form
(iterations ≥ 3). Remaining components: H_STD (#10's assembly
and the exit dichotomy), ERA_GEN, the second re-basing, the
S/S′ side (#1–#5), and #2/#3 — each fenced below.

Phase 33 (2026-11-25) mechanised the **second re-basing** in a
new file `Grind4.v`, extending the ESC-era law to **every even
R ≤ 114** and discharging H_LOOP's ESC instances for
42 ≤ R ≤ 114 (`ESC_ITER_114` in Loop.v). Route (a) was taken
at pb = [5]: the deviated grind **`hGRIND_dev5`** mirrors
`hGRIND_dev` with base case `hPX2B5` (its landing is two-case:
t = 0 carries extras [(1,1),(1,2),(1,2)], t ≥ 1 carries
[(1,2),(1,2),(1,2)] — each level's closing POP consumes the
head pair). Route (b) was reinterpreted, not refuted: the
Phase 29 model evidence ("PUSHX = 0, min PUSH a = 3") is
literally true because the deviation at pb = [5] is PX2B5,
not PUSHX — the re-based grind DOES deviate exactly once.
After the deviated round, three POPs absorb the extras; for
R₂ ≥ 32 the grind continues with a new **even-g0 grind**
`hGRIND_even` (g0 = 2t + 4) and a **third phase** of clean
rounds at a2 = 34 (`rounds_from4`, exact floor j0 + m ≤ a2),
closing at R₃ ≤ 70. All section forms were pre-verified in an
hstep-level simulator mirroring Grind.v's 20 constructors
(validated against the proved `hGRIND_dev` / `REBASE_core` /
`GG_clean` chains). **The new fence is precise**: at
R₃ = 72 (R₂ = 104, **R = 116**) the phase-3 boundary grind at
pb = [20; 0] dips to `HC [20; 0] 0 3 2 ((1, 2)^34 :: …)`,
where **no `hstep` constructor applies** (`hPX2A` needs the
second block ≥ 1; the phase21 model agrees — its PX2A guard
fails with p = 0). Closing R ≥ 116 needs a new machine-level
deviation step list at pb = [20; 0]. Remaining components:
H_STD (#10's assembly and the exit dichotomy), ERA_GEN, the
R ≥ 116 third re-basing, the iterations ≥ 3 re-formation,
the S/S′ side (#1–#5), and #2/#3 — each fenced below.

Phase 34 (2026-11-25) discharged **H_STD** — the standard-regime
assembly, component #10's totality plus the #11 exit dichotomy —
in a new file `Std.v`. The key identifications are definitional:
`cfg_Isec` (Finite.v's formation endpoint: state C, B2 = 97,
s = 2, w = [1], G = 134) **is** the word-model section
`HC [17] 95 1 2 [] 134` (the frozen prefix `[17]` encodes the
separator 0 and the wall 1^17), and `entry_src B2 s` is
definitionally `HB [17] B2 1 s [] 2` — the unique uncovered
guard of the composed five-rule system (reexpansion-derivation
§3: a B-section with w = [1] at G = 2) is exactly the ENTRY
source. The regime from `cfg_Isec` is therefore a single
`hsteps` chain at pb = [17] (`STD_chain`): `hTDN`, one `hSTGA`
collapse, then 65 **grind/collapse cycles** (`STD_cycle`:
`hGRIND t` at floor t + 1 ≤ 95 followed by `hSTGA`; G falls
134 → 2 over 66 Stage A firings in all), then the final
`hGRIND 65`, landing on `HB [17] 95 1 136 [] 2` =
`entry_src 95 136`; Mirror.v's `ENTRY` closes to
`entry_tgt 95 136`. **`H_STD_proved`**: H_STD holds with
(B2, n) = (96, 136), and **`NONHALT_FROM_R_std`** restates
the headline assembly with H_STD discharged — non-halting
from `cfg_R` now rests on the single hypothesis H_LOOP.
The general pattern is `STD_reach_entry` (any empty-stack
I-C-section with even G = 2k + 6 ≥ 6 at a frame A ≥ k + 2
reaches the w = [1] B-section at G = 2). The chain was
pre-verified on the real machine (`rocq/std_verify.py`):
from `cfg_Isec` the first 15 macro boundaries are hit in
order (TDN delta exactly 6, every Stage A delta exactly
2s + 6, GRIND deltas 26/70/162/350/730/1494), and the same
assembly at G0 ∈ {6, 8, 10} runs end-to-end through ENTRY
to `entry_tgt 95 (G0 + 2)`. Scope note: H_STD is discharged
by exhibiting the trajectory's concrete chain; the general
I⁺-preservation induction over *arbitrary* standard-rule
sequences is not separately formalised and is no longer
load-bearing. Remaining components: ERA_GEN, the third
re-basing (R ≥ 116), the iterations ≥ 3 re-formation, the
S/S′ side (#1–#5), and #2/#3 — each fenced below.

Phase 35 (2026-11-25) proved **ERA_GEN** — the
general-residue era law — on its exact domain, in a new
file `EraGen.v`, and discharged the general settled
iteration on that domain in Loop.v. `ERA_GEN_proved` is
Loop.v's `ERA_GEN` statement proved for **every odd ρ
with 1 ≤ ρ ≤ 33** (and every era parameter m ≥ 1): the
assembly is ERA_LAW's with ρ = 2t + 1 substituted —
absorption by `GRIND` at t − 1 (for ρ = 1, t = 0, the
absorption is a single `TDN`), `POP_CHAIN` with
s₁ = ρ + 2m + 2, `REGEN`, the Stage-A era with invariant
s + G = ρ + 2m + 5 over J = t + m cycles, and `ENTRY_gen`
landing at rcsec argument ρ + 2m + 3 (β′ = ρ + 2m + 5).
Both domain bounds are exact and both fences were
pre-verified on the real machine
(`rocq/era_gen_verify.py`): the full predicted boundary
sequence is hit in order, with REGEN / TDN / Stage A /
ENTRY deltas equal to the proved costs, at (ρ, m) =
(29, 2) (the ERA_LAW control), (27, 1), (27, 2), (31, 1),
(31, 2), (33, 1) (floors at equality) and (1, 2)
(absorption = TDN, delta 6); while at (35, 1) and
(30, 1) the absorption landing is **never** reached in
20,000,000 steps. ρ ≥ 35 (odd) exceeds the residue
grind's floor at the fixed frame a2 = 16 (dip
(ρ − 1)/2 > 16); ρ even is obstructed twice over —
Lemma G′ is odd-only (the absorption itself diverges)
and the era's G parity is load-bearing (G₀ = s₁ − 1 must
be even for the Stage-A era to land on the G = 2 entry
source). In Loop.v, **`SETTLED_ITER_GEN_odd`** now
discharges the general settled iteration unconditionally
for odd B2 with 3 ≤ B2 ≤ 35 (ρ = B2 − 2); the conditional
`SETTLED_ITER_GEN` remains for even B2 and B2 ≥ 37, which
are thereby H_LOOP's remaining settled instances (they
arise only inside the iterations ≥ 3 re-formation).
Remaining components: the third re-basing (R ≥ 116), the
iterations ≥ 3 re-formation, the S/S′ side (#1–#5), and
#2/#3 — each fenced below.

## Toolchain

- **Coq 8.18.0** (the proof assistant, pre-Rocq rename; compiled with OCaml
  4.14.1). No system-wide install: the distribution packages were fetched
  with a workspace-local apt state and extracted under
  `~/workspace/coq-toolchain/`; the wrapper `rocq/coqcw` (with `rocq/env.sh`)
  sets `COQLIB`, `OCAMLFIND_CONF`, etc. and invokes that `coqc`.
- Build (from `~/workspace/busy-beaver/rocq/`), in dependency order:

  ```
  ./coqcw TM.v        # machine, execution, entry lemmas, M1–M4
  ./coqcw Configs.v   # concrete configurations (generated)
  ./coqcw Finite.v    # finite segments by kernel computation
  ./coqcw Sections.v  # standard frame: five rules + REGEN
  ./coqcw Mirror.v    # right-edge entry + mirror rules + RI
  ./coqcw TokenPass.v # token pass: Cycle Lemma Gamma + the exit
  ./coqcw DiagPass.v  # #16 stage 2: the diagonal token pass (Phase 30)
  ./coqcw Recoord.v   # #16: re-coordinatisation stages 1-3
  ./coqcw Era.v       # #18: ENTRY_gen, Grind Lemma G', ERA_LAW
  ./coqcw EraGen.v    # #18: ERA_GEN, the general-residue era law (Phase 35)
  ./coqcw Esc.v       # #19 pieces: POP2, probe prefix E1-E5
  ./coqcw Dev.v       # #19: deviation step lists (Phase 28)
  ./coqcw Grind.v     # #19: frame-general lists, word model, G'' pieces
  ./coqcw Grind2.v    # #19: G'' endpoint + ESC-era law (Phase 29)
  ./coqcw Grind3.v    # #19: REBASE + ESC-era law to R <= 40 (Phase 31)
  ./coqcw Grind4.v    # #19: second re-basing, ESC-era law to R <= 114 (Phase 33)
  ./coqcw Loop.v      # cross-era loop assembly (Phase 32; ESC_ITER_114 Phase 33)
  ./coqcw Std.v       # standard-regime assembly: H_STD discharged (Phase 34)
  ```

  Clean rebuild from scratch (Phase 35): all eighteen files compile with
  **no errors** in ~74 s (a few benign warnings: unused introduction
  patterns in `halt_iff`, a comment-delimiter warning, large-nat-literal
  notices in Finite.v). Every headline lemma below was checked with
  `Print Assumptions`: **“Closed under the global context”** — no axioms,
  no admits, anywhere.
- Representation: list-zipper configurations `(state, left, right)`,
  head on `hd right`, blanks implicit — the list-based style of the
  bbchallenge Coq developments (Coq-BB5), specialised to this machine.
  `run n c = Some c'` is the fuel-based executor; a `Some` result already
  certifies that no step on the way halted (cf. `halt_iff`).

## What is proved in Rocq

### TM.v — framework and the halt criterion (component #8, complete)

- `trans`, `step`, `run`, `cfg_blank`, `tape_of`; `run_split`,
  `run_some_step_neq`, `halt_iff` (a step fails ⟺ E-on-0 read — the only
  undefined transition).
- Entry (predecessor) lemmas `pred_E/D/C/F/B` by finite inspection of the
  table: E only from D-on-1; D only from C-on-0; C only from B-on-0 or
  F-on-0; F only from D-on-0, E-on-1 or F-on-1; B only from A-on-0 or B-on-1,
  each with the exact successor shape.
- **M1** (`M1_fwd`, `M1_rev`): halting ⟺ a C-on-0 read whose left cells are
  (1, 0) (zipper form of tape[p−1] = 1, tape[p−2] = 0).
- **M2**: B-entry into that C is always safe. **M3**: the D-on-0 route into
  F is safe (C reads the 1 that D wrote). Both as stated in
  `post-R-proof.md` §1.
- **M4** (`danger`, `M4_rev_local`, `M4_fwd`, `M4_halt_iff`): from the blank
  tape, the machine halts ⟺ some F-on-0 configuration has left triple
  (0, 1, 0). Note: in the zipper formulation the forward direction needs no
  entry case analysis — after the F-step, the C-config's head cell *is*
  tape[q−1] and its left list is the F-config's shifted by one, so all three
  danger components are M1's data read through `pred_C`'s F-case. M3 is
  nevertheless proved as stated (it is the human proof's route, and the
  event lists of the rule derivations use it).

### Finite.v — finite segments by kernel computation (`vm_compute`)

Each check is `seg_check n c0 c1 = true`, proved by `vm_compute`, with
`seg_check_sound` giving the semantic form (same state, same tape) and
`seg_no_halt` extracting “no halting step en route”. Negative controls were
run: off-by-one counts and wrong endpoints return `false`.

| Check | Segment | Status |
|---|---|---|
| `seg_D132_R` | D(132,66) → R in **403,455** steps (component #6) | **proved** |
| `seg_R_Isec` | R → first I-section in **150** steps (component #9) | **proved** |
| `seg_exit4`, `seg_exit4_X` | σ_re(4) → H_4 in **T(4) = 102**, exit successor X_4 at +6 (component #15, instance) | **proved** |
| `seg_exit8`, `seg_exit8_X` | σ_re(8) → H_8 in **T(8) = 2,850**, exit successor X_8 at +6 (component #15, instance) | **proved** |
| `seg_blank_S2`, `seg_S2_S4` | blank → S(2) in 197,317; S(2) → S(4) in 18 (component #1, instances) | **proved** |
| `seg_Sp2_Sp4`, `seg_Sp4_Sp6` | S′(2) → S′(4) in 18; S′(4) → S′(6) in 42 (component #4, instances) | **proved** |

### Sections.v — standard frame: five rules + REGEN (components #10, #11, #17)

Section configs `csec`/`bsec` over the single-block I⁺ frame (see the file
header for the two representation choices: C-sections parametrised by
a2 = a − 2; a continuation-style `tail` fixpoint so pair-prepending is
definitional). The only inductions are the three sweeps (`sweepA`,
`sweepB`, `sweepF`) and `rep_app`, exactly as in the hand derivations;
`probe` is the 5-step probe lemma. Proved, for all parameters in the
stated domains:

- **TDN** — cost 6, for every a2.
- **PUSH** — cost 9, g0 = S(S(S g″)) (i.e. g0 ≥ 3), a2 = S a2′.
- **POP-general** (`pop_prefix` + `pop_sweep` → `POP`) — cost 2s + 3,
  s′ = s + r₁ for every r₁ ≥ 1, s ≥ 2. This is component #17's POP-general.
- **TUP** (Phase 25; `tup_prefix` + probe + `sweepF`) — cost 2s + 6,
  s ≥ 2, first gap g₁ ≥ 3 written S(S(S g₁″)): lands the C-section with
  shuttle s′′ = s − 2, g₀′ = 2 and first pair (g₁″, r₁). With TUP, **all
  five standard rules are sound in Rocq** (component #10's rule layer).
- **Stage A** — cost 2s + 6, s ≥ 2, G ≥ 3, landing the C-section with
  g0′ = s − 1, G′ = G − 2.
- **G bookkeeping (#11) discharged**: the five statements show TDN, PUSH,
  POP and TUP preserve the terminal gap G, and Stage A sends G ↦ G − 2;
  no rule creates or destroys terminal gap otherwise. No separate lemma
  is needed beyond reading the five statements.

REGEN (component #17, completed in Phase 25) is assembled exactly as
`phase19-derivations.md` §1 decomposes it — the POP step list run to the
terminal pair, the Stage A step list at the blank end, the PUSH step
list — via three frame lemmas:

- `POP_terminal` — the POP step list at the terminal pair (pairs = [],
  G = 1): run (2s + 3) lands the *open* B-section `bsec_open (a+1) 1 (s+2)`
  (right side `0 1^{s+2}`, then blank). The blank-end forms `bsec_open`,
  `csecT`, `csecR` carry the tail beyond the working region explicitly.
- `StageA_blank` — the Stage A step list at the blank end: run (2L + 6)
  (L ≥ 2) lands `csecT A (L−1) [false]`.
- `PUSH_T` — the PUSH step list (9 steps) on the `csecT` form.
- **`REGEN`** — run (4s + 22) (bsec a 1 s [] 1) = Some (csecR a (s−1)
  [false]) for every a ≥ 0 (a2 = a − 2 encoding) and s ≥ 2: the documents'
  map (B, a, s, [1], 1) → (C, a+2, 2, [1], G = s−1), span +2, cost 4s + 22.
  One representation fact, proved as `REGEN_tape`: the landing's tape
  equals the tape of the clean section `csec a 1 2 [] (s−1)` — the
  Stage-A-at-blank probe materialises one trailing blank cell in the
  zipper's right list, carried explicitly in the tail parameter
  (r = [false]); the tapes agree at every position.

### Mirror.v — right-edge entry + mirror system (components #12, #13) — Phase 25

Mirror-frame sections over an *abstract frozen prefix*: the left list is
`repeat true b ++ P` with `P` an arbitrary list of cells, so every lemma
holds uniformly in the frozen prefix (the mirror rules never read it).
The working region `rtail pairs` ends in a run — blank beyond — with no
terminal [1;1] block (that is what distinguishes the mirror frame).
β (the left block length) is b + 2 at C-sections (`rcsec`, parametrised
by b2 = β − 2) and b at B-sections (`rbsec`). Proved, for all parameters
in the stated domains, exactly as in `rightedge-derivation.md` §2:

- **RTDN** — cost 6: (C, β, (1, r₁)::…) → (B, β, (1, r₁+2)::…).
- **RPUSH** — cost 9, β ≥ 3: creates the pair (1, 2), first gap g ↦ g − 2.
- **RPOP** — cost 2r₁ + 3 (`rpop_prefix` + `rpop_sweep`): merges the first
  two runs, β ↦ β + 1.
- **RTUP** — cost 2r₁ + 6 (`rtup_prefix` + probe + `sweepF`): lands the
  C-section with pair (r₁ − 2, 2), second gap g₂ ↦ g₂ − 2.
- **RPROBE** — cost 2r₁ + 6 (`rprobe_prefix` + `probe_blank` + `sweepF`):
  the empty-stack probe; its landing `rcsec_probe` carries the probe's
  trailing [1;1;0] tail, and `RPROBE_tape` proves its tape equals the
  documents' C-section (β + 2, pair (r₁ − 1, 2), no further pairs).
- **Invariant RI (parity layer)**: `RI_pairs` (every pair has odd gap and
  even run) is preserved by each rule — `RI_rtdn`, `RI_rpush`, `RI_rpop`,
  `RI_rtup`, `RI_rprobe` (pure list arithmetic from the rule forms; the
  β side conditions are read off the statements).
- **ENTRY (component #12)** — the right-edge entry excursion of
  `rightedge-derivation.md` §1: from the standard-frame B-section
  (B, wall 1^17 0, block B2, gap 2, shuttle s, terminal [1;1]) — encoded
  as `entry_src B2 s` — run (s + 12) lands `entry_tgt B2 s` for every
  B2 ≥ 0 and s ≥ 1 (decomposition: entry prefix (s + 2) + 3 steps + the
  5-step probe + 2 steps). `ENTRY_tape` proves the landing's tape equals
  the first mirror C-section `rcsec P s [(1, 2)]` with frozen prefix
  P = 0 1^{B2+1} 0 1^17 and β = s + 2 — i.e. the documents' entry section
  (C, β_E := s, w = (1), v = (2)) up to the materialised trailing blank.

### TokenPass.v — token pass: Cycle Lemma Γ (#14) and the exit (#15) — Phase 26

Built directly on Mirror.v's proved rules. Because the mirror rules'
landings materialise an occasional trailing blank in the zipper's right
list (the same phenomenon as REGEN_tape), all iteration is done up to
`cfg_sim` (same state, same tape at every position): `step_sim_some`,
`step_sim_none`, `run_sim`, `run_sim_transfer`, with `sim_rprobe` and
`sim_entry` transporting the RPROBE and ENTRY landings to clean section
forms. The token pass itself is formalised at the level of **B-start
words** (gap lists with all runs = 2, the joint invariant J = "all gaps
odd", `Jg`):

- **Phase and excursions**: `PHASE` (RPUSH+RTDN, cost 15) and
  `PHASE_second` (the H-type phase second at cost 9); the excursion cost
  functional `excR` with the closed form on ones-words
  (`excR_repeat1`: excR R (repeat 1 j) = 2j² + (2R+5)j + 2R + 6) and the
  excursion lemmas `EXC_TUP` / `EXC_PROBE` / `EXC_prefix` by induction on
  the merged-run list.
- **Rounds**: `ROUND_A` (type A, cost 29, Δβ = −1), `ROUND_B_TUP` and
  `ROUND_B_PROBE` (type B, cost 15 + excR 4 (1::ms)), `CLOSING_H`.
- **The composed two-round map Ψ**: `psi_run_gen` — for Jg xs with
  u = lo xs < length xs, Ψ runs in `psicost u = 2u² + 17u + 73` steps
  from the B-start (β, (3, x)) to (β + u − 1, (3, wpsi x)) with an
  arbitrary pair-suffix carried verbatim; `psi_step` packages it as a
  step relation on B-start states (S-arg b2 = word β − 3, word xs).
- **Suffix Lemma transports**: `psi_step_front` (Ψ commutes with
  appending a fixed odd tail gap — the Suffix Lemma at step level),
  `psi_step_last2f` (Ψ commutes with last-gap + 2, split case and carry
  case), packaged over orbit segments by `borbit_map`. Orbits are the
  inductive `borbit` (a chain of Ψ steps with all S-args ≥ lb), with
  `borbit_run`, `borbit_lb`, `borbit_weaken`, `borbit_trans`.
- **Orbit recursion** (`borbit_cycle`, the derivation's §5 recursion):
  cycle (2+j)'s orbit = cycle (2+j−1)'s orbit replayed with the last gap
  + 2, then the carry Ψ step at (repeat 1 j ++ [3]), then the same orbit
  at B − 1 with a 1 appended to every word — total cost `bcost (2+j)`,
  with closed form `bcost_closed` (bcost k + 2k² + 13k + 62 = 3·2^{k+3}
  for k ≥ 2).
- **Cycle Lemma Γ** (`CYCLE`): for every frozen prefix P, frame B and
  k ≥ 2 with k − 2 ≤ B,
  run (Dk k) (rcsec P (B+2) ((2k+1, 2)::[])) =
  Some (rcsec_probe P (B+2) (2k+3)), Dk k = 3·2^{k+3} − 4; `CYCLE_sim`
  gives the landing up to cfg_sim as the clean section S_{k+1}.
- **Min-β facts**: `CYCLE_H` — the tokenless home section
  H_k = rcsec P (B−(k−2)) (repeat (1,2) (k+1)) (word β = β_E − k
  exactly) is reached 29 + bcost k + 9 steps into cycle k (attainment);
  `borbit_lb` applied to `borbit_cycle` bounds every orbit B-start's
  S-arg below by B − (k−2) (the derivation-level induction passes
  through every Ψ step node), the closing B-start attains it, and the
  phase-second/excursion landings (`PHASE_second`, `EXC_prefix`) sit at
  rbsec/rcsec args ≥ the round's source S-arg. This is the derivation's
  (ii)/(iii) at section granularity.
- **Cycles 0 and 1** (`CYCLE0`, `CYCLE1`): the finite base cycles,
  costs 20 = D_0 and 44 = D_1, from RTDN/RPROBE and ROUND_B_PROBE.
- **The exit (#15)**: `Dsum` with `Dsum_closed`
  (Dsum K + 4K + 28 = 3·2^{K+3} + 4); `EXIT_iter` iterates the cycles
  from S_0 up to cfg_sim; `EXIT` — at K = β_E − 2 ≥ 2, after
  Tk K = Dsum K + 29 + bcost K + 9 steps the configuration is cfg_sim
  to H_K (rcsec arg 0, word β = 2), and 6 further steps (RTDN,
  event-clean since the run is a `Some`) land cfg_sim at
  rbsec P 0 ((1, 4) :: repeat (1, 2) K), the exit successor in shifted
  coordinates; `EXIT_time`: Tk K + 2K² + 17K + 48 = 3·2^{K+4};
  `EXIT_entry` instantiates the exit at the actual entry prefix
  P = 0 1^{B2+1} 0 1^17 via `sim_entry`. Headline checks:
  `Print Assumptions CYCLE / CYCLE_H / EXIT / EXIT_entry` all report
  **“Closed under the global context.”**

### Recoord.v — re-coordinatisation (#16) — Phase 27

The post-exit continuation of `phase19-derivations.md` §3, in three
stages, over C-sections `gcsec Q a2 g0 s pairs G` parametrised by an
abstract tail Q (`gcsec_nil`: `gcsec [] = csec`).

- **Stage 1 — PROVED** (`STAGE1`, `STAGE1_exit`): the RPOP chain from
  the exit successor. The chain lemma (induction on j) fires RPOP at
  r₁ = 2j + 4 with cost 4j + 11 and landings 2j² + 9j, closing with
  RPROBE; composed with `EXIT` via `run_sim_transfer`, `STAGE1_exit`
  gives: from any mirror C-section `rcsec P K ((1, 2)::[])` — in
  particular the entry section, at K = β_E − 2 — after
  (Tk K + 6) + (2K² + 13K + 14) steps (the Tk K + 6 being the exit
  itself) the configuration is cfg_sim to
  `rcsec P K ((2K + 3, 2)::[])` — the stage-2 source
  S_{β_E−1}(β_E) in shifted coordinates.
- **Stage 2 — instances proved, general case fenced as a hypothesis**:
  `STAGE2 B2 n` is the proposition that the second token pass (the
  Phase 17 suffix recursion on the diagonal) runs in Tk n steps from
  the stage-2 source to cfg_sim of the escape source
  `esc_cfg B2 n = rcsec (entryP B2) 0 ((3, 2):: repeat (1, 2) n)`.
  It is **kernel-verified** at the trajectory's entry parameter
  B2 = 31 for β_E ∈ {4, 6, 8} (`stage2_inst_2/4/6`, costs
  Tk 2 = 102, Tk 4 = 620, Tk 6 = 2850, by `seg_check` + `vm_compute`),
  and (Phase 28) at B2 = 31 for n = 8 and n = 10 (`stage2_inst_8/10`,
  Tk 8 = 2850, Tk 10 = 11976 steps) and at n = 2 for B2 = 15 and
  B2 = 47 (`stage2_inst_15_2`, `stage2_inst_47_2`) — the statement's
  B2-independence and n-scaling are pinned at seven points.
  The general case is a second token-pass development on the diagonal
  (same architecture as TokenPass.v: a word model, round maps, a suffix
  recursion) and is carried as the explicit hypothesis of `RECOORD2` —
  see “Remaining components” below.
  **(Phase 30: the general case is PROVED** — `STAGE2_proved` in
  Recoord.v, from `DSTAGE2` in the new file DiagPass.v (next section);
  the hypothesis is discharged and the instances remain as regression
  checks.)
- **Stage 3 — PROVED for all B2 ≥ 2** (`STAGE3`): the RPUSH escape +
  F-sweep of `phase19-derivations.md` §3, cost B2 + 11, landing the
  canonical standard-frame C-section
  `gcsec Q (L−1) (B2−2) 2 ((1,1):: repeat (1,2) (n+1)) 1` for every
  abstract tail Q, frame L ≥ 1 (the B2 = 2 case is a separate short
  chain; the sweep is `sweepF` at cost b3 + 1 plus list bridging
  `tail_rtail` / `s3R_snoc`). On the trajectory (L = 17, B2 = 31) this
  is the canonical section with a = 16 and residue ρ = B2 − 2 = 29.
- **`RECOORD2` — the conditional composition, PROVED**: for B2 ≥ 3,
  n ≥ 2, given `STAGE2 B2 n`, the full chain ENTRY-exit → stage 1 →
  stage 2 → stage 3 runs in
  (Tk n + 6) + (2n² + 13n + 14) + Tk n + (B2 + 11) steps from
  `entry_tgt (B2−1) n` to cfg_sim of the canonical section
  `csec 16 (B2−2) 2 ((1,1):: repeat (1,2) (n+1)) 1` — the standard I⁺
  frame with a = 16, s = 2, first pair (1, 1), word (1, 2)^{n+1},
  G = 1. This is the two-block (settled-frame) landing of #16; the
  composed loop map reads β′ = ρ + 2β_E + 5 off `ERA_LAW` below.
  **(Phase 30: `RECOORD2_uncond`** — the same statement with no
  hypothesis, via `STAGE2_proved`; #16's two-block landing is fully
  mechanised.)
- **The B2 convention (resolved in Phase 27)**: Mirror.v's
  `entry_src B2` carries the prefix block **S B2** (its frozen prefix is
  0 1^{B2+1} 0 1^17), whereas the documents' “B2 = 31” is the *absolute*
  second block in the mirror frame. The trajectory's ENTRY therefore
  instantiates at Mirror-B2 = 30. Recoord.v's `entryP B2` uses the
  absolute block (prefix 0 1^{B2} 0 1^17), and `RECOORD2` instantiates
  `EXIT_entry` at (B2 − 1) accordingly. Verified against the Phase 19
  segment models (the stage-3 traces `p19-esc12.cfg` / `p19-esc-b31.cfg`
  and `phase19_segment_check.py`, which build the tape with block 31).

### DiagPass.v — the diagonal token pass (#16 stage 2) — Phase 30

Stage 2 for an **arbitrary frozen prefix P**, in the documents'
descent + walk decomposition (`phase19-derivations.md` §3.2,
`phase21-derivations.md` §6). All forms were pre-verified against
the Python word models (`phase17_model.py`, `phase19_stage2.py`,
plus a dedicated recursion check for k ≤ 9) before proving.

- **The T₂ word map and the source invariant** (Part 1): `F2`
  (last gap − 2, gap 3 appended), `frontw`/`lastw`, and
  `wok w` := all gaps odd, `lo w < length w`, last gap ≥ 3, and
  (front of w not all ones ∨ last gap ≥ 5). `wok` is preserved by
  `F2` (`wok_F2`) and by `last2f` (`wok_last2f`), and `lo` is
  preserved by `F2` at `wok` words (`lo_F2`).
- **Ψ transports** (Part 2): `psi_step_shift` (Ψ is invariant under
  a uniform +1 block shift, via `psi_run_gen`), `psi_step_last2f_up`
  (the T₁ transport: `psi_step_last2f` + shift), and `psi_step_F2`
  (the T₂ transport, under `wok`; the front-all-ones case goes
  through `wpsi_app_ones` / `wpsi_F2_ones`).
- **`fchain`** (Part 3): the `borbit` analogue carrying `wok` at
  every step source, with `fchain_borbit` (to `borbit` at lb = 0),
  `fchain_trans`, `fchain_last2f_up`, `fchain_F2`.
- **The descent orbit** (Part 4): `dorbit_cycle` — for every j, an
  `fchain` from (j; [2j+3]) to (0; 1^j ++ [3]) of cost
  `bcost (2 + j)`, by induction on j: the T₁ replay of the previous
  orbit, the join Ψ step at (1; 1^j ++ [5]) (via `PSI_RUN`), and
  the T₂ replay. The cost recursion is exactly TokenPass's
  `bcost`, so `bcost_closed` applies verbatim.
- **DESC** (Part 5): for k ≥ 2 and every odd gap suffix `sfx`,
  run (bcost k + 38) from `rcsec P k ((2k+3, 2):: gpairs sfx)`
  reaches (exactly, hence cfg_sim) `rcsec P 0 (gpairs (1^k ++ [3])
  ++ gpairs sfx)` — the A-round (`ROUND_A`), the descent orbit
  with the suffix appended (`borbit_map` over `psi_step_front_list`),
  and the closing RPUSH (`PHASE_second`).
- **The walk** (Parts 6–7): `rpop_chain` (the RPOP chain with a
  general head run and tail: cost 2·R·j + 2j² + j, head R + 2j);
  `WALK` — W_i → W_{i−1} in `Dk (i−1)` steps for every i ≥ 1
  (RTDN + chain + RTUP, then: nothing at i = 1, a single
  `PHASE_second` at i = 2, `DESC (i−1)` at the grown suffix
  `1 :: sg` for i ≥ 3; the cost identity at i ≥ 3 is
  `bcost_closed`); `WALK_ITER` iterates the walk from W_j to W_0
  in `Dsum j` steps.
- **`DSTAGE2`** (Part 8): DESC(n) at the empty suffix composed
  with `WALK_ITER` at j = n: run (Tk n) from
  `rcsec P n ((2n+3, 2)::[])` reaches cfg_sim of
  `rcsec P 0 ((3, 2):: repeat (1, 2) n)`, for every P and n ≥ 2.
  `Print Assumptions DESC / WALK / DSTAGE2` all report
  **“Closed under the global context.”**

### Era.v — the era law (#18, deviation-free assembly) — Phase 27

- **`ENTRY_gen`** — Mirror.v's ENTRY generalised to an abstract
  standard-frame tail P0: from `entry_src_gen P0 a s` (the B-section
  (B, a, 2, s, []) over tail P0 ++ 0 1^{a+1} 0 1^17 ++ [1;1]) run
  (s + 12) lands `entry_tgt_gen P0 a s`, whose tape is the mirror
  C-section over the frozen prefix P0 ++ 0 1^{a+1} 0 1^17
  (`ENTRY_gen_tape`, `entry_gen_sim`); `bsec_entry_src` identifies the
  P0 = [] source with `bsec a 1 s [] 2`. Mirror's ENTRY is the case
  P0 = 0 1^17.
- **`GRIND`** — the Grind Lemma G′ in endpoint form: for every t, frame
  a2 and carried pairs P, **under the frame-floor hypothesis
  t + 1 ≤ a2**, there is a cost with
  run cost (csec a2 (2t+3) 2 P G) = Some (bsec a2 1 (2t+6) P G).
  Proof: strong induction on t (the recursion halves the gap). Base
  t = 0: PUSH + TDN + POP (costs 9 + 6 + 11). Step: prefix
  PUSH + TDN + TUP (9 + 6 + 14), an inner loop (induction on k)
  alternating `GRIND` at smaller t (the outer IH) with TUP, and a final
  `GRIND` at t − 1 + POP. The frame floor is exactly the hypothesis
  that keeps every recursive application inside its domain — the
  load-bearing content of the documents' floor clause for the era law.
  **Fenced**: the dip clause as a *sequence* statement — “during the
  grind, min a_C = a − (m−1)/2, attained only at w₀ = 1 sections” —
  is not formalised; it quantifies over the grind's internal
  rule-boundary sections, which the endpoint form does not expose.
  Route: a section-sequence formulation of the grind (an inductive
  predicate over C/B-section boundaries with the a-values recorded),
  or a prefix-quantified strengthening of `GRIND`'s induction. The era
  law below does not need it: every grind application in the era
  discharges the floor hypothesis directly.
- **`POP_CHAIN`** — the POP chain over a run list: from
  `bsec a 1 s (map (fun r => (1, r)) rs) G` with every r ≥ 1 and
  s ≥ 2, some cost reaches `bsec (a + length rs) 1 (s + rsum rs) [] G`
  (helpers `map_repeat_2`, `rsum_repeat_2` for the ones/2-runs of the
  era word).
- **`ERA_LAW` — PROVED**: for every n ≥ 1, from the canonical era entry
  `csec 16 29 2 ((1,1):: repeat (1,2) (n−1)) 1` (a = 16, residue
  ρ = 29, s = 2, word (1,2)^{n−1} after the first pair, G = 1) some
  cost reaches cfg_sim of the next era's entry mirror section
  `rcsec (0 1^{n+17}) (2n + 32) [(1, 2)]` — i.e. **β′ = 2n + 34**
  with the new frozen prefix 0 1^{β_E + 17}. Assembly: `GRIND` at
  t = 13 (the residue grind, floor 14 ≤ 16 discharged) →
  `POP_CHAIN` over the run list 1 :: 2^{n−1}, giving the REGEN source
  with **s₁ = 2n + 31** and frame a_f = n + 16 → `REGEN` (cost
  4s + 22; the landing transported to the clean csec via `REGEN_tape`)
  → TDN → the Stage-A era loop (induction on j with k + j = n + 14;
  invariant s + G = 2n + 34, so G = 2n + 30 − 2k is always even —
  **the odd-G sub-case is excluded** — each cycle Stage A + `GRIND`
  at k, floor k + 1 ≤ a_f discharged since k ≤ n + 13 < n + 16) →
  `ENTRY_gen` at P0 = []. In particular **β′ = 2n + 34 > n**: the era
  map strictly increases β, hence the span. The trajectory case is
  n = β_E with ρ = 29, giving the documents' s₁ = 2β_E + 31 and
  β′ = 2β_E + 34.

### EraGen.v — the general-residue era law (#18, ERA_GEN) — Phase 35

- **`ERA_GEN_proved` — PROVED on its domain**: Loop.v's `ERA_GEN`
  statement (the era law in ERA_LAW's shape at residue ρ) for
  every **odd ρ with 1 ≤ ρ ≤ 33** and every era parameter
  m ≥ 1: from `csec 16 rho 2 ((1,1):: repeat (1,2) (m−1)) 1`
  some cost reaches cfg_sim of `rcsec (0 1^{m+17}) (rho + 2m + 3)
  [(1, 2)]` — s₁ = ρ + 2m + 2, β′ = ρ + 2m + 5 (phase19 §2).
  Assembly = ERA_LAW's with ρ = 2t + 1: absorption (`TDN` at
  t = 0; `GRIND` at t − 1 for t ≥ 1, floor t ≤ 16 at the fixed
  frame a2 = 16) → `POP_CHAIN` over 1 :: 2^{m−1} → `REGEN` →
  TDN → the Stage-A era (induction on j with k + j = t + m;
  invariant s + G = ρ + 2m + 5, G₀ = ρ + 2m + 1 even) →
  `ENTRY_gen` at P0 = []. The two floor families (the residue
  grind at a2 = 16; the era-loop grinds at frame m + 16) give
  the **same** bound t ≤ 16, i.e. ρ ≤ 33. The frame a2 = 16 is
  not a specialisation to the trajectory: stage 3 of #16 lands
  at a = 16 for every two-block prefix, so 16 is the settled
  frame's own constant.
- **Fences (exact, machine-checked)**: ρ ≥ 35 odd — the
  residue grind's dip (ρ − 1)/2 exceeds the frame a2 = 16
  (GRIND at t − 1 = 16 would need floor 17 ≤ 16); ρ even —
  Lemma G′ is odd-only and the era's G parity is
  load-bearing (phase19 §2.4's odd-G exclusion is the ρ-odd
  hypothesis in disguise: without it G₀ is odd and the
  Stage-A era cannot land on the G = 2 entry source).
  Pre-verification (`rocq/era_gen_verify.py`, TM.v step
  semantics): the predicted boundary sequences are hit in
  order with REGEN / TDN / Stage A / ENTRY deltas equal to
  the proved costs at (ρ, m) = (29, 2) [the ERA_LAW control],
  (27, 1), (27, 2), (31, 1), (31, 2), (33, 1) [domain
  boundary, floors at equality] and (1, 2) [absorption =
  TDN, delta 6]; the absorption landing is never reached in
  20,000,000 steps at (35, 1) and (30, 1).

### Esc.v — single-block escape pieces (of #19's re-formation) — Phase 27

The ESC family of `phase20-derivations.md` / `phase21-derivations.md`
(the single-block, iteration-2 frame of #16). Delivered pieces:

- **`POP2` — PROVED, fully general**: the transfer rule of phase21
  §1.1, over an abstract frozen prefix P (`gbsec`): from
  (B, P, a, g₀ = 1, s = S s′, pairs (2,2) :: (1, S r₂′) :: rest, G)
  run (S s′ + 9) lands (B, 0 1^{a+1} P, S(S s′), 1, (1, r₂′ + 3) :: rest,
  G) — via the prefix-general TUP `gtup_prefix` (a copy of Sections'
  `tup_prefix` proof over the abstract prefix) plus 7 steps. Verified
  against the Python model for all rest/G including the boundary
  cases (the documents' side conditions are not needed).
- **`PROBE_PREFIX` — PROVED**: the probe prefix E1–E5 (phase20
  theorem P20.1): from `esc_src (l + 7) m` (the ESC source
  (C, [0] 1^L, right 1 1 0³ 1 1 RT(m)), L = l + 7, m = β − 2) run
  (L + 42) lands `e5form (S l) m` exactly. The five excursions are
  proved individually (E1's F-sweep via `sweepF`; E2–E5 by direct
  computation on the exposed forms). Domain note: the documents
  state L ≥ 8; the mechanised proof covers L ≥ 7 — the binding
  constraint is E5, whose excursion pattern needs the e4form zero
  run ≥ 3 (checked against the model: at run 2 the excursion leaves
  the E5 pattern).
- **`PROBE_PREFIX_sim` — PROVED**: the landing is cfg_sim to the clean
  C-section `csec 3 1 2 ((L−6, 2):: (1,1):: repeat (1,2) (β−1)) 1`
  (via the right-side identity `e5form_right` and the left-side
  `nth_app_false`).
- **Not delivered here**: the ESC-family era law β_next = 2β + 4.
  Its grind is G″ (#19), an induction over the deviation system, not
  over the five standard rules. **Delivered in Phase 29** (Grind2.v,
  for R ≤ 10; the R ≥ 12 re-basing segment stays fenced — see
  “Remaining components”).

### Dev.v — the deviation step lists (#19) — Phase 28

Every step list of `phase21-derivations.md` §§1–5, proved for **all**
parameters (abstract pair lists, terminal gap G, and frame tails), in
the absolute-coordinate style of Sections.v/Recoord.v. All were
pre-verified against a Python zipper tracer (`rocq/trace_dev.py`)
before formalisation.

- **Chain units**: `gturn` (the B-section turn closing a TRANS2 chain:
  sweepB + the landing step, cost r + 1), `gunit2` / `gunit2_mk` (the
  gap-1 transfer unit, cost r₁ + 2), `gtup_prefix_mk` (the folded-form
  variant of Esc.v's `gtup_prefix`).
- **PUSHX**: `PUSHX_core` (the uniform 20 steps from
  (C, pb = (), a = 2, s = 2, [3]+W) to (B, 0, 5, [1, g−2]+W, [2]+R),
  for all g ≥ 3) and `PUSHX` (the g = 3 closing via POP, total 33,
  landing (B, 1, 7, W, R)); `PUSHX_TUP` (the general-g follow-on: at
  g ≥ 5 the core landing continues by TUP, = Sections.v's `TUP`
  instantiated). PUSHX is a pb = () rule — its excursion reads the
  prefix; with a nonempty prefix the dispatch is PX2A/PX2B below.
- **PX2A**: `PX2A` (two-block prefix, b ≥ 3: cost b + 11, landing
  (C, pb[:-2], p + 1, 2, [b−2, 1, 1, 1] + W, [1, 2, 2] + R)) via
  `PX2A_chunkA` + `sweepF`; `PX2A_b2` (the b = 2 special form: cost
  23, landing (B, pb[:-2], p − 1, 5, [1, 1, 1] + W, [2, 2] + R)).
- **PX2B** (single prefix block): rows b = 2 (cost 43), 3 (38), 4 (29),
  5 (44), 6 (49) — all by direct computation with abstract pairs/G;
  the b = 4/5/6 landings are also stated in clean `gbsec` form
  (`PX2B_b4'/b5'/b6'`; the trailing blank the excursion materialises
  is the empty prefix block [0]). The b ≥ 7 row is Esc.v's
  `PROBE_PREFIX` (Phase 27), not redone.
- **CGAP2**: `CGAP2_probe` (4 steps, frame gain [a−2], new interface
  block 5), `CGAP2_pop` (6 steps) and `CGAP2_push` (9 steps), composed
  as `CGAP2_pop_total` (total 10) and `CGAP2_push_total` (total 13) —
  the documents' totals confirmed (the F-2 erratum concerns only the
  recursive re-probe accounting, whose first re-probe is the same
  probe lemma at the shifted frame).
- **TRANS2 / TUP2 chains**: `TUP2_1` (chain k = 1, all r₁: cost
  s + 2r₁ + 8, via `gtup_prefix` + `tup2_inner` + `tup2_probe` +
  `sweepF`); `TRANS2_1` (turn k = 1, all r₁ — the generalisation of
  Esc.v's `POP2`, which is its r₁ = 2 case); `TRANS2_2` (turn k = 2:
  two `gtup_prefix` units + `gunit2_mk` + `gturn`, landing frame
  gains [a+1, s+1] and shuttle r₂ + r₃). Era grinds have k ≤ 2
  (phase21 §6), so these are the chain forms the era system uses.
- **TUP2 defect (k = 1, r₁ = 1)**: `TUP2_defect` — total cost s + 23,
  assembled as `gtup_prefix` + `defect_merge` (7 steps) +
  `defect_fstep` + `TAIL13` (the 13-step tail from the post-F gcsec
  (g0 = 0, s = 2, pair gap w₂ − 2)). **The landing is the
  machine-corrected form** (C, pb + [a+1], s + 1, 2,
  [3, w₂ − 4] + w[3:], [r₂] + r[2:], G): the documents' §4 row
  ([w₂ − 2, 1] + w[3:]) agrees only at w₂ = 5 and is wrong for
  w₂ ≥ 6 — finding **F-3**, recorded as a dated erratum in
  `phase21-derivations.md` §4. The defect is era-unreachable (§8);
  the k ≥ 2, r_k = 1 stage-2 shapes remain fenced exactly as in the
  documents.

### Grind.v — frame-general lists, the word model, G″ pieces — Phase 28

- **Frame-general step lists** (Part 1): the five standard rules and
  CGAP2 over an abstract frozen prefix (`gcsec`/`gbsec` forms):
  `gTDN`, `gPUSH` (both by direct computation), `gPOP`
  (`gpop_prefix` + `gpop_sweep`, adapting Sections.v's POP proof),
  `gTUP` (`gtup_prefix3` + probe + `sweepF`), `gSTGA`
  (`gstageA_prefix` + `sweepA` + probe + `sweepF`), and
  `gCGAP2_probe/pop/push` with totals. These are the bridges the word
  model needs; PUSHX and REGEN have no such generalisation (PUSHX
  reads the prefix by design; REGEN's blank-end components
  POP_terminal/StageA_blank/PUSH_T are bsec-form — route: re-prove
  them over `gbsec` open forms).
- **The word model** (Part 2): `hsec` (C/B sections with prefix
  blocks as a nearest-first list of lengths, encoded to the raw
  zipper tail by `enc`) and the inductive `hstep` with **20
  constructors** = the phase21 §1 dispatch (TDN, PUSH, PUSHX at
  pb = (), PX2A, PX2A at b = 2, PX2B rows, CGAP2 pop/push, POP, TUP,
  STGA, REGEN at pb = (), TRANS2 turns k = 1/2, TUP2 k = 1, the TUP2
  defect). **`hstep_sound` — PROVED**: every `hstep` is realised by a
  machine run between the encoded configs (exactly, except REGEN
  whose machine landing is the tape-equal `csecR`, composed via
  `REGEN_tape`); **`hsteps_sound`** lifts this to step sequences via
  TokenPass.v's `run_sim_transfer`.
- **G″ pieces** (Part 3): `grind_prefix` — the forced prefix
  [TDN, TUP, PUSH, TDN, POP] of phase21 §7 as an `hsteps` chain:
  (C, pb, a₂ ≥ 1, [1, R] + W) → (B, pb, a₂, 6, [1, R−2] + W) for
  R ≥ 3, all frames; `grind_prefix_dev` — the dip-bottom deviation
  (a₂ = 0, pb = ()): [TDN, TUP, PUSHX] → (B, (), 1, 7, [1, R−2] + W).
  **`pred_cases` — PROVED**: a case analysis on `hstep` showing the
  only producers of a PUSH-at-a=2 source (HC with a₂ = 0, s = 2,
  g₀ ≥ 3) are TUP (source shuttle = g₀ + 2), STGA (source shuttle
  = g₀ + 1, empty pairs), PX2A (over a 0-block, frame block
  = g₀ − 1), and the TUP2 defect at g₀ = 3. The documents'
  Predecessor Lemma is then exactly the pair of invariant
  obligations: in an era grind (i) the TUP/STGA producers above
  have source shuttle exactly 4, and (ii) PX2A does not occur —
  both are consequences of the era stack invariant, whose
  preservation induction is the remaining G″ work (below).

### Grind2.v — G″ endpoint induction and the ESC-era law (#19) — Phase 29

All section forms were pre-verified against `phase21_model.py` /
`phase20_grind.py` before proving (the round decomposition of the
clean grind, `GRIND_dev(t)`'s shifted landing, the transfer/tail
bookkeeping s_regen = 2β + 1).

- **`hGRIND` — PROVED**: the word-level Grind Lemma G′ (Era.v's
  `GRIND` transplanted to `hstep`): for t + 1 ≤ a2, every pb, P, G,
  `hsteps (HC pb a2 (2t+3) 2 P G) (HB pb a2 1 (2t+6) P G)`. Same
  strong induction (prefix PUSH+TDN+TUP, loop of GRIND/TUP, final
  GRIND + POP).
- **`hGRIND_dev` — PROVED**: the deviated Grind Lemma G′ at the
  boundary frame a2 = t, pb = []:
  `hsteps (HC [] t (2t+3) 2 P G) (HB [] (t+1) 1 (2t+7) P G)` for all
  t, P, G. The recursion mirrors `hGRIND` exactly (its loop sub-calls
  are the clean `hGRIND` at frame t − 1, floors discharged from the
  loop equation); only the final spine call is `hGRIND_dev` again,
  and the base case t = 0 is the single `hPUSHX` step. Exactly one
  PUSHX occurs, on the final spine (model-checked at t = 0..3: rule
  counts 1, 5, 13, 29). This is obligation (c) in this regime: the
  PUSHX landing's continuation is the deviated grind itself, and the
  (+1, +1) landing shift is absorbed by the tail — the human proof's
  finite check is not needed here.
- **Obligation (b), clean regime — `GG_clean` PROVED**: rounds
  `grind_round` (TUP + `hGRIND(j)`) iterated by `GG_rounds` over
  Grind.v's `grind_prefix`: for R = 2m + 4 and m + 1 ≤ a2, every pb,
  P, G, `hsteps (HC pb a2 1 2 ((R, 2) :: P) G)
  (HB pb a2 1 (R + 2) ((2, 2) :: P) G)` — the G″ endpoint (transfer
  source) in the deviation-free regime.
- **`ESC_GRIND_10` — PROVED**: the R = 10 grind at the ESC frame
  a2 = 3: prefix + clean rounds 1–2 + round 3 = TUP +
  `hGRIND_dev(3)`, landing the transfer source
  `HB [] 4 1 13 ((2, 2) :: P) G` (the deviated (+1, +1) shift
  visible in a and s).
- **Transfer tail — `TAIL` PROVED**: `pop_chain_h` (the word-level
  POP chain) composed with `hTRANS2_1` (POP2): from the transfer
  source `HB pb a 1 s ((2, 2) :: (1, 1) :: (1, 2)^{β−1}) 1`, every
  s ≥ 1, β ≥ 1, the chain reaches the REGEN source
  `HB (S a :: pb) (s + β) 1 (2β + 1) [] 1` — s_regen = 2β + 1 and
  the frame inequality β ≤ a_final = s + β used by the era tail.
- **`ESC_TO_REGEN` — PROVED**: the ESC grind endpoint for
  R ∈ {2, 4, 6, 8, 10} (R = 2 by TDN alone; R = 4, 6, 8 by
  `GG_clean` at floors 1, 2, 3 ≤ 3; R = 10 by `ESC_GRIND_10`),
  composed with `TAIL`.
- **`REGEN_gen` — PROVED**: Sections.v's REGEN step list over an
  abstract frozen prefix (`POP_terminal_gen`, `StageA_blank_gen`,
  `PUSH_T_gen` over `gbsec` open forms), with `REGEN_gen_sim`
  transporting the `gcsecR` landing to the clean `gcsec` form (the
  route named in Phase 28's Grind.v summary).
- **`ERA_TAIL` — PROVED**: the era tail over an abstract frame:
  from `HB pb a 1 (2β + 1) [] 1` with β ≥ 2 and β − 1 ≤ a,
  `REGEN_gen` + TDN + the Stage-A era loop (`era_cycle` = STGA +
  `hGRIND`, iterated by `era_loop`) + Era.v's `ENTRY_gen` reach
  cfg_sim of `rcsec (0 :: 1^{a+1} ++ enc pb) (2β + 2) [(1, 2)]`.
- **`ESC_ERA_LAW` — PROVED for R ∈ {2, 4, 6, 8, 10}**: for β ≥ 2,
  from Esc.v's ESC source `esc_src (R + 6) (β − 2)`, some cost
  reaches cfg_sim of the mirror section with b2 = 2β + 2 — i.e.
  **β_next = 2β + 4** in the rcsec convention (β = b2 + 2),
  mirroring `ERA_LAW`. Assembly: `PROBE_PREFIX` +
  `PROBE_PREFIX_sim` → `ESC_TO_REGEN` (via `hsteps_sound`) →
  `ERA_TAIL` (composed via `run_sim_transfer`).
- **Obligation (a) — DISCHARGED for the grind chains**: `grind_inv`
  (B-sections at a = 0: head pair (w, r) has s + w ≤ 7 — the dip
  budget, saturated exactly by the deviated spine — gap-2 heads
  have run 2, the empty stack has s ≤ 3; C-sections at a2 = 0 with
  g0 ≥ 3 have pb = []), **`PRED_inv` — PROVED**: by case analysis
  on Grind.v's `pred_cases`, any `hstep` respecting `grind_inv` at
  both ends and landing on a PUSH-at-a=2 source forces g0 = 3,
  pb = [], and a TUP producer with source shuttle exactly 4 — the
  STGA producer contradicts the empty-stack clause, PX2A the
  frame clause, the TUP2 defect the gap-2/run clause. This is
  `pred_cases`' two obligations. **`PUSHX_only` — PROVED**: at
  `HC [] 0 3 2 pairs G` the only applicable constructor is
  `hPUSHX`. The invariant is threaded through every grind chain:
  `hstepsP` (invariant-respecting `hsteps`) versions `hGRIND_P`,
  `grind_prefix_P`, `grind_round_P`, `GG_rounds_P`, `GG_clean_P`,
  `hGRIND_dev_P`, `ESC_GRIND_10_P` are all proved, so every section
  of those chains satisfies `grind_inv` and `PRED_inv` applies to
  every step.
- **Fenced**: the R ≥ 12 ESC grind (the re-basing segment) — see
  “Remaining components” for the precise statement (`REBASE`),
  obstruction and route.

### Grind3.v — REBASE and the ESC-era law for R ≤ 40 (#19) — Phase 31

All section forms were pre-verified against `phase21_model.py`
before proving (the segment boundaries at R ∈ {12, 14, 16, 20, 22
(β = 7), 28, 38 (β = 3), 40}, and the F-4 fence check at R = 14, 18).

- **`REBASE_core` — PROVED** (no hypotheses): for every u, P, G,
  `hsteps (HC [] 4 12 2 ((u, 2) :: P) G)
  (HB [] 4 1 13 ((2, 2) :: (u, 2) :: P) G)` — PUSH + TDN + TUP, then
  `hGRIND` 0, TUP, `hGRIND` 1, TUP, `hGRIND` 2, TUP, `hGRIND_dev` 3,
  with the pair (u, 2) carried verbatim in the grind lemmas' stack.
  `REBASE_core_P` threads `grind_inv` (every boundary frame has
  a, a2 ≥ 1, so the `_pos` lemmas discharge it).
- **`REBASE` — PROVED**: for u ≥ 3, one closing `hTUP2_1`
  (r₁ = 2, w₂ = u) lands the fenced target
  `HC [5] 13 1 2 ((u − 2, 2) :: P) G` — from the F-4-corrected
  source (g0 = 12, not the fence's 11). `REBASE_P` threaded.
- **`ESC_GRIND_BIG` — PROVED**: for every R ≥ 12, P, G,
  `HC [] 3 1 2 ((R, 2) :: P) G → HC [] 4 12 2 ((R − 10, 2) :: P) G`
  (grind prefix + clean rounds 1–2 + TUP + `hGRIND_dev` 3 + TUP —
  the `ESC_GRIND_10` pattern at general R). `ESC_GRIND_BIG_P`
  threaded.
- **Endpoints — PROVED**, in `ESC_TO_REGEN`'s form (∃ pb a, the
  chain to `HB pb a 1 (2β + 1) [] 1` with β ≤ a):
  `ESC_TO_REGEN_12` (`REBASE_core` at u = 2, then `hTRANS2_2`
  consuming ((2, 2), (2, 2), (1, 1)) and `pop_chain_h`, landing
  `HB [14; 5] (β + 2) 1 (2β + 1) [] 1`); `ESC_TO_REGEN_14`
  (`REBASE` at u = 4, TDN, `TAIL`); `ESC_TO_REGEN_BIG`
  (R = 2m + 16, m ≤ 12: `REBASE` at u = 2m + 6, `GG_clean` at
  (pb = [5], a2 = 13) — floor m + 1 ≤ 13 — then `TAIL`).
- **`ESC_ERA_LAW_31` — PROVED for every even R ≤ 40**: the Phase 29
  era-law assembly factored as `ESC_ERA_LAW_of` (any endpoint in
  `ESC_TO_REGEN` form with β ≤ a yields the era law), applied to
  the Phase 29 endpoints (R ∈ {2, 4, 6, 8, 10}, via
  `ESC_ERA_LAW` itself) and the three new ones. β_next = 2β + 4
  now covers R ∈ {2, 4, 6, 8, 10, 12, 14} ∪ {2m + 16 : m ≤ 12} —
  every even R ≤ 40.
- **Fenced**: the second re-basing, R ≥ 42 — see “Remaining
  components” for the precise statement, obstruction and route.
  **(Phase 33: DONE for R ≤ 114 — Grind4.v, next section; the
  fence moves to R ≥ 116.)**

### Grind4.v — the second re-basing and the ESC-era law for R ≤ 114 (#19) — Phase 33

All section forms were pre-verified in an hstep-level simulator
mirroring Grind.v's 20 constructors exactly (validated against
the proved `hGRIND_dev` t = 0..3 chains, `REBASE_core` = 60
steps, `GG_clean` R₂ = 28 = 32,765 steps, `hGRIND` t = 12 at
a2 = 13 = 16,383 steps), and against `phase21_model.py` traces
of the re-based grind at R₂ ∈ {30, 32, 34, 40, 52, 64} (exactly
one PX2B deviation in each; min PUSH a = 3 in model coords).

- **`hGRIND_dev5` — PROVED**: the deviated grind at pb = [5],
  route (a) of the Phase 31 fence. Two-case landing:
  `hGRIND_dev5_0` (t = 0: the single `hPX2B5` step, landing
  `HB [0] 4 1 4 ((1, 1) :: (1, 2) :: (1, 2) :: P) G)`) and
  `hGRIND_dev5` (t ≥ 1: `hsteps (HC [5] t (2t+3) 2 P G)
  (HB [0] (t+4) 1 (2t+3) ((1, 2) :: (1, 2) :: (1, 2) :: P) G)`,
  strong induction mirroring `hGRIND_dev` — clean `hGRIND`
  loop at frame t − 1, spine the t − 1 instance at stack
  ((1, 2) :: P), closing POP consuming the head pair; step
  counts 2^{t+2} − 3, same as `hGRIND_dev`).
- **`round13_dev5` + `pop3_12` — PROVED**: round 13 of the
  re-based grind (TUP into the boundary grind + `hGRIND_dev5`
  13), and the three POPs absorbing the (1, 2) extras, landing
  `HB [0] 20 1 35 ((R₂ − 28, 2) :: P) G`.
- **`hGRIND_even` — PROVED**: the even-g0 grind
  `hsteps (HC pb (S a2) (2t+4) 2 P G)
  (HB pb a2 1 (2t+4) ((2, 2) :: P) G)` for t ≥ 1, t ≤ a2
  (PUSH + TDN + TUP, a loop of `hGRIND` i + TUP reaching
  g0 = 2t + 1 over the (2, 2) pair, spine `hGRIND` (t − 1)) —
  the phase-2 continuation at R₂ ≥ 32 (g0 = 34 at a2 = 20).
- **`rounds_from6` / `rounds_from4` — PROVED**: generalised
  round chains. `rounds_from6` iterates `grind_round` from
  shuttle 2j0 + 6 with an arbitrary residue g (GG_rounds fixes
  g = 2m + 2); `rounds_from4` iterates from shuttle 2j0 + 4
  with the **exact** floor j0 + m ≤ a2 (round j calls
  `hGRIND` j at frame a2) — phase 3 at a2 = 34 reaches
  R₃ ≤ 70.
- **Endpoints — PROVED**, in `ESC_TO_REGEN` form:
  `ESC_TO_REGEN_42` (the POP×3 landing is TAIL's source;
  pb = [21; 0], a = 35 + β); `ESC_TO_REGEN_44` (TUP +
  `hGRIND_even` 15 + `hTRANS2_2` + `pop_chain_h`;
  pb = [35; 20; 0], a = β + 2); `ESC_TO_REGEN_BIG2`
  (R = 2m + 46, m ≤ 34: even grind + `hTUP2_1` re-basing to
  pb = [20; 0], a2 = 34 + TDN + `rounds_from4` + `hTRANS2_1`
  + `pop_chain_h`; pb = [35; 20; 0], a = 2m + β + 4).
- **`ESC_ERA_LAW_33` — PROVED**: β_next = 2β + 4 for
  R = 42, R = 44 and R = 2m + 46 (m ≤ 34) — every even R
  with 42 ≤ R ≤ 114 — via `ESC_ERA_LAW_of`.
  **`ESC_ERA_LAW_114` — PROVED**: the combined law (Phase
  31's range together with Phase 33's): **every even
  R ≤ 114**.
- **Not threaded**: the new chains are proved at `hsteps`
  level only (no `hstepsP` versions). The era law does not
  need them — `grind_inv` threading was Phase 29's discharge
  of the Predecessor obligations for the chains those phases
  built; the Phase 33 chains are constructive `hstep`
  sequences, sound by `hstep_sound`.
- **Fenced**: the third re-basing, R ≥ 116 — see “Remaining
  components” for the precise statement, obstruction and
  route.

### Loop.v — the cross-era loop assembly — Phase 32

The ascending loop of `168016-proof.md` §4, composed from the
proved components. Entry sections are `entry_sec P beta` :=
`rcsec P (beta − 2) [(1, 2)]`; a `loop_step P beta` is a
positive-length run from `entry_sec P beta` to cfg_sim of
`entry_sec P' beta'` with beta < beta' (hence strictly larger
span: the entry section's β block has length beta).

- **`PASS` — PROVED**: the exit + stage 1 + stage 2 for an
  **arbitrary** frozen prefix P: `STAGE1_exit` (Recoord.v)
  composed with `DSTAGE2` (DiagPass.v) via `run_sim_transfer`:
  run ((Tk K + 6) + (2K² + 13K + 14) + Tk K) from
  `rcsec P K [(1, 2)]` reaches cfg_sim of the escape section
  `rcsec P 0 ((3, 2) :: repeat (1, 2) K)`, for every K ≥ 2.
- **`esc_bridge` — PROVED (definitional)**: over a single-block
  prefix the escape section is *equal* to Esc.v's `esc_src`:
  `rcsec (false :: repeat true L) 0 ((3, 2) :: repeat (1, 2) m)
  = esc_src L m` (both are `mkCfg SC (0 :: 1^L)
  (1 1 0³ 1² (0 1²)^m)`; the rcsec form's leading 1 1 is the
  β block's last two cells). So the ESC era law applies to
  PASS's landing with no further step list.
- **`SETTLED_ITER` — PROVED**: one settled iteration at the
  trajectory prefix: from `entry_sec (entryP 31) (n + 2)`
  (n ≥ 2), RECOORD2_uncond (at B2 = 31, via `sim_entry`) +
  ERA_LAW (at era parameter n + 2) reach cfg_sim of
  `entry_sec (false :: repeat true (n + 19)) (2n + 38)` —
  β ↦ 2β + 34, and the next entry prefix is the single block
  0 1^{n+19}. `SETTLED_ITER_step` packages it as a loop_step.
- **`ERA_GEN` (explicit hypothesis, a Definition)**: the
  general-residue era law in ERA_LAW's shape: for every
  residue ρ and era parameter m ≥ 1, some cost reaches
  cfg_sim of `rcsec P' (rho + 2m + 3) [(1, 2)]` from
  `csec 16 rho 2 ((1, 1) :: repeat (1, 2) (m − 1)) 1`
  (human form, phase19 §2: s₁ = ρ + 2β_E + 2,
  β′ = ρ + 2β_E + 5). `ERA_LAW_GEN` proves the ρ = 29
  instance is ERA_LAW itself. **(Phase 35: PROVED on its
  domain** — odd ρ ≤ 33 — as `ERA_GEN_proved` in EraGen.v;
  the Definition stays as the hypothesis of the conditional
  iteration below, for the residues outside the domain.)
- **`SETTLED_ITER_GEN` — PROVED modulo ERA_GEN**: one settled
  iteration at a general two-block prefix entryP B2
  (B2 ≥ 3): β = n + 2 ↦ β′ = B2 + 2n + 7
  (= ρ + 2β_E + 5 at ρ = B2 − 2). `SETTLED_ITER_GEN_step`
  packages it as a loop_step.
- **`SETTLED_ITER_GEN_odd` — PROVED (Phase 35)**: the same
  iteration with ERA_GEN discharged via `ERA_GEN_proved`:
  unconditional for **odd B2 with 3 ≤ B2 ≤ 35**
  (ρ = B2 − 2 odd, ≤ 33). `SETTLED_ITER_GEN_odd_step`
  packages it as a loop_step. Even B2 and B2 ≥ 37 remain
  on the conditional form above.
- **`ESC_ITER` — PROVED**: one ESC iteration at a
  single-block prefix 0 1^{R+6}: PASS + `esc_bridge` +
  `ESC_ERA_LAW_31` (Grind3.v) reach cfg_sim of an entry
  section with β′ = 2β + 4 and prefix an ESC landing form
  `false :: repeat true (S a) ++ enc pb` with a ≥ β, for
  β ≥ 4 and R in ESC_ERA_LAW_31's range (every even
  R ≤ 40). `ESC_ITER_step` packages it as a loop_step.
- **`TWO_ITERS` — PROVED**: the first two iterations composed
  from the entry landing `entry_tgt 30 n`, for n = 2j + 3
  with j ≤ 12 (iteration 2's residue is R = n + 13 = 2j + 16
  ≤ 40): β = n + 2 ↦ 2n + 38 ↦ **4n + 80**, a single run
  from `entry_tgt 30 n` to cfg_sim of an entry section with
  β = 4n + 80.
- **`loop_chain` / `LOOP_NONHALT` — PROVED**: the abstract
  ascending-loop engine. Given `loop_step` at every entry
  section with β ≥ 4, chains of iterations reach entry
  sections at strictly increasing times (`loop_chain`), so
  the run from any entry section is defined at every length
  N (`LOOP_NONHALT`) — the fuel-based non-halting statement.
- **`NONHALT_FROM_R` — PROVED modulo two explicit
  hypotheses** (lemma parameters, not axioms): from
  `cfg_R`, if **(H_STD)** some run from the first I-section
  `cfg_Isec` reaches cfg_sim of an entry landing
  `entry_tgt (B2 − 1) n` with B2 ≥ 3, n ≥ 2, and
  **(H_LOOP)** `loop_step` holds at every entry section
  with β ≥ 4, then the run from `cfg_R` is total. The
  formation link R → cfg_Isec (150 steps) is
  kernel-verified (Finite.v's `R_reaches_Isec`) and is used
  unconditionally. H_LOOP's discharged instances are
  SETTLED_ITER (B2 = 31), SETTLED_ITER_GEN (general B2,
  modulo ERA_GEN; discharged for odd B2 ≤ 35 by
  SETTLED_ITER_GEN_odd, Phase 35), ESC_ITER (R ≤ 40) and
  — Phase 33 — **`ESC_ITER_114`** (PASS + `esc_bridge` +
  `ESC_ERA_LAW_114` of Grind4.v: β ↦ 2β + 4 for every even
  R ≤ 114; `ESC_ITER_114_step` packages it as a loop_step);
  its undischarged instances are exactly the ESC entries
  at R ≥ 116 (the third re-basing, fenced in Grind4.v),
  the settled entries at even B2 and B2 ≥ 37 (residues
  outside ERA_GEN's proved domain, fenced in EraGen.v),
  and the entry sections over ESC landing prefixes
  (iterations ≥ 3). H_STD is component #10's remaining
  assembly (see the table) plus the #11 exit dichotomy,
  human-proved but not mechanised.
  **(Phase 34: H_STD is DISCHARGED — see the Std.v section
  below; `NONHALT_FROM_R_std` in Std.v is this assembly
  with only H_LOOP remaining.)**

### Std.v — the standard-regime assembly (H_STD discharged) — Phase 34

The totality of the standard regime from the first I-section,
as one word-model chain at the trajectory's frozen prefix
pb = [17] (see the Phase 34 summary at the top of this file
for the identifications and the pre-verification).

- **`STD_cycle` — PROVED**: one grind/collapse cycle:
  `hsteps (HC pb A (2t + 3) 2 [] G) (HC pb A (2t + 5) 2 [] (G − 2))`
  for t + 1 ≤ A and G ≥ 3 — `hGRIND t` (Grind2.v) followed by
  `hSTGA` (Grind.v). The four bounce rules inside the grind
  preserve G; Stage A sends G ↦ G − 2 (component #11's
  bookkeeping, at chain level).
- **`STD_cycles` — PROVED**: k cycles iterated (induction on
  k): G = 2k + 2 descends to G = 2, the grind parameter
  rising t ↦ t + k, under the accumulated floor t + k + 1 ≤ A.
- **`STD_reach_entry` — PROVED**: the regime totality in
  general form: from any C-section `HC pb A 1 2 [] (2k + 6)`
  (g0 = 1, s = 2, w = [1], even G = 2k + 6 ≥ 6) with
  k + 2 ≤ A, the chain `hTDN` + `hSTGA` + (k + 1) cycles +
  final `hGRIND (k + 1)` reaches `HB pb A 1 (2k + 8) [] 2` —
  the w = [1] B-section at G = 2, i.e. the #11 exit. This is
  the exit branch of the dichotomy; the "runs forever"
  branch cannot occur for an empty-stack section, since
  every grind terminates (hGRIND is a proved chain) and G
  strictly decreases at every collapse.
- **`STD_chain` — PROVED**: the trajectory instance
  (k = 64): `hsteps (HC [17] 95 1 2 [] 134)
  (HB [17] 95 1 136 [] 2)` — 66 Stage A collapses, floors
  66 ≤ 95.
- **`Isec_hcfg` / `final_entry_src` — PROVED (definitional)**:
  `cfg_Isec = hcfg (HC [17] 95 1 2 [] 134)` and
  `hcfg (HB [17] 95 1 136 [] 2) = entry_src 95 136`, both by
  `reflexivity`.
- **`H_STD_proved` — PROVED**: `hsteps_sound` on `STD_chain`,
  transported through the two identifications and closed by
  Mirror.v's `ENTRY` (148 = 136 + 12 steps): some run from
  `cfg_Isec` reaches `entry_tgt 95 136` exactly — H_STD's
  existential with (B2, n) = (96, 136).
- **`NONHALT_FROM_R_std` — PROVED**: `NONHALT_FROM_R` with
  its first hypothesis replaced by `H_STD_proved`; the
  headline assembly now has the single hypothesis H_LOOP.
  `Print Assumptions` on all eight Std.v headlines:
  **“Closed under the global context.”**

## Component-by-component status (table of `168016-proof.md` §1)

| # | Component | Mechanisation status |
|---|---|---|
| 1 | First family S (arrivals, period law) | **Finite instances proved** (blank→S(2), S(2)→S(4), Finite.v). General S(k) induction **not started**. |
| 2 | The k = 56 break | **Not started** (finite but ≈3.2×10⁹ steps to S(56) — kernel computation infeasible; needs the analytic cascade or a certified simulation argument). |
| 3 | Transient to S′ (≈5.15×10¹⁰ steps) | **Not started** (same infeasibility). |
| 4 | S′ periods (general induction) | **Finite instances proved** (S′(2)→S′(4), S′(4)→S′(6)). The general proof (Interval/Return lemmas) **not started**. |
| 5 | The m = 132 period (analytic) | **Not started** (depends on #4 general form). |
| 6 | D(132,66) → R, 403,455 steps | **PROVED** (Finite.v). |
| 7 | R is the entry config | **Not a Rocq component** — a statement about the external phase10 simulation; corroboration only, the proof does not depend on it. |
| 8 | Halt criterion (M1–M4) | **PROVED** (TM.v, complete). |
| 9 | Formation R → first I-section, 150 steps | **PROVED** (Finite.v). |
| 10 | Standard regime: five rules total on I, I preserved, event-clean | **Rule soundness PROVED** (Phase 25: TUP added; all five rules — TDN/PUSH/POP-general/TUP/Stage A — are proved for all parameters in Sections.v). **Assembly DISCHARGED for the trajectory (Phase 34, Std.v)**: hypothesis **H_STD** of Loop.v's `NONHALT_FROM_R` is proved (`H_STD_proved`, (B2, n) = (96, 136)) by exhibiting the concrete chain from `cfg_Isec` — TDN + Stage A + 65 grind/collapse cycles (`STD_cycle` = `hGRIND t` + `hSTGA`) + final `hGRIND 65` — through `hsteps_sound` and `ENTRY`; `NONHALT_FROM_R_std` restates the assembly with only H_LOOP remaining. The event-cleanliness reading is discharged per rule (each `run … = Some …` certifies no halting step en route, via `halt_iff`). Not formalised, and no longer load-bearing: the invariant-I⁺ preservation induction over an *arbitrary* rule sequence. |
| 11 | G bookkeeping (only Stage A changes G, by −2) | **PROVED (discharged by the five statements, Phase 25)** — see Sections.v summary above. |
| 12 | Right-edge entry excursion (cost s + 12) | **PROVED** (Phase 25: `ENTRY` + `ENTRY_tape`, Mirror.v; generalised to abstract tails as `ENTRY_gen`, Era.v, Phase 27). |
| 13 | Right-edge mirror rules + invariant RI | **PROVED** (Phase 25: RTDN/RPUSH/RPOP/RTUP/RPROBE + `RPROBE_tape` + RI parity preservation, Mirror.v). The joint invariant J of the token pass belongs to #14. |
| 14 | Token pass / Cycle Lemma (min β = β_E − k) | **PROVED** (Phase 26: `CYCLE` with duration Dk k = 3·2^{k+3} − 4, `CYCLE_H` attainment of H_k at word β = β_E − k, orbit lower bound via `borbit_cycle` + `borbit_lb`, TokenPass.v). |
| 15 | The β = 2 exit (H_{β_E−2} at T(β_E); X(β_E) successor) | **PROVED** (Phase 26: `EXIT` + `EXIT_time` + `EXIT_entry`, TokenPass.v; finite instances β_E = 4, 8 also kernel-verified in Finite.v). |
| 16 | Re-coordinatisation to the single-block I-frame | **PROVED in full** (Phase 27, Recoord.v: `STAGE1`/`STAGE1_exit`, `STAGE3` for all B2 ≥ 2; Phase 30: stage 2 in general — `DSTAGE2` for every frozen prefix, DiagPass.v — giving `STAGE2_proved` and the unconditional composition `RECOORD2_uncond`). The seven kernel-verified stage-2 instances (B2 = 31 for n ∈ {2, 4, 6, 8, 10}; n = 2 for B2 ∈ {15, 47}) remain as regression checks. The single-block (ESC) frame's delivered pieces are in Esc.v (see #19). |
| 17 | REGEN; POP-general | **PROVED** (Phase 25: POP-general in Sections.v (Phase 23); `REGEN` assembled from POP_terminal + StageA_blank + PUSH_T, with `REGEN_tape`). |
| 18 | Era / reset map (Grind Lemma G′, s₁ = 2β_E + 31, β′ = 2β_E + 34) | **Deviation-free assembly PROVED** (Phase 27, Era.v: `ENTRY_gen`, `GRIND` (G′ endpoint form, frame floor as its hypothesis), `POP_CHAIN`, `ERA_LAW` with s₁ = 2β_E + 31, odd-G excluded, β′ = 2β_E + 34 > β_E). **Fenced**: the dip clause as a sequence statement (precise statement + route in the Era.v summary above; the Loop.v assembly does not use it — ERA_LAW discharges GRIND's floor directly). **Cross-era loop assembly DONE** (Phase 32, Loop.v: `PASS`, `SETTLED_ITER`, `ESC_ITER`, `TWO_ITERS`, `LOOP_NONHALT`, `NONHALT_FROM_R`; Phase 33: `ESC_ITER_114`), modulo the explicit hypotheses H_STD (#10 — **discharged Phase 34**, Std.v), ERA_GEN (**proved on its domain — odd ρ ≤ 33 — Phase 35**, EraGen.v; the general settled iteration is discharged for odd B2 ≤ 35 via `SETTLED_ITER_GEN_odd`) and the undischarged H_LOOP instances (ESC entries at R ≥ 116; settled entries at even B2 / B2 ≥ 37; ESC-landing prefixes). |
| 19 | Re-formation (iteration 2) + deviation rules (PUSHX, PX2A/PX2B, TRANS2/TUP2, CGAP2; G″ induction) | **Step lists PROVED** (Phase 27, Esc.v: `POP2`, `PROBE_PREFIX`; Phase 28, Dev.v: PUSHX + follow-on, PX2A (incl. b = 2), PX2B b = 2..6, CGAP2 probe + both dispatches, TUP2 k = 1, TRANS2 k = 1/2, TUP2 defect with the F-3-corrected landing — all for all parameters). **Word model PROVED** (Phase 28, Grind.v: frame-general lists, `hstep` (20 rules) + `hstep_sound`/`hsteps_sound`, `grind_prefix` + `grind_prefix_dev`, `pred_cases`). **G″ endpoint induction PROVED in the clean regime and at the ESC frame** (Phase 29, Grind2.v: `hGRIND`, `GG_clean` for all frames under the floor, `hGRIND_dev` for the boundary frame, `ESC_GRIND_10`); **era stack invariant + Predecessor discharge PROVED** (`grind_inv`, `PRED_inv`, `PUSHX_only`, threaded `hstepsP` grind chains); **ESC-era law β_next = 2β + 4 PROVED for R ∈ {2, 4, 6, 8, 10}** (`ESC_ERA_LAW`). **Re-basing segment PROVED** (Phase 31, Grind3.v: `REBASE` from the F-4-corrected source, `ESC_GRIND_BIG`, endpoints for R = 12 / 14 / 2m + 16) and **ESC-era law extended to every even R ≤ 40** (`ESC_ERA_LAW_31`). **Second re-basing PROVED for R ≤ 114** (Phase 33, Grind4.v: `hGRIND_dev5` (the pb = [5] deviated grind, base case `hPX2B5`), `hGRIND_even`, `rounds_from4`/`rounds_from6`, endpoints for R = 42 / 44 / 2m + 46, `ESC_ERA_LAW_33`, and the combined **`ESC_ERA_LAW_114`**). **Open**: the third re-basing (R ≥ 116, fenced precisely below). The ESC iteration is composed into the cross-era loop in Loop.v (`ESC_ITER`, `TWO_ITERS`, Phase 32; `ESC_ITER_114`, Phase 33); the third re-basing is exactly the R ≥ 116 instance of hypothesis H_LOOP there. (The fenced TUP2 stage-2 shape (k ≥ 2, r_k = 1) is proven unreachable in era grinds at human level; it remains fenced.) |

## Remaining components — precise statements, obstructions, routes

- **#14 Cycle Lemma Γ — DONE (Phase 26, TokenPass.v).** Formalised as
  documented: B-start word model with invariant J (`Jg`), the two round
  maps and the composed map Ψ proved from the mirror rules, the Suffix
  Lemma as step-level transports (`psi_step_front`, `psi_step_last2f`),
  the orbit recursion (`borbit_cycle`) by induction on k, Γ as `CYCLE`
  with D_k = 3·2^{k+3} − 4, and the min-β facts as `CYCLE_H`
  (attainment) + `borbit_lb` (orbit lower bound) at section granularity.
- **#15 exit (general) — DONE (Phase 26, TokenPass.v).** `EXIT`:
  H_{β_E−2} is reached at Tk(β_E − 2) (closed form `EXIT_time`) and the
  RTDN step list fires event-clean, landing cfg_sim at the B-section
  (B, 4, (1^{β_E−2}), (2^{β_E−2})) in shifted coordinates;
  `EXIT_entry` instantiates at the entry prefix. Instances β_E = 4, 8
  remain kernel-verified (Finite.v).
- **#16 stage 2 (general) — DONE (Phase 30, DiagPass.v).** Proved as
  `DSTAGE2` for every frozen prefix P (stronger than the `entryP B2`
  instance `RECOORD2` needed): the descent + walk decomposition, with
  the descent orbit built by the T₁/join/T₂ recursion over `fchain`
  (the `wok`-carrying `borbit` analogue) at cost `bcost k`, and the
  walk iterated at cost `Dsum n`. `STAGE2_proved` and
  `RECOORD2_uncond` in Recoord.v discharge #16's two-block landing
  unconditionally. The route taken differs slightly from the one
  sketched in Phase 27: the orbit recursion is on the descent's own
  B-start chain (T₁ = last gap + 2 with block + 1, T₂ = last gap − 2
  with a gap 3 appended), not on the Phase 17 suffix recursion
  directly; the suffix enters only through `psi_step_front_list`
  (DESC's carried suffix) and the walk's nested descents.
- **#16 stage 1 / stage 3 — DONE (Phase 27, Recoord.v)** as itemised
  above; `RECOORD2` composes all three stages with the exit.
- **#18 era law — deviation-free assembly DONE (Phase 27, Era.v).**
  Remaining: (a) the dip clause as a sequence statement (statement and
  route in the Era.v summary; not used by the Phase 32 assembly);
  (b) the **general-residue era law — DONE on its domain
  (Phase 35, EraGen.v).** `ERA_GEN_proved`: Loop.v's `ERA_GEN`
  statement for every odd ρ ≤ 33 and every m ≥ 1, by Era.v's
  assembly with ρ = 2t + 1 (absorption `GRIND` at t − 1,
  resp. `TDN` at ρ = 1; POP_CHAIN bookkeeping
  s₁ = ρ + 2β_E + 2; the era-loop invariant
  s + G = ρ + 2β_E + 5 over J = t + m cycles). The frame
  a2 = 16 is NOT replaced by a general frame: it is the
  settled frame's own constant (stage 3 lands at a = 16 for
  every two-block prefix), and both floor families (residue
  grind; era-loop grinds) bound t ≤ 16, i.e. ρ ≤ 33.
  Fenced, with machine-checked obstructions
  (`rocq/era_gen_verify.py`): ρ ≥ 35 odd (the grind's dip
  (ρ − 1)/2 exceeds the frame; the absorption landing is
  never reached at (35, 1) in 20,000,000 steps) and ρ even
  (G′ is odd-only — the absorption landing is never
  reached at (30, 1) — and the Stage-A era's G parity is
  load-bearing). Loop.v's `SETTLED_ITER_GEN_odd`
  discharges the general settled iteration for odd
  B2 ≤ 35; even B2 and B2 ≥ 37 remain conditional on the
  unrestricted `ERA_GEN`.
- **Cross-era loop assembly — DONE (Phase 32, Loop.v)**, modulo
  three precisely-stated residuals, all carried as explicit lemma
  parameters (never axioms/admits) in `NONHALT_FROM_R`:
  **(H_STD) — DONE (Phase 34, Std.v).** The route taken is
  the G-descent bookkeeping directly, at the trajectory
  instance: `cfg_Isec` is definitionally the word-model
  section `HC [17] 95 1 2 [] 134`, the exit section
  `HB [17] 95 1 136 [] 2` is definitionally `entry_src 95 136`,
  and the chain between them is `hTDN` + `hSTGA` + 65
  grind/collapse cycles (`hGRIND t` + `hSTGA`, floors
  t + 1 ≤ 95) + `hGRIND 65` (`STD_chain`), closed by
  `ENTRY` to `entry_tgt 95 136` — (B2, n) = (96, 136),
  66 collapses, G: 134 → 2 (`H_STD_proved`;
  `NONHALT_FROM_R_std` is the assembly with H_STD
  discharged). The general I⁺-preservation induction over
  arbitrary rule sequences was not needed: H_STD quantifies
  only over the trajectory from `cfg_Isec`, whose rule
  sequence is the exhibited chain. **(ERA_GEN) — DONE on
  its domain (Phase 35,** EraGen.v: odd ρ ≤ 33); the
  complementary residues (ρ even, ρ ≥ 35) remain fenced
  there with machine-checked obstructions.
  **(H_LOOP rest)** `loop_step` at the entry sections not discharged
  in Loop.v: ESC entries with R ≥ 116 (the third re-basing, fenced
  in the #19 bullet; the second re-basing R ≤ 114 was discharged
  in Phase 33), settled entries at entryP B2 with B2 even or
  B2 ≥ 37 (ERA_GEN's complementary domain, fenced in
  EraGen.v; discharged for odd B2 ≤ 35 in Phase 35), and
  entry sections over ESC-era landing
  prefixes `0 1^(a+1) ++ enc pb` (iterations ≥ 3: PASS already
  covers their pass; their re-formation is the two-block stage 3
  at a general far block — STAGE3 is proved for abstract tails Q
  but at the entryP-shaped near block — composed with ERA_GEN's
  canonical grind on its proved domain). With the third
  re-basing and the remaining ERA_GEN-domain instances
  discharged (H_STD was discharged in Phase 34, ERA_GEN on
  its domain in Phase 35),
  `NONHALT_FROM_R` becomes unconditional from `cfg_R`;
  the blank-tape → R segment (#1–#5) would remain.
- **#19 deviations — step lists DONE (Phase 28, Dev.v); G″ endpoint
  induction and ESC-era law DONE for R ≤ 10 (Phase 29, Grind2.v).**
  Obligations (a)–(c) of Phase 28 are discharged in the regime the
  ESC trajectory uses (see the Grind2.v section above): the clean
  G″ endpoint holds for all frames under the floor (`GG_clean`),
  the deviated boundary grind is a proved induction
  (`hGRIND_dev`), the invariant is threaded (`hstepsP` chains) and
  the Predecessor obligations are discharged (`PRED_inv`,
  `PUSHX_only`), and `ESC_ERA_LAW` gives β_next = 2β + 4 for
  R ∈ {2, 4, 6, 8, 10}. **`REBASE` — DONE (Phase 31, Grind3.v),
  with finding F-4.** The fence's source had g0 = 11; the grind's
  actual section after round 3 (deviated) and its TUP is
  `HC [] 4 12 2 ((R−10, 2) :: P) 1` — the fence's 11 is the s′′ of
  that TUP (phase21_model traces at R = 14, 18: the g0 = 11
  section never occurs, and its chain does not reach the target;
  the g0 = 12 chain reaches it, boundaries verified at
  R ∈ {12, 14, 16, 20, 22, 28, 38, 40}). The corrected segment is
  proved for every carried stack (`REBASE_core`, no hypotheses on
  the passenger pair u; `REBASE` for u ≥ 3), composed with
  `ESC_GRIND_BIG`; the ESC-era law now covers every even R ≤ 40
  (`ESC_ERA_LAW_31`). The fence's measured decomposition (one
  further PUSHX, three POPs, one TUP2 hTUP2_1 at the end) is
  confirmed and located: the PUSHX is `hGRIND_dev` 3's base step,
  the three POPs its closing spine. **The second re-basing —
  DONE for R ≤ 114 (Phase 33, Grind4.v), via route (a) at
  pb = [5].** Route (b) was reinterpreted: the Phase 29 model
  evidence (PUSHX = 0, min PUSH a = 3 at a₀ = 15) is literally
  true because the deviation at pb = [5] is PX2B5, not PUSHX —
  the re-based grind deviates exactly once (verified in the
  hstep simulator and in `phase21_model.py` traces at
  R₂ ∈ {30, 32, 34, 40, 52, 64}), so no dip-shallowness
  invariant can make the rounds clean; the deviated recursion
  had to be derived, and was: `hGRIND_dev5` (base case
  `hPX2B5`, two-case landing), `round13_dev5`, `pop3_12`,
  then for R₂ ≥ 32 the even-g0 grind `hGRIND_even` and the
  phase-3 rounds `rounds_from4` at a2 = 34 closing at
  R₃ ≤ 70, giving `ESC_ERA_LAW_33` and the combined
  `ESC_ERA_LAW_114` (every even R ≤ 114), and
  `ESC_ITER_114` in Loop.v. **Remaining, fenced precisely —
  the third re-basing (R ≥ 116):** phase 3's rounds at
  a2 = 34, pb = [20; 0] stay clean while the last round's
  `hGRIND` floor holds (round j = R₃/2 − 2 needs
  R₃/2 − 1 ≤ 34, i.e. R₃ ≤ 70). At R₃ = 72 (R₂ = 104,
  R = 116) the boundary grind g0 = 71 at a2 = 34 descends
  its 34-level spine to
  `HC [20; 0] 0 3 2 ((1, 2) :: (1, 2) :: (1, 2) :: …)` —
  verified in the hstep simulator (small analogue t = 3 at
  a2 = 3: stuck after the spine descent at exactly that
  shape) — where **no `hstep` constructor applies**:
  `hPX2A` requires the second prefix block to be S p′ ≥ 1
  (here the block under [20] is 0), `hPX2A2` requires
  b = 2, and the phase21 model agrees (step at the model
  section returns “PX2A guard b=20 p=0”). Route: derive a
  NEW machine-level deviation step list at pb = [20; 0]
  (Phase-28-style: the excursion at a C-section with
  g0 = 3, a = 2 over the two-block prefix (0, 20) — its
  landing must be computed from the machine, as F-3/F-4
  warn against trusting the documents' pattern), add an
  `hstep` constructor + soundness, then a deviated grind
  at pb = [20; 0] mirroring `hGRIND_dev5`, and re-derive
  the phase-3 tail absorption; phases beyond phase 3 are
  open (each further re-basing grows pb and the phase
  frame). The fenced TUP2 stage-2 shape stays fenced
  (era-unreachable).
- **#1/#4/#5 S/S′ side**. The S(k) and S′(m) period inductions are
  word-level inductions of the same character as G′ (the human proofs
  are `proof-168016.md`, `sprime-phase2-proof.md`, `ud-proof.md`); #5 is
  the analytic evaluation at m = 132 on top of #4. No conceptual blocker;
  substantial formalisation work.
- **#2/#3**. Finite but ≈3.2×10⁹ / ≈5.15×10¹⁰ steps: kernel computation
  (`vm_compute`) is infeasible at these lengths. Viable routes: (a) the
  analytic cascade already used at human level for #2's break and #3's
  transient (formalise the cascade, not the steps); (b) a certified
  simulator (a verified fast executor with a reflection lemma). **No
  axioms will be introduced for these** — they stay stated goals here
  until one of the routes is carried out.

## Honest gaps and what remains

- The mechanisation now covers the **reduction core** (M1–M4), **every
  feasible finite segment**, **all five standard rules + REGEN** in the
  I⁺ frame, the **complete right-edge mirror system + entry**, the
  **token pass with the Cycle Lemma and the general exit** (#14/#15),
  **re-coordinatisation in full** (#16: stages 1 and 3 and the
  conditional composition, Phase 27; **stage 2 in general and the
  unconditional composition**, Phase 30, DiagPass.v), the
  **deviation-free era law** (#18: G′, s₁ = 2β_E + 31,
  β′ = 2β_E + 34), the **ESC pieces** (`POP2`, probe prefix), **all of
  #19's deviation step lists** (Phase 28, Dev.v), the **hybrid word
  model with soundness, the grind prefix reductions and the
  Predecessor case analysis** (Phase 28, Grind.v), and — Phase 29 —
  the **G″ endpoint induction in the clean and ESC regimes, the era
  stack invariant with the Predecessor discharge, and the ESC-era
  law β_next = 2β + 4 for R ≤ 10** (Grind2.v), and — Phase 31 —
  **`REBASE` and the ESC-era law for every even R ≤ 40**
  (Grind3.v), and — Phase 32 — the **cross-era loop assembly**
  (Loop.v): PASS, both era iterations as loop steps, the first
  two iterations composed in full, the ascending-loop engine,
  and `NONHALT_FROM_R`, and — Phase 33 — the **second
  re-basing and the ESC-era law for every even R ≤ 114**
  (Grind4.v: `hGRIND_dev5`, `hGRIND_even`, `ESC_ERA_LAW_114`;
  Loop.v: `ESC_ITER_114`), and — Phase 34 — the
  **standard-regime assembly** (Std.v: `STD_cycle`,
  `STD_cycles`, `STD_reach_entry`, `STD_chain`,
  `H_STD_proved`, `NONHALT_FROM_R_std`), and — Phase 35 — the
  **general-residue era law on its domain** (EraGen.v:
  `ERA_GEN_proved` for odd ρ ≤ 33; Loop.v:
  `SETTLED_ITER_GEN_odd`). It does **not** yet give an
  unconditional Rocq proof of non-halting: `NONHALT_FROM_R`
  rested on the two explicit hypotheses H_STD and H_LOOP;
  **H_STD is discharged (Phase 34)**, and H_LOOP's
  undischarged instances are the general settled iteration
  at even B2 and B2 ≥ 37 (ERA_GEN's complementary domain,
  fenced in Phase 35), the third re-basing of #19 (R ≥ 116)
  and the iterations ≥ 3 re-formation at ESC landing
  prefixes; and the theorem starts at `cfg_R` — the S/S′
  inductions (#1/#4/#5) and #2/#3 (the blank-tape → R
  segment) are open, as itemised above.
- Suggested next order: the third re-basing (R ≥ 116; new
  deviation step list at pb = [20; 0]) → iterations ≥ 3
  re-formation (incl. the settled instances at even B2 /
  B2 ≥ 37, i.e. ERA_GEN's complementary domain) → S/S′
  inductions and m = 132 (#1/#4/#5) → #2/#3 strategy.

## Files

- `rocq/TM.v` (478 lines) — framework, entry lemmas, M1–M4.
- `rocq/Configs.v` (40 lines) — concrete configs, generated by
  `rocq/gen_configs.py` from the documents' closed forms + simulator.
- `rocq/Finite.v` (195 lines) — canonical form, `seg_check`, the checks.
- `rocq/Sections.v` (452 lines) — sweeps, probe, the five standard rules
  (TDN/PUSH/POP-general/TUP/Stage A), blank-end forms and REGEN.
- `rocq/Mirror.v` (395 lines) — mirror frame over an abstract frozen
  prefix, ENTRY, the five mirror rules, RI parity preservation, tape
  corollaries.
- `rocq/TokenPass.v` (1388 lines) — cfg_sim transport machinery, the
  token-pass word model (phase/excursions/rounds/Ψ), the Suffix Lemma
  transports, the orbit recursion, the Cycle Lemma Γ, cycles 0–1, and
  the general exit (Phase 26).
- `rocq/DiagPass.v` (808 lines) — #16 stage 2: the diagonal token
  pass for every frozen prefix — the T₂ map `F2` and the source
  invariant `wok`, the Ψ transports (shift / T₁ / T₂), `fchain`,
  the descent orbit recursion `dorbit_cycle`, DESC, the walk
  (`rpop_chain`, `WALK`, `WALK_ITER`), and `DSTAGE2` (Phase 30).
- `rocq/Recoord.v` (437 lines) — #16: stage 1 (RPOP chain + RPROBE),
  stage 2 statement + kernel-verified instances (Phase 28: seven
  points), stage 3 (RPUSH escape + F-sweep), the conditional
  composition RECOORD2 (Phase 27), and (Phase 30) `STAGE2_proved` +
  `RECOORD2_uncond` discharging it via DiagPass.v.
- `rocq/Era.v` (376 lines) — #18: ENTRY_gen over abstract tails, the
  Grind Lemma G′ (endpoint form, strong induction), POP_CHAIN, and
  ERA_LAW (Phase 27).
- `rocq/EraGen.v` (204 lines) — #18: `ERA_GEN_proved`, the
  general-residue era law on its domain (odd ρ ≤ 33), by
  ERA_LAW's assembly at ρ = 2t + 1 (absorption `TDN` / `GRIND`
  at t − 1, `POP_CHAIN`, `REGEN`, the Stage-A era, `ENTRY_gen`)
  (Phase 35).
- `rocq/Esc.v` (301 lines) — #19 pieces: prefix-general TUP, POP2, and
  the probe prefix E1–E5 with its cfg_sim landing (Phase 27).
- `rocq/Dev.v` (378 lines) — #19: the deviation step lists (chain
  units, PUSHX, PX2A/PX2B, CGAP2, TUP2/TRANS2 chains, the TUP2 defect
  with the F-3-corrected landing) (Phase 28).
- `rocq/Grind.v` (433 lines) — #19: frame-general step lists, the
  hybrid word model `hstep` + soundness, the grind prefix reductions,
  and the Predecessor case analysis (Phase 28).
- `rocq/Grind2.v` (1265 lines) — #19: `hGRIND` / `hGRIND_dev`
  (clean and deviated Grind Lemma G′ at word level), the clean G″
  endpoint `GG_clean`, `ESC_GRIND_10`, the transfer tail and
  `ESC_TO_REGEN`, frame-general `REGEN_gen`, the era tail
  `ERA_TAIL`, the ESC-era law `ESC_ERA_LAW` (R ≤ 10), and the era
  stack invariant `grind_inv` with `PRED_inv` / `PUSHX_only` and
  the threaded `hstepsP` grind chains (Phase 29).
- `rocq/Grind3.v` (550 lines) — #19: `REBASE_core` / `REBASE` (the
  R ≥ 12 re-basing segment, from the F-4-corrected source),
  `ESC_GRIND_BIG`, the R = 12 / 14 / 2m + 16 grind endpoints, and
  `ESC_ERA_LAW_31` — the ESC-era law β_next = 2β + 4 for every
  even R ≤ 40 (Phase 31).
- `rocq/Grind4.v` (640 lines) — #19: the second re-basing
  (Phase 33): `hGRIND_dev5` / `hGRIND_dev5_0` (the deviated
  grind at pb = [5], base case `hPX2B5`), `round13_dev5`,
  `pop3_12`, `hGRIND_even` (the even-g0 grind),
  `rounds_from6` / `rounds_from4` (generalised round chains),
  the endpoints `ESC_TO_REGEN_42` / `ESC_TO_REGEN_44` /
  `ESC_TO_REGEN_BIG2`, `ESC_ERA_LAW_33` (42 ≤ R ≤ 114) and
  `ESC_ERA_LAW_114` — the ESC-era law β_next = 2β + 4 for
  every even R ≤ 114. The R ≥ 116 fence is stated in its
  header.
- `rocq/Loop.v` (610 lines) — the cross-era loop assembly
  (Phase 32; `ESC_ITER_114` added Phase 33;
  `SETTLED_ITER_GEN_odd` added Phase 35): run-totality
  infrastructure (`run_trans_sim`, `total_transfer`),
  `entry_sec` / `loop_step`, `PASS`
  (exit + stages 1–2 for an arbitrary prefix), `esc_bridge`
  (the escape section over a single-block prefix is
  definitionally `esc_src`), `SETTLED_ITER` (B2 = 31),
  `SETTLED_ITER_GEN` (general B2, modulo the explicit
  hypothesis `ERA_GEN`; `ERA_LAW_GEN` is its ρ = 29 instance)
  and `SETTLED_ITER_GEN_odd` (odd B2 ≤ 35, unconditional via
  EraGen.v), `ESC_ITER` (β ↦ 2β + 4, R ≤ 40), `ESC_ITER_114`
  (β ↦ 2β + 4, every even R ≤ 114), `TWO_ITERS` (the first
  two iterations composed: β ↦ 4n + 80), `loop_chain` /
  `LOOP_NONHALT` (the ascending-loop engine), and
  `NONHALT_FROM_R` (non-halting from `cfg_R` modulo the
  explicit hypotheses H_STD and H_LOOP).
- `rocq/Std.v` (202 lines) — the standard-regime assembly
  (Phase 34): `STD_cycle` (one grind/collapse cycle:
  `hGRIND t` + `hSTGA`), `STD_cycles` (the G-descent
  induction), `STD_reach_entry` (regime totality for
  empty-stack I-C-sections, G = 2k + 6 at frame ≥ k + 2),
  `STD_chain` (the trajectory chain from
  `HC [17] 95 1 2 [] 134` to `HB [17] 95 1 136 [] 2`),
  the definitional identifications `Isec_hcfg` and
  `final_entry_src`, `H_STD_proved` (H_STD discharged,
  (B2, n) = (96, 136)) and `NONHALT_FROM_R_std`
  (the headline assembly modulo H_LOOP only).
- `rocq/trace_rules.py`, `rocq/trace_recoord.py`, `rocq/trace_dev.py` —
  zipper traces used to fix the exact intermediate forms of the
  segment lemmas (the third covers the Phase 28 files; all match the
  documents, except the F-3 defect row noted above).
- `rocq/std_verify.py` — the Phase 34 pre-verification: a
  machine simulator with TM.v's exact step semantics checking
  the Std.v chain's macro boundaries from `cfg_Isec` and the
  end-to-end small instances (G0 ∈ {6, 8, 10}) through ENTRY.
- `rocq/era_gen_verify.py` — the Phase 35 pre-verification: a
  machine simulator with TM.v's exact step semantics checking
  the general-ρ era boundary sequences (positive instances
  ρ ∈ {1, 27, 29, 31, 33}; negative controls ρ ∈ {30, 35}).
- `rocq/env.sh`, `rocq/coqcw` — toolchain wrapper (Coq 8.18.0).
