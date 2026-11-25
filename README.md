# BB(6) holdout #168016 does not halt — submission package

**Machine:** `1RB1RA_1RC1LB_0LD0RA_1RF1LE_---1LF_1LC0LF`
(bbchallenge seed-database ID **168016**; #168016 of the
2026-10-30 BB(6) holdout list of 608 machines)

**Result:** started on the blank tape, this machine **never
halts**. Its only undefined transition is E-on-0.

**Status of this package:** prepared 2026-11-25 for community
submission. **It has not been posted or submitted anywhere yet.**
`draft-announcement.md` contains the announcement drafts and the
exact steps for submitting them.

## What is claimed — and what is not

- **Claimed:** a complete, unconditional **human-level proof** of
  non-halting (`168016-proof.md`, components #1–#19, all (P) or
  finite (C); no remaining hypotheses). The one underived rule
  shape in the documents (TUP2 stage 2 at k ≥ 2, r_k = 1) is
  *proved unreachable* in era grinds, not silently assumed.
- **Independently reproduced:** a clean-room checker, written
  from the proof documents alone, re-verifies the proof's
  computational content: **75 checks, 0 failures** (full run).
  It found two discrepancies, both in statements the theorem
  does not use — a ×1000 slip in the last addend of the finite
  corollary bound (F-1) and a cost-accounting slip for CGAP2,
  a rule proved never to fire in era grinds (F-2). Both are
  corrected as **dated errata** in the proof documents and are
  reported in full in `reproduction/reproduction-report.md`.
- **Mechanisation — in progress, not complete:** the Rocq
  (Coq 8.18) development in `rocq/` proves the halt criterion
  M1–M4 in full, kernel-verifies the finite segments, proves
  all five standard-regime rules (TDN / PUSH / POP-general /
  TUP / Stage A) and REGEN sound for all parameters, proves
  the right-edge entry excursion and all five mirror rules
  (RTDN / RPUSH / RPOP / RTUP / RPROBE) with the invariant RI,
  the token pass (Cycle Lemma Γ) and the general β = 2 exit,
  the re-coordinatisation in full — stages 1 and 3, the
  general stage 2 (the diagonal token pass, proved for every
  frozen prefix), and their unconditional composition — the era law
  (s₁ = 2β_E + 31, β′ = 2β_E + 34), the single-block
  escape pieces (POP2, the probe prefix), the complete
  deviation system (all step lists, the word model and its
  soundness, the grind prefix reductions, the Predecessor
  case analysis), the G″ endpoint induction with the era
  stack invariant and the Predecessor discharge, the
  ESC-family era law (β_next = 2β + 4) for every even
  R ≤ 114 including both re-basing segments, and the
  **cross-era loop assembly** — both era iterations as loop
  steps, the first two iterations composed in full, an
  ascending-loop engine, and non-halting from the record
  configuration R modulo two explicit hypotheses (stated as
  lemma parameters in `Loop.v`), of which the first — the
  standard regime's assembly — is now discharged in
  `Std.v` (from the first I-section the regime reaches the
  entry landing entry_tgt 95 136), leaving iteration at
  the entry sections not yet discharged — of which the
  general settled iteration is now also discharged on the
  era laws' proved domains in `EraGen.v` (ERA_GEN for every
  odd residue ρ ≤ 33) and `EraEven.v` (ERA_GEN_even for
  every even residue ρ ≤ 34; the general settled iteration
  unconditional for every B2 with 3 ≤ B2 ≤ 36) —
  no axioms, no admits. It does **not** yet give an
  unconditional Rocq proof of non-halting;
  `rocq/mechanisation-status.md`
  maps every proof component to its mechanisation status.

## The proof in five lines

Halting is equivalent to one tape pattern (lemmas M1–M4): an
F-on-0 read whose left triple is (0,1,0). A finite transient —
two bounce families S(k), S′(m), an analytic deviation at
m = 132, and a 403,455-step computed segment — reaches the
record tape R = `1^17 0 1^97 0 1^137 0` at step
1,770,887,431,134,099,605,707. After R the dynamics is a
two-regime system of derived word-level rules (standard regime
+ right-edge mirror regime) organised in eras; the token pass
(Cycle Lemma) forces an exit at β = 2, and the continuation
re-coordinatises into the standard regime. One full loop maps
β ↦ 2β + 34 with strictly growing span, so no configuration
ever repeats and the halting pattern never occurs.
See `proof-summary-168016.md` for the full summary.

## File map

```
README.md                  this file
draft-announcement.md      announcement drafts + submission checklist (NOT posted)
proof-summary-168016.md    self-contained summary of the proof
168016-proof.md            the full proof: theorem + component table #1–#19
proof/                     the derivation files the proof depends on
  proof-168016.md            family S, arrival table A.1
  postbreak-168016.md        the k = 56 break, transient, S′ arrivals
  sprime-phases-168016.md    family S′ phase decomposition
  sprime-phase2-proof.md     S′ phase 2
  ud-proof.md                Interval Lemma / U_d chain decomposition
  phase2-complete.md         S′ period proof assembly
  m132-analysis.md           the m = 132 deviation; D(132,66); R
  third-family.md            the post-R regime from R (Phase 10)
  transient-analysis.md      transient / pushdown analysis (Phases 10–11)
  post-R-proof.md            halt criterion M1–M4; the post-R system
  bounce-derivation.md       the five standard rules + invariant I
  reexpansion-derivation.md  Stage A; G bookkeeping
  rightedge-derivation.md    ENTRY; the five mirror rules + invariant RI
  token-pass-derivation.md   Cycle Lemma; the β = 2 exit
  post-exit-analysis.md      exit continuation; re-coordinatisation; era data
  phase19-derivations.md     REGEN; era closed form; re-coordinatisation (P)
  phase20-derivations.md     single-block re-formation; boundary forms
  phase21-derivations.md     deviation system PUSHX/PX2A/PX2B/TRANS2/TUP2/CGAP2 (P)
reproduction/
  reproduce_168016.py        clean-room reproduction checker (Python 3, stdlib only)
  reproduction-report.md     what was re-implemented, every check, findings F-1/F-2
  phase10-expected.txt       reference checkpoints read by the checker as data
                             (disclosed in the checker header; no code is taken from it)
rocq/
  TM.v                       machine, execution, entry lemmas, M1–M4 (proved)
  Configs.v                  concrete configurations (generated by gen_configs.py)
  Finite.v                   finite segments by kernel computation (proved)
  Sections.v                 five standard rules + REGEN soundness (proved)
  Mirror.v                   right-edge entry + five mirror rules + RI (proved)
  TokenPass.v                token pass: Cycle Lemma + the general exit (proved)
  DiagPass.v                 stage 2: the diagonal token pass for every frozen prefix (proved)
  Recoord.v                  re-coordinatisation stages 1-3 + unconditional composition (proved)
  Era.v                      era law: Grind Lemma G' + ERA_LAW (proved)
  EraGen.v                   general-residue era law ERA_GEN for every odd rho <= 33 (proved)
  EraEven.v                  even-residue era law ERA_GEN_even for every even rho <= 34: rotation absorption, beta' = 2m + 4 independent of rho (proved)
  Esc.v                      single-block escape pieces: POP2 + probe prefix (proved)
  Dev.v                      deviation step lists: PUSHX/PX2A/PX2B/CGAP2/TRANS2/TUP2/defect + PX2A0/PX2B0 + PX2Bgen (the uniform single-block family, b >= 5) (proved)
  Grind.v                    word model + soundness, grind prefix, Predecessor analysis (proved)
  Grind2.v                   G'' endpoint induction + ESC-era law for R <= 10 (proved)
  Grind3.v                   REBASE (R >= 12 re-basing) + ESC-era law for every even R <= 40 (proved)
  Grind4.v                   second re-basing (deviated grind at prefix [5]) + ESC-era law for every even R <= 114 (proved)
  Grind5.v                   third re-basing dip bottoms (PX2A0/PX2B0) + deviated grind at prefix [0] (proved)
  Grind6.v                   merged unwind at R = 116 + phase-4/5 continuations: ESC-era law for every even R <= 268 (proved)
  Grind7.v                   phase-6 merged unwind: general boundary descent DIPDESC + GRIND39_MID: ESC-era law for every even R <= 602 (proved)
  Grind8.v                   phase-7 merged unwind: DIPDESC at [110; 19; 0] + hPX2A + GRIND108_MID: ESC-era law for every even R <= 1276 (proved)
  Grind9.v                   phase-8 entry (R >= 1278): funnel PHASE8_TO_MID + continuation stages A-C + DIPDESC_even (proved); the continuation past stage C is a full-stack cascade, fenced with machine evidence (era law still closes at R <= 1276)
  Grind10.v                  the cascade landing (Phase 42): CASCADE_STAGE4 + CASCADE_POPFIN (the cascade's last two stages, proved in general); the phase-8 era law for every even R >= 1278 proved modulo the single statement CASCADE_LANDING (the cascade's landing on the era shape, stress-tested in hsim42.py)
  Loop.v                     cross-era loop assembly: PASS, both era iterations, LOOP_NONHALT, NONHALT_FROM_R (proved modulo one explicit hypothesis H_LOOP; general settled iteration unconditional for every 3 <= B2 <= 36; ESC iteration unconditional for every even R <= 1276 and modulo CASCADE_LANDING above)
  Std.v                      standard-regime assembly: STD_reach_entry, H_STD discharged, NONHALT_FROM_R_std (proved)
  gen_configs.py             generator for Configs.v
  trace_rules.py             zipper traces used to fix the segment lemmas' forms
  trace_recoord.py           zipper traces for the Recoord/Era/Esc forms
  trace_dev.py               zipper traces for the Dev/Grind forms
  std_verify.py              pre-verification of the Std.v chain on the real machine
  era_gen_verify.py          pre-verification of the EraGen.v boundary sequences on the real machine
  era_even_verify.py         pre-verification of the EraEven.v boundary sequences on the real machine
  era_fence35_verify.py      fence evidence for residues rho >= 35 (observed absorptions + 60M-step budget checks)
  hsim36.py                  pre-verification of the Phase 36 step lists and deviated grinds (word simulator + machine recogniser)
  hsim37.py                  pre-verification of the Phase 37 merged unwind (word simulator + machine recogniser)
  hsim38.py                  pre-verification of the Phase 38 phase-6 unwind (word simulator + machine recogniser)
  hsim40.py                  pre-verification of the Phase 40 phase-7 unwind (word simulator + machine recogniser)
  hsim41.py                  pre-verification of the Phase 41 phase-8 entry/stages + the cascade fence evidence (word simulator + machine recogniser)
  hsim42.py                  stress test of CASCADE_LANDING: ~50 shrunk-family cascade landings on the era shape, the odd-residue parity fence, machine REGEN at the terminal (word simulator + machine recogniser)
  mechanisation-status.md    component-by-component mechanisation status
  coqcw, env.sh              build wrapper for the authors' local Coq 8.18 toolchain
```

Not included: the internal project log (`NOTES.md`, Phases
1–42), simulators and run artefacts of the working phases, and
the still-running long simulation from R (component #7 is
corroboration only; the proof does not depend on it).

## How to verify

### 1. Read

`proof-summary-168016.md` (30 minutes) or `168016-proof.md`
with the files under `proof/`.

### 2. Run the independent reproduction

Requires Python 3 (standard library only). The checker reads
`phase10-expected.txt` from its working directory, so run it
from `reproduction/`:

```sh
cd reproduction
python3 reproduce_168016.py            # full suite
python3 reproduce_168016.py --quick    # skips the two longest simulations
```

Expected results (reference machine: 1.5 shared vCPUs):

- full: `==== SUMMARY: 75 PASS, 0 FAIL, 2 FINDING (232.3s) ====`, exit code 0
- `--quick`: `73 PASS, 0 FAIL, 2 FINDING` (the two skipped
  simulation checks are not counted)

The 2 FINDINGs are F-1 and F-2 above: the checker compares the
documents' originally printed corollary bound and CGAP2 cost
against the transition table and reports the slips exactly;
both are corrected as dated errata in the packaged documents.
A FINDING is not a FAIL: exit code is 0 iff no check FAILs.

*Package verification (2026-11-25):* the packaged copy was run
from this directory with `--quick`: **73 PASS, 0 FAIL,
2 FINDING, 85.2 s, exit code 0** — identical findings to the
reference run.

### 3. Build the Rocq development

Requires Coq **8.18.0** (the version used by the authors; the
pre-rename name of Rocq). Compile in dependency order:

```sh
cd rocq
coqc TM.v
coqc Configs.v
coqc Finite.v
coqc Sections.v
coqc Mirror.v
coqc TokenPass.v
coqc DiagPass.v
coqc Recoord.v
coqc Era.v
coqc EraGen.v
coqc Esc.v
coqc Dev.v
coqc Grind.v
coqc Grind2.v
coqc EraEven.v
coqc Grind3.v
coqc Grind4.v
coqc Grind5.v
coqc Grind6.v
coqc Grind7.v
coqc Grind8.v
coqc Grind9.v
coqc Grind10.v
coqc Loop.v
coqc Std.v
```

(With the authors' workspace toolchain, `./coqcw <file>` does
the same via `env.sh`.) Expected: all twenty-five files compile with
**no errors**; the only warnings are benign large-nat-literal
notices in `Finite.v`. Every headline lemma was checked with
`Print Assumptions`: "Closed under the global context" — no
axioms, no admits.

*Package verification (2026-11-25):* the packaged sources were
copied to a clean directory and rebuilt from scratch: **all
twenty-five files compiled successfully**, producing `.vo` files
identical in size to the authors' build (re-verified after the
Phase 42 mechanisation update).

## Authorship and disclosure

Proof developed by Naoki Tsugawa with the assistance of an AI
agent (J.A.R.V.I.S.); the derivations, computations, checker
and Rocq sources are all included above so that every step can
be checked independently. Corrections, if any are needed, will
be issued as dated errata, as was done for findings F-1/F-2
(and F-3, a defect-landing slip found during the Phase 28
mechanisation and corrected in `proof/phase21-derivations.md`).
