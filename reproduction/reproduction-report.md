# Phase 22 — Independent reproduction report: machine #168016 does not halt

Machine: `1RB1RA_1RC1LB_0LD0RA_1RF1LE_---1LF_1LC0LF` (BB(6) holdout
#168016 from the 2026-10-30 list of 608 machines; halts iff state E
reads 0). The human-level proof of non-halting was completed in
Phase 21 (`168016-proof.md`, theorem unconditional). This phase
re-implements the proof's computational content from scratch and
checks it against the transition table. **Nothing was posted
externally.** The proof documents were **not** modified; every
discrepancy found is reported below exactly as measured (§5).

## 1. The checker

`reproduce_168016.py` (this directory, single file, Python 3 stdlib
only). It is a clean-room implementation: it imports no phase* code
and reads no phase* source. Its inputs are the transition table and
the proof documents as specification (mapping in §2). One disclosed
exception: three reference checkpoints for the run out of R are read
as *data* from `phase10-expected.txt` (the dump file produced by the
original Phase 10; `third-family.md` asserts 303/303 of its dumps
matched). No code is taken from it and no other check depends on it.

Run it:

```
cd ~/workspace/busy-beaver
python3 reproduce_168016.py            # full suite
python3 reproduce_168016.py --quick    # skips the two longest sims (B2, B4)
```

Observed runtime: **232 s** full, 83 s `--quick`, on this VM
(1.5 shared vCPUs). Exit code 0 iff no check FAILs. Final result of
the reference run:

```
==== SUMMARY: 75 PASS, 0 FAIL, 2 FINDING (232.3s) ====
```

The checker contains: (a) a fresh exact step simulator with the
event audit of `post-R-proof.md` on every run — counts of reads per
(state, symbol), D-on-0 reads, C-on-0 entry contexts (entry source
and the two cells left of the head), and F-on-0 left triples watched
for the halting pattern (0,1,0) (lemma M4); (b) section parsers for
the standard frame, the single-block frame (with prefix blocks and
the a = 0 boundary form), and the mirror frame; (c) the derived rule
systems as executable word-level maps; (d) a classification driver
that predicts every successor section and its exact step cost from
the word model and requires the step simulator to land exactly
there.

## 2. What was re-implemented, from which document

| Component | Specification document |
|---|---|
| Period law P(m) = 3·2^((m+4)/2) − 6; A.1 arrival table | `proof-168016.md` A.1/A.3 |
| S′ arrival table; transient record | `postbreak-168016.md` |
| S′ period decomposition; m ≤ 130 theorem | `sprime-phases-168016.md`, `phase2-complete.md` |
| D(132,66) closed form; period offset 3·2⁶⁸ − 9183 | `m132-analysis.md` §3 |
| Halt criterion M1–M4; formation (150 steps) | `post-R-proof.md` §1, `168016-proof.md` #9 |
| Five standard rules TDN/PUSH/POP/TUP + invariant I | `bounce-derivation.md` |
| Stage A; POP-general | `reexpansion-derivation.md`, `phase19-derivations.md` §1 |
| Five mirror rules RTDN/RPUSH/RPOP/RTUP/RPROBE; ENTRY | `rightedge-derivation.md` §§2–3 |
| Cycle Lemma Γ; D_k = 3·2^{k+3} − 4; T(β_E) | `token-pass-derivation.md` §§5–6 |
| Exit successor X(β_E); segment costs 760 / 49,120 / 786,384 | `post-exit-analysis.md` §§1–2 |
| REGEN; era law s₁ = 2β_E + 31; β′ = 2β_E + 34; G′ grind | `phase19-derivations.md` §§1–2 |
| Probe prefix (Thm P20.1); POP2; ESC family, β_next = 2β + 4 | `phase20-derivations.md` §§1, 5 |
| PUSHX; PX2A; PX2B; TRANS2/TUP2; CGAP2 | `phase21-derivations.md` §§2–5, `phase20-derivations.md` §4 |

## 3. Checks and results

### Part A — the documents' arithmetic (10 checks, 9 PASS + 1 FINDING)

- **A1/A2**: every consecutive difference in the A.1 table (28
  arrivals) and in the S′ arrival table (34 arrivals) equals the
  period law P. PASS.
- **A3**: S′(132) arrival recomputed as S′(2) arrival +
  Σ_{m≤130} P(m) = **885,443,715,596,040,733,867** — exact. PASS.
- **A4–A6**: period offset of D(132,66) = 3 + 133 + (3·2⁶⁸ − 9319)
  = 3·2⁶⁸ − 9183 = 885,443,715,538,058,468,385; D at real step
  **1,770,887,431,134,099,202,252**; R at **1,770,887,431,134,099,605,707**
  (= D + 403,455). All exact. PASS.
- **A7**: D(132,66) closed form has span 246 and 178 ones. PASS.
- **A8**: the printed finite corollary — **FINDING F-1**, see §5.
- **A9**: Σ_{j<K} D_j = 3·2^{K+3} − 24 − 4K for K = 0..30. PASS.
- **A10**: canonical-section span identity = 3β_E + 51. PASS.

### Part B — finite segments by direct simulation (7 checks, all PASS)

Over 3×10⁸ steps of fresh simulation in this part alone.

- **B1**: blank tape → S(k) with the **exact configuration** (state,
  head, full run list) at every documented arrival step, k = 2..44
  (23 arrivals, up to step 50,528,815). Audit: E-on-0 = 0;
  D-on-0 = 6 (wall-building transient, as in the original record).
- **B2**: isolated S(48) → S(50) in exactly P(48) = 100,663,290 steps.
- **B3**: synthetic S′(2) → S′(30): 14 consecutive periods, each
  exactly P(m) steps with exact tapes.
- **B4**: isolated S′(44) → S′(46) in exactly P(44) = 50,331,642 steps.
- **B5**: D(132,66) → R in exactly **403,455 steps**; the first step
  is the m = 132 deviation (C reads the separator 0 → D). Audit:
  E-on-0 = 0, D-on-0 total 3.
- **B6**: R → first I-section in exactly **150 steps**: section
  (C, B2 = 97, s = 2, w = [1], G = 134); the two C-on-0 reads are
  both B-entry with context (1,1); E-on-1 = 2, D-on-1 = 2, M4 danger 0.
- **B7**: the run out of R reproduces the Phase 10 reference dumps
  at isolated steps 596,545 / 9,596,545 / 99,596,545 (state, head,
  ones, full run list all exact). Audit E-on-0 = 0.

### Part C — rule batteries on fresh parameters (26 checks, 25 PASS + 1 FINDING)

- **C1–C3**: 300 consecutive sections classified against the step
  simulator from each of three fresh two-block-frame grind
  configurations (900 sections; TDN/PUSH/POP/TUP/TRANS2-turn/STGA
  all exercised). 0 mismatches.
- **C4**: Stage A at (a, s, G) = (11, 14, 8): landing and cost 34 exact.
- **C5**: REGEN at held-out (a, s) = (7, 8), (12, 15), (6, 21): both
  documented intermediate checkpoints (merged B at 2s + 3; degenerate
  C at 4s + 13) and the landing (C, a + 2, 2, [1], G = s − 1) at cost
  4s + 22 exact.
- **C6**: ENTRY at held-out (a, s) = (7, 10), (45, 26): lands
  σ_re(s + 2) with B2 = a + 1 at cost s + 12.
- **C7**: PUSHX: cost 33, D-on-0 = 1, landing s = g + 4 — also at the
  held-out r₁ = 4 (s stays 7; see the notation note in §5).
- **C8**: PX2A at held-out (p, b) = (6, 11): cost b + 11 = 22 and the
  documented landing exact; PX2A at b = 2: cost 23, landing exact.
- **C9**: PX2B at held-out b = 11 (cost 53) and b = 15 (cost 57) and
  documented b = 4 (29), b = 2 (43): all landings exact.
- **C10**: TRANS2 family: POP2 (k = 1 turn, cost s + 9), TUP2
  (k = 1 probe, cost s + 12 at s = 12), TRANS2 turn at k = 2 — all exact.
- **C11**: CGAP2 dispatches at held-out a = 7: C-POP total 10,
  C-PUSH total 13, landings exact. The probe chain — **FINDING F-2**, §5.
- **C12**: 200 consecutive mirror-frame sections classified from each
  of two fresh right-sections (400 sections; all five mirror rules
  exercised). 0 mismatches; audit clean.

### Part D — the token pass (14 checks, all PASS)

- **D1 (word model)**: at β_E ∈ {4, 6, 8, 10, 14, 18} the model's
  orbit from σ_re satisfies the Cycle Lemma exactly: every cycle k
  has duration D_k = 3·2^{k+3} − 4, min β over C-sections exactly
  β_E − k attained at the home section H_k = (C, β_E − k,
  (1^{k+1}), (2^{k+1})), and β is restored at S_{k+1}. T values:
  T(4) = **102**, T(6) = **620**, T(8) = **2,850** (all as
  documented), and held-out **T(10) = 11,976**, **T(14) = 196,068**,
  **T(18) = 3,144,896**.
- **D2 (machine)**: the full pass from σ_re is classified
  section-by-section against the step simulator at β_E = 4, 6, 8, 10,
  14 (B2 = 31) and β_E = 10 with B2 = 43 — 18,704 sections, 0
  mismatches; the first β = 2 C-section occurs at exactly the model
  step T(β_E) in every case. Audit: E-on-0 = 0, M4 danger = 0.
- **D3**: the exit successor at T + 6 is exactly
  X(β_E) = 1¹⁷ 0 1³¹ 0² 1⁴ (0 1²)^{β_E−2} with head B at cell 50,
  at β_E = 6 and held-out β_E = 10.

### Part E — re-coordinatisation segment (5 checks, all PASS)

X(β_E) → canonical section (C, a = 18, s = 2, w = [29, 1^{β_E}],
r = [1, 2^{β_E−1}], G = 1), span 3β_E + 51:

| β_E | segment steps | status |
|---|---|---|
| 4 | 192 | residue **29** confirmed (see §5, note N-2) |
| 6 | **760** | documented value exact |
| 10 | 12,264 | held out (new value) |
| 12 | **49,120** | documented value exact |
| 16 | **786,384** | documented value exact |

Audit clean in all five runs.

### Part F — the era and the ESC family (11 checks, all PASS)

- **F1**: the β_E = 6 era from the canonical section is classified
  against the step simulator for all **32,773 sections** of the
  absorption grind (PUSH 8,192 / TDN 8,192 / TUP 8,191 / POP 8,198),
  ending exactly at the REGEN source (B, a = 22, s₁ = 43, [1], G = 1)
  — s₁ = 2·6 + 31 and a = β_E + 16 as derived. Audit clean.
- **F2**: classification continues through REGEN and the Stage-A era
  to the STGA source at s = 34: at all 16 STGA sources seen,
  s + G = 46 = s₁ + 3 exactly, G even and decreasing by 2.
- **F3**: the G′ closed form (grind of odd residue m in
  2^{(m+1)/2} − 1 rules) is validated rule-by-rule against the
  machine at m = 13 (127 rules) and m = 21 (2,047 rules).
- **F4**: word-model era evaluation (absorption grind rule-by-rule,
  Stage-A grinds via the F3-validated closed form) at held-out
  β_E = 10, 14, 20 and documented β_E = 6: in every case
  s₁ = 2β_E + 31, a_REGEN = β_E + 16, exactly one defect POP
  (r₁ = 1), min a over C-sections exactly 4, s + G = s₁ + 3 at every
  STGA source, and the era ends at ENTRY with
  **β′ = 2β_E + 34** (46 / 54 / 62 / 74).
- **F5**: ESC probe prefix (Thm P20.1): landing at exactly L + 42
  steps with D-on-0 = 2 at (L, β) = (12, 6) and held-out (18, 10),
  (26, 8).
- **F6**: the full ESC(12, 6) era is classified to ENTRY → σ_re(16):
  146 sections (grind G″(6), one TRANS2-turn = POP2, POP chain ending
  at s = 13 = 2β + 1, REGEN, Stage-A era with constant
  s + G = 16 = 2β + 4, ENTRY), β_next = 16 = 2β + 4. Audit clean.

### Part G — loop ascent (3 checks, all PASS)

- **G1**: the settled loop map β′ = 2β + 34 iterated from 24:
  24 → 82 → 198 → 430 → 894 → 1822 → 3678, strictly increasing, and
  s_regen + 3 = s₁ + 3 = β′ > β at every step.
- **G2**: the ESC loop map β_next = 2β + 4 from 8: 8 → 20 → 44 → 92
  → 188 → 380, strictly increasing, s_regen + 3 = 2β + 4 > β.
- **G3**: the deviated iteration-3 instance: s_regen = 47, era
  constant 50 = s_regen + 3 > β = 20, β″ = 50 (documented values,
  arithmetic verified).

In total ≈ **186,000 sections** were classified rule-by-rule
against the step simulator across Parts C, D and F, with **0
mismatches**, and every simulation's audit showed E-on-0 = 0 and
M4 danger = 0 (D-on-0 reads occurred only where the documents
predict them: 6 in the wall-building transient, 3 in the
D(132,66) → R segment, 2 in each ESC probe prefix, 1 in PUSHX).

## 4. Headline numbers, independently recomputed

| Claim | Documented | Recomputed | Verdict |
|---|---|---|---|
| T(4) / T(6) / T(8) | 102 / 620 / 2,850 | 102 / 620 / 2,850 (model **and** machine) | exact |
| S′(132) arrival | 885,443,715,596,040,733,867 | same, from S′(2) + Σ P(m) | exact |
| D(132,66) step | 1,770,887,431,134,099,202,252 | same | exact |
| R step | 1,770,887,431,134,099,605,707 | same (D + 403,455; 403,455 re-simulated) | exact |
| Segment X → canonical | 760 / 49,120 / 786,384 (β_E = 6/12/16) | same, by direct simulation | exact |
| Settled span | 3β_E + 51 | identity + measured at β_E = 4, 6, 10, 12, 16 | exact |
| Era law s₁ | 2β_E + 31 | model at β_E = 6, 10, 14, 20; machine at β_E = 6 | exact |
| Loop map (settled) | β′ = 2β_E + 34 | era evaluation at 4 values of β_E | exact |
| Loop map (ESC) | β_next = 2β + 4 | full machine era at β = 6 | exact |
| Finite corollary bound | 1,770,888,448,134,502,657,707 | see F-1 | **slip (×1000 in last addend)** |

## 5. Discrepancies and notation notes (reported, not patched)

**F-1 — the finite corollary's last addend is ×1000 too large.**
`168016-proof.md` (final corollary) and `third-family.md` print
non-halting within the first **1,770,888,448,134,502,657,707**
steps. Subtracting the (exactly recomputed) step of R,
1,770,887,431,134,099,605,707, leaves **1,017,000,403,052,000 =
1000 × 1,017,000,403,052**, whereas `third-family.md` §§3–4 and
`NOTES.md` (Phase 10) consistently state the isolated run from R
had reached ≈ 1.017×10¹² steps at the time of writing. The printed
bound therefore overstates the run-supported addend by a factor of
1000 (a units slip in the corollary's arithmetic). The corrected
bound is **1,770,887,432,151,100,008,759** steps. Impact: none on
the theorem — the unconditional non-halting proof (the ascending
loop) does not use the corollary; the corollary is a finite
"at least this far" statement, and both the printed and corrected
values round to ≈ 1.7709×10²¹. The exact integer 1,017,000,403,052
appears nowhere in the documents (only its 4-significant-figure
rounding does), so the identification of the intended addend is an
inference — but the factor is exactly 1000 and the prose is
unanimous. The background phase10 run has since passed
1.8×10¹² isolated steps, so the corrected bound is supported by
the run as it stands today. The proof documents were left
unchanged, per this phase's instructions.

**F-2 — CGAP2 probe-chain cost accounting.**
`phase21-derivations.md` §5 describes the CGAP2 probe chain
(w₀ = 2, w₁ = 2) recursively with re-probe cost "r₁ + 2". Measured
against the table at (a, w, G) = (5, [2, 2, 1, 3], 5), the composed
cost of probe + re-probe + C-POP is **4 + 2r₁ + 6** at
r₁ = 2, 3, 5 (totals 14, 16, 20), while the document's accounting
gives 4 + (r₁ + 2) + 6 (totals 14, 15, 17) — agreement only at
r₁ = 2, plausibly the traced instance behind the formula. The two
dispatches themselves (C-POP total 10, C-PUSH total 13, landings)
reproduce exactly (C11a/C11b). Impact: none on the theorem —
Phase 21 §6(iii) proves CGAP2 never fires in era grinds (its source
needs a TUP landing at an s = 3 B-section, and every such
B-section in an era grind has w₁ = 1), and this reproduction's era
classifications (F1, F2, F6: 0 CGAP2 firings in ≈ 164,000 classified
era sections) are consistent with that.

**N-1 — PUSHX landing notation.**
`phase20-derivations.md` §4.1 prints the PUSHX landing as
(B, a = 1, s = g + 4, w = W, r = R, G). Measured (C7, two values of
r₁): the landing gap word is **[1] + W** with **R intact** — the
merged run's POP writes the new g₀ = 1 cell and consumes no pair;
s = g + 4 and cost 33 are exactly as documented. This is a
presentational compression in the prose, not a mathematical error:
the phases' own classifications (which this reproduction
independently re-derived in F1/F6) use the correct form.

**N-2 — the β_E = 4 residue conflict is settled: 29.**
`post-exit-analysis.md` §2 says the β_E = 4 segment settles with
residue 25; `phase19-derivations.md` §2.6 corrects this to 29.
Direct simulation (Part E) gives w₀ = **29** and segment cost 192
steps, confirming Phase 19's correction.

## 6. What this checker does and does not establish

**It establishes** (independently of the original code):

1. The documents' internal arithmetic is exact (tables, sums,
   closed forms, headline step numbers), with the single exception
   F-1, which is confined to a corollary.
2. Every finite computation the proof cites is reproducible by
   direct simulation at the points listed in §3 — including the
   full D(132,66) → R segment (403,455 steps), the formation
   (150 steps), the token passes, the re-coordinatisation segments,
   one full era (β_E = 6, ≈ 164,000 classified sections including
   its Stage-A cycles), and one full ESC era.
3. The derived rule systems, re-implemented as word-level maps from
   the documents alone, agree with the step simulator on every one
   of ≈ 186,000 classified sections, including held-out parameter
   values never used in the original phases (β_E = 10, 14, 18 for
   the token pass; β_E = 10, 14, 20 for the era; b = 11, 15 for
   PX2B; (p, b) = (6, 11) for PX2A; r₁ = 4 for PUSHX; fresh grind
   configurations for both frames; ESC (18, 10) and (26, 8)).
4. The loop maps ascend: β′ = 2β_E + 34 (settled), β_next = 2β + 4
   (ESC), and s_regen + 3 > β in all three era families, so the
   loop's configurations never repeat.

**It does not establish**:

1. The hand proofs themselves. The shift-rule derivations (Probe
   Lemma, the S′ phase-2 Interval/Return Lemmas, the Grind Lemma
   G′, the Cycle Lemma's induction, the G″ induction, the stack
   invariant confining TRANS2 chains, the unreachability of the
   fenced TUP2 stage-2 shape) are mathematical arguments in the
   documents; this checker verifies their *consequences* at the
   stated points but does not re-prove them. (Mechanisation is
   Phase 23's business.)
2. The segments that are infeasible to re-simulate: blank → S(56)
   beyond k = 44 (the k = 56 break itself), the 51,539,607,417-step
   transient to S′(2), and the S′ periods for m > 46 individually.
   For these the checker verifies the documents' tables and closed
   forms arithmetically (Part A) and the period engine by direct
   simulation at every feasible point (B1–B4) — the same division
   of labour as the original proof, whose components #1–#5 are
   class (C)/(P) there.
3. Anything about machines other than #168016.

**Bottom line.** With the two findings of §5 recorded — both
confined to statements the theorem does not use — the proof of
Phase 21 **reproduces independently and in full**: every load-bearing
number, rule, segment and era law in `168016-proof.md` was
recomputed from the transition table and the documents alone, and
agrees exactly.
