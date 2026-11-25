# BB(6) holdout #168016 — hunt for a third bounce family (Phase 10, 2026-11-25)

- Seed index: **168016**
- Spec: `1RB1RA_1RC1LB_0LD0RA_1RF1LE_---1LF_1LC0LF`
- Starting point: Phase 9 (`m132-analysis.md`) — the S′ family
  provably breaks at m = 132; exact forward simulation from the
  deviation configuration D(132, 66) produced, at deviation-step
  403,455, one clean record tape

      1¹⁷ 0 1⁹⁷ 0 1¹³⁷ 0   (state B, head on the final 0, 251 ones)

  and then a bounded transient lasting the whole 3×10¹¹-step
  simulated window with no further records. This phase starts from
  that record as a synthetic entry configuration — the exact
  analogue of Phase 4's T(4, 42, 65) methodology, where the isolated
  breach configuration reproduced the real continuation and revealed
  family S′ — and pushes far beyond 3×10¹¹ steps looking for a
  third family S″, a halt, or a head-range escape.

## 1. Method

Tool: `phase10.c` (mode `run BUDGET`), transition tables copied
from the validated `phase9.c`. The start configuration **R** is the
record tape in its own frame:

    R: tape 1¹⁷ 0 1⁹⁷ 0 1¹³⁷ 0 over cells [0, 252], head at 253
       on the final 0, state B, 251 ones.

(Phase 9's frame is this frame shifted by −6: there the record has
span [−6, 246], head 247. RLE, ones and state are
translation-invariant; heads differ by +6.)

The run is **checkpointed and resumable** (`phase10.ckpt`, written
every 5×10⁹ steps and on SIGTERM/SIGINT, atomic rename, FNV checksum
of the full tape verified on load) — a service restart can lose at
most one checkpoint interval. It watches, at **every** step:

- the halt transition (E on 0) — a halt from R would, via Phase 9's
  proven segment, decide #168016 as **halting**;
- state-B edge records (head == hi_nb+1 or lo_nb−1 on a 0): the
  tape's run signature (all 1-run lengths except the last) is
  tabulated; a repeated signature with a different last block is a
  bounce-family candidate (this is exactly the S / S′ record shape:
  fixed wall · growing final block · head on the closing 0). The
  run stops for analysis after the 4th record of one signature
  (3 gaps suffice to fit a period law);
- head-range extremes (EDGE lines) — an escape from the transient's
  confinement would show here first.

## 2. Verification: the isolated start reproduces the real continuation

Phase 9's real run (`dev132q-long.log`) dumped the full
configuration every 10⁹ steps. The 303 dumps after the record
(deviation steps 10⁶ … 3×10¹¹) were extracted to
`phase10-expected.txt` and are checked **exactly** (state, head,
ones count, and the complete RLE string) at the matched isolated
steps (isolated step = deviation step − 403,455) as the run passes
them; any mismatch aborts the run.

**Result: 303 / 303 PASS.** Every dump of the real run after the
record — spanning deviation steps 10⁶ to 3×10¹¹, i.e. the whole
Phase 9 window — is reproduced **exactly** by the isolated start
from R (state, head, ones, full RLE all identical at all 303
points; the first 3 were verified by a fresh bench run from R,
the remaining 300 by the long run resumed from the bench run's
checkpoint — one continuous, checksum-verified checkpoint chain).
The record configuration R is therefore confirmed as the exact
seed of the post-record regime, in the same sense as T(4, 42, 65)
was in Phase 4. (Verification is a finite check at dump points,
not a proof of step-by-step identity; but two independent builds
agreeing at 303 full configurations across 5.5 orders of magnitude
leaves no realistic doubt.)

The checkpoint machinery was exercised for real: a service
restart SIGTERM'd the run at isolated step 828,006,914,106; the
signal handler checkpointed the exact state and the run resumed
from it with **zero progress lost**.

## 3. The transient's dynamics (Phase 9 window, deviation steps 4×10⁵ – 3×10¹¹)

Quantitative analysis of the 303 post-record dumps
(`phase10_analyze.py` over `dev132q-long.log`):

- **Rigid frame.** The nonblank span is [−6, 247] in **all 303**
  dumps; the first block is 1¹⁷ in all 303; the terminal block is
  1² in all 303. The head never leaves [−7, 248] (real frame).
- **Second block.** 1⁹⁷ at the record; in dumps it fluctuates in
  [73, 92] with no trend (series sampled every 25 dumps:
  89, 86, 82, 77, 78, 83, 78, 79, 79, 80, 74, 83, 81;
  corr(log₁₀ step, block2) = −0.36, weak and consistent with
  trendless wandering in a bounded band).
- **Working region.** Between the second block and the long gap:
  (0 1²)-pairs separated by 0-gaps that are **odd in 4684 of 4702
  sampled cases (99.6%)**; gap-value histogram over all dumps is
  close to geometric — 1: 2348, 3: 1215, 5: 572, 7: 286, 9: 132,
  11: 65, 13: 35, 15: 20, 17: 8 (ratio ≈ 0.5 per step of +2);
  the 18 even gaps (2, 4, 6) are rare defects. The number of
  1-runs ranges 11–27; ones count stays in [123, 150].
- **Long gap.** The 0-gap before the terminal 1² ranges over
  [68, 106]. Across consecutive dumps it **never increases**
  (11 decreases, 291 unchanged, 0 increases) and it is **constant
  at 68 for at least the final 25 dumps** (≥ 2.5×10¹⁰ steps) of
  the window. (A naive corr(log₁₀ step, gap) = −0.99 is an
  artefact of the few early downward ratchets; the gap is not
  steadily shrinking — stated plainly to avoid the over-reading.)

So the post-record regime, on the Phase 9 window, is a bounded,
statistically stationary-looking process: a rigid 1¹⁷ · fluctuating
second block · odd-gap pairs region · fixed long gap · terminal 1²,
with no drift in any measured statistic over the last
≈2.7×10¹¹ steps.

## 3b. The long run beyond Phase 9's window

The isolated run from R was pushed to isolated step
**1.017×10¹²** (deviation step ≈ 1.017×10¹²; ≈ **3.4× Phase 9's
3×10¹¹ window**) and is **still running** toward a budget of
3×10¹² isolated steps (checkpointed; see §4). Findings over the
extension (717 further dumps, deviation steps 3×10¹¹ –
1.016×10¹², analysed with the same script):

- **No halt** (E-on-0 watched at every step), **no state-B edge
  record of any kind** (n_brec = 0 — not even a messy one), and
  **no head-range escape**: the head has never left [−6, 248]
  (real frame) since R; the nonblank span is [−6, 247] in every
  dump.
- **No third family.** No tape of the form wall · 1ⁿ · 0 with a
  repeated wall signature occurs anywhere in the 1.017×10¹²
  isolated steps. The Phase 4 analogy — a new family emerging
  after a transient — has now been exceeded by a factor of
  ≈ 19.7 in transient length (Phase 4's transient:
  5.15×10¹⁰ steps; this one: ≥ 1.017×10¹² and counting) with no
  emergence.
- **The transient's statistics are unchanged** in the extension:
  block1 = 17 and terminal block = 2 in all 717 dumps; block2
  ∈ [70, 91], trendless; ones ∈ [126, 150]; inner gaps odd in
  99.5% of samples with the same near-geometric histogram.
- **The long gap ratchets only downward.** Combined over all
  1020 post-record dumps (deviation 10⁶ – 1.016×10¹²): the gap
  moves down 13 times, up **0** times, and is unchanged 1006
  times; in the extension it stepped 68 → 66 → 64 (two moves in
  7.2×10¹¹ steps) and sits at 64. This is an observation, not a
  mechanism: if the ratchet continued at the extension's rate,
  the gap would need ~10¹³–10¹⁴ further steps to vanish (the
  event that would merge the pairs region with the terminal 1²);
  whether it is a slow countdown or an effectively frozen
  parameter cannot be decided from the data.

## 4. Assessment

**What this phase establishes (exact simulation, not proof):**

- The synthetic record configuration R = 1¹⁷ 0 1⁹⁷ 0 1¹³⁷ 0
  (state B, head on the final 0) reproduces Phase 9's real
  continuation exactly at all 303 checkable dumps — R is the
  confirmed entry configuration of the post-S′ regime.
- From R, the machine runs at least 1.017×10¹² further steps
  with no halt, no bounce record, and no head-range escape.
  Combined with Phase 9's proven-plus-simulated segment, the
  non-halting statement for #168016 extends to its first
  **1,770,887,432,151,100,008,759 steps (≈ 1.7709×10²¹)**
  as of the last dump cited here (the run continues; same
  caveats as Phase 9 §5: the analytic segment rests on the
  unmechanised Phase 5–8 human proofs).

  *Erratum (Phase 23, 2026-11-25).* The bound above was
  printed in earlier revisions as 1,770,888,448,134,502,657,707
  — a ×1000 slip in its last addend (the run cited here
  reached ≈ 1.017×10¹² steps, as stated in the bullet above).
  Corrected value: **1,770,887,432,151,100,008,759** steps.
  See `reproduction-report.md` §5, finding **F-1**.

**What it does not establish:** #168016 remains **undecided**.
Unlike the two previous breaks, this post-break regime shows no
sign of resolving into a bounce family on any timescale yet
reached — it is a bounded, statistically stationary process
(rigid 1¹⁷ frame, fluctuating second block, odd-gap pairs
region, a one-way-ratcheting long gap, terminal 1²) that has
persisted ≥ 1.017×10¹² steps. The plausible attack surfaces
are now: (i) a much longer run (the present one continues
toward 3×10¹² isolated steps; resume after any kill with
`./phase10 run 3000000000000`, state in `phase10.ckpt`);
(ii) an analytic attack on the transient itself — the pairs
region's odd-gap dynamics against the second block, and the
long gap's rare downward ratchets, are the obvious objects;
(iii) the Lean/Rocq mechanisation backlog from Phases 5–9,
unchanged.

*Files: `phase10.c` (resumable simulator with built-in
verification), `phase10-expected.txt` (303 reference dumps),
`phase10-run.log` (the long run; `bench.log` holds the fresh-start
segment that verified the first 3 dumps), `phase10.ckpt` (latest
checkpoint; resume with `./phase10 run BUDGET`), `phase10_analyze.py`
(dump statistics). Nothing posted externally.*
