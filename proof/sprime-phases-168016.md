# BB(6) holdout #168016 — S′ family: prediction tests + phase decomposition (Phase 5, 2026-11-25)

- Seed index: **168016**
- Spec: `1RB1RA_1RC1LB_0LD0RA_1RF1LE_---1LF_1LC0LF`
- Starting point: Phase 4 (`postbreak-168016.md`) — the post-break
  regime is a second bounce family S′(m) (wall
  L′ = 1^4 0 1^41 0 1^65 0, 113 cells), verified in the real
  trajectory for even m = 2…68, with one advance prediction
  outstanding: S′(70) at step 470,299,116,901. This phase tests
  that prediction, tests the next one (S′(72)) as well, and
  performs the Phase-3-style phase decomposition of the S′
  period, including the phase-2 head-range law and its
  breaking-point implication.

## Headline results

1. **S′(70) prediction CONFIRMED exactly.** An isolated S′(68)
   start reaches S′(70) in exactly P(68) = 206,158,430,202 steps,
   with the exact predicted configuration (tape L′ · 1^70 · 0,
   state B, head on the final 0). Composed with Phase 4's
   exactly-verified real-trajectory arrival of S′(68) at
   264,140,686,699 (the isolated start is that very configuration
   up to translation, and the machine is translation-invariant),
   S′(70) arrives at real-trajectory step
   **470,299,116,901** — the outstanding Phase 4 prediction, hit
   to the step. This is the sixth consecutive out-of-sample
   advance prediction confirmed for S′ (after m = 60…68).
2. **S′(72) prediction CONFIRMED exactly.** A further advance
   prediction (made before the run, from the same closed form)
   also hit: an isolated S′(70) start reaches S′(72) in exactly
   P(70) = 412,316,860,410 steps, i.e. real-trajectory step
   **882,615,977,311**, exact configuration. (Provenance, for
   honesty: a first combined run was runtime-killed at step
   592,705,486,848, mid-phase-2 of the m = 70 period — the same
   failure mode as Phase 4's run1 — after confirming everything
   through S′(70). The S′(72) confirmation comes from a fresh
   isolated S′(70) start that ran to completion.)
3. **Phase decomposition of S′ is exact at 13 parameter values**
   (m = 16…56 by isolated phase runs; m = 68, 70 by the test
   runs): every period splits as ph1 = 3, ph2 = 3·2^((m+4)/2) −
   2m − 14, ph3 = 2m + 5, summing to P(m) = 3·2^((m+4)/2) − 6.
   Phases 1 and 3 are proven for all m by explicit shift rules
   (Section B); phase 2 remains empirical.
4. **Phase-2 head range for S′ is [112 − m/2, 112 + m]**,
   measured exactly at all 13 values — the same law as the old
   family ([50 − k/2, 51 + k] relative to its 51-cell wall),
   i.e. the head's leftward excursion from the wall's right
   edge has depth exactly m/2. The wall's rightmost block is
   1^65 (positions 47…111, separator 0 at 46), so the excursion
   stays inside the block iff m ≤ 130 and would first touch
   the separator cell at **m = 132** — exactly the geometric
   configuration at which the old family broke (k = 56, block
   1^27, separator at 22). **Extrapolated prediction: S′
   breaks at m = 132.** But S′(132) would only arrive at step
   ≈ 8.85×10^20 — roughly 187,000 years at this simulator's
   speed — so the predicted break is **categorically outside
   simulation range** (the ≲ 3×10^12 envelope reaches only
   m ≈ 74–76). It can be settled only by a phase-2 proof with
   an explicit side condition, never by running. See Section C
   for exactly what is verified vs extrapolated.

## A. The prediction tests (isolated starts)

Tooling: `sprime.c` (new this phase), a phase-boundary detector
mirroring the validated `phase168016.c`, with exact configuration
checks (full tape comparison, cleanliness outside the pattern
span) at every boundary. It was validated before the long runs:
`phase 16` and `phase 40` reproduce Phase 4's data exactly
(S′(18) at 3,066 from S′(16); S′(42) at 12,582,906 from S′(40),
matching the Phase 4 isolated chain), and `phase 56` reproduces
S′(58) at 3,221,225,466.

Boundary-by-boundary results of the two test runs
(`test-sprime.log` / `test-sprime-run1.log`, `test-sprime70.log`):

| boundary | predicted (isolated steps) | observed | verdict |
|---|---|---|---|
| X′(68) | 3 | 3 | exact |
| Y′(68) | 206,158,430,061 | 206,158,430,061 | exact |
| **S′(70)** | **206,158,430,202** | **206,158,430,202** | **exact** |
| X′(70) | +3 into the next period | +3 | exact |
| Y′(70) | 412,316,860,265 (from S′(70)) | 412,316,860,265 | exact |
| **S′(72)** | **412,316,860,410** (from S′(70)) | **412,316,860,410** | **exact** |

No halt, no left breach (head < 0) anywhere in either run; the
minimum head over the completed S′(70) period was 77 (relative
frame). The S′ family is now verified for **36 consecutive
bounces (m = 2…72)**: m ≤ 68 in the composed real trajectory
(Phase 4), m = 70 and m = 72 by isolated starts whose initial
configurations are exactly the trajectory's (translation
invariance makes the step counts compose exactly, as
demonstrated end-to-end by Phase 4 §D's breach-configuration
reproduction).

## B. Phase decomposition of the S′ period

Definitions (translation-invariant; positions relative to the
pattern's left edge):

- **S′(m)**: tape `L′ · 1^m · 0`, head on the final 0 (relative
  position 113 + m), state B.
- **X′(m)**: tape `L′ · 1^(m+1)`, head at 112 + m, state E.
- **Y′(m)**: tape `L′[:111] · "01" · 1^(m+1)` over [0, 113 + m]
  — L′ with its last two cells (positions 111, 112: `10`)
  flipped to `01`, so the 1-run beginning at position 112 has
  length m + 2 — head at 112 + m, state B.

For every measured m the period decomposes as

    S′(m) --phase 1--> X′(m) --phase 2--> Y′(m) --phase 3--> S′(m+2)
    costs:    3          ph2(m)            2m + 5

with ph2(m) = 3·2^((m+4)/2) − 2m − 14 (so the costs sum to
P(m) = 3·2^((m+4)/2) − 6). Measurements (`sprime.c phase`,
`test`; every entry an exact configuration match, not a fit):

| m | ph1 | ph2 (measured) | ph3 (measured) | total = P(m) | phase-2 head range |
|---|---|---|---|---|---|
| 16 | 3 | 3,026 | 37 | 3,066 | [104, 128] |
| 20 | 3 | 12,234 | 45 | 12,282 | [102, 132] |
| 24 | 3 | 49,090 | 53 | 49,146 | [100, 136] |
| 28 | 3 | 196,538 | 61 | 196,602 | [98, 140] |
| 32 | 3 | 786,354 | 69 | 786,426 | [96, 144] |
| 36 | 3 | 3,145,642 | 77 | 3,145,722 | [94, 148] |
| 40 | 3 | 12,582,818 | 85 | 12,582,906 | [92, 152] |
| 44 | 3 | 50,331,546 | 93 | 50,331,642 | [90, 156] |
| 48 | 3 | 201,326,482 | 101 | 201,326,586 | [88, 160] |
| 52 | 3 | 805,306,250 | 109 | 805,306,362 | [86, 164] |
| 56 | 3 | 3,221,225,346 | 117 | 3,221,225,466 | [84, 168] |
| 68 | 3 | 206,158,430,058 | 141 | 206,158,430,202 | [78, 180] |
| 70 | 3 | 412,316,860,262 | 145 | 412,316,860,410 | [77, 182] |

Every measured ph2 equals 3·2^((m+4)/2) − 2m − 14 exactly;
every range equals [112 − m/2, 112 + m] exactly. (One
difference from the old family: its phase-2 range's right end
was 51 + k, one cell beyond the X(k) head position k + 50;
for S′ the right end is 112 + m, exactly the X′(m) head
position. The left end — the structurally decisive one —
follows the identical law in both families.)

### Phase 1: S′(m) → X′(m) in 3 steps — proven for all m

From S′(m) (head on the final 0, state B):
1. B on 0 → `1RC`: writes 1 (block now has m+1 ones), head moves
   right onto a fresh 0, state C.
2. C on 0 → `0LD`: writes 0, head moves left onto the 1 just
   written, state D.
3. D on 1 → `1LE`: writes 1, head moves left, state E.
Result: tape `L′ · 1^(m+1)`, head one cell left of the rightmost
1, state E — exactly X′(m). Purely local; no side conditions. ∎
(Word-for-word the old family's phase 1, which is also how each
S′(m) record in the real trajectory is followed 1 step later by
the state-C record noted in Phase 4.)

### Phase 3: Y′(m) → S′(m+2) in 2m + 5 steps — proven for all m

From Y′(m) (position 111 is 0; positions 112…113+m are 1; blank
beyond; head at 112 + m, state B):
1. **B-sweep** (m+1 steps): B on 1 → `1LB` repeated. The head
   walks left across the 1-run from position 112 + m down to
   position 111. (Uniform rule on 1; the run's left end is
   marked by the 0 at position 111.)
2. **Repair** (1 step): B on 0 → `1RC` at position 111: restores
   L′'s cell 111 to 1, head to 112, state C.
3. **Repair** (1 step): C on 1 → `0RA` at position 112: restores
   L′'s cell 112 to 0, head to 113, state A.
4. **A-sweep** (m+1 steps): A on 1 → `1RA` repeated. The head
   walks right across positions 113…113+m.
5. **Extension** (1 step): A on 0 → `1RB` at position 114 + m
   (blank in Y′(m)): writes the (m+2)-th block 1, head to
   115 + m, state B.
Result: tape `L′ · 1^(m+2) · 0`, head on the final 0, state B —
exactly S′(m+2). Each sweep is a finite run of a single uniform
transition over a 1-run terminated by a 0 (resp. by the blank
cell the sweep itself must reach), so the argument is a routine
induction on the run length; the head never leaves
[111, 115 + m], so the rest of the tape is untouched. Total
(m+1) + 1 + 1 + (m+1) + 1 = 2m + 5. ∎
(This is the old family's phase-3 argument re-instantiated in
S′ geometry; the measured cost 2m + 5 at all 13 values above
agrees.)

### Phase 2: X′(m) → Y′(m) — empirical only; NOT proven

Measured cost ph2(m) = 3·2^((m+4)/2) − 2m − 14 at 13 values of
m (table above); equivalently ph2(m+2) = 2·ph2(m) + 2m + 10 —
the same doubling recurrence as the old family's phase 2,
indicating the same self-similar internal engine, driven only
by the repeater length. The net effect is exactly the flip of
the wall's last two cells `10 → 01`, tape otherwise unchanged,
head returned to position 112 + m in state B instead of E. No
explicit shift-rule decomposition of phase 2 has been
extracted; as with the old family, it is the entire difficulty
of a proof. What this phase adds is the exact head-range law,
which is what makes a breaking-point prediction possible.

## C. The phase-2 head range and the predicted breaking point

**Measured law (exact at m = 16…56, 68, 70):** during phase 2
the head stays within relative positions

    [112 − m/2,  112 + m].

The right end never binds (it is the head's own starting
region). The left end is the wall-penetration depth: measured
from the wall's right edge (position 112), the head reaches
exactly **m/2 cells into the wall**.

**Wall geometry.** L′ = 1^4 0 1^41 0 1^65 0: the rightmost
1-block spans positions 47…111 (65 cells), with the separator
0 at position 46 to its left (then 1^41 over 5…45, separator
at 4, 1^4 over 0…3). The phase-2 left end 112 − m/2 lies
inside the rightmost block iff 112 − m/2 ≥ 47, i.e. **m ≤
130** (at m = 130 the left end is 47, the block's leftmost
cell). At **m = 132** the extrapolated left end is 46 — the
separator cell itself.

**Old-family precedent (Phase 3).** There the wall's rightmost
block was 1^27 over positions 23…49 with separator 0 at 22,
the measured range was [50 − k/2, 51 + k], the law held for
every k ≤ 54 (left end ≥ 23, inside the block), and the family
broke at k = 56 — exactly the first k whose extrapolated left
end (50 − 28 = 22) reaches the separator. In the actual k = 56
run the head, once the phase-2 excursion reached the
separator, cascaded to relative position −4 and the machine
left the family permanently.

**Prediction for S′ (extrapolation — label it as such).** If
the range law persists to m = 130 and the break mechanism is
the same (the phase-2 engine's leftward sweep first reading
the separator 0 at the left edge of the wall's rightmost
block), then **S′ breaks at m = 132**: the period
S′(132) → S′(134) would fail, presumably with a left breach
late in phase 2, analogously to the old family.

**Feasibility — the prediction is untestable by simulation.**
Exact step counts (closed-form sums, arbitrary-precision
checked):

| event | real-trajectory step |
|---|---|
| S′(72) (now confirmed) | 882,615,977,311 |
| S′(74) | 1,707,249,698,137 |
| S′(76) | 3,356,517,139,795 |
| S′(132) | 885,443,715,596,040,733,867 |

The breaking period itself, P(132) = 3·2^68 − 6 =
885,443,715,538,058,477,562 steps, is as large again. At the
measured speed of these runs (≈1.1×10^8 steps/s), merely
*reaching* S′(132) would take ≈ 5.9×10^12 s ≈ **187,000
years**; even a 100× faster simulator would need ≈ 2,800
years. The feasible envelope (≲ 3×10^12 steps) reaches only
S′(74)–S′(76). So, unlike the m = 70/72 predictions, the
m = 132 break prediction **cannot be confirmed or refuted by
any simulation available to this project**. Its only possible
route to certainty is a proof of phase 2 with an explicit
side condition (e.g. "phase 2 succeeds iff the head's
excursion stays within the rightmost wall block", i.e. iff
m ≤ 130), which would convert the break at m = 132 into a
theorem about the period engine — and would then require a
fresh analysis of whatever regime follows, exactly as
Phases 3–4 did for the old family's break.

**Rigor notes.**
- *Verified exactly:* all boundary configurations and step
  counts in Sections A–B (full-tape comparisons in an
  independent C simulator, cross-validated against Phase 4's
  independent tooling at m = 16/40/56 before the long runs);
  the range law and phase costs at the 13 listed m values;
  phases 1 and 3 for all m (shift-rule arguments above).
- *Extrapolated, not verified:* the range law for m > 70; the
  claim that touching the separator is the break mechanism
  (inferred from the single observed old-family break — the
  geometric coincidence is exact, but one observation is not
  a causal proof); the m = 132 break itself.
- Phase 3's lesson cuts both ways and is worth restating: the
  old family's period law was verified for 27 consecutive
  periods and still failed at the 28th — but it failed
  *exactly where its own head-range law said the wall would
  run out*. S′ has now survived 36 consecutive bounces, and
  its range law points to m = 132 with a wide margin
  (excursion depth 35 of 65 at m = 70). Nothing in the
  verified range is close to a boundary; equally, nothing
  verified excludes surprises in phase 2's unexamined
  interior at larger m.

## D. Assessment and what remains

- S′ status: **36 consecutive bounces verified (m = 2…72)**,
  seven of them (m = 60…72) genuine advance predictions
  confirmed to the step. The period's phases 1 and 3 are
  proven for all m; phase 2 has an exact cost law and an
  exact head-range law on the verified range, but no proof.
- #168016 is **still not decided**. The two-storey picture is
  now sharper: family S (k = 2…56, breaks at the separator of
  its 27-cell rightmost block), transient, family S′
  (m = 2…72 verified; predicted to break at m = 132 at its
  65-cell block's separator — a prediction no feasible
  simulation can test).
- Sensible next steps, in order of leverage:
  1. **Attack phase 2's internal structure** (the real prize,
     for both families): the doubling recurrence
     ph2(m+2) = 2·ph2(m) + 2m + 10 suggests a self-similar
     decomposition; finding the intermediate configuration
     that splits phase 2 into two half-size copies would be
     the key to a formula-tape proof — and to proving the
     m ≤ 130 side condition that would make the m = 132
     break a theorem.
  2. Cheap confirmations while that is open: S′(74)
     (isolated, P(72) ≈ 8.2×10^11 steps ≈ 2 hours) — extends
     the verified range but changes nothing structural.
  3. Nothing here is ready to post externally; the community
     caveat from Phase 3 §D still applies.

## Artefacts (this phase)

- `sprime.c` — S′ phase-boundary detector (`phase M`) and
  instrumented prediction tester (`test`, `test1 M ABS
  BUDGET`); validated against Phase 4 at m = 16/40/56 before
  the long runs.
- `phase-sweep.log` — isolated phase decomposition for
  m = 16, 20, 24, 28, 32, 36, 40, 44, 48, 52, 56 (all exact).
- `test-sprime.log`, `test-sprime-run1.log` — combined
  S′(68)-start test run: confirmed X′(68), Y′(68), **S′(70)**,
  X′(70); runtime-killed at step 592,705,486,848 during
  phase 2 of the m = 70 period.
- `test-sprime70.log` — isolated S′(70)-start run (completed):
  confirmed Y′(70) and **S′(72)** exactly; phase-2 range for
  m = 70 measured as [77, 182].
