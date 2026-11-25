# BB(6) holdout #168016 — post-break regime (Phase 4, 2026-11-25)

- Seed index: **168016**
- Spec: `1RB1RA_1RC1LB_0LD0RA_1RF1LE_---1LF_1LC0LF`
- Starting point: Phase 3 (`proof-168016.md`) — the bounce family
  S(k) (wall L = 1^4 0 1^17 0 1^27 0) runs for even k = 2…56 and
  breaks at k = 56. This phase characterises what happens next.

## Headline result

The post-break regime is **a second bounce family**. After a
5.15×10^10-step transient following the k = 56 breach, the real
(blank-tape) trajectory settles into a new family

    S'(m):  tape = L' · 1^m · 0,  head on the final 0, state B,
    L' = 1^4 0 1^41 0 1^65 0   (113 cells, 110 ones),

for even m = 2, 4, 6, …, at absolute offset −16, with **exactly the
same period law as the old family**:

    S'(m) → S'(m+2)  in  3·2^((m+4)/2) − 6  steps.

Verified in the real trajectory for **34 consecutive bounces
(m = 2…68)** — every gap matches the closed form exactly —
including **five genuine advance predictions confirmed
out-of-sample (S'(60), S'(62), S'(64), S'(66), S'(68))**. Isolated synthetic
starts confirm the induction step independently (Section C), and
an isolated start from the breach configuration reproduces the
entire post-break evolution exactly (Section D). The new family
has already survived m = 56, the value that killed the old
family. Whether S' itself breaks at some larger m is the open
question; advance predictions for m = 66 and m = 68 are on record
(Section B).

## A. The breach and the transient (real trajectory)

Tooling: `postbreak.c` (new this phase), cross-validated against
Phase 3 at three independent points — S(56) synthetic first record
(step 3,221,226,692, tape 1^4 0 1^42 0 1^65 0, breach step
3,221,223,994, min head −4 — all exact), and the synthetic S(58) /
S(60) first records (steps 28,991,030,218 / 28,991,030,242 — both
exact). The real-trajectory run reproduces Phase 3's S(k) table
exactly (S(56) at step 3,221,422,603, offset −12).

Post-S(56) timeline (absolute steps, real trajectory):

| step | event |
|---|---|
| 3,221,422,603 | S(56) reached (last member of the old family) |
| 6,442,646,598 | head reaches −15 (state D); tape over [−14, 95] is mostly (110)-periodic texture with defects, 70 ones |
| 6,442,646,963/964 | head reaches −16 (states C/D); the (110) texture persists |
| 6,442,649,295 | first post-break state-B right-edge record: tape `1^4 0 1^42 0 1^65 0`, head on final 0 (the Phase 3 breach record) |
| 6,442,649,296 … 57,982,256,712 | **transient: no edge records at all** — for 51,539,607,417 steps the head never leaves the visited span [−16, 97], while the tape internally reorganises: block vector (4, 42, 65) → wall (4, 41, 65) plus a new rightmost block seeded at 1^2 |
| 57,982,256,713 | S'(2) reached — the new family begins |

## B. The S' family in the real trajectory

Arrivals (state-B right-edge records with tape L' · 1^m · 0,
offset −16, ones = 110 + m — all confirmed):

| m | arrival step | gap from S'(m−2) | 3·2^((m+2)/2) − 6 |
|---|---|---|---|
| 2 | 57,982,256,713 | — | — |
| 4 | 57,982,256,731 | 18 | 18 |
| 6 | 57,982,256,773 | 42 | 42 |
| 8 | 57,982,256,863 | 90 | 90 |
| 10 | 57,982,257,049 | 186 | 186 |
| 12 | 57,982,257,427 | 378 | 378 |
| 14 | 57,982,258,189 | 762 | 762 |
| 16 | 57,982,259,719 | 1,530 | 1,530 |
| 18 | 57,982,262,785 | 3,066 | 3,066 |
| 20 | 57,982,268,923 | 6,138 | 6,138 |
| 22 | 57,982,281,205 | 12,282 | 12,282 |
| 24 | 57,982,305,775 | 24,570 | 24,570 |
| 26 | 57,982,354,921 | 49,146 | 49,146 |
| 28 | 57,982,453,219 | 98,298 | 98,298 |
| 30 | 57,982,649,821 | 196,602 | 196,602 |
| 32 | 57,983,043,031 | 393,210 | 393,210 |
| 34 | 57,983,829,457 | 786,426 | 786,426 |
| 36 | 57,985,402,315 | 1,572,858 | 1,572,858 |
| 38 | 57,988,548,037 | 3,145,722 | 3,145,722 |
| 40 | 57,994,839,487 | 6,291,450 | 6,291,450 |
| 42 | 58,007,422,393 | 12,582,906 | 12,582,906 |
| 44 | 58,032,588,211 | 25,165,818 | 25,165,818 |
| 46 | 58,082,919,853 | 50,331,642 | 50,331,642 |
| 48 | 58,183,583,143 | 100,663,290 | 100,663,290 |
| 50 | 58,384,909,729 | 201,326,586 | 201,326,586 |
| 52 | 58,787,562,907 | 402,653,178 | 402,653,178 |
| 54 | 59,592,869,269 | 805,306,362 | 805,306,362 |
| 56 | 61,203,481,999 | 1,610,612,730 | 1,610,612,730 |
| 58 | 64,424,707,465 | 3,221,225,466 | 3,221,225,466 |
| 60 | 70,867,158,403 | 6,442,450,938 | 6,442,450,938 |
| 62 | 83,752,060,285 | 12,884,901,882 | 12,884,901,882 |
| 64 | 109,521,864,055 | 25,769,803,770 | 25,769,803,770 |
| 66 | 161,061,471,601 | 51,539,607,546 | 51,539,607,546 |
| 68 | 264,140,686,699 | 103,079,215,098 | 103,079,215,098 |

**Advance predictions, confirmed:** the closed form fitted on
m ≤ 58 predicted S'(60) at step 70,867,158,403, S'(62) at
83,752,060,285, S'(64) at 109,521,864,055, S'(66) at
161,061,471,601 and S'(68) at 264,140,686,699 before those parts
of the runs were inspected; the runs produced exactly those
steps, tapes (4, 41, 65, m) and ones counts
(170 / 172 / 174 / 176 / 178). Five consecutive out-of-sample
hits.

**Advance prediction outstanding** (same formula):

| m | predicted arrival step |
|---|---|
| 70 | 470,299,116,901 |

The first real-trajectory run (budget 4×10^11) was terminated by
the runtime (SIGTERM) at ≈1.5×10^11 steps (CPU-time calibration),
mid-period between S'(64) and S'(66); its records through
S'(64) were flushed to `run1.log` before the kill. A replacement
run (`run2.log`, budget 2.7×10^11) independently reproduced the
whole sequence, confirmed S'(66) and S'(68), and exhausted its
budget mid-period between S'(68) and S'(70).

Each S'(m) record is followed 1 step later by the phase-1 analogue
(state C, block grown to m+1) — the same local 3-step opening as
the old family's phase 1 (B on 0 → 1RC …), consistent with the two
families sharing the same period engine, driven only by the
repeater length m and not by the wall (as long as the wall
"reflects" correctly).

## C. Isolated-start verification of S'

Synthetic starts from freshly constructed S'(m) configurations
(`postbreak.c streamBlocks 4 41 65 m`), independent of the composed
trajectory:

- One isolated chain (`streamBlocks 4 41 65 40`, budget 10^10)
  verified **nine consecutive induction steps** S'(m) → S'(m+2)
  for m = 40, 42, …, 56, with arrival steps exactly the closed-form
  cumulative sums: S'(42) at 12,582,906; S'(44) at 37,748,724;
  S'(46) at 88,080,366; S'(48) at 188,743,656; S'(50) at
  390,070,242; S'(52) at 792,723,420; S'(54) at 1,598,029,782;
  S'(56) at 3,208,642,512; S'(58) at 6,429,867,978 (the run then
  exhausted its budget mid-period toward S'(60)).
- **S'(56) → S'(58) in exactly 3,221,225,466 steps** (separate
  isolated start, `streamBlocks 4 41 65 56`): the parameter value
  at which the OLD family broke passes cleanly in the new family,
  in isolation as well as in the composed trajectory.

## D. The breach configuration family (task 3)

The breach record configuration T(a,b,c) = tape `1^a 0 1^b 0 1^c 0`,
head on the final 0, state B:

- **T(4,42,65)** (the actual breach output): an isolated start
  (`streamBlocks 4 42 65`) **reproduces the real continuation
  exactly**: no edge records for 51,539,607,417 steps, then
  S'(2) at relative step 51,539,607,418 and the full S' sequence
  through S'(60) at relative step 64,424,509,108 — every arrival
  exactly the real-trajectory step minus 6,442,649,295 (30
  consecutive arrivals). The breach configuration is therefore
  confirmed as the exact seed of the post-break regime. (An
  earlier firstB probe of the same start with a 2×10^9 budget
  showed the head still deep inside the span — min head 20, no
  left breach — consistent with the long internal transient.)
- **T(4,42,67)** (c varied by +2): after the step-1 phase-1
  write (block 67→68, state C), **no edge record at all in
  ≈6×10^10 steps** (the job was runtime-killed; step count is a
  CPU-time estimate at the calibrated ≈1.5×10^8 steps/s). So the
  c+2 neighbour does **not** funnel into an S'-type family on
  the exact config's timescale — its transient, if it resolves
  at all, is longer than ≈6×10^10 steps. Unresolved.
- **Synthetic-line records are a different wall.** The first
  records of the synthetic S(58) / S(60) starts (Phase 3) have
  tapes (4, 40, 64, 4) and (4, 40, 64, 6) — wall (4, 40, 64), not
  the real line's (4, 41, 65). Isolated continuations
  (`firstB blocks 4 40 64 4` and `… 6`, budget 3×10^11 each)
  fired **no state-B record within ≈8.5×10^10 and ≈8.0×10^10
  steps** respectively (CPU-time estimates; both jobs were
  runtime-killed before their budgets). Those configurations do
  not bounce onward promptly: their continuations sit in long
  internal phases (or leave the record family). Unresolved
  beyond ≈8×10^10 steps.

## E. Assessment

- The post-break regime is **characterised**: a 5.15×10^10-step
  transient, then a clean bouncer family S' with a period law
  identical to the old family's, verified for 34 consecutive
  bounces in the composed trajectory (five of them predicted
  in advance), 9 consecutive isolated induction steps, and a
  full isolated reproduction from the breach configuration.
  This is strong evidence the machine's long-term behaviour is
  "bounce families all the way down" — but Phase 3's lesson
  applies verbatim: the old family survived 27 bounces before
  breaking at the 28th, and S' has survived 34. **S' is not a
  proof.**
- The natural next steps: (i) test the outstanding m = 70
  prediction (arrival at 470,299,116,901; needs a run with
  budget ≳ 5×10^11) — a break of S', if it comes,
  will likely be at a specific m where the period engine's head
  excursion reaches the new wall's left edge, and locating it
  would pin down the mechanism; (ii) extract the phase
  decomposition of the S' period (phase 1 is already visible;
  the phase-2 analogue and its head-range as a function of m
  are the crux — for the old family the phase-2 head range was
  [50 − k/2, 51 + k], and the analogous formula for S' would
  predict its breaking point, if any); (iii) each further
  bounce doubles the cost, so m ≈ 74 (≈3×10^12 steps) is the
  practical ceiling for this simulator.
- Nothing here decides #168016 yet. But the machine is now
  understood as (at least) a two-storey bouncer: family S
  (k = 2…56), a transient, then family S' (m = 2…68). If S'
  also breaks, expect another transient and possibly a third
  family; the wall grew from 51 to 113 cells in the first
  transition, so the process may be a slow "wall-building"
  dynamics rather than a single invariant.

## Artefacts (this phase)

- `postbreak.c` — real-trajectory record streamer (`run`),
  synthetic record streamer (`streamS` / `streamBlocks`), and
  probe-compatible first-record tool (`firstB`); validated
  against Phase 3 at S(56)/S(58)/S(60) exactly.
- `run1.log` — real trajectory, budget 4×10^11, runtime-killed
  at ≈1.5×10^11 steps after logging S' through m = 64.
- `run2.log` — replacement real-trajectory run, budget
  2.7×10^11 (completed): independently reproduced the whole
  post-break sequence and confirmed the S'(66) and S'(68)
  predictions; budget exhausted mid-period toward S'(70).
- `stream-Sprime40.log`, `stream-Sprime56.log` — isolated S'
  induction-step streams (completed).
- `stream-breach44265.log` — isolated breach-configuration
  stream: full reproduction of the post-break evolution,
  S'(2)…S'(60) (killed during the S'(60)→S'(62) period).
- `stream-breach44267.log` — T(4,42,67) variation: one step-1
  record, then silence for ≈6×10^10 steps (killed).
- `firstB-b404064-4.log`, `firstB-b404064-6.log` — isolated
  continuations of the synthetic-line record configurations:
  no record fired within ≈8×10^10 steps each (killed; logs
  empty because firstB prints only on firing).
- `analyze_postbreak.py` — record-stream analyser (family fit /
  translated-cycler check over complete record configurations).
