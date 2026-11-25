# Phase 9 — the m = 132 period of #168016, evaluated analytically

Machine: `1RB1RA_1RC1LB_0LD0RA_1RF1LE_---1LF_1LC0LF` (bbchallenge
holdout seed index 168016). The machine halts iff it is ever in state E
reading 0.

**Headline.** The m = 132 period of the second bounce family S′(m) was
evaluated with the proven machinery of Phases 5–8 instead of by
simulation. The phase-2 cascade runs to completion — all 65 intervals
U_1…U_65 lie inside the proven Interval Lemma — and reaches the closed
form **D(132, 66)** at period offset 3·2⁶⁸ − 9183 (real-trajectory step
**1,770,887,431,134,099,202,252**). The break predicted in Phase 5 is
real, and it is located with complete precision: it is the **very first
step of the return**. D(132, 66)'s head sits at position 46 — exactly
the separator 0 between Π's 1⁴¹ block and the reduced solid — in state
C, so the machine executes `0LD` where the return's warm-up W₆₆ would
need `0RA` (C on 1). The fictitious Y′(132) and S′(134) are never
reached. Forward exact simulation from D(132, 66) (halt transition
watched at every step) shows no halt: the head breaches the left edge,
reorganises the wall, produces one clean three-block record tape
**1¹⁷ 0 1⁹⁷ 0 1¹³⁷ 0** at deviation-step 403,455, and then settles into
a long bounded transient — the same qualitative shape as the
5.15×10¹⁰-step transient that preceded S′ in Phase 4. The machine is
**not decided** by this phase; the proven non-halting bound is extended
(see §5).

Everything below rests on the Phase 1–8 human proofs (shift rules, not
mechanised). The analytic evaluation itself is a finite exact
computation whose rule applications were spot-checked by direct
simulation (§2, §3.4).

---

## 1. Method

Direct simulation to S′(132) is impossible (arrival at step
885,443,715,596,040,733,867 ≈ 8.85×10²⁰). But the Phase 6–8 machinery
evaluates a period by formula:

* phase 1: 3 steps, proven for all m (Phase 5);
* phase 2 split (Phase 6, proven): X′(m) ─(m+1)→ D(m, 1)
  ─[intervals U_d, cost C_d = 3·2^(d+2) − 4d − 11]→ D(m, m/2)
  ─(return, cost R(m))→ Y′(m), with the cost identity
  ph2(m) = (m+1) + Σ_{d=1}^{m/2−1} C_d + R(m);
* Interval Lemma (Phases 7–8): D(m, d) → D(m, d+1) in C_d steps for all
  d ≤ 65 and all m ≥ 2d + 2, via the chain decomposition
  U_d = W_d · U_1(−1) ··· U_{d−1}(−1) and the Window Principle;
* Return Lemma (Phase 8): D(m, m/2) → Y′(m) in R(m) steps for even
  m ≤ 130 — the return is the length-R(m) prefix of the warm-up
  W_{m/2}, whose first step is the warm-up's round structure starting
  with **C on 1 → `0RA` at the head cell of D(m, m/2)**, which lies on
  the solid block 1^(m+2−2d) at position 112 − m/2.

At m = 132 the cascade needs d = 1…65 — every d inside the Interval
Lemma's proven range, with the side condition m ≥ 2d + 2 met with
equality at d = 65 (132 = 2·65 + 2). The return, however, would be
W₆₆, and the Return Lemma's hypothesis is m ≤ 130, equivalently
d = m/2 ≤ 65: D(m, m/2)'s head at 112 − m/2 lies on the solid iff
m/2 ≤ 65. At m = 132 the head lands at 112 − 66 = 46, one cell left of
the solid's left edge (the solid has shrunk to 1¹ at position 47), on
the separator cell 46 itself, whose value is 0. So the analytic
evaluation is forced through the cascade and stops exactly at the
return's first step.

## 2. Validation of the method: the OLD family's k = 56 break, reproduced

Before trusting the m = 132 evaluation, the same analytic method was
applied to the old family S(k), whose break at k = 56 is known exactly
from Phase 3 (direct simulation of the real trajectory). The old family
admits the *same* cascade decomposition, with Π_o = 1⁴ 0 1¹⁷ 0
(positions 0…22):

D_o(k, d) = Π_o · 1^(29−d) · (0 1²)^(d−1) · 0^(k+1−2d) · 1²,
head at 50 − d, state C, anchor 1² at {50+k, 51+k},

with the same universal interval costs C_d and the same return cost
R(k). (`phase9.py` Part 1: the decomposition, every interval from
synthetic starts, the return, and cumulative D_o arrivals in single
runs were verified for **all even k = 4…32 — ALL PASS**. An initial
off-by-one in the anchor position was caught by these checks and fixed
before any k = 56 numbers were produced.)

Analytic prediction for k = 56: D_o(56, 28) is reached at period step
3 + 57 + Σ_{d=1}^{27} C_d = **3,221,223,699**, and its head sits at
50 − 28 = 22 = the separator of Π_o — the same failure mode as
m = 132. Step-by-step simulation from the synthetic D_o(56, 28)
(`phase9.py` Part 2) and an independent full C run from S(56) over
3.22×10⁹ steps (`phase9.c` mode `oldfull`) reproduce Phase 3's known
results **exactly**:

| quantity | analytic/synthetic | Phase 3 (real trajectory) |
|---|---|---|
| all 28 D_o(56, d) arrivals | exact at predicted steps | — (new check) |
| first head position −1 (breach) | period step 3,221,223,994 | 3,221,223,994 ✓ |
| config at period step P(56) = 3,221,225,466 | state A, head rel. 71, (0 1²)-periodic right region, 99 ones | identical ✓ |
| first state-B right-edge record | period step 3,221,226,692, head rel. 109 | 3,221,226,692 ✓ |
| record tape | 1⁴ 0 1⁴² 0 1⁶⁵ 0 (111 ones, span [−4, 109]) | identical ✓ |
| minimum head position | −4 | −4 ✓ |

The method is therefore trustworthy: applied to a case with a known
answer, it reproduces the break exactly, including the deviation point,
the breach step, and the post-break record tape.

*Minor erratum found in passing:* Phase 3's line "Y(56) at period step
3,221,225,343" is inconsistent with its own numbers; the fictitious
Y(56) would sit at 3,221,223,699 + R(56) = **3,221,225,349**. Not
load-bearing anywhere.

## 3. The m = 132 evaluation

### 3.1 The cascade runs to completion

From S′(132) (arrival at real step 885,443,715,596,040,733,867 —
Phase 5 advance prediction, itself a corollary of the Phase 8
theorem):

* phase 1 (3 steps, proven all m) → X′(132);
* initial segment (m + 1 = 133 steps, proven pattern; verified at
  m = 132 from a synthetic X′(132), `phase9.py` Part 3d) → D(132, 1);
* intervals U_1, …, U_65 with costs C_d, Σ_{d=1}^{65} C_d
  = 3·2⁶⁸ − 9319 = 885,443,715,538,058,468,249 → **D(132, 66)**.

D(132, 66) in closed form (Π = 1⁴ 0 1⁴¹ 0, positions 0…46):

D(132, 66) = Π · 1¹ · (0 1²)⁶⁵ · 0¹ · 1²,

head at **46**, state **C**, 178 ones, nonblank span [0, 245]: the
solid is reduced to a single 1 at position 47; 65 pairs (0 1²) occupy
48…242; a single gap 0 at 243; the anchor 1² at 244…245. Cell 46 — the
head cell — is the separator **0** between the 1⁴¹ block and the solid.
(Closed form verified directly, `phase9.py` Part 3e.)

**Period offset of D(132, 66):** 3 + 133 + (3·2⁶⁸ − 9319)
= 3·2⁶⁸ − 9183 = 885,443,715,538,058,468,385.
**Real-trajectory step:** 885,443,715,596,040,733,867
+ 885,443,715,538,058,468,385 = **1,770,887,431,134,099,202,252**.

For reference, the fictitious landmarks of the unbroken period:
Y′(132) would have been at period offset 3·2⁶⁸ − 275
(= D-offset + R(132) = 8908 steps later), and S′(134) at real step
1,770,887,431,134,099,211,429. Neither is reached.

### 3.2 A boundary subtlety at j = 64, resolved

One point in the chain decomposition needs care at d = 65. Phase 7
§4.3 states block j's comparison window as [110 − j, 112 + 2j]; at
j = 64 (inside U₆₅) that window includes cell 46, where the junction
configuration F₆₄(65) (value 0, the Π separator) and the comparison
tape D(130, 64) translated by −1 (value 1) **differ**. The trajectory
is nevertheless forced, because block 64's *read* window is
[47, 240]: U₆₄'s minimum head position (111 − 64 = 47 in its own
frame) is attained only at its final step, and on [47, 240] the two
tapes agree exactly. Moreover the arrival identity at cell 46 itself
holds because both F₆₄(65) and the true endpoint D(132, 66) carry 0
there — the discrepancy is only against the translated comparison
tape, never against the actual trajectory. Blocks j ≤ 63 are
unaffected (their windows start at ≥ 47). The d = 65 chain was
additionally spot-checked computationally far beyond Phases 7–8
(§3.4).

### 3.3 The deviation: first step of the return

The return from D(132, 66) would have to be the warm-up W₆₆. Its
proof (Phases 7–8) requires the head of D(·, 66) to sit on the solid
block; here the head is at 46 on a **0**. Hence the very first return
step already deviates:

* expected (fictitious): C on 1 → `0RA` (erase, right, state A);
* actual: **C on 0 → `0LD`** (write 0, left, state D), head 46 → 45.

Hand-derived continuation (cross-checked against the simulator):
step 2, D on 1 → `1LE`, head 44, state E; step 3, E on 1 → `1LF`,
head 43, state F; then F erases the 1⁴¹ block leftward (`0LF`)
43 → 5, and at cell 4 (value 0) F executes `1LC`. From there the head
cascades through the left wall — the exact analogue of the old
family's k = 56 break, one cascade level deeper.

**Deviation point, stated exactly:** cascade level d = 66 (the return
level), interval = the return D(132, 66) → Y′(132), step 1 of R(132);
configuration D(132, 66) above; period offset 3·2⁶⁸ − 9183; real step
1,770,887,431,134,099,202,252.

### 3.4 Spot checks at m = 132 (`phase9.py` Part 3, `phase9.c`)

* (a) D(132, 65) vs D(134, 65) differ only at cells [244, 245, 246,
  247] (the two anchors), all strictly right of U₆₅'s maximum read
  position 243 — agreement on the whole read window [47, 243]. ✓
* (b) W₆₅ endpoint exact: D(132, 65) ─8777 steps→ F₁(65). ✓
* (c) Chain blocks at d = 65 in the ambient m = 132 trajectory,
  synthetic starts: j = 1…20 verified in Python, j = 21…28 in C
  (C_j up to 3,221,225,349 steps; the C builder's F₂₁(65) matched
  Python's closed form exactly). This extends computational
  verification of the chain from d ≤ 22 (Phase 8) to spot checks at
  d = 65. ✓
* (d) Initial segment at m = 132: X′(132) ─133→ D(132, 1). ✓
* (e) D(132, 66) closed form: head 46, state C, 178 ones, cell 46 = 0. ✓

## 4. Forward simulation from D(132, 66)

Tool: `phase9.c` mode `dev132` / `dev132q` — an exact step-by-step
simulator started from the synthetic D(132, 66), watching the halt
transition (E on 0) at **every** step, logging left/right edge
records, structured state-B records, and periodic full-tape dumps.
Because D(132, 66) is reached from the blank tape by the proven
machinery (§3), a halt anywhere in this forward run would decide
#168016 as halting; conversely every simulated step extends the
non-halting bound (§5).

### 4.1 What happens (deviation-step = steps since D(132, 66))

* **Steps 1–686 — leftward cascade and first breach.** After the
  deviation (§3.3) the head reorganises the left wall into
  (0 1²)-pairs separated by growing 0-gaps, staying within [−4, 46].
  First head position **−1 at step 319** (state C; real step
  1,770,887,431,134,099,202,571), −2 at 320, −3 at 685, **−4 at 686** —
  the head eats through the 1⁴ block and writes outside the pattern's
  left edge, exactly as in the k = 56 break (which also bottomed at
  −4 in its first breach).
* **Steps 686–196,842 — confined reorganisation.** The head works the
  left ≈50 cells only (max head stays 46); the pairs region to the
  right (48…245) is untouched. Ones count drifts 178 → ≈158.
* **Steps 196,843–196,845 — second leftward push.** Head reaches −5
  (state F), −6 (C), **−7** (D; real step
  1,770,887,431,134,099,399,097). The span's left edge settles at −7
  and never moves again in the simulated window.
* **Step 393,873 — rightward breakout.** The head first exceeds 46
  (state B at 47; real step 1,770,887,431,134,099,596,125) and sweeps
  right, converting the pairs region into solid blocks separated by
  single 0s.
* **Step 403,455 — a clean record tape.** State B, head at 247 on the
  final 0, nonblank span [−6, 246], tape exactly

  **1¹⁷ 0 1⁹⁷ 0 1¹³⁷ 0** (251 ones)

  (real step 1,770,887,431,134,099,605,707). This is the precise
  analogue of the old family's breach record 1⁴ 0 1⁴² 0 1⁶⁵ 0, which
  in Phase 4 turned out to be the entry configuration of the
  post-break regime. Whether the present record plays the same role
  is a **hypothesis by analogy** (labelled, not established): what
  follows it in simulation is not an immediate bounce family.
* **Steps 403,456 – 3×10⁹ — long bounded transient.** No halt, no
  further edge records, no S′/S-family or other few-run state-B
  records. The head remains confined to [−7, 248], working a
  pairs-and-gaps region immediately right of a slowly fluctuating
  second block (1⁹⁷ at the record; 1⁸¹–1⁸⁹ in dumps at 10⁶–3×10⁹),
  with a large 0-gap (≈82–106 cells) before a terminal 1² at the
  right edge. Ones count ≈123–140. Qualitatively this matches
  Phase 4's post-breach transient — which lasted 5.15×10¹⁰ steps
  before S′(2) appeared — except that here the transient follows the
  clean record rather than preceding it.

### 4.2 Long run (3×10¹¹ steps)

A second, longer run (`dev132q`, budget 3×10¹¹ steps, ≈36 min at
1.4×10⁸ steps/s) **completed with the budget exhausted: no halt, and
no further records of any kind.** It reproduced the §4.1 trajectory
exactly (same left records at steps 319/320/685/686/196843–196845,
same clean record at step 403,455 — a determinism cross-check of the
two builds), then continued the transient for the remaining
≈3×10¹¹ steps. Full-run tallies: 7 left-edge records (all in the
first 196,845 steps), exactly **1** structured state-B record (the
§4.1 tape), **0** S′/S-family records, **0** halts in 306 dumps.

Throughout steps 403,456 – 3×10¹¹ the picture does not change
qualitatively: the head stays in [−7, 248] (dump-sampled head
positions 10–112, always inside the working region), the span stays
[−6, 247], the second block fluctuates without trend between 1⁷³ and
1⁹² (1⁹⁷ at the record), the ones count stays within 123–158, and the
working region remains (0 1²)-pairs separated by odd 0-gaps
(1, 3, 5, 7, 9, …) followed by a long 0-gap (≈68–106) and the
terminal 1². Final configuration at deviation-step 3×10¹¹: state C,
head 92, tape 1¹⁷ 0 1⁸⁶ 0 · [pairs with odd gaps] · 0⁶⁸ 1²,
137 ones.

Two honest consequences. First, the simulated transient
(3×10¹¹ steps) is already ≈5.8× longer than Phase 4's
5.15×10¹⁰-step transient that preceded S′, so the "third family
emerges after a comparable transient" analogy is **not** confirmed on
its natural timescale — either this transient is much longer, or the
§4.1 record tape is not an entry configuration of the same kind, or
the post-break regime is a different kind of long-lived bounded
process. Second, the period does **not** complete in altered form:
no S′(134)-like or other wall·1ⁿ·0 configuration occurs anywhere in
the 3×10¹¹ steps.

## 5. Proven / simulated / still open

**Proven (human proof, Phases 1–8 + this phase's analytic
evaluation):**

* The m = 132 cascade: S′(132) → D(132, 66) at period offset
  3·2⁶⁸ − 9183, real step 1,770,887,431,134,099,202,252. Every rule
  applied is inside its proven side conditions (Interval Lemma for
  d ≤ 65 with m ≥ 2d + 2; phases 1 and the initial segment for all m).
* The deviation is the first step of the would-be return: at
  D(132, 66) the machine executes C on 0 → `0LD`, not the warm-up's
  `0RA`. Y′(132) and S′(134) do not occur. The Phase 5 break
  prediction is confirmed and pinpointed (cascade level 66, return
  interval, step 1).

**Exact simulation (not proof):**

* The old-family validation of §2 (all numbers exact).
* Forward simulation from D(132, 66): no halt in the first
  3×10¹¹ deviation-steps (halt transition watched at every step).
  Combined with the proven segment, this extends the non-halting
  statement to: **#168016 does not halt within its first
  1,770,887,431,434,099,202,252 steps (≈1.77×10²¹)** — double the
  Phase 8 bound — with the same caveat as before: the analytic
  segment rests on the unmechanised Phase 5–8 human proofs, and the
  simulated segment is exact computation, not proof.

**Still open:**

* #168016 is **not decided**. The post-deviation regime is, as of the
  simulated window (3×10¹¹ steps past the deviation), a long bounded
  transient following one clean record tape (1¹⁷ 0 1⁹⁷ 0 1¹³⁷ 0).
  A third bounce family S″ may yet emerge — but the Phase 4 analogy's
  timescale (5.15×10¹⁰ steps) has already been exceeded ≈5.8-fold
  without emergence (§4.2), so this is a possibility, not an
  expectation. Characterising the regime (or finding a halt) needs
  either a much longer simulation or a fresh analytic attack on the
  transient's structure (the working region's pairs-and-odd-gaps
  pattern, processed against a slowly fluctuating solid block, is
  the obvious object).
* The record tape of §4.1 is a candidate entry configuration for that
  attack: a synthetic start from 1¹⁷ 0 1⁹⁷ 0 1¹³⁷ 0 (head on final 0,
  state B) is finite and explicit, exactly as T(4, 42, 65) was in
  Phase 4.
* Lean/Rocq mechanisation of Phases 5–9 remains undone, as does the
  blank-tape → S′(2) segment (exact simulation only).

*Files: `phase9.py` (Parts 1–3, all PASS; log `phase9-part3.log`),
`phase9.c` (modes `oldfull`, `blocks65`, `dev132`, `dev132q`; logs
`dev132q-3e9.log`, `dev132q-long.log`; `dev132q-long-partial-29e9.log`
is the identical prefix of the long run from an interrupted first
launch). Nothing posted externally.*
