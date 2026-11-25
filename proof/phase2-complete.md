# BB(6) holdout #168016 — phase 2 of S′: proof complete for m ≤ 130 (Phase 8, 2026-11-25)

- Seed index: **168016**
- Spec: `1RB1RA_1RC1LB_0LD0RA_1RF1LE_---1LF_1LC0LF`
- Starting point: Phase 6 (`sprime-phase2-proof.md`) decomposed
  phase 2 and left two gaps; Phase 7 (`ud-proof.md`) closed
  gap 1 (the interval lemma, via the chain decomposition of
  U_d). **This phase closes gap 2 — the return mechanism —
  and assembles the complete proof status of phase 2.**
  Phase 2 of the S′ family is now proven, in human-readable
  shift rules, for every even m ≤ 130.

## 1. The Return Lemma (new, proven)

**Statement.** For every even m with 2 ≤ m ≤ 130, starting
from the cascade configuration D(m, m/2) the machine reaches
Y′(m) in exactly

    R(m) = (m² + 3m − 4)/2

steps, never halting on the way. Moreover the return is
exactly the first R(m) steps of the warm-up W_{m/2} of the
universal trajectory U_{m/2}: it ends one step before the
first read on which the size-m and size-(m+2) tapes differ,
and that differing cell is the size-m tape's own ambient
anchor, whose presence is exactly what completes Y′(m).

Notation as before: d := m/2; Π := 1^4 0 1^41 0 (positions
0…46); D(M, d) = Π · 1^(67−d) · (0 1^2)^(d−1) · 0^(M+1−2d) ·
1^2, head at 112 − d, state C; the anchor 1^2 of D(M, d)
sits at 112 + M … 113 + M. Y′(m) (Phase 5) is
Π · 1^64 · 0 · 1^(m+2) over [0, 113 + m] (0 at 111, run
1^(m+2) at 112…113+m), head at 112 + m, state B.

### Proof

**(i) Agreement of the two starting tapes.** D(m, d) and
D(m + 2, d) have the same Π, the same solid 1^(67−d) at
47…113−d, and the same pairs (0 1^2)^(d−1) ending at
110 + m; both have 0 at 111 + m (a gap cell in each: the
size-m gap is 0^1, the size-(m+2) gap is 0^3). Hence the
two tapes agree on every cell ≤ 111 + m. They first differ
at **112 + m**: the size-m tape has 1 there (the first cell
of its ambient anchor 1^2 at 112 + m…113 + m), the
size-(m+2) tape has 0 (its gap continues to 113 + m, its
anchor sits at 114 + m…115 + m). ∎ (run-length identity)

**(ii) The first R(m) steps of U_d read only cells
≤ 111 + m.** By Phase 6 §C, the return's trajectory is the
prefix of U_{m/2} run at size m + 2, i.e. of the Interval
Lemma instance D(m + 2, d) → D(m + 2, d + 1), proven in
Phase 7. U_d begins with the warm-up W_d (Phase 7 §4.2),
whose rounds cost Σ_{r=1}^{d−1} (4r + 3) = 2d² + d − 3 and
whose final segment costs 4d + 5. The arithmetic

    (2d² + d − 3) + 1 + 2d = 2d² + 3d − 2 = R(m)
    (with d = m/2: (m² + 3m − 4)/2 ✓)

says the first R(m) steps of W_d are exactly: all d − 1
rounds, then the final segment's C-step (1 step) and
A-sweep (2d steps) — the B-step of the final segment is
step R(m) + 1. Reads during these steps, from the
Warm-up Lemma's proof (Phase 7 §4.2): round r reads only
cells ≤ σ + 2 ≤ 110 + 2d = 110 + m (and ≥ 112 − d);
the C-step reads cell 111; the A-sweep reads cells
112…111 + m. So every read in the first R(m) steps is at
a cell in [112 − d, 111 + m]. Note R(m) = W_d − (2d + 4)
< W_d: **the return never leaves the warm-up** — no chain
block U_j(−1) of U_{m/2} is ever entered. ∎

**(iii) Trajectory identity.** Apply the Window Principle
(Phase 7 §4.1) with window (−∞, 111 + m]: the size-(m + 2)
run is known (by (ii)) never to read outside it for R(m)
steps, and by (i) the size-m tape agrees with it there.
Hence the size-m run from D(m, d) follows the identical
(state, head) trajectory for R(m) steps, never halts, and
the two tapes agree on (−∞, 111 + m] throughout. ∎

**(iv) The endpoint is Y′(m).** Track the size-(m + 2)
configuration through the warm-up prefix (Phase 7 §4.2):
after the rounds the solid is 1^(64+2d) on [47, 110 + m]
with head at 111, state C; the final segment's C-step
writes 0 at 111 (`0RA`); the A-sweep (`1RA` × (2d − 1),
then `1RB`) traverses the solid cells 112…110 + m and
writes 1 at 111 + m, ending with head at 112 + m, state
B. So at step R(m) both runs are in state B with head at
112 + m, and both tapes read, on (−∞, 111 + m]:

    Π · 1^64 · 0 · 1^m        (1^64 at 47…110, 0 at 111,
                               1^m at 112…111 + m).

Beyond 111 + m the size-m tape carries its ambient anchor
1^2 at 112 + m…113 + m, which the return never touches:
no step reads or writes a cell > 111 + m (by (ii)), and
the head first *arrives* at 112 + m only on the last
step's move. Assembling the size-m tape at step R(m):

    Π · 1^64 · 0 · 1^m · 1^2  =  Π · 1^64 · 0 · 1^(m+2)
    over [0, 113 + m], head at 112 + m, state B

— exactly Y′(m) (Phase 5's definition: L′[:111] · "01" ·
1^(m+1), i.e. the run from 112 has length m + 2). ∎

**(v) Sharpness — where and why it departs.** Step
R(m) + 1 reads cell 112 + m in state B. The universal run
reads 0 and fires B on 0 → `1RC` (continuing W_d toward
F_1(d)); the size-m run reads 1 and fires B on 1 → `1LB`
— which is precisely phase 3's first step from Y′(m)
(Phase 5). So R(m) is the *maximal* prefix of U_{m/2}
that the size-m tape follows, the departure is a single
named cell (the ambient anchor's first cell), and the
"truncation" of Phase 6 §C is now explained cell-by-cell:
the size-(m + 2) warm-up would spend its next steps
building a local anchor at 111 + m…112 + m; the size-m
tape already owns an anchor two cells earlier, and that
anchor's 1s are exactly the last two cells of Y′(m)'s
defining run. ∎

**Side conditions.** m even; d = m/2 ≤ 65, i.e. m ≤ 130,
inherited from the Warm-up Lemma (the rounds need head
positions ≥ 47 and solid exponent 67 − d ≥ 2). The base
d = 1 (m = 2) is included: no rounds, R(2) = 3.

### Verification (exact, computational)

`phase8.py` (independent `tm.py` path) checks, for each
m ∈ {2, 4, 6, 8, 20, 24, 28, 32, 36, 40, 44} — **all
PASS, zero failures**:

- start tapes agree on (−∞, 111 + m] and differ at
  112 + m exactly as (i) claims;
- lockstep (state, head, read symbol) identity for steps
  1…R(m); maximum read position over those steps is
  exactly 111 + m;
- divergence exactly at step R(m) + 1, state B, head
  112 + m, reads 1 (size m) vs 0 (size m + 2);
- size-m configuration at step R(m) equals the Y′(m)
  closed form (full tape + head + state);
- size-(m + 2) configuration at step R(m) equals the
  warm-up intermediate of (iv) (full configuration);
- every round-boundary configuration of W_d matches
  Phase 7's round invariant, for both ambient sizes;
- (bonus) the size-(m + 2) run's chain boundaries match
  the F_j(d) closed forms and its arrival equals
  D(m + 2, d + 1) at exactly C_d — extending Phase 7's
  computational verification of the chain decomposition
  from d ≤ 12 to **d ≤ 22**.

Held-out values: m = 36 and m = 44 were used in no
earlier phase's return analysis (Phase 6 checked the
return identity at m = 20, 24, 28 and the cost at 32),
and d = 18, 20, 22 exceed Phase 7's verified range. Per
the Phase-3 (k = 56) lesson, the conclusion rests on the
proof above, not on the count of confirmations; the
checks exist to catch errors in the closed forms.

## 2. Complete proof status of phase 2 (S′ family)

Phase 2 at size m, X′(m) → Y′(m), cost
ph2(m) = 3·2^((m+4)/2) − 2m − 14, decomposes as

    ph2(m) = (m + 1)                       [initial segment]
           + Σ_{d=1}^{m/2 − 1} (ph2(2d) + 3)   [cascade intervals]
           + R(m)                          [return]

| Component | Statement | Status |
|---|---|---|
| Initial segment | X′(m) → D(m, 1) in m + 1 steps | **Proven** (Phase 6 §C, shift rules, all m) |
| Midpoint split | X′(m) → A(m) → Mid(m) → Z(m) → Y′(m) with two ph2(m−2) halves | Configurations verified exactly at all even m = 4…36 (Phase 6 §A); **superseded as a proof route** by the cascade decomposition below (it remains a true, checked description) |
| Glue 1 | A(m) → Mid(m) in m + 3 steps | **Proven** (Phase 6 §B, shift rules, all even m ≥ 4) |
| Glue 2 | Z(m) → Y′(m) in m + 3 steps | **Proven** (Phase 6 §B, shift rules, all even m ≥ 2) |
| Cascade intervals | D(m, d) → D(m, d + 1) in ph2(2d) + 3 steps, trajectory the universal U_d, head range [111 − d, 113 + 2d] | **Proven** (Phase 7: chain decomposition U_d = W_d · U_1(−1) ··· U_{d−1}(−1), warm-up by shift rules, window principle, induction on d; all d ≤ 65, all m ≥ 2d + 2). Computationally verified to d ≤ 12 (Phase 7) and d ≤ 22 (Phase 8) |
| Return | D(m, m/2) → Y′(m) in R(m) = (m² + 3m − 4)/2 steps | **Proven** (Phase 8 §1 above: agreement + warm-up prefix bound + window principle + anchor completion; all even m ≤ 130). Computationally verified at 11 values of m incl. held-out 36, 44 |

The other two phases of the S′ period were already
proven in Phase 5: phase 1, S′(m) → X′(m) in 3 steps
(all m, no side conditions), and phase 3, Y′(m) →
S′(m + 2) in 2m + 5 steps (all m, shift rules).

**Hence: the full S′ period S′(m) → S′(m + 2), cost
P(m) = 3·2^((m+4)/2) − 6, is proven for every even
m ≤ 130.**

## 3. The resulting theorem for S′

**Theorem (human-proven, unmechanised).** Let the machine
be started from the configuration S′(2) of the second
bounce family. Then for every even m with 2 ≤ m ≤ 130 it
reaches S′(m + 2) after exactly P(m) further steps without
halting; in particular it reaches S′(132), and therefore
**does not halt at any step before the arrival of
S′(132)**.

Combined with the earlier phases' exact simulation of the
actual trajectory from the blank tape — the first family
S (k = 2…56), the breach, the 51,539,607,417-step
transient, and the arrival at S′(2), all recorded with
exact configuration matches (Phases 3–4) — the machine
**#168016 does not halt within its first
885,443,715,596,040,733,867 steps (≈ 8.85 × 10^20)**,
the arrival step of S′(132).

### What is human-proven vs. what still needs mechanisation

Human-proven (shift-rule arguments, uniform in the
parameters, of the kind the bbchallenge community
accepts as the mathematical content of a proof):

- Phases 1 and 3 of the S′ period, all m (Phase 5).
- Phase 2 for all even m ≤ 130, via: the initial segment
  and both glues (Phase 6), the Interval Lemma for all
  d ≤ 65 via the chain decomposition and the Warm-up
  Lemma (Phase 7), and the Return Lemma (Phase 8).
- Consequently the S′ induction through m = 130 and the
  non-halting bound ≈ 8.85 × 10^20 steps above.

Established by exact computation only (finite checks,
independently re-run several times, but not shift-rule
proofs and not mechanised):

- The blank-tape trajectory up to S′(2): family S to
  k = 56, the k = 56 break, the breach configuration,
  and the ≈ 5.15 × 10^10-step transient into S′
  (Phases 3–4). This is a finite computation
  (≈ 5.8 × 10^10 steps), so it is mechanisable in
  principle by a verified simulator, but it has not been
  mechanised.

Still needed for a community-grade claim that #168016
is *decided* (non-halting, full stop):

1. **The m = 132 period.** The side condition m ≤ 130 is
   geometric (Phase 5): the deepest phase-2 descent
   reaches head position 112 − m/2, which stays inside
   the wall's rightmost block (positions 47…111) iff
   m ≤ 130; at m = 132 it reaches position 46, the
   separator 0 at the block's left edge. Phase 5
   predicts a *break* of the S′ pattern at m = 132 — and
   by Phase 4's precedent a break is a transition to a
   new regime, not a halt. Deciding #168016 requires
   analysing the post-S′ regime (or another argument
   covering m ≥ 132). **Nothing in Phases 5–8 decides the
   machine outright.**
2. **Mechanisation.** None of the shift-rule proofs
   (Phases 5–8) has been formalised in Lean or Rocq, and
   the finite pre-S′ computation has not been re-run
   inside a verified checker. Community-grade credit
   (bbchallenge) ultimately wants a machine-checked
   artefact (cf. BB(5)'s Rocq proof); the human proofs
   here are written to be mechanisable — every step is a
   uniform rule over explicit run-length forms — but the
   formalisation work itself remains.
3. The Phase-3 §D community caveat still applies:
   nothing has been posted externally, and no claim is
   made beyond what is written here.

## Artefacts (this phase)

- `phase8.py` — the verification suite of §1 (lockstep
  return/divergence checks, round invariants, F_j(d)
  boundaries and D(m + 2, d + 1) arrivals for the
  size-(m + 2) runs): **all PASS** at
  m = 2, 4, 6, 8, 20, 24, 28, 32, 36, 40, 44.
- `phase8-run.log` — the m = 24…44 run output.
