# BB(6) holdout #168016 — S′ phase 2: the midpoint split (Phase 6, 2026-11-25)

- Seed index: **168016**
- Spec: `1RB1RA_1RC1LB_0LD0RA_1RF1LE_---1LF_1LC0LF`
- Starting point: Phase 5 (`sprime-phases-168016.md`) — the S′ period
  decomposes as ph1 = 3 (proven), ph2(m) = 3·2^((m+4)/2) − 2m − 14
  (empirical), ph3 = 2m + 5 (proven), with phase-2 head range
  [112 − m/2, 112 + m]. Phase 2 was the only unproven phase. This
  phase attacks its internal structure.

## Headline results

1. **The midpoint split exists and is exact.** Phase 2 at size m
   passes through three explicit formula configurations,

       X′(m) ──ph2(m−2)──▶ A(m) ──m+3──▶ Mid(m)
             ──ph2(m−2)──▶ Z(m) ──m+3──▶ Y′(m),

   i.e. ph2(m) = ph2(m−2) + (m+3) + ph2(m−2) + (m+3), with A(m),
   Mid(m), Z(m) given below in closed form. The two (m+3) segments
   are **proven for all m** by shift rules (Section B). The three
   configurations are verified exactly (full tape + head + state)
   at **every even m = 4…36** (Section A).
2. **A finer recursion (the D-cascade) explains the first half.**
   Phase 2 is a descent through explicit configurations D(m, d),
   d = 1…m/2, whose connecting episodes ("intervals") are
   **exactly m-independent universal trajectories** with cost
   ph2(2d) + 3 and head range [111 − d, 113 + 2d] (Section C).
   The first half of the split is, configurationally, the cascade
   up to a point inside the last interval; its collapsed state
   skeleton equals phase 2(m−2)'s skeleton with the final run
   removed (verified at m = 24, 32 — 10,233 and 163,833 runs,
   prefix-exact).
3. **Honest limits.** The second half (Mid(m) → Z(m)) has cost
   exactly ph2(m−2) and the same skeleton length as the first
   half, but it is **not** the same process as phase 2 at size
   m−2 (no reversal or state permutation identifies them; checked
   exhaustively at m = 24). It decomposes via the cascade as
   [tail of the last interval] + [prefix of the return]. And the
   universal interval trajectories themselves are **not yet
   decomposed**: proving the interval endpoint claim for all d
   is the one remaining lemma between here and a full proof of
   phase 2 for m ≤ 130 (Section E).

## A. The split: configurations and verification

Definitions (translation-invariant; positions relative to the
pattern's left edge; Π := 1^4 0 1^41 0, positions 0…46, so
L′ = Π · 1^65 · 0 with the 1^65 block at 47…111 and separator 0
at 112; tape blank outside [0, 113 + m]):

- **A(m)**: tape Π · 1^64 · 0 · 1^(m−3) · 0^3 · 1^2 — i.e. solid
  1^64 at 47…110, 0 at 111, block 1^(m−3) at 112…108+m, 0^3 at
  109+m…111+m, anchor 1^2 at 112+m…113+m — **head at 108+m,
  state A**.
- **Mid(m)**: tape Π · 1^64 · 0^(m−2) · 1^2 · 0 · 1^2 — gap
  0^(m−2) at 111…108+m, 1^2 at 109+m…110+m, 0 at 111+m, anchor
  1^2 at 112+m…113+m — **head at 111, state F**.
- **Z(m)**: tape Π · 1^63 · 0 · 1^m · 0 · 1^2 — solid 1^63 at
  47…109, 0 at 110, run 1^m at 111…110+m, 0 at 111+m, anchor 1^2
  at 112+m…113+m — **head at 111, state B**.

**Verification.** For every even m = 4, 6, …, 36 (17 values), an
isolated S′(m) start (independent Python simulator via `tm.py`;
X′(m) and Y′(m) also checked exactly in the same runs) passes
through A(m) at phase-2 offset exactly ph2(m−2), through Mid(m)
at exactly ph2(m−2) + m + 3, and through Z(m) at exactly
ph2(m) − (m+3) — full-configuration matches, not fits
(`split_test3.py`, `split_test4.py`). The C tool `sprime2.c`
(mode `dump`, an independent code path) agrees at m = 20, 24,
28, 32. Base case: phase 2 at m = 2 (6 steps) traced in full
(`sprime2.c` mode `ph2trace`); the split formulas already hold
at m = 4.

Cost check: ph2(m−2) + (m+3) + ph2(m−2) + (m+3)
= 2·ph2(m−2) + 2m + 6 = ph2(m) ✓ (the Phase-5 recurrence).

## B. The two glue segments — proven for all m (shift rules)

### Glue 1: A(m) → Mid(m) in m + 3 steps (all even m ≥ 4)

From A(m) (head at 108+m on the last cell of the block
1^(m−3) at 112…108+m, state A; cells 109+m, 110+m, 111+m are 0;
anchor 1^2 at 112+m…113+m):
1. **A-step** (1): A on 1 → `1RA`: head to 109+m, state A.
2. **Write** (1): A on 0 → `1RB`: writes 1 at 109+m, head to
   110+m, state B.
3. **Write** (1): B on 0 → `1RC`: writes 1 at 110+m, head to
   111+m, state C.
4. **Bounce** (1): C on 0 → `0LD`: head to 110+m, state D.
5. **Bounce** (1): D on 1 → `1LE`: head to 109+m, state E.
6. **Bounce** (1): E on 1 → `1LF`: head to 108+m, state F.
7. **F-sweep** (m−3 steps): F on 1 → `0LF` repeated: erases the
   block cells 108+m down to 112; head ends at 111, state F.
   (Uniform rule over a solid 1-run; the sweep stops because we
   stop counting at head 111 — cell 111 is 0 and is not read.)
Result: solid 1^64 (47…110) untouched; cells 111…108+m are 0
(cell 111 already 0, the rest erased) — the gap 0^(m−2); cells
109+m, 110+m are 1 (steps 2–3); cell 111+m still 0; anchor
untouched (head never exceeds 111+m). Head at 111, state F —
exactly Mid(m). Total 6 + (m−3) = m+3. ∎
State sequence [A,B,C,D,E] + F^(m−2) — matches the recorded
sequences at m = 20, 24, 28, 32 exactly (`split_test2.py`).

### Glue 2: Z(m) → Y′(m) in m + 3 steps (all even m ≥ 2)

From Z(m) (head at 111 on the first cell of the run 1^m at
111…110+m, state B; cell 110 is 0; cell 111+m is 0; anchor 1^2
at 112+m…113+m; solid 1^63 at 47…109):
1. **B-step** (1): B on 1 → `1LB`: head to 110, state B.
2. **Repair** (1): B on 0 → `1RC`: writes 1 at 110 (solid
   restored to 1^64 over 47…110), head to 111, state C.
3. **Repair** (1): C on 1 → `0RA`: writes 0 at 111, head to
   112, state A.
4. **A-sweep** (m−1 steps): A on 1 → `1RA` repeated over the
   run cells 112…110+m; head ends at 111+m, state A.
5. **Extension** (1): A on 0 → `1RB`: writes 1 at 111+m, head
   to 112+m, state B.
Result: cell 111 is 0, cells 112…111+m are 1, and the anchor
cells 112+m…113+m were already 1, so the run from 112 has
length m+2; the wall is Π · 1^64 · 0 with cells 111, 112
flipped `10 → 01` — exactly Y′(m), head at 112+m, state B. ∎
State sequence [B,C] + A^m + [B] — matches the recorded
sequences at m = 20, 24, 28, 32 exactly.

## C. The D-cascade: the finer recursion

### The descent configurations

For 1 ≤ d ≤ m/2 define

    D(m, d): tape Π · 1^(67−d) · (0 1^2)^(d−1) · 0^(m+1−2d) · 1^2,
             head at 112 − d, state C.

(Solid 1^(67−d) at 47…113−d; then d−1 pairs (0 1^2); then a
0-gap of length m+1−2d; then the anchor 1^2 at the span's right
end. At d = m/2 the gap has length 1 and the tail reads as
(0 1^2)^d.) These are exactly the configurations at which the
head, during phase 2, first reaches position 112 − d in state C
(the "new-minimum" events). Read off the C left-edge dumps at
m = 20, 24, 28, 32 — all d, exact RLEs (`sprime2.c` mode
`leftedge`; logs `leftedge-24.log`, `leftedge-28.log`,
`leftedge-32.log`).

### Initial segment: X′(m) → D(m, 1) in m + 1 steps — proven

From X′(m) (block 1^(m+1) at 113…113+m, head at 112+m, E):
step 1, E on 1 → `1LF` (head 111+m, F); then F on 1 → `0LF`
repeated erases cells 111+m down to 113 (m−1 steps; head ends
at 112, F); then F on 0 → `1LC` on the wall separator at 112
(writes 1, head 111, C). Result: solid 1^66 (47…112), gap
0^(m−1) (113…111+m), anchor 1^2 — exactly D(m, 1). Total
1 + (m−1) + 1 = m+1. A uniform-rule sweep over a solid block
terminated by the separator 0; routine induction on the block
length. ∎

### Intervals and the return (empirical, exact on the verified range)

- **Interval cost.** D(m, d) → D(m, d+1) takes exactly
  **ph2(2d) + 3** steps, independent of m — verified for all
  d < m/2 at m = 20, 24, 28, 32 (C dumps + Python).
- **Universality.** The interval's (state, head) trajectory is
  *exactly* the same for different m: verified by raw
  sequence equality across m = 24, 28, 32 for d = 1…10
  (`split_test3.py`, `split_test4.py`). Call this universal
  trajectory **U_d**. During U_d the head stays in
  **[111 − d, 113 + 2d]** (max = 113 + 2d verified for
  d = 1…10; min is the endpoint by construction). Every cell
  ≤ 113 + 2d has the same content in D(m, d) for all
  m ≥ 2d + 2 (solid + pairs on [0, 110 + 2d], 0s beyond, up to
  the anchor which sits at ≥ 112 + m ≥ 114 + 2d > 113 + 2d) —
  the empirical core of why U_d is m-independent.
- **Return.** D(m, m/2) → Y′(m) takes exactly
  **R(m) = (m² + 3m − 4)/2** steps (228, 322, 432, 558 at
  m = 20, 24, 28, 32). Moreover the return's (state, head)
  trajectory is *identical to the first R(m) steps of U_{m/2}*
  run at size m+2 (verified for the full return length at
  m = 20, 24, 28): the return is the universal trajectory,
  truncated by the size-m tape's right end.
- **Cost identity** (exact algebra from the pieces):
  ph2(m) = (m+1) + Σ_{d=1}^{m/2−1} (ph2(2d) + 3) + R(m).

## D. How the two decompositions fit together

- The split point A(m) lies **inside the last interval**
  U_{m/2−1}: at U-offset R(m−2) − 2 (equivalently
  2d² + 3d − 4 with d = m/2 − 1) after D(m, m/2 − 1). This is
  forced by the return identity: the size-(m−2) return *is*
  U_{m/2−1} truncated at R(m−2), and A(m) sits 2 steps before
  the corresponding truncation point. Half 1 of the split is
  therefore: initial segment + U_1 + … + U_{m/2−2} + the first
  R(m−2) − 2 steps of U_{m/2−1} — while phase 2 at size m−2 is:
  initial segment (2 steps shorter) + the same U_1…U_{m/2−2} +
  the return (= U_{m/2−1} truncated at R(m−2)). This is exactly
  why half 1's collapsed state skeleton equals phase 2(m−2)'s
  skeleton minus its final run (the Y′-extension step that the
  size-m run does not take).
- Half 2 (Mid(m) → Z(m)) is the complementary cascade segment:
  the rest of U_{m/2−1} (from U-offset R(m−2) + m + 1 to its
  end at D(m, m/2)), then the first R(m) − (m+3) steps of the
  return, ending at Z(m). Its cost is ph2(m−2) by the identity
  R(m) − R(m−2) = 2m + 1. It is a **distinct episode**, not a
  replay of phase 2(m−2): different skeleton (same length,
  L(m−2) − 1 runs, where L(s) = 5·2^(s/2) − 6), sharing the
  engine motif and, at m = 24, an identical final ≥ 40 runs
  with phase 2(m−2)'s skeleton — recorded as an observation,
  not an identity.

## E. What remains (precise gaps)

1. **The interval lemma (the core gap).** A complete proof of
   phase 2 needs, for every d ≥ 1: *from D(·, d) (any
   m ≥ 2d + 2), the machine reaches D(·, d+1) in ph2(2d) + 3
   steps with head range ⊆ [111 − d, 113 + 2d].* Verified for
   d ≤ 15 (costs, inside the cascades at m ≤ 32) and d ≤ 10
   (trajectory identity + ranges). But U_d's *interior* is not
   yet decomposed: its collapsed skeleton has L(2d) + 3
   = 5·2^d − 3 runs and is **not** phase 2(2d)'s skeleton, nor
   a rotation or substring of it (checked d = 2, 3, 4). Finding
   U_d's own split configurations (the D-frame analogues of
   A/Mid/Z) is the precise remaining problem. The base cases
   are in hand: U_1 is 9 steps (traced in full), phase 2 at
   m = 2 is 6 steps (traced in full).
2. **The truncation mechanism.** That U_{m/2} on the size-m
   tape reaches Y′(m) at step R(m) is verified as a trajectory
   identity (m = 20, 24, 28) but not yet explained
   cell-by-cell (which read first differs between the size-m
   and size-(m+2) tapes, and why the outcome is exactly
   Y′(m)). Needed to make the return a proof.
3. **Side condition and the m = 132 caveat.** Everything above
   lives inside the wall's rightmost block: the deepest
   descent at size m reaches head 112 − m/2 and D(m, m/2)'s
   solid is 1^(67 − m/2), both within the block (positions
   ≥ 47) iff **m ≤ 130** — the Phase-5 side condition, now
   visible in cascade terms. Closing gaps 1–2 for d ≤ 66
   would prove phase 2 for all m ≤ 130, hence the S′ induction
   through the arrival of S′(132). Note carefully what that
   does *not* do: the m = 132 period itself is predicted to
   break (Phase 5), and a break is not a halt — Phase 4's
   precedent is that a break leads to a transient and a new
   regime. So a phase-2 proof for m ≤ 130 decides #168016
   only together with an analysis of the post-S′ regime (or
   another argument covering m ≥ 132); on its own it proves
   non-halting *up to* step ≈ 8.85×10^20 and the full S′
   induction through m = 130. This sharpens, and partly
   corrects, the Phase-5 framing.
4. Nothing here is ready to post externally (the Phase-3 §D
   community caveat still applies).

## Artefacts (this phase)

- `sprime2.c` — C tool: `dump M` (configurations at the split
  offsets + fractions), `returns M`, `leftedge M` (D-event
  dumps), `trace M D` (step-by-step interval traces),
  `ph2trace M` (full phase-2 traces for small M). Transition
  tables copied from the validated `sprime.c`.
- `split_test.py` — first split identification (A/Mid configs,
  state sequences; independent Python path via `tm.py`).
- `split_test2.py` — glue state-sequence verification;
  skeleton comparisons (half 1 / half 2 / intervals).
- `split_test3.py` — A/Mid/Z formula checks (m = 6…36);
  interval trajectory m-independence (d ≤ 5); return vs
  next-size interval prefix identity; half-2 permutation /
  reversal tests.
- `split_test4.py` — formula checks extended to m = 4;
  interval independence (d = 6…10); interval / half / return
  head ranges.
- `leftedge-24.log`, `leftedge-28.log`, `leftedge-32.log`,
  `returns-20.log` — C dumps underlying the D-cascade.
