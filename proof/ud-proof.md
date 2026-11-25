# BB(6) holdout #168016 — the universal interval U_d decomposed (Phase 7, 2026-11-25)

- Seed index: **168016**
- Spec: `1RB1RA_1RC1LB_0LD0RA_1RF1LE_---1LF_1LC0LF`
- Starting point: Phase 6 (`sprime-phase2-proof.md`), Section E,
  gap 1 — the **interval lemma**: for every d ≥ 1 and every
  m ≥ 2d + 2, the D-cascade interval from D(m, d) reaches
  D(m, d + 1) in exactly ph2(2d) + 3 steps with head range
  ⊆ [111 − d, 113 + 2d]. Phase 6 verified this for d ≤ 15
  (costs) and d ≤ 10 (trajectory identity) but left U_d's
  interior undecomposed. **This phase decomposes U_d
  completely and reduces the interval lemma to shift-rule
  arguments.** What remains open is listed in Section 6 —
  notably Phase 6's gap 2 (the return mechanism), so phase 2
  as a whole is still not a finished proof.

## Headline results

1. **Chain decomposition (exact).** For every d ≥ 2,

       U_d = W_d · U_1(−1) · U_2(−1) · … · U_{d−1}(−1),

   where U_j(−1) denotes U_j's (state, head) trajectory with
   every head position shifted by −1, and W_d (the "warm-up")
   is an explicit episode of length **2d² + 5d + 2**. The
   blocks are contiguous and cover U_d exactly; the cost
   identity C_d = (2d² + 5d + 2) + Σ_{j<d} C_j is exact
   algebra (Section 3). For d = 1 there are no blocks and
   U_1 = W_1 (9 steps).
2. **Junction configurations in closed form.** The block
   U_j(−1) starts at

       F_j(d) = Π · 1^(66−j) · (0 1^2)^(j−1) · 0^(2(d−j)+1) · 1^2,
       head at 111 − j, state C,

   with the "local anchor" 1^2 at the j-independent position
   111 + 2d … 112 + 2d. F_j(d) agrees with D(2d, j) translated
   by −1 on U_j's whole visited window (Section 4.3), so each
   block is U_j running against a *local* instance of its own
   starting configuration — the induction closes.
3. **The warm-up is proven by shift rules.** W_d consists of
   d − 1 identical-shape "rounds" (round r: `C:1, A:2r,
   B:2r+2`, cost 4r + 3, absorbing one (0 1^2) pair into the
   solid block) followed by a final segment (`C:1, A:2d, B:1,
   C:1, D:1, E:1, F:2d`, cost 4d + 5) of exactly the same
   shape as Phase 6's glue segments. Both parts are proven
   for all d and all m ≥ 2d + 2 in Section 4.2.
4. **Verification is total on the tested range.** Every
   formula, block boundary, window agreement, round
   invariant, endpoint, cost and head range above was
   checked by full-configuration exact match for **all
   d = 1…12** (fresh runs via the independent Python
   simulator `tm.py`; `ud_verify.py`, `ud_verify2.py` — zero
   failures), extending Phase 6's d ≤ 10 trajectory data.
   The proofs in Section 4 do not rest on the size of this
   range; the range is a check on the formulas, in the
   spirit of Phase 3's lesson.

## 1. Statements

Notation as in Phase 6: Π := 1^4 0 1^41 0 (positions 0…46);
D(m, d) is the cascade configuration

    D(m, d): tape Π · 1^(67−d) · (0 1^2)^(d−1) · 0^(m+1−2d) · 1^2,
             head at 112 − d, state C,

and C_d := ph2(2d) + 3 = 3·2^(d+2) − 4d − 11. Throughout,
1 ≤ d ≤ 65 (the wall geometry needs the solid exponent
67 − d ≥ 2 and cascade head positions ≥ 47; the S′
application needs only d ≤ 64, since m ≤ 130 there).

**Interval Lemma (plain form).** For every d ≥ 1 and every
m ≥ 2d + 2, starting from D(m, d) the machine reaches
D(m, d + 1) in exactly C_d steps, never halts on the way,
and the head stays in [111 − d, 113 + 2d] (the minimum is
attained only at the final step).

**Interval Lemma (window form).** Let X be any configuration
in state C whose tape agrees with D(M, d), for some
M ≥ 2d + 2, on the window [111 − d, 113 + 2d] (up to a global
translation of the whole picture). Then the run from X
follows U_d's trajectory (translated) for C_d steps, never
reads outside the window, and arrives at the configuration
that agrees with D(M, d + 1) on the window and with X
outside it.

The window form is what the induction actually uses (blocks
start from F_j(d), not from a genuine D(·, j)); the plain
form is the special case X = D(m, d). The window form
follows from the plain form by the Window Principle
(Section 4.1) plus the range claim, which is part of the
statement.

## 2. Verified facts (computational, exact)

All via `tm.py`-based runs from closed-form D(m, d) starts
(m = 40; m = 30 cross-checks), full-configuration
comparisons — no fits anywhere:

- **(V1) Endpoints, costs, ranges.** For d = 1…12: the run
  from D(m, d) reaches D(m, d + 1) at exactly step C_d, with
  head range exactly [111 − d, 113 + 2d], and the
  (state, head) trajectory and the tape on [0, 113 + 2d] are
  m-independent (`ud.py`, `ud_verify.py`).
- **(V2) Skeleton size.** U_d's collapsed state skeleton has
  exactly 5·2^d − 3 runs (d = 1…8, `ud.py`).
- **(V3) Chain blocks.** For 2 ≤ d ≤ 12 and 1 ≤ j ≤ d − 1:
  the segment of U_d at offsets [off_j(d), off_j(d) + C_j],
  where off_j(d) = (2d² + 5d + 2) + Σ_{i<j} C_i, equals
  U_j's trajectory with head shifted by −1, exactly
  (`ud_verify.py` check 6; tuple-level).
- **(V4) Embedding census.** For d ≤ 8, the set of all
  contiguous embeddings of any U_j (j < d, any constant head
  shift in [−20, 20]) in U_d is *exactly* the recursion tree
  of the chain decomposition — no unexplained embeddings
  (`ud_split3.py` check 2).
- **(V5) Junction formulas.** F_j(d) as in Headline 2 equals
  the actual configuration at off_j(d), full tape on
  [0, 113 + 2d] plus head and state, for all 2 ≤ d ≤ 12,
  1 ≤ j ≤ d − 1 (`ud_verify.py` check 5). Special case
  j = d − 1: F_{d−1}(d) is Phase 6's split point E(d)
  configuration Π · 1^(67−d) · (0 1^2)^(d−2) · 0^3 · 1^2.
- **(V6) Window agreements.** F_j(d) agrees with D(2d, j)
  translated by −1 on [110 − j, 112 + 2j] (start agreement),
  and the arrival configuration at off_j(d) + C_j agrees
  with D(2d, j + 1) translated by −1 on the same window,
  with head 110 − j in state C (arrival agreement) — all
  2 ≤ d ≤ 12, 1 ≤ j ≤ d − 1 (`ud_verify.py` check 7,
  `ud_split5.py`, `ud_verify2.py`).
- **(V7) Warm-up template and invariants.** For d = 1…12,
  W_d's run sequence is exactly the template of Headline 3,
  and the configuration after round r (0 ≤ r ≤ d − 1) is
  exactly Π · 1^(67−d+3r) · (0 1^2)^(d−1−r) · 0^(m+1−2d) ·
  1^2 with head at 112 − d + r, state C (`ud_verify.py`
  checks 2–3).

## 3. The decomposition and its arithmetic

Define W_d := 2d² + 5d + 2 and off_j(d) := W_d +
Σ_{i=1}^{j−1} C_i. The chain decomposition (V3, V5) says
U_d visits F_1(d), F_2(d), …, F_{d−1}(d) at offsets
off_1(d) < off_2(d) < … and D(m, d + 1) at C_d. Cost
identity: Σ_{j=1}^{d−1} C_j = Σ_{j=1}^{d−1} (3·2^(j+2) − 4j − 11),
where Σ_{j=1}^{d−1} 3·2^(j+2) = 3·2^(d+2) − 24 and
Σ_{j=1}^{d−1} (4j + 11) = 2d(d − 1) + 11(d − 1)
= 2d² + 9d − 11, so Σ_{j<d} C_j = 3·2^(d+2) − 2d² − 9d − 13
and W_d + Σ_{j<d} C_j = 3·2^(d+2) − 4d − 11 = C_d. ✓
Run-count identity (consistency with V2): W_d has 3d + 4
runs, so (3d + 4) + Σ_{j<d} (5·2^j − 3) = 3d + 4 +
5·2^d − 10 − 3(d − 1) = 5·2^d − 3 ✓ (no junction merges:
W_d's last step is in state F and every block begins with a
C step; every block's last step is in state F and the next
block begins with a C step).

Reading the decomposition: W_d first *rebuilds the right
end of the tape* — it absorbs all d − 1 pairs into the solid
block and plants a fresh "local anchor" 1^2 at
111 + 2d … 112 + 2d, producing F_1(d). Each block U_j(−1)
then runs against the local environment F_j(d), which on
its visited window is exactly D(2d, j) shifted by −1: the
local instance has effective size M = 2d, independent of j,
because F_j(d)'s gap is 2(d − j) + 1 = (2d) + 1 − 2j. The
block's endpoint (the Interval Lemma at size j, instance
M = 2d, which is legitimate since 2d ≥ 2j + 2 for j ≤ d − 1)
turns the local D(2d, j) pattern into D(2d, j + 1), i.e.
turns F_j(d) into F_{j + 1}(d); the last block (j = d − 1)
produces D(m, d + 1), its local anchor becoming the final
pair's 1^2. This is the same "truncated universal
trajectory" phenomenon as Phase 6's return, now with the
mechanism made explicit: the trajectory is forced by
window agreement, and the arrival is forced by agreement
inside the window plus identity outside it.

## 4. Proofs (shift rules)

Transition reference (spec groups A…F, symbol 0 then 1):
A: `1RB`, `1RA` · B: `1RC`, `1LB` · C: `0LD`, `0RA` ·
D: `1RF`, `1LE` · E: `---`, `1LF` · F: `1LC`, `0LF`.
Note the machine is *trajectory-determined*: in each state
the two symbols lead to different (next state, move) pairs,
so a (state, head) trajectory determines the symbol read —
hence every write — at each step.

### 4.1 Window Principle

If two configurations agree on a window S (up to
translation), both runs are started in the same state with
heads at corresponding positions, and one of the runs is
known never to read outside S for t steps, then the other
run also stays in S for t steps, the two (state, head)
trajectories agree (up to translation) for t steps, and the
two tapes agree on S afterwards. *Proof:* induction on
steps. At each step both heads are at corresponding cells
of S reading equal symbols, so the same transition fires:
same write (inside S), same move, same next state; the
tapes therefore still agree on S. ∎  All uses below have
the range claim of the Interval Lemma as the "known never
to read outside" input.

### 4.2 Warm-up Lemma: D(m, d) → F_1(d) in W_d steps

For all d ≥ 1 and m ≥ 2d + 2, the run from D(m, d) reaches
F_1(d) in exactly 2d² + 5d + 2 steps with head in
[112 − d, 113 + 2d] (for d = 1 the minimum 110 is attained
at the last step). During W_d the head never exceeds
113 + 2d < 112 + m, so the ambient gap and anchor are never
read: the episode is m-independent.

**Rounds.** Claim: before round r (1 ≤ r ≤ d − 1) the
configuration is

    Π · 1^(67−d+3(r−1)) · (0 1^2)^(d−r) · 0^(m+1−2d) · 1^2,
    head at σ − (2r − 1), state C,

where σ := 113 − d + 3(r − 1) is the solid's right end
(solid = [47, σ]). (r = 1 is D(m, d) itself.) Round r is
the run sequence `C:1, A:2r, B:2r+2`:

1. **C-step** (1): the head cell is solid (47 ≤ head ≤ σ,
   using d ≤ 65), value 1. C on 1 → `0RA`: write 0 at the
   head, move right, state A.
2. **A-sweep** (2r): cells head + 1 … σ are 1 (there are
   σ − head = 2r − 1 of them): A on 1 → `1RA` repeated.
   Cell σ + 1 is the leftmost remaining pair's 0: A on 0 →
   `1RB` writes 1, head to σ + 2, state B.
3. **B-sweep** (2r + 2): cells σ + 2, σ + 3 are the pair's
   1^2, cell σ + 1 is now 1, and cells σ down to head + 1
   are 1 — that is 2r + 1 cells read as 1: B on 1 → `1LB`
   repeated, walking left to the head's original cell,
   which is 0 (step 1). B on 0 → `1RC`: write 1 (restoring
   the cell), head one right, state C.

Net effect: the pair at σ + 1 … σ + 3 is now all 1s, i.e.
absorbed into the solid (new right end σ + 3); the erased
cell is restored; head at (σ − (2r − 1)) + 1 = the claim's
head for round r + 1 (σ' − (2r + 1) with σ' = σ + 3 ✓).
Cost 1 + 2r + (2r + 2) = 4r + 3. This is an induction on
r; the round reads only cells ≤ σ + 2 ≤ 110 + 2d. ∎
After round d − 1: solid 1^(64+2d) on [47, 110 + 2d], no
pairs, head at 111, state C.

**Final segment** (4d + 5 steps), from that configuration
(gap 0^(m+1−2d) beyond the solid; the cells 111 + 2d,
112 + 2d, 113 + 2d are gap cells, since m ≥ 2d + 2 puts the
ambient anchor at ≥ 114 + 2d):

1. **C-step** (1): cell 111 is solid 1. C on 1 → `0RA`:
   write 0 at 111, head to 112, state A. (The solid is
   split: [47, 110] and [112, 110 + 2d].)
2. **A-sweep** (2d): cells 112 … 110 + 2d are 1 (2d − 1
   cells): A on 1 → `1RA` repeated; cell 111 + 2d is 0:
   A on 0 → `1RB` writes 1, head to 112 + 2d, state B.
3. **B-step** (1): cell 112 + 2d is 0: B on 0 → `1RC`
   writes 1, head to 113 + 2d, state C.
4. **C-step** (1): cell 113 + 2d is 0: C on 0 → `0LD`,
   head to 112 + 2d, state D.
5. **D-step** (1): cell 112 + 2d is 1 (step 3): D on 1 →
   `1LE`, head to 111 + 2d, state E.
6. **E-step** (1): cell 111 + 2d is 1 (step 2): E on 1 →
   `1LF`, head to 110 + 2d, state F. (E reads 1 here, so
   no halt.)
7. **F-sweep** (2d): cells 110 + 2d down to 112 are 1
   (2d − 1 cells): F on 1 → `0LF` repeated, erasing them,
   head to 111; cell 111 is 0 (step 1): F on 0 → `1LC`
   writes 1 (solid restored to [47, 111], 65 cells), head
   to 110, state C.

Result: Π · 1^65 · 0^(2d−1) · 1^2 with the 1^2 at
111 + 2d … 112 + 2d, head at 110, state C — exactly
F_1(d). Total: Σ_{r=1}^{d−1} (4r + 3) + (4d + 5)
= (2d² + d − 3) + (4d + 5) = 2d² + 5d + 2. ∎
(For d = 1 there are no rounds and the final segment alone
gives the 9-step base case U_1: D(m, 1) → D(m, 2); the
"F_1(1)" it produces agrees with D(m, 2) on the window and
the two agree outside it, since both have Π + solid on the
left and gap + ambient anchor on the right.)

### 4.3 Window agreement identities

For 1 ≤ j ≤ d − 1, F_j(d) agrees with D(2d, j) translated
by −1 on [110 − j, 112 + 2j], and F_{j+1}(d) (resp.
D(m, d + 1) for j = d − 1) agrees with D(2d, j + 1)
translated by −1 on the same window. These are identities
between explicit run-length forms; the content of the
window on each side:

- F_j(d) on [110 − j, 112 + 2j]: solid 1s on
  [110 − j, 112 − j]; pairs (0 1^2)^(j−1) on
  [113 − j, 109 + 2j]; 0s on [110 + 2j, 112 + 2j].
- D(2d, j) on [111 − j, 113 + 2j] (the window shifted back
  by +1): solid 1s on [111 − j, 113 − j]; pairs
  (0 1^2)^(j−1) on [114 − j, 110 + 2j]; 0s on
  [111 + 2j, 113 + 2j] (its gap is 0^(2d+1−2j)).

Translating the second by −1 gives the first, run by run. ✓
The arrival side is identical with j replaced by j + 1
(solid [110 − j, 111 − j], pairs (0 1^2)^j on
[112 − j, 111 + 2j], 0 at 112 + 2j), and for j = d − 1 the
arrival side is D(m, d + 1): its solid reaches 112 − d, its
pairs (0 1^2)^d occupy [113 − d, 112 + 2d] — on the window
[111 − d, 110 + 2d] that is pairs' first d − 1 pairs plus
the 0 at 110 + 2d, matching the translated D(2d, d) — and
outside the window it agrees with F_{d−1}(d): Π and solid
1s on the left; at 111 + 2d … 112 + 2d its last pair's 1^2,
which is F_{d−1}(d)'s untouched local anchor; beyond, the
ambient gap and anchor. ✓ (All instances machine-checked
for d ≤ 12 — V6.)

### 4.4 The block step and assembly

**Block step.** Assume the Interval Lemma (window form)
for all j' < d. Fix 1 ≤ j ≤ d − 1. By Section 4.3,
F_j(d) agrees with D(2d, j) translated by −1 on U_j's
visited window translated by −1, [110 − j, 112 + 2j]; the
instance M = 2d satisfies M ≥ 2j + 2. By the Window
Principle and the lemma at size j, the run from F_j(d)
follows U_j's trajectory translated by −1 for exactly C_j
steps, never leaves the window, and arrives at the
configuration agreeing with D(2d, j + 1) translated by −1
on the window and with F_j(d) outside it. By Section 4.3
that configuration is exactly F_{j+1}(d) — resp.
D(m, d + 1) for j = d − 1: on the window by the arrival
identity; outside the window because F_{j+1}(d) and
F_j(d) agree there (left: Π and solid 1s — F_{j+1}'s solid
ends at 111 − j ≥ the window's left edge 110 − j;
right: on [113 + 2j, 110 + 2d] both are 0 (F_j's gap
runs from 110 + 2j, F_{j+1}'s from 112 + 2j), then the
common local anchor at 111 + 2d … 112 + 2d, then the
common ambient tape). Head range during the block:
[110 − j, 112 + 2j] ⊆ [111 − d, 113 + 2d]. ∎

**Assembly (induction on d).** d = 1: Section 4.2's final
segment (9 steps, full trace in Phase 6). d ≥ 2: the
Warm-up Lemma gives D(m, d) → F_1(d) in W_d steps with
head in [112 − d, 113 + 2d]; the Block step applied at
j = 1, …, d − 1 gives F_1(d) → F_2(d) → … → D(m, d + 1)
in Σ_{j<d} C_j steps. Total W_d + Σ_{j<d} C_j = C_d
(Section 3). Head range: warm-up ⊆ [112 − d, 113 + 2d];
blocks ⊆ [110 − j, 112 + 2j] ⊆ [111 − d, 113 + 2d]; the
global minimum 111 − d is the final head position,
attained only at the end. No halt occurs: the warm-up
never puts E on 0 (E occurs once, reading 1), and blocks
inherit no-halt from the induction hypothesis. This
proves the plain form; the window form follows by the
Window Principle (a general X agreeing with D(M, d) on
the window runs the translated trajectory throughout,
since every stage of the decomposition reads only within
the window: W_d reads ≤ 113 + 2d and ≥ 112 − d, blocks
read within their sub-windows). ∎

## 5. What this gives

- The D-cascade descent of Phase 6 §C is now fully proven:
  the (already proven) initial segment X′(m) → D(m, 1),
  then intervals U_1, …, U_{m/2 − 1} by the Interval
  Lemma, reaching D(m, m/2) — for every even m ≤ 130,
  i.e. as far as the wall geometry (side condition) allows.
- The interval lemma was the last unproven piece of the
  cascade itself. It does **not** by itself finish phase 2:
  see Section 6.

## 6. Remaining gaps (precise)

1. **The return mechanism (Phase 6 §E gap 2) is still
   empirical.** That D(m, m/2) → Y′(m) in R(m) =
   (m² + 3m − 4)/2 steps, with trajectory equal to the
   first R(m) steps of U_{m/2} at size m + 2, is verified
   (m = 20, 24, 28) but not explained cell-by-cell. The
   present decomposition suggests the route — U_{m/2}'s
   own chain decomposition, truncated where the size-m
   tape first differs from the size-(m + 2) tape — but
   carrying it out is a separate step. Until then, phase 2
   for general m ≤ 130 is proven *except* its final return
   segment.
2. **Not mechanized.** Sections 4.2–4.4 are human-level
   shift-rule proofs, uniform in (d, j, r, m); they have
   not been formalized in Lean/Rocq. The computational
   verification (Section 2) covers d ≤ 12 for the interval
   decomposition (and Phase 6 covered costs to d ≤ 15);
   per Phase 3's lesson, the proofs — not the count of
   confirmations — are what the conclusion rests on, and
   any error would most likely hide in the run-arithmetic
   of Section 4.3, which is finite and checkable line by
   line.
3. **The m = 132 caveat is unchanged** (Phase 6 §E.3): a
   completed phase-2 proof for m ≤ 130 would prove the S′
   induction through the arrival of S′(132) and
   non-halting up to step ≈ 8.85×10^20, but the m = 132
   period itself (predicted break, new regime) needs its
   own analysis before #168016 can be called decided.
4. Nothing here is ready to post externally (the Phase-3
   §D community caveat still applies).

## Artefacts (this phase)

- `ud.py` — standalone U_d runs from closed-form D(m, d):
  endpoint/cost/range/m-independence and skeleton counts
  for d = 1…8; trajectories + per-step snapshots saved to
  `ud-traj.json`.
- `ud_split.py` — first split search: the tail embedding
  (U_{d−1} at offset C_d − C_{d−1}, shift −1) and the E(d)
  closed form.
- `ud_split2.py` — full embedding census; E(d) window
  agreement with shift-1 of D(2d, d − 1).
- `ud_split3.py` — the chain decomposition: block-boundary
  checks and the embedding-census = recursion-tree check;
  junction configuration dumps.
- `ud_split4.py` — F_j(d) closed-form verification; start
  window agreements; warm-up run counts.
- `ud_split5.py` — arrival window agreements (d ≤ 8);
  W_d run tables and run-boundary snapshots.
- `ud_verify.py` — the full verification suite, d = 1…12,
  fresh runs (endpoints, ranges, W template, round
  invariants, F formulas, block trajectories, start
  agreements): **0 failures**.
- `ud_verify2.py` — arrival window agreements for
  d = 9…12: **0 failures**.
