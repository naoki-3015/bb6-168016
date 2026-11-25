# Phase 18 — the post-exit continuation of #168016 (2026-11-25)

Question (Phase 17's single remaining gap, `168016-proof.md`
component #15): what happens after the right-edge regime's
β = 2 exit? The exit successor is the B-section
X(β_E) = (B, 4, (1^{β_E−2}), (2^{β_E−2})) in coordinates
shifted 2 cells left — the β block merged with the first
working run, RI's frozen prefix breached.

**Verdict.** The reset hypothesis — re-entry into a
right-edge-like system at the shifted interface — is
**refuted**. The continuation re-coordinatises, through a
finite audited segment, into the **standard I-system of
Phases 13–14** (the same five derived rules TDN / PUSH /
POP / TUP / Stage A), in a new frame: the two-block prefix
1¹⁷ 0 1^B2 is replaced by a **single block 1^a at the
tape's left edge**. Inside that frame the trajectory runs
an era (residue grind at last gap G = 1), hits the frame's
own boundary events — a regeneration rule REGEN at G = 1
(new, verified in closed form) and Stage A at G ≥ 3 — and
finally re-enters the right-edge regime at G = 2 via the
Phase 15 entry excursion, with a new entry parameter

  β′ = 2·β_E + 34   (measured at β_E = 4, 6, 8, 12, 16, 24),

so the whole post-R dynamics is an **infinite ascending
loop of already-derived systems**:

  I-frame era → REGEN → Stage-A era (G: G₀ → 2) → entry →
  right-edge cycles Γ (Phase 17) → β = 2 exit → X(β′) →
  re-coordinatisation → I-frame era → …

with span strictly increasing around the loop (+2 at
REGEN, +2 per right-edge cycle, settled span 3β_E + 51).
Mission outcome: **(a)** for the settled regime (derived
rule system + invariant, §2) and **(b)** for the full
continuation (infinite iteration of derived maps with a
monotone parameter, §5). Not (c): no new structure was
found. The remaining gaps are itemised in §7 — they are
derivations of three verified maps (REGEN, the grind's
closed form, the re-coordinatisation segment uniform in
β_E), not new dynamics.

Conventions: statuses (P)/(C)/(H) as in `168016-proof.md`.
All simulations are `phase15.c` mode `rsec` (exact
simulation, event auditor at every step: the run aborts on
any E-on-0 and counts D-on-0 reads and M4-danger F-on-0
triples (0,1,0)). **No run in this phase produced an
E-on-0, a D-on-0, or an M4-danger triple. The machine does
not halt anywhere in the post-exit continuation explored
here** (largest window: 2×10⁸ steps from σ_re(8)).

## 1. The exit successor and the re-coordinatisation segment

X(β_E) as a full tape configuration (Phase 17's shifted
coordinates unfolded): 

  tape = 1¹⁷ 0¹ 1³¹ 0² 1⁴ (0¹ 1²)^{β_E−2},  head B at cell 50

(the 0² is the breached separator plus the erased β cell;
the 1⁴ is the merged β remnant + first run). Verified
cell-for-cell against the σ_re trajectories at β_E = 4
(X reached at step 108), β_E = 8 (step 2,856), and
β_E = 6 (step 626, hence T(6) = 620 — a new end-to-end
data point for Phase 17's T(β_E)).

From X(β_E) the trajectory passes through three stages
(β_E = 4 traced in detail; β_E = 6, 8 analogous):

1. **Shifted-interface mini-regime** (~50 steps): mixed
   dynamics at the merged interface; the first run grows
   (4 → 6 → 8 in the old coding).
2. **Token walk at the original interface**: C-sections
   with β = 2 recur while a gap-3 token walks left through
   the (1, 2) tail, one pair per ~44 steps, until it is
   the leading gap.
3. **Escape**: at (C, β = 2, g₁ = 3) RPUSH fires at β = 2 —
   the Phase 15 §3 escape in reverse: the head sweeps
   left in F erasing the 1³¹ block (by ≈ step 300 of
   σ_re(4) the tape reads 1¹⁸ 0²⁹ …; the prefix is
   destroyed) and the working region reorganises at the
   tape's left edge. First left-edge sections at
   ≈ step 309 (β_E = 4).

The segment is a finite audited computation for each
β_E. Its cost (X → first canonical I-section, §2) grows
like the token pass's binary counter:

| β_E | segment cost (steps) | settled span |
|---|---|---|
| 4 | ≈ 200 (settled by step ≈ 350 from σ_re) | 63 |
| 6 | 760 | 69 |
| 12 | 49,120 | 87 |
| 16 | 786,384 | 99 |
| 24 | ≈ 2.0133×10⁸ (see §6) | 123 |

(cost ≈ 12·2^{β_E}: ratios 11.9, 12.0, 12.0 at
β_E = 6, 12, 16.) A uniform-in-β_E derivation of the
segment is open (§7, gap iii); per-β_E it is (C).

## 2. The settled regime: the I-system in the single-block frame

**Frame.** Sections are head local minima of exactly two
kinds, alternating — B with head = a, C with head = a − 2 —
for the tape form

  1^a 0^{w_0} 1^s Π_{i≥1} (0^{w_i} 1^{r_i}) 0^G 1²,

i.e. invariant I of Phase 12 with the prefix
[1¹⁷ 0 1^B2] replaced by the single block [1^a] (B2 := a),
plus the frame clauses of §4. The five rules of
Phases 13–14 apply **verbatim** (their derivations are
local to the interface; the only place the prefix enters
is the C-bounce's leftward sweep — §4).

**Canonical settled section** (the segment's output, for
β_E ≥ 6; β_E = 4 settles with residue 25 instead of 29):

  (C, a = 18, s = 2, w = [29, 1^{β_E}], r = [1, 2^{β_E−1}],
   G = 1),   span = 3β_E + 51.

Note **r₁ = 1**: the re-coordinatisation leaves exactly
one defect pair (a 1¹ run) in the stack, immediately
beneath the residue 29. The rules read pair runs only
through POP (which consumes r₁); the defect is buried
and resurfaces exactly once per era (§3).

**Classification** (consecutive section transitions;
successor state, all parameters, and cost must match the
rule exactly — `phase18_parse.py`, `phase18_stream.py`):

| window | transitions | exact | exceptions |
|---|---|---|---|
| σ_re(4), steps ≥ 350, 10⁶ steps | 83,292 | 83,291 | 1 defect POP (§3) |
| σ_re(8), steps ≥ 6000, 3×10⁵ steps | 24,525 | 24,525 | — |
| σ_re(8), steps ≥ 6000, 2×10⁸ steps | 16,666,175 | 16,666,174 | 1 defect POP (§3) |
| X(6), post-settle, 3×10⁶ steps | 249,917 | 249,915 | defect POP + REGEN |
| X(12), post-settle, 3×10⁶ steps | 245,834 | 245,832 | defect POP + REGEN |
| X(16), post-settle, 3×10⁶ steps | 184,356 | 184,354 | defect POP + REGEN |
| X(24), post-settle, 3×10⁸ steps | 8,222,633 | 8,222,631 | defect POP + REGEN |

(REGEN transitions are not classified by the five-rule
classifier — REGEN is the sixth, boundary rule of §3;
in the σ_re(4) and σ_re(8)-long windows the REGEN pair is
additionally bracketed by intra-excursion sections the
parser rejects — the merged forms 1²¹ 0 1⁴¹ and the
degenerate C-section of §3 — so it appears there as two
unparseable sections rather than a mismatch. Rule counts
are near-equal across TDN/PUSH/POP/TUP, as the phase
structure requires; Stage A counts: 15 (σ_re(4) window),
16 (X(6/12/16) windows), 22 (σ_re(8) long window).)

**Audit** (σ_re(8), 2×10⁸ steps, the largest window):
E-reads 8,333,352, all on 1; D-reads 8,333,352, all on 1;
C-on-0: 8,333,351 B-entry (1,1) + 1 F-entry (1,1);
F-on-0 triples: (1,1,1)×8,333,315, (0,1,1)×28,
(1,0,1)×8, (1,1,0)×1, **(0,1,0) = 0**. min head 2;
cells 0–1 never rewritten after the escape.

So the settled post-exit regime is component #10's system
in a second frame — status (P) for the rules (Phases
13–14), (C) for the frame identification (the table
above).

## 3. The frame's boundary events: defect POP, REGEN, Stage A, entry

Within the frame, a B-section with w = [1] is the only
way an era can end. What fires depends on G:

- **G ≥ 3 — Stage A** (Phase 14, derived (P)): cost
  2s + 6, G := G − 2, lands (C, w = [s−1]).
- **G = 2 — right-edge entry** (Phase 15 §1, derived
  (P)): the excursion is local to the right of the
  interface, hence frame-independent; re-verified in
  this frame synthetically at (a = 10, s = 6) and
  (a = 6, s = 4): cost s + 12, lands σ_re with
  **β′ = s + 2** (the block grows a → a + 1). §5.
- **G = 1 — REGEN** (new in this phase): the Stage A
  probe cannot fire inside a 1-cell gap; instead the
  excursion runs to the right end, absorbs the terminal
  pair, probes in the blank (span + 2), and carves a
  fresh long gap out of the shuttle:

  **REGEN: (B, a, s, w = [1], G = 1) →
           (C, a + 2, s = 2, w = [1], G = s − 1),
           cost 4s + 22, span + 2.**

  Verified instances: synthetic s ∈ {5, 6, 9}
  (configurations `p18-b3/b2/b8.cfg`) and trajectory
  s = 39 (σ_re(4)), 43 (X(6)), 47 (σ_re(8)), 55 (X(12)),
  63 (X(16)), 79 (X(24)) — the formula (successor
  parameters and cost) matches all nine exactly. The
  excursion passes through a degenerate C-section
  (a + 3, single gap s + 1, terminal 1²) at its midpoint,
  then a PUSH-cost redistribution lands the clean
  I-section. Status: (C) — a verified closed form on 9
  instances; a shift-rule derivation from the table is
  open (§7, gap i), the same position Stage A was in
  before Phase 14.
  (The degenerate input G = 0 — shuttle merged with the
  terminal pair, not a configuration the system itself
  produces — also rejoins the frame, landing at G = 5
  from s = 6; robustness note only.)

- **The defect POP** (once per era): when the buried
  1¹ defect resurfaces to r₁ during the era's final
  grind, one POP fires with r₁ = 1: successor
  s′ = s + 1 instead of s + 2, cost unchanged (2s + 3).
  This flips the shuttle parity; the era's remaining
  sections run with s odd until the stack empties, and
  REGEN (which lands s = 2) restores parity. Observed
  exactly once in each of the σ_re(4), X(6) and
  σ_re(8)-long eras (steps 393,442 / 393,902 / 399,054),
  in each case fully audited and with exactly this
  effect. Status (C); the one-line derivation is that
  POP's return sweep counts the merged run once, so
  s′ = s + 2 − (2 − r₁) for any r₁ — the r₁ = 2 case is
  Phase 13's POP.

**Era anatomy** (uniform across β_E; numbers for
σ_re(8)): settle (G = 1) → residue grind (≈ 3.94×10⁵
steps, nearly β_E-independent — the stack's top is the
same for all β_E) → defect POP → stack empties at
(B, a = β_E + 16, s₁, w = [1], G = 1) → **REGEN**
(G₀ := s₁ − 1) → Stage-A era: at successive empty-stack
sections s = 4, 6, 8, … and G = G₀, G₀ − 2, …, i.e.
**s + G = s₁ + 3 = const**, with intervals between
Stage A events doubling (the residue grind is the same
binary counter as everywhere else in this machine) →
at G = 2 the residue [s₁ − 2] grinds down → the first
(B, w = [1], G = 2) section fires the entry with
s = const − 2, i.e. **β′ = const = s₁ + 3**.

## 4. Frame safety clauses (the a ≥ 4 condition)

The five rules' derivations are local except the
C-bounce (TDN/PUSH), whose F-sweep runs left across the
block and turns at the first 0 it finds; in the
single-block frame that sweep reaches cell a − 4.
Synthetic boundary tests (`p18-b5/b6/b9/b10.cfg`):

- TDN at a = 5 and a = 4: **exact** (successor and cost).
- TDN at a = 3: deviates — the sweep reaches cell −1,
  writes outside the block, and the successor is not a
  section of the system.
- TDN at a = 2: deviates further — the excursion escapes
  left, writing new cells at negative coordinates.
- PUSH at a = 4 would land a C-section at a = 3 with
  w₀ = 1 (PUSH always lands w₀ = 1), i.e. TDN at a = 3:
  the compound boundary.

The frame invariant is therefore I⁺ = I (with B2 := a)
plus: **a ≥ 2 at B-sections; a ≥ 4 at C-sections; a
C-section with a = 4 has w₀ = 1** (equivalently, no PUSH
fires at a = 4). B-sections at a = 2 are fine (POP from
a = 2 observed, exact). In all classified data the
clauses hold with margin: min a over C-sections is 4
(σ_re(4): the unique a = 4 C-section has w₀ = 1;
σ_re(8)-long: min a_C = 4, attained once at step
398,530 in the grind endgame; min a_B = 2), and no PUSH
at a = 4 occurs in any window (≈ 1.7×10⁷ C-sections).
Whether I⁺ is preserved by the era dynamics in general
is part of the era-analysis gap (§7, gap ii); in the
Stage-A era it is immediate (a is pinned at
β_E + 16 / β_E + 18 there).

## 5. The reset map

Measured at every era boundary reached in this phase:

| β_E | s₁ (at REGEN) | G₀ = s₁ − 1 | era const s₁ + 3 | next entry β′ |
|---|---|---|---|---|
| 4 | 39 | 38 | 42 | 42 (projected) |
| 6 | 43 | 42 | 46 | 46 (projected) |
| 8 | 47 | 46 | 50 | 50 (projected) |
| 12 | 55 | 54 | 58 | 58 (projected) |
| 16 | 63 | 62 | 66 | 66 (projected) |
| 24 | 79 | 78 | 82 | 82 (projected) |

**s₁ = 2β_E + 31** on all six points, hence the loop
map **β′ = 2β_E + 34**. ("Projected": the entry at the
end of the era is covered by the (P) entry derivation
and its synthetic verification in this frame, and
σ_re(8)'s long run reaches G = 2 at step 101,063,082
with the final grind in progress at the window's end —
but no trajectory in this phase was run through the
in-frame entry itself, because after G = 2 the grind of
residue 45 takes ≳ 10⁸ further steps.) The map is
strictly increasing (β′ ≥ β_E + 38 for β_E ≥ 4), and
the settled span 3β_E + 51 increases with it; within a
loop, span also grows by 2 at REGEN and by 2 in each of
the β′ − 2 right-edge cycles before the next exit
(Phase 17). **No configuration of the loop can repeat.**
Status: the map is (C) on six points; deriving
s₁ = 2β_E + 31 from the grind is §7, gap ii.

## 6. β_E = 24

X(24) was run for 3×10⁸ steps (`p18-x24-long.log`;
24,999,849 sections; audit clean: E-reads 12,499,921
all on 1, D-on-0 = 0, F-on-0 danger (0,1,0) = 0;
min head 2). The segment's two nested counter descents
are visible in the old-interface parse (a gap burning
47 → 1 with doubling intervals, steps 1,268 →
100,664,461, then a second descent of ≈ 1.007×10⁸
steps): settlement at ≈ step 2.0133×10⁸ (inferred:
REGEN step minus the era grind ≈ 3.95×10⁵ steps),
span 123, settled form as in §2 (mid-grind sections
show the defect pair buried in the stack). Post-settle
classification (`phase18_stream.py` over steps
≥ 2.01×10⁸): **8,222,631 transitions exact, exceptions
exactly the era's defect POP and REGEN**. The era then
ran as predicted by §5 in every particular: REGEN at
s₁ = **79 = 2·24 + 31** (destination section at step
201,722,658 with G₀ = 78, cost 338 = 4·79 + 22, REGEN
source a = 40 = β_E + 16), span 123 → 125, and a
Stage-A era with s + G = 82 constant (21 Stage A events
in the window, G: 78 → 36, intervals doubling). Min a
over C-sections 4 (step 201,719,130, grind endgame),
over B-sections 2 — I⁺ held throughout.

## 7. What remains open (exact list)

i. **REGEN derivation.** The (B, w = [1], G = 1)
   excursion in shift rules, uniform in (a, s) — the
   formula is verified on 9 instances (s ∈ {5, 6, 9,
   39, 43, 47, 55, 63, 79}). Same status as Stage A before
   Phase 14; no new dynamics involved.
ii. **Era closed form.** Evaluating the five-rule grind
   of the canonical stack [29, 1^{β_E}] (defect at r₁)
   in closed form: that it empties the stack exactly
   once through the defect POP, lands REGEN at
   s₁ = 2β_E + 31, and preserves I⁺ (§4) throughout.
   This is a pushdown-counter evaluation of the same
   kind as the S′ phase-2 proof (Phases 5–8). Also the
   odd-G sub-case: a REGEN with s₁ even would give
   G₀ odd and a Stage-A era ending at G = 1 in another
   REGEN; it does not arise from the canonical stack
   (s₁ is odd there, via the defect), but a complete
   treatment should either derive that or rule the
   sub-case out.
iii. **Re-coordinatisation, uniform in β_E.** The
   segment X(β_E) → canonical section is (C) per
   β_E ∈ {4, 6, 8, 12, 16, 24}; a uniform derivation
   (mini-regime + token walk + escape, cost
   ≈ 12·2^{β_E}) is open. The segment is finite for
   each β_E and every instance is audited; β_E itself
   is not pinned down on the real trajectory (it equals
   s_entry + 2 for the standard regime's exit section),
   so the uniform version is what a complete proof
   needs.
iv. Nothing else. In particular the continuation
   contains **no analogue of the β proviso**: every
   boundary of every frame in the loop has been
   reached and classified in this phase (G ∈ {1, 2,
   ≥ 3}; r₁ ∈ {1, 2}; a at its floor), and the loop's
   parameter map is strictly increasing.

## 8. Files

- `phase18_parse.py` — section parser + five-rule
  classifier for the single-block frame.
- `phase18_stream.py` — O(1)-memory streaming version
  for the 2.4 GB long log.
- Logs: `p18-sre4-rsec.log` (10⁶ steps from σ_re(4)),
  `p18-sre6-rsec.log` (10⁵ from σ_re(6)),
  `p18-sre8-rsec.log` (3×10⁵ from σ_re(8)),
  `p18-sre8-long.log` (2×10⁸ from σ_re(8)),
  `p18-x{6,12,16,24}-rsec.log` (3×10⁶ from X(β_E)),
  `p18-x24-long.log` (3×10⁸ from X(24)),
  `p18-sre8-stream.out`, `p18-x24-stream.out`,
  `p18-x24-stream2.out` (stream analysis totals).
- Configs: `p18-x{6,12,16,24}.cfg` (exit successors),
  `p18-b{1..10}.cfg` (boundary synthetics: entry at
  G = 2 (b1, b7), REGEN at s = 5, 6, 9 (b3, b2, b8),
  G = 0 degenerate (b4), TDN at a = 2, 3, 4, 5
  (b5, b6, b9, b10)).
- The background phase10 run was not disturbed.
  Nothing has been posted externally.
