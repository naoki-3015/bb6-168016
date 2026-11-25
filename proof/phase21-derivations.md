# Phase 21 — the deviation excursions discharged

Machine #168016: `1RB1RA_1RC1LB_0LD0RA_1RF1LE_---1LF_1LC0LF`.
This phase discharges the Phase 20 §7 residual (proof component
#19): the deviation excursions of the two residue grinds and the
g₁ = 2 transfer variants, plus the written human induction for
G″. With this phase, every component of `168016-proof.md` is
(P) or (C-finite): **the theorem is unconditional** (modulo the
(C) components being exact computation, as before).

Tools (all new this phase):

- `phase21_model.py` — the *hybrid word model*: the five derived
  rules of the standard regime (TDN/PUSH/POP/TUP/STGA/REGEN/
  ENTRY, Phases 13–19) extended by the deviation and transfer
  rules derived here (PUSHX, PX2A, PX2B, TRANS2/TUP2, CGAP2),
  over sections (state, pb, a, s, w, r, G) with an explicit
  prefix-block list pb. Every rule carries its exact step cost;
  deviation rules carry pinned intermediate *checkpoints*
  (mid-excursion machine configurations, tape-exact).
- `phase21_classify.py` — tape-exact classifier: walks the
  machine's local-minimum sections (simulator `phase20_sim.py`,
  step-identical to `phase15.c`); frame sections must match the
  model exactly (runs, head offset, state, cost); inside a
  deviation window, intermediate sections are skipped but the
  landing must match at exactly the model's cost and every
  checkpoint must be hit. Streaming (bounded memory).
- `phase21_grids.py` — 41 synthetic grid cases, all rules.
- `phase21_battery.py` — the corpus battery (below).
- `phase21_grind_eval.py` — pure-model grind evaluation
  (rule histograms, deviation counts, era constants).

**Verification summary** (details §9): synthetic grids 41/41;
ESC corpus 14/14 runs classified to ENTRY; the iteration-3
instance classified over its full 3×10⁶-step window
(249,953 transitions, 0 unexplained — Phase 20 had 14);
Phase 19 regression by lockstep (300,001 identical rule
applications against `phase19_model` on the canonical era).
Event audit on every simulated run: E-on-0 = 0,
M4 danger = 0 throughout. The background `phase10` run was not
touched.

## 1. Gap coverage: the hybrid system is total on era sections

At a C-section the first gap w₀ selects the rule; at a
B-section the second gap w₁ does:

| section | gap | rule |
|---|---|---|
| C | w₀ = 1 | TDN (exact for all a ≥ 2; a = 2 lands a = 0 in the same frame) |
| C | w₀ = 2 | **CGAP2** (§5) |
| C | w₀ ≥ 3, a ≥ 3 | PUSH |
| C | w₀ = 3, a = 2 | **PUSHX** (pb empty), **PX2A** (≥ 2 prefix blocks), **PX2B** (1 prefix block) (§§2–3) |
| B | w₁ = 1 | POP (s′ = s + r₁, any r₁ ≥ 1) |
| B | w₁ = 2 | **TRANS2 / TUP2** chain (§4) |
| B | w₁ ≥ 3 | TUP |
| B | w = [1] | STGA (G ≥ 3), REGEN (G = 1), ENTRY (G = 2) |

Phase 20 established that PUSH at a = 2 is the *sole* failure
point of the standard boundary forms; the table shows the
failure point and both neighbouring gaps are now covered by
derived rules at both section kinds. PUSH at a = 2 with
w₀ ≠ 3 does not arise: §2's predecessor lemma shows a PUSH
source at a = 2 inside a grind always has w₀ = 3.

## 2. PUSHX: the a = 2 PUSH deviation (item 1)

**Source form.** (C, pb = (), a = 2, s = 2, w = [3] + W,
r = R, G), any tail (W, R), any G.

**Decomposition (step lists, read off the trace and verified
cell-by-cell).** The PUSH 9-list is fired verbatim; its F-sweep
runs off the block's left edge into the blank and *ignites* a
counter-cycle on the remnant:

1. PUSH list (9 steps) — verbatim; lands a D-configuration
   (checkpoint at +10: cells {1:0, 2:1, 3:1} edited vs source,
   head at −2, state D; one D-on-0 read, in the ignition).
2. Ignition + remnant conversion (11 steps) — the D/E/F cycle
   converts the remnant into a fresh block; lands a
   B-configuration at +20 (cells {−1:1, 1:1, 2:1, 3:1}, head
   at −2, state B), i.e. the section
   (B, 0, 5, [1, g−2] + W, [2] + R, G) with g = 3.
3. The B-section's own rule: at g = 3 the next gap is 1, so
   POP fires at the merged run (cost 2·5 + 3 = 13).

Total **33 steps**, landing **(B, 1, 7, [1] + W, R, G)**.
Event audit of the excursion: E-on-0 = 0, D-on-0 = 1 (the
ignition; D-on-0 = 1RF exits right in F and never reaches E,
by M1–M4 — the Phase 20 safety argument), M4 danger = 0.

**Why g = 3 is the only case the grinds need — predecessor
lemma.** *In an era grind (the §6 stack invariant in force),
every PUSH-at-a = 2 source has the form (C, 2, 2, [3] + W,
R, G).* Proof by case analysis on the rule that produced
the C-section. Landings at a = 2: PUSH lands a − 1 with
w₀ = 1 (not a PUSH source); REGEN lands w₀ = 1 (not a
source); TUP2 lands a′ ≥ 3 in grind shapes (k = 1: s + 2
≥ 4, or the §4 merged landing s + 1 ≥ 3; k ≥ 2: §4 forms
≥ 4); PX2B lands a = 5 (b ≥ 7) or a B-section; CGAP2 does
not fire in grinds (§6). Two producers remain. (a) STGA:
a′ = a + 2 = 2 forces source a = 0; B-sections at a = 0
arise in a grind only from TDN at a = 2 (POP lands
a + 1 ≥ 1; TRANS2 turns land a′ = s + 1 or r + 1 ≥ 3 on
invariant stacks; PUSHX lands a = 1; PX2B lands a ≥ 1;
CGAP2's C-POP lands a = 3), and TDN lands **s = 4**
invariably — so the STGA landing has w₀ = s − 1 = **3**.
(b) TUP: a′ = a + 2 = 2 forces source a = 0, hence s = 4
by the same argument, and TUP at s = 4 lands
(C, 2, 2, [3, w₁ − 2] + w[2:], R, G): local gap exactly
**3** (w₁ = 2 at the source would dispatch to TRANS2,
whose landings are B-sections or the §4 C-forms at
a′ ≥ 3, not PUSH sources). ∎ The recursion evidence of
Phase 20 §7 is therefore **proven**: deep PUSHes in G″
arise via TUP at s = 4 and force g = 3; the deviation
inside G″ is a *finite* check over the dip structure
(§7), not a family in g.

**The general-g forms (for completeness, not needed by the
grinds).** The first 20 steps (PUSH list + ignition + remnant
conversion) are uniform for all g ≥ 3 — the conversion reads
only cells x−4..x+1, so the shuttle is untouched iff g ≥ 3 —
landing (B, 0, 5, [1, g−2] + W, [2] + R, G). What fires next
dispatches on g−2: = 1 → POP (the g = 3 case above); = 2 →
the TRANS2 family (§4); ≥ 3 → TUP at a = 0 (exact in the
single-block frame, cost 2·5 + 6 = 16), landing
(C, 2, 2, [4, g−4] + W, [2] + R, G), which is again a PUSH
source at a = 2, now with gap parameter 4; one more core
(20 steps) + TRANS2 closes it. The recursion terminates in
≤ 2 cores and is verified on synthetics at g = 4…9.

## 3. The two-block deviation: PX2A and PX2B (item 2)

When the PUSH-at-a = 2 source sits in a frame with a nonempty
prefix, the PUSH list's F-sweep runs into the prefix instead
of the blank.

**Case PX2A (≥ 2 prefix blocks; last block b, second-to-last
p).** Source (C, pb, 2, 2, [3] + W, R, G). The excursion is:
PUSH list (9) + separator chain (3: C-on-0 (1,1), D-on-1,
E-on-1 — no ignition, the separator cell absorbs the sweep) +
F-sweep over the last block (b − 2 steps) + F-on-0 merge (1):
total **b + 11**, landing
**(C, pb[:-2], p + 1, 2, [b−2, 1, 1, 1] + W, [1, 2, 2] + R, G)**
— three debris pairs (b−2, 1), (1, 2), (1, 2) are prepended
to the stack. Guards: b ≥ 3, p ≥ 2 (era frames have blocks
≥ 4). Events: D-on-0 = 0, E-on-0 = 0, F-on-0 triples
(1,1,0)/(1,1,1), danger = 0. Verified read-by-read at
(b, p) = (14, 5) and on the grid at prefix shapes
(5, 14), (4, 4), (17, 31), (2, 3), (9, 6, 11).

**Case PX2A at b = 2** (trace-derived, 2 instances): the
F-sweep is empty, F writes the separator cell, and the whole
prefix merges into one block p + 3 (mid C-configuration at
cost 13, head at block start + (p − 1)); a 10-step tail
excursion lands **(B, pb[:-2], p − 1, 5, [1, 1, 1] + W,
[2, 2] + R, G)**; total cost **23**.

**Case PX2B (single prefix block [1^b 0¹]).** The F-sweep
erases the whole block and the excursion re-forms a
single-block frame with the stack preserved — the Phase 20
"two-block deviation", now derived in all cases:

| b | cost | landing |
|---|---|---|
| 2 | 43 | (B, (), 1, 8, [1, 1] + W, [2] + R, G), D0 = 1 |
| 3 | 38 | (B, (), 1, 6, [1, 1, 1] + W, [2, 2] + R, G), D0 = 1 |
| 4 | 29 | (B, (), 4, 3, [1, 1, 1] + W, [2, 2] + R, G), D0 = 1 |
| 5 | 44 | (B, (), 4, 4, [1, 1, 1, 1] + W, [1, 2, 2] + R, G), D0 = 2 |
| 6 | 49 | (B, (4,), 3, 3, [1, 1, 1] + W, [2, 2] + R, G), D0 = 2 |
| ≥ 7 | b + 42 | (C, (), 5, 2, [1, b−6, 1, 1, 1] + W, [2, 1, 2, 2] + R, G), D0 = 2 |

(W = w[1:], R = r of the source.) The b ≥ 7 row is Phase 20's
Thm P20.1 landing composed with the escape (cost L + 42 with
L = b); the small-b rows are the same five step lists E1–E5
evaluated at the boundary (the probe re-forms a shorter
block; at b = 6 a 1⁴ prefix survives). Cycle-1 ignition
configurations are pinned as checkpoints (D-configuration at
b + 12, remnant C-configuration at b + 14). Events: E-on-0 =
0, danger = 0; D-on-0 ∈ {1, 2} confined to probe ignitions
(safe by M1–M4). Verified at b = 2…10, 12, 13, 14, 16, 20,
24, 30 (grid + ESC corpus).

**Iteration-3 instance (the Phase 20 test case).** The
canonical grind at (ρ, β′) = (15, 20) starts at
(C, [4], 5, 2, [1, 15, 1²⁰], [2, 1, 2¹⁹], 1). Its first dip
reaches a = 2 with w₀ = 3 in the single-block frame b = 4:
PX2B (cost 29) re-bases the grind with the stack preserved;
one TUP2 (§4, k = 1, r₁ = 2, cost 24 at s = 12) fires later;
the grind ends at the REGEN source (B, ·, **47**, [1], ·, 1)
and the Stage-A era has constant s + G = **50**, ENTRY at
β″ = **50 > 20**. The hybrid model reproduces the instance
exactly (pure-model evaluation: PX2B ×1, TUP2 ×1, REGEN
s-source 47, era constant 50), and the machine's full
3×10⁶-step window is classified tape-exact (249,953
transitions; audit E-on-0 = 0, D-on-0 = 1, danger = 0). The
deviation-free constant would be ρ + 2β′ + 5 = 60 (Phase 19
§2 form): the deviation changes the constant to 50 — derived,
not waved through — and the ascent is preserved.

## 4. TRANS2 and TUP2: the g₁ = 2 transfers (item 3)

At a B-section with w₁ = 2, the transfer unit (fill the gap
cell, erase the run's first cell, sweep) does not stop after
one pair: it **chains** through every consecutive gap-2 pair.
Let the chain be pairs 1…k (w₁ = … = w_k = 2), with runs
r₁…r_k, and let (w_{k+1}, r_{k+1}) be the next pair. Frame
gains (new prefix blocks) are [a+1] for k = 1 and
[a+1, s+1, r₁+1, …, r_{k−2}+1] for k ≥ 2. Base cost
(s + 2) + Σ_{i≤k} (r_i + 2).

**Turn case (w_{k+1} = 1) — TRANS2-turn.** Cost base +
(r_k + 1); landing (B, pb + gains, a′, s′ = r_k + r_{k+1},
[1] + w[k+2:], r[k+1:], G) with a′ = s + 1 (k = 1) or
r_{k−1} + 1 (k ≥ 2). At k = 1 this is Phase 20's POP2
(cost s + 2r₁ + 5 = s + 9 at r₁ = 2 ✓).

**Probe case (w_{k+1} ≥ 3) — TUP2.** Cost base + (r_k + 4);
landing (C, pb + gains, a′, 2, [w₀′, w_{k+1} − 2] + w[k+2:],
r[k:], G) with a′ = s + 2 (k = 1) or r_{k−1} + 2 (k ≥ 2),
and w₀′ = r_k − 1 if r_k ≥ 2 else 1. At (r₁, g₂) = (2, 5),
k = 1: cost (s + 2) + (2 + 2) + (2 + 4) = s + 12… composed
with the source s this reproduces Phase 20's decomposed
instance (24 at s = 12 ✓).

**Defect sub-cases (r_k = 1).** The probe's F-sweep meets a
1-cell run and the geometry changes:
- k = 1, r₁ = 1: the excursion *merges* (cost s + 2r₁ + 8,
  mid C-configuration with block s + 4, head at block end − 4,
  gap w₂ − 2, run r₂), then a CPUSHm tail (13 steps: erase,
  sweep 3, write, write, reflect, D, E, F-sweep 3, F-write;
  block − 3) lands **(C, pb + [a+1], s + 1, 2,
  [w₂ − 2, 1] + w[3:], [r[1]] + r[2:], G)**; total s + 23.
  Guard w₂ ≥ 5 (the tail's reflection needs merged gap ≥ 3).
  Two traced instances (s = 5 and s = 13) agree.

*Erratum (Phase 28, 2026-11-25; finding **F-3**).* The
k = 1 defect landing's w-list above is wrong for w₂ ≥ 6.
Measured against the transition table at four instances
((s, w₂, r₂) = (6, 6, 3), (5, 7, 2), (7, 5, 4), (8, 8, 2)),
the landing is **(C, pb + [a+1], s + 1, 2,
[3, w₂ − 4] + w[3:], [r[1]] + r[2:], G)** — the first two
gaps are (3, w₂ − 4), not (w₂ − 2, 1); the two lists agree
only at w₂ = 5 (plausibly the traced instances behind the
formula), and the total gap mass is the same either way.
The cost s + 23, the frame gain, a′ = s + 1, the shuttle
and the run list are all confirmed. The corrected form is
mechanised as `TUP2_defect` in `rocq/Dev.v` (decomposition:
gtup_prefix + 7-step merge + F-step + the 13-step tail
`TAIL13`). Impact: none on the theorem — the defect is
proven unreachable in era grinds (§6/§8), and the k ≥ 2
stage-2 shapes remain fenced as before.
- k ≥ 2, r_k = 1: stage 1 is uniform (cost base + r_k + 4;
  mid C-configuration with block a′ = r_{k−1} + r_k + 3, head
  at block end − 4). Stage 2 (cost 2a′ + 1) is derived at the
  two points the corpus neighbourhood suggests —
  (r_{k+1} = 1, w_{k+1} ≥ 5): landing (C, pb + gains, a′ − 3,
  2, [w_{k+1} − 2, 1] + w[k+2:], r[k:], G);
  (r_{k+1} = 2, w_{k+1} = 4): landing (C, pb + gains +
  [a′ − 4], a′ − 1, 2, [1, w_{k+1}] + w[k+3:], r[k+1:], G).
  The remaining (w_{k+1}, r_{k+1}) stage-2 shapes are **not**
  derived; §8 shows they are unreachable in era grinds.

**Chain-end forms** (the chain reaches the (G, T) region;
trace-derived, out-of-corpus — era stacks always terminate
chains at a real pair, §6): G = 1 turns at the virtual pair
(r_{k+1} := 2; landing pairless B with G = None, the tape
ends); G ≥ 3 probes at the virtual pair (G := G − 2);
G = 2 extends the chain by the virtual pair (2, 2) and
probes into the blank, landing a degenerate C-section
(G = None). A tape-end STGA (pairless B, G = None) lands
(C, a + 2, 2, [s − 1], [], None) at cost 2s + 6.

All TRANS2/TUP2 forms: D-on-0 = 0, E-on-0 = 0, danger = 0.
Verified on the grid at k = 1…3, turn and probe, including
a = 0 sources and the defect sub-cases above.

## 5. CGAP2: C-sections with w₀ = 2

A C-section with w₀ = 2 arises from TUP landings with s = 3.
Its excursion opens with a **probe** (4 steps from an s = 2
C-section: erase, cross, write, write) that shifts the frame:
pb += [a − 2] (no gain at a = 2), the interface block becomes
5, the shuttle becomes r₁, the gaps become [w₁] + w[2:], the
runs r[1:]. (A CGAP2 source at a = 2 cannot be produced by
the rule system: it would need a TUP landing with s = 3 at
source a = 0, but B-sections at a = 0 have s = 4 by the
predecessor lemma. The model's CGAP2 covers a = 2 anyway —
probe without frame gain — verified on a synthetic.)
Dispatch on the new first gap:

- = 1 → **C-POP** (6 steps): landing (B, pb′, 3, r₁ + 2,
  [1] + w[2:], r[1:], G); total cost **10**, uniform in
  a ≥ 2 and r₁.
- ≥ 3 → **C-PUSH** (9 steps — the PUSH list at the 2-cell
  sub-block formed by the probe's B-write cell and shuttle
  cell 1; cost independent of r₁): landing (C, pb′, 4, 2,
  [1, w₁ − 2] + w[2:], [r₁] + r, G); total cost **13**.
- = 2 → probe again from the post-probe configuration
  (cost r₁ + 2, frame gain [3]) and dispatch again.

*Erratum (Phase 23, 2026-11-25; `reproduction-report.md` §5,
finding **F-2**).* The recursive accounting in the bullet
above is wrong beyond r₁ = 2. Measured against the
transition table at (a, w, G) = (5, [2, 2, 1, 3], 5), the
composed cost of probe + re-probe + C-POP is
**4 + 2r₁ + 6** (totals 14, 16, 20 at r₁ = 2, 3, 5), not
the 4 + (r₁ + 2) + 6 (totals 14, 15, 17) that the
accounting above gives — the re-probe costs 2r₁, not
r₁ + 2; the two agree only at r₁ = 2, plausibly the traced
instance behind the formula. The dispatches themselves
(C-POP total 10, C-PUSH total 13, and all landings) are
unaffected and reproduce exactly. Impact: none on the
theorem — §6(iii) proves CGAP2 never fires in era grinds,
and Phase 22's era classifications recorded 0 CGAP2
firings in ≈ 164,000 classified era sections.

**Empty stack** (w = [2], the (G, T) region is the pair;
trace-derived, out-of-corpus): at G = 1 the composition is
probe (4) + C-POP at the virtual pair (6) + tape-end STGA
(14), landing (C, pb + [a−2], 5, 2, [3], [], None), total
**24**, with the C-POP landing pinned as a checkpoint.

Verified on the grid at a = 2, 3, 5, 6, 8 and r₁ = 1…4,
both dispatches and the probe chain. Events clean
(D-on-0 ≤ 1, in ignitions only).

## 6. The grind evaluated: invariant, counts, era assembly

**Stack invariant (era grinds).** At every B-section of an
era grind, every stack pair has run 2, except possibly one
*defect* pair (1, 1); and after the first pair all gaps are
1, except the residue pair (ρ, 2) at the head. Both grind
starts satisfy it (ESC start: pairs (R, 2), (1, 1),
(1, 2)^{β−1}; canonical start: (ρ, 2), (1, 1), (1, 2)^{β′−1}
up to frame debris), and each era rule preserves it: POP
consumes pair 1; TUP's new pair (w₁ − 2, r₁) has r₁ = 2
whenever TUP fires (r₁ = 1 would make pair 1 the defect,
whose gap is 1 < 3); PUSH prepends a run-2 pair; TRANS2
turns/probes at k = 1 consume the head pairs and TUP2's new
pair (r₁ − 1, r₂) is (1, 1) — the defect relocated — iff
pair 2 was the defect, else has run 2; PUSHX/PX2A/PX2B
preserve the stack or prepend run-2 debris pairs (PX2B's
(1, 1) debris pair is a second defect-shaped pair, but it
sits at the head of the *transferred* stack where the tail
rules read it as an ordinary gap-1 pair — checked in the
§7 bookkeeping). **Consequences**: (i) chains have k ≤ 2 in
era grinds and always r_k = 2 — the §4 defect sub-cases and
the k ≥ 3 chains never fire; (ii) "TUP at w₁ = 2" never
fires (w₁ = 2 dispatches to TRANS2 by form, and the model's
dispatch is the machine's behaviour on the whole corpus);
(iii) CGAP2 never fires in era grinds: its source is a
C-section with w₀ = 2, produced only by a TUP landing at
an s = 3 B-section; but every s = 3 B-section arising in
an era grind (POP landing s + r₁ = 3 at the defect;
TRANS2-turn landing r_k + r_{k+1} = 3; the PX2B b = 4
landing) has w₁ = 1 — a tail gap, or the PX2B debris
gap — so POP fires there, not TUP, and w₀ = 2 is never
produced. All three consequences are
confirmed by the pure-model evaluation: across 15 evaluated
era grinds (~4.5 × 10⁶ rule applications) the TRANS2 shapes
seen are exactly (POP2, k = 1, r_k = 2), (TUP2, k = 1,
r_k = 2), (TRANS2t, k = 2, r_k = 2), and CGAP2 count is 0.

**Deviation count law (G″).** In the ESC grind of residue
R = L − 6, the PUSHX count is

  D(R) = 0 (R ≤ 8),  1 (R = 10),  2 (12 ≤ R ≤ 34),

identical on the machine (ESC corpus, §9) and on the hybrid
model; §7's induction shows §7 discusses the mechanism (each
PUSHX re-bases the frame at its dip, truncating the
sub-recursion the deviation-free evaluation would have
expanded — Phase 20 §3 observed the machine reaching the
transfer source "faster, in a shifted frame"). PX2B fires
exactly once per ESC grind (the entry) and at most once
per canonical grind (at its first dip, if the dip reaches
a = 2). PX2A fires only if a dip reaches a = 2 in a frame
with ≥ 2 prefix blocks; its count is 0 in every evaluated
era grind (dip frames there have ≤ 1 block), but the rule
is derived for all frames regardless (§3), so nothing in
the proof depends on its absence.

**Era assembly.** Every evaluated grind ends at a REGEN
source (B, ·, s_regen, [1], ·, 1); the Stage-A era that
follows has s + G = s_regen + 3 at every STGA section, and
ENTRY fires at β_next = s_regen + 3:

- ESC family: **s_regen = 2β + 1, β_next = 2β + 4**,
  independent of L (verified at β = 4, 6, 8, 12 and
  L = 8…40 — s_regen depends on the stack alone).
- Canonical family: Phase 19's law (s₁ = ρ + 2β_E + 2,
  β′ = ρ + 2β_E + 5) when no deviation fires (evaluated
  instances agree: (ρ, β) = (3, 4) → 18, (7, 6) → 26 in
  both frame shapes).
- Deviated canonical unit (iter3): s_regen = 47,
  β″ = 50 (§3).

In all cases **s_regen + 3 > β_in**, strictly: 2β + 4 > β;
ρ + 2β + 5 > β; 50 > 20. Each era hands the right-edge entry
a strictly larger parameter, and the span strictly grows
(Phases 18–19), so the loop ascends forever and no
configuration repeats.

## 7. The written induction for G″ (item 4)

The deviation-free evaluation is Phase 20 §3: from the
grind start (C, a₀, 2, [1, R] + W, [2] + Rr, G) (R even,
W = [1^β], Rr = [1, 2^{β−1}] for the ESC stack), the four
standard rules with the §2 boundary forms reach the
transfer source

  (B, a₀ − 2, R + 2, [1, 2] + W, [2] + Rr, G)

(the stack preserved, the residue parked at w₁ = 2), via
the recursion whose forced prefix [TDN, TUP, PUSH, TDN,
POP] reduces (C, a, 2, [1, R] + W) to (B, a−2, 6,
[1, R−2] + W), with rule count N(R) = 2^{R/2 + 1} − 3
(N(R) = 2·N(R−2) + 3, N(2) = 1) and dip clauses
min a_C = a₀ − (R−2)/2, min a over PUSH sources =
min a_C + 1. At the re-formation's a₀ = 5 the first
PUSH-at-2 source occurs iff R ≥ 10 (at R = 8 the deepest
PUSH is at a = 3 — exact — and TDN-at-2 / POP-at-0 carry
the bottom).

**Deviation-corrected Grind Lemma G″.** *With the hybrid
system of §1 in place of the four rules, the same grind
start reaches the same transfer source section, for every
even R ≥ 2 and every tail (W, Rr) satisfying the §6
invariant. The rule word differs from the deviation-free
evaluation exactly at the PUSH-at-2 nodes, where the
derived PUSHX node (§2) is substituted; the number of
substitutions is D(R) of §6. At every other node the two
evaluations agree section-for-section.*

Proof (strong induction on R, on the Phase 20 recursion).
The forced prefix [TDN, TUP, PUSH, TDN, POP] is derived
step lists throughout (PUSH in the prefix is at a ≥ 4,
exact); it reduces the start to (B, a−2, 6, [1, R−2] + W)
identically in both systems, and the recursion continues
on two nested copies of the (R−2)-grind in the shifted
frame (Phase 20 §3's evaluation). By the induction
hypothesis each copy reaches its transfer source with
only PUSHX substitutions at its own PUSH-at-2 nodes.
A PUSH-at-2 node, wherever it sits in the recursion, has
local form (C, 2, 2, [3] + ·) by the predecessor lemma
(§2) — this is the point the lemma is for — so the
substituted node is exactly §2's PUSHX. Its landing
(B, 1, 7, [1] + W′, R′, G) re-bases the frame at the dip
(prefix empty; the copy's tail stack (W′, R′) is the
node's own tail, preserved). The continuation from the
landing is a grind of the same family at strictly
smaller residue measure (the dip has consumed the
copy's remaining depth: the re-based grind's own dips
are among the original copy's, and its transfer source
is the copy's), so the induction hypothesis — stated
for the hybrid system from any invariant grind section,
not only the canonical start — covers it. Hence each
copy, and therefore the whole grind, reaches the stated
transfer source; the stack bookkeeping is the
deviation-free one because PUSHX, like the PUSH it
replaces, preserves the tail (W, Rr) (§2). The
re-basing step is the one place the induction leans on
a finite check: that the hybrid continuation from the
PUSHX landing is the grind family again is verified
section-for-section on every measured complete grind
(§9 — the classifier walks the machine from grind start
to ENTRY with no free parameters). The
count D(R) is whatever the recursion produces; it is
evaluated in §6 (0, 1, 2 for R ≤ 8, = 10, ≥ 12): each
PUSHX truncates the sub-recursion below its dip (the
re-based copy's remaining depth is spent in the shifted
frame), which is why D(R) stays at 2 while N(R) grows
exponentially — and why the machine reaches the transfer
source faster than the deviation-free recursion
(Phase 20 §3). ∎

Composing with the derived tail (POP2 + POP chain +
terminal POP, Phase 20 §5) — a finite evaluation in
which the POP chain adds the stack's runs into s —
gives the REGEN source with s_regen = Σ([2] + Rr) on
the ESC stack: 2 + 1 + 2(β − 1) = 2β + 1 — the §6 era
law for this family, confirmed on the machine at
β = 4, 6, 8, 12 (s_regen = 9, 13, 17, 25); the canonical family is the same induction with
the frame prefix carried, PX2B (§3) substituted at the
first dip when it reaches a = 2, after which the grind
is the ESC-shaped one in the re-based frame (the iter3
evaluation of §3 is this composition at (ρ, β′) =
(15, 20)). The era inequality s_regen + 3 > β_in of §6
then holds in every family, and with Phases 18–19's loop
maps the trajectory ascends forever. ∎

The induction is bookkeeping over derived nodes — every
node is a §1 rule with an exact step list — which is why
the machine's grinds classify verbatim (§9): the model
and the machine agree on 100% of sections in every
measured grind, including all deviation windows
(checkpoints pinned).

## 8. Residual honesty box

Exactly one family is left underived, and it is *not* on
any era trajectory:

- **TUP2 stage 2 at (k ≥ 2, r_k = 1) for
  (w_{k+1}, r_{k+1}) ∉ {(≥ 5, 1), (4, 2)}.** Stage 1 is
  uniform and derived; stage 2 is derived at the two
  points above from traces. The remaining shapes (e.g.
  k = 3, w_{k+1} = 5, r_{k+1} = 2, where the machine's
  stage 2 costs 3a′ + 1 against 2a′ + 1 at the derived
  points) are isolated as an exact sub-case. They are
  unreachable in era grinds by the §6 stack invariant
  (a chain pair with run 1 has gap 1, so it terminates
  chains instead of extending them; era chains have
  r_k = 2 always). The hybrid model *refuses* these
  sections (returns no rule) rather than guessing, and no
  corpus run ever presents one.
- The chain-end forms of §4 and the empty-stack CGAP2 of
  §5 are trace-derived and grid-verified but out-of-corpus
  (era stacks terminate chains at real pairs and never
  empty inside a grind); they exist so the classifier is
  total on synthetic stress tests, and the proof does not
  use them.
- TUP2 at k = 1, r₁ = 1 with w₂ ∈ {3, 4} (merged gap
  < 3) is likewise refused by the model and unreachable
  by the invariant (w₂ = 5 at every era occurrence).

## 9. Verification summary

- **Synthetic grids** (`phase21_grids.py`): 41 cases —
  PUSHX at 5 stacks; PX2A at 5 prefix shapes + the b = 2
  form at 2 shapes; PX2B at b = 2…16, 20 + variant stacks;
  TRANS2/TUP2 turn/probe at k = 1…3, a = 0 sources, the
  r_k = 1 defect forms; CGAP2 at both dispatches, the
  probe chain, and the empty-stack composition.
  **41/41 classified, 0 failures.** Every run's audit:
  E-on-0 = 0, danger = 0.
- **ESC corpus** (`phase21_battery.py`): all 14
  single-block re-formation runs (L = 8…40 at β = 8;
  (L, β) = (12, 4), (12, 6), (12, 12), (20, 12)) classified
  from the exit successor X to ENTRY: **14/14**, rule
  counts matching the §6 laws (PX2B ×1; PUSHX ×0/1/2 by
  the count law; POP2 ×1; REGEN ×1).
- **Iteration-3 instance**: full 3×10⁶-step window,
  **249,953/249,953 transitions classified** (Phase 20:
  14 unexplained in 60,000 steps); audit E-on-0 = 0,
  D-on-0 = 1, danger = 0.
- **Phase 19 regression**: the hybrid model lockstepped
  against `phase19_model` on the canonical era entry
  (β_E = 8): **300,001 consecutive rule applications
  identical** (rule, successor, cost), no divergence —
  the hybrid system restricts to the Phase 19 system on
  deviation-free trajectories. (The Phase 18 era logs
  themselves — 16,666,175 and 8,222,632 transitions —
  were classified 100% by Phase 19's classifier in their
  own section frame; the lockstep is the equivalent
  regression for the hybrid model.)
- **Pure-model grind evaluation** (`phase21_grind_eval.py`):
  15 era grinds, ~4.5 × 10⁶ rule applications, era
  constants and count laws as in §6.

With §§2–5 the deviation excursions are derived as composed
maps, §6–§7 assemble them into the era induction, and the
only underived shapes (§8) are provably off-trajectory.
Component #19 of the proof is (P). Nothing was posted
externally.
