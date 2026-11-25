# BB(6) holdout #168016 — the post-R invariant hunt (Phase 12, 2026-11-25)

- Seed index: **168016**
- Spec: `1RB1RA_1RC1LB_0LD0RA_1RF1LE_---1LF_1LC0LF`
- Starting point: Phase 11 (`transient-analysis.md`) characterised
  the post-R regime as a deterministic one-stack pushdown process
  at bounce sections, with a collapse ratchet G := G − 2 and
  regeneration at G ≤ 2, and identified the missing proof core:
  a **global invariant, valid across all three regimes, that
  state E never reads 0**. This phase hunts for that invariant
  at the section level.

**Verdict up front.** The hunt produces three things: (i) a set
of *proven* micro-lemmas reducing the halt to one exact tape
pattern (§1); (ii) a *total, invariant-preserving rewrite system*
for the section dynamics, extracted exactly and verified on
≈ 2.0×10⁶ consecutive section transitions in three independent
windows — the section invariant **I** (all gaps odd, shuttle
even, rigid finite control) is a genuine inductive invariant of
that rewrite system, and it is re-established after every
collapse (§2–§3); (iii) an *exhaustive event audit* over
3.23×10⁹ steps in every regime, in which the unique dangerous
pattern of §1 occurs **zero times** in 1.47×10⁸ audited events
(§4). What is still missing for a proof is stated exactly in
§6: the rewrite rules of §2 are *extracted from observation,
not derived from the transition table*, and the right-edge
regime has no invariant of its own. **The post-R proof does
not yet close; #168016 remains undecided.** What follows
separates, at every step, general proof (P), exhaustive finite
check (C), and observation (O).

**Phase 13 addendum (2026-11-25).** Obstruction 1 below is
now **closed**: `bounce-derivation.md` derives all four rules
from the transition table by shift rules (the excursion is a
single probe; the only induction is on the swept shuttle
length), proves the complete within-bounce event list (at
most one B-entry C-on-0 with context (1, 1), at most one
F-on-0 whose left triple is never (0, 1, 0)), and refines
POP's cost to exactly **2s + 3** — the "11 + 4t" of §2.3 was
the same number along real POP chains, where s = 4 + 2t.
The derived rules match all 1,666,665 genuine transitions of
the G = 66 window and 64 held-out synthetic bounces with zero
mismatches. Obstructions 2 and 3 stand as stated.

**Phase 14 addendum (2026-11-25).** Obstruction 2 below is
now **closed** as well: `reexpansion-derivation.md` derives
the collapse excursion (**Stage A**) from the transition
table for every post-collapse section σ_coll (merged tape
1¹⁷ 0 1^B2c 0 1^L 0^G 1², head B on the separator — a
section that already satisfies I and violates only
hypothesis H3). Stage A costs exactly 2L + 6, decrements G
by 2, and lands at the C-section with w = [L − 1]; its
event list is one safe probe and one F-on-0 with triple
(1, 1, 1) (or (0, 1, 1) at B2c = 1), never (0, 1, 0). The
section dynamics is therefore a **five-rule** derived
system (TDN / PUSH / POP / TUP / Stage A), total on I, and
I is an invariant of the machine's own section dynamics
across collapses, up to the first w = [1] section at
G = 2. Verified exactly: a 17-config Stage A battery (both
real collapses, the formation parameters, 14 synthetics)
and four 3×10⁶-step section windows (~250,000 sections
each, zero I violations, every transition classified,
event audits single-point clean). The formation stage's
first collapse is also covered from its merged tape
onward (Stage A0 entry landing in I; two further Stage A
cycles in-window). What remains is obstruction 3 (the
right-edge regime — its entry is now pinpointed to a
w = [1] B-section at G = 2) and the formation *merging*
sweep before the first merged tape.

Frame and notation are Phase 11's: the R frame (tape of R at
[0, 252], head 253 at R), "isolated step" = steps since R.
The still-running `phase10` background simulation was only read
(checkpoint at isolated step 1.239×10¹² at the end of this
phase), never disturbed.

## 1. The halt, reduced to one tape pattern (P)

Transition table (next-state), rows = state, columns = read 0/1:

    A: B A      B: C B      C: D A
    D: F E      E: — F      F: C F        (— = halt)

Reading off the entries into each state:

- **E is entered only from D-on-1** (`1LE`); **D is entered
  only from C-on-0** (`0LD`); **C is entered only from B-on-0**
  (`1RC`) **or F-on-0** (`1LC`). (Finite inspection of the
  table.)

**Lemma M1 (halt criterion).** The machine halts iff at some
step the head is in state C reading a 0 at a cell p with
tape[p−1] = 1 and tape[p−2] = 0.
*Proof.* Halt ⟺ E reads 0. E at a cell was entered by D-on-1
at the cell to its right: D wrote 1 there (no change, it read
1) and moved left into E. D was entered by C-on-0 at the cell
to *its* right: C read 0 at p, wrote 0 (no change), moved left
into D at p−1. So a halt occurs iff C reads 0 at p, D then
reads tape[p−1] = 1 (moving into E at p−2), and E reads
tape[p−2] = 0. The two tape cells are untouched between C's
read and E's read (C writes p, D writes p−1, both no-ops on the
values read), so the condition is exactly on the tape at the
moment of C's read. ∎

**Lemma M2 (B-entry is always safe).** If the C of M1 was
entered from B-on-0, the halt pattern cannot occur.
*Proof.* B-on-0 fired at p−1: B read 0 there, wrote 1, moved
right into C at p. How was the head at p−1 in state B? B is
entered only from A-on-0 (from p−2, writing 1 at p−2) or from
B-on-1 (from p, reading a 1 at p). In the first case
tape[p−2] = 1 at C's read (only B's own step intervenes, at
p−1), so M1's pattern (tape[p−2] = 0) fails. In the second
case tape[p] = 1, so C does not read 0 at all. ∎

**Lemma M3 (the D-on-0 route into F is safe).** If C was
entered from F-on-0 where that F was itself entered from
D-on-0, then C reads a 1 (D's own write at the cell C lands
on), so M1 does not apply. *Proof.* D-on-0 at q−1 writes 1 and
moves right into F at q; F-on-0 at q writes 1 and moves left
into C at q−1, which holds the 1 D wrote. ∎

So a halt requires **F-entry**: F-on-0 at some cell q, where F
arrived at q from the right (F-on-1 erasing, or E-on-1), C then
reads 0 at p = q−1, and tape[q−2] = 1, tape[q−3] = 0. I.e.:

**Lemma M4 (dangerous pattern).** The machine halts iff at
some step F reads a 0 at a cell q with
(tape[q−3], tape[q−2], tape[q−1]) = (0, 1, 0) — an isolated 1
(a 1-run of length exactly 1) standing two cells left of the
0 F is reading, with one more 0 between it and that 1.
*Proof.* Immediate from M1–M3 and the entry table for F
(D-on-0 covered by M3; the remaining entries into F are
F-on-1 and E-on-1, both arriving from q+1). ∎

Note the pattern in words: `0 1 0 0` with F stepping onto the
rightmost 0 from a 1 at its right. The rest of this phase is
about showing this pattern never faces an F-read — at sections
(§2), across collapses (§3), and at the raw event level in all
regimes (§4).

## 2. The section system and invariant I (C, with P preservation)

### 2.1 The section state, formalised

A **section** is a head local minimum (direction change −→+)
in the standard transient, as in Phase 11 §1.1. The section
state is

    σ = (state, h, B2, s, w, G, T)

with tape in the structural form
1¹⁷ 0 1^B2 0^g0 (1² 0^g)* 1² 0^G 1², where s is the shuttle
(first working 1-run), w = [g0, g1, …, gk] is the gap word
(g0 the gap after B2, gi≥1 the inter-run gaps), T = 2 the
terminal run, and h the head position. Sections were extracted
from `phase11-bounce20m.log` (2×10⁷ steps from the G = 66 dump
section; the 2×10⁶-step `phase11-bounce.log` is its prefix)
and from two fresh post-collapse windows (§3).

### 2.2 Invariant I (verified on every genuine section)

At every section after the first (the first record of each log
is the start configuration by fiat, not a genuine minimum):

- **(I1)** every gap in w is **odd**;
- **(I2)** the shuttle s is **even**;
- **(I3)** state = C ⟹ s = 2 and h = B2 + 16;
        state = B ⟹ g0 = 1, s ≥ 4, and h = B2 + 18;
- **(I4)** T = 2, and G is unchanged by bounces (G even in the
        standard regime: 106 at formation, then −2 per
        collapse).

Counts (C): 1,666,665 genuine transitions in the G = 66 window
(zero violations of I1–I4; shuttle parity violations 0 in
1,666,666 sections; even inner gaps 0), plus the two
post-collapse windows of §3 (166,674 and 166,651 genuine
transitions, zero violations). Total ≈ 2.0×10⁶ verified
section transitions in three independent windows.

### 2.3 The rewrite rules (extracted exactly; C)

Every observed section transition is one of four rules.
Selection is a function of the section state alone, and the
rules are **total on I**: at a C-section g0 is odd, so exactly
one of g0 = 1 / g0 ≥ 3 holds; at a B-section g0 = 1 and g1 is
odd, so exactly one of g1 = 1 / g1 ≥ 3 holds.

| Rule | Guard | Effect (w = [g0, g1, g2, …], shuttle s) | Cost |
|---|---|---|---|
| **TDN** | state C, g0 = 1 | → B; B2 −= 2; s := 4; w unchanged | 6 |
| **PUSH** | state C, g0 ≥ 3 | → C; B2 −= 1; w := [1, g0−2, g1, g2, …]; s = 2 | 9 |
| **POP** | state B, g1 = 1 | → B; B2 += 1; s += 2; w := [g1, g2, …] (pop; the popped g0 is always 1) | 11 + 4t, t ≥ 0 |
| **TUP** | state B, g1 ≥ 3 | → C; B2 += 2; w := [s−1, g1−2, g2, …]; s := 2 | 2s + 6 |

Verification (C): in the G = 66 window, TDN/PUSH/POP/TUP occur
416,666 / 416,666 / 416,667 / 416,666 times; each rule's stated
effect holds in **every** instance (pure pop in 416,667/416,667;
PUSH tail identity b[2:] = a[1:] and (b0, b1) = (1, g0−2) in
416,666/416,666; TUP tail identity and b0 + b1 = g0 + g1 + 2j − 2
with j = s/2 − 1 in 416,666/416,666, refining to the closed
forms b0 = s − 1, b1 = g1 − 2 since the post-TUP shuttle is
always 2). The only freedom in any rule is POP's t (extra
excursion depth; cost 11 + 4t, geometric in t) — it does not
affect the resulting section state. Excursion depths otherwise
vary (e.g. PUSH depth 7, 9, 11, …) with the net effect fixed.
G changes in 0 of 1,666,665 transitions: bounces never touch
G; only collapses do (§3).

**Preservation (P, arithmetic).** Each rule preserves I:
TDN leaves w (odd) and sets s = 4 (even, ≥ 4) with g0 = 1, as
(I3)-B requires. PUSH writes 1 and g0 − 2 (odd ∸ odd) and keeps
s = 2, as (I3)-C requires. POP pops a 1 and exposes g1 = 1 as
the new g0, s += 2 stays even and ≥ 6. TUP writes s − 1 (odd,
since s even) and g1 − 2 (odd), sets s = 2, as (I3)-C
requires. Head bookkeeping h = B2 + 18 (B) / B2 + 16 (C) is
consistent with the observed sections in all windows. Hence
**I is an inductive invariant of the section rewrite system**:
any section sequence generated by the rules from an I-section
stays in I forever, with G fixed. ∎ (About the rewrite system
— see §6 for what this does and does not prove about the
machine.)

### 2.4 Why I strangles the dangerous pattern (P, given §2.3)

Inside the working region, the 1-runs are: B2 (length ≥ 68 in
all windows), the shuttle (even, so ≥ 2 or — at C-sections —
exactly 2; never 1 at a section), the pairs (exactly 2), and
the terminal (2). The dangerous pattern of M4 needs an
**isolated 1** whose right gap is exactly 2. At a section
there is no isolated 1 at all, and every gap is odd (never 2).
The pattern can therefore only be attempted *mid-bounce*, in
the excursion-touched region — which is what §4 audits at the
raw event level, and what §6 lists as the missing derivation.

## 3. Collapse and regeneration at the section level (C)

A collapse is not a bounce rule: it is the event (Phase 11
§2) in which a bounce's excursion reaches the stack bottom.
At the section level it is a regime transition

    (w, G)  ──collapse + pair-writing + re-expansion──▶  (w′, G − 2)

where w′ is a **regenerated** stack word, not a local rewrite
of w: the pairs region is crushed to one solid block, a fresh
pair is written onto the long gap (G := G − 2 by the 3-step
local rule of Phase 11 §2.2), and pairs are re-carved over
~10⁵–10⁶ steps. What this phase adds:

- **I is re-established after re-expansion (C).** Fresh bounce
  windows were run from the first dumps after the two
  pinpointed collapses of Phase 11 (isolated steps
  412,316,860,191 at G = 68 and 824,633,720,597 at G = 66):
  from the dump at 413×10⁹ (G = 66), 166,675 sections; from the
  dump at 825×10⁹ (G = 64), 166,652 sections. In both windows
  **every genuine section satisfies I** (even gaps 0, odd
  shuttles 0, T ≠ 2 count 0, states B/C only).
- **The collapse anatomy itself is event-clean (C).** The
  3×10⁷-step audit from the post-collapse configuration
  `phase11-collapse.cfg` (covering the G = 68 → 66 decrement
  and the full re-expansion) shows the same single-point event
  distribution as the settled regime (§4): all 1,250,016
  C-on-0 events are B-entry with left context (1, 1) — the
  sweep-trail archetype of M2 — and all F-on-0 triples are
  (1, 1, 1). The formation stage from R, which contains the
  early collapses (first at isolated step 786,397), is audited
  the same way over 10⁹ steps in §4 with the identical result.

What is *not* shown: that re-expansion **must** restore I
(rather than some other attractor). The evidence is two full
collapse cycles audited at both the event level and the
section level, plus the G = 66/64 windows' 333,327 sections —
strong, but it is (C), not (P). See §6.

## 4. The event audit: the dangerous pattern never occurs (C)

Tool: `phase12.c` — an instrumented simulator (same cfg format
and transition tables as the validated `phase11.c`) that runs a
configuration and counts, over the whole run: every E-read by
symbol; every C-on-0 event by (entry ∈ {B, F, init},
tape[p−2], tape[p−1]); every F-on-0 event by the triple
(tape[q−3], tape[q−2], tape[q−1]); every D-read by symbol. It
aborts with a DANGER report if M1's pattern or M4's triple is
ever seen. Nine runs, **3.23×10⁹ steps** in total:

| Run (start config) | Steps | C-on-0 events | Contexts seen |
|---|---|---|---|
| G = 66 settled (`phase11-g66.cfg`) | 10⁹ | 41,666,626 | B-entry (1,1) only |
| Formation from R (`phase11-R.cfg`) | 10⁹ | 41,666,702 | B-entry (1,1) only |
| Collapse + re-expansion (`phase11-collapse.cfg`) | 3×10⁷ | 1,250,016 | B-entry (1,1) only |
| G = 68 settled (`phase11-g68.cfg`) | 2×10⁸ | 8,333,332 | B-entry (1,1) only (+1 init) |
| Synthetic G = 4 (`phase11-syn-g4.cfg`) | 2×10⁸ | 8,333,362 | B-entry (1,1) only |
| Right-edge regime, G = 2 (`phase11-syn-g2.cfg`) | 5×10⁸ | 20,833,368 | B-entry (1,1) only |
| Regeneration, G = 0 (`phase11-syn-g0.cfg`) | 2×10⁸ | 8,333,362 | B-entry (1,1) only |
| Adversarial F@252 (`phase11-adv-f252.cfg`) | 2×10⁸ | 8,333,380 | see below |
| Adversarial F@254 (`phase11-adv-f254.cfg`) | 2×10⁸ | 8,333,380 | see below |

Totals: **147,083,528 C-on-0 events and 147,083,529 F-on-0
events audited; E-reads 147,083,517, every one on a 1;
D-reads on 0: 11, all in the adversarial runs. The dangerous
C-on-0 context (tape[p−2], tape[p−1]) = (0, 1) and the
dangerous F-on-0 triple (0, 1, 0) occurred 0 times.**

In every regime reachable from R the distribution is a
**single point**: each C-on-0 is a B-entry sweep reflection
with both left cells 1 (exactly the M2 archetype), each
F-on-0 has left triple (1, 1, 1) — F steps onto a 0 whose
three left neighbours are 1s, so the ensuing C reads a 1 and
no D/E step-back even starts — and D never reads 0 at all.
**F-entry C-on-0 events do not occur in any reachable regime**
in 3.23×10⁹ steps.

The two **adversarial** runs (head seeded behind the terminal
pair — configurations Phase 11 §2.3 argues are unreachable
from the left, included as stress tests) are the only place
F-entry C-on-0 events occur at all: 13 events in 4×10⁸ steps,
all during the initial disturbance, all safe — 11 with left
context (0, 0) (D-on-0 rattle: D-reads on 0 total 11) and 2
with (1, 1). Their F-on-0 triples diversify briefly
((0,0,0), (0,0,1), (0,1,1), (1,0,1), (1,1,0) — 172 per run)
before settling into the same single-point distribution; the
dangerous triple (0, 1, 0) does not occur even there. The
closest approaches are (0, 1, 1) — C reads a 1, harmless —
and (1, 1, 0) — the ensuing C-on-0 has left context (1, 1).

## 5. The right-edge regime (C/O)

The right-edge regime (entered at G ≤ 2, Phase 11 §3.2) has
**no section structure** (the left interface is frozen; the
head never returns to it) and **no parity invariant**: its
tape (e.g. 1¹⁷ 0 1⁹⁶ 0 1⁶² 0 1⁹ 0² 1² 0⁷ 1² …) contains even
gaps, including 2, and runs of many lengths. Invariant I
simply does not apply there. Its safety evidence is:

- the §4 audit of the synthetic G = 2 configuration over
  5×10⁸ steps: 20,833,368 C-on-0 events, all B-entry (1, 1);
  all F-on-0 triples (1, 1, 1); no D-on-0; no halt — the same
  rigid distribution as the standard regime, despite the
  absence of the parity invariant;
- the G = 0 regeneration audit (2×10⁸ steps, same result),
  covering the exit back toward the standard transient;
- Phase 11's 10⁹-step stability run of the same regime.

Two honest caveats. First, this is (C) over finite windows,
with no invariant explaining *why* the dangerous pattern
stays away there (the blocks it manipulates are long, and the
sawtooth gap is at the right edge where the engagement
geometry differs — an observation, not an argument). Second,
the right-edge regime's **reachability from R is only
projected**: G = 64 needs ~31 more collapses (~10¹³ steps at
observed rates) to reach 2. It has never been entered on the
real trajectory; the synthetic G = 2 / G = 0 configurations
are Phase 11's constructions from the collapse anatomy.

**Phase 15 addendum.** The first caveat is superseded: the
regime has a section structure at the β interface (the right
end of the working region's first run) with invariant RI and
five derived mirror rules — see `rightedge-derivation.md`
and the Phase 15 note in §6, obstruction 3. The reachability
caveat stands unchanged.

## 6. Status: what is proven, what is checked, the obstruction

**Proven (P), general arguments from the transition table:**
- M1: halting ⟺ a C-on-0 read with left context (1, 0).
- M2: B-entry C-on-0 never halts. M3: the D-on-0 route into
  F-entry never halts. M4: halting ⟺ an F-on-0 read with left
  triple (0, 1, 0) — an isolated 1 two cells left of F's 0.
- The four section rules preserve invariant I, and are total
  on I (§2.3): I is an inductive invariant *of the rewrite
  system*.

**Exhaustively checked (C), finite but large:**
- The machine's section dynamics *is* the §2.3 rewrite system
  on ≈ 2.0×10⁶ consecutive transitions in three independent
  windows (G = 66 settled; post-collapse G = 66; post-collapse
  G = 64), with I holding at every section.
- I is re-established after each of the two pinpointed
  collapses (section level) and the collapse + re-expansion
  anatomy is event-clean (§3, §4).
- The dangerous pattern of M4 occurs 0 times in 1.47×10⁸
  F-on-0 events over 3.23×10⁹ steps spanning formation, the
  settled transient at G = 64/66/68, collapse + re-expansion,
  the right-edge regime, regeneration, and two adversarial
  seedings (§4). In all reachable regimes the C-on-0/F-on-0
  context distribution is a single safe point.

**The exact obstruction — three missing derivations:**
1. **The bounce rules are extracted, not derived.**
   **CLOSED by Phase 13** (`bounce-derivation.md`): each rule
   is now an explicit shift-rule computation from the
   transition table, under the hypotheses that the start
   section satisfies I and (for B-sections) at least one pair
   follows the shuttle. The excursion is a single probe — the
   "mini-cascade" picture was wrong; the geometric depth law
   is the population distribution of the four fixed forms
   (depths 3, 5, s+1, s+3) under the section dynamics. The
   within-bounce event list is proven: no E-on-0, no D-on-0,
   C-on-0 only as the probe's B-entry reflection with context
   (1, 1), F-on-0 only with left triple ≠ (0, 1, 0) ((1, 1, 1)
   in the invariant region). §2's invariant is therefore an
   invariant of the machine's section dynamics on every
   bounce whose start section satisfies the hypotheses; the
   boundary case (no pair after the shuttle) is the collapse
   of obstruction 2.
2. **Re-expansion is not proven to restore I.**
   **CLOSED by Phase 14** (`reexpansion-derivation.md`):
   the framing itself was the obstacle. I is never lost at
   a section — the collapse's end section σ_coll satisfies
   I and fails only Phase 13's H3 — and the single
   non-Phase-13 excursion from σ_coll is derived there as
   **Stage A** (cost 2L + 6, G := G − 2, landing at the
   C-section with w = [L − 1], event list proven clean).
   Everything after that landing is the four derived rules;
   the ~10⁵–10⁶-step "re-expansion" of Phase 11 §2.2 is the
   residue L − 1 grinding down *inside* the proven system
   (each surfacing reduces it by exactly 2 — a corollary of
   the rule forms). The composed five-rule system is total
   on I and I-preserving across collapses, up to the first
   w = [1] section at G = 2 (obstruction 3's entry, now
   pinpointed). The formation stage's first collapse is
   likewise covered from its merged tape onward (Stage A0
   entry, §4.2 of the Phase 14 write-up); what remains
   underived there is only the formation *merging* sweep
   that first produces a merged tape.
3. **The right-edge regime has no invariant.** Its safety
   rests on finite audits (§5). A proof needs an invariant
   for the sawtooth dynamics there — none was found; the
   parity mechanism of the standard regime is absent (even
   gaps occur), yet the dangerous pattern still never
   occurs, for reasons the audits document but do not
   explain. (Its reachability from R is itself only a
   projection, §5.)
   **CLOSED by Phase 15** (`rightedge-derivation.md`), with
   one explicitly stated global hypothesis. The regime does
   have a section structure after all — not at the frozen
   left interface (Phase 12 looked there), but at the right
   end of the working region's first run β: the entry
   excursion from the w = [1], G = 2 section is derived in
   closed form (cost s + 12, landing at the first
   right-section σ_re), and from there the dynamics is a
   system of **five mirror rules** (RTDN/RPUSH/RPOP/RTUP/
   RPROBE), each derived from the transition table with its
   event list proven clean by the same probe argument as
   Phase 13 (every C-on-0 is the probe's B-entry reflection
   with context (1, 1); every F-on-0 has triple (1, 1, 1),
   (1, 0, 1), (1, 1, 0) or (0, 1, 1) — never (0, 1, 0); no
   E-on-0, no D-on-0). The invariant is **RI**: frozen
   prefix, all working gaps odd, all non-β runs even,
   B-form ⟹ g1 = 1 — preserved by all five rules, which are
   total on RI. Classification: 0 mismatches on 9,141,616
   consecutive section transitions across four windows (up
   to 10⁸ steps). The regime's macro-structure is a token
   pass cycle: a unique token gap of value v = 2h + 1 in a
   sea of 1-gaps moves left across 17 gaps with exact move
   cost 3·2^(j+3) − 11 (verified for v = 3, 5), is consumed
   at the block, and regenerates with v := v + 2; the pass
   duration (2^h − 1)·3·2¹⁹ fits eight passes over 10⁹
   steps to < 0.002 % — Phase 11's ~10⁸ sawtooth is the
   v = 13 pass. The regime is absorbing (the frozen prefix
   is never written again; no return to I is possible) and
   cycles forever. The one remaining hypothesis is a
   global lower bound on β at C-form sections: the rules
   are derived for all β ≥ 2 and the β = 2 boundary is
   analysed exactly (excursions still event-clean; the
   successor leaves RI; the escape step is an M1-safe
   F-entry C-on-0 (1, 1)), while observed β at C-form
   sections is ≥ 55 over 10⁸ steps (≥ 48 at 4.19×10⁶ home
   samples over 10⁹ steps). §5's "no invariant" caveat is
   thereby superseded; §5's reachability caveat stands
   (entry on the real trajectory is still projected).

**Conclusion.** The post-R regime is now reduced to a
five-rule pushdown rewrite system with a clean inductive
invariant — the rewrite system itself derived (Phase 13),
the collapse excursion derived (Phase 14, obstruction 2
closed) — a proven reduction of the halt to a single tape
pattern, and an event-level audit showing that pattern
never occurs in 3.23×10⁹ steps across every regime. With
Phase 15, the right-edge regime (obstruction 3) is also a
derived rule system with its own invariant RI, proven
event-clean excursion by excursion; its only hypothesis
is the β lower bound (observed margin ≥ 45 over 10⁹
steps), and its entry from R remains a projection (the
w = [1], G = 2 section has been entered only in synthetic
chains). The segments that remain computational facts
rather than derivations are now: the formation merging
sweep before the first merged tape, the projected entry
into the right-edge regime on the real trajectory, and
the β bound inside that regime. **#168016 remains
undecided.** Nothing has been posted externally.

*Files: `phase12.c` (event auditor), `phase12-events.log`
(the nine audits of §4), `phase12_parse.py` (section
statistics), `phase12_rules.py`, `phase12_rules2.py` (rule
extraction and selection), `phase12-postcol66.cfg`,
`phase12-postcol64.cfg` (post-collapse dump configs),
`phase12-bounce-postcol66.log`,
`phase12-bounce-postcol64.log` (post-collapse section
windows), `phase12_runs.sh`. Phase 15: `rightedge-derivation.md`,
`phase15.c`, `phase15_classify.py`, `phase15_classify2.py`,
`phase15_classify_stream.py`, `phase15-exc-summary.tsv`
(the 4,194,714 EXC-END records of the 10⁹-step right-edge
run), configs `p15-e*.cfg`, `p15-r1.cfg`, `p15-home1.cfg`,
`p15-passend.cfg`, `p15-b*.cfg`. The phase10 background run
continues (checkpoint 1.239×10¹² isolated steps at the end
of this phase).*
