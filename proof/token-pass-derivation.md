# Phase 17 — The token pass derived; the β proviso is FALSE (2026-11-25)

Machine #168016 (`1RB1RA_1RC1LB_0LD0RA_1RF1LE_---1LF_1LC0LF`),
right-edge regime (Phase 15, `rightedge-derivation.md`).

**Mission.** Derive the token pass from the five mirror rules
(RTDN / RPUSH / RPOP / RTUP / RPROBE) and discharge the β
proviso of `168016-proof.md` §3 — the hypothesis that no
C-form right-section with β = 2 is ever reached.

**Verdict, up front.** The pass map *is* derived (§§2–5), and
it refutes the proviso. The right-edge dynamics from an entry
σ_re(β_E) organises into **cycles**
Γ: (C, β_E, (2k+1), (2)) → (C, β_E, (2k+3), (2)), and inside
cycle k the minimum of β over C-sections is exactly
**β_E − k** (Cycle Lemma, §5). The minimum is attained at the
tokenless home section H_k = (C, β_E−k, (1^{k+1}), (2^{k+1})).
Consequently **a C-section with β = 2 is reached in cycle
β_E − 2, for every entry β_E ≥ 4** — at the section
(C, 2, (1^{β_E−1}), (2^{β_E−1})) — after which RTDN's
excursion, though event-clean, lands outside the rule system
(the head merges the β block with the first working run and
the frozen prefix of invariant RI is breached). The
restoring mechanism Phase 15 measured (β restored at home
returns, token v := v+2) is real but is only the top of each
cycle: the same cycle's rebuild dips β to β_E − k, one lower
per cycle, and home-form sampling never sees the dip. The
assembled proof's single gap therefore **moves**: it is no
longer "β ≥ 3 forever" (false) but "the continuation after
the β = 2 exit" (§7). Nothing here touches the unconditional
finite bound ≈ 1.7709×10²¹ steps (the right-edge regime has
not been entered on the real trajectory; Phases 9–10 stand).

Tools: `phase17_model.py` (word-level model of the five
rules), `phase17_run.py`, `phase17_run2.py`,
`phase17_cycles.py`; configs `p17-sre4.cfg`, `p17-sre6.cfg`,
`p17-sre8.cfg` (synthetic σ_re entries, B2 = 31); machine
section logs `p17-sre4-sec.log`, `p17-sre8-sec.log`
(`phase15 sec2`). The phase10 background run was not
disturbed (read-only throughout).

## 1. The word-level model and its validation

A right-section is coded by (form, β, a, r): form ∈ {C, B},
word W = 1^β · Π_{i=1..n} (0^{a_i} 1^{r_i}) at working run 0
(the frozen prefix 1¹⁷ 0 1^{B2} 0¹ is fixed and never
rewritten inside the regime — Phase 15). `phase17_model.py`
implements the five rules of `rightedge-derivation.md` §2 in
exactly this coding:

- RTDN (C, a₁=1): β−2, r₁+=2, →B, cost 6.
- RPUSH (C, a₁≥3): β−1, a:=(1, a₁−2)+rest, r:=(2,)+r, →C, cost 9.
- RPOP (B, n≥2, a₂=1): β+1, r₁+=r₂ (merge, drop a₂, r₂), →B, cost 2r₁+3 (pre-rule r₁).
- RTUP (B, n≥2, a₂≥3): β+2, a:=(r₁−1, a₂−2)+rest, r:=(2,)+r[1:], →C, cost 2r₁+6.
- RPROBE (B, n=1): β+2, a:=(r₁−1,), r:=(2,), →C, cost 2r₁+6, span +2.

**Validation (C).** The model reproduces the Phase 15/16
section logs exactly — successor word, form, and step cost —
on **all 808,302 sections** (250,028 small-geometry +
416,632 home + 141,636 pass-boundary; 0 mismatches). It is
also validated end-to-end against the machine simulator
(`phase15.c`) on synthetic entries σ_re(β_E) (§6): exact
agreement on every section up to and including the first
β = 2 C-section (β_E = 4: 11 sections; β_E = 8: 247
sections), diverging only at that section's successor —
which is precisely the exit analysed in §6.

## 2. Joint invariant; phases have length exactly 2

**Lemma J.** At every section reachable from σ_re:
(J1) all gaps a_i are odd ≥ 1 and all runs r_i are even ≥ 2;
(J2) C-form ⟹ r₁ = 2; B-form ⟹ a₁ = 1 and r₁ ≥ 4.

*Proof.* σ_re = (C, β_E, (1), (2)) satisfies J. Each rule
preserves J: RTDN sends r₁ = 2 → 4 (B-form, a₁ = 1 kept);
RPUSH creates r₁ = 2 (C-form); RPOP keeps a₁ = 1 and
r₁ := r₁ + r₂ ≥ 4 + 2 (B-form); RTUP and RPROBE create
r₁ = 2 (C-form) and a₁ = r₁−1 with the pre-rule r₁ ≥ 4,
so a₁ ≥ 3 odd. ∎

**Corollary (phase length).** Post-entry, every C-phase
(maximal run of C-sections) has length exactly 2: a phase
starts with a₁ ≥ 3 (C-sections arise only via RPUSH —
a₁ = 1, mid-phase — or via RTUP/RPROBE — a₁ = r₁−1 ≥ 3 by
J2), fires RPUSH to a₁ = 1, then RTDN to B. This *derives*
Phase 16's law b; law a is J restated.

## 3. The round map (Phase 16's law, derived)

A **round** = one C-phase + the following B-excursion,
ending at the next phase start. At a phase start
(C, β, a₁..a_n; 2, r₂..r_n) with a₁ ≥ 3:

- the phase (RPUSH, RTDN) gives the B-state
  (B, β−3; gaps (1, a₁−2, a₂..), runs (4, 2, r₂..));
- the excursion fires RPOP t times (while the second gap
  is 1) and closes with RTUP or RPROBE (+2).

Writing u for the number of leading 1s in the tail
(a₂, a₃, …) at the phase start (u ≤ n−1):

- **Type A (a₁ ≥ 5):** t = 0 (second gap a₁−2 ≥ 3, RTUP
  immediately). Δβ over the round = −3 + 2 = **−1**;
  next start (C, β−1; 3, a₁−4, a₂..; 2, 2, r₂..). ρ := t = 0.
- **Type B (a₁ = 3), u < n−1:** t = u+1 RPOPs (merged run
  R = 6 + Σ_{i=2}^{u+1} r_i), then RTUP at gap a_{u+2} ≥ 3.
  Δβ = −3 + (u+1) + 2 = **+u**; next start
  (C, β+u; R−1, a_{u+2}−2, a_{u+3}..; 2, r_{u+2}..). ρ = u+1.
- **Type B, u = n−1 (all tail gaps 1):** t = n RPOPs, then
  RPROBE. Δβ = **+(n−1) = +u**; next start
  (C, β+u; R_tot−1; 2) with R_tot = 6 + Σ_{i=2}^{n} r_i;
  the word collapses to one pair; span +2.

**Alternation (Phase 16's law c, derived).** A type-A round
ends at a₁′ = 3 (type B next); a type-B round ends at
a₁′ = R−1 ≥ 5 (type A next; R ≥ 6, and in the RPROBE case
R_tot−1 ≥ 5 likewise). With ρ := t this is exactly Phase
16's law d: type A ⟹ ρ = 0, β_C0 −1; type B ⟹ ρ ≥ 1,
β_C0 −1 + ρ. Phase 16's question — *can ρ = 1 repeat for
β_entry − 2 consecutive A+B pairs?* — is answered in §§4–5:
the β_C0 walk is governed by a binary-counter recursion on
the tail, and its minimum falls by exactly 1 per cycle.
(ρ = 1 does occur with frequency 1/2 among B-rounds — the
geometric histogram of Phase 16 — but the decreases are not
one-per-pair; they accumulate one per *cycle*, §5.)

## 4. B-start dynamics; the Suffix Lemma

Call a phase start with a₁ = 3 a **B-start**, written
(β; x₁..x_m) with tail x = (a₂..a_{n}), m = n−1. Inside the
cycles of §5 every B-start has all runs = 2 (induction:
the round map sends runs (2, s..) at a B-start to
(2, s_{u+1}..) at the next B-start after the intervening
A-round, which preserves the all-2 property; the first
B-start has runs (2,2)). With all runs 2, R = 6 + 2u, and
the composed two-round map Ψ (B-start → B-start) is

- u < m: Ψ(β; x) = (β + u − 1; (1 + 2u, x_{u+1} − 2, x_{u+2}, …, x_m)),
- u = m: the B-round is RPROBE-ending (the cycle closes, §5).

Note u = 0 forces the next tail to start with 1 (so u′ ≥ 1),
and u ≥ 1 forces the next tail to start with 1 + 2u ≥ 3
(so u′ = 0): zeros and nonzeros alternate — the ruler
structure behind the geometric ρ histogram.

**Suffix Lemma.** Let a B-start have tail (x₁..x_m, y) with
y ≥ 3. Then the Ψ-orbit projects onto the Ψ-orbit of the
front (x₁..x_m) — same β at every step, same front tails —
until the first B-start whose front is (1^m); the following
Ψ step is the **carry**: u = m (the leading 1s stop at y),
Ψ(β*; (1^m, y)) = (β* + m − 1; (1 + 2m, y − 2)).

*Proof.* By induction on orbit length. Ψ's u and its update
of the front components depend only on x₁..x_{u+1}; the
last component y is read only as x_{u+1} when u = m, i.e.
exactly when the front is all-ones, where the formula
gives the carry. All other steps leave y untouched and
reproduce the front's own Ψ step verbatim. ∎

## 5. The Cycle Lemma

Define S_k(β) := (C, β, (2k+1), (2)) — a single pair whose
gap is 2k+1. Note σ_re(β_E) = S_0(β_E).

**Cycle Lemma.** For every k ≥ 0 and every β ≥ k + 3, the
orbit of S_k(β) under the five rules:
(i) reaches S_{k+1}(β) after exactly D_k = 3·2^{k+3} − 4
steps (and 2^{k+2} − 2 + O(1) sections);
(ii) has min β over C-sections exactly **β − k**, attained
at the tokenless home section H_k(β) = (C, β−k, (1^{k+1}),
(2^{k+1})) — the phase second of the cycle's last B-phase;
(iii) has min β over B-sections exactly β − k − 2;
(iv) keeps β at S_{k+1} equal to β (the block is restored at
the cycle boundary), ones(W) constant, span(W) + 2.

*Proof.* Induction on k. k = 0, 1 are finite enumerations
(6 and 10 sections; D_0 = 20, D_1 = 44). For k ≥ 2: the
first round from S_k(β) is type A, reaching the B-start
(β−1; (2k−3)). Let ℬ_k(β) denote the B-start sequence of
cycle k (from that B-start to the last B-start, whose round
is the RPROBE round closing the cycle). **Orbit recursion:**
ℬ_k(β) = ℬ_{k−1}(β) with the last tail gap increased by 2,
followed by ℬ_{k−1}(β) with a 1 appended to the tail and β
decreased by 1 throughout. Indeed: cycle k's first B-start
tail (2k−3) is cycle (k−1)'s first B-start tail (2k−5)
with its last (only) gap +2; by the Suffix Lemma the orbit
replays ℬ_{k−1} verbatim (β included) with the +2 carried
on the last gap — the last gap is decremented by 2 at
exactly the same carries in both orbits, so the offset
persists — until the front reaches the all-ones tail where
ℬ_{k−1} would close the cycle; there the last gap is 3,
not 1, so instead of the closing RPROBE round a carry
fires (Suffix Lemma), producing a B-start whose tail is
ℬ_{k−1}'s closing tail with a 1 appended, at β one less
(the carry's Δβ = m − 1 replaces the closing round's
Δβ = m, and the intervening A-round contributes its −1 as
usual); the Suffix Lemma applied again, with the appended
1 as the front's guaranteed final leading 1, replays
ℬ_{k−1} a second time, ending at the all-ones tail
(1^{k−1}) whose B-round is the RPROBE round: it collapses
the word to (C, β, (2k+3), (2)) = S_{k+1}(β), proving (iv)
and the reachability in (i). The duration satisfies
D_k = 2·D_{k−1} + 4 (the two replayed halves cost D_{k−1}
each up to the shared boundary rounds), with D_0 = 20,
giving D_k = 3·2^{k+3} − 4. For (ii)–(iii): by the
recursion and the induction hypothesis, the minimum β over
B-starts in cycle k is min(min ℬ_{k−1}(β), min ℬ_{k−1}(β) − 1)
= (β − (k−1)) − 1 = β − k + 1, attained in the second half;
C-sections are phase starts (β ≥ that minimum's round
start) and phase seconds (start β − 1), so min β over
C-sections is β − k, attained at the phase second of the
final B-start — which is (C, β−k, (1^{k+1}), (2^{k+1}))
because the final B-start is (β−k+1; (1^{k−1})) with runs
all 2, and its RPUSH produces the all-ones word. B-sections
sit at phase-start β − 3 (post-phase) up to +t during the
excursion, giving min β − k − 2. The hypothesis β ≥ k + 3
is exactly what keeps every C-section at β ≥ 3 and every
B-section at β ≥ 1 throughout, so all five rule derivations
(Phase 15) remain valid on the whole cycle. ∎

**Verification (C).** The lemma's every quantitative claim
(duration, cycle-end state, min β_C = β−k, min β_B = β−k−2,
post-cycle gap 2k+3, post-cycle β restored) is exact in the
model for **all** cycles computed, at seven entry values:

| β_E | cycles run | min β_C in cycle k | result |
|---|---|---|---|
| 4 | 0–3 | 4, 3, **2**, (1) | law exact; β=2 in cycle 2 |
| 6 | 0–5 | 6, 5, 4, 3, **2**, (1) | law exact; β=2 in cycle 4 |
| 8 | 0–7 | 8,…,3, **2**, (1) | law exact; β=2 in cycle 6 |
| 12 | 0–11 | 12,…,3, **2**, (1) | law exact; β=2 in cycle 10 |
| 24 | 0–23 | 24,…,3, **2**, (1) | law exact; β=2 in cycle 22 |
| 40 | 0–21 | 40,…,19 | law exact |
| 72 | 0–20 | 72,…,52 | law exact |

(Cycles beyond k = β_E − 2 are the model's *formal*
continuation past the exit of §6 and are listed only to
show the law's persistence; the machine leaves the system
at the first β = 2 section.) The β_E = 72 line is the
syng2 geometry of Phase 15: its cycle-20 minimum 52 matches
the independent run from the genuine pass-boundary section
`p15-passend.cfg` (6×10⁶ sections, min β_C = 52, RPROBE
landings at β = 72 with gaps 37, 39, 41, 43 = cycles
17–20). The Phase 15/16 window floors are likewise
explained: the small-geometry window (β_E = 24, 3×10⁶
steps) covers cycles ≤ 15, floor 24 − 15 = 9 ✓; the home
window covers cycles ≤ 16 of β_E = 72, floor 56 ✓;
pass-boundary window reaches cycle 17, floor 55 ✓.

## 6. The exit: β = 2 is reached

**Theorem (Phase 17).** For every β_E ≥ 4, the machine's
trajectory from σ_re(β_E) coincides with the five-rule
dynamics up to and including the C-section

  H_{β_E−2} = (C, 2, (1^{β_E−1}), (2^{β_E−1})),

reached at step T(β_E) = Σ_{j<β_E−2} D_j + off(β_E−2)
from σ_re, where Σ_{j<K} D_j = 3·2^{K+3} − 24 − 4K and
off(k) is the offset of the last B-phase's second section
within cycle k. At H_{β_E−2}, RTDN fires (g₁ = 1); its
excursion is event-clean (Phase 15 §3), but the successor
is **not** a section of the system: the machine's actual
successor (verified for β_E = 4 and β_E = 8) is the
B-section (B, 4, (1^{β_E−2}), (2^{β_E−2})) in coordinates
shifted 2 cells left — the β block and the first working
run have merged into a single run of 4 and one pair has
been consumed. Invariant RI's frozen prefix is breached;
the right-edge rule system ends there.

*Proof.* By the Cycle Lemma applied for k = 0, …, β_E − 3
(each satisfies β_E ≥ k + 3), the dynamics follows the five
rules through cycle β_E − 3 and enters cycle β_E − 2 at
S_{β_E−2}(β_E) with all C-sections so far at β ≥ 3 and all
B-sections at β ≥ 1, so Phase 15's derivations cover every
excursion. Inside cycle β_E − 2 the same round/B-start
analysis applies verbatim as long as C-sections have
β ≥ 3; by the recursion of §5 the orbit reaches the final
B-start (3; (1^{β_E−2})) at β_C0 = 3, whose phase second is
H_{β_E−2} at β = 2 — the first section of the trajectory
with β < 3 at a C-form section (all earlier C-sections in
the cycle are ≥ 3 by the recursion's minima). The machine
therefore reaches H_{β_E−2}. Its RTDN excursion and the
successor's shape are Phase 15 §3's β = 2 analysis
specialised to g₁ = 1, confirmed by direct simulation
below. ∎

**Machine verification (C).** From `p17-sre8.cfg`
(σ_re(8), B2 = 31), `phase15 sec2` produces 288 sections;
the model matches the machine on every section up to and
including H_6 = (2850, C, 2, (1⁷), (2⁷)) — so **T(8) = 2850**
— and the machine's next sections are (2856, B, 4, (1⁶),
(2⁶)), (2867, B, 1, (1⁶), (6,2,2,2,2,2)), …: the escaped
head is consuming the word from its left edge, outside
both rule systems. From `p17-sre4.cfg`: H_2 = (102, C, 2,
(1³), (2³)), **T(4) = 102**, successor (108, B, 4, (1²),
(2²)). For β_E = 24 the model gives H_22 = (C, 2, (1²³),
(2²³)) at cycle-22 offset 100,662,018, i.e.
**T(24) = 201,325,202** steps from σ_re.

**Relation to Phase 15's pass.** Phase 15's token pass is
the segment of a cycle between two visits to a long home
form: within cycle k ≥ 16 of the β_E = 72 trajectory the
word rebuilds to the 17-pair home form (β_home = 56 =
β_E − 16, token at the last gap), the token walks left and
is consumed, and the next home visit has token v + 2 at the
same β_home — the pass map (β_home, v) ↦ (β_home, v + 2)
with span + 2 and ones constant, exactly as measured. What
the pass picture misses is that the cycle *continues* past
the home visits into the deep rebuild, whose bottom is
H_k at β_E − k < β_home once k > 16. β is restored at home
returns; it is **not** bounded below by β_home, nor by any
constant: the floor falls by 1 per cycle because each cycle
must rebuild a gap 2 longer than the last, and the rebuild
spends one more unit of β at its bottom (the carry
recursion of §5) than the previous cycle did.

## 7. Consequences for the assembled proof

1. **The β proviso is discharged — by refutation.** It is
   not the case that β ≥ 3 at all C-form right-sections.
   For every entry, β = 2 is reached after exactly
   β_E − 2 cycles, i.e. after ≈ 3·2^{β_E+1} steps in the
   regime. (For the entry the proof cannot yet pin down —
   β_E = s_entry + 2 for the exit section's shuttle
   s_entry — this is a finite, if enormous, horizon.)
2. **Strongest true β bound.** Within cycle k,
   β ≥ β_E − k at C-sections and β ≥ β_E − k − 2 at
   B-sections; β ≥ 3 at C-sections holds exactly through
   cycle β_E − 3. The right-edge regime is event-free and
   fully analysed from σ_re up to step T(β_E).
3. **The remaining gap moves.** Non-halting of #168016 now
   hinges on the continuation after the β = 2 exit, whose
   first section is (B, 4, (1^{β_E−2}), (2^{β_E−2})) in
   shifted coordinates (β′ = 4, all gaps 1, all runs 2).
   *Observation, not a claim:* this is formally a B-section
   of the same shape the mirror rules act on, one pair
   shorter and with β′ = 4; if the dynamics re-coordinatises
   at the new interface, the exit could act as a reset that
   re-enters a right-edge-like regime — analysing that is
   Phase 18's question, and nothing in this phase depends
   on it.
4. **Unchanged:** components #1–#13 of `168016-proof.md`,
   the unconditional bound ≈ 1.7709×10²¹ steps, and the
   fact that the real trajectory has not entered the
   right-edge regime (it is in the post-R I-regime; the
   entry is projected, not reached).

*Files for this phase: `phase17_model.py` (validated
word-level model), `phase17_run.py`, `phase17_run2.py`
(section-stream analyses), `phase17_cycles.py` (cycle
measurements), `p17-sre4.cfg`, `p17-sre6.cfg`,
`p17-sre8.cfg`, `p17-sre4-sec.log`, `p17-sre8-sec.log`.*
