# Machine #168016 does not halt — proof summary

**Status: DRAFT for community review (not yet posted).**
Prepared 2026-11-25 as a summary of the full proof record in this
repository (`168016-proof.md` and the derivation files listed in §9),
together with an independent reproduction (`reproduction-report.md`).

## 1. The machine and the result

The machine is the BB(6) holdout #168016 of the 2026-10-30 list of
608 machines:

```
1RB1RA_1RC1LB_0LD0RA_1RF1LE_---1LF_1LC0LF
```

| state | on 0 | on 1 |
|---|---|---|
| A | 1RB | 1RA |
| B | 1RC | 1LB |
| C | 0LD | 0RA |
| D | 1RF | 1LE |
| E | **HALT** | 1LF |
| F | 1LC | 0LF |

**Theorem.** *Started on the blank tape, this machine never halts.*

The only halting transition is E-on-0, so the whole proof is about
controlling where and in what context state E can read a 0.

**Halt criterion (lemmas M1–M4).** E is entered only from D-on-1.
D-on-0 is safe (it is the `1RF` transition) and is used by the proof
only inside left-edge probe ignitions whose entry contexts are
tracked explicitly. A case analysis of the entry contexts of C
(B-entry vs F-entry) and of the left triples at F-on-0 reads shows:
*the machine halts iff some F-on-0 read has left triple (0,1,0)*.
Every regime below is shown to produce only F-on-0 triples in
{(1,1,0), (1,1,1), (1,0,1), (0,0,0), (0,0,1), (0,1,1)} — never
(0,1,0) — and E-on-0 never occurs.

## 2. Overview of the argument

The trajectory is analysed in three large blocks.

1. **A finite transient** (exact simulation + two proved period
   engines) carries the blank tape through two "bounce families"
   S(k) and S′(m), a proved deviation at m = 132, and a 403,455-step
   computed segment to a configuration R =
   `1^17 0 1^97 0 1^137 0` (state B on the final 0), reached at step
   1,770,887,431,134,099,605,707.
2. **A deterministic pushdown regime after R.** From R the machine
   enters a two-regime system of word-level rules (a "standard"
   regime at the left working block and a mirror regime at the
   right edge), organised in *eras*. Each era ends by re-entering
   the mirror regime with a strictly larger parameter β. The
   token-pass analysis (Cycle Lemma) shows the mirror regime always
   exits at β = 2, and the post-exit continuation re-coordinatises
   into the standard regime.
3. **An ascending loop.** One full loop maps the mirror parameter
   β ↦ 2β + 34 (settled form; the exceptional first iterations have
   their own derived maps, β ↦ 2β + 4 and the deviated instance
   20 ↦ 50). The tape span grows by a constant at every cycle of
   the token pass and β strictly increases at every loop iteration,
   so no configuration ever repeats; with the halt criterion, the
   machine never halts.

Everything after R is a *derived rule system*: each rule is proved
by an explicit step list (a forced read of the transition table),
and the invariants are proved preserved. The finite computations
are exact simulations, independently reproduced (§7).

## 3. The transient: families S and S′, and the m = 132 break

**Family S(k)** (even k): tape `1^4 0 1^17 0 1^27 0 1^k 0`, head B
on the final 0. Exact simulation from the blank tape reaches S(k)
for every even k = 2…56 (S(56) at step 3,221,422,603); the period
S(k) → S(k+2) is P(k) = 3·2^((k+4)/2) − 6. At k = 56 the period
engine breaches the left edge of the wall (first crossing at
period-step 3,221,223,994) and the family ends; a computed
transient of 51,539,607,417 steps with no edge records ends at
S′(2). (This break is why the proof does not rest on the period
law alone: the law was verified for 27 consecutive periods and
still failed at the 28th.)

**Family S′(m)** (even m): tape `1^4 0 1^41 0 1^65 0 1^m 0`, head B
on the final 0, same period law P(m). Here the period *is* proved
for all even m ≤ 130: phases 1 and 3 are shift-rule arguments for
all m; phase 2 is proved via the midpoint split, the **Interval
Lemma** (chain decomposition of the universal cascade U_d, with
the Warm-up Lemma) and the **Return Lemma**. Hence S′(132) is
reached at step 885,443,715,596,040,733,867.

**The m = 132 deviation (analytic).** The phase-2 head-range law
(min head 111 − d at cascade depth d) first touches the separator
at d = 66. The configuration D(132,66) is computed in closed form:
tape `1^4 0 1^41 0 1 (0 1^2)^65 0 1^2` over [0,245], head C on cell
46 — a separator 0, where the engine expected a 1. It is reached
at period offset 3·2⁶⁸ − 9183 (real step
1,770,887,431,134,099,202,252). From D(132,66), **exact simulation
(403,455 steps)** reaches R = `1^17 0 1^97 0 1^137 0`.

**Formation.** From R, 150 computed steps reach the first section
of the standard regime (B2 = 97, s = 2, w = [1], G = 134, state C),
with a clean audit.

## 4. The standard regime (invariant I)

Sections are head local minima, read in the frame
`1^17 0 1^B2 0^{g0} 1^s Π(0^{gi} 1^{ri}) 0^G 1^2`. Five rules,
each derived from an explicit step list (the engine is the **Probe
Lemma**: the A/B/C/D/E/F probe at a 0-cell flanked by two 0s):

| rule | guard | effect | cost |
|---|---|---|---|
| TDN | C-section, g0 = 1 | B2 −= 2, s += 2 | 6 |
| PUSH | C-section, g0 ≥ 3 | B2 −= 1, prepend pair (g0 − 2, s) | 9 |
| POP | B-section, g1 = 1 | B2 += 1, s += r1 | 2s + 3 |
| TUP | B-section, g1 ≥ 3 | B2 += 2, probe; g0 := s − 1, g1 −= 2 | 2s + 6 |
| Stage A | B-section, w = [1], G ≥ 3 | B2 += 2, w := [s − 1], G −= 2 | 2s + 6 |

**Grind Lemma G′.** The grind of an odd residue m at a C-section
reaches (B, a − 2, m + 3, [1] + W, R, G) in exactly
2^((m+1)/2) − 1 rules; its dips are exactly
min a_C = a − (m − 1)/2 (attained only at g0 = 1 sections) and
min a_B = a − (m − 1)/2 − 2. These dip clauses are load-bearing:
they are what keeps the frame floor a ≥ 4 tight but unbroken
through every era (§6).

## 5. The mirror regime, the token pass, and the exit

At the right edge the working word W = (β; g1, r1, g2, r2, …)
evolves by five mirror rules (RTDN, RPUSH, RPOP, RTUP, RPROBE —
mirrors of the standard rules, plus the entry-like probe), under
invariant RI (odd gaps, even runs; C-form ⟹ r1 = 2; B-form ⟹
g1 = 1, r1 ≥ 4). **ENTRY** (standard regime, w = [1], G = 2) lands
the entry section σ_re(β) = (C, β, (1), (2)) at cost s + 12 with
β = s + 2.

**Cycle Lemma.** Let S_k(β) = (C, β, (2k + 1), (2)); note
σ_re(β) = S_0(β). For β ≥ k + 3, the orbit of S_k(β) reaches
S_{k+1}(β) in exactly D_k = 3·2^{k+3} − 4 steps; the minimum of β
over the cycle's C-sections is exactly β − k, attained at the
tokenless home section H_k = (C, β − k, (1^{k+1}), (2^{k+1})); the
span grows by 2 and β is restored at the cycle boundary. (Proof:
induction on k via the Suffix Lemma and the round map; the
B-start sequence of cycle k is two replays of cycle k − 1's.)

Consequently β = 2 *is* reached, in cycle β_E − 2 at
H_{β_E−2}, after T(β_E) = Σ_{j<β_E−2} D_j + off(β_E − 2) steps
(T(4) = 102, T(6) = 620, T(8) = 2,850). Six steps later the
machine is at the exit successor

X(β_E) = `1^17 0 1^31 0^2 1^4 (0 1^2)^{β_E−2}`, head B at cell 50

(on the real trajectory B2 = 31, from R's formation).

## 6. Re-coordinatisation and the era

From X(β_E) a three-stage computed/derived segment (RPOP chain,
token pass on the shifted word, escape) reaches the **canonical
section** (C, a = 18, s = 2, w = [29, 1^{β_E}], r = [1, 2^{β_E−1}],
G = 1) — in 760 steps at β_E = 6, 49,120 at 12, 786,384 at 16; the
settled span is 3β_E + 51. From there the era is fully derived:

* the absorption grind G′(29) (32,767 rules) and a POP chain whose
  first pop is the unique *defect* pop (r1 = 1) reach the REGEN
  source with s₁ = 2β_E + 31 at a = β_E + 16 — s₁ is odd *because
  of* the defect pop, which rules out the odd-G sub-case;
* **REGEN** (the composed map POP-list + blank Stage A + PUSHdeg,
  cost 4s + 22) restarts the grind era;
* the Stage-A era keeps s + G = s₁ + 3 constant, G even decreasing
  by 2, until ENTRY at G = 2 lands σ_re(β′) with
  **β′ = s₁ + 3 = 2β_E + 34**.

The frame floor is exactly tight: min a over C-sections in both
grind eras is 4, attained only at g0 = 1 sections, where TDN is
exact (invariant I⁺).

**Boundary behaviour (the second loop iteration on).** From
iteration 2 the escape meets a single-block prefix and the
re-formation needs boundary forms of the rules (TDN at a = 2, POP
at a = 0 — both exact by their step lists' read sets), the transfer
POP2/TRANS2 chains, and the deviation excursions at PUSH-at-a = 2:
**PUSHX** (single-block frame; the source's local gap is always
exactly 3, by the predecessor lemma), **PX2A/PX2B** (prefixed
frames; PX2B at b ≥ 7 is the escape composed with the probe-prefix
theorem), and **CGAP2** (C-sections with g0 = 2). All are derived
in all cases; the era stack invariant (every run 2 except at most
one defect pair (1,1)) confines TRANS2 chains to k ≤ 2 with
r_k = 2 and proves the one underived TUP2 stage-2 shape
unreachable in era grinds. The single-block escape happens
exactly once (iteration 2), with era law β ↦ 2β + 4
(s_regen = 2β + 1); the deviated iteration-3 instance is derived
explicitly (s_regen = 47, era constant 50, β″ = 50 > 20). In all
families **s_regen + 3 > β**, which is the era's contribution to
the ascent.

## 7. Independent reproduction

The proof was reproduced independently in Phase 22
(`reproduce_168016.py`, a clean-room checker written from the
documents alone; full details in `reproduction-report.md`):

* 75 checks, **0 failures**. ≈ 186,000 sections classified
  rule-by-rule against a fresh step simulator, and > 3×10⁸ steps
  of direct simulation, with the M1–M4 event audit clean
  throughout (E-on-0 = 0, no (0,1,0) F-on-0 triple).
* All headline numbers recomputed exactly: the arrival tables and
  period law, S′(132) at 885,443,715,596,040,733,867, D(132,66)
  and R step counts, D(132,66) → R in 403,455 steps, formation in
  150 steps, T(4) = 102, T(8) = 2,850, segment costs
  760 / 49,120 / 786,384, span 3β_E + 51, s₁ = 2β_E + 31,
  β′ = 2β_E + 34, β_next = 2β + 4.
* Held-out parameter values (never used in the original phases)
  were verified against the table: token pass at β_E = 10, 14, 18;
  era at β_E = 10, 14, 20; PX2B at b = 11, 15; PX2A at (6, 11);
  PUSHX at r1 = 4; ESC at (18, 10), (26, 8).
* Two discrepancies were found, both in statements the theorem
  does not use, reported exactly in the reproduction report and
  **not** patched: (i) the finite corollary's printed bound
  (1,770,888,448,134,502,657,707) contains a ×1000 slip in its
  last addend — the run-supported bound is
  1,770,887,432,151,100,008,759; (ii) the composed cost of the
  CGAP2 probe chain is 4 + 2r₁ + 6, not the 4 + (r₁ + 2) + 6 of
  the document's recursive accounting (CGAP2 is proved never to
  fire in era grinds).
* Update (Phase 23, 2026-11-25): both corrections have now
  been applied as dated errata — F-1 in `168016-proof.md`
  and `third-family.md`, F-2 in `phase21-derivations.md`
  §5. The findings remain recorded here and in the
  reproduction report; nothing was silently rewritten.

## 8. What is hand proof and what is computation

*Hand proof (shift rules / induction, in the derivation files):*
the halt criterion M1–M4; phases 1 and 3 of both period engines;
the S′ phase-2 Interval and Return Lemmas; the Probe Lemma and
all five standard rules + invariant I; Stage A, POP-general,
REGEN; all five mirror rules + invariant RI; the Cycle Lemma
(Suffix Lemma, round map, induction on k); the era assembly and
the odd-G exclusion; the Grind Lemmas G′ and G″ with the dip
clauses; the boundary forms, PUSHX/PX2A/PX2B, TRANS2/TUP2 chains,
CGAP2, and the era stack invariant with its unreachability
consequences; the loop ascent.

*Machine-checked computation (exact simulation, independently
reproduced):* the blank-tape trajectory to S(56) and the breach
record; the transient to S′(2); the S′ arrivals to m = 68 in the
original runs (the induction itself is proved, not simulated,
beyond the feasible envelope); D(132,66) → R (403,455 steps);
formation (150 steps); the post-R segment and era verifications
and rule batteries listed in the reproduction report.

*Mechanisation (Phases 23/25–33, in progress):* a Rocq (Coq 8.18)
development is under way (`rocq/`). Already proved there,
with no axioms or admits: the halt criterion M1–M4 in full; the
finite segments D(132,66) → R (403,455 steps), formation
(150 steps), T(4) = 102 and T(8) = 2,850, and small S/S′
arrivals, by kernel computation; the soundness of all five
standard-regime rules (TDN, PUSH, POP-general, TUP, Stage A)
and of REGEN for all parameters; the right-edge entry
excursion and all five mirror rules (RTDN, RPUSH, RPOP, RTUP,
RPROBE) with the invariant RI; the token pass — the Cycle
Lemma Γ with duration D_k = 3·2^{k+3} − 4, the home-section
attainment H_k, and the general β = 2 exit; the
re-coordinatisation in full — stages 1 and 3, the general
stage 2 (the diagonal token pass, proved for every frozen
prefix; the seven kernel-verified instances remain as
regression checks), and the unconditional composition; the era law — the Grind Lemma G′, with
s₁ = 2β_E + 31, the odd-G case excluded, and the loop map
β′ = 2β_E + 34; the single-block escape pieces (POP2 in full
generality, the probe prefix E1–E5); and the complete
deviation system of §7's grind — every step list (PUSHX,
PX2A/PX2B, the CGAP2 probe and dispatches, the TRANS2/TUP2
chains, and the TUP2 defect) proved for all parameters, the
hybrid word model with its soundness theorem, the grind
prefix reductions, and the Predecessor case analysis; and
(Phase 29) the G″ endpoint induction — the clean-regime
endpoint for all frames under its floor and the deviated
boundary grind as a proved induction — the era stack
invariant with the Predecessor Lemma discharged in-grind,
and the ESC-family era law β_next = 2β + 4 for
R ∈ {2, 4, 6, 8, 10}; and (Phase 31) the re-basing
segment REBASE of the R ≥ 12 grind — proved from a
corrected source (finding F-4: the Phase 29 fence's
statement had g0 = 11 for g0 = 12, an off-by-one the
model traces caught before proving) — extending the
ESC-family era law to every even R ≤ 40. (The
defect's mechanised landing is the machine-corrected form —
finding F-3, a dated erratum in `phase21-derivations.md` §4;
the defect is unreachable in era grinds, so the theorem is
unaffected.) And (Phase 32) the **cross-era loop assembly**:
the exit and re-coordinatisation stages composed for an
arbitrary frozen prefix, both era iterations as loop steps
(settled β ↦ 2β + 34 at the trajectory prefix; ESC
β ↦ 2β + 4 for R ≤ 40), the first two iterations composed
in full (β ↦ 4n + 80), an abstract ascending-loop engine
(iteration at every entry section implies the run is
total), and non-halting from the record configuration R —
the formation segment kernel-verified — modulo two
explicit hypotheses stated as lemma parameters (never
axioms): the standard regime's remaining assembly (it
reaches an entry landing from the first I-section), and
iteration at the entry sections not yet discharged (the
general-residue era law inside the general settled
iteration, ESC entries at R ≥ 116, and iterations ≥ 3).
And (Phase 33) the **second re-basing** of the G″ grind:
the deviated grind at prefix [5] (base case the PX2B row
b = 5, not PUSHX), an even-g0 grind, and a third phase of
clean rounds, extending the ESC-family era law to every
even R ≤ 114 and discharging the ESC loop iterations in
that range. And (Phase 34) the **standard regime's
assembly** (hypothesis H_STD of the loop assembly): from
the first I-section (B2 = 97, s = 2, w = [1], G = 134) the
regime is one word-model chain — TDN, a Stage A collapse,
65 grind/collapse cycles (Grind Lemma G′ followed by
Stage A; G: 134 → 2 over 66 collapses in all) and a final
grind — reaching the ENTRY source and hence the entry
landing entry_tgt 95 136, so non-halting from R now
rests on the single remaining hypothesis H_LOOP
(iteration at the entry sections not yet discharged).
And (Phase 35) the **general-residue era law**
(ERA_GEN): the era law at a general residue ρ, proved on
its exact domain — every odd ρ ≤ 33, every era parameter
m ≥ 1 — by ERA_LAW's assembly at ρ = 2t + 1 (absorption
by the residue grind, resp. a single TDN at ρ = 1;
s₁ = ρ + 2β_E + 2, β′ = ρ + 2β_E + 5), discharging the
general settled iteration unconditionally for odd
B2 ≤ 35. Even residues and ρ ≥ 35 are fenced with
machine-checked obstructions: the absorption landing is
never reached at ρ = 30 or ρ = 35 in 20,000,000
simulated steps (the residue grind's dip exceeds the
frame a2 = 16, and Lemma G′ is odd-only).
And (Phase 36) the **third re-basing's dip bottoms**:
the boundary grind at prefix [20; 0] (R = 116) dips to
the section HC [20; 0] 0 3 2 no word-model rule covered;
the dispatch there is a new machine-level deviation step
list, PX2A0 (for every b ≥ 5, HC [b; 0] 0 3 2 runs in
b + 32 steps to HB [0] 3 1 2 over the residue pair
(b − 4, 2) and the usual extras), derived by direct
zipper tracing and proved for all parameters, and the
unwind's own dip bottom HC [0] 0 3 2 has a second new
step list, PX2B0 (20 steps), with the deviated grind at
prefix [0] proved as an induction (hGRIND_dev0). The
R ≥ 116 era law itself was not yet assembled at that
point: the [20; 0] grind's base step consumes the
prefix and leaves the residue pair (16, 2), so its
endpoint had to be assembled through the merged
unwind.
And (Phase 37) that **merged unwind is assembled**:
the R = 116 endpoint is an explicit chain (the phase-3
prefix, 34 phase-3 rounds, the descent of the [20; 0]
grind, PX2A0 at the dip, and the (16, 2) grind at
prefix [0] over the carried era stack), and the
pattern continues through phase 4 (R = 118) and
phase 5 (R = 2m + 46, 38 ≤ m ≤ 111), giving the
ESC-era law β_next = 2β + 4 for **every even R ≤ 268**
(ESC_ERA_LAW_268), with the corresponding loop
iterations discharged in Loop.v (ESC_ITER_268). The
remaining fence is R ≥ 270, where phase 5's final
grind becomes a boundary grind at the three-block
prefix [41; 14; 5] — a phase-6 deviation not yet
derived (`rocq/mechanisation-status.md`).
And (Phase 38) the **phase-6 boundary grind is
closed**: the boundary descent at t = a2 is a
general lemma (DIPDESC: for every t, every prefix
and every stack, the grind descends to its dip with
the stack grown by (1, 2)^t — no floor hypothesis),
its dip at [41; 14; 5] fires the existing PX2A
dispatch, and the continuation grind at the new
frame is assembled explicitly (GRIND39_MID),
extending the ESC-era law to **every even R ≤ 602**
(ESC_ERA_LAW_602), with the corresponding loop
iterations discharged in Loop.v (ESC_ITER_602). The
phase recursion does not admit a general induction
over phase depth in the current lemma vocabulary —
each phase's dip dispatch is a case split on the
literal prefix blocks and its landing parameters
are arithmetic accidents of those blocks — so the
remaining fence is R ≥ 604, a phase-7 deviation of
the same character (`rocq/mechanisation-status.md`
states the verdict precisely).
And (Phase 39) the **even-residue era law**: at an even
residue the absorption does not grind the residue into
the shuttle — when the residue pair reaches gap 2, the
TUP-prefix excursion itself fires as a **frame
rotation** (the shuttle becomes the new near block, the
pair is consumed), landing on a B-section over the
two-block frame with near block exactly ρ and s still
2. Hence s₁ = 2m + 1, the Stage-A era's G₀ = 2m is even
unconditionally, and β′ = 2m + 4 is **independent of
ρ** — the same closed form as the ESC-era law. The law
is proved for every even ρ ≤ 34 and every m ≥ 1
(EVEN_GRIND, ERA_GEN_even in `EraEven.v`; the odd
grind over a general frame, gGRIND, is proved along
the way), discharging the general settled iteration
unconditionally for even B2 with 4 ≤ B2 ≤ 36
(SETTLED_ITER_GEN_even in Loop.v). With Phase 35, the
settled iteration is now unconditional for **every
B2 with 3 ≤ B2 ≤ 36**. Residues ρ ≥ 35 (B2 ≥ 37) are
fenced with machine evidence in both parities: ρ = 35
absorbs only after a sub-frame edge excursion grows
the frame (landing bsec 17 1 39, after which the era's
G parity obstructs), ρ = 36, 37, 39, 41 absorb by
rotation onto a two-block frame of a different shape,
and ρ = 38, 40 show no absorption landing of either
form within 60,000,000 steps — mechanising them needs
a sub-frame edge-grind theory the current vocabulary
does not contain (`rocq/mechanisation-status.md`).
And (Phase 40) the **phase-7 merged unwind** on the ESC
side: at the phase-6 finish's new frame the maximal
164 clean rounds leave the final grind at exactly
t = a2, a boundary descent (DIPDESC) whose dip fires
the existing PX2A dispatch, and the continuation
grind at g0 = 108 is assembled explicitly
(GRIND108_MID in `Grind8.v`), extending the ESC-era
law to **every even R ≤ 1276** (ESC_ERA_LAW_1276),
with the corresponding loop iterations discharged in
Loop.v (ESC_ITER_1276). No new deviation step list
was needed. The remaining ESC fence is R ≥ 1278, a
phase-8 deviation of the same character.
And (Phase 41) the **phase-8 entry** itself: every
entry with m ≥ 616 takes the maximal 334 rounds at
frame ([235; 42; 19], 334) — there are no phase-8
finishes — and the funnel (`PHASE8_TO_MID` in
`Grind9.v`) plus the continuation's first three
stages (stages A–C, each over an arbitrary carried
rest) are mechanised. Two general additions were
needed: a new deviation step list `PX2Bgen`
(Dev.v; the uniform PX2B dispatch at a single
block [b], b ≥ 5, cost b + 32) for stage A's dip
at [19], and the even boundary descent
`DIPDESC_even` (Grind9.v). Past stage C's landing,
however, the continuation is **not** of the same
character as phases 6–8: it consumes the entire
remaining passenger stack and cascades through a
growing frame with no closed form, ending (at the
verified analogues) at a B-section over the empty
stack where the word model has no rule — a
full-stack cascade, fenced with machine evidence
in `rocq/hsim41.py`. The ESC-era law therefore
still closes at R ≤ 1276; closing phase 8 needs a
totality/landing theorem for the
deviation-inclusive grind, not another unwind.
And (Phase 42) the **landing theorem attacked
directly** — with a correction to Phase 41's
reading: the cascade's terminal configuration
*is* the era-landing shape `HB pb a 1 (2β + 1)
[] 1` (the target of every ESC_TO_REGEN lemma,
closed at machine level by REGEN for arbitrary
prefixes), so over the era-shaped stack family
the landing is the precise statement
**CASCADE_LANDING**. It is stress-tested in
`rocq/hsim42.py` (~50 shrunk-family landings,
all on the era shape; machine REGEN confirmed at
the terminal; and a genuine parity fence — for
odd residues the landing shuttle is 2β + r, not
2β + 1, so the closed form is an even-residue
phenomenon). The cascade's last two stages are
proved in general (`CASCADE_STAGE4`,
`CASCADE_POPFIN` in `Grind10.v`), and the
phase-8 era law for **every even R ≥ 1278** is
proved modulo CASCADE_LANDING
(`ESC_ERA_LAW_42`), with the loop iterations
discharged in Loop.v (`ESC_ITER_BIG8`). The
remaining core is the cascade's first three
stages, whose parses are parameter-dependent:
a proof needs a totality theorem for the
segment grind itself.
And (Phase 43) those **first three stages are
proved in the era regime** — the regime the
trajectory actually presents, where the first
residue is odd. The odd pair is ground by a new
g0 = 1 totality (`GG_odd`: grind_prefix + an
induction over the grind rounds, over an
arbitrary deeper tail, with one explicit floor),
stage 1 is a fixed step list, stages 2+3 merge
into one lemma with two small dispatch branches
(the r2 = 2 and r2 = 4 residues), and stage 4
splits into a clean regime (M ≤ 1440, Phase 42),
a degenerate M = 618 branch, and the boundary
regime M ≥ 1441, where the grind exhausts its
counter budget and re-routes through dips.
Every stage boundary was machine-checked on the
shrunk family first (`rocq/hsim43.py`). The
result (`Grind11.v`): CASCADE_LANDING is proved
modulo the strictly smaller statement
**CASCADE_STAGE4_BIG** — the landing of the
single pair (2M − 1234, 2) at the one fixed era
frame [428; 57; 5], counter 822, for M ≥ 1441 —
and the era law / loop iterations are discharged
modulo that core (`ESC_ERA_LAW_43`,
`ESC_ITER_BIG8_43`).
And (Phase 44) the **stage-4 boundary grind is
characterised at the general 3-block frame**
[f; p; 5] and mechanised segment by segment
(`rocq/hsim44.py`: every segment boundary asserted
verbatim in the walk histories before
mechanisation). Its engine is a new dip-aware
rounds totality (`GG_boundary`: the clean rounds
run a − 1 times, then the budget-exhaustion round
re-routes through the DIPDESC descent), and the
segments SEG1 (boundary grind + PX2A re-basing),
SEG2 (PUSH + boundary grind + PX2B5), T1, T2,
T3 (the era regime's second boundary grind +
PX2A0) and T4 (the PX2B0 dip onto the bottom
frame []) are all proved. The result
(`Grind12.v`): CASCADE_STAGE4_BIG is proved
modulo the strictly smaller statement
**CASCADE_STAGE4_TAIL** — the tail traversal at
the bottom frame [] from
`HB [] 0 1 5 (TAILs q v3 vM a β) 1` to the era
landing, with the era parities baked in — and
the era law / loop iterations are discharged
modulo that core (`ESC_ERA_LAW_44`,
`ESC_ITER_BIG8_44`).
And (Phase 45) the **tail is mechanised at the
era slice** (28, 34, 822) — the only
instantiation of CASCADE_STAGE4_TAIL the proof
uses (`rocq/hsim45.py`: primitive walks from the
tail source, macro walks with every layer
boundary asserted verbatim). Its three layers
are proved (`Grind13.v`): layer 0 (two
GG_boundary grinds and the PX2Bgen dip), layer 1
(the hGRIND_even 119 descent), and the layer-2
residue in the clean range vM ≤ 1652. The
result: CASCADE_STAGE4_BIG is proved modulo the
strictly smaller statement **TAIL2_BIG** — the
layer-2 residue totality at the single fixed
state `HB [243; 135; 35; 20; 0] 893 1 1651`,
for the boundary range vM ≥ 1653 only — and
the era law / loop iterations are discharged
modulo that core (`ESC_ERA_LAW_45`,
`ESC_ITER_BIG8_45`). The universal
CASCADE_STAGE4_TAIL remains unproved; it is
strictly stronger than the proof needs.
And (Phase 46) the **TAIL2_BIG descent is
mechanised** (`rocq/hsim46.py`: all 51 descent
waypoints asserted verbatim). The descent from
the PX2A landing is a fixed parse, uniform in
(k, β) with k = vM − 1652 — four dip levels
closed by the new DIPGRIND lemma — landing on
the END state
`HB [317; 40; 14; 5] 2204 1 3711`, which closes
uniformly for k ≤ 3713 (`Grind14.v`). The
result: TAIL2_BIG is **proved for
1653 ≤ vM ≤ 5365**, and for vM ≥ 5366 the era
law / loop iterations are discharged modulo the
strictly smaller statement **TAIL2_END** — the
totality of the one pair (2k, 2) at the one
fixed END state, k ≥ 3714 only
(`ESC_ERA_LAW_46`, `ESC_ITER_BIG8_46`).
And (Phase 47) the **END re-descent is
mechanised** (`rocq/hsim47.py`: the 37-waypoint
chain asserted verbatim at eight (k, β) points;
the cycle-2 fence at k = 11143 / 12000 / 20000).
The re-descent is **not** a return to the END
state — no END-shaped configuration recurs —
it is another fixed parse, uniform in (k, β):
the END front and DIPGRIND (3710, ρ) with
ρ = 2(k − 3713), then the 34-segment
**CASCADE47** at an arbitrary carried tail,
landing on the TOP state
`HB [1279; 745; 151; 77; 35; 20; 0] 4001 1 7427`,
which closes at ρ = 2, 4, 6 and throughout
band 1 (ρ ≤ 14858, the pair grinding cleanly
by CLEANG_even at counter 7426) (`Grind15.v`).
The result: TAIL2_END is **proved for the
whole first band 3714 ≤ k ≤ 11142**, and for
k ≥ 11143 the era law / loop iterations are
discharged modulo the strictly smaller
statement **TAIL2_END2** — the totality of
the one pair (2j, 2) at the one fixed TOP
state, j ≥ 7430 only, where the second
descent is a new cascade with different
constants, so the bands are finite parses
rather than a cycle induction
(`ESC_ERA_LAW_47`, `ESC_ITER_BIG8_47`).
And (Phase 48) the **TOP second descent is
mechanised** (`rocq/hsim48.py`: the 26-waypoint
CASCADE48 chain asserted verbatim at six (j, β)
points, incl. a junk-tail probe; the third fence
at j = 23731 / 24000 / 30000). The second descent
is again a fixed parse, uniform in (j, β): the
TOP front and DIPGRIND (7426, 2(j − 7429)), then
the 24-segment **CASCADE48** at an arbitrary
carried tail, landing on the TOP2 state
`HB [1589; 225; 40; 14; 5] 10430 1 16299`,
which closes at r = 2, 4, 6 and throughout
band 2 (r ≤ 32602, the pair grinding cleanly
by CLEANG_even at counter 16298 — the shuttle
moved into the counter slot by TUP2_1)
(`Grind16.v`). The result: TAIL2_END2 is
**proved for 7430 ≤ j ≤ 23730**, and for
j ≥ 23731 the era law / loop iterations are
discharged modulo the strictly smaller
statement **TAIL2_END3** — the totality of
the one pair (2j, 2) at the one fixed TOP2
state, j ≥ 16302 only, where the third
descent is a new cascade with different
constants (`ESC_ERA_LAW_48`, `ESC_ITER_BIG8_48`).
And (Phase 49) the **TOP2 third descent is
mechanised** (`rocq/hsim49.py`: the 49-waypoint
CASCADE49 chain asserted verbatim at five (j, β)
points, incl. a junk-tail probe; the fourth fence
at j = 48907 / 49000 / 60000). The third descent
is again a fixed parse, uniform in (j, β): the
TOP2 front and DIPGRIND (16298, 2(j − 16301)),
then the 47-segment **CASCADE49** at an arbitrary
carried tail, landing on the TOP3 state
`HB [7493; 3816; 259; 93; 50; 14; 5] 16899 1
32603`, which closes at r3 = 2, 4, 6 and
throughout band 3 (r3 ≤ 65210, the pair grinding
cleanly by CLEANG_even at counter 32602 — the
shuttle moved into the counter slot by TUP2_1)
(`Grind17.v`). The result: TAIL2_END3 is
**proved for 16302 ≤ j ≤ 48906**, and for
j ≥ 48907 the era law / loop iterations are
discharged modulo the strictly smaller
statement **TAIL2_END4** — the totality of
the one pair (2j, 2) at the one fixed TOP3
state, j ≥ 32606 only, where the fourth
descent is a new cascade with different
constants (`ESC_ERA_LAW_49`, `ESC_ITER_BIG8_49`).
And (Phase 50) the **TOP3 fourth descent is
mechanised** (`rocq/hsim50.py`: the 82-waypoint
CASCADE50 chain asserted verbatim at five (j, β)
points, incl. a junk-tail probe; the fifth fence
at j = 99729 / 99800 / 120000). The fourth descent
is again a fixed parse, uniform in (j, β): the
TOP3 front and DIPGRIND (32602, 2(j − 32605)),
then the 64-segment **CASCADE50** at an arbitrary
carried tail, landing on the TOP4 state
`HB [9558; 1285; 774; 112; 20; 0] 47594 1
67121`, which closes at r4 = 2, 4, 6 and
throughout band 4 (r4 ≤ 134246, the pair grinding
cleanly by CLEANG_even at counter 67120 — the
shuttle moved into the counter slot by TUP2_1)
(`Grind18.v`). The result: TAIL2_END4 is
**proved for 32606 ≤ j ≤ 99728**, and for
j ≥ 99729 the era law / loop iterations are
discharged modulo the strictly smaller
statement **TAIL2_END5** — the totality of
the one pair (2j, 2) at the one fixed TOP4
state, j ≥ 67124 only, where the fifth
descent is a new cascade with different
constants (`ESC_ERA_LAW_50`, `ESC_ITER_BIG8_50`).
And (Phase 51) the **TOP4 fifth descent is
mechanised** (`rocq/hsim51.py`: the 16-waypoint
CASCADE51 chain asserted verbatim at five (j, β)
points, incl. a junk-tail probe; the sixth fence
at j = 201373 / 201374 / 210000). The fifth descent
is again a fixed parse, uniform in (j, β): the
TOP4 front and DIPGRIND (67120, 2(j − 67123)),
then the 12-segment **CASCADE51** at an arbitrary
carried tail, landing on the TOP5 state
`HB [20403; 10332; 112; 20; 0] 95597 1
134247`, which closes at r5 = 2, 4, 6 and
throughout band 5 (r5 ≤ 268498, the pair grinding
cleanly by CLEANG_even at counter 134246 — the
shuttle moved into the counter slot by TUP2_1)
(`Grind19.v`). The result: TAIL2_END5 is
**proved for 67124 ≤ j ≤ 201372**, and for
j ≥ 201373 the era law / loop iterations are
discharged modulo the strictly smaller
statement **TAIL2_END6** — the totality of
the one pair (2j, 2) at the one fixed TOP5
state, j ≥ 134250 only, where the sixth
descent is a new cascade with different
constants (`ESC_ERA_LAW_51`, `ESC_ITER_BIG8_51`).

A sixth boundary descent has since been
mechanised the same way: the TOP5 front, then
DIPGRIND (134246, 2(j − 134249)), then the
227-step **CASCADE52** at an arbitrary carried
tail, landing on the TOP6 state
`HB [23252; 3931; 2847; 569; 287; 14; 5]
175058 1 323287`, which closes at r6 = 2, 4, 6
and throughout band 6 (r6 ≤ 646578, the pair
grinding cleanly by CLEANG_even at counter
323286) (`Grind20.v`). The result:
TAIL2_END6 is **proved for
134250 ≤ j ≤ 457538**, and for j ≥ 457539 the
era law / loop iterations are discharged
modulo the strictly smaller statement
**TAIL2_END7** — the totality of the one
pair (2j, 2) at the one fixed TOP6 state,
j ≥ 323290 only, where the seventh descent
is a new cascade with different constants
(`ESC_ERA_LAW_52`, `ESC_ITER_BIG8_52`).

A seventh boundary descent has since been
mechanised the same way: the TOP6 front, then
DIPGRIND (323286, 2(j − 323289)), then the
337-step **CASCADE53** at an arbitrary carried
tail, landing on the TOP7 state
`HB [109099; 62236; 6030; 630; 191; 113; 33;
19; 0] 350961 1 646579`, which closes at
r7 = 2, 4, 6 and throughout band 7
(r7 ≤ 1293162, the pair grinding cleanly by
CLEANG_even at counter 646578) (`Grind21.v`).
The result: TAIL2_END7 is **proved for
323290 ≤ j ≤ 969870**, and for j ≥ 969871 the
era law / loop iterations are discharged
modulo the strictly smaller statement
**TAIL2_END8** — the totality of the one
pair (2j, 2) at the one fixed TOP7 state,
j ≥ 646582 only, where the eighth descent
is a new cascade with different constants
(`ESC_ERA_LAW_53`, `ESC_ITER_BIG8_53`).

An eighth boundary descent has since been
mechanised the same way: the TOP7 front, then
DIPGRIND (646578, 2(j − 646581)), then the
176-step **CASCADE54** at an arbitrary carried
tail, landing on the TOP8 state
`HB [135142; 27487; 14322; 1260; 147;
20; 0] 864782 1 1425923`, which closes at
r8 = 2, 4, 6 and throughout band 8
(r8 ≤ 2851850, the pair grinding cleanly by
CLEANG_even at counter 1425922) (`Grind22.v`).
The result: TAIL2_END8 is **proved for
646582 ≤ j ≤ 2072506**, and for j ≥ 2072507 the
era law / loop iterations are discharged
modulo the strictly smaller statement
**TAIL2_END9** — the totality of the one
pair (2j, 2) at the one fixed TOP8 state,
j ≥ 1425926 only, where the ninth descent
is a new cascade with different constants
(`ESC_ERA_LAW_54`, `ESC_ITER_BIG8_54`).

A ninth boundary descent has since been
mechanised the same way: the TOP8 front, then
DIPGRIND (1425922, 2(j − 1425925)), then the
17-step **CASCADE55** at an arbitrary carried
tail, landing on the TOP9 state
`HB [297773; 149464; 1260; 147;
20; 0] 2020419 1 2851851`, which closes at
r9 = 2, 4, 6 and throughout band 9
(r9 ≤ 5703706, the pair grinding cleanly by
CLEANG_even at counter 2851850) (`Grind23.v`).
The result: TAIL2_END9 is **proved for
1425926 ≤ j ≤ 4277778**, and for j ≥ 4277779 the
era law / loop iterations are discharged
modulo the strictly smaller statement
**TAIL2_END10** — the totality of the one
pair (2j, 2) at the one fixed TOP9 state,
j ≥ 2851854 only, where the tenth descent
is a new cascade with different constants
(`ESC_ERA_LAW_55`, `ESC_ITER_BIG8_55`).

A tenth boundary descent has since been
mechanised the same way: the TOP9 front, then
DIPGRIND (2851850, 2(j − 2851853)), then the
799-step **CASCADE56** at an arbitrary carried
tail, landing on the TOP10 state
`HB [652285; 206767; 138671; 25145; 13306; 4643;
2871; 335; 235; 42; 19] 4042956 1 5937475`, which closes at
r10 = 2, 4, 6 and throughout band 10
(r10 ≤ 11874954, the pair grinding cleanly by
CLEANG_even at counter 5937474) (`Grind24.v`).
The result: TAIL2_END10 is **proved for
2851854 ≤ j ≤ 8789330**, and for j ≥ 8789331 the
era law / loop iterations are discharged
modulo the strictly smaller statement
**TAIL2_END11** — the totality of the one
pair (2j, 2) at the one fixed TOP10 state,
j ≥ 5937478 only, where the eleventh descent
is a new cascade with different constants
(`ESC_ERA_LAW_56`, `ESC_ITER_BIG8_56`).

An eleventh boundary descent has since been
mechanised the same way: the TOP10 front, then
DIPGRIND (5937474, 2(j − 5937477)), then the
17-step **CASCADE57** at an arbitrary carried
tail, landing on the TOP11 state
`HB [1511339; 790956; 25145; 13306; 4643;
2871; 335; 235; 42; 19] 8675859 1 11874955`, which closes at
r11 = 2, 4, 6 and throughout band 11
(r11 ≤ 23749914, the pair grinding cleanly by
CLEANG_even at counter 11874954) (`Grind25.v`).
The result: TAIL2_END11 is **proved for
5937478 ≤ j ≤ 17812434**, and for j ≥ 17812435 the
era law / loop iterations are discharged
modulo the strictly smaller statement
**TAIL2_END12** — the totality of the one
pair (2j, 2) at the one fixed TOP11 state,
j ≥ 11874958 only, where the twelfth descent
is a new cascade with different constants
(`ESC_ERA_LAW_57`, `ESC_ITER_BIG8_57`).
**Not yet claimed:** a complete
mechanised proof — the S/S′ inductions, the dip clause of G′, the
ESC entries at R ≥ 1278 (the ESC-era law is proved
through R ≤ 1276 unconditionally, and for every
even R ≥ 1278 modulo the single statement
TAIL2_END12 — the totality of one pair (2j, 2)
at the one fixed TOP11 state
`HB [1511339; 790956; 25145; 13306; 4643;
2871; 335; 235; 42; 19] 8675859 1 11874955`, j ≥ 11874958 —
via the tail at the era slice and the descent in
Grind14.v, which proves the previous core
TAIL2_BIG for vM ≤ 5365, the END re-descent
in Grind15.v, which proves the previous core
TAIL2_END for 3714 ≤ k ≤ 11142, the TOP
second descent in Grind16.v, which proves the
previous core TAIL2_END2 for 7430 ≤ j ≤ 23730,
and the TOP2 third descent in Grind17.v, which
proves the previous core TAIL2_END3 for
16302 ≤ j ≤ 48906, and the TOP3 fourth descent
in Grind18.v, which proves the previous core
TAIL2_END4 for 32606 ≤ j ≤ 99728, and the
TOP4 fifth descent in Grind19.v, which proves
the previous core TAIL2_END5 for
67124 ≤ j ≤ 201372, and the TOP5 sixth
descent in Grind20.v, which proves the
previous core TAIL2_END6 for
134250 ≤ j ≤ 457538, and the TOP6 seventh
descent in Grind21.v, which proves the
previous core TAIL2_END7 for
323290 ≤ j ≤ 969870, and the TOP7 eighth
descent in Grind22.v, which proves the
previous core TAIL2_END8 for
646582 ≤ j ≤ 2072506, and the TOP8 ninth
descent in Grind23.v, which proves the
previous core TAIL2_END9 for
1425926 ≤ j ≤ 4277778, and the TOP9 tenth
descent in Grind24.v, which proves the
previous core TAIL2_END10 for
2851854 ≤ j ≤ 8789330, and the TOP10 eleventh
descent in Grind25.v, which proves the
previous core TAIL2_END11 for
5937478 ≤ j ≤ 17812434;
the phase-8 entry, its first
three continuation stages, the cascade's stages
1–3 and its last two stages are formalised in
Grind9.v / Grind10.v / Grind11.v, the stage-4
boundary grind's segments in Grind12.v, the
tail's layers in Grind13.v, the TAIL2_BIG
descent in Grind14.v, the END re-descent in
Grind15.v, the TOP second descent in
Grind16.v, the TOP2 third descent in
Grind17.v, the TOP3 fourth descent in
Grind18.v, the TOP4 fifth descent in
Grind19.v, the TOP5 sixth descent in
Grind20.v, the TOP6 seventh descent in
Grind21.v, the TOP7 eighth descent in
Grind22.v, the TOP8 ninth descent in
Grind23.v, the TOP9 tenth descent in
Grind24.v, and the TOP10 eleventh descent in
Grind25.v), and the
general-residue era law at residues ρ ≥ 35 (both
parities) are not yet formalised
(`rocq/mechanisation-status.md` maps every proof component to
its mechanisation status). The finite corollary bound is a
by-product; the theorem is the unconditional non-halting
statement of §1.

## 9. Files

*(Packaging note: in this submission package, `168016-proof.md`
and this summary sit at the top level, the derivation files
under `proof/`, the reproduction under `reproduction/`, and the
Rocq sources under `rocq/`.)*

* `168016-proof.md` — the full proof (theorem + component list).
* `proof-168016.md`, `postbreak-168016.md`,
  `sprime-phases-168016.md`, `sprime-phase2-proof.md`,
  `ud-proof.md`, `phase2-complete.md`, `m132-analysis.md`,
  `third-family.md`, `transient-analysis.md` —
  the transient and the two period engines, and the post-R
  entry point.
* `post-R-proof.md`, `bounce-derivation.md`,
  `reexpansion-derivation.md`, `rightedge-derivation.md`,
  `token-pass-derivation.md`, `post-exit-analysis.md`,
  `phase19-derivations.md`, `phase20-derivations.md`,
  `phase21-derivations.md` — the post-R regimes and the loop.
* `reproduce_168016.py`, `reproduction-report.md` — the
  independent reproduction (Phase 22).
* `rocq/` — the Rocq mechanisation (Phases 23/25–41): `TM.v`,
  `Configs.v`, `Finite.v`, `Sections.v`, `Mirror.v`, `TokenPass.v`,
  `DiagPass.v`, `Recoord.v`, `Era.v`, `EraGen.v`, `EraEven.v`,
  `Esc.v`, `Dev.v`,
  `Grind.v`, `Grind2.v`, `Grind3.v`, `Grind4.v`, `Grind5.v`,
  `Grind6.v`, `Grind7.v`, `Grind8.v`, `Grind9.v`, `Loop.v`, `Std.v`, and
  `mechanisation-status.md`.
* `NOTES.md` — the project log (Phases 1–41). *(Not included in
  this package — internal working log; available from the
  authors on request.)*
