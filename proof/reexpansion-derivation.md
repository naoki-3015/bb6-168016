# BB(6) holdout #168016 — deriving the re-expansion: Stage A and the composed section system (Phase 14, 2026-11-25)

- Seed index: **168016**
- Spec: `1RB1RA_1RC1LB_0LD0RA_1RF1LE_---1LF_1LC0LF`
- Starting point: Phase 12 (`post-R-proof.md`) reduced the
  post-R halt to one tape pattern (lemma M4) and found the
  section invariant **I**, but listed as **obstruction 2**
  that re-expansion after a collapse is not proven to restore
  I: a collapse is a regime transition
  (w, G) → (w′, G − 2) with w′ a *regenerated* stack, verified
  for two full cycles but not derived. Phase 13
  (`bounce-derivation.md`) derived the four bounce rules
  (TDN / PUSH / POP / TUP) under hypotheses H1–H3 and showed
  (§5.3) that the H3 boundary — a B-section with no pair after
  the shuttle — is the collapse, in one shallow synthetic
  instance. **This phase derives that boundary excursion in
  general (Stage A), and with it the whole collapse cycle.**

**Verdict up front.** Obstruction 2 is **closed**. The key
point is a reframing: invariant I is never lost at a section.
The collapse's own end section σ_coll — a B-section with
w = [1] whose tape is the merged block — already satisfies
I; it violates only Phase 13's hypothesis H3. Its excursion
is derived below as **Stage A**: a closed-form shift-rule
computation, parameterised by the merged tape
(B2c, L, G), with cost exactly **2L + 6**, ending at the
C-section σ₂ with w = [L − 1] and G reduced by 2. Every
section transition of the standard regime is therefore one
of **five derived rules** (the four of Phase 13, plus
Stage A), I is an inductive invariant of the machine's
section dynamics *across* collapses, and no excursion of
any of the five rules contains an E-on-0 or M4's pattern.
What Phases 11–12 called "re-expansion" (~10⁵–10⁶ steps)
is the grind-down of the residue L − 1 *inside* this proven
system (§4.3) — a fact about the tape's appearance, not a
gap in the invariant's coverage. The composed system is
proven up to its exact boundary: a Stage A entered at
G = 2, which is obstruction 3's entry point, pinpointed at
the section level in §4.4. Labels: (P) general proof from
the transition table, (C) exhaustive finite check,
(O) observation.

## 1. Setup: the post-collapse section σ_coll

Transition table (write, move, next state), as in Phase 13:

    A: 1RB 1RA     B: 1RC 1LB     C: 0LD 0RA
    D: 1RF 1LE     E:  —  1LF     F: 1LC 0LF        (— = halt)

Coordinates are the R frame. A **collapse section** is a
section (head local minimum, Phase 11 §1.1) whose tape is
the merged form

    1¹⁷ 0 1^B2c 0 1^L 0^G 1² ,

with head in state B on the separator 0 after the B2c
block. Put

    x := 18 + B2c   (the separator cell),

so the B2c block is [x−B2c, x−1], the L block is
[x+1, x+L], G is [x+L+1, x+L+G], and the terminal pair is
[x+L+G+1, x+L+G+2]. In section coordinates this is
σ_coll = (B, head x, B2 = B2c, g0 = 1, s = L, w = [1],
G, T = 2).

**σ_coll satisfies I** (Phase 12 §2.2) whenever L is even
and ≥ 4: I1 (w = [1], odd), I2 (s = L even), I3-B
(g0 = 1, s ≥ 4, head = B2 + 18 = x), I4 (T = 2). It
violates exactly one hypothesis of Phase 13: **H3** (no
pair follows the shuttle — after the L block comes G
directly). Conversely, *every* B-section satisfying I with
w of length 1 is a σ_coll with L := s: the merged tape is
what a length-1 gap word means. The generic arrival is the
final POP of a depleted stack (Phase 13 §4.1 from
w = [1, 1], giving L = s_old + 2, automatically even), but
the derivation below needs no arrival story: it applies to
any σ_coll.

**Entry.** The saved post-collapse configurations of
Phases 11–12 have the head in state B *inside* the L block
(the collapse sweep's return). From any such position,
Sweep-B (Phase 13 §2: B-on-1 is read-only) carries the head
left across the solid block to x, tape unchanged, arriving
at σ_coll. Verified (C): the G = 68 config (head 136)
reaches σ_coll in 23 steps, the G = 66 config (head 138)
in 25 steps, both with the merged tape intact.

**Hypotheses for Stage A.**

- **HA1** The start is σ_coll as above with B2c ≥ 1,
  L ≥ 2, G ≥ 3.
- **HA2** (for the landing in I) L even, G even — hence
  G′ = G − 2 even and the residue L − 1 odd.

The real regime has B2c = 95, L ∈ {70, 72}, G ∈ {64, 66, 68}
at the two pinpointed collapses of Phase 11.

## 2. Stage A: the collapse excursion, derived (P)

From σ_coll, the excursion is the B-bounce common prefix of
Phase 13 §4 with g1 replaced by G, followed by the probe
and the F-erosion. Step list (z := x+L+1, the first cell
of G):

1. `B@x   on 0 -> 1RC`  (x := 1, annexed to B2c; head C at x+1)
2. `C@x+1 on 1 -> 0RA`  (x+1 := 0, the L block's first cell;
   head A at x+2)
3. Sweep-A over [x+2, x+L] (L−1 steps; head A at z)
4. Probe at z (G ≥ 3, Probe Lemma of Phase 13 §2):
   `A@z on 0 -> 1RB`, `B@z+1 on 0 -> 1RC`,
   `C@z+2 on 0 -> 0LD`, `D@z+1 on 1 -> 1LE`,
   `E@z on 1 -> 1LF` (head F at z−1 = x+L)
5. Sweep-F over [x+2, x+L] (L−1 steps, those cells := 0;
   head F at x+1, reading tape[x+1] = 0 from step 2)
6. `F@x+1 on 0 -> 1LC`  (x+1 := 1, annexed; head C at x,
   reading tape[x] = 1 from step 1)

**Cost** 2 + (L−1) + 5 + (L−1) + 1 = **2L + 6**.

**End configuration σ₂.** Tape changes: x and x+1 annexed
to the block; [x+2, x+L] erased; z, z+1 written. Hence

    σ₂ = (C, head x, B2′ = B2c + 2, s′ = 2, w′ = [L−1],
          G′ = G − 2, T = 2),

a C-section (head = B2′ + 16 = x ✓). The head moves right
monotonically through step 4's second step, left
monotonically thereafter until step 6, and σ₂'s next step
(C-on-1) moves right: σ₂ is the first local minimum after
σ_coll, and the excursion is exactly one bounce. Under
HA2, σ₂ satisfies I: w′ = [L−1] odd, s′ = 2, C-form head,
T = 2, G′ even. ∎

**Events (P).** The excursion contains exactly: one
C-on-0 — the probe's (step 4, third step), B-entry with
left context (tape[z], tape[z+1]) = (1, 1), the probe's own
writes — safe by lemma M2; one D-on-1 and one E-on-1 (probe
steps 4–5); one F-on-0 — step 6, at q = x+1, whose left
triple (tape[x−2], tape[x−1], tape[x]) at its read is
(1, 1, 1) for B2c ≥ 2 (x is step 1's write; x−1, x−2 are
B2c cells) and (0, 1, 1) for B2c = 1 (x−2 is the fixed
separator at 17) — **never (0, 1, 0)**; and nothing else:
no other C-on-0, no D-on-0, no E-on-0, no F-entry C-on-0.
By M1–M4 the machine cannot halt inside a Stage A
excursion. The maximum head is z+2; nothing right of z+1
is written except the probe pair itself. ∎

**Remarks.** (i) Stage A is Phase 13 §5.3's shallow
instance (B2 = 68, L = 6, G = 10, cost 18 = 2·6+6, end
w = [5]) promoted to a derivation for all parameters.
(ii) The mechanics need only HA1 (G ≥ 3 for the probe's
third cell); HA2 is what makes the *landing* an I-section.
With L odd the same step list runs and lands at w = [L−1]
even — outside I (see §4.2 on the formation parameters).
(iii) Stage A's guard is exactly "B-section with
len(w) = 1": together with Phase 13's guards (C-sections;
B-sections with len(w) ≥ 2 split on g1 = 1 / ≥ 3) the five
rules are **total on I**.

## 3. The composed section system (P)

**Theorem (standard regime, across collapses).** Let σ be
a section satisfying I with G even. Then every subsequent
section satisfies I, and every transition is one of the
five derived rules — TDN, PUSH (Phase 13 §3), POP, TUP
(Phase 13 §4), Stage A (§2) — with the derived successor
and cost, **up to but not including** the first excursion
from a B-section with w = [1] entered at G = 2. No step of
any covered excursion is an E-on-0 or realises M4's
pattern; in particular the machine does not halt at any
covered step.

*Proof.* Induction on sections. Phase 13 covers every
bounce from an I-section satisfying H3 (B-sections) or no
extra hypothesis (C-sections), and its end sections again
satisfy I (Phase 12 §2.3 preservation arithmetic). The
only I-sections failing H3 are B-sections with len(w) = 1,
i.e. σ_coll form (§1); from those, §2 applies whenever
G ≥ 3, and under G even ≥ 4 it lands at σ₂ satisfying I
with G reduced by 2. The four rules never change G and
never produce a section outside I; Stage A at G ≥ 4
preserves I. The single uncovered guard combination is
len(w) = 1 at G = 2, where Stage A's probe step 3 would
read the terminal's first cell (a 1) instead of a 0 —
outside the step list of §2. Event safety is per-rule:
Phase 13 §3–§4 for the four rules, §2 for Stage A. ∎

**Corollary (the residue is a theorem of the system).**
Call the bottom entry w[-1] the *residue* when it is the
unique large entry (as at σ₂, w = [L−1]). By the five
rules' forms, entries at positions ≥ 2 are immutable until
surfaced; PUSH moves position 0 to position 1 reduced by
exactly 2; TUP reduces position 1 by exactly 2; TDN and
POP never increase any entry; the only entries ever
created are 1 (PUSH) and s−1 (TUP) at the top. Hence the
residue is a non-increasing sequence of odd numbers,
decreasing by exactly 2 at each surfacing to position 0
or 1, and the stack above it is rebuilt entirely by the
rules — the "regenerated stack" of Phase 12 §3 is the
rule dynamics running from w = [L−1]. Its *rate* is not a
theorem (§4.3): the residue surfaces only when the stack
above it empties to height ≤ 2, and the height performs
the ±1 walk of the four rules.

**What this does to obstruction 2.** Phase 12's statement
"re-expansion is not proven to restore I" rested on
treating the collapse as a regime transition whose
~10⁵–10⁶-step aftermath needed its own induction. The
section-level picture is sharper: I holds at σ_coll
itself, the one non-Phase-13 excursion is Stage A
(≤ 2L+6 steps), and everything after σ₂ is the already
derived four rules. There is no unproven re-expansion
process left in the standard regime: obstruction 2 is
**closed**. (The formation stage's *merging* sweep, which
produces the merged tape before the first collapse, is a
separate segment — see §4.2 and §5.)

## 4. Verification (C)

Tools: `phase14.c` (modes `sections`: section recorder with
the Phase 12 event audit built in; `stagea`: σ_coll finder
+ excursion verifier), `phase14_gen.py` (synthetic battery),
`phase14_analyze.py` (I-checker + transition classifier for
the five rules). All checks below are on data not used in
the derivation (the derivation was worked out from the
G = 68 trace of Phase 11 and the formulas above).

### 4.1 Stage A battery: 17/17 exact

Each run verifies σ_coll's parameters, the excursion cost
2L+6, the full end tape (B2c+2, [L−1], 2, G−2, 2), and the
event inventory of §2 (exactly one C-on-0, B-entry (1, 1);
one D-on-1; one E-on-1; one F-on-0, triple (1, 1, 1), or
(0, 1, 1) at B2c = 1; danger 0):

- the **two real collapses**, from their saved mid-return
  configs: (95, 70, 68) — σ_coll at step 23, cost 146;
  (95, 72, 66) — σ_coll at step 25, cost 150;
- the **formation parameters** (96, 31, 106) from σ_coll:
  cost 68 — mechanics exact, landing w = [30] even, i.e.
  outside I, as §2 remark (ii) predicts for odd L;
- Phase 13 §5.3's parameters (68, 6, 10): cost 18, w = [5];
- 13 held-out synthetics: (B2c, L, G) ∈ {(5,4,6), (33,20,40),
  (120,130,100), (2,2,4), (50,44,4) [G′ = 2 edge],
  (80,58,22), (17,100,64), (200,12,8), (3,8,12), (1,6,10)
  [B2c = 1: F-on-0 triple (0, 1, 1), as derived],
  (64,2,6)}, plus mid-block entries (40,26,30) and
  (7,68,68). **17/17 PASS, zero mismatches.**

### 4.2 Long section windows: I holds across collapses

`phase14 sections` from each post-collapse config,
3×10⁶ steps each; every genuine section I-checked and
every transition classified against the five rules
(successor state, B2, s, full gap word, G, and cost):

| Window | Sections | I violations | Transitions classified | Audit (C-on-0 / F-on-0) |
|---|---|---|---|---|
| G = 68 collapse (real) | 250,017 | 0 | 250,016 / 250,016 (STGA×1) | 125,012, all B-entry (1,1) / all (1,1,1) |
| G = 66 collapse (real) | 250,016 | 0 | 250,015 / 250,015 (STGA×1) | 125,012, same single point |
| Formation collapse (real) | 250,014 | 0 | 250,013 / 250,013 (STGA×2) | 125,011 / 125,010, same single point |
| Held-out synth. (44, 54, 38) | 250,020 | 0 | 250,019 / 250,019 (STGA×1) | 125,015 / 125,014, same single point |

E-reads in every window are all on 1 (125,011–125,014 per
window, exactly one per probe-bearing bounce, plus the
final partial bounce's probe where the window ends
mid-bounce — the C-on-0 / D-read / E-read / F-on-0 counts
tie out exactly against PUSH+TUP+Stage A in all four
windows, including which probe steps the window boundary
cuts off); D-on-0 = 0 and M4 danger = 0 throughout. The rule counts are ~62.5k each
of TDN/PUSH/POP/TUP per window, matching Phase 11's
1/4-each statistics.

**The formation window deserves a paragraph.** It starts
from the real formation collapse config (Phase 11 zoom:
merged tape (96, 31, 106), head in state **A** at 128,
inside the L block — not the σ_coll entry). Its first
genuine section is at step 55: (C, B2 = 97, w = [31],
G = 104) — an **I-section**. The entry excursion is a
variant, **Stage A0**: Sweep-A from the entry position +
Probe + Sweep-F, with no B/C prefix: it annexes only the
separator cell (B2′ = B2c + 1 = 97), erases all L cells
(residue w = [L] = [31], not [L−1]), costs (z − h) + L + 6
from entry head h (18 + 5 + 31 + 1 = 55 here), and lands
in I iff L is odd — as here. Its step list is the same
sweep/probe/erosion components as §2 (P, given the entry
form); that the formation collapse *presents* this entry
form is (C), observed on this instance. From that section
on, the window is entirely the composed system of §3 —
including **two further Stage A firings** (G: 104 → 102 at
the second collapse, → 100 at the third), each landing
back in I. So for this instance the formation stage joins
the proven regime at its first collapse and never leaves
it for 3×10⁶ steps. The segment *before* the first merged
tape (the formation merging sweep, and R → first collapse
generally) remains underived — see §5.

### 4.3 The residue grind-down (O)

From the G = 68 window (sections after σ₂): the bottom
entry runs 69 → 51 (step ≈ 1.2×10⁴) → 41 (≈ 2.5×10⁵) →
39 → 37 → 35 (≈ 1.6×10⁶), still 35 at 3×10⁶ steps; the
G = 66 window: 71 → 37 over the same span. Each decrease
is exactly −2 (the corollary of §3), at surfacings that
grow rarer as the stack heightens (height ≤ 17 seen;
height 9 by step ≈ 1.2×10⁴, with small gaps on top — the
tape *looks* like the settled transient from then on,
with one large gap at the stack bottom). This is Phase
11's "~10⁵–10⁶-step re-expansion", now identified as an
in-system process. Consistency (O): Phase 12's
post-collapse dumps at ≈ +6.8×10⁸ steps show last gaps
19 (G = 66 era) and 23 (G = 64 era) — plausibly the same
residues, ground further; the identity is not proven and
is not needed: I holds regardless of the residue's size.

### 4.4 The boundary at G = 2, pinpointed (C)

A synthetic σ_coll chain with (B2c, L, G) = (30, 18, 6),
run for 10⁶ steps: Stage A fires at step 42 (G: 6 → 4,
σ₂ w = [17]) and again at step 6,182 (G: 4 → 2, σ₂
w = [19]); all 1,535 transitions up to section 1535 are
classified and I holds throughout. Section 1535
(step 18,416) is a B-section with w = [1], s = 22, **G = 2**.
Its excursion departs from Stage A exactly where §2's
hypothesis bites: the probe's third step reads the
terminal's first cell (a 1, not 0), the terminal pair is
absorbed (s: 22 → 24, T transiently 4), and the dynamics
enters the right-edge regime — the remaining 81,828
sections of the window violate I's head/T forms, with G
sawtoothing (1 → 17 → 1 → 19 → 1 → …, peak growing by 2
per cycle in this geometry; cf. Phase 11 §3.2). Over the
full 10⁶ steps the event audit stays single-point clean
(41,687 C-on-0, all B-entry (1, 1); all F-on-0 triples
(1, 1, 1); E-on-0 = 0): the machine *leaves the proven
regime* at that section; it does not halt. This is
obstruction 3's entry point, now exact: **a B-section
with w = [1] at G = 2**.

## 5. Status after Phase 14

**Now proven (P), in addition to Phases 12–13:**

- Stage A (§2): the collapse excursion from any σ_coll
  with G ≥ 3 is the stated shift-rule computation, cost
  2L + 6, landing at σ₂; its event list is exactly one
  safe probe and one F-on-0 with triple ≠ (0, 1, 0).
- The composed system (§3): from any I-section with G
  even, the machine's section dynamics is the five derived
  rules, I is preserved across collapses (each Stage A:
  G := G − 2), and no covered step halts — up to the first
  w = [1] section at G = 2. **Obstruction 2 of
  `post-R-proof.md` §6 is closed.**

**Still not proven (unchanged in kind, sharper in
statement):**

- **Obstruction 3 — the right-edge regime.** Its entry is
  now pinpointed (a w = [1] B-section at G = 2; §4.4) and
  its safety evidence is the Phase 12 §4 audit (5×10⁸
  steps), Phase 11's 10⁹-step stability run, and §4.4's
  10⁶-step audit — all single-point clean, none an
  invariant. A proof needs an invariant for the sawtooth
  dynamics there. (Reachability from R is still only
  projected: ≈ 31 more collapses, ~10¹³ steps.)
- **Formation before the first merged tape.** The merging
  sweep that first produces a merged tape from R is not
  derived. From the first merged tape onward, the observed
  instance is covered: Stage A0 entry (C for the instance,
  step list P given the entry form) landing in I, then the
  composed system (C over 3×10⁶ steps, §4.2). What is
  missing is a derivation that the formation dynamics
  *must* present a merged tape with one of the two entry
  forms (B-return or A-sweep) — and the pre-collapse
  formation sections do not satisfy I (e.g. shuttle 1), so
  neither Phase 13 nor this phase's hypotheses apply there.
- The pre-R segments (Phases 3–9) are unchanged: exact
  simulation + the S′ human proof, unmechanised.

**Conclusion.** The post-R standard regime — bounces,
collapses, and re-expansions alike — is now a completely
derived five-rule pushdown system with invariant I, and
the halt is proven equivalent to a single tape pattern
that provably never occurs inside it. The post-R proof
still does not close into a proof of non-halting, because
the right-edge regime (entered only at G = 2, itself only
projected to be reached) and the formation merging sweep
remain computational facts rather than derivations.
**#168016 remains undecided.** Nothing has been posted
externally.

*Files: `phase14.c` (section recorder + Stage A verifier),
`phase14_gen.py` (Stage A battery: 17 configs,
`phase14-*.cfg`, logs `phase14-stagea-*.log`),
`phase14_analyze.py` (I-checker / five-rule classifier),
`phase14-sections-g68.log`, `phase14-sections-g66.log`,
`phase14-sections-form.log`, `phase14-sections-holdout.log`
(3×10⁶-step windows), `phase14-g6.cfg` +
`phase14-sections-g6.log` (the G = 2 boundary probe),
`phase14-g66col.cfg` (the real G = 66 collapse config),
`phase14-formA.cfg` (the real formation collapse config),
`phase14-holdout.cfg`. The phase10 background run was only
read (checkpoint at isolated step 1.411×10¹² at the end of
this phase), never disturbed.*
