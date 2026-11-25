# Phase 19 — discharging the three remaining derivations (2026-11-25)

Mission: derive the three verified closed forms listed in
`168016-proof.md` §5 item 1 — (i) the REGEN excursion,
(ii) the era closed form s₁ = 2β_E + 31 with I⁺ preserved
(odd-G sub-case ruled out or derived), (iii) the
re-coordinatisation segment X(β_E) → canonical I-section
uniform in β_E. Methodological template: Phase 14's Stage A
derivation (`reexpansion-derivation.md` §2) — decompose the
excursion into step lists already derived, prove each piece
from the transition table, state the exact domain, verify
against measured instances and held-out synthetics.

**Outcome.**

- **(i) REGEN: (P).** REGEN is the composition of three
  already-derived step lists: the POP list (Phase 13 §4.1)
  with the terminal pair in the pair-1 role, the Stage A
  list (Phase 14 §2) at the resulting pairless B-section,
  and the PUSH list (Phase 13 §3.2) at the resulting
  degenerate C-section. Uniform for all a ≥ 1, s ≥ 2;
  cost (2s+3) + (2s+10) + 9 = 4s + 22; span +2. Battery:
  96/96 synthetic configurations exact (§1.4).
- **(ii) Era closed form: (P).** Two ingredients. First,
  POP was under-stated in Phase 13: its step list reads
  only pair 1's first cell, so the general rule is
  s′ = s + r₁ for **any** r₁ ≥ 1 at the same cost 2s + 3 —
  the "defect POP" (r₁ = 1) is the same list, not an
  exception. Second, the **Grind Lemma G′** (§2.2),
  proved by strong induction on the residue m: a grind of
  an odd residue m over an arbitrary tail reaches
  (B, a−2, m+3, [1] + W, R, G) in exactly 2^{(m+1)/2} − 1
  rules, with explicit dip clauses (min a at C-sections
  = a − (m−1)/2, attained only at w₀ = 1 sections).
  Assembling G′ at m = 29 with the POP chain gives
  s₁ = 2β_E + 31 for every β_E; I⁺ is preserved through
  the era with the frame floor a = 4 attained exactly
  (and only where TDN is exact); the Stage-A era's
  G-sequence is G₀, G₀−2, …, 2 with G₀ = s₁ − 1 even —
  **the odd-G sub-case is ruled out**: REGEN (G = 1)
  never fires inside the Stage-A era, and the era ends
  at the entry source (B, β_E+16, s₁+1, [1], G = 2),
  β′ = s₁ + 3 = 2β_E + 34.
- **(iii) Re-coordinatisation: (P) for two-block
  prefixes; one exact residual (H).** The segment splits
  into stage 1 (RPOP chain + RPROBE, closed forms in
  β_E), stage 2 (mirror-rule descent + token walk from
  S_{β_E−1}(β_E), evaluated from Phase 17's derived
  suffix recursion; total = T(β_E), the Phase 17 exit
  time), and stage 3 (RPUSH escape + F-sweep, derived
  step list, uniform in the second block B2 ≥ 2 and in
  β_E). Stages 1–2 never touch the prefix, so they are
  prefix-independent. Stage 3 needs a second block to
  erase. On the real trajectory the prefix is the
  two-block 1¹⁷ 0 1³¹ (from R's formation), so the
  **first** loop iteration is now fully derived. But the
  era's entry excursion lands σ_re on a tape with a
  **single-block** prefix, so in iterations ≥ 2 the
  escape has no second block: the F-sweep erases the
  whole block, the head probes the blank (D-on-0 reads
  occur — event-clean in all audits), and a left-edge
  **re-formation** segment follows whose composed map
  is not yet derived. That segment — and only that
  segment — remains (H). The theorem in
  `168016-proof.md` is updated accordingly: it is **not**
  upgraded to unconditional (§4 below states the exact
  residual).

Tools: `phase19_sim.py` (exact simulator with per-step
audit and local-minimum extraction), `phase19_model.py`
(word model of the single-block frame incl. POP-general
and REGEN), `phase19_classify.py` (classifies log
sections against `phase19_model.py`), `phase19_stage2.py`,
`phase19_segment_check.py`. The phase10 background run
was not touched.

---

## 1. REGEN derived (item i)

### 1.1 Statement

For all a ≥ 1 and all s ≥ 2, the B-section
(B, a, s, w = [1], G = 1) of the single-block frame
evolves, without passing through any other section, to

  (C, a + 2, s = 2, w = [1], G = s − 1),

in exactly 4s + 22 steps, with span + 2. The landing
satisfies invariant I⁺ iff s is odd (G = s − 1 even);
the era case has s = s₁ odd (§2.3).

### 1.2 Why there is no "choice" at the boundary

At a B-section with len(w) ≥ 2 and g₁ = 1, the POP rule
of Phase 13 fires. At w = [1], G = 1 the POP step list
still runs — but its successor is a B-section with **no
working pair at all** (the terminal pair has been
absorbed and the gap counter is exhausted), so the
excursion does not terminate there: the machine
continues with what is, step for step, the Stage A list
at G = blank, and the C-section that produces is
degenerate in exactly the way the PUSH list consumes.
REGEN is that composition. There is no branching: at
each intermediate configuration the next derived list is
forced.

### 1.3 The three parts

**Part 1 — POP list with the terminal pair as pair 1.**
Phase 13 §4.1's step list for POP reads only the first
working pair (gap g₁, run r₁) and the shuttle. Here the
first (and only) pair is the terminal pair: g₁ = G = 1,
r₁ = T = 2 (frame clause). The list therefore runs
verbatim: cost **2s + 3**, landing at the merged
B-section

  (B, a + 1, L = s + 2, w = [1], G = blank),

a genuine head local minimum (σ_coll form with the gap
counter exhausted). Events: **none** — the POP list is
a pure pair of sweeps (no C-on-0, no D/E read, no
F-on-0), as the trace audit confirms (21 steps at
(a, s) = (10, 9): all audit counters zero).

**Part 2 — Stage A list at G = blank.** The merged
B-section is a collapse configuration whose "last gap"
is the blank itself. Phase 14 §2's step list needs only
G ≥ 3 **blank cells** for its probe (step 4); blank tape
supplies them, and the probe's writes (z, z+1) become
the new terminal pair. The list runs verbatim with
L := s + 2: cost **2L + 6 = 2s + 10**, span + 2 (the
only span change of the three parts), landing at the
degenerate C-section

  (C, a + 3, s = 2, w = [s + 1], T = 2)

— precisely the midpoint Phase 18 observed ("a + 3,
single gap s + 1, terminal 1²"). Events: exactly Phase
14 §2's list — one C-on-0, the probe's, B-entry with
context (1, 1); one D-on-1; one E-on-1; one F-on-0
with triple (1, 1, 1) for a ≥ 2. No E-on-0, no D-on-0,
no M4 pattern.

**Part 3 — PUSH list at the degenerate C-section.**
The C-section (C, a + 3, 2, [s + 1], T = 2) has
g₀ = s + 1 ≥ 3 iff s ≥ 2 — the PUSH guard of Phase 13
§3.2. The list runs verbatim: cost **9**, landing at

  (C, a + 2, s = 2, w = [1], G = s − 1).

Events: one C-on-0, B-entry with context (1, 1); one
D-on-1; one E-on-1; one F-on-0 with triple (1, 1, 1)
for a ≥ 2 — never (0, 1, 0).

**Total.** (2s + 3) + (2s + 10) + 9 = **4s + 22** ✓;
span +2 (part 2 only; parts 1 and 3 are bounce lists,
span-preserving) ✓. Intermediate sections occur at
exactly steps 2s + 3 and (2s + 3) + (2s + 10) = 4s + 13,
and no others. Whole-excursion audit (traced at
(a, s) = (10, 9), and exact in the §1.4 battery):
exactly **2 C-on-0** (both B-entry (1, 1) — parts 2
and 3), **2 F-on-0** (both triple (1, 1, 1) for
a ≥ 2), 2 D-on-1, 2 E-on-1; E-on-0 = 0, D-on-0 = 0,
M4 danger = 0. By M1–M4 the excursion cannot halt. ∎

### 1.4 Domain and verification

Domain: a ≥ 1, s ≥ 2 (part 3's guard). The era's REGEN
source (§2.3) is (B, β_E + 16, s₁, [1], 1) with
β_E ≥ 4, s₁ ≥ 39 — deep inside the domain.

Verification (`phase19_sim.py`, exact simulation with
per-step audit and section extraction): grid
a ∈ {1, 2, 3, 4, 5, 10, 18, 40} ×
s ∈ {2, 3, 4, 5, 6, 7, 9, 10, 11, 20, 21, 39} —
**96/96 PASS**: both intermediate minima at exactly
steps 2s + 3 and 4s + 13 with the exact predicted
tapes, final successor at exactly 4s + 22, no extra
sections, exact audit (E-on-0 = D-on-0 = M4 = 0
throughout). The 9 Phase 18 instances (synthetic
s ∈ {5, 6, 9} at their a; trajectory s ∈ {39, 43, 47,
55, 63, 79}) are subsumed by the grid ranges and by the
log classifications of §2.6.

---

## 2. The era closed form (item ii)

Frame sections (C / B, a, s, w, r, G) as in Phase 18 §2;
rules TDN / PUSH / POP / TUP / STGA / REGEN as in
`phase19_model.py`.

### 2.1 POP-general: the "defect" is the rule

Phase 13 §4.1 derives POP from a step list whose only
contact with pair 1 is: sweep the shuttle, read pair
1's gap cell (g₁ = 1), and absorb pair 1's run into the
shuttle on the return sweep. The run length r₁ enters
the successor only as the absorbed count. Hence the
list proves, for **every** r₁ ≥ 1:

  **POP-general:** (B, a, s, w, r, G) with g₁ = 1 →
  (B, a + 1, s + r₁, w[1:], r[1:], G), cost 2s + 3,

span-preserving, with the step list's own event list —
which is empty: the POP list is a pure pair of sweeps
(no C-on-0, no D/E read, no F-on-0; traced in §1.3
part 1). Phase 13's
POP is the case r₁ = 2; Phase 18's "defect POP" is the
case r₁ = 1 — the same derivation, no exception, and
the parity flip Phase 18 observed is just s + 1 vs
s + 2. ∎

### 2.2 The Grind Lemma G′

**Lemma G′.** Let (C, a, 2, [m] + W, R, G) be a
C-section with m odd ≥ 3, W any (possibly empty) word
of odd gaps with run word R (all runs ≥ 1), and G
arbitrary (the grind never reads G: every rule that
fires has its guard and its reads inside the first
two pairs or the guard pair below). Then the dynamics
reaches

  (B, a − 2, m + 3, [1] + W, R, G)

in exactly **2^{(m+1)/2} − 1** rules, W, R, G
untouched, and:

- (no boundary) no STGA, REGEN or ENTRY fires during
  the grind: every intermediate B-section has
  len(w) ≥ 2, except the final endpoint;
- (dip) the minimum of a over intermediate C-sections
  is exactly a − (m−1)/2, attained only at sections
  with w₀ = 1; the minimum over B-sections is
  a − (m−1)/2 − 2.

**Proof** (strong induction on m). All rule
applications are TDN / PUSH / POP-general / TUP of
Phases 13–14 / §2.1; guards are checked at each step
(gaps stay odd: PUSH/TUP act on g ≥ 3 producing
(1, g−2); POP-general needs g₁ = 1).

*m = 3:* PUSH → (C, a−1, 2, [1, 1] + W, [2] + R);
TDN (w₀ = 1) → (B, a−3, 4, [1, 1] + W, [2] + R);
POP (w₁ = 1, popping the pair PUSH created, r₁ = 2)
→ (B, a−2, 6, [1] + W, R, G). 3 = 2² − 1 rules ✓.
Dip: C-sections have a ∈ {a, a−1}; min a_C = a − 1
= a − (3−1)/2 ✓, attained at the post-PUSH section,
which has w₀ = 1; B-sections dip to a − 3
= min a_C − 2 ✓.

*m ≥ 5:* the prefix PUSH, TDN, TUP gives
(C, a−1, 2, [3, m−4] + W, [2] + R, G) — the residue
splits as 3 + (m−4) with a guard pair (gap 1, run 2)
installed. Then for j = 3, 5, …, m−4 (odd): apply the
induction hypothesis G′(j) with tail [m−j−1] + W and
runs [2] + R, landing at (B, a−3, j+3, [1, m−j−1] + W,
[2] + R), then TUP, giving (C, a−1, 2, [j+2, m−j−3] + W,
[2] + R). Finally G′(m−2) with tail [1] + W lands at
(B, a−3, m+1, [1, 1] + W, [2] + R), and one
POP-general (r₁ = 2, the guard pair) gives
(B, a−2, m+3, [1] + W, R, G). Rule count:
3 + Σ_{j odd, 3≤j≤m−4} 2^{(j+1)/2} + (2^{(m−1)/2} − 1) + 1
= 2^{(m+1)/2} − 1 ✓ (the sum telescopes:
Σ_{i=2}^{(m−3)/2} 2^i = 2^{(m−1)/2} − 4).
Tail-independence: every rule of the recursion reads
only the first two pairs; the tail [·] + W with runs
[2] + R is carried as inert context — the recursion
for residue j never reaches past the guard pair, by
the induction hypothesis applied with that tail.
Dip: the deepest C-sections occur inside the final
G′(m−2) call, whose own dip (induction, applied at
a−1) is (a−1) − (m−3)/2 = a − (m−1)/2, attained at
w₀ = 1 sections; the earlier calls dip strictly less
(their (j−1)/2 < (m−3)/2 at a−1, resp. a−3 + …
accounted in the model check below); B-sections dip
exactly 2 lower (TDN/POP endpoints). The endpoint's
a = a − 2 ≥ dip. ∎

**Numerical discharge** (`phase19_model.py`): for
m ∈ {3, 5, 9, 15, 21, 29} × tails (k = 0; k = 3 with
all runs 2; k = 5 with one run 1) at a₀ = 80: the G′
endpoint (B, a₀−2, m+3, [1]+W, R, G) is exact,
min a_C = a₀ − (m−1)/2 exactly and attained only at
w₀ = 1 sections, min a_B = min a_C − 2, all
tail-independent, no boundary rule fired. ✓

### 2.3 Era assembly: s₁ = 2β_E + 31

Start: the canonical section of §3.4,
(C, 18, 2, [ρ, 1^n], [1, 2^{n−1}], G = 1), with
n := β_E and residue ρ = B2 − 2 (ρ = 29 for the real
prefix B2 = 31; ρ odd iff B2 odd).

1. **Absorption.** G′ with m = ρ, W = [1^n],
   R = [1, 2^{n−1}]: 2^{(ρ+1)/2} − 1 rules
   (ρ = 29: 32,767) →
   (B, 16, ρ+3, [1^{n+1}], [1, 2^{n−1}], 1).
2. **POP chain.** n applications of POP-general pop
   R in order: the first pops r₁ = 1 (the canonical
   section's single defect pair — the era's unique
   r₁ ≠ 2 POP; every grind-internal POP pops a guard
   pair created within the same grind, r₁ = 2, by
   G′'s proof), the remaining n−1 pop r₁ = 2:
   s = (ρ+3) + 1 + 2(n−1) = **ρ + 2n + 2**, and a grows
   by 1 per POP: 16 + n. REGEN source:
   (B, n + 16, s₁ := ρ + 2n + 2, [1], G = 1).
   For ρ = 29: **s₁ = 2β_E + 31** ✓, a = β_E + 16 ✓.
   Note s₁ is odd **because of** the defect: without
   the r₁ = 1 POP, s₁ = ρ + 2n + 3 would be even
   (ρ odd). The defect is what makes G₀ = s₁ − 1 even
   in §2.4 — Phase 18's "parity flip" is load-bearing.
3. **REGEN** (§1; s₁ ≥ 2 ✓): →
   (C, n + 18, 2, [1], G₀ = s₁ − 1), cost 4s₁ + 22.

Total grind-era rules: 2^{(ρ+1)/2} − 1 + n + 1
(ρ = 29: 32,768 + n ✓, matching the model's era rule
count for n ≥ 6).

During the grind era the only B-sections with
w = [1] are the POP-chain's last section — the REGEN
source itself (chain sections have w = [1^{n+1−k}],
length ≥ 2 before the last; G′'s no-boundary clause
covers the absorption). So nothing else can fire at
G = 1. ✓

### 2.4 The Stage-A era: G-sequence, and the odd-G sub-case ruled out

REGEN lands (C, a_f + 2, 2, [1], G₀) with
a_f := n + 16 and G₀ = s₁ − 1 (even). One TDN gives
the first STGA source (B, a_f, 4, [1], G₀). The era
then cycles, for s = 4, 6, 8, …:

  STGA (Phase 14 §2): (B, a_f, s, [1], G) →
  (C, a_f + 2, 2, [s − 1], G − 2), cost 2s + 6
  (guard G ≥ 3 — met: G even ≥ 4 at every STGA
  source, see below);
  G′ with m = s − 1 (odd), W = R = ∅:
  → (B, a_f, s + 2, [1], G − 2).

Hence **s + G = s₁ + 3 is invariant** through the era
(check: at the first source, 4 + G₀ = s₁ + 3 ✓), a is
pinned at a_f at STGA sources, and G decreases by
exactly 2 per cycle: G₀, G₀ − 2, …, 4, 2 — **all
even**. The cycle at G = 4 lands (via STGA then G′
with m = s₁ − 2) at (B, a_f, s₁ + 1, [1], G = 2):
the entry source of Phase 15 §3, whose excursion
(cost (s₁+1) + 12) lands σ_re with
**β′ = (s₁ + 1) + 2 = s₁ + 3 = ρ + 2n + 5**;
for ρ = 29, **β′ = 2β_E + 34** ✓.

**Odd-G sub-case: ruled out.** REGEN requires a
w = [1] B-section at G = 1. In the Stage-A era every
w = [1] B-section is an STGA source or the entry
source (G′'s no-boundary clause: grind-internal
B-sections have len(w) ≥ 2), and all of them have G
even (G₀ even, −2 per cycle). In the grind era G = 1
throughout, but there the unique w = [1] B-section is
the REGEN source (§2.3). So G = 1 at w = [1] occurs
exactly once per era, at the REGEN source, and the
odd-G configuration (w = [1], G odd ≥ 3, where STGA's
landing would leave I⁺) never arises from the era.
(Independently: §1 derives REGEN for all s ≥ 2, so
even the parity of the REGEN landing is covered —
for odd s the landing has G even and re-enters I⁺;
an even-s REGEN source would land at G odd, the
configuration Phase 18 flagged — the era never
produces one, since s₁ is odd by §2.3 step 2.) ∎

### 2.5 I⁺ preserved through the era

I⁺ = I with B2 := a, plus: a ≥ 4 at C-sections,
a = 4 ⟹ w₀ = 1 at C-sections, a ≥ 2 at B-sections
(Phase 18 §2). The I-clauses proper (odd gaps, T = 2,
head forms, G parity per regime) are preserved by the
five rules exactly as in Phases 13–14 — the only new
rule is POP-general, whose successor form is identical
with s + r₁ in place of s + 2, and r₁ ∈ {1, 2} in the
era (the canonical R has one 1 and the rest 2s; grind
guard pairs have r₁ = 2), preserving the era's
run-parity bookkeeping. It remains to check the frame
clauses, i.e. the dips:

- *Absorption grind* (G′ at a = 18, m = ρ = 29):
  min a_C = 18 − 14 = **4**, attained only at w₀ = 1
  sections → TDN fires there, and TDN is exact at
  a = 4 (Phase 13 derivation covers a ≥ 4; Phase 18's
  synthetic boundary tests b5/b6/b9/b10 confirm
  exactness at a = 4, 5 and deviation at a ≤ 3).
  min a_B = **2** ✓.
- *POP chain:* a increases 16 → n + 16. No dip.
- *REGEN:* a → a + 2.
- *Stage-A era grinds* (G′ at a = a_f + 2 = n + 18,
  m = s − 1 ≤ s₁ − 2 = 2n + 29): the deepest is the
  last (m = s₁ − 2): min a_C = (n + 18) − (2n + 28)/2
  = **4** exactly, again only at w₀ = 1 sections;
  min a_B = 2. Earlier grinds dip strictly less
  (m smaller by ≥ 2 each cycle ⇒ dip smaller by ≥ 1).

So the frame floor a = 4 is **exactly tight** in both
eras, always at w₀ = 1 sections where the firing rule
is TDN — the dip clauses of G′ are load-bearing, and
with them every C-section of the era satisfies
a ≥ 4 ∧ (a = 4 ⟹ w₀ = 1) and every B-section
a ≥ 2. I⁺ is preserved through the era, including
across the defect POP and REGEN. ∎

### 2.6 Verification

- `phase19_model.py` from the canonical section
  reproduces Phase 18's measured eras exactly:
  s₁ = 2n + 31 for n ∈ {4, 6, 8, 12, 16, 24} (n = 4
  with residue **29** — the model settles Phase 18's
  "residue 25 for β_E = 4" as a slip: with residue 29
  the model reproduces s₁(4) = 39 exactly; with 25 it
  does not), a_REGEN = n + 16, exactly one r₁ = 1 POP
  per era, no w = [1] B-section before the REGEN
  source, min a_C = 4, min a_B = 2, era cost
  ≈ 3.94×10⁵ steps at n = 8.
- Log classification (`phase19_classify.py`, the
  Phase 19 model incl. POP-general and REGEN) against
  the machine logs: **p18-sre8-long.log:
  16,666,175 / 16,666,175 consecutive transitions
  classified, 0 mismatches** — Phase 18's single
  unclassified transition (the defect-POP region) is
  now classified. Smaller windows, all 0 mismatches:
  p18-sre4-rsec.log 83,292; p18-sre8-rsec.log 24,525;
  p18-x6-rsec.log 249,917; p18-x12-rsec.log 245,834;
  p18-x16-rsec.log 184,356 classified transitions.
  Rule counts in the long window: TDN 4,166,545 /
  PUSH 4,166,544 / POP 4,166,541 / TUP 4,166,523 /
  STGA 22 — the near-equality of the bounce counts is
  the grind's PUSH/TDN/TUP/POP balance.
- Same for the β_E = 24 era: `p18-x24-long.log` from
  the settlement step 201,326,512:
  **8,222,632 / 8,222,632 transitions classified,
  0 mismatches** (STGA 21). (Starting the same
  classification at step 201,300,000 adds exactly
  2,215 unclassifiable sections — precisely the
  pre-settlement stage-2 sections of §3.2, which live
  in the mirror frame, not this one; stage 2 is
  verified tape-exact separately.)

---

---

## 3. The re-coordinatisation segment (item iii)

### 3.0 Setup

X(β_E) = (B, 4, (1^{β_E−2}), (2^{β_E−2})) in
coordinates shifted 2 left (Phase 17 §6 / Phase 18 §1).
Full tape, two-block case:
1¹⁷ 0 1^B2 0² 1⁴ (0 1²)^{β_E−2}, head B at the first
0² cell; B2 = 31 on the real trajectory (from R's
formation, component #9/#16). Write n := β_E − 2.
The segment has three stages. Stages 1–2 act only on
the working word W (their excursions' leftmost cell is
W's first gap cell — RPOP/RPROBE/mirror-rule step lists
never move left of the working region's left edge), so
**stages 1–2 are independent of the prefix**; stage 3
is where the prefix matters.

### 3.1 Stage 1 — RPOP chain + RPROBE (closed form)

The first excursion (11 steps; the RPOP step list of
Phase 15 §2 at the merged first pair, r₁ = 4 in
shifted coordinates) lands at
(B, β = 1, r₁ = 6, (1^{n−1}), (2^{n−1})). Thereafter
the sections are the RPOP chain

  (B, β = j, (1^{n−j+1}), r₁ = 2j + 4, (2^{n−j})),
  j = 1, …, n,

the j-th landing at step **2j² + 9j** (excursion
costs 4j + 7 = RPOP's 2r₁ + 3 at r₁ = 2j + 2 ✓).
Chain total 2n² + 9n. Then **RPROBE** (Phase 15 §2,
B-form with one pair; cost 2(2n + 4) + 6 = 4n + 14,
span +2) lands at

  S_{β_E−1}(β_E) = (C, β_E, (2β_E − 1), (2))

at step 2n² + 13n + 14. Verified against the machine
logs for β_E ∈ {6, 12, 16}: every chain step and the
S landing exact (`phase19_segment_check.py`; for
β_E = 12 the chain landings are steps
11, 26, 45, 68, …, 290 and S is at 344 ✓).

### 3.2 Stage 2 — descent and token walk from S

From S_{β_E−1}(β_E) the dynamics is the five mirror
rules of Phase 15. Phase 17 §3 derives, from those
rules, the B-start/C-start suffix recursion (ℬ/𝒞)
that evaluates any token word; the Cycle Lemma is its
evaluation at β ≥ m + 3. Stage 2 is the same recursion
evaluated on the diagonal (β, m) = (β_E, β_E − 1) —
below the cycle threshold, so β is exhausted instead
of restored:

- **Stage 2a (descent).** The recursion reaches the
  first β = 2 C-section
  (C, 2, (1^{β_E−2}, 3), (2^{β_E−1}))
  with every earlier C-section at β ≥ 3 and every
  B-section at β ≥ 1. Duration Δ₁(β_E) by the
  recursion evaluation: 38, 276, 1362, 5888, 24222,
  392618, 6290550, 100662018 for
  β_E = 4, 6, 8, 10, 12, 16, 20, 24.
- **Stage 2b (token walk).** The successive β = 2
  C-sections are
  (C, 2, (1^{i}, 3, 1^{β_E−2−i}), (2^{β_E−1})),
  i = β_E−2, …, 0 — the gap-3 token walks left one
  pair per round. The intervals are
  **3·2^{m+2} − 4** for m = β_E−2, …, 1 — exactly the
  Cycle Lemma durations D_{m−1} of Phase 17 §5: each
  round is one token-pass cycle at the interface
  shifted by the RTDN at β = 2 (the §6 exit mechanics
  of Phase 17, non-terminal here because the word
  continues past the token). Walk total:
  Σ_{m=1}^{β_E−2} (3·2^{m+2} − 4) = 3·2^{β_E+1} − 4β_E − 16.
  The walk ends at the **escape section**
  (C, 2, (3, 1^{β_E−2}), (2^{β_E−1})).

**Stage-2 total = T(β_E)**, the Phase 17 exit-time
function (102, 620, 2850, 11976, 48734, 785754,
12581910, 201325202 for β_E = 4, …, 24) — an
independent cross-check: T was computed in Phase 17
from the cycle side; here the same values fall out of
the descent side. Status: (P) via the Phase 17
recursion and its evaluation, the evaluation
cross-verified (C): the word model reproduces the
machine **tape-exactly** (step, state, full tape) for
every section of stage 2 at β_E = 6 (57 sections),
β_E = 12 (4,082 sections), β_E = 16 (65,519 sections)
— `phase19_segment_check.py` — and the structural
claims (first β = 2 section, walk intervals, escape
section) hold in the model for every even
β_E ∈ {4, …, 24} (`phase19_stage2.py`). Events: only
mirror-rule probes; the whole-segment machine audits
(Phase 18 §1) show E-on-0 = 0, M4 = 0, F-on-0 triples
⊆ {(1,1,0), (1,1,1), (0,1,1)} throughout stages 1–2.

### 3.3 Stage 3 — the RPUSH escape (two-block prefix)

At the escape section the tape is
1^L 0 1^B2 0 [W], W = 1² (0³ 1²) (0¹ 1²)^{β_E−2},
head C at W's first cell (L = 17 on the real
trajectory). Step list (traced at (L, B2, β_E) =
(17, 31, 12), 42 steps, matching the machine log's
sections at segment steps 49,078 → 49,120 exactly):

1. **RPUSH** (Phase 15 §2 list at g₀ = 3), 9 steps:
   lands head C on the separator cell between 1^B2
   and W. Events: one B-entry C-on-0 (1, 1), one
   D-on-1, one E-on-1, one F-on-0 with triple (1, 1, 0).
2. **F-entry at the separator:** C-on-0 with context
   (1, 1) — C writes 0 (no change) and moves left
   into D (1 step).
3. **D-on-1, E-on-1** (2 steps) at the last two cells
   of 1^B2 — these two cells survive as the new
   shuttle.
4. **F-sweep:** F-on-1 = 0LF erases the remaining
   B2 − 2 cells of the block (B2 − 2 steps).
5. **F-on-0** at the block's left separator, triple
   (1, 1, 1): writes 1, merging the block remnant
   into the left block: a = L + 1 (1 step).

Cost 9 + 1 + 2 + (B2 − 2) + 1 = **B2 + 11** (42 at
B2 = 31 ✓). Landing tape:

  1^{L+1} 0^{B2−2} 1² 0¹ 1¹ (0¹ 1²)^{β_E−1},
  head C at L − 1,

which is the canonical section
(C, a = L + 1, s = 2, w = [B2 − 2, 1^{β_E}],
r = [1, 2^{β_E−1}], G = 1) of Phase 18 §2 — for
L = 17, B2 = 31: (C, 18, 2, [29, 1^{β_E}],
[1, 2^{β_E−1}], 1), span 3β_E + 51 ✓. The derivation
is uniform for all L ≥ 1, all B2 ≥ 2 (steps 3–4 need
exactly the block's last two cells to read 1, i.e.
B2 ≥ 2), and all β_E ≥ 2. The era of §2 needs the
residue ρ = B2 − 2 **odd**, i.e. B2 odd — the real
trajectory's B2 = 31 ✓. Events over the whole
escape: C-on-0 ×2 (B-entry (1, 1); F-entry (1, 1)),
D-on-1 ×2, E-on-1 ×2, F-on-0 ×2 (triples (1, 1, 0)
and (1, 1, 1)); E-on-0 = D-on-0 = M4 = 0.
Verified by exact traces at (B2, β_E) = (31, 12)
[also the machine log], (31, 8), (21, 8), (3, 8):
exact landing tapes and audits in all four.

**Segment total (two-block, B2 = 31):**
(2n² + 13n + 14) + T(β_E) + 42, n = β_E − 2 —
760 / 49,120 / 786,384 / 201,326,512 steps at
β_E = 6 / 12 / 16 / 24 ✓ (Phase 18's measured
totals). **Loop map, general residue:** with
ρ = B2 − 2, §2.3–2.4 give s₁ = ρ + 2β_E + 2 and
β′ = ρ + 2β_E + 5 — strictly increasing for every
ρ ≥ 1; ρ = 29 yields β′ = 2β_E + 34. ∎ (for
two-block prefixes)

### 3.4 What item (iii) now covers

The first loop iteration — the one the real
trajectory is in, since R's formation (component #9)
produces the two-block prefix 1¹⁷ 0 1³¹ — is derived
uniformly in β_E: stages 1–2 for every β_E ≥ 2
(structural claims model-verified for all even
β_E ≤ 24, tape-exact at 6/12/16), stage 3 for every
B2 ≥ 2. Combined with §2, the loop map
β′ = 2β_E + 34 and the era are (P) **as long as the
prefix at X(β_E) is two-block**. The next section
states exactly where that hypothesis fails.

---

## 4. The residual: the single-block re-formation (H)

The era's exit is the ENTRY excursion (Phase 15 §3)
at (B, a_f, s₁ + 1, [1], G = 2), fired **from the
single-block frame**. Its landing σ_re(β′) sits on a
tape whose left region is a single block 1^{a+1}
followed by 0¹ (Phase 18 §3, configs p18-b1/b7) —
the entry excursion does not recreate a two-block
prefix. Consequently, in every loop iteration ≥ 2,
X(β′) has a **single-block** prefix, and at stage 3
there is no 1^B2 block for the F-sweep to erase.

What is verified about that case (runs
`p19-sre8-single.log` (block 40), `…12.log`
(block 12), `…20.log` (block 20): σ_re(8) entries
with single-block prefixes, 3×10⁶ steps each):

- Stages 1–2 go through **verbatim** (prefix never
  touched): X(8) at step 2,856, RPROBE landing
  S₇(8) at step 3,020, span 66 — identical sections
  to the two-block runs.
- At the escape section, RPUSH + the F-entry run as
  in §3.3 steps 1–3, but the F-sweep erases the
  **entire** single block and continues into the
  blank (head minima −5 at block 12, −8 at blocks
  20/40, relative to the block's left edge).
  **D-on-0 reads occur** (2 at block 12; 4 at blocks
  20/40): D-on-0 = 1RF writes 1 and exits right in
  state F — it never enters E. The accompanying
  C-on-0 probes are F-entry with context (0, 0).
- A **left-edge re-formation** follows: the residue
  burns down by 2 per counter-cycle (36 → 34 → 32 →
  30 observed at block 40, residue = block − 4); in
  the block-12 run, by 3×10⁶ steps a two-block
  prefix 1¹⁷ 0 1¹² has been rebuilt and the dynamics
  is running in a standard-frame-like regime — but
  the exact landing section was **not** pinned down,
  and no shift-rule derivation of the re-formation
  exists yet.
- Audits over all three runs: **E-on-0 = 0,
  M4 danger (0, 1, 0) = 0** throughout; D-on-0 ∈
  {2, 4}, F-entry (0, 0) C-on-0 ∈ {2, 4}. The segment
  is event-clean in every observation; what is
  missing is its derivation as a composed map —
  landing form and cost uniform in (β_E, block
  length) — i.e. one formation-type segment of the
  same kind the project has discharged before
  (cf. R's formation, component #9: 150 steps,
  audited; the β = 2 exit's own continuation was in
  this position before Phase 18).

**Consequence.** The loop is fully derived for
iteration 1. Iterations ≥ 2 are derived except for
this one segment per iteration. The theorem in
`168016-proof.md` §4 is therefore restated as:
non-halting, complete modulo the single-block
re-formation segment (H) — **not** unconditional.
The unconditional finite corollary (≈ 1.7709×10²¹
steps) is unaffected, as are all (P)/(C) components
#1–#15.

## 5. Files

`phase19-derivations.md` (this file),
`phase19_sim.py`, `phase19_model.py`,
`phase19_classify.py`, `phase19_stage2.py`,
`phase19_segment_check.py`,
`p19-esc12.cfg`, `p19-esc-b{3,21,31}.cfg`,
`p19-regen-test.cfg`,
`p19-sre8-single{,12,20}.cfg` + logs,
`p19-classify-big.log`.
