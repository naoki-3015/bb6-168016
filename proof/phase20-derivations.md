# Phase 20 — the single-block re-formation (component #19)

Machine #168016: `1RB1RA_1RC1LB_0LD0RA_1RF1LE_---1LF_1LC0LF`.
Transition table (state, read) → (write, move, next):
A: 0→1RB, 1→1RA. B: 0→1RC, 1→1LB. C: 0→0LD, 1→0RA.
D: 0→1RF, 1→1LE. E: 0→HALT, 1→1LF. F: 0→1LC, 1→0LF.

Phase 19 left exactly one underived segment (component #19):
from loop iteration 2 on, the re-coordinatisation's stage-3
escape meets a **single-block** prefix `1^L 0^1`; the F-sweep
erases the whole block, D-on-0 reads occur, and a left-edge
**re-formation** follows whose landing and composed map were
open. This phase attacks that segment with an exact simulator
in absolute coordinates (`phase20_sim.py`, validated
step-exact against the Phase 15 C simulator), a frame parser /
transition classifier (`phase20_parse.py`), and a word-model
grind driver (`phase20_grind.py`).

**Outcome: outcome (b) of the mission, with most of the
segment discharged.** The re-formation is now derived except
for one sharply located family of boundary excursions — the
**deviation excursions** at PUSH-at-`a = 2` inside the two
grinds (and their canonical-era analogue). Everything else —
the probe prefix, the boundary forms TDN-at-2 / POP-at-0, the
transfer POP2, the era landing, and the composed loop map —
is derived below and machine-verified on every measured
instance. The exact residual is stated in §7.

Conventions: sections are head local minima (move-in L,
move-out R). A frame reading is `(state, a, s, w, r, G)` with
frozen prefix `P` (list of runs left of the interface block):
tape `P · 1^a 0^{w_0} 1^s Π(0^{w_i} 1^{r_i}) 0^G 1^2`; C-sections
have the head at `x − 2`, `s = 2` (x = first cell after the
block); B-sections have the head at `x`, `w_0 = 1`. The model
rules TDN/PUSH/POP/TUP/STGA/REGEN/ENTRY are the Phase 13/14/19
forms (`phase20_parse.model_step`).

---

## 1. The escape configuration and the probe prefix (DERIVED)

The stage-3 escape section on a single-block prefix
(Phase 19 §3.3 with the second block absent) is

```
ESC(L, β):  tape 1^L 0^1 1^2 0^3 1^2 (0^1 1^2)^{β−2},
            head C at cell L+1,   L ≥ 8, β ≥ 2.
```

**Theorem P20.1 (probe prefix).** From ESC(L, β) the machine
reaches, in exactly **L + 42 steps**, the frame section

```
(C, a = 5, s = 2, w = [1, L−6, 1^β], r = [2, 1, 2^{β−1}], G = 1)
```

in the single-block frame whose block `1^5` sits at cells
−4..0 (the escape block's left edge is cell 0). The segment
decomposes into five step lists E1–E5 (below), is uniform in
L ≥ 8 and in β ≥ 2 (the tail `(0^1 1^2)^{β−2}` is never read
except its first pair, as the survivors / single / first
tail pair), and is event-clean: E-on-0 = 0, D-on-0 = 2 (in
E2 and E4 only), M4 danger = 0; see §6 for the safety proof.

Coordinates: block cells `[0, L−1]`, separator `L`, shuttle
`L+1, L+2`, gap `L+3..L+5`, first pair `L+6, L+7`.

**E1 — RPUSH + F-sweep (cost L + 12).**
(i) The Phase 15 RPUSH list (9 steps): C@L+1 on 1 → erase;
A@L+2 on 1; A@L+3 on 0 → write; B@L+4 on 0 → write; C@L+5
on 0 → D (C-on-0, B-entry ctx (1,1)); D@L+4 on 1 → E;
E@L+3 on 1 → F; F@L+2 on 1 → erase; F@L+1 on 0 → write
(F-on-0 triple (1,1,0) — safe, §6), head C at L.
(ii) C@L on 0 → D (F-entry ctx (1,1)); D@L−1 on 1 → E;
E@L−2 on 1 → F; F-sweep erases cells L−3 … 0 (L−2 steps;
cells L−2, L−1 survive — they were read, not erased, by
D and E); F@−1 on 0 → write (triple (0,0,0)); C@−2 on 0
→ D (F-entry ctx (0,0)). Ends at the D-section at −3.
Tape now: `1` at −1; survivors `1^2` at L−2, L−1; `1` at
L+1; `1^2` at L+3, L+4; pair and tail intact; cells
0..L−3 blank.

**E2 — probe ignition (cost 2).** D@−3 on 0 → 1RF (write
−3, exit right in F); F@−2 on 0 → write (triple (0,0,1)),
head C at −3. Tape: `1^3` at −3..−1, gap `0^{L−2}`, then
as after E1.

**E3 — first conversion (cost 12).** C@−3 on 1 → erase;
Sweep-A over −2, −1; A@0 on 0 → write; B@1 on 0 → write;
C@2 on 0 → D (B-entry (1,1)); D@1 on 1 → E; E@0 on 1 → F;
F erases −1, −2; F@−3 on 0 → write (triple (0,0,0));
C@−4 on 0 → D (F-entry (0,0)). Ends at the D-section at
−5. Tape: `1` at −3, `0^2`, `1^2` at 0..1, gap `0^{L−4}`,
survivors, …. Domain: cells 0, 1, 2 blank before the list
(the gap `0^{L−2}`), i.e. L ≥ 5.

**E4 — probe ignition (cost 2).** D@−5 on 0 → 1RF (write
−5); F@−4 on 0 → write (triple (0,0,1)), head C at −5.
Tape: `1^3` at −5..−3, `0^2`, `1^2` at 0..1, gap, ….

**E5 — second conversion = landing (cost 14).** C@−5 on 1
→ erase; Sweep-A over −4, −3; A@−2 on 0 → write; B@−1
on 0 → write; C@0 on 1 → erase; A@1 on 1; A@2 on 0 →
write; B@3 on 0 → write; C@4 on 0 → D (B-entry (1,1));
D@3 on 1 → E; E@2 on 1 → F; F@1 on 1 → erase; F@0 on 0
→ write (triple (1,1,1)), head C at −1 — the landing
section of the theorem: block `1^5` at −4..0 (remnant
cells −4, −3; E5-written −2, −1; F-written 0), separator
cell 1, shuttle `1^2` at 2..3 (E5-written), residue gap
`0^{L−6}` at 4..L−3, survivors `1^2` at L−2, L−1, then
`0^1`, the single at L+1, `0^1`, the probe pair at
L+3, L+4, and the tail. Domain: cell 4 blank (gap reaches
it), i.e. L ≥ 7; with E3, the prefix is stated for L ≥ 8
(R = L − 6 ≥ 2, the grind's domain).

*Verification.* Landing section and cost L + 42 read off
the exact simulator at L = 8, 10, 12, 14, 20 (steps
50, 52, 54, 56, 62) and the era reached at L = 16, 18, 24,
28, 34, 40 with the same prefix anatomy (D-on-0 count = 2
in every no-deviation run; §4). β-independence: the tail
beyond the first pair is untouched, confirmed at
β = 4, 6, 12 (§5).

## 2. Boundary forms at small a (DERIVED)

The Phase 13 step lists have explicit read sets, which
decide exactly when they fire verbatim at the frame floor:

- **TDN** (C-section, w_0 = 1) reads only cells
  `x−2, x−1, x, x+1`. It is exact for every **a ≥ 2**, in
  any frame, including landing at a B-configuration with
  a − 2 = 0. No F-sweep occurs in TDN; its event set is
  empty.
- **POP** (B-section, w_1 = 1) reads only cells `≥ x`. It
  is exact for every **a ≥ 0** — in particular from the
  a = 0 configuration produced by TDN-at-2 (head on the
  blank cell immediately left of the merged block+shuttle
  run, which POP then treats as its shuttle). Event set
  empty.
- **TUP** (B-section, w_1 ≥ 2) reads only cells `≥ x`
  except its probe, whose F-on-0 has triple (1,1,1) for
  a ≥ 2. Exact for a ≥ 0 as a step list; its landing is a
  C-section, which needs a + 2 ≥ 2 — always true.
- **PUSH** (C-section, w_0 ≥ 3) reads down to `x−3`, and
  its landing is a C-section iff `tape[x−3] = 1`, i.e.
  iff **a ≥ 3** in the current frame (at a = 3 the landing
  cell is the block's first cell; the F-on-0 triple is
  then (0,0,1) or (0,1,1) or (1,1,1) — never (0,1,0)).
  At **a = 2** PUSH's list runs off the block: this is
  the deviation of §4.
- **STGA / REGEN / ENTRY** are Phase 14/15/19 lists; in
  the eras of §5 the interface satisfies a ≥ 10 at every
  C-section, so no boundary case arises there.

Consequently the only underived boundary behaviour in
the whole re-formation is **PUSH at a = 2** (and, in the
canonical-era grind, its cousin of §6.2).

## 3. The residue grind G″

After the probe prefix the trajectory is at
`(C, 5, 2, [1, R] + W, [2] + Rr, G = 1)`, R = L − 6 even,
W = [1^β], Rr = [1, 2^{β−1}] — the residue R sits at w_1
behind a leading gap 1, with the survivors' run 2 in
front of it. Call the ensuing model dynamics the **grind
G″(R)**: the four Phase 13 rules (with the §2 boundary
forms) applied until the transfer source of §4,

```
(B, ·, ·, w = [1, 2, 1] + W′, r = [2, 1] + R′, G = 1),
```

is reached (the residue parked at 2 in w_1, a pair of 2s
in front of the single).

**Model evaluation (word model, tail-inert).** With the
boundary forms admitted (a = 0 allowed at B-sections),
the grind is a G′-type recursion: the forced prefix
[TDN, TUP, PUSH, TDN, POP] reduces (C, a, 2, [1, R] + W)
to (B, a−2, 6, [1, R−2] + W), and the recursion closes
with the evaluation

```
end:  (B, a₀ − 2, R + 2, [1, 2] + W, [2] + Rr, G),
rules: N(R) = 2^{R/2 + 1} − 3,
dips: min a over C-sections = a₀ − (R−2)/2,
      min a over B-sections = a₀ − (R−2)/2 − 2,
      min a over PUSH sources = min a_C + 1,
```

verified on the word model for every even R ≤ 34 (rule
counts 1, 5, 13, 29, 61, 125, 253, 509, 2045, 8189,
32765, 262141 at R = 2, 4, …, 34; costs 6, 46, 134, 318,
694, 1454, 2982, 6046, 24462, 98174, 393070, 3145558).
The dips are the whole story of §4: at the re-formation's
a₀ = 5, the model first touches a = 2 at a PUSH source
exactly when R ≥ 10 (min a_C = 5 − (R−2)/2 ≤ 3 with a
PUSH at min a_C + 1 ≤ 2 ⟺ R ≥ 10; at R = 8 the deepest
PUSH is at a = 3 — exact by §2 — and TDN-at-2 / POP-at-0
carry the bottom).

**Machine behaviour.** For **R ≤ 8** the machine follows
the model + boundary forms exactly: the full
re-formations at L = 8, 10, 12, 14 classify transition by
transition (every transition is a model rule, a §1 piece,
POP2, terminal POP, blank Stage A, or PUSHdeg — counts in
§8). For **R ≥ 10** the machine leaves the model at
PUSH-at-2 sources (§4) and reaches the transfer source
faster than the model's recursion, in a shifted frame
(§4.2).

## 4. The deviation excursions (the residual's core)

### 4.1 PUSHX: PUSH at a = 2, decomposed at the observed form

In every measured instance the deviation source is
`(C, 2, 2, [3] + W, R, G)` in the single-block frame
(esc16 step 669; esc18 steps 671, 1419 — in the latter
two the residue sits deeper in the stack; the local form
at the interface is the same). The excursion from such a
source decomposes into four derived pieces:

1. **PUSH's own list** (9 steps, §2): prefix + probe at
   the gap; F erases x−1 and writes x−2; the head lands
   at C@x−3 on a **blank** cell (no block cell there) —
   not a section.
2. **Probe ignition** (3 steps): C@x−3 on 0 → D
   (F-entry ctx (0,0)); D@x−4 on 0 → 1RF (write x−4);
   F@x−3 on 0 → write (triple (0,0,1)); C-section at
   x−4 with remnant `1^3` at x−4..x−2. (One D-on-0;
   safe by §6.)
3. **Remnant conversion** (8 steps): C erases x−4;
   Sweep-A over x−3, x−2; A writes x−1; B turns and
   Sweep-B back to the B-section at x−4 on the erased
   cell. The block, gap and shuttle have merged into a
   single run `1^5` at x−3..x+1.
4. **POP at the merged run** (cost 2·5 + 3 = 13): the
   merged run plays the shuttle; landing
   `(B, a = 1, s = g + 4, w = W, r = R, G)` with the
   block reduced to the single POP-written cell.

Total cost at g = 3: 9 + 3 + 8 + 13 = **33 steps**
(esc16 steps 669–702, verified step by step). Event
audit of the excursion: E-on-0 = 0, D-on-0 = 1,
C-on-0 contexts (1,1) (probe, B-entry) and (0,0)
(ignition), F-on-0 triples (0,0,0), (0,0,1), (1,1,1) —
no (0,1,0). After PUSHX the grind resumes in the same
(single-block) frame at a = 1 with the residue reduced
and re-parked deeper in the stack; the frame later
re-bases (§4.2).

### 4.2 Deviation census and the grind's actual landing

Deviation counts (D-on-0 beyond the probe prefix's 2,
from full-run audits, §8): **R = 10: 1 deviation;
R = 12, 18, 22, 28, 34: 2 deviations each.** No other
D-on-0 occurs anywhere in any run. After the deviations
the grind reaches the transfer source of §3 in a shifted
frame; measured transfer sources (first B-section with
w = [1, 2, 1] + tail, r = [2, 1] + tail after the probe
landing):

| R (L) | frame at transfer source | (a, s) |
|---|---|---|
| 6 (12) | single-block | (3, 8) = model |
| 8 (14) | single-block | (3, 10) = model |
| 10 (16) | single-block | (4, 13) |
| 14 (20) | prefix [1^5 0^1] | (13, 4) |
| 18 (24) | prefix [1^5 0^1] | (13, 8) |
| 22 (28) | prefix [1^5 0^1] | (13, 12) |
| 28 (34) | prefix [1^5 0^1] | (13, 18) |
| 34 (40) | prefix [1^5 0^1] | (13, 24) |

(R = 12's grind ends at (B, 4, 13, w = [1, 2, 2, 1, …],
r = [2, 2, 1, …]) in the single-block frame — the same
(a, s) as R = 10 but with g_2 = 2, so the transfer there
is a g_1 = 2 variant, not POP2; cf. §6.1's TUP2 and
residual item (ii).) For R ≥ 14 the
transfer source has s = R − 10 in the [1^5 0^1] frame.
The grind's step cost on the machine (probe landing →
era) is ~5×10^4 at R = 34 — far below the model's
2^{R/2+1} recursion, because each deviation collapses a
sub-recursion into a merge. A closed form for the
deviation-corrected grind (landing frame and (a, s) as a
function of R, and the deviation count for R > 34) is
**not** derived: this is residual item (i) of §7. What is
derived is that the grind *terminates at a transfer
source of the stated shape in every measured instance*,
and that everything after the transfer source is §5.

## 5. Transfer, POP chain, era (DERIVED)

**POP2 (transfer).** From
`(B, a, s, w = [1, 2, 1] + W, r = [2, r_2] + R, G)` with
r_2 ≥ 1 (any frame; the prefix is never read):

```
step list: B-bounce prefix (cost s + 2), then 7 steps:
  B@x+s+2 on 0 → write (fill g_1's second cell);
  C@x+s+3 on 1 → erase (pair 1's first cell);
  A@x+s+4 on 1; A@x+s+5 on 0 → write (fill g_2);
  B@x+s+6 on 1 → L; B@x+s+5 on 1 → L; B@x+s+4 on 1 → L.
successor: frame shifts — the old block + w_0 cell join
  the frozen prefix (new prefix block 1^{a+1}); new
  interface (B, a′ = s + 1, s′ = r_2 + 2, w′ = [1] + W,
  r′ = R, G).  Cost s + 9.  Events: none.
```

Verified at (s, r_2) = (4, 1), (6, 1), (8, 1), (10, 1)
(costs 13, 15, 17, 19; esc8/10/12/14) step-exactly.

**Tail (already derived in Phases 13/14/19).** From the
POP2 successor: the POP chain (β − 1 pops, POP-general)
empties the stack at `(B, a, 2β + 1, [1], G = 1)` in the
era frame; the terminal POP (cost 2s + 3) and the blank
Stage A (cost 2s + 6, Phase 19 §1.3 verbatim) reach the
degenerate C-section; PUSHdeg (cost 9) lands the era's
first section `(C, B2_era, 2, [1], [], G = 2β)`.

**The era (derived system, Phase 19 §2).** The Stage-A
era in the resulting two-block frame: STGA sources
`(B, a_f, s, [1], G)` with **s + G = 2β + 4** constant,
G = 2β, 2β − 2, …, 2 (all even), the G′ grinds between
them running at a = a_f + 2 with dips ≥ 4 (a_f ≥ 10 in
every measured instance), and ENTRY at
`(B, a_f, 2β + 2, [1], G = 2)` landing σ_re(β_next) with

```
β_next = 2β + 4        (frame-independent),
```

by the Phase 15 entry mechanics (β_next = (era constant)
= s_entry + 2). The next escape's prefix is the era
frame's block pair (b_1, a_f + 1) — a **two-block**
prefix, so iteration 3+ escapes are the Phase 19 §3.3
case (§6).

**Measured era frames** (first STGA source; β = 8):
L = 12: prefix [1^4 0^1], a_f = 16; L = 14: [1^4 0^1], 18;
L = 16: [1^5 0^1], 21; L = 18, 20, 24, 28, 34, 40:
prefix [1^5 0^1 1^14 0^1], a_f = L − 8. ENTRY sources
verified at every one of these L (s = 18, G = 2), and
β_next = 20 read off the post-ENTRY token-pass sections
at L = 12 (tape `1^4 0 1^17 0 1^20 0 1^2`, diagonal
sections with β − 1 = 19).

**β-independence (held-out synthetics).** ESC(12, 4),
ESC(12, 6), ESC(12, 12), ESC(20, 12): probe landing as in
§1; era frames [1^4 0^1] with a_f = L + β − 4 (12, 14, 20
at L = 12) and [1^5 0^1 1^14 0^1] with a_f = 16 at
(20, 12); era constants 12, 16, 28, 28 = 2β + 4; ENTRY
sources at s = 2β + 2 in all four; deviation counts by R
only (0 at R = 6 for all β; 2 at R = 14). The mid block
1^14 in the two-deviation frame is β-independent in
these instances (β = 8 and β = 12).

## 6. Iteration 3 and beyond

### 6.1 The canonical landing's grind also deviates

Iteration 3's escape is two-block (Phase 19 §3.3,
derived), landing the canonical section
`(C, b_1 + 1, 2, [1, ρ] + [1^{β′}], [2, 1] + [2^{β′−1}], 1)`,
ρ = B2_entry − 1. Its first grind is the same residue
grind with a₀ = b_1 + 1 ≈ 5 and residue ρ ≫ 12 on the
real trajectory, so by the §3 dip formula it **must**
hit the small-a boundary: the Phase 19 §2 evaluation of
the canonical era (which assumes the model grind) does
not apply verbatim. Test instance (the (12, 8) chain's
iteration 3: b_1 = 4, ρ = 15, β′ = 20; config
`p20-iter3.cfg`), simulated 2×10^5 steps, audit-clean
(E-on-0 = 0, M4 = 0, D-on-0 = 1):

- The grind's small-a behaviour is the §2 boundary
  forms, now in the two-block frame: TDN-at-2 /
  POP-at-0 pairs (3 occurrences) — the excursions read
  only cells ≥ x − 2, the frozen prefix is untouched,
  exactly as derived in §2.
- **One two-block deviation** (steps 591–640): a
  TUP-at-a=0 (from the a = 0 configuration after a
  TDN-at-2) whose probe gap is 3 wide: the resulting
  F-sweep erases the entire left tape — interface
  block, separator, and the frozen prefix `1^4` — to
  blank; a left-edge probe cycle (one D-on-0, contexts
  (0,0) / triples (0,0,·), as in §1) re-forms a
  **single-block** frame `(B, 4, 3, …)` at step 640,
  with the stack (residue 7 at w_6, tail intact)
  preserved. Event-clean.
- One **TUP2** transfer (step 1460, cost 24 = 2s at
  s = 12): the g_1 = 2 analogue of TUP for
  (r_1, g_2) = (2, 5) — B-bounce prefix, both g_1 cells
  and g_2's first cell filled, pair 1's first cell
  erased, one Probe-Lemma probe (B-entry (1,1), F-on-0
  (1,1,1)); landing (C, 14, 2, [1, 3, …]) in the frame
  with prefix [1^9 0^1]. Decomposed step by step in the
  working notes; the general (r_1, g_2, r_2) form is
  residual item (ii).
- Thereafter the derived tail: POP chain → terminal
  POP (cost 97 = 2·47 + 3) at the REGEN source
  `(B, 33, 47, [1], G = 1)` → blank Stage A (cost
  104 = 2·49 + 6) → PUSHdeg → **Stage-A era with
  constant s + G = 50** (11 STGA sources measured,
  a_f = 33, prefix [1^9 0^1]) → ENTRY by the Phase 15
  mechanics with **β″ = 50** (= era constant =
  s_regen + 3, the relation verified in both other era
  types). Note β″ = 50 ≠ 60 = the no-deviation formula
  ρ + 2β′ + 5: the deviation changed the era's
  bookkeeping (s_regen 47 instead of 57) but not its
  form, and β still strictly increases (20 → 50).

### 6.2 Loop structure from iteration 2 on

- **Iteration 2 (the only single-block escape):**
  §§1–5 — derived except the §4 deviations; lands the
  Stage-A era with β → 2β + 4 and a two-block era
  frame, so iteration 3's escape is two-block.
- **Iterations ≥ 3 (two-block escapes, repeating):**
  Phase 19 §3.3 escape (derived) → canonical landing →
  §6.1 grind (boundary forms + deviations, residual
  items (i)/(ii)) → derived tail → Stage-A era →
  ENTRY with β_next = s_regen + 3 > β (measured
  50 > 20; the general inequality is part of the
  residual). Every such era's frame at ENTRY is again
  a block pair, so the unit repeats: the single-block
  re-formation of §§1–5 occurs exactly once in the
  whole loop (iteration 2, at the real trajectory's
  (L, β) = (β₁ + 17, 2β₁ + 34)), and the residual
  concerns (a) that one grind's deviations (§4) and
  (b) the canonical grind's deviations at every
  iteration ≥ 3.

## 7. The exact residual

The proof of #168016 is complete modulo the following,
and nothing else in the post-R dynamics:

**(i) The deviation excursions of the two grinds.** A
uniform derivation of PUSH-at-a=2 (single-block frame)
and of the TUP-at-a=0 probe excursion (two-block frame),
as composed maps on the grind state: their effect on
(frame, a, s, stack) and a proof that the grind then
resumes and terminates at a transfer source. Status:
PUSH-at-2 fully decomposed at the only observed local
form (C, 2, 2, [3] + W) (§4.1); the two-block excursion
decomposed at the one observed instance (§6.1);
deviation counts measured (≤ 2 per grind at β = 8,
R ≤ 34; 1 in the iteration-3 instance); all instances
event-clean (§8). Not yet derived: the general
(g, W, R) form of PUSHX (g ≥ 5 unobserved — the grind's
recursion produces its deep PUSHes from TUP at s = 4,
which is why g = 3 is the observed case), the
deviation-corrected closed form of the grind's landing,
a bound on the deviation count for large R / ρ, and the
inequality s_regen + 3 > β in the canonical era under
deviations (the composed map's constant changes:
measured β″ = 50 vs the deviation-free 60).

**(ii) The g_1 = 2 transfer variants.** POP2 is derived
for g_2 = 1 (§5). The variant TUP2 (g_1 = 2, probe
present) is decomposed at (r_1, g_2) = (2, 5) (§6.1);
its general (r_1, g_2, r_2) step list is not tabulated.
Variants of this family occur inside the canonical
grind (TUP2 itself) and at R = 12 in the re-formation
grind (g_2 = 2 form); the era landing after them is
measured, not derived, in those instances.

**(iii) The G″ / canonical-grind human induction.** The
model evaluations (G″ here, G′ in Phase 19 §2.2 — the
latter human-proven) — G″'s evaluation is verified on
the word model for all even R ≤ 34 and its forced-prefix
recursion is exhibited in §3, but a written strong
induction in the style of Phase 19 §2.2 is still owed.
This item is bookkeeping, not dynamics: the machine's
path is fully classified in every measured instance
(§8); the deviations of item (i), not this induction,
are what keep the machine's grind from being the
model's.

Everything else in iterations ≥ 2 — probe prefix,
boundary forms, POP2, POP chain, terminal POP, blank
Stage A, PUSHdeg, REGEN, the Stage-A era system, ENTRY,
the token pass, both escape types — is (P) as cited.
The unconditional finite corollary of `168016-proof.md`
(≈ 1.7709 × 10^21 steps) is unaffected.

## 8. Event-cleanliness and verification index

**D-on-0 safety (explicit).** By lemmas M1–M4 (#8), E is
entered only from D-on-1, and a halt requires an F-on-0
with left triple (0,1,0) (equivalently a C-on-0 with
left pair (0,1) feeding D-on-1 with a 0 beyond). D-on-0
is the transition 1RF: it writes 1 and exits **right**
in state F, so no D-on-0 read is ever followed by an
E-read; in every D-on-0 occurrence in this phase
(probe-prefix E2/E4, PUSHX ignition, the two-block
deviation's probe) the next reads are F-on-0 with
triple (0,0,1) and then C-on-1. The C-on-0 contexts
occurring anywhere in the re-formation are (1,1)
(B-entry and F-entry) and (0,0) (F-entry) — never
(0,1) — and the F-on-0 triples are (1,1,0), (0,0,0),
(0,0,1), (1,1,1), (0,1,1), (1,0,1) — never (0,1,0).
Hence no excursion of the re-formation, derived or
deviation, can reach E-on-0. ∎

**Audits (exact simulator, phase20_sim `run`).**
ESC(L, 8): L = 12, 14 (3×10^5 steps): E0 = 0, danger = 0,
D0 = 2. L = 16: D0 = 3 (1 deviation). L = 18, 20, 24,
28, 34, 40 (2×10^5 – 4×10^6 steps): E0 = 0, danger = 0,
D0 = 4 (2 deviations). Synthetics ESC(12, 4): D0 = 4
(two re-formations inside the window — the second
iteration's probe prefix), ESC(12, 6), ESC(12, 12):
D0 = 2; ESC(20, 12): D0 = 4. Iteration-3 instance
(2×10^5 steps): E0 = 0, danger = 0, D0 = 1.

**Classification.** Full transition classification
(phase20_parse) of the re-formation + era at
L = 8, 10, 12, 14 (β = 8): every transition is a model
rule or a derived §1/§5 piece (probe prefix ×5, POP2,
terminal POP, blank Stage A, PUSHdeg); e.g. ESC(12, 8)
over 6000 steps: TDN 124, TUP 115, PUSH 122, POP 125,
STGA 7, PUSHdeg 1, unexplained = exactly the 8 derived
pieces. ESC(16, 8): additionally the PUSHX deviation
(§4.1). Iteration-3 instance over 60000 steps: TDN
1224, TUP 1215, PUSH 1226, POP 1239, STGA 11, PUSHdeg 1,
unexplained 14 = 3 TDN-at-2/POP-at-0 pairs (§2, source
or successor unparseable in the standard frame), the
§6.1 deviation cluster (5), TUP2 (1), terminal POP (1),
blank Stage A (1).

**Tools.** `phase20_sim.py` (exact simulator + audit,
validated step-exact against `phase15.c`), 
`phase20_parse.py` (frame parser + classifier),
`phase20_grind.py` (word-model grind driver). Configs
`p20-esc*.cfg`, `p20-iter3.cfg`. The background phase10
run was not touched.
