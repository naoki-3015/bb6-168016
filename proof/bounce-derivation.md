# BB(6) holdout #168016 — deriving the bounce rules: the excursion induction (Phase 13, 2026-11-25)

- Seed index: **168016**
- Spec: `1RB1RA_1RC1LB_0LD0RA_1RF1LE_---1LF_1LC0LF`
- Starting point: Phase 12 (`post-R-proof.md`) reduced the halt
  to one tape pattern (lemma M4) and extracted the section
  dynamics of the post-R transient as a four-rule rewrite system
  (TDN / PUSH / POP / TUP) preserving invariant I — but the
  rules were *extracted from observation, not derived*
  (obstruction 1 of `post-R-proof.md` §6). **This phase derives
  them.** Each rule is an explicit shift-rule computation from
  the transition table; the only induction is on the length of
  a swept 1-run (the shuttle). The excursion turns out to be a
  *single probe* — there is no within-bounce recursion into the
  stack at all — and the derivation yields one refinement of
  Phase 12: POP's cost is exactly **2s + 3** (Phase 12's
  empirical "11 + 4t" is the same number along real POP chains,
  where s = 4 + 2t).

**Verdict up front.** Obstruction 1 is **closed**: under the
hypotheses H1–H3 of §1 (a section in structural form satisfying
I, and — for B-sections only — at least one pair after the
shuttle), every bounce of the real machine realises exactly the
applicable §2.3 rule of `post-R-proof.md`, with the stated
successor and cost, and its complete within-bounce event list
is: at most one C-on-0 (PUSH and TUP only; B-entry, left
context (1, 1), hence safe by lemma M2) and at most one F-on-0
(PUSH and TUP only; left triple never (0, 1, 0) — it is
(1, 1, 1) in the invariant region). In particular M4's halting
pattern never occurs mid-bounce, E never reads 0, and D never
reads 0. Invariant I is therefore an invariant of the
*machine's* section dynamics, not only of the observed
dynamics, on every bounce whose start section satisfies
H1–H3. What remains open is exactly Phase 12's obstructions 2
and 3 (collapse restoration; the right-edge regime) and the
formation stage before the first H1-section — see §6.
Labels: (P) general proof from the transition table,
(C) exhaustive finite check, (O) observation.

## 1. Setup, coordinates, hypotheses

Transition table (write, move, next state), rows = state,
columns = read 0 / read 1:

    A: 1RB 1RA     B: 1RC 1LB     C: 0LD 0RA
    D: 1RF 1LE     E:  —  1LF     F: 1LC 0LF        (— = halt)

A **section** is a head local minimum in the standard
transient, with tape in the structural form (Phase 11 §1.1,
Phase 12 §2.1)

    1^17 0 1^B2 0^g0 1^s (0^gi 1^2)* 0^G 1^2 ,

w = [g0, g1, …, gk] the gap word (g0 after B2, g1 after the
shuttle 1^s, then one gap before each pair 1^2), G the long
gap, terminal run T = 2. Coordinates are the R frame (first
cell of the nonblank span = 0). Put

    x := 18 + B2        (first cell after the B2 block).

So the B2 block is [x−B2, x−1], g0 starts at x, the shuttle is
[x+g0, x+g0+s−1]; a C-section has head at x−2 (state C), a
B-section has head at x (state B, and g0 = 1 so the head sits
on the unique g0 cell and the shuttle is [x+1, x+s]).

**Hypotheses (the derivation's exact scope).**

- **H1** The start configuration is a section as above with
  B2 ≥ 2, every gap odd, s even.
- **H2** State/head are as in invariant I3: state C at x−2
  with s = 2, or state B at x with g0 = 1 and s ≥ 4. (The
  B-derivations in fact use only s ≥ 2; s ≥ 4 is I's form.)
- **H3** (B-sections only) At least one pair follows the
  shuttle, i.e. w has ≥ 2 entries, so g1 is a genuine
  inter-run gap and the cell x+s+2 exists in the structural
  form (pair1's first cell if g1 = 1, g1's second cell if
  g1 ≥ 3). C-bounces need no such hypothesis: they never reach
  past the shuttle's first cell.

Nothing else is assumed: the deeper gaps g2, g3, … are
arbitrary odd numbers, G and the terminal are arbitrary, and
the stack height beyond H3 is irrelevant — the stated *reach*
of each bounce (§3–§4) never reads a cell outside it. Where
H3 fails, the excursion meets G instead of g1 and the event is
the Phase 11 collapse, not a fifth rule (§5.3).

## 2. Three sweep lemmas and the probe (P)

Each is a one-line induction on a run length from the table.

**Sweep-A.** Head in state A on a 1-run: A-on-1 is `1RA`
(write 1 = no change, move R, stay A). Crossing a 1-run of
length n takes n steps, changes nothing, and exits in state A
on the first cell right of the run. ∎

**Sweep-B.** Head in state B on a 1-run: B-on-1 is `1LB`.
Crossing a 1-run of length n leftward takes n steps, changes
nothing, exits in state B on the first cell left of the run. ∎

**Sweep-F.** Head in state F on a 1-run: F-on-1 is `0LF`
(write 0, move L, stay F). Erasing a 1-run of length n
leftward takes n steps, leaves 0^n, and exits in state F on
the first cell left of the run. ∎

**Probe Lemma.** Let z be the first cell of a 0-gap of width
≥ 3 (tape[z] = tape[z+1] = tape[z+2] = 0), and suppose the
head is in state A on z. Then in exactly 5 steps the machine
sets tape[z] = tape[z+1] = 1 (z+2 unchanged) and the head is
in state F on z−1:

    A@z   on 0 -> 1RB   (z := 1)
    B@z+1 on 0 -> 1RC   (z+1 := 1)
    C@z+2 on 0 -> 0LD   (reflection; no change)
    D@z+1 on 1 -> 1LE   (reads B's write)
    E@z   on 1 -> 1LF   (reads A's write)

The single C-on-0 of the probe is B-entry with left context
(tape[z], tape[z+1]) = (1, 1) at its read — the two cells just
written — hence safe by Phase 12's lemma M2. The single D-read
and E-read are on 1s. No F-on-0 occurs. ∎ (Finite inspection;
this is the reflection archetype of Phase 11 §2.2.)

## 3. The C-bounces (P)

**Common prefix.** From a C-section (head C at x−2,
tape[x−2] = 1 as B2 ≥ 2):

    C@x−2 on 1 -> 0RA   (x−2 := 0)
    A@x−1 on 1 -> 1RA   (head A at x; tape otherwise unchanged)

2 steps, both moving R. Now split on g0 (odd by H1, so
g0 = 1 or g0 ≥ 3 — the guards are total).

### 3.1 TDN (g0 = 1), cost 6

    A@x   on 0 -> 1RB   (x := 1; x+1 is the shuttle's 1st cell)
    B@x+1 on 1 -> 1LB
    B@x   on 1 -> 1LB   (the cell A just wrote)
    B@x−1 on 1 -> 1LB   (head B at x−2, reading the 0 of step 1)

End configuration: state B at x−2 on a 0; its next step
(B-on-0) moves R, so it is a genuine section. Tape changes:
x−2: 1→0, x: 0→1. Hence B2′ = B2 − 2 (the block now ends at
x−3), g0′ = 1 (cell x−2), and the run [x−1, x+s] — old B2
last cell, filled g0 cell, old shuttle — has length s + 2;
with s = 2 (H2) this is s′ = 4, and w′ = w (nothing right of
x+1 was read; max head x+1). This is exactly TDN. Cost
2 + 4 = 6. **Events: none** — the states visited are C, A, B
only; there is no C-on-0, no D, no E, no F anywhere in the
bounce. Move sequence + + + − − −: a single peak at x+1, so
the end configuration is the *first* local minimum after the
start. ∎

### 3.2 PUSH (g0 ≥ 3), cost 9

Continuing from the common prefix, the head is in state A on
x, the first cell of a gap of width g0 ≥ 3: the Probe Lemma
applies at z = x (its 5 steps are steps 3–7 here), leaving
tape[x] = tape[x+1] = 1 and the head in state F on x−1. Then:

    F@x−1 on 1 -> 0LF   (x−1 := 0; the B2 block's last cell)
    F@x−2 on 0 -> 1LC   (x−2 := 1, restoring step 1's erasure;
                         head C at x−3, reading tape[x−3] = 1)

End configuration: state C at x−3 on a 1; its next step
(C-on-1) moves R — a genuine section, and the first local
minimum after the start (moves: R×4, then L×5). Tape changes:
x−1: 1→0; x, x+1: 0→1; x−2: 1→0→1 (net unchanged). Hence
B2′ = B2 − 1 (block [x−B2, x−2]), g0′ = 1 (cell x−1),
s′ = 2 (cells x, x+1 — the probe's writes), g1′ = g0 − 2
(cells x+2 … x+g0−1, untouched), then the old shuttle as the
first pair and g1, g2, … unchanged:

    w′ = [1, g0−2] + w[1:] .

This is exactly PUSH. Cost 2 + 5 + 2 = 9. **Events:** one
C-on-0 (the probe's; B-entry, context (1, 1); safe by M2);
one D-on-1 and one E-on-1 (the probe's); one F-on-0, the last
step, at q = x−2 with left triple
(tape[x−5], tape[x−4], tape[x−3]). The three cells lie in
1^17 0 1^B2; the only 0 among them possible is the separator
at position 17, and the alignments give (1,1,0) for B2 = 2,
(1,0,1) for B2 = 3, (0,1,1) for B2 = 4, (1,1,1) for B2 ≥ 5 —
**never (0, 1, 0)** for any B2 ≥ 2, and (1, 1, 1) in the
invariant region (all observed windows have B2 ≥ 68). Max
head x+2; G and everything right of the shuttle untouched. ∎

## 4. The B-bounces (P)

**Common prefix.** From a B-section (head B at x on the
unique g0 cell, shuttle [x+1, x+s]):

    B@x   on 0 -> 1RC   (x := 1; the g0 cell joins B2)
    C@x+1 on 1 -> 0RA   (x+1 := 0; the shuttle's 1st cell)
    Sweep-A over shuttle cells 2..s (x+2 … x+s, all 1):
        s−1 steps, head A at x+s+1 (the first g1 cell)
    A@x+s+1 on 0 -> 1RB (x+s+1 := 1; head B at x+s+2)

Prefix cost 2 + (s−1) + 1 = s + 2. By H3, g1 is a genuine
odd gap; split on g1 = 1 vs g1 ≥ 3 (total).

### 4.1 POP (g1 = 1), cost 2s + 3

Now x+s+2 is pair1's first cell (a 1):

    B@x+s+2 on 1 -> 1LB   (the turn; pair1 is only read)
    B@x+s+1 on 1 -> 1LB   (the prefix's write)
    Sweep-B over shuttle cells s..2 (x+s … x+2, all 1):
        s−1 steps, head B at x+1, reading tape[x+1] = 0

End configuration: state B at x+1 on a 0; next step (B-on-0)
moves R — a genuine section, the first local minimum after
the start (moves R through step s+3, then L). Tape changes:
x: 0→1 (joins B2), x+1: 1→0, x+s+1: 0→1; nothing else (max
head x+s+2, read-only at the turn; pair1 and beyond are
untouched). Hence B2′ = B2 + 1, g0′ = 1 (cell x+1), and the
run [x+2, x+s+3] — old shuttle cells 2..s (s−1 cells), the
written g1 cell, and pair1 (2 cells) — is the new shuttle,
s′ = s + 2; the gap after it is the old g2, i.e.

    w′ = w[1:]   (pop).

This is exactly POP, with cost (s+2) + 2 + (s−1) = **2s + 3**.
**Events: none** — the states visited are B, C (once, on a 1),
A; there is no C-on-0, no D, no E, no F in the whole bounce.
Phase 12's cost formula "11 + 4t" is refined: in the real
window every POP has cost exactly 2s + 3 (§5.1); the apparent
free parameter t was (s − 4)/2, since along a chain of
consecutive POPs s grows by 2 each time. ∎

### 4.2 TUP (g1 ≥ 3), cost 2s + 6

Now x+s+2 is g1's second cell (a 0), and the Probe Lemma
applies at z = x+s+1 (the prefix's A-step was its first step):

    B@x+s+2 on 0 -> 1RC   (probe step 2)
    C@x+s+3 on 0 -> 0LD   (probe step 3, reflection)
    D@x+s+2 on 1 -> 1LE   (probe step 4)
    E@x+s+1 on 1 -> 1LF   (probe step 5; head F at x+s)
    Sweep-F over shuttle cells s..2 (x+s … x+2, all 1):
        s−1 steps, those cells := 0; head F at x+1
    F@x+1 on 0 -> 1LC     (x+1 := 1; head C at x, reading 1)

End configuration: state C at x on a 1; next step (C-on-1)
moves R — a genuine section, the first local minimum after
the start. Tape changes: x, x+1: →1 (both join B2); shuttle
cells 2..s: 1→0; x+s+1, x+s+2: 0→1 (the probe's writes);
nothing else (max head x+s+3; pair1 and beyond untouched).
Hence B2′ = B2 + 2 (block [x−B2, x+1]), g0′ = s − 1 (the
erased shuttle cells 2..s, positions x+2 … x+s), s′ = 2 (the
probe's writes), g1′ = g1 − 2 (cells x+s+3 … x+s+g1,
untouched), then pair1, g2, … unchanged:

    w′ = [s−1, g1−2] + w[2:] .

This is exactly TUP. Cost (s+2) + 4 + (s−1) + 1 = 2s + 6.
**Events:** one C-on-0 (the probe's; B-entry, context (1, 1);
safe by M2); one D-on-1, one E-on-1; one F-on-0, the last
step, at q = x+1 with left triple
(tape[x−2], tape[x−1], tape[x]) = (1, 1, 1) for every
B2 ≥ 2 (x−2, x−1 are B2 cells; x is the prefix-filled g0
cell) — never (0, 1, 0). ∎

## 5. Verification (C)

The derivations above are (P). They were also checked
computationally on data *not* used to derive them (the
derivations were worked out from four hand-traced instances:
TDN/PUSH at B2 = 80, TUP/POP at B2 = 79, s ∈ {4, 6, 8},
G = 66). Tools: `phase13.c` (single-bounce tracer with a
per-step M4/E-on-0 audit), `phase13_gen.py` (synthetic
section generator), `phase13_check_real.py`,
`phase13_verify.py`, `phase13_chain.py`.

### 5.1 The real window, in full

`phase13_check_real.py` tested the derived predictions —
successor state, B2, s, full gap word, and cost (including
POP = 2s + 3) — against **every transition of
`phase11-bounce20m.log`: 1,666,665 genuine transitions,
0 mismatches** (the single flagged item is transition 0,
whose start is the dump configuration in state F — by fiat
not a genuine section, as Phase 12 already noted). Rule
counts: PUSH 416,666; TDN 416,666; TUP 416,665; POP 416,667.
G never changed. This also settles Phase 12 §2.3's remark
that "PUSH depth 7, 9, 11, …" varies: it does not — every
PUSH has cost 9 and depth 5; the depth histogram of Phase 11
§1.2 is the *population* distribution of the four fixed forms
(depths: TDN 3; PUSH 5; POP s+1; TUP s+3) under the section
dynamics of s, not within-bounce variation.

### 5.2 Held-out synthetic battery

64 synthetic sections with parameters disjoint from the
derivation instances (B2 ∈ {5, 6, 33, 68, 97, 120}; s up to
20; g0 ∈ {1, 3, 15}; g1 ∈ {1, 3, 11}; G ∈ {2, 7, 21, 40, 54,
66} — including odd G and G = 2, which the bounce never
reads; minimal stacks: a single pair for POP/TUP, a single
gap for TDN/PUSH). Each was run for exactly one bounce with
the auditing tracer: **64/64** — successor, cost, and full
tape match the derived rule; M4 danger 0; no E-on-0; every
F-on-0 triple (1, 1, 1) (including at B2 = 5, the smallest
value for which §3.2 predicts (1, 1, 1)).

### 5.3 Chains, and the H3 boundary

- **Composition:** three synthetic sections were run for 300
  consecutive bounces each (`phase13 sections`), and every
  transition checked against the derived rules: **900/900,
  0 mismatches** — the end section of each bounce again
  satisfies H1–H3, so the derivation composes indefinitely
  (within the standard regime).
- **The boundary is real:** a B-section with *no* pair after
  the shuttle (w = [1], tape …1^6 0^10 1^2, B2 = 68, s = 6)
  does **not** follow POP or TUP. The excursion sweeps the
  shuttle, the probe fires inside G (A/B write its first two
  cells, C reflects, D/E step back), Sweep-F erases the
  shuttle, one F-on-0 with triple (1, 1, 1) lands the head in
  C at a section with G = 8: **G := G − 2 by the same probe** —
  the Phase 11 collapse/pair-writing event, reproduced
  step-for-step (`p13-collapse.log`). H3 is exactly the line
  between the four rules and the collapse.

## 6. Status after Phase 13

**Now proven (P), in addition to Phase 12's M1–M4 and the
preservation arithmetic:**

- Every bounce starting at a section satisfying H1–H3
  realises exactly the applicable rule of `post-R-proof.md`
  §2.3 (with POP's cost refined to 2s + 3), ends at the
  stated successor section, and contains no E-on-0, no
  D-on-0, no F-entry C-on-0, and no F-on-0 with left triple
  (0, 1, 0). Combined with Phase 12 §2.3's preservation
  arithmetic, invariant I is an inductive invariant of the
  machine's own section dynamics on such bounces, and by
  M1–M4 the machine cannot halt at any step of such a bounce.

**Still not proven (unchanged from `post-R-proof.md` §6,
minus obstruction 1):**

- **Obstruction 2 — collapse restoration.** When H3 fails,
  the excursion is a collapse (mechanism derived above at the
  probe level for the shallow synthetic case, and traced by
  Phase 11 in the real regime): G := G − 2 and the stack is
  regenerated. That re-expansion *must* restore a section
  satisfying H1–H3 is verified for two full real collapse
  cycles (Phase 12 §3) but not derived; the re-expansion is a
  ~10⁵–10⁶-step process, not a single bounce, and needs its
  own induction.
- **Obstruction 3 — the right-edge regime.** No section
  structure, no invariant; safety rests on the Phase 12 §4
  audit (5×10⁸ steps) and Phase 11's stability run. Its
  reachability from R is itself only projected.
- **Formation.** From R to the first section satisfying H1
  the dynamics is covered by the Phase 12 §4 event audit
  (10⁹ steps, single-point safe distribution) and Phase 11
  §1.1 (all 1345 dumps in clean structural form), not by the
  section derivation.

**Conclusion.** Obstruction 1 is closed: the four bounce
rules are now theorems about the machine (under H1–H3), not
fits to its observed behaviour, and the mid-bounce region —
the one place Phase 12 §2.4 identified where M4's pattern
could be attempted inside the standard regime — is proven
clean. The post-R proof as a whole still does not close:
the collapse restoration and the right-edge regime remain
computational facts rather than derivations. **#168016
remains undecided.** Nothing has been posted externally.

*Files: `phase13.c` (auditing single-bounce tracer + section
runner), `phase13_gen.py` (synthetic section generator),
`phase13_check_real.py` (derived rules vs all 1,666,665 real
transitions), `phase13_verify.py` (64 held-out synthetic
bounces), `phase13_chain.py` (900 composed transitions),
`p13-*.cfg`, `p13-collapse.log` (the H3-boundary collapse).
The phase10 background run was only read, never disturbed.*
