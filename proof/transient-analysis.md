# BB(6) holdout #168016 — analytic attack on the post-R transient (Phase 11, 2026-11-25)

- Seed index: **168016**
- Spec: `1RB1RA_1RC1LB_0LD0RA_1RF1LE_---1LF_1LC0LF`
- Starting point: Phase 10 (`third-family.md`) — from the record
  configuration R = 1¹⁷ 0 1⁹⁷ 0 1¹³⁷ 0 the machine runs a bounded
  transient, ≥ 1.02×10¹² steps with no halt, no state-B record, no
  head escape: rigid frame 1¹⁷ · fluctuating second block · a
  working region of (0 1²)-pairs separated by odd 0-gaps · one long
  0-gap G · terminal 1². Phase 10 measured G ratcheting down 13
  times and never up, mechanism unknown. This phase attacks the
  transient itself: a macro-step for the working region (§1), the
  ratchet mechanism (§2), and a classification (§3).

Frame: R frame of `phase10.c` (tape of R occupies [0, 252], head
253). "Isolated step" = steps since R; deviation step = isolated +
403,455. All tools are new (`phase11.c`, validated to reproduce the
expected dump at isolated step 9,596,545 exactly — state, head,
ones, full RLE); the still-running `phase10` process was only ever
read, never disturbed (its checkpoint advanced 1.035×10¹² →
1.14×10¹² isolated steps during this phase).

**Headline.** The transient is not chaotic. It decomposes into
three mechanisms, each now understood:

1. a **bounce** macro-step at the left interface (mean cost exactly
   12 steps) whose excursion depth obeys an exact geometric law
   (ratio 1/2 per level) and which acts on the gap list as a
   **stack**: only the top ≤ 2 entries are ever rewritten, pushes
   and pops happen only at the top (§1);
2. the **ratchet**: a rare full-depth bounce *collapses* the whole
   pairs region into one solid block, and the return sweep writes
   a fresh pair onto the first two cells of the long gap —
   **G := G − 2 exactly**, by a 3-step local rule. No local
   interaction increases G (§2);
3. at **G ≤ 2 the barrier dissolves** and the machine falls into a
   second, right-edge regime with its own sawtooth gap cycle;
   from a fully solid right end a fresh long gap is carved out
   and the standard transient resumes. **G is a sawtooth, not a
   countdown** — the naive routes to a decision via G are closed
   (§3).

#168016 remains **undecided**. What is proven, what is verified
computation, and what is observation is labelled throughout.

## 1. The macro-step: bounces at the left interface

### 1.1 The section

From R, over 9.6×10⁶ steps the head spends 97.7% of steps in cells
[60, 120), 2.3% in [120, 180), 0.0008% in [180, ∞), and **never**
visits cells < 96: the head lives at the interface between block2
and the working region, probing right with a geometrically
decaying penetration histogram (visit counts ∝ 0.75^Δ per cell
from the peak at ≈107). All 1345 available dumps (isolated steps
596,545 … 1.042×10¹², from `dev132q-long.log`,
`phase10-expected.txt`, and a snapshot of `phase10-run.log`)
decompose into the clean structural form
1¹⁷ 0 1^B2 0^g0 (1² 0^g)* 1² 0^G 1² with **zero exceptions**;
in every dump the head sits in [89, 121], and a non-2 working
1-run occurs only at index 0 (the "shuttle" block, values 1–16+).

The head's motion is a sequence of **bounces**: a rightward sweep
(turning points at local maxima are in state B or C, ≈50/50) and a
leftward return to a local minimum at head ∈ [93, 100] (state B or
C, ≈50/50). Taking the section at head local minima (direction
change −→+), the tape is in the clean structural form at **every
one of 1,666,667 consecutive returns** over 2×10⁷ steps (0
unclean). This is the macro-step.

### 1.2 Exact statistics of one bounce (verified computation)

Over 1,666,666 bounces (2×10⁷ steps from the dump at isolated
5×10¹¹; a second, independent 2×10⁶-step window agrees to the
same rationals):

- **Cost:** mean exactly 12.000 steps/bounce (min 1, max 82 in
  the 2×10⁶ window).
- **Excursion depth** (cells beyond the minimum): always odd;
  P(depth = 3) = 1/4 (416,666 bounces) and
  **P(depth = 2k+1) = 3·2^-(k+1) for k ≥ 2** — 5: 624,999;
  7: 312,500; 9: 156,250; 11: 78,125; …; 45: 1. Counts match the
  rationals to ±1 out to depth 45. The depth law is exactly
  geometric with ratio 1/2 per level — the same 1/2-per-level
  law as the S′ cascade's cost doubling (Phases 6–8).
- **Action on the gap list:** the *rewrite depth* (length of the
  changed prefix, longest-common-suffix measure) is **≤ 2 in
  every one of the 1,666,665 transitions** (0: 416,666 = 1/4;
  1: 416,668 = 1/4; 2: 833,331 = 1/2). Δ#gaps ∈ {−1: 1/4, 0: 1/2,
  +1: 1/4}. A pop removes gaps[0] and a push adds at gaps[0]
  (proved by the pop test in §1.3): **the gap list is a LIFO
  stack with its top at the left**; entries below the top two
  are immutable until surfaced.
- **Interface variables:** ΔB2 ∈ {+1, −1, −2, +2}, each ≈ 1/4.
  Δshuttle: +2 (1/2), 0 (1/4), −2j with probability 2^-(j+2)
  (j ≥ 1). Δones: +1 (1/2), 0 (3/8), −2 (1/16), −4 (1/32), …
  Stack height (#gaps) ranges 9–28, shuttle 2–42, B2 68–89 in
  this window. G never changes across a bounce (0 / 1,666,665).

### 1.3 Determinism and locality

The bounce outcome is a deterministic function of the full
configuration (it is a TM); the content is its *locality*.
Grouping 1,666,665 transitions by the observable local state
L = (state, head, B2, shuttle, gaps[0..K]): for K = 3 there are
10,627 distinct L, of which 816 show > 1 outcome, covering
416,463 visits = 24.99% — **exactly the pop probability 1/4**.
The ambiguity is fully explained: on a pop, the new gaps[K−1] is
the previously unseen gaps[K], so no finite window can predict
it; removing cost/depth from the outcome does not change the
ambiguous set. For K = 5 the same ≈1/4 of visits is ambiguous,
again the pops. So the bounce map reads the stack top plus
however far its excursion reaches, writes only the top ≤ 2
entries, and is otherwise a function of (interface state, stack
top, excursion depth realisation) — a genuine macro-step with
finite description at the top and a geometric depth law.

## 2. The ratchet: collapse + pair-writing (G := G − 2)

### 2.1 Pinpointing (verified computation)

Phase 10's 13 decrements, re-extracted from all 1345 dumps: in
the settled regime every decrement is **exactly −2** (the early
−8, −6, −8 are several events inside one wide formation-stage
bracket). The two clean late brackets were pinpointed with the
zoom tool (restart from the bracket's opening dump, watch the
right-end structure):

- G = 68 bracket (isolated 412×10⁹ … 413×10⁹): first right-end
  change at **isolated step 412,316,860,191**;
- G = 66 bracket (isolated 824×10⁹ … 825×10⁹): first right-end
  change at **isolated step 824,633,720,597**;
- formation stage (from isolated 596,545, G = 106): first
  right-end change at **isolated step 786,397**.

In all three cases the first change is the same event: a
**collapse**. The pairs region is replaced wholesale by a single
solid block; the tape becomes

    1¹⁷ 0 1⁹⁵ 0 1^L 0^G 1²      (L = 70, 72, 31 resp.;
                                 B2: 73→95, 75→95, 89→96;
                                 G unchanged at the collapse instant)

with the head back inside the block in state B. A collapse is a
bounce whose excursion reaches the *bottom* of the stack: its
rightward sweep (A on 0 → `1RB`, B on 0 → `1RC` write 1s) fills
every gap instead of reflecting. Rarity is consistent with the
depth law: P(excursion reaches the bottom of an h-stack) ~
2^-h per bounce; at h ≈ 25 and 1 bounce / 12 steps this gives
one collapse per ~10⁸–10⁹ steps, matching the observed
3.2×10⁸ and 6.3×10⁸ steps between the pinpointed collapses and
their bracket starts (and the much higher rate, ~10⁶–10⁷ steps,
in the formation stage, where the stack is only ~10 high).

### 2.2 The decrement, step by step (exact trace)

From the G = 68 collapse configuration (head 136, state B,
block 1⁷⁰ at [114, 183], gap [184, 251], terminal [252, 253]),
the trace shows the head sweeping right through the block in
state A, then:

    step 94: A on 0 (cell 184) -> `1RB`  write 1, right, B
    step 95: B on 0 (cell 185) -> `1RC`  write 1, right, C
    step 96: C on 0 (cell 186) -> `0LD`  reflect left, D
    step 97: D on 1 (cell 185) -> `1LE`  left, E
    step 98: E on 1 (cell 184) -> `1LF`  left, F
    step 99+: F sweeps left, erasing the block (`0LF`)

Net effect: a fresh pair 1² sits on the first two cells of the
long gap and **G is smaller by exactly 2**; the F-sweep then
begins the re-expansion. The identical event shape was verified
at G = 66 (via the collapse run), and synthetically at G = 4 →
2 from a hand-built collapse configuration (decrement complete
by step 113, same `1^55 0^14 1²` post-event anatomy).

**Re-expansion:** the collapsed block is eroded by F-sweeps
into a secondary gap and pairs are re-carved from its right end
(the secondary "pregap" shrinks by 2 per carving event) over
~10⁵–10⁶ steps; a recognisable pairs region with a fresh stack
is restored, with G fixed at its new value. The stack after a
collapse is regenerated, not restored.

### 2.3 Can G increase? (local case analysis + adversarial tests)

- **Single-interaction table** (pattern 1⁶ stub · 0⁸ gap · 1²
  terminal, head placed on the gap's first cell in each state,
  run to window exit): A-entry writes a pair (−2, as above);
  B-entry fills exactly one cell (a defect, absorbed later);
  C-entry reflects immediately (`0LD`), no change; D- and
  F-entries rattle locally (they move left on 1, so the global
  dynamics cannot deliver them to the long gap's left edge
  moving right — and in 1.02×10¹² real steps plus all zooms,
  the **only** arrival mode ever observed at the long gap is
  the A-sweep of a collapse); E-entry is the halt itself.
- **Pair erasure from the left:** the only left-side eraser of
  a 1 is C (`0RA`/`0LD`); C on 1 is followed within two steps
  by A/B writing 1s on the gap side before any reflection —
  the last pair can shift right (G − 2) but cannot be deleted
  into the gap by a left-side interaction.
- **Adversarial seeding:** head placed at the terminal pair
  (cell 252, state F) or just right of it (cell 254, state F)
  on the real G = 66 dump configuration: the terminal is
  destroyed, the head breaks out right, and the machine falls
  into the §3 right-edge regime with G ≤ 7 — **G never
  increases**; both seedings converge to identical G-watch
  sequences. Getting behind the terminal is anyway unreachable
  from the left: every gap entry writes ≤ 2 cells and reflects
  (the gap is a one-way barrier), and the collapse sweep
  itself stops at the gap edge via the §2.2 rule whenever
  G ≥ 3.

Conclusion, honestly labelled: an increase of G is not merely
unobserved (0 increases in 1345 dumps over 1.02×10¹² steps and
in every targeted simulation); every local interaction that
can touch the long gap leaves it unchanged, shrinks it by
exactly 2, or destroys the terminal structure. A *global*
proof that no other arrival mode at the long gap exists is
still missing — that is the remaining gap in the ratchet
argument, stated plainly.

## 3. Classification, and the G ≤ 2 endgame

### 3.1 What the dynamics is

At the bounce section the transient is exactly:

> **finite interface control** (state, head offset, B2, shuttle
> — all bounded in practice: B2 ∈ [68, 97], shuttle ∈ [1, 42])
> **+ an unbounded LIFO stack of odd gap values** (height 9–28
> observed, values 1–21+), rewritten only at the top,
> **+ the long gap G**, coupled to the stack only by collapses
> (full-depth bounces): each collapse sets G := G − 2 and
> regenerates the stack.

It is **not a finite-state process** (the stack is unbounded),
**not a queue** (LIFO order verified: pops remove gaps[0],
deep entries are immutable until surfaced — rewrite depth ≤ 2
in 1.67M consecutive macro-steps), **not a simple counter**
(the stack carries arbitrary odd values, and collapses reset
it wholesale), and **not chaotic** in any quantitative sense:
the bounce cost is exactly 12 on average, the depth law is
exactly geometric with ratio 1/2, and every Δ-distribution is
an exact dyadic rational over 1.67M samples. The depth law is
the carry law of a binary counter (P(carry ≥ k) = 2^-k), with
the stack entries playing the role of digits and the shuttle
as an accumulator (Δshuttle = −2 per carry level on deep
bounces, +2 on the shallowest) — but the digits carry arbitrary
odd values, so "counter" is an analogy for the depth process,
not a reduction. The honest classification: a **deterministic
one-stack pushdown process with a catastrophe reset**, the
catastrophe being the collapse that couples the stack to G.

### 3.2 The endgame at G ≤ 2: regeneration, not termination

Synthetic collapse configurations (the §2 anatomy with G
replaced) show the countdown does **not** decide anything:

- **G = 4:** the standard decrement fires (step 113): G = 2.
- **G = 2:** the §2.2 rule breaks down (C at the third cell
  reads the terminal's 1, not 0). The terminal pair is
  absorbed into the working region; the head crosses to the
  right edge and stays there. Over 10⁹ steps this **right-edge
  regime** is stable and self-sustaining: head confined to
  [113, 240] (72% of steps in [120, 180), 28% in [180, 240),
  13 steps total in [60, 120) — the left interface is frozen,
  B2 = 96 throughout), span 230 → 240 after an initial
  254 → 230 transition shrink, ones ∈ [196, 206], and a small
  gap at the right edge **sawtooths**: rises to 13–17, erodes
  by −2 steps to 1, regenerates — period ≈ 10⁸ steps (cycles
  observed at ≈5.1×10⁷, ≈1.01×10⁸, ≈2.02×10⁸ steps). No halt
  and no head escape in 10⁹ steps (state-B records were not
  watched by this tool; the span stayed < 254 throughout).
- **G = 0** (right end fully solid): the return sweep carves
  a pair and a fresh gap of 16 within 117 steps; the gap grows
  to ≈39 by 10⁶ steps as the block is reprocessed, and the
  standard transient — with the −2 ratchet (39 → 37 → 35 →
  33 over the next 10⁷ steps) — resumes.

So G sawtooths on two timescales: a slow −2 ratchet
(10⁸–10¹¹ steps per decrement at current stack heights) and,
at the bottom, regeneration. In the real trajectory G = 64
would need ~31 more collapses to reach 2 — of order 10¹³
steps at the observed rates — whereupon the evidence says the
machine enters the right-edge regime rather than halting or
producing a record family.

### 3.3 Decidability assessment

No reduction to a known decidable class was achieved, and the
three naive routes are now closed by the mechanisms above:

1. *"G is a counter"* (prove non-halting by monotone decrease
   to a known configuration): false — G regenerates (§3.2).
2. *"G → 0 decides"*: false — G ∈ {0, 2} leads to another
   persistent regime, not a halt or a bounce family.
3. *Finite-state / CTL / bouncer methods*: inapplicable — the
   stack is unbounded and collapses are global resets.

What a proof would need is a single invariant covering all
three regimes (left-interface stack process; collapse and
re-expansion; right-edge sawtooth). The cleanest formulation
found: the halt is E-on-0; E arises only from D-on-1, and in
every observed interaction E is immediately followed by
`1LF` on a 1 (the §2.2 step-back is the archetype). Proving
"E is never reading 0" as an invariant of the composed system
— equivalently, that every 0-region is entered only in states
A, B, C, D, F with the §2.3 reflection behaviour — is a
well-posed target, but it is a global invariant over an
unbounded stack, i.e. precisely the hard core that remains.

**Status: #168016 is still undecided.** Phase 11 converts the
transient from a black box into three explicit mechanisms
(stack bounces with exact laws; collapse + pair-writing
ratchet G := G − 2; regeneration at G ≤ 2), each verified
computationally and, for the ratchet's local step, by exact
trace. The Phase 10 long run continues in the background
(checkpoint at isolated step 1.14×10¹² at the end of this
phase); its non-halting bound grows accordingly, with the
standing caveat that the pre-R segment rests on the
unmechanised Phase 5–9 human proofs.

*Files: `phase11.c` (modes `run` / `zoom` / `trace` / `bounce`;
independent of all phase10 files), `phase11_parse.py` +
`phase11-dumps.json` (1345 dumps, structural decomposition),
`phase11_cfg.py` (config builder), `phase11-bounce.log`,
`phase11-bounce20m.log` (1,666,667 section records),
`phase11-micro.log`, `phase11-trace.log`,
`phase11-zoom-g68.log`, `phase11-zoom-g66.log`,
`phase11-zoom-early.log`, `phase11-collapse.log`,
`phase11-collapse-trace.log`, `phase11-syng2-long.log`
(10⁹-step right-edge regime), configs `phase11-*.cfg`.
Nothing posted externally.*
