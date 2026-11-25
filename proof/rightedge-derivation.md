# Phase 15 — the right-edge regime derived: five mirror rules,
# invariant RI, and the safety proof (obstruction 3)

Machine #168016 (`1RB1RA_1RC1LB_0LD0RA_1RF1LE_---1LF_1LC0LF`), post-R
regime. This document closes obstruction 3 of `post-R-proof.md` §6:
the right-edge regime entered when Stage A / the bounce system reaches
a B-section with gap word `w = [1]` at `G = 2` (Phase 14 §5: the
probe's third step reads the terminal pair's first cell, the terminal
is absorbed, and the dynamics leaves the section system of invariant
I). Everything below is for the trajectory segment after that entry.
Status labels follow the project convention: **derived** = forced by
the transition table from the stated form (step list written out),
**verified** = checked exhaustively by machine over the stated range,
**open** = neither.

Tools: `phase15.c` (modes `trace`, `entry`, `rsec`, `sec2`),
`phase15_classify.py`, `phase15_classify2.py`,
`phase15_classify_stream.py`; configs `p15-e1.cfg`…`p15-e10.cfg`
(entry battery), `p15-r1.cfg` (small-geometry post-entry),
`p15-home1.cfg` (large-geometry home configuration).

The transition table (rows = state on symbol read; `w Mv N` = write,
move, next state; `---` = the halting transition, E on 0):

| state | on 0 | on 1 |
|---|---|---|
| A | `1RB` | `1RA` |
| B | `1RC` | `1LB` |
| C | `0LD` | `0RA` |
| D | `0RA` | `1LE` |
| E | `---` | `1LF` |
| F | `1LC` | `0LF` |

Micro-lemmas M1–M4 of `post-R-proof.md` §1 are used throughout:
halt ⟺ some E reads 0; M4: an F-on-0 read at cell q can lead to a
halt only if the left triple (tape[q−3], tape[q−2], tape[q−1]) at its
read is (0,1,0); M2: a B-entry C-on-0 (entered from a B step, i.e.
from `1RC`) halts only if its left context (tape[p−1], tape[p−2]) is
(1,0) (M1), in particular context (1,1) is safe.

---

## 1. The entry excursion (derived + verified)

Phase 14 §5 pinpoints the exit from the I-regime: a B-section with
`w = [1]` at `G = 2`. By invariant I the tape there is

```
σ_entry(B2, s) = 1^17 0 1^B2 0^1 1^s 0^2 1^2 ,
head B on the g0 cell (position x = 18 + B2), s even, s ≥ 2.
```

(g0 = 1, shuttle s, the single gap of w is G = 2 itself, terminal
pair.) The bounce from σ_entry does **not** satisfy the hypotheses of
any of TDN/PUSH/POP/TUP/Stage A: the common B-prefix fills g0, erases
the shuttle's first cell, sweeps the shuttle and fills G's first cell
— and then, where POP/TUP would turn or probe inside G, G has a
second cell that is also filled, and the sweep continues into the
terminal pair. The full step list (forced by the table; `z` denotes
the first blank cell, z = x + s + 5):

1. *(common B-prefix, s+2 steps)* `B` fills g0 (`1RC`); `C` erases
   shuttle[0] (`0RA`); Sweep-A over shuttle[1..s−1] (`1RA` ×(s−1));
   `A` fills G[0] (`1RB`). Head `B` on G[1].
2. `B` fills G[1] (`1RC`). Head `C` on terminal[0].
3. `C` erases terminal[0] (`0RA`). Head `A` on terminal[1].
4. `A` crosses terminal[1] (`1RA`). Head `A` on z (blank).
5. *(probe in the blank, 5 steps)* `A` writes z (`1RB`); `B` writes
   z+1 (`1RC`); `C` reflects at z+2 (`0LD`) — **the excursion's only
   C-on-0, B-entry, left context (tape[z], tape[z+1]) = (1,1)**;
   `D` steps back on z+1 (`1LE`); `E` steps back on z (`1LF`).
   Head `F` on terminal[1].
6. `F` erases terminal[1] (`0LF`). Head `F` on terminal[0] (the cell
   erased in step 3).
7. `F` on 0 at terminal[0] (`1LC`): left triple
   (tape[x+s], tape[x+s+1], tape[x+s+2]) = (shuttle's last cell,
   filled G[0], filled G[1]) = **(1,1,1)**. Head `C` on G[1].

**Entry theorem (derived; verified on 10/10 battery configs).**
From σ_entry(B2, s) the machine reaches, in exactly **s + 12** steps
and with no other head local minimum in between, the configuration

```
σ_re(B2, s) = 1^17 0 1^(B2+1) 0^1 1^(s+2) 0^1 1^2 ,
head C on the second-to-last cell of the run 1^(s+2),
```

with event inventory exactly {one C-on-0 (B-entry, context (1,1)),
one D-on-1, one E-on-1, one F-on-0 (triple (1,1,1))} — in particular
no E-on-0 and no M4 pattern. Net effect: the terminal pair is
destroyed and a fresh terminal pair is created two cells further
right (span +2); the shuttle grows by 2 (s → s+2) by absorbing the
two filled G cells and the refilled terminal[0]; B2 grows by 1 (the
filled g0 cell joins it); the gap after the big run is 1 (the erased
terminal[1]).

*Verification.* `phase15 entry` on the battery
(B2, s) ∈ {(30,22), (95,70), (5,4), (68,6), (2,4), (40,30), (1,4),
(10,2), (120,130), (3,8)}: 10/10 PASS (cost s+12, end runs
[17, 1, B2+1, 1, s+2, 1, 2], head and state as stated, audit clean).
Cross-check against Phase 14: for (30,22) the end configuration is
exactly section 1539 of `phase14-sections-g6.log` (step 18,450 =
18,416 + 34; C, head 72, B2 = 31, s = 24, G = 1, T = 2). The σ_coll
form of the entry (head B inside the L block, Phase 14 §5) reduces
to σ_entry by Sweep-B (Phase 14 §3.1), so the theorem covers the
actual trajectory's exit, whose parameters are (B2, s) = (30, 22)
in the (30,18,6) synthetic chain.

**Definition (right-section).** σ_re is the first *right-section*:
a head local minimum of the form

```
tape = 1^17 0 1^B2 0^1 · W,   W = 1^β (0^g 1^r)* ,
head C at the second-to-last cell of the first working run 1^β,
```

where the prefix `1^17 0 1^B2 0^1` (with B2 = B2_entry + 1) is the
*frozen prefix* and W is the *working region*: β = s + 2 at entry,
then a (possibly empty) list of (gap, run) pairs ending with a run
(the last run is the terminal run; beyond it, blank). A *B-form*
right-section has head B on the first gap cell after β instead.
All sections of §2 are at β's right end; §3 shows no others occur.

---

## 2. The five mirror rules (derived)

From a right-section, the head's excursion to the next head local
minimum is forced by the table into exactly one of five rules —
mirrors of TDN/PUSH/POP/TUP (Phase 13) plus the entry-like RPROBE.
Write W = [β, g1, r1, g2, r2, …] (runs and gaps alternating, ending
with a run; k = number of runs after β). "Probe at u" is the Probe
Lemma sequence of Phase 13 §2 at a 0-cell u with tape[u+1] =
tape[u+2] = 0: A writes u, B writes u+1, C reflects at u+2 (the
excursion's only C-on-0, B-entry, context (1,1)), D and E step back
on the two written 1s; head F on u−1; 5 steps.

### C-form sections (head C at β_end − 1)

**RTDN** — guard g1 = 1 (k ≥ 1). Steps: `C` erases β_end−1 (`0RA`);
`A` crosses β_end (`1RA`); `A` fills g1 (`1RB`); `B` turns on r1[0]
(`1LB`); Sweep-B back over the filled g1 cell and β_end (`1LB` ×2);
lands `B` on the erased cell. **Cost 6. Effect: β −= 2, r1 += 2,
→ B-form. Events: none.**

**RPUSH** — guard g1 ≥ 3. Steps: `C` erases β_end−1; `A` crosses
β_end; probe at g1[0]; `F` erases β_end (`0LF`); `F` on 0 at
β_end−1 (the erased cell) → `1LC`, landing `C` at β_end−2.
**Cost 9. Effect: β −= 1; g1 is replaced by (1, pair 2, g1−2) —
the erased β_end cell is the new gap 1, the probe writes are the
new pair. → C-form. Events: the probe's C-on-0 (B-entry (1,1)),
D-on-1, E-on-1, and one F-on-0 whose left triple is (1,1,1) if
β ≥ 4, (1,0,1) if β = 3, (1,1,0) if β = 2** (the cells left of the
erased cell are β cells, then the prefix separator 0, then B2
cells — never (0,1,0)).

### B-form sections (head B at β_end + 1; §3 gives g1 = 1)

Common prefix (2 steps): `B` fills g1 (`1RC`); `C` erases r1[0]
(`0RA`); then Sweep-A over r1[1..] (r1 − 1 steps), head A on the
first cell after r1.

**RPOP** — guard g2 = 1 (k ≥ 2). Steps (after prefix): `A` fills
g2 (`1RB`); `B` turns on r2[0] (`1LB`, read-only); Sweep-B back
over the filled g2 cell and r1[1..] (r1 steps); lands `B` on the
erased r1[0]. **Cost 2·r1 + 3. Effect: β += 1 (the filled g1 cell
joins β); r1 and r2 merge: r1 := r1 + r2 (cells r1[1..], the filled
g2, r2); → B-form. Events: none.**

**RTUP** — guard g2 ≥ 3 (k ≥ 2). Steps (after prefix): probe at
g2[0]; Sweep-F over r1[1..] (r1 − 1 steps, erasing); `F` on 0 at
r1[0] → `1LC`, landing `C` on the filled g1 cell (a 1). **Cost
2·r1 + 6. Effect: β += 2 (filled g1 and restored r1[0]); g1 :=
r1 − 1 (the erased r1[1..]); a pair 2 is written at g2[0..1] and
g2 := g2 − 2; → C-form. Events: probe C-on-0 (B-entry (1,1)),
D-on-1, E-on-1, one F-on-0 with left triple (1,1,1) if β ≥ 2,
(0,1,1) if β = 1** (cells: β's last two cells and the filled g1
cell; for β = 1 the prefix separator supplies the 0 — never
(0,1,0)).

**RPROBE** — guard k = 1 (r1 is the last run). Steps: as RTUP, but
the probe is in the blank beyond r1 (the role of g2[0] is played
by the first blank cell). **Cost 2·r1 + 6. Effect: β += 2; g1 :=
r1 − 1; the probe writes are a new last run 2; span += 2;
→ C-form. Events: as RTUP.**

Each step list is a forced read of the table from the stated
guard: every sweep cell is read in the state/symbol the list
claims (sweeps cross 1-runs in A/B/F exactly as in Phase 13 §2),
every turn is on the stated symbol, and the move sequence of each
excursion is a single right-then-left peak, so the excursion's end
is its only head local minimum. The derivations need β ≥ 2 for
C-form rules (the head must sit on β's second-to-last cell) and
β ≥ 1 for B-form rules; the F-on-0 triple cases at β ∈ {1,2,3}
are listed above and are all ≠ (0,1,0).

*Verification.* The five rules, applied at β's right end, predict
the successor section (state, head, full run list) and the cost of
**every** transition in two independent windows, with **0
mismatches**: (i) 250,028 transitions over 3×10⁶ steps from σ_re
in the small geometry (B2 = 31, β ∈ [7,24]; `phase15_classify.py`
on `p15-r1-sec.log`); (ii) 416,632 transitions over 5×10⁶ steps
from the large-geometry home configuration (B2 = 96, β ∈ [54,76];
`phase15_classify2.py` on `p15-home1-sec.log`, which also confirms
every section is located at working run 0 — the β interface — and
none deeper). (iii) A streamed verification over 10⁸ steps from
the same home configuration (`phase15_classify_stream.py`):
**8,333,320 transitions, 0 mismatches**, all at working run 0,
β ≥ 53 (B-form) / ≥ 55 (C-form) throughout.

---

## 3. Invariant RI and the safety proof

**Invariant RI.** At every right-section:
- (RI1) tape = `1^17 0 1^B2 0^1 · W` with the frozen prefix never
  written (B2 fixed at its entry value + 1); W = 1^β (0^g 1^r)*
  with **every gap odd** and **every non-β run even**; β ≥ 1.
- (RI2) state C ⟹ head at β_end − 1 (hence β ≥ 2); state B ⟹
  head at β_end + 1 and **g1 = 1**.

*Entry.* σ_re satisfies RI: gaps 1 (odd), the single non-β run is
the terminal pair 2 (even), β = s + 2 ≥ 4, C-form. ✓

*Preservation (arithmetic per rule).*
- RTDN: β−2, r1+2 (even stays even), gaps untouched; ends B-form
  with g1 = 1 (the erased cell). ✓ (β' ≥ 1 iff β ≥ 3; β' = 0 at
  β = 2 — see boundary below.)
- RPUSH: β−1; new gaps 1 and g1−2 (odd − 2 = odd); new run 2
  (even); ends C-form. ✓
- RPOP: β+1; merged run r1+r2 (even + even); gaps untouched;
  ends B-form with g1 = 1. ✓
- RTUP: β+2; new g1 = r1−1 (even − 1 = odd); new run 2; g2−2
  (odd); ends C-form. ✓
- RPROBE: β+2; new g1 = r1−1 (odd); new last run 2; span +2;
  ends C-form. ✓

*Totality on RI.* C-form: g1 is odd, so g1 = 1 (RTDN) or g1 ≥ 3
(RPUSH). B-form: g1 = 1 by RI2; then k = 1 (RPROBE), or g2 = 1
(RPOP), or g2 ≥ 3 (RTUP) — g2 is odd by RI1. So every RI section
fires exactly one rule, and by §2 each excursion is a single peak
whose only local minimum is its end: **by induction, as long as
successors stay in RI form, every step after entry belongs to a
rule excursion and every head local minimum is a right-section.**

*Safety.* By M4 and M2 it suffices that no excursion contains an
E-on-0 read or an F-on-0 with triple (0,1,0), and every C-on-0 is
B-entry with context ≠ (1,0). The event lists of §2 give exactly
this: RTDN and RPOP have no events at all; RPUSH, RTUP, RPROBE
have exactly one probe each — C-on-0 B-entry with context (1,1)
(M2-safe), D and E reading the probe's written 1s (never 0), and
one F-on-0 whose triple is (1,1,1), (1,0,1), (1,1,0) or (0,1,1)
according to the rule and β — never (0,1,0) (M4-safe). F-entry
C-on-0 never occurs inside the regime: C-form landings are on a 1
(the restored erased cell in RPUSH, for β ≥ 3; the filled g1 cell
in RTUP/RPROBE). The entry excursion (§1) has the same inventory.
**Hence the right-edge regime contains no halting step: the
machine does not halt at any step covered by a rule excursion
from an RI section.** ∎ (modulo the β boundary, next paragraph)

*The β boundary (exact).* β changes by −2 (RTDN), −1 (RPUSH),
+1 (RPOP), +2 (RTUP, RPROBE). B-form sections with any β ≥ 1 have
RI successors with β' ≥ 2 (RPOP: β+1; RTUP/RPROBE: β+2, landing
C-form). C-form sections with β ≥ 4 have RI successors with
β' ≥ 2. The decreasing chain from a C-form section is at most
RPUSH then RTDN (after RPUSH, g1 = 1), i.e. −3 before a B-rule
must fire. The genuinely exceptional cases are C-form sections
with β ∈ {2, 3}:
- β = 3: RTDN → B-form with β' = 1 (still RI; B-rules restore
  β ≥ 2); RPUSH → C-form with β' = 2 (still RI). In form.
- β = 2: both excursions are still event-clean (RTDN: no events;
  RPUSH: probe (1,1), F-on-0 triple (1,1,0)), but the successor
  leaves RI form: RTDN gives β' = 0 (the gap after the prefix
  becomes 2, even); RPUSH lands the head in state C on the
  prefix separator cell (a 0) — an F-entry C-on-0 with context
  (1,1), which by M1 does not halt, after which the head sweeps
  left through the B2 block in state F, erasing it (verified by
  trace on `p15-b2push.cfg`: T9 C-on-0 F-entry (1,1); T10–T11
  D,E on 1s; from T12, F erases the block leftwards; no E-on-0).
  This is a regime *exit*, not a halt — but its continuation is
  outside the rule system (open, §6).
So the induction is unconditional except for one global
hypothesis: **no C-form section with β = 2 occurs** (β = 3 is
in-form and harmless). Observed β at C-form sections: ≥ 9 over
125,018 C-sections (small geometry, 3×10⁶ steps); ≥ 59 over
208,312 C-sections (large geometry, 5×10⁶ steps); ≥ 55 over
≈4.17×10⁶ C-sections (large geometry, 10⁸ steps, streamed); the home block
(= β at home sections) is ≥ 48 over all 4,194,714 EXC-END records
of the 10⁹-step run (minimum 48 attained once, mode 54); synthetic
probes started at the boundary (β = 2 RTDN form, β = 1 B-form;
`p15-b2tdn.cfg`, `p15-b1.cfg`) leave RI form but remain
event-clean for the full 2×10⁵ steps run (audit single-point:
E-on-0 = 0, danger = 0, one F-entry C-on-0 (1,1) each). A proof
that β ≥ 3 along the actual trajectory would need a global
argument about the β walk (a population effect of the gap word,
like B2's growth in the S′ analysis); it is the one open point
(§6). The margin is wide: β would have to fall by ≥ 45 from its
observed range.

---

## 4. Macro-structure: the token passes (the regime's counter)

Sections (§2) are the micro level. The macro level is seen at
*home returns*: head local minima at the leftmost interface cell
(head 169 in the large geometry = the EXC-END records of Phase
11's `phase11-syng2-long.log`, parsed in full as
`phase15-exc-summary.tsv`, 4,194,714 records over 10⁹ steps).

**Home form (measured, all 10⁹ steps).** At C-form home returns
the tape is the frozen prefix, a block of 56, then 17 gaps and a
terminal pair, with **all gaps = 1 except exactly one *token*
gap of odd value v ≥ 3** at some gap index j ∈ [0, 16] (137
C-form single-token home records form the clean pass skeleton
below; B-form home returns are the 5-step RTDN flicker: block 54,
first run 4). Ones are constant (203), B2 = 96 throughout.

**Passes (measured; move law exact for v = 3, 5).** The token
executes *passes*: it is created at the rightmost gap (j = 16)
by a long excursion, then moves left one gap per macro-excursion
until it reaches j = 0, where it is consumed; a regeneration
then creates the next token with **v := v + 2** at j = 16, the
block restored to 56 and the span grown by exactly 2 (the token's
own growth; the pair count stays 17, ones stay 203). For the
passes v = 3 and v = 5 every macro-excursion cost is verified
from the EXC records: creation (destination j = 16) costs
3·2¹⁹ − 11 (v = 3; v = 5: 3·2¹⁹ + 57), and the move into
destination gap j costs exactly

```
cost(j) = 3·2^(j+3) − 11        (j = 0..15),
```

each move accompanied by the 5-step B-form flicker. One full
transport (creation + 16 moves + flickers) therefore costs
3·2¹⁹ − O(1) ≈ 1.57×10⁶ steps regardless of v. For v ≥ 7 the
descent is no longer a single sweep: the token descends partway,
is re-formed rightward, and descends again, with excursion costs
keeping the same dyadic leading terms (small excesses ≤ ~10²,
e.g. 786,485 / 393,265 / 196,653 in the v = 13 pass). The total
pass duration fits, for all eight fully observed passes,

```
D(v) = (2^((v−1)/2) − 1) · 3·2^19        (error < 0.002 %),
```

v = 3: 1,572,776; v = 5: 4,718,392; v = 7: 11,009,688; v = 9:
23,592,344; v = 11: 48,757,720; v = 13: 99,088,536; v = 15:
199,750,232; v = 17: 401,073,688 (the v = 19 token is created at
step 806,878,469; the run ends at 10⁹ mid-pass). The excess of
D(v) over one transport quantum is the token's repeated-descent
work: the number of quanta per pass is 2^h − 1 with
h = (v−1)/2.

**The counter, and the ~10⁸ period.** The regime's clock is the
token value: h = (v−1)/2 increments by 1 per pass, and each
increment doubles the pass duration. Phase 11's sawtooth cycles
(≈5.1×10⁷, ≈1.01×10⁸, ≈2.02×10⁸ steps) are exactly the v = 11,
13, 15 passes (4.88×10⁷, 9.91×10⁷, 2.00×10⁸); the "small gap
1 → ~17 → 1" is the token value at the tape's right end across a
pass (the right-sig last gap G equals v while the token is the
last gap, and the token's creation value grows 3, 5, …, 17, …).
The dyadic move law cost(j) = 3·2^(j+3) − 11 is the population
law of the five rules: transporting the token across one more
pair requires the RPOP snowplow to rebuild the merged run across
that pair, and the rebuild is itself a transport of the
sub-structure — the same self-similar doubling as the standard
regime's bounce-depth law (Phase 13 §5.1). The regeneration at
j = 0 is itself composed of the five rules: across the v = 3 → 5
boundary window, 141,636 consecutive section transitions classify
under the five rules with 0 mismatches
(`phase15_classify2.py` on `p15-passend-sec.log`), including the
single RPROBE that grows the span.

---

## 5. Exit characterisation

The regime is **absorbing**: the frozen prefix is never written
after entry (freeze check: no write left of cell 168 — the
moving β interface — in any Phase 15 window; over 10⁹ steps
B2 = 96 in all 4,194,714 home records and the head never
returns below the interface). A section satisfying invariant I
has its head at B2 + 16 or B2 + 18 (≤ 114 in this geometry),
which the head never reaches again — **the return-to-I outcome
does not occur from the G = 2 entry.** (Phase 11 §3.2's G = 0 regeneration is a
different configuration: σ_coll at G = 0 is unreachable from
here — Stage A needs G ≥ 3, G = 2 exits into this regime, and
inside the regime the last gap at sections is odd ≥ 1 by RI, so
the G = 0 form never arises. Its own dynamics was audited clean
in Phase 12 §4; it is not part of this trajectory.)

Within the regime, totality (§3) leaves exactly two outcomes:
(i) the pass cycle of §4 repeats forever — v → v + 2 per pass,
pass durations doubling, Σ D(v) = ∞, no halting step by §3; or
(ii) the β = 2 escape of §3, which is non-halting at the exit
step (F-entry C-on-0, context (1,1), M1-safe) but leaves the
rule system. No third outcome exists: every section fires a
rule, every excursion ends at a section, and the only form-exit
is (ii). On the observed trajectory (10⁹ steps, 8 full passes)
only (i) occurs, with β margin ≥ 45 throughout.

---

## 6. Status

**Derived (from the transition table, step lists in §1–§2):**
the entry excursion and its closed form σ_re(B2, s) (cost s+12);
the five mirror rules RTDN/RPUSH/RPOP/RTUP/RPROBE with guards,
costs, successor tapes and event lists, including all F-on-0
triple and probe-context cases at β ∈ {1, 2, 3}; invariant RI,
its preservation and the totality of the rules on RI; the safety
theorem of §3 (no halting step in any rule excursion, via M2/M4);
the β-boundary analysis (β = 3 in-form; β = 2 excursions
event-clean, successors leave RI; the escape step itself is
M1-safe).

**Verified exhaustively (machine):** entry battery 10/10
((B2, s) grid, §1); five-rule classification of every section
transition with 0 mismatches in four windows — 250,028
transitions (small geometry, 3×10⁶ steps), 416,632 (large
geometry home window, 5×10⁶ steps), 141,636 (pass-boundary
window, 1.7×10⁶ steps), 8,333,320 (large geometry, 10⁸ steps,
streamed) — with every section located at the β
interface and every audit single-point (all C-on-0 B-entry
(1,1); all F-on-0 (1,1,1); E-on-0 = D-on-0 = 0); token move law
3·2^(j+3) − 11 for the full passes v = 3 and v = 5; pass
duration fit D(v) = (2^((v−1)/2) − 1)·3·2¹⁹ to < 0.002 % over
eight passes in 10⁹ steps; boundary probes β ∈ {1, 2} event-
clean over 2×10⁵ steps each.

**Open:** (a) a global proof that β ≥ 3 at C-form sections along
the trajectory (the β walk's lower bound — a population
question, as B2's was before the S′ analysis; observed margin
≥ 45 over 10⁹ steps); (b) the continuation after a hypothetical
β = 2 escape (outside both rule systems; the exit step is
proven non-halting); (c) a first-principles derivation of the
pass-level laws (the dyadic move cost and the 2^h − 1 quanta
per pass) from the five rules — the section-level system is
derived, the population laws are measured-exact.

With (a) the only gap, obstruction 3 is closed to the same
standard as obstructions 1–2: **the right-edge regime is
halt-free on the observed trajectory, by a derived rule system
whose every excursion is proven event-clean; the regime cycles
forever through token passes of doubling period and never
returns to invariant I.**
(= β at home C/B sections) is ≥ 48 over all 4,194,714 EXC-END
records of the 10⁹-step run (`phase15-exc-summary.tsv`; minimum
48 attained once, mode 54). Synthetic probes started at the
boundary (β = 2 RTDN form, β = 1 B-form; `p15-b2tdn.cfg`,
`p15-b1.cfg`) leave RI form but remain event-clean for the full
2×10⁵ steps run (audit single-point: E-on-0 = 0, danger = 0, one
F-entry C-on-0 (1,1) each). A proof that β ≥ 3 along the actual
trajectory would need a global argument about the β walk (it is
a population effect of the gap word, like B2's growth in the
S′ analysis); it is the one open point (§6). The margin is wide:
β would have to fall by ≥ 45 from its observed range.
