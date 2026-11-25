# Mechanisation status — BB(6) holdout #168016 in Rocq (Phase 46, 2026-11-25)

Step 2 of the user-approved community sequence (reproduction ✓ Phase 22 →
**mechanisation** → submission prep ✓ Phase 24). This document maps every
component of the dependency table in `168016-proof.md` §1 to its
mechanisation status. **Nothing has been posted or submitted externally.**

Phase 25 (2026-11-25) advanced the mechanisation along the order suggested
at the end of the Phase 23 status: **TUP** (completing the five-rule
standard system, #10, and discharging the G bookkeeping, #11), **REGEN
assembled** (#17 complete), and the **right-edge entry + mirror system**
(#12, #13) in a new file `Mirror.v`.

Phase 26 (2026-11-25) completed the next block in that order: the **token
pass / Cycle Lemma Γ (#14)** and the **general β = 2 exit (#15)**, in a new
file `TokenPass.v` built on Mirror.v.

Phase 27 (2026-11-25) completed the next two blocks: **#16
re-coordinatisation** in a new file `Recoord.v` (stages 1 and 3 proved in
full; stage 2 kernel-verified at instances and carried as the explicit
hypothesis of the proved composition `RECOORD2`), **#18 the era law** in a
new file `Era.v` (the deviation-free assembly: `ENTRY_gen`, the Grind
Lemma G′ in endpoint form, `POP_CHAIN`, and `ERA_LAW` with
s₁ = 2β_E + 31 and β′ = 2β_E + 34), and the **single-block escape pieces**
of #19's re-formation in a new file `Esc.v` (`POP2` fully general, and
the probe prefix E1–E5 as `PROBE_PREFIX`).

Phase 28 (2026-11-25) mechanised **#19's deviation system** in two new
files: `Dev.v` — **every deviation step list proved for all parameters**
(PUSHX with its general-g follow-on, PX2A including the b = 2 special
form, PX2B rows b = 2..6, the CGAP2 probe and both dispatches, the
TUP2 chain k = 1, TRANS2 turns k = 1 and k = 2, and the TUP2 defect
k = 1, r₁ = 1 — the last with a **machine-corrected landing**, finding
F-3 against `phase21-derivations.md` §4, recorded there as a dated
erratum) — and `Grind.v` — the **frame-general step lists** (the five
standard rules and CGAP2 over abstract frozen prefixes), the **hybrid
word model** `hstep` of phase21 §7 with a full **soundness theorem**
(every word step is a machine run, up to `cfg_sim` for REGEN), the
**grind prefix reductions** of the G″ recursion (clean and PUSHX
deviation branches), and the **Predecessor case analysis** (`pred_cases`:
the only four producers of a PUSH-at-a=2 source, with the exact
remaining invariant obligations). Stage 2 of #16 gained further
kernel-verified instances (n = 8, 10 at B2 = 31; B2 = 15, 47 at n = 2)
but its general case remains fenced. The full non-halting theorem is
**not** yet assembled in Rocq; the remaining components are the general
stage 2 of #16, the G″ endpoint induction (with the era stack invariant)
and with it the ESC-era law, and the S/S′ side (#1–#5), each with its
obstruction and route stated below.

Phase 29 (2026-11-25) mechanised the **G″ endpoint induction and the
ESC-era law** in a new file `Grind2.v`, discharging the Phase 28
obligations (a)–(c) in the regime the ESC trajectory at a2 = 3 uses:
**(b)** the grind iteration — `hGRIND` (the word-level Grind Lemma G′,
transplanted from Era.v) composed into rounds (`grind_round`,
`GG_rounds`) over Grind.v's `grind_prefix`, giving the clean-regime
G″ endpoint `GG_clean` for **every** frame pb, a2 and carried stack P
under the floor m + 1 ≤ a2 (R = 2m + 4), plus the deviated round at
a2 = 3 (`ESC_GRIND_10`: rounds 1–2 clean, round 3 = TUP +
`hGRIND_dev`); **(c)** the post-PUSHX continuation — `hGRIND_dev`,
the deviated Grind Lemma G′ at the boundary frame a2 = t (pb = []),
whose recursion mirrors `hGRIND` with the final spine call deviated
and the base case the single PUSHX step, landing shifted by (+1, +1);
the shift is absorbed by the transfer tail, so no finite check is
needed in this regime; **(a)** the era stack invariant `grind_inv`
(the dip budget s + w ≤ 2a + 7 at B-sections, saturated exactly by
the deviated spine) with `PRED_inv` discharging `pred_cases`' two
obligations (a TUP producer at shuttle exactly 4; STGA / PX2A /
TUP2-defect producers excluded) and `PUSHX_only`, the invariant
threaded through all grind chains (`hstepsP` versions of every grind
lemma). The **ESC-era law β_next = 2β + 4 is PROVED** for
R ∈ {2, 4, 6, 8, 10} (`ESC_ERA_LAW`, via `ESC_TO_REGEN` + the
frame-general `REGEN_gen` + `ERA_TAIL` over Era.v's `ENTRY_gen`).
What remains open in #19 is exactly the **R ≥ 12 re-basing segment**
(the nested two-residue recursion inside round 4 of the ESC grind),
fenced with a precise statement below. The full non-halting theorem
is still **not** assembled in Rocq; the other remaining components
are the general stage 2 of #16 and the S/S′ side (#1–#5), as before.

Phase 30 (2026-11-25) mechanised the **general case of stage 2 of
#16** — the diagonal token pass — in a new file `DiagPass.v`,
discharging the one explicit hypothesis of `RECOORD2`. The pass is
proved for **every frozen prefix P** (`DSTAGE2`: from
`rcsec P n ((2n+3, 2)::[])`, run (Tk n) reaches cfg_sim of
`rcsec P 0 ((3, 2):: repeat (1, 2) n)`), decomposed as the documents'
descent + walk: **DESC(k)** (an A-round, a Ψ-orbit — the *descent
orbit*, whose total cost is TokenPass's `bcost k` — and a closing
RPUSH, landing at the first β = 2 section W_k) followed by
**WALK(i)** steps W_i → W_{i−1} of cost Dk (i−1) (RTDN, an RPOP
chain, RTUP, and a nested descent at the grown suffix). The descent
orbit is built by the orbit recursion
𝒟_{k+1} = T₁(𝒟_k) ⧺ join ⧺ T₂(𝒟_k) with
T₁(β; w) = (β + 1; last gap + 2) and
T₂(β; w) = (β; last gap − 2, gap 3 appended), verified numerically
against the Python word models for k ≤ 9 before formalisation. The
T₂ transport is the one place needing a source invariant (`wok`:
the bad word shape — front all ones, last gap 3 — occurs in the
descent orbits only as the final word, never as a step source);
`fchain` is the `borbit` analogue carrying `wok` at every source.
In Recoord.v, **`STAGE2_proved`** instantiates `DSTAGE2` at
`entryP B2` and **`RECOORD2_uncond`** discharges the composition:
**component #16 (two-block landing) is now fully mechanised.**
The seven kernel-verified instances remain as regression checks
(and Tk 2 = 102 agrees). Remaining components: `REBASE` (R ≥ 12),
the cross-era loop assembly, the S/S′ side (#1–#5), and #2/#3.

Phase 31 (2026-11-25) mechanised **`REBASE`** — the R ≥ 12 re-basing
segment of the ESC grind — in a new file `Grind3.v`, and extended the
ESC-era law to **every even R ≤ 40**. Two things came out of the
pre-proof model analysis. First, **finding F-4**: the Phase 29 fence's
source `HC [] 4 11 2 ((R−10, 2) :: P) 1` has an off-by-one in g0 — the
section the grind actually reaches (round 3 deviated, then its TUP) is
`HC [] 4 12 2 ((R−10, 2) :: P) 1`; the g0 = 11 section never occurs in
the grind, and the chain from it does not reach the fenced target
(`phase21_model.py` traces at R = 14, 18). The fence's target was
correct as stated. Second, the corrected segment needs **no
two-residue induction**: `hGRIND` and `hGRIND_dev` quantify over the
whole carried stack, so the second residue pair is a pure passenger —
`REBASE_core` (PUSH + TDN + TUP, then `hGRIND` 0/1/2 interleaved with
TUP, then `hGRIND_dev` 3) lands `HB [] 4 1 13 ((2, 2) :: (u, 2) :: P)`
for **every** u, and one closing `hTUP2_1` gives `REBASE` for u ≥ 3.
The segment's only PUSHX is `hGRIND_dev`'s base step, as the fence
measured. With `ESC_GRIND_BIG` (the R ≥ 12 grind up to the REBASE
source — the `ESC_GRIND_10` pattern at general R), the re-based grind
is `GG_clean` at (pb = [5], a2 = 13) for R ≤ 40; R = 14 closes by
TDN + `TAIL`, R = 12 by `REBASE_core` + `hTRANS2_2` + the POP chain;
the era-law assembly is factored as `ESC_ERA_LAW_of`.
**`ESC_ERA_LAW_31`: β_next = 2β + 4 for every even R ≤ 40.** What
remains open in #19 is the **second re-basing (R ≥ 42)**, fenced
precisely below. Remaining components: the cross-era loop assembly,
the S/S′ side (#1–#5), and #2/#3.

Phase 32 (2026-11-25) assembled the **cross-era loop** in a new
file `Loop.v`: the exit + stages 1–2 composed for an arbitrary
frozen prefix (`PASS`), the settled iteration at the trajectory
prefix (`SETTLED_ITER`: RECOORD2_uncond + ERA_LAW, β = n + 2 ↦
2n + 38, landing on a single-block entry prefix), the settled
iteration at a general two-block prefix conditional on the
explicit hypothesis `ERA_GEN` (the general-residue era law,
mechanised only at ρ = 29), the ESC iteration (`ESC_ITER`: PASS +
the definitional bridge `esc_bridge` to Esc.v's `esc_src` +
ESC_ERA_LAW_31, β ↦ 2β + 4), the first two iterations composed
in full (`TWO_ITERS`, β = n + 2 ↦ 4n + 80 for n = 2j + 3,
j ≤ 12), the abstract ascending-loop engine (`loop_chain`,
`LOOP_NONHALT`: loop_step at every entry section with β ≥ 4
implies the run from any entry section is total), and the
headline **`NONHALT_FROM_R`**: from the record configuration R,
with the formation segment kernel-verified (Finite.v), the run
is total modulo two explicit hypotheses — **H_STD** (component
#10's assembly: the standard regime from the first I-section
reaches an entry landing entry_tgt (B2 − 1) n, B2 ≥ 3, n ≥ 2)
and **H_LOOP** (loop_step at every entry section with β ≥ 4),
of which the settled instances (B2 = 31 fully; general B2
modulo ERA_GEN) and the ESC instances at R ≤ 40 are discharged
in the same file. The undischarged instances of H_LOOP are
exactly the ESC entries at R ≥ 42 (the second re-basing) and
the entry sections whose prefix is an ESC-era landing form
(iterations ≥ 3). Remaining components: H_STD (#10's assembly
and the exit dichotomy), ERA_GEN, the second re-basing, the
S/S′ side (#1–#5), and #2/#3 — each fenced below.

Phase 33 (2026-11-25) mechanised the **second re-basing** in a
new file `Grind4.v`, extending the ESC-era law to **every even
R ≤ 114** and discharging H_LOOP's ESC instances for
42 ≤ R ≤ 114 (`ESC_ITER_114` in Loop.v). Route (a) was taken
at pb = [5]: the deviated grind **`hGRIND_dev5`** mirrors
`hGRIND_dev` with base case `hPX2B5` (its landing is two-case:
t = 0 carries extras [(1,1),(1,2),(1,2)], t ≥ 1 carries
[(1,2),(1,2),(1,2)] — each level's closing POP consumes the
head pair). Route (b) was reinterpreted, not refuted: the
Phase 29 model evidence ("PUSHX = 0, min PUSH a = 3") is
literally true because the deviation at pb = [5] is PX2B5,
not PUSHX — the re-based grind DOES deviate exactly once.
After the deviated round, three POPs absorb the extras; for
R₂ ≥ 32 the grind continues with a new **even-g0 grind**
`hGRIND_even` (g0 = 2t + 4) and a **third phase** of clean
rounds at a2 = 34 (`rounds_from4`, exact floor j0 + m ≤ a2),
closing at R₃ ≤ 70. All section forms were pre-verified in an
hstep-level simulator mirroring Grind.v's 20 constructors
(validated against the proved `hGRIND_dev` / `REBASE_core` /
`GG_clean` chains). **The new fence is precise**: at
R₃ = 72 (R₂ = 104, **R = 116**) the phase-3 boundary grind at
pb = [20; 0] dips to `HC [20; 0] 0 3 2 ((1, 2)^34 :: …)`,
where **no `hstep` constructor applies** (`hPX2A` needs the
second block ≥ 1; the phase21 model agrees — its PX2A guard
fails with p = 0). Closing R ≥ 116 needs a new machine-level
deviation step list at pb = [20; 0]. Remaining components:
H_STD (#10's assembly and the exit dichotomy), ERA_GEN, the
R ≥ 116 third re-basing, the iterations ≥ 3 re-formation,
the S/S′ side (#1–#5), and #2/#3 — each fenced below.

Phase 34 (2026-11-25) discharged **H_STD** — the standard-regime
assembly, component #10's totality plus the #11 exit dichotomy —
in a new file `Std.v`. The key identifications are definitional:
`cfg_Isec` (Finite.v's formation endpoint: state C, B2 = 97,
s = 2, w = [1], G = 134) **is** the word-model section
`HC [17] 95 1 2 [] 134` (the frozen prefix `[17]` encodes the
separator 0 and the wall 1^17), and `entry_src B2 s` is
definitionally `HB [17] B2 1 s [] 2` — the unique uncovered
guard of the composed five-rule system (reexpansion-derivation
§3: a B-section with w = [1] at G = 2) is exactly the ENTRY
source. The regime from `cfg_Isec` is therefore a single
`hsteps` chain at pb = [17] (`STD_chain`): `hTDN`, one `hSTGA`
collapse, then 65 **grind/collapse cycles** (`STD_cycle`:
`hGRIND t` at floor t + 1 ≤ 95 followed by `hSTGA`; G falls
134 → 2 over 66 Stage A firings in all), then the final
`hGRIND 65`, landing on `HB [17] 95 1 136 [] 2` =
`entry_src 95 136`; Mirror.v's `ENTRY` closes to
`entry_tgt 95 136`. **`H_STD_proved`**: H_STD holds with
(B2, n) = (96, 136), and **`NONHALT_FROM_R_std`** restates
the headline assembly with H_STD discharged — non-halting
from `cfg_R` now rests on the single hypothesis H_LOOP.
The general pattern is `STD_reach_entry` (any empty-stack
I-C-section with even G = 2k + 6 ≥ 6 at a frame A ≥ k + 2
reaches the w = [1] B-section at G = 2). The chain was
pre-verified on the real machine (`rocq/std_verify.py`):
from `cfg_Isec` the first 15 macro boundaries are hit in
order (TDN delta exactly 6, every Stage A delta exactly
2s + 6, GRIND deltas 26/70/162/350/730/1494), and the same
assembly at G0 ∈ {6, 8, 10} runs end-to-end through ENTRY
to `entry_tgt 95 (G0 + 2)`. Scope note: H_STD is discharged
by exhibiting the trajectory's concrete chain; the general
I⁺-preservation induction over *arbitrary* standard-rule
sequences is not separately formalised and is no longer
load-bearing. Remaining components: ERA_GEN, the third
re-basing (R ≥ 116), the iterations ≥ 3 re-formation, the
S/S′ side (#1–#5), and #2/#3 — each fenced below.

Phase 35 (2026-11-25) proved **ERA_GEN** — the
general-residue era law — on its exact domain, in a new
file `EraGen.v`, and discharged the general settled
iteration on that domain in Loop.v. `ERA_GEN_proved` is
Loop.v's `ERA_GEN` statement proved for **every odd ρ
with 1 ≤ ρ ≤ 33** (and every era parameter m ≥ 1): the
assembly is ERA_LAW's with ρ = 2t + 1 substituted —
absorption by `GRIND` at t − 1 (for ρ = 1, t = 0, the
absorption is a single `TDN`), `POP_CHAIN` with
s₁ = ρ + 2m + 2, `REGEN`, the Stage-A era with invariant
s + G = ρ + 2m + 5 over J = t + m cycles, and `ENTRY_gen`
landing at rcsec argument ρ + 2m + 3 (β′ = ρ + 2m + 5).
Both domain bounds are exact and both fences were
pre-verified on the real machine
(`rocq/era_gen_verify.py`): the full predicted boundary
sequence is hit in order, with REGEN / TDN / Stage A /
ENTRY deltas equal to the proved costs, at (ρ, m) =
(29, 2) (the ERA_LAW control), (27, 1), (27, 2), (31, 1),
(31, 2), (33, 1) (floors at equality) and (1, 2)
(absorption = TDN, delta 6); while at (35, 1) and
(30, 1) the absorption landing is **never** reached in
20,000,000 steps. ρ ≥ 35 (odd) exceeds the residue
grind's floor at the fixed frame a2 = 16 (dip
(ρ − 1)/2 > 16); ρ even is obstructed twice over —
Lemma G′ is odd-only (the absorption itself diverges)
and the era's G parity is load-bearing (G₀ = s₁ − 1 must
be even for the Stage-A era to land on the G = 2 entry
source). In Loop.v, **`SETTLED_ITER_GEN_odd`** now
discharges the general settled iteration unconditionally
for odd B2 with 3 ≤ B2 ≤ 35 (ρ = B2 − 2); the conditional
`SETTLED_ITER_GEN` remains for even B2 and B2 ≥ 37, which
are thereby H_LOOP's remaining settled instances (they
arise only inside the iterations ≥ 3 re-formation).
Remaining components: the third re-basing (R ≥ 116), the
iterations ≥ 3 re-formation, the S/S′ side (#1–#5), and
#2/#3 — each fenced below.

Phase 36 (2026-11-25) attacked the **third re-basing
(R ≥ 116)** and closed its dip bottom. The Phase 33 fence
was the single section with no `hstep` constructor:
`HC [20; 0] 0 3 2 ((1, 2)^34 :: (2, 2) :: Pe) 1`, the
bottom of the phase-3 boundary grind (grind 34 at
a2 = 34, R = 116). By direct zipper tracing (the
Phase-28 method; `rocq/hsim36.py`), the dispatch there
is a new deviation step list **`PX2A0`**: for every
b ≥ 5, `HC [b; 0] 0 3 2 P G` runs in b + 32 steps to
`HB [0] 3 1 2 ((b − 4, 2) :: (1, 1) :: (1, 2) ::
(1, 2) :: P) G` — `PX2A_chunkA` at p = 0 and its F-sweep
verbatim, then a fixed 23-step tail (the sweep overshoots
into the blank past the empty block). It is proved in
Dev.v for all b ≥ 5 (b = S (S (S (S (S b′′)))), all
stacks P and all G), added to the word model as
constructor **`hPX2A0`** with its `hstep_sound` case,
and instantiated at the fence shape itself
(`PX2A0_dip34`, Grind5.v). The unwind of that grind then
runs the (16, 2) grind at (pb = [0], a2 = 3), whose own
boundary round (grind 3 at frame 3) dips to
`HC [0] 0 3 2` — a second new step list **`PX2B0`**
(20 steps to `HB [] 0 1 5 ((1, 2) :: P) G`, proved in
Dev.v, constructor **`hPX2B0`**) — and the boundary
grind at pb = [0] is now a proved induction
**`hGRIND_dev0`** (Grind5.v): the `hGRIND_dev` recursion
with base case `hPX2B0` + `hPOP`, landing
`HB [] (t + 1) 1 (2t + 7) P G`. What did **not** close:
the deviated grind at pb = [20; 0] has no uniform
landing of `hGRIND_dev` type — its base case consumes
the prefix and leaves the residue pair (16, 2) — so the
R = 116 endpoint (and with it any new `ESC_ERA_LAW` /
`ESC_ITER` instance) still requires assembling the
merged unwind; that is the Phase 37 fence, stated
precisely in “Remaining components”. No H_LOOP instance
is newly discharged in Loop.v. All forms were
pre-verified against the machine: PX2A0 at
b ∈ {5, 6, 7, 8, 10, 12, 16, 20, 24, 30} plus stack/G
variations (first landing at cost b + 32, no
intermediate section), PX2B0 at five stack/G points,
word/machine boundary agreement for the deviated
grinds at t = 1, 2 (154 / 178 word steps, 1877 / 2161
machine steps, every boundary recognised), and
`hGRIND_dev0` rule counts 2, 6, 14, 30, 62 = 2^(t+2) − 2
at t = 0..4 (exactly one PX2B0, no PUSHX).

Phase 37 (2026-11-25) assembled the **merged unwind**
and closed the ESC-era law through **R ≤ 268** (new
file `rocq/Grind6.v`, 867 lines). The R = 116 endpoint
is an explicit chain, not a uniform grind lemma: the
phase-3 prefix is BIG2's (ESC_GRIND_BIG, REBASE,
grind_prefix, 12 clean rounds, round13_dev5, pop3_12,
TUP, hGRIND_even 15, TUP2_1, TDN), then 34 phase-3
rounds at ([20; 0], 34) via the new general-residue
helper **`rounds_from4g`**, the final round's TUP, the
descent of the [20; 0] grind (**`DEV20_DESCEND`**: the
PUSH/TDN/TUP/loop part of hGRIND_dev's recursion at
pb = [20; 0], by induction on the spine), `hPX2A0` at
the dip, and the merged (16, 2) grind at ([0], 3)
(**`GRIND16_MID`**, over an arbitrary carried rest:
segments A–E — TUP + grind_prefix + clean rounds 1–2,
TUP + `hGRIND_dev0` 3, a second G″ grind, TUP +
`hGRIND_dev` 3, TUP2_1 + TDN — then TRANS2_1 over the
spine head and a POP chain via the new
**`pop_chain_h_app`**), landing
`HB [14; 5] 41 1 75 ((2m − 68, 2) :: Pe)` for
R = 2m + 46, m ≥ 35 (**`PHASE3_DEEP`**). The finishes:
m = 35 is TAIL itself (**`ESC_TO_REGEN_116`**, landing
pb = [42; 14; 5], a = β + 75); m = 36 runs TUP +
hGRIND_even 35 + TRANS2_2 + pop_chain_h
(**`ESC_TO_REGEN_118`**, phase 4); m = 37 runs TUP +
hGRIND_even 35 + TUP2_1 + TDN + TAIL
(**`ESC_TO_REGEN_120`**); 38 ≤ m ≤ 111 continues with
rounds at ([41; 14; 5], 74), TUP, a final clean
hGRIND (m − 38) and TAIL (**`ESC_TO_REGEN_BIG3`**,
phase 5). Hence **`ESC_ERA_LAW_37`** (R ∈ {116, 118,
120} ∪ {2m + 46 : 38 ≤ m ≤ 111}) and the combined
**`ESC_ERA_LAW_268`**: β_next = 2β + 4 for **every
even R ≤ 268**. In Loop.v, **`ESC_ITER_268`** /
**`ESC_ITER_268_step`** discharge H_LOOP's ESC
instances for 116 ≤ R ≤ 268. The new fence is at
**m ≥ 112 (R ≥ 270)**: phase 5's final grind
(t = m − 38 at frame 74, pb = [41; 14; 5]) reaches its
floor (m − 37 ≤ 74 fails), i.e. the grind becomes a
boundary (deviated) grind at a three-block prefix — a
phase-6 deviation whose dip bottom has not been
derived. All forms pre-verified in `rocq/hsim37.py`:
GRIND16_TAIL word boundaries at (spine, β) ∈ {(0, 2),
(2, 2), (3, 3), (5, 2)}, word/machine boundary
agreement at (2, 2) (131 rules, 1,598 machine steps),
DEV20_DESCEND boundaries at t = 1, 2, 3, a
rounds_from4g analogue, and frame-10 analogues of the
phase-4 and phase-5 finishes. Clean rebuild: all
twenty files compile; every Print Assumptions audit
“Closed under the global context”.

Phase 38 (2026-11-25) discharged the phase-6 fence
(new file **Grind7.v**, 992 lines). At m ≥ 112,
phase 5's finish breaks twice over: the rounds at
([41; 14; 5], 74) admit at most 74 rounds, and the
final grind (t = m − 38 at frame 74) is over-floor.
Taking the maximal 74 clean rounds leaves the final
grind at exactly t = 74 = a2 over the passenger
residue ((2m − 222, 2) :: Pe). The dip bottom of
that boundary grind is **not a new dispatch case**:
two new general lemmas carry the descent.
**`LOOPN`** is the truncated loop (cnt iterations of
hGRIND i + hTUP, the partial form of hGRIND's
internal countdown), and **`DIPDESC`** is the
boundary descent itself: for every t and every
prefix pb, the grind at t = a2 descends to the dip
HC pb 0 3 2 with the stack grown by (1, 2)^t —
no floor hypothesis, the recursion's own fixed
point (each level's loop is frame-truncated by
exactly the amount that grinds its pushed pair to
(1, 2)). The dip at [41; 14; 5] then fires the
existing **`hPX2A`** (Dev.v, cost 52), landing at
HC [5] 13 39 2 with the stack grown by the
dispatch's three pairs. The continuation is the
([5], 13) grind at g0 = 39 over an arbitrary
carried rest (**`GRIND39_MID`**): PUSH/TDN/TUP +
LOOPN 12 + DIPDESC 12 to its own dip, hPX2B5, a
15-POP run, hTUP, hGRIND_even 14, hTUP2_1,
grind_prefix, two clean rounds and a POP chain
over the spine, landing at
HB [19; 0] (36 + n) 1 (17 + 2n) Rest for spine
length n (here n = 74: HB [19; 0] 110 1 165).
Finishes (**`PHASE6_PREFIX`**, **`PHASE6_TO_MID`**):
m = 112 (R = 270) is TAIL at that landing
(**`ESC_TO_REGEN_112`**); m = 113 (R = 272) runs
one transitional round (TUP + hGRIND_even 80) and
closes with the TRANS2_2 tail (**`TAIL2`**,
**`ESC_TO_REGEN_113`**); m = 114 (R = 274) runs the
transitional round and TAIL
(**`ESC_TO_REGEN_114`**); 115 ≤ m ≤ 278 continues
with rounds at the new frame ([110; 19; 0], 164),
a final clean grind and TAIL
(**`ESC_TO_REGEN_BIG6`**). Hence
**`ESC_ERA_LAW_38`** (R ∈ {270, 272, 274} ∪
{2m + 46 : 115 ≤ m ≤ 278}) and the combined
**`ESC_ERA_LAW_602`**: β_next = 2β + 4 for **every
even R ≤ 602**. In Loop.v, **`ESC_ITER_602`** /
**`ESC_ITER_602_step`** discharge H_LOOP's ESC
instances for 270 ≤ R ≤ 602. The new fence is at
**m ≥ 279 (R ≥ 604)**: at the new frame
([110; 19; 0], 164) the rounds (count m − 115 ≤ 164)
and the final grind (t = m − 115, floor t + 1 ≤ 164)
both bind; the final grind at t = a2 would again be
a DIPDESC descent whose dip at [110; 19; 0] fires
hPX2A into a phase-7 continuation.
**General-induction verdict (assessed this phase):**
the phase recursion does not close by induction on
phase depth in the current lemma vocabulary.
DIPDESC, LOOPN and hGRIND_even are general, but
each phase's continuation is determined by (i)
which dip dispatch fires — a finite case split on
the literal first two prefix blocks (hPX2A here;
hPX2A0 / hPX2B0..6 / hPUSHX elsewhere, with
mutually different landing shapes) — and (ii) the
landing frame and grind parameters, which are
arithmetic accidents of the specific prefix values
(here blocks 41 and 14 give frame 13 and g0 = 39,
whose continuation decomposes as LOOPN 12 +
DIPDESC 12 + hGRIND_even 14). A general closure
would be a totality/landing theorem for the
deviation-inclusive grind relation over arbitrary
prefixes — a strictly larger theorem than any
single phase. Each phase is therefore a finite
extension; this one reaches R ≤ 602. All forms
pre-verified in `rocq/hsim38.py`: DIPDESC and
LOOPN word boundaries at small parameters,
GRIND39 word boundaries at (spine, β) ∈ {(0, 2),
(2, 2), (3, 3)} (98,338 rules) with word/machine
boundary agreement at (0, 2) (1,180,078 machine
steps), shrunk analogues of the m = 113 / m = 114 /
transitional / BIG6 finishes, and the hPX2A
dispatch at the phase-6 dip shape. Clean rebuild:
all twenty-one files compile; every Print
Assumptions audit “Closed under the global
context”.

Phase 39 (2026-11-25) switched fronts to the
**settled side of H_LOOP**: the settled entries at
even B2 and at B2 ≥ 37, the complement of
ERA_GEN's proved domain (Phase 35: odd ρ = B2 − 2,
1 ≤ ρ ≤ 33). New file **EraEven.v**: the **even
era law** is PROVED for every even residue
ρ = 2k + 2 ≤ 34 (k ≤ 16 at the era frame) and
every m ≥ 1 (`ERA_GEN_even`), and Loop.v's
**`SETTLED_ITER_GEN_even`** / `_step` discharge
the settled iteration unconditionally for **even
B2 with 4 ≤ B2 ≤ 36**: β = n + 2 ↦ **β′ = 2n + 8
= 2β + 4** — independent of B2, the same closed
form as the ESC era law. With Phase 35's odd
case, **the settled iteration is now unconditional
for every B2 with 3 ≤ B2 ≤ 36**; only B2 ≥ 37
remains on the conditional `SETTLED_ITER_GEN`.

Why the odd proof stops where it does, and what
generalises: the era frame a2 = 16 is fixed by
`RECOORD2_uncond`'s stage-3 landing for every
two-block prefix, and ERA_GEN's shape is
parity-bound twice over — the absorption is
Lemma G′ (odd gaps only), and the Stage-A era
needs G₀ even, which the odd script gets from
s₁ = ρ + 2m + 2 odd. At an even residue neither
ingredient survives, but the machine supplies a
different mechanism (derived from the machine,
pre-verified in `rocq/era_even_verify.py` — full
boundary sequences with exact cost deltas at
(ρ, m) = (2, 1), (2, 4), (4, 4), (6, 3), (10, 2),
(28, 5), (30, 4), (34, 4), the last a
1,573,191-step era): the absorption's descent
mirrors G′ until the residue pair reaches **gap
2**, where neither POP (gap 1) nor TUP (gap ≥ 3)
applies; what fires is the TUP-prefix excursion
itself (`Esc.gtup_prefix`), a **frame rotation**:
the shuttle becomes the new near block, the old
block rotates behind a 0, and the pair is
consumed. The absorption (`EVEN_GRIND`, floor
k ≤ a2 — at k = a2 the deepest PUSH lands on an
a2 = 0 C-section, which POP, not PUSH, consumes)
lands on `gbsec (0::1^16) ρ 1 2 pairs 1`: near
block exactly ρ, s still 2. Hence s₁ = 2m + 1
(the ρ went into the frame, not the shuttle),
G₀ = 2m is even unconditionally, and
β′ = 2m + 4 drops ρ entirely. The rest of the
era is frame-general already: `gPOP_CHAIN`,
`REGEN_gen`, `gTDN`, `gSTGA` and the new `gGRIND`
(the odd grind over a general frame, the mirror
of Era.GRIND) assemble exactly as in the odd
case. New lemmas in EraEven.v: `gPOP_CHAIN`,
`gGRIND`, `gROT2` (the rotation as a
section-to-section rule), `ABS2` (the ρ = 2
absorption, a 3-step excursion), `EVEN_GRIND`,
`ERA_GEN_even`.

**B2 ≥ 37 (ρ ≥ 35) is fenced, with machine
evidence** (`rocq/era_fence35_verify.py`, direct
simulation at m = 1): ρ = 35 absorbs at step
3,145,681 on `bsec 17 1 39` — the frame GREW by
one via a sub-frame edge excursion at the dip
bottom, s = ρ + 4, and the era that would follow
has G₀ odd, so the Stage-A era cannot land on
the G = 2 entry source; ρ = 37, 39, 41 absorb by
rotation on the two-block frame (38|17) with
s = ρ − 33; ρ = 36 (even) rotates to (37|17)
with s = 2; ρ = 38 and ρ = 40 show **no**
absorption landing of either form within
60,000,000 steps (ρ = 36 needed 3,145,643).
Beyond the frame the behaviour is not one
uniform family; mechanising any of it needs a
sub-frame edge-grind theory (step lists for
C-sections at a2 = 0 and their landings) that
the current lemma vocabulary does not contain.
Phase 35's negative control stands as stated
(the in-domain landing `bsec 16 1 (ρ+3)` is never
reached at ρ ≥ 35); EraGen.v's header carries a
dated Phase 39 addendum. H_LOOP's remaining
settled instances are exactly B2 ≥ 37. Clean
rebuild: all twenty-two files compile; every
Print Assumptions audit “Closed under the global
context”.

Phase 40 (2026-11-25) returned to the **ESC side of
H_LOOP**: the phase-7 entries at even R ≥ 604, the
fence left by Phase 38. New file **Grind8.v**
(1,046 lines): the **phase-7 merged unwind** is
PROVED — the ESC era law β_next = 2β + 4 now holds
for **every even R ≤ 1276** (`ESC_ERA_LAW_1276`),
and Loop.v's **`ESC_ITER_1276`** / `_step` discharge
H_LOOP's ESC instances for 604 ≤ R ≤ 1276. No new
deviation step list was needed: at the phase-7
boundary the maximal 164 clean rounds at frame
([110; 19; 0], 164) leave the final grind at
exactly t = 164 = a2 over the passenger
((2m − 556, 2) :: Pe); the descent is `DIPDESC` 164
(Phase 38's pb-general boundary lemma) and the dip
fires the existing **`hPX2A`**, landing at
HC [0] 18 108 2 over the (1, 2)^164 spine. The
continuation grind at ([0], 18), g0 = 108
(`GRIND108_MID`) is again a merged unwind whose
every dispatch already exists: stage A's LOOPN 17
is floor-exact and its dip fires hPX2B0; stage B is
the boundary even grind at pb = [] (g0 = 40 =
2·18 + 4, one past the hGRIND_even floor) resolved
as PUSH/TDN/TUP + LOOPN 17 (floor-exact, (36, 2)
ground to (2, 2)) + PUSH/TDN/TUP + LOOPN 16
(floor-exact, (33, 2) to (1, 2)) + DIPDESC 16 to
the pb = [] dip, hPUSHX, and hTUP2_1 onto frame
([19], 41); stage C closes with LOOPN 31 +
PUSH/TDN/TUP + LOOPN 30 + the clean hGRIND 30 +
POP + hTRANS2_1 + the spine POP chain, landing at
HB [42; 19] (71 + n) 1 (7 + 2n) over an arbitrary
carried rest. The finishes mirror Phase 38's:
m = 279 (R = 604) is TAIL; m = 280 (R = 606) runs
TUP + hGRIND_even 165 + the TRANS2_2 tail (TAIL2);
m = 281 (R = 608) runs the transitional round onto
frame ([235; 42; 19], 334) and TAIL; 282 ≤ m ≤ 615
continues with rounds at the new frame, a final
clean grind and TAIL (`ESC_TO_REGEN_BIG7`). All
forms were pre-verified in `rocq/hsim40.py`: the
hPX2A dispatch at the dip shape, DIPDESC at
[110; 19; 0], stages A and B as primitive word
walks at the real parameters (1,048,574 and
1,048,575 word rules; ≈1.26 × 10⁷ machine steps
each), stage C at the real frame with a shrunk
passenger, the whole parse at two shrunk analogues
with word/machine boundary agreement, and shrunk
analogues of all four finishes — ALL CHECKS PASS.
The new fence is at **m ≥ 616 (R ≥ 1278)**: at
frame ([235; 42; 19], 334) the rounds (count
m − 282 ≤ 334) and the final grind (t = m − 282,
floor t + 1 ≤ 334) both bind; the final grind at
t = a2 would again be a DIPDESC descent whose dip
at [235; 42; 19] fires hPX2A into a phase-8
continuation — the same finite-extension shape
(Phase 38's strategic verdict stands: no general
induction over phase depth exists in the current
lemma vocabulary). H_LOOP's remaining ESC
instances are exactly R ≥ 1278. Clean rebuild: all
twenty-three files compile; every Print
Assumptions audit “Closed under the global
context”.

Phase 41 (2026-11-25) attacked the **phase-8 ESC
entries** (even R ≥ 1278). New file **Grind9.v**
(502 lines), plus a new deviation step list in
Dev.v and a new word-model constructor in Grind.v.
The phase-8 shape differs from phases 6/7 in kind,
not just in length. **What is PROVED**: the
phase-8 entry is uniform in m — at frame
([235; 42; 19], 334) the rounds and the final
grind both bind for every m ≥ 616, so there are
no TAIL/TAIL2/transitional finishes; every entry
takes the maximal 334 rounds and the final grind
sits at exactly t = 334 = a2. `PHASE8_TO_MID`
(PHASE7_TRANS42 + rounds_from4g 334 + TUP +
DIPDESC 334 + the dip `hPX2A` at [235; 42; 19])
lands on the continuation source at frame
([19], 41), g0 = 233. The continuation's first
three stages are merged unwinds over arbitrary
carried rests: **stage A** (`PHASE8_STAGE_A`:
PUSH/TDN/TUP + LOOPN 40, floor-exact, + DIPDESC 40
to the dip at the single block [19]); **stage B**
(`PHASE8_STAGE_B`: TUP/TDN/TUP + LOOPN 3 +
DIPDESC 3 + the dip `hPX2B0`); **stage C**
(`PHASE8_STAGE_C`: POP×4 + TUP + the even boundary
descent + hPUSHX + POP×3 + hTUP2_1 onto frame
([5], 13)); composed as `PHASE8_TO_STAGE_D`. Two
genuinely general additions were needed, unlike
Phases 38/40: **(i) a new deviation step list**
— the stage-A dip at the single-block prefix
[19] fires no existing hPX2B row (rows covered
b ≤ 6 as whole chunks); zipper tracing shows the
dip is a uniform family for b ≥ 5 with the same
landing shape and cost b + 32 as PX2A0 at [b; 0],
mechanised as `PX2Bgen` in Dev.v (12-step chunk +
sweepF + 23-step tail, b = b′′ + 5, cost b′′ + 37)
and the constructor `hPX2Bgen` in Grind.v;
**(ii) a new boundary lemma** `DIPDESC_even` —
the g0 = 2t + 4 analogue of DIPDESC (PUSH/TDN/TUP
+ LOOPN t grinding the pushed pair to (2, 2),
closing by DIPDESC over that pair; no floor, no
induction). **What is FENCED, with machine
evidence**: beyond stage C's landing
HC [5] 13 1 2, the continuation grind is **not
stack-local** — it consumes the *entire*
remaining passenger stack (the (1, 2)^40 spine,
the residue pair (149, 2), the (1, 2)^334 spine,
the pair (2m − 1230, 2) and all of Pe), cascading
through frames [24; 5], [25; 24; 5] and then
four- and five-block frames whose values are
iterated arithmetic in the stack contents (at the
hsim41 deep-passenger analogue: [26; 25; 24; 5],
then [13; 26; 25; 24; 5]; at a shallower
passenger: [23; 25; 24; 5], then
[7; 23; 25; 24; 5]), and the word walk ends
**stuck** at a B-section over the *empty* stack
(HB [13; 26; 25; 24; 5] 30 1 13 [] 1 at the
analogue), where no hstep rule applies; the raw
machine's next recognised sections there are not
an era REGEN landing. So no continuation lemma
over an arbitrary carried rest exists for
phase 8: closing ESC here needs the
totality/landing theorem for the
deviation-inclusive grind over arbitrary prefixes
(Phase 38's verdict), now with the obstruction
located exactly — the cascade is the grind's
descent through the whole pushdown stack, and a
finite merged unwind cannot follow it because
the frame itself grows without a closed form.
The ESC era law therefore stays at **R ≤ 1276**;
Loop.v is unchanged and H_LOOP's ESC instances
at R ≥ 1278 remain open, now fenced at the
stage-D source HC [5] 13 1 2 over the carried
stack (1, 2) :: (1, 1) :: R2 of PHASE8_TO_STAGE_D.
All forms pre-verified in `rocq/hsim41.py` (ALL
PHASE 41 CHECKS PASS): the PX2Bgen machine form
at 18 cases (first landing at cost b + 32, no
intermediate section), the stage A/B/C word
boundaries at two shrunk analogues, DIPDESC_even
at t ∈ {1, 2, 3, 5}, and the cascade fence
evidence above. No new findings (no F-5). Clean
rebuild: all twenty-four files compile; every
Print Assumptions audit “Closed under the global
context”.

**Phase 42 (2026-11-25): the totality/landing theorem attacked —
and Phase 41's fence corrected.** The Phase 41 conclusion was
that the phase-8 continuation past stage C is a full-stack
cascade with no landing lemma: the word walk "ends stuck at a
B-section over the empty stack" whose "next recognised sections
are not an era REGEN landing". **That reading is wrong, and
Phase 42 corrects it.** The cascade's terminal configuration
*is* the era-landing shape `HB pb a 1 (2β + 1) [] 1` — the
target of every `ESC_TO_REGEN_*` lemma since Phase 29 and the
source of `Grind2.ERA_TAIL`, which converts it to the entry
landing at machine level via `REGEN_gen`, for **arbitrary**
prefix pb (`REGEN_gen`: `run (4s + 22) (gbsec P a 1 s [] 1)
= Some (gcsecR P a (s − 1) [false])`, 2 ≤ s). Phase 41's own
machine trace from the terminal config (hsim41 Part 5) shows
exactly that landing — `HC pb 30 1 2 [] 12` at cost
74 = 4·13 + 22 — followed by TDN (80) and the era-tail
C-section (94): the modelled era REGEN landing, verbatim. The
word model has no `hstep` at the terminal only because
`hREGEN` is stated at pb = [] and `hSTGA` needs G ≥ 3; the era
assembly never needed a word step there (hsim36's dev20 check
already treated the pb-general REGEN shape as a grind landing).
What Phase 41 *did* prove stands: no continuation lemma over
an **arbitrary carried rest** exists — the cascade reads the
whole stack. But over the **era-shaped stack family** the
landing is a precise, testable statement:

> **CASCADE_LANDING**: for every M ≥ 616 and β ≥ 2, the
> stage-D source of `PHASE8_TO_STAGE_D` (Grind9.v) reaches
> `HB pb a 1 (2β + 1) [] 1` for some pb, a with β ≤ a.

**Machine evidence (new file `rocq/hsim42.py`, ALL CHECKS
PASS).** The cascade from the stage-D source was walked on the
shrunk family S(n1, r1, n2, r2, b) = (1, 2) :: (1, 1) ::
(1, 2) :: (1, 2) :: (1, 2)^n1 ++ (r1, 2) :: (1, 1) :: (1, 2) ::
(1, 2) :: (1, 2)^n2 ++ (r2, 2) :: (1, 1) :: (1, 2)^(b − 1)
(the hsim41 analogue is S(7, 22, 3, 26, 6)). At ~50 parameter
points — one-at-a-time sweeps of every parameter (b ∈ 2..12,
n1 ∈ {0, 1, 2, 4, 10}, r1 ∈ {5, 6, 7, 10, 14, 15, 23, 30, 31},
both parities — the real r1 = 149 is odd — n2 ∈ {0, 1, 6, 10},
even r2 ∈ {2, 6, 14, 26}), mixed points, and edge cases
(n2 = 0: 1,056,284 rules, five frame growths; n2 = 1; r2 = 2,
the M = 616 residue; the minimal corner S(0, 6, 3, 2, 2),
46 rules) — **every completed walk terminates at
`HB pb a 1 (2b + 1) [] 1` with b ≤ a**, using only proved
`hstep` constructors (per-point histogram audit; the two
unmechanised hsim rows, PX2A0 at b = 3, 4, never fire in any
cascade walk). Terminal frame values are affine in the
parameters (at the base family: grown blocks n1 + 17,
2n1 + 11, r1 + n2 + 1; a = r2 + 4 for even r2 ≥ 4) — the
landing *shape* is the invariant, the values are not.
Machine-level REGEN from the terminal config is confirmed at
cost 4s + 22 at three parameter points (the REGEN_gen
landing `HC pb a 1 2 [] (s − 1)`). **Growth probes toward the
real parameters** (n1 = 40; r1 = 149; n2 = 334; r2 = 100; two
mixed points) all hit the 3M-rule cap still walking — CAP,
never stuck, never a wrong landing: the word-walk length
grows exponentially in the segment grind parameters (nested
`hGRIND` recursion multiplies segment lengths), so primitive
walking cannot reach the real parameters and the proof must
go through the lemmas, as in every previous phase. **One
genuine fence the tests found**: for **odd r2** (out of
family — the era residue 2M − 1230 is always even) the walk
still lands B-over-empty with G = 1, but at shuttle
**s = 2b + r2**, not 2b + 1 (verified at r2 ∈ {3, 5, 9, 15,
29}; the difference r2 − 1 is independent of b; r2 = 1 is
degenerate, landing at s = 2b + 14 at b = 6, no law asserted).
So β′ = 2β + 4 is an even-residue phenomenon, and
CASCADE_LANDING's parity is load-bearing — the same parity
sensitivity the era laws showed at Phases 35/39.

**Mechanised (new file `rocq/Grind10.v`, 222 lines; Loop.v
953 lines).** (i) **`CASCADE_STAGE4`** — the cascade's rounds
stage, proved in general: for m + 1 ≤ a,
`hsteps (HC pb a 1 2 ((2m + 4, 2) :: P) 1)
(HB pb a 1 (2m + 6) ((2, 2) :: P) 1)` — TDN + TUP +
`hGRIND 0` + `GG_rounds` (Grind2.v). (ii) **`CASCADE_POPFIN`**
— the cascade's final POP chain, proved: for 1 ≤ b,
`hsteps (HB pb a 1 3 (repeat (1, 2) (b − 1)) 1)
(HB pb (a + b − 1) 1 (2b + 1) [] 1)` (Grind6's
`pop_chain_h_app` at s = 3). Every completed hsim42 walk ends
with exactly these two stages: a frame-growth step onto the
rounds stage's source, then the POP chain. (iii) The
**reduction**: `ESC_TO_REGEN_BIG8_of` and `ESC_ERA_LAW_42`
(Grind10.v) prove the phase-8 era law — β ↦ 2β + 4 at
`esc_src (2M + 52) (β − 2)` — from CASCADE_LANDING, by
composing `PHASE7_TO_MID` (stated for all m ≥ 279, so it
covers M ≥ 616 directly), `PHASE8_TO_STAGE_D` and
`ESC_ERA_LAW_of` (Grind3.v); and Loop.v's **`ESC_ITER_BIG8`**
/ `ESC_ITER_BIG8_step` (Part 4c) discharge H_LOOP's ESC
instances at **every even R ≥ 1278** modulo CASCADE_LANDING
(a lemma parameter, like ERA_GEN was — never an axiom).
With `ESC_ITER_1276`, every even R is now covered:
unconditionally for R ≤ 1276, modulo the single named
statement above it. **The remaining core is exactly
CASCADE_LANDING**: its stages 1–3 (the segment grinds at
frames [5], [24; 5], [25; 24; 5]) have parameter-dependent
parses — the frame-growth count across the sweep is 2..6,
not a fixed four stages, and the binding constraint is a
floor *inside* the segment grinds (at the base analogue the
stage-2 boundary grind ends at frame counter exactly
a = r + 2: the floor binds with equality). A proof needs a
totality theorem for the segment grind itself: at each
segment, the grind of a (1, 2)-spine + residue pair at
g0 = 1 over an arbitrary deeper tail, with existential
frame/shuttle values — the grind analogue of `DIPDESC` for
the g0 = 1 regime. That is the precisely-fenced core; the
landing, its last two stages, and the whole reduction to the
era law and the loop are proved. **No F-5**: the correction
concerns the reading of Phase 41's own (correct) machine
evidence, not the proof documents. Full clean rebuild of all
**twenty-five** files passes; a consolidated audit of 25
headline lemmas across all phases (including
`CASCADE_STAGE4`, `CASCADE_POPFIN`, `ESC_ERA_LAW_42`,
`ESC_ITER_BIG8`, `NONHALT_FROM_R_std`) reports "Closed under
the global context" for every one; no admits, no axioms.

**Phase 43 (2026-11-25): CASCADE_LANDING's stages 1–3 proved in
the era regime; the cascade reduced to its stage-4 core.**
Phase 42 left exactly the cascade's stages 1–3 open, with
parameter-dependent parses. Phase 43 parses them on the shrunk
family S(n1, r1, n2, r2, b) of hsim42 **in the era regime —
r1 = 149 is odd**, where the parse differs from hsim42's
even-r1 base analogue — and mechanises them exactly. All
boundary formulas were asserted verbatim in the new file
`rocq/hsim43.py` (ALL PHASE 43 CHECKS PASS) before
mechanisation. Write x = n1 + 17, A1 = 2*n1 + 10,
m1 = (r1 − 7)/2, A_pre = A1 + n2 + 3, s_pre = 2*m1 + 2*n2 + 12
(= r1 + 2*n2 + 5).

**Stage 1** is parity-free: TDN + POP (1, 2) + POP (1, 1) + a
POP chain over the first spine + TUP + `hGRIND_even (n1 + 3)`
+ `hTUP2_1`, landing at `HC [x; 5] A1 1 2 ((r1 − 4, 2) ::
(1, 1) :: Tail)`. **Stages 2+3 merge** in the era regime: the
odd pair (r1 − 4, 2) = (2*m1 + 3, 2) is ground by the new
**`GG_odd`** — `grind_prefix` + the odd GG rounds
**`GG_rounds_odd`** (induction on m1 over
`Grind2.grind_round`) — to a (1, 2) head, so the grind runs
through (1, 1) and the whole second spine before TUP on
(r2, 2); then `hGRIND_even (m1 + n2 + 4)` and `hTUP2_1` land
at the stage-4 source `HC [A_pre + 1; x; 5] s_pre 1 2
((r2 − 4, 2) :: (1, 1) :: Tail)`. This `GG_odd` is the
g0 = 1 totality the Phase 42 fence asked for, in the form the
cascade actually needs: the odd-pair grind at g0 = 1 over an
arbitrary deeper tail, with the explicit floor **m1 + 1 ≤ A1**
— and the merged stage's second floor (hGRIND_even's
m1 + n2 + 4 ≤ A1 + n2 + 3) is the *same* floor. Both are
**M-independent**: r2 enters stages 1–3 only through TUP /
hTUP2_1 / two dispatch branches (era values: 72 ≤ 90,
71 ≤ 89). The branches: **r2 = 4** (M = 617) — the
hGRIND_even target's second pair is (2, 2), hTUP2_1 cannot
fire, `hTRANS2_2` fires instead (terminal A = β + 2 after
POPFIN); **r2 = 2** (M = 616) — after the POPs the head is
the residue (2, 2) itself and `hTRANS2_1` fires directly
(terminal A = s_pre + β + 1). **Stage 4** then splits at the
`CASCADE_STAGE4` floor m4 + 1 ≤ s_pre (m4 = M − 619):
**619 ≤ M ≤ 1440** is the clean regime (CASCADE_STAGE4 +
hTRANS2_1 + CASCADE_POPFIN, all Phase 42); **M = 618**
(r2 = 6) is a fifth branch the composition exposed — the
stage-4 pair is (2, 2) itself and the stage degenerates to
TDN + hTRANS2_1 + POPFIN (machine-checked at the era frame
in hsim43). What remains is the **boundary regime
M ≥ 1441**, where the grind rounds exhaust the counter
budget (j = a) and the walk re-routes through dips / PX2A
re-basings onto a larger budget — the same mechanism as the
even-family point S(7, 22, 0, 26, 6) of hsim42; hsim43 walks
two shrunk odd-family boundary points (S(7, 7, 0, 32, 6):
45,143 rules; S(4, 9, 1, 40, 3): 527,131 rules, 3 frame
growths) onto the era landing shape. It is stated as the
strictly smaller residual core:

> **CASCADE_STAGE4_BIG**: for every M ≥ 1441 and β ≥ 2, the
> stage-4 source `HC [428; 57; 5] 822 1 2 ((2*M − 1234, 2) ::
> (1, 1) :: repeat (1, 2) (β − 1)) 1` reaches
> `HB pb a 1 (2β + 1) [] 1` for some pb, a with β ≤ a.

**Mechanised (new file `rocq/Grind11.v`, 604 lines; Loop.v
1009 lines).** `pop12` (POP chains over (1, 2)-spines),
`GG_rounds_odd`, `GG_odd`, `CASCADE_STAGE1`,
`CASCADE_STAGE23`, `CASCADE_STAGE23_r2_4`,
`CASCADE_STAGE23_r2_2`, the Definition
`CASCADE_STAGE4_BIG`, **`CASCADE_LANDING_of`** (the five-way
composition: CASCADE_LANDING modulo CASCADE_STAGE4_BIG) and
**`ESC_ERA_LAW_43`**; Loop.v Part 4d adds
**`ESC_ITER_BIG8_43` / `ESC_ITER_BIG8_43_step`**, discharging
H_LOOP's ESC instances at every even R ≥ 1278 modulo
CASCADE_STAGE4_BIG. **H_LOOP's ESC side is NOT closed**: it
now rests on CASCADE_STAGE4_BIG alone — one pair at one
fixed frame — in place of the whole three-stage cascade.
No F-6: the M = 618 branch is a case the Phase 42/43
statements did not distinguish, found by the composition
itself (the floor identity 2*M − 1234 = 2*(M − 619) + 4
fails exactly there, by truncated subtraction), not an error
in any proved statement. Full clean rebuild of all
**twenty-six** files passes; a consolidated audit of 28
headline lemmas across all phases (including `GG_odd`,
`CASCADE_STAGE1`, `CASCADE_STAGE23`, `CASCADE_LANDING_of`,
`ESC_ERA_LAW_43`, `ESC_ITER_BIG8_43`,
`NONHALT_FROM_R_std`) reports "Closed under the global
context" for every one; no admits, no axioms.

**Phase 44 (2026-11-25): the stage-4 boundary grind
characterised at the general 3-block frame and mechanised
segment by segment; CASCADE_STAGE4_BIG reduced to the
tail core CASCADE_STAGE4_TAIL.** Phase 43 left the single
core CASCADE_STAGE4_BIG: the grind of the pair
(2*M − 1234, 2) at the fixed frame [428; 57; 5], counter
822, M ≥ 1441. Phase 44 first characterises that grind at
the general frame [f; p; 5] (counter a, pair (2m + 4, 2),
tail (1, 1) :: (1, 2)^(β − 1), boundary regime a ≤ m) in
the new harness `rocq/hsim44.py` (ALL PHASE 44 CHECKS
PASS): the segment boundary configurations below were
asserted verbatim in the walk histories at nine stage-4
points (the S-family regime, era-ratio points with p ≪ f,
a deficit sweep, and the two T3-boundary points
(44, 4, 6, 8, 3) and (50, 5, 6, 8, 3)), at five T4-source
points, and in one growth probe; every walk uses only
proved hstep constructors and lands on the era shape.

The grind's engine is the phase's one new totality,
**`GG_boundary`** — the dip-aware rounds: CASCADE_STAGE4's
clean decomposition (TDN, TUP, `hGRIND` 0, rounds) with
the rounds split at the budget. After a − 1 clean rounds
(the new **`GG_rounds_part`**, GG_rounds with the endpoint
left symbolic) the shuttle is 2a + 4 and the residue pair
is (2(m − a) + 4, 2); the last round's section grind
cannot return to HB — the counter is exhausted — and
re-routes through **TUP + `DIPDESC` a**, emptying the
section onto the PX2A-ready form
`HC pb 0 3 2 (repeat (1, 2) a ++ ((2(m − a) + 2, 2) :: w))`.
The measure is the round count against the counter: the
boundary round is DIPDESC at t = a exactly. On top of it
the segments are: **SEG1** = GG_boundary at [f; p; 5] +
`hPX2A` (re-basing to [5], counter p − 1, g0 = f − 2);
**SEG2** = `hPUSH` + GG_boundary at [5] (counter p − 2,
pair (2·mp + 4, 2) with mp = (f − 8)/2) + `hPX2B5`
(re-basing to [0]); **T1** = POP (1, 1) + `pop12` p +
`hTUP` + `hGRIND_even` p (the (g2, 2) pair re-based to
(g2 − 2, 2) under a fresh (2, 2), g2 = 2(mp − p + 2) + 2);
**T2** = one `hTUP2_1` step onto [p + 5; 0], the pair
becoming (2·m3 + 4, 2) with m3 = mp − p − 1; **T3** = the
era regime m3 ≥ 2p + 4 (equivalently f > 6p + 14 at the
era ratios): GG_boundary at counter 2p + 4 + `hPX2A0`
(the clean regime m3 + 1 ≤ 2p + 4 is `GG_clean`, Phase
29); **T4** at p = 2q + 1 (era q = 28) = `hTUP` +
`grind_prefix` + two rounds + `hTUP` + `DIPDESC` 3 +
`hPX2B0` — the last re-basing, onto the bottom frame []
with shuttle 5.

What remains is the strictly smaller residual core:

> **CASCADE_STAGE4_TAIL**: for every q ≥ 5, β ≥ 2 and
> every v3, vM, a, the tail source
> `HB [] 0 1 5 (TAILs q v3 vM a β) 1` — the stack
> (1, 2)^4 :: (2q − 8, 2) :: (1, 1) :: (1, 2) :: (1, 2) ::
> (1, 2)^(4q + 6) :: (2·v3 + 2, 2) :: (1, 1) :: (1, 2) ::
> (1, 2) :: (1, 2)^a :: (2·vM + 2, 2) :: (1, 1) ::
> (1, 2)^(β − 1) — reaches `HB pb A 1 (2β + 1) [] 1` for
> some pb, A with β ≤ A.

It is strictly smaller than CASCADE_STAGE4_BIG on every
axis: the frame is the bottom frame [] (both PX2A
re-basings and the PX2B0 dip are discharged), the
parameters are the tail's own (q, v3, vM, a, β) with the
era parities baked in (residues 2·v + 2 — the parity
fence of hsim42 forbids the odd forms), and its source is
the T4 landing, not a mid-cascade configuration.
hsim44 Part 4 traverses the tail end-to-end at the
minimal points (97–176 rules); at larger parameters its
grind depths compound (Part 5 probe: S4 boundary reached,
tail still walking at the 6,000,000-rule cap — never
stuck, never a wrong landing), and its sub-structure
re-enters boundary grinds at regrown frames ([5],
[14; 5] in the probe walks): the tail is a grind system
of the same kind, one level down — the next target.

**Mechanised (new file `rocq/Grind12.v`, 537 lines; Loop.v
1069 lines).** `GG_rounds_part`, `GG_boundary`,
`STAGE4_SEG1`, `STAGE4_SEG2`, `STAGE4_T1`, `STAGE4_T2`,
`STAGE4_T3`, `STAGE4_T4`, the Definition
`CASCADE_STAGE4_TAIL`, **`CASCADE_STAGE4_BIG_of`**
(CASCADE_STAGE4_BIG modulo CASCADE_STAGE4_TAIL, at the
era point f = 428, p = 57, a = 822, mp = 210, m3 = 152,
q = 28) and **`ESC_ERA_LAW_44`**; Loop.v Part 4e adds
**`ESC_ITER_BIG8_44` / `ESC_ITER_BIG8_44_step`**,
discharging H_LOOP's ESC instances at every even
R ≥ 1278 modulo CASCADE_STAGE4_TAIL. **H_LOOP's ESC side
is NOT closed**: it now rests on CASCADE_STAGE4_TAIL
alone — the tail at the bottom frame — in place of one
pair at one fixed frame. No F-7: every Phase 44 segment
statement was machine-tested in hsim44.py before
mechanisation; the one identity that failed during the
proof work (the T2 pair identity at p = 1, a
truncated-subtraction corner, refused by lia) was
corrected to its exact domain (p ≥ 2) — a domain
correction to a new lemma, not an error in any proved
statement. Full clean rebuild of all
**twenty-seven** files passes; a consolidated audit of 28
headline lemmas across all phases (including
`GG_boundary`, `STAGE4_SEG1`, `STAGE4_T4`,
`CASCADE_STAGE4_BIG_of`, `ESC_ERA_LAW_44`,
`ESC_ITER_BIG8_44`, `NONHALT_FROM_R`) reports "Closed
under the global context" for every one; no admits, no
axioms.

**Phase 45 (2026-11-25): the stage-4 tail mechanised at
the era slice; CASCADE_STAGE4_BIG reduced to the single
residue core TAIL2_BIG.** Phase 44 left the core
CASCADE_STAGE4_TAIL: the tail traversal at the bottom
frame, over all q ≥ 5, v3, vM, a, β. Its only use in the
whole development is `CASCADE_STAGE4_BIG_of`, which
instantiates it at the **era slice** (q, v3, a) =
(28, 34, 822) (via `S4s_era`). Phase 45 characterises
the tail at that slice in the new harness
`rocq/hsim45.py` (**ALL PHASE 45 CHECKS PASS**: primitive
walks from the tail source at four small points; macro
walks — proved lemmas as macros over a primitive
fallback — at seven era points × β ∈ {2, 3} in the
clean range, with every layer boundary asserted
verbatim; boundary-regime probes at vM = 1653 / 2000 /
5366; a primitive-step audit) and finds a three-layer
parse:

- **Layer 0** (q = 28): `pop12` 4, TUP, PUSH,
  `GG_boundary` (3, 3), PUSHX, `pop12` 3, TUP2_1,
  `GG_boundary` (13, 20), PX2Bgen, pops, TUP,
  `hGRIND_even` 15, TUP2_1, `GG_clean` 4, TRANS2_1 —
  landing at `HB [35; 20; 0] 15 1 3 (TAIL1s v3 vM a b)`.
  Only the (48, 2) residue and its (1, 1) separator are
  touched; (v3, vM, a, β) are carried symbolically.
- **Layer 1** (v3 = 34): `pop12` 120, TUP,
  `hGRIND_even` 119, TUP2_1, `GG_clean` 31, TRANS2_1 —
  landing at `HB [243; 135; 35; 20; 0] 69 1 3
  (TAIL2s vM β)`.
- **Layer 2** (a = 822): `pop12` 824 reaches the
  residue state `HB [243; 135; 35; 20; 0] 893 1 1651
  ((2·vM + 2, 2) :: (1, 1) :: (1, 2)^(β − 1))`. For
  **vM ≤ 1652** the residue closes cleanly: TUP,
  `hGRIND_even` 823, then TRANS2_1 (vM = 0), TRANS2_2
  (vM = 1), TDN + TRANS2_1 (vM = 2) or TUP2_1 +
  `GG_clean` (vM − 3) + TRANS2_1 (3 ≤ vM ≤ 1652), then
  the POP chain; final counters β + 1651 / β + 2 /
  β + 4 / 2·vM + β, all ≥ β (asserted verbatim in
  hsim45 Part 2). For **vM ≥ 1653** the pair
  (2·vM − 2, 2) at counter 1650 is in the boundary
  regime: `GG_boundary` (1650, vM − 3) lands at
  `HC [893; 243; 135; 35; 20; 0] 0 3 2` (spine 1650 ++
  ((2·vM − 3304, 2) :: (1, 1) :: spine (β − 1))) and
  PX2A pops to [135; 35; 20; 0] with g0 = 891 — a
  frame-dependent dip descent. The macro walk
  *completes* there (vM = 1653 / 2000 / 5366, finals
  asserted verbatim in hsim45 Part 3), but its length
  grows with vM (4473 / 5165 / 14529 macro steps) and
  the descent's sub-parses depend on the frame blocks:
  no uniform cycle exists in the current lemma
  vocabulary — the Phase 38 wall, one level down.

What remains is the strictly smaller residual core:

> **TAIL2_BIG**: for every vM ≥ 1653 and β ≥ 2, the
> residue state `HB [243; 135; 35; 20; 0] 893 1 1651
> ((2 * vM + 2, 2) :: (1, 1) :: repeat (1, 2) (β − 1)) 1`
> reaches `HB pb A 1 (2 * β + 1) [] 1` for some pb, A
> with β ≤ A.

It is smaller than CASCADE_STAGE4_TAIL on every axis:
one pair at one fixed state (frame, counter and
shuttle all fixed), one parameter (vM, with β carried
only in the final POP spine), and only the boundary
range vM ≥ 1653 — the parameters q, v3, a are
discharged, and the clean range is proved. Stated
plainly: **Grind12's universal CASCADE_STAGE4_TAIL
does NOT fall in Phase 45** — it is strictly stronger
than the proof needs — **but H_LOOP's ESC side now
rests on TAIL2_BIG alone**: via `TAIL_ERA_of`,
**`CASCADE_STAGE4_BIG_45`** (Grind12's SEG1–T4
composition with the era tail supplied by the slice)
and **`ESC_ERA_LAW_45`**, and Loop.v Part 4f's
**`ESC_ITER_BIG8_45` / `ESC_ITER_BIG8_45_step`**, the
ESC instances at every even R ≥ 1278 discharge modulo
TAIL2_BIG. No F-8: every Phase 45 segment statement
was machine-tested in hsim45.py before mechanisation,
and Grind13.v compiled on its first full build.

**Phase 46 (2026-11-25): the TAIL2_BIG descent
mechanised; TAIL2_BIG proved for vM ≤ 5365 and reduced
to the END-state core TAIL2_END.** Phase 45 left the
core TAIL2_BIG, blocked — per its report — by the
frame-dependent dip descent after `GG_boundary`
(1650, vM − 3) and PX2A at frame [135; 35; 20; 0],
g0 = 891, with no uniform cycle in the vocabulary.
Phase 46 traces that descent in the new harness
`rocq/hsim46.py` (**ALL PHASE 46 CHECKS PASS**: all
51 waypoints of the descent asserted verbatim, in
order, at k = vM − 1652 ∈ {1, 2, 3, 48, 348, 3713} ×
β ∈ {2, 3}; the END parses and finals asserted for
k ∈ {1, 2, 3, 4, 5, 10, 100, 3712, 3713}; full
TAIL2_BIG source walks at vM ∈ {1653, 1654, 1655,
2000, 5365} × β ∈ {2, 3}; the k ≥ 3714 fence finals
asserted verbatim; a primitive-step audit) and finds
the descent is a **fixed parse, uniform in (k, β)** —
the Phase 45 "frame-dependent sub-parses" are the
four dip levels of one recursion, each closed by one
new lemma:

- **DIPGRIND** (the boundary rounds at a general
  counter): `HC pb A 3 2 ((2A + r, 2) :: w) G` →
  `HC pb 0 3 2 (spine A ++ ((r, 2) :: w)) G` for
  1 ≤ A, 1 ≤ r — proof `hGRIND` 0 +
  `GG_rounds_part` (A − 1) + TUP + `DIPDESC` A. The
  four levels are (A, r) = (241, 405) at
  [135; 35; 20; 0], (33, 63) at [20; 0], (3, 6) at
  [0], (3, 2) at [] over the pair (4, 2).
- Between levels: PX2A, PX2A0, PX2B0 + `pop12` 4,
  PUSHX + `pop12` 3; frame regrowth TUP2_1 + TDN +
  TRANS2_1 onto [14; 5], `pop12` 35; the (63, 2)
  pair by TUP + `hGRIND_even` 34 + TUP2_1 + TDN +
  TUP onto [40; 14; 5]; the (405, 2) pair likewise
  (`hGRIND_even` 273) onto [317; 40; 14; 5].
- **CLEANG_odd** (the clean grind of an odd pair
  (2m + 3, 2) at counter 3, floor m + 2 ≤ a2): the
  (57, 2) and (399, 2) pairs grind cleanly to (1, 2);
  `pop12` 1, POP, `pop12` 243 / 1652 close the
  descent at the **END state**
  `HB [317; 40; 14; 5] 2204 1 3711
  ((2k, 2) :: (1, 1) :: (1, 2)^(β − 1))`. The whole
  descent is one hsteps chain, **`DESCENT46`**, with
  no side conditions on k (the front is
  `TAIL2_FRONT`).

The END state then closes **uniformly for
1 ≤ k ≤ 3713** (`END46_1`, k = 1: TRANS2_1 +
CASCADE_POPFIN, A = 3711 + β; `END46_2`, k = 2:
TRANS2_2, A = β + 2; `END46_3`, k = 3: A = β + 4;
`END46_big`, 4 ≤ k ≤ 3713: A = 2k + β − 2): after
TUP + `hGRIND_even` 1853 + TUP2_1 + TDN + TUP, the
pair (2k − 6, 2) grinds cleanly at counter 3710 by
the new **CLEANG_even** (the clean grind of an even
pair (2m + 2, 2) at counter 3, floor m + 1 ≤ a2),
then TRANS2_1 + CASCADE_POPFIN. CLEANG_even's floor
is exactly 2k − 6 ≤ 2·3710 ⟺ k ≤ 3713. At
**k ≥ 3714** the rounds take the DIPDESC boundary
instead (hsim46 Part 4: the boundary config
`HC [2204; 317; 40; 14; 5] 3710 7423
((2, 2) :: (1, 1) :: ...)` occurs at k = 3714) and
the walk completes only through a further descent
whose finals gain a cycle per k-band (k = 3714 →
frame [4002; 1279; 745; 151; 77; 35; 20; 0],
A = 7429; k = 5000 → frame
[7427; 4001; 1279; 745; 151; 77; 35; 20; 0]) — the
Phase 38 wall, one level further down; no finite
case analysis in the current vocabulary closes
every k.

What remains is the strictly smaller residual core:

> **TAIL2_END**: for every k ≥ 3714 and β ≥ 2, the
> END state `HB [317; 40; 14; 5] 2204 1 3711
> ((2 * k, 2) :: (1, 1) :: repeat (1, 2) (β − 1)) 1`
> reaches `HB pb A 1 (2 * β + 1) [] 1` for some pb, A
> with β ≤ A.

It is smaller than TAIL2_BIG on every axis: one
B-section state (no 1651-counter front, no
four-level descent), one pair, and only the range
k ≥ 3714 (vM ≥ 5366) — the range vM ≤ 5365 is
proved. Stated plainly: **TAIL2_BIG does NOT fall
outright in Phase 46 — it is PROVED for
1653 ≤ vM ≤ 5365 and reduced, above that, to
TAIL2_END**: via **`TAIL2_BIG_of`** and
**`ESC_ERA_LAW_46`**, and Loop.v Part 4g's
**`ESC_ITER_BIG8_46` / `ESC_ITER_BIG8_46_step`**,
**H_LOOP's ESC side now rests on TAIL2_END alone**.
No F-9: every Phase 46 segment statement was
machine-tested in hsim46.py before mechanisation
(the two checker corrections during development —
bundle-intermediate configs missing from the walk
sequence, and the descent walk continuing past END
to the era landing — were harness display issues,
not statement errors; the mechanised statements are
exactly the asserted ones).

**Mechanised (new file `rocq/Grind14.v`, 730 lines;
Loop.v 1207 lines).** Arithmetic-form step wrappers
`sTUP`, `sPUSH`, `sTDN`, `sPOP1`, `sTUP2_1`,
`sTRANS2_1`; `DIPGRIND`, `CLEANG_odd`,
`CLEANG_even`; the descent stacks `PXs`, `W1s`,
`W2s`; `TAIL2_FRONT`, `DESCENT46`; `END46_1`,
`END46_2`, `END46_3`, `END46_big`; the Definition
`TAIL2_END`; `TAIL2_BIG_of`, `ESC_ERA_LAW_46`;
Loop.v Part 4g adds `ESC_ITER_BIG8_46` /
`ESC_ITER_BIG8_46_step`. Full clean rebuild of all
**twenty-nine** files passes (~3.5 min); Grind14.v's
own 11 audits and Loop.v's 33 audits are closed,
and a consolidated audit of 21 headline lemmas
(`DIPGRIND`, `CLEANG_odd`, `CLEANG_even`,
`TAIL2_FRONT`, `DESCENT46`, `END46_1`, `END46_2`,
`END46_3`, `END46_big`, `TAIL2_BIG_of`,
`ESC_ERA_LAW_46`, `ESC_ITER_BIG8_46`,
`ESC_ITER_BIG8_46_step`, `TAIL2_CLEAN`,
`CASCADE_STAGE4_BIG_45`, `ESC_ERA_LAW_45`,
`ESC_ITER_BIG8_45`, `GG_boundary`,
`CASCADE_STAGE4_BIG_of`, `NONHALT_FROM_R`,
`NONHALT_FROM_R_std`) reports "Closed under the
global context" for every one; no Admitted / Axiom
/ Parameter in the 16,607 lines of .v sources. The
checkpointed phase10 background run was not
disturbed (read-only checks only; its
checkpoint/log timestamps remain 2026-11-24).

**Mechanised (new file `rocq/Grind13.v`, 565 lines;
Loop.v 1135 lines).** `TAIL_LAYER0`, `TAIL_LAYER1`,
the Definition `TAIL2_BIG`, `TAIL2_CLEAN`,
`TAIL2_ALL`, `TAIL_ERA_of`, `CASCADE_STAGE4_BIG_45`,
`ESC_ERA_LAW_45`; Loop.v Part 4f adds
`ESC_ITER_BIG8_45` / `ESC_ITER_BIG8_45_step`. Full
clean rebuild of all **twenty-eight** files passes
(~3.1 min); Grind13.v's own 7 audits and Loop.v's 31
audits are closed, and a consolidated audit of 15
headline lemmas (`TAIL_LAYER0`, `TAIL_LAYER1`,
`TAIL2_CLEAN`, `TAIL2_ALL`, `TAIL_ERA_of`,
`CASCADE_STAGE4_BIG_45`, `ESC_ERA_LAW_45`,
`ESC_ITER_BIG8_45`, `ESC_ITER_BIG8_45_step`,
`GG_boundary`, `CASCADE_STAGE4_BIG_of`,
`ESC_ERA_LAW_44`, `ESC_ITER_BIG8_44`,
`NONHALT_FROM_R`, `NONHALT_FROM_R_std`) reports
"Closed under the global context" for every one; no
Admitted / Axiom / Parameter in the 17,505 lines of
.v sources. The checkpointed phase10 background run
was not disturbed (read-only checks only; its
checkpoint/log timestamps remain 2026-11-24).

## Toolchain

- **Coq 8.18.0** (the proof assistant, pre-Rocq rename; compiled with OCaml
  4.14.1). No system-wide install: the distribution packages were fetched
  with a workspace-local apt state and extracted under
  `~/workspace/coq-toolchain/`; the wrapper `rocq/coqcw` (with `rocq/env.sh`)
  sets `COQLIB`, `OCAMLFIND_CONF`, etc. and invokes that `coqc`.
- Build (from `~/workspace/busy-beaver/rocq/`), in dependency order:

  ```
  ./coqcw TM.v        # machine, execution, entry lemmas, M1–M4
  ./coqcw Configs.v   # concrete configurations (generated)
  ./coqcw Finite.v    # finite segments by kernel computation
  ./coqcw Sections.v  # standard frame: five rules + REGEN
  ./coqcw Mirror.v    # right-edge entry + mirror rules + RI
  ./coqcw TokenPass.v # token pass: Cycle Lemma Gamma + the exit
  ./coqcw DiagPass.v  # #16 stage 2: the diagonal token pass (Phase 30)
  ./coqcw Recoord.v   # #16: re-coordinatisation stages 1-3
  ./coqcw Era.v       # #18: ENTRY_gen, Grind Lemma G', ERA_LAW
  ./coqcw EraGen.v    # #18: ERA_GEN, the general-residue era law (Phase 35)
  ./coqcw Esc.v       # #19 pieces: POP2, probe prefix E1-E5
  ./coqcw Dev.v       # #19: deviation step lists (Phase 28)
  ./coqcw Grind.v     # #19: frame-general lists, word model, G'' pieces
  ./coqcw Grind2.v    # #19: G'' endpoint + ESC-era law (Phase 29)
  ./coqcw EraEven.v   # #18: the even-residue era law (Phase 39; requires Grind/Grind2)
  ./coqcw Grind3.v    # #19: REBASE + ESC-era law to R <= 40 (Phase 31)
  ./coqcw Grind4.v    # #19: second re-basing, ESC-era law to R <= 114 (Phase 33)
  ./coqcw Grind5.v    # #19: third re-basing dip bottoms, hGRIND_dev0 (Phase 36)
  ./coqcw Grind6.v    # #19: merged unwind, ESC-era law to R <= 268 (Phase 37)
  ./coqcw Grind7.v    # #19: phase-6 merged unwind, ESC-era law to R <= 602 (Phase 38)
  ./coqcw Grind8.v    # #19: phase-7 merged unwind, ESC-era law to R <= 1276 (Phase 40)
  ./coqcw Grind9.v    # #19: phase-8 entry + stages A-C, DIPDESC_even, fenced cascade (Phase 41)
  ./coqcw Grind10.v   # #19: cascade landing: CASCADE_STAGE4/POPFIN + reduction to CASCADE_LANDING (Phase 42)
  ./coqcw Grind11.v   # #19: cascade stages 1-3 in the era regime + reduction to CASCADE_STAGE4_BIG (Phase 43)
  ./coqcw Grind12.v   # #19: stage-4 boundary grind segments (GG_boundary) + reduction to CASCADE_STAGE4_TAIL (Phase 44)
  ./coqcw Grind13.v   # #19: the stage-4 tail at the era slice (TAIL_LAYER0/1, TAIL2_CLEAN) + reduction to TAIL2_BIG (Phase 45)
  ./coqcw Grind14.v   # #19: the TAIL2_BIG descent (DIPGRIND, DESCENT46, END46) + reduction to TAIL2_END (Phase 46)
  ./coqcw Loop.v      # cross-era loop assembly (Phase 32; ESC_ITER_114 Phase 33; ESC_ITER_268 Phase 37; ESC_ITER_602 Phase 38; ESC_ITER_1276 Phase 40; ESC_ITER_BIG8 Phase 42; ESC_ITER_BIG8_43 Phase 43; ESC_ITER_BIG8_44 Phase 44; ESC_ITER_BIG8_45 Phase 45; ESC_ITER_BIG8_46 Phase 46)
  ./coqcw Std.v       # standard-regime assembly: H_STD discharged (Phase 34)
  ```

  Clean rebuild from scratch (Phase 38): all twenty-one files compile with
  **no errors** in ~98 s (a few benign warnings: unused introduction
  patterns in `halt_iff`, a comment-delimiter warning, large-nat-literal
  notices in Finite.v). Every headline lemma below was checked with
  `Print Assumptions`: **“Closed under the global context”** — no axioms,
  no admits, anywhere. (Phase 39: the same clean rebuild over all
  twenty-two files, EraEven.v included, passes in ~2.5 min; Loop.v's
  audit list is now 21 lemmas, all closed.) (Phase 40: the same
  clean rebuild over all twenty-three files, Grind8.v included,
  passes in ~2 min; Loop.v's audit list is now 23 lemmas, all
  closed; Grind8.v's own audits — ESC_ERA_LAW_1276, GRIND108_MID,
  PHASE7_TO_MID — are closed.) (Phase 41: the same clean rebuild
  over all twenty-four files, Grind9.v included, passes in ~2 min;
  Grind9.v's own audits — DIPDESC_even, PHASE8_TO_MID,
  PHASE8_STAGE_A, PHASE8_STAGE_B, PHASE8_STAGE_C,
  PHASE8_TO_STAGE_D — and Dev.v's PX2Bgen audit are closed;
  Loop.v's audit list is unchanged at 23 lemmas, all closed.)
  (Phase 42: the same clean rebuild over all twenty-five
  files, Grind10.v included, passes; Grind10.v's own audits —
  CASCADE_STAGE4, CASCADE_POPFIN, ESC_TO_REGEN_BIG8_of,
  ESC_ERA_LAW_42 — and Loop.v's new ESC_ITER_BIG8 /
  ESC_ITER_BIG8_step audits are closed; a consolidated audit
  of 25 headline lemmas across all phases is closed.)
  (Phase 43: the same clean rebuild over all twenty-six
  files, Grind11.v included, passes in ~2.5 min; Grind11.v's
  own audits — pop12, GG_rounds_odd, GG_odd, CASCADE_STAGE1,
  CASCADE_STAGE23, CASCADE_STAGE23_r2_4,
  CASCADE_STAGE23_r2_2, CASCADE_LANDING_of, ESC_ERA_LAW_43 —
  and Loop.v's new ESC_ITER_BIG8_43 / ESC_ITER_BIG8_43_step
  audits are closed; a consolidated audit of 28 headline
  lemmas across all phases is closed.)
  (Phase 44: the same clean rebuild over all twenty-seven
  files, Grind12.v included, passes in ~2.6 min; Grind12.v's
  own audits — GG_rounds_part, GG_boundary, STAGE4_SEG1,
  STAGE4_SEG2, STAGE4_T1, STAGE4_T2, STAGE4_T3, STAGE4_T4,
  CASCADE_STAGE4_BIG_of, ESC_ERA_LAW_44 — and Loop.v's new
  ESC_ITER_BIG8_44 / ESC_ITER_BIG8_44_step audits are
  closed; a consolidated audit of 28 headline lemmas across
  all phases (the 12 new Phase 44 lemmas among them) is
  closed.)
  (Phase 45: the same clean rebuild over all twenty-eight
  files, Grind13.v included, passes in ~3.1 min; Grind13.v's
  own audits — TAIL_LAYER0, TAIL_LAYER1, TAIL2_CLEAN,
  TAIL2_ALL, TAIL_ERA_of, CASCADE_STAGE4_BIG_45,
  ESC_ERA_LAW_45 — and Loop.v's new ESC_ITER_BIG8_45 /
  ESC_ITER_BIG8_45_step audits are closed; a consolidated
  audit of 15 headline lemmas is closed.)
  (Phase 46: the same clean rebuild over all twenty-nine
  files, Grind14.v included, passes in ~3.5 min; Grind14.v's
  own audits — DIPGRIND, CLEANG_odd, CLEANG_even,
  TAIL2_FRONT, DESCENT46, END46_1, END46_2, END46_3,
  END46_big, TAIL2_BIG_of, ESC_ERA_LAW_46 — and Loop.v's
  new ESC_ITER_BIG8_46 / ESC_ITER_BIG8_46_step audits are
  closed; a consolidated audit of 21 headline lemmas is
  closed.)
- Representation: list-zipper configurations `(state, left, right)`,
  head on `hd right`, blanks implicit — the list-based style of the
  bbchallenge Coq developments (Coq-BB5), specialised to this machine.
  `run n c = Some c'` is the fuel-based executor; a `Some` result already
  certifies that no step on the way halted (cf. `halt_iff`).

## What is proved in Rocq

### TM.v — framework and the halt criterion (component #8, complete)

- `trans`, `step`, `run`, `cfg_blank`, `tape_of`; `run_split`,
  `run_some_step_neq`, `halt_iff` (a step fails ⟺ E-on-0 read — the only
  undefined transition).
- Entry (predecessor) lemmas `pred_E/D/C/F/B` by finite inspection of the
  table: E only from D-on-1; D only from C-on-0; C only from B-on-0 or
  F-on-0; F only from D-on-0, E-on-1 or F-on-1; B only from A-on-0 or B-on-1,
  each with the exact successor shape.
- **M1** (`M1_fwd`, `M1_rev`): halting ⟺ a C-on-0 read whose left cells are
  (1, 0) (zipper form of tape[p−1] = 1, tape[p−2] = 0).
- **M2**: B-entry into that C is always safe. **M3**: the D-on-0 route into
  F is safe (C reads the 1 that D wrote). Both as stated in
  `post-R-proof.md` §1.
- **M4** (`danger`, `M4_rev_local`, `M4_fwd`, `M4_halt_iff`): from the blank
  tape, the machine halts ⟺ some F-on-0 configuration has left triple
  (0, 1, 0). Note: in the zipper formulation the forward direction needs no
  entry case analysis — after the F-step, the C-config's head cell *is*
  tape[q−1] and its left list is the F-config's shifted by one, so all three
  danger components are M1's data read through `pred_C`'s F-case. M3 is
  nevertheless proved as stated (it is the human proof's route, and the
  event lists of the rule derivations use it).

### Finite.v — finite segments by kernel computation (`vm_compute`)

Each check is `seg_check n c0 c1 = true`, proved by `vm_compute`, with
`seg_check_sound` giving the semantic form (same state, same tape) and
`seg_no_halt` extracting “no halting step en route”. Negative controls were
run: off-by-one counts and wrong endpoints return `false`.

| Check | Segment | Status |
|---|---|---|
| `seg_D132_R` | D(132,66) → R in **403,455** steps (component #6) | **proved** |
| `seg_R_Isec` | R → first I-section in **150** steps (component #9) | **proved** |
| `seg_exit4`, `seg_exit4_X` | σ_re(4) → H_4 in **T(4) = 102**, exit successor X_4 at +6 (component #15, instance) | **proved** |
| `seg_exit8`, `seg_exit8_X` | σ_re(8) → H_8 in **T(8) = 2,850**, exit successor X_8 at +6 (component #15, instance) | **proved** |
| `seg_blank_S2`, `seg_S2_S4` | blank → S(2) in 197,317; S(2) → S(4) in 18 (component #1, instances) | **proved** |
| `seg_Sp2_Sp4`, `seg_Sp4_Sp6` | S′(2) → S′(4) in 18; S′(4) → S′(6) in 42 (component #4, instances) | **proved** |

### Sections.v — standard frame: five rules + REGEN (components #10, #11, #17)

Section configs `csec`/`bsec` over the single-block I⁺ frame (see the file
header for the two representation choices: C-sections parametrised by
a2 = a − 2; a continuation-style `tail` fixpoint so pair-prepending is
definitional). The only inductions are the three sweeps (`sweepA`,
`sweepB`, `sweepF`) and `rep_app`, exactly as in the hand derivations;
`probe` is the 5-step probe lemma. Proved, for all parameters in the
stated domains:

- **TDN** — cost 6, for every a2.
- **PUSH** — cost 9, g0 = S(S(S g″)) (i.e. g0 ≥ 3), a2 = S a2′.
- **POP-general** (`pop_prefix` + `pop_sweep` → `POP`) — cost 2s + 3,
  s′ = s + r₁ for every r₁ ≥ 1, s ≥ 2. This is component #17's POP-general.
- **TUP** (Phase 25; `tup_prefix` + probe + `sweepF`) — cost 2s + 6,
  s ≥ 2, first gap g₁ ≥ 3 written S(S(S g₁″)): lands the C-section with
  shuttle s′′ = s − 2, g₀′ = 2 and first pair (g₁″, r₁). With TUP, **all
  five standard rules are sound in Rocq** (component #10's rule layer).
- **Stage A** — cost 2s + 6, s ≥ 2, G ≥ 3, landing the C-section with
  g0′ = s − 1, G′ = G − 2.
- **G bookkeeping (#11) discharged**: the five statements show TDN, PUSH,
  POP and TUP preserve the terminal gap G, and Stage A sends G ↦ G − 2;
  no rule creates or destroys terminal gap otherwise. No separate lemma
  is needed beyond reading the five statements.

REGEN (component #17, completed in Phase 25) is assembled exactly as
`phase19-derivations.md` §1 decomposes it — the POP step list run to the
terminal pair, the Stage A step list at the blank end, the PUSH step
list — via three frame lemmas:

- `POP_terminal` — the POP step list at the terminal pair (pairs = [],
  G = 1): run (2s + 3) lands the *open* B-section `bsec_open (a+1) 1 (s+2)`
  (right side `0 1^{s+2}`, then blank). The blank-end forms `bsec_open`,
  `csecT`, `csecR` carry the tail beyond the working region explicitly.
- `StageA_blank` — the Stage A step list at the blank end: run (2L + 6)
  (L ≥ 2) lands `csecT A (L−1) [false]`.
- `PUSH_T` — the PUSH step list (9 steps) on the `csecT` form.
- **`REGEN`** — run (4s + 22) (bsec a 1 s [] 1) = Some (csecR a (s−1)
  [false]) for every a ≥ 0 (a2 = a − 2 encoding) and s ≥ 2: the documents'
  map (B, a, s, [1], 1) → (C, a+2, 2, [1], G = s−1), span +2, cost 4s + 22.
  One representation fact, proved as `REGEN_tape`: the landing's tape
  equals the tape of the clean section `csec a 1 2 [] (s−1)` — the
  Stage-A-at-blank probe materialises one trailing blank cell in the
  zipper's right list, carried explicitly in the tail parameter
  (r = [false]); the tapes agree at every position.

### Mirror.v — right-edge entry + mirror system (components #12, #13) — Phase 25

Mirror-frame sections over an *abstract frozen prefix*: the left list is
`repeat true b ++ P` with `P` an arbitrary list of cells, so every lemma
holds uniformly in the frozen prefix (the mirror rules never read it).
The working region `rtail pairs` ends in a run — blank beyond — with no
terminal [1;1] block (that is what distinguishes the mirror frame).
β (the left block length) is b + 2 at C-sections (`rcsec`, parametrised
by b2 = β − 2) and b at B-sections (`rbsec`). Proved, for all parameters
in the stated domains, exactly as in `rightedge-derivation.md` §2:

- **RTDN** — cost 6: (C, β, (1, r₁)::…) → (B, β, (1, r₁+2)::…).
- **RPUSH** — cost 9, β ≥ 3: creates the pair (1, 2), first gap g ↦ g − 2.
- **RPOP** — cost 2r₁ + 3 (`rpop_prefix` + `rpop_sweep`): merges the first
  two runs, β ↦ β + 1.
- **RTUP** — cost 2r₁ + 6 (`rtup_prefix` + probe + `sweepF`): lands the
  C-section with pair (r₁ − 2, 2), second gap g₂ ↦ g₂ − 2.
- **RPROBE** — cost 2r₁ + 6 (`rprobe_prefix` + `probe_blank` + `sweepF`):
  the empty-stack probe; its landing `rcsec_probe` carries the probe's
  trailing [1;1;0] tail, and `RPROBE_tape` proves its tape equals the
  documents' C-section (β + 2, pair (r₁ − 1, 2), no further pairs).
- **Invariant RI (parity layer)**: `RI_pairs` (every pair has odd gap and
  even run) is preserved by each rule — `RI_rtdn`, `RI_rpush`, `RI_rpop`,
  `RI_rtup`, `RI_rprobe` (pure list arithmetic from the rule forms; the
  β side conditions are read off the statements).
- **ENTRY (component #12)** — the right-edge entry excursion of
  `rightedge-derivation.md` §1: from the standard-frame B-section
  (B, wall 1^17 0, block B2, gap 2, shuttle s, terminal [1;1]) — encoded
  as `entry_src B2 s` — run (s + 12) lands `entry_tgt B2 s` for every
  B2 ≥ 0 and s ≥ 1 (decomposition: entry prefix (s + 2) + 3 steps + the
  5-step probe + 2 steps). `ENTRY_tape` proves the landing's tape equals
  the first mirror C-section `rcsec P s [(1, 2)]` with frozen prefix
  P = 0 1^{B2+1} 0 1^17 and β = s + 2 — i.e. the documents' entry section
  (C, β_E := s, w = (1), v = (2)) up to the materialised trailing blank.

### TokenPass.v — token pass: Cycle Lemma Γ (#14) and the exit (#15) — Phase 26

Built directly on Mirror.v's proved rules. Because the mirror rules'
landings materialise an occasional trailing blank in the zipper's right
list (the same phenomenon as REGEN_tape), all iteration is done up to
`cfg_sim` (same state, same tape at every position): `step_sim_some`,
`step_sim_none`, `run_sim`, `run_sim_transfer`, with `sim_rprobe` and
`sim_entry` transporting the RPROBE and ENTRY landings to clean section
forms. The token pass itself is formalised at the level of **B-start
words** (gap lists with all runs = 2, the joint invariant J = "all gaps
odd", `Jg`):

- **Phase and excursions**: `PHASE` (RPUSH+RTDN, cost 15) and
  `PHASE_second` (the H-type phase second at cost 9); the excursion cost
  functional `excR` with the closed form on ones-words
  (`excR_repeat1`: excR R (repeat 1 j) = 2j² + (2R+5)j + 2R + 6) and the
  excursion lemmas `EXC_TUP` / `EXC_PROBE` / `EXC_prefix` by induction on
  the merged-run list.
- **Rounds**: `ROUND_A` (type A, cost 29, Δβ = −1), `ROUND_B_TUP` and
  `ROUND_B_PROBE` (type B, cost 15 + excR 4 (1::ms)), `CLOSING_H`.
- **The composed two-round map Ψ**: `psi_run_gen` — for Jg xs with
  u = lo xs < length xs, Ψ runs in `psicost u = 2u² + 17u + 73` steps
  from the B-start (β, (3, x)) to (β + u − 1, (3, wpsi x)) with an
  arbitrary pair-suffix carried verbatim; `psi_step` packages it as a
  step relation on B-start states (S-arg b2 = word β − 3, word xs).
- **Suffix Lemma transports**: `psi_step_front` (Ψ commutes with
  appending a fixed odd tail gap — the Suffix Lemma at step level),
  `psi_step_last2f` (Ψ commutes with last-gap + 2, split case and carry
  case), packaged over orbit segments by `borbit_map`. Orbits are the
  inductive `borbit` (a chain of Ψ steps with all S-args ≥ lb), with
  `borbit_run`, `borbit_lb`, `borbit_weaken`, `borbit_trans`.
- **Orbit recursion** (`borbit_cycle`, the derivation's §5 recursion):
  cycle (2+j)'s orbit = cycle (2+j−1)'s orbit replayed with the last gap
  + 2, then the carry Ψ step at (repeat 1 j ++ [3]), then the same orbit
  at B − 1 with a 1 appended to every word — total cost `bcost (2+j)`,
  with closed form `bcost_closed` (bcost k + 2k² + 13k + 62 = 3·2^{k+3}
  for k ≥ 2).
- **Cycle Lemma Γ** (`CYCLE`): for every frozen prefix P, frame B and
  k ≥ 2 with k − 2 ≤ B,
  run (Dk k) (rcsec P (B+2) ((2k+1, 2)::[])) =
  Some (rcsec_probe P (B+2) (2k+3)), Dk k = 3·2^{k+3} − 4; `CYCLE_sim`
  gives the landing up to cfg_sim as the clean section S_{k+1}.
- **Min-β facts**: `CYCLE_H` — the tokenless home section
  H_k = rcsec P (B−(k−2)) (repeat (1,2) (k+1)) (word β = β_E − k
  exactly) is reached 29 + bcost k + 9 steps into cycle k (attainment);
  `borbit_lb` applied to `borbit_cycle` bounds every orbit B-start's
  S-arg below by B − (k−2) (the derivation-level induction passes
  through every Ψ step node), the closing B-start attains it, and the
  phase-second/excursion landings (`PHASE_second`, `EXC_prefix`) sit at
  rbsec/rcsec args ≥ the round's source S-arg. This is the derivation's
  (ii)/(iii) at section granularity.
- **Cycles 0 and 1** (`CYCLE0`, `CYCLE1`): the finite base cycles,
  costs 20 = D_0 and 44 = D_1, from RTDN/RPROBE and ROUND_B_PROBE.
- **The exit (#15)**: `Dsum` with `Dsum_closed`
  (Dsum K + 4K + 28 = 3·2^{K+3} + 4); `EXIT_iter` iterates the cycles
  from S_0 up to cfg_sim; `EXIT` — at K = β_E − 2 ≥ 2, after
  Tk K = Dsum K + 29 + bcost K + 9 steps the configuration is cfg_sim
  to H_K (rcsec arg 0, word β = 2), and 6 further steps (RTDN,
  event-clean since the run is a `Some`) land cfg_sim at
  rbsec P 0 ((1, 4) :: repeat (1, 2) K), the exit successor in shifted
  coordinates; `EXIT_time`: Tk K + 2K² + 17K + 48 = 3·2^{K+4};
  `EXIT_entry` instantiates the exit at the actual entry prefix
  P = 0 1^{B2+1} 0 1^17 via `sim_entry`. Headline checks:
  `Print Assumptions CYCLE / CYCLE_H / EXIT / EXIT_entry` all report
  **“Closed under the global context.”**

### Recoord.v — re-coordinatisation (#16) — Phase 27

The post-exit continuation of `phase19-derivations.md` §3, in three
stages, over C-sections `gcsec Q a2 g0 s pairs G` parametrised by an
abstract tail Q (`gcsec_nil`: `gcsec [] = csec`).

- **Stage 1 — PROVED** (`STAGE1`, `STAGE1_exit`): the RPOP chain from
  the exit successor. The chain lemma (induction on j) fires RPOP at
  r₁ = 2j + 4 with cost 4j + 11 and landings 2j² + 9j, closing with
  RPROBE; composed with `EXIT` via `run_sim_transfer`, `STAGE1_exit`
  gives: from any mirror C-section `rcsec P K ((1, 2)::[])` — in
  particular the entry section, at K = β_E − 2 — after
  (Tk K + 6) + (2K² + 13K + 14) steps (the Tk K + 6 being the exit
  itself) the configuration is cfg_sim to
  `rcsec P K ((2K + 3, 2)::[])` — the stage-2 source
  S_{β_E−1}(β_E) in shifted coordinates.
- **Stage 2 — instances proved, general case fenced as a hypothesis**:
  `STAGE2 B2 n` is the proposition that the second token pass (the
  Phase 17 suffix recursion on the diagonal) runs in Tk n steps from
  the stage-2 source to cfg_sim of the escape source
  `esc_cfg B2 n = rcsec (entryP B2) 0 ((3, 2):: repeat (1, 2) n)`.
  It is **kernel-verified** at the trajectory's entry parameter
  B2 = 31 for β_E ∈ {4, 6, 8} (`stage2_inst_2/4/6`, costs
  Tk 2 = 102, Tk 4 = 620, Tk 6 = 2850, by `seg_check` + `vm_compute`),
  and (Phase 28) at B2 = 31 for n = 8 and n = 10 (`stage2_inst_8/10`,
  Tk 8 = 2850, Tk 10 = 11976 steps) and at n = 2 for B2 = 15 and
  B2 = 47 (`stage2_inst_15_2`, `stage2_inst_47_2`) — the statement's
  B2-independence and n-scaling are pinned at seven points.
  The general case is a second token-pass development on the diagonal
  (same architecture as TokenPass.v: a word model, round maps, a suffix
  recursion) and is carried as the explicit hypothesis of `RECOORD2` —
  see “Remaining components” below.
  **(Phase 30: the general case is PROVED** — `STAGE2_proved` in
  Recoord.v, from `DSTAGE2` in the new file DiagPass.v (next section);
  the hypothesis is discharged and the instances remain as regression
  checks.)
- **Stage 3 — PROVED for all B2 ≥ 2** (`STAGE3`): the RPUSH escape +
  F-sweep of `phase19-derivations.md` §3, cost B2 + 11, landing the
  canonical standard-frame C-section
  `gcsec Q (L−1) (B2−2) 2 ((1,1):: repeat (1,2) (n+1)) 1` for every
  abstract tail Q, frame L ≥ 1 (the B2 = 2 case is a separate short
  chain; the sweep is `sweepF` at cost b3 + 1 plus list bridging
  `tail_rtail` / `s3R_snoc`). On the trajectory (L = 17, B2 = 31) this
  is the canonical section with a = 16 and residue ρ = B2 − 2 = 29.
- **`RECOORD2` — the conditional composition, PROVED**: for B2 ≥ 3,
  n ≥ 2, given `STAGE2 B2 n`, the full chain ENTRY-exit → stage 1 →
  stage 2 → stage 3 runs in
  (Tk n + 6) + (2n² + 13n + 14) + Tk n + (B2 + 11) steps from
  `entry_tgt (B2−1) n` to cfg_sim of the canonical section
  `csec 16 (B2−2) 2 ((1,1):: repeat (1,2) (n+1)) 1` — the standard I⁺
  frame with a = 16, s = 2, first pair (1, 1), word (1, 2)^{n+1},
  G = 1. This is the two-block (settled-frame) landing of #16; the
  composed loop map reads β′ = ρ + 2β_E + 5 off `ERA_LAW` below.
  **(Phase 30: `RECOORD2_uncond`** — the same statement with no
  hypothesis, via `STAGE2_proved`; #16's two-block landing is fully
  mechanised.)
- **The B2 convention (resolved in Phase 27)**: Mirror.v's
  `entry_src B2` carries the prefix block **S B2** (its frozen prefix is
  0 1^{B2+1} 0 1^17), whereas the documents' “B2 = 31” is the *absolute*
  second block in the mirror frame. The trajectory's ENTRY therefore
  instantiates at Mirror-B2 = 30. Recoord.v's `entryP B2` uses the
  absolute block (prefix 0 1^{B2} 0 1^17), and `RECOORD2` instantiates
  `EXIT_entry` at (B2 − 1) accordingly. Verified against the Phase 19
  segment models (the stage-3 traces `p19-esc12.cfg` / `p19-esc-b31.cfg`
  and `phase19_segment_check.py`, which build the tape with block 31).

### DiagPass.v — the diagonal token pass (#16 stage 2) — Phase 30

Stage 2 for an **arbitrary frozen prefix P**, in the documents'
descent + walk decomposition (`phase19-derivations.md` §3.2,
`phase21-derivations.md` §6). All forms were pre-verified against
the Python word models (`phase17_model.py`, `phase19_stage2.py`,
plus a dedicated recursion check for k ≤ 9) before proving.

- **The T₂ word map and the source invariant** (Part 1): `F2`
  (last gap − 2, gap 3 appended), `frontw`/`lastw`, and
  `wok w` := all gaps odd, `lo w < length w`, last gap ≥ 3, and
  (front of w not all ones ∨ last gap ≥ 5). `wok` is preserved by
  `F2` (`wok_F2`) and by `last2f` (`wok_last2f`), and `lo` is
  preserved by `F2` at `wok` words (`lo_F2`).
- **Ψ transports** (Part 2): `psi_step_shift` (Ψ is invariant under
  a uniform +1 block shift, via `psi_run_gen`), `psi_step_last2f_up`
  (the T₁ transport: `psi_step_last2f` + shift), and `psi_step_F2`
  (the T₂ transport, under `wok`; the front-all-ones case goes
  through `wpsi_app_ones` / `wpsi_F2_ones`).
- **`fchain`** (Part 3): the `borbit` analogue carrying `wok` at
  every step source, with `fchain_borbit` (to `borbit` at lb = 0),
  `fchain_trans`, `fchain_last2f_up`, `fchain_F2`.
- **The descent orbit** (Part 4): `dorbit_cycle` — for every j, an
  `fchain` from (j; [2j+3]) to (0; 1^j ++ [3]) of cost
  `bcost (2 + j)`, by induction on j: the T₁ replay of the previous
  orbit, the join Ψ step at (1; 1^j ++ [5]) (via `PSI_RUN`), and
  the T₂ replay. The cost recursion is exactly TokenPass's
  `bcost`, so `bcost_closed` applies verbatim.
- **DESC** (Part 5): for k ≥ 2 and every odd gap suffix `sfx`,
  run (bcost k + 38) from `rcsec P k ((2k+3, 2):: gpairs sfx)`
  reaches (exactly, hence cfg_sim) `rcsec P 0 (gpairs (1^k ++ [3])
  ++ gpairs sfx)` — the A-round (`ROUND_A`), the descent orbit
  with the suffix appended (`borbit_map` over `psi_step_front_list`),
  and the closing RPUSH (`PHASE_second`).
- **The walk** (Parts 6–7): `rpop_chain` (the RPOP chain with a
  general head run and tail: cost 2·R·j + 2j² + j, head R + 2j);
  `WALK` — W_i → W_{i−1} in `Dk (i−1)` steps for every i ≥ 1
  (RTDN + chain + RTUP, then: nothing at i = 1, a single
  `PHASE_second` at i = 2, `DESC (i−1)` at the grown suffix
  `1 :: sg` for i ≥ 3; the cost identity at i ≥ 3 is
  `bcost_closed`); `WALK_ITER` iterates the walk from W_j to W_0
  in `Dsum j` steps.
- **`DSTAGE2`** (Part 8): DESC(n) at the empty suffix composed
  with `WALK_ITER` at j = n: run (Tk n) from
  `rcsec P n ((2n+3, 2)::[])` reaches cfg_sim of
  `rcsec P 0 ((3, 2):: repeat (1, 2) n)`, for every P and n ≥ 2.
  `Print Assumptions DESC / WALK / DSTAGE2` all report
  **“Closed under the global context.”**

### Era.v — the era law (#18, deviation-free assembly) — Phase 27

- **`ENTRY_gen`** — Mirror.v's ENTRY generalised to an abstract
  standard-frame tail P0: from `entry_src_gen P0 a s` (the B-section
  (B, a, 2, s, []) over tail P0 ++ 0 1^{a+1} 0 1^17 ++ [1;1]) run
  (s + 12) lands `entry_tgt_gen P0 a s`, whose tape is the mirror
  C-section over the frozen prefix P0 ++ 0 1^{a+1} 0 1^17
  (`ENTRY_gen_tape`, `entry_gen_sim`); `bsec_entry_src` identifies the
  P0 = [] source with `bsec a 1 s [] 2`. Mirror's ENTRY is the case
  P0 = 0 1^17.
- **`GRIND`** — the Grind Lemma G′ in endpoint form: for every t, frame
  a2 and carried pairs P, **under the frame-floor hypothesis
  t + 1 ≤ a2**, there is a cost with
  run cost (csec a2 (2t+3) 2 P G) = Some (bsec a2 1 (2t+6) P G).
  Proof: strong induction on t (the recursion halves the gap). Base
  t = 0: PUSH + TDN + POP (costs 9 + 6 + 11). Step: prefix
  PUSH + TDN + TUP (9 + 6 + 14), an inner loop (induction on k)
  alternating `GRIND` at smaller t (the outer IH) with TUP, and a final
  `GRIND` at t − 1 + POP. The frame floor is exactly the hypothesis
  that keeps every recursive application inside its domain — the
  load-bearing content of the documents' floor clause for the era law.
  **Fenced**: the dip clause as a *sequence* statement — “during the
  grind, min a_C = a − (m−1)/2, attained only at w₀ = 1 sections” —
  is not formalised; it quantifies over the grind's internal
  rule-boundary sections, which the endpoint form does not expose.
  Route: a section-sequence formulation of the grind (an inductive
  predicate over C/B-section boundaries with the a-values recorded),
  or a prefix-quantified strengthening of `GRIND`'s induction. The era
  law below does not need it: every grind application in the era
  discharges the floor hypothesis directly.
- **`POP_CHAIN`** — the POP chain over a run list: from
  `bsec a 1 s (map (fun r => (1, r)) rs) G` with every r ≥ 1 and
  s ≥ 2, some cost reaches `bsec (a + length rs) 1 (s + rsum rs) [] G`
  (helpers `map_repeat_2`, `rsum_repeat_2` for the ones/2-runs of the
  era word).
- **`ERA_LAW` — PROVED**: for every n ≥ 1, from the canonical era entry
  `csec 16 29 2 ((1,1):: repeat (1,2) (n−1)) 1` (a = 16, residue
  ρ = 29, s = 2, word (1,2)^{n−1} after the first pair, G = 1) some
  cost reaches cfg_sim of the next era's entry mirror section
  `rcsec (0 1^{n+17}) (2n + 32) [(1, 2)]` — i.e. **β′ = 2n + 34**
  with the new frozen prefix 0 1^{β_E + 17}. Assembly: `GRIND` at
  t = 13 (the residue grind, floor 14 ≤ 16 discharged) →
  `POP_CHAIN` over the run list 1 :: 2^{n−1}, giving the REGEN source
  with **s₁ = 2n + 31** and frame a_f = n + 16 → `REGEN` (cost
  4s + 22; the landing transported to the clean csec via `REGEN_tape`)
  → TDN → the Stage-A era loop (induction on j with k + j = n + 14;
  invariant s + G = 2n + 34, so G = 2n + 30 − 2k is always even —
  **the odd-G sub-case is excluded** — each cycle Stage A + `GRIND`
  at k, floor k + 1 ≤ a_f discharged since k ≤ n + 13 < n + 16) →
  `ENTRY_gen` at P0 = []. In particular **β′ = 2n + 34 > n**: the era
  map strictly increases β, hence the span. The trajectory case is
  n = β_E with ρ = 29, giving the documents' s₁ = 2β_E + 31 and
  β′ = 2β_E + 34.

### EraGen.v — the general-residue era law (#18, ERA_GEN) — Phase 35

- **`ERA_GEN_proved` — PROVED on its domain**: Loop.v's `ERA_GEN`
  statement (the era law in ERA_LAW's shape at residue ρ) for
  every **odd ρ with 1 ≤ ρ ≤ 33** and every era parameter
  m ≥ 1: from `csec 16 rho 2 ((1,1):: repeat (1,2) (m−1)) 1`
  some cost reaches cfg_sim of `rcsec (0 1^{m+17}) (rho + 2m + 3)
  [(1, 2)]` — s₁ = ρ + 2m + 2, β′ = ρ + 2m + 5 (phase19 §2).
  Assembly = ERA_LAW's with ρ = 2t + 1: absorption (`TDN` at
  t = 0; `GRIND` at t − 1 for t ≥ 1, floor t ≤ 16 at the fixed
  frame a2 = 16) → `POP_CHAIN` over 1 :: 2^{m−1} → `REGEN` →
  TDN → the Stage-A era (induction on j with k + j = t + m;
  invariant s + G = ρ + 2m + 5, G₀ = ρ + 2m + 1 even) →
  `ENTRY_gen` at P0 = []. The two floor families (the residue
  grind at a2 = 16; the era-loop grinds at frame m + 16) give
  the **same** bound t ≤ 16, i.e. ρ ≤ 33. The frame a2 = 16 is
  not a specialisation to the trajectory: stage 3 of #16 lands
  at a = 16 for every two-block prefix, so 16 is the settled
  frame's own constant.
- **Fences (exact, machine-checked)**: ρ ≥ 35 odd — the
  residue grind's dip (ρ − 1)/2 exceeds the frame a2 = 16
  (GRIND at t − 1 = 16 would need floor 17 ≤ 16); ρ even —
  Lemma G′ is odd-only and the era's G parity is
  load-bearing (phase19 §2.4's odd-G exclusion is the ρ-odd
  hypothesis in disguise: without it G₀ is odd and the
  Stage-A era cannot land on the G = 2 entry source).
  Pre-verification (`rocq/era_gen_verify.py`, TM.v step
  semantics): the predicted boundary sequences are hit in
  order with REGEN / TDN / Stage A / ENTRY deltas equal to
  the proved costs at (ρ, m) = (29, 2) [the ERA_LAW control],
  (27, 1), (27, 2), (31, 1), (31, 2), (33, 1) [domain
  boundary, floors at equality] and (1, 2) [absorption =
  TDN, delta 6]; the absorption landing is never reached in
  20,000,000 steps at (35, 1) and (30, 1).
  (Phase 39: the ρ-even fence is a fence of this statement's
  shape — the even era law is proved on a different shape in
  EraEven.v, below; the ρ ≥ 35 fence stands in both parities,
  with the beyond-frame behaviour documented there.)

### EraEven.v — the even-residue era law (#18, even ρ) — Phase 39

- **`ERA_GEN_even` — PROVED**: for every **even ρ = 2k + 2 with
  k ≤ 16** (i.e. ρ ≤ 34) and every era parameter m ≥ 1, from
  `csec 16 rho 2 ((1,1):: repeat (1,2) (m−1)) 1` some cost
  reaches cfg_sim of `rcsec P' (2m + 2) [(1, 2)]` — s₁ = 2m + 1,
  β′ = 2m + 4, **independent of ρ**. The shape differs from
  `ERA_GEN`'s (whose landing argument is ρ + 2m + 3) because the
  mechanism differs: the absorption does not grind the residue
  into the shuttle, it **rotates** it into the frame.
- **The absorption — `EVEN_GRIND`** (floor k ≤ A at a general
  frame A): k = 0 is **`ABS2`** (ρ = 2: a 3-step excursion
  0RA/1RA/1RB onto the rotated B-section). For k ≥ 1: PUSH +
  TDN; at k = 1 the residue pair is already (2, 2) and
  **`gROT2`** closes — the TUP-prefix excursion
  (`Esc.gtup_prefix`, cost s + 2) read as a section-to-section
  rotation: `gbsec P a 1 s ((2, r):: rest) G` →
  `gbsec (0:: 1^{a+1} ++ P) s 1 r rest G`. For k ≥ 2: TUP, then
  a climb of (GRIND i; TUP) with the residue pair descending
  2k − 2, 2k − 4, …, 2 (the odd GRIND's loop with shifted
  roles; GRIND floors i + 1 ≤ A − 1 ⟸ k ≤ A), and gROT2 at the
  (2, 2) pair. Landing: `gbsec (0::1^A) (2k+2) 1 2 pairs 1` —
  near block exactly ρ, s = 2, stack and G untouched. At the
  era frame A = 16 the deepest dip reaches a2 = 16 − k; at
  k = 16 the last PUSH lands on an a2 = 0 C-section, which POP
  (not PUSH) consumes — the floor is exact.
- **The era assembly** mirrors EraGen's, over the rotated
  frame P0 = 0::1^16: **`gPOP_CHAIN`** (the frame-general POP
  chain, from Grind.v's `gPOP`) → s₁ = 2m + 1 at frame
  a_f = ρ + m → `REGEN_gen` (Grind2.v) → `gTDN` → the Stage-A
  era (induction on j with kk + j = m − 1; invariant
  s + G = 2m + 4, G₀ = 2m even for every ρ — the parity that
  the odd script borrows from ρ odd is here supplied by the
  rotation) with cycles `gSTGA` + **`gGRIND`** (the Grind
  Lemma G′ over a general frame: the mirror of Era.GRIND with
  Grind.v's `gPUSH`/`gTDN`/`gTUP`/`gPOP`; floors
  kk + 1 ≤ ρ + m + 2 are slack) → `ENTRY_gen` at P0.
- **Pre-verification** (`rocq/era_even_verify.py`, TM.v step
  semantics): the full boundary sequence is hit in order, with
  POP deltas 2s + 3, REGEN delta 4·s₁ + 22, TDN delta 6,
  Stage-A deltas 2s + 6 and ENTRY delta s_fin + 12 all exact,
  at (ρ, m) = (2, 1) [66 steps], (2, 4), (4, 4), (6, 3),
  (10, 2), (28, 5), (30, 4) [393,555 steps] and (34, 4)
  [1,573,191 steps, domain boundary: the dip touches
  a2 = 0 exactly at a PUSH landing]; the absorption climb is
  checked separately at (10, 2) and (30, 2) (every GRIND/TUP
  boundary). **ALL CHECKS PASS.**
- **Fence — ρ ≥ 35, both parities** (`rocq/era_fence35_verify.py`):
  the era frame a2 = 16 is fixed by stage 3 of #16, and beyond
  it the machine's behaviour is not one uniform family:
  ρ = 35 absorbs (step 3,145,681) on `bsec 17 1 39` — a
  sub-frame edge excursion grows the frame by one, s = ρ + 4,
  and the following era would have G₀ odd (Stage-A parity
  obstruction); ρ = 37, 39, 41 absorb by rotation on the
  two-block frame (38|17), s = ρ − 33; ρ = 36 rotates to
  (37|17), s = 2; ρ = 38, 40 show no absorption landing of
  either form within 60,000,000 steps. A mechanisation would
  need a sub-frame edge-grind theory (C-sections at a2 = 0:
  their excursion step lists and landings) that the current
  vocabulary does not contain. In Loop.v, B2 ≥ 37 therefore
  remains on the conditional `SETTLED_ITER_GEN`.

### Esc.v — single-block escape pieces (of #19's re-formation) — Phase 27

The ESC family of `phase20-derivations.md` / `phase21-derivations.md`
(the single-block, iteration-2 frame of #16). Delivered pieces:

- **`POP2` — PROVED, fully general**: the transfer rule of phase21
  §1.1, over an abstract frozen prefix P (`gbsec`): from
  (B, P, a, g₀ = 1, s = S s′, pairs (2,2) :: (1, S r₂′) :: rest, G)
  run (S s′ + 9) lands (B, 0 1^{a+1} P, S(S s′), 1, (1, r₂′ + 3) :: rest,
  G) — via the prefix-general TUP `gtup_prefix` (a copy of Sections'
  `tup_prefix` proof over the abstract prefix) plus 7 steps. Verified
  against the Python model for all rest/G including the boundary
  cases (the documents' side conditions are not needed).
- **`PROBE_PREFIX` — PROVED**: the probe prefix E1–E5 (phase20
  theorem P20.1): from `esc_src (l + 7) m` (the ESC source
  (C, [0] 1^L, right 1 1 0³ 1 1 RT(m)), L = l + 7, m = β − 2) run
  (L + 42) lands `e5form (S l) m` exactly. The five excursions are
  proved individually (E1's F-sweep via `sweepF`; E2–E5 by direct
  computation on the exposed forms). Domain note: the documents
  state L ≥ 8; the mechanised proof covers L ≥ 7 — the binding
  constraint is E5, whose excursion pattern needs the e4form zero
  run ≥ 3 (checked against the model: at run 2 the excursion leaves
  the E5 pattern).
- **`PROBE_PREFIX_sim` — PROVED**: the landing is cfg_sim to the clean
  C-section `csec 3 1 2 ((L−6, 2):: (1,1):: repeat (1,2) (β−1)) 1`
  (via the right-side identity `e5form_right` and the left-side
  `nth_app_false`).
- **Not delivered here**: the ESC-family era law β_next = 2β + 4.
  Its grind is G″ (#19), an induction over the deviation system, not
  over the five standard rules. **Delivered in Phase 29** (Grind2.v,
  for R ≤ 10; the R ≥ 12 re-basing segment stays fenced — see
  “Remaining components”).

### Dev.v — the deviation step lists (#19) — Phase 28

Every step list of `phase21-derivations.md` §§1–5, proved for **all**
parameters (abstract pair lists, terminal gap G, and frame tails), in
the absolute-coordinate style of Sections.v/Recoord.v. All were
pre-verified against a Python zipper tracer (`rocq/trace_dev.py`)
before formalisation.

- **Chain units**: `gturn` (the B-section turn closing a TRANS2 chain:
  sweepB + the landing step, cost r + 1), `gunit2` / `gunit2_mk` (the
  gap-1 transfer unit, cost r₁ + 2), `gtup_prefix_mk` (the folded-form
  variant of Esc.v's `gtup_prefix`).
- **PUSHX**: `PUSHX_core` (the uniform 20 steps from
  (C, pb = (), a = 2, s = 2, [3]+W) to (B, 0, 5, [1, g−2]+W, [2]+R),
  for all g ≥ 3) and `PUSHX` (the g = 3 closing via POP, total 33,
  landing (B, 1, 7, W, R)); `PUSHX_TUP` (the general-g follow-on: at
  g ≥ 5 the core landing continues by TUP, = Sections.v's `TUP`
  instantiated). PUSHX is a pb = () rule — its excursion reads the
  prefix; with a nonempty prefix the dispatch is PX2A/PX2B below.
- **PX2A**: `PX2A` (two-block prefix, b ≥ 3: cost b + 11, landing
  (C, pb[:-2], p + 1, 2, [b−2, 1, 1, 1] + W, [1, 2, 2] + R)) via
  `PX2A_chunkA` + `sweepF`; `PX2A_b2` (the b = 2 special form: cost
  23, landing (B, pb[:-2], p − 1, 5, [1, 1, 1] + W, [2, 2] + R)).
- **PX2B** (single prefix block): rows b = 2 (cost 43), 3 (38), 4 (29),
  5 (44), 6 (49) — all by direct computation with abstract pairs/G;
  the b = 4/5/6 landings are also stated in clean `gbsec` form
  (`PX2B_b4'/b5'/b6'`; the trailing blank the excursion materialises
  is the empty prefix block [0]). The b ≥ 7 row is Esc.v's
  `PROBE_PREFIX` (Phase 27), not redone.
- **CGAP2**: `CGAP2_probe` (4 steps, frame gain [a−2], new interface
  block 5), `CGAP2_pop` (6 steps) and `CGAP2_push` (9 steps), composed
  as `CGAP2_pop_total` (total 10) and `CGAP2_push_total` (total 13) —
  the documents' totals confirmed (the F-2 erratum concerns only the
  recursive re-probe accounting, whose first re-probe is the same
  probe lemma at the shifted frame).
- **TRANS2 / TUP2 chains**: `TUP2_1` (chain k = 1, all r₁: cost
  s + 2r₁ + 8, via `gtup_prefix` + `tup2_inner` + `tup2_probe` +
  `sweepF`); `TRANS2_1` (turn k = 1, all r₁ — the generalisation of
  Esc.v's `POP2`, which is its r₁ = 2 case); `TRANS2_2` (turn k = 2:
  two `gtup_prefix` units + `gunit2_mk` + `gturn`, landing frame
  gains [a+1, s+1] and shuttle r₂ + r₃). Era grinds have k ≤ 2
  (phase21 §6), so these are the chain forms the era system uses.
- **TUP2 defect (k = 1, r₁ = 1)**: `TUP2_defect` — total cost s + 23,
  assembled as `gtup_prefix` + `defect_merge` (7 steps) +
  `defect_fstep` + `TAIL13` (the 13-step tail from the post-F gcsec
  (g0 = 0, s = 2, pair gap w₂ − 2)). **The landing is the
  machine-corrected form** (C, pb + [a+1], s + 1, 2,
  [3, w₂ − 4] + w[3:], [r₂] + r[2:], G): the documents' §4 row
  ([w₂ − 2, 1] + w[3:]) agrees only at w₂ = 5 and is wrong for
  w₂ ≥ 6 — finding **F-3**, recorded as a dated erratum in
  `phase21-derivations.md` §4. The defect is era-unreachable (§8);
  the k ≥ 2, r_k = 1 stage-2 shapes remain fenced exactly as in the
  documents.

### Grind.v — frame-general lists, the word model, G″ pieces — Phase 28

- **Frame-general step lists** (Part 1): the five standard rules and
  CGAP2 over an abstract frozen prefix (`gcsec`/`gbsec` forms):
  `gTDN`, `gPUSH` (both by direct computation), `gPOP`
  (`gpop_prefix` + `gpop_sweep`, adapting Sections.v's POP proof),
  `gTUP` (`gtup_prefix3` + probe + `sweepF`), `gSTGA`
  (`gstageA_prefix` + `sweepA` + probe + `sweepF`), and
  `gCGAP2_probe/pop/push` with totals. These are the bridges the word
  model needs; PUSHX and REGEN have no such generalisation (PUSHX
  reads the prefix by design; REGEN's blank-end components
  POP_terminal/StageA_blank/PUSH_T are bsec-form — route: re-prove
  them over `gbsec` open forms).
- **The word model** (Part 2): `hsec` (C/B sections with prefix
  blocks as a nearest-first list of lengths, encoded to the raw
  zipper tail by `enc`) and the inductive `hstep` with **20
  constructors** = the phase21 §1 dispatch (TDN, PUSH, PUSHX at
  pb = (), PX2A, PX2A at b = 2, PX2B rows, CGAP2 pop/push, POP, TUP,
  STGA, REGEN at pb = (), TRANS2 turns k = 1/2, TUP2 k = 1, the TUP2
  defect). **`hstep_sound` — PROVED**: every `hstep` is realised by a
  machine run between the encoded configs (exactly, except REGEN
  whose machine landing is the tape-equal `csecR`, composed via
  `REGEN_tape`); **`hsteps_sound`** lifts this to step sequences via
  TokenPass.v's `run_sim_transfer`.
- **G″ pieces** (Part 3): `grind_prefix` — the forced prefix
  [TDN, TUP, PUSH, TDN, POP] of phase21 §7 as an `hsteps` chain:
  (C, pb, a₂ ≥ 1, [1, R] + W) → (B, pb, a₂, 6, [1, R−2] + W) for
  R ≥ 3, all frames; `grind_prefix_dev` — the dip-bottom deviation
  (a₂ = 0, pb = ()): [TDN, TUP, PUSHX] → (B, (), 1, 7, [1, R−2] + W).
  **`pred_cases` — PROVED**: a case analysis on `hstep` showing the
  only producers of a PUSH-at-a=2 source (HC with a₂ = 0, s = 2,
  g₀ ≥ 3) are TUP (source shuttle = g₀ + 2), STGA (source shuttle
  = g₀ + 1, empty pairs), PX2A (over a 0-block, frame block
  = g₀ − 1), and the TUP2 defect at g₀ = 3. The documents'
  Predecessor Lemma is then exactly the pair of invariant
  obligations: in an era grind (i) the TUP/STGA producers above
  have source shuttle exactly 4, and (ii) PX2A does not occur —
  both are consequences of the era stack invariant, whose
  preservation induction is the remaining G″ work (below).

### Grind2.v — G″ endpoint induction and the ESC-era law (#19) — Phase 29

All section forms were pre-verified against `phase21_model.py` /
`phase20_grind.py` before proving (the round decomposition of the
clean grind, `GRIND_dev(t)`'s shifted landing, the transfer/tail
bookkeeping s_regen = 2β + 1).

- **`hGRIND` — PROVED**: the word-level Grind Lemma G′ (Era.v's
  `GRIND` transplanted to `hstep`): for t + 1 ≤ a2, every pb, P, G,
  `hsteps (HC pb a2 (2t+3) 2 P G) (HB pb a2 1 (2t+6) P G)`. Same
  strong induction (prefix PUSH+TDN+TUP, loop of GRIND/TUP, final
  GRIND + POP).
- **`hGRIND_dev` — PROVED**: the deviated Grind Lemma G′ at the
  boundary frame a2 = t, pb = []:
  `hsteps (HC [] t (2t+3) 2 P G) (HB [] (t+1) 1 (2t+7) P G)` for all
  t, P, G. The recursion mirrors `hGRIND` exactly (its loop sub-calls
  are the clean `hGRIND` at frame t − 1, floors discharged from the
  loop equation); only the final spine call is `hGRIND_dev` again,
  and the base case t = 0 is the single `hPUSHX` step. Exactly one
  PUSHX occurs, on the final spine (model-checked at t = 0..3: rule
  counts 1, 5, 13, 29). This is obligation (c) in this regime: the
  PUSHX landing's continuation is the deviated grind itself, and the
  (+1, +1) landing shift is absorbed by the tail — the human proof's
  finite check is not needed here.
- **Obligation (b), clean regime — `GG_clean` PROVED**: rounds
  `grind_round` (TUP + `hGRIND(j)`) iterated by `GG_rounds` over
  Grind.v's `grind_prefix`: for R = 2m + 4 and m + 1 ≤ a2, every pb,
  P, G, `hsteps (HC pb a2 1 2 ((R, 2) :: P) G)
  (HB pb a2 1 (R + 2) ((2, 2) :: P) G)` — the G″ endpoint (transfer
  source) in the deviation-free regime.
- **`ESC_GRIND_10` — PROVED**: the R = 10 grind at the ESC frame
  a2 = 3: prefix + clean rounds 1–2 + round 3 = TUP +
  `hGRIND_dev(3)`, landing the transfer source
  `HB [] 4 1 13 ((2, 2) :: P) G` (the deviated (+1, +1) shift
  visible in a and s).
- **Transfer tail — `TAIL` PROVED**: `pop_chain_h` (the word-level
  POP chain) composed with `hTRANS2_1` (POP2): from the transfer
  source `HB pb a 1 s ((2, 2) :: (1, 1) :: (1, 2)^{β−1}) 1`, every
  s ≥ 1, β ≥ 1, the chain reaches the REGEN source
  `HB (S a :: pb) (s + β) 1 (2β + 1) [] 1` — s_regen = 2β + 1 and
  the frame inequality β ≤ a_final = s + β used by the era tail.
- **`ESC_TO_REGEN` — PROVED**: the ESC grind endpoint for
  R ∈ {2, 4, 6, 8, 10} (R = 2 by TDN alone; R = 4, 6, 8 by
  `GG_clean` at floors 1, 2, 3 ≤ 3; R = 10 by `ESC_GRIND_10`),
  composed with `TAIL`.
- **`REGEN_gen` — PROVED**: Sections.v's REGEN step list over an
  abstract frozen prefix (`POP_terminal_gen`, `StageA_blank_gen`,
  `PUSH_T_gen` over `gbsec` open forms), with `REGEN_gen_sim`
  transporting the `gcsecR` landing to the clean `gcsec` form (the
  route named in Phase 28's Grind.v summary).
- **`ERA_TAIL` — PROVED**: the era tail over an abstract frame:
  from `HB pb a 1 (2β + 1) [] 1` with β ≥ 2 and β − 1 ≤ a,
  `REGEN_gen` + TDN + the Stage-A era loop (`era_cycle` = STGA +
  `hGRIND`, iterated by `era_loop`) + Era.v's `ENTRY_gen` reach
  cfg_sim of `rcsec (0 :: 1^{a+1} ++ enc pb) (2β + 2) [(1, 2)]`.
- **`ESC_ERA_LAW` — PROVED for R ∈ {2, 4, 6, 8, 10}**: for β ≥ 2,
  from Esc.v's ESC source `esc_src (R + 6) (β − 2)`, some cost
  reaches cfg_sim of the mirror section with b2 = 2β + 2 — i.e.
  **β_next = 2β + 4** in the rcsec convention (β = b2 + 2),
  mirroring `ERA_LAW`. Assembly: `PROBE_PREFIX` +
  `PROBE_PREFIX_sim` → `ESC_TO_REGEN` (via `hsteps_sound`) →
  `ERA_TAIL` (composed via `run_sim_transfer`).
- **Obligation (a) — DISCHARGED for the grind chains**: `grind_inv`
  (B-sections at a = 0: head pair (w, r) has s + w ≤ 7 — the dip
  budget, saturated exactly by the deviated spine — gap-2 heads
  have run 2, the empty stack has s ≤ 3; C-sections at a2 = 0 with
  g0 ≥ 3 have pb = []), **`PRED_inv` — PROVED**: by case analysis
  on Grind.v's `pred_cases`, any `hstep` respecting `grind_inv` at
  both ends and landing on a PUSH-at-a=2 source forces g0 = 3,
  pb = [], and a TUP producer with source shuttle exactly 4 — the
  STGA producer contradicts the empty-stack clause, PX2A the
  frame clause, the TUP2 defect the gap-2/run clause. This is
  `pred_cases`' two obligations. **`PUSHX_only` — PROVED**: at
  `HC [] 0 3 2 pairs G` the only applicable constructor is
  `hPUSHX`. The invariant is threaded through every grind chain:
  `hstepsP` (invariant-respecting `hsteps`) versions `hGRIND_P`,
  `grind_prefix_P`, `grind_round_P`, `GG_rounds_P`, `GG_clean_P`,
  `hGRIND_dev_P`, `ESC_GRIND_10_P` are all proved, so every section
  of those chains satisfies `grind_inv` and `PRED_inv` applies to
  every step.
- **Fenced**: the R ≥ 12 ESC grind (the re-basing segment) — see
  “Remaining components” for the precise statement (`REBASE`),
  obstruction and route.

### Grind3.v — REBASE and the ESC-era law for R ≤ 40 (#19) — Phase 31

All section forms were pre-verified against `phase21_model.py`
before proving (the segment boundaries at R ∈ {12, 14, 16, 20, 22
(β = 7), 28, 38 (β = 3), 40}, and the F-4 fence check at R = 14, 18).

- **`REBASE_core` — PROVED** (no hypotheses): for every u, P, G,
  `hsteps (HC [] 4 12 2 ((u, 2) :: P) G)
  (HB [] 4 1 13 ((2, 2) :: (u, 2) :: P) G)` — PUSH + TDN + TUP, then
  `hGRIND` 0, TUP, `hGRIND` 1, TUP, `hGRIND` 2, TUP, `hGRIND_dev` 3,
  with the pair (u, 2) carried verbatim in the grind lemmas' stack.
  `REBASE_core_P` threads `grind_inv` (every boundary frame has
  a, a2 ≥ 1, so the `_pos` lemmas discharge it).
- **`REBASE` — PROVED**: for u ≥ 3, one closing `hTUP2_1`
  (r₁ = 2, w₂ = u) lands the fenced target
  `HC [5] 13 1 2 ((u − 2, 2) :: P) G` — from the F-4-corrected
  source (g0 = 12, not the fence's 11). `REBASE_P` threaded.
- **`ESC_GRIND_BIG` — PROVED**: for every R ≥ 12, P, G,
  `HC [] 3 1 2 ((R, 2) :: P) G → HC [] 4 12 2 ((R − 10, 2) :: P) G`
  (grind prefix + clean rounds 1–2 + TUP + `hGRIND_dev` 3 + TUP —
  the `ESC_GRIND_10` pattern at general R). `ESC_GRIND_BIG_P`
  threaded.
- **Endpoints — PROVED**, in `ESC_TO_REGEN`'s form (∃ pb a, the
  chain to `HB pb a 1 (2β + 1) [] 1` with β ≤ a):
  `ESC_TO_REGEN_12` (`REBASE_core` at u = 2, then `hTRANS2_2`
  consuming ((2, 2), (2, 2), (1, 1)) and `pop_chain_h`, landing
  `HB [14; 5] (β + 2) 1 (2β + 1) [] 1`); `ESC_TO_REGEN_14`
  (`REBASE` at u = 4, TDN, `TAIL`); `ESC_TO_REGEN_BIG`
  (R = 2m + 16, m ≤ 12: `REBASE` at u = 2m + 6, `GG_clean` at
  (pb = [5], a2 = 13) — floor m + 1 ≤ 13 — then `TAIL`).
- **`ESC_ERA_LAW_31` — PROVED for every even R ≤ 40**: the Phase 29
  era-law assembly factored as `ESC_ERA_LAW_of` (any endpoint in
  `ESC_TO_REGEN` form with β ≤ a yields the era law), applied to
  the Phase 29 endpoints (R ∈ {2, 4, 6, 8, 10}, via
  `ESC_ERA_LAW` itself) and the three new ones. β_next = 2β + 4
  now covers R ∈ {2, 4, 6, 8, 10, 12, 14} ∪ {2m + 16 : m ≤ 12} —
  every even R ≤ 40.
- **Fenced**: the second re-basing, R ≥ 42 — see “Remaining
  components” for the precise statement, obstruction and route.
  **(Phase 33: DONE for R ≤ 114 — Grind4.v, next section; the
  fence moves to R ≥ 116.)**

### Grind4.v — the second re-basing and the ESC-era law for R ≤ 114 (#19) — Phase 33

All section forms were pre-verified in an hstep-level simulator
mirroring Grind.v's 20 constructors exactly (validated against
the proved `hGRIND_dev` t = 0..3 chains, `REBASE_core` = 60
steps, `GG_clean` R₂ = 28 = 32,765 steps, `hGRIND` t = 12 at
a2 = 13 = 16,383 steps), and against `phase21_model.py` traces
of the re-based grind at R₂ ∈ {30, 32, 34, 40, 52, 64} (exactly
one PX2B deviation in each; min PUSH a = 3 in model coords).

- **`hGRIND_dev5` — PROVED**: the deviated grind at pb = [5],
  route (a) of the Phase 31 fence. Two-case landing:
  `hGRIND_dev5_0` (t = 0: the single `hPX2B5` step, landing
  `HB [0] 4 1 4 ((1, 1) :: (1, 2) :: (1, 2) :: P) G)`) and
  `hGRIND_dev5` (t ≥ 1: `hsteps (HC [5] t (2t+3) 2 P G)
  (HB [0] (t+4) 1 (2t+3) ((1, 2) :: (1, 2) :: (1, 2) :: P) G)`,
  strong induction mirroring `hGRIND_dev` — clean `hGRIND`
  loop at frame t − 1, spine the t − 1 instance at stack
  ((1, 2) :: P), closing POP consuming the head pair; step
  counts 2^{t+2} − 3, same as `hGRIND_dev`).
- **`round13_dev5` + `pop3_12` — PROVED**: round 13 of the
  re-based grind (TUP into the boundary grind + `hGRIND_dev5`
  13), and the three POPs absorbing the (1, 2) extras, landing
  `HB [0] 20 1 35 ((R₂ − 28, 2) :: P) G`.
- **`hGRIND_even` — PROVED**: the even-g0 grind
  `hsteps (HC pb (S a2) (2t+4) 2 P G)
  (HB pb a2 1 (2t+4) ((2, 2) :: P) G)` for t ≥ 1, t ≤ a2
  (PUSH + TDN + TUP, a loop of `hGRIND` i + TUP reaching
  g0 = 2t + 1 over the (2, 2) pair, spine `hGRIND` (t − 1)) —
  the phase-2 continuation at R₂ ≥ 32 (g0 = 34 at a2 = 20).
- **`rounds_from6` / `rounds_from4` — PROVED**: generalised
  round chains. `rounds_from6` iterates `grind_round` from
  shuttle 2j0 + 6 with an arbitrary residue g (GG_rounds fixes
  g = 2m + 2); `rounds_from4` iterates from shuttle 2j0 + 4
  with the **exact** floor j0 + m ≤ a2 (round j calls
  `hGRIND` j at frame a2) — phase 3 at a2 = 34 reaches
  R₃ ≤ 70.
- **Endpoints — PROVED**, in `ESC_TO_REGEN` form:
  `ESC_TO_REGEN_42` (the POP×3 landing is TAIL's source;
  pb = [21; 0], a = 35 + β); `ESC_TO_REGEN_44` (TUP +
  `hGRIND_even` 15 + `hTRANS2_2` + `pop_chain_h`;
  pb = [35; 20; 0], a = β + 2); `ESC_TO_REGEN_BIG2`
  (R = 2m + 46, m ≤ 34: even grind + `hTUP2_1` re-basing to
  pb = [20; 0], a2 = 34 + TDN + `rounds_from4` + `hTRANS2_1`
  + `pop_chain_h`; pb = [35; 20; 0], a = 2m + β + 4).
- **`ESC_ERA_LAW_33` — PROVED**: β_next = 2β + 4 for
  R = 42, R = 44 and R = 2m + 46 (m ≤ 34) — every even R
  with 42 ≤ R ≤ 114 — via `ESC_ERA_LAW_of`.
  **`ESC_ERA_LAW_114` — PROVED**: the combined law (Phase
  31's range together with Phase 33's): **every even
  R ≤ 114**.
- **Not threaded**: the new chains are proved at `hsteps`
  level only (no `hstepsP` versions). The era law does not
  need them — `grind_inv` threading was Phase 29's discharge
  of the Predecessor obligations for the chains those phases
  built; the Phase 33 chains are constructive `hstep`
  sequences, sound by `hstep_sound`.
- **Fenced**: the third re-basing, R ≥ 116 — see “Remaining
  components” for the precise statement, obstruction and
  route.

### Grind5.v — the third re-basing's dip bottoms and the [0] deviated grind — Phase 36

- **`PX2A0` — PROVED (Dev.v)**, for all parameters: with
  b = S (S (S (S (S b′′)))) (i.e. b ≥ 5),
  `run (b′′ + 37) (gcsec (false :: repeat true b ++ [false]) 0 3 2 P G)
  = Some (gbsec [false] 3 1 2 ((S b′′, 2) :: (1, 1) :: (1, 2) ::
  (1, 2) :: P) G)` — cost b + 32. Proof: `PX2A_chunkA` at
  p = 0 (the chunk is stated for general p) + `sweepF` +
  `PX2A0_tail`, a fixed 23-step computation (kernel-checked
  with symbolic b′′: the tail never reads more than the two
  exposed zeros of the swept region). Derived by zipper
  tracing; verified at b ∈ {5, 6, 7, 8, 10, 12, 16, 20, 24,
  30} and at stack/G variations — first landing at cost
  b + 32, no intermediate canonical section
  (`rocq/hsim36.py`). The small rows were also traced
  (not mechanised): b = 4 → cost 22, landing
  `HB [0] 3 1 2 ((1, 1) :: P) G`; b = 3 → cost 25, landing
  `HB [] 0 1 5 ((1, 1) :: (1, 2) :: (1, 2) :: P) G`.
- **`PX2B0` — PROVED (Dev.v)**, for all parameters:
  `run 20 (gcsec [false] 0 3 2 P G)
  = Some (gbsec [] 0 1 5 ((1, 2) :: P) G)`, by kernel
  computation; the following `hPOP` (13 steps) gives the
  PUSHX-shaped landing `HB [] 1 1 7 P G` — the same
  20 + 13 split as `PUSHX_core` + POP, over the [0]
  prefix instead of the empty one.
- **Word model (Grind.v)**: constructors **`hPX2A0`**
  and **`hPX2B0`** appended to `hstep`, with their
  `hstep_sound` cases (costs b′′ + 37 and 20);
  `pred_cases` is unchanged in content — both new targets
  are B-sections, so their inversion cases die by
  discrimination, as the rebuild confirms.
- **`hGRIND_dev0` — PROVED (Grind5.v)**: the deviated
  Grind Lemma G′ at the boundary frame a2 = t at
  pb = [0]: `HC [0] t (2t + 3) 2 P G` →
  `HB [] (S t) 1 (2t + 7) P G`. The proof is
  `hGRIND_dev`'s recursion verbatim (PUSH / TDN / TUP /
  clean-`hGRIND` loop at frame t − 1 / spine / closing
  POP) with base case `hPX2B0` + `hPOP`; pre-verified
  rule counts 2, 6, 14, 30, 62 = 2^(t + 2) − 2 at
  t = 0..4, exactly one PX2B0 and no PUSHX.
- **`PX2A0_dip34` — PROVED (Grind5.v)**: the Phase 33
  fence shape itself — `hPX2A0` at b′′ = 15 over the
  stack `repeat (1, 2) 34 ++ ((2, 2) :: Pe)`, landing
  `HB [0] 3 1 2 ((16, 2) :: (1, 1) :: (1, 2) :: (1, 2)
  :: (1, 2)^34 :: (2, 2) :: Pe) 1`. The dip bottom of
  the R = 116 boundary grind is no longer a dead end in
  the word model.
- **Not closed** (at Phase 36): the deviated grind at
  pb = [20; 0] (the phase-3 boundary grind itself) and
  the R ≥ 116 ESC-era law — **both closed in Phase 37**
  (Grind6.v, next section). Loop.v was unchanged in
  Phase 36: no H_LOOP instance was newly discharged.

### Grind6.v — the merged unwind and the ESC-era law to R ≤ 268 — Phase 37

- **`rounds_from4g` — PROVED**: phase-3/5 rounds with
  a general residue (grind_round j0 … j0 + m − 1,
  floors j0 + m ≤ a2, residue g ↦ g − 2m).
- **`pop_chain_h_app` — PROVED**: the POP chain over
  `repeat (1, 2) m ++ rest` with a carried rest
  (pop_chain_h is the rest = [] case).
- **`DEV20_step` / `DEV20_DESCEND` — PROVED**: the
  descent of the deviated grind at pb = [20; 0] to its
  dip bottom `HC [20; 0] 0 3 2 (repeat (1, 2) t ++ P) G`
  (one level = PUSH + TDN + TUP + the clean hGRIND
  loop, the first four blocks of hGRIND_dev0's S-case
  at pb = [20; 0]; then induction on t).
- **`GRIND16_A`…`GRIND16_E`, `GRIND16_MID` — PROVED**:
  the (16, 2) grind at ([0], 3) over an arbitrary
  carried rest: A = TUP + grind_prefix + clean rounds
  1–2; B = TUP + hGRIND_dev0 3 (the boundary round);
  C = TUP + PUSH + grind_prefix + clean rounds 1–2
  (the second G″ grind); D = TUP + hGRIND_dev 3;
  E = TUP2_1 + TDN; then TRANS2_1 over the spine head
  and pop_chain_h_app, landing
  `HB [14; 5] (n + 7) 1 (2n + 7) Rest 1` for spine
  length n.
- **`PHASE3_DEEP` — PROVED**: for R = 2m + 46,
  m ≥ 35, the ESC grind source reaches
  `HB [14; 5] 41 1 75 ((2m − 68, 2) :: Pe) 1`
  (BIG2's prefix, 34 phase-3 rounds via
  rounds_from4g, the final TUP, DEV20_DESCEND 34,
  hPX2A0, GRIND16_MID at spine 34).
- **`ESC_TO_REGEN_116` / `_118` / `_120` /
  `ESC_TO_REGEN_BIG3` — PROVED**: the endpoints at
  m = 35 (TAIL), m = 36 (TUP + hGRIND_even 35 +
  TRANS2_2 + pop_chain_h), m = 37 (TUP + hGRIND_even
  35 + TUP2_1 + TDN + TAIL) and 38 ≤ m ≤ 111
  (rounds at ([41; 14; 5], 74) + TUP + hGRIND
  (m − 38) + TAIL), each landing
  `HB pb a 1 (2β + 1) [] 1` with β ≤ a.
- **`ESC_ERA_LAW_37` / `ESC_ERA_LAW_268` — PROVED**:
  via ESC_ERA_LAW_of, the ESC-era law
  β_next = 2β + 4 for R ∈ {116, 118, 120} ∪
  {2m + 46 : 38 ≤ m ≤ 111}, and combined with
  ESC_ERA_LAW_114 for **every even R ≤ 268**.
- **Loop.v**: `ESC_ITER_268` / `ESC_ITER_268_step`
  discharge H_LOOP's ESC instances for
  116 ≤ R ≤ 268. **Fenced at Phase 37**: R ≥ 270
  (m ≥ 112) — phase 5's final grind becomes a
  boundary grind at pb = [41; 14; 5] (a phase-6
  deviation); **discharged in Phase 38** (Grind7.v
  below, `ESC_ITER_602` in Loop.v).

### Grind7.v — the phase-6 merged unwind and the ESC-era law to R ≤ 602 — Phase 38

The phase-6 boundary grind (final grind at
t = a2 = 74 over the passenger residue
((2m − 222, 2) :: Pe), pb = [41; 14; 5]) and its
continuation, assembled explicitly. Pre-verified
in `hsim38.py` (see the Phase 38 summary at the top
of this file).

- **`LOOPN` — PROVED** (new general tool): the
  truncated grind loop — cnt iterations of
  (hGRIND i + hTUP) from HC pb a2 (2i + 3) 2
  ((g, 2) :: P) to HC pb a2 (2(i + cnt) + 3) 2
  ((g − 2·cnt, 2) :: P), under i + cnt ≤ a2 and
  2·cnt + 1 ≤ g. The partial form of hGRIND's
  internal (local) countdown loop.
- **`DIPDESC` — PROVED** (new general tool): the
  boundary descent at t = a2 — for every t, every
  prefix pb and every stack P,
  HC pb t (2t + 3) 2 P → HC pb 0 3 2
  ((1, 2)^t ++ P), with **no floor hypothesis**.
  Proof: PUSH/TDN/TUP, LOOPN (t − 1) (the loop is
  frame-truncated by exactly the amount that
  grinds the pushed pair (2t − 1, 2) to (1, 2)),
  then the induction hypothesis at the next level.
  Sibling boundary forms: hGRIND (t + 1 ≤ a2,
  clean) and hGRIND_dev0 (pb = [0]).
- **`GRIND39_MID` — PROVED**: the continuation
  grind at ([5], 13), g0 = 39, over an arbitrary
  carried rest: HC [5] 13 39 2 ((1, 1) :: (1, 2)
  :: (1, 2) :: (1, 2)^n ++ Rest) →
  HB [19; 0] (36 + n) 1 (17 + 2n) Rest. Segments:
  PUSH/TDN/TUP, LOOPN 12, DIPDESC 12 (the
  segment's own dip at ([5], 0, 3)), hPX2B5,
  POP ×15 (one (1, 1) + pop_chain_h_app 14), hTUP,
  hGRIND_even 14, hTUP2_1, grind_prefix,
  grind_round 1, grind_round 2, POP ×4 and the
  spine pop_chain_h_app. Word boundaries verified
  at (n, β) ∈ {(0, 2), (2, 2), (3, 3)} (98,338
  rules at n = 0), word/machine boundary agreement
  at (0, 2) (1,180,078 machine steps).
- **`TAIL2` — PROVED**: the TRANS2_2 tail at a
  ((2, 2) :: (2, 2) :: Pe) section:
  HB pb a 1 (S s0) ((2, 2) :: (2, 2) :: Pe) →
  HB (S (S s0) :: S a :: pb) (β + 2) 1 (2β + 1) [].
- **`PHASE6_PREFIX` / `PHASE6_TO_MID` — PROVED**:
  the common chains. PHASE6_PREFIX (m ≥ 37):
  PHASE3_DEEP + TUP + hGRIND_even 35 + hTUP2_1 +
  hTDN → HB [41; 14; 5] 74 1 4 ((2m − 72, 2) :: Pe).
  PHASE6_TO_MID (m ≥ 112): + the maximal 74 clean
  rounds (rounds_from4g, floor met exactly), the
  final TUP, DIPDESC 74, hPX2A and GRIND39_MID →
  HB [19; 0] 110 1 165 ((2m − 222, 2) :: Pe).
- **Endpoints — PROVED**: `ESC_TO_REGEN_112`
  (m = 112: TAIL; pb = [111; 19; 0], a = 165 + β);
  `ESC_TO_REGEN_113` (m = 113: TUP + hGRIND_even
  80 + TAIL2; pb = [165; 110; 19; 0], a = β + 2);
  `ESC_TO_REGEN_114` (m = 114: TUP + hGRIND_even
  80 + hTUP2_1 + hTDN + TAIL; a = 4 + β);
  `ESC_TO_REGEN_BIG6` (115 ≤ m ≤ 278: + rounds at
  ([110; 19; 0], 164), count m − 115, a final
  hGRIND (m − 115) and TAIL; a = 2m − 224 + β).
- **`ESC_ERA_LAW_38` / `ESC_ERA_LAW_602` —
  PROVED**: via ESC_ERA_LAW_of, the ESC-era law
  β_next = 2β + 4 for R ∈ {270, 272, 274} ∪
  {2m + 46 : 115 ≤ m ≤ 278}, and combined with
  ESC_ERA_LAW_268 for **every even R ≤ 602**.
- **Loop.v**: `ESC_ITER_602` / `ESC_ITER_602_step`
  discharge H_LOOP's ESC instances for
  270 ≤ R ≤ 602. **Fenced**: R ≥ 604 (m ≥ 279) —
  at the new frame ([110; 19; 0], 164) the rounds
  (count m − 115 ≤ 164) and the final grind
  (t = m − 115, floor t + 1 ≤ 164) both bind; the
  final grind at t = a2 would again be a DIPDESC
  descent whose dip at [110; 19; 0] fires hPX2A
  into a phase-7 continuation (the same proof
  pattern one level deeper; not a uniform
  induction — see the general-induction verdict in
  the Phase 38 summary at the top of this file).

### Grind8.v — the phase-7 merged unwind and the ESC-era law to R ≤ 1276 — Phase 40

The Phase 38 fence (m ≥ 279) mechanised by the same merged-unwind
pattern as Phases 37–38. Pre-verification: `rocq/hsim40.py` (the
hPX2A dispatch at the phase-7 dip shape, DIPDESC at [110; 19; 0],
GRIND108 stages A and B as primitive word walks at the real
parameters — 1,048,574 and 1,048,575 word rules — stage C at the
real frame ([19], 41) with a shrunk passenger, the whole parse at
two shrunk analogues (a2, g0) ∈ {(6, 36), (8, 48)} with
word/machine boundary agreement, and shrunk analogues of all
four finishes: ALL CHECKS PASS).

- **`GRIND108_MID` — PROVED**: the continuation grind at
  ([0], 18), g0 = 108, over an arbitrary carried rest:
  HC [0] 18 108 2 ((1, 1) :: (1, 2) :: (1, 2) :: (1, 2)^n ++ Rest)
  ⇢ HB [42; 19] (71 + n) 1 (7 + 2n) Rest. Stage A: PUSH/TDN/TUP,
  LOOPN 17 (floor-exact), DIPDESC 17, hPX2B0, POP ×18, TUP.
  Stage B (the boundary even grind at pb = [], g0 = 40 =
  2·18 + 4): PUSH/TDN/TUP, LOOPN 17 (floor-exact, (36, 2) → (2, 2)),
  PUSH/TDN/TUP, LOOPN 16 (floor-exact, (33, 2) → (1, 2)),
  DIPDESC 16, hPUSHX, POP ×17, hTUP2_1 onto ([19], 41), TDN, TUP.
  Stage C: LOOPN 31, PUSH/TDN/TUP, LOOPN 30, hGRIND 30, POP,
  hTRANS2_1, spine POP chain.
- **`PHASE7_TRANS19` / `PHASE7_TRANS42` — PROVED**: the
  transitional segments (TUP + hGRIND_even + hTUP2_1 + hTDN),
  residue-general (r ≥ 6), onto frames ([110; 19; 0], 164) and
  ([235; 42; 19], 334) respectively.
- **`PHASE7_TO_MID` — PROVED** (m ≥ 279): PHASE6_TO_MID +
  PHASE7_TRANS19 + 164 clean rounds (rounds_from4g, count
  exactly the frame) + final TUP + DIPDESC 164 + hPX2A +
  GRIND108_MID, landing at HB [42; 19] 235 1 335 over the
  passenger ((2m − 556, 2) :: Pe).
- **Endpoints — PROVED**: `ESC_TO_REGEN_604` (m = 279: TAIL;
  pb = [236; 42; 19], a = 335 + β); `ESC_TO_REGEN_606`
  (m = 280: TUP + hGRIND_even 165 + TAIL2; pb = [335; 235; 42; 19],
  a = β + 2); `ESC_TO_REGEN_608` (m = 281: PHASE7_TRANS42 + TAIL;
  a = 4 + β); `ESC_TO_REGEN_BIG7` (282 ≤ m ≤ 615: + rounds at
  ([235; 42; 19], 334), count m − 282, a final hGRIND (m − 282)
  and TAIL; a = 2m − 558 + β).
- **`ESC_ERA_LAW_40` / `ESC_ERA_LAW_1276` — PROVED**: via
  ESC_ERA_LAW_of, the ESC-era law β_next = 2β + 4 for
  R ∈ {604, 606, 608} ∪ {2m + 46 : 282 ≤ m ≤ 615}, and combined
  with ESC_ERA_LAW_602 for **every even R ≤ 1276**.
- **Loop.v**: `ESC_ITER_1276` / `ESC_ITER_1276_step` discharge
  H_LOOP's ESC instances for 604 ≤ R ≤ 1276. **Fenced**:
  R ≥ 1278 (m ≥ 616) — at the new frame ([235; 42; 19], 334)
  the rounds (count m − 282 ≤ 334) and the final grind
  (t = m − 282, floor t + 1 ≤ 334) both bind; the final grind
  at t = a2 would again be a DIPDESC descent whose dip at
  [235; 42; 19] fires hPX2A into a phase-8 continuation (the
  same finite-extension pattern one level deeper; Phase 38's
  general-induction verdict stands).

### Grind9.v — the phase-8 entry, stages A–C, and the cascade fence — Phase 41

- **Dev.v** (493 lines): `PX2Bgen` — the PX2B dispatch at a
  single-block prefix [b], b ≥ 5, a uniform family with the
  PX2A0 landing shape at cost b + 32 (chunk `PX2Bgen_chunk`,
  12 steps; `sweepF`; tail `PX2Bgen_tail`, 23 steps;
  b = b′′ + 5, cost b′′ + 37). The small blocks b = 2, 3, 4
  remain the accident chunks hPX2B2/3/4 (costs 28, 25, 22 in
  other shapes); b = 5, 6 agree with the family modulo the
  extra steps already packaged in hPX2B5/hPX2B6.
- **Grind.v** (461 lines): constructor `hPX2Bgen` + its
  `hstep_sound` case (cost b′′ + 37). `pred_cases` is
  unaffected (the new target is a B-section; the case falls
  by discrimination, as hPX2A0's did in Phase 36).
- **Grind9.v** (502 lines): `DIPDESC_even` (the even
  boundary descent at g0 = 2t + 4, general in t, pb, P, G);
  `PHASE8_TO_MID` (the phase-8 funnel, m ≥ 616);
  `PHASE8_STAGE_A` / `PHASE8_STAGE_B` / `PHASE8_STAGE_C`
  (the continuation's first three stages, each over an
  arbitrary carried rest); `PHASE8_TO_STAGE_D` (the
  composition — the mechanised phase-8 frontier at
  HC [5] 13 1 2 over (1, 2) :: (1, 1) :: R2, with R2 the
  explicit carried stack of the header narrative).
  **Fenced**: everything past that frontier — the
  continuation cascade consumes the whole passenger stack
  and leaves the section grammar (word walk stuck at a
  B-section over the empty stack; see the Phase 41
  narrative). No ESC-era-law extension, no new Loop.v
  discharge: the era law stays at R ≤ 1276. **(Phase 42
  corrects the reading of that fence — the terminal
  B-section over the empty stack IS the era-landing
  shape — and reduces the closure to the single
  statement CASCADE_LANDING; see the Grind10.v section
  below and the Phase 42 narrative at the top.)**

### Grind10.v — the cascade landing: correction, reduction, fenced core — Phase 42

- **`CASCADE_STAGE4` — PROVED**: the cascade's rounds
  stage in general: for m + 1 ≤ a,
  `hsteps (HC pb a 1 2 ((2m + 4, 2) :: P) 1)
  (HB pb a 1 (2m + 6) ((2, 2) :: P) 1)` — TDN + TUP +
  `hGRIND 0` + `GG_rounds` (Grind2.v). At the hsim41/42
  base analogue this is the stage
  HC [26; 25; 24; 5] 12 1 2 ((22, 2) :: …) →
  HB … 1 24 ((2, 2) :: …) (m = 9, floor 10 ≤ 12).
- **`CASCADE_POPFIN` — PROVED**: the cascade's final POP
  chain in era form: for 1 ≤ b,
  `hsteps (HB pb a 1 3 (repeat (1, 2) (b − 1)) 1)
  (HB pb (a + b − 1) 1 (2b + 1) [] 1)` — Grind6's
  `pop_chain_h_app` at s = 3. Every completed hsim42
  walk ends with a frame-growth step onto the rounds
  stage's source followed by this chain.
- **`CASCADE_LANDING` — the remaining core (a
  Definition, hypothesis-style)**: for every M ≥ 616
  and β ≥ 2, the stage-D source of
  `PHASE8_TO_STAGE_D` reaches `HB pb a 1 (2β + 1) [] 1`
  for some pb, a with β ≤ a. Stress-tested in
  `rocq/hsim42.py` (~50 shrunk-family landings, the
  odd-residue parity fence s = 2b + r2, machine REGEN
  at the terminal; growth probes CAP, never stuck).
  Its stages 1–3 have parameter-dependent parses
  (frame-growth count 2..6 across the sweep; the
  binding floor is inside the segment grinds), so a
  proof needs a totality theorem for the segment grind
  at g0 = 1 over an arbitrary deeper tail with
  existential frame/shuttle values — the grind
  analogue of `DIPDESC` for the g0 = 1 regime.
- **`ESC_TO_REGEN_BIG8_of` / `ESC_ERA_LAW_42` —
  PROVED modulo CASCADE_LANDING**: the phase-8 era
  law (β ↦ 2β + 4 at `esc_src (2M + 52) (β − 2)`) by
  `PHASE7_TO_MID` (all m ≥ 279 covers M ≥ 616) +
  `PHASE8_TO_STAGE_D` + the cascade + `ESC_ERA_LAW_of`
  (Grind3.v). Loop.v's `ESC_ITER_BIG8` /
  `ESC_ITER_BIG8_step` (Part 4c) discharge H_LOOP's
  ESC instances at every even R ≥ 1278 modulo the
  same parameter.

### Grind11.v — the cascade's stages 1–3, and the stage-4 core — Phase 43

- **`GG_odd` / `GG_rounds_odd` — PROVED**: the g0 = 1
  totality for odd residue pairs. `GG_rounds_odd` grinds
  `(2m + 1, 2)` to a `(1, 2)` head by induction on m over
  `Grind2.grind_round` (floor j0 + m + 1 ≤ a2);
  `GG_odd` = `grind_prefix` + `GG_rounds_odd`:
  `hsteps (HC pb a2 1 2 ((2*m + 3, 2) :: P) G)
  (HB pb a2 1 (2*m + 6) ((1, 2) :: P) G)` under the floor
  m + 1 ≤ a2, over an arbitrary frame pb and tail P.
  (Helper: `pop12`, POP chains over (1, 2)-spines.)
- **`CASCADE_STAGE1` — PROVED** (parity-free): TDN +
  POP (1, 2) + POP (1, 1) + `pop12` over the first
  spine + TUP + `hGRIND_even (n1 + 3)` + `hTUP2_1`:
  the stage-D stack at spine length n1 + 2 and residue
  r1 ≥ 5 reaches `HC [n1 + 17; 5] (2*n1 + 10) 1 2
  ((r1 − 4, 2) :: (1, 1) :: Tail)`.
- **`CASCADE_STAGE23` — PROVED**: the merged stages
  2+3 in the era (odd-r1) regime: `GG_odd` on
  (2*m1 + 3, 2) + POPs + `pop12` over the second spine
  + TUP on (r2, 2) + `hGRIND_even (m1 + n2 + 4)` +
  `hTUP2_1`, landing at the stage-4 source
  `HC (A1 + n2 + 4 :: x :: pb) (2*m1 + 2*n2 + 12) 1 2
  ((r2 − 4, 2) :: (1, 1) :: Tail)`, for r2 ≥ 6 under
  the single floor m1 + 1 ≤ A1 (both internal floors
  coincide; M-independent). Branches
  **`CASCADE_STAGE23_r2_4`** (r2 = 4: `hTRANS2_2`
  dispatch, landing on the POPFIN source at counter 3)
  and **`CASCADE_STAGE23_r2_2`** (r2 = 2: `hTRANS2_1`
  dispatch on the residue pair itself) — PROVED.
  All boundary formulas pre-verified in
  `rocq/hsim43.py` (ALL PHASE 43 CHECKS PASS: six
  generic odd-r1 points with every intermediate
  boundary asserted, both dispatch branches, two
  stage-4 boundary points, the M = 618 stage-4 branch).
- **`CASCADE_STAGE4_BIG` — the residual core (a
  Definition, hypothesis-style)**: for every M ≥ 1441
  and β ≥ 2, the stage-4 source
  `HC [428; 57; 5] 822 1 2 ((2*M − 1234, 2) :: (1, 1) ::
  repeat (1, 2) (β − 1)) 1` reaches
  `HB pb a 1 (2β + 1) [] 1` for some pb, a with β ≤ a.
  The boundary regime's mechanism (grind rounds hit
  j = a; DIPDESC / PX2A re-basings regenerate the
  budget) is documented in the file header and
  evidenced in hsim43; a proof needs a dip-aware
  totality for the rounds grind at this one frame.
- **`CASCADE_LANDING_of` — PROVED**:
  CASCADE_STAGE4_BIG → CASCADE_LANDING, by the
  five-way stage-4 dispatch (M = 616 / 617 branches,
  M = 618 degeneration, 619 ≤ M ≤ 1440 clean stage 4,
  M ≥ 1441 the core). **`ESC_ERA_LAW_43` — PROVED
  modulo CASCADE_STAGE4_BIG** (via ESC_ERA_LAW_42).
  Loop.v's `ESC_ITER_BIG8_43` / `ESC_ITER_BIG8_43_step`
  (Part 4d) discharge H_LOOP's ESC instances at every
  even R ≥ 1278 modulo CASCADE_STAGE4_BIG.

### Grind12.v — the stage-4 boundary grind, and the tail core — Phase 44

- **`GG_boundary` — PROVED** (the phase's core totality):
  the boundary grind of the pair (2m + 4, 2) at counter
  a ≤ m, frame- and rest-general:
  `hsteps (HC pb a 1 2 ((2*m + 4, 2) :: w) G)
  (HC pb 0 3 2 (repeat (1, 2) a ++ ((2*(m − a) + 2, 2) :: w)) G)`.
  Proof: TDN + TUP + `hGRIND` 0 + **`GG_rounds_part`**
  (a − 1 clean rounds; GG_rounds with the endpoint left
  symbolic) + TUP + `DIPDESC` a — the last round
  dispatches through the dip exactly when the counter
  budget j = a is exhausted. This is the dip-aware
  rounds totality the Phase 43 core statement called
  for.
- **`STAGE4_SEG1` / `STAGE4_SEG2` — PROVED**: SEG1 =
  GG_boundary at [f; p; 5] + `hPX2A`, landing at
  `HC [5] (p − 1) (f − 2) 2 (S1s a m b)`; SEG2 = `hPUSH`
  + GG_boundary at [5] (counter p − 2, pair
  (2·mp + 4, 2)) + `hPX2B5`, landing at
  `HB [0] 4 1 4 (S2s mp p a m b)`.
- **`STAGE4_T1` / `STAGE4_T2` — PROVED**: T1 = POP (1, 1)
  + `pop12` p + `hTUP` + `hGRIND_even` p, landing at
  `HB [0] (p + 4) 1 (2p + 4) ((2, 2) :: (g2 − 2, 2) :: S1s)`
  with g2 = 2(mp − p + 2) + 2; T2 = one `hTUP2_1` step
  onto [p + 5; 0], the pair becoming (2·m3 + 4, 2),
  m3 = mp − p − 1 (domain p ≥ 2, mp ≥ p + 1).
- **`STAGE4_T3` — PROVED** (era regime 2p + 4 ≤ m3):
  GG_boundary at counter 2p + 4 + `hPX2A0`, landing at
  `HB [0] 3 1 2 ((p + 1, 2) :: R3s p m3 a m b)`.
- **`STAGE4_T4` — PROVED** (p = 2q + 1, q ≥ 5): `hTUP` +
  `grind_prefix` + `GG_rounds_part` 2 + `hTUP` +
  `DIPDESC` 3 + `hPX2B0`, landing at
  `HB [] 0 1 5 (S4s q m3 a m b)` — the bottom frame.
- **`CASCADE_STAGE4_TAIL` (Definition)**: the residual
  core — the tail traversal
  `HB [] 0 1 5 (TAILs q v3 vM a b) 1` →
  `HB pb A 1 (2b + 1) [] 1` with b ≤ A, for q ≥ 5,
  b ≥ 2. Strictly smaller than CASCADE_STAGE4_BIG:
  bottom frame, era parities baked in, parameters the
  tail's own.
- **`CASCADE_STAGE4_BIG_of` — PROVED**:
  CASCADE_STAGE4_BIG modulo CASCADE_STAGE4_TAIL (the
  composition SEG1 + SEG2 + T1 + T2 + T3 + T4 at the era
  point, closed by `S4s_era`).
- **`ESC_ERA_LAW_44` — PROVED**: the phase-8 era law
  (β ↦ 2β + 4 at every even R ≥ 1278) modulo
  CASCADE_STAGE4_TAIL, via ESC_ERA_LAW_43 ∘
  CASCADE_STAGE4_BIG_of.
- Evidence: `rocq/hsim44.py` (ALL PHASE 44 CHECKS PASS —
  segment boundaries asserted verbatim at nine stage-4
  points, five T4-source points, one growth probe; all
  walks over proved constructors only, all landings the
  era shape).

### Grind13.v — the stage-4 tail at the era slice, and the TAIL2_BIG core — Phase 45

- **`TAIL_LAYER0` / `TAIL_LAYER1` — PROVED**: the tail's
  layers 0–1 at the era slice (q, v3, a) = (28, 34, 822)
  — the only instantiation of CASCADE_STAGE4_TAIL the
  development uses — symbolic in (v3, vM, a, β) resp.
  (vM, β), landing on the layer-2 residue state
  `HB [243; 135; 35; 20; 0] 893 1 1651
  ((2·vM + 2, 2) :: (1, 1) :: (1, 2)^(β − 1))`.
- **`TAIL2_CLEAN` — PROVED**: the layer-2 residue in the
  clean range vM ≤ 1652 (four dispatches; final counters
  β + 1651 / β + 2 / β + 4 / 2·vM + β).
- **`TAIL2_BIG` (Definition)**: the residual core after
  Phase 45 — the layer-2 residue totality at the residue
  state, vM ≥ 1653 only (the boundary regime).
- **`TAIL_ERA_of` / `CASCADE_STAGE4_BIG_45` /
  `ESC_ERA_LAW_45` — PROVED**: the era law at every even
  R ≥ 1278 modulo TAIL2_BIG.
- Evidence: `rocq/hsim45.py` (ALL PHASE 45 CHECKS PASS).

### Grind14.v — the TAIL2_BIG descent, and the TAIL2_END core — Phase 46

- **`DIPGRIND` — PROVED** (the phase's core totality):
  the boundary rounds at a general counter,
  `hsteps (HC pb A 3 2 ((2 * A + r, 2) :: w) G)
  (HC pb 0 3 2 (repeat (1, 2) A ++ ((r, 2) :: w)) G)`
  for 1 ≤ A, 1 ≤ r. Proof: `hGRIND` 0 +
  `GG_rounds_part` (A − 1) + TUP + `DIPDESC` A.
- **`CLEANG_odd` / `CLEANG_even` — PROVED**: the clean
  grinds at counter 3 of an odd pair (2m + 3, 2)
  (floor m + 2 ≤ a2; closes at (1, 2), shuttle 2m + 8)
  and of an even pair (2m + 2, 2) (floor m + 1 ≤ a2;
  closes at (2, 2), shuttle 2m + 6).
- **`TAIL2_FRONT` — PROVED**: the TAIL2_BIG source
  reaches the PX2A landing `px(k, β)`,
  k = vM − 1652 (TUP + `hGRIND_even` 823 + TUP2_1 +
  `GG_boundary` (1650, vM − 3) + PX2A).
- **`DESCENT46` — PROVED**: the descent from
  `px(k, β)` to the END state
  `HB [317; 40; 14; 5] 2204 1 3711
  ((2k, 2) :: (1, 1) :: (1, 2)^(β − 1))` as one hsteps
  chain, uniform in (k, β) with no side conditions:
  DIPGRIND at (241, 405), (33, 63), (3, 6), (3, 2);
  PX2A / PX2A0 / PX2B0 / PUSHX dip exits; regrowth to
  [317; 40; 14; 5]; CLEANG_odd at the (57, 2) and
  (399, 2) pairs.
- **`END46_1` / `END46_2` / `END46_3` / `END46_big` —
  PROVED**: the END state closes for k = 1 (A =
  3711 + β), k = 2 (A = β + 2), k = 3 (A = β + 4) and
  4 ≤ k ≤ 3713 (A = 2k + β − 2; the last segment is
  CLEANG_even at counter 3710, floor 2k − 6 ≤ 2·3710).
- **`TAIL2_END` (Definition)**: the residual core —
  the END totality for k ≥ 3714 alone.
- **`TAIL2_BIG_of` — PROVED**: Grind13's TAIL2_BIG
  modulo TAIL2_END; the k ≤ 3713 range is discharged
  outright, so TAIL2_BIG is proved for
  1653 ≤ vM ≤ 5365.
- **`ESC_ERA_LAW_46` — PROVED**: the phase-8 era law
  (β ↦ 2β + 4 at every even R ≥ 1278) modulo
  TAIL2_END, via ESC_ERA_LAW_45 ∘ TAIL2_BIG_of.
- Evidence: `rocq/hsim46.py` (ALL PHASE 46 CHECKS
  PASS — 51 descent waypoints asserted verbatim at
  six k-values × β ∈ {2, 3}; END parses/finals for
  k ≤ 3713; full source walks for vM ≤ 5365; the
  k ≥ 3714 fence finals at k = 3714 / 5000).

### Loop.v — the cross-era loop assembly — Phase 32

The ascending loop of `168016-proof.md` §4, composed from the
proved components. Entry sections are `entry_sec P beta` :=
`rcsec P (beta − 2) [(1, 2)]`; a `loop_step P beta` is a
positive-length run from `entry_sec P beta` to cfg_sim of
`entry_sec P' beta'` with beta < beta' (hence strictly larger
span: the entry section's β block has length beta).

- **`PASS` — PROVED**: the exit + stage 1 + stage 2 for an
  **arbitrary** frozen prefix P: `STAGE1_exit` (Recoord.v)
  composed with `DSTAGE2` (DiagPass.v) via `run_sim_transfer`:
  run ((Tk K + 6) + (2K² + 13K + 14) + Tk K) from
  `rcsec P K [(1, 2)]` reaches cfg_sim of the escape section
  `rcsec P 0 ((3, 2) :: repeat (1, 2) K)`, for every K ≥ 2.
- **`esc_bridge` — PROVED (definitional)**: over a single-block
  prefix the escape section is *equal* to Esc.v's `esc_src`:
  `rcsec (false :: repeat true L) 0 ((3, 2) :: repeat (1, 2) m)
  = esc_src L m` (both are `mkCfg SC (0 :: 1^L)
  (1 1 0³ 1² (0 1²)^m)`; the rcsec form's leading 1 1 is the
  β block's last two cells). So the ESC era law applies to
  PASS's landing with no further step list.
- **`SETTLED_ITER` — PROVED**: one settled iteration at the
  trajectory prefix: from `entry_sec (entryP 31) (n + 2)`
  (n ≥ 2), RECOORD2_uncond (at B2 = 31, via `sim_entry`) +
  ERA_LAW (at era parameter n + 2) reach cfg_sim of
  `entry_sec (false :: repeat true (n + 19)) (2n + 38)` —
  β ↦ 2β + 34, and the next entry prefix is the single block
  0 1^{n+19}. `SETTLED_ITER_step` packages it as a loop_step.
- **`ERA_GEN` (explicit hypothesis, a Definition)**: the
  general-residue era law in ERA_LAW's shape: for every
  residue ρ and era parameter m ≥ 1, some cost reaches
  cfg_sim of `rcsec P' (rho + 2m + 3) [(1, 2)]` from
  `csec 16 rho 2 ((1, 1) :: repeat (1, 2) (m − 1)) 1`
  (human form, phase19 §2: s₁ = ρ + 2β_E + 2,
  β′ = ρ + 2β_E + 5). `ERA_LAW_GEN` proves the ρ = 29
  instance is ERA_LAW itself. **(Phase 35: PROVED on its
  domain** — odd ρ ≤ 33 — as `ERA_GEN_proved` in EraGen.v;
  the Definition stays as the hypothesis of the conditional
  iteration below, for the residues outside the domain.)
- **`SETTLED_ITER_GEN` — PROVED modulo ERA_GEN**: one settled
  iteration at a general two-block prefix entryP B2
  (B2 ≥ 3): β = n + 2 ↦ β′ = B2 + 2n + 7
  (= ρ + 2β_E + 5 at ρ = B2 − 2). `SETTLED_ITER_GEN_step`
  packages it as a loop_step.
- **`SETTLED_ITER_GEN_odd` — PROVED (Phase 35)**: the same
  iteration with ERA_GEN discharged via `ERA_GEN_proved`:
  unconditional for **odd B2 with 3 ≤ B2 ≤ 35**
  (ρ = B2 − 2 odd, ≤ 33). `SETTLED_ITER_GEN_odd_step`
  packages it as a loop_step.
- **`SETTLED_ITER_GEN_even` — PROVED (Phase 39)**: the same
  iteration at an **even** prefix, via EraEven.v's
  `ERA_GEN_even`: unconditional for **even B2 with
  4 ≤ B2 ≤ 36** (ρ = B2 − 2 = 2k + 2, k ≤ 16). The landing
  differs in shape: β = n + 2 ↦ **β′ = 2n + 8 = 2β + 4**,
  independent of B2 (the rotation puts ρ into the frame,
  not the shuttle). `SETTLED_ITER_GEN_even_step` packages
  it as a loop_step. With the odd case, the settled
  iteration is unconditional for **every 3 ≤ B2 ≤ 36**;
  only B2 ≥ 37 remains on the conditional form above.
- **`ESC_ITER` — PROVED**: one ESC iteration at a
  single-block prefix 0 1^{R+6}: PASS + `esc_bridge` +
  `ESC_ERA_LAW_31` (Grind3.v) reach cfg_sim of an entry
  section with β′ = 2β + 4 and prefix an ESC landing form
  `false :: repeat true (S a) ++ enc pb` with a ≥ β, for
  β ≥ 4 and R in ESC_ERA_LAW_31's range (every even
  R ≤ 40). `ESC_ITER_step` packages it as a loop_step.
- **`ESC_ITER_BIG8` — PROVED modulo CASCADE_LANDING
  (Phase 42)**: one ESC iteration at a single-block
  prefix 0 1^{2M + 52} for every M ≥ 616 (i.e. every
  even R = 2M + 46 ≥ 1278): PASS + `esc_bridge` +
  `ESC_ERA_LAW_42` (Grind10.v) reach cfg_sim of an
  entry section with β′ = 2β + 4, for β ≥ 4.
  `ESC_ITER_BIG8_step` packages it as a loop_step.
  With `ESC_ITER_1276`, every even R is covered —
  unconditionally for R ≤ 1276, modulo the single
  named statement CASCADE_LANDING above it.
- **`TWO_ITERS` — PROVED**: the first two iterations composed
  from the entry landing `entry_tgt 30 n`, for n = 2j + 3
  with j ≤ 12 (iteration 2's residue is R = n + 13 = 2j + 16
  ≤ 40): β = n + 2 ↦ 2n + 38 ↦ **4n + 80**, a single run
  from `entry_tgt 30 n` to cfg_sim of an entry section with
  β = 4n + 80.
- **`loop_chain` / `LOOP_NONHALT` — PROVED**: the abstract
  ascending-loop engine. Given `loop_step` at every entry
  section with β ≥ 4, chains of iterations reach entry
  sections at strictly increasing times (`loop_chain`), so
  the run from any entry section is defined at every length
  N (`LOOP_NONHALT`) — the fuel-based non-halting statement.
- **`NONHALT_FROM_R` — PROVED modulo two explicit
  hypotheses** (lemma parameters, not axioms): from
  `cfg_R`, if **(H_STD)** some run from the first I-section
  `cfg_Isec` reaches cfg_sim of an entry landing
  `entry_tgt (B2 − 1) n` with B2 ≥ 3, n ≥ 2, and
  **(H_LOOP)** `loop_step` holds at every entry section
  with β ≥ 4, then the run from `cfg_R` is total. The
  formation link R → cfg_Isec (150 steps) is
  kernel-verified (Finite.v's `R_reaches_Isec`) and is used
  unconditionally. H_LOOP's discharged instances are
  SETTLED_ITER (B2 = 31), SETTLED_ITER_GEN (general B2,
  modulo ERA_GEN; discharged for odd B2 ≤ 35 by
  SETTLED_ITER_GEN_odd, Phase 35, and for even
  4 ≤ B2 ≤ 36 by SETTLED_ITER_GEN_even, Phase 39 — i.e.
  for every 3 ≤ B2 ≤ 36), ESC_ITER (R ≤ 40) and
  — Phase 33 — **`ESC_ITER_114`** (PASS + `esc_bridge` +
  `ESC_ERA_LAW_114` of Grind4.v: β ↦ 2β + 4 for every even
  R ≤ 114; `ESC_ITER_114_step` packages it as a loop_step)
  and — Phase 37 — **`ESC_ITER_268`** (via
  `ESC_ERA_LAW_268` of Grind6.v: β ↦ 2β + 4 for every even
  R ≤ 268; `ESC_ITER_268_step` packages it as a loop_step)
  and — Phase 38 — **`ESC_ITER_602`** (via
  `ESC_ERA_LAW_602` of Grind7.v: β ↦ 2β + 4 for every even
  R ≤ 602; `ESC_ITER_602_step` packages it as a loop_step)
  and — Phase 40 — **`ESC_ITER_1276`** (via
  `ESC_ERA_LAW_1276` of Grind8.v: β ↦ 2β + 4 for every even
  R ≤ 1276; `ESC_ITER_1276_step` packages it as a loop_step)
  and — Phase 42 — **`ESC_ITER_BIG8`** (via
  `ESC_ERA_LAW_42` of Grind10.v: β ↦ 2β + 4 for every even
  R ≥ 1278, modulo CASCADE_LANDING; `ESC_ITER_BIG8_step`
  packages it as a loop_step)
  and — Phase 43 — **`ESC_ITER_BIG8_43`** (via
  `ESC_ERA_LAW_43` of Grind11.v: β ↦ 2β + 4 for every even
  R ≥ 1278, modulo CASCADE_STAGE4_BIG only;
  `ESC_ITER_BIG8_43_step` packages it as a loop_step)
  and — Phase 44 — **`ESC_ITER_BIG8_44`** (via
  `ESC_ERA_LAW_44` of Grind12.v: β ↦ 2β + 4 for every even
  R ≥ 1278, modulo CASCADE_STAGE4_TAIL only;
  `ESC_ITER_BIG8_44_step` packages it as a loop_step);
  its undischarged instances are exactly the ESC entries
  at R ≥ 1278 modulo CASCADE_STAGE4_TAIL (the phase-8
  cascade past stage D: entry and stages A–C mechanised
  in Grind9.v, Phase 41; the landing's last two stages
  and the whole reduction proved in Grind10.v, Phase 42;
  the cascade's stages 1–3 proved in the era regime and
  the landing reduced to the stage-4 boundary grind in
  Grind11.v, Phase 43; the stage-4 grind's segments
  mechanised and the core reduced to the bottom-frame
  tail in Grind12.v, Phase 44 — see the Grind12.v
  section),
  the settled entries at B2 ≥ 37 (residues beyond the
  frame-16 era laws of both parities, fenced in
  EraGen.v / EraEven.v),
  and the entry sections over ESC landing prefixes
  (iterations ≥ 3). H_STD is component #10's remaining
  assembly (see the table) plus the #11 exit dichotomy,
  human-proved but not mechanised.
  **(Phase 34: H_STD is DISCHARGED — see the Std.v section
  below; `NONHALT_FROM_R_std` in Std.v is this assembly
  with only H_LOOP remaining.)**

### Std.v — the standard-regime assembly (H_STD discharged) — Phase 34

The totality of the standard regime from the first I-section,
as one word-model chain at the trajectory's frozen prefix
pb = [17] (see the Phase 34 summary at the top of this file
for the identifications and the pre-verification).

- **`STD_cycle` — PROVED**: one grind/collapse cycle:
  `hsteps (HC pb A (2t + 3) 2 [] G) (HC pb A (2t + 5) 2 [] (G − 2))`
  for t + 1 ≤ A and G ≥ 3 — `hGRIND t` (Grind2.v) followed by
  `hSTGA` (Grind.v). The four bounce rules inside the grind
  preserve G; Stage A sends G ↦ G − 2 (component #11's
  bookkeeping, at chain level).
- **`STD_cycles` — PROVED**: k cycles iterated (induction on
  k): G = 2k + 2 descends to G = 2, the grind parameter
  rising t ↦ t + k, under the accumulated floor t + k + 1 ≤ A.
- **`STD_reach_entry` — PROVED**: the regime totality in
  general form: from any C-section `HC pb A 1 2 [] (2k + 6)`
  (g0 = 1, s = 2, w = [1], even G = 2k + 6 ≥ 6) with
  k + 2 ≤ A, the chain `hTDN` + `hSTGA` + (k + 1) cycles +
  final `hGRIND (k + 1)` reaches `HB pb A 1 (2k + 8) [] 2` —
  the w = [1] B-section at G = 2, i.e. the #11 exit. This is
  the exit branch of the dichotomy; the "runs forever"
  branch cannot occur for an empty-stack section, since
  every grind terminates (hGRIND is a proved chain) and G
  strictly decreases at every collapse.
- **`STD_chain` — PROVED**: the trajectory instance
  (k = 64): `hsteps (HC [17] 95 1 2 [] 134)
  (HB [17] 95 1 136 [] 2)` — 66 Stage A collapses, floors
  66 ≤ 95.
- **`Isec_hcfg` / `final_entry_src` — PROVED (definitional)**:
  `cfg_Isec = hcfg (HC [17] 95 1 2 [] 134)` and
  `hcfg (HB [17] 95 1 136 [] 2) = entry_src 95 136`, both by
  `reflexivity`.
- **`H_STD_proved` — PROVED**: `hsteps_sound` on `STD_chain`,
  transported through the two identifications and closed by
  Mirror.v's `ENTRY` (148 = 136 + 12 steps): some run from
  `cfg_Isec` reaches `entry_tgt 95 136` exactly — H_STD's
  existential with (B2, n) = (96, 136).
- **`NONHALT_FROM_R_std` — PROVED**: `NONHALT_FROM_R` with
  its first hypothesis replaced by `H_STD_proved`; the
  headline assembly now has the single hypothesis H_LOOP.
  `Print Assumptions` on all eight Std.v headlines:
  **“Closed under the global context.”**

## Component-by-component status (table of `168016-proof.md` §1)

| # | Component | Mechanisation status |
|---|---|---|
| 1 | First family S (arrivals, period law) | **Finite instances proved** (blank→S(2), S(2)→S(4), Finite.v). General S(k) induction **not started**. |
| 2 | The k = 56 break | **Not started** (finite but ≈3.2×10⁹ steps to S(56) — kernel computation infeasible; needs the analytic cascade or a certified simulation argument). |
| 3 | Transient to S′ (≈5.15×10¹⁰ steps) | **Not started** (same infeasibility). |
| 4 | S′ periods (general induction) | **Finite instances proved** (S′(2)→S′(4), S′(4)→S′(6)). The general proof (Interval/Return lemmas) **not started**. |
| 5 | The m = 132 period (analytic) | **Not started** (depends on #4 general form). |
| 6 | D(132,66) → R, 403,455 steps | **PROVED** (Finite.v). |
| 7 | R is the entry config | **Not a Rocq component** — a statement about the external phase10 simulation; corroboration only, the proof does not depend on it. |
| 8 | Halt criterion (M1–M4) | **PROVED** (TM.v, complete). |
| 9 | Formation R → first I-section, 150 steps | **PROVED** (Finite.v). |
| 10 | Standard regime: five rules total on I, I preserved, event-clean | **Rule soundness PROVED** (Phase 25: TUP added; all five rules — TDN/PUSH/POP-general/TUP/Stage A — are proved for all parameters in Sections.v). **Assembly DISCHARGED for the trajectory (Phase 34, Std.v)**: hypothesis **H_STD** of Loop.v's `NONHALT_FROM_R` is proved (`H_STD_proved`, (B2, n) = (96, 136)) by exhibiting the concrete chain from `cfg_Isec` — TDN + Stage A + 65 grind/collapse cycles (`STD_cycle` = `hGRIND t` + `hSTGA`) + final `hGRIND 65` — through `hsteps_sound` and `ENTRY`; `NONHALT_FROM_R_std` restates the assembly with only H_LOOP remaining. The event-cleanliness reading is discharged per rule (each `run … = Some …` certifies no halting step en route, via `halt_iff`). Not formalised, and no longer load-bearing: the invariant-I⁺ preservation induction over an *arbitrary* rule sequence. |
| 11 | G bookkeeping (only Stage A changes G, by −2) | **PROVED (discharged by the five statements, Phase 25)** — see Sections.v summary above. |
| 12 | Right-edge entry excursion (cost s + 12) | **PROVED** (Phase 25: `ENTRY` + `ENTRY_tape`, Mirror.v; generalised to abstract tails as `ENTRY_gen`, Era.v, Phase 27). |
| 13 | Right-edge mirror rules + invariant RI | **PROVED** (Phase 25: RTDN/RPUSH/RPOP/RTUP/RPROBE + `RPROBE_tape` + RI parity preservation, Mirror.v). The joint invariant J of the token pass belongs to #14. |
| 14 | Token pass / Cycle Lemma (min β = β_E − k) | **PROVED** (Phase 26: `CYCLE` with duration Dk k = 3·2^{k+3} − 4, `CYCLE_H` attainment of H_k at word β = β_E − k, orbit lower bound via `borbit_cycle` + `borbit_lb`, TokenPass.v). |
| 15 | The β = 2 exit (H_{β_E−2} at T(β_E); X(β_E) successor) | **PROVED** (Phase 26: `EXIT` + `EXIT_time` + `EXIT_entry`, TokenPass.v; finite instances β_E = 4, 8 also kernel-verified in Finite.v). |
| 16 | Re-coordinatisation to the single-block I-frame | **PROVED in full** (Phase 27, Recoord.v: `STAGE1`/`STAGE1_exit`, `STAGE3` for all B2 ≥ 2; Phase 30: stage 2 in general — `DSTAGE2` for every frozen prefix, DiagPass.v — giving `STAGE2_proved` and the unconditional composition `RECOORD2_uncond`). The seven kernel-verified stage-2 instances (B2 = 31 for n ∈ {2, 4, 6, 8, 10}; n = 2 for B2 ∈ {15, 47}) remain as regression checks. The single-block (ESC) frame's delivered pieces are in Esc.v (see #19). |
| 17 | REGEN; POP-general | **PROVED** (Phase 25: POP-general in Sections.v (Phase 23); `REGEN` assembled from POP_terminal + StageA_blank + PUSH_T, with `REGEN_tape`). |
| 18 | Era / reset map (Grind Lemma G′, s₁ = 2β_E + 31, β′ = 2β_E + 34) | **Deviation-free assembly PROVED** (Phase 27, Era.v: `ENTRY_gen`, `GRIND` (G′ endpoint form, frame floor as its hypothesis), `POP_CHAIN`, `ERA_LAW` with s₁ = 2β_E + 31, odd-G excluded, β′ = 2β_E + 34 > β_E). **Fenced**: the dip clause as a sequence statement (precise statement + route in the Era.v summary above; the Loop.v assembly does not use it — ERA_LAW discharges GRIND's floor directly). **Cross-era loop assembly DONE** (Phase 32, Loop.v: `PASS`, `SETTLED_ITER`, `ESC_ITER`, `TWO_ITERS`, `LOOP_NONHALT`, `NONHALT_FROM_R`; Phase 33: `ESC_ITER_114`), modulo the explicit hypotheses H_STD (#10 — **discharged Phase 34**, Std.v), ERA_GEN (**proved on its domain — odd ρ ≤ 33 — Phase 35**, EraGen.v; the general settled iteration is discharged for odd B2 ≤ 35 via `SETTLED_ITER_GEN_odd`) and, **Phase 39**, the even era law `ERA_GEN_even` (EraEven.v: even ρ ≤ 34, β′ = 2m + 4 independent of ρ; the general settled iteration is discharged for even 4 ≤ B2 ≤ 36 via `SETTLED_ITER_GEN_even` — together: every 3 ≤ B2 ≤ 36) and the undischarged H_LOOP instances (ESC entries at R ≥ 1278, modulo CASCADE_LANDING since Phase 42, reduced to modulo CASCADE_STAGE4_BIG in Phase 43, and to modulo CASCADE_STAGE4_TAIL in Phase 44 (Grind12.v: GG_boundary + the stage-4 segments SEG1–T4 mechanised; the residual is the tail traversal at the bottom frame []); settled entries at B2 ≥ 37; ESC-landing prefixes). |
| 19 | Re-formation (iteration 2) + deviation rules (PUSHX, PX2A/PX2B, TRANS2/TUP2, CGAP2; G″ induction) | **Step lists PROVED** (Phase 27, Esc.v: `POP2`, `PROBE_PREFIX`; Phase 28, Dev.v: PUSHX + follow-on, PX2A (incl. b = 2), PX2B b = 2..6, CGAP2 probe + both dispatches, TUP2 k = 1, TRANS2 k = 1/2, TUP2 defect with the F-3-corrected landing — all for all parameters). **Word model PROVED** (Phase 28, Grind.v: frame-general lists, `hstep` (20 rules) + `hstep_sound`/`hsteps_sound`, `grind_prefix` + `grind_prefix_dev`, `pred_cases`). **G″ endpoint induction PROVED in the clean regime and at the ESC frame** (Phase 29, Grind2.v: `hGRIND`, `GG_clean` for all frames under the floor, `hGRIND_dev` for the boundary frame, `ESC_GRIND_10`); **era stack invariant + Predecessor discharge PROVED** (`grind_inv`, `PRED_inv`, `PUSHX_only`, threaded `hstepsP` grind chains); **ESC-era law β_next = 2β + 4 PROVED for R ∈ {2, 4, 6, 8, 10}** (`ESC_ERA_LAW`). **Re-basing segment PROVED** (Phase 31, Grind3.v: `REBASE` from the F-4-corrected source, `ESC_GRIND_BIG`, endpoints for R = 12 / 14 / 2m + 16) and **ESC-era law extended to every even R ≤ 40** (`ESC_ERA_LAW_31`). **Second re-basing PROVED for R ≤ 114** (Phase 33, Grind4.v: `hGRIND_dev5` (the pb = [5] deviated grind, base case `hPX2B5`), `hGRIND_even`, `rounds_from4`/`rounds_from6`, endpoints for R = 42 / 44 / 2m + 46, `ESC_ERA_LAW_33`, and the combined **`ESC_ERA_LAW_114`**). **Third re-basing PROVED through R ≤ 268** (Phase 37, Grind6.v: the merged unwind — `DEV20_DESCEND`, `GRIND16_MID`, `PHASE3_DEEP`, endpoints `ESC_TO_REGEN_116` / `_118` / `_120` / `ESC_TO_REGEN_BIG3`, and the combined **`ESC_ERA_LAW_268`**). **Phase-6 merged unwind PROVED through R ≤ 602** (Phase 38, Grind7.v: the general boundary tools `LOOPN` and `DIPDESC` (the t = a2 descent, no floor hypothesis), `GRIND39_MID`, `TAIL2`, `PHASE6_PREFIX`, `PHASE6_TO_MID`, endpoints `ESC_TO_REGEN_112` / `_113` / `_114` / `ESC_TO_REGEN_BIG6`, and the combined **`ESC_ERA_LAW_602`**). **Phase-7 merged unwind PROVED through R ≤ 1276** (Phase 40, Grind8.v: `GRIND108_MID`, `PHASE7_TRANS19`, `PHASE7_TRANS42`, `PHASE7_TO_MID`, endpoints `ESC_TO_REGEN_604` / `_606` / `_608` / `ESC_TO_REGEN_BIG7`, and the combined **`ESC_ERA_LAW_1276`**). **Phase-8 entry + continuation stages A–C PROVED** (Phase 41, Grind9.v: `DIPDESC_even`, `PHASE8_TO_MID`, `PHASE8_STAGE_A` / `_B` / `_C`, `PHASE8_TO_STAGE_D`; new step list `PX2Bgen` (Dev.v) / constructor `hPX2Bgen` (Grind.v) for the stage-A dip at [19]). **Phase-8 cascade landing reduced to one statement** (Phase 42, Grind10.v: `CASCADE_STAGE4` and `CASCADE_POPFIN` — the cascade's last two stages — PROVED in general; `ESC_TO_REGEN_BIG8_of` / `ESC_ERA_LAW_42` PROVED modulo `CASCADE_LANDING`; Phase 41's "not an era REGEN landing" reading corrected — the cascade's terminal IS the era-landing shape, closed at machine level by `REGEN_gen` for arbitrary pb; evidence `hsim42.py`, incl. the odd-residue parity fence s = 2b + r2). **Cascade stages 1–3 PROVED in the era regime** (Phase 43, Grind11.v: `GG_odd` — the odd-pair g0 = 1 totality over an arbitrary deeper tail, floor m + 1 ≤ a2 — `CASCADE_STAGE1`, the merged `CASCADE_STAGE23` with its r2 = 2 / r2 = 4 dispatch branches, and the five-way stage-4 dispatch in `CASCADE_LANDING_of`, incl. the M = 618 degeneration; evidence `hsim43.py`). **Stage-4 boundary grind segments PROVED** (Phase 44, Grind12.v: `GG_boundary` — the dip-aware rounds totality: a − 1 clean rounds via `GG_rounds_part`, then the budget-exhaustion round through `DIPDESC` — `STAGE4_SEG1`, `STAGE4_SEG2`, `STAGE4_T1`, `STAGE4_T2`, `STAGE4_T3`, `STAGE4_T4`, and `CASCADE_STAGE4_BIG_of`: CASCADE_STAGE4_BIG modulo CASCADE_STAGE4_TAIL; evidence `hsim44.py`). **Open**: `CASCADE_STAGE4_TAIL` — the tail traversal at the bottom frame [] from `HB [] 0 1 5 (TAILs q v3 vM a b) 1` to the era landing, with the era parities baked in; its sub-structure re-enters boundary grinds at regrown frames. The ESC iteration is composed into the cross-era loop in Loop.v (`ESC_ITER`, `TWO_ITERS`, Phase 32; `ESC_ITER_114`, Phase 33; `ESC_ITER_268`, Phase 37; `ESC_ITER_602`, Phase 38; `ESC_ITER_1276`, Phase 40; `ESC_ITER_BIG8`, Phase 42, modulo CASCADE_LANDING; `ESC_ITER_BIG8_43`, Phase 43, modulo CASCADE_STAGE4_BIG; `ESC_ITER_BIG8_44`, Phase 44, modulo CASCADE_STAGE4_TAIL; `ESC_ITER_BIG8_45`, Phase 45, modulo TAIL2_BIG — the tail mechanised at the era slice in Grind13.v; `ESC_ITER_BIG8_46`, Phase 46, modulo TAIL2_END — the TAIL2_BIG descent mechanised in Grind14.v, TAIL2_BIG proved for vM ≤ 5365); the R ≥ 1278 instances modulo TAIL2_END are the remaining ESC instances of hypothesis H_LOOP there. (The fenced TUP2 stage-2 shape (k ≥ 2, r_k = 1) is proven unreachable in era grinds at human level; it remains fenced.) |

## Remaining components — precise statements, obstructions, routes

- **#14 Cycle Lemma Γ — DONE (Phase 26, TokenPass.v).** Formalised as
  documented: B-start word model with invariant J (`Jg`), the two round
  maps and the composed map Ψ proved from the mirror rules, the Suffix
  Lemma as step-level transports (`psi_step_front`, `psi_step_last2f`),
  the orbit recursion (`borbit_cycle`) by induction on k, Γ as `CYCLE`
  with D_k = 3·2^{k+3} − 4, and the min-β facts as `CYCLE_H`
  (attainment) + `borbit_lb` (orbit lower bound) at section granularity.
- **#15 exit (general) — DONE (Phase 26, TokenPass.v).** `EXIT`:
  H_{β_E−2} is reached at Tk(β_E − 2) (closed form `EXIT_time`) and the
  RTDN step list fires event-clean, landing cfg_sim at the B-section
  (B, 4, (1^{β_E−2}), (2^{β_E−2})) in shifted coordinates;
  `EXIT_entry` instantiates at the entry prefix. Instances β_E = 4, 8
  remain kernel-verified (Finite.v).
- **#16 stage 2 (general) — DONE (Phase 30, DiagPass.v).** Proved as
  `DSTAGE2` for every frozen prefix P (stronger than the `entryP B2`
  instance `RECOORD2` needed): the descent + walk decomposition, with
  the descent orbit built by the T₁/join/T₂ recursion over `fchain`
  (the `wok`-carrying `borbit` analogue) at cost `bcost k`, and the
  walk iterated at cost `Dsum n`. `STAGE2_proved` and
  `RECOORD2_uncond` in Recoord.v discharge #16's two-block landing
  unconditionally. The route taken differs slightly from the one
  sketched in Phase 27: the orbit recursion is on the descent's own
  B-start chain (T₁ = last gap + 2 with block + 1, T₂ = last gap − 2
  with a gap 3 appended), not on the Phase 17 suffix recursion
  directly; the suffix enters only through `psi_step_front_list`
  (DESC's carried suffix) and the walk's nested descents.
- **#16 stage 1 / stage 3 — DONE (Phase 27, Recoord.v)** as itemised
  above; `RECOORD2` composes all three stages with the exit.
- **#18 era law — deviation-free assembly DONE (Phase 27, Era.v).**
  Remaining: (a) the dip clause as a sequence statement (statement and
  route in the Era.v summary; not used by the Phase 32 assembly);
  (b) the **general-residue era law — DONE on its domain
  (Phase 35, EraGen.v).** `ERA_GEN_proved`: Loop.v's `ERA_GEN`
  statement for every odd ρ ≤ 33 and every m ≥ 1, by Era.v's
  assembly with ρ = 2t + 1 (absorption `GRIND` at t − 1,
  resp. `TDN` at ρ = 1; POP_CHAIN bookkeeping
  s₁ = ρ + 2β_E + 2; the era-loop invariant
  s + G = ρ + 2β_E + 5 over J = t + m cycles). The frame
  a2 = 16 is NOT replaced by a general frame: it is the
  settled frame's own constant (stage 3 lands at a = 16 for
  every two-block prefix), and both floor families (residue
  grind; era-loop grinds) bound t ≤ 16, i.e. ρ ≤ 33.
  Fenced, with machine-checked obstructions
  (`rocq/era_gen_verify.py`): ρ ≥ 35 odd (the grind's dip
  (ρ − 1)/2 exceeds the frame; the absorption landing is
  never reached at (35, 1) in 20,000,000 steps) and ρ even
  (G′ is odd-only — the absorption landing is never
  reached at (30, 1) — and the Stage-A era's G parity is
  load-bearing). Loop.v's `SETTLED_ITER_GEN_odd`
  discharges the general settled iteration for odd
  B2 ≤ 35. **Phase 39 update**: the ρ-even fence was a
  fence of ERA_GEN's shape; the even era law is proved on
  the rotation shape in EraEven.v (`ERA_GEN_even`, even
  ρ ≤ 34), and Loop.v's `SETTLED_ITER_GEN_even`
  discharges the even settled iterations for
  4 ≤ B2 ≤ 36 — the settled iteration is unconditional
  for every 3 ≤ B2 ≤ 36. Only ρ ≥ 35 (B2 ≥ 37) remains
  fenced, in both parities, with the beyond-frame
  behaviour documented in EraEven.v's section
  (`rocq/era_fence35_verify.py`).
- **Cross-era loop assembly — DONE (Phase 32, Loop.v)**, modulo
  three precisely-stated residuals, all carried as explicit lemma
  parameters (never axioms/admits) in `NONHALT_FROM_R`:
  **(H_STD) — DONE (Phase 34, Std.v).** The route taken is
  the G-descent bookkeeping directly, at the trajectory
  instance: `cfg_Isec` is definitionally the word-model
  section `HC [17] 95 1 2 [] 134`, the exit section
  `HB [17] 95 1 136 [] 2` is definitionally `entry_src 95 136`,
  and the chain between them is `hTDN` + `hSTGA` + 65
  grind/collapse cycles (`hGRIND t` + `hSTGA`, floors
  t + 1 ≤ 95) + `hGRIND 65` (`STD_chain`), closed by
  `ENTRY` to `entry_tgt 95 136` — (B2, n) = (96, 136),
  66 collapses, G: 134 → 2 (`H_STD_proved`;
  `NONHALT_FROM_R_std` is the assembly with H_STD
  discharged). The general I⁺-preservation induction over
  arbitrary rule sequences was not needed: H_STD quantifies
  only over the trajectory from `cfg_Isec`, whose rule
  sequence is the exhibited chain. **(ERA_GEN) — DONE on
  its domain (Phase 35,** EraGen.v: odd ρ ≤ 33); the
  complementary even residues are **DONE in Phase 39**
  (EraEven.v: even ρ ≤ 34, on the rotation shape); only
  ρ ≥ 35 remains fenced, in both parities, with
  machine-checked evidence (EraGen.v / EraEven.v).
  **(H_LOOP rest)** `loop_step` at the entry sections not discharged
  in Loop.v: ESC entries with R ≥ 1278, modulo TAIL2_END
  (the phase-8 cascade: the phase-7 range R ≤ 1276 was discharged
  in Phase 40, the phase-8 entry and stages A–C mechanised in
  Phase 41, and the era law at every even R ≥ 1278 reduced to
  the single statement CASCADE_LANDING in Phase 42 — its last
  two stages and the reduction proved in Grind10.v; the
  cascade's stages 1–3 then proved in the era regime in
  Phase 43 (Grind11.v), reducing the residual to
  CASCADE_STAGE4_BIG — the stage-4 boundary grind at
  M ≥ 1441 — via `CASCADE_LANDING_of` / `ESC_ITER_BIG8_43`;
  and the stage-4 grind's segments then mechanised in
  Phase 44 (Grind12.v: `GG_boundary` and SEG1–T4),
  reducing the residual to CASCADE_STAGE4_TAIL — the
  tail traversal at the bottom frame [] — via
  `CASCADE_STAGE4_BIG_of` / `ESC_ITER_BIG8_44`;
  the tail then mechanised at the era slice in
  Phase 45 (Grind13.v: TAIL_LAYER0 / TAIL_LAYER1 /
  TAIL2_CLEAN), reducing the residual to TAIL2_BIG —
  the layer-2 residue totality at one fixed state,
  vM ≥ 1653 — via `TAIL_ERA_of` / `ESC_ITER_BIG8_45`;
  and the TAIL2_BIG descent mechanised in Phase 46
  (Grind14.v: `DIPGRIND`, `DESCENT46`, `END46_*`),
  proving TAIL2_BIG for vM ≤ 5365 and reducing the
  residual to TAIL2_END — the END-state totality at
  k = vM − 1652 ≥ 3714 — via `TAIL2_BIG_of` /
  `ESC_ITER_BIG8_46`;
  the second
  re-basing R ≤ 114 was discharged in Phase 33,
  the third, R ≤ 268, in Phase 37, and the phase-6 range
  R ≤ 602 in Phase 38), settled entries at entryP B2 with
  B2 ≥ 37 (beyond the frame-16 era laws of both parities,
  fenced in EraGen.v / EraEven.v; the settled range
  3 ≤ B2 ≤ 36 is fully discharged — odd in Phase 35,
  even in Phase 39), and
  entry sections over ESC-era landing
  prefixes `0 1^(a+1) ++ enc pb` (iterations ≥ 3: PASS already
  covers their pass; their re-formation is the two-block stage 3
  at a general far block — STAGE3 is proved for abstract tails Q
  but at the entryP-shaped near block — composed with ERA_GEN's
  canonical grind on its proved domain). With the third
  re-basing and the remaining ERA_GEN-domain instances
  discharged (H_STD was discharged in Phase 34, ERA_GEN on
  its domain in Phase 35),
  `NONHALT_FROM_R` becomes unconditional from `cfg_R`;
  the blank-tape → R segment (#1–#5) would remain.
- **#19 deviations — step lists DONE (Phase 28, Dev.v); G″ endpoint
  induction and ESC-era law DONE for R ≤ 10 (Phase 29, Grind2.v).**
  Obligations (a)–(c) of Phase 28 are discharged in the regime the
  ESC trajectory uses (see the Grind2.v section above): the clean
  G″ endpoint holds for all frames under the floor (`GG_clean`),
  the deviated boundary grind is a proved induction
  (`hGRIND_dev`), the invariant is threaded (`hstepsP` chains) and
  the Predecessor obligations are discharged (`PRED_inv`,
  `PUSHX_only`), and `ESC_ERA_LAW` gives β_next = 2β + 4 for
  R ∈ {2, 4, 6, 8, 10}. **`REBASE` — DONE (Phase 31, Grind3.v),
  with finding F-4.** The fence's source had g0 = 11; the grind's
  actual section after round 3 (deviated) and its TUP is
  `HC [] 4 12 2 ((R−10, 2) :: P) 1` — the fence's 11 is the s′′ of
  that TUP (phase21_model traces at R = 14, 18: the g0 = 11
  section never occurs, and its chain does not reach the target;
  the g0 = 12 chain reaches it, boundaries verified at
  R ∈ {12, 14, 16, 20, 22, 28, 38, 40}). The corrected segment is
  proved for every carried stack (`REBASE_core`, no hypotheses on
  the passenger pair u; `REBASE` for u ≥ 3), composed with
  `ESC_GRIND_BIG`; the ESC-era law now covers every even R ≤ 40
  (`ESC_ERA_LAW_31`). The fence's measured decomposition (one
  further PUSHX, three POPs, one TUP2 hTUP2_1 at the end) is
  confirmed and located: the PUSHX is `hGRIND_dev` 3's base step,
  the three POPs its closing spine. **The second re-basing —
  DONE for R ≤ 114 (Phase 33, Grind4.v), via route (a) at
  pb = [5].** Route (b) was reinterpreted: the Phase 29 model
  evidence (PUSHX = 0, min PUSH a = 3 at a₀ = 15) is literally
  true because the deviation at pb = [5] is PX2B5, not PUSHX —
  the re-based grind deviates exactly once (verified in the
  hstep simulator and in `phase21_model.py` traces at
  R₂ ∈ {30, 32, 34, 40, 52, 64}), so no dip-shallowness
  invariant can make the rounds clean; the deviated recursion
  had to be derived, and was: `hGRIND_dev5` (base case
  `hPX2B5`, two-case landing), `round13_dev5`, `pop3_12`,
  then for R₂ ≥ 32 the even-g0 grind `hGRIND_even` and the
  phase-3 rounds `rounds_from4` at a2 = 34 closing at
  R₃ ≤ 70, giving `ESC_ERA_LAW_33` and the combined
  `ESC_ERA_LAW_114` (every even R ≤ 114), and
  `ESC_ITER_114` in Loop.v. **The third re-basing
  (R ≥ 116) — dip bottoms DONE (Phase 36, Dev.v /
  Grind.v / Grind5.v); the endpoint DONE through
  R ≤ 268 (Phase 37, Grind6.v); the phase-6 range
  R ≤ 602 DONE (Phase 38, Grind7.v); the phase-7 range
  R ≤ 1276 DONE (Phase 40, Grind8.v); the phase-8 range
  R ≥ 1278 reduced to CASCADE_LANDING (Phase 42,
  Grind10.v), with the cascade's last two stages proved
  (CASCADE_STAGE4, CASCADE_POPFIN).**
  Phase 3's rounds at a2 = 34, pb = [20; 0] stay clean
  while the last round's `hGRIND` floor holds (round
  j = R₃/2 − 2 needs R₃/2 − 1 ≤ 34, i.e. R₃ ≤ 70). At
  R₃ = 72 (R₂ = 104, R = 116) the boundary grind
  g0 = 71 at a2 = 34 descends its 34-level spine to
  `HC [20; 0] 0 3 2 ((1, 2)^34 :: (2, 2) :: Pe) 1`.
  Phase 36 derived the dispatch there from the machine
  (not from the documents' pattern, per F-3/F-4): the
  new step list **`PX2A0`** (general b ≥ 5 at
  pb = [b; 0], cost b + 32, landing
  `HB [0] 3 1 2 ((b − 4, 2) :: (1, 1) :: (1, 2) ::
  (1, 2) :: P) G`), proved in Dev.v and added as
  `hstep` constructor `hPX2A0` with soundness;
  `PX2A0_dip34` (Grind5.v) is that step at the fence
  shape itself. The grind's unwind then runs the
  (16, 2) grind at (pb = [0], a2 = 3): its rounds 1–2
  are clean `grind_round`s, its boundary round 3 is the
  deviated grind at pb = [0] — **also closed in
  Phase 36**: the dip bottom `HC [0] 0 3 2` has the
  new step list **`PX2B0`** (20 steps, Dev.v,
  constructor `hPX2B0`), and the boundary grind is the
  proved induction **`hGRIND_dev0`** (Grind5.v,
  landing `HB [] (t + 1) 1 (2t + 7) P G`) — and its
  rounds 4–5 continue at pb = [] via `hGRIND_dev`.
  **The R ≥ 116 endpoint — DONE (Phase 37, Grind6.v).**
  As fenced, the deviated grind at pb = [20; 0] has no
  uniform landing (its base step `hPX2A0` consumes the
  prefix and leaves the residue pair (16, 2)), so the
  endpoint was assembled as an explicit merged unwind:
  `PHASE3_DEEP` (BIG2's prefix + 34 phase-3 rounds via
  `rounds_from4g` + the final TUP + `DEV20_DESCEND` 34
  + `hPX2A0` + `GRIND16_MID`, the (16, 2) grind at
  ([0], 3) over an arbitrary carried rest, closing in
  TRANS2_1 + `pop_chain_h_app`), and the finishes
  `ESC_TO_REGEN_116` (TAIL), `_118` (phase 4: TUP +
  hGRIND_even 35 + TRANS2_2 + pop_chain_h), `_120`
  (TUP + hGRIND_even 35 + TUP2_1 + TDN + TAIL) and
  `ESC_TO_REGEN_BIG3` (phase 5, 38 ≤ m ≤ 111: rounds
  at ([41; 14; 5], 74) + TUP + hGRIND (m − 38) +
  TAIL). Combined: `ESC_ERA_LAW_268` — the ESC-era
  law for **every even R ≤ 268** — and Loop.v's
  `ESC_ITER_268` discharges H_LOOP's ESC instances
  for 116 ≤ R ≤ 268. **The phase-6 range — closed
  in Phase 38 (Grind7.v).** Phase 5's final grind
  (t = m − 38 at frame 74, pb = [41; 14; 5]) reaches
  its floor at m = 112 (the hGRIND hypothesis
  m − 37 ≤ 74 fails): the grind's last round becomes
  a boundary (deviated) grind at the three-block
  prefix [41; 14; 5]. Phase 38 closed it: the
  boundary descent is the general `DIPDESC` (no
  floor hypothesis), the dip fires the existing
  `hPX2A`, and the continuation is `GRIND39_MID`,
  giving `ESC_ERA_LAW_602` — the ESC-era law for
  **every even R ≤ 602** — and Loop.v's
  `ESC_ITER_602` discharges H_LOOP's ESC instances
  for 270 ≤ R ≤ 602. **Remaining, fenced precisely —
  R ≥ 604 (m ≥ 279):** at the phase-6 finish's new
  frame ([110; 19; 0], 164) the rounds (count
  m − 115 ≤ 164) and the final grind (t = m − 115,
  floor t + 1 ≤ 164) both bind; the final grind at
  t = a2 would again be a DIPDESC descent whose dip
  at [110; 19; 0] fires hPX2A into a phase-7
  continuation — the same proof pattern one level
  deeper, not a uniform induction (see the
  general-induction verdict in the Phase 38 summary
  at the top of this file). The fenced TUP2
  stage-2 shape stays fenced (era-unreachable).
- **#1/#4/#5 S/S′ side**. The S(k) and S′(m) period inductions are
  word-level inductions of the same character as G′ (the human proofs
  are `proof-168016.md`, `sprime-phase2-proof.md`, `ud-proof.md`); #5 is
  the analytic evaluation at m = 132 on top of #4. No conceptual blocker;
  substantial formalisation work.
- **#2/#3**. Finite but ≈3.2×10⁹ / ≈5.15×10¹⁰ steps: kernel computation
  (`vm_compute`) is infeasible at these lengths. Viable routes: (a) the
  analytic cascade already used at human level for #2's break and #3's
  transient (formalise the cascade, not the steps); (b) a certified
  simulator (a verified fast executor with a reflection lemma). **No
  axioms will be introduced for these** — they stay stated goals here
  until one of the routes is carried out.

## Honest gaps and what remains

- The mechanisation now covers the **reduction core** (M1–M4), **every
  feasible finite segment**, **all five standard rules + REGEN** in the
  I⁺ frame, the **complete right-edge mirror system + entry**, the
  **token pass with the Cycle Lemma and the general exit** (#14/#15),
  **re-coordinatisation in full** (#16: stages 1 and 3 and the
  conditional composition, Phase 27; **stage 2 in general and the
  unconditional composition**, Phase 30, DiagPass.v), the
  **deviation-free era law** (#18: G′, s₁ = 2β_E + 31,
  β′ = 2β_E + 34), the **ESC pieces** (`POP2`, probe prefix), **all of
  #19's deviation step lists** (Phase 28, Dev.v), the **hybrid word
  model with soundness, the grind prefix reductions and the
  Predecessor case analysis** (Phase 28, Grind.v), and — Phase 29 —
  the **G″ endpoint induction in the clean and ESC regimes, the era
  stack invariant with the Predecessor discharge, and the ESC-era
  law β_next = 2β + 4 for R ≤ 10** (Grind2.v), and — Phase 31 —
  **`REBASE` and the ESC-era law for every even R ≤ 40**
  (Grind3.v), and — Phase 32 — the **cross-era loop assembly**
  (Loop.v): PASS, both era iterations as loop steps, the first
  two iterations composed in full, the ascending-loop engine,
  and `NONHALT_FROM_R`, and — Phase 33 — the **second
  re-basing and the ESC-era law for every even R ≤ 114**
  (Grind4.v: `hGRIND_dev5`, `hGRIND_even`, `ESC_ERA_LAW_114`;
  Loop.v: `ESC_ITER_114`), and — Phase 34 — the
  **standard-regime assembly** (Std.v: `STD_cycle`,
  `STD_cycles`, `STD_reach_entry`, `STD_chain`,
  `H_STD_proved`, `NONHALT_FROM_R_std`), and — Phase 35 — the
  **general-residue era law on its domain** (EraGen.v:
  `ERA_GEN_proved` for odd ρ ≤ 33; Loop.v:
  `SETTLED_ITER_GEN_odd`), and — Phase 36 — the **third
  re-basing's dip bottoms and the deviated grind at
  pb = [0]** (Dev.v: `PX2A0` — the [b; 0] dispatch,
  b ≥ 5 — and `PX2B0` — the [0] dispatch; Grind.v:
  constructors `hPX2A0` / `hPX2B0` with soundness;
  Grind5.v: `hGRIND_dev0`, `PX2A0_dip34`), and — Phase 39 —
  the **even-residue era law** (EraEven.v: `EVEN_GRIND`,
  `ERA_GEN_even` for even ρ ≤ 34; Loop.v:
  `SETTLED_ITER_GEN_even`). It does
  **not** yet give an
  unconditional Rocq proof of non-halting: `NONHALT_FROM_R`
  rested on the two explicit hypotheses H_STD and H_LOOP;
  **H_STD is discharged (Phase 34)**, and H_LOOP's
  undischarged instances are the general settled iteration
  at B2 ≥ 37 (beyond the frame-16 era laws of both
  parities, fenced in Phases 35/39), the ESC entries at R ≥ 604 (the
  phase-7 boundary grind; the third re-basing through
  R ≤ 268 was discharged in Phase 37 and the phase-6
  range through R ≤ 602 in Phase 38)
  and the iterations ≥ 3 re-formation at ESC landing
  prefixes; and the theorem starts at `cfg_R` — the S/S′
  inductions (#1/#4/#5) and #2/#3 (the blank-tape → R
  segment) are open, as itemised above. (**Phase 38**:
  the phase-6 range is now discharged through
  R ≤ 602 — Grind7.v's merged unwind and `ESC_ITER_602`;
  H_LOOP's ESC instances remain open only at R ≥ 604.
  **Phase 39**: the settled instances are now discharged
  for every 3 ≤ B2 ≤ 36 — odd in Phase 35, even in
  Phase 39; only B2 ≥ 37 remains. **Phase 46**: the ESC
  instances at R ≥ 1278 are discharged modulo
  TAIL2_END alone (Grind14.v: the TAIL2_BIG descent is
  a fixed DIPGRIND parse; TAIL2_BIG is proved for
  vM ≤ 5365, and the residual is the END totality at
  k ≥ 3714); the phase-8 chain CASCADE_LANDING →
  CASCADE_STAGE4_BIG → CASCADE_STAGE4_TAIL →
  TAIL2_BIG → TAIL2_END is fully mechanised.)
- Suggested next order: iterations ≥ 3 re-formation
  (incl. the settled instances at B2 ≥ 37, which would
  need the sub-frame edge-grind theory fenced in
  Phase 39) → S/S′ inductions
  and m = 132 (#1/#4/#5) → #2/#3 strategy. (The R ≥ 604
  phase-7 deviation remains available as a further
  finite extension of the Phase 38 pattern.)

## Files

- `rocq/TM.v` (478 lines) — framework, entry lemmas, M1–M4.
- `rocq/Configs.v` (40 lines) — concrete configs, generated by
  `rocq/gen_configs.py` from the documents' closed forms + simulator.
- `rocq/Finite.v` (195 lines) — canonical form, `seg_check`, the checks.
- `rocq/Sections.v` (452 lines) — sweeps, probe, the five standard rules
  (TDN/PUSH/POP-general/TUP/Stage A), blank-end forms and REGEN.
- `rocq/Mirror.v` (395 lines) — mirror frame over an abstract frozen
  prefix, ENTRY, the five mirror rules, RI parity preservation, tape
  corollaries.
- `rocq/TokenPass.v` (1388 lines) — cfg_sim transport machinery, the
  token-pass word model (phase/excursions/rounds/Ψ), the Suffix Lemma
  transports, the orbit recursion, the Cycle Lemma Γ, cycles 0–1, and
  the general exit (Phase 26).
- `rocq/DiagPass.v` (808 lines) — #16 stage 2: the diagonal token
  pass for every frozen prefix — the T₂ map `F2` and the source
  invariant `wok`, the Ψ transports (shift / T₁ / T₂), `fchain`,
  the descent orbit recursion `dorbit_cycle`, DESC, the walk
  (`rpop_chain`, `WALK`, `WALK_ITER`), and `DSTAGE2` (Phase 30).
- `rocq/Recoord.v` (437 lines) — #16: stage 1 (RPOP chain + RPROBE),
  stage 2 statement + kernel-verified instances (Phase 28: seven
  points), stage 3 (RPUSH escape + F-sweep), the conditional
  composition RECOORD2 (Phase 27), and (Phase 30) `STAGE2_proved` +
  `RECOORD2_uncond` discharging it via DiagPass.v.
- `rocq/Era.v` (376 lines) — #18: ENTRY_gen over abstract tails, the
  Grind Lemma G′ (endpoint form, strong induction), POP_CHAIN, and
  ERA_LAW (Phase 27).
- `rocq/EraGen.v` (221 lines) — #18: `ERA_GEN_proved`, the
  general-residue era law on its domain (odd ρ ≤ 33), by
  ERA_LAW's assembly at ρ = 2t + 1 (absorption `TDN` / `GRIND`
  at t − 1, `POP_CHAIN`, `REGEN`, the Stage-A era, `ENTRY_gen`)
  (Phase 35; the header carries a dated Phase 39 addendum on
  the two fences).
- `rocq/EraEven.v` (478 lines) — #18: the even-residue era
  law (Phase 39): `gPOP_CHAIN`, `gGRIND` (Lemma G′ over a
  general frame), `gROT2` (the gap-2 frame rotation),
  `ABS2`, `EVEN_GRIND` (the even absorption, floor k ≤ A),
  and `ERA_GEN_even` (even ρ = 2k + 2 ≤ 34, every m ≥ 1;
  β′ = 2m + 4 independent of ρ).
- `rocq/Esc.v` (301 lines) — #19 pieces: prefix-general TUP, POP2, and
  the probe prefix E1–E5 with its cfg_sim landing (Phase 27).
- `rocq/Dev.v` (436 lines) — #19: the deviation step lists (chain
  units, PUSHX, PX2A/PX2B, CGAP2, TUP2/TRANS2 chains, the TUP2 defect
  with the F-3-corrected landing) (Phase 28); Phase 36 additions:
  `PX2A0` (the [b; 0] dip bottom, b ≥ 5) and `PX2B0` (the [0] dip
  bottom).
- `rocq/Grind.v` (450 lines) — #19: frame-general step lists, the
  hybrid word model `hstep` + soundness, the grind prefix reductions,
  and the Predecessor case analysis (Phase 28); Phase 36 additions:
  constructors `hPX2A0` / `hPX2B0` with their soundness cases.
- `rocq/Grind2.v` (1265 lines) — #19: `hGRIND` / `hGRIND_dev`
  (clean and deviated Grind Lemma G′ at word level), the clean G″
  endpoint `GG_clean`, `ESC_GRIND_10`, the transfer tail and
  `ESC_TO_REGEN`, frame-general `REGEN_gen`, the era tail
  `ERA_TAIL`, the ESC-era law `ESC_ERA_LAW` (R ≤ 10), and the era
  stack invariant `grind_inv` with `PRED_inv` / `PUSHX_only` and
  the threaded `hstepsP` grind chains (Phase 29).
- `rocq/Grind3.v` (550 lines) — #19: `REBASE_core` / `REBASE` (the
  R ≥ 12 re-basing segment, from the F-4-corrected source),
  `ESC_GRIND_BIG`, the R = 12 / 14 / 2m + 16 grind endpoints, and
  `ESC_ERA_LAW_31` — the ESC-era law β_next = 2β + 4 for every
  even R ≤ 40 (Phase 31).
- `rocq/Grind4.v` (640 lines) — #19: the second re-basing
  (Phase 33): `hGRIND_dev5` / `hGRIND_dev5_0` (the deviated
  grind at pb = [5], base case `hPX2B5`), `round13_dev5`,
  `pop3_12`, `hGRIND_even` (the even-g0 grind),
  `rounds_from6` / `rounds_from4` (generalised round chains),
  the endpoints `ESC_TO_REGEN_42` / `ESC_TO_REGEN_44` /
  `ESC_TO_REGEN_BIG2`, `ESC_ERA_LAW_33` (42 ≤ R ≤ 114) and
  `ESC_ERA_LAW_114` — the ESC-era law β_next = 2β + 4 for
  every even R ≤ 114. The R ≥ 116 fence is stated in its
  header.
- `rocq/Grind5.v` (155 lines) — #19: the third re-basing
  (Phase 36): `hGRIND_dev0` (the deviated Grind Lemma G′
  at the boundary frame at pb = [0], base case
  `hPX2B0` + `hPOP`) and `PX2A0_dip34` (the R = 116 dip
  bottom step itself). The R ≥ 116 endpoint fence is
  stated in its header.
- `rocq/Grind6.v` (867 lines) — #19: the merged unwind
  (Phase 37): `rounds_from4g`, `pop_chain_h_app`,
  `DEV20_step` / `DEV20_DESCEND` (the [20; 0] descent),
  `GRIND16_A`–`E` / `GRIND16_MID` (the (16, 2) grind at
  ([0], 3) over a carried rest), `PHASE3_DEEP`, the
  endpoints `ESC_TO_REGEN_116` / `_118` / `_120` /
  `ESC_TO_REGEN_BIG3`, and `ESC_ERA_LAW_37` /
  `ESC_ERA_LAW_268` — the ESC-era law β_next = 2β + 4
  for every even R ≤ 268. The R ≥ 270 fence (phase-6
  boundary grind at pb = [41; 14; 5]) is stated in its
  header; it was discharged in Phase 38 (Grind7.v).
- `rocq/Grind7.v` (992 lines) — #19: the phase-6 merged
  unwind (Phase 38): the general boundary tools
  `LOOPN` (truncated grind loop) and `DIPDESC` (the
  t = a2 boundary descent, no floor hypothesis),
  `GRIND39_MID` (the ([5], 13) continuation grind),
  `TAIL2` (the TRANS2_2 tail), `PHASE6_PREFIX`,
  `PHASE6_TO_MID`, the endpoints `ESC_TO_REGEN_112` /
  `_113` / `_114` / `ESC_TO_REGEN_BIG6`, and
  `ESC_ERA_LAW_38` / `ESC_ERA_LAW_602` — the ESC-era
  law β_next = 2β + 4 for every even R ≤ 602. The
  R ≥ 604 fence (phase-7 boundary grind at the frame
  [110; 19; 0]) and the general-induction verdict are
  stated in its header.
- `rocq/Grind11.v` (604 lines) — #19: the cascade's
  stages 1–3 in the era regime (Phase 43): `pop12`,
  `GG_rounds_odd` / `GG_odd` (the odd-pair g0 = 1
  totality), `CASCADE_STAGE1`, `CASCADE_STAGE23` +
  `CASCADE_STAGE23_r2_4` / `CASCADE_STAGE23_r2_2`
  (the merged stage and its dispatch branches), the
  residual core `CASCADE_STAGE4_BIG` (the stage-4
  boundary grind, M ≥ 1441), `CASCADE_LANDING_of`
  (CASCADE_LANDING modulo CASCADE_STAGE4_BIG) and
  `ESC_ERA_LAW_43`. Pre-verification: `rocq/hsim43.py`.
- `rocq/Grind12.v` (537 lines) — #19: the stage-4
  boundary grind's segments and the tail core
  (Phase 44): `GG_rounds_part`, `GG_boundary` (the
  dip-aware rounds totality), `STAGE4_SEG1`,
  `STAGE4_SEG2`, `STAGE4_T1`, `STAGE4_T2`, `STAGE4_T3`,
  `STAGE4_T4`, the residual core `CASCADE_STAGE4_TAIL`
  (the tail traversal at the bottom frame),
  `CASCADE_STAGE4_BIG_of` (CASCADE_STAGE4_BIG modulo
  CASCADE_STAGE4_TAIL) and `ESC_ERA_LAW_44`.
  Pre-verification: `rocq/hsim44.py`.
- `rocq/Grind13.v` (565 lines) — #19: the stage-4
  tail at the era slice (Phase 45): `TAIL_LAYER0`,
  `TAIL_LAYER1`, `TAIL2_CLEAN` (the layer-2 residue,
  clean range vM ≤ 1652), the residual core
  `TAIL2_BIG` (the layer-2 residue totality at one
  fixed state, vM ≥ 1653), `TAIL2_ALL`, `TAIL_ERA_of`,
  `CASCADE_STAGE4_BIG_45` (CASCADE_STAGE4_BIG modulo
  TAIL2_BIG) and `ESC_ERA_LAW_45`.
  Pre-verification: `rocq/hsim45.py`.
- `rocq/Grind14.v` (730 lines) — #19: the TAIL2_BIG
  descent (Phase 46): arithmetic-form step wrappers
  (`sTUP`, `sPUSH`, `sTDN`, `sPOP1`, `sTUP2_1`,
  `sTRANS2_1`), `DIPGRIND` (the boundary rounds at a
  general counter), `CLEANG_odd` / `CLEANG_even`
  (the clean grinds at counter 3), the descent
  stacks `PXs` / `W1s` / `W2s`, `TAIL2_FRONT`,
  `DESCENT46` (the descent px → END, uniform in
  (k, β)), `END46_1` / `END46_2` / `END46_3` /
  `END46_big` (the END state closed for k ≤ 3713),
  the residual core `TAIL2_END` (the END totality,
  k ≥ 3714), `TAIL2_BIG_of` (TAIL2_BIG modulo
  TAIL2_END; proved for vM ≤ 5365) and
  `ESC_ERA_LAW_46`. Pre-verification:
  `rocq/hsim46.py`.
- `rocq/Loop.v` (1207 lines) — the cross-era loop assembly
  (Phase 32; `ESC_ITER_114` added Phase 33;
  `SETTLED_ITER_GEN_odd` added Phase 35; `ESC_ITER_268`
  added Phase 37; `ESC_ITER_602` added Phase 38;
  `SETTLED_ITER_GEN_even` added Phase 39; `ESC_ITER_1276`
  added Phase 40; `ESC_ITER_BIG8` added Phase 42;
  `ESC_ITER_BIG8_43` added Phase 43;
  `ESC_ITER_BIG8_44` added Phase 44;
  `ESC_ITER_BIG8_45` added Phase 45;
  `ESC_ITER_BIG8_46` added Phase 46):
  run-totality
  infrastructure (`run_trans_sim`, `total_transfer`),
  `entry_sec` / `loop_step`, `PASS`
  (exit + stages 1–2 for an arbitrary prefix), `esc_bridge`
  (the escape section over a single-block prefix is
  definitionally `esc_src`), `SETTLED_ITER` (B2 = 31),
  `SETTLED_ITER_GEN` (general B2, modulo the explicit
  hypothesis `ERA_GEN`; `ERA_LAW_GEN` is its ρ = 29 instance)
  and `SETTLED_ITER_GEN_odd` (odd B2 ≤ 35, unconditional via
  EraGen.v) and `SETTLED_ITER_GEN_even` (even
  4 ≤ B2 ≤ 36, unconditional via EraEven.v; β ↦ 2β + 4),
  `ESC_ITER` (β ↦ 2β + 4, R ≤ 40), `ESC_ITER_114`
  (β ↦ 2β + 4, every even R ≤ 114), `ESC_ITER_268`
  (β ↦ 2β + 4, every even R ≤ 268), `ESC_ITER_1276`
  (β ↦ 2β + 4, every even R ≤ 1276), `ESC_ITER_BIG8`
  (β ↦ 2β + 4, every even R ≥ 1278, modulo
  CASCADE_LANDING), `ESC_ITER_BIG8_43` (β ↦ 2β + 4,
  every even R ≥ 1278, modulo CASCADE_STAGE4_BIG),
  `ESC_ITER_BIG8_44` (β ↦ 2β + 4,
  every even R ≥ 1278, modulo CASCADE_STAGE4_TAIL),
  `ESC_ITER_BIG8_45` (β ↦ 2β + 4,
  every even R ≥ 1278, modulo TAIL2_BIG),
  `ESC_ITER_BIG8_46` (β ↦ 2β + 4,
  every even R ≥ 1278, modulo TAIL2_END),
  `TWO_ITERS` (the first
  two iterations composed: β ↦ 4n + 80), `loop_chain` /
  `LOOP_NONHALT` (the ascending-loop engine), and
  `NONHALT_FROM_R` (non-halting from `cfg_R` modulo the
  explicit hypotheses H_STD and H_LOOP).
- `rocq/Std.v` (202 lines) — the standard-regime assembly
  (Phase 34): `STD_cycle` (one grind/collapse cycle:
  `hGRIND t` + `hSTGA`), `STD_cycles` (the G-descent
  induction), `STD_reach_entry` (regime totality for
  empty-stack I-C-sections, G = 2k + 6 at frame ≥ k + 2),
  `STD_chain` (the trajectory chain from
  `HC [17] 95 1 2 [] 134` to `HB [17] 95 1 136 [] 2`),
  the definitional identifications `Isec_hcfg` and
  `final_entry_src`, `H_STD_proved` (H_STD discharged,
  (B2, n) = (96, 136)) and `NONHALT_FROM_R_std`
  (the headline assembly modulo H_LOOP only).
- `rocq/trace_rules.py`, `rocq/trace_recoord.py`, `rocq/trace_dev.py` —
  zipper traces used to fix the exact intermediate forms of the
  segment lemmas (the third covers the Phase 28 files; all match the
  documents, except the F-3 defect row noted above).
- `rocq/std_verify.py` — the Phase 34 pre-verification: a
  machine simulator with TM.v's exact step semantics checking
  the Std.v chain's macro boundaries from `cfg_Isec` and the
  end-to-end small instances (G0 ∈ {6, 8, 10}) through ENTRY.
- `rocq/era_gen_verify.py` — the Phase 35 pre-verification: a
  machine simulator with TM.v's exact step semantics checking
  the general-ρ era boundary sequences (positive instances
  ρ ∈ {1, 27, 29, 31, 33}; negative controls ρ ∈ {30, 35}).
- `rocq/era_even_verify.py` — the Phase 39 pre-verification:
  the even era's full boundary sequences with exact cost
  deltas (positive instances (ρ, m) ∈ {(2, 1), (2, 4),
  (4, 4), (6, 3), (10, 2), (28, 5), (30, 4), (34, 4)}; the
  absorption climb checked at (10, 2) and (30, 2)).
  ALL CHECKS PASS.
- `rocq/era_fence35_verify.py` — the Phase 39 fence evidence
  for ρ ≥ 35: the observed absorptions (ρ = 35: bsec 17 1 39;
  ρ = 37/39/41: rotation to (38|17), s = ρ − 33; ρ = 36:
  rotation to (37|17), s = 2) and the 60,000,000-step budget
  exhaustion at ρ = 38, 40 (~9 min runtime).
- `rocq/hsim36.py` — the Phase 36 pre-verification: a word-level
  `hstep` simulator (mirroring Grind.v, with the two new
  constructors) plus a machine section recogniser over
  `trace_dev.Z`; checks the PX2A0 / PX2B0 machine forms, the
  dev20(1) / dev20(2) word/machine boundary agreement, and the
  `hGRIND_dev0` / `hGRIND_dev` rule counts and landings.
- `rocq/hsim37.py` — the Phase 37 pre-verification: extends
  hsim36's word-level simulator; checks the GRIND16_TAIL
  word boundaries at (spine, β) ∈ {(0, 2), (2, 2), (3, 3),
  (5, 2)}, word/machine boundary agreement at (2, 2)
  (131 rules, 1,598 machine steps), DEV20_DESCEND
  boundaries at t = 1, 2, 3, a rounds_from4g analogue, and
  frame-10 analogues of the phase-4 / phase-5 finishes.
- `rocq/hsim38.py` — the Phase 38 pre-verification: extends
  hsim36's word-level simulator; checks the DIPDESC and
  LOOPN word boundaries at small parameters, the GRIND39
  word boundaries at (spine, β) ∈ {(0, 2), (2, 2), (3, 3)}
  (98,338 rules at spine 0), word/machine boundary
  agreement at (0, 2) (1,180,078 machine steps), shrunk
  analogues of the m = 113 / m = 114 / transitional / BIG6
  finishes, and the hPX2A dispatch at the phase-6 dip
  shape.
- `rocq/env.sh`, `rocq/coqcw` — toolchain wrapper (Coq 8.18.0).
