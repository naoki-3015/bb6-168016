# BB(6) holdout #168016 does not halt — submission package

**Machine:** `1RB1RA_1RC1LB_0LD0RA_1RF1LE_---1LF_1LC0LF`
(bbchallenge seed-database ID **168016**; #168016 of the
2026-10-30 BB(6) holdout list of 608 machines)

**Result:** started on the blank tape, this machine **never
halts**. Its only undefined transition is E-on-0.

**Status of this package:** prepared 2026-11-25 for community
submission. **It has not been posted or submitted anywhere yet.**
`draft-announcement.md` contains the announcement drafts and the
exact steps for submitting them.

## What is claimed — and what is not

- **Claimed:** a complete, unconditional **human-level proof** of
  non-halting (`168016-proof.md`, components #1–#19, all (P) or
  finite (C); no remaining hypotheses). The one underived rule
  shape in the documents (TUP2 stage 2 at k ≥ 2, r_k = 1) is
  *proved unreachable* in era grinds, not silently assumed.
- **Independently reproduced:** a clean-room checker, written
  from the proof documents alone, re-verifies the proof's
  computational content: **75 checks, 0 failures** (full run).
  It found two discrepancies, both in statements the theorem
  does not use — a ×1000 slip in the last addend of the finite
  corollary bound (F-1) and a cost-accounting slip for CGAP2,
  a rule proved never to fire in era grinds (F-2). Both are
  corrected as **dated errata** in the proof documents and are
  reported in full in `reproduction/reproduction-report.md`.
- **Mechanisation — in progress, not complete:** the Rocq
  (Coq 8.18) development in `rocq/` proves the halt criterion
  M1–M4 in full, kernel-verifies the finite segments, proves
  all five standard-regime rules (TDN / PUSH / POP-general /
  TUP / Stage A) and REGEN sound for all parameters, proves
  the right-edge entry excursion and all five mirror rules
  (RTDN / RPUSH / RPOP / RTUP / RPROBE) with the invariant RI,
  the token pass (Cycle Lemma Γ) and the general β = 2 exit,
  the re-coordinatisation in full — stages 1 and 3, the
  general stage 2 (the diagonal token pass, proved for every
  frozen prefix), and their unconditional composition — the era law
  (s₁ = 2β_E + 31, β′ = 2β_E + 34), the single-block
  escape pieces (POP2, the probe prefix), the complete
  deviation system (all step lists, the word model and its
  soundness, the grind prefix reductions, the Predecessor
  case analysis), the G″ endpoint induction with the era
  stack invariant and the Predecessor discharge, the
  ESC-family era law (β_next = 2β + 4) for every even
  R ≤ 114 including both re-basing segments, and the
  **cross-era loop assembly** — both era iterations as loop
  steps, the first two iterations composed in full, an
  ascending-loop engine, and non-halting from the record
  configuration R modulo two explicit hypotheses (stated as
  lemma parameters in `Loop.v`), of which the first — the
  standard regime's assembly — is now discharged in
  `Std.v` (from the first I-section the regime reaches the
  entry landing entry_tgt 95 136), leaving iteration at
  the entry sections not yet discharged — of which the
  general settled iteration is now also discharged on the
  era laws' proved domains in `EraGen.v` (ERA_GEN for every
  odd residue ρ ≤ 33) and `EraEven.v` (ERA_GEN_even for
  every even residue ρ ≤ 34; the general settled iteration
  unconditional for every B2 with 3 ≤ B2 ≤ 36) —
  no axioms, no admits. It does **not** yet give an
  unconditional Rocq proof of non-halting;
  `rocq/mechanisation-status.md`
  maps every proof component to its mechanisation status.

## The proof in five lines

Halting is equivalent to one tape pattern (lemmas M1–M4): an
F-on-0 read whose left triple is (0,1,0). A finite transient —
two bounce families S(k), S′(m), an analytic deviation at
m = 132, and a 403,455-step computed segment — reaches the
record tape R = `1^17 0 1^97 0 1^137 0` at step
1,770,887,431,134,099,605,707. After R the dynamics is a
two-regime system of derived word-level rules (standard regime
+ right-edge mirror regime) organised in eras; the token pass
(Cycle Lemma) forces an exit at β = 2, and the continuation
re-coordinatises into the standard regime. One full loop maps
β ↦ 2β + 34 with strictly growing span, so no configuration
ever repeats and the halting pattern never occurs.
See `proof-summary-168016.md` for the full summary.

## File map

```
README.md                  this file
draft-announcement.md      announcement drafts + submission checklist (NOT posted)
proof-summary-168016.md    self-contained summary of the proof
168016-proof.md            the full proof: theorem + component table #1–#19
proof/                     the derivation files the proof depends on
  proof-168016.md            family S, arrival table A.1
  postbreak-168016.md        the k = 56 break, transient, S′ arrivals
  sprime-phases-168016.md    family S′ phase decomposition
  sprime-phase2-proof.md     S′ phase 2
  ud-proof.md                Interval Lemma / U_d chain decomposition
  phase2-complete.md         S′ period proof assembly
  m132-analysis.md           the m = 132 deviation; D(132,66); R
  third-family.md            the post-R regime from R (Phase 10)
  transient-analysis.md      transient / pushdown analysis (Phases 10–11)
  post-R-proof.md            halt criterion M1–M4; the post-R system
  bounce-derivation.md       the five standard rules + invariant I
  reexpansion-derivation.md  Stage A; G bookkeeping
  rightedge-derivation.md    ENTRY; the five mirror rules + invariant RI
  token-pass-derivation.md   Cycle Lemma; the β = 2 exit
  post-exit-analysis.md      exit continuation; re-coordinatisation; era data
  phase19-derivations.md     REGEN; era closed form; re-coordinatisation (P)
  phase20-derivations.md     single-block re-formation; boundary forms
  phase21-derivations.md     deviation system PUSHX/PX2A/PX2B/TRANS2/TUP2/CGAP2 (P)
reproduction/
  reproduce_168016.py        clean-room reproduction checker (Python 3, stdlib only)
  reproduction-report.md     what was re-implemented, every check, findings F-1/F-2
  phase10-expected.txt       reference checkpoints read by the checker as data
                             (disclosed in the checker header; no code is taken from it)
rocq/
  TM.v                       machine, execution, entry lemmas, M1–M4 (proved)
  Configs.v                  concrete configurations (generated by gen_configs.py)
  Finite.v                   finite segments by kernel computation (proved)
  Sections.v                 five standard rules + REGEN soundness (proved)
  Mirror.v                   right-edge entry + five mirror rules + RI (proved)
  TokenPass.v                token pass: Cycle Lemma + the general exit (proved)
  DiagPass.v                 stage 2: the diagonal token pass for every frozen prefix (proved)
  Recoord.v                  re-coordinatisation stages 1-3 + unconditional composition (proved)
  Era.v                      era law: Grind Lemma G' + ERA_LAW (proved)
  EraGen.v                   general-residue era law ERA_GEN for every odd rho <= 33 (proved)
  EraEven.v                  even-residue era law ERA_GEN_even for every even rho <= 34: rotation absorption, beta' = 2m + 4 independent of rho (proved)
  Esc.v                      single-block escape pieces: POP2 + probe prefix (proved)
  Dev.v                      deviation step lists: PUSHX/PX2A/PX2B/CGAP2/TRANS2/TUP2/defect + PX2A0/PX2B0 + PX2Bgen (the uniform single-block family, b >= 5) (proved)
  Grind.v                    word model + soundness, grind prefix, Predecessor analysis (proved)
  Grind2.v                   G'' endpoint induction + ESC-era law for R <= 10 (proved)
  Grind3.v                   REBASE (R >= 12 re-basing) + ESC-era law for every even R <= 40 (proved)
  Grind4.v                   second re-basing (deviated grind at prefix [5]) + ESC-era law for every even R <= 114 (proved)
  Grind5.v                   third re-basing dip bottoms (PX2A0/PX2B0) + deviated grind at prefix [0] (proved)
  Grind6.v                   merged unwind at R = 116 + phase-4/5 continuations: ESC-era law for every even R <= 268 (proved)
  Grind7.v                   phase-6 merged unwind: general boundary descent DIPDESC + GRIND39_MID: ESC-era law for every even R <= 602 (proved)
  Grind8.v                   phase-7 merged unwind: DIPDESC at [110; 19; 0] + hPX2A + GRIND108_MID: ESC-era law for every even R <= 1276 (proved)
  Grind9.v                   phase-8 entry (R >= 1278): funnel PHASE8_TO_MID + continuation stages A-C + DIPDESC_even (proved); the continuation past stage C is a full-stack cascade, fenced with machine evidence (era law still closes at R <= 1276)
  Grind10.v                  the cascade landing (Phase 42): CASCADE_STAGE4 + CASCADE_POPFIN (the cascade's last two stages, proved in general); the phase-8 era law for every even R >= 1278 proved modulo the single statement CASCADE_LANDING (the cascade's landing on the era shape, stress-tested in hsim42.py)
  Grind11.v                  the cascade's stages 1-3 in the era regime (Phase 43): GG_odd (the odd-pair g0 = 1 grind totality), CASCADE_STAGE1, the merged CASCADE_STAGE23 with its r2 = 2 / r2 = 4 dispatch branches; CASCADE_LANDING proved modulo the strictly smaller core CASCADE_STAGE4_BIG (the stage-4 boundary grind at M >= 1441, one pair at one fixed frame); ESC_ERA_LAW_43
  Grind12.v                  the stage-4 boundary grind's segments (Phase 44): GG_boundary (the dip-aware rounds totality), STAGE4_SEG1 / SEG2 / T1 / T2 / T3 / T4; CASCADE_STAGE4_BIG proved modulo the strictly smaller core CASCADE_STAGE4_TAIL (the tail traversal at the bottom frame, era parities baked in); ESC_ERA_LAW_44
  Grind13.v                  the stage-4 tail at the era slice (Phase 45): TAIL_LAYER0 / TAIL_LAYER1 (the tail's layers 0-1), TAIL2_CLEAN (the layer-2 residue, clean range vM <= 1652); CASCADE_STAGE4_BIG and the era law proved modulo the strictly smaller core TAIL2_BIG (the layer-2 residue totality at one fixed state, boundary range vM >= 1653 only); ESC_ERA_LAW_45
  Grind14.v                  the TAIL2_BIG descent (Phase 46): DIPGRIND (the boundary rounds at a general counter), CLEANG_odd / CLEANG_even (the clean grinds at counter 3), TAIL2_FRONT, DESCENT46 (the descent to the END state, uniform in (k, beta)), END46_1 / END46_2 / END46_3 / END46_big (the END state closed for k <= 3713); TAIL2_BIG proved for vM <= 5365 and the era law proved modulo the strictly smaller core TAIL2_END (the END totality, k >= 3714 only); ESC_ERA_LAW_46
  Grind15.v                  the END re-descent (Phase 47): END47_FRONT, CASCADE47 (the 34-segment fixed parse at an arbitrary carried tail - not a return to END), END47_TO_TOP, TOP47_2 / TOP47_4 / TOP47_6 / TOP47_BAND (the TOP closings at rho = 2, 4, 6 and in band 1, rho <= 14858); TAIL2_END proved for the whole first k-band 3714 <= k <= 11142 and the era law proved modulo the strictly smaller core TAIL2_END2 (the TOP totality at rho = 2j, j >= 7430 only, where the second descent is a new cascade with different constants); ESC_ERA_LAW_47
  Grind16.v                  the TOP second descent (Phase 48): CASCADE48 (the 24-segment fixed parse at an arbitrary carried tail), TOP48_TO_TOP2, TOP48_2 / TOP48_4 / TOP48_6 / TOP48_BAND (the TOP2 closings at r = 2, 4, 6 and in band 2, r <= 32602); TAIL2_END2 proved for 7430 <= j <= 23730 and the era law proved modulo the strictly smaller core TAIL2_END3 (the TOP2 totality at r = 2j, j >= 16302 only, where the third descent is a new cascade with different constants); ESC_ERA_LAW_48
  Grind17.v                  the TOP2 third descent (Phase 49): CASCADE49 (the 47-segment fixed parse at an arbitrary carried tail), TOP49_TO_TOP3, TOP49_2 / TOP49_4 / TOP49_6 / TOP49_BAND (the TOP3 closings at r3 = 2, 4, 6 and in band 3, r3 <= 65210); TAIL2_END3 proved for 16302 <= j <= 48906 and the era law proved modulo the strictly smaller core TAIL2_END4 (the TOP3 totality at r3 = 2j, j >= 32606 only, where the fourth descent is a new cascade with different constants); ESC_ERA_LAW_49
  Grind18.v                  the TOP3 fourth descent (Phase 50): CASCADE50 (the 64-segment fixed parse at an arbitrary carried tail), TOP50_TO_TOP4, TOP50_2 / TOP50_4 / TOP50_6 / TOP50_BAND (the TOP4 closings at r4 = 2, 4, 6 and in band 4, r4 <= 134246); TAIL2_END4 proved for 32606 <= j <= 99728 and the era law proved modulo the strictly smaller core TAIL2_END5 (the TOP4 totality at r4 = 2j, j >= 67124 only, where the fifth descent is a new cascade with different constants); ESC_ERA_LAW_50
  Grind19.v                  the TOP4 fifth descent (Phase 51): CASCADE51 (the 12-segment fixed parse at an arbitrary carried tail), TOP51_TO_TOP5, TOP51_2 / TOP51_4 / TOP51_6 / TOP51_BAND (the TOP5 closings at r5 = 2, 4, 6 and in band 5, r5 <= 268498); TAIL2_END5 proved for 67124 <= j <= 201372 and the era law proved modulo the strictly smaller core TAIL2_END6 (the TOP5 totality at r5 = 2j, j >= 134250 only, where the sixth descent is a new cascade with different constants); ESC_ERA_LAW_51
  Grind20.v                  the TOP5 sixth descent (Phase 52): CASCADE52 (the 227-step fixed parse at an arbitrary carried tail), TOP52_TO_TOP6, TOP52_2 / TOP52_4 / TOP52_6 / TOP52_BAND (the TOP6 closings at r6 = 2, 4, 6 and in band 6, r6 <= 646578); TAIL2_END6 proved for 134250 <= j <= 457538 and the era law proved modulo the strictly smaller core TAIL2_END7 (the TOP6 totality at r6 = 2j, j >= 323290 only, where the seventh descent is a new cascade with different constants); ESC_ERA_LAW_52
  Grind21.v                  the TOP6 seventh descent (Phase 53): CASCADE53 (the 337-step fixed parse at an arbitrary carried tail), TOP53_TO_TOP7, TOP53_2 / TOP53_4 / TOP53_6 / TOP53_BAND (the TOP7 closings at r7 = 2, 4, 6 and in band 7, r7 <= 1293162); TAIL2_END7 proved for 323290 <= j <= 969870 and the era law proved modulo the strictly smaller core TAIL2_END8 (the TOP7 totality at r7 = 2j, j >= 646582 only, where the eighth descent is a new cascade with different constants); ESC_ERA_LAW_53
  Grind22.v                  the TOP7 eighth descent (Phase 54): CASCADE54 (the 176-step fixed parse at an arbitrary carried tail), TOP54_TO_TOP8, TOP54_2 / TOP54_4 / TOP54_6 / TOP54_BAND (the TOP8 closings at r8 = 2, 4, 6 and in band 8, r8 <= 2851850); TAIL2_END8 proved for 646582 <= j <= 2072506 and the era law proved modulo the strictly smaller core TAIL2_END9 (the TOP8 totality at r8 = 2j, j >= 1425926 only, where the ninth descent is a new cascade with different constants); ESC_ERA_LAW_54
  Grind23.v                  the TOP8 ninth descent (Phase 55): CASCADE55 (the 17-step fixed parse at an arbitrary carried tail), TOP55_TO_TOP9, TOP55_2 / TOP55_4 / TOP55_6 / TOP55_BAND (the TOP9 closings at r9 = 2, 4, 6 and in band 9, r9 <= 5703706); TAIL2_END9 proved for 1425926 <= j <= 4277778 and the era law proved modulo the strictly smaller core TAIL2_END10 (the TOP9 totality at r9 = 2j, j >= 2851854 only, where the tenth descent is a new cascade with different constants); ESC_ERA_LAW_55
  Grind24.v                  the TOP9 tenth descent (Phase 56): CASCADE56 (the 799-step fixed parse at an arbitrary carried tail), TOP56_TO_TOP10, TOP56_2 / TOP56_4 / TOP56_6 / TOP56_BAND (the TOP10 closings at r10 = 2, 4, 6 and in band 10, r10 <= 11874954); TAIL2_END10 proved for 2851854 <= j <= 8789330 and the era law proved modulo the strictly smaller core TAIL2_END11 (the TOP10 totality at r10 = 2j, j >= 5937478 only, where the eleventh descent is a new cascade with different constants); ESC_ERA_LAW_56
  Grind25.v                  the TOP10 eleventh descent (Phase 57): CASCADE57 (the 17-step fixed parse at an arbitrary carried tail), TOP57_TO_TOP11, TOP57_2 / TOP57_4 / TOP57_6 / TOP57_BAND (the TOP11 closings at r11 = 2, 4, 6 and in band 11, r11 <= 23749914); TAIL2_END11 proved for 5937478 <= j <= 17812434 and the era law proved modulo the strictly smaller core TAIL2_END12 (the TOP11 totality at r11 = 2j, j >= 11874958 only, where the twelfth descent is a new cascade with different constants); ESC_ERA_LAW_57
  Grind26.v                  the TOP11 twelfth descent, part 1 (Phase 58): CASCADE58a-g (steps 1-336 of the 490-step fixed parse at an arbitrary carried tail), the factored numeral identities NUM58 / NUM58X and repeat-list identities REP58
  Grind26a.v                 the Phase 58 factored closed facts (Phase 58): the CASCADE58r singleton identities S58r1 / S58r2, the TOP11-front identities S58f1-f3 and the hGRIND_even 14701544 side goals S58g1 / S58g2, each proved once by eqb / leb + vm_compute
  Grind26b.v                 the TOP11 twelfth descent, part 2 (Phase 58): CASCADE58h-r (steps 337-490) and the composition CASCADE58
  Grind26c.v                 TOP58_TO_TOP12 (Phase 58): the TOP11 front onto GRIND12, the DIPGRIND (11874954, 2(j - 11874957)) landing on the DIP12 spine, then CASCADE58 onto the TOP12 state
  Grind26d.v                 TOP58_2 (Phase 58): the TOP12 closing at r12 = 2
  Grind26e.v                 TOP58_4 (Phase 58): the TOP12 closing at r12 = 4
  Grind26f.v                 TOP58_6 (Phase 58): the TOP12 closing at r12 = 6
  Grind26g.v                 TOP58_BAND (Phase 58): the TOP12 closing in band 12 (r12 <= 58806190, by CLEANG_even at counter 29403092); TAIL2_END12 proved for 11874958 <= j <= 41278052 and the era law proved modulo the strictly smaller core TAIL2_END13 (the TOP12 totality at r12 = 2j, j >= 29403096 only, where the thirteenth descent is a new cascade with different constants); ESC_ERA_LAW_58
  Grind27.v                  the TOP12 thirteenth descent, part 1 (Phase 59): CASCADE59a-j (segments a-j of the 586-step fixed parse at an arbitrary carried tail; the frame is replaced, eleven blocks becoming nine), the factored numeral identities NUM59X and repeat-list identities REP59
  Grind27a.v                 the Phase 59 factored closed facts, part 1 (Phase 59): the TOP12-front identities S59f1-f3, the DIPGRIND side goal S59a1 and the hGRIND_even 29403093 side goal S59g0, each proved once by eqb / leb + vm_compute
  Grind27h.v                 the Phase 59 factored closed facts, part 2 (Phase 59): the hGRIND_even 29403093 side goals S59g1 / S59g2, the TOP13-front goal S59h0 and the successor identities NUM59b / NUM59e, each proved once by eqb / leb + vm_compute
  Grind27i.v                 the Phase 59 factored closed facts, part 3 (Phase 59): the split-addend identities S59rs1 / S59rs2 (frame splits for the factored big-pop steps) and S59ru1 (the counter split behind S59ru2), each proved once by eqb + vm_compute
  Grind27j.v                 NUM59a (Phase 59): the identity 58806190 = 2 * 29403093 + 4, proved by splitting the addend (29403093 = 14701546 + 14701547), reshaping symbolically by a variable-only ring identity, and evaluating only the right-associated sum (Nat.add is not tail-recursive in the VM, so the direct form OOM-kills)
  Grind27k.v                 the Phase 59 successor identities NUM59f / NUM59g, each proved once by eqb + vm_compute (at most two 58.8M-scale identities per file)
  Grind27l.v                 the Phase 59 identities NUM59h / NUM59i, each proved once by eqb + vm_compute
  Grind27m.v                 the Phase 59 identities NUM59j / NUM59k, each proved once by eqb + vm_compute
  Grind27n.v                 the Phase 59 identities NUM59m / NUM59n, each proved once by eqb + vm_compute
  Grind27o.v                 S59ru2 (Phase 59): the identity 58806191 = 3 + 2 * 29403094, proved by the same split-addend / symbolic-reshape pattern as NUM59a
  Grind27b.v                 the TOP12 thirteenth descent, part 2 (Phase 59): CASCADE59k-u (segments k-u) and the composition CASCADE59
  Grind27c.v                 TOP59_TO_TOP13 (Phase 59): the TOP12 front onto GRIND13, the DIPGRIND (29403092, 2(j - 29403095)) landing on the DIP13 spine, then CASCADE59 onto the TOP13 state
  Grind27d.v                 TOP59_2 (Phase 59): the TOP13 closing at r13 = 2
  Grind27e.v                 TOP59_4 (Phase 59): the TOP13 closing at r13 = 4
  Grind27f.v                 TOP59_6 (Phase 59): the TOP13 closing at r13 = 6
  Grind27g.v                 TOP59_BAND (Phase 59): the TOP13 closing in band 13 (r13 <= 117612386, by CLEANG_even at counter 58806190); TAIL2_END13 proved for 29403096 <= j <= 88209288 and the era law proved modulo the strictly smaller core TAIL2_END14 (the TOP13 totality at r13 = 2j, j >= 58806194 only, where the fourteenth descent is a new cascade with different constants); ESC_ERA_LAW_59
  Grind28.v                  the TOP13 fourteenth descent, part 1 (Phase 60): CASCADE60a-e (segments a-e of the 663-step fixed parse at an arbitrary carried tail; the frame neither grows nor shrinks, nine blocks becoming nine)
  Grind28ag.v                the CASCADE60 prelude (Phase 60): the factored numeral identities NUM60X1-X66 and the repeat-list identity REP60, proved once and used via plain rewrite (split into its own file: the prelude alone peaks ~4.8 GB)
  Grind28ah.v                the TOP13 fourteenth descent, part 2 (Phase 60): CASCADE60f-j (segments f-j)
  Grind28j.v                 the TOP13 fourteenth descent, part 3 (Phase 60): CASCADE60k-q (segments k-q)
  Grind28ai.v                the TOP13 fourteenth descent, part 4 (Phase 60): CASCADE60r (a factored big-pop singleton)
  Grind28ak.v                the TOP13 fourteenth descent, part 5 (Phase 60): CASCADE60s1 (segment s, first half; alone in its file - it peaks ~5.75 GB)
  Grind28al.v                the TOP13 fourteenth descent, part 6 (Phase 60): CASCADE60s2 (segment s, second half)
  Grind28aj.v                the TOP13 fourteenth descent, part 7 (Phase 60): CASCADE60t-v (factored singletons) and the composition CASCADE60
  Grind28a.v                 the Phase 60 factored closed facts, part 1 (Phase 60): the TOP13-front identities S60f1-f4 and the DIPGRIND side goal S60a1, each proved once by eqb / leb + vm_compute
  Grind28b.v                 the Phase 60 factored closed facts, part 2 (Phase 60): the hGRIND_even 67992616 side goals S60g1 / S60g2, each proved once by leb + vm_compute
  Grind28ae.v                the Phase 60 factored closed facts, part 3 (Phase 60): the TOP14-front goal S60h0, proved once by leb + vm_compute
  Grind28af.v                NUM60b (Phase 60): the successor identity 74737818 = S 74737817, proved once by eqb
  Grind28ad.v                NUM60g (Phase 60): the successor identity 74737819 = S 74737818, proved once by eqb
  Grind28q.v                 NUM60e' (Phase 60): the (V-1)-form identity 135985237 = S (135985237 - 1), proved by Nat.sub_1_r + Nat.succ_pred_pos + a single-chain leb (at 136M every two-chain evaluated comparison OOM-kills)
  Grind28r.v                 NUM60i' (Phase 60): the (V-1)-form identity 135985236 = S (135985236 - 1), same route as NUM60e'
  Grind28s.v                 the div/mod halves of NUM60n at k = 2^20 (Phase 60), each proved once by vm_compute
  Grind28w.v                 NUM60n (Phase 60): the identity 135985238 = S 135985237, proved by div/mod decomposition (X = Y from X/k = Y/k and X mod k = Y mod k, combined symbolically via Nat.div_mod_eq)
  Grind28t.v                 the div/mod halves of NUM60m1 at k = 2^20 (Phase 60), each proved once by vm_compute
  Grind28x.v                 NUM60m1 (Phase 60): the identity 135985239 = S 135985238, proved by div/mod decomposition
  Grind28u.v                 the div/mod halves of NUM60m at k = 2^20 (Phase 60), each proved once by vm_compute
  Grind28y.v                 NUM60m (Phase 60): the identity 135985240 = S 135985239, proved by div/mod decomposition
  Grind28f.v                 the div/mod halves of NUM60h at k = 2^20 (Phase 60), each proved once by vm_compute
  Grind28h.v                 NUM60h (Phase 60): the identity 135985236 = 135985237 - 1, proved by div/mod decomposition
  Grind28g.v                 the div/mod halves of NUM60k at k = 2^20 (Phase 60), each proved once by vm_compute
  Grind28z.v                 NUM60k (Phase 60): the identity 135985236 = 135985239 - 3, proved by div/mod decomposition
  Grind28e.v                 the div/mod halves of NUM60f' at k = 2^20 (Phase 60), each proved once by vm_compute
  Grind28k.v                 NUM60f' (Phase 60): the identity 135985238 = S (S (135985237 - 1)), proved by div/mod decomposition
  Grind28v.v                 the div/mod halves of NUM60j' at k = 2^20 (Phase 60), each proved once by vm_compute
  Grind28aa.v                NUM60j' (Phase 60): the identity 135985237 = S (S (135985236 - 1)), proved by div/mod decomposition
  Grind28d.v                 the div/mod halves of NUM60a at k = 2^20 (Phase 60), each proved once by vm_compute
  Grind28ab.v                NUM60a (Phase 60): the identity 135985236 = 2 * 67992616 + 4, proved by div/mod decomposition with the sum side decomposed symbolically per summand (never evaluated whole)
  Grind28i.v                 the div/mod halves of S60rv2 at k = 2^20 (Phase 60), each proved once by vm_compute, and S60rv3 (2 <= 18372853)
  Grind28ac.v                S60rv2 (Phase 60): the identity 135985237 = 18372853 + 2 * 58806192, proved by div/mod decomposition with the sum side decomposed symbolically per summand
  Grind28c.v                 the Phase 60 frame-split identities (Phase 60): S60rr1-3, S60rt1-3, S60rv1 for the factored final-pop steps, plain-proved
  Grind28am.v                P660 (Phase 60): the CLEANG_odd premise 9186421 + 2 <= 15931624 of CASCADE60 step 660, proved by the VM-cast leb route (closearith's lazy-leb fallback is a conversion bomb at this scale)
  Grind28l.v                 TOP60_TO_TOP14 (Phase 60): the TOP13 front onto GRIND14, the DIPGRIND (58806190, 2(j - 58806193)) landing on the DIP14 spine, then CASCADE60 onto the TOP14 state
  Grind28m.v                 TOP60_2 (Phase 60): the TOP14 closing at r14 = 2
  Grind28n.v                 TOP60_4 (Phase 60): the TOP14 closing at r14 = 4
  Grind28o.v                 TOP60_6 (Phase 60): the TOP14 closing at r14 = 6
  Grind28p.v                 TOP60_BAND (Phase 60): the TOP14 closing in band 14 (r14 <= 271970478, by CLEANG_even at counter 135985236); TAIL2_END14 proved for 58806194 <= j <= 194791432 and the era law proved modulo the strictly smaller core TAIL2_END15 (the TOP14 totality at r14 = 2j, j >= 135985240 only, where the fifteenth descent is a new cascade with different constants); ESC_ERA_LAW_60
  Grind29.v                  the TOP14 fifteenth descent, part 1 (Phase 61): CASCADE61a (the first segment of the 1153-step fixed parse at an arbitrary carried tail; the frame grows from nine blocks to thirteen)
  Grind29g1.v-Grind29g24.v   the TOP14 fifteenth descent, parts 2-25 (Phase 61): CASCADE61b-CASCADE61ao (the remaining segments but the last)
  Grind29j.v                 the TOP14 fifteenth descent, part 26 (Phase 61): CASCADE61ap and the composition CASCADE61
  Grind29rep.v               the CASCADE61 prelude (Phase 61): the factored repeat-list identities REP61a-h and their numeral certificates (div/mod values certified by Horner/nia equations + the uniqueness lemmas, no evaluated comparisons - at this scale every evaluation materialises a ~4 GB unary chain)
  Grind29s.v                 the factored closed identities S61r for the big pop12 singletons of CASCADE61 (Phase 61), by the Horner/nia route
  Grind29e1.v-Grind29e14.v   the CASCADE61 numeral prelude (Phase 61): the factored identities NUM61X1-NUM61X133, each proved once by the Horner/nia route and used via plain rewrite
  Grind29m1.v, Grind29m2.v   the pre-proved leb premises P61s/P61u for the big-floor CLEANG / hGRIND steps of CASCADE61 (Phase 61)
  Grind29c1.v-Grind29c14.v   the Phase 61 div/mod certificates (Phase 61): for each tail identity, E (the Horner/nia equation expr = 1048576 * q + r), HLT (r < 1048576) and the div/mod values by Nat.div_unique / Nat.mod_unique
  Grind29a.v                 the Phase 61 factored closed identities (Phase 61): the TOP14-front identities S61f1-f3 and the TOP15 S-identities NUM61h / NUM61b / NUM61e' / NUM61f' / NUM61g / NUM61i' / NUM61j' / NUM61k / NUM61m / NUM61n, each proved by div/mod decomposition at k = 2^20 from the Grind29c* certificates
  Grind29ab.v                NUM61a (Phase 61): the hGRIND_even bridge 271970478 = 2 * 135985237 + 4 of the TOP15 closings, by div/mod decomposition (the NUM60a pattern)
  Grind29h.v                 the Phase 61 symbolic helpers (Phase 61): S_sub_1_61 (V = S (V - 1) for V >= 1), ADD2S, R61ssB, DIVEQ, and the closed premises S61a1 / S61h0 / S61g1 / S61g2, by the Horner/nia route
  Grind29l.v                 TOP61_TO_TOP15 (Phase 61): the TOP14 front onto GRIND15, the DIPGRIND (135985236, 2(j - 135985239)) landing on the DIP15 spine, then CASCADE61 onto the TOP15 state
  Grind29m.v                 TOP61_2 (Phase 61): the TOP15 closing at r15' = 2 (TRANS2_1 + CASCADE_POPFIN)
  Grind29n.v                 TOP61_4 (Phase 61): the TOP15 closing at r15' = 4 (TUP + hGRIND_even 135985237 + TRANS2_2 + CASCADE_POPFIN)
  Grind29o.v                 TOP61_6 (Phase 61): the TOP15 closing at r15' = 6 (TUP + hGRIND_even 135985237 + TUP2_1 + TDN + TRANS2_1 + CASCADE_POPFIN)
  Grind29p.v                 TOP61_BAND (Phase 61): the TOP15 closing in band 15 (r15' <= 543940962, by CLEANG_even at counter 271970478); TAIL2_END15 proved for 135985240 <= j <= 407955720 and the era law proved modulo the strictly smaller core TAIL2_END16 (the TOP15 totality at r15 = 2j, j >= 271970482 only, where the sixteenth descent is a new cascade with different constants); ESC_ERA_LAW_61
  Loop.v                     cross-era loop assembly: PASS, both era iterations, LOOP_NONHALT, NONHALT_FROM_R (proved modulo one explicit hypothesis H_LOOP; general settled iteration unconditional for every 3 <= B2 <= 36; ESC iteration unconditional for every even R <= 1276 and modulo TAIL2_END16 above)
  Std.v                      standard-regime assembly: STD_reach_entry, H_STD discharged, NONHALT_FROM_R_std (proved)
  gen_configs.py             generator for Configs.v
  trace_rules.py             zipper traces used to fix the segment lemmas' forms
  trace_recoord.py           zipper traces for the Recoord/Era/Esc forms
  trace_dev.py               zipper traces for the Dev/Grind forms
  std_verify.py              pre-verification of the Std.v chain on the real machine
  era_gen_verify.py          pre-verification of the EraGen.v boundary sequences on the real machine
  era_even_verify.py         pre-verification of the EraEven.v boundary sequences on the real machine
  era_fence35_verify.py      fence evidence for residues rho >= 35 (observed absorptions + 60M-step budget checks)
  hsim36.py                  pre-verification of the Phase 36 step lists and deviated grinds (word simulator + machine recogniser)
  hsim37.py                  pre-verification of the Phase 37 merged unwind (word simulator + machine recogniser)
  hsim38.py                  pre-verification of the Phase 38 phase-6 unwind (word simulator + machine recogniser)
  hsim40.py                  pre-verification of the Phase 40 phase-7 unwind (word simulator + machine recogniser)
  hsim41.py                  pre-verification of the Phase 41 phase-8 entry/stages + the cascade fence evidence (word simulator + machine recogniser)
  hsim42.py                  stress test of CASCADE_LANDING: ~50 shrunk-family cascade landings on the era shape, the odd-residue parity fence, machine REGEN at the terminal (word simulator + machine recogniser)
  hsim43.py                  pre-verification of the Phase 43 stage decomposition: every stage boundary of the cascade asserted exactly on the shrunk family in the era (odd-r1) regime, both dispatch branches, the M = 618 stage-4 branch, and two stage-4 boundary landings (word simulator + machine recogniser)
  hsim44.py                  pre-verification of the Phase 44 stage-4 decomposition: every segment boundary (SEG1 / SEG2 / T1 / T2 / T3 clean+boundary / T4) asserted verbatim at nine stage-4 points on the general 3-block frame family, five T4-source points, and one growth probe (word simulator + machine recogniser)
  hsim45.py                  pre-verification of the Phase 45 era-slice tail: primitive walks from the tail source at four small points; macro walks (proved lemmas as macros) at seven era points in the clean range with every layer boundary and final counter asserted verbatim; boundary-regime completions at vM = 1653 / 2000 / 5366 (word simulator + machine recogniser)
  hsim46.py                  pre-verification of the Phase 46 descent: all 51 descent waypoints asserted verbatim, in order, at k in {1, 2, 3, 48, 348, 3713} x beta in {2, 3}; END parses and finals for k <= 3713; full TAIL2_BIG source walks for vM <= 5365; the k >= 3714 fence finals at k = 3714 / 5000 (word simulator + machine recogniser)
  hsim47.py                  pre-verification of the Phase 47 END re-descent: the 37-waypoint chain asserted verbatim, in order, at (k, beta) in {(3714, 2), (3714, 3), (3715, 2), (4000, 2), (5000, 3), (11142, 2), (11143, 2), (12000, 2)}; band finals asserted verbatim; the cycle-2 fence (GRIND2 state + second DIPGRIND landing) at k = 11143 / 12000 / 20000 (word simulator + machine recogniser)
  hsim48.py                  pre-verification of the Phase 48 TOP second descent: the 26-waypoint CASCADE48 chain asserted verbatim, in order, at (j, beta) in {(7430, 2), (7430, 3), (7431, 2), (8000, 2), (23730, 2), (23731, 2)} incl. a junk-tail probe; TOP2 band finals asserted verbatim at eight points; the third fence (GRIND3 state + third DIPGRIND landing) at j = 23731 / 24000 / 30000 (word simulator + machine recogniser)
  hsim49.py                  pre-verification of the Phase 49 TOP2 third descent: the 49-waypoint CASCADE49 chain asserted verbatim, in order, at (j, beta) in {(16302, 2), (16302, 3), (16303, 2), (20000, 2), (48906, 2)} incl. a junk-tail probe; TOP3 band finals asserted verbatim at eight points; the fourth fence (GRIND4 state + fourth DIPGRIND landing) at j = 48907 / 49000 / 60000 (word simulator + machine recogniser; streaming walker)
  hsim50.py                  pre-verification of the Phase 50 TOP3 fourth descent: the 82-waypoint CASCADE50 chain asserted verbatim, in order, at (j, beta) in {(32606, 2), (32606, 3), (32607, 2), (40000, 2), (99728, 2)} incl. a junk-tail probe; TOP4 band finals asserted verbatim at nine points; the fifth fence (GRIND5 state + fifth DIPGRIND landing) at j = 99729 / 99800 / 120000 (word simulator + machine recogniser; streaming walker)
  hsim51.py                  pre-verification of the Phase 51 TOP4 fifth descent: the 16-waypoint CASCADE51 chain asserted verbatim, in order, at (j, beta) in {(67124, 2), (67124, 3), (67125, 2), (100000, 2), (201372, 2)} incl. a junk-tail probe; TOP5 finals asserted verbatim; the sixth fence (GRIND6 state + sixth DIPGRIND landing) at j = 201373 / 201374 / 210000 (word simulator + machine recogniser; streaming walker)
  hsim52.py                  pre-verification of the Phase 52 TOP5 sixth descent: the 232-waypoint CASCADE52 chain asserted verbatim, in order, at (j, beta) in {(134250, 2), (134250, 3), (134251, 2), (200000, 2), (457538, 2)} incl. a junk-tail probe; TOP6 finals asserted verbatim; the seventh fence (GRIND7 state + seventh DIPGRIND landing) at j = 457539 / 457540 / 500000 (word simulator + machine recogniser; streaming walker)
  hsim53.py                  pre-verification of the Phase 53 TOP6 seventh descent: the 344-waypoint CASCADE53 chain asserted verbatim, in order, at (j, beta) in {(323290, 2), (323290, 3), (323291, 2), (400000, 2), (969870, 2)} incl. a junk-tail probe; TOP7 finals asserted verbatim; the eighth fence (GRIND8 state + eighth DIPGRIND landing) at j = 969871 / 969872 / 1000000 (word simulator + machine recogniser; streaming walker)
  hsim54.py                  pre-verification of the Phase 54 TOP7 eighth descent: the 183-waypoint CASCADE54 chain asserted verbatim, in order, at (j, beta) in {(646582, 2), (646582, 3), (646583, 2), (800000, 2), (2072506, 2)} incl. a junk-tail probe; TOP8 finals asserted verbatim; the ninth fence (GRIND9 state + ninth DIPGRIND landing) at j = 2072507 / 2072508 / 2200000 (word simulator + machine recogniser; streaming walker)
  hsim55.py                  pre-verification of the Phase 55 TOP8 ninth descent: the 24-waypoint CASCADE55 chain asserted verbatim, in order, at (j, beta) in {(1425926, 2), (1425926, 3), (1425927, 2), (2000000, 2), (4277778, 2)} incl. a junk-tail probe; TOP9 finals asserted verbatim; the tenth fence (GRIND10 state + tenth DIPGRIND landing) at j = 4277779 / 4277780 / 4500000 (word simulator + machine recogniser; streaming walker; executed span-sliced, 192 slice jobs all OK)
  hsim56.py                  pre-verification of the Phase 56 TOP9 tenth descent: the 799-waypoint CASCADE56 chain (run-length-encoded waypoint table, expanded lazily) asserted verbatim, in order, at (2851854, 2) incl. a junk-tail probe; the classified chain at (2851854, 3) identical on cascade steps 7-805 (beta-uniformity); TOP9 -> DIP10 front segments at five (j, beta) points; TOP10 finals asserted verbatim at eight points incl. the band edge j10 = 5937477; the eleventh fence (GRIND11 state + eleventh DIPGRIND landing) at j10 = 5937478 / 5937479 / 6148147 (word simulator + machine recogniser; streaming walker; canonical chain executed as checkpointed slice jobs)
  hsim57.py                  pre-verification of the Phase 57 TOP10 eleventh descent: the classifier validated by exact reproduction of the Phase 56 chain (807 steps, 0 mismatches); the 25-step classified chains at (5937478, 2) and (5937478, 3) waypoint-identical modulo the beta tail (beta-uniformity); TOP11 finals asserted verbatim at eight points incl. the band edge j11 = 11874957; the twelfth fence (GRIND12 state + twelfth DIPGRIND landing) at j11 = 11874958 / 11874959 / 12500000 (word simulator + machine recogniser; streaming walker; the span-sliced canonical/front/junk walk queues did not complete - see mechanisation-status.md)
  hsim58.py                  pre-verification of the Phase 58 TOP11 twelfth descent: the classifier validated by exact reproduction of the Phase 57 chain (25 steps, 0 mismatches); the 498-step classified chains at (11874958, 2) and (11874958, 3) waypoint-identical modulo the beta tail over all 490 cascade steps (beta-uniformity); TOP12 finals asserted verbatim at eight points incl. the band edge j12 = 29403095; the thirteenth fence (GRIND13 state + thirteenth DIPGRIND landing) at j12 = 29403096 / 29403097 / 30000000 (word simulator + machine recogniser; streaming walker; the span-sliced canonical/front/junk walk queues did not complete - see mechanisation-status.md)
  hsim59.py                  pre-verification of the Phase 59 TOP12 thirteenth descent: the classifier validated by exact reproduction of the Phase 58 chain (498 steps, 0 mismatches); the 594-step classified chains at (29403096, 2) and (29403096, 3) identical modulo the beta tail over steps 1..592 (front + all 586 cascade steps; beta-uniformity); TOP13 finals asserted verbatim at eight points incl. the band edge j13 = 58806193; the fourteenth fence (GRIND14 state + fourteenth DIPGRIND landing) at j13 = 58806194 / 58806195 / 60000000 (word simulator + machine recogniser; streaming walker; no span-sliced walk queues were built this phase - see mechanisation-status.md)
  hsim60.py                  pre-verification of the Phase 60 TOP13 fourteenth descent: the classifier validated by exact reproduction of the Phase 59 chain (594 steps, 0 mismatches); the 671-step classified chains at (58806194, 2) and (58806194, 3) identical modulo the beta tail over steps 1..669 (front + all 663 cascade steps; beta-uniformity); TOP14 finals asserted verbatim at eight points incl. the band edge j14 = 135985239; the fifteenth fence (GRIND15 state + fifteenth DIPGRIND landing) at j14 = 135985240 / 135985241 / 200000000 (word simulator + machine recogniser; streaming walker; no span-sliced walk queues were built this phase - see mechanisation-status.md)
  hsim61.py                  pre-verification of the Phase 61 TOP14 fifteenth descent: the classifier validated by exact reproduction of the Phase 60 chain (671 steps, 0 mismatches); the 1161-step classified chains at (135985240, 2) and (135985240, 3) identical modulo the beta tail over steps 1..1159 (front + all 1153 cascade steps; beta-uniformity); TOP15 finals asserted verbatim at eight points incl. the band edge j15 = 271970481; the sixteenth fence (GRIND16 state + sixteenth DIPGRIND landing) at j15 = 271970482 / 271970483 / 400000000, verified at classify granularity - the primitive walker OOMs inside the sixteenth DIPGRIND span (word simulator + machine recogniser; streaming walker; no span-sliced walk queues were built this phase - see mechanisation-status.md)
  mechanisation-status.md    component-by-component mechanisation status
  coqcw, env.sh              build wrapper for the authors' local Coq 8.18 toolchain
```

Not included: the internal project log (`NOTES.md`, Phases
1–42), simulators and run artefacts of the working phases, and
the still-running long simulation from R (component #7 is
corroboration only; the proof does not depend on it).

## How to verify

### 1. Read

`proof-summary-168016.md` (30 minutes) or `168016-proof.md`
with the files under `proof/`.

### 2. Run the independent reproduction

Requires Python 3 (standard library only). The checker reads
`phase10-expected.txt` from its working directory, so run it
from `reproduction/`:

```sh
cd reproduction
python3 reproduce_168016.py            # full suite
python3 reproduce_168016.py --quick    # skips the two longest simulations
```

Expected results (reference machine: 1.5 shared vCPUs):

- full: `==== SUMMARY: 75 PASS, 0 FAIL, 2 FINDING (232.3s) ====`, exit code 0
- `--quick`: `73 PASS, 0 FAIL, 2 FINDING` (the two skipped
  simulation checks are not counted)

The 2 FINDINGs are F-1 and F-2 above: the checker compares the
documents' originally printed corollary bound and CGAP2 cost
against the transition table and reports the slips exactly;
both are corrected as dated errata in the packaged documents.
A FINDING is not a FAIL: exit code is 0 iff no check FAILs.

*Package verification (2026-11-25):* the packaged copy was run
from this directory with `--quick`: **73 PASS, 0 FAIL,
2 FINDING, 85.2 s, exit code 0** — identical findings to the
reference run.

### 3. Build the Rocq development

Requires Coq **8.18.0** (the version used by the authors; the
pre-rename name of Rocq). Compile in dependency order:

```sh
cd rocq
coqc TM.v
coqc Configs.v
coqc Finite.v
coqc Sections.v
coqc Mirror.v
coqc TokenPass.v
coqc DiagPass.v
coqc Recoord.v
coqc Era.v
coqc EraGen.v
coqc Esc.v
coqc Dev.v
coqc Grind.v
coqc Grind2.v
coqc EraEven.v
coqc Grind3.v
coqc Grind4.v
coqc Grind5.v
coqc Grind6.v
coqc Grind7.v
coqc Grind8.v
coqc Grind9.v
coqc Grind10.v
coqc Grind11.v
coqc Grind12.v
coqc Grind13.v
coqc Grind14.v
coqc Grind15.v
coqc Grind16.v
coqc Grind17.v
coqc Grind18.v
coqc Grind19.v
coqc Grind20.v
coqc Grind21.v
coqc Grind22.v
coqc Grind23.v
coqc Grind24.v
coqc Grind25.v
coqc Grind26.v
coqc Grind26a.v
coqc Grind26b.v
coqc Grind26c.v
coqc Grind26d.v
coqc Grind26e.v
coqc Grind26f.v
coqc Grind26g.v
coqc Grind27a.v
coqc Grind27h.v
coqc Grind27i.v
coqc Grind27j.v
coqc Grind27k.v
coqc Grind27l.v
coqc Grind27m.v
coqc Grind27n.v
coqc Grind27o.v
coqc Grind27.v
coqc Grind27b.v
coqc Grind27c.v
coqc Grind27d.v
coqc Grind27e.v
coqc Grind27f.v
coqc Grind27g.v
coqc Grind28a.v
coqc Grind28b.v
coqc Grind28ae.v
coqc Grind28af.v
coqc Grind28ad.v
coqc Grind28q.v
coqc Grind28r.v
coqc Grind28s.v
coqc Grind28w.v
coqc Grind28t.v
coqc Grind28x.v
coqc Grind28u.v
coqc Grind28y.v
coqc Grind28f.v
coqc Grind28h.v
coqc Grind28g.v
coqc Grind28z.v
coqc Grind28e.v
coqc Grind28k.v
coqc Grind28v.v
coqc Grind28aa.v
coqc Grind28d.v
coqc Grind28ab.v
coqc Grind28i.v
coqc Grind28ac.v
coqc Grind28c.v
coqc Grind28am.v
coqc Grind28ag.v
coqc Grind28.v
coqc Grind28ah.v
coqc Grind28j.v
coqc Grind28ai.v
coqc Grind28ak.v
coqc Grind28al.v
coqc Grind28aj.v
coqc Grind28l.v
coqc Grind28m.v
coqc Grind28n.v
coqc Grind28o.v
coqc Grind28p.v
coqc Grind29c1.v
coqc Grind29c2.v
coqc Grind29c3.v
coqc Grind29c4.v
coqc Grind29c5.v
coqc Grind29c6.v
coqc Grind29c7.v
coqc Grind29c8.v
coqc Grind29c9.v
coqc Grind29c10.v
coqc Grind29c11.v
coqc Grind29c12.v
coqc Grind29c13.v
coqc Grind29c14.v
coqc Grind29h.v
coqc Grind29a.v
coqc Grind29ab.v
coqc Grind29e1.v
coqc Grind29e2.v
coqc Grind29e3.v
coqc Grind29e4.v
coqc Grind29e5.v
coqc Grind29e6.v
coqc Grind29e7.v
coqc Grind29e8.v
coqc Grind29e9.v
coqc Grind29e10.v
coqc Grind29e11.v
coqc Grind29e12.v
coqc Grind29e13.v
coqc Grind29e14.v
coqc Grind29rep.v
coqc Grind29s.v
coqc Grind29m1.v
coqc Grind29m2.v
coqc Grind29.v
coqc Grind29g1.v
coqc Grind29g2.v
coqc Grind29g3.v
coqc Grind29g4.v
coqc Grind29g5.v
coqc Grind29g6.v
coqc Grind29g7.v
coqc Grind29g8.v
coqc Grind29g9.v
coqc Grind29g10.v
coqc Grind29g11.v
coqc Grind29g12.v
coqc Grind29g13.v
coqc Grind29g14.v
coqc Grind29g15.v
coqc Grind29g16.v
coqc Grind29g17.v
coqc Grind29g18.v
coqc Grind29g19.v
coqc Grind29g20.v
coqc Grind29g21.v
coqc Grind29g22.v
coqc Grind29g23.v
coqc Grind29g24.v
coqc Grind29j.v
coqc Grind29l.v
coqc Grind29m.v
coqc Grind29n.v
coqc Grind29o.v
coqc Grind29p.v
coqc Loop.v
coqc Std.v
```

(With the authors' workspace toolchain, `./coqcw <file>` does
the same via `env.sh`.) Expected: all one hundred and seventy files compile with
**no errors**; the only warnings are benign large-nat-literal
notices in `Finite.v`. Every headline lemma was checked with
`Print Assumptions`: "Closed under the global context" — no
axioms, no admits.

*Package verification (2026-11-28):* the packaged sources were
copied to a clean directory and rebuilt from scratch: **all
one hundred and seventy files compiled successfully**, producing `.vo` files
identical in size to the authors' build (re-verified after the
Phase 61 mechanisation update).

## Authorship and disclosure

Proof developed by Naoki Tsugawa with the assistance of an AI
agent (J.A.R.V.I.S.); the derivations, computations, checker
and Rocq sources are all included above so that every step can
be checked independently. Corrections, if any are needed, will
be issued as dated errata, as was done for findings F-1/F-2
(and F-3, a defect-landing slip found during the Phase 28
mechanisation and corrected in `proof/phase21-derivations.md`).
