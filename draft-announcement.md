# Draft announcements — #168016 does not halt

**Status: DRAFTS — nothing has been posted.** Prepared 2026-11-25
(Phase 24) for the user's own submission. Replace every
`<...>` placeholder before posting.

**Facts box (check before posting)**

| | |
|---|---|
| Machine | `1RB1RA_1RC1LB_0LD0RA_1RF1LE_---1LF_1LC0LF` |
| bbchallenge seed-database ID | **168016** (also its index in the 2026-10-30 BB(6) holdout list of 608) |
| Result | Does **not** halt (halts iff state E reads a 0) |
| Proof status | Complete human-level proof, unconditional; independently reproduced (75 checks, 0 failures, 2 theorem-irrelevant findings, both corrected as dated errata); Rocq mechanisation **in progress** — non-halting from the record configuration R is assembled modulo one explicit hypothesis (loop iteration at the remaining entry sections); the blank-tape → R transient is **not** yet mechanised |
| Package | `<PACKAGE URL>` |

---

## A. Forum post — the primary route

*Where:* the bbchallenge forum, https://discuss.bbchallenge.org,
category **"Individual machines"** ("the place to share proofs of
non-termination or termination of specific machines").
Per https://bbchallenge.org/contribute ("Write proofs →
Individual machines"), the post title must indicate the ID in the
seed database of the machine being decided.

*Suggested title:*

```
168016: 1RB1RA_1RC1LB_0LD0RA_1RF1LE_---1LF_1LC0LF does not halt
```

*Body:*

---

**Result.** The BB(6) holdout **168016**,
`1RB1RA_1RC1LB_0LD0RA_1RF1LE_---1LF_1LC0LF`, does not halt.
The only undefined transition is E-on-0, so everything reduces to
controlling the contexts in which state E can read a 0. A case
analysis of the entry routes (lemmas M1–M4) shows: *the machine
halts iff some F-on-0 read has left triple (0,1,0)* — and the
proof shows this pattern never occurs.

**Proof outline.**

1. *Transient.* Two "bounce families" S(k) and S′(m) with the
   period law P = 3·2^((k+4)/2) − 6 carry the blank tape forward.
   The S period law is verified for 27 periods and then *breaks*
   at k = 56; the S′ period is proved for all even m ≤ 130
   (Interval and Return Lemmas). At m = 132 the cascade deviates
   analytically, and a 403,455-step computed segment reaches the
   record configuration R = `1^17 0 1^97 0 1^137 0` at step
   1,770,887,431,134,099,605,707.
2. *Two-regime pushdown dynamics.* After R, the trajectory is
   governed by derived word-level rule systems: a standard regime
   (TDN/PUSH/POP/TUP + Stage A, invariant I) and a mirror regime
   at the right edge (five mirror rules, invariant RI), organised
   in eras. Every rule is proved from an explicit step list; the
   token-pass analysis (Cycle Lemma) shows the mirror regime
   always exits at β = 2, and the continuation re-coordinatises
   into the standard regime — including the boundary/deviation
   excursions of the later loop iterations (PUSHX, PX2A/PX2B,
   TRANS2/TUP2, CGAP2), all derived.
3. *Ascending loop.* One full loop maps the mirror parameter
   β ↦ 2β + 34 (settled form; the exceptional first iterations
   have their own derived maps). β strictly increases and the
   tape span grows at every iteration, so no configuration ever
   repeats; with the halt criterion, the machine never halts.

**Verification.**

- The proof is a complete human-level proof (no remaining
  hypotheses); the full text and all derivation files are in the
  package: `<PACKAGE URL>`.
- It has been **independently reproduced** with a clean-room
  checker written from the proof documents alone
  (`reproduce_168016.py`): 75 checks, **0 failures** — ≈186,000
  sections classified rule-by-rule against a fresh simulator,
  > 3×10⁸ steps of direct simulation, all headline numbers
  recomputed exactly, including held-out parameter values.
  The reproduction found two discrepancies, both in statements
  the theorem does not use (a ×1000 slip in the last addend of
  the finite corollary bound, and a cost-accounting slip for
  CGAP2, a rule proved never to fire in era grinds); both are
  corrected as dated errata in the proof documents and reported
  in full in `reproduction-report.md`.
- A **Rocq (Coq 8.18) mechanisation is in progress**: the halt
  criterion M1–M4 is fully proved; the finite segments
  (D(132,66) → R in 403,455 steps, formation in 150 steps,
  T(4) = 102, T(8) = 2,850, small S/S′ arrivals) are verified by
  kernel computation; all three rule systems (the five standard
  rules and REGEN, the five mirror rules, and the complete
  deviation system) are proved sound for all parameters; the
  token pass, the general β = 2 exit, and the
  re-coordinatisation are proved in full; both era laws are
  proved (the settled era β ↦ 2β + 34, also at general odd
  residue ρ ≤ 33; the ESC era β ↦ 2β + 4 for every even
  R ≤ 114); and the cross-era loop is assembled: non-halting
  from the record configuration R is proved modulo one
  explicit hypothesis (iteration at the entry sections not yet
  discharged: ESC entries at R ≥ 116, even or large residues,
  iterations ≥ 3) — all with no axioms or admits. The
  blank-tape → R transient (the S/S′ families and the two
  large finite segments) is **not yet mechanised**;
  `rocq/mechanisation-status.md` in the package maps every
  component to its status. A busycoq submission is the
  intended next step once the mechanisation is complete.

I would welcome independent checks and questions. The fastest
way to gain confidence is to run the reproduction checker
(≈4 minutes) and read `proof-summary-168016.md`.

— `naoki-tsugawa` (proof developed with the assistance
of an AI agent, J.A.R.V.I.S.; all computations and derivations
are included in the package for checking)

---

## B. Discord announcement (short)

*Where:* the bbchallenge Discord server (the community's main
discussion venue), in the BB(6)-related channel. Post after the
forum post, linking to it.

---

Hi all — we've proved that BB(6) holdout **168016**
(`1RB1RA_1RC1LB_0LD0RA_1RF1LE_---1LF_1LC0LF`) **does not halt**.
The proof reduces halting to one tape pattern (an F-on-0 read
with left triple (0,1,0), lemmas M1–M4) and shows the post-R
dynamics is an ascending loop of derived rule systems
(β ↦ 2β + 34), so the pattern never occurs. The human-level
proof is complete and was independently reproduced by a
clean-room checker (75/75 checks); a Rocq mechanisation is in
progress (M1–M4 and the finite segments done). Full write-up,
proof files, checker and Rocq sources: `<PACKAGE URL>` —
forum post: `<FORUM POST URL>`. Happy to answer questions!

---

## C. Wiki page draft

*Where:* https://wiki.bbchallenge.org — one page per machine,
titled by the machine string:
`1RB1RA_1RC1LB_0LD0RA_1RF1LE_---1LF_1LC0LF`.
(No page for this machine exists yet — checked 2026-11-25.)
Wiki pages for other holdouts follow the format below; creating
the page is usually done once a proof has been announced on the
forum, by the author or by community editors.

---

`1RB1RA_1RC1LB_0LD0RA_1RF1LE_---1LF_1LC0LF` (bbch)
(bbchallenge ID **168016**) is a six-state, two-symbol Turing
machine from the list of BB(6) holdouts. Started on a blank
tape, it **does not halt**. A human-level proof has been
announced on the forum (`<FORUM POST URL>`), independently
reproduced by a clean-room checker; a machine-checked Rocq
proof is in preparation (foundation components proved).

The machine's only undefined transition is E reading a 0.
After a long transient through two bounce families, the tape
settles into a two-regime pushdown dynamics whose eras grow
without bound, so the run never repeats and never halts.

## Summary

| Result | Does not halt (human proof announced; Rocq mechanisation in progress) |
| --- | --- |
| bbchallenge ID | 168016 |
| Behaviour | Two bounce families, then a two-regime pushdown dynamics in eras; loop map β ↦ 2β + 34 |
| Post-R entry point | record tape R = `1^17 0 1^97 0 1^137 0` reached at step 1,770,887,431,134,099,605,707 |
| Proofs | Human proof + independent reproduction (package: `<PACKAGE URL>`); Rocq foundation (M1–M4, finite segments, four standard rules) |

## Transition table

|  | 0 | 1 |
| --- | --- | --- |
| A | 1RB | 1RA |
| B | 1RC | 1LB |
| C | 0LD | 0RA |
| D | 1RF | 1LE |
| E | --- | 1LF |
| F | 1LC | 0LF |

The machine halts when it is in state E and reads a 0. E is
entered only from D reading a 1. Following the entry routes
(lemmas M1–M4 of the proof): the machine halts iff some F-on-0
read has left triple (0,1,0).

## Proof of non-halting

1. **Transient.** Families S(k) and S′(m) (tape
   `1^4 0 1^17 0 1^27 0 1^k 0`, resp.
   `1^4 0 1^41 0 1^65 0 1^m 0`) share the period law
   P = 3·2^((k+4)/2) − 6. The S law breaks at k = 56; the S′
   period is proved for all even m ≤ 130. At m = 132 the
   cascade reaches D(132,66) and deviates; 403,455 computed
   steps reach R = `1^17 0 1^97 0 1^137 0`.
2. **Standard regime.** From R the machine enters a system of
   five derived rules (TDN, PUSH, POP, TUP, Stage A) on a stack
   of gap/run pairs, under invariant I; only Stage A changes
   the long gap G, by exactly −2.
3. **Mirror regime and exit.** At G = 2 the machine enters a
   mirror rule system at the right edge. The token pass
   (Cycle Lemma) lowers the cycle floor of β by exactly 1 per
   cycle, so β = 2 is reached and the machine exits,
   event-clean, at the tokenless home section.
4. **Re-coordinatisation and era.** The continuation returns
   to the standard regime in a single-block frame; the era is
   evaluated in closed form (s₁ = 2β_E + 31 via the general
   POP rule and the Grind Lemma), and the next mirror entry is
   β′ = 2β_E + 34. Boundary and deviation excursions of the
   later iterations (PUSHX, PX2A/PX2B, TRANS2/TUP2, CGAP2) are
   derived in all cases.
5. **Ascent.** β strictly increases and the span grows at
   every loop iteration, so no configuration repeats; by the
   halt criterion the machine never halts.

## Proof status

- **Human proof:** complete and unconditional; announced on
  the forum (`<FORUM POST URL>`).
- **Independent reproduction:** clean-room checker, 75 checks,
  0 failures; two theorem-irrelevant discrepancies found and
  corrected as errata (finite corollary bound; CGAP2 cost
  accounting).
- **Rocq (Coq 8.18):** in progress — M1–M4 fully proved;
  finite segments kernel-verified; TDN/PUSH/POP-general/
  Stage A proved for all parameters; full theorem not yet
  assembled. Not yet submitted to busycoq.

## References

- Proof package (proof text, derivation files, reproduction
  checker and report, Rocq sources): `<PACKAGE URL>`
- Forum announcement: `<FORUM POST URL>`

---

## D. What the user must do to actually submit

Nothing below has been done yet; all accounts and posts are the
user's own actions (or need the user's explicit authorisation).

1. **Decide the credit name.** Choose the name/handle the proof
   should be credited to (forum username; the wiki and the
   monthly TMBR roundups credit contributors by handle).
   Replace `<YOUR FORUM USERNAME>` in draft A.
2. **Host the package.** Create a public repository (e.g. a new
   GitHub repo) and upload the contents of this `submission/`
   folder, or prepare to attach the files to the forum post.
   Put the resulting URL in place of every `<PACKAGE URL>`.
   (Optional but recommended: tag the upload, e.g. `v1.0`, so
   later corrections — errata, mechanisation progress — are
   visible as new versions rather than silent edits.)
3. **Forum account.** If you don't have one, sign up at
   https://discuss.bbchallenge.org (Discourse; sign-up options
   are shown on the site).
4. **Post the announcement.** On the forum: *New Topic* →
   category **Individual machines** → title from draft A (it
   contains the seed-database ID 168016, as the contribute page
   requires) → paste the body of draft A → publish. Copy the
   post's URL into `<FORUM POST URL>`.
5. **(Optional) Discord.** Join the bbchallenge Discord server
   (linked from https://bbchallenge.org) and post draft B in
   the BB(6) discussion channel.
6. **(Optional) Wiki page.** Create a wiki account at
   https://wiki.bbchallenge.org and create the page titled
   `1RB1RA_1RC1LB_0LD0RA_1RF1LE_---1LF_1LC0LF` from draft C —
   or leave it to community editors, who commonly create these
   pages once a proof is announced.
7. **Answer reviewers.** Expect questions on the forum thread;
   the proof documents and the reproduction checker are the
   reference. If a genuine gap is found, correct it openly with
   a dated erratum (the same policy used for findings F-1/F-2)
   and update the package.
8. **Later — busycoq.** Once the Rocq mechanisation is complete
   (all components in `rocq/mechanisation-status.md`), port the
   final theorem to the BusyCoq repository's definitions and
   submit it as a pull request there (recent BB(6) proofs were
   submitted this way as single files under `verify/`, named
   `M_<machine>.v`). **Not yet:** the current Rocq files are a
   foundation in our own framework, not a complete proof, and
   must not be submitted as one.
9. **Credit recording.** Once the community accepts the proof,
   the machine is marked decided in the BB(6) holdout tracking
   (wiki page + TMBR monthly roundup); no separate application
   is needed beyond the forum post.
