#!/usr/bin/env python3
"""Phase 42 verification: the totality/landing candidate for the
phase-8 ESC cascade (the fence left by Phase 41).

THE CANDIDATE.  Phase 41 mechanised the phase-8 entry and stages
A-C (Grind9.v, PHASE8_TO_STAGE_D), landing on

    HC [5] 13 1 2 ((1, 2) :: (1, 1) :: R2) 1,
    R2 = (1, 2) :: (1, 2) :: (1, 2)^40 ++
         ((149, 2) :: (1, 1) :: (1, 2) :: (1, 2) ::
          (1, 2)^334 ++ ((2M - 1230, 2) :: (1, 1) ::
          (1, 2)^(beta - 1))),      M >= 616, beta >= 2,

and fenced the continuation as a full-stack cascade ending stuck
at a B-section over the empty stack, "not an era REGEN landing".
Phase 42 re-examines that reading.  The word walk's terminal
config IS the era-landing shape

    HB pb a 1 (2*beta + 1) [] 1,   beta <= a,

i.e. exactly the target of every ESC_TO_REGEN_* lemma (Phases
29-41) and the source of Grind2.ERA_TAIL, which closes the era
at machine level for ARBITRARY pb via REGEN_gen.  Phase 41's own
machine trace from the terminal config confirms it: at cost
4*s + 22 = 74 the machine is at HC pb a 1 2 [] (s - 1) -- the
REGEN_gen landing -- followed by TDN and the era tail.  The word
model has no hstep there only because hREGEN is stated at
pb = [] and hSTGA needs G >= 3; the era assembly never needed a
word step at that config.

CANDIDATE STATEMENT (CASCADE_LANDING, Grind10.v): for all
M >= 616 and beta >= 2 there exist pb, a with beta <= a and

    hsteps (HC [5] 13 1 2 (stage-D stack M beta) 1)
           (HB pb a 1 (2*beta + 1) [] 1).

This file stress-tests the shrunk family

    S(n1, r1, n2, r2, b) =
      (1,2) :: (1,1) :: (1,2) :: (1,2) :: (1,2)^n1 ++
      (r1,2) :: (1,1) :: (1,2) :: (1,2) :: (1,2)^n2 ++
      (r2,2) :: (1,1) :: (1,2)^(b-1)

(the hsim41 analogue is S(7, 22, 3, 26, 6)):

  * Part 1: base point + one-at-a-time sweeps over every
    parameter (including ODD r1 -- the real residue is 149 --
    and odd r2, out-of-family robustness).  Every completed
    walk must terminate at HB pb a 1 (2b+1) [] 1 with a >= b,
    using ONLY proved hstep constructors (histogram audit: the
    unmechanised hsim rows PX2A0_b3/b4 must never fire).
  * Part 2: edge cases -- n2 = 0 / n2 = 1 (different stage
    parses), r2 = 2 (the M = 616 residue; shorter cascade),
    the minimal corner S(0, 6, 3, 2, 2).
  * Part 2b: the parity fence.  For ODD r2 (out of family --
    the era residue 2M - 1230 is always even) the walk still
    lands on a B-section over the empty stack with G = 1, but
    the shuttle is s = 2b + r2, NOT 2b + 1: the closed form
    beta' = 2 beta + 4 is an even-residue phenomenon.  This is
    the one place the stress test REFUTED a stronger candidate
    (all r2), and it is why CASCADE_LANDING keeps the era
    family's parity.  Odd r2 is asserted against its own law
    s = 2b + r2 below.
  * Part 3: machine-level confirmation at the terminal: from
    HB pb a 1 s [] 1 the raw machine reaches the REGEN_gen
    landing HC pb a 1 2 [] (s - 1) at cost 4s + 22 (the
    ERA_TAIL entry), at several parameter points.
  * Part 4: growth probes.  Word-walk length grows
    exponentially in the segment grind parameters (the nested
    hGRIND recursion), so the real point (40, 149, 334, 2M-1230)
    is beyond primitive walking -- those walks are run with a
    cap and must show CAP (still walking, rules applicable),
    never STUCK and never a wrong landing.  The Rocq proof
    route is induction (LOOPN / DIPDESC / GG_rounds), not
    walking; the shrunk family + affine boundary fits are the
    evidence for the statement's uniformity.

Run:  python3 hsim42.py     (all checks assert; prints PASS lines)
"""
import os
import sys
from collections import Counter

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from hsim36 import recognise
from hsim40 import hb
from hsim41 import step_all

PROVED_RULES = {
    'TDN', 'PUSH', 'PUSHX', 'PX2A', 'PX2A2', 'PX2B0', 'PX2B2',
    'PX2B3', 'PX2B4', 'PX2B5', 'PX2B6', 'PX2A0', 'PX2Bgen',
    'CGAP2pop', 'CGAP2push', 'POP', 'TUP', 'STGA', 'REGEN',
    'TRANS2_1', 'TRANS2_2', 'TUP2_1', 'TUP2def',
}


def stageD(n1, r1, n2, r2, b):
    stack = [(1, 2), (1, 1), (1, 2), (1, 2)] + [(1, 2)] * n1 \
        + [(r1, 2), (1, 1), (1, 2), (1, 2)] + [(1, 2)] * n2 \
        + [(r2, 2), (1, 1)] + [(1, 2)] * (b - 1)
    return ('C', (5,), 13, 1, 2, tuple(stack), 1)


def walk(src, max_rules=3000000):
    """Returns (status, terminal, nrules, histogram, nbounds).
    status 'DONE': no hstep rule applies at the terminal (the
    cascade's landings are DONE configs: hREGEN is pb = [] only
    and hSTGA needs G >= 3, so the era-landing shape is terminal
    in the word model by design).  status 'CAP': still walking
    at the cap."""
    cur = src
    hist = Counter()
    nbounds = 0
    prev_len = len(src[1])
    for i in range(max_rules):
        opts = step_all(cur)
        if not opts:
            return 'DONE', cur, i, hist, nbounds
        assert len(opts) == 1, (cur, opts)
        rule, nxt, cost = opts[0]
        hist[rule] += 1
        if len(nxt[1]) > prev_len:
            nbounds += 1
        prev_len = len(nxt[1])
        cur = nxt
    return 'CAP', cur, max_rules, hist, nbounds


def check_landing(n1, r1, n2, r2, b, cap=3000000):
    src = stageD(n1, r1, n2, r2, b)
    status, term, n, hist, nbounds = walk(src, cap)
    assert status == 'DONE', (n1, r1, n2, r2, b, status, term, n)
    st, pb, A, g0, s, pairs, G = term
    assert st == 'B' and pairs == () and G == 1 and g0 == 1, term
    assert s == 2 * b + 1, (n1, r1, n2, r2, b, term)
    assert A >= b, (n1, r1, n2, r2, b, term)
    bad = set(hist) - PROVED_RULES
    assert not bad, (n1, r1, n2, r2, b, bad)
    print(f"PASS landing S(n1={n1}, r1={r1}, n2={n2}, r2={r2}, "
          f"b={b}): {n} rules, {nbounds} frame growths, terminal "
          f"HB {list(pb)} {A} 1 {s} [] 1")
    return term


# ======================================================================
# Part 1: base + one-at-a-time sweeps.
# ======================================================================

def check_sweeps():
    check_landing(7, 22, 3, 26, 6)          # the hsim41 analogue
    for b in (2, 3, 4, 5, 7, 8, 9, 12):
        check_landing(7, 22, 3, 26, b)
    for n1 in (0, 1, 2, 4, 10):
        check_landing(n1, 22, 3, 26, 6)
    for r1 in (5, 6, 7, 10, 14, 15, 23, 30, 31):   # odd values incl.
        check_landing(7, r1, 3, 26, 6)
    for n2 in (6, 10):
        check_landing(7, 22, n2, 26, 6)
    for r2 in (6, 14, 26):                  # even (the era parity)
        check_landing(7, 22, 3, r2, 6)
    # mixed points
    check_landing(2, 15, 6, 14, 3)
    check_landing(0, 5, 6, 6, 2)
    check_landing(10, 15, 6, 14, 4)


# ======================================================================
# Part 2: edge cases (different stage parses, same landing).
# ======================================================================

def check_edges():
    check_landing(7, 22, 0, 26, 6, cap=2500000)   # n2 = 0: 5 growths
    check_landing(7, 22, 1, 26, 6)                # n2 = 1: 5 growths
    check_landing(7, 22, 3, 2, 6)                 # r2 = 2: 3 growths
    check_landing(7, 22, 3, 2, 2)                 # M = 616, beta = 2
    check_landing(0, 6, 3, 2, 2)                  # minimal corner
    check_landing(1, 5, 0, 2, 2, cap=2500000)


# ======================================================================
# Part 2b: odd r2 -- lands over the empty stack, wrong shuttle.
# ======================================================================

def check_odd_r2():
    for r2 in (3, 5, 9, 15):
        src = stageD(7, 22, 3, r2, 6)
        status, term, n, hist, nbounds = walk(src)
        assert status == 'DONE', (r2, status, term)
        st, pb, A, g0, s, pairs, G = term
        assert st == 'B' and pairs == () and G == 1 and g0 == 1, term
        assert s == 2 * 6 + r2, (r2, term)   # NOT 2b + 1
        assert A >= 6, term
        print(f"PASS odd-r2 fence S(n1=7, r1=22, n2=3, r2={r2}, "
              f"b=6): lands HB {list(pb)} {A} 1 {s} [] 1 with "
              f"s = 2b + r2 = {s} (era law needs even r2)")
    # r2 = 1 is degenerate: the "residue" pair (1, 2) is a spine
    # pair, not a grind residue; observed terminal (no law fit):
    src = stageD(7, 22, 3, 1, 6)
    status, term, n, hist, nbounds = walk(src)
    assert status == 'DONE', (status, term)
    assert term == ('B', (25, 24, 5), 33, 1, 26, (), 1), term
    print("PASS odd-r2 degenerate r2=1: lands HB [25, 24, 5] 33 1 "
          "26 [] 1 (B over empty, G = 1; no closed form asserted)")
    src = stageD(7, 22, 3, 5, 2)
    status, term, n, hist, nbounds = walk(src)
    assert status == 'DONE' and term[4] == 2 * 2 + 5, term
    print("PASS odd-r2 fence S(7, 22, 3, 5, 2): s = 2b + r2 = 9 "
          "(independent of b)")


# ======================================================================
# Part 3: machine-level REGEN confirmation at the terminal.
# ======================================================================

def check_machine_regen():
    for params in ((7, 22, 3, 26, 6), (7, 22, 3, 2, 2),
                   (2, 15, 6, 14, 3)):
        term = check_landing(*params)
        st, pb, A, g0, s, pairs, G = term
        z = hb(list(pb), A, s, [], G)
        for _ in range(4 * s + 22):
            z.step()
        rec = recognise(z)
        want = ('HC', list(pb), A, 1, 2, [], s - 1)
        assert want in rec, (params, want, rec)
        print(f"PASS machine REGEN at S{params} terminal: cost "
              f"{4 * s + 22} -> HC {list(pb)} {A} 1 2 [] {s - 1} "
              f"(the ERA_TAIL entry)")


# ======================================================================
# Part 4: growth probes -- CAP, never STUCK, never a wrong landing.
# ======================================================================

def check_growth():
    # completes, but ~1M rules (n1 growth is exponential-ish)
    check_landing(15, 22, 3, 26, 6, cap=2500000)
    # beyond primitive walking: must still be walking at the cap
    for params in ((7, 46, 3, 26, 6), (40, 22, 3, 26, 6),
                   (7, 22, 334, 26, 6), (7, 149, 3, 26, 6),
                   (7, 22, 3, 100, 6), (4, 23, 10, 6, 9),
                   (4, 31, 10, 6, 9)):
        src = stageD(*params)
        status, term, n, hist, nbounds = walk(src, 3000000)
        assert status == 'CAP', (params, status, term)
        bad = set(hist) - PROVED_RULES
        assert not bad, (params, bad)
        print(f"PASS growth probe S{params}: still walking at "
              f"{n} rules (frame {list(term[1])}, {nbounds} "
              f"growths so far) -- CAP, not stuck")


if __name__ == '__main__':
    check_sweeps()
    check_edges()
    check_odd_r2()
    check_machine_regen()
    check_growth()
    print("ALL PHASE 42 CHECKS PASS")
