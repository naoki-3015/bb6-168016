#!/usr/bin/env python3
"""Phase 41 verification: the phase-8 entry of the ESC era grind.

Contents:
  * a word-level hstep simulator: hsim36.step_all plus the new
    Phase 41 constructor PX2Bgen (the PX2B dispatch at a single
    block [b], b >= 5), mirroring Grind.v's hPX2Bgen / Dev.v's
    PX2Bgen;
  * machine-level checks of the PX2Bgen family (first landing at
    cost b + 32, no intermediate recognised section), over
    b in {5,6,7,8,9,10,12,14,16,19,20,24,30} and several stack
    shapes / G values;
  * word-level boundary checks for the phase-8 funnel stages
    A/B/C at shrunk analogues (a2, g0) in {(8, 40), (10, 52)} of
    the ([19], 41), g0 = 233 continuation grind (the real
    parameters are far beyond primitive walking: LOOPN 40 /
    DIPDESC 40 alone are ~2^41 rules), plus standalone word
    checks of the even boundary descent DIPDESC_even;
  * the phase-8 fence evidence: from the stage-D source
    HC [5] 13 1 2 with a deep era passenger, the continuation
    cascades through a growing frame, consumes the ENTIRE
    remaining stack, and reaches a B-section over the empty
    stack where the word model has no applicable rule; a raw
    machine trace from that config shows the next recognised
    section is not an era REGEN landing of the modelled form.

Run:  python3 hsim41.py     (all checks assert; prints PASS lines)
"""
import os
import sys

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from trace_dev import Z, tail, SN
from hsim36 import step_all as step_base, hc, recognise, as_record
from hsim40 import hb

PE2 = [(1, 1), (1, 2)]


def step_all(sec):
    st, pb, A, g0, s, pairs, G = sec
    if st == 'C' and A == 0 and g0 == 3 and s == 2 and len(pb) == 1 \
            and pb[0] >= 5:
        b = pb[0]
        return [('PX2Bgen',
                 ('B', (0,), 3, 1, 2,
                  ((b - 4, 2), (1, 1), (1, 2), (1, 2)) + tuple(pairs), G),
                 b + 32)]
    return step_base(sec)


def walk_hist(src, stop_rule=None, max_rules=5000000):
    """Deterministic word walk; returns (history, terminal_rule)."""
    cur = src
    hist = [cur]
    for _ in range(max_rules):
        opts = step_all(cur)
        if not opts:
            return hist, 'STUCK'
        assert len(opts) == 1, (cur, opts)
        rule, nxt, cost = opts[0]
        hist.append(nxt)
        cur = nxt
        if rule == stop_rule:
            return hist, rule
    return hist, 'CAP'


# ======================================================================
# Part 1: the PX2Bgen machine form.
# ======================================================================

def check_px2bgen_machine():
    cases = []
    for b in (5, 6, 7, 8, 9, 10, 12, 14, 16, 19, 20, 24, 30):
        cases.append((b, [(1, 2)] * 3, 2))
    cases += [(19, [(1, 2)] * 40 + [(149, 2), (1, 1)], 1),
              (19, [(6, 2)] + PE2, 1),
              (12, [(2, 1)], 3),
              (8, [], 2),
              (24, [(5, 3)], 4)]
    for b, pairs, G in cases:
        z = hc((b,), 0, 3, 2, pairs, G)
        want = ('HB', [0], 3, 1, 2,
                [(b - 4, 2), (1, 1), (1, 2), (1, 2)] + list(pairs), G)
        hits = []
        for i in range(b + 32 + 1):
            rec = recognise(z)
            if rec:
                hits.append((i, rec))
            if i < b + 32:
                z.step()
        assert hits[0][0] == 0, (b, pairs, G, hits[:2])
        assert len(hits) == 2 and hits[1][0] == b + 32, \
            (b, pairs, G, hits)
        assert want in hits[1][1], (b, pairs, G, hits[1])
    print(f"PASS PX2Bgen machine form ({len(cases)} cases: first "
          f"landing at cost b + 32, no intermediate section)")


# ======================================================================
# Part 2: word-level stage boundaries at shrunk analogues.
# ======================================================================

def check_stages():
    for (a2, g0) in ((8, 40), (10, 52)):
        for n in (0, 2):
            Q = [(1, 1), (1, 2), (1, 2)] + [(1, 2)] * n \
                + [(6, 2)] + PE2
            src = ('C', (19,), a2, g0, 2, tuple(Q), 1)
            hist, term = walk_hist(src, stop_rule='TUP2_1')
            assert term == 'TUP2_1'
            p1 = g0 - 4 - 2 * (a2 - 1)
            A1 = ('C', (19,), a2 - 1, 3, 2, ((g0 - 4, 2),) + tuple(Q), 1)
            A2 = ('C', (19,), a2 - 1, 2 * (a2 - 1) + 3, 2,
                  ((p1, 2),) + tuple(Q), 1)
            A3 = ('C', (19,), 0, 3, 2,
                  tuple([(1, 2)] * (a2 - 1)) + ((p1, 2),) + tuple(Q), 1)
            A4 = ('B', (0,), 3, 1, 2,
                  ((15, 2), (1, 1), (1, 2), (1, 2))
                  + tuple([(1, 2)] * (a2 - 1)) + ((p1, 2),) + tuple(Q), 1)
            R2 = A4[5][2:]
            B1 = ('C', (0,), 3, 3, 2, ((11, 2), (1, 1)) + R2, 1)
            B2 = ('C', (0,), 3, 9, 2, ((5, 2), (1, 1)) + R2, 1)
            B3 = ('C', (0,), 0, 3, 2,
                  ((1, 2), (1, 2), (1, 2), (5, 2), (1, 1)) + R2, 1)
            B4 = ('B', (), 0, 1, 5, ((1, 2),) + B3[5], 1)
            C1 = ('B', (), 4, 1, 13, ((5, 2), (1, 1)) + R2, 1)
            C2 = ('C', (), 4, 12, 2, ((3, 2), (1, 1)) + R2, 1)
            C3 = ('C', (), 0, 3, 2,
                  ((1, 2), (1, 2), (1, 2), (2, 2), (3, 2), (1, 1)) + R2, 1)
            C4 = ('C', (5,), 13, 1, 2, ((1, 2), (1, 1)) + R2, 1)
            names = ['A1 P/T/T', 'A2 LOOPN', 'A3 DIPDESC dip',
                     'A4 PX2Bgen landing', 'B1 LOOPN source',
                     'B2 LOOPN done', 'B3 DIPDESC dip', 'B4 PX2B0 landing',
                     'C1 POPx4', 'C2 TUP', 'C3 DIPDESC_even dip',
                     'C4 TUP2_1 landing']
            idx = []
            for nm, c in zip(names,
                             [A1, A2, A3, A4, B1, B2, B3, B4,
                              C1, C2, C3, C4]):
                assert c in hist, (a2, g0, n, nm, c)
                idx.append(hist.index(c))
            assert idx == sorted(idx), (a2, g0, n, names, idx)
            print(f"PASS stage boundaries (a2={a2}, g0={g0}, n={n}): "
                  f"A/B/C boundaries in order at rules "
                  f"{[hist.index(c) for c in (A4, B4, C4)]}")


def check_dipdesc_even():
    for t in (1, 2, 3, 5):
        rest = [(3, 2), (1, 1), (6, 2)] + PE2
        src = ('C', (7,), t, 2 * t + 4, 2, tuple(rest), 1)
        want = ('C', (7,), 0, 3, 2,
                tuple([(1, 2)] * (t - 1)) + ((2, 2),) + tuple(rest), 1)
        hist, term = walk_hist(src, max_rules=2000000)
        assert want in hist, (t, term, hist[-1])
        print(f"PASS DIPDESC_even word form (t={t}): dip reached "
              f"at rule {hist.index(want)}")


# ======================================================================
# Part 3: the cascade beyond the stage-D source (the fence).
# ======================================================================

def check_cascade():
    # Stage-D source analogue: frame ([5], 13) over the carried
    # stack (1, 2) :: (1, 1) :: R2 with the (a2, g0) = (8, 40)
    # funnel values and a deep era passenger: the (1, 2)^3 spine
    # (analogue of (1, 2)^334), the residue pair (26, 2) (analogue
    # of (2m - 1230, 2)) and Pe = (1, 1) :: (1, 2)^5.
    R2 = [(1, 2), (1, 2)] + [(1, 2)] * 7 \
        + [(22, 2), (1, 1), (1, 2), (1, 2)] \
        + [(1, 2)] * 3 + [(26, 2), (1, 1)] + [(1, 2)] * 5
    src = ('C', (5,), 13, 1, 2, tuple([(1, 2), (1, 1)] + R2), 1)
    hist, term = walk_hist(src, max_rules=5000000)
    frames = []
    for sec in hist:
        if not frames or frames[-1] != sec[1]:
            frames.append(sec[1])
    consumed = any((26, 2) not in sec[5] for sec in hist)
    print(f"cascade: {len(hist) - 1} word rules, terminal = {term}")
    print(f"cascade: frames visited: {frames}")
    print(f"cascade: residue pair (26, 2) consumed en route: "
          f"{consumed}")
    print(f"cascade: terminal config: {hist[-1]}")
    assert term == 'STUCK', (term, hist[-1])
    assert consumed
    # The word model stops at a B-section over the empty stack.
    # Trace the raw machine from there: the next recognised
    # sections are not an era REGEN landing.
    st, pb, A, g0, s, pairs, G = hist[-1]
    assert st == 'B' and pairs == ()
    z = hb(pb, A, s, [], G)
    hits = []
    for i in range(3000000):
        z.step()
        rec = recognise(z)
        if rec:
            hits.append((i + 1, rec))
            if len(hits) >= 3:
                break
    print(f"cascade: machine trace from the terminal config, "
          f"first recognised sections: {hits}")
    print("PASS cascade fence evidence (word model stuck over the "
          "empty stack; full passenger consumed)")


if __name__ == '__main__':
    check_px2bgen_machine()
    check_stages()
    check_dipdesc_even()
    check_cascade()
    print("ALL PHASE 41 CHECKS PASS")
