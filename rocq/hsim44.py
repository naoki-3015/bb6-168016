#!/usr/bin/env python3
"""Phase 44 verification: the stage-4 boundary grind of
CASCADE_STAGE4_BIG, decomposed into segments SEG1 / SEG2 / T1 /
T2 / T3 / T4 plus the residual tail core CASCADE_STAGE4_TAIL.

THE FAMILY.  The stage-4 source at a three-block frame:
    HC [f; p; 5] a 1 2 ((2m + 4, 2) :: (1, 1) :: (1, 2)^(b - 1)) 1
in the boundary regime m >= a (the CASCADE_STAGE4 floor
m + 1 <= a fails).  Era point: f = 428, p = 57, a = 822,
m = M - 619 (M >= 1441), b = beta.  Write a2 = p - 2,
mp = (f - 8)/2 (f even; the seg-2 pair is (f - 4, 2) =
(2*mp + 4, 2)), g2 = 2*(mp - a2) + 2 (the seg-2 residue),
m3 = mp - p - 1 (the T3 pair is (g2 - 4, 2) = (2*m3 + 4, 2)),
    Q0 = ((2*(m - a) + 2, 2) :: (1, 1) :: (1, 2)^(b - 1)),
    S1 = (1, 1) :: (1, 2) :: (1, 2) :: (1, 2)^a ++ Q0,
    S2 = (1, 1) :: (1, 2) :: (1, 2) :: (1, 2)^a2 ++ ((g2, 2) :: S1),
    R3 = (1, 1) :: (1, 2) :: (1, 2) :: (1, 2)^(2p + 4)
         ++ ((2*m3 - 4*p - 6, 2) :: S1),
    S4 = (1, 2) :: (1, 2)^3 ++ ((p - 9, 2) :: R3)   [p = 2q + 1].

THE SEGMENTS (each a clean composition of proved lemmas; the
floors are noted -- this is the dip-aware rounds totality:
grind_rounds via Grind4.rounds_from6 up to the budget, then the
boundary round = TUP + Grind7.DIPDESC, then the frame's dip):
  SEG1 (3 <= f, 1 <= p, 1 <= a <= m): grind_prefix +
    rounds_from6 (a - 1) + TUP + DIPDESC a + hPX2A:
      HC [f; p; 5] a 1 2 ((2m + 4, 2) :: P0)
        -> HC [5] (p - 1) (f - 2) 2 S1.
  SEG2 (3 <= p, p - 1 <= mp: seg-2 deficit >= 1): PUSH +
    grind_prefix + rounds_from6 (p - 3) + TUP + DIPDESC (p - 2)
    + hPX2B5:
      HC [5] (p - 1) (2*mp + 6) 2 S1 -> HB [0] 4 1 4 S2.
  T1 (1 <= p, 5 <= g2): POP (1, 1) + pop12 p + TUP +
    hGRIND_even p:
      HB [0] 4 1 4 S2
        -> HB [0] (p + 4) 1 (2p + 4) ((2, 2) :: (g2 - 2, 2) :: S1).
  T2 (5 <= g2): hTUP2_1:
      -> HC [p + 5; 0] (2p + 4) 1 2 ((g2 - 4, 2) :: S1).
  T3, two regimes at a2 = 2p + 4:
    * clean (m3 + 1 <= 2p + 4): GG_clean m3 ->
      HB [p + 5; 0] (2p + 4) 1 (2*m3 + 6) ((2, 2) :: S1)
      (the shrunk points below with f <= 6p + 14);
    * boundary (2p + 4 <= m3; THE ERA REGIME, f > 6p + 14):
      grind_prefix + rounds_from6 (2p + 3) + TUP
      + DIPDESC (2p + 4) + hPX2A0:
      -> HB [0] 3 1 2 ((p + 1, 2) :: R3).
  T4 (p = 2q + 1 odd, 5 <= q; the era p = 57): TUP +
    grind_prefix + rounds_from6 2 + TUP + DIPDESC 3 + hPX2B0:
      HB [0] 3 1 2 ((p + 1, 2) :: R3) -> HB [] 0 1 5 S4.
  TAIL (the residual core CASCADE_STAGE4_TAIL, Grind12.v):
      HB [] 0 1 5 S4 -> HB pb A 1 (2b + 1) [] 1, b <= A.

CHECKS.  Parts 1-3 walk stage-4 sources on a grid (S-family
points, era-ratio points with p << f, a deficit sweep, the
T3-boundary points (44, 4, 6, 8, 3) and (50, 5, 6, 8, 3)) and
assert the seg1 / seg2 / T1 / T2 boundary configs verbatim in
the history, the T3 landing for whichever regime the point is
in, and the final era landing.  Part 4 starts walks at the T4
source (era-shaped R3) and asserts the S4 boundary + the TAIL
traversal end-to-end at minimal points; Part 5 is the T4
growth probe (r3 = 4: S4 reached, tail CAP -- still walking,
never stuck).  All walks use only proved hstep constructors
(PROVED_RULES audit).

Run:  python3 hsim44.py     (all checks assert; prints PASS lines)
"""
import os
import sys
from collections import Counter

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from hsim43 import walk_hist
from hsim42 import PROVED_RULES


def spine(n):
    return [(1, 2)] * n


def stacks(f, p, a, m, b):
    a2 = p - 2
    mp = (f - 8) // 2
    g2 = 2 * (mp - a2) + 2
    m3 = mp - p - 1
    Q0 = [(2 * (m - a) + 2, 2), (1, 1)] + spine(b - 1)
    S1 = [(1, 1), (1, 2), (1, 2)] + spine(a) + Q0
    S2 = [(1, 1), (1, 2), (1, 2)] + spine(a2) + [(g2, 2)] + S1
    R3 = [(1, 1), (1, 2), (1, 2)] + spine(2 * p + 4) \
        + [(2 * m3 - 4 * p - 6, 2)] + S1
    return a2, mp, g2, m3, Q0, S1, S2, R3


def d4(f, p, a, m, b):
    return ('C', (f, p, 5), a, 1, 2,
            tuple([(2 * m + 4, 2), (1, 1)] + spine(b - 1)), 1)


def seg1_t(f, p, a, m, b):
    _, _, _, _, _, S1, _, _ = stacks(f, p, a, m, b)
    return ('C', (5,), p - 1, f - 2, 2, tuple(S1), 1)


def seg2_t(f, p, a, m, b):
    _, _, _, _, _, _, S2, _ = stacks(f, p, a, m, b)
    return ('B', (0,), 4, 1, 4, tuple(S2), 1)


def t1_t(f, p, a, m, b):
    _, _, g2, _, _, S1, _, _ = stacks(f, p, a, m, b)
    return ('B', (0,), p + 4, 1, 2 * p + 4,
            tuple([(2, 2), (g2 - 2, 2)] + S1), 1)


def t2_t(f, p, a, m, b):
    _, _, g2, _, _, S1, _, _ = stacks(f, p, a, m, b)
    return ('C', (p + 5, 0), 2 * p + 4, 1, 2,
            tuple([(g2 - 4, 2)] + S1), 1)


def t3_clean_t(f, p, a, m, b):
    _, _, _, m3, _, S1, _, _ = stacks(f, p, a, m, b)
    return ('B', (p + 5, 0), 2 * p + 4, 1, 2 * m3 + 6,
            tuple([(2, 2)] + S1), 1)


def t3_big_t(f, p, a, m, b):
    _, _, _, _, _, _, _, R3 = stacks(f, p, a, m, b)
    return ('B', (0,), 3, 1, 2, tuple([(p + 1, 2)] + R3), 1)


def check_landing_term(term, b, label):
    st, pb, A, g0, s, pairs, G = term
    assert st == 'B' and pairs == () and G == 1 and g0 == 1 \
        and s == 2 * b + 1 and A >= b, (label, term)


def check_stage4(f, p, a, m, b, cap=6000000):
    assert f % 2 == 0 and f >= 4 and p >= 3 and 1 <= a <= m
    a2, mp, g2, m3, _, _, _, _ = stacks(f, p, a, m, b)
    assert mp >= a2 + 1, (f, p, a, m, b, 'seg2 not boundary')
    assert g2 >= 6, (f, p, a, m, b, 'g2 too small')
    hist, rules, status = walk_hist(d4(f, p, a, m, b), cap)
    label = f"S4(f={f}, p={p}, a={a}, m={m}, b={b})"
    assert status == 'DONE', (label, status, hist[-1])
    bad = set(rules) - PROVED_RULES
    assert not bad, (label, bad)
    for nm, tgt in (('seg1', seg1_t(f, p, a, m, b)),
                    ('seg2', seg2_t(f, p, a, m, b)),
                    ('T1', t1_t(f, p, a, m, b)),
                    ('T2', t2_t(f, p, a, m, b))):
        assert tgt in hist, (label, nm)
    idx = [hist.index(t(f, p, a, m, b)) for t in
           (seg1_t, seg2_t, t1_t, t2_t)]
    assert idx == sorted(idx), (label, 'order', idx)
    if m3 + 1 <= 2 * p + 4:
        tgt = t3_clean_t(f, p, a, m, b)
        assert tgt in hist, (label, 'T3 clean')
        regime = f"T3 clean (m3={m3} <= {2 * p + 4})"
    else:
        tgt = t3_big_t(f, p, a, m, b)
        assert tgt in hist, (label, 'T3 boundary')
        regime = f"T3 BOUNDARY (m3={m3} > {2 * p + 4})"
    check_landing_term(hist[-1], b, label)
    print(f"PASS {label}: {len(rules)} rules; seg1@{idx[0]} "
          f"seg2@{idx[1]} T1@{idx[2]} T2@{idx[3]}; {regime}; "
          f"lands HB {list(hist[-1][1])} {hist[-1][2]} 1 "
          f"{hist[-1][4]} [] 1")


def t4_src(q, r3, a, rM, b):
    """The T4 source HB [0] 3 1 2 ((2q + 2, 2) :: R3) with an
    era-shaped R3 (p = 2q + 1, so 2p + 4 = 4q + 6)."""
    S1 = [(1, 1), (1, 2), (1, 2)] + spine(a) \
        + [(rM, 2), (1, 1)] + spine(b - 1)
    R3 = [(1, 1), (1, 2), (1, 2)] + spine(4 * q + 6) \
        + [(r3, 2)] + S1
    return ('B', (0,), 3, 1, 2, tuple([(2 * q + 2, 2)] + R3), 1), R3


def s4_t(q, R3):
    return ('B', (), 0, 1, 5,
            tuple([(1, 2)] + spine(3) + [(2 * q - 8, 2)] + R3), 1)


def check_t4(q, r3, a, rM, b, cap=6000000):
    assert q >= 5 and r3 >= 2 and rM >= 2 and b >= 2
    src, R3 = t4_src(q, r3, a, rM, b)
    hist, rules, status = walk_hist(src, cap)
    label = f"T4(q={q}, r3={r3}, a={a}, rM={rM}, b={b})"
    assert status == 'DONE', (label, status, hist[-1])
    bad = set(rules) - PROVED_RULES
    assert not bad, (label, bad)
    tgt = s4_t(q, R3)
    assert tgt in hist, (label, 'S4 boundary')
    check_landing_term(hist[-1], b, label)
    print(f"PASS {label}: {len(rules)} rules; S4 boundary "
          f"@{hist.index(tgt)} (PX2B0 dip); lands "
          f"HB {list(hist[-1][1])} {hist[-1][2]} 1 "
          f"{hist[-1][4]} [] 1 (TAIL core source reached)")


def check_seg1_only(f, p, a, m, b, cap=6000000):
    """The S-family regime (p comparable to f): SEG1's boundary
    is regime-free, but seg 2 is CLEAN there (mp < a2 + 1), so
    only the seg1 boundary and the final landing are asserted."""
    hist, rules, status = walk_hist(d4(f, p, a, m, b), cap)
    label = f"SEG1(f={f}, p={p}, a={a}, m={m}, b={b})"
    assert status == 'DONE', (label, status, hist[-1])
    bad = set(rules) - PROVED_RULES
    assert not bad, (label, bad)
    tgt = seg1_t(f, p, a, m, b)
    assert tgt in hist, (label, 'seg1')
    check_landing_term(hist[-1], b, label)
    print(f"PASS {label}: {len(rules)} rules; seg1 boundary "
          f"@{hist.index(tgt)}; lands HB {list(hist[-1][1])} "
          f"{hist[-1][2]} 1 {hist[-1][4]} [] 1 (seg2 clean here)")


def check_t4_probe(q, r3, a, rM, b, cap=6000000):
    src, R3 = t4_src(q, r3, a, rM, b)
    hist, rules, status = walk_hist(src, cap)
    label = f"T4probe(q={q}, r3={r3}, a={a}, rM={rM}, b={b})"
    bad = set(rules) - PROVED_RULES
    assert not bad, (label, bad)
    tgt = s4_t(q, R3)
    assert tgt in hist, (label, 'S4 boundary')
    assert status == 'CAP', (label, status, hist[-1])
    print(f"PASS {label}: S4 boundary @{hist.index(tgt)}; tail "
          f"still walking at {len(rules)} rules (frame "
          f"{list(hist[-1][1])}) -- CAP, not stuck")


if __name__ == '__main__':
    # Part 1: S-family stage-4 points (seg 2 clean there)
    check_seg1_only(28, 24, 12, 12, 6)   # S(7,7,0,32,6) frame
    check_seg1_only(23, 21, 16, 16, 3)   # S(4,9,1,40,3) frame
    # Part 2: era-ratio points (p << f), deficit sweep
    check_stage4(28, 5, 12, 12, 6)     # deficit 1
    check_stage4(30, 4, 14, 16, 3)     # deficit 3
    check_stage4(44, 6, 16, 20, 4)     # deficit 5
    check_stage4(36, 8, 10, 15, 2)     # deficit 6, b = 2
    check_stage4(24, 3, 8, 11, 5)      # minimal p = 3
    # Part 3: the T3-boundary (era) regime: m3 >= 2p + 5
    check_stage4(44, 4, 6, 8, 3)
    check_stage4(50, 5, 6, 8, 3)
    # Part 4: T4-source walks (T4 boundary + TAIL core traversed
    # end-to-end at the minimal points; the tail's grind depths
    # compound in r3, so r3 = 2 points complete in ~200 rules)
    check_t4(5, 2, 2, 2, 2)
    check_t4(5, 2, 4, 2, 3)
    check_t4(6, 2, 2, 2, 2)
    check_t4(8, 2, 2, 2, 2)
    # Part 5: T4 growth probe -- r3 = 4: the S4 boundary is
    # reached (T4 segment), and the tail is still walking at the
    # cap (never stuck, never a wrong landing): the TAIL core's
    # larger-parameter evidence is CAP, as in hsim42 Part 4.
    check_t4_probe(5, 4, 2, 2, 2)
    print("ALL PHASE 44 CHECKS PASS")
