#!/usr/bin/env python3
"""Phase 43 verification: the stage decomposition of CASCADE_LANDING
in the ERA regime (r1 = 149 is ODD -- the even-r1 base analogue of
hsim42 has a different stage-2 parse), plus the stage-4 boundary
regime evidence.

THE DECOMPOSITION (asserted exactly below on the shrunk family
S(n1, r1, n2, r2, b) of hsim42, for ODD r1 >= 7 and EVEN r2).
Write x = n1 + 17, A1 = 2*n1 + 10, m1 = (r1 - 7)/2,
A_pre = 2*n1 + n2 + 13, s_pre = r1 + 2*n2 + 5, m4 = (r2 - 8)/2.

  Stage 1 (parity-free; TDN + POPs + TUP + hGRIND_even (n1 + 3)
  + hTUP2_1):
    HC [5] 13 1 2 (stage-D stack)
      -> HC [x; 5] A1 1 2 ((r1 - 4, 2) :: (1, 1) :: Rest1)
    Rest1 = (1, 2)^(n2 + 2) ++ ((r2, 2) :: (1, 1) :: (1, 2)^(b-1)).

  Merged stage 2+3 (the odd pair (r1 - 4, 2) = (2*m1 + 3, 2) is
  ground by GG_odd -- grind_prefix + odd GG rounds -- to a (1, 2)
  head, so the grind runs through (1, 1) and the whole second
  spine before TUP on (r2, 2); then hGRIND_even (m1 + n2 + 4)
  and hTUP2_1):
    -> HB [x; 5] A1 1 (2*m1 + 6) ((1, 2) :: (1, 1) :: Rest1)
    -> HB [x; 5] (A1 + n2 + 4) 1 (2*m1 + 2*n2 + 13)
         ((r2, 2) :: (1, 1) :: (1, 2)^(b - 1))         [POPs]
    -> HC [x; 5] (A1 + n2 + 4) (2*m1 + 2*n2 + 12) 2
         ((r2 - 2, 2) :: (1, 1) :: (1, 2)^(b - 1))     [TUP]
    -> HB [x; 5] A_pre 1 s_pre
         ((2, 2) :: (r2 - 2, 2) :: (1, 1) :: (1, 2)^(b - 1))
                                                       [hGRIND_even]
    -> HC [A_pre + 1; x; 5] s_pre 1 2
         ((r2 - 4, 2) :: (1, 1) :: (1, 2)^(b - 1))     [hTUP2_1]
  Floors: GG_odd needs m1 + 1 <= A1 (era: 72 <= 90);
  hGRIND_even needs m1 + n2 + 4 <= A1 + n2 + 3, i.e.
  m1 <= A1 - 1 (era: 71 <= 89).  Both are M-independent: the
  residue r2 enters stages 1-3 only through TUP / hTUP2_1 /
  the two dispatch branches below.

  r2 = 4 branch (M = 617): the hGRIND_even target's second pair
  is (2, 2), so hTUP2_1 cannot fire; hTRANS2_2 fires instead:
    -> HB [s_pre + 1; A_pre + 1; x; 5] 3 1 3 ((1, 2)^(b - 1))
  and CASCADE_POPFIN closes: terminal A = b + 2 >= b.

  r2 = 2 branch (M = 616): after the POPs the head is the
  residue (2, 2) itself; hTRANS2_1 fires directly (no TUP, no
  hGRIND_even):
    HB [x; 5] (A1 + n2 + 4) 1 (r1 + 2*n2 + 6)
      ((2, 2) :: (1, 1) :: (1, 2)^(b - 1))
    -> HB [A1 + n2 + 5; x; 5] (r1 + 2*n2 + 7) 1 3 ((1, 2)^(b - 1))
  and CASCADE_POPFIN closes: terminal A = r1 + 2*n2 + 6 + b >= b.

  Stage 4 (clean regime, CASCADE_STAGE4 of Grind10.v: needs
  m4 + 1 <= s_pre, i.e. r2 <= 2*r1 + 4*n2 + 16; era: M <= 1440):
    -> HB [s_pre + 1; A_pre + 1; x; 5] (2*m4 + 7) 1 3
         ((1, 2)^(b - 1))                              [TRANS2_1]
    -> HB [s_pre + 1; A_pre + 1; x; 5] (2*m4 + 6 + b) 1
         (2*b + 1) []                                  [POPFIN]
  with 2*m4 + 6 + b >= b iff M >= 616.

  Stage 4 BOUNDARY regime (m4 + 1 > s_pre; era: M >= 1441):
  Part 3 walks shrunk points in this regime and asserts only
  the era landing shape HB pb a 1 (2b + 1) [] 1, b <= a (the
  parses re-route through dips / PX2A, as at the even-family
  point S(7, 22, 0, 26, 6) of hsim42).  This is the evidence
  for the residual core CASCADE_STAGE4_BIG (Grind11.v).

Run:  python3 hsim43.py     (all checks assert; prints PASS lines)
"""
import os
import sys
from collections import Counter

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from hsim41 import step_all
from hsim42 import stageD, PROVED_RULES


def walk_hist(src, max_rules=3000000):
    cur = src
    hist = [cur]
    rules = []
    for _ in range(max_rules):
        opts = step_all(cur)
        if not opts:
            return hist, rules, 'DONE'
        assert len(opts) == 1, (cur, opts)
        rule, nxt, cost = opts[0]
        rules.append(rule)
        hist.append(nxt)
        cur = nxt
    return hist, rules, 'CAP'


def spine(n):
    return [(1, 2)] * n


def check_stages(n1, r1, n2, r2, b, cap=3000000):
    assert r1 % 2 == 1 and r1 >= 7 and r2 % 2 == 0 and r2 >= 2
    x = n1 + 17
    A1 = 2 * n1 + 10
    m1 = (r1 - 7) // 2
    A_pre = 2 * n1 + n2 + 13
    s_pre = r1 + 2 * n2 + 5
    tail = spine(b - 1)
    rest1 = spine(n2 + 2) + [(r2, 2), (1, 1)] + tail
    src = stageD(n1, r1, n2, r2, b)
    hist, rules, status = walk_hist(src, cap)
    assert status == 'DONE', (n1, r1, n2, r2, b, status)
    bad = set(rules) - PROVED_RULES
    assert not bad, (n1, r1, n2, r2, b, bad)
    # stage 1 boundary
    c1 = ('C', (x, 5), A1, 1, 2, tuple([(r1 - 4, 2), (1, 1)] + rest1), 1)
    assert c1 in hist, (n1, r1, n2, r2, b, 'stage1')
    i1 = hist.index(c1)
    # merged stage sub-boundaries
    c2a = ('B', (x, 5), A1, 1, 2 * m1 + 6,
           tuple([(1, 2), (1, 1)] + rest1), 1)
    assert c2a in hist, (n1, r1, n2, r2, b, 'GG_odd')
    c2b = ('B', (x, 5), A1 + n2 + 4, 1, 2 * m1 + 2 * n2 + 13,
           tuple([(r2, 2), (1, 1)] + tail), 1)
    assert c2b in hist, (n1, r1, n2, r2, b, 'POPs')
    assert i1 < hist.index(c2a) < hist.index(c2b)
    term = hist[-1]
    if r2 >= 6:
        c2c = ('C', (x, 5), A1 + n2 + 4, 2 * m1 + 2 * n2 + 12, 2,
               tuple([(r2 - 2, 2), (1, 1)] + tail), 1)
        c2d = ('B', (x, 5), A_pre, 1, s_pre,
               tuple([(2, 2), (r2 - 2, 2), (1, 1)] + tail), 1)
        c2e = ('C', (A_pre + 1, x, 5), s_pre, 1, 2,
               tuple([(r2 - 4, 2), (1, 1)] + tail), 1)
        for nm, c in (('TUP', c2c), ('hGRIND_even', c2d),
                      ('hTUP2_1', c2e)):
            assert c in hist, (n1, r1, n2, r2, b, nm)
        assert hist.index(c2b) < hist.index(c2c) < hist.index(c2d) \
            < hist.index(c2e)
        m4 = (r2 - 8) // 2
        if m4 + 1 <= s_pre:  # clean stage 4
            want = ('B', (s_pre + 1, A_pre + 1, x, 5),
                    2 * m4 + 6 + b, 1, 2 * b + 1, (), 1)
            assert term == want, (n1, r1, n2, r2, b, term, want)
            print(f"PASS stages S(n1={n1}, r1={r1}, n2={n2}, "
                  f"r2={r2}, b={b}): full decomposition, clean "
                  f"stage 4, terminal A = {2 * m4 + 6 + b}")
            return
        # boundary stage 4: only the landing shape is asserted
        st, pb, A, g0, s, pairs, G = term
        assert st == 'B' and pairs == () and G == 1 and g0 == 1 \
            and s == 2 * b + 1 and A >= b, (n1, r1, n2, r2, b, term)
        print(f"PASS stages S(n1={n1}, r1={r1}, n2={n2}, r2={r2}, "
              f"b={b}): stages 1-3 exact; stage 4 BOUNDARY "
              f"(m4 + 1 = {m4 + 1} > s_pre = {s_pre}), lands "
              f"HB {list(pb)} {A} 1 {s} [] 1")
        return
    if r2 == 4:
        c2d = ('B', (x, 5), A_pre, 1, s_pre,
               tuple([(2, 2), (2, 2), (1, 1)] + tail), 1)
        assert c2d in hist, (n1, r1, n2, r2, b, 'r2=4 hGRIND_even')
        want = ('B', (s_pre + 1, A_pre + 1, x, 5), b + 2, 1,
                2 * b + 1, (), 1)
        assert term == want, (n1, r1, n2, r2, b, term, want)
        print(f"PASS stages S(n1={n1}, r1={r1}, n2={n2}, r2=4, "
              f"b={b}): TRANS2_2 branch, terminal A = {b + 2}")
        return
    # r2 == 2
    want = ('B', (A1 + n2 + 5, x, 5), r1 + 2 * n2 + 6 + b, 1,
            2 * b + 1, (), 1)
    assert term == want, (n1, r1, n2, r2, b, term, want)
    print(f"PASS stages S(n1={n1}, r1={r1}, n2={n2}, r2=2, "
          f"b={b}): TRANS2_1 branch, terminal "
          f"A = {r1 + 2 * n2 + 6 + b}")


def check_boundary(n1, r1, n2, r2, b, cap=3000000):
    """Stage-4 boundary regime (asserted: landing shape only)."""
    s_pre = r1 + 2 * n2 + 5
    m4 = (r2 - 8) // 2
    assert m4 + 1 > s_pre, (n1, r1, n2, r2, b, 'not boundary')
    src = stageD(n1, r1, n2, r2, b)
    hist, rules, status = walk_hist(src, cap)
    assert status == 'DONE', (n1, r1, n2, r2, b, status, hist[-1])
    bad = set(rules) - PROVED_RULES
    assert not bad, (n1, r1, n2, r2, b, bad)
    term = hist[-1]
    st, pb, A, g0, s, pairs, G = term
    assert st == 'B' and pairs == () and G == 1 and g0 == 1 \
        and s == 2 * b + 1 and A >= b, (n1, r1, n2, r2, b, term)
    grows = sum(1 for i in range(1, len(hist))
                if len(hist[i][1]) > len(hist[i - 1][1]))
    print(f"PASS boundary S(n1={n1}, r1={r1}, n2={n2}, r2={r2}, "
          f"b={b}): {len(rules)} rules, {grows} frame growths, "
          f"lands HB {list(pb)} {A} 1 {s} [] 1")


def check_stage4_r2_6(b):
    """The M = 618 stage-4 branch: at the era frame the stage-4
    pair is (2, 2) itself (r2 - 4 = 2), so CASCADE_STAGE4 (whose
    pair is (2*m + 4, 2) >= (4, 2)) does not apply; the source
    goes TDN + hTRANS2_1 + POPFIN directly."""
    src = ('C', (428, 57, 5), 822, 1, 2,
           tuple([(2, 2), (1, 1)] + [(1, 2)] * (b - 1)), 1)
    hist, rules, status = walk_hist(src)
    assert status == 'DONE', (b, status)
    assert rules[0] == 'TDN' and rules[1] == 'TRANS2_1', (b, rules)
    assert hist[-1] == ('B', (823, 428, 57, 5), 5 + (b - 1), 1,
                        2 * b + 1, (), 1), (b, hist[-1])
    print(f"PASS stage4 M=618 branch b={b}: TDN + TRANS2_1 + "
          f"POPFIN, terminal A = {5 + (b - 1)}")


if __name__ == '__main__':
    # generic regime: stages 1-3 exact + clean stage 4
    check_stages(7, 15, 3, 26, 6)
    check_stages(7, 23, 3, 26, 6)
    check_stages(3, 9, 2, 10, 2)
    check_stages(5, 11, 2, 14, 4)
    check_stages(7, 15, 4, 26, 3)
    check_stages(4, 21, 5, 18, 5)
    # r2 = 4 and r2 = 2 dispatch branches
    check_stages(7, 15, 3, 4, 6)
    check_stages(5, 11, 2, 4, 3)
    check_stages(7, 15, 3, 2, 6)
    check_stages(3, 9, 2, 2, 2)
    # stage-4 boundary regime: landing shape (the residual core)
    check_boundary(7, 7, 0, 32, 6, cap=2500000)
    check_boundary(4, 9, 1, 40, 3, cap=2500000)
    # the M = 618 stage-4 dispatch branch at the era frame
    check_stage4_r2_6(2)
    check_stage4_r2_6(6)
    print("ALL PHASE 43 CHECKS PASS")
