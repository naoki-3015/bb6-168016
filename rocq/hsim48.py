#!/usr/bin/env python3
"""Phase 48 machine tests for the TAIL2_END2 reduction.

Characterisation (from mwalk traces of TOP(j, beta), j >= 7430):

  TOP(j, b) = HB [1279; 745; 151; 77; 35; 20; 0] 4001 1 7427
              ((2j, 2) :: (1, 1) :: (1, 2)^(b-1)),  rho = 2j >= 14860.

  1. FRONT (the TOP47_BAND front, uniform in j >= 4): TUP,
     hGRIND_even 3711, TUP2_1, TDN, TUP
     -> GRIND2 = HC [4001; F] 7426 3 2 ((2j-6, 2) :: tail(b)),
     F = [1279; 745; 151; 77; 35; 20; 0].
  2. DIPGRIND (7426, r), r = 2j - 14858 >= 2:
     -> HC [4001; F] 0 3 2 (spine 7426 ++ W),  W = ((r, 2) :: tail(b)).
  3. CASCADE48: a FIXED parse (all frames/counters constant; W
     rides untouched at the bottom), descending the TOP frame's
     own blocks by DIPGRIND + PX2A levels:
       [4001; F]  --PX2A+PUSH+TDN+TUP-->  [745; ...] pair (3995, 2)
       DIPGRIND (1277, 1441)
       [745; ...] --PX2A+PUSH+TDN+TUP-->  [77; 35; 20; 0] (739, 2)
       DIPGRIND (149, 441)
       [77; ...]  --PX2A+PUSH+TDN+TUP-->  [20; 0] pair (71, 2)
       DIPGRIND (33, 5)
       [20; 0]    --PX2A0+TUP+TDN+TUP-->  [0] pair (12, 2)
       DIPGRIND (3, 6);  PX2B0 -> HB [] 0 1 5
       pop12 4; TUP+PUSH+TDN+TUP; DIPGRIND (3, 2); PUSHX;
       pop12 3; TUP2_1+TDN+TRANS2_1 -> HB [14; 5] 5 1 3
       pop12 35; TUP + hGRIND_even 34 + TUP2_1 + TDN
         -> HB [40; 14; 5] 72 1 4
       pop12 1 + POP + pop12 151; TUP + hGRIND_even 152
         + TUP2_1 + TDN + TUP -> HC [225; 40; 14; 5] (435, 2)
       CLEANG_odd 216; pop12 1 + POP + pop12 1279
       TUP + hGRIND_even 1498 + TUP2_1 + TDN + TUP
         -> HC [1589; 225; 40; 14; 5] (1435, 2)
       CLEANG_odd 716; pop12 1 + POP + pop12 7428
     -> TOP2 = HB [1589; 225; 40; 14; 5] 10430 1 16299 W.
     (CASCADE48 is stated for an ARBITRARY tail w in Grind16.v;
     Part 1b below probes that generality with a junk tail.)
  4. TOP2 closings by r = 2 * j2, j2 = j - 7429:
     r = 2:        TRANS2_1 + POPFIN, A = 16299 + b,
                   frame [10431; 1589; 225; 40; 14; 5].
     r = 4:        TUP + hGRIND_even 8147 + TRANS2_2 + POPFIN,
                   A = b + 2, frame [16299; 10430; 1589; ...].
     r = 6:        TUP + hGRIND_even 8147 + TUP2_1 + TDN
                   + TRANS2_1 + POPFIN, A = b + 4,
                   frame [16299; 10430; 1589; ...].
     8 <= r <= 32602 (band 2): TUP + hGRIND_even 8147 + TUP2_1
                   + TDN + TUP -> GRIND3 = HC [10430; 1589; ...]
                   16298 3 2 ((r-6, 2) :: tail(b))  -- TUP2_1 moves
                   the shuttle 16298 into the counter slot, so the
                   band counter is 16298, NOT 10430 (the first
                   harness run refuted the 10430 guess: finals
                   land on frame [16299; 10430; ...]);
                   CLEANG_even ((r-8)/2) (floor (r-8)/2 + 1
                   <= 16298, exactly r <= 32602); TRANS2_1
                   + POPFIN, A = r + b - 2,
                   frame [16299; 10430; 1589; ...].
     r >= 32604:   GRIND3's pair (r-6, 2) exceeds the CLEANG_even
                   floor; DIPGRIND (16298, r - 32602) landing
                   occurs (asserted in Part 3).  This is the
                   residual core TAIL2_END3 (at TOP2, r = 2*j2,
                   j2 >= 16302).

Band boundary: r <= 32602  <=>  j <= 23730.
"""
import sys
sys.path.insert(0, '/home/hatch/workspace/busy-beaver/rocq')
from hsim45 import mwalk, fmt
from hsim42 import PROVED_RULES

SP = lambda n: [(1, 2)] * n
F7 = (1279, 745, 151, 77, 35, 20, 0)
TOP2F = (1589, 225, 40, 14, 5)


def TOP(j, b):
    return ('B', F7, 4001, 1, 7427,
            ((2 * j, 2), (1, 1)) + tuple(SP(b - 1)), 1)


def W(r, b):
    return ((r, 2), (1, 1)) + tuple(SP(b - 1))


def waypoints(j, b):
    """The full asserted waypoint chain TOP -> ... -> TOP2."""
    r = 2 * j - 14858
    w = W(r, b)
    tail = ((1, 1),) + tuple(SP(b - 1))
    R1 = ((1441, 2), (1, 1)) + tuple(SP(7428)) + w
    R2 = ((441, 2), (1, 1)) + tuple(SP(1279)) + R1
    R3 = ((5, 2), (1, 1)) + tuple(SP(151)) + R2
    F1 = (4001,) + F7
    F2 = (745, 151, 77, 35, 20, 0)
    F3 = (77, 35, 20, 0)
    pts = []
    pts.append(('C', F1, 7426, 3, 2, ((2 * j - 6, 2),) + tail, 1))
    pts.append(('C', F1, 0, 3, 2, tuple(SP(7426)) + w, 1))
    pts.append(('C', F2, 1277, 3, 2,
                ((3995, 2), (1, 1)) + tuple(SP(7428)) + w, 1))
    pts.append(('C', F2, 0, 3, 2, tuple(SP(1277)) + R1, 1))
    pts.append(('C', F3, 149, 3, 2,
                ((739, 2), (1, 1)) + tuple(SP(1279)) + R1, 1))
    pts.append(('C', F3, 0, 3, 2, tuple(SP(149)) + R2, 1))
    pts.append(('C', (20, 0), 33, 3, 2,
                ((71, 2), (1, 1)) + tuple(SP(151)) + R2, 1))
    pts.append(('C', (20, 0), 0, 3, 2, tuple(SP(33)) + R3, 1))
    pts.append(('C', (0,), 3, 3, 2,
                ((12, 2), (1, 1)) + tuple(SP(35)) + R3, 1))
    pts.append(('C', (0,), 0, 3, 2, tuple(SP(3))
                + ((6, 2), (1, 1)) + tuple(SP(35)) + R3, 1))
    pts.append(('B', (), 0, 1, 5,
                ((1, 2),) + tuple(SP(3))
                + ((6, 2), (1, 1)) + tuple(SP(35)) + R3, 1))
    pts.append(('B', (), 4, 1, 13,
                ((6, 2), (1, 1)) + tuple(SP(35)) + R3, 1))
    pts.append(('C', (), 3, 3, 2,
                ((8, 2), (4, 2), (1, 1)) + tuple(SP(35)) + R3, 1))
    pts.append(('C', (), 0, 3, 2, tuple(SP(3))
                + ((2, 2), (4, 2), (1, 1)) + tuple(SP(35)) + R3, 1))
    pts.append(('B', (), 1, 1, 7, tuple(SP(3))
                + ((2, 2), (4, 2), (1, 1)) + tuple(SP(35)) + R3, 1))
    pts.append(('B', (), 4, 1, 13,
                ((2, 2), (4, 2), (1, 1)) + tuple(SP(35)) + R3, 1))
    pts.append(('B', (14, 5), 5, 1, 3, tuple(SP(35)) + R3, 1))
    pts.append(('B', (14, 5), 40, 1, 73, R3, 1))
    pts.append(('B', (40, 14, 5), 72, 1, 4,
                ((1, 2), (1, 1)) + tuple(SP(151)) + R2, 1))
    pts.append(('B', (40, 14, 5), 225, 1, 309, R2, 1))
    pts.append(('C', (225, 40, 14, 5), 308, 3, 2,
                ((435, 2), (1, 1)) + tuple(SP(1279)) + R1, 1))
    pts.append(('B', (225, 40, 14, 5), 308, 1, 440,
                ((1, 2), (1, 1)) + tuple(SP(1279)) + R1, 1))
    pts.append(('B', (225, 40, 14, 5), 1589, 1, 3001, R1, 1))
    pts.append(('C', TOP2F, 3000, 3, 2,
                ((1435, 2), (1, 1)) + tuple(SP(7428)) + w, 1))
    pts.append(('B', TOP2F, 3000, 1, 1440,
                ((1, 2), (1, 1)) + tuple(SP(7428)) + w, 1))
    pts.append(('B', TOP2F, 10430, 1, 16299, w, 1))
    return pts


def norm(cfg):
    st, pb, A, g0, s, pairs, G = cfg
    return (st, tuple(pb), A, g0, s, tuple(pairs), G)


def check_chain(j, b, cap=400000):
    steps, status, fin = mwalk(TOP(j, b), max_steps=cap)
    hist = [norm(st[-1]) for st in steps]
    pts = [norm(p) for p in waypoints(j, b)]
    pos = -1
    for p in pts:
        found = None
        for i in range(pos + 1, len(hist)):
            if hist[i] == p:
                found = i
                break
        assert found is not None, \
            'j=%d b=%d: waypoint missing after %d: %s' \
            % (j, b, pos, fmt(p))
        pos = found
    return steps, status, fin, pos


def main():
    fails = 0
    used = set()
    # Part 1: full waypoint chain TOP -> TOP2, several bands.
    for (j, b) in [(7430, 2), (7430, 3), (7431, 2), (8000, 2),
                   (23730, 2), (23731, 2)]:
        try:
            steps, status, fin, pos = check_chain(j, b)
            for st in steps:
                if st[0] == 'prim':
                    used.update(st[2])
            print('PASS chain j=%d b=%d: %d waypoints in order, '
                  'TOP2 at step %d, walk %s'
                  % (j, b, len(waypoints(j, b)), pos, status))
        except AssertionError as e:
            fails += 1
            print('FAIL', e)
    # Part 1b: CASCADE48 is tail-general -- junk tail probe.
    w0 = ((7, 2), (1, 1), (3, 2), (1, 2))
    src = ('C', (4001,) + F7, 0, 3, 2, tuple(SP(7426)) + w0, 1)
    steps, status, fin = mwalk(src, max_steps=100000)
    hist = [norm(st[-1]) for st in steps]
    top2 = norm(('B', TOP2F, 10430, 1, 16299, w0, 1))
    ok = top2 in hist
    print(('PASS' if ok else 'FAIL'),
          'tail-generality: TOP2 shape reached with junk tail')
    fails += 0 if ok else 1
    # Part 2: TOP2-closing finals.
    finals = {
        (7430, 2): ((10431, 1589, 225, 40, 14, 5), 16301),
        (7430, 3): ((10431, 1589, 225, 40, 14, 5), 16302),
        (7431, 2): ((16299, 10430, 1589, 225, 40, 14, 5), 4),
        (7431, 3): ((16299, 10430, 1589, 225, 40, 14, 5), 5),
        (7432, 2): ((16299, 10430, 1589, 225, 40, 14, 5), 6),
        (7433, 2): ((16299, 10430, 1589, 225, 40, 14, 5), 8),
        (8000, 3): ((16299, 10430, 1589, 225, 40, 14, 5), 1143),
        (23730, 2): ((16299, 10430, 1589, 225, 40, 14, 5), 32602),
    }
    for (j, b), (fr, A) in sorted(finals.items()):
        steps, status, fin = mwalk(TOP(j, b), max_steps=400000)
        want = ('B', tuple(fr), A, 1, 2 * b + 1, (), 1)
        ok = status == 'DONE' and norm(fin) == want
        print(('PASS' if ok else 'FAIL'),
              'final j=%d b=%d: %s (want A=%d frame %s)'
              % (j, b, fmt(fin), A, list(fr)))
        fails += 0 if ok else 1
    # Part 3: the third fence -- r >= 32604 takes DIPGRIND at 16298.
    for (j, b) in [(23731, 2), (24000, 2), (30000, 2)]:
        r = 2 * j - 14858
        steps, status, fin = mwalk(TOP(j, b), max_steps=400000)
        hist = [norm(st[-1]) for st in steps]
        g3 = norm(('C', (10430,) + TOP2F, 16298, 3, 2,
                   ((r - 6, 2), (1, 1)) + tuple(SP(b - 1)), 1))
        dip3 = norm(('C', (10430,) + TOP2F, 0, 3, 2,
                     tuple(SP(16298))
                     + ((r - 32602, 2), (1, 1)) + tuple(SP(b - 1)), 1))
        ok = g3 in hist and dip3 in hist \
            and hist.index(g3) < hist.index(dip3)
        print(('PASS' if ok else 'FAIL'),
              'fence j=%d: GRIND3 then third DIPGRIND landing '
              'occur (r=%d)' % (j, r))
        fails += 0 if ok else 1
    # Part 4: primitive-step audit.
    bad = used - PROVED_RULES
    print(('PASS' if not bad else 'FAIL'),
          'primitive rules used %s all in PROVED_RULES'
          % (sorted(used),))
    fails += 0 if not bad else 1
    print()
    print('ALL PHASE 48 CHECKS PASS' if fails == 0
          else '%d FAILURES' % fails)
    return fails


if __name__ == '__main__':
    sys.exit(1 if main() else 0)
