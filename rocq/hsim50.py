#!/usr/bin/env python3
"""Phase 50 machine tests for the TAIL2_END4 reduction.

Characterisation (from annotated traces of TOP3(j, beta),
j >= 32606; the DIPGRIND-macro trace was cross-checked against
the plain MACROS walker):

  TOP3(j, b) = HB [7493; 3816; 259; 93; 50; 14; 5] 16899 1 32603
               ((2j, 2) :: (1, 1) :: (1, 2)^(b-1)),  r4 = 2j - 65210.

  1. FRONT (the TOP49 front shape, uniform in j): TUP,
     hGRIND_even 16299, TUP2_1, TDN, TUP
     -> GRIND4 = HC [16899; 7493; 3816; 259; 93; 50; 14; 5]
        32602 3 2 ((2j-6, 2) :: tail(b)).
  2. DIPGRIND (32602, r4), r4 >= 2:
     -> HC [16899; 7493; ...] 0 3 2 (spine 32602 ++ W),
        W = ((r4, 2) :: (1, 1) :: (1, 2)^(b-1)).
  3. CASCADE50: a FIXED parse (all frames/counters constant; W
     rides untouched at the bottom), descending the TOP3 frame's
     own blocks and regrowing a new frame:
       PX2A+PUSH+TDN+TUP -> [3816; 259; 93; 50; 14; 5] (16893, 2)
       DIPGRIND (7491, 1911)
       PX2A+PUSH+TDN+TUP -> [93; 50; 14; 5] (3810, 2)
       DIPGRIND (257, 3296)
       PX2A -> [14; 5] g0=91;  hGRIND 44;  POP;  pop12 259
       front(3296) -> HC [309; 14; 5] 612 (3290, 2)
       DIPGRIND (612, 2066)
       PX2A+PUSH+TDN+TUP -> [5] (303, 2);  DIPGRIND (12, 279)
       PX2Bgen;  pop12 1 + POP + pop12 14
       front(279) -> HC [19; 0] 32 (273, 2)
       DIPGRIND (32, 209)
       PX2A0+TUP+TDN+TUP -> [0] (11, 2);  DIPGRIND (3, 5)
       PX2B0 + pop12 4;  TUP+PUSH+TDN+TUP -> [] (8, 2) over (3, 2)
       DIPGRIND (3, 2);  PUSHX + pop12 3
       TUP2_1+TDN -> HB [5] 13 1 4;  pop12 1 + POP + pop12 34
       front(209) -> HC [49; 5] 74 (203, 2)
       DIPGRIND (74, 55)
       PX2A+PUSH+TDN+TUP -> [] (43, 2);  DIPGRIND (3, 37)
       PUSHX + pop12 3;  TUP+PUSH+TDN+TUP -> [] (8, 2) over (35, 2)
       DIPGRIND (3, 2);  PUSHX + pop12 3
       TUP2_1+TDN+TUP -> HC [5] 13 (31, 2);  DIPGRIND (13, 5)
       PX2Bgen;  pop12 1 + POP + pop12 15
       TUP + hGRIND_even 15 + TUP2_1+TDN -> HB [20; 0] 34 1 4
       pop12 1 + POP + pop12 76
       front(55) -> HC [112; 20; 0] 158 (49, 2)
       CLEANG_odd 23;  pop12 1 + POP + pop12 614
       front(2066) -> HC [774; 112; 20; 0] 1284 (2060, 2)
       CLEANG_even 1029 + TRANS2_1;  pop12 7493
       front(1911) -> HC [9558; 1285; 774; 112; 20; 0] 14988
         (1905, 2)
       CLEANG_odd 951;  pop12 1 + POP + pop12 32604
     -> TOP4 = HB [9558; 1285; 774; 112; 20; 0] 47594 1 67121 W.
     (CASCADE50 is stated for an ARBITRARY tail w in Grind18.v;
     Part 1b below probes that generality with a junk tail.
     A "front(g)" is TUP + hGRIND_even t + TUP2_1 + TDN + TUP
     on the pair (g, 2), the TOP48 front shape.)
  4. TOP4 closings by r4 = 2 * j4, j4 = j - 32605:
     r4 = 2:        TRANS2_1 + POPFIN, A = 67121 + b,
                    frame [47595; 9558; 1285; 774; 112; 20; 0].
     r4 = 4:        TUP + hGRIND_even 33558 + TRANS2_2 + POPFIN,
                    A = b + 2, frame [67121; 47594; 9558; ...].
     r4 = 6:        TUP + hGRIND_even 33558 + TUP2_1 + TDN
                    + TRANS2_1 + POPFIN, A = b + 4, frame as r4=4.
     8 <= r4 <= 134246 (band 4): TUP + hGRIND_even 33558 + TUP2_1
                    + TDN + TUP -> GRIND5 = HC [47594; 9558; ...]
                    67120 3 2 ((r4-6, 2) :: tail(b))  -- TUP2_1
                    moves the shuttle 67120 into the counter
                    slot, so the band counter is 67120;
                    CLEANG_even ((r4-8)/2) (floor (r4-8)/2 + 1
                    <= 67120, exactly r4 <= 134246); TRANS2_1
                    + POPFIN, A = r4 + b - 2,
                    frame [67121; 47594; 9558; ...].
     r4 >= 134248:  GRIND5's pair (r4-6, 2) exceeds the
                    CLEANG_even floor; DIPGRIND (67120,
                    r4 - 134246) landing occurs (asserted in
                    Part 3).  This is the residual core
                    TAIL2_END5 (at TOP4, r4 = 2*j4, j4 >= 67124).

Band boundary: r4 <= 134246  <=>  j <= 99728.
"""
import sys
sys.path.insert(0, '/home/hatch/workspace/busy-beaver/rocq')
from hsim45 import mwalk, fmt, MACROS
from hsim41 import step_all
from hsim42 import PROVED_RULES


def swalk(src, max_steps=2000000):
    """Streaming version of hsim45.mwalk: yields each recorded config
    (prim-segment endpoints and macro targets, in order), then a final
    ('STATUS', status, cfg, used_rules) tuple."""
    cfg = src
    prim = 0
    used = set()
    total = 0
    while total < max_steps:
        if cfg[0] == 'B' and not cfg[5]:
            yield ('STATUS', 'DONE', cfg, used)
            return
        hit = None
        for mac in MACROS:
            hit = mac(cfg)
            if hit:
                break
        if hit:
            if prim:
                yield cfg
                prim = 0
            cfg = hit[2]
            total += 1
            yield cfg
            continue
        opts = step_all(cfg)
        assert len(opts) == 1, ('walk stuck/branching', cfg)
        prim += 1
        used.add(opts[0][0])
        cfg = opts[0][1]
        total += 1
    yield ('STATUS', 'CAP', cfg, used)

SP = lambda n: [(1, 2)] * n
TOP3F = (7493, 3816, 259, 93, 50, 14, 5)
TOP4F = (9558, 1285, 774, 112, 20, 0)


def TOP3(j, b):
    return ('B', TOP3F, 16899, 1, 32603,
            ((2 * j, 2), (1, 1)) + tuple(SP(b - 1)), 1)


def W(r4, b):
    return ((r4, 2), (1, 1)) + tuple(SP(b - 1))


def waypoints(j, b):
    """The full asserted waypoint chain TOP3 -> ... -> TOP4."""
    r4 = 2 * j - 65210
    w = W(r4, b)
    tail = ((1, 1),) + tuple(SP(b - 1))
    A1 = ((1911, 2), (1, 1)) + tuple(SP(32604)) + w
    A2 = ((3296, 2), (1, 1)) + tuple(SP(7493)) + A1
    A3 = ((2066, 2), (1, 1)) + tuple(SP(7493)) + A1
    A4 = ((209, 2), (1, 1)) + tuple(SP(614)) + A3
    A5 = ((55, 2), (1, 1)) + tuple(SP(614)) + A3
    A6 = ((279, 2), (1, 1)) + tuple(SP(614)) + A3
    A7 = ((5, 2), (1, 1)) + tuple(SP(34)) + A4
    A8 = ((3, 2), (1, 1)) + tuple(SP(34)) + A4
    A9 = ((37, 2), (1, 1)) + tuple(SP(76)) + A5
    A10 = ((35, 2), (1, 1)) + tuple(SP(76)) + A5
    A11 = ((5, 2), (1, 1)) + tuple(SP(76)) + A5
    F1 = (16899,) + TOP3F
    pts = []
    pts.append(('C', TOP3F, 16899, 32602, 2, ((2 * j - 2, 2),) + tail, 1))
    pts.append(('B', TOP3F, 16898, 1, 32602,
                ((2, 2), (2 * j - 2, 2)) + tail, 1))
    pts.append(('C', F1, 32602, 3, 2, ((2 * j - 6, 2),) + tail, 1))
    pts.append(('C', F1, 0, 3, 2, tuple(SP(32602)) + w, 1))
    pts.append(('C', (3816, 259, 93, 50, 14, 5), 7491, 3, 2,
                ((16893, 2), (1, 1)) + tuple(SP(32604)) + w, 1))
    pts.append(('C', (3816, 259, 93, 50, 14, 5), 0, 3, 2,
                tuple(SP(7491)) + A1, 1))
    pts.append(('C', (93, 50, 14, 5), 257, 3, 2,
                ((3810, 2), (1, 1)) + tuple(SP(7493)) + A1, 1))
    pts.append(('C', (93, 50, 14, 5), 0, 3, 2, tuple(SP(257)) + A2, 1))
    pts.append(('C', (14, 5), 49, 91, 2, ((1, 1),) + tuple(SP(259)) + A2, 1))
    pts.append(('B', (14, 5), 49, 1, 94, ((1, 1),) + tuple(SP(259)) + A2, 1))
    pts.append(('B', (14, 5), 50, 1, 95, tuple(SP(259)) + A2, 1))
    pts.append(('B', (14, 5), 309, 1, 613, A2, 1))
    pts.append(('C', (14, 5), 309, 612, 2,
                ((3294, 2), (1, 1)) + tuple(SP(7493)) + A1, 1))
    pts.append(('B', (14, 5), 308, 1, 612,
                ((2, 2), (3294, 2), (1, 1)) + tuple(SP(7493)) + A1, 1))
    pts.append(('C', (309, 14, 5), 612, 3, 2,
                ((3290, 2), (1, 1)) + tuple(SP(7493)) + A1, 1))
    pts.append(('C', (309, 14, 5), 0, 3, 2, tuple(SP(612)) + A3, 1))
    pts.append(('C', (5,), 12, 3, 2,
                ((303, 2), (1, 1)) + tuple(SP(614)) + A3, 1))
    pts.append(('C', (5,), 0, 3, 2, tuple(SP(12)) + A6, 1))
    pts.append(('B', (0,), 3, 1, 2,
                ((1, 2), (1, 1)) + tuple(SP(14)) + A6, 1))
    pts.append(('B', (0,), 4, 1, 4, ((1, 1),) + tuple(SP(14)) + A6, 1))
    pts.append(('B', (0,), 5, 1, 5, tuple(SP(14)) + A6, 1))
    pts.append(('B', (0,), 19, 1, 33, A6, 1))
    pts.append(('C', (0,), 19, 32, 2,
                ((277, 2), (1, 1)) + tuple(SP(614)) + A3, 1))
    pts.append(('B', (0,), 18, 1, 32,
                ((2, 2), (277, 2), (1, 1)) + tuple(SP(614)) + A3, 1))
    pts.append(('C', (19, 0), 32, 3, 2,
                ((273, 2), (1, 1)) + tuple(SP(614)) + A3, 1))
    pts.append(('C', (19, 0), 0, 3, 2, tuple(SP(32)) + A4, 1))
    pts.append(('C', (0,), 3, 3, 2,
                ((11, 2), (1, 1)) + tuple(SP(34)) + A4, 1))
    pts.append(('C', (0,), 0, 3, 2, tuple(SP(3)) + A7, 1))
    pts.append(('B', (), 0, 1, 5, tuple(SP(4)) + A7, 1))
    pts.append(('B', (), 4, 1, 13, A7, 1))
    pts.append(('C', (), 3, 3, 2, ((8, 2),) + A8, 1))
    pts.append(('C', (), 0, 3, 2, tuple(SP(3)) + ((2, 2),) + A8, 1))
    pts.append(('B', (), 1, 1, 7, tuple(SP(3)) + ((2, 2),) + A8, 1))
    pts.append(('B', (), 4, 1, 13, ((2, 2),) + A8, 1))
    pts.append(('B', (5,), 13, 1, 4,
                ((1, 2), (1, 1)) + tuple(SP(34)) + A4, 1))
    pts.append(('B', (5,), 14, 1, 6, ((1, 1),) + tuple(SP(34)) + A4, 1))
    pts.append(('B', (5,), 15, 1, 7, tuple(SP(34)) + A4, 1))
    pts.append(('B', (5,), 49, 1, 75, A4, 1))
    pts.append(('C', (5,), 49, 74, 2,
                ((207, 2), (1, 1)) + tuple(SP(614)) + A3, 1))
    pts.append(('B', (5,), 48, 1, 74,
                ((2, 2), (207, 2), (1, 1)) + tuple(SP(614)) + A3, 1))
    pts.append(('C', (49, 5), 74, 3, 2,
                ((203, 2), (1, 1)) + tuple(SP(614)) + A3, 1))
    pts.append(('C', (49, 5), 0, 3, 2, tuple(SP(74)) + A5, 1))
    pts.append(('C', (), 3, 3, 2,
                ((43, 2), (1, 1)) + tuple(SP(76)) + A5, 1))
    pts.append(('C', (), 0, 3, 2, tuple(SP(3)) + A9, 1))
    pts.append(('B', (), 1, 1, 7, tuple(SP(3)) + A9, 1))
    pts.append(('B', (), 4, 1, 13, A9, 1))
    pts.append(('C', (), 3, 3, 2, ((8, 2),) + A10, 1))
    pts.append(('C', (), 0, 3, 2, tuple(SP(3)) + ((2, 2),) + A10, 1))
    pts.append(('B', (), 1, 1, 7, tuple(SP(3)) + ((2, 2),) + A10, 1))
    pts.append(('B', (), 4, 1, 13, ((2, 2),) + A10, 1))
    pts.append(('C', (5,), 13, 3, 2,
                ((31, 2), (1, 1)) + tuple(SP(76)) + A5, 1))
    pts.append(('C', (5,), 0, 3, 2, tuple(SP(13)) + A11, 1))
    pts.append(('B', (0,), 3, 1, 2,
                ((1, 2), (1, 1)) + tuple(SP(15)) + A11, 1))
    pts.append(('B', (0,), 4, 1, 4, ((1, 1),) + tuple(SP(15)) + A11, 1))
    pts.append(('B', (0,), 5, 1, 5, tuple(SP(15)) + A11, 1))
    pts.append(('B', (0,), 20, 1, 35, A11, 1))
    pts.append(('C', (0,), 20, 34, 2,
                ((3, 2), (1, 1)) + tuple(SP(76)) + A5, 1))
    pts.append(('B', (0,), 19, 1, 34,
                ((2, 2), (3, 2), (1, 1)) + tuple(SP(76)) + A5, 1))
    pts.append(('B', (20, 0), 34, 1, 4,
                ((1, 2), (1, 1)) + tuple(SP(76)) + A5, 1))
    pts.append(('B', (20, 0), 35, 1, 6, ((1, 1),) + tuple(SP(76)) + A5, 1))
    pts.append(('B', (20, 0), 36, 1, 7, tuple(SP(76)) + A5, 1))
    pts.append(('B', (20, 0), 112, 1, 159, A5, 1))
    pts.append(('C', (20, 0), 112, 158, 2,
                ((53, 2), (1, 1)) + tuple(SP(614)) + A3, 1))
    pts.append(('B', (20, 0), 111, 1, 158,
                ((2, 2), (53, 2), (1, 1)) + tuple(SP(614)) + A3, 1))
    pts.append(('C', (112, 20, 0), 158, 3, 2,
                ((49, 2), (1, 1)) + tuple(SP(614)) + A3, 1))
    pts.append(('B', (112, 20, 0), 158, 1, 54,
                ((1, 2), (1, 1)) + tuple(SP(614)) + A3, 1))
    pts.append(('B', (112, 20, 0), 159, 1, 56,
                ((1, 1),) + tuple(SP(614)) + A3, 1))
    pts.append(('B', (112, 20, 0), 160, 1, 57, tuple(SP(614)) + A3, 1))
    pts.append(('B', (112, 20, 0), 774, 1, 1285, A3, 1))
    pts.append(('C', (112, 20, 0), 774, 1284, 2,
                ((2064, 2), (1, 1)) + tuple(SP(7493)) + A1, 1))
    pts.append(('B', (112, 20, 0), 773, 1, 1284,
                ((2, 2), (2064, 2), (1, 1)) + tuple(SP(7493)) + A1, 1))
    pts.append(('C', (774, 112, 20, 0), 1284, 3, 2,
                ((2060, 2), (1, 1)) + tuple(SP(7493)) + A1, 1))
    pts.append(('B', (774, 112, 20, 0), 1284, 1, 2064,
                ((2, 2), (1, 1)) + tuple(SP(7493)) + A1, 1))
    pts.append(('B', (1285, 774, 112, 20, 0), 2065, 1, 3,
                tuple(SP(7493)) + A1, 1))
    pts.append(('B', (1285, 774, 112, 20, 0), 9558, 1, 14989, A1, 1))
    pts.append(('C', (1285, 774, 112, 20, 0), 9558, 14988, 2,
                ((1909, 2), (1, 1)) + tuple(SP(32604)) + w, 1))
    pts.append(('B', (1285, 774, 112, 20, 0), 9557, 1, 14988,
                ((2, 2), (1909, 2), (1, 1)) + tuple(SP(32604)) + w, 1))
    pts.append(('C', (9558, 1285, 774, 112, 20, 0), 14988, 3, 2,
                ((1905, 2), (1, 1)) + tuple(SP(32604)) + w, 1))
    pts.append(('B', (9558, 1285, 774, 112, 20, 0), 14988, 1, 1910,
                ((1, 2), (1, 1)) + tuple(SP(32604)) + w, 1))
    pts.append(('B', (9558, 1285, 774, 112, 20, 0), 14989, 1, 1912,
                ((1, 1),) + tuple(SP(32604)) + w, 1))
    pts.append(('B', (9558, 1285, 774, 112, 20, 0), 14990, 1, 1913,
                tuple(SP(32604)) + w, 1))
    pts.append(('B', TOP4F, 47594, 1, 67121, w, 1))
    return pts


def norm(cfg):
    st, pb, A, g0, s, pairs, G = cfg
    return (st, tuple(pb), A, g0, s, tuple(pairs), G)


def check_chain(j, b, cap=2000000):
    pts = [norm(p) for p in waypoints(j, b)]
    pos = -1
    status = fin = None
    used = set()
    nrec = 0
    for rec in swalk(TOP3(j, b), max_steps=cap):
        if isinstance(rec, tuple) and rec and rec[0] == 'STATUS':
            status, fin, used = rec[1], rec[2], rec[3]
            break
        nrec += 1
        if pos + 1 < len(pts) and norm(rec) == pts[pos + 1]:
            pos += 1
    assert pos == len(pts) - 1, \
        'j=%d b=%d: waypoint %d missing: %s' \
        % (j, b, pos + 1, fmt(pts[pos + 1]))
    return status, fin, pos, used


def main():
    fails = 0
    used = set()
    # Part 1: full waypoint chain TOP3 -> TOP4, several bands.
    for (j, b) in [(32606, 2), (32606, 3), (32607, 2), (40000, 2),
                   (99728, 2)]:
        try:
            status, fin, pos, u = check_chain(j, b)
            used.update(u)
            print('PASS chain j=%d b=%d: %d waypoints in order, '
                  'walk %s' % (j, b, len(waypoints(j, b)), status))
        except AssertionError as e:
            fails += 1
            print('FAIL', e)
    # Part 1b: CASCADE50 is tail-general -- junk tail probe.
    w0 = ((7, 2), (1, 1), (3, 2), (1, 2))
    src = ('C', (16899,) + TOP3F, 0, 3, 2, tuple(SP(32602)) + w0, 1)
    top4 = norm(('B', TOP4F, 47594, 1, 67121, w0, 1))
    ok = False
    for rec in swalk(src, max_steps=600000):
        if isinstance(rec, tuple) and rec and rec[0] == 'STATUS':
            break
        if norm(rec) == top4:
            ok = True
    print(('PASS' if ok else 'FAIL'),
          'tail-generality: TOP4 shape reached with junk tail')
    fails += 0 if ok else 1
    # Part 2: TOP4-closing finals.
    F6 = (47595, 9558, 1285, 774, 112, 20, 0)
    F7 = (67121, 47594, 9558, 1285, 774, 112, 20, 0)
    finals = {
        (32606, 2): (F6, 67123),
        (32606, 3): (F6, 67124),
        (32607, 2): (F7, 4),
        (32607, 3): (F7, 5),
        (32608, 2): (F7, 6),
        (32609, 2): (F7, 8),
        (32609, 3): (F7, 9),
        (40000, 3): (F7, 14791),
        (99728, 2): (F7, 134246),
    }
    for (j, b), (fr, A) in sorted(finals.items()):
        status = fin = None
        for rec in swalk(TOP3(j, b), max_steps=2000000):
            if isinstance(rec, tuple) and rec and rec[0] == 'STATUS':
                status, fin = rec[1], rec[2]
                break
        want = ('B', tuple(fr), A, 1, 2 * b + 1, (), 1)
        ok = status == 'DONE' and norm(fin) == want
        print(('PASS' if ok else 'FAIL'),
              'final j=%d b=%d: %s (want A=%d frame %s)'
              % (j, b, fmt(fin), A, list(fr)))
        fails += 0 if ok else 1
    # Part 3: the fifth fence -- r4 >= 134248 takes DIPGRIND at 67120.
    for (j, b) in [(99729, 2), (99800, 2), (120000, 2)]:
        r4 = 2 * j - 65210
        g5 = norm(('C', (47594,) + TOP4F, 67120, 3, 2,
                   ((r4 - 6, 2), (1, 1)) + tuple(SP(b - 1)), 1))
        dip5 = norm(('C', (47594,) + TOP4F, 0, 3, 2,
                     tuple(SP(67120))
                     + ((r4 - 134246, 2), (1, 1)) + tuple(SP(b - 1)), 1))
        seen_g5 = seen_dip5 = False
        for rec in swalk(TOP3(j, b), max_steps=1000000):
            if isinstance(rec, tuple) and rec and rec[0] == 'STATUS':
                break
            n = norm(rec)
            if n == g5:
                seen_g5 = True
            elif seen_g5 and n == dip5:
                seen_dip5 = True
        ok = seen_g5 and seen_dip5
        print(('PASS' if ok else 'FAIL'),
              'fence j=%d: GRIND5 then fifth DIPGRIND landing '
              'occur (r4=%d)' % (j, r4))
        fails += 0 if ok else 1
    # Part 4: primitive-step audit.
    bad = used - PROVED_RULES
    print(('PASS' if not bad else 'FAIL'),
          'primitive rules used %s all in PROVED_RULES'
          % (sorted(used),))
    fails += 0 if not bad else 1
    print()
    print('ALL PHASE 50 CHECKS PASS' if fails == 0
          else '%d FAILURES' % fails)
    return fails


if __name__ == '__main__':
    sys.exit(1 if main() else 0)
