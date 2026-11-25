#!/usr/bin/env python3
"""Phase 49 machine tests for the TAIL2_END3 reduction.

Characterisation (from mwalk traces of TOP2(j, beta), j >= 16302):

  TOP2(j, b) = HB [1589; 225; 40; 14; 5] 10430 1 16299
               ((2j, 2) :: (1, 1) :: (1, 2)^(b-1)),  r = 2j >= 32604.

  1. FRONT (the TOP48_BAND front, uniform in j >= 4): TUP,
     hGRIND_even 8147, TUP2_1, TDN, TUP
     -> GRIND3 = HC [10430; 1589; 225; 40; 14; 5] 16298 3 2
        ((2j-6, 2) :: tail(b)).
  2. DIPGRIND (16298, r - 32602), r - 32602 >= 2:
     -> HC [10430; 1589; ...] 0 3 2 (spine 16298 ++ W),
        W = ((r - 32602, 2) :: tail(b)).
  3. CASCADE49: a FIXED parse (all frames/counters constant; W
     rides untouched at the bottom), descending the TOP2 frame's
     own blocks and regrowing a new frame:
       PX2A+PUSH+TDN+TUP -> [225; 40; 14; 5] (10424, 2)
       DIPGRIND (1587, 7250)
       PX2A+PUSH+TDN+TUP -> [14; 5] (219, 2)
       DIPGRIND (38, 143)
       PX2A+PUSH+TDN+TUP -> [] (8, 2);  DIPGRIND (3, 2)
       PUSHX + pop12 3 + TRANS2_1 -> HB [5] 14 1 3
       pop12 40 + front(143) -> HC [54; 5] 82 (137, 2)
       CLEANG_odd 67;  pop12 1 + POP + pop12 1589 + front(7250)
         -> HC [1673; 54; 5] 3322 (7244, 2)
       DIPGRIND (3322, 600)
       PX2A+PUSH+TDN+TUP -> [5] (1667, 2);  DIPGRIND (52, 1563)
       PX2Bgen;  pop12 1 + POP + pop12 54 + front(1563)
         -> HC [59; 0] 112 (1557, 2)
       DIPGRIND (112, 1333)
       PX2A0+TUP+TDN+TUP -> [0] (51, 2);  DIPGRIND (3, 45)
       PX2B0 + pop12 4;  TUP+PUSH+TDN+TUP -> [] (8, 2) over (43, 2)
       DIPGRIND (3, 2);  PUSHX + pop12 3 + TUP2_1+TDN+TUP
         -> HC [5] 13 (39, 2)
       DIPGRIND (13, 13);  PX2Bgen
       pop12 1 + POP + pop12 15 + front(13) -> HC [20; 0] 34 (7, 2)
       CLEANG_odd 2;  pop12 1 + POP + pop12 114 + front(1333)
         -> HC [150; 20; 0] 242 (1327, 2)
       DIPGRIND (242, 843)
       PX2A+PUSH+TDN+TUP -> [0] (144, 2);  DIPGRIND (18, 108)
       PX2B0 + pop12 19;  TUP+PUSH+TDN+TUP -> [] (38, 2) over (106, 2)
       DIPGRIND (18, 2);  PUSHX + pop12 18 + TUP2_1+TDN+TUP
         -> HC [20] 43 (102, 2)
       DIPGRIND (43, 16)
       PX2Bgen+TUP+TDN+TUP -> [0] (12, 2);  DIPGRIND (3, 6)
       PX2B0 + pop12 4;  TUP+PUSH+TDN+TUP -> [] (8, 2) over (4, 2)
       DIPGRIND (3, 2);  PUSHX + pop12 3 + TUP2_1+TDN+TRANS2_1
         -> HB [14; 5] 5 1 3
       pop12 45 + front(16) -> HC [50; 14; 5] 92 (10, 2)
       CLEANG_even 4 + TRANS2_1 -> HB [93; 50; 14; 5] 15 1 3
       pop12 244 + front(843) -> HC [259; 93; 50; 14; 5] 490 (837, 2)
       CLEANG_odd 417;  pop12 1 + POP + pop12 3324 + front(600)
         -> HC [3816; 259; 93; 50; 14; 5] 7492 (594, 2)
       CLEANG_even 296 + TRANS2_1
     -> TOP3 = HB [7493; 3816; 259; 93; 50; 14; 5] 16899 1 32603 W.
     (CASCADE49 is stated for an ARBITRARY tail w in Grind17.v;
     Part 1b below probes that generality with a junk tail.
     A "front(g)" is TUP + hGRIND_even t + TUP2_1 + TDN + TUP
     on the pair (g, 2), the TOP48 front shape.)
  4. TOP3 closings by r3 = r - 32602 = 2 * j3, j3 = j - 16301:
     r3 = 2:        TRANS2_1 + POPFIN, A = 32603 + b,
                    frame [16900; 7493; 3816; 259; 93; 50; 14; 5].
     r3 = 4:        TUP + hGRIND_even 16299 + TRANS2_2 + POPFIN,
                    A = b + 2, frame [32603; 16899; 7493; ...].
     r3 = 6:        TUP + hGRIND_even 16299 + TUP2_1 + TDN
                    + TRANS2_1 + POPFIN, A = b + 4, frame as r3=4.
     8 <= r3 <= 65210 (band 3): TUP + hGRIND_even 16299 + TUP2_1
                    + TDN + TUP -> GRIND4 = HC [16899; 7493; ...]
                    32602 3 2 ((r3-6, 2) :: tail(b))  -- TUP2_1
                    moves the shuttle 32602 into the counter
                    slot, so the band counter is 32602;
                    CLEANG_even ((r3-8)/2) (floor (r3-8)/2 + 1
                    <= 32602, exactly r3 <= 65210); TRANS2_1
                    + POPFIN, A = r3 + b - 2,
                    frame [32603; 16899; 7493; ...].
     r3 >= 65212:   GRIND4's pair (r3-6, 2) exceeds the
                    CLEANG_even floor; DIPGRIND (32602,
                    r3 - 65210) landing occurs (asserted in
                    Part 3).  This is the residual core
                    TAIL2_END4 (at TOP3, r3 = 2*j3, j3 >= 32606).

Band boundary: r3 <= 65210  <=>  j <= 48906.
"""
import sys
sys.path.insert(0, '/home/hatch/workspace/busy-beaver/rocq')
from hsim45 import mwalk, fmt, MACROS
from hsim41 import step_all
from hsim42 import PROVED_RULES


def swalk(src, max_steps=100000):
    """Streaming version of hsim45.mwalk: yields each recorded config
    (prim-segment endpoints and macro targets, in order), then a final
    ('STATUS', status, cfg, used_rules) tuple.  Avoids storing the
    whole history (the stacks here are ~50k pairs per config)."""
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
TOP2F = (1589, 225, 40, 14, 5)
TOP3F = (7493, 3816, 259, 93, 50, 14, 5)


def TOP2(j, b):
    return ('B', TOP2F, 10430, 1, 16299,
            ((2 * j, 2), (1, 1)) + tuple(SP(b - 1)), 1)


def W(r, b):
    return ((r, 2), (1, 1)) + tuple(SP(b - 1))


def waypoints(j, b):
    """The full asserted waypoint chain TOP2 -> ... -> TOP3."""
    r = 2 * j - 32602
    w = W(r, b)
    tail = ((1, 1),) + tuple(SP(b - 1))
    U1 = ((7250, 2), (1, 1)) + tuple(SP(16300)) + w
    U2 = ((143, 2), (1, 1)) + tuple(SP(1589)) + U1
    U4 = ((600, 2), (1, 1)) + tuple(SP(16300)) + w
    U5 = ((1563, 2), (1, 1)) + tuple(SP(3324)) + U4
    U6 = ((1333, 2), (1, 1)) + tuple(SP(3324)) + U4
    U7 = ((45, 2), (1, 1)) + tuple(SP(114)) + U6
    U7p = ((43, 2), (1, 1)) + tuple(SP(114)) + U6
    U8 = ((13, 2), (1, 1)) + tuple(SP(114)) + U6
    U9 = ((843, 2), (1, 1)) + tuple(SP(3324)) + U4
    U10 = ((108, 2), (1, 1)) + tuple(SP(244)) + U9
    U10p = ((106, 2), (1, 1)) + tuple(SP(244)) + U9
    U11 = ((16, 2), (1, 1)) + tuple(SP(244)) + U9
    U12 = ((6, 2), (1, 1)) + tuple(SP(45)) + U11
    U12p = ((4, 2), (1, 1)) + tuple(SP(45)) + U11
    F1 = (10430,) + TOP2F
    pts = []
    pts.append(('C', F1, 16298, 3, 2, ((2 * j - 6, 2),) + tail, 1))
    pts.append(('C', F1, 0, 3, 2, tuple(SP(16298)) + w, 1))
    pts.append(('C', (225, 40, 14, 5), 1587, 3, 2,
                ((10424, 2), (1, 1)) + tuple(SP(16300)) + w, 1))
    pts.append(('C', (225, 40, 14, 5), 0, 3, 2,
                tuple(SP(1587)) + U1, 1))
    pts.append(('C', (14, 5), 38, 3, 2,
                ((219, 2), (1, 1)) + tuple(SP(1589)) + U1, 1))
    pts.append(('C', (14, 5), 0, 3, 2, tuple(SP(38)) + U2, 1))
    pts.append(('C', (), 3, 3, 2,
                ((8, 2), (1, 1)) + tuple(SP(40)) + U2, 1))
    pts.append(('C', (), 0, 3, 2,
                tuple(SP(3)) + ((2, 2), (1, 1)) + tuple(SP(40)) + U2, 1))
    pts.append(('B', (5,), 14, 1, 3, tuple(SP(40)) + U2, 1))
    pts.append(('C', (54, 5), 82, 3, 2,
                ((137, 2), (1, 1)) + tuple(SP(1589)) + U1, 1))
    pts.append(('B', (54, 5), 82, 1, 142,
                ((1, 2), (1, 1)) + tuple(SP(1589)) + U1, 1))
    pts.append(('C', (1673, 54, 5), 3322, 3, 2,
                ((7244, 2), (1, 1)) + tuple(SP(16300)) + w, 1))
    pts.append(('C', (1673, 54, 5), 0, 3, 2,
                tuple(SP(3322)) + U4, 1))
    pts.append(('C', (5,), 52, 3, 2,
                ((1667, 2), (1, 1)) + tuple(SP(3324)) + U4, 1))
    pts.append(('C', (5,), 0, 3, 2, tuple(SP(52)) + U5, 1))
    pts.append(('B', (0,), 3, 1, 2,
                ((1, 2), (1, 1)) + tuple(SP(54)) + U5, 1))
    pts.append(('C', (59, 0), 112, 3, 2,
                ((1557, 2), (1, 1)) + tuple(SP(3324)) + U4, 1))
    pts.append(('C', (59, 0), 0, 3, 2, tuple(SP(112)) + U6, 1))
    pts.append(('C', (0,), 3, 3, 2,
                ((51, 2), (1, 1)) + tuple(SP(114)) + U6, 1))
    pts.append(('C', (0,), 0, 3, 2, tuple(SP(3)) + U7, 1))
    pts.append(('B', (), 0, 1, 5, tuple(SP(4)) + U7, 1))
    pts.append(('C', (), 3, 3, 2, ((8, 2),) + U7p, 1))
    pts.append(('C', (), 0, 3, 2, tuple(SP(3)) + ((2, 2),) + U7p, 1))
    pts.append(('C', (5,), 13, 3, 2,
                ((39, 2), (1, 1)) + tuple(SP(114)) + U6, 1))
    pts.append(('C', (5,), 0, 3, 2, tuple(SP(13)) + U8, 1))
    pts.append(('B', (0,), 3, 1, 2,
                ((1, 2), (1, 1)) + tuple(SP(15)) + U8, 1))
    pts.append(('C', (20, 0), 34, 3, 2,
                ((7, 2), (1, 1)) + tuple(SP(114)) + U6, 1))
    pts.append(('B', (20, 0), 34, 1, 12,
                ((1, 2), (1, 1)) + tuple(SP(114)) + U6, 1))
    pts.append(('C', (150, 20, 0), 242, 3, 2,
                ((1327, 2), (1, 1)) + tuple(SP(3324)) + U4, 1))
    pts.append(('C', (150, 20, 0), 0, 3, 2,
                tuple(SP(242)) + U9, 1))
    pts.append(('C', (0,), 18, 3, 2,
                ((144, 2), (1, 1)) + tuple(SP(244)) + U9, 1))
    pts.append(('C', (0,), 0, 3, 2, tuple(SP(18)) + U10, 1))
    pts.append(('B', (), 0, 1, 5, tuple(SP(19)) + U10, 1))
    pts.append(('C', (), 18, 3, 2, ((38, 2),) + U10p, 1))
    pts.append(('C', (), 0, 3, 2,
                tuple(SP(18)) + ((2, 2),) + U10p, 1))
    pts.append(('C', (20,), 43, 3, 2,
                ((102, 2), (1, 1)) + tuple(SP(244)) + U9, 1))
    pts.append(('C', (20,), 0, 3, 2, tuple(SP(43)) + U11, 1))
    pts.append(('C', (0,), 3, 3, 2,
                ((12, 2), (1, 1)) + tuple(SP(45)) + U11, 1))
    pts.append(('C', (0,), 0, 3, 2, tuple(SP(3)) + U12, 1))
    pts.append(('B', (), 0, 1, 5, tuple(SP(4)) + U12, 1))
    pts.append(('C', (), 3, 3, 2, ((8, 2),) + U12p, 1))
    pts.append(('C', (), 0, 3, 2,
                tuple(SP(3)) + ((2, 2),) + U12p, 1))
    pts.append(('B', (14, 5), 5, 1, 3, tuple(SP(45)) + U11, 1))
    pts.append(('C', (50, 14, 5), 92, 3, 2,
                ((10, 2), (1, 1)) + tuple(SP(244)) + U9, 1))
    pts.append(('B', (93, 50, 14, 5), 15, 1, 3,
                tuple(SP(244)) + U9, 1))
    pts.append(('C', (259, 93, 50, 14, 5), 490, 3, 2,
                ((837, 2), (1, 1)) + tuple(SP(3324)) + U4, 1))
    pts.append(('B', (259, 93, 50, 14, 5), 490, 1, 842,
                ((1, 2), (1, 1)) + tuple(SP(3324)) + U4, 1))
    pts.append(('C', (3816, 259, 93, 50, 14, 5), 7492, 3, 2,
                ((594, 2), (1, 1)) + tuple(SP(16300)) + w, 1))
    pts.append(('B', TOP3F, 16899, 1, 32603, w, 1))
    return pts


def norm(cfg):
    st, pb, A, g0, s, pairs, G = cfg
    return (st, tuple(pb), A, g0, s, tuple(pairs), G)


def check_chain(j, b, cap=400000):
    pts = [norm(p) for p in waypoints(j, b)]
    pos = -1
    status = fin = None
    used = set()
    nrec = 0
    for rec in swalk(TOP2(j, b), max_steps=cap):
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
    # Part 1: full waypoint chain TOP2 -> TOP3, several bands.
    for (j, b) in [(16302, 2), (16302, 3), (16303, 2), (20000, 2),
                   (48906, 2)]:
        try:
            status, fin, pos, u = check_chain(j, b)
            used.update(u)
            print('PASS chain j=%d b=%d: %d waypoints in order, '
                  'walk %s' % (j, b, len(waypoints(j, b)), status))
        except AssertionError as e:
            fails += 1
            print('FAIL', e)
    # Part 1b: CASCADE49 is tail-general -- junk tail probe.
    w0 = ((7, 2), (1, 1), (3, 2), (1, 2))
    src = ('C', (10430,) + TOP2F, 0, 3, 2, tuple(SP(16298)) + w0, 1)
    top3 = norm(('B', TOP3F, 16899, 1, 32603, w0, 1))
    ok = False
    for rec in swalk(src, max_steps=200000):
        if isinstance(rec, tuple) and rec and rec[0] == 'STATUS':
            break
        if norm(rec) == top3:
            ok = True
    print(('PASS' if ok else 'FAIL'),
          'tail-generality: TOP3 shape reached with junk tail')
    fails += 0 if ok else 1
    # Part 2: TOP3-closing finals.
    F4 = (16900, 7493, 3816, 259, 93, 50, 14, 5)
    F5 = (32603, 16899, 7493, 3816, 259, 93, 50, 14, 5)
    finals = {
        (16302, 2): (F4, 32605),
        (16302, 3): (F4, 32606),
        (16303, 2): (F5, 4),
        (16303, 3): (F5, 5),
        (16304, 2): (F5, 6),
        (16305, 2): (F5, 8),
        (20000, 3): (F5, 7399),
        (48906, 2): (F5, 65210),
    }
    for (j, b), (fr, A) in sorted(finals.items()):
        status = fin = None
        for rec in swalk(TOP2(j, b), max_steps=600000):
            if isinstance(rec, tuple) and rec and rec[0] == 'STATUS':
                status, fin = rec[1], rec[2]
                break
        want = ('B', tuple(fr), A, 1, 2 * b + 1, (), 1)
        ok = status == 'DONE' and norm(fin) == want
        print(('PASS' if ok else 'FAIL'),
              'final j=%d b=%d: %s (want A=%d frame %s)'
              % (j, b, fmt(fin), A, list(fr)))
        fails += 0 if ok else 1
    # Part 3: the fourth fence -- r3 >= 65212 takes DIPGRIND at 32602.
    for (j, b) in [(48907, 2), (49000, 2), (60000, 2)]:
        r3 = 2 * j - 32602
        g4 = norm(('C', (16899,) + TOP3F, 32602, 3, 2,
                   ((r3 - 6, 2), (1, 1)) + tuple(SP(b - 1)), 1))
        dip4 = norm(('C', (16899,) + TOP3F, 0, 3, 2,
                     tuple(SP(32602))
                     + ((r3 - 65210, 2), (1, 1)) + tuple(SP(b - 1)), 1))
        seen_g4 = seen_dip4 = False
        for rec in swalk(TOP2(j, b), max_steps=400000):
            if isinstance(rec, tuple) and rec and rec[0] == 'STATUS':
                break
            n = norm(rec)
            if n == g4:
                seen_g4 = True
            elif seen_g4 and n == dip4:
                seen_dip4 = True
        ok = seen_g4 and seen_dip4
        print(('PASS' if ok else 'FAIL'),
              'fence j=%d: GRIND4 then fourth DIPGRIND landing '
              'occur (r3=%d)' % (j, r3))
        fails += 0 if ok else 1
    # Part 4: primitive-step audit.
    bad = used - PROVED_RULES
    print(('PASS' if not bad else 'FAIL'),
          'primitive rules used %s all in PROVED_RULES'
          % (sorted(used),))
    fails += 0 if not bad else 1
    print()
    print('ALL PHASE 49 CHECKS PASS' if fails == 0
          else '%d FAILURES' % fails)
    return fails


if __name__ == '__main__':
    sys.exit(1 if main() else 0)
