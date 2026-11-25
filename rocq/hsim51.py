#!/usr/bin/env python3
"""Phase 51 machine tests for the TAIL2_END5 reduction.

Characterisation (from annotated traces of TOP4(j, beta),
j >= 67124; the DIPGRIND/CLEANG-macro trace was cross-checked
against the plain MACROS walker):

  TOP4(j, b) = HB [9558; 1285; 774; 112; 20; 0] 47594 1 67121
               ((2j, 2) :: (1, 1) :: (1, 2)^(b-1)),  r5 = 2j - 134246.

  1. FRONT (the TOP50 front shape, uniform in j): TUP,
     hGRIND_even 33558, TUP2_1, TDN, TUP
     -> GRIND5 = HC [47594; 9558; 1285; 774; 112; 20; 0]
        67120 3 2 ((2j-6, 2) :: tail(b)).
  2. DIPGRIND (67120, r5), r5 >= 2:
     -> HC [47594; 9558; ...] 0 3 2 (spine 67120 ++ W),
        W = ((r5, 2) :: (1, 1) :: (1, 2)^(b-1)).
  3. CASCADE51: a FIXED parse (all frames/counters constant; W
     rides untouched at the bottom), descending the TOP4 frame's
     own blocks and regrowing a new frame:
       PX2A+PUSH+TDN+TUP -> [1285; 774; 112; 20; 0] (47588, 2)
       DIPGRIND (9556, 28476)
       PX2A -> [112; 20; 0] g0=1283, (1, 1) over spine 9558
       hGRIND 640;  POP;  pop12 9558
       front(28476) -> HC [10332; 112; 20; 0] 20402 (28470, 2)
       CLEANG_even 14234;  TRANS2_1;  pop12 67122
     -> TOP5 = HB [20403; 10332; 112; 20; 0] 95597 1 134247 W.
     (CASCADE51 is stated for an ARBITRARY tail w in Grind19.v;
     Part 1b below probes that generality with a junk tail.
     A "front(g)" is TUP + hGRIND_even t + TUP2_1 + TDN + TUP
     on the pair (g, 2), the TOP50 front shape.)
  4. TOP5 closings by r5 = 2 * j5, j5 = j - 67123:
     r5 = 2:        TRANS2_1 + POPFIN, A = 134247 + b,
                    frame [95598; 20403; 10332; 112; 20; 0].
     r5 = 4:        TUP + hGRIND_even 67121 + TRANS2_2 + POPFIN,
                    A = b + 2, frame [134247; 95597; 20403; ...].
     r5 = 6:        TUP + hGRIND_even 67121 + TUP2_1 + TDN
                    + TRANS2_1 + POPFIN, A = b + 4, frame as r5=4.
     8 <= r5 <= 268498 (band 5): TUP + hGRIND_even 67121 + TUP2_1
                    + TDN + TUP -> GRIND6 = HC [95597; 20403; ...]
                    134246 3 2 ((r5-6, 2) :: tail(b))  -- TUP2_1
                    moves the shuttle 134247 into the counter
                    slot, so the band counter is 134246;
                    CLEANG_even ((r5-8)/2) (floor (r5-8)/2 + 1
                    <= 134246, exactly r5 <= 268498); TRANS2_1
                    + POPFIN, A = r5 + b - 2,
                    frame [134247; 95597; 20403; ...].
     r5 >= 268500:  GRIND6's pair (r5-6, 2) exceeds the
                    CLEANG_even floor; DIPGRIND (134246,
                    r5 - 268498) landing occurs (asserted in
                    Part 3).  This is the residual core
                    TAIL2_END6 (at TOP5, r5 = 2*j5, j5 >= 134250).

Band boundary: r5 <= 268498  <=>  j <= 201372.
"""
import sys
sys.path.insert(0, '/home/hatch/workspace/busy-beaver/rocq')
from hsim45 import mwalk, fmt, MACROS
from hsim41 import step_all
from hsim42 import PROVED_RULES
from hsim50 import swalk, SP


def TOP4(j, b):
    return ('B', TOP4F, 47594, 1, 67121,
            ((2 * j, 2), (1, 1)) + tuple(SP(b - 1)), 1)


def W(r5, b):
    return ((r5, 2), (1, 1)) + tuple(SP(b - 1))


TOP4F = (9558, 1285, 774, 112, 20, 0)
TOP5F = (20403, 10332, 112, 20, 0)
F5 = (47594,) + TOP4F
F1285 = (1285, 774, 112, 20, 0)
F112 = (112, 20, 0)
F10332 = (10332, 112, 20, 0)


def waypoints(j, b):
    """The full asserted waypoint chain TOP4 -> ... -> TOP5."""
    r5 = 2 * j - 134246
    w = W(r5, b)
    tail = ((1, 1),) + tuple(SP(b - 1))
    deep = ((28476, 2), (1, 1)) + tuple(SP(67122)) + w
    pts = []
    pts.append(('C', TOP4F, 47594, 67120, 2, ((2 * j - 2, 2),) + tail, 1))
    pts.append(('B', TOP4F, 47593, 1, 67120,
                ((2, 2), (2 * j - 2, 2)) + tail, 1))
    pts.append(('C', F5, 67120, 3, 2, ((2 * j - 6, 2),) + tail, 1))
    pts.append(('C', F5, 0, 3, 2, tuple(SP(67120)) + w, 1))
    pts.append(('C', F1285, 9556, 3, 2,
                ((47588, 2), (1, 1)) + tuple(SP(67122)) + w, 1))
    pts.append(('C', F1285, 0, 3, 2, tuple(SP(9556)) + deep, 1))
    pts.append(('C', F112, 773, 1283, 2, ((1, 1),) + tuple(SP(9558))
                + deep, 1))
    pts.append(('B', F112, 773, 1, 1286, ((1, 1),) + tuple(SP(9558))
                + deep, 1))
    pts.append(('B', F112, 774, 1, 1287, tuple(SP(9558)) + deep, 1))
    pts.append(('B', F112, 10332, 1, 20403, deep, 1))
    pts.append(('C', F112, 10332, 20402, 2,
                ((28474, 2), (1, 1)) + tuple(SP(67122)) + w, 1))
    pts.append(('B', F112, 10331, 1, 20402,
                ((2, 2), (28474, 2), (1, 1)) + tuple(SP(67122)) + w, 1))
    pts.append(('C', F10332, 20402, 3, 2,
                ((28470, 2), (1, 1)) + tuple(SP(67122)) + w, 1))
    pts.append(('B', F10332, 20402, 1, 28474,
                ((2, 2), (1, 1)) + tuple(SP(67122)) + w, 1))
    pts.append(('B', TOP5F, 28475, 1, 3, tuple(SP(67122)) + w, 1))
    pts.append(('B', TOP5F, 95597, 1, 134247, w, 1))
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
    for rec in swalk(TOP4(j, b), max_steps=cap):
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
    # Part 1: full waypoint chain TOP4 -> TOP5, several bands.
    for (j, b) in [(67124, 2), (67124, 3), (67125, 2), (100000, 2),
                   (201372, 2)]:
        try:
            status, fin, pos, u = check_chain(j, b)
            used.update(u)
            print('PASS chain j=%d b=%d: %d waypoints in order, '
                  'walk %s' % (j, b, len(waypoints(j, b)), status))
        except AssertionError as e:
            fails += 1
            print('FAIL', e)
    # Part 1b: CASCADE51 is tail-general -- junk tail probe.
    w0 = ((7, 2), (1, 1), (3, 2), (1, 2))
    src = ('C', F5, 0, 3, 2, tuple(SP(67120)) + w0, 1)
    top5 = norm(('B', TOP5F, 95597, 1, 134247, w0, 1))
    ok = False
    for rec in swalk(src, max_steps=600000):
        if isinstance(rec, tuple) and rec and rec[0] == 'STATUS':
            break
        if norm(rec) == top5:
            ok = True
    print(('PASS' if ok else 'FAIL'),
          'tail-generality: TOP5 shape reached with junk tail')
    fails += 0 if ok else 1
    # Part 2: TOP5-closing finals.
    F6 = (95598,) + TOP5F
    F7 = (134247, 95597) + TOP5F
    finals = {
        (67124, 2): (F6, 134249),
        (67124, 3): (F6, 134250),
        (67125, 2): (F7, 4),
        (67125, 3): (F7, 5),
        (67126, 2): (F7, 6),
        (67127, 2): (F7, 8),
        (67127, 3): (F7, 9),
        (100000, 3): (F7, 65755),
        (201372, 2): (F7, 268498),
    }
    for (j, b), (fr, A) in sorted(finals.items()):
        status = fin = None
        for rec in swalk(TOP4(j, b), max_steps=2000000):
            if isinstance(rec, tuple) and rec and rec[0] == 'STATUS':
                status, fin = rec[1], rec[2]
                break
        want = ('B', tuple(fr), A, 1, 2 * b + 1, (), 1)
        ok = status == 'DONE' and norm(fin) == want
        print(('PASS' if ok else 'FAIL'),
              'final j=%d b=%d: %s (want A=%d frame %s)'
              % (j, b, fmt(fin), A, list(fr)))
        fails += 0 if ok else 1
    # Part 3: the sixth fence -- r5 >= 268500 takes DIPGRIND at 134246.
    for (j, b) in [(201373, 2), (201374, 2), (210000, 2)]:
        r5 = 2 * j - 134246
        g6 = norm(('C', (95597,) + TOP5F, 134246, 3, 2,
                   ((r5 - 6, 2), (1, 1)) + tuple(SP(b - 1)), 1))
        dip6 = norm(('C', (95597,) + TOP5F, 0, 3, 2,
                     tuple(SP(134246))
                     + ((r5 - 268498, 2), (1, 1)) + tuple(SP(b - 1)), 1))
        seen_g6 = seen_dip6 = False
        for rec in swalk(TOP4(j, b), max_steps=3000000):
            if isinstance(rec, tuple) and rec and rec[0] == 'STATUS':
                break
            n = norm(rec)
            if n == g6:
                seen_g6 = True
            elif seen_g6 and n == dip6:
                seen_dip6 = True
        ok = seen_g6 and seen_dip6
        print(('PASS' if ok else 'FAIL'),
              'fence j=%d: GRIND6 then sixth DIPGRIND landing '
              'occur (r5=%d)' % (j, r5))
        fails += 0 if ok else 1
    # Part 4: primitive-step audit.
    bad = used - PROVED_RULES
    print(('PASS' if not bad else 'FAIL'),
          'primitive rules used %s all in PROVED_RULES'
          % (sorted(used),))
    fails += 0 if not bad else 1
    print()
    print('ALL PHASE 51 CHECKS PASS' if fails == 0
          else '%d FAILURES' % fails)
    return fails


if __name__ == '__main__':
    sys.exit(1 if main() else 0)
