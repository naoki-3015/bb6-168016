#!/usr/bin/env python3
"""hsim46.py — Phase 46 machine checks: the TAIL2_BIG dip descent.

Phase 45 reduced the ESC side of H_LOOP to TAIL2_BIG (Grind13.v):
the layer-2 residue totality at HB [243; 135; 35; 20; 0] 893 1 1651
((2 vM + 2, 2) :: (1, 1) :: (1, 2)^(beta - 1)) for vM >= 1653.
Its front (TUP, hGRIND_even 823, TUP2_1, GG_boundary (1650, vM - 3),
PX2A) lands at

  px(k, beta) = HC [135; 35; 20; 0] 242 891 2 (W0 k beta),
  k = vM - 1652 >= 1,
  W0 k beta = (1, 1) :: (1, 2)^1652 ++ ((2k, 2) :: (1, 1)
              :: (1, 2)^(beta - 1)).

Phase 46 traces the descent from px and finds a FIXED parse,
uniform in (k, beta) — the frame-dependent sub-parses of the
Phase 45 report are the four dip levels of one recursion:

  level at frame [135; 35; 20; 0], A = 241, pair (887, 2):
    boundary rounds (DIPGRIND: hGRIND 0 + GG_rounds_part (A - 1)
    + TUP + DIPDESC A) to the dip pair (405, 2), then PX2A;
  level at frame [20; 0], A = 33, pair (129, 2): DIPGRIND to
    (63, 2), then PX2A0 (the second block is 0);
  level at frame [0], A = 3, pair (12, 2): DIPGRIND to (6, 2),
    then PX2B0, pop12 4, TUP + PUSH + TDN + TUP;
  level at frame [], A = 3, pair (8, 2) over (4, 2): DIPGRIND
    to (2, 2), then PUSHX, pop12 3;
  frame regrowth (TUP2_1, TDN, TRANS2_1) onto [14; 5], pop12 35;
  the (63, 2) pair: TUP + hGRIND_even 34 + TUP2_1 + TDN + TUP
    onto frame [40; 14; 5] at pair (57, 2);
  the (57, 2) pair grinds CLEANLY (CLEANG_odd: rounds to (3, 2),
    TUP, hGRIND) to (1, 2); pop12 1, POP, pop12 243;
  the (405, 2) pair: TUP + hGRIND_even 273 + TUP2_1 + TDN + TUP
    onto frame [317; 40; 14; 5] at pair (399, 2);
  the (399, 2) pair grinds CLEANLY (CLEANG_odd) to (1, 2);
    pop12 1, POP, pop12 1652 — reaching the END state

  END(k, beta) = HB [317; 40; 14; 5] 2204 1 3711
                   ((2k, 2) :: (1, 1) :: (1, 2)^(beta - 1)).

Part 1 asserts every waypoint of this parse, in order, at
(k, beta) in {1, 2, 3, 48, 348, 3713} x {2} + {1, 2} x {3}.

The END state itself closes UNIFORMLY for 1 <= k <= 3713:
  k = 1: TRANS2_1 + POPFIN, final A = 3711 + beta;
  k = 2: TUP + hGRIND_even 1853 + TRANS2_2 + POPFIN,
    final A = beta + 2;
  k = 3: TUP + hGRIND_even 1853 + TUP2_1 + TDN + TRANS2_1
    + POPFIN, final A = beta + 4;
  k >= 4: TUP + hGRIND_even 1853 + TUP2_1 + TDN + TUP, then
    the pair (2k - 6, 2) grinds CLEANLY at counter 3710
    (CLEANG_even: hGRIND 0 + GG_rounds_part (k - 5)
    + grind_round (k - 4)) to (2, 2) — the floor is exactly
    2k - 6 <= 2 * 3710, i.e. k <= 3713 — then TRANS2_1
    + POPFIN, final A = 2k + beta - 2.
Part 2 asserts these parses and finals verbatim.

Part 3: the full TAIL2_BIG source walk at vM in
{1653, 1654, 1655, 2000, 5365} x beta in {2, 3} completes at
exactly those finals (all >= beta): TAIL2_BIG holds for
1653 <= vM <= 5365 (k <= 3713).

Part 4 (the fence): at k = 3714 the END rounds hit the
DIPDESC boundary (the config HC [2204; 317; 40; 14; 5] 3710
7423 ((2, 2) :: (1, 1) :: ...) occurs) and the walk completes
only through a further frame descent — final frame
[4002; 1279; 745; 151; 77; 35; 20; 0], A = 7429 (beta = 2);
at k = 5000 yet another cycle is added (final frame
[7427; 4001; 1279; 745; 151; 77; 35; 20; 0]).  No finite
case analysis in the current vocabulary closes every k;
the residual core TAIL2_END (Grind14.v) is the END totality
for k >= 3714 alone.

Part 5: audit — every primitive step used is in PROVED_RULES.
"""
import sys
sys.path.insert(0, '.')
from hsim41 import step_all
from hsim42 import PROVED_RULES
from hsim45 import mwalk, fmt, spine, config_seq

FAILS = []


def check(cond, msg):
    if cond:
        print('  PASS', msg)
    else:
        print('  FAIL', msg)
        FAILS.append(msg)


P4 = (135, 35, 20, 0)
P2 = (20, 0)
P1 = (0,)
P0 = ()
F14 = (14, 5)
F40 = (40, 14, 5)
F317 = (317, 40, 14, 5)
F5 = (2204,) + F317
F6 = (3711,) + F5


def W0(k, b):
    return ((1, 1),) + tuple(spine(1652)) + ((2 * k, 2), (1, 1)) \
        + tuple(spine(b - 1))


def W1(k, b):
    return ((1, 1),) + tuple(spine(243)) + ((405, 2),) + W0(k, b)


def W2(k, b):
    return ((1, 1),) + tuple(spine(35)) + ((63, 2),) + W1(k, b)


def px(k, b):
    return ('C', P4, 242, 891, 2, W0(k, b), 1)


def END(k, b):
    return ('B', F317, 2204, 1, 3711,
            ((2 * k, 2), (1, 1)) + tuple(spine(b - 1)), 1)


def descent_ckpts(k, b):
    w0, w1, w2 = W0(k, b), W1(k, b), W2(k, b)
    s35 = tuple(spine(35)) + ((63, 2),) + w1
    return [
        ('src', px(k, b)),
        ('L0-in', ('C', P4, 241, 3, 2, ((887, 2),) + w0, 1)),
        ('L0-rounds', ('B', P4, 241, 1, 486, ((407, 2),) + w0, 1)),
        ('L0-dip', ('C', P4, 241, 485, 2, ((405, 2),) + w0, 1)),
        ('L0-out', ('C', P4, 0, 3, 2,
                    tuple(spine(241)) + ((405, 2),) + w0, 1)),
        ('L1-in', ('C', P2, 33, 3, 2, ((129, 2),) + w1, 1)),
        ('L1-rounds', ('B', P2, 33, 1, 70, ((65, 2),) + w1, 1)),
        ('L1-dip', ('C', P2, 33, 69, 2, ((63, 2),) + w1, 1)),
        ('L1-out', ('C', P2, 0, 3, 2,
                    tuple(spine(33)) + ((63, 2),) + w1, 1)),
        ('PX2A0', ('B', P1, 3, 1, 2, ((16, 2), (1, 1)) + s35, 1)),
        ('TUP-a', ('C', P1, 3, 1, 2, ((14, 2), (1, 1)) + s35, 1)),
        ('TDN-a', ('B', P1, 3, 1, 4, ((14, 2), (1, 1)) + s35, 1)),
        ('L2-in', ('C', P1, 3, 3, 2, ((12, 2),) + w2, 1)),
        ('L2-rounds', ('B', P1, 3, 1, 10, ((8, 2),) + w2, 1)),
        ('L2-dip', ('C', P1, 3, 9, 2, ((6, 2),) + w2, 1)),
        ('L2-out', ('C', P1, 0, 3, 2,
                    tuple(spine(3)) + ((6, 2),) + w2, 1)),
        ('PX2B0', ('B', P0, 0, 1, 5,
                   ((1, 2),) + tuple(spine(3)) + ((6, 2),) + w2, 1)),
        ('pop4', ('B', P0, 4, 1, 13, ((6, 2),) + w2, 1)),
        ('TUP-b', ('C', P0, 4, 12, 2, ((4, 2),) + w2, 1)),
        ('L3-in', ('C', P0, 3, 3, 2, ((8, 2), (4, 2)) + w2, 1)),
        ('L3-rounds', ('B', P0, 3, 1, 10, ((4, 2), (4, 2)) + w2, 1)),
        ('L3-dip', ('C', P0, 3, 9, 2, ((2, 2), (4, 2)) + w2, 1)),
        ('L3-out', ('C', P0, 0, 3, 2,
                    tuple(spine(3)) + ((2, 2), (4, 2)) + w2, 1)),
        ('PUSHX', ('B', P0, 1, 1, 7,
                   tuple(spine(3)) + ((2, 2), (4, 2)) + w2, 1)),
        ('pop3', ('B', P0, 4, 1, 13, ((2, 2), (4, 2)) + w2, 1)),
        ('TUP2_1-a', ('C', (5,), 13, 1, 2, ((2, 2),) + w2, 1)),
        ('TDN-b', ('B', (5,), 13, 1, 4, ((2, 2),) + w2, 1)),
        ('TRANS2_1-a', ('B', F14, 5, 1, 3, s35, 1)),
        ('pop35', ('B', F14, 40, 1, 73, ((63, 2),) + w1, 1)),
        ('TUP-c', ('C', F14, 40, 72, 2, ((61, 2),) + w1, 1)),
        ('GE-34', ('B', F14, 39, 1, 72, ((2, 2), (61, 2)) + w1, 1)),
        ('TUP2_1-b', ('C', F40, 72, 1, 2, ((59, 2),) + w1, 1)),
        ('TDN-c', ('B', F40, 72, 1, 4, ((59, 2),) + w1, 1)),
        ('L4-in', ('C', F40, 72, 3, 2, ((57, 2),) + w1, 1)),
        ('CG57-r', ('B', F40, 72, 1, 60, ((3, 2),) + w1, 1)),
        ('CG57-tup', ('C', F40, 72, 59, 2, ((1, 2),) + w1, 1)),
        ('CG57-out', ('B', F40, 72, 1, 62, ((1, 2),) + w1, 1)),
        ('pop1-a', ('B', F40, 73, 1, 64, w1, 1)),
        ('POP-a', ('B', F40, 74, 1, 65,
                   tuple(spine(243)) + ((405, 2),) + w0, 1)),
        ('pop243', ('B', F40, 317, 1, 551, ((405, 2),) + w0, 1)),
        ('TUP-d', ('C', F40, 317, 550, 2, ((403, 2),) + w0, 1)),
        ('GE-273', ('B', F40, 316, 1, 550,
                    ((2, 2), (403, 2)) + w0, 1)),
        ('TUP2_1-c', ('C', F317, 550, 1, 2, ((401, 2),) + w0, 1)),
        ('TDN-d', ('B', F317, 550, 1, 4, ((401, 2),) + w0, 1)),
        ('L5-in', ('C', F317, 550, 3, 2, ((399, 2),) + w0, 1)),
        ('CG399-r', ('B', F317, 550, 1, 402, ((3, 2),) + w0, 1)),
        ('CG399-tup', ('C', F317, 550, 401, 2, ((1, 2),) + w0, 1)),
        ('CG399-out', ('B', F317, 550, 1, 404, ((1, 2),) + w0, 1)),
        ('pop1-b', ('B', F317, 551, 1, 406, w0, 1)),
        ('POP-b', ('B', F317, 552, 1, 407,
                   tuple(spine(1652)) + ((2 * k, 2), (1, 1))
                   + tuple(spine(b - 1)), 1)),
        ('END', END(k, b)),
    ]


def end_ckpts(k, b):
    tail = tuple(spine(b - 1))
    if k == 1:
        return [('E1', ('B', (2205,) + F317, 3712, 1, 3, tail, 1)),
                ('E2', ('B', (2205,) + F317, 3711 + b, 1, 2 * b + 1,
                        (), 1))]
    if k == 2:
        return [('E1', ('C', F317, 2204, 3710, 2,
                        ((2, 2), (1, 1)) + tail, 1)),
                ('E2', ('B', F317, 2203, 1, 3710,
                        ((2, 2), (2, 2), (1, 1)) + tail, 1)),
                ('E3', ('B', F6, 3, 1, 3, tail, 1)),
                ('E4', ('B', F6, b + 2, 1, 2 * b + 1, (), 1))]
    if k == 3:
        return [('E1', ('C', F317, 2204, 3710, 2,
                        ((4, 2), (1, 1)) + tail, 1)),
                ('E2', ('B', F317, 2203, 1, 3710,
                        ((2, 2), (4, 2), (1, 1)) + tail, 1)),
                ('E3', ('C', F5, 3710, 1, 2,
                        ((2, 2), (1, 1)) + tail, 1)),
                ('E4', ('B', F5, 3710, 1, 4,
                        ((2, 2), (1, 1)) + tail, 1)),
                ('E5', ('B', F6, 5, 1, 3, tail, 1)),
                ('E6', ('B', F6, b + 4, 1, 2 * b + 1, (), 1))]
    return [('E1', ('C', F317, 2204, 3710, 2,
                    ((2 * k - 2, 2), (1, 1)) + tail, 1)),
            ('E2', ('B', F317, 2203, 1, 3710,
                    ((2, 2), (2 * k - 2, 2), (1, 1)) + tail, 1)),
            ('E3', ('C', F5, 3710, 1, 2,
                    ((2 * k - 4, 2), (1, 1)) + tail, 1)),
            ('E4', ('B', F5, 3710, 1, 4,
                    ((2 * k - 4, 2), (1, 1)) + tail, 1)),
            ('E5', ('C', F5, 3710, 3, 2,
                    ((2 * k - 6, 2), (1, 1)) + tail, 1)),
            ('E6', ('B', F5, 3710, 1, 2 * k - 2,
                    ((2, 2), (1, 1)) + tail, 1)),
            ('E7', ('B', F6, 2 * k - 1, 1, 3, tail, 1)),
            ('E8', ('B', F6, 2 * k + b - 2, 1, 2 * b + 1, (), 1))]


def expand_seq(steps, src):
    """Full config sequence: macro steps are single entries, but
    mwalk's prim bundles collapse several primitive steps into one
    entry — replay them through step_all so bundle-intermediate
    configs (PX2A0 / TUP2_1 landings, ...) appear."""
    seq = [src]
    cur = src
    for st in steps:
        if st[0] == 'macro':
            cur = st[4]
            seq.append(cur)
        else:
            for r in st[2]:
                opts = step_all(cur)
                assert len(opts) == 1 and opts[0][0] == r, \
                    (cur, r, opts)
                cur = opts[0][1]
                seq.append(cur)
    return seq


def assert_in_order(seq, ckpts):
    idx = []
    for name, cfg in ckpts:
        if cfg not in seq:
            return False, name, idx
        idx.append(seq.index(cfg))
    mono = all(idx[i] < idx[i + 1] for i in range(len(idx) - 1))
    return mono, None, idx


USED = set()


def collect(steps):
    for st in steps:
        if st[0] == 'prim':
            USED.update(st[2])


print('== Part 1: the descent px -> END, all waypoints ==')
for (k, b) in [(1, 2), (2, 2), (3, 2), (48, 2), (348, 2),
               (3713, 2), (1, 3), (2, 3)]:
    steps, status, fin = mwalk(px(k, b), max_steps=200000)
    collect(steps)
    seq = expand_seq(steps, px(k, b))
    ok, miss, idx = assert_in_order(seq, descent_ckpts(k, b))
    check(ok and status == 'DONE' and fin == end_ckpts(k, b)[-1][1],
          'descent k=%d beta=%d: %d waypoints in order, passes END '
          'and completes' % (k, b, len(descent_ckpts(k, b)))
          + ('' if ok else ' (missing/out-of-order: %s)' % miss))

print('== Part 2: END processing, 1 <= k <= 3713 ==')
for (k, b) in [(1, 2), (2, 2), (3, 2), (4, 2), (5, 2), (10, 2),
               (100, 2), (3712, 2), (3713, 2), (4, 3), (3713, 3)]:
    steps, status, fin = mwalk(END(k, b), max_steps=300000)
    collect(steps)
    seq = expand_seq(steps, END(k, b))
    ck = end_ckpts(k, b)
    ok, miss, idx = assert_in_order(seq, ck)
    exp_fin = ck[-1][1]
    check(ok and status == 'DONE' and fin == exp_fin,
          'END k=%d beta=%d: parse in order, final A=%d'
          % (k, b, exp_fin[2])
          + ('' if ok else ' (missing/out-of-order: %s)' % miss))

print('== Part 3: full TAIL2_BIG source walks, k <= 3713 ==')
FSTAR = (243, 135, 35, 20, 0)
for (vM, b) in [(1653, 2), (1654, 2), (1655, 2), (2000, 2),
                (5365, 2), (1653, 3), (1654, 3), (5365, 3)]:
    k = vM - 1652
    src = ('B', FSTAR, 893, 1, 1651,
           ((2 * vM + 2, 2), (1, 1)) + tuple(spine(b - 1)), 1)
    steps, status, fin = mwalk(src, max_steps=300000)
    collect(steps)
    seq = expand_seq(steps, src)
    if k == 1:
        exp = ('B', (2205,) + F317, 3711 + b, 1, 2 * b + 1, (), 1)
    else:
        exp = ('B', F6, 2 * k + b - 2, 1, 2 * b + 1, (), 1)
    ok = (status == 'DONE' and fin == exp and END(k, b) in seq
          and px(k, b) in seq and fin[2] >= b)
    check(ok, 'TAIL2_BIG vM=%d beta=%d (k=%d): completes via px '
          'and END at A=%d >= beta' % (vM, b, k, exp[2]))

print('== Part 4: the fence at k >= 3714 ==')
steps, status, fin = mwalk(END(3714, 2), max_steps=300000)
seq = expand_seq(steps, END(3714, 2))
dip = ('C', F5, 3710, 7423, 2, ((2, 2), (1, 1)) + tuple(spine(1)), 1)
exp3714 = ('B', (4002, 1279, 745, 151, 77, 35, 20, 0), 7429, 1, 5,
           (), 1)
check(dip in seq and status == 'DONE' and fin == exp3714,
      'END k=3714: DIPDESC boundary hit; completes only via a '
      'further descent at %s' % (fmt(exp3714),))
steps, status, fin = mwalk(END(5000, 2), max_steps=300000)
exp5000 = ('B', (7427, 4001, 1279, 745, 151, 77, 35, 20, 0), 2574,
           1, 5, (), 1)
check(status == 'DONE' and fin == exp5000,
      'END k=5000: yet another cycle, final %s' % (fmt(exp5000),))

print('== Part 5: primitive-step audit ==')
bad = USED - PROVED_RULES
check(not bad, 'primitive rules used %s all in PROVED_RULES'
      % (sorted(USED),))

print()
if FAILS:
    print('FAILURES:', len(FAILS))
    sys.exit(1)
print('ALL PHASE 46 CHECKS PASS')
