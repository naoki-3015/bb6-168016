#!/usr/bin/env python3
"""hsim45.py — Phase 45 machine checks: the stage-4 TAIL at the era
slice (q, v3, a) = (28, 34, 822) of Grind12's CASCADE_STAGE4_TAIL.

Phase 44 reduced CASCADE_STAGE4_BIG to the tail totality TAIL
(Grind12.CASCAPE_STAGE4_TAIL, over all q >= 5, v3, vM, a, beta).
Phase 45 characterises the tail at the ERA SLICE — the only
instantiation the proof of CASCADE_STAGE4_BIG actually uses
(Grind12.CASCADE_STAGE4_BIG_of instantiates the tail at
(28, 34, M - 1441, 822, beta)) — and finds a three-layer parse:

  layer 0 (q = 28): the spine + the (48, 2) residue are consumed by
    pop12 4, TUP, PUSH, GG_boundary (3, 3) [PUSHX], pop12 3,
    TUP2_1, GG_boundary (13, 20) [PX2Bgen], pops, TUP,
    hGRIND_even 15, TUP2_1, GG_clean 4, TRANS2_1, landing at
      HB [35; 20; 0] 15 1 3 (TAIL1s)        — L0 below.
  layer 1 (v3 = 34): pop12 120, TUP, hGRIND_even 119, TUP2_1,
    GG_clean 31, TRANS2_1, landing at
      HB [243; 135; 35; 20; 0] 69 1 3 (TAIL2s)   — L1 below.
  layer 2 (a = 822): pop12 824 reaches the residue state
      HB [243; 135; 35; 20; 0] 893 1 1651
        ((2 vM + 2, 2) :: (1, 1) :: spine (beta - 1))   — CE below.
    For vM <= 1652 the residue closes CLEANLY (TUP, hGRIND_even 823,
    then TRANS2_2 / TDN+TRANS2_1 / GG_clean (vM - 3) + TRANS2_1,
    then the POP chain), with final counter
      A = beta + 1651 (vM = 0), beta + 2 (vM = 1), beta + 4 (vM = 2),
      A = 2 vM + beta (3 <= vM <= 1652), all >= beta.
    For vM >= 1653 the pair (2 vM - 2, 2) at counter 1650 is in the
    BOUNDARY regime: GG_boundary (1650, vM - 3) fires and lands at
    HC [893; 243; 135; 35; 20; 0] 0 3 2
      (spine 1650 ++ ((2 vM - 3304, 2) :: (1, 1) :: spine (beta-1)))
    and PX2A pops the frame to [135; 35; 20; 0] with g0 = 891 —
    the descent that the residual core TAIL2_BIG (Grind13) names.

Part 1: primitive walks of the tail at small parameters (regression
  with the Phase 44 T4 points, walked from the TAIL source itself).
Part 2: macro walks (proved lemmas as macros, primitive fallback)
  at the era slice for vM in {0, 1, 2, 3, 5, 100, 1652} and
  beta in {2, 3}: the L0 / L1 / CE boundary configs occur in order,
  the walk completes at the era landing, and the final counter
  matches the closed forms above exactly.
Part 3: boundary regime vM >= 1653 (beta = 2): the macro walk
  reaches the GG_boundary landing and its unique next step is
  PX2A to the asserted landing; the macro walk then COMPLETES at
  the era landing for vM in {1653, 2000, 5366} (finals asserted
  verbatim) — but its length grows with vM (4473 / 5165 / 14529
  macro steps): the descent has no uniform cycle in the current
  lemma vocabulary, which is exactly what the residual core
  TAIL2_BIG (Grind13) names.  A primitive walk from the PX2A
  landing is still walking at a 1,000,000-rule cap.
Part 4: audit — every primitive step used belongs to PROVED_RULES.
"""
import sys
sys.path.insert(0, '.')
from hsim41 import step_all
from hsim42 import PROVED_RULES
from hsim43 import walk_hist

FAILS = []


def check(cond, msg):
    if cond:
        print('  PASS', msg)
    else:
        print('  FAIL', msg)
        FAILS.append(msg)


def spine(n):
    return [(1, 2)] * n


def TAILs(q, v3, vM, a, b):
    return (spine(4) + [(2 * q - 8, 2), (1, 1), (1, 2), (1, 2)]
            + spine(4 * q + 6)
            + [(2 * v3 + 2, 2), (1, 1), (1, 2), (1, 2)]
            + spine(a)
            + [(2 * vM + 2, 2), (1, 1)] + spine(b - 1))


def TAIL1s(v3, vM, a, b):
    return ([(1, 2), (1, 2)] + spine(4 * 28 + 6)
            + [(2 * v3 + 2, 2), (1, 1), (1, 2), (1, 2)]
            + spine(a)
            + [(2 * vM + 2, 2), (1, 1)] + spine(b - 1))


def TAIL2s(vM, b):
    return spine(824) + [(2 * vM + 2, 2), (1, 1)] + spine(b - 1)


FSTAR = (243, 135, 35, 20, 0)


def L0(v3, vM, a, b):
    return ('B', (35, 20, 0), 15, 1, 3, tuple(TAIL1s(v3, vM, a, b)), 1)


def L1(vM, b):
    return ('B', FSTAR, 69, 1, 3, tuple(TAIL2s(vM, b)), 1)


def CE(vM, b):
    return ('B', FSTAR, 893, 1, 1651,
            ((2 * vM + 2, 2), (1, 1)) + tuple(spine(b - 1)), 1)


# ----------------------------------------------------------------------
# macro walker: proved lemmas as macros + primitive fallback.
# Configs: (st, pb tuple, A, g0, s, pairs tuple, G).
# ----------------------------------------------------------------------

def try_pop12(cfg):
    st, pb, A, g0, s, pairs, G = cfg
    if st != 'B' or s < 2:
        return None
    n = 0
    while n < len(pairs) and pairs[n] == (1, 2):
        n += 1
    if n == 0:
        return None
    return ('pop12', (n,), ('B', pb, A + n, g0, s + 2 * n, pairs[n:], G))


def try_gg_clean(cfg):
    st, pb, A, g0, s, pairs, G = cfg
    if st != 'C' or g0 != 2 or A < 1 or not pairs:
        return None
    g, r = pairs[0]
    if r != 2 or g < 4 or g % 2 != 0:
        return None
    m = (g - 4) // 2
    if m + 1 > A:
        return None
    return ('GG_clean', (m,),
            ('B', pb, A, 1, 2 * m + 6, ((2, 2),) + pairs[1:], G))


def try_gg_boundary(cfg):
    st, pb, A, g0, s, pairs, G = cfg
    if st != 'C' or g0 != 2 or A < 1 or not pairs:
        return None
    g, r = pairs[0]
    if r != 2 or g < 4 or g % 2 != 0:
        return None
    m = (g - 4) // 2
    if not (A <= m):
        return None
    land = tuple(spine(A)) + ((2 * (m - A) + 2, 2),) + pairs[1:]
    return ('GG_boundary', (A, m), ('C', pb, 0, 3, 2, land, G))


def try_gg_odd(cfg):
    st, pb, A, g0, s, pairs, G = cfg
    if st != 'C' or g0 != 2 or A < 1 or not pairs:
        return None
    g, r = pairs[0]
    if r != 2 or g < 3 or g % 2 != 1:
        return None
    m = (g - 3) // 2
    if m + 1 > A:
        return None
    return ('GG_odd', (m,),
            ('B', pb, A, 1, 2 * m + 6, ((1, 2),) + pairs[1:], G))


def try_hgrind_even(cfg):
    st, pb, A, g0, s, pairs, G = cfg
    if st != 'C' or A < 1 or g0 < 4 or g0 % 2 != 0:
        return None
    t = (g0 - 4) // 2
    if t < 1 or t > A - 1:
        return None
    return ('hGRIND_even', (t,),
            ('B', pb, A - 1, 1, g0, ((2, 2),) + pairs, G))


def try_hgrind(cfg):
    st, pb, A, g0, s, pairs, G = cfg
    if st != 'C' or g0 < 3 or g0 % 2 != 1:
        return None
    t = (g0 - 3) // 2
    if t + 1 > A:
        return None
    return ('hGRIND', (t,),
            ('B', pb, A, 1, 2 * t + 6, pairs, G))


def try_dipdesc(cfg):
    st, pb, A, g0, s, pairs, G = cfg
    if st != 'C' or g0 != 2 * A + 3 or A < 1:
        return None
    return ('DIPDESC', (A,),
            ('C', pb, 0, 3, 2, tuple(spine(A)) + pairs, G))


MACROS = [try_pop12, try_gg_clean, try_gg_boundary, try_gg_odd,
          try_hgrind_even, try_hgrind, try_dipdesc]


def mwalk(src, max_steps=100000):
    steps = []
    cfg = src
    prim = 0
    prim_rules = []

    def flush():
        nonlocal prim, prim_rules
        if prim:
            steps.append(('prim', prim, tuple(prim_rules), cfg))
            prim = 0
            prim_rules = []

    total = 0
    while total < max_steps:
        if cfg[0] == 'B' and not cfg[5]:
            flush()
            return steps, 'DONE', cfg
        hit = None
        for mac in MACROS:
            hit = mac(cfg)
            if hit:
                break
        if hit:
            flush()
            name, params, nxt = hit
            steps.append(('macro', name, params, cfg, nxt))
            cfg = nxt
            total += 1
            continue
        opts = step_all(cfg)
        assert len(opts) == 1, ('walk stuck/branching', cfg)
        prim += 1
        prim_rules.append(opts[0][0])
        cfg = opts[0][1]
        total += 1
    flush()
    return steps, 'CAP', cfg


def config_seq(steps, src):
    seq = [src]
    for st in steps:
        seq.append(st[-1])
    return seq


def fmt(cfg):
    st, pb, A, g0, s, pairs, G = cfg
    out = []
    i = 0
    while i < len(pairs):
        if pairs[i] == (1, 2):
            j = i
            while j < len(pairs) and pairs[j] == (1, 2):
                j += 1
            out.append('(1,2)^%d' % (j - i))
            i = j
        else:
            out.append(str(pairs[i]))
            i += 1
    return '%s %s A=%d g0=%d s=%d [%s] G=%d' % (
        'HB' if st == 'B' else 'HC', list(pb), A, g0, s, ' '.join(out), G)


# ----------------------------------------------------------------------
print('== Part 1: primitive walks from the TAIL source (small) ==')
for (q, v3, vM, a, b) in [(5, 0, 0, 2, 2), (6, 0, 0, 2, 2),
                          (5, 0, 0, 4, 3), (7, 0, 0, 2, 2)]:
    src = ('B', (), 0, 1, 5, tuple(TAILs(q, v3, vM, a, b)), 1)
    hist, rules, status = walk_hist(src, 300000)
    fin = hist[-1]
    ok = (status == 'DONE' and fin[0] == 'B' and fin[5] == ()
          and fin[4] == 2 * b + 1 and fin[2] >= b)
    check(ok, 'TAIL(%d,%d,%d,%d,%d) lands: %s'
          % (q, v3, vM, a, b, fmt(fin)))

print('== Part 2: era slice, clean range vM <= 1652 ==')
EXP_FRAME = {0: (894, 243, 135, 35, 20, 0)}
for vM in [0, 1, 2, 3, 5, 100, 1652]:
    for b in [2, 3]:
        src = ('B', (), 0, 1, 5, tuple(TAILs(28, 34, vM, 822, b)), 1)
        steps, status, fin = mwalk(src)
        seq = config_seq(steps, src)
        i0 = seq.index(L0(34, vM, 822, b)) if L0(34, vM, 822, b) in seq else -1
        i1 = seq.index(L1(vM, b)) if L1(vM, b) in seq else -1
        i2 = seq.index(CE(vM, b)) if CE(vM, b) in seq else -1
        if vM == 0:
            expA, expF = b + 1651, (894, 243, 135, 35, 20, 0)
        elif vM == 1:
            expA, expF = b + 2, (1651, 893, 243, 135, 35, 20, 0)
        elif vM == 2:
            expA, expF = b + 4, (1651, 893, 243, 135, 35, 20, 0)
        else:
            expA, expF = 2 * vM + b, (1651, 893, 243, 135, 35, 20, 0)
        ok = (status == 'DONE' and 0 <= i0 < i1 < i2
              and fin == ('B', expF, expA, 1, 2 * b + 1, (), 1))
        check(ok, 'era TAIL vM=%d beta=%d: L0@%d L1@%d CE@%d, final A=%d'
              % (vM, b, i0, i1, i2, expA))

print('== Part 3: boundary regime vM >= 1653 ==')
EXP_BIG = {1653: ((2205, 317, 40, 14, 5), 3713),
           2000: ((3711, 2204, 317, 40, 14, 5), 696),
           5366: ((4002, 1279, 745, 151, 77, 35, 20, 0), 7429)}
for vM in [1653, 2000, 5366]:
    b = 2
    src = ('B', (), 0, 1, 5, tuple(TAILs(28, 34, vM, 822, b)), 1)
    steps, status, fin = mwalk(src, max_steps=100000)
    seq = config_seq(steps, src)
    gb = ('C', (893, 243, 135, 35, 20, 0), 0, 3, 2,
          tuple(spine(1650)) + ((2 * vM - 3304, 2), (1, 1))
          + tuple(spine(b - 1)), 1)
    px = ('C', (135, 35, 20, 0), 242, 891, 2,
          ((1, 1), (1, 2), (1, 2)) + tuple(spine(1650))
          + ((2 * vM - 3304, 2), (1, 1)) + tuple(spine(b - 1)), 1)
    ig = seq.index(gb) if gb in seq else -1
    nxt = step_all(gb) if ig >= 0 else []
    px_ok = len(nxt) == 1 and nxt[0][0] == 'PX2A' and nxt[0][1] == px
    expF, expA = EXP_BIG[vM]
    fin_ok = (status == 'DONE'
              and fin == ('B', expF, expA, 1, 2 * b + 1, (), 1))
    check(ig >= 0 and px_ok and fin_ok,
          'era TAIL vM=%d: GG_boundary landing @%d, PX2A next, macro '
          'walk completes (%d steps) at A=%d' % (vM, ig, len(steps), expA))
# primitive walk from the vM = 1653 PX2A landing: still walking.
px1653 = ('C', (135, 35, 20, 0), 242, 891, 2,
          ((1, 1), (1, 2), (1, 2)) + tuple(spine(1650))
          + ((2 * 1653 - 3304, 2), (1, 1)) + tuple(spine(1)), 1)
cur = px1653
status = 'CAP'
for _ in range(1000000):
    opts = step_all(cur)
    if not opts:
        status = 'DONE'
        break
    assert len(opts) == 1
    cur = opts[0][1]
check(status == 'CAP',
      'primitive walk from the vM=1653 PX2A landing still walking '
      'at 1,000,000 rules')

print('== Part 4: primitive-step audit ==')
used = set()
for vM in [0, 3]:
    src = ('B', (), 0, 1, 5, tuple(TAILs(28, 34, vM, 822, 2)), 1)
    steps, status, fin = mwalk(src)
    for st in steps:
        if st[0] == 'prim':
            used.update(st[2])
bad = used - PROVED_RULES
check(not bad, 'primitive rules used %s all in PROVED_RULES'
      % (sorted(used),))

print()
if FAILS:
    print('FAILURES:', len(FAILS))
    sys.exit(1)
print('ALL PHASE 45 CHECKS PASS')
