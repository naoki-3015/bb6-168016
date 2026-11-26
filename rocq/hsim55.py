#!/usr/bin/env python3
"""Phase 55 machine tests for the TAIL2_END9 reduction.

Characterisation (from annotated traces of TOP8(j, beta),
j >= 1425926; the walk was replayed step by step through the
walker's own macro/prim functions and classified into lemma
applications -- the classifier was first validated by exact
reproduction of the Phase 54 classified chain
(chain54_646582_2.json, 184 steps, 0 mismatches) -- and the
CASCADE55 label sequence is identical at (j, beta) in
{(1425926, 2), (1425926, 3), (1425927, 2), (1425928, 2),
(1425929, 2), (2000000, 2), (4277778, 2)}):

  TOP8(j, b) = HB [135142; 27487; 14322; 1260; 147; 20; 0]
               864782
               1 1425923 ((2j, 2) :: (1, 1) :: (1, 2)^(b-1)),
  r9 = 2j - 2851850.

  1. FRONT (the TOP54 front shape, uniform in j): TUP,
     hGRIND_even 712959, TUP2_1, TDN, TUP
     -> GRIND9 = HC [864782; 135142; 27487; 14322; 1260;
        147; 20; 0] 1425922 3 2 ((2j-6, 2) :: tail(b)).
  2. DIPGRIND (1425922, r9), r9 >= 2:
     -> HC [864782; 135142; ...] 0 3 2 (spine 1425922 ++ W),
        W = ((r9, 2) :: (1, 1) :: (1, 2)^(b-1)).
  3. CASCADE55: a FIXED parse (only 17 lemma steps from the
     spine to TOP9; all frames/counters constant; W rides
     untouched at the bottom).  Far shorter than CASCADE54
     (176 steps): the frame shrinks from seven blocks to six.
     Steps: PX2A, PUSH, TDN, TUP, DIPGRIND (135140, 594496),
     PX2A, hGRIND 13741, POP, pop12 135142, TUP,
     hGRIND_even 148884, TUP2_1, TDN, TUP,
     CLEANG_even 297244, TRANS2_1, pop12 1425924.
     -> TOP9 = HB [297773; 149464; 1260; 147; 20; 0]
        2020419 1 2851851 W.
     (CASCADE55 is stated for an ARBITRARY tail w in
     Grind23.v; Part 1b below probes that generality with a
     junk tail.)
  4. TOP9 closings by r9' = 2 * j9, j9 = j - 1425925:
     r9' = 2:        TRANS2_1 + POPFIN, A = 2851851 + b,
                    frame [2020420; 297773; 149464; ...].
     r9' = 4:        TUP + hGRIND_even 1425923 + TRANS2_2
                    + POPFIN, A = b + 2,
                    frame [2851851; 2020419; 297773; ...].
     r9' = 6:        TUP + hGRIND_even 1425923 + TUP2_1 + TDN
                    + TRANS2_1 + POPFIN, A = b + 4,
                    frame as r9' = 4.
     8 <= r9' <= 5703706 (band 9): TUP + hGRIND_even 1425923
                    + TUP2_1 + TDN + TUP -> GRIND10
                    = HC [2020419; 297773; ...] 2851850 3 2
                    ((r9'-6, 2) :: tail(b))  -- TUP2_1 moves
                    the shuttle 2851851 into the counter
                    slot, so the band counter is 2851850;
                    CLEANG_even ((r9'-8)/2) (floor
                    (r9'-8)/2 + 1 <= 2851850, exactly
                    r9' <= 5703706); TRANS2_1 + POPFIN,
                    A = r9' + b - 2, frame as r9' = 4.
     r9' >= 5703708: GRIND10's pair (r9'-6, 2) exceeds the
                    CLEANG_even floor; DIPGRIND (2851850,
                    r9' - 5703706) landing occurs (asserted
                    in Part 3).  This is the residual core
                    TAIL2_END10 (at TOP9, r9' = 2*j9,
                    j9 >= 2851854).

Band boundary: r9' <= 5703706  <=>  j <= 4277778 (TOP8 params)
             <=>  j9 <= 2851853 (TOP9 params).
"""
import sys
sys.path.insert(0, '/home/hatch/workspace/busy-beaver/rocq')
from hsim45 import mwalk, fmt, MACROS
from hsim41 import step_all
from hsim42 import PROVED_RULES
from hsim50 import swalk, SP


def TOP8(j, b):
    return ('B', TOP8F, 864782, 1, 1425923,
            ((2 * j, 2), (1, 1)) + tuple(SP(b - 1)), 1)


def W(r9, b):
    return ((r9, 2), (1, 1)) + tuple(SP(b - 1))


TOP8F = (135142, 27487, 14322, 1260, 147, 20, 0)
TOP9F = (297773, 149464, 1260, 147, 20, 0)
F9 = (864782,) + TOP8F
F10 = (2020419,) + TOP9F

# CASCADE55 waypoint table (targets only), generated from the
# classified chain: pair lists are run-length items ('R', n) /
# ('P', a, b), with the final item 'W' standing for the arbitrary
# tail w (here W(r9, b)).
CASCADE55_WPS = [
    ('C', (27487, 14322, 1260, 147, 20, 0), 135141, 864780, 2, (('P', 1, 1), ('R', 1425924), 'W'), 1),  # P PX2A
    ('C', (27487, 14322, 1260, 147, 20, 0), 135140, 1, 2, (('P', 864778, 2), ('P', 1, 1), ('R', 1425924), 'W'), 1),  # P PUSH
    ('B', (27487, 14322, 1260, 147, 20, 0), 135140, 1, 4, (('P', 864778, 2), ('P', 1, 1), ('R', 1425924), 'W'), 1),  # P TDN
    ('C', (27487, 14322, 1260, 147, 20, 0), 135140, 3, 2, (('P', 864776, 2), ('P', 1, 1), ('R', 1425924), 'W'), 1),  # sTUP
    ('C', (27487, 14322, 1260, 147, 20, 0), 0, 3, 2, (('R', 135140), ('P', 594496, 2), ('P', 1, 1), ('R', 1425924), 'W'), 1),  # DIPGRIND 135140 594496
    ('C', (1260, 147, 20, 0), 14321, 27485, 2, (('P', 1, 1), ('R', 135142), ('P', 594496, 2), ('P', 1, 1), ('R', 1425924), 'W'), 1),  # P PX2A
    ('B', (1260, 147, 20, 0), 14321, 1, 27488, (('P', 1, 1), ('R', 135142), ('P', 594496, 2), ('P', 1, 1), ('R', 1425924), 'W'), 1),  # hGRIND 13741
    ('B', (1260, 147, 20, 0), 14322, 1, 27489, (('R', 135142), ('P', 594496, 2), ('P', 1, 1), ('R', 1425924), 'W'), 1),  # P POP
    ('B', (1260, 147, 20, 0), 149464, 1, 297773, (('P', 594496, 2), ('P', 1, 1), ('R', 1425924), 'W'), 1),  # M pop12 (135142,)
    ('C', (1260, 147, 20, 0), 149464, 297772, 2, (('P', 594494, 2), ('P', 1, 1), ('R', 1425924), 'W'), 1),  # sTUP
    ('B', (1260, 147, 20, 0), 149463, 1, 297772, (('P', 2, 2), ('P', 594494, 2), ('P', 1, 1), ('R', 1425924), 'W'), 1),  # hGRIND_even 148884
    ('C', (149464, 1260, 147, 20, 0), 297772, 1, 2, (('P', 594492, 2), ('P', 1, 1), ('R', 1425924), 'W'), 1),  # P TUP2_1
    ('B', (149464, 1260, 147, 20, 0), 297772, 1, 4, (('P', 594492, 2), ('P', 1, 1), ('R', 1425924), 'W'), 1),  # P TDN
    ('C', (149464, 1260, 147, 20, 0), 297772, 3, 2, (('P', 594490, 2), ('P', 1, 1), ('R', 1425924), 'W'), 1),  # sTUP
    ('B', (149464, 1260, 147, 20, 0), 297772, 1, 594494, (('P', 2, 2), ('P', 1, 1), ('R', 1425924), 'W'), 1),  # CLEANG_even 297244
    ('B', (297773, 149464, 1260, 147, 20, 0), 594495, 1, 3, (('R', 1425924), 'W'), 1),  # P TRANS2_1
    ('B', (297773, 149464, 1260, 147, 20, 0), 2020419, 1, 2851851, ('W',), 1),  # M pop12 (1425924,)
]


def expand(items, w):
    out = []
    for it in items:
        if it == 'W':
            out.extend(w)
        elif it[0] == 'R':
            out.extend(SP(it[1]))
        else:
            out.append((it[1], it[2]))
    return tuple(out)


def waypoints(j, b):
    """The full asserted waypoint chain TOP8 -> ... -> TOP9
    (plus the r9 = 2 / r9 = 4 closing waypoints)."""
    r9 = 2 * j - 2851850
    w = W(r9, b)
    tail = ((1, 1),) + tuple(SP(b - 1))
    pts = []
    pts.append(('C', TOP8F, 864782, 1425922, 2, ((2 * j - 2, 2),) + tail, 1))
    pts.append(('B', TOP8F, 864781, 1, 1425922,
                ((2, 2), (2 * j - 2, 2)) + tail, 1))
    pts.append(('C', F9, 1425922, 1, 2, ((2 * j - 4, 2),) + tail, 1))
    pts.append(('B', F9, 1425922, 1, 4, ((2 * j - 4, 2),) + tail, 1))
    pts.append(('C', F9, 1425922, 3, 2, ((2 * j - 6, 2),) + tail, 1))
    pts.append(('C', F9, 0, 3, 2, tuple(SP(1425922)) + w, 1))
    for (st, pb, A, g0, s, items, G) in CASCADE55_WPS:
        pts.append((st, pb, A, g0, s, expand(items, w), G))
    if r9 == 2:
        pts.append(('B', (2020420,) + TOP9F, 2851852, 1, 3,
                    tuple(SP(b - 1)), 1))
    if r9 == 4:
        pts.append(('C', TOP9F, 2020419, 2851850, 2,
                    ((2, 2), (1, 1)) + tuple(SP(b - 1)), 1))
        pts.append(('B', TOP9F, 2020418, 1, 2851850,
                    ((2, 2), (2, 2), (1, 1)) + tuple(SP(b - 1)), 1))
        pts.append(('B', (2851851, 2020419) + TOP9F, 3, 1, 3,
                    tuple(SP(b - 1)), 1))
    return pts


def norm(cfg):
    st, pb, A, g0, s, pairs, G = cfg
    return (st, tuple(pb), A, g0, s, tuple(pairs), G)


# awalk (retained from hsim53 for reference; check_chain now
# walks at swalk granularity -- see there).  Macro-set note:
# an earlier Phase 54 draft dropped try_hgrind because its
# span can strictly contain classifier steps of other kinds
# (at cascade steps 137-139 of the (646582, 2) walk it spans
# the classifier's PUSH / TDN / pop12 (2,) steps, whose
# targets then fall inside the span).  That broke the walk:
# the DIPGRIND rounds are hGRIND-shaped, and without the
# macro each round decomposes into primitives that
# accumulate residue pairs -- 30,000,000 steps covered only
# 23 of the 646578 rounds of the front DIPGRIND span.  So
# try_hgrind stays in the macro set, and check_chain
# tolerates a segment jump over intermediate waypoints by
# verifying each skipped waypoint afterwards with a
# lemma-level replay from the jump's anchor config (the
# lemma parse from the anchor passes through them before
# the landing).


def awalk(src, max_steps=30000000):
    """Streaming every-step walker (hsim53's awalk, cap raised):
    yields the target config of EVERY macro/prim step in order,
    then a final ('STATUS', status, cfg, used_rules) tuple."""
    cfg = src
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
            cfg = hit[2]
            total += 1
            yield cfg
            continue
        opts = step_all(cfg)
        assert len(opts) == 1, ('walk stuck/branching', cfg)
        used.add(opts[0][0])
        cfg = opts[0][1]
        total += 1
        yield cfg
    yield ('STATUS', 'CAP', cfg, used)


# ------------------------------------------------------------------
# Lemma-level stepper (the cascade classifier of
# phase54-work/classify.py, inlined so this file stays
# self-contained): pattern-matches the Coq lemma vocabulary
# at a config and returns (label, next config) in O(1)-ish.
# Used to verify waypoints that a swalk segment jumps over:
# the lemma steps from the jump's anchor pass through the
# skipped waypoints in order and end at the jump's landing,
# and every pattern is one of the proved hsteps lemmas.
# (SP is hsim50's, identical to the classifier's own.)


def lemmastep(cfg):
    st, pb, A, g0, s, pairs, G = cfg
    pb = tuple(pb)
    pairs = tuple(pairs)
    if st == 'B':
        assert g0 == 1, cfg
        if not pairs:
            return None
        (g, r), rest = pairs[0], pairs[1:]
        if (g, r) == (1, 2) and s >= 2:
            n = 0
            while n < len(pairs) and pairs[n] == (1, 2):
                n += 1
            return ('M pop12 (%d,)' % n,
                    ('B', pb, A + n, 1, s + 2 * n, pairs[n:], G))
        if (g, r) == (1, 1) and s >= 2:
            return ('P POP', ('B', pb, A + 1, 1, s + 1, rest, G))
        if g == 1 and r >= 3 and s >= 2:
            return ('P POP_r%d' % r, ('B', pb, A + 1, 1, s + r, rest, G))
        if g == 2 and r == 2 and rest:
            (w2, r2), rest2 = rest[0], rest[1:]
            if w2 == 1 and r2 >= 1:
                return ('P TRANS2_1',
                        ('B', (A + 1,) + pb, s + 1, 1, r + r2, rest2, G))
            if w2 >= 3 and r2 == 2:
                return ('P TUP2_1',
                        ('C', (A + 1,) + pb, s, r - 1, 2,
                         ((w2 - 2, r2),) + rest2, G))
            if w2 == 2 and rest2 and rest2[0][0] == 1 and rest2[0][1] >= 1:
                r3 = rest2[0][1]
                return ('P TRANS2_2',
                        ('B', (s + 1, A + 1) + pb, r + 1, 1, r2 + r3,
                         rest2[1:], G))
        if g == 2 and r == 1 and rest and rest[0][0] >= 5 and rest[0][1] >= 2:
            w2, r2 = rest[0]
            return ('P TUP2def',
                    ('C', (A + 1,) + pb, s - 1, 3, 2,
                     ((w2 - 4, r2),) + rest[1:], G))
        if g >= 3 and s >= 2:
            return ('sTUP', ('C', pb, A, s - 1, 2, ((g - 2, r),) + rest, G))
        return ('UNMATCHED-B', None)
    # C section
    assert s == 2, cfg
    if g0 == 1:
        return ('P TDN', ('B', pb, A, 1, 4, pairs, G))
    if g0 == 3 and A == 0:
        if pb == ():
            return ('P PUSHX', ('B', (), 1, 1, 7, pairs, G))
        if len(pb) == 1:
            b = pb[0]
            if b == 0:
                return ('P PX2B0', ('B', (), 0, 1, 5, ((1, 2),) + pairs, G))
            if b >= 5:
                return ('P PX2Bgen',
                        ('B', (0,), 3, 1, 2,
                         ((b - 4, 2), (1, 1), (1, 2), (1, 2)) + pairs, G))
            if b == 2:
                return ('P PX2B2', ('B', (), 1, 1, 8, ((1, 2),) + pairs, G))
            if b == 3:
                return ('P PX2B3',
                        ('B', (), 1, 1, 6, ((1, 2), (1, 2)) + pairs, G))
            if b == 4:
                return ('P PX2B4',
                        ('B', (0,), 4, 1, 3, ((1, 2), (1, 2)) + pairs, G))
            return ('UNMATCHED-PX2B1', None)
        if len(pb) == 2 and pb[1] == 0:
            b = pb[0]
            if b >= 5:
                return ('P PX2A0',
                        ('B', (0,), 3, 1, 2,
                         ((b - 4, 2), (1, 1), (1, 2), (1, 2)) + pairs, G))
            return ('UNMATCHED-PX2A0-small', None)
        if len(pb) >= 2 and pb[1] >= 1:
            b, p = pb[0], pb[1]
            if b >= 3:
                return ('P PX2A',
                        ('C', pb[2:], p - 1, b - 2, 2,
                         ((1, 1), (1, 2), (1, 2)) + pairs, G))
            if b == 2:
                return ('P PX2A2',
                        ('B', pb[2:], p - 1, 1, 5,
                         ((1, 2), (1, 2)) + pairs, G))
        return ('UNMATCHED-dispatch', None)
    if g0 == 3 and A >= 1:
        if pairs and pairs[0][1] == 2:
            g = pairs[0][0]
            rest = pairs[1:]
            if g == 2:
                # CLEANG_even 0 == hGRIND 0 (Phase 52 precedent)
                return ('hGRIND 0', ('B', pb, A, 1, 6, pairs, G))
            if g % 2 == 0:
                m = (g - 2) // 2
                if m + 1 <= A:
                    return ('CLEANG_even %d' % m,
                            ('B', pb, A, 1, 2 * m + 6, ((2, 2),) + rest, G))
                r = g - 2 * A
                return ('DIPGRIND %d %d' % (A, r),
                        ('C', pb, 0, 3, 2,
                         tuple(SP(A)) + ((r, 2),) + rest, G))
            m = (g - 3) // 2
            if m >= 0 and m + 2 <= A:
                return ('CLEANG_odd %d' % m,
                        ('B', pb, A, 1, 2 * m + 8, ((1, 2),) + rest, G))
            r = g - 2 * A
            if r >= 1:
                return ('DIPGRIND %d %d' % (A, r),
                        ('C', pb, 0, 3, 2,
                         tuple(SP(A)) + ((r, 2),) + rest, G))
        return ('P PUSH', ('C', pb, A - 1, 1, 2, ((g0 - 2, 2),) + pairs, G))
    if g0 >= 4 and A >= 1:
        if g0 % 2 == 0:
            t = (g0 - 4) // 2
            if 1 <= t <= A - 1:
                return ('hGRIND_even %d' % t,
                        ('B', pb, A - 1, 1, g0, ((2, 2),) + pairs, G))
            return ('P PUSH',
                    ('C', pb, A - 1, 1, 2, ((g0 - 2, 2),) + pairs, G))
        t = (g0 - 3) // 2
        if t + 1 <= A:
            return ('hGRIND %d' % t, ('B', pb, A, 1, 2 * t + 6, pairs, G))
        if g0 == 2 * A + 3:
            return ('DIPDESC %d' % A,
                    ('C', pb, 0, 3, 2, tuple(SP(A)) + pairs, G))
        return ('P PUSH', ('C', pb, A - 1, 1, 2, ((g0 - 2, 2),) + pairs, G))
    if g0 == 2:
        return ('UNMATCHED-C-g02', None)
    return ('UNMATCHED-C', None)




def _matches(rec, t):
    return rec[0] == t[0] and rec[2] == t[2] and rec[3] == t[3] \
        and rec[4] == t[4] and (rec == t or norm(rec) == t)


def check_chain(j, b, cap=30000000):
    pts = [norm(p) for p in waypoints(j, b)]
    pos = -1
    status = fin = None
    used = set()
    nrec = 0
    src = TOP8(j, b)
    anchor = norm(src)
    skips = []  # (anchor, [skipped waypoints], landing)
    # Walk at swalk granularity (prim-segment endpoints and
    # macro targets -- exactly the granularity the classifier
    # segmented the walk at, so every classifier waypoint is a
    # swalk record).  The every-prim awalk of hsim53 is too slow
    # at this phase's scale: each word step on a spine-carrying
    # config costs O(spine) ~ 646578, and the cascade spans
    # millions of word steps.
    for rec in swalk(src, max_steps=cap):
        if isinstance(rec, tuple) and rec and rec[0] == 'STATUS':
            status, fin, used = rec[1], rec[2], rec[3]
            break
        nrec += 1
        if pos + 1 < len(pts):
            if _matches(rec, pts[pos + 1]):
                pos += 1
                anchor = pts[pos]
            else:
                # a segment may jump over intermediate
                # waypoints: look a few waypoints ahead for
                # this record.  The skip's anchor is the last
                # MATCHED waypoint (a classifier step boundary,
                # where the lemma parse can start) -- not the
                # immediately preceding record, which may sit
                # inside a classifier step.
                for k in range(pos + 2, min(pos + 9, len(pts))):
                    if _matches(rec, pts[k]):
                        skips.append((anchor, pts[pos + 1:k],
                                      pts[k]))
                        pos = k
                        anchor = pts[pos]
                        break
    assert pos == len(pts) - 1, \
        'j=%d b=%d: waypoint %d missing: %s' \
        % (j, b, pos + 1, fmt(pts[pos + 1]))
    # Verify every skipped waypoint: replay lemma steps
    # (lemmastep) from the jump's anchor config -- the lemma
    # parse from the anchor passes through the skipped
    # waypoints in order and ends at the jump's landing.
    # (Neither an mwalk -- it segments identically to swalk
    # and would jump the same waypoints -- nor a prim-level
    # walk -- a DIPGRIND span's prim decomposition is
    # quadratic in the spine length -- can serve here.)
    for (anchor, skipped, landing) in skips:
        targets = skipped + [landing]
        ti = 0
        cfg = anchor
        steps = 0
        while ti < len(targets) and steps < 100000:
            hit = lemmastep(cfg)
            assert hit is not None and hit[1] is not None, \
                ('verify replay unmatched', cfg)
            cfg = hit[1]
            steps += 1
            if norm(cfg) == targets[ti]:
                ti += 1
        assert ti == len(targets), \
            'j=%d b=%d: skipped waypoint not verified: %s' \
            % (j, b, fmt(targets[ti]))
    return status, fin, pos, used


def main():
    fails = 0
    used = set()
    # Part 1: full waypoint chain TOP8 -> TOP9, several bands.
    for (j, b) in [(1425926, 2), (1425926, 3), (1425927, 2), (2000000, 2),
                   (4277778, 2)]:
        try:
            status, fin, pos, u = check_chain(j, b)
            used.update(u)
            print('PASS chain j=%d b=%d: %d waypoints in order, '
                  'walk %s' % (j, b, len(waypoints(j, b)), status),
                  flush=True)
        except AssertionError as e:
            fails += 1
            print('FAIL', e, flush=True)
    # Part 1b: CASCADE55 is tail-general -- junk tail probe.
    w0 = ((7, 2), (1, 1), (3, 2), (1, 2))
    src = ('C', F9, 0, 3, 2, tuple(SP(1425922)) + w0, 1)
    top9 = norm(('B', TOP9F, 2020419, 1, 2851851, w0, 1))
    ok = False
    for rec in swalk(src, max_steps=6000000):
        if isinstance(rec, tuple) and rec and rec[0] == 'STATUS':
            break
        if norm(rec) == top9:
            ok = True
            break
    print(('PASS' if ok else 'FAIL'),
          'tail-generality: TOP9 shape reached with junk tail',
          flush=True)
    fails += 0 if ok else 1
    # Part 2: TOP9-closing finals.
    F10p = (2020420,) + TOP9F
    F11p = (2851851, 2020419) + TOP9F
    finals = {
        (1425926, 2): (F10p, 2851853),
        (1425926, 3): (F10p, 2851854),
        (1425927, 2): (F11p, 4),
        (1425927, 3): (F11p, 5),
        (1425928, 2): (F11p, 6),
        (1425929, 2): (F11p, 8),
        (1425929, 3): (F11p, 9),
        (2000000, 3): (F11p, 1148151),
        (4277778, 2): (F11p, 5703706),
    }
    for (j, b), (fr, A) in sorted(finals.items()):
        status = fin = None
        for rec in swalk(TOP8(j, b), max_steps=30000000):
            if isinstance(rec, tuple) and rec and rec[0] == 'STATUS':
                status, fin = rec[1], rec[2]
                break
        want = ('B', tuple(fr), A, 1, 2 * b + 1, (), 1)
        ok = status == 'DONE' and norm(fin) == want
        print(('PASS' if ok else 'FAIL'),
              'final j=%d b=%d: %s (want A=%d frame %s)'
              % (j, b, fmt(fin), A, list(fr)), flush=True)
        fails += 0 if ok else 1
    # Part 3: the tenth fence -- r9' >= 5703708 takes DIPGRIND
    # at 2851850.  (j is TOP8's parameter; j9 = j - 1425925.)
    for (j, b) in [(4277779, 2), (4277780, 2), (4500000, 2)]:
        j9 = j - 1425925
        g10 = norm(('C', F10, 2851850, 3, 2,
                    ((2 * j9 - 6, 2), (1, 1)) + tuple(SP(b - 1)), 1))
        dip10 = norm(('C', F10, 0, 3, 2,
                      tuple(SP(2851850))
                      + ((2 * j9 - 5703706, 2), (1, 1))
                      + tuple(SP(b - 1)), 1))
        seen_g10 = seen_dip10 = False
        for rec in swalk(TOP8(j, b), max_steps=30000000):
            if isinstance(rec, tuple) and rec and rec[0] == 'STATUS':
                break
            n = norm(rec)
            if n == g10:
                seen_g10 = True
            elif seen_g10 and n == dip10:
                seen_dip10 = True
                break
        ok = seen_g10 and seen_dip10
        print(('PASS' if ok else 'FAIL'),
              'fence j=%d: GRIND10 then tenth DIPGRIND landing '
              'occur (r9p=%d)' % (j, 2 * j9), flush=True)
        fails += 0 if ok else 1
    # Part 4: primitive-step audit.
    bad = used - PROVED_RULES
    print(('PASS' if not bad else 'FAIL'),
          'primitive rules used %s all in PROVED_RULES'
          % (sorted(used),), flush=True)
    fails += 0 if not bad else 1
    print()
    print('ALL PHASE 55 CHECKS PASS' if fails == 0
          else '%d FAILURES' % fails)
    return fails


if __name__ == '__main__':
    sys.exit(1 if main() else 0)
