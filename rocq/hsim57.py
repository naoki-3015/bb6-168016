#!/usr/bin/env python3
"""Phase 57 machine tests for the TAIL2_END11 reduction.

Characterisation (from annotated traces of TOP10(j, beta),
j >= 5937478; the walk was replayed step by step through the
walker's own macro/prim functions and classified into lemma
applications -- the classifier was first validated by exact
reproduction of the Phase 56 classified chain
(chain56_2851854_2.jsonl, 807 steps, 0 mismatches) -- and the
CASCADE57 label sequence and abstracted targets are identical
at (j, beta) in {(5937478, 2), (5937478, 3)}):

  TOP10(j, b) = HB [652285; 206767; 138671; 25145; 13306;
               4643; 2871; 335; 235; 42; 19] 4042956
               1 5937475 ((2j, 2) :: (1, 1) :: (1, 2)^(b-1)),
  r11 = 2j - 11874954 (the DIPGRIND residue at GRIND11).

  1. FRONT (the TOP56 front shape, uniform in j): TUP,
     hGRIND_even 2968735, TUP2_1, TDN, TUP
     -> GRIND11 = HC [4042956; 652285; 206767; 138671; 25145;
        13306; 4643; 2871; 335; 235; 42; 19] 5937474 3 2
        ((2j-6, 2) :: tail(b)).
  2. DIPGRIND (5937474, r11), r11 >= 2:
     -> HC [4042956; 652285; ...] 0 3 2 (spine 5937474 ++ W),
        W = ((r11, 2) :: (1, 1) :: (1, 2)^(b-1)).
  3. CASCADE57: a FIXED parse of only 17 lemma steps from
     the spine to TOP11 (every frame and counter a literal;
     W rides untouched at the bottom).  After CASCADE56's
     799 steps, the eleventh descent is again SHORT (the
     CASCADE55 pattern): 2 PX2A, 1 PUSH, 2 TDN, 3 TUP, a
     SINGLE DIPGRIND level (652283, 2738384), 1 hGRIND
     103381, 1 POP, pop12 652285, hGRIND_even 755667,
     TUP2_1, CLEANG_even 1369188, TRANS2_1, pop12 5937476.
     The frame SHRINKS from eleven blocks to ten:
     -> TOP11 = HB [1511339; 790956; 25145; 13306; 4643;
        2871; 335; 235; 42; 19] 8675859 1 11874955 W.
     (CASCADE57 is stated for an ARBITRARY tail w in
     Grind25.v; Part 1b below probes that generality with a
     junk tail.)
  4. TOP11 closings by r11' = 2 * j11, j11 = j - 5937477:
     r11' = 2:       TRANS2_1 + POPFIN, A = 11874955 + b,
                    frame [8675860; 1511339; 790956; ...].
     r11' = 4:       TUP + hGRIND_even 5937475 + TRANS2_2
                    + POPFIN, A = b + 2,
                    frame [11874955; 8675859; 1511339; ...].
     r11' = 6:       TUP + hGRIND_even 5937475 + TUP2_1 + TDN
                    + TRANS2_1 + POPFIN, A = b + 4,
                    frame as r11' = 4.
     8 <= r11' <= 23749914 (band 11): TUP + hGRIND_even
                    5937475 + TUP2_1 + TDN + TUP -> GRIND12
                    = HC [8675859; 1511339; ...] 11874954 3 2
                    ((r11'-6, 2) :: tail(b))  -- TUP2_1 moves
                    the shuttle 11874955 into the counter
                    slot, so the band counter is 11874954;
                    CLEANG_even ((r11'-8)/2) (floor
                    (r11'-8)/2 + 1 <= 11874954, exactly
                    r11' <= 23749914); TRANS2_1 + POPFIN,
                    A = r11' + b - 2, frame as r11' = 4.
     r11' >= 23749916: GRIND12's pair (r11'-6, 2) exceeds
                    the CLEANG_even floor; DIPGRIND
                    (11874954, r11' - 23749914) landing occurs
                    (asserted in Part 3).  This is the
                    residual core TAIL2_END12 (at TOP11,
                    r11' = 2*j11, j11 >= 11874958).

Band boundary: r11' <= 23749914  <=>  j <= 17812434 (TOP10
             params)  <=>  j11 <= 11874957 (TOP11 params).
"""
import sys
sys.path.insert(0, '/home/hatch/workspace/busy-beaver/rocq')
from hsim45 import mwalk, fmt, MACROS
from hsim41 import step_all
from hsim42 import PROVED_RULES
from hsim50 import swalk, SP
from hsim55 import lemmastep, _matches, norm


def TOP10(j, b):
    return ('B', TOP10F, 4042956, 1, 5937475,
            ((2 * j, 2), (1, 1)) + tuple(SP(b - 1)), 1)


def W(r11, b):
    return ((r11, 2), (1, 1)) + tuple(SP(b - 1))


TOP10F = (652285, 206767, 138671, 25145, 13306, 4643, 2871,
          335, 235, 42, 19)
TOP11F = (1511339, 790956, 25145, 13306, 4643, 2871,
          335, 235, 42, 19)
F11 = (4042956,) + TOP10F
F12 = (8675859,) + TOP11F

# CASCADE57 waypoint table (targets only), generated from the
# classified chain: pair lists are run-length items
# ('R', n) / ('P', a, b), with the final item 'W' standing for
# the arbitrary tail w (here W(r11, b)).
CASCADE57_WPS = [
    ('C', (206767, 138671, 25145, 13306, 4643, 2871, 335, 235, 42, 19), 652284, 4042954, 2, (('P', 1, 1), ('R', 5937476), 'W'), 1),  # P PX2A
    ('C', (206767, 138671, 25145, 13306, 4643, 2871, 335, 235, 42, 19), 652283, 1, 2, (('P', 4042952, 2), ('P', 1, 1), ('R', 5937476), 'W'), 1),  # P PUSH
    ('B', (206767, 138671, 25145, 13306, 4643, 2871, 335, 235, 42, 19), 652283, 1, 4, (('P', 4042952, 2), ('P', 1, 1), ('R', 5937476), 'W'), 1),  # P TDN
    ('C', (206767, 138671, 25145, 13306, 4643, 2871, 335, 235, 42, 19), 652283, 3, 2, (('P', 4042950, 2), ('P', 1, 1), ('R', 5937476), 'W'), 1),  # sTUP
    ('C', (206767, 138671, 25145, 13306, 4643, 2871, 335, 235, 42, 19), 0, 3, 2, (('R', 652283), ('P', 2738384, 2), ('P', 1, 1), ('R', 5937476), 'W'), 1),  # DIPGRIND 652283 2738384
    ('C', (25145, 13306, 4643, 2871, 335, 235, 42, 19), 138670, 206765, 2, (('P', 1, 1), ('R', 652285), ('P', 2738384, 2), ('P', 1, 1), ('R', 5937476), 'W'), 1),  # P PX2A
    ('B', (25145, 13306, 4643, 2871, 335, 235, 42, 19), 138670, 1, 206768, (('P', 1, 1), ('R', 652285), ('P', 2738384, 2), ('P', 1, 1), ('R', 5937476), 'W'), 1),  # hGRIND 103381
    ('B', (25145, 13306, 4643, 2871, 335, 235, 42, 19), 138671, 1, 206769, (('R', 652285), ('P', 2738384, 2), ('P', 1, 1), ('R', 5937476), 'W'), 1),  # P POP
    ('B', (25145, 13306, 4643, 2871, 335, 235, 42, 19), 790956, 1, 1511339, (('P', 2738384, 2), ('P', 1, 1), ('R', 5937476), 'W'), 1),  # M pop12 (652285,)
    ('C', (25145, 13306, 4643, 2871, 335, 235, 42, 19), 790956, 1511338, 2, (('P', 2738382, 2), ('P', 1, 1), ('R', 5937476), 'W'), 1),  # sTUP
    ('B', (25145, 13306, 4643, 2871, 335, 235, 42, 19), 790955, 1, 1511338, (('P', 2, 2), ('P', 2738382, 2), ('P', 1, 1), ('R', 5937476), 'W'), 1),  # hGRIND_even 755667
    ('C', (790956, 25145, 13306, 4643, 2871, 335, 235, 42, 19), 1511338, 1, 2, (('P', 2738380, 2), ('P', 1, 1), ('R', 5937476), 'W'), 1),  # P TUP2_1
    ('B', (790956, 25145, 13306, 4643, 2871, 335, 235, 42, 19), 1511338, 1, 4, (('P', 2738380, 2), ('P', 1, 1), ('R', 5937476), 'W'), 1),  # P TDN
    ('C', (790956, 25145, 13306, 4643, 2871, 335, 235, 42, 19), 1511338, 3, 2, (('P', 2738378, 2), ('P', 1, 1), ('R', 5937476), 'W'), 1),  # sTUP
    ('B', (790956, 25145, 13306, 4643, 2871, 335, 235, 42, 19), 1511338, 1, 2738382, (('P', 2, 2), ('P', 1, 1), ('R', 5937476), 'W'), 1),  # CLEANG_even 1369188
    ('B', (1511339, 790956, 25145, 13306, 4643, 2871, 335, 235, 42, 19), 2738383, 1, 3, (('R', 5937476), 'W'), 1),  # P TRANS2_1
    ('B', (1511339, 790956, 25145, 13306, 4643, 2871, 335, 235, 42, 19), 8675859, 1, 11874955, ('W'), 1),  # M pop12 (5937476,)
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


def expand_cfg(cfg, w):
    st, pb, A, g0, s, items, G = cfg
    return (st, pb, A, g0, s, expand(items, w), G)



def waypoints_rle(j, b):
    """The full asserted waypoint chain TOP10 -> ... -> TOP11
    (plus the r11' = 2 / 4 / 6 and band closing waypoints), in
    run-length form: pair lists are item lists ('P', a, b) /
    ('R', n) / 'W'.  Kept unexpanded -- at this phase's scale
    one expanded chain is ~40 GB of tuples."""
    j11 = j - 5937477
    tail = (('P', 1, 1), ('R', b - 1))
    pts = []
    pts.append(('C', TOP10F, 4042956, 5937474, 2,
                (('P', 2 * j - 2, 2),) + tail, 1))
    pts.append(('B', TOP10F, 4042955, 1, 5937474,
                (('P', 2, 2), ('P', 2 * j - 2, 2)) + tail, 1))
    pts.append(('C', F11, 5937474, 1, 2,
                (('P', 2 * j - 4, 2),) + tail, 1))
    pts.append(('B', F11, 5937474, 1, 4,
                (('P', 2 * j - 4, 2),) + tail, 1))
    pts.append(('C', F11, 5937474, 3, 2,
                (('P', 2 * j - 6, 2),) + tail, 1))
    pts.append(('C', F11, 0, 3, 2, (('R', 5937474), 'W'), 1))
    pts.extend(CASCADE57_WPS)
    # TOP11 state reached; closing waypoints by r11' = 2 * j11.
    if j11 == 1:
        pts.append(('B', (8675860,) + TOP11F, 11874956, 1, 3,
                    (('R', b - 1),), 1))
    if j11 == 2:
        pts.append(('C', TOP11F, 8675859, 11874954, 2,
                    (('P', 2, 2), ('P', 1, 1), ('R', b - 1)), 1))
        pts.append(('B', TOP11F, 8675858, 1, 11874954,
                    (('P', 2, 2), ('P', 2, 2), ('P', 1, 1),
                     ('R', b - 1)), 1))
        pts.append(('B', (11874955, 8675859) + TOP11F, 3, 1, 3,
                    (('R', b - 1),), 1))
    if j11 == 3:
        pts.append(('C', TOP11F, 8675859, 11874954, 2,
                    (('P', 4, 2), ('P', 1, 1), ('R', b - 1)), 1))
        pts.append(('B', TOP11F, 8675858, 1, 11874954,
                    (('P', 2, 2), ('P', 4, 2), ('P', 1, 1),
                     ('R', b - 1)), 1))
        pts.append(('C', F12, 11874954, 1, 2,
                    (('P', 2, 2), ('P', 1, 1), ('R', b - 1)), 1))
        pts.append(('B', F12, 11874954, 1, 4,
                    (('P', 2, 2), ('P', 1, 1), ('R', b - 1)), 1))
        pts.append(('B', (11874955, 8675859) + TOP11F, 5, 1, 3,
                    (('R', b - 1),), 1))
    if j11 >= 4:
        pts.append(('C', TOP11F, 8675859, 11874954, 2,
                    (('P', 2 * j11 - 2, 2), ('P', 1, 1),
                     ('R', b - 1)), 1))
        pts.append(('B', TOP11F, 8675858, 1, 11874954,
                    (('P', 2, 2), ('P', 2 * j11 - 2, 2),
                     ('P', 1, 1), ('R', b - 1)), 1))
        pts.append(('C', F12, 11874954, 1, 2,
                    (('P', 2 * j11 - 4, 2), ('P', 1, 1),
                     ('R', b - 1)), 1))
        pts.append(('B', F12, 11874954, 1, 4,
                    (('P', 2 * j11 - 4, 2), ('P', 1, 1),
                     ('R', b - 1)), 1))
        pts.append(('C', F12, 11874954, 3, 2,
                    (('P', 2 * j11 - 6, 2), ('P', 1, 1),
                     ('R', b - 1)), 1))
        pts.append(('B', F12, 11874954, 1, 2 * j11 - 2,
                    (('P', 2, 2), ('P', 1, 1), ('R', b - 1)), 1))
    return pts


def check_chain(j, b, cap=60000000):
    """check_chain with lazy waypoint expansion (the Phase 56
    scale forbids materialising the whole chain).  Matching,
    skip recording and lemmastep replay verification are
    hsim55's, verbatim in behaviour."""
    rle = waypoints_rle(j, b)
    w = W(2 * j - 11874954, b)
    N = len(rle)
    cache = {}

    def target(k):
        if k not in cache:
            if len(cache) > 24:
                cache.clear()
            cache[k] = norm(expand_cfg(rle[k], w))
        return cache[k]

    pos = -1
    status = fin = None
    used = set()
    src = TOP9(j, b)
    anchor = norm(src)
    skips = []  # (anchor, [skipped waypoints], landing)
    for rec in swalk(src, max_steps=cap):
        if isinstance(rec, tuple) and rec and rec[0] == 'STATUS':
            status, fin, used = rec[1], rec[2], rec[3]
            break
        if pos + 1 < N:
            if _matches(rec, target(pos + 1)):
                pos += 1
                anchor = target(pos)
            else:
                for k in range(pos + 2, min(pos + 9, N)):
                    if _matches(rec, target(k)):
                        skips.append((anchor,
                                      [target(t)
                                       for t in range(pos + 1, k)],
                                      target(k)))
                        pos = k
                        anchor = target(pos)
                        break
    assert pos == N - 1, \
        'j=%d b=%d: waypoint %d missing: %s' \
        % (j, b, pos + 1, fmt(target(pos + 1)))
    for (anchor, skipped, landing) in skips:
        targets = skipped + [landing]
        ti = 0
        cfg = anchor
        steps = 0
        while ti < len(targets) and steps < 200000:
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


def front_check(j, b):
    """The front segment TOP10(j, b) -> DIP10 spine (waypoints
    0..5), with check_chain's skip recording + lemmastep
    replay verification and early exit at the spine."""
    rle = waypoints_rle(j, b)
    w = W(2 * j - 11874954, b)
    pts = [norm(expand_cfg(c, w)) for c in rle[:6]]
    pos = -1
    anchor = norm(TOP10(j, b))
    skips = []
    for rec in swalk(TOP10(j, b), max_steps=20000000):
        if isinstance(rec, tuple) and rec and rec[0] == 'STATUS':
            break
        if pos + 1 < len(pts):
            if _matches(rec, pts[pos + 1]):
                pos += 1
                anchor = pts[pos]
            else:
                for k in range(pos + 2, min(pos + 9, len(pts))):
                    if _matches(rec, pts[k]):
                        skips.append((anchor, pts[pos + 1:k],
                                      pts[k]))
                        pos = k
                        anchor = pts[pos]
                        break
        if pos == len(pts) - 1:
            break
    assert pos == len(pts) - 1, \
        'front j=%d b=%d: waypoint %d missing' % (j, b, pos + 1)
    for (a0, skipped, landing) in skips:
        targets = skipped + [landing]
        ti = 0
        cfg = a0
        steps = 0
        while ti < len(targets) and steps < 200000:
            hit = lemmastep(cfg)
            assert hit is not None and hit[1] is not None, \
                ('front replay unmatched', cfg)
            cfg = hit[1]
            steps += 1
            if norm(cfg) == targets[ti]:
                ti += 1
        assert ti == len(targets), \
            'front j=%d b=%d: skipped waypoint not verified' \
            % (j, b)



def TOP11(j11, b):
    return ('B', TOP11F, 8675859, 1, 11874955,
            ((2 * j11, 2), (1, 1)) + tuple(SP(b - 1)), 1)


def main():
    """Execution structure (Phase 57 scale): Part 1 (the
    canonical chain) and Part 1b (the junk-tail probe) are
    executed SPAN-SLICED via phase57-work/walkslice57.py
    (checkpointed slice queues phase57-work/jobs and
    jobs-junk; each slice replicates check_chain's matching
    and lemmastep skip-replay verification on its segment);
    Parts 1c, 2, 3, 4 below run directly in this process.
    Running this main() monolithically re-executes Part 1
    and 1b in-process (hours at this scale)."""
    fails = 0
    used = set()
    # Part 1: the canonical full waypoint chain (5937478, 2).
    try:
        status, fin, pos, u = check_chain(5937478, 2)
        used.update(u)
        print('PASS chain j=5937478 b=2: %d waypoints in order, '
              'walk %s' % (len(waypoints_rle(5937478, 2)), status),
              flush=True)
    except AssertionError as e:
        fails += 1
        print('FAIL', e, flush=True)
    # Part 1b: CASCADE57 is tail-general -- junk tail probe.
    w0 = ((7, 2), (1, 1), (3, 2), (1, 2))
    src = ('C', F11, 0, 3, 2, tuple(SP(5937474)) + w0, 1)
    top11 = norm(('B', TOP11F, 8675859, 1, 11874955, w0, 1))
    ok = False
    for rec in swalk(src, max_steps=60000000):
        if isinstance(rec, tuple) and rec and rec[0] == 'STATUS':
            break
        if norm(rec) == top11:
            ok = True
            break
    print(('PASS' if ok else 'FAIL'),
          'tail-generality: TOP11 shape reached with junk tail',
          flush=True)
    fails += 0 if ok else 1
    # Part 1c: front segments at the other chain points (the
    # cascade parse is (j, beta)-uniform: classifier chains
    # at beta = 2, 3 are identical; the cascade segment is
    # walk-verified at the canonical point and for the junk
    # tail above).
    for (j, b) in [(5937478, 3), (5937479, 2), (5937480, 2),
                   (7000000, 2), (17812434, 2)]:
        try:
            front_check(j, b)
            print('PASS front segment j=%d b=%d: TOP10 -> DIP11 '
                  'spine' % (j, b), flush=True)
        except AssertionError as e:
            fails += 1
            print('FAIL', e, flush=True)
    # Part 2: TOP11-closing finals (walks from the TOP11
    # state, whose stack is just W).
    F12p = (8675860,) + TOP11F
    F13p = (11874955, 8675859) + TOP11F
    finals = {
        (1, 2): (F12p, 11874957),
        (1, 3): (F12p, 11874958),
        (2, 2): (F13p, 4),
        (2, 3): (F13p, 5),
        (3, 2): (F13p, 6),
        (3, 3): (F13p, 7),
        (1000000, 3): (F13p, 2000001),
        (11874957, 2): (F13p, 23749914),
    }
    for (j11, b), (fr, A) in sorted(finals.items()):
        status = fin = None
        for rec in swalk(TOP11(j11, b), max_steps=60000000):
            if isinstance(rec, tuple) and rec and rec[0] == 'STATUS':
                status, fin, u = rec[1], rec[2], rec[3]
                used.update(u)
                break
        want = ('B', tuple(fr), A, 1, 2 * b + 1, (), 1)
        ok = status == 'DONE' and norm(fin) == want
        print(('PASS' if ok else 'FAIL'),
              'TOP11 final j11=%d b=%d: %s (want A=%d frame %s)'
              % (j11, b, fmt(fin), A, list(fr)), flush=True)
        fails += 0 if ok else 1
    # Part 3: the twelfth fence from the TOP11 state --
    # r11' >= 23749916 takes DIPGRIND at 11874954 (j11 is
    # TOP11's parameter).
    for (j11, b) in [(11874958, 2), (11874959, 2), (12500000, 2)]:
        g12 = norm(('C', F12, 11874954, 3, 2,
                    ((2 * j11 - 6, 2), (1, 1)) + tuple(SP(b - 1)), 1))
        dip12 = norm(('C', F12, 0, 3, 2,
                      tuple(SP(11874954))
                      + ((2 * j11 - 23749914, 2), (1, 1))
                      + tuple(SP(b - 1)), 1))
        seen_g12 = seen_dip12 = False
        for rec in swalk(TOP11(j11, b), max_steps=60000000):
            if isinstance(rec, tuple) and rec and rec[0] == 'STATUS':
                break
            n = norm(rec)
            if n == g12:
                seen_g12 = True
            elif seen_g12 and n == dip12:
                seen_dip12 = True
                break
        ok = seen_g12 and seen_dip12
        print(('PASS' if ok else 'FAIL'),
              'fence j11=%d: GRIND12 then twelfth DIPGRIND '
              'landing occur (r11p=%d)' % (j11, 2 * j11),
              flush=True)
        fails += 0 if ok else 1
    # Part 4: primitive-step audit over the terminating
    # walks (the slice walks' records are produced by the
    # same mwalk/step_all; the classifier's step vocabulary
    # is exactly the PROVED_RULES lemma set).
    bad = used - PROVED_RULES
    print(('PASS' if not bad else 'FAIL'),
          'primitive rules used %s all in PROVED_RULES'
          % (sorted(used),), flush=True)
    fails += 0 if not bad else 1
    print()
    print('ALL PHASE 57 CHECKS PASS' if fails == 0
          else '%d FAILURES' % fails)
    return fails


if __name__ == '__main__':
    sys.exit(1 if main() else 0)
