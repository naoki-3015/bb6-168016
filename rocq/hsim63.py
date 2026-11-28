#!/usr/bin/env python3
"""Machine-side harness for Phase 63 of the #168016 Rocq
mechanisation: the SEVENTEENTH descent (TAIL2_END17 at TOP16,
j >= 595648560).  Same machinery as hsim62.py (itself from
hsim50-61): expand/check_chain/front_check operate on
RLE-encoded stacks.

Setting: the front takes TOP16(j, b) -- HB TOP16F 367754682 1
595648557 W -- through TUP, hGRIND_even 297824276, TUP2_1,
TDN, TUP to GRIND17 (HC F17 595648556 3 2 W), F17 = (367754682,)
+ TOP16F, and DIPGRIND (595648556, 2*j17) descends to the
CASCADE63 initial config HC F17 0 3 2 (SP(595648556) ++ W),
W = ((2*j17, 2), (1, 1)) + SP(b - 1), j17 = j - 595648559.
CASCADE63 (17 steps, uniform in beta modulo the tail) lands
at TOP17 -- HB TOP17F 842094153 1 1191297119 W.  The TOP17
frame SHRANK by one block against TOP16 (12 blocks against
13).  Closings at TOP17, by r17 = 2*j17:
  * r17 = 2: TRANS2_1 + CASCADE_POPFIN onto HB
    [(842094154); TOP17F] (1191297119 + b - 1) 1 3 [].
  * r17 = 4: TUP + hGRIND_even 595648557 + TRANS2_2 +
    CASCADE_POPFIN onto HB [1191297119; 842094153; TOP17F]
    (b + 2) 1 (2b + 1) [].
  * r17 = 6: TUP + hGRIND_even 595648557 + TUP2_1 + TDN +
    TRANS2_1 + CASCADE_POPFIN onto the same frame with
    A = b + 4.
  * 8 <= r17 <= 2382594242 (band 17): TUP + hGRIND_even
    595648557 + TUP2_1 + TDN + TUP + CLEANG_even at counter
    1191297118, then TRANS2_1 + CASCADE_POPFIN onto the same
    frame with A = r17 + b - 2.
  * r17 >= 2382594244 (the eighteenth fence): GRIND18 --
    HC F18 1191297118 3 2 ((r17 - 6, 2) :: W), F18 =
    (842094153,) + TOP17F -- and DIPGRIND (1191297118,
    r17 - 2382594242) descends an eighteenth time: the
    residual TAIL2_END18 (Grind31p.v).

Parts 1/1b/1c are NOT executed by this file (Phase 60-62
pattern): Part 2 (TOP17 finals) and Part 3 (the eighteenth
fence, at classify granularity -- the Phase 61/62 deviation,
documented in the status file) live in
phase63-work/finals63.py and finals63-fence2.py; the
primitive-step audit is Part 4 of finals63.py.
"""
import sys
sys.path.insert(0, '/home/hatch/workspace/busy-beaver/rocq')
sys.path.insert(0, '/home/hatch/workspace/busy-beaver/phase63-work')
import hsim50
import hsim55
from hsim55 import lemmastep, _matches, norm
from rle_classify import classify_rle

TOP16F = (60654542, 9546949, 4860546, 349423, 101323, 57668,
          5526, 626, 189, 112, 33, 19, 0)
TOP17F = (130856035, 65515088, 349423, 101323, 57668, 5526,
          626, 189, 112, 33, 19, 0)
S17 = 842094153
SH17 = 1191297119
F17 = (367754682,) + TOP16F
F18 = (S17,) + TOP17F


def SP(n):
    return ((1, 2),) * n


def W(r17, b):
    return ((r17, 2), (1, 1)) + SP(b - 1)


def TOP16(j, b):
    return ('B', TOP16F, 367754682, 1, 595648557, W(2 * j, b), 1)


CASCADE63_WPS = [
    ('C', (9546949, 4860546, 349423, 101323, 57668, 5526, 626, 189, 112, 33, 19, 0), 60654541, 367754680, 2, (('P', 1, 1), ('R', 595648558), 'W'), 1),  # P PX2A
    ('C', (9546949, 4860546, 349423, 101323, 57668, 5526, 626, 189, 112, 33, 19, 0), 60654540, 1, 2, (('P', 367754678, 2), ('P', 1, 1), ('R', 595648558), 'W'), 1),  # P PUSH
    ('B', (9546949, 4860546, 349423, 101323, 57668, 5526, 626, 189, 112, 33, 19, 0), 60654540, 1, 4, (('P', 367754678, 2), ('P', 1, 1), ('R', 595648558), 'W'), 1),  # P TDN
    ('C', (9546949, 4860546, 349423, 101323, 57668, 5526, 626, 189, 112, 33, 19, 0), 60654540, 3, 2, (('P', 367754676, 2), ('P', 1, 1), ('R', 595648558), 'W'), 1),  # sTUP
    ('C', (9546949, 4860546, 349423, 101323, 57668, 5526, 626, 189, 112, 33, 19, 0), 0, 3, 2, (('R', 60654540), ('P', 246445596, 2), ('P', 1, 1), ('R', 595648558), 'W'), 1),  # DIPGRIND 60654540 246445596
    ('C', (349423, 101323, 57668, 5526, 626, 189, 112, 33, 19, 0), 4860545, 9546947, 2, (('P', 1, 1), ('R', 60654542), ('P', 246445596, 2), ('P', 1, 1), ('R', 595648558), 'W'), 1),  # P PX2A
    ('B', (349423, 101323, 57668, 5526, 626, 189, 112, 33, 19, 0), 4860545, 1, 9546950, (('P', 1, 1), ('R', 60654542), ('P', 246445596, 2), ('P', 1, 1), ('R', 595648558), 'W'), 1),  # hGRIND 4773472
    ('B', (349423, 101323, 57668, 5526, 626, 189, 112, 33, 19, 0), 4860546, 1, 9546951, (('R', 60654542), ('P', 246445596, 2), ('P', 1, 1), ('R', 595648558), 'W'), 1),  # P POP
    ('B', (349423, 101323, 57668, 5526, 626, 189, 112, 33, 19, 0), 65515088, 1, 130856035, (('P', 246445596, 2), ('P', 1, 1), ('R', 595648558), 'W'), 1),  # M pop12 (60654542,)
    ('C', (349423, 101323, 57668, 5526, 626, 189, 112, 33, 19, 0), 65515088, 130856034, 2, (('P', 246445594, 2), ('P', 1, 1), ('R', 595648558), 'W'), 1),  # sTUP
    ('B', (349423, 101323, 57668, 5526, 626, 189, 112, 33, 19, 0), 65515087, 1, 130856034, (('P', 2, 2), ('P', 246445594, 2), ('P', 1, 1), ('R', 595648558), 'W'), 1),  # hGRIND_even 65428015
    ('C', (65515088, 349423, 101323, 57668, 5526, 626, 189, 112, 33, 19, 0), 130856034, 1, 2, (('P', 246445592, 2), ('P', 1, 1), ('R', 595648558), 'W'), 1),  # P TUP2_1
    ('B', (65515088, 349423, 101323, 57668, 5526, 626, 189, 112, 33, 19, 0), 130856034, 1, 4, (('P', 246445592, 2), ('P', 1, 1), ('R', 595648558), 'W'), 1),  # P TDN
    ('C', (65515088, 349423, 101323, 57668, 5526, 626, 189, 112, 33, 19, 0), 130856034, 3, 2, (('P', 246445590, 2), ('P', 1, 1), ('R', 595648558), 'W'), 1),  # sTUP
    ('B', (65515088, 349423, 101323, 57668, 5526, 626, 189, 112, 33, 19, 0), 130856034, 1, 246445594, (('P', 2, 2), ('P', 1, 1), ('R', 595648558), 'W'), 1),  # CLEANG_even 123222794
    ('B', (130856035, 65515088, 349423, 101323, 57668, 5526, 626, 189, 112, 33, 19, 0), 246445595, 1, 3, (('R', 595648558), 'W'), 1),  # P TRANS2_1
    ('B', (130856035, 65515088, 349423, 101323, 57668, 5526, 626, 189, 112, 33, 19, 0), 842094153, 1, 1191297119, ('W',), 1),  # M pop12 (595648558,)
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





def check_chain(j, b, cap=120000000):
    """check_chain with lazy waypoint expansion (the Phase 56
    scale forbids materialising the whole chain).  Matching,
    skip recording and lemmastep replay verification are
    hsim55's, verbatim in behaviour."""
    rle = waypoints_rle(j, b)
    w = W(2 * (j - 595648559), b)
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
    src = TOP16(j, b)
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
    """The front segment TOP16(j, b) -> DIP17 spine (waypoints
    0..5), with check_chain's skip recording + lemmastep
    replay verification and early exit at the spine."""
    rle = waypoints_rle(j, b)
    w = W(2 * (j - 595648559), b)
    pts = [norm(expand_cfg(c, w)) for c in rle[:6]]
    pos = -1
    anchor = norm(TOP16(j, b))
    skips = []
    for rec in swalk(TOP16(j, b), max_steps=20000000):
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




def waypoints_rle(j, b):
    """The full asserted waypoint chain TOP16 -> ... -> TOP17
    (plus the r17 = 2 / 4 / 6 and band closing waypoints), in
    run-length form.  Kept unexpanded -- at this phase's scale
    one expanded chain is ~3 TB of tuples."""
    j17 = j - 595648559
    tail = (('P', 1, 1), ('R', b - 1))
    pts = []
    pts.append(('C', TOP16F, 367754682, 595648556, 2,
                (('P', 2 * j - 2, 2),) + tail, 1))
    pts.append(('B', TOP16F, 367754681, 1, 595648556,
                (('P', 2, 2), ('P', 2 * j - 2, 2)) + tail, 1))
    pts.append(('C', F17, 595648556, 1, 2,
                (('P', 2 * j - 4, 2),) + tail, 1))
    pts.append(('B', F17, 595648556, 1, 4,
                (('P', 2 * j - 4, 2),) + tail, 1))
    pts.append(('C', F17, 595648556, 3, 2,
                (('P', 2 * j - 6, 2),) + tail, 1))
    pts.append(('C', F17, 0, 3, 2, (('R', 595648556), 'W'), 1))
    pts.extend(CASCADE63_WPS)
    if j17 == 1:
        pts.append(('B', (S17 + 1,) + TOP17F, SH17 + 1, 1, 3,
                    (('R', b - 1),), 1))
    elif j17 == 2:
        pts.append(('C', TOP17F, S17, SH17 - 1, 2,
                    (('P', 2, 2), ('P', 1, 1), ('R', b - 1)), 1))
        pts.append(('B', TOP17F, S17 - 1, 1, SH17 - 1,
                    (('P', 2, 2), ('P', 2, 2), ('P', 1, 1),
                     ('R', b - 1)), 1))
        pts.append(('B', (SH17, S17) + TOP17F, 3, 1, 3,
                    (('R', b - 1),), 1))
    elif j17 == 3:
        pts.append(('C', TOP17F, S17, SH17 - 1, 2,
                    (('P', 4, 2), ('P', 1, 1), ('R', b - 1)), 1))
        pts.append(('B', TOP17F, S17 - 1, 1, SH17 - 1,
                    (('P', 2, 2), ('P', 4, 2), ('P', 1, 1),
                     ('R', b - 1)), 1))
        pts.append(('C', F18, SH17 - 1, 1, 2,
                    (('P', 2, 2), ('P', 1, 1), ('R', b - 1)), 1))
        pts.append(('B', F18, SH17 - 1, 1, 4,
                    (('P', 2, 2), ('P', 1, 1), ('R', b - 1)), 1))
        pts.append(('B', (SH17, S17) + TOP17F, 5, 1, 3,
                    (('R', b - 1),), 1))
    else:
        pts.append(('C', TOP17F, S17, SH17 - 1, 2,
                    (('P', 2 * j17 - 2, 2), ('P', 1, 1),
                     ('R', b - 1)), 1))
        pts.append(('B', TOP17F, S17 - 1, 1, SH17 - 1,
                    (('P', 2, 2), ('P', 2 * j17 - 2, 2),
                     ('P', 1, 1), ('R', b - 1)), 1))
        pts.append(('C', F18, SH17 - 1, 1, 2,
                    (('P', 2 * j17 - 4, 2), ('P', 1, 1),
                     ('R', b - 1)), 1))
        pts.append(('B', F18, SH17 - 1, 1, 4,
                    (('P', 2 * j17 - 4, 2), ('P', 1, 1),
                     ('R', b - 1)), 1))
        pts.append(('C', F18, SH17 - 1, 3, 2,
                    (('P', 2 * j17 - 6, 2), ('P', 1, 1),
                     ('R', b - 1)), 1))
        pts.append(('B', F18, SH17 - 1, 1, 2 * j17 - 2,
                    (('P', 2, 2), ('P', 1, 1), ('R', b - 1)), 1))
    return pts


def TOP17(j17, b):
    return ('B', TOP17F, S17, 1, SH17, W(2 * j17, b), 1)


def main():
    print('hsim63: Parts 1/1b/1c are not executed by this file '
          '(Phase 60-62 pattern).')
    print('Run phase63-work/finals63.py (Parts 2 + 4) and '
          'phase63-work/finals63-fence2.py (Part 3).')


if __name__ == '__main__':
    main()
