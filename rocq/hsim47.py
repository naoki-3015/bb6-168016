#!/usr/bin/env python3
"""Phase 47 machine tests for the TAIL2_END reduction.

Characterisation (from mwalk traces of END(k, beta), k >= 3714):

  END(k, b) = HB [317; 40; 14; 5] 2204 1 3711 ((2k, 2) :: tail(b))

  1. FRONT (uniform in k, b): TUP, hGRIND_even 1853, TUP2_1, TDN, TUP
     -> HC [2204; 317; 40; 14; 5] 3710 3 2 ((2k-6, 2) :: tail(b)).
  2. DIPGRIND (3710, rho), rho = 2(k - 3713) >= 2:
     -> HC [2204; 317; 40; 14; 5] 0 3 2 (spine 3710 ++ W),
     W = ((rho, 2) :: (1, 1) :: (1, 2)^(b-1)).
  3. CASCADE47: a FIXED parse (34 waypoints, all frames/counters
     constant; rho and the era tail ride untouched at the bottom)
     -> MID = HB [1279; 745; 151; 77; 35; 20; 0] 289 1 3
              (spine 3712 ++ W).
  4. pop12 3712 -> TOP = HB [1279; 745; 151; 77; 35; 20; 0]
     4001 1 7427 W.
  5. TOP closings:
     rho = 2:        TRANS2_1 + POPFIN, A = 7427 + b,
                     frame [4002; 1279; ...].
     rho = 4:        TUP + hGRIND_even 3711 + TRANS2_2 + POPFIN,
                     A = b + 2, frame [7427; 4001; 1279; ...].
     rho = 6:        TUP + hGRIND_even 3711 + TUP2_1 + TDN
                     + TRANS2_1 + POPFIN (the pair after TUP2_1 is
                     (2, 2) itself, so TRANS2_1 fires at once),
                     A = b + 4, frame [7427; 4001; 1279; ...].
     8 <= rho <= 14858 (band 1): TUP + hGRIND_even 3711 + TUP2_1
                     + TDN + TUP -> GRIND2 = HC [4001; 1279; ...]
                     7426 3 2 ((rho-6, 2) :: tail(b)); CLEANG_even
                     ((rho-8)/2) (floor (rho-8)/2 + 1 <= 7426);
                     TRANS2_1 + POPFIN, A = rho + b - 2,
                     frame [7427; 4001; 1279; ...].
     rho >= 14860:   GRIND2's pair (rho-6, 2) exceeds the
                     CLEANG_even floor 2*7426; the rounds take the
                     DIPDESC boundary: DIPGRIND (7426, rho - 14858)
                     landing HC [4001; 1279; ...] 0 3 2
                     (spine 7426 ++ ((rho-14858, 2) :: tail(b)))
                     occurs (asserted in Part 3).  This is the
                     residual core TAIL2_END2 (at TOP, rho >= 14860).

Band boundary: rho <= 14858  <=>  k <= 11142.
"""
import sys
sys.path.insert(0, '/home/hatch/workspace/busy-beaver/rocq')
from hsim45 import mwalk
from hsim46 import END, fmt

SP = lambda n: [(1, 2)] * n


def W(rho, b):
    return [(rho, 2), (1, 1)] + SP(b - 1)


def waypoints(k, b):
    """The full asserted waypoint chain END -> ... -> TOP."""
    rho = 2 * (k - 3713)
    w = W(rho, b)
    tail = [(1, 1)] + SP(b - 1)
    F5 = [2204, 317, 40, 14, 5]
    pts = []
    pts.append(('C', F5, 3710, 3, 2, [(2 * k - 6, 2)] + tail, 1))
    pts.append(('C', F5, 0, 3, 2, SP(3710) + w, 1))
    pts.append(('C', [40, 14, 5], 315, 3, 2,
                [(2198, 2), (1, 1)] + SP(3712) + w, 1))
    pts.append(('C', [40, 14, 5], 0, 3, 2,
                SP(315) + [(1568, 2), (1, 1)] + SP(3712) + w, 1))
    pts.append(('C', [5], 12, 3, 2,
                [(34, 2), (1, 1)] + SP(317)
                + [(1568, 2), (1, 1)] + SP(3712) + w, 1))
    pts.append(('C', [5], 0, 3, 2,
                SP(12) + [(10, 2), (1, 1)] + SP(317)
                + [(1568, 2), (1, 1)] + SP(3712) + w, 1))
    pts.append(('B', [0], 3, 1, 2,
                [(1, 2), (1, 1)] + SP(14) + [(10, 2), (1, 1)] + SP(317)
                + [(1568, 2), (1, 1)] + SP(3712) + w, 1))
    pts.append(('C', [19, 0], 32, 3, 2,
                [(4, 2), (1, 1)] + SP(317)
                + [(1568, 2), (1, 1)] + SP(3712) + w, 1))
    pts.append(('B', [33, 19, 0], 9, 1, 3,
                SP(317) + [(1568, 2), (1, 1)] + SP(3712) + w, 1))
    pts.append(('C', [326, 33, 19, 0], 636, 3, 2,
                [(1562, 2), (1, 1)] + SP(3712) + w, 1))
    pts.append(('C', [326, 33, 19, 0], 0, 3, 2,
                SP(636) + [(290, 2), (1, 1)] + SP(3712) + w, 1))
    pts.append(('C', [19, 0], 31, 3, 2,
                [(320, 2), (1, 1)] + SP(638)
                + [(290, 2), (1, 1)] + SP(3712) + w, 1))
    pts.append(('C', [19, 0], 0, 3, 2,
                SP(31) + [(258, 2), (1, 1)] + SP(638)
                + [(290, 2), (1, 1)] + SP(3712) + w, 1))
    pts.append(('C', [0], 3, 3, 2,
                [(11, 2), (1, 1)] + SP(33) + [(258, 2), (1, 1)] + SP(638)
                + [(290, 2), (1, 1)] + SP(3712) + w, 1))
    pts.append(('C', [0], 0, 3, 2,
                SP(3) + [(5, 2), (1, 1)] + SP(33)
                + [(258, 2), (1, 1)] + SP(638)
                + [(290, 2), (1, 1)] + SP(3712) + w, 1))
    pts.append(('B', [], 0, 1, 5,
                SP(4) + [(5, 2), (1, 1)] + SP(33)
                + [(258, 2), (1, 1)] + SP(638)
                + [(290, 2), (1, 1)] + SP(3712) + w, 1))
    R1 = (SP(33) + [(258, 2), (1, 1)] + SP(638)
          + [(290, 2), (1, 1)] + SP(3712) + w)
    pts.append(('C', [], 3, 3, 2, [(8, 2), (3, 2), (1, 1)] + R1, 1))
    pts.append(('C', [], 0, 3, 2,
                SP(3) + [(2, 2), (3, 2), (1, 1)] + R1, 1))
    pts.append(('B', [], 1, 1, 7,
                SP(3) + [(2, 2), (3, 2), (1, 1)] + R1, 1))
    pts.append(('B', [5], 13, 1, 4, [(1, 2), (1, 1)] + R1, 1))
    R2 = SP(638) + [(290, 2), (1, 1)] + SP(3712) + w
    pts.append(('C', [48, 5], 72, 3, 2, [(252, 2), (1, 1)] + R2, 1))
    pts.append(('C', [48, 5], 0, 3, 2,
                SP(72) + [(108, 2), (1, 1)] + R2, 1))
    R3 = SP(74) + [(108, 2), (1, 1)] + R2
    pts.append(('C', [], 3, 3, 2, [(42, 2), (1, 1)] + R3, 1))
    pts.append(('C', [], 0, 3, 2, SP(3) + [(36, 2), (1, 1)] + R3, 1))
    pts.append(('B', [], 1, 1, 7, SP(3) + [(36, 2), (1, 1)] + R3, 1))
    pts.append(('C', [], 3, 3, 2, [(8, 2), (34, 2), (1, 1)] + R3, 1))
    pts.append(('C', [], 0, 3, 2,
                SP(3) + [(2, 2), (34, 2), (1, 1)] + R3, 1))
    pts.append(('B', [], 1, 1, 7,
                SP(3) + [(2, 2), (34, 2), (1, 1)] + R3, 1))
    pts.append(('C', [5], 13, 3, 2, [(30, 2), (1, 1)] + R3, 1))
    pts.append(('C', [5], 0, 3, 2, SP(13) + [(4, 2), (1, 1)] + R3, 1))
    pts.append(('B', [0], 3, 1, 2,
                [(1, 2), (1, 1)] + SP(15) + [(4, 2), (1, 1)] + R3, 1))
    pts.append(('B', [35, 20, 0], 3, 1, 3, R3, 1))
    pts.append(('C', [77, 35, 20, 0], 150, 3, 2,
                [(102, 2), (1, 1)] + R2, 1))
    pts.append(('B', [151, 77, 35, 20, 0], 107, 1, 3, R2, 1))
    pts.append(('C', [745, 151, 77, 35, 20, 0], 1278, 3, 2,
                [(284, 2), (1, 1)] + SP(3712) + w, 1))
    pts.append(('B', [1279, 745, 151, 77, 35, 20, 0], 289, 1, 3,
                SP(3712) + w, 1))
    pts.append(('B', [1279, 745, 151, 77, 35, 20, 0], 4001, 1, 7427,
                w, 1))
    return pts


def norm(cfg):
    st, pb, A, g0, s, pairs, G = cfg
    return (st, tuple(pb), A, g0, s, tuple(pairs), G)


def check_chain(k, b):
    steps, status, fin = mwalk(END(k, b), max_steps=3000000)
    hist = [norm(st[-1]) for st in steps]
    pts = [norm(p) for p in waypoints(k, b)]
    pos = -1
    for p in pts:
        found = None
        for i in range(pos + 1, len(hist)):
            if hist[i] == p:
                found = i
                break
        assert found is not None, \
            'k=%d b=%d: waypoint missing after %d: %s' \
            % (k, b, pos, fmt(p))
        pos = found
    return steps, status, fin, pos


def main():
    fails = 0
    # Part 1: full waypoint chain END -> TOP, several bands.
    for (k, b) in [(3714, 2), (3714, 3), (3715, 2), (4000, 2),
                   (5000, 3), (11142, 2), (11143, 2), (12000, 2)]:
        try:
            steps, status, fin, pos = check_chain(k, b)
            print('PASS chain k=%d b=%d: %d waypoints in order, '
                  'TOP at step %d, walk %s'
                  % (k, b, len(waypoints(k, b)), pos, status))
        except AssertionError as e:
            fails += 1
            print('FAIL', e)
    # Part 2: band-1 finals.
    finals = {
        (3714, 2): ([4002, 1279, 745, 151, 77, 35, 20, 0], 7429),
        (3714, 3): ([4002, 1279, 745, 151, 77, 35, 20, 0], 7430),
        (3715, 2): ([7427, 4001, 1279, 745, 151, 77, 35, 20, 0], 4),
        (3715, 3): ([7427, 4001, 1279, 745, 151, 77, 35, 20, 0], 5),
        (3716, 2): ([7427, 4001, 1279, 745, 151, 77, 35, 20, 0], 6),
        (3717, 2): ([7427, 4001, 1279, 745, 151, 77, 35, 20, 0], 8),
        (3718, 3): ([7427, 4001, 1279, 745, 151, 77, 35, 20, 0], 11),
        (4000, 2): ([7427, 4001, 1279, 745, 151, 77, 35, 20, 0], 574),
        (5000, 3): ([7427, 4001, 1279, 745, 151, 77, 35, 20, 0],
                    2574 + 1),
        (11142, 2): ([7427, 4001, 1279, 745, 151, 77, 35, 20, 0],
                     14858),
    }
    for (k, b), (fr, A) in sorted(finals.items()):
        steps, status, fin = mwalk(END(k, b), max_steps=3000000)
        want = ('B', tuple(fr), A, 1, 2 * b + 1, (), 1)
        ok = status == 'DONE' and norm(fin) == want
        print(('PASS' if ok else 'FAIL'),
              'final k=%d b=%d: %s (want A=%d frame %s)'
              % (k, b, fmt(fin), A, fr))
        fails += 0 if ok else 1
    # Part 3: the fence -- rho >= 14860 takes the cycle-2 DIPDESC.
    for (k, b) in [(11143, 2), (12000, 2), (20000, 2)]:
        rho = 2 * (k - 3713)
        steps, status, fin = mwalk(END(k, b), max_steps=3000000)
        hist = [norm(st[-1]) for st in steps]
        g2 = norm(('C', [4001, 1279, 745, 151, 77, 35, 20, 0],
                   7426, 3, 2, [(rho - 6, 2), (1, 1)] + SP(b - 1), 1))
        dip2 = norm(('C', [4001, 1279, 745, 151, 77, 35, 20, 0],
                     0, 3, 2,
                     SP(7426) + [(rho - 14858, 2), (1, 1)]
                     + SP(b - 1), 1))
        ok = g2 in hist and dip2 in hist \
            and hist.index(g2) < hist.index(dip2)
        print(('PASS' if ok else 'FAIL'),
              'fence k=%d: GRIND2 then cycle-2 DIPGRIND landing '
              'occur (rho=%d)' % (k, rho))
        fails += 0 if ok else 1
    print()
    print('ALL PHASE 47 CHECKS PASS' if fails == 0
          else '%d FAILURES' % fails)
    return fails


if __name__ == '__main__':
    sys.exit(1 if main() else 0)
