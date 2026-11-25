#!/usr/bin/env python3
"""Trace zipper configurations step by step for one bounce of each
rule (single-block frame), to fix the exact intermediate forms used
in the Rocq segment lemmas of Sections.v."""
SPEC = "1RB1RA_1RC1LB_0LD0RA_1RF1LE_---1LF_1LC0LF"
SN = ["A", "B", "C", "D", "E", "F"]


def parse(spec):
    states = []
    for group in spec.strip().split('_'):
        trans = []
        for i in (0, 3):
            t = group[i:i + 3]
            trans.append(None if t == '---' else
                         (int(t[0]), 1 if t[1] == 'R' else -1,
                          ord(t[2]) - ord('A')))
        states.append(trans)
    return states


TM = parse(SPEC)


def cells_of(a, g0, s, pairs, G):
    cells = [1] * a + [0] * g0 + [1] * s
    for g, r in pairs:
        cells += [0] * g + [1] * r
    cells += [0] * G + [1, 1]
    return cells


def rle(lst):
    out = []
    for v in lst:
        if out and out[-1][0] == v:
            out[-1][1] += 1
        else:
            out.append([v, 1])
    return ' '.join('%d:%d' % (v, n) for v, n in out)


class Z:
    def __init__(self, cells, head, st):
        self.tape = {i: v for i, v in enumerate(cells) if v}
        self.h = head
        self.st = st

    def show(self):
        keys = list(self.tape.keys()) + [self.h]
        lo, hi = min(keys), max(keys)
        left = [self.tape.get(i, 0) for i in range(self.h - 1, lo - 1, -1)]
        right = [self.tape.get(i, 0) for i in range(self.h, hi + 1)]
        return 'st=%s L[%s] R[%s]' % (SN[self.st], rle(left), rle(right))

    def step(self):
        sym = self.tape.get(self.h, 0)
        tr = TM[self.st][sym]
        assert tr is not None, 'HALT'
        w, mv, nx = tr
        if w:
            self.tape[self.h] = 1
        elif self.h in self.tape:
            del self.tape[self.h]
        self.h += mv
        self.st = nx


def trace(label, cells, head, st, nsteps):
    z = Z(cells, head, st)
    print('== %s ==' % label)
    print(' 0', z.show())
    for i in range(1, nsteps + 1):
        z.step()
        print('%2d' % i, z.show())
    print()


# TDN: C-section a=6, g0=1, s=2, pairs=[(3,2)], G=7 ; head a-2=4
trace('TDN a=6 g0=1 s=2', cells_of(6, 1, 2, [(3, 2)], 7), 4, 2, 6)
# PUSH: C-section a=6, g0=5, s=2, pairs=[(3,2)], G=7
trace('PUSH a=6 g0=5 s=2', cells_of(6, 5, 2, [(3, 2)], 7), 4, 2, 9)
# POP: B-section a=5, g0=1, s=4, pairs=[(1,3),(3,2)], G=7 ; head a=5
trace('POP a=5 s=4 r1=3', cells_of(5, 1, 4, [(1, 3), (3, 2)], 7), 5, 1, 11)
# Stage A: B-section a=5, g0=1, s=4 (L), pairs=[], G=8 ; cost 2*4+6=14
trace('StageA a=5 L=4 G=8', cells_of(5, 1, 4, [], 8), 5, 1, 14)
