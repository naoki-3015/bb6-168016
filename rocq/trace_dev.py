#!/usr/bin/env python3
"""Zipper tracer for Phase 28: print (state, left RLE nearest-first, right RLE)
at each step from an explicit starting zipper."""
SPEC = "1RB1RA_1RC1LB_0LD0RA_1RF1LE_---1LF_1LC0LF"
SN = ["A", "B", "C", "D", "E", "F"]

def parse(spec):
    states = []
    for group in spec.strip().split('_'):
        trans = []
        for i in (0, 3):
            t = group[i:i + 3]
            trans.append(None if t == '---' else
                         (int(t[0]), 1 if t[1] == 'R' else -1, ord(t[2]) - ord('A')))
        states.append(trans)
    return states

TM = parse(SPEC)

def rle(lst):
    out = []
    for v in lst:
        if out and out[-1][0] == v:
            out[-1][1] += 1
        else:
            out.append([v, 1])
    return ' '.join('%d:%d' % (v, n) for v, n in out) if out else '(empty)'

class Z:
    # left: list nearest-first; right: list from head rightward. Tape beyond
    # both lists is blank; we keep explicit trailing blanks minimal.
    def __init__(self, left, right, st):
        self.left = list(left)
        self.right = list(right)
        self.st = st
    def show(self):
        return 'st=%s L[%s] R[%s]' % (SN[self.st], rle(self.left), rle(self.right))
    def step(self):
        sym = self.right[0] if self.right else 0
        tr = TM[self.st][sym]
        assert tr is not None, 'HALT at ' + self.show()
        w, mv, nx = tr
        if self.right:
            self.right[0] = w
        else:
            self.right = [w]
        if mv == 1:
            self.left.insert(0, self.right.pop(0))
        else:
            if self.left:
                self.right.insert(0, self.left.pop(0))
            else:
                self.right.insert(0, 0)
        self.st = nx
    def run(self, n, show_from=0):
        for i in range(n + 1):
            if i >= show_from:
                print('%3d %s' % (i, self.show()))
            if i < n:
                self.step()

def tail(pairs, G):
    out = []
    for g, r in pairs:
        out += [0] * g + [1] * r
    out += [0] * G + [1, 1]
    return out

def sec_cells(a, g0, s, pairs, G):
    return [1] * a + [0] * g0 + [1] * s + tail(pairs, G)
