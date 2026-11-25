#!/usr/bin/env python3
"""Phase 23: generate the concrete configurations for the Rocq
finite-segment checks (Configs.v), and sanity-verify every finite
claim in Python first (dict simulator, table parsed from the spec).

A configuration is emitted as a Coq zipper (state, left, right):
left = cells left of the head, nearest first; right = cells from
the head rightward.  Runs are emitted via `rep b n`.
"""
import sys

SPEC = "1RB1RA_1RC1LB_0LD0RA_1RF1LE_---1LF_1LC0LF"
A, B, C, D, E, F = range(6)
SN = ["SA", "SB", "SC", "SD", "SE", "SF"]


def parse(spec):
    states = []
    for group in spec.strip().split('_'):
        trans = []
        for i in (0, 3):
            t = group[i:i + 3]
            if t == '---':
                trans.append(None)
            else:
                trans.append((int(t[0]), 1 if t[1] == 'R' else -1,
                              ord(t[2]) - ord('A')))
        states.append(trans)
    return states


TM = parse(SPEC)


class Sim:
    def __init__(self, cells=(), head=0, state=0):
        self.tape = {i: v for i, v in enumerate(cells) if v}
        self.h = head
        self.st = state

    def step(self):
        sym = self.tape.get(self.h, 0)
        tr = TM[self.st][sym]
        if tr is None:
            return False
        w, mv, nx = tr
        if w:
            self.tape[self.h] = 1
        elif self.h in self.tape:
            del self.tape[self.h]
        self.h += mv
        self.st = nx
        return True

    def run(self, n):
        for _ in range(n):
            if not self.step():
                return False
        return True

    def rle(self):
        """Head-relative finite span as run list [(v, n), ...]."""
        keys = list(self.tape.keys()) + [self.h]
        lo, hi = min(keys), max(keys)
        cells = [self.tape.get(i, 0) for i in range(lo, hi + 1)]
        runs = []
        for v in cells:
            if runs and runs[-1][0] == v:
                runs[-1][1] += 1
            else:
                runs.append([v, 1])
        return [tuple(r) for r in runs], self.h - lo, self.st


def runs_cells(runs):
    cells = []
    for v, n in runs:
        cells += [v] * n
    return cells


def s_runs(k, wall):
    runs = []
    for b in wall:
        runs += [(1, b), (0, 1)]
    runs += [(1, k), (0, 1)]
    return runs


# ---- concrete configurations: (runs, head_index, state) ----------------
CFG = {}
CFG['blank'] = ([], 0, A)                       # empty tape, head 0
CFG['S2'] = (s_runs(2, (4, 17, 27)), None, B)
CFG['S4'] = (s_runs(4, (4, 17, 27)), None, B)
CFG['Sp2'] = (s_runs(2, (4, 41, 65)), None, B)
CFG['Sp4'] = (s_runs(4, (4, 41, 65)), None, B)
CFG['Sp6'] = (s_runs(6, (4, 41, 65)), None, B)
for nm in ('S2', 'S4', 'Sp2', 'Sp4', 'Sp6'):
    runs, _, st = CFG[nm]
    CFG[nm] = (runs, sum(n for _, n in runs) - 1, st)   # head = last cell
CFG['D132'] = ([(1, 4), (0, 1), (1, 41), (0, 1), (1, 1)]
               + [(0, 1), (1, 2)] * 66, 46, C)
CFG['R'] = ([(1, 17), (0, 1), (1, 97), (0, 1), (1, 137), (0, 1)], 253, B)
CFG['Isec'] = ([(1, 17), (0, 1), (1, 97), (0, 1), (1, 2), (0, 134),
                (1, 2)], 113, C)
CFG['sre4'] = ([(1, 17), (0, 1), (1, 31), (0, 1), (1, 4), (0, 1),
                (1, 2)], 52, C)
CFG['sre8'] = ([(1, 17), (0, 1), (1, 31), (0, 1), (1, 8), (0, 1),
                (1, 2)], 56, C)


def sim_from(name):
    runs, head, st = CFG[name]
    return Sim(runs_cells(runs), head, st)


def snap(name):
    runs, head, st = CFG[name]
    return runs, head, st


FAILS = []


def expect(sim, name, label):
    runs, head, st = snap(name)
    got_runs, got_head, got_st = sim.rle()
    ok = (got_runs == runs and got_head == head and got_st == st)
    print(('OK ' if ok else 'FAIL ') + label)
    if not ok:
        FAILS.append(label)
        print('  want', (runs, head, SN[st]))
        print('  got ', (got_runs, got_head, SN[got_st]))


# ---- Python sanity verification of every finite claim ------------------
sim = Sim()
assert sim.run(197317)
expect(sim, 'S2', 'blank -> S(2) in 197,317')
assert sim.run(197335 - 197317)
expect(sim, 'S4', 'blank -> S(4) in 197,335 (S period P(2) = 18)')

for nm, m, per in (('Sp2', 2, 18), ('Sp4', 4, 42)):
    sim = sim_from(nm)
    assert sim.run(per)
    expect(sim, 'Sp%d' % (m + 2), "S'(%d) -> S'(%d) in P(%d) = %d"
           % (m, m + 2, m, per))

sim = sim_from('D132')
assert sim.run(403455)
expect(sim, 'R', 'D(132,66) -> R in 403,455')

sim = sim_from('R')
assert sim.run(150)
expect(sim, 'Isec', 'R -> first I-section in 150')

for be, t in ((4, 102), (8, 2850)):
    sim = sim_from('sre%d' % be)
    assert sim.run(t)
    runs, head, st = sim.rle()
    CFG['H%d' % be] = (runs, head, st)
    print('H%d from sim:' % be, runs, 'head', head, SN[st])
    assert sim.run(6)
    runs, head, st = sim.rle()
    CFG['X%d' % be] = (runs, head, st)
    print('X%d from sim:' % be, runs, 'head', head, SN[st])
    want = ([(1, 17), (0, 1), (1, 31), (0, 2), (1, 4)]
            + [(0, 1), (1, 2)] * (be - 2))
    assert runs == want and head == 50 and st == B, \
        'X%d shape mismatch vs post-exit-analysis S1' % be
    print('OK  X%d shape == 1^17 0 1^31 0^2 1^4 (0 1^2)^%d, head B@50'
          % (be, be - 2))

if FAILS:
    print('FAILURES:', FAILS)
    sys.exit(1)

# ---- emit Configs.v ------------------------------------------------------
def rep(b, n):
    return 'repeat %s %d' % ('true' if b else 'false', n)


def emit_list(runs):
    if not runs:
        return '[]'
    return '(' + ' ++ '.join(rep(b, n) for b, n in runs) + ')'


out = []
out.append('(* Phase 23 -- concrete configurations for the finite-segment')
out.append('   checks, generated by gen_configs.py from the documents\'')
out.append('   closed forms (S/S\' walls, D(132,66), R, formation endpoint,')
out.append('   sigma_re) and, for the H (beta = 2) and X (exit successor)')
out.append('   configurations, from the verified simulator at the documented')
out.append('   steps T(4) = 102, T(8) = 2850 (+6).  A configuration is a')
out.append('   zipper (state, left, right); left is nearest-first. *)')
out.append('Require Import List.')
out.append('Import ListNotations.')
out.append('Require Import TM.')
out.append('')

for name in ('blank', 'S2', 'S4', 'Sp2', 'Sp4', 'Sp6', 'D132', 'R',
             'Isec', 'sre4', 'sre8', 'H4', 'X4', 'H8', 'X8'):
    runs, head, st = CFG[name]
    cells = runs_cells(runs)
    left = cells[:head][::-1]
    right = cells[head:]

    def rle_of(lst):
        rr = []
        for v in lst:
            if rr and rr[-1][0] == v:
                rr[-1][1] += 1
            else:
                rr.append([v, 1])
        return [tuple(r) for r in rr]

    out.append('Definition cfg_%s : config := mkCfg %s %s %s.'
               % (name, SN[st], emit_list(rle_of(left)),
                  emit_list(rle_of(right))))
    out.append('')

with open('Configs.v', 'w') as fh:
    fh.write('\n'.join(out))
print('Configs.v written')
