#!/usr/bin/env python3
"""
reproduce_168016.py — independent reproduction checker for the proof that
bbchallenge BB(6) machine #168016 does not halt.

Machine:  1RB1RA_1RC1LB_0LD0RA_1RF1LE_---1LF_1LC0LF
          (halts iff state E reads 0)

CLEAN-ROOM STATEMENT.  This file was written from scratch for Phase 22.
It imports NO code from the earlier phases (no phase*.py / phase*.c model
or simulator is used, read, or required).  Its only inputs are:

  * the transition table above (the machine spec), and
  * the proof documents in this directory, used as the specification:
      168016-proof.md            (theorem + component list)
      proof-168016.md            (S family, A.1 arrival table)
      postbreak-168016.md        (S' arrival table, transient record)
      sprime-phases-168016.md, phase2-complete.md, m132-analysis.md
                                 (S' periods, m = 132 break, D(132,66))
      post-R-proof.md            (halt criterion M1-M4, formation)
      bounce-derivation.md       (five standard rules + invariant I)
      reexpansion-derivation.md  (Stage A)
      rightedge-derivation.md    (five mirror rules, ENTRY)
      token-pass-derivation.md   (Cycle Lemma, T(beta_E))
      post-exit-analysis.md      (exit successor X, segment costs)
      phase19-derivations.md     (REGEN, era law s1 = 2 beta_E + 31)
      phase20-derivations.md     (probe prefix, POP2, ESC family)
      phase21-derivations.md     (PUSHX, PX2A, PX2B, TRANS2/TUP2, CGAP2)
  * ONE disclosed exception: three reference checkpoints for the run out
    of R are read as *data* from phase10-expected.txt (the dump file the
    original Phase 10 produced; third-family.md asserts 303/303 of its
    dumps matched).  No code is taken from it, and no other check depends
    on it.

WHAT IT CHECKS (details in reproduction-report.md):
  A. the documents' arithmetic: arrival tables vs the period law,
     component step sums, the D(132,66) closed form, headline numbers;
  B. finite segments by direct simulation with a fresh exact simulator
     (blank tape -> S(k) arrivals, isolated S and S' periods,
     D(132,66) -> R, R -> formation, R continuation checkpoints);
  C. the derived rule systems as executable word-level maps, checked
     rule-by-rule against the step simulator on fresh batteries
     (including held-out parameter values);
  D. the token pass: Cycle Lemma durations, min-beta law, T(beta_E),
     and the exit successor X(beta_E), model + machine;
  E. the re-coordinatisation segment X -> canonical section;
  F. the era: machine classification of the beta_E = 6 era, word-model
     era evaluation at held-out beta_E, the ESC escape family;
  G. the loop ascent (beta strictly increases, s_regen + 3 > beta).

Every simulation carries the event audit of post-R-proof.md:
E-on-0 reads (a halt), D-on-0 reads, C-on-0 entry contexts, and
F-on-0 left triples watched for the halting pattern (0,1,0) (M4).

Run:  python3 reproduce_168016.py            (full suite, ~2-3 minutes)
      python3 reproduce_168016.py --quick    (skips the three longest
                                              direct simulations)
Exit code 0 iff no check FAILs.  FINDINGs (document discrepancies that do
not touch the theorem) are reported, not hidden.
"""

import sys
import time

SPEC = "1RB1RA_1RC1LB_0LD0RA_1RF1LE_---1LF_1LC0LF"
QUICK = "--quick" in sys.argv

# --------------------------------------------------------------------------
# Transition table, parsed from the spec string (bbchallenge format).
# --------------------------------------------------------------------------
def parse_spec(spec):
    tr = []
    for blk in spec.split('_'):
        for v in (0, 1):
            s = blk[3 * v:3 * v + 3]
            if s[0] == '-':
                tr.append((-1, 0, -1))          # halting transition
            else:
                tr.append((int(s[0]), 1 if s[1] == 'R' else -1,
                           ord(s[2]) - 65))
    return tr

TR = parse_spec(SPEC)
W_ = [t[0] for t in TR]     # write
M_ = [t[1] for t in TR]     # move
N_ = [t[2] for t in TR]     # next state
SN = "ABCDEF"
A, B, C, D, E, F = range(6)

# --------------------------------------------------------------------------
# Exact step simulator with event audit (fresh implementation).
# Tape: bytearray with a movable origin; grows on demand.
# --------------------------------------------------------------------------
class Sim:
    __slots__ = ("tape", "off", "h", "st", "steps", "last_move", "cnt",
                 "d0", "e0", "danger", "c_ctx", "c_entry", "halted",
                 "vmin", "vmax")

    def __init__(self, cells=(), head=0, state=0):
        self.off = 2048
        self.tape = bytearray(8192)
        for i, b in enumerate(cells):
            self.tape[self.off + i] = b
        self.h = self.off + head
        # The visited window must cover the whole placed tape: the head
        # may never visit the left part of a block it sits in.
        self.vmin = self.off if cells else self.h
        self.vmax = self.off + len(cells) - 1 if cells else self.h
        self.st = state
        self.steps = 0
        self.last_move = 0
        self.cnt = [0] * 12          # reads per (state, value)
        self.d0 = 0                  # D-on-0 reads
        self.e0 = 0                  # E-on-0 reads (== halts)
        self.danger = 0              # F-on-0 with left triple (0,1,0)
        self.c_ctx = []              # C-on-0 entry contexts (entry, l1, l2)
        self.c_entry = None
        self.halted = False

    def _grow(self):
        old = self.tape
        n = len(old) * 2
        self.tape = bytearray(n)
        shift = n // 2 - self.off
        self.tape[shift:shift + len(old)] = old
        self.off += shift
        self.h += shift
        self.vmin += shift
        self.vmax += shift

    def step(self):
        h = self.h
        if h < 64 or h >= len(self.tape) - 64:
            self._grow()
            h = self.h
        st = self.st
        idx = st * 2 + self.tape[h]
        self.cnt[idx] += 1
        if idx == 6:                       # D on 0
            self.d0 += 1
        elif idx == 8:                     # E on 0 -> halt
            self.e0 += 1
            self.halted = True
            return False
        elif idx == 10:                    # F on 0: M4 watch
            t = self.tape
            if t[h - 3] == 0 and t[h - 2] == 1 and t[h - 1] == 0:
                self.danger += 1
        elif idx == 4:                     # C on 0: entry context
            t = self.tape
            self.c_ctx.append((self.c_entry, t[h - 1], t[h - 2]))
        w = W_[idx]
        self.tape[h] = w
        mv = M_[idx]
        self.h = h + mv
        if self.h < self.vmin:
            self.vmin = self.h
        elif self.h > self.vmax:
            self.vmax = self.h
        self.last_move = mv
        nst = N_[idx]
        if nst == 2:                       # entering C: remember from where
            self.c_entry = 'B' if idx == 2 else ('F' if idx == 10 else '?')
        self.st = nst
        self.steps += 1
        return True

    def run(self, n):
        for _ in range(n):
            if not self.step():
                return False
        return True

    def span(self):
        # Nonblank span (extended to the head), found by trimming the
        # visited window [vmin, vmax]; cells outside it are blank.
        t = self.tape
        lo, hi = self.vmin, self.vmax
        while lo < self.h and t[lo] == 0:
            lo += 1
        while hi > self.h and t[hi] == 0:
            hi -= 1
        return lo, hi

    def runs(self):
        """(runs, head_rel): run-length list over the nonblank span
        (extended to include the head), head position relative to it."""
        lo, hi = self.span()
        out = []
        cur = self.tape[lo]
        n = 0
        for i in range(lo, hi + 1):
            if self.tape[i] == cur:
                n += 1
            else:
                out.append((cur, n))
                cur = self.tape[i]
                n = 1
        out.append((cur, n))
        return out, self.h - lo

    def snapshot(self):
        runs, hrel = self.runs()
        return (SN[self.st], hrel, tuple(runs))

    def is_section_boundary(self):
        """Current configuration is a head local minimum: arrived moving
        left, next step moves right."""
        if self.last_move != -1:
            return False
        idx = self.st * 2 + self.tape[self.h]
        return M_[idx] == 1

    def next_section(self):
        """Advance to the next head local minimum; return steps taken,
        or -1 on halt."""
        n = 0
        while True:
            if n > 0 and self.is_section_boundary():
                return n
            if not self.step():
                return -1
            n += 1

# --------------------------------------------------------------------------
# Section parsers.  A frame section is (form, pb, a, s, w, r, G):
#   tape  [1^b 0]_pb  1^a 0^{w0} 1^s  prod(0^{wi} 1^{ri})  0^G 1^2
#   form 'B': head on the first cell after block a (position x);
#   form 'C': head at x - 2.  G is None when the tape ends after the
#   last pair / shuttle (degenerate configurations).
# A right-section is (form, pb, beta, w, r):
#   tape  [1^b 0]_pb  1^beta  prod(0^{wi} 1^{ri})   (ends with a run)
# --------------------------------------------------------------------------
def _tail_parse(items):
    """items: runs after the shuttle.  Returns (gaps, runs, G) or None."""
    G = None
    items = list(items)
    if len(items) >= 2 and items[-1] == (1, 2) and items[-2][0] == 0:
        G = items[-2][1]
        items = items[:-2]
    elif len(items) >= 1 and items[-1][0] == 0:
        G = items[-1][1]
        items = items[:-1]
    if len(items) % 2 != 0:
        return None
    gaps, runs = [], []
    for i in range(0, len(items), 2):
        if items[i][0] != 0 or items[i + 1][0] != 1:
            return None
        gaps.append(items[i][1])
        runs.append(items[i + 1][1])
    return gaps, runs, G

def parse_frame(sim):
    runs, hrel = sim.runs()
    starts = []
    p = 0
    for v, n in runs:
        starts.append(p)
        p += n
    blocks = [i for i, (v, n) in enumerate(runs) if v == 1]
    form = SN[sim.st]
    if form not in ('B', 'C'):
        return None
    j = None
    a = None
    for oi, bi in enumerate(blocks):
        e = starts[bi] + runs[bi][1] - 1
        if form == 'B' and e + 1 == hrel:
            j, a = oi, runs[bi][1]
            break
        if form == 'C' and e - 1 == hrel:
            j, a = oi, runs[bi][1]
            break
    if j is None:
        if form != 'B':
            return None
        # a == 0: head on the blank cell after (separator, empty block)
        for oi, bi in enumerate(blocks):
            e = starts[bi] + runs[bi][1] - 1
            if e + 2 == hrel:
                j, a = oi, 0
                break
        if j is None:
            return None
        pb = tuple(runs[b][1] for b in blocks[:j + 1])
        gi = None
        for i, (v, n) in enumerate(runs):
            if v == 0 and starts[i] <= hrel < starts[i] + n:
                gi = i
                break
        if gi is None or gi + 1 >= len(runs):
            return None
        g0 = runs[gi][1] - 1                    # minus the separator cell
        rest = runs[gi + 1:]
        if rest[0][0] != 1:
            return None
        tp = _tail_parse(rest[1:])
        if tp is None:
            return None
        gaps, rs, G = tp
        return (form, pb, 0, rest[0][1], [g0] + gaps, rs, G)
    pb = tuple(runs[b][1] for b in blocks[:j])
    rest = runs[blocks[j] + 1:]
    if len(rest) < 2 or rest[0][0] != 0 or rest[1][0] != 1:
        return None
    tp = _tail_parse(rest[2:])
    if tp is None:
        return None
    gaps, rs, G = tp
    return (form, pb, a, rest[1][1], [rest[0][1]] + gaps, rs, G)

def parse_right(sim):
    runs, hrel = sim.runs()
    starts = []
    p = 0
    for v, n in runs:
        starts.append(p)
        p += n
    blocks = [i for i, (v, n) in enumerate(runs) if v == 1]
    form = SN[sim.st]
    if form not in ('B', 'C'):
        return None
    for oi, bi in enumerate(blocks):
        e = starts[bi] + runs[bi][1] - 1
        if (form == 'C' and e - 1 == hrel) or (form == 'B' and e + 1 == hrel):
            rest = runs[bi + 1:]
            if len(rest) % 2 != 0:
                return None
            w, r = [], []
            for i in range(0, len(rest), 2):
                if rest[i][0] != 0 or rest[i + 1][0] != 1:
                    return None
                w.append(rest[i][1])
                r.append(rest[i + 1][1])
            return (form, tuple(runs[b][1] for b in blocks[:oi]),
                    runs[bi][1], w, r)
    return None

def cells_of_frame(pb, a, s, w, r, G):
    cells = []
    for b in pb:
        cells += [1] * b + [0]
    cells += [1] * a + [0] * w[0] + [1] * s
    for gi, ri in zip(w[1:], r):
        cells += [0] * gi + [1] * ri
    if G is not None:
        cells += [0] * G + [1] * 2
    return cells

def sim_of_frame(sec):
    form, pb, a, s, w, r, G = sec
    cells = cells_of_frame(pb, a, s, w, r, G)
    x = sum(b + 1 for b in pb) + a
    head = x if form == 'B' else x - 2
    return Sim(cells, head, B if form == 'B' else C)

def cells_of_right(pb, beta, w, r):
    cells = []
    for b in pb:
        cells += [1] * b + [0]
    cells += [1] * beta
    for gi, ri in zip(w, r):
        cells += [0] * gi + [1] * ri
    return cells

def sim_of_right(sec):
    form, pb, beta, w, r = sec
    cells = cells_of_right(pb, beta, w, r)
    x = sum(b + 1 for b in pb) + beta
    head = x if form == 'B' else x - 2
    return Sim(cells, head, B if form == 'B' else C)

# --------------------------------------------------------------------------
# Word-level models, implemented from the derivation documents.
# frame_step(sec) -> (successor, cost, rule_name) or None.
# Sections: (form, pb, a, s, w, r, G); w[0] is the gap after block a,
# pairs are (w[i], r[i-1]) for i >= 1.
# --------------------------------------------------------------------------
def frame_step(sec):
    form, pb, a, s, w, r, G = sec
    if form == 'C':
        if s != 2:
            return None
        g0 = w[0]
        if g0 == 1:                                   # TDN (Bounce §4.1)
            return (('B', pb, a - 2, s + 2, w, r, G), 6, 'TDN')
        if g0 == 2:                                   # CGAP2 (Phase 21 §5)
            return cgap2(sec)
        # g0 >= 3: PUSH family
        if a >= 3:                                    # PUSH (Bounce §4.3)
            return (('C', pb, a - 1, 2, [1, g0 - 2] + w[1:], [s] + r, G),
                    9, 'PUSH')
        if a == 2:
            if len(pb) == 0:                          # PUSHX (Phase 20 §4.1)
                # Documented landing (B, 1, g0 + 4, W, R, G), cost 33.
                # Phase 22 measurement (C7) fixes the notation: the
                # landing gap word is [1] + W with R intact (the merged
                # run's POP writes the new g0 = 1 cell; no pair is
                # consumed).  Era sources always have g0 = 3
                # (predecessor lemma, Phase 21 §2).
                if g0 != 3:
                    return None
                return (('B', pb, 1, g0 + 4, [1] + w[1:], r, G), 33, 'PUSHX')
            if len(pb) == 1:                          # PX2B (Phase 21 §3)
                return px2b(sec)
            return px2a(sec)                          # PX2A (Phase 21 §3)
        return None
    # form == 'B'
    if len(w) == 1:
        if G is None:
            return None
        if G >= 3:                                    # Stage A (Reexp. §2)
            return (('C', pb, a + 2, 2, [s - 1], [], G - 2), 2 * s + 6, 'STGA')
        if G == 1:                                    # REGEN (Phase 19 §1)
            return (('C', pb, a + 2, 2, [1], [], s - 1), 4 * s + 22, 'REGEN')
        # G == 2: ENTRY (Rightedge §3) -> mirror frame; marker successor
        return (('ENTRY', pb, a, s, w, r, G), s + 12, 'ENTRY')
    g1 = w[1]
    if g1 == 1:                                       # POP-general (§4.2/19)
        return (('B', pb, a + 1, s + r[0], w[1:], r[1:], G), 2 * s + 3, 'POP')
    if g1 == 2:                                       # TRANS2 (Phase 21 §4)
        return trans2(sec)
    # g1 >= 3: TUP (Bounce §4.4)
    return (('C', pb, a + 2, 2, [s - 1, g1 - 2] + w[2:], r, G), 2 * s + 6, 'TUP')

def trans2(sec):
    form, pb, a, s, w, r, G = sec
    # chain of gap-2 pairs 1..k (pair i: gap w[i], run r[i-1])
    k = 0
    while k + 1 < len(w) and w[k + 1] == 2:
        k += 1
    if k == 0 or k + 1 >= len(w):
        return None                    # chain-end forms: not exercised here
    base = (s + 2) + sum(r[i] + 2 for i in range(k))
    rk = r[k - 1]
    if k == 1:
        gains = [a + 1]
        a_turn, a_probe = s + 1, s + 2
    else:
        gains = [a + 1, s + 1] + [r[i] + 1 for i in range(k - 2)]
        a_turn, a_probe = r[k - 2] + 1, r[k - 2] + 2
    if w[k + 1] == 1:                                 # turn (k=1: POP2)
        return (('B', pb + tuple(gains), a_turn, rk + r[k],
                 [1] + w[k + 2:], r[k + 1:], G), base + rk + 1, 'TRANS2-turn')
    if w[k + 1] >= 3:                                 # probe (TUP2)
        w0p = rk - 1 if rk >= 2 else 1
        return (('C', pb + tuple(gains), a_probe, 2,
                 [w0p, w[k + 1] - 2] + w[k + 2:], r[k - 1:], G),
                base + rk + 4, 'TUP2')
    return None

def px2a(sec):
    form, pb, a, s, w, r, G = sec
    b, p = pb[-1], pb[-2]
    W, R = w[1:], r
    if b == 2:
        return (('B', pb[:-2], p - 1, 5, [1, 1, 1] + W, [2, 2] + R, G),
                23, 'PX2A-b2')
    return (('C', pb[:-2], p + 1, 2, [b - 2, 1, 1, 1] + W, [1, 2, 2] + R, G),
            b + 11, 'PX2A')

def px2b(sec):
    form, pb, a, s, w, r, G = sec
    b = pb[-1]
    W, R = w[1:], r
    if b == 2:
        return (('B', (), 1, 8, [1, 1] + W, [2] + R, G), 43, 'PX2B')
    if b == 3:
        return (('B', (), 1, 6, [1, 1, 1] + W, [2, 2] + R, G), 38, 'PX2B')
    if b == 4:
        return (('B', (), 4, 3, [1, 1, 1] + W, [2, 2] + R, G), 29, 'PX2B')
    if b == 5:
        return (('B', (), 4, 4, [1, 1, 1, 1] + W, [1, 2, 2] + R, G), 44, 'PX2B')
    if b == 6:
        return (('B', (4,), 3, 3, [1, 1, 1] + W, [2, 2] + R, G), 49, 'PX2B')
    return (('C', (), 5, 2, [1, b - 6, 1, 1, 1] + W, [2, 1, 2, 2] + R, G),
            b + 42, 'PX2B')

def cgap2(sec):
    """CGAP2 (Phase 21 §5): C-section with w0 = 2.  Only the two
    dispatches are modelled, exactly as documented (C-POP total 10,
    C-PUSH total 13).  The probe chain (w1 = 2) is NOT modelled: the
    document gives only a recursive description of it, and Phase 22
    probes it separately (see check C11 and reproduction-report.md)."""
    form, pb, a, s, w, r, G = sec
    if w[1] == 2:
        return None
    pb2 = pb + ((a - 2,) if a > 2 else ())
    if w[1] == 1:                                   # C-POP: probe 4 + 6
        return (('B', pb2, 3, r[0] + 2, [1] + w[2:], r[1:], G), 10, 'CGAP2')
    # w[1] >= 3: C-PUSH: probe 4 + 9
    return (('C', pb2, 4, 2, [1, w[1] - 2] + w[2:], r, G), 13, 'CGAP2')

# Mirror model (rightedge-derivation.md §2).  Section: (form, pb, beta, w, r)
# with len(w) == len(r); the word ends with a run.
def mirror_step(sec):
    form, pb, beta, w, r = sec
    if form == 'C':
        if w[0] == 1:                                 # RTDN
            return (('B', pb, beta - 2, w, [r[0] + 2] + r[1:]), 6, 'RTDN')
        if w[0] >= 3:                                 # RPUSH
            return (('C', pb, beta - 1, [1, w[0] - 2] + w[1:], [2] + r),
                    9, 'RPUSH')
        return None
    # form == 'B' (first gap is 1 by invariant RI)
    if len(w) == 1:                                   # RPROBE
        return (('C', pb, beta + 2, [r[0] - 1], [2]), 2 * r[0] + 6, 'RPROBE')
    if w[1] == 1:                                     # RPOP
        return (('B', pb, beta + 1, [1] + w[2:], [r[0] + r[1]] + r[2:]),
                2 * r[0] + 3, 'RPOP')
    if w[1] >= 3:                                     # RTUP
        return (('C', pb, beta + 2, [r[0] - 1, w[1] - 2] + w[2:], [2] + r[1:]),
                2 * r[0] + 6, 'RTUP')
    return None

# --------------------------------------------------------------------------
# Classification driver: model predicts each successor section + cost;
# the step simulator must land exactly there.
# Returns (n_classified, mismatch_detail or None, rule_counts, sim).
# --------------------------------------------------------------------------
def classify(sim, sec, model, parser, max_sections, stop=None):
    counts = {}
    cur = sec
    n = 0
    while n < max_sections:
        if stop is not None and stop(cur):
            break
        pred = model(cur)
        if pred is None:
            return n, f"model has no rule at {cur}", counts, sim
        succ, cost, rule = pred
        if succ[0] == 'ENTRY':
            # verify the ENTRY excursion against the mirror frame
            if not sim.run(cost):
                return n, "halt during ENTRY", counts, sim
            got = parse_right(sim)
            want = ('C', cur[1] + (cur[2] + 1,), cur[3] + 2, [1], [2])
            counts[rule] = counts.get(rule, 0) + 1
            n += 1
            if got != want:
                return n, f"ENTRY landing {got} != {want}", counts, sim
            return n, None, counts, sim
        if not sim.run(cost):
            return n, f"halt during {rule} from {cur}", counts, sim
        if not sim.is_section_boundary():
            return n, (f"{rule} from {cur}: after {cost} steps the "
                       f"configuration is not a section boundary"), counts, sim
        got = parser(sim)
        if got != succ:
            return n, f"{rule} from {cur}: landing {got} != predicted {succ}", counts, sim
        counts[rule] = counts.get(rule, 0) + 1
        cur = succ
        n += 1
    return n, None, counts, sim

# --------------------------------------------------------------------------
# Result bookkeeping
# --------------------------------------------------------------------------
RESULTS = []

def check(name, ok, detail=""):
    RESULTS.append((name, "PASS" if ok else "FAIL", detail))
    print(f"[{'PASS' if ok else 'FAIL'}] {name}" + (f" — {detail}" if detail else ""))

def finding(name, detail):
    RESULTS.append((name, "FINDING", detail))
    print(f"[FINDING] {name} — {detail}")

# ==========================================================================
# PART A — the documents' arithmetic, recomputed from the stated components
# ==========================================================================
def P(k):
    """Period law (proof-168016.md A.3 / sprime-phases-168016.md B):
    S(m) -> S(m+2) and S'(m) -> S'(m+2) in 3*2^((m+4)/2) - 6 steps."""
    return 3 * 2 ** ((k + 4) // 2) - 6

def part_a():
    print("\n=== PART A: arithmetic cross-checks ===")
    # A.1 arrival table (proof-168016.md A.1), embedded from the document.
    a1 = {2: 197317, 4: 197335, 6: 197377, 8: 197467, 10: 197653,
          12: 198031, 14: 198793, 16: 200323, 18: 203389, 20: 209527,
          22: 221809, 24: 246379, 26: 295525, 28: 393823, 30: 590425,
          32: 983635, 34: 1770061, 36: 3342919, 38: 6488641, 40: 12780091,
          42: 25362997, 44: 50528815, 46: 100860457, 48: 201523747,
          50: 402850333, 52: 805503511, 54: 1610809873, 56: 3221422603}
    bad = [k for k in sorted(a1) if k >= 4 and a1[k] - a1[k - 2] != P(k - 2)]
    check("A1: A.1 table differences == period law P(k)", not bad,
          f"28 arrivals, first S(2) at 197,317; mismatches at k={bad}")
    # S' arrival table (postbreak-168016.md B): gaps == P(m-2) as well.
    sp = {2: 57982256713, 4: 57982256731, 6: 57982256773, 8: 57982256863,
          10: 57982257049, 12: 57982257427, 14: 57982258189, 16: 57982259719,
          18: 57982262785, 20: 57982268923, 22: 57982281205, 24: 57982305775,
          26: 57982354921, 28: 57982453219, 30: 57982649821, 32: 57983043031,
          34: 57983829457, 36: 57985402315, 38: 57988548037, 40: 57994839487,
          42: 58007422393, 44: 58032588211, 46: 58082919853, 48: 58183583143,
          50: 58384909729, 52: 58787562907, 54: 59592869269, 56: 61203481999,
          58: 64424707465, 60: 70867158403, 62: 83752060285, 64: 109521864055,
          66: 161061471601, 68: 264140686699}
    bad = [m for m in sorted(sp) if m >= 4 and sp[m] - sp[m - 2] != P(m - 2)]
    check("A2: S' arrival table differences == period law P(m)", not bad,
          f"34 arrivals from S'(2) at 57,982,256,713; mismatches at m={bad}")
    # S'(132) arrival = S'(2) arrival + sum of proven period costs m <= 130.
    arr132 = sp[2] + sum(P(m) for m in range(2, 132, 2))
    check("A3: S'(132) arrival recomputed == 885,443,715,596,040,733,867",
          arr132 == 885443715596040733867, f"got {arr132:,}")
    # m = 132 period to D(132,66) (m132-analysis.md §3).
    per_d = 3 + 133 + (3 * 2**68 - 9319)
    check("A4: period offset of D(132,66) == 3*2^68 - 9183",
          per_d == 3 * 2**68 - 9183 == 885443715538058468385,
          f"{per_d:,}")
    d_step = arr132 + per_d
    check("A5: D(132,66) real step == 1,770,887,431,134,099,202,252",
          d_step == 1770887431134099202252, f"got {d_step:,}")
    r_step = d_step + 403455
    check("A6: R real step == 1,770,887,431,134,099,605,707",
          r_step == 1770887431134099605707, f"got {r_step:,}")
    # D(132,66) closed form (m132-analysis.md §3): span 246, 178 ones.
    d_runs = [(1, 4), (0, 1), (1, 41), (0, 1), (1, 1)] + [(0, 1), (1, 2)] * 65 \
        + [(0, 1), (1, 2)]
    ones = sum(n for v, n in d_runs if v == 1)
    span = sum(n for v, n in d_runs)
    check("A7: D(132,66) closed form: span 246, 178 ones, head cell 46 is 0",
          span == 246 and ones == 178, f"span {span}, ones {ones}")
    # The printed finite corollary vs its components.
    printed = 1770888448134502657707
    addend = printed - r_step
    if addend == 1017000403052000 and addend == 1000 * 1017000403052:
        finding("A8: finite corollary bound (168016-proof.md, end)",
                f"printed bound {printed:,} minus R step {r_step:,} = "
                f"{addend:,} = exactly 1000 x 1,017,000,403,052, while "
                f"third-family.md §§3-4 and NOTES.md (Phase 10) state the "
                f"isolated run from R had reached ~1.017e12 steps.  A x1000 "
                f"slip in the corollary's last addend; the corrected bound "
                f"is {r_step + 1017000403052:,}.  Both values round to "
                f"~1.7709e21 and the theorem does not use the corollary.")
    else:
        check("A8: finite corollary bound recomputed from components",
              False, f"printed - R step = {addend:,}")
    # Cycle-sum closed form (token-pass-derivation.md §6).
    ok = all(sum(3 * 2 ** (j + 3) - 4 for j in range(K)) == 3 * 2 ** (K + 3) - 24 - 4 * K
             for K in range(0, 31))
    check("A9: sum_{j<K} D_j == 3*2^(K+3) - 24 - 4K (K = 0..30)", ok)
    # Settled span identity (post-exit-analysis.md §2): 3 beta_E + 51.
    ok = all(18 + (29 + be) + 2 + (1 + 2 * (be - 1)) + 1 + 2 == 3 * be + 51
             for be in range(4, 42, 2))
    check("A10: canonical section span == 3*beta_E + 51 (arithmetic)", ok)

# ==========================================================================
# PART B — finite segments by direct simulation
# ==========================================================================
def s_config(k, wall=(4, 17, 27)):
    runs = []
    for b in wall:
        runs += [(1, b), (0, 1)]
    runs += [(1, k), (0, 1)]
    cells = []
    for v, n in runs:
        cells += [v] * n
    return cells, len(cells) - 1, tuple(runs)

def part_b():
    print("\n=== PART B: direct simulation of finite segments ===")
    a1 = {2: 197317, 4: 197335, 6: 197377, 8: 197467, 10: 197653,
          12: 198031, 14: 198793, 16: 200323, 18: 203389, 20: 209527,
          22: 221809, 24: 246379, 26: 295525, 28: 393823, 30: 590425,
          32: 983635, 34: 1770061, 36: 3342919, 38: 6488641, 40: 12780091,
          42: 25362997, 44: 50528815}
    # B1: blank tape -> S(k) arrivals, exact configuration at each step.
    sim = Sim()
    done = 0
    ok = True
    detail = ""
    for k in sorted(a1):
        if not sim.run(a1[k] - done):
            ok, detail = False, f"halted before S({k})"
            break
        done = a1[k]
        cells, head, runs = s_config(k)
        want = ('B', head, runs)
        got = sim.snapshot()
        if got != want:
            ok, detail = False, f"S({k}) at step {done}: got {got}, want {want}"
            break
    check("B1: blank tape -> S(k) exact arrivals, k = 2..44", ok,
          detail or f"23 arrivals matched to the step; audit E-on-0 = {sim.e0}, "
                    f"D-on-0 = {sim.d0} (wall-building transient)")
    if not QUICK:
        # B2: isolated S(48) -> S(50), one full period at larger k.
        cells, head, _ = s_config(48)
        sim = Sim(cells, head, B)
        sim.run(P(48))
        cells, head, runs = s_config(50)
        check("B2: isolated S(48) -> S(50) in P(48) = 100,663,290 steps",
              sim.snapshot() == ('B', head, runs) and sim.e0 == 0,
              f"audit E-on-0 = {sim.e0}")
    # B3: S' chain from synthetic S'(2), m = 2 -> 30, then isolated 44 -> 46.
    wall = (4, 41, 65)
    cells, head, _ = s_config(2, wall)
    sim = Sim(cells, head, B)
    ok = True
    detail = ""
    for m in range(2, 30, 2):
        if not sim.run(P(m)):
            ok, detail = False, f"halted in S' period m={m}"
            break
        cells2, head2, runs2 = s_config(m + 2, wall)
        if sim.snapshot() != ('B', head2, runs2):
            ok, detail = False, f"S'({m + 2}) mismatch"
            break
    check("B3: synthetic S'(2) -> S'(30), 14 consecutive periods", ok,
          detail or "each period exactly P(m) steps, exact tape")
    if not QUICK:
        cells, head, _ = s_config(44, wall)
        sim = Sim(cells, head, B)
        sim.run(P(44))
        cells, head, runs = s_config(46, wall)
        check("B4: isolated S'(44) -> S'(46) in P(44) = 50,331,642 steps",
              sim.snapshot() == ('B', head, runs) and sim.e0 == 0, "")
    # B5: D(132,66) -> R in 403,455 steps; first step is the deviation.
    d_runs = [(1, 4), (0, 1), (1, 41), (0, 1), (1, 1)] + [(0, 1), (1, 2)] * 65 \
        + [(0, 1), (1, 2)]
    cells = []
    for v, n in d_runs:
        cells += [v] * n
    sim = Sim(cells, 46, C)
    first = sim.step() and sim.st == D and sim.cnt[4] == 1
    sim.run(403455 - 1)
    r_runs = ((1, 17), (0, 1), (1, 97), (0, 1), (1, 137), (0, 1))
    got = sim.snapshot()
    check("B5: D(132,66) -> R in exactly 403,455 steps",
          first and got == ('B', 253, r_runs) and sim.e0 == 0,
          f"first step C-on-0 -> D (the m=132 deviation); audit E-on-0 = {sim.e0}, "
          f"D-on-0 total = {sim.d0}")
    # B6: R -> first I-section in exactly 150 steps (formation).
    r_cells = []
    for v, n in r_runs:
        r_cells += [v] * n
    sim = Sim(r_cells, 253, B)
    sim.run(150)
    sec = parse_frame(sim)
    want = ('C', (17,), 97, 2, [1], [], 134)
    ctx_ok = sim.c_ctx == [('B', 1, 1), ('B', 1, 1)]
    check("B6: R -> formation: first I-section at step 150",
          sec == want and ctx_ok and sim.cnt[9] == 2 and sim.cnt[7] == 2
          and sim.danger == 0 and sim.e0 == 0,
          f"section {sec}; C-on-0 contexts {sim.c_ctx} (both B-entry (1,1)); "
          f"E-on-1 reads {sim.cnt[9]}, D-on-1 reads {sim.cnt[7]}, M4 danger {sim.danger}")
    # B7: R continuation checkpoints (reference data: phase10-expected.txt,
    # first three dumps; disclosed in the header).
    try:
        dumps = []
        with open("phase10-expected.txt") as fh:
            for line in fh:
                parts = line.split()
                if len(parts) < 5:
                    continue
                runs = tuple((int(x.split(':')[0]), int(x.split(':')[1]))
                             for x in parts[4].split(','))
                dumps.append((int(parts[0]), parts[1], int(parts[2]),
                              int(parts[3]), runs))
                if len(dumps) == 3:
                    break
        sim = Sim(r_cells, 253, B)
        done = 0
        ok = True
        detail = ""
        for step, st, hd, ones, runs in dumps:
            if not sim.run(step - done):
                ok, detail = False, f"halted before dump at {step}"
                break
            done = step
            got_runs, got_h = sim.runs()
            got_ones = sum(n for v, n in got_runs if v == 1)
            if (SN[sim.st], got_h, got_ones, tuple(got_runs)) != (st, hd, ones, runs):
                ok, detail = False, f"dump at {step}: got {(SN[sim.st], got_h, got_ones)}, want {(st, hd, ones)}"
                break
        check("B7: R continuation matches phase10 dumps at 596,545 / "
              "9,596,545 / 99,596,545 steps", ok,
              detail or f"state/head/ones/full run list exact at all three; "
                        f"audit E-on-0 = {sim.e0}")
    except FileNotFoundError:
        check("B7: R continuation dumps", False, "phase10-expected.txt not found")

# ==========================================================================
# PART C — rule batteries: word model vs step simulator, fresh parameters
# ==========================================================================
def excursion(sec, want, cost, label, audit=None):
    """Run one model excursion of exactly `cost` steps from section `sec`
    and compare the landing section."""
    sim = sim_of_frame(sec)
    if not sim.run(cost):
        check(label, False, "halted mid-excursion")
        return
    got = parse_frame(sim)
    ok = got == want and sim.is_section_boundary()
    det = f"{sec} -> {got} in {cost} steps (want {want})"
    if audit:
        det += "; " + audit(sim)
    check(label, ok, det)

def part_c():
    print("\n=== PART C: rule-system batteries (fresh parameters) ===")
    # C1-C3: chained classification in the two-block frame (grind-like
    # configurations; 300 consecutive sections each).
    chains = [
        (('C', (17,), 40, 2, [1, 15, 1, 1], [2, 1, 2], 9), "C1"),
        (('C', (17,), 26, 2, [1, 21, 1], [2, 4], 5), "C2"),
        (('B', (17,), 30, 9, [1, 1, 3, 1], [2, 6, 2], 12), "C3"),
    ]
    for sec0, label in chains:
        sim = sim_of_frame(sec0)
        n, err, counts, _ = classify(sim, sec0, frame_step, parse_frame, 300)
        check(f"{label}: 300 consecutive sections classified (two-block frame)",
              err is None and n == 300,
              f"classified {n}; rules {counts}; {err or ''}audit E-on-0 = {sim.e0}, "
              f"M4 danger = {sim.danger}")
    # C4: Stage A at a fresh point.
    excursion(('B', (17,), 11, 14, [1], [], 8),
              ('C', (17,), 13, 2, [13], [], 6), 34, "C4: STGA (a=11, s=14, G=8)")
    # C5: REGEN at held-out (a, s), with the two intermediate checkpoints
    # of phase19-derivations.md §1 (merged B at 2s+3, degenerate C at 4s+13).
    for (a, s) in [(7, 8), (12, 15), (6, 21)]:
        sim = sim_of_frame(('B', (), a, s, [1], [], 1))
        sim.run(2 * s + 3)
        mid1 = parse_frame(sim)
        sim.run(2 * s + 10)
        mid2 = parse_frame(sim)
        sim.run(9)
        fin = parse_frame(sim)
        ok = (mid1 == ('B', (), a + 1, s + 2, [1], [], None)
              and mid2 == ('C', (), a + 3, 2, [s + 1], [], None)
              and fin == ('C', (), a + 2, 2, [1], [], s - 1)
              and sim.danger == 0 and sim.e0 == 0)
        check(f"C5: REGEN (a={a}, s={s}), cost {4 * s + 22} with checkpoints",
              ok, f"checkpoints {mid1}, {mid2}; landing {fin}")
    # C6: ENTRY at fresh points -> sigma_re in the mirror frame.
    for (a, s) in [(7, 10), (45, 26)]:
        sim = sim_of_frame(('B', (17,), a, s, [1], [], 2))
        sim.run(s + 12)
        got = parse_right(sim)
        want = ('C', (17, a + 1), s + 2, [1], [2])
        check(f"C6: ENTRY (a={a}, s={s}) -> sigma_re({s + 2})",
              got == want and sim.danger == 0, f"landing {got}")
    # C7: PUSHX, including a held-out first-run value r1 = 4.
    excursion(('C', (), 2, 2, [3, 1, 5], [2, 2], 7),
              ('B', (), 1, 7, [1, 1, 5], [2, 2], 7), 33, "C7a: PUSHX (r1=2)",
              audit=lambda sm: f"D-on-0 in excursion = {sm.d0} (want 1)")
    sim = sim_of_frame(('C', (), 2, 2, [3, 1, 5], [2, 2], 7))
    sim.run(33)
    check("C7a': PUSHX D-on-0 count == 1", sim.d0 == 1, f"got {sim.d0}")
    excursion(('C', (), 2, 2, [3, 1, 5], [4, 2], 7),
              ('B', (), 1, 7, [1, 1, 5], [4, 2], 7), 33,
              "C7b: PUSHX (r1=4, held out; s = g + 4 = 7, not 5 + r1)")
    # C8: PX2A at a held-out prefix (p, b) = (6, 11), and the b = 2 form.
    excursion(('C', (6, 11), 2, 2, [3, 1], [2], 5),
              ('C', (), 7, 2, [9, 1, 1, 1, 1], [1, 2, 2, 2], 5), 22,
              "C8a: PX2A (p=6, b=11, held out)")
    excursion(('C', (6, 2), 2, 2, [3, 1], [2], 5),
              ('B', (), 5, 5, [1, 1, 1, 1], [2, 2, 2], 5), 23,
              "C8b: PX2A at b=2")
    # C9: PX2B at held-out b = 11 and b = 15, plus documented b = 4, b = 2.
    excursion(('C', (11,), 2, 2, [3, 1, 5], [2, 2], 5),
              ('C', (), 5, 2, [1, 5, 1, 1, 1, 1, 5], [2, 1, 2, 2, 2, 2], 5), 53,
              "C9a: PX2B (b=11, held out)")
    excursion(('C', (15,), 2, 2, [3, 1], [2], 5),
              ('C', (), 5, 2, [1, 9, 1, 1, 1, 1], [2, 1, 2, 2, 2], 5), 57,
              "C9b: PX2B (b=15, held out)")
    excursion(('C', (4,), 2, 2, [3, 1, 1], [2, 2], 5),
              ('B', (), 4, 3, [1, 1, 1, 1, 1], [2, 2, 2, 2], 5), 29,
              "C9c: PX2B (b=4)")
    excursion(('C', (2,), 2, 2, [3, 1], [2], 5),
              ('B', (), 1, 8, [1, 1, 1], [2, 2], 5), 43,
              "C9d: PX2B (b=2)")
    # C10: TRANS2 family: POP2 (k=1 turn), TUP2 (k=1 probe), k=2 turn.
    excursion(('B', (), 3, 8, [1, 2, 1, 1], [2, 1, 2], 1),
              ('B', (4,), 9, 3, [1, 1], [2], 1), 17, "C10a: POP2 (k=1 turn)")
    excursion(('B', (), 5, 12, [1, 2, 5, 1], [2, 3, 2], 5),
              ('C', (6,), 14, 2, [1, 3, 1], [3, 2], 5), 24, "C10b: TUP2 (k=1 probe)")
    excursion(('B', (), 5, 6, [1, 2, 2, 1, 3], [2, 4, 2, 2], 5),
              ('B', (6, 7), 3, 6, [1, 3], [2], 5), 23, "C10c: TRANS2 turn (k=2)")
    # C11: CGAP2 dispatches at held-out a = 7; then the probe chain probe.
    excursion(('C', (), 7, 2, [2, 1, 3], [3, 2], 5),
              ('B', (5,), 3, 5, [1, 3], [2], 5), 10, "C11a: CGAP2 C-POP (a=7)")
    excursion(('C', (), 7, 2, [2, 4, 1], [3, 2], 5),
              ('C', (5,), 4, 2, [1, 2, 1], [3, 2], 5), 13, "C11b: CGAP2 C-PUSH (a=7)")
    # Probe chain (w = [2, 2, 1, 3]): the document's recursive accounting
    # gives 4 + (r1 + 2) + 6; measure the machine's composed cost at
    # r1 = 2, 3, 5 and compare.
    pts = []
    for r1 in (2, 3, 5):
        sim = sim_of_frame(('C', (), 5, 2, [2, 2, 1, 3], [r1, 2, 2], 5))
        n = sim.next_section()
        pts.append((r1, n, 4 + (r1 + 2) + 6))
    if all(n == 4 + 2 * r1 + 6 for r1, n, doc in pts) and \
            any(n != doc for r1, n, doc in pts):
        finding("C11c: CGAP2 probe-chain cost (phase21-derivations.md §5)",
                f"machine composed cost at r1 = 2, 3, 5 is "
                f"{[n for _, n, _ in pts]} = 4 + 2*r1 + 6; the document's "
                f"recursive accounting (re-probe cost r1 + 2) gives "
                f"{[d for _, _, d in pts]} — it agrees only at r1 = 2. "
                f"Confined to CGAP2, which Phase 21 §6(iii) proves never "
                f"fires in era grinds; the theorem is untouched.")
    else:
        check("C11c: CGAP2 probe-chain cost", False, f"measured {pts}")
    # C12: mirror-rule chains at fresh right-sections.
    for sec0, label in [
            (('C', (17, 43), 11, [5, 1, 3], [2, 2, 4]), "C12a"),
            (('B', (17, 43), 8, [1, 3, 1], [6, 2, 2]), "C12b")]:
        sim = sim_of_right(sec0)
        n, err, counts, _ = classify(sim, sec0, mirror_step, parse_right, 200)
        check(f"{label}: 200 consecutive mirror sections classified",
              err is None and n == 200,
              f"classified {n}; rules {counts}; {err or ''}audit E-on-0 = {sim.e0}, "
              f"M4 danger = {sim.danger}")

# ==========================================================================
# PART D — the token pass: Cycle Lemma, T(beta_E), exit successor X
# ==========================================================================
def model_pass(beta_e):
    """Word-model token pass from S_0(beta_e) = sigma_re.  Returns
    (T, cycles) where T is the step of the first beta = 2 C-section and
    cycles[k] = (D_k, min_beta_C_in_cycle_k, H_k section)."""
    sec = ('C', (17, 31), beta_e, [1], [2])
    total = 0
    cycles = []
    k = 0
    while True:
        # one cycle: run until S_{k+1} = (C, beta_e, [2k+3], [2]) is reached
        cyc_steps = 0
        min_c = sec[2] if sec[0] == 'C' else None
        h_sec = sec if (sec[0] == 'C' and sec[2] == beta_e - k
                        and sec[3] == [1] * (k + 1)
                        and sec[4] == [2] * (k + 1)) else None
        first_c2 = None
        while True:
            pred = mirror_step(sec)
            if pred is None:
                return None, None
            succ, cost, rule = pred
            total += cost
            cyc_steps += cost
            sec = succ
            if sec[0] == 'C':
                if min_c is None or sec[2] < min_c:
                    min_c = sec[2]
                if sec[2] == beta_e - k and sec[3] == [1] * (k + 1) \
                        and sec[4] == [2] * (k + 1):
                    h_sec = sec
                if sec[2] == 2 and first_c2 is None:
                    first_c2 = total
            if sec[0] == 'C' and sec[2] == beta_e and sec[3] == [2 * k + 3] \
                    and sec[4] == [2]:
                break
        cycles.append((cyc_steps, min_c, h_sec))
        if first_c2 is not None:
            return first_c2, cycles
        k += 1
        if k > beta_e:
            return None, None

def part_d():
    print("\n=== PART D: token pass (Cycle Lemma, T, exit) ===")
    # D1: model pass at documented + held-out beta_E; Cycle Lemma laws.
    expected_t = {4: 102, 6: 620, 8: 2850}
    for be in (4, 6, 8, 10, 14, 18):
        t, cycles = model_pass(be)
        ok = t is not None
        det = ""
        if ok:
            for k, (dk, minc, hsec) in enumerate(cycles):
                if dk != 3 * 2 ** (k + 3) - 4:
                    ok, det = False, f"cycle {k}: D_k = {dk} != {3 * 2 ** (k + 3) - 4}"
                    break
                if minc != be - k:
                    ok, det = False, f"cycle {k}: min beta_C = {minc} != {be - k}"
                    break
                if hsec is None and k <= be - 2:
                    ok, det = False, f"cycle {k}: home section H_k not seen"
                    break
            if be in expected_t and t != expected_t[be]:
                ok, det = False, f"T = {t} != documented {expected_t[be]}"
        check(f"D1: model token pass beta_E = {be}: D_k law, min-beta law, "
              f"T = {t}", ok, det or
              f"{len(cycles)} cycles; T({be}) = {t}"
              + (" (documented)" if be in expected_t else " (held out)"))
    # D2: machine pass from sigma_re: classify every section with the
    # mirror model up to the first beta = 2 C-section; T must match.
    for be, b2 in [(4, 31), (6, 31), (8, 31), (10, 31), (14, 31), (10, 43)]:
        sec0 = ('C', (17, b2), be, [1], [2])
        sim = sim_of_right(sec0)
        t_model, _ = model_pass(be)
        n, err, counts, _ = classify(
            sim, sec0, mirror_step, parse_right, 100000,
            stop=lambda s: s[0] == 'C' and s[2] == 2)
        got = parse_right(sim)
        ok = err is None and got is not None and got[0] == 'C' and got[2] == 2 \
            and sim.steps == t_model and sim.e0 == 0 and sim.danger == 0
        check(f"D2: machine token pass beta_E = {be} (B2 = {b2}): "
              f"T = {sim.steps}", ok,
              f"{n} sections classified, rules {counts}; model T = {t_model}; "
              f"{err or ''}audit E-on-0 = {sim.e0}, M4 danger = {sim.danger}")
    # D3: exit successor X(beta_E) at +6 steps after H, full tape.
    for be in (6, 10):
        sec0 = ('C', (17, 31), be, [1], [2])
        sim = sim_of_right(sec0)
        classify(sim, sec0, mirror_step, parse_right, 100000,
                 stop=lambda s: s[0] == 'C' and s[2] == 2)
        sim.run(6)
        runs, hrel = sim.runs()
        want = [(1, 17), (0, 1), (1, 31), (0, 2), (1, 4)] + [(0, 1), (1, 2)] * (be - 2)
        check(f"D3: exit successor X({be}) full tape at T + 6",
              tuple(runs) == tuple(want) and SN[sim.st] == 'B' and hrel == 50,
              f"head B at cell {hrel} (want 50), state {SN[sim.st]}")

# ==========================================================================
# PART E — re-coordinatisation segment X(beta_E) -> canonical section
# ==========================================================================
def x_sim(beta_e):
    cells = [1] * 17 + [0] + [1] * 31 + [0] * 2 + [1] * 4
    for _ in range(beta_e - 2):
        cells += [0, 1, 1]
    return Sim(cells, 50, B)

def run_to_canonical(beta_e, max_steps=3000000):
    sim = x_sim(beta_e)
    steps = 0
    while steps < max_steps:
        n = sim.next_section()
        if n < 0:
            return None, steps, sim
        steps += n
        sec = parse_frame(sim)
        if sec is not None and sec[0] == 'C' and sec[1] == () and sec[2] == 18 \
                and sec[3] == 2 and sec[6] == 1 and len(sec[4]) == beta_e + 1:
            return sec, steps, sim
    return None, steps, sim

def part_e():
    print("\n=== PART E: re-coordinatisation segment ===")
    documented = {6: 760, 12: 49120, 16: 786384}
    for be in (6, 12, 16, 10, 4):
        sec, steps, sim = run_to_canonical(be)
        want_w = [29] + [1] * be
        want_r = [1] + [2] * (be - 1)
        ok = sec is not None and sec[4] == want_w and sec[5] == want_r
        det = f"canonical section {sec}; segment {steps} steps"
        if be in documented:
            ok = ok and steps == documented[be]
            det += f" (documented {documented[be]})"
        if be == 10:
            det += " (held out: no documented segment cost)"
        if be == 4:
            det += (" — settles the post-exit-analysis §2 'residue 25' vs "
                    "phase19-derivations §2.6 'residue 29' conflict: the "
                    "machine gives w0 = "
                    f"{sec[4][0] if sec else '?'}")
        check(f"E: X({be}) -> canonical section in {steps} steps", ok,
              det + f"; audit E-on-0 = {sim.e0}, M4 danger = {sim.danger}")

# ==========================================================================
# PART F — the era (machine classification + model evaluation) and ESC
# ==========================================================================
def canonical_sec(beta_e):
    return ('C', (), 18, 2, [29] + [1] * beta_e, [1] + [2] * (beta_e - 1), 1)

def grind_eval(sec, m):
    """Closed-form grind G' (phase19-derivations.md §2.2): from
    (C, pb, a, 2, [m] + W, R, G) to (B, pb, a-2, m+3, [1] + W, R, G),
    2^((m+1)/2) - 1 rules.  Returns (successor, n_rules, min_a_C)."""
    form, pb, a, s, w, r, G = sec
    assert form == 'C' and w[0] == m
    return (('B', pb, a - 2, m + 3, [1] + w[1:], r, G),
            2 ** ((m + 1) // 2) - 1, a - (m - 1) // 2)

def era_model(beta_e):
    """Word-model era evaluation from the canonical section, using the
    derived rules rule-by-rule for the absorption grind and POP chain,
    and the G' closed form (machine-validated in F1/F3) for the Stage-A
    era grinds.  Returns a dict of measured era quantities."""
    sec = canonical_sec(beta_e)
    # absorption grind: rule-by-rule until w == [1] B-section (REGEN source)
    rules = 0
    defect_pops = 0
    min_ac = None
    while True:
        if sec[0] == 'C' and (min_ac is None or sec[2] < min_ac):
            min_ac = sec[2]
        pred = frame_step(sec)
        if pred is None:
            return {"error": f"no rule at {sec}"}
        succ, cost, rule = pred
        if rule == 'POP' and sec[5][0] == 1:
            defect_pops += 1
        rules += 1
        sec = succ
        if sec[0] == 'B' and sec[4] == [1] and sec[6] == 1:
            break
        if rules > 200000:
            return {"error": "absorption grind did not terminate"}
    regen_source = sec
    # REGEN, then Stage-A era with closed-form grinds until ENTRY.
    pred = frame_step(sec)
    sec = pred[0]
    stga_sources = []
    while True:
        if sec[0] == 'B' and sec[4] == [1]:
            if sec[6] == 2:
                beta_next = sec[3] + 2
                break
            stga_sources.append((sec[3], sec[6]))
            pred = frame_step(sec)          # STGA
            sec = pred[0]
        # sec is (C, a, 2, [m], [], G): closed-form grind
        sec, nrules, minc = grind_eval(sec, sec[4][0])
        rules += nrules
    return {"s1": regen_source[3], "a_regen": regen_source[2],
            "defect_pops": defect_pops, "min_a_C": min_ac,
            "stga_sources": stga_sources, "beta_next": beta_next,
            "rules": rules}

def part_f():
    print("\n=== PART F: the era and the ESC family ===")
    # F1: machine classification of the beta_E = 6 era from the canonical
    # section through the absorption grind to the REGEN source.
    sec0 = canonical_sec(6)
    sim = sim_of_frame(sec0)
    n, err, counts, _ = classify(
        sim, sec0, frame_step, parse_frame, 100000,
        stop=lambda s: s[0] == 'B' and s[4] == [1] and s[6] == 1)
    got = parse_frame(sim)
    check("F1: machine era (beta_E = 6): absorption grind classified to "
          "the REGEN source", err is None and got == ('B', (), 22, 43, [1], [], 1),
          f"{n} sections, rules {counts}; REGEN source {got} "
          f"(want s1 = 43 = 2*6 + 31, a = 22 = 6 + 16); {err or ''}"
          f"audit E-on-0 = {sim.e0}, M4 danger = {sim.danger}")
    # F2: continue machine classification through REGEN and the Stage-A
    # era's first cycles; s + G must stay = s1 + 3 = 46 at STGA sources.
    sec = got
    ok = True
    det = ""
    seen = []
    while True:
        pred = frame_step(sec)
        if pred is None:
            ok, det = False, f"no rule at {sec}"
            break
        succ, cost, rule = pred
        if rule == 'STGA':
            seen.append((sec[3], sec[6]))
            if sec[3] + sec[6] != 46:
                ok, det = False, f"s + G = {sec[3] + sec[6]} != 46 at {sec}"
                break
            if sec[3] >= 33:
                break
        if not sim.run(cost):
            ok, det = False, "halted"
            break
        got2 = parse_frame(sim)
        if got2 != succ:
            ok, det = False, f"{rule}: landing {got2} != {succ}"
            break
        sec = succ
    check("F2: machine era (beta_E = 6): REGEN + Stage-A cycles, "
          "s + G = 46 invariant", ok,
          det or f"STGA sources (s, G) seen: {seen}; audit E-on-0 = {sim.e0}")
    # F3: G' closed form validated rule-by-rule against the machine at
    # m = 13 and m = 21 (synthetic grind starts).
    for m in (13, 21):
        sec0 = ('C', (17,), 30, 2, [m, 1, 1], [2, 2], 7)
        sim = sim_of_frame(sec0)
        want, nrules, minc = grind_eval(sec0, m)
        n, err, counts, _ = classify(
            sim, sec0, frame_step, parse_frame, nrules + 1,
            stop=lambda s, w=want: s == w)
        got = parse_frame(sim)
        check(f"F3: grind G' closed form at m = {m} ({nrules} rules)",
              err is None and got == want,
              f"classified {n} sections to {got}; {err or ''}")
    # F4: word-model era evaluation at held-out beta_E (and documented 6).
    for be in (6, 10, 14, 20):
        res = era_model(be)
        if "error" in res:
            check(f"F4: era evaluation beta_E = {be}", False, res["error"])
            continue
        ok = (res["s1"] == 2 * be + 31 and res["a_regen"] == be + 16
              and res["defect_pops"] == 1 and res["min_a_C"] == 4
              and res["beta_next"] == 2 * be + 34
              and all(s + g == res["s1"] + 3 for s, g in res["stga_sources"]))
        check(f"F4: era evaluation beta_E = {be}: s1 = {res['s1']}, "
              f"beta' = {res['beta_next']}", ok,
              f"a_regen = {res['a_regen']}, defect pops = {res['defect_pops']}, "
              f"min a_C = {res['min_a_C']}, {len(res['stga_sources'])} STGA cycles, "
              f"s + G = s1 + 3 throughout"
              + (" (held out)" if be != 6 else " (documented)"))
    # F5: ESC probe prefix at documented and held-out (L, beta).
    for (L, be) in [(12, 6), (18, 10), (26, 8)]:
        cells = [1] * L + [0] + [1] * 2 + [0] * 3 + [1] * 2
        for _ in range(be - 2):
            cells += [0, 1, 1]
        sim = Sim(cells, L + 1, C)
        sim.run(L + 42)
        sec = parse_frame(sim)
        want = ('C', (), 5, 2, [1, L - 6] + [1] * be, [2, 1] + [2] * (be - 1), 1)
        check(f"F5: ESC({L}, {be}) probe prefix: landing at L + 42 = {L + 42}",
              sec == want and sim.d0 == 2 and sim.danger == 0 and sim.e0 == 0,
              f"landing {sec}; D-on-0 = {sim.d0} (want 2, in E2/E4 ignitions)"
              + (" (held out)" if (L, be) != (12, 6) else ""))
    # F6: the full ESC era at (L, beta) = (12, 6) by machine
    # classification: probe prefix, grind G''(6), POP2, POP chain,
    # REGEN, Stage-A era (constant 2 beta + 4 = 16), ENTRY to sigma_re(16).
    cells = [1] * 12 + [0] + [1] * 2 + [0] * 3 + [1] * 2
    for _ in range(4):
        cells += [0, 1, 1]
    sim = Sim(cells, 13, C)
    sim.run(54)                                  # probe prefix, L + 42
    sec = parse_frame(sim)
    n, err, counts, _ = classify(
        sim, sec, frame_step, parse_frame, 100000,
        stop=lambda s: False)
    # classify stops only via ENTRY handling or a model gap; ENTRY is
    # reported through the classify ENTRY branch (returns err None).
    check("F6: ESC(12, 6) full era classified to ENTRY -> sigma_re(16)",
          err is None and counts.get('ENTRY', 0) == 1,
          f"{n} sections after the probe prefix; rules {counts}; {err or ''}"
          f"audit E-on-0 = {sim.e0}, M4 danger = {sim.danger}")

# ==========================================================================
# PART G — loop ascent (symbolic iteration of the composed loop maps)
# ==========================================================================
def part_g():
    print("\n=== PART G: loop ascent ===")
    seq = [24]
    for _ in range(6):
        seq.append(2 * seq[-1] + 34)
    ok = all(seq[i + 1] > seq[i] for i in range(len(seq) - 1)) and \
        all(2 * b + 31 + 3 == 2 * b + 34 > b for b in seq)
    check("G1: settled loop map beta' = 2 beta + 34 strictly increases; "
          "s_regen + 3 = s1 + 3 = beta' > beta", ok, f"orbit from 24: {seq}")
    seq = [8]
    for _ in range(5):
        seq.append(2 * seq[-1] + 4)
    ok = all(seq[i + 1] > seq[i] for i in range(len(seq) - 1)) and \
        all(2 * b + 1 + 3 == 2 * b + 4 > b for b in seq)
    check("G2: ESC loop map beta_next = 2 beta + 4 strictly increases; "
          "s_regen + 3 = 2 beta + 4 > beta", ok, f"orbit from 8: {seq}")
    check("G3: deviated iteration-3 instance (documented): s_regen = 47, "
          "era constant 50 = s_regen + 3 > beta = 20, beta'' = 50",
          47 + 3 == 50 > 20, "phase20-derivations.md §6.1 / phase21 §3")

def main():
    t0 = time.time()
    print("reproduce_168016.py — independent reproduction of the "
          "non-halting proof for BB(6) machine #168016")
    print(f"spec: {SPEC}" + ("  [--quick]" if QUICK else ""))
    part_a()
    part_b()
    part_c()
    part_d()
    part_e()
    part_f()
    part_g()
    npass = sum(1 for _, s, _ in RESULTS if s == "PASS")
    nfail = sum(1 for _, s, _ in RESULTS if s == "FAIL")
    nfind = sum(1 for _, s, _ in RESULTS if s == "FINDING")
    print(f"\n==== SUMMARY: {npass} PASS, {nfail} FAIL, {nfind} FINDING "
          f"({time.time() - t0:.1f}s) ====")
    for name, status, detail in RESULTS:
        if status != "PASS":
            print(f"{status}: {name} — {detail}")
    return 1 if nfail else 0

if __name__ == "__main__":
    sys.exit(main())
