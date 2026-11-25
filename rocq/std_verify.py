#!/usr/bin/env python3
"""Phase 34 pre-verification: the standard-regime assembly for H_STD.

Simulates the machine #168016 with the exact step semantics of
rocq/TM.v (zipper configs; E-on-0 = halt) and checks, on the REAL
machine (not a word model):

(A) From cfg_Isec (Configs.v): the macro-boundary sequence predicted
    by the assembly
      HC [17] 95 1 2 [] 134
        --TDN-->  HB 95 1 4 [] 134
        --STGA--> HC 95 3 2 [] 132
        --GRIND t -> HB 95 1 (2t+6) [] (132-2t)
         --STGA--> HC 95 (2t+5) 2 [] (130-2t)      for t = 0, 1, 2, ...
    recording the step at which each predicted section form is first
    reached, in order.  Rule-cost deltas for TDN / Stage A are
    checked against the proved costs (6 and 2s+6).

(B) End-to-end small instances of the SAME assembly at the same
    frame a2 = 95 with G0 in {6, 8, 10}: the full predicted boundary
    sequence through the final grind, the identification of the
    final B-section with entry_src 95 (G0+2), and the ENTRY landing
    entry_tgt 95 (G0+2) exactly G0+2+12 steps later.

Configs are compared by (state, set of 1-cell offsets relative to
the head) -- the tape-equality of Finite.v's canon / cfg_sim.
"""

# trans[(state, read)] = (write, dir, next) ; None = halt (E-on-0)
TRANS = {
    ('A', 0): (1, 'R', 'B'), ('A', 1): (1, 'R', 'A'),
    ('B', 0): (1, 'R', 'C'), ('B', 1): (1, 'L', 'B'),
    ('C', 0): (0, 'L', 'D'), ('C', 1): (0, 'R', 'A'),
    ('D', 0): (1, 'R', 'F'), ('D', 1): (1, 'L', 'E'),
    ('E', 0): None,          ('E', 1): (1, 'L', 'F'),
    ('F', 0): (1, 'L', 'C'), ('F', 1): (0, 'L', 'F'),
}


class Machine:
    def __init__(self, state, ones, head=0):
        self.state = state
        self.ones = set(ones)   # absolute positions of 1-cells
        self.head = head
        self.steps = 0
        self.halted = False

    def key(self):
        return (self.state, frozenset(p - self.head for p in self.ones))

    def step(self):
        r = 1 if self.head in self.ones else 0
        t = TRANS[(self.state, r)]
        if t is None:
            self.halted = True
            return False
        w, d, q = t
        if w:
            self.ones.add(self.head)
        else:
            self.ones.discard(self.head)
        self.head += 1 if d == 'R' else -1
        self.state = q
        self.steps += 1
        return True


def tail(pairs, G):
    out = []
    for (g, r) in pairs:
        out += [0] * g + [1] * r
    return out + [0] * G + [1, 1]


def relkey(state, left, right):
    ones = set()
    for i, b in enumerate(right):
        if b:
            ones.add(i)
    for i, b in enumerate(left):
        if b:
            ones.add(-1 - i)
    return (state, frozenset(ones))


Q0 = [0] + [1] * 17  # enc [17]: separator 0 + wall 1^17


def gcsec(a2, g0, s, pairs, G):
    return relkey('C', [1] * a2 + Q0,
                  [1, 1] + [0] * g0 + [1] * s + tail(pairs, G))


def gbsec(a, g0, s, pairs, G):
    return relkey('B', [1] * a + Q0,
                  [0] * g0 + [1] * s + tail(pairs, G))


def entry_src(B2, s):
    return relkey('B', [1] * B2 + [0] + [1] * 17,
                  [0] + [1] * s + [0] * 2 + [1, 1])


def entry_tgt(B2, s):
    return relkey('C', [1] * s + [0] + [1] * (B2 + 1) + [0] + [1] * 17,
                  [1, 1, 0, 1, 1, 0])


def machine_from_key(key):
    state, ones = key
    return Machine(state, set(ones), head=0)


def run_through(m, targets, budget):
    """Advance m until each target key is hit in order.
    Returns list of (index, step) or None on halt/budget exhaustion."""
    hits = []
    ti = 0
    if m.key() == targets[0]:
        hits.append((0, 0))
        ti = 1
    while ti < len(targets):
        if m.steps >= budget:
            return hits, 'budget'
        if not m.step():
            return hits, 'HALT'
        if m.key() == targets[ti]:
            hits.append((ti, m.steps))
            ti += 1
    return hits, 'ok'


def main():
    ok = True

    # sanity: the two identifications used by the assembly
    cfg_isec = relkey('C', [1] * 95 + [0] + [1] * 17,
                      [1] * 2 + [0] + [1] * 2 + [0] * 134 + [1] * 2)
    assert cfg_isec == gcsec(95, 1, 2, [], 134), 'cfg_Isec != HC [17] 95 1 2 [] 134'
    assert entry_src(95, 136) == gbsec(95, 1, 136, [], 2), 'entry_src != HB form'
    print('identifications: cfg_Isec = HC[17] 95 1 2 [] 134, '
          'entry_src B2 s = HB[17] B2 1 s [] 2  OK')

    # ---- (A) trajectory macro boundaries from cfg_Isec ----
    targets = [gcsec(95, 1, 2, [], 134),
               gbsec(95, 1, 4, [], 134),
               gcsec(95, 3, 2, [], 132)]
    labels = ['start HC 1 [] 134', 'TDN -> HB s=4 G=134', 'STGA -> HC 3 [] 132']
    for t in range(6):
        targets.append(gbsec(95, 1, 2 * t + 6, [], 132 - 2 * t))
        labels.append(f'GRIND {t} -> HB s={2 * t + 6} G={132 - 2 * t}')
        targets.append(gcsec(95, 2 * t + 5, 2, [], 130 - 2 * t))
        labels.append(f'STGA -> HC {2 * t + 5} [] {130 - 2 * t}')
    m = machine_from_key(cfg_isec)
    hits, status = run_through(m, targets, 3_000_000)
    print(f'(A) status={status}, boundaries hit: {len(hits)}/{len(targets)}')
    prev = 0
    for (i, st) in hits:
        print(f'    step {st:>9}  (+{st - prev:>7})  {labels[i]}')
        prev = st
    if hits and hits[0] == (0, 0) and len(hits) >= 2:
        d_tdn = hits[1][1] - hits[0][1]
        print(f'    TDN delta = {d_tdn} (proved cost 6)')
        ok &= (d_tdn == 6)
    # Stage A deltas: boundary 2 (after STGA at s=4) and the STGA
    # boundaries after each GRIND: indices 4, 6, 8, ...
    stga_expect = {2: 2 * 4 + 6, 4: 2 * 6 + 6, 6: 2 * 8 + 6,
                   8: 2 * 10 + 6, 10: 2 * 12 + 6, 12: 2 * 14 + 6,
                   14: 2 * 16 + 6}
    hitmap = dict(hits)
    for idx, exp in stga_expect.items():
        if idx in hitmap and idx - 1 in hitmap:
            d = hitmap[idx] - hitmap[idx - 1]
            print(f'    STGA delta at boundary {idx} = {d} (proved cost {exp})')
            ok &= (d == exp)
    ok &= (status == 'ok')

    # ---- (B) end-to-end small instances ----
    for G0 in (6, 8, 10):
        k = (G0 - 6) // 2 + 1  # number of STD cycles after the first STGA
        tg = [gcsec(95, 1, 2, [], G0),
              gbsec(95, 1, 4, [], G0),
              gcsec(95, 3, 2, [], G0 - 2)]
        lab = ['start', 'TDN', 'STGA']
        G = G0 - 2
        for t in range(k):
            tg.append(gbsec(95, 1, 2 * t + 6, [], G))
            lab.append(f'GRIND {t}')
            tg.append(gcsec(95, 2 * t + 5, 2, [], G - 2))
            lab.append('STGA')
            G -= 2
        s_fin = 2 * (k + 1) + 6 - 2  # = 2k+6 ... recompute below
        s_fin = 2 * k + 6
        # final grind is GRIND k from HC (2k+3) [] 2
        tg.append(gbsec(95, 1, s_fin, [], 2))
        lab.append(f'GRIND {k} -> entry_src form')
        tg.append(entry_tgt(95, s_fin))
        lab.append('ENTRY -> entry_tgt')
        m = machine_from_key(tg[0])
        hits, status = run_through(m, tg, 3_000_000)
        hitmap = dict(hits)
        last = hits[-1] if hits else None
        entry_delta = None
        if len(hits) >= 2:
            entry_delta = hits[-1][1] - hits[-2][1]
        print(f'(B) G0={G0}: status={status}, boundaries {len(hits)}/{len(tg)}, '
              f'final step={last[1] if last else None}, '
              f'ENTRY delta={entry_delta} (expect {s_fin + 12}), s_fin={s_fin}')
        ok &= (status == 'ok' and entry_delta == s_fin + 12
               and hitmap.get(len(tg) - 2) is not None
               and tg[-2] == entry_src(95, s_fin))

    print('ALL CHECKS PASS' if ok else 'FAILURES PRESENT')
    return 0 if ok else 1


if __name__ == '__main__':
    raise SystemExit(main())
