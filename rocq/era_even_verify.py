#!/usr/bin/env python3
"""Phase 39 pre-verification: the even-residue era law.

Simulates machine #168016 with the exact step semantics of rocq/TM.v
(zipper configs; E-on-0 = halt) and checks, on the REAL machine, the
boundary sequence predicted by the even-rho assembly (EraEven.v):

  csec 16 rho 2 ((1,1) :: (1,2)^(m-1)) 1          rho = 2k+2 even
    --EVEN_GRIND (absorption: PUSH/TDN/TUP prefix, climb of
       GRIND i + TUP, final gap-2 rotation gtup_prefix)-->
  gbsec P0 rho 1 2 pairs 1,  P0 = [0] ++ 1^16
    --POP_CHAIN over runs 1 :: 2^(m-1) (delta 2s+3 per pop)-->
  gbsec P0 (rho+m) 1 (2m+1) [] 1                  (s1 = 2m+1, odd)
    --REGEN (delta 4*s1 + 22)-->
  gcsec P0 (rho+m) 1 2 [] (2m)                    (G0 = 2m, even)
    --TDN (delta 6)-->
  gbsec P0 (rho+m) 1 4 [] (2m)
    --J = m-1 cycles of (STGA ; GRIND k), s + G = 2m + 4-->
  gbsec P0 (rho+m) 1 (2m+2) [] 2                  (entry source)
    --ENTRY_gen (delta s_fin + 12)-->
  entry_tgt_gen P0 (rho+m) (2m+2)
    ==tape== rcsec (0 :: 1^(rho+m+1) ++ P0) (2m+2) [(1,2)]

Predicted domain: rho even, 2 <= rho <= 34 (EVEN_GRIND floor
k <= a2 = 16, i.e. rho <= 2*16 + 2), era parameter m >= 1.
The landing beta' = 2m + 4 is INDEPENDENT of rho (the residue is
converted into frame: the absorption landing's near block is rho).

Also checks the EVEN_GRIND climb's intermediate landings at
(rho, m) = (10, 2) and (30, 2): after the prefix, the climb visits
csec 15 (2i+3) 2 ((rho-4-2i, 2) :: pairs) 1 and the GRIND landings
bsec 15 1 (2i+6) ((rho-4-2i, 2) :: pairs) 1, i = 0 .. k-2, before
the rotation at the (2, 2) pair.

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


def rtail(pairs):
    out = []
    for (g, r) in pairs:
        out += [0] * g + [1] * r
    return out


def relkey(state, left, right):
    ones = set()
    for i, b in enumerate(right):
        if b:
            ones.add(i)
    for i, b in enumerate(left):
        if b:
            ones.add(-1 - i)
    return (state, frozenset(ones))


def csec(a2, g0, s, pairs, G):
    return relkey('C', [1] * a2,
                  [1, 1] + [0] * g0 + [1] * s + tail(pairs, G))


def bsec(a, g0, s, pairs, G):
    return relkey('B', [1] * a,
                  [0] * g0 + [1] * s + tail(pairs, G))


# P0 = [0] ++ 1^16 as a left list (nearest first): the gbsec frame's
# far part.  gbsec P0 a: left = 1^a ++ P0.
P0 = [0] + [1] * 16


def gbsec(a, g0, s, pairs, G):
    return relkey('B', [1] * a + P0,
                  [0] * g0 + [1] * s + tail(pairs, G))


def gcsec(a2, g0, s, pairs, G):
    return relkey('C', [1] * a2 + P0,
                  [1, 1] + [0] * g0 + [1] * s + tail(pairs, G))


def entry_tgt_gen(a, s):
    # entry_tgt_gen P0 a s: left = 1^s ++ (0 :: 1^(a+1) ++ P0)
    return relkey('C', [1] * s + [0] + [1] * (a + 1) + P0,
                  [1, 1, 0, 1, 1, 0])


def rcsec(P, b2, pairs):
    return relkey('C', [1] * b2 + P, [1, 1] + rtail(pairs))


def machine_from_key(key):
    state, ones = key
    return Machine(state, set(ones), head=0)


def run_through(m, targets, budget):
    """Advance m until each target key is hit in order.
    Returns (hits, status): hits = [(index, step)], status in
    {'ok', 'budget', 'HALT'}."""
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


def even_targets(rho, m):
    """Predicted boundary sequence for even rho, era parameter m."""
    pairs = [(1, 1)] + [(1, 2)] * (m - 1)
    s1 = 2 * m + 1
    G0 = 2 * m
    s_fin = 2 * m + 2
    a_f = rho + m
    tg = [csec(16, rho, 2, pairs, 1)]
    lab = ['start csec 16 rho 2 pairs 1']
    tg.append(gbsec(rho, 1, 2, pairs, 1))
    lab.append('EVEN_GRIND -> gbsec P0 rho 1 2 pairs 1')
    # POP_CHAIN, one target per pop
    s = 2
    a = rho
    rest = pairs
    while rest:
        (g, r) = rest[0]
        s = s + r
        a = a + 1
        rest = rest[1:]
        tg.append(gbsec(a, 1, s, rest, 1))
        lab.append(f'POP -> gbsec P0 {a} 1 {s} {rest} 1')
    idx_regen_src = len(tg) - 1
    tg.append(gcsec(a_f, 1, 2, [], G0))
    lab.append('REGEN -> gcsec P0 (rho+m) 1 2 [] G0')
    idx_regen_land = len(tg) - 1
    tg.append(gbsec(a_f, 1, 4, [], G0))
    lab.append('TDN -> gbsec P0 (rho+m) 1 4 [] G0')
    for k in range(m - 1):
        tg.append(gcsec(a_f, 2 * k + 3, 2, [], G0 - 2 * k - 2))
        lab.append(f'STGA k={k} -> gcsec g0={2 * k + 3} G={G0 - 2 * k - 2}')
        tg.append(gbsec(a_f, 1, 2 * k + 6, [], G0 - 2 * k - 2))
        lab.append(f'GRIND {k} -> gbsec s={2 * k + 6} G={G0 - 2 * k - 2}')
    idx_entry_src = len(tg) - 1
    tg.append(entry_tgt_gen(a_f, s_fin))
    lab.append('ENTRY_gen -> entry_tgt_gen')
    meta = {'s1': s1, 'G0': G0, 's_fin': s_fin, 'a_f': a_f,
            'idx_regen_src': idx_regen_src,
            'idx_regen_land': idx_regen_land,
            'idx_entry_src': idx_entry_src}
    return tg, lab, meta


def check_even(rho, m, budget):
    tg, lab, meta = even_targets(rho, m)
    # sanity: the ENTRY landing's tape is the predicted rcsec form
    Pprime = [0] + [1] * (meta['a_f'] + 1) + P0
    assert tg[-1] == rcsec(Pprime, meta['s_fin'], [(1, 2)]), \
        'entry_tgt_gen key != rcsec key'
    mach = machine_from_key(tg[0])
    hits, status = run_through(mach, tg, budget)
    hitmap = dict(hits)
    ok = (status == 'ok')
    print(f'(rho={rho}, m={m}): status={status}, '
          f'boundaries {len(hits)}/{len(tg)}, total steps={mach.steps}')
    if status != 'ok':
        nxt = len(hits)
        if nxt < len(tg):
            print(f'    first missed boundary: {lab[nxt]}')
    # fixed-cost delta checks
    irs, irl = meta['idx_regen_src'], meta['idx_regen_land']
    if irs in hitmap and irl in hitmap:
        d = hitmap[irl] - hitmap[irs]
        exp = 4 * meta['s1'] + 22
        print(f'    REGEN delta = {d} (proved cost {exp})')
        ok &= (d == exp)
    if irl in hitmap and irl + 1 in hitmap:
        d = hitmap[irl + 1] - hitmap[irl]
        print(f'    TDN delta = {d} (proved cost 6)')
        ok &= (d == 6)
    ies = meta['idx_entry_src']
    if ies in hitmap and ies + 1 in hitmap:
        d = hitmap[ies + 1] - hitmap[ies]
        exp = meta['s_fin'] + 12
        print(f'    ENTRY delta = {d} (expect s_fin + 12 = {exp})')
        ok &= (d == exp)
    # POP deltas: targets 2 .. irs are the pop landings
    prev = hitmap.get(1)
    s = 2
    rs = [1] + [2] * (m - 1)
    for j, r in enumerate(rs):
        idx = 2 + j
        if prev is not None and idx in hitmap:
            d = hitmap[idx] - prev
            exp = 2 * s + 3
            if d != exp:
                print(f'    POP {j} delta = {d} (expect {exp}) MISMATCH')
                ok = False
            prev = hitmap[idx]
            s += r
    # STGA deltas
    base = meta['idx_regen_land'] + 1  # index of TDN landing
    for k in range(m - 1):
        src_i = base + 2 * k
        dst_i = src_i + 1
        if src_i in hitmap and dst_i in hitmap:
            d = hitmap[dst_i] - hitmap[src_i]
            exp = 2 * (4 + 2 * k) + 6
            if d != exp:
                print(f'    STGA k={k} delta = {d} (expect {exp}) MISMATCH')
                ok = False
    print(f'    -> {"PASS" if ok else "FAIL"}')
    return ok


def check_climb(rho, m, budget):
    """The EVEN_GRIND climb's intermediate landings (rho >= 6)."""
    k = rho // 2 - 1
    pairs = [(1, 1)] + [(1, 2)] * (m - 1)
    tg = [csec(16, rho, 2, pairs, 1)]
    lab = ['start']
    # prefix: PUSH + TDN + TUP
    tg.append(csec(15, 3, 2, [(rho - 4, 2)] + pairs, 1))
    lab.append('prefix (PUSH+TDN+TUP) -> csec 15 3 2 ((rho-4,2)::pairs) 1')
    for i in range(0, k - 1):
        # GRIND i landing
        tg.append(bsec(15, 1, 2 * i + 6, [(rho - 4 - 2 * i, 2)] + pairs, 1))
        lab.append(f'GRIND {i} -> bsec 15 1 {2 * i + 6} '
                   f'((rho-4-2i,2)::pairs) 1')
        if i < k - 2:
            tg.append(csec(15, 2 * i + 5, 2,
                           [(rho - 6 - 2 * i, 2)] + pairs, 1))
            lab.append(f'TUP -> csec 15 {2 * i + 5} 2 ((rho-6-2i,2)::pairs) 1')
    tg.append(gbsec(rho, 1, 2, pairs, 1))
    lab.append('rotation -> gbsec P0 rho 1 2 pairs 1')
    mach = machine_from_key(tg[0])
    hits, status = run_through(mach, tg, budget)
    ok = (status == 'ok')
    print(f'climb (rho={rho}, m={m}): status={status}, '
          f'boundaries {len(hits)}/{len(tg)}, steps={mach.steps}')
    if status != 'ok' and len(hits) < len(tg):
        print(f'    first missed: {lab[len(hits)]}')
    print(f'    -> {"PASS" if ok else "FAIL"}')
    return ok


def main():
    ok = True
    ok &= check_climb(10, 2, 10_000_000)
    ok &= check_climb(30, 2, 40_000_000)
    ok &= check_even(2, 1, 10_000_000)
    ok &= check_even(2, 4, 10_000_000)
    ok &= check_even(4, 4, 10_000_000)
    ok &= check_even(6, 3, 10_000_000)
    ok &= check_even(10, 2, 10_000_000)
    ok &= check_even(28, 5, 40_000_000)
    ok &= check_even(30, 4, 40_000_000)
    ok &= check_even(34, 4, 40_000_000)
    print('ALL CHECKS PASS' if ok else 'FAILURES PRESENT')
    return 0 if ok else 1


if __name__ == '__main__':
    raise SystemExit(main())
