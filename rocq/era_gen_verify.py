#!/usr/bin/env python3
"""Phase 35 pre-verification: ERA_GEN, the general-residue era law.

Simulates machine #168016 with the exact step semantics of rocq/TM.v
(zipper configs; E-on-0 = halt) and checks, on the REAL machine, the
boundary sequence predicted by the generalisation of Era.v's ERA_LAW
assembly to residue rho (odd), era parameter m (= beta_E), at the
fixed frame a2 = 16 (the canonical section of phase19 SS2.3):

  csec 16 rho 2 ((1,1) :: (1,2)^(m-1)) 1
    --absorption: GRIND (t-1) for rho = 2t+1 >= 3; TDN for rho = 1-->
  bsec 16 1 (rho+3) ((1,1) :: (1,2)^(m-1)) 1
    --POP_CHAIN over runs 1 :: 2^(m-1)-->
  bsec (16+m) 1 (rho+2m+2) [] 1                     (s1 = rho + 2m + 2)
    --REGEN (cost 4*s1 + 22)-->
  csec (16+m) 1 2 [] (rho+2m+1)                     (G0 = s1 - 1, even)
    --TDN (cost 6)-->
  bsec (16+m) 1 4 [] (rho+2m+1)
    --J = t + m cycles of (STGA ; GRIND k), s + G = rho + 2m + 5-->
  bsec (16+m) 1 (rho+2m+3) [] 2                     (entry source)
    --ENTRY_gen (cost s_fin + 12)-->
  entry_tgt_gen [] (16+m) (rho+2m+3)
    ==tape== rcsec (0 :: 1^(m+17)) (rho+2m+3) [(1,2)]

Predicted domain: rho odd, 1 <= rho <= 33 (residue-grind floor
t <= 16 at a2 = 16; era-loop floors k + 1 <= m + 16 give the same
bound).  Negative controls: rho = 35 (floor exceeded -- the grind
dips through the frame) and rho = 30 (even -- G' is odd-only and
the Stage-A era's G-parity invariant fails).

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


def entry_tgt_gen(a, s):
    return relkey('C', [1] * s + [0] + [1] * (a + 1),
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


def era_targets(rho, m):
    """Predicted boundary sequence for odd rho = 2t+1, era param m.
    Returns (targets, labels, meta) where meta carries the indices
    of the REGEN landing and the entry source for delta checks."""
    t = (rho - 1) // 2
    pairs = [(1, 1)] + [(1, 2)] * (m - 1)
    J = t + m
    s1 = rho + 2 * m + 2
    G0 = rho + 2 * m + 1
    s_fin = rho + 2 * m + 3
    tg = [csec(16, rho, 2, pairs, 1)]
    lab = [f'start csec 16 {rho} 2 pairs 1']
    tg.append(bsec(16, 1, rho + 3, pairs, 1))
    lab.append('absorption -> bsec 16 1 (rho+3) pairs 1')
    tg.append(bsec(16 + m, 1, s1, [], 1))
    lab.append('POP_CHAIN -> REGEN source')
    idx_regen_src = len(tg) - 1
    tg.append(csec(16 + m, 1, 2, [], G0))
    lab.append('REGEN -> csec (16+m) 1 2 [] G0')
    idx_regen_land = len(tg) - 1
    tg.append(bsec(16 + m, 1, 4, [], G0))
    lab.append('TDN -> bsec (16+m) 1 4 [] G0')
    for k in range(J):
        tg.append(csec(16 + m, 2 * k + 3, 2, [], G0 - 2 * k - 2))
        lab.append(f'STGA k={k} -> csec g0={2 * k + 3} G={G0 - 2 * k - 2}')
        tg.append(bsec(16 + m, 1, 2 * k + 6, [], G0 - 2 * k - 2))
        lab.append(f'GRIND {k} -> bsec s={2 * k + 6} G={G0 - 2 * k - 2}')
    idx_entry_src = len(tg) - 1
    tg.append(entry_tgt_gen(16 + m, s_fin))
    lab.append('ENTRY_gen -> entry_tgt_gen')
    meta = {'t': t, 'J': J, 's1': s1, 'G0': G0, 's_fin': s_fin,
            'idx_regen_src': idx_regen_src,
            'idx_regen_land': idx_regen_land,
            'idx_entry_src': idx_entry_src}
    return tg, lab, meta


def check_positive(rho, m, budget):
    tg, lab, meta = era_targets(rho, m)
    # sanity: the ENTRY landing's tape is the predicted rcsec form
    assert tg[-1] == rcsec([0] + [1] * (m + 17), meta['s_fin'], [(1, 2)]), \
        'entry_tgt_gen key != rcsec key'
    mach = machine_from_key(tg[0])
    hits, status = run_through(mach, tg, budget)
    hitmap = dict(hits)
    ok = (status == 'ok')
    print(f'(rho={rho}, m={m}): status={status}, '
          f'boundaries {len(hits)}/{len(tg)}, total steps={mach.steps}')
    if len(hits) >= 2:
        d = hits[1][1] - hits[0][1]
        kind = 'TDN' if rho == 1 else f'GRIND {meta["t"] - 1}'
        print(f'    absorption ({kind}) delta = {d}')
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
    # STGA deltas at the first two cycles (proved cost 2s + 6)
    base = meta['idx_regen_land'] + 1  # index of TDN landing
    for k in (0, 1):
        src_i = base + 2 * k
        dst_i = src_i + 1
        if src_i in hitmap and dst_i in hitmap:
            d = hitmap[dst_i] - hitmap[src_i]
            exp = 2 * (4 + 2 * k) + 6
            print(f'    STGA k={k} delta = {d} (proved cost {exp})')
            ok &= (d == exp)
    print(f'    -> {"PASS" if ok else "FAIL"}')
    return ok


def check_negative(rho, m, budget):
    """For out-of-domain rho: run the odd-rho boundary prediction
    (with t = (rho-1)//2 rounding where needed) and report how far
    the machine actually gets.  For even rho the absorption target
    uses the same formal bookkeeping, which the machine is expected
    NOT to follow."""
    t = (rho - 1) // 2
    pairs = [(1, 1)] + [(1, 2)] * (m - 1)
    targets = [csec(16, rho, 2, pairs, 1),
               bsec(16, 1, rho + 3, pairs, 1),
               bsec(16 + m, 1, rho + 2 * m + 2, [], 1)]
    mach = machine_from_key(targets[0])
    hits, status = run_through(mach, targets, budget)
    print(f'(rho={rho}, m={m}) NEGATIVE: status={status}, '
          f'boundaries hit {len(hits)}/{len(targets)} '
          f'(absorption target reached: {len(hits) >= 2}), '
          f'steps run={mach.steps}')
    return len(hits) < 2  # success = the prediction indeed fails


def main():
    ok = True
    # control: rho = 29 is ERA_LAW (proved in Era.v)
    ok &= check_positive(29, 2, 40_000_000)
    # the two required non-29 instances
    ok &= check_positive(27, 1, 40_000_000)
    ok &= check_positive(27, 2, 40_000_000)
    ok &= check_positive(31, 1, 40_000_000)
    ok &= check_positive(31, 2, 40_000_000)
    # domain boundary: rho = 33 (t = 16, floors at equality)
    ok &= check_positive(33, 1, 60_000_000)
    # rho = 1: absorption is TDN, not GRIND
    ok &= check_positive(1, 2, 40_000_000)
    # negative controls
    ok &= check_negative(35, 1, 20_000_000)
    ok &= check_negative(30, 1, 20_000_000)
    print('ALL CHECKS PASS' if ok else 'FAILURES PRESENT')
    return 0 if ok else 1


if __name__ == '__main__':
    raise SystemExit(main())
