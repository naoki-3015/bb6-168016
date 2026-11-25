#!/usr/bin/env python3
"""Phase 39 fence evidence for the settled residues rho >= 35
(B2 >= 37), complementing EraGen.v's Phase 35 negative control
(era_gen_verify.py: the in-domain absorption landing
bsec 16 1 (rho+3) pairs 1 is never reached for odd rho >= 35).

This script documents what the machine ACTUALLY does at rho >= 35
(absorption from the era source csec 16 rho 2 ((1,1)::(1,2)^(m-1)) 1
at m = 1, direct simulation with the exact step semantics of
rocq/TM.v -- zipper configs, E-on-0 = halt):

  rho = 33 (odd, in-domain control): absorption at step 1,572,782
      on bsec 16 1 36 [(1,1)] 1 (s = rho + 3, the proved law).
  rho = 35 (odd): absorption completes at step 3,145,681 on
      bsec 17 1 39 [(1,1)] 1 -- the frame GREW by one and
      s = rho + 4 (one more than the in-domain rho + 3): a single
      sub-frame "edge" excursion at the dip bottom.  The era that
      would follow has G0 = s1 - 1 = rho + 2m + 2 ODD, so the
      Stage-A era cannot land on the G = 2 entry source.
  rho = 37, 39, 41 (odd): absorption completes by ROTATION on the
      two-block section gbsec (0::1^17) 38 1 (rho-33) [(1,1)] 1
      (steps 6,291,334 / 6,291,354 / 6,291,398).
  rho = 36 (even): absorption completes by rotation on
      gbsec (0::1^17) 37 1 2 [(1,1)] 1 at step 3,145,643.
  rho = 38, 40 (even): NO absorption landing of either form
      (pure-frame bsec, or two-block gbsec, with the original
      stack, g0 = 1, G = 1) within 60,000,000 steps (rho = 36
      needed only 3,145,643).

Conclusion (the Phase 39 fence): residues rho >= 35 exceed the
fixed era frame a2 = 16 (RECOORD2_uncond's stage-3 landing) in
BOTH parities.  What lies beyond is not one uniform family: a
frame-growing edge excursion (rho = 35, with era-parity fallout),
rotation landings on a two-block frame (rho = 36, 37, 39, 41),
and no observed two-block absorption at all (rho = 38, 40).
Mechanising any of it needs a sub-frame edge-grind theory
(step lists for C-sections at a2 = 0 and their landings) that
the current lemma vocabulary does not contain; the settled
iteration is therefore discharged exactly for 3 <= B2 <= 36
(Loop.v: SETTLED_ITER_GEN_odd + SETTLED_ITER_GEN_even) and
B2 >= 37 stays on the conditional SETTLED_ITER_GEN.

Run: python3 era_fence35_verify.py   (about 9 minutes)
"""

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
        self.ones = set(ones)
        self.head = head
        self.steps = 0
        self.halted = False

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


def csec_key(a2, g0, s, pairs, G):
    ones = set()
    for i in range(a2):
        ones.add(-1 - i)
    right = [1, 1] + [0] * g0 + [1] * s + tail(pairs, G)
    for i, b in enumerate(right):
        if b:
            ones.add(i)
    return ('C', ones)


def parse_body(bits):
    """Parse 0^g0 1^s (0^g 1^r)* 0^G 1 1; returns (g0, s, pairs, G)."""
    n = len(bits)
    i = 0
    g0 = 0
    while i < n and bits[i] == 0:
        g0 += 1
        i += 1
    s = 0
    while i < n and bits[i] == 1:
        s += 1
        i += 1
    if s < 1:
        return None
    pairs = []
    while True:
        rest = bits[i:]
        if not rest:
            return None
        if sum(rest) == 2:
            j = 0
            while j < len(rest) and rest[j] == 0:
                j += 1
            if rest[j:] == [1, 1]:
                return (g0, s, pairs, j)
            return None
        g = 0
        while i < n and bits[i] == 0:
            g += 1
            i += 1
        if g < 1:
            return None
        r = 0
        while i < n and bits[i] == 1:
            r += 1
            i += 1
        if r < 1:
            return None
        pairs.append((g, r))


def left_frames(ones, head):
    """('pure', a) if the left ones are exactly head-1..head-a;
    ('two', a, b) for a two-block frame; else None."""
    left = sorted(p for p in ones if p < head)
    if not left:
        return ('pure', 0)
    a = 0
    while (head - 1 - a) in ones:
        a += 1
    covered = set(range(head - a, head))
    rest = [p for p in left if p not in covered]
    if not rest:
        return ('pure', a)
    top = head - a - 2
    if top not in ones:
        return None
    b = 0
    while (top - b) in ones:
        b += 1
    covered2 = set(range(top - b + 1, top + 1))
    if [p for p in rest if p not in covered2]:
        return None
    return ('two', a, b)


def parse_config(state, ones, head):
    if state not in ('B', 'C'):
        return None
    fr = left_frames(ones, head)
    if fr is None:
        return None
    right_ones = [p - head for p in ones if p >= head]
    if not right_ones:
        return None
    maxoff = max(right_ones)
    bits = [1 if (head + i) in ones else 0 for i in range(maxoff + 1)]
    if state == 'C':
        if bits[:2] != [1, 1]:
            return None
        body = parse_body(bits[2:])
        if body is None:
            return None
        g0, s, pairs, G = body
        return ('C', fr, g0, s, tuple(pairs), G)
    body = parse_body(bits)
    if body is None:
        return None
    g0, s, pairs, G = body
    return ('B', fr, g0, s, tuple(pairs), G)


def fmt(sec):
    if sec is None:
        return None
    st, fr, g0, s, pairs, G = sec
    if fr[0] == 'pure':
        frs = f'a={fr[1]}' if st == 'B' else f'a2={fr[1]}'
    else:
        frs = f'frame=({fr[1]}|{fr[2]})'
    return f'{st} {frs} g0={g0} s={s} w={list(pairs)} G={G}'


def absorb(rho, m, budget):
    pairs = [(1, 1)] + [(1, 2)] * (m - 1)
    state, ones = csec_key(16, rho, 2, pairs, 1)
    mach = Machine(state, ones, head=0)
    last_sec = parse_config(mach.state, mach.ones, mach.head)
    min_a2 = 16
    while mach.steps < budget:
        if not mach.step():
            return ('HALT', mach.steps, min_a2, None)
        st = mach.state
        cand = False
        if st == 'B':
            cand = (mach.head not in mach.ones
                    and (mach.head + 1) in mach.ones)
        elif st == 'C':
            cand = (mach.head in mach.ones
                    and (mach.head + 1) in mach.ones)
        if cand:
            sec = parse_config(st, mach.ones, mach.head)
            if sec is not None and sec != last_sec:
                last_sec = sec
                if sec[0] == 'C' and sec[1][0] == 'pure':
                    min_a2 = min(min_a2, sec[1][1])
                if (sec[0] == 'B' and list(sec[4]) == pairs
                        and sec[5] == 1 and sec[2] == 1):
                    return ('absorbed', mach.steps, min_a2, sec)
    return ('budget', mach.steps, min_a2, None)


EXPECTED = {
    33: ('absorbed', 'B a=16 g0=1 s=36 w=[(1, 1)] G=1'),
    35: ('absorbed', 'B a=17 g0=1 s=39 w=[(1, 1)] G=1'),
    37: ('absorbed', 'B frame=(38|17) g0=1 s=4 w=[(1, 1)] G=1'),
    39: ('absorbed', 'B frame=(38|17) g0=1 s=6 w=[(1, 1)] G=1'),
    41: ('absorbed', 'B frame=(38|17) g0=1 s=8 w=[(1, 1)] G=1'),
    36: ('absorbed', 'B frame=(37|17) g0=1 s=2 w=[(1, 1)] G=1'),
    38: ('budget', None),
    40: ('budget', None),
}


def main():
    ok = True
    for rho in [33, 35, 37, 39, 41, 36, 38, 40]:
        st, steps, mina2, land = absorb(rho, 1, 60_000_000)
        got = (st, fmt(land) if land is not None else None)
        want = EXPECTED[rho]
        good = got[0] == want[0] and (want[1] is None or got[1] == want[1])
        ok = ok and good
        print(f'rho={rho}: {st} steps={steps} min_a2={mina2} '
              f'land={got[1]}  '
              f'{"OK" if good else "MISMATCH want=" + str(want)}')
    print('ALL CHECKS PASS' if ok else 'FAILURES PRESENT')
    return 0 if ok else 1


if __name__ == '__main__':
    raise SystemExit(main())
