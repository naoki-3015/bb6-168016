#!/usr/bin/env python3
"""Phase 27 pre-verification: zipper-exact traces for component #16
(re-coordinatisation stages 1-3), the ESC probe prefix (Thm P20.1)
and the POP2 transfer.  Configs are built EXACTLY as the Rocq
definitions in TM.v / Sections.v / Mirror.v build them (lists,
nearest-first left), stepped with the same transition table, and
compared for literal equality at the predicted step counts."""
SPEC = "1RB1RA_1RC1LB_0LD0RA_1RF1LE_---1LF_1LC0LF"
SA, SB, SC, SD, SE, SF = range(6)
SN = "ABCDEF"

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
T, F = True, False

def rep(b, n):
    return [b] * n

def rtail(pairs):
    out = []
    for g, r in pairs:
        out += rep(F, g) + rep(T, r)
    return out

def tail(pairs, G):
    if not pairs:
        return rep(F, G) + [T, T]
    g, r = pairs[0]
    return rep(F, g) + rep(T, r) + tail(pairs[1:], G)

def rcsec(P, b2, pairs):
    return (SC, rep(T, b2) + P, [T, T] + rtail(pairs))

def rbsec(P, b, pairs):
    return (SB, rep(T, b) + P, rtail(pairs))

def rcsec_probe(P, b, g):
    return (SC, rep(T, b) + P, [T, T] + rep(F, g) + [T, T, F])

def csec(a2, g0, s, pairs, G):
    return (SC, rep(T, a2),
            [T, T] + rep(F, g0) + rep(T, s) + tail(pairs, G))

def bsec(a, g0, s, pairs, G):
    return (SB, rep(T, a), rep(F, g0) + rep(T, s) + tail(pairs, G))

def step(c):
    st, l, r = c
    sym = r[0] if r else F
    tr = TM[st][sym]
    assert tr is not None, "HALT"
    w, mv, nx = tr
    w = bool(w)
    if mv == 1:  # DR
        return (nx, [w] + l, r[1:])
    # DL
    return (nx, l[1:], [(l[0] if l else F), w] + r[1:])

def run(n, c):
    for _ in range(n):
        c = step(c)
    return c

def show(c):
    st, l, r = c
    def rle(lst):
        out = []
        for v in lst:
            if out and out[-1][0] == v:
                out[-1][1] += 1
            else:
                out.append([v, 1])
        return ' '.join('%d:%d' % (int(v), n) for v, n in out)
    return 'st=%s L[%s] R[%s]' % (SN[st], rle(l), rle(r))

ok = True
def check(label, got, want):
    global ok
    good = got == want
    ok = ok and good
    print(('PASS ' if good else 'FAIL ') + label)
    if not good:
        print('  got ', show(got))
        print('  want', show(want))

if __name__ == '__main__':
    # ---------------- Stage 1: RPOP chain + RPROBE ----------------
    # Entry prefix for B2 = 31: P = 0 1^32 0 1^17 (nearest first).
    P31 = [F] + rep(T, 32) + [F] + rep(T, 17)
    for n in (2, 4, 6, 10):
        src = rbsec(P31, 0, [(1, 4)] + [(1, 2)] * n)
        for j in range(n + 1):
            want = rbsec(P31, j, [(1, 2 * j + 4)] + [(1, 2)] * (n - j))
            check(f'stage1 n={n} j={j} cost={2*j*j+9*j}',
                  run(2 * j * j + 9 * j, src), want)
        tot = 2 * n * n + 13 * n + 14
        want = rcsec_probe(P31, n, 2 * n + 3)
        check(f'stage1 n={n} RPROBE total={tot}', run(tot, src), want)

    # ---------------- Stage 2: section trace ----------------
    def parse_mirror(c, P):
        """Parse c as rcsec/rbsec over prefix P; return (form, b, pairs)."""
        st, l, r = c
        b = 0
        while b < len(l) and l[b] and (len(l) - b > len(P) or l[b:] != P):
            b += 1
        if l[b:] != P:
            return None
        if st == SC:
            if r[:2] != [T, T]:
                return None
            rr = r[2:]
        elif st == SB:
            rr = r
        else:
            return None
        pairs = []
        i = 0
        while i < len(rr):
            g = 0
            while i < len(rr) and not rr[i]:
                g += 1; i += 1
            rn = 0
            while i < len(rr) and rr[i]:
                rn += 1; i += 1
            if rn == 0:
                return ('tail', b, pairs, rr)
            pairs.append((g, rn))
        return (SN[st], b, pairs)

    def trace_stage2(n):
        P = P31
        c = rcsec(P, n, [(2 * n + 3, 2)])
        print(f'--- stage2 trace n={n} (betaE={n+2}) ---')
        t = 0
        prev = None
        while True:
            p = parse_mirror(c, P)
            if p and (len(p) == 3):
                form, b, pairs = p
                gaps = tuple(g for g, _ in pairs)
                runs = tuple(r for _, r in pairs)
                key = (form, b, gaps, runs)
                if key != prev:
                    print(f'  t={t:8d} {form} b={b} gaps={gaps} runs={runs}')
                    prev = key
                if form == 'C' and b == 0 and gaps and gaps[0] == 3:
                    print(f'  ESCAPE at t={t}')
                    return c, t
            c = step(c)
            t += 1
            if t > 3000000:
                print('  (trace cap)'); return c, t

    for n in (2, 4):
        trace_stage2(n)

    # ---------------- Stage 3: RPUSH escape + F-sweep ----------------
    for (L, B2, n) in ((17, 31, 2), (17, 31, 6), (17, 3, 6), (17, 21, 2),
                       (5, 7, 4), (1, 2, 2)):
        P3 = [F] + rep(T, B2) + [F] + rep(T, L)
        src = rcsec(P3, 0, [(3, 2)] + [(1, 2)] * n)
        want = csec(L - 1, B2 - 2, 2, [(1, 1)] + [(1, 2)] * (n + 1), 1)
        check(f'stage3 L={L} B2={B2} n={n} cost={B2+11}',
              run(B2 + 11, src), want)

    print('ALL OK' if ok else 'SOME FAILED')
