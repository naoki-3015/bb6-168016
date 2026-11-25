#!/usr/bin/env python3
"""Phase 40 verification: the phase-7 merged unwind (R >= 604).

The Phase 38 fence: at R = 2m + 46 with m >= 279, phase 6's finish
(ESC_TO_REGEN_BIG6 in Grind7.v) breaks at the new frame
([110; 19; 0], 164): the rounds (count m - 115) and the final grind
(t = m - 115, floor t + 1 <= 164) both bind.  Taking the maximal
164 clean rounds leaves the final grind at exactly t = 164 = a2
over the passenger residue ((2m - 556, 2) :: Pe): a boundary grind.
Its descent is DIPDESC 164 (Grind7.v, pb-general), the dip at
[110; 19; 0] fires the existing hPX2A, landing at
HC [0] 18 108 2 with the dispatch's three extra pairs over the
(1, 2)^164 spine.  The continuation grind at ([0], 18), g0 = 108
(GRIND108_MID in Grind8.v) parses as:

  PUSH/TDN/TUP, LOOPN 17 (floor-exact), DIPDESC 17, hPX2B0,
  POP x18, TUP           -> HC [] 18 40 2 ((68, 2) :: Q0)
  PUSH/TDN/TUP, LOOPN 17 (floor-exact; (36, 2) ground to (2, 2)),
  PUSH/TDN/TUP, LOOPN 16 (floor-exact; (33, 2) to (1, 2)),
  DIPDESC 16, hPUSHX, POP x17, hTUP2_1, TDN, TUP
                         -> HC [19] 41 3 2 ((64, 2) :: Q0)
  LOOPN 31, PUSH/TDN/TUP, LOOPN 30, hGRIND 30, POP, hTRANS2_1,
  POP chain over the spine
                         -> HB [42; 19] (71 + n) 1 (7 + 2n) Rest

This file verifies the parse:
  * the hPX2A dispatch at the real phase-7 dip shape, and
    DIPDESC at [110; 19; 0] for small t;
  * stage A (source -> HC [] 18 40 2) and stage B (-> HC [19] 41
    3 2) as primitive word walks AT THE REAL PARAMETERS
    (about 10^6 rules each);
  * stage C at the real frame ([19], 41) with a shrunk passenger
    (30, 2) (LOOPN 31 at the real passenger is 2^33 rules --
    beyond any primitive walk);
  * the whole GRIND108 parse at two shrunk analogues
    (a2, g0) = (6, 36) and (8, 48), which preserve every
    arithmetic accident of the real parse (the floor-exact
    LOOPNs, the even-grind boundary shape g0 = 2*a2 + 4, the
    PX2B0 / PUSHX dips, TUP2_1, TRANS2_1), at spine n in {0, 2};
  * word/machine boundary agreement for analogue (6, 36) at
    (n, beta) = (0, 2);
  * the finishes: the transitional segment into frame
    ([110; 19; 0], 164) (shrunk), TAIL at the phase-7 landing
    (m = 279 analogue), the m = 280 analogue (TUP + hGRIND_even
    + TAIL2), the m = 281 analogue (transitional + TAIL), and
    the BIG7 analogue (transitional + rounds + final grind
    + TAIL at a shrunk frame).

Run:  python3 hsim40.py     (all checks assert; prints PASS lines)
"""
import os
import sys

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from hsim36 import step_all, run_chain, recognise, as_record, hc, enc
from trace_dev import Z, tail


def hb(pb, a, s, pairs, G):
    left = [1] * a + enc(list(pb))
    right = [0] + [1] * s + tail(list(pairs), G)
    return Z(left, right, 1)


def walk_stream(src, bounds, label, max_steps=3000000):
    """Follow the unique constructor without retaining the chain;
    assert every predicted boundary section occurs, in order;
    stop as soon as the last boundary is reached."""
    bi = 0
    cur = src
    steps = 0
    total = 0
    if bounds and cur == bounds[0]:
        bi = 1
    while steps < max_steps and bi < len(bounds):
        opts = step_all(cur)
        if not opts:
            break
        assert len(opts) == 1, (label, cur, opts)
        rule, nxt, cost = opts[0]
        total += cost
        steps += 1
        if rule == 'ENTRY':
            cur = nxt
            break
        cur = nxt
        if bi < len(bounds) and cur == bounds[bi]:
            bi += 1
    assert bi == len(bounds), (label, f"boundary {bi}/{len(bounds)}",
                               cur)
    print(f"PASS {label} ({steps} rules, {total} machine steps)")


def walk_to(src, tgt, label, max_steps=200000):
    cur = src
    steps = 0
    while steps < max_steps:
        if cur == tgt:
            print(f"PASS {label} ({steps} rules)")
            return
        opts = step_all(cur)
        assert opts and len(opts) == 1, (label, cur, opts)
        rule, nxt, cost = opts[0]
        steps += 1
        cur = nxt
    raise AssertionError((label, 'target not reached', cur))


PE2 = [(1, 1), (1, 2)]  # beta = 2 era stack


def q0(n, rest):
    return [(1, 1), (1, 2), (1, 2)] + [(1, 2)] * n + list(rest)


# ------------------------------------------------------------------
# The dip dispatch and DIPDESC at the phase-7 prefix.
# ------------------------------------------------------------------

def check_px2a_dip():
    src = ('C', (110, 19, 0), 0, 3, 2,
           tuple([(1, 2)] * 2 + [(6, 2)] + PE2), 1)
    opts = step_all(src)
    assert len(opts) == 1 and opts[0][0] == 'PX2A', opts
    tgt = ('C', (0,), 18, 108, 2,
           tuple([(1, 1), (1, 2), (1, 2)] + [(1, 2)] * 2
                 + [(6, 2)] + PE2), 1)
    assert opts[0][1] == tgt, opts[0][1]
    print("PASS hPX2A dispatch at the phase-7 dip shape "
          "[110; 19; 0] -> HC [0] 18 108 2")


def check_dipdesc_110():
    P = [(4, 2), (1, 1), (1, 2)]
    for t in (1, 2, 3):
        src = ('C', (110, 19, 0), t, 2 * t + 3, 2, tuple(P), 1)
        tgt = ('C', (110, 19, 0), 0, 3, 2,
               tuple([(1, 2)] * t + P), 1)
        walk_to(src, tgt, f"DIPDESC boundary pb=[110; 19; 0] t={t}")


# ------------------------------------------------------------------
# GRIND108 stages A and B at the real parameters.
# ------------------------------------------------------------------

def check_stageA_real():
    n = 0
    rest = [(2, 2)] + PE2
    Q = q0(n, rest)
    src = ('C', (0,), 18, 108, 2, tuple(Q), 1)
    bounds = [
        ('C', (0,), 17, 3, 2, tuple([(104, 2)] + Q), 1),     # P/T/T
        ('C', (0,), 17, 37, 2, tuple([(70, 2)] + Q), 1),     # LOOPN 17
        ('C', (0,), 0, 3, 2,
         tuple([(1, 2)] * 17 + [(70, 2)] + Q), 1),           # DIPDESC 17
        ('B', (), 0, 1, 5,
         tuple([(1, 2)] * 18 + [(70, 2)] + Q), 1),           # PX2B0
        ('B', (), 18, 1, 41, tuple([(70, 2)] + Q), 1),       # POP x18
        ('C', (), 18, 40, 2, tuple([(68, 2)] + Q), 1),       # TUP
    ]
    walk_stream(src, bounds, "GRIND108 stage A at real parameters (n=0)")


def check_stageB_real():
    n = 0
    rest = [(2, 2)] + PE2
    Q = q0(n, rest)
    src = ('C', (), 18, 40, 2, tuple([(68, 2)] + Q), 1)
    bounds = [
        ('C', (), 17, 3, 2, tuple([(36, 2), (68, 2)] + Q), 1),  # P/T/T
        ('C', (), 17, 37, 2, tuple([(2, 2), (68, 2)] + Q), 1),  # LOOPN 17
        ('C', (), 16, 3, 2,
         tuple([(33, 2), (2, 2), (68, 2)] + Q), 1),             # P/T/T
        ('C', (), 16, 35, 2,
         tuple([(1, 2), (2, 2), (68, 2)] + Q), 1),              # LOOPN 16
        ('C', (), 0, 3, 2,
         tuple([(1, 2)] * 16 + [(1, 2), (2, 2), (68, 2)] + Q), 1),
        ('B', (), 1, 1, 7,
         tuple([(1, 2)] * 16 + [(1, 2), (2, 2), (68, 2)] + Q), 1),
        ('B', (), 18, 1, 41, tuple([(2, 2), (68, 2)] + Q), 1),  # POP x17
        ('C', (19,), 41, 1, 2, tuple([(66, 2)] + Q), 1),        # TUP2_1
        ('B', (19,), 41, 1, 4, tuple([(66, 2)] + Q), 1),        # TDN
        ('C', (19,), 41, 3, 2, tuple([(64, 2)] + Q), 1),        # TUP
    ]
    walk_stream(src, bounds, "GRIND108 stage B at real parameters (n=0)")


# ------------------------------------------------------------------
# Stage C at the real frame ([19], 41), shrunk passenger (30, 2).
# ------------------------------------------------------------------

def check_stageC_frame():
    n = 2
    rest = [(2, 2)] + PE2
    Q = q0(n, rest)
    src = ('C', (19,), 41, 3, 2, tuple([(30, 2)] + Q), 1)
    bounds = [
        ('C', (19,), 41, 31, 2, tuple([(2, 2)] + Q), 1),      # LOOPN 14
        ('C', (19,), 40, 3, 2, tuple([(27, 2), (2, 2)] + Q), 1),
        ('C', (19,), 40, 29, 2, tuple([(1, 2), (2, 2)] + Q), 1),
        ('B', (19,), 40, 1, 32, tuple([(1, 2), (2, 2)] + Q), 1),
        ('B', (19,), 41, 1, 34, tuple([(2, 2)] + Q), 1),      # POP
        ('B', (42, 19), 35, 1, 3,
         tuple([(1, 2)] * (n + 2) + rest), 1),                 # TRANS2_1
        ('B', (42, 19), 37 + n, 1, 7 + 2 * n, tuple(rest), 1),  # POP chain
    ]
    walk_stream(src, bounds, "GRIND108 stage C at the real frame "
                             "([19], 41), passenger (30, 2)")


# ------------------------------------------------------------------
# The whole GRIND108 parse at shrunk analogues (a2, g0).
#
# With a = a2 - 1 the parse's parameters are forced:
#   stage A: passenger g1 = g0 - 4 after PUSH/TDN/TUP; LOOPN a
#     (floor-exact) leaves p1 = g1 - 2a; DIPDESC a; PX2B0; the POP
#     run lands at sB = 2a + 7.
#   stage B: source shuttle gB = 2a + 6 = 2*a2 + 4 (the even-grind
#     boundary shape -- asserted); its two loops are floor-exact
#     for every a2 (pushed pairs 2a + 2 and 2a - 1 grind to (2, 2)
#     and (1, 2) in exactly a and a - 1 iterations); DIPDESC (a-1);
#     PUSHX; TUP2_1 onto frame fC = sB at pbC = a2 + 1.
#   stage C: passenger pC = p1 - 4; LOOPN cnt1 = (pC - 4)/2 to
#     (2, 2); LOOPN cnt2 = cnt1 - 1 to (1, 2); hGRIND cnt2; POP;
#     TRANS2_1; POP chain.  Landing a = 2*cnt2 + 9 + n + 2,
#     s = 7 + 2n.
# ------------------------------------------------------------------

def grind108_analogue(a2, g0, n, rest):
    Q = q0(n, rest)
    a = a2 - 1
    g1 = g0 - 4
    p1 = g1 - 2 * a
    sB = 2 * a + 7
    gB = 2 * a + 6
    assert gB == 2 * a2 + 4, (a2, g0, gB)
    fC = sB
    pbC = (a2 + 1,)
    pC = p1 - 4
    cnt1 = (pC - 4) // 2
    cnt2 = cnt1 - 1
    aT = 2 * cnt2 + 9
    pbL = (fC + 1,) + pbC
    land = ('B', pbL, aT + n + 2, 1, 7 + 2 * n, tuple(rest), 1)
    src = ('C', (0,), a2, g0, 2, tuple(Q), 1)
    bounds = [
        ('C', (0,), a, 3, 2, tuple([(g1, 2)] + Q), 1),
        ('C', (0,), a, 2 * a + 3, 2, tuple([(p1, 2)] + Q), 1),
        ('C', (0,), 0, 3, 2, tuple([(1, 2)] * a + [(p1, 2)] + Q), 1),
        ('B', (), 0, 1, 5, tuple([(1, 2)] * (a + 1) + [(p1, 2)] + Q), 1),
        ('B', (), a2, 1, sB, tuple([(p1, 2)] + Q), 1),
        ('C', (), a2, gB, 2, tuple([(p1 - 2, 2)] + Q), 1),
        ('C', (), a, 3, 2, tuple([(gB - 4, 2), (p1 - 2, 2)] + Q), 1),
        ('C', (), a, 2 * a + 3, 2, tuple([(2, 2), (p1 - 2, 2)] + Q), 1),
        ('C', (), a - 1, 3, 2,
         tuple([(gB - 7, 2), (2, 2), (p1 - 2, 2)] + Q), 1),
        ('C', (), a - 1, 2 * a + 1, 2,
         tuple([(1, 2), (2, 2), (p1 - 2, 2)] + Q), 1),
        ('C', (), 0, 3, 2,
         tuple([(1, 2)] * (a - 1) + [(1, 2), (2, 2), (p1 - 2, 2)]
               + Q), 1),
        ('B', (), 1, 1, 7,
         tuple([(1, 2)] * (a - 1) + [(1, 2), (2, 2), (p1 - 2, 2)]
               + Q), 1),
        ('B', (), a2, 1, sB, tuple([(2, 2), (p1 - 2, 2)] + Q), 1),
        ('C', pbC, fC, 1, 2, tuple([(pC, 2)] + Q), 1),
        ('B', pbC, fC, 1, 4, tuple([(pC, 2)] + Q), 1),
        ('C', pbC, fC, 3, 2, tuple([(pC - 2, 2)] + Q), 1),
        ('C', pbC, fC, 2 * cnt1 + 3, 2, tuple([(2, 2)] + Q), 1),
        ('C', pbC, fC - 1, 3, 2, tuple([(pC - 5, 2), (2, 2)] + Q), 1),
        ('C', pbC, fC - 1, 2 * cnt2 + 3, 2,
         tuple([(1, 2), (2, 2)] + Q), 1),
        ('B', pbC, fC - 1, 1, 2 * cnt2 + 6,
         tuple([(1, 2), (2, 2)] + Q), 1),
        ('B', pbC, fC, 1, 2 * cnt2 + 8, tuple([(2, 2)] + Q), 1),
        ('B', pbL, aT, 1, 3, tuple([(1, 2)] * (n + 2) + rest), 1),
        land,
    ]
    return src, bounds, land


def check_analogue(a2, g0, n):
    rest = [(2, 2)] + PE2
    src, bounds, land = grind108_analogue(a2, g0, n, rest)
    walk_stream(src, bounds,
                f"GRIND108 shrunk analogue (a2={a2}, g0={g0}, n={n})")


def check_analogue_machine():
    a2, g0, n = 6, 36, 0
    rest = [(2, 2)] + PE2
    src, bounds, land = grind108_analogue(a2, g0, n, rest)
    ch, st = run_chain(src, max_steps=200000)
    secs = [src] + [nxt for (_, _, nxt) in ch]
    assert land in secs, (st, secs[-1])
    z = hc((0,), a2, g0, 2, tuple(q0(n, rest)), 1)
    assert as_record(src) in recognise(z)
    bset = list(bounds)
    hit = 0
    for rule, cost, nxt in ch:
        for _ in range(cost):
            z.step()
        if hit < len(bset) and nxt == bset[hit]:
            rec = recognise(z)
            assert as_record(nxt) in rec, (rule, nxt, rec)
            hit += 1
    assert hit == len(bset), (hit, len(bset))
    print(f"PASS GRIND108 analogue word/machine boundary agreement "
          f"({len(ch)} rules)")


# ------------------------------------------------------------------
# The finishes.
# ------------------------------------------------------------------

def check_finishes():
    # transitional segment into frame ([110; 19; 0], 164), shrunk:
    # HB [19; 0] 10 1 21 ((12, 2) :: Pe) -> HB [10; 19; 0] 20 1 4
    walk_stream(('B', (19, 0), 10, 1, 21, tuple([(12, 2)] + PE2), 1),
                [('C', (19, 0), 10, 20, 2, tuple([(10, 2)] + PE2), 1),
                 ('B', (19, 0), 9, 1, 20,
                  tuple([(2, 2), (10, 2)] + PE2), 1),
                 ('C', (10, 19, 0), 20, 1, 2, tuple([(8, 2)] + PE2), 1),
                 ('B', (10, 19, 0), 20, 1, 4, tuple([(8, 2)] + PE2), 1)],
                "transitional segment analogue "
                "(TUP + hGRIND_even + TUP2_1 + TDN)")
    # m = 279 analogue: TAIL at the phase-7 landing shape
    walk_stream(('B', (42, 19), 12, 1, 21, tuple([(2, 2)] + PE2), 1),
                [('B', (13, 42, 19), 23, 1, 5, (), 1)],
                "finish analogue m=279 (TAIL)")
    # m = 280 analogue: TUP + hGRIND_even + TAIL2
    walk_stream(('B', (42, 19), 12, 1, 21, tuple([(4, 2)] + PE2), 1),
                [('C', (42, 19), 12, 20, 2, tuple([(2, 2)] + PE2), 1),
                 ('B', (42, 19), 11, 1, 20,
                  tuple([(2, 2), (2, 2)] + PE2), 1),
                 ('B', (21, 12, 42, 19), 3, 1, 3, ((1, 2),), 1),
                 ('B', (21, 12, 42, 19), 4, 1, 5, (), 1)],
                "finish analogue m=280 (TUP + hGRIND_even + TAIL2)")
    # m = 281 analogue: transitional + TAIL at the new frame
    walk_stream(('B', (42, 19), 12, 1, 21, tuple([(6, 2)] + PE2), 1),
                [('C', (42, 19), 12, 20, 2, tuple([(4, 2)] + PE2), 1),
                 ('B', (42, 19), 11, 1, 20,
                  tuple([(2, 2), (4, 2)] + PE2), 1),
                 ('C', (12, 42, 19), 20, 1, 2, tuple([(2, 2)] + PE2), 1),
                 ('B', (12, 42, 19), 20, 1, 4, tuple([(2, 2)] + PE2), 1),
                 ('B', (21, 12, 42, 19), 6, 1, 5, (), 1)],
                "finish analogue m=281 (transitional + TAIL)")
    # BIG7 analogue: transitional + 3 rounds + final grind + TAIL
    walk_stream(('B', (42, 19), 12, 1, 21, tuple([(14, 2)] + PE2), 1),
                [('B', (12, 42, 19), 20, 1, 4, tuple([(10, 2)] + PE2), 1),
                 ('B', (12, 42, 19), 20, 1, 10, tuple([(4, 2)] + PE2), 1),
                 ('C', (12, 42, 19), 20, 9, 2, tuple([(2, 2)] + PE2), 1),
                 ('B', (12, 42, 19), 20, 1, 12, tuple([(2, 2)] + PE2), 1),
                 ('B', (21, 12, 42, 19), 14, 1, 5, (), 1)],
                "BIG7 analogue (transitional + 3 rounds + final "
                "grind + TAIL)")


def main():
    check_px2a_dip()
    check_dipdesc_110()
    check_stageA_real()
    check_stageB_real()
    check_stageC_frame()
    check_analogue(6, 36, 0)
    check_analogue(6, 36, 2)
    check_analogue(8, 48, 0)
    check_analogue(8, 48, 2)
    check_analogue_machine()
    check_finishes()
    print("ALL PHASE 40 CHECKS PASS")


if __name__ == '__main__':
    main()
