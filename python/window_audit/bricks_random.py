# Random tests of Stmt_BrickInt, Stmt_BrickVal, Stmt_Harmonic, Stmt_OmegaPhi0 (Lean definitions, literally).
import random, math
from fractions import Fraction as Fr
from exact_indep import polyBrick, ratBrick, vp, lcm_upto, primes_upto, omegaKP
random.seed(2026)
fails = []; cnt = 0
def fl(a, b):  # Lean Int.ediv for b > 0 == floor
    return a // b
def wPoly(a, b, k, p): return fl(k - b, p) - fl(k - a, p) - fl(a - b, p)
def wRat(a, b, k, p): return fl(b - a - 1, p) - fl(k - a, p) - fl(b - 1 - k, p)
P = primes_upto(60)
for it in range(400):
    N = random.randint(1, 60)
    # poly: 1 <= b <= a <= N, k <= N  (BrickInt.poly: any k, b <= a)
    a = random.randint(1, N); b = random.randint(1, a); k = random.randint(0, N)
    deg = a - b + 3
    s = polyBrick(a, b, k, deg)
    D = lcm_upto(a - b)
    for i in range(deg + 1):
        cnt += 1
        if (Fr(D) ** i * s[i]).denominator != 1: fails.append(("BrickInt.poly", a, b, k, i))
        for p in P:
            if N < p * p and s[i] != 0 and vp(p, s[i]) < wPoly(a, b, k, p) - i: fails.append(("BrickVal.poly", a, b, k, p, i))
    # rat: 1 <= a < b <= N+1, k <= N  (BrickVal) ; BrickInt.rat: a0 <= a < b <= b0, a0 <= k < b0
    a = random.randint(1, N); b = random.randint(a + 1, N + 1); k = random.randint(0, N)
    deg = 8
    s = ratBrick(a, b, k, deg)
    for i in range(deg + 1):
        cnt += 1
        for p in P:
            if N < p * p and s[i] != 0 and vp(p, s[i]) < wRat(a, b, k, p) - i: fails.append(("BrickVal.rat", a, b, k, p, i))
    a0 = random.randint(0, a); b0 = random.randint(b, b + 10); k2 = random.randint(a0, b0 - 1)
    s2 = ratBrick(a, b, k2, deg)
    D = lcm_upto(b0 - a0 - 1)
    for i in range(deg + 1):
        cnt += 1
        if (Fr(D) ** i * s2[i]).denominator != 1: fails.append(("BrickInt.rat", a, b, k2, a0, b0, i))
# Harmonic
for it in range(300):
    Nn = random.randint(0, 80); m = random.randint(Nn, 90); s = random.randint(0, 12)
    H = sum((Fr(1, l ** s) for l in range(1, Nn + 1)), Fr(0))
    cnt += 1
    if (Fr(lcm_upto(m)) ** s * H).denominator != 1: fails.append(("Harm.int", Nn, m, s))
    for p in P:
        if Nn < p * p and H != 0 and vp(p, H) < -s: fails.append(("Harm.val", Nn, s, p))
# OmegaPhi0 on cfgW and random configs, arbitrary n, p > 0, k (also k = 0, k > h0)
def phi0(r, q, e0, eta, x, y):
    F = math.floor
    s = 0
    for j in range(r):
        s += F(y) + F(e0 * x - y) - F(y - eta[j] * x) - F((e0 - eta[j]) * x - y) - 2 * F(eta[j] * x)
    for j in range(r, q):
        s += F((e0 - 2 * eta[j]) * x) - F(y - eta[j] * x) - F((e0 - eta[j]) * x - y)
    return s
cfgs = [(5, 23, 160, [47, 47, 47, 47, 48, 50, 50] + [j + 43 for j in range(8, 24)]), (3, 13, 91, [27, 27, 27] + [25 + j for j in range(4, 14)]),
        (3, 7, 5, [1] * 7), (7, 11, 3, [9, 1, 4, 4, 2, 8, 8, 1, 1, 0, 5])]   # last one: NOT admissible (identity is config-free)
for it in range(3000):
    r, q, e0, eta = random.choice(cfgs)
    n = random.randint(0, 50); p = random.randint(1, 400); k = random.randint(0, 3 * (e0 * n + 2) + 5)
    h0 = e0 * n + 2; h = [e * n + 1 for e in eta]
    cnt += 1
    if omegaKP(r, q, h0, h, p, k) != phi0(r, q, e0, eta, Fr(n, p), Fr(k - 1, p)): fails.append(("OmegaPhi0", r, q, n, p, k))
print("checks:", cnt, " failures:", len(fails), fails[:8])
