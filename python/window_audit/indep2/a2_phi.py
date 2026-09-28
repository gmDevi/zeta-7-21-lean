# Auditor-2 (window): phi(x) = min_y phi0(x,y) for cfgW, the integral int_{1/60}^inf phi dx/x^2 (C2),
# and a check of the Lean table Zeta2Lean/Window/PhiTable.lean (validity of every piece, phiSumQ).
# Breakpoint set computed from the actual coefficient set (not assumed Farey-160).
import re, sys, time
from fractions import Fraction as Fr
import mpmath as mp

r, q, e0 = 5, 23, 160
eta = [47, 47, 47, 47, 48, 50, 50] + [j + 43 for j in range(8, 24)]
# phi0 literally as in Defs.lean, as a list of (coef, alpha, beta): coef * floor(alpha x + beta y)
T = []
for j in range(r):
    e = eta[j]
    T += [(1, 0, 1), (1, e0, -1), (-1, -e, 1), (-1, e0 - e, -1), (-2, e, 0)]
for j in range(r, q):
    e = eta[j]
    T += [(1, e0 - 2 * e, 0), (-1, -e, 1), (-1, e0 - e, -1)]

def phi0(P, Q, Y):          # x = P/Q, y = Y/(2Q)
    return sum(c * ((2 * a * P + b * Y) // (2 * Q)) for c, a, b in T)

def phi(x):
    P, Q = x.numerator, x.denominator
    th = sorted({(-b * a * P) % Q for c, a, b in T if b != 0} | {0})   # thresholds * Q
    ys = [2 * t for t in th] + [th[i] + (th[i + 1] if i + 1 < len(th) else Q) for i in range(len(th))]
    return min(phi0(P, Q, Y) for Y in ys)

# denominators of breakpoints: x-only coefficients, y-term coefficients, and pairwise differences
xonly = {abs(a) for c, a, b in T if b == 0 and a != 0}
ycoef = sorted({-a * b for c, a, b in T if b != 0} | {0})
D = set(xonly) | {abs(a) for a in ycoef if a} | {abs(a - b) for a in ycoef for b in ycoef if a != b}
print("max breakpoint denominator:", max(D), " #D =", len(D))
bp = sorted({Fr(u, d) for d in D for u in range(0, d + 1)})
print("breakpoints in [0,1]:", len(bp))

t0 = time.time()
vals = []          # phi on open intervals (bp[i], bp[i+1])
for i in range(len(bp) - 1):
    vals.append(phi((bp[i] + bp[i + 1]) / 2))
atbp = [phi(x) if x != 0 else None for x in bp]
print("phi evaluated in %.1f s; min on intervals %d, min at breakpoints %d" % (time.time() - t0, min(vals), min(v for v in atbp if v is not None)))
# extra adversarial sampling: 3 more interior points per interval must give the same value (type constant)
bad = 0
for i in range(len(bp) - 1):
    a, b = bp[i], bp[i + 1]
    for w in (Fr(1, 7), Fr(3, 5), Fr(97, 100)):
        if phi(a + (b - a) * w) != vals[i]:
            bad += 1
print("interval-constancy violations (3 extra points per interval):", bad)

# the integral: int_{1/60}^1 phi dx/x^2 + sum_{m>=1} int_0^1 phi(x)/(x+m)^2 dx
mp.mp.dps = 30
I0 = mp.mpf(0); I1 = mp.mpf(0)
for i, v in enumerate(vals):
    if v == 0: continue
    a, b = bp[i], bp[i + 1]
    if a >= Fr(1, 60):
        I0 += v * (mp.mpf(b.denominator) / b.numerator - (mp.mpf(a.denominator) / a.numerator if a else 0))
    # sum_{m>=1} (1/(a+m) - 1/(b+m)) = psi(1+b) - psi(1+a)
    I1 += v * (mp.digamma(1 + mp.mpf(b.numerator) / b.denominator) - mp.digamma(1 + mp.mpf(a.numerator) / a.denominator))
I0 = -I0  # 1/a - 1/b
print("int_[1/60,1) phi/x^2 =", mp.nstr(I0, 22))
print("int_[1,inf)  phi/x^2 =", mp.nstr(I1, 22))
print("int total            =", mp.nstr(I0 + I1, 22))
print("C2 = 1341 - int      =", mp.nstr(1341 - I0 - I1, 22))

# the Lean table
src = open(sys.argv[1], encoding='utf-8').read()
pieces = [tuple(int(z) for z in m) for m in re.findall(r"⟨(\d+), (\d+), (\d+), (\d+), (\d+)⟩", src)]
print("Lean table pieces:", len(pieces))
import bisect
viol = 0
for an, ad, bn, bd, v in pieces:
    a, b = Fr(an, ad), Fr(bn, bd)
    i = bisect.bisect_right(bp, a) - 1          # interval containing a (a itself may be a breakpoint)
    while i < len(bp) - 1 and bp[i] < b:
        if bp[i + 1] > a and vals[i] < v: viol += 1       # open interval meets (a,b)
        if a < bp[i] < b and atbp[i] < v: viol += 1       # breakpoint strictly inside
        i += 1
print("table violations:", viol)
S = Fr(0)
for an, ad, bn, bd, v in pieces:
    a, b = Fr(an, ad), Fr(bn, bd)
    w = (1 / a - 1 / b) if Fr(1, 60) <= a else Fr(0)
    w += sum(Fr(1) / (a + m) - Fr(1) / (b + m) for m in range(1, 21))
    S += v * w
print("phiSumQ(table, 60, 20) =", float(S), " 1341 - it =", float(1341 - S), " < 748:", 1341 - S < 748)
# coverage: which positive-phi intervals are not inside a table piece (only affects tightness)
cov = [False] * len(vals)
for an, ad, bn, bd, v in pieces:
    a, b = Fr(an, ad), Fr(bn, bd)
    for i in range(bisect.bisect_left(bp, a), len(bp) - 1):
        if bp[i] >= b: break
        if bp[i + 1] <= b: cov[i] = True
print("positive-phi intervals not covered by the table:", sum(1 for i, v in enumerate(vals) if v > 0 and not cov[i]))
