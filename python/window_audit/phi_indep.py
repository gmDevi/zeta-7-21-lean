# Independent recomputation of Zudilin's phi-function for cfgW and of C2.
# Auditor's code (not derived from vz.py / window_phitable.py).
# phi0(x,y) = sum_{j<=r} (fl(y) + fl(e0 x - y) - fl(y - e_j x) - fl((e0-e_j)x - y) - 2 fl(e_j x))
#           + sum_{j>r} (fl((e0-2e_j)x) - fl(y - e_j x) - fl((e0-e_j)x - y))
# phi(x) = min_y phi0(x,y).  Breakpoints of phi have denominators <= 160, so the Farey
# sequence of order 160 is a superset of the breakpoints.
import re, sys, math
from fractions import Fraction as Fr
import mpmath as mp

r, q, e0 = 5, 23, 160
def etaW(j):
    if j <= 4: return 47
    if j == 5: return 48
    if j <= 7: return 50
    return j + 43
eta = {j: etaW(j) for j in range(1, q + 1)}

# compressed terms: (alpha, beta) -> coefficient, term = coef * floor(alpha x + beta y)
terms = {}
def add(a, b, c):
    terms[(a, b)] = terms.get((a, b), 0) + c
for j in range(1, r + 1):
    add(0, 1, 1); add(e0, -1, 1); add(-eta[j], 1, -1); add(e0 - eta[j], -1, -1); add(eta[j], 0, -2)
for j in range(r + 1, q + 1):
    add(e0 - 2 * eta[j], 0, 1); add(-eta[j], 1, -1); add(e0 - eta[j], -1, -1)
terms = [(a, b, c) for (a, b), c in terms.items() if c != 0]
# periodicity sanity: sum c*alpha = 0, sum c*beta = 0
assert sum(c * a for a, b, c in terms) == 0 and sum(c * b for a, b, c in terms) == 0

def phi0_int(P, Q, Y):
    # x = P/Q, y = Y/(2Q)
    s = 0
    for a, b, c in terms:
        s += c * ((2 * a * P + b * Y) // (2 * Q))
    return s

def phi(x):
    x = Fr(x)
    P, Q = x.numerator, x.denominator
    crit = {0}
    for a, b, c in terms:
        if b != 0:
            crit.add(2 * ((-b * a * P) % Q))
    crit = sorted(crit)
    cand = list(crit)
    for i in range(len(crit)):
        nxt = crit[i + 1] if i + 1 < len(crit) else 2 * Q
        cand.append((crit[i] + nxt) // 2)
    return min(phi0_int(P, Q, Y) for Y in cand)

def farey(N):
    a, b, c, d = 0, 1, 1, N
    out = [Fr(0)]
    while c <= N:
        k = (N + b) // d
        a, b, c, d = c, d, k * c - a, k * d - b
        out.append(Fr(a, b))
    return out

F = farey(160)
print("Farey-160 points:", len(F))
vals = []  # (a, b, phi on (a,b))
for i in range(len(F) - 1):
    a, b = F[i], F[i + 1]
    vals.append((a, b, phi((a + b) / 2)))
ptval = {x: phi(x) for x in F[1:-1]}
print("min phi on open Farey intervals:", min(v for _, _, v in vals))
print("min phi at Farey points:", min(ptval.values()))

# merge equal consecutive values (for counting pieces)
merged = []
for a, b, v in vals:
    if merged and merged[-1][2] == v and ptval.get(a, None) is not None and ptval[a] >= v:
        merged[-1] = (merged[-1][0], b, v)
    else:
        merged.append((a, b, v))
print("merged pieces:", len(merged), " nonzero:", sum(1 for m in merged if m[2] != 0))

# C2 = 1341 - int_{1/60}^inf phi(x) dx/x^2
mp.mp.dps = 50
lo = Fr(1, 60)
I_main = Fr(0)
for a, b, v in vals:
    if a >= lo and v != 0:
        I_main += v * (1 / a - 1 / b)
I_tail = mp.mpf(0)
for a, b, v in vals:
    if v != 0:
        I_tail += v * (mp.digamma(1 + mp.mpf(b.numerator) / b.denominator) - mp.digamma(1 + mp.mpf(a.numerator) / a.denominator))
I = mp.mpf(I_main.numerator) / I_main.denominator + I_tail
print("int_[1/60,1) =", mp.nstr(mp.mpf(I_main.numerator) / I_main.denominator, 20))
print("int_[1,inf)  =", mp.nstr(I_tail, 20))
print("int total    =", mp.nstr(I, 25))
print("C2 = 1341 - int =", mp.nstr(1341 - I, 25))

# certified sum with M=60, K=20 over MY pieces
def weight(a, b, v, M=60, K=20):
    w = (1 / a - 1 / b) if (a > 0 and Fr(1, M) <= a) else Fr(0)
    for m in range(1, K + 1):
        w += 1 / (a + m) - 1 / (b + m)
    return v * w
S_mine = sum((weight(a, b, v) for a, b, v in vals if v > 0), Fr(0))
print("phiSumQ(60,20) over my Farey pieces (v>0):", float(S_mine), " 1341 - it =", float(1341 - S_mine))

# ---- check the Lean table ----
path = sys.argv[1]
txt = open(path, encoding="utf-8").read()
tab = [tuple(map(int, m)) for m in re.findall(r"⟨(\d+), (\d+), (\d+), (\d+), (\d+)⟩", txt)]
print("Lean table entries:", len(tab))
Fset = set(F)
bad = 0
prev_b = Fr(-1)
S_lean = Fr(0)
for (an, ad, bn, bd, v) in tab:
    a, b = Fr(an, ad), Fr(bn, bd)
    assert ad > 0 and bd > 0 and 0 <= a < b <= 1, (an, ad, bn, bd)
    assert prev_b <= a
    prev_b = b
    if a not in Fset or b not in Fset:
        print("endpoint not Farey-160:", (an, ad, bn, bd)); bad += 1; continue
    ia, ib = F.index(a), F.index(b)
    for i in range(ia, ib):
        if vals[i][2] < v:
            print("VIOLATION interval", vals[i], "v =", v); bad += 1
    for i in range(ia + 1, ib):
        if ptval[F[i]] < v:
            print("VIOLATION at interior point", F[i], ptval[F[i]], "v =", v); bad += 1
    S_lean += weight(a, b, v)
print("table violations:", bad)
print("phiSumQ(60,20) of Lean table =", float(S_lean), " exact num bits:", S_lean.numerator.bit_length())
print("1341 - phiSumQ =", float(1341 - S_lean), " < 748 ?", 1341 - S_lean < 748)
# coverage: which positive-phi Farey intervals are NOT covered by the table
cov = [False] * len(vals)
for (an, ad, bn, bd, v) in tab:
    ia, ib = F.index(Fr(an, ad)), F.index(Fr(bn, bd))
    for i in range(ia, ib): cov[i] = True
unc = [(vals[i]) for i in range(len(vals)) if not cov[i] and vals[i][2] > 0]
print("positive-phi Farey intervals not covered:", len(unc), unc[:5])
