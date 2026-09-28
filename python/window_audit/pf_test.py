# Stmt_PF, literally: Rser c n y == sum_{j,k} C(B_{j,k}) ((C(y+k)+X)^(j-r))^{-1} in Q[[X]] (first 6 coeffs),
# at non-poles y (integers >= 0, zeros y = -l with 1 <= l < h1, fractions, points inside the pole range).
import sys
import mpmath as mp
from fractions import Fraction as Fr
from math import comb, factorial
from exact_indep import config, laurent, smul, sinv, lin

def rser_literal(r, q, e0, eta, n, y, N):
    h0 = e0 * n + 2; h = [e * n + 1 for e in eta]
    Nh = Fr(1)
    for j in range(r, q): Nh *= factorial(h0 - 2 * h[j])
    for j in range(r): Nh /= factorial(h[j] - 1) ** 2
    num = [Fr(1)]
    for i in range(1, h0): num = smul(num, lin(y + i), N)
    num = num + [Fr(0)] * (N + 1 - len(num))
    numr = [Fr(1)] + [Fr(0)] * N
    for _ in range(r): numr = smul(numr, num, N)
    den = [Fr(1)]
    for j in range(q):
        for i in range(h[j], h0 - h[j] + 1): den = smul(den, lin(y + i), N)
    den = den + [Fr(0)] * (N + 1 - len(den))
    s = smul([Nh * (h0 + 2 * y), 2 * Nh], numr, N)
    return smul(s, sinv(den, N), N)[:N + 1]

def pf_rhs(r, q, h0, h, B, y, N):
    out = [Fr(0)] * (N + 1)
    for (j, k), b in B.items():
        if b == 0: continue
        s = j - r; a = y + k
        for m in range(N + 1):
            out[m] += b * (-1) ** m * comb(s + m - 1, m) * a ** (-s - m)   # [eps^m] (a+eps)^(-s)
    return out

name = sys.argv[1]; n = int(sys.argv[2])
cfg = config(name if name in ('W', 'T3') else tuple(eval(name)))
r, q, e0, eta = cfg
h0, h, ex, Nh, B = laurent(r, q, e0, eta, n)
N = 5
ys = [Fr(0), Fr(3), Fr(1, 2), Fr(-7, 3), Fr(17, 5), Fr(-1), Fr(-(h[0] - 1)), Fr(-(h0 // 2)) + Fr(1, 3), Fr(-(h0 - h[0] + 3))]
bad = 0
for y in ys:
    if any(y + k == 0 for k in range(h[0], h0 - h[0] + 1)):
        print("skip pole", y); continue
    L = rser_literal(r, q, e0, eta, n, y, N)
    R = pf_rhs(r, q, h0, h, B, y, N)
    ok = L == R
    bad += 0 if ok else 1
    print("y = %-10s PF holds on coeffs 0..%d: %s   (coeff %d of Rser = %s)" % (y, N, ok, r - 1, mp.nstr(mp.mpf(L[r - 1].numerator) / L[r - 1].denominator, 6)))
print("PF failures:", bad)
