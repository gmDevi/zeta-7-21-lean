# Auditor-2 (window): exact Laurent data of R~ for cfgW (own log/exp expansion at each pole),
# the linear form -A0 + sum A_s zeta(s) (compared with the direct series), the vanishing of A_5 and
# of the even A_s, and Lemma 19 (Delta_n A in Z) prime by prime, with the slack at each prime of Phi_n.
import sys, time
from fractions import Fraction as Fr
from math import comb, factorial, gcd
import mpmath as mp

r, q, e0 = 5, 23, 160
eta = [47, 47, 47, 47, 48, 50, 50] + [j + 43 for j in range(8, 24)]
n = int(sys.argv[1]) if len(sys.argv) > 1 else 1
h0 = e0 * n + 2
h = [None] + [e * n + 1 for e in eta]          # h[1..q]
Nh = Fr(1)
for j in range(r + 1, q + 1): Nh *= factorial(h0 - 2 * h[j])
for j in range(1, r + 1): Nh /= factorial(h[j] - 1) ** 2
mult = {}
for i in range(1, h0): mult[i] = mult.get(i, 0) + r
for j in range(1, q + 1):
    for i in range(h[j], h0 - h[j] + 1): mult[i] = mult.get(i, 0) - 1
K = q - r  # max pole order

def series_exp(c, N):          # exp(sum_{m>=1} c[m] e^m) up to e^N, exact
    out = [Fr(0)] * (N + 1); out[0] = Fr(1)
    # out' = c' out  ->  m out_m = sum_{k=1}^m k c_k out_{m-k}
    for m in range(1, N + 1):
        out[m] = sum(k * c[k] * out[m - k] for k in range(1, m + 1)) / m
    return out

t0 = time.time()
B = {}   # B[(j,k)]
for k in range(1, h0):
    ek = mult.get(k, 0)
    if ek >= 0: continue                # no pole
    order = -ek
    const = Nh
    c = [Fr(0)] * (K + 1)
    for i, m in mult.items():
        if i == k or m == 0: continue
        d = i - k
        const *= Fr(d) ** m
        for mm in range(1, K + 1):
            c[mm] += Fr(m * (-1) ** (mm - 1), mm * d ** mm)
    reg = series_exp(c, K)
    # times (h0 - 2k + 2 eps)
    a0 = h0 - 2 * k
    reg = [const * (a0 * reg[m] + (2 * reg[m - 1] if m else 0)) for m in range(K + 1)]
    # R~(-k+e) = e^{-order} * reg ; coefficient of e^{-(j-r)} is reg[order-(j-r)]
    for jr in range(1, order + 1):
        B[(r + jr, k)] = reg[order - jr]
print("n=%d: poles %d..%d, max order %d, Laurent data in %.1fs" % (n, min(k for _, k in B), max(k for _, k in B),
      max(-mult.get(k, 0) for k in range(1, h0)), time.time() - t0))

def harm(N, s):
    return sum(Fr(1, l ** s) for l in range(1, N + 1))
A = {}
for s in range(r, q):
    A[s] = comb(s - 1, r - 1) * sum((v for (j, k), v in B.items() if j == s + 1), Fr(0))
A0 = sum((comb(j - 2, r - 1) * v * harm(k - h[1], j - 1) for (j, k), v in B.items()), Fr(0))
print("A_s = 0 for s =", [s for s in A if A[s] == 0])
print("A_s != 0 for s =", [s for s in A if A[s] != 0])
# symmetry B_{j,h0-k} = (-1)^j B_{j,k}
print("symmetry B_{j,h0-k} = (-1)^j B_{j,k}:", all(B.get((j, h0 - k), 0) == (-1) ** j * v for (j, k), v in B.items()))
# linear form vs the direct series
import math
mag = max(len(str(abs(x.numerator))) - len(str(x.denominator)) for x in [A0] + [A[s] for s in A if A[s] != 0])
print('max log10|coefficient| ~', mag)
mp.mp.dps = mag + 360 * n + 60
Fv = -mp.mpf(A0.numerator) / A0.denominator + sum(mp.mpf(A[s].numerator) / A[s].denominator * mp.zeta(s) for s in A if A[s] != 0)
print("linear form: log|F| =", mp.nstr(mp.log(abs(Fv)), 22), " sign", '+' if Fv > 0 else '-')

# Lemma 19
def lcmupto(m):
    L = 1
    for i in range(1, m + 1): L = L * i // gcd(L, i)
    return L
m0 = max(h[r] - 1, h0 - 2 * h[r + 1])
mj = [None] + [max(m0, h0 - h[1] - h[r + j]) for j in range(1, q - r + 1)]
print("m_j/n =", [x // n for x in mj[1:]], " (exact multiples:", all(x % n == 0 for x in mj[1:]), ")")
D = lcmupto(mj[1]) ** r
for j in range(2, q - r + 1): D *= lcmupto(mj[j])
def fl(a, p): return a // p
def omega_kp(p, k):
    s = 0
    for j in range(1, r + 1):
        s += fl(k - 1, p) + fl(h0 - k - 1, p) - fl(k - h[j], p) - fl(h0 - h[j] - k, p) - 2 * fl(h[j] - 1, p)
    for j in range(r + 1, q + 1):
        s += fl(h0 - 2 * h[j], p) - fl(k - h[j], p) - fl(h0 - h[j] - k, p)
    return s
def isprime(p): return p > 1 and all(p % d for d in range(2, int(p ** 0.5) + 1))
Phi = 1; om = {}
for p in range(2, mj[q - r] + 1):
    if isprime(p) and p * p > h0:
        w1 = min(omega_kp(p, k) for k in range(h[r + 1], h0 - h[r + 1] + 1))     # JTNB (8.9) range
        w2 = min(omega_kp(p, k) for k in range(p))                            # Lean: full residue system
        assert w1 == w2, (p, w1, w2)
        om[p] = w1
        Phi *= p ** max(w1, 0)
print("Phi_n primes and omega_p:", om)
Delta = Fr(D, Phi)
ok0 = (Delta * A0).denominator == 1
oks = all((Delta * A[s]).denominator == 1 for s in A)
print("Delta*A0 in Z:", ok0, " Delta*A_s in Z for all s:", oks)
# slack per prime of Phi: min over the coefficients of v_p(Delta * coeff)
def vp(x, p):
    if x == 0: return 10 ** 9
    v = 0; a, b = x.numerator, x.denominator
    while a % p == 0: a //= p; v += 1
    while b % p == 0: b //= p; v -= 1
    return v
coeffs = [A0] + [A[s] for s in A if A[s] != 0]
print("slack v_p(Delta*coeffs) at primes of Phi:", {p: min(vp(Delta * x, p) for x in coeffs) for p in om})
small = [p for p in range(2, mj[1] + 1) if isprime(p) and p * p <= h0]
print("slack at small primes:", {p: min(vp(Delta * x, p) for x in coeffs) for p in small})
print("log(Delta)/n = %.4f" % (float(mp.log(D) - mp.log(Phi)) / n))

# ---- per-coefficient statements (Stmt_LaurentSupp, Stmt_LaurentInt, Stmt_LaurentVal) on the exact data
Dm0 = lcmupto(m0)
bad_supp = [(j, k) for (j, k), v in B.items() if v != 0 and not (h[j] <= k <= h0 - h[j])]
bad_int = [(j, k) for (j, k), v in B.items() if (Fr(Dm0) ** (q - j) * v).denominator != 1]
bad_val = []
for p in range(2, 2 * h0 + 3):
    if isprime(p) and p * p > h0:
        for (j, k), v in B.items():
            if v != 0 and not (omega_kp(p, k) - (q - j) <= vp(v, p)):
                bad_val.append((p, j, k))
print("LaurentSupp violations:", len(bad_supp), " LaurentInt violations (D_m0^(q-j) B):", len(bad_int),
      " LaurentVal violations (p^2 > h0, p <= 2h0+2):", len(bad_val))
# JTNB's rough inclusion D_{m0}^{q-j-1} A_j in Z and the refined ord_p A_j >= -(q-j-1) + omega_p
print("rough: D_m0^(q-s-1) A_s in Z:", all((Fr(Dm0) ** (q - s - 1) * A[s]).denominator == 1 for s in A))
