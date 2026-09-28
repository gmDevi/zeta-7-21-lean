# Auditor's independent exact computation of Zudilin's forms (JTNB §8), generic config.
# Laurent data by the log/exp method (NOT the Lean brick products), then:
#  - literal transcription of the Lean definitions polyBrick/ratBrick/Gk/B (cross-check),
#  - A_s, A0 (Lean: H_{k-h1}) vs A0' (H_{k-1}), vanishing, window,
#  - Lemma 19 integrality prime by prime (Lean omegaP over a full residue system and Zudilin's range),
#  - (8.10)/(8.11) (LaurentInt, LaurentVal), LaurentSupp, CoeffVanish,
#  - numeric F_n = -A0 + sum A_s zeta(s).
import sys, math, time, json
from fractions import Fraction as Fr
from math import comb, factorial, gcd
import mpmath as mp

def config(name):
    if isinstance(name, tuple): return name
    if name == 'W':
        return 5, 23, 160, [47, 47, 47, 47, 48, 50, 50] + [j + 43 for j in range(8, 24)]
    if name == 'T3':
        return 3, 13, 91, [27, 27, 27] + [25 + j for j in range(4, 14)]
    raise ValueError(name)

def primes_upto(N):
    s = bytearray([1]) * (N + 1); s[0:2] = b'\x00\x00'
    for i in range(2, int(N ** 0.5) + 1):
        if s[i]: s[i * i::i] = bytearray(len(s[i * i::i]))
    return [i for i in range(N + 1) if s[i]]

def vp(p, x):
    x = Fr(x)
    if x == 0: return None
    v = 0; a, b = x.numerator, x.denominator
    while a % p == 0: a //= p; v += 1
    while b % p == 0: b //= p; v -= 1
    return v

def lcm_upto(m):
    L = 1
    for i in range(1, m + 1): L = L * i // gcd(L, i)
    return L

def laurent(r, q, e0, eta, n):
    h0 = e0 * n + 2
    h = [e * n + 1 for e in eta]
    ex = {i: r - sum(1 for hj in h if hj <= i <= h0 - hj) for i in range(1, h0)}
    Nh = Fr(1)
    for j in range(r, q): Nh *= factorial(h0 - 2 * h[j])
    for j in range(r): Nh /= factorial(h[j] - 1) ** 2
    B = {}
    for k in range(h[0], h0 - h[0] + 1):
        order = -ex[k]
        if order <= 0:
            for j in range(r + 1, q + 1): B[(j, k)] = Fr(0)
            continue
        M = order - 1
        idx = [i for i in range(1, h0) if i != k and ex[i] != 0]
        L = 1
        for i in idx: L = L * abs(i - k) // gcd(L, abs(i - k))
        lco = [Fr(0)] * (M + 1)
        for m in range(1, M + 1):
            num = sum(ex[i] * (L // (i - k)) ** m for i in idx)
            lco[m] = Fr((-1) ** (m + 1) * num, m * L ** m)
        E = [Fr(1)] + [Fr(0)] * M
        for m in range(1, M + 1):
            E[m] = sum((kk * lco[kk] * E[m - kk] for kk in range(1, m + 1)), Fr(0)) / m
        Ck = Fr(1)
        for i in idx: Ck *= Fr(i - k) ** ex[i]
        c0 = h0 - 2 * k
        ser = [c0 * E[0]] + [c0 * E[m] + 2 * E[m - 1] for m in range(1, M + 1)]
        for j in range(r + 1, q + 1):
            d = j - r; ii = order - d
            B[(j, k)] = Nh * Ck * ser[ii] if 0 <= ii <= M else Fr(0)
    return h0, h, ex, Nh, B

# ---------- literal transcription of the Lean definitions (truncated power series) ----------
def smul(a, b, N):
    out = [Fr(0)] * (N + 1)
    for i, x in enumerate(a):
        if x == 0 or i > N: continue
        for j, y in enumerate(b):
            if i + j > N: break
            out[i + j] += x * y
    return out
def sinv(a, N):
    # Mathlib: inverse is 0 if constant coeff is 0
    if a[0] == 0: return [Fr(0)] * (N + 1)
    out = [Fr(0)] * (N + 1); out[0] = 1 / Fr(a[0])
    for m in range(1, N + 1):
        s = sum((a[i] * out[m - i] for i in range(1, min(m, len(a) - 1) + 1)), Fr(0))
        out[m] = -s * out[0]
    return out
def lin(c):  # C c + X
    return [Fr(c), Fr(1)]
def polyBrick(a, b, k, N):
    s = [Fr(1, factorial(max(a - b, 0)))]   # (a - b) truncated subtraction as in Lean
    for i in range(b, a): s = smul(s, lin(i - k), N)
    return s + [Fr(0)] * (N + 1 - len(s)) if len(s) < N + 1 else s[:N + 1]
def ratBrick(a, b, k, N):
    f = Fr(factorial(max(b - a - 1, 0)))
    if a <= k < b:
        pr = [Fr(1)]
        for i in range(a, b):
            if i != k: pr = smul(pr, lin(i - k), N)
        pr = pr + [Fr(0)] * (N + 1 - len(pr))
        s = [f * x for x in sinv(pr, N)]
    else:
        pr = [Fr(1)]
        for i in range(a, b): pr = smul(pr, lin(i - k), N)
        pr = pr + [Fr(0)] * (N + 1 - len(pr))
        s = smul([Fr(0), f], sinv(pr, N), N)
    return s + [Fr(0)] * (N + 1 - len(s))
def Gk(r, q, e0, eta, n, k, N):
    h0 = e0 * n + 2; h = [e * n + 1 for e in eta]
    s = [Fr(h0 - 2 * k), Fr(2)]
    for j in range(r):
        s = smul(s, smul(polyBrick(h[j], 1, k, N), polyBrick(h0, h0 - h[j] + 1, k, N), N), N)
    for j in range(r, q):
        s = smul(s, ratBrick(h[j], h0 - h[j] + 1, k, N), N)
    return s + [Fr(0)] * (N + 1 - len(s))

# ---------- omega, Delta ----------
def omegaKP(r, q, h0, h, p, k):
    s = 0
    for j in range(r):
        s += (k - 1) // p + (h0 - k - 1) // p - (k - h[j]) // p - (h0 - h[j] - k) // p - 2 * ((h[j] - 1) // p)
    for j in range(r, q):
        s += (h0 - 2 * h[j]) // p - (k - h[j]) // p - (h0 - h[j] - k) // p
    return s

def run(name, n, dps=None, lean_check=False, zeta_check=True):
    r, q, e0, eta = config(name)
    t0 = time.time()
    h0, h, ex, Nh, B = laurent(r, q, e0, eta, n)
    K = range(h[0], h0 - h[0] + 1)
    print(f"== config {name} n={n}: h0={h0} h1={h[0]} |Krange|={len(K)}  laurent {time.time()-t0:.1f}s")
    fails = []
    # Lean-literal B
    if lean_check:
        t1 = time.time(); nb = 0
        for k in K:
            G = Gk(r, q, e0, eta, n, k, q - r)
            for j in range(r + 1, q + 1):
                if G[q - j] != B[(j, k)]: fails.append(("LeanB", j, k))
                nb += 1
        print(f"  Lean-literal B = log/exp Laurent coefficients: {nb} checked, mismatches {sum(1 for f in fails if f[0]=='LeanB')}  ({time.time()-t1:.1f}s)")
    # LaurentSupp, CoeffVanish
    for j in range(r + 1, q + 1):
        for k in K:
            if (k < h[j - 1] or k > h0 - h[j - 1]) and B[(j, k)] != 0: fails.append(("Supp", j, k))
            if B[(j, h0 - k)] != (-1) ** j * B[(j, k)]: fails.append(("Symm", j, k))
    if sum(B[(r + 1, k)] for k in K) != 0: fails.append(("ressum",))
    # A's
    A = {s: comb(s - 1, r - 1) * sum((B[(s + 1, k)] for k in K), Fr(0)) for s in range(r, q)}
    nonzero = sorted(s for s in A if A[s] != 0)
    window = [s for s in range(r + 2, q - 1) if s % 2 == 1]
    print("  s with A_s != 0:", nonzero, " window:", window, " equal:", nonzero == window)
    if nonzero != window: fails.append(("window",))
    # harmonic numbers
    Nmax = h0 - h[0]
    Hs = {}
    for s in range(r, q):
        acc = Fr(0); lst = [Fr(0)]
        for l in range(1, Nmax + 1):
            acc += Fr(1, l ** s); lst.append(acc)
        Hs[s] = lst
    A0 = sum((comb(j - 2, r - 1) * sum((B[(j, k)] * Hs[j - 1][k - h[0]] for k in K), Fr(0)) for j in range(r + 1, q + 1)), Fr(0))
    A0p = sum((comb(j - 2, r - 1) * sum((B[(j, k)] * Hs[j - 1][k - 1] for k in K), Fr(0)) for j in range(r + 1, q + 1)), Fr(0))
    print("  A0 (Lean, H_{k-h1}) == A0' (H_{k-1}):", A0 == A0p)
    if A0 != A0p: fails.append(("A0shift",))
    # Delta
    m0 = max(h[r - 1] - 1, h0 - 2 * h[r])
    mj = [max(m0, h0 - h[0] - h[r + j - 1]) for j in range(1, q - r + 1)]
    Dprod = lcm_upto(mj[0]) ** r
    for j in range(2, q - r + 1): Dprod *= lcm_upto(mj[j - 1])
    PhiN = 1; om_lean = {}; om_zud = {}
    for p in primes_upto(mj[-1]):
        if h0 < p * p:
            ol = min(omegaKP(r, q, h0, h, p, k) for k in range(p))
            oz = min(omegaKP(r, q, h0, h, p, k) for k in range(h[r], h0 - h[r] + 1))
            om_lean[p] = ol; om_zud[p] = oz
            PhiN *= p ** max(ol, 0)
    Delta = Fr(Dprod, PhiN)
    print("  m_j/n:", [Fr(m, n) for m in mj][:6], "...", " omega_lean == omega_zud for all p in Phi:", om_lean == om_zud,
          " min omega_p:", min(om_lean.values()) if om_lean else None)
    print("  log Delta_n / n ~ %.3f" % (float(mp.log(Dprod) - mp.log(PhiN)) / n))
    # Lean's omega_p (full residue system) can only be smaller than JTNB's (range h_{r+1}..h0-h_{r+1})
    if any(om_lean[p] > om_zud[p] for p in om_lean): fails.append(("omega-range",))
    # Lemma 19 integrality + prime-by-prime slack
    vals = [("A0", A0)] + [(f"A{s}", A[s]) for s in range(r, q)]
    for nm, v in vals:
        if (Delta * v).denominator != 1: fails.append(("L19", nm))
    ps = primes_upto(2 * h0 + 2)
    slack = {}
    for p in ps:
        vD = vp(p, Delta)
        mins = [vD + vp(p, v) for nm, v in vals if v != 0]
        slack[p] = min(mins)
    tight = [p for p in ps if slack[p] == 0]
    print("  Lemma19: Delta*A integral for all:", not any(f[0] == 'L19' for f in fails),
          " min slack", min(slack.values()), " primes with zero slack (first 12):", tight[:12])
    # (8.10) LaurentInt, (8.11) LaurentVal
    Dm0 = lcm_upto(m0)
    for j in range(r + 1, q + 1):
        for k in K:
            b = B[(j, k)]
            if b == 0: continue
            if (Dm0 ** (q - j) * b).denominator != 1: fails.append(("LInt", j, k))
            for p in ps:
                if h0 < p * p and p <= 2 * h0 + 2:
                    if vp(p, b) < omegaKP(r, q, h0, h, p, k) - (q - j): fails.append(("LVal", j, k, p))
    print("  LaurentInt/LaurentVal/Supp/Symm/ressum failures:", [f for f in fails if f[0] in ('LInt','LVal','Supp','Symm','ressum')][:5])
    out = {"h0": h0, "A": {s: A[s] for s in window}, "A0": A0, "Nh": Nh, "B": B, "ex": ex, "Delta": Delta}
    if zeta_check:
        mag = max(abs(float(mp.log10(abs(mp.mpf(v.numerator)))) - float(mp.log10(mp.mpf(v.denominator)))) for v in [A0] + [A[s] for s in window])
        mp.mp.dps = dps or int(mag + 1200)
        F = -mp.mpf(A0.numerator) / A0.denominator + sum(mp.mpf(A[s].numerator) / A[s].denominator * mp.zeta(s) for s in window)
        print("  max log10|coef| ~ %.1f ; F_n = %s ; log|F_n| = %s ; log|F_n|/n = %s" % (mag, mp.nstr(F, 20), mp.nstr(mp.log(abs(F)), 16), mp.nstr(mp.log(abs(F)) / n, 12)))
        out["F"] = F
    print("  FAILURES:", len(fails), fails[:5], f"  total {time.time()-t0:.1f}s")
    return out

if __name__ == "__main__":
    name = sys.argv[1]; n = int(sys.argv[2]); lean = len(sys.argv) > 3 and sys.argv[3] == 'lean'
    run(name, n, lean_check=lean)
