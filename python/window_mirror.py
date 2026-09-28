"""Exact mirror of Zeta2Lean/Window/Defs.lean + numerical checks of every Stmt of Window/Statements.lean.

Every Lean definition is transcribed literally, with Lean semantics:
  * natural-number subtraction is truncated (nsub), casts happen where Lean casts;
  * `/` on Int is floor division for a positive divisor (Python //);
  * `x / 0 = 0` in Q;  the PowerSeries inverse of a series with zero constant term is 0;
  * Nat.lcmUpto m = lcm(1..m) (= 1 for m = 0).
Power series are truncated coefficient lists of fractions.Fraction (exact).

Checks (see BLUEPRINT_WINDOW.md, "Numerical mirror"):
  admissible, window, muSum; Stmt_PF (random rational y, exact); Stmt_CoeffVanish (symm, ressum, and
  the resulting A_s = 0 for s = r and even s); Stmt_LinearForm (value vs. the independent engine /
  direct series); Stmt_BrickInt, Stmt_BrickVal (random bricks, exact); Stmt_LaurentSupp/Int/Val
  (exhaustive in j, k, p for small n); Stmt_Harmonic; Stmt_Lemma19 (exact integrality);
  Stmt_OmegaPhi0 (random); Stmt_PhiTable (every piece of the Lean file, random x in the piece and all
  critical y); Stmt_PhiData (exact); Stmt_DenomGrowth (trend of log Delta_n / n); Stmt_L20Upper (the
  recorded exact values of |F_n|, n <= 9); Stmt_AuxPrime (exact literal A0, Acoef at n = 4, and an
  l-adic evaluation of the same definitions modulo l^30 for every even n <= 60 with l = 63n - 1 prime,
  checked against the exact values at n = 4).

usage: python3 python/window_mirror.py [--quick] [--aux]
  (stdlib only; mpmath optional for the value checks; --aux runs only the Stmt_AuxPrime section)
"""
import sys, os, re, math, random, time, json
from fractions import Fraction as Fr

try:
    import mpmath as mp
except ImportError:  # value checks are skipped
    mp = None

QUICK = "--quick" in sys.argv
AUX_ONLY = "--aux" in sys.argv       # only the Stmt_AuxPrime section (plus the basic checks)
random.seed(20260925)
FAILS = []
NCHECK = [0]


def check(cond, msg):
    NCHECK[0] += 1
    if not cond:
        FAILS.append(msg)
        print("  FAIL:", msg, flush=True)


def nsub(a, b):
    return a - b if a >= b else 0


def isprime(p):
    if p < 2:
        return False
    if p % 2 == 0:
        return p == 2
    i = 3
    while i * i <= p:
        if p % i == 0:
            return False
        i += 2
    return True


def lcm_upto(m):
    L = 1
    for i in range(1, m + 1):
        L = L * i // math.gcd(L, i)
    return L


def vp(x, p):
    """padicValRat p x (Lean: 0 for x = 0)."""
    x = Fr(x)
    if x == 0:
        return 0
    v = 0
    a, b = x.numerator, x.denominator
    while a % p == 0:
        a //= p
        v += 1
    while b % p == 0:
        b //= p
        v -= 1
    return v


def floor(x):
    x = Fr(x)
    return x.numerator // x.denominator


# ---------------------------------------------------------------- power series (truncated)

def ps_const(c, L):
    return [Fr(c)] + [Fr(0)] * (L - 1)


def ps_mul(A, B):
    L = len(A)
    out = [Fr(0)] * L
    for i, a in enumerate(A):
        if a:
            for j in range(L - i):
                if B[j]:
                    out[i + j] += a * B[j]
    return out


def ps_mul_lin(A, c):
    """A * (C c + X)"""
    L = len(A)
    out = [c * A[0]] + [c * A[i] + A[i - 1] for i in range(1, L)]
    return out


def ps_mul_X(A):
    return [Fr(0)] + A[:-1]


def ps_inv(A):
    L = len(A)
    if A[0] == 0:
        return [Fr(0)] * L  # Lean: φ⁻¹ = 0 iff constantCoeff φ = 0
    inv0 = 1 / A[0]
    out = [inv0] + [Fr(0)] * (L - 1)
    for m in range(1, L):
        s = sum(A[i] * out[m - i] for i in range(1, m + 1))
        out[m] = -s * inv0
    return out


def ps_pow(A, e):
    L = len(A)
    out = ps_const(1, L)
    for _ in range(e):
        out = ps_mul(out, A)
    return out


def prod_lin(consts, L):
    out = ps_const(1, L)
    for c in consts:
        out = ps_mul_lin(out, Fr(c))
    return out


# ---------------------------------------------------------------- Defs.lean, literally

class Config:
    def __init__(self, r, q, eta0, eta, name):
        self.r, self.q, self.eta0, self._eta, self.name = r, q, eta0, eta, name

    def eta(self, j):
        return self._eta(j)

    def h0(self, n):
        return self.eta0 * n + 2

    def h(self, n, j):
        return self.eta(j) * n + 1


def etaW(j):
    if j <= 4:
        return 47
    if j == 5:
        return 48
    if j <= 7:
        return 50
    return j + 43


cfgW = Config(5, 23, 160, etaW, "cfgW")
# Zudilin's Theorem 3 configuration (r = 3, q = 13, eta0 = 91, eta = (27,27,27,29,...,38)): a
# second admissible configuration, used as an independent test of the generic statements.
cfgT3 = Config(3, 13, 91, lambda j: 27 if j <= 3 else 25 + j, "thm3")


def admissible(c):
    ok = (c.r % 2 == 1 and c.q % 2 == 1 and c.r >= 3 and c.r + 4 <= c.q and c.eta(1) >= 1
          and all(c.eta(i) <= c.eta(i + 1) for i in range(1, c.q))
          and 2 * c.eta(c.q) < c.eta0
          and 2 * sum(c.eta(j) for j in range(1, c.q + 1)) + 2 * c.r <= nsub(c.q, c.r) * c.eta0)
    return ok


def Nh(c, n):
    num = Fr(1)
    for j in range(c.r + 1, c.q + 1):
        num *= math.factorial(nsub(c.h0(n), 2 * c.h(n, j)))
    den = Fr(1)
    for j in range(1, c.r + 1):
        den *= Fr(math.factorial(nsub(c.h(n, j), 1))) ** 2
    return num / den if den != 0 else Fr(0)


def Rser(c, n, y, L):
    y = Fr(y)
    h0 = c.h0(n)
    A = ps_const(Nh(c, n), L)
    A = ps_mul(A, [Fr(h0) + 2 * y, Fr(2)] + [Fr(0)] * (L - 2) if L >= 2 else [Fr(h0) + 2 * y])
    P = prod_lin([y + i for i in range(1, h0)], L)
    A = ps_mul(A, ps_pow(P, c.r))
    D = ps_const(1, L)
    for j in range(1, c.q + 1):
        for i in range(c.h(n, j), nsub(h0, c.h(n, j)) + 1):
            D = ps_mul_lin(D, y + i)
    return ps_mul(A, ps_inv(D))


def term(c, n, t):
    return Rser(c, n, t, c.r)[c.r - 1]


def polyBrick(a, b, k, L):
    P = prod_lin([Fr(i) - k for i in range(b, a)], L)
    f = Fr(1, math.factorial(nsub(a, b)))
    return [f * x for x in P]


def ratBrick(a, b, k, L):
    fac = Fr(math.factorial(nsub(nsub(b, a), 1)))
    if a <= k < b:
        P = prod_lin([Fr(i) - k for i in range(a, b) if i != k], L)
        return [fac * x for x in ps_inv(P)]
    else:
        P = prod_lin([Fr(i) - k for i in range(a, b)], L)
        return [fac * x for x in ps_mul_X(ps_inv(P))]


def Gk(c, n, k, L):
    h0 = c.h0(n)
    G = [Fr(h0) - 2 * k, Fr(2)] + [Fr(0)] * (L - 2)
    for j in range(1, c.r + 1):
        G = ps_mul(G, polyBrick(c.h(n, j), 1, k, L))
        G = ps_mul(G, polyBrick(h0, nsub(h0, c.h(n, j)) + 1, k, L))
    for j in range(c.r + 1, c.q + 1):
        G = ps_mul(G, ratBrick(c.h(n, j), nsub(h0, c.h(n, j)) + 1, k, L))
    return G


class Form:
    """All data of the form for (c, n): B, A, A0, Delta, ... (exact)."""

    def __init__(self, c, n):
        self.c, self.n = c, n
        L = c.q - c.r + 1
        self.h0 = c.h0(n)
        self.K = list(range(c.h(n, 1), nsub(self.h0, c.h(n, 1)) + 1))
        self.G = {k: Gk(c, n, k, L) for k in self.K}

    def B(self, j, k):
        c = self.c
        G = self.G.get(k)
        if G is None:
            G = Gk(c, self.n, k, c.q - c.r + 1)
        idx = nsub(c.q, j)
        return G[idx] if idx < len(G) else Fr(0)

    def Acoef(self, s):
        c = self.c
        return math.comb(nsub(s, 1), nsub(c.r, 1)) * sum(self.B(s + 1, k) for k in self.K)

    def A0(self):
        c = self.c
        tot = Fr(0)
        for j in range(c.r + 1, c.q + 1):
            inner = sum(self.B(j, k) * harm(nsub(k, c.h(self.n, 1)), nsub(j, 1)) for k in self.K)
            tot += math.comb(nsub(j, 2), nsub(c.r, 1)) * inner
        return tot


_harm_cache = {}


def harm(N, s):
    key = (N, s)
    if key not in _harm_cache:
        _harm_cache[key] = sum((Fr(1, l ** s) for l in range(1, N + 1)), Fr(0))
    return _harm_cache[key]


def window(c):
    return [s for s in range(c.r + 2, nsub(c.q, 2) + 1) if s % 2 == 1]


def m0(c, n):
    return max(nsub(c.h(n, c.r), 1), nsub(c.h0(n), 2 * c.h(n, c.r + 1)))


def mj(c, n, j):
    return max(m0(c, n), nsub(nsub(c.h0(n), c.h(n, 1)), c.h(n, c.r + j)))


def Dprod(c, n):
    out = lcm_upto(mj(c, n, 1)) ** c.r
    for j in range(2, nsub(c.q, c.r) + 1):
        out *= lcm_upto(mj(c, n, j))
    return out


def omegaKP(c, n, p, k):
    h0 = c.h0(n)
    tot = 0
    for j in range(1, c.r + 1):
        hj = c.h(n, j)
        tot += ((k - 1) // p + (h0 - k - 1) // p - (k - hj) // p - (h0 - hj - k) // p
                - 2 * ((hj - 1) // p))
    for j in range(c.r + 1, c.q + 1):
        hj = c.h(n, j)
        tot += (h0 - 2 * hj) // p - (k - hj) // p - (h0 - hj - k) // p
    return tot


def omegaP(c, n, p):
    if p <= 0:
        return 0
    return min(omegaKP(c, n, p, k) for k in range(p))


def PhiN(c, n):
    out = 1
    for p in range(0, mj(c, n, nsub(c.q, c.r)) + 1):
        if isprime(p) and c.h0(n) < p * p:
            out *= p ** max(omegaP(c, n, p), 0)
    return out


def Delta(c, n):
    return Fr(Dprod(c, n), PhiN(c, n))


def wPoly(a, b, k, p):
    return (k - b) // p - (k - a) // p - (a - b) // p


def wRat(a, b, k, p):
    return (b - a - 1) // p - (k - a) // p - (b - 1 - k) // p


def phi0(c, x, y):
    x, y = Fr(x), Fr(y)
    tot = 0
    for j in range(1, c.r + 1):
        e = c.eta(j)
        tot += (floor(y) + floor(c.eta0 * x - y) - floor(y - e * x) - floor((c.eta0 - e) * x - y)
                - 2 * floor(e * x))
    for j in range(c.r + 1, c.q + 1):
        e = c.eta(j)
        tot += floor((c.eta0 - 2 * e) * x) - floor(y - e * x) - floor((c.eta0 - e) * x - y)
    return tot


def mu(c, j):
    return max(max(c.eta(c.r), nsub(c.eta0, 2 * c.eta(c.r + 1))), nsub(nsub(c.eta0, c.eta(1)), c.eta(c.r + j)))


def muSum(c):
    return c.r * mu(c, 1) + sum(mu(c, j) for j in range(2, nsub(c.q, c.r) + 1))


def qdiv(a, b):
    return Fr(a) / b if b != 0 else Fr(0)


def piece_a(e):
    return qdiv(e[0], e[1])


def piece_b(e):
    return qdiv(e[2], e[3])


def phiWeight(M, K, e):
    a, b, v = piece_a(e), piece_b(e), e[4]
    s = Fr(0)
    if qdiv(1, M) <= a:
        s += qdiv(1, a) - qdiv(1, b)
    for m in range(1, K + 1):
        s += qdiv(1, a + m) - qdiv(1, b + m)
    return v * s


C0lo = Fr(7481, 10)
C2hi = Fr(748)


def read_phitable():
    here = os.path.dirname(os.path.abspath(__file__))
    path = os.path.join(here, "..", "Zeta2Lean", "Window", "PhiTable.lean")
    txt = open(path, encoding="utf-8").read()
    return [tuple(int(t) for t in m.groups())
            for m in re.finditer(r"⟨(\d+), (\d+), (\d+), (\d+), (\d+)⟩", txt)]


# ---------------------------------------------------------------- checks

def section(name):
    print(f"== {name}", flush=True)


def check_basic():
    section("Admissible / window / muSum")
    check(admissible(cfgW), "Admissible cfgW")
    check(admissible(cfgT3), "Admissible thm3")
    check(window(cfgW) == [7, 9, 11, 13, 15, 17, 19, 21], "window cfgW")
    check(muSum(cfgW) == 1341, "muSum cfgW = 1341")
    check([mj(cfgW, 1, j) for j in range(1, 19)] == [63, 63, 62, 61] + [60] * 14, "m_j for n = 1")
    check(mu(cfgW, cfgW.q - cfgW.r) == 60, "mu_{q-r} = 60")
    for n in (1, 2, 5, 17):
        check(all(mj(cfgW, n, j) == mu(cfgW, j) * n for j in range(1, 19)), f"m_j = mu_j n (n={n})")
    print(f"   window {window(cfgW)}, muSum {muSum(cfgW)}")


def check_bricks():
    section("Stmt_BrickInt, Stmt_BrickVal (random bricks, exact)")
    trials = 60 if QUICK else 250
    for _ in range(trials):
        # polynomial brick
        b = random.randint(1, 12)
        a = b + random.randint(0, 12)
        k = random.randint(0, 40)
        L = a - b + 3
        P = polyBrick(a, b, k, L)
        D = lcm_upto(nsub(a, b))
        for i in range(L):
            check((Fr(D) ** i * P[i]).denominator == 1, f"BrickInt.poly a={a} b={b} k={k} i={i}")
        N = max(a, k)
        for p in [p for p in range(2, 60) if isprime(p) and N < p * p]:
            for i in range(L):
                if P[i] != 0:
                    check(wPoly(a, b, k, p) - i <= vp(P[i], p), f"BrickVal.poly a={a} b={b} k={k} p={p} i={i}")
        # rational brick
        a = random.randint(1, 12)
        b = a + random.randint(1, 12)
        a0 = random.randint(0, a)
        b0 = b + random.randint(0, 6)
        k = random.randint(a0, b0 - 1)
        L = 8
        S = ratBrick(a, b, k, L)
        D = lcm_upto(nsub(nsub(b0, a0), 1))
        for i in range(L):
            check((Fr(D) ** i * S[i]).denominator == 1, f"BrickInt.rat a={a} b={b} k={k} a0={a0} b0={b0} i={i}")
        k2 = random.randint(0, 40)
        S2 = ratBrick(a, b, k2, L)
        N = max(b - 1, k2)
        for p in [p for p in range(2, 60) if isprime(p) and N < p * p]:
            for i in range(L):
                if S2[i] != 0:
                    check(wRat(a, b, k2, p) - i <= vp(S2[i], p), f"BrickVal.rat a={a} b={b} k={k2} p={p} i={i}")


def check_harmonic():
    section("Stmt_Harmonic")
    for _ in range(80):
        N = random.randint(0, 40)
        m = N + random.randint(0, 10)
        s = random.randint(0, 8)
        check((Fr(lcm_upto(m)) ** s * harm(N, s)).denominator == 1, f"Harmonic.int N={N} m={m} s={s}")
        for p in [p for p in range(2, 50) if isprime(p) and N < p * p]:
            H = harm(N, s)
            if H != 0:
                check(-s <= vp(H, p), f"Harmonic.val N={N} s={s} p={p}")


def check_form(c, n, value_ref=None):
    t0 = time.time()
    F = Form(c, n)
    h0 = F.h0
    print(f"   [{c.name} n={n}] h0={h0}, |Krange|={len(F.K)}, Laurent data in {time.time() - t0:.1f}s", flush=True)
    J = range(c.r + 1, c.q + 1)
    # LaurentSupp
    for j in J:
        hj = c.h(n, j)
        for k in list(range(0, hj)) + list(range(nsub(h0, hj) + 1, h0 + 3)):
            if k in F.G or random.random() < 0.2:
                check(F.B(j, k) == 0, f"LaurentSupp {c.name} n={n} j={j} k={k}")
    # LaurentInt
    D = Fr(lcm_upto(m0(c, n)))
    for j in J:
        for k in F.K:
            check((D ** nsub(c.q, j) * F.B(j, k)).denominator == 1, f"LaurentInt {c.name} n={n} j={j} k={k}")
    # LaurentVal
    primes = [p for p in range(2, 2 * h0 + 3) if isprime(p) and h0 < p * p]
    for p in primes:
        for j in J:
            for k in F.K:
                Bv = F.B(j, k)
                if Bv != 0:
                    check(omegaKP(c, n, p, k) - nsub(c.q, j) <= vp(Bv, p),
                          f"LaurentVal {c.name} n={n} p={p} j={j} k={k}")
    # CoeffVanish
    for j in J:
        for k in F.K:
            check(F.B(j, h0 - k) == (-1) ** j * F.B(j, k), f"CoeffVanish.symm {c.name} n={n} j={j} k={k}")
    check(sum(F.B(c.r + 1, k) for k in F.K) == 0, f"CoeffVanish.ressum {c.name} n={n}")
    A = {s: F.Acoef(s) for s in range(c.r, c.q)}
    occ = sorted(s for s in A if A[s] != 0)
    check(occ == window(c), f"occurring zeta values {occ} = window {window(c)} ({c.name} n={n})")
    # Lemma19
    Dl = Delta(c, n)
    A0v = F.A0()
    check((Dl * A0v).denominator == 1, f"Lemma19 A0 {c.name} n={n}")
    for s in range(c.r, c.q):
        check((Dl * A[s]).denominator == 1, f"Lemma19 A_{s} {c.name} n={n}")
    print(f"   [{c.name} n={n}] log Dprod = {math.log(Dprod(c, n)):.3f}, log PhiN = {math.log(PhiN(c, n)):.3f}, "
          f"log Delta = {math.log(Dprod(c, n)) - math.log(PhiN(c, n)):.3f}", flush=True)
    # PF at random rational y (first coefficients, exact)
    Lpf = 4
    pts = [Fr(random.randint(0, 30)), Fr(random.randint(-3000, 3000), random.randint(1, 97)),
           Fr(-random.randint(1, c.h(n, 1) - 1))]
    for y in pts:
        if any(y + k == 0 for k in F.K):
            continue
        lhs = Rser(c, n, y, Lpf)
        rhs = [Fr(0)] * Lpf
        for j in J:
            for k in F.K:
                Bv = F.B(j, k)
                if Bv:
                    base = [y + k, Fr(1)] + [Fr(0)] * (Lpf - 2)
                    inv = ps_inv(ps_pow(base, j - c.r))
                    for i in range(Lpf):
                        rhs[i] += Bv * inv[i]
        check(lhs == rhs, f"PF {c.name} n={n} y={y}")
    # linear form value
    if mp is not None:
        # the coefficients are huge (about e^{1050 n} for cfgW) and cancel down to e^{-750 n}:
        # work with twice the number of digits of the largest coefficient
        big = max([abs(A0v)] + [abs(A[s]) for s in window(c)])
        digits = int(math.log10(big.numerator + 1) - math.log10(big.denominator)) + 1
        with mp.workdps(2 * max(digits, 50) + 150):
            val = -mp.mpf(A0v.numerator) / A0v.denominator
            for s in window(c):
                val += mp.mpf(A[s].numerator) / A[s].denominator * mp.zeta(s)
            print(f"   [{c.name} n={n}] linear form value: log|F| = {float(mp.log(abs(val))):.10f}, sign {int(mp.sign(val))}",
                  flush=True)
            if value_ref is not None:
                check(abs(float(mp.log(abs(val))) - value_ref[0]) < 1e-8 and int(mp.sign(val)) == value_ref[1],
                      f"LinearForm value vs independent engine {c.name} n={n}")
            return F, val
    return F, None


def check_series(c, n, val, T):
    """Stmt_LinearForm: partial sums of the series sum_t term(t) (exact) converge to the value."""
    section(f"Stmt_LinearForm series check ({c.name}, n={n}, T={T})")
    S = Fr(0)
    last = None
    for t in range(T):
        tt = term(c, n, t)
        S += tt
        last = tt
    with mp.workdps(120):
        err = abs(mp.mpf(S.numerator) / S.denominator - val)
        rel = err / abs(val)
        lt = abs(mp.mpf(last.numerator) / last.denominator)
        print(f"   partial sum to t<{T}: rel. error {mp.nstr(rel, 5)}, last term {mp.nstr(lt, 5)}", flush=True)
        check(rel < mp.mpf(10) ** -20, f"series vs linear form {c.name} n={n}")


def check_engine(c, n, val):
    """Stmt_LinearForm value against the independent partial-fraction engine docs/window/zud_exact.py
    (log-derivative method, mpmath), called live."""
    here = os.path.dirname(os.path.abspath(__file__))
    path = os.path.join(here, "..", "docs", "window", "zud_exact.py")
    if mp is None or val is None or not os.path.exists(path):
        print("   (engine or mpmath missing, skipped)")
        return
    import importlib.util
    spec = importlib.util.spec_from_file_location("zud_exact", path)
    ze = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(ze)
    eta = [c.eta(j) for j in range(1, c.q + 1)]
    dps = mp.mp.dps
    v2, coef, const = ze.form(c.r, c.eta0, eta, n, 2 * 1100 * n if c is cfgW else 400 * n + 200)
    with mp.workdps(60):
        rel = abs((v2 - val) / val)
    mp.mp.dps = dps
    print(f"   [{c.name} n={n}] zud_exact.py value: log|F| = {float(mp.log(abs(v2))):.10f}; relative difference {mp.nstr(rel, 3)}")
    check(rel < mp.mpf(10) ** -30, f"LinearForm value vs zud_exact.py (live) {c.name} n={n}")


def check_zeta_real():
    section("Stmt_ZetaReal (mpmath)")
    if mp is None:
        return
    with mp.workdps(40):
        for s in range(2, 24):
            ser = mp.nsum(lambda m: 1 / (m + 1) ** s, [0, mp.inf])
            check(abs(ser - mp.zeta(s)) < mp.mpf(10) ** -30, f"ZetaReal s={s}")


def check_omega_phi0():
    section("Stmt_OmegaPhi0 (random)")
    for _ in range(300 if QUICK else 1500):
        c = random.choice([cfgW, cfgT3])
        n = random.randint(0, 30)
        p = random.randint(1, 400)
        k = random.randint(0, 600)
        check(omegaKP(c, n, p, k) == phi0(c, Fr(n, p), Fr(k - 1, p)), f"OmegaPhi0 {c.name} n={n} p={p} k={k}")


def phi_min_at_int(Tm, P, U):
    """exact min_y phi0(U/P, y) using integer arithmetic: x = U/P, y = w/(2P), w in candidates."""
    Q = 2 * P
    crit = set([0])
    for a, b, cc in Tm:
        if b != 0:
            crit.add((2 * ((-b * a * U) % P)))
    crit = sorted(crit)
    cand = list(crit)
    for i in range(len(crit)):
        lo = crit[i]
        hi = crit[i + 1] if i + 1 < len(crit) else Q
        cand.append((lo + hi) // 2)
    best = None
    for w in cand:
        v = sum(cc * ((2 * a * U + b * w) // Q) for a, b, cc in Tm)
        best = v if best is None or v < best else best
    return best


def phi_terms(c):
    T = []
    for j in range(1, c.q + 1):
        e = c.eta(j)
        if j <= c.r:
            T += [(0, 1, 1), (c.eta0, -1, 1), (-e, 1, -1), (c.eta0 - e, -1, -1), (e, 0, -2)]
        else:
            T += [(c.eta0 - 2 * e, 0, 1), (-e, 1, -1), (c.eta0 - e, -1, -1)]
    return T


def check_phitable():
    section("Stmt_PhiTable (every piece: random x in the piece, all critical y) and Stmt_PhiData")
    tab = read_phitable()
    check(len(tab) == 2602, f"phiTable has {len(tab)} pieces")
    Tm = phi_terms(cfgW)
    # sanity: phi0 literal == integer evaluation
    for _ in range(50):
        U, P = random.randint(0, 999), random.randint(1, 999)
        w = random.randint(0, 2 * P - 1)
        check(phi0(cfgW, Fr(U, P), Fr(w, 2 * P)) == sum(cc * ((2 * a * U + b * w) // (2 * P)) for a, b, cc in Tm),
              "integer phi0 evaluation")
    bad = 0
    for e in tab:
        a, b, v = piece_a(e), piece_b(e), e[4]
        # midpoint and one random interior point (with a random common denominator)
        xs = [(a + b) / 2]
        P = random.randint(10 ** 5, 10 ** 6)
        lo, hi = floor(a * P) + 1, -floor(-b * P) - 1
        if lo <= hi:
            xs.append(Fr(random.randint(lo, hi), P))
        for x in xs:
            if not (a < x < b):
                continue
            m = random.randint(0, 3)
            X = x + m
            val = phi_min_at_int(Tm, X.denominator, X.numerator)
            if val < v:
                bad += 1
                check(False, f"PhiTable piece {e}: phi({x}) = {val} < {v}")
            if x == (a + b) / 2:
                check(val == v, f"PhiTable piece {e}: phi(mid) = {val} != {v}")
    print(f"   pieces checked: {len(tab)}, violations: {bad}")
    # PhiData
    check(all(e[1] > 0 and e[3] > 0 and 0 <= piece_a(e) < piece_b(e) <= 1 for e in tab), "PhiData.bounds")
    check(all(piece_b(tab[i]) <= piece_a(tab[i + 1]) for i in range(len(tab) - 1)), "PhiData.sorted")
    S = sum((phiWeight(mu(cfgW, cfgW.q - cfgW.r), 20, e) for e in tab), Fr(0))
    print(f"   phiSumQ = {float(S):.10f};  muSum - phiSumQ = {1341 - float(S):.10f}  (C2hi = {float(C2hi)})")
    check(Fr(muSum(cfgW)) - S < C2hi, "PhiData.sum")
    return tab


def check_growth(tab):
    section("Stmt_DenomGrowth (trend; PNT is asymptotic, small n are far from the limit)")
    Tm = phi_terms(cfgW)
    for n in ([5, 10] if QUICK else [5, 10, 20, 40]):
        t0 = time.time()
        logD = math.log(Dprod(cfgW, n))
        logP = math.log(PhiN(cfgW, n))
        # lower bound of log PhiN through the table (what the Lean proof uses)
        lb = 0.0
        for p in range(2, 60 * n + 1):
            if isprime(p) and cfgW.h0(n) < p * p:
                x = Fr(n % p, p)
                for e in tab:
                    if piece_a(e) < x < piece_b(e):
                        if Fr(n, p) >= Fr(1, 60) and (Fr(n, p) < 1 or Fr(n, p) < 21):
                            lb += e[4] * math.log(p)
                        break
        check(logP >= lb - 1e-9, f"log PhiN >= table bound (n={n})")
        print(f"   n={n:3d}: log Dprod/n = {logD / n:9.3f}, log PhiN/n = {logP / n:8.3f} (table bound {lb / n:8.3f}),"
              f" log Delta/n = {(logD - logP) / n:8.3f}   [{time.time() - t0:.0f}s]", flush=True)
    print("   (limits: 1341 and 593.95 (table: 593.51), so log Delta/n -> C2 = 747.05; Stmt_DenomGrowth needs < 748)")


# ---------------------------------------------------------------- Stmt_AuxPrime (l-adic evaluation)

def aux_padic(c, n, l, P=30):
    """A0 c n and Acoef c n s, evaluated l-adically from the literal definitions (Gk, B, A0, Acoef,
    harm) in Z/l^P.  Exact modulo l^P: every quantity that is inverted is asserted to be an l-unit,
    except inside the rational bricks of a k with at least q - r factors X (then Gk = 0 mod X^{q-r}
    literally, whatever the inverses are).  A product of consecutive linear factors (i - k + X) is
    formed as (product of the constants) * exp(sum of the logarithm series), from prefix tables of
    unit powers; the factors with l | (i - k) are multiplied in explicitly (they occur only in the
    polynomial bricks).  Needs l > q - r (division by m <= q - r - 1 in log/exp).
    Returns (l^E A0 mod l^P, E, {s: Acoef s mod l^P for r <= s <= q-1}), E = q - 1 (clears every
    harmonic denominator l^{j-1})."""
    q, r = c.q, c.r
    L = q - r                        # B(j, k) = [X^{q-j}] Gk, q - j in 0 .. q-r-1
    assert l > L
    mod = l ** P
    h0 = c.h0(n)
    h1 = c.h(n, 1)
    K = list(range(h1, nsub(h0, h1) + 1))
    V = h0 + 2                       # |i - k| <= V
    inv = lambda x: pow(x % mod, -1, mod)
    invm = [0] + [inv(m) for m in range(1, L)]
    # prefix tables over v in [-V, V]: PP = product of the units, S[m] = sum of unit^{-m}
    PP, S = {}, {m: {} for m in range(1, L)}
    acc, accs = 1, [0] * L
    PP[-V - 1] = 1
    for m in range(1, L):
        S[m][-V - 1] = 0
    for v in range(-V, V + 1):
        if v % l != 0:
            acc = acc * v % mod
            iv = inv(v)
            pw = 1
            for m in range(1, L):
                pw = pw * iv % mod
                accs[m] = (accs[m] + pw) % mod
        PP[v] = acc
        for m in range(1, L):
            S[m][v] = accs[m]

    def unit_range(A, B):            # v in [A, B]: product of the units, their power sums, the non-units
        if A > B:
            return 1, [0] * L, []
        prod = PP[B] * inv(PP[A - 1]) % mod
        ps = [0] + [(S[m][B] - S[m][A - 1]) % mod for m in range(1, L)]
        nonunits = list(range(A + (-A) % l, B + 1, l))    # the multiples of l (0 included)
        return prod, ps, nonunits

    def ser_mul(Aa, Bb):
        out = [0] * L
        for i, a in enumerate(Aa):
            if a:
                for j in range(L - i):
                    out[i + j] = (out[i + j] + a * Bb[j]) % mod
        return out

    def ser_exp(lam):                # exp of a series with lam[0] = 0
        E = [1] + [0] * (L - 1)
        for m in range(1, L):
            E[m] = sum(i * lam[i] * E[m - i] for i in range(1, m + 1)) % mod * invm[m] % mod
        return E

    B = {}
    for k in K:
        st = {"const": 1, "lam": [0] * L, "extra": []}

        def mult(i_lo, i_hi, sign):    # (prod_{i in [i_lo, i_hi)} (i - k + X))^{sign}
            pr, ps, nu = unit_range(i_lo - k, i_hi - 1 - k)
            if sign < 0:
                assert not nu, "an l-divisible factor would be inverted"
                pr = inv(pr)
            st["const"] = st["const"] * pr % mod
            lam = st["lam"]
            for m in range(1, L):     # log(c + X) = log c + sum_m (-1)^{m+1} X^m / (m c^m)
                t = ps[m] * invm[m] % mod
                lam[m] = (lam[m] + (t if (m % 2 == 1) == (sign > 0) else -t)) % mod
            if sign > 0:
                st["extra"].extend(nu)

        xpow = sum(1 for j in range(r + 1, q + 1)
                   if not (c.h(n, j) <= k < nsub(h0, c.h(n, j)) + 1))
        if xpow >= L:                 # Gk = X^{q-r} * (...): every B(j, k) vanishes, literally
            for j in range(r + 1, q + 1):
                B[(j, k)] = 0
            continue
        lin = [(h0 - 2 * k) % mod, 2] + [0] * (L - 2)
        for j in range(1, r + 1):
            hj = c.h(n, j)
            f = math.factorial(nsub(hj, 1))
            assert f % l != 0
            st["const"] = st["const"] * inv(f) % mod * inv(f) % mod
            mult(1, hj, +1)                               # polyBrick h_j 1 k
            mult(nsub(h0, hj) + 1, h0, +1)                # polyBrick h0 (h0 - h_j + 1) k
        for j in range(r + 1, q + 1):
            hj = c.h(n, j)
            a, b = hj, nsub(h0, hj) + 1                   # ratBrick h_j (h0 - h_j + 1) k
            f = math.factorial(nsub(nsub(b, a), 1))
            assert f % l != 0
            st["const"] = st["const"] * f % mod
            if a <= k < b:
                mult(a, k, -1)
                mult(k + 1, b, -1)
            else:
                mult(a, b, -1)
        G = [x * st["const"] % mod for x in ser_exp(st["lam"])]
        G = ser_mul(G, lin)
        for v in st["extra"]:
            G = ser_mul(G, [v % mod, 1] + [0] * (L - 2))
        G = ([0] * xpow + G)[:L]
        for j in range(r + 1, q + 1):
            B[(j, k)] = G[q - j]
    Acoef_ = {s: math.comb(nsub(s, 1), nsub(r, 1)) * sum(B[(s + 1, k)] for k in K) % mod
              for s in range(r, q)}
    # l^E harm(N, s) for all N <= h0 - 2 h1: the units m directly, the multiples m = l t (t < l) as
    # l^{E-s} t^{-s}
    E = q - 1
    Nmax = nsub(h0, 2 * h1)
    assert Nmax < l * l
    lE = pow(l, E, mod)
    HP = {}
    for s in range(r, q):
        row, tot = [0], 0
        for m in range(1, Nmax + 1):
            if m % l:
                tot += lE * pow(inv(m), s, mod)
            else:
                tot += pow(l, E - s, mod) * pow(inv(m // l), s, mod)
            row.append(tot % mod)
        HP[s] = row
    A0l = 0
    for j in range(r + 1, q + 1):
        inner = sum(B[(j, k)] * HP[nsub(j, 1)][nsub(k, h1)] for k in K if B[(j, k)])
        A0l = (A0l + math.comb(nsub(j, 2), nsub(r, 1)) * inner) % mod
    return A0l, E, Acoef_


def vmod(x, l, P):
    """l-adic valuation of an element of Z/l^P (None if it is 0 mod l^P, i.e. valuation >= P)."""
    x %= l ** P
    if x == 0:
        return None
    v = 0
    while x % l == 0:
        x //= l
        v += 1
    return v


def red(x, l, P):
    """An l-integral Fraction modulo l^P."""
    x = Fr(x)
    assert vp(x, l) >= 0
    return x.numerator * pow(x.denominator, -1, l ** P) % l ** P


def check_auxprime(nmax, exact_ns):
    section("Stmt_AuxPrime (n even, l = 63n - 1 prime): v_l(A0 cfgW n) < 0 <= v_l(Acoef cfgW n s), s in window")
    P = 30
    for n in exact_ns:
        l = 63 * n - 1
        t0 = time.time()
        F = Form(cfgW, n)
        A0v = F.A0()
        As = {s: F.Acoef(s) for s in range(cfgW.r, cfgW.q)}
        vA0 = vp(A0v, l)
        vAs = [vp(As[s], l) for s in window(cfgW)]
        print(f"   [exact, literal Form] n={n}, l={l}: v_l(A0) = {vA0}, v_l(A_s) (s = 7, 9, ..., 21) = {vAs}"
              f"   [{time.time() - t0:.0f}s]", flush=True)
        check(vA0 < 0, f"AuxPrime exact: v_l(A0) < 0 (n={n})")
        check(all(v >= 0 for v in vAs), f"AuxPrime exact: v_l(A_s) >= 0 (n={n})")
        # the l-adic evaluation agrees with the exact values modulo l^P
        A0l, E, Al = aux_padic(cfgW, n, l, P)
        check(A0l == red(A0v * Fr(l) ** E, l, P), f"aux_padic: l^E A0 = exact mod l^{P} (n={n})")
        for s in range(cfgW.r, cfgW.q):
            check(Al[s] == red(As[s], l, P), f"aux_padic: A_{s} = exact mod l^{P} (n={n})")
    for n in range(2, nmax + 1, 2):
        l = 63 * n - 1
        if not isprime(l):
            continue
        t0 = time.time()
        A0l, E, Al = aux_padic(cfgW, n, l, P)
        vA0 = vmod(A0l, l, P)
        vA0 = None if vA0 is None else vA0 - E
        vAs = [vmod(Al[s], l, P) for s in window(cfgW)]
        check(vA0 is not None and vA0 < 0, f"AuxPrime l-adic: v_l(A0) < 0 (n={n})")
        check(all(v is None or v >= 0 for v in vAs), f"AuxPrime l-adic: v_l(A_s) >= 0 (n={n})")
        check(vA0 == -5, f"v_l(A0) = -5 (Theorem N) (n={n})")
        check(Al[cfgW.r] == 0 and all(Al[s] == 0 for s in range(cfgW.r + 1, cfgW.q, 2)),
              f"A_r = A_even = 0 mod l^P (n={n})")
        print(f"   [l-adic mod l^{P}] n={n:3d}, l={l:5d}: v_l(A0) = {vA0}, v_l(A_s) = "
              f"{['>=%d' % P if v is None else v for v in vAs]}   [{time.time() - t0:.1f}s]", flush=True)


def check_lemma20():
    section("Stmt_L20Upper: recorded exact values, n <= 9 (docs/window/exact_r5_q23_n9.jsonl)")
    here = os.path.dirname(os.path.abspath(__file__))
    path = os.path.join(here, "..", "docs", "window", "exact_r5_q23_n9.jsonl")
    if not os.path.exists(path):
        print("   (file missing, skipped)")
        return {}
    ref = {}
    for line in open(path):
        d = json.loads(line)
        n = d["n"]
        ref[n] = (d["log_abs_F"], d["sign"])
        check(d["log_abs_F"] <= -float(C0lo) * n, f"L20Upper at n={n}")
        check(d["sign"] != 0, f"recorded F_n != 0 at n={n}")
        print(f"   n={n}: log|F_n|/n = {d['log_abs_F'] / n:.4f} (need <= {-float(C0lo)}), sign {d['sign']:+d}")
    return ref


def main():
    t0 = time.time()
    if AUX_ONLY:
        check_basic()
        check_auxprime(40 if QUICK else 60, [4])
        print(f"\n{NCHECK[0]} checks, {len(FAILS)} failed, {time.time() - t0:.0f}s")
        if FAILS:
            print("FAILED:", FAILS[:20])
            sys.exit(1)
        return
    check_basic()
    check_bricks()
    check_harmonic()
    check_omega_phi0()
    check_zeta_real()
    ref = check_lemma20()
    section("Laurent data, CoeffVanish, Lemma19, PF, linear form (exact)")
    F3, v3 = check_form(cfgT3, 1)
    check_engine(cfgT3, 1, v3)
    if not QUICK:
        check_form(cfgT3, 2)
        check_form(cfgT3, 3)
    FW, vW = check_form(cfgW, 1, ref.get(1))
    check_engine(cfgW, 1, vW)
    if not QUICK:
        check_form(cfgW, 2, ref.get(2))
    if mp is not None and v3 is not None:
        check_series(cfgT3, 1, v3, 400 if QUICK else 1500)
    tab = check_phitable()
    check_growth(tab)
    check_auxprime(40 if QUICK else 60, [4])
    print(f"\n{NCHECK[0]} checks, {len(FAILS)} failed, {time.time() - t0:.0f}s")
    if FAILS:
        print("FAILED:", FAILS[:20])
        sys.exit(1)


if __name__ == "__main__":
    main()
