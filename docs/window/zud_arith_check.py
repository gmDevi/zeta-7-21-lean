"""EXACT rational check of Zudilin's Lemma 19 (denominators with Phi_n) for given (r, eta0, eta), small n.
Computes the linear form Ftilde_n = c_0 + sum_s c_s zeta(s) exactly (Fractions), then checks
  L_n = D_{m1}^r D_{m2} ... D_{m_{q-r}} / Phi_n  makes every c_s and c_0 integral, prime by prime,
with m0 = max(h_r - 1, h0 - 2 h_{r+1}), m_j = max(m0, h0 - h_1 - h_{r+j}),
Phi_n = prod_{sqrt(h0) < p <= m_{q-r}} p^{psi_p},  psi_p = min_{h_{r+1}<=k<=h0-h_{r+1}} omega_{k,p}.
Also reports the true lcm-denominator vs L_n (slack per prime) and which zeta(s) occur.
usage: python zud_arith_check.py <dir> r eta0 "e1,..,eq" n
"""
import sys, json, math
from fractions import Fraction as Fr
from sympy import primerange

def lcm_upto(N):
    L = 1
    for p in primerange(2, N + 1):
        pk = p
        while pk * p <= N: pk *= p
        L *= pk
    return L

def vp(x, p):
    if x == 0: return 10**9
    v = 0
    while x % p == 0: x //= p; v += 1
    return v

def vpF(f, p):
    return vp(f.numerator, p) - vp(f.denominator, p)

def main():
    r = int(sys.argv[2]); e0 = int(sys.argv[3]); e = [int(x) for x in sys.argv[4].split(',')]; n = int(sys.argv[5])
    q = len(e); h0 = e0 * n + 2; h = [x * n + 1 for x in e]
    maxs = q + r + 1
    Hm = [[Fr(0)] * (h0 + 2) for _ in range(maxs + 1)]
    for m in range(1, maxs + 1):
        acc = Fr(0)
        for d in range(1, h0 + 2):
            acc += Fr(1, d ** m); Hm[m][d] = acc
    def psum(a, b, k, m):
        if a > b: return Fr(0)
        lo, hi = a - k, b - k; s = Fr(0)
        if hi >= 1: s += Hm[m][hi] - (Hm[m][lo - 1] if lo >= 2 else 0)
        if lo <= -1:
            top = -lo; bot = max(1, -hi); v = Hm[m][top] - Hm[m][bot - 1]
            s += v if m % 2 == 0 else -v
        return s
    def iprod(a, b, k):
        P = 1
        for l in range(a, b + 1):
            if l != k: P *= (l - k)
        return P
    norm = Fr(1)
    for hj in h[r:]: norm *= math.factorial(h0 - 2 * hj)
    for hj in h[:r]: norm /= math.factorial(hj - 1) ** 2
    coef = {}; const = Fr(0)
    for k in range(min(h), h0 - min(h) + 1):
        mden = sum(1 for hj in h if hj <= k <= h0 - hj)
        mnum = r + (1 if 2 * k == h0 else 0)
        o = mden - mnum
        if o <= 0: continue
        G0 = Fr(h0 - 2 * k) if 2 * k != h0 else Fr(2)
        G0 *= Fr(iprod(1, h0 - 1, k)) ** r
        for hj in h: G0 /= iprod(hj, h0 - hj, k)
        P = [Fr(0)] * (o + 1)
        for m in range(1, o):
            v = Fr(2, h0 - 2 * k) ** m if 2 * k != h0 else Fr(0)
            v += r * psum(1, h0 - 1, k, m)
            for hj in h: v -= psum(hj, h0 - hj, k, m)
            P[m] = v
        B = [Fr(0)] * o; A = [Fr(0)] * o; A[0] = Fr(1)
        for m in range(1, o): B[m] = (-1) ** (m + 1) * P[m] / m
        for m in range(1, o): A[m] = sum(j * B[j] * A[m - j] for j in range(1, m + 1)) / m
        for i in range(1, o + 1):
            s = i + r - 1
            w = norm * G0 * A[o - i] * (-1) ** (r - 1) * math.comb(i + r - 2, r - 1)
            coef[s] = coef.get(s, Fr(0)) + w
            const -= w * (Hm[s][k - 1] if k >= 2 else 0)
    occurring = sorted(s for s, c in coef.items() if c != 0)
    # Lemma 19 denominators
    m0 = max(h[r - 1] - 1, h0 - 2 * h[r])
    ms = [max(m0, h0 - h[0] - h[r + j]) for j in range(q - r)]
    Ln = lcm_upto(ms[0]) ** r
    for mj in ms[1:]: Ln *= lcm_upto(mj)
    # Phi_n
    def omega(k, p):
        v = 0
        for j, hj in enumerate(h):
            if j < r:
                v += (k - 1) // p + (h0 - k - 1) // p - (k - hj) // p - (h0 - hj - k) // p - 2 * ((hj - 1) // p)
            else:
                v += (h0 - 2 * hj) // p - (k - hj) // p - (h0 - hj - k) // p
        return v
    Phi = 1; psi = {}
    for p in primerange(int(math.isqrt(h0)) + 1, ms[-1] + 1):
        psi[p] = min(omega(k, p) for k in range(h[r], h0 - h[r] + 1))
        Phi *= p ** max(psi[p], 0)
    allc = [const] + [coef[s] for s in occurring]
    ok = True; slack = {}
    for p in primerange(2, h0 + 2):
        vL = vp(Ln, p) - (max(psi.get(p, 0), 0))
        worst = min(vpF(c, p) for c in allc)
        slack[p] = vL + worst
        if vL + worst < 0: ok = False
    trueden = 1
    for c in allc: trueden = trueden * c.denominator // math.gcd(trueden, c.denominator)
    print(json.dumps(dict(r=r, q=q, e0=e0, e=e, n=n, h0=h0, occurring_zeta=occurring, m=ms,
                          log_Ln=math.log(Ln), log_Phi=math.log(Phi), psi={str(p): v for p, v in psi.items() if v},
                          lemma19_holds=ok, min_slack=min(slack.values()),
                          negative_slack_primes=[p for p, v in slack.items() if v < 0],
                          log_true_lcm_den=math.log(trueden),
                          log_Ln_over_Phi=math.log(Ln) - math.log(Phi))))

if __name__ == '__main__':
    main()
