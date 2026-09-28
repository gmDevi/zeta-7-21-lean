"""High-precision evaluation of Zudilin's form
  Ftilde_n = prod_{j>r}(h0-2h_j)! / prod_{j<=r}(h_j-1)!^2 * 1/(r-1)! sum_{t>=0} R^{(r-1)}(t),
  R(t) = (h0+2t) (t+1)_{h0-1}^r / prod_j (t+h_j)_{h0+1-2h_j},  h0 = eta0 n + 2, h_j = eta_j n + 1.
Returns the coefficients c_s of zeta(s) (s = r .. q+r-1) and the value, so one can check which zeta
values occur (expect only odd s in [r+2, q-2]) and measure log|F|/n against the saddle prediction.
Partial fractions via log-derivative power sums; all arithmetic in mpmath at high precision
(exact up to the working precision; no series truncation).
usage: python zud_exact.py <dir> r eta0 "e1,e2,..." nmax dps_per_n
"""
import sys, json, mpmath as mp

def form(r, e0, e, n, dps):
    mp.mp.dps = dps
    h0 = e0 * n + 2
    h = [ej * n + 1 for ej in e]
    q = len(h)
    L = h0 + 5
    maxm = q + 2
    # harmonic tables H[m][N] = sum_{d=1}^N d^-m
    H = [[mp.mpf(0)] * (L + 1) for _ in range(maxm + r + 2)]
    for m in range(1, maxm + r + 2):
        acc = mp.mpf(0); row = H[m]
        for d in range(1, L + 1):
            acc += mp.mpf(1) / mp.mpf(d) ** m; row[d] = acc
    def psum(a, b, k, m):
        """sum_{l=a..b, l != k} 1/(l-k)^m"""
        if a > b: return mp.mpf(0)
        lo, hi = a - k, b - k   # d ranges lo..hi excluding 0
        s = mp.mpf(0)
        if hi >= 1: s += H[m][hi] - (H[m][lo - 1] if lo >= 2 else 0)
        if lo <= -1:
            top = -lo; bot = max(1, -hi)
            v = H[m][top] - H[m][bot - 1]
            s += v if m % 2 == 0 else -v
        return s
    def lprod(a, b, k):
        """log|prod_{l=a..b, l!=k}(l-k)| and sign"""
        if a > b: return mp.mpf(0), 1
        lo, hi = a - k, b - k
        lg = mp.mpf(0); sg = 1
        if hi >= 1: lg += mp.loggamma(hi + 1) - (mp.loggamma(lo) if lo >= 2 else 0)
        if lo <= -1:
            top = -lo; bot = max(1, -hi)
            lg += mp.loggamma(top + 1) - mp.loggamma(bot)
            if (top - bot + 1) % 2 == 1: sg = -sg
        return lg, sg
    lognorm = sum(mp.loggamma(h0 - 2 * hj + 1) for hj in h[r:]) - 2 * sum(mp.loggamma(hj) for hj in h[:r])
    coef = {}   # zeta(s) coefficients
    const = mp.mpf(0)
    kmin = min(h); kmax = h0 - min(h)
    for k in range(kmin, kmax + 1):
        mden = sum(1 for hj in h if hj <= k <= h0 - hj)
        mnum = r * (1 if 1 <= k <= h0 - 1 else 0) + (1 if 2 * k == h0 else 0)
        o = mden - mnum
        if o <= 0: continue
        # G(eps) = R(-k+eps) eps^o ; log G(0) and power sums
        lg = mp.mpf(0); sg = 1
        if 2 * k != h0:
            c = h0 - 2 * k; lg += mp.log(abs(c)); sg *= (1 if c > 0 else -1)
        else:
            lg += mp.log(2)
        a_, s_ = lprod(1, h0 - 1, k); lg += r * a_; sg *= s_ ** r
        for hj in h:
            a_, s_ = lprod(hj, h0 - hj, k); lg -= a_; sg *= s_
        P = [mp.mpf(0)] * (o + 1)
        for m in range(1, o + 1):
            v = mp.mpf(0)
            if 2 * k != h0:
                v += (mp.mpf(2) / (h0 - 2 * k)) ** m   # log(h0-2k+2eps): coefficient 2/c
            v += r * psum(1, h0 - 1, k, m)
            for hj in h:
                v -= psum(hj, h0 - hj, k, m)
            P[m] = v
        # exp(sum_m (-1)^{m+1} P_m eps^m / m) series up to eps^{o-1}
        A = [mp.mpf(0)] * o
        B = [mp.mpf(0)] * o     # B = sum (-1)^{m+1} P_m/m eps^m
        for m in range(1, o):
            B[m] = (-1) ** (m + 1) * P[m] / m
        A[0] = mp.mpf(1)
        for m in range(1, o):   # A' = B' A  => m A_m = sum_{j=1}^m j B_j A_{m-j}
            A[m] = sum(j * B[j] * A[m - j] for j in range(1, m + 1)) / m
        G0 = sg * mp.exp(lg + lognorm)
        for i in range(1, o + 1):
            aik = G0 * A[o - i]
            s = i + r - 1
            w = aik * (-1) ** (r - 1) * mp.binomial(i + r - 2, r - 1)
            coef[s] = coef.get(s, mp.mpf(0)) + w
            const -= w * (H[s][k - 1] if k >= 2 else 0)
    val = const + sum(c * mp.zeta(s) for s, c in coef.items())
    return val, coef, const

if __name__ == '__main__':
    d = sys.argv[1]; r = int(sys.argv[2]); e0 = int(sys.argv[3]); e = [int(x) for x in sys.argv[4].split(',')]
    nmax = int(sys.argv[5]); dpn = int(sys.argv[6])
    out = []
    for n in range(1, nmax + 1):
        val, coef, const = form(r, e0, e, n, 60 + dpn * n)
        big = max(abs(c) for c in coef.values())
        rec = dict(n=n, log_abs_F=float(mp.log(abs(val))), log_abs_F_over_n=float(mp.log(abs(val)) / n),
                   log_maxcoef_over_n=float(mp.log(big) / n),
                   rel_coefs={str(s): float(mp.log(abs(c)) / n) if c != 0 else None for s, c in sorted(coef.items())},
                   sign=int(mp.sign(val)))
        print(json.dumps(rec), flush=True)
        out.append(rec)
