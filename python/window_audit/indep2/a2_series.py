# Auditor-2 (window): F~_n by direct high-precision summation of the defining series
#   F~_n = sum_{t>=0} [eps^4] R~(t+eps),  R~(t) = N_h (h0+2t) prod_{i=1}^{h0-1}(t+i)^5 / prod_{j=1}^{23} prod_{i=h_j}^{h0-h_j}(t+i)
# (no partial fractions, no bricks).  [eps^4] via the log-derivative power sums.
import sys, time
import mpmath as mp
r, q, e0 = 5, 23, 160
eta = [47, 47, 47, 47, 48, 50, 50] + [j + 43 for j in range(8, 24)]

def data(n):
    h0 = e0 * n + 2
    h = [e * n + 1 for e in eta]
    mult = {}
    for i in range(1, h0):
        mult[i] = mult.get(i, 0) + r
    for hj in h:
        for i in range(hj, h0 - hj + 1):
            mult[i] = mult.get(i, 0) - 1
    mult = {i: m for i, m in mult.items() if m != 0}
    return h0, h, mult

def logNh(n, h0, h):
    return (sum(mp.log(mp.factorial(h0 - 2 * hj)) for hj in h[r:])
            - 2 * sum(mp.log(mp.factorial(hj - 1)) for hj in h[:r]))

def Fn(n, T, dps):
    mp.mp.dps = dps
    h0, h, mult = data(n)
    lN = logNh(n, h0, h)
    items = sorted(mult.items())
    total = mp.mpf(0)
    maxlog = -mp.inf
    last = None
    for t in range(0, T + 1):
        a = mp.mpf(h0 + 2 * t)
        # log R~(t) and power sums
        lR = lN + mp.log(a)
        p = [None, mp.mpf(0), mp.mpf(0), mp.mpf(0), mp.mpf(0)]
        u = 2 / a
        p[1] += u; p[2] += u ** 2; p[3] += u ** 3; p[4] += u ** 4
        for i, m in items:
            x = mp.mpf(t + i)
            lR += m * mp.log(x)
            y = 1 / x
            y2 = y * y
            p[1] += m * y; p[2] += m * y2; p[3] += m * y2 * y; p[4] += m * y2 * y2
        c1, c2, c3, c4 = p[1], -p[2] / 2, p[3] / 3, -p[4] / 4
        coef = c4 + c1 * c3 + c2 * c2 / 2 + c1 * c1 * c2 / 2 + c1 ** 4 / 24
        term = mp.exp(lR) * coef
        total += term
        if term != 0:
            maxlog = max(maxlog, mp.log(abs(term)))
        last = term
    return total, maxlog, last

if __name__ == "__main__":
    for n, T, dps in [(1, 1000, 700), (2, 1600, 1250), (3, 2200, 1800)]:
        t0 = time.time()
        # low-precision scout for the size of the largest term
        F, ml, last = Fn(n, T, dps)
        lF = mp.log(abs(F))
        print("n=%d T=%d dps=%d: log|F| = %s sign %s | log max|term| = %s | log|last term| = %s | %.0f s" % (
            n, T, dps, mp.nstr(lF, 20), '+' if F > 0 else '-', mp.nstr(ml, 8),
            mp.nstr(mp.log(abs(last)), 8), time.time() - t0))
        sys.stdout.flush()
