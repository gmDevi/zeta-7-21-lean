# log(Delta_n)/n for cfgW with exact omega_p (Lean definition: min over a full residue system).
import sys, math
import numpy as np
r, q, e0 = 5, 23, 160
eta = [47, 47, 47, 47, 48, 50, 50] + [j + 43 for j in range(8, 24)]
def primes_upto(N):
    s = np.ones(N + 1, dtype=bool); s[:2] = False
    for i in range(2, int(N ** 0.5) + 1):
        if s[i]: s[i * i::i] = False
    return np.nonzero(s)[0]
def psi(m, P):
    return sum(math.log(p) * int(math.log(m) / math.log(p) + 1e-12) for p in P if p <= m)
for n in map(int, sys.argv[1].split(",")):
    h0 = e0 * n + 2; h = [e * n + 1 for e in eta]
    m0 = max(h[r - 1] - 1, h0 - 2 * h[r])
    mj = [max(m0, h0 - h[0] - h[r + j - 1]) for j in range(1, q - r + 1)]
    P = primes_upto(max(mj))
    logD = r * psi(mj[0], P) + sum(psi(m, P) for m in mj[1:])
    logPhi = 0.0
    for p in P:
        p = int(p)
        if p > mj[-1] or p * p <= h0: continue
        k = np.arange(p, dtype=np.int64)
        w = np.zeros(p, dtype=np.int64)
        for j in range(r):
            w += (k - 1) // p + (h0 - k - 1) // p - (k - h[j]) // p - (h0 - h[j] - k) // p - 2 * ((h[j] - 1) // p)
        for j in range(r, q):
            w += (h0 - 2 * h[j]) // p - (k - h[j]) // p - (h0 - h[j] - k) // p
        om = int(w.min())
        logPhi += max(om, 0) * math.log(p)
    print("n=%4d  log Dprod/n = %.3f  log Phi_n/n = %.3f  log Delta_n/n = %.3f" % (n, logD / n, logPhi / n, (logD - logPhi) / n), flush=True)
