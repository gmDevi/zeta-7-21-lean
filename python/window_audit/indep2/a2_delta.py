# log(Delta_n)/n for cfgW with exact omega_p (min over a full residue system), own code.
import sys, math
r, q, e0 = 5, 23, 160
eta = [47, 47, 47, 47, 48, 50, 50] + [j + 43 for j in range(8, 24)]
def primes(N):
    s = bytearray([1]) * (N + 1); s[0] = s[1] = 0
    for i in range(2, int(N ** 0.5) + 1):
        if s[i]: s[i * i::i] = bytearray(len(s[i * i::i]))
    return [i for i in range(N + 1) if s[i]]
def logpsi(x, P):
    return sum(math.log(p) * int(math.log(x) / math.log(p) + 1e-12) for p in P if p <= x)
for n in [int(a) for a in sys.argv[1:]]:
    h0 = e0 * n + 2; h = [None] + [e * n + 1 for e in eta]
    def om(p, k):
        s = 0
        for j in range(1, r + 1):
            s += (k - 1) // p + (h0 - k - 1) // p - (k - h[j]) // p - (h0 - h[j] - k) // p - 2 * ((h[j] - 1) // p)
        for j in range(r + 1, q + 1):
            s += (h0 - 2 * h[j]) // p - (k - h[j]) // p - (h0 - h[j] - k) // p
        return s
    P = primes(63 * n)
    logD = 6 * logpsi(63 * n, P) + logpsi(62 * n, P) + logpsi(61 * n, P) + 14 * logpsi(60 * n, P)
    logPhi = 0.0
    for p in P:
        if p > 60 * n or p * p <= h0: continue
        # candidate k: thresholds of the floor terms in k (k = c mod p), and their successors
        cands = set()
        for c in [1, h0 - 1] + [h[j] for j in range(1, q + 1)] + [h0 - h[j] + 1 for j in range(1, q + 1)]:
            cands.add(c % p); cands.add((c + 1) % p); cands.add((c - 1) % p)
        w = min(om(p, k) for k in cands)
        if n <= 20:
            assert w == min(om(p, k) for k in range(p))
        logPhi += max(w, 0) * math.log(p)
    print("n=%d log Dprod/n=%.4f log Phi/n=%.4f log Delta/n=%.4f" % (n, logD / n, logPhi / n, (logD - logPhi) / n))
