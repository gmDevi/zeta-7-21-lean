# Auditor-2: Barnes integral for larger n using g(-y) = conj g(y):  F = (1/pi) Re int_0^inf g,
# restricted to |y - y*| <= W(n) (tau-units), where the integrand is > e^{-120} of its peak; compared with (F).
import sys, time, mpmath as mp
from a2_barnes import V5, leading, eta, e0, r
n = int(sys.argv[1]); W = mp.mpf(sys.argv[2]) if len(sys.argv) > 2 else mp.mpf(4)
mp.mp.dps = 40
xs = mp.mpf('159.356418053794830583663509361'); ys = mp.mpf('8.39371237206876207347965336941')
h0 = e0 * n + 2; h = [e * n + 1 for e in eta]
lNh = (sum(mp.loggamma(h0 - 2 * hj + 1) for hj in h[r:]) - 2 * sum(mp.loggamma(hj) for hj in h[:r]))
def g(s):
    t = n * (mp.mpc(xs, s) - e0)
    lg = (mp.log(h0 + 2 * t) + 5 * mp.loggamma(h0 + t) + 5 * mp.loggamma(-t) + sum(mp.loggamma(hj + t) - mp.loggamma(1 + h0 - hj + t) for hj in h))
    return mp.exp(lg + lNh) * V5(mp.cos(mp.pi * t)) * n
t0 = time.time()
step = mp.mpf(1) / (4 * n) if n < 40 else mp.mpf(1) / (2 * n)
lo = max(mp.mpf(0), ys - W); hi = ys + W
edges = [lo]
while edges[-1] < hi: edges.append(min(hi, edges[-1] + step))
tot = mp.mpf(0)
for a, b in zip(edges[:-1], edges[1:]):
    tot += mp.quad(g, [a, b])
F = mp.re(tot) / mp.pi
edge_ratio = max(abs(g(lo)), abs(g(hi))) / abs(g(ys))
t3 = mp.mpc(xs, ys)
f2 = mp.mpc('0.27212245899863666045', '0.54298742193168633591')
f0v = mp.mpc('-750.711694833944313681960496431', '-1465.90909590539762207106350328')
lead, B = leading(n, t3, f2, f0v)
print("n=%d W=%s: F=%s log|F|/n=%s | lead=%s ratio=%s | n*(ratio-1)=%s | edge/peak=%s [%.0fs]" % (
    n, mp.nstr(W, 3), mp.nstr(F, 15), mp.nstr(mp.log(abs(F)) / n, 12), mp.nstr(lead, 12), mp.nstr(F / lead, 10),
    mp.nstr(n * (F / lead - 1), 6), mp.nstr(edge_ratio, 3), time.time() - t0))
