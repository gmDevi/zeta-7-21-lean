# Auditor-2 (window): the Barnes integral for n = 1 on the whole line Re tau = x* with fine segments
# (length 0.1 on [-150, 150], tanh-sinh on each, plus the two tails), and the magnitude profile
# log|g(y)| (symmetric in y: g(-y) = conj g(y)).  The coarser a2_barnes2.py is only accurate to 4e-9 at n = 1.
#   F~_1 = (N_h/2pi) int_R G(t) V5(cos pi t) dy_t,  t = n(tau - eta0),  tau = x* + i s.
import mpmath as mp, time
from a2_barnes import V5, eta, e0, r
n = 1; mp.mp.dps = 40
xs = mp.mpf('159.356418053794830583663509361'); ys = mp.mpf('8.39371237206876207347965336941')
h0 = e0 * n + 2; h = [e * n + 1 for e in eta]
lNh = (sum(mp.loggamma(h0 - 2 * hj + 1) for hj in h[r:]) - 2 * sum(mp.loggamma(hj) for hj in h[:r]))
def g(s):
    t = n * (mp.mpc(xs, s) - e0)
    lg = (mp.log(h0 + 2 * t) + 5 * mp.loggamma(h0 + t) + 5 * mp.loggamma(-t) + sum(mp.loggamma(hj + t) - mp.loggamma(1 + h0 - hj + t) for hj in h))
    return mp.exp(lg + lNh) * V5(mp.cos(mp.pi * t)) * n
# magnitude profile
for s in [-200,-100,-60,-40,-20,-8.39,-4,-1,0,1,4,8.39,12,20,40,60,100,200]:
    print(s, mp.nstr(mp.log(abs(g(mp.mpf(s)))), 8))
t0=time.time()
tot = 0; maxerr = 0
edges = [mp.mpf(x)/10 for x in range(-1500, 1501)]
for a, b in zip(edges[:-1], edges[1:]):
    v, e = mp.quad(g, [a, b], error=True)
    tot += v; maxerr = max(maxerr, e)
tot += mp.quad(g, [-mp.inf, -150]) + mp.quad(g, [150, mp.inf])
print("F =", mp.nstr(tot / (2 * mp.pi), 25), " max seg err", mp.nstr(maxerr, 3), "%.0fs" % (time.time() - t0))
