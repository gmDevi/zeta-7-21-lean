# Auditor-2 (window): Barnes integral on the line Re tau = x*, tau-units, many short segments.
#   F~_n = (N_h/2pi) int_R G(t) V5(cos pi t) dy_t,  t = n(tau - eta0),  tau = x* + i s,  dy_t = n ds.
import sys, time
import mpmath as mp
from a2_barnes import V5, leading, eta, e0, r

def run(n, dps=45):
    mp.mp.dps = dps
    xs = mp.mpf('159.356418053794830583663509361'); ys = mp.mpf('8.39371237206876207347965336941')
    h0 = e0 * n + 2
    h = [e * n + 1 for e in eta]
    lNh = (sum(mp.loggamma(h0 - 2 * hj + 1) for hj in h[r:]) - 2 * sum(mp.loggamma(hj) for hj in h[:r]))
    def g(s):
        t = n * (mp.mpc(xs, s) - e0)
        lg = (mp.log(h0 + 2 * t) + 5 * mp.loggamma(h0 + t) + 5 * mp.loggamma(-t)
              + sum(mp.loggamma(hj + t) - mp.loggamma(1 + h0 - hj + t) for hj in h))
        return mp.exp(lg + lNh) * V5(mp.cos(mp.pi * t)) * n
    L = mp.mpf(1) / (2 * n)
    tot = mp.quad(g, [ys - L, ys + L])
    for direction in (1, -1):
        a = ys + direction * L
        small = 0
        while small < 6:
            b = a + direction * L
            v = mp.quad(g, sorted([a, b]))
            if direction < 0: v = -v if a < b else v
            tot += v if direction > 0 else mp.quad(g, [b, a])
            if abs(v) < abs(tot) * mp.mpf(10) ** (-dps - 3): small += 1
            else: small = 0
            a = b
            if abs(a - ys) > 400: break
    return tot / (2 * mp.pi)

if __name__ == "__main__":
    t3 = mp.mpc('159.356418053794830583663509361', '8.39371237206876207347965336941')
    f2 = mp.mpc('0.27212245899863666045', '0.54298742193168633591')
    f0v = mp.mpc('-750.711694833944313681960496431', '-1465.90909590539762207106350328')
    for n in [int(a) for a in sys.argv[1:]]:
        t0 = time.time()
        v = run(n)
        mp.mp.dps = 40
        lead, B = leading(n, t3, f2, f0v)
        print("n=%d contour F=%s imag/|F|=%s log|F|=%s | lead=%s ratio=%s [%.0fs]" % (
            n, mp.nstr(mp.re(v), 20), mp.nstr(abs(mp.im(v) / mp.re(v)), 3), mp.nstr(mp.log(abs(mp.re(v))), 20),
            mp.nstr(lead, 12), mp.nstr(mp.re(v) / lead, 10), time.time() - t0))
        sys.stdout.flush()
