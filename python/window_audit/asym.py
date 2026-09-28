# Stirling prefactor and the leading term (F) of proof.md, checked against the Barnes integral.
import sys, time
import mpmath as mp
from exact_indep import config

r, q, e0, eta = config('W')
mp.mp.dps = 40
Ceta = mp.fsum((e0 - 2 * e) * mp.log(e0 - 2 * e) for e in eta[r:]) - 2 * mp.fsum(e * mp.log(e) for e in eta[:r])
xl = lambda z: z * mp.log(z)
f = lambda t: r * xl(t) + r * xl(e0 - t) + mp.fsum(xl(t - e0 + e) - xl(t - e) for e in eta) + Ceta
fp = lambda t: r * mp.log(t) - r * mp.log(e0 - t) + mp.fsum(mp.log(t - e0 + e) - mp.log(t - e) for e in eta)
fpp = lambda t: r / t + r / (e0 - t) + mp.fsum(1 / (t - e0 + e) - 1 / (t - e) for e in eta)
f0 = lambda t: r * e0 * mp.log(e0 - t) + mp.fsum(e * mp.log(t - e) - (e0 - e) * mp.log(t - e0 + e) for e in eta) + Ceta
tau3 = mp.findroot(lambda t: fp(t) - 3j * mp.pi, mp.mpc('159.356418', '8.393712'))
def A(t):
    v = (2 * mp.pi) ** 9 * (2 * t - e0) * t ** mp.mpf(7.5) * (e0 - t) ** mp.mpf(-2.5)
    for e in eta: v *= (t - e0 + e) ** mp.mpf(0.5) * (t - e) ** mp.mpf(-1.5)
    for e in eta[r:]: v *= mp.sqrt(e0 - 2 * e)
    for e in eta[:r]: v /= e
    return v
print("tau3 =", mp.nstr(tau3, 20), " f'' =", mp.nstr(fpp(tau3), 12), " A(tau3) =", mp.nstr(A(tau3), 12))

def logNhG(n, t, lam):
    h0 = e0 * n + 2; h = [e * n + 1 for e in eta]
    logNh = mp.fsum(mp.loggamma(h0 - 2 * h[j] + 1) for j in range(r, q)) - 2 * mp.fsum(mp.loggamma(h[j]) for j in range(r))
    return logNh + mp.log(h0 + 2 * t) + r * mp.loggamma(h0 + t) + r * mp.loggamma(-t) + \
        mp.fsum(mp.loggamma(hj + t) - mp.loggamma(1 + h0 - hj + t) for hj in h) - 1j * mp.pi * lam * t

print("Stirling check at tau = tau3 and at tau = x*+2i, lambda = 3:  log[N_h G e^{-i pi 3 t}] - log[n^-13 A e^{n Phi_3}]  (Im mod 2 pi)")
for tau in (tau3, mp.mpc(mp.re(tau3), 2)):
    for n in (25, 50, 100, 200, 400, 800):
        t = n * (tau - e0)
        d = logNhG(n, t, 3) - (-13 * mp.log(n) + mp.log(A(tau)) + n * (f(tau) - 3j * mp.pi * tau))
        dim = mp.im(d) - 2 * mp.pi * mp.nint(mp.im(d) / (2 * mp.pi))
        print("   tau=%s n=%4d  Re diff = %s  Im diff = %s   n*|diff| = %s" % (mp.nstr(tau, 8), n, mp.nstr(mp.re(d), 6), mp.nstr(dim, 6), mp.nstr(n * abs(mp.mpc(mp.re(d), dim)), 6)))

Bc = 1j * A(tau3) * mp.sqrt(2 * mp.pi / fpp(tau3))
beta = mp.arg(Bc) - mp.pi / 2
omega = mp.im(f0(tau3)); C0 = -mp.re(f0(tau3))
print("|B| =", mp.nstr(abs(Bc), 12), " beta =", mp.nstr(beta, 12), " omega/pi =", mp.nstr(omega / mp.pi, 15), " C0 =", mp.nstr(C0, 18))
def lead(n):
    return abs(Bc) / (24 * mp.pi) * mp.mpf(n) ** mp.mpf(-12.5) * mp.exp(-C0 * n) * mp.cos(n * omega + beta)

def barnes_local(n, half=3.0, step=0.5):
    # integrate only |Im tau - y*| <= half (the rest is < e^{-0.5 n * ...}); full V5 integrand
    h0 = e0 * n + 2; h = [e * n + 1 for e in eta]
    M = (mp.re(tau3) - e0) * n
    def integrand(y):
        t = mp.mpc(M, y)
        c = mp.cos(mp.pi * t)
        return mp.exp(logNhG(n, t, 0)) * (c ** 3 + 2 * c) / 3
    ys = mp.im(tau3) * n
    lo = ys - half * n if n >= 10 else -12 * n - 30
    hi = ys + half * n if n >= 10 else 40 * n + 60
    pts = [lo + i * step for i in range(int((hi - lo) / step) + 1)]
    if n < 10:
        pts = [-mp.inf] + pts + [mp.inf]
        return mp.re(mp.quad(integrand, pts)) / (2 * mp.pi)
    # n >= 10: the conjugate saddle at -y* contributes the same real part (J_{-3} = -conj J_3)
    ptsm = [-p for p in reversed(pts)]
    return (mp.re(mp.quad(integrand, pts)) + mp.re(mp.quad(integrand, ptsm))) / (2 * mp.pi)

if __name__ == "__main__":
    mp.mp.dps = 30
    ns = [int(x) for x in sys.argv[1].split(",")]
    for n in ns:
        t0 = time.time()
        Fb = barnes_local(n)
        L = lead(n)
        print("n=%4d  F_n(contour) = %s   lead = %s   ratio = %s   log|F|/n = %s  sign ok: %s  (%ds)" % (
            n, mp.nstr(Fb, 12), mp.nstr(L, 12), mp.nstr(Fb / L, 8), mp.nstr(mp.log(abs(Fb)) / n, 10), mp.sign(Fb) == mp.sign(L), time.time() - t0))
