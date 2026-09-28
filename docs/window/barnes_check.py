"""barnes_check.py -- NUMERICAL validation of the Barnes representation (Prop. A) and of the two-term asymptotics.
  F~_n = (N_h/pi) * sum_{lambda in {1,3,...,r-2}} c_lambda * Im J_lambda,
  J_lambda = int_{M-i inf}^{M+i inf} G(t) e^{-i pi lambda t} dt,   M = n (x* - eta0)  (line through the dominant saddle),
  G(t) = (h0+2t) Gamma(h0+t)^r Gamma(-t)^r prod_j Gamma(h_j+t)/Gamma(1+h0-h_j+t),
  N_h = prod_{j>r} (h0-2h_j)! / prod_{j<=r} (h_j-1)!^2,   V_r(cos pi t) = sum_lambda c_lambda (e^{i pi lambda t} + e^{-i pi lambda t})
  (V_3 = y -> c_1 = 1/2;  V_5 = (y^3+2y)/3 -> c_3 = 1/24, c_1 = 11/24).
Compares with exact F~_n (zud_exact.py output, n<=9), then evaluates larger n and the saddle formula
  F~_n^asym = (c_d/pi) Im[ i n C_n(tau_d) sqrt(2 pi/(n f''(tau_d))) e^{n f0(tau_d)} ],  C_n(tau) := N_h G(t) e^{-i pi lam_d t} e^{-n Phi_d(tau)}.
usage: python barnes_check.py <workdir> [config] [nlist] [exact_jsonl]
"""
import sys, json, mpmath as mp
sys.path.insert(0, sys.argv[1])
from zud5 import CONFIGS, roots, f, fprime, fsecond, f0, Phi
name = sys.argv[2] if len(sys.argv) > 2 else 'q23_160'
nlist = [int(x) for x in sys.argv[3].split(',')] if len(sys.argv) > 3 else [1, 2, 3, 4, 5, 6, 7, 8, 9]
exact_file = sys.argv[4] if len(sys.argv) > 4 else None
cfg = CONFIGS[name]; r, e0, e = cfg['r'], cfg['e0'], cfg['e']
lam_d = r - 2
CL = {3: {1: mp.mpf(1) / 2}, 5: {3: mp.mpf(1) / 24, 1: mp.mpf(11) / 24}, 7: {5: mp.mpf(2) / (45 * 16), 3: mp.mpf(26) / (45 * 4) + 5 * mp.mpf(2) / (45 * 16), 1: mp.mpf(17) / 90 + 3 * mp.mpf(26) / (45 * 4) + 10 * mp.mpf(2) / (45 * 16)}}[r]
mp.mp.dps = 50
rts, _ = roots(cfg, dps=80)
ups = sorted([z for z in rts if mp.im(z) > 1e-10 and mp.re(z) > e0 - e[0]], key=lambda z: -mp.re(z))
tau_d = ups[0]
xs, ys = mp.re(tau_d), mp.im(tau_d)
print('config', name, 'tau_d =', mp.nstr(tau_d, 15), ' Re f0 =', mp.nstr(mp.re(f0(tau_d, cfg)), 15), ' Im f0/pi =', mp.nstr(mp.im(f0(tau_d, cfg)) / mp.pi, 12))
exact = {}
if exact_file:
    for line in open(exact_file):
        try:
            d = json.loads(line); exact[d['n']] = (d['log_abs_F'], d['sign'])
        except Exception:
            pass

def logG(t, n):
    h0 = e0 * n + 2; h = [ej * n + 1 for ej in e]
    v = mp.log(h0 + 2 * t) + r * mp.loggamma(h0 + t) + r * mp.loggamma(-t)
    for hj in h:
        v += mp.loggamma(hj + t) - mp.loggamma(1 + h0 - hj + t)
    return v

def logNh(n):
    h0 = e0 * n + 2; h = [ej * n + 1 for ej in e]
    return sum(mp.loggamma(h0 - 2 * hj + 1) for hj in h[r:]) - 2 * sum(mp.loggamma(hj) for hj in h[:r])

for n in nlist:
    mp.mp.dps = 40 + 2 * n if n < 60 else 160
    lN = logNh(n)
    lf0 = n * f0(tau_d, cfg)
    def integrand(y, lam):
        tau = mp.mpc(xs, y)
        t = n * (tau - e0)
        # scale out e^{n Re f0(tau_d)} to keep numbers O(1)
        return mp.exp(lN + logG(t, n) - 1j * mp.pi * lam * t - mp.re(lf0)) * 1j   # dtau = i dy, dt = n dtau
    # subdivision adapted to the peak at y* (units of tau); tails handled by quad's infinite intervals
    pts = [-mp.inf, -20, -5, -1, 0, ys / 2, ys - 1, ys, ys + 1, ys + 3, ys + 8, ys + 20, ys + 60, mp.inf]
    total = mp.mpf(0)
    parts = {}
    for lam, cl in CL.items():
        J = mp.quad(lambda y: integrand(y, lam), pts, maxdegree=8)
        J = n * J
        parts[lam] = J
        total += cl * mp.im(J) / mp.pi
    logF = mp.log(abs(total)) + mp.re(lf0)
    sgn = int(mp.sign(total))
    # asymptotic (saddle) formula with the exact prefactor at the saddle
    t_d = n * (tau_d - e0)
    Cn = mp.exp(lN + logG(t_d, n) - 1j * mp.pi * lam_d * t_d - n * Phi(tau_d, lam_d, cfg))
    asym = CL[lam_d] / mp.pi * mp.im(1j * n * Cn * mp.sqrt(2 * mp.pi / (n * fsecond(tau_d, cfg))) * mp.exp(1j * mp.im(lf0)))
    # (times e^{n Re f0}, scaled out)
    ratio = total / asym if asym != 0 else mp.nan
    sub = {lam: float(mp.log(abs(mp.im(J)) + mp.mpf(10) ** -300) / n + mp.re(f0(tau_d, cfg))) for lam, J in parts.items()}
    msg = 'n=%3d  log|F|/n = %s  sign %+d   branch rates %s   exact/asym = %s' % (
        n, mp.nstr(logF / n, 14), sgn, {k: round(v, 3) for k, v in sub.items()}, mp.nstr(ratio, 8))
    if n in exact:
        lE, sE = exact[n]
        msg += '   | exact log|F| = %.10f  contour = %s  diff = %.3e  sign exact %+d' % (lE, mp.nstr(logF, 16), float(logF - lE), sE)
    print(msg, flush=True)
