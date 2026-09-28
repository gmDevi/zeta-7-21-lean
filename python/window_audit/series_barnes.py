# (1) Lean's Fn literally: sum_{t>=0} [eps^{r-1}] Rser(t), high precision, vs the exact linear form.
# (2) Barnes integral (N_h/2 pi i) int_{M+iR} G(t) V_r(cos pi t) dt vs exact F_n.
# (3) Stirling check of N_h G e^{-i pi lam t} = n^-13 A(tau) e^{n Phi_lam(tau)} (1+O(1/n)).
# (4) leading term of proof.md (F) vs Barnes values at larger n.
import sys, time
import mpmath as mp
import sympy as sp
from fractions import Fraction as Fr
from math import factorial
from exact_indep import config, run

# --- V_r check with sympy: sin^r(z) * ((-1)^(r-1)/(r-1)!) cot^(r-1)(z) = V_r(cos z)
z = sp.symbols('z')
for r_, V in ((3, lambda c: c), (5, lambda c: (c**3 + 2*c)/3)):
    expr = sp.sin(z)**r_ * (-1)**(r_-1) / sp.factorial(r_-1) * sp.diff(sp.cot(z), z, r_-1) - V(sp.cos(z))
    print("V_%d identity residual:" % r_, sp.simplify(sp.expand_trig(sp.simplify(expr))))

def Vr(r, c):
    return c if r == 3 else (c**3 + 2*c)/3

def lean_series(name, n, T, dps):
    r, q, e0, eta = config(name)
    mp.mp.dps = dps
    h0 = e0 * n + 2; h = [e * n + 1 for e in eta]
    # Rser: numerator prod_{i=1}^{h0-1} (y+i+eps)^r ; denominator prod_j prod_{i=h_j}^{h0-h_j} (y+i+eps)
    ex = {i: r - sum(1 for hj in h if hj <= i <= h0 - hj) for i in range(1, h0)}
    Nh = Fr(1)
    for j in range(r, q): Nh *= factorial(h0 - 2 * h[j])
    for j in range(r): Nh /= factorial(h[j] - 1) ** 2
    Nh = mp.mpf(Nh.numerator) / Nh.denominator
    idx = [i for i in ex if ex[i] != 0]
    S = mp.mpf(0); tmax = mp.mpf(0); last = None
    for t in range(T + 1):
        lg = mp.log(Nh) + mp.log(h0 + 2 * t) + mp.fsum(ex[i] * mp.log(t + i) for i in idx)
        Rt = mp.exp(lg)
        # series of log: log(1+2eps/(h0+2t)) + sum_i e_i log(1+eps/(t+i))
        l = [mp.mpf(0)] * r
        for m in range(1, r):
            sm = mp.fsum(ex[i] / mp.mpf(t + i) ** m for i in idx) + (mp.mpf(2) / (h0 + 2 * t)) ** m
            l[m] = (-1) ** (m + 1) * sm / m
        E = [mp.mpf(1)] + [mp.mpf(0)] * (r - 1)
        for m in range(1, r):
            E[m] = mp.fsum(kk * l[kk] * E[m - kk] for kk in range(1, m + 1)) / m
        term = Rt * E[r - 1]
        S += term; tmax = max(tmax, abs(term)); last = term
    return S, tmax, last

def barnes(name, n, dps=40, M=None):
    r, q, e0, eta = config(name)
    mp.mp.dps = dps
    h0 = e0 * n + 2; h = [e * n + 1 for e in eta]
    logNh = mp.fsum(mp.loggamma(h0 - 2 * h[j] + 1) for j in range(r, q)) - 2 * mp.fsum(mp.loggamma(h[j]) for j in range(r))
    if M is None: M = mp.mpf(-0.6435819462051694) * n
    def integrand(y):
        t = mp.mpc(M, y)
        lg = mp.log(h0 + 2 * t) + r * mp.loggamma(h0 + t) + r * mp.loggamma(-t) + \
             mp.fsum(mp.loggamma(hj + t) - mp.loggamma(1 + h0 - hj + t) for hj in h)
        return mp.exp(lg + logNh) * Vr(r, mp.cos(mp.pi * t))
    lo, hi = -12 * n - 30, 40 * n + 60
    step = mp.mpf(0.5)
    pts = [-mp.inf] + [lo + i * step for i in range(int((hi - lo) / step) + 1)] + [mp.inf]
    I = mp.quad(integrand, pts)
    return I / (2 * mp.pi)

if __name__ == "__main__":
    which = sys.argv[1]
    if which == "series":
        name, n, T, dps = sys.argv[2], int(sys.argv[3]), int(sys.argv[4]), int(sys.argv[5])
        t0 = time.time()
        ex = run(name, n, zeta_check=True)
        Fex = ex["F"]
        S, tmax, last = lean_series(name, n, T, dps)
        mp.mp.dps = dps
        print(f"[series {name} n={n}] T={T}: sum = {mp.nstr(S, 25)}  max|term| = {mp.nstr(tmax, 5)}  last term = {mp.nstr(last, 5)}")
        print(f"   relative difference to the exact linear form: {mp.nstr(abs(S - Fex) / abs(Fex), 5)}   ({time.time()-t0:.0f}s)")
    elif which == "barnes":
        name = sys.argv[2]
        for n in map(int, sys.argv[3].split(",")):
            t0 = time.time()
            ex = run(name, n, zeta_check=True)
            B = barnes(name, n)
            mp.mp.dps = 40
            print(f"[barnes {name} n={n}] contour = {mp.nstr(mp.re(B), 20)} (Im {mp.nstr(mp.im(B), 3)}), exact = {mp.nstr(ex['F'], 20)}, rel.diff = {mp.nstr(abs(mp.re(B) - ex['F']) / abs(ex['F']), 5)}  ({time.time()-t0:.0f}s)")
