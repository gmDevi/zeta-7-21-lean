"""Independent re-implementation (verifier) of Zudilin 2004 Sect. 8 ledger (Prop. 5), general odd r.
phi(x) = min_y phi0(x,y) computed EXACTLY on every interval of constancy (integer arithmetic),
integral int_{1/M}^oo phi(x) dx/x^2 computed exactly per piece (1/x differences + trigamma tail).
C0 from all saddle points (all roots with Im>0 listed with Re f0 and Im f0/pi).
"""
import math, sys, json
from fractions import Fraction as Fr
import numpy as np, mpmath as mp

def terms_z04(e0, e, r):
    T = []  # (a, b, c): c*floor(a x + b y)
    for j, ej in enumerate(e):
        if j < r:
            T += [(0, 1, 1), (e0, -1, 1), (-ej, 1, -1), (e0 - ej, -1, -1), (ej, 0, -2)]
        else:
            T += [(e0 - 2 * ej, 0, 1), (-ej, 1, -1), (e0 - ej, -1, -1)]
    return T

def compress(T):
    d = {}
    for a, b, c in T:
        d[(a, b)] = d.get((a, b), 0) + c
    return [(a, b, c) for (a, b), c in d.items() if c != 0]

def xbreaks(T):
    """all x in [0,1] where phi can change: a x in Z for all a, and (a1 -/+ a2) x in Z for y-terms."""
    A0 = set(abs(a) for a, b, c in T)
    Y = [(a, b) for a, b, c in T if b != 0]
    for a1, b1 in Y:
        for a2, b2 in Y:
            # critical y: b=+1 -> y = -a x ; b=-1 -> y = a x  ; i.e. y = -b a x
            A0.add(abs(b1 * a1 - b2 * a2))
    A0.discard(0)
    pts = set([Fr(0), Fr(1)])
    for d in A0:
        for k in range(1, d):
            pts.add(Fr(k, d))
    return sorted(pts)

def phi_at(T, x):
    """exact min over y of sum c floor(a x + b y), x rational (Fraction) in (0,1)."""
    P, Q = x.numerator, x.denominator
    a = np.array([t[0] for t in T], dtype=np.int64); b = np.array([t[1] for t in T], dtype=np.int64)
    c = np.array([t[2] for t in T], dtype=np.int64)
    Qs = 2 * Q
    # critical y*Qs values
    crit = set()
    for ai, bi, ci in T:
        if bi != 0:
            crit.add((2 * ((-bi * ai * P) % Q)))
    crit = sorted(crit)
    cand = list(crit)
    for i in range(len(crit)):
        lo = crit[i]; hi = crit[i + 1] if i + 1 < len(crit) else crit[0] + Qs
        cand.append(((lo + hi) // 2) % Qs)
    Yv = np.array(cand, dtype=np.int64)[:, None]
    num = 2 * a[None, :] * P + b[None, :] * Yv
    vals = (np.floor_divide(num, Qs) * c[None, :]).sum(axis=1)
    return int(vals.min())

def phi_integral(T, M):
    mp.mp.dps = 30
    T = compress(T)
    bp = xbreaks(T)
    tot = mp.mpf(0)
    lo_cut = Fr(1, M)
    pieces = []
    for i in range(len(bp) - 1):
        x0, x1 = bp[i], bp[i + 1]
        v = phi_at(T, (x0 + x1) / 2)
        pieces.append((x0, x1, v))
    # int_1^oo phi/x^2 = int_0^1 phi(x) psi'(1+x) dx = sum v (psi(1+x1) - psi(1+x0))
    tail = mp.mpf(0); low = mp.mpf(0)
    for x0, x1, v in pieces:
        if v == 0: continue
        tail += v * (mp.digamma(1 + mp.mpf(x1.numerator) / x1.denominator) - mp.digamma(1 + mp.mpf(x0.numerator) / x0.denominator))
        a0 = max(x0, lo_cut)
        if a0 < x1:
            low += v * (Fr(1) / a0 - Fr(1) / x1)
    return float(tail + low), pieces

def f0(tau, e0, e, r):
    tau = mp.mpc(tau)
    v = r * e0 * mp.log(e0 - tau)
    for ej in e:
        v += ej * mp.log(tau - ej) - (e0 - ej) * mp.log(tau - e0 + ej)
    for ej in e[:r]:
        v -= 2 * ej * mp.log(ej)
    for ej in e[r:]:
        v += (e0 - 2 * ej) * mp.log(e0 - 2 * ej)
    return v

def saddles(e0, e, r, dps=80):
    mp.mp.dps = dps
    t = mp.mpf(1)
    import sympy as sp
    x = sp.Symbol('x')
    P = sp.expand((x - e0) ** r * sp.prod([x - ej for ej in e]) - x ** r * sp.prod([x - e0 + ej for ej in e]))
    co = [int(cf) for cf in sp.Poly(P, x).all_coeffs()]
    rts = mp.polyroots(co, maxsteps=500, extraprec=400)
    out = []
    for z in rts:
        if mp.im(z) > 1e-20:
            fv = f0(z, e0, e, r)
            out.append(dict(tau=complex(z), Ref0=float(mp.re(fv)), Imf0_over_pi=float(mp.im(fv) / mp.pi)))
    out.sort(key=lambda d: -d['tau'].real)
    return out, len(co) - 1

def mlist(e0, e, r):
    q = len(e)
    return [max(e[r - 1], e0 - 2 * e[r], e0 - e[0] - e[r + j]) for j in range(q - r)]

def ledger(e0, e, r):
    q = len(e)
    S, deg = saddles(e0, e, r)
    C0 = -S[0]['Ref0']
    m = mlist(e0, e, r)
    I, _ = phi_integral(terms_z04(e0, e, r), m[-1])
    C2 = r * m[0] + sum(m[1:]) - I
    return dict(e0=e0, e=e, r=r, q=q, deg=deg, sum_e=sum(e), degree_bound=e0 * (q - r) / 2,
                C0=C0, C2=C2, margin=C0 - C2, m=m, phi_int=I, saddles=[dict(tau=[s['tau'].real, s['tau'].imag], Ref0=s['Ref0'], Imf0_over_pi=s['Imf0_over_pi']) for s in S])

if __name__ == '__main__':
    cases = {
        'thm3': (91, [27, 27, 27] + [25 + j for j in range(4, 14)], 3),
        'b21': (160, [47, 47, 47, 47, 48, 50, 50, 51, 52, 53, 54, 55, 56, 57, 58, 59, 60, 61, 62, 63, 64, 65, 66], 5),
        'b13': (105, [30, 30, 30, 30, 30, 33, 34, 35, 36, 37, 38, 39, 40, 41, 42], 5),
    }
    which = sys.argv[1:] or list(cases)
    for k in which:
        e0, e, r = cases[k]
        res = ledger(e0, e, r)
        print(k, json.dumps(res, default=str), flush=True)
