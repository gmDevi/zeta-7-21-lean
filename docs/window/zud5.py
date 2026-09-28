"""Shared definitions for the r=5 Lemma-20 analysis of Zudilin's JTNB 2004 Sect. 8 forms.
Config Q23 (eta0=160): F~_n = N_h/(r-1)! sum_{t>=0} R^{(r-1)}(t) in Q + Q zeta(7) + ... + Q zeta(21).
Barnes form (Prop. A in proof.md):
  F~ = (N_h/(2 pi i)) * (-1)^{r+1} * int_{M-i inf}^{M+i inf} (h0+2t) Gamma(h0+t)^r Gamma(-t)^r
         prod_j Gamma(hj+t)/Gamma(1+h0-hj+t) * V_r(cos pi t) dt,   -h0 < M < -(h0-h1)  [or -h1 < M < 0],
  V_5(y) = (y^3 + 2y)/3,  V_5(cos pi t) = (cos 3 pi t + 11 cos pi t)/12.
Stirling phase in tau = -t/n (upper half-plane, principal logs; cut plane C minus ((-inf, eta0-eta1] u [eta0, inf))):
  f(tau) = r tau log tau + r (eta0-tau) log(eta0-tau) + sum_j [(tau-eta0+etaj) log(tau-eta0+etaj) - (tau-etaj) log(tau-etaj)] + Cn
  Phi_k(tau) = f(tau) - i pi k tau  (branch k in {+-1, +-3});  saddle: f'(tau) = i pi k  <=>  P(tau) = 0,
  P(tau) = (tau-eta0)^r prod(tau-etaj) - tau^r prod(tau-eta0+etaj);  f0 = f - tau f' (Zudilin's f0).
"""
import mpmath as mp

CONFIGS = {
    'q23_160': dict(r=5, e0=160, e=[47, 47, 47, 47, 48, 50, 50, 51, 52, 53, 54, 55, 56, 57, 58, 59, 60, 61, 62, 63, 64, 65, 66]),
    'q23_320': dict(r=5, e0=320, e=[94, 94, 94, 95, 96, 100, 100, 102, 104, 106, 108, 110, 112, 114, 116, 118, 120, 122, 124, 126, 128, 130, 132]),
    'q23_536': dict(r=5, e0=536, e=[148, 148, 149, 153, 157, 166, 166, 168, 172, 176, 180, 182, 184, 188, 192, 196, 200, 204, 208, 212, 216, 220, 224]),
    'thm3': dict(r=3, e0=91, e=[27, 27, 27] + [25 + j for j in range(4, 14)]),
}

def polymul(a, b):
    out = [0] * (len(a) + len(b) - 1)
    for i, x in enumerate(a):
        if x:
            for j, y in enumerate(b):
                out[i + j] += x * y
    return out

def saddle_poly(cfg):
    """exact integer coefficients (highest first) of P(tau) = (tau-e0)^r prod(tau-ej) - tau^r prod(tau-e0+ej)"""
    r, e0, e = cfg['r'], cfg['e0'], cfg['e']
    P1 = [1]; P2 = [1]
    for _ in range(r):
        P1 = polymul(P1, [1, -e0]); P2 = polymul(P2, [1, 0])
    for ej in e:
        P1 = polymul(P1, [1, -ej]); P2 = polymul(P2, [1, -e0 + ej])
    P = [a - b for a, b in zip(P1, P2)]
    while P and P[0] == 0:
        P = P[1:]
    return P

def polyval(co, z):
    v = mp.mpc(0)
    for c in co:
        v = v * z + c
    return v

def polyder(co):
    d = len(co) - 1
    return [c * (d - i) for i, c in enumerate(co[:-1])]

def Cnorm(cfg):
    r, e0, e = cfg['r'], cfg['e0'], cfg['e']
    return sum((e0 - 2 * ej) * mp.log(e0 - 2 * ej) for ej in e[r:]) - 2 * sum(ej * mp.log(ej) for ej in e[:r])

def f(tau, cfg):
    r, e0, e = cfg['r'], cfg['e0'], cfg['e']
    tau = mp.mpc(tau)
    v = r * tau * mp.log(tau) + r * (e0 - tau) * mp.log(e0 - tau)
    for ej in e:
        v += (tau - e0 + ej) * mp.log(tau - e0 + ej) - (tau - ej) * mp.log(tau - ej)
    return v + Cnorm(cfg)

def fprime(tau, cfg):
    r, e0, e = cfg['r'], cfg['e0'], cfg['e']
    tau = mp.mpc(tau)
    v = r * (mp.log(tau) - mp.log(e0 - tau))
    for ej in e:
        v += mp.log(tau - e0 + ej) - mp.log(tau - ej)
    return v

def fsecond(tau, cfg):
    r, e0, e = cfg['r'], cfg['e0'], cfg['e']
    tau = mp.mpc(tau)
    v = r * (1 / tau + 1 / (e0 - tau))
    for ej in e:
        v += 1 / (tau - e0 + ej) - 1 / (tau - ej)
    return v

def f0(tau, cfg):
    r, e0, e = cfg['r'], cfg['e0'], cfg['e']
    tau = mp.mpc(tau)
    v = r * e0 * mp.log(e0 - tau)
    for ej in e:
        v += (ej - e0) * mp.log(tau - e0 + ej) + ej * mp.log(tau - ej)
    return v + Cnorm(cfg)

def Phi(tau, k, cfg):
    return f(tau, cfg) - 1j * mp.pi * k * mp.mpc(tau)

def Phiprime(tau, k, cfg):
    return fprime(tau, cfg) - 1j * mp.pi * k

def roots(cfg, dps=60):
    co = saddle_poly(cfg)
    with mp.workdps(dps):
        rts = mp.polyroots(co, maxsteps=500, extraprec=6 * dps)
        dco = polyder(co)
        out = []
        for z in rts:
            z = mp.mpc(z)
            for _ in range(6):   # Newton polish
                z = z - polyval(co, z) / polyval(dco, z)
            out.append(z)
    return out, co
