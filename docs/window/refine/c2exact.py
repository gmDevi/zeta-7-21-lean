"""c2exact.py -- EXACT continuum constants C2 (Zudilin's Lemma 19) and C2' (refined), certified tails.

Continuum exponent functions of x = n/p (u = 1/x = p/n), evaluated on OPEN y-cells (proof.md Sect. 4):
  phi0(x,y)  Zudilin's 1-periodic function;  phi(x) = min_y phi0(x,y)
  Psi_L19(x) = Dcount(1/x) - [1/x <= m_{q-r}] max(phi(x),0),   Dcount(u) = r[u<=m1] + sum_{j>=2}[u<=m_j]
  on y in the pole range (eta_{r+1} x, (eta0-eta_{r+1}) x):
     far  = [y > 1 + eta1 x],   flat = [y-1 < eta_{r+1} x  and  y+1 > (eta0-eta_{r+1}) x],
     o    = #{j>r : eta_j x < y < (eta0-eta_j) x},   nuN(x) = sum_{j>r} floor((eta0-2eta_j)x) - 2 sum_{j<=r} floor(eta_j x)
     E_PP  = q-1 - r[not far] - phi0
     E_BPP = flat ? (far ? min(q-1-phi0, o+r-1-nuN) : min(q-r-1-phi0, -nuN)) : E_PP
  Psi_X(x) = max(0, max over cells of E_X),   Psi_REF = min(Psi_L19, Psi_PP, Psi_BPP).
  C2  = int_0^oo Psi_L19(1/u) du = r m1 + m2 + ... + m_{q-r} - int_{1/m_{q-r}}^oo phi(x) dx/x^2
  C2' = int_0^oo Psi_REF(1/u) du = C2 - G,  G = int (Psi_L19 - Psi_REF)(x) dx/x^2 (exact rational, finite x-range)
Every x-breakpoint is a/d with d a difference of y-slopes (or eta_j, eta0-2eta_j): all candidates are enumerated,
the functions are evaluated exactly (integer arithmetic) at interval midpoints, and constancy is re-checked at two
random rational interior points of every interval.
Tail int_1^oo phi(x)dx/x^2 = sum_pieces v [psi(1+x1)-psi(1+x0)] in mpmath.iv (outward rounding):
  psi(1+x) = psi(K+1+x) - sum_{k=1}^K 1/(k+x),  psi(z) = ln z - 1/(2z) - sum_{k=1}^N B_2k/(2k z^2k) + theta*|B_{2N+2}|/((2N+2) z^{2N+2}),
  |theta| <= 1 (enveloping property for real z>0, from DLMF 5.9.16).
usage: python c2exact.py <outdir> <tag> r eta0 "e1,...,eq"  [--no-tail]
"""
import sys, json, math, random, time
from fractions import Fraction as Fr
import numpy as np


def compress(T):
    d = {}
    for a, b, c in T:
        d[(a, b)] = d.get((a, b), 0) + c
    return [(a, b, c) for (a, b), c in sorted(d.items()) if c != 0]


class Cont:
    def __init__(self, r, e0, e):
        e = sorted(int(x) for x in e)
        self.r, self.e0, self.e, self.q = r, e0, e, len(e)
        q = self.q
        T = []
        for j, ej in enumerate(e):
            if j < r:
                T += [(0, 1, 1), (e0, -1, 1), (-ej, 1, -1), (e0 - ej, -1, -1), (ej, 0, -2)]
            else:
                T += [(e0 - 2 * ej, 0, 1), (-ej, 1, -1), (e0 - ej, -1, -1)]
        self.T = compress(T)
        self.Ty = [(a, b, c) for a, b, c in self.T if b != 0]
        self.Tx = [(a, b, c) for a, b, c in self.T if b == 0]
        self.Ty_a = np.array([t[0] for t in self.Ty], dtype=np.int64)
        self.Ty_b = np.array([t[1] for t in self.Ty], dtype=np.int64)
        self.Ty_c = np.array([t[2] for t in self.Ty], dtype=np.int64)
        # periodic y-slopes: floor(a x + b y) jumps at y = -b a x + b m
        self.per_slopes = sorted(set(-b * a for a, b, c in self.Ty))
        m0 = max(e[r - 1], e0 - 2 * e[r])
        self.m = [max(m0, e0 - e[0] - e[r + j]) for j in range(q - r)]
        er1 = e[r]
        # non-periodic lines (slope, offset)
        self.np_lines = [(er1, 0), (e0 - er1, 0), (e[0], 1), (er1, 1), (e0 - er1, -1)]
        self.np_lines += [(ej, 0) for ej in e[r:]] + [(e0 - ej, 0) for ej in e[r:]]
        allsl = set(self.per_slopes) | set(s for s, _ in self.np_lines)
        D = set(abs(s1 - s2) for s1 in allsl for s2 in allsl)
        D |= set(e[:r]) | set(e0 - 2 * ej for ej in e[r:]) | set(self.m)
        D.discard(0)
        self.D = sorted(D)
        Dphi = set(abs(s1 - s2) for s1 in self.per_slopes for s2 in self.per_slopes)
        Dphi |= set(e[:r]) | set(e0 - 2 * ej for ej in e[r:])
        Dphi.discard(0)
        self.Dphi = sorted(Dphi)

    # ------------------------------------------------------------ exact evaluation at x = a/b (ints)
    def _floor_terms_y(self, a, b, Y2):
        """sum over y-terms of c*floor(alpha x + beta y) at x = a/b, y = Y2/(2b); Y2: python-int list -> ints"""
        Yv = np.array(Y2, dtype=np.int64)[:, None]
        assert abs(int(Yv.max(initial=0))) < 2 ** 40 and a < 2 ** 40 and b < 2 ** 40
        num = 2 * self.Ty_a[None, :] * a + self.Ty_b[None, :] * Yv
        return [int(v) for v in (np.floor_divide(num, 2 * b) * self.Ty_c[None, :]).sum(axis=1)]

    def phi0x_part(self, a, b):
        return sum(c * ((al * a) // b) for al, be, c in self.Tx)

    def ycells(self, a, b, Ylo2, Yhi2, lines_np=()):
        """midpoints (in units 1/(2b)) of the open cells of (Ylo2, Yhi2) cut by all periodic lines and lines_np."""
        pts = set([Ylo2, Yhi2])
        for c in self.per_slopes:
            # Y2 = 2(c a + m b) in [Ylo2, Yhi2]
            mlo = -((2 * c * a - Ylo2) // (2 * b)) - 1
            mhi = (Yhi2 - 2 * c * a) // (2 * b) + 1
            for mm in range(mlo, mhi + 1):
                Y = 2 * (c * a + mm * b)
                if Ylo2 < Y < Yhi2:
                    pts.add(Y)
        for c, off in lines_np:
            Y = 2 * (c * a + off * b)
            if Ylo2 < Y < Yhi2:
                pts.add(Y)
        pts = sorted(pts)
        return [(pts[i] + pts[i + 1]) // 2 for i in range(len(pts) - 1)], pts
        # (pts are even, so midpoints are exact integers)

    def phi(self, a, b):
        """phi(x) = min over open cells of one period [0,1) of phi0(x, .)  (x = a/b)."""
        mids, _ = self.ycells(a, b, 0, 2 * b)
        vals = self._floor_terms_y(a, b, mids)
        return self.phi0x_part(a, b) + min(vals)

    def dcount(self, u):
        r, m = self.r, self.m
        return r * (u <= m[0]) + sum(1 for mj in m[1:] if u <= mj)

    def psi_all(self, a, b):
        """(Psi_L19, Psi_PP, Psi_BPP) at x = a/b (exact)."""
        r, q, e0, e = self.r, self.q, self.e0, self.e
        x = Fr(a, b); u = 1 / x
        ph = self.phi(a, b)
        L19 = self.dcount(u) - (max(ph, 0) if u <= self.m[-1] else 0)
        er1 = e[r]
        Ylo2, Yhi2 = 2 * er1 * a, 2 * (e0 - er1) * a
        mids, _ = self.ycells(a, b, Ylo2, Yhi2, self.np_lines)
        fy = self._floor_terms_y(a, b, mids)
        px = self.phi0x_part(a, b)
        nuN = sum(((e0 - 2 * ej) * a) // b for ej in e[r:]) - 2 * sum((ej * a) // b for ej in e[:r])
        PP = 0; BPP = 0
        for Y, fv in zip(mids, fy):
            ph0 = px + fv
            far = Y > 2 * b + 2 * a * e[0]
            flat = (Y - 2 * b < 2 * a * er1) and (Y + 2 * b > 2 * a * (e0 - er1))
            o = sum(1 for ej in e[r:] if 2 * a * ej < Y < 2 * a * (e0 - ej))
            Epp = q - 1 - (0 if far else r) - ph0
            if flat:
                Eb = min(q - 1 - ph0, o + r - 1 - nuN) if far else min(q - r - 1 - ph0, -nuN)
            else:
                Eb = Epp
            PP = max(PP, Epp); BPP = max(BPP, Eb)
        return L19, PP, BPP

    # ------------------------------------------------------------ piece enumeration
    def xbreaks(self, xlo, xhi, D):
        pts = set([xlo, xhi])
        for d in D:
            alo = math.floor(xlo * d); ahi = math.ceil(xhi * d)
            for a in range(alo, ahi + 1):
                f = Fr(a, d)
                if xlo < f < xhi:
                    pts.add(f)
        return sorted(pts)

    def phi_pieces(self, check=True, seed=1):
        rnd = random.Random(seed)
        bp = self.xbreaks(Fr(0), Fr(1), self.Dphi)
        pieces = []
        for x0, x1 in zip(bp[:-1], bp[1:]):
            xm = (x0 + x1) / 2
            v = self.phi(xm.numerator, xm.denominator)
            if check:
                for _ in range(2):
                    t = Fr(rnd.randint(1, 999), 1000); xt = x0 + (x1 - x0) * t
                    assert self.phi(xt.numerator, xt.denominator) == v, ('phi not constant', x0, x1)
            if pieces and pieces[-1][2] == v:
                pieces[-1] = (pieces[-1][0], x1, v)
            else:
                pieces.append((x0, x1, v))
        return pieces

    def ref_pieces(self, xlo, xhi, check=True, seed=2):
        rnd = random.Random(seed)
        bp = self.xbreaks(xlo, xhi, self.D)
        out = []
        for x0, x1 in zip(bp[:-1], bp[1:]):
            xm = (x0 + x1) / 2
            v = self.psi_all(xm.numerator, xm.denominator)
            if check:
                for _ in range(2):
                    t = Fr(rnd.randint(1, 999), 1000); xt = x0 + (x1 - x0) * t
                    assert self.psi_all(xt.numerator, xt.denominator) == v, ('Psi not constant', x0, x1)
            out.append((x0, x1) + tuple(v))
        return out


def digamma_diff_iv(pieces, K=40, N=16, prec=200):
    """certified enclosure of sum_pieces v [psi(1+x1) - psi(1+x0)] (pieces with Fraction endpoints)."""
    from mpmath import iv, mp
    iv.prec = prec; mp.prec = prec
    import sympy
    Bq = [sympy.bernoulli(2 * k) for k in range(0, N + 2)]          # exact rationals
    Biv = [iv.mpf(int(b.p)) / int(b.q) for b in Bq]
    cache = {}

    def psi1(x):              # psi(1+x), x Fraction in [0,1]
        if x in cache:
            return cache[x]
        X = iv.mpf(x.numerator) / x.denominator
        s = iv.mpf(0)
        for k in range(1, K + 1):
            s = s + 1 / (iv.mpf(k) + X)
        z = iv.mpf(K + 1) + X
        ps = iv.log(z) - 1 / (2 * z)
        zz = z * z; zp = zz
        for k in range(1, N + 1):
            ps = ps - Biv[k] / (2 * k * zp)
            zp = zp * zz
        rem = abs(Biv[N + 1]) / ((2 * N + 2) * zp)
        ps = ps + iv.mpf([-rem.b, rem.b])
        val = ps - s
        cache[x] = val
        return val

    tot = iv.mpf(0)
    for x0, x1, v in pieces:
        if v == 0:
            continue
        tot = tot + v * (psi1(x1) - psi1(x0))
    return tot


def compute(r, e0, e, tail=True, check=True, verbose=True):
    t0 = time.time()
    C = Cont(r, e0, e)
    m = C.m; M = m[-1]
    res = dict(r=r, e0=e0, e=C.e, m=m)
    # ---- phi pieces on [0,1)
    pieces = C.phi_pieces(check=check)
    res['phi_pieces'] = len(pieces); res['phi_min'] = min(v for _, _, v in pieces)
    assert res['phi_min'] >= 0, 'phi < 0 somewhere (max(phi,0) handling needed)'
    # rational part: int_{1/M}^{1} phi dx/x^2 (M >= 1)
    lo = Fr(1, M)
    rat = Fr(0)
    for x0, x1, v in pieces:
        a0 = max(x0, lo)
        if a0 < x1 and v:
            rat += v * (1 / a0 - 1 / x1)
    Dsum = r * m[0] + sum(m[1:])
    res['Dsum'] = Dsum
    res['phi_int_rational_part'] = str(rat)
    if tail:
        from mpmath import iv, mp
        dg = digamma_diff_iv(pieces)
        C2 = iv.mpf(Dsum) - (iv.mpf(rat.numerator) / rat.denominator) - dg
        res['phi_int_tail'] = [mp.nstr(mp.mpf(dg.a), 30), mp.nstr(mp.mpf(dg.b), 30)]
        res['C2'] = [mp.nstr(mp.mpf(C2.a), 30), mp.nstr(mp.mpf(C2.b), 30)]
    # ---- refined part: x in [1/m1, x_hi], x_hi = 2/(min(eta0-eta_{r+1}-eta1, eta0-2eta_{r+1})) (below: Psi_REF = Psi_L19)
    er1 = C.e[r]
    wlo = min(e0 - er1 - C.e[0], e0 - 2 * er1)
    xlo = Fr(1, m[0]); xhi = Fr(2, wlo)
    rp = C.ref_pieces(xlo, xhi, check=check)
    G = Fr(0); Gpp = Fr(0); Gbpp = Fr(0); worse = 0
    bands = {}
    for x0, x1, L19, PP, BPP in rp:
        REF = min(L19, PP, BPP)
        w = 1 / x0 - 1 / x1                       # = length in u
        G += (L19 - REF) * w; Gpp += (L19 - min(L19, PP)) * w; Gbpp += (L19 - min(L19, BPP)) * w
        if BPP > L19:
            worse += 1
        ub = int(1 / x1)
        bands[ub] = bands.get(ub, Fr(0)) + (L19 - REF) * w
    res['ref_x_range'] = [str(xlo), str(xhi)]; res['ref_pieces'] = len(rp)
    res['G'] = str(G); res['G_float'] = float(G)
    res['G_PP_only'] = float(Gpp); res['G_BPP_only'] = float(Gbpp); res['BPP_worse_than_L19_pieces'] = worse
    res['G_by_u_band'] = {k: round(float(v), 6) for k, v in sorted(bands.items()) if v}
    # sanity: at the upper end of the x-range (u = wlo/2) the three agree
    if tail:
        C2p = C2 - (iv.mpf(G.numerator) / G.denominator)
        res['C2prime'] = [mp.nstr(mp.mpf(C2p.a), 30), mp.nstr(mp.mpf(C2p.b), 30)]
    res['time'] = round(time.time() - t0, 1)
    return res, pieces, rp


if __name__ == '__main__':
    outdir, tag = sys.argv[1], sys.argv[2]
    r = int(sys.argv[3]); e0 = int(sys.argv[4]); e = [int(x) for x in sys.argv[5].split(',')]
    tail = '--no-tail' not in sys.argv
    res, pieces, rp = compute(r, e0, e, tail=tail)
    print(json.dumps(res, indent=1))
    with open(f'{outdir}/c2exact_{tag}.json', 'w') as fh:
        json.dump(res, fh, indent=1)
    with open(f'{outdir}/c2exact_{tag}_refpieces.txt', 'w') as fh:
        fh.write('# x0 x1 (u1=1/x1 .. u0=1/x0)  Psi_L19 Psi_PP Psi_BPP  (exact rationals)\n')
        for x0, x1, a, b, c in rp:
            fh.write(f'{x0} {x1}  u=[{float(1/x1):.6f},{float(1/x0):.6f}]  {a} {b} {c}\n')
