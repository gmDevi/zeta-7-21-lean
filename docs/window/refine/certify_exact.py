"""certify_exact.py -- CERTIFIED, exact-rational mirror of certify_iv.py (no floating point anywhere).

Every elementary value is enclosed by rational bounds obtained from series with explicit remainders, exactly the
kind of certificate the pair Lean project uses (Landscape/Numerics.lean):
  log 2   = 2 artanh(1/3),  artanh(z) = sum z^{2i+1}/(2i+1),  0 <= tail <= |z|^{2N+1} / ((2N+1)(1 - z^2));
  log q   = k log 2 + 2 artanh((m-1)/(m+1)),  q = 2^k m,  m in [2/3, 4/3];
  atan w  = sum (-1)^i w^{2i+1}/(2i+1) for |w| <= 3/7 (alternating, |tail| <= |w|^{2N+1}/(2N+1));
            atan u = pi/4 + atan((u-1)/(u+1)) for 2/5 < u <= 1;  atan u = pi/2 - atan(1/u) for u > 1;  odd;
  pi      = 16 atan(1/5) - 4 atan(1/239) (Machin).
All interval arithmetic is exact on Fractions; endpoints of elementary values are rounded outward to 10^-40.
The script re-derives C0', (D), (T), (B), (K) of certify_iv.py and writes the list of every elementary enclosure used
(certificate_exact.json): these are the only numerical facts a formalisation has to re-prove.
usage: python certify_exact.py <workdir> [x0] [p] [Y]
"""
import sys, json, math, time
from fractions import Fraction as Fr

W = sys.argv[1]
X0 = Fr(sys.argv[2]) if len(sys.argv) > 2 else Fr(3984, 25)
P = Fr(sys.argv[3]) if len(sys.argv) > 3 else Fr(26208, 3125)
Y = Fr(sys.argv[4]) if len(sys.argv) > 4 else Fr(60)
E0 = 160
ETA = [47, 47, 47, 47, 48, 50, 50, 51, 52, 53, 54, 55, 56, 57, 58, 59, 60, 61, 62, 63, 64, 65, 66]
R = 5
DEN = 10 ** 40
t0 = time.time()
LEDGER = {}      # (func, arg) -> (lo, hi)


def rd(x):
    return Fr(math.floor(x * DEN), DEN)


def ru(x):
    return Fr(-math.floor(-x * DEN), DEN)


class Iv:
    __slots__ = ('lo', 'hi')

    def __init__(self, lo, hi=None):
        self.lo = Fr(lo); self.hi = Fr(lo if hi is None else hi)
        assert self.lo <= self.hi

    def __add__(s, o):
        o = o if isinstance(o, Iv) else Iv(o)
        return Iv(s.lo + o.lo, s.hi + o.hi)
    __radd__ = __add__

    def __neg__(s):
        return Iv(-s.hi, -s.lo)

    def __sub__(s, o):
        o = o if isinstance(o, Iv) else Iv(o)
        return Iv(s.lo - o.hi, s.hi - o.lo)

    def __rsub__(s, o):
        return Iv(o) - s

    def __mul__(s, o):
        o = o if isinstance(o, Iv) else Iv(o)
        ps = [s.lo * o.lo, s.lo * o.hi, s.hi * o.lo, s.hi * o.hi]
        return Iv(min(ps), max(ps))
    __rmul__ = __mul__

    def inv(s):
        assert s.lo > 0 or s.hi < 0
        return Iv(1 / s.hi, 1 / s.lo)

    def __truediv__(s, o):
        o = o if isinstance(o, Iv) else Iv(o)
        return s * o.inv()

    def outward(s):
        return Iv(rd(s.lo), ru(s.hi))

    def __repr__(s):
        return '[%.15g, %.15g]' % (float(s.lo), float(s.hi))


def artanh_series(z, N):
    """enclosure of artanh(z), |z| < 1 rational"""
    az = abs(z)
    S = Fr(0); zp = z; z2 = z * z
    for i in range(N):
        S += zp / (2 * i + 1); zp *= z2
    tail = az ** (2 * N + 1) / ((2 * N + 1) * (1 - z2))
    return Iv(S - tail, S + tail) if z != 0 else Iv(0)


LOG2 = (artanh_series(Fr(1, 3), 50) * 2).outward()


def log_q(q):
    q = Fr(q); assert q > 0
    key = ('log', str(q))
    if key in LEDGER:
        return LEDGER[key]
    k = q.numerator.bit_length() - q.denominator.bit_length()
    m = q / Fr(2) ** k
    while m > Fr(4, 3):
        m /= 2; k += 1
    while m < Fr(2, 3):
        m *= 2; k -= 1
    z = (m - 1) / (m + 1)                 # |z| <= 1/5
    v = (LOG2 * k + artanh_series(z, 40) * 2).outward()
    LEDGER[key] = v
    return v


def atan_small(w, N=70):
    """alternating series, |w| <= 3/7"""
    assert abs(w) <= Fr(3, 7)
    S = Fr(0); wp = w; w2 = w * w
    for i in range(N):
        S += (-1) ** i * wp / (2 * i + 1); wp *= w2
    tail = abs(w) ** (2 * N + 1) / (2 * N + 1)
    return Iv(S - tail, S + tail)


PI = (atan_small(Fr(1, 5), 60) * 16 - atan_small(Fr(1, 239), 30) * 4).outward()


def atan_q(u):
    u = Fr(u)
    key = ('atan', str(u))
    if key in LEDGER:
        return LEDGER[key]
    if u < 0:
        v = -atan_q(-u)
    elif u > 1:
        v = PI * Fr(1, 2) - atan_q(1 / u)
    elif u > Fr(2, 5):
        v = PI * Fr(1, 4) + atan_small((u - 1) / (u + 1))
    else:
        v = atan_small(u)
    v = v.outward()
    LEDGER[key] = v
    return v


def log_iv(x):
    return Iv(log_q(x.lo).lo, log_q(x.hi).hi)


rep = dict(x0=str(X0), p=str(P), Y=str(Y), checks={})
c0 = E0 - X0
A_ = X0 - E0 + ETA[0]
a = [X0 - E0 + e for e in ETA]
b = [X0 - e for e in ETA]
assert 0 < c0 < A_ and all(0 < aj < bj for aj, bj in zip(a, b))
assert all(abs(e - 160) <= 160 for e in ETA)


def Gf(aa, y):
    """(a/2) log(a^2+y^2) + y atan(a/y) - a,  y > 0 rational"""
    return log_q(aa * aa + y * y) * (aa / 2) + atan_q(aa / y) * y - aa


def C_eta():
    v = Iv(0)
    for e in ETA[R:]:
        v = v + log_q(E0 - 2 * e) * (E0 - 2 * e)
    for e in ETA[:R]:
        v = v - log_q(e) * (2 * e)
    return v


Ce = C_eta()
Up = Ce - 336 + (Gf(X0, P) - Gf(X0 - E0, P)) * R - PI * (2 * P)
for aj, bj in zip(a, b):
    Up = Up - (Gf(bj, P) - Gf(aj, P))
dUp = (atan_q(X0 / P) + atan_q(c0 / P)) * R - PI * 2
for aj, bj in zip(a, b):
    dUp = dUp - (atan_q(bj / P) - atan_q(aj / P))
spread = max(P, A_ - P)
absd = max(abs(dUp.lo), abs(dUp.hi))
sup_bound = Up.hi + absd * spread
C0p = -sup_bound
print('(V) U(x0,p) in %s   U\'(x0,p) in [%.10g, %.10g]' % (Up, float(dUp.lo), float(dUp.hi)))
print('(V) sup_{[0,A]} U <= %.16f  =>  C0\' >= %.16f   (exact rational, %d digits in the denominator)' % (
    float(sup_bound), float(C0p), len(str(C0p.denominator))))
rep['C0prime_lower'] = str(C0p); rep['C0prime_float'] = float(C0p)
STAGES = [('V: U(p), dU(p), C_eta', len(LEDGER))]
for tgt in [Fr(7481, 10), Fr(7506, 10), Fr(750618, 1000), Fr(7507116, 10000)]:
    print('    C0\' >= %s : %s' % (float(tgt), C0p >= tgt))
rep['checks']['C0prime_gt_748.1'] = C0p > Fr(7481, 10)      # the Lean target C0lo = 748.1

# (D) one cell [A, Y] (and bisect if needed)
def cell_sup(l, r):
    v = (atan_q(X0 / l) + atan_q(c0 / l)) * R - PI * 2
    for aj, bj in zip(a, b):
        v = v + atan_q(aj / l) - atan_q(bj / r)
    return v.hi

cells = []; stack = [(A_, Y)]; okD = True
while stack:
    l, r = stack.pop()
    sp = cell_sup(l, r)
    if sp < 0:
        cells.append((l, r, sp)); continue
    if r - l < Fr(1, 64):
        okD = False; break
    m = (l + r) / 2
    stack += [(m, r), (l, m)]
print('(D) U\' < 0 on [A, Y]: %s, cells %s' % (okD, [(str(l), str(r), '%.6g' % float(sp)) for l, r, sp in sorted(cells)]))
rep['checks']['D'] = okD
STAGES.append(('D', len(LEDGER)))
rep['D_cells'] = [[str(l), str(r), str(sp)] for l, r, sp in sorted(cells)]

# (T)
kap = (atan_q(Y / X0) + atan_q(Y / c0)) * R - PI * 3
thr = Fr(22) / (162 + 2 * Y)
okT = kap.lo > thr
print('(T) kappa in %s > 22/(162+2Y) = %.8g : %s' % (kap, float(thr), okT))
rep['checks']['T'] = okT; rep['kappa_lo'] = str(kap.lo)
STAGES.append(('T', len(LEDGER)))

# (B)
xl = X0 - Fr(1, 2); xh = X0 + Fr(1, 2)
B1 = log_q(xh / (E0 - xh)) * R
B2 = Iv(0)
for e in ETA:
    B2 = B2 + log_q((xl - e) / (xl - E0 + e))
Bv = max(B1.hi, B2.hi)
okB = E0 - xh > 0 and xl - E0 + ETA[0] > 0
print('(B) B = max(%.10g, %.10g) : %s' % (float(B1.hi), float(B2.hi), okB))
rep['checks']['B'] = okB; rep['B'] = str(Bv)
STAGES.append(('B', len(LEDGER)))

# (K)
K1 = Iv(0)
for e in ETA[R:]:
    K1 = K1 + log_q(E0 - 2 * e) * Fr(1, 2)
for e in ETA[:R]:
    K1 = K1 - log_q(e)
logpi = log_iv(PI)
K2 = K1 + Fr(18, 12 * 28) + (log_q(8) + logpi * 5 - log_q(3)) + (LOG2 + 1) * 5
tailfac = (kap - thr).inv() + Y
logK = (LOG2 + logpi) * 4 - logpi + K2 + Bv / 2 + log_q(162 + 2 * Y) * 11 + log_iv(tailfac)
print('(K) C_eta in %s  K1 in %s  K2 in %s  log K <= %.10f' % (Ce, K1, K2, float(logK.hi)))
rep['C_eta'] = [str(Ce.lo), str(Ce.hi)]; rep['logK_hi'] = str(logK.hi)
STAGES.append(('K', len(LEDGER)))

# n0 for several targets:  logK + 16 log n <= (C0' - target) n, checked with log n <= rational upper bounds
def n0_for(target):
    gap = C0p - Fr(target)
    n = max(1, int(16 / gap) + 1)
    while True:
        if logK.hi + 16 * log_q(n).hi <= gap * n:
            return n
        n += 1

for target in ['7481/10', '7482/10', '7470513057897/10000000000', '740', '1463/2']:
    n0 = n0_for(target)
    print('    |F_n| <= exp(-%s n) for every n >= %d' % (float(Fr(target)), n0))
    rep['n0_' + target] = n0

STAGES.append(('n0 (log n values, optional)', len(LEDGER)))
prev = 0
for nm, c in STAGES:
    print('    new elementary enclosures in stage %-26s %d' % (nm + ':', c - prev)); prev = c
rep['stages'] = STAGES
rep['elementary_enclosures'] = [[k[0], k[1], str(v.lo), str(v.hi)] for k, v in LEDGER.items()]
rep['pi'] = [str(PI.lo), str(PI.hi)]; rep['log2'] = [str(LOG2.lo), str(LOG2.hi)]
print('elementary enclosures used: %d (%d log, %d atan) + pi + log 2' % (
    len(LEDGER), sum(1 for k in LEDGER if k[0] == 'log'), sum(1 for k in LEDGER if k[0] == 'atan')))
allok = all(rep['checks'].values())
rep['all_certified'] = allok
print('ALL CERTIFIED (exact rational)' if allok else 'NOT ALL CERTIFIED', ' time %.1fs' % (time.time() - t0))
with open(W + '/certificate_exact_x%s_p%s_Y%s.json' % (str(X0).replace('/', '_'), str(P).replace('/', '_'), str(Y)), 'w') as fh:
    json.dump(rep, fh, indent=1)
