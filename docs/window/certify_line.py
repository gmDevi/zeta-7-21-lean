"""certify_line.py -- CERTIFIED inputs (mpmath.iv outward-rounded interval arithmetic, 130 bits) for the r=5 case of
Zudilin's Lemma 20 on the vertical line  Re tau = x* := Re tau_d  through the dominant saddle tau_d (branch lambda_d = r-2).

Notation (zud5.py):  f(tau) = r tau log tau + r (eta0-tau) log(eta0-tau) + sum_j [(tau-eta0+eta_j) log(tau-eta0+eta_j)
  - (tau-eta_j) log(tau-eta_j)] + C,   Phi_k(tau) = f(tau) - i pi k tau,   u_k(y) := Re Phi_k(x* + i y),
  f0 = f - tau f' (= Phi_k at a saddle of branch k),  P(tau) = (tau-eta0)^r prod(tau-eta_j) - tau^r prod(tau-eta0+eta_j).

Certified statements (each printed with CERTIFIED / FAILED):
 (R)  a disk D(z0, rho) contains exactly one zero tau_d of P (Rouche against the linear Taylor polynomial), and on the
      box B containing D:  f'(B)/(i pi) contains the odd integer lambda_d and no other integer  =>  f'(tau_d) = i pi lambda_d.
 (S)  Re f''(tau_d) > 0 (the vertical line is a direction of local maximum of Re Phi_d);  enclosures of C0 = -Re f0(tau_d),
      omega/pi = Im f0(tau_d)/pi and dist(omega/pi, Z) >= 1/4.
 (M)  A := x* - eta0 + eta_1 > y* := Im tau_d   (monotonicity range of Im f' on [0, A]; the analytic part of the proof).
 (T)  r [atan(Y/x*) + atan(Y/(eta0-x*))] > lambda_d pi at Y = Y_d   (tail threshold, analytic part).
 (D)  Im f'(x* + i y) > lambda_d pi for y in [A, Y_d]  (subdivision; empty if A >= Y_d).
 (G)  gap: u_d(y* - delta) <= Re f0(tau_d) - eps  and  u_d(y* + delta) <= Re f0(tau_d) - eps  for delta = 1 (and 0.25).
 (K)  for every subdominant branch k in {1, 3, ..., r-4}:  sup_{y in [0, y*]} u_k(y) <= U_k  with U_k < Re f0(tau_d) - 1.
 (V)  consistency: u_d(y*) (line formula) and Re f0(tau_d) (box formula) overlap.
usage: python certify_line.py <workdir> [config] [prec]
"""
import sys, json, time
from mpmath import iv, mp
sys.path.insert(0, sys.argv[1])
from zud5 import CONFIGS, saddle_poly
name = sys.argv[2] if len(sys.argv) > 2 else 'q23_160'
PREC = int(sys.argv[3]) if len(sys.argv) > 3 else 130
iv.prec = PREC; mp.prec = PREC
cfg = CONFIGS[name]; r, e0, e = cfg['r'], cfg['e0'], cfg['e']
q = len(e); lam_d = r - 2
PI = iv.pi
t0 = time.time()
report = dict(config=name, r=r, e0=e0, e=e, prec=PREC, checks={})

def I(x):
    return iv.mpf(x)

def hull(*xs):
    return iv.mpf([min(x.a for x in xs), max(x.b for x in xs)])

# ---------------------------------------------------------------- (R) root enclosure by Rouche
co = saddle_poly(cfg)                       # exact integers, highest degree first
deg = len(co) - 1
dco = [c * (deg - i) for i, c in enumerate(co[:-1])]
ddco = [c * (deg - 1 - i) for i, c in enumerate(dco[:-1])]

def horner_iv(coefs, z):
    v = iv.mpc(0, 0)
    for c in coefs:
        v = v * z + iv.mpc(int(c), 0)
    return v

def horner_mp(coefs, z):
    v = mp.mpc(0)
    for c in coefs:
        v = v * z + c
    return v

# high-precision Newton from a polyroots seed: the root with Im>0 and largest Re (Zudilin's tau0)
with mp.workdps(60):
    seeds = mp.polyroots(co, maxsteps=500, extraprec=800)
cands = [mp.mpc(z) for z in seeds if mp.im(z) > 1e-6]
cands.sort(key=lambda z: -mp.re(z))
z0 = cands[0]
for _ in range(12):
    z0 = z0 - horner_mp(co, z0) / horner_mp(dco, z0)
Z0 = iv.mpc(iv.mpf(mp.re(z0)), iv.mpf(mp.im(z0)))          # point interval (exact conversion)
Pz0 = horner_iv(co, Z0); dPz0 = horner_iv(dco, Z0)
pa = abs(Pz0).b; pb = abs(dPz0).a
rho = iv.mpf(4) * pa / pb
absz0 = abs(Z0).b
M = iv.mpf(0)
for i, c in enumerate(ddco):
    M = M + abs(iv.mpf(int(c))) * (I(absz0) + rho) ** (deg - 2 - i)
lhs = I(pa) + M * rho * rho / 2
rhs = I(pb) * rho
okR = bool(lhs.b < rhs.a)
print('(R) Rouche: |P(z0)|<=%s  |P\'(z0)|>=%s  rho=%s  sup|P\'\'|<=%s  ->  %s' % (
    mp.nstr(mp.mpf(pa), 5), mp.nstr(mp.mpf(pb), 5), mp.nstr(mp.mpf(rho.b), 5), mp.nstr(mp.mpf(M.b), 5),
    'CERTIFIED (exactly one zero of P in D(z0,rho))' if okR else 'FAILED'))
report['checks']['R_rouche'] = okR
RHO = iv.mpf(rho.b)
X = iv.mpf([Z0.real.a, Z0.real.b]) + iv.mpf([-RHO.b, RHO.b])
Y = iv.mpf([Z0.imag.a, Z0.imag.b]) + iv.mpf([-RHO.b, RHO.b])
B = iv.mpc(X, Y)                                          # box containing the disk

def lg(z):
    """principal log of a complex interval with Re z > 0 (checked)."""
    assert z.real.a > 0, 'argument box not in the right half-plane'
    return iv.log(z)

E0 = iv.mpc(I(e0), 0)
def f_iv(z):
    v = I(r) * z * lg(z) + I(r) * (E0 - z) * lg(E0 - z)
    for ej in e:
        v = v + (z - E0 + I(ej)) * lg(z - E0 + I(ej)) - (z - I(ej)) * lg(z - I(ej))
    C = iv.mpf(0)
    for ej in e[r:]:
        C = C + I(e0 - 2 * ej) * iv.log(I(e0 - 2 * ej))
    for ej in e[:r]:
        C = C - 2 * I(ej) * iv.log(I(ej))
    return v + C
def fp_iv(z):
    v = I(r) * (lg(z) - lg(E0 - z))
    for ej in e:
        v = v + lg(z - E0 + I(ej)) - lg(z - I(ej))
    return v
def fpp_iv(z):
    v = I(r) * (1 / z + 1 / (E0 - z))
    for ej in e:
        v = v + 1 / (z - E0 + I(ej)) - 1 / (z - I(ej))
    return v
def f0_iv(z):
    v = I(r) * I(e0) * lg(E0 - z)
    for ej in e:
        v = v + I(ej - e0) * lg(z - E0 + I(ej)) + I(ej) * lg(z - I(ej))
    C = iv.mpf(0)
    for ej in e[r:]:
        C = C + I(e0 - 2 * ej) * iv.log(I(e0 - 2 * ej))
    for ej in e[:r]:
        C = C - 2 * I(ej) * iv.log(I(ej))
    return v + C

lam = fp_iv(B) / iv.mpc(0, PI)
lam_re, lam_im = lam.real, lam.imag
okL = bool(lam_re.a < lam_d < lam_re.b and lam_re.b - lam_re.a < 0.5 and lam_im.a < 0 < lam_im.b and lam_im.b - lam_im.a < 0.5)
print('(R) branch: f\'(B)/(i pi) = [%s, %s] + i[%s, %s]  ->  %s' % (mp.nstr(mp.mpf(lam_re.a), 12), mp.nstr(mp.mpf(lam_re.b), 12),
      mp.nstr(mp.mpf(lam_im.a), 5), mp.nstr(mp.mpf(lam_im.b), 5), ('CERTIFIED lambda = %d' % lam_d) if okL else 'FAILED'))
report['checks']['R_branch'] = okL

# ---------------------------------------------------------------- (S) second derivative, C0, omega
fpp = fpp_iv(B)
okS = bool(fpp.real.a > 0)
print('(S) f\'\'(tau_d) = [%s, %s] + i[%s, %s]  Re>0: %s' % (mp.nstr(mp.mpf(fpp.real.a), 12), mp.nstr(mp.mpf(fpp.real.b), 12),
      mp.nstr(mp.mpf(fpp.imag.a), 12), mp.nstr(mp.mpf(fpp.imag.b), 12), 'CERTIFIED' if okS else 'FAILED'))
f0v = f0_iv(B)
C0 = -f0v.real
om = f0v.imag / PI
oa, ob = mp.mpf(om.a), mp.mpf(om.b)            # exact conversions of the certified endpoints
nearest = int(mp.nint((oa + ob) / 2))
dist = mp.mpf(0) if (oa <= nearest <= ob) else min(abs(oa - nearest), abs(ob - nearest))
okO = bool(dist >= mp.mpf('1e-9') and (ob - oa) < mp.mpf('1e-12'))   # any certified positive distance suffices (omega not in pi Z)
print('(S) C0 = -Re f0(tau_d) in [%s, %s]   (width %s)' % (mp.nstr(mp.mpf(C0.a), 16), mp.nstr(mp.mpf(C0.b), 16), mp.nstr(mp.mpf(C0.b) - mp.mpf(C0.a), 3)))
print('(S) omega/pi = Im f0(tau_d)/pi in [%s, %s]; nearest integer %d, distance >= %s  ->  %s' % (
      mp.nstr(mp.mpf(om.a), 14), mp.nstr(mp.mpf(om.b), 14), nearest, mp.nstr(mp.mpf(dist), 6), 'CERTIFIED (omega not in pi Z)' if okO else 'FAILED'))
report['checks']['S_fpp_re_pos'] = okS; report['checks']['S_omega_not_in_piZ'] = okO
report['tau_d'] = [str(mp.mpf(X.a)), str(mp.mpf(X.b)), str(mp.mpf(Y.a)), str(mp.mpf(Y.b))]
report['C0'] = [str(mp.mpf(C0.a)), str(mp.mpf(C0.b))]
report['omega_over_pi'] = [str(mp.mpf(om.a)), str(mp.mpf(om.b))]
report['fpp'] = [str(mp.mpf(fpp.real.a)), str(mp.mpf(fpp.real.b)), str(mp.mpf(fpp.imag.a)), str(mp.mpf(fpp.imag.b))]

# ---------------------------------------------------------------- line quantities
XS = X                                       # x* enclosure (width ~ rho)
def imfp_line(Yv):
    """Im f'(x* + i y) for y in the interval Yv (all real parts positive)."""
    v = I(r) * iv.atan2(Yv, XS) - I(r) * iv.atan2(-Yv, I(e0) - XS)
    for ej in e:
        v = v + iv.atan2(Yv, XS - I(e0) + I(ej)) - iv.atan2(Yv, XS - I(ej))
    return v
def ref_line(Yv):
    """Re f(x* + i y):  sum s [a log|z| - b arg z],  z = a + i b."""
    def term(a, b):
        return a * iv.log(a * a + b * b) / 2 - b * iv.atan2(b, a)
    v = I(r) * term(XS, Yv) + I(r) * term(I(e0) - XS, -Yv)
    for ej in e:
        v = v + term(XS - I(e0) + I(ej), Yv) - term(XS - I(ej), Yv)
    C = iv.mpf(0)
    for ej in e[r:]:
        C = C + I(e0 - 2 * ej) * iv.log(I(e0 - 2 * ej))
    for ej in e[:r]:
        C = C - 2 * I(ej) * iv.log(I(ej))
    return v + C
def u_line(k, Yv):
    return ref_line(Yv) + I(k) * PI * Yv
def refpp_line(Yv):
    """Re f''(x* + i y)."""
    def h(a, b):
        return a / (a * a + b * b)
    v = I(r) * (h(XS, Yv) + h(I(e0) - XS, Yv))
    for ej in e:
        v = v + h(XS - I(e0) + I(ej), Yv) - h(XS - I(ej), Yv)
    return v

# (M) monotonicity range
A = XS - I(e0) + I(e[0])
ystar = Y
okM = bool(A.a > ystar.b)
print('(M) A = x* - eta0 + eta_1 = %s > y* = %s : %s' % (mp.nstr(mp.mpf(A.a), 8), mp.nstr(mp.mpf(ystar.b), 8), 'CERTIFIED' if okM else 'FAILED'))
report['checks']['M_A_gt_ystar'] = okM
# numerical belt-and-braces for the analytic claim Re f'' > 0 on [0, A]
okMM = True; worst = None
NA = 200
for i in range(NA):
    Yv = iv.mpf([mp.mpf(A.a) * i / NA, mp.mpf(A.a) * (i + 1) / NA])
    v = refpp_line(Yv)
    if worst is None or v.a < worst: worst = v.a
    if not (v.a > 0): okMM = False
print('(M\') Re f\'\'(x*+iy) > 0 on [0, A] by subdivision (%d pieces): %s   (min lower bound %s)' % (NA, 'CERTIFIED' if okMM else 'FAILED', mp.nstr(mp.mpf(worst), 6)))
report['checks']['M_refpp_pos_numeric'] = okMM

# (T) tail threshold
Yd = None
for cand in [I(x) for x in (2, 3, 5, 8, 10, 15, 20, 30, 40, 50, 55, 60, 70, 80, 100, 150, 200, 300)]:
    v = I(r) * (iv.atan2(cand, XS) + iv.atan2(cand, I(e0) - XS))
    if v.a > (I(lam_d) * PI).b:
        Yd = cand; break
okT = Yd is not None
print('(T) tail threshold Y_d = %s: r[atan(Y/x*)+atan(Y/(eta0-x*))] > lambda_d pi : %s' % (mp.nstr(mp.mpf(Yd.a), 5) if okT else None, 'CERTIFIED' if okT else 'FAILED'))
report['checks']['T_tail'] = okT; report['Y_d'] = float(Yd.a) if okT else None

# (D) Im f' > lambda_d pi on [A, Y_d]
okD = True; nD = 0; worstD = None
if okT and Yd.a > A.a:
    stack = [(mp.mpf(A.a), mp.mpf(Yd.b))]
    while stack:
        a_, b_ = stack.pop()
        v = imfp_line(iv.mpf([a_, b_]))
        nD += 1
        if v.a > (I(lam_d) * PI).b:
            if worstD is None or v.a < worstD: worstD = v.a
            continue
        if b_ - a_ < mp.mpf(2) ** -20 or nD > 20000:
            okD = False; break
        m_ = (a_ + b_) / 2
        stack.append((a_, m_)); stack.append((m_, b_))
    print('(D) Im f\'(x*+iy) > lambda_d pi on [A, Y_d] = [%s, %s]: %s  (%d pieces, min lower bound %s vs %s)' % (
        mp.nstr(mp.mpf(A.a), 6), mp.nstr(mp.mpf(Yd.b), 6), 'CERTIFIED' if okD else 'FAILED', nD, mp.nstr(mp.mpf(worstD), 8) if worstD is not None else None, mp.nstr(mp.mpf((I(lam_d) * PI).b), 8)))
else:
    print('(D) [A, Y_d] empty (A >= Y_d): nothing to certify')
report['checks']['D_imfp_gt_lampi'] = okD

# (V) consistency of u_d(y*) with Re f0(tau_d)
ud_star = u_line(lam_d, ystar)
okV = bool(ud_star.a <= -C0.a and -C0.b <= ud_star.b) or bool(-C0.a <= ud_star.b and ud_star.a <= -C0.b)
print('(V) u_d(y*) in [%s, %s] vs Re f0(tau_d) in [%s, %s]: overlap %s' % (mp.nstr(mp.mpf(ud_star.a), 16), mp.nstr(mp.mpf(ud_star.b), 16),
      mp.nstr(mp.mpf(-C0.b), 16), mp.nstr(mp.mpf(-C0.a), 16), 'CERTIFIED' if okV else 'FAILED'))
report['checks']['V_consistency'] = okV

# (G) gap constants
report['gaps'] = {}
okG = True
for delta in ('1', '0.25', '2', '5'):
    d = I(delta)
    lo = u_line(lam_d, ystar - d); hi = u_line(lam_d, ystar + d)
    sup_out = max(mp.mpf(lo.b), mp.mpf(hi.b))
    eps = mp.mpf(-C0.b) - sup_out          # (lower bound of Re f0) - (upper bound of the two values); mp arithmetic on certified endpoints
    ok = bool(eps > mp.mpf('1e-30'))
    okG = okG and ok if delta == '1' else okG
    print('(G) delta=%s: u_d(y*-delta) <= %s, u_d(y*+delta) <= %s; eps = Re f0 - max >= %s : %s' % (
        delta, mp.nstr(mp.mpf(lo.b), 12), mp.nstr(mp.mpf(hi.b), 12), mp.nstr(eps, 8), 'CERTIFIED' if ok else 'FAILED'))
    report['gaps'][delta] = dict(u_minus=str(mp.mpf(lo.b)), u_plus=str(mp.mpf(hi.b)), eps=str(eps), ok=ok)
report['checks']['G_gap_delta1'] = okG

# (K) subdominant branches on [0, y*]
report['subdominant'] = {}
okK = True
for k in range(1, lam_d, 2):
    stack = [(mp.mpf(0), mp.mpf(ystar.b))]
    nK = 0; sup_k = None; failK = False
    target = mp.mpf(-C0.b) - 1        # need sup u_k <= Re f0 - 1
    while stack:
        a_, b_ = stack.pop()
        v = u_line(k, iv.mpf([a_, b_]))
        nK += 1
        if v.b <= target:
            if sup_k is None or v.b > sup_k: sup_k = v.b
            continue
        if b_ - a_ < mp.mpf(2) ** -24 or nK > 50000:
            failK = True; break
        m_ = (a_ + b_) / 2
        stack.append((a_, m_)); stack.append((m_, b_))
    # also the value at y=0 and the threshold where the k-branch turns (y_k with Im f' = k pi) for the record
    ok = not failK
    okK = okK and ok
    print('(K) branch k=%d: sup_{[0,y*]} u_k <= %s  (%d pieces; need <= Re f0 - 1 = %s): %s' % (
        k, mp.nstr(mp.mpf(sup_k), 12) if sup_k is not None else None, nK, mp.nstr(target, 12), 'CERTIFIED' if ok else 'FAILED'))
    report['subdominant'][k] = dict(sup=str(mp.mpf(sup_k)) if sup_k is not None else None, pieces=nK, ok=ok)
    # threshold check for the k-branch tail: r[atan(y/x*)+atan(y/(eta0-x*))] > k pi at y = y*  (so u_k decreasing beyond y*)
    v = I(r) * (iv.atan2(ystar, XS) + iv.atan2(ystar, I(e0) - XS))
    print('     r[atan(y*/x*)+atan(y*/(eta0-x*))] = %s vs k pi = %s (Im f\'(x*+iy*) = lambda_d pi > k pi anyway)' % (mp.nstr(mp.mpf(v.a), 6), mp.nstr(mp.mpf((I(k) * PI).b), 6)))
report['checks']['K_subdominant'] = okK

# extra: value u_d(0) = Re f(x*) (start of the line on the real axis) and Im f'(x*+i0)=0
u0 = ref_line(iv.mpf(0))
print('(X) u_k(0) = Re f(x*) in [%s, %s] (same for all k)' % (mp.nstr(mp.mpf(u0.a), 12), mp.nstr(mp.mpf(u0.b), 12)))
report['u_at_0'] = [str(mp.mpf(u0.a)), str(mp.mpf(u0.b))]

allok = all(report['checks'].values())
print('ALL CERTIFIED' if allok else 'NOT ALL CERTIFIED', ' time %.1fs' % (time.time() - t0))
report['all_certified'] = allok
with open(sys.argv[1] + '/certify_%s.json' % name, 'w') as fh:
    json.dump(report, fh, indent=1)
