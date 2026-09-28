"""final_check_v2.py -- assembler / final-referee checks for proof_v2.md (window {zeta(7),...,zeta(21)}).
(proof_v2.md is docs/proof.md of this repository.)

Usage:  python final_check_v2.py <workdir>
  <workdir> = the research-session folder of the first proof; the refine tracks are read from the sibling folder
  ../window-21-refine/<track>/.  In this repository the files it reads are in docs/window/refine/, and two of them
  (the crude-upper-bound certificates for the sharp line and for p = 9) are not included, so it does not run
  unchanged; its output is final_check_v2.log.

What it does (all exact rational arithmetic; no floating point enters any inequality):
 (1) Margin arithmetic.  Reads the EXACT rational lower bounds C0' from the crude-upper-bound certificates and the
     interval enclosure of C2 and C2' = C2 - 18 from refined-lemma19/margins.json, and prints certified lower bounds
     for C0' - C2' (route R1) and C0' - C2 (route R2), plus C0 - C2' (route R3) from window-21-proof/certify_q23_160.json.
 (2) Q_1 recomputed from the telescoping formula (5.1) of aux-prime-nonvanishing at n = 1/63 (independent code);
     primality of its numerator (deterministic below 2^64) and residue mod 63.
 (3) Cross-track consistency at the auxiliary prime l = 63n - 1 (n even, l prime, n <= NMAX):
     the refined exponent e_l^REF = min(e^L19, e^PP, e^BPP) of refined-lemma19 Theorem 1 must be >= -v_l(c0) = 5
     (Theorem N); also checks the hypotheses used in Theorem N (l > m0 = 60n, K = {110n, 110n+1}, o_k = 2, V_k = 1).
     V_k = v_l(N_h G0(k)) is computed from the definition by counting l-divisible factors (l - k = m*l, |m| small).
"""
import sys, os, json, re
from fractions import Fraction as Fr

W = sys.argv[1] if len(sys.argv) > 1 else '.'
REF = os.path.join(os.path.dirname(os.path.abspath(W)), 'window-21-refine')
NMAX = int(sys.argv[2]) if len(sys.argv) > 2 else 400

def dec(x, digits=25):
    """exact Fraction -> decimal string truncated toward -inf (for lower bounds) with `digits` decimals"""
    s = -1 if x < 0 else 1
    a = abs(x)
    ip = a.numerator // a.denominator
    fp = a - ip
    d = (fp * 10**digits)
    di = d.numerator // d.denominator
    if s < 0 and d != di:
        di += 1  # truncation toward -inf for negatives
    return ('-' if s < 0 else '') + str(ip) + '.' + str(di).zfill(digits)

def parse_iv(s):
    # "[a, b]" -> (Fraction(a), Fraction(b))
    a, b = s.strip('[] ').split(',')
    return Fr(a.strip()), Fr(b.strip())

out = []
def P(*a):
    line = ' '.join(str(x) for x in a)
    print(line); out.append(line)

# ---------------------------------------------------------------- (1) margins
P('=== (1) certified margin arithmetic (exact rationals)')
cert = {}
for tag, fn in [('simple', 'certificate_exact_x159_p181_20_Y60.json'),
                ('sharp', 'certificate_exact_x3984_25_p26208_3125_Y60.json'),
                ('p9', 'certificate_exact_x159_p9_Y60.json')]:
    d = json.load(open(os.path.join(REF, 'crude-upper-bound', fn)))
    assert d['all_certified'] is True, fn
    cert[tag] = Fr(d['C0prime_lower'])
    P('C0prime_lower[%s] = %s  (exact rational from %s; float display in the log was %.16f)' % (
        tag, dec(cert[tag], 22), fn, d['C0prime_float']))

m = json.load(open(os.path.join(REF, 'refined-lemma19', 'margins.json')))['q23_160']
assert m['G'] == '18'
C2lo = parse_iv(m['C2'][0])[0]; C2hi = parse_iv(m['C2'][1])[1]
C2plo = parse_iv(m['C2prime'][0])[0]; C2phi = parse_iv(m['C2prime'][1])[1]
C0lo = parse_iv(m['C0'][0])[0]; C0hi = parse_iv(m['C0'][1])[1]
assert C2plo == C2lo - 18 and C2phi == C2hi - 18
P('C2  in [%s, %s]' % (dec(C2lo, 27), dec(C2hi, 27)))
P("C2' in [%s, %s]   (C2' = C2 - G, G = 18 exactly)" % (dec(C2plo, 27), dec(C2phi, 27)))
P('C0  in [%s, %s]   (window-21-proof certify_q23_160, used only by routes R3/R4)' % (dec(C0lo, 25), dec(C0hi, 25)))
for tag in ('simple', 'sharp', 'p9'):
    P("route R1 (%-6s): C0' - C2' >= %s" % (tag, dec(cert[tag] - C2phi, 20)))
for tag in ('simple', 'sharp'):
    P("route R2 (%-6s): C0' - C2  >= %s" % (tag, dec(cert[tag] - C2hi, 20)))
P("route R3         : C0  - C2' >= %s" % dec(C0lo - C2phi, 20))
P("route R4         : C0  - C2  >= %s" % dec(C0lo - C2hi, 20))
assert all(cert[t] - C2phi > 21 for t in cert) and all(cert[t] - C2hi > 3 for t in ('simple', 'sharp'))

# ---------------------------------------------------------------- configuration
r, q, e0 = 5, 23, 160
eta = [47, 47, 47, 47, 48, 50, 50] + list(range(51, 67))
assert len(eta) == q and sum(eta) == 1272

# ---------------------------------------------------------------- (2) Q_1
P('')
P('=== (2) Q_1 from the telescoping ratio (5.1) at n = 1/63 (independent code)')
def rho(n, k):
    h0 = e0 * n + 2
    hj = [ej * n + 1 for ej in eta]
    v = Fr(h0 - 2 * k + 2) / (h0 - 2 * k) * (Fr(h0 - k) / (1 - k)) ** 5
    for h in hj:
        v *= Fr(h - k) / (h0 - h + 1 - k)
    return v
n_ = Fr(1, 63)
kstar = 110 * n_ + 1
Q1 = 1 + rho(n_, kstar)
P('Q_1 =', Q1, ' (claimed 984698059590803/1545332660300000):', Q1 == Fr(984698059590803, 1545332660300000))
def is_prime_det(N):
    # deterministic Miller-Rabin for N < 3.3e24 (bases = first 13 primes)
    if N < 2: return False
    small = [2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37, 41]
    for p in small:
        if N % p == 0: return N == p
    d, s = N - 1, 0
    while d % 2 == 0: d //= 2; s += 1
    for a in small:
        x = pow(a, d, N)
        if x in (1, N - 1): continue
        for _ in range(s - 1):
            x = x * x % N
            if x == N - 1: break
        else:
            return False
    return True
num = abs(Q1.numerator)
P('num(Q_1) = %d prime: %s  residue mod 63: %d  (bad residue would be 62)' % (num, is_prime_det(num), num % 63))
den = Q1.denominator
fac = {}; x = den; p = 2
while p * p <= x:
    while x % p == 0: fac[p] = fac.get(p, 0) + 1; x //= p
    p += 1
if x > 1: fac[x] = fac.get(x, 0) + 1
P('den(Q_1) =', den, '=', fac, ' (all primes < 251 = smallest aux prime)')
assert Q1 == Fr(984698059590803, 1545332660300000) and is_prime_det(num) and num % 63 == 47 and max(fac) < 251

# ---------------------------------------------------------------- (3) cross-track consistency at l = 63n-1
P('')
P('=== (3) refined exponent at the auxiliary prime l = 63n-1 vs Theorem N (-v_l(c0) = 5), n even, l prime, n <= %d' % NMAX)
def vp(N, p):
    N = abs(N); c = 0
    assert N != 0
    while N % p == 0: N //= p; c += 1
    return c
def vfact(N, p):
    c = 0; t = p
    while t <= N: c += N // t; t *= p
    return c
mrat = [63, 63, 62, 61] + [60] * 14   # m_j / n of Lemma 19 (window-21-proof section 2)
count = 0; bad = 0; summary = {}
for n in range(2, NMAX + 1, 2):
    l = 63 * n - 1
    if not is_prime_det(l):
        continue
    h0 = e0 * n + 2
    h = [ej * n + 1 for ej in eta]
    Kset = range(h[r], h0 - h[r] + 1)      # K = [h_{r+1}, h0 - h_{r+1}]
    assert l * l > h0 and l > 60 * n
    nu = sum(vfact(h0 - 2 * h[j], l) for j in range(r, q)) - 2 * sum(vfact(h[j] - 1, l) for j in range(r))
    # Lemma 19 exponent at l (Phi_n only involves primes <= m_{q-r} n = 60n < l)
    eL19 = r * (l <= mrat[0] * n) + sum(1 for mj in mrat[1:] if l <= mj * n)
    ePP = 0; eBPP = 0; farinfo = []
    for k in Kset:
        o = sum(1 for j in range(r, q) if h[j] <= k <= h0 - h[j]) - (2 * k == h0)
        assert o >= 1
        # V_k = v_l(N_h G0(k)): count l-divisible factors l' - k = m*l (m != 0) in numerator/denominator
        V = nu + (vp(h0 - 2 * k, l) if 2 * k != h0 else 0)
        mm = 1
        while True:
            hit = False
            for sgn in (1, -1):
                lp = k + sgn * mm * l
                if 1 <= lp <= h0 - 1:
                    hit = True; V += r * (1 + vp(mm, l))
                for j in range(q):
                    if h[j] <= lp <= h0 - h[j]:
                        hit = True; V -= (1 + vp(mm, l))
            if not hit and k + mm * l > h0 and k - mm * l < 1:
                break
            mm += 1
        far = (k - h[0] >= l)
        flat = not any((kk != k) and ((kk - k) % l == 0) for kk in (k - l, k + l) if h[r] <= kk <= h0 - h[r])
        Lk = o + r - 1 if far else o - 1
        ePP = max(ePP, Lk - V)
        if flat:
            Ek = (o + r - 1 - max(V, nu)) if far else min(o - 1 - V, -nu)
        else:
            Ek = Lk - V
        eBPP = max(eBPP, Ek)
        if far:
            farinfo.append((k, o, V))
    eREF = min(eL19, ePP, eBPP)
    ok = (eREF >= 5) and sorted(farinfo) == [(110 * n, 2, 1), (110 * n + 1, 2, 1)]
    count += 1; bad += (not ok)
    key = (eL19, ePP, eBPP, eREF)
    summary[key] = summary.get(key, 0) + 1
    if n <= 30 or not ok:
        P('n=%4d l=%6d  e_L19=%d e_PP=%d e_BPP=%d e_REF=%d  far poles (k,o_k,V_k)=%s  nu=%d  %s' % (
            n, l, eL19, ePP, eBPP, eREF, farinfo, nu, 'OK' if ok else 'FAIL'))
P('checked %d auxiliary primes; failures: %d; (e_L19, e_PP, e_BPP, e_REF) pattern counts: %s' % (count, bad, summary))
assert bad == 0
P('')
P('ALL FINAL CHECKS PASSED')
open(os.path.join(W, 'final_check_v2.log'), 'w', encoding='utf-8').write('\n'.join(out) + '\n')
