"""Leading constant of the auxiliary-prime argument (exact rational arithmetic).

Configuration: Zudilin JTNB 16 (2004) (8.13): h0 = eta0*n + 2, h_j = eta_j*n + 1, eta sorted increasingly.
m1 = h0 - h1 - h_{r+1} = M*n with M = eta0 - eta_1 - eta_{r+1}.  Auxiliary prime ell = M*n - c (c >= 1 small).
K = [h1 + ell, h0 - h_{r+1}] = {k* - d : 0 <= d <= c},  k* = h0 - h_{r+1}.

On K (for n > n_c):  pole order o = mu_{r+1} (multiplicity of eta_{r+1} among eta_{r+1..q}),
ell-adic excess e = r - mu_1 (mu_1 = multiplicity of eta_1), and
   c0 == -beta * ell^{e-o-r+1} * sum_{k in K} u_k    (mod ell^{e-o-r+2} Z_(ell)),
   beta = sum_{t=0}^{min(e,o-1)} (-1)^{e-t} binom(e,t) w_{o-t},  w_i = (-1)^{r-1} binom(i+r-2, r-1),
u_k = G_k(0)/(-ell)^e (an ell-unit).  u_{k-1}/u_k = G_{k-1}(0)/G_k(0) is the telescoping ratio
   rho(k) = [(h0-2k+2)/(h0-2k)] * [(h0-k)/(1-k)]^r * prod_j [(h_j-k)/(h0-h_j+1-k)],
a rational function of n; modulo ell (M n == c) it equals rho evaluated at n = c/M.  Hence
   sum_K u_k == u_{k*} * Q_c (mod ell),   Q_c := sum_{d=0}^{c} prod_{d'<d} rho(k*-d')|_{n=c/M}.
This script prints beta, Q_c, the factorisations, and the finitely many exceptional primes ell = M n - c
(ell | numerator of beta*Q_c or of a reduced factor).
usage: python aux_constants.py <outdir> r eta0 "e1,...,eq" cmax
"""
import sys, json
from fractions import Fraction as Fr
from math import comb
from sympy import factorint as _fi, isprime


def factorint(x):
    """partial factorisation: trial division + rho with limits; a large cofactor is kept and flagged"""
    f = _fi(x, limit=10**6)
    out = {}
    for p, v in f.items():
        if p > 10**12 and not isprime(p):
            g = _fi(p, use_trial=False, use_rho=True, use_pm1=True, use_ecm=True, limit=None) if p < 10**40 else {p: 1}
            for pp, vv in g.items(): out[pp] = out.get(pp, 0) + vv * v
        else:
            out[p] = out.get(p, 0) + v
    return out


def config(r, e0, e):
    e = sorted(e); q = len(e)
    M = e0 - e[0] - e[r]
    mu1 = e.count(e[0]); mur1 = sum(1 for x in e[r:] if x == e[r])
    return e, q, M, mu1, mur1


def beta_const(r, e_, o):
    w = lambda i: (-1) ** (r - 1) * comb(i + r - 2, r - 1)
    return sum((-1) ** (e_ - t) * comb(e_, t) * w(o - t) for t in range(0, min(e_, o - 1) + 1))


def rho_factors(r, e0, e, n, k):
    """list of (num, den) factors of G_{k-1}(0)/G_k(0) as exact rationals in n (n may be a Fraction)"""
    h0 = e0 * n + 2; h = [x * n + 1 for x in e]
    F = [((h0 - 2 * k + 2), (h0 - 2 * k))]
    F += [((h0 - k), (1 - k))] * r
    F += [((hj - k), (h0 - hj + 1 - k)) for hj in h]
    return F


def Qc(r, e0, e, c):
    e, q, M, mu1, mur1 = config(r, e0, e)
    n = Fr(c, M)
    h0 = e0 * n + 2; hr1 = e[r] * n + 1
    kstar = h0 - hr1
    Q = Fr(1); pi = Fr(1); zero_factor = False; facts = []
    for d in range(c):
        k = kstar - d
        prod = Fr(1)
        for a, b in rho_factors(r, e0, e, n, k):
            if a == 0 or b == 0: zero_factor = True
            facts.append((a, b))
            prod *= Fr(a) / Fr(b) if b != 0 else Fr(0)
        pi *= prod
        Q += pi
    return Q, facts, zero_factor, M


def main():
    outdir = sys.argv[1]; r = int(sys.argv[2]); e0 = int(sys.argv[3]); e = [int(x) for x in sys.argv[4].split(',')]
    cmax = int(sys.argv[5])
    e, q, M, mu1, mur1 = config(r, e0, e)
    ee = r - mu1; o = mur1
    beta = beta_const(r, ee, o)
    print(flush=True); print(f'config r={r} q={q} eta0={e0} eta={e}')
    print(f'M = eta0-eta1-eta_(r+1) = {M};  mu1 = {mu1} -> e = r-mu1 = {ee};  mu_(r+1) = {mur1} -> o = {o};'
          f'  leading exponent e-o-r+1 = {ee - o - r + 1};  beta = {beta}')
    out = dict(r=r, q=q, eta0=e0, eta=e, M=M, e=ee, o=o, beta=beta, lead_exp=ee - o - r + 1, cases=[])
    for c in range(1, cmax + 1):
        from math import gcd
        if gcd(c, M) != 1:
            continue
        Q, facts, zf, _ = Qc(r, e0, e, c)
        num = abs(Q.numerator) * abs(beta); den = Q.denominator
        # primes that could spoil: numerator of beta*Q_c, and numerators/denominators of every reduced factor
        bad = set(factorint(num).keys()) if num else set()
        for a, b in facts:
            for x in (Fr(a), Fr(b)):
                for y in (x.numerator, x.denominator):
                    if y != 0: bad |= set(factorint(abs(y)).keys())
        bad_l = sorted(p for p in bad if p % M == (-c) % M and p > M)   # candidate ell = M n - c
        rec = dict(c=c, Q=str(Q), Q_float=float(Q), zero_factor=zf, beta_Q_num_factors={str(p): v for p, v in factorint(num).items()} if num else None,
                   exceptional_ell=bad_l, parity_note=f'ell odd needs n != c mod 2')
        out['cases'].append(rec)
        sys.stdout.flush()
        print(f'c={c:2d}: Q_c = {Q}  (~{float(Q):.6g}); zero factor: {zf}; beta*Q_c numerator = {num} = {factorint(num) if num else 0}')
        print(f'       exceptional ell = {M}n-{c} (prime, dividing a relevant numerator/denominator): {bad_l}')
    with open(f'{outdir}/aux_constants.json', 'w') as f: json.dump(out, f, indent=1)


if __name__ == '__main__':
    main()
