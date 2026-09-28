"""Exact (rational) check of Lemma C(b) and Lemma E (5.1) at small n: G_k(0) from its product definition,
v_ell(G_k(0)) = 1 on K, and G_{k-1}(0)/G_k(0) == rho(k) exactly; plus the reduction of rho mod ell to rho|_{n=c/63}.
usage: python check_ratio_exact.py "n:c,n:c,..." """
import sys, math
from fractions import Fraction as Fr
eta = [47] * 4 + [48, 50, 50] + list(range(51, 67)); r = 5


def G0(n, k):
    h0 = 160 * n + 2; h = [x * n + 1 for x in eta]
    num = 1
    for l in range(1, h0):
        if l != k: num *= (l - k) ** r
    den = 1
    for hj in h:
        for l in range(hj, h0 - hj + 1):
            if l != k: den *= (l - k)
    Nh = Fr(1)
    for hj in sorted(h)[r:]: Nh *= math.factorial(h0 - 2 * hj)
    for hj in sorted(h)[:r]: Nh /= math.factorial(hj - 1) ** 2
    return Nh * (h0 - 2 * k) * Fr(num, den)


def rho(n, k):
    h0 = 160 * n + 2; h = [x * n + 1 for x in eta]
    v = Fr(h0 - 2 * k + 2, h0 - 2 * k) * Fr(h0 - k, 1 - k) ** r
    for hj in h: v *= Fr(hj - k, h0 - hj + 1 - k)
    return v


def vl(x, l):
    v = 0; a, b = x.numerator, x.denominator
    while a % l == 0: a //= l; v += 1
    while b % l == 0: b //= l; v -= 1
    return v


for pair in sys.argv[1].split(','):
    n, c = map(int, pair.split(':')); l = 63 * n - c
    ks = 110 * n + 1
    Gs = {ks - d: G0(n, ks - d) for d in range(c + 1)}
    vs = [vl(Gs[k], l) for k in Gs]
    exact = all(Gs[ks - d - 1] / Gs[ks - d] == rho(n, ks - d) for d in range(c))
    red = []
    for d in range(c):
        x = rho(n, ks - d); y = rho(Fr(c, 63), Fr(ks - d).__class__(110 * Fr(c, 63) + 1 - d))
        red.append((x.numerator * y.denominator - y.numerator * x.denominator) % l == 0)
    print(f'n={n} c={c} ell={l}: v_ell(G_k(0)) on K = {vs}; ratio identity (5.1) exact: {exact}; reduction mod ell: {red}')
