# Auditor-2 (window): helpers for the Barnes representation (own derivation):
#   F~_n = (N_h/2pi) int_R G(M+iy) V5(cos pi(M+iy)) dy,  M = n(x* - eta0) in (-h1, 0),
#   G(t) = (h0+2t) Gamma(h0+t)^5 Gamma(-t)^5 prod_j Gamma(h_j+t)/Gamma(1+h0-h_j+t),  V5(y) = (y^3+2y)/3.
# check_V5: sin^5(z) (1/4!) cot''''(z) = V5(cos z);  leading(): the limit formula (F) of proof.md 3.6.
# Leading term: F~_n ~ (1/(24 pi)) n^{-25/2} Im( i A(tau3) sqrt(2pi/f''(tau3)) e^{n f0(tau3)} ).
import sys, time
import mpmath as mp
r, q, e0 = 5, 23, 160
eta = [47, 47, 47, 47, 48, 50, 50] + [j + 43 for j in range(8, 24)]

def V5(y):
    return (y ** 3 + 2 * y) / 3

def check_V5():
    mp.mp.dps = 40
    for z in (mp.mpc('0.37', '0.21'), mp.mpc('-1.3', '2.2'), mp.mpf('0.77')):
        lhs = mp.sin(z) ** 5 * mp.diff(mp.cot, z, 4) / 24
        print("V5 identity at", mp.nstr(z, 5), ": |sin^5 cot''''/24 - V5(cos)| =", mp.nstr(abs(lhs - V5(mp.cos(z))), 3))

def leading(n, t3, f2, f0v):
    A = ((2 * mp.pi) ** 9 * (2 * t3 - e0) * t3 ** mp.mpf(7.5) * (e0 - t3) ** mp.mpf(-2.5)
         * mp.fprod((t3 - e0 + e) ** mp.mpf(0.5) * (t3 - e) ** mp.mpf(-1.5) for e in eta)
         * mp.fprod(mp.sqrt(e0 - 2 * e) for e in eta[r:]) / mp.fprod(eta[:r]))
    B = 1j * A * mp.sqrt(2 * mp.pi / f2)
    return mp.im(B * mp.exp(n * f0v)) * mp.mpf(n) ** mp.mpf(-12.5) / (24 * mp.pi), B

if __name__ == "__main__":
    check_V5()
    mp.mp.dps = 50
    t3 = mp.mpc('159.356418053794830583663509361', '8.39371237206876207347965336941')
    f2 = mp.mpc('0.27212245899863666045', '0.54298742193168633591')
    f0v = mp.mpc('-750.711694833944313681960496431', '-1465.90909590539762207106350328')
    lead, B = leading(1, t3, f2, f0v)
    print("|B| =", mp.nstr(abs(B), 12), " beta = arg B - pi/2 =", mp.nstr(mp.arg(B) - mp.pi / 2, 12))
