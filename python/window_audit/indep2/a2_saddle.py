# Auditor-2 (window): independent saddle-point constants for cfgW (r=5, q=23, eta0=160).
# Derivation (own): with t = n(tau - eta0), Stirling on N_h G(t) e^{-i pi lam t} gives exp(n Phi_lam(tau)),
#   Phi_lam = f(tau) - i pi lam tau,
#   f(tau) = 5 tau log tau + 5 (e0-tau) log(e0-tau) + sum_j [(tau-e0+e_j) log(tau-e0+e_j) - (tau-e_j) log(tau-e_j)] + C_eta,
#   C_eta  = sum_{j>5} (e0-2e_j) log(e0-2e_j) - 2 sum_{j<=5} e_j log e_j.
# Saddle: f'(tau) = i pi lam, f' = 5 log tau - 5 log(e0-tau) + sum_j log((tau-e0+e_j)/(tau-e_j)).
# exp(f') = -1  <=>  P(tau) = (tau-e0)^5 prod (tau-e_j) - tau^5 prod (tau-e0+e_j) = 0.
# Value at a saddle: Phi_lam(tau_lam) = f - tau f' = f0(tau) (Zudilin's f0).
import mpmath as mp
mp.mp.dps = 60
r, q, e0 = 5, 23, 160
eta = [47, 47, 47, 47, 48, 50, 50] + [j + 43 for j in range(8, 24)]
assert len(eta) == q
Ceta = sum((e0 - 2 * e) * mp.log(e0 - 2 * e) for e in eta[r:]) - 2 * sum(e * mp.log(e) for e in eta[:r])

def f(t):
    return (r * t * mp.log(t) + r * (e0 - t) * mp.log(e0 - t)
            + sum((t - e0 + e) * mp.log(t - e0 + e) - (t - e) * mp.log(t - e) for e in eta) + Ceta)

def f1(t):
    return r * mp.log(t) - r * mp.log(e0 - t) + sum(mp.log(t - e0 + e) - mp.log(t - e) for e in eta)

def f2(t):
    return r / t + r / (e0 - t) + sum(1 / (t - e0 + e) - 1 / (t - e) for e in eta)

def f0(t):
    return r * e0 * mp.log(e0 - t) + sum(e * mp.log(t - e) - (e0 - e) * mp.log(t - e0 + e) for e in eta) + Ceta

# polynomial P with exact integer coefficients (sympy-free: expand by hand)
def polymul(a, b):
    c = [0] * (len(a) + len(b) - 1)
    for i, x in enumerate(a):
        for j, y in enumerate(b):
            c[i + j] += x * y
    return c
# coefficient lists, lowest degree first
P1 = [1]
for _ in range(r):
    P1 = polymul(P1, [-e0, 1])
for e in eta:
    P1 = polymul(P1, [-e, 1])
P2 = [1]
for _ in range(r):
    P2 = polymul(P2, [0, 1])
for e in eta:
    P2 = polymul(P2, [e - e0, 1])
P = [a - b for a, b in zip(P1, P2)]
while P[-1] == 0:
    P.pop()
print("deg P =", len(P) - 1, " leading coeff =", P[-1])
roots = mp.polyroots(P[::-1], maxsteps=400, extraprec=400)
rows = []
for z in roots:
    z = mp.mpc(z)
    # refine with Newton on P
    for _ in range(5):
        pv = mp.polyval(P[::-1], z)
        dp = mp.polyval([k * c for k, c in enumerate(P)][1:][::-1], z)
        z = z - pv / dp
    lam = f1(z) / (mp.pi * 1j) if mp.im(z) != 0 or (0 < mp.re(z) < e0) else None
    rows.append((z, lam))
print("%-48s %-28s %s" % ("root", "f'/(i pi)", "Re f0 / Im f0/pi"))
for z, lam in sorted(rows, key=lambda w: -float(mp.re(w[0]))):
    if lam is None:
        print("%-48s (on a cut)" % mp.nstr(z, 16))
        continue
    v = f0(z)
    print("%-48s %-28s %s  %s" % (mp.nstr(z, 16), mp.nstr(lam, 8), mp.nstr(mp.re(v), 14), mp.nstr(mp.im(v) / mp.pi, 14)))

# dominant lambda=3 saddle in the upper half plane
cands = [(z, lam) for z, lam in rows if lam is not None and mp.im(z) > 0 and abs(lam - 3) < 1e-20]
print('lambda=3 roots with Im>0:', [mp.nstr(z,12) for z,_ in cands])
t3 = max(cands, key=lambda w: mp.re(w[0]))[0]  # the one on an admissible line e0-e1 < Re < e0
t3 = mp.findroot(lambda t: f1(t) - 3j * mp.pi, t3)
print("\ntau3        =", mp.nstr(t3, 30))
print("f'(tau3)/(i pi) =", mp.nstr(f1(t3) / (1j * mp.pi), 25))
print("f''(tau3)   =", mp.nstr(f2(t3), 20))
v3 = f0(t3)
print("f0(tau3)    =", mp.nstr(v3, 30))
print("check f - tau f' =", mp.nstr(f(t3) - t3 * f1(t3) - v3, 5))
C0 = -mp.re(v3)
om = mp.im(v3) / mp.pi
print("C0          =", mp.nstr(C0, 25))
print("omega/pi    =", mp.nstr(om, 25), " dist to Z:", mp.nstr(abs(om - mp.nint(om)), 10))
# Zudilin's selection rule (JTNB Lemma 20): root with Im>0 and max Re
up = [z for z, lam in rows if mp.im(z) > 1e-30]
zmax = max(up, key=lambda z: mp.re(z))
print("max-Re root with Im>0:", mp.nstr(zmax, 20), " same as tau3:", abs(zmax - t3) < 1e-20)
# lambda=1 saddle(s) in the upper half plane
for z, lam in rows:
    if lam is not None and mp.im(z) > 0 and abs(lam - 1) < 1e-20:
        print("lambda=1 saddle:", mp.nstr(z, 20), " Re f0 =", mp.nstr(mp.re(f0(z)), 15))

# landscape on the line Re tau = x* : u_lam(y) = Re f(x*+iy) + lam*pi*y
xs = mp.re(t3)
def u(lam, y):
    return mp.re(f(mp.mpc(xs, y))) + lam * mp.pi * y
mp.mp.dps = 30
ys = [mp.mpf(k) / 20 for k in range(-2000, 6001)]
u3 = [u(3, y) for y in ys]
u1 = [u(1, y) for y in ys]
i3 = max(range(len(ys)), key=lambda i: u3[i]); i1 = max(range(len(ys)), key=lambda i: u1[i])
print("\nline Re tau = x* =", mp.nstr(xs, 20))
print("grid [-100,300] step 0.05: max u3 = %s at y=%s ; max u1 = %s at y=%s" % (
    mp.nstr(u3[i3], 15), mp.nstr(ys[i3], 6), mp.nstr(u1[i1], 12), mp.nstr(ys[i1], 6)))
# unimodality of u3 on the grid
inc = all(u3[i + 1] > u3[i] for i in range(i3)); dec = all(u3[i + 1] < u3[i] for i in range(i3, len(ys) - 1))
print("u3 strictly increasing before / decreasing after the max on the grid:", inc, dec)
for d in (0.25, 1, 2, 5):
    print("gap u3(y*+-%s) - u3(y*) = %s, %s" % (d, mp.nstr(u(3, mp.im(t3) + d) + C0, 6), mp.nstr(u(3, mp.im(t3) - d) + C0, 6)))
print("u(0) = Re f(x*) =", mp.nstr(u(0, 0), 15))
