# Independent saddle-point data for cfgW (auditor's code).
import mpmath as mp
mp.mp.dps = 60
r, q, e0 = 5, 23, 160
def etaW(j):
    if j <= 4: return 47
    if j == 5: return 48
    if j <= 7: return 50
    return j + 43
eta = [etaW(j) for j in range(1, q + 1)]

# P(tau) = (tau-e0)^r prod(tau-eta_j) - tau^r prod(tau-e0+eta_j), integer coefficients
def polymul(a, b):
    out = [0] * (len(a) + len(b) - 1)
    for i, x in enumerate(a):
        for j, y in enumerate(b):
            out[i + j] += x * y
    return out
# coefficient lists, highest degree first
P1 = [1]
for _ in range(r): P1 = polymul(P1, [1, -e0])
for e in eta: P1 = polymul(P1, [1, -e])
P2 = [1]
for _ in range(r): P2 = polymul(P2, [1, 0])
for e in eta: P2 = polymul(P2, [1, -(e0 - e)])
P = [a - b for a, b in zip(P1, P2)]
while P[0] == 0: P = P[1:]
print("deg P =", len(P) - 1)
roots = mp.polyroots(P, maxsteps=500, extraprec=800)

Ceta = sum((e0 - 2 * e) * mp.log(e0 - 2 * e) for e in eta[r:]) - 2 * sum(e * mp.log(e) for e in eta[:r])
def fp(t):   # f'(tau), principal logs
    return r * mp.log(t) - r * mp.log(e0 - t) + sum(mp.log(t - e0 + e) - mp.log(t - e) for e in eta)
def fpp(t):
    return r / t + r / (e0 - t) + sum(1 / (t - e0 + e) - 1 / (t - e) for e in eta)
def f(t):
    xl = lambda z: z * mp.log(z)
    return r * xl(t) + r * xl(e0 - t) + sum(xl(t - e0 + e) - xl(t - e) for e in eta) + Ceta
def f0(t):
    return r * e0 * mp.log(e0 - t) + sum(e * mp.log(t - e) - (e0 - e) * mp.log(t - e0 + e) for e in eta) + Ceta

print("C_eta =", mp.nstr(Ceta, 20))
rows = []
for z in roots:
    if abs(mp.im(z)) < mp.mpf(10) ** -40: z = mp.mpf(mp.re(z))
    lam = fp(mp.mpc(z)) / (1j * mp.pi) if mp.im(z) != 0 else None
    rows.append((z, lam))
rows.sort(key=lambda zr: (float(mp.re(zr[0])), float(mp.im(zr[0]))))
for z, lam in rows:
    s = "tau = %-45s" % mp.nstr(z, 18)
    if lam is not None:
        v = f0(mp.mpc(z))
        s += " lambda = %-28s Re f0 = %s" % (mp.nstr(lam, 8), mp.nstr(mp.re(v), 14))
    print(s)

# dominant saddle of branch lambda = 3 in the upper half plane with eta0-eta1 < Re < eta0
cands = [(z, lam) for z, lam in rows if lam is not None and abs(lam - 3) < 1e-20]
print("lambda=3 roots:", [mp.nstr(z, 12) for z, _ in cands])
tau3 = [z for z, _ in cands if mp.im(z) > 0 and e0 - eta[0] < mp.re(z) < e0][0]
v = f0(tau3)
print("tau3 =", mp.nstr(tau3, 25))
print("f'(tau3)/(i pi) =", mp.nstr(fp(tau3) / (1j * mp.pi), 25))
print("f''(tau3) =", mp.nstr(fpp(tau3), 15))
print("C0 = -Re f0(tau3) =", mp.nstr(-mp.re(v), 25))
print("omega/pi = Im f0(tau3)/pi =", mp.nstr(mp.im(v) / mp.pi, 25))
print("check f(tau3) - tau3 f'(tau3) - f0(tau3) =", mp.nstr(abs(f(tau3) - tau3 * fp(tau3) - v), 5))
C2 = mp.mpf('747.0513057896742841981284')
print("C0 - C2 =", mp.nstr(-mp.re(v) - C2, 15))
for lam in (1,):
    cs = [z for z, l in rows if l is not None and abs(l - lam) < 1e-20 and mp.im(z) > 0]
    for z in cs:
        print("lambda=1 saddle", mp.nstr(z, 15), " Re f0 =", mp.nstr(mp.re(f0(z)), 15))

# landscape on the line Re tau = x*
xs = mp.re(tau3)
mp.mp.dps = 30
def u(lam, y):
    return mp.re(f(mp.mpc(xs, y))) + lam * mp.pi * y
print("u(0) = Re f(x*) =", mp.nstr(u(0, 0), 15))
import math
for lam in (3, 1):
    best = (-1e9, None)
    y = -300.0
    while y <= 300.0:
        val = float(u(lam, y))
        if val > best[0]: best = (val, y)
        y += 0.05
    # refine
    yy = mp.findroot(lambda t: mp.diff(lambda s: u(lam, s), t), best[1]) if abs(best[1]) < 299 else best[1]
    print("lambda=%d: grid max %.6f at y=%.3f ; refined max u = %s at y = %s" % (lam, best[0], best[1], mp.nstr(u(lam, yy), 15), mp.nstr(yy, 12)))
# monotonicity of u3 away from y* on a grid
ys = mp.im(tau3)
prev = None; mono_ok = True
y = -300.0
vals = []
while y <= 300.0:
    vals.append((y, float(u(3, y)))); y += 0.1
for (y1, v1), (y2, v2) in zip(vals, vals[1:]):
    if y2 <= float(ys) and v2 < v1 - 1e-12: mono_ok = False
    if y1 >= float(ys) and v2 > v1 + 1e-12: mono_ok = False
print("u3 unimodal on grid [-300,300] step 0.1:", mono_ok)
# gaps
for d in (0.25, 1, 2, 5):
    print("u3(y*+-%s) + C0 =" % d, mp.nstr(u(3, ys + d) - mp.re(v), 8), mp.nstr(u(3, ys - d) - mp.re(v), 8))
