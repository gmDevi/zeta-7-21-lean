import sys, json, mpmath as mp
sys.path.insert(0, sys.argv[1])
from zud5 import *
name = sys.argv[2] if len(sys.argv) > 2 else 'q23_160'
cfg = CONFIGS[name]; r, e0, e = cfg['r'], cfg['e0'], cfg['e']
mp.mp.dps = 40
rts, co = roots(cfg, dps=80)
print('config', name, 'degree', len(co) - 1, 'nroots', len(rts))
print('sum eta =', sum(e), ' bound eta0(q-r)/2 =', e0 * (len(e) - r) / 2)
rows = []
for z in rts:
    fp = fprime(z, cfg)
    lam = fp / (1j * mp.pi)
    v0 = f0(z, cfg)
    rows.append((float(mp.re(z)), float(mp.im(z)), complex(lam), float(mp.re(v0)), float(mp.im(v0) / mp.pi)))
rows.sort(key=lambda t: (-t[0], -t[1]))
print('%12s %12s | %8s %8s | %12s %12s' % ('Re tau', 'Im tau', 'Re lam', 'Im lam', 'Re f0', 'Im f0/pi'))
for a, b, lam, rf, imf in rows:
    print('%12.6f %12.6f | %8.4f %8.4f | %12.4f %12.4f' % (a, b, lam.real, lam.imag, rf, imf))
# real lambda=0 saddle mu0 in the gap (eta0-eta1, eta0)
g = lambda x: mp.re(fprime(mp.mpc(x, 0), cfg))
mu0 = mp.findroot(g, (e0 - e[0] + 0.5, e0 - 0.01), solver='bisect')
print('mu0 (lambda=0 real saddle) =', mu0, ' f(mu0) =', mp.re(f(mu0, cfg)), " f''(mu0) =", mp.re(fsecond(mu0, cfg)))
ups = [z for z in rts if mp.im(z) > 1e-10 and mp.re(z) > e0 - e[0]]
ups.sort(key=lambda z: -mp.re(z))
for z in ups:
    lam = int(mp.nint(mp.re(fprime(z, cfg) / (1j * mp.pi))))
    Ph = Phi(z, lam, cfg); Pp = fsecond(z, cfg)
    print('saddle k=%d: tau=%s  Phi_k(tau)=%s  f0=%s  Phi2=%s  |Phi2|=%.6f arg=%.6f' % (
        lam, mp.nstr(z, 12), mp.nstr(Ph, 12), mp.nstr(f0(z, cfg), 12), mp.nstr(Pp, 8), float(abs(Pp)), float(mp.arg(Pp))))
    th = (mp.pi - mp.arg(Pp)) / 2
    print('   descent directions theta = %.5f rad (%.2f deg) and opposite' % (float(th), float(th * 180 / mp.pi)))
print('real profile f(x) on gap:')
for x in [e0 - e[0] + 0.5, 120, 130, 140, 150, float(mu0), 155, 158, 159, 159.3564, 159.9, 159.99]:
    print('   x=%9.4f  f=%12.4f  fp=%10.4f' % (x, float(mp.re(f(mp.mpc(x, 1e-30), cfg))), float(mp.re(fprime(mp.mpc(x, 1e-30), cfg)))))
print('cut profile Re f(x+i0) for x>e0 (terms of the sum; branch lambda=5):')
for x in [e0 + 1e-6, e0 + 0.01, e0 + 0.1, e0 + 0.5, e0 + 1, e0 + 2, e0 + 5, e0 + 10, e0 + 20, e0 + 50]:
    z = mp.mpc(x, 1e-30)
    print('   x=%9.4f  Re f=%12.4f  Im fp/pi=%8.4f' % (x, float(mp.re(f(z, cfg))), float(mp.im(fprime(z, cfg)) / mp.pi)))
t3 = ups[0]
print('vertical line through tau_3 (Re Phi_3 and Re Phi_1):')
for y in [-40, -20, -10, -5, -2, 0, 2, 4, 6, 8, float(mp.im(t3)), 10, 12, 15, 20, 30, 50, 80, 120, 200]:
    z = mp.mpc(mp.re(t3), y) if y != 0 else mp.mpc(mp.re(t3), 1e-30)
    print('   y=%8.3f  RePhi3=%12.4f  RePhi1=%12.4f  Im fp/pi=%8.4f' % (y, float(mp.re(Phi(z, 3, cfg))), float(mp.re(Phi(z, 1, cfg))), float(mp.im(fprime(z, cfg)) / mp.pi)))
def descend(z0, k, sgn, h=0.02, smax=400):
    Pp = fsecond(z0, cfg)
    th = (mp.pi - mp.arg(Pp)) / 2
    z = z0 + sgn * mp.mpf('1e-3') * mp.exp(1j * th)
    path = [z]; s = 0
    while s < smax:
        d = -mp.conj(Phiprime(z, k, cfg)); d = d / abs(d)
        zm = z + h / 2 * d
        d2 = -mp.conj(Phiprime(zm, k, cfg)); d2 = d2 / abs(d2)
        z = z + h * d2; s += h
        path.append(z)
        if mp.im(z) < 1e-6 and len(path) > 5 and mp.im(path[-2]) >= 1e-6:
            break
        if mp.im(z) > 300 or mp.im(z) < -300 or mp.re(z) < 0 or mp.re(z) > 2 * e0:
            break
    return path
for (z0, k) in [(ups[0], 3), (ups[1], 1)]:
    for sgn in (+1, -1):
        p = descend(z0, k, sgn)
        end = p[-1]
        print('descent from k=%d saddle %s dir %+d: end after %d steps at %s, RePhi_k there = %.3f' % (
            k, mp.nstr(z0, 8), sgn, len(p), mp.nstr(end, 8), float(mp.re(Phi(end, k, cfg)))))
        for i in range(0, len(p), max(1, len(p) // 12)):
            z = p[i]
            print('      %s  RePhi=%.4f' % (mp.nstr(z, 8), float(mp.re(Phi(z, k, cfg)))))
