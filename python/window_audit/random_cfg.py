# Random admissible configurations (Lean's `Admissible`): generic Stmts must hold for all of them.
import random, sys, io, contextlib
from exact_indep import run
random.seed(int(sys.argv[1]) if len(sys.argv) > 1 else 1)
def admissible(r, q, e0, eta):
    return (r % 2 == 1 and q % 2 == 1 and r >= 3 and r + 4 <= q and eta[0] >= 1
            and all(eta[i] <= eta[i + 1] for i in range(q - 1)) and 2 * eta[-1] < e0
            and 2 * sum(eta) + 2 * r <= (q - r) * e0)
cfgs = [(3, 7, 5, [1] * 7), (3, 7, 7, [1, 1, 1, 2, 2, 2, 2]), (5, 9, 18, [1, 2, 3, 4, 4, 4, 4, 4, 4]), (3, 9, 25, [1, 1, 10, 10, 10, 10, 10, 10, 10]),
        (3, 9, 16, [5, 5, 5, 5, 5, 5, 5, 5, 5])]
while len(cfgs) < 14:
    r = random.choice([3, 3, 5]); q = r + random.choice([4, 6])
    e0 = random.randint(6, 34)
    eta = sorted(random.randint(1, (e0 - 1) // 2) for _ in range(q))
    if admissible(r, q, e0, eta): cfgs.append((r, q, e0, eta))
tot = 0
for c in cfgs:
    assert admissible(*c), c
    for n in (1, 2):
        buf = io.StringIO()
        with contextlib.redirect_stdout(buf):
            out = run(c, n, lean_check=True, zeta_check=False)
        txt = buf.getvalue()
        fl = [l for l in txt.splitlines() if 'FAILURES' in l][0]
        ok = 'FAILURES: 0' in fl
        tot += 0 if ok else 1
        print(c, "n=%d" % n, "OK" if ok else "FAIL", "" if ok else txt)
print("configs with failures:", tot)
