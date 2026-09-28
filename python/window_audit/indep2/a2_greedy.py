# Auditor-2 (window): pieces a greedy (largest weight first) certificate needs for a given C2hi,
# with K = 20 translates (as phiSumQ) and with all translates (K = None, digamma).
# usage: python a2_greedy.py <path to Zeta2Lean/Window/PhiTable.lean>
import re, sys
from fractions import Fraction as Fr
import mpmath as mp
src = open(sys.argv[1] if len(sys.argv) > 1 else 'PhiTable.lean', encoding='utf-8').read()
P = [tuple(int(z) for z in m) for m in re.findall(r"⟨(\d+), (\d+), (\d+), (\d+), (\d+)⟩", src)]
def w(an, ad, bn, bd, v, K):
    a, b = Fr(an, ad), Fr(bn, bd)
    s = (1 / a - 1 / b) if a >= Fr(1, 60) else Fr(0)
    if K is None:
        return float(v * s) + float(v * (mp.digamma(1 + mp.mpf(bn) / bd) - mp.digamma(1 + mp.mpf(an) / ad)))
    return float(v * (s + sum(Fr(1) / (a + m) - Fr(1) / (b + m) for m in range(1, K + 1))))
for K in (20, None):
    ws = sorted((w(*p, K) for p in P), reverse=True)
    tot = sum(ws)
    for target in (750.6, 750.5, 748.0):
        need = 1341 - target; acc = 0
        for i, x in enumerate(ws):
            acc += x
            if acc >= need: break
        print("K=%s total=%.6f  C2hi=%.1f needs %d pieces (sum %.4f >= %.4f)" % (K, tot, target, i + 1, acc, need))
