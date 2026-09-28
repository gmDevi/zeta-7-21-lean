# How many table pieces does a certificate need for a given C2hi? (greedy by weight)
import re, sys
from fractions import Fraction as Fr
txt = open(sys.argv[1] if len(sys.argv) > 1 else 'PhiTable.lean', encoding='utf-8').read()
tab = [tuple(map(int, m)) for m in re.findall(r"⟨(\d+), (\d+), (\d+), (\d+), (\d+)⟩", txt)]
def weight(a, b, v, M=60, K=20):
    w = (1 / a - 1 / b) if (a > 0 and Fr(1, M) <= a) else Fr(0)
    for m in range(1, K + 1): w += 1 / (a + m) - 1 / (b + m)
    return v * w
ws = sorted((float(weight(Fr(an, ad), Fr(bn, bd), v)) for an, ad, bn, bd, v in tab), reverse=True)
tot = sum(ws)
for C2hi in (748.0, 749.0, 750.0, 750.5, 750.6):
    need = 1341 - C2hi; acc = 0
    for i, w in enumerate(ws):
        acc += w
        if acc > need: print("C2hi=%.1f needs %d pieces (sum %.4f > %.4f)" % (C2hi, i + 1, acc, need)); break
    else: print("C2hi=%.1f impossible with K=20 (max %.4f)" % (C2hi, tot))
