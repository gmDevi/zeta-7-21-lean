"""margins.py -- certified margins C0 - C2' (mpmath.iv): C0 enclosure from certify_<cfg>.json (130-bit, endpoints printed
to ~38 digits, widened by 1e-30), C2' enclosure recomputed here by c2exact.compute (200-bit, widened by 1e-25).
usage: python margins.py <refdir>"""
import sys, json
sys.path.insert(0, sys.argv[1])
from mpmath import iv, mp
from c2exact import compute
rd = sys.argv[1]
iv.prec = 200; mp.prec = 200
CFG = {'q23_160': ('../../window-21-proof/certify_q23_160.json', 5, 160, [47, 47, 47, 47, 48, 50, 50, 51, 52, 53, 54, 55, 56, 57, 58, 59, 60, 61, 62, 63, 64, 65, 66]),
       'fix160': ('certify_fix160.json', 5, 160, [45, 46, 47, 48, 49, 50, 51, 52, 53, 53, 54, 55, 56, 57, 58, 59, 60, 61, 62, 63, 64, 65, 66]),
       'stair179': ('certify_stair179.json', 5, 179, [54 + j for j in range(1, 24)]),
       'thm3': ('../../window-21-proof/certify_thm3.json', 3, 91, [27, 27, 27] + [25 + j for j in range(4, 14)])}
out = {}
for name, (cj, r, e0, e) in CFG.items():
    J = json.load(open(f'{rd}/{cj}'))
    assert J['all_certified'] if 'all_certified' in J else True
    eps30 = iv.mpf('1e-30')
    C0 = iv.mpf([mp.mpf(J['C0'][0]), mp.mpf(J['C0'][1])]) + iv.mpf([-eps30.b, eps30.b])
    res, _, _ = compute(r, e0, e, tail=True, check=False)
    eps25 = mp.mpf('1e-25')
    C2 = iv.mpf([mp.mpf(res['C2'][0]) - eps25, mp.mpf(res['C2'][1]) + eps25])
    C2p = iv.mpf([mp.mpf(res['C2prime'][0]) - eps25, mp.mpf(res['C2prime'][1]) + eps25])
    mL = C0 - C2; mR = C0 - C2p
    out[name] = dict(r=r, e0=e0, e=e, C0=[mp.nstr(C0.a, 25), mp.nstr(C0.b, 25)], C2=[mp.nstr(C2.a, 25), mp.nstr(C2.b, 25)],
                     G=res['G'], C2prime=[mp.nstr(C2p.a, 25), mp.nstr(C2p.b, 25)],
                     margin_L19=[mp.nstr(mL.a, 20), mp.nstr(mL.b, 20)], margin_refined=[mp.nstr(mR.a, 20), mp.nstr(mR.b, 20)],
                     margin_refined_positive=bool(mR.a > 0), rel_margin=float(mp.mpf(mR.a) / mp.mpf(C2p.b)), per_unit_eta0=float(mp.mpf(mR.a) / e0))
    print(name, json.dumps(out[name]), flush=True)
json.dump(out, open(f'{rd}/margins.json', 'w'), indent=1)
