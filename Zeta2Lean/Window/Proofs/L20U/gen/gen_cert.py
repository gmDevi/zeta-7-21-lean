"""Generate Zeta2Lean/Window/Proofs/L20U/Cert.lean: certified numerics for the window landscape
U(eta) = C_eta - 336 + 5[Gf(159,eta) - Gf(-1,eta)] - sum_j [Gf(159-eta_j,eta) - Gf(eta_j-1,eta)] - 2 pi eta
at the tangent point p = 9, the monotone cell [46, 60] and the tail [60, oo).

Exact rational arithmetic (fractions.Fraction); every enclosure is re-checked in Lean by norm_num
(lemmas of L20U/Numerics.lean, a verbatim copy of the pair project's Landscape/Numerics.lean).
usage (from the project root; stdlib only):
  python3 Zeta2Lean/Window/Proofs/L20U/gen/gen_cert.py Zeta2Lean/Window/Proofs/L20U/Cert.lean
The enclosure scheme (log_upper, ..., atan_lower) is adapted from the pair project's
Pair/Proofs/Landscape/gen/landscape_common.py (lean_q also prints negative rationals).
"""
import sys
from fractions import Fraction as Fr
from collections import Counter

# ---------------------------------------------------------------- landscape_common (pair project)
C_HI = Fr(6931471808, 10**10)
C_LO = Fr(6931471803, 10**10)
DEC = 10**12


def lean_q(q):
    q = Fr(q)
    if q < 0:
        return "(-(%s) : ℝ)" % lean_q(-q)[1:-5]
    if q.denominator == 1:
        return "(%d : ℝ)" % q.numerator
    return "(%d / %d : ℝ)" % (q.numerator, q.denominator)


def Slog(z): return 2*(z + z**3/3 + z**5/5 + z**7/7 + z**9/9 + z**11/11)
def Rlog(z): return 2*z**13/(13*(1 - z**2))
def ceil_dec(x): return Fr(-((-x.numerator*DEC) // x.denominator), DEC)
def floor_dec(x): return Fr((x.numerator*DEC) // x.denominator, DEC)


def red_pow2(q):
    k = 0
    t = Fr(q)
    while t >= 2:
        t /= 2; k += 1
    while t < 1:
        t *= 2; k -= 1
    return k, t


def log_upper(q):
    q = Fr(q); assert q > 0
    k, t = red_pow2(q)
    z = (t - 1)/(t + 1)
    assert 0 <= z < Fr(1, 3)
    if k >= 0:
        U = ceil_dec(Slog(z) + Rlog(z) + k*C_HI)
        assert q <= 2**k * ((1+z)/(1-z))
        term = ("(log_le_of_le_mul (q := %s) (z := %s) (U := %s) %d (by norm_num) (by norm_num) "
                "(by norm_num) (by norm_num) (by norm_num [Slog, Rlog]))") % (lean_q(q), lean_q(z), lean_q(U), k)
    else:
        U = ceil_dec(Slog(z) + Rlog(z) - (-k)*C_LO)
        assert q * 2**(-k) <= (1+z)/(1-z)
        term = ("(log_le_of_mul_le (q := %s) (z := %s) (U := %s) %d (by norm_num) (by norm_num) "
                "(by norm_num) (by norm_num) (by norm_num [Slog, Rlog]))") % (lean_q(q), lean_q(z), lean_q(U), -k)
    return U, term


def log_lower(q):
    q = Fr(q); assert q > 0
    k, t = red_pow2(q)
    z = (t - 1)/(t + 1)
    if k >= 0:
        L = floor_dec(Slog(z) + k*C_LO)
        term = ("(le_log_of_mul_le (q := %s) (z := %s) (L := %s) %d (by norm_num) (by norm_num) "
                "(by norm_num) (by norm_num [Slog]))") % (lean_q(q), lean_q(z), lean_q(L), k)
    else:
        L = floor_dec(Slog(z) - (-k)*C_HI)
        term = ("(le_log_of_le_mul (q := %s) (z := %s) (L := %s) %d (by norm_num) (by norm_num) "
                "(by norm_num) (by norm_num) (by norm_num [Slog]))") % (lean_q(q), lean_q(z), lean_q(L), -k)
    return L, term


def Pat8(w): return w - w**3/3 + w**5/5 - w**7/7 + w**9/9 - w**11/11 + w**13/13 - w**15/15
def Pat9(w): return Pat8(w) + w**17/17


def atan_upper(u):
    u = Fr(u); assert u >= 0
    if u <= Fr(1, 2):
        U = ceil_dec(Pat9(u))
        return Fr(0), U, "(arctan_le_R1 (u := %s) (U := %s) (by norm_num) (by norm_num [Pat9, Pat8]))" % (lean_q(u), lean_q(U))
    if u <= 1:
        w = (1 - u)/(1 + u)
        L = floor_dec(Pat8(w))
        return Fr(1, 4), -L, ("(arctan_le_R2 (u := %s) (w := %s) (L := %s) (by norm_num) (by norm_num) "
                              "(by norm_num) (by norm_num [Pat8]))") % (lean_q(u), lean_q(w), lean_q(L))
    if u <= 2:
        w = (u - 1)/(u + 1)
        U = ceil_dec(Pat9(w))
        return Fr(1, 4), U, ("(arctan_le_R3 (u := %s) (w := %s) (U := %s) (by norm_num) (by norm_num) "
                             "(by norm_num) (by norm_num [Pat9, Pat8]))") % (lean_q(u), lean_q(w), lean_q(U))
    w = 1/u
    L = floor_dec(Pat8(w))
    return Fr(1, 2), -L, ("(arctan_le_R4 (u := %s) (w := %s) (L := %s) (by norm_num) (by norm_num) "
                          "(by norm_num [Pat8]))") % (lean_q(u), lean_q(w), lean_q(L))


def atan_lower(u):
    u = Fr(u); assert u >= 0
    if u <= Fr(1, 2):
        L = floor_dec(Pat8(u))
        return Fr(0), L, "(arctan_ge_R1 (u := %s) (L := %s) (by norm_num) (by norm_num [Pat8]))" % (lean_q(u), lean_q(L))
    if u <= 1:
        w = (1 - u)/(1 + u)
        U = ceil_dec(Pat9(w))
        return Fr(1, 4), -U, ("(arctan_ge_R2 (u := %s) (w := %s) (U := %s) (by norm_num) (by norm_num) "
                              "(by norm_num) (by norm_num [Pat9, Pat8]))") % (lean_q(u), lean_q(w), lean_q(U))
    if u <= 2:
        w = (u - 1)/(u + 1)
        L = floor_dec(Pat8(w))
        return Fr(1, 4), L, ("(arctan_ge_R3 (u := %s) (w := %s) (L := %s) (by norm_num) (by norm_num) "
                             "(by norm_num) (by norm_num [Pat8]))") % (lean_q(u), lean_q(w), lean_q(L))
    w = 1/u
    U = ceil_dec(Pat9(w))
    return Fr(1, 2), -U, ("(arctan_ge_R4 (u := %s) (w := %s) (U := %s) (by norm_num) (by norm_num) "
                          "(by norm_num [Pat9, Pat8]))") % (lean_q(u), lean_q(w), lean_q(U))

# ---------------------------------------------------------------- the window landscape
PI_LO = Fr(314159265358979323846, 10**20)
PI_HI = Fr(314159265358979323847, 10**20)
ETA = [47, 47, 47, 47, 48, 50, 50, 51, 52, 53, 54, 55, 56, 57, 58, 59, 60, 61, 62, 63, 64, 65, 66]
assert sum(ETA) == 1272
P = Fr(9)
MULT = Counter(ETA)          # eta -> multiplicity (j = 1..23)
ETAS = sorted(MULT)          # 47, 48, 50, ..., 66
A_VALS = [e - 1 for e in ETAS]     # + terms  Gf(eta-1, p)
B_VALS = [159 - e for e in ETAS]   # - terms  Gf(159-eta, p)
PLUS = [159, 1] + A_VALS           # Gf upper bounds, arctan(./9) upper
MINUS = B_VALS                     # Gf lower bounds


def lit(a):
    """Lean literal of a rational as it should appear inside expressions (no type ascription)."""
    a = Fr(a)
    if a < 0:
        return "-(%s)" % lit(-a)
    if a.denominator == 1:
        return "%d" % a.numerator
    return "%d / %d" % (a.numerator, a.denominator)


def rnum(v): return "(%s : ℝ)" % lit(v)
def pi_expr(al, c): return "%s * π + %s" % (rnum(al), rnum(c))
def ceil6(x): return Fr(-((-x.numerator*10**6)//x.denominator), 10**6)
def floor6(x): return Fr((x.numerator*10**6)//x.denominator, 10**6)


def ev_up(pc, c): return (PI_HI if pc > 0 else PI_LO)*pc + c
def ev_lo(pc, c): return (PI_LO if pc > 0 else PI_HI)*pc + c


class Cert:
    def __init__(self):
        self.lines = []
        self.logf = {}
        self.atf = {}
        self.gff = {}

    def log_fact(self, Q, dirn):
        key = (Fr(Q), dirn)
        if key not in self.logf:
            name = "cl%d" % (len(self.logf) + 1)
            if dirn == 'up':
                b, t = log_upper(Q); stmt = "Real.log %s ≤ %s" % (rnum(Q), rnum(b))
            else:
                b, t = log_lower(Q); stmt = "%s ≤ Real.log %s" % (rnum(b), rnum(Q))
            self.lines.append("theorem %s : %s := by\n  have h := %s\n  linarith\n" % (name, stmt, t))
            self.logf[key] = (name, b)
        return self.logf[key]

    def at_fact(self, V, dirn):
        key = (Fr(V), dirn)
        if key not in self.atf:
            name = "ca%d" % (len(self.atf) + 1)
            if dirn == 'up':
                al, c, t = atan_upper(V); stmt = "Real.arctan %s ≤ %s" % (rnum(V), pi_expr(al, c))
            else:
                al, c, t = atan_lower(V); stmt = "%s ≤ Real.arctan %s" % (pi_expr(al, c), rnum(V))
            self.lines.append("theorem %s : %s := by\n  have h := %s\n  linarith\n" % (name, stmt, t))
            self.atf[key] = (name, al, c)
        return self.atf[key]

    def gf_fact(self, a, y, dirn):
        """a > 0, y > 0: Gf a y = a/2 log(a^2+y^2) + y arctan(a/y) - a, bounded up or down as P pi + C"""
        a = Fr(a); y = Fr(y)
        key = (a, y, dirn)
        if key in self.gff:
            return self.gff[key]
        assert a > 0 and y > 0
        name = "cg%d" % (len(self.gff) + 1)
        Q = a*a + y*y; V = a/y
        ln, lb = self.log_fact(Q, dirn)
        an, al, ac = self.at_fact(V, dirn)
        Pc = y*al; C = a/2*lb + y*ac - a
        eq = "Gf_eq_pos (a := %s) (y := %s) (Q := %s) (V := %s) (by norm_num) (by norm_num)" % (
            rnum(a), rnum(y), rnum(Q), rnum(V))
        if dirn == 'up':
            stmt = "Gf %s %s ≤ %s" % (rnum(a), rnum(y), pi_expr(Pc, C))
        else:
            stmt = "%s ≤ Gf %s %s" % (pi_expr(Pc, C), rnum(a), rnum(y))
        self.lines.append("theorem %s : %s := by\n  rw [%s]\n  linarith [%s, %s]\n" % (name, stmt, eq, ln, an))
        self.gff[key] = (name, Pc, C)
        return self.gff[key]


def main(out):
    cert = Cert()
    L = []
    # ---- C_eta upper bound
    ceta_terms = []   # (coefficient, argument)
    for e in ETAS:
        if e < 50:
            continue
        m = MULT[e]
        a = 160 - 2*e
        ceta_terms.append((m*a, a))
    cl = []
    Cpc = Fr(0); Cc = Fr(0)
    for coef, a in ceta_terms:
        n, b = cert.log_fact(a, 'up'); cl.append(n); Cc += coef*b
    neg_terms = [(MULT[47]*47, 47), (MULT[48]*48, 48)]
    for coef, a in neg_terms:
        n, b = cert.log_fact(a, 'lo'); cl.append(n); Cc -= 2*coef*b
    ceta_hi = ceil6(Cc)
    ceta_rhs = " + ".join("%d * Real.log %d" % (coef, a) for coef, a in ceta_terms) + \
        " - 2 * (%d * Real.log 47 + %d * Real.log 48)" % (neg_terms[0][0], neg_terms[1][0])
    # ---- U(9) upper bound: C_eta - 336 + 5 (Gf 159 9 + Gf 1 9) - sum_e m_e (Gf (159-e) 9 - Gf (e-1) 9) - 18 pi
    names = []
    upc = Fr(-18); uc = ceta_hi - 336
    for a in [159, 1]:
        n, Pc, C = cert.gf_fact(a, P, 'up'); names.append(n); upc += 5*Pc; uc += 5*C
    for e in ETAS:
        m = MULT[e]
        nb, Pb, Cb = cert.gf_fact(159 - e, P, 'lo'); names.append(nb)
        na, Pa, Ca = cert.gf_fact(e - 1, P, 'up'); names.append(na)
        upc += -m*Pb + m*Pa; uc += -m*Cb + m*Ca
    U9hi = ceil6(ev_up(upc, uc))

    def gterm(e):
        m = MULT[e]
        s = "(Gf %s 9 - Gf %s 9)" % (lit(159 - e), lit(e - 1))
        return s if m == 1 else "%d * %s" % (m, s)
    u9_rhs = "Ceta - 336 + 5 * (Gf 159 9 + Gf 1 9) - (" + " + ".join(gterm(e) for e in ETAS) + ") - 2 * π * 9"
    # ---- U'(9) two-sided: 5 (arctan(159/9) + arctan(1/9)) - sum_e m_e (arctan((159-e)/9) - arctan((e-1)/9)) - 2 pi
    def dterm(e):
        m = MULT[e]
        s = "(Real.arctan %s - Real.arctan %s)" % (rnum(Fr(159 - e, 9)), rnum(Fr(e - 1, 9)))
        return s if m == 1 else "%d * %s" % (m, s)
    d9_rhs = "5 * (Real.arctan %s + Real.arctan %s) - (" % (rnum(Fr(159, 9)), rnum(Fr(1, 9))) + \
        " + ".join(dterm(e) for e in ETAS) + ") - 2 * π"
    dn_hi = []; dpc_hi = Fr(-2); dc_hi = Fr(0)
    dn_lo = []; dpc_lo = Fr(-2); dc_lo = Fr(0)
    for v in [159, 1]:
        n, al, c = cert.at_fact(Fr(v, 9), 'up'); dn_hi.append(n); dpc_hi += 5*al; dc_hi += 5*c
        n, al, c = cert.at_fact(Fr(v, 9), 'lo'); dn_lo.append(n); dpc_lo += 5*al; dc_lo += 5*c
    for e in ETAS:
        m = MULT[e]
        n, al, c = cert.at_fact(Fr(159 - e, 9), 'lo'); dn_hi.append(n); dpc_hi -= m*al; dc_hi -= m*c
        n, al, c = cert.at_fact(Fr(e - 1, 9), 'up'); dn_hi.append(n); dpc_hi += m*al; dc_hi += m*c
        n, al, c = cert.at_fact(Fr(159 - e, 9), 'up'); dn_lo.append(n); dpc_lo -= m*al; dc_lo -= m*c
        n, al, c = cert.at_fact(Fr(e - 1, 9), 'lo'); dn_lo.append(n); dpc_lo += m*al; dc_lo += m*c
    D9hi = ceil6(ev_up(dpc_hi, dc_hi))
    D9lo = floor6(ev_lo(dpc_lo, dc_lo))
    # ---- cell [46, 60]: 5 (arctan(159/46) + arctan(1/46)) - 23 (arctan(93/60) - arctan(65/46)) - 2 pi
    c1 = cert.at_fact(Fr(159, 46), 'up'); c2 = cert.at_fact(Fr(1, 46), 'up')
    c3 = cert.at_fact(Fr(93, 60), 'lo'); c4 = cert.at_fact(Fr(65, 46), 'up')
    cpc = 5*c1[1] + 5*c2[1] - 23*c3[1] + 23*c4[1] - 2
    cc = 5*c1[2] + 5*c2[2] - 23*c3[2] + 23*c4[2]
    cell = ceil6(ev_up(cpc, cc))
    # ---- tail [60, oo): 5 (arctan(159/60) + arctan(1/60)) - 2 pi
    t1 = cert.at_fact(Fr(159, 60), 'up'); t2 = cert.at_fact(Fr(1, 60), 'up')
    tpc = 5*t1[1] + 5*t2[1] - 2
    tc = 5*t1[2] + 5*t2[2]
    tail = ceil6(ev_up(tpc, tc))
    print("Ceta_hi", float(ceta_hi), "U9hi", float(U9hi), "D9", float(D9lo), float(D9hi),
          "cell", float(cell), "tail", float(tail), "U9hi+37D9hi", float(U9hi + 37*D9hi), file=sys.stderr)
    assert D9lo >= 0 and U9hi + 37*D9hi <= -749 and cell <= Fr(-1, 2) and tail <= Fr(-1, 10)
    print("facts: log %d, arctan %d, Gf %d" % (len(cert.logf), len(cert.atf), len(cert.gff)), file=sys.stderr)

    H = []
    H.append('''module

public import Zeta2Lean.Window.Proofs.L20U.Pointwise
public import Zeta2Lean.Window.Proofs.L20U.Numerics

@[expose] public section

set_option linter.style.header false
set_option linter.style.longLine false

/-!
# Theorem U, part 5a: certified numerical values for the landscape (GENERATED)

Generated by `gen_cert.py` (exact rational arithmetic; see the docstring of `L20U/Landscape.lean`).
Every `log`/`arctan` enclosure is re-checked here by `norm_num` through the lemmas of
`L20U/Numerics.lean` (`artanh` series with a geometric tail, alternating Taylor polynomials of
`arctan` with range reduction, `Real.log_two_gt_d9`/`_lt_d9`), and `π` by `Real.pi_gt_d20`,
`Real.pi_lt_d20`.  Values used (`p = 9`, true values in brackets):
* `C_η ≤ %s` [`1275.7761127…`];
* `U(9) ≤ %s` [`-750.6313113…`];
* `%s ≤ U'(9) ≤ %s` [`0.0147383…`];  hence `U(9) + 37 U'(9) ≤ %s < -749`;
* cell `[46, 60]`: `5(arctan(159/46) + arctan(1/46)) - 23(arctan(93/60) - arctan(65/46)) - 2π ≤ %s`;
* tail: `5(arctan(159/60) + arctan(1/60)) - 2π ≤ %s` [`-0.1503…`].
-/

open Real Finset

noncomputable section

namespace ZetaWindow

namespace L20U

/-- `U'(η)` for `η > 0` (`∂_η Gf(a, η) = arctan(a/η)`, `Gf(-1, ·) = -Gf(1, ·)`). -/
def dUw (η : ℝ) : ℝ :=
  5 * (Real.arctan (159 / η) + Real.arctan (1 / η)) -
    ∑ j ∈ Icc 1 23, (Real.arctan ((159 - (etaW j : ℝ)) / η) - Real.arctan (((etaW j : ℝ) - 1) / η)) -
      2 * π

theorem Gf_eq_pos {a y Q V : ℝ} (hQ : a ^ 2 + y ^ 2 = Q) (hV : a / y = V) :
    Gf a y = a / 2 * Real.log Q + y * Real.arctan V - a := by
  unfold Gf; rw [hQ, hV]

/-! ## Enclosures -/
''' % (lit(ceta_hi), lit(U9hi), lit(D9lo), lit(D9hi), lit(U9hi + 37*D9hi), lit(cell), lit(tail)))
    body = "\n".join(cert.lines)
    T = []
    T.append('''
/-! ## `C_η`, `U(9)`, `U'(9)` -/

theorem Ceta_eq : Ceta = %s := by
  unfold Ceta
  rw [show Finset.Icc 6 23 = Finset.Ico 6 24 by decide, show Finset.Icc 1 5 = Finset.Ico 1 6 by decide,
    Finset.sum_Ico_eq_sum_range, Finset.sum_Ico_eq_sum_range]
  norm_num [Finset.sum_range_succ, etaW]
  ring

theorem Ceta_le : Ceta ≤ %s := by
  rw [Ceta_eq]
  linarith [%s]

theorem Uw9_eq : Uw 9 = %s := by
  unfold Uw
  rw [show Gf (-1) 9 = -Gf 1 9 from Gf_neg 1 9]
  rw [show Finset.Icc 1 23 = Finset.Ico 1 24 by decide, Finset.sum_Ico_eq_sum_range]
  norm_num [Finset.sum_range_succ, etaW]
  ring

theorem Uw9_le : Uw 9 ≤ %s := by
  rw [Uw9_eq]
  linarith [Ceta_le, %s, Real.pi_gt_d20, Real.pi_lt_d20]

theorem dUw9_eq : dUw 9 = %s := by
  unfold dUw
  rw [show Finset.Icc 1 23 = Finset.Ico 1 24 by decide, Finset.sum_Ico_eq_sum_range]
  norm_num [Finset.sum_range_succ, etaW]
  ring

theorem dUw9_le : dUw 9 ≤ %s := by
  rw [dUw9_eq]
  linarith [%s, Real.pi_gt_d20, Real.pi_lt_d20]

theorem dUw9_ge : %s ≤ dUw 9 := by
  rw [dUw9_eq]
  linarith [%s, Real.pi_gt_d20, Real.pi_lt_d20]

theorem cell_le :
    5 * (Real.arctan (159 / 46) + Real.arctan (1 / 46)) -
      23 * (Real.arctan (31 / 20) - Real.arctan (65 / 46)) - 2 * π ≤ %s := by
  linarith [%s, %s, %s, %s, Real.pi_gt_d20, Real.pi_lt_d20]

theorem tail_le : 5 * (Real.arctan (53 / 20) + Real.arctan (1 / 60)) - 2 * π ≤ %s := by
  linarith [%s, %s, Real.pi_gt_d20, Real.pi_lt_d20]

end L20U

end ZetaWindow

end
''' % (ceta_rhs, lit(ceta_hi), ", ".join(cl),
       u9_rhs, lit(U9hi), ", ".join(names),
       d9_rhs, lit(D9hi), ", ".join(dn_hi), lit(D9lo), ", ".join(dn_lo),
       lit(cell), c1[0], c2[0], c3[0], c4[0],
       lit(tail), t1[0], t2[0]))
    with open(out, "w", newline="\n") as f:
        f.write(H[0] + "\n" + body + T[0])


if __name__ == "__main__":
    main(sys.argv[1])
