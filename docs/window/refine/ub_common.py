"""ub_common.py -- shared definitions for the crude (pointwise) upper bound of F~_n, window {7..21}.

Configuration (proof.md of window-21-proof): r = 5, q = 23, eta0 = 160,
  eta = (47,47,47,47,48,50,50,51,52,...,66),  h0 = 160 n + 2,  h_j = eta_j n + 1.
  R(t) = (h0+2t) prod_{l=1}^{h0-1}(t+l)^5 / prod_j prod_{l=h_j}^{h0-h_j}(t+l),
  N_h = prod_{j>5}(h0-2h_j)! / prod_{j<=5}((h_j-1)!)^2,   F~_n = N_h sum_{t>=0} R^{(4)}(t)/4!.

Real-variable landscape (no complex logarithms):
  Gf(a, y) = (a/2) log(a^2+y^2) + y arctan(a/y) - a      (y != 0),   Gf(a, 0) = a log|a| - a,
  i.e. Gf(., y) is the antiderivative in a of log|a + i y|;   d/dy Gf(a, y) = arctan(a/y) (y > 0).
  V(x, y) = 5[Gf(x, y) - Gf(x-eta0, y)] - sum_j [Gf(x-eta_j, y) - Gf(x-eta0+eta_j, y)],
  U(x, y) = C_eta - 336 + V(x, y) - 2 pi |y|,
  C_eta = sum_{j>5}(eta0-2eta_j) log(eta0-2eta_j) - 2 sum_{j<=5} eta_j log eta_j.
Identity (check only, not used in the proof): U(x, y) = Re f(x+iy) + 3 pi |y| = u_3(y) of proof.md 3.5.
"""
import mpmath as mp

R_ = 5
E0 = 160
ETA = [47, 47, 47, 47, 48, 50, 50, 51, 52, 53, 54, 55, 56, 57, 58, 59, 60, 61, 62, 63, 64, 65, 66]
Q_ = len(ETA)
assert Q_ == 23 and sum(ETA) == 1272
# log-n coefficient: 5*eta0 - sum_j (eta0 - 2 eta_j) = -336
assert R_ * E0 - sum(E0 - 2 * e for e in ETA) == -336
assert sum(E0 - 2 * e for e in ETA[R_:]) - 2 * sum(ETA[:R_]) == 336


def C_eta():
    return sum((E0 - 2 * e) * mp.log(E0 - 2 * e) for e in ETA[R_:]) - 2 * sum(e * mp.log(e) for e in ETA[:R_])


def Gf(a, y):
    a = mp.mpf(a); y = mp.mpf(y)
    if y == 0:
        return (a * mp.log(abs(a)) - a) if a != 0 else mp.mpf(0)
    return a / 2 * mp.log(a * a + y * y) + y * mp.atan(a / y) - a


def V(x, y):
    x = mp.mpf(x)
    v = R_ * (Gf(x, y) - Gf(x - E0, y))
    for e in ETA:
        v -= Gf(x - e, y) - Gf(x - E0 + e, y)
    return v


def U(x, y):
    return C_eta() - 336 + V(x, y) - 2 * mp.pi * abs(mp.mpf(y))


def dU_dy(x, y):
    """d/dy U(x, y) for y > 0:  sum of +-arctan(a/y) - 2 pi."""
    x = mp.mpf(x); y = mp.mpf(y)
    v = R_ * (mp.atan(x / y) - mp.atan((x - E0) / y))
    for e in ETA:
        v -= mp.atan((x - e) / y) - mp.atan((x - E0 + e) / y)
    return v - 2 * mp.pi


def d2U_dy2(x, y):
    """d^2/dy^2 U = -[5(h(x)+h(c)) + sum_j (h(a_j) - h(b_j))],  h(a) = a/(a^2+y^2)."""
    x = mp.mpf(x); y = mp.mpf(y)
    h = lambda a: a / (a * a + y * y)
    v = R_ * (h(x) + h(E0 - x))
    for e in ETA:
        v += h(x - E0 + e) - h(x - e)
    return -v


def dU_dx(x, y):
    """d/dx U = Re f'(x+iy) = (1/2)[5 log((x^2+y^2)/((x-eta0)^2+y^2)) - sum_j log(((x-eta_j)^2+y^2)/((x-eta0+eta_j)^2+y^2))]."""
    x = mp.mpf(x); y = mp.mpf(y)
    L = lambda a: mp.log(a * a + y * y)
    v = R_ * (L(x) - L(x - E0))
    for e in ETA:
        v -= L(x - e) - L(x - E0 + e)
    return v / 2


# ---- complex-analytic phase (proof.md 3.3), for cross-checks only
def f_complex(tau):
    tau = mp.mpc(tau)
    v = R_ * tau * mp.log(tau) + R_ * (E0 - tau) * mp.log(E0 - tau)
    for e in ETA:
        v += (tau - E0 + e) * mp.log(tau - E0 + e) - (tau - e) * mp.log(tau - e)
    return v + C_eta()


# ---- exact objects at finite n (for validation)
def h0(n):
    return E0 * n + 2


def hj(n, j):          # j = 1..23
    return ETA[j - 1] * n + 1


def log_abs_R(n, t):
    """log |R(t)| by direct summation over the linear factors (t complex, not a pole)."""
    t = mp.mpc(t)
    H0 = h0(n)
    v = mp.log(abs(H0 + 2 * t))
    s = mp.mpf(0)
    for l in range(1, H0):
        s += mp.log(abs(t + l))
    v += R_ * s
    for j in range(1, Q_ + 1):
        H = hj(n, j)
        for l in range(H, H0 - H + 1):
            v -= mp.log(abs(t + l))
    return v


def log_Nh(n):
    H0 = h0(n)
    v = mp.mpf(0)
    for j in range(R_ + 1, Q_ + 1):
        v += mp.loggamma(H0 - 2 * hj(n, j) + 1)
    for j in range(1, R_ + 1):
        v -= 2 * mp.loggamma(hj(n, j))
    return v


def K5(t):
    """K_5(t) = (1/4!) (d/dt)^4 [pi cot pi t] = sum_k (t-k)^{-5} = (pi^5/24) * 8C(1+C^2)(2+3C^2), C = cot(pi t).
    Evaluated as (pi^5/3) C (2+3C^2) / sin^2(pi t)  (1 + C^2 = csc^2): no cancellation for large |Im t|."""
    t = mp.mpc(t)
    C = mp.cot(mp.pi * t)
    S = mp.sin(mp.pi * t)
    return mp.pi ** 5 / 3 * C * (2 + 3 * C * C) / (S * S)
