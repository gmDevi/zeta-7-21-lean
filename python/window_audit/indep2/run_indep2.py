# Second independent audit pass (auditor-2, 2026-09-25, after the WSL crash).  Own code; it does not
# import python/window_mirror.py, python/window_audit/*.py, or docs/window/*.py.
#   a2_saddle.py       all 27 roots of the saddle polynomial P, branch f'/(i pi), f0, tau3, f'', C0, omega/pi,
#                      Zudilin's max-Re rule, the landscape u_1, u_3 on the line Re tau = x* (grid [-100, 300]).
#   a2_series.py       F~_n for n = 1..9 by direct high-precision summation of sum_t [eps^4] R~(t+eps)
#                      (log-derivative power sums; no partial fractions, no bricks).  a2_series_run.py n.
#   a2_barnes.py       V5 identity sin^5 z cot''''(z)/24 = V5(cos z); the limit formula (F) and |B|, beta.
#   a2_barnes2.py      Barnes integral on the line (n = 2, 3, 5; n = 1 only to 4e-9, see a2_barnes_fine.py).
#   a2_barnes_fine.py  Barnes integral for n = 1 with fine segments (agrees with the series to 3.7e-14).
#   a2_barnes_large.py Barnes integral for n = 12, 20, 50, 100 (half line, g(-y) = conj g(y)) vs (F).
#   a2_phi.py          phi on the exact breakpoint set (denominators from the coefficients, max 160), the
#                      integral int_{1/60}^inf phi dx/x^2, C2, and every piece of the Lean table.
#   a2_lemma19.py      exact Laurent data (log/exp at each pole), A_s, A0 (H_{k-h1}), the linear form vs the
#                      series, symmetry, Lemma 19 prime by prime, LaurentSupp/Int/Val (n = 1, 2).
#   a2_greedy.py       greedy piece counts;  a2_delta.py  log(Delta_n)/n with exact omega_p.
#   lean_eval_check.lean  kernel evaluation of omegaKP, omegaP, mj, PhiN, Dprod (cfgW, n = 1) against Python.
# Regenerate (python from a short working directory, with this directory copied there):
#   python a2_saddle.py > a2_saddle.log            (20 s)
#   for n in 1..9: python a2_series_run.py n       (n = 9: 9 min; concatenated in a2_series.log)
#   python a2_barnes.py > a2_barnes.log;  python a2_barnes2.py 1 2 3 5;  python a2_barnes_fine.py (8 min)
#   python a2_barnes_large.py 12 6; 20 5; 50 3.5; 100 2.6      (about 1 min each)
#   python a2_phi.py <PhiTable.lean> > a2_phi.log  (20 s)
#   python a2_lemma19.py 1; python a2_lemma19.py 2 (> a2_lemma19.log, 30 s)
#   python a2_greedy.py <PhiTable.lean>;  python a2_delta.py 1 2 5 10 20 40 80 160
import subprocess, sys
if __name__ == "__main__":
    table = sys.argv[1] if len(sys.argv) > 1 else "PhiTable.lean"
    for args in (["a2_saddle.py"], ["a2_phi.py", table], ["a2_lemma19.py", "1"], ["a2_lemma19.py", "2"],
                 ["a2_greedy.py", table], ["a2_barnes.py"], ["a2_series_run.py", "1"], ["a2_series_run.py", "2"]):
        print("$ python " + " ".join(args), flush=True)
        subprocess.run([sys.executable] + args)
