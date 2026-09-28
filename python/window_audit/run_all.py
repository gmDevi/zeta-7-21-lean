# Independent audit of the window formalisation (auditor's own code; it reuses neither
# python/window_mirror.py nor docs/window/{vz,zud_exact,zud5,certify_line,barnes_check}.py).
#   phi_indep.py     phi(x) = min_y phi0(x,y) on the Farey-160 intervals (a superset of all breakpoints),
#                    exact integer evaluation; int_{1/60}^inf phi dx/x^2, C2; checks EVERY piece of the
#                    Lean table (value on each Farey sub-interval and at each interior Farey point);
#                    phiSumQ(60,20) of the Lean table.
#   greedy.py        pieces needed by a greedy certificate for several C2hi.
#   saddle_indep.py  all 27 roots of the saddle polynomial, branches, f0, C0, omega/pi, f'', landscape
#                    u_lambda on the line Re tau = x*.
#   exact_indep.py   exact Laurent data by power sums + series exponential (not the Lean bricks), then a
#                    literal transcription of polyBrick/ratBrick/Gk/B, A_s, A0 (both harmonic cut-offs),
#                    Lemma 19 prime by prime, (8.10), (8.11), support, symmetry, residue sum, F_n.
#   random_cfg.py    the generic Stmts on 14 random/edge admissible configurations, n = 1, 2.
#   bricks_random.py BrickInt, BrickVal, Harmonic, OmegaPhi0 on random inputs.
#   pf_test.py       Stmt_PF literally (Rser vs partial fractions, exact, first 6 coefficients) at non-poles.
#   series_barnes.py Lean's Fn literally (sum_t [eps^{r-1}] Rser(t)) and the Barnes integral vs exact F_n.
#   asym.py          Stirling prefactor n^-13 A(tau) e^{n Phi_3}, leading term (F) vs contour values.
#   delta_growth.py  log(Delta_n)/n with exact omega_p.
# Regenerate all logs (sequential, ~25 min on one core; Windows or Linux python with mpmath, sympy, numpy):
#   python run_all.py <path to Zeta2Lean/Window/PhiTable.lean>
import subprocess, sys, time
table = sys.argv[1] if len(sys.argv) > 1 else "PhiTable.lean"
jobs = [
    ("phi_indep.log", ["phi_indep.py", table]),
    ("greedy.log", ["greedy.py", table]),
    ("saddle_indep.log", ["saddle_indep.py"]),
    ("bricks_random.log", ["bricks_random.py"]),
    ("exact_indep.log", ["exact_indep.py", "W", "1", "lean"]),
    ("exact_indep.log", ["exact_indep.py", "W", "2", "lean"]),
    ("exact_indep.log", ["exact_indep.py", "W", "3"]),
    ("exact_indep.log", ["exact_indep.py", "T3", "1", "lean"]),
    ("exact_indep.log", ["exact_indep.py", "T3", "2", "lean"]),
    ("exact_indep.log", ["exact_indep.py", "T3", "3"]),
    ("random_cfg.log", ["random_cfg.py", "7"]),
    ("pf_test.log", ["pf_test.py", "T3", "1"]),
    ("pf_test.log", ["pf_test.py", "W", "1"]),
    ("pf_test.log", ["pf_test.py", "(3, 9, 25, [1, 1, 10, 10, 10, 10, 10, 10, 10])", "2"]),
    ("pf_test.log", ["pf_test.py", "(5, 9, 18, [1, 2, 3, 4, 4, 4, 4, 4, 4])", "1"]),
    ("barnes_W123.log", ["series_barnes.py", "barnes", "W", "1,2,3"]),
    ("series_W1.log", ["series_barnes.py", "series", "W", "1", "700", "1300"]),
    ("asym.log", ["asym.py", "1,2,3,4,5,6,7,8,9,12,20,50,100"]),
    ("delta_growth.log", ["delta_growth.py", "1,2,3,5,10,20,40,80,160,320,640"]),
]
opened = set()
for log, args in jobs:
    t0 = time.time()
    mode = "a" if log in opened else "w"
    opened.add(log)
    with open(log, mode, encoding="utf-8") as fh:
        fh.write("$ python " + " ".join(args) + "\n"); fh.flush()
        subprocess.run([sys.executable] + args, stdout=fh, stderr=subprocess.STDOUT)
        fh.write("[%.0f s]\n" % (time.time() - t0))
    print(log, args, "%.0f s" % (time.time() - t0), flush=True)
