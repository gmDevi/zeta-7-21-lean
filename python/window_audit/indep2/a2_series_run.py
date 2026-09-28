import sys, time, mpmath as mp
import a2_series as S
n = int(sys.argv[1]); T = 700 * n + 300; dps = 60 + 25 * n
t0 = time.time()
F, ml, last = S.Fn(n, T, dps)
mp.mp.dps = dps
print("n=%d T=%d dps=%d log|F|=%s sign=%s logmax=%s loglast=%s F=%s  (%.0fs)" % (n, T, dps, mp.nstr(mp.log(abs(F)), 22), '+' if F > 0 else '-', mp.nstr(ml, 8), mp.nstr(mp.log(abs(last)), 8), mp.nstr(F, 25), time.time() - t0))
