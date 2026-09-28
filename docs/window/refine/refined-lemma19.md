# Refined Lemma 19 (per-pole bound) for Zudilin's §8 forms, the constant C₂′, and the {ζ(7),…,ζ(21)} margin

Track `refined-lemma19` (ingredient H′ of `docs/proof.md`; not used by the Lean proof), written by an AI prover agent on
2026-09-25. Research-session paths were replaced by the paths of this repository; only some of the scripts and data
named below are included (see `README.md` in this folder). Labels: **PROVED** (written out here), **CERTIFIED** (exact rational arithmetic and/or outward-rounded interval arithmetic,
script named), **COMPUTED-EXACT** (exact integers by multimodular CRT), **NUMERICAL**.

## 0. Results

| # | statement | status | where |
|---|---|---|---|
| T1 | Per-pole bound (all odd r ≥ 3, all admissible h, every prime p with p² > h₀): p^{e_p} kills every denominator of c₀, c_r, …, c_{q−1}, with e_p = max(0, max_k E_k) (general poles: the probe's bound; "flat" poles: a sharper brick-wise bound) | PROVED | §2 |
| T4 | log Δ′ₙ = C₂′ n + o(n) (PNT), Δ′ₙ ∣ Δₙ, C₂′ = ∫₀^∞ Ψ_REF(1/u) du = C₂ − G, with G an explicit rational number | PROVED | §3 |
| N1 | η₀ = 160 configuration of docs/window/proof.md: **G = 18 exactly**, **C₂′ = 729.0513057896742841981284469**, **C₀ − C₂′ ∈ [21.66038904427002948382, 21.66038904427002948384]** (was 3.66) | CERTIFIED | §4 |
| N2 | Re-optimised q = 23 (Lemma 20 inputs re-certified): η₀=160, η=(45,…,53,53,…,66): margin **35.5137959249**; η₀=179, η_j = 54+j: margin **52.2993840655** | CERTIFIED | §6 |
| V | Refined bound vs TRUE denominators: 14 configurations (r=3,5; q=13,21,23), 266 (configuration, n) instances (n = 1 … 700), **218,581 (n,p) pairs, 0 violations**; equality at 94–99 % of large primes | COMPUTED-EXACT | §5 |
| Q | q = 21 ({7,…,19}) stays negative: best refined margin −28.0 (staircase η₀=146), TRUE denominators ≈ −24.5 there | NUMERICAL | §6.3 |

## 1. Setting (Zudilin, JTNB 16 (2004), (8.1)–(8.9))

Odd r ≥ 3, odd q ≥ r+4, integers 1 ≤ h₁ ≤ … ≤ h_q < h₀/2 with Σh_j ≤ h₀(q−r)/2. I_j := [h_j, h₀−h_j]; K := I_{r+1} ∩ ℤ.
With N_h := ∏_{j>r}(h₀−2h_j)! / ∏_{j≤r}(h_j−1)!², Zudilin's brick form (8.7) reads

  N_h R(t) = (h₀+2t) · ∏_{j≤r} P_j(t) P′_j(t) · ∏_{j>r} Q_j(t),
  P_j = (t+1)_{h_j−1}/(h_j−1)!,  P′_j = (t+h₀−h_j+1)_{h_j−1}/(h_j−1)!,  Q_j = (h₀−2h_j)!/∏_{l∈I_j}(t+l).

**Poles.** R has degree ≤ −2 (8.3). At t = −k the denominator vanishes to order #{j : k ∈ I_j}, the numerator to order
r·[1≤k≤h₀−1] + [2k=h₀]; as I_j ⊂ [1,h₀−1] and I₁ ⊃ … ⊃ I_q, the poles are exactly the k ∈ K, of order
o_k = #{j>r : k∈I_j} − [2k=h₀] ≥ 1. Hence N_hR(t) = Σ_{k∈K} Σ_{i=1}^{o_k} a_{i,k}(t+k)^{−i} with
a_{i,k} = [u^{o_k−i}] g_k(u), g_k(u) := N_hR(u−k)·u^{o_k} (analytic at 0), G₀(k) := g_k(0)/N_h.

**The linear form.** R has a zero of order r at t = −1,…,−(h₁−1), so the sum may start at t = 1−h₁ (Zudilin (8.6)); for
r ≥ 3 everything converges absolutely and (1/(r−1)!)(d/dt)^{r−1}(t+k)^{−i} = w_i (t+k)^{−(i+r−1)}, w_i = C(i+r−2, r−1)
(r odd). With H_s(N) = Σ_{l≤N} l^{−s} and k−h₁ ≥ 0:

  F̃ₙ = c₀ + Σ_{s=r}^{q−1} c_s ζ(s),  c_s = Σ_k w_{s−r+1} a_{s−r+1,k},  c₀ = −Σ_k Σ_{i=1}^{o_k} w_i a_{i,k} H_{i+r−1}(k−h₁).   (1.1)

(Zudilin's Lemma 19 shows c_r = 0 and c_s = 0 for even s; not needed for denominators.)

## 2. The per-pole bound (PROVED)

For a prime p with p² > h₀ and k ∈ K put V_k := v_p(g_k(0)) = v_p(N_hG₀(k)), ν := v_p(N_h),
far_k := [k−h₁ ≥ p], flat_k := [k−p < h_{r+1} and k+p > h₀−h_{r+1}] (no l ∈ K∖{k} with l ≡ k mod p), and

  E_k := o_k+r−1−V_k (far, not flat);   o_k−1−V_k (near, not flat);
  E_k := o_k+r−1−max(V_k, ν) (far, flat);  min(o_k−1−V_k, −ν) (near, flat).

**Theorem 1.** Every coefficient c ∈ {c₀, c_r, …, c_{q−1}} satisfies v_p(c) ≥ −e_p^{BPP}, e_p^{BPP} := max(0, max_{k∈K} E_k).
Dropping the flat case gives the (weaker) bound e_p^{PP} = max(0, max_k [L_k − V_k]), L_k = o_k+r−1 (far) or o_k−1 (near):
this is exactly the probe's per-pole bound (window-19-probe/notes.md §3.1), now proved.

**Lemma A (Taylor coefficients, general k).** For every m ≥ 0: v_p([u^m] g_k) ≥ V_k − m.
*Proof.* g_k(u) = g_k(0) · (1+2u/(h₀−2k))^{[2k≠h₀]} · ∏_{l≠k}(1+u/(l−k))^{e_l}, e_l ∈ ℤ the net exponent of (t+l) in N_hR
(for 2k = h₀ the factor (h₀+2t) = 2(t+k) is part of u^{o_k}). Each factor (1+u/d)^e (e ∈ ℤ, 0 < |d| ≤ h₀ < p², so
v_p(d) ≤ 1) has u^m-coefficient C(e,m)d^{−m} with valuation ≥ −m (C(e,m) ∈ ℤ also for e < 0); p is odd, so the same holds
for 2/(h₀−2k). The property "v_p([u^m]·) ≥ −m for all m" is stable under products. ∎

**Lemma B (flat k).** If flat_k then v_p([u^m] g_k) ≥ max(V_k − m, ν) for every m ≥ 0.
*Proof.* Write g_k = ∏_b b(u) over the bricks at t = u−k: B₀ = (h₀−2k)+2u (or the constant 2 if 2k = h₀),
P̃_j(u) = ∏_{l=1}^{h_j−1}(u+l−k)/(h_j−1)!, P̃′_j likewise, Q̃_j(u) = (h₀−2h_j)!/∏_{l∈I_j∖{k}}(u+l−k).
Claim: each brick satisfies v_p([u^m]b) ≥ max(ν_b − m, −f_b), where ν_b = v_p(b(0)) and
 * B₀: f = 0 (coefficients h₀−2k, 2, 0, 0, …; v_p(h₀−2k) ≤ 1 since |h₀−2k| < p²);
 * P̃_j, P̃′_j: f_j = v_p((h_j−1)!). Indeed [u^m]P̃_j = e_{N−m}(d)/N! (N = h_j−1, d_l = l−k); if c of the d_l are divisible
   by p (each exactly once, |d_l| < p²), every product of N−m of them contains ≥ c−m such factors, so
   v_p ≥ max(0, c−m) − f_j = max(ν−m, −f_j) because ν = c − f_j;
 * Q̃_j: f = −ν_{Q_j} with ν_{Q_j} = v_p((h₀−2h_j)!): flatness and I_j ⊂ K make every l−k (l ∈ I_j∖{k}) a p-unit, so
   ∏(1+u/(l−k))^{−1} has p-integral coefficients and v_p([u^m]Q̃_j) ≥ ν_{Q_j} = max(ν_{Q_j}−m, ν_{Q_j}).
Product rule: if v_p(A_i) ≥ max(α−i, α′) and v_p(B_j) ≥ max(β−j, β′) (α ≥ α′, β ≥ β′), then
v_p([u^m]AB) ≥ min_{i+j=m} [max(α−i,α′) + max(β−j,β′)] ≥ max(α+β−m, α′+β′). Induction over the bricks gives
v_p([u^m]g_k) ≥ max(Σν_b − m, −Σf_b) = max(V_k − m, ν), since −Σ_b f_b = Σ_{j>r}v_p((h₀−2h_j)!) − 2Σ_{j≤r}v_p((h_j−1)!) = v_p(N_h). ∎

**Lemma C.** For 0 ≤ N < p²: v_p(H_s(N)) ≥ −s·[N ≥ p]. (Only l = p, 2p, … < p² have v_p(l) = 1.) Here N = k−h₁ < h₀.

*Proof of Theorem 1.* Put A_k(m) := V_k − m, or max(V_k−m, ν) if flat_k; then v_p(a_{i,k}) ≥ A_k(o_k−i) (Lemmas A, B) and
v_p(w_i) ≥ 0. By (1.1) and Lemma C, v_p(c₀) ≥ −max_k max_{1≤i≤o_k}[(i+r−1)far_k − A_k(o_k−i)] and
v_p(c_s) ≥ −max_k max_i [−A_k(o_k−i)]. Evaluating the inner maxima: non-flat far: (i+r−1) − V_k + o_k − i = o_k+r−1−V_k;
non-flat near: max_i(o_k−i−V_k) = o_k−1−V_k; flat far: max_i min(o_k+r−1−V_k, i+r−1−ν) = o_k+r−1−max(V_k,ν) (at i=o_k);
flat near: max_i min(o_k−i−V_k, −ν) = min(o_k−1−V_k, −ν). In each case the c_s-maximum is ≤ E_k. ∎

**Corollary 1 (Δ′ₙ).** Let e_p^{L19} be Zudilin's exponent (v_p of D_{m₁}^r D_{m₂}⋯D_{m_{q−r}}Φₙ^{−1}) and
e_p := min(e_p^{L19}, e_p^{PP}, e_p^{BPP}) for p² > h₀, e_p := e_p^{L19} otherwise. Then Δ′ₙ := ∏p^{e_p} divides Δₙ and
Δ′ₙF̃ₙ ∈ ℤ + ℤζ(r+2) + … + ℤζ(q−2) (Lemma 19 for the small primes and the vanishing coefficients; Theorem 1 for p² > h₀).
Remark: Lemma 19 is not even needed for small p: the same proof with v_p(d) ≤ λ := ⌊log_p h₀⌋ and Kummer's bound on the
non-pole Q-values gives v_p(c) ≥ −(3q−2r−1)λ for every p, which contributes O(√n) to log Δ′ₙ.

## 3. Asymptotics (PROVED)

Now h₀ = η₀n+2, h_j = η_jn+1 (η sorted), x := n/p, y := (k−1)/p. Zudilin's 1-periodic
φ₀(x,y) = Σ_{j≤r}(⌊y⌋+⌊η₀x−y⌋−⌊y−η_jx⌋−⌊(η₀−η_j)x−y⌋−2⌊η_jx⌋) + Σ_{j>r}(⌊(η₀−2η_j)x⌋−⌊y−η_jx⌋−⌊(η₀−η_j)x−y⌋), φ(x) := min_y φ₀.

**Lemma D (o_k-cancellation).** For p² > h₀, k ∈ K: o_k − V_k = q − r − φ₀(x,y) − δ_k, δ_k := [2k=h₀] + v_p(h₀−2k)[2k≠h₀];
ν = ν(x) := Σ_{j>r}⌊(η₀−2η_j)x⌋ − 2Σ_{j≤r}⌊η_jx⌋.
*Proof.* With v_p(N!) = ⌊N/p⌋ (N < p²), the brick values give V_k = Σ_{j≤r}[⌊(k−1)/p⌋+⌊(h₀−1−k)/p⌋−⌊(k−h_j)/p⌋−⌊(h₀−h_j−k)/p⌋
−2⌊(h_j−1)/p⌋] + Σ_{j>r}[⌊(h₀−2h_j)/p⌋ − χ_j] + v_p(h₀−2k)[2k≠h₀], where χ_j = ⌊(k−h_j)/p⌋+⌊(h₀−h_j−k)/p⌋ if k ∈ I_j and,
by ⌊−s/p⌋ = −⌊(s−1)/p⌋−1 (Zudilin (7.5)), the same plus 1 if k ∉ I_j (value (h₀−2h_j)!(h_j−k−1)!/(h₀−h_j−k)! resp. its mirror).
So V_k = φ_{k,p} − #{j>r: k∉I_j} + v_p(h₀−2k)[2k≠h₀] with Zudilin's φ_{k,p} = φ₀(n/p,(k−1)/p) (8.9), and
#{j>r: k∉I_j} = q−r−o_k−[2k=h₀]. ∎ (Checked on every pole for 218,581 (n,p) pairs, `check_true.py`.)

Hence E_k^{PP} = q−1−r[k−h₁<p]−φ₀−δ_k: **the pole order cancels**, and Lemma 19's per-k exponent (q−1)−φ_{k,p} is
recovered except that near poles (k−h₁ < p) save r and δ_k is dropped. In the continuum, with
far = [y > 1+η₁x], flat = [(η₀−η_{r+1})x−1 < y < η_{r+1}x+1], o(x,y) = #{j>r: η_jx < y < (η₀−η_j)x}:

  E_PP = q−1−r(1−far)−φ₀,  E_BPP = E_PP (not flat), min(q−1−φ₀, o+r−1−ν) (flat, far), min(q−r−1−φ₀, −ν) (flat, near),
  Ψ_X(x) := max(0, max of E_X over the open y-cells of (η_{r+1}x, (η₀−η_{r+1})x)),
  Ψ_L19(x) := Dcount(1/x) − [1/x ≤ m_{q−r}]φ(x),  Dcount(u) = r[u≤m₁] + Σ_{j≥2}[u≤m_j]  (Zudilin's continuum),
  Ψ_REF := min(Ψ_L19, Ψ_PP, Ψ_BPP),  C₂ = ∫₀^∞Ψ_L19(1/u)du,  **C₂′ := ∫₀^∞ Ψ_REF(1/u) du**.

**Lemma E (grid vs cells).** If p² > h₀, p > η₀, p ∤ n then e_p^X ≤ Ψ_X(n/p) for X ∈ {L19, PP, BPP}, with equality
except for O_η(1) primes.
*Proof.* All functions of y entering E_X jump only on lines y = cx+m with integer slope c ∈ S₊ = {0, η_j} (floors
⌊y−cx⌋, o-entry y ≥ η_jx, far, flat's upper end, left end of K: value at the jump = right limit) or c ∈ S₋ = {η₀, η₀−η_j}
(floors ⌊cx−y⌋, o-exit, flat's lower end, right end of K: value = left limit); S₊ ∩ S₋ = ∅ since η_j < η₀/2 < η₀−η_i. Two
lines of different slopes never meet on the grid (1/p)ℤ: (c−c′)n = (m′−m)p is impossible for p ∤ n, 0 < |c−c′| ≤ η₀ < p.
So at every grid point all jumping terms agree with one adjacent open cell inside the range, and E_X(grid) ≤ E_X(cell)
(δ_k ≥ 0 lowers E_PP; at 2k = h₀ both o_k and V_k shift so that E_BPP drops by ≥ 0). For L19, φ_p = min over the grid
≥ φ(x) and Zudilin's discrete m_j equal m_jn exactly. Equality: every cell of length ≥ 3/p contains two grid points,
at most one with p ∣ h₀−2k (one residue class; cells are shorter than 1); cells of length ≤ 2/p need
p ∣ (c−c′)n ∓ t (t ∈ {1,2}), and each of these O(η₀) nonzero integers has ≤ 2 prime factors > √h₀ for n large. ∎
(Numerically, `compare_cont.py`: e_p ≤ Ψ(n/p) at every tested prime; ≤ 1 exception to equality per n; n = 7…150, 3 configurations.)

**Theorem 4.** log Δ′ₙ = C₂′ n + o(n), and C₂′ = C₂ − G, G := ∫(Ψ_L19 − Ψ_REF)(1/u) du, supported in
u ∈ [u₀, m₁], u₀ := ½min(η₀−η_{r+1}−η₁, η₀−2η_{r+1}); G is a finite sum of (integer) × (difference of rationals).
*Proof.* Small primes p ≤ √h₀ contribute ≤ (q−1)π(√h₀)log h₀ = O(√n); p ∣ n, p ≤ η₀ and the O(1) exceptions of Lemma E
contribute O(log n). For the rest e_p = Ψ_REF(n/p) (≤ is all the irrationality proof needs). Ψ_REF(1/u) ≤ q−1 is a step
function with finitely many steps on every [ε, m₁] (breakpoints a/d, d a difference of slopes), vanishes for u > m₁, so the
PNT θ(X) ∼ X gives Σ_p Ψ_REF(n/p) log p = n∫Ψ_REF(1/u)du + O(εn) + o(n). Support of G: for u ≤ u₀ there are no flat cells
((η₀−2η_{r+1})x ≥ 2) and the far part (1+η₁x, (η₀−η_{r+1})x) has length ≥ 1, so Ψ_PP = Ψ_BPP = max(0, q−1−φ) = Ψ_L19
(φ ≤ q−1 checked: max φ = 16, 17, 16, 9 for the four configurations of §4/§6; the identity Ψ_REF = Ψ_L19 for u < u₀ was
also spot-checked at 1,600 random rational x); for u > m₁ all vanish. ∎
(Equality in Theorem 4 uses that Zudilin's continuum is exact on (m₀, m_{q−r}]; this holds whenever m_{q−r} = m₀, true for
every configuration below. In general only "≤" is claimed, which suffices.)

## 4. Exact C₂′ and the certified margin for the η₀ = 160 configuration (CERTIFIED)

`c2exact.py` enumerates all candidate x-breakpoints a/d (d any difference of y-slopes, η_j, η₀−2η_j, m_j), evaluates φ and
(Ψ_L19, Ψ_PP, Ψ_BPP) exactly (integer floors) at every interval midpoint, re-checks constancy at two random rational
interior points of every interval (assertion), and integrates exactly: ∫ v dx/x² = v(1/x₀ − 1/x₁). The tail
∫₁^∞ φ(x)dx/x² = Σ v[ψ(1+x₁)−ψ(1+x₀)] is enclosed in mpmath.iv (200 bits) via ψ(1+x) = ψ(41+x) − Σ_{k≤40}1/(k+x) and the
Stirling series with 16 exact Bernoulli terms plus the enveloping remainder |B₃₄|/(34z³⁴) (DLMF 5.9.16).
Control: Zudilin's Theorem 3 (r=3, η₀=91): C₂ = 226.2494426638866717… (paper: 226.24944266), G = 14/3, margin 1.33 → 6.00.

η₀ = 160, η = (47⁴,48,50²,51,…,66): 793 φ-pieces; **C₂ = 747.05130578967428419812844694** (= docs/window/proof.md value).
Gain pieces (u = p/n; Ψ_L19 → Ψ_REF): [46,47] 14→13; [51,52] 6→5; [52,53] 7→5; [53,160/3] 7→4; [56,57] 9→8; [57,58] 9→7;
[58,59] 10→7; [59,60] 10→6; [60,61] 8→7; [61,62] 7→6 (flat); [62,63] 6→5 (flat); zero elsewhere. **G = 18 exactly**
(PP alone: 16). **C₂′ = 729.05130578967428419812844694**; with C₀ ∈ [750.71169483394431368195842, …96256]
(docs/window/proof.md `certify_q23_160.json`): **C₀ − C₂′ ∈ [21.660389044270029483829, 21.660389044270029483835]**
(relative 2.97 %; was 3.6604 = 0.49 %). `margins.py` → `margins.json`.
The gain pieces coincide with the measured TRUE slack steps of window-19-probe (stepfit_q23: 1 on [46,47], 1/2/3 on
[51,53.35], 1/2/3/4 on [56,60], 1 on [60,63]); not captured (second order): 1 on [53.35,54], [25.5,27], [23,23.5] and
short pieces below u = 18 (≈ 5.1 of the TRUE 23.3).

## 5. Verification against TRUE denominators (COMPUTED-EXACT)

TRUE exponent of p = max(0, e_L − slack) from the GPU multimodular engine (window-19-probe `mm_engine.py`: exact integers
Δₙc_s by CRT, extra-prime check `crt_ok` true in every run). `check_true.py` recomputes Lemma 19 independently (always equal
to the engine's e_L), computes PP, BPP, REF from factorials (not from Lemma D), tests EVERY prime ≤ h₀+2 (small primes
included) and verifies Lemma D on all poles.

| config (r, q, η₀) | n | (n,p) pairs | violations | REF = TRUE (large p) |
|---|---|---|---|---|
| q23: 5,23,160 (the proof) | 1…60, 80, 100, 130, 160, 200 | 50,549 | 0 | 96.0 % |
| fix160: 5,23,160 (re-optimised) | 1…10, 15, 20, 30, 40, 60 | 4,966 | 0 | 96.5 % |
| stair179: 5,23,179 (re-optimised) | 1…12, 15, 20, 25, 30, 40, 50, 60, 80 | 9,489 | 0 | 98.8 % |
| s172: 5,23,172 | 10, 20, 30, 40 | 2,323 | 0 | 98.5 % |
| thm3: 3,13,91 (Zudilin Thm 3) | 1…40, 50, 60, 80 | 13,485 | 0 | 94.5 % |
| q21 η*: 5,21,146 | 1…80, 90…300 (11), 450, 700 | 107,456 | 0 | 95.9 % |
| best1, st48, g45, e144, sym55 (q=21 probe spots) | 30…150 | 21,666 | 0 | 78–97 % |
| q21 staircases η₀=146, 179 | 20…80 | 8,647 | 0 | 96.5–97 % |
| **total** | 266 instances | **218,581** | **0** | |

Large-prime savings per n over Lemma 19 (refined vs TRUE, `true_large.py`): η₀=160: 18.0 (continuum 18) vs 23.3;
fix160: ≈42 (42) vs ≈46.5; stair179: ≈137.5 (138.5) vs ≈139.5; thm3: ≈4.7 (14/3).

## 6. Re-optimisation for q = 23 under the refined arithmetic

`opt_ref.py` (coordinate/pair/block descent; objective C₀ − C₂′; hard constraint: the zero τ_d of P with Im > 0 and max
Re lies on branch λ = r−2 = 3 and η₀−η₁ < Re τ_d < η₀) and `scan_fam.py` (staircases η_j = a+⌈cj⌉). All constants are
homogeneous of degree 1 in (η₀, η), so margin/η₀ is the figure of merit (0.023 for the proof's η under Lemma 19).

| configuration | C₀ | C₂ (L19) | G | C₂′ | margin C₀−C₂′ | per η₀ |
|---|---|---|---|---|---|---|
| η₀=160, (47⁴,48,50²,51,…,66) (proof) | 750.7116948339 | 747.0513057897 | 18 | 729.0513057897 | **21.6603890443** | 0.135 |
| fix160: η₀=160, (45,46,…,53,53,54,…,66) | 750.1035506302 | 756.5897547054 | 42 | 714.5897547054 | **35.5137959249** | 0.222 |
| stair179: η₀=179, η_j = 54+j (55,…,77) | 732.3010308716 | 818.5016468062 | 277/2 | 680.0016468062 | **52.2993840655** | 0.292 |

(all CERTIFIED: C₂′ by `c2exact.py`, C₀ and every Lemma-20 input by docs/window/proof.md's `certify_line.py` run on
`zud5.py` here: `certify_fix160.log`, `certify_stair179.log` = ALL CERTIFIED: Rouché root, branch λ=3, Re f″ > 0
(0.2725 / 0.2417), ω/π ∉ ℤ (distance 0.467 / 0.214), (M) A > y*, (T), (D), gaps (G), subdominant λ=1: sup u₁ ≤ Re f₀ − 4.12 / − 6.56.)
The Lemma 20 proof of docs/window/proof.md §3 is configuration-independent given these certified items (§3.3 needs only an
admissible line; (L1)–(L3) are analytic), so both new configurations give the theorem with the new margins.
Lemma 19 alone would give −6.49 and −86.20 for them: the optimum moved to staircases where Zudilin's worst-case charge at
the top of the D-range is most wasteful, and there the refined bound is almost exact (99 % of the TRUE saving).

### 6.3 q = 21 ({7,…,19}): still out of reach (NUMERICAL + COMPUTED-EXACT)
Staircase scan (η₀ ∈ {130,146,160,179,200}) and two descents: best refined margin −27.98 (η₀ = 158, η_j = 47+j) /
−28.13 (η₀ = 146, η_j = 39+j), about −0.19 per η₀. TRUE denominators (engine, n = 20…80): large-prime saving ≈ 36 at
η₀=146 (L19 margin −60.46 ⇒ TRUE margin ≈ −24.5) and ≈ 114 at η₀=179 (L19 −141.5 ⇒ ≈ −27.5). No denominator lemma can
rescue these configurations.

## 7. Limitations
1. Asymptotic via the PNT (no effective n₀), exactly as Zudilin's Proposition 5 and docs/window/proof.md.
2. The small-prime part and the vanishing of c_r and even c_s are Zudilin's Lemma 19 (or the crude self-contained bound of the Remark).
3. Second-order (inter-pole) cancellations are not used: η₀=160 keeps ≈ 5.3 of the TRUE 23.3 unused.
4. Optimisation is heuristic (local descents plus a staircase scan); only the three tabulated configurations are certified.

## 8. Files (work dir)
`rl19.py` (per-prime L19/PP/BPP, Lemma D check), `check_true.py` → `check_*.jsonl/log`, `true_large.py`, `compare_cont.py`,
`c2exact.py` → `c2exact_{q23_160,fix160,stair179,thm3}.json`, `*_refpieces.txt`, `margins.py` → `margins.json`,
`opt_ref.py` → `opt_q23_*.{log,jsonl}`, `opt_q21_*`, `scan_fam.py` → `scan_stair23/21.*`, `zud5.py` (configs for
certify_line.py) → `certify_{fix160,stair179}.{log,json}`, engine data `mm_{fix160,stair179,s172,thm3,q21stair146,q21stair179}.jsonl`.
