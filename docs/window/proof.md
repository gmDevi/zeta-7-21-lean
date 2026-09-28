# At least one of ζ(7), ζ(9), ζ(11), ζ(13), ζ(15), ζ(17), ζ(19), ζ(21) is irrational

> **Editorial note (2026-09-26).** This is the first version of the informal proof (research direction
> `window-21-proof`, written on 2026-09-25 by AI agents of a separate research workflow; see `formalization.yaml`,
> `automation`). It is superseded by `docs/proof.md`, which the Lean
> development formalises (its route R2); this version is route R4 of `docs/proof.md` §6 and uses the saddle-point
> analysis (steps B–G below), which the Lean proof does not use. Its body is unchanged, except that paths of the
> research session were replaced by the paths of this repository or by a description; the scripts named here are in
> `docs/window/` unless stated otherwise.

Status labels: PROVED (published or elementary, written out here), CERTIFIED (interval arithmetic, script named),
COMPUTED (high-precision, not certified), NUMERICAL.

## 0. Result and the status of every step

**Theorem.** At least one of the eight numbers ζ(7), ζ(9), …, ζ(21) is irrational.

Route: Zudilin, JTNB 16 (2004) §8, general-η very-well-poised forms with r = 5 derivatives (they kill ζ(3), ζ(5) and, by
the well-poised symmetry, all even zetas), q = 23, η₀ = 160, η = (47,47,47,47,48,50,50,51,52,…,66). Zudilin's Proposition 5
needs two inputs: Lemma 19 (arithmetic, proved there for every odd r) and Lemma 20 (asymptotics, proved there only for
r = 3; "remains true for odd r > 3", p. 286, never executed). This note supplies Lemma 20 for r = 5 and this η.

| step | statement | status | where |
|---|---|---|---|
| A | Barnes representation F̃ₙ = (N_h/2πi)∫_{M+iℝ} G(t)V₅(cos πt)dt, −h₁ < M < 0 | PROVED (§3.1); validated to 1e−13 against exact F̃ₙ, n ≤ 9 (NUMERICAL, `barnes_check.py`) | §3.1, §5 |
| B | branch split V₅(y) = (y³+2y)/3, F̃ₙ = (N_h/π)[(1/24) Im J₃ + (11/24) Im J₁] | PROVED (sympy check of V₅) | §3.2 |
| C | Stirling phase Φ_λ = f − iπλτ on the line Re τ = x*, uniform O(1/n) remainder | PROVED (explicit bound) | §3.3 |
| D | dominant saddle τ₃ = 159.35641805… + 8.39371237…i, f′(τ₃) = 3πi, Re f″(τ₃) > 0 | CERTIFIED (`certify_line.py` (R),(S)) | §3.4 |
| E | landscape on the line: u₃ has its unique global max at y*, u₁ ≤ −754.6 | PROVED (monotonicity, (L1)–(L3)) + CERTIFIED ((D),(G),(K)) | §3.5 |
| F | Lemma 20 (r=5, this η): limsup (1/n)log\|F̃ₙ\| = −C₀ = −750.7116948339, F̃ₙ ≠ 0 on a positive-density set | PROVED modulo D, E (saddle-point theorem) | §3.6 |
| G | ω/π = Im f₀(τ₃)/π = −466.6133574734 ∉ ℤ (distance ≥ 0.3866) | CERTIFIED | §3.6 |
| H | Lemma 19: Δₙ F̃ₙ ∈ ℤ + ℤζ(7) + … + ℤζ(21), log Δₙ = C₂ n + o(n), C₂ = 747.0513057897 | PROVED (Zudilin, all odd r; PNT ⇒ o(n) ineffective); m_j exact, φ-integral COMPUTED (50 digits, two implementations) | §2 |
| I | C₀ − C₂ = +3.6603890443 > 0 ⇒ theorem | PROVED given A–H | §4 |

Nothing in the proof is new in method: it is Zudilin's own r = 3 argument (JTNB Lemma 20 ⇐ Izv. 2002 Lemmas 2–6) and the
Rivoal–Zudilin 2018 multi-branch pattern, made rigorous for one configuration by certified inequalities. What is new is the
statement (§7): no window starting at ζ(7) shorter than {7,…,35} is in the literature.

## 1. The linear forms (JTNB 2004, (8.2)–(8.7))

Odd q ≥ r+4 and odd r; here r = 5, q = 23. For n ≥ 1 put h₀ = η₀n + 2 and h_j = η_jn + 1 (j = 1..q), so that
h₁ ≤ … ≤ h_q < h₀/2 and Σh_j = 1272n + 23 ≤ h₀(q−r)/2 = 1440n + 18 (condition (8.1)). Define

  R(t) = (h₀+2t)·(t+1)_{h₀−1}^r / ∏_{j=1}^{q}(t+h_j)_{h₀+1−2h_j}
       = (h₀+2t)·Γ(h₀+t)^r/Γ(1+t)^r · ∏_j Γ(h_j+t)/Γ(1+h₀−h_j+t),   deg R = 1 − r − q + (r−q)h₀ + 2Σh_j = −336n − 4,

  F̃ₙ := N_h · (1/(r−1)!) Σ_{t≥0} R^{(r−1)}(t),   N_h := ∏_{j>r}(h₀−2h_j)! / ∏_{j≤r}(h_j−1)!².

R has zeros of order r at t = −1, …, −(h₀−1) (outside the pole ranges [−(h₀−h_j), −h_j]) and R(−t−h₀) = −R(t) (8.5).
`zud_exact.py` evaluates F̃ₙ exactly (partial fractions) and confirms that only ζ(7), ζ(9), …, ζ(21)
occur (ζ(5), ζ(6), ζ(8), … coefficients vanish to working precision, `exact_r5_q23_n9.jsonl`, n ≤ 9).

## 2. Arithmetic: Lemma 19 and C₂ (PROVED by Zudilin for all odd r; constants recomputed here)

**Lemma 19 (JTNB p. 281).** F̃ₙ ∈ ℚ + ℚζ(r+2) + ℚζ(r+4) + … + ℚζ(q−2), and with m₀ = max{h_r−1, h₀−2h_{r+1}},
m_j = max{m₀, h₀−h₁−h_{r+j}} (j = 1..q−r), D_m = lcm(1..m), and Φₙ the integer (8.8),

  Δₙ F̃ₙ ∈ ℤζ(q−2) + … + ℤζ(r+2) + ℤ,   Δₙ := D_{m₁}^r D_{m₂}⋯D_{m_{q−r}} · Φₙ^{−1}.

The proof (Leibniz rule + Lemmas 15–18 on the elementary bricks + the symmetry (8.5), which kills the even indices) does
not use r = 3 anywhere. Exact check (COMPUTED-EXACT, `zud_arith_check.py`, `arith_check_r5_q23.jsonl`):
at n = 1, 2, 3 the true denominators of the coefficients of F̃ₙ obey Lemma 19 prime by prime, with zero slack at some
primes (the lemma is tight).

Scaled by n: m = (63, 63, 62, 61, 60, 60, …, 60) (18 entries; m₁ = max(η₅, η₀−2η₆, η₀−η₁−η₆) = max(48, 60, 63)),
r m₁ + m₂ + … + m₁₈ = 315 + 186 + 840 = 1341 exactly. By the prime number theorem (Prop. 5 and its derivation, valid for
every odd r since the periodic function φ₀(x,y) carries r explicitly),

  log Δₙ = C₂ n + o(n),   C₂ = 1341 − ∫_{1/m₁₈}^{∞} φ(x) dx/x²,   φ(x) = min_y φ₀(x,y).

φ is piecewise constant on 2,644 rational intervals of [0, 1) (2,602 with nonzero value; φ ≥ 0 everywhere); the integral
equals Σ_pieces v·[ψ(1+x₁) − ψ(1+x₀)] plus the exact 1/x-part on [1/60, 1] (`vz.py`, a verifier's script, exact integer minimisation per piece; recomputed here with a
50-digit digamma tail): ∫ = 593.94869421032569…, so

  **C₂ = 747.0513057896743** (COMPUTED; three implementations agree: vz.py exact pieces, zud_engine.py 10⁶-point
  midpoint rule 747.054, the scout's exact-rational engine to 1e−9; vz.py reproduces Zudilin's Theorem 3 constant
  C₂ = 226.24944266 to all printed digits).

The o(n) comes from the PNT (θ(x) ~ x): the theorem is asymptotic in the same sense as Zudilin's.

## 3. Analytic part: Lemma 20 for r = 5 and this η

### 3.1 Proposition A (Barnes integral; PROVED)

Let K_r(t) := ((−1)^{r−1}/(r−1)!)·(d/dt)^{r−1}[π cot πt]. Near an integer k, π cot πt = 1/(t−k) + O(t−k), so
K_r(t) = (t−k)^{−r} + O(1) and Res_{t=k} K_r R = R^{(r−1)}(k)/(r−1)! whenever R is regular at k. For −h₁ < M < 0,

  (1/(r−1)!) Σ_{t≥0} R^{(r−1)}(t) = −(1/2πi) ∫_{M−i∞}^{M+i∞} K_r(t)R(t) dt.

Proof: integrate over the rectangle with vertices M ± iN, N+½ ± iN (N > h₀ an integer). Inside: the poles of K_r at
t = 0, 1, …, N (residues = the terms of the sum) and the negative integers k with M < k ≤ −1; at the latter R has a zero of
order r (k > −h₁, so k is outside every pole range of R) which cancels the pole of order r of K_r: no residue. On the three far sides R = O(N^{−2})
(deg R ≤ −2) and K_r is bounded away from the integers (it is a polynomial in cot πt, bounded on Re t = N+½ and on
|Im t| ≥ 1); the sides contribute O(N^{−1}) → 0. Orientation gives the minus sign. ∎

Write sin^r z · K-form: with cot_r(z) := ((−1)^{r−1}/(r−1)!) cot^{(r−1)}(z) one has sin^r(z)cot_r(z) = V_r(cos z), a
polynomial with V₃(y) = y, V₅(y) = (y³+2y)/3, V₇(y) = (2y⁵+26y³+17y)/45 (sympy, `barnes_check.py` header). Since
π/(sin(πt)Γ(1+t)) = −Γ(−t), K_r(t)R(t) = (−1)^r V_r(cos πt) G(t) with

  G(t) := (h₀+2t) Γ(h₀+t)^r Γ(−t)^r ∏_j Γ(h_j+t)/Γ(1+h₀−h_j+t),

so for r = 5:  **F̃ₙ = (N_h/(2πi)) ∫_{M−i∞}^{M+i∞} G(t) V₅(cos πt) dt.**  (A)

### 3.2 Branches (PROVED)

V₅(cos πt) = (1/24)(e^{3πit}+e^{−3πit}) + (11/24)(e^{πit}+e^{−πit}). Put J_λ := ∫_{M+iℝ} G(t)e^{−iπλt}dt. G(t̄) = conj G(t)
(real parameters) gives J_{−λ} = −conj(J_λ) on a vertical line, hence

  F̃ₙ = (N_h/π)·[ (1/24) Im J₃ + (11/24) Im J₁ ].   (B)

### 3.3 Stirling phase on a vertical line (PROVED)

Put τ := η₀ + t/n (so the sum's terms t ≥ 0 are τ ≥ η₀, the poles of R are the segments [η_j, η₀−η_j], the zeros fill
(0, η₀)), and t = n(τ−η₀). The Gamma arguments are nτ+2, n(η₀−τ), n(τ−η₀+η_j)+1, n(τ−η_j)+2, and in N_h: n(η₀−2η_j)+1,
nη_j+1. On a line Re τ = x with η₀−η₁ < x < η₀ (⇔ −h₁ < M < 0) all of them have positive real part ≥ n·min(x, η₀−x, x−η₀+η₁)
and |arg| ≤ π/2. Stirling with the standard remainder |log Γ(w) − (w−½)log w + w − ½log 2π| ≤ 1/(12|w|cos²(½arg w)) ≤ 1/(6|w|)
(DLMF 5.11.9–10 with N = 1) gives, uniformly on the line,

  N_h G(t) e^{−iπλt} = n^{−13} A(τ) e^{nΦ_λ(τ)} (1 + ρₙ(τ)),   |ρₙ(τ)| ≤ e^{15/n} − 1 = O(1/n)

(84 Gamma factors: 56 in G with |w| ≥ 0.6436 n contribute ≤ 56/(6·0.6436 n) = 14.5/n, 28 in N_h with |w| ≥ 28n contribute
≤ 0.17/n; the shifts a ∈ {1, 2} in Γ(nz+a) and the "+2" in h₀+2t add ≤ 0.3/n),

  Φ_λ(τ) := f(τ) − iπλτ,   f(τ) = rτ log τ + r(η₀−τ)log(η₀−τ) + Σ_j[(τ−η₀+η_j)log(τ−η₀+η_j) − (τ−η_j)log(τ−η_j)] + C_η,
  C_η = Σ_{j>r}(η₀−2η_j)log(η₀−2η_j) − 2Σ_{j≤r}η_j log η_j,
  A(τ) = (2π)^9 (2τ−η₀) τ^{15/2} (η₀−τ)^{−5/2} ∏_j (τ−η₀+η_j)^{1/2}(τ−η_j)^{−3/2} · ∏_{j>r}(η₀−2η_j)^{1/2} ∏_{j≤r} η_j^{−1}

(principal branches; the factor e^{iπλnη₀} = 1 because λη₀n is even). The n log n and the linear-in-n terms cancel exactly
because Σ_{j>r}(η₀−2η_j) − 2Σ_{j≤r}η_j = (q−r)η₀ − 2Ση = 336 = −[rη₀ − qη₀ + 2Ση]; the n-power is −14 from the Gamma
prefactors plus 1 from h₀+2t. |A(x+iy)| = O(|y|^{−17}) as |y| → ∞, so ∫|A|dy < ∞. The saddle equation f′(τ) = iπλ reads
τ^r∏(τ−η₀+η_j) = −(η₀−τ)^r∏(τ−η_j), i.e. P(τ) := (τ−η₀)^r∏_j(τ−η_j) − τ^r∏_j(τ−η₀+η_j) = 0 (r odd), and at a root of
branch λ, Φ_λ(τ_λ) = f(τ_λ) − τ_λ f′(τ_λ) = f₀(τ_λ) with Zudilin's f₀(τ) = rη₀log(η₀−τ) + Σ_j[η_j log(τ−η_j) − (η₀−η_j)log(τ−η₀+η_j)] + C_η.

### 3.4 The dominant saddle (CERTIFIED, `certify_line.py`, 130-bit mpmath.iv, log `certify_q23_160.log`)

P has integer coefficients and degree 27. All 27 roots (explore.py, 80 digits; branch λ = f′/(iπ)):
174.9196 (real, λ = −5, on the cut [η₀,∞)); 159.35642 ± 8.39371i (λ = ±3); 154.37513 ± 2.88062i (λ = ±1); seventeen roots on the
mirror line Re τ = η₀/2 = 80 (λ = ±7, ±9, …, ±21 and the real root τ = 80 with λ = 23; not saddles of any branch that
occurs, since only |λ| ≤ 3 = r−2 appears in V₅, and with Re f₀ = +54 … +1102 they would be irrelevant anyway); the images 0.6436 ± 8.394i, 5.6249 ± 2.881i and −14.92 under τ ↦ η₀−τ.
The r = 3 case of Zudilin (Thm 3 configuration) has the same picture (87.479 ± 3.328i dominant, mirror-line roots with
Re f₀ > 0), so nothing is anomalous.

(R) Rouché on the disk D(z₀, ρ), ρ = 1.24·10⁻²³: |P(z₀)| + ½ sup_D|P″| ρ² < |P′(z₀)| ρ, so exactly one zero τ₃ of P lies in D;
f′(D)/(iπ) ⊂ [3.0, 3.0] + i[−5.6·10⁻²⁴, 5.6·10⁻²⁴] and f′(τ₃)/(iπ) must be an odd integer ⇒ **f′(τ₃) = 3πi**:
  τ₃ = x* + iy*,  x* = 159.35641805379484…,  y* = 8.393712372068762…  (η₀−η₁ = 113 < x* < η₀ = 160: the line is admissible).
(S) f″(τ₃) = 0.272122458999 + 0.542987421932 i, **Re f″(τ₃) > 0**;  **C₀ := −Re f₀(τ₃) = 750.7116948339443** (width 4e−21);
  **ω/π := Im f₀(τ₃)/π = −466.6133574734306**, distance to ℤ ≥ 0.3866.
Also u(0) := Re f(x*) = −767.130018491 (value of every branch at the real axis crossing).

### 3.5 The landscape on the line Re τ = x* (PROVED + CERTIFIED)

Let u_λ(y) := Re Φ_λ(x*+iy) = Re f(x*+iy) + λπy. Then u_λ′(y) = λπ − Im f′(x*+iy) and, with a_j := x*−η₀+η_j ∈ [46.36, 65.36],
b_j := x*−η_j ∈ [93.36, 112.36] (0 < a_j < b_j because η_j < η₀/2), c := η₀−x* = 0.6436,

  Im f′(x*+iy) = r[arctan(y/x*) + arctan(y/c)] + Σ_j [arctan(y/a_j) − arctan(y/b_j)],
  Re f″(x*+iy) = r[h(x*) + h(c)] + Σ_j [h(a_j) − h(b_j)],   h(a) := a/(a²+y²).

(L1) y < 0: every arctan is negative and arctan(y/a_j) < arctan(y/b_j), so Im f′ < 0 and u_λ′ > λπ > 0 for λ ≥ 1:
     u_λ is increasing on (−∞, 0].
(L2) y > 0: the brackets are ≥ 0, so Im f′ ≥ r[arctan(y/x*) + arctan(y/c)], increasing in y. CERTIFIED (T): at Y_d = 55 the
     right side exceeds 3π; hence u₃′ < 0 and u₁′ < 0 on [55, ∞).
(L3) 0 ≤ y ≤ A := a₁ = 46.356: h is decreasing on [y, ∞) and a_j ≥ A ≥ y, so h(a_j) ≥ h(b_j); with the positive r-terms,
     Re f″ > 0, i.e. Im f′(x*+iy) is strictly increasing on [0, A], from 0 at y = 0 to the value 3π at y = y* = 8.394 < A
     (this is f′(τ₃) = 3πi). Hence Im f′ < 3π on [0, y*) and > 3π on (y*, A]. (Belt and braces: (M′) certifies Re f″ > 0 on
     [0, A] with minimum lower bound 0.089.)
(D)  CERTIFIED: Im f′(x*+iy) > 3π on [A, 55] (lower bound 14.25 > 9.42).

Consequently u₃ is strictly increasing on (−∞, y*] and strictly decreasing on [y*, ∞): **unique global maximum at y*, with
u₃(y*) = Re f₀(τ₃) = −C₀** ((V) checks the two enclosures overlap), and it is nondegenerate: u₃″(y*) = −Re f″(τ₃) < 0.
Quantitative gaps (G): u₃(y*±0.25) ≤ −C₀ − 0.0084, u₃(y*±1) ≤ −C₀ − 0.134, u₃(y*±2) ≤ −C₀ − 0.529, u₃(y*±5) ≤ −C₀ − 3.196;
by monotonicity these bound sup_{|y−y*|≥δ} u₃.
For λ = 1: u₁ increases on (−∞, y₁] and decreases on [y₁, ∞), where y₁ ∈ (0, y*) is the point with Im f′ = π (Im f′ passes
π before 3π); so sup_ℝ u₁ = u₁(y₁) ≤ sup_{[0,y*]} u₁ ≤ **−754.606** (K, certified; the true value is ≈ −767, the crude
bound suffices since −754.6 < −C₀ − 1 = −751.71).

### 3.6 Laplace's method and Lemma 20 (PROVED modulo 3.4–3.5)

On the line, N_h J_λ = i n ∫_ℝ N_h G(t)e^{−iπλt} dy = i n^{−12} ∫_ℝ A(x*+iy) e^{nΦ_λ(x*+iy)} (1+ρₙ) dy.

λ = 1: |N_h J₁| ≤ n^{−12}(1+K/n) e^{n·sup u₁} ∫|A| dy ≤ K′ n^{−12} e^{−754.6 n}.

λ = 3: split at |y−y*| = δ. Outside, |integrand| ≤ |A| e^{n(−C₀−ε(δ))}(1+K/n), giving ≤ K″ n^{−12} e^{−n(C₀+ε(δ))}. Inside, τ₃
is a simple saddle of the analytic function Φ₃ (Φ₃′(τ₃) = 0, Φ₃″(τ₃) = f″(τ₃) ≠ 0), the path is the straight line through it,
Re Φ₃ has its strict maximum on the path at τ₃ with Re[Φ₃″(τ₃)·i²] = −Re f″(τ₃) < 0, and A is analytic and nonzero at τ₃
(2τ₃ − η₀ ≠ 0, all other factors are powers of nonzero numbers). The saddle-point theorem for a path through a simple saddle
(Olver, *Asymptotics and Special Functions*, Ch. 4 §7, Thm 7.1, applied to the two half-paths; equivalently Izv. 2002 Lemma 5
or [8, Lemma 3] of Rivoal–Zudilin 2018) gives

  N_h J₃ = i n^{−25/2} A(τ₃) √(2π/f″(τ₃)) e^{n f₀(τ₃)} (1 + O(1/n))   (principal square root, Re f″ > 0).

Insert into (B): with B := i A(τ₃)√(2π/f″(τ₃)) ≠ 0, β := arg B − π/2, ω := Im f₀(τ₃),

  **F̃ₙ = (|B|/(24π)) n^{−25/2} e^{−C₀ n} [cos(nω + β) + O(1/n)] + O(n^{−12} e^{−754.6 n}).**   (F)

**Lemma 20 (r = 5, this η).** limsup (1/n) log|F̃ₙ| = −C₀ = Re f₀(τ₃), and F̃ₙ ≠ 0 for a set of n of positive lower density.
Proof. The upper bound is immediate from (F). For the lower bound, ω/π ∉ ℤ (certified, (S)). If ω/π is irrational, nω+β is
equidistributed mod 2π and |cos(nω+β)| ≥ ½ on a set of density 2/3. If ω/π = p/q in lowest terms, the points nω mod 2π are
q′ ∈ {q, 2q} ≥ 3 equally spaced points (q′ = 2 would force ω ∈ πℤ), so in every block of q′ consecutive n some point lies
within π/q′ ≤ π/3 of 0 or π, i.e. |cos| ≥ ½. On that set, for n large, |F̃ₙ| ≥ (|B|/(48π)) n^{−25/2} e^{−C₀n}(1 − O(1/n)) −
O(n^{−12}e^{−754.6n}) > 0. ∎

(The sign of F̃ₙ for large n is the sign of cos(nω+β); §5 compares this with exact signs.)

## 4. Conclusion (Zudilin's Proposition 5 with r = 5)

Suppose ζ(7), …, ζ(21) are all rational, with common denominator d. By Lemma 19, d·Δₙ·F̃ₙ ∈ ℤ for every n. By §2 and Lemma 20,
along the positive-density set of §3.6, 0 < |d Δₙ F̃ₙ| ≤ d·e^{(C₂ − C₀ + o(1)) n} = d·e^{(−3.6603890443 + o(1)) n} → 0,
a contradiction. ∎  (C₀ − C₂ = 750.7116948339 − 747.0513057897 = **3.6603890443 per n**; relative margin 0.49 %.)

## 5. Numerical validation (NUMERICAL; `barnes_check.py`, logs `barnes_q23_160_n1to9.log`, `barnes_q23_160_large.log`)

The contour (A) evaluated on the line Re τ = x* (mpmath quad, 40+2n digits) against the exact F̃ₙ of `exact_r5_q23_n9.jsonl`:
n = 1..9, |log|F̃ₙ|_contour − log|F̃ₙ|_exact| ≤ 4.5·10⁻¹³ and all nine signs agree (+ + − + + − − + −). This validates (A), (B)
and every sign/normalisation. The two branches at n = 9: the λ = 3 part is e^{15 n} larger than the λ = 1 part. Ratio of the
exact value to the leading term of (F) (with the exact prefactor at the saddle): 1.095, 0.948, 1.012, 1.055, 0.997, 1.011,
0.959, 1.003, 1.015 (n = 1..9), i.e. (F) already holds to a few per cent at n ≤ 9. Larger n (contour only, 160 digits):
n = 16, 20, 30, 50, 100, 200 give ratios 1.0025, 0.9906, 1.0135, 1.0014, 0.9872, **1.00035**, and log|F̃ₙ|/n = −755.90,
−755.07, −753.80, −752.66, −751.80, −751.285 (the printed λ = 1 "branch rate" at n ≥ 50 is a 10⁻³⁰⁰ floor artifact; that
branch is e^{−16n} smaller). The rates converge to −C₀ like −C₀ − 12.5 log n/n + B/n with B ≈ −49 (n = 200: predicted
−751.29), consistent with the n^{−25/2} prefactor of (F); the sign pattern follows cos(nω+β).

## 6. Other configurations (same script, all CERTIFIED)

| config | C₀ | ω/π (dist to ℤ) | Re f″ | sup u₁ bound | margin C₀−C₂ |
|---|---|---|---|---|---|
| r=3, Zudilin Thm 3 (η₀ = 91) | 227.5801964127 | −86.8972 (0.103) | 0.7073 | (no λ=1 subdominant; λ=1 is dominant) | +1.3308 (his) |
| r=5, q=23, η₀ = 160 (this proof) | 750.7116948339 | −466.6134 (0.387) | 0.2721 | −754.6 | +3.6604 |
| r=5, q=23, η₀ = 320 | 1500.5544112068 | −933.1461 (0.146) | 0.1361 | −1508.5 | +10.79 (engine) |
| r=5, q=23, η₀ = 536 (scout) | 2551.3220575000 | −1567.1730 (0.173) | — | — | +3.90 (scout) |

The r = 3 control reproduces the hypotheses of Zudilin's proved lemma. The η₀ = 320 configuration gives the same theorem
with margin 10.79 per n; only its C₂ is engine-computed (not re-verified by vz.py), so the write-up uses η₀ = 160.

## 7. Novelty (web read-only, 2026-09-25)

Published windows starting at ζ(7): {7,…,37} (Zudilin, Izv. Math. 66 (2002), Thm 1), {7,…,35} (Zudilin, Math. Notes 70
(2001), Thm 2; also a corollary of Lai–Zhou, Publ. Math. Debrecen 101 (2022): two of ζ(5..35)). Nothing shorter in: Zudilin
JTNB 2004 (§8 remark: improvement "can be" obtained, "we are not able to demonstrate the general case of Lemma 20"),
Zudilin SIGMA 2018 ({5..25} elementary), Rivoal–Zudilin 2018/2020 (two of 5..69), FSZ Compositio 2019, Lai–Yu 2020, Lai
JTNB 2025/2026 (asymptotic counts), Lai–Sprang 2023, Lai–Lupu–Sprang 2025 (p-adic), Krattenthaler–Rivoal Mem. AMS 2007
({5..19}-type via the denominator conjecture, starts at 5), Fischler 2021/2022. The scout's `records_ledger.json` records the
improvement as "claimed, not executed". Hence **{7,…,21} is new**, subject to the same standard ingredients as Zudilin's
Theorem 3 (PNT, Lemma 19) plus the certified computations above.

## 8. Stretch: the denominator conjecture for general η (reading result)

Krattenthaler–Rivoal (arXiv math/0311114, Mem. AMS 186 (2007)) prove their Conjecture 1 (Théorème 1, p. 12) for the
**symmetric** series S_{n,A,B,C,r}(z) = n!^{A−2Br} Σ_k (1/C!)∂_k^C [(k+n/2)(k−rn)_{rn}^B (k+n+1)_{rn}^B/(k)_{n+1}^A] z^{−k}:
all numerator blocks have the same length rn and multiplicity B, the denominator is (k)_{n+1}^A; the conclusion is
d_n^{A−l−1} p_{l,n} ∈ ℤ, 2 d_n^{A+C−1} p_{0,C,n} ∈ ℤ (one power of d_n saved). The parameters A, B, C, r are arbitrary, but the
block lengths are not: Zudilin's general-η forms (JTNB §9, Conjecture "drop D_{m_{q−r}}") are NOT covered. Théorèmes 3–6
refine the symmetric case (Φₙ-type savings for r = 1). So "drop D_{m_{q−r}}" for general η remains a CONJECTURE; the q = 21
window {7,…,19} cannot be claimed on it. Moreover the scout's GPU search with the conjectural objective
(log `vwp_r5_q21.log` of the research session, not included; objective margin_denconj = C₀ − C₂ + m_{q−r}) found only negative values:
−9.15 (η₀ = 114), −21.4 (η₀ = 267), −27.5 (η₀ = 336), −32.1 (η₀ = 154), i.e. about −0.08 per unit η₀ at best, while the
unconditional margin is −0.45 per unit η₀. Precise statement of the obstruction for (b2): even with a KR-type theorem for
unequal block lengths, no q = 21 configuration with C₀ − C₂ + m_{q−r} > 0 is known (best −9.15 at η₀ = 114), so {7,…,19}
is out of reach of this family by both the missing theorem and the ledger.

## 9. Limitations and obstructions (precise)

1. The o(n) in log Δₙ is the PNT's; the theorem is asymptotic (no effective n₀), exactly as Zudilin's.
2. The method needs η₀−η₁ < Re τ_d < η₀ (the Barnes line through the saddle must avoid the cuts). For the scout's r = 7
   candidates (windows from ζ(9)) Re τ_d > η₀ (`vwp_conditional_windows.json`), so the straight line fails and a polygonal
   contour hugging the cut [η₀, ∞) is needed (as in Rivoal–Zudilin 2018, case ℓ = 2); the certification would need 2-D boxes.
3. The nonvanishing is only on a positive-density subsequence (ω/π ∉ ℤ); this is all Prop. 5 needs.
4. q = 21 ({7..19}) fails in this family by 0.385 per unit η₀ (row W3) without the denominator conjecture (§8).

## 10. Files (`docs/window/`)

`zud5.py` (definitions, exact saddle polynomial), `explore.py` → `explore_q23_160.log` (all 27 roots, branches, profiles,
descent paths), `certify_line.py` → `certify_{q23_160,thm3,q23_320,q23_536}.{log,json}` (CERTIFIED items; only the
`q23_160` files are included here), `barnes_check.py` → `barnes_q23_160_n1to9.log`, `barnes_q23_160_large.log`
(validation), the verifier's `vz.py` (C₂). The research session's scout files named in §§7–9 (`records_ledger.json`,
`vwp_conditional_windows.json`, `zud_engine.py`) are not included.
