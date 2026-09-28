# Crude upper bound for F̃ₙ (window {ζ(7),…,ζ(21)}): |F̃ₙ| ≤ e^{117} n^{16} e^{−750.618 n} for every n ≥ 1

Track `crude-upper-bound` (Theorem U of `docs/proof.md`), written by an AI prover agent on 2026-09-25. Research-session
paths were replaced by the paths of this repository; only some of the scripts, logs and certificates named below are
included (see `README.md` in this folder). Labels: **PROVED** (argument written out here), **CERTIFIED** (interval /
exact-rational arithmetic, script named), **NUMERICAL** (evidence only, not used).

## 0. Result

Configuration of `docs/window/proof.md` (Zudilin JTNB 16 (2004) §8): r = 5, q = 23, η₀ = 160,
η = (47,47,47,47,48,50,50,51,52,…,66) (Ση = 1272, η₁+…+η₅ = 236), h₀ = 160n+2, h_j = η_j n+1,

  R(t) = (h₀+2t) ∏_{l=1}^{h₀−1}(t+l)⁵ / ∏_{j=1}^{23} ∏_{l=h_j}^{h₀−h_j}(t+l),   N_h = ∏_{j=6}^{23}(h₀−2h_j)! / ∏_{j=1}^{5}((h_j−1)!)²,

  F̃ₙ = N_h Σ_{k≥0} [ε⁴] R(k+ε)   (= `Fn cfgW n` of `Zeta2Lean/Window/Defs.lean`).

**Theorem U.** Take either parameter set

| set | line x₀ | tangent point p | contour abscissa M_n (∈ ℤ+½) | C₀′ (certified lower bound) | log K ≤ | loss C₀ − C₀′ |
|---|---|---|---|---|---|---|
| simple | 159 | 181/20 | ½ − n | **750.6183158756** | 116.92713 | 0.0934 |
| sharp | 3984/25 | 26208/3125 | −⌊16n/25⌋ − ½ | **750.7116742473** | 120.06369 | 2.06·10⁻⁵ |

Then for **every** n ≥ 1:   **|F̃ₙ| ≤ K · n¹⁶ · e^{−C₀′ n}.**

**Corollaries.** (i) |F̃ₙ| ≤ e^{−748.1 n} for all n ≥ 74 (simple) resp. n ≥ 73 (sharp): this is `Stmt_L20Upper`
(C0lo = 748.1) of `zeta-window-lean`. (ii) limsup (1/n) log|F̃ₙ| ≤ −750.7116742473 = −C₀ + 2.06·10⁻⁵.
(iii) With the unrefined Lemma 19 (C₂ = 747.0513057897): C₀′ − C₂ = +3.5670 (simple), +3.6603684 (sharp), i.e. the
upper half of Lemma 20 is settled with essentially the full margin of docs/window/proof.md; with a refined C₂′ ≈ 731.5 the
margin is ≈ +19.1 / +19.2. (iv) For every ε > 0 the same proof, with (x₀, p) closer to the saddle (x*, y*) =
(159.3564180538, 8.3937123721), certifies C₀′ = C₀ − ε: the loss is ≈ 0.678(x₀ − x*)² + |U′(x₀,p)|·max(p, A−p).

**What the upper bound no longer needs** (compared with docs/window/proof.md §3): the saddle τ₃ (Rouché, branch
certification), Re f″(τ₃) > 0, the global unimodality of u₃, the λ = 1 branch analysis, Laplace/Olver, complex
Stirling. What remains: the contour representation (Lemma 1, PROVED, standard), elementary real-variable inequalities,
one concavity lemma, and ≈ 250 rational enclosures of log/arctan values (one tangent point, one monotone cell).

| step | statement | status | where |
|---|---|---|---|
| L1 | F̃ₙ = −(N_h/2πi) ∫_{M+iℝ} K₅R dt, M ∈ ℤ+½, −h₁ < M < 0 | PROVED (validated: n ≤ 9 exact to 4.5e−13, all signs) | §2, §7 |
| L2 | \|K₅(M+is)\| ≤ (8π⁵/3) e^{−2π\|s\|} on half-integer lines | PROVED | §3 |
| L3 | window comparison of Σ log\|t+l\| with ∫ (all Im t, incl. 0) | PROVED | §4 |
| L4 | log(N_h\|K₅R\|) ≤ nU(x,η) + 4log(2πn) + 11 log(n(162+2\|η\|)) + K₂ | PROVED (Robbins for N_h) | §5 |
| L5 | U(x₀,·) concave on [0,A]; one tangent ⇒ sup U ≤ −C₀′; U′<0 on [A,60]; U′ ≤ −κ on [60,∞); \|∂ₓU\| ≤ B | PROVED + CERTIFIED | §6 |
| T | assembly, explicit K | PROVED | §7 |

## 1. The real landscape function

  Gf(a, y) := (a/2) log(a²+y²) + y·arctan(a/y) − a  (y ≠ 0),   Gf(a, 0) := a log|a| − a   (continuous in y).

Gf(·, y) is a primitive of a ↦ ½log(a²+y²) = log|a+iy| (also for y = 0, as an improper integral across a = 0);
∂_y Gf(a, y) = arctan(a/y), ∂²_y Gf(a, y) = −a/(a²+y²) (y > 0); Gf(a, −y) = Gf(a, y); and the scaling law
Gf(λa, λy) = λ Gf(a, y) + λ a log λ (λ > 0). (This is `Gf` of `zeta2-pair-lean`, `Pair/Proofs/Growth.lean`.) Put

  C_η := Σ_{j=6}^{23}(η₀−2η_j)log(η₀−2η_j) − 2Σ_{j=1}^{5}η_j log η_j = 1275.77611272375881896 (CERTIFIED),
  U(x, y) := C_η − 336 + 5[Gf(x, y) − Gf(x−η₀, y)] − Σ_{j=1}^{23}[Gf(x−η_j, y) − Gf(x−η₀+η_j, y)] − 2π|y|.

(336 = Σ_{j>5}(η₀−2η_j) − 2Σ_{j≤5}η_j = −[5η₀ − Σ_j(η₀−2η_j)].) NUMERICAL remark (not used): U(x, y) = Re f(x+iy) + 3π|y|,
i.e. U is the function u₃ of docs/window/proof.md §3.5 on the line Re τ = x (checked to 3·10⁻³⁷, `explore_U.log`).

## 2. Lemma 1 (Barnes-type representation) — PROVED

K₅(t) := Σ_{k∈ℤ}(t−k)^{−5} = (1/4!)(d/dt)⁴[π cot πt]. **For n ≥ 1 and M ∈ ℤ+½ with −h₁ < M < 0,
F̃ₙ = −(N_h/2πi) ∫_{M−i∞}^{M+i∞} K₅(t)R(t) dt** (absolutely convergent).

*Proof (residue-free, as formalised for the pair in `zeta2-pair-lean`: `vline_higher`, `vline_left`, `vline_Pc_kerS`).*
The poles of R are the integers −l with l ∈ [h_j, h₀−h_j] for some j, all ≤ −h₁ < M; so R is holomorphic on
{Re t > −h₁} ⊃ {Re t ≥ M}, and |R(t)| ≤ C|t|⁻² there (deg R = −336n − 17 ≤ −2; docs/window/proof.md §1 prints −336n − 4, a
harmless slip). Fix k ∈ ℤ. If k < M, R(t)(t−k)⁻⁵ is holomorphic on Re t ≥ M and O(|t|⁻⁷): closing with rectangles to the
right, ∫_{M+iℝ} R(t)(t−k)⁻⁵dt = 0. If k > M, Cauchy's formula for the 4th derivative on the same rectangles (the line is
traversed clockwise with respect to the right half-plane) gives ∫_{M+iℝ} R(t)(t−k)⁻⁵dt = −2πi [ε⁴]R(k+ε). On the line
|t−k| ≥ |M−k| ≥ ½, so Σ_k |t−k|⁻⁵ ≤ 2Σ_{m≥0}(m+½)⁻⁵ uniformly and ∫|R||dt| < ∞: summation and integration commute
(dominated convergence), and ∫ K₅R dt = −2πi Σ_{k>M}[ε⁴]R(k+ε). For integers M < k ≤ −1, −k < h₁ ≤ h_j lies outside every
pole range while (t+1)_{h₀−1}⁵ vanishes to order 5 at k, so [ε⁴]R(k+ε) = 0 and the sum is Σ_{k≥0}. Multiply by −N_h/2πi. ∎
(Equivalently docs/window/proof.md §3.1 with K₅R = −G·V₅(cos πt).)

## 3. Lemma 2 (kernel on half-integer lines) — PROVED

**For M ∈ ℤ+½ and s ∈ ℝ: |K₅(M+is)| = (π⁵/3)·T(1−T²)|2−3T²| ≤ (8π⁵/3)e^{−2π|s|}, T := tanh(π|s|).**
*Proof.* cot⁗ = 8C(1+C²)(2+3C²) (C = cot; differentiate cot′ = −(1+C²) three times), so K₅(t) = (π⁵/3)C(1+C²)(2+3C²) with
C = cot(πt). For t = M+is, C = cot(π/2 + iπs) = −i tanh(πs): |C| = T, 1+C² = 1−T² = sech²(πs) ≤ 4e^{−2π|s|}, and
|2+3C²| = |2−3T²| ≤ 2. ∎ (NUMERICAL: ratio ≤ 0.5 on 300 random points, `validate_chain.log`. Lean alternative:
K₅(t) = `kerS 5 (t+1/2)`; `norm_kerS_vline_le` and `kerS_decay` of `zeta2-pair-lean` give the same shape with a non-explicit
constant, which suffices for the eventual statement. Numerical caveat: evaluating 1+C² naively cancels catastrophically for
large |s|; compute K₅ as (π⁵/3)C(2+3C²)/sin²(πt).)

## 4. Lemma 3 (window comparison) — PROVED

Let t = M+iy (M, y real), g(u) := log|t+u| (u ∈ ℝ), and integers A ≤ B.
(a) If no t+l (A ≤ l ≤ B) vanishes: **Σ_{l=A}^{B} g(l) ≤ ∫_{A−1}^{B+1} g(u)du + 1 + log 2.**
(b) If M + A − 1 ≥ 0: **Σ_{l=A}^{B} g(l) ≥ ∫_{A−1}^{B} g(u)du.**
In both, ∫_α^β g = Gf(M+β, y) − Gf(M+α, y).

*Proof.* g is decreasing on (−∞, −M] and increasing on [−M, ∞). (a) Let L = ⌊−M⌋. For l ≤ L, g(l) ≤ ∫_{l−1}^{l} g; for
l ≥ L+1, g(l) ≤ ∫_l^{l+1} g. These unit intervals are disjoint and cover [A−1, B+1] except one unit interval J
(J = [L, L+1], [B, B+1] or [A−1, A] according as A ≤ L < B, B ≤ L, or A > L). Since g(u) ≥ log|M+u| and
min_a ∫_a^{a+1} log|v|dv = ∫_{−1/2}^{1/2} log|v|dv = −1 − log 2, we get −∫_J g ≤ 1 + log 2. (b) g is increasing on
[A−1, ∞), so g(l) ≥ ∫_{l−1}^{l} g. ∎ (Valid for every y, including the real-axis crossing y = 0. The pair-lean lemmas
`num_sum_le`, `den_sum_ge` are the case y ≥ 1 without the constant 1 + log 2.)

## 5. Lemma 4 (pointwise bound on the line) — PROVED

**Let n ≥ 1, M ∈ ℤ+½ with 1 − h₁ ≤ M ≤ −½, x := η₀ + M/n, t := M + inη (η ∈ ℝ). Then**

  **log(N_h|K₅(t)R(t)|) ≤ nU(x, η) + 4log(2πn) + log|h₀+2t| + 10 log|nx+2+inη| + K₂,**

K₁ := ½Σ_{j>5}log(η₀−2η_j) − Σ_{j≤5}log η_j ∈ 14.7201681460 ± 10⁻¹⁰, K₂ := K₁ + 3/56 + log(8π⁵/3) + 5(1+log 2) ≤ 29.9439541597.
If also x ≤ 160, the two middle logarithms are ≤ 11 log(n(162 + 2|η|)).

*Proof.* (1) log|R(t)| = log|h₀+2t| + 5Σ_{l=1}^{h₀−1}g(l) − Σ_j Σ_{l=h_j}^{h₀−h_j} g(l). Lemma 3(a) with (A,B) = (1, h₀−1)
(no term vanishes: M ∉ ℤ) and 3(b) with (A,B) = (h_j, h₀−h_j) (M + h_j − 1 ≥ M + h₁ − 1 ≥ 0):
log|R| ≤ log|h₀+2t| + 5(1+log 2) + 5[Gf(M+h₀, y) − Gf(M, y)] − Σ_j[Gf(M+h₀−h_j, y) − Gf(M+h_j−1, y)], y = nη.
(2) M+h₀ = nx+2, M = n(x−η₀), M+h₀−h_j = n(x−η_j)+1, M+h_j−1 = n(x−η₀+η_j). The shifts: Gf(nx+2, y) − Gf(nx, y) =
∫_{nx}^{nx+2} ½log(u²+y²)du ≤ 2 log|nx+2+iy| (nx > 0), and Gf(n(x−η_j)+1, y) − Gf(n(x−η_j), y) ≥ log(n(x−η_j)) ≥ 0
(x − η_j ≥ 47). Scaling (§1): log|R| ≤ n·[U(x,η) − C_η + 336 + 2π|η|] − 336 n log n + log|h₀+2t| + 10 log|nx+2+iy| + 5(1+log 2);
the n log n coefficient is 5η₀ − Σ_j(η₀−2η_j) = −336.
(3) Robbins, √(2πm)(m/e)^m ≤ m! ≤ √(2πm)(m/e)^m e^{1/(12m)}, with h₀−2h_j = (η₀−2η_j)n (≥ 28n) and h_j−1 = η_j n:
log N_h ≤ n(C_η − 336) + 336 n log n + 4 log(2πn) + K₁ + 18/(12·28). (4) Lemma 2: log|K₅(t)| ≤ log(8π⁵/3) − 2πn|η|.
Add (2)–(4). Last claim: |h₀+2t| = |n(2x−η₀)+2+2inη| ≤ n(162+2|η|), |nx+2+inη| ≤ n(162+2|η|) for x ≤ 160. ∎
(NUMERICAL: holds with slack ≥ 134 nats at n = 1…30, `validate_chain.log`.)

## 6. Lemma 5 (landscape on the line x₀) — PROVED + CERTIFIED

Let c₀ := η₀ − x₀, A := x₀ − η₀ + η₁, a_j := x₀ − η₀ + η_j, b_j := x₀ − η_j; so 0 < c₀ < A = a₁ ≤ a_j < b_j
(simple: c₀ = 1, A = 46, a_j = η_j − 1, b_j = 159 − η_j; sharp: c₀ = 16/25, A = 1159/25). Write U(η) := U(x₀, η). For η > 0,

  U′(η) = 5[arctan(x₀/η) + arctan(c₀/η)] − 2π − Σ_j[arctan(b_j/η) − arctan(a_j/η)],
  U″(η) = −[5h(x₀) + 5h(c₀) + Σ_j (h(a_j) − h(b_j))],   h(a) := a/(a²+η²).

(a) **Concavity (PROVED).** For 0 < η ≤ A: h is decreasing on [η, ∞) and η ≤ a_j < b_j, so h(a_j) ≥ h(b_j); with
h(x₀), h(c₀) > 0 this gives U″ < 0. U is continuous at 0, hence concave on [0, A]. (Belt and braces, CERTIFIED:
U″ ≤ −0.091 (simple), ≤ −0.089 (sharp) on [0, A] by 400 interval pieces.)
(b) **One tangent (CERTIFIED, `certify_iv.py`, `certify_exact.py`).**
 simple: U(181/20) ∈ −750.63093443929581424 ± 10⁻²⁰, U′(181/20) ∈ 3.41503752315687·10⁻⁴ ± 10⁻²⁰;
 sharp: U(26208/3125) ∈ −750.71168613149548685 ± 10⁻²⁰, U′(26208/3125) ∈ −3.12958314870·10⁻⁷ ± 10⁻²⁰.
 By (a), U(η) ≤ U(p) + U′(p)(η − p) ≤ U(p) + |U′(p)|·max(p, A−p) =: −C₀′ on [0, A]:
 **C₀′ = 750.61831587564774 (simple), 750.71167424739169 (sharp).**
(c) **One monotone cell (CERTIFIED).** Each summand of U′ is monotone in η, so on [l, r]:
 sup U′ ≤ 5[arctan(x₀/l) + arctan(c₀/l)] − 2π + Σ_j arctan(a_j/l) − Σ_j arctan(b_j/r).
 With [l, r] = [A, 60]: sup U′ ≤ −3.8873 (simple), −3.9814 (sharp). So U is decreasing on [A, 60].
(d) **Tail (PROVED + CERTIFIED).** Since b_j > a_j > 0 and arctan u + arctan(1/u) = π/2 (u > 0):
 U′(η) ≤ 3π − 5[arctan(η/x₀) + arctan(η/c₀)], decreasing in η; at η = 60 it is −κ with
 κ ∈ 0.15006196980 (simple), 0.17632419232 (sharp) (CERTIFIED), both > 22/282 = 0.0780.
 **Consequently U(η) ≤ −C₀′ for all η ≥ 0 (by (b) on [0,A] and monotonicity on [A,∞)), and
 U(η) ≤ −C₀′ − κ(η − 60) for η ≥ 60.**
(e) **x-Lipschitz bound (PROVED + CERTIFIED).** ∂ₓU = ½[5 log((x²+η²)/((η₀−x)²+η²)) − Σ_j log(((x−η_j)²+η²)/((x−η₀+η_j)²+η²))]
 and each ratio lies between 1 and its value at η = 0, so for |x − x₀| ≤ ½ and all η:
 |∂ₓU| ≤ B := max(5 log((x₀+½)/(η₀−x₀−½)), Σ_j log((x₀−½−η_j)/(x₀−½−η₀+η_j))) = 28.8259555140 (simple), 35.2020564429 (sharp).

## 7. Assembly — PROVED

Fix n ≥ 1 and M = M_n from the table: M_n ∈ ℤ+½, 1 − h₁ ≤ M_n ≤ −½, and x_n := η₀ + M_n/n satisfies |x_n − x₀| ≤ 1/(2n),
x_n ≤ 160. K₅ and R are real on ℝ, so |K₅R|(t̄) = |K₅R|(t), and Lemma 1 gives, with s = nη,

  |F̃ₙ| ≤ (N_h/2π)∫_ℝ|K₅R|(M_n+is)ds = (n/π)∫_0^∞ N_h|K₅R|(M_n+inη)dη.

Lemma 4 and Lemma 5(e) (U(x_n,η) ≤ U(x₀,η) + B/(2n)):  N_h|K₅R|(M_n+inη) ≤ (2π)⁴ e^{K₂+B/2} n¹⁵ (162+2η)¹¹ e^{nU(x₀,η)}.
By Lemma 5(d), ∫_0^{60}(162+2η)¹¹e^{nU}dη ≤ 60·282¹¹e^{−C₀′n}, and with (1+v/141)¹¹ ≤ e^{11v/141},
∫_{60}^∞(162+2η)¹¹e^{nU}dη ≤ 282¹¹e^{−C₀′n}∫_0^∞e^{−(nκ − 22/282)v}dv ≤ 282¹¹e^{−C₀′n}/(κ − 22/282). Hence

  **|F̃ₙ| ≤ K n¹⁶ e^{−C₀′n},  K := (2π)⁴π⁻¹ e^{K₂+B/2} · 282¹¹ · (60 + 1/(κ − 22/282)),**

log K ≤ 116.9271258620 (simple), 120.0636865496 (sharp) (CERTIFIED). Corollary (i): log K + 16 log n ≤ (C₀′ − 748.1)n holds
for n = 74 (simple; 73 sharp) and, the right side growing faster, for all larger n (checked with rational log bounds). ∎

## 8. Validation (NUMERICAL; not used by the proof)

* `contour_check.py` (40 digits): the representation of Lemma 1 on M_n = −⌊0.64n⌋ − ½ reproduces the exact F̃ₙ of
  `docs/window/exact_r5_q23_n9.jsonl` for n = 1…9 to ≤ 4.5·10⁻¹³ in log|F̃ₙ|, all nine signs; n = 12 gives
  log|F̃₁₂|/12 = −757.612674289 (= docs/window/proof.md §5).
* The quantity actually bounded, J_n := (N_h/2π)∫|K₅R||dt|, tracks |F̃ₙ| (no exponential loss on a vertical line):
  log J_n/n = −754.979, −752.648, −751.767, −751.282, −751.019, −750.846 at n = 20, 50, 100, 200, 400, 1000, against
  log|F̃ₙ|/n = −755.068, −752.660, −751.802, −751.285 (n = 20…200); log(J_n/|F̃ₙ|) ∈ [0.4, 3.8] for n ≤ 12 (large where
  cos(nω+β) is small). J_n behaves like −C₀ − 12.5 log n/n + O(1/n), exactly as |F̃ₙ| (docs/window/proof.md §5).
* `validate_chain.py`: Lemma 3 on 400 random instances (worst slack 1.67 resp. 0.010), Lemma 2 (max ratio 0.5),
  Lemma 4 at n = 1…30 (slack ≥ 134 nats), Robbins bound for N_h (slack 0.036–0.053).
* The theorem's bound vs truth: (log bound)/n = −733.72, −749.61, −750.39 at n = 9, 200, 1000 (simple) vs
  log|F̃ₙ|/n = −759.21, −751.29 (n = 9, 200) and log J₁₀₀₀/1000 = −750.85; the only losses are the prefactor n¹⁶
  (truth: n^{−12.5}) and the constant K.

## 9. The other candidates

* **Termwise / Cauchy estimates on circles: impossible.** (1/n)log(N_hR(n(τ−η₀))) → C_η − 336 + V(τ,0) for real τ > η₀,
  whose maximum is **−701.698** (τ = 174.9196, the real λ = −5 critical point; `termwise_rate.log`; exact −703.53 at
  n = 60). The Taylor coefficients N_hR⁽⁴⁾(t)/4! have the same rate, so any bound by Σ_t|term_t| (with or without
  Cauchy estimates on circles, whose maxima are ≥ the centre values) is ≥ e^{(−701.698+o(1))n}: the series cancels
  e^{49.01n}, a loss of 49.01 per n > the affordable 15–19 (and > the unrefined margin 3.66).
* **Stirling version on Re τ = x*** (docs/window/proof.md §3.3, |V₅(cos πt)| ≤ e^{3π|Im t|}, |1+ρₙ| ≤ e^{15/n}): same exponent
  sup u₃ = −C₀, no loss either, but needs complex Stirling with remainder (DLMF 5.11.9–10) and the Gamma-function
  bookkeeping (constant A(τ)); Lemmas 3–4 replace it by finite sums of logarithms.
* **This proof** = Barnes line + pointwise bounds, exponent loss 0 in the limit; the line need not pass through the
  saddle (loss 0.678(x₀−x*)², 0.081 for x₀ = 159) and the saddle need not be located.

## 10. Lean porting notes (this repository, then open gap `lemma20` upper half; now `Zeta2Lean/Window/Proofs/Lemma20Upper.lean`)

Everything has a counterpart in `Zeta2Lean/Pair/Proofs/Growth.lean` of the pair project
(https://github.com/gmDevi/zeta2-7-9-lean; no `sorry` in that file or in `Landscape/*.lean`, checked by grep 2026-09-25):
* L1 ← `vline_higher` (right poles, −2π·Taylor coefficient), `vline_left` (left poles, 0), dominated interchange as in
  `vline_Pc_kerS`; kernel K₅(t) = `kerS 5 (t + 1/2)`; hypotheses: R holomorphic on Re t > −h₁, ‖R t‖ ≤ C/‖t‖ on Re t ≥ M.
* L2 ← `norm_kerS_vline_le` (lines Re ∈ ℤ after the ½-shift) + `kerS_decay`; any κ suffices for the ∀ᶠ statement.
* L3 ← `num_sum_le`, `num_sum_le_Ico`, `den_sum_ge` (y ≥ 1); for |y| < 1 add the unit-interval bound
  ∫_a^{a+1}log|v| ≥ −1 − log 2 (or copy the crossing-segment comparison `norm_Rc_vert_le`/`seg_A`).
* L4 ← `Gf_scale`, `window_scale`, `norm_Rc_le_exp`; Mathlib `Stirling` for N_h (only O(log n) accuracy is needed).
* L5 ← new but elementary: ∂²_y Gf = −a/(a²+y²), concavity via second derivative, tangent-line inequality; numeric facts
  via `Landscape/Numerics.lean` (artanh-series log bounds, alternating arctan bounds, π/4, π/2 reductions).
  `certificate_exact_x159_p181_20_Y60.json` lists every enclosure (rational endpoints, 10⁻⁴⁰): 138 for (b) incl. C_η,
  78 for (c), 3 for (d), 20 for (e), 7 constants (the 58 log n values are only for the explicit n₀).
* Assembly ← `integral_exp_affine_Ioi`, `eventually_poly_le_exp`.

## 11. Files (this folder)

`ub_common.py` (definitions), `explore_U.py/.log` (landscape, identity U = Re f + 3π|y|, choice of x₀, p),
`certify_iv.py` (mpmath.iv, 150 bits) → `certify_iv_main.log`, `certify_iv_x159.log`, `certify_iv_*.json`;
`certify_exact.py` (exact rationals, series with remainders, no floating point) → `certify_exact.log`,
`certificate_exact_*.json`; `validate_chain.py/.log`; `contour_check.py/.log`, `contour_check_J_large.log`;
`termwise_rate.py/.log`; `check_ledger.py/.log` (all 933 exact-rational enclosures of the three certificate files
contain the 80-digit mpmath value; widths ≤ 1.6·10⁻³⁹). Both certifications agree to all printed digits and print
ALL CERTIFIED for both parameter sets (and for the integer variant p = 9: C₀′ = 750.0859958360, n₀(748.1) = 96).
