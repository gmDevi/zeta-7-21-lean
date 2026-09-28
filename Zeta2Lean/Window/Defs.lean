module

public import Mathlib

@[expose] public section

/-!
# Zeta2Lean.Window.Defs — every definition of the window formalisation

Target (`Zeta2Lean/Window/Main.lean`), stated with Mathlib notions only:

  `¬ ∀ k ∈ ({7, 9, 11, 13, 15, 17, 19, 21} : Finset ℕ), ∃ q : ℚ, riemannZeta (k : ℂ) = (q : ℂ)`,

i.e. at least one of `ζ(7), ζ(9), …, ζ(21)` is irrational.  Informal proof: `docs/proof.md` (first
version `docs/window/proof.md`), built on W. Zudilin, *Arithmetic of linear forms involving odd
zeta values*, J. Théor. Nombres Bordeaux 16 (2004) 251–291, §8 (called "JTNB" below): forms
(8.1)–(8.13), Lemma 19 (arithmetic, all odd `r`), Lemma 20 (asymptotics; proved there only for
`r = 3`, here replaced by Theorems U and N of `docs/proof.md`), Proposition 5 (criterion).  Map of
statements: `BLUEPRINT_WINDOW.md`.

**No definition of this file occurs in the final statement**, so none of them is trusted: if one
of them were unfaithful to JTNB, the Lean theorem would still be the theorem displayed above.  They
only have to make the `Stmt_*` of `Window/Statements.lean` true (checked numerically by
`python/window_mirror.py`, which transcribes every definition below literally).

## The construction (JTNB §8), generic in the configuration `c = (r, q, η₀, η)`

For `n ≥ 1`: `h₀ = η₀ n + 2`, `h_j = η_j n + 1` (`j = 1..q`, JTNB (8.13)), and
```
R(t)  = (h₀+2t) (t+1)_{h₀-1}^r / ∏_{j=1}^q (t+h_j)_{h₀+1-2h_j}                         (8.2)
N_h   = ∏_{j>r} (h₀-2h_j)! / ∏_{j≤r} (h_j-1)!²,     R̃ = N_h R                          (8.6)
F̃_n  = ∑_{t≥0} R̃^{(r-1)}(t)/(r-1)!  = ∑_{t ≥ 0} [ε^{r-1}] R̃(t+ε)             (8.4), (8.6)
```
`R̃` is a product of Nesterenko "bricks" (JTNB (7.3)):
`R̃(t) = (h₀+2t) ∏_{j≤r} P_j(t) Q_j(t) ∏_{j>r} S_j(t)` with the integer-valued polynomials
`P_j(t) = (t+1)_{h_j-1}/(h_j-1)!`, `Q_j(t) = (t+h₀-h_j+1)_{h_j-1}/(h_j-1)!` and the rational bricks
`S_j(t) = (h₀-2h_j)!/(t+h_j)_{h₀-2h_j+1}` (simple poles at `t = -h_j, …, -(h₀-h_j)`).
The pole of `R̃` at `t = -k` has order `≤ q - r`; its Laurent coefficients are read off from
`G_k(ε) = ε^{q-r} R̃(-k+ε) = (h₀-2k+2ε) ∏_{j≤r} P_j(-k+ε) Q_j(-k+ε) ∏_{j>r} (ε S_j(-k+ε))`
(`Gk`), a power series: `B_{j,k} = [ε^{q-j}] G_k` is the coefficient of `(t+k)^{-(j-r)}`
(`j = r+1..q`, JTNB p. 281).  With `r` odd,
```
F̃_n = ∑_{s=r}^{q-1} A_s ζ(s) - A₀,   A_s = C(s-1, r-1) ∑_k B_{s+1,k},
A₀  = ∑_{j=r+1}^{q} C(j-2, r-1) ∑_k B_{j,k} H^{(j-1)}_{k-h_1}                            (8.12)
```
and `A_r = 0`, `A_s = 0` for even `s` (symmetry (8.5)), so only `ζ(r+2), ζ(r+4), …, ζ(q-2)` remain.

## Conventions

* Power series are Mathlib's `PowerSeries ℚ`; every `⁻¹` below is applied to a series with non-zero
  constant term wherever it is used (Mathlib: `φ⁻¹ = 0` iff `constantCoeff φ = 0`).  `Rser c n y`
  is only meaningful when `y` is not a pole (`y + k ≠ 0` for `k ∈ Krange`), e.g. `y = t ∈ ℕ`.
* `/` on `ℤ` is `Int.ediv`, which is floor division for a positive divisor `p`
  (`Rat.floor_intCast_div_natCast`); so `omegaKP` is literally JTNB (8.9).
* All `ℕ`-subtractions are non-truncating under `Admissible c` and `1 ≤ n`.
-/

set_option linter.style.longLine false

open Filter Topology Finset PowerSeries

noncomputable section

namespace ZetaWindow

/-! ## Configurations (JTNB (8.1), (8.13)) -/

/-- A configuration of Zudilin's very-well-poised forms: `r` derivatives (odd), `q` factors (odd),
directions `η₀` and `η_j` (`j = 1..q`; `eta 0` and `eta j` for `j > q` are unused junk). -/
structure Config where
  r : ℕ
  q : ℕ
  eta0 : ℕ
  eta : ℕ → ℕ

namespace Config

/-- `h₀ = η₀ n + 2` (JTNB (8.13)). -/
def h0 (c : Config) (n : ℕ) : ℕ := c.eta0 * n + 2

/-- `h_j = η_j n + 1` (JTNB (8.13)). -/
def h (c : Config) (n j : ℕ) : ℕ := c.eta j * n + 1

end Config

/-- Zudilin's admissibility conditions (JTNB §8): `r, q` odd, `r ≥ 3`, `q ≥ r + 4`,
`1 ≤ η₁ ≤ η₂ ≤ ⋯ ≤ η_q < η₀/2`, and (8.1) `h₁ + ⋯ + h_q ≤ h₀ (q-r)/2` for every `n ≥ 1`, which in
terms of the directions is `2 ∑ η_j + 2r ≤ (q-r) η₀`. -/
structure Admissible (c : Config) : Prop where
  r_odd : Odd c.r
  q_odd : Odd c.q
  three_le_r : 3 ≤ c.r
  r_add_four_le_q : c.r + 4 ≤ c.q
  one_le_eta : 1 ≤ c.eta 1
  eta_mono : ∀ i j, 1 ≤ i → i ≤ j → j ≤ c.q → c.eta i ≤ c.eta j
  two_eta_lt : 2 * c.eta c.q < c.eta0
  deg_cond : 2 * (∑ j ∈ Icc 1 c.q, c.eta j) + 2 * c.r ≤ (c.q - c.r) * c.eta0

/-- The window directions `η = (47, 47, 47, 47, 48, 50, 50, 51, 52, …, 66)` (`η_j = j + 43` for
`8 ≤ j ≤ 23`). -/
def etaW (j : ℕ) : ℕ :=
  if j ≤ 4 then 47 else if j = 5 then 48 else if j ≤ 7 then 50 else j + 43

/-- **The window configuration** `r = 5`, `q = 23`, `η₀ = 160`, `η = etaW` (docs/window/proof.md §1). -/
def cfgW : Config := ⟨5, 23, 160, etaW⟩

/-! ## The linear forms (JTNB (8.2)–(8.6)) -/

/-- The normalisation `N_h = ∏_{j=r+1}^q (h₀-2h_j)! / ∏_{j=1}^r (h_j-1)!²` of JTNB (8.6). -/
def Nh (c : Config) (n : ℕ) : ℚ :=
  (∏ j ∈ Icc (c.r + 1) c.q, ((c.h0 n - 2 * c.h n j).factorial : ℚ)) /
    ∏ j ∈ Icc 1 c.r, ((c.h n j - 1).factorial : ℚ) ^ 2

/-- The Taylor expansion `ε ↦ R̃(y + ε) = N_h R(y + ε)` of JTNB (8.2), (8.6) at a point `y` that is
not a pole:
`N_h (h₀ + 2y + 2ε) (∏_{i=1}^{h₀-1} (y+i+ε))^r / ∏_{j=1}^q ∏_{i=h_j}^{h₀-h_j} (y+i+ε)`. -/
def Rser (c : Config) (n : ℕ) (y : ℚ) : PowerSeries ℚ :=
  C (Nh c n) * (C ((c.h0 n : ℚ) + 2 * y) + C 2 * X) *
    (∏ i ∈ Ico 1 (c.h0 n), (C (y + i) + X)) ^ c.r *
    (∏ j ∈ Icc 1 c.q, ∏ i ∈ Icc (c.h n j) (c.h0 n - c.h n j), (C (y + i) + X))⁻¹

/-- The `t`-th term `R̃^{(r-1)}(t)/(r-1)! = [ε^{r-1}] R̃(t + ε)` of the series (8.4)/(8.6). -/
def term (c : Config) (n t : ℕ) : ℚ :=
  coeff (c.r - 1) (Rser c n t)

/-- **Zudilin's linear form** `F̃_n = ∑_{t ≥ 0} R̃^{(r-1)}(t)/(r-1)!` (JTNB (8.6); docs/window/proof.md §1).
(`tsum`: `Stmt_LinearForm` proves that the series converges, so no junk value enters.) -/
def Fn (c : Config) (n : ℕ) : ℝ :=
  ∑' t : ℕ, (term c n t : ℝ)

/-- `ζ(s) = ∑_{m ≥ 1} m^{-s}` as a real number (`Stmt_ZetaReal`: equals `riemannZeta s` for `s ≥ 2`). -/
def zetaR (s : ℕ) : ℝ :=
  ∑' m : ℕ, 1 / ((m : ℝ) + 1) ^ s

/-- Generalised harmonic number `H^{(s)}_N = ∑_{l=1}^{N} l^{-s}`. -/
def harm (N s : ℕ) : ℚ :=
  ∑ l ∈ Icc 1 N, 1 / (l : ℚ) ^ s

/-! ## Bricks and Laurent coefficients (JTNB (7.3), (8.7), p. 281) -/

/-- Taylor expansion at `t = -k` of the polynomial brick `(t+b)(t+b+1)⋯(t+a-1)/(a-b)!`
(`a ≥ b`, JTNB (7.3)): `∏_{i=b}^{a-1} (i - k + ε) / (a-b)!`. -/
def polyBrick (a b k : ℕ) : PowerSeries ℚ :=
  C (1 / ((a - b).factorial : ℚ)) * ∏ i ∈ Ico b a, (C ((i : ℚ) - k) + X)

/-- Expansion at `t = -k` of `(t+k) · (b-a-1)!/((t+a)(t+a+1)⋯(t+b-1))` (the rational brick of
JTNB (7.3), `a < b`, times the factor `t + k` that JTNB Lemmas 16, 18 attach to it).  If `a ≤ k < b`
the factor `t + k` cancels the pole; otherwise it is the factor `ε`. -/
def ratBrick (a b k : ℕ) : PowerSeries ℚ :=
  if a ≤ k ∧ k < b then
    C ((b - a - 1).factorial : ℚ) * (∏ i ∈ (Ico a b).erase k, (C ((i : ℚ) - k) + X))⁻¹
  else
    C ((b - a - 1).factorial : ℚ) * X * (∏ i ∈ Ico a b, (C ((i : ℚ) - k) + X))⁻¹

/-- `G_k(ε) = ε^{q-r} R̃(-k + ε)`, as the product of bricks:
`(h₀-2k+2ε) ∏_{j≤r} P_j(-k+ε) Q_j(-k+ε) ∏_{j>r} ε S_j(-k+ε)`, where
`P_j = polyBrick h_j 1`, `Q_j = polyBrick h₀ (h₀-h_j+1)`, `ε S_j = ratBrick h_j (h₀-h_j+1)`. -/
def Gk (c : Config) (n k : ℕ) : PowerSeries ℚ :=
  (C ((c.h0 n : ℚ) - 2 * k) + C 2 * X) *
    (∏ j ∈ Icc 1 c.r,
      (polyBrick (c.h n j) 1 k * polyBrick (c.h0 n) (c.h0 n - c.h n j + 1) k)) *
    ∏ j ∈ Icc (c.r + 1) c.q, ratBrick (c.h n j) (c.h0 n - c.h n j + 1) k

/-- Laurent coefficient `B_{j,k} = [ε^{q-j}] G_k`: the coefficient of `(t+k)^{-(j-r)}` in the
partial-fraction expansion of `R̃` (`r+1 ≤ j ≤ q`; JTNB p. 281). -/
def B (c : Config) (n j k : ℕ) : ℚ :=
  coeff (c.q - j) (Gk c n k)

/-- The pole range `h₁ ≤ k ≤ h₀ - h₁` (all poles `t = -k` of `R̃` lie in it; it is symmetric under
`k ↦ h₀ - k`). -/
def Krange (c : Config) (n : ℕ) : Finset ℕ :=
  Icc (c.h n 1) (c.h0 n - c.h n 1)

/-- Coefficient of `ζ(s)` in `F̃_n` (`r ≤ s ≤ q-1`): `A_s = C(s-1, r-1) ∑_k B_{s+1,k}` (JTNB (8.12)). -/
def Acoef (c : Config) (n s : ℕ) : ℚ :=
  (Nat.choose (s - 1) (c.r - 1) : ℚ) * ∑ k ∈ Krange c n, B c n (s + 1) k

/-- The rational part: `F̃_n = ∑_s A_s ζ(s) - A₀`,
`A₀ = ∑_{j=r+1}^{q} C(j-2, r-1) ∑_k B_{j,k} H^{(j-1)}_{k-h_1}` (JTNB p. 281; the harmonic numbers stop
at `k - h₁` because the sum over `t` may start at `t = 1 - h₁`, where `R̃` has zeros of order `r`). -/
def A0 (c : Config) (n : ℕ) : ℚ :=
  ∑ j ∈ Icc (c.r + 1) c.q, (Nat.choose (j - 2) (c.r - 1) : ℚ) *
    ∑ k ∈ Krange c n, B c n j k * harm (k - c.h n 1) (j - 1)

/-- The zeta values that survive: `ζ(r+2), ζ(r+4), …, ζ(q-2)` (for `cfgW`: `ζ(7), …, ζ(21)`). -/
def window (c : Config) : Finset ℕ :=
  (Icc (c.r + 2) (c.q - 2)).filter Odd

/-! ## Denominators (JTNB Lemma 19, (8.8), (8.9)) -/

/-- `m₀ = max{h_r - 1, h₀ - 2h_{r+1}}`. -/
def m0 (c : Config) (n : ℕ) : ℕ :=
  max (c.h n c.r - 1) (c.h0 n - 2 * c.h n (c.r + 1))

/-- `m_j = max{m₀, h₀ - h₁ - h_{r+j}}` (`j = 1..q-r`); for `cfgW`, `m_j = (63,63,62,61,60,…,60)·n`. -/
def mj (c : Config) (n j : ℕ) : ℕ :=
  max (m0 c n) (c.h0 n - c.h n 1 - c.h n (c.r + j))

/-- `D_{m₁}^r D_{m₂} ⋯ D_{m_{q-r}}`, `D_m = lcm(1, …, m)` (Mathlib's `Nat.lcmUpto`). -/
def Dprod (c : Config) (n : ℕ) : ℕ :=
  Nat.lcmUpto (mj c n 1) ^ c.r * ∏ j ∈ Icc 2 (c.q - c.r), Nat.lcmUpto (mj c n j)

/-- Zudilin's exponent `ω_{k,p}` (JTNB (8.9)), literally:
`∑_{j≤r} (⌊(k-1)/p⌋ + ⌊(h₀-k-1)/p⌋ - ⌊(k-h_j)/p⌋ - ⌊(h₀-h_j-k)/p⌋ - 2⌊(h_j-1)/p⌋)
 + ∑_{j>r} (⌊(h₀-2h_j)/p⌋ - ⌊(k-h_j)/p⌋ - ⌊(h₀-h_j-k)/p⌋)`. -/
def omegaKP (c : Config) (n p k : ℕ) : ℤ :=
  (∑ j ∈ Icc 1 c.r,
    (((k : ℤ) - 1) / p + ((c.h0 n : ℤ) - k - 1) / p - ((k : ℤ) - c.h n j) / p
      - ((c.h0 n : ℤ) - c.h n j - k) / p - 2 * (((c.h n j : ℤ) - 1) / p))) +
  ∑ j ∈ Icc (c.r + 1) c.q,
    (((c.h0 n : ℤ) - 2 * c.h n j) / p - ((k : ℤ) - c.h n j) / p - ((c.h0 n : ℤ) - c.h n j - k) / p)

/-- p-adic weight of the polynomial brick `polyBrick a b` at `t = -k` (JTNB (7.4), second form):
`⌊(k-b)/p⌋ - ⌊(k-a)/p⌋ - ⌊(a-b)/p⌋`. -/
def wPoly (a b k p : ℕ) : ℤ :=
  ((k : ℤ) - b) / p - ((k : ℤ) - a) / p - ((a : ℤ) - b) / p

/-- p-adic weight of the rational brick `ratBrick a b` at `t = -k` (JTNB (7.7)):
`⌊(b-a-1)/p⌋ - ⌊(k-a)/p⌋ - ⌊(b-1-k)/p⌋`. -/
def wRat (a b k p : ℕ) : ℤ :=
  ((b : ℤ) - a - 1) / p - ((k : ℤ) - a) / p - ((b : ℤ) - 1 - k) / p

/-- `ω_p = min_k ω_{k,p}`, the minimum over a full residue system `0 ≤ k < p` (`ω_{k,p}` is
`p`-periodic in `k`).  JTNB (8.9) takes the minimum over `h_{r+1} ≤ k ≤ h₀-h_{r+1}`.  Ours is never
larger (it is the minimum over all `k ∈ ℤ`), which only weakens `Stmt_Lemma19`.  The two agree for
every prime `p ≤ m_{q-r}` of `Φ_n` whenever `m_{q-r} ≤ h₀ - 2h_{r+1}` (then JTNB's range has
`h₀ - 2h_{r+1} + 1 > p` consecutive elements); this holds for `cfgW` (`m_{q-r} = h₀ - 2h_{r+1} = 60n`)
but not for every admissible configuration. -/
def omegaP (c : Config) (n p : ℕ) : ℤ :=
  if hp : 0 < p then (range p).inf' (nonempty_range_iff.2 hp.ne') (omegaKP c n p) else 0

/-- `Φ_n = ∏_{√h₀ < p ≤ m_{q-r}} p^{ω_p}` (JTNB (8.8)). -/
def PhiN (c : Config) (n : ℕ) : ℕ :=
  ∏ p ∈ (range (mj c n (c.q - c.r) + 1)).filter (fun p => p.Prime ∧ c.h0 n < p ^ 2),
    p ^ (omegaP c n p).toNat

/-- `Δ_n = D_{m₁}^r D_{m₂} ⋯ D_{m_{q-r}} / Φ_n` (a positive rational; JTNB Lemma 19). -/
def Delta (c : Config) (n : ℕ) : ℚ :=
  (Dprod c n : ℚ) / (PhiN c n : ℚ)

/-! ## The φ-function and its certified integral (JTNB p. 283–284; docs/window/proof.md §2) -/

/-- Zudilin's `φ₀(x, y)` (JTNB p. 283), 1-periodic in `x` and in `y`, over `ℚ`:
`∑_{j≤r} (⌊y⌋ + ⌊η₀x - y⌋ - ⌊y - η_j x⌋ - ⌊(η₀-η_j)x - y⌋ - 2⌊η_j x⌋)
 + ∑_{j>r} (⌊(η₀-2η_j)x⌋ - ⌊y - η_j x⌋ - ⌊(η₀-η_j)x - y⌋)`.
`ω_{k,p}(n) = φ₀(n/p, (k-1)/p)` (`Stmt_OmegaPhi0`). -/
def phi0 (c : Config) (x y : ℚ) : ℤ :=
  (∑ j ∈ Icc 1 c.r,
    (⌊y⌋ + ⌊(c.eta0 : ℚ) * x - y⌋ - ⌊y - (c.eta j : ℚ) * x⌋
      - ⌊((c.eta0 : ℚ) - c.eta j) * x - y⌋ - 2 * ⌊(c.eta j : ℚ) * x⌋)) +
  ∑ j ∈ Icc (c.r + 1) c.q,
    (⌊((c.eta0 : ℚ) - 2 * c.eta j) * x⌋ - ⌊y - (c.eta j : ℚ) * x⌋
      - ⌊((c.eta0 : ℚ) - c.eta j) * x - y⌋)

/-- An entry of the φ-table: the open interval `(an/ad, bn/bd) ⊂ (0, 1)` and the value `v`. -/
structure Piece where
  an : ℕ
  ad : ℕ
  bn : ℕ
  bd : ℕ
  v : ℕ

/-- Left end `a = an/ad`. -/
def Piece.a (e : Piece) : ℚ := (e.an : ℚ) / e.ad

/-- Right end `b = bn/bd`. -/
def Piece.b (e : Piece) : ℚ := (e.bn : ℚ) / e.bd

/-- `φ ≥ v` on the piece and on all its integer translates: for every `x` whose fractional part
lies in `(a, b)` and every `y`, `v ≤ φ₀(x, y)`. -/
def PieceValid (c : Config) (e : Piece) : Prop :=
  ∀ x y : ℚ, e.a < Int.fract x → Int.fract x < e.b → (e.v : ℤ) ≤ phi0 c x y

/-- `μ_j = m_j / n = max{η_r, η₀ - 2η_{r+1}, η₀ - η₁ - η_{r+j}}`. -/
def mu (c : Config) (j : ℕ) : ℕ :=
  max (max (c.eta c.r) (c.eta0 - 2 * c.eta (c.r + 1))) (c.eta0 - c.eta 1 - c.eta (c.r + j))

/-- `r μ₁ + μ₂ + ⋯ + μ_{q-r}` (`= 1341` for `cfgW`): `log D_{m₁}^r ⋯ D_{m_{q-r}} ~ muSum · n` (PNT). -/
def muSum (c : Config) : ℕ :=
  c.r * mu c 1 + ∑ j ∈ Icc 2 (c.q - c.r), mu c j

/-- Certified weight of a piece: `v · ((1/a - 1/b) [a ≥ 1/M] + ∑_{m=1}^{K} (1/(a+m) - 1/(b+m)))`,
a lower bound for `∫ φ(x) dx/x²` over `x ∈ (a,b) + {0, 1, …, K}`, `x ≥ 1/M`. -/
def phiWeight (M K : ℕ) (e : Piece) : ℚ :=
  (e.v : ℚ) * ((if 1 / (M : ℚ) ≤ e.a then 1 / e.a - 1 / e.b else 0) +
    ∑ m ∈ Icc 1 K, (1 / (e.a + m) - 1 / (e.b + m)))

/-- `∑_{pieces} phiWeight`: a certified lower bound for `∫_{1/M}^{∞} φ(x) dx/x²`. -/
def phiSumQ (T : List Piece) (M K : ℕ) : ℚ :=
  (T.map (phiWeight M K)).sum

/-! ## The two constants -/

/-- Certified rate of decay of `F̃_n` used by the assembly: `748.1 < C₀ = 750.71169483…`
(docs/window/proof.md §3.4 (S)). -/
def C0lo : ℚ := 7481 / 10

/-- Certified growth rate of `Δ_n` used by the assembly: `C₂ ≤ 1341 - 593.514… = 747.485… < 748`
(φ-table with `K = 20` translates). -/
def C2hi : ℚ := 748

/-! ## Basic API (proved here, available to every proof file) -/

theorem etaW_mono : Monotone etaW := by
  intro i j hij
  unfold etaW
  split_ifs <;> omega

theorem admissible_cfgW : Admissible cfgW where
  r_odd := by decide
  q_odd := by decide
  three_le_r := by decide
  r_add_four_le_q := by decide
  one_le_eta := by decide
  eta_mono := fun i j _ hij _ => etaW_mono hij
  two_eta_lt := by decide
  deg_cond := by decide

theorem window_cfgW : window cfgW = ({7, 9, 11, 13, 15, 17, 19, 21} : Finset ℕ) := by
  decide

theorem muSum_cfgW : muSum cfgW = 1341 := by
  decide

theorem Dprod_pos (c : Config) (n : ℕ) : 0 < Dprod c n := by
  unfold Dprod
  exact Nat.mul_pos (pow_pos (Nat.lcmUpto_pos _) _)
    (Finset.prod_pos fun j _ => Nat.lcmUpto_pos _)

theorem PhiN_pos (c : Config) (n : ℕ) : 0 < PhiN c n := by
  unfold PhiN
  apply Finset.prod_pos
  intro p hp
  simp only [Finset.mem_filter] at hp
  exact pow_pos hp.2.1.pos _

theorem Delta_pos (c : Config) (n : ℕ) : 0 < Delta c n := by
  unfold Delta
  have h1 : (0 : ℚ) < Dprod c n := by exact_mod_cast Dprod_pos c n
  have h2 : (0 : ℚ) < PhiN c n := by exact_mod_cast PhiN_pos c n
  exact div_pos h1 h2

end ZetaWindow

end
