import Zeta2Lean.Window.PhiTable
import Zeta2Lean.Cited.PNTStatement

/-!
# Zeta2Lean.Window.Statements — one `Prop` per lemma of the window proof

Every lemma is a `def Stmt_X : Prop` (or a `structure` with named fields); `Window/Proofs/*.lean`
prove them, taking the statements they depend on as *hypotheses*; `Window/Assembly.lean` derives
`MainStatement` from the top-level ones; `Window/Main.lean` wires everything together.
Map: `BLUEPRINT_WINDOW.md`.

**Route R2 of docs/proof.md §6.**  JTNB Lemma 20 (the asymptotics of `F̃_n`) is proved in JTNB
only for `r = 3`.  The formalisation does not need it: two statements replace it, both proved in
`docs/proof.md` without any saddle-point analysis:
* `Stmt_L20Upper` — `|F̃_n| ≤ e^{-748.1 n}` eventually (Theorem U: pointwise bounds on the fixed
  contour `Re t = 1/2 - n`, certified numerics);
* `Stmt_AuxPrime` — `v_ℓ(A₀) < 0 ≤ v_ℓ(A_s)` at the auxiliary primes `ℓ = 63 n - 1` (Theorem N:
  elementary `ℓ`-adic bookkeeping).  It replaces a statement `F̃_n ≠ 0` infinitely often, whose
  proof would need the saddle-point asymptotics; `Window/Assembly.lean` derives the nonvanishing
  from it under the rationality hypothesis, with Dirichlet's theorem.
Both are stated in the weakest form `Window/Assembly.lean` uses.  Every statement of this file is
proved in `Window/Proofs/`.

**Prime number theorem and Dirichlet's theorem.**  `Zeta2.PNT_Stmt` (`ψ(x)/x → 1`,
`Zeta2Lean/Cited/PNTStatement.lean`) is proved in `Zeta2Lean/Cited/PNT.lean`
(`Zeta2.Cited.pnt_of_stmts Zeta2.Cited.WienerIkehara_proof`), and `Window/Main.lean` uses that
proof.  Dirichlet's theorem on primes in progressions is Mathlib's
`Nat.forall_exists_prime_gt_and_modEq`.

References: "JTNB" = Zudilin, J. Théor. Nombres Bordeaux 16 (2004), §§7–8; `docs/proof.md` = the
informal proof of the window theorem (tracks in `docs/window/refine/`); `docs/window/proof.md` =
its first version (route R4 of `docs/proof.md` §6, with the saddle-point analysis).
-/

set_option linter.style.longLine false

open Filter Topology Finset PowerSeries

noncomputable section

namespace ZetaWindow

/-! ## The main statement (Mathlib notions only) -/

/-- **Main theorem** (target): at least one of `ζ(7), ζ(9), …, ζ(21)` is irrational. -/
def MainStatement : Prop :=
  ¬ ∀ k ∈ ({7, 9, 11, 13, 15, 17, 19, 21} : Finset ℕ), ∃ q : ℚ, riemannZeta (k : ℂ) = (q : ℂ)

/-! ## Glue: zeta values and the criterion -/

/-- `riemannZeta s = ∑_{m ≥ 1} m^{-s}` for integers `s ≥ 2`, as a real number. -/
def Stmt_ZetaReal : Prop :=
  ∀ s : ℕ, 2 ≤ s → riemannZeta (s : ℂ) = ((zetaR s : ℝ) : ℂ)

/-- **Irrationality criterion** (JTNB Proposition 5, elementary part; docs/window/proof.md §4).  If
`F_n = -a₀(n) + ∑_{s ∈ S} a_s(n) ζ_s` with `Δ_n a₀(n), Δ_n a_s(n) ∈ ℤ`, `0 < Δ_n ≤ e^{c₂ n}`,
`|F_n| ≤ e^{-c₀ n}` with `c₂ < c₀`, and `F_n ≠ 0` infinitely often, then the `ζ_s` (`s ∈ S`) are not
all rational.  (Proof: with a common denominator `d` of the `ζ_s`, `d Δ_n F_n ∈ ℤ` and
`|d Δ_n F_n| ≤ d e^{(c₂-c₀) n} < 1` eventually, so `F_n = 0` eventually.)  `Window/Assembly.lean`
derives the hypothesis "`F_n ≠ 0` infinitely often" inside the proof by contradiction, i.e. under
the rationality assumption, from `Stmt_AuxPrime`. -/
def Stmt_Criterion : Prop :=
  ∀ (S : Finset ℕ) (ζs : ℕ → ℝ) (Δ : ℕ → ℚ) (a0 : ℕ → ℚ) (a : ℕ → ℕ → ℚ) (F : ℕ → ℝ)
    (c2 c0 : ℝ),
    c2 < c0 →
    (∀ᶠ n in atTop, 0 < Δ n) →
    (∀ᶠ n in atTop, F n = -(a0 n : ℝ) + ∑ s ∈ S, (a n s : ℝ) * ζs s) →
    (∀ᶠ n in atTop, ∃ z : ℤ, Δ n * a0 n = z) →
    (∀ᶠ n in atTop, ∀ s ∈ S, ∃ z : ℤ, Δ n * a n s = z) →
    (∀ᶠ n in atTop, (Δ n : ℝ) ≤ Real.exp (c2 * n)) →
    (∀ᶠ n in atTop, |F n| ≤ Real.exp (-(c0 * n))) →
    (∃ᶠ n in atTop, F n ≠ 0) →
    ¬ ∀ s ∈ S, ∃ q : ℚ, ζs s = q

/-! ## The linear form (JTNB (8.4)–(8.7), p. 281; docs/window/proof.md §1) -/

/-- **Partial fractions** of `R̃` at every non-pole `y`, as Taylor expansions:
`R̃(y + ε) = ∑_{j=r+1}^{q} ∑_{k ∈ Krange} B_{j,k} (y + k + ε)^{-(j-r)}`. -/
def Stmt_PF : Prop :=
  ∀ c : Config, Admissible c → ∀ n : ℕ, 1 ≤ n → ∀ y : ℚ, (∀ k ∈ Krange c n, y + k ≠ 0) →
    Rser c n y = ∑ j ∈ Icc (c.r + 1) c.q, ∑ k ∈ Krange c n,
      C (B c n j k) * ((C (y + k) + X) ^ (j - c.r))⁻¹

/-- **Vanishing sums** (JTNB p. 282): the symmetry `R̃(-t-h₀) = -R̃(t)` (JTNB (8.5)) gives
`B_{j,h₀-k} = (-1)^j B_{j,k}` (hence `A_s = 0` for even `s`), and `deg R̃ ≤ -2` (JTNB (8.3)) gives
`∑_k B_{r+1,k} = 0` (the sum of the residues; hence `A_r = 0`). -/
structure Stmt_CoeffVanish : Prop where
  symm : ∀ c : Config, Admissible c → ∀ n : ℕ, 1 ≤ n → ∀ j k : ℕ, j ∈ Icc (c.r + 1) c.q →
    k ∈ Krange c n → B c n j (c.h0 n - k) = (-1) ^ j * B c n j k
  ressum : ∀ c : Config, Admissible c → ∀ n : ℕ, 1 ≤ n →
    ∑ k ∈ Krange c n, B c n (c.r + 1) k = 0

/-- **The linear form** (JTNB Lemma 19, first half; docs/window/proof.md §1): the series `∑_t R̃^{(r-1)}(t)/(r-1)!`
converges to `-A₀ + ∑_{s ∈ window} A_s ζ(s)`, `window = {r+2, r+4, …, q-2}`. -/
def Stmt_LinearForm : Prop :=
  ∀ c : Config, Admissible c → ∀ n : ℕ, 1 ≤ n →
    HasSum (fun t : ℕ => (term c n t : ℝ))
      (-(A0 c n : ℝ) + ∑ s ∈ window c, (Acoef c n s : ℝ) * zetaR s)

/-! ## Arithmetic (JTNB Lemmas 15–19; docs/window/proof.md §2) -/

/-- **Integrality of bricks** (JTNB Lemmas 15, 16): `D_{a-b}^i [ε^i] P(-k+ε) ∈ ℤ` for the polynomial
brick (every `k`), and `D_{b₀-a₀-1}^i [ε^i] (ε S(-k+ε)) ∈ ℤ` for the rational brick when
`a₀ ≤ a < b ≤ b₀`, `a₀ ≤ k < b₀`. -/
structure Stmt_BrickInt : Prop where
  poly : ∀ a b k i : ℕ, b ≤ a →
    ∃ z : ℤ, (Nat.lcmUpto (a - b) : ℚ) ^ i * coeff i (polyBrick a b k) = z
  rat : ∀ a b k a0 b0 i : ℕ, a0 ≤ a → a < b → b ≤ b0 → a0 ≤ k → k < b0 →
    ∃ z : ℤ, (Nat.lcmUpto (b0 - a0 - 1) : ℚ) ^ i * coeff i (ratBrick a b k) = z

/-- **p-adic valuation of bricks** (JTNB Lemmas 17, 18): for a prime `p` with `N < p²` (all numbers
involved are `≤ N`), `ord_p [ε^i] ≥ w - i` with the weights `wPoly`, `wRat` ((7.4), (7.7)). -/
structure Stmt_BrickVal : Prop where
  poly : ∀ a b k p N i : ℕ, p.Prime → 1 ≤ b → b ≤ a → a ≤ N → k ≤ N → N < p ^ 2 →
    coeff i (polyBrick a b k) ≠ 0 →
      wPoly a b k p - i ≤ padicValRat p (coeff i (polyBrick a b k))
  rat : ∀ a b k p N i : ℕ, p.Prime → 1 ≤ a → a < b → b ≤ N + 1 → k ≤ N → N < p ^ 2 →
    coeff i (ratBrick a b k) ≠ 0 →
      wRat a b k p - i ≤ padicValRat p (coeff i (ratBrick a b k))

/-- **Support of the Laurent coefficients**: `B_{j,k} = 0` unless `h_j ≤ k ≤ h₀ - h_j` (the pole of
`R̃` at `-k` has order `#{i > r : h_i ≤ k ≤ h₀-h_i}` at most; `η` is sorted). -/
def Stmt_LaurentSupp : Prop :=
  ∀ c : Config, Admissible c → ∀ n : ℕ, 1 ≤ n → ∀ j k : ℕ, j ∈ Icc (c.r + 1) c.q →
    (k < c.h n j ∨ c.h0 n - c.h n j < k) → B c n j k = 0

/-- **Rough integrality** (JTNB (8.10)): `D_{m₀}^{q-j} B_{j,k} ∈ ℤ`. -/
def Stmt_LaurentInt : Prop :=
  ∀ c : Config, Admissible c → ∀ n : ℕ, 1 ≤ n → ∀ j k : ℕ, j ∈ Icc (c.r + 1) c.q →
    k ∈ Krange c n → ∃ z : ℤ, (Nat.lcmUpto (m0 c n) : ℚ) ^ (c.q - j) * B c n j k = z

/-- **p-adic refinement** (JTNB (8.11)): `ord_p B_{j,k} ≥ ω_{k,p} - (q - j)` for primes `p > √h₀`. -/
def Stmt_LaurentVal : Prop :=
  ∀ c : Config, Admissible c → ∀ n : ℕ, 1 ≤ n → ∀ p : ℕ, p.Prime → c.h0 n < p ^ 2 →
    ∀ j k : ℕ, j ∈ Icc (c.r + 1) c.q → k ∈ Krange c n → B c n j k ≠ 0 →
      omegaKP c n p k - ((c.q - j : ℕ) : ℤ) ≤ padicValRat p (B c n j k)

/-- **Harmonic numbers**: `D_m^s H^{(s)}_N ∈ ℤ` for `N ≤ m`, and `ord_p H^{(s)}_N ≥ -s` when `N < p²`. -/
structure Stmt_Harmonic : Prop where
  int : ∀ N m s : ℕ, N ≤ m → ∃ z : ℤ, (Nat.lcmUpto m : ℚ) ^ s * harm N s = z
  val : ∀ N s p : ℕ, p.Prime → N < p ^ 2 → harm N s ≠ 0 → -(s : ℤ) ≤ padicValRat p (harm N s)

/-- **JTNB Lemma 19** (all odd `r`): `Δ_n A₀ ∈ ℤ` and `Δ_n A_s ∈ ℤ` (`r ≤ s ≤ q-1`), with
`Δ_n = D_{m₁}^r D_{m₂} ⋯ D_{m_{q-r}} / Φ_n`. -/
def Stmt_Lemma19 : Prop :=
  ∀ c : Config, Admissible c → ∀ n : ℕ, 1 ≤ n →
    (∃ z : ℤ, Delta c n * A0 c n = z) ∧
      ∀ s ∈ Icc c.r (c.q - 1), ∃ z : ℤ, Delta c n * Acoef c n s = z

/-! ## Growth of the denominators (JTNB p. 283–284, Proposition 5; docs/window/proof.md §2) -/

/-- `ω_{k,p}(n) = φ₀(n/p, (k-1)/p)`: each floor of JTNB (8.9) is a floor of JTNB's `φ₀`. -/
def Stmt_OmegaPhi0 : Prop :=
  ∀ (c : Config) (n p k : ℕ), 0 < p → omegaKP c n p k = phi0 c ((n : ℚ) / p) (((k : ℚ) - 1) / p)

/-- **The φ-certificate** (computer-assisted; docs/window/proof.md §2 "φ-integral"): every entry of the table
`phiTable` (2602 pieces, `Window/PhiTable.lean`) is valid, i.e. `φ₀(x, y) ≥ v` whenever the fractional
part of `x` lies in the piece. -/
def Stmt_PhiTable : Prop :=
  ∀ e ∈ phiTable, PieceValid cfgW e

/-- **Closed facts about the table** (decidable): the pieces are proper subintervals of `[0, 1]`, in
increasing order and disjoint, and the certified integral is large enough:
`muSum cfgW - phiSumQ phiTable 60 20 = 1341 - 593.5146… < C2hi = 748`. -/
structure Stmt_PhiData : Prop where
  bounds : ∀ e ∈ phiTable, 0 < e.ad ∧ 0 < e.bd ∧ 0 ≤ e.a ∧ e.a < e.b ∧ e.b ≤ 1
  sorted : phiTable.IsChain (fun e f => e.b ≤ f.a)
  sum : (muSum cfgW : ℚ) - phiSumQ phiTable (mu cfgW (cfgW.q - cfgW.r)) 20 < C2hi

/-- **Growth of `Δ_n`** (uses PNT): `Δ_n ≤ e^{748 n}` for all large `n` (true exponent
`C₂ = 1341 - ∫_{1/60}^∞ φ(x) dx/x² = 747.0513…`). -/
def Stmt_DenomGrowth : Prop :=
  ∀ᶠ n in atTop, (Delta cfgW n : ℝ) ≤ Real.exp ((C2hi : ℝ) * n)

/-! ## Upper bound for the linear forms (Lemma 20, upper half; docs/proof.md §2.3, Theorem U) -/

/-- **Upper bound** `|F̃_n| ≤ e^{-748.1 n}` for all large `n`.  Theorem U of docs/proof.md (track
`crude-upper-bound`, `docs/window/refine/crude-upper-bound.md`) proves
`|F̃_n| ≤ K n^{16} e^{-C₀' n}` for **every** `n ≥ 1`, with `C₀' = 750.6183158756…` and
`log K ≤ 116.92713` (contour `Re t = 1/2 - n`, pointwise bounds, one concavity lemma, ≈ 300
certified `log`/`arctan` enclosures), hence this statement for `n ≥ 74`.  The true rate is
`C₀ = 750.71169…` (docs/window/proof.md §3); any rate `> C2hi = 748` suffices here. -/
def Stmt_L20Upper : Prop :=
  ∀ᶠ n in atTop, |Fn cfgW n| ≤ Real.exp (-((C0lo : ℝ) * n))

/-! ## Nonvanishing: the auxiliary primes (docs/proof.md §2.2, Theorem N) -/

/-- **Auxiliary-prime separation** (Theorem N of docs/proof.md, track `aux-prime-nonvanishing`,
`docs/window/refine/aux-prime-nonvanishing.md`): for all large even `n` such that `ℓ = 63 n - 1` is
prime, `v_ℓ(A₀) < 0 ≤ v_ℓ(A_s)` for every `s` in the window.  Informally `v_ℓ(A₀) = -5` exactly, for
every even `n ≥ 2` with `ℓ` prime: `ℓ⁵ A₀ ≡ -4 Q₁ u (mod ℓ)` with an `ℓ`-unit `u` and
`Q₁ = 984698059590803/1545332660300000`.  The eventual form frees a proof from certifying that the
numerator of `Q₁` is prime (it suffices that `ℓ` exceeds it).

Use (`Window/Assembly.lean`): if the window values `ζ(s) = q_s` were rational, then for such `n`
with `ℓ` larger than their denominators, `F̃_n = -A₀ + ∑_s A_s q_s` has
`v_ℓ(F̃_n) = v_ℓ(A₀) < 0`, so `F̃_n ≠ 0`; Dirichlet's theorem (primes `≡ -1 (mod 126)`) gives
infinitely many such `n`.  This replaces the former `Stmt_L20Nonzero` (`F̃_n ≠ 0` infinitely
often), which needed the saddle-point asymptotics of docs/window/proof.md §3.6. -/
def Stmt_AuxPrime : Prop :=
  ∀ᶠ n in atTop, Even n → (63 * n - 1).Prime →
    padicValRat (63 * n - 1) (A0 cfgW n) < 0 ∧
      ∀ s ∈ window cfgW, 0 ≤ padicValRat (63 * n - 1) (Acoef cfgW n s)

end ZetaWindow

end
