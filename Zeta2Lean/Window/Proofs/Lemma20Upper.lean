module

public import Zeta2Lean.Window.Proofs.L20U.Landscape

@[expose] public section

set_option linter.style.header false
set_option linter.style.longLine false

/-!
# Upper bound `|F̃_n| ≤ e^{-748.1 n}` eventually (Theorem U of docs/proof.md §2.3)

**Proves `Stmt_L20Upper`**: `∀ᶠ n in atTop, |Fn cfgW n| ≤ exp (-(748.1 n))`, from the proved
`Stmt_PF`, `Stmt_CoeffVanish`, `Stmt_LinearForm`.

This is the upper half of JTNB Lemma 20 for `r = 5` (proved in JTNB only for `r = 3`).  The proof
is Theorem U of docs/proof.md (track `crude-upper-bound`, `docs/window/refine/crude-upper-bound.md`):
pointwise bounds on one fixed vertical line and a few certified numerical values.  It needs no
saddle point, no complex Stirling formula and no Olver asymptotics.

**Setting.**  `R(t) = (h₀+2t) ∏_{l=1}^{h₀-1} (t+l)⁵ / ∏_{j=1}^{23} ∏_{l=h_j}^{h₀-h_j} (t+l)`
(`deg R = -336n - 17`), `N_h = Nh cfgW n`, `term cfgW n t = [ε⁴] N_h R(t+ε)`, `Fn cfgW n = ∑' t, term`.

## Formal proof (helper modules `Proofs/L20U/*.lean`, namespace `ZetaWindow.L20U`)

* `VLine.lean` (verbatim from the pair project https://github.com/gmDevi/zeta2-7-9-lean,
  `Zeta2Lean/Pair/Proofs/Growth.lean`):
  Cauchy's theorem/formula of every order on right half-planes along vertical lines
  (`vline_higher`, `vline_left`), the half-integer kernels `kerS` (bounded on lines through
  integers, `O(e^{-2π Im t})`, conjugation symmetry), `acoef`, `coeff_inv_C_add_X_pow`.
* `Contour.lean` — **L1**.  `Pw n t = ∑_{j,k} B_{j,k} (t+k)^{-(j-5)}` and its Taylor coefficients
  `Dw n i`; `term = Dw n 4` and `Dw n 4 (-l) = 0` for `1 ≤ l ≤ 47n` (from `Stmt_PF`); the product
  form `Pw = Rw = N_h R` on `Re t > -h₁` (identity theorem, `Pw_eq_Rw`); decay `O(|t|⁻²)` (from
  `Stmt_CoeffVanish.ressum`); the representation
  `∫_ℝ Pw(M+iy) K₅(M+iy) dy = -2π F̃_n` on `M = 1/2 - n`, `K₅(t) = kerS 5 (t+1/2) = ∑_ν (t-ν)^{-5}`
  (`line_rep`; `Stmt_LinearForm` gives the summability), hence
  `|F̃_n| ≤ (1/π) ‖∫_0^∞ Pw K₅(M+iy) dy‖` (`abs_Fn_le`).
* `Gf.lean` — **L3**.  `Gf(a,y) = (a/2)log(a²+y²) + y arctan(a/y) - a`; window comparison of
  `∑ log|t+l|` with `∫ log|t+u| du` for **every** `y > 0` (`num_window`: the one uncovered unit
  interval `[-1/2, 1/2]` costs `1 + log 2`; `den_window`), shifts of the endpoints (`Gf_shift_le`).
* `Pointwise.lean` — **L2 + L4**.  `‖K₅(M+iy)‖ ≤ κ e^{-2πy}` (`Kw_bound`); Stirling bounds for
  `N_h` (`log_Nh_le`); scaling `Gf(na, nη) = n Gf(a, η) + n a log n` (the `n log n` terms cancel:
  `336 + 5·160 - 1136 = 0`); result
  `‖Pw(M+iy) K₅(M+iy)‖ ≤ A (163n + y)^34 exp(n U(y/n))` for `n ≥ 2`, `y > 0` (`norm_PK_le`), with
  `U(η) = C_η - 336 + 5[Gf(159,η) - Gf(-1,η)] - ∑_j [Gf(159-η_j,η) - Gf(η_j-1,η)] - 2πη` (`Uw`).
  The line is compared with `x₀ = 159` directly (endpoint shifts `5/2, 1/2, 3/2, 1/2` at cost
  `O(log(163n + y))`), so the `x`-Lipschitz constant `B` of the informal proof is not needed.
* `Landscape.lean` — **L5**.  `U(η) ≤ -749` for `η > 0` and `U(η) ≤ -749 - (η-60)/10` for `η ≥ 60`
  (`Uw_le`, `Uw_le_tail`): concavity on `(0, 46]`, tangent at `p = 9` (`U(9) = -750.6313…`,
  `U'(9) = 0.01474…`, so `C₀' = 750.086 > 749`), `U' < 0` on `[46, 60]`, `U' ≤ -1/10` on `[60, ∞)`.
* `Numerics.lean` (verbatim from the pair project's `Landscape/Numerics.lean`) and `Cert.lean`
  (**generated** by `L20U/gen/gen_cert.py`, exact rationals; regenerate with
  `python3 Zeta2Lean/Window/Proofs/L20U/gen/gen_cert.py Zeta2Lean/Window/Proofs/L20U/Cert.lean`,
  byte-identical): 59 `log` and 86 `arctan` enclosures, each re-checked by `norm_num`, and the
  expansions of `C_η`, `U(9)`, `U'(9)` (`Ceta_le`, `Uw9_le`, `dUw9_le`, `dUw9_ge`, `cell_le`, `tail_le`).
* Here: splitting `∫_0^∞ = ∫_0^{60n} + ∫_{60n}^∞` gives `|F̃_n| ≤ C n^35 e^{-749 n}` for `n ≥ 4`
  (`Fn_bound`), and `C n^35 ≤ e^{0.9 n}` eventually.

**Status: done** (2026-09-26, window prove round 1; complete, no gaps; `#print axioms L20Upper_proof`:
`[propext, Classical.choice, Quot.sound]`; `leanchecker` replays all eight modules).  Nothing
depends on the informal proof's certificate files; the only numerical inputs are the enclosures
of `Cert.lean`, all kernel-checked.

## Informal proof (crude-upper-bound.md §§1–7), for reference

* **L1 (contour).**  For `M ∈ ℤ + 1/2`, `-h₁ < M < 0`:
  `F̃_n = -(N_h/2πi) ∫_{M-i∞}^{M+i∞} K₅(t) R(t) dt`.
* **L2 (kernel).**  On `Re t ∈ ℤ + 1/2`: `|K₅(M+is)| ≤ (8π⁵/3) e^{-2π|s|}` (here: any constant).
* **L3 (window comparison).**  `∑_{l=A}^{B} log|t+l| ≤ ∫_{A-1}^{B+1} + 1 + log 2` and
  `≥ ∫_{A-1}^{B}` if `M + A - 1 ≥ 0`.
* **L4 (pointwise bound).**  `log(N_h |K₅ R|) ≤ n U(x, η) + O(log n + log(1 + |η|))`.
* **L5 (landscape on `x₀ = 159`).**  Concavity on `[0, 46]`, one tangent, one monotone cell, tail.
* **Assembly.**  `|F̃_n| ≤ K n^{16} e^{-C₀' n}` with `C₀' = 750.618` (informal proof, `p = 181/20`);
  the formal proof uses `p = 9` and the rate `749` (any rate `> 748.1` suffices).

## Numerical check

`python/window_mirror.py`, section "Stmt_L20Upper": the recorded exact values
`log|F̃_n|/n = -799.45, -779.72, …, -759.21` (`n = 1..9`) are all `≤ -748.1`; the contour
representation L1 reproduces them to `4.5·10⁻¹³` (crude-upper-bound.md §8).
-/

open Complex MeasureTheory Filter Topology Set Finset
open scoped Real

noncomputable section

namespace ZetaWindow

namespace L20U

/-- Polynomials are eventually dominated by `exp(δ m)` (pair project, any degree). -/
theorem eventually_poly_le_exp' (A : ℝ) {δ : ℝ} (hδ : 0 < δ) (k : ℕ) :
    ∀ᶠ m : ℕ in atTop, A * (m : ℝ) ^ k ≤ Real.exp (δ * m) := by
  have hA1 : 0 < |A| + 1 := by positivity
  have h1 := (isLittleO_pow_exp_pos_mul_atTop k hδ).def (c := 1 / (|A| + 1)) (by positivity)
  have h2 := tendsto_natCast_atTop_atTop.eventually h1
  filter_upwards [h2] with m hm
  rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (by positivity),
    abs_of_pos (Real.exp_pos _)] at hm
  have hmk : 0 ≤ (m : ℝ) ^ k := by positivity
  calc A * (m : ℝ) ^ k ≤ (|A| + 1) * (m : ℝ) ^ k := by
        gcongr; linarith [le_abs_self A]
    _ ≤ (|A| + 1) * (1 / (|A| + 1) * Real.exp (δ * m)) := by gcongr
    _ = Real.exp (δ * m) := by field_simp

/-- `(163n + y)^34 ≤ (223n)^34 e^{(y - 60n)/20}` for `n ≥ 4`, `y ≥ 60n`. -/
theorem poly_tail_le {n : ℝ} (hn : 4 ≤ n) {y : ℝ} (hy : 60 * n ≤ y) :
    (163 * n + y) ^ 34 ≤ (223 * n) ^ 34 * Real.exp ((y - 60 * n) / 20) := by
  have hn0 : 0 < n := by linarith
  have h1 : 163 * n + y ≤ 223 * n * Real.exp ((y - 60 * n) / (223 * n)) := by
    have := Real.add_one_le_exp ((y - 60 * n) / (223 * n))
    have e : 223 * n * ((y - 60 * n) / (223 * n) + 1) = 163 * n + y := by field_simp; ring
    calc 163 * n + y = 223 * n * ((y - 60 * n) / (223 * n) + 1) := e.symm
      _ ≤ _ := by gcongr
  have h2 : (163 * n + y) ^ 34 ≤ (223 * n * Real.exp ((y - 60 * n) / (223 * n))) ^ 34 :=
    pow_le_pow_left₀ (by linarith) h1 34
  refine le_trans h2 ?_
  rw [mul_pow, ← Real.exp_nat_mul]
  gcongr
  push_cast
  rw [mul_div_assoc']
  rw [div_le_div_iff₀ (by positivity) (by norm_num)]
  have : 0 ≤ y - 60 * n := by linarith
  nlinarith

/-- **Theorem U** (formal version, rate `749`): `|F̃_n| ≤ C n^35 e^{-749 n}` for all `n ≥ 4`. -/
theorem Fn_bound (hPF : Stmt_PF) (hV : Stmt_CoeffVanish) (hLF : Stmt_LinearForm) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ n : ℕ, 4 ≤ n →
      |Fn cfgW n| ≤ C * (n : ℝ) ^ 35 * Real.exp (-(749 * n)) := by
  obtain ⟨A, hA0, hA⟩ := norm_PK_le hPF
  refine ⟨80 * A * 223 ^ 34 / π, by positivity, fun n hn => ?_⟩
  have hn1 : 1 ≤ n := by omega
  have hn2 : 2 ≤ n := by omega
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn1
  have hn4 : (4 : ℝ) ≤ n := by exact_mod_cast hn
  set f : ℝ → ℂ := fun y => Pw n ((Mn n : ℂ) + y * I) * Kw ((Mn n : ℂ) + y * I) with hf
  have hint : Integrable f := line_integrable hV hn1
  have h1 := abs_Fn_le hPF hV hLF hn1
  set E : ℝ := A * (223 * n) ^ 34 * Real.exp (-(749 * n)) with hE
  have hE0 : 0 ≤ E := by positivity
  have hN60 : (0 : ℝ) ≤ 60 * n := by positivity
  have hsplit : ∫ y in Ioi (0 : ℝ), f y =
      (∫ y in Ioc (0 : ℝ) (60 * n), f y) + ∫ y in Ioi (60 * (n : ℝ)), f y := by
    rw [← setIntegral_union (Ioc_disjoint_Ioi le_rfl) measurableSet_Ioi hint.integrableOn
      hint.integrableOn, Ioc_union_Ioi_eq_Ioi hN60]
  -- the part `0 < y ≤ 60 n`: `U ≤ -749`
  have hB1 : ‖∫ y in Ioc (0 : ℝ) (60 * n), f y‖ ≤ E * (60 * n) := by
    have hbd : ∀ y ∈ Ioc (0 : ℝ) (60 * n), ‖f y‖ ≤ E := by
      intro y hy
      have h := hA n hn2 y hy.1
      have hU := Uw_le (y / n) (by have := hy.1; positivity)
      calc ‖f y‖ ≤ A * (163 * n + y) ^ 34 * Real.exp (n * Uw (y / n)) := h
        _ ≤ A * (223 * n) ^ 34 * Real.exp (-(749 * n)) := by
          gcongr
          · have := hy.1; positivity
          · linarith [hy.2]
          · nlinarith
    refine le_trans (norm_setIntegral_le_of_norm_le_const measure_Ioc_lt_top hbd) ?_
    rw [Real.volume_real_Ioc_of_le hN60, sub_zero, mul_comm]
  -- the part `y > 60 n`: `U ≤ -749 - (η - 60)/10`
  have hB2 : ‖∫ y in Ioi (60 * (n : ℝ)), f y‖ ≤ E * 20 := by
    have hbd : ∀ᵐ y ∂(volume.restrict (Ioi (60 * (n : ℝ)))), ‖f y‖ ≤
        A * (223 * n) ^ 34 * Real.exp ((-(749 * n) + 3 * n) - 1 / 20 * y) := by
      refine (ae_restrict_iff' measurableSet_Ioi).mpr (Eventually.of_forall fun y hy => ?_)
      have hy' : 60 * (n : ℝ) ≤ y := le_of_lt hy
      have hy0 : 0 < y := by linarith
      have h := hA n hn2 y hy0
      have hU := Uw_le_tail (y / n) (by rw [le_div_iff₀ hn0]; linarith)
      have hP := poly_tail_le hn4 hy'
      have hnU : (n : ℝ) * Uw (y / n) ≤ -(749 * n) - (y - 60 * n) / 10 := by
        have e : (n : ℝ) * (-749 - (y / n - 60) / 10) = -(749 * n) - (y - 60 * n) / 10 := by
          field_simp
        rw [← e]
        exact mul_le_mul_of_nonneg_left hU hn0.le
      calc ‖f y‖ ≤ A * (163 * n + y) ^ 34 * Real.exp (n * Uw (y / n)) := h
        _ ≤ A * ((223 * n) ^ 34 * Real.exp ((y - 60 * n) / 20)) *
            Real.exp (-(749 * n) - (y - 60 * n) / 10) := by
          gcongr
        _ = A * (223 * n) ^ 34 * Real.exp ((-(749 * n) + 3 * n) - 1 / 20 * y) := by
          have e : (y - 60 * (n : ℝ)) / 20 + (-(749 * n) - (y - 60 * n) / 10) =
              (-(749 * n) + 3 * n) - 1 / 20 * y := by ring
          rw [← e, Real.exp_add]
          ring
    have hgint : Integrable (fun y : ℝ => A * (223 * n) ^ 34 *
        Real.exp ((-(749 * n) + 3 * n) - 1 / 20 * y)) (volume.restrict (Ioi (60 * (n : ℝ)))) :=
      (integrableOn_exp_affine_Ioi _ _ _ (by norm_num)).const_mul _
    refine le_trans (norm_integral_le_of_norm_le hgint hbd) (le_of_eq ?_)
    rw [integral_const_mul, integral_exp_affine_Ioi _ _ _ (by norm_num), hE]
    have e : (-(749 * (n : ℝ)) + 3 * n) - 1 / 20 * (60 * n) = -(749 * n) := by ring
    rw [e]
    ring
  have hpi : 0 < π := Real.pi_pos
  rw [hsplit] at h1
  have h2 : ‖(∫ y in Ioc (0 : ℝ) (60 * n), f y) + ∫ y in Ioi (60 * (n : ℝ)), f y‖ ≤
      E * (60 * n) + E * 20 := le_trans (norm_add_le _ _) (add_le_add hB1 hB2)
  refine le_trans h1 ?_
  rw [div_le_iff₀ hpi]
  refine le_trans h2 ?_
  have e2 : 80 * A * 223 ^ 34 / π * (n : ℝ) ^ 35 * Real.exp (-(749 * n)) * π =
      E * (80 * n) := by
    rw [hE]; field_simp
  rw [e2]
  nlinarith

end L20U

theorem L20Upper_proof (hPF : Stmt_PF) (hV : Stmt_CoeffVanish) (hLF : Stmt_LinearForm) :
    Stmt_L20Upper := by
  obtain ⟨C, hC0, hC⟩ := L20U.Fn_bound hPF hV hLF
  unfold Stmt_L20Upper
  filter_upwards [L20U.eventually_poly_le_exp' C (δ := 9 / 10) (by norm_num) 35,
    eventually_ge_atTop 4] with n hpoly hn
  refine le_trans (hC n hn) ?_
  have hC0lo : ((C0lo : ℚ) : ℝ) = 7481 / 10 := by unfold C0lo; push_cast; ring
  rw [hC0lo]
  calc C * (n : ℝ) ^ 35 * Real.exp (-(749 * n))
      ≤ Real.exp (9 / 10 * n) * Real.exp (-(749 * n)) := by gcongr
    _ = Real.exp (-(7481 / 10 * n)) := by rw [← Real.exp_add]; congr 1; ring

end ZetaWindow

end
