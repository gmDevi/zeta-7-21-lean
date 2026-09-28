import Zeta2Lean.Window.Statements

set_option linter.style.header false
set_option linter.style.longLine false

/-!
# Theorem U, part 1: vertical-line integrals and the half-integer kernels

General complex-analysis toolkit for `Proofs/Lemma20Upper.lean` (Theorem U of docs/proof.md).
Every declaration of this file is copied **verbatim** from the proved pair project
(https://github.com/gmDevi/zeta2-7-9-lean, `Zeta2Lean/Pair/Proofs/Growth.lean`, same Lean/Mathlib
versions), only the namespace changed; nothing here depends on the window configuration.

* Cauchy's theorem and Cauchy's formula (all orders) for right half-planes, on vertical lines
  (`vline_integral_eq_zero`, `vline_cauchy`, `vline_left`, `vline_higher`), from
  `Complex.integral_boundary_rect_eq_zero_of_differentiableOn` and differentiation under the
  integral sign (`hasDerivAt_vline_integral`);
* the kernels `kerS s t = ∑_{ν ∈ ℤ} (t - ν - 1/2)^{-s}`: bounded on vertical lines through
  integers (`norm_kerS_vline_le`), exponentially decaying in the upper half-plane (`kerS_decay`,
  Eisenstein `q`-expansion), conjugation-symmetric, holomorphic off the half-integers;
* the Taylor coefficients `acoef` of `(x+ε)^{-i}` and the power-series inverse
  `coeff_inv_C_add_X_pow`; `integral_exp_affine_Ioi`.
-/

open Complex MeasureTheory Filter Topology Set Finset PowerSeries
open scoped Real

noncomputable section

namespace ZetaWindow

namespace L20U

/-! ## Vertical-line integrals -/

/-- A continuous function on `ℝ` bounded by `C/(1+y²)` is integrable. -/
theorem integrable_of_bound_inv_one_add_sq {g : ℝ → ℂ} (hg : Continuous g) {C : ℝ}
    (hC : ∀ y, ‖g y‖ ≤ C * (1 + y ^ 2)⁻¹) : Integrable g :=
  (integrable_inv_one_add_sq.const_mul C).mono' hg.aestronglyMeasurable (Eventually.of_forall hC)

/-- If `g` is continuous and `‖g y‖ ≤ C / y²` for `|y| ≥ r ≥ 1`, then `‖g y‖ ≤ K (1+y²)⁻¹`. -/
theorem exists_bound_inv_one_add_sq {g : ℝ → ℂ} (hg : Continuous g) {C r : ℝ} (hr : 1 ≤ r)
    (hC0 : 0 ≤ C) (hC : ∀ y, r ≤ |y| → ‖g y‖ ≤ C / y ^ 2) :
    ∃ K, ∀ y, ‖g y‖ ≤ K * (1 + y ^ 2)⁻¹ := by
  obtain ⟨M, hM⟩ := (isCompact_Icc (a := -r) (b := r)).exists_bound_of_continuousOn
    hg.continuousOn
  refine ⟨max (M * (1 + r ^ 2)) (2 * C), fun y => ?_⟩
  have hpos : 0 < 1 + y ^ 2 := by positivity
  by_cases hy : r ≤ |y|
  · have h1 := hC y hy
    have hy1 : 1 ≤ y ^ 2 := by
      have : 1 ≤ |y| := le_trans hr hy
      nlinarith [sq_abs y, abs_nonneg y]
    have hy2 : 0 < y ^ 2 := by linarith
    calc ‖g y‖ ≤ C / y ^ 2 := h1
      _ ≤ 2 * C * (1 + y ^ 2)⁻¹ := by
          rw [← div_eq_mul_inv, div_le_div_iff₀ hy2 hpos]
          nlinarith
      _ ≤ max (M * (1 + r ^ 2)) (2 * C) * (1 + y ^ 2)⁻¹ := by
          gcongr
          exact le_max_right _ _
  · push Not at hy
    have hy' : y ∈ Icc (-r) r := ⟨by linarith [neg_abs_le y], by linarith [le_abs_self y]⟩
    have h1 := hM y hy'
    have hM0 : 0 ≤ M := le_trans (norm_nonneg _) h1
    have hyr : y ^ 2 ≤ r ^ 2 := by
      have : |y| ≤ r := hy.le
      nlinarith [sq_abs y, abs_nonneg y]
    calc ‖g y‖ ≤ M := h1
      _ ≤ M * (1 + r ^ 2) * (1 + y ^ 2)⁻¹ := by
          rw [mul_assoc, ← div_eq_mul_inv]
          have : 1 ≤ (1 + r ^ 2) / (1 + y ^ 2) := by
            rw [le_div_iff₀ hpos]; linarith
          nlinarith
      _ ≤ max (M * (1 + r ^ 2)) (2 * C) * (1 + y ^ 2)⁻¹ := by
          gcongr
          exact le_max_left _ _

/-- The vertical line `y ↦ c + y i` is continuous. -/
theorem continuous_vline (c : ℝ) : Continuous fun y : ℝ => (c : ℂ) + (y : ℂ) * I := by
  fun_prop

theorem vline_re (c y : ℝ) : ((c : ℂ) + (y : ℂ) * I).re = c := by simp

theorem vline_im (c y : ℝ) : ((c : ℂ) + (y : ℂ) * I).im = y := by simp

theorem abs_le_norm_vline (c y : ℝ) : |y| ≤ ‖(c : ℂ) + (y : ℂ) * I‖ := by
  have := Complex.abs_im_le_norm ((c : ℂ) + (y : ℂ) * I)
  simpa using this

theorem abs_le_norm_vline_re (c y : ℝ) : |c| ≤ ‖(c : ℂ) + (y : ℂ) * I‖ := by
  have := Complex.abs_re_le_norm ((c : ℂ) + (y : ℂ) * I)
  simpa using this

/-- **Cauchy's theorem for a right half-plane.**  If `f` is holomorphic on `{Re t > c'}`, `c' < c`,
and `‖f t‖ ≤ C/‖t‖²` for `Re t ≥ c`, `‖t‖ ≥ r`, then `∫_ℝ f(c + y i) dy = 0` (and the integrand
is integrable). -/
theorem vline_integral_eq_zero {f : ℂ → ℂ} {c c' : ℝ} (hcc : c' < c)
    (hf : DifferentiableOn ℂ f {t | c' < t.re}) {C r : ℝ} (hr : 1 ≤ r) (hC0 : 0 ≤ C)
    (hC : ∀ t : ℂ, c ≤ t.re → r ≤ ‖t‖ → ‖f t‖ ≤ C / ‖t‖ ^ 2) :
    Integrable (fun y : ℝ => f (c + y * I)) ∧ ∫ y : ℝ, f (c + y * I) = 0 := by
  have hopen : IsOpen {t : ℂ | c' < t.re} := isOpen_lt continuous_const Complex.continuous_re
  have hcont : Continuous fun y : ℝ => f (c + y * I) := by
    refine hf.continuousOn.comp_continuous (continuous_vline c) fun y => ?_
    show c' < ((c : ℂ) + (y : ℂ) * I).re
    rw [vline_re]; exact hcc
  -- decay along the line
  have hdec : ∀ y : ℝ, r ≤ |y| → ‖f (c + y * I)‖ ≤ C / y ^ 2 := by
    intro y hy
    have hn := abs_le_norm_vline c y
    have h1 := hC _ (by rw [vline_re]) (le_trans hy hn)
    have hy0 : 0 < |y| := lt_of_lt_of_le (by linarith) hy
    calc ‖f (c + y * I)‖ ≤ C / ‖(c : ℂ) + (y : ℂ) * I‖ ^ 2 := h1
      _ ≤ C / y ^ 2 := by
          rw [← sq_abs y]
          apply div_le_div_of_nonneg_left hC0 (pow_pos hy0 2)
          exact pow_le_pow_left₀ (abs_nonneg _) hn 2
  obtain ⟨K, hK⟩ := exists_bound_inv_one_add_sq hcont hr hC0 hdec
  have hint : Integrable (fun y : ℝ => f (c + y * I)) :=
    integrable_of_bound_inv_one_add_sq hcont hK
  refine ⟨hint, ?_⟩
  -- rectangle estimate
  have hrect : ∀ R : ℝ, r + |c| + 1 ≤ R →
      ‖∫ y in (-R)..R, f (c + y * I)‖ ≤ C * (4 + 2 * |c|) / R := by
    intro R hR
    have hR1 : 1 ≤ R := by linarith [abs_nonneg c]
    have hRpos : 0 < R := by linarith
    have hcR : c ≤ R := by linarith [le_abs_self c]
    have hrR : r ≤ R := by linarith [abs_nonneg c]
    set z : ℂ := ⟨c, -R⟩
    set w : ℂ := ⟨R, R⟩
    have hsub : Set.uIcc z.re w.re ×ℂ Set.uIcc z.im w.im ⊆ {t : ℂ | c' < t.re} := by
      intro t ht
      rw [Complex.mem_reProdIm] at ht
      have h1 := ht.1
      simp only [z, w] at h1
      rw [Set.uIcc_of_le hcR] at h1
      show c' < t.re
      linarith [h1.1]
    have key := Complex.integral_boundary_rect_eq_zero_of_differentiableOn f z w (hf.mono hsub)
    simp only [z, w] at key
    -- bounds on the three other sides
    have hbot : ‖∫ x in c..R, f (↑x + ↑(-R) * I)‖ ≤ C / R ^ 2 * |R - c| := by
      apply intervalIntegral.norm_integral_le_of_norm_le_const
      intro x hx
      rw [Set.uIoc_of_le hcR] at hx
      have hre : c ≤ ((x : ℂ) + ((-R : ℝ) : ℂ) * I).re := by simp; exact hx.1.le
      have hn : R ≤ ‖(x : ℂ) + ((-R : ℝ) : ℂ) * I‖ := by
        have := abs_le_norm_vline x (-R)
        rwa [abs_neg, abs_of_pos hRpos] at this
      calc ‖f (↑x + ↑(-R) * I)‖ ≤ C / ‖(x : ℂ) + ((-R : ℝ) : ℂ) * I‖ ^ 2 :=
            hC _ hre (le_trans hrR hn)
        _ ≤ C / R ^ 2 := by
            apply div_le_div_of_nonneg_left hC0 (by positivity)
            exact pow_le_pow_left₀ hRpos.le hn 2
    have htop : ‖∫ x in c..R, f (↑x + ↑R * I)‖ ≤ C / R ^ 2 * |R - c| := by
      apply intervalIntegral.norm_integral_le_of_norm_le_const
      intro x hx
      rw [Set.uIoc_of_le hcR] at hx
      have hre : c ≤ ((x : ℂ) + (R : ℂ) * I).re := by simp; exact hx.1.le
      have hn : R ≤ ‖(x : ℂ) + (R : ℂ) * I‖ := by
        have := abs_le_norm_vline x R
        rwa [abs_of_pos hRpos] at this
      calc ‖f (↑x + ↑R * I)‖ ≤ C / ‖(x : ℂ) + (R : ℂ) * I‖ ^ 2 := hC _ hre (le_trans hrR hn)
        _ ≤ C / R ^ 2 := by
            apply div_le_div_of_nonneg_left hC0 (by positivity)
            exact pow_le_pow_left₀ hRpos.le hn 2
    have hright : ‖∫ y in (-R)..R, f (↑R + ↑y * I)‖ ≤ C / R ^ 2 * |R - (-R)| := by
      apply intervalIntegral.norm_integral_le_of_norm_le_const
      intro y _
      have hre : c ≤ ((R : ℂ) + (y : ℂ) * I).re := by simp; exact hcR
      have hn : R ≤ ‖(R : ℂ) + (y : ℂ) * I‖ := by
        have := abs_le_norm_vline_re R y
        rwa [abs_of_pos hRpos] at this
      calc ‖f (↑R + ↑y * I)‖ ≤ C / ‖(R : ℂ) + (y : ℂ) * I‖ ^ 2 := hC _ hre (le_trans hrR hn)
        _ ≤ C / R ^ 2 := by
            apply div_le_div_of_nonneg_left hC0 (by positivity)
            exact pow_le_pow_left₀ hRpos.le hn 2
    have heq : I • ∫ y in (-R)..R, f (↑c + ↑y * I) =
        ((∫ x in c..R, f (↑x + ↑(-R) * I)) - ∫ x in c..R, f (↑x + ↑R * I)) +
          I • ∫ y in (-R)..R, f (↑R + ↑y * I) := by
      exact (sub_eq_zero.mp key).symm
    have hnorm : ‖∫ y in (-R)..R, f (↑c + ↑y * I)‖ =
        ‖I • ∫ y in (-R)..R, f (↑c + ↑y * I)‖ := by
      rw [norm_smul, Complex.norm_I, one_mul]
    rw [hnorm, heq]
    have habs1 : |R - c| ≤ R + |c| := by
      rw [abs_le]; constructor <;> linarith [le_abs_self c, neg_abs_le c]
    have habs2 : |R - (-R)| = 2 * R := by rw [sub_neg_eq_add, ← two_mul, abs_of_pos (by linarith)]
    calc ‖((∫ x in c..R, f (↑x + ↑(-R) * I)) - ∫ x in c..R, f (↑x + ↑R * I)) +
          I • ∫ y in (-R)..R, f (↑R + ↑y * I)‖
        ≤ ‖∫ x in c..R, f (↑x + ↑(-R) * I)‖ + ‖∫ x in c..R, f (↑x + ↑R * I)‖ +
            ‖∫ y in (-R)..R, f (↑R + ↑y * I)‖ := by
          refine le_trans (norm_add_le _ _) ?_
          rw [norm_smul, Complex.norm_I, one_mul]
          gcongr
          exact norm_sub_le _ _
      _ ≤ C / R ^ 2 * |R - c| + C / R ^ 2 * |R - c| + C / R ^ 2 * |R - (-R)| := by
          gcongr
      _ ≤ C / R ^ 2 * (R + |c|) + C / R ^ 2 * (R + |c|) + C / R ^ 2 * (2 * R) := by
          rw [habs2]
          have : 0 ≤ C / R ^ 2 := by positivity
          gcongr
      _ = C * (4 * R + 2 * |c|) / R ^ 2 := by ring
      _ ≤ C * (4 + 2 * |c|) / R := by
          rw [div_le_div_iff₀ (by positivity) hRpos]
          have : 0 ≤ C * |c| * R * (R - 1) :=
            mul_nonneg (mul_nonneg (mul_nonneg hC0 (abs_nonneg c)) hRpos.le) (by linarith)
          nlinarith [this]
  -- pass to the limit
  have hlim : Tendsto (fun R : ℝ => ∫ y in (-R)..R, f (c + y * I)) atTop
      (𝓝 (∫ y : ℝ, f (c + y * I))) :=
    intervalIntegral_tendsto_integral hint tendsto_neg_atTop_atBot tendsto_id
  have hlim0 : Tendsto (fun R : ℝ => ∫ y in (-R)..R, f (c + y * I)) atTop (𝓝 0) := by
    have hb : Tendsto (fun R : ℝ => C * (4 + 2 * |c|) / R) atTop (𝓝 0) :=
      tendsto_const_nhds.div_atTop tendsto_id
    refine squeeze_zero_norm' ?_ hb
    filter_upwards [eventually_ge_atTop (r + |c| + 1)] with R hR
    exact hrect R hR
  exact tendsto_nhds_unique hlim hlim0

/-- The explicit kernel integral: `∫_ℝ ((c+iy-(c+p))⁻¹ - (c+iy-(c-p))⁻¹) dy = -2π` for `p > 0`. -/
theorem vline_integral_inv_sub {c p : ℝ} (hp : 0 < p) :
    Integrable (fun y : ℝ => ((c : ℂ) + y * I - ((c + p : ℝ) : ℂ))⁻¹ -
      ((c : ℂ) + y * I - ((c - p : ℝ) : ℂ))⁻¹) ∧
    ∫ y : ℝ, (((c : ℂ) + y * I - ((c + p : ℝ) : ℂ))⁻¹ -
      ((c : ℂ) + y * I - ((c - p : ℝ) : ℂ))⁻¹) = -2 * π := by
  have hpt : ∀ y : ℝ, ((c : ℂ) + y * I - ((c + p : ℝ) : ℂ))⁻¹ -
      ((c : ℂ) + y * I - ((c - p : ℝ) : ℂ))⁻¹ =
        (((-2 / p) * (1 + (p⁻¹ * y) ^ 2)⁻¹ : ℝ) : ℂ) := by
    intro y
    have h1 : (c : ℂ) + y * I - ((c + p : ℝ) : ℂ) = ((-p : ℝ) : ℂ) + (y : ℂ) * I := by
      push_cast; ring
    have h2 : (c : ℂ) + y * I - ((c - p : ℝ) : ℂ) = ((p : ℝ) : ℂ) + (y : ℂ) * I := by
      push_cast; ring
    rw [h1, h2]
    have hne1 : ((-p : ℝ) : ℂ) + (y : ℂ) * I ≠ 0 := by
      intro h
      have := congrArg Complex.re h
      simp at this
      linarith
    have hne2 : ((p : ℝ) : ℂ) + (y : ℂ) * I ≠ 0 := by
      intro h
      have := congrArg Complex.re h
      simp at this
      linarith
    have hreal : (-2 / p) * (1 + (p⁻¹ * y) ^ 2)⁻¹ = -(2 * p) / (p ^ 2 + y ^ 2) := by
      field_simp
    rw [hreal]
    have hprod : (((-p : ℝ) : ℂ) + (y : ℂ) * I) * (((p : ℝ) : ℂ) + (y : ℂ) * I) =
        -(((p ^ 2 + y ^ 2 : ℝ)) : ℂ) := by
      push_cast
      ring_nf
      rw [Complex.I_sq]
      ring
    rw [inv_sub_inv hne1 hne2, hprod]
    have hpy : ((p ^ 2 + y ^ 2 : ℝ) : ℂ) ≠ 0 := by
      have : (0 : ℝ) < p ^ 2 + y ^ 2 := by positivity
      exact_mod_cast this.ne'
    push_cast
    field_simp
    ring
  have hint : Integrable (fun y : ℝ => ((c : ℂ) + y * I - ((c + p : ℝ) : ℂ))⁻¹ -
      ((c : ℂ) + y * I - ((c - p : ℝ) : ℂ))⁻¹) := by
    simp_rw [hpt]
    exact ((integrable_inv_one_add_mul_sq (inv_ne_zero hp.ne')).const_mul (-2 / p)).ofReal
  refine ⟨hint, ?_⟩
  simp_rw [hpt]
  rw [integral_complex_ofReal, integral_const_mul, integral_univ_inv_one_add_mul_sq]
  rw [abs_inv, abs_of_pos hp]
  have hp0 : (p : ℂ) ≠ 0 := by exact_mod_cast hp.ne'
  push_cast
  field_simp

/-- **Cauchy's integral formula for a right half-plane** (simple pole):
`∫_ℝ F(c+iy) (c+iy-x)⁻¹ dy = -2π F(x)` for `x > c`, if `F` is holomorphic on `Re t > c'`
(`c' < c`) and `O(1/|t|)` there. -/
theorem vline_cauchy {F : ℂ → ℂ} {c c' : ℝ} (hcc : c' < c)
    (hF : DifferentiableOn ℂ F {t | c' < t.re}) {C r : ℝ} (hr : 1 ≤ r) (hC0 : 0 ≤ C)
    (hC : ∀ t : ℂ, c ≤ t.re → r ≤ ‖t‖ → ‖F t‖ ≤ C / ‖t‖) {x : ℝ} (hx : c < x) :
    ∫ y : ℝ, F (c + y * I) * ((c : ℂ) + y * I - x)⁻¹ = -2 * π * F x := by
  set p : ℝ := x - c with hp_def
  have hp : 0 < p := by rw [hp_def]; linarith
  set a : ℝ := c - p with ha_def
  have hxcp : x = c + p := by rw [hp_def]; ring
  set c'' : ℝ := max c' a with hc''
  have hc''c : c'' < c := max_lt hcc (by rw [ha_def]; linarith)
  set U : Set ℂ := {t | c'' < t.re} with hU
  have hUopen : IsOpen U := isOpen_lt continuous_const Complex.continuous_re
  have hUsub : U ⊆ {t | c' < t.re} := by
    intro t ht
    show c' < t.re
    exact lt_of_le_of_lt (le_max_left _ _) ht
  have hxU : (x : ℂ) ∈ U := by
    show c'' < ((x : ℂ)).re
    simp only [Complex.ofReal_re]; linarith
  set H : ℂ → ℂ := fun t => dslope F x t + F x * (t - a)⁻¹ with hH
  have hHdiff : DifferentiableOn ℂ H U := by
    refine DifferentiableOn.add ?_ ?_
    · exact (Complex.differentiableOn_dslope (hUopen.mem_nhds hxU)).2 (hF.mono hUsub)
    · refine DifferentiableOn.mul (differentiableOn_const _) ?_
      refine DifferentiableOn.inv (differentiableOn_id.sub (differentiableOn_const _)) ?_
      intro t ht h
      have : t.re = a := by
        have := congrArg Complex.re h
        simpa [sub_eq_zero] using this
      have h2 : c'' < t.re := ht
      have : a ≤ c'' := le_max_right _ _
      linarith
  -- decay of `H`
  set r₁ : ℝ := max r (2 * |x| + 2 * |a| + 1) with hr₁
  have hr₁1 : 1 ≤ r₁ := le_trans hr (le_max_left _ _)
  have hHdec : ∀ t : ℂ, c ≤ t.re → r₁ ≤ ‖t‖ →
      ‖H t‖ ≤ (2 * C + 4 * ‖F x‖ * |a - x|) / ‖t‖ ^ 2 := by
    intro t htre htn
    have htr : r ≤ ‖t‖ := le_trans (le_max_left _ _) htn
    have ht2 : 2 * |x| + 2 * |a| + 1 ≤ ‖t‖ := le_trans (le_max_right _ _) htn
    have htpos : 0 < ‖t‖ := by linarith [abs_nonneg x, abs_nonneg a]
    have hx2 : ‖t‖ / 2 ≤ ‖t - x‖ := by
      have := norm_sub_norm_le t (x : ℂ)
      rw [Complex.norm_real, Real.norm_eq_abs] at this
      linarith [abs_nonneg a]
    have ha2 : ‖t‖ / 2 ≤ ‖t - a‖ := by
      have := norm_sub_norm_le t (a : ℂ)
      rw [Complex.norm_real, Real.norm_eq_abs] at this
      linarith [abs_nonneg x]
    have htx : t ≠ (x : ℂ) := by
      intro h; rw [h, Complex.norm_real, Real.norm_eq_abs] at ht2
      linarith [abs_nonneg a, abs_nonneg x]
    have hta : t - a ≠ 0 := by
      intro h; rw [h, norm_zero] at ha2; linarith
    have htx' : t - x ≠ 0 := sub_ne_zero.mpr htx
    have hHt : H t = F t * (t - x)⁻¹ + F x * (a - x) * ((t - a)⁻¹ * (t - x)⁻¹) := by
      simp only [hH]
      rw [dslope_of_ne _ htx, slope_def_field]
      field_simp
      ring
    rw [hHt]
    have hn1 : ‖F t * (t - x)⁻¹‖ ≤ C / ‖t‖ * (2 / ‖t‖) := by
      rw [norm_mul, norm_inv]
      gcongr
      · exact hC t htre htr
      · rw [inv_le_comm₀ (by positivity) (by positivity)]
        rw [inv_div]; exact hx2
    have hn2 : ‖F x * (a - x) * ((t - a)⁻¹ * (t - x)⁻¹)‖ ≤
        ‖F x‖ * |a - x| * ((2 / ‖t‖) * (2 / ‖t‖)) := by
      rw [norm_mul, norm_mul, norm_mul, norm_inv, norm_inv]
      have : ‖((a : ℂ) - x)‖ = |a - x| := by
        rw [← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs]
      rw [this]
      gcongr
      · rw [inv_le_comm₀ (by positivity) (by positivity), inv_div]; exact ha2
      · rw [inv_le_comm₀ (by positivity) (by positivity), inv_div]; exact hx2
    calc ‖F t * (t - x)⁻¹ + F x * (a - x) * ((t - a)⁻¹ * (t - x)⁻¹)‖
        ≤ C / ‖t‖ * (2 / ‖t‖) + ‖F x‖ * |a - x| * ((2 / ‖t‖) * (2 / ‖t‖)) :=
          le_trans (norm_add_le _ _) (add_le_add hn1 hn2)
      _ = (2 * C + 4 * ‖F x‖ * |a - x|) / ‖t‖ ^ 2 := by
          field_simp
          ring
  obtain ⟨hHint, hHzero⟩ := vline_integral_eq_zero hc''c (hHdiff.mono fun t ht => ht) hr₁1
    (by positivity) hHdec
  obtain ⟨hKint, hKval⟩ := vline_integral_inv_sub (c := c) hp
  -- pointwise decomposition on the line
  have hdecomp : ∀ y : ℝ, F (c + y * I) * ((c : ℂ) + y * I - x)⁻¹ =
      H (c + y * I) + F x * (((c : ℂ) + y * I - ((c + p : ℝ) : ℂ))⁻¹ -
        ((c : ℂ) + y * I - ((c - p : ℝ) : ℂ))⁻¹) := by
    intro y
    have hne : (c : ℂ) + y * I ≠ (x : ℂ) := by
      intro h
      have := congrArg Complex.re h
      simp at this
      linarith
    have hne' : (c : ℂ) + y * I - x ≠ 0 := sub_ne_zero.mpr hne
    have hcp : ((c + p : ℝ) : ℂ) = x := by rw [← hxcp]
    have hcm : ((c - p : ℝ) : ℂ) = a := by rw [ha_def]
    rw [hcp, hcm]
    simp only [hH]
    rw [dslope_of_ne _ hne, slope_def_field]
    field_simp
    ring
  simp_rw [hdecomp]
  rw [integral_add hHint (hKint.const_mul _), hHzero, integral_const_mul, hKval]
  ring

/-- Derivative of `x ↦ ((w - x)^s)⁻¹` (real variable `x`, `w - x ≠ 0`). -/
theorem hasDerivAt_inv_sub_pow (w : ℂ) (s : ℕ) {x : ℝ} (hx : w - x ≠ 0) :
    HasDerivAt (fun x : ℝ => ((w - x) ^ s)⁻¹) ((s : ℂ) * ((w - x) ^ (s + 1))⁻¹) x := by
  have h1 : HasDerivAt (fun x : ℝ => w - (x : ℂ)) (-1) x := by
    have := ((hasDerivAt_id x).ofReal_comp).const_sub w
    simpa using this
  have h3 := (hasDerivAt_zpow (-(s : ℤ)) (w - x) (Or.inl hx)).comp x h1
  have hfun : ((fun z : ℂ => z ^ (-(s : ℤ))) ∘ fun x : ℝ => w - (x : ℂ)) =
      fun x : ℝ => ((w - x) ^ s)⁻¹ := by
    funext y
    simp [zpow_neg, zpow_natCast]
  rw [hfun] at h3
  convert h3 using 1
  have he : (-(s : ℤ) - 1) = -((s + 1 : ℕ) : ℤ) := by push_cast; ring
  rw [he, zpow_neg, zpow_natCast]
  push_cast
  ring

/-- **Differentiation under the integral sign** for the kernels `(c + iy - x)^{-s}`. -/
theorem hasDerivAt_vline_integral {g : ℝ → ℂ} (hg : Integrable g) (hgc : Continuous g)
    {c x₀ : ℝ} (hx₀ : x₀ ≠ c) (s : ℕ) :
    HasDerivAt (fun x : ℝ => ∫ y : ℝ, g y * (((c : ℂ) + y * I - x) ^ s)⁻¹)
      ((s : ℂ) * ∫ y : ℝ, g y * (((c : ℂ) + y * I - x₀) ^ (s + 1))⁻¹) x₀ := by
  set δ : ℝ := |x₀ - c| / 2 with hδ
  have hδpos : 0 < δ := by
    rw [hδ]; have : 0 < |x₀ - c| := abs_pos.mpr (sub_ne_zero.mpr hx₀); linarith
  have hne : ∀ x : ℝ, x ≠ c → ∀ y : ℝ, (c : ℂ) + y * I - x ≠ 0 := by
    intro x hx y h
    have := congrArg Complex.re h
    simp at this
    exact hx (by linarith)
  have hnorm_ge : ∀ x y : ℝ, |c - x| ≤ ‖(c : ℂ) + y * I - x‖ := by
    intro x y
    have := Complex.abs_re_le_norm ((c : ℂ) + y * I - x)
    simpa using this
  have hball : ∀ x ∈ Metric.ball x₀ δ, δ ≤ |c - x| := by
    intro x hx
    rw [Metric.mem_ball, Real.dist_eq] at hx
    have h1 : |x₀ - c| ≤ |x₀ - x| + |x - c| := by
      have := abs_sub_le x₀ x c; linarith
    rw [abs_sub_comm x₀ x] at h1
    rw [abs_sub_comm c x]
    rw [hδ] at hx ⊢
    linarith
  have hcont : ∀ x : ℝ, x ≠ c → ∀ k : ℕ,
      Continuous fun y : ℝ => g y * (((c : ℂ) + y * I - x) ^ k)⁻¹ := by
    intro x hx k
    exact hgc.mul (Continuous.inv₀ (by fun_prop) fun y => pow_ne_zero _ (hne x hx y))
  set F : ℝ → ℝ → ℂ := fun x y => g y * (((c : ℂ) + y * I - x) ^ s)⁻¹ with hF
  set F' : ℝ → ℝ → ℂ := fun x y => g y * ((s : ℂ) * (((c : ℂ) + y * I - x) ^ (s + 1))⁻¹)
    with hF'
  have hmeas : ∀ᶠ x in 𝓝 x₀, AEStronglyMeasurable (F x) volume := by
    filter_upwards [eventually_ne_nhds hx₀] with x hx
    exact (hcont x hx s).aestronglyMeasurable
  have hFint : Integrable (F x₀) volume := by
    refine (hg.norm.mul_const ((|c - x₀|)⁻¹ ^ s)).mono' (hcont x₀ hx₀ s).aestronglyMeasurable
      (Eventually.of_forall fun y => ?_)
    simp only [hF]
    rw [norm_mul, norm_inv, norm_pow]
    gcongr
    rw [← inv_pow]
    have hpos : 0 < |c - x₀| := abs_pos.mpr (sub_ne_zero.mpr (Ne.symm hx₀))
    gcongr
    exact hnorm_ge x₀ y
  have hF'meas : AEStronglyMeasurable (F' x₀) volume := by
    have := (hcont x₀ hx₀ (s + 1)).const_mul (s : ℂ)
    refine (this.aestronglyMeasurable).congr (Eventually.of_forall fun y => ?_)
    simp only [hF']
    ring
  set bound : ℝ → ℝ := fun y => ‖g y‖ * ((s : ℝ) * (δ⁻¹) ^ (s + 1)) with hbound
  have hbound_int : Integrable bound volume := hg.norm.mul_const _
  have hbnd : ∀ᵐ y ∂volume, ∀ x ∈ Metric.ball x₀ δ, ‖F' x y‖ ≤ bound y := by
    refine Eventually.of_forall fun y x hx => ?_
    simp only [hF', hbound]
    rw [norm_mul, norm_mul, norm_inv, norm_pow, Complex.norm_natCast]
    gcongr
    rw [← inv_pow]
    gcongr
    exact le_trans (hball x hx) (hnorm_ge x y)
  have hdiff : ∀ᵐ y ∂volume, ∀ x ∈ Metric.ball x₀ δ,
      HasDerivAt (fun x => F x y) (F' x y) x := by
    refine Eventually.of_forall fun y x hx => ?_
    have hxc : x ≠ c := by
      intro h; have := hball x hx; rw [h, sub_self, abs_zero] at this; linarith
    simp only [hF, hF']
    exact (hasDerivAt_inv_sub_pow _ s (hne x hxc y)).const_mul (g y)
  have key := hasDerivAt_integral_of_dominated_loc_of_deriv_le (Metric.ball_mem_nhds x₀ hδpos)
    hmeas hFint hF'meas hbnd hbound_int hdiff
  convert key.2 using 1
  simp only [hF']
  rw [← integral_const_mul]
  congr 1
  ext y
  ring

/-- Vanishing when the pole is to the left of the line. -/
theorem vline_left {F : ℂ → ℂ} {c c' : ℝ} (hcc : c' < c)
    (hF : DifferentiableOn ℂ F {t | c' < t.re}) {C r : ℝ} (hr : 1 ≤ r) (hC0 : 0 ≤ C)
    (hC : ∀ t : ℂ, c ≤ t.re → r ≤ ‖t‖ → ‖F t‖ ≤ C / ‖t‖) {x : ℝ} (hx : x < c) {s : ℕ}
    (hs : 1 ≤ s) :
    ∫ y : ℝ, F (c + y * I) * (((c : ℂ) + y * I - x) ^ s)⁻¹ = 0 := by
  set c'' : ℝ := max c' x
  have hc''c : c'' < c := max_lt hcc hx
  have hdiff : DifferentiableOn ℂ (fun t => F t * ((t - x) ^ s)⁻¹) {t | c'' < t.re} := by
    refine DifferentiableOn.mul (hF.mono fun t ht => ?_) ?_
    · show c' < t.re
      exact lt_of_le_of_lt (le_max_left _ _) ht
    refine DifferentiableOn.inv (DifferentiableOn.pow (differentiableOn_id.sub
      (differentiableOn_const _)) s) ?_
    intro t ht h
    have h1 : t - x = 0 := (pow_eq_zero_iff (by omega)).mp h
    have := congrArg Complex.re h1
    simp at this
    have h2 : c'' < t.re := ht
    have : x ≤ c'' := le_max_right _ _
    linarith
  set r₁ : ℝ := max r (2 * |x| + 1)
  have hr₁ : 1 ≤ r₁ := le_trans hr (le_max_left _ _)
  have hdec : ∀ t : ℂ, c ≤ t.re → r₁ ≤ ‖t‖ →
      ‖F t * ((t - x) ^ s)⁻¹‖ ≤ (C * 2 ^ s) / ‖t‖ ^ 2 := by
    intro t htre htn
    have htr : r ≤ ‖t‖ := le_trans (le_max_left _ _) htn
    have ht2 : 2 * |x| + 1 ≤ ‖t‖ := le_trans (le_max_right _ _) htn
    have ht1 : 1 ≤ ‖t‖ := by linarith [abs_nonneg x]
    have htpos : 0 < ‖t‖ := by linarith
    have hx2 : ‖t‖ / 2 ≤ ‖t - x‖ := by
      have := norm_sub_norm_le t (x : ℂ)
      rw [Complex.norm_real, Real.norm_eq_abs] at this
      linarith
    have hx2pos : 0 < ‖t‖ / 2 := by positivity
    rw [norm_mul, norm_inv, norm_pow]
    calc ‖F t‖ * (‖t - ↑x‖ ^ s)⁻¹ ≤ C / ‖t‖ * ((‖t‖ / 2) ^ s)⁻¹ := by
          gcongr
          exact hC t htre htr
      _ = C * 2 ^ s / ‖t‖ / ‖t‖ ^ s := by
          rw [div_pow]; field_simp
      _ ≤ C * 2 ^ s / ‖t‖ / ‖t‖ := by
          gcongr
          calc ‖t‖ = ‖t‖ ^ 1 := (pow_one _).symm
            _ ≤ ‖t‖ ^ s := pow_le_pow_right₀ ht1 hs
      _ = C * 2 ^ s / ‖t‖ ^ 2 := by ring
  exact (vline_integral_eq_zero hc''c hdiff hr₁ (by positivity) hdec).2

/-- **Cauchy's formula for higher-order poles**, by differentiating the simple-pole formula.
`D j` is the `j`-th Taylor coefficient function (`D 0 = F`, `D j' = (j+1) D (j+1)` on `x > c`). -/
theorem vline_higher {F : ℂ → ℂ} {c c' : ℝ} (hcc : c' < c)
    (hF : DifferentiableOn ℂ F {t | c' < t.re}) {C r : ℝ} (hr : 1 ≤ r) (hC0 : 0 ≤ C)
    (hC : ∀ t : ℂ, c ≤ t.re → r ≤ ‖t‖ → ‖F t‖ ≤ C / ‖t‖)
    (hg : Integrable (fun y : ℝ => F (c + y * I)))
    (D : ℕ → ℝ → ℂ) (hD0 : ∀ x : ℝ, c < x → D 0 x = F x)
    (hD : ∀ (j : ℕ) (x : ℝ), c < x → HasDerivAt (D j) (((j : ℂ) + 1) * D (j + 1) x) x) :
    ∀ (j : ℕ) (x : ℝ), c < x →
      ∫ y : ℝ, F (c + y * I) * (((c : ℂ) + y * I - x) ^ (j + 1))⁻¹ = -2 * π * D j x := by
  have hgc : Continuous fun y : ℝ => F (c + y * I) := by
    refine hF.continuousOn.comp_continuous (continuous_vline c) fun y => ?_
    show c' < ((c : ℂ) + (y : ℂ) * I).re
    rw [vline_re]; exact hcc
  intro j
  induction j with
  | zero =>
    intro x hx
    simp only [zero_add, pow_one]
    rw [vline_cauchy hcc hF hr hC0 hC hx, hD0 x hx]
  | succ j ih =>
    intro x hx
    have hxne : x ≠ c := ne_of_gt hx
    have h1 := hasDerivAt_vline_integral hg hgc hxne (j + 1)
    have heq : (fun x : ℝ => ∫ y : ℝ, F (c + y * I) * (((c : ℂ) + y * I - x) ^ (j + 1))⁻¹)
        =ᶠ[𝓝 x] fun x => -2 * π * D j x := by
      filter_upwards [Ioi_mem_nhds hx] with x' hx'
      exact ih x' hx'
    have h2 : HasDerivAt (fun x => -2 * π * D j x)
        (((j + 1 : ℕ) : ℂ) *
          ∫ y : ℝ, F (c + y * I) * (((c : ℂ) + y * I - x) ^ (j + 1 + 1))⁻¹) x :=
      h1.congr_of_eventuallyEq heq.symm
    have h3 : HasDerivAt (fun x => -2 * π * D j x)
        (-2 * π * (((j : ℂ) + 1) * D (j + 1) x)) x := (hD j x hx).const_mul _
    have h4 := h2.unique h3
    have hj : ((j : ℂ) + 1) ≠ 0 := by exact_mod_cast Nat.succ_ne_zero j
    push_cast at h4
    have : ((j : ℂ) + 1) * ∫ y : ℝ, F (c + y * I) * (((c : ℂ) + y * I - x) ^ (j + 1 + 1))⁻¹ =
        ((j : ℂ) + 1) * (-2 * π * D (j + 1) x) := by
      rw [h4]; ring
    exact mul_left_cancel₀ hj this

/-- Reduction to the upper half of the line for conjugation-symmetric integrands. -/
theorem integral_line_conj {f : ℂ → ℂ} {c : ℝ} (hf : ∀ t, f ((starRingEnd ℂ) t) = (starRingEnd ℂ) (f t))
    (hint : Integrable (fun y : ℝ => f (c + y * I))) :
    ∫ y : ℝ, f (c + y * I) =
      (∫ y in Ioi (0 : ℝ), f (c + y * I)) + (starRingEnd ℂ) (∫ y in Ioi (0 : ℝ), f (c + y * I)) := by
  rw [← intervalIntegral.integral_Iic_add_Ioi hint.integrableOn hint.integrableOn, add_comm]
  congr 1
  have h1 : ∫ y in Iic (0 : ℝ), f (c + y * I) = ∫ y in Ioi (0 : ℝ), f (c + (-y : ℝ) * I) := by
    rw [integral_comp_neg_Ioi (c := 0) (f := fun y : ℝ => f (c + y * I)), neg_zero]
  rw [h1, ← integral_conj]
  congr 1
  ext y
  rw [← hf]
  congr 1
  apply Complex.ext <;> simp

theorem norm_integral_line_conj_le {f : ℂ → ℂ} {c : ℝ}
    (hf : ∀ t, f ((starRingEnd ℂ) t) = (starRingEnd ℂ) (f t))
    (hint : Integrable (fun y : ℝ => f (c + y * I))) :
    ‖∫ y : ℝ, f (c + y * I)‖ ≤ 2 * ‖∫ y in Ioi (0 : ℝ), f (c + y * I)‖ := by
  rw [integral_line_conj hf hint]
  refine le_trans (norm_add_le _ _) ?_
  rw [Complex.norm_conj]
  linarith

/-! ## Half-integer kernels -/

/-- The half-integer points `x_ν = ν + 1/2`. -/
def hpt (ν : ℤ) : ℂ := (ν : ℂ) + 1 / 2

/-- The kernel `K_s(t) = ∑_{ν ∈ ℤ} (t - (ν + 1/2))^{-s}`. -/
def kerS (s : ℕ) (t : ℂ) : ℂ := ∑' ν : ℤ, ((t - hpt ν) ^ s)⁻¹

theorem summable_norm_inv_int_add_pow (a : ℂ) {s : ℕ} (hs : 2 ≤ s) :
    Summable fun ν : ℤ => ‖(((ν : ℂ) + a) ^ s)⁻¹‖ := by
  have h1 := (Real.summable_one_div_int_add_rpow a.re (s : ℝ)).mpr (by
    have : (2 : ℝ) ≤ s := by exact_mod_cast hs
    linarith)
  refine Summable.of_norm_bounded_eventually h1 ?_
  rw [Filter.eventually_cofinite]
  refine Set.Subsingleton.finite ?_
  have hsub : {x : ℤ | ¬‖‖(((x : ℂ) + a) ^ s)⁻¹‖‖ ≤ 1 / |(x : ℝ) + a.re| ^ (s : ℝ)} ⊆
      {x : ℤ | (x : ℝ) + a.re = 0} := by
    intro x hx
    simp only [Set.mem_ofPred_eq] at hx ⊢
    by_contra hne
    apply hx
    rw [norm_norm, norm_inv, norm_pow, Real.rpow_natCast, one_div]
    have hpos : 0 < |(x : ℝ) + a.re| := abs_pos.mpr hne
    have hle : |(x : ℝ) + a.re| ≤ ‖(x : ℂ) + a‖ := by
      have := Complex.abs_re_le_norm ((x : ℂ) + a)
      simpa using this
    gcongr
  refine Set.Subsingleton.anti ?_ hsub
  intro x hx y hy
  simp only [Set.mem_ofPred_eq] at hx hy
  have : (x : ℝ) = y := by linarith
  exact_mod_cast this

theorem summable_norm_kerS_term (t : ℂ) {s : ℕ} (hs : 2 ≤ s) :
    Summable fun ν : ℤ => ‖((t - hpt ν) ^ s)⁻¹‖ := by
  have := summable_norm_inv_int_add_pow (1 / 2 - t) hs
  refine this.congr fun ν => ?_
  rw [norm_inv, norm_inv, norm_pow, norm_pow]
  congr 1
  rw [← norm_neg]
  congr 1
  simp only [hpt]
  ring

theorem summable_kerS_term (t : ℂ) {s : ℕ} (hs : 2 ≤ s) :
    Summable fun ν : ℤ => ((t - hpt ν) ^ s)⁻¹ :=
  (summable_norm_kerS_term t hs).of_norm

/-- `Z_s^{abs} = ∑_ν |ν + 1/2|^{-s}`. -/
def zabs (s : ℕ) : ℝ := ∑' ν : ℤ, ‖((hpt ν) ^ s)⁻¹‖

theorem hpt_eq_ofReal (k : ℤ) : hpt k = (((k : ℝ) + 1 / 2 : ℝ) : ℂ) := by
  simp only [hpt]; push_cast; ring

theorem norm_hpt (k : ℤ) : ‖hpt k‖ = |(k : ℝ) + 1 / 2| := by
  rw [hpt_eq_ofReal, Complex.norm_real, Real.norm_eq_abs]

theorem half_le_norm_hpt (k : ℤ) : (1 / 2 : ℝ) ≤ ‖hpt k‖ := by
  rw [norm_hpt]
  rcases le_or_gt 0 k with hk | hk
  · have : (0 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk
    rw [abs_of_nonneg (by linarith)]
    linarith
  · have : (k : ℝ) ≤ -1 := by
      have : k ≤ -1 := by omega
      exact_mod_cast this
    rw [abs_of_neg (by linarith)]
    linarith

theorem norm_sub_hpt_ge_of_int (c : ℤ) (y : ℝ) (ν : ℤ) :
    ‖hpt (c - 1 - ν)‖ ≤ ‖(c : ℂ) + (y : ℂ) * I - hpt ν‖ := by
  have h1 := Complex.abs_re_le_norm ((c : ℂ) + (y : ℂ) * I - hpt ν)
  have hre : ((c : ℂ) + (y : ℂ) * I - hpt ν).re = (c : ℝ) - ν - 1 / 2 := by
    rw [hpt_eq_ofReal]
    simp only [Complex.sub_re, Complex.add_re, Complex.ofReal_re, Complex.mul_re,
      Complex.I_re, Complex.I_im, Complex.ofReal_im, Complex.intCast_re]
    ring
  rw [hre] at h1
  rw [norm_hpt]
  have : ((c - 1 - ν : ℤ) : ℝ) + 1 / 2 = (c : ℝ) - ν - 1 / 2 := by push_cast; ring
  rw [this]
  exact h1

/-- On a vertical line through an integer, `‖K_s‖ ≤ ∑_ν |ν + 1/2|^{-s}`. -/
theorem norm_kerS_vline_le {s : ℕ} (hs : 2 ≤ s) (c : ℤ) (y : ℝ) :
    ‖kerS s ((c : ℂ) + (y : ℂ) * I)‖ ≤ zabs s := by
  unfold kerS zabs
  refine le_trans (norm_tsum_le_tsum_norm (summable_norm_kerS_term _ hs)) ?_
  have hsum0 : Summable fun ν : ℤ => ‖((hpt ν) ^ s)⁻¹‖ := by
    have := summable_norm_kerS_term 0 hs
    refine this.congr fun ν => ?_
    rw [norm_inv, norm_inv, norm_pow, norm_pow, zero_sub, norm_neg]
  have hsum1 : Summable fun ν : ℤ => ‖((hpt (c - 1 - ν)) ^ s)⁻¹‖ := by
    have := (Equiv.summable_iff (Equiv.subLeft (c - 1))
      (f := fun ν : ℤ => ‖((hpt ν) ^ s)⁻¹‖)).mpr hsum0
    simpa only [Function.comp_def, Equiv.subLeft_apply] using this
  calc ∑' ν : ℤ, ‖(((c : ℂ) + (y : ℂ) * I - hpt ν) ^ s)⁻¹‖
      ≤ ∑' ν : ℤ, ‖((hpt (c - 1 - ν)) ^ s)⁻¹‖ := by
        refine Summable.tsum_le_tsum (fun ν => ?_) (summable_norm_kerS_term _ hs) hsum1
        rw [norm_inv, norm_inv, norm_pow, norm_pow]
        have hpos : 0 < ‖hpt (c - 1 - ν)‖ := lt_of_lt_of_le (by norm_num) (half_le_norm_hpt _)
        gcongr
        exact norm_sub_hpt_ge_of_int c y ν
    _ = ∑' ν : ℤ, ‖((hpt ν) ^ s)⁻¹‖ := by
        have e := (Equiv.subLeft (c - 1)).tsum_eq (fun ν => ‖((hpt ν) ^ s)⁻¹‖)
        simp only [Equiv.subLeft_apply] at e
        exact e

/-- Conjugation symmetry of the kernel. -/
theorem kerS_conj (s : ℕ) (t : ℂ) : kerS s ((starRingEnd ℂ) t) = (starRingEnd ℂ) (kerS s t) := by
  unfold kerS
  rw [Complex.conj_tsum]
  congr 1
  ext ν
  rw [map_inv₀, map_pow, map_sub, hpt_eq_ofReal, Complex.conj_ofReal]

/-- Differentiability of the kernel on a ball staying away from the half-integers. -/
theorem kerS_differentiableOn_ball {s : ℕ} (hs : 2 ≤ s) (t₀ : ℂ) {r : ℝ} (hr : 0 < r)
    (h : ∀ ν : ℤ, 2 * r ≤ ‖t₀ - hpt ν‖) : DifferentiableOn ℂ (kerS s) (Metric.ball t₀ r) := by
  unfold kerS
  refine differentiableOn_tsum_of_summable_norm
    ((summable_norm_kerS_term t₀ hs).mul_left (2 ^ s)) (fun ν => ?_) Metric.isOpen_ball
    (fun ν w hw => ?_)
  · refine DifferentiableOn.inv (DifferentiableOn.pow (differentiableOn_id.sub
      (differentiableOn_const _)) s) fun w hw h0 => ?_
    have h1 : w - hpt ν = 0 := (pow_eq_zero_iff (by omega)).mp h0
    rw [Metric.mem_ball, dist_eq_norm] at hw
    have h2 := h ν
    have : ‖t₀ - hpt ν‖ ≤ ‖w - t₀‖ := by
      have : t₀ - hpt ν = -(w - t₀) + (w - hpt ν) := by ring
      rw [this, h1, add_zero, norm_neg]
    linarith
  · rw [Metric.mem_ball, dist_eq_norm] at hw
    have h2 := h ν
    have hge : ‖t₀ - hpt ν‖ / 2 ≤ ‖w - hpt ν‖ := by
      have : ‖t₀ - hpt ν‖ ≤ ‖w - hpt ν‖ + ‖w - t₀‖ := by
        have : t₀ - hpt ν = (w - hpt ν) - (w - t₀) := by ring
        rw [this]; exact norm_sub_le _ _
      linarith
    have hpos : 0 < ‖t₀ - hpt ν‖ / 2 := by linarith
    rw [norm_inv, norm_inv, norm_pow, norm_pow]
    calc (‖w - hpt ν‖ ^ s)⁻¹ ≤ ((‖t₀ - hpt ν‖ / 2) ^ s)⁻¹ := by gcongr
      _ = 2 ^ s * (‖t₀ - hpt ν‖ ^ s)⁻¹ := by rw [div_pow]; field_simp

theorem kerS_differentiableOn_upper {s : ℕ} (hs : 2 ≤ s) :
    DifferentiableOn ℂ (kerS s) {t | 0 < t.im} := by
  intro t₀ ht₀
  have ht₀' : 0 < t₀.im := ht₀
  have hball := kerS_differentiableOn_ball hs t₀ (r := t₀.im / 2) (by linarith) fun ν => by
    have := Complex.abs_im_le_norm (t₀ - hpt ν)
    have him : (t₀ - hpt ν).im = t₀.im := by simp [hpt]
    rw [him, abs_of_pos ht₀'] at this
    linarith
  exact (hball.differentiableAt (Metric.ball_mem_nhds t₀ (by linarith))).differentiableWithinAt

theorem kerS_differentiableAt_vline {s : ℕ} (hs : 2 ≤ s) (c : ℤ) (y : ℝ) :
    DifferentiableAt ℂ (kerS s) ((c : ℂ) + (y : ℂ) * I) := by
  have hball := kerS_differentiableOn_ball hs ((c : ℂ) + (y : ℂ) * I) (r := 1 / 4) (by norm_num)
    fun ν => by
      have h1 := norm_sub_hpt_ge_of_int c y ν
      have h2 := half_le_norm_hpt (c - 1 - ν)
      linarith
  exact hball.differentiableAt (Metric.ball_mem_nhds _ (by norm_num))

/-- **Exponential decay** of the kernel in the upper half-plane (q-expansion). -/
theorem kerS_decay {s : ℕ} (hs : 2 ≤ s) :
    ∃ κ : ℝ, 0 ≤ κ ∧ ∀ t : ℂ, 1 ≤ t.im → ‖kerS s t‖ ≤ κ * Real.exp (-2 * π * t.im) := by
  obtain ⟨k, rfl⟩ : ∃ k, s = k + 1 := ⟨s - 1, by omega⟩
  have hk : 1 ≤ k := by omega
  set ρ₀ : ℝ := Real.exp (-2 * π) with hρ₀
  have hρ₀pos : 0 < ρ₀ := Real.exp_pos _
  have hρ₀lt : ρ₀ < 1 := by
    rw [hρ₀]; exact Real.exp_lt_one_iff.mpr (by linarith [Real.pi_pos])
  have hsum0 : Summable fun d : ℕ => (d : ℝ) ^ k * ρ₀ ^ d :=
    summable_pow_mul_geometric_of_norm_lt_one k (by rw [Real.norm_eq_abs, abs_of_pos hρ₀pos]; exact hρ₀lt)
  set S₀ : ℝ := ∑' d : ℕ, (d : ℝ) ^ k * ρ₀ ^ d
  have hS₀ : 0 ≤ S₀ := tsum_nonneg fun d => by positivity
  refine ⟨(2 * π) ^ (k + 1) / (k.factorial : ℝ) * (S₀ / ρ₀), by positivity, fun t ht => ?_⟩
  have htpos : 0 < (t - 1 / 2).im := by simp; linarith
  set z : UpperHalfPlane := ⟨t - 1 / 2, htpos⟩
  have hz : (z : ℂ) = t - 1 / 2 := rfl
  have hq := EisensteinSeries.qExpansion_identity hk z
  have hker : kerS (k + 1) t = ∑' n : ℤ, 1 / ((z : ℂ) + n) ^ (k + 1) := by
    unfold kerS
    rw [← (Equiv.neg ℤ).tsum_eq]
    congr 1
    ext n
    simp only [Equiv.neg_apply, hpt, hz, one_div]
    congr 2
    push_cast
    ring
  rw [hker, hq]
  set ρ : ℝ := Real.exp (-2 * π * t.im) with hρ
  have hqn : ‖Complex.exp (2 * π * I * (z : ℂ))‖ = ρ := by
    rw [Complex.norm_exp, hz, hρ]
    congr 1
    simp only [Complex.mul_re, Complex.mul_im, Complex.sub_re, Complex.sub_im, Complex.I_re,
      Complex.I_im, Complex.ofReal_re, Complex.ofReal_im, Complex.re_ofNat, Complex.im_ofNat]
    norm_num
  have hρle : ρ ≤ ρ₀ := by
    rw [hρ, hρ₀]; apply Real.exp_le_exp.mpr
    nlinarith [Real.pi_pos]
  have hρpos : 0 < ρ := Real.exp_pos _
  have hsum1 : Summable fun d : ℕ => ‖(d : ℂ) ^ k * Complex.exp (2 * π * I * (z : ℂ)) ^ d‖ := by
    have : Summable fun d : ℕ => (d : ℝ) ^ k * ρ ^ d :=
      summable_pow_mul_geometric_of_norm_lt_one k
        (by rw [Real.norm_eq_abs, abs_of_pos hρpos]; linarith)
    refine this.congr fun d => ?_
    rw [norm_mul, norm_pow, norm_pow, Complex.norm_natCast, hqn]
  rw [norm_mul]
  have hcoef : ‖(-2 * (π : ℂ) * I) ^ (k + 1) / (k.factorial : ℂ)‖ =
      (2 * π) ^ (k + 1) / (k.factorial : ℝ) := by
    rw [norm_div, norm_pow, Complex.norm_natCast]
    congr 2
    rw [norm_mul, norm_mul, Complex.norm_I, mul_one, norm_neg, Complex.norm_ofNat,
      Complex.norm_real, Real.norm_eq_abs, abs_of_pos Real.pi_pos]
  rw [hcoef, show (2 * π) ^ (k + 1) / (k.factorial : ℝ) * (S₀ / ρ₀) * ρ =
    (2 * π) ^ (k + 1) / (k.factorial : ℝ) * (S₀ / ρ₀ * ρ) by ring]
  have hA : 0 ≤ (2 * π) ^ (k + 1) / (k.factorial : ℝ) := by positivity
  refine mul_le_mul_of_nonneg_left ?_ hA
  refine le_trans (norm_tsum_le_tsum_norm hsum1) ?_
  have hterm : ∀ d : ℕ, ‖(d : ℂ) ^ k * Complex.exp (2 * π * I * (z : ℂ)) ^ d‖ ≤
      (S₀ / ρ₀ * ρ) * 0 + (ρ / ρ₀) * ((d : ℝ) ^ k * ρ₀ ^ d) := by
    intro d
    rw [norm_mul, norm_pow, norm_pow, Complex.norm_natCast, hqn, mul_zero, zero_add]
    rcases d with _ | d
    · have hk0 : k ≠ 0 := by omega
      simp [hk0]
    · rw [pow_succ, pow_succ]
      have : ρ ^ d ≤ ρ₀ ^ d := pow_le_pow_left₀ hρpos.le hρle d
      have h2 : ((d + 1 : ℕ) : ℝ) ^ k * (ρ ^ d * ρ) ≤ ((d + 1 : ℕ) : ℝ) ^ k * (ρ₀ ^ d * ρ) := by
        gcongr
      calc ((d + 1 : ℕ) : ℝ) ^ k * (ρ ^ d * ρ) ≤ ((d + 1 : ℕ) : ℝ) ^ k * (ρ₀ ^ d * ρ) := h2
        _ = ρ / ρ₀ * (((d + 1 : ℕ) : ℝ) ^ k * (ρ₀ ^ d * ρ₀)) := by field_simp
  calc ∑' d : ℕ, ‖(d : ℂ) ^ k * Complex.exp (2 * π * I * (z : ℂ)) ^ d‖
      ≤ ∑' d : ℕ, ((S₀ / ρ₀ * ρ) * 0 + (ρ / ρ₀) * ((d : ℝ) ^ k * ρ₀ ^ d)) :=
        Summable.tsum_le_tsum hterm hsum1 ((hsum0.mul_left (ρ / ρ₀)).congr fun d => by ring)
    _ = (ρ / ρ₀) * S₀ := by
        simp only [mul_zero, zero_add]
        rw [tsum_mul_left]
    _ = S₀ / ρ₀ * ρ := by ring

/-- `a(i,j) = (-1)^j C(i+j-1, j)`: `(x+ε)^{-i} = ∑_j a(i,j) x^{-(i+j)} ε^j`. -/
def acoef (i j : ℕ) : ℚ := (-1) ^ j * (((i + j - 1).choose j : ℕ) : ℚ)

theorem acoef_zero (i : ℕ) : acoef i 0 = 1 := by simp [acoef]

theorem acoef_succ (i j : ℕ) (hi : 1 ≤ i) :
    acoef i j * (-((i + j : ℕ) : ℚ)) = ((j : ℚ) + 1) * acoef i (j + 1) := by
  unfold acoef
  obtain ⟨N, hN1, hN2⟩ : ∃ N, i + j - 1 = N ∧ i + j = N + 1 := ⟨i + j - 1, rfl, by omega⟩
  have h1 : i + (j + 1) - 1 = N + 1 := by omega
  rw [hN1, h1, hN2]
  have h2 : ((N + 1 : ℕ) : ℚ) * ((N.choose j : ℕ) : ℚ) =
      (((N + 1).choose (j + 1) : ℕ) : ℚ) * ((j : ℚ) + 1) := by
    exact_mod_cast Nat.add_one_mul_choose_eq N j
  rw [pow_succ]
  linear_combination (-(-1 : ℚ) ^ j) * h2

theorem hasDerivAt_inv_add_pow (k : ℂ) (N : ℕ) {z : ℂ} (hz : z + k ≠ 0) :
    HasDerivAt (fun z => ((z + k) ^ N)⁻¹) (-(N : ℂ) * ((z + k) ^ (N + 1))⁻¹) z := by
  have h1 : HasDerivAt (fun z : ℂ => z + k) 1 z := (hasDerivAt_id z).add_const k
  have h3 := (hasDerivAt_zpow (-(N : ℤ)) (z + k) (Or.inl hz)).comp z h1
  have hfun : ((fun w : ℂ => w ^ (-(N : ℤ))) ∘ fun z : ℂ => z + k) =
      fun z : ℂ => ((z + k) ^ N)⁻¹ := by
    funext y
    simp [zpow_neg, zpow_natCast]
  rw [hfun] at h3
  convert h3 using 1
  have he : (-(N : ℤ) - 1) = -((N + 1 : ℕ) : ℤ) := by push_cast; ring
  rw [he, zpow_neg, zpow_natCast]
  push_cast
  ring

theorem inv_C_add_X_pow_succ (c : ℚ) (hc : c ≠ 0) (d : ℕ) :
    ((C c + X : PowerSeries ℚ) ^ (d + 1))⁻¹ =
      C (c⁻¹ ^ (d + 1)) * rescale (-c⁻¹) (mk fun n => ((d + n).choose d : ℚ)) := by
  rw [PowerSeries.inv_eq_iff_mul_eq_one]
  · have h1 : (C c + X : PowerSeries ℚ) = C c * rescale (-c⁻¹) (1 - X) := by
      rw [map_sub, map_one, rescale_X, mul_sub, mul_one, ← mul_assoc, ← map_mul, mul_neg,
        mul_inv_cancel₀ hc, map_neg, map_one, neg_one_mul, sub_neg_eq_add]
    rw [h1, mul_pow, ← map_pow C, ← map_pow (rescale (-c⁻¹))]
    calc C (c⁻¹ ^ (d + 1)) * rescale (-c⁻¹) (mk fun n => ((d + n).choose d : ℚ)) *
          (C (c ^ (d + 1)) * rescale (-c⁻¹) ((1 - X) ^ (d + 1)))
        = C (c⁻¹ ^ (d + 1) * c ^ (d + 1)) *
            rescale (-c⁻¹) ((mk fun n => ((d + n).choose d : ℚ)) * (1 - X) ^ (d + 1)) := by
          rw [map_mul, map_mul]
          ring
      _ = 1 := by
          rw [mk_add_choose_mul_one_sub_pow_eq_one, ← mul_pow, inv_mul_cancel₀ hc, one_pow,
            map_one, map_one, one_mul]
  · simp [hc]

theorem coeff_inv_C_add_X_pow (c : ℚ) (hc : c ≠ 0) (i j : ℕ) (hi : 1 ≤ i) :
    coeff j ((C c + X : PowerSeries ℚ) ^ i)⁻¹ = acoef i j * (c ^ (i + j))⁻¹ := by
  obtain ⟨d, rfl⟩ : ∃ d, i = d + 1 := ⟨i - 1, by omega⟩
  rw [inv_C_add_X_pow_succ c hc d, coeff_C_mul, coeff_rescale, coeff_mk]
  unfold acoef
  have hch : (d + j).choose d = (d + 1 + j - 1).choose j := by
    rw [show d + 1 + j - 1 = d + j by omega]
    exact Nat.choose_symm_add
  rw [hch, neg_pow, ← inv_pow]
  ring

theorem tsum_nat_shift_zero {f : ℕ → ℂ} (hf : Summable f) (M : ℕ) (hz : ∀ l < M, f l = 0) :
    ∑' l : ℕ, f l = ∑' l : ℕ, f (l + M) := by
  rw [← hf.sum_add_tsum_nat_add M, Finset.sum_eq_zero fun l hl => hz l (Finset.mem_range.1 hl),
    zero_add]

theorem integral_exp_affine_Ioi (A β c : ℝ) (hβ : 0 < β) :
    ∫ y in Ioi c, Real.exp (A - β * y) = Real.exp (A - β * c) / β := by
  have e : ∀ y : ℝ, Real.exp (A - β * y) = Real.exp A * Real.exp (-β * y) := by
    intro y; rw [← Real.exp_add]; ring_nf
  simp_rw [e]
  rw [integral_const_mul, integral_exp_mul_Ioi (by linarith) c, neg_div_neg_eq]
  ring

theorem integrableOn_exp_affine_Ioi (A β c : ℝ) (hβ : 0 < β) :
    IntegrableOn (fun y : ℝ => Real.exp (A - β * y)) (Ioi c) := by
  have e : ∀ y : ℝ, Real.exp (A - β * y) = Real.exp A * Real.exp (-β * y) := by
    intro y; rw [← Real.exp_add]; ring_nf
  simp_rw [e]
  exact (exp_neg_integrableOn_Ioi c hβ).const_mul _

end L20U

end ZetaWindow

end
