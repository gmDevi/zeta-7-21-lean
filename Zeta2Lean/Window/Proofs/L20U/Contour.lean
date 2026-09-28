module

public import Zeta2Lean.Window.Proofs.L20U.VLine

@[expose] public section

set_option linter.style.header false
set_option linter.style.longLine false

/-!
# Theorem U, part 3: the contour representation (Lemma 1 of crude-upper-bound.md)

For the window configuration and `n ≥ 1`:
* `Pw n t = ∑_{j,k} B_{j,k} (t+k)^{-(j-r)}` is the complex partial-fraction function of `R̃ = N_h R`,
  `Dw n i` its `i`-th Taylor coefficient function (`Dw_hasDerivAt`); from `Stmt_PF`,
  `term cfgW n t = Dw n 4 t` (`term_eq_Dw`) and `Dw n 4 (-l) = 0` for `1 ≤ l ≤ 47 n`
  (`Dw_four_neg_eq_zero`: zeros of order 5 of `R̃`);
* **product form** `Pw n t = Rw n t := N_h (h₀+2t) (∏_{i=1}^{h₀-1}(t+i))^5 / ∏_j ∏_{i=h_j}^{h₀-h_j} (t+i)`
  on `Re t > -h₁` (`Pw_eq_Rw`): both sides are holomorphic there and agree at the rationals
  `1/(m+1)` (constant coefficient of `Stmt_PF`), so the identity theorem applies;
* decay `‖Pw n t‖ ≤ MPw n / ‖t‖²` (`norm_Pw_le`, from `Stmt_CoeffVanish.ressum`);
* **representation** (`line_rep`): on the line `Re t = M_n = 1/2 - n`,
  `∫_ℝ Pw(M_n + iy) K₅(M_n + iy) dy = -2π F̃_n`, `K₅(t) = ∑_ν (t-ν)^{-5} = kerS 5 (t + 1/2)`
  (Cauchy on right half-planes, `vline_higher`/`vline_left`, dominated interchange; the poles
  `1-n ≤ ν ≤ -1` of the kernel right of the line contribute `0` by the zeros of `R̃`);
* hence `|F̃_n| ≤ (1/π) ‖∫_0^∞ Pw(M_n+iy) K₅(M_n+iy) dy‖` (`abs_Fn_le`, conjugation symmetry).
-/

open Complex MeasureTheory Filter Topology Set Finset PowerSeries
open scoped Real

noncomputable section

namespace ZetaWindow

namespace L20U

/-! ## The partial-fraction function and its Taylor coefficients -/

/-- The complex partial-fraction function `∑_{j,k} B_{j,k} (t+k)^{-(j-r)}` of `R̃` (window). -/
def Pw (n : ℕ) (t : ℂ) : ℂ :=
  ∑ j ∈ Icc (cfgW.r + 1) cfgW.q, ∑ k ∈ Krange cfgW n,
    (B cfgW n j k : ℂ) * ((t + k) ^ (j - cfgW.r))⁻¹

/-- Its `i`-th Taylor coefficient `∑_{j,k} B_{j,k} a(j-r, i) (t+k)^{-(j-r+i)}`. -/
def Dw (n i : ℕ) (t : ℂ) : ℂ :=
  ∑ j ∈ Icc (cfgW.r + 1) cfgW.q, ∑ k ∈ Krange cfgW n,
    (B cfgW n j k : ℂ) * (acoef (j - cfgW.r) i : ℂ) * ((t + k) ^ (j - cfgW.r + i))⁻¹

theorem Pw_eq_Dw_zero (n : ℕ) (t : ℂ) : Pw n t = Dw n 0 t := by
  simp [Pw, Dw, acoef_zero]

theorem krange_ge {n k : ℕ} (hk : k ∈ Krange cfgW n) : cfgW.h n 1 ≤ k :=
  (Finset.mem_Icc.1 hk).1

theorem krange_le {n k : ℕ} (hk : k ∈ Krange cfgW n) : k ≤ cfgW.h0 n :=
  le_trans (Finset.mem_Icc.1 hk).2 (Nat.sub_le _ _)

theorem add_ne_zero_of_re {n : ℕ} {t : ℂ} (ht : -(cfgW.h n 1 : ℝ) < t.re) {k : ℕ}
    (hk : k ∈ Krange cfgW n) : t + k ≠ 0 := by
  intro h0
  have h1 := congrArg Complex.re h0
  simp only [Complex.add_re, Complex.natCast_re, Complex.zero_re] at h1
  have h2 : ((cfgW.h n 1 : ℕ) : ℝ) ≤ k := by exact_mod_cast krange_ge hk
  linarith

theorem Dw_hasDerivAt (n i : ℕ) {z : ℂ} (hz : ∀ k ∈ Krange cfgW n, z + k ≠ 0) :
    HasDerivAt (Dw n i) (((i : ℂ) + 1) * Dw n (i + 1) z) z := by
  have hD : HasDerivAt (Dw n i) (∑ j ∈ Icc (cfgW.r + 1) cfgW.q, ∑ k ∈ Krange cfgW n,
      (B cfgW n j k : ℂ) * (acoef (j - cfgW.r) i : ℂ) *
        (-((j - cfgW.r + i : ℕ) : ℂ) * ((z + k) ^ (j - cfgW.r + i + 1))⁻¹)) z := by
    unfold Dw
    apply HasDerivAt.fun_sum
    intro j _
    apply HasDerivAt.fun_sum
    intro k hk
    exact (hasDerivAt_inv_add_pow (k : ℂ) (j - cfgW.r + i) (hz k hk)).const_mul _
  convert hD using 1
  unfold Dw
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun j hj => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  have hj1 : 1 ≤ j - cfgW.r := by have := (Finset.mem_Icc.1 hj).1; omega
  have hc := acoef_succ (j - cfgW.r) i hj1
  have hc' : ((acoef (j - cfgW.r) i : ℚ) : ℂ) * (-((j - cfgW.r + i : ℕ) : ℂ)) =
      ((i : ℂ) + 1) * ((acoef (j - cfgW.r) (i + 1) : ℚ) : ℂ) := by exact_mod_cast hc
  rw [show j - cfgW.r + (i + 1) = j - cfgW.r + i + 1 by ring]
  linear_combination (-(B cfgW n j k : ℂ) * ((z + k) ^ (j - cfgW.r + i + 1))⁻¹) * hc'

theorem Dw_hasDerivAt_real (n i : ℕ) {x : ℝ} (hx : -(cfgW.h n 1 : ℝ) < x) :
    HasDerivAt (fun y : ℝ => Dw n i y) (((i : ℂ) + 1) * Dw n (i + 1) x) x := by
  refine (Dw_hasDerivAt n i fun k hk => add_ne_zero_of_re ?_ hk).comp_ofReal
  simpa using hx

theorem Pw_differentiableOn (n : ℕ) :
    DifferentiableOn ℂ (Pw n) {t : ℂ | -(cfgW.h n 1 : ℝ) < t.re} := by
  intro t ht
  have h := (Dw_hasDerivAt n 0 fun k hk => add_ne_zero_of_re ht hk).differentiableAt
  have he : Pw n = Dw n 0 := funext fun t => Pw_eq_Dw_zero n t
  rw [he]
  exact h.differentiableWithinAt

theorem Pw_conj (n : ℕ) (t : ℂ) : Pw n ((starRingEnd ℂ) t) = (starRingEnd ℂ) (Pw n t) := by
  unfold Pw
  simp only [map_sum, map_mul, map_inv₀, map_pow, map_add, map_natCast, map_ratCast]

/-! ## Taylor coefficients of `R̃` from `Stmt_PF` -/

/-- `[ε^i] R̃(y + ε) = Dw n i y` at every rational non-pole `y`. -/
theorem coeff_Rser_eq_Dw (hPF : Stmt_PF) {n : ℕ} (hn : 1 ≤ n) (y : ℚ)
    (hy : ∀ k ∈ Krange cfgW n, y + k ≠ 0) (i : ℕ) :
    ((coeff i (Rser cfgW n y) : ℚ) : ℂ) = Dw n i (y : ℂ) := by
  have h1 : coeff i (∑ j ∈ Icc (cfgW.r + 1) cfgW.q, ∑ k ∈ Krange cfgW n,
      C (B cfgW n j k) * ((C (y + k) + X) ^ (j - cfgW.r))⁻¹ : PowerSeries ℚ) =
      ∑ j ∈ Icc (cfgW.r + 1) cfgW.q, ∑ k ∈ Krange cfgW n,
        B cfgW n j k * (acoef (j - cfgW.r) i * ((y + k) ^ (j - cfgW.r + i))⁻¹) := by
    rw [map_sum]
    refine Finset.sum_congr rfl fun j hj => ?_
    rw [map_sum]
    refine Finset.sum_congr rfl fun k hk => ?_
    rw [coeff_C_mul, coeff_inv_C_add_X_pow _ (hy k hk) (j - cfgW.r) i
      (by have := (Finset.mem_Icc.1 hj).1; omega)]
  rw [hPF cfgW admissible_cfgW n hn y hy, h1]
  unfold Dw
  push_cast
  refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun k _ => ?_
  ring

/-- `term cfgW n t = Dw n 4 t`. -/
theorem term_eq_Dw (hPF : Stmt_PF) {n : ℕ} (hn : 1 ≤ n) (t : ℕ) :
    ((term cfgW n t : ℚ) : ℂ) = Dw n 4 (t : ℂ) := by
  have hy : ∀ k ∈ Krange cfgW n, (t : ℚ) + k ≠ 0 := by
    intro k hk
    have h1 : 1 ≤ k := le_trans (by simp [Config.h]) (krange_ge hk)
    have : (1 : ℚ) ≤ k := by exact_mod_cast h1
    have : (0 : ℚ) ≤ t := Nat.cast_nonneg t
    linarith
  have := coeff_Rser_eq_Dw hPF hn (t : ℚ) hy 4
  rw [show ((t : ℚ) : ℂ) = (t : ℂ) by push_cast; rfl] at this
  exact this

/-- At `y = -l`, `1 ≤ l < h₀`, `R̃(y+ε)` has a zero of order `r` (copy of
`LinearForm.coeff_Rser_zero`). -/
theorem coeff_Rser_zero' (c : Config) (n l : ℕ) (hr : 1 ≤ c.r) (hl1 : 1 ≤ l) (hl : l < c.h0 n)
    (y : ℚ) (hy : y + l = 0) :
    coeff (c.r - 1) (Rser c n y) = 0 := by
  have hdvd : (X : PowerSeries ℚ) ∣ ∏ i ∈ Ico 1 (c.h0 n), (C (y + i) + X) := by
    have h := Finset.dvd_prod_of_mem (fun i : ℕ => C (y + i) + X) (mem_Ico.2 ⟨hl1, hl⟩)
    simpa [hy] using h
  have hdvd2 : (X : PowerSeries ℚ) ^ c.r ∣ Rser c n y := by
    unfold Rser
    exact dvd_mul_of_dvd_left (dvd_mul_of_dvd_right (pow_dvd_pow_of_dvd hdvd c.r) _) _
  exact (PowerSeries.X_pow_dvd_iff.1 hdvd2) (c.r - 1) (by omega)

/-- **Zeros**: `Dw n 4 (-l) = 0` for `1 ≤ l ≤ 47 n` (`= h₁ - 1`). -/
theorem Dw_four_neg_eq_zero (hPF : Stmt_PF) {n : ℕ} (hn : 1 ≤ n) (l : ℕ) (hl1 : 1 ≤ l)
    (hl : l ≤ 47 * n) : Dw n 4 (-(l : ℂ)) = 0 := by
  have hy : ∀ k ∈ Krange cfgW n, (-(l : ℚ)) + k ≠ 0 := by
    intro k hk
    have h1 : 47 * n + 1 ≤ k := by
      have := krange_ge hk
      simpa [Config.h, cfgW, etaW, mul_comm] using this
    have : ((47 * n + 1 : ℕ) : ℚ) ≤ k := by exact_mod_cast h1
    have : (l : ℚ) ≤ 47 * n := by exact_mod_cast hl
    push_cast at *
    linarith
  have h := coeff_Rser_eq_Dw hPF hn (-(l : ℚ)) hy 4
  have hz := coeff_Rser_zero' cfgW n l (by decide) hl1
    (by simp only [Config.h0, cfgW]; omega) (-(l : ℚ)) (by ring)
  rw [show cfgW.r - 1 = 4 from rfl] at hz
  rw [hz] at h
  rw [show ((-(l : ℚ) : ℚ) : ℂ) = -(l : ℂ) by push_cast; rfl] at h
  rw [← h]
  simp

/-! ## The product form (identity theorem) -/

/-- The product form `N_h (h₀+2t) (∏_{i=1}^{h₀-1}(t+i))^r / ∏_j ∏_{i=h_j}^{h₀-h_j} (t+i)`. -/
def Rw (n : ℕ) (t : ℂ) : ℂ :=
  (Nh cfgW n : ℂ) * ((cfgW.h0 n : ℂ) + 2 * t) * (∏ i ∈ Ico 1 (cfgW.h0 n), (t + i)) ^ cfgW.r /
    ∏ j ∈ Icc 1 cfgW.q, ∏ i ∈ Icc (cfgW.h n j) (cfgW.h0 n - cfgW.h n j), (t + i)

theorem h1_le_hj (n j : ℕ) (hj : 1 ≤ j) : cfgW.h n 1 ≤ cfgW.h n j := by
  simp only [Config.h]
  exact Nat.add_le_add_right (Nat.mul_le_mul_right n (etaW_mono hj)) 1

theorem Rw_den_ne_zero {n : ℕ} {t : ℂ} (ht : -(cfgW.h n 1 : ℝ) < t.re) :
    ∏ j ∈ Icc 1 cfgW.q, ∏ i ∈ Icc (cfgW.h n j) (cfgW.h0 n - cfgW.h n j), (t + i) ≠ 0 := by
  rw [Finset.prod_ne_zero_iff]
  intro j hj
  rw [Finset.prod_ne_zero_iff]
  intro i hi
  have h1 : cfgW.h n 1 ≤ i := le_trans (h1_le_hj n j (Finset.mem_Icc.1 hj).1) (Finset.mem_Icc.1 hi).1
  intro h0
  have h2 := congrArg Complex.re h0
  simp only [Complex.add_re, Complex.natCast_re, Complex.zero_re] at h2
  have h3 : ((cfgW.h n 1 : ℕ) : ℝ) ≤ i := by exact_mod_cast h1
  linarith

theorem Rw_differentiableOn (n : ℕ) :
    DifferentiableOn ℂ (Rw n) {t : ℂ | -(cfgW.h n 1 : ℝ) < t.re} := by
  unfold Rw
  refine DifferentiableOn.div ?_ ?_ fun t ht => Rw_den_ne_zero ht
  · exact Differentiable.differentiableOn (by fun_prop)
  · exact Differentiable.differentiableOn (by fun_prop)

theorem constantCoeff_Rser (c : Config) (n : ℕ) (y : ℚ) :
    constantCoeff (Rser c n y) = Nh c n * ((c.h0 n : ℚ) + 2 * y) *
      (∏ i ∈ Ico 1 (c.h0 n), (y + i)) ^ c.r *
      (∏ j ∈ Icc 1 c.q, ∏ i ∈ Icc (c.h n j) (c.h0 n - c.h n j), (y + i))⁻¹ := by
  unfold Rser
  simp [map_mul, map_pow, map_prod, PowerSeries.constantCoeff_inv]

/-- The rational identity `Pw n y = Rw n y` (constant coefficient of `Stmt_PF`). -/
theorem Pw_rat_eq (hPF : Stmt_PF) {n : ℕ} (hn : 1 ≤ n) (y : ℚ) (hy0 : 0 ≤ y) :
    Pw n (y : ℂ) = Rw n (y : ℂ) := by
  have hy : ∀ k ∈ Krange cfgW n, y + k ≠ 0 := by
    intro k hk
    have h1 : 1 ≤ k := le_trans (by simp [Config.h]) (krange_ge hk)
    have : (1 : ℚ) ≤ k := by exact_mod_cast h1
    linarith
  have h := congrArg (fun φ => constantCoeff φ) (hPF cfgW admissible_cfgW n hn y hy)
  simp only [constantCoeff_Rser] at h
  simp only [map_sum, map_mul, PowerSeries.constantCoeff_C, PowerSeries.constantCoeff_inv,
    map_pow, map_add, PowerSeries.constantCoeff_X, add_zero] at h
  have hc := congrArg (fun q : ℚ => (q : ℂ)) h
  push_cast at hc
  unfold Pw Rw
  rw [div_eq_mul_inv]
  exact hc.symm

theorem Pw_eq_Rw (hPF : Stmt_PF) {n : ℕ} (hn : 1 ≤ n) {t : ℂ}
    (ht : -(cfgW.h n 1 : ℝ) < t.re) : Pw n t = Rw n t := by
  set U : Set ℂ := {t : ℂ | -(cfgW.h n 1 : ℝ) < t.re} with hU
  have hUo : IsOpen U := isOpen_lt continuous_const Complex.continuous_re
  have hUc : IsPreconnected U := (convex_halfSpace_re_gt _).isPreconnected
  have hf : AnalyticOnNhd ℂ (Pw n) U := (Pw_differentiableOn n).analyticOnNhd hUo
  have hg : AnalyticOnNhd ℂ (Rw n) U := (Rw_differentiableOn n).analyticOnNhd hUo
  have h0 : (0 : ℂ) ∈ U := by
    change -(cfgW.h n 1 : ℝ) < (0 : ℂ).re
    simp only [Complex.zero_re, Left.neg_neg_iff]
    exact_mod_cast Nat.succ_pos _
  have hlim : Tendsto (fun m : ℕ => (((1 / ((m : ℚ) + 1) : ℚ)) : ℂ)) atTop (𝓝[≠] 0) := by
    rw [tendsto_nhdsWithin_iff]
    constructor
    · have h1 : Tendsto (fun m : ℕ => 1 / ((m : ℂ) + 1)) atTop (𝓝 0) :=
        tendsto_one_div_add_atTop_nhds_zero_nat
      refine h1.congr fun m => ?_
      push_cast
      ring
    · refine Filter.Eventually.of_forall fun m => ?_
      simp only [Set.mem_compl_iff, Set.mem_singleton_iff]
      have : (0 : ℚ) < 1 / ((m : ℚ) + 1) := by positivity
      exact_mod_cast this.ne'
  have hfreq : ∃ᶠ z in 𝓝[≠] (0 : ℂ), Pw n z = Rw n z := by
    refine hlim.frequently (Filter.Eventually.frequently (Filter.Eventually.of_forall fun m => ?_))
    exact Pw_rat_eq hPF hn _ (by positivity)
  exact hf.eqOn_of_preconnected_of_frequently_eq hg hUc h0 hfreq ht

/-! ## Decay of `Pw` -/

/-- `∑_{j,k} |B_{j,k}| (2k + 4)`. -/
def MPw (n : ℕ) : ℝ :=
  ∑ j ∈ Icc (cfgW.r + 1) cfgW.q, ∑ k ∈ Krange cfgW n, ‖(B cfgW n j k : ℂ)‖ * (2 * k + 4)

theorem MPw_nonneg (n : ℕ) : 0 ≤ MPw n :=
  Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => by positivity

/-- With `∑_k B_{r+1,k} = 0`: `‖Pw n t‖ ≤ MPw n / ‖t‖²` for `‖t‖ ≥ 2h₀ + 2`. -/
theorem norm_Pw_le (hV : Stmt_CoeffVanish) {n : ℕ} (hn : 1 ≤ n) {t : ℂ}
    (ht : 2 * (cfgW.h0 n : ℝ) + 2 ≤ ‖t‖) : ‖Pw n t‖ ≤ MPw n / ‖t‖ ^ 2 := by
  have hc1 : ∑ k ∈ Krange cfgW n, (B cfgW n (cfgW.r + 1) k : ℂ) = 0 := by
    have := hV.ressum cfgW admissible_cfgW n hn
    exact_mod_cast this
  have hh0 : (0 : ℝ) ≤ cfgW.h0 n := Nat.cast_nonneg _
  have htpos : 0 < ‖t‖ := by linarith
  have ht0 : t ≠ 0 := norm_pos_iff.mp htpos
  have htk : ∀ k ∈ Krange cfgW n, ‖t‖ / 2 ≤ ‖t + k‖ := by
    intro k hk
    have hk' : (k : ℝ) ≤ cfgW.h0 n := by exact_mod_cast krange_le hk
    have h1 := norm_sub_le (t + k) (k : ℂ)
    rw [add_sub_cancel_right, Complex.norm_natCast] at h1
    linarith
  have hdecomp : Pw n t = ∑ j ∈ Icc (cfgW.r + 1) cfgW.q, ∑ k ∈ Krange cfgW n,
      (B cfgW n j k : ℂ) * (((t + k) ^ (j - cfgW.r))⁻¹ - if j = cfgW.r + 1 then t⁻¹ else 0) := by
    have hzero : ∑ j ∈ Icc (cfgW.r + 1) cfgW.q, ∑ k ∈ Krange cfgW n,
        (B cfgW n j k : ℂ) * (if j = cfgW.r + 1 then t⁻¹ else 0) = 0 := by
      have : ∀ j ∈ Finset.Icc (cfgW.r + 1) cfgW.q, ∑ k ∈ Krange cfgW n,
          (B cfgW n j k : ℂ) * (if j = cfgW.r + 1 then t⁻¹ else 0) =
            if j = cfgW.r + 1 then (∑ k ∈ Krange cfgW n, (B cfgW n (cfgW.r + 1) k : ℂ)) * t⁻¹
            else 0 := by
        intro j _
        split_ifs with hj
        · subst hj; rw [Finset.sum_mul]
        · simp
      rw [Finset.sum_congr rfl this, Finset.sum_ite_eq' (Finset.Icc (cfgW.r + 1) cfgW.q) (cfgW.r + 1),
        hc1]
      simp
    calc Pw n t = Pw n t - 0 := (sub_zero _).symm
      _ = Pw n t - ∑ j ∈ Icc (cfgW.r + 1) cfgW.q, ∑ k ∈ Krange cfgW n,
            (B cfgW n j k : ℂ) * (if j = cfgW.r + 1 then t⁻¹ else 0) := by rw [hzero]
      _ = _ := by
          unfold Pw
          rw [← Finset.sum_sub_distrib]
          refine Finset.sum_congr rfl fun j _ => ?_
          rw [← Finset.sum_sub_distrib]
          refine Finset.sum_congr rfl fun k _ => ?_
          ring
  rw [hdecomp]
  unfold MPw
  rw [Finset.sum_div]
  refine le_trans (norm_sum_le _ _) (Finset.sum_le_sum fun j hj => ?_)
  rw [Finset.sum_div]
  refine le_trans (norm_sum_le _ _) (Finset.sum_le_sum fun k hk => ?_)
  have hj1 : cfgW.r + 1 ≤ j := (Finset.mem_Icc.1 hj).1
  have htk1 := htk k hk
  have htk0 : t + k ≠ 0 := by
    intro h0; rw [h0, norm_zero] at htk1; linarith
  have hk0 : (0 : ℝ) ≤ k := Nat.cast_nonneg k
  rw [norm_mul, mul_div_assoc]
  gcongr
  split_ifs with h1
  · rw [h1, show cfgW.r + 1 - cfgW.r = 1 by rfl, pow_one]
    have : (t + k)⁻¹ - t⁻¹ = -(k : ℂ) * (t⁻¹ * (t + k)⁻¹) := by field_simp; ring
    rw [this, norm_mul, norm_mul, norm_neg, Complex.norm_natCast, norm_inv, norm_inv]
    have hq : ‖t + k‖⁻¹ ≤ 2 / ‖t‖ := by
      rw [inv_le_comm₀ (by linarith) (by positivity), inv_div]; exact htk1
    calc (k : ℝ) * (‖t‖⁻¹ * ‖t + ↑k‖⁻¹) ≤ k * (‖t‖⁻¹ * (2 / ‖t‖)) := by gcongr
      _ = 2 * k / ‖t‖ ^ 2 := by field_simp
      _ ≤ (2 * k + 4) / ‖t‖ ^ 2 := by gcongr; linarith
  · rw [sub_zero, norm_inv, norm_pow]
    have hj2 : 2 ≤ j - cfgW.r := by omega
    have hhalf : 1 ≤ ‖t‖ / 2 := by linarith
    calc (‖t + ↑k‖ ^ (j - cfgW.r))⁻¹ ≤ ((‖t‖ / 2) ^ (j - cfgW.r))⁻¹ := by
          gcongr
      _ ≤ ((‖t‖ / 2) ^ 2)⁻¹ := by
          gcongr
      _ = 4 / ‖t‖ ^ 2 := by field_simp; ring
      _ ≤ (2 * k + 4) / ‖t‖ ^ 2 := by gcongr; linarith

theorem Pw_decay1 (hV : Stmt_CoeffVanish) {n : ℕ} (hn : 1 ≤ n) :
    ∀ t : ℂ, 2 * (cfgW.h0 n : ℝ) + 2 ≤ ‖t‖ → ‖Pw n t‖ ≤ MPw n / ‖t‖ := by
  intro t ht
  have hh0 : (0 : ℝ) ≤ cfgW.h0 n := Nat.cast_nonneg _
  have ht1 : 1 ≤ ‖t‖ := by linarith
  refine le_trans (norm_Pw_le hV hn ht) ?_
  have hpos : 0 < ‖t‖ := by linarith
  rw [div_le_div_iff₀ (by positivity) hpos]
  have := MPw_nonneg n
  rw [sq]
  exact mul_le_mul_of_nonneg_left (le_mul_of_one_le_left hpos.le ht1) this

theorem Pw_vline_continuous (n : ℕ) {c : ℝ} (hc : -(cfgW.h n 1 : ℝ) < c) :
    Continuous fun y : ℝ => Pw n (c + y * I) := by
  refine (Pw_differentiableOn n).continuousOn.comp_continuous (continuous_vline c) fun y => ?_
  change -(cfgW.h n 1 : ℝ) < ((c : ℂ) + (y : ℂ) * I).re
  rw [vline_re]; exact hc

theorem Pw_vline_integrable (hV : Stmt_CoeffVanish) {n : ℕ} (hn : 1 ≤ n) {c : ℝ}
    (hc : -(cfgW.h n 1 : ℝ) < c) : Integrable fun y : ℝ => Pw n (c + y * I) := by
  have hcont := Pw_vline_continuous n hc
  have hh0 : (0 : ℝ) ≤ cfgW.h0 n := Nat.cast_nonneg _
  obtain ⟨K, hK⟩ := exists_bound_inv_one_add_sq hcont (r := 2 * (cfgW.h0 n : ℝ) + 2)
    (by linarith) (MPw_nonneg n) fun y hy => by
      have h1 := abs_le_norm_vline c y
      have hn' : 2 * (cfgW.h0 n : ℝ) + 2 ≤ ‖(c : ℂ) + (y : ℂ) * I‖ := le_trans hy h1
      refine le_trans (norm_Pw_le hV hn hn') ?_
      have hy0 : 0 < |y| := lt_of_lt_of_le (by linarith) hy
      rw [← sq_abs y]
      apply div_le_div_of_nonneg_left (MPw_nonneg n) (pow_pos hy0 2)
      exact pow_le_pow_left₀ (abs_nonneg _) h1 2
  exact integrable_of_bound_inv_one_add_sq hcont hK

/-- `∫ Pw(c+iy) (c+iy-x)^{-(j+1)} dy = -2π D_j(x)` for real `x > c > -h₁`. -/
theorem vline_Pw_right (hV : Stmt_CoeffVanish) {n : ℕ} (hn : 1 ≤ n) {c : ℝ}
    (hc : -(cfgW.h n 1 : ℝ) < c) (j : ℕ) {x : ℝ} (hx : c < x) :
    ∫ y : ℝ, Pw n (c + y * I) * (((c : ℂ) + y * I - x) ^ (j + 1))⁻¹ = -2 * π * Dw n j x := by
  have hh0 : (0 : ℝ) ≤ cfgW.h0 n := Nat.cast_nonneg _
  exact vline_higher (c' := -(cfgW.h n 1 : ℝ)) hc (Pw_differentiableOn n)
    (r := 2 * (cfgW.h0 n : ℝ) + 2) (by linarith) (MPw_nonneg n)
    (fun t _ ht2 => Pw_decay1 hV hn t ht2) (Pw_vline_integrable hV hn hc)
    (fun j x => Dw n j x) (fun x _ => (Pw_eq_Dw_zero n x).symm)
    (fun j x hx' => Dw_hasDerivAt_real n j (lt_trans hc hx')) j x hx

/-- Vanishing for poles to the left of the line. -/
theorem vline_Pw_left (hV : Stmt_CoeffVanish) {n : ℕ} (hn : 1 ≤ n) {c : ℝ}
    (hc : -(cfgW.h n 1 : ℝ) < c) {x : ℝ} (hx : x < c) {s : ℕ} (hs : 1 ≤ s) :
    ∫ y : ℝ, Pw n (c + y * I) * (((c : ℂ) + y * I - x) ^ s)⁻¹ = 0 := by
  have hh0 : (0 : ℝ) ≤ cfgW.h0 n := Nat.cast_nonneg _
  exact vline_left (c' := -(cfgW.h n 1 : ℝ)) hc (Pw_differentiableOn n)
    (r := 2 * (cfgW.h0 n : ℝ) + 2) (by linarith) (MPw_nonneg n)
    (fun t _ ht2 => Pw_decay1 hV hn t ht2) hx hs

/-! ## The kernel `K₅` and the line `Re t = 1/2 - n` -/

theorem summable_norm_hpt_sub (c : ℤ) {s : ℕ} (hs : 2 ≤ s) :
    Summable fun ν : ℤ => ‖((hpt (c - 1 - ν)) ^ s)⁻¹‖ := by
  have hsum0 : Summable fun ν : ℤ => ‖((hpt ν) ^ s)⁻¹‖ := by
    have := summable_norm_kerS_term 0 hs
    refine this.congr fun ν => ?_
    rw [norm_inv, norm_inv, norm_pow, norm_pow, zero_sub, norm_neg]
  have := (Equiv.summable_iff (Equiv.subLeft (c - 1))
    (f := fun ν : ℤ => ‖((hpt ν) ^ s)⁻¹‖)).mpr hsum0
  simpa only [Function.comp_def, Equiv.subLeft_apply] using this

/-- `K₅(t) = ∑_{ν ∈ ℤ} (t - ν)^{-5}` (poles at the integers). -/
def Kw (t : ℂ) : ℂ := kerS 5 (t + 1 / 2)

/-- The abscissa `M_n = 1/2 - n` of the contour. -/
def Mn (n : ℕ) : ℝ := 1 / 2 - n

theorem Kw_conj (t : ℂ) : Kw ((starRingEnd ℂ) t) = (starRingEnd ℂ) (Kw t) := by
  unfold Kw
  rw [← kerS_conj]
  congr 1
  simp [map_add, map_ofNat]

theorem Mn_vline (n : ℕ) (y : ℝ) :
    ((Mn n : ℝ) : ℂ) + (y : ℂ) * I + 1 / 2 = (((1 - n : ℤ) : ℂ) + (y : ℂ) * I) := by
  unfold Mn; push_cast; ring

theorem Mn_gt (n : ℕ) : -(cfgW.h n 1 : ℝ) < Mn n := by
  unfold Mn
  simp only [Config.h, cfgW, etaW]
  push_cast
  have : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  norm_num
  nlinarith

theorem norm_Kw_line_le (n : ℕ) (y : ℝ) : ‖Kw ((Mn n : ℂ) + y * I)‖ ≤ zabs 5 := by
  unfold Kw
  rw [Mn_vline]
  exact norm_kerS_vline_le (by norm_num) _ y

theorem Kw_line_continuous (n : ℕ) : Continuous fun y : ℝ => Kw ((Mn n : ℂ) + y * I) := by
  refine continuous_iff_continuousAt.2 fun y => ?_
  have hd := kerS_differentiableAt_vline (s := 5) (by norm_num) (1 - n : ℤ) y
  have hfun : (fun y : ℝ => Kw ((Mn n : ℂ) + y * I)) =
      (fun y : ℝ => kerS 5 (((1 - n : ℤ) : ℂ) + (y : ℂ) * I)) := by
    funext y; unfold Kw; rw [Mn_vline]
  rw [hfun]
  exact ContinuousAt.comp (f := fun y : ℝ => ((1 - n : ℤ) : ℂ) + (y : ℂ) * I) (x := y)
    hd.continuousAt (by fun_prop)

theorem line_integrable (hV : Stmt_CoeffVanish) {n : ℕ} (hn : 1 ≤ n) :
    Integrable fun y : ℝ => Pw n ((Mn n : ℂ) + y * I) * Kw ((Mn n : ℂ) + y * I) := by
  have hcont : Continuous fun y : ℝ => Pw n ((Mn n : ℂ) + y * I) * Kw ((Mn n : ℂ) + y * I) :=
    (Pw_vline_continuous n (Mn_gt n)).mul (Kw_line_continuous n)
  refine ((Pw_vline_integrable hV hn (Mn_gt n)).norm.mul_const (zabs 5)).mono'
    hcont.aestronglyMeasurable (Eventually.of_forall fun y => ?_)
  rw [norm_mul]
  exact mul_le_mul_of_nonneg_left (norm_Kw_line_le n y) (norm_nonneg _)

/-- **Lemma 1** (contour representation): `∫_ℝ Pw(M_n+iy) K₅(M_n+iy) dy = -2π F̃_n`. -/
theorem line_rep (hPF : Stmt_PF) (hV : Stmt_CoeffVanish) (hLF : Stmt_LinearForm) {n : ℕ}
    (hn : 1 ≤ n) :
    ∫ y : ℝ, Pw n ((Mn n : ℂ) + y * I) * Kw ((Mn n : ℂ) + y * I) = -2 * π * (Fn cfgW n : ℂ) := by
  set c : ℤ := 1 - n with hc
  set M : ℝ := Mn n with hM
  set G : ℤ → ℝ → ℂ := fun ν y =>
    Pw n ((M : ℂ) + y * I) * ((((c : ℂ) + y * I) - hpt ν) ^ 5)⁻¹ with hG
  have hexp : ∀ y : ℝ, Pw n ((M : ℂ) + y * I) * Kw ((M : ℂ) + y * I) = ∑' ν : ℤ, G ν y := by
    intro y
    simp only [hG, Kw, kerS]
    rw [hM, Mn_vline, ← hc, tsum_mul_left]
  have hker : ∀ (ν : ℤ) (y : ℝ), ‖((((c : ℂ) + y * I) - hpt ν) ^ 5)⁻¹‖ ≤
      ‖((hpt (c - 1 - ν)) ^ 5)⁻¹‖ := by
    intro ν y
    rw [norm_inv, norm_inv, norm_pow, norm_pow]
    have hpos : 0 < ‖hpt (c - 1 - ν)‖ := lt_of_lt_of_le (by norm_num) (half_le_norm_hpt _)
    gcongr
    exact norm_sub_hpt_ge_of_int c y ν
  have hPint := Pw_vline_integrable hV hn (Mn_gt n)
  have hne : ∀ (ν : ℤ) (y : ℝ), ((c : ℂ) + y * I) - hpt ν ≠ 0 := by
    intro ν y h0
    have h3 := norm_sub_hpt_ge_of_int c y ν
    rw [h0, norm_zero] at h3
    have := half_le_norm_hpt (c - 1 - ν)
    linarith
  have hGcont : ∀ ν : ℤ, Continuous (G ν) := by
    intro ν
    refine (Pw_vline_continuous n (Mn_gt n)).mul (Continuous.inv₀ (by fun_prop) fun y => ?_)
    exact pow_ne_zero _ (hne ν y)
  have hGint : ∀ ν : ℤ, Integrable (G ν) := by
    intro ν
    refine (hPint.norm.mul_const ‖((hpt (c - 1 - ν)) ^ 5)⁻¹‖).mono'
      (hGcont ν).aestronglyMeasurable (Eventually.of_forall fun y => ?_)
    simp only [hG]
    rw [norm_mul]
    exact mul_le_mul_of_nonneg_left (hker ν y) (norm_nonneg _)
  have hGsum : Summable fun ν : ℤ => ∫ y : ℝ, ‖G ν y‖ := by
    refine Summable.of_nonneg_of_le (fun ν => integral_nonneg fun y => norm_nonneg _)
      (fun ν => ?_) ((summable_norm_hpt_sub c (by norm_num : 2 ≤ 5)).mul_left
        (∫ y : ℝ, ‖Pw n ((M : ℂ) + y * I)‖))
    rw [← integral_mul_const]
    refine integral_mono (hGint ν).norm (hPint.norm.mul_const _) fun y => ?_
    simp only [hG]
    rw [norm_mul]
    exact mul_le_mul_of_nonneg_left (hker ν y) (norm_nonneg _)
  simp_rw [hexp]
  rw [← integral_tsum_of_summable_integral_norm hGint hGsum]
  -- evaluate each term
  have hval : ∀ ν : ℤ, ∫ y : ℝ, G ν y = if c ≤ ν then -2 * π * Dw n 4 (ν : ℂ) else 0 := by
    intro ν
    have hGν : ∀ y : ℝ, G ν y = Pw n ((M : ℂ) + y * I) *
        (((M : ℂ) + y * I - ((ν : ℝ) : ℂ)) ^ 5)⁻¹ := by
      intro y
      simp only [hG, hpt, hc, hM, Mn]
      congr 3
      push_cast
      ring
    simp_rw [hGν]
    split_ifs with hν
    · have hx : M < (ν : ℝ) := by
        have : ((c : ℤ) : ℝ) ≤ (ν : ℝ) := by exact_mod_cast hν
        rw [hc] at this
        push_cast at this
        rw [hM, Mn]
        linarith
      have := vline_Pw_right hV hn (Mn_gt n) 4 hx
      rw [show (4 + 1 : ℕ) = 5 from rfl] at this
      rw [this]
      push_cast
      ring
    · have hx : (ν : ℝ) < M := by
        have : (ν : ℝ) + 1 ≤ ((c : ℤ) : ℝ) := by
          have : ν + 1 ≤ c := by omega
          exact_mod_cast this
        rw [hc] at this
        push_cast at this
        rw [hM, Mn]
        linarith
      exact vline_Pw_left hV hn (Mn_gt n) hx (by norm_num)
  simp_rw [hval]
  have hinj : Function.Injective (fun l : ℕ => c + (l : ℤ)) := by
    intro a b hab
    simp only [add_right_inj, Nat.cast_inj] at hab
    exact hab
  rw [← hinj.tsum_eq (f := fun ν : ℤ => if c ≤ ν then -2 * π * Dw n 4 (ν : ℂ) else 0)]
  swap
  · intro ν hν
    simp only [Function.mem_support, ne_eq, ite_eq_right_iff, not_forall] at hν
    obtain ⟨hcν, _⟩ := hν
    refine ⟨(ν - c).toNat, ?_⟩
    simp only
    omega
  simp only [le_add_iff_nonneg_right, Nat.cast_nonneg, ↓reduceIte]
  rw [tsum_mul_left]
  congr 1
  -- `∑_{l ≥ 0} Dw 4 (1 - n + l) = ∑_{t ≥ 0} term t = F̃_n`
  have hterm : ∀ t : ℕ, Dw n 4 (((c + ((t + (n - 1) : ℕ) : ℤ) : ℤ) : ℂ)) = ((term cfgW n t : ℚ) : ℂ) := by
    intro t
    rw [term_eq_Dw hPF hn t]
    congr 1
    rw [hc]
    push_cast [Nat.cast_sub hn]
    ring
  have hsumR : Summable fun t : ℕ => ((term cfgW n t : ℚ) : ℂ) := by
    have h1 := (hLF cfgW admissible_cfgW n hn).summable
    have h2 := Complex.ofRealCLM.summable h1
    refine h2.congr fun t => ?_
    simp
  have hsumS : Summable fun l : ℕ => Dw n 4 (((c + (l : ℤ) : ℤ) : ℂ)) := by
    rw [← summable_nat_add_iff (n - 1)]
    exact hsumR.congr fun t => (hterm t).symm
  have hzero : ∀ l < n - 1, Dw n 4 (((c + (l : ℤ) : ℤ) : ℂ)) = 0 := by
    intro l hl
    have e : (((c + (l : ℤ) : ℤ) : ℂ)) = -(((n - 1 - l : ℕ) : ℕ) : ℂ) := by
      rw [hc]
      push_cast [Nat.cast_sub (by omega : l ≤ n - 1), Nat.cast_sub hn]
      ring
    rw [e]
    exact Dw_four_neg_eq_zero hPF hn (n - 1 - l) (by omega) (by omega)
  rw [tsum_nat_shift_zero hsumS (n - 1) hzero]
  simp_rw [hterm]
  unfold Fn
  rw [Complex.ofReal_tsum]
  congr 1

/-- `|F̃_n| ≤ (1/π) ‖∫_0^∞ Pw(M_n+iy) K₅(M_n+iy) dy‖`. -/
theorem abs_Fn_le (hPF : Stmt_PF) (hV : Stmt_CoeffVanish) (hLF : Stmt_LinearForm) {n : ℕ}
    (hn : 1 ≤ n) :
    |Fn cfgW n| ≤
      ‖∫ y in Ioi (0 : ℝ), Pw n ((Mn n : ℂ) + y * I) * Kw ((Mn n : ℂ) + y * I)‖ / π := by
  have hrep := line_rep hPF hV hLF hn
  have hconj : ∀ t, (fun t => Pw n t * Kw t) ((starRingEnd ℂ) t) =
      (starRingEnd ℂ) ((fun t => Pw n t * Kw t) t) := by
    intro t
    simp only [Pw_conj, Kw_conj, map_mul]
  have h2 := norm_integral_line_conj_le (f := fun t => Pw n t * Kw t) (c := Mn n) hconj
    (line_integrable hV hn)
  rw [hrep] at h2
  have hpi : 0 < π := Real.pi_pos
  have hn2 : ‖-2 * (π : ℂ) * (Fn cfgW n : ℂ)‖ = 2 * π * |Fn cfgW n| := by
    rw [norm_mul, norm_mul, norm_neg, Complex.norm_real, Complex.norm_real, Real.norm_eq_abs,
      Real.norm_eq_abs, abs_of_pos hpi]
    norm_num
  rw [hn2] at h2
  rw [le_div_iff₀ hpi]
  nlinarith [abs_nonneg (Fn cfgW n)]

end L20U

end ZetaWindow

end
