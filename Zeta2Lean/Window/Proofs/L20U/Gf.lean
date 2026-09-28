module

public import Zeta2Lean.Window.Statements

@[expose] public section

set_option linter.style.header false
set_option linter.style.longLine false

/-!
# Theorem U, part 2: the primitive `Gf` and the window comparison (Lemma 3)

`Gf a y = (a/2) log(a² + y²) + y arctan(a/y) - a` is a primitive in `a` of
`log |a + i y| = log(a² + y²)/2` (`y > 0`).  The first block (`Gf`, `Gf_hasDerivAt`, `Gf_sub_ge`,
`Gf_sub_le`, `Gf_mono`, `norm_eq_exp_log`, `Gf_scale`, `Gf_hasDerivAt_y`, `continuous_Gf_y`) is
copied verbatim from the proved pair project (`Pair/Proofs/Growth.lean`).

New here (crude-upper-bound.md §4, Lemma 3, for **every** `y > 0`; the pair's `num_sum_le`,
`den_sum_ge` need `y ≥ 1`):
* `win_up` (`α ≥ 0`), `win_down` (`α + N ≤ 1`): upper bounds of `∑_{m<N} log|α + m + iy|` by
  `∫ log|u + iy| du` over the adjacent unit intervals;
* `win_lower` (`α ≥ 1`): the lower bound;
* `num_window`: the numerator window `∑_{i=1}^{h₀-1} log|M + i + iy|` on the half-integer line
  `M = 1/2 - n`, `≤ Gf(M + h₀) - Gf(M) + 1 + log 2` (the one unit interval `[-1/2, 1/2]` that is
  not covered costs `-2 Gf(1/2, y) ≤ 1 + log 2`);
* `den_window`: `∑_{i=a}^{b} log|M + i + iy| ≥ Gf(M + b) - Gf(M + a - 1)` when `M + a ≥ 1`;
* `Gf_shift_le`, `Gf_shift_nonneg`: moving an endpoint by `δ` costs at most `δ log(|a| + δ + y)`
  (and nothing, in the favourable direction, where `|u| ≥ 1`).
-/

open Complex MeasureTheory Filter Topology Set Finset
open scoped Real

noncomputable section

namespace ZetaWindow

namespace L20U

/-! ## The primitive `Gf` -/

/-- A primitive of `σ ↦ log(σ² + y²)/2` (for `y > 0`); at `y = 0` it is `a log|a| - a`. -/
def Gf (a y : ℝ) : ℝ := a / 2 * Real.log (a ^ 2 + y ^ 2) + y * Real.arctan (a / y) - a

theorem Gf_hasDerivAt {y : ℝ} (hy : 0 < y) (a : ℝ) :
    HasDerivAt (fun a => Gf a y) (Real.log (a ^ 2 + y ^ 2) / 2) a := by
  have hpos : 0 < a ^ 2 + y ^ 2 := by positivity
  have h1 : HasDerivAt (fun a : ℝ => a ^ 2 + y ^ 2) (2 * a) a := by
    simpa using (hasDerivAt_pow 2 a).add_const (y ^ 2)
  have h2 := h1.log hpos.ne'
  have h3 : HasDerivAt (fun a : ℝ => a / y) (1 / y) a := by
    simpa using (hasDerivAt_id a).div_const y
  have h4 := h3.arctan
  have h5 := ((hasDerivAt_id a).div_const 2).mul h2
  have h6 := h4.const_mul y
  have h7 := (h5.add h6).sub (hasDerivAt_id a)
  convert h7 using 1
  · funext a; simp [Gf]
  · have hy0 : y ≠ 0 := hy.ne'
    simp only [id]
    field_simp
    ring

theorem Gf_sub_ge {y : ℝ} (hy : 0 < y) {α β : ℝ} (hab : α ≤ β) {L : ℝ}
    (hL : ∀ ξ ∈ Set.Icc α β, L ≤ Real.log (ξ ^ 2 + y ^ 2) / 2) :
    L * (β - α) ≤ Gf β y - Gf α y := by
  rcases eq_or_lt_of_le hab with h | h
  · subst h; simp
  · obtain ⟨ξ, hξ, hξeq⟩ := exists_hasDerivAt_eq_slope (fun a => Gf a y)
      (fun a => Real.log (a ^ 2 + y ^ 2) / 2) h
      (fun x _ => (Gf_hasDerivAt hy x).continuousAt.continuousWithinAt)
      (fun x _ => Gf_hasDerivAt hy x)
    have h1 := hL ξ ⟨hξ.1.le, hξ.2.le⟩
    rw [hξeq] at h1
    have hpos : 0 < β - α := by linarith
    rw [le_div_iff₀ hpos] at h1
    linarith

theorem Gf_sub_le {y : ℝ} (hy : 0 < y) {α β : ℝ} (hab : α ≤ β) {L : ℝ}
    (hL : ∀ ξ ∈ Set.Icc α β, Real.log (ξ ^ 2 + y ^ 2) / 2 ≤ L) :
    Gf β y - Gf α y ≤ L * (β - α) := by
  rcases eq_or_lt_of_le hab with h | h
  · subst h; simp
  · obtain ⟨ξ, hξ, hξeq⟩ := exists_hasDerivAt_eq_slope (fun a => Gf a y)
      (fun a => Real.log (a ^ 2 + y ^ 2) / 2) h
      (fun x _ => (Gf_hasDerivAt hy x).continuousAt.continuousWithinAt)
      (fun x _ => Gf_hasDerivAt hy x)
    have h1 := hL ξ ⟨hξ.1.le, hξ.2.le⟩
    rw [hξeq] at h1
    have hpos : 0 < β - α := by linarith
    rw [div_le_iff₀ hpos] at h1
    linarith

theorem Gf_mono {y : ℝ} (hy : 1 ≤ y) {α β : ℝ} (hab : α ≤ β) : Gf α y ≤ Gf β y := by
  have := Gf_sub_ge (y := y) (by linarith) hab (L := 0) fun ξ _ => by
    have h1 : 1 ≤ ξ ^ 2 + y ^ 2 := by nlinarith
    have := Real.log_nonneg h1
    linarith
  linarith

/-- `‖w‖ = exp(log(re² + im²)/2)` when `Im w ≠ 0`. -/
theorem norm_eq_exp_log (w : ℂ) (hw : w.im ≠ 0) :
    ‖w‖ = Real.exp (Real.log (w.re ^ 2 + w.im ^ 2) / 2) := by
  have hpos : 0 < w.re ^ 2 + w.im ^ 2 := by
    have : 0 < w.im ^ 2 := by positivity
    linarith [sq_nonneg w.re]
  have h1 : ‖w‖ = Real.sqrt (w.re ^ 2 + w.im ^ 2) := Complex.norm_eq_sqrt_sq_add_sq w
  rw [h1, Real.sqrt_eq_rpow, Real.rpow_def_of_pos hpos]
  ring_nf

theorem Gf_scale {N : ℝ} (hN : 0 < N) (a : ℝ) {y : ℝ} (hy : 0 < y) :
    Gf (N * a) (N * y) = N * Gf a y + N * a * Real.log N := by
  unfold Gf
  have h1 : (N * a) ^ 2 + (N * y) ^ 2 = N ^ 2 * (a ^ 2 + y ^ 2) := by ring
  have h2 : 0 < a ^ 2 + y ^ 2 := by positivity
  rw [h1, Real.log_mul (by positivity) h2.ne', Real.log_pow, mul_div_mul_left _ _ hN.ne']
  push_cast
  ring

/-! ## Derivative and continuity in `y` -/

theorem Gf_hasDerivAt_y (a : ℝ) {y : ℝ} (hy : 0 < y) :
    HasDerivAt (fun y => Gf a y) (Real.arctan (a / y)) y := by
  have hpos : 0 < a ^ 2 + y ^ 2 := by positivity
  have h1 : HasDerivAt (fun y : ℝ => a ^ 2 + y ^ 2) (2 * y) y := by
    simpa using (hasDerivAt_pow 2 y).const_add (a ^ 2)
  have h2 := (h1.log hpos.ne').const_mul (a / 2)
  have h3 : HasDerivAt (fun y : ℝ => a / y) (-a / y ^ 2) y := by
    have := (hasDerivAt_inv hy.ne').const_mul a
    convert this using 1
    · ext y'; simp [div_eq_mul_inv]
    · field_simp
  have h4 := h3.arctan
  have h5 := (hasDerivAt_id y).mul h4
  have h6 := (h2.add h5).sub_const a
  convert h6 using 1
  · ext y'; simp [Gf]
  · simp only [id]
    field_simp
    ring

theorem continuous_mul_arctan_div (a : ℝ) : Continuous fun y : ℝ => y * Real.arctan (a / y) := by
  refine continuous_iff_continuousAt.2 fun y₀ => ?_
  by_cases hy₀ : y₀ = 0
  · subst hy₀
    show Tendsto (fun y : ℝ => y * Real.arctan (a / y)) (𝓝 0) (𝓝 (0 * Real.arctan (a / 0)))
    rw [zero_mul]
    refine squeeze_zero_norm (a := fun y : ℝ => |y| * (π / 2)) (fun y => ?_) ?_
    · rw [Real.norm_eq_abs, abs_mul]
      gcongr
      exact abs_le.mpr ⟨(Real.neg_pi_div_two_lt_arctan _).le, (Real.arctan_lt_pi_div_two _).le⟩
    · have : Tendsto (fun y : ℝ => |y| * (π / 2)) (𝓝 0) (𝓝 (|0| * (π / 2))) :=
        (continuous_abs.mul continuous_const).continuousAt
      simpa using this
  · exact continuousAt_id.mul (Real.continuous_arctan.continuousAt.comp
      (continuousAt_const.div continuousAt_id hy₀))

theorem continuous_Gf_y (a : ℝ) : Continuous fun y : ℝ => Gf a y := by
  unfold Gf
  have hlog : Continuous fun y : ℝ => a / 2 * Real.log (a ^ 2 + y ^ 2) := by
    by_cases ha : a = 0
    · subst ha; simp only [zero_div, zero_mul]; exact continuous_const
    · have h1 : 0 < a ^ 2 := by positivity
      have hc : Continuous fun y : ℝ => a ^ 2 + y ^ 2 := by fun_prop
      refine continuous_const.mul (hc.log fun y => ?_)
      have h2 := sq_nonneg y
      exact ne_of_gt (by linarith)
  exact (hlog.add (continuous_mul_arctan_div a)).sub continuous_const

/-! ## Window comparison for every `y > 0` (new; crude-upper-bound.md §4) -/

theorem Gf_neg (a y : ℝ) : Gf (-a) y = -Gf a y := by
  unfold Gf
  simp only [neg_sq, neg_div, Real.arctan_neg]
  ring

/-- `log(u² + y²)/2` is monotone in `|u|`. -/
theorem logsq_le {y u v : ℝ} (hy : 0 < y) (h : |u| ≤ |v|) :
    Real.log (u ^ 2 + y ^ 2) / 2 ≤ Real.log (v ^ 2 + y ^ 2) / 2 := by
  have h1 : u ^ 2 ≤ v ^ 2 := by
    rw [← sq_abs u, ← sq_abs v]; exact pow_le_pow_left₀ (abs_nonneg _) h 2
  have h2 : 0 < u ^ 2 + y ^ 2 := by positivity
  have := Real.log_le_log h2 (show u ^ 2 + y ^ 2 ≤ v ^ 2 + y ^ 2 by linarith)
  linarith

/-- Increasing side (`α ≥ 0`): `∑_{m<N} log|α+m+iy| ≤ ∫_α^{α+N} log|u+iy| du`. -/
theorem win_up {y : ℝ} (hy : 0 < y) {α : ℝ} (hα : 0 ≤ α) (N : ℕ) :
    ∑ m ∈ range N, Real.log ((α + m) ^ 2 + y ^ 2) / 2 ≤ Gf (α + N) y - Gf α y := by
  induction N with
  | zero => simp
  | succ N ih =>
    rw [sum_range_succ]
    have hN : (0 : ℝ) ≤ N := Nat.cast_nonneg N
    have hstep := Gf_sub_ge hy (show α + N ≤ α + N + 1 by linarith)
      (L := Real.log ((α + N) ^ 2 + y ^ 2) / 2) fun ξ hξ => by
        apply logsq_le hy
        rw [abs_of_nonneg (by linarith), abs_of_nonneg (by linarith [hξ.1])]
        exact hξ.1
    have e2 : α + N + 1 - (α + N) = 1 := by ring
    rw [e2, mul_one] at hstep
    have e3 : α + ((N + 1 : ℕ) : ℝ) = α + N + 1 := by push_cast; ring
    rw [e3]
    linarith

/-- Decreasing side (`α + N ≤ 1`, i.e. all points `≤ 0`):
`∑_{m<N} log|α+m+iy| ≤ ∫_{α-1}^{α+N-1} log|u+iy| du`. -/
theorem win_down {y : ℝ} (hy : 0 < y) {α : ℝ} (N : ℕ) (hα : α + N ≤ 1) :
    ∑ m ∈ range N, Real.log ((α + m) ^ 2 + y ^ 2) / 2 ≤ Gf (α + N - 1) y - Gf (α - 1) y := by
  induction N with
  | zero => simp
  | succ N ih =>
    rw [sum_range_succ]
    have hN1 : α + (N : ℝ) + 1 ≤ 1 := by push_cast at hα; linarith
    have ih' := ih (by linarith)
    have hstep := Gf_sub_ge hy (show α + N - 1 ≤ α + N by linarith)
      (L := Real.log ((α + N) ^ 2 + y ^ 2) / 2) fun ξ hξ => by
        apply logsq_le hy
        rw [abs_of_nonpos (by linarith), abs_of_nonpos (by linarith [hξ.2])]
        linarith [hξ.2]
    have e2 : α + N - (α + N - 1) = 1 := by ring
    rw [e2, mul_one] at hstep
    have e3 : α + ((N + 1 : ℕ) : ℝ) - 1 = α + N := by push_cast; ring
    rw [e3]
    linarith

/-- Lower bound (`α ≥ 1`): `∑_{m<N} log|α+m+iy| ≥ ∫_{α-1}^{α+N-1} log|u+iy| du`. -/
theorem win_lower {y : ℝ} (hy : 0 < y) {α : ℝ} (hα : 1 ≤ α) (N : ℕ) :
    Gf (α + N - 1) y - Gf (α - 1) y ≤ ∑ m ∈ range N, Real.log ((α + m) ^ 2 + y ^ 2) / 2 := by
  induction N with
  | zero => simp
  | succ N ih =>
    rw [sum_range_succ]
    have hN : (0 : ℝ) ≤ N := Nat.cast_nonneg N
    have hstep := Gf_sub_le hy (show α + N - 1 ≤ α + N by linarith)
      (L := Real.log ((α + N) ^ 2 + y ^ 2) / 2) fun ξ hξ => by
        apply logsq_le hy
        rw [abs_of_nonneg (by linarith [hξ.1]), abs_of_nonneg (by linarith)]
        exact hξ.2
    have e2 : α + N - (α + N - 1) = 1 := by ring
    rw [e2, mul_one] at hstep
    have e3 : α + ((N + 1 : ℕ) : ℝ) - 1 = α + N := by push_cast; ring
    rw [e3]
    linarith

/-- `-2 Gf(1/2, y) ≤ 1 + log 2`: the unit interval `[-1/2, 1/2]` around the zero of `u`. -/
theorem Gf_half_ge {y : ℝ} (hy : 0 < y) : -(1 + Real.log 2) ≤ 2 * Gf (1 / 2) y := by
  unfold Gf
  have h1 : Real.log (1 / 4) ≤ Real.log ((1 / 2) ^ 2 + y ^ 2) :=
    Real.log_le_log (by norm_num) (by nlinarith)
  have h2 : Real.log (1 / 4 : ℝ) = -(2 * Real.log 2) := by
    rw [show (1 / 4 : ℝ) = (2 ^ 2)⁻¹ by norm_num, Real.log_inv, Real.log_pow]; push_cast; ring
  have h3 : 0 ≤ Real.arctan (1 / 2 / y) := by
    have := Real.arctan_strictMono.monotone (show (0 : ℝ) ≤ 1 / 2 / y by positivity)
    rwa [Real.arctan_zero] at this
  have h4 : 0 ≤ y * Real.arctan (1 / 2 / y) := mul_nonneg hy.le h3
  nlinarith

/-- **Numerator window** on the half-integer line `M = 1/2 - n` (Lemma 3(a)):
`∑_{i=1}^{h₀-1} log|M+i+iy| ≤ Gf(M+h₀, y) - Gf(M, y) + 1 + log 2`. -/
theorem num_window {y : ℝ} (hy : 0 < y) (n h0 : ℕ) (hn : 1 ≤ n) (hnh : n ≤ h0) :
    ∑ i ∈ Ico 1 h0, Real.log (((1 / 2 - n : ℝ) + i) ^ 2 + y ^ 2) / 2 ≤
      Gf ((1 / 2 - n : ℝ) + h0) y - Gf (1 / 2 - n : ℝ) y + (1 + Real.log 2) := by
  rw [← Finset.sum_Ico_consecutive _ hn hnh, Finset.sum_Ico_eq_sum_range,
    Finset.sum_Ico_eq_sum_range]
  have hn1 : ((n - 1 : ℕ) : ℝ) = (n : ℝ) - 1 := by rw [Nat.cast_sub hn]; push_cast; ring
  have hnh' : ((h0 - n : ℕ) : ℝ) = (h0 : ℝ) - n := by rw [Nat.cast_sub hnh]
  have h1 : ∑ m ∈ range (n - 1), Real.log (((1 / 2 - n : ℝ) + ((1 + m : ℕ) : ℝ)) ^ 2 + y ^ 2) / 2 ≤
      Gf (-(1 / 2)) y - Gf (1 / 2 - n) y := by
    have := win_down hy (α := 3 / 2 - n) (n - 1) (by rw [hn1]; linarith)
    rw [hn1] at this
    have e1 : (3 / 2 - n : ℝ) + ((n : ℝ) - 1) - 1 = -(1 / 2) := by ring
    have e2 : (3 / 2 - n : ℝ) - 1 = 1 / 2 - n := by ring
    rw [e1, e2] at this
    refine le_trans (le_of_eq ?_) this
    refine Finset.sum_congr rfl fun m _ => ?_
    push_cast
    ring_nf
  have h2 : ∑ m ∈ range (h0 - n), Real.log (((1 / 2 - n : ℝ) + ((n + m : ℕ) : ℝ)) ^ 2 + y ^ 2) / 2 ≤
      Gf (1 / 2 + ((h0 : ℝ) - n)) y - Gf (1 / 2) y := by
    have := win_up hy (α := 1 / 2) (by norm_num) (h0 - n)
    rw [hnh'] at this
    refine le_trans (le_of_eq ?_) this
    refine Finset.sum_congr rfl fun m _ => ?_
    push_cast
    ring_nf
  have h3 := Gf_half_ge hy
  have h4 : Gf (-(1 / 2)) y = -Gf (1 / 2) y := Gf_neg _ _
  have e : (1 / 2 : ℝ) + ((h0 : ℝ) - n) = (1 / 2 - n : ℝ) + h0 := by ring
  rw [e] at h2
  linarith

/-- **Denominator window** (Lemma 3(b)): for `M + a ≥ 1`,
`∑_{i=a}^{b} log|M+i+iy| ≥ Gf(M+b, y) - Gf(M+a-1, y)`. -/
theorem den_window {y : ℝ} (hy : 0 < y) (M : ℝ) (a b : ℕ) (hab : a ≤ b + 1) (hMa : 1 ≤ M + a) :
    Gf (M + b) y - Gf (M + a - 1) y ≤ ∑ i ∈ Icc a b, Real.log ((M + i) ^ 2 + y ^ 2) / 2 := by
  have hI : Finset.Icc a b = Finset.Ico a (b + 1) := by
    ext i; simp only [Finset.mem_Icc, Finset.mem_Ico]; omega
  rw [hI, Finset.sum_Ico_eq_sum_range]
  have := win_lower hy hMa (b + 1 - a)
  have hc : ((b + 1 - a : ℕ) : ℝ) = (b : ℝ) + 1 - a := by rw [Nat.cast_sub hab]; push_cast; ring
  rw [hc] at this
  have e : M + a + ((b : ℝ) + 1 - a) - 1 = M + b := by ring
  rw [e] at this
  refine le_trans this (le_of_eq ?_)
  refine Finset.sum_congr rfl fun m _ => ?_
  push_cast
  ring_nf

/-- Moving the upper endpoint up by `δ` costs at most `δ log(|a| + δ + y)`. -/
theorem Gf_shift_le {y : ℝ} (hy : 0 < y) (a : ℝ) {δ : ℝ} (hδ : 0 ≤ δ) :
    Gf (a + δ) y - Gf a y ≤ δ * Real.log (|a| + δ + y) := by
  have h := Gf_sub_le hy (show a ≤ a + δ by linarith) (L := Real.log (|a| + δ + y)) fun ξ hξ => by
    have hpos : 0 < ξ ^ 2 + y ^ 2 := by positivity
    have hξa : |ξ| ≤ |a| + δ := by
      rw [abs_le]; constructor <;> linarith [hξ.1, hξ.2, le_abs_self a, neg_abs_le a]
    have hsq : ξ ^ 2 ≤ (|a| + δ) ^ 2 := by
      rw [← sq_abs ξ]; exact pow_le_pow_left₀ (abs_nonneg _) hξa 2
    have hle : ξ ^ 2 + y ^ 2 ≤ (|a| + δ + y) ^ 2 := by
      nlinarith [abs_nonneg a]
    have := Real.log_le_log hpos hle
    rw [Real.log_pow] at this
    push_cast at this
    linarith
  have e : a + δ - a = δ := by ring
  rw [e] at h
  linarith

/-- `Gf` is increasing on intervals where `|u| ≥ 1`. -/
theorem Gf_shift_nonneg {y : ℝ} (hy : 0 < y) {a b : ℝ} (hab : a ≤ b)
    (h1 : ∀ u ∈ Set.Icc a b, 1 ≤ |u|) : Gf a y ≤ Gf b y := by
  have h := Gf_sub_ge hy hab (L := 0) fun ξ hξ => by
    have h2 := h1 ξ hξ
    have hsq : 1 ≤ ξ ^ 2 + y ^ 2 := by nlinarith [sq_abs ξ, abs_nonneg ξ]
    have := Real.log_nonneg hsq
    linarith
  linarith

end L20U

end ZetaWindow

end
