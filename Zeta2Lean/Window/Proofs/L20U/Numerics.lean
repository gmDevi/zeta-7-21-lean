import Zeta2Lean.Window.Statements

set_option linter.style.header false
set_option linter.style.longLine false

/-!
# Certified numerics for the landscape inequalities

Verbatim copy (namespace changed) of `Zeta2Lean/Pair/Proofs/Landscape/Numerics.lean` of the
proved pair project (https://github.com/gmDevi/zeta2-7-9-lean); used by `L20U/Cert.lean`.

Rigorous rational bounds for `Real.log q` and `Real.arctan u` at explicit rationals, in a form
where every side condition is a closed rational inequality checked by `norm_num`.

* **Logarithms.**  For `0 ≤ z < 1`, `log ((1 + z)/(1 - z)) = 2 ∑ z^(2k+1)/(2k+1)`
  (`Real.hasSum_log_sub_log_of_abs_lt_one`), hence
  `Slog z ≤ log ((1+z)/(1-z)) ≤ Slog z + Rlog z` (six terms, geometric tail).  A rational
  `q > 0` is written as `q = 2^k (1+z)/(1-z)` (or `q 2^k = (1+z)/(1-z)`) and `log 2` is bounded by
  `Real.log_two_gt_d9`, `Real.log_two_lt_d9`.
* **Arctangents.**  For `w ≥ 0`, `Pat8 w ≤ arctan w ≤ Pat9 w` (alternating Taylor polynomials of
  degree 15 and 17; derivative comparison).  Range reduction: `arctan u = π/4 ± arctan w` with
  `w = |u - 1|/(u + 1)`, and `arctan u = π/2 - arctan (1/u)` for `u > 0`.
* **`x log x`.** Monotone on `[2/5, ∞)`, antitone on `[0, 1/3]` and on `[-1/3, 0]`.
-/

open Real Finset

noncomputable section

namespace ZetaWindow.L20U

/-! ## Logarithms -/

/-- Twice the partial sum `z + z³/3 + ⋯ + z¹¹/11` of `artanh z`. -/
def Slog (z : ℝ) : ℝ := 2 * (z + z ^ 3 / 3 + z ^ 5 / 5 + z ^ 7 / 7 + z ^ 9 / 9 + z ^ 11 / 11)

/-- The tail bound `2 z¹³ / (13 (1 - z²))`. -/
def Rlog (z : ℝ) : ℝ := 2 * z ^ 13 / (13 * (1 - z ^ 2))

theorem log_ratio_hasSum {z : ℝ} (hz0 : 0 ≤ z) (hz1 : z < 1) :
    HasSum (fun k : ℕ => (2 : ℝ) * (1 / (2 * k + 1)) * z ^ (2 * k + 1))
      (Real.log ((1 + z) / (1 - z))) := by
  have habs : |z| < 1 := by rw [abs_of_nonneg hz0]; exact hz1
  rw [Real.log_div (by linarith) (by linarith)]
  exact Real.hasSum_log_sub_log_of_abs_lt_one habs

theorem Slog_le_log {z : ℝ} (hz0 : 0 ≤ z) (hz1 : z < 1) :
    Slog z ≤ Real.log ((1 + z) / (1 - z)) := by
  have h := log_ratio_hasSum hz0 hz1
  have := sum_le_hasSum (range 6) (fun i _ => by positivity) h
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at this
  unfold Slog
  norm_num at this
  linarith

theorem log_le_Slog_add {z : ℝ} (hz0 : 0 ≤ z) (hz1 : z < 1) :
    Real.log ((1 + z) / (1 - z)) ≤ Slog z + Rlog z := by
  have h := log_ratio_hasSum hz0 hz1
  set f : ℕ → ℝ := fun k => (2 : ℝ) * (1 / (2 * k + 1)) * z ^ (2 * k + 1) with hf
  have htail : HasSum (fun k => f (k + 6)) (Real.log ((1 + z) / (1 - z)) - ∑ i ∈ range 6, f i) :=
    (hasSum_nat_add_iff' 6).mpr h
  have hz2 : z ^ 2 < 1 := by nlinarith
  have hgeom : HasSum (fun k : ℕ => (2 * z ^ 13 / 13) * (z ^ 2) ^ k)
      ((2 * z ^ 13 / 13) * (1 - z ^ 2)⁻¹) :=
    (hasSum_geometric_of_lt_one (by positivity) hz2).mul_left _
  have hle : ∀ k : ℕ, f (k + 6) ≤ (2 * z ^ 13 / 13) * (z ^ 2) ^ k := by
    intro k
    simp only [hf]
    have e : z ^ (2 * (k + 6) + 1) = z ^ 13 * (z ^ 2) ^ k := by ring
    rw [e]
    have hk : (0 : ℝ) ≤ k := k.cast_nonneg
    have h1 : (1 : ℝ) / (2 * ((k + 6 : ℕ) : ℝ) + 1) ≤ 1 / 13 := by
      push_cast
      rw [div_le_div_iff₀ (by positivity) (by norm_num)]
      linarith
    have h2 : 0 ≤ z ^ 13 * (z ^ 2) ^ k := by positivity
    calc 2 * (1 / (2 * ((k + 6 : ℕ) : ℝ) + 1)) * (z ^ 13 * (z ^ 2) ^ k)
        ≤ 2 * (1 / 13) * (z ^ 13 * (z ^ 2) ^ k) := by gcongr
      _ = 2 * z ^ 13 / 13 * (z ^ 2) ^ k := by ring
  have := hasSum_le hle htail hgeom
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, hf] at this
  have hz3 : 0 < 1 - z ^ 2 := by linarith
  have e2 : 2 * z ^ 13 / 13 * (1 - z ^ 2)⁻¹ = Rlog z := by
    unfold Rlog; field_simp
  rw [e2] at this
  unfold Slog
  norm_num at this
  linarith

theorem log_two_le_d9 : Real.log 2 ≤ 6931471808 / 10 ^ 10 := by
  have := Real.log_two_lt_d9; norm_num at this ⊢; linarith

theorem d9_le_log_two : (6931471803 / 10 ^ 10 : ℝ) ≤ Real.log 2 := by
  have := Real.log_two_gt_d9; norm_num at this ⊢; linarith

/-- Upper bound, `q ≤ 2^k (1+z)/(1-z)`. -/
theorem log_le_of_le_mul {q z U : ℝ} (k : ℕ) (hz0 : 0 ≤ z) (hz1 : z < 1) (hq : 0 < q)
    (hqt : q ≤ 2 ^ k * ((1 + z) / (1 - z)))
    (hU : Slog z + Rlog z + k * (6931471808 / 10 ^ 10) ≤ U) : Real.log q ≤ U := by
  have ht : 0 < (1 + z) / (1 - z) := div_pos (by linarith) (by linarith)
  have h1 : Real.log q ≤ Real.log (2 ^ k * ((1 + z) / (1 - z))) := Real.log_le_log hq hqt
  rw [Real.log_mul (by positivity) ht.ne', Real.log_pow] at h1
  have h2 := log_le_Slog_add hz0 hz1
  have hk : (0 : ℝ) ≤ k := k.cast_nonneg
  have h4 : (k : ℝ) * Real.log 2 ≤ k * (6931471808 / 10 ^ 10) :=
    mul_le_mul_of_nonneg_left log_two_le_d9 hk
  linarith

/-- Upper bound, `q 2^k ≤ (1+z)/(1-z)`. -/
theorem log_le_of_mul_le {q z U : ℝ} (k : ℕ) (hz0 : 0 ≤ z) (hz1 : z < 1) (hq : 0 < q)
    (hqt : q * 2 ^ k ≤ (1 + z) / (1 - z))
    (hU : Slog z + Rlog z - k * (6931471803 / 10 ^ 10) ≤ U) : Real.log q ≤ U := by
  have h1 : Real.log (q * 2 ^ k) ≤ Real.log ((1 + z) / (1 - z)) :=
    Real.log_le_log (by positivity) hqt
  rw [Real.log_mul hq.ne' (by positivity), Real.log_pow] at h1
  have h2 := log_le_Slog_add hz0 hz1
  have hk : (0 : ℝ) ≤ k := k.cast_nonneg
  have h4 : (k : ℝ) * (6931471803 / 10 ^ 10) ≤ k * Real.log 2 :=
    mul_le_mul_of_nonneg_left d9_le_log_two hk
  linarith

/-- Lower bound, `2^k (1+z)/(1-z) ≤ q`. -/
theorem le_log_of_mul_le {q z L : ℝ} (k : ℕ) (hz0 : 0 ≤ z) (hz1 : z < 1)
    (hqt : 2 ^ k * ((1 + z) / (1 - z)) ≤ q)
    (hL : L ≤ Slog z + k * (6931471803 / 10 ^ 10)) : L ≤ Real.log q := by
  have ht : 0 < (1 + z) / (1 - z) := div_pos (by linarith) (by linarith)
  have h1 : Real.log (2 ^ k * ((1 + z) / (1 - z))) ≤ Real.log q :=
    Real.log_le_log (by positivity) hqt
  rw [Real.log_mul (by positivity) ht.ne', Real.log_pow] at h1
  have h2 := Slog_le_log hz0 hz1
  have hk : (0 : ℝ) ≤ k := k.cast_nonneg
  have h4 : (k : ℝ) * (6931471803 / 10 ^ 10) ≤ k * Real.log 2 :=
    mul_le_mul_of_nonneg_left d9_le_log_two hk
  linarith

/-- Lower bound, `(1+z)/(1-z) ≤ q 2^k`. -/
theorem le_log_of_le_mul {q z L : ℝ} (k : ℕ) (hz0 : 0 ≤ z) (hz1 : z < 1) (hq : 0 < q)
    (hqt : (1 + z) / (1 - z) ≤ q * 2 ^ k)
    (hL : L ≤ Slog z - k * (6931471808 / 10 ^ 10)) : L ≤ Real.log q := by
  have ht : 0 < (1 + z) / (1 - z) := div_pos (by linarith) (by linarith)
  have h1 : Real.log ((1 + z) / (1 - z)) ≤ Real.log (q * 2 ^ k) := Real.log_le_log ht hqt
  rw [Real.log_mul hq.ne' (by positivity), Real.log_pow] at h1
  have h2 := Slog_le_log hz0 hz1
  have hk : (0 : ℝ) ≤ k := k.cast_nonneg
  have h4 : (k : ℝ) * Real.log 2 ≤ k * (6931471808 / 10 ^ 10) :=
    mul_le_mul_of_nonneg_left log_two_le_d9 hk
  linarith

/-! ## Arctangents -/

/-- Taylor polynomial of `arctan` of degree 15 (a lower bound on `[0, ∞)`). -/
def Pat8 (w : ℝ) : ℝ :=
  w - w ^ 3 / 3 + w ^ 5 / 5 - w ^ 7 / 7 + w ^ 9 / 9 - w ^ 11 / 11 + w ^ 13 / 13 - w ^ 15 / 15

/-- Taylor polynomial of `arctan` of degree 17 (an upper bound on `[0, ∞)`). -/
def Pat9 (w : ℝ) : ℝ := Pat8 w + w ^ 17 / 17

theorem hasDerivAt_Pat8 (x : ℝ) :
    HasDerivAt Pat8 (1 - x ^ 2 + x ^ 4 - x ^ 6 + x ^ 8 - x ^ 10 + x ^ 12 - x ^ 14) x := by
  have h := ((((((((hasDerivAt_id x).sub ((hasDerivAt_pow 3 x).div_const 3)).add
    ((hasDerivAt_pow 5 x).div_const 5)).sub ((hasDerivAt_pow 7 x).div_const 7)).add
    ((hasDerivAt_pow 9 x).div_const 9)).sub ((hasDerivAt_pow 11 x).div_const 11)).add
    ((hasDerivAt_pow 13 x).div_const 13)).sub ((hasDerivAt_pow 15 x).div_const 15))
  convert h using 1
  · funext w; simp [Pat8]
  · norm_num

theorem hasDerivAt_Pat9 (x : ℝ) :
    HasDerivAt Pat9 (1 - x ^ 2 + x ^ 4 - x ^ 6 + x ^ 8 - x ^ 10 + x ^ 12 - x ^ 14 + x ^ 16) x := by
  have h := (hasDerivAt_Pat8 x).add ((hasDerivAt_pow 17 x).div_const 17)
  convert h using 1
  · funext w; rfl
  · norm_num

theorem Pat8_le_arctan {w : ℝ} (hw : 0 ≤ w) : Pat8 w ≤ Real.arctan w := by
  set g : ℝ → ℝ := fun x => Real.arctan x - Pat8 x with hg
  have hd : ∀ x, HasDerivAt g (x ^ 16 / (1 + x ^ 2)) x := by
    intro x
    have h := (Real.hasDerivAt_arctan x).sub (hasDerivAt_Pat8 x)
    convert h using 1
    have : (0 : ℝ) < 1 + x ^ 2 := by positivity
    field_simp
    ring
  have hmono : Monotone g := by
    refine monotone_of_deriv_nonneg (fun x => (hd x).differentiableAt) fun x => ?_
    rw [(hd x).deriv]; positivity
  have := hmono hw
  simp only [hg, Real.arctan_zero] at this
  have h0 : Pat8 0 = 0 := by simp [Pat8]
  linarith

theorem arctan_le_Pat9 {w : ℝ} (hw : 0 ≤ w) : Real.arctan w ≤ Pat9 w := by
  set g : ℝ → ℝ := fun x => Pat9 x - Real.arctan x with hg
  have hd : ∀ x, HasDerivAt g (x ^ 18 / (1 + x ^ 2)) x := by
    intro x
    have h := (hasDerivAt_Pat9 x).sub (Real.hasDerivAt_arctan x)
    convert h using 1
    have : (0 : ℝ) < 1 + x ^ 2 := by positivity
    field_simp
    ring
  have hmono : Monotone g := by
    refine monotone_of_deriv_nonneg (fun x => (hd x).differentiableAt) fun x => ?_
    rw [(hd x).deriv]; positivity
  have := hmono hw
  simp only [hg, Real.arctan_zero] at this
  have h0 : Pat9 0 = 0 := by simp [Pat9, Pat8]
  linarith

/-- `arctan u = π/4 + arctan ((u-1)/(u+1))` for `u > -1`. -/
theorem arctan_eq_pi_div_four_add {u : ℝ} (hu : -1 < u) :
    Real.arctan u = π / 4 + Real.arctan ((u - 1) / (u + 1)) := by
  have hu1 : 0 < u + 1 := by linarith
  have hlt : (1 : ℝ) * ((u - 1) / (u + 1)) < 1 := by
    rw [one_mul, div_lt_one hu1]; linarith
  rw [← Real.arctan_one, Real.arctan_add hlt]
  congr 1
  field_simp
  ring

/-- `R1` (direct): `arctan u ≤ U` from `Pat9 u ≤ U`, `u ≥ 0`. -/
theorem arctan_le_R1 {u U : ℝ} (hu : 0 ≤ u) (hU : Pat9 u ≤ U) : Real.arctan u ≤ U :=
  le_trans (arctan_le_Pat9 hu) hU

theorem arctan_ge_R1 {u L : ℝ} (hu : 0 ≤ u) (hL : L ≤ Pat8 u) : L ≤ Real.arctan u :=
  le_trans hL (Pat8_le_arctan hu)

/-- `R2` (`0 ≤ u ≤ 1`, `w = (1-u)/(1+u)`): `arctan u = π/4 - arctan w`. -/
theorem arctan_eq_R2 {u w : ℝ} (hu : 0 ≤ u) (hw : (1 - u) / (1 + u) = w) :
    Real.arctan u = π / 4 - Real.arctan w := by
  have h1 := arctan_eq_pi_div_four_add (u := u) (by linarith)
  have h2 : (u - 1) / (u + 1) = -w := by
    rw [← hw]
    have : (0 : ℝ) < 1 + u := by linarith
    have : (0 : ℝ) < u + 1 := by linarith
    field_simp
    ring
  rw [h1, h2, Real.arctan_neg]
  ring

theorem arctan_le_R2 {u w L : ℝ} (hu : 0 ≤ u) (hw : (1 - u) / (1 + u) = w) (hw0 : 0 ≤ w)
    (hL : L ≤ Pat8 w) : Real.arctan u ≤ π / 4 - L := by
  rw [arctan_eq_R2 hu hw]; linarith [Pat8_le_arctan hw0]

theorem arctan_ge_R2 {u w U : ℝ} (hu : 0 ≤ u) (hw : (1 - u) / (1 + u) = w) (hw0 : 0 ≤ w)
    (hU : Pat9 w ≤ U) : π / 4 - U ≤ Real.arctan u := by
  rw [arctan_eq_R2 hu hw]; linarith [arctan_le_Pat9 hw0]

/-- `R3` (`u ≥ 1`, `w = (u-1)/(u+1)`): `arctan u = π/4 + arctan w`. -/
theorem arctan_le_R3 {u w U : ℝ} (hu : 0 ≤ u) (hw : (u - 1) / (u + 1) = w) (hw0 : 0 ≤ w)
    (hU : Pat9 w ≤ U) : Real.arctan u ≤ π / 4 + U := by
  rw [arctan_eq_pi_div_four_add (by linarith), hw]; linarith [arctan_le_Pat9 hw0]

theorem arctan_ge_R3 {u w L : ℝ} (hu : 0 ≤ u) (hw : (u - 1) / (u + 1) = w) (hw0 : 0 ≤ w)
    (hL : L ≤ Pat8 w) : π / 4 + L ≤ Real.arctan u := by
  rw [arctan_eq_pi_div_four_add (by linarith), hw]; linarith [Pat8_le_arctan hw0]

/-- `R4` (`u > 0`, `w = 1/u`): `arctan u = π/2 - arctan w`. -/
theorem arctan_eq_R4 {u w : ℝ} (hu : 0 < u) (hw : 1 / u = w) :
    Real.arctan u = π / 2 - Real.arctan w := by
  have hw0 : 0 < w := by rw [← hw]; positivity
  have : u = w⁻¹ := by rw [← hw, one_div, inv_inv]
  rw [this, Real.arctan_inv_of_pos hw0]

theorem arctan_le_R4 {u w L : ℝ} (hu : 0 < u) (hw : 1 / u = w) (hL : L ≤ Pat8 w) :
    Real.arctan u ≤ π / 2 - L := by
  have hw0 : 0 < w := by rw [← hw]; positivity
  rw [arctan_eq_R4 hu hw]; linarith [Pat8_le_arctan hw0.le]

theorem arctan_ge_R4 {u w U : ℝ} (hu : 0 < u) (hw : 1 / u = w) (hU : Pat9 w ≤ U) :
    π / 2 - U ≤ Real.arctan u := by
  have hw0 : 0 < w := by rw [← hw]; positivity
  rw [arctan_eq_R4 hu hw]; linarith [arctan_le_Pat9 hw0.le]

/-! ## `x log x` -/

/-- `x ↦ x log x` (with `Real.log x = log |x|`). -/
def xlx (u : ℝ) : ℝ := u * Real.log u

theorem xlx_neg (u : ℝ) : xlx (-u) = -xlx u := by
  unfold xlx; rw [Real.log_neg_eq_log]; ring

theorem exp_neg_one_lt_two_fifths : Real.exp (-1) < 2 / 5 := by
  have := Real.exp_neg_one_lt_d9; norm_num at this ⊢; linarith

theorem one_third_lt_exp_neg_one : (1 / 3 : ℝ) < Real.exp (-1) := by
  have := Real.exp_neg_one_gt_d9; norm_num at this ⊢; linarith

/-- `x log x` is increasing on `[2/5, ∞)`. -/
theorem xlx_mono {u v : ℝ} (hu : 2 / 5 ≤ u) (huv : u ≤ v) : xlx u ≤ xlx v :=
  Real.mul_log_strictMonoOn.monotoneOn (Set.mem_Ici.2 (by linarith [exp_neg_one_lt_two_fifths]))
    (Set.mem_Ici.2 (by linarith [exp_neg_one_lt_two_fifths])) huv

/-- `x log x` is decreasing on `[0, 1/3]`. -/
theorem xlx_anti_pos {u v : ℝ} (hu : 0 ≤ u) (huv : u ≤ v) (hv : v ≤ 1 / 3) : xlx v ≤ xlx u :=
  Real.mul_log_strictAntiOn.antitoneOn
    ⟨hu, by linarith [one_third_lt_exp_neg_one]⟩
    ⟨by linarith, by linarith [one_third_lt_exp_neg_one]⟩ huv

/-- `x log x` is decreasing on `[-1/3, 0]`. -/
theorem xlx_anti_neg {u v : ℝ} (hu : -(1 / 3) ≤ u) (huv : u ≤ v) (hv : v ≤ 0) : xlx v ≤ xlx u := by
  have h := xlx_anti_pos (u := -v) (v := -u) (by linarith) (by linarith) (by linarith)
  have e1 : u = -(-u) := by ring
  have e2 : v = -(-v) := by ring
  rw [e1, e2, xlx_neg (-u), xlx_neg (-v)]
  linarith

end ZetaWindow.L20U
