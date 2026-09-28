import Zeta2Lean.Window.Proofs.L20U.Contour
import Zeta2Lean.Window.Proofs.L20U.Gf

set_option linter.style.header false
set_option linter.style.longLine false

/-!
# Theorem U, part 4: the pointwise bound on the contour (Lemmas 2 and 4 of crude-upper-bound.md)

On the line `t = M_n + iy`, `M_n = 1/2 - n`, `y > 0`, `n ≥ 2`:

  `‖Pw n t‖ · ‖K₅ t‖ ≤ A (163 n + y)^34 exp(n U(y/n))`       (`norm_PK_le`)

with the landscape function (`x₀ = 159`)

  `U(η) = C_η - 336 + 5[Gf(159,η) - Gf(-1,η)] - ∑_{j=1}^{23} [Gf(159-η_j,η) - Gf(η_j-1,η)] - 2πη`,
  `C_η = ∑_{j=6}^{23} (160-2η_j) log(160-2η_j) - 2 ∑_{j=1}^{5} η_j log η_j`.

Ingredients:
* `Pw = Rw` (product form, `Contour.lean`), `‖t + i‖ = exp(log((M_n+i)² + y²)/2)`;
* the window comparison (`Gf.lean`): numerator `≤ Gf(159n + 5/2) - Gf(1/2 - n) + 1 + log 2`,
  denominators `≥ Gf((159-η_j)n + 3/2) - Gf((η_j-1)n + 1/2)`, and the shifts to the scaled points
  `159n, -n, (159-η_j)n, (η_j-1)n` (cost `O(log(163n+y))`; this replaces the `x`-Lipschitz bound
  `B` of the informal proof, i.e. the line is compared with `x₀ = 159` directly);
* Stirling for `N_h` (`Stirling.stirlingSeq` antitone, `Real.pow_div_factorial_le_exp`):
  `log N_h ≤ n C_η + 336 (n log n - n) + 9 log(64n) + 18`;
* scaling `Gf(na, nη) = n Gf(a, η) + n a log n`: the `n log n` terms cancel (`336 + 5·160 - 1136 = 0`);
* the kernel: `‖K₅(M_n + iy)‖ ≤ κ e^{-2πy}` (`Kw_bound`: `kerS_decay` for `y ≥ 1`, the bound on
  lines through integers for `y < 1`); any constant is fine for the eventual statement.
-/

open Complex MeasureTheory Filter Topology Set Finset
open scoped Real

noncomputable section

namespace ZetaWindow

namespace L20U

/-! ## The landscape function -/

/-- `C_η = ∑_{j=6}^{23} (160-2η_j) log(160-2η_j) - 2 ∑_{j=1}^{5} η_j log η_j` (`= 1275.776…`). -/
def Ceta : ℝ :=
  ∑ j ∈ Icc 6 23, ((160 - 2 * etaW j : ℕ) : ℝ) * Real.log ((160 - 2 * etaW j : ℕ) : ℝ) -
    2 * ∑ j ∈ Icc 1 5, (etaW j : ℝ) * Real.log (etaW j : ℝ)

/-- The landscape `U(159, η)`. -/
def Uw (η : ℝ) : ℝ :=
  Ceta - 336 + 5 * (Gf 159 η - Gf (-1) η) -
    ∑ j ∈ Icc 1 23, (Gf (159 - (etaW j : ℝ)) η - Gf ((etaW j : ℝ) - 1) η) - 2 * π * η

/-! ## The directions -/

theorem etaW_ge (j : ℕ) : 47 ≤ etaW j := by unfold etaW; split_ifs <;> omega

theorem etaW_le {j : ℕ} (hj : j ≤ 23) : etaW j ≤ 66 := by unfold etaW; split_ifs <;> omega

theorem etaW_ge6 {j : ℕ} (hj : 6 ≤ j) : 50 ≤ etaW j := by unfold etaW; split_ifs <;> omega

theorem sum_a : ∑ j ∈ Icc 6 23, ((160 - 2 * etaW j : ℕ) : ℝ) = 808 := by
  have : (∑ j ∈ Icc 6 23, (160 - 2 * etaW j)) = 808 := by decide
  exact_mod_cast this

theorem sum_eta5 : ∑ j ∈ Icc 1 5, (etaW j : ℝ) = 236 := by
  have : (∑ j ∈ Icc 1 5, etaW j) = 236 := by decide
  exact_mod_cast this

theorem sum_eta23 : ∑ j ∈ Icc 1 23, (etaW j : ℝ) = 1272 := by
  have : (∑ j ∈ Icc 1 23, etaW j) = 1272 := by decide
  exact_mod_cast this

/-! ## Stirling bounds for `N_h` -/

theorem factorial_le_stirling {m : ℕ} (hm : 1 ≤ m) :
    (m.factorial : ℝ) ≤ Real.exp 1 * Real.sqrt m * ((m : ℝ) / Real.exp 1) ^ m := by
  have h1 : Stirling.stirlingSeq m ≤ Stirling.stirlingSeq 1 := by
    obtain ⟨k, rfl⟩ : ∃ k, m = k + 1 := ⟨m - 1, by omega⟩
    exact Stirling.stirlingSeq'_antitone (Nat.zero_le k)
  rw [Stirling.stirlingSeq_one] at h1
  unfold Stirling.stirlingSeq at h1
  have hm0 : (0 : ℝ) < m := by exact_mod_cast hm
  have hpos : 0 < Real.sqrt (2 * (m : ℝ)) * ((m : ℝ) / Real.exp 1) ^ m := by positivity
  rw [div_le_div_iff₀ hpos (by positivity)] at h1
  have hs : Real.sqrt (2 * (m : ℝ)) = Real.sqrt 2 * Real.sqrt m := Real.sqrt_mul (by norm_num) _
  rw [hs] at h1
  have hs2 : 0 < Real.sqrt 2 := by positivity
  have h2 : (m.factorial : ℝ) * Real.sqrt 2 ≤
      (Real.exp 1 * Real.sqrt m * ((m : ℝ) / Real.exp 1) ^ m) * Real.sqrt 2 := by
    calc (m.factorial : ℝ) * Real.sqrt 2
        ≤ Real.exp 1 * (Real.sqrt 2 * Real.sqrt m * ((m : ℝ) / Real.exp 1) ^ m) := h1
      _ = _ := by ring
  exact le_of_mul_le_mul_right h2 hs2

theorem log_factorial_le {m : ℕ} (hm : 1 ≤ m) :
    Real.log (m.factorial : ℝ) ≤ m * Real.log m - m + Real.log m / 2 + 1 := by
  have hm0 : (0 : ℝ) < m := by exact_mod_cast hm
  have h := Real.log_le_log (by positivity) (factorial_le_stirling hm)
  rw [Real.log_mul (by positivity) (by positivity), Real.log_mul (by positivity) (by positivity),
    Real.log_exp, Real.log_sqrt hm0.le, Real.log_pow, Real.log_div hm0.ne' (by positivity),
    Real.log_exp] at h
  linarith

theorem log_factorial_ge (m : ℕ) : m * Real.log m - m ≤ Real.log (m.factorial : ℝ) := by
  rcases Nat.eq_zero_or_pos m with rfl | hm
  · simp
  have hm0 : (0 : ℝ) < m := by exact_mod_cast hm
  have h := Real.pow_div_factorial_le_exp (m : ℝ) hm0.le m
  have hf : (0 : ℝ) < m.factorial := by positivity
  rw [div_le_iff₀ hf] at h
  have h2 := Real.log_le_log (by positivity) h
  rw [Real.log_pow, Real.log_mul (Real.exp_pos _).ne' hf.ne', Real.log_exp] at h2
  linarith

theorem Nh_eq (n : ℕ) : (Nh cfgW n : ℝ) =
    (∏ j ∈ Icc 6 23, ((cfgW.h0 n - 2 * cfgW.h n j).factorial : ℝ)) /
      ∏ j ∈ Icc 1 5, ((cfgW.h n j - 1).factorial : ℝ) ^ 2 := by
  unfold Nh
  push_cast
  rfl

theorem log_fact_den_le {n : ℕ} (hn : 1 ≤ n) {j : ℕ} (hj : j ∈ Finset.Icc 6 23) :
    Real.log ((cfgW.h0 n - 2 * cfgW.h n j).factorial : ℝ) ≤
      n * (((160 - 2 * etaW j : ℕ) : ℝ) * Real.log ((160 - 2 * etaW j : ℕ) : ℝ)) +
        ((160 - 2 * etaW j : ℕ) : ℝ) * (n * Real.log n - n) + Real.log (64 * n) / 2 + 1 := by
  obtain ⟨hj1, hj2⟩ := Finset.mem_Icc.1 hj
  have he1 := etaW_ge6 hj1
  have he2 := etaW_le hj2
  have ha1 : 28 ≤ 160 - 2 * etaW j := by omega
  have ha2 : 160 - 2 * etaW j ≤ 64 := by omega
  have hm_eq : ((cfgW.h0 n - 2 * cfgW.h n j : ℕ) : ℝ) = ((160 - 2 * etaW j : ℕ) : ℝ) * n := by
    have h1 : 2 * cfgW.h n j ≤ cfgW.h0 n := by
      simp only [Config.h, Config.h0, cfgW]
      nlinarith [Nat.mul_le_mul_right n he2]
    rw [Nat.cast_sub h1, Nat.cast_sub (by omega : 2 * etaW j ≤ 160)]
    simp only [Config.h, Config.h0, cfgW]
    push_cast
    ring
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  have ha0 : (0 : ℝ) < ((160 - 2 * etaW j : ℕ) : ℝ) := by exact_mod_cast (by omega : 0 < 160 - 2 * etaW j)
  have ha28 : (28 : ℝ) ≤ ((160 - 2 * etaW j : ℕ) : ℝ) := by exact_mod_cast ha1
  have ha64 : ((160 - 2 * etaW j : ℕ) : ℝ) ≤ 64 := by exact_mod_cast ha2
  have hm1 : 1 ≤ cfgW.h0 n - 2 * cfgW.h n j := by
    have hn1r : (1 : ℝ) ≤ n := by exact_mod_cast hn
    have : (1 : ℝ) ≤ ((cfgW.h0 n - 2 * cfgW.h n j : ℕ) : ℝ) := by
      rw [hm_eq]; nlinarith
    exact_mod_cast this
  have h := log_factorial_le hm1
  rw [hm_eq, Real.log_mul ha0.ne' hn0.ne'] at h
  have hlog : Real.log ((160 - 2 * etaW j : ℕ) : ℝ) + Real.log n ≤ Real.log (64 * n) := by
    rw [← Real.log_mul ha0.ne' hn0.ne']
    exact Real.log_le_log (by positivity) (by nlinarith)
  have e : ((160 - 2 * etaW j : ℕ) : ℝ) * n *
      (Real.log ((160 - 2 * etaW j : ℕ) : ℝ) + Real.log n) - ((160 - 2 * etaW j : ℕ) : ℝ) * n =
      n * (((160 - 2 * etaW j : ℕ) : ℝ) * Real.log ((160 - 2 * etaW j : ℕ) : ℝ)) +
        ((160 - 2 * etaW j : ℕ) : ℝ) * (n * Real.log n - n) := by ring
  linarith

theorem log_fact_num_ge {n : ℕ} (hn : 1 ≤ n) (j : ℕ) :
    n * ((etaW j : ℝ) * Real.log (etaW j : ℝ)) + (etaW j : ℝ) * (n * Real.log n - n) ≤
      Real.log ((cfgW.h n j - 1).factorial : ℝ) := by
  have hm : cfgW.h n j - 1 = etaW j * n := by simp [Config.h, cfgW]
  rw [hm]
  have h := log_factorial_ge (etaW j * n)
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  have he0 : (0 : ℝ) < etaW j := by exact_mod_cast (by have := etaW_ge j; omega : 0 < etaW j)
  push_cast at h
  rw [Real.log_mul he0.ne' hn0.ne'] at h
  have e : (etaW j : ℝ) * n * (Real.log (etaW j) + Real.log n) - (etaW j : ℝ) * n =
      n * ((etaW j : ℝ) * Real.log (etaW j : ℝ)) + (etaW j : ℝ) * (n * Real.log n - n) := by ring
  linarith

/-- `log N_h ≤ n C_η + 336 (n log n - n) + 9 log(64 n) + 18`. -/
theorem log_Nh_le {n : ℕ} (hn : 1 ≤ n) :
    Real.log (Nh cfgW n : ℝ) ≤
      n * Ceta + 336 * (n * Real.log n - n) + 9 * Real.log (64 * n) + 18 := by
  rw [Nh_eq, Real.log_div (by positivity) (by positivity),
    Real.log_prod (fun j _ => by positivity), Real.log_prod (fun j _ => by positivity)]
  simp only [Real.log_pow]
  have h1 : ∑ j ∈ Icc 6 23, Real.log ((cfgW.h0 n - 2 * cfgW.h n j).factorial : ℝ) ≤
      ∑ j ∈ Icc 6 23, (n * (((160 - 2 * etaW j : ℕ) : ℝ) * Real.log ((160 - 2 * etaW j : ℕ) : ℝ)) +
        ((160 - 2 * etaW j : ℕ) : ℝ) * (n * Real.log n - n) + (Real.log (64 * n) / 2 + 1)) :=
    Finset.sum_le_sum fun j hj => by have := log_fact_den_le hn hj; linarith
  have h2 : ∑ j ∈ Icc 1 5, (n * ((etaW j : ℝ) * Real.log (etaW j : ℝ)) +
      (etaW j : ℝ) * (n * Real.log n - n)) ≤
      ∑ j ∈ Icc 1 5, Real.log ((cfgW.h n j - 1).factorial : ℝ) :=
    Finset.sum_le_sum fun j _ => log_fact_num_ge hn j
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.sum_mul, sum_a,
    Finset.sum_const, Nat.card_Icc, nsmul_eq_mul] at h1
  rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.sum_mul, sum_eta5] at h2
  have h3 : ∑ j ∈ Icc 1 5, ((2 : ℕ) : ℝ) * Real.log ((cfgW.h n j - 1).factorial : ℝ) =
      2 * ∑ j ∈ Icc 1 5, Real.log ((cfgW.h n j - 1).factorial : ℝ) := by
    rw [← Finset.mul_sum]; push_cast; ring
  rw [h3]
  unfold Ceta
  push_cast at h1
  nlinarith [h1, h2]

/-! ## The kernel on the line -/

theorem Kw_bound : ∃ κ : ℝ, 0 ≤ κ ∧ ∀ (n : ℕ) (y : ℝ), 0 < y →
    ‖Kw ((Mn n : ℂ) + y * I)‖ ≤ κ * Real.exp (-2 * π * y) := by
  obtain ⟨κ₀, hκ₀, hκ⟩ := kerS_decay (s := 5) (by norm_num)
  have hz : 0 ≤ zabs 5 := tsum_nonneg fun _ => norm_nonneg _
  refine ⟨max κ₀ (zabs 5 * Real.exp (2 * π)), le_trans hκ₀ (le_max_left _ _), fun n y hy => ?_⟩
  by_cases hy1 : 1 ≤ y
  · have him : ((Mn n : ℂ) + y * I + 1 / 2).im = y := by simp
    have h := hκ ((Mn n : ℂ) + y * I + 1 / 2) (by rw [him]; exact hy1)
    rw [him] at h
    calc ‖Kw ((Mn n : ℂ) + y * I)‖ ≤ κ₀ * Real.exp (-2 * π * y) := h
      _ ≤ _ := by gcongr; exact le_max_left _ _
  · push Not at hy1
    have h := norm_Kw_line_le n y
    calc ‖Kw ((Mn n : ℂ) + y * I)‖ ≤ zabs 5 := h
      _ = zabs 5 * Real.exp (2 * π) * Real.exp (-2 * π) := by
          rw [mul_assoc, ← Real.exp_add]; simp
      _ ≤ zabs 5 * Real.exp (2 * π) * Real.exp (-2 * π * y) :=
          mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr (by nlinarith [Real.pi_pos])) (by positivity)
      _ ≤ _ := by gcongr; exact le_max_right _ _

/-! ## Window sums on the line -/

theorem norm_line_add_nat (n : ℕ) {y : ℝ} (hy : 0 < y) (i : ℕ) :
    ‖(Mn n : ℂ) + y * I + (i : ℂ)‖ = Real.exp (Real.log (((Mn n : ℝ) + i) ^ 2 + y ^ 2) / 2) := by
  have hw : ((Mn n : ℂ) + y * I + (i : ℂ)).im ≠ 0 := by simpa using hy.ne'
  rw [norm_eq_exp_log _ hw]
  simp

/-- Numerator: `∑_{i=1}^{h₀-1} log|t+i| ≤ Gf(159n) - Gf(-n) + 1 + log 2 + (5/2) log(163n + y)`. -/
theorem num_le {n : ℕ} (hn : 2 ≤ n) {y : ℝ} (hy : 0 < y) :
    ∑ i ∈ Ico 1 (cfgW.h0 n), Real.log (((Mn n : ℝ) + i) ^ 2 + y ^ 2) / 2 ≤
      Gf (159 * n) y - Gf (-(n : ℝ)) y + (1 + Real.log 2) + 5 / 2 * Real.log (163 * n + y) := by
  have hn1 : 1 ≤ n := by omega
  have hnh : n ≤ cfgW.h0 n := by simp only [Config.h0, cfgW]; omega
  have h := num_window hy n (cfgW.h0 n) hn1 hnh
  have hn0 : (2 : ℝ) ≤ n := by exact_mod_cast hn
  have e1 : (1 / 2 - n : ℝ) + (cfgW.h0 n : ℕ) = 159 * n + 5 / 2 := by
    simp only [Config.h0, cfgW]; push_cast; ring
  rw [e1] at h
  have h2 := Gf_shift_le hy (159 * n) (show (0 : ℝ) ≤ 5 / 2 by norm_num)
  have h3 : Real.log (|159 * (n : ℝ)| + 5 / 2 + y) ≤ Real.log (163 * n + y) := by
    rw [abs_of_nonneg (by positivity)]
    exact Real.log_le_log (by positivity) (by linarith)
  have h4 : Gf (-(n : ℝ)) y ≤ Gf (1 / 2 - n) y := by
    refine Gf_shift_nonneg hy (by linarith) fun u hu => ?_
    rw [abs_of_neg (by linarith [hu.2])]
    linarith [hu.2]
  have e2 : ∑ i ∈ Ico 1 (cfgW.h0 n), Real.log (((Mn n : ℝ) + i) ^ 2 + y ^ 2) / 2 =
      ∑ i ∈ Ico 1 (cfgW.h0 n), Real.log (((1 / 2 - n : ℝ) + i) ^ 2 + y ^ 2) / 2 := rfl
  rw [e2]
  nlinarith

/-- Denominator `j`: `∑_{i=h_j}^{h₀-h_j} log|t+i| ≥ Gf((159-η_j)n) - Gf((η_j-1)n) - log(163n+y)/2`. -/
theorem den_ge {n : ℕ} (hn : 1 ≤ n) {y : ℝ} (hy : 0 < y) {j : ℕ} (hj : j ∈ Finset.Icc 1 23) :
    Gf ((159 - (etaW j : ℝ)) * n) y - Gf (((etaW j : ℝ) - 1) * n) y - Real.log (163 * n + y) / 2 ≤
      ∑ i ∈ Icc (cfgW.h n j) (cfgW.h0 n - cfgW.h n j), Real.log (((Mn n : ℝ) + i) ^ 2 + y ^ 2) / 2 := by
  obtain ⟨hj1, hj2⟩ := Finset.mem_Icc.1 hj
  have he1 := etaW_ge j
  have he2 := etaW_le hj2
  have hn0 : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have he1r : (47 : ℝ) ≤ etaW j := by exact_mod_cast he1
  have he2r : (etaW j : ℝ) ≤ 66 := by exact_mod_cast he2
  have hle : cfgW.h n j ≤ cfgW.h0 n := by
    simp only [Config.h, Config.h0, cfgW]
    nlinarith [Nat.mul_le_mul_right n he2]
  have hab : cfgW.h n j ≤ cfgW.h0 n - cfgW.h n j + 1 := by
    have : 2 * cfgW.h n j ≤ cfgW.h0 n := by
      simp only [Config.h, Config.h0, cfgW]
      nlinarith [Nat.mul_le_mul_right n he2]
    omega
  have ehj : ((cfgW.h n j : ℕ) : ℝ) = (etaW j : ℝ) * n + 1 := by
    simp only [Config.h, cfgW]; push_cast; ring
  have eh0 : ((cfgW.h0 n : ℕ) : ℝ) = 160 * n + 2 := by
    simp only [Config.h0, cfgW]; push_cast; ring
  have hMa : 1 ≤ (Mn n : ℝ) + (cfgW.h n j : ℕ) := by
    rw [ehj]; unfold Mn; nlinarith
  have h := den_window hy (Mn n) (cfgW.h n j) (cfgW.h0 n - cfgW.h n j) hab hMa
  have e1 : (Mn n : ℝ) + ((cfgW.h0 n - cfgW.h n j : ℕ) : ℝ) = (159 - (etaW j : ℝ)) * n + 3 / 2 := by
    rw [Nat.cast_sub hle, ehj, eh0]; unfold Mn; ring
  have e2 : (Mn n : ℝ) + ((cfgW.h n j : ℕ) : ℝ) - 1 = ((etaW j : ℝ) - 1) * n + 1 / 2 := by
    rw [ehj]; unfold Mn; ring
  rw [e1, e2] at h
  have h3 : Gf ((159 - (etaW j : ℝ)) * n) y ≤ Gf ((159 - (etaW j : ℝ)) * n + 3 / 2) y := by
    refine Gf_shift_nonneg hy (by linarith) fun u hu => ?_
    have : (93 : ℝ) ≤ (159 - (etaW j : ℝ)) * n := by nlinarith
    rw [abs_of_pos (by linarith [hu.1])]
    linarith [hu.1]
  have h4 := Gf_shift_le hy (((etaW j : ℝ) - 1) * n) (show (0 : ℝ) ≤ 1 / 2 by norm_num)
  have h5 : Real.log (|((etaW j : ℝ) - 1) * n| + 1 / 2 + y) ≤ Real.log (163 * n + y) := by
    have hpos : 0 ≤ ((etaW j : ℝ) - 1) * n := by nlinarith
    rw [abs_of_nonneg hpos]
    exact Real.log_le_log (by positivity) (by nlinarith)
  nlinarith

/-! ## Scaling -/

theorem Gf_scale_nat {n : ℕ} (hn : 1 ≤ n) (a : ℝ) {y : ℝ} (hy : 0 < y) :
    Gf (a * n) y = n * Gf a (y / n) + a * (n * Real.log n) := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  have h := Gf_scale hn0 a (y := y / n) (by positivity)
  rw [mul_div_cancel₀ _ hn0.ne'] at h
  rw [mul_comm a, h]
  ring

theorem den_sum_scale {n : ℕ} (hn : 1 ≤ n) {y : ℝ} (hy : 0 < y) :
    ∑ j ∈ Icc 1 23, (Gf ((159 - (etaW j : ℝ)) * n) y - Gf (((etaW j : ℝ) - 1) * n) y) =
      n * ∑ j ∈ Icc 1 23, (Gf (159 - (etaW j : ℝ)) (y / n) - Gf ((etaW j : ℝ) - 1) (y / n)) +
        1136 * (n * Real.log n) := by
  have hj : ∀ j ∈ Finset.Icc 1 23, Gf ((159 - (etaW j : ℝ)) * n) y - Gf (((etaW j : ℝ) - 1) * n) y =
      n * (Gf (159 - (etaW j : ℝ)) (y / n) - Gf ((etaW j : ℝ) - 1) (y / n)) +
        (160 - 2 * (etaW j : ℝ)) * (n * Real.log n) := by
    intro j _
    rw [Gf_scale_nat hn _ hy, Gf_scale_nat hn _ hy]
    ring
  have h1136 : ∑ i ∈ Finset.Icc 1 23, (160 - 2 * (etaW i : ℝ)) = 1136 := by
    rw [Finset.sum_sub_distrib, ← Finset.mul_sum, sum_eta23]
    simp only [Finset.sum_const, Nat.card_Icc, nsmul_eq_mul]
    norm_num
  rw [Finset.sum_congr rfl hj, Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.sum_mul, h1136]

/-! ## The pointwise bound -/

theorem Nh_pos (n : ℕ) : (0 : ℝ) < Nh cfgW n := by
  rw [Nh_eq]
  positivity

/-- **Lemma 4**: `‖R̃(M_n + iy)‖ ≤ 64 e^{23} (163n + y)^{34} exp(n (U(y/n) + 2π y/n))`. -/
theorem norm_Rw_le {n : ℕ} (hn : 2 ≤ n) {y : ℝ} (hy : 0 < y) :
    ‖Rw n ((Mn n : ℂ) + y * I)‖ ≤
      64 * Real.exp 23 * (163 * n + y) ^ 34 * Real.exp (n * (Uw (y / n) + 2 * π * (y / n))) := by
  have hn1 : 1 ≤ n := by omega
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn1
  set t : ℂ := (Mn n : ℂ) + y * I with ht
  set L : ℝ := Real.log (163 * n + y) with hL
  have hpos : (0 : ℝ) < 163 * n + y := by positivity
  have hL64 : Real.log (64 * n) ≤ L := Real.log_le_log (by positivity) (by linarith)
  -- the norm of the product form
  have hNh : ‖(Nh cfgW n : ℂ)‖ = (Nh cfgW n : ℝ) := by
    rw [show (Nh cfgW n : ℂ) = ((Nh cfgW n : ℝ) : ℂ) by push_cast; rfl, Complex.norm_real,
      Real.norm_eq_abs, abs_of_pos (Nh_pos n)]
  have hnum : ‖∏ i ∈ Ico 1 (cfgW.h0 n), (t + i)‖ =
      Real.exp (∑ i ∈ Ico 1 (cfgW.h0 n), Real.log (((Mn n : ℝ) + i) ^ 2 + y ^ 2) / 2) := by
    rw [norm_prod, Real.exp_sum]
    exact Finset.prod_congr rfl fun i _ => norm_line_add_nat n hy i
  have hden : ‖∏ j ∈ Icc 1 cfgW.q, ∏ i ∈ Icc (cfgW.h n j) (cfgW.h0 n - cfgW.h n j), (t + i)‖ =
      Real.exp (∑ j ∈ Icc 1 cfgW.q, ∑ i ∈ Icc (cfgW.h n j) (cfgW.h0 n - cfgW.h n j),
        Real.log (((Mn n : ℝ) + i) ^ 2 + y ^ 2) / 2) := by
    rw [norm_prod, Real.exp_sum]
    refine Finset.prod_congr rfl fun j _ => ?_
    rw [norm_prod, Real.exp_sum]
    exact Finset.prod_congr rfl fun i _ => norm_line_add_nat n hy i
  have hlin : ‖(cfgW.h0 n : ℂ) + 2 * t‖ ≤ 2 * (163 * n + y) := by
    have e : (cfgW.h0 n : ℂ) + 2 * t = (((158 * n + 3 : ℝ)) : ℂ) + ((2 * y : ℝ) : ℂ) * I := by
      rw [ht]; unfold Mn; simp only [Config.h0, cfgW]; push_cast; ring
    rw [e]
    refine le_trans (norm_add_le _ _) ?_
    rw [norm_mul, Complex.norm_real, Complex.norm_real, Complex.norm_I, Real.norm_eq_abs,
      Real.norm_eq_abs, abs_of_pos (by positivity), abs_of_pos (by positivity)]
    have hn1r : (1 : ℝ) ≤ n := by exact_mod_cast hn1
    linarith
  have hRw : ‖Rw n t‖ = (Nh cfgW n : ℝ) * ‖(cfgW.h0 n : ℂ) + 2 * t‖ *
      Real.exp (5 * ∑ i ∈ Ico 1 (cfgW.h0 n), Real.log (((Mn n : ℝ) + i) ^ 2 + y ^ 2) / 2 -
        ∑ j ∈ Icc 1 cfgW.q, ∑ i ∈ Icc (cfgW.h n j) (cfgW.h0 n - cfgW.h n j),
          Real.log (((Mn n : ℝ) + i) ^ 2 + y ^ 2) / 2) := by
    unfold Rw
    rw [norm_div, norm_mul, norm_mul, norm_pow, hNh, hnum, hden, Real.exp_sub,
      ← Real.exp_nat_mul]
    simp only [show cfgW.r = 5 from rfl]
    push_cast
    ring
  -- bounds on the exponent
  have hS := num_le hn hy
  have hD : ∑ j ∈ Icc 1 23, (Gf ((159 - (etaW j : ℝ)) * n) y - Gf (((etaW j : ℝ) - 1) * n) y -
      L / 2) ≤ ∑ j ∈ Icc 1 cfgW.q, ∑ i ∈ Icc (cfgW.h n j) (cfgW.h0 n - cfgW.h n j),
        Real.log (((Mn n : ℝ) + i) ^ 2 + y ^ 2) / 2 :=
    Finset.sum_le_sum fun j hj => den_ge hn1 hy hj
  rw [Finset.sum_sub_distrib, den_sum_scale hn1 hy] at hD
  simp only [Finset.sum_const, Nat.card_Icc, nsmul_eq_mul] at hD
  have h159 : Gf (159 * n) y = n * Gf 159 (y / n) + 159 * (n * Real.log n) := by
    rw [show (159 : ℝ) * n = 159 * (n : ℝ) from rfl, Gf_scale_nat hn1 159 hy]
  have hm1 : Gf (-(n : ℝ)) y = n * Gf (-1) (y / n) + (-1) * (n * Real.log n) := by
    rw [show -(n : ℝ) = (-1) * n by ring, Gf_scale_nat hn1 (-1) hy]
  have hNb := log_Nh_le hn1
  have hNh' : (Nh cfgW n : ℝ) = Real.exp (Real.log (Nh cfgW n : ℝ)) :=
    (Real.exp_log (Nh_pos n)).symm
  have hlin' : ‖(cfgW.h0 n : ℂ) + 2 * t‖ ≤ Real.exp (Real.log 2 + L) := by
    rw [Real.exp_add, Real.exp_log (by norm_num), hL, Real.exp_log hpos]
    exact hlin
  have hpow : (163 * (n : ℝ) + y) ^ 34 = Real.exp (34 * L) := by
    rw [hL, show (34 : ℝ) * Real.log (163 * n + y) = ((34 : ℕ) : ℝ) * Real.log (163 * n + y) by
      norm_num, ← Real.log_pow, Real.exp_log (by positivity)]
  have h64 : (64 : ℝ) = Real.exp (6 * Real.log 2) := by
    rw [show (6 : ℝ) * Real.log 2 = ((6 : ℕ) : ℝ) * Real.log 2 by norm_num, ← Real.log_pow,
      Real.exp_log (by norm_num)]
    norm_num
  rw [hRw, hpow, h64, hNh']
  calc Real.exp (Real.log (Nh cfgW n : ℝ)) * ‖(cfgW.h0 n : ℂ) + 2 * t‖ *
        Real.exp (5 * ∑ i ∈ Ico 1 (cfgW.h0 n), Real.log (((Mn n : ℝ) + i) ^ 2 + y ^ 2) / 2 -
          ∑ j ∈ Icc 1 cfgW.q, ∑ i ∈ Icc (cfgW.h n j) (cfgW.h0 n - cfgW.h n j),
            Real.log (((Mn n : ℝ) + i) ^ 2 + y ^ 2) / 2)
      ≤ Real.exp (Real.log (Nh cfgW n : ℝ)) * Real.exp (Real.log 2 + L) *
        Real.exp (5 * ∑ i ∈ Ico 1 (cfgW.h0 n), Real.log (((Mn n : ℝ) + i) ^ 2 + y ^ 2) / 2 -
          ∑ j ∈ Icc 1 cfgW.q, ∑ i ∈ Icc (cfgW.h n j) (cfgW.h0 n - cfgW.h n j),
            Real.log (((Mn n : ℝ) + i) ^ 2 + y ^ 2) / 2) := by gcongr
    _ = Real.exp (Real.log (Nh cfgW n : ℝ) + (Real.log 2 + L) +
          (5 * ∑ i ∈ Ico 1 (cfgW.h0 n), Real.log (((Mn n : ℝ) + i) ^ 2 + y ^ 2) / 2 -
            ∑ j ∈ Icc 1 cfgW.q, ∑ i ∈ Icc (cfgW.h n j) (cfgW.h0 n - cfgW.h n j),
              Real.log (((Mn n : ℝ) + i) ^ 2 + y ^ 2) / 2)) := by
        rw [← Real.exp_add, ← Real.exp_add]
    _ ≤ Real.exp (6 * Real.log 2) * Real.exp 23 * Real.exp (34 * L) *
          Real.exp (n * (Uw (y / n) + 2 * π * (y / n))) := by
        rw [← Real.exp_add, ← Real.exp_add, ← Real.exp_add]
        apply Real.exp_le_exp.mpr
        unfold Uw
        have hq : cfgW.q = 23 := rfl
        rw [hq] at hD ⊢
        rw [show ((23 + 1 - 1 : ℕ) : ℝ) = 23 by norm_num] at hD
        linarith [hS, hD, hNb, hL64, h159, hm1]

/-- **Pointwise bound on the contour** (Lemmas 2 + 4). -/
theorem norm_PK_le (hPF : Stmt_PF) : ∃ A : ℝ, 0 ≤ A ∧ ∀ n : ℕ, 2 ≤ n → ∀ y : ℝ, 0 < y →
    ‖Pw n ((Mn n : ℂ) + y * I) * Kw ((Mn n : ℂ) + y * I)‖ ≤
      A * (163 * n + y) ^ 34 * Real.exp (n * Uw (y / n)) := by
  obtain ⟨κ, hκ0, hκ⟩ := Kw_bound
  refine ⟨64 * Real.exp 23 * κ, by positivity, fun n hn y hy => ?_⟩
  have hn1 : 1 ≤ n := by omega
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn1
  have hre : -(cfgW.h n 1 : ℝ) < ((Mn n : ℂ) + y * I).re := by
    rw [vline_re]; exact Mn_gt n
  rw [norm_mul, Pw_eq_Rw hPF hn1 hre]
  have h1 := norm_Rw_le hn hy
  have h2 := hκ n y hy
  have e : Real.exp (n * (Uw (y / n) + 2 * π * (y / n))) * Real.exp (-2 * π * y) =
      Real.exp (n * Uw (y / n)) := by
    rw [← Real.exp_add]
    congr 1
    field_simp
    ring
  calc ‖Rw n ((Mn n : ℂ) + y * I)‖ * ‖Kw ((Mn n : ℂ) + y * I)‖
      ≤ (64 * Real.exp 23 * (163 * n + y) ^ 34 * Real.exp (n * (Uw (y / n) + 2 * π * (y / n)))) *
          (κ * Real.exp (-2 * π * y)) := by
        gcongr
    _ = 64 * Real.exp 23 * κ * (163 * n + y) ^ 34 *
          (Real.exp (n * (Uw (y / n) + 2 * π * (y / n))) * Real.exp (-2 * π * y)) := by ring
    _ = _ := by rw [e]

end L20U

end ZetaWindow

end
