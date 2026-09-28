import Zeta2Lean.Window.Statements

set_option linter.style.header false
set_option linter.style.longLine false

/-!
# Support of the Laurent coefficients

**Theorem.** `Stmt_LaurentSupp` (no hypotheses): for admissible `c`, `n ≥ 1`, `r+1 ≤ j ≤ q`, and
`k < h_j` or `k > h₀ - h_j`: `B c n j k = 0`.

**Proof.**  Let `i ∈ [j, q]`.  Then `h_i ≥ h_j` (`Admissible.eta_mono`), so `k` is outside
`[h_i, h₀ - h_i]`: if `k < h_j` then `k < h_i`, and if `h₀ - h_j < k` then `h₀ - h_i ≤ h₀ - h_j < k`
(truncated subtraction is antitone in its second argument, so no admissibility bound is needed
here).  Hence `ratBrick h_i (h₀-h_i+1) k` is in its `else` branch, i.e. a multiple of `X`
(`X_dvd_ratBrick_of_not`).  These are `#[j, q] = q - j + 1` factors of the product
`∏_{i ∈ [r+1, q]} ratBrick …`, which is a factor of `Gk c n k`, so `X^{q-j+1} ∣ Gk c n k`
(`X_pow_dvd_Gk`) and `B c n j k = [ε^{q-j}] Gk c n k = 0` (`PowerSeries.X_pow_dvd_iff`).
(Analytically: the pole of `R̃` at `-k` has order `#{i > r : h_i ≤ k ≤ h₀-h_i} < j - r`.)

Only `Admissible.eta_mono` is used (for the indices `1 ≤ r + 1 ≤ j ≤ i ≤ q`); `1 ≤ n` is not needed.

**Numerical check.** `python/window_mirror.py`, section "Laurent data …": all `j`, all `k` below `h_j`
and above `h₀ - h_j` (up to `h₀ + 2`), exact.

**Status: done** (complete, kernel-checked; axioms `propext`, `Classical.choice`, `Quot.sound`).
-/

open Filter Topology Finset PowerSeries

noncomputable section

namespace ZetaWindow

namespace LaurentSupport

/-- In its `else` branch (`¬ (a ≤ k ∧ k < b)`), the rational brick `ratBrick a b k` is a multiple of
`X`: it is `C (b-a-1)! * X * (∏ …)⁻¹`. -/
theorem X_dvd_ratBrick_of_not {a b k : ℕ} (h : ¬ (a ≤ k ∧ k < b)) :
    (X : PowerSeries ℚ) ∣ ratBrick a b k := by
  unfold ratBrick
  rw [ite_eq_right h]
  exact Dvd.dvd.mul_right (dvd_mul_left X _) _

/-- `h` is monotone in the index on `[1, q]` (from `Admissible.eta_mono`). -/
theorem h_mono {c : Config} (hc : Admissible c) (n : ℕ) {i j : ℕ} (h1 : 1 ≤ i) (hij : i ≤ j)
    (hj : j ≤ c.q) : c.h n i ≤ c.h n j := by
  unfold Config.h
  exact Nat.add_le_add_right (Nat.mul_le_mul (hc.eta_mono i j h1 hij hj) (le_refl n)) 1

/-- For `r + 1 ≤ j ≤ q` and `k` outside `[h_j, h₀ - h_j]`, every rational brick with index
`i ∈ [j, q]` is in its `else` branch, hence divisible by `X`. -/
theorem X_dvd_ratBrick_tail {c : Config} (hc : Admissible c) (n : ℕ) {j k : ℕ}
    (hj : j ∈ Icc (c.r + 1) c.q) (hk : k < c.h n j ∨ c.h0 n - c.h n j < k) :
    ∀ i ∈ Icc j c.q, (X : PowerSeries ℚ) ∣ ratBrick (c.h n i) (c.h0 n - c.h n i + 1) k := by
  intro i hi
  have hj' := Finset.mem_Icc.mp hj
  have hi' := Finset.mem_Icc.mp hi
  have hh : c.h n j ≤ c.h n i := h_mono hc n (by omega) hi'.1 hi'.2
  apply X_dvd_ratBrick_of_not
  rintro ⟨h1, h2⟩
  rcases hk with hk | hk <;> omega

/-- `X^{q-j+1}` divides `Gk c n k` when `r + 1 ≤ j ≤ q` and `k ∉ [h_j, h₀ - h_j]`. -/
theorem X_pow_dvd_Gk {c : Config} (hc : Admissible c) (n : ℕ) {j k : ℕ}
    (hj : j ∈ Icc (c.r + 1) c.q) (hk : k < c.h n j ∨ c.h0 n - c.h n j < k) :
    (X : PowerSeries ℚ) ^ (c.q - j + 1) ∣ Gk c n k := by
  have hj' := Finset.mem_Icc.mp hj
  -- the `q - j + 1` factors with index in `[j, q]`
  have hdvd1 : (X : PowerSeries ℚ) ^ (c.q - j + 1) ∣
      ∏ i ∈ Icc j c.q, ratBrick (c.h n i) (c.h0 n - c.h n i + 1) k := by
    have hprod := Finset.prod_dvd_prod_of_dvd (s := Icc j c.q) (fun _ => (X : PowerSeries ℚ))
      (fun i => ratBrick (c.h n i) (c.h0 n - c.h n i + 1) k) (X_dvd_ratBrick_tail hc n hj hk)
    rw [Finset.prod_const, Nat.card_Icc] at hprod
    have he : c.q + 1 - j = c.q - j + 1 := by omega
    rwa [he] at hprod
  -- `[j, q] ⊆ [r+1, q]`
  have hsub : Icc j c.q ⊆ Icc (c.r + 1) c.q := by
    intro i hi
    simp only [Finset.mem_Icc] at hi ⊢
    omega
  unfold Gk
  exact Dvd.dvd.mul_left (dvd_trans hdvd1 (Finset.prod_dvd_prod_of_subset _ _ _ hsub)) _

end LaurentSupport

theorem LaurentSupp_proof : Stmt_LaurentSupp := by
  intro c hc n _ j k hj hk
  unfold B
  exact (PowerSeries.X_pow_dvd_iff.mp (LaurentSupport.X_pow_dvd_Gk hc n hj hk)) _ (by omega)

end ZetaWindow

end
