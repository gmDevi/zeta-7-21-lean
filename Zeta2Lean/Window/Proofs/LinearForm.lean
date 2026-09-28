module

public import Zeta2Lean.Window.Statements

@[expose] public section

set_option linter.style.header false
set_option linter.style.longLine false

/-!
# The linear form in odd zeta values (JTNB Lemma 19, first half, p. 281–282; docs/window/proof.md §1)

**Proves `Stmt_LinearForm`** from `Stmt_PF` and `Stmt_CoeffVanish`: for admissible `c` and `n ≥ 1`,
`HasSum (fun t : ℕ => (term c n t : ℝ)) (-(A0 c n) + ∑_{s ∈ window c} (Acoef c n s) * zetaR s)`.

**Informal proof.**
1. *Terms.*  At a non-pole `y`, `Stmt_PF` gives
   `[ε^{r-1}] Rser c n y = ∑_{j,k} B_{j,k} [ε^{r-1}] (y+k+ε)^{-(j-r)} = ∑_{j,k} B_{j,k} C(j-2, r-1) (y+k)^{-(j-1)}`,
   using `[ε^m] (a+ε)^{-s} = (-1)^m C(s+m-1, m) a^{-s-m}` and `r` odd (`(-1)^{r-1} = 1`).
2. *Start the series at `t = 1 - h₁`.*  For `1 ≤ l ≤ h₁ - 1` the factor `i = l` of
   `(∏_{i=1}^{h₀-1} (y+i+ε))^r` at `y = -l` is `ε^r`, so `X^r ∣ Rser c n (-l)` and its coefficient of
   `ε^{r-1}` vanishes.  Hence, with `a = h₁ - 1` and `g(t') = [ε^{r-1}] Rser c n (t' - a)`,
   `g(t') = 0` for `t' < a` and `g(t + a) = term c n t`: the two series have the same sum.
3. *Series.*  Every `y = t' - a` (`t' ∈ ℕ`) is a non-pole (`y + k ≥ t' + 1` for `k ∈ Krange`), so by 1.
   `g(t') = ∑_{j,k} B_{j,k} C(j-2,r-1) (t' + k')^{-(j-1)}` with `k' = k - a ≥ 1`.  For `w = j - 1 ≥ r ≥ 3`,
   `∑_{t' ≥ 0} (t'+k')^{-w} = ζ(w) - H^{(w)}_{k'-1} = ζ(w) - H^{(w)}_{k-h₁}`, and a finite linear
   combination of `HasSum`s gives `HasSum g (∑_{j,k} B_{j,k} C(j-2,r-1) (ζ(j-1) - H^{(j-1)}_{k-h₁}))`.
   (This is JTNB's cut-off `H_{k-h₁}` of `A₀`; the blueprint's equivalent route via
   `H_{k-1} - H_{k-h₁} = ∑_{l=1}^{h₁-1} (k-l)^{-w}` is not needed.)
4. *Regroup.*  The value is `∑_{s=r}^{q-1} A_s ζ(s) - A₀` (`s = j - 1`).
5. *Vanishing.*  `A_r = 0` by `ressum`; for even `s`, reindexing `k ↦ h₀ - k` (an involution of
   `Krange`) and `symm` give `∑_k B_{s+1,k} = (-1)^{s+1} ∑_k B_{s+1,k} = -∑_k B_{s+1,k}`, so `A_s = 0`.
   The surviving `s ∈ [r, q-1]` are the odd `s ≥ r+2`, `s ≤ q-2`, i.e. `window c`.

**Formal proof (below, namespace `ZetaWindow.LinearForm`).**
* `invSer a m` is the explicit series `∑_i (-1)^i C(i+m, m) a^{-(i+m+1)} ε^i`;
  `pow_mul_invSer`: `(C a + X)^{m+1} * invSer a m = 1` (induction on `m`, Pascal's rule), hence
  `inv_pow_eq_invSer` (`PowerSeries.inv_eq_iff_mul_eq_one`) and `coeff_inv_pow`
  (`[ε^{r-1}] ((b+ε)^{j-r})⁻¹ = C(j-2, r-1) b^{-(j-1)}`, `Nat.choose_symm_add`).
* `coeff_Rser_eq` (step 1, from `Stmt_PF`), `coeff_Rser_zero` (step 2, `PowerSeries.X_pow_dvd_iff`;
  it does not even need the denominator to be a unit).
* `hasSum_shift` (step 3): `Real.summable_one_div_nat_pow`, `summable_nat_add_iff`,
  `hasSum_nat_add_iff'`, reindexing `range (k-1) ≃ Icc 1 (k-1)`.
* `sum_Krange_reflect`, `Acoef_eq_zero` (step 5), `sum_Icc_shift` (`j = s + 1`), `h1_lt_h0`.
* `LinearForm_proof`: `hasSum_sum` twice + `HasSum.mul_left`, then `hasSum_nat_add_iff' a` removes
  the vanishing first `a` terms, and the value is regrouped with `Finset.sum_subset`.

Nothing depends on `r = 3` or on `cfgW`: the statement is proved for every admissible configuration
and every `n ≥ 1`; besides the hypotheses it uses only `Odd r`, `Odd q`, `r ≥ 3`, `q ≥ 1` and `η₁ ≤ η_q < η₀/2`.

**Numerical check.** `python/window_mirror.py`: (a) the value `-A₀ + ∑ A_s ζ(s)` for `cfgW`, `n = 1, 2`
equals the independent engine `docs/window/zud_exact.py` (validated against the Barnes integral to
`1e-13`, `docs/window/barnes_q23_160_n1to9.log`): `log|F̃₁| = -799.4450029421`,
`log|F̃₂| = -1559.4383100008`; (b) for the Theorem 3 configuration the exact partial sums
`∑_{t<1500} term t` agree with the value to relative error `8e-99`.

**Status: done** (complete, no gaps; `#print axioms LinearForm_proof`: propext, Classical.choice,
Quot.sound).
-/

open Filter Topology Finset PowerSeries

noncomputable section

namespace ZetaWindow

namespace LinearForm

/-! ### The explicit inverse of `(a + ε)^{m+1}` -/

/-- `∑_i (-1)^i C(i+m, m) a^{-(i+m+1)} ε^i`, the expansion of `(a + ε)^{-(m+1)}`. -/
def invSer (a : ℚ) (m : ℕ) : PowerSeries ℚ :=
  PowerSeries.mk fun i => (-1) ^ i * ((i + m).choose m : ℚ) * a⁻¹ ^ (i + m + 1)

theorem coeff_invSer (a : ℚ) (m i : ℕ) :
    coeff i (invSer a m) = (-1) ^ i * ((i + m).choose m : ℚ) * a⁻¹ ^ (i + m + 1) := by
  rw [invSer, coeff_mk]

theorem mul_invSer_zero (a : ℚ) (ha : a ≠ 0) : (C a + X) * invSer a 0 = 1 := by
  ext i
  rw [add_mul, map_add, coeff_C_mul, coeff_one]
  rcases i with _ | i
  · rw [coeff_zero_X_mul, coeff_invSer]
    simp only [pow_zero, add_zero, Nat.choose_self, Nat.cast_one, mul_one, one_mul, zero_add,
      pow_one, ite_true]
    exact mul_inv_cancel₀ ha
  · rw [coeff_succ_X_mul, coeff_invSer, coeff_invSer]
    simp only [Nat.choose_zero_right, Nat.cast_one, mul_one, add_zero, Nat.add_one_ne_zero,
      ite_false]
    linear_combination (-(-1) ^ i * a⁻¹ ^ (i + 1)) * mul_inv_cancel₀ ha

theorem mul_invSer_succ (a : ℚ) (ha : a ≠ 0) (m : ℕ) :
    (C a + X) * invSer a (m + 1) = invSer a m := by
  ext i
  rw [add_mul, map_add, coeff_C_mul]
  rcases i with _ | i
  · rw [coeff_zero_X_mul, coeff_invSer, coeff_invSer]
    simp only [pow_zero, zero_add, Nat.choose_self, Nat.cast_one, one_mul, add_zero]
    linear_combination a⁻¹ ^ (m + 1) * mul_inv_cancel₀ ha
  · rw [coeff_succ_X_mul, coeff_invSer, coeff_invSer, coeff_invSer]
    have h1 : (((i + 1 + (m + 1)).choose (m + 1) : ℕ) : ℚ) =
        ((i + 1 + m).choose m : ℚ) + ((i + (m + 1)).choose (m + 1) : ℚ) := by
      have e : i + 1 + (m + 1) = (i + (m + 1)) + 1 := by omega
      rw [e, Nat.choose_succ_succ', show i + (m + 1) = i + 1 + m by omega]
      push_cast
      ring
    rw [h1]
    linear_combination
      (-1) ^ (i + 1) * (((i + 1 + m).choose m : ℚ) + ((i + (m + 1)).choose (m + 1) : ℚ)) *
        a⁻¹ ^ (i + m + 2) * mul_inv_cancel₀ ha

/-- `(a + ε)^{m+1} · ∑_i (-1)^i C(i+m, m) a^{-(i+m+1)} ε^i = 1`. -/
theorem pow_mul_invSer (a : ℚ) (ha : a ≠ 0) (m : ℕ) : (C a + X) ^ (m + 1) * invSer a m = 1 := by
  induction m with
  | zero => rw [zero_add, pow_one]; exact mul_invSer_zero a ha
  | succ m ih => rw [pow_succ, mul_assoc, mul_invSer_succ a ha m, ih]

theorem inv_pow_eq_invSer (a : ℚ) (ha : a ≠ 0) (m : ℕ) :
    ((C a + X) ^ (m + 1))⁻¹ = invSer a m := by
  rw [PowerSeries.inv_eq_iff_mul_eq_one]
  · rw [mul_comm]
    exact pow_mul_invSer a ha m
  · simp [ha]

/-- `[ε^{r-1}] (b + ε)^{-(j-r)} = C(j-2, r-1) b^{-(j-1)}` for odd `r` and `j ≥ r+1`. -/
theorem coeff_inv_pow (r j : ℕ) (hr : Odd r) (hj : r + 1 ≤ j) (b : ℚ) (hb : b ≠ 0) :
    coeff (r - 1) (((C b + X) ^ (j - r))⁻¹ : PowerSeries ℚ) =
      ((j - 2).choose (r - 1) : ℚ) * b⁻¹ ^ (j - 1) := by
  obtain ⟨m, rfl⟩ : ∃ m, j = r + 1 + m := ⟨j - (r + 1), by omega⟩
  have e1 : r + 1 + m - r = m + 1 := by omega
  rw [e1, inv_pow_eq_invSer b hb m, coeff_invSer]
  obtain ⟨u, rfl⟩ := hr
  have e2 : 2 * u + 1 - 1 = 2 * u := by omega
  have e3 : 2 * u + 1 + 1 + m - 2 = 2 * u + m := by omega
  have e4 : 2 * u + 1 + 1 + m - 1 = 2 * u + m + 1 := by omega
  rw [e2, e3, e4, pow_mul, neg_one_sq, one_pow, one_mul, Nat.choose_symm_add]

/-! ### The terms of the series via partial fractions -/

/-- `[ε^{r-1}]` of the partial-fraction sum of `Stmt_PF`. -/
theorem coeff_pf_sum (c : Config) (hc : Admissible c) (n : ℕ) (y : ℚ)
    (hy : ∀ k ∈ Krange c n, y + k ≠ 0) :
    coeff (c.r - 1) (∑ j ∈ Icc (c.r + 1) c.q, ∑ k ∈ Krange c n,
      C (B c n j k) * ((C (y + k) + X) ^ (j - c.r))⁻¹) =
    ∑ j ∈ Icc (c.r + 1) c.q, ∑ k ∈ Krange c n,
      B c n j k * ((j - 2).choose (c.r - 1) : ℚ) * (y + k)⁻¹ ^ (j - 1) := by
  rw [map_sum]
  refine sum_congr rfl fun j hj => ?_
  rw [map_sum]
  refine sum_congr rfl fun k hk => ?_
  rw [coeff_C_mul, coeff_inv_pow c.r j hc.r_odd (mem_Icc.1 hj).1 (y + k) (hy k hk), mul_assoc]

/-- The coefficient `[ε^{r-1}] R̃(y+ε)` at a non-pole `y`, from `Stmt_PF`. -/
theorem coeff_Rser_eq (hPF : Stmt_PF) (c : Config) (hc : Admissible c) (n : ℕ) (hn : 1 ≤ n)
    (y : ℚ) (hy : ∀ k ∈ Krange c n, y + k ≠ 0) :
    coeff (c.r - 1) (Rser c n y) =
    ∑ j ∈ Icc (c.r + 1) c.q, ∑ k ∈ Krange c n,
      B c n j k * ((j - 2).choose (c.r - 1) : ℚ) * (y + k)⁻¹ ^ (j - 1) := by
  rw [hPF c hc n hn y hy]
  exact coeff_pf_sum c hc n y hy

/-- At `y = -l` with `1 ≤ l < h₀`, `R̃(y+ε)` has a zero of order `r` (the factor `i = l` of
`(∏_{i=1}^{h₀-1} (y+i+ε))^r` is `ε^r`), so `[ε^{r-1}] R̃(y+ε) = 0`. -/
theorem coeff_Rser_zero (c : Config) (n l : ℕ) (hr : 1 ≤ c.r) (hl1 : 1 ≤ l) (hl : l < c.h0 n)
    (y : ℚ) (hy : y + l = 0) :
    coeff (c.r - 1) (Rser c n y) = 0 := by
  have hdvd : (X : PowerSeries ℚ) ∣ ∏ i ∈ Ico 1 (c.h0 n), (C (y + i) + X) := by
    have h := Finset.dvd_prod_of_mem (fun i : ℕ => C (y + i) + X) (mem_Ico.2 ⟨hl1, hl⟩)
    simpa [hy] using h
  have hdvd2 : (X : PowerSeries ℚ) ^ c.r ∣ Rser c n y := by
    unfold Rser
    exact dvd_mul_of_dvd_left (dvd_mul_of_dvd_right (pow_dvd_pow_of_dvd hdvd c.r) _) _
  exact (PowerSeries.X_pow_dvd_iff.1 hdvd2) (c.r - 1) (by omega)

/-! ### Shifted `p`-series -/

/-- `∑_{t ≥ 0} (t+k)^{-w} = ζ(w) - H^{(w)}_{k-1}` for `w ≥ 2`, `k ≥ 1`. -/
theorem hasSum_shift (w k : ℕ) (hw : 2 ≤ w) (hk : 1 ≤ k) :
    HasSum (fun t : ℕ => ((t : ℝ) + k)⁻¹ ^ w) (zetaR w - (harm (k - 1) w : ℝ)) := by
  have hs : Summable (fun m : ℕ => 1 / ((m : ℝ) + 1) ^ w) := by
    have h0 := (summable_nat_add_iff 1).mpr
      (Real.summable_one_div_nat_pow.mpr (by omega : 1 < w))
    refine h0.congr fun m => ?_
    push_cast
    ring
  have h1 : HasSum (fun m : ℕ => 1 / ((m : ℝ) + 1) ^ w) (zetaR w) := hs.hasSum
  have h2 := (hasSum_nat_add_iff' (k - 1)).mpr h1
  have e1 : (fun t : ℕ => 1 / (((t + (k - 1) : ℕ) : ℝ) + 1) ^ w) =
      fun t : ℕ => ((t : ℝ) + k)⁻¹ ^ w := by
    funext t
    rw [one_div, inv_pow]
    congr 2
    push_cast [Nat.cast_sub hk]
    ring
  have e2 : ∑ i ∈ range (k - 1), 1 / ((i : ℝ) + 1) ^ w = (harm (k - 1) w : ℝ) := by
    unfold harm
    push_cast
    apply Finset.sum_nbij' (fun i => i + 1) (fun l => l - 1)
    · intro a ha
      simp only [mem_range, mem_Icc] at ha ⊢
      omega
    · intro a ha
      simp only [mem_range, mem_Icc] at ha ⊢
      omega
    · intro a _
      simp
    · intro a ha
      simp only [mem_Icc] at ha
      omega
    · intro a _
      push_cast
      ring
  rw [e1, e2] at h2
  exact h2

/-! ### The vanishing coefficients -/

/-- `k ↦ h₀ - k` is an involution of `Krange`. -/
theorem sum_Krange_reflect (c : Config) (n : ℕ) (f : ℕ → ℚ) :
    ∑ k ∈ Krange c n, f (c.h0 n - k) = ∑ k ∈ Krange c n, f k := by
  apply Finset.sum_nbij' (fun k => c.h0 n - k) (fun k => c.h0 n - k)
  · intro a ha
    simp only [Krange, mem_Icc] at ha ⊢
    omega
  · intro a ha
    simp only [Krange, mem_Icc] at ha ⊢
    omega
  · intro a ha
    simp only [Krange, mem_Icc] at ha
    omega
  · intro a ha
    simp only [Krange, mem_Icc] at ha
    omega
  · intro a _
    rfl

/-- `A_s = 0` for `r ≤ s ≤ q - 1`, `s ∉ window`: `A_r = 0` (sum of residues) and `A_s = 0` for
even `s` (symmetry `k ↦ h₀ - k`). -/
theorem Acoef_eq_zero (hCV : Stmt_CoeffVanish) (c : Config) (hc : Admissible c) (n : ℕ)
    (hn : 1 ≤ n) (s : ℕ) (hs : s ∈ Icc c.r (c.q - 1)) (hsw : s ∉ window c) :
    Acoef c n s = 0 := by
  have hs' := mem_Icc.1 hs
  simp only [window, mem_filter, mem_Icc, not_and] at hsw
  unfold Acoef
  by_cases hsr : s = c.r
  · rw [hsr, hCV.ressum c hc n hn, mul_zero]
  · rcases Nat.even_or_odd s with he | ho
    · have hj : s + 1 ∈ Icc (c.r + 1) c.q := by
        obtain ⟨w, hw⟩ := hc.q_odd
        rw [mem_Icc]
        omega
      have hsym : ∀ k ∈ Krange c n, B c n (s + 1) (c.h0 n - k) = -B c n (s + 1) k := by
        intro k hk
        rw [hCV.symm c hc n hn (s + 1) k hj hk, he.add_one.neg_one_pow, neg_one_mul]
      have h1 : ∑ k ∈ Krange c n, B c n (s + 1) (c.h0 n - k) = ∑ k ∈ Krange c n, B c n (s + 1) k :=
        sum_Krange_reflect c n (B c n (s + 1))
      have h2 : ∑ k ∈ Krange c n, B c n (s + 1) (c.h0 n - k) =
          -∑ k ∈ Krange c n, B c n (s + 1) k := by
        rw [← sum_neg_distrib]
        exact sum_congr rfl hsym
      have h3 : ∑ k ∈ Krange c n, B c n (s + 1) k = 0 := by linarith
      rw [h3, mul_zero]
    · exfalso
      obtain ⟨u, hu⟩ := ho
      obtain ⟨v, hv⟩ := hc.r_odd
      obtain ⟨w, hw⟩ := hc.q_odd
      exact hsw ⟨by omega, by omega⟩ ⟨u, hu⟩

/-- Reindexing `j = s + 1`. -/
theorem sum_Icc_shift (F : ℕ → ℝ) (r q : ℕ) (hq : 1 ≤ q) :
    ∑ j ∈ Icc (r + 1) q, F (j - 1) = ∑ s ∈ Icc r (q - 1), F s := by
  apply Finset.sum_nbij' (fun j => j - 1) (fun s => s + 1)
  · intro a ha
    simp only [mem_Icc] at ha ⊢
    omega
  · intro a ha
    simp only [mem_Icc] at ha ⊢
    omega
  · intro a ha
    simp only [mem_Icc] at ha
    omega
  · intro a ha
    simp only [mem_Icc] at ha
    omega
  · intro a _
    rfl

/-- `h₁ < h₀` (from `η₁ ≤ η_q < η₀/2`). -/
theorem h1_lt_h0 (c : Config) (hc : Admissible c) (n : ℕ) : c.h n 1 < c.h0 n := by
  have hq : 1 ≤ c.q := by
    have := hc.three_le_r
    have := hc.r_add_four_le_q
    omega
  have h1 : c.eta 1 ≤ c.eta c.q := hc.eta_mono 1 c.q le_rfl hq le_rfl
  have h2 := hc.two_eta_lt
  have h3 : c.eta 1 * n ≤ c.eta0 * n := Nat.mul_le_mul_right n (by omega)
  simp only [Config.h, Config.h0]
  omega

end LinearForm

open LinearForm in
theorem LinearForm_proof (hPF : Stmt_PF) (hCV : Stmt_CoeffVanish) : Stmt_LinearForm := by
  intro c hc n hn
  obtain ⟨a, ha⟩ : ∃ a, c.h n 1 = a + 1 := ⟨c.eta 1 * n, rfl⟩
  have hr3 := hc.three_le_r
  have hr1 : 1 ≤ c.r := by omega
  have hq1 : 1 ≤ c.q := by
    have := hc.r_add_four_le_q
    omega
  have hh1 := h1_lt_h0 c hc n
  have hKa : ∀ k ∈ Krange c n, a + 1 ≤ k := by
    intro k hk
    simp only [Krange, mem_Icc] at hk
    omega
  -- the series started at `t = -a = 1 - h₁`
  set g : ℕ → ℝ := fun t' => ((coeff (c.r - 1) (Rser c n ((t' : ℚ) - a)) : ℚ) : ℝ) with hg_def
  have hnp : ∀ t' : ℕ, ∀ k ∈ Krange c n, ((t' : ℚ) - a) + k ≠ 0 := by
    intro t' k hk
    have h1 : ((a + 1 : ℕ) : ℚ) ≤ k := by exact_mod_cast hKa k hk
    have h2 : (0 : ℚ) ≤ t' := Nat.cast_nonneg _
    push_cast at h1
    apply ne_of_gt
    linarith
  have hg : ∀ t' : ℕ, g t' = ∑ j ∈ Icc (c.r + 1) c.q, ∑ k ∈ Krange c n,
      ((B c n j k : ℝ) * ((j - 2).choose (c.r - 1) : ℝ)) *
        ((t' : ℝ) + ((k - a : ℕ) : ℝ))⁻¹ ^ (j - 1) := by
    intro t'
    simp only [hg_def]
    rw [coeff_Rser_eq hPF c hc n hn _ (hnp t')]
    push_cast
    refine sum_congr rfl fun j _ => sum_congr rfl fun k hk => ?_
    rw [Nat.cast_sub (by have := hKa k hk; omega : a ≤ k)]
    ring
  have hgV : HasSum g (∑ j ∈ Icc (c.r + 1) c.q, ∑ k ∈ Krange c n,
      ((B c n j k : ℝ) * ((j - 2).choose (c.r - 1) : ℝ)) *
        (zetaR (j - 1) - (harm (k - c.h n 1) (j - 1) : ℝ))) := by
    rw [show g = _ from funext hg]
    refine hasSum_sum fun j hj => hasSum_sum fun k hk => ?_
    refine HasSum.mul_left _ ?_
    have hj' := mem_Icc.1 hj
    have hkk := hKa k hk
    have h := hasSum_shift (j - 1) (k - a) (by omega) (by omega)
    rwa [show k - a - 1 = k - c.h n 1 by omega] at h
  -- the first `a` terms vanish (`y = -l`, `1 ≤ l ≤ h₁ - 1`)
  have hzero : ∀ i ∈ range a, g i = 0 := by
    intro i hi
    have hi' := mem_range.1 hi
    simp only [hg_def]
    rw [coeff_Rser_zero c n (a - i) hr1 (by omega) (by omega) _
      (by rw [Nat.cast_sub hi'.le]; ring)]
    simp
  have key := (hasSum_nat_add_iff' a).mpr hgV
  rw [Finset.sum_eq_zero hzero, sub_zero] at key
  have hfun : (fun t : ℕ => (term c n t : ℝ)) = fun t => g (t + a) := by
    funext t
    simp only [hg_def, term]
    rw [show ((t + a : ℕ) : ℚ) - a = (t : ℚ) by push_cast; ring]
  rw [hfun]
  convert key using 1
  -- the value: regroup, `A_r = 0`, `A_{even} = 0`
  have hA0 : (A0 c n : ℝ) = ∑ j ∈ Icc (c.r + 1) c.q, ∑ k ∈ Krange c n,
      ((B c n j k : ℝ) * ((j - 2).choose (c.r - 1) : ℝ)) * (harm (k - c.h n 1) (j - 1) : ℝ) := by
    simp only [A0]
    push_cast
    refine sum_congr rfl fun j _ => ?_
    rw [mul_sum]
    refine sum_congr rfl fun k _ => ?_
    ring
  have hZ : ∑ s ∈ window c, (Acoef c n s : ℝ) * zetaR s =
      ∑ j ∈ Icc (c.r + 1) c.q, ∑ k ∈ Krange c n,
        ((B c n j k : ℝ) * ((j - 2).choose (c.r - 1) : ℝ)) * zetaR (j - 1) := by
    have hsub : window c ⊆ Icc c.r (c.q - 1) := by
      intro s hs
      simp only [window, mem_filter, mem_Icc] at hs ⊢
      omega
    rw [sum_subset hsub (fun s hs hsw => by rw [Acoef_eq_zero hCV c hc n hn s hs hsw]; simp)]
    rw [← sum_Icc_shift (fun s => (Acoef c n s : ℝ) * zetaR s) c.r c.q hq1]
    refine sum_congr rfl fun j hj => ?_
    have hj' := mem_Icc.1 hj
    simp only [Acoef]
    rw [show j - 1 + 1 = j by omega, show j - 1 - 1 = j - 2 by omega]
    push_cast
    simp only [mul_sum, sum_mul]
    refine sum_congr rfl fun k _ => ?_
    ring
  rw [hA0, hZ]
  simp only [mul_sub, sum_sub_distrib]
  ring

end ZetaWindow

end
