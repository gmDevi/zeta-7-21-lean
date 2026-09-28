import Zeta2Lean.Window.Statements

set_option linter.style.header false
set_option linter.style.longLine false

/-!
# Rough integrality of the Laurent coefficients (JTNB (8.10))

**Proves `Stmt_LaurentInt` from `Stmt_BrickInt` and `Stmt_LaurentSupp`:** for admissible `c`,
`n ≥ 1`, `r+1 ≤ j ≤ q`, `k ∈ Krange`: `D_{m₀}^{q-j} · B c n j k ∈ ℤ`,
`m₀ = max{h_r - 1, h₀ - 2h_{r+1}}`, `D_m = Nat.lcmUpto m`.

**Proof (as formalised below).**  If `k ∉ [h_j, h₀-h_j]`, then `B = 0` (`Stmt_LaurentSupp`).
Otherwise `h_{r+1} ≤ h_j ≤ k ≤ h₀ - h_j ≤ h₀ - h_{r+1}` (`h_mono`: η is sorted).  Put `D = D_{m₀}`
and call `f` *`D`-integral* if `D^i [ε^i] f ∈ ℤ` for all `i`; these series form a subring `DInt D`
of `ℚ⟦ε⟧` (Cauchy product), and `DInt D_m ⊆ DInt D_{m'}` for `m ≤ m'` (`mem_lcmUpto_mono`).
Every factor of `Gk c n k` is `D`-integral (`Gk_mem`):
* `C(h₀-2k) + 2X` has integer coefficients (`C_mem`, `X_mem`);
* `polyBrick h_i 1 k` and `polyBrick h₀ (h₀-h_i+1) k` (`i ≤ r`) by `Stmt_BrickInt.poly`: in both
  cases `a - b = h_i - 1 ≤ h_r - 1 ≤ m₀` (`h_mono`, and `h_i ≤ h₀` from `two_h_le`);
* `ratBrick h_i (h₀-h_i+1) k` (`i > r`) by `Stmt_BrickInt.rat` with `a₀ = h_{r+1}`,
  `b₀ = h₀ - h_{r+1} + 1`, so `b₀ - a₀ - 1 = h₀ - 2h_{r+1} ≤ m₀`; its hypotheses are `a₀ ≤ h_i`
  (`h_mono`), `h_i < h₀ - h_i + 1` (`two_h_le`: `2h_i ≤ h₀` from `2η_q < η₀`),
  `h₀ - h_i + 1 ≤ b₀`, and `a₀ ≤ k < b₀` (the support range above).
Hence `Gk c n k ∈ DInt D` and `D^{q-j} [ε^{q-j}] Gk c n k = D^{q-j} B_{j,k} ∈ ℤ`.

The hypothesis `k ∈ Krange` is not used: the conclusion holds for every `k ∈ ℕ` (outside the
support range `B = 0`).  From `Admissible` only `eta_mono`, `two_eta_lt` and `r + 4 ≤ q` (for
`r ≤ q`) are used.  The subring `DInt` duplicates `BrickIntegral.DInt` (proof files import only
`Window.Statements`).

**Numerical check.** `python/window_mirror.py`, section "Laurent data …": all `j`, all `k ∈ Krange`,
exact (`cfgW` `n = 1, 2`; Theorem 3 configuration `n = 1, 2, 3`).

**Status: done** (complete, no gaps; `#print axioms LaurentInt_proof`: propext, Classical.choice,
Quot.sound).
-/

open Filter Topology Finset PowerSeries

noncomputable section

namespace ZetaWindow

namespace LaurentIntegral

/-! ### `d`-integral power series -/

/-- The subring of `ℚ⟦X⟧` of `d`-integral series: `d^i · [X^i] A ∈ ℤ` for every `i`. -/
def DInt (d : ℚ) : Subring (PowerSeries ℚ) where
  carrier := {A | ∀ i : ℕ, ∃ z : ℤ, d ^ i * coeff i A = z}
  mul_mem' := by
    intro A B hA hB i
    simp only [Set.mem_ofPred_eq] at hA hB
    choose zA hzA using hA
    choose zB hzB using hB
    refine ⟨∑ p ∈ antidiagonal i, zA p.1 * zB p.2, ?_⟩
    rw [coeff_mul, Finset.mul_sum]
    push_cast
    refine Finset.sum_congr rfl fun p hp => ?_
    rw [← hzA, ← hzB, ← (mem_antidiagonal.1 hp), pow_add]
    ring
  one_mem' := by
    intro i
    rcases i with _ | i
    · exact ⟨1, by simp⟩
    · exact ⟨0, by simp [coeff_one]⟩
  add_mem' := by
    intro A B hA hB i
    obtain ⟨a, ha⟩ := hA i
    obtain ⟨b, hb⟩ := hB i
    exact ⟨a + b, by rw [map_add, mul_add, ha, hb]; push_cast; ring⟩
  zero_mem' := fun i => ⟨0, by simp⟩
  neg_mem' := by
    intro A hA i
    obtain ⟨a, ha⟩ := hA i
    exact ⟨-a, by rw [map_neg, mul_neg, ha]; push_cast; ring⟩

theorem DInt_mem {d : ℚ} {A : PowerSeries ℚ} :
    A ∈ DInt d ↔ ∀ i : ℕ, ∃ z : ℤ, d ^ i * coeff i A = z := Iff.rfl

/-- Constants with an integer value are `d`-integral. -/
theorem C_mem {d a : ℚ} (h : ∃ z : ℤ, a = z) : C a ∈ DInt d := by
  obtain ⟨z, rfl⟩ := h
  rw [DInt_mem]
  intro i
  rw [coeff_C]
  split_ifs with hi
  · subst hi
    exact ⟨z, by simp⟩
  · exact ⟨0, by simp⟩

/-- `X` is `d`-integral for a natural number `d`. -/
theorem X_mem (d : ℕ) : (X : PowerSeries ℚ) ∈ DInt (d : ℚ) := by
  rw [DInt_mem]
  intro i
  rw [coeff_X]
  split_ifs with hi
  · subst hi
    exact ⟨d, by simp⟩
  · exact ⟨0, by simp⟩

/-- Enlarging the denominator: for `d ∣ e`, `d`-integral series are `e`-integral. -/
theorem mem_of_dvd {d e : ℕ} (hde : d ∣ e) {A : PowerSeries ℚ} (hA : A ∈ DInt (d : ℚ)) :
    A ∈ DInt (e : ℚ) := by
  obtain ⟨q, rfl⟩ := hde
  rw [DInt_mem] at hA ⊢
  intro i
  obtain ⟨z, hz⟩ := hA i
  refine ⟨(q : ℤ) ^ i * z, ?_⟩
  push_cast
  linear_combination ((q : ℚ) ^ i) * hz

/-- `D_m ∣ D_{m'}` for `m ≤ m'`. -/
theorem lcmUpto_dvd_lcmUpto {m m' : ℕ} (h : m ≤ m') : Nat.lcmUpto m ∣ Nat.lcmUpto m' := by
  unfold Nat.lcmUpto
  exact Finset.lcm_dvd fun l hl => Finset.dvd_lcm (Finset.Icc_subset_Icc_right h hl)

/-- `D_m`-integral series are `D_{m'}`-integral for `m ≤ m'`. -/
theorem mem_lcmUpto_mono {m m' : ℕ} (h : m ≤ m') {A : PowerSeries ℚ}
    (hA : A ∈ DInt (Nat.lcmUpto m : ℚ)) : A ∈ DInt (Nat.lcmUpto m' : ℚ) :=
  mem_of_dvd (lcmUpto_dvd_lcmUpto h) hA

/-! ### The inequalities between the `h_j` -/

/-- `h` is monotone in the index on `[1, q]` (from `Admissible.eta_mono`). -/
theorem h_mono {c : Config} (hc : Admissible c) (n : ℕ) {i j : ℕ} (h1 : 1 ≤ i) (hij : i ≤ j)
    (hj : j ≤ c.q) : c.h n i ≤ c.h n j := by
  unfold Config.h
  exact Nat.add_le_add_right (Nat.mul_le_mul (hc.eta_mono i j h1 hij hj) (le_refl n)) 1

/-- `2 h_i ≤ h₀` for `1 ≤ i ≤ q` (from `η_i ≤ η_q` and `2η_q < η₀`). -/
theorem two_h_le {c : Config} (hc : Admissible c) (n : ℕ) {i : ℕ} (h1 : 1 ≤ i) (hi : i ≤ c.q) :
    2 * c.h n i ≤ c.h0 n := by
  have he : 2 * c.eta i ≤ c.eta0 := by
    have := hc.eta_mono i c.q h1 hi le_rfl
    have := hc.two_eta_lt
    omega
  have hm : 2 * (c.eta i * n) ≤ c.eta0 * n := by
    rw [← mul_assoc]
    exact Nat.mul_le_mul_right n he
  unfold Config.h Config.h0
  omega

/-! ### `G_k` is `D_{m₀}`-integral on the support range -/

/-- **(8.10) for the brick product.**  For `h_{r+1} ≤ k ≤ h₀ - h_{r+1}`, `G_k = ε^{q-r} R̃(-k+ε)`
is `D_{m₀}`-integral. -/
theorem Gk_mem (hBI : Stmt_BrickInt) {c : Config} (hc : Admissible c) (n : ℕ) {k : ℕ}
    (hk1 : c.h n (c.r + 1) ≤ k) (hk2 : k ≤ c.h0 n - c.h n (c.r + 1)) :
    Gk c n k ∈ DInt (Nat.lcmUpto (m0 c n) : ℚ) := by
  have hrq : c.r + 4 ≤ c.q := hc.r_add_four_le_q
  have hm1 : c.h n c.r - 1 ≤ m0 c n := le_max_left _ _
  have hm2 : c.h0 n - 2 * c.h n (c.r + 1) ≤ m0 c n := le_max_right _ _
  unfold Gk
  refine mul_mem (mul_mem ?_ ?_) ?_
  · -- the linear factor `(h₀ - 2k) + 2ε`
    refine add_mem (C_mem ⟨(c.h0 n : ℤ) - 2 * k, by push_cast; ring⟩)
      (mul_mem (C_mem ⟨2, by norm_num⟩) (X_mem _))
  · -- the polynomial bricks `P_i Q_i`, `i ≤ r`
    refine prod_mem fun i hi => ?_
    have hi' := Finset.mem_Icc.1 hi
    have hir : c.h n i ≤ c.h n c.r := h_mono hc n hi'.1 hi'.2 (by omega)
    have h1i : 1 ≤ c.h n i := by unfold Config.h; omega
    have h2i : 2 * c.h n i ≤ c.h0 n := two_h_le hc n hi'.1 (by omega)
    refine mul_mem ?_ ?_
    · exact mem_lcmUpto_mono (by omega)
        (DInt_mem.2 fun l => hBI.poly (c.h n i) 1 k l h1i)
    · exact mem_lcmUpto_mono (by omega)
        (DInt_mem.2 fun l => hBI.poly (c.h0 n) (c.h0 n - c.h n i + 1) k l (by omega))
  · -- the rational bricks `ε S_i`, `i > r`
    refine prod_mem fun i hi => ?_
    have hi' := Finset.mem_Icc.1 hi
    have hri : c.h n (c.r + 1) ≤ c.h n i := h_mono hc n (by omega) hi'.1 hi'.2
    have h2i : 2 * c.h n i ≤ c.h0 n := two_h_le hc n (by omega) hi'.2
    exact mem_lcmUpto_mono (by omega)
      (DInt_mem.2 fun l => hBI.rat (c.h n i) (c.h0 n - c.h n i + 1) k (c.h n (c.r + 1))
        (c.h0 n - c.h n (c.r + 1) + 1) l hri (by omega) (by omega) hk1 (by omega))

end LaurentIntegral

open LaurentIntegral in
theorem LaurentInt_proof (hBI : Stmt_BrickInt) (hS : Stmt_LaurentSupp) : Stmt_LaurentInt := by
  intro c hc n hn j k hj _hk
  by_cases hsupp : k < c.h n j ∨ c.h0 n - c.h n j < k
  · exact ⟨0, by rw [hS c hc n hn j k hj hsupp, mul_zero, Int.cast_zero]⟩
  · rw [not_or, not_lt, not_lt] at hsupp
    have hj' := Finset.mem_Icc.1 hj
    have hrq : c.r + 4 ≤ c.q := hc.r_add_four_le_q
    have hrj : c.h n (c.r + 1) ≤ c.h n j := h_mono hc n (by omega) hj'.1 hj'.2
    unfold B
    exact DInt_mem.1 (Gk_mem hBI hc n (by omega) (by omega)) (c.q - j)

end ZetaWindow

end
