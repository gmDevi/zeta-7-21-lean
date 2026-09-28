import Zeta2Lean.Window.Statements

set_option linter.style.header false
set_option linter.style.longLine false

/-!
# Denominators of generalised harmonic numbers

**Proves `Stmt_Harmonic`** (no hypotheses):
* `int`: `N ≤ m → D_m^s · H^{(s)}_N ∈ ℤ`;
* `val`: for a prime `p` with `N < p²`, `H^{(s)}_N ≠ 0 → -s ≤ v_p(H^{(s)}_N)`,
where `H^{(s)}_N = harm N s = ∑_{l=1}^{N} 1/l^s` and `D_m = Nat.lcmUpto m`.

**Proof.**  *int*: for `1 ≤ l ≤ N ≤ m`, `l ∣ D_m` (`Finset.dvd_lcm`), so
`D_m^s / l^s = (D_m/l)^s` with `D_m/l ∈ ℕ` (`Nat.cast_div`); the integer is
`z = ∑_{l=1}^N (D_m/l)^s`.
*val*: for `1 ≤ l ≤ N < p²`, `p² ∤ l`, so `v_p(l) ≤ 1` and `v_p(1/l^s) = -s·v_p(l) ≥ -s`
(`padicValRat.inv`, `padicValRat.pow`, `padicValRat.of_nat`).  The ultrametric inequality
(`padicValRat.min_le_padicValRat_add`, extended to finite sums by induction in
`le_padicValRat_sum`) gives `v_p(H) ≥ -s`.  Because the bound `-s` is `≤ 0 = v_p(0)`, vanishing
partial sums need no special treatment, and the hypothesis `H ≠ 0` is not even used.

**Status: done** (complete, no gaps; axioms: propext, Classical.choice, Quot.sound).
-/

open Filter Topology Finset

noncomputable section

namespace ZetaWindow

namespace Harmonic

/-- Every `l ∈ [1, m]` divides `D_m = lcm(1, …, m)`. -/
theorem dvd_lcmUpto {l m : ℕ} (h1 : 1 ≤ l) (hlm : l ≤ m) : l ∣ Nat.lcmUpto m := by
  unfold Nat.lcmUpto
  exact Finset.dvd_lcm (s := Icc 1 m) (f := id) (mem_Icc.2 ⟨h1, hlm⟩)

/-- Ultrametric inequality for finite sums, for a bound `c ≤ 0` (so that `v_p(0) = 0 ≥ c` causes
no trouble): if every term has `v_p ≥ c`, so does the sum. -/
theorem le_padicValRat_sum {p : ℕ} [Fact p.Prime] {ι : Type*} (S : Finset ι) (f : ι → ℚ) (c : ℤ)
    (hc : c ≤ 0) (hf : ∀ i ∈ S, c ≤ padicValRat p (f i)) :
    c ≤ padicValRat p (∑ i ∈ S, f i) := by
  classical
  induction S using Finset.induction_on with
  | empty => simpa using hc
  | insert a S ha ih =>
    rw [Finset.sum_insert ha]
    have ih' := ih (fun i hi => hf i (Finset.mem_insert_of_mem hi))
    by_cases h0 : f a + ∑ i ∈ S, f i = 0
    · rw [h0, padicValRat.zero]
      exact hc
    · exact le_trans (le_min (hf a (Finset.mem_insert_self a S)) ih')
        (padicValRat.min_le_padicValRat_add h0)

/-- `v_p(l) ≤ 1` for `1 ≤ l < p²`. -/
theorem padicValNat_le_one {p l : ℕ} [Fact p.Prime] (h1 : 1 ≤ l) (hl : l < p ^ 2) :
    padicValNat p l ≤ 1 := by
  by_contra h
  have hdvd : p ^ 2 ∣ l := (padicValNat_dvd_iff_le (n := 2) (by omega)).2 (by omega)
  exact absurd (Nat.le_of_dvd (by omega) hdvd) (by omega)

/-- `v_p(1/l^s) ≥ -s` for `1 ≤ l < p²`. -/
theorem padicValRat_term {p l s : ℕ} [Fact p.Prime] (h1 : 1 ≤ l) (hl : l < p ^ 2) :
    -(s : ℤ) ≤ padicValRat p (1 / (l : ℚ) ^ s) := by
  rw [one_div, padicValRat.inv, padicValRat.pow, padicValRat.of_nat]
  have hv : (padicValNat p l : ℤ) ≤ 1 := by exact_mod_cast padicValNat_le_one h1 hl
  have hmul := mul_le_mul_of_nonneg_left hv (Int.natCast_nonneg s)
  linarith

end Harmonic

theorem Harmonic_proof : Stmt_Harmonic where
  int := by
    intro N m s hNm
    refine ⟨∑ l ∈ Icc 1 N, ((Nat.lcmUpto m / l : ℕ) : ℤ) ^ s, ?_⟩
    rw [harm, Finset.mul_sum]
    simp only [Int.cast_sum, Int.cast_pow, Int.cast_natCast]
    refine Finset.sum_congr rfl fun l hl => ?_
    obtain ⟨h1, hlN⟩ := mem_Icc.1 hl
    have hdvd : l ∣ Nat.lcmUpto m := Harmonic.dvd_lcmUpto h1 (hlN.trans hNm)
    have hl0 : (l : ℚ) ≠ 0 := by exact_mod_cast (show l ≠ 0 by omega)
    rw [Nat.cast_div hdvd hl0, div_pow, mul_one_div]
  val := by
    intro N s p hp hN _
    have := Fact.mk hp
    unfold harm
    refine Harmonic.le_padicValRat_sum _ _ _ (by omega) fun l hl => ?_
    obtain ⟨h1, hlN⟩ := mem_Icc.1 hl
    exact Harmonic.padicValRat_term h1 (by omega)

end ZetaWindow

end
