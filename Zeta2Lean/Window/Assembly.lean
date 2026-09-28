module

public import Zeta2Lean.Window.Statements

@[expose] public section

/-!
# Zeta2Lean.Window.Assembly — the main theorem from the statements (complete, no gaps)

`main_of_stmts : Stmt_ZetaReal → Stmt_Criterion → Stmt_LinearForm → Stmt_Lemma19 →
  Stmt_DenomGrowth → Stmt_L20Upper → Stmt_AuxPrime → MainStatement`.

This is JTNB Proposition 5 for the window configuration `cfgW`, with the nonvanishing of `F̃_n`
supplied arithmetically (route R2 of docs/proof.md §6; docs/proof.md §3).  Suppose
`ζ(7), …, ζ(21)` were all rational, `ζ(s) = q_s`.
1. By `Stmt_LinearForm`, `F̃_n = -A₀ + ∑_{s ∈ window} A_s ζ(s) = -A₀ + ∑_s A_s q_s`.
2. **Nonvanishing** (`Fn_frequently_ne_zero`).  Dirichlet's theorem (`auxPrime_frequently`, primes
   `≡ -1 (mod 126)`) gives infinitely many even `n` with `ℓ = 63n - 1` prime; for those that are
   large enough, `Stmt_AuxPrime` gives `v_ℓ(A₀) < 0 ≤ v_ℓ(A_s)`, and `ℓ` exceeds every
   denominator of the `q_s`, so `v_ℓ(q_s) ≥ 0`.  Then `-A₀ + ∑_s A_s q_s ≠ 0`
   (`neg_add_sum_ne_zero`: otherwise `A₀ = ∑_s A_s q_s` would have valuation `≥ 0`).  Hence
   `F̃_n ≠ 0` infinitely often.
3. By `Stmt_Lemma19`, `Δ_n A₀, Δ_n A_s ∈ ℤ`; by `Stmt_DenomGrowth` and `Stmt_L20Upper`,
   `Δ_n |F̃_n| ≤ e^{(748 - 748.1) n} → 0`.  `Stmt_Criterion` turns 1–3 into a contradiction with the
   rationality assumption, and `Stmt_ZetaReal` translates `zetaR` into Mathlib's `riemannZeta`.

Informally (docs/proof.md §3) the integer `d Δ_n F̃_n` is non-zero because its `ℓ`-adic valuation is
`v_ℓ(Δ_n) - 5`; step 2 is the same argument before multiplying by `d Δ_n`.
-/

open Filter Topology Finset

noncomputable section

namespace ZetaWindow

/-- The zeta indices of the window form part of the range `r ≤ s ≤ q - 1` of `Stmt_Lemma19`. -/
theorem window_cfgW_subset : ∀ s ∈ window cfgW, s ∈ Icc cfgW.r (cfgW.q - 1) := by
  intro s hs
  rw [window_cfgW] at hs
  simp only [Finset.mem_insert, Finset.mem_singleton] at hs
  simp only [cfgW, Finset.mem_Icc]
  omega

namespace AssemblyAux

/-- **Dirichlet's theorem** for the auxiliary primes: there are infinitely many even `n` with
`63 n - 1` prime (the primes `p ≡ 125 (mod 126)`, `n = (p + 1)/63`). -/
theorem auxPrime_frequently : ∃ᶠ n : ℕ in atTop, Even n ∧ (63 * n - 1).Prime := by
  rw [Filter.frequently_atTop]
  intro N
  obtain ⟨p, hpN, hp, hmod⟩ :=
    Nat.forall_exists_prime_gt_and_modEq (126 * N) (q := 126) (a := 125) (by norm_num) (by norm_num)
  have h125 : p % 126 = 125 := hmod
  refine ⟨(p + 1) / 63, by omega, ⟨(p + 1) / 126, by omega⟩, ?_⟩
  have hp' : 63 * ((p + 1) / 63) - 1 = p := by omega
  rw [hp']
  exact hp

/-- A rational whose denominator is prime to `ℓ` has non-negative `ℓ`-adic valuation. -/
theorem padicValRat_nonneg_of_not_dvd_den {ℓ : ℕ} {x : ℚ} (h : ¬ ℓ ∣ x.den) :
    0 ≤ padicValRat ℓ x := by
  rw [padicValRat_def, padicValNat.eq_zero_of_not_dvd h]
  simp

/-- Non-negative `ℓ`-adic valuation is stable under products. -/
theorem padicValRat_mul_nonneg {ℓ : ℕ} [Fact ℓ.Prime] {x y : ℚ} (hx : 0 ≤ padicValRat ℓ x)
    (hy : 0 ≤ padicValRat ℓ y) : 0 ≤ padicValRat ℓ (x * y) := by
  rcases eq_or_ne x 0 with rfl | hx0
  · simp
  rcases eq_or_ne y 0 with rfl | hy0
  · simp
  rw [padicValRat.mul hx0 hy0]
  omega

/-- Non-negative `ℓ`-adic valuation is stable under finite sums. -/
theorem padicValRat_sum_nonneg {ℓ : ℕ} [Fact ℓ.Prime] {ι : Type*} (S : Finset ι) (f : ι → ℚ)
    (hf : ∀ i ∈ S, 0 ≤ padicValRat ℓ (f i)) : 0 ≤ padicValRat ℓ (∑ i ∈ S, f i) := by
  classical
  induction S using Finset.induction_on with
  | empty => simp
  | insert a S ha ih =>
    rw [Finset.sum_insert ha]
    by_cases h0 : f a + ∑ i ∈ S, f i = 0
    · rw [h0]
      simp
    · exact le_trans (le_min (hf a (Finset.mem_insert_self a S))
        (ih fun i hi => hf i (Finset.mem_insert_of_mem hi)))
        (padicValRat.min_le_padicValRat_add h0)

/-- **The `ℓ`-adic separation** (docs/proof.md §3, step 2): if `v_ℓ(a₀) < 0 ≤ v_ℓ(a_s)` and
`v_ℓ(q_s) ≥ 0` for all `s ∈ S`, then `-a₀ + ∑_s a_s q_s ≠ 0`. -/
theorem neg_add_sum_ne_zero {ℓ : ℕ} [Fact ℓ.Prime] (S : Finset ℕ) (a0 : ℚ) (a q : ℕ → ℚ)
    (h0 : padicValRat ℓ a0 < 0) (ha : ∀ s ∈ S, 0 ≤ padicValRat ℓ (a s))
    (hq : ∀ s ∈ S, 0 ≤ padicValRat ℓ (q s)) : -a0 + ∑ s ∈ S, a s * q s ≠ 0 := by
  intro h
  have hsum : 0 ≤ padicValRat ℓ (∑ s ∈ S, a s * q s) :=
    padicValRat_sum_nonneg S _ fun s hs => padicValRat_mul_nonneg (ha s hs) (hq s hs)
  have heq : a0 = ∑ s ∈ S, a s * q s := by linarith
  rw [← heq] at hsum
  omega

end AssemblyAux

open AssemblyAux in
/-- **Nonvanishing under the rationality hypothesis** (docs/proof.md §3, step 2): if the window
values `zetaR s` are all rational, then `F̃_n ≠ 0` for infinitely many `n` (namely for the large
even `n` with `63 n - 1` prime). -/
theorem Fn_frequently_ne_zero (hLF : Stmt_LinearForm) (hA : Stmt_AuxPrime)
    (hrat : ∀ s ∈ window cfgW, ∃ q : ℚ, zetaR s = q) : ∃ᶠ n in atTop, Fn cfgW n ≠ 0 := by
  choose! q hq using hrat
  -- a common bound `d` for the denominators of the `q_s`
  set d : ℕ := ∏ s ∈ window cfgW, (q s).den with hd
  have hdpos : 0 < d := Finset.prod_pos fun s _ => (q s).den_pos
  refine (auxPrime_frequently.and_eventually (hA.and (eventually_gt_atTop d))).mono ?_
  rintro n ⟨⟨hev, hprime⟩, hsep, hnd⟩
  have := Fact.mk hprime
  obtain ⟨hA0, hAs⟩ := hsep hev hprime
  have hF : Fn cfgW n = -(A0 cfgW n : ℝ) + ∑ s ∈ window cfgW, (Acoef cfgW n s : ℝ) * zetaR s :=
    (hLF cfgW admissible_cfgW n (by omega)).tsum_eq
  -- `ℓ = 63 n - 1 > d ≥ den q_s`, so `v_ℓ(q_s) ≥ 0`
  have hq' : ∀ s ∈ window cfgW, 0 ≤ padicValRat (63 * n - 1) (q s) := by
    intro s hs
    apply padicValRat_nonneg_of_not_dvd_den
    have hle : (q s).den ≤ d := Nat.le_of_dvd hdpos (Finset.dvd_prod_of_mem _ hs)
    exact Nat.not_dvd_of_pos_of_lt (q s).den_pos (by omega)
  have hne := neg_add_sum_ne_zero (window cfgW) (A0 cfgW n) (Acoef cfgW n) q hA0 hAs hq'
  rw [hF]
  have hcast : -(A0 cfgW n : ℝ) + ∑ s ∈ window cfgW, (Acoef cfgW n s : ℝ) * zetaR s =
      ((-A0 cfgW n + ∑ s ∈ window cfgW, Acoef cfgW n s * q s : ℚ) : ℝ) := by
    push_cast
    congr 1
    exact Finset.sum_congr rfl fun s hs => by rw [hq s hs]
  rw [hcast]
  exact_mod_cast hne

/-- **Main theorem from the statements** (JTNB Proposition 5 with `r = 5`, `q = 23`; nonvanishing
from the auxiliary primes). -/
theorem main_of_stmts (hZ : Stmt_ZetaReal) (hC : Stmt_Criterion) (hLF : Stmt_LinearForm)
    (hL19 : Stmt_Lemma19) (hG : Stmt_DenomGrowth) (hU : Stmt_L20Upper)
    (hA : Stmt_AuxPrime) : MainStatement := by
  have hadm := admissible_cfgW
  have hn1 : ∀ᶠ n : ℕ in atTop, 1 ≤ n := eventually_ge_atTop 1
  intro hall
  -- under the assumption, the window values `zetaR s` are rational
  have hrat : ∀ s ∈ window cfgW, ∃ q : ℚ, zetaR s = q := by
    intro s hs
    have hs' := hs
    rw [window_cfgW] at hs'
    obtain ⟨q, hq⟩ := hall s hs'
    have h2 : 2 ≤ s := by
      simp only [Finset.mem_insert, Finset.mem_singleton] at hs'
      omega
    refine ⟨q, ?_⟩
    rw [hZ s h2] at hq
    exact_mod_cast hq
  -- the criterion, with the nonvanishing from the auxiliary primes
  refine hC (window cfgW) zetaR (Delta cfgW) (A0 cfgW) (Acoef cfgW) (Fn cfgW)
    (C2hi : ℝ) (C0lo : ℝ) ?_ (Eventually.of_forall fun n => Delta_pos cfgW n) ?_ ?_ ?_
    hG hU (Fn_frequently_ne_zero hLF hA hrat) hrat
  · norm_num [C2hi, C0lo]
  · filter_upwards [hn1] with n hn
    exact (hLF cfgW hadm n hn).tsum_eq
  · filter_upwards [hn1] with n hn
    exact (hL19 cfgW hadm n hn).1
  · filter_upwards [hn1] with n hn
    intro s hs
    exact (hL19 cfgW hadm n hn).2 s (window_cfgW_subset s hs)

end ZetaWindow

end
