module

public import Zeta2Lean.Window.Statements

@[expose] public section

set_option linter.style.header false
set_option linter.style.longLine false

/-!
# Vanishing sums: symmetry and the residue sum (JTNB (8.3), (8.5), p. 282)

**Theorem.** `Stmt_CoeffVanish` from `Stmt_PF`:
* `symm`: `B c n j (h₀ - k) = (-1)^j B c n j k` for `r+1 ≤ j ≤ q`, `k ∈ Krange`;
* `ressum`: `∑_{k ∈ Krange} B c n (r+1) k = 0`.

**Proof of `symm` (as formalised; `Stmt_PF` is not needed).**  Write `ρ = rescale (-1)` (the ring
hom `ε ↦ -ε`; it fixes constants, `rescale_C`, and commutes with `⁻¹`, `rescale_inv`).  The key
identity is `G_{h₀-k} = -ρ(G_k)` for every `k ≤ h₀` (`Gk_reflect`; this is JTNB (8.5),
`R̃(-t-h₀) = -R̃(t)`, brick by brick).  All bricks are products of linear factors `i - k + ε`,
and the reflection `i ↦ h₀ - i` gives `i - (h₀-k) + ε = -ρ((h₀-i) - k + ε)` (`prod_reflect`):
* the linear factor: `(h₀ - 2(h₀-k)) + 2ε = -ρ((h₀-2k) + 2ε)` (`lin_reflect`);
* the polynomial bricks: `polyBrick a b (h₀-k) = (-1)^{a-b} ρ(polyBrick (h₀+1-b) (h₀+1-a) k)`
  (`polyBrick_reflect`), so `P_j(h₀-k) = (-1)^{h_j-1} ρ Q_j(k)` and `Q_j(h₀-k) = (-1)^{h_j-1} ρ P_j(k)`,
  and `P_j Q_j` is invariant (`PQ_reflect`);
* the rational bricks (`a = h_j`, `b = h₀-h_j+1`, so `a + b = h₀ + 1` and `Ico a b` is mapped onto
  itself): `ratBrick a b (h₀-k) = (-1)^{b-a-1} ρ(ratBrick a b k)` (`ratBrick_reflect`).  In the
  `if` branch (`a ≤ k < b`, equivalently `a ≤ h₀-k < b`) the reflection maps
  `(Ico a b).erase (h₀-k)` onto `(Ico a b).erase k`; in the `else` branch the `b-a` factors give
  `(-1)^{b-a}` and `ρ X = -X` gives the missing `-1`.  Here `b-a-1 = h₀-2h_j ≡ h₀ (mod 2)`
  (`neg_one_pow_ratBrick`);
* total sign: `-((-1)^{h₀})^{q-r} = -1` because `q - r` is even (`r`, `q` odd).
Then `B_{j,h₀-k} = [ε^{q-j}](-ρ G_k) = -(-1)^{q-j} B_{j,k} = (-1)^j B_{j,k}` (`q` odd).
From `Admissible` only `r_odd`, `q_odd`, `eta_mono`, `two_eta_lt` (for `2h_j ≤ h₀`) are used;
`k ∈ Krange` is used only through `k ≤ h₀`, and `1 ≤ n` is not used.

**Proof of `ressum` (as formalised).**  The sum of the residues vanishes because `deg R̃ ≤ -2`.
1. Constant coefficients of `Stmt_PF` at `y = m ∈ ℕ` (not a pole: `m + k ≥ 1`) give
   `R̃(m) = ∑_{j,k} B_{j,k} (m+k)^{-(j-r)}` in `ℚ` (`constantCoeff_Rser`, `constantCoeff_PF`).
2. `m R̃(m) = P(m)/Q(m)` with `P = N_h X (2X + h₀) (∏_{i=1}^{h₀-1} (X+i))^r` and
   `Q = ∏_{j=1}^{q} ∏_{i=h_j}^{h₀-h_j} (X+i)` in `ℝ[X]`; `deg P ≤ 2 + r(h₀-1) < deg Q`
   (`deg_count`: this is (8.1) = `Admissible.deg_cond`, together with `r + 4 ≤ q`), so
   `m R̃(m) → 0` (`Polynomial.div_tendsto_atTop_zero_of_degree_lt`).
3. `m (m+k)^{-e} → [e = 1]` for `e ≥ 1` (`tendsto_div_add_pow`), so
   `m ∑_{j,k} B_{j,k} (m+k)^{-(j-r)} → ∑_k B_{r+1,k}`.
4. Uniqueness of limits gives `∑_k B_{r+1,k} = 0`.
From `Admissible` only `deg_cond`, `r_add_four_le_q`, `eta_mono`, `two_eta_lt` are used directly
(plus whatever `Stmt_PF` needs).

**Numerical check.** `python/window_mirror.py`, section "Laurent data …": `symm` for all `j, k`,
`ressum`, and the resulting set of `s` with `A_s ≠ 0` equals `window c` (exact; `cfgW` `n = 1, 2`,
Theorem 3 configuration `n = 1, 2, 3`).

**Status: done** (complete, no gaps; `#print axioms CoeffVanish_proof`: propext, Classical.choice,
Quot.sound; `Stmt_PF` enters only as the hypothesis `hPF`).
-/

open Filter Topology Finset PowerSeries

noncomputable section

namespace ZetaWindow

namespace CoeffVanish

/-! ### `symm`: the reflection `k ↦ h₀ - k` -/

/-- `rescale a` fixes constants. -/
theorem rescale_C (a r : ℚ) : rescale a (C r) = C r := by
  ext m
  rw [coeff_rescale, coeff_C]
  split_ifs with h
  · subst h
    simp
  · simp

/-- `rescale a` commutes with the power-series inverse (both sides are `0` when the constant
coefficient vanishes). -/
theorem rescale_inv (a : ℚ) (φ : PowerSeries ℚ) : rescale a φ⁻¹ = (rescale a φ)⁻¹ := by
  have hc : constantCoeff (rescale a φ) = constantCoeff φ := by
    rw [← coeff_zero_eq_constantCoeff_apply, coeff_rescale, pow_zero, one_mul,
      coeff_zero_eq_constantCoeff_apply]
  by_cases h : constantCoeff φ = 0
  · rw [PowerSeries.inv_eq_zero.mpr h, map_zero, PowerSeries.inv_eq_zero.mpr (hc.trans h)]
  · rw [PowerSeries.eq_inv_iff_mul_eq_one (hc ▸ h), ← map_mul, PowerSeries.inv_mul_cancel φ h,
      map_one]

/-- `((-1)^m φ)⁻¹ = (-1)^m φ⁻¹`. -/
theorem inv_neg_one_pow_mul (m : ℕ) (φ : PowerSeries ℚ) :
    ((-1 : PowerSeries ℚ) ^ m * φ)⁻¹ = (-1) ^ m * φ⁻¹ := by
  rw [PowerSeries.mul_inv_rev, mul_comm]
  congr 1
  symm
  rw [PowerSeries.eq_inv_iff_mul_eq_one]
  · rw [← mul_pow, neg_one_mul, neg_neg, one_pow]
  · rw [map_pow, map_neg, map_one]
    exact pow_ne_zero _ (neg_ne_zero.mpr one_ne_zero)

/-- The reflection `i ↦ h₀ - i` on a product of linear factors: if it maps `s` onto `t` (both in
`[0, h₀]`), then `∏_{i ∈ s} (i - (h₀-k) + ε) = (-1)^{#s} ρ(∏_{i ∈ t} (i - k + ε))`. -/
theorem prod_reflect {h0 k : ℕ} (hk : k ≤ h0) (s t : Finset ℕ) (hs : ∀ i ∈ s, i ≤ h0)
    (ht : ∀ i ∈ t, i ≤ h0) (hst : ∀ i ∈ s, h0 - i ∈ t) (hts : ∀ i ∈ t, h0 - i ∈ s) :
    ∏ i ∈ s, (C ((i : ℚ) - ((h0 - k : ℕ) : ℚ)) + X : PowerSeries ℚ) =
      (-1) ^ s.card * rescale (-1 : ℚ) (∏ i ∈ t, (C ((i : ℚ) - k) + X)) := by
  have h1 : ∀ i ∈ s, (C ((i : ℚ) - ((h0 - k : ℕ) : ℚ)) + X : PowerSeries ℚ) =
      -(rescale (-1 : ℚ) (C (((h0 - i : ℕ) : ℚ) - k) + X)) := by
    intro i hi
    have hi' : i ≤ h0 := hs i hi
    rw [map_add, rescale_C, rescale_neg_one_X, Nat.cast_sub hk, Nat.cast_sub hi', neg_add,
      neg_neg, ← map_neg]
    congr 2
    ring
  rw [Finset.prod_congr rfl h1, Finset.prod_neg, map_prod]
  congr 1
  refine Finset.prod_nbij' (fun i => h0 - i) (fun i => h0 - i) hst hts ?_ ?_ ?_
  · intro i hi
    have := hs i hi
    omega
  · intro i hi
    have := ht i hi
    omega
  · intro i _
    rfl

/-- Reflection of a polynomial brick: `P_{a,b}(h₀-k) = (-1)^{a-b} ρ(P_{a',b'}(k))` with
`a' = h₀+1-b`, `b' = h₀+1-a`. -/
theorem polyBrick_reflect {h0 k a b a' b' : ℕ} (hk : k ≤ h0) (hba : b ≤ a) (ha : a ≤ h0 + 1)
    (ha' : a' + b = h0 + 1) (hb' : b' + a = h0 + 1) :
    polyBrick a b (h0 - k) = (-1) ^ (a - b) * rescale (-1 : ℚ) (polyBrick a' b' k) := by
  unfold polyBrick
  rw [prod_reflect hk (Ico b a) (Ico b' a'), Nat.card_Ico, map_mul, rescale_C]
  · have : a' - b' = a - b := by omega
    rw [this]
    ring
  · intro i hi
    rw [Finset.mem_Ico] at hi
    omega
  · intro i hi
    rw [Finset.mem_Ico] at hi
    omega
  · intro i hi
    rw [Finset.mem_Ico] at hi ⊢
    omega
  · intro i hi
    rw [Finset.mem_Ico] at hi ⊢
    omega

/-- Reflection of a rational brick with `a + b = h₀ + 1`:
`S_{a,b}(h₀-k) = (-1)^{b-a-1} ρ(S_{a,b}(k))` (both branches of `ratBrick`). -/
theorem ratBrick_reflect {h0 k a b : ℕ} (hk : k ≤ h0) (hab : a < b) (hsum : a + b = h0 + 1) :
    ratBrick a b (h0 - k) = (-1) ^ (b - a - 1) * rescale (-1 : ℚ) (ratBrick a b k) := by
  unfold ratBrick
  by_cases hin : a ≤ k ∧ k < b
  · have hin' : a ≤ h0 - k ∧ h0 - k < b := by omega
    rw [ite_eq_left hin, ite_eq_left hin']
    rw [prod_reflect hk ((Ico a b).erase (h0 - k)) ((Ico a b).erase k)]
    · rw [Finset.card_erase_of_mem (Finset.mem_Ico.mpr hin'), Nat.card_Ico, inv_neg_one_pow_mul,
        map_mul, rescale_C, rescale_inv]
      ring
    · intro i hi
      rw [Finset.mem_erase, Finset.mem_Ico] at hi
      omega
    · intro i hi
      rw [Finset.mem_erase, Finset.mem_Ico] at hi
      omega
    · intro i hi
      rw [Finset.mem_erase, Finset.mem_Ico] at hi ⊢
      omega
    · intro i hi
      rw [Finset.mem_erase, Finset.mem_Ico] at hi ⊢
      omega
  · have hin' : ¬ (a ≤ h0 - k ∧ h0 - k < b) := by omega
    rw [ite_eq_right hin, ite_eq_right hin']
    rw [prod_reflect hk (Ico a b) (Ico a b)]
    · rw [Nat.card_Ico, inv_neg_one_pow_mul, map_mul, map_mul, rescale_C, rescale_inv,
        rescale_neg_one_X]
      have hp : (-1 : PowerSeries ℚ) ^ (b - a) = (-1) ^ (b - a - 1) * (-1) := by
        rw [← pow_succ]
        congr 1
        omega
      rw [hp]
      ring
    · intro i hi
      rw [Finset.mem_Ico] at hi
      omega
    · intro i hi
      rw [Finset.mem_Ico] at hi
      omega
    · intro i hi
      rw [Finset.mem_Ico] at hi ⊢
      omega
    · intro i hi
      rw [Finset.mem_Ico] at hi ⊢
      omega

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

/-- `1 ≤ h_i`. -/
theorem one_le_h (c : Config) (n i : ℕ) : 1 ≤ c.h n i := by
  unfold Config.h
  omega

/-- The linear factor: `(h₀ - 2(h₀-k)) + 2ε = -ρ((h₀-2k) + 2ε)`. -/
theorem lin_reflect {h0 k : ℕ} (hk : k ≤ h0) :
    (C ((h0 : ℚ) - 2 * ((h0 - k : ℕ) : ℚ)) + C 2 * X : PowerSeries ℚ) =
      -rescale (-1 : ℚ) (C ((h0 : ℚ) - 2 * k) + C 2 * X) := by
  rw [map_add, map_mul, rescale_C, rescale_C, rescale_neg_one_X, Nat.cast_sub hk]
  have : (C ((h0 : ℚ) - 2 * ((h0 : ℚ) - k)) : PowerSeries ℚ) = -C ((h0 : ℚ) - 2 * k) := by
    rw [← map_neg]
    congr 1
    ring
  rw [this]
  ring

/-- The pair `P_j Q_j` is invariant: `P_j(h₀-k) Q_j(h₀-k) = ρ(P_j(k) Q_j(k))` (`1 ≤ h_j ≤ h₀`). -/
theorem PQ_reflect {h0 k hj : ℕ} (hk : k ≤ h0) (h1 : 1 ≤ hj) (h2 : hj ≤ h0) :
    polyBrick hj 1 (h0 - k) * polyBrick h0 (h0 - hj + 1) (h0 - k) =
      rescale (-1 : ℚ) (polyBrick hj 1 k * polyBrick h0 (h0 - hj + 1) k) := by
  rw [polyBrick_reflect (a' := h0) (b' := h0 - hj + 1) hk h1 (by omega) (by omega) (by omega),
    polyBrick_reflect (a' := hj) (b' := 1) hk (by omega) (by omega) (by omega) (by omega),
    map_mul]
  have e : h0 - (h0 - hj + 1) = hj - 1 := by omega
  rw [e]
  have hsq : ((-1 : PowerSeries ℚ) ^ (hj - 1)) * (-1) ^ (hj - 1) = 1 := by
    rw [← mul_pow, neg_one_mul, neg_neg, one_pow]
  linear_combination (rescale (-1 : ℚ) (polyBrick hj 1 k) *
    rescale (-1 : ℚ) (polyBrick h0 (h0 - hj + 1) k)) * hsq

/-- The sign of a rational brick is `(-1)^{h₀-2h_j} = (-1)^{h₀}`. -/
theorem neg_one_pow_ratBrick {h0 hj : ℕ} (h : 2 * hj ≤ h0) :
    (-1 : PowerSeries ℚ) ^ (h0 - hj + 1 - hj - 1) = (-1) ^ h0 := by
  have e : h0 = (h0 - hj + 1 - hj - 1) + 2 * hj := by omega
  conv_rhs => rw [e]
  rw [pow_add, pow_mul, neg_one_sq, one_pow, mul_one]

/-- **The reflection of `G_k`** (JTNB (8.5), `R̃(-t-h₀) = -R̃(t)`): `G_{h₀-k}(ε) = -G_k(-ε)` for
every `k ≤ h₀`. -/
theorem Gk_reflect {c : Config} (hc : Admissible c) (n : ℕ) {k : ℕ} (hk : k ≤ c.h0 n) :
    Gk c n (c.h0 n - k) = -rescale (-1 : ℚ) (Gk c n k) := by
  have hrq : c.r + 4 ≤ c.q := hc.r_add_four_le_q
  unfold Gk
  rw [lin_reflect hk]
  have hP : ∀ j ∈ Icc 1 c.r,
      polyBrick (c.h n j) 1 (c.h0 n - k) * polyBrick (c.h0 n) (c.h0 n - c.h n j + 1) (c.h0 n - k) =
        rescale (-1 : ℚ) (polyBrick (c.h n j) 1 k * polyBrick (c.h0 n) (c.h0 n - c.h n j + 1) k) := by
    intro j hj
    have hj' := Finset.mem_Icc.mp hj
    have := two_h_le hc n hj'.1 (by omega)
    exact PQ_reflect hk (one_le_h c n j) (by omega)
  have hS : ∀ j ∈ Icc (c.r + 1) c.q,
      ratBrick (c.h n j) (c.h0 n - c.h n j + 1) (c.h0 n - k) =
        (-1) ^ c.h0 n * rescale (-1 : ℚ) (ratBrick (c.h n j) (c.h0 n - c.h n j + 1) k) := by
    intro j hj
    have hj' := Finset.mem_Icc.mp hj
    have h2 := two_h_le hc n (by omega) hj'.2
    rw [ratBrick_reflect hk (by omega) (by omega), neg_one_pow_ratBrick h2]
  rw [Finset.prod_congr rfl hP, Finset.prod_congr rfl hS, Finset.prod_mul_distrib,
    Finset.prod_const, Nat.card_Icc]
  have heven : Even (c.q + 1 - (c.r + 1)) := by
    rw [Nat.add_sub_add_right]
    exact Nat.Odd.sub_odd hc.q_odd hc.r_odd
  have hsign : ((-1 : PowerSeries ℚ) ^ c.h0 n) ^ (c.q + 1 - (c.r + 1)) = 1 := by
    rw [← pow_mul, mul_comm, pow_mul, heven.neg_one_pow, one_pow]
  rw [hsign, one_mul]
  simp only [map_mul, map_prod]
  ring

/-- **`symm`**: `B_{j,h₀-k} = (-1)^j B_{j,k}`. -/
theorem B_symm (c : Config) (hc : Admissible c) (n : ℕ) (_hn : 1 ≤ n) (j k : ℕ)
    (hj : j ∈ Icc (c.r + 1) c.q) (hk : k ∈ Krange c n) :
    B c n j (c.h0 n - k) = (-1) ^ j * B c n j k := by
  have hk' : k ≤ c.h0 n := by
    unfold Krange at hk
    rw [Finset.mem_Icc] at hk
    omega
  have hjq : j ≤ c.q := (Finset.mem_Icc.mp hj).2
  unfold B
  rw [Gk_reflect hc n hk', map_neg, coeff_rescale]
  rcases Nat.even_or_odd j with hje | hjo
  · have : Odd (c.q - j) := Nat.Odd.sub_even hjq hc.q_odd hje
    rw [this.neg_one_pow, hje.neg_one_pow]
    ring
  · have : Even (c.q - j) := Nat.Odd.sub_odd hc.q_odd hjo
    rw [this.neg_one_pow, hjo.neg_one_pow]
    ring

/-! ### `ressum`: the sum of the residues vanishes (`deg R̃ ≤ -2`) -/

/-- The constant coefficient of `Rser c n y`: the value `R̃(y)`. -/
theorem constantCoeff_Rser (c : Config) (n : ℕ) (y : ℚ) :
    constantCoeff (Rser c n y) = Nh c n * ((c.h0 n : ℚ) + 2 * y) *
      (∏ i ∈ Ico 1 (c.h0 n), (y + i)) ^ c.r *
      (∏ j ∈ Icc 1 c.q, ∏ i ∈ Icc (c.h n j) (c.h0 n - c.h n j), (y + i))⁻¹ := by
  unfold Rser
  simp only [map_mul, map_pow, map_prod, map_add, constantCoeff_C, constantCoeff_X,
    PowerSeries.constantCoeff_inv, mul_zero, add_zero]

/-- The constant coefficient of the partial-fraction side of `Stmt_PF`. -/
theorem constantCoeff_PF (c : Config) (n : ℕ) (y : ℚ) :
    constantCoeff (∑ j ∈ Icc (c.r + 1) c.q, ∑ k ∈ Krange c n,
      C (B c n j k) * ((C (y + k) + X) ^ (j - c.r))⁻¹) =
    ∑ j ∈ Icc (c.r + 1) c.q, ∑ k ∈ Krange c n, B c n j k * ((y + k) ^ (j - c.r))⁻¹ := by
  simp only [map_sum, map_mul, map_pow, map_add, constantCoeff_C, constantCoeff_X,
    PowerSeries.constantCoeff_inv, add_zero]

/-- `m / (m + x)^e → [e = 1]` as `m → ∞`, for `e ≥ 1`. -/
theorem tendsto_div_add_pow (x : ℝ) {e : ℕ} (he : 1 ≤ e) :
    Tendsto (fun m : ℕ => (m : ℝ) / ((m : ℝ) + x) ^ e) atTop (𝓝 (if e = 1 then 1 else 0)) := by
  split_ifs with h
  · subst h
    simpa using tendsto_natCast_div_add_atTop x
  · have hdeg : (Polynomial.X : Polynomial ℝ).degree <
        ((Polynomial.X + Polynomial.C x) ^ e).degree := by
      apply Polynomial.degree_lt_degree
      rw [(Polynomial.monic_X_add_C x).natDegree_pow, Polynomial.natDegree_X_add_C,
        Polynomial.natDegree_X]
      omega
    have := (Polynomial.div_tendsto_atTop_zero_of_degree_lt _ _ hdeg).comp
      tendsto_natCast_atTop_atTop
    refine this.congr (fun m => ?_)
    simp [Polynomial.eval_pow]

/-- The degree count behind `deg R̃ ≤ -2` (JTNB (8.1) = `Admissible.deg_cond`, and `r + 4 ≤ q`):
`2 + r (h₀ - 1) < ∑_{j=1}^{q} #[h_j, h₀-h_j]` (numerator degree of `m R̃(m)` versus denominator
degree; `1 ≤ n` is not needed). -/
theorem deg_count {c : Config} (hc : Admissible c) (n : ℕ) :
    2 + c.r * (c.h0 n - 1) < ∑ j ∈ Icc 1 c.q, (c.h0 n - c.h n j + 1 - c.h n j) := by
  have hterm : ∀ j ∈ Icc 1 c.q,
      (c.h0 n - c.h n j + 1 - c.h n j) + 2 * (n * c.eta j) = c.eta0 * n + 1 := by
    intro j hj
    have h2 := two_h_le hc n (Finset.mem_Icc.1 hj).1 (Finset.mem_Icc.1 hj).2
    unfold Config.h0 Config.h at *
    have e : n * c.eta j = c.eta j * n := Nat.mul_comm _ _
    omega
  have hsum : ∑ j ∈ Icc 1 c.q, (c.h0 n - c.h n j + 1 - c.h n j) +
      2 * (n * ∑ j ∈ Icc 1 c.q, c.eta j) = c.q * (c.eta0 * n + 1) := by
    rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib, Finset.sum_congr rfl hterm,
      Finset.sum_const, Nat.card_Icc, smul_eq_mul, Nat.add_sub_cancel]
  have hdeg := hc.deg_cond
  have hrq := hc.r_add_four_le_q
  have h01 : c.h0 n - 1 = c.eta0 * n + 1 := by
    unfold Config.h0
    omega
  rw [h01]
  generalize ∑ j ∈ Icc 1 c.q, c.eta j = S at hsum hdeg
  generalize ∑ j ∈ Icc 1 c.q, (c.h0 n - c.h n j + 1 - c.h n j) = T at hsum ⊢
  obtain ⟨d, hd⟩ : ∃ d, c.q = c.r + 4 + d := ⟨c.q - (c.r + 4), by omega⟩
  rw [hd] at hsum hdeg
  rw [show c.r + 4 + d - c.r = 4 + d by omega] at hdeg
  have hdegn : (2 * S + 2 * c.r) * n ≤ (4 + d) * c.eta0 * n := Nat.mul_le_mul_right n hdeg
  nlinarith

/-- **`ressum`**: the sum of the residues vanishes, `∑_k B_{r+1,k} = 0` (JTNB (8.3)). -/
theorem B_ressum (hPF : Stmt_PF) (c : Config) (hc : Admissible c) (n : ℕ) (hn : 1 ≤ n) :
    ∑ k ∈ Krange c n, B c n (c.r + 1) k = 0 := by
  have hrq := hc.r_add_four_le_q
  -- Step 1: `R̃(m) = ∑_{j,k} B_{j,k} (m+k)^{-(j-r)}` for every `m ∈ ℕ` (constant coefficients).
  have key : ∀ m : ℕ, Nh c n * ((c.h0 n : ℚ) + 2 * m) *
      (∏ i ∈ Ico 1 (c.h0 n), ((m : ℚ) + i)) ^ c.r *
      (∏ j ∈ Icc 1 c.q, ∏ i ∈ Icc (c.h n j) (c.h0 n - c.h n j), ((m : ℚ) + i))⁻¹ =
      ∑ j ∈ Icc (c.r + 1) c.q, ∑ k ∈ Krange c n, B c n j k * (((m : ℚ) + k) ^ (j - c.r))⁻¹ := by
    intro m
    have hy : ∀ k ∈ Krange c n, (m : ℚ) + k ≠ 0 := by
      intro k hk
      unfold Krange at hk
      have h1 := (Finset.mem_Icc.mp hk).1
      have h2 : 1 ≤ c.h n 1 := one_le_h c n 1
      exact_mod_cast (show m + k ≠ 0 by omega)
    have h := congrArg constantCoeff (hPF c hc n hn (m : ℚ) hy)
    rw [constantCoeff_Rser, constantCoeff_PF] at h
    exact h
  -- Step 2: `m R̃(m) = P(m)/Q(m)` with `deg P < deg Q`, hence `m R̃(m) → 0`.
  set P : Polynomial ℝ := Polynomial.C (Nh c n : ℝ) *
    (Polynomial.X * (Polynomial.C 2 * Polynomial.X + Polynomial.C (c.h0 n : ℝ))) *
    (∏ i ∈ Ico 1 (c.h0 n), (Polynomial.X + Polynomial.C (i : ℝ))) ^ c.r with hP
  set Q : Polynomial ℝ := ∏ j ∈ Icc 1 c.q, ∏ i ∈ Icc (c.h n j) (c.h0 n - c.h n j),
    (Polynomial.X + Polynomial.C (i : ℝ)) with hQ
  have hQdeg : Q.natDegree = ∑ j ∈ Icc 1 c.q, (c.h0 n - c.h n j + 1 - c.h n j) := by
    rw [hQ, Polynomial.natDegree_prod_of_monic _ _ (fun j _ => Polynomial.monic_prod_of_monic _ _
      (fun i _ => Polynomial.monic_X_add_C _))]
    refine Finset.sum_congr rfl (fun j _ => ?_)
    rw [Polynomial.natDegree_prod_of_monic _ _ (fun i _ => Polynomial.monic_X_add_C _)]
    simp only [Polynomial.natDegree_X_add_C, Finset.sum_const, Nat.card_Icc, smul_eq_mul, mul_one]
  have hPdeg : P.natDegree ≤ 2 + c.r * (c.h0 n - 1) := by
    have hF : (∏ i ∈ Ico 1 (c.h0 n), (Polynomial.X + Polynomial.C (i : ℝ))).natDegree =
        c.h0 n - 1 := by
      rw [Polynomial.natDegree_prod_of_monic _ _ (fun i _ => Polynomial.monic_X_add_C _)]
      simp only [Polynomial.natDegree_X_add_C, Finset.sum_const, Nat.card_Ico, smul_eq_mul,
        mul_one]
    rw [hP]
    refine Polynomial.natDegree_mul_le.trans (add_le_add ?_ ?_)
    · refine (Polynomial.natDegree_C_mul_le _ _).trans ?_
      refine Polynomial.natDegree_mul_le.trans ?_
      have := Polynomial.natDegree_linear_le (a := (2 : ℝ)) (b := (c.h0 n : ℝ))
      rw [Polynomial.natDegree_X]
      omega
    · refine Polynomial.natDegree_pow_le.trans ?_
      rw [hF]
  have hPQ : P.degree < Q.degree :=
    Polynomial.degree_lt_degree (hPdeg.trans_lt (hQdeg ▸ deg_count hc n))
  have hL : Tendsto (fun m : ℕ => Polynomial.eval (m : ℝ) P / Polynomial.eval (m : ℝ) Q) atTop
      (𝓝 0) :=
    (Polynomial.div_tendsto_atTop_zero_of_degree_lt P Q hPQ).comp tendsto_natCast_atTop_atTop
  -- Step 3: `m ∑_{j,k} B_{j,k} (m+k)^{-(j-r)} → ∑_k B_{r+1,k}`.
  have hR : Tendsto (fun m : ℕ => ∑ j ∈ Icc (c.r + 1) c.q, ∑ k ∈ Krange c n,
      (B c n j k : ℝ) * ((m : ℝ) / ((m : ℝ) + k) ^ (j - c.r))) atTop
      (𝓝 (∑ j ∈ Icc (c.r + 1) c.q, ∑ k ∈ Krange c n,
        (B c n j k : ℝ) * (if j - c.r = 1 then 1 else 0))) := by
    refine tendsto_finsetSum _ (fun j hj => tendsto_finsetSum _ (fun k _ => ?_))
    have hj' := Finset.mem_Icc.mp hj
    exact (tendsto_div_add_pow (k : ℝ) (by omega)).const_mul _
  have hsum : ∑ j ∈ Icc (c.r + 1) c.q, ∑ k ∈ Krange c n,
      (B c n j k : ℝ) * (if j - c.r = 1 then 1 else 0) =
        ∑ k ∈ Krange c n, (B c n (c.r + 1) k : ℝ) := by
    rw [Finset.sum_eq_single (c.r + 1)]
    · simp
    · intro j hj hne
      have : j - c.r ≠ 1 := by
        have := Finset.mem_Icc.mp hj
        omega
      simp [this]
    · intro h
      exact absurd (Finset.mem_Icc.mpr ⟨le_rfl, by omega⟩) h
  rw [hsum] at hR
  -- Step 4: the two sequences agree (Step 1 times `m`), so the limits agree.
  have hfun : ∀ m : ℕ, Polynomial.eval (m : ℝ) P / Polynomial.eval (m : ℝ) Q =
      ∑ j ∈ Icc (c.r + 1) c.q, ∑ k ∈ Krange c n,
        (B c n j k : ℝ) * ((m : ℝ) / ((m : ℝ) + k) ^ (j - c.r)) := by
    intro m
    have h := congrArg (fun q : ℚ => (q : ℝ)) (key m)
    push_cast at h
    have e1 : ∑ j ∈ Icc (c.r + 1) c.q, ∑ k ∈ Krange c n,
        (B c n j k : ℝ) * ((m : ℝ) / ((m : ℝ) + k) ^ (j - c.r)) =
        (m : ℝ) * ∑ j ∈ Icc (c.r + 1) c.q, ∑ k ∈ Krange c n,
          (B c n j k : ℝ) * (((m : ℝ) + k) ^ (j - c.r))⁻¹ := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl (fun j _ => ?_)
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl (fun k _ => ?_)
      rw [div_eq_mul_inv]
      ring
    rw [e1, ← h, hP, hQ]
    simp only [Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_X, Polynomial.eval_add,
      Polynomial.eval_pow, Polynomial.eval_prod]
    rw [div_eq_mul_inv]
    ring
  have hlim := tendsto_nhds_unique (hL.congr hfun) hR
  exact_mod_cast hlim.symm

end CoeffVanish

theorem CoeffVanish_proof (hPF : Stmt_PF) : Stmt_CoeffVanish := by
  exact ⟨CoeffVanish.B_symm, CoeffVanish.B_ressum hPF⟩

end ZetaWindow

end

