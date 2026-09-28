import Zeta2Lean.Window.Statements

set_option linter.style.header false
set_option linter.style.longLine false

/-!
# p-adic refinement for the Laurent coefficients (JTNB (8.11))

**Theorem.** `Stmt_LaurentVal` from `Stmt_BrickVal`: for admissible `c`, `n ≥ 1`, a prime `p` with
`h₀ < p²`, `r+1 ≤ j ≤ q`, `k ∈ Krange`, `B c n j k ≠ 0`:
`omegaKP c n p k - (q - j) ≤ v_p(B c n j k)`.

**Informal proof.**  Call `f ∈ ℚ⟦ε⟧` *`w`-tame* if `[ε^i] f ≠ 0 → w - i ≤ v_p([ε^i] f)` for all `i`;
products of tame series are tame with the weights added (ultrametric inequality on the Cauchy
product).  With `N = h₀` (all of `h_i, h₀ - h_i + 1, k` are `≤ h₀` and `h₀ < p²`) every factor of
`Gk c n k` is tame, by `Stmt_BrickVal` for the bricks:
* `C(h₀-2k) + 2X` is `0`-tame (its coefficients `h₀-2k` and `2` are integers);
* `P_i = polyBrick h_i 1 k`: weight `wPoly h_i 1 k p = ⌊(k-1)/p⌋ - ⌊(k-h_i)/p⌋ - ⌊(h_i-1)/p⌋`;
* `Q_i = polyBrick h₀ (h₀-h_i+1) k`: weight
  `wPoly h₀ (h₀-h_i+1) k p = ⌊(k-h₀+h_i-1)/p⌋ - ⌊(k-h₀)/p⌋ - ⌊(h_i-1)/p⌋`
  `= ⌊(h₀-k-1)/p⌋ - ⌊(h₀-h_i-k)/p⌋ - ⌊(h_i-1)/p⌋` (JTNB (7.5) twice: `⌊-x/p⌋ = -⌊(x-1)/p⌋ - 1`);
* `ε S_i = ratBrick h_i (h₀-h_i+1) k`: weight `wRat … = ⌊(h₀-2h_i)/p⌋ - ⌊(k-h_i)/p⌋ - ⌊(h₀-h_i-k)/p⌋`.
The weights add up to `omegaKP c n p k` **exactly** (JTNB (8.9), term by term), so `Gk c n k` is
`ω_{k,p}`-tame and `[ε^{q-j}] Gk = B c n j k ≠ 0` gives `ω_{k,p} - (q-j) ≤ v_p(B)`.

## Formalisation (this file; complete, no gaps)

* The multiplicative half of the tame calculus of `BrickValuation.lean` is repeated here
  (`VpGe`, `Tame`, `Tame.mul`, `Tame.prod`, …; proof files import only `Window.Statements`).
  No inverse is needed: the bricks come already tamed from the hypothesis `Stmt_BrickVal`
  (`tame_poly`, `tame_rat`).
* Side conditions of `Stmt_BrickVal` with `N = h₀`: `2 h_i ≤ h₀` for `1 ≤ i ≤ q` (`two_h_le`, from
  `eta_mono` and `2 η_q < η₀`), `1 ≤ h_i`, and `k ≤ h₀ - h₁ ≤ h₀` from `k ∈ Krange`.  The hypothesis
  `1 ≤ n` is not used, and `p` odd is not needed (`v_p(2) ≥ 0` suffices for the linear factor).
* The weight identities: `wPoly_P` (cast of `1`), `wPoly_Q` (JTNB (7.5) twice, `neg_ediv_eq`),
  `wRat_S` (casts only), summed with `Finset.sum_congr`.

**Remark on JTNB.**  The (7.5) identity for the `Q`-bricks is exactly what turns JTNB's weight
`⌊(k-b)/p⌋ - ⌊(k-a)/p⌋` of (7.4) into the two floors `⌊(h₀-k-1)/p⌋ - ⌊(h₀-h_j-k)/p⌋` printed in
(8.9); no inequality is lost anywhere, so (8.11) holds with the *Taylor* coefficients for every
`n` and every prime `p` with `p² > h₀` (including `p ≤ q - r`, cf. the remark in
`BrickValuation.lean`).

**Numerical check.** `python/window_mirror.py`, section "Laurent data …": every prime `p` with
`h₀ < p² `, `p ≤ 2h₀ + 2`, all `j`, all `k ∈ Krange` with `B ≠ 0`, exact (`cfgW` `n = 1, 2`; Theorem 3
configuration `n = 1, 2, 3`).

**Status: done** (difficulty 3/5).
-/

open Filter Topology Finset PowerSeries

noncomputable section

namespace ZetaWindow

namespace LaurentValuation

/-! ### `v_p(x) ≥ c`, with `0` counting as `+∞`, and `w`-tame power series -/

/-- `x = 0` or `c ≤ v_p(x)`. -/
def VpGe (p : ℕ) (c : ℤ) (x : ℚ) : Prop :=
  x = 0 ∨ c ≤ padicValRat p x

/-- `F` is `w`-tame: for every `i`, `[ε^i] F = 0` or `w - i ≤ v_p([ε^i] F)`. -/
def Tame (p : ℕ) (w : ℤ) (F : PowerSeries ℚ) : Prop :=
  ∀ i : ℕ, VpGe p (w - i) (coeff i F)

section Tame

variable {p : ℕ}

theorem VpGe.zero (c : ℤ) : VpGe p c 0 := Or.inl rfl

theorem VpGe.mono {c c' : ℤ} {x : ℚ} (h : VpGe p c x) (hc : c' ≤ c) : VpGe p c' x := by
  rcases h with h | h
  · exact Or.inl h
  · exact Or.inr (hc.trans h)

theorem Tame.mono {w w' : ℤ} {F : PowerSeries ℚ} (h : Tame p w F) (hw : w' ≤ w) :
    Tame p w' F :=
  fun i => (h i).mono (by omega)

theorem Tame.one : Tame p 0 (1 : PowerSeries ℚ) := by
  intro i
  rw [coeff_one]
  split_ifs with h
  · subst h; right; simp
  · exact Or.inl rfl

theorem Tame.ofC (c : ℚ) : Tame p (padicValRat p c) (C c) := by
  intro i
  rw [coeff_C]
  split_ifs with h
  · subst h; right; simp
  · exact Or.inl rfl

theorem Tame.ofX : Tame p 1 (X : PowerSeries ℚ) := by
  intro i
  rw [coeff_X]
  split_ifs with h
  · subst h; right; simp
  · exact Or.inl rfl

variable [hp : Fact p.Prime]

theorem VpGe.add {c : ℤ} {x y : ℚ} (hx : VpGe p c x) (hy : VpGe p c y) : VpGe p c (x + y) := by
  rcases hx with hx | hx
  · rw [hx, zero_add]; exact hy
  rcases hy with hy | hy
  · rw [hy, add_zero]; exact Or.inr hx
  by_cases hxy : x + y = 0
  · exact Or.inl hxy
  · exact Or.inr (le_trans (le_min hx hy) (padicValRat.min_le_padicValRat_add hxy))

theorem VpGe.mul {c d : ℤ} {x y : ℚ} (hx : VpGe p c x) (hy : VpGe p d y) :
    VpGe p (c + d) (x * y) := by
  by_cases hx0 : x = 0
  · left; rw [hx0, zero_mul]
  by_cases hy0 : y = 0
  · left; rw [hy0, mul_zero]
  have hx' : c ≤ padicValRat p x := hx.resolve_left hx0
  have hy' : d ≤ padicValRat p y := hy.resolve_left hy0
  right
  rw [padicValRat.mul hx0 hy0]
  omega

theorem VpGe.sum {ι : Type*} (s : Finset ι) (f : ι → ℚ) {c : ℤ}
    (h : ∀ i ∈ s, VpGe p c (f i)) : VpGe p c (∑ i ∈ s, f i) :=
  Finset.sum_induction f (VpGe p c) (fun _ _ ha hb => ha.add hb) (VpGe.zero c) h

theorem Tame.add {w : ℤ} {F G : PowerSeries ℚ} (hF : Tame p w F) (hG : Tame p w G) :
    Tame p w (F + G) := by
  intro i
  rw [map_add]
  exact (hF i).add (hG i)

theorem Tame.mul {w w' : ℤ} {F G : PowerSeries ℚ} (hF : Tame p w F) (hG : Tame p w' G) :
    Tame p (w + w') (F * G) := by
  intro i
  rw [coeff_mul]
  refine VpGe.sum _ _ (fun x hx => ?_)
  rw [HasAntidiagonal.mem_antidiagonal] at hx
  refine ((hF x.1).mul (hG x.2)).mono (le_of_eq ?_)
  rw [← hx]; push_cast; ring

theorem Tame.prod {ι : Type*} (s : Finset ι) (w : ι → ℤ)
    (f : ι → PowerSeries ℚ) (h : ∀ i ∈ s, Tame p (w i) (f i)) :
    Tame p (∑ i ∈ s, w i) (∏ i ∈ s, f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => rw [sum_empty, prod_empty]; exact Tame.one
  | insert a s ha ih =>
    rw [sum_insert ha, prod_insert ha]
    exact (h a (mem_insert_self a s)).mul (ih fun i hi => h i (mem_insert_of_mem hi))

/-- The linear factor `h₀ - 2k + 2ε` of `G_k` is `0`-tame: its coefficients `h₀ - 2k` and `2` are
integers (no parity assumption on `p` is needed). -/
theorem Tame.linear (a b : ℕ) : Tame p 0 (C ((a : ℚ) - 2 * b) + C 2 * X) := by
  have h1 : Tame p 0 (C ((a : ℚ) - 2 * b)) := by
    refine (Tame.ofC _).mono ?_
    have e : ((a : ℚ) - 2 * b) = (((a : ℤ) - 2 * b : ℤ) : ℚ) := by push_cast; ring
    rw [e, padicValRat.of_int]
    positivity
  have h2 : Tame p 0 (C (2 : ℚ) * X) := by
    refine ((Tame.ofC _).mul Tame.ofX).mono ?_
    have e : padicValRat p (2 : ℚ) = padicValRat p ((2 : ℕ) : ℚ) := by simp
    rw [e, padicValRat.of_nat]
    positivity
  exact h1.add h2

end Tame

/-! ### The bricks are tame (`Stmt_BrickVal`) -/

theorem tame_poly (hBV : Stmt_BrickVal) {a b k p N : ℕ} (hp : p.Prime) (hb : 1 ≤ b) (hba : b ≤ a)
    (haN : a ≤ N) (hkN : k ≤ N) (hN : N < p ^ 2) : Tame p (wPoly a b k p) (polyBrick a b k) := by
  intro i
  by_cases h : coeff i (polyBrick a b k) = 0
  · exact Or.inl h
  · exact Or.inr (hBV.poly a b k p N i hp hb hba haN hkN hN h)

theorem tame_rat (hBV : Stmt_BrickVal) {a b k p N : ℕ} (hp : p.Prime) (ha : 1 ≤ a) (hab : a < b)
    (hbN : b ≤ N + 1) (hkN : k ≤ N) (hN : N < p ^ 2) : Tame p (wRat a b k p) (ratBrick a b k) := by
  intro i
  by_cases h : coeff i (ratBrick a b k) = 0
  · exact Or.inl h
  · exact Or.inr (hBV.rat a b k p N i hp ha hab hbN hkN hN h)

/-! ### The weights (JTNB (7.5)) and admissibility bounds -/

/-- JTNB (7.5): `⌊-x/p⌋ = -⌊(x-1)/p⌋ - 1`. -/
theorem neg_ediv_eq {p : ℕ} (hp0 : 0 < p) (x : ℤ) :
    (-x) / (p : ℤ) = -((x - 1) / (p : ℤ)) - 1 := by
  have hp' : (0 : ℤ) < p := by exact_mod_cast hp0
  have h1 : (p : ℤ) * ((x - 1) / p) + (x - 1) % p = x - 1 := Int.mul_ediv_add_emod _ _
  have h2 : 0 ≤ (x - 1) % (p : ℤ) := Int.emod_nonneg _ hp'.ne'
  have h3 : (x - 1) % (p : ℤ) < p := Int.emod_lt_of_pos _ hp'
  exact ((Int.ediv_emod_unique (r := (p : ℤ) - 1 - (x - 1) % p) hp').2
    ⟨by linear_combination -h1, by omega, by omega⟩).1

/-- Weight of `P_i = polyBrick h_i 1` at `t = -k`: `⌊(k-1)/p⌋ - ⌊(k-h_i)/p⌋ - ⌊(h_i-1)/p⌋`. -/
theorem wPoly_P (hi k p : ℕ) :
    wPoly hi 1 k p = ((k : ℤ) - 1) / p - ((k : ℤ) - hi) / p - ((hi : ℤ) - 1) / p := by
  simp only [wPoly, Nat.cast_one]

/-- Weight of `Q_i = polyBrick h₀ (h₀-h_i+1)` at `t = -k`, by JTNB (7.5) twice:
`wPoly h₀ (h₀-h_i+1) k p = ⌊(h₀-k-1)/p⌋ - ⌊(h₀-h_i-k)/p⌋ - ⌊(h_i-1)/p⌋`. -/
theorem wPoly_Q {p : ℕ} (hp0 : 0 < p) {h0 hi : ℕ} (k : ℕ) (hle : hi ≤ h0) :
    wPoly h0 (h0 - hi + 1) k p =
      ((h0 : ℤ) - k - 1) / p - ((h0 : ℤ) - hi - k) / p - ((hi : ℤ) - 1) / p := by
  unfold wPoly
  have hc : ((h0 - hi + 1 : ℕ) : ℤ) = (h0 : ℤ) - hi + 1 := by
    rw [Nat.cast_add, Nat.cast_sub hle, Nat.cast_one]
  rw [hc]
  have e1 := neg_ediv_eq hp0 ((h0 : ℤ) - hi - k + 1)
  have e2 := neg_ediv_eq hp0 ((h0 : ℤ) - k)
  rw [show -((h0 : ℤ) - hi - k + 1) = (k : ℤ) - ((h0 : ℤ) - hi + 1) by ring,
    show (h0 : ℤ) - hi - k + 1 - 1 = (h0 : ℤ) - hi - k by ring] at e1
  rw [show -((h0 : ℤ) - k) = (k : ℤ) - h0 by ring] at e2
  rw [show (h0 : ℤ) - ((h0 : ℤ) - hi + 1) = (hi : ℤ) - 1 by ring, e1, e2]
  ring

/-- Weight of `ε S_i = ratBrick h_i (h₀-h_i+1)` at `t = -k`:
`⌊(h₀-2h_i)/p⌋ - ⌊(k-h_i)/p⌋ - ⌊(h₀-h_i-k)/p⌋`. -/
theorem wRat_S {h0 hi : ℕ} (k p : ℕ) (hle : hi ≤ h0) :
    wRat hi (h0 - hi + 1) k p =
      ((h0 : ℤ) - 2 * hi) / p - ((k : ℤ) - hi) / p - ((h0 : ℤ) - hi - k) / p := by
  unfold wRat
  have hc : ((h0 - hi + 1 : ℕ) : ℤ) = (h0 : ℤ) - hi + 1 := by
    rw [Nat.cast_add, Nat.cast_sub hle, Nat.cast_one]
  rw [hc, show (h0 : ℤ) - hi + 1 - hi - 1 = (h0 : ℤ) - 2 * hi by ring,
    show (h0 : ℤ) - hi + 1 - 1 - k = (h0 : ℤ) - hi - k by ring]

/-- `2 h_i ≤ h₀` for `1 ≤ i ≤ q` (from `η_i ≤ η_q` and `2 η_q < η₀`). -/
theorem two_h_le {c : Config} (hc : Admissible c) (n : ℕ) {i : ℕ} (h1 : 1 ≤ i) (hi : i ≤ c.q) :
    2 * c.h n i ≤ c.h0 n := by
  have hm := hc.eta_mono i c.q h1 hi le_rfl
  have ht := hc.two_eta_lt
  have h2 : 2 * c.eta i * n ≤ c.eta0 * n := Nat.mul_le_mul_right n (by omega)
  unfold Config.h Config.h0
  linarith

theorem one_le_h (c : Config) (n i : ℕ) : 1 ≤ c.h n i := by
  unfold Config.h
  exact Nat.le_add_left 1 _

end LaurentValuation

open LaurentValuation in
theorem LaurentVal_proof (hBV : Stmt_BrickVal) : Stmt_LaurentVal := by
  intro c hc n _ p hp hp2 j k _ hk hB
  have : Fact p.Prime := ⟨hp⟩
  have hp0 : 0 < p := hp.pos
  have hkN : k ≤ c.h0 n := by
    unfold Krange at hk
    rw [Finset.mem_Icc] at hk
    omega
  have hrq : c.r ≤ c.q := by have := hc.r_add_four_le_q; omega
  -- the bricks are tame (`Stmt_BrickVal` with `N = h₀`)
  have hPQ : ∀ i ∈ Icc 1 c.r,
      Tame p (wPoly (c.h n i) 1 k p + wPoly (c.h0 n) (c.h0 n - c.h n i + 1) k p)
        (polyBrick (c.h n i) 1 k * polyBrick (c.h0 n) (c.h0 n - c.h n i + 1) k) := by
    intro i hi
    rw [Finset.mem_Icc] at hi
    have hi2 := two_h_le hc n hi.1 (hi.2.trans hrq)
    have hi1 := one_le_h c n i
    exact (tame_poly (N := c.h0 n) hBV hp le_rfl hi1 (by omega) hkN hp2).mul
      (tame_poly (N := c.h0 n) hBV hp (by omega) (by omega) le_rfl hkN hp2)
  have hS : ∀ i ∈ Icc (c.r + 1) c.q,
      Tame p (wRat (c.h n i) (c.h0 n - c.h n i + 1) k p)
        (ratBrick (c.h n i) (c.h0 n - c.h n i + 1) k) := by
    intro i hi
    rw [Finset.mem_Icc] at hi
    have hi2 := two_h_le hc n (by omega) hi.2
    have hi1 := one_le_h c n i
    exact tame_rat (N := c.h0 n) hBV hp hi1 (by omega) (by omega) hkN hp2
  -- `G_k` is `ω_{k,p}`-tame: the weights add up to `omegaKP` (JTNB (8.9))
  have hG : Tame p (omegaKP c n p k) (Gk c n k) := by
    unfold Gk
    refine (((Tame.linear (c.h0 n) k).mul (Tame.prod _ _ _ hPQ)).mul
      (Tame.prod _ _ _ hS)).mono (le_of_eq ?_)
    rw [zero_add]
    unfold omegaKP
    congr 1
    · refine Finset.sum_congr rfl (fun i hi => ?_)
      rw [Finset.mem_Icc] at hi
      have hi2 := two_h_le hc n hi.1 (hi.2.trans hrq)
      rw [wPoly_P, wPoly_Q hp0 k (by omega)]
      ring
    · refine Finset.sum_congr rfl (fun i hi => ?_)
      rw [Finset.mem_Icc] at hi
      have hi2 := two_h_le hc n (by omega) hi.2
      rw [wRat_S k p (by omega)]
  exact (hG (c.q - j)).resolve_left hB

#print axioms LaurentVal_proof

end ZetaWindow

end
