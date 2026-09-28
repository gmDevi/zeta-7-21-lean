import Zeta2Lean.Window.Statements

set_option linter.style.header false
set_option linter.style.longLine false

/-!
# p-adic valuation of the bricks (JTNB Lemmas 17, 18)

**Task.** Prove `Stmt_BrickVal` (no hypotheses): for a prime `p` and `N < p²` bounding all numbers
involved,
* `poly` (`1 ≤ b ≤ a ≤ N`, `k ≤ N`): `[ε^i] polyBrick a b k ≠ 0 → wPoly a b k p - i ≤ v_p([ε^i] …)`;
* `rat` (`1 ≤ a < b ≤ N + 1`, `k ≤ N`): `[ε^i] ratBrick a b k ≠ 0 → wRat a b k p - i ≤ v_p([ε^i] …)`,
with `wPoly a b k p = ⌊(k-b)/p⌋ - ⌊(k-a)/p⌋ - ⌊(a-b)/p⌋` (JTNB (7.4)) and
`wRat a b k p = ⌊(b-a-1)/p⌋ - ⌊(k-a)/p⌋ - ⌊(b-1-k)/p⌋` (JTNB (7.7)).

**Informal proof.**  Call `f ∈ ℚ⟦ε⟧` *`w`-tame* if `[ε^i] f ≠ 0 → w - i ≤ v_p([ε^i] f)` for all `i`.
(a) `w`-tame · `w'`-tame is `(w+w')`-tame (ultrametric inequality on `[ε^i](fg) = ∑ [ε^u]f [ε^{i-u}]g`);
(b) `C c` is `v_p(c)`-tame; `X` is `1`-tame; for `c ≠ 0` with `v_p(c) ≤ 1`, `C c + X` is `v_p(c)`-tame
and `(C c + X)⁻¹ = ∑ (-1)^i c^{-1-i} ε^i` is `(-v_p(c))`-tame.
*poly*: `polyBrick a b k = C(1/(a-b)!) ∏_{l=b}^{a-1} (C(l-k) + X)`.  The factor `l = k` (present iff
`b ≤ k < a`) is `X`; the others have `0 < |l-k| ≤ N-1 < p²`, so `v_p(l-k) ≤ 1`.  Total weight
`w = -v_p((a-b)!) + ∑_{l≠k} v_p(l-k) + [b ≤ k < a]`.  By Legendre (`v_p(m!) = ⌊m/p⌋` for `m < p²`) and
`∏_{l≠k} |l-k| = (k-b)!(a-1-k)!`, `(k-b)!/(k-a)!` or `(a-1-k)!/(b-1-k)!` (for `b ≤ k < a`, `k ≥ a`,
`k < b`), `w = wPoly a b k p` after JTNB (7.5): `⌊s/p⌋ = -⌊(-s-1)/p⌋ - 1` for integers `s`.
*rat*: `ratBrick a b k = C((b-a-1)!) · (X or 1) · ∏_{i ≠ k} (C(i-k) + X)⁻¹`, weight
`v_p((b-a-1)!) + [k ∉ [a,b)] - ∑_{i≠k} v_p(i-k)`, which equals `wRat a b k p` by the same two facts.

## Formalisation (this file; complete, no gaps)

* `Tame p w F` (`w`-tame, with `0` counting as `+∞` via `VpGe`) is closed under `+` (same weight),
  `*` (`Tame.mul`), finite products (`Tame.prod`, weights add), weakening (`Tame.mono`) and inverses
  (`Tame.inv`: if `v_p(F(0)) ≤ w` then `F⁻¹` is `(-w)`-tame, by strong induction on the recursion
  `PowerSeries.coeff_inv`, as in the parent project's `DenomL2c`).  `C c` is `v_p(c)`-tame (`Tame.ofC`),
  `X` is `1`-tame (`Tame.ofX`), hence `C c + X` is `v_p(c)`-tame when `v_p(c) ≤ 1` (`Tame.lin`).
  The brick `ratBrick` is `C((b-a-1)!) · (X or 1) · P⁻¹` with `P = ∏ (C(i-k) + X)`, `P(0) = ∏ (i-k)`, and
  `v_p(P(0)) = ∑ v_p(i-k)` (`padicValRat_prod`), so `Tame.inv` applies with `w = ∑ v_p(i-k)`.
* Instead of Legendre's formula and products of factorials, the weights are compared by
  **induction on the length of the brick**.  With `W p k i = 1` if `i = k` and `v_p(i-k)` otherwise
  (the weight of the factor `C(i-k) + X`), and `ind p x = [p ∣ x]`:
  - `v_p(m) = [p ∣ m]` for `0 < |m| < p²` (`padicValRat_small`), so `W p k i = ind p (i-k)`
    (`W_eq`) and `v_p((d+1)!) = v_p(d!) + [p ∣ d+1]`;
  - `⌊x/p⌋ = ⌊(x-1)/p⌋ + [p ∣ x]` (`ediv_eq_sub_one_ediv_add_ind`) gives
    `wPoly (a+1) b k p = wPoly a b k p + [p ∣ k-a] - [p ∣ a+1-b]` (`wPoly_succ`) and
    `wRat a (b+1) k p = wRat a b k p + [p ∣ b-a] - [p ∣ b-k]` (`wRat_succ`);
  - JTNB (7.5), `⌊-x/p⌋ = -⌊(x-1)/p⌋ - 1` (`neg_ediv_eq`), gives the base case
    `wRat a (a+1) k p = 1 - [p ∣ k-a]` (`wRat_base`).
  Hence `-v_p((a-b)!) + ∑_{i∈[b,a)} W p k i = wPoly a b k p` (`poly_weight`) and
  `v_p((b-a-1)!) + 1 - ∑_{i∈[a,b)} W p k i = wRat a b k p` (`rat_weight`); these are exactly the
  weights of the brick factorisations above.
* Only `p` prime, `b ≤ a ≤ N` (resp. `a < b ≤ N + 1`), `k ≤ N` and `N < p²` are used; the hypotheses
  `1 ≤ b`, `1 ≤ a` of the statement are not needed.

**Remark on JTNB.**  JTNB Lemmas 17, 18 bound `ord_p` of the *derivatives* `R^{(j)}(-k)` (proof by
induction with (7.6)).  `Stmt_BrickVal` bounds the *Taylor coefficients* `[ε^j] = R^{(j)}(-k)/j!`,
which is stronger by `ord_p(j!)` (a difference only when `p ≤ j`).  The Taylor form is what the
Leibniz rule for `B_{j,k} = (1/(q-j)!) (R(t)(t+k)^{q-r})^{(q-j)}` needs (JTNB (8.11)); with
`p > √h₀` it agrees with the derivative form once `√h₀ > q - r`, i.e. for all but finitely many `n`,
so JTNB's asymptotic argument is unaffected.  The factorisation argument above proves the Taylor form
directly, for every `n`.

**Numerical check.** `python/window_mirror.py`, section "Stmt_BrickInt, Stmt_BrickVal": random bricks,
every prime `p < 60` with `N < p²`, every coefficient, exact.

**Status: done** (difficulty 3/5).
-/

open Filter Topology Finset PowerSeries

noncomputable section

namespace ZetaWindow

namespace BrickValuation

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

/-- Inverse: if `F` is `w`-tame and `v_p(F(0)) ≤ w`, then `F⁻¹` is `(-w)`-tame.  (No hypothesis
`F(0) ≠ 0` is needed: in Mathlib `F⁻¹ = 0` when `F(0) = 0`, and the recursion below still applies.
For a `w`-tame `F` with `F(0) ≠ 0` one always has `w ≤ v_p(F(0))`, so `hw` means `w = v_p(F(0))`.) -/
theorem Tame.inv {w : ℤ} {F : PowerSeries ℚ} (hF : Tame p w F)
    (hw : padicValRat p (constantCoeff F) ≤ w) : Tame p (-w) F⁻¹ := by
  intro j
  induction j using Nat.strong_induction_on with
  | _ j ih =>
    rw [coeff_inv]
    split_ifs with hj
    · subst hj; right; rw [padicValRat.inv]; push_cast; linarith
    · have hsum : VpGe p (-(j : ℤ)) (∑ x ∈ antidiagonal j,
          if x.2 < j then coeff x.1 F * coeff x.2 F⁻¹ else 0) := by
        refine VpGe.sum _ _ (fun x hx => ?_)
        rw [HasAntidiagonal.mem_antidiagonal] at hx
        split_ifs with hlt
        · refine ((hF x.1).mul (ih x.2 hlt)).mono (le_of_eq ?_)
          rw [← hx]; push_cast; ring
        · exact Or.inl rfl
      have hc : VpGe p (-w) (-(constantCoeff F)⁻¹) := by
        right; rw [padicValRat.neg, padicValRat.inv]; linarith
      refine (hc.mul hsum).mono (le_of_eq ?_)
      ring

/-- A linear factor `c + ε` with `v_p(c) ≤ 1` is `v_p(c)`-tame. -/
theorem Tame.lin {c : ℚ} (hc : padicValRat p c ≤ 1) : Tame p (padicValRat p c) (C c + X) :=
  (Tame.ofC c).add (Tame.ofX.mono hc)

/-- `v_p` of a finite product of non-zero rationals is the sum of the `v_p`. -/
theorem padicValRat_prod {ι : Type*} (s : Finset ι) (f : ι → ℚ)
    (h : ∀ i ∈ s, f i ≠ 0) : padicValRat p (∏ i ∈ s, f i) = ∑ i ∈ s, padicValRat p (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    have hs : ∀ i ∈ s, f i ≠ 0 := fun i hi => h i (mem_insert_of_mem hi)
    rw [prod_insert ha, sum_insert ha,
      padicValRat.mul (h a (mem_insert_self a s)) (prod_ne_zero_iff.2 hs), ih hs]

end Tame

/-! ### Small integers, and the floor identities -/

/-- `[p ∣ x]` as an integer. -/
def ind (p : ℕ) (x : ℤ) : ℤ := if (p : ℤ) ∣ x then 1 else 0

section Arith

variable {p : ℕ}

theorem ind_neg (x : ℤ) : ind p (-x) = ind p x := by
  unfold ind; simp only [dvd_neg]

theorem ind_le_one (x : ℤ) : ind p x ≤ 1 := by
  unfold ind; split_ifs <;> norm_num

/-- `⌊x/p⌋ = ⌊(x-1)/p⌋ + [p ∣ x]`. -/
theorem ediv_eq_sub_one_ediv_add_ind (hp0 : 0 < p) (x : ℤ) :
    x / (p : ℤ) = (x - 1) / (p : ℤ) + ind p x := by
  have hp' : (0 : ℤ) < p := by exact_mod_cast hp0
  have h1 : (p : ℤ) * ((x - 1) / p) + (x - 1) % p = x - 1 := Int.mul_ediv_add_emod _ _
  have h2 : 0 ≤ (x - 1) % (p : ℤ) := Int.emod_nonneg _ hp'.ne'
  have h3 : (x - 1) % (p : ℤ) < p := Int.emod_lt_of_pos _ hp'
  unfold ind
  by_cases hr : (x - 1) % (p : ℤ) + 1 = p
  · have hq : x / (p : ℤ) = (x - 1) / p + 1 :=
      ((Int.ediv_emod_unique hp').2 ⟨by linear_combination h1 - hr, le_rfl, hp'⟩).1
    have hd : (p : ℤ) ∣ x := ⟨(x - 1) / p + 1, by linear_combination -h1 + hr⟩
    rw [ite_eq_left hd, hq]
  · have hq := (Int.ediv_emod_unique (a := x) (r := (x - 1) % (p : ℤ) + 1)
      (q := (x - 1) / p) hp').2 ⟨by linear_combination h1, by omega, by omega⟩
    have hd : ¬ (p : ℤ) ∣ x := by
      intro hd
      have := Int.emod_eq_zero_of_dvd hd
      omega
    rw [ite_eq_right hd, hq.1, add_zero]

/-- JTNB (7.5): `⌊-x/p⌋ = -⌊(x-1)/p⌋ - 1`. -/
theorem neg_ediv_eq (hp0 : 0 < p) (x : ℤ) : (-x) / (p : ℤ) = -((x - 1) / (p : ℤ)) - 1 := by
  have hp' : (0 : ℤ) < p := by exact_mod_cast hp0
  have h1 : (p : ℤ) * ((x - 1) / p) + (x - 1) % p = x - 1 := Int.mul_ediv_add_emod _ _
  have h2 : 0 ≤ (x - 1) % (p : ℤ) := Int.emod_nonneg _ hp'.ne'
  have h3 : (x - 1) % (p : ℤ) < p := Int.emod_lt_of_pos _ hp'
  exact ((Int.ediv_emod_unique (r := (p : ℤ) - 1 - (x - 1) % p) hp').2
    ⟨by linear_combination -h1, by omega, by omega⟩).1

/-- `wPoly (a+1) b k p = wPoly a b k p + [p ∣ k-a] - [p ∣ a+1-b]`. -/
theorem wPoly_succ (hp0 : 0 < p) (a b k : ℕ) :
    wPoly (a + 1) b k p = wPoly a b k p + ind p ((k : ℤ) - a) - ind p ((a : ℤ) + 1 - b) := by
  unfold wPoly
  push_cast
  have h1 := ediv_eq_sub_one_ediv_add_ind hp0 ((k : ℤ) - a)
  have h2 := ediv_eq_sub_one_ediv_add_ind hp0 ((a : ℤ) + 1 - b)
  rw [show (k : ℤ) - a - 1 = (k : ℤ) - (a + 1) by ring] at h1
  rw [show (a : ℤ) + 1 - b - 1 = (a : ℤ) - b by ring] at h2
  linarith

/-- `wRat a (b+1) k p = wRat a b k p + [p ∣ b-a] - [p ∣ b-k]`. -/
theorem wRat_succ (hp0 : 0 < p) (a b k : ℕ) :
    wRat a (b + 1) k p = wRat a b k p + ind p ((b : ℤ) - a) - ind p ((b : ℤ) - k) := by
  unfold wRat
  push_cast
  have h1 := ediv_eq_sub_one_ediv_add_ind hp0 ((b : ℤ) - a)
  have h2 := ediv_eq_sub_one_ediv_add_ind hp0 ((b : ℤ) - k)
  rw [show (b : ℤ) + 1 - a - 1 = (b : ℤ) - a by ring,
    show (b : ℤ) + 1 - 1 - k = (b : ℤ) - k by ring]
  rw [show (b : ℤ) - k - 1 = (b : ℤ) - 1 - k by ring] at h2
  linarith

/-- `wRat a (a+1) k p = 1 - [p ∣ k-a]` (uses JTNB (7.5)). -/
theorem wRat_base (hp0 : 0 < p) (a k : ℕ) : wRat a (a + 1) k p = 1 - ind p ((k : ℤ) - a) := by
  unfold wRat
  push_cast
  have h1 := ediv_eq_sub_one_ediv_add_ind hp0 ((k : ℤ) - a)
  have h2 := neg_ediv_eq hp0 ((k : ℤ) - a)
  rw [show (a : ℤ) + 1 - a - 1 = 0 by ring, show (a : ℤ) + 1 - 1 - k = -((k : ℤ) - a) by ring,
    Int.zero_ediv]
  linarith

variable [hp : Fact p.Prime]

/-- `v_p(m) = [p ∣ m]` for `0 < |m| < p²`. -/
theorem padicValRat_small {m : ℤ} (hm : m ≠ 0) (hlt : m.natAbs < p ^ 2) :
    padicValRat p (m : ℚ) = ind p m := by
  rw [padicValRat.of_int, padicValInt, ind]
  have hk : 0 < m.natAbs := Int.natAbs_pos.2 hm
  split_ifs with hd
  · have hd' : p ∣ m.natAbs := Int.natCast_dvd.1 hd
    have h1 : 1 ≤ padicValNat p m.natAbs := one_le_padicValNat_of_dvd hk.ne' hd'
    have h2 : padicValNat p m.natAbs ≤ 1 := by
      by_contra h
      have hdvd : p ^ 2 ∣ m.natAbs := (padicValNat_dvd_iff_le (n := 2) hk.ne').2 (by omega)
      exact absurd (Nat.le_of_dvd hk hdvd) (by omega)
    have h3 : padicValNat p m.natAbs = 1 := le_antisymm h2 h1
    rw [h3]; rfl
  · have hd' : ¬ p ∣ m.natAbs := fun h => hd (Int.natCast_dvd.2 h)
    rw [padicValNat.eq_zero_of_not_dvd hd']; rfl

/-- `v_p(m) = [p ∣ m]` for `0 < m < p²`. -/
theorem padicValNat_small {m : ℕ} (h1 : 1 ≤ m) (hm : m < p ^ 2) :
    (padicValNat p m : ℤ) = ind p m := by
  have h := padicValRat_small (p := p) (m := (m : ℤ)) (by omega) (by simpa using hm)
  rw [Int.cast_natCast, padicValRat.of_nat] at h
  exact h

/-- Weight of the factor `C (i - k) + X`: `1` if `i = k` (the factor is `X`), else `v_p(i - k)`. -/
def W (p k i : ℕ) : ℤ := if i = k then 1 else padicValRat p ((i : ℚ) - k)

theorem W_eq {k i N : ℕ} (hi : i ≤ N) (hk : k ≤ N) (hN : N < p ^ 2) :
    W p k i = ind p ((i : ℤ) - k) := by
  unfold W
  split_ifs with h
  · subst h; simp [ind]
  · have hm : ((i : ℤ) - k) ≠ 0 := by omega
    have hlt : ((i : ℤ) - k).natAbs < p ^ 2 := by omega
    rw [show ((i : ℚ) - k) = (((i : ℤ) - k : ℤ) : ℚ) by push_cast; ring]
    exact padicValRat_small hm hlt

theorem padicValRat_sub_le_one {k i N : ℕ} (hi : i ≤ N) (hk : k ≤ N) (hN : N < p ^ 2) :
    padicValRat p ((i : ℚ) - k) ≤ 1 := by
  by_cases h : i = k
  · subst h; simp
  · have h' := W_eq (p := p) hi hk hN
    rw [W, ite_eq_right h] at h'
    rw [h']
    exact ind_le_one _

theorem Tame.factor {k i N : ℕ} (hi : i ≤ N) (hk : k ≤ N) (hN : N < p ^ 2) :
    Tame p (W p k i) (C ((i : ℚ) - k) + X) := by
  by_cases h : i = k
  · subst h; rw [W, ite_eq_left rfl, sub_self, map_zero, zero_add]; exact Tame.ofX
  · rw [W, ite_eq_right h]; exact Tame.lin (padicValRat_sub_le_one hi hk hN)

/-- The weight of the polynomial brick: `-v_p(d!) + ∑_{i ∈ [b, b+d)} W p k i = wPoly (b+d) b k p`. -/
theorem poly_weight {b k N : ℕ} (hk : k ≤ N) (hN : N < p ^ 2) : ∀ d : ℕ, b + d ≤ N →
    -(padicValNat p d.factorial : ℤ) + ∑ i ∈ Ico b (b + d), W p k i = wPoly (b + d) b k p := by
  intro d
  induction d with
  | zero => intro _; simp [wPoly]
  | succ d ih =>
    intro hd
    have ih' := ih (by omega)
    have hW := W_eq (p := p) (i := b + d) (by omega) hk hN
    have hv := padicValNat_small (p := p) (m := d + 1) (by omega) (by omega)
    have hs := wPoly_succ hp.out.pos (b + d) b k
    have e1 : ind p (((b + d : ℕ) : ℤ) - k) = ind p ((k : ℤ) - (b + d : ℕ)) := by
      rw [← ind_neg, neg_sub]
    have e2 : ind p (((b + d : ℕ) : ℤ) + 1 - b) = ind p ((d + 1 : ℕ) : ℤ) := by
      congr 1; push_cast; ring
    rw [show b + (d + 1) = b + d + 1 by ring, sum_Ico_succ_top (by omega), Nat.factorial_succ,
      padicValNat.mul (by omega) (Nat.factorial_ne_zero d), hs, hW]
    push_cast at hv ih' e1 e2 ⊢
    linarith

/-- The weight of the rational brick:
`v_p(d!) + 1 - ∑_{i ∈ [a, a+1+d)} W p k i = wRat a (a+1+d) k p`. -/
theorem rat_weight {a k N : ℕ} (hk : k ≤ N) (hN : N < p ^ 2) : ∀ d : ℕ, a + d ≤ N →
    (padicValNat p d.factorial : ℤ) + 1 - ∑ i ∈ Ico a (a + 1 + d), W p k i =
      wRat a (a + 1 + d) k p := by
  intro d
  induction d with
  | zero =>
    intro h
    rw [add_zero, Nat.Ico_succ_singleton, sum_singleton, W_eq (by omega) hk hN,
      wRat_base hp.out.pos, Nat.factorial_zero, padicValNat_one_right, ← ind_neg, neg_sub]
    simp
  | succ d ih =>
    intro hd
    have ih' := ih (by omega)
    have hW := W_eq (p := p) (i := a + 1 + d) (by omega) hk hN
    have hv := padicValNat_small (p := p) (m := d + 1) (by omega) (by omega)
    have hs := wRat_succ hp.out.pos a (a + 1 + d) k
    have e2 : ind p (((a + 1 + d : ℕ) : ℤ) - a) = ind p ((d + 1 : ℕ) : ℤ) := by
      congr 1; push_cast; ring
    rw [show a + 1 + (d + 1) = a + 1 + d + 1 by ring, sum_Ico_succ_top (by omega),
      Nat.factorial_succ, padicValNat.mul (by omega) (Nat.factorial_ne_zero d), hs, hW]
    push_cast at hv ih' e2 ⊢
    linarith

end Arith

end BrickValuation

open BrickValuation in
theorem BrickVal_proof : Stmt_BrickVal where
  poly := by
    intro a b k p N i hp hb hba haN hkN hN hne
    have := Fact.mk hp
    have hT : Tame p (wPoly a b k p) (polyBrick a b k) := by
      unfold polyBrick
      have h1 := Tame.ofC (p := p) (1 / ((a - b).factorial : ℚ))
      have h2 := Tame.prod (p := p) (Ico b a) (W p k) (fun i => C ((i : ℚ) - k) + X)
        (fun i hi => Tame.factor (N := N) (by rw [mem_Ico] at hi; omega) hkN hN)
      refine (h1.mul h2).mono (le_of_eq ?_)
      have hw := poly_weight (p := p) (b := b) hkN hN (a - b) (by omega)
      rw [Nat.add_sub_cancel' hba] at hw
      rw [one_div, padicValRat.inv, padicValRat.of_nat]
      linarith
    exact (hT i).resolve_left hne
  rat := by
    intro a b k p N i hp ha hab hbN hkN hN hne
    have := Fact.mk hp
    have hw := rat_weight (p := p) (a := a) hkN hN (b - a - 1) (by omega)
    rw [show a + 1 + (b - a - 1) = b by omega] at hw
    have hmem : ∀ i ∈ Ico a b, i ≤ N := fun i hi => by rw [mem_Ico] at hi; omega
    have hT : Tame p (wRat a b k p) (ratBrick a b k) := by
      unfold ratBrick
      split_ifs with hk
      · -- `a ≤ k < b`: the factor `t + k` cancels the pole
        set s := (Ico a b).erase k with hs
        have hne0 : ∀ i ∈ s, ((i : ℚ) - k) ≠ 0 := by
          intro i hi
          rw [hs, mem_erase] at hi
          exact sub_ne_zero.2 (by exact_mod_cast hi.1)
        have hP := Tame.prod (p := p) s (fun i => padicValRat p ((i : ℚ) - k))
          (fun i => C ((i : ℚ) - k) + X)
          (fun i hi => Tame.lin (padicValRat_sub_le_one (hmem i (mem_of_mem_erase hi)) hkN hN))
        have h0 : constantCoeff (∏ i ∈ s, (C ((i : ℚ) - k) + X)) = ∏ i ∈ s, ((i : ℚ) - k) := by
          simp [map_prod]
        have hPinv := hP.inv (by rw [h0, padicValRat_prod _ _ hne0])
        refine ((Tame.ofC _).mul hPinv).mono (le_of_eq ?_)
        have hsplit := sum_erase_add (Ico a b) (W p k) (mem_Ico.2 hk)
        have hWs : ∑ i ∈ s, W p k i = ∑ i ∈ s, padicValRat p ((i : ℚ) - k) := by
          refine sum_congr rfl (fun i hi => ?_)
          rw [hs, mem_erase] at hi
          rw [W, ite_eq_right hi.1]
        rw [← hs, hWs, W, ite_eq_left rfl] at hsplit
        rw [padicValRat.of_nat]
        linarith
      · -- `k ∉ [a, b)`: the factor `t + k` is `ε`
        have hne0 : ∀ i ∈ Ico a b, ((i : ℚ) - k) ≠ 0 := by
          intro i hi
          have hik : i ≠ k := by rw [mem_Ico] at hi; omega
          exact sub_ne_zero.2 (by exact_mod_cast hik)
        have hP := Tame.prod (p := p) (Ico a b) (fun i => padicValRat p ((i : ℚ) - k))
          (fun i => C ((i : ℚ) - k) + X)
          (fun i hi => Tame.lin (padicValRat_sub_le_one (hmem i hi) hkN hN))
        have h0 : constantCoeff (∏ i ∈ Ico a b, (C ((i : ℚ) - k) + X)) =
            ∏ i ∈ Ico a b, ((i : ℚ) - k) := by
          simp [map_prod]
        have hPinv := hP.inv (by rw [h0, padicValRat_prod _ _ hne0])
        refine (((Tame.ofC _).mul Tame.ofX).mul hPinv).mono (le_of_eq ?_)
        have hWs : ∑ i ∈ Ico a b, W p k i = ∑ i ∈ Ico a b, padicValRat p ((i : ℚ) - k) := by
          refine sum_congr rfl (fun i hi => ?_)
          have hik : i ≠ k := by rw [mem_Ico] at hi; omega
          rw [W, ite_eq_right hik]
        rw [hWs] at hw
        rw [padicValRat.of_nat]
        linarith
    exact (hT i).resolve_left hne

end ZetaWindow

end
