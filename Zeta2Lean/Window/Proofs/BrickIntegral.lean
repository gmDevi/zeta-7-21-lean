module

public import Zeta2Lean.Window.Statements

@[expose] public section

set_option linter.style.header false
set_option linter.style.longLine false

/-!
# Integrality of the bricks (JTNB Lemmas 15, 16)

**Proves `Stmt_BrickInt`** (no hypotheses):
* `poly`: for `b ≤ a`, every `k` and `i`: `D_{a-b}^i · [ε^i] polyBrick a b k ∈ ℤ`;
* `rat`: for `a₀ ≤ a < b ≤ b₀` and `a₀ ≤ k < b₀`: `D_{b₀-a₀-1}^i · [ε^i] ratBrick a b k ∈ ℤ`
(`D_m = Nat.lcmUpto m`).

**Proof (as formalised below).**  A series `A ∈ ℚ⟦ε⟧` is `d`-integral if `d^j [ε^j] A ∈ ℤ` for
every `j`; these series form a subring `DInt d` (Cauchy product), which contains the integer
constants and `c·ε` whenever `d c ∈ ℤ`, and `DInt d ⊆ DInt e` for `d ∣ e`.

*poly* (JTNB Lemma 15).  `polyBrick a b k = pb (a-b) (b-k)` with the ascending binomial brick
`pb m s = (ε+s)(ε+s+1)⋯(ε+s+m-1)/m! = binom(ε+s+m-1, m)` (`s ∈ ℤ`).  Pascal's rule
`pb (m+1) (s+1) = pb (m+1) s + pb m (s+1)` (`pb_pascal`) and integer induction on `s` reduce
`pb m s ∈ DInt D_m` (all `s ∈ ℤ`, `pb_mem`) to the case `s = 0`, where
`pb (m+1) 0 = (ε/(m+1)) ∏_{j=1}^{m} (1 + ε/j)` is a product of `D_{m+1}`-integral factors
(`pb_succ_zero_eq`); `D_m ∣ D_{m+1}` handles the second Pascal term.  (This replaces the
Vandermonde / Beta-integral argument of the informal proof by the elementary Pascal induction.)

*rat* (JTNB Lemma 16).  No inverse of a power series has to be computed.  `RSpec L s T` says
`T · ∏_{j<L} (ε+s+j) = (L-1)! ε`, i.e. `T` is the expansion at `t = -k` of
`(t+k)(L-1)!/((t+a)⋯(t+a+L-1))`, `s = a-k`.  Such a `T` is unique (`ℚ⟦ε⟧` is a domain,
`RSpec_unique`), and `ratBrick a b k` is one (`ratBrick_spec`, both branches of its definition,
with `L = b-a`, `s = a-k`).  The partial-fraction recurrence
`(t+a)^{-1}⋯(t+a+L)^{-1} L! = (L-1)!/((t+a)⋯(t+a+L-1)) - (L-1)!/((t+a+1)⋯(t+a+L))` becomes
`RSpec (L+1) s T₁ → RSpec (L+1) (s+1) T₂ → RSpec (L+2) s (T₁ - T₂)` (`RSpec_rec`, pure ring
algebra), with the base cases `RSpec 1 0 1` and `RSpec 1 s (ε/(s+ε))`,
`ε/(s+ε) = ∑_{n≥1} (-1)^{n-1} ε^n/s^n` (`rbase`), which is `D_M`-integral for `1 ≤ |s| ≤ M`.
Induction on `L` gives a `D_M`-integral solution whenever `-M ≤ s` and `s+L-1 ≤ M`
(`RSpec_exists`); with `M = b₀-a₀-1` both bounds follow from `a₀ ≤ a`, `b ≤ b₀`, `a₀ ≤ k < b₀`.

The proof of `poly` does not use `b ≤ a` (for `b > a` the brick is the empty product `1`), and
`pb_mem` holds for every shift `s ∈ ℤ`, i.e. JTNB Lemma 15 at every integer point `t = -k`.

**Status: done** (complete, no gaps; `#print axioms BrickInt_proof`: propext, Classical.choice,
Quot.sound).
-/

open Filter Topology Finset PowerSeries

noncomputable section

namespace ZetaWindow

namespace BrickIntegral

/-! ### `d`-integral power series -/

/-- The subring of `ℚ⟦X⟧` of `d`-integral series: `d^j · [X^j] A ∈ ℤ` for every `j`. -/
def DInt (d : ℚ) : Subring (PowerSeries ℚ) where
  carrier := {A | ∀ j : ℕ, ∃ z : ℤ, d ^ j * coeff j A = z}
  mul_mem' := by
    intro A B hA hB j
    simp only [Set.mem_ofPred_eq] at hA hB
    choose zA hzA using hA
    choose zB hzB using hB
    refine ⟨∑ p ∈ antidiagonal j, zA p.1 * zB p.2, ?_⟩
    rw [coeff_mul, Finset.mul_sum]
    push_cast
    refine Finset.sum_congr rfl fun p hp => ?_
    rw [← hzA, ← hzB, ← (mem_antidiagonal.1 hp), pow_add]
    ring
  one_mem' := by
    intro j
    rcases j with _ | j
    · exact ⟨1, by simp⟩
    · exact ⟨0, by simp [coeff_one]⟩
  add_mem' := by
    intro A B hA hB j
    obtain ⟨a, ha⟩ := hA j
    obtain ⟨b, hb⟩ := hB j
    exact ⟨a + b, by rw [map_add, mul_add, ha, hb]; push_cast; ring⟩
  zero_mem' := fun j => ⟨0, by simp⟩
  neg_mem' := by
    intro A hA j
    obtain ⟨a, ha⟩ := hA j
    exact ⟨-a, by rw [map_neg, mul_neg, ha]; push_cast; ring⟩

theorem DInt_mem {d : ℚ} {A : PowerSeries ℚ} :
    A ∈ DInt d ↔ ∀ j : ℕ, ∃ z : ℤ, d ^ j * coeff j A = z := Iff.rfl

/-- `C c · X` is `d`-integral as soon as `d c ∈ ℤ`. -/
theorem C_mul_X_mem {d c : ℚ} (h : ∃ z : ℤ, d * c = z) : C c * X ∈ DInt d := by
  rw [DInt_mem]
  intro j
  rw [coeff_C_mul, coeff_X]
  split_ifs with hj
  · subst hj
    obtain ⟨z, hz⟩ := h
    exact ⟨z, by rw [pow_one, mul_one, hz]⟩
  · exact ⟨0, by simp⟩

/-- Enlarging the denominator: for `d ∣ e`, `d`-integral series are `e`-integral. -/
theorem mem_of_dvd {d e : ℕ} (hde : d ∣ e) {A : PowerSeries ℚ} (hA : A ∈ DInt (d : ℚ)) :
    A ∈ DInt (e : ℚ) := by
  obtain ⟨q, rfl⟩ := hde
  rw [DInt_mem] at hA ⊢
  intro j
  obtain ⟨z, hz⟩ := hA j
  refine ⟨(q : ℤ) ^ j * z, ?_⟩
  push_cast
  linear_combination ((q : ℚ) ^ j) * hz

/-- Every `l ∈ [1, m]` divides `D_m = lcm(1, …, m)`. -/
theorem dvd_lcmUpto {l m : ℕ} (h1 : 1 ≤ l) (hlm : l ≤ m) : l ∣ Nat.lcmUpto m := by
  unfold Nat.lcmUpto
  exact Finset.dvd_lcm (s := Icc 1 m) (f := id) (mem_Icc.2 ⟨h1, hlm⟩)

/-- `D_m ∣ D_{m'}` for `m ≤ m'`. -/
theorem lcmUpto_dvd_lcmUpto {m m' : ℕ} (h : m ≤ m') : Nat.lcmUpto m ∣ Nat.lcmUpto m' := by
  unfold Nat.lcmUpto
  exact Finset.lcm_dvd fun l hl => Finset.dvd_lcm (Finset.Icc_subset_Icc_right h hl)

/-- `l ∣ D` implies `D · (1/l) ∈ ℤ`. -/
theorem int_of_dvd {l D : ℕ} (h : l ∣ D) : ∃ z : ℤ, (D : ℚ) * (1 / (l : ℚ)) = z := by
  obtain ⟨q, rfl⟩ := h
  rcases Nat.eq_zero_or_pos l with h0 | hpos
  · subst h0
    exact ⟨0, by simp⟩
  · refine ⟨q, ?_⟩
    have : (l : ℚ) ≠ 0 := by exact_mod_cast hpos.ne'
    push_cast
    field_simp

/-! ### Polynomial bricks (JTNB Lemma 15) -/

/-- The ascending binomial brick `(ε+s)(ε+s+1)⋯(ε+s+m-1)/m! = binom(ε+s+m-1, m)`, `s ∈ ℤ`. -/
def pb (m : ℕ) (s : ℤ) : PowerSeries ℚ :=
  C (1 / (m.factorial : ℚ)) * ∏ j ∈ range m, (C ((s : ℚ) + j) + X)

/-- `polyBrick a b k = pb (a-b) (b-k)`. -/
theorem polyBrick_eq (a b k : ℕ) : polyBrick a b k = pb (a - b) ((b : ℤ) - k) := by
  unfold polyBrick pb
  rw [Finset.prod_Ico_eq_prod_range]
  congr 1
  refine Finset.prod_congr rfl fun j _ => ?_
  have e : ((b + j : ℕ) : ℚ) - (k : ℚ) = (((b : ℤ) - k : ℤ) : ℚ) + (j : ℚ) := by
    push_cast
    ring
  rw [e]

theorem pb_zero (s : ℤ) : pb 0 s = 1 := by
  simp [pb]

/-- Pascal's rule `binom(x+1, m+1) = binom(x, m+1) + binom(x, m)` for the bricks. -/
theorem pb_pascal (m : ℕ) (s : ℤ) : pb (m + 1) (s + 1) = pb (m + 1) s + pb m (s + 1) := by
  have h1 : ∏ j ∈ range (m + 1), (C (((s + 1 : ℤ) : ℚ) + j) + X) =
      (∏ j ∈ range m, (C (((s + 1 : ℤ) : ℚ) + j) + X)) * (C ((s : ℚ) + ((m : ℚ) + 1)) + X) := by
    rw [Finset.prod_range_succ]
    have e : ((s + 1 : ℤ) : ℚ) + (m : ℚ) = (s : ℚ) + ((m : ℚ) + 1) := by
      push_cast
      ring
    rw [e]
  have h2 : ∏ j ∈ range (m + 1), (C ((s : ℚ) + j) + X) =
      (∏ j ∈ range m, (C (((s + 1 : ℤ) : ℚ) + j) + X)) * (C (s : ℚ) + X) := by
    rw [Finset.prod_range_succ']
    have e : ∀ j : ℕ, C ((s : ℚ) + ((j + 1 : ℕ) : ℚ)) + X =
        C (((s + 1 : ℤ) : ℚ) + (j : ℚ)) + X := by
      intro j
      have : (s : ℚ) + ((j + 1 : ℕ) : ℚ) = ((s + 1 : ℤ) : ℚ) + (j : ℚ) := by
        push_cast
        ring
      rw [this]
    simp only [e, Nat.cast_zero, add_zero]
  unfold pb
  rw [h1, h2]
  have key : (1 / ((m + 1).factorial : ℚ)) * ((s : ℚ) + ((m : ℚ) + 1)) =
      (1 / ((m + 1).factorial : ℚ)) * (s : ℚ) + 1 / (m.factorial : ℚ) := by
    rw [Nat.factorial_succ]
    push_cast
    field_simp
  have key': C (1 / ((m + 1).factorial : ℚ)) * C ((s : ℚ) + ((m : ℚ) + 1)) =
      C (1 / ((m + 1).factorial : ℚ)) * C (s : ℚ) + C (1 / (m.factorial : ℚ)) := by
    rw [← map_mul, ← map_mul, ← map_add, key]
  linear_combination (∏ j ∈ range m, (C (((s + 1 : ℤ) : ℚ) + j) + X)) * key'

/-- `binom(ε+m, m+1) = (ε/(m+1)) ∏_{j=1}^{m} (1 + ε/j)`. -/
theorem pb_succ_zero_eq (m : ℕ) : pb (m + 1) 0 =
    (C (1 / ((m + 1 : ℕ) : ℚ)) * X) * ∏ j ∈ range m, (C (1 / ((j + 1 : ℕ) : ℚ)) * X + 1) := by
  have h3 : ∀ j : ℕ, C (((0 : ℤ) : ℚ) + ((j + 1 : ℕ) : ℚ)) + X =
      C (((j + 1 : ℕ) : ℚ)) * (C (1 / ((j + 1 : ℕ) : ℚ)) * X + 1) := by
    intro j
    have hj : ((j + 1 : ℕ) : ℚ) ≠ 0 := by positivity
    have e1 : C (((0 : ℤ) : ℚ) + ((j + 1 : ℕ) : ℚ)) = C (((j + 1 : ℕ) : ℚ)) := by
      rw [Int.cast_zero, zero_add]
    have e2 : C (((j + 1 : ℕ) : ℚ)) * C (1 / ((j + 1 : ℕ) : ℚ)) = 1 := by
      rw [← map_mul, mul_one_div_cancel hj, map_one]
    linear_combination e1 - X * e2
  have hfac : (1 / ((m + 1).factorial : ℚ)) * ∏ j ∈ range m, ((j + 1 : ℕ) : ℚ) =
      1 / ((m + 1 : ℕ) : ℚ) := by
    rw [← Nat.cast_prod, Finset.prod_range_add_one_eq_factorial, Nat.factorial_succ]
    have : (m.factorial : ℚ) ≠ 0 := by positivity
    push_cast
    field_simp
  have hC : C (1 / ((m + 1).factorial : ℚ)) * ∏ j ∈ range m, C (((j + 1 : ℕ) : ℚ)) =
      C (1 / ((m + 1 : ℕ) : ℚ)) := by
    rw [← hfac, map_mul, map_prod]
  have h0 : C (((0 : ℤ) : ℚ) + ((0 : ℕ) : ℚ)) + X = (X : PowerSeries ℚ) := by simp
  unfold pb
  rw [Finset.prod_range_succ', h0]
  simp only [h3]
  rw [Finset.prod_mul_distrib]
  linear_combination (X * ∏ j ∈ range m, (C (1 / ((j + 1 : ℕ) : ℚ)) * X + 1)) * hC

theorem pb_succ_zero_mem (m : ℕ) : pb (m + 1) 0 ∈ DInt (Nat.lcmUpto (m + 1) : ℚ) := by
  rw [pb_succ_zero_eq]
  refine mul_mem (C_mul_X_mem (int_of_dvd (dvd_lcmUpto (by omega) le_rfl)))
    (prod_mem fun j hj => ?_)
  have hj := Finset.mem_range.1 hj
  exact add_mem (C_mul_X_mem (int_of_dvd (dvd_lcmUpto (by omega) (by omega)))) (one_mem _)

/-- **JTNB Lemma 15**: `pb m s` is `D_m`-integral for every `s ∈ ℤ`. -/
theorem pb_mem (m : ℕ) : ∀ s : ℤ, pb m s ∈ DInt (Nat.lcmUpto m : ℚ) := by
  induction m with
  | zero =>
    intro s
    rw [pb_zero]
    exact one_mem _
  | succ m ih =>
    have ih' : ∀ s : ℤ, pb m s ∈ DInt (Nat.lcmUpto (m + 1) : ℚ) := fun s =>
      mem_of_dvd (lcmUpto_dvd_lcmUpto (Nat.le_succ m)) (ih s)
    intro s
    refine Int.induction_on s (pb_succ_zero_mem m) (fun i hi => ?_) (fun i hi => ?_)
    · rw [pb_pascal]
      exact add_mem hi (ih' _)
    · have h := pb_pascal m (-(i : ℤ) - 1)
      rw [sub_add_cancel] at h
      have e : pb (m + 1) (-(i : ℤ) - 1) = pb (m + 1) (-(i : ℤ)) - pb m (-(i : ℤ)) := by
        rw [h]
        ring
      rw [e]
      exact sub_mem hi (ih' _)

/-! ### Rational bricks (JTNB Lemma 16) -/

/-- `T` is the expansion at `t = -k` of `(t+k)(L-1)!/((t+a)(t+a+1)⋯(t+a+L-1))`, `s = a-k`:
`T · ∏_{j<L} (ε+s+j) = (L-1)! ε`. -/
def RSpec (L : ℕ) (s : ℤ) (T : PowerSeries ℚ) : Prop :=
  T * ∏ j ∈ range L, (C ((s : ℚ) + j) + X) = C (((L - 1).factorial : ℚ)) * X

theorem lin_ne_zero (c : ℚ) : (C c + X : PowerSeries ℚ) ≠ 0 := by
  intro h
  have := congrArg (coeff 1) h
  simp [coeff_X] at this

theorem RSpec_unique {L : ℕ} {s : ℤ} {T₁ T₂ : PowerSeries ℚ} (h₁ : RSpec L s T₁)
    (h₂ : RSpec L s T₂) : T₁ = T₂ := by
  have hP : ∏ j ∈ range L, (C ((s : ℚ) + j) + X) ≠ 0 :=
    Finset.prod_ne_zero_iff.2 fun j _ => lin_ne_zero _
  exact mul_right_cancel₀ hP (h₁.trans h₂.symm)

/-- The partial-fraction recurrence `S(a, b+1) = S(a, b) - S(a+1, b+1)` of the rational bricks. -/
theorem RSpec_rec {L : ℕ} {s : ℤ} {T₁ T₂ : PowerSeries ℚ} (h₁ : RSpec (L + 1) s T₁)
    (h₂ : RSpec (L + 1) (s + 1) T₂) : RSpec (L + 1 + 1) s (T₁ - T₂) := by
  unfold RSpec at h₁ h₂ ⊢
  simp only [Nat.add_sub_cancel] at h₁ h₂ ⊢
  have A1 : ∏ j ∈ range (L + 1), (C ((s : ℚ) + j) + X) =
      (∏ j ∈ range L, (C ((s : ℚ) + ((j + 1 : ℕ) : ℚ)) + X)) * (C (s : ℚ) + X) := by
    rw [Finset.prod_range_succ']
    simp only [Nat.cast_zero, add_zero]
  have A2 : ∏ j ∈ range (L + 1), (C (((s + 1 : ℤ) : ℚ) + j) + X) =
      (∏ j ∈ range L, (C ((s : ℚ) + ((j + 1 : ℕ) : ℚ)) + X)) *
        (C ((s : ℚ) + ((L + 1 : ℕ) : ℚ)) + X) := by
    rw [Finset.prod_range_succ]
    have e : ∀ j : ℕ, C (((s + 1 : ℤ) : ℚ) + (j : ℚ)) + X =
        C ((s : ℚ) + ((j + 1 : ℕ) : ℚ)) + X := by
      intro j
      have : ((s + 1 : ℤ) : ℚ) + (j : ℚ) = (s : ℚ) + ((j + 1 : ℕ) : ℚ) := by
        push_cast
        ring
      rw [this]
    simp only [e]
  have A3 : ∏ j ∈ range (L + 1 + 1), (C ((s : ℚ) + j) + X) =
      (∏ j ∈ range L, (C ((s : ℚ) + ((j + 1 : ℕ) : ℚ)) + X)) * (C (s : ℚ) + X) *
        (C ((s : ℚ) + ((L + 1 : ℕ) : ℚ)) + X) := by
    rw [Finset.prod_range_succ, A1]
  rw [A1] at h₁
  rw [A2] at h₂
  rw [A3]
  have hu : C ((s : ℚ) + ((L + 1 : ℕ) : ℚ)) = C (s : ℚ) + C (((L + 1 : ℕ) : ℚ)) := by
    rw [← map_add]
  have hf : C (((L + 1).factorial : ℚ)) = C ((L.factorial : ℚ)) * C (((L + 1 : ℕ) : ℚ)) := by
    rw [← map_mul, Nat.factorial_succ, Nat.cast_mul]
    congr 1
    ring
  linear_combination (C ((s : ℚ) + ((L + 1 : ℕ) : ℚ)) + X) * h₁ - (C (s : ℚ) + X) * h₂ +
    C ((L.factorial : ℚ)) * X * hu - X * hf

theorem RSpec_one_zero : RSpec 1 0 1 := by
  simp [RSpec]

/-- `ε/(s+ε) = ∑_{n ≥ 1} (-1)^{n-1} ε^n / s^n`. -/
def rbase (s : ℚ) : PowerSeries ℚ :=
  mk fun n => if n = 0 then 0 else -(-1 / s) ^ n

theorem RSpec_one_rbase {s : ℤ} (hs : s ≠ 0) : RSpec 1 s (rbase (s : ℚ)) := by
  have hs' : (s : ℚ) ≠ 0 := by exact_mod_cast hs
  have e : (s : ℚ) * (-1 / (s : ℚ)) = -1 := by field_simp
  unfold RSpec
  simp only [range_one, prod_singleton, Nat.cast_zero, add_zero, Nat.sub_self,
    Nat.factorial_zero, Nat.cast_one, map_one, one_mul]
  ext n
  rw [mul_add, map_add, mul_comm (rbase _) (C _), coeff_C_mul, mul_comm (rbase _) X]
  rcases n with _ | n
  · simp [rbase]
  · rw [coeff_succ_X_mul, coeff_X]
    simp only [rbase, coeff_mk]
    rcases n with _ | n
    · rw [ite_eq_right (by omega), ite_eq_left rfl, ite_eq_left rfl, zero_add, pow_one]
      linear_combination -e
    · rw [ite_eq_right (by omega), ite_eq_right (by omega), ite_eq_right (by omega),
        pow_succ (-1 / (s : ℚ)) (n + 1)]
      linear_combination (-(-1 / (s : ℚ)) ^ (n + 1)) * e

theorem rbase_mem {s : ℤ} (hs0 : s ≠ 0) {D : ℕ} (hs : s.natAbs ∣ D) :
    rbase (s : ℚ) ∈ DInt (D : ℚ) := by
  rw [DInt_mem]
  intro n
  simp only [rbase, coeff_mk]
  split_ifs with hn
  · exact ⟨0, by simp⟩
  · have hsD : s ∣ (D : ℤ) := Int.natAbs_dvd.1 (Int.natCast_dvd_natCast.2 hs)
    obtain ⟨z, hz⟩ := hsD
    refine ⟨-(-z) ^ n, ?_⟩
    have hDq : (D : ℚ) = (s : ℚ) * (z : ℚ) := by exact_mod_cast hz
    have hs' : (s : ℚ) ≠ 0 := by exact_mod_cast hs0
    have e : (s : ℚ) * (z : ℚ) * (-1 / (s : ℚ)) = -(z : ℚ) := by field_simp
    rw [hDq, mul_neg, ← mul_pow, e]
    push_cast
    ring

/-- A `D_M`-integral solution of `RSpec (L+1) s` exists when `-M ≤ s` and `s + L ≤ M`. -/
theorem RSpec_exists (M L : ℕ) : ∀ s : ℤ, -(M : ℤ) ≤ s → s + L ≤ M →
    ∃ T ∈ DInt (Nat.lcmUpto M : ℚ), RSpec (L + 1) s T := by
  induction L with
  | zero =>
    intro s h1 h2
    by_cases hs : s = 0
    · subst hs
      exact ⟨1, one_mem _, RSpec_one_zero⟩
    · refine ⟨rbase (s : ℚ), rbase_mem hs (dvd_lcmUpto ?_ ?_), RSpec_one_rbase hs⟩
      · omega
      · omega
  | succ L ih =>
    intro s h1 h2
    obtain ⟨T₁, hT₁, hS₁⟩ := ih s h1 (by omega)
    obtain ⟨T₂, hT₂, hS₂⟩ := ih (s + 1) (by omega) (by omega)
    exact ⟨T₁ - T₂, sub_mem hT₁ hT₂, RSpec_rec hS₁ hS₂⟩

/-- `ratBrick a b k` solves `RSpec (b-a) (a-k)` (both branches of its definition). -/
theorem ratBrick_spec (a b k : ℕ) : RSpec (b - a) ((a : ℤ) - k) (ratBrick a b k) := by
  have hprod : ∏ j ∈ range (b - a), (C ((((a : ℤ) - k : ℤ) : ℚ) + j) + X) =
      ∏ i ∈ Ico a b, (C ((i : ℚ) - k) + X) := by
    rw [Finset.prod_Ico_eq_prod_range]
    refine Finset.prod_congr rfl fun j _ => ?_
    have e : (((a : ℤ) - k : ℤ) : ℚ) + (j : ℚ) = ((a + j : ℕ) : ℚ) - (k : ℚ) := by
      push_cast
      ring
    rw [e]
  have hcc : ∀ i : ℕ, constantCoeff (C ((i : ℚ) - k) + X) = (i : ℚ) - k := by
    intro i
    simp
  unfold RSpec
  rw [hprod]
  unfold ratBrick
  split_ifs with h
  · have hmem : k ∈ Ico a b := Finset.mem_Ico.2 h
    rw [← Finset.mul_prod_erase _ _ hmem]
    have hk : C ((k : ℚ) - k) + X = (X : PowerSeries ℚ) := by simp
    rw [hk]
    have hne : constantCoeff (∏ i ∈ (Ico a b).erase k, (C ((i : ℚ) - k) + X)) ≠ 0 := by
      rw [map_prod]
      refine Finset.prod_ne_zero_iff.2 fun i hi => ?_
      rw [hcc]
      have hik : i ≠ k := Finset.ne_of_mem_erase hi
      exact sub_ne_zero.2 (by exact_mod_cast hik)
    have hinv := PowerSeries.inv_mul_cancel _ hne
    linear_combination (C (((b - a - 1).factorial : ℚ)) * X) * hinv
  · have hne : constantCoeff (∏ i ∈ Ico a b, (C ((i : ℚ) - k) + X)) ≠ 0 := by
      rw [map_prod]
      refine Finset.prod_ne_zero_iff.2 fun i hi => ?_
      rw [hcc]
      have hik : i ≠ k := by
        rintro rfl
        exact h (Finset.mem_Ico.1 hi)
      exact sub_ne_zero.2 (by exact_mod_cast hik)
    have hinv := PowerSeries.inv_mul_cancel _ hne
    linear_combination (C (((b - a - 1).factorial : ℚ)) * X) * hinv

end BrickIntegral

open BrickIntegral in
theorem BrickInt_proof : Stmt_BrickInt where
  poly := by
    intro a b k i _hba
    rw [polyBrick_eq a b k]
    exact DInt_mem.1 (pb_mem (a - b) _) i
  rat := by
    intro a b k a0 b0 i ha0 hab hbb0 hk0 hkb0
    obtain ⟨T, hT, hS⟩ :=
      RSpec_exists (b0 - a0 - 1) (b - a - 1) ((a : ℤ) - k) (by omega) (by omega)
    have hL : b - a - 1 + 1 = b - a := by omega
    rw [hL] at hS
    rw [RSpec_unique (ratBrick_spec a b k) hS]
    exact DInt_mem.1 hT i

end ZetaWindow

end
