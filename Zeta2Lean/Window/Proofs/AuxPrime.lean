module

public import Zeta2Lean.Window.Statements

@[expose] public section

set_option linter.style.header false
set_option linter.style.longLine false

/-!
# Auxiliary-prime separation at `ℓ = 63n - 1` (Theorem N of docs/proof.md §2.2)

**Proves `Stmt_AuxPrime`** from `Stmt_LaurentSupp` and `Stmt_LaurentInt`: for all large `n` with
`ℓ := 63 n - 1` prime,
* `padicValRat ℓ (A0 cfgW n) < 0` (in fact `= -5`, `A0_val`), and
* `0 ≤ padicValRat ℓ (Acoef cfgW n s)` for every `s ∈ window cfgW`.

This replaces the former gap `Stmt_L20Nonzero` (`F̃_n ≠ 0` infinitely often, which needed the
saddle-point asymptotics).  `Window/Assembly.lean` turns it into the nonvanishing of `F̃_n` under the
rationality hypothesis (with Dirichlet's theorem).  Source: `docs/proof.md` §2.2 and
`docs/window/refine/aux-prime-nonvanishing.md` (Lemmas B–E, Theorem N with `c = 1`).  Dictionary:
docs/proof.md's `c₀ = -A0 cfgW n`, `c_s = Acoef cfgW n s`, `a_{i,k} = B cfgW n (i+5) k` (the coefficient
of `(t+k)^{-i}`); its `G_k(ε) = ε^{o_k} N_h R(-k+ε)` is `Gk cfgW n k / X^{18 - o_k}`.

**Status: done** (complete, kernel-checked; `#print axioms AuxPrime_proof`:
`[propext, Classical.choice, Quot.sound]`).  Of the four hypotheses only `Stmt_LaurentSupp` and
`Stmt_LaurentInt` are used; `Stmt_LaurentVal` and `Stmt_Harmonic` belong to the fixed signature.
The evenness of `n` is not used either (it follows from the primality of `63n - 1`).

## Numbers for `cfgW` (`n ≥ 2`)

`h₀ = 160n+2`, `h_j = η_j n + 1` with `η = (47,47,47,47,48,50,50,51,52,…,66)`;
`Krange = [h₁, h₀-h₁] = [47n+1, 113n+1]`; `B_{j,k} ≠ 0` only for `k ∈ [h_j, h₀-h_j] ⊆ [50n+1, 110n+1]`
(`Stmt_LaurentSupp`); `m0 cfgW n = max(h₅-1, h₀-2h₆) = 60n` (`m0W`).  The prime `ℓ = 63n - 1`
satisfies `60n < ℓ < 63n`.

## Proof as formalized (namespace `ZetaWindow.AuxPrime`)

0. **Infrastructure** (after the pair project's `NVq`): the subring `Zq ℓ` of `ℓ`-integral
   rationals, residues `HasRes ℓ x r` in `ZMod ℓ`, `ℓ`-units `IsU`, power series with `ℓ`-integral
   coefficients `ZqPS`, and `PSU` (`ZqPS` with a unit constant term; closed under `*`, `∏`, `⁻¹`).
1. **Lemma B** (`B_mem`, `Acoef_mem`).  `Stmt_LaurentInt` gives `D_{60n}^{23-j} B_{j,k} ∈ ℤ`, and
   `ℓ ∤ D_{60n} = Nat.lcmUpto (60n)` (`not_dvd_lcmUpto`, via `lcmUpto ∣ (60n)!`).  So every
   `B_{j,k}` and every `A_s = C(s-1,4) ∑_k B_{s+1,k}` is `ℓ`-integral: the second conjunct.
2. **Harmonic numbers.**  `harm_mem`: `H^{(s)}_N ∈ Z_(ℓ)` for `N < ℓ`; `harm_res`: for
   `ℓ ≤ N < 2ℓ`, `s ≥ 1`, `ℓ^s H^{(s)}_N ≡ 1 (mod ℓ)` (only `l = ℓ` is singular).
3. **Lemma C** (the top poles `k ∈ {110n, 110n+1}`).  `Gk_eq`: for `109n + 1 < k`, the sixteen
   rational bricks `j = 8, …, 23` take the `X · xBrick` branch of `ratBrick`, so `Gk = X^{16} V_k`
   (`Vk`); hence `B_{7,k} = V_k(0)`, `B_{6,k} = [X¹] V_k` (`B7_eq`, `B6_eq`).  `Vk_eq`: the factor
   `i = k + 1 - 63n` (`= 47n+1, 47n+2`) of `P₅ = polyBrick h₅ 1 k` is `C(-ℓ) + X`, so
   `V_k = (X - ℓ) U_k` (`Uk`).  `Uk_PSU`: every other linear constant `i - k` lies in
   `(-2ℓ, 2ℓ) ∖ {0, ±ℓ}` (`not_dvd_of_bounds`, by `omega` on the explicit ranges) and every factorial
   is `(≤ 60n)!`, so `U_k ∈ Z_(ℓ)⟦ε⟧` with `u_k := U_k(0)` a unit.  `top_data`:
   `B_{7,k} = -ℓ u_k`, `B_{6,k} = u_k - ℓ U_k'(0)`.
4. **Lemma D** (`A0_res`).  In `ℓ⁵ A₀ = ∑_{j=6}^{23} C(j-2,4) ∑_k ℓ⁵ B_{j,k} H^{(j-1)}_{k-h₁}` every
   term with `k < 110n` is `ℓ · (ℓ-integral)`, and every term with `k > h₀ - h_j` vanishes
   (`term_zero`); what is left are `j ∈ {6, 7}` at `k ∈ {110n, 110n+1}` (`k - h₁ ∈ {ℓ, ℓ+1}`):
   `top6` (`≡ u_k`) and `top7` (`≡ -u_k`), so `ℓ⁵ A₀ ≡ C(4,4)(u₁+u₂) - C(5,4)(u₁+u₂) = -4(u₁+u₂)`.
5. **Lemma E** (`Vk_shift`, exact in `ℚ`).  Shifting every brick product by one
   (`shift_Ico`, `shift_erase` and the brick versions `polyBrick_shift`, `ratBrick_shift`,
   `xBrick_shift`; the intervals of `j ≤ 7` contain both poles, those of `j ≥ 8` neither) gives
   `V_{110n}(0) · Dpoly(n) = V_{110n+1}(0) · Npoly(n)`, i.e. `u₁ Dpoly(n) = u₂ Npoly(n)`, where
   `Dpoly`, `Npoly` are the products of the 29 shift factors `(h₀-2k)(1-k)⁵ ∏(h₀-h_j+1-k)` and
   `(h₀-2k+2)(h₀-k)⁵ ∏(h_j-k)` at `k = 110n+1` (so `ρ(110n+1) = Npoly/Dpoly`).
6. **Reduction modulo `ℓ`** (`res_sum_ne`).  In `ZMod ℓ`, `63 n = 1`, so every factor `αn + β` is
   `(α + 63β) n` and `Dpoly(n) = Dconst · n^{29}`, `Npoly(n) = Nconst · n^{29}` (`Dpoly_eval`,
   `Npoly_eval`), with the integers (`decide`) `Dconst = 63^{29} Dpoly(1/63)` and
   `Nconst = 63^{29} Npoly(1/63)`.  Their sum is
   `Dconst + Nconst = 17238229314307001757455123952577000881432133632000000`
   `= 2^21·3^16·5^6·7^5·11^3·13·17·19·29·31·47·53·59·984698059590803 = Dconst · Q₁`
   (`Q₁ = 984698059590803/1545332660300000` of the informal proof).  If `u₁ + u₂ ≡ 0`, then
   `u₂ (Dconst + Nconst) ≡ 0`, impossible for `ℓ > Dconst + Nconst` since `u₂` is a unit.
7. **Conclusion** (`A0_val`).  `ℓ⁵ A₀ ≡ -4 (u₁ + u₂) ≢ 0`, so `v_ℓ(ℓ⁵ A₀) = 0` and
   `v_ℓ(A₀) = -5`.  `AuxPrime_proof` takes `n ≥ Dconst + Nconst` (then `ℓ = 63n - 1` exceeds it);
   informally there is no exceptional `n` at all (docs/proof.md), but the eventual statement makes a
   primality certificate unnecessary.

**Lean pitfall (worth knowing for other `ZMod p` proofs in this Mathlib).**  Type-class synthesis
of `Neg (ZMod ℓ)` (with `Fact ℓ.Prime`) finds the instance
`instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent` (`Mathlib/GroupTheory/Nilpotent.lean`), which
`ring` does not see through, so `ring`/`linear_combination` then fail on goals with a literal
`-x`, `x : ZMod ℓ`.  This file never writes such a negation: negative residues are casts
`((-u : ℚ) : ZMod ℓ)`, `((-4 : ℤ) : ZMod ℓ)`, which `push_cast` turns into the ring's `-`.

**Numerical check.**  `python/window_mirror.py --aux` (section "Stmt_AuxPrime"): the literal exact
`A0 cfgW n`, `Acoef cfgW n s` at `n = 4` (`ℓ = 251`) and `n = 8` (`ℓ = 503`) give `v_ℓ(A0) = -5` and
`v_ℓ(A_7, A_9, …, A_21) = (1, 1, 0, 0, 2, 4, 8, 10)`; the `ℓ`-adic evaluation gives the same for
every even `n ≤ 60` with `63n - 1` prime.  `(Dconst + Nconst)/Dconst` equals the `Q₁` of docs/proof.md
(recomputed with Python `fractions`).
-/

open Filter Topology Finset PowerSeries

noncomputable section

namespace ZetaWindow

namespace AuxPrime

/-! ### `ℓ`-integral rationals and residues modulo `ℓ` (after the pair project's `NVq`) -/

variable {L : ℕ} [hLP : Fact L.Prime]

/-- The `ℓ`-integral rationals (`ℓ ∤ den`), a subring of `ℚ`. -/
def Zq (L : ℕ) [Fact L.Prime] : Subring ℚ where
  carrier := {x | ¬ L ∣ x.den}
  mul_mem' {a b} ha hb h := by
    rcases (Nat.Prime.dvd_mul (Fact.out : L.Prime)).1 (h.trans (Rat.mul_den_dvd a b)) with h' | h'
    · exact ha h'
    · exact hb h'
  one_mem' := by
    change ¬ L ∣ (1 : ℚ).den
    rw [Rat.den_one]
    exact (Fact.out : L.Prime).not_dvd_one
  add_mem' {a b} ha hb h := by
    rcases (Nat.Prime.dvd_mul (Fact.out : L.Prime)).1 (h.trans (Rat.add_den_dvd a b)) with h' | h'
    · exact ha h'
    · exact hb h'
  zero_mem' := by
    change ¬ L ∣ (0 : ℚ).den
    rw [Rat.den_zero]
    exact (Fact.out : L.Prime).not_dvd_one
  neg_mem' {a} ha := by
    change ¬ L ∣ (-a).den
    rw [Rat.den_neg_eq_den]
    exact ha

theorem mem_Zq {x : ℚ} : x ∈ Zq L ↔ ¬ L ∣ x.den := Iff.rfl

theorem Zq_int (z : ℤ) : (z : ℚ) ∈ Zq L := intCast_mem _ z

theorem Zq_nat (k : ℕ) : (k : ℚ) ∈ Zq L := natCast_mem _ k

theorem Zq_inv_int {z : ℤ} (hz : ¬ (L : ℤ) ∣ z) : (z : ℚ)⁻¹ ∈ Zq L := by
  rw [mem_Zq, Rat.inv_intCast_den]
  split_ifs with h0
  · exact (Fact.out : L.Prime).not_dvd_one
  · intro h
    exact hz (Int.natCast_dvd.2 h)

theorem den_cast_ne {x : ℚ} (hx : x ∈ Zq L) : ((x.den : ℕ) : ZMod L) ≠ 0 := by
  rw [Ne, ZMod.natCast_eq_zero_iff]
  exact hx

theorem res_add {x y : ℚ} (hx : x ∈ Zq L) (hy : y ∈ Zq L) :
    ((x + y : ℚ) : ZMod L) = (x : ZMod L) + (y : ZMod L) :=
  Rat.cast_add_of_ne_zero (den_cast_ne hx) (den_cast_ne hy)

theorem res_mul {x y : ℚ} (hx : x ∈ Zq L) (hy : y ∈ Zq L) :
    ((x * y : ℚ) : ZMod L) = (x : ZMod L) * (y : ZMod L) :=
  Rat.cast_mul_of_ne_zero (den_cast_ne hx) (den_cast_ne hy)

theorem res_int (z : ℤ) : (((z : ℚ)) : ZMod L) = (z : ZMod L) := Rat.cast_intCast z

/-- `x` is `ℓ`-integral with residue `r`. -/
def HasRes (L : ℕ) [Fact L.Prime] (x : ℚ) (r : ZMod L) : Prop :=
  x ∈ Zq L ∧ (x : ZMod L) = r

theorem HasRes.add {x y : ℚ} {r s : ZMod L} (hx : HasRes L x r) (hy : HasRes L y s) :
    HasRes L (x + y) (r + s) :=
  ⟨add_mem hx.1 hy.1, by rw [res_add hx.1 hy.1, hx.2, hy.2]⟩

theorem HasRes.mul {x y : ℚ} {r s : ZMod L} (hx : HasRes L x r) (hy : HasRes L y s) :
    HasRes L (x * y) (r * s) :=
  ⟨mul_mem hx.1 hy.1, by rw [res_mul hx.1 hy.1, hx.2, hy.2]⟩


theorem HasRes.of_mem {x : ℚ} (hx : x ∈ Zq L) : HasRes L x (x : ZMod L) := ⟨hx, rfl⟩

theorem HasRes.nat (k : ℕ) : HasRes L (k : ℚ) (k : ZMod L) :=
  ⟨Zq_nat k, Rat.cast_natCast k⟩

theorem HasRes.zero : HasRes L 0 0 := ⟨zero_mem _, by simp⟩

theorem HasRes.congr {x y : ℚ} {r s : ZMod L} (hx : HasRes L x r) (hxy : x = y) (hrs : r = s) :
    HasRes L y s := hxy ▸ hrs ▸ hx

theorem HasRes.sum {ι : Type*} (s : Finset ι) (f : ι → ℚ) (r : ι → ZMod L)
    (hf : ∀ i ∈ s, HasRes L (f i) (r i)) : HasRes L (∑ i ∈ s, f i) (∑ i ∈ s, r i) := by
  classical
  induction s using Finset.induction_on with
  | empty => exact ⟨zero_mem _, by simp⟩
  | insert a s ha ih =>
    rw [Finset.sum_insert ha, Finset.sum_insert ha]
    exact (hf a (mem_insert_self a s)).add (ih fun i hi => hf i (mem_insert_of_mem hi))

/-- A sum all of whose terms have residue `0`. -/
theorem HasRes.sum_zero {ι : Type*} (s : Finset ι) (f : ι → ℚ)
    (hf : ∀ i ∈ s, HasRes L (f i) 0) : HasRes L (∑ i ∈ s, f i) 0 :=
  (HasRes.sum s f (fun _ => 0) hf).congr rfl (by simp)

/-- `ℓ · z` has residue `0` for `ℓ`-integral `z`. -/
theorem HasRes.L_mul {z : ℚ} (hz : z ∈ Zq L) : HasRes L ((L : ℚ) * z) 0 := by
  have := (HasRes.nat (L := L) L).mul (HasRes.of_mem hz)
  rwa [ZMod.natCast_self, zero_mul] at this

theorem num_not_dvd {x : ℚ} (hr : (x : ZMod L) ≠ 0) : ¬ (L : ℤ) ∣ x.num := by
  intro h
  apply hr
  rw [Rat.cast_def, (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).2 h, zero_div]

theorem Zq_inv_of_res {x : ℚ} (hr : (x : ZMod L) ≠ 0) : x⁻¹ ∈ Zq L := by
  have hx : x⁻¹ = ((x.den : ℤ) : ℚ) * (((x.num : ℤ) : ℚ))⁻¹ := by
    conv_lhs => rw [← Rat.num_div_den x]
    rw [inv_div, div_eq_mul_inv]
    push_cast
    rfl
  rw [hx]
  exact mul_mem (Zq_int _) (Zq_inv_int (num_not_dvd hr))

theorem pv_nonneg {x : ℚ} (hx : x ∈ Zq L) : 0 ≤ padicValRat L x := by
  rw [padicValRat_def, padicValNat.eq_zero_of_not_dvd hx]
  simp

theorem pv_eq_zero {x : ℚ} (hx : x ∈ Zq L) (hr : (x : ZMod L) ≠ 0) : padicValRat L x = 0 := by
  rw [padicValRat_def, padicValNat.eq_zero_of_not_dvd hx,
    padicValInt.eq_zero_of_not_dvd (num_not_dvd hr)]
  simp

/-! ### `ℓ`-adic units -/

/-- `x` is an `ℓ`-adic unit. -/
def IsU (L : ℕ) [Fact L.Prime] (x : ℚ) : Prop := x ∈ Zq L ∧ (x : ZMod L) ≠ 0

theorem IsU.mul {x y : ℚ} (hx : IsU L x) (hy : IsU L y) : IsU L (x * y) :=
  ⟨mul_mem hx.1 hy.1, by rw [res_mul hx.1 hy.1]; exact mul_ne_zero hx.2 hy.2⟩

theorem IsU.ne_zero {x : ℚ} (hx : IsU L x) : x ≠ 0 := by
  rintro rfl
  exact hx.2 (by simp)

theorem IsU.inv {x : ℚ} (hx : IsU L x) : IsU L x⁻¹ := by
  refine ⟨Zq_inv_of_res hx.2, ?_⟩
  intro h
  have := res_mul hx.1 (Zq_inv_of_res hx.2)
  rw [mul_inv_cancel₀ hx.ne_zero, h, mul_zero, Rat.cast_one] at this
  exact one_ne_zero this

theorem IsU.int {z : ℤ} (hz : ¬ (L : ℤ) ∣ z) : IsU L (z : ℚ) :=
  ⟨Zq_int z, by rw [res_int, Ne, ZMod.intCast_zmod_eq_zero_iff_dvd]; exact hz⟩

/-- A difference of naturals prime to `ℓ` is an `ℓ`-adic unit. -/
theorem IsU.sub_nat {i k : ℕ} (h : ¬ (L : ℤ) ∣ ((i : ℤ) - k)) : IsU L ((i : ℚ) - k) := by
  have e : ((i : ℚ) - k) = (((i : ℤ) - k : ℤ) : ℚ) := by push_cast; ring
  rw [e]
  exact IsU.int h

/-- `m!` is an `ℓ`-adic unit for `m < ℓ`. -/
theorem IsU.fact {m : ℕ} (hm : m < L) : IsU L ((m.factorial : ℕ) : ℚ) := by
  have e : ((m.factorial : ℕ) : ℚ) = (((m.factorial : ℕ) : ℤ) : ℚ) := by push_cast; rfl
  rw [e]
  refine IsU.int ?_
  intro h
  have h' : L ∣ m.factorial := Int.natCast_dvd_natCast.1 h
  exact absurd ((Nat.Prime.dvd_factorial (Fact.out : L.Prime)).1 h') (not_le.2 hm)

theorem IsU.one_div_fact {m : ℕ} (hm : m < L) : IsU L (1 / ((m.factorial : ℕ) : ℚ)) := by
  rw [one_div]
  exact (IsU.fact hm).inv

/-- An integer in `(-2ℓ, 2ℓ)` other than `0, ±ℓ` is prime to `ℓ`. -/
theorem not_dvd_of_bounds {z : ℤ} (h1 : -(2 * (L : ℤ)) < z) (h2 : z < 2 * (L : ℤ)) (h3 : z ≠ 0)
    (h4 : z ≠ L) (h5 : z ≠ -(L : ℤ)) : ¬ (L : ℤ) ∣ z := by
  rintro ⟨t, rfl⟩
  have hL0 : (0 : ℤ) < L := by exact_mod_cast (Fact.out : L.Prime).pos
  have ht1 : -2 < t := by nlinarith
  have ht2 : t < 2 := by nlinarith
  interval_cases t <;> simp_all

/-! ### Power series with `ℓ`-integral coefficients -/

/-- Power series over `ℚ` with `ℓ`-integral coefficients. -/
def ZqPS (L : ℕ) [Fact L.Prime] : Subring (PowerSeries ℚ) :=
  (PowerSeries.map (Zq L).subtype).range

theorem mem_ZqPS {F : PowerSeries ℚ} : F ∈ ZqPS L ↔ ∀ j, coeff j F ∈ Zq L := by
  constructor
  · rintro ⟨F', rfl⟩ j
    rw [coeff_map]
    exact (coeff j F').2
  · intro h
    refine ⟨PowerSeries.mk fun j => ⟨coeff j F, h j⟩, ?_⟩
    ext j
    simp [coeff_map]

theorem C_mem {a : ℚ} (ha : a ∈ Zq L) : C a ∈ ZqPS L := by
  rw [mem_ZqPS]
  intro j
  rw [coeff_C]
  split_ifs
  · exact ha
  · exact zero_mem _

theorem X_mem : (X : PowerSeries ℚ) ∈ ZqPS L := by
  rw [mem_ZqPS]
  intro j
  rw [coeff_X]
  split_ifs
  · exact one_mem _
  · exact zero_mem _

theorem inv_mem {F : PowerSeries ℚ} (hF : F ∈ ZqPS L) (h0 : constantCoeff F ≠ 0)
    (h0' : (constantCoeff F)⁻¹ ∈ Zq L) : F⁻¹ ∈ ZqPS L := by
  obtain ⟨G, rfl⟩ := hF
  have hc : ((constantCoeff G : Zq L) : ℚ) = constantCoeff (PowerSeries.map (Zq L).subtype G) := by
    rw [← coeff_zero_eq_constantCoeff_apply, ← coeff_zero_eq_constantCoeff_apply, coeff_map]
    rfl
  let u : (Zq L)ˣ :=
    { val := constantCoeff G
      inv := ⟨(constantCoeff (PowerSeries.map (Zq L).subtype G))⁻¹, h0'⟩
      val_inv := Subtype.ext (by
        change ((constantCoeff G : Zq L) : ℚ) * _ = 1
        rw [hc, mul_inv_cancel₀ h0])
      inv_val := Subtype.ext (by
        change _ * ((constantCoeff G : Zq L) : ℚ) = 1
        rw [hc, inv_mul_cancel₀ h0]) }
  refine ⟨invOfUnit G u, ?_⟩
  rw [eq_comm, PowerSeries.inv_eq_iff_mul_eq_one h0, ← map_mul, invOfUnit_mul G u rfl, map_one]

/-- A power series with `ℓ`-integral coefficients and unit constant term. -/
def PSU (L : ℕ) [Fact L.Prime] (F : PowerSeries ℚ) : Prop :=
  F ∈ ZqPS L ∧ IsU L (constantCoeff F)

theorem PSU.mul {F G : PowerSeries ℚ} (hF : PSU L F) (hG : PSU L G) : PSU L (F * G) :=
  ⟨mul_mem hF.1 hG.1, by rw [map_mul]; exact hF.2.mul hG.2⟩

theorem PSU.prod {ι : Type*} (s : Finset ι) (f : ι → PowerSeries ℚ) (hf : ∀ i ∈ s, PSU L (f i)) :
    PSU L (∏ i ∈ s, f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => exact ⟨one_mem _, by rw [prod_empty, map_one]; exact ⟨one_mem _, by simp⟩⟩
  | insert a s ha ih =>
    rw [Finset.prod_insert ha]
    exact (hf a (mem_insert_self a s)).mul (ih fun i hi => hf i (mem_insert_of_mem hi))

theorem PSU.inv {F : PowerSeries ℚ} (hF : PSU L F) : PSU L F⁻¹ :=
  ⟨inv_mem hF.1 hF.2.ne_zero hF.2.inv.1, by rw [constantCoeff_inv]; exact hF.2.inv⟩

theorem PSU.const {a : ℚ} (ha : IsU L a) : PSU L (C a) :=
  ⟨C_mem ha.1, by rw [constantCoeff_C]; exact ha⟩

theorem PSU.lin1 {a : ℚ} (ha : IsU L a) : PSU L (C a + X) :=
  ⟨add_mem (C_mem ha.1) X_mem, by simpa using ha⟩

theorem PSU.lin2 {a : ℚ} (ha : IsU L a) : PSU L (C a + C 2 * X) := by
  refine ⟨add_mem (C_mem ha.1) (mul_mem (C_mem ?_) X_mem), by simpa using ha⟩
  exact_mod_cast Zq_nat 2

theorem PSU.prod_lin (S : Finset ℕ) (k : ℕ) (hS : ∀ i ∈ S, ¬ (L : ℤ) ∣ ((i : ℤ) - k)) :
    PSU L (∏ i ∈ S, (C ((i : ℚ) - k) + X)) :=
  PSU.prod _ _ fun i hi => PSU.lin1 (IsU.sub_nat (hS i hi))

theorem HasRes.one : HasRes L 1 1 := ⟨one_mem _, by simp⟩

/-! ### Integrality from a denominator prime to `ℓ`; harmonic numbers -/

/-- A prime `ℓ > m` does not divide `D_m = lcm(1, …, m)`. -/
theorem not_dvd_lcmUpto {m : ℕ} (hm : m < L) : ¬ L ∣ Nat.lcmUpto m := fun h =>
  absurd ((Nat.Prime.dvd_factorial (Fact.out : L.Prime)).1 (h.trans (Nat.lcmUpto_dvd_factorial m)))
    (not_le.2 hm)

/-- `D^e x ∈ ℤ` with `ℓ ∤ D` makes `x` an `ℓ`-integral rational. -/
theorem mem_of_int {D e : ℕ} (hD : ¬ L ∣ D) {x : ℚ} (h : ∃ z : ℤ, (D : ℚ) ^ e * x = z) :
    x ∈ Zq L := by
  obtain ⟨z, hz⟩ := h
  have hD0 : (D : ℚ) ≠ 0 := by
    intro h0
    apply hD
    rw [Nat.cast_eq_zero.1 h0]
    exact dvd_zero L
  have hx : x = (((D ^ e : ℕ) : ℤ) : ℚ)⁻¹ * (z : ℚ) := by
    rw [← hz]
    push_cast
    rw [← mul_assoc, inv_mul_cancel₀ (pow_ne_zero _ hD0), one_mul]
  rw [hx]
  refine mul_mem (Zq_inv_int ?_) (Zq_int z)
  intro h
  exact hD ((Fact.out : L.Prime).dvd_of_dvd_pow (Int.natCast_dvd_natCast.1 h))

/-- `1/l^s` is `ℓ`-integral when `ℓ ∤ l`. -/
theorem inv_pow_mem {l : ℕ} (s : ℕ) (hl : ¬ L ∣ l) : 1 / (l : ℚ) ^ s ∈ Zq L := by
  have e : (1 / (l : ℚ) ^ s) = ((((l ^ s : ℕ) : ℤ) : ℚ))⁻¹ := by push_cast; rw [one_div]
  rw [e]
  refine Zq_inv_int ?_
  intro h
  exact hl ((Fact.out : L.Prime).dvd_of_dvd_pow (Int.natCast_dvd_natCast.1 h))

/-- `H^{(s)}_N` is `ℓ`-integral for `N < ℓ`. -/
theorem harm_mem {N : ℕ} (s : ℕ) (hN : N < L) : harm N s ∈ Zq L := by
  unfold harm
  refine sum_mem fun l hl => inv_pow_mem s ?_
  have hl' := mem_Icc.1 hl
  intro h
  have := Nat.le_of_dvd (by omega) h
  omega

/-- For `ℓ ≤ N < 2ℓ` and `s ≥ 1`: `ℓ^s H^{(s)}_N ≡ 1 (mod ℓ)` (only the term `l = ℓ` is singular). -/
theorem harm_res {N s : ℕ} (hs : 1 ≤ s) (h1 : L ≤ N) (h2 : N < 2 * L) :
    HasRes L ((L : ℚ) ^ s * harm N s) 1 := by
  have hL0 : (L : ℚ) ≠ 0 := by exact_mod_cast (Fact.out : L.Prime).ne_zero
  have hL2 : 2 ≤ L := (Fact.out : L.Prime).two_le
  have hmem : L ∈ Icc 1 N := mem_Icc.2 ⟨by omega, h1⟩
  have hrest : ∑ l ∈ (Icc 1 N).erase L, 1 / (l : ℚ) ^ s ∈ Zq L := by
    refine sum_mem fun l hl => inv_pow_mem s ?_
    have hl1 := mem_erase.1 hl
    have hl2 := mem_Icc.1 hl1.2
    rintro ⟨t, ht⟩
    have ht2 : t < 2 := by
      by_contra hcon
      have : L * 2 ≤ L * t := Nat.mul_le_mul_left L (by omega)
      omega
    interval_cases t <;> omega
  unfold harm
  rw [← add_sum_erase _ _ hmem]
  have hpow : (L : ℚ) ^ s = L * L ^ (s - 1) := by
    rw [← pow_succ']
    congr 1
    omega
  have e : (L : ℚ) ^ s * (1 / (L : ℚ) ^ s + ∑ l ∈ (Icc 1 N).erase L, 1 / (l : ℚ) ^ s) =
      1 + (L : ℚ) * ((L : ℚ) ^ (s - 1) * ∑ l ∈ (Icc 1 N).erase L, 1 / (l : ℚ) ^ s) := by
    rw [mul_add, mul_one_div_cancel (pow_ne_zero _ hL0), hpow]
    ring
  rw [e]
  exact (HasRes.one.add (HasRes.L_mul (mul_mem (pow_mem (Zq_nat L) _) hrest))).congr rfl (by simp)

/-! ### Brick algebra: constant terms and the shift `k ↦ k + 1` -/

/-- The rational brick `(b-a-1)!/((t+a)⋯(t+b-1))` at `t = -k` outside its pole range (i.e.
`ratBrick a b k` without its factor `ε`). -/
def xBrick (a b k : ℕ) : PowerSeries ℚ :=
  C ((b - a - 1).factorial : ℚ) * (∏ i ∈ Ico a b, (C ((i : ℚ) - k) + X))⁻¹

theorem ratBrick_else {a b k : ℕ} (h : ¬ (a ≤ k ∧ k < b)) : ratBrick a b k = X * xBrick a b k := by
  rw [ratBrick, ite_eq_right h, xBrick]
  ring

theorem ratBrick_unit {a b k : ℕ} (h : a ≤ k ∧ k < b) :
    ratBrick a b k =
      C ((b - a - 1).factorial : ℚ) * (∏ i ∈ (Ico a b).erase k, (C ((i : ℚ) - k) + X))⁻¹ := by
  rw [ratBrick, ite_eq_left h]

theorem cc_prod_lin (S : Finset ℕ) (k : ℕ) :
    constantCoeff (∏ i ∈ S, (C ((i : ℚ) - k) + X)) = ∏ i ∈ S, ((i : ℚ) - k) := by
  rw [map_prod]
  simp

theorem cc_polyBrick (a b k : ℕ) :
    constantCoeff (polyBrick a b k) = 1 / ((a - b).factorial : ℚ) * ∏ i ∈ Ico b a, ((i : ℚ) - k) := by
  rw [polyBrick, map_mul, constantCoeff_C, cc_prod_lin]

theorem cc_ratBrick_unit {a b k : ℕ} (h : a ≤ k ∧ k < b) :
    constantCoeff (ratBrick a b k) =
      ((b - a - 1).factorial : ℚ) * (∏ i ∈ (Ico a b).erase k, ((i : ℚ) - k))⁻¹ := by
  rw [ratBrick_unit h, map_mul, constantCoeff_C, constantCoeff_inv, cc_prod_lin]

theorem cc_xBrick (a b k : ℕ) :
    constantCoeff (xBrick a b k) = ((b - a - 1).factorial : ℚ) * (∏ i ∈ Ico a b, ((i : ℚ) - k))⁻¹ := by
  rw [xBrick, map_mul, constantCoeff_C, constantCoeff_inv, cc_prod_lin]

/-- Telescoping of consecutive linear factors under `k ↦ k + 1`. -/
theorem shift_Ico (a b k : ℕ) (hab : a ≤ b) :
    (∏ i ∈ Ico a b, ((i : ℚ) - k)) * ((a : ℚ) - (k + 1)) =
      (∏ i ∈ Ico a b, ((i : ℚ) - (k + 1))) * ((b : ℚ) - (k + 1)) := by
  induction b, hab using Nat.le_induction with
  | base => simp
  | succ b hab ih =>
    rw [prod_Ico_succ_top hab, prod_Ico_succ_top hab]
    push_cast
    linear_combination ((b : ℚ) - k) * ih

/-- The same with the pole factor (`i = k`, resp. `i = k + 1`) removed. -/
theorem shift_erase (a b k : ℕ) (ha : a ≤ k) (hb : k + 1 < b) :
    (∏ i ∈ (Ico a b).erase k, ((i : ℚ) - k)) * ((a : ℚ) - (k + 1)) =
      (∏ i ∈ (Ico a b).erase (k + 1), ((i : ℚ) - (k + 1))) * ((b : ℚ) - (k + 1)) := by
  have e1 : (Ico a b).erase k = Ico a k ∪ Ico (k + 1) b := by
    ext i
    simp only [mem_erase, mem_Ico, mem_union]
    omega
  have e2 : (Ico a b).erase (k + 1) = Ico a (k + 1) ∪ Ico (k + 1 + 1) b := by
    ext i
    simp only [mem_erase, mem_Ico, mem_union]
    omega
  have d1 : Disjoint (Ico a k) (Ico (k + 1) b) := by
    rw [disjoint_left]
    intro i h1 h2
    rw [mem_Ico] at h1 h2
    omega
  have d2 : Disjoint (Ico a (k + 1)) (Ico (k + 1 + 1) b) := by
    rw [disjoint_left]
    intro i h1 h2
    rw [mem_Ico] at h1 h2
    omega
  rw [e1, e2, prod_union d1, prod_union d2, prod_Ico_succ_top ha,
    prod_eq_prod_Ico_succ_bot (show k + 1 < b by omega)]
  have h1 := shift_Ico a k k ha
  have h2 := shift_Ico (k + 1 + 1) b k (by omega)
  push_cast at h1 h2 ⊢
  linear_combination (∏ i ∈ Ico (k + 1 + 1) b, ((i : ℚ) - k)) * h1 -
    (∏ i ∈ Ico a k, ((i : ℚ) - (k + 1))) * h2

theorem inv_shift {f P Q dA dB : ℚ} (hP : P ≠ 0) (hQ : Q ≠ 0) (h : P * dA = Q * dB) :
    f * P⁻¹ * dB = f * Q⁻¹ * dA := by
  calc f * P⁻¹ * dB = f * P⁻¹ * dB * (Q * Q⁻¹) := by rw [mul_inv_cancel₀ hQ, mul_one]
    _ = f * Q⁻¹ * (Q * dB) * P⁻¹ := by ring
    _ = f * Q⁻¹ * (P * dA) * P⁻¹ := by rw [h]
    _ = f * Q⁻¹ * dA * (P * P⁻¹) := by ring
    _ = f * Q⁻¹ * dA := by rw [mul_inv_cancel₀ hP, mul_one]

theorem polyBrick_shift (a b k : ℕ) (hba : b ≤ a) :
    constantCoeff (polyBrick a b k) * ((b : ℚ) - (k + 1)) =
      constantCoeff (polyBrick a b (k + 1)) * ((a : ℚ) - (k + 1)) := by
  rw [cc_polyBrick, cc_polyBrick, mul_assoc, mul_assoc]
  congr 1
  push_cast
  exact shift_Ico b a k hba

theorem ratBrick_shift (a b k : ℕ) (ha : a ≤ k) (hb : k + 1 < b) :
    constantCoeff (ratBrick a b k) * ((b : ℚ) - (k + 1)) =
      constantCoeff (ratBrick a b (k + 1)) * ((a : ℚ) - (k + 1)) := by
  rw [cc_ratBrick_unit ⟨ha, by omega⟩, cc_ratBrick_unit ⟨by omega, hb⟩]
  have hP : ∏ i ∈ (Ico a b).erase k, ((i : ℚ) - k) ≠ 0 :=
    prod_ne_zero_iff.2 fun i hi => sub_ne_zero.2 (by exact_mod_cast ne_of_mem_erase hi)
  have hQ : ∏ i ∈ (Ico a b).erase (k + 1), ((i : ℚ) - ((k + 1 : ℕ) : ℚ)) ≠ 0 :=
    prod_ne_zero_iff.2 fun i hi => sub_ne_zero.2 (by exact_mod_cast ne_of_mem_erase hi)
  have h := shift_erase a b k ha hb
  push_cast at hQ ⊢
  exact inv_shift hP hQ h

theorem xBrick_shift (a b k : ℕ) (hab : a ≤ b) (hbk : b ≤ k) :
    constantCoeff (xBrick a b k) * ((b : ℚ) - (k + 1)) =
      constantCoeff (xBrick a b (k + 1)) * ((a : ℚ) - (k + 1)) := by
  rw [cc_xBrick, cc_xBrick]
  have hP : ∏ i ∈ Ico a b, ((i : ℚ) - k) ≠ 0 := by
    refine prod_ne_zero_iff.2 fun i hi => sub_ne_zero.2 ?_
    have := (mem_Ico.1 hi).2
    exact_mod_cast (show i ≠ k by omega)
  have hQ : ∏ i ∈ Ico a b, ((i : ℚ) - ((k + 1 : ℕ) : ℚ)) ≠ 0 := by
    refine prod_ne_zero_iff.2 fun i hi => sub_ne_zero.2 ?_
    have := (mem_Ico.1 hi).2
    exact_mod_cast (show i ≠ k + 1 by omega)
  have h := shift_Ico a b k hab
  push_cast at hQ ⊢
  exact inv_shift hP hQ h

/-- Multiplying two shift identities. -/
theorem mul_shift {x' x d e y' y d2 e2 : ℚ} (h1 : x' * d = x * e) (h2 : y' * d2 = y * e2) :
    (x' * y') * (d * d2) = (x * y) * (e * e2) := by
  calc (x' * y') * (d * d2) = (x' * d) * (y' * d2) := by ring
    _ = (x * e) * (y * e2) := by rw [h1, h2]
    _ = (x * y) * (e * e2) := by ring

/-- Multiplying a family of shift identities. -/
theorem prod_shift {s : Finset ℕ} {f' f d e : ℕ → ℚ} (h : ∀ j ∈ s, f' j * d j = f j * e j) :
    (∏ j ∈ s, f' j) * (∏ j ∈ s, d j) = (∏ j ∈ s, f j) * ∏ j ∈ s, e j := by
  rw [← prod_mul_distrib, ← prod_mul_distrib]
  exact prod_congr rfl h

theorem PSU_polyBrick {a b k : ℕ} (hab : a - b < L)
    (hS : ∀ i ∈ Ico b a, ¬ (L : ℤ) ∣ ((i : ℤ) - k)) : PSU L (polyBrick a b k) := by
  rw [polyBrick]
  exact PSU.mul (PSU.const (IsU.one_div_fact hab)) (PSU.prod_lin _ _ hS)

theorem PSU_ratBrick_unit {a b k : ℕ} (h : a ≤ k ∧ k < b) (hf : b - a - 1 < L)
    (hS : ∀ i ∈ (Ico a b).erase k, ¬ (L : ℤ) ∣ ((i : ℤ) - k)) : PSU L (ratBrick a b k) := by
  rw [ratBrick_unit h]
  exact PSU.mul (PSU.const (IsU.fact hf)) (PSU.prod_lin _ _ hS).inv

theorem PSU_xBrick {a b k : ℕ} (hf : b - a - 1 < L)
    (hS : ∀ i ∈ Ico a b, ¬ (L : ℤ) ∣ ((i : ℤ) - k)) : PSU L (xBrick a b k) := by
  rw [xBrick]
  exact PSU.mul (PSU.const (IsU.fact hf)) (PSU.prod_lin _ _ hS).inv

theorem coeff0_lin_mul (a : ℚ) (U : PowerSeries ℚ) :
    constantCoeff ((C a + X) * U) = a * constantCoeff U := by
  simp

theorem coeff1_lin_mul (a : ℚ) (U : PowerSeries ℚ) :
    coeff 1 ((C a + X) * U) = a * coeff 1 U + coeff 0 U := by
  rw [add_mul, map_add, coeff_C_mul, coeff_succ_X_mul]

/-! ### The window configuration `cfgW` -/

theorem h0W (n : ℕ) : cfgW.h0 n = 160 * n + 2 := rfl

theorem hW (n j : ℕ) : cfgW.h n j = etaW j * n + 1 := rfl

theorem etaW_small {j : ℕ} (hj : j ≤ 4) : etaW j = 47 := by
  unfold etaW
  rw [ite_eq_left hj]

theorem etaW_big {j : ℕ} (hj : 8 ≤ j) : etaW j = j + 43 := by
  unfold etaW
  split_ifs <;> omega

theorem etaW_le {j : ℕ} (hj : j ≤ 23) : etaW j ≤ 66 := by
  unfold etaW
  split_ifs <;> omega

theorem h1W (n : ℕ) : cfgW.h n 1 = 47 * n + 1 := rfl

theorem h5W (n : ℕ) : cfgW.h n 5 = 48 * n + 1 := rfl

theorem h6W (n : ℕ) : cfgW.h n 6 = 50 * n + 1 := rfl

theorem h7W (n : ℕ) : cfgW.h n 7 = 50 * n + 1 := rfl

theorem h_small {n j : ℕ} (hj : j ∈ Icc 1 4) : cfgW.h n j = 47 * n + 1 := by
  rw [hW, etaW_small (mem_Icc.1 hj).2]

/-- `51n + 1 ≤ h_j ≤ 66n + 1` for the sixteen rational bricks `j = 8, …, 23`. -/
theorem h_big {n j : ℕ} (hj : j ∈ Icc 8 23) :
    51 * n + 1 ≤ cfgW.h n j ∧ cfgW.h n j ≤ 66 * n + 1 := by
  have hj' := mem_Icc.1 hj
  rw [hW, etaW_big hj'.1]
  have h1 : 51 * n ≤ (j + 43) * n := Nat.mul_le_mul_right n (by omega)
  have h2 : (j + 43) * n ≤ 66 * n := Nat.mul_le_mul_right n (by omega)
  omega

/-- `h_j ≤ 66n + 1` for `j ≤ 23`. -/
theorem h_le {n j : ℕ} (hj : j ≤ 23) : cfgW.h n j ≤ 66 * n + 1 := by
  rw [hW]
  have : etaW j * n ≤ 66 * n := Nat.mul_le_mul_right n (etaW_le hj)
  omega

theorem Icc_6_23 : Icc 6 23 = insert 6 (insert 7 (Icc 8 23)) := by
  ext j
  simp only [mem_Icc, mem_insert]
  omega

theorem Icc_1_5 : Icc 1 5 = insert 5 (Icc 1 4) := by
  ext j
  simp only [mem_Icc, mem_insert]
  omega

theorem card_Icc_8_23 : (Icc 8 23).card = 16 := rfl

/-- `G_k / ε^{16}` at the top poles `109n + 1 < k ≤ 110n + 1`: there the sixteen rational bricks
`j = 8, …, 23` have no pole (they contribute `ε · xBrick`), while `j = 6, 7` (`η = 50`) have one. -/
def Vk (n k : ℕ) : PowerSeries ℚ :=
  (C ((cfgW.h0 n : ℚ) - 2 * k) + C 2 * X) *
    (∏ j ∈ Icc 1 5, (polyBrick (cfgW.h n j) 1 k *
      polyBrick (cfgW.h0 n) (cfgW.h0 n - cfgW.h n j + 1) k)) *
    (ratBrick (cfgW.h n 6) (cfgW.h0 n - cfgW.h n 6 + 1) k *
      ratBrick (cfgW.h n 7) (cfgW.h0 n - cfgW.h n 7 + 1) k) *
    ∏ j ∈ Icc 8 23, xBrick (cfgW.h n j) (cfgW.h0 n - cfgW.h n j + 1) k

theorem Gk_eq {n k : ℕ} (hk1 : 109 * n + 1 < k) :
    Gk cfgW n k = X ^ 16 * Vk n k := by
  have hr : cfgW.r = 5 := rfl
  have hq : cfgW.q = 23 := rfl
  unfold Gk
  rw [hr, hq, show 5 + 1 = 6 from rfl, Icc_6_23, prod_insert (by simp), prod_insert (by simp)]
  have hx : ∀ j ∈ Icc 8 23, ratBrick (cfgW.h n j) (cfgW.h0 n - cfgW.h n j + 1) k =
      X * xBrick (cfgW.h n j) (cfgW.h0 n - cfgW.h n j + 1) k := by
    intro j hj
    refine ratBrick_else ?_
    have := h_big (n := n) hj
    have := h0W n
    omega
  have hX : ∏ j ∈ Icc 8 23, (X * xBrick (cfgW.h n j) (cfgW.h0 n - cfgW.h n j + 1) k) =
      X ^ 16 * ∏ j ∈ Icc 8 23, xBrick (cfgW.h n j) (cfgW.h0 n - cfgW.h n j + 1) k := by
    rw [prod_mul_distrib, prod_const, card_Icc_8_23]
  rw [prod_congr rfl hx, hX]
  unfold Vk
  ring

theorem B7_eq {n k : ℕ} (hk1 : 109 * n + 1 < k) : B cfgW n 7 k = constantCoeff (Vk n k) := by
  rw [B, Gk_eq hk1, show cfgW.q - 7 = 0 + 16 from rfl, coeff_X_pow_mul,
    coeff_zero_eq_constantCoeff_apply]

theorem B6_eq {n k : ℕ} (hk1 : 109 * n + 1 < k) : B cfgW n 6 k = coeff 1 (Vk n k) := by
  rw [B, Gk_eq hk1, show cfgW.q - 6 = 1 + 16 from rfl, coeff_X_pow_mul]

/-- `V_k = (ε - ℓ) U_k` at `k ∈ {110n, 110n+1}`: the factor `i = k - ℓ` (`= 47n+1` or `47n+2`) of
`P₅ = polyBrick h₅ 1` is taken out. -/
def Uk (n k : ℕ) : PowerSeries ℚ :=
  (C ((cfgW.h0 n : ℚ) - 2 * k) + C 2 * X) *
    ((∏ j ∈ Icc 1 4, (polyBrick (cfgW.h n j) 1 k *
      polyBrick (cfgW.h0 n) (cfgW.h0 n - cfgW.h n j + 1) k)) *
    ((C (1 / ((cfgW.h n 5 - 1).factorial : ℚ)) *
        ∏ i ∈ (Ico 1 (cfgW.h n 5)).erase (k + 1 - 63 * n), (C ((i : ℚ) - k) + X)) *
      polyBrick (cfgW.h0 n) (cfgW.h0 n - cfgW.h n 5 + 1) k)) *
    (ratBrick (cfgW.h n 6) (cfgW.h0 n - cfgW.h n 6 + 1) k *
      ratBrick (cfgW.h n 7) (cfgW.h0 n - cfgW.h n 7 + 1) k) *
    ∏ j ∈ Icc 8 23, xBrick (cfgW.h n j) (cfgW.h0 n - cfgW.h n j + 1) k

omit hLP in
theorem Vk_eq {n k : ℕ} (hLn : L + 1 = 63 * n) (hn : 2 ≤ n) (hk1 : 110 * n ≤ k)
    (hk2 : k ≤ 110 * n + 1) : Vk n k = (C (-(L : ℚ)) + X) * Uk n k := by
  have hmem : k + 1 - 63 * n ∈ Ico 1 (cfgW.h n 5) := by
    rw [mem_Ico, h5W]
    omega
  have hval : (((k + 1 - 63 * n : ℕ) : ℚ) - k) = -(L : ℚ) := by
    have h1 : ((k + 1 - 63 * n : ℕ) : ℚ) = (k : ℚ) + 1 - 63 * n := by
      rw [Nat.cast_sub (by omega)]
      push_cast
      ring
    have h2 : (L : ℚ) = 63 * n - 1 := by
      have : ((L + 1 : ℕ) : ℚ) = ((63 * n : ℕ) : ℚ) := by rw [hLn]
      push_cast at this
      linarith
    rw [h1, h2]
    ring
  have hP5 : polyBrick (cfgW.h n 5) 1 k = C (1 / ((cfgW.h n 5 - 1).factorial : ℚ)) *
      ((C (-(L : ℚ)) + X) *
        ∏ i ∈ (Ico 1 (cfgW.h n 5)).erase (k + 1 - 63 * n), (C ((i : ℚ) - k) + X)) := by
    rw [polyBrick, ← mul_prod_erase _ _ hmem, hval]
  unfold Vk Uk
  rw [Icc_1_5, prod_insert (by simp), hP5]
  ring

/-- `U_k` is `ℓ`-integral with an `ℓ`-unit constant term (Lemma C of the informal proof): every
remaining linear factor `i - k` lies in `(-2ℓ, 2ℓ) ∖ {0, ±ℓ}`, and every factorial is `(≤ 60n)!`. -/
theorem Uk_PSU {n k : ℕ} (hLn : L + 1 = 63 * n) (hn : 2 ≤ n) (hk1 : 110 * n ≤ k)
    (hk2 : k ≤ 110 * n + 1) : PSU L (Uk n k) := by
  have h0 := h0W n
  unfold Uk
  refine PSU.mul (PSU.mul (PSU.mul ?_ (PSU.mul ?_ (PSU.mul (PSU.mul ?_ ?_) ?_)))
    (PSU.mul ?_ ?_)) ?_
  · -- the linear factor `h₀ - 2k + 2ε`
    refine PSU.lin2 ?_
    have e : ((cfgW.h0 n : ℚ) - 2 * k) = (((cfgW.h0 n : ℤ) - 2 * k : ℤ) : ℚ) := by push_cast; ring
    rw [e]
    exact IsU.int (not_dvd_of_bounds (by omega) (by omega) (by omega) (by omega) (by omega))
  · -- `P_j Q_j`, `j ≤ 4`
    refine PSU.prod _ _ fun j hj => PSU.mul ?_ ?_
    · have hh := h_small (n := n) hj
      refine PSU_polyBrick (by omega) fun i hi => ?_
      have hi' := mem_Ico.1 hi
      exact not_dvd_of_bounds (by omega) (by omega) (by omega) (by omega) (by omega)
    · have hh := h_small (n := n) hj
      refine PSU_polyBrick (by omega) fun i hi => ?_
      have hi' := mem_Ico.1 hi
      exact not_dvd_of_bounds (by omega) (by omega) (by omega) (by omega) (by omega)
  · exact PSU.const (IsU.one_div_fact (by rw [h5W]; omega))
  · refine PSU.prod_lin _ _ fun i hi => ?_
    have hi1 := mem_erase.1 hi
    have hi2 := mem_Ico.1 hi1.2
    rw [h5W] at hi2
    exact not_dvd_of_bounds (by omega) (by omega) (by omega) (by omega) (by omega)
  · have hh := h5W n
    refine PSU_polyBrick (by omega) fun i hi => ?_
    have hi' := mem_Ico.1 hi
    exact not_dvd_of_bounds (by omega) (by omega) (by omega) (by omega) (by omega)
  · have hh := h6W n
    refine PSU_ratBrick_unit ⟨by omega, by omega⟩ (by omega) fun i hi => ?_
    have hi1 := mem_erase.1 hi
    have hi2 := mem_Ico.1 hi1.2
    exact not_dvd_of_bounds (by omega) (by omega) (by omega) (by omega) (by omega)
  · have hh := h7W n
    refine PSU_ratBrick_unit ⟨by omega, by omega⟩ (by omega) fun i hi => ?_
    have hi1 := mem_erase.1 hi
    have hi2 := mem_Ico.1 hi1.2
    exact not_dvd_of_bounds (by omega) (by omega) (by omega) (by omega) (by omega)
  · refine PSU.prod _ _ fun j hj => ?_
    have hh := h_big (n := n) hj
    refine PSU_xBrick (by omega) fun i hi => ?_
    have hi' := mem_Ico.1 hi
    exact not_dvd_of_bounds (by omega) (by omega) (by omega) (by omega) (by omega)

/-! ### Telescoping between the two top poles (Lemma E) -/

/-- The product of the shift factors of the left-hand side of Lemma E, as a polynomial in `m = n`:
`(h₀-2k) ∏_{j≤5} (1-k)(h₀-h_j+1-k) ∏_{j≥6} (h₀-h_j+1-k)` at `k = 110n+1`. -/
def Dpoly {R : Type*} [CommRing R] (m : R) : R :=
  (-60 * m) * (∏ j ∈ Icc 1 5, ((-110 * m) * ((50 - (etaW j : R)) * m + 1))) * (1 * 1) *
    ∏ j ∈ Icc 8 23, ((50 - (etaW j : R)) * m + 1)

/-- The product of the shift factors of the right-hand side of Lemma E:
`(h₀-2k+2) ∏_{j≤5} (h_j-k)(h₀-k) ∏_{j≥6} (h_j-k)` at `k = 110n+1`. -/
def Npoly {R : Type*} [CommRing R] (m : R) : R :=
  (2 - 60 * m) * (∏ j ∈ Icc 1 5, ((((etaW j : R) - 110) * m) * (50 * m + 1))) *
    ((-60 * m) * (-60 * m)) * ∏ j ∈ Icc 8 23, (((etaW j : R) - 110) * m)

theorem cast_b (n j : ℕ) (hj : j ≤ 23) :
    ((cfgW.h0 n - cfgW.h n j + 1 : ℕ) : ℚ) = (160 - (etaW j : ℚ)) * n + 2 := by
  have hle : cfgW.h n j ≤ cfgW.h0 n := by
    have := h_le (n := n) hj
    rw [h0W]
    omega
  rw [Nat.cast_add, Nat.cast_sub hle, h0W, hW]
  push_cast
  ring

theorem lin_sh (n : ℕ) :
    constantCoeff (C ((cfgW.h0 n : ℚ) - 2 * ((110 * n : ℕ) : ℚ)) + C 2 * X) * (-60 * (n : ℚ)) =
      constantCoeff (C ((cfgW.h0 n : ℚ) - 2 * ((110 * n + 1 : ℕ) : ℚ)) + C 2 * X) *
        (2 - 60 * (n : ℚ)) := by
  simp only [map_add, map_mul, constantCoeff_C, constantCoeff_X, mul_zero, add_zero]
  rw [h0W]
  push_cast
  ring

theorem pb_sh (n j : ℕ) :
    constantCoeff (polyBrick (cfgW.h n j) 1 (110 * n)) * (-110 * (n : ℚ)) =
      constantCoeff (polyBrick (cfgW.h n j) 1 (110 * n + 1)) * (((etaW j : ℚ) - 110) * n) := by
  have h := polyBrick_shift (cfgW.h n j) 1 (110 * n) (by rw [hW]; omega)
  have e1 : ((1 : ℕ) : ℚ) - (((110 * n : ℕ) : ℚ) + 1) = -110 * (n : ℚ) := by push_cast; ring
  have e2 : ((cfgW.h n j : ℕ) : ℚ) - (((110 * n : ℕ) : ℚ) + 1) = ((etaW j : ℚ) - 110) * n := by
    rw [hW]
    push_cast
    ring
  rw [e1, e2] at h
  exact h

theorem pb'_sh (n j : ℕ) (hj : j ≤ 23) :
    constantCoeff (polyBrick (cfgW.h0 n) (cfgW.h0 n - cfgW.h n j + 1) (110 * n)) *
        ((50 - (etaW j : ℚ)) * n + 1) =
      constantCoeff (polyBrick (cfgW.h0 n) (cfgW.h0 n - cfgW.h n j + 1) (110 * n + 1)) *
        (50 * (n : ℚ) + 1) := by
  have hh := hW n j
  have h0 := h0W n
  have h := polyBrick_shift (cfgW.h0 n) (cfgW.h0 n - cfgW.h n j + 1) (110 * n) (by omega)
  have e1 : ((cfgW.h0 n - cfgW.h n j + 1 : ℕ) : ℚ) - (((110 * n : ℕ) : ℚ) + 1) =
      (50 - (etaW j : ℚ)) * n + 1 := by
    rw [cast_b n j hj]
    push_cast
    ring
  have e2 : ((cfgW.h0 n : ℕ) : ℚ) - (((110 * n : ℕ) : ℚ) + 1) = 50 * (n : ℚ) + 1 := by
    rw [h0W]
    push_cast
    ring
  rw [e1, e2] at h
  exact h

theorem rb_sh (n j : ℕ) (hn : 1 ≤ n) (hj : cfgW.h n j = 50 * n + 1) :
    constantCoeff (ratBrick (cfgW.h n j) (cfgW.h0 n - cfgW.h n j + 1) (110 * n)) * 1 =
      constantCoeff (ratBrick (cfgW.h n j) (cfgW.h0 n - cfgW.h n j + 1) (110 * n + 1)) *
        (-60 * (n : ℚ)) := by
  have h0 := h0W n
  have h := ratBrick_shift (cfgW.h n j) (cfgW.h0 n - cfgW.h n j + 1) (110 * n) (by omega)
    (by omega)
  have e1 : ((cfgW.h0 n - cfgW.h n j + 1 : ℕ) : ℚ) - (((110 * n : ℕ) : ℚ) + 1) = 1 := by
    rw [show cfgW.h0 n - cfgW.h n j + 1 = 110 * n + 2 by omega]
    push_cast
    ring
  have e2 : ((cfgW.h n j : ℕ) : ℚ) - (((110 * n : ℕ) : ℚ) + 1) = -60 * (n : ℚ) := by
    rw [hj]
    push_cast
    ring
  rw [e1, e2] at h
  exact h

theorem xb_sh (n j : ℕ) (hn : 2 ≤ n) (hj : j ∈ Icc 8 23) :
    constantCoeff (xBrick (cfgW.h n j) (cfgW.h0 n - cfgW.h n j + 1) (110 * n)) *
        ((50 - (etaW j : ℚ)) * n + 1) =
      constantCoeff (xBrick (cfgW.h n j) (cfgW.h0 n - cfgW.h n j + 1) (110 * n + 1)) *
        (((etaW j : ℚ) - 110) * n) := by
  have hb := h_big (n := n) hj
  have h0 := h0W n
  have h := xBrick_shift (cfgW.h n j) (cfgW.h0 n - cfgW.h n j + 1) (110 * n) (by omega)
    (by omega)
  have e1 : ((cfgW.h0 n - cfgW.h n j + 1 : ℕ) : ℚ) - (((110 * n : ℕ) : ℚ) + 1) =
      (50 - (etaW j : ℚ)) * n + 1 := by
    rw [cast_b n j (mem_Icc.1 hj).2]
    push_cast
    ring
  have e2 : ((cfgW.h n j : ℕ) : ℚ) - (((110 * n : ℕ) : ℚ) + 1) = ((etaW j : ℚ) - 110) * n := by
    rw [hW]
    push_cast
    ring
  rw [e1, e2] at h
  exact h

/-- **Lemma E** (exact form): `V_{110n}(0) · Dpoly(n) = V_{110n+1}(0) · Npoly(n)`. -/
theorem Vk_shift {n : ℕ} (hn : 2 ≤ n) :
    constantCoeff (Vk n (110 * n)) * Dpoly (n : ℚ) =
      constantCoeff (Vk n (110 * n + 1)) * Npoly (n : ℚ) := by
  unfold Vk Dpoly Npoly
  simp only [map_mul, map_prod]
  refine mul_shift (mul_shift (mul_shift (lin_sh n) ?_)
    (mul_shift (rb_sh n 6 (by omega) (h6W n)) (rb_sh n 7 (by omega) (h7W n)))) ?_
  · exact prod_shift fun j hj => mul_shift (pb_sh n j)
      (pb'_sh n j (by have := (mem_Icc.1 hj).2; omega))
  · exact prod_shift fun j hj => xb_sh n j hn hj

/-! ### Reduction modulo `ℓ` (`63 n ≡ 1`) -/


/-- `63^{29} · Dpoly(1/63)`. -/
def Dconst : ℤ :=
  -60 * (∏ j ∈ Icc 1 5, (-110 * (113 - (etaW j : ℤ)))) * (63 * 63) *
    ∏ j ∈ Icc 8 23, (113 - (etaW j : ℤ))

/-- `63^{29} · Npoly(1/63)`. -/
def Nconst : ℤ :=
  66 * (∏ j ∈ Icc 1 5, (((etaW j : ℤ) - 110) * 113)) * 3600 *
    ∏ j ∈ Icc 8 23, ((etaW j : ℤ) - 110)

theorem Dconst_val : Dconst = 27052758463045404478168355924002860888883200000000000 := by
  decide

theorem Nconst_val : Nconst = -9814529148738402720713231971425860007451066368000000 := by
  decide

/-- `Dconst + Nconst = 63^{29} Dpoly(1/63) (1 + ρ(1/63)) = 63^{29} Dpoly(1/63) · Q₁`. -/
theorem DN_sum : Dconst + Nconst = 17238229314307001757455123952577000881432133632000000 := by
  rw [Dconst_val, Nconst_val]
  norm_num

theorem Dpoly_eval {R : Type*} [CommRing R] {m : R} (h63 : 63 * m = 1) :
    Dpoly m = (Dconst : R) * m ^ 29 := by
  have e1 : ∀ j ∈ Icc 1 5, ((-110 * m) * ((50 - (etaW j : R)) * m + 1)) =
      (-110 * (113 - (etaW j : R))) * m ^ 2 := fun j _ => by
    linear_combination (110 * m) * h63
  have e2 : ∀ j ∈ Icc 8 23, ((50 - (etaW j : R)) * m + 1) = (113 - (etaW j : R)) * m :=
    fun j _ => by linear_combination (-1 : R) * h63
  have e3 : (1 : R) * 1 = 63 * 63 * m ^ 2 := by linear_combination (-(63 * m + 1)) * h63
  have p1 : ∏ j ∈ Icc 1 5, ((-110 * m) * ((50 - (etaW j : R)) * m + 1)) =
      (∏ j ∈ Icc 1 5, (-110 * (113 - (etaW j : R)))) * (m ^ 2) ^ 5 := by
    rw [prod_congr rfl e1, prod_mul_distrib, prod_const]
    rfl
  have p2 : ∏ j ∈ Icc 8 23, ((50 - (etaW j : R)) * m + 1) =
      (∏ j ∈ Icc 8 23, (113 - (etaW j : R))) * m ^ 16 := by
    rw [prod_congr rfl e2, prod_mul_distrib, prod_const, card_Icc_8_23]
  unfold Dpoly Dconst
  rw [p1, p2, e3]
  push_cast
  ring

theorem Npoly_eval {R : Type*} [CommRing R] {m : R} (h63 : 63 * m = 1) :
    Npoly m = (Nconst : R) * m ^ 29 := by
  have e0 : (2 : R) - 60 * m = 66 * m := by linear_combination (-2 : R) * h63
  have e1 : ∀ j ∈ Icc 1 5, ((((etaW j : R) - 110) * m) * (50 * m + 1)) =
      (((etaW j : R) - 110) * 113) * m ^ 2 := fun j _ => by
    linear_combination (-(((etaW j : R) - 110) * m)) * h63
  have p1 : ∏ j ∈ Icc 1 5, ((((etaW j : R) - 110) * m) * (50 * m + 1)) =
      (∏ j ∈ Icc 1 5, (((etaW j : R) - 110) * 113)) * (m ^ 2) ^ 5 := by
    rw [prod_congr rfl e1, prod_mul_distrib, prod_const]
    rfl
  have p2 : ∏ j ∈ Icc 8 23, (((etaW j : R) - 110) * m) =
      (∏ j ∈ Icc 8 23, ((etaW j : R) - 110)) * m ^ 16 := by
    rw [prod_mul_distrib, prod_const, card_Icc_8_23]
  unfold Npoly Nconst
  rw [e0, p1, p2]
  push_cast
  ring

/-- **The residue `u_{110n} + u_{110n+1}` is non-zero modulo `ℓ`** (Lemma E + `ℓ > 63^{29} D Q₁`):
from `u₁ Dpoly(n) = u₂ Npoly(n)` and `63 n ≡ 1`, `u₁ Dconst ≡ u₂ Nconst`; if `u₁ + u₂ ≡ 0` then
`u₂ (Dconst + Nconst) ≡ 0`, impossible for `0 < Dconst + Nconst < ℓ`. -/
theorem res_sum_ne {n : ℕ} (hLn : L + 1 = 63 * n)
    (hbig : 17238229314307001757455123952577000881432133632000000 < L)
    {u1 u2 : ℚ} (hu1 : u1 ∈ Zq L) (hu2 : IsU L u2)
    (htel : u1 * Dpoly (n : ℚ) = u2 * Npoly (n : ℚ)) :
    (u1 : ZMod L) + (u2 : ZMod L) ≠ 0 := by
  have h63 : 63 * (n : ZMod L) = 1 := by
    have : ((L + 1 : ℕ) : ZMod L) = ((63 * n : ℕ) : ZMod L) := by rw [hLn]
    push_cast at this
    rw [ZMod.natCast_self, zero_add] at this
    rw [← this]
  have hm0 : (n : ZMod L) ≠ 0 := by
    intro h0
    rw [h0, mul_zero] at h63
    exact zero_ne_one h63
  have hD : ((Dpoly (n : ℤ) : ℤ) : ℚ) = Dpoly (n : ℚ) := by
    unfold Dpoly
    push_cast
    ring
  have hN : ((Npoly (n : ℤ) : ℤ) : ℚ) = Npoly (n : ℚ) := by
    unfold Npoly
    push_cast
    ring
  have hDz : ((Dpoly (n : ℤ) : ℤ) : ZMod L) = Dpoly (n : ZMod L) := by
    unfold Dpoly
    push_cast
    ring
  have hNz : ((Npoly (n : ℤ) : ℤ) : ZMod L) = Npoly (n : ZMod L) := by
    unfold Npoly
    push_cast
    ring
  rw [← hD, ← hN] at htel
  have key : (u1 : ZMod L) * Dpoly (n : ZMod L) = (u2 : ZMod L) * Npoly (n : ZMod L) := by
    rw [← hDz, ← hNz, ← res_int, ← res_int, ← res_mul hu1 (Zq_int _), ← res_mul hu2.1 (Zq_int _),
      htel]
  rw [Dpoly_eval h63, Npoly_eval h63] at key
  have key' : (u1 : ZMod L) * (Dconst : ZMod L) = (u2 : ZMod L) * (Nconst : ZMod L) := by
    apply mul_right_cancel₀ (pow_ne_zero 29 hm0)
    linear_combination key
  intro hsum
  have hS : ((17238229314307001757455123952577000881432133632000000 : ℤ) : ZMod L) =
      (Dconst : ZMod L) + (Nconst : ZMod L) := by
    rw [← DN_sum]
    push_cast
    ring
  have h0 : (u2 : ZMod L) *
      ((17238229314307001757455123952577000881432133632000000 : ℤ) : ZMod L) = 0 := by
    rw [hS]
    linear_combination -key' + (Dconst : ZMod L) * hsum
  rcases mul_eq_zero.1 h0 with h | h
  · exact hu2.2 h
  · rw [ZMod.intCast_zmod_eq_zero_iff_dvd] at h
    have := Int.le_of_dvd (by norm_num) h
    omega

/-! ### `ℓ`-integrality of the Laurent coefficients (Lemma B) -/

theorem m0W (n : ℕ) : m0 cfgW n = 60 * n := by
  change max (cfgW.h n 5 - 1) (cfgW.h0 n - 2 * cfgW.h n 6) = 60 * n
  rw [h5W, h6W, h0W, Nat.max_eq_right (by omega)]
  omega

/-- **Lemma B.** Every `B_{j,k}` is `ℓ`-integral: `D_{m₀}^{q-j} B_{j,k} ∈ ℤ` (`Stmt_LaurentInt`)
with `m₀ = 60n < ℓ`, and `ℓ ∤ D_{60n}`. -/
theorem B_mem (hLI : Stmt_LaurentInt) {n : ℕ} (hLn : L + 1 = 63 * n) (hn : 1 ≤ n) {j k : ℕ}
    (hj : j ∈ Icc 6 23) (hk : k ∈ Krange cfgW n) : B cfgW n j k ∈ Zq L := by
  have h := hLI cfgW admissible_cfgW n hn j k hj hk
  rw [m0W] at h
  exact mem_of_int (not_dvd_lcmUpto (by omega)) h

/-- The coefficients `A_s` (`s ∈ window`) are `ℓ`-integral. -/
theorem Acoef_mem (hLI : Stmt_LaurentInt) {n : ℕ} (hLn : L + 1 = 63 * n) (hn : 1 ≤ n) {s : ℕ}
    (hs : s ∈ window cfgW) : Acoef cfgW n s ∈ Zq L := by
  rw [window_cfgW] at hs
  have hs' : s + 1 ∈ Icc 6 23 := by
    simp only [mem_insert, mem_singleton] at hs
    rw [mem_Icc]
    omega
  unfold Acoef
  exact mul_mem (Zq_nat _) (sum_mem fun k hk => B_mem hLI hLn hn hs' hk)

/-! ### The principal part of `A₀` at `ℓ` (Lemma D) -/

/-- The terms of `ℓ⁵ A₀` that vanish modulo `ℓ`: `k < 110n` (then `k - h₁ < ℓ`, everything is
`ℓ`-integral) or `B_{j,k} = 0` (`k > h₀ - h_j`, `Stmt_LaurentSupp`). -/
theorem term_zero (hLS : Stmt_LaurentSupp) (hLI : Stmt_LaurentInt) {n : ℕ}
    (hLn : L + 1 = 63 * n) (hn : 1 ≤ n) {j k : ℕ} (hj : j ∈ Icc 6 23) (hk : k ∈ Krange cfgW n)
    (hk' : k < 110 * n ∨ cfgW.h0 n - cfgW.h n j < k) :
    HasRes L ((L : ℚ) ^ 5 * (B cfgW n j k * harm (k - cfgW.h n 1) (j - 1))) 0 := by
  rcases hk' with hk' | hk'
  · have hB := B_mem hLI hLn hn hj hk
    have hH := harm_mem (L := L) (j - 1) (show k - cfgW.h n 1 < L by rw [h1W]; omega)
    have e : (L : ℚ) ^ 5 * (B cfgW n j k * harm (k - cfgW.h n 1) (j - 1)) =
        L * ((L : ℚ) ^ 4 * (B cfgW n j k * harm (k - cfgW.h n 1) (j - 1))) := by ring
    rw [e]
    exact HasRes.L_mul (mul_mem (pow_mem (Zq_nat L) 4) (mul_mem hB hH))
  · rw [hLS cfgW admissible_cfgW n hn j k hj (Or.inr hk'), zero_mul, mul_zero]
    exact HasRes.zero

/-- The term `j = 6` at a top pole: `ℓ⁵ B_{6,k} H^{(5)}_N ≡ u_k (mod ℓ)` (`ℓ ≤ N < 2ℓ`). -/
theorem top6 {n K N : ℕ} {u v : ℚ} (hu : u ∈ Zq L) (hv : v ∈ Zq L)
    (hB : B cfgW n 6 K = -L * v + u) (hN1 : L ≤ N) (hN2 : N < 2 * L) :
    HasRes L ((L : ℚ) ^ 5 * (B cfgW n 6 K * harm N 5)) (u : ZMod L) := by
  have hBr : HasRes L (B cfgW n 6 K) (u : ZMod L) := by
    rw [hB]
    exact ((HasRes.L_mul (neg_mem hv)).add (HasRes.of_mem hu)).congr (by ring) (by ring)
  exact (hBr.mul (harm_res (L := L) (s := 5) (by norm_num) hN1 hN2)).congr (by ring) (by ring)

/-- The term `j = 7` at a top pole: `ℓ⁵ B_{7,k} H^{(6)}_N ≡ -u_k (mod ℓ)`. -/
theorem top7 {n K N : ℕ} {u : ℚ} (hu : u ∈ Zq L)
    (hB : B cfgW n 7 K = -L * u) (hN1 : L ≤ N) (hN2 : N < 2 * L) :
    HasRes L ((L : ℚ) ^ 5 * (B cfgW n 7 K * harm N 6)) ((-u : ℚ) : ZMod L) := by
  have := (HasRes.of_mem (neg_mem hu)).mul (harm_res (L := L) (s := 6) (by norm_num) hN1 hN2)
  refine this.congr ?_ (by ring)
  rw [hB]
  ring

theorem Krange_mem {n k : ℕ} : k ∈ Krange cfgW n ↔ 47 * n + 1 ≤ k ∧ k ≤ 113 * n + 1 := by
  rw [Krange, mem_Icc, h1W, h0W]
  omega

theorem sum6 (hLS : Stmt_LaurentSupp) (hLI : Stmt_LaurentInt) {n : ℕ} (hLn : L + 1 = 63 * n)
    (hn : 2 ≤ n) {u1 u2 v1 v2 : ℚ} (hu1 : u1 ∈ Zq L) (hu2 : u2 ∈ Zq L) (hv1 : v1 ∈ Zq L)
    (hv2 : v2 ∈ Zq L) (hB1 : B cfgW n 6 (110 * n) = -L * v1 + u1)
    (hB2 : B cfgW n 6 (110 * n + 1) = -L * v2 + u2) :
    HasRes L (∑ k ∈ Krange cfgW n, (L : ℚ) ^ 5 * (B cfgW n 6 k * harm (k - cfgW.h n 1) (6 - 1)))
      ((u1 : ZMod L) + ((u2 : ZMod L) + 0)) := by
  have hK1 : 110 * n ∈ Krange cfgW n := Krange_mem.2 (by omega)
  have hK2 : 110 * n + 1 ∈ (Krange cfgW n).erase (110 * n) :=
    mem_erase.2 ⟨by omega, Krange_mem.2 (by omega)⟩
  rw [← add_sum_erase _ _ hK1, ← add_sum_erase _ _ hK2]
  refine (top6 hu1 hv1 hB1 ?_ ?_).add ((top6 hu2 hv2 hB2 ?_ ?_).add
    (HasRes.sum_zero _ _ fun k hk => ?_))
  · rw [h1W]; omega
  · rw [h1W]; omega
  · rw [h1W]; omega
  · rw [h1W]; omega
  · have hk1 := mem_erase.1 hk
    have hk2 := mem_erase.1 hk1.2
    refine term_zero hLS hLI hLn (by omega) (by simp) hk2.2 ?_
    rw [h6W, h0W]
    omega

theorem sum7 (hLS : Stmt_LaurentSupp) (hLI : Stmt_LaurentInt) {n : ℕ} (hLn : L + 1 = 63 * n)
    (hn : 2 ≤ n) {u1 u2 : ℚ} (hu1 : u1 ∈ Zq L) (hu2 : u2 ∈ Zq L)
    (hB1 : B cfgW n 7 (110 * n) = -L * u1) (hB2 : B cfgW n 7 (110 * n + 1) = -L * u2) :
    HasRes L (∑ k ∈ Krange cfgW n, (L : ℚ) ^ 5 * (B cfgW n 7 k * harm (k - cfgW.h n 1) (7 - 1)))
      (((-u1 : ℚ) : ZMod L) + (((-u2 : ℚ) : ZMod L) + 0)) := by
  have hK1 : 110 * n ∈ Krange cfgW n := Krange_mem.2 (by omega)
  have hK2 : 110 * n + 1 ∈ (Krange cfgW n).erase (110 * n) :=
    mem_erase.2 ⟨by omega, Krange_mem.2 (by omega)⟩
  rw [← add_sum_erase _ _ hK1, ← add_sum_erase _ _ hK2]
  refine (top7 hu1 hB1 ?_ ?_).add ((top7 hu2 hB2 ?_ ?_).add
    (HasRes.sum_zero _ _ fun k hk => ?_))
  · rw [h1W]; omega
  · rw [h1W]; omega
  · rw [h1W]; omega
  · rw [h1W]; omega
  · have hk1 := mem_erase.1 hk
    have hk2 := mem_erase.1 hk1.2
    refine term_zero hLS hLI hLn (by omega) (by simp) hk2.2 ?_
    rw [h7W, h0W]
    omega

theorem mul_T (c : ℕ) (S : Finset ℕ) (f : ℕ → ℚ) {r : ZMod L}
    (h : HasRes L (∑ k ∈ S, (L : ℚ) ^ 5 * f k) r) :
    HasRes L ((L : ℚ) ^ 5 * ((c : ℚ) * ∑ k ∈ S, f k)) ((c : ZMod L) * r) := by
  refine ((HasRes.nat c).mul h).congr ?_ rfl
  rw [mul_sum, mul_sum, mul_sum]
  exact sum_congr rfl fun k _ => by ring

/-- **Lemma D.** `ℓ⁵ A₀ ≡ -4 (u_{110n} + u_{110n+1}) (mod ℓ)`, given the top-pole data
`B_{7,k} = -ℓ u_k`, `B_{6,k} = u_k - ℓ v_k` with `u_k, v_k` `ℓ`-integral. -/
theorem A0_res (hLS : Stmt_LaurentSupp) (hLI : Stmt_LaurentInt) {n : ℕ} (hLn : L + 1 = 63 * n)
    (hn : 2 ≤ n) {u1 u2 v1 v2 : ℚ} (hu1 : u1 ∈ Zq L) (hu2 : u2 ∈ Zq L) (hv1 : v1 ∈ Zq L)
    (hv2 : v2 ∈ Zq L) (h6a : B cfgW n 6 (110 * n) = -L * v1 + u1)
    (h6b : B cfgW n 6 (110 * n + 1) = -L * v2 + u2) (h7a : B cfgW n 7 (110 * n) = -L * u1)
    (h7b : B cfgW n 7 (110 * n + 1) = -L * u2) :
    HasRes L ((L : ℚ) ^ 5 * A0 cfgW n) (((-4 : ℤ) : ZMod L) * ((u1 : ZMod L) + (u2 : ZMod L))) := by
  have hr : cfgW.r = 5 := rfl
  have hq : cfgW.q = 23 := rfl
  unfold A0
  rw [hr, hq, show 5 + 1 = 6 from rfl, Icc_6_23, sum_insert (by simp), sum_insert (by simp),
    mul_add, mul_add]
  have H6 := mul_T (Nat.choose (6 - 2) (5 - 1)) _ _
    (sum6 hLS hLI hLn hn hu1 hu2 hv1 hv2 h6a h6b)
  have H7 := mul_T (Nat.choose (7 - 2) (5 - 1)) _ _ (sum7 hLS hLI hLn hn hu1 hu2 h7a h7b)
  have H8 : HasRes L ((L : ℚ) ^ 5 * ∑ j ∈ Icc 8 23, ((Nat.choose (j - 2) (5 - 1) : ℚ) *
      ∑ k ∈ Krange cfgW n, B cfgW n j k * harm (k - cfgW.h n 1) (j - 1))) 0 := by
    rw [mul_sum]
    refine HasRes.sum_zero _ _ fun j hj => ?_
    have hj' : j ∈ Icc 6 23 := by
      have := mem_Icc.1 hj
      rw [mem_Icc]
      omega
    have hS : HasRes L (∑ k ∈ Krange cfgW n,
        (L : ℚ) ^ 5 * (B cfgW n j k * harm (k - cfgW.h n 1) (j - 1))) 0 := by
      refine HasRes.sum_zero _ _ fun k hk => term_zero hLS hLI hLn (by omega) hj' hk ?_
      by_cases hk' : k < 110 * n
      · exact Or.inl hk'
      · right
        have := h_big (n := n) hj
        have := h0W n
        omega
    exact (mul_T _ _ _ hS).congr rfl (by ring)
  have c6 : Nat.choose (6 - 2) (5 - 1) = 1 := rfl
  have c7 : Nat.choose (7 - 2) (5 - 1) = 5 := rfl
  refine (H6.add (H7.add H8)).congr rfl ?_
  rw [c6, c7]
  push_cast
  ring

/-! ### Theorem N -/

/-- The data at the two top poles `k ∈ {110n, 110n+1}` (Lemma C): `B_{7,k} = -ℓ u` and
`B_{6,k} = u - ℓ v` with `u` an `ℓ`-unit and `v` `ℓ`-integral (`u = U_k(0)`, `v = U_k'(0)`). -/
theorem top_data {n K : ℕ} (hLn : L + 1 = 63 * n) (hn : 2 ≤ n) (hK1 : 110 * n ≤ K)
    (hK2 : K ≤ 110 * n + 1) :
    ∃ u v : ℚ, IsU L u ∧ v ∈ Zq L ∧ B cfgW n 7 K = -L * u ∧ B cfgW n 6 K = -L * v + u := by
  have hU := Uk_PSU (L := L) hLn hn hK1 hK2
  refine ⟨constantCoeff (Uk n K), coeff 1 (Uk n K), hU.2, mem_ZqPS.1 hU.1 1, ?_, ?_⟩
  · rw [B7_eq (n := n) (k := K) (by omega), Vk_eq hLn hn hK1 hK2, coeff0_lin_mul]
  · rw [B6_eq (n := n) (k := K) (by omega), Vk_eq hLn hn hK1 hK2, coeff1_lin_mul,
      coeff_zero_eq_constantCoeff_apply]

/-- **Theorem N** (Lean normalization): `v_ℓ(A₀) = -5` for `ℓ = 63n - 1` prime and larger than
`Dconst + Nconst = 63^{29} Dpoly(1/63) Q₁`. -/
theorem A0_val (hLS : Stmt_LaurentSupp) (hLI : Stmt_LaurentInt) {n : ℕ} (hLn : L + 1 = 63 * n)
    (hbig : 17238229314307001757455123952577000881432133632000000 < L) :
    padicValRat L (A0 cfgW n) = -5 := by
  have hn : 2 ≤ n := by omega
  have hL0 : (L : ℚ) ≠ 0 := by exact_mod_cast (Fact.out : L.Prime).ne_zero
  obtain ⟨u1, v1, hu1, hv1, h7a, h6a⟩ :=
    top_data (L := L) hLn hn (le_refl (110 * n)) (by omega : 110 * n ≤ 110 * n + 1)
  obtain ⟨u2, v2, hu2, hv2, h7b, h6b⟩ :=
    top_data (L := L) hLn hn (by omega : 110 * n ≤ 110 * n + 1) (le_refl (110 * n + 1))
  -- Lemma E: `u₁ Dpoly(n) = u₂ Npoly(n)`
  have htel : u1 * Dpoly (n : ℚ) = u2 * Npoly (n : ℚ) := by
    have h := Vk_shift hn
    rw [← B7_eq (n := n) (k := 110 * n) (by omega), ← B7_eq (n := n) (k := 110 * n + 1) (by omega),
      h7a, h7b] at h
    have h' : (-(L : ℚ)) * (u1 * Dpoly (n : ℚ)) = (-(L : ℚ)) * (u2 * Npoly (n : ℚ)) := by
      linear_combination h
    exact mul_left_cancel₀ (neg_ne_zero.2 hL0) h'
  have hres := A0_res hLS hLI hLn hn hu1.1 hu2.1 hv1 hv2 h6a h6b h7a h7b
  have h4 : ((-4 : ℤ) : ZMod L) ≠ 0 := by
    rw [Ne, ZMod.intCast_zmod_eq_zero_iff_dvd]
    intro h
    have := Int.le_of_dvd (by norm_num) (dvd_neg.1 h)
    omega
  have hne : ((-4 : ℤ) : ZMod L) * ((u1 : ZMod L) + (u2 : ZMod L)) ≠ 0 :=
    mul_ne_zero h4 (res_sum_ne hLn hbig hu1.1 hu2 htel)
  rw [← hres.2] at hne
  have hA : A0 cfgW n ≠ 0 := by
    intro h
    rw [h, mul_zero, Rat.cast_zero] at hne
    exact hne rfl
  have h0 := pv_eq_zero hres.1 hne
  rw [padicValRat.mul (pow_ne_zero _ hL0) hA, padicValRat.pow,
    padicValRat.self (Fact.out : L.Prime).one_lt] at h0
  push_cast at h0
  linarith

end AuxPrime

open AuxPrime in
-- The signature is fixed by the blueprint; `Stmt_LaurentVal` and `Stmt_Harmonic` are not needed.
set_option linter.unusedVariables false in
theorem AuxPrime_proof (hLS : Stmt_LaurentSupp) (hLI : Stmt_LaurentInt) (hLV : Stmt_LaurentVal)
    (hH : Stmt_Harmonic) : Stmt_AuxPrime := by
  unfold Stmt_AuxPrime
  rw [Filter.eventually_atTop]
  refine ⟨17238229314307001757455123952577000881432133632000000, fun n hn _ hp => ?_⟩
  have : Fact (63 * n - 1).Prime := ⟨hp⟩
  have hLn : 63 * n - 1 + 1 = 63 * n := by
    have := hp.two_le
    omega
  have hbig : 17238229314307001757455123952577000881432133632000000 < 63 * n - 1 := by omega
  refine ⟨?_, fun s hs => pv_nonneg (Acoef_mem hLI hLn (by omega) hs)⟩
  rw [A0_val hLS hLI hLn hbig]
  norm_num

end ZetaWindow

end
