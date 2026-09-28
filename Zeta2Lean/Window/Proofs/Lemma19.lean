module

public import Zeta2Lean.Window.Statements

@[expose] public section

set_option linter.style.header false
set_option linter.style.longLine false

/-!
# JTNB Lemma 19: `Δ_n A₀, Δ_n A_s ∈ ℤ` (docs/window/proof.md §2)

**Proves `Stmt_Lemma19` from `Stmt_LaurentSupp`, `Stmt_LaurentInt`, `Stmt_LaurentVal`,
`Stmt_Harmonic`:** for admissible `c` and `n ≥ 1`,
`Delta c n * A0 c n ∈ ℤ` and `Delta c n * Acoef c n s ∈ ℤ` for `r ≤ s ≤ q - 1`,
where `Delta c n = Dprod c n / PhiN c n`, `Dprod = D_{m₁}^r D_{m₂} ⋯ D_{m_{q-r}}`,
`PhiN = ∏_{p prime, h₀ < p², p ≤ m_{q-r}} p^{ω_p}`.

**Informal proof** (JTNB p. 281–282).  Write `Q = Dprod c n`, `Φ = PhiN c n`.
(a) *Rough inclusions* `Q A_s ∈ ℤ`, `Q A₀ ∈ ℤ`.  Facts: `m₀ ≤ m_{q-r} ≤ ⋯ ≤ m₂ ≤ m₁` (η sorted);
`D_m ∣ D_{m'}` for `m ≤ m'`.  For `A_s` (`s = j - 1`): `D_{m₀}^{q-j} B_{j,k} ∈ ℤ` (`Stmt_LaurentInt`) and
`D_{m₀}^{q-j} ∣ Q` (`q - j ≤ q - 1` = number of lcm-factors of `Q`, each divisible by `D_{m₀}`).  For
`A₀`: `B_{j,k} ≠ 0` only if `k ≤ h₀ - h_j` (`Stmt_LaurentSupp`), then `k - h₁ ≤ h₀ - h₁ - h_j ≤ m_{j-r}`,
so `D_{m_{j-r}}^{j-1} H^{(j-1)}_{k-h₁} ∈ ℤ` (`Stmt_Harmonic.int`), and
`D_{m₀}^{q-j} D_{m_{j-r}}^{j-1} ∣ Q`: the `j - 1 = r + (j-r-1)` largest factors `D_{m₁}^r D_{m₂} ⋯
D_{m_{j-r}}` of `Q` are each divisible by `D_{m_{j-r}}`, the remaining `q - j` by `D_{m₀}`.
(b) *Large primes* `h₀ < p²`, `p ≤ m_{q-r}`: `v_p(Q) ≥ q - 1` (`p ≤ m_i` gives `p ∣ D_{m_i}`).
`ω_{k,p}` is `p`-periodic in `k` (each floor term of (8.9) shifts by `±1` under `k ↦ k + p` and the
shifts cancel), so `ω_{k,p} ≥ ω_p` (the minimum over `0 ≤ k < p`) for every `k`.
By `Stmt_LaurentVal`, `v_p(B_{j,k}) ≥ ω_p - (q - j)` (when `B ≠ 0`), and by
`Stmt_Harmonic.val` (`k - h₁ < h₀ < p²`) `v_p(H^{(j-1)}_{k-h₁}) ≥ -(j-1)`; so
`v_p(A_s), v_p(A₀) ≥ ω_p - (q-1)` (ultrametric; zero terms are harmless) and `v_p(Q A) ≥ ω_p`.
(c) *Assembly.*  `z := Q A ∈ ℤ` by (a); for every prime `p` of `Φ`, `p^{ω_p} ∣ z` by (b) (when
`ω_p ≤ 0` the exponent `ω_p.toNat` is `0`).  The prime powers are pairwise coprime, so `Φ ∣ z`,
and `Δ A = z / Φ ∈ ℤ`.  (This is the statement "a rational with all `v_p ≥ 0` is an integer",
in the form of divisibility of the integer `z`; primes outside `Φ` need nothing beyond (a).)

## Formalisation (this file; complete)

* `ZZ : Subring ℚ` is the image of `ℤ`; `natCast_mul_mem_of_dvd` enlarges a denominator.
* `split_dvd_Dprod`: `D_{m_t}^{r+t-1} D_{m₀}^{q-r-t} ∣ Dprod` for `1 ≤ t ≤ q - r` (split
  `Icc 2 (q-r)` at `t`, `Finset.prod_Ico_consecutive`); `pow_dvd_Dprod` (`p^{q-1} ∣ Dprod` for
  `1 ≤ p ≤ m_{q-r}`) is its case `t = q - r`.
* `omegaKP_add_mul` (periodicity, `Int.add_mul_ediv_right`) and `omegaP_le`.
* `VpGe p c x := x = 0 ∨ c ≤ v_p(x)` with the ultrametric calculus (as in `LaurentValuation.lean`).
* `rough_Acoef`, `rough_A0`, `vp_Acoef`, `vp_A0`, and the assembly `int_of_rough_of_val`
  (`Finset.prod_dvd_of_coprime`, `padicValInt_dvd_iff`, `padicValNat_dvd_iff_le`).

The hypothesis `k ∈ Krange` of the statements is supplied by the sums over `Krange`.  The reasoning
of this file uses from `Admissible` only `eta_mono`, `two_eta_lt` and `r + 4 ≤ q` (the hypotheses
`Stmt_*` receive `Admissible c` whole); `r` odd is not used, and neither is `ω_{k,p} ≥ 0`
(`ω_p.toNat ≤ v_p(Q A)` follows from `ω_p ≤ v_p(Q A)` and `0 ≤ v_p(Q A)`).  The ranges of the
primes are exactly those of `PhiN`: the valuation bound (b) is used only for `h₀ < p²`,
`p ≤ m_{q-r}`, and `v_p(Q) ≥ q - 1` only for `p ≤ m_{q-r}`.

**Numerical check.** `python/window_mirror.py`, section "Laurent data …, Lemma19": exact integrality of
`Δ_n A₀` and of all `Δ_n A_s` for `cfgW` (`n = 1, 2`) and the Theorem 3 configuration (`n = 1, 2, 3`);
also `docs/window/arith_check_r5_q23.jsonl` (Zudilin's own ω-range, `n ≤ 3`: zero slack at some primes,
the lemma is tight).

**Status: done** (difficulty 4/5; complete, no gaps; `#print axioms Lemma19_proof`: propext,
Classical.choice, Quot.sound).
-/

open Filter Topology Finset

noncomputable section

namespace ZetaWindow

namespace Lemma19

/-! ### Integers inside `ℚ` -/

/-- The subring `ℤ ⊆ ℚ`. -/
def ZZ : Subring ℚ := (Int.castRingHom ℚ).range

theorem mem_ZZ {x : ℚ} : x ∈ ZZ ↔ ∃ z : ℤ, x = z := by
  unfold ZZ
  rw [RingHom.mem_range]
  constructor
  · rintro ⟨z, rfl⟩
    exact ⟨z, rfl⟩
  · rintro ⟨z, rfl⟩
    exact ⟨z, rfl⟩

/-- Enlarging the denominator: if `d ∣ Q` and `d x ∈ ℤ` then `Q x ∈ ℤ`. -/
theorem natCast_mul_mem_of_dvd {d Q : ℕ} (hd : d ∣ Q) {x : ℚ} (hx : (d : ℚ) * x ∈ ZZ) :
    (Q : ℚ) * x ∈ ZZ := by
  obtain ⟨e, rfl⟩ := hd
  have h : ((d * e : ℕ) : ℚ) * x = (e : ℚ) * ((d : ℚ) * x) := by push_cast; ring
  rw [h]
  exact mul_mem (natCast_mem _ _) hx

/-! ### `D_m = lcm(1, …, m)` -/

/-- `D_m ∣ D_{m'}` for `m ≤ m'`. -/
theorem lcmUpto_dvd_lcmUpto {m m' : ℕ} (h : m ≤ m') : Nat.lcmUpto m ∣ Nat.lcmUpto m' := by
  unfold Nat.lcmUpto
  exact Finset.lcm_dvd fun l hl => Finset.dvd_lcm (Finset.Icc_subset_Icc_right h hl)

/-- Every `l ∈ [1, m]` divides `D_m`. -/
theorem dvd_lcmUpto {l m : ℕ} (h1 : 1 ≤ l) (hlm : l ≤ m) : l ∣ Nat.lcmUpto m := by
  unfold Nat.lcmUpto
  exact Finset.dvd_lcm (s := Icc 1 m) (f := id) (mem_Icc.2 ⟨h1, hlm⟩)

/-! ### The `h_j` and the `m_j` -/

/-- `h` is monotone in the index on `[1, q]` (from `Admissible.eta_mono`). -/
theorem h_mono {c : Config} (hc : Admissible c) (n : ℕ) {i j : ℕ} (h1 : 1 ≤ i) (hij : i ≤ j)
    (hj : j ≤ c.q) : c.h n i ≤ c.h n j := by
  unfold Config.h
  exact Nat.add_le_add_right (Nat.mul_le_mul (hc.eta_mono i j h1 hij hj) (le_refl n)) 1

/-- `2 h_i ≤ h₀` for `1 ≤ i ≤ q` (from `η_i ≤ η_q` and `2η_q < η₀`). -/
theorem two_h_le {c : Config} (hc : Admissible c) (n : ℕ) {i : ℕ} (h1 : 1 ≤ i) (hi : i ≤ c.q) :
    2 * c.h n i ≤ c.h0 n := by
  have hm := hc.eta_mono i c.q h1 hi le_rfl
  have ht := hc.two_eta_lt
  have h2 : 2 * c.eta i * n ≤ c.eta0 * n := Nat.mul_le_mul_right n (by omega)
  unfold Config.h Config.h0
  linarith

theorem m0_le_mj (c : Config) (n j : ℕ) : m0 c n ≤ mj c n j := le_max_left _ _

/-- `m_j` is antitone in `j` on `[1, q - r]`. -/
theorem mj_anti {c : Config} (hc : Admissible c) (n : ℕ) {i i' : ℕ} (h1 : 1 ≤ i)
    (hii' : i ≤ i') (hi' : i' ≤ c.q - c.r) : mj c n i' ≤ mj c n i := by
  have hrq : c.r + 4 ≤ c.q := hc.r_add_four_le_q
  have hh : c.h n (c.r + i) ≤ c.h n (c.r + i') := h_mono hc n (by omega) (by omega) (by omega)
  unfold mj
  exact max_le_max le_rfl (Nat.sub_le_sub_left hh _)

/-! ### Divisibility of `Dprod = D_{m₁}^r D_{m₂} ⋯ D_{m_{q-r}}` -/

/-- For `1 ≤ t ≤ q - r`: `D_{m_t}^{r+t-1} D_{m₀}^{q-r-t} ∣ Dprod` (the first `r + t - 1` factors are
divisible by `D_{m_t}`, the remaining `q - r - t` by `D_{m₀}`). -/
theorem split_dvd_Dprod {c : Config} (hc : Admissible c) (n : ℕ) {t : ℕ} (ht1 : 1 ≤ t)
    (ht : t ≤ c.q - c.r) :
    Nat.lcmUpto (mj c n t) ^ (c.r + t - 1) * Nat.lcmUpto (m0 c n) ^ (c.q - c.r - t) ∣
      Dprod c n := by
  have hrq : c.r + 4 ≤ c.q := hc.r_add_four_le_q
  unfold Dprod
  rw [← Finset.Ico_add_one_right_eq_Icc,
    ← Finset.prod_Ico_consecutive _ (show 2 ≤ t + 1 by omega) (show t + 1 ≤ c.q - c.r + 1 by omega)]
  have h1 : Nat.lcmUpto (mj c n t) ^ c.r ∣ Nat.lcmUpto (mj c n 1) ^ c.r :=
    pow_dvd_pow_of_dvd (lcmUpto_dvd_lcmUpto (mj_anti hc n le_rfl ht1 ht)) _
  have h2 : Nat.lcmUpto (mj c n t) ^ (t - 1) ∣ ∏ i ∈ Ico 2 (t + 1), Nat.lcmUpto (mj c n i) := by
    have e : ∏ _i ∈ Ico 2 (t + 1), Nat.lcmUpto (mj c n t) = Nat.lcmUpto (mj c n t) ^ (t - 1) := by
      rw [prod_const, Nat.card_Ico]
      rfl
    rw [← e]
    refine Finset.prod_dvd_prod_of_dvd _ _ fun i hi => ?_
    rw [Finset.mem_Ico] at hi
    exact lcmUpto_dvd_lcmUpto (mj_anti hc n (by omega) (by omega) ht)
  have h3 : Nat.lcmUpto (m0 c n) ^ (c.q - c.r - t) ∣
      ∏ i ∈ Ico (t + 1) (c.q - c.r + 1), Nat.lcmUpto (mj c n i) := by
    have e : ∏ _i ∈ Ico (t + 1) (c.q - c.r + 1), Nat.lcmUpto (m0 c n) =
        Nat.lcmUpto (m0 c n) ^ (c.q - c.r - t) := by
      rw [prod_const, Nat.card_Ico]
      congr 1
      omega
    rw [← e]
    exact Finset.prod_dvd_prod_of_dvd _ _ fun i _ => lcmUpto_dvd_lcmUpto (m0_le_mj c n i)
  have e : Nat.lcmUpto (mj c n t) ^ (c.r + t - 1) =
      Nat.lcmUpto (mj c n t) ^ c.r * Nat.lcmUpto (mj c n t) ^ (t - 1) := by
    rw [← pow_add]
    congr 1
    omega
  rw [e, mul_assoc]
  exact mul_dvd_mul h1 (mul_dvd_mul h2 h3)

/-- `p^{q-1} ∣ Dprod` for `1 ≤ p ≤ m_{q-r}` (so `v_p(Dprod) ≥ q - 1` for the primes of `Φ_n`). -/
theorem pow_dvd_Dprod {c : Config} (hc : Admissible c) (n : ℕ) {p : ℕ} (hp1 : 1 ≤ p)
    (hp : p ≤ mj c n (c.q - c.r)) : p ^ (c.q - 1) ∣ Dprod c n := by
  have hrq : c.r + 4 ≤ c.q := hc.r_add_four_le_q
  have h := split_dvd_Dprod hc n (t := c.q - c.r) (by omega) le_rfl
  rw [show c.r + (c.q - c.r) - 1 = c.q - 1 by omega, Nat.sub_self, pow_zero, mul_one] at h
  exact (pow_dvd_pow_of_dvd (dvd_lcmUpto hp1 hp) _).trans h

/-! ### Periodicity of `ω_{k,p}` in `k` -/

/-- `ω_{k + pm, p} = ω_{k,p}`: under `k ↦ k + pm` every floor of (8.9) shifts by `±m`, and the
shifts cancel. -/
theorem omegaKP_add_mul (c : Config) (n p k m : ℕ) (hp : 0 < p) :
    omegaKP c n p (k + p * m) = omegaKP c n p k := by
  have hp' : (p : ℤ) ≠ 0 := by exact_mod_cast hp.ne'
  have sh1 : ∀ a : ℤ, (a + (m : ℤ) * p) / p = a / p + m := fun a =>
    Int.add_mul_ediv_right a m hp'
  have sh2 : ∀ a : ℤ, (a + (-(m : ℤ)) * p) / p = a / p - m := fun a => by
    rw [Int.add_mul_ediv_right a (-(m : ℤ)) hp']
    ring
  have e : ((k + p * m : ℕ) : ℤ) = (k : ℤ) + (m : ℤ) * p := by push_cast; ring
  unfold omegaKP
  rw [e]
  congr 1
  · refine Finset.sum_congr rfl fun j _ => ?_
    rw [show (k : ℤ) + (m : ℤ) * p - 1 = ((k : ℤ) - 1) + (m : ℤ) * p by ring,
      show (c.h0 n : ℤ) - ((k : ℤ) + (m : ℤ) * p) - 1 = ((c.h0 n : ℤ) - k - 1) + (-(m : ℤ)) * p by ring,
      show (k : ℤ) + (m : ℤ) * p - c.h n j = ((k : ℤ) - c.h n j) + (m : ℤ) * p by ring,
      show (c.h0 n : ℤ) - c.h n j - ((k : ℤ) + (m : ℤ) * p) =
        ((c.h0 n : ℤ) - c.h n j - k) + (-(m : ℤ)) * p by ring,
      sh1, sh1, sh2, sh2]
    ring
  · refine Finset.sum_congr rfl fun j _ => ?_
    rw [show (k : ℤ) + (m : ℤ) * p - c.h n j = ((k : ℤ) - c.h n j) + (m : ℤ) * p by ring,
      show (c.h0 n : ℤ) - c.h n j - ((k : ℤ) + (m : ℤ) * p) =
        ((c.h0 n : ℤ) - c.h n j - k) + (-(m : ℤ)) * p by ring,
      sh1, sh2]
    ring

/-- `ω_p ≤ ω_{k,p}` for every `k` (`ω_p` is the minimum over the residues `0 ≤ k < p`). -/
theorem omegaP_le (c : Config) (n : ℕ) {p : ℕ} (hp : 0 < p) (k : ℕ) :
    omegaP c n p ≤ omegaKP c n p k := by
  have h := omegaKP_add_mul c n p (k % p) (k / p) hp
  rw [Nat.mod_add_div] at h
  rw [h]
  unfold omegaP
  simp only [hp, ↓reduceDIte]
  exact Finset.inf'_le _ (Finset.mem_range.2 (Nat.mod_lt k hp))

/-! ### `v_p(x) ≥ c`, with `0` counting as `+∞` -/

/-- `x = 0` or `c ≤ v_p(x)`. -/
def VpGe (p : ℕ) (c : ℤ) (x : ℚ) : Prop :=
  x = 0 ∨ c ≤ padicValRat p x

section VpGe

variable {p : ℕ}

theorem VpGe.zero (c : ℤ) : VpGe p c 0 := Or.inl rfl

theorem VpGe.mono {c c' : ℤ} {x : ℚ} (h : VpGe p c x) (hc : c' ≤ c) : VpGe p c' x := by
  rcases h with h | h
  · exact Or.inl h
  · exact Or.inr (hc.trans h)

/-- Natural numbers have `v_p ≥ 0`. -/
theorem VpGe.natCast (a : ℕ) : VpGe p 0 (a : ℚ) := by
  right
  rw [padicValRat.of_nat]
  exact Int.natCast_nonneg _

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

end VpGe

/-! ### (b) Valuations at the large primes -/

/-- `v_p(B_{j,k}) ≥ ω_p - (q - j)` for `h₀ < p²` (`Stmt_LaurentVal` and `ω_p ≤ ω_{k,p}`). -/
theorem vp_B (hV : Stmt_LaurentVal) {c : Config} (hc : Admissible c) {n : ℕ} (hn : 1 ≤ n)
    {p : ℕ} (hp : p.Prime) (hp2 : c.h0 n < p ^ 2) {j k : ℕ} (hj : j ∈ Icc (c.r + 1) c.q)
    (hk : k ∈ Krange c n) :
    VpGe p (omegaP c n p - ((c.q - j : ℕ) : ℤ)) (B c n j k) := by
  by_cases hB : B c n j k = 0
  · exact Or.inl hB
  · right
    have h1 := hV c hc n hn p hp hp2 j k hj hk hB
    have h2 := omegaP_le c n hp.pos k
    linarith

/-- `v_p(A_s) ≥ ω_p - (q - 1)` for `h₀ < p²`. -/
theorem vp_Acoef (hV : Stmt_LaurentVal) {c : Config} (hc : Admissible c) {n : ℕ} (hn : 1 ≤ n)
    {p : ℕ} (hp : p.Prime) (hp2 : c.h0 n < p ^ 2) {s : ℕ} (hs : s ∈ Icc c.r (c.q - 1)) :
    VpGe p (omegaP c n p - ((c.q - 1 : ℕ) : ℤ)) (Acoef c n s) := by
  have := Fact.mk hp
  have hs' := Finset.mem_Icc.1 hs
  have hrq : c.r + 4 ≤ c.q := hc.r_add_four_le_q
  have hj : s + 1 ∈ Icc (c.r + 1) c.q := by
    rw [Finset.mem_Icc]
    omega
  unfold Acoef
  refine ((VpGe.natCast _).mul (VpGe.sum _ _ fun k hk => vp_B hV hc hn hp hp2 hj hk)).mono ?_
  omega

/-- `v_p(A₀) ≥ ω_p - (q - 1)` for `h₀ < p²`. -/
theorem vp_A0 (hV : Stmt_LaurentVal) (hH : Stmt_Harmonic) {c : Config} (hc : Admissible c)
    {n : ℕ} (hn : 1 ≤ n) {p : ℕ} (hp : p.Prime) (hp2 : c.h0 n < p ^ 2) :
    VpGe p (omegaP c n p - ((c.q - 1 : ℕ) : ℤ)) (A0 c n) := by
  have := Fact.mk hp
  have hrq : c.r + 4 ≤ c.q := hc.r_add_four_le_q
  unfold A0
  refine VpGe.sum _ _ fun j hj => ?_
  have hj' := Finset.mem_Icc.1 hj
  refine ((VpGe.natCast _).mul (VpGe.sum _ _ fun k hk => ?_)).mono (le_of_eq (zero_add _).symm)
  have hk' : c.h n 1 ≤ k ∧ k ≤ c.h0 n - c.h n 1 := Finset.mem_Icc.1 hk
  have h1 := two_h_le hc n (i := 1) le_rfl (by omega)
  have hN : k - c.h n 1 < p ^ 2 := by omega
  have hharm : VpGe p (-((j - 1 : ℕ) : ℤ)) (harm (k - c.h n 1) (j - 1)) := by
    by_cases h0 : harm (k - c.h n 1) (j - 1) = 0
    · exact Or.inl h0
    · exact Or.inr (hH.val _ _ p hp hN h0)
  refine ((vp_B hV hc hn hp hp2 hj hk).mul hharm).mono ?_
  omega

/-! ### (a) Rough inclusions -/

/-- `Q A_s ∈ ℤ` (`Stmt_LaurentInt` and `D_{m₀}^{q-j} ∣ Q`). -/
theorem rough_Acoef (hI : Stmt_LaurentInt) {c : Config} (hc : Admissible c) {n : ℕ}
    (hn : 1 ≤ n) {s : ℕ} (hs : s ∈ Icc c.r (c.q - 1)) :
    (Dprod c n : ℚ) * Acoef c n s ∈ ZZ := by
  have hs' := Finset.mem_Icc.1 hs
  have hrq : c.r + 4 ≤ c.q := hc.r_add_four_le_q
  have hj : s + 1 ∈ Icc (c.r + 1) c.q := by
    rw [Finset.mem_Icc]
    omega
  have hdvd : Nat.lcmUpto (m0 c n) ^ (c.q - (s + 1)) ∣ Dprod c n := by
    have h := split_dvd_Dprod hc n (t := s + 1 - c.r) (by omega) (by omega)
    rw [show c.q - c.r - (s + 1 - c.r) = c.q - (s + 1) by omega] at h
    exact (dvd_mul_left _ _).trans h
  unfold Acoef
  rw [mul_left_comm, Finset.mul_sum]
  refine mul_mem (natCast_mem _ _) (sum_mem fun k hk => natCast_mul_mem_of_dvd hdvd ?_)
  obtain ⟨z, hz⟩ := hI c hc n hn (s + 1) k hj hk
  exact mem_ZZ.2 ⟨z, by push_cast; exact hz⟩

/-- `Q A₀ ∈ ℤ` (`Stmt_LaurentSupp`, `Stmt_LaurentInt`, `Stmt_Harmonic.int` and
`D_{m_{j-r}}^{j-1} D_{m₀}^{q-j} ∣ Q`). -/
theorem rough_A0 (hS : Stmt_LaurentSupp) (hI : Stmt_LaurentInt) (hH : Stmt_Harmonic)
    {c : Config} (hc : Admissible c) {n : ℕ} (hn : 1 ≤ n) :
    (Dprod c n : ℚ) * A0 c n ∈ ZZ := by
  have hrq : c.r + 4 ≤ c.q := hc.r_add_four_le_q
  unfold A0
  rw [Finset.mul_sum]
  refine sum_mem fun j hj => ?_
  have hj' := Finset.mem_Icc.1 hj
  rw [mul_left_comm, Finset.mul_sum]
  refine mul_mem (natCast_mem _ _) (sum_mem fun k hk => ?_)
  by_cases hB : B c n j k = 0
  · rw [hB, zero_mul, mul_zero]
    exact zero_mem _
  have hk' : c.h n 1 ≤ k ∧ k ≤ c.h0 n - c.h n 1 := Finset.mem_Icc.1 hk
  have hsupp : c.h n j ≤ k ∧ k ≤ c.h0 n - c.h n j := by
    by_contra h
    exact hB (hS c hc n hn j k hj (by omega))
  have h1 := two_h_le hc n (i := 1) le_rfl (by omega)
  have h2 := two_h_le hc n (i := j) (by omega) hj'.2
  have hdvd := split_dvd_Dprod hc n (t := j - c.r) (by omega) (by omega)
  rw [show c.r + (j - c.r) - 1 = j - 1 by omega, show c.q - c.r - (j - c.r) = c.q - j by omega]
    at hdvd
  refine natCast_mul_mem_of_dvd hdvd ?_
  obtain ⟨z1, hz1⟩ := hI c hc n hn j k hj hk
  have hN : k - c.h n 1 ≤ mj c n (j - c.r) := by
    unfold mj
    rw [show c.r + (j - c.r) = j by omega]
    exact le_max_of_le_right (by omega)
  obtain ⟨z2, hz2⟩ := hH.int (k - c.h n 1) (mj c n (j - c.r)) (j - 1) hN
  refine mem_ZZ.2 ⟨z2 * z1, ?_⟩
  push_cast
  rw [← hz1, ← hz2]
  ring

/-! ### (c) Assembly: `Φ_n ∣ Q A` -/

/-- If `Q A ∈ ℤ` and `v_p(A) ≥ ω_p - (q-1)` at every prime `p` with `h₀ < p²`, then `Δ_n A ∈ ℤ`. -/
theorem int_of_rough_of_val {c : Config} (hc : Admissible c) (n : ℕ) (A : ℚ)
    (hrough : (Dprod c n : ℚ) * A ∈ ZZ)
    (hval : ∀ p : ℕ, p.Prime → c.h0 n < p ^ 2 →
      VpGe p (omegaP c n p - ((c.q - 1 : ℕ) : ℤ)) A) :
    ∃ z : ℤ, Delta c n * A = z := by
  obtain ⟨z0, hz0⟩ := mem_ZZ.1 hrough
  have hdvd : ((PhiN c n : ℕ) : ℤ) ∣ z0 := by
    unfold PhiN
    rw [Nat.cast_prod]
    apply Finset.prod_dvd_of_coprime
    · intro p hp p' hp' hne
      rw [Finset.coe_filter] at hp hp'
      exact Nat.isCoprime_iff_coprime.2
        (Nat.Coprime.pow _ _ ((Nat.coprime_primes hp.2.1 hp'.2.1).2 hne))
    · intro p hp
      rw [Finset.mem_filter, Finset.mem_range] at hp
      obtain ⟨hpm, hpp, hp2⟩ := hp
      have := Fact.mk hpp
      rw [Nat.cast_pow, padicValInt_dvd_iff]
      by_cases hz : z0 = 0
      · exact Or.inl hz
      right
      have hA : A ≠ 0 := by
        rintro rfl
        rw [mul_zero] at hz0
        exact hz (by exact_mod_cast hz0.symm)
      have hQ : (Dprod c n : ℚ) ≠ 0 := by exact_mod_cast (Dprod_pos c n).ne'
      have hvQ : ((c.q - 1 : ℕ) : ℤ) ≤ padicValRat p (Dprod c n : ℚ) := by
        rw [padicValRat.of_nat]
        exact_mod_cast (padicValNat_dvd_iff_le (Dprod_pos c n).ne').1
          (pow_dvd_Dprod hc n hpp.one_lt.le (by omega))
      have hvA : omegaP c n p - ((c.q - 1 : ℕ) : ℤ) ≤ padicValRat p A :=
        (hval p hpp hp2).resolve_left hA
      have hv : padicValRat p (z0 : ℚ) = padicValRat p (Dprod c n : ℚ) + padicValRat p A := by
        rw [← hz0, padicValRat.mul hQ hA]
      rw [padicValRat.of_int] at hv
      rw [Int.toNat_le]
      omega
  obtain ⟨w, hw⟩ := hdvd
  refine ⟨w, ?_⟩
  have hΦ : (PhiN c n : ℚ) ≠ 0 := by exact_mod_cast (PhiN_pos c n).ne'
  unfold Delta
  rw [div_mul_eq_mul_div, hz0, hw]
  push_cast
  field_simp

end Lemma19

open Lemma19 in
theorem Lemma19_proof (hS : Stmt_LaurentSupp) (hI : Stmt_LaurentInt) (hV : Stmt_LaurentVal)
    (hH : Stmt_Harmonic) : Stmt_Lemma19 := by
  intro c hc n hn
  refine ⟨?_, fun s hs => ?_⟩
  · exact int_of_rough_of_val hc n _ (rough_A0 hS hI hH hc hn)
      fun p hp hp2 => vp_A0 hV hH hc hn hp hp2
  · exact int_of_rough_of_val hc n _ (rough_Acoef hI hc hn hs)
      fun p hp hp2 => vp_Acoef hV hc hn hp hp2 hs

#print axioms Lemma19_proof

end ZetaWindow

end
