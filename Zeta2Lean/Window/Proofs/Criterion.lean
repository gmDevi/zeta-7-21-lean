module

public import Zeta2Lean.Window.Statements

@[expose] public section

set_option linter.style.header false
set_option linter.style.longLine false

/-!
# The irrationality criterion (JTNB Proposition 5, elementary part; docs/window/proof.md §4)

**Statement.** `Stmt_Criterion` (no hypotheses):
if `F_n = -a₀(n) + ∑_{s ∈ S} a_s(n) ζ_s`, `Δ_n a₀(n) ∈ ℤ`, `Δ_n a_s(n) ∈ ℤ`, `0 < Δ_n ≤ e^{c₂ n}`,
`|F_n| ≤ e^{-c₀ n}` (all eventually), `c₂ < c₀`, and `F_n ≠ 0` frequently, then
`¬ ∀ s ∈ S, ∃ q : ℚ, ζ_s = q`.

**Informal proof.** Suppose `ζ_s = q_s ∈ ℚ` for all `s ∈ S`, and let `d = ∏_{s ∈ S} (q_s).den ≥ 1`,
so `d q_s ∈ ℤ`.  For every `n` in the (eventual) set where all hypotheses hold,
`z_n := d Δ_n F_n = -d (Δ_n a₀(n)) + ∑_s (Δ_n a_s(n)) (d q_s)` is an integer, and
`|z_n| ≤ d e^{c₂ n} e^{-c₀ n} = d e^{-(c₀-c₂) n}`.  Since `e^{-(c₀-c₂) n} → 0`, eventually
`|z_n| < 1`, i.e. `z_n = 0`, i.e. `F_n = 0` (as `d > 0`, `Δ_n > 0`).  This contradicts `F_n ≠ 0`
frequently (`Filter.Frequently.and_eventually` gives an `n` where everything holds at once).

**Formal proof (as done below).**
* `Criterion.common_denom`: `d = ∏_{s ∈ S} den(q_s) > 0` and integers `p_s` with `p_s = d q_s`
  (for `s ∈ S`).
* `Criterion.tendsto_small`: `d e^{-(c₀ - c₂) n} → 0`, hence eventually `< 1`.
* `Criterion_proof`: pick one `n` where `F_n ≠ 0` and all eventual hypotheses hold, build the integer
  `Z = -d z₀ + ∑_s z_s p_s` (with `Δ_n a₀ = z₀`, `Δ_n a_s = z_s`), show `Z = d Δ_n F_n` and
  `|Z| < 1`, so `Z = 0` (`Int.abs_lt_one_iff`), hence `F_n = 0`: contradiction.
The case `S = ∅` needs no special treatment (then `d = 1`).

**Status: done** (complete; `#print axioms Criterion_proof` lists only `propext`,
`Classical.choice`, `Quot.sound`).
-/

open Filter Topology Finset

noncomputable section

namespace ZetaWindow

namespace Criterion

/-- A common denominator of finitely many rationals `q_s` (`s ∈ S`): `d = ∏_{s ∈ S} den(q_s) > 0`
and integers `p_s` with `p_s = d q_s` for every `s ∈ S`. -/
lemma common_denom (S : Finset ℕ) (q : ℕ → ℚ) :
    ∃ d : ℕ, 0 < d ∧ ∃ p : ℕ → ℤ, ∀ s ∈ S, ((p s : ℤ) : ℚ) = (d : ℚ) * q s := by
  refine ⟨∏ s ∈ S, (q s).den, Finset.prod_pos (fun s _ => (q s).den_pos), ?_⟩
  refine ⟨fun s => (q s).num * (((∏ i ∈ S, (q i).den) / (q s).den : ℕ) : ℤ), ?_⟩
  intro s hs
  have hdvd : (q s).den ∣ ∏ i ∈ S, (q i).den := Finset.dvd_prod_of_mem _ hs
  obtain ⟨c, hc⟩ := hdvd
  beta_reduce
  rw [hc, Nat.mul_div_cancel_left c (q s).den_pos]
  push_cast
  rw [← Rat.mul_den_eq_num (q s)]
  ring

/-- For `c₂ < c₀` and any constant `d`, `d e^{-(c₀ - c₂) n} → 0` as `n → ∞`. -/
lemma tendsto_small (d c2 c0 : ℝ) (hc : c2 < c0) :
    Tendsto (fun n : ℕ => d * Real.exp (-((c0 - c2) * n))) atTop (𝓝 0) := by
  have h1 : Tendsto (fun n : ℕ => (c0 - c2) * (n : ℝ)) atTop atTop :=
    Tendsto.const_mul_atTop (sub_pos.mpr hc) tendsto_natCast_atTop_atTop
  have h2 : Tendsto (fun n : ℕ => Real.exp (-((c0 - c2) * n))) atTop (𝓝 0) :=
    Real.tendsto_exp_neg_atTop_nhds_zero.comp h1
  have h3 := h2.const_mul d
  rwa [mul_zero] at h3

/-- Cast a rational identity `x * y = z` (`z ∈ ℤ`) to `ℝ`. -/
lemma cast_mul_eq_int {x y : ℚ} {z : ℤ} (h : x * y = z) : (x : ℝ) * (y : ℝ) = (z : ℝ) := by
  have := congrArg (fun t : ℚ => (t : ℝ)) h
  push_cast at this
  exact this

end Criterion

open Criterion in
/-- **The irrationality criterion** (JTNB Proposition 5, elementary part; docs/window/proof.md §4). -/
theorem Criterion_proof : Stmt_Criterion := by
  intro S ζs Δ a0 a F c2 c0 hc hΔpos hF ha0 ha hΔle hFle hfreq hall
  -- all `ζ_s` rational: `ζ_s = q_s`, common denominator `d`, `d q_s = p_s ∈ ℤ`
  choose! q hq using hall
  obtain ⟨d, hdpos, p, hp⟩ := common_denom S q
  have hdR : (0 : ℝ) < d := by exact_mod_cast hdpos
  have hsmall : ∀ᶠ n : ℕ in atTop, (d : ℝ) * Real.exp (-((c0 - c2) * n)) < 1 :=
    (tendsto_small (d : ℝ) c2 c0 hc).eventually_lt_const one_pos
  -- one `n` where `F_n ≠ 0` and every eventual hypothesis holds
  obtain ⟨n, hFn, hΔn, hFeq, ha0n, han, hΔlen, hFlen, hsmn⟩ :=
    (hfreq.and_eventually
      (hΔpos.and (hF.and (ha0.and (ha.and (hΔle.and (hFle.and hsmall))))))).exists
  obtain ⟨z0, hz0⟩ := ha0n
  choose! zs hzs using han
  have hΔR : (0 : ℝ) < (Δ n : ℝ) := by exact_mod_cast hΔn
  -- the integer `Z = d Δ_n F_n`
  set Z : ℤ := -((d : ℤ) * z0) + ∑ s ∈ S, zs s * p s with hZ
  have e0 : (Δ n : ℝ) * (a0 n : ℝ) = (z0 : ℝ) := cast_mul_eq_int hz0
  have es : ∀ s ∈ S,
      (d : ℝ) * ((Δ n : ℝ) * ((a n s : ℝ) * ζs s)) = (zs s : ℝ) * (p s : ℝ) := by
    intro s hs
    have h1 : (Δ n : ℝ) * (a n s : ℝ) = (zs s : ℝ) := cast_mul_eq_int (hzs s hs)
    have h2 : (d : ℝ) * ζs s = (p s : ℝ) := by
      have h3 := congrArg (fun t : ℚ => (t : ℝ)) (hp s hs)
      push_cast at h3
      rw [hq s hs, h3]
    calc (d : ℝ) * ((Δ n : ℝ) * ((a n s : ℝ) * ζs s))
        = ((Δ n : ℝ) * (a n s : ℝ)) * ((d : ℝ) * ζs s) := by ring
      _ = (zs s : ℝ) * (p s : ℝ) := by rw [h1, h2]
  have hsum : ∑ s ∈ S, (zs s : ℝ) * (p s : ℝ) =
      ∑ s ∈ S, (d : ℝ) * ((Δ n : ℝ) * ((a n s : ℝ) * ζs s)) :=
    Finset.sum_congr rfl (fun s hs => (es s hs).symm)
  have hZeq : (Z : ℝ) = (d : ℝ) * ((Δ n : ℝ) * F n) := by
    rw [hFeq, hZ]
    push_cast
    rw [hsum, ← e0, mul_add, mul_add, Finset.mul_sum, Finset.mul_sum]
    ring
  -- `|Z| ≤ d e^{c₂ n} e^{-c₀ n} = d e^{-(c₀ - c₂) n} < 1`
  have hZabs : |(Z : ℝ)| < 1 := by
    rw [hZeq, abs_mul, abs_mul, abs_of_pos hdR, abs_of_pos hΔR]
    calc (d : ℝ) * ((Δ n : ℝ) * |F n|)
        ≤ (d : ℝ) * (Real.exp (c2 * n) * Real.exp (-(c0 * n))) := by gcongr
      _ = (d : ℝ) * Real.exp (-((c0 - c2) * n)) := by
          rw [← Real.exp_add]
          congr 2
          ring
      _ < 1 := hsmn
  have hZ0 : Z = 0 := by
    have hZabs' : |Z| < 1 := by exact_mod_cast hZabs
    exact Int.abs_lt_one_iff.mp hZabs'
  -- hence `d Δ_n F_n = 0`, so `F_n = 0`
  have hprod : (d : ℝ) * ((Δ n : ℝ) * F n) = 0 := by
    rw [← hZeq, hZ0, Int.cast_zero]
  rcases mul_eq_zero.mp hprod with h | h
  · exact hdR.ne' h
  · rcases mul_eq_zero.mp h with h' | h'
    · exact hΔR.ne' h'
    · exact hFn h'

end ZetaWindow

end
