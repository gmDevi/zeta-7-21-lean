module

public import Zeta2Lean.Window.Proofs.L20U.Cert

@[expose] public section

set_option linter.style.header false
set_option linter.style.longLine false

/-!
# Theorem U, part 5b: the landscape on the line `x₀ = 159` (Lemma 5 of crude-upper-bound.md)

`U(η) = C_η - 336 + 5[Gf(159,η) - Gf(-1,η)] - ∑_j [Gf(159-η_j,η) - Gf(η_j-1,η)] - 2πη` (`Uw`,
`Pointwise.lean`) satisfies

* `U(η) ≤ -749` for every `η > 0` (`Uw_le`; true maximum `-750.6309…` at `η ≈ 9.05`),
* `U(η) ≤ -749 - (η - 60)/10` for `η ≥ 60` (`Uw_le_tail`).

Proof (crude-upper-bound.md §6 with the tangent point `p = 9`):
* `U' = dUw` on `(0, ∞)` (`Uw_hasDerivAt`, from `∂_η Gf(a, η) = arctan(a/η)`):
  `U'(η) = 5[arctan(159/η) + arctan(1/η)] - ∑_j [arctan((159-η_j)/η) - arctan((η_j-1)/η)] - 2π`;
* **concavity** on `(0, 46]` (`dUw_anti`): `arctan(159/η)`, `arctan(1/η)` decrease, and for
  `0 < a < b`, `arctan(b/η) - arctan(a/η) = arctan((b-a)η/(η²+ab))` increases on `(0, a]`
  (`arctan_sub_eq`, `arctan_diff_mono`); here `a = η_j - 1 ≥ 46`, `b = 159 - η_j`;
* **tangent** (`Uw_tangent`, mean value theorem): `U(η) ≤ U(9) + U'(9)(η - 9)` on `(0, 46]`, and
  with the certified `U(9) ≤ -750.631301`, `0 ≤ U'(9) ≤ 0.014739` (`L20U/Cert.lean`):
  `U ≤ -750.631301 + 37 · 0.014739 < -749` on `(0, 46]`;
* **cell** `[46, 60]`: `U' ≤ 5[arctan(159/46) + arctan(1/46)] - 23[arctan(93/60) - arctan(65/46)] - 2π
  ≤ -0.715` (`dUw_cell`; `93 ≤ 159 - η_j`, `η_j - 1 ≤ 65`), so `U` decreases there;
* **tail** `[60, ∞)`: every bracket `arctan((159-η_j)/η) - arctan((η_j-1)/η)` is `≥ 0`, so
  `U' ≤ 5[arctan(159/60) + arctan(1/60)] - 2π ≤ -0.150 < -1/10` (`dUw_tail`).
-/

open Complex MeasureTheory Filter Topology Set Finset
open scoped Real

noncomputable section

namespace ZetaWindow

namespace L20U

theorem Uw_hasDerivAt {η : ℝ} (hη : 0 < η) : HasDerivAt Uw (dUw η) η := by
  have h1 := ((Gf_hasDerivAt_y 159 hη).sub (Gf_hasDerivAt_y (-1) hη)).const_mul 5
  have h2 : HasDerivAt
      (fun x => ∑ j ∈ Icc 1 23, (Gf (159 - (etaW j : ℝ)) x - Gf ((etaW j : ℝ) - 1) x))
      (∑ j ∈ Icc 1 23,
        (Real.arctan ((159 - (etaW j : ℝ)) / η) - Real.arctan (((etaW j : ℝ) - 1) / η))) η :=
    HasDerivAt.fun_sum fun j _ => (Gf_hasDerivAt_y _ hη).sub (Gf_hasDerivAt_y _ hη)
  have h3 := (hasDerivAt_id η).const_mul (2 * π)
  have h := ((h1.const_add (Ceta - 336)).sub h2).sub h3
  convert h using 1
  · funext x
    simp only [Uw, id, Pi.sub_apply]
  · unfold dUw
    rw [neg_div, Real.arctan_neg]
    ring

theorem arctan_sub_eq {a b η : ℝ} (ha : 0 < a) (hb : 0 < b) (hη : 0 < η) :
    Real.arctan (b / η) - Real.arctan (a / η) = Real.arctan ((b - a) * η / (η ^ 2 + a * b)) := by
  have hxy : b / η * -(a / η) < 1 := by
    have h0 : 0 ≤ b / η * (a / η) := by positivity
    have e : b / η * -(a / η) = -(b / η * (a / η)) := by ring
    linarith
  have h := Real.arctan_add hxy
  rw [Real.arctan_neg] at h
  rw [sub_eq_add_neg, h]
  congr 1
  have hη0 : η ≠ 0 := hη.ne'
  have hden : η ^ 2 + a * b ≠ 0 := by positivity
  have hden2 : b * a + η ^ 2 ≠ 0 := by positivity
  have e1 : b / η + -(a / η) = (b - a) / η := by ring
  have e2 : (1 : ℝ) - b / η * -(a / η) = (η ^ 2 + a * b) / η ^ 2 := by
    field_simp
    ring
  rw [e1, e2, div_div_eq_mul_div]
  field_simp

/-- For `0 < a < b`, `η ↦ arctan(b/η) - arctan(a/η)` is increasing on `(0, a]`. -/
theorem arctan_diff_mono {a b η₁ η₂ : ℝ} (ha : 0 < a) (hab : a < b) (h1 : 0 < η₁)
    (h12 : η₁ ≤ η₂) (h2 : η₂ ≤ a) :
    Real.arctan (b / η₁) - Real.arctan (a / η₁) ≤ Real.arctan (b / η₂) - Real.arctan (a / η₂) := by
  have hb : 0 < b := by linarith
  have hη₂ : 0 < η₂ := by linarith
  rw [arctan_sub_eq ha hb h1, arctan_sub_eq ha hb hη₂]
  apply Real.arctan_strictMono.monotone
  rw [div_le_div_iff₀ (by positivity) (by positivity)]
  have h3 : η₁ * η₂ ≤ a * b := by nlinarith
  nlinarith [mul_nonneg (mul_nonneg (sub_nonneg.2 hab.le) (sub_nonneg.2 h12)) (sub_nonneg.2 h3)]

theorem etaW_mem {j : ℕ} (hj : j ∈ Finset.Icc 1 23) :
    (47 : ℝ) ≤ etaW j ∧ (etaW j : ℝ) ≤ 66 := by
  constructor
  · exact_mod_cast etaW_ge j
  · exact_mod_cast etaW_le (Finset.mem_Icc.1 hj).2

/-- **Concavity**: `U'` is decreasing on `(0, 46]`. -/
theorem dUw_anti {η₁ η₂ : ℝ} (h1 : 0 < η₁) (h12 : η₁ ≤ η₂) (h2 : η₂ ≤ 46) :
    dUw η₂ ≤ dUw η₁ := by
  unfold dUw
  have t1 : Real.arctan (159 / η₂) ≤ Real.arctan (159 / η₁) :=
    Real.arctan_strictMono.monotone (div_le_div_of_nonneg_left (by norm_num) h1 h12)
  have t2 : Real.arctan (1 / η₂) ≤ Real.arctan (1 / η₁) :=
    Real.arctan_strictMono.monotone (div_le_div_of_nonneg_left (by norm_num) h1 h12)
  have t3 : ∑ j ∈ Icc 1 23,
      (Real.arctan ((159 - (etaW j : ℝ)) / η₁) - Real.arctan (((etaW j : ℝ) - 1) / η₁)) ≤
      ∑ j ∈ Icc 1 23,
        (Real.arctan ((159 - (etaW j : ℝ)) / η₂) - Real.arctan (((etaW j : ℝ) - 1) / η₂)) := by
    apply Finset.sum_le_sum
    intro j hj
    obtain ⟨he1, he2⟩ := etaW_mem hj
    exact arctan_diff_mono (by linarith) (by linarith) h1 h12 (by linarith)
  linarith

/-- **Tangent inequality** on `(0, 46]` (concavity + mean value theorem). -/
theorem Uw_tangent {p η : ℝ} (hp : 0 < p) (hp46 : p ≤ 46) (hη : 0 < η) (hη46 : η ≤ 46) :
    Uw η ≤ Uw p + dUw p * (η - p) := by
  rcases lt_trichotomy η p with h | h | h
  · obtain ⟨ξ, hξ, hξeq⟩ := exists_hasDerivAt_eq_slope Uw dUw h
      (fun x hx => (Uw_hasDerivAt (by linarith [hx.1])).continuousAt.continuousWithinAt)
      (fun x hx => Uw_hasDerivAt (by linarith [hx.1]))
    have hd := dUw_anti (by linarith [hξ.1]) hξ.2.le hp46
    rw [hξeq, le_div_iff₀ (by linarith)] at hd
    nlinarith
  · subst h; simp
  · obtain ⟨ξ, hξ, hξeq⟩ := exists_hasDerivAt_eq_slope Uw dUw h
      (fun x hx => (Uw_hasDerivAt (by linarith [hx.1])).continuousAt.continuousWithinAt)
      (fun x hx => Uw_hasDerivAt (by linarith [hx.1]))
    have hd := dUw_anti hp hξ.1.le (by linarith [hξ.2])
    rw [hξeq, div_le_iff₀ (by linarith)] at hd
    nlinarith

/-- **Monotone cell** `[46, 60]`: `U' ≤ -1/2`. -/
theorem dUw_cell {ζ : ℝ} (h46 : 46 ≤ ζ) (h60 : ζ ≤ 60) : dUw ζ ≤ -1 / 2 := by
  have hζ : 0 < ζ := by linarith
  have t1 : Real.arctan (159 / ζ) ≤ Real.arctan (159 / 46) :=
    Real.arctan_strictMono.monotone (div_le_div_of_nonneg_left (by norm_num) (by norm_num) h46)
  have t2 : Real.arctan (1 / ζ) ≤ Real.arctan (1 / 46) :=
    Real.arctan_strictMono.monotone (div_le_div_of_nonneg_left (by norm_num) (by norm_num) h46)
  have t3 : ∑ _j ∈ Icc 1 23, (Real.arctan (31 / 20) - Real.arctan (65 / 46)) ≤
      ∑ j ∈ Icc 1 23,
        (Real.arctan ((159 - (etaW j : ℝ)) / ζ) - Real.arctan (((etaW j : ℝ) - 1) / ζ)) := by
    apply Finset.sum_le_sum
    intro j hj
    obtain ⟨he1, he2⟩ := etaW_mem hj
    have u1 : Real.arctan (31 / 20) ≤ Real.arctan ((159 - (etaW j : ℝ)) / ζ) := by
      apply Real.arctan_strictMono.monotone
      rw [le_div_iff₀ hζ]
      linarith
    have u2 : Real.arctan (((etaW j : ℝ) - 1) / ζ) ≤ Real.arctan (65 / 46) := by
      apply Real.arctan_strictMono.monotone
      rw [div_le_iff₀ hζ]
      linarith
    linarith
  rw [Finset.sum_const, Nat.card_Icc, nsmul_eq_mul] at t3
  have hc := cell_le
  unfold dUw
  push_cast at t3
  linarith

/-- **Tail** `[60, ∞)`: `U' ≤ -1/10`. -/
theorem dUw_tail {ζ : ℝ} (h60 : 60 ≤ ζ) : dUw ζ ≤ -1 / 10 := by
  have hζ : 0 < ζ := by linarith
  have t1 : Real.arctan (159 / ζ) ≤ Real.arctan (53 / 20) := by
    apply Real.arctan_strictMono.monotone
    rw [div_le_iff₀ hζ]
    linarith
  have t2 : Real.arctan (1 / ζ) ≤ Real.arctan (1 / 60) :=
    Real.arctan_strictMono.monotone (div_le_div_of_nonneg_left (by norm_num) (by norm_num) h60)
  have t3 : 0 ≤ ∑ j ∈ Icc 1 23,
      (Real.arctan ((159 - (etaW j : ℝ)) / ζ) - Real.arctan (((etaW j : ℝ) - 1) / ζ)) := by
    apply Finset.sum_nonneg
    intro j hj
    obtain ⟨he1, he2⟩ := etaW_mem hj
    have : Real.arctan (((etaW j : ℝ) - 1) / ζ) ≤ Real.arctan ((159 - (etaW j : ℝ)) / ζ) :=
      Real.arctan_strictMono.monotone (div_le_div_of_nonneg_right (by linarith) hζ.le)
    linarith
  have hc := tail_le
  unfold dUw
  linarith

/-- `U ≤ -749` on `(0, 46]` (tangent at `p = 9`). -/
theorem Uw_le_46 {η : ℝ} (hη : 0 < η) (hη46 : η ≤ 46) : Uw η ≤ -749 := by
  have h := Uw_tangent (p := 9) (by norm_num) (by norm_num) hη hη46
  have h1 := Uw9_le
  have h2 := dUw9_le
  have h3 := dUw9_ge
  have h4 : dUw 9 * (η - 9) ≤ dUw 9 * 37 :=
    mul_le_mul_of_nonneg_left (by linarith) (by linarith)
  nlinarith

/-- `U` decreases on `[46, 60]`. -/
theorem Uw_le_cell {η : ℝ} (h46 : 46 ≤ η) (h60 : η ≤ 60) : Uw η ≤ Uw 46 := by
  rcases eq_or_lt_of_le h46 with h | h
  · subst h; rfl
  · obtain ⟨ξ, hξ, hξeq⟩ := exists_hasDerivAt_eq_slope Uw dUw h
      (fun x hx => (Uw_hasDerivAt (by linarith [hx.1])).continuousAt.continuousWithinAt)
      (fun x hx => Uw_hasDerivAt (by linarith [hx.1]))
    have hd := dUw_cell hξ.1.le (by linarith [hξ.2])
    rw [hξeq, div_le_iff₀ (by linarith)] at hd
    nlinarith

/-- `U(η) ≤ U(60) - (η - 60)/10` for `η ≥ 60`. -/
theorem Uw_le_tail' {η : ℝ} (h60 : 60 ≤ η) : Uw η ≤ Uw 60 - (η - 60) / 10 := by
  rcases eq_or_lt_of_le h60 with h | h
  · subst h; simp
  · obtain ⟨ξ, hξ, hξeq⟩ := exists_hasDerivAt_eq_slope Uw dUw h
      (fun x hx => (Uw_hasDerivAt (by linarith [hx.1])).continuousAt.continuousWithinAt)
      (fun x hx => Uw_hasDerivAt (by linarith [hx.1]))
    have hd := dUw_tail hξ.1.le
    rw [hξeq, div_le_iff₀ (by linarith)] at hd
    nlinarith

/-- **Lemma 5** (landscape): `U(η) ≤ -749` for every `η > 0`. -/
theorem Uw_le : ∀ η : ℝ, 0 < η → Uw η ≤ -749 := by
  intro η hη
  have h46 := Uw_le_46 (η := 46) (by norm_num) le_rfl
  rcases le_or_gt η 46 with h | h
  · exact Uw_le_46 hη h
  · rcases le_or_gt η 60 with h' | h'
    · exact le_trans (Uw_le_cell h.le h') h46
    · have h60 := le_trans (Uw_le_cell (η := 60) (by norm_num) le_rfl) h46
      have := Uw_le_tail' h'.le
      linarith

/-- **Lemma 5** (tail): `U(η) ≤ -749 - (η - 60)/10` for `η ≥ 60`. -/
theorem Uw_le_tail : ∀ η : ℝ, 60 ≤ η → Uw η ≤ -749 - (η - 60) / 10 := by
  intro η hη
  have h46 := Uw_le_46 (η := 46) (by norm_num) le_rfl
  have h60 := le_trans (Uw_le_cell (η := 60) (by norm_num) le_rfl) h46
  have := Uw_le_tail' hη
  linarith

end L20U

end ZetaWindow

end
