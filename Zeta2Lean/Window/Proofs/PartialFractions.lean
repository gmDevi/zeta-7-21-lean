import Zeta2Lean.Window.Statements

set_option linter.style.header false
set_option linter.style.longLine false

/-!
# Partial fractions of `R̃` (JTNB (8.2), (8.7), p. 281; docs/window/proof.md §1)

**Theorem.** `Stmt_PF` (no hypotheses): for admissible `c`, `n ≥ 1` and every `y : ℚ` that is not
a pole (`y + k ≠ 0` for `k ∈ Krange c n`),
`Rser c n y = ∑_{j=r+1}^{q} ∑_{k ∈ Krange} C (B c n j k) * ((C (y + k) + X) ^ (j - r))⁻¹`
in `PowerSeries ℚ`.

**Proof (uniform denominator).**  Write `K = Krange c n = [h₁, h₀-h₁]`, `I_j = [h_j, h₀-h_j]`
(`I_j ⊆ K` by `eta_mono`), and multiply `R̃` by `W(t) = ∏_{k ∈ K} (t+k)^{q-r}` (not by the exact
denominator, so no pole orders have to be computed).
1. *The polynomial `P = R̃ · W`* (`Ppoly`).  For `j ≤ r`,
   `(t+1)_{h₀-1} = (t+1)_{h_j-1} · ∏_{i ∈ I_j} (t+i) · (t+h₀-h_j+1)_{h_j-1}`, and for `j > r`,
   `∏_{k ∈ K} (t+k) = ∏_{i ∈ I_j} (t+i) · ∏_{i ∈ K \ I_j} (t+i)`; since `q - r` factors of `W` are
   used, one per `j > r`,
   `P(t) = N_h (2t+h₀) ∏_{j≤r} (t+1)_{h_j-1} (t+h₀-h_j+1)_{h_j-1} ∏_{j>r} ∏_{i ∈ K \ I_j} (t+i)`.
   In series form this is `Rser_eq_subst`: `Rser c n y = P(y+ε) · W(y+ε)⁻¹` (cross-multiplication of
   two fractions with unit denominators).
2. *The partial-fraction side* `PF = ∑_{j,k} B_{j,k} (t+k)^{q-j} ∏_{k' ∈ K, k' ≠ k} (t+k')^{q-r}`
   (`PFpoly`), i.e. `W · ∑ B_{j,k} (t+k)^{-(j-r)}`.
3. *Local identity at a pole* (`subst_Ppoly`).  For `k₀ ∈ K`, with
   `V(ε) = ∏_{k' ∈ K, k' ≠ k₀} (k'-k₀+ε)^{q-r}`:  `P(-k₀+ε) = G_{k₀}(ε) · V(ε)` **exactly** in
   `ℚ⟦ε⟧`.  The polynomial bricks of `Gk` are the factors `(t+1)_{h_j-1}`, `(t+h₀-h_j+1)_{h_j-1}`
   up to `1/(h_j-1)!`; the key point is the rational brick (`ratBrick_mul_prod`):
   `ratBrick h_j (h₀-h_j+1) k₀ · ∏_{k' ∈ K, k' ≠ k₀} (k'-k₀+ε) = (h₀-2h_j)! ∏_{i ∈ K \ I_j} (i-k₀+ε)`
   in both branches of `ratBrick` (`k₀ ∈ I_j`: the inverse cancels `∏_{I_j \ {k₀}}`; `k₀ ∉ I_j`: the
   factor `ε` of the brick is the missing factor `i = k₀` of `∏_{K \ I_j}`).  The factorials
   recombine to `N_h`.
4. *Divisibility* (`dvd_subst`, `X_add_C_pow_dvd`).  `PF(-k₀+ε) = T(ε) V(ε) + E(ε)` with
   `T = ∑_j B_{j,k₀} ε^{q-j}` the truncation of `G_{k₀}` below `ε^{q-r}` (definition of `B`) and
   `ε^{q-r} ∣ E`.  So `ε^{q-r} ∣ (P - PF)(-k₀+ε)`, i.e. `(t+k₀)^{q-r} ∣ P - PF`.
5. *Degrees* (`natDegree_Ppoly_lt`, `natDegree_PFpoly_lt`).  Both have degree `< (q-r)·#K = deg W`:
   for `PF` since `j ≥ r+1`; for `P` because
   `deg P ≤ 1 + 2n∑_{j≤r}η_j + ∑_{j>r} (#K - #I_j) < (q-r)#K` reduces to
   `1 + 2n∑_{j=1}^{q} η_j < (q-r)(η₀ n + 1)`, which follows from (8.1) = `Admissible.deg_cond`
   (`2∑η_j + 2r ≤ (q-r)η₀`) with a margin of at least `2rn + q - r - 1`.  (Equivalently
   `deg R̃ = 1 + r - q - (q-r)η₀ n + 2n∑η_j ≤ 1 + r - q - 2rn`; for `cfgW`, `deg R̃ = -336n - 17`.)
6. The `(t+k)^{q-r}` (`k ∈ K`) are pairwise coprime, so `W ∣ P - PF`, and `deg (P - PF) < deg W`
   gives `P = PF` (`poly_eq`).  Evaluating at `t = y + ε` and multiplying by `W(y+ε)⁻¹` gives the
   series form (`series_eq`), each term being
   `(y+k+ε)^{q-j} ∏_{k'≠k} (y+k'+ε)^{q-r} · W(y+ε)⁻¹ = ((y+k+ε)^{j-r})⁻¹`.

Uses of admissibility: `eta_mono` (`h₁ ≤ h_j`, so `I_j ⊆ K`), `two_eta_lt` (`2h_j < h₀`, so all
`ℕ`-subtractions are exact and `K ≠ ∅`), `deg_cond` (step 5), `r + 4 ≤ q` and `3 ≤ r` (index
ranges and the margin).  `Odd r`, `Odd q` are not used (they enter only `Stmt_CoeffVanish`).

**Numerical check.** `python/window_mirror.py`, section "Laurent data … PF": exact equality of the first
four coefficients at random rational `y` for `cfgW` (`n = 1, 2`) and Zudilin's Theorem 3
configuration (`n = 1, 2, 3`); audit: 36 non-pole points in 4 configurations.

**Status: done** (complete and kernel-checked; axioms `propext`, `Classical.choice`, `Quot.sound`).
-/

open Filter Topology Finset PowerSeries

noncomputable section

namespace ZetaWindow

namespace PartialFractions

/-! ### Consequences of admissibility -/

theorem h_ge_one (c : Config) (n j : ℕ) : 1 ≤ c.h n j := by
  unfold Config.h; omega

theorem h1_le_h {c : Config} (hc : Admissible c) (n : ℕ) {j : ℕ} (hj1 : 1 ≤ j) (hjq : j ≤ c.q) :
    c.h n 1 ≤ c.h n j := by
  unfold Config.h
  have := Nat.mul_le_mul_right n (hc.eta_mono 1 j le_rfl hj1 hjq)
  omega

theorem two_h_lt {c : Config} (hc : Admissible c) {n : ℕ} (hn : 1 ≤ n) {j : ℕ} (hj1 : 1 ≤ j)
    (hjq : j ≤ c.q) : 2 * c.h n j < c.h0 n := by
  have h1 := hc.eta_mono j c.q hj1 hjq le_rfl
  have h2 := hc.two_eta_lt
  have h3 : 2 * c.eta j < c.eta0 := by omega
  unfold Config.h Config.h0
  nlinarith

/-- `I_j = [h_j, h₀-h_j] ⊆ K` (the index set of the `j`-th rational brick, as an `Ico`). -/
theorem Iset_subset {c : Config} (hc : Admissible c) (n : ℕ) {j : ℕ} (hj1 : 1 ≤ j)
    (hjq : j ≤ c.q) : Ico (c.h n j) (c.h0 n - c.h n j + 1) ⊆ Krange c n := by
  intro i hi
  have h1 := h1_le_h hc n hj1 hjq
  simp only [Krange, Finset.mem_Ico, Finset.mem_Icc] at hi ⊢
  omega

/-- `I_j = [h_j, h₀-h_j] ⊆ K` (as an `Icc`). -/
theorem Icc_subset_Krange {c : Config} (hc : Admissible c) (n : ℕ) {j : ℕ} (hj1 : 1 ≤ j)
    (hjq : j ≤ c.q) : Icc (c.h n j) (c.h0 n - c.h n j) ⊆ Krange c n := by
  intro i hi
  have h1 := h1_le_h hc n hj1 hjq
  simp only [Krange, Finset.mem_Icc] at hi ⊢
  omega

theorem one_le_card_Krange {c : Config} (hc : Admissible c) {n : ℕ} (hn : 1 ≤ n) :
    1 ≤ (Krange c n).card := by
  have h2 := two_h_lt hc hn (j := 1) le_rfl
    (by have := hc.r_add_four_le_q; have := hc.three_le_r; omega)
  unfold Krange
  rw [Nat.card_Icc]
  omega

/-! ### Splitting products over index ranges -/

theorem prod_Ico_split (f : ℕ → PowerSeries ℚ) {a b d : ℕ} (h1 : 1 ≤ a) (h2 : a ≤ b + 1)
    (h3 : b + 1 ≤ d) :
    ∏ i ∈ Ico 1 d, f i = (∏ i ∈ Ico 1 a, f i) * (∏ i ∈ Icc a b, f i) * ∏ i ∈ Ico (b + 1) d, f i := by
  rw [← Finset.Ico_add_one_right_eq_Icc, mul_assoc, Finset.prod_Ico_consecutive _ h2 h3,
    Finset.prod_Ico_consecutive _ h1 (h2.trans h3)]

theorem prod_Icc_one_split (f : ℕ → PowerSeries ℚ) {r q : ℕ} (h : r ≤ q) :
    ∏ j ∈ Icc 1 q, f j = (∏ j ∈ Icc 1 r, f j) * ∏ j ∈ Icc (r + 1) q, f j := by
  rw [← Finset.Ico_add_one_right_eq_Icc 1 q, ← Finset.Ico_add_one_right_eq_Icc 1 r,
    ← Finset.Ico_add_one_right_eq_Icc (r + 1) q]
  exact (Finset.prod_Ico_consecutive f (by omega) (by omega)).symm

theorem prod_K_split {c : Config} (hc : Admissible c) (n : ℕ) {j : ℕ} (hj1 : 1 ≤ j)
    (hjq : j ≤ c.q) (f : ℕ → PowerSeries ℚ) :
    ∏ k ∈ Krange c n, f k = (∏ i ∈ Icc (c.h n j) (c.h0 n - c.h n j), f i) *
      ∏ i ∈ Krange c n \ Ico (c.h n j) (c.h0 n - c.h n j + 1), f i := by
  have e : ∏ i ∈ Icc (c.h n j) (c.h0 n - c.h n j), f i =
      ∏ i ∈ Ico (c.h n j) (c.h0 n - c.h n j + 1), f i := by
    rw [Finset.Ico_add_one_right_eq_Icc]
  rw [e, mul_comm]
  exact (Finset.prod_sdiff (Iset_subset hc n hj1 hjq)).symm

/-! ### Polynomials -/

/-- `∏_{i ∈ s} (t + i)` in `ℚ[t]`. -/
def prodLin (s : Finset ℕ) : Polynomial ℚ :=
  ∏ i ∈ s, (Polynomial.X + Polynomial.C (i : ℚ))

theorem prodLin_monic (s : Finset ℕ) : (prodLin s).Monic :=
  Polynomial.monic_prod_of_monic _ _ (fun _ _ => Polynomial.monic_X_add_C _)

theorem natDegree_prodLin (s : Finset ℕ) : (prodLin s).natDegree = s.card := by
  unfold prodLin
  rw [Polynomial.natDegree_prod_of_monic _ _ (fun _ _ => Polynomial.monic_X_add_C _),
    Finset.sum_congr rfl (fun (i : ℕ) _ => Polynomial.natDegree_X_add_C ((i : ℕ) : ℚ)),
    Finset.sum_const,
    smul_eq_mul, mul_one]

/-- `P(t) = R̃(t) · ∏_{k ∈ K} (t+k)^{q-r}` in reduced brick form:
`N_h (2t + h₀) ∏_{j ≤ r} (t+1)_{h_j-1} (t+h₀-h_j+1)_{h_j-1} ∏_{j > r} ∏_{i ∈ K \ I_j} (t + i)`. -/
def Ppoly (c : Config) (n : ℕ) : Polynomial ℚ :=
  Polynomial.C (Nh c n) * (Polynomial.C 2 * Polynomial.X + Polynomial.C (c.h0 n : ℚ)) *
    (∏ j ∈ Icc 1 c.r,
      (prodLin (Ico 1 (c.h n j)) * prodLin (Ico (c.h0 n - c.h n j + 1) (c.h0 n)))) *
    ∏ j ∈ Icc (c.r + 1) c.q, prodLin (Krange c n \ Ico (c.h n j) (c.h0 n - c.h n j + 1))

/-- The partial-fraction side times `∏_{k ∈ K} (t+k)^{q-r}`:
`∑_{j,k} B_{j,k} (t+k)^{q-j} ∏_{k' ∈ K, k' ≠ k} (t+k')^{q-r}`. -/
def PFpoly (c : Config) (n : ℕ) : Polynomial ℚ :=
  ∑ j ∈ Icc (c.r + 1) c.q, ∑ k ∈ Krange c n,
    Polynomial.C (B c n j k) * (Polynomial.X + Polynomial.C (k : ℚ)) ^ (c.q - j) *
      ∏ k' ∈ (Krange c n).erase k, (Polynomial.X + Polynomial.C (k' : ℚ)) ^ (c.q - c.r)

/-! ### The substitution `t ↦ a + ε` -/

/-- The substitution `t ↦ a + ε`, as a ring hom `ℚ[t] →+* ℚ⟦ε⟧`. -/
def subst (a : ℚ) : Polynomial ℚ →+* PowerSeries ℚ :=
  Polynomial.eval₂RingHom (C : ℚ →+* PowerSeries ℚ) (C a + X)

theorem subst_X (a : ℚ) : subst a Polynomial.X = C a + X := by
  simp [subst]

theorem subst_C (a b : ℚ) : subst a (Polynomial.C b) = C b := by
  simp [subst]

theorem subst_X_add_C (a b : ℚ) :
    subst a (Polynomial.X + Polynomial.C b) = C (a + b) + X := by
  rw [map_add, subst_X, subst_C, map_add]
  ring

theorem subst_neg_X_add_C (k : ℕ) (b : ℚ) :
    subst (-(k : ℚ)) (Polynomial.X + Polynomial.C b) = C (b - k) + X := by
  rw [subst_X_add_C, neg_add_eq_sub]

theorem subst_lin (a h : ℚ) :
    subst a (Polynomial.C 2 * Polynomial.X + Polynomial.C h) = C 2 * (C a + X) + C h := by
  rw [map_add, map_mul, subst_C, subst_X, subst_C]

theorem subst_prodLin (a : ℚ) (s : Finset ℕ) :
    subst a (prodLin s) = ∏ i ∈ s, (C (a + i) + X) := by
  unfold prodLin
  rw [map_prod]
  exact Finset.prod_congr rfl (fun i _ => subst_X_add_C a i)

theorem subst_neg_prodLin (k : ℕ) (s : Finset ℕ) :
    subst (-(k : ℚ)) (prodLin s) = ∏ i ∈ s, (C ((i : ℚ) - k) + X) := by
  unfold prodLin
  rw [map_prod]
  exact Finset.prod_congr rfl (fun i _ => subst_neg_X_add_C k i)

/-- `subst (-k₀) P` is the power series of the polynomial `P(t - k₀)`. -/
theorem coe_comp_eq_subst (k₀ : ℚ) (P : Polynomial ℚ) :
    ((P.comp (Polynomial.X - Polynomial.C k₀) : Polynomial ℚ) : PowerSeries ℚ) =
      subst (-k₀) P := by
  have h : (Polynomial.coeToPowerSeries.ringHom).comp
      (Polynomial.compRingHom (Polynomial.X - Polynomial.C k₀)) = subst (-k₀) := by
    apply Polynomial.ringHom_ext
    · intro a
      simp [subst]
    · simp only [RingHom.comp_apply, Polynomial.coe_compRingHom_apply, Polynomial.X_comp,
        Polynomial.coeToPowerSeries.ringHom_apply, subst_X]
      rw [Polynomial.coe_sub, Polynomial.coe_X, Polynomial.coe_C, map_neg]
      ring
  exact RingHom.congr_fun h P

/-! ### Rational bricks against the uniform denominator -/

theorem constantCoeff_lin (i k : ℕ) (h : i ≠ k) :
    constantCoeff (C ((i : ℚ) - k) + X : PowerSeries ℚ) ≠ 0 := by
  rw [map_add, constantCoeff_C, constantCoeff_X, add_zero, sub_ne_zero]
  exact_mod_cast h

/-- **Key brick identity.**  For `Ico a b ⊆ K` and `k ∈ K`:
`ratBrick a b k · ∏_{k' ∈ K, k' ≠ k} (k'-k+ε) = (b-a-1)! ∏_{i ∈ K \ [a,b)} (i-k+ε)`. -/
theorem ratBrick_mul_prod (a b k : ℕ) (K : Finset ℕ) (hsub : Ico a b ⊆ K) (hk : k ∈ K) :
    ratBrick a b k * ∏ k' ∈ K.erase k, (C ((k' : ℚ) - k) + X) =
      C ((b - a - 1).factorial : ℚ) * ∏ i ∈ K \ Ico a b, (C ((i : ℚ) - k) + X) := by
  unfold ratBrick
  split_ifs with h
  · have hkI : k ∈ Ico a b := Finset.mem_Ico.2 h
    have hsplit : K.erase k = (Ico a b).erase k ∪ (K \ Ico a b) := by
      ext x
      simp only [Finset.mem_erase, Finset.mem_union, Finset.mem_sdiff]
      constructor
      · rintro ⟨hxk, hxK⟩
        by_cases hx : x ∈ Ico a b
        · exact Or.inl ⟨hxk, hx⟩
        · exact Or.inr ⟨hxK, hx⟩
      · rintro (⟨hxk, hx⟩ | ⟨hxK, hx⟩)
        · exact ⟨hxk, hsub hx⟩
        · exact ⟨fun h' => hx (h' ▸ hkI), hxK⟩
    have hdisj : Disjoint ((Ico a b).erase k) (K \ Ico a b) := by
      rw [Finset.disjoint_left]
      intro x hx1 hx2
      exact (Finset.mem_sdiff.1 hx2).2 (Finset.mem_of_mem_erase hx1)
    have hne : constantCoeff (∏ i ∈ (Ico a b).erase k, (C ((i : ℚ) - k) + X)) ≠ 0 := by
      rw [map_prod, Finset.prod_ne_zero_iff]
      intro i hi
      exact constantCoeff_lin i k (Finset.ne_of_mem_erase hi)
    have key := PowerSeries.inv_mul_cancel _ hne
    rw [hsplit, Finset.prod_union hdisj]
    linear_combination
      (C ((b - a - 1).factorial : ℚ) * ∏ i ∈ K \ Ico a b, (C ((i : ℚ) - k) + X)) * key
  · have hkI : k ∉ Ico a b := fun h' => h (Finset.mem_Ico.1 h')
    have hsub' : Ico a b ⊆ K.erase k := fun x hx =>
      Finset.mem_erase.2 ⟨fun h' => hkI (h' ▸ hx), hsub hx⟩
    have hkS : k ∈ K \ Ico a b := Finset.mem_sdiff.2 ⟨hk, hkI⟩
    have herase : (K \ Ico a b).erase k = K.erase k \ Ico a b := by
      ext x
      simp only [Finset.mem_erase, Finset.mem_sdiff]
      tauto
    have hne : constantCoeff (∏ i ∈ Ico a b, (C ((i : ℚ) - k) + X)) ≠ 0 := by
      rw [map_prod, Finset.prod_ne_zero_iff]
      intro i hi
      exact constantCoeff_lin i k (fun h' => hkI (h' ▸ hi))
    have key := PowerSeries.inv_mul_cancel _ hne
    have hXk : (C ((k : ℚ) - k) + X : PowerSeries ℚ) = X := by
      rw [sub_self, map_zero, zero_add]
    rw [← Finset.prod_sdiff hsub', ← Finset.mul_prod_erase _ _ hkS, hXk, herase]
    linear_combination
      (C ((b - a - 1).factorial : ℚ) * X * ∏ i ∈ K.erase k \ Ico a b, (C ((i : ℚ) - k) + X)) * key

/-! ### The local identity at a pole: `P(-k₀+ε) = G_{k₀}(ε) V(ε)` -/

theorem subst_Ppoly {c : Config} (hc : Admissible c) {n : ℕ} (hn : 1 ≤ n) {k₀ : ℕ}
    (hk : k₀ ∈ Krange c n) :
    subst (-(k₀ : ℚ)) (Ppoly c n) =
      Gk c n k₀ * ∏ k' ∈ (Krange c n).erase k₀, (C ((k' : ℚ) - k₀) + X) ^ (c.q - c.r) := by
  have hrq := hc.r_add_four_le_q
  -- `V = ∏_{j > r} U`
  have hV : ∏ k' ∈ (Krange c n).erase k₀, (C ((k' : ℚ) - k₀) + X) ^ (c.q - c.r) =
      ∏ _j ∈ Icc (c.r + 1) c.q, ∏ k' ∈ (Krange c n).erase k₀, (C ((k' : ℚ) - k₀) + X) := by
    rw [Finset.prod_pow, Finset.prod_const, Nat.card_Icc]
    congr 1
    omega
  -- the rational bricks
  have hrat : ∀ j ∈ Icc (c.r + 1) c.q,
      ratBrick (c.h n j) (c.h0 n - c.h n j + 1) k₀ *
          ∏ k' ∈ (Krange c n).erase k₀, (C ((k' : ℚ) - k₀) + X) =
        C ((c.h0 n - 2 * c.h n j).factorial : ℚ) *
          ∏ i ∈ Krange c n \ Ico (c.h n j) (c.h0 n - c.h n j + 1), (C ((i : ℚ) - k₀) + X) := by
    intro j hj
    rw [Finset.mem_Icc] at hj
    rw [ratBrick_mul_prod _ _ _ _ (Iset_subset hc n (by omega) hj.2) hk]
    have he : c.h0 n - c.h n j + 1 - c.h n j - 1 = c.h0 n - 2 * c.h n j := by omega
    rw [he]
  -- the polynomial bricks
  have hpoly : ∀ j ∈ Icc 1 c.r,
      polyBrick (c.h n j) 1 k₀ * polyBrick (c.h0 n) (c.h0 n - c.h n j + 1) k₀ =
        C ((1 / ((c.h n j - 1).factorial : ℚ)) ^ 2) *
          ((∏ i ∈ Ico 1 (c.h n j), (C ((i : ℚ) - k₀) + X)) *
            ∏ i ∈ Ico (c.h0 n - c.h n j + 1) (c.h0 n), (C ((i : ℚ) - k₀) + X)) := by
    intro j hj
    rw [Finset.mem_Icc] at hj
    have h2 := two_h_lt hc hn (j := j) hj.1 (by omega)
    have he : c.h0 n - (c.h0 n - c.h n j + 1) = c.h n j - 1 := by omega
    unfold polyBrick
    rw [he, map_pow]
    ring
  -- `N_h = ∏_{j>r} (h₀-2h_j)! · ∏_{j≤r} (1/(h_j-1)!)²`
  have hNh : Nh c n = (∏ j ∈ Icc (c.r + 1) c.q, ((c.h0 n - 2 * c.h n j).factorial : ℚ)) *
      ∏ j ∈ Icc 1 c.r, (1 / ((c.h n j - 1).factorial : ℚ)) ^ 2 := by
    unfold Nh
    rw [div_eq_mul_inv, ← Finset.prod_inv_distrib]
    congr 1
    refine Finset.prod_congr rfl (fun j _ => ?_)
    rw [one_div, inv_pow]
  have hL : subst (-(k₀ : ℚ)) (Polynomial.C 2 * Polynomial.X + Polynomial.C (c.h0 n : ℚ)) =
      C ((c.h0 n : ℚ) - 2 * k₀) + C 2 * X := by
    rw [subst_lin]
    simp only [map_sub, map_mul, map_neg]
    ring
  have hP : subst (-(k₀ : ℚ)) (Ppoly c n) =
      C (Nh c n) * (C ((c.h0 n : ℚ) - 2 * k₀) + C 2 * X) *
        (∏ j ∈ Icc 1 c.r, ((∏ i ∈ Ico 1 (c.h n j), (C ((i : ℚ) - k₀) + X)) *
          ∏ i ∈ Ico (c.h0 n - c.h n j + 1) (c.h0 n), (C ((i : ℚ) - k₀) + X))) *
        ∏ j ∈ Icc (c.r + 1) c.q,
          ∏ i ∈ Krange c n \ Ico (c.h n j) (c.h0 n - c.h n j + 1), (C ((i : ℚ) - k₀) + X) := by
    unfold Ppoly
    rw [map_mul, map_mul, map_mul, subst_C, hL, map_prod, map_prod]
    simp only [map_mul, subst_neg_prodLin]
  have hG : Gk c n k₀ * ∏ _j ∈ Icc (c.r + 1) c.q,
        ∏ k' ∈ (Krange c n).erase k₀, (C ((k' : ℚ) - k₀) + X) =
      (C ((c.h0 n : ℚ) - 2 * k₀) + C 2 * X) *
        (∏ j ∈ Icc 1 c.r,
          (polyBrick (c.h n j) 1 k₀ * polyBrick (c.h0 n) (c.h0 n - c.h n j + 1) k₀)) *
        ∏ j ∈ Icc (c.r + 1) c.q, (ratBrick (c.h n j) (c.h0 n - c.h n j + 1) k₀ *
          ∏ k' ∈ (Krange c n).erase k₀, (C ((k' : ℚ) - k₀) + X)) := by
    unfold Gk
    simp only [Finset.prod_mul_distrib]
    ring
  rw [hP, hV, hG, Finset.prod_congr rfl hpoly, Finset.prod_congr rfl hrat, hNh]
  simp only [map_mul, map_prod, Finset.prod_mul_distrib]
  ring

/-! ### Divisibility at each pole -/

/-- `ε^{q-r} ∣ (P - PF)(-k₀ + ε)`. -/
theorem dvd_subst {c : Config} (hc : Admissible c) {n : ℕ} (hn : 1 ≤ n) {k₀ : ℕ}
    (hk : k₀ ∈ Krange c n) :
    (X : PowerSeries ℚ) ^ (c.q - c.r) ∣ subst (-(k₀ : ℚ)) (Ppoly c n - PFpoly c n) := by
  have hrq := hc.r_add_four_le_q
  have hX : (C ((k₀ : ℚ) - k₀) + X : PowerSeries ℚ) = X := by
    rw [sub_self, map_zero, zero_add]
  set V : PowerSeries ℚ :=
    ∏ k' ∈ (Krange c n).erase k₀, (C ((k' : ℚ) - k₀) + X) ^ (c.q - c.r) with hV
  set T : PowerSeries ℚ := ∑ j ∈ Icc (c.r + 1) c.q, C (B c n j k₀) * X ^ (c.q - j) with hT
  set E : PowerSeries ℚ := ∑ j ∈ Icc (c.r + 1) c.q, ∑ k ∈ (Krange c n).erase k₀,
      C (B c n j k) * (C ((k : ℚ) - k₀) + X) ^ (c.q - j) *
        ∏ k' ∈ (Krange c n).erase k, (C ((k' : ℚ) - k₀) + X) ^ (c.q - c.r) with hE
  have hR : subst (-(k₀ : ℚ)) (Ppoly c n) = Gk c n k₀ * V := subst_Ppoly hc hn hk
  have hPF : subst (-(k₀ : ℚ)) (PFpoly c n) = T * V + E := by
    unfold PFpoly
    simp only [map_sum, map_mul, map_pow, map_prod, subst_C, subst_neg_X_add_C]
    rw [hT, hE, Finset.sum_mul, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl (fun j _ => ?_)
    rw [← Finset.add_sum_erase _ _ hk, hX]
  -- `T` is the truncation of `G_{k₀}` below `ε^{q-r}` (definition of `B`)
  have hTdvd : (X : PowerSeries ℚ) ^ (c.q - c.r) ∣ Gk c n k₀ - T := by
    rw [PowerSeries.X_pow_dvd_iff]
    intro m hm
    rw [map_sub, hT, map_sum]
    simp only [PowerSeries.coeff_C_mul_X_pow]
    rw [Finset.sum_eq_single (c.q - m)]
    · rw [ite_eq_left (by omega)]
      unfold B
      rw [Nat.sub_sub_self (by omega), sub_self]
    · intro j hj _
      rw [Finset.mem_Icc] at hj
      rw [ite_eq_right (by omega)]
    · intro h
      exfalso
      apply h
      rw [Finset.mem_Icc]
      omega
  have hEdvd : (X : PowerSeries ℚ) ^ (c.q - c.r) ∣ E := by
    rw [hE]
    apply Finset.dvd_sum
    intro j _
    apply Finset.dvd_sum
    intro k hk'
    have hk0 : k₀ ∈ (Krange c n).erase k :=
      Finset.mem_erase.2 ⟨(Finset.ne_of_mem_erase hk').symm, hk⟩
    apply Dvd.dvd.mul_left
    have := Finset.dvd_prod_of_mem
      (fun k' : ℕ => (C ((k' : ℚ) - k₀) + X : PowerSeries ℚ) ^ (c.q - c.r)) hk0
    simp only [hX] at this
    exact this
  rw [map_sub, hR, hPF]
  have : Gk c n k₀ * V - (T * V + E) = (Gk c n k₀ - T) * V - E := by ring
  rw [this]
  exact dvd_sub (dvd_mul_of_dvd_left hTdvd V) hEdvd

/-- `(t + k₀)^{q-r} ∣ P - PF` for every `k₀ ∈ K`. -/
theorem X_add_C_pow_dvd {c : Config} (hc : Admissible c) {n : ℕ} (hn : 1 ≤ n) {k₀ : ℕ}
    (hk : k₀ ∈ Krange c n) :
    (Polynomial.X + Polynomial.C (k₀ : ℚ)) ^ (c.q - c.r) ∣ Ppoly c n - PFpoly c n := by
  set P := Ppoly c n - PFpoly c n with hP
  set Q := P.comp (Polynomial.X - Polynomial.C (k₀ : ℚ)) with hQ
  have hQdvd : Polynomial.X ^ (c.q - c.r) ∣ Q := by
    rw [Polynomial.X_pow_dvd_iff]
    intro d hd
    have h1 := dvd_subst hc hn hk
    rw [← hP, ← coe_comp_eq_subst, ← hQ, PowerSeries.X_pow_dvd_iff] at h1
    have h2 := h1 d hd
    rwa [Polynomial.coeff_coe] at h2
  obtain ⟨S, hS⟩ := hQdvd
  have hPQ : P = Q.comp (Polynomial.X + Polynomial.C (k₀ : ℚ)) := by
    rw [hQ, Polynomial.comp_assoc]
    simp
  refine ⟨S.comp (Polynomial.X + Polynomial.C (k₀ : ℚ)), ?_⟩
  rw [hPQ, hS, Polynomial.mul_comp, Polynomial.X_pow_comp]

/-! ### Degree bounds -/

theorem natDegree_PFpoly_lt {c : Config} (hc : Admissible c) {n : ℕ} (hn : 1 ≤ n) :
    (PFpoly c n).natDegree < (c.q - c.r) * (Krange c n).card := by
  have hrq := hc.r_add_four_le_q
  have hK := one_le_card_Krange hc hn
  have hle : (PFpoly c n).natDegree ≤
      (c.q - c.r) * ((Krange c n).card - 1) + (c.q - c.r - 1) := by
    unfold PFpoly
    apply Polynomial.natDegree_sum_le_of_forall_le
    intro j hj
    apply Polynomial.natDegree_sum_le_of_forall_le
    intro k hk
    rw [Finset.mem_Icc] at hj
    have hcard : ((Krange c n).erase k).card = (Krange c n).card - 1 :=
      Finset.card_erase_of_mem hk
    have h1 := Polynomial.natDegree_mul_le (p := Polynomial.C (B c n j k))
      (q := (Polynomial.X + Polynomial.C (k : ℚ)) ^ (c.q - j))
    rw [Polynomial.natDegree_C, zero_add] at h1
    have h2 : ((Polynomial.X + Polynomial.C (k : ℚ)) ^ (c.q - j)).natDegree = c.q - j := by
      rw [(Polynomial.monic_X_add_C _).natDegree_pow, Polynomial.natDegree_X_add_C, mul_one]
    have h3 : (∏ k' ∈ (Krange c n).erase k,
        (Polynomial.X + Polynomial.C (k' : ℚ)) ^ (c.q - c.r)).natDegree =
          (c.q - c.r) * ((Krange c n).card - 1) := by
      rw [Polynomial.natDegree_prod_of_monic _ _
        (fun k' _ => (Polynomial.monic_X_add_C _).pow _)]
      rw [Finset.sum_congr rfl (fun k' _ => by
        rw [(Polynomial.monic_X_add_C (k' : ℚ)).natDegree_pow, Polynomial.natDegree_X_add_C,
          mul_one])]
      rw [Finset.sum_const, smul_eq_mul, hcard, mul_comm]
    refine Polynomial.natDegree_mul_le.trans ?_
    rw [h3]
    omega
  have h4 : (c.q - c.r) * (Krange c n).card =
      (c.q - c.r) * ((Krange c n).card - 1) + (c.q - c.r) := by
    rw [← Nat.mul_succ]
    congr 1
    omega
  omega

theorem natDegree_Ppoly_lt {c : Config} (hc : Admissible c) {n : ℕ} (hn : 1 ≤ n) :
    (Ppoly c n).natDegree < (c.q - c.r) * (Krange c n).card := by
  have hrq := hc.r_add_four_le_q
  have hr3 := hc.three_le_r
  have hlin : (Polynomial.C (Nh c n) *
      (Polynomial.C 2 * Polynomial.X + Polynomial.C (c.h0 n : ℚ))).natDegree ≤ 1 := by
    refine Polynomial.natDegree_mul_le.trans ?_
    rw [Polynomial.natDegree_C, zero_add]
    exact Polynomial.natDegree_linear_le
  have hP1 : (∏ j ∈ Icc 1 c.r, (prodLin (Ico 1 (c.h n j)) *
      prodLin (Ico (c.h0 n - c.h n j + 1) (c.h0 n)))).natDegree =
        ∑ j ∈ Icc 1 c.r, 2 * (c.eta j * n) := by
    rw [Polynomial.natDegree_prod_of_monic _ _
      (fun j _ => (prodLin_monic _).mul (prodLin_monic _))]
    refine Finset.sum_congr rfl (fun j hj => ?_)
    rw [Finset.mem_Icc] at hj
    have h2 := two_h_lt hc hn (j := j) hj.1 (by omega)
    rw [(prodLin_monic _).natDegree_mul (prodLin_monic _), natDegree_prodLin, natDegree_prodLin,
      Nat.card_Ico, Nat.card_Ico]
    unfold Config.h Config.h0 at *
    omega
  have hP2 : (∏ j ∈ Icc (c.r + 1) c.q,
      prodLin (Krange c n \ Ico (c.h n j) (c.h0 n - c.h n j + 1))).natDegree =
        ∑ j ∈ Icc (c.r + 1) c.q,
          ((Krange c n).card - (Ico (c.h n j) (c.h0 n - c.h n j + 1)).card) := by
    rw [Polynomial.natDegree_prod_of_monic _ _ (fun j _ => prodLin_monic _)]
    refine Finset.sum_congr rfl (fun j hj => ?_)
    rw [Finset.mem_Icc] at hj
    rw [natDegree_prodLin, Finset.card_sdiff_of_subset (Iset_subset hc n (by omega) hj.2)]
  have hdeg : (Ppoly c n).natDegree ≤ 1 + ∑ j ∈ Icc 1 c.r, 2 * (c.eta j * n) +
      ∑ j ∈ Icc (c.r + 1) c.q,
        ((Krange c n).card - (Ico (c.h n j) (c.h0 n - c.h n j + 1)).card) := by
    unfold Ppoly
    refine Polynomial.natDegree_mul_le.trans ?_
    rw [hP2]
    refine Nat.add_le_add_right (Polynomial.natDegree_mul_le.trans ?_) _
    rw [hP1]
    exact Nat.add_le_add_right hlin _
  -- `∑_{j>r} (#K - #I_j) + ∑_{j>r} #I_j = (q-r) #K`
  have hX2 : ∑ j ∈ Icc (c.r + 1) c.q,
        ((Krange c n).card - (Ico (c.h n j) (c.h0 n - c.h n j + 1)).card) +
      ∑ j ∈ Icc (c.r + 1) c.q, (Ico (c.h n j) (c.h0 n - c.h n j + 1)).card =
        (c.q - c.r) * (Krange c n).card := by
    rw [← Finset.sum_add_distrib]
    have hterm : ∀ j ∈ Icc (c.r + 1) c.q,
        (Krange c n).card - (Ico (c.h n j) (c.h0 n - c.h n j + 1)).card +
          (Ico (c.h n j) (c.h0 n - c.h n j + 1)).card = (Krange c n).card := by
      intro j hj
      rw [Finset.mem_Icc] at hj
      have := Finset.card_le_card (Iset_subset hc n (j := j) (by omega) hj.2)
      omega
    rw [Finset.sum_congr rfl hterm, Finset.sum_const, Nat.card_Icc, smul_eq_mul]
    congr 1
    omega
  -- `∑_{j>r} #I_j + 2 n ∑_{j>r} η_j = (q-r)(η₀ n + 1)`
  have hI : ∑ j ∈ Icc (c.r + 1) c.q, (Ico (c.h n j) (c.h0 n - c.h n j + 1)).card +
      2 * ((∑ j ∈ Icc (c.r + 1) c.q, c.eta j) * n) = (c.q - c.r) * (c.eta0 * n + 1) := by
    rw [Finset.sum_mul, Finset.mul_sum, ← Finset.sum_add_distrib]
    have hterm : ∀ j ∈ Icc (c.r + 1) c.q,
        (Ico (c.h n j) (c.h0 n - c.h n j + 1)).card + 2 * (c.eta j * n) = c.eta0 * n + 1 := by
      intro j hj
      rw [Finset.mem_Icc] at hj
      have h2 := two_h_lt hc hn (j := j) (by omega) hj.2
      rw [Nat.card_Ico]
      unfold Config.h Config.h0 at *
      omega
    rw [Finset.sum_congr rfl hterm, Finset.sum_const, Nat.card_Icc, smul_eq_mul]
    congr 1
    omega
  have hX1 : ∑ j ∈ Icc 1 c.r, 2 * (c.eta j * n) = 2 * ((∑ j ∈ Icc 1 c.r, c.eta j) * n) := by
    rw [Finset.sum_mul, Finset.mul_sum]
  have hsplit : ∑ j ∈ Icc 1 c.q, c.eta j =
      ∑ j ∈ Icc 1 c.r, c.eta j + ∑ j ∈ Icc (c.r + 1) c.q, c.eta j := by
    rw [← Finset.Ico_add_one_right_eq_Icc 1 c.q, ← Finset.Ico_add_one_right_eq_Icc 1 c.r,
      ← Finset.Ico_add_one_right_eq_Icc (c.r + 1) c.q]
    exact (Finset.sum_Ico_consecutive _ (by omega) (by omega)).symm
  have hdc := hc.deg_cond
  rw [hsplit] at hdc
  rw [hX1] at hdeg
  have hdcn := Nat.mul_le_mul_right n hdc
  nlinarith [hX2, hI, hdeg, hdcn]

/-! ### The polynomial identity `P = PF` -/

theorem poly_eq {c : Config} (hc : Admissible c) {n : ℕ} (hn : 1 ≤ n) :
    Ppoly c n = PFpoly c n := by
  have hdvd : ∏ k ∈ Krange c n, (Polynomial.X + Polynomial.C (k : ℚ)) ^ (c.q - c.r) ∣
      Ppoly c n - PFpoly c n := by
    apply Finset.prod_dvd_of_coprime
    · intro i _ j _ hij
      have hinj : Function.Injective (fun k : ℕ => -(k : ℚ)) := by
        intro a b h
        simpa using h
      have := Polynomial.pairwise_coprime_X_sub_C hinj hij
      simp only [Function.onFun, map_neg, sub_neg_eq_add] at this ⊢
      exact this.pow
    · intro k hk
      exact X_add_C_pow_dvd hc hn hk
  have hdeg : (Ppoly c n - PFpoly c n).natDegree <
      (∏ k ∈ Krange c n, (Polynomial.X + Polynomial.C (k : ℚ)) ^ (c.q - c.r)).natDegree := by
    have hmon : ∀ k ∈ Krange c n,
        ((Polynomial.X + Polynomial.C (k : ℚ)) ^ (c.q - c.r)).Monic :=
      fun k _ => (Polynomial.monic_X_add_C _).pow _
    rw [Polynomial.natDegree_prod_of_monic _ _ hmon]
    have h4 : ∑ k ∈ Krange c n,
        ((Polynomial.X + Polynomial.C (k : ℚ)) ^ (c.q - c.r)).natDegree =
          (c.q - c.r) * (Krange c n).card := by
      rw [Finset.sum_congr rfl (fun k _ => by
        rw [(Polynomial.monic_X_add_C (k : ℚ)).natDegree_pow, Polynomial.natDegree_X_add_C,
          mul_one])]
      rw [Finset.sum_const, smul_eq_mul, mul_comm]
    rw [h4]
    have h1 := Polynomial.natDegree_sub_le (Ppoly c n) (PFpoly c n)
    have h2 := natDegree_Ppoly_lt hc hn
    have h3 := natDegree_PFpoly_lt hc hn
    omega
  exact sub_eq_zero.1 (Polynomial.eq_zero_of_dvd_of_natDegree_lt hdvd hdeg)

/-! ### The series form -/

theorem mul_inv_eq_mul_inv {A B A' W : PowerSeries ℚ} (hB : constantCoeff B ≠ 0)
    (hW : constantCoeff W ≠ 0) (h : A * W = A' * B) : A * B⁻¹ = A' * W⁻¹ := by
  have hB' := PowerSeries.mul_inv_cancel B hB
  have hW' := PowerSeries.mul_inv_cancel W hW
  calc A * B⁻¹ = A * B⁻¹ * (W * W⁻¹) := by rw [hW', mul_one]
    _ = (A * W) * B⁻¹ * W⁻¹ := by ring
    _ = (A' * B) * B⁻¹ * W⁻¹ := by rw [h]
    _ = A' * W⁻¹ * (B * B⁻¹) := by ring
    _ = A' * W⁻¹ := by rw [hB', mul_one]

/-- `Rser c n y = P(y+ε) · W(y+ε)⁻¹` with `W = ∏_{k ∈ K} (t+k)^{q-r}`. -/
theorem Rser_eq_subst {c : Config} (hc : Admissible c) {n : ℕ} (hn : 1 ≤ n) (y : ℚ)
    (hy : ∀ k ∈ Krange c n, y + k ≠ 0) :
    Rser c n y = subst y (Ppoly c n) *
      (∏ k ∈ Krange c n, (C (y + (k : ℚ)) + X) ^ (c.q - c.r))⁻¹ := by
  have hrq := hc.r_add_four_le_q
  have hr3 := hc.three_le_r
  have hf0 : ∀ i ∈ Krange c n, constantCoeff (C (y + (i : ℚ)) + X : PowerSeries ℚ) ≠ 0 := by
    intro i hi
    rw [map_add, constantCoeff_C, constantCoeff_X, add_zero]
    exact hy i hi
  have hB0 : constantCoeff (∏ j ∈ Icc 1 c.q,
      ∏ i ∈ Icc (c.h n j) (c.h0 n - c.h n j), (C (y + (i : ℚ)) + X) : PowerSeries ℚ) ≠ 0 := by
    rw [map_prod, Finset.prod_ne_zero_iff]
    intro j hj
    rw [Finset.mem_Icc] at hj
    rw [map_prod, Finset.prod_ne_zero_iff]
    intro i hi
    exact hf0 i (Icc_subset_Krange hc n hj.1 hj.2 hi)
  have hW0 : constantCoeff (∏ k ∈ Krange c n, (C (y + (k : ℚ)) + X) ^ (c.q - c.r) :
      PowerSeries ℚ) ≠ 0 := by
    rw [map_prod, Finset.prod_ne_zero_iff]
    intro k hk
    rw [map_pow]
    exact pow_ne_zero _ (hf0 k hk)
  -- `(t+1)_{h₀-1}^r = ∏_{j ≤ r} (t+1)_{h_j-1} (t+h₀-h_j+1)_{h_j-1} · ∏_{j ≤ r} ∏_{I_j} (t+i)`
  have hA : (∏ i ∈ Ico 1 (c.h0 n), (C (y + (i : ℚ)) + X)) ^ c.r =
      (∏ j ∈ Icc 1 c.r, ((∏ i ∈ Ico 1 (c.h n j), (C (y + (i : ℚ)) + X)) *
        ∏ i ∈ Ico (c.h0 n - c.h n j + 1) (c.h0 n), (C (y + (i : ℚ)) + X))) *
      ∏ j ∈ Icc 1 c.r, ∏ i ∈ Icc (c.h n j) (c.h0 n - c.h n j), (C (y + (i : ℚ)) + X) := by
    rw [← Finset.prod_mul_distrib]
    rw [show (∏ i ∈ Ico 1 (c.h0 n), (C (y + (i : ℚ)) + X)) ^ c.r =
        ∏ _j ∈ Icc 1 c.r, ∏ i ∈ Ico 1 (c.h0 n), (C (y + (i : ℚ)) + X) by
      rw [Finset.prod_const, Nat.card_Icc, Nat.add_sub_cancel]]
    refine Finset.prod_congr rfl (fun j hj => ?_)
    rw [Finset.mem_Icc] at hj
    have h2 := two_h_lt hc hn (j := j) hj.1 (by omega)
    have h1 := h_ge_one c n j
    rw [prod_Ico_split (fun i : ℕ => (C (y + (i : ℚ)) + X : PowerSeries ℚ))
      (b := c.h0 n - c.h n j) (d := c.h0 n) h1 (by omega) (by omega)]
    ring
  -- `∏_{j ≤ q} ∏_{I_j} = ∏_{j ≤ r} ∏_{I_j} · ∏_{j > r} ∏_{I_j}`
  have hB : ∏ j ∈ Icc 1 c.q, ∏ i ∈ Icc (c.h n j) (c.h0 n - c.h n j), (C (y + (i : ℚ)) + X) =
      (∏ j ∈ Icc 1 c.r, ∏ i ∈ Icc (c.h n j) (c.h0 n - c.h n j), (C (y + (i : ℚ)) + X)) *
        ∏ j ∈ Icc (c.r + 1) c.q, ∏ i ∈ Icc (c.h n j) (c.h0 n - c.h n j), (C (y + (i : ℚ)) + X) :=
    prod_Icc_one_split (fun j : ℕ => ∏ i ∈ Icc (c.h n j) (c.h0 n - c.h n j),
      (C (y + (i : ℚ)) + X : PowerSeries ℚ)) (by omega)
  -- `W = ∏_{j > r} (∏_{I_j} · ∏_{K \ I_j})`
  have hW : ∏ k ∈ Krange c n, (C (y + (k : ℚ)) + X) ^ (c.q - c.r) =
      ∏ j ∈ Icc (c.r + 1) c.q, ((∏ i ∈ Icc (c.h n j) (c.h0 n - c.h n j), (C (y + (i : ℚ)) + X)) *
        ∏ i ∈ Krange c n \ Ico (c.h n j) (c.h0 n - c.h n j + 1), (C (y + (i : ℚ)) + X)) := by
    rw [Finset.prod_pow]
    rw [show (∏ k ∈ Krange c n, (C (y + (k : ℚ)) + X)) ^ (c.q - c.r) =
        ∏ _j ∈ Icc (c.r + 1) c.q, ∏ k ∈ Krange c n, (C (y + (k : ℚ)) + X) by
      rw [Finset.prod_const, Nat.card_Icc]
      congr 1
      omega]
    refine Finset.prod_congr rfl (fun j hj => ?_)
    rw [Finset.mem_Icc] at hj
    exact prod_K_split hc n (by omega) hj.2 (fun i : ℕ => (C (y + (i : ℚ)) + X : PowerSeries ℚ))
  have hsubstP : subst y (Ppoly c n) =
      C (Nh c n) * (C 2 * (C y + X) + C (c.h0 n : ℚ)) *
        (∏ j ∈ Icc 1 c.r, ((∏ i ∈ Ico 1 (c.h n j), (C (y + (i : ℚ)) + X)) *
          ∏ i ∈ Ico (c.h0 n - c.h n j + 1) (c.h0 n), (C (y + (i : ℚ)) + X))) *
        ∏ j ∈ Icc (c.r + 1) c.q,
          ∏ i ∈ Krange c n \ Ico (c.h n j) (c.h0 n - c.h n j + 1), (C (y + (i : ℚ)) + X) := by
    unfold Ppoly
    rw [map_mul, map_mul, map_mul, subst_C, subst_lin, map_prod, map_prod]
    simp only [map_mul, subst_prodLin]
  have hL : (C ((c.h0 n : ℚ) + 2 * y) + C 2 * X : PowerSeries ℚ) =
      C 2 * (C y + X) + C (c.h0 n : ℚ) := by
    rw [map_add, map_mul]
    ring
  unfold Rser
  apply mul_inv_eq_mul_inv hB0 hW0
  rw [hA, hW, hB, hsubstP, hL]
  simp only [Finset.prod_mul_distrib]
  ring

theorem series_eq {c : Config} (hc : Admissible c) {n : ℕ} (hn : 1 ≤ n) (y : ℚ)
    (hy : ∀ k ∈ Krange c n, y + k ≠ 0) :
    Rser c n y = ∑ j ∈ Icc (c.r + 1) c.q, ∑ k ∈ Krange c n,
      C (B c n j k) * ((C (y + k) + X) ^ (j - c.r))⁻¹ := by
  have hf0 : ∀ i ∈ Krange c n, constantCoeff (C (y + (i : ℚ)) + X : PowerSeries ℚ) ≠ 0 := by
    intro i hi
    rw [map_add, constantCoeff_C, constantCoeff_X, add_zero]
    exact hy i hi
  set W : PowerSeries ℚ := ∏ k ∈ Krange c n, (C (y + (k : ℚ)) + X) ^ (c.q - c.r) with hW
  have hW0 : constantCoeff W ≠ 0 := by
    rw [hW, map_prod, Finset.prod_ne_zero_iff]
    intro k hk
    rw [map_pow]
    exact pow_ne_zero _ (hf0 k hk)
  rw [Rser_eq_subst hc hn y hy, poly_eq hc hn]
  unfold PFpoly
  rw [map_sum, Finset.sum_mul]
  refine Finset.sum_congr rfl (fun j hj => ?_)
  rw [Finset.mem_Icc] at hj
  rw [map_sum, Finset.sum_mul]
  refine Finset.sum_congr rfl (fun k hk => ?_)
  rw [map_mul, map_mul, subst_C, map_pow, subst_X_add_C, map_prod]
  simp only [map_pow, subst_X_add_C]
  rw [mul_assoc, mul_assoc]
  congr 1
  have hFk : constantCoeff ((C (y + (k : ℚ)) + X) ^ (j - c.r) : PowerSeries ℚ) ≠ 0 := by
    rw [map_pow]
    exact pow_ne_zero _ (hf0 k hk)
  rw [PowerSeries.eq_inv_iff_mul_eq_one hFk]
  have hWk : W = (C (y + (k : ℚ)) + X) ^ (c.q - c.r) *
      ∏ k' ∈ (Krange c n).erase k, (C (y + (k' : ℚ)) + X) ^ (c.q - c.r) := by
    rw [hW]
    exact (Finset.mul_prod_erase _
      (fun k' : ℕ => (C (y + (k' : ℚ)) + X : PowerSeries ℚ) ^ (c.q - c.r)) hk).symm
  calc (C (y + (k : ℚ)) + X) ^ (c.q - j) *
        ((∏ k' ∈ (Krange c n).erase k, (C (y + (k' : ℚ)) + X) ^ (c.q - c.r)) * W⁻¹) *
        (C (y + (k : ℚ)) + X) ^ (j - c.r)
      = ((C (y + (k : ℚ)) + X) ^ (c.q - j) * (C (y + (k : ℚ)) + X) ^ (j - c.r) *
          ∏ k' ∈ (Krange c n).erase k, (C (y + (k' : ℚ)) + X) ^ (c.q - c.r)) * W⁻¹ := by ring
    _ = W * W⁻¹ := by
        rw [← pow_add, show c.q - j + (j - c.r) = c.q - c.r by omega, hWk]
    _ = 1 := PowerSeries.mul_inv_cancel W hW0

end PartialFractions

theorem PF_proof : Stmt_PF := by
  intro c hc n hn y hy
  exact PartialFractions.series_eq hc hn y hy

end ZetaWindow

end
