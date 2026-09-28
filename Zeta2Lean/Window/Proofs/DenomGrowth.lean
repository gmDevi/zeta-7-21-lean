import Zeta2Lean.Window.Statements

set_option linter.style.header false
set_option linter.style.longLine false

/-!
# Growth of the denominators: `Δ_n ≤ e^{748 n}` eventually (JTNB Proposition 5; docs/window/proof.md §2)

**Statement.** `Stmt_DenomGrowth` from `Zeta2.PNT_Stmt` (`ψ(x)/x → 1`), `Stmt_OmegaPhi0`,
`Stmt_PhiTable` and `Stmt_PhiData`: `∀ᶠ n in atTop, (Delta cfgW n : ℝ) ≤ exp (748 n)`.

**Informal proof.**  Let `δ > 0` small (fixed below) and `n` large.
1. *Numerator.*  For `cfgW` and every `n`, `mj cfgW n j = mu cfgW j * n` (`= 63n, 63n, 62n, 61n, 60n, …`),
   so `log Dprod = 5 ψ(63n) + ∑_{j=2}^{18} ψ(μ_j n) ≤ (1+δ) · 1341 · n` once `n ≥ X₀` (PNT; `muSum_cfgW`).
2. *Φ_n from the table.*  `log PhiN = ∑_{p prime, h₀ < p², p ≤ 60n} ω_p log p` (all `ω_p ≥ 0`).  For a
   piece `e` and a translate `m ∈ {0, …, 20}` (with `m = 0` only if `e.a ≥ 1/60`), every prime `p`
   with `(e.a + m) p < n < (e.b + m) p` has `fract(n/p) ∈ (e.a, e.b)`, hence (`Stmt_OmegaPhi0`,
   `Stmt_PhiTable`) `ω_{k,p} = φ₀(n/p, (k-1)/p) ≥ v` for all `k`, i.e. `ω_p ≥ v`.  Since the table is
   sorted and disjoint (`Stmt_PhiData`), at most one piece, and at most one of its translates, contains
   `n/p`.  Therefore
   `log PhiN ≥ ∑_{e, m} v_e (θ(n/(e.a+m)) - θ(n/(e.b+m)) - E_n)`, `E_n = log(60n+1) + θ(⌊√(160n+2)⌋)`
   (the `log(60n+1)` removes a possible prime `p = n/(e.a+m)`, the `θ`-term the primes with `p² ≤ h₀`).
3. *PNT for θ.*  `(1-δ) x ≤ θ(x)` and `θ(x) ≤ ψ(x) ≤ (1+δ) x` for all `x ≥ X₀` (uniformly; from PNT
   and `Chebyshev.psi_sub_theta_le_mul_sqrt`).  All arguments `n/(e.a+m)`, `n/(e.b+m)` are `≥ n/21`, so
   for `n ≥ 21 X₀`: `log PhiN ≥ n P - δ n W - E_n V` with `P = phiSumQ phiTable 60 20`,
   `W = ∑_{e,m} v_e (1/(e.a+m) + 1/(e.b+m))`, `V = ∑_{e,m} v_e`; and `E_n ≤ 42 √n`.
4. *Conclusion.*  By `Stmt_PhiData.sum`, `ε := 748 - (1341 - P) > 0`.  With `δ (1341 + W) = ε/4` and
   `n ≥ 21 X₀ + (56 V/ε)² + 1` (so `E_n V ≤ (3/4) ε n`):
   `log Δ_n = log Dprod - log PhiN ≤ 748 n - ε n + (ε/4) n + (3/4) ε n = 748 n`.

**Lean structure** (helpers in `ZetaWindow.DenomGrowth`).
* §1 The table functional `tabL T G = ∑_{e ∈ T} v_e ([1/60 ≤ a] G(a,b) + ∑_{m=1}^{20} G(a+m, b+m))`:
  linear (`tabL_add`, `tabL_sub`, `tabL_mul`, `tabL_sum`), monotone in `G` on `1/60 ≤ a < b ≤ 21`
  (`tabL_mono`), and `phiSumQ T 60 20 = tabL T (1/a - 1/b)` (`phiSumQ_cast`).
* §2–4 `tabL T [a < n/p < b] ≤ ω_p` (`tabL_ind_le`): a sorted chain has at most one piece containing
  a point (`sum_le_of_chain`), a piece has at most one translate containing it (`cntI_le_one`,
  `floor_of_mem`), and on it `v ≤ ω_p` (`v_le_omega`: `Stmt_OmegaPhi0` + `Stmt_PhiTable`).
* §5 `θ(n/a) - θ(n/b) - E_n ≤ Gn n a b = ∑_{i ≤ 60n, i prime, i² > h₀} log i · [a < n/i < b]`
  (`Gn_ge`, termwise over `range (60n+1)`, `theta_eq_sum_range`).
* §6 Uniform PNT bounds (`pnt_unif`).
* §7 `log Dprod ≤ (1+δ) 1341 n` (`log_Dprod`, `log_Dprod_le`, `mj_cfgW`);
  `log PhiN = ∑ ω_i log i` (`log_PhiN`), `tabL T (Gn n) ≤ log PhiN` (`log_PhiN_ge`), and
  `n P - δ n W - E_n V ≤ log PhiN` (`log_PhiN_ge'`).
* §8 `E_n ≤ 42 √n` (`En_le`: `log y ≤ 2√y`, `θ(x) ≤ log 4 · x`).
* `DenomGrowth_proof`: the choice of `ε`, `δ`, `X₀` and the final inequality in `log` form
  (`Real.log_le_iff_le_exp`).

**Numerical check.** `python/window_mirror.py`, section "Stmt_DenomGrowth": `log Δ_n / n = 832.9,
803.1, 785.3, 780.5` for `n = 5, 10, 20, 40` (slow PNT convergence; the limit is `C₂ = 747.05`), and
`log PhiN ≥` the table bound of step 2 exactly.  `python/window_audit/delta_growth.py` (exact `ω_p`)
reproduces these and continues `769.7, 761.6, 756.2, 755.0` for `n = 80, 160, 320, 640`; much of the
remaining gap is the cut-off `p² > h₀` (it drops `x = n/p ≥ √(n/160)`), which vanishes as `n → ∞`.

**Status: proved** (complete; axioms: `propext`, `Classical.choice`, `Quot.sound`).
-/

open Filter Topology Finset

noncomputable section

namespace ZetaWindow

namespace DenomGrowth

/-! ### 1. The table functional `Λ_T` -/

/-- The share of one piece: `v · ([1/60 ≤ a] G(a, b) + ∑_{m=1}^{20} G(a+m, b+m))`
(the shape of `phiWeight 60 20`, with `G(a, b) = 1/a - 1/b`). -/
def pieceW (G : ℚ → ℚ → ℝ) (e : Piece) : ℝ :=
  (e.v : ℝ) * ((if (1 / 60 : ℚ) ≤ e.a then G e.a e.b else 0) +
    ∑ m ∈ Icc (1 : ℕ) 20, G (e.a + m) (e.b + m))

/-- `Λ_T(G) = ∑_{e ∈ T} pieceW G e`. -/
def tabL (T : List Piece) (G : ℚ → ℚ → ℝ) : ℝ :=
  (T.map (pieceW G)).sum

theorem pieceW_add (G H : ℚ → ℚ → ℝ) (e : Piece) :
    pieceW (fun a b => G a b + H a b) e = pieceW G e + pieceW H e := by
  unfold pieceW
  split_ifs <;> simp only [Finset.sum_add_distrib] <;> ring

theorem pieceW_mul (c : ℝ) (G : ℚ → ℚ → ℝ) (e : Piece) :
    pieceW (fun a b => c * G a b) e = c * pieceW G e := by
  unfold pieceW
  split_ifs <;> simp only [← Finset.mul_sum] <;> ring

theorem pieceW_sub (G H : ℚ → ℚ → ℝ) (e : Piece) :
    pieceW (fun a b => G a b - H a b) e = pieceW G e - pieceW H e := by
  unfold pieceW
  split_ifs <;> simp only [Finset.sum_sub_distrib] <;> ring

theorem pieceW_zero (e : Piece) : pieceW (fun _ _ => 0) e = 0 := by
  unfold pieceW
  split_ifs <;> simp

theorem tabL_add (T : List Piece) (G H : ℚ → ℚ → ℝ) :
    tabL T (fun a b => G a b + H a b) = tabL T G + tabL T H := by
  unfold tabL
  rw [← List.sum_map_add]
  congr 1
  exact List.map_congr_left fun e _ => pieceW_add G H e

theorem tabL_sub (T : List Piece) (G H : ℚ → ℚ → ℝ) :
    tabL T (fun a b => G a b - H a b) = tabL T G - tabL T H := by
  induction T with
  | nil => simp [tabL]
  | cons e T ih =>
    simp only [tabL, List.map_cons, List.sum_cons] at ih ⊢
    rw [ih, pieceW_sub]
    ring

theorem tabL_mul (T : List Piece) (c : ℝ) (G : ℚ → ℚ → ℝ) :
    tabL T (fun a b => c * G a b) = c * tabL T G := by
  induction T with
  | nil => simp [tabL]
  | cons e T ih =>
    simp only [tabL, List.map_cons, List.sum_cons] at ih ⊢
    rw [ih, pieceW_mul]
    ring

theorem tabL_zero (T : List Piece) : tabL T (fun _ _ => 0) = 0 := by
  unfold tabL
  apply List.sum_eq_zero
  intro x hx
  obtain ⟨e, _, rfl⟩ := List.mem_map.1 hx
  exact pieceW_zero e

theorem tabL_sum {ι : Type*} (T : List Piece) (s : Finset ι) (w : ι → ℝ)
    (H : ι → ℚ → ℚ → ℝ) :
    tabL T (fun a b => ∑ i ∈ s, w i * H i a b) = ∑ i ∈ s, w i * tabL T (H i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using tabL_zero T
  | insert j s hj ih =>
    simp only [Finset.sum_insert hj]
    rw [tabL_add T (fun a b => w j * H j a b) (fun a b => ∑ i ∈ s, w i * H i a b), ih,
      tabL_mul]

/-- Monotonicity: only the pairs `(a, b)` with `1/60 ≤ a < b ≤ 21` occur. -/
theorem tabL_mono (T : List Piece) (hT : ∀ e ∈ T, 0 ≤ e.a ∧ e.a < e.b ∧ e.b ≤ 1)
    (G H : ℚ → ℚ → ℝ) (hGH : ∀ a b : ℚ, 1 / 60 ≤ a → a < b → b ≤ 21 → G a b ≤ H a b) :
    tabL T G ≤ tabL T H := by
  unfold tabL
  apply List.sum_le_sum
  intro e he
  obtain ⟨h0, h1, h2⟩ := hT e he
  unfold pieceW
  apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg _)
  apply add_le_add
  · split_ifs with h
    · exact hGH _ _ h h1 (by linarith)
    · exact le_rfl
  · apply Finset.sum_le_sum
    intro m hm
    have hm' := Finset.mem_Icc.1 hm
    have hm1 : (1 : ℚ) ≤ m := by exact_mod_cast hm'.1
    have hm2 : (m : ℚ) ≤ 20 := by exact_mod_cast hm'.2
    exact hGH _ _ (by linarith) (by linarith) (by linarith)

/-- The certified sum as a value of `Λ_T`. -/
theorem phiSumQ_cast (T : List Piece) :
    ((phiSumQ T 60 20 : ℚ) : ℝ) = tabL T (fun a b => ((1 / a - 1 / b : ℚ) : ℝ)) := by
  unfold phiSumQ tabL
  rw [Rat.cast_list_sum, List.map_map]
  congr 1
  apply List.map_congr_left
  intro e _
  simp only [Function.comp_apply, phiWeight, pieceW, Rat.cast_mul, Rat.cast_natCast,
    Rat.cast_add, Rat.cast_sum, apply_ite (Rat.cast : ℚ → ℝ), Rat.cast_zero, Nat.cast_ofNat]

/-! ### 2. At most one piece of a sorted table contains a given point -/

theorem chain_ge (e : Piece) (T : List Piece) (hc : (e :: T).IsChain (fun e f => e.b ≤ f.a))
    (hb : ∀ g ∈ e :: T, g.a < g.b) : ∀ g ∈ T, e.b ≤ g.a := by
  induction T generalizing e with
  | nil => simp
  | cons f T ih =>
    rw [List.isChain_cons_cons] at hc
    intro g hg
    rcases List.mem_cons.1 hg with rfl | hg
    · exact hc.1
    · have h1 := ih f hc.2 (fun g hg => hb g (List.mem_cons_of_mem _ hg)) g hg
      have h2 := hb f (by simp)
      linarith [hc.1]

theorem sum_le_of_chain (T : List Piece) (hc : T.IsChain (fun e f => e.b ≤ f.a))
    (hb : ∀ g ∈ T, g.a < g.b) (f : ℚ) (M : ℝ) (hM : 0 ≤ M) (c : Piece → ℝ)
    (hc1 : ∀ e ∈ T, c e ≤ 1) (hsupp : ∀ e ∈ T, c e ≠ 0 → e.a < f ∧ f < e.b)
    (hv : ∀ e ∈ T, e.a < f → f < e.b → (e.v : ℝ) ≤ M) :
    (T.map (fun e => (e.v : ℝ) * c e)).sum ≤ M := by
  induction T with
  | nil => simpa using hM
  | cons e T ih =>
    have hcT : T.IsChain (fun e f => e.b ≤ f.a) := hc.tail
    have hge := chain_ge e T hc hb
    simp only [List.map_cons, List.sum_cons]
    by_cases hce : c e = 0
    · rw [hce, mul_zero, zero_add]
      exact ih hcT (fun g hg => hb g (List.mem_cons_of_mem _ hg))
        (fun g hg => hc1 g (List.mem_cons_of_mem _ hg))
        (fun g hg => hsupp g (List.mem_cons_of_mem _ hg))
        (fun g hg => hv g (List.mem_cons_of_mem _ hg))
    · obtain ⟨ha, hb'⟩ := hsupp e (by simp) hce
      have hzero : (T.map (fun e => (e.v : ℝ) * c e)).sum = 0 := by
        apply List.sum_eq_zero
        intro x hx
        obtain ⟨g, hg, rfl⟩ := List.mem_map.1 hx
        have hcg : c g = 0 := by
          by_contra hne
          have h1 := (hsupp g (List.mem_cons_of_mem _ hg) hne).1
          have h2 := hge g hg
          linarith
        simp [hcg]
      rw [hzero, add_zero]
      calc (e.v : ℝ) * c e ≤ (e.v : ℝ) * 1 :=
            mul_le_mul_of_nonneg_left (hc1 e (by simp)) (Nat.cast_nonneg _)
        _ = e.v := mul_one _
        _ ≤ M := hv e (by simp) ha hb'

/-! ### 3. The indicator of `x ∈ (a, b)` and the count of translates -/

/-- `[a < x < b]`. -/
def indI (x a b : ℚ) : ℝ := if a < x ∧ x < b then 1 else 0

/-- How many of the translates of `e` used by the table contain `x` (at most one). -/
def cntI (x : ℚ) (e : Piece) : ℝ :=
  (if (1 / 60 : ℚ) ≤ e.a then indI x e.a e.b else 0) +
    ∑ m ∈ Icc (1 : ℕ) 20, indI x (e.a + m) (e.b + m)

theorem floor_of_mem (e : Piece) (h0 : 0 ≤ e.a) (h1 : e.b ≤ 1) (x : ℚ) (m : ℕ)
    (hx : e.a + m < x ∧ x < e.b + m) :
    ⌊x⌋ = (m : ℤ) ∧ e.a < Int.fract x ∧ Int.fract x < e.b := by
  have hfl : ⌊x⌋ = (m : ℤ) := by
    rw [Int.floor_eq_iff]
    push_cast
    constructor <;> linarith [hx.1, hx.2]
  have hfr : Int.fract x = x - m := by
    rw [← Int.self_sub_floor, hfl]
    push_cast
    ring
  refine ⟨hfl, ?_, ?_⟩
  · rw [hfr]; linarith [hx.1]
  · rw [hfr]; linarith [hx.2]

theorem cntI_le_one (e : Piece) (h0 : 0 ≤ e.a) (h1 : e.b ≤ 1) (x : ℚ) : cntI x e ≤ 1 := by
  have hS : ∑ m ∈ Icc (1 : ℕ) 20, indI x (e.a + m) (e.b + m) ≤ 1 := by
    unfold indI
    rw [Finset.sum_boole]
    have hc : ((Icc (1 : ℕ) 20).filter (fun m : ℕ => e.a + m < x ∧ x < e.b + m)).card ≤ 1 := by
      rw [Finset.card_le_one]
      intro m hm m' hm'
      rw [Finset.mem_filter] at hm hm'
      have h := (floor_of_mem e h0 h1 x m hm.2).1
      have h' := (floor_of_mem e h0 h1 x m' hm'.2).1
      rw [h] at h'
      exact_mod_cast h'
    exact_mod_cast hc
  unfold cntI
  by_cases hx : (1 / 60 : ℚ) ≤ e.a ∧ e.a < x ∧ x < e.b
  · have hzero : ∑ m ∈ Icc (1 : ℕ) 20, indI x (e.a + m) (e.b + m) = 0 := by
      apply Finset.sum_eq_zero
      intro m hm
      have hm1 : (1 : ℚ) ≤ m := by exact_mod_cast (Finset.mem_Icc.1 hm).1
      unfold indI
      exact ite_eq_right (fun h => by linarith [h.1, hx.2.2])
    rw [hzero, ite_eq_left hx.1]
    unfold indI
    rw [ite_eq_left hx.2]
    norm_num
  · have hfirst : (if (1 / 60 : ℚ) ≤ e.a then indI x e.a e.b else 0) = 0 := by
      split_ifs with h
      · unfold indI
        exact ite_eq_right (fun h' => hx ⟨h, h'⟩)
      · rfl
    rw [hfirst, zero_add]
    exact hS

theorem cntI_supp (e : Piece) (h0 : 0 ≤ e.a) (h1 : e.b ≤ 1) (x : ℚ) (hc : cntI x e ≠ 0) :
    e.a < Int.fract x ∧ Int.fract x < e.b := by
  unfold cntI at hc
  by_cases hfirst : (if (1 / 60 : ℚ) ≤ e.a then indI x e.a e.b else 0) = 0
  · rw [hfirst, zero_add] at hc
    obtain ⟨m, _, hm⟩ := Finset.exists_ne_zero_of_sum_ne_zero hc
    unfold indI at hm
    split_ifs at hm with hx
    · exact (floor_of_mem e h0 h1 x m hx).2
    · exact absurd rfl hm
  · split_ifs at hfirst with hc'
    · unfold indI at hfirst
      split_ifs at hfirst with hx
      · exact (floor_of_mem e h0 h1 x 0 (by simpa using hx)).2
      · exact absurd rfl hfirst
    · exact absurd rfl hfirst

/-! ### 4. `ω_p ≥ v` on a valid piece, and `Λ_T([· < n/p < ·]) ≤ ω_p` -/

theorem v_le_omega (hO : Stmt_OmegaPhi0) (e : Piece) (he : PieceValid cfgW e) (n p : ℕ)
    (hp : 0 < p) (h1 : e.a < Int.fract ((n : ℚ) / p)) (h2 : Int.fract ((n : ℚ) / p) < e.b) :
    (e.v : ℝ) ≤ ((omegaP cfgW n p).toNat : ℝ) := by
  have hv : (e.v : ℤ) ≤ omegaP cfgW n p := by
    unfold omegaP
    rw [dite_eq_left hp]
    apply Finset.le_inf'
    intro k _
    rw [hO cfgW n p k hp]
    exact he _ _ h1 h2
  have h : e.v ≤ (omegaP cfgW n p).toNat :=
    (Int.le_toNat (le_trans (Nat.cast_nonneg _) hv)).2 hv
  exact_mod_cast h

theorem tabL_ind_le (hO : Stmt_OmegaPhi0) (T : List Piece)
    (hb : ∀ e ∈ T, 0 < e.ad ∧ 0 < e.bd ∧ 0 ≤ e.a ∧ e.a < e.b ∧ e.b ≤ 1)
    (hs : T.IsChain (fun e f => e.b ≤ f.a)) (hv : ∀ e ∈ T, PieceValid cfgW e)
    (n p : ℕ) (hp : 0 < p) :
    tabL T (indI ((n : ℚ) / p)) ≤ ((omegaP cfgW n p).toNat : ℝ) := by
  change (T.map (fun e => (e.v : ℝ) * cntI ((n : ℚ) / p) e)).sum ≤ _
  exact sum_le_of_chain T hs (fun g hg => (hb g hg).2.2.2.1) (Int.fract ((n : ℚ) / p)) _
    (Nat.cast_nonneg _) (cntI ((n : ℚ) / p))
    (fun e he => cntI_le_one e (hb e he).2.2.1 (hb e he).2.2.2.2 _)
    (fun e he hc => cntI_supp e (hb e he).2.2.1 (hb e he).2.2.2.2 _ hc)
    (fun e he h1 h2 => v_le_omega hO e (hv e he) n p hp h1 h2)

/-! ### 5. `θ` as a sum over `range N`; the primes of `Φ_n` in one window `n/p ∈ (a, b)` -/

theorem theta_eq_sum_range {X : ℝ} (hX : 0 ≤ X) {N : ℕ} (hXN : X < N) :
    Chebyshev.theta X = ∑ i ∈ range N, if i.Prime ∧ (i : ℝ) ≤ X then Real.log i else 0 := by
  rw [Chebyshev.theta, ← Finset.sum_filter]
  apply Finset.sum_congr _ (fun _ _ => rfl)
  ext i
  simp only [Finset.mem_filter, Finset.mem_Ioc, Finset.mem_range]
  constructor
  · rintro ⟨⟨_, h1⟩, hp⟩
    have hiX : (i : ℝ) ≤ X := (Nat.le_floor_iff hX).1 h1
    refine ⟨?_, hp, hiX⟩
    have : (i : ℝ) < N := lt_of_le_of_lt hiX hXN
    exact_mod_cast this
  · rintro ⟨_, hp, hiX⟩
    exact ⟨⟨hp.pos, (Nat.le_floor_iff hX).2 hiX⟩, hp⟩

/-- `∑_{p ∈ Φ_n, a < n/p < b} log p`, summed over `i < 60n + 1` with indicators. -/
def Gn (n : ℕ) (a b : ℚ) : ℝ :=
  ∑ i ∈ range (60 * n + 1),
    (if i.Prime ∧ 160 * n + 2 < i ^ 2 then Real.log i else 0) * indI ((n : ℚ) / i) a b

/-- The error term `E_n = log(60n+1) + θ(⌊√(160n+2)⌋)`. -/
def En (n : ℕ) : ℝ :=
  Real.log ((60 * n + 1 : ℕ) : ℝ) + Chebyshev.theta ((Nat.sqrt (160 * n + 2) : ℕ) : ℝ)

/-- One window: the primes `n/b < p ≤ n/a` are those of `Gn n a b`, up to the endpoint
`p = n/a` and the primes `p² ≤ h₀`. -/
theorem Gn_ge (n : ℕ) (hn : 1 ≤ n) (a b : ℚ) (ha : 1 / 60 ≤ a) (hab : a < b) :
    Chebyshev.theta ((n : ℝ) / a) - Chebyshev.theta ((n : ℝ) / b) - En n ≤ Gn n a b := by
  unfold Gn
  have hEn : En n = Real.log ((60 * n + 1 : ℕ) : ℝ) +
      Chebyshev.theta ((Nat.sqrt (160 * n + 2) : ℕ) : ℝ) := rfl
  rw [hEn]
  set N := 60 * n + 1 with hN
  set s := Nat.sqrt (160 * n + 2) with hs
  set X : ℝ := (n : ℝ) / a with hXdef
  set Y : ℝ := (n : ℝ) / b with hYdef
  set L : ℝ := Real.log (N : ℝ) with hL
  have ha0 : (0 : ℚ) < a := lt_of_lt_of_le (by norm_num) ha
  have hb0 : (0 : ℚ) < b := ha0.trans hab
  have ha0' : (0 : ℝ) < a := by exact_mod_cast ha0
  have hb0' : (0 : ℝ) < b := by exact_mod_cast hb0
  have hab' : (a : ℝ) < b := by exact_mod_cast hab
  have ha' : (1 / 60 : ℝ) ≤ a := by
    have h := (Rat.cast_le (K := ℝ)).2 ha
    push_cast at h
    exact h
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  have hY0 : 0 ≤ Y := by rw [hYdef]; positivity
  have hYX : Y < X := by rw [hXdef, hYdef]; exact div_lt_div_of_pos_left hn0 ha0' hab'
  have hX60 : X ≤ 60 * n := by
    rw [hXdef, div_le_iff₀ ha0']
    nlinarith
  have hNR : (N : ℝ) = 60 * n + 1 := by rw [hN]; push_cast; ring
  have hXN : X < N := by rw [hNR]; linarith
  have hsN : (s : ℝ) < N := by
    have : s < N := by
      rw [hs, Nat.sqrt_lt', hN]
      nlinarith
    exact_mod_cast this
  have hL0 : 0 ≤ L := Real.log_natCast_nonneg _
  rw [theta_eq_sum_range (hY0.trans hYX.le) hXN, theta_eq_sum_range hY0 (hYX.trans hXN),
    theta_eq_sum_range (Nat.cast_nonneg s) hsN]
  have hLsum : ∑ i ∈ range N, (if i = ⌊X⌋₊ then L else 0) ≤ L := by
    rw [Finset.sum_ite_eq']
    split_ifs
    · exact le_rfl
    · exact hL0
  have key : ∀ i ∈ range N,
      (if i.Prime ∧ (i : ℝ) ≤ X then Real.log i else 0) -
          (if i.Prime ∧ (i : ℝ) ≤ Y then Real.log i else 0) ≤
        (if i.Prime ∧ 160 * n + 2 < i ^ 2 then Real.log i else 0) * indI ((n : ℚ) / i) a b +
          (if i = ⌊X⌋₊ then L else 0) + (if i.Prime ∧ (i : ℝ) ≤ s then Real.log i else 0) := by
    intro i hi
    have hiN : i < N := Finset.mem_range.1 hi
    have hlog : 0 ≤ Real.log i := Real.log_natCast_nonneg i
    have hlogL : Real.log i ≤ L := by
      rcases Nat.eq_zero_or_pos i with h | h
      · rw [h, Nat.cast_zero, Real.log_zero]; exact hL0
      · exact Real.log_le_log (by exact_mod_cast h) (by exact_mod_cast hiN.le)
    have hind : 0 ≤ indI ((n : ℚ) / i) a b := by unfold indI; split_ifs <;> norm_num
    have hA : 0 ≤ (if i.Prime ∧ 160 * n + 2 < i ^ 2 then Real.log i else 0) *
        indI ((n : ℚ) / i) a b :=
      mul_nonneg (by split_ifs <;> linarith) hind
    have hB : 0 ≤ (if i = ⌊X⌋₊ then L else 0) := by split_ifs <;> linarith
    have hC : 0 ≤ (if i.Prime ∧ (i : ℝ) ≤ s then Real.log i else 0) := by
      split_ifs <;> linarith
    by_cases hp : i.Prime
    swap
    · have e1 : (if i.Prime ∧ (i : ℝ) ≤ X then Real.log i else 0) = 0 :=
        ite_eq_right (fun h => hp h.1)
      have e2 : (if i.Prime ∧ (i : ℝ) ≤ Y then Real.log i else 0) = 0 :=
        ite_eq_right (fun h => hp h.1)
      rw [e1, e2]
      linarith
    by_cases hiY : (i : ℝ) ≤ Y
    · have hiX : (i : ℝ) ≤ X := hiY.trans hYX.le
      have e1 : (if i.Prime ∧ (i : ℝ) ≤ X then Real.log i else 0) = Real.log i :=
        ite_eq_left ⟨hp, hiX⟩
      have e2 : (if i.Prime ∧ (i : ℝ) ≤ Y then Real.log i else 0) = Real.log i :=
        ite_eq_left ⟨hp, hiY⟩
      rw [e1, e2]
      linarith
    have e2 : (if i.Prime ∧ (i : ℝ) ≤ Y then Real.log i else 0) = 0 :=
      ite_eq_right (fun h => hiY h.2)
    by_cases hiX : (i : ℝ) ≤ X
    swap
    · have e1 : (if i.Prime ∧ (i : ℝ) ≤ X then Real.log i else 0) = 0 :=
        ite_eq_right (fun h => hiX h.2)
      rw [e1, e2]
      linarith
    have e1 : (if i.Prime ∧ (i : ℝ) ≤ X then Real.log i else 0) = Real.log i :=
      ite_eq_left ⟨hp, hiX⟩
    rw [e1, e2, sub_zero]
    by_cases hsq : 160 * n + 2 < i ^ 2
    · by_cases hXi : (i : ℝ) < X
      · have hi0 : (0 : ℚ) < i := by exact_mod_cast hp.pos
        have h1 : a < (n : ℚ) / i := by
          rw [lt_div_iff₀ hi0]
          have h' : (i : ℝ) * a < n := by
            rw [hXdef, lt_div_iff₀ ha0'] at hXi
            exact hXi
          have h'' : ((a * i : ℚ) : ℝ) < ((n : ℚ) : ℝ) := by push_cast; linarith
          exact_mod_cast h''
        have h2 : (n : ℚ) / i < b := by
          rw [div_lt_iff₀ hi0]
          have hYi : Y < i := lt_of_not_ge hiY
          have h' : (n : ℝ) < i * b := by
            rw [hYdef, div_lt_iff₀ hb0'] at hYi
            exact hYi
          have h'' : ((n : ℚ) : ℝ) < ((b * i : ℚ) : ℝ) := by push_cast; linarith
          exact_mod_cast h''
        have e3 : indI ((n : ℚ) / i) a b = 1 := ite_eq_left ⟨h1, h2⟩
        have e4 : (if i.Prime ∧ 160 * n + 2 < i ^ 2 then Real.log i else 0) = Real.log i :=
          ite_eq_left ⟨hp, hsq⟩
        rw [e3, e4, mul_one]
        linarith
      · have hiXeq : (i : ℝ) = X := le_antisymm hiX (not_lt.1 hXi)
        have hfl : i = ⌊X⌋₊ := by rw [← hiXeq, Nat.floor_natCast]
        have e3 : (if i = ⌊X⌋₊ then L else 0) = L := ite_eq_left hfl
        rw [e3]
        linarith
    · have hsi : i ≤ s := Nat.le_sqrt'.2 (not_lt.1 hsq)
      have hsi' : (i : ℝ) ≤ s := by exact_mod_cast hsi
      have e3 : (if i.Prime ∧ (i : ℝ) ≤ s then Real.log i else 0) = Real.log i :=
        ite_eq_left ⟨hp, hsi'⟩
      rw [e3]
      linarith
  have hsum := Finset.sum_le_sum key
  rw [Finset.sum_sub_distrib, Finset.sum_add_distrib, Finset.sum_add_distrib] at hsum
  linarith

/-! ### 6. PNT: uniform bounds for `θ` and `ψ` -/

theorem pnt_unif (hPNT : Zeta2.PNT_Stmt) {δ : ℝ} (hδ : 0 < δ) :
    ∃ X₀ : ℝ, 0 ≤ X₀ ∧ ∀ x : ℝ, X₀ ≤ x →
      (1 - δ) * x ≤ Chebyshev.theta x ∧ Chebyshev.psi x ≤ (1 + δ) * x := by
  obtain ⟨C, hC⟩ := Chebyshev.psi_sub_theta_le_mul_sqrt
  have h1 : ∀ᶠ x : ℝ in atTop, 1 - δ / 2 < Chebyshev.psi x / x :=
    (tendsto_order.1 hPNT).1 _ (by linarith)
  have h2 : ∀ᶠ x : ℝ in atTop, Chebyshev.psi x / x < 1 + δ :=
    (tendsto_order.1 hPNT).2 _ (by linarith)
  have h3 : ∀ᶠ x : ℝ in atTop, (2 * |C| / δ) ^ 2 + 1 ≤ x := eventually_ge_atTop _
  obtain ⟨X₁, hX₁⟩ := eventually_atTop.1 (h1.and (h2.and h3))
  refine ⟨max X₁ 0, le_max_right _ _, fun x hx => ?_⟩
  obtain ⟨hx1, hx2, hx3⟩ := hX₁ x (le_trans (le_max_left _ _) hx)
  have hxpos : 0 < x := by nlinarith [sq_nonneg (2 * |C| / δ)]
  rw [lt_div_iff₀ hxpos] at hx1
  rw [div_lt_iff₀ hxpos] at hx2
  have hsq : 2 * |C| / δ ≤ Real.sqrt x := by
    have h := Real.sqrt_le_sqrt (show (2 * |C| / δ) ^ 2 ≤ x by linarith)
    rwa [Real.sqrt_sq (div_nonneg (by positivity) hδ.le)] at h
  have hs0 : 0 ≤ Real.sqrt x := Real.sqrt_nonneg x
  have hsx : Real.sqrt x * Real.sqrt x = x := Real.mul_self_sqrt hxpos.le
  have hC' : |C| ≤ δ / 2 * Real.sqrt x := by
    rw [div_le_iff₀ hδ] at hsq
    linarith
  have hCx : C * Real.sqrt x ≤ δ / 2 * x := by
    calc C * Real.sqrt x ≤ |C| * Real.sqrt x := mul_le_mul_of_nonneg_right (le_abs_self C) hs0
      _ ≤ (δ / 2 * Real.sqrt x) * Real.sqrt x := mul_le_mul_of_nonneg_right hC' hs0
      _ = δ / 2 * x := by rw [mul_assoc, hsx]
  have hθ := hC x
  refine ⟨?_, by linarith⟩
  linarith

/-! ### 7. The two logarithms -/

theorem mj_cfgW (n j : ℕ) (h1 : 1 ≤ j) (h2 : j ≤ 18) : mj cfgW n j = mu cfgW j * n := by
  interval_cases j <;> simp [mj, m0, mu, Config.h0, Config.h, cfgW, etaW] <;> omega

theorem mu_ge (j : ℕ) : 1 ≤ mu cfgW j := by
  unfold mu
  exact le_trans (by decide : 1 ≤ cfgW.eta cfgW.r) (le_trans (le_max_left _ _) (le_max_left _ _))

theorem log_Dprod (n : ℕ) :
    Real.log (Dprod cfgW n : ℝ) = 5 * Chebyshev.psi (mj cfgW n 1 : ℕ) +
      ∑ j ∈ Icc 2 18, Chebyshev.psi (mj cfgW n j : ℕ) := by
  have hr : cfgW.r = 5 := rfl
  have hqr : cfgW.q - cfgW.r = 18 := rfl
  unfold Dprod
  rw [hqr, hr]
  push_cast
  have hne : ∀ m : ℕ, (Nat.lcmUpto m : ℝ) ≠ 0 := fun m => Nat.cast_ne_zero.2 (Nat.lcmUpto_ne_zero m)
  rw [Real.log_mul (pow_ne_zero _ (hne _)) (Finset.prod_ne_zero_iff.2 fun j _ => hne _),
    Real.log_pow, Real.log_prod (fun j _ => hne _)]
  simp only [Chebyshev.psi_eq_log_lcmUpto]
  push_cast
  ring

theorem log_Dprod_le (n : ℕ) (δ X₀ : ℝ) (hX : ∀ x : ℝ, X₀ ≤ x → Chebyshev.psi x ≤ (1 + δ) * x)
    (hn : X₀ ≤ n) : Real.log (Dprod cfgW n : ℝ) ≤ (1 + δ) * 1341 * n := by
  rw [log_Dprod]
  have hmu : ∀ j, 1 ≤ j → j ≤ 18 →
      Chebyshev.psi (mj cfgW n j : ℕ) ≤ (1 + δ) * ((mu cfgW j : ℝ) * n) := by
    intro j h1 h2
    rw [mj_cfgW n j h1 h2]
    push_cast
    apply hX
    have h1' : (1 : ℝ) ≤ mu cfgW j := by exact_mod_cast mu_ge j
    have := mul_le_mul_of_nonneg_right h1' (Nat.cast_nonneg n)
    linarith
  have hsum : (5 : ℝ) * mu cfgW 1 + ∑ j ∈ Icc 2 18, (mu cfgW j : ℝ) = 1341 := by
    have h := muSum_cfgW
    unfold muSum at h
    have hr : cfgW.r = 5 := rfl
    have hqr : cfgW.q - cfgW.r = 18 := rfl
    rw [hqr, hr] at h
    exact_mod_cast h
  have h1 := hmu 1 le_rfl (by norm_num)
  have h2 : ∑ j ∈ Icc 2 18, Chebyshev.psi (mj cfgW n j : ℕ) ≤
      ∑ j ∈ Icc 2 18, (1 + δ) * ((mu cfgW j : ℝ) * n) :=
    Finset.sum_le_sum fun j hj =>
      hmu j (by linarith [(Finset.mem_Icc.1 hj).1]) (Finset.mem_Icc.1 hj).2
  rw [← Finset.mul_sum, ← Finset.sum_mul] at h2
  calc 5 * Chebyshev.psi (mj cfgW n 1 : ℕ) + ∑ j ∈ Icc 2 18, Chebyshev.psi (mj cfgW n j : ℕ)
      ≤ 5 * ((1 + δ) * ((mu cfgW 1 : ℝ) * n)) +
          (1 + δ) * ((∑ j ∈ Icc 2 18, (mu cfgW j : ℝ)) * n) := by linarith
    _ = (1 + δ) * ((5 : ℝ) * mu cfgW 1 + ∑ j ∈ Icc 2 18, (mu cfgW j : ℝ)) * n := by ring
    _ = (1 + δ) * 1341 * n := by rw [hsum]

theorem log_PhiN (n : ℕ) :
    Real.log (PhiN cfgW n : ℝ) = ∑ i ∈ range (60 * n + 1),
      if i.Prime ∧ 160 * n + 2 < i ^ 2 then ((omegaP cfgW n i).toNat : ℝ) * Real.log i else 0 := by
  have hm : mj cfgW n (cfgW.q - cfgW.r) = 60 * n := by
    rw [show cfgW.q - cfgW.r = 18 from rfl, mj_cfgW n 18 (by norm_num) le_rfl,
      show mu cfgW 18 = 60 by decide]
  unfold PhiN
  rw [hm]
  push_cast
  rw [Real.log_prod (fun p hp => pow_ne_zero _ (Nat.cast_ne_zero.2
    (Finset.mem_filter.1 hp).2.1.ne_zero)), Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro i _
  rw [Real.log_pow]
  rfl

theorem log_PhiN_ge (hO : Stmt_OmegaPhi0) (T : List Piece)
    (hb : ∀ e ∈ T, 0 < e.ad ∧ 0 < e.bd ∧ 0 ≤ e.a ∧ e.a < e.b ∧ e.b ≤ 1)
    (hs : T.IsChain (fun e f => e.b ≤ f.a)) (hv : ∀ e ∈ T, PieceValid cfgW e) (n : ℕ) :
    tabL T (Gn n) ≤ Real.log (PhiN cfgW n : ℝ) := by
  rw [log_PhiN]
  have hG : tabL T (Gn n) = ∑ i ∈ range (60 * n + 1),
      (if i.Prime ∧ 160 * n + 2 < i ^ 2 then Real.log i else 0) * tabL T (indI ((n : ℚ) / i)) :=
    tabL_sum T (range (60 * n + 1)) (fun i => if i.Prime ∧ 160 * n + 2 < i ^ 2 then Real.log i else 0)
      (fun i => indI ((n : ℚ) / i))
  rw [hG]
  apply Finset.sum_le_sum
  intro i _
  split_ifs with h
  · have h1 := tabL_ind_le hO T hb hs hv n i h.1.pos
    have hlog : 0 ≤ Real.log i := Real.log_natCast_nonneg i
    calc Real.log i * tabL T (indI ((n : ℚ) / i))
        ≤ Real.log i * ((omegaP cfgW n i).toNat : ℝ) := mul_le_mul_of_nonneg_left h1 hlog
      _ = ((omegaP cfgW n i).toNat : ℝ) * Real.log i := mul_comm _ _
  · simp

/-- `log Φ_n ≥ n Λ(1/a - 1/b) - δ n Λ(1/a + 1/b) - E_n Λ(1)` once `θ(x) = (1 ± δ) x` on `x ≥ n/21`. -/
theorem log_PhiN_ge' (hO : Stmt_OmegaPhi0) (T : List Piece)
    (hb : ∀ e ∈ T, 0 < e.ad ∧ 0 < e.bd ∧ 0 ≤ e.a ∧ e.a < e.b ∧ e.b ≤ 1)
    (hs : T.IsChain (fun e f => e.b ≤ f.a)) (hv : ∀ e ∈ T, PieceValid cfgW e) (n : ℕ)
    (hn : 1 ≤ n) (δ X₀ : ℝ) (hX₀ : 0 ≤ X₀)
    (hX : ∀ x : ℝ, X₀ ≤ x → (1 - δ) * x ≤ Chebyshev.theta x ∧ Chebyshev.theta x ≤ (1 + δ) * x)
    (hn21 : 21 * X₀ ≤ n) :
    (n : ℝ) * tabL T (fun a b => ((1 / a - 1 / b : ℚ) : ℝ)) -
        δ * n * tabL T (fun a b => ((1 / a + 1 / b : ℚ) : ℝ)) - En n * tabL T (fun _ _ => 1) ≤
      Real.log (PhiN cfgW n : ℝ) := by
  have hb' : ∀ e ∈ T, 0 ≤ e.a ∧ e.a < e.b ∧ e.b ≤ 1 := fun e he => (hb e he).2.2
  have hfun : (fun a b : ℚ => (1 - δ) * ((n : ℝ) / a) - (1 + δ) * ((n : ℝ) / b) - En n) =
      fun a b : ℚ => ((n : ℝ) * ((1 / a - 1 / b : ℚ) : ℝ) - δ * n * ((1 / a + 1 / b : ℚ) : ℝ)) -
        En n * 1 := by
    funext a b
    push_cast
    ring
  have hid : tabL T (fun a b : ℚ => (1 - δ) * ((n : ℝ) / a) - (1 + δ) * ((n : ℝ) / b) - En n) =
      (n : ℝ) * tabL T (fun a b => ((1 / a - 1 / b : ℚ) : ℝ)) -
        δ * n * tabL T (fun a b => ((1 / a + 1 / b : ℚ) : ℝ)) - En n * tabL T (fun _ _ => 1) := by
    rw [hfun, tabL_sub, tabL_sub, tabL_mul, tabL_mul, tabL_mul]
  rw [← hid]
  calc tabL T (fun a b : ℚ => (1 - δ) * ((n : ℝ) / a) - (1 + δ) * ((n : ℝ) / b) - En n)
      ≤ tabL T (Gn n) := by
        apply tabL_mono T hb'
        intro a b ha hab hb21
        have ha0q : (0 : ℚ) < a := lt_of_lt_of_le (by norm_num) ha
        have ha0 : (0 : ℝ) < a := by exact_mod_cast ha0q
        have hb0 : (0 : ℝ) < b := by exact_mod_cast ha0q.trans hab
        have ha21 : (a : ℝ) ≤ 21 := by
          have : a ≤ 21 := by linarith
          exact_mod_cast this
        have hb21' : (b : ℝ) ≤ 21 := by exact_mod_cast hb21
        have hXa : X₀ ≤ (n : ℝ) / a := by
          rw [le_div_iff₀ ha0]
          nlinarith [mul_le_mul_of_nonneg_left ha21 hX₀]
        have hXb : X₀ ≤ (n : ℝ) / b := by
          rw [le_div_iff₀ hb0]
          nlinarith [mul_le_mul_of_nonneg_left hb21' hX₀]
        have h1 := (hX _ hXa).1
        have h2 := (hX _ hXb).2
        have h3 := Gn_ge n hn a b ha hab
        linarith
    _ ≤ Real.log (PhiN cfgW n : ℝ) := log_PhiN_ge hO T hb hs hv n

/-! ### 8. The error term is `O(√n)` -/

theorem En_le (n : ℕ) (hn : 1 ≤ n) : En n ≤ 42 * Real.sqrt n := by
  unfold En
  have hn' : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hsq : Real.sqrt n ^ 2 = n := Real.sq_sqrt (by positivity)
  have h1 : Real.log ((60 * n + 1 : ℕ) : ℝ) ≤ 16 * Real.sqrt n := by
    push_cast
    have hpos : (0 : ℝ) < 60 * n + 1 := by positivity
    have hl : Real.log (60 * n + 1) ≤ 2 * Real.sqrt (60 * n + 1) := by
      have h := Real.log_le_sub_one_of_pos (Real.sqrt_pos.2 hpos)
      rw [Real.log_sqrt hpos.le] at h
      linarith
    have hs : Real.sqrt (60 * n + 1) ≤ 8 * Real.sqrt n := by
      rw [Real.sqrt_le_left (by positivity), mul_pow, hsq]
      nlinarith
    linarith
  have h2 : Chebyshev.theta ((Nat.sqrt (160 * n + 2) : ℕ) : ℝ) ≤ 26 * Real.sqrt n := by
    have h := Chebyshev.theta_le_log4_mul_x (Nat.cast_nonneg (Nat.sqrt (160 * n + 2)))
    have hl4 : Real.log 4 ≤ 2 := by
      have : Real.log 4 = 2 * Real.log 2 := by
        rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]
        norm_num
      linarith [Real.log_two_lt_d9]
    have hs1 : ((Nat.sqrt (160 * n + 2) : ℕ) : ℝ) ≤ Real.sqrt ((160 * n + 2 : ℕ) : ℝ) :=
      Real.nat_sqrt_le_real_sqrt
    have hs2 : Real.sqrt ((160 * n + 2 : ℕ) : ℝ) ≤ 13 * Real.sqrt n := by
      push_cast
      rw [Real.sqrt_le_left (by positivity), mul_pow, hsq]
      nlinarith
    calc Chebyshev.theta ((Nat.sqrt (160 * n + 2) : ℕ) : ℝ)
        ≤ Real.log 4 * ((Nat.sqrt (160 * n + 2) : ℕ) : ℝ) := h
      _ ≤ 2 * (13 * Real.sqrt n) :=
          mul_le_mul hl4 (hs1.trans hs2) (Nat.cast_nonneg _) (by norm_num)
      _ = 26 * Real.sqrt n := by ring
  linarith

end DenomGrowth

open DenomGrowth in
theorem DenomGrowth_proof (hPNT : Zeta2.PNT_Stmt) (hO : Stmt_OmegaPhi0) (hT : Stmt_PhiTable)
    (hD : Stmt_PhiData) : Stmt_DenomGrowth := by
  have hb := hD.bounds
  have hs := hD.sorted
  have hb' : ∀ e ∈ phiTable, 0 ≤ e.a ∧ e.a < e.b ∧ e.b ≤ 1 := fun e he => (hb e he).2.2
  -- the certified sum `1341 - phiSumQ < 748`
  have hsumQ : (1341 : ℚ) - phiSumQ phiTable 60 20 < 748 := by
    have h := hD.sum
    have hmu : mu cfgW (cfgW.q - cfgW.r) = 60 := by decide
    rw [hmu, muSum_cfgW] at h
    unfold C2hi at h
    exact_mod_cast h
  have hsumR : (1341 : ℝ) - ((phiSumQ phiTable 60 20 : ℚ) : ℝ) < 748 := by exact_mod_cast hsumQ
  rw [phiSumQ_cast] at hsumR
  obtain ⟨P, hP⟩ : ∃ P, P = tabL phiTable (fun a b => ((1 / a - 1 / b : ℚ) : ℝ)) := ⟨_, rfl⟩
  obtain ⟨W, hW⟩ : ∃ W, W = tabL phiTable (fun a b => ((1 / a + 1 / b : ℚ) : ℝ)) := ⟨_, rfl⟩
  obtain ⟨V, hV⟩ : ∃ V, V = tabL phiTable (fun _ _ => (1 : ℝ)) := ⟨_, rfl⟩
  rw [← hP] at hsumR
  have hW0 : 0 ≤ W := by
    have h := tabL_mono phiTable hb' (fun _ _ => (0 : ℝ))
      (fun a b => ((1 / a + 1 / b : ℚ) : ℝ)) (fun a b ha hab _ => by
        have ha0 : (0 : ℚ) < a := lt_of_lt_of_le (by norm_num) ha
        have hb0 : (0 : ℚ) < b := ha0.trans hab
        have : (0 : ℚ) ≤ 1 / a + 1 / b := by positivity
        exact_mod_cast this)
    rw [tabL_zero] at h
    rw [hW]
    exact h
  have hV0 : 0 ≤ V := by
    have h := tabL_mono phiTable hb' (fun _ _ => (0 : ℝ)) (fun _ _ => (1 : ℝ))
      (fun _ _ _ _ _ => zero_le_one)
    rw [tabL_zero] at h
    rw [hV]
    exact h
  obtain ⟨ε, hε⟩ : ∃ ε, ε = 748 - (1341 - P) := ⟨_, rfl⟩
  have hε0 : 0 < ε := by linarith
  have hW' : (1341 + W) ≠ 0 := by linarith
  obtain ⟨δ, hδ0, hδW⟩ : ∃ δ : ℝ, 0 < δ ∧ δ * (1341 + W) = ε / 4 :=
    ⟨ε / (4 * (1341 + W)), div_pos hε0 (by linarith), by field_simp⟩
  obtain ⟨X₀, hX₀0, hX₀⟩ := pnt_unif hPNT hδ0
  have hev : ∀ᶠ n : ℕ in atTop, 21 * X₀ + (56 * V / ε) ^ 2 + 1 ≤ (n : ℝ) :=
    tendsto_natCast_atTop_atTop.eventually_ge_atTop _
  filter_upwards [hev] with n hn
  have hsq0 : 0 ≤ (56 * V / ε) ^ 2 := sq_nonneg _
  have hn1 : 1 ≤ n := by
    have : (1 : ℝ) ≤ n := by linarith
    exact_mod_cast this
  -- numerator: `log Dprod ≤ (1 + δ) 1341 n`
  have hnum := log_Dprod_le n δ X₀ (fun x hx => (hX₀ x hx).2) (by linarith)
  -- denominator: `log Φ_n ≥ n P - δ n W - E_n V`
  have hden := log_PhiN_ge' hO phiTable hb hs hT n hn1 δ X₀ hX₀0
    (fun x hx => ⟨(hX₀ x hx).1, (Chebyshev.theta_le_psi x).trans (hX₀ x hx).2⟩) (by linarith)
  rw [← hP, ← hW, ← hV] at hden
  -- the error term: `E_n V ≤ (3/4) ε n`
  have hE := En_le n hn1
  have hsqrt : 56 * V / ε ≤ Real.sqrt n := by
    have h := Real.sqrt_le_sqrt (show (56 * V / ε) ^ 2 ≤ (n : ℝ) by linarith)
    rwa [Real.sqrt_sq (div_nonneg (by linarith) hε0.le)] at h
  have hVE : En n * V ≤ 3 / 4 * ε * n := by
    have h1 : En n * V ≤ 42 * Real.sqrt n * V := mul_le_mul_of_nonneg_right hE hV0
    have h2 : 56 * V ≤ ε * Real.sqrt n := by
      rw [div_le_iff₀ hε0] at hsqrt
      linarith
    have h3 : Real.sqrt n * Real.sqrt n = n := Real.mul_self_sqrt (Nat.cast_nonneg n)
    have h4 := mul_le_mul_of_nonneg_left h2 (Real.sqrt_nonneg (n : ℝ))
    nlinarith
  -- conclusion
  have hDpos : (0 : ℝ) < (Dprod cfgW n : ℝ) := by exact_mod_cast Dprod_pos cfgW n
  have hPpos : (0 : ℝ) < (PhiN cfgW n : ℝ) := by exact_mod_cast PhiN_pos cfgW n
  have hDelta : ((Delta cfgW n : ℚ) : ℝ) = (Dprod cfgW n : ℝ) / (PhiN cfgW n : ℝ) := by
    unfold Delta
    push_cast
    rfl
  have hC2 : ((C2hi : ℚ) : ℝ) = 748 := by unfold C2hi; norm_num
  rw [hDelta, hC2, ← Real.log_le_iff_le_exp (div_pos hDpos hPpos),
    Real.log_div hDpos.ne' hPpos.ne']
  calc Real.log (Dprod cfgW n : ℝ) - Real.log (PhiN cfgW n : ℝ)
      ≤ (1 + δ) * 1341 * n - ((n : ℝ) * P - δ * n * W - En n * V) := by linarith
    _ = 748 * n - ε * n + (δ * (1341 + W)) * n + En n * V := by rw [hε]; ring
    _ = 748 * n - ε * n + ε / 4 * n + En n * V := by rw [hδW]
    _ ≤ 748 * n := by linarith

end ZetaWindow

end
