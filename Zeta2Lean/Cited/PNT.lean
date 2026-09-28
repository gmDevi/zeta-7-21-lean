module

public import Zeta2Lean.Cited.PNTStatement
public import Zeta2Lean.Cited.Vendor.PNT.WienerIkehara

@[expose] public section

/-!
# Zeta2Lean.Cited.PNT — the prime number theorem `PNT_Stmt`, proved

The prime number theorem is used by the growth bound of the denominators
(`Zeta2Lean/Window/Proofs/DenomGrowth.lean`).  This file proves it from the Wiener–Ikehara
theorem:

* `Stmt_WienerIkehara` — the theorem `WienerIkehara.tendsto_sum_div` of mathlib4 PR #43238 with
  its hypothesis class unbundled;
* `WienerIkehara_proof` — the vendored theorem applied field by field;
* `tendsto_residueClass_sum_div_of_WI`, `tendsto_residueClass_sum_div_atTop_of_WI`,
  `pnt_of_stmts` — `WeakPNT.lean` of mathlib4 PR #43238 (head `78e1b2bbd0`, Apache 2.0) with the
  Wiener–Ikehara theorem taken as a hypothesis;
* `PNT_proof : PNT_Stmt`.

The mathematical work is in the two vendored files `Cited/Vendor/PNT/SchwartzCompactSupport.lean`
(Terence Tao) and `Cited/Vendor/PNT/WienerIkehara.lean` (the PrimeNumberTheoremAnd contributors),
Apache 2.0 (see `LICENSE` there), with their copyright headers, authors and provenance notes kept
verbatim.  The vendored files and the declarations of this file are identical to those of the
2-adic repositories this one was copied from (https://github.com/gmDevi/zeta2-7-9-11-lean,
https://github.com/gmDevi/zeta2-7-9-lean; there the statements and proofs of this file are in
`Cited/Statements.lean`, `Cited/Proofs/WienerIkehara.lean`, `Cited/Assembly.lean` and
`Cited/Main.lean`, respectively in `Cited/PNT.lean`).  `PNT_Stmt` is defined in
`Zeta2Lean/Cited/PNTStatement.lean`.
-/

open Filter Topology Finset

noncomputable section

namespace Zeta2.Cited

/-- **Wiener–Ikehara Tauberian theorem** (mathlib4 PR #43233/#43238,
`WienerIkehara.tendsto_sum_div`, adapted from PrimeNumberTheoremAnd; the fields of the class
`WienerIkehara` in the same order: `f, C, bound, A, hA, G, hG, hG', hf, hpos`).
Let `f : ℕ → ℝ` be non-negative with the Chebyshev-type bound `∑_{i<n} |f i| ≤ C n`, whose
`L`-series converges for real `σ > 1` and, after subtracting `A/(s-1)`, extends continuously
(as `G`) to the closed half-plane `re s ≥ 1`.  Then `(∑_{n ≤ x} f n) / x → A`.
(`LSeries` ignores `f 0`; the sum includes it, which does not change the limit.) -/
def Stmt_WienerIkehara : Prop :=
  ∀ (f : ℕ → ℝ) (C A : ℝ) (G : ℂ → ℂ),
    (∀ n : ℕ, ∑ i ∈ range n, |f i| ≤ C * n) →
    0 ≤ A →
    ContinuousOn G {s | 1 ≤ s.re} →
    Set.EqOn G (fun s ↦ LSeries (fun n ↦ (f n : ℂ)) s - (A : ℂ) / (s - 1)) {s | 1 < s.re} →
    (∀ σ : ℝ, 1 < σ → LSeriesSummable (fun n ↦ (f n : ℂ)) σ) →
    0 ≤ f →
    Tendsto (fun x : ℝ ↦ (∑ n ∈ Icc 0 ⌊x⌋₊, f n) / x) atTop (𝓝 A)

/-- **Wiener–Ikehara** (vendored from mathlib4 PR #43238, `WienerIkehara.tendsto_sum_div`). -/
theorem WienerIkehara_proof : Stmt_WienerIkehara := by
  intro f C A G hbound hA hG hG' hf hpos
  exact @WienerIkehara.tendsto_sum_div
    { f := f, C := C, bound := hbound, A := A, hA := hA, G := G, hG := hG, hG' := hG', hf := hf,
      hpos := hpos }

section PNT

open ArithmeticFunction.vonMangoldt Chebyshev Real

/-- Wiener–Ikehara for the von Mangoldt function restricted to the residue class `a` mod `q`:
the average of `residueClass a` over `[0, x]` tends to `(q.totient)⁻¹` (mathlib4 PR #43238,
`tendsto_residueClass_sum_div`, with the Wiener–Ikehara theorem as the hypothesis `hWI`). -/
theorem tendsto_residueClass_sum_div_of_WI (hWI : Stmt_WienerIkehara) {q : ℕ} [NeZero q]
    {a : ZMod q} (ha : IsUnit a) :
    Tendsto (fun x : ℝ ↦ (∑ n ∈ Icc 0 ⌊x⌋₊, residueClass a n) / x) atTop
      (𝓝 ((q.totient : ℝ)⁻¹)) := by
  refine hWI (residueClass a) (log 4 + 4) (q.totient : ℝ)⁻¹ (LFunctionResidueClassAux a)
    (fun N => ?_) (by positivity) (continuousOn_LFunctionResidueClassAux a) (fun s hs => ?_)
    (fun σ hσ => ?_) (residueClass_nonneg a)
  · calc
      _ ≤ ∑ i ∈ range N, Λ i := by
        simp_rw [abs_of_nonneg (residueClass_nonneg _ _)]
        grw [residueClass_le]
      _ ≤ (log 4 + 4) * N := by
        rcases eq_or_ne N 0 with rfl | h
        · simp
        grw [Nat.range_eq_Icc_zero_sub_one _ h, (by simp : N - 1 = ⌊(N : ℝ) - 1⌋₊),
          ← psi_eq_sum_Icc, psi_le_const_mul_self <| sub_nonneg_of_le <|
          Nat.one_le_cast_iff_ne_zero.mpr h, (by linarith : (N : ℝ) - 1 ≤ N)]
  · rw [eqOn_LFunctionResidueClassAux ha hs]
    push_cast
    ring
  · exact LSeriesSummable_of_abscissaOfAbsConv_lt_re <|
      (abscissaOfAbsConv_residueClass_le_one a).trans_lt <| mod_cast hσ

/-- The weak prime number theorem in arithmetic progressions, from Wiener–Ikehara (mathlib4 PR
#43238, `ArithmeticFunction.vonMangoldt.tendsto_residueClass_sum_div_atTop`). -/
theorem tendsto_residueClass_sum_div_atTop_of_WI (hWI : Stmt_WienerIkehara) {q a : ℕ}
    [NeZero q] (ha : a.Coprime q) (ha' : a < q) :
    Tendsto (fun x : ℝ ↦ (∑ n ∈ Icc 0 ⌊x⌋₊, if n % q = a then Λ n else 0) / x) atTop
      (𝓝 ((q.totient : ℝ)⁻¹)) := by
  apply (tendsto_residueClass_sum_div_of_WI hWI ((ZMod.isUnit_iff_coprime a q).mpr ha)).congr
  simp [residueClass, Set.indicator_apply, ZMod.natCast_eq_natCast_iff', Nat.mod_eq_of_lt ha']

/-- **The prime number theorem** `ψ(x)/x → 1`, from the Wiener–Ikehara theorem (the `q = 1`
case; mathlib4 PR #43238, `Chebyshev.tendsto_psi_div_atTop`). -/
theorem pnt_of_stmts (hWI : Stmt_WienerIkehara) : PNT_Stmt := by
  unfold PNT_Stmt
  simpa [Nat.mod_one, Nat.totient_one, psi_eq_sum_Icc] using
    tendsto_residueClass_sum_div_atTop_of_WI hWI (q := 1) (a := 0) (by simp) one_pos

end PNT

end Zeta2.Cited

namespace Zeta2

/-- **The prime number theorem** `ψ(x)/x → 1`, proved (Wiener–Ikehara, vendored from
mathlib4 PRs #43046/#43233/#43238). -/
theorem PNT_proof : PNT_Stmt :=
  Cited.pnt_of_stmts Cited.WienerIkehara_proof

end Zeta2

#print axioms Zeta2.PNT_proof
