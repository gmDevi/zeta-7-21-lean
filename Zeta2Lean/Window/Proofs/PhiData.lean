module

public import Zeta2Lean.Window.Statements

@[expose] public section

set_option linter.style.header false
set_option linter.style.longLine false

/-!
# Closed facts about the φ-table (decidable; docs/window/proof.md §2)

**Task.** Prove `Stmt_PhiData`: the 2602 pieces of `phiTable` (`Window/PhiTable.lean`) are proper
subintervals of `[0, 1]` with positive denominators, listed in increasing order and pairwise
disjoint (`IsChain (e.b ≤ f.a)`), and the certified integral satisfies
`muSum cfgW - phiSumQ phiTable 60 20 = 1341 - 593.5146378485… = 747.4853… < C2hi = 748`.

**Proof.** Everything is a closed computation checked by the kernel (`decide +kernel`), arranged so
that the kernel only sees small natural numbers:
* `bounds`, `sorted`: the rational comparisons `an/ad < bn/bd`, `bn/bd ≤ 1`, `e.b ≤ f.a` are
  cross-multiplied into `ℕ` (`bounds_of_nat`, `le_of_nat`), and the `ℕ` forms are decided.
* `sum`: an integer fixed-point lower bound.  With `scale = 10¹²`, `fxTerm e m = ⌊scale (bn ad - an bd)
  / ((an + m ad)(bn + m bd))⌋ ≤ scale (1/(a+m) - 1/(b+m))` and similarly `fx0` for the `m = 0` term
  (`Nat.cast_div_le`), so `fxSum T M K ≤ scale · phiSumQ T M K` for every table with valid bounds
  (`fxSum_le`).  The kernel evaluates `fxSum phiTable 60 20 = 593514637594143 > 593.5146 · 10¹²`
  (`fxSum_phiTable`), whence `phiSumQ phiTable 60 20 > 593.5146` (`phiSumQ_phiTable_gt`) and
  `1341 - phiSumQ < 747.4854 < 748`.  The truncation loss is `2.5 · 10⁻⁷`; the exact value is
  `phiSumQ = 593.5146378485069…` (3943-bit numerator).

The first version decided the exact rational statement directly (`decide +kernel`, about 135 s of
kernel time for `sum`, 55k additions of rationals with 4000-bit denominators; 130–275 s per file).
The fixed-point version needs about 11 s of kernel time for `sum` and elaborates the whole file in
16–50 s, depending on the machine load.  `python/window_mirror.py`, section
"Stmt_PhiTable … Stmt_PhiData", recomputes the same numbers exactly.

**Status: complete** (axioms `propext`, `Classical.choice`, `Quot.sound` only).
-/

open Filter Topology Finset

noncomputable section

namespace ZetaWindow

namespace PhiData

/-! ### The two order facts, checked on numerators and denominators in `ℕ` -/

/-- `bounds` from its cross-multiplied form in `ℕ`. -/
theorem bounds_of_nat {e : Piece}
    (h : 0 < e.ad ∧ 0 < e.bd ∧ e.an * e.bd < e.bn * e.ad ∧ e.bn ≤ e.bd) :
    0 < e.ad ∧ 0 < e.bd ∧ 0 ≤ e.a ∧ e.a < e.b ∧ e.b ≤ 1 := by
  obtain ⟨had, hbd, hlt, hle⟩ := h
  have had' : (0 : ℚ) < e.ad := by exact_mod_cast had
  have hbd' : (0 : ℚ) < e.bd := by exact_mod_cast hbd
  refine ⟨had, hbd, by unfold Piece.a; positivity, ?_, ?_⟩
  · unfold Piece.a Piece.b
    rw [div_lt_div_iff₀ had' hbd']
    exact_mod_cast hlt
  · unfold Piece.b
    rw [div_le_one₀ hbd']
    exact_mod_cast hle

/-- `e.b ≤ f.a` from its cross-multiplied form in `ℕ`. -/
theorem le_of_nat {e f : Piece} (h : 0 < e.bd ∧ 0 < f.ad ∧ e.bn * f.ad ≤ f.an * e.bd) :
    e.b ≤ f.a := by
  obtain ⟨hbd, had, hle⟩ := h
  unfold Piece.a Piece.b
  rw [div_le_div_iff₀ (by exact_mod_cast hbd) (by exact_mod_cast had)]
  exact_mod_cast hle

set_option maxRecDepth 100000 in
theorem bounds_nat :
    ∀ e ∈ phiTable, 0 < e.ad ∧ 0 < e.bd ∧ e.an * e.bd < e.bn * e.ad ∧ e.bn ≤ e.bd := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem sorted_nat :
    phiTable.IsChain (fun e f => 0 < e.bd ∧ 0 < f.ad ∧ e.bn * f.ad ≤ f.an * e.bd) := by
  decide +kernel

theorem phiTable_bounds :
    ∀ e ∈ phiTable, 0 < e.ad ∧ 0 < e.bd ∧ 0 ≤ e.a ∧ e.a < e.b ∧ e.b ≤ 1 :=
  fun e he => bounds_of_nat (bounds_nat e he)

theorem phiTable_sorted : phiTable.IsChain (fun e f => e.b ≤ f.a) :=
  sorted_nat.imp fun _ _ h => le_of_nat h

/-! ### An integer fixed-point lower bound for `phiSumQ` -/

/-- Fixed-point scale `10¹²` of the integer lower bound for `phiSumQ`. -/
def scale : ℕ := 1000000000000

/-- `bn·ad - an·bd`, the numerator of `b - a = (bn·ad - an·bd)/(ad·bd)`. -/
def gapNum (e : Piece) : ℕ := e.bn * e.ad - e.an * e.bd

/-- `⌊scale · (1/(a+m) - 1/(b+m))⌋` in `ℕ`, using
`1/(a+m) - 1/(b+m) = (bn·ad - an·bd) / ((an + m·ad)(bn + m·bd))`. -/
def fxTerm (e : Piece) (m : ℕ) : ℕ :=
  scale * gapNum e / ((e.an + m * e.ad) * (e.bn + m * e.bd))

/-- `⌊scale · (1/a - 1/b)⌋ = ⌊scale · (bn·ad - an·bd)/(an·bn)⌋` if `1/M ≤ a`, else `0`. -/
def fx0 (M : ℕ) (e : Piece) : ℕ :=
  if 1 / (M : ℚ) ≤ e.a then scale * gapNum e / (e.an * e.bn) else 0

/-- Integer lower bound for `scale · phiWeight M K e`. -/
def fxWeight (M K : ℕ) (e : Piece) : ℕ :=
  e.v * (fx0 M e + ∑ m ∈ Icc 1 K, fxTerm e m)

/-- Integer lower bound for `scale · phiSumQ T M K`. -/
def fxSum (T : List Piece) (M K : ℕ) : ℕ :=
  (T.map (fxWeight M K)).sum

theorem gapNum_cast {e : Piece} (had : 0 < e.ad) (hbd : 0 < e.bd) (hab : e.a < e.b) :
    (gapNum e : ℚ) = (e.bn : ℚ) * e.ad - (e.an : ℚ) * e.bd := by
  have hlt : e.an * e.bd < e.bn * e.ad := by
    have h := hab
    unfold Piece.a Piece.b at h
    rw [div_lt_div_iff₀ (by exact_mod_cast had) (by exact_mod_cast hbd)] at h
    exact_mod_cast h
  unfold gapNum
  rw [Nat.cast_sub hlt.le]
  push_cast
  ring

theorem fxTerm_le {e : Piece} (had : 0 < e.ad) (hbd : 0 < e.bd) (hab : e.a < e.b) {m : ℕ}
    (hm : 1 ≤ m) : (fxTerm e m : ℚ) ≤ (scale : ℚ) * (1 / (e.a + m) - 1 / (e.b + m)) := by
  unfold fxTerm
  refine Nat.cast_div_le.trans (le_of_eq ?_)
  have hm' : (0 : ℚ) < m := by exact_mod_cast hm
  have had' : (0 : ℚ) < e.ad := by exact_mod_cast had
  have hbd' : (0 : ℚ) < e.bd := by exact_mod_cast hbd
  have hA : (0 : ℚ) < e.an + m * e.ad :=
    add_pos_of_nonneg_of_pos (Nat.cast_nonneg _) (mul_pos hm' had')
  have hB : (0 : ℚ) < e.bn + m * e.bd :=
    add_pos_of_nonneg_of_pos (Nat.cast_nonneg _) (mul_pos hm' hbd')
  rw [Nat.cast_mul, gapNum_cast had hbd hab]
  push_cast
  unfold Piece.a Piece.b
  rw [div_add' _ _ _ had'.ne', div_add' _ _ _ hbd'.ne', one_div_div, one_div_div,
    div_sub_div _ _ hA.ne' hB.ne', mul_div_assoc']
  congr 1
  ring

theorem fx0_le {M : ℕ} (hM : 0 < M) {e : Piece} (had : 0 < e.ad) (hbd : 0 < e.bd)
    (hab : e.a < e.b) :
    (fx0 M e : ℚ) ≤ (scale : ℚ) * (if 1 / (M : ℚ) ≤ e.a then 1 / e.a - 1 / e.b else 0) := by
  unfold fx0
  split_ifs with h
  · have hM' : (0 : ℚ) < M := by exact_mod_cast hM
    have ha : 0 < e.a := lt_of_lt_of_le (by positivity) h
    have hb : 0 < e.b := ha.trans hab
    have han : 0 < e.an := by
      rcases Nat.eq_zero_or_pos e.an with h0 | h0
      · simp [Piece.a, h0] at ha
      · exact h0
    have hbn : 0 < e.bn := by
      rcases Nat.eq_zero_or_pos e.bn with h0 | h0
      · simp [Piece.b, h0] at hb
      · exact h0
    have han' : (0 : ℚ) < e.an := by exact_mod_cast han
    have hbn' : (0 : ℚ) < e.bn := by exact_mod_cast hbn
    refine Nat.cast_div_le.trans (le_of_eq ?_)
    rw [Nat.cast_mul, gapNum_cast had hbd hab]
    push_cast
    unfold Piece.a Piece.b
    rw [one_div_div, one_div_div, div_sub_div _ _ han'.ne' hbn'.ne', mul_div_assoc']
    congr 1
    ring
  · simp

theorem fxWeight_le {M K : ℕ} (hM : 0 < M) {e : Piece} (had : 0 < e.ad) (hbd : 0 < e.bd)
    (hab : e.a < e.b) : (fxWeight M K e : ℚ) ≤ (scale : ℚ) * phiWeight M K e := by
  have h0 := fx0_le hM had hbd hab
  have hs : ∑ m ∈ Icc 1 K, (fxTerm e m : ℚ) ≤
      ∑ m ∈ Icc 1 K, (scale : ℚ) * (1 / (e.a + m) - 1 / (e.b + m)) :=
    Finset.sum_le_sum fun m hm => fxTerm_le had hbd hab (Finset.mem_Icc.1 hm).1
  rw [← Finset.mul_sum] at hs
  unfold fxWeight phiWeight
  push_cast
  calc (e.v : ℚ) * ((fx0 M e : ℚ) + ∑ m ∈ Icc 1 K, (fxTerm e m : ℚ))
      ≤ (e.v : ℚ) * ((scale : ℚ) * (if 1 / (M : ℚ) ≤ e.a then 1 / e.a - 1 / e.b else 0) +
          (scale : ℚ) * ∑ m ∈ Icc 1 K, (1 / (e.a + m) - 1 / (e.b + m))) :=
        mul_le_mul_of_nonneg_left (add_le_add h0 hs) (Nat.cast_nonneg _)
    _ = _ := by ring

/-- Soundness of the fixed-point bound: `fxSum T M K ≤ scale · phiSumQ T M K`. -/
theorem fxSum_le {M K : ℕ} (hM : 0 < M) (T : List Piece)
    (hT : ∀ e ∈ T, 0 < e.ad ∧ 0 < e.bd ∧ 0 ≤ e.a ∧ e.a < e.b ∧ e.b ≤ 1) :
    (fxSum T M K : ℚ) ≤ (scale : ℚ) * phiSumQ T M K := by
  induction T with
  | nil => simp [fxSum, phiSumQ]
  | cons e T ih =>
    have he := hT e (by simp)
    have hT' : ∀ f ∈ T, 0 < f.ad ∧ 0 < f.bd ∧ 0 ≤ f.a ∧ f.a < f.b ∧ f.b ≤ 1 :=
      fun f hf => hT f (by simp [hf])
    have ih' := ih hT'
    simp only [fxSum, phiSumQ, List.map_cons, List.sum_cons, Nat.cast_add] at ih' ⊢
    rw [mul_add]
    exact add_le_add (fxWeight_le hM he.1 he.2.1 he.2.2.2.1) ih'

set_option maxRecDepth 100000 in
/-- The kernel computation (`fxSum phiTable 60 20 = 593514637594143`). -/
theorem fxSum_phiTable : 5935146 * 10 ^ 8 < fxSum phiTable 60 20 := by
  decide +kernel

/-- The certified value `phiSumQ phiTable 60 20 > 593.5146`, i.e. `C₂ ≤ 1341 - 593.5146 = 747.4854`. -/
theorem phiSumQ_phiTable_gt : (5935146 / 10000 : ℚ) < phiSumQ phiTable 60 20 := by
  have h1 : ((5935146 * 10 ^ 8 : ℕ) : ℚ) < (fxSum phiTable 60 20 : ℚ) := by
    exact_mod_cast fxSum_phiTable
  have h2 := fxSum_le (M := 60) (K := 20) (by norm_num) phiTable phiTable_bounds
  have hS : (scale : ℚ) = 10 ^ 12 := by norm_num [scale]
  rw [hS] at h2
  push_cast at h1
  linarith

end PhiData

theorem PhiData_proof : Stmt_PhiData where
  bounds := PhiData.phiTable_bounds
  sorted := PhiData.phiTable_sorted
  sum := by
    have hmu : mu cfgW (cfgW.q - cfgW.r) = 60 := by decide
    rw [hmu, muSum_cfgW]
    have h := PhiData.phiSumQ_phiTable_gt
    unfold C2hi
    push_cast
    linarith

end ZetaWindow

end
