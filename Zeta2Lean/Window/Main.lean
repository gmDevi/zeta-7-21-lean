import Zeta2Lean.Window.Assembly
import Zeta2Lean.Window.Proofs.ZetaReal
import Zeta2Lean.Window.Proofs.Criterion
import Zeta2Lean.Window.Proofs.PartialFractions
import Zeta2Lean.Window.Proofs.CoeffVanish
import Zeta2Lean.Window.Proofs.LinearForm
import Zeta2Lean.Window.Proofs.BrickIntegral
import Zeta2Lean.Window.Proofs.BrickValuation
import Zeta2Lean.Window.Proofs.LaurentSupport
import Zeta2Lean.Window.Proofs.LaurentIntegral
import Zeta2Lean.Window.Proofs.LaurentValuation
import Zeta2Lean.Window.Proofs.Harmonic
import Zeta2Lean.Window.Proofs.Lemma19
import Zeta2Lean.Window.Proofs.OmegaPhi0
import Zeta2Lean.Window.Proofs.PhiTable
import Zeta2Lean.Window.Proofs.PhiData
import Zeta2Lean.Window.Proofs.DenomGrowth
import Zeta2Lean.Window.Proofs.Lemma20Upper
import Zeta2Lean.Window.Proofs.AuxPrime
import Zeta2Lean.Cited.PNT

set_option linter.style.header false

/-!
# Zeta2Lean.Window.Main — at least one of `ζ(7), ζ(9), …, ζ(21)` is irrational

Wires the proofs of all statements into `main_of_stmts` (`Window/Assembly.lean`).

Dependency graph (see `BLUEPRINT_WINDOW.md`):
* `LinearForm ← PF, CoeffVanish (← PF)`
* `Lemma19 ← LaurentSupp, LaurentInt (← BrickInt, LaurentSupp), LaurentVal (← BrickVal), Harmonic`
* `DenomGrowth ← PNT (Zeta2Lean/Cited/PNT.lean), OmegaPhi0, PhiTable, PhiData`
* `L20Upper ← PF, CoeffVanish, LinearForm` (Theorem U of docs/proof.md: the analytic upper bound)
* `AuxPrime ← LaurentSupp, LaurentInt, LaurentVal, Harmonic` (Theorem N of docs/proof.md: the
  auxiliary-prime separation that replaces the nonvanishing half of Lemma 20)
* `ZetaReal`, `Criterion`

Two theorems, both depending only on the axioms `[propext, Classical.choice, Quot.sound]`
(`#print axioms` at the end of this file):
* `zeta_7_to_21_not_all_rational_of_L20Upper` takes the analytic upper bound `Stmt_L20Upper` as a
  hypothesis;
* `zeta_7_to_21_not_all_rational` is the main theorem, stated with Mathlib notions only; it supplies
  that hypothesis with `L20Upper_proof`.  `Solution.lean` restates it for Comparator.
-/

namespace ZetaWindow

/-- The prime number theorem `ψ(x)/x → 1`, proved in `Zeta2Lean/Cited/PNT.lean` (Wiener–Ikehara,
vendored from mathlib4 PRs #43046/#43233/#43238). -/
theorem PNT_window : Zeta2.PNT_Stmt :=
  Zeta2.Cited.pnt_of_stmts Zeta2.Cited.WienerIkehara_proof

/-- **Main theorem, modulo the analytic upper bound** (Theorem U of docs/proof.md, the upper half of
JTNB Lemma 20 for `r = 5` and `cfgW`).  If `|F̃_n| ≤ e^{-748.1 n}` eventually, then at least one of
`ζ(7), ζ(9), …, ζ(21)` is irrational.  (The nonvanishing half of Lemma 20 is replaced by the
arithmetic `Stmt_AuxPrime`.) -/
theorem zeta_7_to_21_not_all_rational_of_L20Upper (hU : Stmt_L20Upper) :
    ¬ ∀ k ∈ ({7, 9, 11, 13, 15, 17, 19, 21} : Finset ℕ), ∃ q : ℚ, riemannZeta (k : ℂ) = (q : ℂ) :=
  main_of_stmts ZetaReal_proof Criterion_proof
    (LinearForm_proof PF_proof (CoeffVanish_proof PF_proof))
    (Lemma19_proof LaurentSupp_proof (LaurentInt_proof BrickInt_proof LaurentSupp_proof)
      (LaurentVal_proof BrickVal_proof) Harmonic_proof)
    (DenomGrowth_proof PNT_window OmegaPhi0_proof PhiTable_proof PhiData_proof)
    hU
    (AuxPrime_proof LaurentSupp_proof (LaurentInt_proof BrickInt_proof LaurentSupp_proof)
      (LaurentVal_proof BrickVal_proof) Harmonic_proof)

/-- **Main theorem** (target statement, Mathlib notions only): at least one of
`ζ(7), ζ(9), ζ(11), ζ(13), ζ(15), ζ(17), ζ(19), ζ(21)` is irrational. -/
theorem zeta_7_to_21_not_all_rational :
    ¬ ∀ k ∈ ({7, 9, 11, 13, 15, 17, 19, 21} : Finset ℕ), ∃ q : ℚ, riemannZeta (k : ℂ) = (q : ℂ) :=
  zeta_7_to_21_not_all_rational_of_L20Upper
    (L20Upper_proof PF_proof (CoeffVanish_proof PF_proof)
      (LinearForm_proof PF_proof (CoeffVanish_proof PF_proof)))

end ZetaWindow

#print axioms ZetaWindow.main_of_stmts
#print axioms ZetaWindow.Fn_frequently_ne_zero
#print axioms ZetaWindow.PNT_window
#print axioms ZetaWindow.PhiData_proof
#print axioms ZetaWindow.ZetaReal_proof
#print axioms ZetaWindow.Criterion_proof
#print axioms ZetaWindow.Harmonic_proof
#print axioms ZetaWindow.OmegaPhi0_proof
#print axioms ZetaWindow.LaurentSupp_proof
#print axioms ZetaWindow.BrickInt_proof
#print axioms ZetaWindow.BrickVal_proof
#print axioms ZetaWindow.LaurentInt_proof
#print axioms ZetaWindow.LaurentVal_proof
#print axioms ZetaWindow.PF_proof
#print axioms ZetaWindow.CoeffVanish_proof
#print axioms ZetaWindow.LinearForm_proof
#print axioms ZetaWindow.Lemma19_proof
#print axioms ZetaWindow.zeta_7_to_21_not_all_rational_of_L20Upper
#print axioms ZetaWindow.zeta_7_to_21_not_all_rational
