module

public import Zeta2Lean.Window.Statements

@[expose] public section

set_option linter.style.header false
set_option linter.style.longLine false

/-!
# `riemannZeta s = ∑_{m ≥ 1} m^{-s}` for `s ≥ 2` (glue to Mathlib)

**Task.** Prove `Stmt_ZetaReal`: for `s : ℕ`, `2 ≤ s`, `riemannZeta (s : ℂ) = ((zetaR s : ℝ) : ℂ)`.

**Proof.** Mathlib's `zeta_eq_tsum_one_div_nat_add_one_cpow` (valid for `1 < re s`) gives
`riemannZeta s = ∑' m, 1 / (m + 1 : ℂ) ^ (s : ℂ)`; `Complex.cpow_natCast` turns the complex power
into a natural power and `Complex.ofReal_tsum` moves the cast inside the sum.

**Status: complete** (proved by the architect).
-/

open Filter Topology Finset

noncomputable section

namespace ZetaWindow

theorem ZetaReal_proof : Stmt_ZetaReal := by
  intro s hs
  have h1 : 1 < (s : ℂ).re := by
    rw [Complex.natCast_re]
    exact_mod_cast (by omega : 1 < s)
  rw [zeta_eq_tsum_one_div_nat_add_one_cpow h1, zetaR, Complex.ofReal_tsum]
  refine tsum_congr fun m => ?_
  rw [Complex.cpow_natCast]
  push_cast
  ring

end ZetaWindow

end
