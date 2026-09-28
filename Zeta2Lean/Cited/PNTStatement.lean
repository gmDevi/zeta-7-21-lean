module

public import Mathlib

@[expose] public section

/-!
# Zeta2Lean.Cited.PNTStatement — the prime number theorem, as a statement

`Zeta2.PNT_Stmt` is the prime number theorem `ψ(x)/x → 1` for Mathlib's second Chebyshev function
`Chebyshev.psi`.  `Zeta2Lean/Cited/PNT.lean` proves it (`Zeta2.PNT_proof`) from the vendored
Wiener–Ikehara theorem, and `Zeta2Lean/Window/Proofs/DenomGrowth.lean` uses it for the growth of the
denominators.  The statement has a module of its own, importing only Mathlib, so that the window
statements (`Zeta2Lean/Window/Statements.lean`) do not import the vendored files.

The definition, its name and its namespace are those of `Zeta2Lean/Statements.lean` in the two
2-adic repositories this one was copied from (https://github.com/gmDevi/zeta2-7-9-11-lean and
https://github.com/gmDevi/zeta2-7-9-lean).
-/

open Filter Topology

noncomputable section

namespace Zeta2

/-- **Prime number theorem**: `ψ(x) / x → 1`, where `ψ = Chebyshev.psi` is the second Chebyshev
function (`ψ n = log lcm(1,…,n)`, Mathlib `Chebyshev.psi_eq_log_lcmUpto`).  Proved in
`Zeta2Lean/Cited/PNT.lean` (`Zeta2.PNT_proof`). -/
def PNT_Stmt : Prop :=
  Tendsto (fun x : ℝ => Chebyshev.psi x / x) atTop (𝓝 1)

end Zeta2

end
