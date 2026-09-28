module

public import Zeta2Lean.Window.Main

@[expose] public section

/-!
# Proof of the statement in `Challenge.lean`

`ZetaWindow.zeta_7_to_21_not_all_rational` (`Zeta2Lean/Window/Main.lean`) is the main theorem of
this repository, and its type is the statement of `Challenge.lean`. That statement uses only
Mathlib's `riemannZeta`. Comparator checks that the two statements are identical, and that the
proof uses only the axioms `propext`, `Classical.choice` and `Quot.sound`.
-/

namespace ZetaWindow

/-- **At least one of ζ(7), ζ(9), …, ζ(21) is irrational** (the statement of `Challenge.lean`). -/
theorem zeta_7_to_21_not_all_rational_palomar :
    ¬ ∀ k ∈ ({7, 9, 11, 13, 15, 17, 19, 21} : Finset ℕ),
      ∃ q : ℚ, riemannZeta (k : ℂ) = (q : ℂ) :=
  zeta_7_to_21_not_all_rational

end ZetaWindow
