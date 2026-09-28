import Mathlib

/-!
# At least one of ζ(7), ζ(9), …, ζ(21) is irrational

This is the statement to audit. It imports only Mathlib and uses no definition of this
repository: `riemannZeta` is Mathlib's Riemann zeta function, and for an integer `k ≥ 2` it is
`∑_{m ≥ 1} m^{-k}` (Mathlib's `zeta_nat_eq_tsum_of_gt_one`). The theorem says that the eight
numbers ζ(7), ζ(9), ζ(11), ζ(13), ζ(15), ζ(17), ζ(19), ζ(21) are not all rational, that is, at
least one of them is irrational. It does not say which one.

The best earlier result of this form that our literature search found is W. Zudilin's (Math. Notes
70 (2001), Theorem 2): at least one of ζ(7), ζ(9), …, ζ(35) is irrational. The proof follows
Zudilin's very-well-poised linear forms (J. Théor. Nombres Bordeaux 16 (2004), §8) with five
derivatives, the improvement Zudilin anticipated there (p. 286). The result has not been refereed,
and it was produced by AI agents under human direction. `README.md`, `docs/proof.md` and
`formalization.yaml` give the proof, the sources and how the work was produced.
-/

namespace ZetaWindow

/-- **At least one of ζ(7), ζ(9), ζ(11), ζ(13), ζ(15), ζ(17), ζ(19), ζ(21) is irrational**: it is
not the case that for every `k ∈ {7, 9, …, 21}` the value `riemannZeta k` equals (the image in
`ℂ` of) a rational number. -/
theorem zeta_7_to_21_not_all_rational_palomar :
    ¬ ∀ k ∈ ({7, 9, 11, 13, 15, 17, 19, 21} : Finset ℕ),
      ∃ q : ℚ, riemannZeta (k : ℂ) = (q : ℂ) := by
  sorry

end ZetaWindow
