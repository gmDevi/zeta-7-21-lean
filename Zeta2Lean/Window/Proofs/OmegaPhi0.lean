import Zeta2Lean.Window.Statements

set_option linter.style.header false
set_option linter.style.longLine false

/-!
# `ω_{k,p}(n) = φ₀(n/p, (k-1)/p)` (JTNB (8.9) versus p. 283)

**Statement.** `Stmt_OmegaPhi0` (no hypotheses): for every configuration `c` and `n, p, k` with
`0 < p`, `omegaKP c n p k = phi0 c (n/p) ((k-1)/p)`.

**Informal proof.**  Term by term.  With `x = n/p`, `y = (k-1)/p`, `h₀ = η₀ n + 2`, `h_j = η_j n + 1`:
`(k-1)/p = y`, `(h₀-k-1)/p = η₀x - y`, `(k-h_j)/p = y - η_j x`, `(h₀-h_j-k)/p = (η₀-η_j)x - y`,
`(h_j-1)/p = η_j x`, `(h₀-2h_j)/p = (η₀-2η_j)x`, and for an integer `m`,
`m / p` (Euclidean division in `ℤ`) `= ⌊(m : ℚ)/p⌋` (`Rat.floor_intCast_div_natCast`; this holds
for every `p : ℕ`, also `p = 0`, where both sides are `0`).  Both sides are sums over the same index
sets, so it suffices to rewrite each of the six kinds of `ℤ`-quotients of `omegaKP` (eight
rewrites: five in the sum over `j ≤ r`, three in the sum over `j > r`) into the corresponding floor
of `phi0` (`ediv_eq_floor`, whose side condition is a ring identity in `ℚ`, linear in `p⁻¹`, so it
needs no `p ≠ 0`).

**Numerical check.** `python/window_mirror.py`, section "Stmt_OmegaPhi0": 1500 random `(n, p, k)` for
`cfgW` and the Theorem 3 configuration, exact.

**Status: proved** (complete; axioms: `propext`, `Classical.choice`, `Quot.sound`).
-/

open Filter Topology Finset

noncomputable section

namespace ZetaWindow

namespace OmegaPhi0

/-- Euclidean division of an integer by a natural number is the floor of the rational quotient,
stated with an arbitrary rational `z` equal to that quotient (so that `rw` can produce the exact
floor argument that occurs in `phi0`). -/
theorem ediv_eq_floor (m : ℤ) (p : ℕ) (z : ℚ) (hz : (m : ℚ) / p = z) : m / (p : ℤ) = ⌊z⌋ := by
  rw [← hz, Rat.floor_intCast_div_natCast]

end OmegaPhi0

open OmegaPhi0 in
theorem OmegaPhi0_proof : Stmt_OmegaPhi0 := by
  intro c n p k _hp
  unfold omegaKP phi0
  congr 1
  · -- the `r` indices `j ≤ r` (polynomial bricks `P_j`, `Q_j` and the numerator `(t+1)_{h₀-1}^r`)
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [ediv_eq_floor ((k : ℤ) - 1) p (((k : ℚ) - 1) / p)
        (by push_cast; ring),
      ediv_eq_floor ((c.h0 n : ℤ) - k - 1) p ((c.eta0 : ℚ) * ((n : ℚ) / p) - ((k : ℚ) - 1) / p)
        (by push_cast [Config.h0]; ring),
      ediv_eq_floor ((k : ℤ) - c.h n j) p (((k : ℚ) - 1) / p - (c.eta j : ℚ) * ((n : ℚ) / p))
        (by push_cast [Config.h]; ring),
      ediv_eq_floor ((c.h0 n : ℤ) - c.h n j - k) p
        (((c.eta0 : ℚ) - c.eta j) * ((n : ℚ) / p) - ((k : ℚ) - 1) / p)
        (by push_cast [Config.h0, Config.h]; ring),
      ediv_eq_floor ((c.h n j : ℤ) - 1) p ((c.eta j : ℚ) * ((n : ℚ) / p))
        (by push_cast [Config.h]; ring)]
  · -- the `q - r` indices `j > r` (rational bricks `S_j`)
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [ediv_eq_floor ((c.h0 n : ℤ) - 2 * c.h n j) p (((c.eta0 : ℚ) - 2 * c.eta j) * ((n : ℚ) / p))
        (by push_cast [Config.h0, Config.h]; ring),
      ediv_eq_floor ((k : ℤ) - c.h n j) p (((k : ℚ) - 1) / p - (c.eta j : ℚ) * ((n : ℚ) / p))
        (by push_cast [Config.h]; ring),
      ediv_eq_floor ((c.h0 n : ℤ) - c.h n j - k) p
        (((c.eta0 : ℚ) - c.eta j) * ((n : ℚ) / p) - ((k : ℚ) - 1) / p)
        (by push_cast [Config.h0, Config.h]; ring)]

end ZetaWindow

end
