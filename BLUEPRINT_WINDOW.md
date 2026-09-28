# Blueprint: at least one of ζ(7), ζ(9), …, ζ(21) is irrational

Lean 4 + Mathlib formalisation of the (new, unrefereed) window theorem of `docs/window/proof.md`
(first version, 2026-09-25), in the robust version `docs/proof.md` (2026-09-25; route R2 of its §6;
called `proof_v2` below and in the Lean docstrings). The published record for windows starting at
ζ(7) is {7, …, 35} (Zudilin, Math. Notes 70 (2001)). The proof runs Zudilin's very-well-poised forms of
JTNB 16 (2004) §8 with r = 5 derivatives, q = 23, η₀ = 160,
η = (47, 47, 47, 47, 48, 50, 50, 51, 52, …, 66). Lemma 20 (the asymptotics) is proved in JTNB only
for r = 3. Route R2 does not need it: an upper bound from pointwise estimates on a fixed contour
(Theorem U) and an arithmetic nonvanishing at auxiliary primes (Theorem N) replace it, so no
saddle-point analysis is left in the proof.

**Restatement of 2026-09-26 (restater).** The first blueprint had two `lemma20` gap statements,
`Stmt_L20Upper` and `Stmt_L20Nonzero` (`∃ᶠ n, F̃_n ≠ 0`). The second one needed the saddle-point
asymptotics (Olver, ω/π ∉ ℤ) and is replaced by the arithmetic `Stmt_AuxPrime` (Theorem N).
`Stmt_L20Upper` is unchanged (`C0lo = 748.1`) and is now proved informally by Theorem U. The
assembly derives the nonvanishing itself, under the rationality hypothesis, with Mathlib's Dirichlet
theorem. The main statement and every other `Stmt_*` are unchanged.

## Target (`Zeta2Lean/Window/Main.lean`), Mathlib notions only

```lean
theorem ZetaWindow.zeta_7_to_21_not_all_rational :
    ¬ ∀ k ∈ ({7, 9, 11, 13, 15, 17, 19, 21} : Finset ℕ), ∃ q : ℚ, riemannZeta (k : ℂ) = (q : ℂ)

theorem ZetaWindow.zeta_7_to_21_not_all_rational_of_L20Upper
    (hU : Stmt_L20Upper) : <same statement>
```

The statement uses only Mathlib's `riemannZeta`, so no project definition is trusted. If a definition
in `Window/Defs.lean` were unfaithful to JTNB, the theorem would still be the displayed one. Every
definition only has to make the `Stmt_*` true, and `python/window_mirror.py` checks that numerically.

**Status (2026-09-26): complete.** Every statement below is proved; `zeta_7_to_21_not_all_rational`
depends only on `[propext, Classical.choice, Quot.sound]`. `Solution.lean` restates it for Comparator
as `zeta_7_to_21_not_all_rational_palomar` (statement in `Challenge.lean`).

**The two new inputs (proof_v2 §2; both proved informally, both formalised):**
* `Stmt_L20Upper`: `∀ᶠ n, |F̃_n| ≤ e^{-748.1 n}` (Theorem U: `|F̃_n| ≤ K n^{16} e^{-750.618 n}` for
  every `n ≥ 1`; the true rate is `C₀ = 750.7116948339…`);
* `Stmt_AuxPrime`: for all large even `n` with `ℓ = 63n - 1` prime,
  `v_ℓ(A₀) < 0 ≤ v_ℓ(A_s)` (`s ∈ window`) (Theorem N: `v_ℓ(A₀) = -5` exactly).

**Proved inputs:** the prime number theorem `Zeta2.PNT_Stmt` (statement in
`Zeta2Lean/Cited/PNTStatement.lean`, proof in `Zeta2Lean/Cited/PNT.lean`, Wiener–Ikehara);
Dirichlet's theorem (Mathlib, `Nat.forall_exists_prime_gt_and_modEq`, used in `Window/Assembly.lean`).

## Architecture

```
Zeta2Lean/Window/Defs.lean        definitions (generic in Config = (r, q, η₀, η)) + proved API:
                                  admissible_cfgW, window_cfgW, muSum_cfgW, Delta_pos, …
Zeta2Lean/Window/PhiTable.lean    GENERATED data: the 2602 pieces of φ on (0,1) (python/window_phitable.py)
Zeta2Lean/Window/Statements.lean  one Stmt_X : Prop per lemma; MainStatement
Zeta2Lean/Window/Assembly.lean    main_of_stmts, Fn_frequently_ne_zero, Dirichlet step (complete, no sorry)
Zeta2Lean/Window/Proofs/*.lean    theorem X_proof (deps as hypotheses) : Stmt_X   (18 files; L20U/ holds helpers)
Zeta2Lean/Window/Main.lean        wiring, PNT from Cited/PNT.lean, the main theorems, #print axioms
Zeta2Lean/Cited/PNTStatement.lean Zeta2.PNT_Stmt (ψ(x)/x → 1), Mathlib only
Zeta2Lean/Cited/PNT.lean          its proof from the vendored Wiener–Ikehara theorem (Cited/Vendor/PNT/)
python/window_mirror.py           exact mirror of Defs.lean + numerical check of every Stmt (--aux: AuxPrime only)
python/window_phitable.py         independent φ-table generator (reproduces docs/window/vz.py exactly)
python/window_audit/              the auditor's independent recomputation (run_all.py; see STATUS_WINDOW.md)
python/window_audit/indep2/       second independent audit pass (run_indep2.py; see STATUS_WINDOW.md)
docs/proof.md                     proof_v2, the informal proof that the Lean development follows (route R2)
docs/window/                      proof.md (first version), certificates and engines of the informal proof
docs/window/refine/               the tracks behind proof_v2 (Theorem U, Theorem N, refined Lemma 19)
```

Proof files import only `Zeta2Lean.Window.Statements` (and, for `Lemma20Upper`, the helper modules
`Proofs/L20U/`). Their dependencies arrive as hypotheses, so every file can be elaborated on its own
with `scripts/check.sh`. The root `Zeta2Lean.lean` imports `Zeta2Lean.Window.Main`; `lake build`
(or `bash scripts/build.sh`) builds everything, including `Challenge` and `Solution`.

## The construction (Defs.lean, JTNB §8)

For `n ≥ 1`, `h₀ = η₀n + 2` and `h_j = η_j n + 1`. The rational function is
`R̃ = N_h (h₀+2t) (t+1)_{h₀-1}^r / ∏_j (t+h_j)_{h₀+1-2h_j}`
`= (h₀+2t) ∏_{j≤r} P_j Q_j ∏_{j>r} S_j`, a product of Nesterenko bricks (JTNB (7.3)).

| Lean | mathematics |
|---|---|
| `Rser c n y` | Taylor series `ε ↦ R̃(y+ε)` at a non-pole `y`, unreduced product (JTNB (8.2), (8.6)) |
| `term c n t`, `Fn c n` | `[ε^{r-1}] R̃(t+ε)` and `F̃_n = ∑'_{t≥0} term` (JTNB (8.4)/(8.6)) |
| `polyBrick`, `ratBrick` | brick expansions at `t = -k`; `ratBrick` carries the factor `(t+k)` of JTNB Lemmas 16 and 18 |
| `Gk c n k`, `B c n j k` | `G_k = ε^{q-r} R̃(-k+ε)` (brick product) and `B_{j,k} = [ε^{q-j}] G_k` (Laurent coefficients) |
| `Acoef`, `A0`, `window` | `F̃ = ∑_s A_s ζ(s) - A₀` (JTNB (8.12)); `window = {r+2, r+4, …, q-2}` |
| `m0`, `mj`, `Dprod`, `omegaKP`, `omegaP`, `PhiN`, `Delta` | JTNB Lemma 19, (8.8), (8.9); `Δ_n = D_{m₁}^r D_{m₂}⋯D_{m_{q-r}} / Φ_n` |
| `phi0`, `Piece`, `PieceValid`, `phiWeight`, `phiSumQ`, `mu`, `muSum` | JTNB p. 283–284, the φ-integral |
| `C0lo = 748.1`, `C2hi = 748` | certified rates; `C₂ = 747.0513 ≤ 747.486 < C2hi < C0lo < C₀ = 750.7117` |

## Statement map

| Stmt | content | source | file | deps | diff. | status |
|---|---|---|---|---|---|---|
| `Stmt_ZetaReal` | `riemannZeta s = ∑ m^{-s}` (s ≥ 2) | Mathlib | `ZetaReal` | – | 1 | **done** |
| `Stmt_Criterion` | `Δ_n F_n ∈ ℤ`, `→ 0`, `≠ 0` i.o. ⇒ not all rational | JTNB Prop. 5 | `Criterion` | – | 2 | **done** |
| `Stmt_PF` | `R̃(y+ε) = ∑ B_{j,k} (y+k+ε)^{-(j-r)}` at non-poles | JTNB p. 281 | `PartialFractions` | – | 4 | **done** |
| `Stmt_CoeffVanish` | `B_{j,h₀-k} = (-1)^j B_{j,k}`; `∑_k B_{r+1,k} = 0` | JTNB (8.3), (8.5) | `CoeffVanish` | PF | 3 | **done** |
| `Stmt_LinearForm` | `HasSum term (-A₀ + ∑_{s∈window} A_s ζ(s))` | JTNB Lemma 19 (part 1) | `LinearForm` | PF, CoeffVanish | 4 | **done** |
| `Stmt_BrickInt` | `D_{a-b}^i [ε^i] P ∈ ℤ`, `D_{b₀-a₀-1}^i [ε^i] εS ∈ ℤ` | JTNB Lemmas 15, 16 | `BrickIntegral` | – | 3 | **done** |
| `Stmt_BrickVal` | `ord_p [ε^i] ≥ w - i` (`wPoly`, `wRat`) | JTNB Lemmas 17, 18 | `BrickValuation` | – | 3 | **done** |
| `Stmt_LaurentSupp` | `B_{j,k} = 0` unless `h_j ≤ k ≤ h₀-h_j` | pole orders | `LaurentSupport` | – | 2 | **done** |
| `Stmt_LaurentInt` | `D_{m₀}^{q-j} B_{j,k} ∈ ℤ` | JTNB (8.10) | `LaurentIntegral` | BrickInt, LaurentSupp | 3 | **done** |
| `Stmt_LaurentVal` | `ord_p B_{j,k} ≥ ω_{k,p} - (q-j)` (`p² > h₀`) | JTNB (8.11) | `LaurentValuation` | BrickVal | 3 | **done** |
| `Stmt_Harmonic` | `D_m^s H^{(s)}_N ∈ ℤ`; `ord_p H ≥ -s` (`N < p²`) | – | `Harmonic` | – | 2 | **done** |
| `Stmt_Lemma19` | `Δ_n A₀, Δ_n A_s ∈ ℤ` | JTNB Lemma 19 | `Lemma19` | LaurentSupp, LaurentInt, LaurentVal, Harmonic | 4 | **done** |
| `Stmt_OmegaPhi0` | `ω_{k,p}(n) = φ₀(n/p, (k-1)/p)` | JTNB (8.9) vs p. 283 | `OmegaPhi0` | – | 2 | **done** |
| `Stmt_PhiTable` | every table piece is valid: `φ₀ ≥ v` on it | docs/window/proof.md §2 (computed there) | `PhiTable` | – | 5 (computer-assisted) | **done** (verified checker, `decide +kernel`) |
| `Stmt_PhiData` | table sorted and in `[0,1]`, `1341 - phiSumQ < 748` | docs/window/proof.md §2 | `PhiData` | – | 1 | **done** (`decide +kernel`) |
| `Stmt_DenomGrowth` | `Δ_n ≤ e^{748 n}` eventually | JTNB Prop. 5 + PNT | `DenomGrowth` | PNT, OmegaPhi0, PhiTable, PhiData | 4 | **done** |
| `Stmt_L20Upper` | `\|F̃_n\| ≤ e^{-748.1 n}` eventually | proof_v2 §2.3, Theorem U | `Lemma20Upper` (+ `L20U/`) | PF, CoeffVanish, LinearForm | 4 | **done** (certificates checked by `norm_num`) |
| `Stmt_AuxPrime` | `v_ℓ(A₀) < 0 ≤ v_ℓ(A_s)` at `ℓ = 63n - 1` prime, `n` even, eventually | proof_v2 §2.2, Theorem N | `AuxPrime` | LaurentSupp, LaurentInt, LaurentVal, Harmonic | 3 | **done** |
| `MainStatement` | the theorem | proof_v2 §3 | `Assembly` | ZetaReal, Criterion, LinearForm, Lemma19, DenomGrowth, L20Upper, AuxPrime (+ Dirichlet, Mathlib) | – | **done** |

## Dependency graph

```
MainStatement ⇐ ZetaReal, Criterion, LinearForm, Lemma19, DenomGrowth, L20Upper, AuxPrime
  LinearForm  ⇐ PF, CoeffVanish ⇐ PF
  Lemma19     ⇐ LaurentSupp, LaurentInt ⇐ (BrickInt, LaurentSupp), LaurentVal ⇐ BrickVal, Harmonic
  DenomGrowth ⇐ PNT (proved, Cited/PNT.lean), OmegaPhi0, PhiTable, PhiData
  L20Upper    ⇐ PF, CoeffVanish, LinearForm            (Theorem U)
  AuxPrime    ⇐ LaurentSupp, LaurentInt, LaurentVal, Harmonic   (Theorem N)
```

All statements are proved (2026-09-26); `STATUS_WINDOW.md` records the rounds.

**How the assembly uses `Stmt_AuxPrime`** (`Window/Assembly.lean`, proof_v2 §3). Inside the proof
by contradiction, with `ζ(s) = q_s ∈ ℚ` for `s ∈ window`: Dirichlet (`auxPrime_frequently`) gives
infinitely many even `n` with `ℓ = 63n - 1` prime; for large ones `ℓ > d = ∏ den q_s`, so
`v_ℓ(q_s) ≥ 0`, and `F̃_n = -A₀ + ∑ A_s q_s` is non-zero because `v_ℓ(A₀) < 0 ≤ v_ℓ(∑ A_s q_s)`
(`neg_add_sum_ne_zero`). The proved `Stmt_Criterion` then does the rest (the integer `d Δ_n F̃_n`
is non-zero and `< 1` in absolute value). The `ℓ`-adic valuation of Lean's `Δ_n` at `ℓ` is 6
(`D_{m₁}⁵ D_{m₂}` with `m₁ = m₂ = 63n ≥ ℓ > m₃ = 62n`; `Φ_n` only has primes `≤ 60n`), so
`v_ℓ(Δ_n A₀) = 1`; the argument does not need this value.

## Key design decisions

1. **Mathlib-only statement.** `MainStatement` mentions only `riemannZeta`. `zetaR s = ∑ 1/(m+1)^s`
   is bridged by `Stmt_ZetaReal`, which is proved. The `Challenge.lean`/`Solution.lean` pair for Palomar
   copies the statement verbatim.
2. **Generic in the configuration.** `Config = (r, q, η₀, η)` with Zudilin's admissibility conditions
   (`Admissible`). Everything except the φ-table, `DenomGrowth` and Lemma 20 is stated for every
   admissible configuration. The mirror tests the generic statements on `cfgW` and on Zudilin's
   Theorem 3 configuration (r = 3, q = 13, η₀ = 91).
3. **Power series instead of derivatives.** `R̃^{(r-1)}(t)/(r-1)! = [ε^{r-1}] R̃(t+ε)`, and the Laurent
   coefficients are `[ε^{q-j}]` of the brick product `G_k`, all in `PowerSeries ℚ`, as in the parent
   project. This way every arithmetic lemma is a statement about rational coefficients.
4. **ω over a full residue system.** `omegaP` takes the minimum of `ω_{k,p}` over `0 ≤ k < p`, while
   JTNB (8.9) uses `h_{r+1} ≤ k ≤ h₀-h_{r+1}`. The two agree for the primes `p ≤ m_{q-r} = 60n` that
   enter `Φ_n`, because that range contains more than `p` consecutive integers. Ours is never larger, so
   `Stmt_Lemma19` is only weaker. The p-periodicity of `ω_{k,p}` in `k` is part of the `Lemma19` proof.
5. **The analytic input in its weakest usable form; nonvanishing by arithmetic.** The assembly needs
   one upper bound with some rate `C0lo > C2hi` (`Stmt_L20Upper`) and, under the rationality
   hypothesis, `F̃_n ≠ 0` infinitely often. The latter now comes from `Stmt_AuxPrime`, an eventual
   statement about the rationals `A0 cfgW n`, `Acoef cfgW n s` only (no analysis, no `Fn`). It is
   eventual so that a proof may take `ℓ > num(Q₁) = 984698059590803` instead of certifying that this
   numerator is prime. It carries `Even n` as a hypothesis (implied by the primality of `63n - 1`).
   The positive-density argument of docs/window/proof.md §3.6 (ω/π ∉ ℤ) is not used.
6. **Constants.** The φ-certificate uses all 2602 pieces with `φ > 0` and 20 integer translates. It
   certifies `C₂ ≤ 1341 - 593.5146 = 747.4854`. So `C2hi = 748` and `C0lo = 748.1` leave the analytic
   upper bound a slack of **2.61 per n** (the true rate is `C₀ = 750.7117`). Theorem U's rate
   `C₀' = 750.618` uses it with room to spare (`n ≥ 74`); the Lean proof of Theorem U proves the
   rate 749 (tangent point `η = 9`). proof_v2's refined Lemma 19
   (`C₂' ≤ 729.05`, route R1) would enlarge the margin to 21.5 but needs a new denominator `D_n`
   and new arithmetic statements; it is not adopted, because the proved `Stmt_Lemma19`,
   `Stmt_PhiData` and `C2hi = 748` already leave a positive margin.

## The φ-certificate: why it cannot be crude

`C₀ - C₂ = 3.6604` per n, while `∫_{1/60}^{∞} φ(x) dx/x² = 593.9487`. The certificate therefore has to
capture the integral to within 0.62 %. Of this, `x ∈ [1/60, 1)` contributes 584.84 and `x ≥ 1` (primes
`p ≤ n`, periodic φ) contributes 9.11, which alone exceeds the slack. A greedy choice needs about 1880
of the 2602 non-zero pieces (`C2hi` = 750.6, K = 20 translates; `python/window_audit/greedy.py`). The
full table costs only about 40 % more kernel time, and it frees the analytic slack above.
`Stmt_PhiTable` (validity of every piece) is the certified version of a number that
`docs/window/proof.md` only COMPUTED. It is a new computer-assisted verification:
`Proofs/PhiTable.lean` proves it with a checker whose soundness is proved in Lean and which the kernel
evaluates (`decide +kernel`). `Stmt_PhiData` is proved by kernel evaluation as well.

## Numerical mirror (`python/window_mirror.py`, log `python/window_mirror_full.log`)

The mirror uses stdlib `fractions` for every exact check and mpmath for the zeta values. Every Lean
definition is transcribed literally, including truncated ℕ-subtraction, floor division on ℤ,
`x/0 = 0`, and the zero inverse of a power series whose constant term is 0.

The full run makes **415 069 checks with 0 failures** (684 s, 2026-09-26; 414 992 in 288 s before
the `AuxPrime` section was added):
* Admissibility, `window`, `muSum = 1341`, and `m_j = μ_j n`.
* `BrickInt`, `BrickVal`: 250 random bricks, every coefficient, primes `p < 60`.
* `Harmonic`; `OmegaPhi0` (1500 random `(n, p, k)`); `ZetaReal`.
* Exhaustive checks in `j`, `k` and `p ≤ 2h₀+2` of `LaurentSupp`, `LaurentInt`, `LaurentVal`,
  `CoeffVanish` (the occurring ζ's are exactly `window`), `Lemma19` (exact integrality of `Δ_n A₀` and
  `Δ_n A_s`), and `PF` at random rational `y`. These run for `cfgW` with n = 1, 2 and the Theorem 3
  configuration with n = 1, 2, 3.
* The linear-form value for `cfgW` equals the independent engine `docs/window/zud_exact.py`, called
  live (relative difference `7e-263`). That engine was validated against the Barnes integral to
  `1e-13` for n ≤ 9. For example `log|F̃₁| = -799.4450029421` and `log|F̃₂| = -1559.4383100008`.
* The series itself, via exact partial sums, for the Theorem 3 configuration (relative error `8e-99`).
* `PhiTable`: at every piece, φ(midpoint) = `v`, and the exact minimum over all critical `y` at a
  random interior point is `≥ v`. `PhiData` is checked exactly.
* `DenomGrowth` trend: `log Δ_n / n` = 832.9, 803.1, 785.3, 780.5 for n = 5, 10, 20, 40. Convergence to
  `C₂` is slow (PNT).
* `L20Upper` on the recorded exact values for n ≤ 9: all are `≤ -748.1 n` (and non-zero).
* `AuxPrime` (section added 2026-09-26; `--aux` runs it alone): the literal exact `A0 cfgW 4`,
  `Acoef cfgW 4 s` (`ℓ = 251`) give `v_ℓ(A₀) = -5` and `v_ℓ(A_7, …, A_21) = (1,1,0,0,2,4,8,10)`. An
  `ℓ`-adic evaluation of the same definitions modulo `ℓ^30` (`aux_padic`, equal to the exact values
  modulo `ℓ^30` at n = 4) gives the same valuations for every even `n ≤ 60` with `63n - 1` prime.

`python/window_phitable.py --crosscheck docs/window/vz.py` reproduces all 2644 pieces of `vz.py`
(an independent implementation, literal `phi0`).

## Mathematical review (adversarial pass done while blueprinting)

* Lemma 19 was re-derived for general odd r. The proof never uses r = 3: bricks, Leibniz rule, the
  (7.5) floor identities, and the rough and p-adic parts. It was confirmed exactly (see above).
* In the Barnes representation (A), the residue computation `K_r(k+ε) = ε^{-r} + O(1)`, the zeros of R
  of order r at `M < k ≤ -1`, the orientation sign and `π/(sin πt Γ(1+t)) = -Γ(-t)` were all checked.
  In the branch split (B), `V₅(cos θ) = (cos 3θ + 11 cos θ)/12` and `J_{-λ} = -conj J_λ` hold. For the
  Stirling bookkeeping (C), the `n log n` terms cancel (`-336` from `G`, `+336` from `N_h`), the
  linear terms cancel exactly, the n-power is `-14 + 1`, then `n^{-12}` after `dt = n dτ`, and `n^{-25/2}` after Laplace; `e^{iπλnη₀} = 1`. The
  landscape (E) monotonicity argument and `f - τ f' = f₀` were also checked. No error was found.
* **Minor slip in docs/window/proof.md §1:** `deg R = -336n - 17`, not `-336n - 4`. The numerator has
  degree `800n+6` and the denominator `1136n+23`. The proof only uses `deg R ≤ -2`, so it is not
  affected.
* The φ-integral is only COMPUTED in docs/window/proof.md (two implementations). A crude certified
  lower bound is **not** enough (see above). The Lean table is the first certification.
* Lemma 20 as proved in docs/window/proof.md rests on (i) a saddle-point theorem for a complex phase along a
  line (Olver Ch. 4 Thm 7.1) and (ii) interval numerics in `mpmath.iv` (130-bit). The restatement of
  2026-09-26 removes both from the formalisation: `Stmt_L20Upper` follows from Theorem U (pointwise
  bounds on the contour `Re t = 1/2 - n`, exact-rational certificates of ≈ 300 `log`/`arctan`
  enclosures, `docs/window/refine/`), and the nonvanishing from Theorem N (`Stmt_AuxPrime`).
* Restater's checks of Theorem N in the Lean normalization (`c₀ = -A0`, `c_s = Acoef s`,
  `a_{i,k} = B (i+5) k`), exact at n = 4 and 8: `X^{16} ∣ Gk` at `k = 110n, 110n+1`,
  `v_ℓ(B_{7,k}) = 1`, `v_ℓ(B_{6,k}) = 0`, `B_{7,110n}/B_{7,110n+1} = ρ(110n+1)` of Lemma E,
  `ℓ⁵ A₀ ≡ -4(u_{110n} + u_{110n+1}) ≡ -4 Q₁ u_{110n+1} (mod ℓ)`; and `ω_{k,ℓ} = 17` at both top poles
  (so `Stmt_LaurentVal` gives `v_ℓ(B_{7,k}) ≥ 1`).
* The theorem is asymptotic and ineffective, through PNT, exactly like Zudilin's.

## Workflow for provers

(The instructions the prover subagents followed; kept as a record.)

* Elaborate one file: `bash scripts/check.sh Zeta2Lean/Window/Proofs/Foo.lean`.
* Never edit `Window/Defs.lean`, `Window/PhiTable.lean`, `Window/Statements.lean`,
  `Window/Assembly.lean` or `Window/Main.lean`. If a statement looks false, report it to the architect
  with a mirror counterexample.
* Keep the `theorem X_proof` header (its hypotheses and type) exactly as in the stub. Put helpers in the
  file, in `namespace ZetaWindow.<FileName>` or as `private` lemmas.
* Scratch files go in `Zeta2Lean/Scratch/<yourname>_*.lean`, which is git-ignored. Delete them when done.
* The parent project's proofs (`Zeta2Lean/Proofs/` of https://github.com/gmDevi/zeta2-7-9-11-lean,
  removed from this repository) are templates for several files: `PartialFractions`, `CoeffVanish`,
  `LinearForm`, `BuildingBlock`, `DenomL2a`, `DenomL2c` (the tame calculus) and `Asymptotics` (PNT).
  For `Lemma20Upper` the template is `Zeta2Lean/Pair/Proofs/Growth.lean` of the pair project
  https://github.com/gmDevi/zeta2-7-9-lean, with `Landscape/` (contour representation, window
  comparison, certified `log`/`arctan` values); for `AuxPrime` it is `Pair/Proofs/Nonvanishing.lean`
  there (auxiliary-prime nonvanishing of the pair) and this project's `Proofs/Lemma19.lean` (`VpGe`
  calculus).
