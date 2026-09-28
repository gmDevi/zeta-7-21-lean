# At least one of ζ(7), ζ(9), …, ζ(21) is irrational

A Lean 4 + Mathlib formalisation of an unrefereed result that our literature search did not find stated
before (see *Novelty* below):

> **Theorem.** At least one of the eight numbers ζ(7), ζ(9), ζ(11), ζ(13), ζ(15), ζ(17), ζ(19), ζ(21) is
> irrational.

It improves W. Zudilin's theorem that at least one of ζ(7), ζ(9), …, ζ(35) is irrational (*One of the eight
numbers ζ(5), ζ(7), …, ζ(17), ζ(19) is irrational*, Math. Notes 70 (2001) 426–431, Theorem 2). The proof uses
the very-well-poised linear forms of W. Zudilin, *Arithmetic of linear forms involving odd zeta values*,
J. Théor. Nombres Bordeaux 16 (2004) 251–291, §8, with five derivatives. At the end of §8 (p. 286) Zudilin
remarks that his lists ζ(7), …, ζ(35) and ζ(9), …, ζ(51) can be shortened with these forms, but that he could not
prove the needed asymptotic lemma (his Lemma 20) for more than three derivatives. This repository carries out that
improvement for the list starting at ζ(7), without Lemma 20.

## What exactly is proved in Lean

```lean
-- Zeta2Lean/Window/Main.lean
theorem ZetaWindow.zeta_7_to_21_not_all_rational :
    ¬ ∀ k ∈ ({7, 9, 11, 13, 15, 17, 19, 21} : Finset ℕ), ∃ q : ℚ, riemannZeta (k : ℂ) = (q : ℂ)
```

`#print axioms` reports `[propext, Classical.choice, Quot.sound]`, and the theorem has no hypotheses. There is no
`sorry` (apart from the intended one in the Palomar statement file `Challenge.lean`), no `axiom` declaration and no
`native_decide`; the computer-assisted parts (below) are checked by the Lean kernel, through `decide +kernel` and
`norm_num`. CI replays every module in the kernel with `leanchecker`.

**The statement uses only Mathlib.** `riemannZeta` is Mathlib's Riemann zeta function, and `(k : ℂ)`, `(q : ℂ)` are
the casts of a natural number and of a rational number. For an integer k ≥ 2, `riemannZeta k = ∑_{m ≥ 1} m^{-k}`
(Mathlib's `zeta_nat_eq_tsum_of_gt_one`), so these are the classical values ζ(k). No definition of this repository
occurs in the statement, and nothing is cited in it: the definitions used by the proof
(`Zeta2Lean/Window/Defs.lean`) need not be trusted, since if one of them did not mean what its docstring says, the
theorem would still be the one displayed. The theorem says that the eight values are not all rational. It does not
say which of them is irrational, and it gives no irrationality measure and no effective bound.

## The mathematics

The informal proof is `docs/proof.md`. (Its first version, `docs/window/proof.md`, proves the same theorem with a
saddle-point analysis that neither `docs/proof.md`'s route R2 nor the Lean proof uses.) The construction is
Zudilin's (JTNB 2004, (8.1)–(8.13)) with r = 5 derivatives, q = 23 factors, η₀ = 160 and
η = (47, 47, 47, 47, 48, 50, 50, 51, 52, 53, …, 66): for n ≥ 1, h₀ = 160n + 2, h_j = η_j n + 1,

R(t) = (h₀+2t) (t+1)⁵_{h₀−1} / ∏_{j=1}^{23} (t+h_j)_{h₀+1−2h_j},  N_h = ∏_{j>5} (h₀−2h_j)! / ∏_{j≤5} ((h_j−1)!)²,
F̃ₙ = N_h Σ_{t≥0} R⁽⁴⁾(t)/4!.

The proof formalised here is route R2 of `docs/proof.md` §6:
* **Linear form.** F̃ₙ = −A₀ + Σ_{s ∈ {7, 9, …, 21}} A_s ζ(s) with rational A₀, A_s. The partial-fraction
  coefficients give it; ζ(5) drops out because the residues of R sum to zero (deg R ≤ −2), and the even zeta values
  drop out by the symmetry R(−t−h₀) = −R(t).
* **Denominators** (Zudilin's Lemma 19). Δₙ A₀ and Δₙ A_s are integers, where
  Δₙ = D_{63n}⁵ D_{63n} D_{62n} D_{61n} D_{60n}¹⁴ / Φₙ, D_m = lcm(1, …, m), and Φₙ is a product of primes p > √h₀
  with exponents given by Zudilin's periodic function φ₀.
* **Growth of the denominators.** log Δₙ ≤ 748n for all large n. The prime number theorem gives
  log D_{mn} = mn + o(n), so the numerator is e^{1341n+o(n)}; a table of 2602 pieces of the function
  φ(x) = min_y φ₀(x, y), each certified in Lean, gives log Φₙ ≥ 593.514n − o(n). (The true exponent is
  C₂ = 747.0513….)
* **Size of the forms** (Theorem U of `docs/proof.md`). |F̃ₙ| ≤ e^{−748.1n} for all large n. F̃ₙ is a contour
  integral of N_h R against the kernel K₅(t) = Σ_{ν∈ℤ} (t−ν)^{−5} along the line Re t = ½ − n. On that line,
  log|N_h R K₅| ≤ n U(Im t / n) + O(log n + log(1 + |Im t|)), by comparing the log-sums with integrals and by Stirling
  bounds for N_h; and U ≤ −749, by a concavity argument, one tangent at η = 9 and certified values of log and arctan.
  No saddle point is located. (The true rate is C₀ = 750.7116….)
* **Nonvanishing** (Theorem N of `docs/proof.md`). For all large n with ℓ = 63n − 1 prime, v_ℓ(A₀) = −5 while
  v_ℓ(A_s) ≥ 0. So if ζ(7), …, ζ(21) were rational with denominators prime to ℓ, F̃ₙ would be non-zero. Dirichlet's
  theorem (primes ≡ −1 mod 126) gives infinitely many such n. This is the Archimedean form of the auxiliary-prime
  criterion of L. Lai and J. Sprang (arXiv:2306.10393, Lemma 2.3), proved here in the form needed.
* **Criterion** (Zudilin's Proposition 5, elementary part). With d a common denominator of the ζ(s), d Δₙ F̃ₙ is a
  non-zero integer of absolute value at most d e^{(748 − 748.1)n} → 0: a contradiction.

What is new: Zudilin proves Lemma 20 (the asymptotics of F̃ₙ, which give both the upper bound and F̃ₙ ≠ 0) only for
r = 3. Here Lemma 20 is replaced by Theorem U (an upper bound with no saddle-point analysis) and Theorem N (an
arithmetic nonvanishing); the configuration (q = 23, η₀ = 160, η) was found by the parameter search behind this
work. `docs/proof.md` also contains a
refined denominator bound (route R1, margin 21.567 per n instead of 3.567); the Lean proof does not use it.

## The proof in Lean

`Zeta2Lean/Window/Defs.lean` defines the forms for every admissible configuration `c = (r, q, η₀, η)`
(`Config`, `Admissible`), with the Taylor expansions `Rser c n y` of R at non-poles, the terms
`term c n t = [ε^{r−1}] N_h R(t+ε)` and `Fn c n = ∑' t, term c n t` (= F̃ₙ), the brick products `Gk`, the
Laurent coefficients `B c n j k`, the coefficients `A0`, `Acoef` and the window `{r+2, r+4, …, q−2}`, Zudilin's
exponents `omegaKP`, `PhiN`, `Delta`, and the function `phi0`; `cfgW` is the configuration above.
`Zeta2Lean/Window/PhiTable.lean` holds the table of 2602 pieces (generated by `python/window_phitable.py`).
`Zeta2Lean/Window/Statements.lean` has one statement per lemma, and `Zeta2Lean/Window/Assembly.lean`
(`main_of_stmts`) derives the theorem from them, with the constants `C2hi = 748` and `C0lo = 748.1`. The proofs,
one file per statement in `Zeta2Lean/Window/Proofs/`:
* **Linear form** (`PartialFractions`, `CoeffVanish`, `LinearForm`): `HasSum term (−A₀ + Σ_s A_s ζ(s))` for every
  admissible configuration, with the coefficients of ζ(r) and of the even ζ(s) equal to 0.
* **Zudilin's Lemma 19** (`BrickIntegral`, `BrickValuation`, `LaurentSupport`, `LaurentIntegral`,
  `LaurentValuation`, `Harmonic`, `Lemma19`): `Δₙ A₀, Δₙ A_s ∈ ℤ` for every admissible configuration and every n,
  from Zudilin's Lemmas 15–18 on the elementary "bricks".
* **Growth of Δₙ** (`OmegaPhi0`, `PhiTable`, `PhiData`, `DenomGrowth`): `Δₙ ≤ e^{748n}` eventually. `PhiTable`
  proves that every piece of the table is valid (φ₀(x, y) ≥ v for all y when x mod 1 lies in the piece) with a
  checker whose soundness is proved in Lean and which the kernel evaluates by `decide +kernel`; `PhiData` checks by
  `decide +kernel` that the pieces are sorted and disjoint and that 1341 − (table sum) < 748, with an integer
  fixed-point lower bound for the sum; `DenomGrowth` combines them with the prime number theorem.
* **Theorem U** (`Lemma20Upper`, helper modules `Proofs/L20U/`): `|F̃ₙ| ≤ e^{−748.1n}` eventually. `Contour.lean`
  proves the contour representation (Cauchy's formula on half-planes, the zeros of R); `Gf.lean` and `Pointwise.lean`
  the pointwise bound; `Landscape.lean` the landscape inequality U ≤ −749, whose numerical inputs are 59 `log` and
  86 `arctan` enclosures in `Cert.lean` (generated by `L20U/gen/gen_cert.py`, exact rationals), each checked by
  `norm_num` through the rational bounds of `Numerics.lean`.
* **Theorem N** (`AuxPrime`): `v_ℓ(A₀) < 0 ≤ v_ℓ(A_s)` for large n with ℓ = 63n − 1 prime (in fact v_ℓ(A₀) = −5),
  by ℓ-adic bookkeeping in `ZMod ℓ` and an exact telescoping identity; two integer constants are computed by
  `decide`.
* **Criterion and assembly** (`Criterion`, `Assembly.lean`): Zudilin's Proposition 5 (elementary part), Dirichlet's
  theorem from Mathlib (`Nat.forall_exists_prime_gt_and_modEq`), and `ZetaReal` (the bridge to `riemannZeta`).
* **Prime number theorem** (`Zeta2Lean/Cited/PNT.lean`, `Zeta2.PNT_proof`: ψ(x)/x → 1 with Mathlib's
  `Chebyshev.psi`), from the Wiener–Ikehara theorem vendored under `Zeta2Lean/Cited/Vendor/PNT/` from mathlib4 pull
  requests #43046, #43233 and #43238 (head 78e1b2bbd0). That code is derived from the PrimeNumberTheoremAnd project,
  keeps its Apache-2.0 headers and authors, and was ported to this Mathlib pin.

**Computer assistance.** Three kinds of certified computation occur, all checked by the Lean kernel (none uses
`native_decide` or trusts the compiler): the φ-table (`PhiTable`, `PhiData`: `decide +kernel` on natural numbers),
the `log`/`arctan` enclosures of Theorem U (`L20U/Cert.lean`: `norm_num`), and two integer constants of Theorem N
(`decide`). The Python generators of the table and of the enclosures are in the repository; they are not trusted,
since Lean checks their output. `python/window_mirror.py` is an exact-arithmetic mirror of every definition, with
numerical checks of every statement (415,069 checks, log in `python/window_mirror_full.log`).

**Differences from `docs/proof.md`.** The Lean proof follows route R2 of `docs/proof.md` §6, with these differences:
* weaker constants: the criterion uses Δₙ ≤ e^{748n} and |F̃ₙ| ≤ e^{−748.1n} (`docs/proof.md`: C₂ = 747.0513… and
  |F̃ₙ| ≤ K n¹⁶ e^{−750.618n} for every n); Theorem U is proved in the form |F̃ₙ| ≤ C n³⁵ e^{−749n} for n ≥ 4, with
  the tangent point η = 9 instead of 181/20, and the line is compared directly with x₀ = 159, so the Lipschitz
  constant B of `docs/proof.md` §2.3 is not needed;
* its own kernel-checked certificates, in place of the certificate files of `docs/window/refine/`;
* Theorem N for all large n, which avoids certifying that the numerator of the constant Q₁ is prime (it suffices
  that ℓ exceeds it), instead of every even n ≥ 2;
* results that `docs/proof.md` cites are proved in Lean: Zudilin's Lemma 19 for every prime, the vanishing of the
  ζ(5) and even-ζ coefficients, the prime number theorem, the Stirling bounds and the contour identities.
  Dirichlet's theorem, Cauchy's integral formula and ζ(k) = Σ m^{−k} come from Mathlib;
* Lean's ω_p in Φₙ is the minimum over a full residue system, which is never larger than Zudilin's minimum over the
  pole range and agrees with it for this configuration at every prime of Φₙ;
* the refined denominators (ingredient H′, route R1) and the saddle-point analysis of `docs/window/proof.md` are
  not formalised; the theorem does not need them.

## Status and caveats

* **Unrefereed, produced by AI agents.** The mathematics (the configuration, Theorems U and N, the informal proofs)
  and this formalisation were produced by AI agents (Anthropic Claude models) under the direction of the
  maintainer, and have not been reviewed by a human expert (`formalization.yaml` describes the process). The Lean
  kernel checks the formal statement displayed above, which uses only Mathlib's definitions.
* **Novelty.** In the literature found by the search described here, the shortest list of odd zeta values starting
  at ζ(7) known to contain an irrational number is ζ(7), …, ζ(35): Zudilin's Theorem 2 of 2001, which also follows
  from L. Lai and L. Zhou, *At least two of ζ(5), ζ(7), …, ζ(35) are irrational*, Publ. Math. Debrecen 101 (2022)
  353–372. Lai and Zhou's result is of a
  different kind: two irrational values among ζ(5), …, ζ(35), where the theorem here gives one among ζ(7), …, ζ(21);
  neither implies the other. Our search (2026-09-24 to 2026-09-26, by AI agents) covered Zudilin's publication list,
  arXiv (with author searches for Zudilin, Rivoal, Fischler, Lai and Sprang), zbMATH Open, the lists of works citing
  Zudilin's papers of 2001–2004 in OpenAlex, Semantic Scholar, mathnet.ru and Google Scholar, Zudilin's 2011 survey
  and 2013 habilitation thesis, and Zenodo. It found no shorter such list, and no execution of Zudilin's 2004 remark.
  MathSciNet was not searched, so novelty beyond this search is not established.
* **Claims about single values.** An unrefereed Zenodo preprint (P. Anand, *Zeta 7 is Irrational*, 23 September
  2026, doi:10.5281/zenodo.22920911) claims that ζ(7) is irrational, which would imply the theorem. Our own
  check could not confirm two constants on which its final inequality rests, so we do not regard ζ(7) as
  settled. It adapts the method of another unrefereed preprint (A. Fauzan, *ζ(5) is irrational*,
  17 September 2026, doi:10.5281/zenodo.22826419), for which Lean formalisations have been announced; ζ(5) does not
  occur in the theorem here.
* **Relation to the 2-adic repositories.** This repository started as a copy of
  https://github.com/gmDevi/zeta2-7-9-11-lean (registered in the Palomar registry as PALOMAR-2026-09-25-000023:
  at least one of the 2-adic zeta values ζ₂(7), ζ₂(9), ζ₂(11) is irrational), and the files of that project that the
  theorem here does not use were removed. The two share the vendored Wiener–Ikehara files and the proof of the prime
  number theorem (identical files and declarations). Two helper files of Theorem U (`L20U/VLine.lean`,
  `L20U/Numerics.lean`) and part of `L20U/Gf.lean` are copied from https://github.com/gmDevi/zeta2-7-9-lean
  (PALOMAR-2026-09-25-000026: at least one of ζ₂(7), ζ₂(9) is irrational), whose growth bound uses the same
  contour technique. The mathematics is otherwise independent: the results there concern 2-adic values. The Lean
  library is still called `Zeta2Lean`, and the prime number theorem is still stated in the namespace `Zeta2`, for
  this historical reason.

## Layout

* `Zeta2Lean/Window/Defs.lean`, `Zeta2Lean/Window/PhiTable.lean`: the definitions and the φ-table.
* `Zeta2Lean/Window/Statements.lean`: one statement per lemma. `Zeta2Lean/Window/Assembly.lean`: the theorem from the
  statements.
* `Zeta2Lean/Window/Proofs/*.lean`: one proof per statement; `Proofs/L20U/` holds the parts of Theorem U, and
  `Proofs/L20U/gen/gen_cert.py` generates `Cert.lean`.
* `Zeta2Lean/Window/Main.lean`: the wiring, the main theorem and `#print axioms`.
* `Zeta2Lean/Cited/PNTStatement.lean`, `Zeta2Lean/Cited/PNT.lean`, `Zeta2Lean/Cited/Vendor/PNT/`: the prime number
  theorem and the vendored Wiener–Ikehara code (Apache-2.0).
* `BLUEPRINT_WINDOW.md`: statement map, dependency graph and design decisions. `STATUS_WINDOW.md`: the log of the
  formalisation rounds, the two adversarial audits and the checks.
* `docs/proof.md`: the informal proof. `docs/window/`: its first version, the three track write-ups behind it
  (`docs/window/refine/`) and the scripts, certificates and logs of the informal proof.
* `python/`: `window_mirror.py` (exact-arithmetic mirror of the definitions, with numerical checks of every
  statement), `window_phitable.py` (generator of the φ-table), `window_audit/` (the auditors' independent
  recomputations), and logs of full runs.
* `scripts/`: `check.sh` (elaborate one file), `build.sh`, `audit.sh` (sorry and forbidden-construct census),
  `kernels.sh` (`leanchecker`, one module at a time).
* `Challenge.lean`, `Solution.lean`, `comparator.json`, `formalization.yaml`: the statement, proof and metadata
  for [Comparator](https://github.com/leanprover/comparator) and the Palomar registry (next section).

## Challenge and Solution

`Challenge.lean` imports only Mathlib and states the theorem as `ZetaWindow.zeta_7_to_21_not_all_rational_palomar`,
with `sorry`; it uses no definition of this repository. `Solution.lean` proves the same statement from
`ZetaWindow.zeta_7_to_21_not_all_rational`. `comparator.json` asks Comparator to check that the two statements are
identical and that the proof uses only `propext`, `Quot.sound` and `Classical.choice`. The toolchain (v4.35.0-rc2)
ships `lake comparator`; it needs `bwrap` (bubblewrap) for its sandbox. On 2026-09-26 the toolchain's
`lake comparator`, run as Palomar runs it (`Challenge.lean` compiled outside Lake against Mathlib only, both modules
exported with `leanexport`, the NanoDa and con-ron kernels besides Lean's), accepted `Solution.lean`; the run was
unsandboxed, because bubblewrap is not installed on that machine. An altered copy of `Challenge.lean`, with ζ(23) in
place of ζ(21), was rejected. Compiled alone with `lean` against the pinned Mathlib, `Challenge.lean` depends only on
Lean core and Mathlib. `formalization.yaml` records the sources, the production process and the review status.

## Building

```bash
lake exe cache get
lake build                                    # also builds Challenge and Solution
lake env lean Zeta2Lean/Window/Main.lean      # prints the axioms of the main theorems
lake comparator                               # judges Solution against Challenge (needs bwrap)
bash scripts/audit.sh                         # sorry / forbidden-construct census
bash scripts/kernels.sh                       # leanchecker on every module, one at a time
```

## Licence

Apache-2.0 (`LICENSE`). The vendored files under `Zeta2Lean/Cited/Vendor/PNT/` keep their upstream Apache-2.0
headers and authors.
