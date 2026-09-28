# Status: at least one of ζ(7), ζ(9), …, ζ(21) is irrational

Updated 2026-09-25/26 by the lead architect (window blueprint), by the auditor (two adversarial passes,
below), by the window integrator after prove rounds 1 and 2, the round-1 re-integration and the
round-2 (re-run) integration, by the window restater (switch to the robust route of proof_v2,
2026-09-26, after the PC crash at 02:10) and by the window integrator after the robust-route prove
round 1 (2026-09-26: **all stubs proved**), and by the preparer and an independent auditor for
publication (2026-09-26, next two sections). See `BLUEPRINT_WINDOW.md` for the plan. `proof_v2` is
now `docs/proof.md`, and `proof.md` (the first version) is `docs/window/proof.md`.

## Publication cleanup (preparer), 2026-09-26

* **Removed** (not in the import closure of `Zeta2Lean.Window.Main`, checked with the import graph and
  with a declaration-level audit): the {7, 9, 11} development of the parent repository
  (`Zeta2Lean/{Defs,Statements,Assembly,Main}.lean`, the 24 files of `Zeta2Lean/Proofs/`), the Andrews
  part of `Zeta2Lean/Cited/` (`Defs`, `Statements`, `Assembly`, `Main`, `Proofs/`), `BLUEPRINT.md`,
  `STATUS.md`, the 2-adic `docs/proof.md` and `docs/cited/`, the 2-adic Python mirrors and data, and the
  old Palomar files of the 2-adic submission.
* **PNT regrouped, declarations unchanged.** The window used only `Zeta2.PNT_Stmt` and the PNT chain of
  the parent `Cited/` tree. `Zeta2.PNT_Stmt` is now in `Zeta2Lean/Cited/PNTStatement.lean` (imports only
  Mathlib, so the window statements still do not import the vendored files), and
  `Stmt_WienerIkehara`, `WienerIkehara_proof`, the PNT section and the new `Zeta2.PNT_proof` are in
  `Zeta2Lean/Cited/PNT.lean` (same declarations as the file of that name in
  https://github.com/gmDevi/zeta2-7-9-lean). The vendored files are unchanged.
* **Declaration audit.** For every constant of the project modules in the closure of
  `Zeta2Lean.Window.Main`: name, kind, type hash and value hash before and after. All 2080 surviving
  constants are unchanged (7 of them moved module: the PNT chain); 213 constants of the removed modules
  are gone; `Zeta2.PNT_proof` is new. Before the cleanup the `Window` constants used, transitively, only
  `Zeta2.PNT_Stmt`, the PNT chain and the vendored files.
* **Docstrings.** References to `proof_v2`/`proof.md` point to `docs/proof.md`/`docs/window/proof.md`,
  stale "stub" remarks were updated, and local paths were replaced by the public repositories. Only
  comments changed (checked by the audit above).
* **Checks.** `lake build` green (8970 jobs, default targets `Zeta2Lean`, `Challenge`, `Solution`);
  `scripts/audit.sh`: no sorry, no forbidden construct; every `#print axioms` of `Window/Main.lean` and
  of `ZetaWindow.zeta_7_to_21_not_all_rational_palomar` gives `[propext, Classical.choice, Quot.sound]`;
  `scripts/kernels.sh`: `leanchecker` replays all 35 modules of the closure of `Solution`;
  `Challenge.lean` compiled alone with `lean` against the pinned Mathlib depends only on `Init` and
  `Mathlib`; the toolchain's `lake comparator`, run as Palomar runs it (NanoDa and con-ron besides Lean's
  kernel; unsandboxed), accepted `Solution.lean` (con-ron: 78 325 declarations), and rejected a copy of
  `Challenge.lean` with ζ(23) in place of ζ(21).

## Independent pre-publication audit (auditor), 2026-09-26

* **Policy.** Re-read PalomarPolicy `CONTRIBUTING.md`, `llms.txt`, PalomarTemplate and the
  formalization.yaml v0.4 standard (PalomarSubmission `main` still `a59f25bd`). Re-checked: root layout,
  one `lakefile.toml`, toolchain `v4.35.0-rc2` (the `toolchains.json` minimum and the `lean-toolchain` of
  the pinned Mathlib, whose tag resolves to the pinned commit `06535612`), manifest packages identical to
  Mathlib's manifest, `Challenge.lean` importing only `Mathlib`, size limits, `comparator.json`, the root
  `LICENSE` (Apache-2.0, identical to the template's), and `formalization.yaml` through Palomar's loaders
  and the upstream v0.4 schema.
* **Fidelity.** With `pp.explicit`, the compared statement uses `Nat.cast` and `Rat.cast` into `ℂ` and
  Mathlib's `riemannZeta`. A scratch file (not committed) proves in Lean that the statement is equivalent
  to `∃ k ∈ {7, 9, …, 21}, Irrational (∑' n : ℕ, 1 / (n : ℝ) ^ k)`.
* **Comparator, repeated.** The same Palomar-style run (`lake comparator` with NanoDa and con-ron,
  unsandboxed) accepted `Solution.lean` (con-ron: 78 325 declarations). A second negative control, with
  `∃ q : ℤ` in place of `∃ q : ℚ`, was rejected ("statement do not match"). The exports were deleted.
* **Corrections.** The session's transcripts record which workflow wrote each part: the first informal proof
  `docs/window/proof.md` and its scripts `zud5.py`, `explore.py`, `certify_line.py` and `barnes_check.py`
  were written by a separate research workflow, and everything else by the main workflows. `formalization.yaml` (`automation`), `README.md` and the editorial note of
  `docs/window/proof.md` now say so. Also corrected: a research-session path in
  `docs/window/refine/crude-upper-bound.md` and the issue number of the Math. Notes citation.

## Headline

* **COMPLETE (2026-09-26, robust-route prove round 1 integration).** All 18 statements are proved.
  `ZetaWindow.zeta_7_to_21_not_all_rational` (Mathlib-only statement: at least one of
  `ζ(7), ζ(9), …, ζ(21)` is irrational) depends only on **`[propext, Classical.choice, Quot.sound]`**.
  * `bash scripts/build.sh Zeta2Lean.Window.Main`: **green**, exit 0, 8968 jobs.
  * `scripts/audit.sh`: **0 sorry/admit, no forbidden construct** (no axiom/opaque/unsafe,
    native_decide, implemented_by, extern, skipKernelTC, ofReduceBool).
  * `#print axioms` of all 19 names at the end of `Window/Main.lean` (including both main theorems):
    `[propext, Classical.choice, Quot.sound]`.
  * `git diff` before the commit: only the four prover files and the new `Proofs/L20U/` helper
    directory changed; `Defs`, `Statements`, `Assembly`, `Main`, lakefile/manifest/toolchain untouched.
  * No statement issues were reported by the provers; nothing to adjudicate.
  * Committed as `1989ca4`. The new helper modules `Proofs/L20U/{VLine, Contour, Gf, Pointwise,
    Numerics, Cert, Landscape}.lean` (3689 lines; `gen/gen_cert.py` generates the certificate) carry
    Theorem U: pointwise bounds on the vertical contour `Re t = 1/2 - n` with certified numerics,
    giving `|F̃_n| ≤ e^{-748.1 n}` eventually.
  * The earlier bullets below describe the state before this round (4 stubs) and are kept as history.
* **Restated to the robust route (proof_v2, route R2), 2026-09-26.** The gap `Stmt_L20Nonzero`
  (`F̃_n ≠ 0` infinitely often, which needed the saddle-point asymptotics) is replaced by the
  arithmetic `Stmt_AuxPrime` (Theorem N: `v_ℓ(A₀) < 0 ≤ v_ℓ(A_s)` at `ℓ = 63n - 1`); `Stmt_L20Upper`
  (`C0lo = 748.1`) is unchanged and is now proved informally by Theorem U (no saddle point). **No gap
  is left: all four open files are formalisation work on informally proved and certified statements.**
  Details in the section "Restatement to the robust route" below.
* `bash scripts/build.sh Zeta2Lean.Window.Main` is **green** (exit 0, 8961 jobs) on 2026-09-26 after the
  restatement. `PhiData` uses an integer fixed-point certificate (about 11 s of kernel time).
* **Sorry census (`scripts/audit.sh`): 4** = the stubs `DenomGrowth`, `PhiTable`, `AuxPrime` (arithmetic)
  and `Lemma20Upper` (analytic); no forbidden construct.
* `#print axioms` (end of `Window/Main.lean`):
  * `main_of_stmts`, `Fn_frequently_ne_zero`, `PNT_window`, `ZetaReal_proof`, `PhiData_proof`,
    `Criterion_proof`, `Harmonic_proof`, `OmegaPhi0_proof`, `LaurentSupp_proof`, `BrickInt_proof`,
    `BrickVal_proof`, `LaurentInt_proof`, `LaurentVal_proof`, `PF_proof`, `CoeffVanish_proof`,
    `LinearForm_proof`, `Lemma19_proof`:
    `[propext, Classical.choice, Quot.sound]`;
  * `zeta_7_to_21_not_all_rational_of_L20Upper` and `zeta_7_to_21_not_all_rational`: additionally
    `sorryAx`. For the conditional theorem it comes from `DenomGrowth_proof` (through
    `PhiTable_proof`) and `AuxPrime_proof`; the unconditional one also uses `L20Upper_proof`.
* **The linear-form side and the arithmetic side (JTNB Lemma 19) are fully kernel-checked for every
  admissible configuration.** What remains is the denominator growth (PNT + φ-certificate), the
  auxiliary-prime separation (Theorem N) and the analytic upper bound (Theorem U).
* `python/window_mirror.py` (full run after the restatement, Windows Python with mpmath):
  **415 069 checks, 0 failed** (684 s, `python/window_mirror_full.log`; 414 992 before the new
  `Stmt_AuxPrime` section).
* (Before the publication cleanup) the root `Zeta2Lean.lean` did not import `Window` yet, so the
  default build and the 2-adic project were unchanged.
* Build hygiene: on 2026-09-25 around 20:41, a transient host memory shortage left 0-byte `.olean`
  files for three modules, while lake's traces still marked them as built. Later builds then failed
  with `invalid header`. Diagnose with `find .lake/build -size 0 -name '*.olean'`. The fix is to delete
  those modules' `.olean*`, `.ilean*`, `.trace` and `.c` artifacts and rebuild (never `lake clean`).
* Git repair (2026-09-25, 21:00): the WSL crash at about 20:50 interrupted the first audit commit.
  `master` pointed to a 0-byte commit object, and 36 loose objects were empty (`fatal: bad object HEAD`).
  The repair: `master` was reset to the last intact commit `01a2b3b`, the empty objects were moved to
  `.git/corrupt-backup-20260925/`, the NUL tails were stripped from the reflogs, and the index was
  rebuilt with `git read-tree HEAD`. `git fsck` is clean. The first pass's files were intact in the
  working tree and are committed with the second audit pass. After the crash the build was re-run,
  green, with the same axioms.

## Per-file census (`Zeta2Lean/Window/`)

| file | theorem : Stmt | deps (hypotheses) | sorry | difficulty | status |
|---|---|---|---|---|---|
| `Defs.lean` | definitions + API (`admissible_cfgW`, `window_cfgW`, `muSum_cfgW`, `Delta_pos`) | – | 0 | – | done |
| `PhiTable.lean` | data: 2602 pieces (generated) | – | 0 | – | done |
| `Statements.lean` | 18 `Stmt_*` + `MainStatement` (`Stmt_AuxPrime` replaces `Stmt_L20Nonzero`) | – | 0 | – | done |
| `Assembly.lean` | `main_of_stmts`, `Fn_frequently_ne_zero`, Dirichlet and `ℓ`-adic helpers | – | 0 | – | done |
| `Main.lean` | wiring, `PNT_window`, the two main theorems | – | 0 | – | done |
| `Proofs/ZetaReal` | `ZetaReal_proof : Stmt_ZetaReal` | – | 0 | 1 | **done** |
| `Proofs/PhiData` | `PhiData_proof : Stmt_PhiData` | – | 0 | 1 | **done** (`decide +kernel` on ℕ; fixed-point bound, round 1) |
| `Proofs/Criterion` | `Criterion_proof : Stmt_Criterion` | – | 0 | 2 | **done** (round 1) |
| `Proofs/Harmonic` | `Harmonic_proof : Stmt_Harmonic` | – | 0 | 2 | **done** (round 1) |
| `Proofs/OmegaPhi0` | `OmegaPhi0_proof : Stmt_OmegaPhi0` | – | 0 | 2 | **done** (round 2) |
| `Proofs/LaurentSupport` | `LaurentSupp_proof : Stmt_LaurentSupp` | – | 0 | 2 | **done** (round 2) |
| `Proofs/BrickIntegral` | `BrickInt_proof : Stmt_BrickInt` | – | 0 | 3 | **done** (round 2) |
| `Proofs/BrickValuation` | `BrickVal_proof : Stmt_BrickVal` | – | 0 | 3 | **done** (round 2; Taylor-coefficient form, `N < p²`) |
| `Proofs/LaurentIntegral` | `LaurentInt_proof : Stmt_LaurentInt` | BrickInt, LaurentSupp | 0 | 3 | **done** (see 2026-09-26 section) |
| `Proofs/LaurentValuation` | `LaurentVal_proof : Stmt_LaurentVal` | BrickVal | 0 | 3 | **done** (see 2026-09-26 section) |
| `Proofs/CoeffVanish` | `CoeffVanish_proof : Stmt_CoeffVanish` | PF | 0 | 3 | **done** (round 2 re-run) |
| `Proofs/PartialFractions` | `PF_proof : Stmt_PF` | – | 0 | 4 | **done** (round 2 re-run) |
| `Proofs/LinearForm` | `LinearForm_proof : Stmt_LinearForm` | PF, CoeffVanish | 0 | 4 | **done** (round 2 re-run) |
| `Proofs/Lemma19` | `Lemma19_proof : Stmt_Lemma19` | LaurentSupp, LaurentInt, LaurentVal, Harmonic | 0 | 4 | **done** (round 2 re-run) |
| `Proofs/DenomGrowth` | `DenomGrowth_proof : Stmt_DenomGrowth` | PNT, OmegaPhi0, PhiTable, PhiData | 0 | 4 | **done** (robust-route round 1) |
| `Proofs/PhiTable` | `PhiTable_proof : Stmt_PhiTable` | – | 0 | 5 (computer-assisted) | **done** (robust-route round 1) |
| `Proofs/Lemma20Upper` (+ `Proofs/L20U/*`) | `L20Upper_proof : Stmt_L20Upper` | PF, CoeffVanish, LinearForm | 0 | 4 | **done** (Theorem U, robust-route round 1) |
| `Proofs/AuxPrime` | `AuxPrime_proof : Stmt_AuxPrime` | LaurentSupp, LaurentInt, LaurentVal, Harmonic | 0 | 3 | **done** (Theorem N, robust-route round 1) |

All the Mathlib names cited in the stub docstrings were `#check`ed and exist in this Mathlib; two
wrong names were corrected (and one more, `Nat.Coprime.lcm_right`, by the restater).
`scripts/audit.sh` finds no forbidden construct.

## Restatement to the robust route (window restater), 2026-09-26

The PC crashed at 02:10; no uncommitted work was left in the tracked files (`git status` clean at the
start). The restater switched the formalisation to route R2 of `docs/window/proof_v2.md` (now
`docs/proof.md`) §6 (Zudilin's Lemma 19, Theorem U, Theorem N).

* **Why.** `Stmt_L20Nonzero` (unconditionally, `F̃_n ≠ 0` infinitely often) needs the saddle-point
  asymptotics of proof.md §3.4–3.6 (Olver's theorem, `ω/π ∉ ℤ`, positive density). proof_v2 replaces
  it by Theorem N (track `aux-prime-nonvanishing`): at `ℓ = 63n - 1` prime, `v_ℓ(c₀) = -5 < 0 ≤ v_ℓ(c_s)`,
  which makes `d Δ_n F̃_n` a non-zero integer under the rationality hypothesis. The upper bound is
  Theorem U (track `crude-upper-bound`): `|F̃_n| ≤ K n^{16} e^{-750.618 n}` for every `n ≥ 1` from
  pointwise bounds on the contour `Re t = 1/2 - n` and ≈ 300 certified `log`/`arctan` enclosures, so
  `Stmt_L20Upper` holds for `n ≥ 74`.
* **Statement changes** (`git diff`: `Statements`, `Assembly`, `Main`, the two stubs; `Defs` and
  `PhiTable.lean` untouched; every other `Stmt_*` unchanged).
  * `Stmt_L20Nonzero` is removed. New:
    `Stmt_AuxPrime := ∀ᶠ n in atTop, Even n → (63 * n - 1).Prime →
      padicValRat (63 * n - 1) (A0 cfgW n) < 0 ∧ ∀ s ∈ window cfgW, 0 ≤ padicValRat (63 * n - 1) (Acoef cfgW n s)`.
    This is the weakest separation the assembly needs (Theorem N gives `= -5`). It is eventual, so a
    proof may take `ℓ > num(Q₁) = 984698059590803` instead of certifying that this numerator is
    prime (the pair project's `Nonvanishing.lean` does the same with `q > 10⁹`).
  * `Stmt_L20Upper` unchanged (`C0lo = 748.1`); `Stmt_Criterion` unchanged (it is still the
    workhorse). Only docstrings changed.
  * `main_of_stmts : … → Stmt_DenomGrowth → Stmt_L20Upper → Stmt_AuxPrime → MainStatement`. New,
    complete, in `Window/Assembly.lean`: `AssemblyAux.auxPrime_frequently` (Dirichlet: Mathlib's
    `Nat.forall_exists_prime_gt_and_modEq` with modulus 126 and residue 125, `n = (p+1)/63`),
    `padicValRat_nonneg_of_not_dvd_den`, `padicValRat_mul_nonneg`, `padicValRat_sum_nonneg`,
    `neg_add_sum_ne_zero`, and `Fn_frequently_ne_zero` (if the window values `zetaR s = q_s` are all
    rational, then `F̃_n ≠ 0` for the large even `n` with `63n - 1` prime, because
    `ℓ > ∏ den q_s`). Inside the proof by contradiction this supplies the last hypothesis of
    `Stmt_Criterion`.
  * `Window/Main.lean`: `zeta_7_to_21_not_all_rational_of_lemma20 (hU) (hN)` became
    `zeta_7_to_21_not_all_rational_of_L20Upper (hU)`. The target theorem
    `zeta_7_to_21_not_all_rational` keeps its name and statement.
  * `Proofs/Lemma20Nonzero.lean` → `Proofs/AuxPrime.lean` (`git mv`):
    `AuxPrime_proof (hLS : Stmt_LaurentSupp) (hLI : Stmt_LaurentInt) (hLV : Stmt_LaurentVal)
    (hH : Stmt_Harmonic) : Stmt_AuxPrime`, with Theorem N written out in the Lean normalization
    (`c₀ = -A0`, `c_s = Acoef s`, `a_{i,k} = B (i+5) k`), and Lean hints.
  * `Proofs/Lemma20Upper.lean`: `L20Upper_proof (hPF : Stmt_PF) (hV : Stmt_CoeffVanish)
    (hLF : Stmt_LinearForm) : Stmt_L20Upper`. These three proved statements are the bridge from `term`
    (a power-series coefficient) to complex analysis, as in the pair project's
    `Growth_proof (hPF) (hV)`. The docstring now gives Theorem U (L1–L5, constants, porting table).
  * Copied from the research session: `docs/window/proof_v2.md` (now `docs/proof.md`),
    `docs/window/final_check_v2.{py,log}`
    and `docs/window/refine/` (the three track write-ups, the Theorem U certificate
    `certificate_exact_x159_p181_20_Y60.json` with its certifier, the `Q₁` constants; index in
    `docs/window/refine/README.md`).
* **Checks of the new statement in the Lean normalization** (`python/window_mirror.py`, new section
  "Stmt_AuxPrime", `--aux` runs it alone):
  * literal exact `A0 cfgW n`, `Acoef cfgW n s` (the mirror's `Form`, `Fraction` arithmetic):
    `n = 4` (`ℓ = 251`, 154 s) and `n = 8` (`ℓ = 503`, 1195 s, separate run): `v_ℓ(A₀) = -5` and
    `v_ℓ(A_7, A_9, …, A_21) = (1, 1, 0, 0, 2, 4, 8, 10)`, the pattern the track reported for every
    `n ≤ 2994`;
  * an `ℓ`-adic evaluation of the same definitions modulo `ℓ^30` (`aux_padic`: the literal brick
    products, with every inverted constant asserted to be an `ℓ`-unit) agrees with the exact values
    modulo `ℓ^30` at `n = 4` and `n = 8`, and gives the same valuations for all 14 even `n ≤ 60` with
    `63n - 1` prime (`n = 4, 8, 14, 20, 24, 26, 30, 34, 36, 38, 46, 48, 56, 60`), with `A_5` and the
    even `A_s` vanishing modulo `ℓ^30`; full mirror run 415 069 checks, 0 failed (684 s);
  * exact at `n = 4, 8`: `X^{16} ∣ Gk` at `k = 110n, 110n+1`, `v_ℓ(B_{7,k}) = 1`, `v_ℓ(B_{6,k}) = 0`,
    `B_{7,110n}/B_{7,110n+1} = ρ(110n+1)` (Lemma E), `ℓ⁵ A₀ ≡ -4(u_{110n} + u_{110n+1}) ≡
    -4 Q₁ u_{110n+1} (mod ℓ)`; `ω_{k,ℓ} = 17` at both top poles, so `Stmt_LaurentVal` already gives
    `v_ℓ(B_{7,k}) ≥ 1`;
  * Lean's `Δ_n` has `v_ℓ(Δ_n) = 6` at these primes (`m₁ = m₂ = 63n ≥ ℓ > m₃ = 62n`, `Φ_n` only has
    primes `≤ 60n`), so `v_ℓ(Δ_n A₀) = 1`, as in the track's §6 table. The assembly does not need
    this value.
* **Build.** `bash scripts/build.sh Zeta2Lean.Window.Main`: green, 8961 jobs; axioms as in the
  headline. The assembly was first checked against the old build in a scratch file.
* **Refined Lemma 19 (proof_v2 H′, `C₂′ ≤ 729.05`) is not adopted.** It would need a new denominator
  `D_n` and new per-pole/flat-pole arithmetic statements. `Stmt_DenomGrowth` and `Stmt_PhiTable` would
  not get easier, because the proved `Stmt_PhiData` and `C2hi = 748 < C0lo = 748.1` already close the
  argument. It remains the fallback if a margin larger than 0.1 in the Lean constants is ever needed.
* **Partial work of the interrupted round-3 provers** (git-ignored scratch files, not part of the
  repository; untouched by the restater):
  `Zeta2Lean/Scratch/dg_main.lean` (721 lines), `dgB_main.lean` (233), `dg_api.lean`, `dgB_ps.sh`
  (DenomGrowth, last modified 02:04) and `phitable_a.lean` … `phitable_g.lean` (PhiTable checker
  experiments, last modified 02:02). They contain no `sorry` but no finished proof either. The next
  DenomGrowth and PhiTable provers should start from them.

### Open files after the restatement (all hypotheses proved; can run in parallel)

| file | concrete task | hypotheses | informal source | template |
|---|---|---|---|---|
| `Proofs/PhiTable.lean` | a kernel-evaluable checker `pieceOK`, its soundness `pieceOK e = true → PieceValid cfgW e`, and `phiTable.all pieceOK = true` by `decide +kernel` (split along `phiTable0 … phiTable5`) | – | proof.md §2; `python/window_phitable.py` | docstring design; scratch `phitable_*.lean` |
| `Proofs/DenomGrowth.lean` | `Δ_n ≤ e^{748 n}` eventually: `log Dprod ≤ (1+δ) 1341 n` (PNT for ψ), `log Φ_n ≥` the table sum (`θ` in the intervals `n/(b+m) < p < n/(a+m)`, `ω_p ≥ v` by `OmegaPhi0` + `PhiTable`), `1341 - phiSumQ < 748` (`PhiData`) | PNT, OmegaPhi0, PhiTable, PhiData | JTNB Prop. 5; proof.md §2 | parent `Proofs/Asymptotics.lean`; scratch `dg_main.lean`, `dgB_main.lean` |
| `Proofs/Lemma20Upper.lean` | Theorem U: contour representation (L1), kernel bound on half-integer lines (L2), window comparison (L3), pointwise bound (L4), landscape on `x₀ = 159` with the certified enclosures (L5), assembly; any `C₀' > 748.1` suffices | PF, CoeffVanish, LinearForm | `docs/window/refine/crude-upper-bound.md` | pair `Growth.lean` + `Landscape/` |
| `Proofs/AuxPrime.lean` | Theorem N: `ℓ`-integrality of every `B_{j,k}` (`LaurentInt`, `m₀ = 60n < ℓ`), the two top poles `110n, 110n+1` (`Gk = X^{16} V_k`, one `ℓ`-divisible factor in `P₅`), the principal part `ℓ⁵ A₀ ≡ -4 ∑ u_k`, the telescoping ratio mod `ℓ` (`63n ≡ 1`), and `ℓ > num(Q₁)` | LaurentSupp, LaurentInt, LaurentVal, Harmonic | `docs/window/refine/aux-prime-nonvanishing.md` | pair `Nonvanishing.lean` (`NVq`) |

## Round-2 (re-run) integration (window integrator), 2026-09-26

* Provers changed only `Proofs/PartialFractions.lean`, `Proofs/CoeffVanish.lean`,
  `Proofs/LinearForm.lean` and `Proofs/Lemma19.lean` (`git diff --stat`: +1890/−108 in those four
  files). `git diff HEAD` of `Defs`, `Statements`, `Assembly`, `Main` and `PhiTable.lean` was empty
  before the integrator's edit. In each file the `theorem …_proof … : Stmt_*` signature is identical
  to `HEAD`, and every import is still only `Zeta2Lean.Window.Statements`. The only integrator edit is
  four `#print axioms` lines in `Main.lean`. No compile break needed fixing.
* Full build green (8961 jobs). All four new proofs print `[propext, Classical.choice, Quot.sound]`.
  Audit: 4 sorries (`DenomGrowth`, `PhiTable`, and the 2 `lemma20` gaps), no forbidden construct, and
  no `set_option maxHeartbeats` or `decide` in the new files.
* Statement issues reported: none (`[]`), so there was nothing to adjudicate with the mirror. The
  statements were already mirror-checked in round 0 (414 992 checks) and by both audit passes
  (`Stmt_PF` literally in ℚ⟦X⟧ at 36 points; `CoeffVanish` and `Lemma19` on 14 random admissible
  configurations). They are now theorems for every admissible configuration.
* Verdicts on the informal-mathematics reports (all accepted; the integrator re-derived each claim):
  * `PartialFractions`: no issue. The prover multiplies by the uniform W = ∏_K (t+k)^{q−r} instead of
    using the exact pole orders μ_k. The (j,k) terms with B = 0 are then harmless, which simplifies
    blueprint step 3 without changing the statement. The degree formula
    deg R̃ = 1 + r − q − (q−r)η₀n + 2nΣη_j ≤ 1 + r − q − 2rn under (8.1) was recomputed: for `cfgW`,
    Ση_j = 4·47 + 48 + 2·50 + 51 + (52+…+66) = 1272, so deg R̃ = −17 − 2880n + 2544n = −336n − 17. This
    matches the blueprint's erratum to proof.md §1 and the first audit pass (−353 at n = 1).
  * `CoeffVanish`: no issue. The signs were re-derived:
    * the rational-brick sign is (−1)^{h₀−2h_j};
    * the total sign is −(−1)^{(q−r)h₀} = −1, because q − r = 18 is even;
    * the final sign is −(−1)^{q−j} = (−1)^j, because q = 23 is odd.

    The residue-sum argument needs deg R̃ ≤ −2, which holds with a margin of 336n + 15. `symm` holds
    for every k ≤ h₀ and every n, so the statement is stronger than needed and not vacuous.
  * `LinearForm`: no issue. Every ingredient is now kernel-checked for every admissible
    configuration:
    * [εᵐ](a+ε)^{−s} = (−1)ᵐ C(s+m−1, m) a^{−s−m};
    * the order-r zeros at t = −1, …, −(h₁−1);
    * the H_{k−h₁} cut-off;
    * A_r = 0 (residue sum), and even A_s = 0 (sign (−1)^{s+1} = −1).

    The formal route avoids the blueprint's identity H_{k−1} − H_{k−h₁} = Σ_{l<h₁} (k−l)^{−w}. As a
    by-product, it confirms the audit's numerical observation that A₀ is the same with either cut-off.
  * `Lemma19`: no issue. The rough part uses D_{m₀}^{q−j} D_{m_{j−r}}^{j−1} | Dprod. This holds
    because m₀ ≤ m_{q−r} ≤ … ≤ m₁, and B_{j,k} ≠ 0 forces k − h₁ ≤ m_{j−r}. The p-adic part only needs
    v_p(Dprod) ≥ q − 1 for p ≤ m_{q−r}, and the two bounds add up exactly:
    * v_p(B) ≥ ω_p − (q−j);
    * v_p(H^{(j−1)}_{k−h₁}) ≥ −(j−1), since k − h₁ < h₀ < p², so only multiples p·i with i < p occur.

    Lean's ω_p (the minimum over a full residue class system, with periodicity proved) agrees with
    JTNB's range minimum for `cfgW` at every prime of Φₙ, because the range has 60n + 1 ≥ p + 1
    elements. The same was checked numerically in audit pass 2, so `DenomGrowth`'s C₂ is unaffected.
    Nothing uses r = 3.
* The mathematical risk now sits only in `DenomGrowth`/`PhiTable` (PNT + the φ-table certificate; the
  table data are already verified, the open part is the Lean proof that the pieces bound φ and the
  PNT-to-Φₙ step) and in the `lemma20` gap.

## Round-1 re-integration (window integrator, workflow re-run "Try again"), 2026-09-26

* The four round-1 reports (`ZetaReal`, `PhiData`, `Criterion`, `Harmonic`: complete, 0 sorry) had already
  been integrated in commit `2d4bc72`. `git diff 2d4bc72 HEAD` on those four files is empty, so this
  re-run integrated the same, unchanged content.
* **Working-tree finding.** At the start of this run, `Proofs/LaurentIntegral.lean` and
  `Proofs/LaurentValuation.lean` had uncommitted, complete proofs. They were last modified on
  2026-09-25 at about 23:30, most likely by round-3 provers of the interrupted earlier run. No Lean
  process was running. The integrator verified them before committing:
  * each file's `theorem … : Stmt_*` line is byte-identical to `HEAD`;
  * `git diff HEAD` of `Defs`, `Statements`, `Assembly`, `Main` and `PhiTable.lean` is empty;
  * the full build is green;
  * both proofs print `[propext, Classical.choice, Quot.sound]` (two `#print axioms` lines added to
    `Main.lean`, the only integrator edit);
  * the audit finds no sorry in either file and no forbidden construct.

  Their informal content matches JTNB (8.10) and (8.11):
  * `LaurentInt`: the `D_{m₀}`-integral subring, bricks from `Stmt_BrickInt`, with `a₀ = h_{r+1}` and
    `b₀ = h₀ − h_{r+1} + 1` for the rational bricks;
  * `LaurentVal`: the tame-weight calculus. The brick weights sum *exactly* to `ω_{k,p}`, with JTNB
    (7.5) applied twice for the `Q`-bricks.

  Neither uses r = 3. `Stmt_LaurentVal` is the Taylor-coefficient form under `h₀ < p²`, which is
  consistent with the round-2 verdict on `BrickValuation`.
* Statement issues: none reported (`[]`), so there was nothing to adjudicate with the mirror.
* Verdicts on the informal-mathematics reports (all accepted):
  * `ZetaReal`: no issue (Mathlib bridge `ζ(s) = Σ m^{-s}`, s ≥ 2).
  * `PhiData`: no issue, recomputed.
    * `C₂ = 1341 − ∫φ/x²`, where `1341 = 5·63 + 63 + 62 + 61 + 14·60` (the exponents of `Δₙ`), and
      `∫φ/x² = 593.9487` gives `C₂ = 747.0513`.
    * The certified table sum `593.5146` gives `C₂ ≤ 747.4854 < C2hi = 748`.
    * The difference `0.4341 ≈ φ̄/21` is the tail of the translates, and it enters on the safe side.
  * `Criterion`: no issue (JTNB Prop. 5, elementary part; uses only `c2 < c0`, and `C2hi = 748 <
    C0lo = 748.1`).
  * `Harmonic`: no issue (the `val` field is proved without the `H ≠ 0` hypothesis).
* The mathematical risk is unchanged. It is in the `lemma20` gap and in the remaining stubs:
  * `DenomGrowth` and `PhiTable` (φ-certificate + PNT);
  * `PF`, `CoeffVanish` and `LinearForm` (the linear form);
  * `Lemma19` (assembly of the Laurent pieces, all of whose inputs are now proved).

## Prove round 2: integration (window integrator), 2026-09-25

* Provers changed only `Proofs/OmegaPhi0.lean`, `Proofs/LaurentSupport.lean`,
  `Proofs/BrickIntegral.lean` and `Proofs/BrickValuation.lean` (`git diff`). `Defs`, `Statements`,
  `Assembly`, `Main`, `PhiTable.lean` and every `Stmt_*` are unchanged. `BrickInt_proof` and
  `BrickVal_proof` are now given with `where` (the `Stmt_*` are structures), with the same type. The
  integrator added only four `#print axioms` lines to `Main.lean`. No compile break needed fixing.
* Full build green (8961 jobs); all four new proofs print `[propext, Classical.choice, Quot.sound]`;
  audit: 10 sorries (8 stubs + 2 gaps), no forbidden construct.
* Statement issues reported: none. Two provers noted that their statement is *stronger* than needed:
  * `BrickInt.poly` never uses `b ≤ a`;
  * `pb_mem` gives JTNB Lemma 15 at every integer shift.

  That is harmless, so there was nothing to adjudicate with the mirror (it passed 414 992 checks of
  these `Stmt_*` in round 0).
* Verdicts on the informal-mathematics reports (all accepted; none changes the analysis):
  * `OmegaPhi0`: no issue. `omegaKP` = JTNB (8.9) and `phi0` = JTNB's φ₀ (p. 283) term by term. The
    identity ω_{k,p} = φ₀(n/p, (k−1)/p) under h₀ = η₀n+2, h_j = η_j n+1 is now kernel-checked for every
    configuration and every p. The residue-class-minimum convention of `omegaP` versus JTNB's range
    minimum was already documented (audit pass 1) and is never larger, so the bound is safe.
  * `LaurentSupport`: no issue. The P_j Q_j bricks (j ≤ r) cancel their poles. The pole order at −k is
    #{i > r : h_i ≤ k ≤ h₀−h_i}, an initial segment because η is sorted. It is proved from `eta_mono`
    alone.
  * `BrickIntegral`: no issue. The route is more elementary than JTNB's (a Pascal induction for the
    polynomial bricks, and a uniqueness characterisation plus a telescoping recurrence for the rational
    bricks). It independently confirms JTNB Lemmas 15 and 16 for all parameters, and nothing depends
    on r = 3.
  * `BrickValuation`: **the remark is confirmed, and the formalization has no gap.** JTNB 2004
    (Lemma 17) states the bound for ord_p R^{(j)}(−k), with hypothesis
    p > a₀ − b₀ − 1. The Leibniz step (8.11) for B_{j,k} needs the Taylor coefficients R^{(j)}/j!,
    which differ by ord_p(j!).
    * Lean's `Stmt_BrickVal` states the Taylor form, under the weaker hypothesis N < p² that Lemma 19
      needs (primes p > √h₀).
    * The proof tames each linear factor: 1/(c+ε) has coefficients of valuation ≥ −v_p(c) − i when
      v_p(c) ≤ 1, and tameness is multiplicative.
    * The integrator re-derived this argument, and it is correct.
    * Literal JTNB matches the Taylor form only when p > (max derivative order) = q − r − 1 = 17. For
      `cfgW`, the primes in (√h₀, 17] exist only at n = 1 (h₀ = 162: p = 13, 17). So the literal
      derivation has at most a finite-n gap, which is asymptotically irrelevant. The Lean statement
      covers every n.

## Prove round 1: integration (window integrator), 2026-09-25

* Provers changed only `Proofs/Criterion.lean`, `Proofs/Harmonic.lean` and `Proofs/PhiData.lean`
  (`git diff`). `Defs`, `Statements`, `Assembly`, `PhiTable.lean` and every theorem statement are
  unchanged. `ZetaReal` was already done and was not touched. The integrator added only two
  `#print axioms` lines (`Criterion_proof`, `Harmonic_proof`) to `Main.lean`.
* Full build green; the axioms are as listed in the headline; audit: 14 sorries, no forbidden construct.
* The provers reported no statement issues. There was nothing to adjudicate with the mirror.
* Verdicts on the provers' informal-mathematics reports (all accepted, and none changes the analysis):
  * `ZetaReal`: no issue. It is the standard bridge `ζ(s) = Σ m^{-s}` (s ≥ 2) from Mathlib.
  * `PhiData`: no issue. The new proof is sound by construction: `fxSum_le` (each floor ≤ the exact
    term, `Nat.cast_div_le`) plus the kernel-evaluated `fxSum phiTable 60 20 > 593.5146·10¹²`. The
    reported gap `593.9487 − 593.5146 = 0.4340 ≈ φ̄/21` is the tail beyond the 20 translates, as
    expected. The certified bound is `C₂ ≤ 747.4854 < C2hi = 748`.
  * `Criterion`: no issue. The proof is the textbook argument (common denominator `d = ∏ den q_s`, and
    the integer `d Δₙ Fₙ` with `|·| < 1`). It uses only `c2 < c0`. The constants `C2hi = 748 <
    C0lo = 748.1` keep a margin of 2.6 below the true `C₀ = 750.71` for the `lemma20` gap.
  * `Harmonic`: no issue. `val` is proved without its `H ≠ 0` hypothesis, since the bound `−s ≤ 0 =
    v_p(0)`, so the statement is stronger than needed and not vacuous.
* The mathematical risk is unchanged. It sits in the `lemma20` gap (Olver saddle point + certified
  landscape) and in the remaining non-gap stubs (DenomGrowth / PhiTable being the heaviest).

## Adversarial audit (window), 2026-09-25

### First pass (its commit was lost in the WSL crash; files recovered from the working tree)

**Verdict: consistent.** Two documentation claims were corrected; no statement changed. No statement
is false, vacuous or junk-dependent. The main statement is faithful and uses only Mathlib notions, and
`main_of_stmts` really derives it from the `Stmt_*`. Every load-bearing number was recomputed with the
auditor's own code in `python/window_audit/` (logs next to the scripts). That code does not reuse the
mirror, `vz.py` or `zud_exact.py`, and `run_all.py` regenerates everything in about 20 minutes.

*Lean side.*
* Junk values:
  * every ℕ-subtraction is non-truncating under `Admissible` and `1 ≤ n`;
  * `/` on ℤ is floor division for `p > 0` (checked by `decide`);
  * every power-series inverse used has a non-zero constant term;
  * `Fn` is a `tsum`, but `Stmt_LinearForm` asserts `HasSum`;
  * `ad = 0` / `bd = 0` in the table are excluded by `PhiData.bounds`.
* `#print axioms PNT_window` is now printed in `Main.lean`: `[propext, Classical.choice, Quot.sound]`.
* `Fn cfgW n` is JTNB's F̃ₙ, so the two gap statements concern the right object:
  * the literal Lean series `∑_{t≤700} [ε⁴] Rser(t)` equals the exact linear form to relative
    `1.2e-259` (n = 1);
  * the Lean brick coefficients `B` equal Laurent coefficients computed by a different method (power
    sums and a series exponential) for n = 1, 2;
  * the Barnes integral (own contour code) matches the exact F̃ₙ to `4e-14` (n = 2, 3).
* The generic statements hold beyond `cfgW`. They were tested on 14 admissible configurations at
  n = 1, 2, with 0 failures:
  * the configurations are random, plus edge cases: equality in `deg_cond`, all η equal, and
    m₀ = h_r − 1 dominating;
  * checked: `B`, `LaurentSupp`, `CoeffVanish`, the set of occurring ζ = `window`, `A0` with
    H_{k−h₁} equal to the version with H_{k−1}, `Lemma19`, `LaurentInt` and `LaurentVal`.
* `Stmt_PF` was checked literally in ℚ⟦X⟧, exactly on the first 6 coefficients, at 36 non-pole points
  (integers, zeros `y = -l`, fractions, points inside the pole range) in 4 configurations: 0 failures.
* `BrickInt`, `BrickVal`, `Harmonic` and `OmegaPhi0` pass 15 029 random checks with 0 failures.
  Lean's `omegaKP` agrees with the Python value on a sample (`#eval`).
* Doc fix in `Defs.lean` (`omegaP`): the docstring said Lean's ω_p equals JTNB's range minimum for
  every configuration. That holds for `cfgW` (m_{q−r} = h₀ − 2h_{r+1} = 60n) but not in general.
  Lean's value is never larger, so no statement is affected.
* Doc fix in `BLUEPRINT_WINDOW.md`: the greedy piece count for C2hi = 750.6 is 1878 with K = 20, not
  about 1830. The conclusion (a crude certificate is not enough) is unchanged.

*Mathematics (claimed → recomputed).*

| quantity | claimed | auditor |
|---|---|---|
| m/n, `muSum` | (63,63,62,61,60¹⁴), 1341 | same (from the definitions) |
| ∫_{1/60}^∞ φ dx/x² | 593.94869421032569 | 593.94869421032572 (Farey-160 superset of breakpoints, exact per piece) |
| C₂ | 747.0513057896743 | 747.0513057896743 |
| `phiSumQ` (M = 60, K = 20); certified C₂ bound | 593.5146378485; 747.4854 | 593.5146378485069; 747.4853621515 (the table has 0 violations, and every piece is checked at all interior Farey-160 points) |
| τ₃ | 159.35641805379484 + 8.393712372068762 i | 159.3564180537948306 + 8.3937123720687621 i (all 27 roots of P, Zudilin's max-Re rule picks the same root) |
| f″(τ₃) | 0.272122458999 + 0.542987421932 i | same |
| C₀ | 750.7116948339443 | 750.71169483394431 |
| ω/π | −466.6133574734306 | −466.6133574734306 |
| C₀ − C₂ | 3.6603890443 | 3.66038904427 |
| λ = 1 branch | subdominant, sup u₁ ≤ −754.606 on the line | saddles at Re f₀ = −786.61; sup u₁ = −766.47 at y = 0.447 |
| u₃ on the line | unique max at y*, gaps −0.0084/−0.134/−0.529/−3.196 | the same; unimodal on a 0.1-grid of [−300, 300] |
| log\|F̃₁\|, log\|F̃₂\|, log\|F̃₃\| | −799.4450029421, −1559.4383100008, −2314.2272525205 | −799.4450029421402, −1559.438310000763, −2314.227252520493 |
| signs n = 1..9 | + + − + + − − + − | same (own contour) |
| Stirling prefactor n⁻¹³A(τ)e^{nΦ₃} | relative error O(1/n) | n·\|error\| = 0.14897 → const (n = 25…800) |
| leading term (F) | ratio → 1 | exact/lead = 0.902, 0.950, …, 0.988 (n = 1..9); 0.9888, 0.9951, 0.9979, 0.99923 (n = 12, 20, 50, 100) |
| log Δₙ/n | 832.9, 803.1, 785.3, 780.5 (n = 5..40) | the same values, then 769.7, 761.6, 756.2, 755.0 (n = 80..640) → 747.05 slowly (the p ≤ √h₀ cutoff drops x ≥ √(n/160)) |
| deg R | −336n − 17 (blueprint erratum to proof.md) | −353 at n = 1, confirmed |
| greedy piece count, C2hi = 750.6 | ≈ 1830 | 1878 with K = 20 (the conclusion is unchanged) |

The ratios in proof.md §5 (1.095, 0.948, …) divide by the finite-n Gamma prefactor at the saddle. The
ratios above divide by the limit formula (F) itself. Both are consistent (the prefactors differ by
0.149/n).

No mathematical error was found. Lemma 20 remains the only unverified input. Its ingredients check
out numerically to high accuracy (Barnes representation, branch split, Stirling, landscape, Laplace
leading term, ω/π ∉ ℤ). A rigorous proof still needs Olver's saddle-point theorem and certified
interval numerics.

### Second independent pass (auditor 2, after the WSL crash), 2026-09-25

**Verdict: consistent, and the first pass is confirmed.** No statement changed. This pass used its own
code in `python/window_audit/indep2/` (list and commands in `run_indep2.py`). That code does not
import the mirror, the first-pass scripts or `docs/window/*.py`.

*Lean side.*
* The pass re-derived the truth of all 18 `Stmt_*` for every admissible configuration: bricks and
  tame weights (JTNB (7.5)), pole support, the symmetry sign `-(-1)^{r(h₀-1)+q(h₀+1)} = -1`,
  `deg R = 1-r-q+(r-q)h₀+2Σh_j ≤ 1-r-q` under `deg_cond`, the `H_{k-h₁}` cut-off, and the
  large/small-prime split of Lemma 19.
* Junk values and vacuity: no finding beyond the first pass. The two gap hypotheses are satisfiable
  as far as numerics can tell (`F̃ₙ ≠ 0` and `log|F̃ₙ|/n ≤ -751.8` for every computed `n`).
* `lean_eval_check.lean` (kernel evaluation, exit 0) checks the following for `cfgW`, n = 1:
  * `/` on ℤ floors;
  * `omegaKP` (three samples), `omegaP … 13 = 12`, `mj = (63,63,62,61,60¹⁴)`;
  * `PhiN cfgW 1` and `Dprod cfgW 1` equal the Python values, so Lean's `Delta cfgW 1` is the Δ₁
    checked below.
* `bash scripts/build.sh Zeta2Lean.Window.Main` is green after the crash. `scripts/audit.sh` reports
  16 sorries (14 stubs and 2 gaps) and no forbidden construct.

*Mathematics (auditor 2's values; all agree with the claims and with the first pass).*

| quantity | auditor 2 |
|---|---|
| τ₃; f″(τ₃) | 159.35641805379483058 + 8.39371237206876207 i; 0.27212245899864 + 0.54298742193169 i |
| C₀; ω/π (distance to ℤ) | 750.71169483394431368; −466.61335747343060 (0.38664) |
| λ = 1 saddle; line maxima | Re f₀ = −786.6102; on Re τ = x*: max u₃ = −C₀ at y*, max u₁ = −766.47 (y ≈ 0.45), u(0) = −767.130018 |
| breakpoints of φ | denominators (78 values, max 160) → 2645 points, i.e. 2644 intervals = the 2644 pieces of `vz.py` |
| ∫_{1/60}^∞ φ dx/x²; C₂ | 593.9486942103257158; 747.0513057896742842 |
| Lean table | 0 violations (every sub-interval, every interior breakpoint), phiSumQ = 593.5146378485069, 1341 − phiSumQ = 747.48536 < 748 |
| F̃ₙ, n = 1..9 (direct series `Σ_t [ε⁴] R̃(t+ε)`, no partial fractions) | all nine log\|F̃ₙ\| equal `exact_r5_q23_n9.jsonl` to 16 digits; signs + + − + + − − + − |
| linear form from the auditor's exact Laurent data | equals the direct series to 22 digits (n = 1, 2); A_s ≠ 0 exactly for s ∈ {7, …, 21} |
| Lemma 19, (8.10), (8.11), support | exact for n = 1, 2: Δₙ A₀, Δₙ A_s ∈ ℤ, slack 0 at most primes of Φₙ, 0 violations; JTNB's ω_p = Lean's ω_p at every prime of Φₙ |
| Barnes integral vs series | 3.7e−14, 4e−13, 2.1e−13, 1.4e−15 (n = 1, 2, 3, 5); V₅ identity to 1e−39 |
| exact (or contour) / leading term (F) | 0.9023, 0.9504, 0.9662, 0.9797 (n = 1, 2, 3, 5); 0.98876, 0.99506, 0.99792, 0.99923 (n = 12, 20, 50, 100); log\|F̃₁₀₀\|/100 = −751.80 |
| log Δₙ/n | 902.70, 844.72, 832.93, 803.06, 785.32, 780.53, 769.72, 761.63 (n = 1, 2, 5, 10, 20, 40, 80, 160) |
| greedy count, C2hi = 750.6 | 1878 with K = 20 and 1831 with all translates, so the original "about 1830" (K = ∞) and 1878 (K = 20) are both right |
| `python/window_mirror.py`, re-run after the crash | 414 992 checks, 0 failed (257 s) |
| first-pass scripts `bricks_random.py`, `random_cfg.py 7`, `pf_test.py W 1`, re-run | 15 029 checks, 0 failures; 14 configurations, 0 failures; `PF failures: 0` (the logs reproduce) |

*Remarks (no action needed).*
* P has two λ = 3 roots in the upper half-plane: τ₃ and its mirror `η₀ − conj τ₃ = 0.64358 + 8.39371 i`,
  with the same Re f₀. Only τ₃ lies on an admissible line (113 < Re τ < 160). Zudilin's max-Re rule
  picks τ₃, and proof.md §3.4 lists the mirror root correctly. The line argument (E) is unaffected.
* `Stmt_DenomGrowth` cannot be observed at accessible n. The cut-off `p² > h₀` omits about
  `φ̄ · √(160/n)` of the φ-integral, where `φ̄ = 9.114` is the mean of φ over a period. So
  `log Δₙ/n < 748` needs `n ≳ 1.5·10⁴`, before PNT fluctuations are counted. This is expected, since the
  theorem is ineffective, and it does not affect the eventual statement.

## What the theorems depend on once the stubs are proved

0. (2026-09-26: all stubs are now proved; both main theorems are axiom-clean.) Remaining stubs after the restatement (4) were: `PhiTable`, `DenomGrowth`, `AuxPrime` (arithmetic)
   and `Lemma20Upper` (analytic). None is a mathematical gap: each is proved informally in
   proof.md / proof_v2 with certified numerics.

1. The Lean kernel and Mathlib (`v4.35.0-rc2`), with the axioms `propext`, `Classical.choice` and
   `Quot.sound`.
2. `zeta_7_to_21_not_all_rational_of_L20Upper`: the analytic upper bound `Stmt_L20Upper` as its only
   hypothesis (once `PhiTable`, `DenomGrowth` and `AuxPrime` are complete).
   `zeta_7_to_21_not_all_rational`: nothing more once `L20Upper_proof` is complete as well.
3. Nothing else. PNT is proved in `Zeta2Lean/Cited`, Dirichlet's theorem is Mathlib's, and no project
   definition occurs in the statement.
