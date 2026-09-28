# The three refinement tracks behind `docs/proof.md`

Copies of the research-session folders `window-21-refine/<track>/` that `docs/proof.md` (called `proof_v2.md` during
the research) cites. Each `<track>.md` is that folder's `proof.md`; on 2026-09-26 its header was rewritten and the
research-session paths in it were replaced by the paths of this repository. The scripts are unchanged, so their
relative paths still refer to the session layout. Only the files that the Lean formalization cites are included.

| file | track | used by |
|---|---|---|
| `crude-upper-bound.md` | Theorem U: \|F̃ₙ\| ≤ K n¹⁶ e^{−C₀′n} for every n ≥ 1, contour Re t = ½ − n | `Stmt_L20Upper` (`Zeta2Lean/Window/Proofs/Lemma20Upper.lean`) |
| `certificate_exact_x159_p181_20_Y60.json` | every rational enclosure behind C₀′ and K (simple parameter set) | same (the Lean proof has its own certificate, `Zeta2Lean/Window/Proofs/L20U/Cert.lean`) |
| `certify_exact.py`, `ub_common.py`, `certify_exact.log` | the exact-rational certifier and its log (ALL CERTIFIED) | same |
| `aux-prime-nonvanishing.md` | Theorem N: v_ℓ(c₀) = −5 < 0 ≤ v_ℓ(c_s) at ℓ = 63n − 1 | `Stmt_AuxPrime` (`Zeta2Lean/Window/Proofs/AuxPrime.lean`) |
| `aux_constants.py/.log/.json` | the constants β, Q₁ (and Q_c for other c) | same |
| `check_ratio_exact.py/.log` | the telescoping ratio (5.1) as an exact rational identity | same |
| `refined-lemma19.md` | refined denominators, C₂′ ≤ 729.0513 (route R1) | not used (the Lean route is R2: Zudilin's Lemma 19, C₂ ≤ 747.49 < 748) |
| `margins.py/.json`, `c2exact.py`, `c2exact_q23_160.json` | the certified enclosure of C₂ and C₂′ | not used (context for `Stmt_PhiData`) |

`../final_check_v2.py` and `../final_check_v2.log` are the assembler's cross-track checks of `docs/proof.md` §5.
