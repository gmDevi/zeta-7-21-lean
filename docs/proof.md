# At least one of ζ(7), ζ(9), ζ(11), ζ(13), ζ(15), ζ(17), ζ(19), ζ(21) is irrational — informal proof

Assembled on 2026-09-25 by an AI agent acting as assembler and final referee (see `formalization.yaml`, automation).
It combines three tracks, `docs/window/refine/{refined-lemma19,aux-prime-nonvanishing,crude-upper-bound}.md`, each
checked by an independent verifier agent, with the definitions of the first version of the proof,
`docs/window/proof.md`. This file supersedes `docs/window/proof.md` as the reference. The first version remains a
valid, independent route with margin 3.66 (§6). The Lean docstrings call this file "proof_v2" or `docs/proof.md`.

> **Editorial note (2026-09-26, publication).** The Lean development of this repository formalises **route R2** of
> §6: Zudilin's Lemma 19 with the constant C₂ (not the refined Lemma 19 H′ of §2.1), Theorem U (§2.3) and Theorem N
> (§2.2), assembled as in §3. H′ and routes R1, R3 and R4 are not formalised. The Lean proof also proves what this text
> cites for route R2: Zudilin's Lemma 19 (for every admissible configuration and every prime), the vanishing of the
> ζ(5) and even-ζ coefficients, the prime number theorem, and the Stirling-type bound for N_h and the contour
> identities (from Mathlib's Stirling formula and Cauchy integral theorem); Dirichlet's theorem is Mathlib's. It
> uses weaker constants (|F̃ₙ| ≤ e^{−748.1n} and Δₙ ≤ e^{748n} eventually) and its own kernel-checked certificates;
> `README.md` lists the differences. The nonvanishing argument of §3 (steps 1–2) is an instance of the Archimedean
> auxiliary-prime criterion of L. Lai and J. Sprang (arXiv:2306.10393, Lemma 2.3). File names of the research
> session have been replaced by the paths of this repository; §11 says which supporting files are not included.

Labels:
- **PROVED**: the argument is written out here or in the named track file. Published results are marked *cited*.
- **CERTIFIED**: exact rational arithmetic and/or outward-rounded interval arithmetic, with the script named. These
  results are used by the proof.
- **NUMERICAL**: validation only. Nothing labelled NUMERICAL is used by the logic.

## 0. Result

**Theorem.** At least one of the eight numbers ζ(7), ζ(9), …, ζ(21) is irrational.

**Route R1.** Zudilin, JTNB 16 (2004) §8 forms with r = 5, q = 23, η₀ = 160, η = (47⁴, 48, 50², 51, 52, …, 66), plus
three ingredients:

| | ingredient | statement | track |
|---|---|---|---|
| H′ | refined Lemma 19 | an integer D_n with D_n c ∈ ℤ for every coefficient c, and log D_n ≤ C₂′n + o(n), where **C₂′ ≤ 729.051305789674284198128447044** | `refined-lemma19` |
| N | auxiliary-prime nonvanishing | if n is even and ℓ = 63n − 1 is prime, then v_ℓ(c₀) = −5 < 0 ≤ v_ℓ(c_s) for every s | `aux-prime-nonvanishing` |
| U | crude upper bound | \|F̃ₙ\| ≤ K n¹⁶ e^{−C₀′n} for **every** n ≥ 1, with **C₀′ ≥ 750.6183158756477496** (simple line) or **≥ 750.7116742473916946** (sharp line) | `crude-upper-bound` |

**Certified margin.**

  C₀′ − C₂′ ≥ **21.56701008597** (simple line) or ≥ **21.66036845771** (sharp line), per n.

`docs/window/proof.md` had 3.66039, a relative margin of 0.49 %. The new relative margin is 2.96 %.

**Status: PROVED modulo cited standard results, plus CERTIFIED computations.**
- The cited results are:
  - Zudilin's Lemma 19, used only for primes p ≤ √h₀ and for the vanishing of the ζ(5) and even-ζ coefficients;
  - the prime number theorem, which makes the o(n) ineffective, exactly as in Zudilin's Proposition 5;
  - Dirichlet's theorem;
  - Robbins' Stirling bounds;
  - Cauchy's integral formula.
- The certified computations are:
  - the enclosure of C₂′;
  - about 300 rational log/arctan enclosures behind C₀′ and K;
  - the exact constant Q₁ and the primality of its numerator.
- Verification: an independent verifier re-derived each of H′, N and U and recomputed it with its own code. All three
  verdicts are "confirmed with corrections", and every correction is cosmetic (§8). The assembler re-checked the points
  where the three tracks connect (§5).

**Parts of `docs/window/proof.md` that R1 no longer uses:**
- complex Stirling with remainders (step C);
- the location and certification of the saddle τ₃ (D);
- the landscape along the line through the saddle (E);
- Olver's saddle-point theorem (F);
- ω/π ∉ ℤ and the positive-density argument (G).

## 1. Setting (`docs/window/proof.md` §1; Zudilin (8.2)–(8.12))

For n ≥ 1 let h₀ = 160n + 2, h_j = η_j n + 1 and N_h = ∏_{j>5}(h₀−2h_j)! / ∏_{j≤5}((h_j−1)!)². Define

  R(t) = (h₀+2t)·(t+1)⁵_{h₀−1} / ∏_{j=1}^{23}(t+h_j)_{h₀+1−2h_j},   deg R = −336n − 17,
  F̃ₙ := N_h Σ_{t≥0} [ε⁴] R(t+ε) = N_h (1/4!) Σ_{t≥0} R⁽⁴⁾(t).

`docs/window/proof.md` §1 prints −336n − 4 for deg R; only deg R ≤ −2 is ever used. F̃ₙ is `Fn cfgW n` of the Lean
development (`Zeta2Lean/Window/Defs.lean`).

**Partial fractions.** The poles of R are t = −k with k ∈ K := [h₆, h₀−h₆] = [50n+1, 110n+1], of order
o_k = #{j>5 : h_j ≤ k ≤ h₀−h_j} − [2k = h₀]. Hence N_hR(t) = Σ_{k∈K} Σ_{i≤o_k} a_{i,k}(t+k)^{−i}.

**Linear form.** R⁽⁴⁾ vanishes at t = −1, …, 1−h₁, so the sum may start at t = 1−h₁ (Zudilin (8.6)). With w_i = C(i+3, 4)
and H_s(N) = Σ_{m≤N} m^{−s} this gives

  F̃ₙ = c₀ + Σ_{s=5}^{22} c_s ζ(s),  c_s = Σ_k w_{s−4} a_{s−4,k},  c₀ = −Σ_k Σ_i w_i a_{i,k} H_{i+4}(k−h₁).   (1.1)

**Vanishing coefficients** (Zudilin, Lemma 19; *cited*, elementary):
- c₅ = Σ_k a_{1,k} = 0, because the residues of R sum to zero when deg R ≤ −2;
- c_s = 0 for even s, by the symmetry R(−t−h₀) = −R(t).

So F̃ₙ ∈ ℚ + ℚζ(7) + ℚζ(9) + … + ℚζ(21).

H′ and N are statements about these same c₀ and c_s. The c₀ of the shifted sum (from t = 1−h₁) equals the c₀ of the
unshifted sum (from t = 0): the difference is Σ_{t=1−h₁}^{−1} N_hR⁽⁴⁾(t)/4! = 0.

The verifier of N checked the following in exact rationals for n = 1…30 (NUMERICAL):
- c₅ = 0;
- every even c_s = 0;
- shifted c₀ = unshifted c₀.

## 2. The three ingredients

### 2.1 H′: refined Lemma 19 (`docs/window/refine/refined-lemma19.md`)

**Notation.** Let p be a prime with p² > h₀ and let k ∈ K. Put:
- g_k(u) := N_hR(u−k)·u^{o_k};
- V_k := v_p(g_k(0)) and ν := v_p(N_h);
- far_k := [k − h₁ ≥ p];
- flat_k := [no l ∈ K∖{k} satisfies l ≡ k (mod p)].

Define E_k as follows:

| pole k | E_k |
|---|---|
| far | o_k + 4 − V_k |
| near, not flat | o_k − 1 − V_k |
| near, flat | min(o_k − 1 − V_k, −ν) |

The track also prints a separate flat-far formula, o_k+4−max(V_k, ν). It gives the same value, because V_k ≥ ν at
flat poles (verifier).

**Theorem H′1 (PROVED; refined §2).** v_p(c) ≥ −max(0, max_{k∈K} E_k) for every c ∈ {c₀, c₅, …, c₂₂}.

The proof has three lemmas:
- **Lemma A.** Each Taylor factor (1+u/d)^e with 0 < |d| < p² costs at most 1 per power of u.
- **Lemma B (flat poles).** Only the polynomial bricks P_j lose p-adic precision, and their total loss is ≤ −ν. This
  uses elementary symmetric functions and a max-plus product rule.
- **Lemma C.** v_p(H_s(N)) ≥ −s[N ≥ p] for N < p².

**The integer D_n.** Let e_p^{L19} be Zudilin's exponent (JTNB p. 281), and let e_p^{PP} and e_p^{BPP} be the bounds of
H′1 without and with the flat refinement. Put

  e_p := min(e_p^{L19}, e_p^{PP}, e_p^{BPP}) if p² > h₀,   e_p := e_p^{L19} if p² ≤ h₀,   D_n := ∏_p p^{max(0, e_p)}.

Then D_n c ∈ ℤ for every coefficient c, by H′1 and Zudilin's Lemma 19 (*cited* for p² ≤ h₀). The positive part avoids
the "Δ′ₙ ∣ Δₙ" wording that the verifier corrected (§8).

**Theorem H′4 (PROVED; refined §3; PNT).** log D_n ≤ C₂′n + o(n), where C₂′ := ∫₀^∞ Ψ_REF(1/u) du and
Ψ_REF = min(Ψ_L19, Ψ_PP, Ψ_BPP) is the continuum exponent. The primes contribute as follows:
- **p ≤ √h₀.** e_p^{L19} ≤ 22⌊log_p(63n)⌋, so these primes contribute O(√n).
- **p² > h₀, p ∤ n** (and p > η₀, which holds for n > 160). Two lemmas apply:
  - Lemma D: the pole order cancels, o_k − V_k = q − r − φ₀(n/p, (k−1)/p) − δ_k.
  - Lemma E: on the grid the exponent never exceeds the value of an adjacent open cell. Lines of different slopes do not
    meet on (1/p)ℤ.

  Together they give max(0, e_p) ≤ Ψ_REF(n/p). This uses Ψ_REF ≥ 0, which holds because φ ≤ 16 < 22.
- **p ∣ n.** e_p ≤ 22, so these primes contribute O(log² n).
- **The PNT** applied to the step function Ψ_REF(1/u) (finitely many steps on [ε, 63], zero for u > 63) gives the main
  term C₂′n.

**Value (CERTIFIED; `c2exact.py` → `c2exact_q23_160.json`, `margins.json`).**
- Ψ_REF ≤ Ψ_L19 holds everywhere, and on u ∈ [30, 63] the exact computation gives ∫(Ψ_L19 − Ψ_REF)(1/u) du = **18**.
  Only this upper-bound direction is used, so the "support of G" claim in refined §3 is not needed.
- The gain pieces are [46,47], [51,160/3] and [56,63]. The flat refinement contributes [61,63]; the per-pole bound alone
  gives 16.
- C₂ = 1341 − ∫_{1/60}^∞ φ(x)dx/x² ∈ [747.051305789674284198128446843, 747.051305789674284198128447044]. This comes
  from exact rational pieces and a 200-bit interval enclosure of the digamma tail. The breakpoint enumeration is complete:
  all a/d with d a difference of y-slopes, an η_j or an η₀ − 2η_j, plus the points 1/m_j.
- Hence **C₂′ ≤ C₂ − 18 ≤ 729.051305789674284198128447044**.
- `docs/window/proof.md` had C₂ only as COMPUTED; it is now CERTIFIED.
- Independent recomputations: the verifier's `vcont.py` (own exact enumeration with 2,644 φ-pieces and an 80-digit tail)
  gets C₂ = 747.05130578967428419812844694…, and G = 18 with identical pieces. `docs/window/proof.md`'s `vz.py` agrees to all 16
  printed digits.

### 2.2 N: auxiliary-prime nonvanishing (`docs/window/refine/aux-prime-nonvanishing.md`)

**Theorem N (PROVED; aux §§2–6).** Let n ≥ 2 be even with ℓ := 63n − 1 prime. Then v_ℓ(c_s) ≥ 0 for s = 5, …, 22, and
v_ℓ(c₀) = −5. More precisely ℓ⁵c₀ ≡ 4·Q₁·u_{k*} (mod ℓ), where u_{k*} is an ℓ-unit and

  Q₁ = 984698059590803 / 1545332660300000,

whose numerator is prime and ≡ 47 (mod 63), and whose denominator is 2⁵·5⁵·11⁷·13·61.

*Proof outline.*
- **Lemma B.** Since ℓ > m₀ = 60n, every factorial in the brick form (8.7) is ≤ 60n. Every pole distance satisfies
  |l−k| ≤ h₀ − 2h₆ = 60n < ℓ. So all a_{i,k} ∈ ℤ_(ℓ), and hence all c_s ∈ ℤ_(ℓ).
- **Lemma C.** Only the poles K_ℓ = {110n, 110n+1} satisfy k − h₁ ≥ ℓ. At each of them o_k = 2 and
  G_k(ε) = (ε−ℓ)U_k(ε), with u_k = U_k(0) an ℓ-unit. The unique ℓ-divisible factor is (l − k) with l = k − ℓ ∈ {47n+1, 47n+2};
  it lies in the P₅ block [1, 48n] (η₅ = 48) and in no other block.
- **Lemma D.** For k ∈ K_ℓ, H_s(k−h₁) = ℓ^{−s} + (ℓ-integral). With w₁ = 1 and w₂ = 5 this gives
  c₀ ≡ −Σ_{K_ℓ}(u_k − 5u_k)ℓ^{−5} = 4ℓ^{−5}Σ u_k (mod ℓ^{−4}ℤ_(ℓ)).
- **Lemma E.** u_{110n}/u_{110n+1} = ρ(110n+1) is an explicit ratio of ℓ-units, formula (5.1). Reducing it mod ℓ with
  63n ≡ 1 gives Σ u_k ≡ Q₁u_{k*}.
- **Conclusion.** ℓ ≠ num(Q₁), since the residues mod 63 are 62 and 47, and ℓ ∤ den(Q₁). ∎

The set I₁ := {n even : 63n − 1 prime} = {4, 8, 14, 20, 24, 26, 30, …} is infinite by Dirichlet (primes ≡ −1 mod 63).
The track also proves an odd-n variant with ℓ = 63n − 2 and a general Theorem G; R1 needs neither.

### 2.3 U: crude upper bound (`docs/window/refine/crude-upper-bound.md`)

**Theorem U (PROVED + CERTIFIED).** For every n ≥ 1, |F̃ₙ| ≤ K n¹⁶ e^{−C₀′n}. The C₀′ values below are the exact
certified rationals, truncated downward:

| parameter set | line Re t = M_n | x₀ | tangent point p | C₀′ ≥ | log K ≤ |
|---|---|---|---|---|---|
| simple | ½ − n | 159 | 181/20 | 750.6183158756477496 | 116.92712587 |
| sharp | −⌊16n/25⌋ − ½ | 3984/25 | 26208/3125 | 750.7116742473916946 | 120.06368655 |

The chain of lemmas:
- **U1 (PROVED).** F̃ₙ = −(N_h/2πi)∫_{M+iℝ}K₅(t)R(t)dt for M ∈ ℤ+½ with −h₁ < M < 0, where K₅(t) = Σ_k(t−k)^{−5}.
  - Proof: Cauchy's formula on right half-planes, plus dominated convergence.
  - There are no contributions from the points M < k ≤ −1, because R has zeros of order 5 there.
  - This is `docs/window/proof.md` Proposition A, with a residue-free proof.
- **U2 (PROVED).** |K₅(M+is)| ≤ (8π⁵/3)e^{−2π|s|}.
  - Here K₅ = (π⁵/3)C(1+C²)(2+3C²), with C = cot πt.
  - On half-integer lines, C = −i·tanh πs.
- **U3 (PROVED).** Σ_{l=A}^{B} log|t+l| ≤ ∫_{A−1}^{B+1} + 1 + log 2 for every Im t, and ≥ ∫_{A−1}^{B} if M + A − 1 ≥ 0.
- **U4 (PROVED).** log(N_h|K₅R|)(M+inη) ≤ nU(x,η) + 4 log(2πn) + 11 log(n(162+2|η|)) + K₂.
  - Here x = 160 + M/n, and Robbins' bounds are used for N_h.
  - U(x,y) = C_η − 336 + 5[Gf(x,y) − Gf(x−160,y)] − Σ_j[Gf(x−η_j,y) − Gf(x−160+η_j,y)] − 2π|y|.
  - Gf(a,y) = (a/2)log(a²+y²) + y·arctan(a/y) − a.
- **U5 (PROVED + CERTIFIED).**
  - U(x₀,·) is concave on [0, A], analytically: U″ = −[5h(x₀) + 5h(c₀) + Σ_j(h(a_j) − h(b_j))] < 0, with h(a) = a/(a²+η²).
  - One certified tangent at p gives sup_{[0,A]} U ≤ −C₀′.
  - One certified monotone cell gives U′ < 0 on [A, 60].
  - On [60, ∞), U′ ≤ 3π − 5[arctan(η/x₀) + arctan(η/c₀)] ≤ −κ, with κ ≥ 0.1500 > 22/282.
  - |∂ₓU| ≤ B absorbs the offset x_n − x₀ = O(1/n).
- **Assembly.** |F̃ₙ| ≤ (n/π)∫₀^∞ N_h|K₅R| dη ≤ K n¹⁶ e^{−C₀′n}, with
  K = (2π)⁴π^{−1}e^{K₂+B/2}·282¹¹·(60 + 1/(κ − 22/282)).

**Certification.**
- The prover certified the constants twice: `certify_iv.py` (mpmath.iv, 150 bits) and `certify_exact.py` (exact
  rationals, series with explicit remainders, no floating point). Both print ALL CERTIFIED.
- The verifier's `riv.py` uses an independent method (exp/sin/cos Taylor bounds with remainders) and reproduces every
  constant.
- All 933 of the prover's enclosures intersect the verifier's.

## 3. Proof of the Theorem (route R1)

Suppose ζ(7), ζ(9), …, ζ(21) are all rational. Choose d ≥ 1 with ζ(s) = p_s/d, p_s ∈ ℤ.

1. **An integer.** For n ∈ I₁ with ℓ = 63n − 1 > d, put

   N_n := d·D_n·F̃ₙ = d·D_n c₀ + Σ_{s ∈ {7,9,…,21}} p_s·D_n c_s   (by (1.1) and the vanishing of c₅ and the even c_s).

   Every term is an integer (§2.1), so N_n ∈ ℤ.
2. **It is nonzero.**
   - Since ℓ ∤ d, Theorem N gives v_ℓ(d·D_n c₀) = v_ℓ(D_n) − 5.
   - Every other term has v_ℓ(p_s D_n c_s) ≥ v_ℓ(D_n).
   - By the strict ultrametric inequality, v_ℓ(N_n) = v_ℓ(D_n) − 5 < ∞. So N_n ≠ 0 and |N_n| ≥ 1.

   In fact v_ℓ(D_n) = 5 exactly, so ℓ ∤ N_n. The reason: the two far poles of Lemma C give e_ℓ^{BPP} = 2 + 4 − 1 = 5,
   while e_ℓ^{L19} = 6 and e_ℓ^{PP} ≥ 5. §5 checks this for n ≤ 400; the proof does not need it.
3. **It is small.** By Theorems U and H′4,

   |N_n| ≤ d·e^{C₂′n + o(n)}·K n¹⁶ e^{−C₀′n} = exp(−(C₀′ − C₂′)n + o(n)),  where C₀′ − C₂′ ≥ 21.567 > 0.

4. **Contradiction.** I₁ ∩ {ℓ > d} is infinite, and along it 1 ≤ |N_n| → 0. ∎

Only upper bounds are used: on log D_n and |F̃ₙ|, along the subsequence I₁. Nothing uses the saddle-point asymptotics,
the arithmetic of ω, or density arguments. The o(n) is ineffective, because it comes from the PNT, exactly as in
Zudilin's Proposition 5 and `docs/window/proof.md`. Every other constant is explicit.

## 4. Status of every step of route R1

| # | step | status | source | independent checks (NUMERICAL unless stated) |
|---|---|---|---|---|
| S1 | forms, (1.1), F̃ₙ ∈ ℚ + Σ_{s odd, 7..21} ℚζ(s) | PROVED (Zudilin (8.2)–(8.12), Lemma 19 vanishing, *cited*; elementary) | `docs/window/proof.md` §1, refined §1, aux §1 | exact rationals n ≤ 30: c₅ = c_even = 0; shifted c₀ = unshifted c₀; F̃ₙ = `exact_r5_q23_n9.jsonl` (n ≤ 9) in 3 independent engines |
| S2 | H′1: denominators at p² > h₀ (Lemmas A, B, C) | PROVED | refined §2 | 25.5M Lemma A and 18.6M Lemma B coefficient checks; 680 random admissible h (r = 3, 5, 7); 219,178 (n,p) pairs against TRUE denominators from the GPU CRT engine, plus new values of n with the verifier's own 31-bit engine; 0 violations |
| S3 | denominators at p² ≤ h₀ | PROVED (Zudilin Lemma 19, *cited*; contributes O(√n)) | JTNB p. 281 | exact Δₙc_s ∈ ℤ for n ≤ 30 (the verifier's own coding) |
| S4 | H′4: Lemma D (o_k cancels), Lemma E (grid ≤ continuum), PNT | PROVED (PNT *cited*; ineffective) | refined §3 | Lemma D on every pole in 42 exact instances and 680 random configurations; e_p ≤ Ψ(n/p) at 87,594 primes, never exceeded |
| S5 | C₂ ∈ [747.051305789674284198128446843, …447044]; G = 18; C₂′ ≤ 729.051305789674284198128447044 | CERTIFIED (`c2exact.py`: exact rationals + 200-bit interval tail) | refined §4, `margins.json` | `vcont.py` (independent exact enumeration); `vz.py` (`docs/window/proof.md`); the saving measured at n = 1000 is 18.07 |
| S6 | Lemma B: all c_s ∈ ℤ_(ℓ) for ℓ > 60n | PROVED | aux §2 | exact n ≤ 30; ℓ-adic engine |
| S7 | Lemmas C, D: K_ℓ = {110n, 110n+1}, o_k = 2, one ℓ-factor from P₅; c₀ ≡ 4ℓ⁻⁵Σu_k | PROVED | aux §§3–4 | 14 exact + 158 ℓ-adic (verifier); 158 ℓ-adic + 83 exact CRT (prover) |
| S8 | Lemma E, Q₁ exact, num(Q₁) prime ≡ 47 (mod 63) | PROVED + CERTIFIED (exact rational; deterministic primality test, < 2⁶⁴) | aux §5, `aux_constants.py` | `vx_constants.py` (sympy derivation); `final_check_v2.py` (2) |
| S9 | Theorem N: v_ℓ(c₀) = −5 < 0 ≤ v_ℓ(c_s) | PROVED from S6–S8 | aux §6 | pattern v_ℓ(c₇..c₂₁) = (1,1,0,0,2,4,8,10) in every run, n up to 2994 |
| S10 | I₁ infinite | PROVED (Dirichlet, *cited*) | — | — |
| S11 | U1 Barnes-type identity | PROVED | crude §2 | contour = direct summation, all signs, n ≤ 150 |
| S12 | U2 kernel bound | PROVED | crude §3 | ratio ≤ ½ |
| S13 | U3 window comparison (all Im t) | PROVED | crude §4 | 8,589 adversarial cases |
| S14 | U4 pointwise bound (Robbins *cited*) | PROVED | crude §5 | slack ≥ 133 nats for n ≤ 80 and n up to 10⁶ |
| S15 | U5 landscape: concavity (analytic); tangent, cell, κ, B, C_η (≈ 300 enclosures) | PROVED + CERTIFIED | crude §6, `certify_exact.py`, `certify_iv.py` | `riv.py` (independent); 933 enclosures cross-checked |
| S16 | Theorem U assembly, explicit K, all n ≥ 1 | PROVED + CERTIFIED | crude §7 | J_n ≤ bound on 228 rows (slack ≥ 164 nats); J_n ≥ \|F̃ₙ\| on 96 exact pairs |
| S17 | final argument (§3); margin ≥ 21.56701008597 / 21.66036845771 | PROVED; margin arithmetic CERTIFIED (exact rationals) | §3; `final_check_v2.py` (1) | — |

**Steps of `docs/window/proof.md` that R1 does not use:**
- B, the branch split;
- C, complex Stirling;
- D, the saddle, Rouché and branch λ = 3;
- E, the landscape through τ₃;
- F, Olver's asymptotic;
- G, ω/π ∉ ℤ.

These steps are still CERTIFIED and PROVED as stated in `docs/window/proof.md`, and they carry the backup routes R3 and R4 (§6).

## 5. Final-referee checks by the assembler (`final_check_v2.py` → `final_check_v2.log`, exact rationals)

1. **Margins**, from the certificate files themselves (`C0prime_lower` in `certificate_exact_*.json`; the C₂ interval in
   `margins.json`):

   | route | lower bound on the margin |
   |---|---|
   | R1, simple line | C₀′ − C₂′ ≥ 21.56701008597346541 |
   | R1, sharp line | C₀′ − C₂′ ≥ 21.66036845771741043 |
   | R1, integer tangent point p = 9 | C₀′ − C₂′ ≥ 21.03469004636599593 |
   | R2 (simple / sharp) | C₀′ − C₂ ≥ 3.56701008597 / 3.66036845771 |
   | R3 | C₀ − C₂′ ≥ 21.66038904427002948 |
   | R4 | C₀ − C₂ ≥ 3.66038904427002948 |

2. **Q₁** was recomputed with independent code from the telescoping ratio (5.1) at n = 1/63. The value is identical. The
   numerator 984698059590803 is prime (deterministic Miller–Rabin) and ≡ 47 (mod 63). The denominator's primes are
   ≤ 61, below every auxiliary prime (the smallest is 251).
3. **The H′–N joint.**
   - The refined exponent at ℓ must be ≥ −v_ℓ(c₀) = 5; a smaller value would contradict Theorem N.
   - At all 77 auxiliary primes ℓ = 63n − 1 with n ≤ 400, V_k was computed from the definition: e^{L19} = 6,
     e^{PP} = 8, e^{BPP} = 5. So e_ℓ^{REF} = 5 = −v_ℓ(c₀) exactly: the flat-pole bound is sharp at ℓ.
   - The hypotheses of Theorem N were confirmed each time: the far poles, as (k, o_k, V_k), are (110n, 2, 1) and
     (110n+1, 2, 1), and ν = 0.
   - This is consistent with the gain piece [62,63], where L19, PP and BPP are 6, 8 and 5.
4. **The same F̃ₙ in all tracks.** Each verifier reproduced `docs/window/exact_r5_q23_n9.jsonl` (n ≤ 9, 16 digits,
   all signs) with its own engine (the verifiers' scripts are not included in this repository):
   - `vx_exact.py`: exact partial fractions;
   - `v_exactF.py`: direct summation from the definition, extended to n = 150;
   - `vexact.py`: partial fractions equal to the direct series to 60 digits.
5. **A display defect (cosmetic).**
   - `docs/window/refine/certify_exact.log` prints C₀′ as `%.16f` of a float.
   - For the simple set it shows 750.6183158756477951. That is 4.5·10⁻¹⁴ above the certified exact rational
     15012366317512954992182192938743473422815509/2·10⁴⁰ = 750.61831587564774960911…
   - The JSON field and the verifier's `riv.py` agree on the exact value.
   - This file quotes only the exact values, truncated downward.

## 6. Robustness: four complete routes

| route | denominators | upper bound on \|F̃ₙ\| | nonvanishing | certified margin | what it avoids |
|---|---|---|---|---|---|
| **R1 (this file)** | H′ (C₂′) | U | N | ≥ 21.567 / 21.660 | saddle location, landscape through τ₃, Olver, ω/π |
| R2 | Zudilin's Lemma 19 (C₂) | U | N | ≥ 3.567 / 3.660 | everything in H′ (Lemmas A–E, C₂′) |
| R3 | H′ (C₂′) | `docs/window/proof.md` A–E (Stirling on the saddle line) | N, or `docs/window/proof.md` F–G | ≥ 21.660 | Theorem U |
| R4 = `docs/window/proof.md` | Zudilin's Lemma 19 (C₂) | A–E | F–G | ≥ 3.660 | all three new tracks |

Every route has a positive certified margin, and the new components fail safe:
- if H′ fails, use R2;
- if U fails, use R3;
- if N fails, use R3 with F–G;
- if all three fail, the original proof R4 remains.

The Lean project may prefer R2 for formalization. It needs no saddle and no refined denominators, only U, N and
Zudilin's Lemma 19. The crude track reports that Theorem U gives |F̃ₙ| ≤ e^{−748.1n} for n ≥ 74, which is the
`Stmt_L20Upper` target (C0lo = 748.1). *(Editorial, 2026-09-26: the Lean proof of this repository follows R2; see the
note at the top and `README.md`.)*

## 7. Exactly what changed from `docs/window/proof.md`

Only the LEAD NOTICE of `docs/window/proof.md` was edited.

1. **Arithmetic (§2, step H → H′).**
   - For p² > h₀, the exponent of p is now min(Zudilin's, per-pole, flat-pole).
   - C₂ → C₂′ ≤ C₂ − 18 ≤ 729.051305789674284198128447044, the upper end of the certified interval.
   - C₂ itself goes from COMPUTED (three floating implementations) to CERTIFIED (`c2exact.py`).
2. **Upper bound (§3.3–§3.6 upper half, steps C/D/E/F → U).**
   - The line through the saddle is replaced by fixed half-integer lines M_n = ½ − n (or −⌊16n/25⌋ − ½).
   - Complex Stirling is replaced by finite log-sums (U3, U4).
   - The certified global landscape through τ₃ is replaced by one concavity lemma, one tangent point, one monotone cell
     and a tail slope.
   - The bound holds for every n ≥ 1 with an explicit K. The price is C₀ − C₀′ = 0.0934 (simple) or 2.1·10⁻⁵ (sharp).
3. **Nonvanishing (§3.6 lower half, steps F/G → N).**
   - Old: positive density via Olver's asymptotic and ω/π ∉ ℤ.
   - New: an ℓ-adic separation at ℓ = 63n − 1, which makes the integer N_n nonzero for every n ∈ I₁ with ℓ > d.
     I₁ has density zero but is infinite, which is all Proposition 5 needs.
4. **Conclusion (§4).** The margin goes from 3.6603890443 to ≥ 21.56701008597 (simple) / 21.66036845771 (sharp).
5. **Kept.**
   - §1 (definitions).
   - §3.1 Proposition A (it is U1).
   - §§3.2–3.6: still valid; used by R3/R4 and by the configurations of §9.
   - §5 validation, extended by the verifiers to n = 150 by direct summation.
   - §7 novelty (unchanged: {7,…,21} is not in the literature as of the 2026-09-25 web check).
6. **Superseded limitations in `docs/window/proof.md` §9.**
   - §9.3 ("nonvanishing only on a positive-density subsequence") no longer applies.
   - §9.2 is relaxed. The upper bound needs only an admissible line and a certified landscape supremum on it, not the
     saddle. Nonvanishing for other configurations can come from Theorem G (aux §7) under (G1) η₁ < η_{r+1} and
     (G2) η₁ + 2η_{r+1} < η₀, after a per-configuration check that β·Q_c ≢ 0.
7. **Errata to `docs/window/proof.md`**, not edited in its body:
   - §1: deg R = −336n − 17, not −336n − 4. Harmless.
   - §3.3: "e^{iπλnη₀} = 1 because λη₀n is even" is correct for η₀ = 160. For odd η₀ the factor is (−1)ⁿ, common to both
     branches and harmless. This matters only for the stair179 configuration of §9.

## 8. Corrections recorded from the verifications (all cosmetic, none affects R1)

**refined-lemma19**
- The flat-far clause is vacuous.
- Corollary 1's "Δ′ₙ ∣ Δₙ" should read "Δ′ₙc ∈ ℤ". Zudilin's exponent can be negative for degenerate h, for example
  r = 3, q = 7, h = (224; 24, 26, 31, 43, 63, 64, 81), p = 31. R1 uses D_n = ∏p^{max(0,e_p)}.
- The re-used Lemma 20 for η₀ = 179 carries a (−1)ⁿ factor.

**aux-prime-nonvanishing**
- The listed "prime factorizations" of num(Q_c) for c = 5, 8, 10, 11 contain composite cofactors (BPSW), so the
  exceptional sets for those c are undetermined. R1 uses c = 1 only.
- The 25-digit factor of num(Q₂) now has a Pocklington–Lehmer certificate.

**crude-upper-bound**
- The "±10⁻²⁰" in §6(b) are 17-decimal roundings.
- "J_n tracks |F̃ₙ| within a bounded factor" is false in general: only the exponential rates agree. This remark is not
  used.
- Lean note: `den_sum_ge`, like `num_sum_le`, needs the |y| < 1 extension.
- The float display of C₀′ noted in §5.5.

## 9. Other configurations and q = 21 (not part of the theorem)

**Re-optimised q = 23 configurations** (refined §6), each certified by `certify_line.py` (ALL CERTIFIED):

| configuration | margin C₀ − C₂′ |
|---|---|
| fix160: η₀ = 160, η = (45, …, 53, 53, …, 66) | 35.5137959249 |
| stair179: η₀ = 179, η_j = 54 + j | 52.2993840655 |

- **Route.** Both are R3-type: H′ plus `docs/window/proof.md` §3 re-run with their own certified saddle and landscape inputs.
- **Verifier checks.** The verifier confirmed both, including the (−1)ⁿ correction for η₀ = 179. Exact F̃ₙ for n ≤ 9
  matches the asymptotics, 27/27 signs.
- **stair179 needs the flat-pole Lemma B.** With the per-pole bound alone its margin would be −15.7.
- **Not yet upgraded.** Theorems U and N were not run for these configurations; that would need a new U certificate and
  the Theorem G constant check. They are not needed for the Theorem.

**q = 21 ({7,…,19})** remains out of reach in this family (NUMERICAL):

| configuration | refined margin |
|---|---|
| staircase η₀ = 158 | −27.98 |
| staircase η₀ = 146 | −28.13 |
| η* | −47.18 |

True denominators give about −24.5 and −27.5 on the best staircases.

## 10. Residual caveats (the harshest reading)

1. **Cited results.**
   - Zudilin's Lemma 19 is used only for p ≤ √h₀, where it contributes O(√n), and for c₅ = c_even = 0 (elementary,
     and checked exactly for n ≤ 30).
   - A self-contained crude bound for the small primes, (3q−2r−1)⌊log_p h₀⌋, is only sketched (refined §2 Remark).
   - The PNT, Dirichlet, Robbins and Cauchy are textbook results.
2. **Ineffectivity.** No explicit n₀ is claimed. The PNT error term in the large-prime sum is only known to be o(n)
   here. The small-prime part is O(√n), about 556√n by the verifier's estimate. So the contradiction appears only for
   large n. This is the same as in Zudilin's proofs.
3. **Computer assistance.**
   - The C₂′ enclosure (`c2exact.py`) and the C₀′/K constants (`certify_exact.py`, `certify_iv.py`) are machine-certified.
   - Each has an independent re-implementation by a verifier: `vcont.py` (exact rationals, with a non-interval 80-digit
     tail) and `riv.py` (interval).
   - Any two implementations differ by at most 10⁻¹³: the exact rationals agree, and only a float display differs (§5.5).
     The margin, 21.5, exceeds that by more than 14 orders of magnitude.
4. **The most intricate new combinatorics** is Lemma E (grid versus continuum) in H′4.
   - It is PROVED, re-derived by the verifier, and never violated at 87,594 primes.
   - If it failed, R2 would still give a margin of 3.567.
5. **Not peer-reviewed.** *(Editorial, 2026-09-26.)* Route R2 is now formalised in Lean in this repository (see
   `README.md`); this text itself has been checked only by AI agents.
   - Theorem U reuses complex-analysis lemmas of the Lean pair project (https://github.com/gmDevi/zeta2-7-9-lean:
     `vline_higher`, `vline_left`, `kerS`, `Gf_scale`, …); new for Lean were the concavity lemma, the certificate of
     `log`/`arctan` enclosures, and window lemmas valid for all y > 0.
   - Theorem N is elementary ℓ-adic bookkeeping plus one exact rational constant.

## 11. Files

*(Editorial, 2026-09-26: this section lists the files of the research session that are included in this repository,
at their paths here. The session's other scripts, logs and certificates, among them the verifiers' independent
re-implementations `vcont.py`, `riv.py`, `vx_*.py`, and `certify_iv.py`, are not included.)*

**`docs/`**
- `proof.md` (this file).

**`docs/window/`**
- `proof.md`: the first version of the proof, route R4 (and the saddle-point steps used by R3).
- `final_check_v2.py` → `final_check_v2.log` (§5).
- `zud5.py`, `zud_exact.py`, `zud_arith_check.py`, `vz.py`: the definitions, the exact evaluation of F̃ₙ, the exact
  check of Lemma 19 at n ≤ 3, and the φ-integral (C₂); data `exact_r5_q23_n9.jsonl`, `arith_check_r5_q23.jsonl`.
- `certify_line.py` → `certify_q23_160.{json,log}`, `explore.py` → `explore_q23_160.log`, `barnes_check.py` →
  `barnes_q23_160_{n1to9,large}.log`: the certified saddle-point data and the numerical validation of
  `docs/window/proof.md`.

**`docs/window/refine/`** (index: `README.md` there)
- `refined-lemma19.md`, `c2exact.py` → `c2exact_q23_160.json`, `margins.py` → `margins.json`.
- `aux-prime-nonvanishing.md`, `aux_constants.{py,log,json}`, `check_ratio_exact.{py,log}`.
- `crude-upper-bound.md`, `certify_exact.py` (with `ub_common.py`) → `certify_exact.log`,
  `certificate_exact_x159_p181_20_Y60.json`.
