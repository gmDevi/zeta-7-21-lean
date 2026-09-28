# Arithmetic nonvanishing of the {ζ(7),…,ζ(21)} forms via the auxiliary prime ℓ = 63n − 1

Track `aux-prime-nonvanishing` (Theorem N of `docs/proof.md`), written by an AI prover agent on 2026-09-25.
Research-session paths were replaced by the paths of this repository; only some of the scripts and logs named below
are included (see `README.md` in this folder). Status labels:
- **PROVED**: a complete argument is written here, modulo the cited published facts.
- **CERTIFIED**: interval arithmetic.
- **COMPUTED-EXACT**: exact integer or rational computation.
- **NUMERICAL**: floating-point only.

This track plays the role of the Theorems A/G of the 2-adic pair proof (the nonvanishing argument of
https://github.com/gmDevi/zeta2-7-9-lean, `docs/proof.md` there) for the real forms of `docs/window/proof.md`. It turns
out to be simpler here. In the window (m₀, m₁] = (60n, 63n] of Lemma 19, all the
ζ-coefficients are ℓ-integral, so the only thing to show is that c₀ has a pole at ℓ. That pole is a sum over c+1
explicit Laurent coefficients, and its leading part is a fixed rational number.

## 0. Result

**Setting** (docs/window/proof.md §1; Zudilin, JTNB 16 (2004) (8.2)–(8.7)):
- r = 5, q = 23, η₀ = 160 and η = (47⁴, 48, 50², 51, 52, …, 66);
- h₀ = 160n + 2 and h_j = η_j n + 1;
- R(t) = (h₀+2t)(t+1)⁵_{h₀−1} / ∏_{j=1}^{23}(t+h_j)_{h₀+1−2h_j};
- N_h = ∏_{j>5}(h₀−2h_j)! / ∏_{j≤5}(h_j−1)!²;
- F̃ₙ = N_h·(1/4!)Σ_{t≥0}R⁽⁴⁾(t) = c₀ + Σ_{s=5}^{22} c_s ζ(s), with the explicit coefficients (1.1) below;
- c₅ = 0 and c_s = 0 for even s (Zudilin, Lemma 19).

**Theorem N (ℓ-adic separation).** Let c ∈ {1, 2} and n ≥ c+1, and suppose ℓ := 63n − c is prime. Then:

  (i) v_ℓ(c_s) ≥ 0 for every s ∈ {5, …, 22};
  (ii) v_ℓ(c₀) = −5.

More precisely, ℓ⁵c₀ ≡ 4·Q_c·u* (mod ℓ), where u* is an explicit ℓ-adic unit (Lemma C) and

 Q₁ = 984698059590803 / 1545332660300000,
 Q₂ = −70061130878449927481654965996581102348947 / 160859515096393689693968160225229600.

The numerator of Q₁ is a prime ≡ 47 (mod 63). The numerator of Q₂ is 11897 · 673328295253 · 8746067329636949836491967,
with prime factors ≡ 53, 19, 34 (mod 63). Neither ever divides ℓ ≡ −c (mod 63), so **there is no exceptional n**.

Define I_c := {n ≥ c+1 : 63n − c prime}. Then I₁ ⊂ 2ℤ and I₂ ⊂ 2ℤ+1, and both are infinite: by Dirichlet there are
infinitely many primes ≡ 62 and ≡ 61 (mod 63). I₁ = {4, 8, 14, 20, 24, 26, 30, …} and I₂ = {5, 7, 11, 17, 21, …}.

**Corollary N1 (unconditional nonvanishing).** F̃ₙ ≠ 0 for every sufficiently large n ∈ I₁ ∪ I₂. The threshold is
ineffective.

**Corollary N2 (the window theorem needs Lemma 20 only as an upper bound).** Suppose ζ(7), …, ζ(21) ∈ ℚ with common
denominator d. For every n ∈ I₁ with ℓ = 63n − 1 > d, the number N_n := dΔₙF̃ₙ is a **nonzero** integer, with
v_ℓ(N_n) = v_ℓ(Δₙ) − 5 = 1. Here Δₙ is Lemma 19's normalisation, or any other common denominator.

Combined with the upper bound |F̃ₙ| ≤ K n⁻¹² e^{−C₀n} (docs/window/proof.md steps A–E) and log Δₙ = C₂n + o(n), where
C₀ − C₂ = 3.66 > 0, this is impossible for large n ∈ I₁. So at least one of ζ(7), …, ζ(21) is irrational.

Steps **F** (saddle-point asymptotics with the constant B) and **G** (ω/π ∉ ℤ, positive-density cos argument) of
docs/window/proof.md are no longer needed.

| step | content | status |
|---|---|---|
| (1.1) | shifted representation of c₀, c_s | PROVED (Zudilin (8.6), (8.12) + elementary) |
| Lemma B | ℓ > m₀ = 60n ⇒ every Laurent coefficient a_{i,k} and every c_s is ℓ-integral | PROVED (+ COMPUTED-EXACT) |
| Lemma C | top poles K = {110n+1−d : 0 ≤ d ≤ c}: o_k = 2, G_k = (ε−ℓ)U_k with U_k(0) a unit | PROVED (+ COMPUTED-EXACT) |
| Lemma D | c₀ ≡ 4ℓ⁻⁵ Σ_K u_k (mod ℓ⁻⁴ℤ_(ℓ)) | PROVED (+ COMPUTED-EXACT) |
| Lemma E | Σ_K u_k ≡ Q_c u_{k*} (mod ℓ); Q₁, Q₂ exact | PROVED; constants COMPUTED-EXACT; (5.1) also checked as an exact rational identity (`check_ratio_exact.py`) |
| Thm N | v_ℓ(c₀) = −5 < 0 ≤ v_ℓ(c_s), no exceptions | PROVED; checked at all 152 n ∈ I₁∪I₂ with n ≤ 400 plus 6 values of n up to 1508 (ℓ-adic engine), and at all 83 n ≤ 198 with exact CRT integers (§8) |
| Cor N1 | F̃ₙ ≠ 0 for large n ∈ I | PROVED |
| Cor N2 | theorem from Thm N + upper bound (A–E) + Lemma 19 | PROVED given A–E and H of docs/window/proof.md |
| §6 | compatible with any normalisation, incl. the per-pole refined Δ′ₙ; bonus: exact exponent on (m₀, m₁] | PROVED + COMPUTED-EXACT |
| §7 | general configurations (Theorem G) | PROVED; controls: Zudilin's Thm 3 config, η₀ = 320 config |

## 1. The linear form in Zudilin's shifted representation (PROVED)

**Poles.** R has poles at t = −k for k ∈ [h₆, h₀−h₆] = [50n+1, 110n+1], of order

 o_k = #{j > 5 : h_j ≤ k ≤ h₀−h_j} − [2k = h₀] ≥ 1.

Here all j ≤ 5 satisfy k ∈ [h_j, h₀−h_j], and each such j cancels one of the five numerator zeros at −k.

**Partial fractions.** Put G_k(ε) := ε^{o_k}N_hR(−k+ε) and a_{i,k} := [ε^{o_k−i}]G_k. Then

 N_hR(t) = Σ_k Σ_{i=1}^{o_k} a_{i,k}(t+k)^{−i},

with no polynomial part, since deg R = −336n−4.

**The shift.** R has zeros of order 5 at t = −1, …, −(h₁−1): no pole range meets [1, h₁−1]. So R⁽⁴⁾ vanishes there, and
F̃ₙ = (N_h/4!)Σ_{t≥1−h₁}R⁽⁴⁾(t). This is Zudilin's (8.6).

**The coefficients.** Use
- (1/4!)(d/dt)⁴(t+k)^{−i} = w_i(t+k)^{−(i+4)} with w_i = C(i+3, 4), so w₁ = 1 and w₂ = 5;
- Σ_{t≥1−h₁}(t+k)^{−s} = ζ(s) − H_s(k−h₁) for s ≥ 5 and k ≥ h₆ > h₁, where H_s(N) := Σ_{m=1}^{N} m^{−s}.

This gives

 c_s = Σ_k w_{s−4} a_{s−4,k},  c₀ = −Σ_k Σ_{i=1}^{o_k} w_i a_{i,k} H_{i+4}(k−h₁).  (1.1)

These are Zudilin's A_{s} and −A₀ in (8.12), with B_{jk} = a_{j−5,k}. Lemma 19 states Δₙc₀ ∈ ℤ, Δₙc_s ∈ ℤ, and c₅ = 0
and c_s = 0 for even s. Both engines of §8 implement (1.1) independently; c₅ and the even c_s vanish to full precision
in every run.

## 2. Lemma B (ℓ-integrality above m₀) — PROVED

**Lemma B.** Let ℓ be a prime with ℓ > m₀ := max(h₅−1, h₀−2h₆) = 60n. Then a_{i,k} ∈ ℤ_(ℓ) for all i, k, and hence
c_s ∈ ℤ_(ℓ) for all s.

*Proof.* Split (t+1)_{h₀−1} = (t+1)_{h_j−1}·(t+h_j)_{h₀+1−2h_j}·(t+h₀−h_j+1)_{h_j−1}. This gives Zudilin's bricks (8.7):

 N_hR(t) = (h₀+2t) · ∏_{j≤5} P_j(t) · ∏_{j>5} Q_j(t),  where
 P_j(t) = (t+1)_{h_j−1}(t+h₀−h_j+1)_{h_j−1}/(h_j−1)!²,  Q_j(t) = (h₀−2h_j)!/(t+h_j)_{h₀+1−2h_j}.

- (a) h_j − 1 ≤ 48n < ℓ, so (h_j−1)! is an ℓ-unit and P_j ∈ ℤ_(ℓ)[t]. Hence P_j(−k+ε) ∈ ℤ_(ℓ)[ε].
- (b) Let j > 5 and l ∈ [h_j, h₀−h_j] with l ≠ k. Both l and the pole k lie in [h₆, h₀−h₆], an interval of length
  60n. So 0 < |l−k| ≤ 60n < ℓ, and 1/(l−k+ε) ∈ ℤ_(ℓ)[[ε]]. The factor with l = k is ε⁻¹.
- (c) h₀ + 2(−k+ε) = (h₀−2k) + 2ε; this equals 2ε if 2k = h₀.

Counting the powers of ε:

 G_k(ε) = [h₀−2k+2ε, or 2 if 2k = h₀] · ∏_{j≤5}P_j(−k+ε) · ∏_{j>5}(h₀−2h_j)!∏_{l∈[h_j,h₀−h_j]∖{k}}(l−k+ε)⁻¹.

Every factor lies in ℤ_(ℓ)[[ε]]. ∎

This is Zudilin's (8.10), D_{m₀}^{q−j}B_{jk} ∈ ℤ, specialised to ℓ > m₀. COMPUTED-EXACT: min_{i,k} v_ℓ(a_{i,k}) = 0 in
every run of §8.

## 3. Lemma C (the top poles) — PROVED

Fix c ≥ 1 and n ≥ c+1 with ℓ := 63n − c prime. Then 60n < ℓ < 63n. Put k* := h₀ − h₆ = 110n+1 and

 K := {poles k : k − h₁ ≥ ℓ} = {k* − d : 0 ≤ d ≤ c}.

To see this, note that k − h₁ ≥ ℓ ⇔ k ≥ 110n+1−c.

**Lemma C.** For k ∈ K:
- (a) o_k = 2;
- (b) G_k(ε) = (ε − ℓ)·U_k(ε) with U_k ∈ ℤ_(ℓ)[[ε]] and u_k := U_k(0) ∈ ℤ_(ℓ)^×. In particular v_ℓ(G_k(0)) = 1 and
  u_k = G_k(0)/(−ℓ).

*Proof.* (a) Let k = k*−d. Then k ≤ h₀−h_j ⇔ (η_j−50)n ≤ d. This holds for η_j ≤ 50, and fails for η_j ≥ 51 because
d ≤ c < n. So j = 6, 7 are the only j > 5 counted, and 2k ≠ h₀.

(b) Go through the factors of the product in Lemma B.
- The Q_j factors and h₀−2k are ℓ-units, since they are nonzero and |·| ≤ 60n < ℓ.
- N_h is an ℓ-unit: all its factorial arguments are ≤ 60n < ℓ.
- In P_j the factors are l−k+ε with l in the blocks B_j = [1, h_j−1] ∪ [h₀−h_j+1, h₀−1]. We have
  |l−k| ≤ k−1 ≤ 110n < 2ℓ, so ℓ | (l−k) only if l = k ± ℓ.
- l = k+ℓ ≥ 173n+1−2c > h₀−1, so it is never in a block.
- l = k−ℓ ∈ [47n+1, 47n+1+c]. This lies in [1, h_j−1] = [1, η_j n] exactly when η_j ≥ 48, i.e. only for j = 5
  (using 47n+1+c ≤ 48n ⇔ n ≥ c+1). It never lies in the upper block, which starts at 112n+2.

So G_k contains exactly one factor with ℓ-divisible constant term, namely (−ℓ+ε) from P₅. Every other factor is a unit
plus ε. ∎

COMPUTED-EXACT: in every run of §8, |K| = c+1, and o_k = 2 and v_ℓ(G_k(0)) = 1 for every k ∈ K.

## 4. Lemma D (the pole of c₀ at ℓ) — PROVED

**Lemma D.** Under the hypotheses of Lemma C,

 **c₀ ≡ 4 ℓ⁻⁵ Σ_{k∈K} u_k  (mod ℓ⁻⁴ ℤ_(ℓ)).**  (4.1)

*Proof.* Split the sum (1.1) according to whether k ∈ K.
- **k ∉ K.** Then k−h₁ < ℓ, so H_s(k−h₁) ∈ ℤ_(ℓ). By Lemma B, a_{i,k} ∈ ℤ_(ℓ), so the term is ℓ-integral.
- **k ∈ K.** Then ℓ ≤ k−h₁ ≤ ℓ+c < 2ℓ, so H_s(k−h₁) = ℓ^{−s} + (ℓ-integral). By Lemma C,
  a_{2,k} = G_k(0) = −ℓu_k and a_{1,k} = [ε¹]G_k = u_k − ℓU_k′(0). Hence the term is

   −(w₁a_{1,k}ℓ⁻⁵ + w₂a_{2,k}ℓ⁻⁶) = −(u_k − ℓU_k′(0))ℓ⁻⁵ + 5u_kℓ⁻⁵ = 4u_kℓ⁻⁵ + U_k′(0)ℓ⁻⁴.

 ∎

**General form of the constant.** If G_k = (ε−ℓ)^e U_k and o_k = o, then the terms with i + t = o all have order
ℓ^{e−o−r+1}, and c₀ ≡ −β ℓ^{e−o−r+1} Σ_K u_k, where

 β := Σ_{t=0}^{min(e,o−1)} (−1)^{e−t}C(e,t)w_{o−t}.

For e ≤ o−1 this is a finite difference: β = (−1)^e C(o−e+r−2, r−1−e) ≠ 0. Here e = 1, o = 2, r = 5 gives
β = −C(4,3) = −4. This is the analogue of β₁ = −168 in the pair proof.

## 5. Lemma E (telescoping) — PROVED; constants COMPUTED-EXACT (`aux_constants.py`)

**Lemma E.** For k, k−1 ∈ K,

 u_{k−1}/u_k = G_{k−1}(0)/G_k(0) = ρ(k) := [(h₀−2k+2)/(h₀−2k)] · [(h₀−k)/(1−k)]⁵ · ∏_{j=1}^{23} (h_j−k)/(h₀−h_j+1−k),  (5.1)

and every factor is an ℓ-unit. Reduced mod ℓ, where 63n ≡ c, this gives

 Σ_{k∈K} u_k ≡ Q_c · u_{k*} (mod ℓ),  Q_c := Σ_{d=0}^{c} ∏_{d′<d} ρ(k*−d′)|_{n=c/63}.  (5.2)

*Proof.* **The formula (5.1).** Since 2k ≠ h₀,

 G_k(0) = N_h(h₀−2k) ∏_{l∈[1,h₀−1]∖{k}}(l−k)⁵ / ∏_j ∏_{l∈[h_j,h₀−h_j]∖{k}}(l−k).

Take an interval [a, b] such that k−1 and k are both inside it or both outside it. Shifting l ↦ l+1 gives

 ∏_{l∈[a,b]∖{k−1}}(l−k+1) / ∏_{l∈[a,b]∖{k}}(l−k) = (b+1−k)/(a−k).

For k, k−1 ∈ K this applies to every interval: [1, h₀−1] and [h_j, h₀−h_j] with η_j ≤ 50 contain both points, while for
η_j ≥ 51 both points lie above h₀−h_j = (160−η_j)n+1, because k−1 ≥ k*−c > 109n+1. Both G's carry the single factor
−ℓ, so u_{k−1}/u_k = G_{k−1}(0)/G_k(0).

**The factors are ℓ-units.** Take k = k*−d with 0 ≤ d ≤ c−1.
- h₀−2k+2 and h₀−2k lie in [−60n+2d, −60n+2d+2], so they are nonzero with |·| < ℓ.
- h₀−k = 50n+1+d ∈ (0, ℓ).
- 1−k = −110n+d satisfies |·| < 2ℓ and 1−k ≠ −ℓ.
- h_j−k = (η_j−110)n+d. For η_j = 47 this is −ℓ−(c−d) with 1 ≤ c−d < ℓ. For η_j ≥ 48 it lies in (−ℓ, 0).
- h₀−h_j+1−k = (50−η_j)n+1+d. For η_j ≤ 50 it lies in (0, ℓ); for η_j ≥ 51 it lies in (−ℓ, 0), using d ≤ n−2.

**Reduction mod ℓ.** Each factor has the form A/B with A = αn+β′ and B = γn+δ. Since 63A ≡ αc+63β′ (mod ℓ) and ℓ ∤ A,
we get ℓ ∤ (αc+63β′), and likewise for B. So A/B ≡ (αc+63β′)/(γc+63δ) (mod ℓ), a ratio of two integers prime to ℓ.
In particular ℓ ∤ den(Q_c). ∎

**The constants** (exact rational arithmetic):
- **c = 1:** ρ(k*)|_{n=1/63} = (−11/10)(−113/110)⁵ ∏_j(η_j−110)/(113−η_j) = (−11/10)(−113/110)⁵·(−304290/1055483)
  = −560634600709197/1545332660300000 ≈ −0.3628. So **Q₁ = 1 + ρ = 984698059590803/1545332660300000 ≈ 0.6372**,
  whose numerator is prime and ≡ 47 (mod 63).
- **c = 2:** Q₂ ≈ −435542.35, with numerator 11897·673328295253·8746067329636949836491967 (all prime; residues 53, 19,
  34 mod 63).
- **Other c.** Q_c is also nonzero for c = 4, 5, 8, 10, 11 (`aux_constants.log`). For c ≥ 8 a few exceptional primes
  occur, e.g. 157426957477 for c = 8.

## 6. Theorem N, Corollaries N1–N2, and compatibility with the refined denominators

**Proof of Theorem N.**
- (i) is Lemma B, since ℓ = 63n − c > 60n.
- (ii) Lemmas D and E give ℓ⁵c₀ ≡ 4Q_c u_{k*} (mod ℓ). Here 4 and u_{k*} are units (ℓ is odd), and ℓ ∤ den(Q_c).
  The numerator of Q_c has no prime factor ≡ −c (mod 63), while ℓ ≡ −c (mod 63). So ℓ⁵c₀ is a unit and v_ℓ(c₀) = −5.

∎

**Proof of Corollary N1** (as the pair's Cor. B).
1. Let V ⊂ ℚ¹⁹ be the space of vectors x = (x₀, x₅, …, x₂₂) with x₀ + Σ x_sζ(s) = 0.
2. V contains no nonzero vector with x₅ = … = x₂₂ = 0, so x₀ = Σ α_s x_s on V for some α_s ∈ ℚ.
3. Take n ∈ I with ℓ larger than every denominator of the α_s, and suppose F̃ₙ = 0.
4. Then (c₀, c_s) ∈ V, so v_ℓ(c₀) ≥ min_s v_ℓ(α_s c_s) ≥ 0. This contradicts v_ℓ(c₀) = −5.

∎

**Proof of Corollary N2.**
- *N_n is a nonzero integer.* Write ζ(s) = p_s/d. By Lemma 19, N_n = dΔₙc₀ + Σ_s p_sΔₙc_s ∈ ℤ, and c₅ = c_even = 0.
  For ℓ ∤ d we have v_ℓ(dΔₙc₀) = v_ℓ(Δₙ) − 5, while v_ℓ(p_sΔₙc_s) ≥ v_ℓ(Δₙ). So v_ℓ(N_n) = v_ℓ(Δₙ) − 5 < ∞ and
  N_n ≠ 0. Numerically v_ℓ(Δₙ) = 6: D_{m₁}⁵D_{m₂} with m₁ = m₂ = 63n ≥ ℓ > m₃ = 62n; Φₙ only involves p ≤ 60n.
- *Upper bound.* From (A) and (B) of docs/window/proof.md,
  |F̃ₙ| ≤ (1/π)[(1/24)|N_hJ₃| + (11/24)|N_hJ₁|] with |N_hJ_λ| ≤ n⁻¹² e^{15/n} e^{n·sup_y u_λ} ∫|A(x*+iy)|dy.
  The certified landscape (E) gives sup u₃ = u₃(y*) = −C₀ and sup u₁ ≤ −754.6 < −C₀, so |F̃ₙ| ≤ K n⁻¹² e^{−C₀n}
  for all n.
- *Contradiction.* With log Δₙ = C₂n + o(n) (H), 1 ≤ |N_n| ≤ d·e^{(C₂−C₀+o(1))n} → 0 along I₁. ∎

Nothing here uses Re f″(τ₃) > 0, Olver's theorem, the constant B, or ω/π ∉ ℤ.

**Consequence for the analytic side of the program.** Once nonvanishing is arithmetic, the analytic input is only a
certified inequality sup_{contour} Re Φ_λ ≤ −C₂′ − δ for each branch λ, for any admissible contour. Four things are no
longer required:
- the contour need not pass exactly through the saddle;
- no nondegeneracy of the saddle is needed;
- no exclusion of equal-height saddles or of cancellation between branches is needed;
- no arithmetic condition on ω is needed.

With the refined denominators (margin ≈ +19 to +21 instead of +3.66), even crude certified bounds on a nearby line
would suffice. For configurations whose saddle has Re τ_d > η₀ (the r = 7 windows of docs/window/proof.md §9.2), a polygonal
contour then only needs sup bounds on its pieces. Theorem G below covers the nonvanishing for such configurations, as
long as (G1) and (G2) hold.

**Compatibility with the refined denominators (PROVED + COMPUTED-EXACT; `refined_compat.py`, `refined_compat.log`).**
- The separation v_ℓ(c₀) < min_s v_ℓ(c_s) is invariant under multiplying all coefficients by a common scalar.
- It therefore holds for Zudilin's F(h) (8.4), since N_h is an ℓ-unit, for F̃ₙ, and for Δₙ or any valid refined Δ′ₙ.
- Any valid common denominator has v_ℓ(Δ′ₙ) ≥ 5 = −v_ℓ(c₀), and then v_ℓ(Δ′ₙc₀) = v_ℓ(Δ′ₙ) − 5 < v_ℓ(Δ′ₙ) ≤ v_ℓ(Δ′ₙc_s).
- The auxiliary primes cost only O(log n), and the refined asymptotics log Δ′ₙ = C₂′n + o(n) hold along every
  subsequence, in particular along I₁.
- If another track needs n ≡ a (mod N), use any c ∈ {1, 2, 4, 5, …} with gcd(63a−c, 63N) = 1 and Q_c ≢ 0. Dirichlet
  still gives infinitely many n.

Values at ℓ = 63n − 1 (n = 20, 30, 60, 80, 100, 160):

| quantity | value at ℓ |
|---|---|
| v_ℓ(N_h) | 0 |
| v_ℓ(Δₙ), Lemma 19 | 6 |
| exponent of the per-pole model (window-19-probe §3.1, combined with L19) | 6 |
| true exponent = −v_ℓ(c₀) | 5 |
| v_ℓ(Δₙc₀), v_ℓ(Δₙc₇), …, v_ℓ(Δₙc₂₁) | 1; 7, 7, 6, 6, 8, 10, 14, 16 |

The model is never below the truth, so it is consistent.

**Bonus (Lemma B′, PROVED): the exact exponent on (m₀, m₁].** Let p ∈ (m₀, m₁], so p² > h₀ and p > m₁/2. Put
K_p := {k : k − h₁ ≥ p} and e_k := v_p(N_hG_k(0)); e_k counts the p-divisible factors, all in the P_j. Then

 exponent_p ≤ max(0, max_{k∈K_p}(o_k + r − 1 − e_k)).

*Proof.* Lemma B gives integrality of every a_{i,k}. Moreover [ε^μ]∏_{t≤e_k}(ε+α_t) has v_p ≥ e_k − μ, so
v_p(a_{i,k}) ≥ max(0, e_k − o_k + i). Only k ∈ K_p meet p in H_s(k−h₁). ∎

The per-pole model maximises over all poles. The poles k ∉ K_p give spurious terms o_k − 1 − e_k; at the central poles
this is 17 − 10 = 7. So Lemma B′ lowers the model by exactly 1 on (61n, 63n].

COMPUTED-EXACT against the true exponents at every prime in (m₀, m₁], for n = 20, 30, 40, 50, 60, 80, 100, 130, 160,
200: Lemma B′ **equals the true exponent at every prime**, with no violation of true ≤ B′ ≤ model. It gains
2.17 / 2.10 / 1.96 per n over the model at n = 200 / 100 / 160; the asymptotic gain is 2 per n. So the refined margin
of window-19-probe §3.1 (≈ +19) becomes ≈ +21.

## 7. Theorem G (general configurations) — PROVED; two controls COMPUTED-EXACT

**Hypotheses.**
- r, q odd, q ≥ r+4.
- η₁ ≤ … ≤ η_q < η₀/2 with Ση ≤ η₀(q−r)/2, h₀ = η₀n + 2, h_j = η_jn + 1.
- (G1) η₁ < η_{r+1}.
- (G2) η₁ + 2η_{r+1} < η₀.

**Notation.**
- M := η₀ − η₁ − η_{r+1}.
- μ₁ := #{j : η_j = η₁}; (G1) gives μ₁ ≤ r.
- e := r − μ₁ and o := #{j > r : η_j = η_{r+1}}.
- β and Q_c as above; the ρ in (5.1) uses the same formula with r in place of 5.

**Statement.** Let n be large compared with c, and let ℓ = Mn − c be prime with ℓ ∤ β·num(Q_c). Then:
- v_ℓ(c_s) ≥ 0 for all s;
- v_ℓ(c₀) = e − o − r + 1 < 0;
- ℓ^{−(e−o−r+1)}c₀ ≡ −β Q_c u_{k*} (mod ℓ).

**Proof.** Identical to §§2–5.
- (G1) and (G2) give m₀ = max(η_r, η₀−2η_{r+1})n < Mn, and |h₀−2k| < ℓ on K.
- (G2) gives |l−k| < 2ℓ and k+ℓ > h₀−1 on K, and h₀−k < ℓ.
- η_q + η₁ < η₀ puts the remaining factors of (5.1) in (−ℓ, ℓ) ∖ {0} for n > c+1.
- e − o − r + 1 ≤ −1 always, because μ₁ ≥ 1 and o ≥ 1.

**Controls** (`other/`; ℓ-adic engine):

| config | M | e, o | β | exponent | Q₁ | runs |
|---|---|---|---|---|---|---|
| this proof (η₀ = 160) | 63 | 1, 2 | −4 | −5 | 984698059590803/1545332660300000 | 158 values of n (≤ 400, and 600 … 1508), all ok |
| Zudilin Thm 3 (r = 3, η₀ = 91, η = (27³, 29, …, 38)) | 35 | 0, 1 | 1 | −3 | 3612505373/7626585373 | 33 values of n (c = 1, 2, n ≤ 80), all ok |
| η₀ = 320 (margin 10.79) | 126 | 2, 2 | 3 | −4 | 46917142797143/73614028545200 | 14 values of n (c = 1, n ≤ 30), all ok |

So the arithmetic nonvanishing also gives an alternative to Zudilin's own analytic lower bound in his Theorem 3.

## 8. Verification inventory

Two independent exact engines were used.

**`padic_form.py` (new).** An ℓ-adic engine with fixed absolute precision ℓ^{v+24}:
- it expands G_k through prefix tables of unit products and unit power sums mod ℓ²⁴;
- it builds the series by exp/log;
- it multiplies ℓ-divisible factors in explicitly;
- H_s(k−h₁) is split into unit part + ℓ^{−s}.

**`window-19-probe/mm_engine.py` (existing).** A GPU multimodular engine: exact integers X_s = Δₙc_s by CRT, with 4
verification primes. Earlier it was validated bit-for-bit against Fractions.

| check | script → data | range | result |
|---|---|---|---|
| T1–T5 (Lemmas B–E, Thm N) at ℓ = 63n−c, c = 1, 2 | `verify_aux.py` → `verify_aux_c12.{jsonl,log}`, `verify_aux_large.{jsonl,log}` | all 152 n ∈ I₁ ∪ I₂ with n ≤ 400 (ℓ ≤ 25073); plus n = 600, 601, 1005, 1006, 1501, 1508 (ℓ up to 95003) | **158/158 pass** |
| exact integers: v_ℓ(X₀) = v_ℓ(Δₙ)−5 = 1, v_ℓ(X_s) ≥ 6, unit(X₀/ℓ) = unit(Δₙ/ℓ⁶)·(ℓ⁵c₀ mod ℓ), both engines agree on every v_ℓ(c_s) | `verify_mm.py` → `verify_mm_c12.{jsonl,log}` | all 83 n ∈ I₁ ∪ I₂ with n ≤ 198 (ℓ ≤ 12473); crt_ok in every run | **83/83 pass** |
| earlier exact data (window-19-probe `mm_q23.jsonl`) | `check_probe_data.py` → `check_probe_data.log` | n = 1…60, 80, 100, 130, 160, 200 | (a) all 56 primes 63n−c, c ≤ 5, n ≥ c+1: identical pattern; (b) Lemma B at all 930 (n, p) with p ∈ (m₀, m₁]: 0 violations |
| constants β, Q_c, exceptional primes | `aux_constants.py` → `aux_constants.{log,json}` | c ≤ 12 | c = 1, 2: no exceptional prime |
| Lemma B′ vs true exponents | `refined_compat.py` → `refined_compat.log` | 10 values of n, all primes in (m₀, m₁] | B′ = true everywhere |
| general configurations | `verify_aux.py` → `other/*.jsonl` | Thm 3 config, η₀ = 320 | all ok |

The invariant pattern at ℓ = 63n − c (both engines, every n): v_ℓ(c₀) = −5; v_ℓ(c₇, c₉, …, c₂₁) = (1, 1, 0, 0, 2, 4, 8,
10); c₅ = c_even = 0; min v_ℓ(a_{i,k}) = 0; and the leading residue ℓ⁵c₀ mod ℓ equals 4Σ_K u_k = 4Q_cu_{k*} in every
case.

## 9. Files (this folder)

- `proof.md` — this document.
- `aux_constants.py` (+ `.log`, `.json`): β, Q_c, exceptional primes.
- `padic_form.py`: independent ℓ-adic engine.
- `verify_aux.py` → `verify_aux_c12.{jsonl,log}`: T1–T5.
- `verify_mm.py` → `verify_mm_c12.{jsonl,log}`: exact CRT integers vs prediction.
- `refined_compat.py` → `refined_compat.log`: Lemma B′ and the model.
- `summarize_verif.py`: summary of the jsonl files.
- `check_probe_data.py` → `check_probe_data.log`: the pre-existing exact data at the auxiliary primes and on (m₀, m₁].
- `check_ratio_exact.py` → `check_ratio_exact.log`: (5.1) as an exact rational identity, and its reduction mod ℓ (n = 4, 5, 7, 8, 11).
- `other/`: Thm 3 and η₀ = 320 controls.
