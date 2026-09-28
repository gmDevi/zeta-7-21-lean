import Zeta2Lean.Window.Statements

set_option linter.style.header false
set_option linter.style.longLine false

/-!
# The φ-certificate (computer-assisted; docs/window/proof.md §2 "φ-integral", JTNB p. 283–284)

**Statement.** `Stmt_PhiTable` (no hypotheses): every entry `e = ⟨an, ad, bn, bd, v⟩` of `phiTable`
(2602 pieces, `Window/PhiTable.lean`) satisfies `PieceValid cfgW e`: for all `x y : ℚ` with
`a < fract x < b` (`a = an/ad`, `b = bn/bd`), `v ≤ phi0 cfgW x y`.  Together with `Stmt_PhiData` it
certifies `∫_{1/60}^{∞} φ(x) dx/x² ≥ 593.514…`, i.e. `C₂ ≤ 747.486 < 748`.

**Proof: a verified checker, evaluated by the kernel** (`decide +kernel`, no compiler trust).

1. *Terms* (`phi0_eq_phiL`).  For `cfgW`, `φ₀(x, y) = 5⌊y⌋ + Σ_{TX} c⌊A x⌋ + Σ_{TY} c⌊±(A x - y)⌋`
   (`phiL`): 19 `x`-only terms (`TX`) and 39 terms with `y` (`TY`, slopes `160`; `47, 48, 50, …, 66`
   in `⌊y - A x⌋`; `113, 112, 110, …, 94` in `⌊A x - y⌋`; all slopes distinct).
2. *Periodicity* (`phiL_add`, `phiL_fract`).  Both slope sums vanish (`slope_zero`, `shift_zero`),
   so `φ₀(x, y) = φ₀(fract x, fract y)`: it suffices to take `x ∈ (a, b)` and `y ∈ [0, 1)`.
3. *Frozen floors* (`frozen`, `fl_eq`, `val_eq`, `sum_xval`).  On a piece every term has the floor
   `G = ⌊A a⌋ = A an / ad`; the check `fOK` (`0 < A bn - G bd ≤ bd`, i.e. `G < A b ≤ G + 1`) gives
   `0 < θ(x) := A x - G < 1` on `(a, b)` (an affine function, controlled at both ends by
   `affine_pos`).  Then `⌊A x - y⌋ = G - [θ < y]` and `⌊y - A x⌋ = [θ ≤ y] - G - 1`: every `y`-term is
   a constant plus a jump at its threshold `θ`.
4. *Order of the thresholds* (`th_lt`).  With `θ(a) = ka/ad` (`ka = A an mod ad`) and
   `θ(b) = kb/bd` (`kb = A bn - G bd`), the terms are sorted by the key `ka (bd + 1) + kb`
   (lexicographic in `(ka, kb)`); `pairOK` checks `kb ≤ kb'` and `key < key'` for consecutive terms,
   hence `θ ≤ θ'` at both ends and `<` at one end, hence `θ < θ'` on `(a, b)`.
5. *The walk* (`walk_sound`).  Along the sorted thresholds, the value of `φ₀(x, ·)` in every gap
   is the constant part plus the jumps already passed; `walk` checks that all these gap values are
   `≥ v`, in `ℕ` (positive part `P`, negative part plus `v` in `M`, check `M ≤ P`).  Every `y ∈ [0, 1)`
   lies in a gap or on a threshold, and there the value equals one of the two neighbouring gap values.
6. *One piece* (`pieceOK_sound`): `pieceOK e S = true` for a list `S` of annotated terms whose
   underlying terms are a permutation of `TY` implies `v ≤ phiL x y` for `x ∈ (a, b)`, `y ∈ [0, 1)`.
7. *Chains and blocks* (`chain_sound`, `blocks_sound`).  `chain` checks consecutive pieces; each
   piece is sorted (`isort`, insertion sort, a permutation: `isort_perm`) starting from the order of
   the previous piece, which is nearly sorted already.  `blocks 50` restarts the chain from `TY` every
   50 pieces.
8. *Kernel evaluation* (`chk0` … `chk5`): `blocks 50 10 phiTableK = true` by `decide +kernel`, one
   theorem per chunk of `Window/PhiTable.lean`.

**Kernel-efficiency notes** (measured with `-DElab.async=false` and the profiler, 2026-09-26).
Everything the kernel evaluates is in `ℕ` with `Nat.mul/div/mod/sub/add/ble/blt` (GMP-accelerated
in the kernel) and `Bool`; `ℤ` arithmetic is several times slower in the kernel, so the signed
running sums are split into `P` and `M`.  Recursion is written with `List.rec` directly (no
`brecOn`).  Starting each sort from the previous piece's order makes the whole check about five
times faster than sorting every piece from `TY`.  The cost per piece grows with the length of a
chain inside one `decide`, hence the blocks of 50.  Kernel time for the six chunks: 20–75 s, and
the whole file elaborates in 35–120 s, depending on the machine load; peak memory is about 0.9 GB
above the bare import of `Window.Statements`.  The checker is tight: it accepts all 2602 pieces,
and raising any single `v` by one makes it fail (checked with `#eval` during development).

**Status: complete** (axioms `propext`, `Classical.choice`, `Quot.sound` only).
-/

namespace ZetaWindow

namespace PhiTable

/-! ## The 58 terms of `φ₀` for `cfgW` -/

/-- An `x`-only term `c ⌊A x⌋` of `φ₀`, with `c = -m` if `neg` and `c = m` otherwise. -/
structure XT where
  A : ℕ
  neg : Bool
  m : ℕ

/-- A term of `φ₀` involving `y`: `c ⌊A x - y⌋` if `st`, `c ⌊y - A x⌋` otherwise, with `|c| = m`.
`pc` records the sign of its constant part on a piece (`c = m` iff `st = pc`). -/
structure YT where
  A : ℕ
  st : Bool
  pc : Bool
  m : ℕ

/-- The coefficient of an `x`-term. -/
def XT.c (t : XT) : ℤ := if t.neg then -(t.m : ℤ) else (t.m : ℤ)

/-- The coefficient of a `y`-term. -/
def YT.c (t : YT) : ℤ := if t.st = t.pc then (t.m : ℤ) else -(t.m : ℤ)

/-- Value of an `x`-term. -/
def XT.val (t : XT) (x : ℚ) : ℤ := t.c * ⌊(t.A : ℚ) * x⌋

/-- The floor of a `y`-term. -/
def YT.fl (t : YT) (x y : ℚ) : ℤ :=
  if t.st then ⌊(t.A : ℚ) * x - y⌋ else ⌊y - (t.A : ℚ) * x⌋

/-- Value of a `y`-term. -/
def YT.val (t : YT) (x y : ℚ) : ℤ := t.c * t.fl x y

/-- The `x`-only terms: `-8⌊47x⌋ - 2⌊48x⌋ + 2⌊60x⌋ + ⌊58x⌋ + ⌊56x⌋ + ⋯ + ⌊28x⌋`. -/
def TX : List XT :=
  [⟨47, true, 8⟩, ⟨48, true, 2⟩, ⟨60, false, 2⟩, ⟨58, false, 1⟩, ⟨56, false, 1⟩, ⟨54, false, 1⟩,
   ⟨52, false, 1⟩, ⟨50, false, 1⟩, ⟨48, false, 1⟩, ⟨46, false, 1⟩, ⟨44, false, 1⟩, ⟨42, false, 1⟩,
   ⟨40, false, 1⟩, ⟨38, false, 1⟩, ⟨36, false, 1⟩, ⟨34, false, 1⟩, ⟨32, false, 1⟩, ⟨30, false, 1⟩,
   ⟨28, false, 1⟩]

/-- The terms with `y` (except `5⌊y⌋`): `5⌊160x - y⌋ - 4⌊y - 47x⌋ - ⌊y - 48x⌋ - 2⌊y - 50x⌋
- ⌊y - 51x⌋ - ⋯ - ⌊y - 66x⌋ - 4⌊113x - y⌋ - ⌊112x - y⌋ - 2⌊110x - y⌋ - ⌊109x - y⌋ - ⋯ - ⌊94x - y⌋`. -/
def TY : List YT :=
  [⟨160, true, true, 5⟩,
   ⟨47, false, true, 4⟩, ⟨48, false, true, 1⟩, ⟨50, false, true, 2⟩, ⟨51, false, true, 1⟩,
   ⟨52, false, true, 1⟩, ⟨53, false, true, 1⟩, ⟨54, false, true, 1⟩, ⟨55, false, true, 1⟩,
   ⟨56, false, true, 1⟩, ⟨57, false, true, 1⟩, ⟨58, false, true, 1⟩, ⟨59, false, true, 1⟩,
   ⟨60, false, true, 1⟩, ⟨61, false, true, 1⟩, ⟨62, false, true, 1⟩, ⟨63, false, true, 1⟩,
   ⟨64, false, true, 1⟩, ⟨65, false, true, 1⟩, ⟨66, false, true, 1⟩,
   ⟨113, true, false, 4⟩, ⟨112, true, false, 1⟩, ⟨110, true, false, 2⟩, ⟨109, true, false, 1⟩,
   ⟨108, true, false, 1⟩, ⟨107, true, false, 1⟩, ⟨106, true, false, 1⟩, ⟨105, true, false, 1⟩,
   ⟨104, true, false, 1⟩, ⟨103, true, false, 1⟩, ⟨102, true, false, 1⟩, ⟨101, true, false, 1⟩,
   ⟨100, true, false, 1⟩, ⟨99, true, false, 1⟩, ⟨98, true, false, 1⟩, ⟨97, true, false, 1⟩,
   ⟨96, true, false, 1⟩, ⟨95, true, false, 1⟩, ⟨94, true, false, 1⟩]

/-- `φ₀` for `cfgW`, term by term. -/
def phiL (x y : ℚ) : ℤ :=
  5 * ⌊y⌋ + (TX.map fun t => t.val x).sum + (TY.map fun t => t.val x y).sum

theorem phi0_eq_phiL (x y : ℚ) : phi0 cfgW x y = phiL x y := by
  simp only [phi0, cfgW, phiL, TX, TY, XT.val, YT.val, YT.fl, XT.c, YT.c, List.map_cons,
    List.map_nil, List.sum_cons, List.sum_nil]
  simp [Finset.sum_Icc_succ_top, etaW]
  ring_nf

/-! ## Periodicity -/

theorem XT.val_add (t : XT) (x : ℚ) (k : ℤ) : t.val (x + k) = t.val x + t.c * (t.A : ℤ) * k := by
  unfold XT.val
  rw [show (t.A : ℚ) * (x + k) = (t.A : ℚ) * x + ((t.A * k : ℤ) : ℚ) by push_cast; ring,
    Int.floor_add_intCast]
  ring

/-- Slope of a `y`-term in `x`. -/
def ySlope (t : YT) : ℤ := t.c * (if t.st then (t.A : ℤ) else -(t.A : ℤ))

/-- Slope of a `y`-term in `y`. -/
def yShift (t : YT) : ℤ := t.c * (if t.st then (-1 : ℤ) else 1)

theorem YT.val_add (t : YT) (x y : ℚ) (k k' : ℤ) :
    t.val (x + k) (y + k') = t.val x y + ySlope t * k + yShift t * k' := by
  rcases t with ⟨A, st, pc, m⟩
  cases st
  · simp only [YT.val, YT.fl, ySlope, yShift, Bool.false_eq_true, ↓reduceIte]
    rw [show y + k' - (A : ℚ) * (x + k) = (y - (A : ℚ) * x) + ((k' - A * k : ℤ) : ℚ) by
      push_cast; ring, Int.floor_add_intCast]
    ring
  · simp only [YT.val, YT.fl, ySlope, yShift, ↓reduceIte]
    rw [show (A : ℚ) * (x + k) - (y + k') = ((A : ℚ) * x - y) + ((A * k - k' : ℤ) : ℚ) by
      push_cast; ring, Int.floor_add_intCast]
    ring

theorem sumX_add (l : List XT) (x : ℚ) (k : ℤ) :
    (l.map fun t => t.val (x + k)).sum =
      (l.map fun t => t.val x).sum + (l.map fun t => t.c * (t.A : ℤ)).sum * k := by
  induction l with
  | nil => simp
  | cons t l ih =>
    simp only [List.map_cons, List.sum_cons]
    rw [ih, XT.val_add]
    ring

theorem sumY_add (l : List YT) (x y : ℚ) (k k' : ℤ) :
    (l.map fun t => t.val (x + k) (y + k')).sum =
      (l.map fun t => t.val x y).sum + (l.map ySlope).sum * k + (l.map yShift).sum * k' := by
  induction l with
  | nil => simp
  | cons t l ih =>
    simp only [List.map_cons, List.sum_cons]
    rw [ih, YT.val_add]
    ring

theorem slope_zero : (TX.map fun t => t.c * (t.A : ℤ)).sum + (TY.map ySlope).sum = 0 := by
  decide

theorem shift_zero : 5 + (TY.map yShift).sum = 0 := by
  decide

theorem phiL_add (x y : ℚ) (k k' : ℤ) : phiL (x + k) (y + k') = phiL x y := by
  unfold phiL
  rw [sumX_add, sumY_add, Int.floor_add_intCast]
  linear_combination k * slope_zero + k' * shift_zero

theorem phiL_fract (x y : ℚ) : phiL x y = phiL (Int.fract x) (Int.fract y) := by
  conv_lhs => rw [← Int.fract_add_floor x, ← Int.fract_add_floor y]
  exact phiL_add _ _ _ _

/-! ## The checker (kernel-evaluable, natural numbers only) -/

/-- A `y`-term annotated on a piece `(a, b) = (an/ad, bn/bd)`: the frozen floor `G = ⌊A a⌋`,
`ka = A an - G ad` (so `θ(a) = ka/ad` for the threshold `θ(x) = A x - G`), `kb = A bn - G bd`
(`θ(b) = kb/bd`), and the sort key `ka (bd + 1) + kb` (lexicographic in `(ka, kb)`). -/
structure U where
  t : YT
  G : ℕ
  ka : ℕ
  kb : ℕ
  key : ℕ

/-- Annotate a `y`-term on a piece. -/
def mkU (e : Piece) (t : YT) : U :=
  let Aan := Nat.mul t.A e.an
  let G := Nat.div Aan e.ad
  let ka := Nat.mod Aan e.ad
  let kb := Nat.sub (Nat.mul t.A e.bn) (Nat.mul G e.bd)
  ⟨t, G, ka, kb, Nat.add (Nat.mul ka (Nat.succ e.bd)) kb⟩

/-- Insert by key. -/
def ins (u : U) (l : List U) : List U :=
  List.rec (motive := fun _ => List U) [u]
    (fun v l r => cond (Nat.ble u.key v.key) (u :: v :: l) (v :: r)) l

/-- Insertion sort by key (linear on an already sorted list). -/
def isort (l : List U) : List U :=
  List.rec (motive := fun _ => List U) [] (fun u _ r => ins u r) l

/-- Frozen-floor check `0 < kb ≤ bd`, i.e. `G < A b ≤ G + 1`. -/
def fOK (e : Piece) (kb : ℕ) : Bool := Nat.blt 0 kb && Nat.ble kb e.bd

/-- Consecutive thresholds: `kb ≤ kb'` and `key < key'` (so `θ ≤ θ'` at both ends, not equal). -/
def pairOK (u u' : U) : Bool := Nat.ble u.kb u'.kb && Nat.blt u.key u'.key

/-- Magnitude of the constant part: `m G` (`st`) or `m (G + 1)` (`!st`). -/
def cmag (u : U) : ℕ := Nat.mul u.t.m (cond u.t.st u.G (Nat.succ u.G))

/-- The walk along the sorted thresholds with running positive part `P` and negative part `M`
(including `v`): checks `M ≤ P` in every gap. -/
def walk (e : Piece) (l : List U) : ℕ → ℕ → U → Bool :=
  List.rec (motive := fun _ => ℕ → ℕ → U → Bool)
    (fun P M u => fOK e u.kb && Nat.ble M P &&
      cond u.t.pc (Nat.ble (Nat.add M u.t.m) P) (Nat.ble M (Nat.add P u.t.m)))
    (fun u' _ r P M u => fOK e u.kb && pairOK u u' && Nat.ble M P &&
      cond u.t.pc (r P (Nat.add M u.t.m) u') (r (Nat.add P u.t.m) M u'))
    l

/-- Positive constant parts. -/
def sumP (l : List U) : ℕ :=
  List.rec (motive := fun _ => ℕ) 0 (fun u _ r => cond u.t.pc (Nat.add (cmag u) r) r) l

/-- Negative constant parts. -/
def sumM (l : List U) : ℕ :=
  List.rec (motive := fun _ => ℕ) 0 (fun u _ r => cond u.t.pc r (Nat.add (cmag u) r)) l

/-- Frozen floor `⌊A a⌋` of an `x`-term. -/
def xG (e : Piece) (t : XT) : ℕ := Nat.div (Nat.mul t.A e.an) e.ad

/-- Frozen-floor checks of the `x`-terms. -/
def xOK (e : Piece) (l : List XT) : Bool :=
  List.rec (motive := fun _ => Bool) true
    (fun t _ r => fOK e (Nat.sub (Nat.mul t.A e.bn) (Nat.mul (xG e t) e.bd)) && r) l

/-- Positive part of the `x`-terms. -/
def xP (e : Piece) (l : List XT) : ℕ :=
  List.rec (motive := fun _ => ℕ) 0
    (fun t _ r => cond t.neg r (Nat.add (Nat.mul t.m (xG e t)) r)) l

/-- Negative part of the `x`-terms. -/
def xM (e : Piece) (l : List XT) : ℕ :=
  List.rec (motive := fun _ => ℕ) 0
    (fun t _ r => cond t.neg (Nat.add (Nat.mul t.m (xG e t)) r) r) l

/-- The check of one piece, given its annotated `y`-terms sorted by threshold. -/
def pieceOK (e : Piece) (S : List U) : Bool :=
  Nat.blt 0 e.ad && Nat.blt 0 e.bd && xOK e TX &&
    List.rec (motive := fun _ => Bool) false
      (fun u l _ => walk e l (Nat.add (xP e TX) (sumP S))
        (Nat.add e.v (Nat.add (xM e TX) (sumM S))) u) S

/-- `List.map (mkU e)`. -/
def mapU (e : Piece) (l : List YT) : List U :=
  List.rec (motive := fun _ => List U) [] (fun t _ r => mkU e t :: r) l

/-- `List.map U.t`. -/
def mapT (l : List U) : List YT :=
  List.rec (motive := fun _ => List YT) [] (fun u _ r => u.t :: r) l

/-- Check consecutive pieces; the term order of each piece is sorted starting from the order of
the previous piece (nearly sorted already). -/
def chain (T : List Piece) : List YT → Bool :=
  List.rec (motive := fun _ => List YT → Bool) (fun _ => true)
    (fun e _ r L => let S := isort (mapU e L); pieceOK e S && r (mapT S)) T

/-- Check `T` in blocks of `K` consecutive pieces, each block starting from `TY` (`f` = fuel). -/
def blocks (K f : ℕ) (T : List Piece) : Bool :=
  Nat.rec (motive := fun _ => List Piece → Bool) (fun T => T.isEmpty)
    (fun _ r T => chain (T.take K) TY && r (T.drop K)) f T

/-! ## Soundness -/

theorem nat_div_eq (a b : ℕ) : Nat.div a b = a / b := rfl

theorem nat_mod_eq (a b : ℕ) : Nat.mod a b = a % b := rfl

theorem nat_sub_eq (a b : ℕ) : Nat.sub a b = a - b := rfl

@[simp] theorem mkU_t (e : Piece) (t : YT) : (mkU e t).t = t := rfl

theorem mkU_G (e : Piece) (t : YT) : (mkU e t).G = t.A * e.an / e.ad := rfl

theorem mkU_ka (e : Piece) (t : YT) : (mkU e t).ka = t.A * e.an % e.ad := rfl

theorem mkU_kb (e : Piece) (t : YT) : (mkU e t).kb = t.A * e.bn - t.A * e.an / e.ad * e.bd := rfl

theorem mkU_key (e : Piece) (t : YT) :
    (mkU e t).key = (mkU e t).ka * (e.bd + 1) + (mkU e t).kb := rfl

theorem fOK_iff (e : Piece) (kb : ℕ) : fOK e kb = true ↔ 0 < kb ∧ kb ≤ e.bd := by
  simp [fOK, Nat.blt_eq, Nat.ble_eq]

theorem pairOK_iff (u u' : U) : pairOK u u' = true ↔ u.kb ≤ u'.kb ∧ u.key < u'.key := by
  simp [pairOK, Nat.blt_eq, Nat.ble_eq]

/-- An affine function `≥ 0` at both ends of `(a, b)` and `> 0` at one of them is `> 0` inside. -/
theorem affine_pos {a b x fa fb fx : ℚ} (hax : a < x) (hxb : x < b) (hfa : 0 ≤ fa) (hfb : 0 ≤ fb)
    (hpos : 0 < fa ∨ 0 < fb) (hid : fx * (b - a) = fa * (b - x) + fb * (x - a)) : 0 < fx := by
  have hba : 0 < b - a := by linarith
  have h : 0 < fa * (b - x) + fb * (x - a) := by
    rcases hpos with h | h
    · have h1 := mul_pos h (sub_pos.2 hxb)
      have h2 := mul_nonneg hfb (sub_nonneg.2 hax.le)
      linarith
    · have h1 := mul_pos h (sub_pos.2 hax)
      have h2 := mul_nonneg hfa (sub_nonneg.2 hxb.le)
      linarith
  rw [← hid] at h
  by_contra hc
  push Not at hc
  have := mul_nonpos_of_nonpos_of_nonneg hc hba.le
  linarith

section Piece

variable {e : Piece}

/-- Left end: `A a = G + ka/ad` with `G = ⌊A an / ad⌋`, `ka = A an mod ad`. -/
theorem left_eq (had : 0 < e.ad) (A : ℕ) :
    (A : ℚ) * e.a = ((A * e.an / e.ad : ℕ) : ℚ) + ((A * e.an % e.ad : ℕ) : ℚ) / e.ad := by
  have h := Nat.div_add_mod (A * e.an) e.ad
  have had' : (0 : ℚ) < e.ad := by exact_mod_cast had
  have h' : ((e.ad * (A * e.an / e.ad) + A * e.an % e.ad : ℕ) : ℚ) = ((A * e.an : ℕ) : ℚ) := by
    rw [h]
  push_cast at h'
  unfold Piece.a
  field_simp
  linarith

/-- Right end: `A b = G + kb/bd` when `kb = A bn - G bd > 0`. -/
theorem right_eq (hbd : 0 < e.bd) (A : ℕ) (hkb : 0 < A * e.bn - A * e.an / e.ad * e.bd) :
    (A : ℚ) * e.b = ((A * e.an / e.ad : ℕ) : ℚ) +
      ((A * e.bn - A * e.an / e.ad * e.bd : ℕ) : ℚ) / e.bd := by
  have hlt : A * e.an / e.ad * e.bd < A * e.bn := Nat.sub_pos_iff_lt.1 hkb
  have hbd' : (0 : ℚ) < e.bd := by exact_mod_cast hbd
  rw [Nat.cast_sub hlt.le]
  push_cast
  unfold Piece.b
  field_simp
  ring

/-- The threshold `θ(x) = A x - G` of an annotated term. -/
def th (u : U) (x : ℚ) : ℚ := (u.t.A : ℚ) * x - u.G

/-- The frozen floor: if `0 < kb ≤ bd` then `0 < A x - G < 1` on `(a, b)`. -/
theorem frozen (had : 0 < e.ad) (hbd : 0 < e.bd) {x : ℚ} (hax : e.a < x) (hxb : x < e.b)
    (A : ℕ) (hkb : 0 < A * e.bn - A * e.an / e.ad * e.bd)
    (hkb' : A * e.bn - A * e.an / e.ad * e.bd ≤ e.bd) :
    0 < (A : ℚ) * x - ((A * e.an / e.ad : ℕ) : ℚ) ∧
      (A : ℚ) * x - ((A * e.an / e.ad : ℕ) : ℚ) < 1 := by
  have hL := left_eq had A
  have hR := right_eq hbd A hkb
  set G : ℚ := ((A * e.an / e.ad : ℕ) : ℚ)
  set ka : ℚ := ((A * e.an % e.ad : ℕ) : ℚ) with hka_def
  set kb : ℚ := ((A * e.bn - A * e.an / e.ad * e.bd : ℕ) : ℚ) with hkb_def
  have had' : (0 : ℚ) < e.ad := by exact_mod_cast had
  have hbd' : (0 : ℚ) < e.bd := by exact_mod_cast hbd
  have hka0 : 0 ≤ ka := by positivity
  have hka1 : ka < e.ad := by
    rw [hka_def]; exact_mod_cast Nat.mod_lt _ had
  have hkb0 : 0 < kb := by rw [hkb_def]; exact_mod_cast hkb
  have hkb1 : kb ≤ e.bd := by rw [hkb_def]; exact_mod_cast hkb'
  have hfa0 : 0 ≤ ka / e.ad := div_nonneg hka0 had'.le
  have hfa1 : 0 < 1 - ka / e.ad := by rw [sub_pos, div_lt_one had']; exact hka1
  have hfb0 : 0 < kb / e.bd := div_pos hkb0 hbd'
  have hfb1 : 0 ≤ 1 - kb / e.bd := by rw [sub_nonneg, div_le_one hbd']; exact hkb1
  constructor
  · refine affine_pos hax hxb hfa0 hfb0.le (Or.inr hfb0) ?_
    linear_combination (e.b - x) * hL + (x - e.a) * hR
  · have := affine_pos (fx := 1 - ((A : ℚ) * x - G)) hax hxb hfa1.le hfb1 (Or.inl hfa1) (by
      linear_combination (-(e.b - x)) * hL + (-(x - e.a)) * hR)
    linarith

/-- The order of two thresholds on `(a, b)` from `pairOK`. -/
theorem th_lt (had : 0 < e.ad) (hbd : 0 < e.bd) {x : ℚ} (hax : e.a < x) (hxb : x < e.b)
    (t t' : YT) (hf : fOK e (mkU e t).kb = true) (hf' : fOK e (mkU e t').kb = true)
    (hp : pairOK (mkU e t) (mkU e t') = true) : th (mkU e t) x < th (mkU e t') x := by
  rw [fOK_iff, mkU_kb] at hf hf'
  rw [pairOK_iff, mkU_key, mkU_key, mkU_ka, mkU_ka, mkU_kb, mkU_kb] at hp
  obtain ⟨hle, hlt⟩ := hp
  -- lexicographic comparison of `(ka, kb)`
  set ka := t.A * e.an % e.ad
  set ka' := t'.A * e.an % e.ad
  set kb := t.A * e.bn - t.A * e.an / e.ad * e.bd
  set kb' := t'.A * e.bn - t'.A * e.an / e.ad * e.bd
  have hlex : ka ≤ ka' ∧ (ka < ka' ∨ kb < kb') := by
    have h1 : ka ≤ ka' := by
      by_contra h
      push Not at h
      have h2 : (ka' + 1) * (e.bd + 1) ≤ ka * (e.bd + 1) := Nat.mul_le_mul_right _ h
      nlinarith [hf'.2]
    refine ⟨h1, ?_⟩
    rcases Nat.lt_or_ge ka ka' with h | h
    · exact Or.inl h
    · right
      have h3 : ka = ka' := le_antisymm h1 h
      rw [h3] at hlt
      omega
  have hL := left_eq had t.A
  have hL' := left_eq had t'.A
  have hR := right_eq hbd t.A hf.1
  have hR' := right_eq hbd t'.A hf'.1
  have had' : (0 : ℚ) < e.ad := by exact_mod_cast had
  have hbd' : (0 : ℚ) < e.bd := by exact_mod_cast hbd
  have hfa : 0 ≤ (ka' : ℚ) / e.ad - (ka : ℚ) / e.ad := by
    rw [← sub_div]; apply div_nonneg _ had'.le; rw [sub_nonneg]; exact_mod_cast hlex.1
  have hfb : 0 ≤ (kb' : ℚ) / e.bd - (kb : ℚ) / e.bd := by
    rw [← sub_div]; apply div_nonneg _ hbd'.le; rw [sub_nonneg]; exact_mod_cast hle
  have hpos : 0 < (ka' : ℚ) / e.ad - (ka : ℚ) / e.ad ∨ 0 < (kb' : ℚ) / e.bd - (kb : ℚ) / e.bd := by
    rcases hlex.2 with h | h
    · left; rw [← sub_div]; apply div_pos _ had'; rw [sub_pos]; exact_mod_cast h
    · right; rw [← sub_div]; apply div_pos _ hbd'; rw [sub_pos]; exact_mod_cast h
  have := affine_pos (fx := th (mkU e t') x - th (mkU e t) x) hax hxb hfa hfb hpos (by
    simp only [th, mkU_t, mkU_G]
    linear_combination (e.b - x) * hL' - (e.b - x) * hL + (x - e.a) * hR' - (x - e.a) * hR)
  linarith

end Piece

/-! ### Indicators and the walk -/

/-- Whether `y` is past the threshold of `u` (`θ < y` for `⌊A x - y⌋`, `θ ≤ y` for `⌊y - A x⌋`). -/
def U.ind (u : U) (x y : ℚ) : ℤ :=
  if u.t.st then (if th u x < y then 1 else 0) else (if th u x ≤ y then 1 else 0)

/-- The jump of `φ₀` at the threshold of `u`. -/
def U.J (u : U) : ℤ := if u.t.pc then -(u.t.m : ℤ) else (u.t.m : ℤ)

theorem ind_of_lt {u : U} {x y : ℚ} (h : y < th u x) : u.ind x y = 0 := by
  unfold U.ind
  have h1 : ¬ th u x < y := not_lt.2 h.le
  have h2 : ¬ th u x ≤ y := not_le.2 h
  simp only [h1, h2, ↓reduceIte, ite_self]

theorem ind_cases (u : U) (x y : ℚ) : (u.ind x y = 0 ∧ y ≤ th u x) ∨ u.ind x y = 1 := by
  unfold U.ind
  by_cases h1 : th u x < y
  · by_cases h2 : th u x ≤ y
    · right; simp only [h1, h2, ↓reduceIte, ite_self]
    · exact absurd h1.le h2
  · by_cases h2 : th u x ≤ y
    · have h3 : th u x = y := le_antisymm h2 (not_lt.1 h1)
      cases u.t.st
      · right; simp only [h2, ↓reduceIte, Bool.false_eq_true]
      · left; exact ⟨by simp only [h1, ↓reduceIte], h3.ge⟩
    · left; exact ⟨by simp only [h1, h2, ↓reduceIte, ite_self], (not_le.1 h2).le⟩

theorem walk_nil (e : Piece) (P M : ℕ) (u : U) :
    walk e [] P M u = (fOK e u.kb && Nat.ble M P &&
      cond u.t.pc (Nat.ble (Nat.add M u.t.m) P) (Nat.ble M (Nat.add P u.t.m))) := rfl

theorem walk_cons (e : Piece) (u' : U) (l : List U) (P M : ℕ) (u : U) :
    walk e (u' :: l) P M u = (fOK e u.kb && pairOK u u' && Nat.ble M P &&
      cond u.t.pc (walk e l P (Nat.add M u.t.m) u') (walk e l (Nat.add P u.t.m) M u')) := rfl

theorem jump_ok (u : U) (P M : ℕ)
    (h : cond u.t.pc (Nat.ble (Nat.add M u.t.m) P) (Nat.ble M (Nat.add P u.t.m)) = true) :
    (0 : ℤ) ≤ (P : ℤ) - M + u.J := by
  unfold U.J
  cases hpc : u.t.pc <;> rw [hpc] at h <;> simp only [Bool.cond_true, Bool.cond_false] at h <;>
    have h' := Nat.le_of_ble_eq_true h <;> simp only [Nat.add_eq] at h' <;>
    simp only [Bool.false_eq_true, ↓reduceIte] <;> omega

theorem cond_walk {e : Piece} {l : List U} {u u' : U} {P M : ℕ}
    (h : cond u.t.pc (walk e l P (Nat.add M u.t.m) u') (walk e l (Nat.add P u.t.m) M u') = true) :
    ∃ P' M' : ℕ, walk e l P' M' u' = true ∧ (P' : ℤ) - M' = (P : ℤ) - M + u.J := by
  unfold U.J
  cases hpc : u.t.pc <;> rw [hpc] at h <;> simp only [Bool.cond_true, Bool.cond_false] at h
  · exact ⟨_, _, h, by simp only [Nat.add_eq, Bool.false_eq_true, ↓reduceIte]; push_cast; ring⟩
  · exact ⟨_, _, h, by simp only [Nat.add_eq, ↓reduceIte]; push_cast; ring⟩

/-- **The walk.**  If the walk succeeds, every gap value `P - M + (jumps passed)` is `≥ 0`; the
thresholds are ordered because consecutive ones pass `pairOK`. -/
theorem walk_sound (e : Piece) (x : ℚ) (Q : U → Prop)
    (hord : ∀ u u' : U, Q u → Q u' → fOK e u.kb = true → fOK e u'.kb = true →
      pairOK u u' = true → th u x < th u' x) :
    ∀ (l : List U) (P M : ℕ) (u : U), (∀ w ∈ u :: l, Q w) → walk e l P M u = true →
      (∀ w ∈ u :: l, fOK e w.kb = true) ∧ ∀ y : ℚ,
        (0 : ℤ) ≤ (P : ℤ) - M + ((u :: l).map fun w => w.J * w.ind x y).sum ∧
        (y < th u x → ((u :: l).map fun w => w.J * w.ind x y).sum = 0) := by
  intro l
  induction l with
  | nil =>
    intro P M u _ h
    rw [walk_nil] at h
    simp only [Bool.and_eq_true] at h
    obtain ⟨⟨hf, hMP⟩, hc⟩ := h
    have hMP' : (M : ℤ) ≤ P := by exact_mod_cast Nat.le_of_ble_eq_true hMP
    refine ⟨by simpa using hf, fun y => ⟨?_, fun hy => ?_⟩⟩
    · simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero]
      rcases ind_cases u x y with ⟨hi, _⟩ | hi
      · rw [hi, mul_zero, add_zero]; linarith
      · rw [hi, mul_one]; exact jump_ok u P M hc
    · simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero]
      rw [ind_of_lt hy, mul_zero]
  | cons u' l ih =>
    intro P M u hQ h
    rw [walk_cons] at h
    simp only [Bool.and_eq_true] at h
    obtain ⟨⟨⟨hf, hp⟩, hMP⟩, hc⟩ := h
    obtain ⟨P', M', hw, hPM⟩ := cond_walk hc
    have hQ' : ∀ w ∈ u' :: l, Q w := fun w hw => hQ w (List.mem_cons_of_mem _ hw)
    obtain ⟨hfs, hy⟩ := ih P' M' u' hQ' hw
    have hf' : fOK e u'.kb = true := hfs u' (by simp)
    have hlt : th u x < th u' x := hord u u' (hQ u (by simp)) (hQ' u' (by simp)) hf hf' hp
    have hMP' : (M : ℤ) ≤ P := by exact_mod_cast Nat.le_of_ble_eq_true hMP
    refine ⟨?_, fun y => ?_⟩
    · intro w hw'
      rcases List.mem_cons.1 hw' with hw'' | hw''
      · rw [hw'']; exact hf
      · exact hfs w hw''
    · obtain ⟨hy1, hy2⟩ := hy y
      simp only [List.map_cons, List.sum_cons] at hy1 hy2 ⊢
      constructor
      · rcases ind_cases u x y with ⟨hi, hyle⟩ | hi
        · rw [hi, mul_zero, zero_add, hy2 (lt_of_le_of_lt hyle hlt)]
          linarith
        · rw [hi, mul_one]
          linarith
      · intro hyu
        rw [ind_of_lt hyu, mul_zero, zero_add]
        exact hy2 (hyu.trans hlt)

/-! ### Values of the terms on a piece -/

section Piece2

variable {e : Piece}

/-- The floor of a `y`-term on the piece, through the indicator of its threshold. -/
theorem fl_eq (had : 0 < e.ad) (hbd : 0 < e.bd) {x y : ℚ} (hax : e.a < x) (hxb : x < e.b)
    (hy0 : 0 ≤ y) (hy1 : y < 1) (t : YT) (hf : fOK e (mkU e t).kb = true) :
    t.fl x y = if t.st then ((mkU e t).G : ℤ) - (mkU e t).ind x y
      else (mkU e t).ind x y - ((mkU e t).G + 1) := by
  rw [fOK_iff, mkU_kb] at hf
  obtain ⟨h0, h1⟩ := frozen had hbd hax hxb t.A hf.1 hf.2
  have hth : th (mkU e t) x = (t.A : ℚ) * x - ((t.A * e.an / e.ad : ℕ) : ℚ) := by
    simp only [th, mkU_t, mkU_G]
  rw [← hth] at h0 h1
  have hAx : (t.A : ℚ) * x = ((mkU e t).G : ℚ) + th (mkU e t) x := by
    simp only [th, mkU_t]; ring
  unfold YT.fl U.ind
  simp only [mkU_t]
  by_cases hst : t.st = true
  swap
  · simp only [hst, Bool.false_eq_true, ↓reduceIte]
    by_cases h : th (mkU e t) x ≤ y
    · simp only [h, ↓reduceIte]
      rw [Int.floor_eq_iff]
      push_cast
      constructor <;> linarith
    · simp only [h, ↓reduceIte]
      rw [Int.floor_eq_iff]
      push_cast
      push Not at h
      constructor <;> linarith
  · simp only [hst, ↓reduceIte]
    by_cases h : th (mkU e t) x < y
    · simp only [h, ↓reduceIte]
      rw [Int.floor_eq_iff]
      push_cast
      constructor <;> linarith
    · simp only [h, ↓reduceIte]
      rw [Int.floor_eq_iff]
      push_cast
      push Not at h
      constructor <;> linarith

/-- The value of a `y`-term on the piece: constant part plus jump times indicator. -/
theorem val_eq (had : 0 < e.ad) (hbd : 0 < e.bd) {x y : ℚ} (hax : e.a < x) (hxb : x < e.b)
    (hy0 : 0 ≤ y) (hy1 : y < 1) (t : YT) (hf : fOK e (mkU e t).kb = true) :
    t.val x y = (if t.pc then ((cmag (mkU e t) : ℕ) : ℤ) else -((cmag (mkU e t) : ℕ) : ℤ)) +
      (mkU e t).J * (mkU e t).ind x y := by
  rw [YT.val, fl_eq had hbd hax hxb hy0 hy1 t hf]
  unfold cmag U.J
  simp only [mkU_t]
  rcases t with ⟨A, st, pc, m⟩
  cases st <;> cases pc <;>
    simp only [YT.c, Bool.false_eq_true, ↓reduceIte, Bool.cond_true, Bool.cond_false, Nat.mul_eq,
      Nat.succ_eq_add_one] <;> push_cast <;> ring

theorem sumP_cons (u : U) (l : List U) :
    sumP (u :: l) = cond u.t.pc (Nat.add (cmag u) (sumP l)) (sumP l) := rfl

theorem sumM_cons (u : U) (l : List U) :
    sumM (u :: l) = cond u.t.pc (sumM l) (Nat.add (cmag u) (sumM l)) := rfl

theorem sum_val (had : 0 < e.ad) (hbd : 0 < e.bd) {x y : ℚ} (hax : e.a < x) (hxb : x < e.b)
    (hy0 : 0 ≤ y) (hy1 : y < 1) :
    ∀ S : List U, (∀ u ∈ S, ∃ t, u = mkU e t) → (∀ u ∈ S, fOK e u.kb = true) →
      (S.map fun u => u.t.val x y).sum =
        ((sumP S : ℕ) : ℤ) - ((sumM S : ℕ) : ℤ) + (S.map fun u => u.J * u.ind x y).sum
  | [], _, _ => by simp [sumP, sumM]
  | u :: S, hS, hf => by
    have ih := sum_val had hbd hax hxb hy0 hy1 S (fun w hw => hS w (by simp [hw]))
      (fun w hw => hf w (by simp [hw]))
    obtain ⟨t, rfl⟩ := hS u (by simp)
    have hft := hf (mkU e t) (by simp)
    simp only [List.map_cons, List.sum_cons, ih, sumP_cons, sumM_cons, mkU_t]
    rw [val_eq had hbd hax hxb hy0 hy1 t hft]
    cases t.pc <;> simp only [Bool.cond_true, Bool.cond_false, Nat.add_eq, Bool.false_eq_true,
      ↓reduceIte] <;> push_cast <;> ring

theorem xOK_cons (t : XT) (l : List XT) :
    xOK e (t :: l) = (fOK e (Nat.sub (Nat.mul t.A e.bn) (Nat.mul (xG e t) e.bd)) && xOK e l) := rfl

theorem xP_cons (t : XT) (l : List XT) :
    xP e (t :: l) = cond t.neg (xP e l) (Nat.add (Nat.mul t.m (xG e t)) (xP e l)) := rfl

theorem xM_cons (t : XT) (l : List XT) :
    xM e (t :: l) = cond t.neg (Nat.add (Nat.mul t.m (xG e t)) (xM e l)) (xM e l) := rfl

theorem sum_xval (had : 0 < e.ad) (hbd : 0 < e.bd) {x : ℚ} (hax : e.a < x) (hxb : x < e.b) :
    ∀ l : List XT, xOK e l = true →
      (l.map fun t => t.val x).sum = ((xP e l : ℕ) : ℤ) - ((xM e l : ℕ) : ℤ)
  | [], _ => by simp [xP, xM]
  | t :: l, h => by
    rw [xOK_cons] at h
    simp only [Bool.and_eq_true] at h
    obtain ⟨h1, h2⟩ := h
    have ih := sum_xval had hbd hax hxb l h2
    rw [fOK_iff] at h1
    change 0 < t.A * e.bn - t.A * e.an / e.ad * e.bd ∧ t.A * e.bn - t.A * e.an / e.ad * e.bd ≤ e.bd
      at h1
    obtain ⟨f0, f1⟩ := frozen had hbd hax hxb t.A h1.1 h1.2
    have hv : t.val x = t.c * ((xG e t : ℕ) : ℤ) := by
      have hfl : ⌊(t.A : ℚ) * x⌋ = ((t.A * e.an / e.ad : ℕ) : ℤ) := by
        generalize t.A * e.an / e.ad = G at f0 f1
        rw [Int.floor_eq_iff, Int.cast_natCast]
        constructor <;> linarith
      rw [XT.val, hfl]
      rfl
    simp only [List.map_cons, List.sum_cons]
    rw [ih, xP_cons, xM_cons, hv]
    rcases t with ⟨A, neg, m⟩
    cases neg <;> simp only [XT.c, Bool.cond_true, Bool.cond_false, Nat.add_eq, Nat.mul_eq,
      Bool.false_eq_true, ↓reduceIte] <;> push_cast <;> ring

end Piece2

/-! ### One piece, the chain, the blocks -/

theorem pieceValid_of (e : Piece)
    (h : ∀ x y : ℚ, e.a < x → x < e.b → 0 ≤ y → y < 1 → (e.v : ℤ) ≤ phiL x y) :
    PieceValid cfgW e := by
  intro x y hx1 hx2
  rw [phi0_eq_phiL, phiL_fract]
  exact h _ _ hx1 hx2 (Int.fract_nonneg y) (Int.fract_lt_one y)

theorem pieceOK_def (e : Piece) (S : List U) :
    pieceOK e S = (Nat.blt 0 e.ad && Nat.blt 0 e.bd && xOK e TX &&
      List.rec (motive := fun _ => Bool) false
        (fun u l _ => walk e l (Nat.add (xP e TX) (sumP S))
          (Nat.add e.v (Nat.add (xM e TX) (sumM S))) u) S) := rfl

/-- **Soundness of the piece check.** -/
theorem pieceOK_sound (e : Piece) (S : List U) (hS : ∀ u ∈ S, ∃ t, u = mkU e t)
    (hperm : (S.map U.t).Perm TY) (h : pieceOK e S = true) {x y : ℚ} (hax : e.a < x)
    (hxb : x < e.b) (hy0 : 0 ≤ y) (hy1 : y < 1) : (e.v : ℤ) ≤ phiL x y := by
  rw [pieceOK_def] at h
  simp only [Bool.and_eq_true] at h
  obtain ⟨⟨⟨had, hbd⟩, hx⟩, hw⟩ := h
  have had' : 0 < e.ad := by simpa [Nat.blt_eq] using had
  have hbd' : 0 < e.bd := by simpa [Nat.blt_eq] using hbd
  cases S with
  | nil => exact absurd hw (by simp)
  | cons u l =>
    have hord : ∀ w w' : U, (∃ t, w = mkU e t) → (∃ t, w' = mkU e t) → fOK e w.kb = true →
        fOK e w'.kb = true → pairOK w w' = true → th w x < th w' x := by
      rintro w w' ⟨t, rfl⟩ ⟨t', rfl⟩ hf hf' hp
      exact th_lt had' hbd' hax hxb t t' hf hf' hp
    obtain ⟨hfs, hy⟩ := walk_sound e x (fun w => ∃ t, w = mkU e t) hord l _ _ u hS hw
    obtain ⟨h1, -⟩ := hy y
    have hTY : (TY.map fun t => t.val x y).sum = ((u :: l).map fun w => w.t.val x y).sum := by
      have := (hperm.map (fun t => t.val x y)).sum_eq
      rw [List.map_map] at this
      exact this.symm
    have hy' : ⌊y⌋ = 0 := Int.floor_eq_zero_iff.2 ⟨hy0, hy1⟩
    unfold phiL
    rw [hy', hTY, sum_xval had' hbd' hax hxb TX hx, sum_val had' hbd' hax hxb hy0 hy1 _ hS hfs]
    simp only [Nat.add_eq] at h1
    push_cast at h1
    linarith

theorem mapU_eq (e : Piece) : ∀ L : List YT, mapU e L = L.map (mkU e)
  | [] => rfl
  | t :: L => by
    change mkU e t :: mapU e L = _
    rw [mapU_eq e L]
    rfl

theorem mapT_eq : ∀ S : List U, mapT S = S.map U.t
  | [] => rfl
  | u :: S => by
    change u.t :: mapT S = _
    rw [mapT_eq S]
    rfl

theorem ins_perm (u : U) : ∀ l : List U, (ins u l).Perm (u :: l)
  | [] => List.Perm.refl _
  | v :: l => by
    change (cond (Nat.ble u.key v.key) (u :: v :: l) (v :: ins u l)).Perm (u :: v :: l)
    cases Nat.ble u.key v.key
    · exact ((ins_perm u l).cons v).trans (List.Perm.swap u v l)
    · exact List.Perm.refl _

theorem isort_perm : ∀ l : List U, (isort l).Perm l
  | [] => List.Perm.refl _
  | u :: l => by
    change (ins u (isort l)).Perm (u :: l)
    exact (ins_perm u (isort l)).trans ((isort_perm l).cons u)

theorem chain_cons (e : Piece) (T : List Piece) (L : List YT) :
    chain (e :: T) L = (pieceOK e (isort (mapU e L)) && chain T (mapT (isort (mapU e L)))) := rfl

/-- **Soundness of the chain.** -/
theorem chain_sound : ∀ (T : List Piece) (L : List YT), chain T L = true → L.Perm TY →
    ∀ e ∈ T, PieceValid cfgW e
  | [], _, _, _ => fun e he => absurd he List.not_mem_nil
  | e :: T, L, h, hL => by
    rw [chain_cons] at h
    simp only [Bool.and_eq_true] at h
    obtain ⟨h1, h2⟩ := h
    have hSperm : (isort (mapU e L)).Perm (L.map (mkU e)) := by
      rw [← mapU_eq]; exact isort_perm _
    have hS : ∀ u ∈ isort (mapU e L), ∃ t, u = mkU e t := by
      intro u hu
      obtain ⟨t, -, rfl⟩ := List.mem_map.1 (hSperm.subset hu)
      exact ⟨t, rfl⟩
    have hST : ((isort (mapU e L)).map U.t).Perm TY := by
      have := hSperm.map U.t
      rw [List.map_map] at this
      have hc : (U.t ∘ mkU e) = id := by funext t; rfl
      rw [hc, List.map_id] at this
      exact this.trans hL
    intro e' he'
    rcases List.mem_cons.1 he' with heq | he''
    · subst heq
      exact pieceValid_of e' (fun x y hax hxb hy0 hy1 =>
        pieceOK_sound e' _ hS hST h1 hax hxb hy0 hy1)
    · rw [mapT_eq] at h2
      exact chain_sound T _ h2 hST e' he''

theorem blocks_zero (K : ℕ) (T : List Piece) : blocks K 0 T = T.isEmpty := rfl

theorem blocks_succ (K f : ℕ) (T : List Piece) :
    blocks K (f + 1) T = (chain (T.take K) TY && blocks K f (T.drop K)) := rfl

/-- **Soundness of the block check.** -/
theorem blocks_sound (K : ℕ) : ∀ (f : ℕ) (T : List Piece), blocks K f T = true →
    ∀ e ∈ T, PieceValid cfgW e
  | 0, T, h => by
    rw [blocks_zero, List.isEmpty_iff] at h
    subst h
    intro e he
    exact absurd he List.not_mem_nil
  | f + 1, T, h => by
    rw [blocks_succ] at h
    simp only [Bool.and_eq_true] at h
    intro e he
    rw [← List.take_append_drop K T, List.mem_append] at he
    rcases he with he | he
    · exact chain_sound _ _ h.1 (List.Perm.refl _) e he
    · exact blocks_sound K f _ h.2 e he

/-! ## The kernel computation: one theorem per chunk of `Window/PhiTable.lean` -/

set_option maxRecDepth 100000 in
/-- Pieces 0 … 449. -/
theorem chk0 : blocks 50 10 phiTable0 = true := by decide +kernel

set_option maxRecDepth 100000 in
/-- Pieces 450 … 899. -/
theorem chk1 : blocks 50 10 phiTable1 = true := by decide +kernel

set_option maxRecDepth 100000 in
/-- Pieces 900 … 1349. -/
theorem chk2 : blocks 50 10 phiTable2 = true := by decide +kernel

set_option maxRecDepth 100000 in
/-- Pieces 1350 … 1799. -/
theorem chk3 : blocks 50 10 phiTable3 = true := by decide +kernel

set_option maxRecDepth 100000 in
/-- Pieces 1800 … 2249. -/
theorem chk4 : blocks 50 10 phiTable4 = true := by decide +kernel

set_option maxRecDepth 100000 in
/-- Pieces 2250 … 2601. -/
theorem chk5 : blocks 50 10 phiTable5 = true := by decide +kernel

end PhiTable

/-- **`Stmt_PhiTable`**: every piece of the φ-table is valid (`PhiTable.blocks_sound` applied to the
six kernel-checked chunks). -/
theorem PhiTable_proof : Stmt_PhiTable := by
  intro e he
  simp only [phiTable, List.mem_append] at he
  rcases he with ((((h | h) | h) | h) | h) | h
  · exact PhiTable.blocks_sound 50 10 _ PhiTable.chk0 e h
  · exact PhiTable.blocks_sound 50 10 _ PhiTable.chk1 e h
  · exact PhiTable.blocks_sound 50 10 _ PhiTable.chk2 e h
  · exact PhiTable.blocks_sound 50 10 _ PhiTable.chk3 e h
  · exact PhiTable.blocks_sound 50 10 _ PhiTable.chk4 e h
  · exact PhiTable.blocks_sound 50 10 _ PhiTable.chk5 e h

end ZetaWindow
