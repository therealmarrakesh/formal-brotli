import Brotli.Spec.PrefixCode

/-!
# Context modeling

RFC 7932 §7.
-/

namespace Brotli.Spec

/-- p1 and p2, from the bytes so far, most recent first; zero at the start of the stream (§7.1). -/
def contextBytes : List Nat → Nat × Nat
  | [] => (0, 0)
  | [p1] => (p1, 0)
  | p1 :: p2 :: _ => (p1, p2)

/-- Lut0 (§7.1). -/
def Lut0 : List Nat :=
  [ 0,  0,  0,  0,  0,  0,  0,  0,  0,  4,  4,  0,  0,  4,  0,  0,
    0,  0,  0,  0,  0,  0,  0,  0,  0,  0,  0,  0,  0,  0,  0,  0,
    8, 12, 16, 12, 12, 20, 12, 16, 24, 28, 12, 12, 32, 12, 36, 12,
   44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 32, 32, 24, 40, 28, 12,
   12, 48, 52, 52, 52, 48, 52, 52, 52, 48, 52, 52, 52, 52, 52, 48,
   52, 52, 52, 52, 52, 48, 52, 52, 52, 52, 52, 24, 12, 28, 12, 12,
   12, 56, 60, 60, 60, 56, 60, 60, 60, 56, 60, 60, 60, 60, 60, 56,
   60, 60, 60, 60, 60, 56, 60, 60, 60, 60, 60, 24, 12, 28, 12,  0,
    0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1,
    0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1,
    0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1,
    0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1,
    2, 3, 2, 3, 2, 3, 2, 3, 2, 3, 2, 3, 2, 3, 2, 3,
    2, 3, 2, 3, 2, 3, 2, 3, 2, 3, 2, 3, 2, 3, 2, 3,
    2, 3, 2, 3, 2, 3, 2, 3, 2, 3, 2, 3, 2, 3, 2, 3,
    2, 3, 2, 3, 2, 3, 2, 3, 2, 3, 2, 3, 2, 3, 2, 3]

/-- Lut1 (§7.1). -/
def Lut1 : List Nat :=
  [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
   0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
   0, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1,
   2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 1, 1, 1, 1, 1, 1,
   1, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2,
   2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 1, 1, 1, 1, 1,
   1, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3,
   3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 1, 1, 1, 1, 0,
   0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
   0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
   0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
   0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
   0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
   0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
   2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2,
   2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2]

/-- Lut2 (§7.1). -/
def Lut2 : List Nat :=
  [0, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1,
   2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2,
   2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2,
   2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2,
   3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3,
   3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3,
   3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3,
   3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3,
   4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4,
   4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4,
   4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4,
   4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4,
   5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5,
   5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5,
   5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5,
   6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 7]

theorem Lut_lengths : Lut0.length = 256 ∧ Lut1.length = 256 ∧ Lut2.length = 256 := by
  decide +kernel

/-- The Context ID of the next literal: modes LSB6, MSB6, UTF8 and Signed are 0 to 3 (§7.1). -/
def contextId (mode p1 p2 : Nat) : Nat :=
  match mode with
  | 0 => p1 &&& 0x3f
  | 1 => p1 >>> 2
  | 2 => Lut0.getD p1 0 ||| Lut1.getD p2 0
  | _ => (Lut2.getD p1 0 <<< 3) ||| Lut2.getD p2 0

private theorem getD_lt {l : List Nat} {n : Nat} (hn : 0 < n) (h : ∀ v ∈ l, v < n) (i : Nat) :
    l.getD i 0 < n := by
  rw [List.getD_eq_getElem?_getD]
  cases hi : l[i]? with
  | none => simpa using hn
  | some v => simpa using h v (List.mem_of_getElem? hi)

/-- Context IDs for literals are in 0..63 (§7.1). -/
theorem contextId_lt (mode : Nat) {p1 : Nat} (p2 : Nat) (h1 : p1 < 256) :
    contextId mode p1 p2 < 64 := by
  have l0 := getD_lt (l := Lut0) (n := 64) (by decide) (by decide +kernel)
  have l1 := getD_lt (l := Lut1) (n := 64) (by decide) (by decide +kernel)
  have l2 := getD_lt (l := Lut2) (n := 8) (by decide) (by decide +kernel)
  unfold contextId
  split
  · exact Nat.and_lt_two_pow (n := 6) p1 (by decide)
  · rw [Nat.shiftRight_eq_div_pow]
    omega
  · exact Nat.or_lt_two_pow (n := 6) (l0 p1) (l1 p2)
  · refine Nat.or_lt_two_pow (n := 6) ?_ ?_
    · have := l2 p1
      rw [Nat.shiftLeft_eq]
      omega
    · have := l2 p2
      omega

/-- The context modes of `n` literal block types, two bits each (§7.1). -/
def readContextModes : Nat → List Bool → Option (List Nat × List Bool)
  | 0, bs => some ([], bs)
  | n + 1, bs => do
    let (mode, bs) ← readInt 2 bs
    let (modes, bs) ← readContextModes n bs
    some (mode :: modes, bs)

/-- Every context mode is one of the integers 0, 1, 2, 3. -/
theorem readContextModes_lt : ∀ (n : Nat) (bs : List Bool) (modes : List Nat) (r : List Bool),
    readContextModes n bs = some (modes, r) → ∀ m ∈ modes, m < 4
  | 0, _, modes, _, h, m, hm => by
    simp only [readContextModes, Option.some.injEq, Prod.mk.injEq] at h
    rw [← h.1] at hm
    simp at hm
  | n + 1, bs, modes, r, h, m, hm => by
    simp only [readContextModes] at h
    cases h1 : readInt 2 bs with
    | none => rw [h1] at h; simp at h
    | some p =>
      obtain ⟨v, bs1⟩ := p
      rw [h1] at h
      dsimp only [bind, Option.bind] at h
      cases h2 : readContextModes n bs1 with
      | none => rw [h2] at h; simp at h
      | some q =>
        obtain ⟨ms, bs2⟩ := q
        rw [h2] at h
        simp only [Option.some.injEq, Prod.mk.injEq] at h
        rw [← h.1] at hm
        rcases List.mem_cons.mp hm with rfl | hm
        · exact readInt_lt 2 bs m bs1 h1
        · exact readContextModes_lt n bs1 ms bs2 h2 m hm

/-- The Context ID of a distance code, from the copy length (§7.2). -/
def distanceContextId : Nat → Nat
  | 2 => 0
  | 3 => 1
  | 4 => 2
  | _ => 3

/-- Context IDs for distances are in 0..3. -/
theorem distanceContextId_lt (l : Nat) : distanceContextId l < 4 := by
  unfold distanceContextId
  split <;> omega

/-- The size of the literal context map (§7.3). -/
def literalContextMapSize (nbltypesL : Nat) : Nat := 64 * nbltypesL

/-- The size of the distance context map (§7.3). -/
def distanceContextMapSize (nbltypesD : Nat) : Nat := 4 * nbltypesD

/-- The index of the literal prefix code, from the literal context map (§7.3). -/
def literalPrefixCodeIndex (cmap : List Nat) (btype cid : Nat) : Option Nat :=
  cmap[64 * btype + cid]?

/-- The index of the distance prefix code, from the distance context map (§7.3). -/
def distancePrefixCodeIndex (cmap : List Nat) (btype cid : Nat) : Option Nat :=
  cmap[4 * btype + cid]?

/-- The position of a literal's block type and context ID is inside the literal context map. -/
theorem literalIndex_lt {n btype cid : Nat} (hb : btype < n) (hc : cid < 64) :
    64 * btype + cid < literalContextMapSize n := by
  unfold literalContextMapSize
  omega

/-- The position of a distance's block type and context ID is inside the distance context map. -/
theorem distanceIndex_lt {n btype cid : Nat} (hb : btype < n) (hc : cid < 4) :
    4 * btype + cid < distanceContextMapSize n := by
  unfold distanceContextMapSize
  omega

/-- The alphabet size of a context map's prefix code (§7.3). -/
def contextMapAlphabetSize (ntrees rlemax : Nat) : Nat := ntrees + rlemax

/-- The value a symbol stands for, or `none` if it is a run length code (§7.3). -/
def contextMapValue (rlemax sym : Nat) : Option Nat :=
  if sym = 0 then some 0
  else if sym ≤ rlemax then none
  else some (sym - rlemax)

/-- With RLEMAX 0, the symbols are directly the values (§7.3). -/
theorem contextMapValue_rlemax_zero (sym : Nat) : contextMapValue 0 sym = some sym := by
  unfold contextMapValue
  split <;> simp_all

/-- The loop of `readContextMapValues`, with `out` the out-of-fuel result. -/
def readContextMapValuesWith (rlemax : Nat) (code : PrefixCode)
    (out : Option (List Nat × List Bool)) :
    Nat → Nat → List Bool → Option (List Nat × List Bool)
  | 0, _, _ => out
  | fuel + 1, left, bs =>
    if left = 0 then some ([], bs)
    else do
      let (sym, bs) ← decodeSymbol code bs
      match contextMapValue rlemax sym with
      | some v =>
        let (vals, bs) ← readContextMapValuesWith rlemax code out fuel (left - 1) bs
        some (v :: vals, bs)
      | none =>
        let (extra, bs) ← readInt sym bs
        let run := (1 <<< sym) + extra
        if left < run then none
        else
          let (vals, bs) ← readContextMapValuesWith rlemax code out fuel (left - run) bs
          some (List.replicate run 0 ++ vals, bs)

/-- The `left` values still to read of a context map; a run past the map's size is invalid (§7.3). Fuel:
`left + 1` (`readContextMapValues_out`). -/
def readContextMapValues (rlemax : Nat) (code : PrefixCode) :
    Nat → Nat → List Bool → Option (List Nat × List Bool) :=
  readContextMapValuesWith rlemax code none

/-- While the fuel exceeds `left`, the out-of-fuel result is never reached. -/
theorem readContextMapValuesWith_out (rlemax : Nat) (code : PrefixCode) : ∀ (fuel left : Nat)
    (bs : List Bool), left < fuel → ∀ out out',
    readContextMapValuesWith rlemax code out fuel left bs =
      readContextMapValuesWith rlemax code out' fuel left bs
  | 0, _, _, h, _, _ => by omega
  | f + 1, left, bs, h, out, out' => by
    simp only [readContextMapValuesWith]
    split
    · rfl
    rename_i hleft
    cases hd : decodeSymbol code bs with
    | none => rfl
    | some p =>
      obtain ⟨sym, bs1⟩ := p
      dsimp only [bind, Option.bind]
      split
      · rw [readContextMapValuesWith_out rlemax code f (left - 1) bs1 (by omega) out out']
      · cases hx : readInt sym bs1 with
        | none => rfl
        | some q =>
          obtain ⟨e, bs2⟩ := q
          dsimp only
          split
          · rfl
          · have hpos : 0 < 1 <<< sym := by
              rw [Nat.shiftLeft_eq, Nat.one_mul]
              exact Nat.two_pow_pos _
            rw [readContextMapValuesWith_out rlemax code f (left - ((1 <<< sym) + e)) bs2
              (by omega) out out']

/-- At the fuel `size + 1`, `readContextMapValues` never reaches its out-of-fuel result. -/
theorem readContextMapValues_out (rlemax : Nat) (code : PrefixCode) (size : Nat) (bs : List Bool)
    (out : Option (List Nat × List Bool)) :
    readContextMapValues rlemax code (size + 1) size bs =
      readContextMapValuesWith rlemax code out (size + 1) size bs :=
  readContextMapValuesWith_out rlemax code (size + 1) size bs (by omega) none out

/-- `readContextMapValues` returns exactly `left` values. -/
theorem readContextMapValues_length (rlemax : Nat) (code : PrefixCode) : ∀ (fuel left : Nat)
    (bs : List Bool) (vals : List Nat) (r : List Bool),
    readContextMapValues rlemax code fuel left bs = some (vals, r) → vals.length = left
  | 0, _, _, _, _, h => by simp [readContextMapValues, readContextMapValuesWith] at h
  | f + 1, left, bs, vals, r, h => by
    simp only [readContextMapValues, readContextMapValuesWith] at h
    split at h
    · simp only [Option.some.injEq, Prod.mk.injEq] at h
      rw [← h.1]
      simp [*]
    rename_i hleft
    cases hd : decodeSymbol code bs with
    | none => rw [hd] at h; simp at h
    | some p =>
      obtain ⟨sym, bs1⟩ := p
      rw [hd] at h
      dsimp only [bind, Option.bind] at h
      split at h
      · cases hv : readContextMapValuesWith rlemax code none f (left - 1) bs1 with
        | none => rw [hv] at h; simp at h
        | some q =>
          obtain ⟨vs, bs2⟩ := q
          rw [hv] at h
          simp only [Option.some.injEq, Prod.mk.injEq] at h
          have := readContextMapValues_length rlemax code f (left - 1) bs1 vs bs2 hv
          rw [← h.1]
          simp only [List.length_cons]
          omega
      · cases hx : readInt sym bs1 with
        | none => rw [hx] at h; simp at h
        | some q =>
          obtain ⟨e, bs2⟩ := q
          rw [hx] at h
          dsimp only at h
          split at h
          · simp at h
          · rename_i hrun
            cases hv : readContextMapValuesWith rlemax code none f (left - ((1 <<< sym) + e)) bs2 with
            | none => rw [hv] at h; simp at h
            | some t =>
              obtain ⟨vs, bs3⟩ := t
              rw [hv] at h
              simp only [Option.some.injEq, Prod.mk.injEq] at h
              have := readContextMapValues_length rlemax code f _ bs2 vs bs3 hv
              rw [← h.1]
              simp only [List.length_append, List.length_replicate]
              omega

/-- The values `readContextMapValues` returns are below NTREES. -/
theorem readContextMapValues_lt {rlemax ntrees : Nat} {code : PrefixCode} (hn : 0 < ntrees)
    (hc : code.Symbols (contextMapAlphabetSize ntrees rlemax)) : ∀ (fuel left : Nat)
    (bs : List Bool) (vals : List Nat) (r : List Bool),
    readContextMapValues rlemax code fuel left bs = some (vals, r) → ∀ v ∈ vals, v < ntrees
  | 0, _, _, _, _, h, _, _ => by simp [readContextMapValues, readContextMapValuesWith] at h
  | f + 1, left, bs, vals, r, h, x, hx => by
    simp only [readContextMapValues, readContextMapValuesWith] at h
    split at h
    · simp only [Option.some.injEq, Prod.mk.injEq] at h
      rw [← h.1] at hx
      simp at hx
    cases hd : decodeSymbol code bs with
    | none => rw [hd] at h; simp at h
    | some p =>
      obtain ⟨sym, bs1⟩ := p
      rw [hd] at h
      dsimp only [bind, Option.bind] at h
      have hsym := decodeSymbol_lt hc hd
      unfold contextMapAlphabetSize at hsym
      split at h
      · rename_i v hval
        cases hv : readContextMapValuesWith rlemax code none f (left - 1) bs1 with
        | none => rw [hv] at h; simp at h
        | some q =>
          obtain ⟨vs, bs2⟩ := q
          rw [hv] at h
          simp only [Option.some.injEq, Prod.mk.injEq] at h
          rw [← h.1] at hx
          rcases List.mem_cons.mp hx with rfl | hx
          · unfold contextMapValue at hval
            split at hval
            · simp only [Option.some.injEq] at hval
              omega
            · split at hval
              · simp at hval
              · simp only [Option.some.injEq] at hval
                omega
          · exact readContextMapValues_lt hn hc f (left - 1) bs1 vs bs2 hv x hx
      · cases hr : readInt sym bs1 with
        | none => rw [hr] at h; simp at h
        | some q =>
          obtain ⟨e, bs2⟩ := q
          rw [hr] at h
          dsimp only at h
          split at h
          · simp at h
          · cases hv : readContextMapValuesWith rlemax code none f (left - ((1 <<< sym) + e)) bs2 with
            | none => rw [hv] at h; simp at h
            | some t =>
              obtain ⟨vs, bs3⟩ := t
              rw [hv] at h
              simp only [Option.some.injEq, Prod.mk.injEq] at h
              rw [← h.1] at hx
              rcases List.mem_append.mp hx with hx | hx
              · rw [(List.mem_replicate.mp hx).2]
                exact hn
              · exact readContextMapValues_lt hn hc f _ bs2 vs bs3 hv x hx

/-- RLEMAX (§7.3). -/
def readRLEMAX (bs : List Bool) : Option (Nat × List Bool) := do
  let (flag, bs) ← readInt 1 bs
  if flag = 0 then some (0, bs)
  else
    let (x, bs) ← readInt 4 bs
    some (x + 1, bs)

/-- RLEMAX is 0 to 16 (§7.3). -/
theorem readRLEMAX_range {bs r : List Bool} {v : Nat} (h : readRLEMAX bs = some (v, r)) : v ≤ 16 := by
  unfold readRLEMAX at h
  cases h1 : readInt 1 bs with
  | none => rw [h1] at h; simp at h
  | some p =>
    obtain ⟨flag, bs1⟩ := p
    rw [h1] at h
    dsimp only [bind, Option.bind] at h
    split at h
    · simp only [Option.some.injEq, Prod.mk.injEq] at h
      omega
    · cases h2 : readInt 4 bs1 with
      | none => rw [h2] at h; simp at h
      | some q =>
        obtain ⟨x, bs2⟩ := q
        rw [h2] at h
        simp only [Option.some.injEq, Prod.mk.injEq] at h
        have : x < 16 := by simpa using readInt_lt 4 bs1 x bs2 h2
        omega

/-- A run's count, `1 << k` plus `k` extra bits, is `1 << k` to `(1 << (k + 1)) - 1`. -/
theorem runLength_range {k extra : Nat} {bs r : List Bool} (h : readInt k bs = some (extra, r)) :
    1 <<< k ≤ (1 <<< k) + extra ∧ (1 <<< k) + extra ≤ (1 <<< (k + 1)) - 1 := by
  have hx := readInt_lt k bs extra r h
  simp only [Nat.shiftLeft_eq, Nat.one_mul, Nat.pow_succ]
  omega

/-- Run length code `k` repeats a zero `1 << k` to `(1 << (k + 1)) - 1` times, and a run past the map's size is
invalid (§7.3). -/
theorem readContextMapValues_run {rlemax k extra left fuel : Nat} {code : PrefixCode}
    {bs b1 b2 : List Bool} (h0 : left ≠ 0) (hd : decodeSymbol code bs = some (k, b1))
    (hv : contextMapValue rlemax k = none) (he : readInt k b1 = some (extra, b2)) :
    readContextMapValues rlemax code (fuel + 1) left bs =
      (if left < (1 <<< k) + extra then none
      else
        (readContextMapValues rlemax code fuel (left - ((1 <<< k) + extra)) b2).map fun x =>
          (List.replicate ((1 <<< k) + extra) 0 ++ x.1, x.2)) ∧
    1 <<< k ≤ (1 <<< k) + extra ∧ (1 <<< k) + extra ≤ (1 <<< (k + 1)) - 1 := by
  refine ⟨?_, runLength_range he⟩
  simp only [readContextMapValues, readContextMapValuesWith, h0, ↓reduceIte]
  rw [hd]
  dsimp only [bind, Option.bind]
  rw [hv]
  dsimp only
  rw [he]
  dsimp only
  split
  · rfl
  · cases readContextMapValuesWith rlemax code none fuel (left - ((1 <<< k) + extra)) b2 <;> rfl

/-- The loop of `inverseMoveToFront`: each index's value moves to the front. -/
def inverseMoveToFrontFrom : List Nat → List Nat → List Nat
  | _, [] => []
  | mtf, index :: v =>
    let value := mtf.getD index 0
    value :: inverseMoveToFrontFrom (value :: mtf.eraseIdx index) v

/-- The inverse move-to-front transform (§7.3). -/
def inverseMoveToFront (v : List Nat) : List Nat :=
  inverseMoveToFrontFrom (List.range 256) v

/-- The transform keeps the number of values. -/
theorem inverseMoveToFrontFrom_length : ∀ (v mtf : List Nat),
    (inverseMoveToFrontFrom mtf v).length = v.length
  | [], _ => rfl
  | i :: v, mtf => by
    simp [inverseMoveToFrontFrom, inverseMoveToFrontFrom_length v]

private theorem inverseMoveToFrontFrom_lt {n : Nat} : ∀ (v mtf : List Nat),
    (∀ x ∈ v, x < n) → (∀ i < n, mtf.getD i 0 < n) → ∀ x ∈ inverseMoveToFrontFrom mtf v, x < n
  | [], _, _, _, x, hx => by simp [inverseMoveToFrontFrom] at hx
  | index :: v, mtf, hv, hm, x, hx => by
    have hindex : index < n := hv index (List.mem_cons_self ..)
    have hvalue := hm index hindex
    simp only [inverseMoveToFrontFrom] at hx
    rcases List.mem_cons.mp hx with rfl | hx
    · exact hvalue
    · refine inverseMoveToFrontFrom_lt v _ (fun y hy => hv y (List.mem_cons_of_mem _ hy)) ?_ x hx
      intro i hi
      cases i with
      | zero => simpa using hvalue
      | succ j =>
        simp only [List.getD_cons_succ]
        rw [List.getD_eq_getElem?_getD, List.getElem?_eraseIdx]
        split
        · rw [← List.getD_eq_getElem?_getD]
          exact hm j (by omega)
        · rw [← List.getD_eq_getElem?_getD]
          exact hm (j + 1) hi

/-- The transform keeps values below `n` (§7.3). -/
theorem inverseMoveToFront_lt {n : Nat} {v : List Nat} (hv : ∀ x ∈ v, x < n) :
    ∀ x ∈ inverseMoveToFront v, x < n := by
  refine inverseMoveToFrontFrom_lt v _ hv ?_
  intro i hi
  by_cases h : i < 256
  · simpa [List.getD_eq_getElem?_getD, List.getElem?_range, h] using hi
  · have : (List.range 256).getD i 0 = 0 := by
      rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by simpa using h)]
      rfl
    omega

/-- A context map of `size` values: every value of [0..NTREES-1] must occur (§7.3). -/
def readContextMap (size ntrees : Nat) (bs : List Bool) : Option (List Nat × List Bool) := do
  let (rlemax, bs) ← readRLEMAX bs
  let (code, bs) ← readPrefixCode (contextMapAlphabetSize ntrees rlemax) bs
  let (vals, bs) ← readContextMapValues rlemax code (size + 1) size bs
  let (imtf, bs) ← readInt 1 bs
  let final := if imtf = 0 then vals else inverseMoveToFront vals
  if (List.range ntrees).all final.contains then some (final, bs) else none

/-- A context map has `size` values. -/
theorem readContextMap_length {size ntrees : Nat} {bs r : List Bool} {cmap : List Nat}
    (h : readContextMap size ntrees bs = some (cmap, r)) : cmap.length = size := by
  unfold readContextMap at h
  cases h1 : readRLEMAX bs with
  | none => rw [h1] at h; simp at h
  | some a =>
    obtain ⟨rlemax, bs1⟩ := a
    rw [h1] at h
    dsimp only [bind, Option.bind] at h
    cases h2 : readPrefixCode (contextMapAlphabetSize ntrees rlemax) bs1 with
    | none => rw [h2] at h; simp at h
    | some b =>
      obtain ⟨code, bs2⟩ := b
      rw [h2] at h
      dsimp only at h
      cases h3 : readContextMapValues rlemax code (size + 1) size bs2 with
      | none => rw [h3] at h; simp at h
      | some c =>
        obtain ⟨vals, bs3⟩ := c
        rw [h3] at h
        dsimp only at h
        have hlen := readContextMapValues_length rlemax code _ _ _ _ _ h3
        cases h4 : readInt 1 bs3 with
        | none => rw [h4] at h; simp at h
        | some d =>
          obtain ⟨imtf, bs4⟩ := d
          rw [h4] at h
          dsimp only at h
          generalize hf : (if imtf = 0 then vals else inverseMoveToFront vals) = final at h
          split at h
          · simp only [Option.some.injEq, Prod.mk.injEq] at h
            rw [← h.1, ← hf]
            split
            · exact hlen
            · rw [inverseMoveToFront, inverseMoveToFrontFrom_length, hlen]
          · simp at h

/-- Every value of a context map is below NTREES. -/
theorem readContextMap_lt {size ntrees : Nat} {bs r : List Bool} {cmap : List Nat}
    (hn : 0 < ntrees) (h : readContextMap size ntrees bs = some (cmap, r)) :
    ∀ v ∈ cmap, v < ntrees := by
  unfold readContextMap at h
  cases h1 : readRLEMAX bs with
  | none => rw [h1] at h; simp at h
  | some a =>
    obtain ⟨rlemax, bs1⟩ := a
    rw [h1] at h
    dsimp only [bind, Option.bind] at h
    cases h2 : readPrefixCode (contextMapAlphabetSize ntrees rlemax) bs1 with
    | none => rw [h2] at h; simp at h
    | some b =>
      obtain ⟨code, bs2⟩ := b
      rw [h2] at h
      dsimp only at h
      cases h3 : readContextMapValues rlemax code (size + 1) size bs2 with
      | none => rw [h3] at h; simp at h
      | some c =>
        obtain ⟨vals, bs3⟩ := c
        rw [h3] at h
        dsimp only at h
        have hlt := readContextMapValues_lt hn (readPrefixCode_symbols h2) _ _ _ _ _ h3
        cases h4 : readInt 1 bs3 with
        | none => rw [h4] at h; simp at h
        | some d =>
          obtain ⟨imtf, bs4⟩ := d
          rw [h4] at h
          dsimp only at h
          generalize hf : (if imtf = 0 then vals else inverseMoveToFront vals) = final at h
          split at h
          · simp only [Option.some.injEq, Prod.mk.injEq] at h
            rw [← h.1, ← hf]
            split
            · exact hlt
            · exact inverseMoveToFront_lt hlt
          · simp at h

/-- Every value below NTREES occurs in a context map. -/
theorem readContextMap_values {size ntrees : Nat} {bs r : List Bool} {cmap : List Nat}
    (h : readContextMap size ntrees bs = some (cmap, r)) : ∀ v < ntrees, v ∈ cmap := by
  unfold readContextMap at h
  cases h1 : readRLEMAX bs with
  | none => rw [h1] at h; simp at h
  | some a =>
    obtain ⟨rlemax, bs1⟩ := a
    rw [h1] at h
    dsimp only [bind, Option.bind] at h
    cases h2 : readPrefixCode (contextMapAlphabetSize ntrees rlemax) bs1 with
    | none => rw [h2] at h; simp at h
    | some b =>
      obtain ⟨code, bs2⟩ := b
      rw [h2] at h
      dsimp only at h
      cases h3 : readContextMapValues rlemax code (size + 1) size bs2 with
      | none => rw [h3] at h; simp at h
      | some c =>
        obtain ⟨vals, bs3⟩ := c
        rw [h3] at h
        dsimp only at h
        cases h4 : readInt 1 bs3 with
        | none => rw [h4] at h; simp at h
        | some d =>
          obtain ⟨imtf, bs4⟩ := d
          rw [h4] at h
          dsimp only at h
          generalize (if imtf = 0 then vals else inverseMoveToFront vals) = final at h
          split at h
          · rename_i hall
            simp only [Option.some.injEq, Prod.mk.injEq] at h
            rw [← h.1]
            intro v hv
            simpa using List.all_eq_true.mp hall v (List.mem_range.mpr hv)
          · simp at h

end Brotli.Spec
