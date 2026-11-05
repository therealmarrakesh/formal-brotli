module

public import Brotli.Spec.PrefixCode

@[expose] public section

/-!
# Encoding of literal insertion lengths and copy lengths

RFC 7932 §5.
-/

namespace Brotli.Spec

/-- The insert-and-copy length code alphabet's size (§3.3). -/
def insertCopyAlphabetSize : Nat := 704

/-- Insert length codes 0 to 23: extra bits, lowest length, highest length (§5). -/
def insertLengthCodes : List (Nat × Nat × Nat) :=
  [(0, 0, 0), (0, 1, 1), (0, 2, 2), (0, 3, 3), (0, 4, 4), (0, 5, 5), (1, 6, 7), (1, 8, 9),
    (2, 10, 13), (2, 14, 17), (3, 18, 25), (3, 26, 33), (4, 34, 49), (4, 50, 65), (5, 66, 97),
    (5, 98, 129), (6, 130, 193), (7, 194, 321), (8, 322, 577), (9, 578, 1089), (10, 1090, 2113),
    (12, 2114, 6209), (14, 6210, 22593), (24, 22594, 16799809)]

/-- Copy length codes 0 to 23: extra bits, lowest length, highest length (§5). -/
def copyLengthCodes : List (Nat × Nat × Nat) :=
  [(0, 2, 2), (0, 3, 3), (0, 4, 4), (0, 5, 5), (0, 6, 6), (0, 7, 7), (0, 8, 8), (0, 9, 9),
    (1, 10, 11), (1, 12, 13), (2, 14, 17), (2, 18, 21), (3, 22, 29), (3, 30, 37), (4, 38, 53),
    (4, 54, 69), (5, 70, 101), (5, 102, 133), (6, 134, 197), (7, 198, 325), (8, 326, 581),
    (9, 582, 1093), (10, 1094, 2117), (24, 2118, 16779333)]

/-- In each row the highest length is the lowest plus `2 ^ bits - 1`. -/
theorem lengthCodes_ranges :
    (∀ r ∈ insertLengthCodes, r.2.2 = r.2.1 + 2 ^ r.1 - 1) ∧
    (∀ r ∈ copyLengthCodes, r.2.2 = r.2.1 + 2 ^ r.1 - 1) := by
  decide +kernel

/-- The lowest copy length is 2 (§2). -/
theorem copyLengthCodes_min :
    (∀ r ∈ copyLengthCodes, 2 ≤ r.2.1) ∧ ∃ r ∈ copyLengthCodes, r.2.1 = 2 := by
  decide +kernel

/-- Every code has 0 to 24 extra bits, and both ends occur (§5). -/
theorem lengthCodes_extraBits :
    (∀ r ∈ insertLengthCodes, r.1 ≤ 24) ∧ (∀ r ∈ copyLengthCodes, r.1 ≤ 24) ∧
    (∃ r ∈ insertLengthCodes, r.1 = 0) ∧ (∃ r ∈ insertLengthCodes, r.1 = 24) ∧
    (∃ r ∈ copyLengthCodes, r.1 = 0) ∧ (∃ r ∈ copyLengthCodes, r.1 = 24) := by
  decide +kernel

/-- The cells of the insert-and-copy table: lowest and highest code, first insert length code, first
copy length code (§5). -/
def insertCopyCells : List (Nat × Nat × Nat × Nat) :=
  [(0, 63, 0, 0), (64, 127, 0, 8),
    (128, 191, 0, 0), (192, 255, 0, 8), (384, 447, 0, 16),
    (256, 319, 8, 0), (320, 383, 8, 8), (512, 575, 8, 16),
    (448, 511, 16, 0), (576, 639, 16, 8), (640, 703, 16, 16)]

/-- Every code of the alphabet lies in exactly one cell of 64 codes. -/
theorem insertCopyCells_partition :
    (∀ cell ∈ insertCopyCells, cell.2.1 = cell.1 + 63 ∧ cell.2.1 < insertCopyAlphabetSize) ∧
    ∀ c < insertCopyAlphabetSize,
      (insertCopyCells.filter fun cell => cell.1 ≤ c && c ≤ cell.2.1).length = 1 := by
  decide +kernel

/-- The insert length code and copy length code of the insert-and-copy length code `c` (§5). -/
def insertCopyCodes (c : Nat) : Option (Nat × Nat) :=
  match insertCopyCells.find? fun cell => cell.1 ≤ c && c ≤ cell.2.1 with
  | some (_, _, insertBase, copyBase) => some (insertBase + ((c >>> 3) &&& 7), copyBase + (c &&& 7))
  | none => none

/-- Whether the code implies distance symbol 0 (§5). -/
def implicitZeroDistance (c : Nat) : Bool :=
  c < 128

/-- An insert-and-copy length code and its extra bits (§5). Returns the code, the insertion length and
the copy length. -/
def readInsertCopy (code : PrefixCode) (bs : List Bool) : Option ((Nat × Nat × Nat) × List Bool) := do
  let (c, bs) ← decodeSymbol code bs
  let (insertCode, copyCode) ← insertCopyCodes c
  let (insertBits, insertBase, _) ← insertLengthCodes[insertCode]?
  let (copyBits, copyBase, _) ← copyLengthCodes[copyCode]?
  let (insertExtra, bs) ← readInt insertBits bs
  let (copyExtra, bs) ← readInt copyBits bs
  some ((c, insertBase + insertExtra, copyBase + copyExtra), bs)

/-- Every copy length `readInsertCopy` returns is at least 2. -/
theorem readInsertCopy_copy_ge_two {code : PrefixCode} {bs r : List Bool} {c i l : Nat}
    (h : readInsertCopy code bs = some ((c, i, l), r)) : 2 ≤ l := by
  unfold readInsertCopy at h
  cases h1 : decodeSymbol code bs with
  | none => rw [h1] at h; simp at h
  | some p =>
    obtain ⟨c', bs1⟩ := p
    rw [h1] at h
    dsimp only [bind, Option.bind] at h
    cases h2 : insertCopyCodes c' with
    | none => rw [h2] at h; simp at h
    | some q =>
      obtain ⟨ic, cc⟩ := q
      rw [h2] at h
      dsimp only at h
      cases h3 : insertLengthCodes[ic]? with
      | none => rw [h3] at h; simp at h
      | some t =>
        obtain ⟨ib, ibase, ihi⟩ := t
        rw [h3] at h
        dsimp only at h
        cases h4 : copyLengthCodes[cc]? with
        | none => rw [h4] at h; simp at h
        | some u =>
          obtain ⟨cb, cbase, chi⟩ := u
          rw [h4] at h
          dsimp only at h
          have hmin := copyLengthCodes_min.1 _ (List.mem_of_getElem? h4)
          cases h5 : readInt ib bs1 with
          | none => rw [h5] at h; simp at h
          | some v =>
            obtain ⟨ie, bs2⟩ := v
            rw [h5] at h
            dsimp only at h
            cases h6 : readInt cb bs2 with
            | none => rw [h6] at h; simp at h
            | some w =>
              obtain ⟨ce, bs3⟩ := w
              rw [h6] at h
              simp only [Option.some.injEq, Prod.mk.injEq] at h
              simp only at hmin
              omega

end Brotli.Spec
