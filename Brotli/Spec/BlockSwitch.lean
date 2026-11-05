module

public import Brotli.Spec.PrefixCode

@[expose] public section

/-!
# Encoding of block-switch commands

RFC 7932 §6. What concerns a whole meta-block is in `Stream`.
-/

namespace Brotli.Spec

/-- The block type a block type symbol gives, with `n` block types (§6). -/
def nextBlockType (n prev cur sym : Nat) : Nat :=
  if sym = 0 then prev
  else if sym = 1 then (if cur = n - 1 then 0 else cur + 1)
  else sym - 2

/-- The alphabet size of a block type code with `n` block types (§6). -/
def blockTypeAlphabetSize (n : Nat) : Nat := n + 2

/-- A symbol of the alphabet gives a block type below `n`, given block types below `n`. -/
theorem nextBlockType_lt {n prev cur sym : Nat} (hprev : prev < n) (hcur : cur < n)
    (hsym : sym < blockTypeAlphabetSize n) : nextBlockType n prev cur sym < n := by
  unfold nextBlockType
  unfold blockTypeAlphabetSize at hsym
  split
  · exact hprev
  · split
    · split <;> omega
    · omega

/-- Symbol `t + 2` gives block type `t`. -/
theorem nextBlockType_explicit (n prev cur t : Nat) : nextBlockType n prev cur (t + 2) = t := by
  unfold nextBlockType
  simp

/-- The previous and the current block type of a block category. -/
structure BlockTypes where
  prev : Nat
  cur : Nat
  deriving DecidableEq

/-- The initial block types: previous 1, current 0 (§6). -/
def initialBlockTypes : BlockTypes :=
  ⟨1, 0⟩

/-- The block types after a block type symbol (§6). -/
def switchBlockType (n : Nat) (bt : BlockTypes) (sym : Nat) : BlockTypes :=
  ⟨bt.cur, nextBlockType n bt.prev bt.cur sym⟩

private theorem foldl_switchBlockType_lt {n : Nat} : ∀ (syms : List Nat) (bt : BlockTypes),
    bt.prev < n → bt.cur < n → (∀ s ∈ syms, s < blockTypeAlphabetSize n) →
    (syms.foldl (switchBlockType n) bt).prev < n ∧ (syms.foldl (switchBlockType n) bt).cur < n
  | [], _, hp, hc, _ => ⟨hp, hc⟩
  | s :: syms, bt, hp, hc, hs =>
    foldl_switchBlockType_lt syms (switchBlockType n bt s) hc
      (nextBlockType_lt hp hc (hs s (List.mem_cons_self ..)))
      (fun t ht => hs t (List.mem_cons_of_mem _ ht))

/-- With `n ≥ 2` block types, block switches keep the block types below `n`. -/
theorem blockTypes_lt {n : Nat} (hn : 2 ≤ n) (syms : List Nat)
    (hs : ∀ s ∈ syms, s < blockTypeAlphabetSize n) :
    (syms.foldl (switchBlockType n) initialBlockTypes).prev < n ∧
      (syms.foldl (switchBlockType n) initialBlockTypes).cur < n :=
  foldl_switchBlockType_lt syms initialBlockTypes (by simp [initialBlockTypes]; omega)
    (by simp [initialBlockTypes]; omega) hs

/-- A block type code (§6); giving the current block type is invalid (§2). -/
def readBlockType (n : Nat) (code : PrefixCode) (bt : BlockTypes) (bs : List Bool) :
    Option (BlockTypes × List Bool) := do
  let (sym, bs) ← decodeSymbol code bs
  let next := switchBlockType n bt sym
  if next.cur = bt.cur then none else some (next, bs)

/-- Consecutive blocks of a category have different block types (§2). -/
theorem readBlockType_differs {n : Nat} {code : PrefixCode} {bt next : BlockTypes} {bs r : List Bool}
    (h : readBlockType n code bt bs = some (next, r)) : next.cur ≠ bt.cur := by
  unfold readBlockType at h
  cases hd : decodeSymbol code bs with
  | none => rw [hd] at h; simp at h
  | some p =>
    obtain ⟨sym, bs1⟩ := p
    rw [hd] at h
    dsimp only [bind, Option.bind] at h
    split at h
    · simp at h
    · rename_i hne
      simp only [Option.some.injEq, Prod.mk.injEq] at h
      rw [← h.1]
      exact hne

/-- The block count code alphabet's size (§3.3). -/
def blockCountAlphabetSize : Nat := 26

/-- Block count codes 0 to 25: extra bits, lowest count, highest count (§6). -/
def blockCountCodes : List (Nat × Nat × Nat) :=
  [(2, 1, 4), (2, 5, 8), (2, 9, 12), (2, 13, 16), (3, 17, 24), (3, 25, 32), (3, 33, 40),
    (3, 41, 48), (4, 49, 64), (4, 65, 80), (4, 81, 96), (4, 97, 112), (5, 113, 144),
    (5, 145, 176), (5, 177, 208), (5, 209, 240), (6, 241, 304), (6, 305, 368), (7, 369, 496),
    (8, 497, 752), (9, 753, 1264), (10, 1265, 2288), (11, 2289, 4336), (12, 4337, 8432),
    (13, 8433, 16624), (24, 16625, 16793840)]

/-- The table has a row for each symbol of the block count code alphabet. -/
theorem blockCountCodes_length : blockCountCodes.length = blockCountAlphabetSize := by
  decide +kernel

/-- In each row the highest block count is the lowest plus `2 ^ bits - 1`. -/
theorem blockCountCodes_ranges : ∀ r ∈ blockCountCodes, r.2.2 = r.2.1 + 2 ^ r.1 - 1 := by
  decide +kernel

/-- Every block count code has 2 to 24 extra bits, and both ends occur (§6). -/
theorem blockCountCodes_extraBits :
    (∀ r ∈ blockCountCodes, 2 ≤ r.1 ∧ r.1 ≤ 24) ∧ (∃ r ∈ blockCountCodes, r.1 = 2) ∧
      (∃ r ∈ blockCountCodes, r.1 = 24) := by
  decide +kernel

/-- The largest block count is 16793840. -/
theorem blockCountCodes_largest :
    (∀ r ∈ blockCountCodes, r.2.2 ≤ 16793840) ∧ (∃ r ∈ blockCountCodes, r.2.2 = 16793840) := by
  decide +kernel

/-- A block count code and its extra bits (§6). -/
def readBlockCount (code : PrefixCode) (bs : List Bool) : Option (Nat × List Bool) := do
  let (c, bs) ← decodeSymbol code bs
  let (bits, lowest, _) ← blockCountCodes[c]?
  let (extra, bs) ← readInt bits bs
  some (lowest + extra, bs)

end Brotli.Spec
