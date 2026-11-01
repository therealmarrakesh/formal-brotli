import Brotli.Decoder.Lookup
import Brotli.Properties.Lookups

/-!
# The command lookup

An insert-and-copy symbol's extra bits and lowest lengths come from one table, two slots per symbol, instead of
searching the spec's tables for each command. `cmdRow_spec` proves the table is the spec's.
-/

namespace Brotli.Decoder

open Brotli.Spec Brotli.Properties

/-- A symbol's insert extra bits, lowest insert length, copy extra bits and lowest copy length. -/
def cmdRow (c : Nat) : Nat × Nat × Nat × Nat :=
  match insertCopyCodes c with
  | none => (0, 0, 0, 0)
  | some (ic, cc) =>
    let i := insertLengthCodes.getD ic (0, 0, 0)
    let l := copyLengthCodes.getD cc (0, 0, 0)
    (i.1, i.2.1, l.1, l.2.1)

/-- Slot `i` of the table: symbol `i / 2`'s insert fields in the even slot, and its copy fields in the odd one. -/
def cmdEntry (i : Nat) : Nat :=
  let r := cmdRow (i / 2)
  if i % 2 = 0 then r.1 + 256 * r.2.1 else r.2.2.1 + 256 * r.2.2.2

/-- Byte `j` of the table, the first of a slot the least significant. -/
def cmdByte (j : Nat) : Nat :=
  (cmdEntry (j / 4) >>> (8 * (j % 4))) &&& 255

/-- The command lookup table. -/
def cmdLut : ByteArray :=
  ((List.range 5632).map fun j => (cmdByte j).toUInt8).toByteArray

theorem cmdLut_size : cmdLut.size = 5632 := by
  simp [cmdLut, List.size_toByteArray]

private theorem cmdLut_size32 : cmdLut.size < 2 ^ 32 := by
  rw [cmdLut_size]
  decide

private theorem cmdByte_lt (j : Nat) : cmdByte j < 256 :=
  Nat.lt_of_le_of_lt Nat.and_le_right (by decide)

private theorem cmdLut_byte {j : Nat} (h : j < 5632) : (cmdLut.data[j]?.getD 0).toNat = cmdByte j := by
  have hb := cmdByte_lt j
  simp only [cmdLut, List.data_toByteArray]
  simp [h]
  omega

private theorem slots_whole : ∀ i, i < 1408 →
    cmdByte (4 * i) + 256 * cmdByte (4 * i + 1) + 65536 * cmdByte (4 * i + 2) + 16777216 * cmdByte (4 * i + 3) =
      cmdEntry i := by
  decide +kernel

private theorem cmdLut_slot {i : Nat} (h : i < 1408) : u32At cmdLut i = cmdEntry i := by
  unfold u32At
  rw [cmdLut_byte (by omega), cmdLut_byte (by omega), cmdLut_byte (by omega), cmdLut_byte (by omega)]
  exact slots_whole i h

private theorem rows_small : ∀ c, c < 704 →
    (cmdRow c).1 ≤ 24 ∧ (cmdRow c).2.1 ≤ 22594 ∧ (cmdRow c).2.2.1 ≤ 24 ∧ (cmdRow c).2.2.2 ≤ 2118 := by
  decide +kernel

/-- What a row holds, in the spec's tables. -/
theorem cmdRow_spec {c : Nat} (hc : c < 704) :
    ∃ ic cc ih ch, insertCopyCodes c = some (ic, cc) ∧
      insertLengthCodes[ic]? = some ((cmdRow c).1, (cmdRow c).2.1, ih) ∧
      copyLengthCodes[cc]? = some ((cmdRow c).2.2.1, (cmdRow c).2.2.2, ch) := by
  obtain ⟨ic, cc, ⟨i0, i1, i2⟩, ⟨l0, l1, l2⟩, h1, h2, h3⟩ := insertCopy_tables hc
  refine ⟨ic, cc, i2, l2, h1, ?_, ?_⟩
  · unfold cmdRow
    rw [h1]
    simp [List.getD_eq_getElem?_getD, h2]
  · unfold cmdRow
    rw [h1]
    simp [List.getD_eq_getElem?_getD, h3]

/-- The bounds of a row. -/
theorem cmdRow_small {c : Nat} (hc : c < 704) :
    (cmdRow c).1 ≤ 24 ∧ (cmdRow c).2.1 ≤ 22594 ∧ (cmdRow c).2.2.1 ≤ 24 ∧ (cmdRow c).2.2.2 ≤ 2118 :=
  rows_small c hc

private theorem u64_usize {c : UInt64} (h : c.toNat < 2 ^ 32) : c.toUSize.toNat = c.toNat :=
  word_toUSize h

private theorem slot_even {c : UInt64} (hc : c.toNat < 704) : (c + c).toUSize.toNat = 2 * c.toNat := by
  have h1 : (c + c).toNat = 2 * c.toNat := by
    rw [UInt64.toNat_add]
    exact (Nat.mod_eq_of_lt (by omega)).trans (by omega)
  rw [u64_usize (by omega), h1]

private theorem slot_odd {c : UInt64} (hc : c.toNat < 704) : (c + c + 1).toUSize.toNat = 2 * c.toNat + 1 := by
  have h1 : (c + c).toNat = 2 * c.toNat := by
    rw [UInt64.toNat_add]
    exact (Nat.mod_eq_of_lt (by omega)).trans (by omega)
  have h2 : (c + c + 1).toNat = 2 * c.toNat + 1 := by
    rw [UInt64.toNat_add, h1, show (1 : UInt64).toNat = 1 from rfl]
    exact Nat.mod_eq_of_lt (by omega)
  rw [u64_usize (by omega), h2]

theorem lt704 {c : UInt64} (h : c < 704) : c.toNat < 704 := by
  have := UInt64.lt_iff_toNat_lt.mp h
  rwa [show (704 : UInt64).toNat = 704 from rfl] at this

theorem lt26 {c : UInt64} (h : c < 26) : c.toNat < 26 := by
  have := UInt64.lt_iff_toNat_lt.mp h
  rwa [show (26 : UInt64).toNat = 26 from rfl] at this

/-- A symbol's insert slot. -/
@[inline] def insertRow (c : UInt64) (hc : c.toNat < 704) : UInt64 :=
  slotWord cmdLut (c + c).toUSize
    (by
      rw [slot_even hc, cmdLut_size]
      omega) cmdLut_size32

/-- A symbol's copy slot. -/
@[inline] def copyRow (c : UInt64) (hc : c.toNat < 704) : UInt64 :=
  slotWord cmdLut (c + c + 1).toUSize
    (by
      rw [slot_odd hc, cmdLut_size]
      omega) cmdLut_size32

/-- A slot's extra bits. -/
@[inline] def rowBits (row : UInt64) : UInt64 := row &&& 255

/-- A slot's lowest length. -/
@[inline] def rowBase (row : UInt64) : UInt64 := row >>> 8

private theorem slot_fields {row : UInt64} {b l : Nat} (h : row.toNat = b + 256 * l) (hb : b < 256) :
    (rowBits row).toNat = b ∧ (rowBase row).toNat = l := by
  constructor
  · unfold rowBits
    rw [UInt64.toNat_and, show (255 : UInt64).toNat = 2 ^ 8 - 1 from rfl, Nat.and_two_pow_sub_one_eq_mod, h]
    omega
  · unfold rowBase
    rw [UInt64.toNat_shiftRight, show (8 : UInt64).toNat % 64 = 8 from rfl, Nat.shiftRight_eq_div_pow, h]
    show (b + 256 * l) / 256 = l
    omega

/-- What the insert slot holds. -/
theorem insertRow_fields {c : UInt64} (hc : c.toNat < 704) :
    (rowBits (insertRow c hc)).toNat = (cmdRow c.toNat).1 ∧ (rowBase (insertRow c hc)).toNat = (cmdRow c.toNat).2.1 := by
  have hs := cmdRow_small hc
  refine slot_fields ?_ (by omega)
  unfold insertRow
  rw [slotWord_toNat, slot_even hc, cmdLut_slot (by omega)]
  have h1 : 2 * c.toNat / 2 = c.toNat := by omega
  have h2 : 2 * c.toNat % 2 = 0 := by omega
  simp only [cmdEntry, h1, h2, ↓reduceIte]

/-- What the copy slot holds. -/
theorem copyRow_fields {c : UInt64} (hc : c.toNat < 704) :
    (rowBits (copyRow c hc)).toNat = (cmdRow c.toNat).2.2.1 ∧ (rowBase (copyRow c hc)).toNat = (cmdRow c.toNat).2.2.2 := by
  have hs := cmdRow_small hc
  refine slot_fields ?_ (by omega)
  unfold copyRow
  rw [slotWord_toNat, slot_odd hc, cmdLut_slot (by omega)]
  have h1 : (2 * c.toNat + 1) / 2 = c.toNat := by omega
  have h2 : (2 * c.toNat + 1) % 2 = 1 := by omega
  simp only [cmdEntry, h1, h2]
  rfl

/-! ### Block counts -/

/-- Slot `i` of the block count table: the extra bits, then the lowest count above them. -/
def countEntry (i : Nat) : Nat :=
  let r := blockCountCodes.getD i (0, 0, 0)
  r.1 + 256 * r.2.1

/-- Byte `j` of the block count table. -/
def countByte (j : Nat) : Nat :=
  (countEntry (j / 4) >>> (8 * (j % 4))) &&& 255

/-- The block count table. -/
def countLut : ByteArray :=
  ((List.range 104).map fun j => (countByte j).toUInt8).toByteArray

theorem countLut_size : countLut.size = 104 := by
  simp [countLut, List.size_toByteArray]

private theorem countLut_size32 : countLut.size < 2 ^ 32 := by
  rw [countLut_size]
  decide

private theorem countLut_byte {j : Nat} (h : j < 104) : (countLut.data[j]?.getD 0).toNat = countByte j := by
  have hb : countByte j < 256 := Nat.lt_of_le_of_lt Nat.and_le_right (by decide)
  simp only [countLut, List.data_toByteArray]
  simp [h]
  omega

private theorem count_whole : ∀ i, i < 26 →
    countByte (4 * i) + 256 * countByte (4 * i + 1) + 65536 * countByte (4 * i + 2) + 16777216 * countByte (4 * i + 3) =
      countEntry i := by
  decide +kernel

private theorem count_small : ∀ i, i < 26 → (blockCountCodes.getD i (0, 0, 0)).1 < 256 := by
  decide +kernel

/-- A block count symbol's slot. -/
@[inline] def countRow (c : UInt64) (hc : c.toNat < 26) : UInt64 :=
  slotWord countLut c.toUSize
    (by
      rw [u64_usize (by omega), countLut_size]
      omega) countLut_size32

/-- What a block count slot holds. -/
theorem countRow_fields {c : UInt64} (hc : c.toNat < 26) :
    (rowBits (countRow c hc)).toNat = (blockCountCodes.getD c.toNat (0, 0, 0)).1 ∧
      (rowBase (countRow c hc)).toNat = (blockCountCodes.getD c.toNat (0, 0, 0)).2.1 := by
  refine slot_fields ?_ (count_small _ hc)
  unfold countRow
  rw [slotWord_toNat, u64_usize (by omega)]
  unfold u32At
  rw [countLut_byte (by omega), countLut_byte (by omega), countLut_byte (by omega), countLut_byte (by omega)]
  exact count_whole _ hc

end Brotli.Decoder
