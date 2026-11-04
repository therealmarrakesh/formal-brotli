import Brotli.Decoder.Hit

/-!
# Table slots

A table is a run of slots in one byte array. A slot takes 2 bytes, one 16-bit number: a bit count in its low 4 bits and
a 12-bit value above them, so that a read is one 16-bit load. `slotAt` is what a slot holds, and these lemmas say how
writes change it.
-/

namespace Brotli.Decoder

/-- Slot `i`'s 16-bit number. -/
def slotNum (t : ByteArray) (i : Nat) : Nat :=
  (t.data[2 * i]?.getD 0).toNat + 256 * (t.data[2 * i + 1]?.getD 0).toNat

/-- What slot `i` holds: its bit count and value. -/
def slotAt (t : ByteArray) (i : Nat) : Nat × Nat := (slotNum t i % 16, slotNum t i / 16)

/-- Writes one slot. -/
@[inline] def writeSlot (t : ByteArray) (i bits val : Nat) : ByteArray :=
  (t.set! (2 * i) ((bits + 16 * val) % 256).toUInt8).set! (2 * i + 1) ((bits + 16 * val) / 256).toUInt8

private theorem data_set (t : ByteArray) (i : Nat) (v : UInt8) : (t.set! i v).data = t.data.setIfInBounds i v := by
  cases t
  rfl

theorem size_writeSlot (t : ByteArray) (i bits val : Nat) : (writeSlot t i bits val).size = t.size := by
  have h : ∀ (t : ByteArray) (i : Nat) (v : UInt8), (t.set! i v).size = t.size := by
    intro t i v
    show (t.set! i v).data.size = t.data.size
    rw [data_set]
    simp
  simp only [writeSlot, h]

/-- A slot in the array holds what was written. -/
theorem slotAt_writeSlot_same {t : ByteArray} {i bits val : Nat} (hi : 2 * i + 1 < t.size) (hb : bits < 16)
    (hv : val < 4096) : slotAt (writeSlot t i bits val) i = (bits, val) := by
  have hsz : t.size = t.data.size := rfl
  have hlt : (bits + 16 * val) / 256 < 256 := by omega
  simp only [slotAt, slotNum, writeSlot, data_set]
  simp [Array.getElem?_setIfInBounds, Array.size_setIfInBounds, ← hsz]
  have h0 : 2 * i < t.size := by omega
  simp only [h0, hi, ↓reduceIte, Option.getD_some, UInt8.toNat_ofNat']
  constructor <;> omega

/-- Writing a slot leaves the others alone. -/
theorem slotAt_writeSlot_ne {t : ByteArray} {i j bits val : Nat} (h : j ≠ i) :
    slotAt (writeSlot t i bits val) j = slotAt t j := by
  simp only [slotAt, slotNum, writeSlot, data_set]
  have h1 : 2 * i ≠ 2 * j := by omega
  have h2 : 2 * i + 1 ≠ 2 * j := by omega
  have h3 : 2 * i ≠ 2 * j + 1 := by omega
  simp [h1, h2, h3]

end Brotli.Decoder
