import Brotli.Decoder.Hit

/-!
# Table slots

A table is a run of slots in one byte array. A slot takes 4 bytes: a bit count, then a 16-bit value, then a spare
byte, so that a read is one 32-bit load. `slotAt` is what a slot holds, and these lemmas say how writes change it.
-/

namespace Brotli.Decoder

/-- What slot `i` holds: its bit count and value. -/
def slotAt (t : ByteArray) (i : Nat) : Nat × Nat :=
  ((t.data[4 * i]?.getD 0).toNat, (t.data[4 * i + 1]?.getD 0).toNat + 256 * (t.data[4 * i + 2]?.getD 0).toNat)

/-- Writes one slot. -/
@[inline] def writeSlot (t : ByteArray) (i bits val : Nat) : ByteArray :=
  ((t.set! (4 * i) bits.toUInt8).set! (4 * i + 1) (val % 256).toUInt8).set! (4 * i + 2) (val / 256).toUInt8

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
theorem slotAt_writeSlot_same {t : ByteArray} {i bits val : Nat} (hi : 4 * i + 2 < t.size) (hb : bits < 256)
    (hv : val < 65536) : slotAt (writeSlot t i bits val) i = (bits, val) := by
  have hsz : t.size = t.data.size := rfl
  have hval : (val / 256) < 256 := by omega
  simp only [slotAt, writeSlot, data_set]
  simp [Array.getElem?_setIfInBounds, Array.size_setIfInBounds, ← hsz]
  have h0 : 4 * i < t.size := by omega
  have h1 : 4 * i + 1 < t.size := by omega
  simp only [h0, h1, hi, ↓reduceIte, Option.getD_some, UInt8.toNat_ofNat']
  omega

/-- Writing a slot leaves the others alone. -/
theorem slotAt_writeSlot_ne {t : ByteArray} {i j bits val : Nat} (h : j ≠ i) :
    slotAt (writeSlot t i bits val) j = slotAt t j := by
  simp only [slotAt, writeSlot, data_set]
  have h1 : 4 * i ≠ 4 * j := by omega
  have h2 : 4 * i + 1 ≠ 4 * j := by omega
  have h3 : 4 * i + 2 ≠ 4 * j := by omega
  have h4 : 4 * i ≠ 4 * j + 1 := by omega
  have h5 : 4 * i + 1 ≠ 4 * j + 1 := by omega
  have h6 : 4 * i + 2 ≠ 4 * j + 1 := by omega
  have h7 : 4 * i ≠ 4 * j + 2 := by omega
  have h8 : 4 * i + 1 ≠ 4 * j + 2 := by omega
  have h9 : 4 * i + 2 ≠ 4 * j + 2 := by omega
  simp [h1, h2, h3, h4, h6, h7]

end Brotli.Decoder
