import Brotli.Decoder.Table
import Brotli.Decoder.BitBuffer

/-!
# Table lookup

The hot path of symbol decoding: one load for the root slot, and a second for a long code word. `lookup` returns a
slot as one word, the bit count in the low byte and the value above it, and is proved to agree with `decodeSymbol`.
The arena stays below `2 ^ 32` bytes, so its positions always fit a `USize`.
-/

namespace Brotli.Decoder

open Brotli.Spec Brotli.Properties

private theorem usize_toNat_add {a b : USize} (h : a.toNat + b.toNat < 2 ^ 32) : (a + b).toNat = a.toNat + b.toNat := by
  rw [USize.toNat_add]
  apply Nat.mod_eq_of_lt
  have := USize.le_size
  rw [USize.size_eq_two_pow] at this
  omega

private theorem usize_ofNat_toNat' {n : Nat} (h : n < 2 ^ 32) : (USize.ofNat n).toNat = n := by
  rw [USize.toNat_ofNat']
  apply Nat.mod_eq_of_lt
  have := USize.le_size
  rw [USize.size_eq_two_pow] at this
  omega

private theorem usize_shift2 {i : USize} (h : 4 * i.toNat < 2 ^ 32) : (i * USize.ofNat 4).toNat = 4 * i.toNat := by
  rw [USize.toNat_mul, usize_ofNat_toNat' (by decide)]
  rw [Nat.mul_comm]
  apply Nat.mod_eq_of_lt
  have := USize.le_size
  rw [USize.size_eq_two_pow] at this
  omega

private theorem toNat_toUSize {v : UInt64} (h : v.toNat < 2 ^ 32) : v.toUSize.toNat = v.toNat := by
  rw [UInt64.toNat_toUSize]
  apply Nat.mod_eq_of_lt
  have := USize.le_size
  rw [USize.size_eq_two_pow] at this
  omega

/-- Slot `i`'s 4 bytes as one word, the first the least significant. -/
@[inline] def slotWord (t : ByteArray) (i : USize) (h : 4 * i.toNat + 4 ≤ t.size) (h32 : t.size < 2 ^ 32) : UInt64 :=
  let p := i * USize.ofNat 4
  (t.uget p (by rw [usize_shift2 (by omega)]; omega)).toUInt64 |||
    ((t.uget (p + USize.ofNat 1) (by
        rw [usize_toNat_add (by rw [usize_shift2 (by omega), usize_ofNat_toNat' (by decide)]; omega),
          usize_shift2 (by omega), usize_ofNat_toNat' (by decide)]
        omega)).toUInt64 <<< 8) |||
    ((t.uget (p + USize.ofNat 2) (by
        rw [usize_toNat_add (by rw [usize_shift2 (by omega), usize_ofNat_toNat' (by decide)]; omega),
          usize_shift2 (by omega), usize_ofNat_toNat' (by decide)]
        omega)).toUInt64 <<< 16) |||
    ((t.uget (p + USize.ofNat 3) (by
        rw [usize_toNat_add (by rw [usize_shift2 (by omega), usize_ofNat_toNat' (by decide)]; omega),
          usize_shift2 (by omega), usize_ofNat_toNat' (by decide)]
        omega)).toUInt64 <<< 24)

private theorem uget_slot {a : ByteArray} {p : USize} {k : Nat} (hp : p.toNat = k) (h : p.toNat < a.size) :
    (a.uget p h).toNat = (a.data[k]?.getD 0).toNat := by
  subst hp
  cases a with
  | mk bs =>
    have h' : p.toNat < bs.size := h
    simp [ByteArray.uget, h']

private theorem byte_lt (x : UInt8) : x.toUInt64.toNat < 2 ^ 8 := by
  have := x.toNat_lt
  simpa using this

private theorem four_bytes (a b c d : UInt8) :
    (a.toUInt64 ||| (b.toUInt64 <<< 8) ||| (c.toUInt64 <<< 16) ||| (d.toUInt64 <<< 24)).toNat =
      a.toNat + 256 * b.toNat + 65536 * c.toNat + 16777216 * d.toNat := by
  have h8 : (8 : UInt64).toNat = 8 := rfl
  have h16 : (16 : UInt64).toNat = 16 := rfl
  have h24 : (24 : UInt64).toNat = 24 := rfl
  have e1 : (a.toUInt64 ||| (b.toUInt64 <<< 8)).toNat = a.toNat + 256 * b.toNat := by
    have := BitBuffer.add_word (word := a.toUInt64) (count := 8) (v := b.toUInt64) (n := 8) (by rw [h8]; omega)
      (by rw [h8]; omega) (by rw [h8]; exact byte_lt a) (byte_lt b)
    simpa [h8] using this
  have ha := a.toNat_lt
  have hb := b.toNat_lt
  have hc := c.toNat_lt
  have hd := d.toNat_lt
  have e2 : (a.toUInt64 ||| (b.toUInt64 <<< 8) ||| (c.toUInt64 <<< 16)).toNat =
      a.toNat + 256 * b.toNat + 65536 * c.toNat := by
    have := BitBuffer.add_word (word := a.toUInt64 ||| (b.toUInt64 <<< 8)) (count := 16) (v := c.toUInt64) (n := 8)
      (by rw [h16]; omega) (by rw [h16]; omega) (by rw [h16, e1]; omega) (byte_lt c)
    rw [e1] at this
    simpa [h16] using this
  have := BitBuffer.add_word (word := a.toUInt64 ||| (b.toUInt64 <<< 8) ||| (c.toUInt64 <<< 16)) (count := 24)
    (v := d.toUInt64) (n := 8) (by rw [h24]; omega) (by rw [h24]; omega) (by rw [h24, e2]; omega) (byte_lt d)
  rw [e2] at this
  simpa [h24] using this

/-- What a slot's word holds: its bit count in the low byte, and its value in the next two. -/
theorem slotWord_spec {t : ByteArray} {i : USize} (h : 4 * i.toNat + 4 ≤ t.size) (h32 : t.size < 2 ^ 32) :
    (slotWord t i h h32).toNat % 256 = (slotAt t i.toNat).1 ∧
      (slotWord t i h h32).toNat / 256 % 65536 = (slotAt t i.toNat).2 := by
  have hp : (i * USize.ofNat 4).toNat = 4 * i.toNat := usize_shift2 (by omega)
  have hk : ∀ k, k < 4 → (i * USize.ofNat 4 + USize.ofNat k).toNat = 4 * i.toNat + k := by
    intro k hk
    rw [usize_toNat_add (by rw [hp, usize_ofNat_toNat' (by omega)]; omega), hp, usize_ofNat_toNat' (by omega)]
  unfold slotWord
  dsimp only
  rw [four_bytes, uget_slot hp, uget_slot (hk 1 (by decide)), uget_slot (hk 2 (by decide))]
  simp only [slotAt]
  generalize t.uget _ _ = last
  have h0 := (t.data[4 * i.toNat]?.getD 0).toNat_lt
  have h1 := (t.data[4 * i.toNat + 1]?.getD 0).toNat_lt
  have h2 := (t.data[4 * i.toNat + 2]?.getD 0).toNat_lt
  omega

/-- A root slot's position. -/
@[inline] def rootIndex (base : USize) (w : UInt64) : USize :=
  base + (w &&& 255).toUSize

private theorem and_255 (v : UInt64) : (v &&& 255).toNat = v.toNat % 256 := by
  rw [UInt64.toNat_and]
  exact Nat.and_two_pow_sub_one_eq_mod v.toNat 8

theorem rootIndex_toNat {t : ByteArray} {base : USize} (w : UInt64) (hok : TableFits t base.toNat)
    (h32 : t.size < 2 ^ 32) : (rootIndex base w).toNat = base.toNat + w.toNat % 256 := by
  have hr := hok.root
  have hl : w.toNat % 256 < 256 := Nat.mod_lt _ (by decide)
  have hu : (w &&& 255).toUSize.toNat = w.toNat % 256 := by
    rw [toNat_toUSize (by rw [and_255]; omega), and_255]
  unfold rootIndex
  rw [usize_toNat_add (by rw [hu]; omega), hu]

theorem rootIndex_bound {t : ByteArray} {base : USize} (w : UInt64) (hok : TableFits t base.toNat)
    (h32 : t.size < 2 ^ 32) : 4 * (rootIndex base w).toNat + 4 ≤ t.size := by
  rw [rootIndex_toNat w hok h32]
  have hr := hok.root
  have hl : w.toNat % 256 < 256 := Nat.mod_lt _ (by decide)
  omega

/-- A sub-table slot's position, for a root slot's word `e`. -/
@[inline] def subIndex (base : USize) (w e : UInt64) : USize :=
  base + USize.ofNat 256 + ((e >>> 8) &&& 65535).toUSize + (BitBuffer.peek ⟨w >>> 8, 0⟩ ((e &&& 255) - 8)).toUSize

/-- Where a sub-table slot is, for a root slot with a bit count above 8. -/
theorem subIndex_spec {t : ByteArray} {base : USize} {w e : UInt64} (hok : TableFits t base.toNat)
    (h32 : t.size < 2 ^ 32) (he1 : e.toNat % 256 = (slotAt t (base.toNat + w.toNat % 256)).1)
    (he2 : e.toNat / 256 % 65536 = (slotAt t (base.toNat + w.toNat % 256)).2) (hbig : ¬ (e &&& 255) ≤ 8) :
    (subIndex base w e).toNat = base.toNat + 256 + (slotAt t (base.toNat + w.toNat % 256)).2 +
        (w.toNat / 256) % 2 ^ ((slotAt t (base.toNat + w.toNat % 256)).1 - 8) ∧
      4 * (subIndex base w e).toNat + 4 ≤ t.size := by
  have hr : w.toNat % 256 < 256 := Nat.mod_lt _ (by decide)
  have hb : 8 < (slotAt t (base.toNat + w.toNat % 256)).1 := by
    have : ¬ (e &&& 255).toNat ≤ (8 : UInt64).toNat := fun hl => hbig (UInt64.le_iff_toNat_le.mpr hl)
    rw [and_255, he1] at this
    have h8 : (8 : UInt64).toNat = 8 := rfl
    omega
  obtain ⟨h15, hsub⟩ := hok.sub _ hr hb
  generalize hE : slotAt t (base.toNat + w.toNat % 256) = E at *
  have hE1 : E.1 ≤ 15 := h15
  have hm : ((e &&& 255) - 8).toNat = E.1 - 8 := by
    rw [UInt64.toNat_sub_of_le _ _ (UInt64.le_iff_toNat_le.mpr (by rw [and_255, he1]; exact Nat.le_of_lt hb)), and_255, he1]
    rfl
  have hoff : ((e >>> 8) &&& 65535).toNat = E.2 := by
    rw [UInt64.toNat_and, show (65535 : UInt64).toNat = 2 ^ 16 - 1 from rfl, Nat.and_two_pow_sub_one_eq_mod,
      UInt64.toNat_shiftRight, Nat.shiftRight_eq_div_pow]
    exact he2
  have hshift : (w >>> 8).toNat = w.toNat / 256 := by
    rw [UInt64.toNat_shiftRight, Nat.shiftRight_eq_div_pow]
    rfl
  have hj : (BitBuffer.peek ⟨w >>> 8, 0⟩ ((e &&& 255) - 8)).toNat = (w.toNat / 256) % 2 ^ (E.1 - 8) := by
    rw [BitBuffer.peek_toNat _ (by rw [hm]; omega), hm]
    simp only
    rw [hshift]
  have hjlt : (w.toNat / 256) % 2 ^ (E.1 - 8) < 2 ^ (E.1 - 8) := Nat.mod_lt _ (Nat.two_pow_pos _)
  have hroot := hok.root
  have hoffU : ((e >>> 8) &&& 65535).toUSize.toNat = E.2 := by
    rw [toNat_toUSize (by rw [hoff]; omega), hoff]
  have hjU : (BitBuffer.peek ⟨w >>> 8, 0⟩ ((e &&& 255) - 8)).toUSize.toNat = (w.toNat / 256) % 2 ^ (E.1 - 8) := by
    rw [toNat_toUSize (by rw [hj]; omega), hj]
  have h256 : (USize.ofNat 256).toNat = 256 := usize_ofNat_toNat' (by decide)
  have hval : (subIndex base w e).toNat = base.toNat + 256 + E.2 + (w.toNat / 256) % 2 ^ (E.1 - 8) := by
    unfold subIndex
    rw [usize_toNat_add (by
        rw [usize_toNat_add (by rw [usize_toNat_add (by rw [h256]; omega), h256, hoffU]; omega), usize_toNat_add
          (by rw [h256]; omega), h256, hoffU, hjU]
        omega),
      usize_toNat_add (by rw [usize_toNat_add (by rw [h256]; omega), h256, hoffU]; omega),
      usize_toNat_add (by rw [h256]; omega), h256, hoffU, hjU]
  exact ⟨hval, by rw [hval]; omega⟩

/-- Looks up the next bits, giving the slot's word: its bit count in the low byte, and its value above. -/
@[inline] def lookup (t : ByteArray) (base : USize) (w : UInt64) (hok : TableFits t base.toNat)
    (h32 : t.size < 2 ^ 32) : UInt64 :=
  let e := slotWord t (rootIndex base w) (rootIndex_bound w hok h32) h32
  if hbig : e &&& 255 ≤ 8 then e
  else
    slotWord t (subIndex base w e)
      (subIndex_spec hok h32
        (by
          rw [← rootIndex_toNat w hok h32]
          exact (slotWord_spec _ h32).1)
        (by
          rw [← rootIndex_toNat w hok h32]
          exact (slotWord_spec _ h32).2)
        hbig).2 h32

/-- `lookup` reads the slot `lookupSlots` describes. -/
theorem lookup_spec {t : ByteArray} {base : USize} {w : UInt64} (hok : TableFits t base.toNat)
    (h32 : t.size < 2 ^ 32) :
    (lookup t base w hok h32).toNat % 256 = (lookupSlots t base.toNat w.toNat).1 ∧
      (lookup t base w hok h32).toNat / 256 % 65536 = (lookupSlots t base.toNat w.toNat).2 := by
  have hi := rootIndex_toNat w hok h32
  obtain ⟨e1, e2⟩ := slotWord_spec (rootIndex_bound w hok h32) h32
  rw [hi] at e1 e2
  unfold lookup lookupSlots
  dsimp only
  split
  · rename_i hle
    have hle' : (slotAt t (base.toNat + w.toNat % 256)).1 ≤ 8 := by
      have := UInt64.le_iff_toNat_le.mp hle
      rw [and_255, e1] at this
      exact this
    simp only [hle', ↓reduceIte]
    exact ⟨e1, e2⟩
  · rename_i hbig
    obtain ⟨s1, s2⟩ := subIndex_spec hok h32 e1 e2 hbig
    have hnot : ¬ (slotAt t (base.toNat + w.toNat % 256)).1 ≤ 8 := by
      intro hl
      apply hbig
      apply UInt64.le_iff_toNat_le.mpr
      rw [and_255, e1]
      exact hl
    simp only [hnot, ↓reduceIte]
    rw [← s1]
    exact slotWord_spec s2 h32

/-- What the decoder does with a lookup, in the spec's terms. Enough bits at hand: `decodeSymbol` gives that symbol
and uses that many bits, whatever follows. Too few: `decodeSymbol` has nothing to give from what's at hand. -/
theorem lookup_decode {t : ByteArray} {base : USize} {b : BitBuffer} {c : PrefixCode} (hok : TableOk t base.toNat c)
    (h32 : t.size < 2 ^ 32) (hC : Complete c) :
    let v := lookup t base b.word hok.toTableFits h32
    (∀ f : List Bool, (v.toNat % 256 ≤ b.count.toNat →
        decodeSymbol c (b.held ++ f) =
          some (v.toNat / 256 % 65536, lowBits (b.word.toNat / 2 ^ (v.toNat % 256)) (b.count.toNat - v.toNat % 256) ++ f))) ∧
      (b.count.toNat < v.toNat % 256 → decodeSymbol c b.held = none) := by
  intro v
  obtain ⟨h1, h2⟩ := lookup_spec (w := b.word) hok.toTableFits h32
  have hh := hok.hit b.word.toNat
  rw [← h1, ← h2] at hh
  exact ⟨fun f hle => hh.decode hC hle f, fun hlt => hh.short hC hlt⟩

end Brotli.Decoder
