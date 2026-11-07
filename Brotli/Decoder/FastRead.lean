module

public import Brotli.Decoder.State
public import Brotli.Decoder.Reader

@[expose] public section

/-!
# The fast command loop's reads

The reads the fast command loop makes of its table arena (`TabOk`), each one load or two with its bounds proved, and
equal to the reads the step machine makes: a symbol by one 8-byte load at its slot (`lookupT`, equal to `lookup`), a
mask `2 ^ n - 1` (`maskT`), a 4-byte table base (`load32`) and an 8-byte entry (`load64`).
-/

namespace Brotli.Decoder

open Brotli.Spec

/-! ### Four bytes -/

theorem four_bytes32 (b0 b1 b2 b3 : UInt8) :
    (b0.toUInt64 ||| (b1.toUInt64 <<< 8) ||| (b2.toUInt64 <<< 16) ||| (b3.toUInt64 <<< 24)).toNat =
      b0.toNat + 256 * (b1.toNat + 256 * (b2.toNat + 256 * b3.toNat)) := by
  have c0 : b0.toNat < 256 := b0.toNat_lt
  have c1 : b1.toNat < 256 := b1.toNat_lt
  have c2 : b2.toNat < 256 := b2.toNat_lt
  have e1 := or_byte (b := b1) (k := 8) (K := 8) (P := 256) rfl (by decide) rfl (UInt8.toNat_toUInt64 b0) c0
  have e2 := or_byte (b := b2) (k := 16) (K := 16) (P := 65536) rfl (by decide) rfl e1 (by omega)
  have e3 := or_byte (b := b3) (k := 24) (K := 24) (P := 16777216) rfl (by decide) rfl e2 (by omega)
  rw [e3]
  omega

/-- The 4 bytes from `i` as one little-endian word, which compiles to one 4-byte load. -/
@[inline] def load32 (t : ByteArray) (i : USize) (h : i.toNat + 4 ≤ t.size) (h32 : t.size < 2 ^ 32) : UInt64 :=
  (t.uget i (by omega)).toUInt64 |||
    ((t.uget (i + USize.ofNat 1) (by rw [fastIdx_add (by omega)]; omega)).toUInt64 <<< 8) |||
    ((t.uget (i + USize.ofNat 2) (by rw [fastIdx_add (by omega)]; omega)).toUInt64 <<< 16) |||
    ((t.uget (i + USize.ofNat 3) (by rw [fastIdx_add (by omega)]; omega)).toUInt64 <<< 24)

theorem load32_toNat (t : ByteArray) (i : USize) (h : i.toNat + 4 ≤ t.size) (h32 : t.size < 2 ^ 32) :
    (load32 t i h h32).toNat = leAt t i.toNat 4 := by
  unfold load32
  rw [four_bytes32]
  simp only [uget_toNat]
  rw [fastIdx_add (k := 1) (by omega), fastIdx_add (k := 2) (by omega), fastIdx_add (k := 3) (by omega)]
  simp only [leAt, byteN, Nat.add_assoc, Nat.reduceAdd, Nat.mul_zero, Nat.add_zero]

/-! ### A symbol by one load -/

/-- A slot's number from the 8 bytes at its start: their low 16 bits. -/
theorem leAt_slot (t : ByteArray) (q : Nat) : leAt t (2 * q) 8 % 65536 = slotNum t q := by
  simp only [leAt, byteN, slotNum]
  have := (t.data[2 * q]?.getD 0).toNat_lt
  have := (t.data[2 * q + 1]?.getD 0).toNat_lt
  omega

/-- A slot's word from an 8-byte load at its start. -/
theorem load64_slot {t : ByteArray} {i : USize} {q : Nat} (hi : i.toNat = 2 * q) (h : i.toNat + 8 ≤ t.size)
    (h32 : t.size < 2 ^ 32) : load64 t i h h32 &&& 0xFFFF = UInt64.ofNat (slotNum t q) := by
  apply UInt64.toNat_inj.mp
  rw [UInt64.toNat_and, show (0xFFFF : UInt64).toNat = 2 ^ 16 - 1 from rfl, Nat.and_two_pow_sub_one_eq_mod, load64_toNat,
    hi, show (2 : Nat) ^ 16 = 65536 from rfl, leAt_slot, UInt64.toNat_ofNat']
  have := slotNum_lt t q
  exact (Nat.mod_eq_of_lt (by omega)).symm

theorem lookupT_root {t : ByteArray} {base : USize} {lim : Nat} (hin : TableIn t base.toNat lim) (hl : lim + 6 ≤ t.size)
    (h32 : t.size < 2 ^ 32) (w : UInt64) :
    (rootIndex base w <<< USize.ofNat 1).toNat = 2 * (rootIndex base w).toNat ∧
      (rootIndex base w <<< USize.ofNat 1).toNat + 8 ≤ t.size := by
  have hf := hin.fits (by omega)
  have hr := rootIndex_toNat w hf h32
  have hw : w.toNat % 256 < 256 := Nat.mod_lt _ (by decide)
  have hroot := hin.root
  have e : (rootIndex base w <<< USize.ofNat 1).toNat = 2 * (rootIndex base w).toNat := by
    have hs := USize.le_size
    rw [USize.size_eq_two_pow] at hs
    rw [USize.toNat_shiftLeft, fastLit (by decide), Nat.mod_eq_of_lt (show 1 < System.Platform.numBits by
      rcases System.Platform.numBits_eq with h | h <;> omega), Nat.shiftLeft_eq, hr]
    exact (Nat.mod_eq_of_lt (by omega)).trans (by omega)
  exact ⟨e, by rw [e, hr]; omega⟩

theorem lookupT_sub {t : ByteArray} {base : USize} {lim : Nat} (hin : TableIn t base.toNat lim) (hl : lim + 6 ≤ t.size)
    (h32 : t.size < 2 ^ 32) {w e : UInt64} (he : e = UInt64.ofNat (slotNum t (base.toNat + w.toNat % 256)))
    (hbig : ¬ (e &&& 15) ≤ 8) :
    (subIndex base w e <<< USize.ofNat 1).toNat = 2 * (subIndex base w e).toNat ∧
      (subIndex base w e <<< USize.ofNat 1).toNat + 8 ≤ t.size := by
  have hf := hin.fits (by omega)
  have hv : e.toNat = slotNum t (base.toNat + w.toNat % 256) := by
    rw [he, UInt64.toNat_ofNat']
    have := slotNum_lt t (base.toNat + w.toNat % 256)
    exact Nat.mod_eq_of_lt (by omega)
  have he1 : e.toNat % 16 = (slotAt t (base.toNat + w.toNat % 256)).1 := by rw [hv]; rfl
  have he2 : e.toNat / 16 = (slotAt t (base.toNat + w.toNat % 256)).2 := by rw [hv]; rfl
  obtain ⟨s1, _⟩ := subIndex_spec hf h32 he1 he2 hbig
  have hw : w.toNat % 256 < 256 := Nat.mod_lt _ (by decide)
  have hb : 8 < (slotAt t (base.toNat + w.toNat % 256)).1 := by
    have : ¬ (e &&& 15).toNat ≤ (8 : UInt64).toNat := fun hl => hbig (UInt64.le_iff_toNat_le.mpr hl)
    rw [UInt64.toNat_and, show (15 : UInt64).toNat = 2 ^ 4 - 1 from rfl, Nat.and_two_pow_sub_one_eq_mod, he1] at this
    exact Nat.lt_of_not_le this
  obtain ⟨_, hsub⟩ := hin.sub _ hw hb
  have hj : (w.toNat / 256) % 2 ^ ((slotAt t (base.toNat + w.toNat % 256)).1 - 8) <
      2 ^ ((slotAt t (base.toNat + w.toNat % 256)).1 - 8) := Nat.mod_lt _ (Nat.two_pow_pos _)
  have e : (subIndex base w e <<< USize.ofNat 1).toNat = 2 * (subIndex base w e).toNat := by
    have hs := USize.le_size
    rw [USize.size_eq_two_pow] at hs
    rw [USize.toNat_shiftLeft, fastLit (by decide), Nat.mod_eq_of_lt (show 1 < System.Platform.numBits by
      rcases System.Platform.numBits_eq with h | h <;> omega), Nat.shiftLeft_eq, s1]
    exact (Nat.mod_eq_of_lt (by omega)).trans (by omega)
  exact ⟨e, by rw [e, s1]; omega⟩

/-- `lookup` by one 8-byte load at the slot, of which the low 16 bits are kept, so that the length's test and the symbol
come from one value (P31); a code word longer than 8 bits takes a second load. Each load reads up to 6 bytes past its
slot, which stay in the arena: every table lies within `lim`, and 6 bytes follow it. -/
@[inline] def lookupT (t : ByteArray) (base : USize) (w : UInt64) {lim : Nat} (hin : TableIn t base.toNat lim)
    (hl : lim + 6 ≤ t.size) (h32 : t.size < 2 ^ 32) : UInt64 :=
  let e := load64 t (rootIndex base w <<< USize.ofNat 1) (lookupT_root hin hl h32 w).2 h32 &&& 0xFFFF
  if hbig : e &&& 15 ≤ 8 then e
  else
    load64 t (subIndex base w e <<< USize.ofNat 1)
      (lookupT_sub hin hl h32 (load64_slot (lookupT_root hin hl h32 w).1 _ h32 |>.trans
        (by rw [rootIndex_toNat w (hin.fits (by omega)) h32])) hbig).2 h32 &&& 0xFFFF

theorem slot16_load {t : ByteArray} {i : USize} (h : 2 * i.toNat + 2 ≤ t.size) (h32 : t.size < 2 ^ 32) {j : USize}
    (hj : j.toNat = 2 * i.toNat) (h8 : j.toNat + 8 ≤ t.size) : load64 t j h8 h32 &&& 0xFFFF = slot16 t i h h32 := by
  rw [load64_slot hj h8 h32, slot16_eq]

/-- `lookupT` is `lookup`. -/
theorem lookupT_eq {t : ByteArray} {base : USize} {w : UInt64} {lim : Nat} (hin : TableIn t base.toNat lim)
    (hl : lim + 6 ≤ t.size) (h32 : t.size < 2 ^ 32) :
    lookupT t base w hin hl h32 = lookup t base w (hin.fits (by omega)) h32 := by
  unfold lookupT lookup
  have hroot := lookupT_root hin hl h32 w
  have e1 := slot16_load (rootIndex_bound w (hin.fits (by omega)) h32) h32 hroot.1 hroot.2
  simp only [e1]
  split
  · rfl
  · rename_i hbig
    have he : slot16 t (rootIndex base w) (rootIndex_bound w (hin.fits (by omega)) h32) h32 =
        UInt64.ofNat (slotNum t (base.toNat + w.toNat % 256)) := by
      rw [slot16_eq, rootIndex_toNat w (hin.fits (by omega)) h32]
    exact slot16_load _ h32 (lookupT_sub hin hl h32 he hbig).1 _

end Brotli.Decoder
