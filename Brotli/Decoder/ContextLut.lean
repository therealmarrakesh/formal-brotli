module

public import Brotli.Spec.Stream

@[expose] public section

/-!
# The context lookup

A literal's context ID comes from the two previous bytes. Rather than branch on the context mode for each byte, one
table of 4 × 512 bytes gives each mode's part from the previous byte and from the one before it, and the context ID
is their `|||`. `cid_eq` proves this is the spec's `contextId`.
-/

namespace Brotli.Decoder

open Brotli.Spec

/-- The part of a context ID from the previous byte. -/
def ctxLow (mode p1 : Nat) : Nat :=
  match mode with
  | 0 => p1 &&& 0x3f
  | 1 => p1 >>> 2
  | 2 => Lut0.getD p1 0
  | _ => Lut2.getD p1 0 <<< 3

/-- The part of a context ID from the byte before it. -/
def ctxHigh (mode p2 : Nat) : Nat :=
  match mode with
  | 0 => 0
  | 1 => 0
  | 2 => Lut1.getD p2 0
  | _ => Lut2.getD p2 0

/-- A context ID is its two parts. -/
theorem contextId_parts (mode p1 p2 : Nat) : contextId mode p1 p2 = ctxLow mode p1 ||| ctxHigh mode p2 := by
  unfold contextId ctxLow ctxHigh
  split <;> simp

private theorem parts_lt : ∀ m, m < 4 → ∀ p, p < 256 → ctxLow m p < 256 ∧ ctxHigh m p < 256 := by
  decide +kernel

/-- Entry `i` of the table: mode `i / 512`, from the previous byte in the first half and the byte before in the
second. -/
def ctxEntry (i : Nat) : Nat :=
  if i % 512 < 256 then ctxLow (i / 512) (i % 512) else ctxHigh (i / 512) (i % 512 - 256)

/-- The context lookup table. -/
def contextLut : ByteArray :=
  ((List.range 2048).map fun i => (ctxEntry i).toUInt8).toByteArray

theorem contextLut_size : contextLut.size = 2048 := by
  simp [contextLut, List.size_toByteArray]

private theorem contextLut_get {p : USize} (h' : p.toNat < contextLut.size) :
    (contextLut.uget p h').toNat = ctxEntry p.toNat := by
  have h : p.toNat < 2048 := by
    rw [contextLut_size] at h'
    exact h'
  have hlt : ctxEntry p.toNat < 256 := by
    unfold ctxEntry
    have hm : p.toNat / 512 < 4 := by omega
    split
    · exact (parts_lt _ hm _ (by omega)).1
    · exact (parts_lt _ hm _ (by omega)).2
  simp only [ByteArray.uget, contextLut, List.data_toByteArray]
  simp
  omega

private theorem usize_add {a b : USize} (h : a.toNat + b.toNat < 2 ^ 32) : (a + b).toNat = a.toNat + b.toNat := by
  rw [USize.toNat_add, ← USize.size_eq_two_pow]
  have := USize.le_size
  exact Nat.mod_eq_of_lt (by omega)

private theorem usize_ofNat {n : Nat} (h : n < 2 ^ 32) : (USize.ofNat n).toNat = n := by
  rw [USize.toNat_ofNat', ← USize.size_eq_two_pow]
  have := USize.le_size
  exact Nat.mod_eq_of_lt (by omega)

private theorem toUSize_toNat (x : UInt8) : x.toUSize.toNat = x.toNat := by
  simp

/-- A literal's context ID, with `modeOff` the context mode's place in the table. -/
@[inline] def cidFast (modeOff : USize) (p1 p2 : UInt8) (hm : modeOff.toNat + 512 ≤ 2048) : UInt8 :=
  contextLut.uget (modeOff + p1.toUSize) (by
    have := p1.toNat_lt
    rw [usize_add (by rw [toUSize_toNat]; omega), toUSize_toNat, contextLut_size]
    omega) |||
  contextLut.uget (modeOff + USize.ofNat 256 + p2.toUSize) (by
    have := p2.toNat_lt
    rw [usize_add (by rw [usize_add (by rw [usize_ofNat (by decide)]; omega), usize_ofNat (by decide), toUSize_toNat]; omega),
      usize_add (by rw [usize_ofNat (by decide)]; omega), usize_ofNat (by decide), toUSize_toNat, contextLut_size]
    omega)

/-- `cidFast` is the spec's context ID. -/
theorem cid_eq {modeOff : USize} {p1 p2 : UInt8} (hm : modeOff.toNat + 512 ≤ 2048) (hd : modeOff.toNat % 512 = 0) :
    (cidFast modeOff p1 p2 hm).toNat = contextId (modeOff.toNat / 512) p1.toNat p2.toNat := by
  have h1 := p1.toNat_lt
  have h2 := p2.toNat_lt
  have i1 : (modeOff + p1.toUSize).toNat = modeOff.toNat + p1.toNat := by
    rw [usize_add (by rw [toUSize_toNat]; omega), toUSize_toNat]
  have i2 : (modeOff + USize.ofNat 256 + p2.toUSize).toNat = modeOff.toNat + 256 + p2.toNat := by
    rw [usize_add (by rw [usize_add (by rw [usize_ofNat (by decide)]; omega), usize_ofNat (by decide), toUSize_toNat]; omega),
      usize_add (by rw [usize_ofNat (by decide)]; omega), usize_ofNat (by decide), toUSize_toNat]
  unfold cidFast
  rw [UInt8.toNat_or, contextLut_get, contextLut_get, i1, i2, contextId_parts]
  have e1 : ctxEntry (modeOff.toNat + p1.toNat) = ctxLow (modeOff.toNat / 512) p1.toNat := by
    unfold ctxEntry
    have hm1 : (modeOff.toNat + p1.toNat) % 512 = p1.toNat := by omega
    have hm2 : (modeOff.toNat + p1.toNat) / 512 = modeOff.toNat / 512 := by omega
    rw [hm1, hm2, ite_eq_left h1]
  have e2 : ctxEntry (modeOff.toNat + 256 + p2.toNat) = ctxHigh (modeOff.toNat / 512) p2.toNat := by
    unfold ctxEntry
    have hm1 : (modeOff.toNat + 256 + p2.toNat) % 512 = 256 + p2.toNat := by omega
    have hm2 : (modeOff.toNat + 256 + p2.toNat) / 512 = modeOff.toNat / 512 := by omega
    rw [hm1, hm2, ite_eq_right (by omega), Nat.add_sub_cancel_left]
  rw [e1, e2]

end Brotli.Decoder
