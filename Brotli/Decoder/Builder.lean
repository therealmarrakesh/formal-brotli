module

public import Brotli.Decoder.TableDown
public import Brotli.Decoder.Window
public import Brotli.Decoder.Lookup
public import Brotli.Decoder.Fixed

@[expose] public section

/-!
# Building a table in fixed-width values

The table builder that runs. It walks a code's symbols longest first, from lists of each length's symbols (`ListsIs`),
and writes each code word's slots in place. `buildFast_eq` proves it writes exactly the bytes of `buildDown`, whose
proofs say what a table means, and `buildSingleFast_eq` does the same for `buildSingle`.
-/

namespace Brotli.Decoder

open Brotli.Spec

/-! ### Bytes and 16-bit values in an array -/

/-- Writes a byte, if the position is in the array. -/
@[inline] def setU (t : ByteArray) (i : USize) (v : UInt8) : ByteArray :=
  if h : i.toNat < t.size then t.uset i v h else t

/-- Reads a byte, 0 outside the array. -/
@[inline] def getU (t : ByteArray) (i : USize) : UInt8 :=
  if h : i.toNat < t.size then t.uget i h else 0

private theorem data_uset (t : ByteArray) (i : USize) (v : UInt8) (h : i.toNat < t.size) :
    (t.uset i v h).data = t.data.set i.toNat v h := by
  cases t
  rfl

private theorem data_set (t : ByteArray) (i : Nat) (v : UInt8) : (t.set! i v).data = t.data.setIfInBounds i v := by
  cases t
  rfl

private theorem ba_ext {a b : ByteArray} (h : a.data = b.data) : a = b := by
  cases a
  cases b
  simp_all

theorem uset_eq (t : ByteArray) (i : USize) (v : UInt8) (h : i.toNat < t.size) : t.uset i v h = t.set! i.toNat v := by
  apply ba_ext
  rw [data_set, data_uset, Array.setIfInBounds, dite_eq_left (show i.toNat < t.data.size from h)]

/-- A write within the array is `setU`'s. -/
theorem uset_setU (t : ByteArray) (i : USize) (v : UInt8) (h : i.toNat < t.size) : t.uset i v h = setU t i v := by
  unfold setU
  rw [dite_eq_left h]

/-- A read within the array is `getU`'s. -/
theorem uget_getU (t : ByteArray) (i : USize) (h : i.toNat < t.size) : t.uget i h = getU t i := by
  unfold getU
  rw [dite_eq_left h]

theorem setU_eq (t : ByteArray) (i : USize) (v : UInt8) : setU t i v = t.set! i.toNat v := by
  unfold setU
  by_cases h : i.toNat < t.size
  · rw [dite_eq_left h, uset_eq]
  · rw [dite_eq_right h]
    apply ba_ext
    rw [data_set, Array.setIfInBounds, dite_eq_right (show ¬ i.toNat < t.data.size from h)]

private theorem size_set (t : ByteArray) (i : Nat) (v : UInt8) : (t.set! i v).size = t.size := by
  show (t.set! i v).data.size = t.data.size
  rw [data_set]
  simp

theorem size_setU (t : ByteArray) (i : USize) (v : UInt8) : (setU t i v).size = t.size := by
  rw [setU_eq, size_set]

theorem size_uset' (t : ByteArray) (i : USize) (v : UInt8) (h : i.toNat < t.size) : (t.uset i v h).size = t.size := by
  rw [uset_eq, size_set]

theorem uget_toNat (t : ByteArray) (i : USize) (h : i.toNat < t.size) :
    (t.uget i h).toNat = (t.data[i.toNat]?.getD 0).toNat := by
  cases t with
  | mk bs =>
    have h' : i.toNat < bs.size := h
    simp [ByteArray.uget, h']

theorem getU_toNat (t : ByteArray) (i : USize) : (getU t i).toNat = (t.data[i.toNat]?.getD 0).toNat := by
  unfold getU
  by_cases h : i.toNat < t.size
  · rw [dite_eq_left h, uget_toNat]
  · rw [dite_eq_right h]
    have h' : ¬ i.toNat < t.data.size := h
    rw [Array.getElem?_eq_none (by omega)]
    rfl

private theorem get_set_same {t : ByteArray} {i : Nat} {v : UInt8} (h : i < t.size) :
    (t.set! i v).data[i]?.getD 0 = v := by
  rw [data_set]
  simp
  intro hle
  omega

private theorem get_set_ne {t : ByteArray} {i j : Nat} {v : UInt8} (h : j ≠ i) : (t.set! i v).data[j]? = t.data[j]? := by
  rw [data_set]
  simp [Ne.symm h]

/-- A byte written reads back. -/
theorem setU_get_same {t : ByteArray} {i : USize} {v : UInt8} (h : i.toNat < t.size) :
    (setU t i v).data[i.toNat]?.getD 0 = v := by
  rw [setU_eq]
  exact get_set_same h

/-- Other bytes stay. -/
theorem setU_get_ne {t : ByteArray} {i : USize} {v : UInt8} {j : Nat} (h : j ≠ i.toNat) :
    (setU t i v).data[j]? = t.data[j]? := by
  rw [setU_eq]
  exact get_set_ne h

theorem uset_get_same {t : ByteArray} {i : USize} {v : UInt8} (h : i.toNat < t.size) :
    (t.uset i v h).data[i.toNat]?.getD 0 = v := by
  rw [uset_setU]
  exact setU_get_same h

theorem uset_get_ne {t : ByteArray} {i : USize} {v : UInt8} {j : Nat} (h : i.toNat < t.size) (hj : j ≠ i.toNat) :
    (t.uset i v h).data[j]? = t.data[j]? := by
  rw [uset_setU]
  exact setU_get_ne hj

private theorem usize_add' {a b : USize} (h : a.toNat + b.toNat < 2 ^ 32) : (a + b).toNat = a.toNat + b.toNat := by
  rw [USize.toNat_add, ← USize.size_eq_two_pow]
  have := USize.le_size
  exact Nat.mod_eq_of_lt (by omega)

private theorem usize_lit' {n : Nat} (h : n < 2 ^ 32) : (USize.ofNat n).toNat = n := by
  rw [USize.toNat_ofNat', ← USize.size_eq_two_pow]
  have := USize.le_size
  exact Nat.mod_eq_of_lt (by omega)

private theorem usize_mul' {a : USize} {n : Nat} (hn : n < 2 ^ 32) (h : a.toNat * n < 2 ^ 32) :
    (a * USize.ofNat n).toNat = a.toNat * n := by
  rw [USize.toNat_mul, usize_lit' hn, ← USize.size_eq_two_pow]
  have := USize.le_size
  exact Nat.mod_eq_of_lt (by omega)

private theorem usize_next {i n : USize} (h : i < n) : (i + USize.ofNat 1).toNat = i.toNat + 1 := by
  have hlt : i.toNat < n.toNat := USize.lt_iff_toNat_lt.mp h
  have hn := n.toNat_lt_size
  rw [USize.toNat_add, usize_lit' (by decide), ← USize.size_eq_two_pow]
  exact Nat.mod_eq_of_lt (by omega)

private theorem u64_add' {a b : UInt64} (h : a.toNat + b.toNat < 2 ^ 64) : (a + b).toNat = a.toNat + b.toNat := by
  rw [UInt64.toNat_add]
  exact Nat.mod_eq_of_lt h

private theorem u64_sub' {a b : UInt64} (h : b.toNat ≤ a.toNat) : (a - b).toNat = a.toNat - b.toNat :=
  UInt64.toNat_sub_of_le _ _ (UInt64.le_iff_toNat_le.mpr h)

private theorem u64_shl {a d : UInt64} (hd : d.toNat < 64) (h : a.toNat * 2 ^ d.toNat < 2 ^ 64) :
    (a <<< d).toNat = a.toNat * 2 ^ d.toNat := by
  rw [UInt64.toNat_shiftLeft, Nat.mod_eq_of_lt hd, Nat.shiftLeft_eq]
  exact Nat.mod_eq_of_lt h

private theorem u64_shr {a d : UInt64} (hd : d.toNat < 64) : (a >>> d).toNat = a.toNat / 2 ^ d.toNat := by
  rw [UInt64.toNat_shiftRight, Nat.mod_eq_of_lt hd, Nat.shiftRight_eq_div_pow]

theorem one_shl {d : UInt64} (hd : d.toNat < 32) : ((1 : UInt64) <<< d).toNat = 2 ^ d.toNat := by
  have hp : 2 ^ d.toNat < 2 ^ 32 := Nat.pow_lt_pow_right (by decide) hd
  rw [u64_shl (by omega) (by rw [show (1 : UInt64).toNat = 1 from rfl]; omega)]
  exact Nat.one_mul _

private theorem two_shl {d : UInt64} (hd : d.toNat < 32) : ((2 : UInt64) <<< d).toNat = 2 * 2 ^ d.toNat := by
  have hp : 2 ^ d.toNat < 2 ^ 32 := Nat.pow_lt_pow_right (by decide) hd
  rw [u64_shl (by omega) (by rw [show (2 : UInt64).toNat = 2 from rfl]; omega)]
  rfl

private theorem and255 (v : UInt64) : (v &&& 255).toNat = v.toNat % 256 := by
  rw [UInt64.toNat_and, show (255 : UInt64).toNat = 2 ^ 8 - 1 from rfl, Nat.and_two_pow_sub_one_eq_mod]

private theorem and15 (v : UInt64) : (v &&& 15).toNat = v.toNat % 16 := by
  rw [UInt64.toNat_and, show (15 : UInt64).toNat = 2 ^ 4 - 1 from rfl, Nat.and_two_pow_sub_one_eq_mod]

private theorem byte_of {v : UInt64} {n : Nat} (h : v.toNat % 256 = n % 256) : v.toUInt8 = n.toUInt8 := by
  apply UInt8.toNat_inj.mp
  rw [UInt64.toNat_toUInt8]
  show _ = (UInt8.ofNat n).toNat
  rw [UInt8.toNat_ofNat']
  exact h

/-- A 16-bit value in an array. -/
def u16At (b : ByteArray) (i : Nat) : Nat :=
  (b.data[2 * i]?.getD 0).toNat + 256 * (b.data[2 * i + 1]?.getD 0).toNat

theorem u16At_lt (b : ByteArray) (i : Nat) : u16At b i < 65536 := by
  unfold u16At
  have h1 := (b.data[2 * i]?.getD 0).toNat_lt
  have h2 := (b.data[2 * i + 1]?.getD 0).toNat_lt
  omega

/-- Reads a 16-bit value. -/
@[inline] def u16Get (b : ByteArray) (i : USize) : UInt64 :=
  let p := i * USize.ofNat 2
  (getU b p).toUInt64 ||| ((getU b (p + USize.ofNat 1)).toUInt64 <<< 8)

/-- Writes a 16-bit value. -/
@[inline] def u16Set (b : ByteArray) (i : USize) (v : UInt64) : ByteArray :=
  let p := i * USize.ofNat 2
  setU (setU b p v.toUInt8) (p + USize.ofNat 1) (v >>> 8).toUInt8

private theorem p2 {i : USize} (h : i.toNat < 2 ^ 16) : (i * USize.ofNat 2).toNat = 2 * i.toNat := by
  rw [usize_mul' (by decide) (by omega)]
  omega

private theorem p3 {i : USize} (h : i.toNat < 2 ^ 16) : (i * USize.ofNat 2 + USize.ofNat 1).toNat = 2 * i.toNat + 1 := by
  rw [usize_add' (by rw [p2 h, usize_lit' (by decide)]; omega), p2 h, usize_lit' (by decide)]

theorem u16Get_toNat (b : ByteArray) {i : USize} (h : i.toNat < 2 ^ 16) : (u16Get b i).toNat = u16At b i.toNat := by
  unfold u16Get u16At
  dsimp only
  have hlo : (getU b (i * USize.ofNat 2)).toUInt64.toNat < 2 ^ 8 := by
    have := (getU b (i * USize.ofNat 2)).toNat_lt
    simpa using this
  have hhi : (getU b (i * USize.ofNat 2 + USize.ofNat 1)).toUInt64.toNat < 2 ^ 8 := by
    have := (getU b (i * USize.ofNat 2 + USize.ofNat 1)).toNat_lt
    simpa using this
  have h8 : (8 : UInt64).toNat = 8 := rfl
  have key := BitBuffer.add_word (word := (getU b (i * USize.ofNat 2)).toUInt64) (count := 8)
    (v := (getU b (i * USize.ofNat 2 + USize.ofNat 1)).toUInt64) (n := 8) (by rw [h8]; omega) (by rw [h8]; omega)
    (by rw [h8]; exact hlo) hhi
  rw [key, h8, UInt8.toNat_toUInt64, UInt8.toNat_toUInt64, getU_toNat, getU_toNat, p2 h, p3 h]

theorem size_u16Set (b : ByteArray) (i : USize) (v : UInt64) : (u16Set b i v).size = b.size := by
  unfold u16Set
  simp only [size_setU]

/-- Reads a 16-bit value in the array. -/
@[inline] def u16GetU (b : ByteArray) (i : USize) (h : 2 * i.toNat + 1 < b.size) (h16 : i.toNat < 2 ^ 16) : UInt64 :=
  (b.uget (i * USize.ofNat 2) (by rw [p2 h16]; omega)).toUInt64 |||
    ((b.uget (i * USize.ofNat 2 + USize.ofNat 1) (by rw [p3 h16]; omega)).toUInt64 <<< 8)

/-- Writes a 16-bit value in the array. -/
@[inline] def u16SetU (b : ByteArray) (i : USize) (v : UInt64) (h : 2 * i.toNat + 1 < b.size) (h16 : i.toNat < 2 ^ 16) :
    ByteArray :=
  (b.uset (i * USize.ofNat 2) v.toUInt8 (by rw [p2 h16]; omega)).uset (i * USize.ofNat 2 + USize.ofNat 1) (v >>> 8).toUInt8
    (by rw [size_uset', p3 h16]; omega)

theorem u16GetU_eq (b : ByteArray) (i : USize) (h : 2 * i.toNat + 1 < b.size) (h16 : i.toNat < 2 ^ 16) :
    u16GetU b i h h16 = u16Get b i := by
  simp only [u16GetU, u16Get, uget_getU]

theorem u16SetU_eq (b : ByteArray) (i : USize) (v : UInt64) (h : 2 * i.toNat + 1 < b.size) (h16 : i.toNat < 2 ^ 16) :
    u16SetU b i v h h16 = u16Set b i v := by
  simp only [u16SetU, u16Set, uset_setU]

theorem size_u16SetU (b : ByteArray) (i : USize) (v : UInt64) (h : 2 * i.toNat + 1 < b.size) (h16 : i.toNat < 2 ^ 16) :
    (u16SetU b i v h h16).size = b.size := by
  rw [u16SetU_eq, size_u16Set]

theorem u16At_set_same {b : ByteArray} {i : USize} {v : UInt64} (h : i.toNat < 2 ^ 16) (hs : 2 * i.toNat + 1 < b.size)
    (hv : v.toNat < 65536) : u16At (u16Set b i v) i.toNat = v.toNat := by
  unfold u16Set u16At
  dsimp only
  rw [setU_eq, setU_eq, p2 h, p3 h, get_set_ne (by omega), get_set_same (by omega), get_set_same (by rw [size_set]; exact hs)]
  have e1 : v.toUInt8.toNat = v.toNat % 256 := by simp
  have e2 : (v >>> 8).toUInt8.toNat = v.toNat / 256 := by
    rw [UInt64.toNat_toUInt8, u64_shr (by decide)]
    show v.toNat / 256 % 256 = _
    omega
  rw [e1, e2]
  omega

theorem u16At_set_ne {b : ByteArray} {i : USize} {v : UInt64} {j : Nat} (h : i.toNat < 2 ^ 16) (hj : j ≠ i.toNat) :
    u16At (u16Set b i v) j = u16At b j := by
  unfold u16Set u16At
  dsimp only
  rw [setU_eq, setU_eq, p2 h, p3 h, get_set_ne (by omega), get_set_ne (by omega), get_set_ne (by omega), get_set_ne (by omega)]

/-- `n` zero bytes, made at each call: as a constant, the array of `n` boxed bytes it is made from would be kept too. -/
@[noinline, never_extract] def zerosOf (n : Nat) : ByteArray := ⟨Array.replicate n 0⟩

/-- `t` with `k` zero bytes pushed. -/
def pushZeros (t : ByteArray) : Nat → ByteArray
  | 0 => t
  | k + 1 => pushZeros (t.push 0) k

theorem pushZeros_data : ∀ (k : Nat) (t : ByteArray), (pushZeros t k).data = t.data ++ Array.replicate k 0
  | 0, t => by simp [pushZeros]
  | k + 1, t => by
    rw [pushZeros, pushZeros_data k, ByteArray.data_push, Array.push_eq_append, Array.append_assoc,
      ← Array.replicate_succ']

/-- `zerosOf`, pushed byte by byte into an array with room for them, so that no array of boxed bytes is made. -/
@[noinline, never_extract] def zerosPushed (n : Nat) : ByteArray := pushZeros (freshBytes n) n

/-- The compiled code makes `zerosOf` by pushing. -/
@[csimp] theorem zerosOf_eq_pushed : @zerosOf = @zerosPushed := by
  funext n
  apply ByteArray.ext
  rw [zerosPushed, pushZeros_data, show (freshBytes n).data = #[] from rfl, Array.empty_append]
  rfl

/-- 65536 zero bytes. Arrays are zero-filled by copying from it: a copy into an array that has room writes in place,
where a copy of an array onto itself copies all of it. -/
def zeroBlock : ByteArray := zerosOf 65536

theorem zeroBlock_data : zeroBlock.data = Array.replicate 65536 0 := rfl

/-- `t` with `n` zero bytes added at its end, copied from `zeroBlock` at most 65536 at a time. Into an array with room
for them the copy writes in place; into one without, as for a small table built from an empty array, it makes an array of
exactly the bytes needed, so that no array has more room than the state counts. -/
def zeroExtend (t : ByteArray) (n : Nat) : ByteArray :=
  if _h : n ≤ 65536 then zeroBlock.copySlice 0 t t.size n true
  else zeroExtend (zeroBlock.copySlice 0 t t.size 65536 true) (n - 65536)
termination_by n
decreasing_by omega

/-- `zeroBlock_copy` for any array of `N` zeros: stated for a variable `N`, so that the kernel never works with the
literal 65536. -/
private theorem zeros_copy (z t : ByteArray) {N n : Nat} (hz : z.data = Array.replicate N 0) (h : n ≤ N) :
    (z.copySlice 0 t t.size n true).data = t.data ++ Array.replicate n 0 := by
  simp only [ByteArray.copySlice, hz]
  rw [Array.extract_eq_self_of_le (by simp),
    Array.extract_empty_of_size_le_start (start := t.size + min n ((Array.replicate N (0 : UInt8)).size - 0))
      (by simp only [ByteArray.size_data, Array.size_replicate]; omega),
    Array.append_empty, Array.extract_replicate]
  congr 2
  omega

theorem zeroBlock_copy (t : ByteArray) {n : Nat} (h : n ≤ 65536) :
    (zeroBlock.copySlice 0 t t.size n true).data = t.data ++ Array.replicate n 0 :=
  zeros_copy zeroBlock t zeroBlock_data h

theorem zeroExtend_data : ∀ (n : Nat) (t : ByteArray), (zeroExtend t n).data = t.data ++ Array.replicate n 0 := by
  intro n
  induction n using Nat.strongRecOn with
  | _ n ih =>
    intro t
    rw [zeroExtend]
    by_cases h : n ≤ 65536
    · rw [dite_eq_left h]
      exact zeroBlock_copy t h
    · rw [dite_eq_right h, ih _ (by omega), zeroBlock_copy t (Nat.le_refl _), Array.append_assoc, Array.replicate_append_replicate,
        show 65536 + (n - 65536) = n by omega]

theorem zeroExtend_eq (t : ByteArray) (n : Nat) : zeroExtend t n = t ++ ByteArray.mk (Array.replicate n 0) := by
  apply ByteArray.ext
  rw [ByteArray.data_append]
  exact zeroExtend_data n t

/-- `zeroExtend` appends `zeros`. -/
theorem zeroExtend_zeros (t : ByteArray) (n : Nat) : zeroExtend t n = t ++ zeros n := zeroExtend_eq t n

theorem size_zeroExtend (t : ByteArray) (n : Nat) : (zeroExtend t n).size = t.size + n := by
  rw [zeroExtend_zeros, ByteArray.size_append, size_zeros]

/-- A scratch array of `k` zero bytes, made at its size. -/
@[inline] def zeroBytes (k : Nat) : ByteArray := zeroExtend (freshBytes k) k

theorem zeroBytes_data {k : Nat} (_h : k < 2 ^ 32) : (zeroBytes k).data = Array.replicate k 0 := by
  unfold zeroBytes
  rw [zeroExtend_data]
  exact Array.empty_append

theorem zeroBytes_size {k : Nat} (h : k < 2 ^ 32) : (zeroBytes k).size = k := by
  show (zeroBytes k).data.size = k
  rw [zeroBytes_data h]
  simp

theorem zeroBytes_get {k i : Nat} (h : k < 2 ^ 32) : (zeroBytes k).data[i]?.getD 0 = 0 := by
  rw [zeroBytes_data h, Array.getElem?_replicate]
  split <;> rfl

/-! ### The code lengths -/

/-- The first `n` code lengths in an array. -/
def lensOf (lens : ByteArray) (n : Nat) : List Nat := (lens.data.toList.take n).map UInt8.toNat

theorem length_lensOf {lens : ByteArray} {n : Nat} (hn : n ≤ lens.size) : (lensOf lens n).length = n := by
  have h : lens.data.size = lens.size := rfl
  simp [lensOf, h]
  omega

theorem lensOf_get {lens : ByteArray} {n i : Nat} (hi : i < n) (hn : n ≤ lens.size) :
    (lensOf lens n)[i]? = some (lens.data[i]?.getD 0).toNat := by
  have h : i < lens.data.size := Nat.lt_of_lt_of_le hi hn
  have e : lens.data[i]? = some lens.data[i] := Array.getElem?_eq_getElem h
  unfold lensOf
  rw [List.getElem?_map, List.getElem?_take, ite_eq_left hi, Array.getElem?_toList, e]
  rfl

/-! ### Reversing a code -/

/-- Each byte reversed. -/
def rev8Lut : ByteArray := ((List.range 256).map fun j => (revBits 8 j).toUInt8).toByteArray

theorem rev8Lut_size : rev8Lut.size = 256 := by
  simp [rev8Lut, List.size_toByteArray]

private theorem rev8Lut_byte {j : Nat} (h : j < 256) : (rev8Lut.data[j]?.getD 0).toNat = revBits 8 j := by
  have hb : revBits 8 j < 256 := revBits_lt 8 j
  simp only [rev8Lut, List.data_toByteArray]
  simp [h]
  omega

private theorem rev8_idx (v : UInt64) : (v &&& 255).toUSize.toNat < rev8Lut.size := by
  rw [rev8Lut_size, word_toUSize (by rw [and255]; omega), and255]
  omega

/-- A byte, reversed. -/
@[inline] def rev8 (v : UInt64) : UInt64 := (rev8Lut.uget (v &&& 255).toUSize (by exact rev8_idx v)).toUInt64

private theorem rev8_toNat (v : UInt64) : (rev8 v).toNat = revBits 8 v.toNat := by
  unfold rev8
  rw [UInt8.toNat_toUInt64, uget_toNat, word_toUSize (by rw [and255]; omega), and255, rev8Lut_byte (by omega)]
  exact revBits_mod 8 v.toNat

private theorem revBits_add : ∀ (a b w : Nat), revBits (a + b) w = revBits a w * 2 ^ b + revBits b (w / 2 ^ a)
  | 0, b, w => by simp [revBits]
  | a + 1, b, w => by
    rw [show a + 1 + b = (a + b) + 1 by omega]
    simp only [revBits]
    rw [revBits_add a b (w / 2), Nat.pow_add, Nat.add_mul, ← Nat.mul_assoc, Nat.div_div_eq_div_mul, Nat.pow_succ,
      Nat.mul_comm 2 (2 ^ a), Nat.add_assoc]

private theorem revBits_zero : ∀ (l : Nat), revBits l 0 = 0
  | 0 => rfl
  | l + 1 => by simp [revBits, revBits_zero l]

/-- A code word's `l` bits, reversed. -/
@[inline] def revFast (l c : UInt64) : UInt64 := (rev8 (c >>> 8) ||| (rev8 c <<< 8)) >>> (16 - l)

theorem revFast_toNat {l c : UInt64} (hl : l.toNat ≤ 15) (hc : c.toNat < 2 ^ l.toNat) :
    (revFast l c).toNat = revBits l.toNat c.toNat := by
  unfold revFast
  have h8 : (8 : UInt64).toNat = 8 := rfl
  have hlo : (rev8 (c >>> 8)).toNat < 2 ^ 8 := by
    rw [rev8_toNat]
    exact revBits_lt 8 _
  have hhi : (rev8 c).toNat < 2 ^ 8 := by
    rw [rev8_toNat]
    exact revBits_lt 8 _
  have key := BitBuffer.add_word (word := rev8 (c >>> 8)) (count := 8) (v := rev8 c) (n := 8) (by rw [h8]; omega)
    (by rw [h8]; omega) (by rw [h8]; exact hlo) hhi
  have hd : (16 - l).toNat = 16 - l.toNat := u64_sub' (by rw [show (16 : UInt64).toNat = 16 from rfl]; omega)
  have hc0 : c.toNat / 2 ^ l.toNat = 0 := Nat.div_eq_of_lt hc
  have e1 := revBits_add l.toNat (16 - l.toNat) c.toNat
  rw [hc0, revBits_zero, show l.toNat + (16 - l.toNat) = 16 by omega, Nat.add_zero] at e1
  have e2 := revBits_add 8 8 c.toNat
  rw [show (8 + 8 : Nat) = 16 from rfl] at e2
  rw [u64_shr (by rw [hd]; omega), key, hd, h8, rev8_toNat, rev8_toNat, u64_shr (by decide), h8]
  have e3 : revBits 8 (c.toNat / 2 ^ 8) + 2 ^ 8 * revBits 8 c.toNat = revBits l.toNat c.toNat * 2 ^ (16 - l.toNat) := by
    rw [← e1, e2]
    omega
  rw [e3]
  exact Nat.mul_div_cancel _ (Nat.two_pow_pos _)

/-! ### Slots -/

private theorem slot2 {pos : UInt64} {size : Nat} (hs : size < 2 ^ 32) (h : 2 * pos.toNat + 1 < size) {j : UInt64}
    (hj : j.toNat ≤ 1) : (pos * 2 + j).toUSize.toNat = 2 * pos.toNat + j.toNat := by
  have h2 : (pos * 2).toNat = 2 * pos.toNat := by
    rw [UInt64.toNat_mul, show (2 : UInt64).toNat = 2 from rfl, Nat.mod_eq_of_lt (by omega)]
    omega
  have e : (pos * 2 + j).toNat = 2 * pos.toNat + j.toNat := by
    rw [u64_add' (by rw [h2]; omega), h2]
  rw [word_toUSize (by rw [e]; omega), e]

/-- Writes one slot, its 16-bit number `v`. -/
@[inline] def putSlot (t : ByteArray) (pos v : UInt64) (h : 2 * pos.toNat + 1 < t.size) (h32 : t.size < 2 ^ 32) :
    ByteArray :=
  (t.uset (pos * 2 + 0).toUSize v.toUInt8 (by rw [slot2 h32 h (by decide)]; show 2 * pos.toNat + 0 < _; omega)).uset
    (pos * 2 + 1).toUSize (v >>> 8).toUInt8 (by
      rw [size_uset', slot2 h32 h (by decide)]
      show 2 * pos.toNat + 1 < _
      omega)

theorem size_putSlot (t : ByteArray) (pos v : UInt64) (h : 2 * pos.toNat + 1 < t.size) (h32 : t.size < 2 ^ 32) :
    (putSlot t pos v h h32).size = t.size := by
  simp only [putSlot, size_uset']

/-- Writing a slot's number is writing its bit count and value. -/
theorem putSlot_eq {t : ByteArray} {pos v : UInt64} {h : 2 * pos.toNat + 1 < t.size} {h32 : t.size < 2 ^ 32}
    {bits val : Nat} (hv : v.toNat = bits + 16 * val) : putSlot t pos v h h32 = writeSlot t pos.toNat bits val := by
  have e0 : v.toUInt8 = ((bits + 16 * val) % 256).toUInt8 := byte_of (by rw [hv]; omega)
  have e1 : (v >>> 8).toUInt8 = ((bits + 16 * val) / 256).toUInt8 := byte_of (by
    rw [u64_shr (by decide), hv]
    show (bits + 16 * val) / 256 % 256 = _
    omega)
  unfold putSlot writeSlot
  rw [uset_eq, uset_eq, slot2 h32 h (j := 0) (by decide), slot2 h32 h (j := 1) (by decide), e0, e1]
  rfl

/-- Reads one slot's 16-bit number. -/
@[inline] def getSlot (t : ByteArray) (pos : UInt64) (h : 2 * pos.toNat + 1 < t.size) (h32 : t.size < 2 ^ 32) : UInt64 :=
  (t.uget (pos * 2 + 0).toUSize (by rw [slot2 h32 h (by decide)]; show 2 * pos.toNat + 0 < _; omega)).toUInt64 |||
    ((t.uget (pos * 2 + 1).toUSize (by rw [slot2 h32 h (by decide)]; show 2 * pos.toNat + 1 < _; omega)).toUInt64 <<< 8)

theorem getSlot_toNat {t : ByteArray} {pos : UInt64} (h : 2 * pos.toNat + 1 < t.size) (h32 : t.size < 2 ^ 32) :
    (getSlot t pos h h32).toNat = slotNum t pos.toNat := by
  have h8 : (8 : UInt64).toNat = 8 := rfl
  have hb : ∀ x : UInt8, x.toUInt64.toNat < 2 ^ 8 := fun x => by
    have := x.toNat_lt
    simpa using this
  unfold getSlot slotNum
  rw [BitBuffer.add_word (count := 8) (n := 8) (by rw [h8]; omega) (by rw [h8]; omega) (by rw [h8]; exact hb _) (hb _), h8,
    UInt8.toNat_toUInt64, UInt8.toNat_toUInt64, uget_toNat, uget_toNat, slot2 h32 h (j := 0) (by decide),
    slot2 h32 h (j := 1) (by decide)]
  rfl

private theorem fill_next {t : ByteArray} {pos step count : UInt64}
    (h : ∀ k, k < count.toNat → 2 * (pos.toNat + k * step.toNat) + 1 < t.size)
    (h32 : t.size < 2 ^ 32) {k : Nat} (hk : k < (count - 1).toNat) (hc : count ≠ 0) :
    2 * ((pos + step).toNat + k * step.toNat) + 1 < t.size := by
  have hne : count.toNat ≠ 0 := fun e => hc (UInt64.toNat_inj.mp (by rw [e]; rfl))
  have h1 : (count - 1).toNat = count.toNat - 1 := u64_sub' (by rw [show (1 : UInt64).toNat = 1 from rfl]; omega)
  have := h (k + 1) (by omega)
  rw [Nat.add_mul, Nat.one_mul] at this
  have e : (pos + step).toNat = pos.toNat + step.toNat := u64_add' (by omega)
  rw [e]
  omega

/-- Writes `count` slots from `pos`, every `step`, each the number `v`, all in the array. -/
def fillRun (v step : UInt64) (t : ByteArray) (pos count : UInt64) (h32 : t.size < 2 ^ 32)
    (h : ∀ k, k < count.toNat → 2 * (pos.toNat + k * step.toNat) + 1 < t.size) : ByteArray :=
  if hc : count = 0 then t
  else
    fillRun v step
      (putSlot t pos v (by
        have := h 0 (by
          have : count.toNat ≠ 0 := fun e => hc (UInt64.toNat_inj.mp (by rw [e]; rfl))
          omega)
        simpa using this) h32) (pos + step) (count - 1) (by rw [size_putSlot]; exact h32) (by
        intro k hk
        rw [size_putSlot]
        exact fill_next h h32 hk hc)
termination_by count.toNat
decreasing_by
  have hne : count.toNat ≠ 0 := fun e => hc (UInt64.toNat_inj.mp (by rw [e]; rfl))
  have h1 : (count - 1).toNat = count.toNat - 1 := u64_sub' (by rw [show (1 : UInt64).toNat = 1 from rfl]; omega)
  omega

theorem fillRun_eq {v : UInt64} {bits val : Nat} (hv : v.toNat = bits + 16 * val) (step : UInt64) :
    ∀ (N : Nat) (t : ByteArray) (pos count : UInt64) (h32 : t.size < 2 ^ 32)
    (h : ∀ k, k < count.toNat → 2 * (pos.toNat + k * step.toNat) + 1 < t.size), count.toNat = N →
    fillRun v step t pos count h32 h = writeRange bits val step.toNat N t pos.toNat := by
  intro N
  induction N with
  | zero =>
    intro t pos count h32 h hc
    have hz : count = 0 := UInt64.toNat_inj.mp (by rw [hc]; rfl)
    rw [fillRun, dite_eq_left hz]
    rfl
  | succ N ih =>
    intro t pos count h32 h hc
    have hz : count ≠ 0 := fun e => by rw [e] at hc; exact Nat.succ_ne_zero _ hc.symm
    have hp := h 0 (by omega)
    have hk1 : (count - 1).toNat = N := by
      rw [u64_sub' (by rw [show (1 : UInt64).toNat = 1 from rfl]; omega), hc]
      rfl
    rw [fillRun, dite_eq_right hz, ih _ _ _ _ _ hk1, putSlot_eq hv, writeRange]
    by_cases hN : N = 0
    · subst hN
      rfl
    · have := h 1 (by omega)
      rw [Nat.one_mul] at this
      have e := u64_add' (a := pos) (b := step) (by omega)
      rw [e]

/-! ### One code word -/

/-- What a step of the builder needs of the array, for a code word of length `l` and code `c`: room for a sub-table,
the root slots in the array, and, for a long code word whose root slot has a sub-table, that it is at least as deep as
the code word and in the array. -/
structure BuildOk (t : ByteArray) (base l c : Nat) : Prop where
  h32 : t.size + 512 < 2 ^ 32
  root : 2 * (base + 256) ≤ t.size
  len : 1 ≤ l ∧ l ≤ 15
  code : c < 2 ^ l
  sub : 8 < l → (slotAt t (base + rootOf l c)).1 ≠ 0 →
    l ≤ (slotAt t (base + rootOf l c)).1 ∧
      2 * (base + (slotAt t (base + rootOf l c)).2 + 2 ^ ((slotAt t (base + rootOf l c)).1 - 8)) ≤ t.size

/-- A run of slots, one every `2 ^ l` from a start below that, stays below `2 ^ W`. -/
private theorem run_lt {l W st k : Nat} (hl : l ≤ W) (hst : st < 2 ^ l) (hk : k < 2 ^ (W - l)) :
    st + k * 2 ^ l < 2 ^ W :=
  ((range_iff hl hst (st + k * 2 ^ l)).mpr ⟨k, hk, rfl⟩).1

/-- A long code word, with what is known of its root slot's number `e`. -/
structure LongOk (t : ByteArray) (base l c : Nat) (rv rp e : UInt64) : Prop where
  ok : BuildOk t base l c
  long : 8 < l
  rv : rv.toNat = revBits l c
  rp : rp.toNat = base + rootOf l c
  e : e.toNat = slotNum t (base + rootOf l c)

private theorem long_root {t : ByteArray} {base l c : Nat} {rv rp e : UInt64} (h : LongOk t base l c rv rp e) :
    2 * rp.toNat + 1 < t.size := by
  have := h.ok.root
  have := rootOf_lt l c
  rw [h.rp]
  omega

private theorem long_rev {t : ByteArray} {base l c : Nat} {rv rp e : UInt64} (h : LongOk t base l c rv rp e) :
    rv.toNat / 256 < 2 ^ (l - 8) := by
  rw [h.rv]
  have hst : revBits l c < 2 ^ l := revBits_lt l c
  have hp : 2 ^ l = 256 * 2 ^ (l - 8) := by
    rw [show (256 : Nat) = 2 ^ 8 from rfl, ← Nat.pow_add]
    congr 1
    have := h.long
    omega
  exact Nat.div_lt_of_lt_mul (by rw [← hp]; exact hst)

private theorem long_l {t : ByteArray} {base l c : Nat} {rv rp e : UInt64} (h : LongOk t base l c rv rp e) {lU : UInt64}
    (hl : lU.toNat = l) : (lU - 8).toNat = l - 8 := by
  have := h.long
  rw [u64_sub' (by rw [hl, show (8 : UInt64).toNat = 8 from rfl]; omega), hl]
  rfl

/-- The slots of a long code word whose root slot has a sub-table are in the array. -/
private theorem long_sub {t : ByteArray} {base l c : Nat} {rv rp e : UInt64} (h : LongOk t base l c rv rp e)
    (hz : ¬ e &&& 15 = 0) {lU baseU : UInt64} (hl : lU.toNat = l) (hb : baseU.toNat = base) :
    ∀ k, k < (1 <<< ((e &&& 15) - lU)).toNat →
      2 * ((baseU + (e >>> 4) + (rv >>> 8)).toNat + k * (1 <<< (lU - 8)).toNat) + 1 < t.size := by
  have h32 := h.ok.h32
  have he1 : (e &&& 15).toNat = (slotAt t (base + rootOf l c)).1 := by
    rw [and15, h.e]
    rfl
  have he2 : (e >>> 4).toNat = (slotAt t (base + rootOf l c)).2 := by
    rw [u64_shr (by decide), h.e]
    rfl
  have hnz : (slotAt t (base + rootOf l c)).1 ≠ 0 := by
    rw [← he1]
    intro e0
    exact hz (UInt64.toNat_inj.mp (by rw [e0]; rfl))
  obtain ⟨hge, hin⟩ := h.ok.sub h.long hnz
  generalize slotAt t (base + rootOf l c) = E at he1 he2 hnz hge hin
  have hE15 : E.1 < 16 := by
    rw [← he1, and15]
    omega
  have hlen := h.ok.len
  have hl8 := h.long
  have hrv := long_rev h
  have hsub : ((e &&& 15) - lU).toNat = E.1 - l := by
    rw [u64_sub' (by rw [he1, hl]; exact hge), he1, hl]
  have hs1 : (1 <<< ((e &&& 15) - lU)).toNat = 2 ^ (E.1 - l) := by
    rw [one_shl (by rw [hsub]; omega), hsub]
  have hs2 : (1 <<< (lU - 8)).toNat = 2 ^ (l - 8) := by
    rw [one_shl (by rw [long_l h hl]; omega), long_l h hl]
  have hrv8 : (rv >>> 8).toNat = rv.toNat / 256 := by
    rw [u64_shr (by decide)]
    rfl
  have := Nat.two_pow_pos (E.1 - 8)
  have : 2 ^ (l - 8) ≤ 2 ^ 7 := Nat.pow_le_pow_right (by decide) (by omega)
  have hpos : (baseU + (e >>> 4) + (rv >>> 8)).toNat = base + E.2 + rv.toNat / 256 := by
    rw [u64_add' (by rw [u64_add' (by rw [hb, he2]; omega), hb, he2, hrv8]; omega), u64_add' (by rw [hb, he2]; omega), hb, he2,
      hrv8]
  intro k hk
  rw [hs1] at hk
  rw [hpos, hs2]
  have := run_lt (l := l - 8) (W := E.1 - 8) (by omega) hrv (k := k) (by rw [show E.1 - 8 - (l - 8) = E.1 - l by omega]; exact hk)
  omega

/-- The slot of a long code word that opens its root's sub-table is in the grown array. -/
private theorem long_open {t : ByteArray} {base l c : Nat} {rv rp e : UInt64} (h : LongOk t base l c rv rp e) {lU : UInt64}
    (hl : lU.toNat = l) :
    ∀ k, k < (1 : UInt64).toNat →
      2 * (((t.size.toUInt64 >>> 1) + (rv >>> 8)).toNat + k * (1 <<< (lU - 8)).toNat) + 1 <
        (zeroExtend t (2 <<< (lU - 8)).toNat).size := by
  have h32 := h.ok.h32
  have hl8 := h.long
  have hlen := h.ok.len
  have hrv := long_rev h
  have hs : (2 <<< (lU - 8)).toNat = 2 * 2 ^ (l - 8) := by
    rw [two_shl (by rw [long_l h hl]; omega), long_l h hl]
  have hhalf : (t.size.toUInt64 >>> 1).toNat = t.size / 2 := by
    rw [u64_shr (by decide), Nat.toUInt64_eq, u64_lit (by omega)]
    rfl
  have hrv8 : (rv >>> 8).toNat = rv.toNat / 256 := by
    rw [u64_shr (by decide)]
    rfl
  have : 2 ^ (l - 8) ≤ 2 ^ 7 := Nat.pow_le_pow_right (by decide) (by omega)
  intro k hk
  have hk0 : k = 0 := by
    have : k < 1 := hk
    omega
  subst hk0
  rw [size_zeroExtend, hs, u64_add' (by rw [hhalf, hrv8]; omega), hhalf, hrv8]
  omega

/-- Opening a sub-table grows the array by at most 256 bytes. -/
private theorem long_size {t : ByteArray} {base l c : Nat} {rv rp e : UInt64} (h : LongOk t base l c rv rp e)
    {lU : UInt64} (hl : lU.toNat = l) : (zeroExtend t (2 <<< (lU - 8)).toNat).size < 2 ^ 32 := by
  have h32 := h.ok.h32
  have hl8 := h.long
  have hlen := h.ok.len
  have : 2 ^ (l - 8) ≤ 2 ^ 7 := Nat.pow_le_pow_right (by decide) (by omega)
  rw [size_zeroExtend, two_shl (by rw [long_l h hl]; omega), long_l h hl]
  omega

/-- Writes a long code word's slots, given its root slot's number `e`: opening the root's sub-table at the end of the
array if it has none. -/
@[inline] def longFast (baseU : UInt64) (t : ByteArray) (s lU : UInt64) (rv rp e : UInt64) {base l c : Nat}
    (h : LongOk t base l c rv rp e) (hl : lU.toNat = l) (hb : baseU.toNat = base) : ByteArray :=
  if hz : e &&& 15 = 0 then
    let half := t.size.toUInt64 >>> 1
    let t1 := zeroExtend t (2 <<< (lU - 8)).toNat
    fillRun (lU + (s <<< 4)) (1 <<< (lU - 8))
      (putSlot t1 rp (lU + ((half - baseU) <<< 4)) (by
        rw [size_zeroExtend]
        have := long_root h
        omega) (by exact long_size h hl))
      (half + (rv >>> 8)) 1
      (by rw [size_putSlot]; exact long_size h hl)
      (by
        intro k hk
        rw [size_putSlot]
        exact long_open h hl k hk)
  else
    fillRun (lU + (s <<< 4)) (1 <<< (lU - 8)) t (baseU + (e >>> 4) + (rv >>> 8)) (1 <<< ((e &&& 15) - lU))
      (by have := h.ok.h32; omega) (by exact long_sub h hz hl hb)

/-- The slots of a short code word are root slots. -/
private theorem short_in {t : ByteArray} {base l c : Nat} (h : BuildOk t base l c) (hl8 : l ≤ 8) {lU cU baseU : UInt64}
    (hl : lU.toNat = l) (hc : cU.toNat = c) (hb : baseU.toNat = base) :
    ∀ k, k < (1 <<< (8 - lU)).toNat → 2 * ((baseU + revFast lU cU).toNat + k * (1 <<< lU).toNat) + 1 < t.size := by
  have h32 := h.h32
  have hroot := h.root
  have hlen := h.len
  have hrv : (revFast lU cU).toNat = revBits l c := by
    rw [revFast_toNat (by omega) (by rw [hl, hc]; exact h.code), hl, hc]
  have h8 : (8 - lU).toNat = 8 - l := by
    rw [u64_sub' (by rw [hl, show (8 : UInt64).toNat = 8 from rfl]; omega), hl]
    rfl
  have hs1 : (1 <<< (8 - lU)).toNat = 2 ^ (8 - l) := by
    rw [one_shl (by rw [h8]; omega), h8]
  have hs2 : (1 <<< lU).toNat = 2 ^ l := by
    rw [one_shl (by omega), hl]
  have hst : revBits l c < 2 ^ l := revBits_lt l c
  intro k hk
  rw [hs1] at hk
  rw [u64_add' (by rw [hb, hrv]; have := revBits_lt l c; have : 2 ^ l ≤ 2 ^ 15 := Nat.pow_le_pow_right (by decide) hlen.2; omega),
    hb, hrv, hs2]
  have := run_lt (l := l) (W := 8) hl8 hst (k := k) hk
  omega

/-- Writes a code word's slots, longest code words first. -/
@[inline] def stepFast (baseU : UInt64) (t : ByteArray) (s lU cU : UInt64) {base l c : Nat} (h : BuildOk t base l c)
    (hl : lU.toNat = l) (hc : cU.toNat = c) (hb : baseU.toNat = base) : ByteArray :=
  let rv := revFast lU cU
  if hl8 : lU ≤ 8 then
    fillRun (lU + (s <<< 4)) (1 <<< lU) t (baseU + rv) (1 <<< (8 - lU)) (by have := h.h32; omega)
      (by exact short_in h (by rw [← hl]; exact UInt64.le_iff_toNat_le.mp hl8) hl hc hb)
  else
    let rp := baseU + (rv &&& 255)
    have hlong : LongOk t base l c rv rp (getSlot t rp (by
        have hrv : rv.toNat = revBits l c := by
          rw [revFast_toNat (by have := h.len; omega) (by rw [hl, hc]; exact h.code), hl, hc]
        have hrp : rp.toNat = base + rootOf l c := by
          show (baseU + (rv &&& 255)).toNat = _
          rw [u64_add' (by rw [and255, hb]; have := h.h32; have := h.root; omega), and255, hb, hrv]
          rfl
        have := h.root
        have := rootOf_lt l c
        rw [hrp]
        omega) (by have := h.h32; omega)) := by
      have hrv : rv.toNat = revBits l c := by
        rw [revFast_toNat (by have := h.len; omega) (by rw [hl, hc]; exact h.code), hl, hc]
      have hrp : rp.toNat = base + rootOf l c := by
        show (baseU + (rv &&& 255)).toNat = _
        rw [u64_add' (by rw [and255, hb]; have := h.h32; have := h.root; omega), and255, hb, hrv]
        rfl
      refine ⟨h, by rw [← hl]; exact Nat.lt_of_not_le fun e => hl8 (UInt64.le_iff_toNat_le.mpr e), hrv, hrp, ?_⟩
      rw [getSlot_toNat, hrp]
    longFast baseU t s lU rv rp _ hlong hl hb

private theorem writeRange_congr' {bits val step step' count count' pos pos' : Nat} {t t' : ByteArray}
    (h1 : step = step') (h2 : count = count') (h3 : t = t') (h4 : pos = pos') :
    writeRange bits val step count t pos = writeRange bits val step' count' t' pos' := by
  subst h1 h2 h3 h4
  rfl

/-- A slot's number for a bit count `l` and symbol `s`. -/
private theorem slot_num {lU s : UInt64} {l : Nat} (hl : lU.toNat = l) (hl15 : l ≤ 15) (hs : s.toNat < 4096) :
    (lU + (s <<< 4)).toNat = l + 16 * s.toNat := by
  have h4 : (s <<< 4).toNat = 16 * s.toNat := by
    rw [u64_shl (by decide) (by rw [show (4 : UInt64).toNat = 4 from rfl]; omega), show (4 : UInt64).toNat = 4 from rfl]
    omega
  rw [u64_add' (by rw [hl, h4]; omega), hl, h4]

/-- `longFast` writes what `downStep` does for a long code word. -/
theorem longFast_eq {baseU : UInt64} {t : ByteArray} {s lU rv rp e : UInt64} {base l c : Nat}
    (h : LongOk t base l c rv rp e) (hl : lU.toNat = l) (hb : baseU.toNat = base) (hs : s.toNat < 4096) :
    longFast baseU t s lU rv rp e h hl hb =
      if (slotAt t (base + rootOf l c)).1 = 0 then
        writeRange l s.toNat (2 ^ (l - 8)) 1 (openSub base t (rootOf l c) l) (t.size / 2 + revBits l c / 256)
      else
        writeRange l s.toNat (2 ^ (l - 8)) (2 ^ ((slotAt t (base + rootOf l c)).1 - l)) t
          (base + (slotAt t (base + rootOf l c)).2 + revBits l c / 256) := by
  have h32 := h.ok.h32
  have hroot := h.ok.root
  have hlen := h.ok.len
  have hl8 := h.long
  have hv := slot_num hl hlen.2 hs
  have he1 : (e &&& 15).toNat = (slotAt t (base + rootOf l c)).1 := by
    rw [and15, h.e]
    rfl
  have he2 : (e >>> 4).toNat = (slotAt t (base + rootOf l c)).2 := by
    rw [u64_shr (by decide), h.e]
    rfl
  have hs2 : (1 <<< (lU - 8)).toNat = 2 ^ (l - 8) := by
    rw [one_shl (by rw [long_l h hl]; omega), long_l h hl]
  have hrv8 : (rv >>> 8).toNat = revBits l c / 256 := by
    rw [u64_shr (by decide), h.rv]
    rfl
  have hp7 : 2 ^ (l - 8) ≤ 2 ^ 7 := Nat.pow_le_pow_right (by decide) (by omega)
  have hrlt : revBits l c / 256 < 2 ^ (l - 8) := by
    have := long_rev h
    rw [h.rv] at this
    exact this
  unfold longFast
  by_cases hz : e &&& 15 = 0
  · have hz' : (slotAt t (base + rootOf l c)).1 = 0 := by
      rw [← he1, hz]
      rfl
    rw [dite_eq_left hz, ite_eq_left hz']
    dsimp only
    have hhalf : (t.size.toUInt64 >>> 1).toNat = t.size / 2 := by
      rw [u64_shr (by decide), Nat.toUInt64_eq, u64_lit (by omega)]
      rfl
    have hoff : (lU + ((t.size.toUInt64 >>> 1) - baseU) <<< 4).toNat = l + 16 * (t.size / 2 - base) := by
      have hsub : ((t.size.toUInt64 >>> 1) - baseU).toNat = t.size / 2 - base := by
        rw [u64_sub' (by rw [hhalf, hb]; omega), hhalf, hb]
      have h4 : (((t.size.toUInt64 >>> 1) - baseU) <<< 4).toNat = 16 * (t.size / 2 - base) := by
        rw [u64_shl (by decide) (by rw [hsub, show (4 : UInt64).toNat = 4 from rfl]; omega), hsub,
          show (4 : UInt64).toNat = 4 from rfl]
        omega
      rw [u64_add' (by rw [hl, h4]; omega), hl, h4]
    rw [fillRun_eq hv _ 1 _ _ _ _ _ rfl, putSlot_eq hoff]
    unfold openSub
    refine writeRange_congr' hs2 rfl ?_ ?_
    · rw [zeroExtend_zeros, two_shl (by rw [long_l h hl]; omega), long_l h hl, h.rp]
    · rw [u64_add' (by rw [hhalf, hrv8]; omega), hhalf, hrv8]
  · have hz' : (slotAt t (base + rootOf l c)).1 ≠ 0 := by
      rw [← he1]
      intro e0
      exact hz (UInt64.toNat_inj.mp (by rw [e0]; rfl))
    rw [dite_eq_right hz, ite_eq_right hz']
    obtain ⟨hge, hin⟩ := h.ok.sub hl8 hz'
    have hE15 : (slotAt t (base + rootOf l c)).1 < 16 := by
      rw [← he1, and15]
      omega
    have hsub : ((e &&& 15) - lU).toNat = (slotAt t (base + rootOf l c)).1 - l := by
      rw [u64_sub' (by rw [he1, hl]; exact hge), he1, hl]
    have hs1 : (1 <<< ((e &&& 15) - lU)).toNat = 2 ^ ((slotAt t (base + rootOf l c)).1 - l) := by
      rw [one_shl (by rw [hsub]; omega), hsub]
    have := Nat.two_pow_pos ((slotAt t (base + rootOf l c)).1 - 8)
    rw [fillRun_eq hv _ _ _ _ _ _ _ hs1]
    refine writeRange_congr' hs2 rfl rfl ?_
    rw [u64_add' (by rw [u64_add' (by rw [hb, he2]; omega), hb, he2, hrv8]; omega), u64_add' (by rw [hb, he2]; omega), hb, he2,
      hrv8]

/-- `stepFast` writes what `downStep` does. -/
theorem stepFast_eq {baseU : UInt64} {t : ByteArray} {s lU cU : UInt64} {base l c : Nat} (h : BuildOk t base l c)
    (hl : lU.toNat = l) (hc : cU.toNat = c) (hb : baseU.toNat = base) (hs : s.toNat < 4096) :
    stepFast baseU t s lU cU h hl hc hb = downStep base t s.toNat l c := by
  have hlen := h.len
  have h32 := h.h32
  have hroot := h.root
  have hv := slot_num hl hlen.2 hs
  have hrv : (revFast lU cU).toNat = revBits l c := by
    rw [revFast_toNat (by omega) (by rw [hl, hc]; exact h.code), hl, hc]
  unfold stepFast downStep
  by_cases hl8 : l ≤ 8
  · have hl8U : lU ≤ 8 := UInt64.le_iff_toNat_le.mpr (by rw [hl]; exact hl8)
    rw [dite_eq_left hl8U, ite_eq_left hl8]
    have h8 : (8 - lU).toNat = 8 - l := by
      rw [u64_sub' (by rw [hl, show (8 : UInt64).toNat = 8 from rfl]; omega), hl]
      rfl
    have hs1 : (1 <<< (8 - lU)).toNat = 2 ^ (8 - l) := by
      rw [one_shl (by rw [h8]; omega), h8]
    have hs2 : (1 <<< lU).toNat = 2 ^ l := by
      rw [one_shl (by omega), hl]
    have : 2 ^ l ≤ 2 ^ 8 := Nat.pow_le_pow_right (by decide) hl8
    have := revBits_lt l c
    rw [fillRun_eq hv _ _ _ _ _ _ _ hs1]
    refine writeRange_congr' hs2 rfl rfl ?_
    rw [u64_add' (by rw [hb, hrv]; omega), hb, hrv]
  · have hl8U : ¬ lU ≤ 8 := fun e => hl8 (by rw [← hl]; exact UInt64.le_iff_toNat_le.mp e)
    rw [dite_eq_right hl8U, ite_eq_right hl8]
    dsimp only
    rw [longFast_eq _ hl hb hs]

/-- A step's needs hold while a table is built: the root slot of a long code word whose sub-table is open has it as
deep as the code word, in the array. -/
theorem DownInv.stepOk {lens : List Nat} (hC : Complete (.canonical lens)) {t0 t : ByteArray} {base : Nat}
    {done ops : List Nat} {o : Nat → Nat} (h : DownInv lens t0 base done t ops o) (hlen : lens.length ≤ 704)
    (hbase : 2 * base + 2672 < 2 ^ 32) {s l c : Nat} (hs : lens[s]? = some l) (h0 : l ≠ 0) (hc : code lens s = some c) :
    BuildOk t base l c := by
  have hl15 : l ≤ 15 := hC.1 l (List.mem_of_getElem? hs)
  have hsize := h.size
  have h1 := opSum_le ops (depths lens) 256
  have h2 := offSum_le hC
  have h3 := longCount_le lens
  refine ⟨by omega, by omega, ⟨by omega, hl15⟩, code_lt_two_pow (Nat.le_of_eq hC.2) hs h0 hl15 hc, ?_⟩
  · intro hl8 hz
    have hdge := (depths_spec hC.1).2.2.2 s l c ⟨hs, hl8, hc⟩
    have hm : rootOf l c ∈ ops := Classical.byContradiction fun hn => hz (h.empty _ (rootOf_lt l c) hn (by omega))
    obtain ⟨_, _, h3', h4⟩ := h.opsOk _ hm
    rw [h3']
    dsimp only
    refine ⟨by omega, ?_⟩
    rw [show 8 + (depths lens).getD (rootOf l c) 0 - 8 = (depths lens).getD (rootOf l c) 0 by omega]
    omega

/-! ### The symbols of each length -/

/-- `next` links `v` to the symbols `ss`: each symbol `s` as `s + 1`, then `next`'s 16-bit value at `s` links the rest,
and 0 ends them. -/
def ChainIs (next : ByteArray) : Nat → List Nat → Prop
  | v, [] => v = 0
  | v, s :: ss => v = s + 1 ∧ 2 * s + 1 < next.size ∧ ChainIs next (u16At next s) ss

/-- `head`'s 16-bit value at each length from 1 to 15 links that length's symbols, in decreasing order. -/
def ListsIs (head next : ByteArray) (lens : List Nat) : Prop :=
  32 ≤ head.size ∧ ∀ l, 1 ≤ l → l ≤ 15 → ChainIs next (u16At head l) (symsOf lens l).reverse

theorem slotNum_eq_u16At (t : ByteArray) (i : Nat) : slotNum t i = u16At t i := rfl

/-- A 16-bit value written with `putSlot` reads back, cut to 16 bits, and the others stay. -/
theorem u16At_putSlot' {t : ByteArray} {pos v : UInt64} {h : 2 * pos.toNat + 1 < t.size} {h32 : t.size < 2 ^ 32} (j : Nat) :
    u16At (putSlot t pos v h h32) j = if j = pos.toNat then v.toNat % 65536 else u16At t j := by
  have e0 := slot2 h32 h (j := 0) (by decide)
  have e1 := slot2 h32 h (j := 1) (by decide)
  have h0' : (pos * 2 + 0).toUSize.toNat < t.size := by rw [e0]; show 2 * pos.toNat + 0 < _; omega
  have h1' : (pos * 2 + 1).toUSize.toNat < (t.uset (pos * 2 + 0).toUSize v.toUInt8 h0').size := by
    rw [size_uset', e1]
    show 2 * pos.toNat + 1 < _
    omega
  unfold putSlot u16At
  rw [show (0 : UInt64).toNat = 0 from rfl] at e0
  rw [show (1 : UInt64).toNat = 1 from rfl] at e1
  by_cases hj : j = pos.toNat
  · subst hj
    rw [ite_eq_left rfl]
    have g1 := uset_get_same (t := t.uset (pos * 2 + 0).toUSize v.toUInt8 h0') (v := (v >>> 8).toUInt8) h1'
    rw [e1] at g1
    have g0 : ((t.uset (pos * 2 + 0).toUSize v.toUInt8 h0').uset (pos * 2 + 1).toUSize (v >>> 8).toUInt8 h1').data[2 * pos.toNat]?.getD 0 =
        v.toUInt8 := by
      rw [uset_get_ne h1' (by rw [e1]; omega)]
      have := uset_get_same (t := t) (v := v.toUInt8) h0'
      rw [e0, Nat.add_zero] at this
      rw [Nat.add_zero] at e0
      exact this
    rw [g0, g1]
    have e2 : (v >>> 8).toUInt8.toNat = v.toNat / 256 % 256 := by
      rw [UInt64.toNat_toUInt8, u64_shr (by decide)]
      rfl
    rw [e2, UInt64.toNat_toUInt8]
    omega
  · rw [ite_eq_right hj, uset_get_ne h1' (by rw [e1]; omega), uset_get_ne h1' (by rw [e1]; omega),
      uset_get_ne h0' (by rw [e0]; omega), uset_get_ne h0' (by rw [e0]; omega)]
/-- A chain stays when `next` keeps its links at the chain's symbols. -/
theorem ChainIs.frame' {next next' : ByteArray} :
    ∀ {v : Nat} {ss : List Nat}, ChainIs next v ss → (∀ s ∈ ss, u16At next' s = u16At next s ∧ 2 * s + 1 < next'.size) →
    ChainIs next' v ss
  | _, [], h, _ => h
  | _, s :: ss, ⟨h1, _, h3⟩, hn => by
    obtain ⟨e, hs⟩ := hn s List.mem_cons_self
    refine ⟨h1, hs, ?_⟩
    rw [e]
    exact ChainIs.frame' h3 fun s' hs' => hn s' (List.mem_cons_of_mem _ hs')

/-- The symbols of a length, with one more length after them. -/
theorem symsOf_push (L : List Nat) (x l : Nat) :
    symsOf (L ++ [x]) l = symsOf L l ++ (if x = l then [L.length] else []) := by
  unfold symsOf
  rw [List.length_append, List.length_singleton, List.range_succ, List.filter_append]
  congr 1
  · apply List.filter_congr
    intro s hs
    rw [List.getElem?_append_left (List.mem_range.mp hs)]
  · by_cases he : x = l <;> simp [he]

/-- The symbols of a length, with a run of `n` more of one length after them. -/
theorem symsOf_run (L : List Nat) (x l : Nat) : ∀ n,
    symsOf (L ++ List.replicate n x) l = symsOf L l ++ (if x = l then List.range' L.length n else [])
  | 0 => by simp
  | n + 1 => by
    rw [List.replicate_succ', ← List.append_assoc, symsOf_push, symsOf_run L x l n, List.length_append, List.length_replicate]
    by_cases he : x = l
    · simp only [he, ↓reduceIte, List.append_assoc]
      rw [List.range'_1_concat]
    · simp [he]

/-- With every length's list empty, the lists are those of no symbols. -/
theorem ListsIs.empty {head next : ByteArray} (hs : 32 ≤ head.size) (hz : ∀ l, 1 ≤ l → l ≤ 15 → u16At head l = 0) :
    ListsIs head next [] := by
  refine ⟨hs, fun l h1 h2 => ?_⟩
  show ChainIs next (u16At head l) (symsOf [] l).reverse
  have : symsOf [] l = [] := rfl
  rw [this, hz l h1 h2]
  rfl

/-- One more symbol of length 0: the lists stay. -/
theorem ListsIs.zero {head next : ByteArray} {L : List Nat} (h : ListsIs head next L) : ListsIs head next (L ++ [0]) := by
  refine ⟨h.1, fun l h1 h2 => ?_⟩
  rw [symsOf_push, ite_eq_right (by omega), List.append_nil]
  exact h.2 l h1 h2

/-- One more symbol of length 0, as many times as wanted. -/
theorem ListsIs.zeros {head next : ByteArray} {L : List Nat} (h : ListsIs head next L) (n : Nat) :
    ListsIs head next (L ++ List.replicate n 0) := by
  refine ⟨h.1, fun l h1 h2 => ?_⟩
  rw [symsOf_run, ite_eq_right (by omega), List.append_nil]
  exact h.2 l h1 h2

/-- A run of `n` symbols of length `l` after the others: in front of length `l`'s list, each linked to the one before. -/
theorem ListsIs.run {head next head' next' : ByteArray} {L : List Nat} {l n : Nat} (h : ListsIs head next L)
    (hroom : 2 * (L.length + n) ≤ next'.size)
    (hn : ∀ j, j < L.length → u16At next' j = u16At next j)
    (hrun : ∀ j, L.length ≤ j → j < L.length + n → u16At next' j = if j = L.length then u16At head l else j)
    (hh : ∀ j, j ≠ l → u16At head' j = u16At head j) (hhl : u16At head' l = if n = 0 then u16At head l else L.length + n)
    (hhs : 32 ≤ head'.size) : ListsIs head' next' (L ++ List.replicate n l) := by
  have hsym : ∀ l', ∀ s ∈ symsOf L l', s < L.length := fun l' s hs =>
    (List.getElem?_eq_some_iff.mp (mem_symsOf.mp hs)).1
  have hold : ∀ l', 1 ≤ l' → l' ≤ 15 → ChainIs next' (u16At head l') (symsOf L l').reverse := by
    intro l' h1 h2
    refine ChainIs.frame' (h.2 l' h1 h2) fun s hs => ?_
    have hs' := hsym l' s (List.mem_reverse.mp hs)
    exact ⟨hn s hs', by omega⟩
  refine ⟨hhs, fun l' h1 h2 => ?_⟩
  rw [symsOf_run]
  by_cases he : l = l'
  · subst he
    rw [ite_eq_left rfl, List.reverse_append, hhl]
    -- The run, from its last symbol down to its first, then the old list.
    have key : ∀ m, m ≤ n → ChainIs next' (if m = 0 then u16At head l else L.length + m)
        ((List.range' L.length m).reverse ++ (symsOf L l).reverse) := by
      intro m
      induction m with
      | zero => intro _; simpa using hold l h1 h2
      | succ m ih =>
        intro hm
        rw [ite_eq_right (by omega), List.range'_1_concat, List.reverse_append, List.reverse_singleton,
          List.singleton_append, List.cons_append]
        refine ⟨by omega, by omega, ?_⟩
        rw [hrun _ (by omega) (by omega)]
        have := ih (by omega)
        by_cases hm0 : m = 0
        · subst hm0
          simpa using this
        · rw [ite_eq_right (by omega)]
          rw [ite_eq_right hm0] at this
          exact this
    exact key n (Nat.le_refl _)
  · rw [ite_eq_right he, List.append_nil, hh l' (Ne.symm he)]
    exact hold l' h1 h2

/-- Every length's list emptied: 32 zero bytes over `head`, written in place. -/
@[inline] def resetHead (head : ByteArray) : ByteArray := zeroBlock.copySlice 0 head 0 32 true

/-- `resetHead_data` for any array of `N ≥ 32` zeros, as for `zeros_copy`. -/
private theorem zeros_over (z head : ByteArray) {N : Nat} (hz : z.data = Array.replicate N 0) (hN : 32 ≤ N)
    (h : head.size = 32) : (z.copySlice 0 head 0 32 true).data = Array.replicate 32 0 := by
  have hs : head.data.size = 32 := h
  simp only [ByteArray.copySlice, hz]
  simp [hs, Array.extract_replicate, Nat.min_eq_left hN]

theorem resetHead_data {head : ByteArray} (h : head.size = 32) : (resetHead head).data = Array.replicate 32 0 :=
  zeros_over zeroBlock head zeroBlock_data (by decide) h

theorem resetHead_size {head : ByteArray} (h : head.size = 32) : (resetHead head).size = 32 := by
  show (resetHead head).data.size = 32
  rw [resetHead_data h]
  simp

theorem resetHead_lists {head : ByteArray} (h : head.size = 32) (next : ByteArray) : ListsIs (resetHead head) next [] := by
  refine ListsIs.empty (by rw [resetHead_size h]; exact Nat.le_refl _) fun l _ _ => ?_
  unfold u16At
  rw [resetHead_data h, Array.getElem?_replicate, Array.getElem?_replicate]
  split <;> split <;> rfl

/-- The lists' arrays a state holds while its own are taken out. -/
def headNone : ByteArray := zeroBytes 32
def nextNone : ByteArray := zeroBytes 1408

theorem headNone_size : headNone.size = 32 := zeroBytes_size (by decide)
theorem nextNone_size : nextNone.size = 1408 := zeroBytes_size (by decide)

attribute [irreducible] headNone nextNone

/-- The symbols of a length increase. -/
theorem symsOf_lt {lens : List Nat} {l i j : Nat} (hij : i < j) (hj : j < (symsOf lens l).length) :
    (symsOf lens l)[i] < (symsOf lens l)[j] :=
  List.pairwise_iff_getElem.mp (List.pairwise_lt_range.filter _ : (symsOf lens l).Pairwise (· < ·)) i j
    (Nat.lt_trans hij hj) hj hij

/-- Where the builder's walk is, for a code with lengths `lens` whose table started from `t0`: at length `l`, with the
symbols of that length from the `k`th last on still to write, linked from `v`, and `e` the code above the next one's. -/
structure WalkAt (lens : List Nat) (t0 head next : ByteArray) (base : Nat) (t : ByteArray) (l v e k : Nat) : Prop where
  complete : Complete (.canonical lens)
  small : lens.length ≤ 704
  lists : ListsIs head next lens
  hsz : head.size < 2 ^ 32
  nsz : next.size < 2 ^ 32
  room : 2 * base + 2672 < 2 ^ 32
  lrange : 1 ≤ l ∧ l ≤ 15
  kle : k ≤ (symsOf lens l).length
  chain : ChainIs next v ((symsOf lens l).reverse.drop k)
  ecode : e = nextCode lens l + ((symsOf lens l).length - k)
  inv : ∃ done ops o, DownInv lens t0 base done t ops o ∧ (∀ s' l', lens[s']? = some l' → l < l' → s' ∈ done) ∧
    ∀ i (hi : i < (symsOf lens l).length), (symsOf lens l).length - k ≤ i → (symsOf lens l)[i] ∈ done

/-- The walk's next symbol, when the link isn't 0. -/
theorem WalkAt.next_sym {lens : List Nat} {t0 head next t : ByteArray} {base l v e k : Nat}
    (h : WalkAt lens t0 head next base t l v e k) (hv : v ≠ 0) :
    ∃ (hk : k < (symsOf lens l).length),
      (symsOf lens l).reverse.drop k = (symsOf lens l)[(symsOf lens l).length - 1 - k] :: (symsOf lens l).reverse.drop (k + 1) ∧
      v = (symsOf lens l)[(symsOf lens l).length - 1 - k] + 1 ∧
      2 * (symsOf lens l)[(symsOf lens l).length - 1 - k] + 1 < next.size ∧
      ChainIs next (u16At next (symsOf lens l)[(symsOf lens l).length - 1 - k]) ((symsOf lens l).reverse.drop (k + 1)) := by
  have hk : k < (symsOf lens l).length := by
    refine Nat.lt_of_not_le fun hle => hv ?_
    have hd : (symsOf lens l).reverse.drop k = [] := List.drop_eq_nil_of_le (by rw [List.length_reverse]; exact hle)
    have := h.chain
    rw [hd] at this
    exact this
  have hk' : k < (symsOf lens l).reverse.length := by rw [List.length_reverse]; exact hk
  have hd : (symsOf lens l).reverse.drop k =
      (symsOf lens l)[(symsOf lens l).length - 1 - k] :: (symsOf lens l).reverse.drop (k + 1) := by
    rw [List.drop_eq_getElem_cons hk', List.getElem_reverse]
  have hc := h.chain
  rw [hd] at hc
  exact ⟨hk, hd, hc.1, hc.2.1, hc.2.2⟩

/-- A link is a symbol plus one, below 705. -/
theorem chain_le {next : ByteArray} {lens : List Nat} {l : Nat} (hlen : lens.length ≤ 704) :
    ∀ (v : Nat) (ss : List Nat), (∀ s ∈ ss, s ∈ symsOf lens l) → ChainIs next v ss → v ≤ 704
  | v, [], _, hc => by
    have : v = 0 := hc
    omega
  | v, s :: ss, hm, hc => by
    have hs := (List.getElem?_eq_some_iff.mp (mem_symsOf.mp (hm s List.mem_cons_self))).1
    have : v = s + 1 := hc.1
    omega

theorem mem_drop_rev {lens : List Nat} {l k s : Nat} (h : s ∈ (symsOf lens l).reverse.drop k) :
    s ∈ symsOf lens l :=
  List.mem_reverse.mp (List.mem_of_mem_drop h)

/-- The walk's next link is below its link. -/
theorem WalkAt.link_lt {lens : List Nat} {t0 head next t : ByteArray} {base l v e k : Nat}
    (h : WalkAt lens t0 head next base t l v e k) (hv : v ≠ 0) :
    ∃ s, v = s + 1 ∧ 2 * s + 1 < next.size ∧ u16At next s < v := by
  obtain ⟨hk, hd, hvs, hin, hch⟩ := h.next_sym hv
  refine ⟨_, hvs, hin, ?_⟩
  by_cases hk1 : k + 1 < (symsOf lens l).length
  · have hk1' : k + 1 < (symsOf lens l).reverse.length := by rw [List.length_reverse]; exact hk1
    rw [List.drop_eq_getElem_cons hk1', List.getElem_reverse] at hch
    have hlt := symsOf_lt (lens := lens) (l := l) (i := (symsOf lens l).length - 1 - (k + 1))
      (j := (symsOf lens l).length - 1 - k) (by omega) (by omega)
    rw [hch.1, hvs]
    omega
  · have hd1 : (symsOf lens l).reverse.drop (k + 1) = [] :=
      List.drop_eq_nil_of_le (by rw [List.length_reverse]; omega)
    rw [hd1] at hch
    have : u16At next (symsOf lens l)[(symsOf lens l).length - 1 - k] = 0 := hch
    omega

/-- The walk's step needs hold. -/
theorem WalkAt.stepOk {lens : List Nat} {t0 head next t : ByteArray} {base l v e k : Nat}
    (h : WalkAt lens t0 head next base t l v e k) (hv : v ≠ 0) : BuildOk t base l (e - 1) := by
  obtain ⟨hk, _, _, _, _⟩ := h.next_sym hv
  obtain ⟨done, ops, o, hinv, _, _⟩ := h.inv
  obtain ⟨hg, hc⟩ := code_symsOf (lens := lens) (l := l) (k := (symsOf lens l).length - 1 - k) (by omega)
    (by have := h.lrange; omega)
  have he : e - 1 = nextCode lens l + ((symsOf lens l).length - 1 - k) := by
    have := h.ecode
    omega
  rw [he]
  exact hinv.stepOk h.complete h.small h.room hg (by have := h.lrange; omega) hc

/-- A walk step keeps the walk's place. -/
theorem WalkAt.step {lens : List Nat} {t0 head next t : ByteArray} {base l v e k : Nat}
    (h : WalkAt lens t0 head next base t l v e k) (hv : v ≠ 0) :
    WalkAt lens t0 head next base (downStep base t (v - 1) l (e - 1)) l (u16At next (v - 1)) (e - 1) (k + 1) := by
  obtain ⟨hk, _, hvs, _, hch⟩ := h.next_sym hv
  obtain ⟨done, ops, o, hinv, hlong, hcov⟩ := h.inv
  have hl0 : l ≠ 0 := by have := h.lrange; omega
  obtain ⟨hg, hc⟩ := code_symsOf (lens := lens) (l := l) (k := (symsOf lens l).length - 1 - k) (by omega) hl0
  have he : e - 1 = nextCode lens l + ((symsOf lens l).length - 1 - k) := by
    have := h.ecode
    omega
  have hs : v - 1 = (symsOf lens l)[(symsOf lens l).length - 1 - k] := by omega
  obtain ⟨ops', o', hinv'⟩ := hinv.step h.complete h.small hg hl0 hc hlong
  refine ⟨h.complete, h.small, h.lists, h.hsz, h.nsz, h.room, h.lrange, hk, by rw [hs]; exact hch,
    by have := h.ecode; omega,
    ⟨_, ops', o', by rw [hs, he]; exact hinv', fun s' l' hg' hl' => List.mem_cons_of_mem _ (hlong s' l' hg' hl'), ?_⟩⟩
  intro i hi hle
  by_cases hei : i = (symsOf lens l).length - 1 - k
  · subst hei
    exact List.mem_cons_self
  · exact List.mem_cons_of_mem _ (hcov i hi (by omega))

/-- At the end of a length's links, the walk goes on to the next shorter length. -/
theorem WalkAt.down {lens : List Nat} {t0 head next t : ByteArray} {base l v e k : Nat}
    (h : WalkAt lens t0 head next base t l v e k) (hv : v = 0) (hl : 1 < l) :
    WalkAt lens t0 head next base t (l - 1) (u16At head (l - 1)) (e / 2) 0 := by
  have hkk : k = (symsOf lens l).length := by
    refine Nat.le_antisymm h.kle (Nat.le_of_not_lt fun hlt => ?_)
    have hk' : k < (symsOf lens l).reverse.length := by rw [List.length_reverse]; exact hlt
    have := h.chain
    rw [List.drop_eq_getElem_cons hk'] at this
    have : v = _ := this.1
    omega
  obtain ⟨done, ops, o, hinv, hlong, hcov⟩ := h.inv
  have hl1 : l - 1 + 1 = l := by omega
  have hlen := length_symsOf (lens := lens) (l := l) (by omega)
  have hlen' := length_symsOf (lens := lens) (l := l - 1) (by omega)
  refine ⟨h.complete, h.small, h.lists, h.hsz, h.nsz, h.room, ⟨by omega, by have := h.lrange; omega⟩, Nat.zero_le _,
    ?_, ?_, ⟨done, ops, o, hinv, ?_, fun i hi hle => absurd hle (by omega)⟩⟩
  · rw [List.drop_zero]
    exact h.lists.2 (l - 1) (by omega) (by have := h.lrange; omega)
  · have he := h.ecode
    rw [hkk, Nat.sub_self, Nat.add_zero] at he
    rw [he, ← hl1, nextCode_half, hl1, Nat.sub_zero, hlen']
  · intro s' l' hg' hl'
    by_cases he : l' = l
    · subst he
      obtain ⟨i, hi, e'⟩ := List.getElem_of_mem (mem_symsOf.mpr hg')
      exact e' ▸ hcov i hi (by omega)
    · exact hlong s' l' hg' (by omega)

/-! ### The walk in fixed-width values -/

section Walk

variable {head next t : ByteArray} {baseU lU v e : UInt64}

private theorem v_ne {v : UInt64} (hv : ¬ v = 0) : v.toNat ≠ 0 := fun e => hv (UInt64.toNat_inj.mp (by rw [e]; rfl))

private theorem sub1 {v : UInt64} (hv : v.toNat ≠ 0) : (v - 1).toNat = v.toNat - 1 :=
  u64_sub' (by rw [show (1 : UInt64).toNat = 1 from rfl]; omega)

private theorem lU_gt (hl : ¬ lU ≤ 1) : 1 < lU.toNat :=
  Nat.lt_of_not_le fun e => hl (UInt64.le_iff_toNat_le.mpr e)

theorem walk_hsz (h : ∃ lens t0 k, WalkAt lens t0 head next baseU.toNat t lU.toNat v.toNat e.toNat k) :
    head.size < 2 ^ 32 := by
  obtain ⟨_, _, _, hw⟩ := h
  exact hw.hsz

theorem walk_nsz (h : ∃ lens t0 k, WalkAt lens t0 head next baseU.toNat t lU.toNat v.toNat e.toNat k) :
    next.size < 2 ^ 32 := by
  obtain ⟨_, _, _, hw⟩ := h
  exact hw.nsz

theorem walk_head (h : ∃ lens t0 k, WalkAt lens t0 head next baseU.toNat t lU.toNat v.toNat e.toNat k)
    (hl : ¬ lU ≤ 1) : 2 * (lU - 1).toNat + 1 < head.size := by
  obtain ⟨_, _, _, hw⟩ := h
  have := hw.lrange
  have := hw.lists.1
  have := lU_gt hl
  rw [sub1 (by omega)]
  omega

theorem walk_link (h : ∃ lens t0 k, WalkAt lens t0 head next baseU.toNat t lU.toNat v.toNat e.toNat k)
    (hv : ¬ v = 0) : 2 * (v - 1).toNat + 1 < next.size := by
  obtain ⟨_, _, _, hw⟩ := h
  obtain ⟨s, hs, hin, _⟩ := hw.link_lt (v_ne hv)
  rw [sub1 (v_ne hv), hs, Nat.add_sub_cancel]
  exact hin

theorem walk_ok (h : ∃ lens t0 k, WalkAt lens t0 head next baseU.toNat t lU.toNat v.toNat e.toNat k)
    (hv : ¬ v = 0) : BuildOk t baseU.toNat lU.toNat (e - 1).toNat := by
  obtain ⟨_, _, _, hw⟩ := h
  obtain ⟨hk, _⟩ := hw.next_sym (v_ne hv)
  have he : e.toNat ≠ 0 := by
    have := hw.ecode
    omega
  rw [sub1 he]
  exact hw.stepOk (v_ne hv)

theorem walk_down (h : ∃ lens t0 k, WalkAt lens t0 head next baseU.toNat t lU.toNat v.toNat e.toNat k)
    (hv : v = 0) (hl : ¬ lU ≤ 1) :
    ∃ lens t0 k, WalkAt lens t0 head next baseU.toNat t (lU - 1).toNat
      (getSlot head (lU - 1) (walk_head h hl) (walk_hsz h)).toNat (e >>> 1).toNat k := by
  obtain ⟨lens, t0, k, hw⟩ := h
  refine ⟨lens, t0, 0, ?_⟩
  have h1 := lU_gt hl
  have hd := hw.down (by rw [hv]; rfl) h1
  rw [getSlot_toNat, slotNum_eq_u16At, sub1 (by omega), u64_shr (by decide)]
  exact hd

theorem walk_next (h : ∃ lens t0 k, WalkAt lens t0 head next baseU.toNat t lU.toNat v.toNat e.toNat k)
    (hv : ¬ v = 0) :
    ∃ lens t0 k, WalkAt lens t0 head next baseU.toNat (stepFast baseU t (v - 1) lU (e - 1) (walk_ok h hv) rfl rfl rfl)
      lU.toNat (getSlot next (v - 1) (walk_link h hv) (walk_nsz h)).toNat (e - 1).toNat k := by
  obtain ⟨lens, t0, k, hw⟩ := h
  refine ⟨lens, t0, k + 1, ?_⟩
  have hv' := v_ne hv
  have hle := chain_le hw.small v.toNat _ (fun s hs => mem_drop_rev hs) hw.chain
  obtain ⟨hk, _⟩ := hw.next_sym hv'
  have he : e.toNat ≠ 0 := by
    have := hw.ecode
    omega
  rw [stepFast_eq _ rfl rfl rfl (by rw [sub1 hv']; omega), getSlot_toNat, slotNum_eq_u16At, sub1 hv', sub1 he]
  exact hw.step hv'

theorem walk_dec_down (h : ∃ lens t0 k, WalkAt lens t0 head next baseU.toNat t lU.toNat v.toNat e.toNat k)
    (hv : v = 0) (hl : ¬ lU ≤ 1) :
    (lU - 1).toNat * 1024 + (getSlot head (lU - 1) (walk_head h hl) (walk_hsz h)).toNat < lU.toNat * 1024 + v.toNat := by
  have hd := walk_down h hv hl
  obtain ⟨lens, _, _, hw⟩ := hd
  have hle := chain_le hw.small _ _ (fun s hs => mem_drop_rev hs) hw.chain
  have h1 := lU_gt hl
  rw [sub1 (by omega)]
  omega

theorem walk_dec_next (h : ∃ lens t0 k, WalkAt lens t0 head next baseU.toNat t lU.toNat v.toNat e.toNat k)
    (hv : ¬ v = 0) :
    lU.toNat * 1024 + (getSlot next (v - 1) (walk_link h hv) (walk_nsz h)).toNat < lU.toNat * 1024 + v.toNat := by
  obtain ⟨_, _, _, hw⟩ := h
  obtain ⟨s, hs, _, hlt⟩ := hw.link_lt (v_ne hv)
  rw [getSlot_toNat, slotNum_eq_u16At, sub1 (v_ne hv), hs, Nat.add_sub_cancel]
  omega

end Walk

/-- Writes the code words of the symbols linked from `v` at length `lU`, then those of the shorter lengths. -/
def walkFast (head next : ByteArray) (baseU : UInt64) (t : ByteArray) (lU v e : UInt64)
    (h : ∃ lens t0 k, WalkAt lens t0 head next baseU.toNat t lU.toNat v.toNat e.toNat k) : ByteArray :=
  if hv : v = 0 then
    if hl : lU ≤ 1 then t
    else
      walkFast head next baseU t (lU - 1) (getSlot head (lU - 1) (walk_head h hl) (walk_hsz h)) (e >>> 1) (walk_down h hv hl)
  else
    walkFast head next baseU (stepFast baseU t (v - 1) lU (e - 1) (walk_ok h hv) rfl rfl rfl) lU
      (getSlot next (v - 1) (walk_link h hv) (walk_nsz h)) (e - 1) (walk_next h hv)
termination_by lU.toNat * 1024 + v.toNat
decreasing_by
  · exact walk_dec_down h hv hl
  · exact walk_dec_next h hv

/-- What is left of `walkDown` from a place in it: the symbols `rest` of length `l`, from the code above `e`, then the
shorter lengths. -/
def contDown (f : ByteArray → Nat → Nat → Nat → ByteArray) (lens : List Nat) (l : Nat) (rest : List Nat) (e : Nat)
    (acc : ByteArray) : ByteArray :=
  let r := walkSyms f l rest e acc
  walkFrom f lens (l - 1) (r.2 / 2) r.1

/-- The walk writes what is left of `walkDown` from its place. -/
theorem walkFast_eq (head next : ByteArray) (baseU : UInt64) : ∀ (N : Nat) (t : ByteArray) (lU v e : UInt64)
    (h : ∃ lens t0 k, WalkAt lens t0 head next baseU.toNat t lU.toNat v.toNat e.toNat k) {lens : List Nat}
    {t0 : ByteArray} {k : Nat} (_hw : WalkAt lens t0 head next baseU.toNat t lU.toNat v.toNat e.toNat k),
    lU.toNat * 1024 + v.toNat < N →
    walkFast head next baseU t lU v e h =
      contDown (downStep baseU.toNat) lens lU.toNat ((symsOf lens lU.toNat).reverse.drop k) e.toNat t := by
  intro N
  induction N with
  | zero => intro _ _ _ _ _ _ _ _ _ hN; omega
  | succ N ih =>
    intro t lU v e h lens t0 k hw hN
    rw [walkFast]
    by_cases hv : v = 0
    · rw [dite_eq_left hv]
      have hkk : k = (symsOf lens lU.toNat).length := by
        refine Nat.le_antisymm hw.kle (Nat.le_of_not_lt fun hlt => ?_)
        have hk' : k < (symsOf lens lU.toNat).reverse.length := by rw [List.length_reverse]; exact hlt
        have := hw.chain
        rw [List.drop_eq_getElem_cons hk'] at this
        have h0 : v.toNat = _ := this.1
        rw [hv] at h0
        exact absurd h0 (by simp)
      have hd : (symsOf lens lU.toNat).reverse.drop k = [] :=
        List.drop_eq_nil_of_le (by rw [List.length_reverse]; omega)
      rw [hd]
      unfold contDown
      dsimp only [walkSyms]
      by_cases hl : lU ≤ 1
      · rw [dite_eq_left hl]
        have : lU.toNat - 1 = 0 := by
          have : lU.toNat ≤ 1 := UInt64.le_iff_toNat_le.mp hl
          omega
        rw [this]
        rfl
      · rw [dite_eq_right hl]
        have h1 := lU_gt hl
        have hw' : WalkAt lens t0 head next baseU.toNat t (lU - 1).toNat
            (getSlot head (lU - 1) (walk_head h hl) (walk_hsz h)).toNat (e >>> 1).toNat 0 := by
          rw [getSlot_toNat, slotNum_eq_u16At, sub1 (by omega), u64_shr (by decide)]
          exact hw.down (by rw [hv]; rfl) h1
        have hdec := walk_dec_down h hv hl
        have hb := Nat.lt_of_lt_of_le hdec (Nat.le_of_lt_succ hN)
        have h2 : (e >>> 1).toNat = e.toNat / 2 := by
          rw [u64_shr (by decide)]
          rfl
        rw [ih _ _ _ _ _ hw' hb, List.drop_zero, sub1 (by omega), h2]
        unfold contDown
        obtain ⟨m, hm⟩ : ∃ m, lU.toNat - 1 = m + 1 := ⟨lU.toNat - 2, by omega⟩
        rw [hm]
        simp only [walkFrom, Nat.add_sub_cancel]
    · rw [dite_eq_right hv]
      have hv' := v_ne hv
      obtain ⟨hk, hdk, hvs, _, _⟩ := hw.next_sym hv'
      have hle := chain_le hw.small v.toNat _ (fun s hs => mem_drop_rev hs) hw.chain
      have he : e.toNat ≠ 0 := by
        have := hw.ecode
        omega
      have hw' : WalkAt lens t0 head next baseU.toNat (stepFast baseU t (v - 1) lU (e - 1) (walk_ok h hv) rfl rfl rfl)
          lU.toNat (getSlot next (v - 1) (walk_link h hv) (walk_nsz h)).toNat (e - 1).toNat (k + 1) := by
        rw [stepFast_eq _ rfl rfl rfl (by rw [sub1 hv']; omega), getSlot_toNat, slotNum_eq_u16At, sub1 hv', sub1 he]
        exact hw.step hv'
      have hdec := walk_dec_next h hv
      have hb := Nat.lt_of_lt_of_le hdec (Nat.le_of_lt_succ hN)
      have hs : v.toNat - 1 = (symsOf lens lU.toNat)[(symsOf lens lU.toNat).length - 1 - k] := by omega
      rw [ih _ _ _ _ _ hw' hb, stepFast_eq _ rfl rfl rfl (by rw [sub1 hv']; omega), hdk]
      unfold contDown
      dsimp only [walkSyms]
      rw [sub1 he, sub1 hv', hs]

/-- What `buildFast` needs: a complete code over at most 704 symbols, given by the lists of its lengths' symbols, and an
arena of whole slots with room for the table. -/
def BuildArgs (t head next : ByteArray) (lens : List Nat) : Prop :=
  Complete (.canonical lens) ∧ lens.length ≤ 704 ∧ ListsIs head next lens ∧ head.size < 2 ^ 32 ∧ next.size < 2 ^ 32 ∧
    t.size % 2 = 0 ∧ t.size + 2672 < 2 ^ 32

theorem half_toNat {t : ByteArray} (h : t.size + 2672 < 2 ^ 32) : (t.size.toUInt64 >>> 1).toNat = t.size / 2 := by
  rw [u64_shr (by decide), Nat.toUInt64_eq, u64_lit (by omega)]
  rfl

theorem build_start {t head next : ByteArray} {lens : List Nat} (h : BuildArgs t head next lens) :
    WalkAt lens (zeroExtend t 512) head next (t.size.toUInt64 >>> 1).toNat (zeroExtend t 512) 15 (u16At head 15) 32768 0 := by
  obtain ⟨hC, hlen, hl, hh, hn, h2, h32⟩ := h
  rw [half_toNat h32]
  have hlen15 := length_symsOf (lens := lens) (l := 15) (by decide)
  have htop := top_code hC
  refine ⟨hC, hlen, hl, hh, hn, by omega, by decide, Nat.zero_le _, by rw [List.drop_zero]; exact hl.2 15 (by decide) (by decide),
    by rw [Nat.sub_zero, hlen15]; omega, ⟨[], [], fun _ => 0, ?_, fun s' l' hg hl' => ?_, fun i hi hle => absurd hle (by omega)⟩⟩
  · have hinit := DownInv.init (lens := lens) (t := t) (base := t.size / 2) (by omega)
    rw [zeroExtend_zeros]
    refine ⟨hinit.size, fun q hq => ?_, hinit.opsOk, hinit.disj, hinit.empty, hinit.roots, hinit.hits⟩
    rfl
  · have := hC.1 l' (List.mem_of_getElem? hg)
    omega

/-- Appends a canonical code's table to the arena, the code given by the lists of its lengths' symbols. Its slots start
at `t.size / 2`. -/
def buildFast (t head next : ByteArray) (h : ∃ lens, BuildArgs t head next lens) : ByteArray :=
  walkFast head next (t.size.toUInt64 >>> 1) (zeroExtend t 512) 15
    (getSlot head 15 (by obtain ⟨_, ha⟩ := h; have := ha.2.2.1.1; show 2 * 15 + 1 < _; omega) (by obtain ⟨_, ha⟩ := h; exact ha.2.2.2.1))
    32768 (by
      obtain ⟨lens, ha⟩ := h
      refine ⟨lens, zeroExtend t 512, 0, ?_⟩
      rw [getSlot_toNat, slotNum_eq_u16At]
      exact build_start ha)

/-- The running builder writes the bytes of `buildDown`, whose theorem says what they mean. -/
theorem buildFast_eq {t head next : ByteArray} {lens : List Nat} (ha : BuildArgs t head next lens)
    (h : ∃ lens, BuildArgs t head next lens) : buildFast t head next h = buildDown t lens := by
  have hw := build_start ha
  have h1 : 2 * (15 : UInt64).toNat + 1 < head.size := by
    have := ha.2.2.1.1
    show 2 * 15 + 1 < _
    omega
  have hw' : WalkAt lens (zeroExtend t 512) head next (t.size.toUInt64 >>> 1).toNat (zeroExtend t 512) (15 : UInt64).toNat
      (getSlot head 15 h1 ha.2.2.2.1).toNat (32768 : UInt64).toNat 0 := by
    rw [getSlot_toNat, slotNum_eq_u16At]
    exact hw
  have hle := chain_le ha.2.1 _ _ (fun s hs => mem_drop_rev hs) hw.chain
  have hb : (15 : UInt64).toNat * 1024 + (getSlot head 15 h1 ha.2.2.2.1).toNat < 16384 := by
    rw [getSlot_toNat, slotNum_eq_u16At]
    show 15 * 1024 + u16At head 15 < _
    omega
  unfold buildFast
  rw [walkFast_eq _ _ _ _ _ _ _ _ _ hw' hb, half_toNat ha.2.2.2.2.2.2, List.drop_zero, zeroExtend_zeros]
  rfl

/-! ### The lists from a lengths array -/

/-- A chain stays when `next` changes only at a symbol not in it. -/
theorem ChainIs.frame {next : ByteArray} {j : USize} {x : UInt64} (hj : j.toNat < 2 ^ 16) :
    ∀ {v : Nat} {ss : List Nat}, ChainIs next v ss → (∀ s ∈ ss, s ≠ j.toNat) → ChainIs (u16Set next j x) v ss
  | _, [], h, _ => h
  | _, s :: ss, ⟨h1, h2, h3⟩, hn => by
    refine ⟨h1, by rw [size_u16Set]; exact h2, ?_⟩
    rw [u16At_set_ne hj (hn s List.mem_cons_self)]
    exact ChainIs.frame hj h3 fun s' hs' => hn s' (List.mem_cons_of_mem _ hs')

private theorem lens_byte_toUSize {lens : ByteArray} {i : USize} (h : i.toNat < lens.size) :
    (lens.uget i h).toUSize.toNat = (lens.data[i.toNat]?.getD 0).toNat := by
  rw [UInt8.toNat_toUSize, uget_toNat]

/-- What `listsLoop` needs: at most 704 code lengths, each at most 15. -/
def LensSmall (lens : ByteArray) (n : USize) : Prop :=
  n.toNat ≤ 704 ∧ ∀ j, j < n.toNat → (lens.data[j]?.getD 0).toNat ≤ 15

instance (lens : ByteArray) (n : USize) : Decidable (LensSmall lens n) := by
  unfold LensSmall
  infer_instance

/-- Links the symbols from `i` of the `n` code lengths in `lens`, each in front of its length's list. -/
def listsLoop (lens : ByteArray) (n : USize) (hn : n.toNat ≤ lens.size) (hs : LensSmall lens n) (i : USize)
    (head next : ByteArray) (hh : head.size = 32) (hx : next.size = 2 * n.toNat) : ByteArray × ByteArray :=
  if hi : i < n then
    have hil : i.toNat < lens.size := Nat.lt_of_lt_of_le (USize.lt_iff_toNat_lt.mp hi) hn
    let l := (lens.uget i hil).toUSize
    if l = 0 then listsLoop lens n hn hs (i + USize.ofNat 1) head next hh hx
    else
      have hl : l.toNat ≤ 15 := by
        show (lens.uget i hil).toUSize.toNat ≤ 15
        rw [lens_byte_toUSize hil]
        exact hs.2 _ (USize.lt_iff_toNat_lt.mp hi)
      have hi' : i.toNat < n.toNat := USize.lt_iff_toNat_lt.mp hi
      -- the old head read before `head` is written, so that it is held once there and written in place
      let old := u16GetU head l (by omega) (by omega)
      listsLoop lens n hn hs (i + USize.ofNat 1)
        (u16SetU head l (i.toUInt64 + 1) (by omega) (by omega))
        (u16SetU next i old (by have := hs.1; omega) (by have := hs.1; omega))
        (by rw [size_u16SetU]; exact hh) (by rw [size_u16SetU]; exact hx)
  else (head, next)
termination_by n.toNat - i.toNat
decreasing_by
  all_goals
    have h1 := USize.lt_iff_toNat_lt.mp hi
    have h2 := usize_next hi
    omega

/-- The lists of each length's symbols of the `n` code lengths in `lens`. -/
def listsOf (lens : ByteArray) (n : USize) (hn : n.toNat ≤ lens.size) (hs : LensSmall lens n) : ByteArray × ByteArray :=
  listsLoop lens n hn hs 0 (zeroBytes 32) (zeroBytes (2 * n.toNat)) (zeroBytes_size (by decide))
    (zeroBytes_size (by have := hs.1; omega))

theorem listsLoop_spec {lens : ByteArray} {n : USize} {hn : n.toNat ≤ lens.size} (hs : LensSmall lens n) :
    ∀ (N : Nat) (i : USize) (head next : ByteArray) (hh : head.size = 32) (hnx : next.size = 2 * n.toNat),
    n.toNat - i.toNat = N → i.toNat ≤ n.toNat →
    (∀ l, 1 ≤ l → l ≤ 15 →
      ChainIs next (u16At head l) ((List.range i.toNat).filter (fun s => (lensOf lens n.toNat)[s]? == some l)).reverse) →
    (listsLoop lens n hn hs i head next hh hnx).1.size = 32 ∧ (listsLoop lens n hn hs i head next hh hnx).2.size = 2 * n.toNat ∧
      ListsIs (listsLoop lens n hn hs i head next hh hnx).1 (listsLoop lens n hn hs i head next hh hnx).2 (lensOf lens n.toNat) := by
  have h704 := hs.1
  intro N
  induction N with
  | zero =>
    intro i head next hh hnx hN hi hc
    have hin : ¬ i < n := fun h => by have := USize.lt_iff_toNat_lt.mp h; omega
    rw [listsLoop, dite_eq_right hin]
    dsimp only
    refine ⟨hh, hnx, by omega, fun l h1 h2 => ?_⟩
    have := hc l h1 h2
    rwa [show i.toNat = (lensOf lens n.toNat).length by rw [length_lensOf hn]; omega] at this
  | succ N ih =>
    intro i head next hh hnx hN hi hc
    have hlt : i < n := USize.lt_iff_toNat_lt.mpr (by omega)
    have hi1 := usize_next hlt
    have hil : i.toNat < lens.size := by omega
    have hget := lensOf_get (lens := lens) (n := n.toNat) (i := i.toNat) (by omega) hn
    have hl15 : (lens.data[i.toNat]?.getD 0).toNat ≤ 15 := hs.2 _ (by omega)
    -- The lists below `i + 1`.
    have hrange : ∀ l, ((List.range (i.toNat + 1)).filter (fun s => (lensOf lens n.toNat)[s]? == some l)) =
        ((List.range i.toNat).filter (fun s => (lensOf lens n.toNat)[s]? == some l)) ++
          (if (lens.data[i.toNat]?.getD 0).toNat = l then [i.toNat] else []) := by
      intro l
      rw [List.range_succ, List.filter_append]
      congr 1
      by_cases he : (lens.data[i.toNat]?.getD 0).toNat = l <;> simp [hget, he]
    have hmem : ∀ l s, s ∈ (List.range i.toNat).filter (fun s => (lensOf lens n.toNat)[s]? == some l) → s ≠ i.toNat := by
      intro l s hs
      have := List.mem_range.mp (List.mem_filter.mp hs).1
      omega
    rw [listsLoop, dite_eq_left hlt]
    dsimp only
    have hlv := lens_byte_toUSize hil
    by_cases h0 : (lens.uget i hil).toUSize = 0
    · rw [ite_eq_left h0]
      have hz : (lens.data[i.toNat]?.getD 0).toNat = 0 := by rw [← hlv, h0]; rfl
      refine ih (i + USize.ofNat 1) head next hh hnx (by omega) (by omega) fun l h1 h2 => ?_
      rw [hi1, hrange l, ite_eq_right (by omega), List.append_nil]
      exact hc l h1 h2
    · rw [ite_eq_right h0]
      have hl0 : (lens.uget i hil).toUSize.toNat ≠ 0 := fun e => h0 (USize.toNat_inj.mp (by rw [e]; rfl))
      refine ih (i + USize.ofNat 1) _ _ _ _ (by omega) (by omega) ?_
      simp only [u16SetU_eq, u16GetU_eq]
      generalize hL : (lens.uget i hil).toUSize = L at h0 hl0 hlv ⊢
      have hL16 : L.toNat < 16 := by omega
      have hi16 : i.toNat < 2 ^ 16 := by omega
      have hL2 : L.toNat < 2 ^ 16 := by omega
      have hiv : (i.toUInt64 + 1).toNat = i.toNat + 1 := by
        rw [u64_add' (by rw [USize.toNat_toUInt64, show (1 : UInt64).toNat = 1 from rfl]; omega), USize.toNat_toUInt64]
        rfl
      intro l h1 h2
      rw [hi1, hrange l]
      by_cases he : L.toNat = l
      · subst he
        rw [ite_eq_left (by omega), List.reverse_append, List.reverse_singleton, List.singleton_append,
          u16At_set_same hL2 (by omega) (by omega), hiv]
        refine ⟨rfl, by rw [size_u16Set]; omega, ?_⟩
        rw [u16At_set_same hi16 (by omega) (by rw [u16Get_toNat _ hL2]; exact u16At_lt _ _), u16Get_toNat _ hL2]
        exact ChainIs.frame hi16 (hc _ h1 h2) fun s hs => hmem _ s (List.mem_reverse.mp hs)
      · rw [ite_eq_right (by omega), List.append_nil, u16At_set_ne hL2 (Ne.symm he)]
        exact ChainIs.frame hi16 (hc l h1 h2) fun s hs => hmem _ s (List.mem_reverse.mp hs)

theorem listsOf_spec {lens : ByteArray} {n : USize} {hn : n.toNat ≤ lens.size} (hs : LensSmall lens n) :
    (listsOf lens n hn hs).1.size = 32 ∧ (listsOf lens n hn hs).2.size = 2 * n.toNat ∧
      ListsIs (listsOf lens n hn hs).1 (listsOf lens n hn hs).2 (lensOf lens n.toNat) := by
  refine listsLoop_spec hs _ 0 _ _ _ _ rfl (by simp) ?_
  intro l _ _
  show ChainIs _ (u16At (zeroBytes 32) l) []
  show u16At (zeroBytes 32) l = 0
  unfold u16At
  rw [zeroBytes_get (by decide), zeroBytes_get (by decide)]
  rfl

/-- What `buildLens` needs: a complete code over the `n` code lengths in `lens`, at most 704, and an arena of whole
slots with room for the table. -/
def LensArgs (t lens : ByteArray) (n : USize) : Prop :=
  Complete (.canonical (lensOf lens n.toNat)) ∧ n.toNat ≤ 704 ∧ t.size % 2 = 0 ∧ t.size + 2672 < 2 ^ 32

/-- A complete code's lengths are small. -/
theorem LensArgs.small {t lens : ByteArray} {n : USize} (h : LensArgs t lens n) (hn : n.toNat ≤ lens.size) : LensSmall lens n :=
  ⟨h.2.1, fun j hj => h.1.1 _ (List.mem_of_getElem? (lensOf_get (lens := lens) (n := n.toNat) (i := j) hj hn))⟩

theorem lens_build {t lens : ByteArray} {n : USize} {hn : n.toNat ≤ lens.size} (h : LensArgs t lens n) :
    BuildArgs t (listsOf lens n hn (h.small hn)).1 (listsOf lens n hn (h.small hn)).2 (lensOf lens n.toNat) := by
  have hs := h.small hn
  obtain ⟨hC, h704, h2, h32⟩ := h
  obtain ⟨s1, s2, hl⟩ := listsOf_spec (hn := hn) hs
  exact ⟨hC, by rw [length_lensOf hn]; exact h704, hl, by omega, by omega, h2, h32⟩

/-- Appends a canonical code's table to the arena, from the `n` code lengths in `lens`. Its slots start at
`t.size / 2`. -/
def buildLens (t lens : ByteArray) (n : USize) (hn : n.toNat ≤ lens.size) (h : LensArgs t lens n) : ByteArray :=
  match hl : listsOf lens n hn (h.small hn) with
  | (head, next) => buildFast t head next ⟨lensOf lens n.toNat, by
      have := lens_build (hn := hn) h
      rw [hl] at this
      exact this⟩

theorem buildLens_eq {t lens : ByteArray} {n : USize} {hn : n.toNat ≤ lens.size} (h : LensArgs t lens n) :
    buildLens t lens n hn h = buildDown t (lensOf lens n.toNat) := by
  unfold buildLens
  split
  rename_i head next hl
  have := lens_build (hn := hn) h
  rw [hl] at this
  exact buildFast_eq this _

/-- Appends a single-symbol code's table. -/
def buildSingleFast (t : ByteArray) (sym : UInt64) (h : t.size + 2672 < 2 ^ 32 ∧ t.size % 2 = 0) : ByteArray :=
  fillRun (sym <<< 4) 1 (zeroExtend t 512) (t.size.toUInt64 >>> 1) 256 (by rw [size_zeroExtend]; omega) (by
    intro k hk
    have hk' : k < 256 := hk
    rw [size_zeroExtend, half_toNat h.1]
    show 2 * (t.size / 2 + k * 1) + 1 < _
    omega)

theorem buildSingleFast_eq {t : ByteArray} {sym : UInt64} (h : t.size + 2672 < 2 ^ 32 ∧ t.size % 2 = 0)
    (hsym : sym.toNat < 4096) : buildSingleFast t sym h = buildSingle t sym.toNat := by
  have hv : (sym <<< 4).toNat = 0 + 16 * sym.toNat := by
    rw [u64_shl (by decide) (by rw [show (4 : UInt64).toNat = 4 from rfl]; omega), show (4 : UInt64).toNat = 4 from rfl]
    omega
  unfold buildSingleFast buildSingle
  rw [fillRun_eq hv _ 256 _ _ _ _ _ rfl, half_toNat h.1, zeroExtend_zeros]
  rfl

end Brotli.Decoder
