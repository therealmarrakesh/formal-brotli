import Brotli.Decoder.Table
import Brotli.Decoder.Copy
import Brotli.Decoder.Lookup
import Brotli.Decoder.Fixed

/-!
# Building a table in fixed-width values

The table builder that runs. It takes a code's lengths from a byte array and keeps its counters in scratch byte arrays.
`buildFast_eq` proves it writes exactly the bytes of `buildCanonical`, whose proofs say what a table means, and
`buildSingleFast_eq` does the same for `buildSingle`.
-/

namespace Brotli.Decoder

open Brotli.Spec Brotli.Properties

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

private theorem size_uset' (t : ByteArray) (i : USize) (v : UInt8) (h : i.toNat < t.size) : (t.uset i v h).size = t.size := by
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

private theorem and255 (v : UInt64) : (v &&& 255).toNat = v.toNat % 256 := by
  rw [UInt64.toNat_and, show (255 : UInt64).toNat = 2 ^ 8 - 1 from rfl, Nat.and_two_pow_sub_one_eq_mod]

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

/-- 65536 zero bytes. Arrays are zero-filled by copying from it: a copy into an array that has room writes in place,
where a copy of an array onto itself copies all of it. -/
def zeroBlock : ByteArray := ⟨Array.replicate 65536 0⟩

/-- `t` with `n` zero bytes added at its end, copied from `zeroBlock` at most 65536 at a time. Into an array with room
for them the copy writes in place; into one without, as for a small table built from an empty array, it makes an array of
exactly the bytes needed, so that no array has more room than the state counts. -/
def zeroExtend (t : ByteArray) (n : Nat) : ByteArray :=
  if _h : n ≤ 65536 then zeroBlock.copySlice 0 t t.size n true
  else zeroExtend (zeroBlock.copySlice 0 t t.size 65536 true) (n - 65536)
termination_by n
decreasing_by omega

theorem zeroBlock_copy (t : ByteArray) {n : Nat} (h : n ≤ 65536) :
    (zeroBlock.copySlice 0 t t.size n true).data = t.data ++ Array.replicate n 0 := by
  simp only [ByteArray.copySlice, zeroBlock]
  rw [Array.extract_eq_self_of_le (by simp),
    Array.extract_empty_of_size_le_start (start := t.size + min n ((Array.replicate 65536 (0 : UInt8)).size - 0))
      (by simp only [ByteArray.size_data, Array.size_replicate]; omega),
    Array.append_empty, Array.extract_replicate]
  congr 2
  omega

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

/-- A scratch array of `k` zero bytes, made at its size. -/
@[inline] def zeroBytes (k : Nat) : ByteArray := zeroExtend (ByteArray.emptyWithCapacity k) k

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

private theorem lensOf_drop {lens : ByteArray} {n i : Nat} (hi : i < n) (hn : n ≤ lens.size) :
    (lensOf lens n).drop i = (lens.data[i]?.getD 0).toNat :: (lensOf lens n).drop (i + 1) := by
  have hl : i < (lensOf lens n).length := by rw [length_lensOf hn]; exact hi
  rw [List.drop_eq_getElem_cons hl]
  congr 1
  have := lensOf_get hi hn
  rw [List.getElem?_eq_getElem hl] at this
  exact Option.some.inj this

private theorem lensOf_drop_end {lens : ByteArray} {n i : Nat} (hi : n ≤ i) (hn : n ≤ lens.size) :
    (lensOf lens n).drop i = [] := by
  apply List.drop_eq_nil_of_le
  rw [length_lensOf hn]
  exact hi

private theorem uget_lens {lens : ByteArray} {n i : USize} (hn : n.toNat ≤ lens.size) (hi : i < n) :
    i.toNat < lens.size :=
  Nat.lt_of_lt_of_le (USize.lt_iff_toNat_lt.mp hi) hn

/-! ### Counting the lengths and finding the first codes -/

/-- A 16-entry array of numbers, held as 16-bit values. -/
def U16Match (a : Array Nat) (b : ByteArray) : Prop :=
  b.size = 32 ∧ a.size = 16 ∧ ∀ k, k < 16 → a.getD k 0 = u16At b k

theorem U16Match.set {a : Array Nat} {b : ByteArray} (h : U16Match a b) {l : USize} {v : UInt64} (hl : l.toNat < 16)
    (hv : v.toNat < 65536) : U16Match (a.setIfInBounds l.toNat v.toNat) (u16Set b l v) := by
  obtain ⟨h1, h2, h3⟩ := h
  refine ⟨by rw [size_u16Set]; exact h1, by simpa using h2, ?_⟩
  intro k hk
  rw [getD_set (by omega)]
  by_cases he : k = l.toNat
  · subst he
    rw [ite_eq_left rfl, u16At_set_same (by omega) (by omega) hv]
  · rw [ite_eq_right he, u16At_set_ne (by omega) he, h3 k hk]

/-- Counts how many times each length occurs. -/
def countLens (lens : ByteArray) (n : USize) (hn : n.toNat ≤ lens.size) (i : USize) (cs : ByteArray) : ByteArray :=
  if hi : i < n then
    let l := (lens.uget i (uget_lens hn hi)).toUSize
    countLens lens n hn (i + USize.ofNat 1) (u16Set cs l (u16Get cs l + 1))
  else cs
termination_by n.toNat - i.toNat
decreasing_by
  have := usize_next hi
  have := USize.lt_iff_toNat_lt.mp hi
  omega

private theorem lens_byte {lens : ByteArray} {i : USize} (h : i.toNat < lens.size) :
    (lens.uget i h).toUSize.toNat = (lens.data[i.toNat]?.getD 0).toNat := by
  rw [UInt8.toNat_toUSize, uget_toNat]

private theorem lens_small {lens : ByteArray} {n : Nat} (hn : n ≤ lens.size) (hl : ∀ l ∈ lensOf lens n, l ≤ 15) {i : Nat}
    (hi : i < n) : (lens.data[i]?.getD 0).toNat ≤ 15 :=
  hl _ (List.mem_of_getElem? (lensOf_get hi hn))

theorem countLens_spec {lens : ByteArray} {n : USize} {hn : n.toNat ≤ lens.size} (h64 : n.toNat < 65536)
    (hl : ∀ l ∈ lensOf lens n.toNat, l ≤ 15) : ∀ (N : Nat) (i : USize) (cs : ByteArray) (a : Array Nat),
    n.toNat - i.toNat = N → i.toNat ≤ n.toNat → U16Match a cs → (∀ k, k < 16 → a.getD k 0 ≤ i.toNat) →
    U16Match (((lensOf lens n.toNat).drop i.toNat).foldl (fun cs l => cs.setIfInBounds l (cs.getD l 0 + 1)) a)
      (countLens lens n hn i cs) := by
  intro N
  induction N with
  | zero =>
    intro i cs a hN hle hm _
    have hnot : ¬ i < n := fun h => by have := USize.lt_iff_toNat_lt.mp h; omega
    rw [countLens, dite_eq_right hnot, lensOf_drop_end (by omega) hn]
    exact hm
  | succ N ih =>
    intro i cs a hN hle hm hb
    have hi : i < n := USize.lt_iff_toNat_lt.mpr (by omega)
    have hltn := USize.lt_iff_toNat_lt.mp hi
    rw [countLens, dite_eq_left hi, lensOf_drop hltn hn, List.foldl_cons]
    dsimp only
    have hsmall := lens_small hn hl hltn
    rw [← lens_byte (uget_lens hn hi)] at hsmall ⊢
    generalize hl0 : (lens.uget i (uget_lens hn hi)).toUSize = l at hsmall ⊢
    have hgoal := usize_next hi
    have hval : (u16Get cs l + 1).toNat = a.getD l.toNat 0 + 1 := by
      rw [u64_add' (by rw [u16Get_toNat _ (by omega), show (1 : UInt64).toNat = 1 from rfl]; have := u16At_lt cs l.toNat; omega),
        u16Get_toNat _ (by omega), show (1 : UInt64).toNat = 1 from rfl, hm.2.2 _ (by omega)]
    have hvb : (u16Get cs l + 1).toNat < 65536 := by
      rw [hval]
      have := hb l.toNat (by omega)
      omega
    have hm' := hm.set (l := l) (v := u16Get cs l + 1) (by omega) hvb
    rw [hval] at hm'
    rw [← hgoal]
    refine ih _ _ _ (by omega) (by omega) hm' ?_
    intro k hk
    rw [getD_set (by rw [hm.2.1]; omega)]
    have := hb k hk
    have := hb l.toNat (by omega)
    split <;> omega

/-- Turns the counts into the first code of each length, in place, with `c` the first code of length `b`. -/
def firstCodes (cs : ByteArray) (b : USize) (c : UInt64) : ByteArray :=
  if _hb : b < USize.ofNat 16 then
    let k := if b = 0 then 0 else u16Get cs b
    firstCodes (u16Set cs b c) (b + USize.ofNat 1) ((c + k) <<< 1)
  else cs
termination_by 16 - b.toNat
decreasing_by
  have h1 := usize_next _hb
  have h2 := USize.lt_iff_toNat_lt.mp _hb
  rw [usize_lit' (by decide)] at h2
  omega

private theorem nextCode_le_pow {L : List Nat} (hk : lengthSum L ≤ 32768) {b : Nat} (h : b ≤ 15) :
    nextCode L b ≤ 32768 := by
  cases b with
  | zero => simp [nextCode]
  | succ b =>
    have h1 := nextCode_add_le hk (len := b + 1) (by omega) h
    have h2 : 2 ^ (b + 1) ≤ 2 ^ 15 := Nat.pow_le_pow_right (by decide) h
    have : (2 : Nat) ^ 15 = 32768 := rfl
    omega

theorem firstCodes_spec {L : List Nat} (hl : ∀ l ∈ L, l ≤ 15) (hk : lengthSum L ≤ 32768) :
    ∀ (N : Nat) (b : USize) (cs : ByteArray) (c : UInt64), 16 - b.toNat = N → b.toNat ≤ 16 → cs.size = 32 →
    (∀ k, k < b.toNat → u16At cs k = nextCode L k) →
    (∀ k, b.toNat ≤ k → k < 16 → u16At cs k = (lengthCounts L).getD k 0) → c.toNat = nextCode L b.toNat →
    (firstCodes cs b c).size = 32 ∧ ∀ k, k < 16 → u16At (firstCodes cs b c) k = nextCode L k := by
  intro N
  induction N with
  | zero =>
    intro b cs c hN hle hs h1 _ _
    have hnot : ¬ b < USize.ofNat 16 := fun h => by
      have := USize.lt_iff_toNat_lt.mp h
      rw [usize_lit' (by decide)] at this
      omega
    rw [firstCodes, dite_eq_right hnot]
    exact ⟨hs, fun k hk => h1 k (by omega)⟩
  | succ N ih =>
    intro b cs c hN hle hs h1 h2 hc
    have hb : b < USize.ofNat 16 := USize.lt_iff_toNat_lt.mpr (by rw [usize_lit' (by decide)]; omega)
    have hsucc := usize_next hb
    have hcle : c.toNat ≤ 32768 := by
      rw [hc]
      exact nextCode_le_pow hk (by omega)
    have hcount : (if b = 0 then 0 else u16Get cs b).toNat = blCount L b.toNat := by
      by_cases hz : b = 0
      · rw [ite_eq_left hz, hz]
        simp [blCount]
      · rw [ite_eq_right hz, u16Get_toNat _ (by omega), h2 _ (Nat.le_refl _) (by omega)]
        exact lengthCounts_eq hl (usize_ne hz)
    have hkb : (if b = 0 then 0 else u16Get cs b).toNat < 65536 := by
      by_cases hz : b = 0
      · rw [ite_eq_left hz]
        decide
      · rw [ite_eq_right hz, u16Get_toNat _ (by omega)]
        exact u16At_lt _ _
    rw [firstCodes, dite_eq_left hb]
    dsimp only
    generalize (if b = 0 then 0 else u16Get cs b) = k at hcount hkb ⊢
    refine ih _ _ _ (by omega) (by omega) (by rw [size_u16Set]; exact hs) ?_ ?_ ?_
    · intro j hj
      by_cases he : j = b.toNat
      · rw [he, u16At_set_same (by omega) (by omega) (by omega), hc]
      · rw [u16At_set_ne (by omega) he]
        exact h1 j (by omega)
    · intro j hj hj16
      rw [u16At_set_ne (by omega) (by omega)]
      exact h2 j (by omega) hj16
    · have hsum : (c + k).toNat = c.toNat + k.toNat := u64_add' (by omega)
      rw [hsucc, u64_shl (by decide) (by rw [hsum, show (1 : UInt64).toNat = 1 from rfl]; omega), hsum, hc, hcount]
      show _ = (nextCode L b.toNat + blCount L b.toNat) <<< 1
      rw [Nat.shiftLeft_eq]
      rfl

/-- The first code of each length, in an array. -/
def firstCodesOf (lens : ByteArray) (n : USize) (hn : n.toNat ≤ lens.size) : ByteArray :=
  firstCodes (countLens lens n hn 0 (zeroBytes 32)) 0 0

theorem firstCodesOf_spec {lens : ByteArray} {n : USize} {hn : n.toNat ≤ lens.size} (h64 : n.toNat < 65536)
    (hC : Complete (.canonical (lensOf lens n.toNat))) :
    U16Match (nextCodes (lensOf lens n.toNat)) (firstCodesOf lens n hn) := by
  have hs0 : (zeroBytes 32).size = 32 := zeroBytes_size (by decide)
  have h0 : U16Match (Array.replicate 16 0) (zeroBytes 32) := by
    refine ⟨hs0, by simp, ?_⟩
    intro k _
    unfold u16At
    rw [zeroBytes_get (by decide), zeroBytes_get (by decide)]
    simp [Array.getD_eq_getD_getElem?, Array.getElem?_replicate]
    split <;> rfl
  have hz : (0 : USize).toNat = 0 := rfl
  have hc := countLens_spec (hn := hn) h64 hC.1 _ 0 _ _ rfl (by rw [hz]; omega) h0 (by
    intro k _
    simp [Array.getD_eq_getD_getElem?, Array.getElem?_replicate]
    split <;> simp)
  rw [hz, List.drop_zero] at hc
  obtain ⟨c1, _, c3⟩ := hc
  obtain ⟨hsz, hat⟩ := firstCodes_spec hC.1 (Nat.le_of_eq hC.2) _ 0 (countLens lens n hn 0 (zeroBytes 32)) 0 rfl (by rw [hz]; omega) c1
    (by intro k hk; rw [hz] at hk; omega)
    (by
      intro k _ hk
      rw [← c3 k hk]
      rfl)
    (by rw [hz]; rfl)
  obtain ⟨n1, n2⟩ := nextCodes_spec hC.1
  refine ⟨hsz, n1, ?_⟩
  intro k hk
  rw [n2 k hk]
  exact (hat k hk).symm

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
@[inline] def rev8 (v : UInt64) : UInt64 := (rev8Lut.uget (v &&& 255).toUSize (rev8_idx v)).toUInt64

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

/-! ### Walking the code words -/

/-- Visits each symbol that has a code, with its code word from the counters `nc`. -/
@[specialize] def walkCodes {β : Type} (f : β → UInt64 → UInt64 → UInt64 → β) (lens : ByteArray) (n : USize)
    (hn : n.toNat ≤ lens.size) (i : USize) (nc : ByteArray) (acc : β) : β :=
  if hi : i < n then
    let l := (lens.uget i (uget_lens hn hi)).toUInt64
    if l = 0 then walkCodes f lens n hn (i + USize.ofNat 1) nc acc
    else
      let c := u16Get nc l.toUSize
      walkCodes f lens n hn (i + USize.ofNat 1) (u16Set nc l.toUSize (c + 1)) (f acc i.toUInt64 l c)
  else acc
termination_by n.toNat - i.toNat
decreasing_by
  all_goals
    have := usize_next hi
    have := USize.lt_iff_toNat_lt.mp hi
    omega

/-- The walk does what `foldCodes` does, for functions that agree on each symbol that has a code. -/
theorem walkCodes_rel {β γ : Type} {g : β → Nat → Nat → Nat → β} {f : γ → UInt64 → UInt64 → UInt64 → γ} {lens : ByteArray}
    {n : USize} {hn : n.toNat ≤ lens.size} (hC : Complete (.canonical (lensOf lens n.toNat))) (R : β → γ → Prop)
    (hf : ∀ a b (s l c : UInt64), R a b → (lensOf lens n.toNat)[s.toNat]? = some l.toNat → l.toNat ≠ 0 →
      code (lensOf lens n.toNat) s.toNat = some c.toNat → R (g a s.toNat l.toNat c.toNat) (f b s l c))
    {nb : ByteArray} (hnb : U16Match (nextCodes (lensOf lens n.toNat)) nb) {a : β} {b : γ} (h0 : R a b) :
    R (foldCodes g (lensOf lens n.toNat) 0 (nextCodes (lensOf lens n.toNat)) a) (walkCodes f lens n hn 0 nb b) := by
  generalize hL : lensOf lens n.toNat = L at hC hf hnb ⊢
  have key : ∀ (N : Nat) (i : USize) (nc : Array Nat) (nb : ByteArray) (a : β) (b : γ), n.toNat - i.toNat = N →
      i.toNat ≤ n.toNat → U16Match nc nb →
      (∀ l, l ≠ 0 → l < 16 → nc.getD l 0 = nextCode L l + ((L.take i.toNat).filter (· == l)).length) → R a b →
      R (foldCodes g (L.drop i.toNat) i.toNat nc a) (walkCodes f lens n hn i nb b) := by
    intro N
    induction N with
    | zero =>
      intro i nc nb a b hN hle _ _ hr
      have hnot : ¬ i < n := fun h => by have := USize.lt_iff_toNat_lt.mp h; omega
      rw [walkCodes, dite_eq_right hnot, ← hL, lensOf_drop_end (by omega) hn]
      exact hr
    | succ N ih =>
      intro i nc nb a b hN hle hm hnc hr
      have hi : i < n := USize.lt_iff_toNat_lt.mpr (by omega)
      have hltn := USize.lt_iff_toNat_lt.mp hi
      have hsucc := usize_next hi
      have hx : (lens.uget i (uget_lens hn hi)).toUInt64.toNat = (lens.data[i.toNat]?.getD 0).toNat := by
        rw [UInt8.toNat_toUInt64, uget_toNat]
      have hget : L[i.toNat]? = some (lens.data[i.toNat]?.getD 0).toNat := by
        rw [← hL]
        exact lensOf_get hltn hn
      have hdrop : L.drop i.toNat = (lens.data[i.toNat]?.getD 0).toNat :: L.drop (i.toNat + 1) := by
        rw [← hL]
        exact lensOf_drop hltn hn
      rw [walkCodes, dite_eq_left hi, hdrop, foldCodes]
      dsimp only
      rw [← hx] at hget ⊢
      generalize (lens.uget i (uget_lens hn hi)).toUInt64 = l at hget ⊢
      have htake : ∀ k, ((L.take (i.toNat + 1)).filter (· == k)).length =
          ((L.take i.toNat).filter (· == k)).length + (if l.toNat = k then 1 else 0) := by
        intro k
        rw [List.take_add_one, hget, List.filter_append, List.length_append]
        by_cases hx : l.toNat = k <;> simp [hx]
      by_cases h0 : l = 0
      · have hl0 : l.toNat = 0 := by
          rw [h0]
          rfl
        rw [ite_eq_left hl0, ite_eq_left h0, ← hsucc]
        refine ih _ _ _ _ _ (by omega) (by omega) hm ?_ hr
        intro k hk0 hk16
        rw [hsucc, hnc k hk0 hk16, htake k, ite_eq_right (by omega)]
        rfl
      · have hl0 : l.toNat ≠ 0 := fun e => h0 (UInt64.toNat_inj.mp (by rw [e]; rfl))
        have hl15 : l.toNat ≤ 15 := hC.1 _ (List.mem_of_getElem? hget)
        have hus : l.toUSize.toNat = l.toNat := word_toUSize (by omega)
        rw [ite_eq_right hl0, ite_eq_right h0]
        have hval : (u16Get nb l.toUSize).toNat = nc.getD l.toNat 0 := by
          rw [u16Get_toNat _ (by omega), hus, hm.2.2 _ (by omega)]
        have hcode : code L i.toNat = some (nc.getD l.toNat 0) := by
          rw [hnc _ hl0 (by omega)]
          simp [code, hget, hl0]
        have hclt : nc.getD l.toNat 0 < 2 ^ l.toNat := code_lt_two_pow (Nat.le_of_eq hC.2) hget hl0 hl15 hcode
        have hpow : 2 ^ l.toNat ≤ 2 ^ 15 := Nat.pow_le_pow_right (by decide) hl15
        have hp15 : (2 : Nat) ^ 15 = 32768 := rfl
        have hc1 : (u16Get nb l.toUSize + 1).toNat = nc.getD l.toNat 0 + 1 := by
          rw [u64_add' (by rw [hval, show (1 : UInt64).toNat = 1 from rfl]; omega), hval]
          rfl
        have hm' := hm.set (l := l.toUSize) (v := u16Get nb l.toUSize + 1) (by omega) (by omega)
        rw [hus, hc1] at hm'
        rw [← hsucc]
        have hs64 : i.toUInt64.toNat = i.toNat := USize.toNat_toUInt64 i
        have hfin := hf a b i.toUInt64 l (u16Get nb l.toUSize) hr (by rw [hs64]; exact hget) hl0
          (by rw [hs64, hval]; exact hcode)
        rw [hs64, hval] at hfin
        refine ih _ _ _ _ _ (by omega) (by omega) hm' ?_ hfin
        intro k hk0 hk16
        rw [getD_set (by rw [hm.2.1]; omega), hsucc, htake k]
        by_cases he : k = l.toNat
        · subst he
          simp [hnc _ hk0 hk16]
          omega
        · simp [he, Ne.symm he, hnc _ hk0 hk16]
  have h := key _ 0 _ nb a b rfl (by show 0 ≤ _; omega) hnb (by
    intro l _ _
    simp [(nextCodes_spec hC.1).2 l (by omega)]) h0
  exact h

/-! ### Depths and offsets -/

/-- 256 numbers, held as bytes. -/
def ByteMatch (a : Array Nat) (b : ByteArray) : Prop :=
  b.size = 256 ∧ a.size = 256 ∧ ∀ r, r < 256 → a.getD r 0 = (b.data[r]?.getD 0).toNat

/-- A long code word's sub-table needs at least its bits past the root. -/
@[inline] def depthStep (D : ByteArray) (_ l c : UInt64) : ByteArray :=
  if l ≤ 8 then D
  else
    let r := (revFast l c &&& 255).toUSize
    let d := l - 8
    let old := (getU D r).toUInt64
    setU D r (if old < d then d else old).toUInt8

theorem rootIdx {l c : UInt64} (hl : l.toNat ≤ 15) (hc : c.toNat < 2 ^ l.toNat) :
    (revFast l c &&& 255).toUSize.toNat = rootOf l.toNat c.toNat := by
  rw [word_toUSize (by rw [and255]; omega), and255, revFast_toNat hl hc]
  rfl

theorem depthStep_rel {A : Array Nat} {D : ByteArray} (hm : ByteMatch A D) {s l c : UInt64} (hl : l.toNat ≤ 15)
    (hc : c.toNat < 2 ^ l.toNat) :
    ByteMatch (recordDepth A s.toNat l.toNat c.toNat) (depthStep D s l c) := by
  unfold recordDepth depthStep
  by_cases h8 : l.toNat ≤ 8
  · rw [ite_eq_left h8, ite_eq_left (UInt64.le_iff_toNat_le.mpr h8)]
    exact hm
  · have h8' : ¬ l ≤ 8 := fun h => h8 (UInt64.le_iff_toNat_le.mp h)
    rw [ite_eq_right h8, ite_eq_right h8']
    dsimp only
    obtain ⟨h1, h2, h3⟩ := hm
    have hr := rootIdx hl hc
    have hrlt := rootOf_lt l.toNat c.toNat
    rw [← hr] at hrlt ⊢
    generalize (revFast l c &&& 255).toUSize = r at hrlt ⊢
    have hold : (getU D r).toUInt64.toNat = A.getD r.toNat 0 := by
      rw [UInt8.toNat_toUInt64, getU_toNat, h3 _ hrlt]
    have hd : (l - 8).toNat = l.toNat - 8 := u64_sub' (by rw [show (8 : UInt64).toNat = 8 from rfl]; omega)
    have holdlt : A.getD r.toNat 0 < 256 := by
      rw [h3 _ hrlt]
      exact (D.data[r.toNat]?.getD 0).toNat_lt
    have hv : (if (getU D r).toUInt64 < l - 8 then l - 8 else (getU D r).toUInt64).toNat = max (A.getD r.toNat 0) (l.toNat - 8) := by
      by_cases hlt : (getU D r).toUInt64 < l - 8
      · have := UInt64.lt_iff_toNat_lt.mp hlt
        rw [ite_eq_left hlt, hd]
        rw [hold, hd] at this
        omega
      · have : ¬ (getU D r).toUInt64.toNat < (l - 8).toNat := fun h => hlt (UInt64.lt_iff_toNat_lt.mpr h)
        rw [ite_eq_right hlt, hold]
        rw [hold, hd] at this
        omega
    generalize (if (getU D r).toUInt64 < l - 8 then l - 8 else (getU D r).toUInt64) = v at hv
    refine ⟨by rw [size_setU]; exact h1, by simpa using h2, ?_⟩
    intro q hq
    rw [getD_set (by omega), setU_eq]
    by_cases he : q = r.toNat
    · subst he
      rw [ite_eq_left rfl, get_set_same (by omega), UInt64.toNat_toUInt8, hv]
      omega
    · rw [ite_eq_right he, get_set_ne he]
      exact h3 q hq

/-- The offsets, as `offsetsFast` leaves them. -/
structure OffRun where
  off : ByteArray
  next : UInt64

/-- Assigns the sub-tables' offsets from root slot `r`, with `next` where the next sub-table starts. -/
def offsetsFast (D off : ByteArray) (r : USize) (next : UInt64) : OffRun :=
  if _hr : r < USize.ofNat 256 then
    let d := (getU D r).toUInt64
    offsetsFast D (u16Set off r next) (r + USize.ofNat 1) (if d = 0 then next else next + (1 <<< d))
  else ⟨off, next⟩
termination_by 256 - r.toNat
decreasing_by
  all_goals
    have h1 := usize_next _hr
    have h2 := USize.lt_iff_toNat_lt.mp _hr
    rw [usize_lit' (by decide)] at h2
    omega

theorem offsetsFast_spec {A : Array Nat} {D : ByteArray} (hm : ByteMatch A D) (hA : ∀ r, A.getD r 0 ≤ 7) :
    ∀ (N : Nat) (r : USize) (off : ByteArray) (next : UInt64), 256 - r.toNat = N → r.toNat ≤ 256 → off.size = 512 →
    (∀ k, k < r.toNat → u16At off k = offSum A k) → next.toNat = offSum A r.toNat →
    (offsetsFast D off r next).off.size = 512 ∧ (offsetsFast D off r next).next.toNat = offSum A 256 ∧
      ∀ k, k < 256 → u16At (offsetsFast D off r next).off k = offSum A k := by
  intro N
  induction N with
  | zero =>
    intro r off next hN hle hs h1 h2
    have hnot : ¬ r < USize.ofNat 256 := fun h => by
      have := USize.lt_iff_toNat_lt.mp h
      rw [usize_lit' (by decide)] at this
      omega
    have hr : r.toNat = 256 := by omega
    rw [offsetsFast, dite_eq_right hnot]
    rw [hr] at h1 h2
    exact ⟨hs, h2, h1⟩
  | succ N ih =>
    intro r off next hN hle hs h1 h2
    have hr : r < USize.ofNat 256 := USize.lt_iff_toNat_lt.mpr (by rw [usize_lit' (by decide)]; omega)
    have hsucc := usize_next hr
    have hbound := offSum_bound hA r.toNat
    rw [offsetsFast, dite_eq_left hr]
    dsimp only
    have hd : (getU D r).toUInt64.toNat = A.getD r.toNat 0 := by
      rw [UInt8.toNat_toUInt64, getU_toNat, hm.2.2 _ (by omega)]
    have hd7 := hA r.toNat
    have hnv : next.toNat < 65536 := by omega
    have hnext : (if (getU D r).toUInt64 = 0 then next else next + (1 <<< (getU D r).toUInt64)).toNat =
        offSum A (r.toNat + 1) := by
      show _ = offSum A r.toNat + subSize (A.getD r.toNat 0)
      unfold subSize
      by_cases hz : (getU D r).toUInt64 = 0
      · have : A.getD r.toNat 0 = 0 := by
          rw [← hd, hz]
          rfl
        rw [ite_eq_left hz, ite_eq_left this, h2]
        rfl
      · have : A.getD r.toNat 0 ≠ 0 := by
          rw [← hd]
          exact fun e => hz (UInt64.toNat_inj.mp (by rw [e]; rfl))
        rw [ite_eq_right hz, ite_eq_right this, ← hd]
        have hsh := one_shl (d := (getU D r).toUInt64) (by omega)
        have hp : 2 ^ (getU D r).toUInt64.toNat ≤ 2 ^ 7 := Nat.pow_le_pow_right (by decide) (by omega)
        have h27 : (2 : Nat) ^ 7 = 128 := rfl
        rw [u64_add' (by rw [hsh]; omega), hsh, h2]
    refine ih _ _ _ (by omega) (by omega) (by rw [size_u16Set]; exact hs) ?_ (by rw [hsucc]; exact hnext)
    intro k hk
    by_cases he : k = r.toNat
    · rw [he, u16At_set_same (by omega) (by omega) hnv, h2]
    · rw [u16At_set_ne (by omega) he]
      exact h1 k (by omega)

/-! ### Writing the slots -/

private theorem slot_byte {pos : UInt64} {size : Nat} (hs : size < 2 ^ 32) (h : 4 * pos.toNat + 2 < size) {j : UInt64}
    (hj : j.toNat ≤ 2) : (pos * 4 + j).toUSize.toNat = 4 * pos.toNat + j.toNat := by
  have h4 : (pos * 4).toNat = 4 * pos.toNat := by
    rw [UInt64.toNat_mul, show (4 : UInt64).toNat = 4 from rfl]
    rw [Nat.mod_eq_of_lt (by omega)]
    omega
  have e : (pos * 4 + j).toNat = 4 * pos.toNat + j.toNat := by
    rw [u64_add' (by rw [h4]; omega), h4]
  rw [word_toUSize (by rw [e]; omega), e]

/-- Writes one slot. -/
@[inline] def putSlot (t : ByteArray) (pos : UInt64) (b v0 v1 : UInt8) (h : 4 * pos.toNat + 2 < t.size) (h32 : t.size < 2 ^ 32) :
    ByteArray :=
  ((t.uset (pos * 4 + 0).toUSize b (by rw [slot_byte h32 h (by decide)]; show 4 * pos.toNat + 0 < _; omega)).uset
      (pos * 4 + 1).toUSize v0 (by
        rw [size_uset', slot_byte h32 h (by decide)]
        show 4 * pos.toNat + 1 < _
        omega)).uset (pos * 4 + 2).toUSize v1 (by
    rw [size_uset', size_uset', slot_byte h32 h (by decide)]
    show 4 * pos.toNat + 2 < _
    omega)

theorem size_putSlot (t : ByteArray) (pos : UInt64) (b v0 v1 : UInt8) (h : 4 * pos.toNat + 2 < t.size) (h32 : t.size < 2 ^ 32) :
    (putSlot t pos b v0 v1 h h32).size = t.size := by
  simp only [putSlot, size_uset']

theorem putSlot_eq {t : ByteArray} {pos : UInt64} {b v0 v1 : UInt8} {h : 4 * pos.toNat + 2 < t.size} {h32 : t.size < 2 ^ 32}
    {bits val : Nat} (hb : b = bits.toUInt8) (h0 : v0 = (val % 256).toUInt8) (h1 : v1 = (val / 256).toUInt8) :
    putSlot t pos b v0 v1 h h32 = writeSlot t pos.toNat bits val := by
  unfold putSlot writeSlot
  rw [uset_eq, uset_eq, uset_eq, slot_byte h32 h (j := 0) (by decide), slot_byte h32 h (j := 1) (by decide),
    slot_byte h32 h (j := 2) (by decide), hb, h0, h1]
  rfl

private theorem fill_next {t : ByteArray} {pos step count : UInt64} (h : ∀ k, k < count.toNat → 4 * (pos.toNat + k * step.toNat) + 2 < t.size)
    (h32 : t.size < 2 ^ 32) {k : Nat} (hk : k < (count - 1).toNat) (hc : count ≠ 0) :
    4 * ((pos + step).toNat + k * step.toNat) + 2 < t.size := by
  have hne : count.toNat ≠ 0 := fun e => hc (UInt64.toNat_inj.mp (by rw [e]; rfl))
  have h1 : (count - 1).toNat = count.toNat - 1 := u64_sub' (by rw [show (1 : UInt64).toNat = 1 from rfl]; omega)
  have := h (k + 1) (by omega)
  rw [Nat.add_mul, Nat.one_mul] at this
  have e : (pos + step).toNat = pos.toNat + step.toNat := u64_add' (by omega)
  rw [e]
  omega

/-- Writes `count` slots from `pos`, every `step`. The caller has checked that they are all in the array. -/
def fillRun (b v0 v1 : UInt8) (step : UInt64) (t : ByteArray) (pos count : UInt64) (h32 : t.size < 2 ^ 32)
    (h : ∀ k, k < count.toNat → 4 * (pos.toNat + k * step.toNat) + 2 < t.size) : ByteArray :=
  if hc : count = 0 then t
  else
    fillRun b v0 v1 step
      (putSlot t pos b v0 v1 (by
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

theorem fillRun_eq {b v0 v1 : UInt8} {bits val : Nat} (hb : b = bits.toUInt8) (h0 : v0 = (val % 256).toUInt8)
    (h1 : v1 = (val / 256).toUInt8) (step : UInt64) : ∀ (N : Nat) (t : ByteArray) (pos count : UInt64) (h32 : t.size < 2 ^ 32)
    (h : ∀ k, k < count.toNat → 4 * (pos.toNat + k * step.toNat) + 2 < t.size), count.toNat = N →
    fillRun b v0 v1 step t pos count h32 h = writeRange bits val step.toNat N t pos.toNat := by
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
    rw [fillRun, dite_eq_right hz, ih _ _ _ _ _ hk1, putSlot_eq hb h0 h1, writeRange]
    by_cases hN : N = 0
    · subst hN
      rfl
    · have := h 1 (by omega)
      rw [Nat.one_mul] at this
      have e := u64_add' (a := pos) (b := step) (by omega)
      rw [e]

/-- Writes `count` slots from `pos`, every `step`, after checking once that they are all in the array. -/
@[inline] def fillFrom (bits val step count : UInt64) (t : ByteArray) (pos : UInt64) : ByteArray :=
  if h : t.size < 4294967296 ∧ 4 * (pos.toNat + (count.toNat - 1) * step.toNat) + 2 < t.size then
    fillRun bits.toUInt8 val.toUInt8 (val >>> 8).toUInt8 step t pos count h.1 (fun k hk => by
      have := Nat.mul_le_mul_right step.toNat (show k ≤ count.toNat - 1 by omega)
      have := h.2
      omega)
  else t

theorem fillFrom_eq {bits val step count : UInt64} {t : ByteArray} {pos : UInt64} (h32 : t.size < 2 ^ 32)
    (hc : 0 < count.toNat)
    (h : ∀ k, k < count.toNat → 4 * (pos.toNat + k * step.toNat) + 2 < t.size) :
    fillFrom bits val step count t pos = writeRange bits.toNat val.toNat step.toNat count.toNat t pos.toNat := by
  unfold fillFrom
  rw [dite_eq_left ⟨h32, h _ (by omega)⟩]
  refine fillRun_eq (byte_of rfl) (byte_of (by omega)) (byte_of ?_) step _ t pos count _ _ rfl
  rw [u64_shr (by decide)]
  rfl

/-- Writes a code word's slots: those of every bit pattern that begins with it. -/
@[inline] def writeCodeFast (base : UInt64) (D off t : ByteArray) (s l c : UInt64) : ByteArray :=
  let rv := revFast l c
  if l ≤ 8 then fillFrom l s (1 <<< l) (1 <<< (8 - l)) t (base + rv)
  else
    let r := (rv &&& 255).toUSize
    fillFrom l s (1 <<< (l - 8)) (1 <<< ((getU D r).toUInt64 - (l - 8))) t (base + 256 + u16Get off r + (rv >>> (8 : UInt64)))

theorem writeCodeFast_eq {L : List Nat} (hC : Complete (.canonical L)) {D off t : ByteArray} {O : Array Nat}
    (hD : ByteMatch (depths L) D) (hO : ∀ i, i < 256 → O.getD i 0 = offSum (depths L) i)
    (hoff : ∀ i, i < 256 → u16At off i = offSum (depths L) i) {base s l c : UInt64}
    (hs : L[s.toNat]? = some l.toNat) (h0 : l.toNat ≠ 0) (hc : code L s.toNat = some c.toNat)
    (hsize : 4 * (base.toNat + 256 + offSum (depths L) 256) ≤ t.size) (h32 : t.size < 2 ^ 32) :
    writeCodeFast base D off t s l c = writeCode base.toNat (depths L) O t s.toNat l.toNat c.toNat := by
  have hl15 : l.toNat ≤ 15 := hC.1 _ (List.mem_of_getElem? hs)
  have hclt : c.toNat < 2 ^ l.toNat := code_lt_two_pow (Nat.le_of_eq hC.2) hs h0 hl15 hc
  have hrv := revFast_toNat hl15 hclt
  have hrvlt : revBits l.toNat c.toNat < 2 ^ l.toNat := revBits_lt _ _
  have hp15 : 2 ^ l.toNat ≤ 2 ^ 15 := Nat.pow_le_pow_right (by decide) hl15
  have hp : (2 : Nat) ^ 15 = 32768 := rfl
  have hin := fun k hk => written_in (off := O) hC hO (base := base.toNat) (t := t) hs h0 hc hsize (k := k) hk
  unfold writeCodeFast writeCode
  dsimp only
  by_cases hl : l.toNat ≤ 8
  · rw [ite_eq_left (UInt64.le_iff_toNat_le.mpr hl), ite_eq_left hl]
    simp only [hl, ↓reduceIte] at hin
    have h8 : (8 - l).toNat = 8 - l.toNat := u64_sub' (by rw [show (8 : UInt64).toNat = 8 from rfl]; exact hl)
    have hs1 := one_shl (d := l) (by omega)
    have hs2 := one_shl (d := 8 - l) (by omega)
    have hpos : (base + revFast l c).toNat = base.toNat + revBits l.toNat c.toNat := by
      have := hin 0 (Nat.two_pow_pos _)
      rw [u64_add' (by rw [hrv]; omega), hrv]
    rw [fillFrom_eq h32 (by rw [hs2, h8]; exact Nat.two_pow_pos _) (by
      intro k hk
      rw [hs2, h8] at hk
      rw [hpos, hs1]
      exact hin k hk), hs1, hs2, h8, hpos]
  · have h8' : ¬ l ≤ 8 := fun h => hl (UInt64.le_iff_toNat_le.mp h)
    rw [ite_eq_right h8', ite_eq_right hl]
    simp only [hl, ↓reduceIte] at hin
    have hr := rootIdx hl15 hclt
    have hrlt := rootOf_lt l.toNat c.toNat
    have hl8 : (l - 8).toNat = l.toNat - 8 := u64_sub' (by rw [show (8 : UInt64).toNat = 8 from rfl]; omega)
    have hd : (getU D (revFast l c &&& 255).toUSize).toUInt64.toNat = (depths L).getD (rootOf l.toNat c.toNat) 0 := by
      rw [UInt8.toNat_toUInt64, getU_toNat, hr, hD.2.2 _ hrlt]
    have hdeep : l.toNat - 8 ≤ (depths L).getD (rootOf l.toNat c.toNat) 0 :=
      (depths_spec hC.1).2.2.2 s.toNat l.toNat c.toNat ⟨hs, by omega, hc⟩
    have hd7 := (depths_spec hC.1).2.1 (rootOf l.toNat c.toNat)
    have hdsub : ((getU D (revFast l c &&& 255).toUSize).toUInt64 - (l - 8)).toNat =
        (depths L).getD (rootOf l.toNat c.toNat) 0 - (l.toNat - 8) := by
      rw [u64_sub' (by rw [hd, hl8]; exact hdeep), hd, hl8]
    have hs1 := one_shl (d := l - 8) (by omega)
    have hs2 := one_shl (d := (getU D (revFast l c &&& 255).toUSize).toUInt64 - (l - 8)) (by omega)
    have hoffv : (u16Get off (revFast l c &&& 255).toUSize).toNat = O.getD (rootOf l.toNat c.toNat) 0 := by
      rw [u16Get_toNat _ (by omega), hr, hoff _ hrlt, hO _ hrlt]
    have hstart := hin 0 (Nat.two_pow_pos _)
    have hpos : (base + 256 + u16Get off (revFast l c &&& 255).toUSize + (revFast l c >>> (8 : UInt64))).toNat =
        base.toNat + 256 + O.getD (rootOf l.toNat c.toNat) 0 + revBits l.toNat c.toNat / 256 := by
      rw [Nat.zero_mul] at hstart
      have hsh : (revFast l c >>> (8 : UInt64)).toNat = revBits l.toNat c.toNat / 256 := by
        rw [u64_shr (by decide), hrv]
        rfl
      have h256 : (base + 256).toNat = base.toNat + 256 := u64_add' (by rw [show (256 : UInt64).toNat = 256 from rfl]; omega)
      have hmid : (base + 256 + u16Get off (revFast l c &&& 255).toUSize).toNat =
          base.toNat + 256 + O.getD (rootOf l.toNat c.toNat) 0 := by
        rw [u64_add' (by rw [h256, hoffv]; omega), h256, hoffv]
      rw [u64_add' (by rw [hmid, hsh]; omega), hmid, hsh]
    rw [fillFrom_eq h32 (by rw [hs2, hdsub]; exact Nat.two_pow_pos _) (by
      intro k hk
      rw [hs2, hdsub] at hk
      rw [hpos, hs1, hl8]
      exact hin k hk), hs1, hs2, hdsub, hl8, hpos]

/-- Writes each root slot with a sub-table, from `r`. -/
def rootsFast (base : UInt64) (D off : ByteArray) (n r : UInt64) (t : ByteArray) : ByteArray :=
  if _hn : n = 0 then t
  else
    let d := (getU D r.toUSize).toUInt64
    rootsFast base D off (n - 1) (r + 1)
      (if d = 0 then t else fillFrom (8 + d) (u16Get off r.toUSize) 1 1 t (base + r))
termination_by n.toNat
decreasing_by
  all_goals
    have hne : n.toNat ≠ 0 := fun e => _hn (UInt64.toNat_inj.mp (by rw [e]; rfl))
    have h1 : (n - 1).toNat = n.toNat - 1 := u64_sub' (by rw [show (1 : UInt64).toNat = 1 from rfl]; omega)
    omega

theorem rootsFast_eq {A O : Array Nat} {D off : ByteArray} (hD : ByteMatch A D) (hA : ∀ r, A.getD r 0 ≤ 7)
    (hO : ∀ r, r < 256 → u16At off r = O.getD r 0) {base : UInt64} (hb : base.toNat + 256 < 2 ^ 32) :
    ∀ (N : Nat) (n r : UInt64) (t : ByteArray), n.toNat = N → r.toNat + N ≤ 256 → 4 * (base.toNat + 256) ≤ t.size →
    t.size < 2 ^ 32 → rootsFast base D off n r t = writeRoots base.toNat A O N r.toNat t := by
  intro N
  induction N with
  | zero =>
    intro n r t hn _ _ _
    have hz : n = 0 := UInt64.toNat_inj.mp (by rw [hn]; rfl)
    rw [rootsFast, dite_eq_left hz]
    rfl
  | succ N ih =>
    intro n r t hn hr hs h32
    have hz : n ≠ 0 := fun e => by rw [e] at hn; exact Nat.succ_ne_zero _ hn.symm
    have hn1 : (n - 1).toNat = N := by
      rw [u64_sub' (by rw [show (1 : UInt64).toNat = 1 from rfl]; omega), hn]
      rfl
    have hr1 : (r + 1).toNat = r.toNat + 1 := u64_add' (by rw [show (1 : UInt64).toNat = 1 from rfl]; omega)
    have hus : r.toUSize.toNat = r.toNat := word_toUSize (by omega)
    have hd : (getU D r.toUSize).toUInt64.toNat = A.getD r.toNat 0 := by
      rw [UInt8.toNat_toUInt64, getU_toNat, hus, hD.2.2 _ (by omega)]
    have hstep : (if (getU D r.toUSize).toUInt64 = 0 then t
        else fillFrom (8 + (getU D r.toUSize).toUInt64) (u16Get off r.toUSize) 1 1 t (base + r)) =
        (if A.getD r.toNat 0 = 0 then t else writeSlot t (base.toNat + r.toNat) (8 + A.getD r.toNat 0) (O.getD r.toNat 0)) := by
      by_cases h0 : A.getD r.toNat 0 = 0
      · have : (getU D r.toUSize).toUInt64 = 0 := UInt64.toNat_inj.mp (by rw [hd, h0]; rfl)
        rw [ite_eq_left this, ite_eq_left h0]
      · have : (getU D r.toUSize).toUInt64 ≠ 0 := fun e => h0 (by rw [← hd, e]; rfl)
        rw [ite_eq_right this, ite_eq_right h0]
        have h7 := hA r.toNat
        have hbits : (8 + (getU D r.toUSize).toUInt64).toNat = 8 + A.getD r.toNat 0 := by
          rw [u64_add' (by rw [hd, show (8 : UInt64).toNat = 8 from rfl]; omega), hd]
          rfl
        have hval : (u16Get off r.toUSize).toNat = O.getD r.toNat 0 := by
          rw [u16Get_toNat _ (by omega), hus, hO _ (by omega)]
        have hpos : (base + r).toNat = base.toNat + r.toNat := u64_add' (by omega)
        rw [fillFrom_eq h32 (by decide) (by
          intro k hk
          have hk0 : k = 0 := by
            have : k < 1 := hk
            omega
          subst hk0
          rw [hpos]
          omega), hbits, hval, hpos]
        rfl
    rw [rootsFast, dite_eq_right hz, writeRoots]
    dsimp only
    rw [hstep, ← hr1]
    have hsz : (if A.getD r.toNat 0 = 0 then t
        else writeSlot t (base.toNat + r.toNat) (8 + A.getD r.toNat 0) (O.getD r.toNat 0)).size = t.size := by
      split
      · rfl
      · exact size_writeSlot ..
    exact ih _ _ _ hn1 (by omega) (by rw [hsz]; exact hs) (by rw [hsz]; exact h32)

/-! ### The builder -/

/-- What a table takes, worked out before the arena grows. -/
structure Plan where
  nc : ByteArray
  D : ByteArray
  o : OffRun

/-- Works out a table's sub-tables, from the `n` code lengths in `lens`. -/
def planFast (lens : ByteArray) (n : USize) (hn : n.toNat ≤ lens.size) : Plan :=
  let nc := firstCodesOf lens n hn
  let D := walkCodes depthStep lens n hn 0 nc (zeroBytes 256)
  ⟨nc, D, offsetsFast D (zeroBytes 512) (USize.ofNat 0) 0⟩

/-- The bytes a table adds to the arena. -/
@[inline] def Plan.bytes (p : Plan) : UInt64 := (256 + p.o.next) * 4

/-- Appends a planned table to the arena. Its slots start at `t.size / 4`. -/
def fillFast (t lens : ByteArray) (n : USize) (hn : n.toNat ≤ lens.size) (p : Plan) : ByteArray :=
  let base := UInt64.ofNat (t.size / 4)
  let t1 := zeroExtend t p.bytes.toNat
  let t2 := walkCodes (writeCodeFast base p.D p.o.off) lens n hn 0 p.nc t1
  rootsFast base p.D p.o.off 256 0 t2

/-- Appends a canonical code's table to the arena, with the `n` code lengths in `lens`. Its slots start at
`t.size / 4`. -/
def buildFast (t lens : ByteArray) (n : USize) (hn : n.toNat ≤ lens.size) : ByteArray :=
  fillFast t lens n hn (planFast lens n hn)

/-- A plan's bytes are what the table adds. -/
theorem planFast_bytes {lens : ByteArray} {n : USize} {hn : n.toNat ≤ lens.size} (h64 : n.toNat < 65536)
    (hC : Complete (.canonical (lensOf lens n.toNat))) :
    (planFast lens n hn).bytes.toNat = 4 * (256 + offSum (depths (lensOf lens n.toNat)) 256) ∧
      offSum (depths (lensOf lens n.toNat)) 256 ≤ 32768 := by
  have hfirst := firstCodesOf_spec (hn := hn) h64 hC
  unfold planFast Plan.bytes
  dsimp only
  generalize firstCodesOf lens n hn = nc at hfirst ⊢
  have hDm : ByteMatch (depths (lensOf lens n.toNat)) (walkCodes depthStep lens n hn 0 nc (zeroBytes 256)) :=
    walkCodes_rel (g := recordDepth) hC ByteMatch (by
      intro a b s l c hr hs h0 hc
      have hl15 : l.toNat ≤ 15 := hC.1 _ (List.mem_of_getElem? hs)
      exact depthStep_rel hr hl15 (code_lt_two_pow (Nat.le_of_eq hC.2) hs h0 hl15 hc)) hfirst (by
      refine ⟨zeroBytes_size (by decide), by simp, ?_⟩
      intro r _
      rw [zeroBytes_get (by decide)]
      simp [Array.getD_eq_getD_getElem?, Array.getElem?_replicate]
      split <;> rfl)
  obtain ⟨_, dLe, _, _⟩ := depths_spec hC.1
  have hoffs := offsetsFast_spec hDm dLe _ (USize.ofNat 0) (zeroBytes 512) 0 rfl
    (by rw [usize_lit' (by decide)]; omega) (zeroBytes_size (by decide))
    (by intro k hk; rw [usize_lit' (by decide)] at hk; omega)
    (by rw [usize_lit' (by decide)]; rfl)
  have o2 := hoffs.2.1
  have hbound := offSum_bound dLe 256
  generalize offsetsFast (walkCodes depthStep lens n hn 0 nc (zeroBytes 256)) (zeroBytes 512) (USize.ofNat 0) 0 = o at o2 ⊢
  have hnext : (256 + o.next).toNat = 256 + offSum (depths (lensOf lens n.toNat)) 256 := by
    rw [u64_add' (by rw [show (256 : UInt64).toNat = 256 from rfl, o2]; omega), o2]
    rfl
  refine ⟨?_, by omega⟩
  rw [UInt64.toNat_mul, hnext, show (4 : UInt64).toNat = 4 from rfl, Nat.mod_eq_of_lt (by omega)]
  omega

/-- The running builder writes the bytes of `buildCanonical`, whose theorem says what they mean. -/
theorem buildFast_eq {t lens : ByteArray} {n : USize} {hn : n.toNat ≤ lens.size} (h64 : n.toNat < 65536)
    (hC : Complete (.canonical (lensOf lens n.toNat))) (hsize : t.size + 4 * (256 + 32768) < 2 ^ 32) :
    buildFast t lens n hn = buildCanonical t (lensOf lens n.toNat) := by
  have hfirst := firstCodesOf_spec (hn := hn) h64 hC
  unfold buildFast fillFast planFast Plan.bytes buildCanonical
  dsimp only
  generalize firstCodesOf lens n hn = nc at hfirst ⊢
  have hfold : ∀ {β γ : Type} {g : β → Nat → Nat → Nat → β} {f : γ → UInt64 → UInt64 → UInt64 → γ} (R : β → γ → Prop)
      (_ : ∀ a b (s l c : UInt64), R a b → (lensOf lens n.toNat)[s.toNat]? = some l.toNat → l.toNat ≠ 0 →
        code (lensOf lens n.toNat) s.toNat = some c.toNat → R (g a s.toNat l.toNat c.toNat) (f b s l c))
      {a : β} {b : γ}, R a b →
      R (foldCodes g (lensOf lens n.toNat) 0 (nextCodes (lensOf lens n.toNat)) a) (walkCodes f lens n hn 0 nc b) :=
    fun R hf _ _ h => walkCodes_rel hC R hf hfirst h
  generalize lensOf lens n.toNat = L at hC hfold ⊢
  obtain ⟨_, dLe, _, _⟩ := depths_spec hC.1
  have hbase : (UInt64.ofNat (t.size / 4)).toNat = t.size / 4 := u64_lit (by omega)
  have hz256 : ByteMatch (Array.replicate 256 0) (zeroBytes 256) := by
    refine ⟨zeroBytes_size (by decide), by simp, ?_⟩
    intro r _
    rw [zeroBytes_get (by decide)]
    simp [Array.getD_eq_getD_getElem?, Array.getElem?_replicate]
    split <;> rfl
  -- The depths.
  have hDm : ByteMatch (depths L) (walkCodes depthStep lens n hn 0 nc (zeroBytes 256)) :=
    hfold (g := recordDepth) ByteMatch (by
      intro a b s l c hr hs h0 hc
      have hl15 : l.toNat ≤ 15 := hC.1 _ (List.mem_of_getElem? hs)
      exact depthStep_rel hr hl15 (code_lt_two_pow (Nat.le_of_eq hC.2) hs h0 hl15 hc)) hz256
  generalize walkCodes depthStep lens n hn 0 nc (zeroBytes 256) = D at hDm ⊢
  -- The offsets.
  have hoffs := offsetsFast_spec hDm dLe _ (USize.ofNat 0) (zeroBytes 512) 0 rfl
    (by rw [usize_lit' (by decide)]; omega) (zeroBytes_size (by decide))
    (by intro k hk; rw [usize_lit' (by decide)] at hk; omega)
    (by rw [usize_lit' (by decide)]; rfl)
  generalize offsetsFast D (zeroBytes 512) (USize.ofNat 0) 0 = o at hoffs ⊢
  obtain ⟨_, o2, o3⟩ := hoffs
  obtain ⟨oTot, oAt⟩ := offsets_spec (depths L)
  have hbound := offSum_bound dLe 256
  -- The space.
  have hnext : (256 + o.next).toNat = 256 + offSum (depths L) 256 := by
    rw [u64_add' (by rw [show (256 : UInt64).toNat = 256 from rfl, o2]; omega), o2]
    rfl
  have hspace : ((256 + o.next) * 4).toNat = 4 * (256 + offSum (depths L) 256) := by
    rw [UInt64.toNat_mul, hnext, show (4 : UInt64).toNat = 4 from rfl, Nat.mod_eq_of_lt (by omega)]
    omega
  rw [zeroExtend_eq, hspace, oTot]
  generalize ht1 : t ++ ByteArray.mk (Array.replicate (4 * (256 + offSum (depths L) 256)) 0) = t1
  have hmk : (ByteArray.mk (Array.replicate (4 * (256 + offSum (depths L) 256)) 0)).size =
      4 * (256 + offSum (depths L) 256) := by
    show (Array.replicate _ _).size = _
    simp
  have hs1 : t1.size = t.size + 4 * (256 + offSum (depths L) 256) := by
    rw [← ht1, ByteArray.size_append, hmk]
  -- The code words.
  obtain ⟨hw1, hw2⟩ := hfold (β := ByteArray) (γ := ByteArray)
    (g := fun t' s l c => writeCode (t.size / 4) (depths L) (offsets (depths L)).1 t' s l c)
    (f := writeCodeFast (UInt64.ofNat (t.size / 4)) D o.off) (a := t1) (b := t1)
    (fun a b => a = b ∧ a.size = t1.size)
    (by
      rintro a b s l c ⟨rfl, hsz⟩ hs h0 hc
      have heq := writeCodeFast_eq (O := (offsets (depths L)).1) hC hDm oAt o3 (base := UInt64.ofNat (t.size / 4)) hs h0 hc
        (t := a) (by rw [hsz, hs1, hbase]; omega) (by rw [hsz, hs1]; omega)
      rw [hbase] at heq
      exact ⟨heq.symm, by rw [size_writeCode', hsz]⟩)
    ⟨rfl, rfl⟩
  generalize foldCodes (fun t' s l c => writeCode (t.size / 4) (depths L) (offsets (depths L)).1 t' s l c) L 0
    (nextCodes L) t1 = t2 at hw1 hw2 ⊢
  rw [← hw1]
  have e := rootsFast_eq (O := (offsets (depths L)).1) hDm dLe (fun r hr => by rw [o3 r hr, oAt r hr])
    (base := UInt64.ofNat (t.size / 4)) (by rw [hbase]; omega) 256 256 0 t2 rfl (by show 0 + 256 ≤ 256; omega)
    (by rw [hw2, hs1, hbase]; omega) (by rw [hw2, hs1]; omega)
  rw [hbase] at e
  exact e

/-- Appends a single-symbol code's table. -/
def buildSingleFast (t : ByteArray) (sym : UInt64) : ByteArray :=
  fillFrom 0 sym 1 256 (zeroExtend t 1024) (UInt64.ofNat (t.size / 4))

theorem buildSingleFast_eq {t : ByteArray} {sym : UInt64} (hsize : t.size + 4 * 256 < 2 ^ 32) :
    buildSingleFast t sym = buildSingle t sym.toNat := by
  unfold buildSingleFast buildSingle
  rw [zeroExtend_eq]
  have hmk : (ByteArray.mk (Array.replicate 1024 0)).size = 1024 := by
    show (Array.replicate _ _).size = _
    simp
  have hs : (t ++ ByteArray.mk (Array.replicate 1024 0)).size = t.size + 1024 := by
    rw [ByteArray.size_append, hmk]
  have hbase : (UInt64.ofNat (t.size / 4)).toNat = t.size / 4 := u64_lit (by omega)
  rw [fillFrom_eq (by rw [hs]; omega) (by decide) (by
    intro k hk
    have hk' : k < 256 := hk
    rw [hs, hbase]
    show 4 * (t.size / 4 + k * 1) + 2 < _
    omega), hbase]
  rfl


end Brotli.Decoder
