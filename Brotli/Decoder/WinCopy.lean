module

@[expose] public section

/-!
# Window copy primitives

A copy within one `ByteArray`, which the language lacks: `copySlice` from an array to itself copies the whole array
first (the array is held twice by the call, so it isn't exclusive), and byte stores cost a check each. These are the
one place the decoder uses `@[extern]` (`AGENTS.md`, Trust; owner, 2026-11-07).

Each primitive is an ordinary definition: its body, a snapshot copy written with `copySlice` (every byte written is the
byte its source held before the copy), is what the proofs reason about. At compile time the `@[extern c inline]` C
replaces the body: `lean_sarray_ensure_exclusive` (the check `ByteArray.uset` makes, copying the array if it is shared,
so the result is a new value exactly as the body's), then `memmove` (`winMove`), which is a snapshot copy for every
input, or a 16-byte `memcpy` (`winCopy16`), whose signature proves the two ranges don't overlap, where `memcpy` is a
snapshot copy too. Both ranges are inside the array by the signature, so the C never writes or reads outside it. The C
is trusted to match the body, as the runtime's own `ByteArray` operations are.

`winMove_get` and `winCopy16_get` give every byte of the result. `fwdCopy` is the format's copy, byte by byte, each
read seeing the bytes written before it; `fwdCopy_eq_winMove` proves the two agree when the source ends before the
destination begins (a copy at a distance of at least its length).

The fixed-width stores (owner, 2026-11-08) write a value's low 2, 4 or 8 bytes in place, little-endian, which the
language also lacks: a `ByteArray` has only byte stores, each with its own check. Each one's body is `storeLE`, the
bytes (`leList`) copied in with `copySlice`; its C is `lean_sarray_ensure_exclusive`, then one `memcpy` from a local of
the store's width, which on a little-endian target writes those same bytes (the C doesn't compile on any other). The
range is inside the array by the signature. `storeLE_get` gives every byte of the result.
-/

namespace Brotli.Decoder

/-- `n` bytes of `w` copied from `s` to `d` as a snapshot. Compiled as `memmove` within the array. -/
@[extern c inline "({ lean_object * r_ = lean_sarray_ensure_exclusive(#1); __builtin_memmove(lean_sarray_cptr(r_) + #2, lean_sarray_cptr(r_) + #3, #4); r_; })"]
def winMove (w : ByteArray) (d s n : USize)
    (_h : d.toNat + n.toNat ≤ w.size ∧ s.toNat + n.toNat ≤ w.size) : ByteArray :=
  w.copySlice s.toNat w d.toNat n.toNat

/-- 16 bytes of `w` copied from `s` to `d`, the two ranges apart. Compiled as a 16-byte `memcpy` within the array (one
16-byte load and one store). -/
@[extern c inline "({ lean_object * r_ = lean_sarray_ensure_exclusive(#1); __builtin_memcpy(lean_sarray_cptr(r_) + #2, lean_sarray_cptr(r_) + #3, 16); r_; })"]
def winCopy16 (w : ByteArray) (d s : USize)
    (_h : d.toNat + 16 ≤ w.size ∧ s.toNat + 16 ≤ w.size ∧ (s.toNat + 16 ≤ d.toNat ∨ d.toNat + 16 ≤ s.toNat)) :
    ByteArray :=
  w.copySlice s.toNat w d.toNat 16

/-- The bytes of a snapshot copy within one array, both ranges inside it. -/
theorem copySlice_self_get (w : ByteArray) (d s n i : Nat) (hd : d + n ≤ w.size) (hs : s + n ≤ w.size) :
    (w.copySlice s w d n).data[i]? = if d ≤ i ∧ i < d + n then w.data[s + (i - d)]? else w.data[i]? := by
  have hsz : w.size = w.data.size := rfl
  have hmin : min n (w.data.size - s) = n := by omega
  simp only [ByteArray.copySlice, hmin]
  rw [Array.getElem?_append, Array.getElem?_append]
  simp only [Array.size_append, Array.size_extract, Array.getElem?_extract]
  by_cases h1 : i < d
  · have : i < min d w.data.size - 0 := by omega
    simp only [this, ↓reduceIte, Nat.zero_add]
    have : ¬ (d ≤ i ∧ i < d + n) := by omega
    simp only [this, ↓reduceIte]
    have : i < min d w.data.size - 0 + (min (s + n) w.data.size - s) := by omega
    simp only [this, ↓reduceIte]
  · by_cases h2 : i < d + n
    · have hA : ¬ i < min d w.data.size - 0 := by omega
      have hB : i < min d w.data.size - 0 + (min (s + n) w.data.size - s) := by omega
      have hC : i - (min d w.data.size - 0) < min (s + n) w.data.size - s := by omega
      have hD : d ≤ i ∧ i < d + n := ⟨by omega, h2⟩
      simp only [hA, hB, hC, hD, ↓reduceIte, and_self]
      have : s + (i - (min d w.data.size - 0)) = s + (i - d) := by omega
      rw [this]
    · have hB : ¬ i < min d w.data.size - 0 + (min (s + n) w.data.size - s) := by omega
      have hD : ¬ (d ≤ i ∧ i < d + n) := by omega
      simp only [hB, hD, ↓reduceIte]
      by_cases h3 : i < w.data.size
      · have hC : i - (min d w.data.size - 0 + (min (s + n) w.data.size - s)) < min w.data.size w.data.size - (d + n) :=
          by omega
        simp only [hC, ↓reduceIte]
        have : d + n + (i - (min d w.data.size - 0 + (min (s + n) w.data.size - s))) = i := by omega
        rw [this]
      · have hC : ¬ i - (min d w.data.size - 0 + (min (s + n) w.data.size - s)) <
            min w.data.size w.data.size - (d + n) := by omega
        simp only [hC, ↓reduceIte]
        exact (Array.getElem?_eq_none (by omega)).symm

/-- `winMove`'s bytes. -/
theorem winMove_get (w : ByteArray) (d s n : USize) (h : d.toNat + n.toNat ≤ w.size ∧ s.toNat + n.toNat ≤ w.size)
    (i : Nat) :
    (winMove w d s n h).data[i]? =
      if d.toNat ≤ i ∧ i < d.toNat + n.toNat then w.data[s.toNat + (i - d.toNat)]? else w.data[i]? :=
  copySlice_self_get w d.toNat s.toNat n.toNat i h.1 h.2

/-- `winCopy16`'s bytes. -/
theorem winCopy16_get (w : ByteArray) (d s : USize)
    (h : d.toNat + 16 ≤ w.size ∧ s.toNat + 16 ≤ w.size ∧ (s.toNat + 16 ≤ d.toNat ∨ d.toNat + 16 ≤ s.toNat))
    (i : Nat) :
    (winCopy16 w d s h).data[i]? =
      if d.toNat ≤ i ∧ i < d.toNat + 16 then w.data[s.toNat + (i - d.toNat)]? else w.data[i]? :=
  copySlice_self_get w d.toNat s.toNat 16 i h.1 h.2.1

/-- The size of a snapshot copy within one array is the array's. -/
theorem copySlice_self_size (w : ByteArray) (d s n : Nat) (hd : d + n ≤ w.size) (hs : s + n ≤ w.size) :
    (w.copySlice s w d n).size = w.size := by
  have hsz : w.size = w.data.size := rfl
  have hmin : min n (w.data.size - s) = n := by omega
  show (w.copySlice s w d n).data.size = w.data.size
  simp only [ByteArray.copySlice, hmin, Array.size_append, Array.size_extract]
  omega

theorem winMove_size (w : ByteArray) (d s n : USize) (h : d.toNat + n.toNat ≤ w.size ∧ s.toNat + n.toNat ≤ w.size) :
    (winMove w d s n h).size = w.size :=
  copySlice_self_size w d.toNat s.toNat n.toNat h.1 h.2

theorem winCopy16_size (w : ByteArray) (d s : USize)
    (h : d.toNat + 16 ≤ w.size ∧ s.toNat + 16 ≤ w.size ∧ (s.toNat + 16 ≤ d.toNat ∨ d.toNat + 16 ≤ s.toNat)) :
    (winCopy16 w d s h).size = w.size :=
  copySlice_self_size w d.toNat s.toNat 16 h.1 h.2.1

/-- The format's copy within one array: byte `k` from `s + k` to `d + k`, in order, each read seeing the bytes written
before it (so a copy shorter-distanced than its length repeats bytes). -/
def fwdCopy (w : ByteArray) (d s : Nat) : Nat → ByteArray
  | 0 => w
  | k + 1 => let v := fwdCopy w d s k; ⟨v.data.setIfInBounds (d + k) (v.data[s + k]?.getD 0)⟩

theorem fwdCopy_size (w : ByteArray) (d s : Nat) : ∀ k, (fwdCopy w d s k).size = w.size
  | 0 => rfl
  | k + 1 => by
    show ((fwdCopy w d s k).data.setIfInBounds (d + k) _).size = w.size
    rw [Array.size_setIfInBounds]
    exact fwdCopy_size w d s k

/-- With the source ending before the destination begins, the format's copy reads only bytes it hasn't written. -/
theorem fwdCopy_get (w : ByteArray) (d s : Nat) :
    ∀ k, s + k ≤ d → d + k ≤ w.size → ∀ i,
      (fwdCopy w d s k).data[i]? = if d ≤ i ∧ i < d + k then w.data[s + (i - d)]? else w.data[i]?
  | 0, _, _, i => by
    have : ¬ (d ≤ i ∧ i < d + 0) := by omega
    simp only [this, ↓reduceIte]
    rfl
  | k + 1, hs, hd, i => by
    have ih := fwdCopy_get w d s k (by omega) (by omega)
    have hsz := fwdCopy_size w d s k
    have hsz' : (fwdCopy w d s k).data.size = w.data.size := hsz
    have hwsz : w.size = w.data.size := rfl
    -- the byte read, `s + k`, is before the destination, so it is the original byte
    have hread : (fwdCopy w d s k).data[s + k]? = w.data[s + k]? := by
      have hn : ¬ (d ≤ s + k ∧ s + k < d + k) := by omega
      rw [ih (s + k)]
      simp only [hn, ↓reduceIte]
    show ((fwdCopy w d s k).data.setIfInBounds (d + k) ((fwdCopy w d s k).data[s + k]?.getD 0))[i]? = _
    rw [hread, Array.getElem?_setIfInBounds]
    by_cases hi : d + k = i
    · subst hi
      have hlt : d + k < (fwdCopy w d s k).data.size := by omega
      have hin : d ≤ d + k ∧ d + k < d + (k + 1) := by omega
      have : s + (d + k - d) = s + k := by omega
      simp only [hlt, hin, ↓reduceIte, and_self, this]
      rw [Array.getElem?_eq_getElem (by omega : s + k < w.data.size)]
      rfl
    · simp only [hi, ↓reduceIte]
      rw [ih i]
      by_cases hr : d ≤ i ∧ i < d + k
      · have : d ≤ i ∧ i < d + (k + 1) := by omega
        simp only [hr, this, ↓reduceIte, and_self]
      · have : ¬ (d ≤ i ∧ i < d + (k + 1)) := by omega
        simp only [hr, this, ↓reduceIte]

/-! ### Fixed-width stores -/

/-- The low `n` bytes of `v`, little-endian. -/
def leList : UInt64 → Nat → List UInt8
  | _, 0 => []
  | v, n + 1 => v.toUInt8 :: leList (v >>> 8) n

theorem leList_length : ∀ (v : UInt64) (n : Nat), (leList v n).length = n
  | _, 0 => rfl
  | v, n + 1 => by rw [leList, List.length_cons, leList_length]

/-- The low `n` bytes of `v` written from `i`, little-endian: what the stores below are. -/
def storeLE (t : ByteArray) (i : USize) (v : UInt64) (n : Nat) : ByteArray :=
  (ByteArray.mk (leList v n).toArray).copySlice 0 t i.toNat n

/-- The bytes of a copy from the start of one array into another, both ranges inside them. -/
theorem copySlice_get (src t : ByteArray) (d n i : Nat) (hd : d + n ≤ t.size) (hs : n ≤ src.size) :
    (src.copySlice 0 t d n).data[i]? = if d ≤ i ∧ i < d + n then src.data[i - d]? else t.data[i]? := by
  have hsz : t.size = t.data.size := rfl
  have hss : src.size = src.data.size := rfl
  have hmd : min d t.data.size = d := by omega
  have hmn : min n src.data.size = n := by omega
  simp only [ByteArray.copySlice]
  rw [Array.getElem?_append, Array.getElem?_append]
  simp only [Array.size_append, Array.size_extract, Array.getElem?_extract, Nat.zero_add, Nat.sub_zero, Nat.min_self,
    hmd, hmn]
  by_cases h1 : i < d
  · have hD : ¬ d ≤ i := by omega
    have hB : i < d + n := by omega
    simp only [h1, hB, hD, ↓reduceIte, false_and]
  · by_cases h2 : i < d + n
    · have hC : i - d < n := by omega
      have hD : d ≤ i ∧ i < d + n := ⟨by omega, h2⟩
      simp only [h1, h2, hC, hD, ↓reduceIte, and_self]
    · simp only [h2, ↓reduceIte, and_false]
      by_cases h3 : i < t.data.size
      · have hC : i - (d + n) < t.data.size - (d + n) := by omega
        have e : d + n + (i - (d + n)) = i := by omega
        simp only [hC, ↓reduceIte, e]
      · have hC : ¬ i - (d + n) < t.data.size - (d + n) := by omega
        have e : t.data[i]? = none := Array.getElem?_eq_none (by omega)
        simp only [hC, ↓reduceIte, e]

/-- `storeLE`'s bytes: `v`'s from `i`, and the others as they were. -/
theorem storeLE_get (t : ByteArray) (i : USize) (v : UInt64) (n : Nat) (h : i.toNat + n ≤ t.size) (q : Nat) :
    (storeLE t i v n).data[q]? = if i.toNat ≤ q ∧ q < i.toNat + n then (leList v n)[q - i.toNat]? else t.data[q]? := by
  unfold storeLE
  rw [copySlice_get _ t i.toNat n q h (by
    show n ≤ (leList v n).toArray.size
    rw [List.size_toArray, leList_length]
    exact Nat.le_refl _)]
  simp only [List.getElem?_toArray]

theorem storeLE_size (t : ByteArray) (i : USize) (v : UInt64) (n : Nat) (h : i.toNat + n ≤ t.size) :
    (storeLE t i v n).size = t.size := by
  have hsz : t.size = t.data.size := rfl
  have hl : (leList v n).toArray.size = n := by rw [List.size_toArray, leList_length]
  show (storeLE t i v n).data.size = t.data.size
  simp only [storeLE, ByteArray.copySlice, Array.size_append, Array.size_extract, hl]
  omega

/-- `v`'s low 2 bytes written from `i`, little-endian. Compiled as one 2-byte store. -/
@[extern c inline "({ _Static_assert(__BYTE_ORDER__ == __ORDER_LITTLE_ENDIAN__, \"little-endian target\"); lean_object * r_ = lean_sarray_ensure_exclusive(#1); uint16_t v_ = (uint16_t)(#3); __builtin_memcpy(lean_sarray_cptr(r_) + #2, &v_, 2); r_; })"]
def store16 (t : ByteArray) (i : USize) (v : UInt64) (_h : i.toNat + 2 ≤ t.size) : ByteArray :=
  storeLE t i v 2

/-- `v`'s low 4 bytes written from `i`, little-endian. Compiled as one 4-byte store. -/
@[extern c inline "({ _Static_assert(__BYTE_ORDER__ == __ORDER_LITTLE_ENDIAN__, \"little-endian target\"); lean_object * r_ = lean_sarray_ensure_exclusive(#1); uint32_t v_ = (uint32_t)(#3); __builtin_memcpy(lean_sarray_cptr(r_) + #2, &v_, 4); r_; })"]
def store32 (t : ByteArray) (i : USize) (v : UInt64) (_h : i.toNat + 4 ≤ t.size) : ByteArray :=
  storeLE t i v 4

/-- `v`'s 8 bytes written from `i`, little-endian. Compiled as one 8-byte store. -/
@[extern c inline "({ _Static_assert(__BYTE_ORDER__ == __ORDER_LITTLE_ENDIAN__, \"little-endian target\"); lean_object * r_ = lean_sarray_ensure_exclusive(#1); uint64_t v_ = (uint64_t)(#3); __builtin_memcpy(lean_sarray_cptr(r_) + #2, &v_, 8); r_; })"]
def store64 (t : ByteArray) (i : USize) (v : UInt64) (_h : i.toNat + 8 ≤ t.size) : ByteArray :=
  storeLE t i v 8

/-- At a distance of at least its length, the format's copy is `winMove`'s snapshot. -/
theorem fwdCopy_eq_winMove (w : ByteArray) (d s n : USize)
    (h : d.toNat + n.toNat ≤ w.size ∧ s.toNat + n.toNat ≤ w.size) (hsep : s.toNat + n.toNat ≤ d.toNat) :
    fwdCopy w d.toNat s.toNat n.toNat = winMove w d s n h := by
  apply ByteArray.ext
  apply Array.ext_getElem?
  intro i
  rw [fwdCopy_get w d.toNat s.toNat n.toNat hsep h.1 i]
  exact (winMove_get w d s n h i).symm

/-- At a distance of at least 16, 16 bytes of the format's copy are `winCopy16`'s. -/
theorem fwdCopy_eq_winCopy16 (w : ByteArray) (d s : USize)
    (h : d.toNat + 16 ≤ w.size ∧ s.toNat + 16 ≤ w.size ∧ (s.toNat + 16 ≤ d.toNat ∨ d.toNat + 16 ≤ s.toNat))
    (hsep : s.toNat + 16 ≤ d.toNat) :
    fwdCopy w d.toNat s.toNat 16 = winCopy16 w d s h := by
  apply ByteArray.ext
  apply Array.ext_getElem?
  intro i
  rw [fwdCopy_get w d.toNat s.toNat 16 hsep h.1 i]
  exact (winCopy16_get w d s h i).symm
