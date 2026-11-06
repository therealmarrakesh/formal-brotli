module

public import Brotli.Decoder.StreamRaw

@[expose] public section

/-!
# Uncompressed bytes by whole copies

`rawRunF` is `rawRun` with a faster way to the same result: while the bit buffer is empty, `rawRun` refills exactly eight
bytes and then spends them one at a time, ending empty again eight bytes on. `rawRunF` moves as many such groups as the
run, the chunk and the window's end allow with one `copySlice` from the input into the window, which is a `memcpy` in
place since the window is held once, and takes `rawRun`'s own steps otherwise. `rawRun_eq_rawRunF` proves the two equal,
and `@[csimp]` makes the compiled code use `rawRunF`, so every proof about `rawRun` stands for what runs (design rule 1:
the same bytes are read and written, in the same order).
-/

namespace Brotli.Decoder

open Brotli.Spec

/-- `copySlice`'s bytes, for a copy that fits. -/
theorem copySlice_data_get {src dest : ByteArray} {so d m : Nat} {e : Bool} (hs : so + m ≤ src.size)
    (hd : d + m ≤ dest.size) (i : Nat) (hi : i < (src.copySlice so dest d m e).data.size) (hi' : i < dest.data.size) :
    (src.copySlice so dest d m e).data[i] =
      if h : d ≤ i ∧ i < d + m then src.data[so + (i - d)]'(by have : src.size = src.data.size := rfl; omega)
      else dest.data[i] := by
  have h1 : src.size = src.data.size := rfl
  have h2 : dest.size = dest.data.size := rfl
  simp only [ByteArray.copySlice, Array.getElem_append, Array.getElem_extract, Array.size_extract,
    Array.size_append]
  split
  · split
    · rw [dite_eq_right (show ¬(d ≤ i ∧ i < d + m) by omega)]
      congr 1
      omega
    · rw [dite_eq_left (show d ≤ i ∧ i < d + m by omega)]
      congr 1
      omega
  · rw [dite_eq_right (show ¬(d ≤ i ∧ i < d + m) by omega)]
    congr 1
    omega

theorem copySlice_size' {src dest : ByteArray} {so d m : Nat} {e : Bool} (hs : so + m ≤ src.size)
    (hd : d + m ≤ dest.size) : (src.copySlice so dest d m e).size = dest.size := by
  have h1 : src.size = src.data.size := rfl
  have h2 : dest.size = dest.data.size := rfl
  show (src.copySlice so dest d m e).data.size = dest.data.size
  simp only [ByteArray.copySlice, Array.size_append, Array.size_extract]
  omega

/-- One more byte of a copy is one more write. -/
theorem copySlice_succ {src dest : ByteArray} {so d m : Nat} {e : Bool} (hs : so + m + 1 ≤ src.size)
    (hd : d + m + 1 ≤ dest.size) :
    src.copySlice so dest d (m + 1) e =
      (src.copySlice so dest d m e).set (d + m) (src[so + m]'(by omega))
        (by rw [copySlice_size' (by omega) (by omega)]; omega) := by
  have h1 : src.size = src.data.size := rfl
  have h2 : dest.size = dest.data.size := rfl
  have s1 := copySlice_size' (src := src) (dest := dest) (so := so) (d := d) (m := m + 1) (e := e) (by omega) (by omega)
  have s0 := copySlice_size' (src := src) (dest := dest) (so := so) (d := d) (m := m) (e := e) (by omega) (by omega)
  have s0' : (src.copySlice so dest d m e).data.size = dest.data.size := s0
  have s1' : (src.copySlice so dest d (m + 1) e).data.size = dest.data.size := s1
  apply ByteArray.ext_getElem
  · show _ = ((src.copySlice so dest d m e).data.set (d + m) _ _).size
    rw [Array.size_set]
    exact s1.trans s0.symm
  · intro i hi hi'
    have hi2 : i < dest.data.size := by
      have : (src.copySlice so dest d (m + 1) e).size = (src.copySlice so dest d (m + 1) e).data.size := rfl
      omega
    simp only [ByteArray.getElem_eq_getElem_data, ByteArray.data_set, Array.getElem_set]
    rw [copySlice_data_get (by omega) (by omega) i (by omega) hi2]
    by_cases he : d + m = i
    · rw [ite_eq_left he, dite_eq_left (show d ≤ i ∧ i < d + (m + 1) by omega)]
      congr 1
      omega
    · rw [ite_eq_right he, copySlice_data_get (by omega) (by omega) i (by omega) hi2]
      by_cases hin : d ≤ i ∧ i < d + m
      · rw [dite_eq_left (show d ≤ i ∧ i < d + (m + 1) by omega), dite_eq_left hin]
      · rw [dite_eq_right (show ¬(d ≤ i ∧ i < d + (m + 1)) by omega), dite_eq_right hin]

/-- A copy of none leaves the array. -/
theorem copySlice_zero' {src dest : ByteArray} {so d : Nat} {e : Bool} (hso : so ≤ src.size) (hd : d ≤ dest.size) :
    src.copySlice so dest d 0 e = dest := by
  have s0 := copySlice_size' (src := src) (dest := dest) (so := so) (d := d) (m := 0) (e := e) (by omega) (by omega)
  apply ByteArray.ext_getElem s0
  intro i hi hi'
  have hi2 : i < dest.data.size := hi'
  have hi3 : i < (src.copySlice so dest d 0 e).data.size := hi
  simp only [ByteArray.getElem_eq_getElem_data]
  rw [copySlice_data_get (by omega) (by omega) i hi3 hi2, dite_eq_right (show ¬(d ≤ i ∧ i < d + 0) by omega)]

/-- The word of `loadBuffer`, as a number. -/
theorem loadBuffer_word {a : ByteArray} {i : USize} {h8 : i.toNat + 8 ≤ a.size} {hu : i.toNat + 8 ≤ USize.size} :
    (loadBuffer a i h8 hu).word.toNat =
      (byteAt a i 0 (by decide) h8 hu).toNat + 2 ^ 8 * (byteAt a i 1 (by decide) h8 hu).toNat +
      2 ^ 16 * (byteAt a i 2 (by decide) h8 hu).toNat + 2 ^ 24 * (byteAt a i 3 (by decide) h8 hu).toNat +
      2 ^ 32 * (byteAt a i 4 (by decide) h8 hu).toNat + 2 ^ 40 * (byteAt a i 5 (by decide) h8 hu).toNat +
      2 ^ 48 * (byteAt a i 6 (by decide) h8 hu).toNat + 2 ^ 56 * (byteAt a i 7 (by decide) h8 hu).toNat := by
  have step : ∀ (b : BitBuffer) (x : UInt8) (c : Nat), b.Wf → b.count.toNat = c → c ≤ 56 →
      (b.push x).Wf ∧ (b.push x).count.toNat = c + 8 ∧ (b.push x).word.toNat = b.word.toNat + 2 ^ c * x.toNat := by
    intro b x c hw hc hc56
    subst hc
    exact ⟨BitBuffer.push_wf x hw hc56, BitBuffer.push_count hc56, push_word hw hc56⟩
  unfold loadBuffer
  have w0 : (BitBuffer.mk 0 0).Wf := BitBuffer.empty_wf
  obtain ⟨w1, c1, e1⟩ := step _ (byteAt a i 0 (by decide) h8 hu) 0 w0 rfl (by decide)
  obtain ⟨w2, c2, e2⟩ := step _ (byteAt a i 1 (by decide) h8 hu) 8 w1 c1 (by decide)
  obtain ⟨w3, c3, e3⟩ := step _ (byteAt a i 2 (by decide) h8 hu) 16 w2 c2 (by decide)
  obtain ⟨w4, c4, e4⟩ := step _ (byteAt a i 3 (by decide) h8 hu) 24 w3 c3 (by decide)
  obtain ⟨w5, c5, e5⟩ := step _ (byteAt a i 4 (by decide) h8 hu) 32 w4 c4 (by decide)
  obtain ⟨w6, c6, e6⟩ := step _ (byteAt a i 5 (by decide) h8 hu) 40 w5 c5 (by decide)
  obtain ⟨w7, c7, e7⟩ := step _ (byteAt a i 6 (by decide) h8 hu) 48 w6 c6 (by decide)
  obtain ⟨_, _, e8⟩ := step _ (byteAt a i 7 (by decide) h8 hu) 56 w7 c7 (by decide)
  rw [e8, e7, e6, e5, e4, e3, e2, e1]
  have : (BitBuffer.mk 0 0).word.toNat = 0 := rfl
  rw [this]
  omega

/-- A composed copy is one copy. -/
theorem copySlice_comp {src dest : ByteArray} {so d m l : Nat} (hs : so + m + l ≤ src.size)
    (hd : d + m + l ≤ dest.size) :
    src.copySlice (so + m) (src.copySlice so dest d m false) (d + m) l false = src.copySlice so dest d (m + l) false := by
  have s1 := copySlice_size' (src := src) (dest := dest) (so := so) (d := d) (m := m) (e := false) (by omega) (by omega)
  have s2 := copySlice_size' (src := src) (dest := src.copySlice so dest d m false) (so := so + m) (d := d + m) (m := l)
    (e := false) (by omega) (by omega)
  have s3 := copySlice_size' (src := src) (dest := dest) (so := so) (d := d) (m := m + l) (e := false) (by omega)
    (by omega)
  have d1 : (src.copySlice so dest d m false).data.size = dest.data.size := s1
  have d2 : (src.copySlice (so + m) (src.copySlice so dest d m false) (d + m) l false).data.size = dest.data.size :=
    s2.trans s1
  have d3 : (src.copySlice so dest d (m + l) false).data.size = dest.data.size := s3
  apply ByteArray.ext_getElem ((s2.trans s1).trans s3.symm)
  intro i hi hi'
  have hi2 : i < dest.data.size := by
    have : (src.copySlice so dest d (m + l) false).size = (src.copySlice so dest d (m + l) false).data.size := rfl
    omega
  simp only [ByteArray.getElem_eq_getElem_data]
  rw [copySlice_data_get (src := src) (dest := src.copySlice so dest d m false) (so := so + m) (d := d + m) (m := l)
      (by omega) (by omega) i (by omega) (by omega),
    copySlice_data_get (src := src) (dest := dest) (so := so) (d := d) (m := m + l) (by omega) (by omega) i (by omega)
      hi2]
  by_cases h1 : d + m ≤ i ∧ i < d + m + l
  · rw [dite_eq_left h1, dite_eq_left (show d ≤ i ∧ i < d + (m + l) by omega)]
    congr 1
    omega
  · rw [dite_eq_right h1, copySlice_data_get (by omega) (by omega) i (by omega) hi2]
    by_cases h2 : d ≤ i ∧ i < d + m
    · rw [dite_eq_left h2, dite_eq_left (show d ≤ i ∧ i < d + (m + l) by omega)]
    · rw [dite_eq_right h2, dite_eq_right (show ¬(d ≤ i ∧ i < d + (m + l)) by omega)]

/-! ### USize facts -/

theorem u_add {a b : USize} (h : a.toNat + b.toNat < USize.size) : (a + b).toNat = a.toNat + b.toNat := by
  rw [USize.toNat_add]
  exact Nat.mod_eq_of_lt h

theorem u_sub {a b : USize} (h : b.toNat ≤ a.toNat) : (a - b).toNat = a.toNat - b.toNat :=
  USize.toNat_sub_of_le _ _ (USize.le_iff_toNat_le.mpr h)

theorem u_of {n : Nat} (h : n < 2 ^ 32) : (USize.ofNat n).toNat = n := by
  rw [USize.toNat_ofNat', ← USize.size_eq_two_pow]
  have := USize.le_size
  exact Nat.mod_eq_of_lt (by omega)

theorem u_and {x mask : USize} {k : Nat} (hm : mask.toNat = 2 ^ k - 1) :
    (x &&& mask).toNat = x.toNat % 2 ^ k := by
  rw [USize.toNat_and, hm]
  exact Nat.and_two_pow_sub_one_eq_mod _ _

private theorem shr8 (x : UInt64) : (x >>> 8).toNat = x.toNat / 256 := by
  rw [UInt64.toNat_shiftRight]
  show x.toNat >>> 8 = _
  rw [Nat.shiftRight_eq_div_pow]

/-- The load's word, a byte at a time from the bottom. -/
theorem loadBuffer_horner {a : ByteArray} {p : USize} (h8a : p.toNat + 8 ≤ a.size) (hu : p.toNat + 8 ≤ USize.size) :
    (loadBuffer a p h8a hu).word.toNat = (a.data[p.toNat + 0]'(by have : a.size = a.data.size := rfl; omega)).toNat +
      256 * ((a.data[p.toNat + 1]'(by have : a.size = a.data.size := rfl; omega)).toNat + 256 *
      ((a.data[p.toNat + 2]'(by have : a.size = a.data.size := rfl; omega)).toNat + 256 *
      ((a.data[p.toNat + 3]'(by have : a.size = a.data.size := rfl; omega)).toNat + 256 *
      ((a.data[p.toNat + 4]'(by have : a.size = a.data.size := rfl; omega)).toNat + 256 *
      ((a.data[p.toNat + 5]'(by have : a.size = a.data.size := rfl; omega)).toNat + 256 *
      ((a.data[p.toNat + 6]'(by have : a.size = a.data.size := rfl; omega)).toNat + 256 *
      (a.data[p.toNat + 7]'(by have : a.size = a.data.size := rfl; omega)).toNat)))))) := by
  rw [loadBuffer_word]
  simp only [byteAt_eq, Nat.reducePow]
  omega

/-- One byte off the bottom of a word. -/
private theorem peel {x : UInt64} {b T : Nat} (hb : b < 256) (hx : x.toNat = b + 256 * T) :
    (x >>> 8).toNat = T ∧ x.toUInt8.toNat = b := by
  rw [shr8, UInt64.toNat_toUInt8, hx]
  constructor <;> omega

/-- The load's eight bytes, from the bottom, are the chunk's next eight, and nothing is left above them. -/
theorem load_bytes {a : ByteArray} {p : USize} (h8a : p.toNat + 8 ≤ a.size) (hu : p.toNat + 8 ≤ USize.size) :
    (loadBuffer a p h8a hu).word >>> 8 >>> 8 >>> 8 >>> 8 >>> 8 >>> 8 >>> 8 >>> 8 = 0 ∧
    (loadBuffer a p h8a hu).word.toUInt8 = a.data[p.toNat + 0]'(by have : a.size = a.data.size := rfl; omega) ∧
    ((loadBuffer a p h8a hu).word >>> 8).toUInt8 = a.data[p.toNat + 1]'(by have : a.size = a.data.size := rfl; omega) ∧
    ((loadBuffer a p h8a hu).word >>> 8 >>> 8).toUInt8 =
      a.data[p.toNat + 2]'(by have : a.size = a.data.size := rfl; omega) ∧
    ((loadBuffer a p h8a hu).word >>> 8 >>> 8 >>> 8).toUInt8 =
      a.data[p.toNat + 3]'(by have : a.size = a.data.size := rfl; omega) ∧
    ((loadBuffer a p h8a hu).word >>> 8 >>> 8 >>> 8 >>> 8).toUInt8 =
      a.data[p.toNat + 4]'(by have : a.size = a.data.size := rfl; omega) ∧
    ((loadBuffer a p h8a hu).word >>> 8 >>> 8 >>> 8 >>> 8 >>> 8).toUInt8 =
      a.data[p.toNat + 5]'(by have : a.size = a.data.size := rfl; omega) ∧
    ((loadBuffer a p h8a hu).word >>> 8 >>> 8 >>> 8 >>> 8 >>> 8 >>> 8).toUInt8 =
      a.data[p.toNat + 6]'(by have : a.size = a.data.size := rfl; omega) ∧
    ((loadBuffer a p h8a hu).word >>> 8 >>> 8 >>> 8 >>> 8 >>> 8 >>> 8 >>> 8).toUInt8 =
      a.data[p.toNat + 7]'(by have : a.size = a.data.size := rfl; omega) := by
  have hd : a.size = a.data.size := rfl
  have c0 := (a.data[p.toNat + 0]'(by omega)).toNat_lt
  have c1 := (a.data[p.toNat + 1]'(by omega)).toNat_lt
  have c2 := (a.data[p.toNat + 2]'(by omega)).toNat_lt
  have c3 := (a.data[p.toNat + 3]'(by omega)).toNat_lt
  have c4 := (a.data[p.toNat + 4]'(by omega)).toNat_lt
  have c5 := (a.data[p.toNat + 5]'(by omega)).toNat_lt
  have c6 := (a.data[p.toNat + 6]'(by omega)).toNat_lt
  have c7 := (a.data[p.toNat + 7]'(by omega)).toNat_lt
  have hH := loadBuffer_horner h8a hu
  obtain ⟨w1, y0⟩ := peel c0 hH
  obtain ⟨w2, y1⟩ := peel c1 w1
  obtain ⟨w3, y2⟩ := peel c2 w2
  obtain ⟨w4, y3⟩ := peel c3 w3
  obtain ⟨w5, y4⟩ := peel c4 w4
  obtain ⟨w6, y5⟩ := peel c5 w5
  obtain ⟨w7, y6⟩ := peel c6 w6
  obtain ⟨w8, y7⟩ := peel (T := 0) c7 (w7.trans (by omega))
  exact ⟨UInt64.toNat_inj.mp w8, UInt8.toNat_inj.mp y0, UInt8.toNat_inj.mp y1, UInt8.toNat_inj.mp y2,
    UInt8.toNat_inj.mp y3, UInt8.toNat_inj.mp y4, UInt8.toNat_inj.mp y5, UInt8.toNat_inj.mp y6, UInt8.toNat_inj.mp y7⟩

private theorem ringNext_toNat' {q mask : USize} {k : Nat} (hk : k ≤ 24) (hm : mask.toNat = 2 ^ k - 1)
    (hq : q.toNat < 2 ^ k) : (ringNext q mask).toNat = (q.toNat + 1) % 2 ^ k := by
  have hR : 2 ^ k ≤ 2 ^ 24 := Nat.pow_le_pow_right (by decide) hk
  have h24 : (2 : Nat) ^ 24 = 16777216 := by decide
  have hU := USize.le_size
  unfold ringNext
  rw [u_and hm, u_add (by rw [u_of (by decide)]; omega), u_of (by decide)]

private theorem uget_get {a : ByteArray} {i : USize} (h : i.toNat < a.size) : a.uget i h = a[i.toNat] := by
  cases a
  rfl

private theorem ringWrite_set {r : ByteArray} {q : USize} {v : UInt8} (h : q.toNat < r.size) :
    ringWrite r q v h = r.set q.toNat v h := by
  cases r
  rfl

/-- Writing the next byte of a copy at the next position extends the copy by one. -/
theorem fold_eq {a r : ByteArray} {p wp q : USize} {m : Nat} {v : UInt8} (hpa : p.toNat + m + 1 ≤ a.size)
    (hwr : wp.toNat + m + 1 ≤ r.size) (hq : q.toNat = wp.toNat + m)
    (hv : v = a.data[p.toNat + m]'(by have : a.size = a.data.size := rfl; omega))
    (h : q.toNat < (a.copySlice p.toNat r wp.toNat m false).size) :
    ringWrite (a.copySlice p.toNat r wp.toNat m false) q v h = a.copySlice p.toNat r wp.toNat (m + 1) false := by
  rw [copySlice_succ hpa hwr, ringWrite_set]
  congr 1

/-! ### The groups -/

/-- The whole groups of eight bytes a run can move by one copy: by the run, the chunk and the window's end. -/
@[inline] def rawGroups (n pos stop mask wpos : USize) : USize :=
  usmin (n / USize.ofNat 8) (usmin ((stop - pos) / USize.ofNat 8) ((mask + USize.ofNat 1 - wpos) / USize.ofNat 8))

theorem rawGroups_toNat {n pos stop mask wpos : USize} {k : Nat} (hk : k ≤ 24) (hmask : mask.toNat = 2 ^ k - 1)
    (hp : pos.toNat ≤ stop.toNat) (hwp : wpos.toNat < 2 ^ k) :
    (rawGroups n pos stop mask wpos).toNat =
      min (n.toNat / 8) (min ((stop.toNat - pos.toNat) / 8) ((2 ^ k - wpos.toNat) / 8)) := by
  have hR : 2 ^ k ≤ 2 ^ 24 := Nat.pow_le_pow_right (by decide) hk
  have h24 : (2 : Nat) ^ 24 = 16777216 := by decide
  have hU := USize.le_size
  have h1 : (mask + USize.ofNat 1).toNat = 2 ^ k := by
    have := Nat.one_le_two_pow (n := k)
    rw [u_add (by rw [u_of (by decide)]; omega), u_of (by decide), hmask]
    omega
  have h8 : (USize.ofNat 8).toNat = 8 := u_of (by decide)
  unfold rawGroups
  rw [usmin_toNat, usmin_toNat, USize.toNat_div, USize.toNat_div, USize.toNat_div, h8, u_sub hp,
    u_sub (by rw [h1]; omega), h1]

/-- The groups fit the run, the chunk and the window's end. -/
theorem rawGroups_le {n pos stop mask wpos : USize} {k : Nat} (hk : k ≤ 24) (hmask : mask.toNat = 2 ^ k - 1)
    (hp : pos.toNat ≤ stop.toNat) (hwp : wpos.toNat < 2 ^ k) :
    (rawGroups n pos stop mask wpos).toNat * 8 ≤ n.toNat ∧
      pos.toNat + (rawGroups n pos stop mask wpos).toNat * 8 ≤ stop.toNat ∧
      wpos.toNat + (rawGroups n pos stop mask wpos).toNat * 8 ≤ 2 ^ k := by
  rw [rawGroups_toNat hk hmask hp hwp]
  generalize hD : stop.toNat - pos.toNat = D
  generalize hE : 2 ^ k - wpos.toNat = E
  have h1 : pos.toNat + D = stop.toNat := by omega
  have h2 : wpos.toNat + E = 2 ^ k := by omega
  omega

/-- `rawRun`, moving whole groups of eight bytes by one `copySlice` while the buffer is empty. -/
def rawRunF (a : ByteArray) (stop : USize) (hs : stop.toNat ≤ a.size) (mask : USize) (k : Nat) (hk : k ≤ 24)
    (hmask : mask.toNat = 2 ^ k - 1) (n : USize) (word count : UInt64) (pos : USize) (ring : ByteArray) (wpos : USize)
    (p1 p2 : UInt8) (hp : pos.toNat ≤ stop.toNat) (hsize : ring.size = 2 ^ k) (hwp : wpos.toNat < 2 ^ k) : RawRun :=
  if hn : n = 0 then ⟨word, count, pos, ring, wpos, p1, p2, n⟩
  else if hg : word = 0 ∧ count = 0 ∧ rawGroups n pos stop mask wpos ≠ 0 then
    have hG := rawGroups_le (n := n) hk hmask hp hwp
    have hg0 := usize_ne hg.2.2
    have hst := stop.toNat_lt_size
    have hsz : USize.size = 2 ^ System.Platform.numBits := USize.size_eq_two_pow
    have hU := USize.le_size
    have hnU := n.toNat_lt_size
    have hR : 2 ^ k ≤ 2 ^ 24 := Nat.pow_le_pow_right (by decide) hk
    have h24 : (2 : Nat) ^ 24 = 16777216 := by decide
    have hm : (rawGroups n pos stop mask wpos * USize.ofNat 8).toNat = (rawGroups n pos stop mask wpos).toNat * 8 := by
      rw [USize.toNat_mul, u_of (by decide)]
      exact Nat.mod_eq_of_lt (by omega)
    have hpe : (pos + rawGroups n pos stop mask wpos * USize.ofNat 8).toNat =
        pos.toNat + (rawGroups n pos stop mask wpos * USize.ofNat 8).toNat := u_add (by omega)
    have h1 : (pos + rawGroups n pos stop mask wpos * USize.ofNat 8 - USize.ofNat 1).toNat =
        pos.toNat + (rawGroups n pos stop mask wpos * USize.ofNat 8).toNat - 1 := by
      rw [u_sub (by rw [u_of (by decide), hpe]; omega), hpe, u_of (by decide)]
    have h2 : (pos + rawGroups n pos stop mask wpos * USize.ofNat 8 - USize.ofNat 2).toNat =
        pos.toNat + (rawGroups n pos stop mask wpos * USize.ofNat 8).toNat - 2 := by
      rw [u_sub (by rw [u_of (by decide), hpe]; omega), hpe, u_of (by decide)]
    rawRunF a stop hs mask k hk hmask (n - rawGroups n pos stop mask wpos * USize.ofNat 8) 0 0
      (pos + rawGroups n pos stop mask wpos * USize.ofNat 8)
      (a.copySlice pos.toNat ring wpos.toNat (rawGroups n pos stop mask wpos * USize.ofNat 8).toNat false)
      ((wpos + rawGroups n pos stop mask wpos * USize.ofNat 8) &&& mask)
      (a.uget (pos + rawGroups n pos stop mask wpos * USize.ofNat 8 - USize.ofNat 1) (by rw [h1]; omega))
      (a.uget (pos + rawGroups n pos stop mask wpos * USize.ofNat 8 - USize.ofNat 2) (by rw [h2]; omega))
      (by rw [hpe]; omega) ((copySlice_size' (by omega) (by omega)).trans hsize)
      (by rw [u_and hmask]; exact Nat.mod_lt _ (Nat.two_pow_pos _))
  else
    have hnext : (ringNext wpos mask).toNat < 2 ^ k := by
      unfold ringNext
      rw [USize.toNat_and, hmask, Nat.and_two_pow_sub_one_eq_mod]
      exact Nat.mod_lt _ (Nat.two_pow_pos _)
    have hr : wpos.toNat < ring.size := by omega
    if 8 ≤ count then
      let byte := word.toUInt8
      rawRunF a stop hs mask k hk hmask (n - USize.ofNat 1) (word >>> 8) (count - 8) pos (ringWrite ring wpos byte hr)
        (ringNext wpos mask) byte p1 hp ((size_ringWrite ring wpos byte hr).trans hsize) hnext
    else
      let r := refill word count a pos stop hs hp
      if h8 : 8 ≤ r.count ∧ r.pos ≤ stop then
        let byte := r.word.toUInt8
        rawRunF a stop hs mask k hk hmask (n - USize.ofNat 1) (r.word >>> 8) (r.count - 8) r.pos
          (ringWrite ring wpos byte hr) (ringNext wpos mask) byte p1 (USize.le_iff_toNat_le.mp h8.2)
          ((size_ringWrite ring wpos byte hr).trans hsize) hnext
      else ⟨r.word, r.count, r.pos, ring, wpos, p1, p2, n⟩
termination_by n.toNat
decreasing_by
  all_goals first
    | (have := usize_pred hn; have := usize_ne hn; omega)
    | (rw [u_sub (by omega)]; omega)

section
variable {a : ByteArray} {stop : USize} {hs : stop.toNat ≤ a.size} {mask : USize} {k : Nat} {hk : k ≤ 24}
  {hmask : mask.toNat = 2 ^ k - 1}

theorem rawRun_congr {n n' : USize} {w w' c c' : UInt64} {p p' : USize} {r r' : ByteArray} {wp wp' : USize}
    {x1 x1' x2 x2' : UInt8} (e1 : n = n') (e2 : w = w') (e3 : c = c') (e4 : p = p') (e5 : r = r') (e6 : wp = wp')
    (e7 : x1 = x1') (e8 : x2 = x2') (hp : p.toNat ≤ stop.toNat) (hsize : r.size = 2 ^ k) (hwp : wp.toNat < 2 ^ k)
    (hp' : p'.toNat ≤ stop.toNat) (hsize' : r'.size = 2 ^ k) (hwp' : wp'.toNat < 2 ^ k) :
    rawRun a stop hs mask k hk hmask n w c p r wp x1 x2 hp hsize hwp =
      rawRun a stop hs mask k hk hmask n' w' c' p' r' wp' x1' x2' hp' hsize' hwp' := by
  subst e1 e2 e3 e4 e5 e6 e7 e8
  rfl

theorem rawRun_ring {n : USize} {w c : UInt64} {p : USize} {r r' : ByteArray} {wp : USize} {x1 x2 : UInt8}
    (e : r = r') {hp : p.toNat ≤ stop.toNat} {hsize : r.size = 2 ^ k} {hwp : wp.toNat < 2 ^ k} :
    rawRun a stop hs mask k hk hmask n w c p r wp x1 x2 hp hsize hwp =
      rawRun a stop hs mask k hk hmask n w c p r' wp x1 x2 hp (e ▸ hsize) hwp := by
  subst e
  rfl

/-- A byte from a buffer holding one. -/
theorem rawRun_byte {n : USize} {w c : UInt64} {p : USize} {r : ByteArray} {wp : USize} {x1 x2 : UInt8}
    {hp : p.toNat ≤ stop.toNat} {hsize : r.size = 2 ^ k} {hwp : wp.toNat < 2 ^ k} (hn : n ≠ 0) (h8 : 8 ≤ c) :
    rawRun a stop hs mask k hk hmask n w c p r wp x1 x2 hp hsize hwp =
      rawRun a stop hs mask k hk hmask (n - USize.ofNat 1) (w >>> 8) (c - 8) p
        (ringWrite r wp w.toUInt8 (by omega)) (ringNext wp mask) w.toUInt8 x1 hp
        ((size_ringWrite r wp w.toUInt8 (by omega)).trans hsize)
        (by rw [ringNext_toNat' hk hmask hwp]; exact Nat.mod_lt _ (Nat.two_pow_pos _)) := by
  rw [rawRun, dite_eq_right hn]
  dsimp only
  rw [ite_eq_left h8]

/-- With the buffer empty and eight bytes left in the chunk, a refill takes all eight. -/
theorem refill_zero {p : USize} (hp : p.toNat ≤ stop.toNat) (h8 : p.toNat + 8 ≤ stop.toNat)
    (h8a : p.toNat + 8 ≤ a.size) (hu : p.toNat + 8 ≤ USize.size) :
    refill 0 0 a p stop hs hp = ⟨(loadBuffer a p h8a hu).word, 64, p + USize.ofNat 8⟩ := by
  have hc : USize.ofNat 8 ≤ stop - p := USize.le_iff_toNat_le.mpr (by rw [u_of (by decide), u_sub hp]; omega)
  unfold refill
  rw [ite_eq_right (show ¬ ((56 : UInt64) < 0) by decide), dite_eq_left hc]
  simp only [BitBuffer.fill]
  have e1 : (64 : UInt64) - ((64 : UInt64) - 0) >>> (3 : UInt64) <<< (3 : UInt64) = 0 := by decide
  have e2 : (0 : UInt64) + ((64 : UInt64) - 0) >>> (3 : UInt64) <<< (3 : UInt64) = 64 := by decide
  have e3 : (((64 : UInt64) - 0) >>> 3).toUSize = USize.ofNat 8 := by
    apply USize.toNat_inj.mp
    have h8' : (((64 : UInt64) - 0) >>> 3).toNat = 8 := by decide
    have hsz : USize.size = 2 ^ System.Platform.numBits := USize.size_eq_two_pow
    have hU := USize.le_size
    rw [UInt64.toNat_toUSize, h8', u_of (by decide)]
    exact Nat.mod_eq_of_lt (by omega)
  rw [e1, e2, e3]
  have e4 : ∀ x : UInt64, 0 ||| x <<< (0 : UInt64) >>> (0 : UInt64) <<< (0 : UInt64) = x := by
    intro x
    apply UInt64.toNat_inj.mp
    simp
  rw [e4]

/-- With the buffer empty and eight bytes left in the chunk: the refill, and the first of them. -/
theorem rawRun_fill {n p : USize} {r : ByteArray} {wp : USize} {x1 x2 : UInt8}
    {hp : p.toNat ≤ stop.toNat} {hsize : r.size = 2 ^ k} {hwp : wp.toNat < 2 ^ k} (hn : n ≠ 0)
    (h8 : p.toNat + 8 ≤ stop.toNat) :
    rawRun a stop hs mask k hk hmask n 0 0 p r wp x1 x2 hp hsize hwp =
      rawRun a stop hs mask k hk hmask (n - USize.ofNat 1)
        ((loadBuffer a p (by omega) (by have := stop.toNat_lt_size; omega)).word >>> 8) (64 - 8) (p + USize.ofNat 8)
        (ringWrite r wp (loadBuffer a p (by omega) (by have := stop.toNat_lt_size; omega)).word.toUInt8 (by omega))
        (ringNext wp mask) (loadBuffer a p (by omega) (by have := stop.toNat_lt_size; omega)).word.toUInt8 x1
        (by have := stop.toNat_lt_size; rw [u_add (by rw [u_of (by decide)]; omega), u_of (by decide)]; omega)
        ((size_ringWrite r wp _ (by omega)).trans hsize)
        (by rw [ringNext_toNat' hk hmask hwp]; exact Nat.mod_lt _ (Nat.two_pow_pos _)) := by
  have hst := stop.toNat_lt_size
  have hrf := refill_zero (hs := hs) hp h8 (by omega) (by omega)
  have hpe : (p + USize.ofNat 8).toNat = p.toNat + 8 := by
    rw [u_add (by rw [u_of (by decide)]; omega), u_of (by decide)]
  rw [rawRun, dite_eq_right hn]
  dsimp only
  rw [ite_eq_right (show ¬ ((8 : UInt64) ≤ 0) by decide)]
  simp only [hrf]
  rw [dite_eq_left ⟨(by decide : (8 : UInt64) ≤ 64), USize.le_iff_toNat_le.mpr (by rw [hpe]; omega)⟩]

/-- With the buffer empty, eight bytes left in the chunk and eight before the window's end, a group of eight is one
copy. -/
theorem rawRun_group {n p : USize} {r : ByteArray} {wp : USize} {x1 x2 : UInt8}
    {hp : p.toNat ≤ stop.toNat} {hsize : r.size = 2 ^ k} {hwp : wp.toNat < 2 ^ k}
    (hn : 8 ≤ n.toNat) (h8 : p.toNat + 8 ≤ stop.toNat) (hw8 : wp.toNat + 8 ≤ 2 ^ k)
    {hp' : (p + USize.ofNat 8).toNat ≤ stop.toNat} {hsize' : (a.copySlice p.toNat r wp.toNat 8 false).size = 2 ^ k}
    {hwp' : ((wp + USize.ofNat 8) &&& mask).toNat < 2 ^ k} :
    rawRun a stop hs mask k hk hmask n 0 0 p r wp x1 x2 hp hsize hwp =
      rawRun a stop hs mask k hk hmask (n - USize.ofNat 8) 0 0 (p + USize.ofNat 8)
        (a.copySlice p.toNat r wp.toNat 8 false) ((wp + USize.ofNat 8) &&& mask)
        (a[p.toNat + 7]'(by omega)) (a[p.toNat + 6]'(by omega)) hp' hsize' hwp' := by
  have hst := stop.toNat_lt_size
  have hU := USize.le_size
  have hR : 2 ^ k ≤ 2 ^ 24 := Nat.pow_le_pow_right (by decide) hk
  have h24 : (2 : Nat) ^ 24 = 16777216 := by decide
  have hsub : ∀ x : USize, 1 ≤ x.toNat → (x - USize.ofNat 1).toNat = x.toNat - 1 := fun x hx => by
    rw [u_sub (by rw [u_of (by decide)]; omega), u_of (by decide)]
  have hne : ∀ x : USize, 1 ≤ x.toNat → x ≠ 0 := fun x hx e => by
    rw [e] at hx
    exact absurd hx (by decide)
  have n1 := hsub n (by omega)
  have n2 := hsub (n - USize.ofNat 1) (by omega)
  have n3 := hsub (n - USize.ofNat 1 - USize.ofNat 1) (by omega)
  have n4 := hsub (n - USize.ofNat 1 - USize.ofNat 1 - USize.ofNat 1) (by omega)
  have n5 := hsub (n - USize.ofNat 1 - USize.ofNat 1 - USize.ofNat 1 - USize.ofNat 1) (by omega)
  have n6 := hsub (n - USize.ofNat 1 - USize.ofNat 1 - USize.ofNat 1 - USize.ofNat 1 - USize.ofNat 1) (by omega)
  have n7 := hsub (n - USize.ofNat 1 - USize.ofNat 1 - USize.ofNat 1 - USize.ofNat 1 - USize.ofNat 1 - USize.ofNat 1)
    (by omega)
  have n8 := hsub (n - USize.ofNat 1 - USize.ofNat 1 - USize.ofNat 1 - USize.ofNat 1 - USize.ofNat 1 - USize.ofNat 1 -
    USize.ofNat 1) (by omega)
  have h8a : p.toNat + 8 ≤ a.size := by omega
  have hu : p.toNat + 8 ≤ USize.size := by omega
  have hz := load_bytes h8a hu
  have w8 := hz.1
  have z0 := hz.2.1
  have z1 := hz.2.2.1
  have z2 := hz.2.2.2.1
  have z3 := hz.2.2.2.2.1
  have z4 := hz.2.2.2.2.2.1
  have z5 := hz.2.2.2.2.2.2.1
  have z6 := hz.2.2.2.2.2.2.2.1
  have z7 := hz.2.2.2.2.2.2.2.2
  -- the positions written
  have hq1 : (ringNext wp mask).toNat = wp.toNat + 1 := by
    rw [ringNext_toNat' hk hmask hwp]
    exact Nat.mod_eq_of_lt (by omega)
  have hq2 : (ringNext (ringNext wp mask) mask).toNat = wp.toNat + 2 := by
    rw [ringNext_toNat' hk hmask (by omega), hq1]
    exact Nat.mod_eq_of_lt (by omega)
  have hq3 : (ringNext (ringNext (ringNext wp mask) mask) mask).toNat = wp.toNat + 3 := by
    rw [ringNext_toNat' hk hmask (by omega), hq2]
    exact Nat.mod_eq_of_lt (by omega)
  have hq4 : (ringNext (ringNext (ringNext (ringNext wp mask) mask) mask) mask).toNat = wp.toNat + 4 := by
    rw [ringNext_toNat' hk hmask (by omega), hq3]
    exact Nat.mod_eq_of_lt (by omega)
  have hq5 : (ringNext (ringNext (ringNext (ringNext (ringNext wp mask) mask) mask) mask) mask).toNat =
      wp.toNat + 5 := by
    rw [ringNext_toNat' hk hmask (by omega), hq4]
    exact Nat.mod_eq_of_lt (by omega)
  have hq6 : (ringNext (ringNext (ringNext (ringNext (ringNext (ringNext wp mask) mask) mask) mask) mask)
      mask).toNat = wp.toNat + 6 := by
    rw [ringNext_toNat' hk hmask (by omega), hq5]
    exact Nat.mod_eq_of_lt (by omega)
  have hq7 : (ringNext (ringNext (ringNext (ringNext (ringNext (ringNext (ringNext wp mask) mask) mask) mask) mask)
      mask) mask).toNat = wp.toNat + 7 := by
    rw [ringNext_toNat' hk hmask (by omega), hq6]
    exact Nat.mod_eq_of_lt (by omega)
  -- the window as a copy of none, then each write folded into the copy as it happens
  refine (rawRun_ring (copySlice_zero' (src := a) (so := p.toNat) (d := wp.toNat) (e := false) (by omega)
    (by omega)).symm).trans ?_
  refine (rawRun_fill (hne n (by omega)) h8).trans ?_
  refine (rawRun_ring (fold_eq (m := 0) (by omega) (by omega) (by omega) z0 _)).trans ?_
  refine (rawRun_byte (hne _ (by omega)) (by decide)).trans ?_
  refine (rawRun_ring (fold_eq (m := 1) (by omega) (by omega) hq1 z1 _)).trans ?_
  refine (rawRun_byte (hne _ (by omega)) (by decide)).trans ?_
  refine (rawRun_ring (fold_eq (m := 2) (by omega) (by omega) hq2 z2 _)).trans ?_
  refine (rawRun_byte (hne _ (by omega)) (by decide)).trans ?_
  refine (rawRun_ring (fold_eq (m := 3) (by omega) (by omega) hq3 z3 _)).trans ?_
  refine (rawRun_byte (hne _ (by omega)) (by decide)).trans ?_
  refine (rawRun_ring (fold_eq (m := 4) (by omega) (by omega) hq4 z4 _)).trans ?_
  refine (rawRun_byte (hne _ (by omega)) (by decide)).trans ?_
  refine (rawRun_ring (fold_eq (m := 5) (by omega) (by omega) hq5 z5 _)).trans ?_
  refine (rawRun_byte (hne _ (by omega)) (by decide)).trans ?_
  refine (rawRun_ring (fold_eq (m := 6) (by omega) (by omega) hq6 z6 _)).trans ?_
  refine (rawRun_byte (hne _ (by omega)) (by decide)).trans ?_
  refine (rawRun_ring (fold_eq (m := 7) (by omega) (by omega) hq7 z7 _)).trans ?_
  refine rawRun_congr ?_ w8 (by decide) rfl rfl ?_ ?_ ?_ _ _ _ _ _ _
  · apply USize.toNat_inj.mp
    rw [n8, n7, n6, n5, n4, n3, n2, n1, u_sub (by rw [u_of (by decide)]; omega), u_of (by decide)]
    omega
  · apply USize.toNat_inj.mp
    rw [ringNext_toNat' hk hmask (by omega), hq7, u_and hmask, u_add (by rw [u_of (by decide)]; omega),
      u_of (by decide)]
  · rw [z7, ByteArray.getElem_eq_getElem_data]
  · rw [z6, ByteArray.getElem_eq_getElem_data]

/-- Whole groups, any number of them, are one copy. -/
theorem rawRun_groups : ∀ (j : Nat) {n p : USize} {r : ByteArray} {wp : USize} {x1 x2 : UInt8} (m : USize)
    {hp : p.toNat ≤ stop.toNat} {hsize : r.size = 2 ^ k} {hwp : wp.toNat < 2 ^ k},
    m.toNat = 8 * (j + 1) → m.toNat ≤ n.toNat → p.toNat + m.toNat ≤ stop.toNat → wp.toNat + m.toNat ≤ 2 ^ k →
    ∀ (hb1 : (p + m - USize.ofNat 1).toNat < a.size) (hb2 : (p + m - USize.ofNat 2).toNat < a.size)
      (hp' : (p + m).toNat ≤ stop.toNat) (hsize' : (a.copySlice p.toNat r wp.toNat m.toNat false).size = 2 ^ k)
      (hwp' : ((wp + m) &&& mask).toNat < 2 ^ k),
    rawRun a stop hs mask k hk hmask n 0 0 p r wp x1 x2 hp hsize hwp =
      rawRun a stop hs mask k hk hmask (n - m) 0 0 (p + m) (a.copySlice p.toNat r wp.toNat m.toNat false)
        ((wp + m) &&& mask) (a.uget (p + m - USize.ofNat 1) hb1) (a.uget (p + m - USize.ofNat 2) hb2) hp' hsize'
        hwp' := by
  intro j
  induction j with
  | zero =>
    intro n p r wp x1 x2 m hp hsize hwp hm hmn hpm hwm hb1 hb2 hp' hsize' hwp'
    have hst := stop.toNat_lt_size
    have hU := USize.le_size
    have hR : 2 ^ k ≤ 2 ^ 24 := Nat.pow_le_pow_right (by decide) hk
    have h24 : (2 : Nat) ^ 24 = 16777216 := by decide
    have hm8 : m = USize.ofNat 8 := USize.toNat_inj.mp (by rw [hm, u_of (by decide)])
    subst hm8
    have h8 : (USize.ofNat 8).toNat = 8 := u_of (by decide)
    have hpe : (p + USize.ofNat 8).toNat = p.toNat + 8 := by rw [u_add (by omega), h8]
    refine (rawRun_group (hp' := hp') (hsize' := by rw [← h8]; exact hsize') (hwp' := hwp') (by omega) (by omega)
      (by omega)).trans ?_
    refine rawRun_congr rfl rfl rfl rfl (by rw [h8]) rfl ?_ ?_ _ _ _ _ _ _
    · rw [uget_get, ByteArray.getElem_eq_getElem_data, ByteArray.getElem_eq_getElem_data]
      congr 1
      rw [u_sub (by rw [u_of (by decide), hpe]; omega), hpe, u_of (by decide)]
      omega
    · rw [uget_get, ByteArray.getElem_eq_getElem_data, ByteArray.getElem_eq_getElem_data]
      congr 1
      rw [u_sub (by rw [u_of (by decide), hpe]; omega), hpe, u_of (by decide)]
      omega
  | succ j ih =>
    intro n p r wp x1 x2 m hp hsize hwp hm hmn hpm hwm hb1 hb2 hp' hsize' hwp'
    have hst := stop.toNat_lt_size
    have hU := USize.le_size
    have hR : 2 ^ k ≤ 2 ^ 24 := Nat.pow_le_pow_right (by decide) hk
    have h24 : (2 : Nat) ^ 24 = 16777216 := by decide
    have h8 : (USize.ofNat 8).toNat = 8 := u_of (by decide)
    have hpe : (p + USize.ofNat 8).toNat = p.toNat + 8 := by rw [u_add (by omega), h8]
    have hwe : ((wp + USize.ofNat 8) &&& mask).toNat = wp.toNat + 8 := by
      rw [u_and hmask, u_add (by omega), h8]
      exact Nat.mod_eq_of_lt (by omega)
    have hm' : (m - USize.ofNat 8).toNat = m.toNat - 8 := by rw [u_sub (by omega), h8]
    have hn' : (n - USize.ofNat 8).toNat = n.toNat - 8 := by rw [u_sub (by omega), h8]
    have hpm' : (p + USize.ofNat 8 + (m - USize.ofNat 8)).toNat = p.toNat + m.toNat := by
      rw [u_add (by rw [hpe, hm']; omega), hpe, hm']
      omega
    have hpm2 : (p + m).toNat = p.toNat + m.toNat := u_add (by omega)
    have hcs8 := copySlice_size' (src := a) (dest := r) (so := p.toNat) (d := wp.toNat) (m := 8) (e := false)
      (by omega) (by omega)
    refine (rawRun_group (hp' := by rw [hpe]; omega) (hsize' := hcs8.trans hsize)
      (hwp' := by rw [hwe]; omega) (by omega) (by omega) (by omega)).trans ?_
    refine (ih (m - USize.ofNat 8) (by omega) (by rw [hm', hn']; omega) (by rw [hpe, hm']; omega)
      (by rw [hwe, hm']; omega) (by rw [u_sub (by rw [u_of (by decide), hpm']; omega), hpm', u_of (by decide)]; omega)
      (by rw [u_sub (by rw [u_of (by decide), hpm']; omega), hpm', u_of (by decide)]; omega)
      (by rw [hpm']; omega)
      (by rw [copySlice_size' (by rw [hpe, hm']; omega) (by rw [hcs8, hsize, hwe, hm']; omega), hcs8, hsize])
      (by rw [u_and hmask]; exact Nat.mod_lt _ (Nat.two_pow_pos _))).trans ?_
    refine rawRun_congr ?_ rfl rfl ?_ ?_ ?_ ?_ ?_ _ _ _ _ _ _
    · apply USize.toNat_inj.mp
      rw [u_sub (by rw [hm', hn']; omega), hm', hn', u_sub (by omega)]
      omega
    · apply USize.toNat_inj.mp
      rw [hpm', hpm2]
    · rw [hpe, hwe, hm']
      have e := copySlice_comp (src := a) (dest := r) (so := p.toNat) (d := wp.toNat) (m := 8) (l := m.toNat - 8)
        (by omega) (by omega)
      rw [e]
      congr 1
      omega
    · apply USize.toNat_inj.mp
      rw [u_and hmask, u_and hmask, u_add (by rw [hwe, hm']; omega), hwe, hm', u_add (by omega)]
      congr 1
      omega
    · rw [uget_get, uget_get]
      congr 1
      rw [u_sub (by rw [u_of (by decide), hpm']; omega), u_sub (by rw [u_of (by decide), hpm2]; omega), hpm', hpm2]
    · rw [uget_get, uget_get]
      congr 1
      rw [u_sub (by rw [u_of (by decide), hpm']; omega), u_sub (by rw [u_of (by decide), hpm2]; omega), hpm', hpm2]

end

/-- `rawRunF` is `rawRun`. -/
theorem rawRun_eq_rawRunF_aux {a : ByteArray} {stop : USize} {hs : stop.toNat ≤ a.size} {mask : USize} {k : Nat}
    {hk : k ≤ 24} {hmask : mask.toNat = 2 ^ k - 1} :
    ∀ (N : Nat) (n : USize) (word count : UInt64) (pos : USize) (ring : ByteArray) (wpos : USize) (p1 p2 : UInt8)
      (hp : pos.toNat ≤ stop.toNat) (hsize : ring.size = 2 ^ k) (hwp : wpos.toNat < 2 ^ k), n.toNat = N →
      rawRun a stop hs mask k hk hmask n word count pos ring wpos p1 p2 hp hsize hwp =
        rawRunF a stop hs mask k hk hmask n word count pos ring wpos p1 p2 hp hsize hwp := by
  intro N
  induction N using Nat.strongRecOn with
  | ind N ih =>
  intro n word count pos ring wpos p1 p2 hp hsize hwp hN
  by_cases hn : n = 0
  · rw [rawRun, rawRunF, dite_eq_left hn, dite_eq_left hn]
  · by_cases hg : word = 0 ∧ count = 0 ∧ rawGroups n pos stop mask wpos ≠ 0
    · rw [rawRunF, dite_eq_right hn, dite_eq_left hg]
      dsimp only
      obtain ⟨rfl, rfl, hg0⟩ := hg
      have hG := rawGroups_le (n := n) hk hmask hp hwp
      have hg1 := usize_ne hg0
      have hU := USize.le_size
      have hnU := n.toNat_lt_size
      have hsz : USize.size = 2 ^ System.Platform.numBits := USize.size_eq_two_pow
      have hm : (rawGroups n pos stop mask wpos * USize.ofNat 8).toNat = (rawGroups n pos stop mask wpos).toNat * 8 := by
        rw [USize.toNat_mul, u_of (by decide)]
        exact Nat.mod_eq_of_lt (by omega)
      have hlt : (n - rawGroups n pos stop mask wpos * USize.ofNat 8).toNat < N := by
        rw [u_sub (by omega)]
        omega
      exact (rawRun_groups ((rawGroups n pos stop mask wpos).toNat - 1) (rawGroups n pos stop mask wpos * USize.ofNat 8)
        (by omega) (by omega) (by omega) (by omega) _ _ _ _ _).trans (ih _ hlt _ _ _ _ _ _ _ _ _ _ _ rfl)
    · rw [rawRun, rawRunF, dite_eq_right hn, dite_eq_right hn, dite_eq_right hg]
      dsimp only
      by_cases h8 : 8 ≤ count
      · rw [ite_eq_left h8, ite_eq_left h8]
        exact ih (n - USize.ofNat 1).toNat (by rw [usize_pred hn]; have := usize_ne hn; omega) _ _ _ _ _ _ _ _ _ _ _
          rfl
      · rw [ite_eq_right h8, ite_eq_right h8]
        by_cases h8r : 8 ≤ (refill word count a pos stop hs hp).count ∧ (refill word count a pos stop hs hp).pos ≤ stop
        · rw [dite_eq_left h8r, dite_eq_left h8r]
          exact ih (n - USize.ofNat 1).toNat (by rw [usize_pred hn]; have := usize_ne hn; omega) _ _ _ _ _ _ _ _ _ _ _
            rfl
        · rw [dite_eq_right h8r, dite_eq_right h8r]

/-- The swap: what runs moves whole groups of eight bytes by one copy. -/
@[csimp] theorem rawRun_eq_rawRunF : @rawRun = @rawRunF := by
  funext a stop hs mask k hk hmask n word count pos ring wpos p1 p2 hp hsize hwp
  exact rawRun_eq_rawRunF_aux _ n word count pos ring wpos p1 p2 hp hsize hwp rfl

end Brotli.Decoder
