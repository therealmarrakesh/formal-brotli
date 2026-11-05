module

public import Brotli.Spec.Stream

@[expose] public section

/-!
# The window

A ring buffer of `2 ^ k` bytes holding the most recent output. It is tied to the spec's `output`, a list with the
most recent byte first. Bytes waiting to go out are just the newest window bytes not yet handed over.
-/

namespace Brotli.Decoder

/-- A new empty array with room for `n` bytes, made at each call: with constant arguments, an allocation written in place
would otherwise be made once for the whole program and shared, so that its first write copies it. -/
@[noinline, never_extract] def freshBytes (n : Nat) : ByteArray := ByteArray.emptyWithCapacity n

/-- Where the ring holds the byte `d` back from the newest, with `pos` the next position to write. -/
def ringIdx (R pos d : Nat) : Nat :=
  if d < pos then pos - 1 - d else pos + R - 1 - d

/-- The ring of `2 ^ k` bytes, next written at `pos`, holds the newest bytes of `out`. -/
structure RingOk (ring : ByteArray) (k pos : Nat) (out : List Nat) : Prop where
  size : ring.size = 2 ^ k
  pos_lt : pos < 2 ^ k
  holds : ∀ d, d < 2 ^ k → d < out.length →
    (ring.data[ringIdx (2 ^ k) pos d]?.getD 0).toNat = out.getD d 0

/-- An empty ring holds an empty output. -/
theorem RingOk.empty {ring : ByteArray} {k : Nat} (h : ring.size = 2 ^ k) : RingOk ring k 0 [] :=
  ⟨h, Nat.two_pow_pos _, by intro d _ hd; simp at hd⟩

private theorem usize_lt {n : Nat} (h : n < 2 ^ 32) : n < USize.size := by
  have := USize.le_size
  omega

private theorem usize_add {a b : USize} (h : a.toNat + b.toNat < 2 ^ 32) : (a + b).toNat = a.toNat + b.toNat := by
  rw [USize.toNat_add, ← USize.size_eq_two_pow]
  exact Nat.mod_eq_of_lt (usize_lt h)

private theorem usize_sub {a b : USize} (h : b.toNat ≤ a.toNat) : (a - b).toNat = a.toNat - b.toNat :=
  USize.toNat_sub_of_le _ _ (USize.le_iff_toNat_le.mpr h)

private theorem usize_ofNat {n : Nat} (h : n < 2 ^ 32) : (USize.ofNat n).toNat = n := by
  rw [USize.toNat_ofNat', ← USize.size_eq_two_pow]
  exact Nat.mod_eq_of_lt (usize_lt h)

private theorem and_mask {x mask : USize} {k : Nat} (hm : mask.toNat = 2 ^ k - 1) : (x &&& mask).toNat = x.toNat % 2 ^ k := by
  rw [USize.toNat_and, hm]
  exact Nat.and_two_pow_sub_one_eq_mod _ _

private theorem data_uset (a : ByteArray) (i : USize) (v : UInt8) (h : i.toNat < a.size) :
    (a.uset i v h).data = a.data.set i.toNat v h := by
  cases a
  rfl

/-- A window's size. -/
@[inline] def ringSize (k : USize) : USize := USize.ofNat 1 <<< k

/-- A window's mask. -/
@[inline] def ringMask (k : USize) : USize := ringSize k - USize.ofNat 1

theorem ringSize_toNat {k : USize} (hk : k.toNat ≤ 24) : (ringSize k).toNat = 2 ^ k.toNat := by
  have h32 := USize.le_size
  have hb : 32 ≤ System.Platform.numBits := by
    rcases System.Platform.numBits_eq with h | h <;> omega
  have hp : 2 ^ k.toNat ≤ 2 ^ 24 := Nat.pow_le_pow_right (by decide) hk
  have h24 : (2 : Nat) ^ 24 = 16777216 := by decide
  have hm : k.toNat % System.Platform.numBits = k.toNat := Nat.mod_eq_of_lt (by omega)
  unfold ringSize
  rw [USize.toNat_shiftLeft, usize_ofNat (by decide), hm, Nat.shiftLeft_eq, Nat.one_mul, ← USize.size_eq_two_pow]
  exact Nat.mod_eq_of_lt (by omega)

theorem ringMask_toNat {k : USize} (hk : k.toNat ≤ 24) : (ringMask k).toNat = 2 ^ k.toNat - 1 := by
  unfold ringMask
  have hpos : 1 ≤ 2 ^ k.toNat := Nat.two_pow_pos _
  rw [usize_sub (by rw [usize_ofNat (by decide)]; show _ ≤ (ringSize k).toNat; rw [ringSize_toNat hk]; exact hpos),
    usize_ofNat (by decide)]
  show (ringSize k).toNat - 1 = _
  rw [ringSize_toNat hk]

/-- The checks on a window that a loop's entry needs. -/
@[inline] def winCheck (k wpos : USize) (ring : ByteArray) : Bool :=
  decide (k ≤ USize.ofNat 24) && decide (ring.size = (ringSize k).toNat) && decide (wpos < ringSize k)

theorem winCheck_k {k wpos : USize} {ring : ByteArray} (h : winCheck k wpos ring = true) : k.toNat ≤ 24 := by
  simp only [winCheck, Bool.and_eq_true, decide_eq_true_eq] at h
  have := USize.le_iff_toNat_le.mp h.1.1
  rwa [usize_ofNat (by decide)] at this

theorem winCheck_size {k wpos : USize} {ring : ByteArray} (h : winCheck k wpos ring = true) : ring.size = 2 ^ k.toNat := by
  have hk := winCheck_k h
  simp only [winCheck, Bool.and_eq_true, decide_eq_true_eq] at h
  rw [h.1.2, ringSize_toNat hk]

theorem winCheck_pos {k wpos : USize} {ring : ByteArray} (h : winCheck k wpos ring = true) : wpos.toNat < 2 ^ k.toNat := by
  have hk := winCheck_k h
  simp only [winCheck, Bool.and_eq_true, decide_eq_true_eq] at h
  have := USize.lt_iff_toNat_lt.mp h.2
  rwa [ringSize_toNat hk] at this

theorem winCheck_of {k wpos : USize} {ring : ByteArray} (hk : k.toNat ≤ 24) (hs : ring.size = 2 ^ k.toNat)
    (hp : wpos.toNat < 2 ^ k.toNat) : winCheck k wpos ring = true := by
  simp only [winCheck, Bool.and_eq_true, decide_eq_true_eq]
  refine ⟨⟨USize.le_iff_toNat_le.mpr ?_, ?_⟩, USize.lt_iff_toNat_lt.mpr ?_⟩
  · rw [usize_ofNat (by decide)]
    exact hk
  · rw [ringSize_toNat hk]
    exact hs
  · rw [ringSize_toNat hk]
    exact hp

/-- The smaller of two positions. -/
@[inline] def usmin (a b : USize) : USize := if a ≤ b then a else b

theorem usmin_toNat (a b : USize) : (usmin a b).toNat = min a.toNat b.toNat := by
  unfold usmin
  by_cases h : a ≤ b
  · have h' := USize.le_iff_toNat_le.mp h
    rw [ite_eq_left h]
    omega
  · have h' : ¬ a.toNat ≤ b.toNat := fun e => h (USize.le_iff_toNat_le.mpr e)
    rw [ite_eq_right h]
    omega

/-- How many bytes may wait in a window before a step stops for output space: the cap, at least one, and at most the
window. -/
@[inline] def room (k cap : USize) : USize := usmin (if cap = 0 then USize.ofNat 1 else cap) (ringSize k)

theorem room_le {k cap : USize} (hk : k.toNat ≤ 24) : (room k cap).toNat ≤ 2 ^ k.toNat := by
  unfold room
  rw [usmin_toNat, ringSize_toNat hk]
  omega

theorem room_one {k cap : USize} (hk : k.toNat ≤ 24) : 1 ≤ (room k cap).toNat := by
  unfold room
  rw [usmin_toNat, ringSize_toNat hk]
  have : 1 ≤ 2 ^ k.toNat := Nat.one_le_two_pow
  split
  · rw [usize_ofNat (by decide)]
    omega
  · rename_i hc
    have : cap.toNat ≠ 0 := fun e => hc (USize.toNat_inj.mp (by rw [e]; rfl))
    omega

/-- The bytes waiting to go out, after more were written. -/
theorem pend_after {pend run : USize} {k : Nat} (hk : k ≤ 24) (h : pend.toNat + run.toNat ≤ 2 ^ k) :
    (pend + run).toNat = pend.toNat + run.toNat := by
  have hp : 2 ^ k ≤ 2 ^ 24 := Nat.pow_le_pow_right (by decide) hk
  have h24 : (2 : Nat) ^ 24 = 16777216 := by decide
  exact usize_add (by omega)

/-- The window's bytes written, after more were written. -/
theorem written_after {w written run : USize} {W : Nat} {k : USize} (hk : k.toNat ≤ 24) (hw : W + 16 = 2 ^ k.toNat)
    (hwr : written.toNat ≤ W) (hrun : run.toNat ≤ 2 ^ k.toNat) (hw' : w = ringSize k - USize.ofNat 16) :
    (usmin w (written + run)).toNat = min W (written.toNat + run.toNat) := by
  have hp : 2 ^ k.toNat ≤ 2 ^ 24 := Nat.pow_le_pow_right (by decide) hk
  have h24 : (2 : Nat) ^ 24 = 16777216 := by decide
  have hwN : w.toNat = W := by
    subst hw'
    rw [usize_sub (by rw [usize_ofNat (by decide), ringSize_toNat hk]; omega), usize_ofNat (by decide), ringSize_toNat hk]
    omega
  rw [usmin_toNat, hwN, usize_add (by omega)]

/-- Writes the next byte. -/
@[inline] def ringWrite (ring : ByteArray) (pos : USize) (v : UInt8) (h : pos.toNat < ring.size) : ByteArray :=
  ring.uset pos v h

theorem size_ringWrite (ring : ByteArray) (pos : USize) (v : UInt8) (h : pos.toNat < ring.size) :
    (ringWrite ring pos v h).size = ring.size := by
  show (ringWrite ring pos v h).data.size = ring.data.size
  simp only [ringWrite, data_uset, Array.size_set]

/-- A small position plus one. -/
theorem usize_succ {i : USize} (h : i.toNat + 1 < 2 ^ 32) : (i + USize.ofNat 1).toNat = i.toNat + 1 := by
  rw [usize_add (by rw [usize_ofNat (by decide)]; exact h), usize_ofNat (by decide)]

/-- The next position to write. -/
@[inline] def ringNext (pos mask : USize) : USize :=
  (pos + USize.ofNat 1) &&& mask

/-- Writing a byte makes it the newest. -/
theorem RingOk.write {ring : ByteArray} {k : Nat} {pos mask : USize} {out : List Nat} {v : UInt8}
    (h : RingOk ring k pos.toNat out) (hk : k ≤ 24) (hm : mask.toNat = 2 ^ k - 1) (hp : pos.toNat < ring.size) :
    RingOk (ringWrite ring pos v hp) k (ringNext pos mask).toNat (v.toNat :: out) := by
  have hR : 2 ^ k ≤ 2 ^ 24 := Nat.pow_le_pow_right (by decide) hk
  have hR1 : 1 ≤ 2 ^ k := Nat.two_pow_pos _
  have h24 : (2 : Nat) ^ 24 = 16777216 := by decide
  have hlt := h.pos_lt
  have hnext : (ringNext pos mask).toNat = if pos.toNat + 1 = 2 ^ k then 0 else pos.toNat + 1 := by
    unfold ringNext
    rw [and_mask hm, usize_add (by rw [usize_ofNat (by decide)]; omega), usize_ofNat (by decide)]
    split
    · rename_i he
      rw [he, Nat.mod_self]
    · exact Nat.mod_eq_of_lt (by omega)
  have hsize : (ringWrite ring pos v hp).size = 2 ^ k := by
    show (ringWrite ring pos v hp).data.size = _
    simp only [ringWrite, data_uset, Array.size_set]
    exact h.size
  refine ⟨hsize, by rw [hnext]; split <;> omega, ?_⟩
  intro d hd hdl
  rw [hnext]
  simp only [ringWrite, data_uset]
  cases d with
  | zero =>
    have hidx : ringIdx (2 ^ k) (if pos.toNat + 1 = 2 ^ k then 0 else pos.toNat + 1) 0 = pos.toNat := by
      unfold ringIdx
      split <;> split <;> omega
    rw [hidx]
    simp [hp]
  | succ d =>
    have hidx : ringIdx (2 ^ k) (if pos.toNat + 1 = 2 ^ k then 0 else pos.toNat + 1) (d + 1) =
        ringIdx (2 ^ k) pos.toNat d := by
      unfold ringIdx
      split <;> split <;> split <;> omega
    have hne : ringIdx (2 ^ k) pos.toNat d ≠ pos.toNat := by
      unfold ringIdx
      split <;> omega
    rw [hidx]
    have hold := h.holds d (by omega) (by simpa using hdl)
    simp only [List.getD_cons_succ]
    rw [← hold, Array.getElem?_set, ite_eq_right (Ne.symm hne)]

/-- The position of the byte `d` back from the next to write, for `d` from 1. -/
@[inline] def ringBack (pos d mask ringSize : USize) : USize :=
  (pos + ringSize - d) &&& mask

/-- Where `ringBack` points. -/
theorem ringBack_toNat {k : Nat} {pos d mask size : USize} (hk : k ≤ 24) (hm : mask.toNat = 2 ^ k - 1)
    (hs : size.toNat = 2 ^ k) (hp : pos.toNat < 2 ^ k) (hd1 : 1 ≤ d.toNat) (hd2 : d.toNat ≤ 2 ^ k) :
    (ringBack pos d mask size).toNat = ringIdx (2 ^ k) pos.toNat (d.toNat - 1) := by
  have hR : 2 ^ k ≤ 2 ^ 24 := Nat.pow_le_pow_right (by decide) hk
  have h24 : (2 : Nat) ^ 24 = 16777216 := by decide
  have hadd : (pos + size).toNat = pos.toNat + 2 ^ k := by
    rw [usize_add (by omega), hs]
  unfold ringBack ringIdx
  rw [and_mask hm, usize_sub (by omega), hadd]
  split
  · rename_i hlt
    have e : pos.toNat + 2 ^ k - d.toNat = (pos.toNat - d.toNat) + 2 ^ k := by omega
    rw [e, Nat.add_mod_right, Nat.mod_eq_of_lt (by omega)]
    omega
  · rw [Nat.mod_eq_of_lt (by omega)]
    omega

/-- Reading back within the ring gives the spec's byte. -/
theorem RingOk.read {ring : ByteArray} {k pos : Nat} {out : List Nat} {d : Nat} (h : RingOk ring k pos out)
    (hd1 : 1 ≤ d) (hd2 : d ≤ 2 ^ k) (hdl : d ≤ out.length) {p : USize} (hp : p.toNat = ringIdx (2 ^ k) pos (d - 1))
    (hb : p.toNat < ring.size) : (ring.uget p hb).toNat = out.getD (d - 1) 0 := by
  rw [← h.holds (d - 1) (by omega) (by omega), ← hp]
  cases ring with
  | mk bs =>
    have hb' : p.toNat < bs.size := hb
    simp [ByteArray.uget, hb']

/-- A position `ringIdx` gives is in the ring. -/
theorem ringIdx_lt {R pos d : Nat} (hp : pos < R) (hd : d < R) : ringIdx R pos d < R := by
  unfold ringIdx
  split <;> omega

/-! ### Handing bytes out -/

/-- The oldest `u` bytes not yet handed out start here, for `1 ≤ u`. -/
def ringStart (R pos u : Nat) : Nat := ringIdx R pos (u - 1)

/-- Adds `len` ring bytes from `start` to the caller's buffer. -/
@[inline] def emitRun (ring buf : ByteArray) (start len : Nat) : ByteArray :=
  ring.copySlice start buf buf.size len false

/-- A run adds exactly those bytes to the buffer. -/
theorem emitRun_data (ring buf : ByteArray) {start len : Nat} (h : start + len ≤ ring.size) :
    (emitRun ring buf start len).data.toList =
      buf.data.toList ++ (ring.data.toList.drop start).take len := by
  have hsz : ring.size = ring.data.size := rfl
  have hb : buf.size = buf.data.size := rfl
  have hmin : min len (ring.data.size - start) = len := by omega
  show (buf.data.extract 0 buf.size ++ ring.data.extract start (start + len) ++
    buf.data.extract (buf.size + min len (ring.data.size - start)) buf.data.size).toList = _
  have hA : buf.data.extract 0 buf.data.size = buf.data := by simp
  have hC : buf.data.extract (buf.data.size + len) buf.data.size = #[] :=
    Array.extract_eq_empty_of_le (by omega)
  rw [hmin, hb, hA, hC, Array.append_empty, Array.toList_append, Array.toList_extract]
  simp [List.extract]

/-- A run of ring bytes is the next of the bytes waiting to go out, oldest first. -/
theorem RingOk.emit_bytes {ring : ByteArray} {k pos : Nat} {out : List Nat} (h : RingOk ring k pos out) {u len : Nat}
    (hu1 : 1 ≤ u) (huR : u ≤ 2 ^ k) (hul : u ≤ out.length) (hlen : len ≤ u)
    (hrun : ringStart (2 ^ k) pos u + len ≤ 2 ^ k) :
    ((ring.data.toList.drop (ringStart (2 ^ k) pos u)).take len).map UInt8.toNat = ((out.take u).reverse).take len := by
  have hsize : ring.data.size = 2 ^ k := h.size
  have hsize' : ring.size = 2 ^ k := h.size
  have hplt := h.pos_lt
  apply List.ext_getElem
  · simp
    omega
  · intro i hi1 hi2
    have hil : i < len := by
      simp only [List.length_map, List.length_take, List.length_drop, Array.length_toList] at hi1
      omega
    have hiu : i < u := by omega
    have hidx : ringIdx (2 ^ k) pos (u - 1 - i) = ringStart (2 ^ k) pos u + i := by
      unfold ringStart at hrun ⊢
      unfold ringIdx at hrun ⊢
      split at hrun <;> (repeat' split) <;> omega
    have hval := h.holds (u - 1 - i) (by omega) (by omega)
    rw [hidx] at hval
    have hbound : ringStart (2 ^ k) pos u + i < ring.data.size := by omega
    simp only [List.getElem_map, List.getElem_take, List.getElem_drop, Array.getElem_toList, List.getElem_reverse,
      List.length_take]
    rw [Array.getElem?_eq_getElem hbound] at hval
    simp only [Option.getD_some] at hval
    rw [hval, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by omega)]
    simp only [Option.getD_some]
    congr 1
    omega

end Brotli.Decoder
