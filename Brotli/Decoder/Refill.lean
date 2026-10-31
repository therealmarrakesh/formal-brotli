import Brotli.Decoder.BitBuffer

/-!
# Refilling the bit buffer

Taking bytes from the caller's input array. With eight bytes at hand, a refill is one 64-bit load; near the end of
the chunk, it takes a byte at a time. Either way, the bits held followed by the unread chunk stay the same bits.
-/

namespace Brotli.Decoder

open Brotli.Spec

/-- The unread bytes of a chunk. -/
def chunk (input : ByteArray) (pos stop : Nat) : List UInt8 :=
  (input.data.toList.drop pos).take (stop - pos)

/-- The unread bits of a chunk. -/
def chunkBits (input : ByteArray) (pos stop : Nat) : List Bool :=
  bits (chunk input pos stop)

private theorem chunk_cons {input : ByteArray} {pos stop : Nat} (h : pos < stop) (hs : stop ≤ input.size) :
    chunk input pos stop = input.data[pos]'(by have : input.size = input.data.size := rfl; omega) ::
      chunk input (pos + 1) stop := by
  have hp : pos < input.data.size := by
    have : input.size = input.data.size := rfl
    omega
  have hl : pos < input.data.toList.length := by simpa using hp
  have hk : stop - pos = (stop - (pos + 1)) + 1 := by omega
  rw [chunk, hk, List.drop_eq_getElem_cons hl, List.take_succ_cons]
  simp [chunk]

private theorem chunkBits_cons {input : ByteArray} {pos stop : Nat} (h : pos < stop) (hs : stop ≤ input.size) :
    chunkBits input pos stop = lowBits (input.data[pos]'(by have : input.size = input.data.size := rfl; omega)).toNat 8 ++
      chunkBits input (pos + 1) stop := by
  rw [chunkBits, chunk_cons h hs, bits_cons, chunkBits]

private theorem usize_ofNat_toNat {n : Nat} (h : n < 2 ^ 32) : (USize.ofNat n).toNat = n := by
  rw [USize.toNat_ofNat']
  apply Nat.mod_eq_of_lt
  have := USize.le_size
  rw [USize.size_eq_two_pow] at this
  omega

private theorem usize_add {p : USize} {n : Nat} (hn : n < 2 ^ 32) (h : p.toNat + n < USize.size) :
    (p + USize.ofNat n).toNat = p.toNat + n := by
  rw [USize.toNat_add, usize_ofNat_toNat hn]
  apply Nat.mod_eq_of_lt
  rwa [← USize.size_eq_two_pow]

/-- The `k`th of eight bytes at `i`. -/
@[inline] private def byteAt (a : ByteArray) (i : USize) (k : Nat) (hk : k < 8) (h8 : i.toNat + 8 ≤ a.size)
    (hu : i.toNat + 8 ≤ USize.size) : UInt8 :=
  a.uget (i + USize.ofNat k) (by
    rw [usize_add (by omega) (by omega)]
    omega)

private theorem byteAt_eq {a : ByteArray} {i : USize} {k : Nat} {hk : k < 8} {h8 : i.toNat + 8 ≤ a.size}
    {hu : i.toNat + 8 ≤ USize.size} :
    byteAt a i k hk h8 hu = a.data[i.toNat + k]'(by have : a.size = a.data.size := rfl; omega) := by
  have hi : (i + USize.ofNat k).toNat = i.toNat + k := usize_add (by omega) (by omega)
  cases a with
  | mk bs =>
    simp only [byteAt, ByteArray.uget]
    simp [hi]

/-- Eight bytes at `i`, the first the least significant. -/
@[inline] private def loadBuffer (a : ByteArray) (i : USize) (h8 : i.toNat + 8 ≤ a.size)
    (hu : i.toNat + 8 ≤ USize.size) : BitBuffer :=
  (((((((BitBuffer.push ⟨0, 0⟩ (byteAt a i 0 (by decide) h8 hu)).push (byteAt a i 1 (by decide) h8 hu)).push
    (byteAt a i 2 (by decide) h8 hu)).push (byteAt a i 3 (by decide) h8 hu)).push
    (byteAt a i 4 (by decide) h8 hu)).push (byteAt a i 5 (by decide) h8 hu)).push
    (byteAt a i 6 (by decide) h8 hu)).push (byteAt a i 7 (by decide) h8 hu)

private theorem bits_append' (x t : List UInt8) : bits (x ++ t) = bits x ++ bits t := bits_append x t

private theorem bits_drop : ∀ (k : Nat) (l : List UInt8), (bits l).drop (8 * k) = bits (l.drop k)
  | 0, _ => by simp
  | _ + 1, [] => by simp [bits]
  | k + 1, x :: t => by
    have hA : 8 * (k + 1) = (lowBits x.toNat 8).length + 8 * k := by
      rw [lowBits_length]
      omega
    rw [bits_cons, hA, List.drop_length_add_append, List.drop_succ_cons]
    exact bits_drop k t

private theorem chunk_drop (input : ByteArray) (pos stop k : Nat) :
    chunk input (pos + k) stop = (chunk input pos stop).drop k := by
  simp only [chunk, List.drop_take, List.drop_drop]
  congr 1
  omega

/-- The eight bytes `loadBuffer` reads, in order, are the chunk's first. -/
private theorem chunk_eight {input : ByteArray} {pos stop : Nat} (h : pos + 8 ≤ stop) (hs : stop ≤ input.size) :
    ∃ xs, xs.length = 8 ∧ (∀ i : USize, i.toNat = pos → ∀ (h8 : i.toNat + 8 ≤ input.size)
        (hu : i.toNat + 8 ≤ USize.size), (loadBuffer input i h8 hu) = xs.foldl BitBuffer.push BitBuffer.empty) ∧
      chunk input pos stop = xs ++ chunk input (pos + 8) stop := by
  have hsz : input.size = input.data.size := rfl
  refine ⟨[input.data[pos]'(by omega), input.data[pos + 1]'(by omega), input.data[pos + 2]'(by omega),
    input.data[pos + 3]'(by omega), input.data[pos + 4]'(by omega), input.data[pos + 5]'(by omega),
    input.data[pos + 6]'(by omega), input.data[pos + 7]'(by omega)], rfl, ?_, ?_⟩
  · intro i hi h8 hu
    subst hi
    simp only [loadBuffer, byteAt_eq, List.foldl_cons, List.foldl_nil, Nat.add_zero]
    rfl
  · rw [chunk_cons (by omega) hs, chunk_cons (by omega) hs, chunk_cons (by omega) hs, chunk_cons (by omega) hs,
      chunk_cons (by omega) hs, chunk_cons (by omega) hs, chunk_cons (by omega) hs, chunk_cons (by omega) hs]
    simp

/-- Fills the buffer with as many whole bytes as fit, in one load. It takes at least 8 free bits and 8 unread
bytes. -/
@[inline] def BitBuffer.fill (b : BitBuffer) (a : ByteArray) (pos : USize) (h8 : pos.toNat + 8 ≤ a.size)
    (hu : pos.toNat + 8 ≤ USize.size) : BitBuffer × USize :=
  let k := (64 - b.count) >>> 3
  let nb := k <<< 3
  let s := 64 - nb
  let v := ((loadBuffer a pos h8 hu).word <<< s) >>> s
  (⟨b.word ||| (v <<< b.count), b.count + nb⟩, pos + k.toUSize)

private theorem shift_pair (v : UInt64) {s n : Nat} {us : UInt64} (hus : us.toNat = s) (hs : s + n = 64) (hs' : s < 64) :
    ((v <<< us) >>> us).toNat = v.toNat % 2 ^ n := by
  subst hus
  have hmod : us.toNat % 64 = us.toNat := Nat.mod_eq_of_lt hs'
  simp only [UInt64.toNat_shiftRight, UInt64.toNat_shiftLeft, hmod, Nat.shiftRight_eq_div_pow, Nat.shiftLeft_eq]
  have hp : (2 : Nat) ^ 64 = 2 ^ us.toNat * 2 ^ n := by rw [← Nat.pow_add, hs]
  rw [hp, Nat.mul_comm v.toNat, Nat.mul_mod_mul_left, Nat.mul_div_cancel_left _ (Nat.two_pow_pos _)]

/-- What `fill` does: the bits at hand and the unread chunk stay the same bits, and the buffer is near full. -/
theorem BitBuffer.fill_spec {b : BitBuffer} {a : ByteArray} {pos stop : USize} (hw : b.Wf) (hc : b.count.toNat ≤ 56)
    (h : pos.toNat + 8 ≤ stop.toNat) (hs : stop.toNat ≤ a.size) (h8 : pos.toNat + 8 ≤ a.size)
    (hu : pos.toNat + 8 ≤ USize.size) :
    (b.fill a pos h8 hu).1.Wf ∧ 56 < (b.fill a pos h8 hu).1.count.toNat ∧
      pos.toNat ≤ (b.fill a pos h8 hu).2.toNat ∧ (b.fill a pos h8 hu).2.toNat ≤ stop.toNat ∧
      (b.fill a pos h8 hu).1.held ++ chunkBits a (b.fill a pos h8 hu).2.toNat stop.toNat =
        b.held ++ chunkBits a pos.toNat stop.toNat := by
  unfold BitBuffer.fill
  dsimp only
  have hc64 : (64 : UInt64).toNat = 64 := rfl
  have h3 : (3 : UInt64).toNat = 3 := rfl
  have hsub : (64 - b.count).toNat = 64 - b.count.toNat :=
    UInt64.toNat_sub_of_le _ _ (UInt64.le_iff_toNat_le.mpr (by rw [hc64]; omega)) |>.trans (by rw [hc64])
  have hk : ((64 - b.count) >>> 3).toNat = (64 - b.count.toNat) / 8 := by
    simp only [UInt64.toNat_shiftRight, hsub, h3, Nat.shiftRight_eq_div_pow]
  generalize (64 - b.count) >>> 3 = k at hk ⊢
  have hk1 : 1 ≤ k.toNat := by omega
  have hk8 : k.toNat ≤ 8 := by omega
  have hnb : (k <<< 3).toNat = 8 * k.toNat := by
    simp only [UInt64.toNat_shiftLeft, h3, Nat.shiftLeft_eq]
    rw [show 3 % 64 = 3 from rfl, show (2 : Nat) ^ 3 = 8 from rfl, Nat.mul_comm]
    exact Nat.mod_eq_of_lt (by have : (2 : Nat) ^ 64 = 18446744073709551616 := by decide
                               omega)
  generalize k <<< 3 = nb at hnb ⊢
  have hus : (64 - nb).toNat = 64 - nb.toNat :=
    (UInt64.toNat_sub_of_le _ _ (UInt64.le_iff_toNat_le.mpr (by rw [hc64]; omega))).trans (by rw [hc64])
  obtain ⟨xs, hl, hload, hsplit⟩ := chunk_eight h hs
  obtain ⟨lw, lc, lh⟩ := BitBuffer.pushAll xs BitBuffer.empty BitBuffer.empty_wf (by simp [BitBuffer.empty, hl])
  have hload' := hload pos rfl h8 hu
  have hheld : lowBits (loadBuffer a pos h8 hu).word.toNat 64 = bits xs := by
    have hc0 : BitBuffer.empty.count.toNat = 0 := rfl
    rw [hload']
    have e : lowBits (List.foldl BitBuffer.push BitBuffer.empty xs).word.toNat
        (List.foldl BitBuffer.push BitBuffer.empty xs).count.toNat = bits xs := by
      simpa [BitBuffer.held, BitBuffer.empty, lowBits] using lh
    rw [lc, hc0, hl] at e
    simpa using e
  generalize (loadBuffer a pos h8 hu).word = word at hheld ⊢
  have hv : ((word <<< (64 - nb)) >>> (64 - nb)).toNat = word.toNat % 2 ^ nb.toNat :=
    shift_pair word hus (by omega) (by omega)
  generalize (word <<< (64 - nb)) >>> (64 - nb) = v at hv ⊢
  have hvlt : v.toNat < 2 ^ nb.toNat := by
    rw [hv]
    exact Nat.mod_lt _ (Nat.two_pow_pos _)
  have hroom : b.count.toNat + nb.toNat ≤ 64 := by omega
  have hword : (b.word ||| (v <<< b.count)).toNat = b.word.toNat + 2 ^ b.count.toNat * v.toNat :=
    BitBuffer.add_word hroom (by omega) hw.word_lt hvlt
  have hcount : (b.count + nb).toNat = b.count.toNat + nb.toNat := by
    rw [UInt64.toNat_add]
    exact Nat.mod_eq_of_lt (by have : (2 : Nat) ^ 64 = 18446744073709551616 := by decide
                               omega)
  have hkz : k.toUSize.toNat = k.toNat := by
    rw [UInt64.toNat_toUSize]
    apply Nat.mod_eq_of_lt
    have := USize.le_size
    rw [USize.size_eq_two_pow] at this
    omega
  have hpos : (pos + k.toUSize).toNat = pos.toNat + k.toNat := by
    have hlim := stop.toNat_lt_size
    rw [USize.toNat_add, hkz]
    apply Nat.mod_eq_of_lt
    rw [← USize.size_eq_two_pow]
    omega
  refine ⟨⟨?_, ?_⟩, ?_, ?_, ?_, ?_⟩
  · simp only [hcount]
    omega
  · simp only [hword, hcount]
    rw [Nat.pow_add]
    have h1 := hw.word_lt
    have h2 : 2 ^ b.count.toNat * v.toNat + 2 ^ b.count.toNat ≤ 2 ^ b.count.toNat * 2 ^ nb.toNat := by
      rw [← Nat.mul_succ]
      exact Nat.mul_le_mul_left _ hvlt
    omega
  · simp only [hcount]
    omega
  · simp only [hpos]
    omega
  · simp only [hpos]
    omega
  · simp only [BitBuffer.held, hword, hcount, hpos]
    rw [lowBits_add _ _ _ _ hw.word_lt, hv, lowBits_mod, ← lowBits_take nb.toNat 64 word.toNat (by omega), hheld]
    have hlen : (bits xs).length = 64 := by
      rw [← hheld, lowBits_length]
    have hR : chunkBits a pos.toNat stop.toNat = bits xs ++ chunkBits a (pos.toNat + 8) stop.toNat := by
      rw [chunkBits, hsplit, bits_append, chunkBits]
    have hD : chunkBits a (pos.toNat + k.toNat) stop.toNat = (bits xs).drop nb.toNat ++
        chunkBits a (pos.toNat + 8) stop.toNat := by
      rw [chunkBits, chunk_drop, ← bits_drop, ← chunkBits, hR, hnb,
        List.drop_append_of_le_length (by rw [hlen]; omega)]
    rw [hD, hR, List.append_assoc, ← List.append_assoc (List.take _ _), List.take_append_drop]

/-- Takes whole bytes one at a time, for fewer than eight unread. -/
def BitBuffer.fillSlow (a : ByteArray) (stop : USize) (hs : stop.toNat ≤ a.size) :
    Nat → BitBuffer → USize → BitBuffer × USize
  | 0, b, p => (b, p)
  | n + 1, b, p =>
    if h : b.count.toNat ≤ 56 ∧ p < stop then
      BitBuffer.fillSlow a stop hs n (b.push (a.uget p (by
        have := USize.lt_iff_toNat_lt.mp h.2
        omega))) (p + USize.ofNat 1)
    else (b, p)

private theorem uget_eq {a : ByteArray} {p : USize} (h : p.toNat < a.size) :
    a.uget p h = a.data[p.toNat]'h := by
  cases a with
  | mk bs => simp [ByteArray.uget]

/-- What `fillSlow` does: the same bits, and it stops with the buffer near full or the chunk used up. -/
theorem BitBuffer.fillSlow_spec {a : ByteArray} {stop : USize} (hs : stop.toNat ≤ a.size) : ∀ (n : Nat) (b : BitBuffer)
    (p : USize), b.Wf → p.toNat ≤ stop.toNat → 56 < b.count.toNat + 8 * n →
    (BitBuffer.fillSlow a stop hs n b p).1.Wf ∧ 56 < (BitBuffer.fillSlow a stop hs n b p).1.count.toNat ∨
      (BitBuffer.fillSlow a stop hs n b p).1.Wf ∧ (BitBuffer.fillSlow a stop hs n b p).2 = stop
  | 0, b, p, hw, _, hn => by
    left
    exact ⟨hw, by simpa [BitBuffer.fillSlow] using hn⟩
  | n + 1, b, p, hw, hp, hn => by
    simp only [BitBuffer.fillSlow]
    split
    · rename_i h
      have hlt := USize.lt_iff_toNat_lt.mp h.2
      have hnext : (p + USize.ofNat 1).toNat = p.toNat + 1 :=
        usize_add (by decide) (Nat.lt_of_le_of_lt (by omega) stop.toNat_lt_size)
      refine BitBuffer.fillSlow_spec hs n _ _ (BitBuffer.push_wf _ hw h.1) (by omega) ?_
      rw [BitBuffer.push_count h.1]
      omega
    · rename_i h
      by_cases hc : b.count.toNat ≤ 56
      · right
        refine ⟨hw, ?_⟩
        have hnot : ¬ p.toNat < stop.toNat := fun hl => h ⟨hc, USize.lt_iff_toNat_lt.mpr hl⟩
        have : p.toNat = stop.toNat := by omega
        exact USize.toNat_inj.mp this
      · left
        exact ⟨hw, Nat.lt_of_not_le hc⟩

/-- `fillSlow` keeps the same bits and moves forward within the chunk. -/
theorem BitBuffer.fillSlow_bits {a : ByteArray} {stop : USize} (hs : stop.toNat ≤ a.size) : ∀ (n : Nat) (b : BitBuffer)
    (p : USize), b.Wf → p.toNat ≤ stop.toNat →
    p.toNat ≤ (BitBuffer.fillSlow a stop hs n b p).2.toNat ∧ (BitBuffer.fillSlow a stop hs n b p).2.toNat ≤ stop.toNat ∧
      (BitBuffer.fillSlow a stop hs n b p).1.held ++
          chunkBits a (BitBuffer.fillSlow a stop hs n b p).2.toNat stop.toNat =
        b.held ++ chunkBits a p.toNat stop.toNat
  | 0, b, p, _, hp => ⟨Nat.le_refl _, hp, rfl⟩
  | n + 1, b, p, hw, hp => by
    simp only [BitBuffer.fillSlow]
    split
    · rename_i h
      have hlt := USize.lt_iff_toNat_lt.mp h.2
      have hnext : (p + USize.ofNat 1).toNat = p.toNat + 1 :=
        usize_add (by decide) (Nat.lt_of_le_of_lt (by omega) stop.toNat_lt_size)
      have hb : p.toNat < a.size := by omega
      obtain ⟨h1, h2, h3⟩ := BitBuffer.fillSlow_bits hs n (b.push (a.uget p hb)) (p + USize.ofNat 1)
        (BitBuffer.push_wf _ hw h.1) (by omega)
      refine ⟨by omega, h2, ?_⟩
      rw [h3, hnext, BitBuffer.push_held _ hw h.1, List.append_assoc, chunkBits_cons hlt hs, uget_eq hb]
    · exact ⟨Nat.le_refl _, hp, rfl⟩

/-- A refill's result, flat so that hot loops keep every field as a plain value. -/
structure Refilled where
  word : UInt64
  count : UInt64
  pos : USize

/-- The buffer in a refill's result. -/
@[inline] def Refilled.buf (r : Refilled) : BitBuffer := ⟨r.word, r.count⟩

/-- Fills the buffer as far as whole bytes fit, from the unread part of the chunk. Its arguments are the buffer's
fields, so that only the path with fewer than eight bytes unread allocates anything. -/
@[inline] def refill (word count : UInt64) (a : ByteArray) (pos stop : USize) (hs : stop.toNat ≤ a.size)
    (hp : pos.toNat ≤ stop.toNat) : Refilled :=
  if 56 < count then ⟨word, count, pos⟩
  else if h : USize.ofNat 8 ≤ stop - pos then
    let r := (BitBuffer.mk word count).fill a pos
      (by
        have h1 := USize.le_iff_toNat_le.mp h
        rw [usize_ofNat_toNat (by decide), USize.toNat_sub_of_le _ _ (USize.le_iff_toNat_le.mpr hp)] at h1
        omega)
      (by
        have h1 := USize.le_iff_toNat_le.mp h
        rw [usize_ofNat_toNat (by decide), USize.toNat_sub_of_le _ _ (USize.le_iff_toNat_le.mpr hp)] at h1
        have := stop.toNat_lt_size
        omega)
    ⟨r.1.word, r.1.count, r.2⟩
  else
    let r := BitBuffer.fillSlow a stop hs 8 ⟨word, count⟩ pos
    ⟨r.1.word, r.1.count, r.2⟩

/-- What `refill` does: a well-formed buffer, the same bits, and the buffer near full or the chunk used up. -/
theorem refill_spec {word count : UInt64} {a : ByteArray} {pos stop : USize} (hs : stop.toNat ≤ a.size)
    (hp : pos.toNat ≤ stop.toNat) (hw : (BitBuffer.mk word count).Wf) :
    (refill word count a pos stop hs hp).buf.Wf ∧
      pos.toNat ≤ (refill word count a pos stop hs hp).pos.toNat ∧
      (refill word count a pos stop hs hp).pos.toNat ≤ stop.toNat ∧
      (refill word count a pos stop hs hp).buf.held ++
          chunkBits a (refill word count a pos stop hs hp).pos.toNat stop.toNat =
        (BitBuffer.mk word count).held ++ chunkBits a pos.toNat stop.toNat ∧
      (56 < (refill word count a pos stop hs hp).count.toNat ∨ (refill word count a pos stop hs hp).pos = stop) := by
  unfold refill
  split
  · rename_i h
    have h1 := UInt64.lt_iff_toNat_lt.mp h
    exact ⟨hw, Nat.le_refl _, hp, rfl, Or.inl h1⟩
  · rename_i h
    have hc : (BitBuffer.mk word count).count.toNat ≤ 56 :=
      Nat.le_of_not_lt fun hl => h (UInt64.lt_iff_toNat_lt.mpr hl)
    split
    · rename_i hb
      have h1 := USize.le_iff_toNat_le.mp hb
      rw [usize_ofNat_toNat (by decide), USize.toNat_sub_of_le _ _ (USize.le_iff_toNat_le.mpr hp)] at h1
      have hk : pos.toNat + 8 ≤ stop.toNat := by omega
      obtain ⟨w, c, p1, p2, e⟩ := BitBuffer.fill_spec (stop := stop) hw hc hk hs (by omega)
        (by have := stop.toNat_lt_size; omega)
      exact ⟨w, p1, p2, e, Or.inl c⟩
    · obtain ⟨p1, p2, e⟩ := BitBuffer.fillSlow_bits hs 8 ⟨word, count⟩ pos hw hp
      rcases BitBuffer.fillSlow_spec hs 8 ⟨word, count⟩ pos hw hp (by omega) with ⟨w, c⟩ | ⟨w, c⟩
      · exact ⟨w, p1, p2, e, Or.inl c⟩
      · exact ⟨w, p1, p2, e, Or.inr c⟩

end Brotli.Decoder
