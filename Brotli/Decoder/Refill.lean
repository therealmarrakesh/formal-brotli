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

/-- Skipping bytes of a chunk. -/
theorem chunkBits_drop (input : ByteArray) (pos stop k : Nat) :
    chunkBits input (pos + k) stop = (chunkBits input pos stop).drop (8 * k) := by
  unfold chunkBits
  rw [chunk_drop, bits_drop]

/-- A chunk's length in bits. -/
theorem chunkBits_length {input : ByteArray} {pos stop : Nat} (hs : stop ≤ input.size) : (chunkBits input pos stop).length = (stop - pos) * 8 := by
  unfold chunkBits chunk
  rw [bits_length]
  have hsz : input.data.size = input.size := rfl
  simp only [List.length_take, List.length_drop, Array.length_toList, hsz]
  have : min (stop - pos) (input.size - pos) = stop - pos := by omega
  rw [this]

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

/-- A refill's result, flat so that hot loops keep every field as a plain value. -/
structure Refilled where
  word : UInt64
  count : UInt64
  pos : USize

/-- Takes whole bytes one at a time, for fewer than eight unread. Its state is plain values, and only its result
allocates. -/
def BitBuffer.fillSlow (a : ByteArray) (stop : USize) (hs : stop.toNat ≤ a.size) (word count : UInt64) (p : USize) : Refilled :=
  if h : count ≤ 56 ∧ p < stop then
    have hlt := USize.lt_iff_toNat_lt.mp h.2
    have hnext : (p + USize.ofNat 1).toNat = p.toNat + 1 :=
      usize_add (by decide) (Nat.lt_of_le_of_lt (by omega) stop.toNat_lt_size)
    let b := (BitBuffer.mk word count).push (a.uget p (by omega))
    BitBuffer.fillSlow a stop hs b.word b.count (p + USize.ofNat 1)
  else ⟨word, count, p⟩
termination_by stop.toNat - p.toNat
decreasing_by
  omega

private theorem uget_eq {a : ByteArray} {p : USize} (h : p.toNat < a.size) :
    a.uget p h = a.data[p.toNat]'h := by
  cases a with
  | mk bs => simp [ByteArray.uget]

/-- What `fillSlow` does: the same bits, moving forward within the chunk, and it stops with the buffer near full or
the chunk used up. -/
theorem BitBuffer.fillSlow_spec {a : ByteArray} {stop : USize} (hs : stop.toNat ≤ a.size) : ∀ (N : Nat) (word count : UInt64)
    (p : USize), stop.toNat - p.toNat = N → (BitBuffer.mk word count).Wf → p.toNat ≤ stop.toNat →
    let r := BitBuffer.fillSlow a stop hs word count p
    (BitBuffer.mk r.word r.count).Wf ∧ p.toNat ≤ r.pos.toNat ∧ r.pos.toNat ≤ stop.toNat ∧
      (BitBuffer.mk r.word r.count).held ++ chunkBits a r.pos.toNat stop.toNat =
        (BitBuffer.mk word count).held ++ chunkBits a p.toNat stop.toNat ∧
      (56 < r.count.toNat ∨ r.pos = stop) := by
  intro N
  induction N using Nat.strongRecOn with
  | ind N ih =>
    intro word count p hN hw hp
    rw [BitBuffer.fillSlow]
    split
    · rename_i h
      have hc : (BitBuffer.mk word count).count.toNat ≤ 56 := UInt64.le_iff_toNat_le.mp h.1
      have hlt := USize.lt_iff_toNat_lt.mp h.2
      have hnext : (p + USize.ofNat 1).toNat = p.toNat + 1 :=
        usize_add (by decide) (Nat.lt_of_le_of_lt (by omega) stop.toNat_lt_size)
      have hb : p.toNat < a.size := by omega
      have hw' := BitBuffer.push_wf (a.uget p hb) hw hc
      have hheld := BitBuffer.push_held (a.uget p hb) hw hc
      dsimp only
      generalize (BitBuffer.mk word count).push (a.uget p hb) = b' at hw' hheld ⊢
      have hih := ih (stop.toNat - (p + USize.ofNat 1).toNat) (by omega) b'.word b'.count (p + USize.ofNat 1) rfl hw' (by omega)
      dsimp only at hih ⊢
      obtain ⟨h1, h2, h3, h4, h5⟩ := hih
      refine ⟨h1, by omega, h3, ?_, h5⟩
      have hheld' : (BitBuffer.mk b'.word b'.count).held = b'.held := rfl
      rw [h4, hnext, hheld', hheld, List.append_assoc, chunkBits_cons hlt hs, uget_eq hb]
    · rename_i h
      refine ⟨hw, Nat.le_refl _, hp, rfl, ?_⟩
      by_cases hc : count ≤ 56
      · right
        have hnot : ¬ p.toNat < stop.toNat := fun hl => h ⟨hc, USize.lt_iff_toNat_lt.mpr hl⟩
        exact USize.toNat_inj.mp (by show p.toNat = _; omega)
      · left
        have : ¬ count.toNat ≤ 56 := fun e => hc (UInt64.le_iff_toNat_le.mpr e)
        show 56 < count.toNat
        omega

/-! ### The slow fill, unrolled

`fillSlow` is a loop, so it isn't inlined, and its `Refilled` result is allocated on every call: on every step once
fewer than eight bytes remain, and on every step after the input runs out. It takes at most eight bytes, since each
adds eight bits to at most 56, so `fillSlowU` is the same eight steps written out, each ending in a continuation:
inlined into `refill`, its result is never built. `fillSlow_csimp` proves the two equal. -/

/-- One step of the slow fill: a byte taken while there is room and input, ending in `more`, or the buffer as it
stands, in `done`. -/
@[inline] def fillStep {α : Type} (a : ByteArray) (stop : USize) (hs : stop.toNat ≤ a.size)
    (more done : UInt64 → UInt64 → USize → α) (word count : UInt64) (p : USize) : α :=
  if h : count ≤ 56 ∧ p < stop then
    have hlt := USize.lt_iff_toNat_lt.mp h.2
    let b := (BitBuffer.mk word count).push (a.uget p (by omega))
    more b.word b.count (p + USize.ofNat 1)
  else done word count p

/-- The slow fill's result from its fields. -/
@[inline] def mkRefilled (w c : UInt64) (q : USize) : Refilled := ⟨w, c, q⟩

/-- `fillSlow` as eight steps written out. -/
@[inline] def fillSlowU (a : ByteArray) (stop : USize) (hs : stop.toNat ≤ a.size) (word count : UInt64) (p : USize) :
    Refilled :=
  fillStep a stop hs (fillStep a stop hs (fillStep a stop hs (fillStep a stop hs (fillStep a stop hs
    (fillStep a stop hs (fillStep a stop hs (fillStep a stop hs mkRefilled mkRefilled) mkRefilled) mkRefilled)
    mkRefilled) mkRefilled) mkRefilled) mkRefilled) mkRefilled word count p

/-- `fillSlow` is its first step, gone on with by itself. -/
private theorem fillSlow_step (a : ByteArray) (stop : USize) (hs : stop.toNat ≤ a.size) :
    BitBuffer.fillSlow a stop hs = fillStep a stop hs (BitBuffer.fillSlow a stop hs) mkRefilled := by
  funext word count p
  rw [BitBuffer.fillSlow]
  rfl

/-- `fillSlow` unrolled `k` times. -/
private def fillG (a : ByteArray) (stop : USize) (hs : stop.toNat ≤ a.size) :
    Nat → UInt64 → UInt64 → USize → Refilled
  | 0 => BitBuffer.fillSlow a stop hs
  | k + 1 => fillStep a stop hs (fillG a stop hs k) mkRefilled

/-- The written-out steps, `k` deep. -/
private def fillU (a : ByteArray) (stop : USize) (hs : stop.toNat ≤ a.size) :
    Nat → UInt64 → UInt64 → USize → Refilled
  | 0 => mkRefilled
  | k + 1 => fillStep a stop hs (fillU a stop hs k) mkRefilled

private theorem fillG_eq (a : ByteArray) (stop : USize) (hs : stop.toNat ≤ a.size) :
    ∀ k, fillG a stop hs k = BitBuffer.fillSlow a stop hs := by
  intro k
  induction k with
  | zero => rfl
  | succ k ih =>
    show fillStep a stop hs (fillG a stop hs k) mkRefilled = _
    rw [ih, ← fillSlow_step]

/-- The step goes on only with eight more bits than it was given. -/
private theorem fillStep_congr {a : ByteArray} {stop : USize} {hs : stop.toNat ≤ a.size}
    {m1 m2 : UInt64 → UInt64 → USize → Refilled} {lo : Nat}
    (h : ∀ w c q, lo + 8 ≤ c.toNat → m1 w c q = m2 w c q) :
    ∀ w c q, lo ≤ c.toNat → fillStep a stop hs m1 mkRefilled w c q = fillStep a stop hs m2 mkRefilled w c q := by
  intro w c q hc
  unfold fillStep
  split
  · rename_i hh
    apply h
    rw [BitBuffer.push_count (UInt64.le_iff_toNat_le.mp hh.1)]
    show lo + 8 ≤ c.toNat + 8
    omega
  · rfl

/-- At depth `k`, the unrolled fill and the loop agree on every buffer with at least `64 - 8k` bits. -/
private theorem fillGU (a : ByteArray) (stop : USize) (hs : stop.toNat ≤ a.size) :
    ∀ k w c q, 64 - 8 * k ≤ c.toNat → fillG a stop hs k w c q = fillU a stop hs k w c q := by
  intro k
  induction k with
  | zero =>
    intro w c q hc
    show BitBuffer.fillSlow a stop hs w c q = mkRefilled w c q
    rw [BitBuffer.fillSlow, dite_eq_right]
    · rfl
    · intro hh
      have := UInt64.le_iff_toNat_le.mp hh.1
      have h56 : (56 : UInt64).toNat = 56 := rfl
      omega
  | succ k ih =>
    intro w c q hc
    exact fillStep_congr (lo := 64 - 8 * (k + 1)) (fun w c q h => ih w c q (by omega)) w c q hc

/-- The compiler runs the slow fill written out, which allocates nothing, in place of the loop. -/
@[csimp] theorem fillSlow_csimp : @BitBuffer.fillSlow = @fillSlowU := by
  funext a stop hs word count p
  rw [← fillG_eq a stop hs 8]
  exact fillGU a stop hs 8 word count p (by omega)

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
  else BitBuffer.fillSlow a stop hs word count pos

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
    · exact BitBuffer.fillSlow_spec hs _ word count pos rfl hw hp

/-- No bytes between a position and itself. -/
theorem chunkBits_self (input : ByteArray) (n : Nat) : chunkBits input n n = [] := by
  simp [chunkBits, chunk, bits]

/-- A chunk's bits, cut at a position between its ends. -/
theorem chunkBits_split (input : ByteArray) {pos q stop : Nat} (h1 : pos ≤ q) (h2 : q ≤ stop) :
    chunkBits input pos stop = chunkBits input pos q ++ chunkBits input q stop := by
  unfold chunkBits chunk
  rw [← bits_append]
  congr 1
  have e : stop - pos = (q - pos) + (stop - q) := by omega
  rw [e, List.take_add]
  simp only [List.drop_drop, Nat.add_sub_cancel' h1]

/-- What a refill takes, on its own: the bits held after it are the bits held before and the bytes it took, and so at most
64 bits lie between the first bit held before it and the position after it. -/
theorem refill_local {word count : UInt64} {a : ByteArray} {pos stop : USize} (hs : stop.toNat ≤ a.size)
    (hp : pos.toNat ≤ stop.toNat) (hw : (BitBuffer.mk word count).Wf) :
    (refill word count a pos stop hs hp).buf.held =
        (BitBuffer.mk word count).held ++ chunkBits a pos.toNat (refill word count a pos stop hs hp).pos.toNat ∧
      8 * (refill word count a pos stop hs hp).pos.toNat + count.toNat ≤ 8 * pos.toNat + 64 := by
  obtain ⟨w, h1, h2, e, -⟩ := refill_spec hs hp hw
  rw [chunkBits_split a h1 h2, ← List.append_assoc] at e
  have e' := List.append_cancel_right e
  refine ⟨e', ?_⟩
  have hl := congrArg List.length e'
  have hc := w.count_le
  rw [List.length_append, chunkBits_length (Nat.le_trans h2 hs)] at hl
  have l1 : (refill word count a pos stop hs hp).buf.held.length = (refill word count a pos stop hs hp).count.toNat :=
    lowBits_length _ _
  have l2 : (BitBuffer.mk word count).held.length = count.toNat := lowBits_length _ _
  have l3 : (refill word count a pos stop hs hp).buf.count = (refill word count a pos stop hs hp).count := rfl
  rw [l1, l2] at hl
  rw [l3] at hc
  have := Nat.sub_add_cancel h1
  rw [Nat.sub_mul] at hl
  omega

/-! ### The same unread bytes in two arrays -/

/-- Two positions, each in its own array with its own stop, with the same unread bytes. -/
def Same (a1 : ByteArray) (e1 : USize) (a2 : ByteArray) (e2 : USize) (p1 p2 : USize) : Prop :=
  e1.toNat ≤ a1.size ∧ e2.toNat ≤ a2.size ∧ p1.toNat ≤ e1.toNat ∧ p2.toNat ≤ e2.toNat ∧
    e1.toNat - p1.toNat = e2.toNat - p2.toNat ∧ chunk a1 p1.toNat e1.toNat = chunk a2 p2.toNat e2.toNat

private theorem usize_add' {p u : USize} (h : p.toNat + u.toNat < USize.size) : (p + u).toNat = p.toNat + u.toNat := by
  rw [USize.toNat_add]
  apply Nat.mod_eq_of_lt
  rwa [← USize.size_eq_two_pow]

private theorem chunk_get? {a : ByteArray} {p e k : Nat} (h : p + k < e) : (chunk a p e)[k]? = a.data.toList[p + k]? := by
  unfold chunk
  rw [List.getElem?_take, ite_eq_left (by omega), List.getElem?_drop]

private theorem chunk_drop' {a : ByteArray} {p e k : Nat} : chunk a (p + k) e = (chunk a p e).drop k := by
  unfold chunk
  rw [List.drop_take, List.drop_drop]
  congr 1
  omega

/-- The bytes at the same distance into the same unread bytes. -/
theorem Same.byte {a1 a2 : ByteArray} {e1 e2 p1 p2 : USize} (h : Same a1 e1 a2 e2 p1 p2) {k : Nat}
    (hk : p1.toNat + k < e1.toNat) : a1.data.toList[p1.toNat + k]? = a2.data.toList[p2.toNat + k]? := by
  obtain ⟨_, _, _, _, h5, h6⟩ := h
  rw [← chunk_get? hk, ← chunk_get? (show p2.toNat + k < e2.toNat by omega), h6]

/-- Moving both positions on by the same amount, within the unread bytes. -/
theorem Same.adv {a1 a2 : ByteArray} {e1 e2 p1 p2 : USize} (h : Same a1 e1 a2 e2 p1 p2) {u : USize}
    (hu : u.toNat ≤ e1.toNat - p1.toNat) : Same a1 e1 a2 e2 (p1 + u) (p2 + u) := by
  obtain ⟨h1, h2, h3, h4, h5, h6⟩ := h
  have q1 : (p1 + u).toNat = p1.toNat + u.toNat := usize_add' (by have := e1.toNat_lt_size; omega)
  have q2 : (p2 + u).toNat = p2.toNat + u.toNat := usize_add' (by have := e2.toNat_lt_size; omega)
  refine ⟨h1, h2, by omega, by omega, by omega, ?_⟩
  rw [q1, q2, chunk_drop', chunk_drop', h6]

private theorem uget_same {a1 a2 : ByteArray} {e1 e2 p1 p2 : USize} (h : Same a1 e1 a2 e2 p1 p2) {k : Nat}
    (hk : p1.toNat + k < e1.toNat) (g1 : p1.toNat + k < a1.data.size) (g2 : p2.toNat + k < a2.data.size) :
    a1.data[p1.toNat + k]'g1 = a2.data[p2.toNat + k]'g2 := by
  have e := h.byte hk
  simp only [Array.getElem?_toList, Array.getElem?_eq_getElem g1, Array.getElem?_eq_getElem g2] at e
  exact Option.some.inj e

private theorem loadBuffer_same {a1 a2 : ByteArray} {e1 e2 p1 p2 : USize} (h : Same a1 e1 a2 e2 p1 p2)
    (hk : p1.toNat + 8 ≤ e1.toNat) (h81 : p1.toNat + 8 ≤ a1.size) (hu1 : p1.toNat + 8 ≤ USize.size)
    (h82 : p2.toNat + 8 ≤ a2.size) (hu2 : p2.toNat + 8 ≤ USize.size) :
    loadBuffer a1 p1 h81 hu1 = loadBuffer a2 p2 h82 hu2 := by
  have s1 : a1.size = a1.data.size := rfl
  have s2 : a2.size = a2.data.size := rfl
  simp only [loadBuffer, byteAt_eq]
  rw [uget_same h (k := 0) (by omega) (by omega) (by omega), uget_same h (k := 1) (by omega) (by omega) (by omega),
    uget_same h (k := 2) (by omega) (by omega) (by omega), uget_same h (k := 3) (by omega) (by omega) (by omega),
    uget_same h (k := 4) (by omega) (by omega) (by omega), uget_same h (k := 5) (by omega) (by omega) (by omega),
    uget_same h (k := 6) (by omega) (by omega) (by omega), uget_same h (k := 7) (by omega) (by omega) (by omega)]

private theorem fillSlow_same {a1 a2 : ByteArray} {e1 e2 : USize} (hs1 : e1.toNat ≤ a1.size) (hs2 : e2.toNat ≤ a2.size) :
    ∀ (N : Nat) (word count : UInt64) (p1 p2 : USize), e1.toNat - p1.toNat = N → Same a1 e1 a2 e2 p1 p2 →
    (BitBuffer.fillSlow a1 e1 hs1 word count p1).word = (BitBuffer.fillSlow a2 e2 hs2 word count p2).word ∧
      (BitBuffer.fillSlow a1 e1 hs1 word count p1).count = (BitBuffer.fillSlow a2 e2 hs2 word count p2).count ∧
      Same a1 e1 a2 e2 (BitBuffer.fillSlow a1 e1 hs1 word count p1).pos (BitBuffer.fillSlow a2 e2 hs2 word count p2).pos := by
  intro N
  induction N using Nat.strongRecOn with
  | ind N ih =>
    intro word count p1 p2 hN h
    have hS := h
    obtain ⟨_, _, h3, h4, h5, _⟩ := h
    rw [BitBuffer.fillSlow, BitBuffer.fillSlow]
    by_cases hc : count ≤ 56 ∧ p1 < e1
    · have hlt := USize.lt_iff_toNat_lt.mp hc.2
      have hc2 : count ≤ 56 ∧ p2 < e2 := ⟨hc.1, USize.lt_iff_toNat_lt.mpr (by omega)⟩
      rw [dite_eq_left hc, dite_eq_left hc2]
      have hb : ∀ g1 g2, a1.uget p1 g1 = a2.uget p2 g2 := by
        intro g1 g2
        rw [uget_eq, uget_eq]
        exact uget_same hS (k := 0) (by omega) (by have : a1.size = a1.data.size := rfl; omega)
          (by have : a2.size = a2.data.size := rfl; omega)
      dsimp only
      rw [hb]
      have h1 : (USize.ofNat 1).toNat = 1 := usize_ofNat_toNat (by decide)
      have hq : (p1 + USize.ofNat 1).toNat = p1.toNat + 1 := by
        rw [usize_add' (by have := e1.toNat_lt_size; omega), h1]
      exact ih _ (by omega) _ _ _ _ rfl (hS.adv (u := USize.ofNat 1) (by omega))
    · have hc2 : ¬ (count ≤ 56 ∧ p2 < e2) := fun e => hc ⟨e.1, USize.lt_iff_toNat_lt.mpr
        (by have := USize.lt_iff_toNat_lt.mp e.2; omega)⟩
      rw [dite_eq_right hc, dite_eq_right hc2]
      exact ⟨rfl, rfl, hS⟩

/-- A refill depends only on the unread bytes: the same buffer, and positions with the same unread bytes. -/
theorem refill_same {word count : UInt64} {a1 a2 : ByteArray} {e1 e2 p1 p2 : USize} (hs1 : e1.toNat ≤ a1.size)
    (hs2 : e2.toNat ≤ a2.size) (hp1 : p1.toNat ≤ e1.toNat) (hp2 : p2.toNat ≤ e2.toNat) (h : Same a1 e1 a2 e2 p1 p2) :
    (refill word count a1 p1 e1 hs1 hp1).word = (refill word count a2 p2 e2 hs2 hp2).word ∧
      (refill word count a1 p1 e1 hs1 hp1).count = (refill word count a2 p2 e2 hs2 hp2).count ∧
      Same a1 e1 a2 e2 (refill word count a1 p1 e1 hs1 hp1).pos (refill word count a2 p2 e2 hs2 hp2).pos := by
  have hS := h
  obtain ⟨_, _, _, _, h5, _⟩ := h
  unfold refill
  by_cases h56 : 56 < count
  · rw [ite_eq_left h56, ite_eq_left h56]
    exact ⟨rfl, rfl, hS⟩
  · rw [ite_eq_right h56, ite_eq_right h56]
    have d1 : (e1 - p1).toNat = e1.toNat - p1.toNat := USize.toNat_sub_of_le _ _ (USize.le_iff_toNat_le.mpr hp1)
    have d2 : (e2 - p2).toNat = e2.toNat - p2.toNat := USize.toNat_sub_of_le _ _ (USize.le_iff_toNat_le.mpr hp2)
    have h8 : (USize.ofNat 8).toNat = 8 := usize_ofNat_toNat (by decide)
    by_cases hb : USize.ofNat 8 ≤ e1 - p1
    · have hb1 := USize.le_iff_toNat_le.mp hb
      have hb2 : USize.ofNat 8 ≤ e2 - p2 := USize.le_iff_toNat_le.mpr (by omega)
      rw [dite_eq_left hb, dite_eq_left hb2]
      have key : ∀ g1 u1 g2 u2, loadBuffer a1 p1 g1 u1 = loadBuffer a2 p2 g2 u2 :=
        fun _ _ _ _ => loadBuffer_same hS (by omega) _ _ _ _
      unfold BitBuffer.fill
      dsimp only
      rw [h8, d1] at hb1
      rw [key _ _ (by omega) (by have := e2.toNat_lt_size; omega)]
      refine ⟨rfl, rfl, hS.adv ?_⟩
      have hc : count.toNat ≤ 56 := Nat.le_of_not_lt fun hl => h56 (UInt64.lt_iff_toNat_lt.mpr hl)
      have hk : ((64 - count) >>> 3).toNat ≤ 8 := by
        rw [UInt64.toNat_shiftRight, UInt64.toNat_sub_of_le _ _ (UInt64.le_iff_toNat_le.mpr (by show count.toNat ≤ 64; omega))]
        rw [Nat.shiftRight_eq_div_pow]
        show (64 - count.toNat) / 8 ≤ 8
        omega
      rw [UInt64.toNat_toUSize, Nat.mod_eq_of_lt (by rw [← USize.size_eq_two_pow]; have := USize.le_size; omega)]
      omega
    · have hb2 : ¬ USize.ofNat 8 ≤ e2 - p2 := fun e => hb (USize.le_iff_toNat_le.mpr
        (by have := USize.le_iff_toNat_le.mp e; omega))
      rw [dite_eq_right hb, dite_eq_right hb2]
      exact fillSlow_same hs1 hs2 _ word count p1 p2 rfl hS

end Brotli.Decoder
