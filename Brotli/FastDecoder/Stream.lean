module

public import Brotli.FastDecoder.Header
public import Brotli.FastDecoder.Mem

@[expose] public section

/-!
# The stream layer

The stream's frame (`DESIGN.md` 5.8, 9.5): the decoder's start, the window size, a meta-block's start, and what
follows a meta-block. The two fields are single elements read in exact mode (5.4): read from one refill, tested
that every bit was real, and only then given effect; where a bit is not there nothing changes but the reason, which
becomes "input". Metadata, uncompressed data and the end touch the caller's arrays and are the driver's.

The buffer is given to `start` already large enough: its room and growth belong with the memory limit (9.5).
-/

namespace Brotli.FastDecoder

/-- The constant tables copied into the front (8.1). -/
def startTabs (buf : ByteArray) : ByteArray :=
  let buf := ctxTab.copySlice 0 buf ctxTabAt.toNat 2048
  let buf := cmdInfo.copySlice 0 buf cmdAt.toNat 5632
  let buf := rev8.copySlice 0 buf revAt.toNat 256
  clSym.copySlice 0 buf clSymAt.toNat 64

/-- Copying the tables in leaves the buffer its front. -/
theorem startTabs_front (buf : ByteArray) (h : ringAt.toNat ≤ buf.size) : ringAt.toNat ≤ (startTabs buf).size :=
  Nat.le_trans (Nat.le_trans (Nat.le_trans (Nat.le_trans h (copySlice_size_ge ..)) (copySlice_size_ge ..))
    (copySlice_size_ge ..)) (copySlice_size_ge ..)

/-- The last four distances with their first values, the four zero slots after them (from `Slot.dists`, 256), and the
guard zero. -/
def startDists (buf : ByteArray) (h : ringAt.toNat ≤ buf.size) : ByteArray :=
  let buf := setSlot buf Slot.dists 4 h
  let buf := setSlot buf 264 16 (by sized h)
  let buf := setSlot buf 272 15 (by sized h)
  let buf := setSlot buf 280 11 (by sized h)
  have h : ringAt.toNat ≤ buf.size := by sized h
  let buf := setSlot buf 288 0 h
  let buf := setSlot buf 296 0 (by sized h)
  have h : ringAt.toNat ≤ buf.size := by sized h
  let buf := setSlot buf 304 0 h
  let buf := setSlot buf 312 0 (by sized h)
  store16 buf guardAt 0 (front (by sized h))

@[simp] theorem startDists_size (buf : ByteArray) (h : ringAt.toNat ≤ buf.size) : (startDists buf h).size = buf.size := by
  simp [startDists]

/-- The slots a decoder starts with: nothing staged, no output waiting, and the phase the window size. -/
def startSlots (buf : ByteArray) (h : ringAt.toNat ≤ buf.size) : ByteArray :=
  let buf := setSlot buf Slot.phase Phase.wbits h
  let buf := setSlot buf Slot.reason 0 (by sized h)
  let buf := setSlot buf Slot.bitpos (stageAt <<< 3) (by sized h)
  let buf := setSlot buf Slot.inEnd (stageAt <<< 3) (by sized h)
  have h : ringAt.toNat ≤ buf.size := by sized h
  let buf := setSlot buf Slot.opos ringAt h
  let buf := setSlot buf Slot.handed ringAt (by sized h)
  let buf := setSlot buf Slot.counters 0 (by sized h)
  have h : ringAt.toNat ≤ buf.size := by sized h
  let buf := setSlot buf Slot.lits 0 h
  let buf := setSlot buf Slot.cmd cmdNone (by sized h)
  let buf := setSlot buf Slot.dsymKey 0 (by sized h)
  let buf := setSlot buf Slot.last 0 (by sized h)
  have h : ringAt.toNat ≤ buf.size := by sized h
  let buf := setSlot buf Slot.full 0 h
  setSlot buf Slot.pend 0 (by sized h)

/-- The front of `buf` set up: the constant tables copied in and the slots set. -/
def startOn (buf : ByteArray) (h : ringAt.toNat ≤ buf.size) : ByteArray :=
  startSlots (startDists (startTabs buf) (startTabs_front buf h)) (by simpa using startTabs_front buf h)

@[simp] theorem startSlots_size (buf : ByteArray) (h : ringAt.toNat ≤ buf.size) : (startSlots buf h).size = buf.size := by
  simp [startSlots]

/-- Setting the front up leaves the buffer its front. -/
theorem startOn_front (buf : ByteArray) (h : ringAt.toNat ≤ buf.size) : ringAt.toNat ≤ (startOn buf h).size := by
  unfold startOn
  rw [startSlots_size, startDists_size]
  exact startTabs_front buf h

/-- An array for the front, every byte of the front written (5.2): zeros, for `startOn` to write over. Its room,
`cap`, has space besides for the first tables of the first header, which stand in it until the stream's room is
given (`giveRoom`). -/
@[noinline, never_extract] def newFront (n cap : UInt64) : ByteArray :=
  zeroFill (ByteArray.emptyWithCapacity cap.toNat) 0 n

/-- The decoder's start (2.3, 5.9): its state for a memory limit of `limit` bytes. The front is allocated and
written; the ring and the tables get their room when the first meta-block that produces output has declared what
it needs (`giveRoom`, `growTo`). A limit below the front's size leaves no room for a decoder at all: the state is
then the empty array, for which every call returns "memory limit". -/
def start (limit : UInt64) : ByteArray :=
  if limit < ringAt then ByteArray.empty
  else
    let cap : UInt64 := if limit < ringAt + 49152 then limit else ringAt + 49152
    let buf := newFront ringAt cap
    if h : ringAt.toNat ≤ buf.size then
      let buf := startOn buf h
      have h : ringAt.toNat ≤ buf.size := startOn_front _ h
      let buf := setSlot buf Slot.limit limit h
      let buf := setSlot buf Slot.size ringAt (by sized h)
      let buf := setSlot buf Slot.cap cap (by sized h)
      let buf := setSlot buf Slot.moves 0 (by sized h)
      setSlot buf Slot.room 0 (by sized h)
    else buf


/-- An element could not be read whole: nothing changes but the reason. -/
def wantInput (buf : ByteArray) (h : ringAt.toNat ≤ buf.size) : ByteArray :=
  setSlot buf Slot.reason Reason.input h

@[simp] theorem wantInput_size (buf : ByteArray) (h : ringAt.toNat ≤ buf.size) : (wantInput buf h).size = buf.size := by
  simp [wantInput]

/-- The window size's field, from the bits `w`: the ring is `2 ^` this many bytes (2.1). -/
@[inline] def wbitsOf (w : UInt64) : UInt64 :=
  if w &&& 1 = 0 then 16
  else if (w >>> 1) &&& 7 ≠ 0 then (17 : UInt64) + ((w >>> 1) &&& 7)
  else if (w >>> 4) &&& 7 = 0 then 17 else (8 : UInt64) + ((w >>> 4) &&& 7)

/-- The window size: 1, 4 or 7 bits (2.1), its one unused pattern rejected. It sets the ring's end, `2 ^ WBITS`
bytes past its start, and the window, 16 less. -/
def stepWbits (buf : ByteArray) (h : ringAt.toNat ≤ buf.size) : ByteArray :=
  let bp := slot buf Slot.bitpos h
  let w := bitsAt buf bp
  let n : UInt64 := (w >>> 1) &&& 7
  let k : UInt64 := (w >>> 4) &&& 7
  let nb : UInt64 := if w &&& 1 = 0 then 1 else if n ≠ 0 then 4 else 7
  let wbits : UInt64 := wbitsOf w
  if slot buf Slot.inEnd h < bp + nb then wantInput buf h
  else if nb = 7 ∧ k = 1 then hReject buf h
  else
    let buf := setSlot buf Slot.ringEnd (ringAt + ((1 : UInt64) <<< wbits)) h
    let buf := setSlot buf Slot.win (((1 : UInt64) <<< wbits) - 16) (by sized h)
    let buf := setSlot buf Slot.bitpos (bp + nb) (by sized h)
    setSlot buf Slot.phase Phase.mbStart (by sized h)

/-- After the last meta-block: the end, whose zero bits to the byte boundary are the driver's to check (5.1). -/
def toEnd (buf : ByteArray) (h : ringAt.toNat ≤ buf.size) : ByteArray :=
  setSlot buf Slot.phase Phase.streamEnd h

/-- After a meta-block: the next one's start, or after the last, the end. -/
def afterMb (buf : ByteArray) (h : ringAt.toNat ≤ buf.size) : ByteArray :=
  if slot buf Slot.last h ≠ 0 then toEnd buf h else setSlot buf Slot.phase Phase.mbStart h

/-- The bits of a metadata block's start, from the bits `w` (2.1): whether it is the last, the count of nibbles, the
reserved bit, the count of bytes and the skip length. The bits to the byte boundary follow. -/
@[inline] def metaWidth (w : UInt64) : UInt64 :=
  (1 : UInt64) + (w &&& 1) + 2 + 3 + (((w >>> ((1 : UInt64) + (w &&& 1) + 2 + 1)) &&& (3 : UInt64)) <<< (3 : UInt64))

/-- Where the length ends in the start of a block of data, from the bits `w`: whether it is the last, the count of
nibbles and the nibbles. -/
@[inline] def lenEnd (w : UInt64) : UInt64 :=
  (1 : UInt64) + (w &&& 1) + 2 + ((((w >>> ((1 : UInt64) + (w &&& 1))) &&& (3 : UInt64)) + 4) <<< (2 : UInt64))

/-- The bits of the start of a block of data: to the length's end, and the flag for uncompressed data in a block
that is not the last. -/
@[inline] def dataWidth (w : UInt64) : UInt64 :=
  lenEnd w + (1 - (w &&& 1))

/-- A meta-block's start (2.1, 5.8): one element of at most 31 bits, with the bits to the byte boundary where the
format has them. Whether it is the last, and if so whether it is empty; the count of nibbles; then the length and,
for a block that is not the last, whether it is uncompressed; or, for metadata, the reserved bit, the count of bytes
and the skip length. Rejected (5.10): a length of more than 4 nibbles whose top nibble is zero; metadata with its
reserved bit set, or a skip length of more than one byte whose top byte is zero; a bit that is not zero before the
byte boundary, for metadata and for uncompressed data. -/
def stepMbStart (buf : ByteArray) (h : ringAt.toNat ≤ buf.size) : ByteArray :=
  let bp := slot buf Slot.bitpos h
  let e := slot buf Slot.inEnd h
  let w := bitsAt buf bp
  let islast : UInt64 := w &&& 1
  let empty : UInt64 := islast &&& (w >>> 1)
  let p0 : UInt64 := 1 + islast
  if empty ≠ 0 then
    if e < bp + 2 then wantInput buf h
    else toEnd (setSlot (setSlot buf Slot.bitpos (bp + 2) h) Slot.last 1 (by sized h)) (by sized h)
  else
    let code : UInt64 := (w >>> p0) &&& 3
    let p1 : UInt64 := p0 + 2
    if code = 3 then
      -- metadata
      let reserved : UInt64 := (w >>> p1) &&& 1
      let sb : UInt64 := (w >>> (p1 + 1)) &&& 3
      let v : UInt64 := (w >>> (p1 + 3)) &&& mask (sb <<< 3)
      let p2 : UInt64 := metaWidth w
      let fill : UInt64 := ((0 : UInt64) - (bp + p2)) &&& 7
      if e < bp + p2 + fill then wantInput buf h
      else if reserved ≠ 0 ∨ (1 < sb ∧ v >>> ((sb - 1) <<< 3) = 0) ∨ (w >>> p2) &&& mask fill ≠ 0 then hReject buf h
      else
        let buf := setSlot buf Slot.bitpos (bp + p2 + fill) h
        let buf := setSlot buf Slot.last islast (by sized h)
        let buf := setSlot buf Slot.mbLeft (if sb = 0 then 0 else v + 1) (by sized h)
        setSlot buf Slot.phase Phase.metadata (by sized h)
    else
      let nib : UInt64 := code + 4
      let v : UInt64 := (w >>> p1) &&& mask (nib <<< 2)
      let p2 : UInt64 := lenEnd w
      let unc : UInt64 := if islast = 0 then (w >>> p2) &&& 1 else 0
      let p3 : UInt64 := dataWidth w
      let fill : UInt64 := if unc ≠ 0 then ((0 : UInt64) - (bp + p3)) &&& 7 else 0
      if e < bp + p3 + fill then wantInput buf h
      else if (4 < nib ∧ v >>> ((nib - 1) <<< 2) = 0) ∨ (w >>> p3) &&& mask fill ≠ 0 then hReject buf h
      else
        let buf := setSlot buf Slot.bitpos (bp + p3 + fill) h
        let buf := setSlot buf Slot.last islast (by sized h)
        if unc ≠ 0 then
          let buf := setSlot buf Slot.mbLeft (v + 1) (by sized h)
          setSlot buf Slot.phase Phase.raw (by sized h)
        else
          -- compressed: the meta-block's end, the tables past the smaller of it and the ring's end, and the header
          let mbEnd : UInt64 := slot buf Slot.opos (by sized h) + v + 1
          let re := slot buf Slot.ringEnd (by sized h)
          let top : UInt64 := if slot buf Slot.full (by sized h) ≠ 0 then re else if mbEnd < re then mbEnd else re
          let buf := setSlot buf Slot.mbEnd mbEnd (by sized h)
          let place : UInt64 := (top + margin + (7 : UInt64)) &&& ~~~(7 : UInt64)
          -- the first meta-block that produces output, the room not yet given: its header's first tables go in the
          -- front's array, short of their place, until the header has declared its counts of codes (`giveRoom`)
          let early : Bool := slot buf Slot.room (by sized h) == 0
          let buf := setSlot buf Slot.tabNext (if early then provAt else place) (by sized h)
          let buf := setSlot buf Slot.shift (place - provAt) (by sized h)
          have h : ringAt.toNat ≤ buf.size := by sized h
          let buf := if early then setSlot buf Slot.room 2 h else buf
          headerStart buf (by sized h)

@[simp] theorem stepWbits_size (buf : ByteArray) (h : ringAt.toNat ≤ buf.size) : (stepWbits buf h).size = buf.size := by
  simp [stepWbits, apply_ite ByteArray.size]

@[simp] theorem toEnd_size (buf : ByteArray) (h : ringAt.toNat ≤ buf.size) : (toEnd buf h).size = buf.size := by
  simp [toEnd]

@[simp] theorem afterMb_size (buf : ByteArray) (h : ringAt.toNat ≤ buf.size) : (afterMb buf h).size = buf.size := by
  simp [afterMb, apply_ite ByteArray.size]

@[simp] theorem stepMbStart_size (buf : ByteArray) (h : ringAt.toNat ≤ buf.size) :
    (stepMbStart buf h).size = buf.size := by
  simp [stepMbStart, apply_ite ByteArray.size]

/-! ### The frame's elements: their widths

Facts of arithmetic alone. An element is at most 56 bits, so that one refill covers it (`DESIGN.md` 5.4, the ledger):
the window size is at most 7 bits by its definition, and a meta-block's start, with the bits to the byte boundary, at
most 38. The window size's field gives a ring of `2 ^ 10` to `2 ^ 24` bytes. -/

/-- A value under a mask is no more than the mask. -/
theorem and_le_toNat (x m : UInt64) : (x &&& m).toNat ≤ m.toNat := by
  rw [UInt64.toNat_and]; exact Nat.le_trans Nat.and_le_right (Nat.le_refl _)

/-- The window size's field, where it is not the unused pattern, names a ring of `2 ^ 10` to `2 ^ 24` bytes. -/
theorem wbitsOf_range (w : UInt64)
    (hk : ¬ (w &&& 1 ≠ 0 ∧ (w >>> 1) &&& 7 = 0 ∧ (w >>> 4) &&& 7 = 1)) :
    10 ≤ (wbitsOf w).toNat ∧ (wbitsOf w).toNat ≤ 24 := by
  have hn : ((w >>> 1) &&& 7).toNat ≤ 7 := and_le_toNat _ 7
  have hk7 : ((w >>> 4) &&& 7).toNat ≤ 7 := and_le_toNat _ 7
  unfold wbitsOf
  by_cases h0 : w &&& 1 = 0
  · rw [ite_eq_left h0]; decide
  · rw [ite_eq_right h0]
    by_cases h1 : (w >>> 1) &&& 7 ≠ 0
    · rw [ite_eq_left h1, UInt64.toNat_add]
      have : (17 : UInt64).toNat = 17 := rfl
      omega
    · rw [ite_eq_right h1]
      by_cases h2 : (w >>> 4) &&& 7 = 0
      · rw [ite_eq_left h2]; decide
      · rw [ite_eq_right h2, UInt64.toNat_add]
        have : (8 : UInt64).toNat = 8 := rfl
        have hk0 : ((w >>> 4) &&& 7).toNat ≠ 0 := fun e => h2 (UInt64.toNat_inj.mp e)
        have hk1 : ((w >>> 4) &&& 7).toNat ≠ 1 :=
          fun e => hk ⟨h0, Classical.not_not.mp h1, UInt64.toNat_inj.mp e⟩
        omega

/-- The start of a metadata block, with its skip length and the bits to the byte boundary, is at most 38 bits. -/
theorem metaStart_bits (w a c : UInt64) :
    ((1 : UInt64) + (w &&& 1) + 2 + 3 + ((a &&& (3 : UInt64)) <<< (3 : UInt64)) + (c &&& (7 : UInt64))).toNat ≤ 38 := by
  have h1 : (w &&& 1).toNat ≤ 1 := and_le_toNat _ 1
  have h2 : (a &&& 3).toNat ≤ 3 := and_le_toNat _ 3
  have h3 : (c &&& 7).toNat ≤ 7 := and_le_toNat _ 7
  have e1 : (1 : UInt64).toNat = 1 := rfl
  have e2 : (2 : UInt64).toNat = 2 := rfl
  have e3 : (3 : UInt64).toNat = 3 := rfl
  have hs : ((a &&& 3) <<< 3).toNat = (a &&& 3).toNat * 8 := by
    rw [UInt64.toNat_shiftLeft, Nat.shiftLeft_eq]
    have : (3 : UInt64).toNat % 64 = 3 := rfl
    rw [this]; omega
  simp only [UInt64.toNat_add, hs]
  omega

/-- The start of a block of data, with its length, the flag for uncompressed data where there is one, and the bits to
the byte boundary, is at most 38 bits. A count of nibbles of 3 is metadata, not data. -/
theorem dataStart_bits (w b c : UInt64) (hb : b &&& 3 ≠ 3) :
    ((1 : UInt64) + (w &&& 1) + 2 + (((b &&& (3 : UInt64)) + 4) <<< (2 : UInt64)) + (1 - (w &&& 1)) +
      (c &&& (7 : UInt64))).toNat ≤ 38 := by
  have h1 : (w &&& 1).toNat ≤ 1 := and_le_toNat _ 1
  have h2 : (b &&& 3).toNat ≤ 3 := and_le_toNat _ 3
  have h2n : (b &&& 3).toNat ≠ 3 := fun e => hb (UInt64.toNat_inj.mp e)
  have h3 : (c &&& 7).toNat ≤ 7 := and_le_toNat _ 7
  have e1 : (1 : UInt64).toNat = 1 := rfl
  have e2 : (2 : UInt64).toNat = 2 := rfl
  have e4 : (4 : UInt64).toNat = 4 := rfl
  have hn : ((b &&& 3) + 4).toNat = (b &&& 3).toNat + 4 := by rw [UInt64.toNat_add]; omega
  have hs : (((b &&& 3) + 4) <<< 2).toNat = ((b &&& 3).toNat + 4) * 4 := by
    rw [UInt64.toNat_shiftLeft, Nat.shiftLeft_eq, hn]
    have : (2 : UInt64).toNat % 64 = 2 := rfl
    rw [this]; omega
  have hm : ((1 : UInt64) - (w &&& 1)).toNat = 1 - (w &&& 1).toNat := by
    rw [UInt64.toNat_sub_of_le _ _ (by rw [UInt64.le_iff_toNat_le]; omega)]; omega
  simp only [UInt64.toNat_add, hs, hm]
  omega

/-- A metadata block's start as the decoder reads it (`stepMbStart`), with the bits to the byte boundary, is at most
38 bits: one refill covers it. -/
theorem metaWidth_le (w c : UInt64) : (metaWidth w + (c &&& (7 : UInt64))).toNat ≤ 38 :=
  metaStart_bits w _ c

/-- The same for the start of a block of data, which is what the decoder reads where the count of nibbles is not 3. -/
theorem dataWidth_le (w c : UInt64) (hb : (w >>> ((1 : UInt64) + (w &&& 1))) &&& 3 ≠ 3) :
    (dataWidth w + (c &&& (7 : UInt64))).toNat ≤ 38 :=
  dataStart_bits w _ c hb
