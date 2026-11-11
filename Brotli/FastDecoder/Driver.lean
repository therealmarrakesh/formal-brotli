module

public import Brotli.FastDecoder.Event

@[expose] public section

/-!
# The driver

The one function that holds the caller's two arrays as well as `buf` (`DESIGN.md` 5.1, 9.3). Each time round it
reads the phase and does one thing: a step of the header; the command loop, in the mode the input ahead allows; or
what touches the caller's arrays or ends the call: staging input (5.4), handing out output (5.5), returning a status.

**Pausing for input.** A loop that cannot go on for want of input leaves for the reason "input". If the chunk has
more, the next piece is staged. If it has none, the command loop is run in exact mode, which reads the last bits an
element at a time (the header chooses its own mode by what lies ahead). When exact mode too stops for input, the
bytes received hold no further whole element: what waits is handed out and the call returns "needs input", or
"rejected" if the caller has said the input ends here.

**Pausing for output.** The command loop is given a bound one byte beyond what the caller can take (5.5), so it stops
with more waiting than there is room for; the driver hands out what fits and returns "needs output".

**The stream's frame** (5.8, 9.5). The window size and a meta-block's start are single elements, read exactly by
`Stream.lean`'s steps once a refill's worth of input is staged or the chunk is used up. Metadata is skipped and
uncompressed data copied here, since both take bytes straight from the caller's chunk once the staged ones are used.
A meta-block of commands is over when the loop stops before a head with the meta-block's last byte produced. After
the last meta-block any further byte rejects, and the call returns "done" once the caller has said the input ends.

**Events** (5.1, 9.7). What the command loop leaves for is done by the handlers of `Event.lean`, called here by the
reason: a block switch; a command that does not fit, which becomes a command in pieces, done a piece at a time with
this loop between the pieces to stage input, hand out output and wrap; a copy that needs care; a meta-block's end.
The loop's own bound stops at the window's end in the ring: the ring's last 16 bytes are the handlers', which
compare a distance with the window and the bytes produced both.

**The wrap** (5.5). With the output at the ring's end and more to come, what waits is handed out, the ring's last two
bytes go to the guard, and the output goes back to the ring's start.

The bounds rest on the decoder's invariant and are left to the final proof (`Owed.lean`).
-/

namespace Brotli.FastDecoder

/-- What a call returns (2.3). -/
inductive Status where
  | needsInput
  | needsOutput
  | done
  | rejected
  | memLimit
  deriving DecidableEq, Repr, Inhabited

/-- A call's reply (2.3): the state, the bytes of the chunk it used, the caller's buffer with output appended, and
the status. The only thing a call allocates. -/
structure Reply where
  state : ByteArray
  used : UInt64
  out : ByteArray
  status : Status

/-- The next piece of the caller's chunk staged (5.4): the unread tail moved to the area's front, `bitpos` lowered by
what was dropped, as much of the chunk from `ipos` as there is room for copied after it, and zeros written after the
last real byte for the margin. `Slot.inEnd` becomes the last real bit, and `Slot.took` the bytes taken. -/
def stageIn (buf : ByteArray) (inp : @& ByteArray) (ipos stop : UInt64) (h : ringAt.toNat ≤ buf.size) : ByteArray :=
  let bp := slot buf Slot.bitpos h
  let src : UInt64 := bp >>> 3
  let tail : UInt64 := (slot buf Slot.inEnd h >>> 3) - src
  let buf1 := if src = stageAt then buf else move buf stageAt src tail owed
  have h1 : ringAt.toNat ≤ buf1.size := by sized h
  let room : UInt64 := stageSize - margin - tail
  let n : UInt64 := if stop - ipos < room then stop - ipos else room
  let buf2 := inp.copySlice ipos.toNat buf1 (stageAt + tail).toNat n.toNat
  have h2 : ringAt.toNat ≤ buf2.size := Nat.le_trans h1 (copySlice_size_ge ..)
  let e : UInt64 := stageAt + tail + n
  let buf := fill64 buf2 e 8 8 0 owed
  have h : ringAt.toNat ≤ buf.size := by sized h2
  let buf := setSlot buf Slot.bitpos ((stageAt <<< 3) + (bp &&& 7)) h
  let buf := setSlot buf Slot.inEnd (e <<< 3) (by sized h)
  setSlot buf Slot.took n (by sized h)

/-- Staging leaves the buffer its front. -/
theorem stageIn_front (buf : ByteArray) (inp : ByteArray) (ipos stop : UInt64) (h : ringAt.toNat ≤ buf.size) :
    ringAt.toNat ≤ (stageIn buf inp ipos stop h).size := by
  unfold stageIn
  simp only [setSlot_size, fill64_size]
  refine Nat.le_trans ?_ (copySlice_size_ge ..)
  sized h

/-- The command loop entered in one of its four compiled forms. -/
def runLoop (buf : ByteArray) (exact : Bool) (h : ringAt.toNat ≤ buf.size) : ByteArray :=
  if slot buf Slot.triv h ≠ 0 then
    if exact then runTrivExact buf h else runTriv buf h
  else
    if exact then runCtxExact buf h else runCtx buf h

/-- The driver. `inp` from `ipos` to `stop` is what is left of the caller's chunk, which began at `start`; `last`
says the input ends with it; `out` is the caller's buffer, to be filled no further than `outEnd`. -/
def drive (inp : @& ByteArray) (start stop : UInt64) (last : Bool) (outEnd : UInt64) (buf : ByteArray)
    (ipos : UInt64) (out : ByteArray) : Reply :=
  if h : ringAt.toNat ≤ buf.size then
    let phase := slot buf Slot.phase h
    let handed := slot buf Slot.handed h
    let waiting : UInt64 := slot buf Slot.opos h - handed
    let space : UInt64 := outEnd - out.size.toUInt64
    -- the bytes received hold no further whole element: everything they produced is handed out (2.4), and the call
    -- ends
    let pause := fun (buf : ByteArray) (out : ByteArray) (h : ringAt.toNat ≤ buf.size) =>
      let handed := slot buf Slot.handed h
      let waiting : UInt64 := slot buf Slot.opos h - handed
      let space : UInt64 := outEnd - out.size.toUInt64
      let n : UInt64 := if space < waiting then space else waiting
      let out := buf.copySlice handed.toNat out out.size n.toNat
      let buf := setSlot buf Slot.handed (handed + n) h
      if space < waiting then (⟨buf, ipos - start, out, .needsOutput⟩ : Reply)
      else if last then ⟨setSlot buf Slot.phase Phase.rejected (by sized h), ipos - start, out, .rejected⟩
      else ⟨buf, ipos - start, out, .needsInput⟩
    -- the next piece of the chunk staged, and round again
    let more := fun (buf : ByteArray) (out : ByteArray) (h : ringAt.toNat ≤ buf.size) =>
      let buf1 := stageIn buf inp ipos stop h
      have h1 : ringAt.toNat ≤ buf1.size := stageIn_front buf inp ipos stop h
      drive inp start stop last outEnd buf1 (ipos + slot buf1 Slot.took h1) out
    -- the wrap (5.5), with the output at the ring's end and no more waiting than the caller has room for: what
    -- waits is handed out, the ring's last two bytes go to the guard, and the output goes back to the ring's start.
    -- The meta-block's end moves back with it
    let wrap := fun (buf : ByteArray) (out : ByteArray) (h : ringAt.toNat ≤ buf.size) =>
      let handed := slot buf Slot.handed h
      let re := slot buf Slot.ringEnd h
      let out := buf.copySlice handed.toNat out out.size (re - handed).toNat
      let mb := slot buf Slot.mbEnd h
      let buf1 := store16 buf guardAt (load16 buf (re - 2) owed) (front h)
      have h1 : ringAt.toNat ≤ buf1.size := by sized h
      let buf := setSlot buf1 Slot.opos ringAt h1
      let buf := setSlot buf Slot.handed ringAt (by sized h1)
      let buf := setSlot buf Slot.mbEnd (mb - (re - ringAt)) (by sized h1)
      let buf := setSlot buf Slot.full 1 (by sized h1)
      drive inp start stop last outEnd buf ipos out
    if phase = Phase.header then
      -- as for the commands below: the margin is made up first if the chunk has more, so that the header reads the
      -- last bits of a staged piece an element at a time only when the chunk is used up
      if slot buf Slot.inEnd h - slot buf Slot.bitpos h < ((margin + 8) <<< 3) ∧ ipos < stop then more buf out h
      else
        let buf := headerStep (setSlot buf Slot.reason 0 h) (by sized h)
        have h : ringAt.toNat ≤ buf.size := by sized h
        if slot buf Slot.reason h ≠ Reason.input then drive inp start stop last outEnd buf ipos out
        else if ipos < stop then more buf out h
        else pause buf out h
    else if phase = Phase.commands then
      let opos := slot buf Slot.opos h
      let re := slot buf Slot.ringEnd h
      let mb := slot buf Slot.mbEnd h
      if space < waiting then
        -- more waits than the caller has room for: what fits is handed out
        let out := buf.copySlice handed.toNat out out.size space.toNat
        ⟨setSlot buf Slot.handed (handed + space) h, ipos - start, out, .needsOutput⟩
      else if opos = re ∧ opos ≠ mb then wrap buf out h
      else
        -- running mode holds only while the margin of real input lies ahead (5.4): a loop taken up in the middle of a
        -- command reads on without a test. So the margin is made up first if the chunk has more, and where it has
        -- none the loop runs in exact mode
        let short : Bool := slot buf Slot.inEnd h - slot buf Slot.bitpos h < ((margin + 8) <<< 3)
        if short ∧ ipos < stop then more buf out h
        else
          -- one byte more than the caller can take (5.5)
          let cap : UInt64 := handed + space + 1
          -- after a handler: an element was short (the chunk's next piece, or the end of what the bytes received
          -- hold), or round again
          let after := fun (buf : ByteArray) (h : ringAt.toNat ≤ buf.size) =>
            if slot buf Slot.reason h ≠ Reason.input then drive inp start stop last outEnd buf ipos out
            else if ipos < stop then more buf out h
            else pause buf out h
          if slot buf Slot.pend h ≠ 0 then
            -- a command in pieces: its next piece, no further than the meta-block's end, the ring's end and the cap
            let buf := setSlot buf Slot.lim (lo (lo mb re) cap) h
            let buf := piece (setSlot buf Slot.reason 0 (by sized h)) (by sized h)
            after buf (by sized h)
          else
            -- the loop's bound (5.5, 9.7): the meta-block's end, the window's end in the ring (the ring's last 16
            -- bytes are the handlers'), the cap
            let buf := setSlot buf Slot.bound (lo (lo mb (ringAt + slot buf Slot.win h)) cap) h
            let buf := runLoop buf short (by sized h)
            have h : ringAt.toNat ≤ buf.size := owed
            let reason := slot buf Slot.reason h
            if reason = Reason.input then
              if short then pause buf out h else drive inp start stop last outEnd buf ipos out
            else if (reason = Reason.command ∨ reason = Reason.icSwitch) ∧ slot buf Slot.opos h = slot buf Slot.mbEnd h then
              -- the loop stopped before a head (or before the block switch a head would need) with the meta-block's
              -- last byte produced: the meta-block is over
              drive inp start stop last outEnd (endMb buf h) ipos out
            else
              -- an event, by the reason the loop left for
              let buf := setSlot buf Slot.reason 0 h
              have h : ringAt.toNat ≤ buf.size := by sized h
              let buf :=
                if reason = Reason.icSwitch then switchBlock buf 1 h (by decide)
                else if reason = Reason.distSwitch then switchBlock buf 2 h (by decide)
                else if reason = Reason.copy then pieceFromCopy buf h
                else pieceHead buf h
              after buf (by sized h)
    else if phase = Phase.wbits ∨ phase = Phase.mbStart then
      -- one element, read exactly (5.8): the chunk's next piece is staged first if less than a refill lies ahead
      if slot buf Slot.inEnd h - slot buf Slot.bitpos h < 64 ∧ ipos < stop then more buf out h
      else
        let buf := setSlot buf Slot.reason 0 h
        let buf := if phase = Phase.wbits then stepWbits buf (by sized h) else stepMbStart buf (by sized h)
        have h : ringAt.toNat ≤ buf.size := by sized h
        if slot buf Slot.reason h ≠ Reason.input then drive inp start stop last outEnd buf ipos out
        else if ipos < stop then more buf out h
        else pause buf out h
    else if phase = Phase.metadata then
      -- the bytes to skip (5.8): those staged, then the chunk's own, which are never copied
      let left := slot buf Slot.mbLeft h
      let bp := slot buf Slot.bitpos h
      let avail : UInt64 := (slot buf Slot.inEnd h - bp) >>> 3
      if left = 0 then drive inp start stop last outEnd (afterMb buf h) ipos out
      else if avail ≠ 0 then
        let k : UInt64 := if avail < left then avail else left
        let buf := setSlot buf Slot.bitpos (bp + (k <<< 3)) h
        drive inp start stop last outEnd (setSlot buf Slot.mbLeft (left - k) (by sized h)) ipos out
      else if ipos < stop then
        let k : UInt64 := if stop - ipos < left then stop - ipos else left
        drive inp start stop last outEnd (setSlot buf Slot.mbLeft (left - k) h) (ipos + k) out
      else pause buf out h
    else if phase = Phase.raw then
      -- uncompressed bytes (5.8), copied to the ring: those staged, then the chunk's own straight from the caller's
      -- array, no further than the ring's end and one byte more than the caller can take
      let left := slot buf Slot.mbLeft h
      let opos := slot buf Slot.opos h
      let re := slot buf Slot.ringEnd h
      if left = 0 then drive inp start stop last outEnd (afterMb buf h) ipos out
      else if space < waiting then
        let out := buf.copySlice handed.toNat out out.size space.toNat
        ⟨setSlot buf Slot.handed (handed + space) h, ipos - start, out, .needsOutput⟩
      else if opos = re then wrap buf out h
      else
        let n0 : UInt64 := if re - opos < left then re - opos else left
        let cap : UInt64 := handed + space + 1 - opos
        let n : UInt64 := if cap < n0 then cap else n0
        let bp := slot buf Slot.bitpos h
        let avail : UInt64 := (slot buf Slot.inEnd h - bp) >>> 3
        if avail ≠ 0 then
          let k : UInt64 := if avail < n then avail else n
          let buf := move buf opos (bp >>> 3) k owed
          have h : ringAt.toNat ≤ buf.size := by sized h
          let buf := setSlot buf Slot.bitpos (bp + (k <<< 3)) h
          let buf := setSlot buf Slot.opos (opos + k) (by sized h)
          drive inp start stop last outEnd (setSlot buf Slot.mbLeft (left - k) (by sized h)) ipos out
        else if ipos < stop then
          let k : UInt64 := if stop - ipos < n then stop - ipos else n
          let buf := inp.copySlice ipos.toNat buf opos.toNat k.toNat
          have h : ringAt.toNat ≤ buf.size := Nat.le_trans h (copySlice_size_ge ..)
          let buf := setSlot buf Slot.opos (opos + k) h
          drive inp start stop last outEnd (setSlot buf Slot.mbLeft (left - k) (by sized h)) (ipos + k) out
        else pause buf out h
    else if phase = Phase.streamEnd then
      -- the stream is over (5.8). First the bits to the byte boundary, which must be zero: they lie in the byte the
      -- reading stands in, so they are there. Then a further byte rejects; what waits is handed out, and the call
      -- returns "done" once the caller has said the input ends here
      let bp := slot buf Slot.bitpos h
      let fill : UInt64 := ((0 : UInt64) - bp) &&& 7
      if fill ≠ 0 then
        if bitsAt buf bp &&& mask fill ≠ 0 then drive inp start stop last outEnd (hReject buf h) ipos out
        else drive inp start stop last outEnd (setSlot buf Slot.bitpos (bp + fill) h) ipos out
      else
      if slot buf Slot.inEnd h ≠ slot buf Slot.bitpos h ∨ ipos < stop then
        drive inp start stop last outEnd (hReject buf h) ipos out
      else
        let n : UInt64 := if space < waiting then space else waiting
        let out := buf.copySlice handed.toNat out out.size n.toNat
        let buf := setSlot buf Slot.handed (handed + n) h
        if space < waiting then ⟨buf, ipos - start, out, .needsOutput⟩
        else if last then ⟨setSlot buf Slot.phase Phase.done (by sized h), ipos - start, out, .done⟩
        else ⟨buf, ipos - start, out, .needsInput⟩
    else if phase = Phase.done then ⟨buf, ipos - start, out, .done⟩
    else if phase = Phase.rejected then
      -- the bytes of this chunk up to where the reading stood when it was rejected (5.4)
      let unread : UInt64 := (slot buf Slot.inEnd h >>> 3) - ((slot buf Slot.bitpos h + 7) >>> 3)
      ⟨buf, (if ipos - start < unread then 0 else ipos - start - unread), out, .rejected⟩
    else if phase = Phase.memLimit then ⟨buf, ipos - start, out, .memLimit⟩
    else ⟨buf, ipos - start, out, .rejected⟩
  else ⟨buf, ipos - start, out, .rejected⟩
termination_by stop.toNat - ipos.toNat
decreasing_by all_goals exact owed

/-- One call (2.3): the chunk of `inp` from `start` to `stop`, the caller's buffer `out` with `space` bytes of room,
and whether the input ends with this chunk. -/
def call (buf : ByteArray) (inp : @& ByteArray) (start stop : UInt64) (out : ByteArray) (space : UInt64)
    (last : Bool) : Reply :=
  drive inp start stop last (out.size.toUInt64 + space) buf start out
