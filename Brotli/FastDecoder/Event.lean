module

public import Brotli.FastDecoder.Stream

@[expose] public section

/-!
# The event handlers

What the command loop leaves for (`DESIGN.md` 5.1, 5.6, 5.10, 9.7): a block switch, a command that does not fit whole,
a copy that needs care, a meta-block's end. Each is a function from `buf` to `buf`, called by the driver, run once an
event. They read with the loop's reading functions, always exactly: an element is read whole, tested that every bit
was real, and only then given effect; where a bit is not there nothing changes but the reason, which becomes "input".
A rule of the format broken sets the phase to rejected.

**A command in pieces.** A command the loop did not admit is done here a piece at a time, its state in three slots
(`Slot.pend`, `Slot.owed`, `Slot.pdist`): the head; the literals, as many at a time as their block's count and the
output's bound allow; the distance; the copy or the dictionary word, cut where the bound cuts it. Between pieces the
driver does what a piece cannot: staging input, handing out output, the wrap. The bound here (`Slot.lim`) is the
least of the meta-block's end, the ring's end and one byte more than the caller can take.

The bounds rest on the decoder's invariant and are left to the final proof (`Owed.lean`).
-/

namespace Brotli.FastDecoder

/-! The stages of a command in pieces, in `Slot.pend` from bit 32; below them the copy length (bits 0 to 24), whether
the distance is the last one (25) and the distance's context (26 and 27), as in the loop's command word. -/
namespace Pend

def lits : UInt64 := 1
def dist : UInt64 := 2
def copy : UInt64 := 3
def word : UInt64 := 4

end Pend

/-! ### Block switches -/

/-- A block switch in category `c` (0 literals, 1 insert-and-copy, 2 distances): one element, the type's symbol, the
count's symbol and the count's extra bits, at most 54 bits. Rejected (5.10): a category of one type, whose count no
valid meta-block exhausts; the type already current. The category's current type and the one before, its count, the
table or row the loop reads for it, and the set of types seen are brought up to date. -/
@[noinline] def switchBlock (buf : ByteArray) (c : UInt64) (h : ringAt.toNat ≤ buf.size) (hc : c.toNat ≤ 2) :
    ByteArray :=
  let ca := catAt c
  let n := load64 buf (ca + Cat.n) (catSlot h hc Cat.n)
  if n < 2 then hReject buf h
  else
    let bp := slot buf Slot.bitpos h
    let w := bitsAt buf bp
    let e := lookup buf (load64 buf (ca + Cat.typeName) (catSlot h hc Cat.typeName)) w
    let l1 : UInt64 := e &&& 15
    let sym : UInt64 := e >>> 4
    let cur := load64 buf (ca + Cat.cur) (catSlot h hc Cat.cur)
    let prev := load64 buf (ca + Cat.prev) (catSlot h hc Cat.prev)
    let t : UInt64 := if sym = 0 then prev else if sym = 1 then (if cur + 1 = n then 0 else cur + 1) else sym - 2
    let e2 := lookup buf (load64 buf (ca + Cat.countName) (catSlot h hc Cat.countName)) (w >>> l1)
    let info := load32 countTab ((e2 >>> 4) <<< 2) owed
    let nb : UInt64 := info >>> 24
    let l2 : UInt64 := e2 &&& 15
    let count : UInt64 := (info &&& (0xFFFF : UInt64)) + ((w >>> (l1 + l2)) &&& mask nb)
    let total : UInt64 := l1 + l2 + nb
    if slot buf Slot.inEnd h < bp + total then wantInput buf h
    else if t = cur then hReject buf h
    else
      let buf1 := store64 buf (ca + Cat.prev) cur (catSlot h hc Cat.prev)
      let buf2 := store64 buf1 (ca + Cat.cur) t (catSlot (by sized h) hc Cat.cur)
      let sw : UInt64 := seenAt + (c <<< 5) + ((t >>> 6) <<< 3)
      let buf3 := store64 buf2 sw (load64 buf2 sw owed ||| ((1 : UInt64) <<< (t &&& 63))) owed
      have h3 : ringAt.toNat ≤ buf3.size := by sized h
      let buf := setSlot buf3 Slot.bitpos (bp + total) h3
      have h : ringAt.toNat ≤ buf.size := by sized h3
      let counters := slot buf Slot.counters h
      if c = 0 then
        let mode := load8 buf (slot buf Slot.modesAt h + t) owed
        let lit := load32 buf (slot buf Slot.litNamesAt h + (load8 buf (slot buf Slot.lmapAt h + (t <<< 6)) owed <<< 2)) owed
        let buf := setSlot buf Slot.ctxRow (slot buf Slot.rowsL h + (t <<< 13)) h
        let buf := setSlot buf Slot.ctxOff (ctxTabAt + (mode <<< 9) + 256) (by sized h)
        let buf := setSlot buf Slot.litRow lit (by sized h)
        setSlot buf Slot.counters ((counters &&& ~~~litMask) ||| count) (by sized h)
      else if c = 1 then
        let buf := setSlot buf Slot.icTable (load64 buf (slot buf Slot.icNamesAt h + (t <<< 3)) owed) h
        setSlot buf Slot.icLeft count (by sized h)
      else
        let buf := setSlot buf Slot.distRow (slot buf Slot.rowsD h + (t <<< 5)) h
        setSlot buf Slot.counters ((counters &&& ~~~distMask) ||| (count <<< 25)) (by sized h)

/-! ### A meta-block's end -/

/-- Whether every block type of category `c` was seen (5.10). -/
def seenAll (buf : ByteArray) (c : UInt64) (h : ringAt.toNat ≤ buf.size) (hc : c.toNat ≤ 2) : Bool :=
  let n := load64 buf (catAt c + Cat.n) (catSlot h hc Cat.n)
  let p : UInt64 := seenAt + (c <<< 5)
  -- the bits a word of the set must hold: the types from `64 * i` that are below `n`
  let want := fun (i : UInt64) =>
    if (i + 1) <<< 6 ≤ n then (0xFFFFFFFFFFFFFFFF : UInt64) else if i <<< 6 < n then mask (n - (i <<< 6)) else 0
  load64 buf p (seenBase h hc) &&& want 0 == want 0 && load64 buf (p + 8) (seenSlot h hc 8) &&& want 1 == want 1 &&
    load64 buf (p + 16) (seenSlot h hc 16) &&& want 2 == want 2 && load64 buf (p + 24) (seenSlot h hc 24) &&& want 3 == want 3

/-- A meta-block of commands is over: every block type declared must have been used; then what follows it. -/
@[noinline] def endMb (buf : ByteArray) (h : ringAt.toNat ≤ buf.size) : ByteArray :=
  if seenAll buf 0 h (by decide) && seenAll buf 1 h (by decide) && seenAll buf 2 h (by decide) then afterMb buf h
  else hReject buf h

/-! ### A command in pieces -/

/-- The head of a command the loop did not admit, read again: the insert-and-copy symbol and both lengths' extra
bits, at most 63 bits, the extra bits from a refill of their own. The command becomes the one in pieces, its
literals owed. -/
@[noinline] def pieceHead (buf : ByteArray) (h : ringAt.toNat ≤ buf.size) : ByteArray :=
  let bp := slot buf Slot.bitpos h
  let e := lookupW buf (slot buf Slot.icTable h) (bitsAt buf bp)
  let total : UInt64 := elemBitsOf e
  let x := bitsAt buf (bp + (e &&& 15))
  let ie : UInt64 := extraOf e
  let ilen : UInt64 := headIlen e x ie
  let clen : UInt64 := headClen e x ie
  if slot buf Slot.inEnd h < bp + total then wantInput buf h
  else
    let buf := setSlot buf Slot.icLeft (slot buf Slot.icLeft h - 1) h
    let buf := setSlot buf Slot.bitpos (bp + total) (by sized h)
    let buf := setSlot buf Slot.owed ilen (by sized h)
    let buf := setSlot buf Slot.cmd cmdNone (by sized h)
    let buf := setSlot buf Slot.lits 0 (by sized h)
    setSlot buf Slot.pend (clen ||| headFlags e ||| (Pend.lits <<< (32 : UInt64))) (by sized h)

/-- A copy the loop left for, with its distance read: it becomes the copy of a command in pieces. -/
def pieceFromCopy (buf : ByteArray) (h : ringAt.toNat ≤ buf.size) : ByteArray :=
  let clen : UInt64 := slot buf Slot.cmd h &&& 0x1FFFFFF
  let buf1 := setSlot buf Slot.pdist (slot buf Slot.evt h) h
  let buf2 := setSlot buf1 Slot.cmd cmdNone (by sized h)
  let buf3 := setSlot buf2 Slot.lits 0 (by sized h)
  setSlot buf3 Slot.pend (clen ||| (Pend.copy <<< 32)) (by sized h)

/-- Literals read one after another, exactly: `n` of them at most, from the input at `bp` to the output at `opos`,
`v` being what finding a literal's table carries (`LitWay`). It stops at the first literal whose bits are not all
there, with the reason "input". The positions are stored, and in `Slot.evt` how many of the `n` were not read. -/
@[specialize] def litsRun (litName : (buf : ByteArray) → UInt64 → ringAt.toNat ≤ buf.size → UInt64)
    (litNext : (buf : ByteArray) → UInt64 → UInt64 → ringAt.toNat ≤ buf.size → UInt64)
    (buf : ByteArray) (bp opos v n : UInt64) (h : ringAt.toNat ≤ buf.size) : ByteArray :=
  let fin := fun (buf : ByteArray) (reason : UInt64) (h : ringAt.toNat ≤ buf.size) =>
    let buf := setSlot buf Slot.bitpos bp h
    let buf := setSlot buf Slot.opos opos (by sized h)
    let buf := setSlot buf Slot.evt n (by sized h)
    setSlot buf Slot.reason reason (by sized h)
  if hn : n = 0 then fin buf 0 h
  else
    let e := lookup8 buf (litName buf v h) (bitsAt buf bp)
    if slot buf Slot.inEnd h < bp + (e &&& 15) then fin buf Reason.input h
    else
      have : (n - 1).toNat < n.toNat := pred_lt hn
      -- what the next literal's table needs is read before the store, so that the store finds `buf` held once
      let v' : UInt64 := litNext buf v (e >>> 4) h
      litsRun litName litNext (store8 buf opos (e >>> 4) owed) (bp + (e &&& 15)) (opos + 1) v'
        (n - 1) (by sized h)
termination_by n.toNat

@[simp] theorem litsRun_size (litName : (buf : ByteArray) → UInt64 → ringAt.toNat ≤ buf.size → UInt64)
    (litNext : (buf : ByteArray) → UInt64 → UInt64 → ringAt.toNat ≤ buf.size → UInt64)
    (buf : ByteArray) (bp opos v n : UInt64) (h : ringAt.toNat ≤ buf.size) :
    (litsRun litName litNext buf bp opos v n h).size = buf.size := by
  fun_induction litsRun litName litNext buf bp opos v n h <;> simp_all +zetaDelta

/-- The literals a command in pieces owes: as many as their block's count and the bound allow, read here. With none
owed the command goes on to its distance, or ends where the output stands at the meta-block's end (2.1). Rejected:
a literal owed at the meta-block's end. Where the block's count is spent its switch is read first; where the bound
leaves no room nothing is done, and the driver makes room. -/
@[noinline] def pieceLits (buf : ByteArray) (h : ringAt.toNat ≤ buf.size) : ByteArray :=
  let left := slot buf Slot.owed h
  let opos := slot buf Slot.opos h
  let pend := slot buf Slot.pend h
  if left = 0 then
    if opos = slot buf Slot.mbEnd h then setSlot buf Slot.pend 0 h
    else setSlot buf Slot.pend ((pend &&& (0xFFFFFFFF : UInt64)) ||| (Pend.dist <<< (32 : UInt64))) h
  else if opos = slot buf Slot.mbEnd h then hReject buf h
  else
    let counters := slot buf Slot.counters h
    if counters &&& litMask = 0 then switchBlock buf 0 h (by decide)
    else
      let n : UInt64 := lo (lo left (counters &&& litMask)) (slot buf Slot.lim h - opos)
      let bp := slot buf Slot.bitpos h
      let buf1 :=
        if slot buf Slot.triv h ≠ 0 then litsRun trivWay.name trivWay.next buf bp opos (trivWay.init buf opos h) n h
        else litsRun ctxWay.name ctxWay.next buf bp opos (ctxWay.init buf opos h) n h
      have h1 : ringAt.toNat ≤ buf1.size := by sized h
      let done : UInt64 := n - slot buf1 Slot.evt h1
      let buf2 := setSlot buf1 Slot.owed (left - done) h1
      setSlot buf2 Slot.counters (counters - done) (by sized h1)

/-- The distance of a command in pieces: the last one again, or an element read exactly, the symbol and its extra
bits, with the loop's formula. Where the distance block's count is spent its switch is read first. -/
@[noinline] def pieceDist (buf : ByteArray) (h : ringAt.toNat ≤ buf.size) : ByteArray :=
  let pend := slot buf Slot.pend h
  let counters := slot buf Slot.counters h
  let next : UInt64 := (pend &&& (0xFFFFFFFF : UInt64)) ||| (Pend.copy <<< (32 : UInt64))
  if (pend >>> 25) &&& 1 ≠ 0 then
    let buf1 := setSlot buf Slot.pdist (load64 buf (Slot.dists + ((counters >>> 62) <<< 3)) (distSlot h counters)) h
    setSlot buf1 Slot.pend next (by sized h)
  else if counters &&& distMask = 0 then switchBlock buf 2 h (by decide)
  else
    let bp := slot buf Slot.bitpos h
    let e := lookupW buf (load64 buf (slot buf Slot.distRow h + (((pend >>> 26) &&& 3) <<< 3)) owed) (bitsAt buf bp)
    let total : UInt64 := elemBitsOf e
    let x := bitsAt buf (bp + (e &&& 15))
    let f : UInt64 := distFlags e
    let dist : UInt64 := distOf buf counters e x f
    if slot buf Slot.inEnd h < bp + total then wantInput buf h
    else
      let buf1 := setSlot buf Slot.bitpos (bp + total) h
      let buf2 := setSlot buf1 Slot.counters (counters - distOne) (by sized h)
      let buf3 := setSlot buf2 Slot.pdist (dist ||| (distPush f <<< (62 : UInt64))) (by sized h)
      setSlot buf3 Slot.pend next (by sized h)

/-- `n` bytes copied one at a time from `src` to `dst`, as the format defines a copy (2.1): a byte may be one this
copy wrote. The source goes round the ring: past its end `re` it is `size` back. -/
def copyRun (buf : ByteArray) (dst src n re size : UInt64) : ByteArray :=
  if hn : n = 0 then buf
  else
    have : (n - 1).toNat < n.toNat := pred_lt hn
    let s : UInt64 := if re ≤ src then src - size else src
    copyRun (store8 buf dst (load8 buf s owed) owed) (dst + 1) (s + 1) (n - 1) re size
termination_by n.toNat

@[simp] theorem copyRun_size (buf : ByteArray) (dst src n re size : UInt64) :
    (copyRun buf dst src n re size).size = buf.size := by
  fun_induction copyRun buf dst src n re size <;> simp_all +zetaDelta

/-- A dictionary word of `outlen` bytes (the transform `tid` of the `n` bytes at `src`) written: whole at `opos`
where the `room` allows; where not, to the side (the table builder's links, idle in this phase), to be moved out in
parts. -/
def wordOut (buf : ByteArray) (opos src n tid outlen room : UInt64) (h : ringAt.toNat ≤ buf.size) : ByteArray :=
  if outlen ≤ room then
    let buf1 := wordPut buf opos src n tid
    have h1 : ringAt.toNat ≤ buf1.size := by sized h
    let buf2 := setSlot buf1 Slot.opos (opos + outlen) h1
    setSlot buf2 Slot.pend 0 (by sized h1)
  else
    let buf1 := wordPut buf linkAt src n tid
    have h1 : ringAt.toNat ≤ buf1.size := by sized h
    let buf2 := setSlot buf1 Slot.owed outlen h1
    let buf3 := setSlot buf2 Slot.pdist linkAt (by sized h1)
    setSlot buf3 Slot.pend (Pend.word <<< 32) (by sized h1)

/-- A copy from the ring of a command in pieces: the distance `d` pushed if `pd` says so (once: the flag is cleared
with it), then as much of the `clen` bytes copied as the `room` allows, the source taken a ring further on where it
falls before the ring's start; the rest stays owed. -/
def ringOut (buf : ByteArray) (opos d pd clen room re : UInt64) (h : ringAt.toNat ≤ buf.size) : ByteArray :=
  let counters := slot buf Slot.counters h
  let counters' : UInt64 := counters + ((pd >>> 62) <<< 62)
  let buf1 := if pd >>> 62 ≠ 0 then store64 buf (Slot.dists + ((counters' >>> 62) <<< 3)) d (distSlot h counters') else buf
  have h1 : ringAt.toNat ≤ buf1.size := by sized h
  let buf2 := setSlot buf1 Slot.counters counters' h1
  let buf3 := setSlot buf2 Slot.pdist d (by sized h1)
  have h3 : ringAt.toNat ≤ buf3.size := by sized h1
  let n : UInt64 := lo clen room
  -- the source: `d` back, and a ring further on where that falls before the ring's start
  let src : UInt64 := if opos < d + ringAt then opos + (re - ringAt) - d else opos - d
  let buf4 :=
    if n ≤ d ∧ src + n ≤ re then move buf3 opos src n owed else copyRun buf3 opos src n re (re - ringAt)
  have h4 : ringAt.toNat ≤ buf4.size := by sized h3
  setSlot (setSlot buf4 Slot.opos (opos + n) h4) Slot.pend
    (if n = clen then 0 else (clen - n) ||| (Pend.copy <<< (32 : UInt64))) (by simpa using h4)

/-- The copy of a command in pieces, by its distance (2.1, 5.5). Rejected (5.10): a distance of zero or less. The
largest distance is the smaller of the window and the bytes produced.
- *Within it:* a copy from the ring, which may not pass the meta-block's end. The distance is pushed, once. As much
  is copied as the bound allows, the source taken a ring further on where it falls before the ring's start; the rest
  stays owed.
- *Beyond it:* a word of the dictionary, of the copy's length (4 to 24, or rejected) under a transform (its number
  below 121, or rejected), which may not pass the meta-block's end. It is written whole where the bound allows; where
  not, to the side (the table builder's links, idle in this phase), to be moved out in parts. -/
@[noinline] def pieceCopy (buf : ByteArray) (h : ringAt.toNat ≤ buf.size) : ByteArray :=
  let pend := slot buf Slot.pend h
  let pd := slot buf Slot.pdist h
  let d : UInt64 := pd &&& 0xFFFFFFFF
  let clen : UInt64 := pend &&& 0x1FFFFFF
  let opos := slot buf Slot.opos h
  let re := slot buf Slot.ringEnd h
  let win := slot buf Slot.win h
  let room : UInt64 := slot buf Slot.lim h - opos
  let toEnd : UInt64 := slot buf Slot.mbEnd h - opos
  let maxd : UInt64 := if slot buf Slot.full h ≠ 0 then win else lo (opos - ringAt) win
  if d = 0 ∨ 0x80000000 ≤ d then hReject buf h
  else if d ≤ maxd then
    if toEnd < clen then hReject buf h
    else ringOut buf opos d pd clen room re h
  else if 20 < clen - 4 then hReject buf h
  else
    let li := load64 lenTab (clen <<< 3) owed
    let nd : UInt64 := li &&& 31
    let wid : UInt64 := d - maxd - 1
    let tid : UInt64 := wid >>> nd
    if 121 ≤ tid then hReject buf h
    else
      let t : UInt64 := load64 transTab (tid <<< 5) owed
      let first : UInt64 := (t >>> 8) &&& 0xFF
      let om : UInt64 := first + ((t >>> 16) &&& 0xFF)
      let n : UInt64 := if om < clen then clen - om else 0
      let outlen : UInt64 := ((t >>> 24) &&& (0xFF : UInt64)) + n + ((t >>> 32) &&& (0xFF : UInt64))
      if toEnd < outlen then hReject buf h
      else wordOut buf opos ((li >>> 8) + (wid &&& mask nd) * clen + first) n tid outlen room h

/-- A dictionary word's bytes left, moved out from the side as far as the bound allows. -/
@[noinline] def pieceWord (buf : ByteArray) (h : ringAt.toNat ≤ buf.size) : ByteArray :=
  let left := slot buf Slot.owed h
  let at' := slot buf Slot.pdist h
  let opos := slot buf Slot.opos h
  let n : UInt64 := lo left (slot buf Slot.lim h - opos)
  let buf1 := move buf opos at' n owed
  have h1 : ringAt.toNat ≤ buf1.size := by sized h
  let buf2 := setSlot buf1 Slot.opos (opos + n) h1
  let buf3 := setSlot buf2 Slot.owed (left - n) (by sized h1)
  let buf4 := setSlot buf3 Slot.pdist (at' + n) (by sized h1)
  setSlot buf4 Slot.pend (if n = left then 0 else Pend.word <<< 32) (by sized h1)

/-- The next piece of the command in pieces, by its stage. -/
def piece (buf : ByteArray) (h : ringAt.toNat ≤ buf.size) : ByteArray :=
  let stage : UInt64 := slot buf Slot.pend h >>> 32
  if stage = Pend.lits then pieceLits buf h
  else if stage = Pend.dist then pieceDist buf h
  else if stage = Pend.copy then pieceCopy buf h
  else pieceWord buf h

/-! ### Sizes

Every handler keeps the buffer's size: it only stores into it. -/

@[simp] theorem switchBlock_size (buf : ByteArray) (c : UInt64) (h : ringAt.toNat ≤ buf.size) (hc : c.toNat ≤ 2) :
    (switchBlock buf c h hc).size = buf.size := by
  simp [switchBlock, apply_ite ByteArray.size]

@[simp] theorem endMb_size (buf : ByteArray) (h : ringAt.toNat ≤ buf.size) : (endMb buf h).size = buf.size := by
  simp [endMb, apply_ite ByteArray.size]

@[simp] theorem pieceHead_size (buf : ByteArray) (h : ringAt.toNat ≤ buf.size) :
    (pieceHead buf h).size = buf.size := by
  simp [pieceHead, apply_ite ByteArray.size]

@[simp] theorem pieceFromCopy_size (buf : ByteArray) (h : ringAt.toNat ≤ buf.size) :
    (pieceFromCopy buf h).size = buf.size := by
  simp [pieceFromCopy]

@[simp] theorem pieceDist_size (buf : ByteArray) (h : ringAt.toNat ≤ buf.size) :
    (pieceDist buf h).size = buf.size := by
  simp [pieceDist, apply_ite ByteArray.size]

@[simp] theorem wordOut_size (buf : ByteArray) (opos src n tid outlen room : UInt64) (h : ringAt.toNat ≤ buf.size) :
    (wordOut buf opos src n tid outlen room h).size = buf.size := by
  simp [wordOut, apply_ite ByteArray.size]

@[simp] theorem ringOut_size (buf : ByteArray) (opos d pd clen room re : UInt64) (h : ringAt.toNat ≤ buf.size) :
    (ringOut buf opos d pd clen room re h).size = buf.size := by
  unfold ringOut
  dsimp only
  rw [setSlot_size, setSlot_size]
  split <;> simp [apply_ite ByteArray.size]

@[simp] theorem pieceCopy_size (buf : ByteArray) (h : ringAt.toNat ≤ buf.size) :
    (pieceCopy buf h).size = buf.size := by
  unfold pieceCopy
  dsimp only
  repeat' split
  all_goals simp only [hReject_size, wordOut_size, ringOut_size]

@[simp] theorem pieceWord_size (buf : ByteArray) (h : ringAt.toNat ≤ buf.size) :
    (pieceWord buf h).size = buf.size := by
  simp [pieceWord]

@[simp] theorem pieceLits_size (buf : ByteArray) (h : ringAt.toNat ≤ buf.size) :
    (pieceLits buf h).size = buf.size := by
  simp [pieceLits, apply_ite ByteArray.size]

@[simp] theorem piece_size (buf : ByteArray) (h : ringAt.toNat ≤ buf.size) : (piece buf h).size = buf.size := by
  simp [piece, apply_ite ByteArray.size]
