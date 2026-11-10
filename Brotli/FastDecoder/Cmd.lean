module

public import Brotli.FastDecoder.Table
public import Brotli.FastDecoder.Consts
public import Brotli.FastDecoder.Word

@[expose] public section

/-!
# The command loop

A meta-block's commands (`DESIGN.md` 5.6, 8.1), in running mode: the input ahead is real for as many rounds as the budget
says, so nothing about the input is tested.

**The seven carried values.** `buf`; `opos`; the input's position as a byte, `bb`, and a bit offset from it, `sh`;
and three words:
- `counters`: the literal block's count (bits 0 to 24), the distance block's count (25 to 49), the budget of rounds
  (50 to 61) and the index of the last distance in the ring of four (62 and 63, so that stepping it wraps by itself);
- `lits`: what finding a literal's table carries from one literal to the next (`LitWay`): with contexts, the offset
  of the next literal's table position in the block type's table; without, nothing;
- `cmd`: the command in hand: its copy length (bits 0 to 24), whether its distance is the last one (25), its
  distance's context (26 and 27), and the literals it has still to read (32 to 47). Bit 62 alone says there is no
  command in hand; bit 63 says a copy is being continued, with the length left in bits 0 to 24 and its distance in
  bits 32 to 61.

**The input's position.** An element is read from the 8 bytes at `bb`, shifted by `sh`. After an element of `n` bits,
`bb` moves on by the whole bytes in `sh` and `sh` becomes its bits within a byte and `n`: so `bb` is the byte where
the element before began, and its load never waits for that element's length. `sh` stays under 49, which leaves a
symbol's 15 bits in the word; an element's extra bits are taken from a fresh word where they would not fit.

**A round** is the distance and copy of the command in hand and then the head of the next command; the next command's
literals are rounds of their own, one each.

**Leaving.** The loop runs only what it has admitted whole. For anything else it saves its values in the slow state
with the reason and returns (`leave`): the budget is spent; a command does not fit (its head is left unread); the
distance block's count is zero; a copy needs care (its distance is read, and saved with whether it is to be pushed).

The loop's bounds rest on the decoder's invariant, and its termination on the budget, so both are left to the final
proof (`Owed.lean`).
-/

namespace Brotli.FastDecoder

/-! ### The distance symbols' table -/

/-- An entry of the distance symbols' table: the count of extra bits (bits 0 to 4), the shift of the extra bits (5
and 6), which slot of the last distances to start from (8 and 9, added to the ring's index; with bit 10 a slot that
holds zero), whether the distance is pushed (11), and a base, as 32 bits that wrap (32 to 63). A distance is the
slot's value, the base and the shifted extra bits, summed in 32 bits: one formula for every kind. -/
@[inline] def dsymWord (k z push base nbits shift : UInt64) : UInt64 :=
  (nbits <<< 8) ||| (nbits <<< 16) ||| ((k ||| (z <<< 2) ||| (shift <<< 4) ||| (push <<< 6)) <<< 24) |||
    ((base &&& (0xFFFFFFFF : UInt64)) <<< 32)

/-- The entry of one of the 16 symbols that start from a last distance. -/
def lastWord (s : UInt64) : UInt64 :=
  if s = 0 then dsymWord 0 0 0 0 0 0
  else if s < 4 then dsymWord (4 - s) 0 1 0 0 0
  else
    let t := s - 4
    let k : UInt64 := if t < 6 then 0 else 3
    let m := if t < 6 then t else t - 6
    let mag := (m >>> 1) + 1
    dsymWord k 0 1 (if m &&& 1 = 0 then 0 - mag else mag) 0 0

/-- The entries of symbols `s` to `n`, for the header's `np` (NPOSTFIX) and `nd` (NDIRECT). -/
def dsymFill (np nd : UInt64) (buf : ByteArray) (s n : UInt64) : ByteArray :=
  if hs : s < n then
    let wd :=
      if s < 16 then lastWord s
      else if s < 16 + nd then dsymWord 0 1 1 (s - 15) 0 0
      else
        let d := s - nd - 16
        let nb := 1 + (d >>> (np + 1))
        let off := ((2 + ((d >>> np) &&& 1)) <<< nb) - 4
        dsymWord 0 1 1 ((off <<< np) + (d &&& mask np) + nd + 1) nb np
    have : n.toNat - (s + 1).toNat < n.toNat - s.toNat := succ_nearer hs
    dsymFill np nd (store64 buf (dsymAt + (s <<< 3)) wd owed) (s + 1) n
  else buf
termination_by n.toNat - s.toNat

/-- The distance symbols' table for a header's NPOSTFIX and NDIRECT. -/
def buildDsym (buf : ByteArray) (np nd : UInt64) : ByteArray :=
  dsymFill np nd buf 0 (16 + nd + ((48 : UInt64) <<< np))

/-! ### The words' fields -/

def litMask : UInt64 := 0x1FFFFFF
def distOne : UInt64 := 0x2000000
def distMask : UInt64 := 0x3FFFFFE000000
def budgetOne : UInt64 := 0x4000000000000
def budgetMask : UInt64 := 0x3FFC000000000000
def cmdNone : UInt64 := 0x4000000000000000
def cmdCont : UInt64 := 0x8000000000000000

/-! ### Why the loop left -/

namespace Reason

def budget : UInt64 := 1
def command : UInt64 := 2
def distSwitch : UInt64 := 3
def copy : UInt64 := 4

end Reason

/-- The loop's values saved in the slow state, with the reason for leaving. -/
@[noinline] def leave (buf : ByteArray) (reason bitpos opos counters lits cmd evt : UInt64)
    (h : ringAt.toNat ≤ buf.size) : ByteArray :=
  let b := setSlot buf Slot.reason reason h
  let b := setSlot b Slot.bitpos bitpos (by sized h)
  let b := setSlot b Slot.opos opos (by sized h)
  let b := setSlot b Slot.counters counters (by sized h)
  let b := setSlot b Slot.lits lits (by sized h)
  let b := setSlot b Slot.cmd cmd (by sized h)
  setSlot b Slot.evt evt (by sized h)

/-- How far a command in hand is from done, for the loop's termination: nothing in hand, a copy being continued by
its length left, or a whole command. -/
def cmdRank (cmd : UInt64) : Nat :=
  if cmd >>> 63 ≠ 0 then 1 + (cmd &&& 0x1FFFFFF).toNat else if cmd >>> 62 ≠ 0 then 0 else 0x4000000

/-! ### The loop -/

/-- How the command loop finds a literal's table: three functions, passed to the loop one by one (a structure of
functions is not specialised on), so that the loop is compiled once for each way it is called with.
`v` is what the way carries from one literal to the next, in 32 bits. -/
structure LitWay where
  /-- The position of the table the next literal is read with. -/
  name : (buf : ByteArray) → UInt64 → ringAt.toNat ≤ buf.size → UInt64
  /-- `v` after the literal `b`. -/
  next : (buf : ByteArray) → UInt64 → UInt64 → ringAt.toNat ≤ buf.size → UInt64
  /-- `v` at the start of a run of literals at `opos`. -/
  init : (buf : ByteArray) → UInt64 → ringAt.toNat ≤ buf.size → UInt64

/-- The command loop. -/
@[specialize] def run (litName : (buf : ByteArray) → UInt64 → ringAt.toNat ≤ buf.size → UInt64)
    (litNext : (buf : ByteArray) → UInt64 → UInt64 → ringAt.toNat ≤ buf.size → UInt64)
    (litInit : (buf : ByteArray) → UInt64 → ringAt.toNat ≤ buf.size → UInt64)
    (buf : ByteArray) (bb sh opos counters lits cmd : UInt64) (h : ringAt.toNat ≤ buf.size) : ByteArray :=
  -- the head of the next command
  let head := fun (buf : ByteArray) (bb sh opos counters : UInt64) (h : ringAt.toNat ≤ buf.size) =>
    if counters &&& budgetMask = 0 then leave buf Reason.budget ((bb <<< 3) + sh) opos counters 0 cmdNone 0 h
    else
      let w : UInt64 := load64 buf bb owed
      let e : UInt64 := lookupW buf (slot buf Slot.icTable h) (w >>> sh)
      let total : UInt64 := (e >>> 8) &&& 0xFF
      let s1 : UInt64 := sh + (e &&& 15)
      let x : UInt64 := if sh + total ≤ 64 then w >>> s1 else load64 buf (bb + (s1 >>> 3)) owed >>> (s1 &&& 7)
      let ie : UInt64 := (e >>> 16) &&& 0xFF
      let ilen : UInt64 := ((e >>> 32) &&& (0xFFFF : UInt64)) + (x &&& mask ie)
      let clen : UInt64 := (e >>> 48) + ((x >>> ie) &&& mask ((e >>> 24) &&& 0xFF))
      if opos + ilen + clen ≤ slot buf Slot.bound h ∧ ilen ≤ (counters &&& litMask) ∧ ilen ≤ 16 then
        run litName litNext litInit buf (bb + (sh >>> 3)) ((sh &&& 7) + total) opos (counters - budgetOne - ilen)
          (litInit buf opos h) (clen ||| (((e >>> 4) &&& 7) <<< 25) ||| (ilen <<< 32)) h
      else leave buf Reason.command ((bb <<< 3) + sh) opos counters 0 cmdNone 0 h
  -- a copy of `rem` bytes at a distance of 16 or more, by blocks of 16: two in a round
  let copy := fun (buf : ByteArray) (bb sh opos counters rem dist : UInt64) (h : ringAt.toNat ≤ buf.size) =>
    let src := opos - dist
    let buf1 := copy16 buf opos src owed
    if rem ≤ 16 then head buf1 bb sh (opos + rem) counters (by sized h)
    else
      let buf2 := copy16 buf1 (opos + 16) (src + 16) owed
      if rem ≤ 32 then head buf2 bb sh (opos + rem) counters (by sized h)
      else run litName litNext litInit buf2 bb sh (opos + 32) counters 0 (cmdCont ||| (rem - (32 : UInt64)) ||| (dist <<< 32))
        (by sized h)
  -- what a distance means: a copy from the ring, a dictionary word, or something for a handler
  let emit := fun (buf : ByteArray) (bb sh opos counters dist push clen : UInt64) (h : ringAt.toNat ≤ buf.size) =>
    if dist + ringAt ≤ opos ∧ 8 ≤ dist then
      -- within the bytes produced: the distance becomes the last one, and the copy is made
      let counters' := counters + (push <<< 62)
      let buf' := store64 buf (Slot.dists + ((counters' >>> 62) <<< 3)) dist owed
      if 16 ≤ dist then copy buf' bb sh opos counters' clen dist (by sized h)
      else
        -- a distance of 8 to 15: two blocks of 8, after which the bytes repeat at twice the distance, 16 or more
        let src := opos - dist
        let buf1 := copy8 buf' opos src owed
        if clen ≤ 8 then head buf1 bb sh (opos + clen) counters' (by sized h)
        else
          let buf2 := copy8 buf1 (opos + 8) (src + 8) owed
          if clen ≤ 16 then head buf2 bb sh (opos + clen) counters' (by sized h)
          else run litName litNext litInit buf2 bb sh (opos + 16) counters' 0
            (cmdCont ||| (clen - (16 : UInt64)) ||| (dist <<< 33)) (by sized h)
    else if opos < dist + ringAt ∧ dist < 0x80000000 ∧ clen - 4 ≤ 20 then
      -- beyond the bytes produced: a word of the dictionary, of the copy's length, under a transform
      let li := load64 lenTab (clen <<< 3) owed
      let nd : UInt64 := li &&& 31
      let wid : UInt64 := dist + ringAt - opos - 1
      let tid : UInt64 := wid >>> nd
      if tid < 121 then
        let t : UInt64 := load64 transTab (tid <<< 5) owed
        let first : UInt64 := (t >>> 8) &&& 0xFF
        let om : UInt64 := first + ((t >>> 16) &&& 0xFF)
        let n : UInt64 := if om < clen then clen - om else 0
        let outlen : UInt64 := ((t >>> 24) &&& (0xFF : UInt64)) + n + ((t >>> 32) &&& (0xFF : UInt64))
        if opos + outlen ≤ slot buf Slot.bound h then
          head (wordPut buf opos ((li >>> 8) + (wid &&& mask nd) * clen + first) n tid) bb sh (opos + outlen)
            counters (by sized h)
        else leave buf Reason.copy ((bb <<< 3) + sh) opos counters 0 clen (dist ||| (push <<< 62)) h
      else leave buf Reason.copy ((bb <<< 3) + sh) opos counters 0 clen (dist ||| (push <<< 62)) h
    else leave buf Reason.copy ((bb <<< 3) + sh) opos counters 0 clen (dist ||| (push <<< 62)) h
  if cmd - (0x100000000 : UInt64) < (0x3FFFFFFF00000000 : UInt64) then
    -- a literal, read from the word at the byte where the element before it began: its address does not wait for
    -- that element's length
    let v : UInt64 := lits
    let e := lookup8 buf (litName buf v h) (load64 buf bb owed >>> sh)
    let b : UInt64 := e >>> 4
    let v' : UInt64 := litNext buf v b h
    run litName litNext litInit (store8 buf opos b owed) (bb + (sh >>> 3)) ((sh &&& 7) + (e &&& 15)) (opos + 1) counters
      v' (cmd - (0x100000000 : UInt64)) (by sized h)
  else if cmd >>> 62 ≠ 0 then
    if cmd >>> 63 ≠ 0 then copy buf bb sh opos counters (cmd &&& 0x1FFFFFF) ((cmd >>> 32) &&& 0x3FFFFFFF) h
    else head buf bb sh opos counters h
  else if (cmd >>> 25) &&& 1 ≠ 0 then
    -- the last distance again
    emit buf bb sh opos counters (load64 buf (Slot.dists + ((counters >>> 62) <<< 3)) owed) 0 (cmd &&& 0x1FFFFFF) h
  else if counters &&& distMask = 0 then
    leave buf Reason.distSwitch ((bb <<< 3) + sh) opos counters 0 cmd 0 h
  else
    -- a distance read from the input
    let w : UInt64 := load64 buf bb owed
    let e : UInt64 := lookupW buf (load64 buf (slot buf Slot.distRow h + (((cmd >>> 26) &&& 3) <<< 3)) owed) (w >>> sh)
    let total : UInt64 := (e >>> 8) &&& 0xFF
    let s1 : UInt64 := sh + (e &&& 15)
    let x : UInt64 := if sh + total ≤ 64 then w >>> s1 else load64 buf (bb + (s1 >>> 3)) owed >>> (s1 &&& 7)
    let f : UInt64 := (e >>> 24) &&& 0xFF
    let j : UInt64 := (((counters >>> 62) + f) &&& 3) ||| (f &&& 4)
    let extra : UInt64 := (x &&& mask ((e >>> 16) &&& 0xFF)) <<< ((f >>> 4) &&& 3)
    let dist : UInt64 := (load64 buf (Slot.dists + (j <<< 3)) owed + (e >>> 32) + extra) &&& 0xFFFFFFFF
    emit buf (bb + (sh >>> 3)) ((sh &&& 7) + total) opos (counters - distOne) dist ((f >>> 6) &&& 1)
      (cmd &&& 0x1FFFFFF) h
termination_by ((counters &&& budgetMask).toNat, cmdRank cmd, ((cmd >>> 32) &&& 0xFFFF).toNat)
decreasing_by all_goals exact owed

/-- A literal's table by its context. Each literal block type has a table of 2048 table positions, 4 bytes each, at
the class of the byte before the last times 1024 and the last byte times 4 (a class is what a byte contributes to the
context as the byte before the last, under the block type's mode). `v` is that offset, so the next literal's table
is one load from the literal just read, with one shift and one or between them; the class comes from a byte read a
literal earlier. -/
@[inline] def ctxWay : LitWay where
  name := fun buf v h => load32 buf (slot buf Slot.ctxRow h + v) owed
  next := fun buf v b h => (b <<< 2) ||| (load8 buf (slot buf Slot.ctxOff h + ((v >>> 2) &&& 0xFF)) owed <<< 10)
  init := fun buf opos h =>
    (load8 buf (opos - 1) owed <<< 2) ||| (load8 buf (slot buf Slot.ctxOff h + load8 buf (opos - 2) owed) owed <<< 10)

/-- A literal's table where the context does not matter: the one table, and nothing carried. -/
@[inline] def trivWay : LitWay where
  name := fun buf _ h => slot buf Slot.litRow h
  next := fun _ _ _ _ => 0
  init := fun _ _ _ => 0

/-- The command loop entered from the slow state, for a meta-block whose literals have contexts. -/
def runCtx (buf : ByteArray) (h : ringAt.toNat ≤ buf.size) : ByteArray :=
  let bp := slot buf Slot.bitpos h
  run ctxWay.name ctxWay.next ctxWay.init buf (bp >>> 3) (bp &&& 7) (slot buf Slot.opos h) (slot buf Slot.counters h) (slot buf Slot.lits h)
    (slot buf Slot.cmd h) h

/-- The command loop entered from the slow state, for a meta-block whose literal contexts are all trivial. -/
def runTriv (buf : ByteArray) (h : ringAt.toNat ≤ buf.size) : ByteArray :=
  let bp := slot buf Slot.bitpos h
  run trivWay.name trivWay.next trivWay.init buf (bp >>> 3) (bp &&& 7) (slot buf Slot.opos h) (slot buf Slot.counters h) (slot buf Slot.lits h)
    (slot buf Slot.cmd h) h
