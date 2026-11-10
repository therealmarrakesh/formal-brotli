module

public import Brotli.FastDecoder.Prim

@[expose] public section

/-!
# The buffer's layout and the slow state's map

Everything the decoder knows is in one `ByteArray`, `buf` (`DESIGN.md` 5.1, 5.2). Its *front* is laid out here, at
fixed positions: the slow state, the distance symbols' table, the staging area for input and the guard. The ring starts
where the front ends, and the current meta-block's tables follow the ring; those positions depend on the stream and are
kept in the slow state.

The slow state is slots of 8 bytes at the offsets named in `Slot`. The map grows as the decoder is written: a slot is
added here by the part that first needs it. The sizes (the slow state's, the staging area's) are provisional until the
whole is measured.
-/

namespace Brotli.FastDecoder

/-! ### The front -/

/-- The slow state's size: 64 slots. -/
def slowSize : UInt64 := 512

/-- Where the distance symbols' table starts: 520 entries of 8 bytes (5.7). -/
def dsymAt : UInt64 := 512

/-- Where the staging area for input starts (5.4). -/
def stageAt : UInt64 := 4672

/-- The staging area's size, the margin of zeros after the last real byte included. -/
def stageSize : UInt64 := 4096

/-- The real input that must lie ahead for a round in running mode: a round's largest input and the 8 bytes a refill
loads (5.6). Also the zeros kept after the last real byte. -/
def margin : UInt64 := 64

/-- The builder's lists (5.7), one word of 4 bytes for each code length 0 to 15: the count of the length's symbols in
the high half, and in the low half the position where the next symbol of that length is to be linked. -/
def listAt : UInt64 := 8768

/-- The first symbol of each length's list: 16 entries of 2 bytes. -/
def headAt : UInt64 := 8832

/-- The links: for each symbol, the next symbol of its length. 704 entries of 2 bytes. -/
def linkAt : UInt64 := 8864

/-- The context table (`ctxTab`), copied here when a stream starts so that the command loop reads it at a constant
place in `buf`: 2048 bytes. -/
def ctxTabAt : UInt64 := 10272

/-- What each insert-and-copy symbol stands for (`cmdInfo`), copied here likewise: 704 entries of 8 bytes. -/
def cmdAt : UInt64 := 12320

/-- Where the guard is: the two bytes before the ring's first (5.5). -/
def guardAt : UInt64 := 17966

/-- Where the ring starts, which is the front's size. -/
def ringAt : UInt64 := 17968

/-! ### The slow state: the slots' offsets -/

namespace Slot

/-- Where the stream stands: one of the phases below. -/
def phase : UInt64 := 0
/-- Why the last loop left. -/
def reason : UInt64 := 8
/-- The memory limit the decoder was started with. -/
def limit : UInt64 := 16

/-- The position in `buf` of the next unread bit. -/
def bitpos : UInt64 := 24
/-- The bit position just after the last real bit staged. -/
def inEnd : UInt64 := 32
/-- The bytes that were already in the staging area when the call began. -/
def carried : UInt64 := 40

/-- The position in `buf` where the next output byte goes. -/
def opos : UInt64 := 48
/-- The position up to which output has been handed to the caller. -/
def handed : UInt64 := 56
/-- The output's bound: the position a command's lengths are compared with. -/
def bound : UInt64 := 64
/-- The position where the ring ends. -/
def ringEnd : UInt64 := 72
/-- The bytes produced so far, for the largest distance a copy may use. -/
def produced : UInt64 := 80
/-- The bytes of the current meta-block still to produce beyond `opos`. -/
def mbLeft : UInt64 := 88

/-- The command loop's counters. -/
def counters : UInt64 := 96
/-- The literals the command in hand has still to read, with the two bytes before them. -/
def lits : UInt64 := 104
/-- The command in hand. -/
def cmd : UInt64 := 112
/-- What an event carries out of the command loop: for a copy that needs care, its distance, and in bit 62 whether
the distance is to be pushed. -/
def evt : UInt64 := 120
/-- The position in `buf` of the current literal block type's part of the context table: 512 bytes for its mode. -/
def ctxOff : UInt64 := 128
/-- The last four distances, a ring of four slots from here, and after them four slots that hold zero (5.6). -/
def dists : UInt64 := 256

/-- The current insert-and-copy table's name. -/
def icTable : UInt64 := 152
/-- The position of the current literal block type's row of table names. -/
def litRow : UInt64 := 160
/-- The position of the current literal block type's table of table positions by context (`ctxWay`). -/
def ctxRow : UInt64 := 136
/-- The position of the current distance block type's row of table names. -/
def distRow : UInt64 := 168

/-- The position where the next table is to be built. -/
def tabNext : UInt64 := 176
/-- The name of the table last built. -/
def name : UInt64 := 184

end Slot

/-! ### The phases (5.1) -/

namespace Phase

def wbits : UInt64 := 0
def mbStart : UInt64 := 1
def metadata : UInt64 := 2
def raw : UInt64 := 3
def header : UInt64 := 4
def commands : UInt64 := 5
def streamEnd : UInt64 := 6
def done : UInt64 := 7
def rejected : UInt64 := 8
def memLimit : UInt64 := 9

end Phase

/-- A slot of the slow state, read. The slot's offset is a constant, so its bound is decided where it is named. -/
@[inline] def slot (buf : ByteArray) (off : UInt64) (h : ringAt.toNat ≤ buf.size)
    (ho : off.toNat + 8 ≤ slowSize.toNat := by decide) : UInt64 :=
  load64 buf off (Nat.le_trans ho (Nat.le_trans (by decide) h))

/-- A slot of the slow state, written. -/
@[inline] def setSlot (buf : ByteArray) (off v : UInt64) (h : ringAt.toNat ≤ buf.size)
    (ho : off.toNat + 8 ≤ slowSize.toNat := by decide) : ByteArray :=
  store64 buf off v (Nat.le_trans ho (Nat.le_trans (by decide) h))

@[simp] theorem setSlot_size (buf : ByteArray) (off v : UInt64) (h : ringAt.toNat ≤ buf.size)
    (ho : off.toNat + 8 ≤ slowSize.toNat) : (setSlot buf off v h ho).size = buf.size :=
  store64_size ..

open Lean in
/-- `sized h` proves a bound on the size of an array made from another by stores, from the same bound `h` on the
other: a store keeps the size. It uses the `@[simp]` theorems that say so, one for each function that stores. -/
macro "sized " h:term : tactic =>
  `(tactic| simpa +zetaDelta using $h)
