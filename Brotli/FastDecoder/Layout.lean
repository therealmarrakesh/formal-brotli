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

/-- The slow state's size: 128 slots. -/
def slowSize : UInt64 := 1024

/-- Where the distance symbols' table starts: 520 entries of 8 bytes (5.7). -/
def dsymAt : UInt64 := 1024

/-- Where the staging area for input starts (5.4). -/
def stageAt : UInt64 := 5184

/-- The staging area's size, the margin of zeros after the last real byte included. -/
def stageSize : UInt64 := 4096

/-- The real input that must lie ahead for a round in running mode: a round's largest input and the 8 bytes a refill
loads (5.6). Also the zeros kept after the last real byte. -/
def margin : UInt64 := 64

/-- The builder's lists (5.7), one word of 4 bytes for each code length 0 to 15: the count of the length's symbols in
the high half, and in the low half the position where the next symbol of that length is to be linked. -/
def listAt : UInt64 := 9280

/-- The first symbol of each length's list: 16 entries of 2 bytes. -/
def headAt : UInt64 := 9344

/-- The links: for each symbol, the next symbol of its length. 704 entries of 2 bytes. -/
def linkAt : UInt64 := 9376

/-- The context table (`ctxTab`), copied here when a stream starts so that the command loop reads it at a constant
place in `buf`: 2048 bytes. -/
def ctxTabAt : UInt64 := 10784

/-- What each insert-and-copy symbol stands for (`cmdInfo`), copied here likewise: 704 entries of 8 bytes. -/
def cmdAt : UInt64 := 12832

/-- The reversed bytes (`rev8`), copied here likewise, for the table builder: 256 bytes. -/
def revAt : UInt64 := 18464

/-- The code-length code's symbols by mask bit (`clSym`), copied here likewise: 64 bytes. -/
def clSymAt : UInt64 := 18720

/-- Where the guard is: the two bytes before the ring's first (5.5). -/
def guardAt : UInt64 := 18798

/-- Where the ring starts, which is the front's size. -/
def ringAt : UInt64 := 18800

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
/-- The builder's place in a list when a run of symbols ends: the next symbol. -/
def walk : UInt64 := 192
/-- The commands left in the current insert-and-copy block, beyond those the loop's budget holds. -/
def icLeft : UInt64 := 200
/-- The position where the current meta-block's output ends. -/
def mbEnd : UInt64 := 208
/-- The bytes of the caller's chunk the last staging took. -/
def took : UInt64 := 216
/-- Whether the meta-block in hand is the stream's last. -/
def last : UInt64 := 224
/-- The window: 16 less than the ring. -/
def win : UInt64 := 232

/-! #### The header's (5.7, 9.1) -/

/-- The header's place: one of `HP`. -/
def hphase : UInt64 := 320
/-- The place the prefix-code sub-machine goes back to. -/
def hret : UInt64 := 328
/-- The alphabet's size of the code being read. -/
def hsize : UInt64 := 336
/-- Whether the code's table is wide, where what its symbols stand for is read from, and its least root. -/
def hwide : UInt64 := 344
def hmeta : UInt64 := 352
def hrmin : UInt64 := 360
/-- What the header's loops save: an index, a count, a sum, the last length that was not zero, and the last repeat
code with its count. -/
def hi : UInt64 := 368
def hn : UInt64 := 376
def hacc : UInt64 := 384
def hprev : UInt64 := 392
def hrep : UInt64 := 400
/-- A simple code's symbols, 16 bits each. -/
def hsyms : UInt64 := 408
/-- The category being read: 0 literals, 1 insert-and-copy, 2 distances. -/
def hcat : UInt64 := 416
/-- The distance parameters, and those the distance symbols' table was last built for (as `dsymKey`). -/
def npostfix : UInt64 := 424
def ndirect : UInt64 := 432
def dsymKey : UInt64 := 440
/-- The positions of the header's working arrays: the context modes (a byte a literal block type), the two maps (a
byte a context), and each kind of code's table names (4 bytes a literal code, its position; 8 the others). -/
def modesAt : UInt64 := 448
def lmapAt : UInt64 := 456
def dmapAt : UInt64 := 464
def litNamesAt : UInt64 := 472
def icNamesAt : UInt64 := 480
def distNamesAt : UInt64 := 488
/-- The counts of literal and of distance codes. -/
def treesL : UInt64 := 496
def treesD : UInt64 := 504
/-- The context map being read: its run-length limit, position, size, count of codes, the place to go back to, and
its code's table. -/
def rlemax : UInt64 := 512
def mapAt : UInt64 := 520
def mapSize : UInt64 := 528
def mapTrees : UInt64 := 536
def mapRet : UInt64 := 544
def mapName : UInt64 := 552
/-- The code-length code's table. -/
def clName : UInt64 := 560
/-- The index of the code being read among its kind. -/
def hcode : UInt64 := 568
/-- The positions of the literal block types' context tables (8192 bytes each) and of the distance block types' rows
of four names; and whether every literal block type's contexts are trivial. -/
def rowsL : UInt64 := 576
def rowsD : UInt64 := 584
def triv : UInt64 := 592
/-- The bits a simple code's symbol is written in. -/
def habits : UInt64 := 600
/-- The three categories, 48 bytes each (`Cat`). -/
def cats : UInt64 := 608

end Slot

/-! ### A category's fields, from `Slot.cats + 48 * c` -/
namespace Cat

/-- The count of block types. -/
def n : UInt64 := 0
/-- The names of the tables of the block-type code and the block-count code. -/
def typeName : UInt64 := 8
def countName : UInt64 := 16
/-- The elements left in the current block. -/
def count : UInt64 := 24
/-- The current block type and the one before. -/
def cur : UInt64 := 32
def prev : UInt64 := 40

end Cat

/-- The code-length code's table: 32 entries of a byte. -/
def clTabAt : UInt64 := 776

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

/-- A place at a constant position in the front is inside a buffer that holds its front. -/
theorem front {buf : ByteArray} (h : ringAt.toNat ≤ buf.size) {p : UInt64} {w : Nat}
    (hp : p.toNat + w ≤ ringAt.toNat := by decide) : p.toNat + w ≤ buf.size :=
  Nat.le_trans hp h

/-- A place in the front at a constant position `a` and an offset `x` of at most `c`. -/
theorem frontAt {buf : ByteArray} (h : ringAt.toNat ≤ buf.size) (a x : UInt64) (c w : Nat) (hx : x.toNat ≤ c)
    (ha : a.toNat + c + w ≤ ringAt.toNat) : (a + x).toNat + w ≤ buf.size := by
  have h1 : (a + x).toNat ≤ a.toNat + x.toNat := by
    rw [UInt64.toNat_add]
    exact Nat.mod_le _ _
  omega

/-- The top 6 bits of a word are at most 63. -/
theorem shr58_le (x : UInt64) : (x >>> 58).toNat ≤ 63 := by
  have h := x.toNat_lt
  rw [UInt64.toNat_shiftRight]
  show x.toNat >>> 58 ≤ 63
  rw [Nat.shiftRight_eq_div_pow]
  omega

/-- The mode of a loop that reads input, as a test (5.4): whether an element that ends at the bit position given
used only real bits. A loop asks it after reading an element and before the element has any effect. -/
@[inline] def realAlways : (buf : ByteArray) → UInt64 → ringAt.toNat ≤ buf.size → Bool :=
  fun _ _ _ => true

/-- Exact mode's test: the element ends at or before the last real bit staged. -/
@[inline] def realExact : (buf : ByteArray) → UInt64 → ringAt.toNat ≤ buf.size → Bool :=
  fun buf bp h => decide (bp ≤ slot buf Slot.inEnd h)

open Lean in
/-- `sized h` proves a bound on the size of an array made from another by stores, from the same bound `h` on the
other: a store keeps the size. It uses the `@[simp]` theorems that say so, one for each function that stores. -/
macro "sized " h:term : tactic =>
  `(tactic| simpa +zetaDelta [apply_ite ByteArray.size, apply_dite ByteArray.size] using $h)

/-- A copy into an array from another leaves it no smaller. -/
theorem copySlice_size_ge (src : ByteArray) (so : Nat) (dest : ByteArray) (d len : Nat) :
    dest.size ≤ (src.copySlice so dest d len).size := by
  simp only [ByteArray.copySlice, ByteArray.size, Array.size_append, Array.size_extract]
  omega
