module

public import Brotli.FastDecoder.Layout
public import Brotli.FastDecoder.Bits
public import Brotli.FastDecoder.Num
public import Brotli.FastDecoder.Owed

@[expose] public section

/-!
# A prefix code's table, and its builder

**The table** (`DESIGN.md` 5.7). Entries of 16 bits: a code length in the low 4 bits and a symbol above. A table has a
*root* of `2 ^ r` entries, where `r` is the code's longest length up to `rootCap`, indexed by the next `r` bits of
input. A root entry whose low 4 bits are at most `r` is a symbol with its length. One whose low 4 bits are more than
`r` points to a *sub-table*: the excess is the sub-table's width in bits and the 12 bits above are its place, in
entries from the table's start; it is indexed by the bits after the root's, and its entries hold a symbol with its
code's whole length. So a lookup ends at an entry whose low 4 bits are the bits to consume, whichever level it is in.
A code of one symbol has `r = 0` and one entry, of length zero. A table is *named* by one value, its position in `buf`
times 16 and its `r`.

**The lists.** While a code's lengths are read, each symbol is added to the end of the list of its length
(`listAdd`): the lists are threaded through one array of links indexed by symbol, and since symbols arrive in
increasing order each list is in symbol order.

**The builder** (`build`) walks the lists once, shortest length first: the order of the walk is the order of the
codes, so a code is a counter stepped once a symbol. The counter is kept in 8 bits with its first bit highest, which a
table of reversed bytes turns into the first slot to write, and each symbol is written to all its slots by one strided
fill. Symbols with codes longer than the root come last, already in order, and fill sub-tables each made exactly as
wide as its codes need.

The walk's bounds (a link is a symbol of the alphabet, a slot is inside the table's room) rest on what the lists hold
and on the code being complete, so they are left to the final proof (`Owed.lean`).
-/

namespace Brotli.FastDecoder

/-- The widest root. The reversal below is of 8 bits, so a wider root needs a wider reversal. -/
def rootCap : UInt64 := 8

/-- Each byte with its bits in reverse order. -/
def rev8 : ByteArray :=
  ⟨Array.ofFn (n := 256) fun i =>
    let b := i.val.toUInt8
    let b := (b >>> 4) ||| (b <<< 4)
    let b := ((b &&& 0xCC) >>> 2) ||| ((b &&& 0x33) <<< 2)
    ((b &&& 0xAA) >>> 1) ||| ((b &&& 0x55) <<< 1)⟩

theorem rev8_size : rev8.size = 256 :=
  Array.size_ofFn

/-- The low 8 bits of `k` in reverse order. -/
@[inline] def rev (k : UInt64) : UInt64 :=
  load8 rev8 (k &&& 255) (by
    rw [rev8_size, UInt64.toNat_and]
    exact Nat.succ_le_succ Nat.and_le_right)

/-! ### Lookup -/

/-- The entry for the code at the bottom of `w` in the table `name`: its low 4 bits are the code's length and the
bits above are the symbol. `w` holds at least 15 bits of input. -/
@[inline] def lookup (buf : ByteArray) (name w : UInt64) : UInt64 :=
  let pos := name >>> 4
  let r := name &&& 15
  let e := load16 buf (pos + ((w &&& mask r) <<< 1)) owed
  if (e &&& 15) ≤ r then e
  else load16 buf (pos + (((e >>> 4) + ((w >>> r) &&& mask ((e &&& 15) - r))) <<< 1)) owed

/-! ### The lists -/

/-- The words of lengths `2 * k` and `2 * k + 1` made empty. -/
@[inline] def resetPair (buf : ByteArray) (k : UInt64) (h : ringAt.toNat ≤ buf.size)
    (hk : (listAt + (8 : UInt64) * k).toNat + 8 ≤ ringAt.toNat := by decide) : ByteArray :=
  store64 buf (listAt + (8 : UInt64) * k) ((headAt + (4 : UInt64) * k) ||| ((headAt + (4 : UInt64) * k + 2) <<< 32))
    (Nat.le_trans hk h)

@[simp] theorem resetPair_size (buf : ByteArray) (k : UInt64) (h : ringAt.toNat ≤ buf.size)
    (hk : (listAt + (8 : UInt64) * k).toNat + 8 ≤ ringAt.toNat) : (resetPair buf k h hk).size = buf.size :=
  store64_size ..

/-- The 16 lists made empty: each count zero, and each list's next symbol to be linked at its head. -/
def listsReset (buf : ByteArray) (h : ringAt.toNat ≤ buf.size) : ByteArray :=
  let buf := resetPair buf 0 h
  let buf := resetPair buf 1 (by sized h)
  let buf := resetPair buf 2 (by sized h)
  let buf := resetPair buf 3 (by sized h)
  let buf := resetPair buf 4 (by sized h)
  let buf := resetPair buf 5 (by sized h)
  let buf := resetPair buf 6 (by sized h)
  resetPair buf 7 (by sized h)

/-- Symbol `s` added to the end of the list of length `len`: linked after the list's last symbol, and made the last.
One load and two stores. -/
@[inline] def listAdd (buf : ByteArray) (len s : UInt64) : ByteArray :=
  let wd := load32 buf (listAt + (len <<< 2)) owed
  let buf := store16 buf (wd &&& (0xFFFF : UInt64)) s owed
  store32 buf (listAt + (len <<< 2))
    (((wd &&& (0xFFFF0000 : UInt64)) + (0x10000 : UInt64)) ||| (linkAt + (s <<< 1))) owed

/-- The count of symbols of length `len`. -/
@[inline] def listCount (buf : ByteArray) (len : UInt64) : UInt64 :=
  load32 buf (listAt + (len <<< 2)) owed >>> 16

/-- The first symbol of length `len`. -/
@[inline] def listHead (buf : ByteArray) (len : UInt64) : UInt64 :=
  load16 buf (headAt + (len <<< 1)) owed

/-- The symbol after `s` in its list. -/
@[inline] def listNext (buf : ByteArray) (s : UInt64) : UInt64 :=
  load16 buf (linkAt + (s <<< 1)) owed

/-! ### The builder -/

/-- The longest length that has a symbol, looking down from `len`. -/
def maxLen (buf : ByteArray) (len : UInt64) : UInt64 :=
  if h1 : len ≤ 1 then len
  else if listCount buf len ≠ 0 then len
  else
    have : (len - 1).toNat < len.toNat := pred_lt (by intro e; subst e; exact h1 (by decide))
    maxLen buf (len - 1)
termination_by len.toNat

/-- The width of a sub-table that starts with a code of length `len`, of which `n` symbols remain: wide enough for
the codes that fall under one root slot and no wider. `left` is the room at the present length. -/
def subWidth (buf : ByteArray) (r len n left : UInt64) : UInt64 :=
  if hl : len < 15 then
    if left ≤ n then len - r
    else
      have : 15 - (len + 1).toNat < 15 - len.toNat := succ_nearer hl
      subWidth buf r (len + 1) (listCount buf (len + 1)) ((left - n) <<< 1)
  else len - r
termination_by 15 - len.toNat

/-- The builder's results put in the slow state: the table's name, and where the next table goes. `nxt` is the
table's size in entries. -/
@[inline] def built (buf : ByteArray) (pos r nxt : UInt64) (h : ringAt.toNat ≤ buf.size) : ByteArray :=
  let buf1 := setSlot buf Slot.name ((pos <<< 4) ||| r) h
  setSlot buf1 Slot.tabNext (pos + (nxt <<< 1)) (by sized h)

@[simp] theorem built_size (buf : ByteArray) (pos r nxt : UInt64) (h : ringAt.toNat ≤ buf.size) :
    (built buf pos r nxt h).size = buf.size := by
  simp [built]

/-- The walk through the lists of lengths beyond the root. `key` is the root slot the next sub-table hangs from,
as a code; `subkey` is the code within the current sub-table, its first bit highest of 8, and `0x100` when the
sub-table is full; `cur` and `tb` are the current sub-table's place and width, `nxt` the next free entry. -/
def subWalk (pos maxl r : UInt64) (buf : ByteArray) (len n s key subkey cur tb nxt : UInt64)
    (h : ringAt.toNat ≤ buf.size) : ByteArray :=
  if hn : n ≠ 0 then
    if hk : subkey = 0x100 then
      let tb' := subWidth buf r len n ((1 : UInt64) <<< (len - r))
      let buf' := store16 buf (pos + (rev key <<< 1)) ((nxt <<< 4) ||| (r + tb')) owed
      subWalk pos maxl r buf' len n s (key + ((0x80 : UInt64) >>> (r - 1))) 0 nxt tb' (nxt + ((1 : UInt64) <<< tb'))
        (by sized h)
    else
      let next := listNext buf s
      let buf' := fill16 buf (pos + ((cur + rev subkey) <<< 1)) ((2 : UInt64) <<< (len - r))
        ((1 : UInt64) <<< (tb - (len - r))) ((s <<< 4) ||| len) owed
      have : (n - 1).toNat < n.toNat := pred_lt hn
      subWalk pos maxl r buf' len (n - 1) next key (subkey + ((0x80 : UInt64) >>> (len - r - 1))) cur tb nxt
        (by sized h)
  else if hl : len < maxl then
    have : maxl.toNat - (len + 1).toNat < maxl.toNat - len.toNat := succ_nearer hl
    subWalk pos maxl r buf (len + 1) (listCount buf (len + 1)) (listHead buf (len + 1)) key subkey cur tb nxt h
  else
    built buf pos r nxt h
termination_by (maxl.toNat - len.toNat, n.toNat, if subkey = 0x100 then 1 else 0)

/-- The walk through the lists of lengths within the root. `key` is the next code, its first bit highest of 8. -/
def rootWalk (pos maxl r : UInt64) (buf : ByteArray) (len n s key : UInt64) (h : ringAt.toNat ≤ buf.size) :
    ByteArray :=
  if hn : n ≠ 0 then
    let next := listNext buf s
    let buf' := fill16 buf (pos + (rev key <<< 1)) ((2 : UInt64) <<< len) ((1 : UInt64) <<< (r - len))
      ((s <<< 4) ||| len) owed
    have : (n - 1).toNat < n.toNat := pred_lt hn
    rootWalk pos maxl r buf' len (n - 1) next (key + ((0x80 : UInt64) >>> (len - 1))) (by sized h)
  else if hl : len < r then
    have : r.toNat - (len + 1).toNat < r.toNat - len.toNat := succ_nearer hl
    rootWalk pos maxl r buf (len + 1) (listCount buf (len + 1)) (listHead buf (len + 1)) key h
  else if r < maxl then
    subWalk pos maxl r buf len 0 0 key 0x100 0 0 ((1 : UInt64) <<< r) h
  else
    built buf pos r ((1 : UInt64) <<< r) h
termination_by (r.toNat - len.toNat, n.toNat)

/-- The table of the code whose symbols are in the lists, a complete code of two symbols or more, built at the
position in `Slot.tabNext`. Its name is left in `Slot.name`, and `Slot.tabNext` is moved past it. -/
def build (buf : ByteArray) (h : ringAt.toNat ≤ buf.size) : ByteArray :=
  let pos := slot buf Slot.tabNext h
  let maxl := maxLen buf 15
  let r := if maxl ≤ rootCap then maxl else rootCap
  rootWalk pos maxl r buf 0 0 0 0 h

/-- The table of a code of the one symbol `s`: one entry, read from no bits. -/
def buildOne (buf : ByteArray) (s : UInt64) (h : ringAt.toNat ≤ buf.size) : ByteArray :=
  let pos := slot buf Slot.tabNext h
  let buf1 := store16 buf pos (s <<< 4) owed
  built buf1 pos 0 1 (by sized h)
