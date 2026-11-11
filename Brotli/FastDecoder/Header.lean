module

public import Brotli.FastDecoder.Cmd

@[expose] public section

/-!
# A meta-block's header

The header of a compressed meta-block (`DESIGN.md` 5.7, 9.1) as a machine that can stop between any two elements, in
running mode: the caller makes sure the margin of real input lies ahead before each call.

**One element a call.** The header's place is a number in the slow state (`Slot.hphase`, one of `HP`). `headerStep`
reads it and does one thing: reads one element, stores what it learnt in the slow state, sets the next place, and
returns `buf`. Two long stretches are loops of their own that run on a budget of rounds worked out from the real input
ahead, and leave with their few values saved when it is spent: a code's symbol lengths (`lensLoop`, a round at most 8
bits) and a context map's values (`valsLoop`, a round at most 31 bits). The 18 lengths of the code-length code are a
third loop (`clLoop`, 72 bits at most, inside the margin), which in running mode never leaves.

**Reading a prefix code is a sub-machine** (`pcEnter`), entered with the alphabet's size, the kind of table to build
and the place to go back to; it leaves the table's name in `Slot.name`. Reading a context map is another (`mapEnter`),
which uses the first.

**Where a header's things go.** Everything is taken from `Slot.tabNext` as its size becomes known, tables and working
arrays alike: the context modes, the two maps, each kind of code's list of table names, and at the end the rows the
command loop reads. The inverse move-to-front's list and the set of codes a map names are scratch just past
`Slot.tabNext`, overwritten by what is built next.

**Never the old buffer.** A function here names its buffer `buf` at every step, so that no value is read from a buffer
after a store has been made into it: that would share the array, and the store would copy it.

The bounds rest on the decoder's invariant and are left to the final proof (`Owed.lean`), with the sizes after the
loops and the builder until this part's design is final.
-/

namespace Brotli.FastDecoder

/-! ### The header's places -/

namespace HP

def catN : UInt64 := 0
def catType : UInt64 := 1
def catCount : UInt64 := 2
def catFirst : UInt64 := 3
def params : UInt64 := 4
def modes : UInt64 := 5
def treesL : UInt64 := 6
def treesD : UInt64 := 7
def litInit : UInt64 := 8
def litRet : UInt64 := 9
def icRet : UInt64 := 10
def distRet : UInt64 := 11
def finish : UInt64 := 12
def pcStart : UInt64 := 13
def pcSym : UInt64 := 14
def pcSel : UInt64 := 15
def pcLens : UInt64 := 16
def mapRle : UInt64 := 17
def mapCodeRet : UInt64 := 18
def mapVals : UInt64 := 19
def mapImtf : UInt64 := 20
def pcCl : UInt64 := 21

end HP

/-! ### Small parts -/

/-- The bits from `bp` on, the next unread bit lowest: at least 57. -/
@[inline] def bitsAt (buf : ByteArray) (bp : UInt64) : UInt64 :=
  refill buf bp owed

/-- The input's position and the header's place, stored. -/
@[inline] def hGoto (buf : ByteArray) (place bp : UInt64) (h : ringAt.toNat ≤ buf.size) : ByteArray :=
  setSlot (setSlot buf Slot.bitpos bp h) Slot.hphase place (by sized h)

@[simp] theorem hGoto_size (buf : ByteArray) (place bp : UInt64) (h : ringAt.toNat ≤ buf.size) :
    (hGoto buf place bp h).size = buf.size := by
  simp [hGoto]

/-- The stream is rejected. -/
def hReject (buf : ByteArray) (h : ringAt.toNat ≤ buf.size) : ByteArray :=
  setSlot buf Slot.phase Phase.rejected h

@[simp] theorem hReject_size (buf : ByteArray) (h : ringAt.toNat ≤ buf.size) : (hReject buf h).size = buf.size := by
  simp [hReject]

/-- A count of 1 to 256 in its variable-length code, from the bits `w`: the count in the low half and the bits it
took (1 to 11) in the high half. -/
@[inline] def varLen (w : UInt64) : UInt64 :=
  if w &&& 1 = 0 then (1 : UInt64) ||| ((1 : UInt64) <<< 32)
  else
    let n : UInt64 := (w >>> 1) &&& 7
    if n = 0 then (2 : UInt64) ||| ((4 : UInt64) <<< 32)
    else
      let x : UInt64 := (w >>> 4) &&& mask n
      (((1 : UInt64) <<< n) + (1 : UInt64) + x) ||| ((n + (4 : UInt64)) <<< 32)

/-- The least `b` with `size ≤ 2 ^ b`, looking up from `b`: the bits a simple code's symbol is written in. -/
def alphaBits (size b : UInt64) : UInt64 :=
  if hb : b < 16 then
    if size ≤ (1 : UInt64) <<< b then b
    else
      have : 16 - (b + 1).toNat < 16 - b.toNat := succ_nearer hb
      alphaBits size (b + 1)
  else b
termination_by 16 - b.toNat

@[inline] def lo (a b : UInt64) : UInt64 := if a ≤ b then a else b

@[inline] def hi (a b : UInt64) : UInt64 := if a ≤ b then b else a

/-- Where category `c`'s fields are. -/
@[inline] def catAt (c : UInt64) : UInt64 :=
  Slot.cats + c * 48

/-- A field of a category's record lies in the front: the category `c` (0 to 2), the field at `f`. -/
theorem catSlot {buf : ByteArray} (h : ringAt.toNat ≤ buf.size) {c : UInt64} (hc : c.toNat ≤ 2) (f : UInt64)
    (hf : f.toNat ≤ 40 := by decide) : (catAt c + f).toNat + 8 ≤ buf.size := by
  have h1 : (catAt c).toNat ≤ 704 := by
    unfold catAt
    rw [UInt64.toNat_add, UInt64.toNat_mul]
    have a : Slot.cats.toNat = 608 := rfl
    have b : (48 : UInt64).toNat = 48 := rfl
    rw [a, b]
    rw [Nat.mod_eq_of_lt (show c.toNat * 48 < 2 ^ 64 by omega), Nat.mod_eq_of_lt (by omega)]
    omega
  exact frontAt h (catAt c) f 40 8 hf (by have : ringAt.toNat = 18800 := rfl; omega)

/-! ### The prefix-code sub-machine -/

/-- The sub-machine entered: a code over `size` symbols, its table of the kind `wide`, `mt`, `rmin` (as `build`
takes them), and the place to go back to. -/
def pcEnter (buf : ByteArray) (size wide mt rmin ret : UInt64) (h : ringAt.toNat ≤ buf.size) : ByteArray :=
  let buf := setSlot buf Slot.hsize size h
  let buf := setSlot buf Slot.hwide wide (by sized h)
  let buf := setSlot buf Slot.hmeta mt (by sized h)
  let buf := setSlot buf Slot.hrmin rmin (by sized h)
  let buf := setSlot buf Slot.hret ret (by sized h)
  setSlot buf Slot.hphase HP.pcStart (by sized h)

@[simp] theorem pcEnter_size (buf : ByteArray) (size wide mt rmin ret : UInt64) (h : ringAt.toNat ≤ buf.size) :
    (pcEnter buf size wide mt rmin ret h).size = buf.size := by
  simp [pcEnter]

/-- The code's table built from the lists, and the sub-machine left. -/
def pcBuild (buf : ByteArray) (h : ringAt.toNat ≤ buf.size) : ByteArray :=
  let buf := build buf (slot buf Slot.hwide h) (slot buf Slot.hmeta h) (slot buf Slot.hrmin h) h
  have h : ringAt.toNat ≤ buf.size := by sized h
  setSlot buf Slot.hphase (slot buf Slot.hret h) h

/-- A simple code of `n` symbols `syms` (16 bits each, in the order read) built: its symbols are put in the lists by
length and, within a length, in order. -/
def simpleBuild (buf : ByteArray) (n syms sel : UInt64) (h : ringAt.toNat ≤ buf.size) : ByteArray :=
  let s0 : UInt64 := syms &&& 0xFFFF
  let s1 : UInt64 := (syms >>> 16) &&& 0xFFFF
  let s2 : UInt64 := (syms >>> 32) &&& 0xFFFF
  let s3 : UInt64 := syms >>> 48
  if n = 1 then
    let buf := buildOne buf s0 (slot buf Slot.hwide h) (slot buf Slot.hmeta h) (slot buf Slot.hrmin h) h
    have h : ringAt.toNat ≤ buf.size := by sized h
    setSlot buf Slot.hphase (slot buf Slot.hret h) h
  else
    let buf := listsReset buf h
    let buf :=
      if n = 2 then listAdd (listAdd buf 1 (lo s0 s1)) 1 (hi s0 s1)
      else if n = 3 then listAdd (listAdd (listAdd buf 1 s0) 2 (lo s1 s2)) 2 (hi s1 s2)
      else if sel = 0 then
        let a := lo s0 s1
        let b := hi s0 s1
        let c := lo s2 s3
        let d := hi s2 s3
        let m1 := hi a c
        let m2 := lo b d
        listAdd (listAdd (listAdd (listAdd buf 2 (lo a c)) 2 (lo m1 m2)) 2 (hi m1 m2)) 2 (hi b d)
      else listAdd (listAdd (listAdd (listAdd buf 1 s0) 2 s1) 3 (lo s2 s3)) 3 (hi s2 s3)
    pcBuild buf (by sized h)

/-- Which of the 18 symbols have the length `l`, from `lens`, their lengths 3 bits each: a bit for each, at the top
of its 3. One comparison of the whole word. -/
@[inline] def lenMask (lens l : UInt64) : UInt64 :=
  let x : UInt64 := lens ^^^ (l * (0o111111111111111111 : UInt64))
  (~~~(((x &&& (0o333333333333333333 : UInt64)) + (0o333333333333333333 : UInt64)) ||| x)) &&&
    (0o444444444444444444 : UInt64)

/-- The symbol, times 8, of the lowest bit of a mask as `lenMask` gives, from `m` and `m` with that bit cleared. -/
@[inline] def maskSym (buf : ByteArray) (m m' : UInt64) (h : ringAt.toNat ≤ buf.size) : UInt64 :=
  load8 buf (clSymAt + (((m ^^^ m') * (0x03F79D71B4CB0A89 : UInt64)) >>> 58))
    (frontAt h clSymAt _ 63 1 (shr58_le _) (by decide))

/-- One symbol of length `len` stored in the code-length code's table: the lowest symbol of the mask `m` (`m'` is
`m` without it), at the entry its code `key` alone names. -/
@[inline] def clPut (buf : ByteArray) (m m' key len : UInt64) (h : ringAt.toNat ≤ buf.size) : ByteArray :=
  store8 buf (clTabAt + revB buf key) (maskSym buf m m' h ||| len) owed

@[simp] theorem clPut_size (buf : ByteArray) (m m' key len : UInt64) (h : ringAt.toNat ≤ buf.size) :
    (clPut buf m m' key len h).size = buf.size := by
  simp [clPut]

/-- The table's first `n` entries copied onto the next `n`, for `n` of 1 to 8: one load and one store of 8 bytes,
which for `n` under 8 runs past them into entries a later copy rewrites. -/
@[inline] def clDouble (buf : ByteArray) (n : UInt64) (h : ringAt.toNat ≤ buf.size)
    (hn : (clTabAt + n).toNat + 8 ≤ ringAt.toNat := by decide) : ByteArray :=
  store64 buf (clTabAt + n) (load64 buf clTabAt (front h)) (Nat.le_trans hn h)

@[simp] theorem clDouble_size (buf : ByteArray) (n : UInt64) (h : ringAt.toNat ≤ buf.size)
    (hn : (clTabAt + n).toNat + 8 ≤ ringAt.toNat) : (clDouble buf n h hn).size = buf.size := by
  simp [clDouble]

/-! The code-length code's table: 32 entries of one byte at `clTabAt`, the symbol in the high 5 bits and its length
in the low 3, indexed by the next 5 bits of input. It is made a length at a time, 1 to 5, from `lens`, the 18
lengths, 3 bits each, by five small loops, one for each length, so that everything a length fixes is a constant in
its loop.

Codes go by length and then by symbol, so one counter runs through them all: `key`, the next code with its first bit
highest of 8, stepped by `0x100 >> length` a symbol. The symbols of a length are a mask (`lenMask`), walked from its
lowest bit, so a symbol with no length costs nothing. Each symbol is stored once, at the entry its code alone names
(the code's bits and zeros above them).

Before a length's symbols are stored the table's first `2 ^ (length - 1)` entries are copied onto the next as many:
every shorter symbol's entries repeat at that distance, so its copies are made there, and the entries still unclaimed
are copied as they are and claimed later (the code is complete, so every entry is). Nothing is emptied first and
nothing is tested. -/

/-- The symbols of length 5. -/
def clW5 (buf : ByteArray) (m key : UInt64) (h : ringAt.toNat ≤ buf.size) : ByteArray :=
  if hm : m ≠ 0 then clW5 (clPut buf m (m &&& (m - 1)) key 5 h) (m &&& (m - 1)) (key + 0x08) (by sized h)
  else buf
termination_by m.toNat
decreasing_by exact and_pred_lt hm

@[simp] theorem clW5_size (buf : ByteArray) (m key : UInt64) (h : ringAt.toNat ≤ buf.size) :
    (clW5 buf m key h).size = buf.size := by
  fun_induction clW5 buf m key h <;> simp_all +zetaDelta

/-- The symbols of length 4; then the 16 entries doubled, and length 5. -/
def clW4 (buf : ByteArray) (m key lens : UInt64) (h : ringAt.toNat ≤ buf.size) : ByteArray :=
  if hm : m ≠ 0 then clW4 (clPut buf m (m &&& (m - 1)) key 4 h) (m &&& (m - 1)) (key + 0x10) lens (by sized h)
  else
    clW5 (copy16 buf (clTabAt + 16) clTabAt ⟨front h, front h, Or.inl (by decide)⟩) (lenMask lens 5) key (by sized h)
termination_by m.toNat
decreasing_by exact and_pred_lt hm

@[simp] theorem clW4_size (buf : ByteArray) (m key lens : UInt64) (h : ringAt.toNat ≤ buf.size) :
    (clW4 buf m key lens h).size = buf.size := by
  fun_induction clW4 buf m key lens h <;> simp_all +zetaDelta

/-- The symbols of length 3; then the 8 entries doubled, and length 4. -/
def clW3 (buf : ByteArray) (m key lens : UInt64) (h : ringAt.toNat ≤ buf.size) : ByteArray :=
  if hm : m ≠ 0 then clW3 (clPut buf m (m &&& (m - 1)) key 3 h) (m &&& (m - 1)) (key + 0x20) lens (by sized h)
  else clW4 (clDouble buf 8 h) (lenMask lens 4) key lens (by sized h)
termination_by m.toNat
decreasing_by exact and_pred_lt hm

@[simp] theorem clW3_size (buf : ByteArray) (m key lens : UInt64) (h : ringAt.toNat ≤ buf.size) :
    (clW3 buf m key lens h).size = buf.size := by
  fun_induction clW3 buf m key lens h <;> simp_all +zetaDelta

/-- The symbols of length 2; then the 4 entries doubled, and length 3. -/
def clW2 (buf : ByteArray) (m key lens : UInt64) (h : ringAt.toNat ≤ buf.size) : ByteArray :=
  if hm : m ≠ 0 then clW2 (clPut buf m (m &&& (m - 1)) key 2 h) (m &&& (m - 1)) (key + 0x40) lens (by sized h)
  else clW3 (clDouble buf 4 h) (lenMask lens 3) key lens (by sized h)
termination_by m.toNat
decreasing_by exact and_pred_lt hm

@[simp] theorem clW2_size (buf : ByteArray) (m key lens : UInt64) (h : ringAt.toNat ≤ buf.size) :
    (clW2 buf m key lens h).size = buf.size := by
  fun_induction clW2 buf m key lens h <;> simp_all +zetaDelta

/-- The symbols of length 1; then the 2 entries doubled, and length 2. -/
def clW1 (buf : ByteArray) (m key lens : UInt64) (h : ringAt.toNat ≤ buf.size) : ByteArray :=
  if hm : m ≠ 0 then clW1 (clPut buf m (m &&& (m - 1)) key 1 h) (m &&& (m - 1)) (key + 0x80) lens (by sized h)
  else clW2 (clDouble buf 2 h) (lenMask lens 2) key lens (by sized h)
termination_by m.toNat
decreasing_by exact and_pred_lt hm

@[simp] theorem clW1_size (buf : ByteArray) (m key lens : UInt64) (h : ringAt.toNat ≤ buf.size) :
    (clW1 buf m key lens h).size = buf.size := by
  fun_induction clW1 buf m key lens h <;> simp_all +zetaDelta

/-- The table of a code-length code of one symbol, the one that has a length: every entry that symbol, read from no
bits. -/
def clOne (buf : ByteArray) (lens : UInt64) (h : ringAt.toNat ≤ buf.size) : ByteArray :=
  let m : UInt64 := (((lens &&& (0o333333333333333333 : UInt64)) + (0o333333333333333333 : UInt64)) ||| lens) &&&
    (0o444444444444444444 : UInt64)
  let v : UInt64 := maskSym buf m (m &&& (m - 1)) h * (0x0101010101010101 : UInt64)
  let buf1 := store64 buf clTabAt v (front h)
  let buf2 := store64 buf1 (clTabAt + 8) v (front (by sized h))
  let buf3 := store64 buf2 (clTabAt + 16) v (front (by sized h))
  store64 buf3 (clTabAt + 24) v (front (by sized h))

@[simp] theorem clOne_size (buf : ByteArray) (lens : UInt64) (h : ringAt.toNat ≤ buf.size) :
    (clOne buf lens h).size = buf.size := by
  simp [clOne]

/-- The code-length code is read: `nz` of its lengths are not zero, and `lens` holds the 18 lengths, 3 bits each. Its
table is made, and the lists and the loop's values are made ready for the symbols' lengths. -/
def clDone (buf : ByteArray) (bp nz lens : UInt64) (h : ringAt.toNat ≤ buf.size) : ByteArray :=
  let buf := if nz = 1 then clOne buf lens h else clW1 buf (lenMask lens 1) 0 lens h
  have h : ringAt.toNat ≤ buf.size := by sized h
  let buf := listsReset buf h
  let buf := setSlot buf Slot.hi 0 (by sized h)
  let buf := setSlot buf Slot.hacc 32768 (by sized h)
  let buf := setSlot buf Slot.hprev 8 (by sized h)
  let buf := setSlot buf Slot.hrep 0 (by sized h)
  hGoto buf HP.pcLens bp (by sized h)

/-- The code-length loop left for want of input (exact mode): its values saved, to be taken up at `HP.pcCl`. -/
def clSave (buf : ByteArray) (bp i sum nz lens : UInt64) (h : ringAt.toNat ≤ buf.size) : ByteArray :=
  let buf := setSlot buf Slot.hi i h
  let buf := setSlot buf Slot.hacc sum (by sized h)
  let buf := setSlot buf Slot.hn nz (by sized h)
  let buf := setSlot buf Slot.hsyms lens (by sized h)
  let buf := setSlot buf Slot.reason Reason.input (by sized h)
  hGoto buf HP.pcCl bp (by sized h)

/-- The code-length code's lengths, from the `i`th in the order they come: each is one of six codes of 2 to 4 bits,
read off the next 4 bits of the word in hand, `w`, which is loaded again once `bp` has passed `lim` (as in
`lensLoop`). Nothing is stored: the lengths are gathered in `lens`, 3 bits a symbol; `sum` is the sum of
`32 >> length` so far and `nz` the count of lengths not zero. The code is complete when the sum is 32; with all 18
read it must be of one symbol. `real` is the mode (5.4): asked of each length before it takes effect, and where it
says no the loop leaves with its values as they were. -/
@[specialize] def clLoop (real : (buf : ByteArray) → UInt64 → ringAt.toNat ≤ buf.size → Bool)
    (buf : ByteArray) (bp w lim i sum nz lens : UInt64) (h : ringAt.toNat ≤ buf.size) : ByteArray :=
  if hi : i < 18 then
    if lim < bp then clLoop real buf bp (bitsAt buf bp) (bp + 49) i sum nz lens h
    else
      let v : UInt64 := w &&& 15
      let len : UInt64 := ((0x5340234013402340 : UInt64) >>> (v <<< 2)) &&& 15
      let nb : UInt64 := ((0x4222322242223222 : UInt64) >>> (v <<< 2)) &&& 15
      if !(real buf (bp + nb) h) then clSave buf bp i sum nz lens h
      else if len = 0 then clLoop real buf (bp + nb) (w >>> nb) lim (i + 1) sum nz lens h
      else
        let sym := load8 clOrder i (Nat.succ_le_of_lt (UInt64.lt_iff_toNat_lt.mp hi))
        let lens' : UInt64 := lens ||| (len <<< (sym + (sym <<< 1)))
        let sum' : UInt64 := sum + ((32 : UInt64) >>> len)
        if sum' = 32 then clDone buf (bp + nb) (nz + 1) lens' h
        else if 32 < sum' then hReject buf h
        else clLoop real buf (bp + nb) (w >>> nb) lim (i + 1) sum' (nz + 1) lens' h
  else if nz = 1 then clDone buf bp 1 lens h
  else hReject buf h
termination_by (18 - i.toNat, if lim < bp then 1 else 0)
decreasing_by all_goals exact owed

/-- The code-length loop in the mode the input ahead allows: running while its 18 lengths' 72 bits are certainly
real, exact otherwise. -/
def clGo (buf : ByteArray) (bp w lim i sum nz lens : UInt64) (h : ringAt.toNat ≤ buf.size) : ByteArray :=
  if bp + 72 ≤ slot buf Slot.inEnd h then clLoop realAlways buf bp w lim i sum nz lens h
  else clLoop realExact buf bp w lim i sum nz lens h

/-- The first element of a prefix code: 2 bits that say whether it is simple, and for a simple code 2 more, the
count of its symbols less one. A code given by lengths goes straight on to the code-length code's lengths. -/
@[noinline] def stepPcStart (buf : ByteArray) (h : ringAt.toNat ≤ buf.size) : ByteArray :=
  let bp := slot buf Slot.bitpos h
  let w := bitsAt buf bp
  let hskip : UInt64 := w &&& 3
  if hskip = 1 then
    let bits := alphaBits (slot buf Slot.hsize h) 0
    let buf := setSlot buf Slot.hn (((w >>> 2) &&& 3) + 1) h
    let buf := setSlot buf Slot.hi 0 (by sized h)
    let buf := setSlot buf Slot.hsyms 0 (by sized h)
    let buf := setSlot buf Slot.habits bits (by sized h)
    hGoto buf HP.pcSym (bp + 4) (by sized h)
  else
    clGo buf (bp + 2) (w >>> 2) (bp + 49) hskip 0 0 0 h

/-- The code-length code's lengths taken up again where the loop left them. -/
@[noinline] def stepPcCl (buf : ByteArray) (h : ringAt.toNat ≤ buf.size) : ByteArray :=
  clGo buf (slot buf Slot.bitpos h) 0 0 (slot buf Slot.hi h) (slot buf Slot.hacc h) (slot buf Slot.hn h)
    (slot buf Slot.hsyms h) h

/-- One symbol of a simple code: inside the alphabet, and not one already given. -/
@[noinline] def stepPcSym (buf : ByteArray) (h : ringAt.toNat ≤ buf.size) : ByteArray :=
  let bp := slot buf Slot.bitpos h
  let nb := slot buf Slot.habits h
  let v : UInt64 := bitsAt buf bp &&& mask nb
  let i := slot buf Slot.hi h
  let syms := slot buf Slot.hsyms h
  let n := slot buf Slot.hn h
  if slot buf Slot.hsize h ≤ v ∨ (0 < i ∧ v = syms &&& 0xFFFF) ∨ (1 < i ∧ v = (syms >>> 16) &&& 0xFFFF) ∨
      (2 < i ∧ v = (syms >>> 32) &&& 0xFFFF) then hReject buf h
  else
    let syms' : UInt64 := syms ||| (v <<< (i <<< 4))
    let buf := setSlot buf Slot.hsyms syms' h
    let buf := setSlot buf Slot.hi (i + 1) (by sized h)
    if i + 1 < n then hGoto buf HP.pcSym (bp + nb) (by sized h)
    else if n = 4 then hGoto buf HP.pcSel (bp + nb) (by sized h)
    else simpleBuild (setSlot buf Slot.bitpos (bp + nb) (by sized h)) n syms' 0 (by sized h)

/-- The bit that chooses between the two shapes of a simple code of four symbols. -/
@[noinline] def stepPcSel (buf : ByteArray) (h : ringAt.toNat ≤ buf.size) : ByteArray :=
  let bp := slot buf Slot.bitpos h
  let sel : UInt64 := bitsAt buf bp &&& 1
  let syms := slot buf Slot.hsyms h
  simpleBuild (setSlot buf Slot.bitpos (bp + 1) h) 4 syms sel (by sized h)

/-- `m` symbols from `s` on each linked to the one after it: four links by one store while four remain (their
values are consecutive, so the four are one word), then one at a time. -/
def linkRun (buf : ByteArray) (s m : UInt64) : ByteArray :=
  if h4 : 4 ≤ m then
    have : (m - 4).toNat < m.toNat := sub_lt_of_ne (by decide) h4
    linkRun (store64 buf (linkAt + (s <<< 1))
      ((0x0004000300020001 : UInt64) + s * (0x0001000100010001 : UInt64)) owed) (s + 4) (m - 4)
  else if hm : m ≠ 0 then
    have : (m - 1).toNat < m.toNat := pred_lt hm
    linkRun (store16 buf (linkAt + (s <<< 1)) (s + 1) owed) (s + 1) (m - 1)
  else buf
termination_by m.toNat

@[simp] theorem linkRun_size (buf : ByteArray) (s m : UInt64) : (linkRun buf s m).size = buf.size := by
  fun_induction linkRun buf s m <;> simp_all +zetaDelta

/-- `n` symbols from `s` on added to the list of length `len`, for `n` not zero: the first linked after the list's
last symbol, each of the others after the one before it, and the list's word written once, its count up by `n` and
its last symbol the run's last. Runs are short (a repeat code gives 3 to 6 at first), so the first four links are
one store made in line for a run of up to five: links past the run's end belong to symbols not yet reached, which
write their own when they come. A longer run, or one within three symbols of the largest alphabet's end (where
the store would pass the links), goes to `linkRun`. -/
@[inline] def listRun (buf : ByteArray) (len s n : UInt64) : ByteArray :=
  let wd := load32 buf (listAt + (len <<< 2)) owed
  let buf := store16 buf (wd &&& (0xFFFF : UInt64)) s owed
  let wide := n ≤ 5 ∧ s < 700
  let buf :=
    if wide then
      store64 buf (linkAt + (s <<< 1)) ((0x0004000300020001 : UInt64) + s * (0x0001000100010001 : UInt64)) owed
    else linkRun buf s (n - 1)
  store32 buf (listAt + (len <<< 2))
    (((wd &&& (0xFFFF0000 : UInt64)) + (n <<< 16)) ||| (linkAt + ((s + n - 1) <<< 1))) owed

@[simp] theorem listRun_size (buf : ByteArray) (len s n : UInt64) :
    (listRun buf len s n).size = buf.size := by
  unfold listRun
  simp only [store32_size]
  split <;> simp

/-- The lengths' loop left with its budget spent: its values saved. -/
def lensSave (buf : ByteArray) (bp i sum prev rep : UInt64) (h : ringAt.toNat ≤ buf.size) : ByteArray :=
  let buf := setSlot buf Slot.bitpos bp h
  let buf := setSlot buf Slot.hi i (by sized h)
  let buf := setSlot buf Slot.hacc sum (by sized h)
  let buf := setSlot buf Slot.hprev prev (by sized h)
  setSlot buf Slot.hrep rep (by sized h)

/-- The lengths' loop left with the code complete. -/
def lensDone (buf : ByteArray) (bp : UInt64) (h : ringAt.toNat ≤ buf.size) : ByteArray :=
  pcBuild (setSlot buf Slot.bitpos bp h) (by sized h)

/-- The rounds the lengths' loop may run before it must look again: no more than the real input ahead covers, and no
more than the symbols the alphabet has left, since a round takes at least one. -/
@[inline] def lensBudget (rounds size i : UInt64) : UInt64 :=
  if size - i < rounds then size - i else rounds

/-- The symbols' lengths, one code-length symbol a round, at most 8 bits. The symbol is looked up in the code-length
code's table, 32 entries at a constant place. The input is a word in hand, `w`, the bits from `bp` on, shifted down
as they are used, so that a round does not wait for a load whose address the round before decides; it is loaded
again once `bp` has passed `lim`, 49 bits on from the last load, which leaves a round's 8 bits in it until then.

`i` is the next symbol; `space` what the code still has room for (in units of `32768 >> length`, from 32768 down);
`pr` the last length that was not zero (bits 0 to 3), with the last repeat code's count (bits 8 to 39) and which code
it was (bits 40 on), zero unless the round before was a repeat. The budget is not counted down: the loop runs until
`i` reaches `iEnd`, which a plain length does not move, and which is never past the alphabet's end; so an alphabet
used up with space left ends the loop there, and is rejected where the loop is entered again.

A length of 1 to 15 adds the symbol to that length's list; code 16 repeats the last length and code 17 repeats zero,
a repeat that follows one of its own kind extending it. The code is complete when no space is left; a length the
space cannot hold and a repeat past the alphabet are rejected.

`real` is the mode (5.4): asked of each symbol, with its extra bits, before it takes effect. In running mode the end
`iEnd` already keeps the loop inside the real input and the test is not there; in exact mode a symbol that is not all
there leaves the loop with its values as they were and the reason "input". -/
@[specialize] def lensLoop (real : (buf : ByteArray) → UInt64 → ringAt.toNat ≤ buf.size → Bool)
    (buf : ByteArray) (bp w lim i iEnd space pr : UInt64) (h : ringAt.toNat ≤ buf.size) : ByteArray :=
  if i = iEnd then lensSave buf bp i space pr 0 h
  else if lim < bp then lensLoop real buf bp (bitsAt buf bp) (bp + 49) i iEnd space pr h
  else
    let e := load8 buf (clTabAt + (w &&& 31)) owed
    let sym : UInt64 := e >>> 3
    let nb : UInt64 := e &&& 7
    let used : UInt64 := if sym < 16 then nb else if sym = 16 then nb + 2 else nb + 3
    if !(real buf (bp + used) h) then
      setSlot (lensSave buf bp i space pr 0 h) Slot.reason Reason.input (by simp [lensSave]; exact h)
    else if sym = 0 then lensLoop real buf (bp + nb) (w >>> nb) lim (i + 1) iEnd space (pr &&& 15) h
    else if sym < 16 then
      let dec : UInt64 := (32768 : UInt64) >>> sym
      if dec < space then
        lensLoop real (listAdd buf sym i) (bp + nb) (w >>> nb) lim (i + 1) iEnd (space - dec) sym (by sized h)
      else if dec = space then lensDone (listAdd buf sym i) (bp + nb) (by sized h)
      else hReject buf h
    else
      let size := slot buf Slot.hsize h
      let prev : UInt64 := pr &&& 15
      let x : UInt64 := w >>> nb
      let old : UInt64 := if pr >>> 40 = sym then (pr >>> 8) &&& 0xFFFFFFFF else 0
      if sym = 16 then
        let new : UInt64 := if old = 0 then 3 + (x &&& 3) else 4 * (old - 2) + 3 + (x &&& 3)
        let run : UInt64 := new - old
        let dec : UInt64 := run * ((32768 : UInt64) >>> prev)
        if size < i + run ∨ space < dec then hReject buf h
        else if dec = space then lensDone (listRun buf prev i run) (bp + nb + 2) (by sized h)
        else
          lensLoop real (listRun buf prev i run) (bp + nb + 2) (x >>> 2) lim (i + run)
            (i + run + lensBudget (iEnd - i - 1) size (i + run)) (space - dec)
            (prev ||| (new <<< 8) ||| ((16 : UInt64) <<< 40)) (by sized h)
      else
        let new : UInt64 := if old = 0 then 3 + (x &&& 7) else 8 * (old - 2) + 3 + (x &&& 7)
        let j : UInt64 := i + (new - old)
        if size < j then hReject buf h
        else
          lensLoop real buf (bp + nb + 3) (x >>> 3) lim j (j + lensBudget (iEnd - i - 1) size j) space
            (prev ||| (new <<< 8) ||| ((17 : UInt64) <<< 40)) h
termination_by (iEnd.toNat - i.toNat, if lim < bp then 1 else 0)
decreasing_by all_goals exact owed

/-- The symbols' lengths, as far as the real input ahead allows. While the input covers at least one round at a
round's largest cost the loop runs in running mode for as many rounds as it covers; the last bits of a chunk, which
may still hold whole symbols, are read in exact mode, a symbol at a time. -/
@[noinline] def stepPcLens (buf : ByteArray) (h : ringAt.toNat ≤ buf.size) : ByteArray :=
  let bp := slot buf Slot.bitpos h
  let i := slot buf Slot.hi h
  let size := slot buf Slot.hsize h
  if size ≤ i then hReject buf h
  else
    let rounds : UInt64 := (slot buf Slot.inEnd h - bp) >>> 3
    if rounds = 0 then
      lensLoop realExact buf bp 0 0 i size (slot buf Slot.hacc h) (slot buf Slot.hprev h) h
    else
      lensLoop realAlways buf bp 0 0 i (i + lensBudget rounds size i) (slot buf Slot.hacc h) (slot buf Slot.hprev h) h

/-! ### A context map -/

/-- The map sub-machine entered: `size` values at `mp`, naming `nt` codes, and the place to go back to. -/
def mapEnter (buf : ByteArray) (mp size nt ret : UInt64) (h : ringAt.toNat ≤ buf.size) : ByteArray :=
  let buf := setSlot buf Slot.mapAt mp h
  let buf := setSlot buf Slot.mapSize size (by sized h)
  let buf := setSlot buf Slot.mapTrees nt (by sized h)
  let buf := setSlot buf Slot.mapRet ret (by sized h)
  setSlot buf Slot.hphase HP.mapRle (by sized h)

/-- The run-length limit, 0 to 16, in 1 or 5 bits; then the map's own code. -/
@[noinline] def stepMapRle (buf : ByteArray) (h : ringAt.toNat ≤ buf.size) : ByteArray :=
  let bp := slot buf Slot.bitpos h
  let w := bitsAt buf bp
  let r : UInt64 := if w &&& 1 = 0 then 0 else ((w >>> 1) &&& 15) + 1
  let nb : UInt64 := if w &&& 1 = 0 then 1 else 5
  let nt := slot buf Slot.mapTrees h
  let buf := setSlot buf Slot.rlemax r h
  let buf := setSlot buf Slot.bitpos (bp + nb) (by sized h)
  pcEnter buf (nt + r) 0 0 0 HP.mapCodeRet (by sized h)

/-- The map's code is built: on to its values. -/
@[noinline] def stepMapCodeRet (buf : ByteArray) (h : ringAt.toNat ≤ buf.size) : ByteArray :=
  let buf := setSlot buf Slot.mapName (slot buf Slot.name h) h
  let buf := setSlot buf Slot.hi 0 (by sized h)
  setSlot buf Slot.hphase HP.mapVals (by sized h)

/-- `n` zero bytes from `p`. -/
def zeroRun (buf : ByteArray) (p n : UInt64) : ByteArray :=
  if hn : n = 0 then buf
  else
    have : (n - 1).toNat < n.toNat := pred_lt hn
    zeroRun (store8 buf p 0 owed) (p + 1) (n - 1)
termination_by n.toNat

@[simp] theorem zeroRun_size (buf : ByteArray) (p n : UInt64) :
    (zeroRun buf p n).size = buf.size := by
  fun_induction zeroRun buf p n <;> simp_all +zetaDelta

/-- The map's loop left: at the map's end, on to the move-to-front bit; otherwise its place saved. -/
def valsSave (buf : ByteArray) (bp p : UInt64) (h : ringAt.toNat ≤ buf.size) : ByteArray :=
  let mp := slot buf Slot.mapAt h
  if mp + slot buf Slot.mapSize h ≤ p then hGoto buf HP.mapImtf bp h
  else setSlot (setSlot buf Slot.bitpos bp h) Slot.hi (p - mp) (by sized h)

@[simp] theorem valsSave_size (buf : ByteArray) (bp p : UInt64) (h : ringAt.toNat ≤ buf.size) :
    (valsSave buf bp p h).size = buf.size := by
  simp [valsSave, apply_ite ByteArray.size]

/-- A map's values, a symbol a round, at most 31 bits: zero, a run of zeros (symbols 1 to the run-length limit, with
as many extra bits as the symbol), or a value (the symbol less the limit). A run past the map's end is rejected. The
input is a word in hand as in `lensLoop`, loaded again once `bp` has passed `lim`, 26 bits on from the last load,
which leaves a round's 31 bits in it until then.

The loop is shaped to keep what changes in registers across its store (section 4): besides `buf` and the code's
table `name` it carries five values. `p` is where the next value goes, a position in `buf`, not an index into the
map; the budget is not counted down but is an end for `p`, `pEnd`, which a value does not move and which is never
past the map's end; and what only a run of zeros or the loop's end needs (the run-length limit apart, the map's
place and size) is read from the slow state there.

`real` is the mode (5.4), asked of each symbol with its extra bits before it takes effect, as in `lensLoop`. -/
@[specialize] def valsLoop (real : (buf : ByteArray) → UInt64 → ringAt.toNat ≤ buf.size → Bool)
    (name : UInt64) (buf : ByteArray) (bp w lim p pEnd : UInt64) (h : ringAt.toNat ≤ buf.size) : ByteArray :=
  if p = pEnd then valsSave buf bp p h
  else if lim < bp then valsLoop real name buf bp (bitsAt buf bp) (bp + 26) p pEnd h
  else
    let e := lookup buf name w
    let sym : UInt64 := e >>> 4
    let nb : UInt64 := e &&& 15
    let rle := slot buf Slot.rlemax h
    if sym = 0 ∨ rle < sym then
      if !(real buf (bp + nb) h) then setSlot (valsSave buf bp p h) Slot.reason Reason.input (by sized h)
      else
        valsLoop real name (store8 buf p (if sym = 0 then 0 else sym - rle) owed) (bp + nb) (w >>> nb) lim (p + 1)
          pEnd (by sized h)
    else if !(real buf (bp + nb + sym) h) then setSlot (valsSave buf bp p h) Slot.reason Reason.input (by sized h)
    else
      let pMax : UInt64 := slot buf Slot.mapAt h + slot buf Slot.mapSize h
      let run : UInt64 := ((1 : UInt64) <<< sym) + ((w >>> nb) &&& mask sym)
      if pMax - p < run then hReject buf h
      else
        let p' : UInt64 := p + run
        let left : UInt64 := pEnd - p - 1
        valsLoop real name (zeroRun buf p run) (bp + nb + sym) (w >>> (nb + sym)) lim p'
          (p' + (if pMax - p' < left then pMax - p' else left)) (by sized h)
termination_by (pEnd.toNat - p.toNat, if lim < bp then 1 else 0)
decreasing_by all_goals exact owed

/-- The map's values, as far as the real input ahead allows: in running mode for as many rounds as the input covers
at a round's largest cost (and no more than the values the map has left, since a round gives at least one); in exact
mode, a symbol at a time, for the last bits of a chunk. -/
@[noinline] def stepMapVals (buf : ByteArray) (h : ringAt.toNat ≤ buf.size) : ByteArray :=
  let bp := slot buf Slot.bitpos h
  let mp := slot buf Slot.mapAt h
  let i := slot buf Slot.hi h
  let left := slot buf Slot.mapSize h - i
  let rounds : UInt64 := (slot buf Slot.inEnd h - bp) >>> 5
  if rounds = 0 ∧ left ≠ 0 then valsLoop realExact (slot buf Slot.mapName h) buf bp 0 0 (mp + i) (mp + i + left) h
  else
    valsLoop realAlways (slot buf Slot.mapName h) buf bp 0 0 (mp + i) (mp + i + (if left < rounds then left else rounds))
      h

/-- The bytes at `m` set to 0, 1, 2 and so on, 8 at a time from the `k`th 8 to the `n`th. -/
def identFill (buf : ByteArray) (m k n : UInt64) : ByteArray :=
  if hk : k < n then
    have : n.toNat - (k + 1).toNat < n.toNat - k.toNat := succ_nearer hk
    identFill (store64 buf (m + (k <<< 3)) ((0x0706050403020100 : UInt64) + k * (0x0808080808080808 : UInt64)) owed) m
      (k + 1) n
  else buf
termination_by n.toNat - k.toNat

@[simp] theorem identFill_size (buf : ByteArray) (m k n : UInt64) :
    (identFill buf m k n).size = buf.size := by
  fun_induction identFill buf m k n <;> simp_all +zetaDelta

/-- The inverse move-to-front transform of the map's values from the `j`th, in place, with the list at `m`: each
value is replaced by the list's entry at that place, which moves to the list's front. -/
def imtfLoop (buf : ByteArray) (mp m j size : UInt64) : ByteArray :=
  if hj : j < size then
    have : size.toNat - (j + 1).toNat < size.toNat - j.toNat := succ_nearer hj
    let idx := load8 buf (mp + j) owed
    let v := load8 buf (m + idx) owed
    let buf := store8 buf (mp + j) v owed
    let buf := if idx = 0 then buf else store8 (move buf (m + 1) m idx owed) m v owed
    imtfLoop buf mp m (j + 1) size
  else buf
termination_by size.toNat - j.toNat

@[simp] theorem imtfLoop_size (buf : ByteArray) (mp m j size : UInt64) :
    (imtfLoop buf mp m j size).size = buf.size := by
  fun_induction imtfLoop buf mp m j size <;> simp_all +zetaDelta <;> split <;> simp

/-- The codes the map's values from the `j`th name, as a set of bits, for a map of at most 64 codes. -/
def seenBits (buf : ByteArray) (mp j size acc : UInt64) : UInt64 :=
  if hj : j < size then
    have : size.toNat - (j + 1).toNat < size.toNat - j.toNat := succ_nearer hj
    seenBits buf mp (j + 1) size (acc ||| ((1 : UInt64) <<< load8 buf (mp + j) owed))
  else acc
termination_by size.toNat - j.toNat

/-- Each value of the map from the `j`th marked in the bytes at `s`. -/
def markLoop (buf : ByteArray) (mp s j size : UInt64) : ByteArray :=
  if hj : j < size then
    have : size.toNat - (j + 1).toNat < size.toNat - j.toNat := succ_nearer hj
    markLoop (store8 buf (s + load8 buf (mp + j) owed) 1 owed) mp s (j + 1) size
  else buf
termination_by size.toNat - j.toNat

@[simp] theorem markLoop_size (buf : ByteArray) (mp s j size : UInt64) :
    (markLoop buf mp s j size).size = buf.size := by
  fun_induction markLoop buf mp s j size <;> simp_all +zetaDelta

/-- Whether every code from `k` to `n` is marked at `s`. -/
def allSeen (buf : ByteArray) (s k n : UInt64) : Bool :=
  if hk : k < n then
    have : n.toNat - (k + 1).toNat < n.toNat - k.toNat := succ_nearer hk
    if load8 buf (s + k) owed = 0 then false else allSeen buf s (k + 1) n
  else true
termination_by n.toNat - k.toNat

/-- The bit that says whether the map's values are move-to-front coded, and the transform if so; then the check that
the map names every one of its codes: by a set of bits in a register for a map of at most 64 codes, by marks
otherwise. The list and the marks are scratch past `Slot.tabNext`, set up only as far as the map's codes go. -/
@[noinline] def stepMapImtf (buf : ByteArray) (h : ringAt.toNat ≤ buf.size) : ByteArray :=
  let bp := slot buf Slot.bitpos h
  let coded : UInt64 := bitsAt buf bp &&& 1
  let mp := slot buf Slot.mapAt h
  let size := slot buf Slot.mapSize h
  let nt := slot buf Slot.mapTrees h
  let sc := slot buf Slot.tabNext h
  let ret := slot buf Slot.mapRet h
  let words : UInt64 := (nt + 7) >>> 3
  let buf := setSlot buf Slot.bitpos (bp + 1) h
  let buf := if coded = 0 then buf else imtfLoop (identFill buf sc 0 words) mp sc 0 size
  have h : ringAt.toNat ≤ buf.size := by sized h
  if nt ≤ 64 then
    if seenBits buf mp 0 size 0 = (if nt = 64 then (0xFFFFFFFFFFFFFFFF : UInt64) else ((1 : UInt64) <<< nt) - 1)
    then setSlot buf Slot.hphase ret h else hReject buf h
  else
    let buf := markLoop (fill64 buf (sc + 256) 8 words 0 owed) mp (sc + 256) 0 size
    have h : ringAt.toNat ≤ buf.size := by sized h
    if allSeen buf (sc + 256) 0 nt then setSlot buf Slot.hphase ret h else hReject buf h

/-! ### The header's own places -/

/-- After category `c`: the next category, or the distance parameters. -/
def catNext (buf : ByteArray) (c : UInt64) (h : ringAt.toNat ≤ buf.size) : ByteArray :=
  if c = 2 then setSlot buf Slot.hphase HP.params h
  else setSlot (setSlot buf Slot.hcat (c + 1) h) Slot.hphase HP.catN (by sized h)

/-- A category's count of block types. With one type there is nothing more to read, and its block's count is one no
meta-block can exhaust. -/
@[noinline] def stepCatN (buf : ByteArray) (h : ringAt.toNat ≤ buf.size) : ByteArray :=
  let bp := slot buf Slot.bitpos h
  let v := varLen (bitsAt buf bp)
  let n : UInt64 := v &&& 0xFFFFFFFF
  let c := slot buf Slot.hcat h
  let ca := catAt c
  let buf := setSlot buf Slot.bitpos (bp + (v >>> 32)) h
  let buf := store64 buf (ca + Cat.n) n owed
  let buf := store64 buf (ca + Cat.cur) 0 owed
  let buf := store64 buf (ca + Cat.prev) 1 owed
  if n < 2 then catNext (store64 buf (ca + Cat.count) 16777216 owed) c (by sized h)
  else pcEnter buf (n + 2) 0 0 0 HP.catType (by sized h)

/-- The block-type code is built: on to the block-count code. -/
@[noinline] def stepCatType (buf : ByteArray) (h : ringAt.toNat ≤ buf.size) : ByteArray :=
  let name := slot buf Slot.name h
  let ca := catAt (slot buf Slot.hcat h)
  pcEnter (store64 buf (ca + Cat.typeName) name owed) 26 0 0 0 HP.catCount (by sized h)

/-- The block-count code is built: on to the first block's count. -/
@[noinline] def stepCatCount (buf : ByteArray) (h : ringAt.toNat ≤ buf.size) : ByteArray :=
  let name := slot buf Slot.name h
  let ca := catAt (slot buf Slot.hcat h)
  setSlot (store64 buf (ca + Cat.countName) name owed) Slot.hphase HP.catFirst (by sized h)

/-- A category's first block count: a symbol and its extra bits, at most 39 bits. -/
@[noinline] def stepCatFirst (buf : ByteArray) (h : ringAt.toNat ≤ buf.size) : ByteArray :=
  let bp := slot buf Slot.bitpos h
  let c := slot buf Slot.hcat h
  let ca := catAt c
  let w := bitsAt buf bp
  let e := lookup buf (load64 buf (ca + Cat.countName) owed) w
  let info := load32 countTab ((e >>> 4) <<< 2) owed
  let nb : UInt64 := info >>> 24
  let n : UInt64 := e &&& 15
  let count : UInt64 := (info &&& (0xFFFF : UInt64)) + ((w >>> n) &&& mask nb)
  let buf := store64 buf (ca + Cat.count) count owed
  catNext (setSlot buf Slot.bitpos (bp + n + nb) (by sized h)) c (by sized h)

/-- The distance parameters, 6 bits; and room for the context modes. -/
@[noinline] def stepParams (buf : ByteArray) (h : ringAt.toNat ≤ buf.size) : ByteArray :=
  let bp := slot buf Slot.bitpos h
  let w := bitsAt buf bp
  let np : UInt64 := w &&& 3
  let nd : UInt64 := ((w >>> 2) &&& 15) <<< np
  let nl := slot buf Slot.cats h
  let tn := slot buf Slot.tabNext h
  let buf := setSlot buf Slot.npostfix np h
  let buf := setSlot buf Slot.ndirect nd (by sized h)
  let buf := setSlot buf Slot.modesAt tn (by sized h)
  let buf := setSlot buf Slot.tabNext (tn + ((nl + 7) &&& ~~~(7 : UInt64))) (by sized h)
  let buf := setSlot buf Slot.hi 0 (by sized h)
  hGoto buf HP.modes (bp + 6) (by sized h)

/-- One literal block type's context mode, 2 bits. -/
@[noinline] def stepModes (buf : ByteArray) (h : ringAt.toNat ≤ buf.size) : ByteArray :=
  let bp := slot buf Slot.bitpos h
  let mode : UInt64 := bitsAt buf bp &&& 3
  let i := slot buf Slot.hi h
  let nl := slot buf Slot.cats h
  let buf := store8 buf (slot buf Slot.modesAt h + i) mode owed
  let buf := setSlot buf Slot.hi (i + 1) (by sized h)
  hGoto buf (if i + 1 = nl then HP.treesL else HP.modes) (bp + 2) (by sized h)

/-- The count of literal codes, and room for the literal map: all zero with one code, read otherwise. -/
@[noinline] def stepTreesL (buf : ByteArray) (h : ringAt.toNat ≤ buf.size) : ByteArray :=
  let bp := slot buf Slot.bitpos h
  let v := varLen (bitsAt buf bp)
  let nt : UInt64 := v &&& 0xFFFFFFFF
  let size : UInt64 := slot buf Slot.cats h <<< 6
  let tn := slot buf Slot.tabNext h
  let buf := setSlot buf Slot.bitpos (bp + (v >>> 32)) h
  let buf := setSlot buf Slot.treesL nt (by sized h)
  let buf := setSlot buf Slot.lmapAt tn (by sized h)
  let buf := setSlot buf Slot.tabNext (tn + size) (by sized h)
  if nt < 2 then setSlot (fill64 buf tn 8 (size >>> 3) 0 owed) Slot.hphase HP.treesD (by sized h)
  else mapEnter buf tn size nt HP.treesD (by sized h)

/-- The count of distance codes, and room for the distance map likewise. -/
@[noinline] def stepTreesD (buf : ByteArray) (h : ringAt.toNat ≤ buf.size) : ByteArray :=
  let bp := slot buf Slot.bitpos h
  let v := varLen (bitsAt buf bp)
  let nt : UInt64 := v &&& 0xFFFFFFFF
  let size : UInt64 := slot buf (Slot.cats + 96) h <<< 2
  let room : UInt64 := (size + 7) &&& ~~~(7 : UInt64)
  let tn := slot buf Slot.tabNext h
  let buf := setSlot buf Slot.bitpos (bp + (v >>> 32)) h
  let buf := setSlot buf Slot.treesD nt (by sized h)
  let buf := setSlot buf Slot.dmapAt tn (by sized h)
  let buf := setSlot buf Slot.tabNext (tn + room) (by sized h)
  if nt < 2 then setSlot (fill64 buf tn 8 (room >>> 3) 0 owed) Slot.hphase HP.litInit (by sized h)
  else mapEnter buf tn size nt HP.litInit (by sized h)

/-- The next distance code, or the header's finishing. -/
def goDist (buf : ByteArray) (h : ringAt.toNat ≤ buf.size) : ByteArray :=
  if slot buf Slot.hcode h < slot buf Slot.treesD h then
    pcEnter buf (16 + slot buf Slot.ndirect h + ((48 : UInt64) <<< slot buf Slot.npostfix h)) 1 dsymAt 0 HP.distRet h
  else setSlot buf Slot.hphase HP.finish h

/-- The next insert-and-copy code; or, after the last, the distance symbols' table (rebuilt only when the distance
parameters differ from those it was last built for), room for the distance codes' names, and the first of them. -/
def goIc (buf : ByteArray) (h : ringAt.toNat ≤ buf.size) : ByteArray :=
  if slot buf Slot.hcode h < slot buf (Slot.cats + 48) h then pcEnter buf 704 1 cmdAt 0 HP.icRet h
  else
    let np := slot buf Slot.npostfix h
    let nd := slot buf Slot.ndirect h
    let key : UInt64 := ((nd <<< 8) ||| np) + 1
    let buf := if key = slot buf Slot.dsymKey h then buf else buildDsym buf np nd
    have h : ringAt.toNat ≤ buf.size := by sized h
    let tn := slot buf Slot.tabNext h
    let nt := slot buf Slot.treesD h
    let buf := setSlot buf Slot.dsymKey key h
    let buf := setSlot buf Slot.distNamesAt tn (by sized h)
    let buf := setSlot buf Slot.tabNext (tn + (nt <<< 3)) (by sized h)
    let buf := setSlot buf Slot.hcode 0 (by sized h)
    goDist buf (by sized h)

/-- The next literal code; or, after the last, room for the insert-and-copy codes' names, and the first of them. -/
def goLit (buf : ByteArray) (h : ringAt.toNat ≤ buf.size) : ByteArray :=
  if slot buf Slot.hcode h < slot buf Slot.treesL h then pcEnter buf 256 0 0 8 HP.litRet h
  else
    let tn := slot buf Slot.tabNext h
    let ni := slot buf (Slot.cats + 48) h
    let buf := setSlot buf Slot.icNamesAt tn h
    let buf := setSlot buf Slot.tabNext (tn + (ni <<< 3)) (by sized h)
    let buf := setSlot buf Slot.hcode 0 (by sized h)
    goIc buf (by sized h)

/-- Room for the literal codes' table positions, and the first of the codes. -/
@[noinline] def stepLitInit (buf : ByteArray) (h : ringAt.toNat ≤ buf.size) : ByteArray :=
  let tn := slot buf Slot.tabNext h
  let nt := slot buf Slot.treesL h
  let buf := setSlot buf Slot.litNamesAt tn h
  let buf := setSlot buf Slot.tabNext (tn + (((nt <<< 2) + 7) &&& ~~~(7 : UInt64))) (by sized h)
  let buf := setSlot buf Slot.hcode 0 (by sized h)
  goLit buf (by sized h)

/-- A literal code is built: its table's position kept. -/
@[noinline] def stepLitRet (buf : ByteArray) (h : ringAt.toNat ≤ buf.size) : ByteArray :=
  let k := slot buf Slot.hcode h
  let name := slot buf Slot.name h
  let buf := store32 buf (slot buf Slot.litNamesAt h + (k <<< 2)) (name &&& 0xFFFFFFFF) owed
  let buf := setSlot buf Slot.hcode (k + 1) (by sized h)
  goLit buf (by sized h)

/-- An insert-and-copy code is built: its table's name kept. -/
@[noinline] def stepIcRet (buf : ByteArray) (h : ringAt.toNat ≤ buf.size) : ByteArray :=
  let k := slot buf Slot.hcode h
  let name := slot buf Slot.name h
  let buf := store64 buf (slot buf Slot.icNamesAt h + (k <<< 3)) name owed
  let buf := setSlot buf Slot.hcode (k + 1) (by sized h)
  goIc buf (by sized h)

/-- A distance code is built: its table's name kept. -/
@[noinline] def stepDistRet (buf : ByteArray) (h : ringAt.toNat ≤ buf.size) : ByteArray :=
  let k := slot buf Slot.hcode h
  let name := slot buf Slot.name h
  let buf := store64 buf (slot buf Slot.distNamesAt h + (k <<< 3)) name owed
  let buf := setSlot buf Slot.hcode (k + 1) (by sized h)
  goDist buf (by sized h)

/-! ### Finishing -/

/-- Whether each literal block type from `t` to `nl` has one code for all its 64 contexts. -/
def trivFrom (buf : ByteArray) (lm t nl : UInt64) : Bool :=
  if ht : t < nl then
    have : nl.toNat - (t + 1).toNat < nl.toNat - t.toNat := succ_nearer ht
    let p : UInt64 := lm + (t <<< 6)
    let pat : UInt64 := load8 buf p owed * (0x0101010101010101 : UInt64)
    if load64 buf p owed = pat ∧ load64 buf (p + 8) owed = pat ∧ load64 buf (p + 16) owed = pat ∧
        load64 buf (p + 24) owed = pat ∧ load64 buf (p + 32) owed = pat ∧ load64 buf (p + 40) owed = pat ∧
        load64 buf (p + 48) owed = pat ∧ load64 buf (p + 56) owed = pat then trivFrom buf lm (t + 1) nl
    else false
  else true
termination_by nl.toNat - t.toNat

/-- A literal block type's 64 codes as table positions, 4 bytes each at `row`, from the `k`th: the map at `lm`
composed with the codes' table positions at `names`. -/
def rowFill (buf : ByteArray) (lm names row k : UInt64) : ByteArray :=
  if hk : k < 64 then
    have : 64 - (k + 1).toNat < 64 - k.toNat := succ_nearer hk
    rowFill (store32 buf (row + (k <<< 2)) (load32 buf (names + (load8 buf (lm + k) owed <<< 2)) owed) owed) lm names
      row (k + 1)
  else buf
termination_by 64 - k.toNat

@[simp] theorem rowFill_size (buf : ByteArray) (lm names row k : UInt64) :
    (rowFill buf lm names row k).size = buf.size := by
  fun_induction rowFill buf lm names row k <;> simp_all +zetaDelta

/-- A literal block type's context table at `dst`, from the last byte `p` on: 32 bytes a last byte, the table
position for each class of the byte before (`ctxWay`). A last byte's contexts are neighbours in the row of 64, so
they are copied from it as a block: 8 of them in the signed mode, 4 in UTF-8 where the last byte's part leaves the
two low bits free (elsewhere in UTF-8 the four are fetched one by one), and one in the two modes that use the last
byte alone. `cta` is the mode's part of the context table. -/
def ctxFill (buf : ByteArray) (mode cta row dst p : UInt64) : ByteArray :=
  if hp : p < 256 then
    have : 256 - (p + 1).toNat < 256 - p.toNat := succ_nearer hp
    let part := load8 buf (cta + p) owed
    let d : UInt64 := dst + (p <<< 5)
    let src : UInt64 := row + (part <<< 2)
    let buf :=
      if mode < 2 then store32 buf d (load32 buf src owed) owed
      else if mode = 3 then copy16 (copy16 buf d src owed) (d + 16) (src + 16) owed
      else if part &&& 3 = 0 then copy16 buf d src owed
      else
        let buf := store32 buf d (load32 buf src owed) owed
        let buf := store32 buf (d + 4) (load32 buf (row + ((part ||| 1) <<< 2)) owed) owed
        let buf := store32 buf (d + 8) (load32 buf (row + ((part ||| 2) <<< 2)) owed) owed
        store32 buf (d + 12) (load32 buf (row + ((part ||| 3) <<< 2)) owed) owed
    ctxFill buf mode cta row dst (p + 1)
  else buf
termination_by 256 - p.toNat

@[simp] theorem ctxFill_size (buf : ByteArray) (mode cta row dst p : UInt64) :
    (ctxFill buf mode cta row dst p).size = buf.size := by
  fun_induction ctxFill buf mode cta row dst p <;> simp_all +zetaDelta <;> (repeat' split) <;> simp

/-- The context tables of the literal block types from `t` to `nl`, 8192 bytes each from `dst`; `row` is 256 bytes
of scratch for a type's row. -/
def ctxTypes (buf : ByteArray) (modes lm names dst row t nl : UInt64) : ByteArray :=
  if ht : t < nl then
    have : nl.toNat - (t + 1).toNat < nl.toNat - t.toNat := succ_nearer ht
    let mode := load8 buf (modes + t) owed
    let buf := rowFill buf (lm + (t <<< 6)) names row 0
    ctxTypes (ctxFill buf mode (ctxTabAt + (mode <<< 9)) row (dst + (t <<< 13)) 0) modes lm names dst row (t + 1) nl
  else buf
termination_by nl.toNat - t.toNat

@[simp] theorem ctxTypes_size (buf : ByteArray) (modes lm names dst row t nl : UInt64) :
    (ctxTypes buf modes lm names dst row t nl).size = buf.size := by
  fun_induction ctxTypes buf modes lm names dst row t nl <;> simp_all +zetaDelta

/-- The distance block types' rows from the `k`th name to the `n`th: the name of the table of the code the map
gives. -/
def distRows (buf : ByteArray) (dm names dst k n : UInt64) : ByteArray :=
  if hk : k < n then
    have : n.toNat - (k + 1).toNat < n.toNat - k.toNat := succ_nearer hk
    let code := load8 buf (dm + k) owed
    distRows (store64 buf (dst + (k <<< 3)) (load64 buf (names + (code <<< 3)) owed) owed) dm names dst (k + 1) n
  else buf
termination_by n.toNat - k.toNat

@[simp] theorem distRows_size (buf : ByteArray) (dm names dst k n : UInt64) :
    (distRows buf dm names dst k n).size = buf.size := by
  fun_induction distRows buf dm names dst k n <;> simp_all +zetaDelta

/-- The command loop's slots set for the first blocks, with the rows at `rl` and `rd`, and the phase made the
commands. -/
def finishSlots (buf : ByteArray) (triv : Bool) (rl rd nd lm names modes : UInt64) (h : ringAt.toNat ≤ buf.size) :
    ByteArray :=
  let ic := load64 buf (slot buf Slot.icNamesAt h) owed
  let mode0 := load8 buf modes owed
  let lit0 := load32 buf (names + (load8 buf lm owed <<< 2)) owed
  let counters : UInt64 := (slot buf Slot.counters h &&& ((3 : UInt64) <<< 62)) ||| slot buf (Slot.cats + 24) h |||
    (slot buf (Slot.cats + 120) h <<< 25)
  let buf := setSlot buf Slot.tabNext (rd + (nd <<< 5)) h
  let buf := setSlot buf Slot.rowsL rl (by sized h)
  let buf := setSlot buf Slot.rowsD rd (by sized h)
  let buf := setSlot buf Slot.triv (if triv then 1 else 0) (by sized h)
  let buf := setSlot buf Slot.icTable ic (by sized h)
  let buf := setSlot buf Slot.icLeft (slot buf (Slot.cats + 72) (by sized h)) (by sized h)
  let buf := setSlot buf Slot.ctxRow rl (by sized h)
  let buf := setSlot buf Slot.ctxOff (ctxTabAt + (mode0 <<< 9) + 256) (by sized h)
  let buf := setSlot buf Slot.litRow lit0 (by sized h)
  let buf := setSlot buf Slot.distRow rd (by sized h)
  let buf := setSlot buf Slot.counters counters (by sized h)
  let buf := setSlot buf Slot.cmd cmdNone (by sized h)
  let buf := setSlot buf Slot.lits 0 (by sized h)
  setSlot buf Slot.phase Phase.commands (by sized h)

/-- The header's end: the maps composed with the tables' names into what the command loop reads (a context table
for each literal block type unless every type's contexts are trivial, and a row of four names for each distance block
type), then the loop's slots. The output's bound and the budget are the driver's. -/
@[noinline] def stepFinish (buf : ByteArray) (h : ringAt.toNat ≤ buf.size) : ByteArray :=
  let nl := slot buf Slot.cats h
  let nd := slot buf (Slot.cats + 96) h
  let lm := slot buf Slot.lmapAt h
  let names := slot buf Slot.litNamesAt h
  let modes := slot buf Slot.modesAt h
  let rl := slot buf Slot.tabNext h
  let triv := trivFrom buf lm 0 nl
  let rd : UInt64 := if triv then rl else rl + (nl <<< 13)
  let dm := slot buf Slot.dmapAt h
  let dnames := slot buf Slot.distNamesAt h
  let buf := if triv then buf else ctxTypes buf modes lm names rl (rd + (nd <<< 5)) 0 nl
  finishSlots (distRows buf dm dnames rd 0 (nd <<< 2)) triv rl rd nd lm names modes (by sized h)

/-! ### The machine -/

/-- A header begun: the first category's count of block types is next. `Slot.tabNext` is where the meta-block's tables
go, set by whoever starts the meta-block. No command is in pieces. -/
def headerStart (buf : ByteArray) (h : ringAt.toNat ≤ buf.size) : ByteArray :=
  -- the block types seen (5.10): none, but each category's first, type 0
  let buf := fill64 buf seenAt 8 12 0 (seenFill h)
  let buf := store64 buf seenAt 1 (front (by sized h))
  let buf := store64 buf (seenAt + 32) 1 (front (by sized h))
  let buf := store64 buf (seenAt + 64) 1 (front (by sized h))
  have h : ringAt.toNat ≤ buf.size := by sized h
  let buf := setSlot buf Slot.pend 0 h
  let buf := setSlot buf Slot.hcat 0 (by sized h)
  let buf := setSlot buf Slot.hphase HP.catN (by sized h)
  setSlot buf Slot.phase Phase.header (by sized h)

/-- The bits the single element at place `p` takes, read at `bp` (5.4: an element is read whole or not at all). The
places that read nothing, and the three loops, which see to their own elements, take none here. -/
def elemBits (buf : ByteArray) (p bp : UInt64) (h : ringAt.toNat ≤ buf.size) : UInt64 :=
  if p = HP.catN ∨ p = HP.treesL ∨ p = HP.treesD then varLen (bitsAt buf bp) >>> 32
  else if p = HP.catFirst then
    let w := bitsAt buf bp
    let e := lookup buf (load64 buf (catAt (slot buf Slot.hcat h) + Cat.countName) owed) w
    (e &&& (15 : UInt64)) + (load32 countTab ((e >>> 4) <<< 2) owed >>> 24)
  else if p = HP.params then 6
  else if p = HP.modes then 2
  else if p = HP.pcStart then (if bitsAt buf bp &&& (3 : UInt64) = 1 then 4 else 2)
  else if p = HP.pcSym then slot buf Slot.habits h
  else if p = HP.pcSel ∨ p = HP.mapImtf then 1
  else if p = HP.mapRle then (if bitsAt buf bp &&& (1 : UInt64) = 0 then 1 else 5)
  else 0

/-- The step at place `p`. -/
def headerDo (buf : ByteArray) (p : UInt64) (h : ringAt.toNat ≤ buf.size) : ByteArray :=
  if p = 0 then stepCatN buf h
  else if p = 1 then stepCatType buf h
  else if p = 2 then stepCatCount buf h
  else if p = 3 then stepCatFirst buf h
  else if p = 4 then stepParams buf h
  else if p = 5 then stepModes buf h
  else if p = 6 then stepTreesL buf h
  else if p = 7 then stepTreesD buf h
  else if p = 8 then stepLitInit buf h
  else if p = 9 then stepLitRet buf h
  else if p = 10 then stepIcRet buf h
  else if p = 11 then stepDistRet buf h
  else if p = 12 then stepFinish buf h
  else if p = 13 then stepPcStart buf h
  else if p = 14 then stepPcSym buf h
  else if p = 15 then stepPcSel buf h
  else if p = 16 then stepPcLens buf h
  else if p = 17 then stepMapRle buf h
  else if p = 18 then stepMapCodeRet buf h
  else if p = 19 then stepMapVals buf h
  else if p = 20 then stepMapImtf buf h
  else stepPcCl buf h

/-- One step of the header from its place: one element, or as much of a loop as the real input ahead allows. The
header is over when the phase is no longer the header: the commands, or rejected.

A single element is read whole or not at all (5.4). No single element of a header is longer than 39 bits, so while
64 real bits lie ahead the step is taken with no more ado; in the last bits of a chunk the element's own length is
worked out first, and the step taken only if every bit of it is real. Otherwise nothing is changed but the reason,
which becomes "input". -/
def headerStep (buf : ByteArray) (h : ringAt.toNat ≤ buf.size) : ByteArray :=
  let p := slot buf Slot.hphase h
  let bp := slot buf Slot.bitpos h
  let e := slot buf Slot.inEnd h
  if bp + 64 ≤ e then headerDo buf p h
  else if bp + elemBits buf p bp h ≤ e then headerDo buf p h
  else setSlot buf Slot.reason Reason.input h

/-! ### Every part keeps the buffer's size -/

-- one tactic serves them all, with the facts about a choice's size given whether a part has a choice or not
set_option linter.unusedSimpArgs false

@[simp] theorem pcBuild_size (buf : ByteArray)  (h : ringAt.toNat ≤ buf.size) :
    (pcBuild buf  h).size = buf.size := by
  simp [pcBuild, apply_ite ByteArray.size, apply_dite ByteArray.size]

@[simp] theorem simpleBuild_size (buf : ByteArray) (n syms sel : UInt64) (h : ringAt.toNat ≤ buf.size) :
    (simpleBuild buf n syms sel h).size = buf.size := by
  simp [simpleBuild, apply_ite ByteArray.size, apply_dite ByteArray.size]

@[simp] theorem clDone_size (buf : ByteArray) (bp nz lens : UInt64) (h : ringAt.toNat ≤ buf.size) :
    (clDone buf bp nz lens h).size = buf.size := by
  simp [clDone, apply_ite ByteArray.size, apply_dite ByteArray.size]

@[simp] theorem clSave_size (buf : ByteArray) (bp i sum nz lens : UInt64) (h : ringAt.toNat ≤ buf.size) :
    (clSave buf bp i sum nz lens h).size = buf.size := by
  simp [clSave, apply_ite ByteArray.size, apply_dite ByteArray.size]

@[simp] theorem clLoop_size (real : (buf : ByteArray) → UInt64 → ringAt.toNat ≤ buf.size → Bool)  (buf : ByteArray) (bp w lim i sum nz lens : UInt64) (h : ringAt.toNat ≤ buf.size) :
    (clLoop real  buf bp w lim i sum nz lens h).size = buf.size := by
  fun_induction clLoop real  buf bp w lim i sum nz lens h <;>
    simp_all +zetaDelta [apply_ite ByteArray.size, apply_dite ByteArray.size]

@[simp] theorem clGo_size (buf : ByteArray) (bp w lim i sum nz lens : UInt64) (h : ringAt.toNat ≤ buf.size) :
    (clGo buf bp w lim i sum nz lens h).size = buf.size := by
  simp [clGo, apply_ite ByteArray.size, apply_dite ByteArray.size]

@[simp] theorem stepPcStart_size (buf : ByteArray)  (h : ringAt.toNat ≤ buf.size) :
    (stepPcStart buf  h).size = buf.size := by
  simp [stepPcStart, apply_ite ByteArray.size, apply_dite ByteArray.size]

@[simp] theorem stepPcCl_size (buf : ByteArray)  (h : ringAt.toNat ≤ buf.size) :
    (stepPcCl buf  h).size = buf.size := by
  simp [stepPcCl, apply_ite ByteArray.size, apply_dite ByteArray.size]

@[simp] theorem stepPcSym_size (buf : ByteArray)  (h : ringAt.toNat ≤ buf.size) :
    (stepPcSym buf  h).size = buf.size := by
  simp [stepPcSym, apply_ite ByteArray.size, apply_dite ByteArray.size]

@[simp] theorem stepPcSel_size (buf : ByteArray)  (h : ringAt.toNat ≤ buf.size) :
    (stepPcSel buf  h).size = buf.size := by
  simp [stepPcSel, apply_ite ByteArray.size, apply_dite ByteArray.size]

@[simp] theorem lensSave_size (buf : ByteArray) (bp i sum prev rep : UInt64) (h : ringAt.toNat ≤ buf.size) :
    (lensSave buf bp i sum prev rep h).size = buf.size := by
  simp [lensSave, apply_ite ByteArray.size, apply_dite ByteArray.size]

@[simp] theorem lensDone_size (buf : ByteArray) (bp : UInt64) (h : ringAt.toNat ≤ buf.size) :
    (lensDone buf bp h).size = buf.size := by
  simp [lensDone, apply_ite ByteArray.size, apply_dite ByteArray.size]

@[simp] theorem lensLoop_size (real : (buf : ByteArray) → UInt64 → ringAt.toNat ≤ buf.size → Bool)  (buf : ByteArray) (bp w lim i iEnd space pr : UInt64) (h : ringAt.toNat ≤ buf.size) :
    (lensLoop real  buf bp w lim i iEnd space pr h).size = buf.size := by
  fun_induction lensLoop real  buf bp w lim i iEnd space pr h <;>
    simp_all +zetaDelta [apply_ite ByteArray.size, apply_dite ByteArray.size]

@[simp] theorem stepPcLens_size (buf : ByteArray)  (h : ringAt.toNat ≤ buf.size) :
    (stepPcLens buf  h).size = buf.size := by
  simp [stepPcLens, apply_ite ByteArray.size, apply_dite ByteArray.size]

@[simp] theorem mapEnter_size (buf : ByteArray) (mp size nt ret : UInt64) (h : ringAt.toNat ≤ buf.size) :
    (mapEnter buf mp size nt ret h).size = buf.size := by
  simp [mapEnter, apply_ite ByteArray.size, apply_dite ByteArray.size]

@[simp] theorem stepMapRle_size (buf : ByteArray)  (h : ringAt.toNat ≤ buf.size) :
    (stepMapRle buf  h).size = buf.size := by
  simp [stepMapRle, apply_ite ByteArray.size, apply_dite ByteArray.size]

@[simp] theorem stepMapCodeRet_size (buf : ByteArray)  (h : ringAt.toNat ≤ buf.size) :
    (stepMapCodeRet buf  h).size = buf.size := by
  simp [stepMapCodeRet, apply_ite ByteArray.size, apply_dite ByteArray.size]

@[simp] theorem valsLoop_size (real : (buf : ByteArray) → UInt64 → ringAt.toNat ≤ buf.size → Bool) (name : UInt64) (buf : ByteArray) (bp w lim p pEnd : UInt64) (h : ringAt.toNat ≤ buf.size) :
    (valsLoop real name buf bp w lim p pEnd h).size = buf.size := by
  fun_induction valsLoop real name buf bp w lim p pEnd h <;>
    simp_all +zetaDelta [apply_ite ByteArray.size, apply_dite ByteArray.size]

@[simp] theorem stepMapVals_size (buf : ByteArray)  (h : ringAt.toNat ≤ buf.size) :
    (stepMapVals buf  h).size = buf.size := by
  simp [stepMapVals, apply_ite ByteArray.size, apply_dite ByteArray.size]

@[simp] theorem stepMapImtf_size (buf : ByteArray)  (h : ringAt.toNat ≤ buf.size) :
    (stepMapImtf buf  h).size = buf.size := by
  simp [stepMapImtf, apply_ite ByteArray.size, apply_dite ByteArray.size]

@[simp] theorem catNext_size (buf : ByteArray) (c : UInt64) (h : ringAt.toNat ≤ buf.size) :
    (catNext buf c h).size = buf.size := by
  simp [catNext, apply_ite ByteArray.size, apply_dite ByteArray.size]

@[simp] theorem stepCatN_size (buf : ByteArray)  (h : ringAt.toNat ≤ buf.size) :
    (stepCatN buf  h).size = buf.size := by
  simp [stepCatN, apply_ite ByteArray.size, apply_dite ByteArray.size]

@[simp] theorem stepCatType_size (buf : ByteArray)  (h : ringAt.toNat ≤ buf.size) :
    (stepCatType buf  h).size = buf.size := by
  simp [stepCatType, apply_ite ByteArray.size, apply_dite ByteArray.size]

@[simp] theorem stepCatCount_size (buf : ByteArray)  (h : ringAt.toNat ≤ buf.size) :
    (stepCatCount buf  h).size = buf.size := by
  simp [stepCatCount, apply_ite ByteArray.size, apply_dite ByteArray.size]

@[simp] theorem stepCatFirst_size (buf : ByteArray)  (h : ringAt.toNat ≤ buf.size) :
    (stepCatFirst buf  h).size = buf.size := by
  simp [stepCatFirst, apply_ite ByteArray.size, apply_dite ByteArray.size]

@[simp] theorem stepParams_size (buf : ByteArray)  (h : ringAt.toNat ≤ buf.size) :
    (stepParams buf  h).size = buf.size := by
  simp [stepParams, apply_ite ByteArray.size, apply_dite ByteArray.size]

@[simp] theorem stepModes_size (buf : ByteArray)  (h : ringAt.toNat ≤ buf.size) :
    (stepModes buf  h).size = buf.size := by
  simp [stepModes, apply_ite ByteArray.size, apply_dite ByteArray.size]

@[simp] theorem stepTreesL_size (buf : ByteArray)  (h : ringAt.toNat ≤ buf.size) :
    (stepTreesL buf  h).size = buf.size := by
  simp [stepTreesL, apply_ite ByteArray.size, apply_dite ByteArray.size]

@[simp] theorem stepTreesD_size (buf : ByteArray)  (h : ringAt.toNat ≤ buf.size) :
    (stepTreesD buf  h).size = buf.size := by
  simp [stepTreesD, apply_ite ByteArray.size, apply_dite ByteArray.size]

@[simp] theorem goDist_size (buf : ByteArray)  (h : ringAt.toNat ≤ buf.size) :
    (goDist buf  h).size = buf.size := by
  simp [goDist, apply_ite ByteArray.size, apply_dite ByteArray.size]

@[simp] theorem goIc_size (buf : ByteArray)  (h : ringAt.toNat ≤ buf.size) :
    (goIc buf  h).size = buf.size := by
  simp [goIc, apply_ite ByteArray.size, apply_dite ByteArray.size]

@[simp] theorem goLit_size (buf : ByteArray)  (h : ringAt.toNat ≤ buf.size) :
    (goLit buf  h).size = buf.size := by
  simp [goLit, apply_ite ByteArray.size, apply_dite ByteArray.size]

@[simp] theorem stepLitInit_size (buf : ByteArray)  (h : ringAt.toNat ≤ buf.size) :
    (stepLitInit buf  h).size = buf.size := by
  simp [stepLitInit, apply_ite ByteArray.size, apply_dite ByteArray.size]

@[simp] theorem stepLitRet_size (buf : ByteArray)  (h : ringAt.toNat ≤ buf.size) :
    (stepLitRet buf  h).size = buf.size := by
  simp [stepLitRet, apply_ite ByteArray.size, apply_dite ByteArray.size]

@[simp] theorem stepIcRet_size (buf : ByteArray)  (h : ringAt.toNat ≤ buf.size) :
    (stepIcRet buf  h).size = buf.size := by
  simp [stepIcRet, apply_ite ByteArray.size, apply_dite ByteArray.size]

@[simp] theorem stepDistRet_size (buf : ByteArray)  (h : ringAt.toNat ≤ buf.size) :
    (stepDistRet buf  h).size = buf.size := by
  simp [stepDistRet, apply_ite ByteArray.size, apply_dite ByteArray.size]

@[simp] theorem finishSlots_size (buf : ByteArray) (triv : Bool) (rl rd nd lm names modes : UInt64) (h : ringAt.toNat ≤ buf.size) :
    (finishSlots buf triv rl rd nd lm names modes h).size = buf.size := by
  simp [finishSlots, apply_ite ByteArray.size, apply_dite ByteArray.size]

@[simp] theorem stepFinish_size (buf : ByteArray)  (h : ringAt.toNat ≤ buf.size) :
    (stepFinish buf  h).size = buf.size := by
  simp [stepFinish, apply_ite ByteArray.size, apply_dite ByteArray.size]

@[simp] theorem headerStart_size (buf : ByteArray)  (h : ringAt.toNat ≤ buf.size) :
    (headerStart buf  h).size = buf.size := by
  simp [headerStart, apply_ite ByteArray.size, apply_dite ByteArray.size]

@[simp] theorem headerDo_size (buf : ByteArray) (p : UInt64) (h : ringAt.toNat ≤ buf.size) :
    (headerDo buf p h).size = buf.size := by
  simp [headerDo, apply_ite ByteArray.size, apply_dite ByteArray.size]

@[simp] theorem headerStep_size (buf : ByteArray)  (h : ringAt.toNat ≤ buf.size) :
    (headerStep buf  h).size = buf.size := by
  simp [headerStep, apply_ite ByteArray.size, apply_dite ByteArray.size]
