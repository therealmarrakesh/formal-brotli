module

public import Brotli.FastDecoder.Layout
public import Brotli.FastDecoder.Bits
public import Brotli.FastDecoder.Num
public import Brotli.FastDecoder.Owed

@[expose] public section

/-!
# A prefix code's table, and its builder
**The table** (`DESIGN.md` 5.7). Entries of 16 bits. A table has a *root* of `2 ^ r` entries, where `r` is the code's
longest length up to `rootCap`, indexed by the next `r` bits of input. An entry with its top bit clear is a symbol
(bits 4 to 14) with its code's length (bits 0 to 3). A root entry with its top bit set points to a *sub-table*: its
low 4 bits are the sub-table's width in bits and bits 4 to 14 its place, in entries from the table's start; it is
indexed by the bits after the root's, and its entries hold a symbol with its code's whole length. So a lookup ends at
an entry whose low 4 bits are the bits to consume, whichever level it is in. A code of one symbol has `r = 0` and one
entry, of length zero. A table is *named* by one value: its position in `buf` in the low 32 bits and its root's mask,
`2 ^ r - 1`, above, so that a lookup's index is the input and the mask and no width is turned into a mask on the way.
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

/-- The low 8 bits of `k` in reverse order, from the copy of `rev8` in the buffer's front: read at a constant place
in `buf`, with no pointer of its own to load (`DESIGN.md` 8.1). -/
@[inline] def revB (buf : ByteArray) (k : UInt64) : UInt64 :=
  load8 buf (revAt + (k &&& 255)) owed

/-! ### Lookup -/

/-- The entry for the code at the bottom of `w` in the narrow table `name`: its low 4 bits are the code's length and
the bits above are the symbol. `w` holds at least 15 bits of input. -/
@[inline] def lookup (buf : ByteArray) (name w : UInt64) : UInt64 :=
  let pos : UInt64 := name &&& 0xFFFFFFFF
  let e := load16 buf (pos + ((w &&& (name >>> 32)) <<< 1)) owed
  if e &&& 0x8000 = 0 then e
  else load16 buf (pos + ((((e >>> 4) &&& 0x7FF) + ((w >>> rootCap) &&& mask (e &&& 15))) <<< 1)) owed

/-- The same for a narrow table at `pos` whose root is 8 bits whatever its code: the index does not wait for the
table's name. -/
@[inline] def lookup8 (buf : ByteArray) (pos w : UInt64) : UInt64 :=
  let e := load16 buf (pos + ((w &&& 0xFF) <<< 1)) owed
  if e &&& 0x8000 = 0 then e
  else load16 buf (pos + ((((e >>> 4) &&& (0x7FF : UInt64)) + ((w >>> 8) &&& mask (e &&& 15))) <<< 1)) owed

/-- The entry for the code at the bottom of `w` in the wide table `name`: what the symbol stands for, with the code's
length added into its two low bytes. -/
@[inline] def lookupW (buf : ByteArray) (name w : UInt64) : UInt64 :=
  let pos : UInt64 := name &&& 0xFFFFFFFF
  let e := load64 buf (pos + ((w &&& (name >>> 32)) <<< 3)) owed
  if e &&& 0x80 = 0 then e
  else load64 buf (pos + (((e >>> 32) + ((w >>> rootCap) &&& mask ((e >>> 8) &&& 0xFF))) <<< 3)) owed

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

@[simp] theorem listAdd_size (buf : ByteArray) (len s : UInt64) : (listAdd buf len s).size = buf.size := by
  simp [listAdd]

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


/-- Symbol `sym` of length `len` written to `count` slots of the table at `pos`, from slot `idx` and every `stride`
slots after. With `wide = 0` an entry is 2 bytes, the symbol and its length; otherwise 8 bytes, what the symbol stands
for (the 8 bytes at `mt + 8 * sym`) with the length added into its two low bytes. -/
@[inline] def put (wide mt : UInt64) (buf : ByteArray) (pos idx stride count sym len : UInt64) : ByteArray :=
  if wide = 0 then fill16 buf (pos + (idx <<< 1)) (stride <<< 1) count ((sym <<< 4) ||| len) owed
  else fill64 buf (pos + (idx <<< 3)) (stride <<< 3) count (load64 buf (mt + (sym <<< 3)) owed + len * 257) owed

@[simp] theorem put_size (wide mt : UInt64) (buf : ByteArray) (pos idx stride count sym len : UInt64) :
    (put wide mt buf pos idx stride count sym len).size = buf.size := by
  unfold put
  split <;> simp

/-- The root slot `idx` made a pointer to the sub-table of width `tb` at entry `nxt`. -/
@[inline] def putPtr (wide : UInt64) (buf : ByteArray) (pos idx tb nxt : UInt64) : ByteArray :=
  if wide = 0 then store16 buf (pos + (idx <<< 1)) ((0x8000 : UInt64) ||| (nxt <<< 4) ||| tb) owed
  else store64 buf (pos + (idx <<< 3)) ((0x80 : UInt64) ||| (tb <<< 8) ||| (nxt <<< 32)) owed

@[simp] theorem putPtr_size (wide : UInt64) (buf : ByteArray) (pos idx tb nxt : UInt64) :
    (putPtr wide buf pos idx tb nxt).size = buf.size := by
  unfold putPtr
  split <;> simp

/-- The builder's results put in the slow state: the table's name, and where the next table goes. `nxt` is the
table's size in entries. -/
@[inline] def built (wide : UInt64) (buf : ByteArray) (pos r nxt : UInt64) (h : ringAt.toNat ≤ buf.size) :
    ByteArray :=
  let buf1 := setSlot buf Slot.name (pos ||| (mask r <<< 32)) h
  setSlot buf1 Slot.tabNext (pos + (nxt <<< (if wide = 0 then 1 else 3))) (by sized h)

@[simp] theorem built_size (wide : UInt64) (buf : ByteArray) (pos r nxt : UInt64) (h : ringAt.toNat ≤ buf.size) :
    (built wide buf pos r nxt h).size = buf.size := by
  simp [built]

/-- A run of `n` symbols of one length from `s` on in their list, written into one table (the root, or one
sub-table): symbol by symbol, each to `cnt` slots, the first at `base` and the slot that `key` reversed names, and
every `stride` slots after; `key`, the code with its first bit highest of 8, goes up by `kstep` a symbol. `ent` makes
a symbol's entry from the symbol and `la`, what its length adds; `fil` writes it. The loop is compiled once for each
kind of entry, and carries nothing for the choice. The symbol after the run is left in `Slot.walk`. -/
@[specialize] def tabRun (ent : ByteArray → UInt64 → UInt64 → UInt64)
    (fil : ByteArray → UInt64 → UInt64 → UInt64 → UInt64 → UInt64 → ByteArray)
    (buf : ByteArray) (base la stride cnt kstep s n key : UInt64) : ByteArray :=
  if hn : n = 0 then store64 buf Slot.walk s owed
  else
    have : (n - 1).toNat < n.toNat := pred_lt hn
    let next := listNext buf s
    tabRun ent fil (fil buf base (revB buf key) stride cnt (ent buf s la)) base la stride cnt kstep next (n - 1)
      (key + kstep)
termination_by n.toNat

theorem tabRun_size (ent : ByteArray → UInt64 → UInt64 → UInt64)
    (fil : ByteArray → UInt64 → UInt64 → UInt64 → UInt64 → UInt64 → ByteArray)
    (hf : ∀ b base idx st c v, (fil b base idx st c v).size = b.size)
    (buf : ByteArray) (base la stride cnt kstep s n key : UInt64) :
    (tabRun ent fil buf base la stride cnt kstep s n key).size = buf.size := by
  fun_induction tabRun ent fil buf base la stride cnt kstep s n key <;> simp_all

/-- The run for narrow entries: the symbol and its length, 2 bytes. -/
@[noinline] def runNarrow (buf : ByteArray) (base len stride cnt kstep s n key : UInt64) : ByteArray :=
  tabRun (fun _ s la => (s <<< 4) ||| la)
    (fun buf base idx stride cnt v => fill16 buf (base + (idx <<< 1)) (stride <<< 1) cnt v owed)
    buf base len stride cnt kstep s n key

/-- The run for wide entries: what the symbol stands for (the 8 bytes at `mt + 8 * sym`) with the length added into
its two low bytes. -/
@[noinline] def runWide (mt : UInt64) (buf : ByteArray) (base len stride cnt kstep s n key : UInt64) : ByteArray :=
  tabRun (fun buf s la => load64 buf (mt + (s <<< 3)) owed + la)
    (fun buf base idx stride cnt v => fill64 buf (base + (idx <<< 3)) (stride <<< 3) cnt v owed)
    buf base (len * 257) stride cnt kstep s n key

@[simp] theorem runNarrow_size (buf : ByteArray) (base len stride cnt kstep s n key : UInt64) :
    (runNarrow buf base len stride cnt kstep s n key).size = buf.size := by
  unfold runNarrow
  exact tabRun_size _ _ (by intros; simp) ..

@[simp] theorem runWide_size (mt : UInt64) (buf : ByteArray) (base len stride cnt kstep s n key : UInt64) :
    (runWide mt buf base len stride cnt kstep s n key).size = buf.size := by
  unfold runWide
  exact tabRun_size _ _ (by intros; simp) ..

/-- A run in the table at `pos`, of the kind `wide` and `mt` say, from entry `at0` of it. -/
@[inline] def runIn (wide mt pos : UInt64) (buf : ByteArray) (at0 len stride cnt kstep s n key : UInt64) : ByteArray :=
  if wide = 0 then runNarrow buf (pos + (at0 <<< 1)) len stride cnt kstep s n key
  else runWide mt buf (pos + (at0 <<< 3)) len stride cnt kstep s n key

@[simp] theorem runIn_size (wide mt pos : UInt64) (buf : ByteArray) (at0 len stride cnt kstep s n key : UInt64) :
    (runIn wide mt pos buf at0 len stride cnt kstep s n key).size = buf.size := by
  unfold runIn
  split <;> simp

/-- The `n` symbols of one length beyond the root, from `s` on in their list, written into sub-tables. `key` is the
code with its first bit highest of 16: its high byte is the root slot the symbol's sub-table hangs from and its low
byte the code within the sub-table. The low byte is zero exactly when a new root slot begins, and then the sub-table
is started in passing: its width worked out from the symbols remaining (`subWidth`), the root slot pointed at it
(`ptr`). `cur` and `tb` are the current sub-table's place and width, `nxt` the next free entry; they are left in
`Slot.walk` (16 bits each for `cur` and `nxt`, `tb` above). The root is `rootCap` bits wherever there are sub-tables.
Compiled once for each kind of entry, as `tabRun`. -/
@[specialize] def subRun (ent : ByteArray → UInt64 → UInt64 → UInt64)
    (fil : ByteArray → UInt64 → UInt64 → UInt64 → UInt64 → UInt64 → ByteArray)
    (ptr : ByteArray → UInt64 → UInt64 → UInt64 → UInt64 → ByteArray)
    (buf : ByteArray) (pos len la s n key cur tb nxt : UInt64) : ByteArray :=
  if hn : n = 0 then store64 buf Slot.walk (cur ||| (nxt <<< 16) ||| (tb <<< 32)) owed
  else
    let d : UInt64 := len - rootCap
    let go := fun (buf : ByteArray) (cur tb nxt : UInt64) =>
      have : (n - 1).toNat < n.toNat := pred_lt hn
      let next := listNext buf s
      subRun ent fil ptr
        (fil buf pos (cur + revB buf key) ((1 : UInt64) <<< d) ((1 : UInt64) <<< (tb - d)) (ent buf s la))
        pos len la next (n - 1) (key + ((0x10000 : UInt64) >>> len)) cur tb nxt
    if key &&& 0xFF = 0 then
      let tb' := subWidth buf rootCap len n ((1 : UInt64) <<< d)
      go (ptr buf pos (revB buf (key >>> 8)) tb' nxt) nxt tb' (nxt + ((1 : UInt64) <<< tb'))
    else go buf cur tb nxt
termination_by n.toNat

@[noinline] def subNarrow (buf : ByteArray) (pos len s n key cur tb nxt : UInt64) : ByteArray :=
  subRun (fun _ s la => (s <<< 4) ||| la)
    (fun buf base idx stride cnt v => fill16 buf (base + (idx <<< 1)) (stride <<< 1) cnt v owed)
    (fun buf pos idx tb nxt => putPtr 0 buf pos idx tb nxt)
    buf pos len len s n key cur tb nxt

@[noinline] def subWide (mt : UInt64) (buf : ByteArray) (pos len s n key cur tb nxt : UInt64) : ByteArray :=
  subRun (fun buf s la => load64 buf (mt + (s <<< 3)) owed + la)
    (fun buf base idx stride cnt v => fill64 buf (base + (idx <<< 3)) (stride <<< 3) cnt v owed)
    (fun buf pos idx tb nxt => putPtr 1 buf pos idx tb nxt)
    buf pos len (len * 257) s n key cur tb nxt

theorem subRun_size (ent : ByteArray → UInt64 → UInt64 → UInt64)
    (fil : ByteArray → UInt64 → UInt64 → UInt64 → UInt64 → UInt64 → ByteArray)
    (ptr : ByteArray → UInt64 → UInt64 → UInt64 → UInt64 → ByteArray)
    (hf : ∀ b base idx st c v, (fil b base idx st c v).size = b.size)
    (hp : ∀ b pos idx tb nxt, (ptr b pos idx tb nxt).size = b.size)
    (buf : ByteArray) (pos len la s n key cur tb nxt : UInt64) :
    (subRun ent fil ptr buf pos len la s n key cur tb nxt).size = buf.size := by
  fun_induction subRun ent fil ptr buf pos len la s n key cur tb nxt <;> simp_all +zetaDelta

@[simp] theorem subNarrow_size (buf : ByteArray) (pos len s n key cur tb nxt : UInt64) :
    (subNarrow buf pos len s n key cur tb nxt).size = buf.size := by
  unfold subNarrow
  exact subRun_size _ _ _ (by intros; simp) (by intros; simp) ..

@[simp] theorem subWide_size (mt : UInt64) (buf : ByteArray) (pos len s n key cur tb nxt : UInt64) :
    (subWide mt buf pos len s n key cur tb nxt).size = buf.size := by
  unfold subWide
  exact subRun_size _ _ _ (by intros; simp) (by intros; simp) ..

/-- The walk through the lists of lengths beyond the root, a length at a time. -/
def subWalk (wide mt pos maxl : UInt64) (buf : ByteArray) (len key cur tb nxt : UInt64)
    (h : ringAt.toNat ≤ buf.size) : ByteArray :=
  if hl : len < maxl then
    have : maxl.toNat - (len + 1).toNat < maxl.toNat - len.toNat := succ_nearer hl
    let l : UInt64 := len + 1
    let n := listCount buf l
    if n = 0 then subWalk wide mt pos maxl buf l key cur tb nxt h
    else
      let s := listHead buf l
      let buf' := if wide = 0 then subNarrow buf pos l s n key cur tb nxt else subWide mt buf pos l s n key cur tb nxt
      have h' : ringAt.toNat ≤ buf'.size := by
        simp only [buf']
        split <;> simpa using h
      let st := slot buf' Slot.walk h'
      subWalk wide mt pos maxl buf' l (key + n * ((0x10000 : UInt64) >>> l)) (st &&& 0xFFFF) (st >>> 32)
        ((st >>> 16) &&& 0xFFFF) h'
  else
    built wide buf pos rootCap nxt h
termination_by maxl.toNat - len.toNat

/-- The walk through the lists of lengths within the root, a length at a time. `key` is the next code, its first bit
highest of 8. -/
def rootWalk (wide mt pos maxl r : UInt64) (buf : ByteArray) (len key : UInt64) (h : ringAt.toNat ≤ buf.size) :
    ByteArray :=
  if hl : len < r then
    have : r.toNat - (len + 1).toNat < r.toNat - len.toNat := succ_nearer hl
    let l : UInt64 := len + 1
    let n := listCount buf l
    let kstep : UInt64 := (0x100 : UInt64) >>> l
    let buf' :=
      if n = 0 then buf
      else runIn wide mt pos buf 0 l ((1 : UInt64) <<< l) ((1 : UInt64) <<< (r - l)) kstep (listHead buf l) n key
    rootWalk wide mt pos maxl r buf' l (key + n * kstep) (by
      simp only [buf']
      split <;> simpa using h)
  else if r < maxl then
    subWalk wide mt pos maxl buf len (key <<< 8) 0 0 ((1 : UInt64) <<< r) h
  else
    built wide buf pos r ((1 : UInt64) <<< r) h
termination_by r.toNat - len.toNat

@[simp] theorem subWalk_size (wide mt pos maxl : UInt64) (buf : ByteArray) (len key cur tb nxt : UInt64)
    (h : ringAt.toNat ≤ buf.size) : (subWalk wide mt pos maxl buf len key cur tb nxt h).size = buf.size := by
  fun_induction subWalk wide mt pos maxl buf len key cur tb nxt h <;> simp_all +zetaDelta <;> split <;> simp

@[simp] theorem rootWalk_size (wide mt pos maxl r : UInt64) (buf : ByteArray) (len key : UInt64)
    (h : ringAt.toNat ≤ buf.size) : (rootWalk wide mt pos maxl r buf len key h).size = buf.size := by
  fun_induction rootWalk wide mt pos maxl r buf len key h <;> simp_all +zetaDelta <;> split <;> simp

/-- The table of the code whose symbols are in the lists, a complete code of two symbols or more, built at the
position in `Slot.tabNext`. Its root is as wide as the code's longest length, up to `rootCap` and no less than
`rmin`. Its name is left in `Slot.name`, and `Slot.tabNext` is moved past it. -/
def build (buf : ByteArray) (wide mt rmin : UInt64) (h : ringAt.toNat ≤ buf.size) : ByteArray :=
  let pos := slot buf Slot.tabNext h
  let maxl := maxLen buf 15
  let r0 := if maxl ≤ rootCap then maxl else rootCap
  let r := if r0 < rmin then rmin else r0
  rootWalk wide mt pos maxl r buf 0 0 h

/-- The table of a code of the one symbol `s`, read from no bits: every entry of a root of `rmin` bits. -/
def buildOne (buf : ByteArray) (s wide mt rmin : UInt64) (h : ringAt.toNat ≤ buf.size) : ByteArray :=
  let pos := slot buf Slot.tabNext h
  let buf1 := put wide mt buf pos 0 1 ((1 : UInt64) <<< rmin) s 0
  built wide buf1 pos rmin ((1 : UInt64) <<< rmin) (by sized h)

@[simp] theorem listsReset_size (buf : ByteArray) (h : ringAt.toNat ≤ buf.size) : (listsReset buf h).size = buf.size := by
  simp [listsReset]

@[simp] theorem build_size (buf : ByteArray) (wide mt rmin : UInt64) (h : ringAt.toNat ≤ buf.size) :
    (build buf wide mt rmin h).size = buf.size := by
  simp [build]

@[simp] theorem buildOne_size (buf : ByteArray) (s wide mt rmin : UInt64) (h : ringAt.toNat ≤ buf.size) :
    (buildOne buf s wide mt rmin h).size = buf.size := by
  simp [buildOne]
