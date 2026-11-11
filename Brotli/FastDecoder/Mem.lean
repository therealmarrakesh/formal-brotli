module

public import Brotli.FastDecoder.Layout

@[expose] public section

/-!
# The buffer's room and growth

The decoder allocates its buffer itself (`DESIGN.md` 5.2, 5.9, 9.9). An array's bytes exist only once written, so the
array is *extended* by writing zeros at its end; it is given its *room* (capacity) once, when the first meta-block
that produces output starts, so that extending it within the room moves nothing. What the stream asks for at any
point (its *demand*) is compared with the limit before a byte of it is written.

The array's size is kept in `Slot.size`, so that nothing but this module asks the array for it.
-/

namespace Brotli.FastDecoder


/-- How far past a need the array is extended, so that a header does not extend it at every table. -/
def growStep : UInt64 := 16384

/-- A block of zeros to extend an array from. -/
def zeroBlock : ByteArray := ⟨Array.replicate 65536 0⟩

/-- How much of the way from `at'` to `to` one block of zeros covers. -/
@[inline] def fillStep (at' to : UInt64) : UInt64 :=
  if to - at' < 65536 then to - at' else 65536

/-- A step is at least a byte and no more than what is left. -/
theorem fillStep_bounds {at' to : UInt64} (h : at' < to) :
    1 ≤ (fillStep at' to).toNat ∧ at'.toNat + (fillStep at' to).toNat ≤ to.toNat := by
  have hlt := UInt64.lt_iff_toNat_lt.mp h
  have hsub : (to - at').toNat = to.toNat - at'.toNat :=
    UInt64.toNat_sub_of_le _ _ (UInt64.le_iff_toNat_le.mpr (by omega))
  have e : (65536 : UInt64).toNat = 65536 := rfl
  unfold fillStep
  split
  · omega
  · rename_i hge
    have := UInt64.le_iff_toNat_le.mp (UInt64.not_lt.mp hge)
    omega

/-- The array extended with zeros from its end `at'` to `to`, a block at a time. -/
def zeroFill (buf : ByteArray) (at' to : UInt64) : ByteArray :=
  if h : at' < to then
    have : to.toNat - (at' + fillStep at' to).toNat < to.toNat - at'.toNat := by
      have hb := fillStep_bounds h
      have := to.toNat_lt
      rw [UInt64.toNat_add]
      omega
    zeroFill (zeroBlock.copySlice 0 buf at'.toNat (fillStep at' to).toNat) (at' + fillStep at' to) to
  else buf
termination_by to.toNat - at'.toNat

/-- Extending an array never makes it smaller. -/
theorem zeroFill_size_ge (buf : ByteArray) (at' to : UInt64) : buf.size ≤ (zeroFill buf at' to).size := by
  fun_induction zeroFill buf at' to with
  | case1 buf at' h _ ih => exact Nat.le_trans (copySlice_size_ge ..) ih
  | case2 => exact Nat.le_refl _

/-- A new array with room for `cap` bytes, holding what `buf` holds. -/
@[noinline, never_extract] def roomFor (buf : ByteArray) (cap : UInt64) : ByteArray :=
  buf.copySlice 0 (ByteArray.emptyWithCapacity cap.toNat) 0 buf.size

/-- The new array holds at least what the old one did. -/
theorem roomFor_front (buf : ByteArray) (cap : UInt64) (h : ringAt.toNat ≤ buf.size) :
    ringAt.toNat ≤ (roomFor buf cap).size := by
  unfold roomFor
  rw [ByteArray.copySlice_eq_append]
  simp only [ByteArray.size_append, ByteArray.size_extract]
  omega

/-- The demand a need stands for (5.9): the need itself; or, while a single meta-block's first tables stand `shift`
short of their place (`room = 2`), the need there. -/
@[inline] def demandOf (need room shift : UInt64) : UInt64 :=
  if room = 2 then need + shift else need

/-- The least power of two that is `n` or more, from `p` up (`p` a power of two). -/
def pow2From (n p : UInt64) : UInt64 :=
  if _h : 0 < p ∧ p < n ∧ p < 0x4000000000000000 then
    have : 0x8000000000000000 - (p <<< 1).toNat < 0x8000000000000000 - p.toNat := by
      have hp := UInt64.lt_iff_toNat_lt.mp _h.2.2
      have h0 := UInt64.lt_iff_toNat_lt.mp _h.1
      have e0 : (0 : UInt64).toNat = 0 := rfl
      have e : (0x4000000000000000 : UInt64).toNat = 0x4000000000000000 := rfl
      have e1 : (1 : UInt64).toNat % 64 = 1 := rfl
      rw [UInt64.toNat_shiftLeft, Nat.shiftLeft_eq, e1, Nat.pow_one]
      omega
    pow2From n (p <<< 1)
  else p
termination_by 0x8000000000000000 - p.toNat

/-- The lesser of two. -/
@[inline] def least (a b : UInt64) : UInt64 := if a < b then a else b

/-- `a` less `b`, and nothing where `b` is the greater. -/
@[inline] def less (a b : UInt64) : UInt64 := if a < b then 0 else a - b

/-- The step beyond a need: none while the header's first tables are in the front's array. -/
@[inline] def stepOf (room : UInt64) : UInt64 := if room = 2 then 0 else growStep

/-- The room's state once an array has been given a room: given, unless the first tables are still in the front's. -/
@[inline] def roomGiven (room : UInt64) : UInt64 := if room = 0 then 1 else room

/-- The array made to hold `need` bytes (5.9). The need is the stream's demand: over the limit, nothing is written
and the phase becomes the memory limit. Otherwise the array is extended with zeros to the need and a step beyond (no
further than the limit).

Where that passes the array's room, the array gets a larger one, as the reference decoder's ring does (9.13): a new
array of the least power of two that holds it, the old one's bytes copied, the old one freed. So a stream of many
meta-blocks starts with room for its first and at most doubles its way up, and its bytes are copied twice over at the
most in all. While the copy is made both arrays exist, and both are counted against the limit: the new room is no
more than the limit less the old. -/
@[noinline] def growTo (buf : ByteArray) (need : UInt64) (h : ringAt.toNat ≤ buf.size) : ByteArray :=
  let limit := slot buf Slot.limit h
  let room := slot buf Slot.room h
  if limit < demandOf need room (slot buf Slot.shift h) then setSlot buf Slot.phase Phase.memLimit h
  else
    let size := slot buf Slot.size h
    let cap := slot buf Slot.cap h
    -- the step beyond the need is for the array with the room: the front's array is extended only as far as needed
    let step : UInt64 := stepOf room
    let target : UInt64 := least limit (need + step)
    if target ≤ cap then
      let buf2 := zeroFill buf size target
      have h2 : ringAt.toNat ≤ buf2.size := Nat.le_trans h (zeroFill_size_ge ..)
      setSlot buf2 Slot.size target h2
    else
      let want := pow2From target 65536
      let spare : UInt64 := less limit cap
      let newcap : UInt64 := least want spare
      if newcap < target then setSlot buf Slot.phase Phase.memLimit h
      else
        let moves := slot buf Slot.moves h
        let buf2 := zeroFill (roomFor buf newcap) size target
        have h2 : ringAt.toNat ≤ buf2.size := Nat.le_trans (roomFor_front buf newcap h) (zeroFill_size_ge ..)
        let buf3 := setSlot buf2 Slot.size target h2
        let buf4 := setSlot buf3 Slot.cap newcap (by sized h2)
        let buf5 := setSlot buf4 Slot.moves (moves + 1) (by sized h2)
        setSlot buf5 Slot.room (roomGiven room) (by sized h2)

/-- Growing leaves the buffer its front. -/
theorem growTo_front (buf : ByteArray) (need : UInt64) (h : ringAt.toNat ≤ buf.size) :
    ringAt.toNat ≤ (growTo buf need h).size := by
  unfold growTo
  dsimp only
  split
  · simpa using h
  · split
    · simp only [setSlot_size]
      exact Nat.le_trans h (zeroFill_size_ge ..)
    · split
      · simpa using h
      · simp only [setSlot_size]
        exact Nat.le_trans (roomFor_front _ _ h) (zeroFill_size_ge ..)

/-! ### The room of a stream of one meta-block

Sized as the reference decoder sizes its tables: from the counts of codes the header declares, each code at the most
its table can take (9.12). The counts are known part of the way through the header; what the header has built by
then (the block-switch codes' tables, the context modes, the two maps) is small, and stands in the front's array
from `provAt`. Then the array with the room is made, exactly: the front, the ring's part for the meta-block's
output, the slack, those first tables moved to their place, and the bound for the rest. -/

/-- Where a single meta-block's header puts its first tables until the room is given. -/
def provAt : UInt64 := 18864

/-- A bound on what the rest of the header takes from the tables' next place, from the counts it has declared: the
lists of names; a table for each code, at the most a table of its alphabet takes (`alphabet + 376` entries: a root of
256 and the sub-tables' 120, the reference decoder's figure); the context tables, the rows and the finishing step's
scratch. -/
def tableBound (buf : ByteArray) (h : ringAt.toNat ≤ buf.size) : UInt64 :=
  let nl := slot buf Slot.cats h
  let ni := slot buf (Slot.cats + 48) h
  let nd := slot buf (Slot.cats + 96) h
  let tl := slot buf Slot.treesL h
  let td := slot buf Slot.treesD h
  let alphaD : UInt64 := (16 : UInt64) + slot buf Slot.ndirect h + ((48 : UInt64) <<< slot buf Slot.npostfix h)
  (((tl <<< (2 : UInt64)) + (7 : UInt64)) &&& ~~~(7 : UInt64)) + (ni <<< (3 : UInt64)) + (td <<< (3 : UInt64)) +
    tl * (1264 : UInt64) + ni * (8640 : UInt64) + td * ((alphaD + (376 : UInt64)) <<< (3 : UInt64)) +
    (nl <<< (13 : UInt64)) + (nd <<< (5 : UInt64)) + (256 : UInt64)

/-- A new array with room for `cap` bytes: the front of `buf`; zeros for the ring's part, as far as `base`; and
the `early` bytes of `buf` from `provAt`, moved to `base`. -/
@[noinline, never_extract] def roomMove (buf : ByteArray) (cap base early : UInt64) : ByteArray :=
  let nb := buf.copySlice 0 (ByteArray.emptyWithCapacity cap.toNat) 0 ringAt.toNat
  let nb := zeroFill nb ringAt base
  buf.copySlice provAt.toNat nb base.toNat early.toNat

/-- The new array holds the front. -/
theorem roomMove_front (buf : ByteArray) (cap base early : UInt64) (h : ringAt.toNat ≤ buf.size) :
    ringAt.toNat ≤ (roomMove buf cap base early).size := by
  unfold roomMove
  refine Nat.le_trans ?_ (copySlice_size_ge ..)
  refine Nat.le_trans ?_ (zeroFill_size_ge ..)
  rw [ByteArray.copySlice_eq_append]
  simp only [ByteArray.size_append, ByteArray.size_extract]
  omega

/-- A position in the header's first tables, moved by `shift` with them. -/
@[inline] def moved (buf : ByteArray) (off shift : UInt64) (h : ringAt.toNat ≤ buf.size)
    (ho : off.toNat + 8 ≤ slowSize.toNat := by decide) : ByteArray :=
  setSlot buf off (slot buf off h ho + shift) h ho

@[simp] theorem moved_size (buf : ByteArray) (off shift : UInt64) (h : ringAt.toNat ≤ buf.size)
    (ho : off.toNat + 8 ≤ slowSize.toNat) : (moved buf off shift h ho).size = buf.size := by
  simp [moved]

/-- The array with exactly the room `need`, made and extended to it, and the positions the header has kept (the
tables' next place, the modes, the two maps, the block-switch codes' tables) moved by `shift` with the tables. -/
def roomSet (buf : ByteArray) (cap base early shift : UInt64) (h : ringAt.toNat ≤ buf.size) : ByteArray :=
  let buf1 := roomMove buf cap base early
  have h1 : ringAt.toNat ≤ buf1.size := roomMove_front buf cap base early h
  let buf := moved buf1 Slot.tabNext shift h1
  let buf := moved buf Slot.modesAt shift (by sized h1)
  let buf := moved buf Slot.lmapAt shift (by sized h1)
  let buf := moved buf Slot.dmapAt shift (by sized h1)
  have h2 : ringAt.toNat ≤ buf.size := by sized h1
  -- the three categories' type and count codes' tables: `Slot.cats` (608) and 48 a category, at 8 and 16
  let buf := moved buf 616 shift h2
  let buf := moved buf 624 shift (by sized h2)
  let buf := moved buf 664 shift (by sized h2)
  let buf := moved buf 672 shift (by sized h2)
  have h3 : ringAt.toNat ≤ buf.size := by sized h2
  let buf := moved buf 712 shift h3
  let buf := moved buf 720 shift (by sized h3)
  let buf := setSlot buf Slot.size (base + early) (by sized h3)
  let buf := setSlot buf Slot.cap cap (by sized h3)
  setSlot buf Slot.room 1 (by sized h3)
/-- The room of a stream of one meta-block, given when its header has declared its counts of codes. What the stream
has asked for so far (the ring's part and the header's first tables) is compared with the limit. The array made then
(`roomSet`) has room for that and the bound on the header's other tables, and no more than the limit; the room is
only reserved, and the array is extended into it as the tables are built (`growTo`), each need compared with the
limit as it comes. -/
@[noinline] def giveRoom (buf : ByteArray) (h : ringAt.toNat ≤ buf.size) : ByteArray :=
  let limit := slot buf Slot.limit h
  let shift := slot buf Slot.shift h
  let early : UInt64 := slot buf Slot.tabNext h - provAt
  let base : UInt64 := provAt + shift
  let bound : UInt64 := base + early + tableBound buf h + growStep + growStep
  if limit < base + early then setSlot buf Slot.phase Phase.memLimit h
  else
    let cap := pow2From bound 65536
    roomSet buf (if limit < cap then limit else cap) base early shift h
