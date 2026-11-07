module

public import Brotli.Decoder.CopyRing
public import Brotli.Decoder.StepDistance
public import Brotli.Decoder.Loop
public import Brotli.Decoder.FastLoop

/-!
# The compiled command loop

`runCmdE` is `runCmd` as the compiler runs it: one loop with the whole command state in local variables, so that no
step rebuilds a record. It does exactly what `runCmd` does, step for step: the same refills, reads and writes, in the
same order (AGENTS.md, design rule 1). It takes what the stream's relation gives of the state (`KInv`, `LoopInv.lean`)
and carries it through every step as a proof, so that it tests none of it at run time. `runCmdP` is `runCmd` taking
that proof, `runCmdP_csimp` proves `runCmdE` equal to it, and every proof is about `runCmd`.

`kstep` is one step, ending in a continuation: `contC` takes the record the next literal run builds its result in and
the state's fields, and goes on; `exit` takes the state as a record and stops. It is inlined into `runCmdK`, whose
`contC` is its own recursive call, so every step ends in a jump. `kstep_eq` proves a step equal to `stepCmd` on the
record built from the fields (`mkCmd`), for a continuation that doesn't depend on the record it is handed.
-/

namespace Brotli.Decoder

open Brotli.Spec

/-! ### A literal run that builds its result in a record it is given

The literal run's result is built in a record the loop hands it, so that the run doesn't allocate: the record's memory
is reused when it is held once. `spare` is never written, which is what makes the exit read the old record. The run is
proved equal to the plain one, with the given record's spare field kept. -/

/-- The record a literal run builds its result in: the run's fields, and a spare one. -/
structure RunOut where
  word : UInt64
  count : UInt64
  pos : USize
  wpos : USize
  ring : ByteArray
  p1 : UInt8
  p2 : UInt8
  left : USize
  spare : UInt8

/-- `literalRun`, building its result in `cell`. -/
def literalRunC (cell : RunOut) {nTrees : Nat} {arena litBase lMap : ByteArray} (C : LitChecked arena litBase lMap nTrees)
    (a : ByteArray) (stop : USize) (hs : stop.toNat ≤ a.size) (mapBase modeOff mask : USize) (k : Nat)
    (hmb : mapBase.toNat + 64 ≤ lMap.size) (hm : modeOff.toNat + 512 ≤ 2048) (hd : modeOff.toNat % 512 = 0)
    (hmask : mask.toNat = 2 ^ k - 1) (hk : k ≤ 24) (n : USize) (word count : UInt64) (pos wpos : USize) (ring : ByteArray)
    (p1 p2 : UInt8) (hp : pos.toNat ≤ stop.toNat) (hw : (BitBuffer.mk word count).Wf) (hsize : ring.size = 2 ^ k)
    (hwp : wpos.toNat < 2 ^ k) : RunOut :=
  if hn : n = 0 then
    { cell with word := word, count := count, pos := pos, wpos := wpos, ring := ring, p1 := p1, p2 := p2, left := 0 }
  else
    let r := refill word count a pos stop hs hp
    let rw := r.word
    let rc := r.count
    let rp := r.pos
    have hspec := refill_spec hs hp hw
    let cid := cidFast modeOff p1 p2 hm
    have hcid : cid.toNat < 64 := cid_lt hm hd
    have hi : (mapIndex mapBase cid).toNat < lMap.size := by
      rw [mapIndex_toNat (by have := C.map32; omega)]
      omega
    let tree := lMap.uget (mapIndex mapBase cid) hi
    have htree : tree.toNat < nTrees := C.treeLt _ hi
    have hb : 4 * tree.toNat + 4 ≤ litBase.size := by
      rw [C.baseSize]
      omega
    let base := treeBase litBase tree hb C.base32
    have hfit : TableFits arena base.toNat := by
      rw [treeBase_toNat]
      exact C.fits _ htree
    let v := lookup arena base rw hfit C.arena32
    let l := v &&& 15
    if hl : l ≤ rc then
      let byte := (v >>> 4).toUInt8
      have hl63 : l.toNat < 64 := by
        have : (v &&& 15).toNat = v.toNat % 16 := by
          rw [UInt64.toNat_and]
          exact Nat.and_two_pow_sub_one_eq_mod v.toNat 4
        show (v &&& 15).toNat < 64
        omega
      have hr : wpos.toNat < ring.size := by omega
      let ring' := ringWrite ring wpos byte hr
      have hsize' : ring'.size = 2 ^ k := (size_ringWrite ring wpos byte hr).trans hsize
      have hnext : (ringNext wpos mask).toNat < 2 ^ k := by
        unfold ringNext
        rw [USize.toNat_and, hmask, Nat.and_two_pow_sub_one_eq_mod]
        exact Nat.mod_lt _ (Nat.two_pow_pos _)
      let b := (BitBuffer.mk rw rc).drop l
      literalRunC cell C a stop hs mapBase modeOff mask k hmb hm hd hmask hk (n - USize.ofNat 1) b.word b.count rp
        (ringNext wpos mask) ring' byte p1 hspec.2.2.1 (BitBuffer.drop_wf hspec.1 hl63 (UInt64.le_iff_toNat_le.mp hl))
        hsize' hnext
    else { cell with word := rw, count := rc, pos := rp, wpos := wpos, ring := ring, p1 := p1, p2 := p2, left := n }
termination_by n.toNat
decreasing_by
  have := usize_pred hn
  have := usize_ne hn
  omega

/-- A literal run's result in a record. -/
@[inline] def litInto (cell : RunOut) (r : LitRun) : RunOut :=
  { cell with
    word := r.word, count := r.count, pos := r.pos, wpos := r.wpos, ring := r.ring, p1 := r.p1, p2 := r.p2
    left := r.left }

theorem literalRunC_eq' (cell : RunOut) {nTrees : Nat} {arena litBase lMap : ByteArray}
    (C : LitChecked arena litBase lMap nTrees) (a : ByteArray) (stop : USize) (hs : stop.toNat ≤ a.size)
    (mapBase modeOff mask : USize) (k : Nat) (hmb : mapBase.toNat + 64 ≤ lMap.size) (hm : modeOff.toNat + 512 ≤ 2048)
    (hd : modeOff.toNat % 512 = 0) (hmask : mask.toNat = 2 ^ k - 1) (hk : k ≤ 24) :
    ∀ (N : Nat) (n : USize) (word count : UInt64) (pos wpos : USize) (ring : ByteArray) (p1 p2 : UInt8)
      (hp : pos.toNat ≤ stop.toNat) (hw : (BitBuffer.mk word count).Wf) (hsize : ring.size = 2 ^ k)
      (hwp : wpos.toNat < 2 ^ k), n.toNat = N →
      literalRunC cell C a stop hs mapBase modeOff mask k hmb hm hd hmask hk n word count pos wpos ring p1 p2 hp hw hsize
          hwp =
        litInto cell (literalRun C a stop hs mapBase modeOff mask k hmb hm hd hmask hk n word count pos wpos ring p1 p2 hp
          hw hsize hwp) := by
  intro N
  induction N with
  | zero =>
    intro n word count pos wpos ring p1 p2 hp hw hsize hwp hN
    have hn : n = 0 := usize_zero hN
    rw [literalRunC, literalRun, dite_eq_left hn, dite_eq_left hn]
    rfl
  | succ N ih =>
    intro n word count pos wpos ring p1 p2 hp hw hsize hwp hN
    have hn : n ≠ 0 := fun e => by rw [e] at hN; exact Nat.succ_ne_zero _ hN.symm
    rw [literalRunC, literalRun, dite_eq_right hn, dite_eq_right hn]
    dsimp only
    -- one `split` takes both sides' test, which is the same term
    split
    · apply ih
      rw [usize_pred hn]
      omega
    · rfl

/-- The literal run on a record is the literal run, with the record's spare field kept. -/
theorem literalRunC_eq (cell : RunOut) {nTrees : Nat} {arena litBase lMap : ByteArray}
    (C : LitChecked arena litBase lMap nTrees) (a : ByteArray) (stop : USize) (hs : stop.toNat ≤ a.size)
    (mapBase modeOff mask : USize) (k : Nat) (hmb : mapBase.toNat + 64 ≤ lMap.size) (hm : modeOff.toNat + 512 ≤ 2048)
    (hd : modeOff.toNat % 512 = 0) (hmask : mask.toNat = 2 ^ k - 1) (hk : k ≤ 24) (n : USize) (word count : UInt64)
    (pos wpos : USize) (ring : ByteArray) (p1 p2 : UInt8) (hp : pos.toNat ≤ stop.toNat)
    (hw : (BitBuffer.mk word count).Wf) (hsize : ring.size = 2 ^ k) (hwp : wpos.toNat < 2 ^ k) :
    literalRunC cell C a stop hs mapBase modeOff mask k hmb hm hd hmask hk n word count pos wpos ring p1 p2 hp hw hsize
        hwp =
      litInto cell (literalRun C a stop hs mapBase modeOff mask k hmb hm hd hmask hk n word count pos wpos ring p1 p2 hp
        hw hsize hwp) :=
  literalRunC_eq' cell C a stop hs mapBase modeOff mask k hmb hm hd hmask hk _ n word count pos wpos ring p1 p2 hp hw
    hsize hwp rfl

/-- `literalRunT`, building its result in `cell`. -/
def literalRunCT (cell : RunOut) (arena : ByteArray) (h32 : arena.size < 2 ^ 32) (base : USize)
    (hfit : TableFits arena base.toNat) (a : ByteArray) (stop : USize) (hs : stop.toNat ≤ a.size) (mask : USize) (k : Nat)
    (hmask : mask.toNat = 2 ^ k - 1) (n : USize) (word count : UInt64) (pos wpos : USize) (ring : ByteArray) (p1 p2 : UInt8)
    (hp : pos.toNat ≤ stop.toNat) (hw : (BitBuffer.mk word count).Wf) (hsize : ring.size = 2 ^ k)
    (hwp : wpos.toNat < 2 ^ k) : RunOut :=
  if hn : n = 0 then
    { cell with word := word, count := count, pos := pos, wpos := wpos, ring := ring, p1 := p1, p2 := p2, left := 0 }
  else
    let r := refill word count a pos stop hs hp
    let rw := r.word
    let rc := r.count
    let rp := r.pos
    have hspec := refill_spec hs hp hw
    let v := lookup arena base rw hfit h32
    let l := v &&& 15
    if hl : l ≤ rc then
      let byte := (v >>> 4).toUInt8
      have hl63 : l.toNat < 64 := by
        have : (v &&& 15).toNat = v.toNat % 16 := by
          rw [UInt64.toNat_and]
          exact Nat.and_two_pow_sub_one_eq_mod v.toNat 4
        show (v &&& 15).toNat < 64
        omega
      have hr : wpos.toNat < ring.size := by omega
      let ring' := ringWrite ring wpos byte hr
      have hsize' : ring'.size = 2 ^ k := (size_ringWrite ring wpos byte hr).trans hsize
      have hnext : (ringNext wpos mask).toNat < 2 ^ k := by
        unfold ringNext
        rw [USize.toNat_and, hmask, Nat.and_two_pow_sub_one_eq_mod]
        exact Nat.mod_lt _ (Nat.two_pow_pos _)
      let b := (BitBuffer.mk rw rc).drop l
      literalRunCT cell arena h32 base hfit a stop hs mask k hmask (n - USize.ofNat 1) b.word b.count rp (ringNext wpos mask)
        ring' byte p1 hspec.2.2.1 (BitBuffer.drop_wf hspec.1 hl63 (UInt64.le_iff_toNat_le.mp hl)) hsize' hnext
    else { cell with word := rw, count := rc, pos := rp, wpos := wpos, ring := ring, p1 := p1, p2 := p2, left := n }
termination_by n.toNat
decreasing_by
  have := usize_pred hn
  have := usize_ne hn
  omega

theorem literalRunCT_eq' (cell : RunOut) (arena : ByteArray) (h32 : arena.size < 2 ^ 32) (base : USize)
    (hfit : TableFits arena base.toNat) (a : ByteArray) (stop : USize) (hs : stop.toNat ≤ a.size) (mask : USize) (k : Nat)
    (hmask : mask.toNat = 2 ^ k - 1) :
    ∀ (N : Nat) (n : USize) (word count : UInt64) (pos wpos : USize) (ring : ByteArray) (p1 p2 : UInt8)
      (hp : pos.toNat ≤ stop.toNat) (hw : (BitBuffer.mk word count).Wf) (hsize : ring.size = 2 ^ k)
      (hwp : wpos.toNat < 2 ^ k), n.toNat = N →
      literalRunCT cell arena h32 base hfit a stop hs mask k hmask n word count pos wpos ring p1 p2 hp hw hsize hwp =
        litInto cell (literalRunT arena h32 base hfit a stop hs mask k hmask n word count pos wpos ring p1 p2 hp hw hsize
          hwp) := by
  intro N
  induction N with
  | zero =>
    intro n word count pos wpos ring p1 p2 hp hw hsize hwp hN
    have hn : n = 0 := usize_zero hN
    rw [literalRunCT, literalRunT, dite_eq_left hn, dite_eq_left hn]
    rfl
  | succ N ih =>
    intro n word count pos wpos ring p1 p2 hp hw hsize hwp hN
    have hn : n ≠ 0 := fun e => by rw [e] at hN; exact Nat.succ_ne_zero _ hN.symm
    rw [literalRunCT, literalRunT, dite_eq_right hn, dite_eq_right hn]
    dsimp only
    -- one `split` takes both sides' test, which is the same term
    split
    · apply ih
      rw [usize_pred hn]
      omega
    · rfl

/-- The literal run on a record for block type `t`, selected as `literalRunS` selects. -/
@[inline] def literalRunCS (cell : RunOut) (H : Hdr) (t : UInt64) (ht : t.toNat < H.nL.toNat) (a : ByteArray)
    (stop : USize) (hs : stop.toNat ≤ a.size) (modeOff mask : USize) (k : Nat) (hm : modeOff.toNat + 512 ≤ 2048)
    (hd : modeOff.toNat % 512 = 0) (hmask : mask.toNat = 2 ^ k - 1) (hk : k ≤ 24) (n : USize) (word count : UInt64)
    (pos wpos : USize) (ring : ByteArray) (p1 p2 : UInt8) (hp : pos.toNat ≤ stop.toNat) (hw : (BitBuffer.mk word count).Wf)
    (hsize : ring.size = 2 ^ k) (hwp : wpos.toNat < 2 ^ k) : RunOut :=
  if hb : trivBase H t ht = 4294967295 then
    literalRunC cell H.lit a stop hs (t <<< 6).toUSize modeOff mask k (mapBase_le ht) hm hd hmask hk n word count pos wpos
      ring p1 p2 hp hw hsize hwp
  else
    literalRunCT cell H.arena H.lit.arena32 (trivBase H t ht).toUSize (trivBase_spec ht hb).1 a stop hs mask k hmask n word
      count pos wpos ring p1 p2 hp hw hsize hwp

/-- The selected run on a record is the selected run, with the record's spare field kept. -/
theorem literalRunCS_eq (cell : RunOut) (H : Hdr) (t : UInt64) (ht : t.toNat < H.nL.toNat) (a : ByteArray)
    (stop : USize) (hs : stop.toNat ≤ a.size) (modeOff mask : USize) (k : Nat) (hm : modeOff.toNat + 512 ≤ 2048)
    (hd : modeOff.toNat % 512 = 0) (hmask : mask.toNat = 2 ^ k - 1) (hk : k ≤ 24) (n : USize) (word count : UInt64)
    (pos wpos : USize) (ring : ByteArray) (p1 p2 : UInt8) (hp : pos.toNat ≤ stop.toNat) (hw : (BitBuffer.mk word count).Wf)
    (hsize : ring.size = 2 ^ k) (hwp : wpos.toNat < 2 ^ k) :
    literalRunCS cell H t ht a stop hs modeOff mask k hm hd hmask hk n word count pos wpos ring p1 p2 hp hw hsize hwp =
      litInto cell (literalRunS H t ht a stop hs modeOff mask k hm hd hmask hk n word count pos wpos ring p1 p2 hp hw hsize
        hwp) := by
  unfold literalRunCS literalRunS
  by_cases hb : trivBase H t ht = 4294967295
  · rw [dite_eq_left hb, dite_eq_left hb]
    exact literalRunC_eq _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
  · rw [dite_eq_right hb, dite_eq_right hb]
    exact literalRunCT_eq' _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ rfl

/-- What a literal run on a record leaves: the window's size, the write position in it, the bits well formed and the
position within the chunk. -/
def LitInvC (k : Nat) (stop : USize) (r : RunOut) : Prop :=
  r.ring.size = 2 ^ k ∧ r.wpos.toNat < 2 ^ k ∧ (BitBuffer.mk r.word r.count).Wf ∧ r.pos.toNat ≤ stop.toNat

theorem literalRunC_inv (cell : RunOut) {nTrees : Nat} {arena litBase lMap : ByteArray}
    (C : LitChecked arena litBase lMap nTrees) (a : ByteArray) (stop : USize) (hs : stop.toNat ≤ a.size)
    (mapBase modeOff mask : USize) (k : Nat) (hmb : mapBase.toNat + 64 ≤ lMap.size) (hm : modeOff.toNat + 512 ≤ 2048)
    (hd : modeOff.toNat % 512 = 0) (hmask : mask.toNat = 2 ^ k - 1) (hk : k ≤ 24) (n : USize) (word count : UInt64)
    (pos wpos : USize) (ring : ByteArray) (p1 p2 : UInt8) (hp : pos.toNat ≤ stop.toNat)
    (hw : (BitBuffer.mk word count).Wf) (hsize : ring.size = 2 ^ k) (hwp : wpos.toNat < 2 ^ k) :
    LitInvC k stop (literalRunC cell C a stop hs mapBase modeOff mask k hmb hm hd hmask hk n word count pos wpos ring p1
      p2 hp hw hsize hwp) := by
  rw [literalRunC_eq]
  exact literalRun_inv C a stop hs mapBase modeOff mask k hmb hm hd hmask hk n word count pos wpos ring p1 p2 hp hw hsize
    hwp

theorem literalRunCS_inv (cell : RunOut) (H : Hdr) (t : UInt64) (ht : t.toNat < H.nL.toNat) (a : ByteArray)
    (stop : USize) (hs : stop.toNat ≤ a.size) (modeOff mask : USize) (k : Nat) (hm : modeOff.toNat + 512 ≤ 2048)
    (hd : modeOff.toNat % 512 = 0) (hmask : mask.toNat = 2 ^ k - 1) (hk : k ≤ 24) (n : USize) (word count : UInt64)
    (pos wpos : USize) (ring : ByteArray) (p1 p2 : UInt8) (hp : pos.toNat ≤ stop.toNat) (hw : (BitBuffer.mk word count).Wf)
    (hsize : ring.size = 2 ^ k) (hwp : wpos.toNat < 2 ^ k) :
    LitInvC k stop (literalRunCS cell H t ht a stop hs modeOff mask k hm hd hmask hk n word count pos wpos ring p1 p2 hp hw
      hsize hwp) := by
  rw [literalRunCS_eq, literalRunS_eq]
  exact literalRun_inv H.lit a stop hs _ modeOff mask k _ hm hd hmask hk n word count pos wpos ring p1 p2 hp hw hsize hwp

/-- The command state from its fields. -/
def mkCmd (word count : UInt64) (ring : ByteArray) (wpos pend cap written : USize) (p1 p2 : UInt8)
    (remaining iCount lCount dCount : UInt64) (flags : Flags)
    (iCur iPrev lCur lPrev dCur dPrev d0 d1 d2 d3 code ilen clen copyBits copyBase dist : UInt64)
    (wordBuf : ByteArray) (wordPos : USize) (tag : Tag) (left : UInt64) (pos : USize) (status : StepStatus) : Cmd :=
  ⟨word, count, ring, wpos, pend, cap, written, p1, p2, remaining, iCount, lCount, dCount, flags,
    ⟨iCur, iPrev, lCur, lPrev, dCur, dPrev, d0, d1, d2, d3, code, ilen, clen, copyBits, copyBase, dist, wordBuf, wordPos⟩,
    tag, left, pos, status⟩

/-- A step's continuation: the state's fields and the position. -/
abbrev KCont (α : Type) : Type :=
  UInt64 → UInt64 → ByteArray → USize → USize → USize → USize → UInt8 → UInt8 → UInt64 → UInt64 → UInt64 → UInt64 →
    Flags → UInt64 → UInt64 → UInt64 → UInt64 → UInt64 → UInt64 → UInt64 → UInt64 → UInt64 → UInt64 → UInt64 →
    UInt64 → UInt64 → UInt64 → UInt64 → UInt64 → ByteArray → USize → Tag → UInt64 → USize → α

/-- A step's continuation in the loop: the state's fields, the position, and what the loop knows of them. -/
abbrev KContP (H : Hdr) (k stop : USize) (α : Type) : Type :=
  (word count : UInt64) → (ring : ByteArray) → (wpos pend cap written : USize) → (p1 p2 : UInt8) →
    (remaining iCount lCount dCount : UInt64) → (flags : Flags) →
    (iCur iPrev lCur lPrev dCur dPrev d0 d1 d2 d3 code ilen clen copyBits copyBase dist : UInt64) →
    (wordBuf : ByteArray) → (wordPos : USize) → (tag : Tag) → (left : UInt64) → (pos : USize) →
    KInv H k stop word count ring wpos written iCur iPrev lCur lPrev dCur dPrev copyBits dist wordBuf wordPos tag pos → α

/-- A step's continuation in the loop, which also takes the record the next literal run builds its result in. -/
abbrev KContC (H : Hdr) (k stop : USize) (α : Type) : Type := RunOut → KContP H k stop α

/-- How a step's result goes on: with the record's fields if it moved on, otherwise with the record. -/
def kcase {α : Type} (cont : KCont α) (exit : Cmd → α) (r : Cmd) : α :=
  if r.status = .next then
    cont r.word r.count r.ring r.wpos r.pend r.cap r.written r.p1 r.p2 r.remaining r.iCount r.lCount r.dCount r.flags
      r.ext.iCur r.ext.iPrev r.ext.lCur r.ext.lPrev r.ext.dCur r.ext.dPrev r.ext.d0 r.ext.d1 r.ext.d2 r.ext.d3
      r.ext.code r.ext.ilen r.ext.clen r.ext.copyBits r.ext.copyBase r.ext.dist r.ext.wordBuf r.ext.wordPos r.tag r.left
      r.pos
  else exit r

/-- `applyDistance` on the fields. -/
@[inline] def kapply {α : Type} {H : Hdr} {k stop : USize} (cont : KContP H k stop α) (exit : Cmd → α)
    (word count : UInt64) (ring : ByteArray) (wpos pend cap written : USize) (p1 p2 : UInt8)
    (remaining iCount lCount dCount : UInt64) (flags : Flags)
    (iCur iPrev lCur lPrev dCur dPrev d0 d1 d2 d3 code ilen clen copyBits copyBase dist : UInt64)
    (wordBuf : ByteArray) (wordPos : USize) (tag : Tag) (left : UInt64) (pos : USize) (dcode d : UInt64) (hd : d ≠ 0)
    (hki : KInv H k stop word count ring wpos written iCur iPrev lCur lPrev dCur dPrev copyBits dist wordBuf wordPos tag
      pos) : α :=
  if hwd : written.toUInt64 < d then
    if h : dictValid clen (d - (written.toUInt64 + 1)) then
      let wb := dictBuild clen (d - (written.toUInt64 + 1)) h
      if remaining < wb.usize.toUInt64 then
        exit (mkCmd word count ring wpos pend cap written p1 p2 remaining iCount lCount dCount flags iCur iPrev lCur lPrev
          dCur dPrev d0 d1 d2 d3 code ilen clen copyBits copyBase dist wordBuf wordPos tag left pos .bad)
      else
        cont word count ring wpos pend cap written p1 p2 (remaining - wb.usize.toUInt64) iCount lCount dCount flags iCur
          iPrev lCur lPrev dCur dPrev d0 d1 d2 d3 code ilen clen copyBits copyBase dist wb 0 .word left pos
          (hki.retag ⟨Nat.zero_le _, dictBuild_le h⟩)
    else
      exit (mkCmd word count ring wpos pend cap written p1 p2 remaining iCount lCount dCount flags iCur iPrev lCur lPrev
        dCur dPrev d0 d1 d2 d3 code ilen clen copyBits copyBase dist wordBuf wordPos tag left pos .bad)
  else if remaining < clen then
    exit (mkCmd word count ring wpos pend cap written p1 p2 remaining iCount lCount dCount flags iCur iPrev lCur lPrev
      dCur dPrev d0 d1 d2 d3 code ilen clen copyBits copyBase dist wordBuf wordPos tag left pos .bad)
  else if dcode = 0 then
    cont word count ring wpos pend cap written p1 p2 (remaining - clen) iCount lCount dCount flags iCur iPrev lCur lPrev
      dCur dPrev d0 d1 d2 d3 code ilen clen copyBits copyBase d wordBuf wordPos .copy clen pos
      (hki.retag (copy_dist_ok hd hwd hki.written))
  else
    cont word count ring wpos pend cap written p1 p2 (remaining - clen) iCount lCount dCount flags iCur iPrev lCur lPrev
      dCur dPrev d d0 d1 d2 code ilen clen copyBits copyBase d wordBuf wordPos .copy clen pos
      (hki.retag (copy_dist_ok hd hwd hki.written))

/-- One step of the command loop on the fields: `stepCmd`, ending in a continuation. -/
@[inline] def kstep {α : Type} (H : Hdr) (k : USize) (a : ByteArray) (stop : USize) (hs : stop.toNat ≤ a.size)
    (contC : KContC H k stop α) (exit : Cmd → α)
    (word count : UInt64) (ring : ByteArray) (wpos pend cap written : USize) (p1 p2 : UInt8)
    (remaining iCount lCount dCount : UInt64) (flags : Flags)
    (iCur iPrev lCur lPrev dCur dPrev d0 d1 d2 d3 code ilen clen copyBits copyBase dist : UInt64)
    (wordBuf : ByteArray) (wordPos : USize) (tag : Tag) (left : UInt64) (pos : USize) (cell : RunOut)
    (hinv : KInv H k stop word count ring wpos written iCur iPrev lCur lPrev dCur dPrev copyBits dist wordBuf wordPos tag pos) : α :=
  let cont := contC cell
    let rf := refill word count a pos stop hs hinv.pos
    let w := rf.word
    let c := rf.count
    let p := rf.pos
    have hr := hinv.refill hs hinv.pos
    match tag with
    | .command =>
      if remaining = 0 then
        exit (mkCmd w c ring wpos pend cap written p1 p2 remaining iCount lCount dCount flags iCur iPrev lCur lPrev
          dCur dPrev d0 d1 d2 d3 code ilen clen copyBits copyBase dist wordBuf wordPos .command left p .done)
      else if iCount = 0 then
        if hn : 2 ≤ H.nI then
          let hn' := UInt64.le_iff_toNat_le.mp hn
          let r := blockSwitch H.arena H.lit.arena32 H.baseTI H.baseCI (H.swI hn').1 (H.swI hn').2 H.nI iCur iPrev w c
          match hst : r.status with
          | .ok =>
            cont r.word r.count ring wpos pend cap written p1 p2 remaining (r.blockCount - 1) lCount dCount
              { flags with
                fI0 := markWord flags.fI0 r.cur 0, fI1 := markWord flags.fI1 r.cur 1, fI2 := markWord flags.fI2 r.cur 2
                fI3 := markWord flags.fI3 r.cur 3 }
              r.cur iCur lCur lPrev dCur dPrev d0 d1 d2 d3 code ilen clen copyBits copyBase dist wordBuf wordPos
              .insertCopy left p (hr.swI hn hst trivial)
          | .short =>
            exit (mkCmd w c ring wpos pend cap written p1 p2 remaining iCount lCount dCount flags iCur iPrev lCur lPrev
              dCur dPrev d0 d1 d2 d3 code ilen clen copyBits copyBase dist wordBuf wordPos .command left p .needsInput)
          | .bad =>
            exit (mkCmd w c ring wpos pend cap written p1 p2 remaining iCount lCount dCount flags iCur iPrev lCur lPrev
              dCur dPrev d0 d1 d2 d3 code ilen clen copyBits copyBase dist wordBuf wordPos .command left p .bad)
        else
          exit (mkCmd w c ring wpos pend cap written p1 p2 remaining iCount lCount dCount flags iCur iPrev lCur lPrev
            dCur dPrev d0 d1 d2 d3 code ilen clen copyBits copyBase dist wordBuf wordPos .command left p .bad)
      else
        cont w c ring wpos pend cap written p1 p2 remaining (iCount - 1) lCount dCount flags iCur iPrev lCur lPrev dCur
          dPrev d0 d1 d2 d3 code ilen clen copyBits copyBase dist wordBuf wordPos .insertCopy left p
          (hr.retag trivial)
    | .insertCopy =>
      have ht' : iCur.toNat < H.nI.toNat := hr.iCur
      have hb : 4 * iCur.toNat + 4 ≤ H.icBase.size := by
        rw [H.icSize]
        omega
      let v := lookup H.arena (tableBase H.icBase iCur hb H.ic32) w
        (by rw [tableBase_toNat]; exact H.icFits _ ht') H.lit.arena32
      if hwb : wordBits v ≤ c then
        have hc : wordSym v < 704 := ic_sym hr.hdr ht' hwb
        let b1 := (BitBuffer.mk w c).drop (wordBits v)
        let row := insertRow (wordSym v) (lt704 hc)
        if hrb : rowBits row ≤ b1.count then
          let b2 := b1.drop (rowBits row)
          let cr := copyRow (wordSym v) (lt704 hc)
          cont b2.word b2.count ring wpos pend cap written p1 p2 remaining iCount lCount dCount flags iCur iPrev lCur
            lPrev dCur dPrev d0 d1 d2 d3 (wordSym v) (rowBase row + b1.peek (rowBits row)) clen (rowBits cr)
            (rowBase cr) dist wordBuf wordPos .copyLength left p
            ((hr.drop (wordBits_lt v) hwb hr.tagged).drop (insertRow_bits (lt704 hc)) hrb
              (copyRow_bits (lt704 hc)))
        else
          exit (mkCmd w c ring wpos pend cap written p1 p2 remaining iCount lCount dCount flags iCur iPrev lCur lPrev
            dCur dPrev d0 d1 d2 d3 code ilen clen copyBits copyBase dist wordBuf wordPos .insertCopy left p
            .needsInput)
      else
        exit (mkCmd w c ring wpos pend cap written p1 p2 remaining iCount lCount dCount flags iCur iPrev lCur lPrev
          dCur dPrev d0 d1 d2 d3 code ilen clen copyBits copyBase dist wordBuf wordPos .insertCopy left p .needsInput)
    | .copyLength =>
      if remaining < ilen then
        exit (mkCmd w c ring wpos pend cap written p1 p2 remaining iCount lCount dCount flags iCur iPrev lCur lPrev
          dCur dPrev d0 d1 d2 d3 code ilen clen copyBits copyBase dist wordBuf wordPos .copyLength left p .bad)
      else if hcb : copyBits ≤ c then
        let b := BitBuffer.mk w c
        let b1 := b.drop copyBits
        cont b1.word b1.count ring wpos pend cap written p1 p2 remaining iCount lCount dCount flags iCur iPrev lCur lPrev
          dCur dPrev d0 d1 d2 d3 code ilen (copyBase + b.peek copyBits) copyBits copyBase dist wordBuf wordPos .literals
          ilen p (hr.drop (by have : copyBits.toNat ≤ 24 := hr.tagged; omega) hcb trivial)
      else
        exit (mkCmd w c ring wpos pend cap written p1 p2 remaining iCount lCount dCount flags iCur iPrev lCur lPrev
          dCur dPrev d0 d1 d2 d3 code ilen clen copyBits copyBase dist wordBuf wordPos .copyLength left p .needsInput)
    | .literals =>
      if left = 0 then
        cont w c ring wpos pend cap written p1 p2 remaining iCount lCount dCount flags iCur iPrev lCur lPrev dCur dPrev
          d0 d1 d2 d3 code ilen clen copyBits copyBase dist wordBuf wordPos .distance left p (hr.retag trivial)
      else if lCount = 0 then
        if hn : 2 ≤ H.nL then
          let hn' := UInt64.le_iff_toNat_le.mp hn
          let r := blockSwitch H.arena H.lit.arena32 H.baseTL H.baseCL (H.swL hn').1 (H.swL hn').2 H.nL lCur lPrev w c
          match hst : r.status with
          | .ok =>
            cont r.word r.count ring wpos pend cap written p1 p2 remaining iCount r.blockCount dCount
              { flags with
                fL0 := markWord flags.fL0 r.cur 0, fL1 := markWord flags.fL1 r.cur 1, fL2 := markWord flags.fL2 r.cur 2
                fL3 := markWord flags.fL3 r.cur 3 }
              iCur iPrev r.cur lCur dCur dPrev d0 d1 d2 d3 code ilen clen copyBits copyBase dist wordBuf wordPos
              .literals left p (hr.swL hn hst trivial)
          | .short =>
            exit (mkCmd w c ring wpos pend cap written p1 p2 remaining iCount lCount dCount flags iCur iPrev lCur lPrev
              dCur dPrev d0 d1 d2 d3 code ilen clen copyBits copyBase dist wordBuf wordPos .literals left p .needsInput)
          | .bad =>
            exit (mkCmd w c ring wpos pend cap written p1 p2 remaining iCount lCount dCount flags iCur iPrev lCur lPrev
              dCur dPrev d0 d1 d2 d3 code ilen clen copyBits copyBase dist wordBuf wordPos .literals left p .bad)
        else
          exit (mkCmd w c ring wpos pend cap written p1 p2 remaining iCount lCount dCount flags iCur iPrev lCur lPrev
            dCur dPrev d0 d1 d2 d3 code ilen clen copyBits copyBase dist wordBuf wordPos .literals left p .bad)
      else if room k cap ≤ pend then
        exit (mkCmd w c ring wpos pend cap written p1 p2 remaining iCount lCount dCount flags iCur iPrev lCur lPrev
          dCur dPrev d0 d1 d2 d3 code ilen clen copyBits copyBase dist wordBuf wordPos .literals left p .needsOutput)
      else
        have ht' : lCur.toNat < H.nL.toNat := hr.lCur
        have hm : lCur.toUSize.toNat < H.modes.size := by
          rw [cur_usize ht', H.modesSize]
          exact ht'
        have hmLt := H.modesLt _ hm
        let run := (umin left (umin lCount (room k cap - pend).toUInt64)).toUSize
        let r := literalRunCS cell H lCur ht' a stop hs ((H.modes.uget lCur.toUSize hm).toUInt64 <<< 9).toUSize
          (ringMask k) k.toNat
          (by
            rw [modeOff_toNat hmLt]
            omega)
          (by
            rw [modeOff_toNat hmLt]
            omega)
          (ringMask_toNat hr.k24) hr.k24 run w c p wpos ring p1 p2 hr.pos hr.wf hr.size hr.wpos
        have hri := literalRunCS_inv cell H lCur ht' a stop hs ((H.modes.uget lCur.toUSize hm).toUInt64 <<< 9).toUSize
          (ringMask k) k.toNat
          (by
            rw [modeOff_toNat hmLt]
            omega)
          (by
            rw [modeOff_toNat hmLt]
            omega)
          (ringMask_toNat hr.k24) hr.k24 run w c p wpos ring p1 p2 hr.pos hr.wf hr.size hr.wpos
        let used := run - r.left
        if r.left = 0 then
          contC { r with ring := ByteArray.empty } r.word r.count r.ring r.wpos (pend + used) cap
            (usmin (ringSize k - USize.ofNat 16) (written + used))
            r.p1 r.p2 (remaining - used.toUInt64) iCount (lCount - used.toUInt64) dCount flags iCur iPrev lCur lPrev
            dCur dPrev d0 d1 d2 d3 code ilen clen copyBits copyBase dist wordBuf wordPos .literals
            (left - used.toUInt64) r.pos (hr.set hri.1 hri.2.1 (written_usmin hr.k24 hr.k16 _) hri.2.2.1 hri.2.2.2 trivial)
        else
          exit (mkCmd r.word r.count r.ring r.wpos (pend + used) cap (usmin (ringSize k - USize.ofNat 16) (written + used))
            r.p1 r.p2 (remaining - used.toUInt64) iCount (lCount - used.toUInt64) dCount flags iCur iPrev lCur lPrev
            dCur dPrev d0 d1 d2 d3 code ilen clen copyBits copyBase dist wordBuf wordPos .literals
            (left - used.toUInt64) r.pos .needsInput)
    | .distance =>
      if remaining = 0 then
        cont w c ring wpos pend cap written p1 p2 remaining iCount lCount dCount flags iCur iPrev lCur lPrev dCur dPrev
          d0 d1 d2 d3 code ilen clen copyBits copyBase dist wordBuf wordPos .command left p (hr.retag trivial)
      else if code < 128 then
        if hd0 : d0 = 0 then
          exit (mkCmd w c ring wpos pend cap written p1 p2 remaining iCount lCount dCount flags iCur iPrev lCur lPrev
            dCur dPrev d0 d1 d2 d3 code ilen clen copyBits copyBase dist wordBuf wordPos .distance left p .bad)
        else
          kapply cont exit w c ring wpos pend cap written p1 p2 remaining iCount lCount dCount flags iCur iPrev lCur lPrev
            dCur dPrev d0 d1 d2 d3 code ilen clen copyBits copyBase dist wordBuf wordPos .distance left p 0 d0 hd0
            (hr.retag trivial)
      else if dCount = 0 then
        if hn : 2 ≤ H.nD then
          let hn' := UInt64.le_iff_toNat_le.mp hn
          let r := blockSwitch H.arena H.lit.arena32 H.baseTD H.baseCD (H.swD hn').1 (H.swD hn').2 H.nD dCur dPrev w c
          match hst : r.status with
          | .ok =>
            cont r.word r.count ring wpos pend cap written p1 p2 remaining iCount lCount (r.blockCount - 1)
              { flags with
                fD0 := markWord flags.fD0 r.cur 0, fD1 := markWord flags.fD1 r.cur 1, fD2 := markWord flags.fD2 r.cur 2
                fD3 := markWord flags.fD3 r.cur 3 }
              iCur iPrev lCur lPrev r.cur dCur d0 d1 d2 d3 code ilen clen copyBits copyBase dist wordBuf wordPos
              .distanceSymbol left p (hr.swD hn hst trivial)
          | .short =>
            exit (mkCmd w c ring wpos pend cap written p1 p2 remaining iCount lCount dCount flags iCur iPrev lCur lPrev
              dCur dPrev d0 d1 d2 d3 code ilen clen copyBits copyBase dist wordBuf wordPos .distance left p .needsInput)
          | .bad =>
            exit (mkCmd w c ring wpos pend cap written p1 p2 remaining iCount lCount dCount flags iCur iPrev lCur lPrev
              dCur dPrev d0 d1 d2 d3 code ilen clen copyBits copyBase dist wordBuf wordPos .distance left p .bad)
        else
          exit (mkCmd w c ring wpos pend cap written p1 p2 remaining iCount lCount dCount flags iCur iPrev lCur lPrev
            dCur dPrev d0 d1 d2 d3 code ilen clen copyBits copyBase dist wordBuf wordPos .distance left p .bad)
      else
        cont w c ring wpos pend cap written p1 p2 remaining iCount lCount (dCount - 1) flags iCur iPrev lCur lPrev dCur
          dPrev d0 d1 d2 d3 code ilen clen copyBits copyBase dist wordBuf wordPos .distanceSymbol left p
          (hr.retag trivial)
    | .distanceSymbol =>
      have ht' : dCur.toNat < H.nD.toNat := hr.dCur
      have hi : (dMapIndex dCur clen).toNat < H.dMap.size := by
        have h1 := H.dMap32
        have h2 := H.dMapSize
        have hcid := distanceContextId_lt clen.toNat
        rw [dMapIndex_toNat (by omega)]
        omega
      let tree := H.dMap.uget (dMapIndex dCur clen) hi
      have htree : tree.toNat < H.treesD.toNat := H.dMapLt _ hi
      have hb : 4 * tree.toUInt64.toNat + 4 ≤ H.dBase.size := by
        rw [H.dSize, UInt8.toNat_toUInt64]
        omega
      have hfit : TableFits H.arena (tableBase H.dBase tree.toUInt64 hb H.d32).toNat := by
        rw [tableBase_toNat, UInt8.toNat_toUInt64]
        exact H.dFits _ htree
      let v := lookup H.arena (tableBase H.dBase tree.toUInt64 hb H.d32) w hfit H.lit.arena32
      if hwb : wordBits v ≤ c then
        let nbits := extraBitsFast H.npostfix H.ndirect (wordSym v)
        let b1 := (BitBuffer.mk w c).drop (wordBits v)
        have hn24 : nbits ≤ 24 := d_bits hr.hdr htree hwb
        if hnb : nbits ≤ b1.count then
          let b2 := b1.drop nbits
          let d := distFast H.npostfix H.ndirect d0 d1 d2 d3 (wordSym v) (b1.peek nbits)
          if hd0 : d = 0 then
            exit (mkCmd w c ring wpos pend cap written p1 p2 remaining iCount lCount dCount flags iCur iPrev lCur
              lPrev dCur dPrev d0 d1 d2 d3 code ilen clen copyBits copyBase dist wordBuf wordPos .distanceSymbol left
              p .bad)
          else
            kapply cont exit b2.word b2.count ring wpos pend cap written p1 p2 remaining iCount lCount dCount flags
              iCur iPrev lCur lPrev dCur dPrev d0 d1 d2 d3 code ilen clen copyBits copyBase dist wordBuf wordPos
              .distanceSymbol left p (wordSym v) d hd0
              ((hr.drop (wordBits_lt v) hwb hr.tagged).drop
                (by
                  have := UInt64.le_iff_toNat_le.mp hn24
                  have h24 : (24 : UInt64).toNat = 24 := rfl
                  omega) hnb trivial)
        else
          exit (mkCmd w c ring wpos pend cap written p1 p2 remaining iCount lCount dCount flags iCur iPrev lCur lPrev
            dCur dPrev d0 d1 d2 d3 code ilen clen copyBits copyBase dist wordBuf wordPos .distanceSymbol left p
            .needsInput)
      else
        exit (mkCmd w c ring wpos pend cap written p1 p2 remaining iCount lCount dCount flags iCur iPrev lCur lPrev
          dCur dPrev d0 d1 d2 d3 code ilen clen copyBits copyBase dist wordBuf wordPos .distanceSymbol left p
          .needsInput)
    | .copy =>
      if hl0 : left = 0 then
        cont w c ring wpos pend cap written p1 p2 remaining iCount lCount dCount flags iCur iPrev lCur lPrev dCur dPrev
          d0 d1 d2 d3 code ilen clen copyBits copyBase dist wordBuf wordPos .command left p (hr.retag trivial)
      else if hrm : room k cap ≤ pend then
        exit (mkCmd w c ring wpos pend cap written p1 p2 remaining iCount lCount dCount flags iCur iPrev lCur lPrev
          dCur dPrev d0 d1 d2 d3 code ilen clen copyBits copyBase dist wordBuf wordPos .copy left p .needsOutput)
      else
        let run := (umin left (room k cap - pend).toUInt64).toUSize
        let d := dist.toUSize
        have hdd := copy_dist hr.k24 hr.tagged
        have hrun : run ≠ 0 := copy_run_ne hr.k24 hl0 hrm
        have h2 : 2 ≤ 2 ^ k.toNat := by have := hr.k16; omega
        let r := copyRunF d (ringMask k) (ringSize k) k.toNat hr.k24 (ringMask_toNat hr.k24) (ringSize_toNat hr.k24)
          hdd.2.2.1 hdd.2.2.2 run ring wpos p1 p2 hr.size hr.wpos h2 hrun
        have hri := copyRunF_inv hr.k24 (ringMask_toNat hr.k24) (ringSize_toNat hr.k24) hdd.2.2.1 hdd.2.2.2 run ring wpos
          p1 p2 hr.size hr.wpos h2 hrun
        cont w c r.ring r.wpos (pend + run) cap (usmin (ringSize k - USize.ofNat 16) (written + run)) r.p1 r.p2
          remaining iCount lCount dCount flags iCur iPrev lCur lPrev dCur dPrev d0 d1 d2 d3 code ilen clen copyBits
          copyBase dist wordBuf wordPos .copy (left - run.toUInt64) p
          (hr.wrote hri.1 hri.2 (written_usmin hr.k24 hr.k16 _) hr.tagged)
    | .word =>
      if hw0 : wordBuf.usize - wordPos = 0 then
        cont w c ring wpos pend cap written p1 p2 remaining iCount lCount dCount flags iCur iPrev lCur lPrev dCur dPrev
          d0 d1 d2 d3 code ilen clen copyBits copyBase dist wordBuf wordPos .command left p (hr.retag trivial)
      else if hrm : room k cap ≤ pend then
        exit (mkCmd w c ring wpos pend cap written p1 p2 remaining iCount lCount dCount flags iCur iPrev lCur lPrev
          dCur dPrev d0 d1 d2 d3 code ilen clen copyBits copyBase dist wordBuf wordPos .word left p .needsOutput)
      else
        let run := usmin (wordBuf.usize - wordPos) (room k cap - pend)
        have h := word_bounds hr.tagged (room k cap - pend)
        have hrun : run ≠ 0 := word_run_ne hw0 hrm
        have h2 : 2 ≤ 2 ^ k.toNat := by have := hr.k16; omega
        let r := wordRunF wordBuf (ringMask k) k.toNat hr.k24 (ringMask_toNat hr.k24) run wordPos ring wpos p1 p2 h.1
          h.2 hr.size hr.wpos h2 hrun
        have hri := wordRunF_inv hr.k24 (ringMask_toNat hr.k24) run wordPos ring wpos p1 p2 h.1 h.2 hr.size hr.wpos h2
          hrun
        cont w c r.ring r.wpos (pend + run) cap (usmin (ringSize k - USize.ofNat 16) (written + run)) r.p1 r.p2
          remaining iCount lCount dCount flags iCur iPrev lCur lPrev dCur dPrev d0 d1 d2 d3 code ilen clen copyBits
          copyBase dist wordBuf (wordPos + run) .word left p
          (hr.wrote hri.1 hri.2 (written_usmin hr.k24 hr.k16 _) (word_next hr.tagged (room k cap - pend)))

/-- `runCmd` on the fields: up to `n` steps, each ending in a jump to the next. -/
def runCmdK (H : Hdr) (k : USize) (a : ByteArray) (stop : USize) (hs : stop.toNat ≤ a.size) (n : USize) :
    (cell : RunOut) → (word count : UInt64) → (ring : ByteArray) → (wpos pend cap written : USize) → (p1 p2 : UInt8) →
    (remaining iCount lCount dCount : UInt64) → (flags : Flags) →
    (iCur iPrev lCur lPrev dCur dPrev d0 d1 d2 d3 code ilen clen copyBits copyBase dist : UInt64) →
    (wordBuf : ByteArray) → (wordPos : USize) → (tag : Tag) → (left : UInt64) → (pos : USize) →
    KInv H k stop word count ring wpos written iCur iPrev lCur lPrev dCur dPrev copyBits dist wordBuf wordPos tag pos →
    Cmd :=
  if _hn : n = 0 then
    fun _ word count ring wpos pend cap written p1 p2 remaining iCount lCount dCount flags iCur iPrev lCur lPrev dCur
        dPrev d0 d1 d2 d3 code ilen clen copyBits copyBase dist wordBuf wordPos tag left pos _ =>
    mkCmd word count ring wpos pend cap written p1 p2 remaining iCount lCount dCount flags iCur iPrev lCur lPrev dCur dPrev
      d0 d1 d2 d3 code ilen clen copyBits copyBase dist wordBuf wordPos tag left pos .next
  else
    fun cell word count ring wpos pend cap written p1 p2 remaining iCount lCount dCount flags iCur iPrev lCur lPrev dCur
        dPrev d0 d1 d2 d3 code ilen clen copyBits copyBase dist wordBuf wordPos tag left pos hinv =>
    kstep H k a stop hs
      (fun cell word count ring wpos pend cap written p1 p2 remaining iCount lCount dCount flags iCur iPrev lCur lPrev dCur
          dPrev d0 d1 d2 d3 code ilen clen copyBits copyBase dist wordBuf wordPos tag left pos h =>
        runCmdK H k a stop hs (n - USize.ofNat 1) cell word count ring wpos pend cap written p1 p2 remaining iCount lCount
          dCount flags iCur iPrev lCur lPrev dCur dPrev d0 d1 d2 d3 code ilen clen copyBits copyBase dist wordBuf wordPos
          tag left pos h)
      (fun c => c)
      word count ring wpos pend cap written p1 p2 remaining iCount lCount dCount flags iCur iPrev lCur lPrev dCur dPrev
      d0 d1 d2 d3 code ilen clen copyBits copyBase dist wordBuf wordPos tag left pos cell hinv
termination_by n.toNat
decreasing_by
  have := usize_pred _hn
  have := usize_ne _hn
  omega

/-- What the compiled loop needs to know of a state. -/
public abbrev CmdInv (H : Hdr) (k stop : USize) (st : Cmd) (pos : USize) : Prop :=
  KInv H k stop st.word st.count st.ring st.wpos st.written st.iCur st.iPrev st.lCur st.lPrev st.dCur st.dPrev
    st.copyBits st.dist st.wordBuf st.wordPos st.tag pos

/-- `runCmd`, for a state the compiled loop may run from. The compiler runs `runCmdE` in its place. -/
@[expose] public def runCmdP (H : Hdr) (k : USize) (a : ByteArray) (stop : USize) (hs : stop.toNat ≤ a.size) (n : USize) (st : Cmd)
    (pos : USize) (_h : CmdInv H k stop st pos) : Cmd :=
  runCmd H k a stop hs n st pos

/-- `runCmdP` as the compiler runs it: the state taken apart once, then the loop on its fields. -/
public def runCmdE (H : Hdr) (k : USize) (a : ByteArray) (stop : USize) (hs : stop.toNat ≤ a.size) (n : USize) (st : Cmd)
    (pos : USize) (h : CmdInv H k stop st pos) : Cmd :=
  match st, h with
  | ⟨word, count, ring, wpos, pend, cap, written, p1, p2, remaining, iCount, lCount, dCount, flags,
      ⟨iCur, iPrev, lCur, lPrev, dCur, dPrev, d0, d1, d2, d3, code, ilen, clen, copyBits, copyBase, dist, wordBuf, wordPos⟩,
      tag, left, _, _⟩, h =>
    -- the first record, built from values so that it is allocated here and held once
    runCmdK H k a stop hs n ⟨word, count, pos, wpos, ByteArray.empty, p1, p2, 0, 0⟩ word count ring wpos pend cap written
      p1 p2 remaining iCount lCount dCount flags iCur iPrev lCur lPrev dCur dPrev d0 d1 d2 d3 code ilen clen copyBits
      copyBase dist wordBuf wordPos tag left pos h

/-! ### The command loop with the fast loop -/

/-- The command loop with the fast loop (`FastLoop.lean`): at a command's literals or its distance, with 40 bytes of the
chunk left and room for the rest of the command, the fast loop; otherwise, and always after the fast loop has left, one
step of the step machine. -/
def runCmdKF (H : Hdr) (k : USize) (a : ByteArray) (stop : USize) (hs : stop.toNat ≤ a.size) (n : USize) (fresh : Bool) :
    (cell : RunOut) → (word count : UInt64) → (ring : ByteArray) → (wpos pend cap written : USize) → (p1 p2 : UInt8) →
    (remaining iCount lCount dCount : UInt64) → (flags : Flags) →
    (iCur iPrev lCur lPrev dCur dPrev d0 d1 d2 d3 code ilen clen copyBits copyBase dist : UInt64) →
    (wordBuf : ByteArray) → (wordPos : USize) → (tag : Tag) → (left : UInt64) → (pos : USize) →
    KInv H k stop word count ring wpos written iCur iPrev lCur lPrev dCur dPrev copyBits dist wordBuf wordPos tag pos →
    Cmd :=
  if _hn : n = 0 then
    fun _ word count ring wpos pend cap written p1 p2 remaining iCount lCount dCount flags iCur iPrev lCur lPrev dCur
        dPrev d0 d1 d2 d3 code ilen clen copyBits copyBase dist wordBuf wordPos tag left pos _ =>
    mkCmd word count ring wpos pend cap written p1 p2 remaining iCount lCount dCount flags iCur iPrev lCur lPrev dCur dPrev
      d0 d1 d2 d3 code ilen clen copyBits copyBase dist wordBuf wordPos tag left pos .next
  else
    fun cell word count ring wpos pend cap written p1 p2 remaining iCount lCount dCount flags iCur iPrev lCur lPrev dCur
        dPrev d0 d1 d2 d3 code ilen clen copyBits copyBase dist wordBuf wordPos tag left pos hinv =>
    let lits : UInt64 := if tag = .literals then left else 0
    let rm := room k cap
    let roomLeft : UInt64 := if rm ≤ pend then 0 else (rm - pend).toUInt64
    let bEnd := wpos.toUInt64 + umin remaining roomLeft
    if hf : fresh = true ∧ (tag = .literals ∨ tag = .distance) ∧ USize.ofNat 40 ≤ stop - pos ∧
        ¬ bEnd < wpos.toUInt64 + lits + clen then
      have hm : pos.toNat + 40 ≤ stop.toNat := by
        have h1 := USize.le_iff_toNat_le.mp hf.2.2.1
        rw [fastLit (by decide), USize.toNat_sub_of_le _ _ (USize.le_iff_toNat_le.mpr hinv.pos)] at h1
        have := hinv.pos
        omega
      match fastEnter H k a stop hs cap n word count ring wpos pend written p1 p2 remaining iCount lCount dCount flags
          ⟨iCur, iPrev, lCur, lPrev, dCur, dPrev, d0, d1, d2, d3, code, ilen, clen, copyBits, copyBase, dist, wordBuf,
            wordPos⟩ tag lits bEnd pos hinv hm with
      | ⟨⟨word, count, ring, wpos, pend, cap, written, p1, p2, remaining, iCount, lCount, dCount, flags,
          ⟨iCur, iPrev, lCur, lPrev, dCur, dPrev, d0, d1, d2, d3, code, ilen, clen, copyBits, copyBase, dist, wordBuf,
            wordPos⟩, tag, left, pos, _⟩, h⟩ =>
        runCmdKF H k a stop hs (n - USize.ofNat 1) false cell word count ring wpos pend cap written p1 p2 remaining iCount
          lCount dCount flags iCur iPrev lCur lPrev dCur dPrev d0 d1 d2 d3 code ilen clen copyBits copyBase dist wordBuf
          wordPos tag left pos h
    else
    kstep H k a stop hs
      (fun cell word count ring wpos pend cap written p1 p2 remaining iCount lCount dCount flags iCur iPrev lCur lPrev dCur
          dPrev d0 d1 d2 d3 code ilen clen copyBits copyBase dist wordBuf wordPos tag left pos h =>
        runCmdKF H k a stop hs (n - USize.ofNat 1) true cell word count ring wpos pend cap written p1 p2 remaining iCount
          lCount dCount flags iCur iPrev lCur lPrev dCur dPrev d0 d1 d2 d3 code ilen clen copyBits copyBase dist wordBuf
          wordPos tag left pos h)
      (fun c => c)
      word count ring wpos pend cap written p1 p2 remaining iCount lCount dCount flags iCur iPrev lCur lPrev dCur dPrev
      d0 d1 d2 d3 code ilen clen copyBits copyBase dist wordBuf wordPos tag left pos cell hinv
termination_by n.toNat
decreasing_by
  all_goals
    have := usize_pred _hn
    have := usize_ne _hn
    omega

/-- The command loop with the fast loop, from a state the compiled loop may run from. -/
public def runCmdF (H : Hdr) (k : USize) (a : ByteArray) (stop : USize) (hs : stop.toNat ≤ a.size) (n : USize) (st : Cmd)
    (pos : USize) (h : CmdInv H k stop st pos) : Cmd :=
  match st, h with
  | ⟨word, count, ring, wpos, pend, cap, written, p1, p2, remaining, iCount, lCount, dCount, flags,
      ⟨iCur, iPrev, lCur, lPrev, dCur, dPrev, d0, d1, d2, d3, code, ilen, clen, copyBits, copyBase, dist, wordBuf, wordPos⟩,
      tag, left, _, _⟩, h =>
    runCmdKF H k a stop hs n true ⟨word, count, pos, wpos, ByteArray.empty, p1, p2, 0, 0⟩ word count ring wpos pend cap
      written p1 p2 remaining iCount lCount dCount flags iCur iPrev lCur lPrev dCur dPrev d0 d1 d2 d3 code ilen clen
      copyBits copyBase dist wordBuf wordPos tag left pos h

/-! ### The compiled loop is `runCmd` -/

/-- Takes both sides of an equation through the same tests: `split` reduces one side's test, and the hypothesis it
gives reduces the other side's copy. -/
macro "ksplit" : tactic =>
  `(tactic| repeat' (first
    | (split <;> rename_i h <;> (try simp only [h, ↓reduceIte, ↓reduceDIte, and_self, and_true, true_and]))
    | rfl
    | contradiction))

/-- `ksplit`, closing branches with a given tactic before trying `rfl`: on a branch where the other side's test failed
and a fact rules that out, `rfl` would unfold both sides and hit the recursion limit. -/
macro "ksplitT " t:tacticSeq : tactic =>
  `(tactic| repeat' (first
    | (split <;> rename_i h <;> (try simp only [h, ↓reduceIte, ↓reduceDIte, and_self, and_true, true_and]))
    | ($t)
    | rfl
    | contradiction))

section
/-- A continuation that depends neither on the record it is handed nor on the proof. -/
abbrev Drops {α : Type} (H : Hdr) (k stop : USize) (contC : KContC H k stop α) (g : KCont α) : Prop :=
  ∀ c word count ring wpos pend cap written p1 p2 remaining iCount lCount dCount flags iCur iPrev lCur lPrev dCur dPrev
    d0 d1 d2 d3 code ilen clen copyBits copyBase dist wordBuf wordPos tag left pos h,
    contC c word count ring wpos pend cap written p1 p2 remaining iCount lCount dCount flags iCur iPrev lCur lPrev dCur
        dPrev d0 d1 d2 d3 code ilen clen copyBits copyBase dist wordBuf wordPos tag left pos h =
      g word count ring wpos pend cap written p1 p2 remaining iCount lCount dCount flags iCur iPrev lCur lPrev dCur dPrev
        d0 d1 d2 d3 code ilen clen copyBits copyBase dist wordBuf wordPos tag left pos

variable {α : Type} (H : Hdr) (k : USize) (a : ByteArray) (stop : USize) (hs : stop.toNat ≤ a.size)
  (contC : KContC H k stop α) (g : KCont α) (exit : Cmd → α)
  (word count : UInt64) (ring : ByteArray) (wpos pend cap written : USize) (p1 p2 : UInt8)
  (remaining iCount lCount dCount : UInt64) (flags : Flags)
  (iCur iPrev lCur lPrev dCur dPrev d0 d1 d2 d3 code ilen clen copyBits copyBase dist : UInt64)
  (wordBuf : ByteArray) (wordPos : USize) (left : UInt64) (pos sp : USize) (ss : StepStatus) (cell : RunOut)

/-- What a step on the fields must equal, for a tag, when its continuation doesn't depend on the record it passes. -/
abbrev KStepIs (tag : Tag) (hinv : KInv H k stop word count ring wpos written iCur iPrev lCur lPrev dCur dPrev copyBits dist wordBuf wordPos tag pos) :
    Prop :=
  kstep H k a stop hs contC exit word count ring wpos pend cap written p1 p2 remaining iCount lCount dCount flags iCur
      iPrev lCur lPrev dCur dPrev d0 d1 d2 d3 code ilen clen copyBits copyBase dist wordBuf wordPos tag left pos cell
      hinv =
    kcase g exit (stepCmd H k a stop hs (mkCmd word count ring wpos pend cap written p1 p2 remaining iCount lCount
      dCount flags iCur iPrev lCur lPrev dCur dPrev d0 d1 d2 d3 code ilen clen copyBits copyBase dist wordBuf wordPos
      tag left sp ss) pos)

-- The simp sets below unfold every step and accessor a tag may reach; which accessors a tag's proof uses isn't worth
-- tracking by hand, so the linter for unused simp arguments is off for these eight lemmas.
set_option linter.unusedSimpArgs false

theorem kstep_command (hcont : Drops H k stop contC g)
    (hinv : KInv H k stop word count ring wpos written iCur iPrev lCur lPrev dCur dPrev copyBits dist wordBuf wordPos _ pos) :
    KStepIs H k a stop hs contC g exit word count ring wpos pend cap written p1 p2 remaining iCount lCount dCount flags iCur
      iPrev lCur lPrev dCur dPrev d0 d1 d2 d3 code ilen clen copyBits copyBase dist wordBuf wordPos left pos sp ss cell
      .command hinv := by
  unfold KStepIs kstep stepCmd
  simp only [hcont]
  rw [dite_eq_left (USize.le_iff_toNat_le.mpr hinv.pos)]
  simp only [mkCmd, stepAt, stepCommand, markStep, Cmd.iCur, Cmd.iPrev]
  ksplit

theorem kstep_insertCopy (hcont : Drops H k stop contC g)
    (hinv : KInv H k stop word count ring wpos written iCur iPrev lCur lPrev dCur dPrev copyBits dist wordBuf wordPos _ pos) :
    KStepIs H k a stop hs contC g exit word count ring wpos pend cap written p1 p2 remaining iCount lCount dCount flags iCur
      iPrev lCur lPrev dCur dPrev d0 d1 d2 d3 code ilen clen copyBits copyBase dist wordBuf wordPos left pos sp ss cell
      .insertCopy hinv := by
  unfold KStepIs kstep stepCmd
  simp only [hcont]
  rw [dite_eq_left (USize.le_iff_toNat_le.mpr hinv.pos)]
  have hI : iCur < H.nI := UInt64.lt_iff_toNat_lt.mpr hinv.iCur
  have hsym : ∀ (w c : UInt64) (hb : 4 * iCur.toNat + 4 ≤ H.icBase.size)
      (hf : TableFits H.arena (tableBase H.icBase iCur hb H.ic32).toNat),
      wordBits (lookup H.arena (tableBase H.icBase iCur hb H.ic32) w hf H.lit.arena32) ≤ c →
      wordSym (lookup H.arena (tableBase H.icBase iCur hb H.ic32) w hf H.lit.arena32) < 704 :=
    fun _ _ _ _ h => ic_sym hinv.hdr hinv.iCur h
  simp only [mkCmd, stepAt, stepInsertCopy, insertStep, markStep, Cmd.iCur, hI, ↓reduceDIte]
  -- `stepCmd`'s symbol test failing is ruled out by the table's code
  ksplitT with_reducible exact absurd (hsym _ _ _ _ (by assumption)) (by assumption)

theorem kstep_copyLength (hcont : Drops H k stop contC g)
    (hinv : KInv H k stop word count ring wpos written iCur iPrev lCur lPrev dCur dPrev copyBits dist wordBuf wordPos _ pos) :
    KStepIs H k a stop hs contC g exit word count ring wpos pend cap written p1 p2 remaining iCount lCount dCount flags iCur
      iPrev lCur lPrev dCur dPrev d0 d1 d2 d3 code ilen clen copyBits copyBase dist wordBuf wordPos left pos sp ss cell
      .copyLength hinv := by
  unfold KStepIs kstep stepCmd
  simp only [hcont]
  rw [dite_eq_left (USize.le_iff_toNat_le.mpr hinv.pos)]
  simp only [mkCmd, stepAt, stepCopyLength, markStep, Cmd.ilen, Cmd.copyBits, Cmd.copyBase]
  ksplit

theorem kstep_literals (hcont : Drops H k stop contC g)
    (hinv : KInv H k stop word count ring wpos written iCur iPrev lCur lPrev dCur dPrev copyBits dist wordBuf wordPos _ pos) :
    KStepIs H k a stop hs contC g exit word count ring wpos pend cap written p1 p2 remaining iCount lCount dCount flags iCur
      iPrev lCur lPrev dCur dPrev d0 d1 d2 d3 code ilen clen copyBits copyBase dist wordBuf wordPos left pos sp ss cell
      .literals hinv := by
  unfold KStepIs kstep stepCmd
  simp only [hcont]
  rw [dite_eq_left (USize.le_iff_toNat_le.mpr hinv.pos)]
  have hL : lCur < H.nL := UInt64.lt_iff_toNat_lt.mpr hinv.lCur
  have hwin := hinv.win
  have hp' : ∀ hq, (refill word count a pos stop hs hq).pos ≤ stop :=
    fun hq => USize.le_iff_toNat_le.mpr (refill_spec hs hq hinv.wf).2.2.1
  have hwf : ∀ hq, wfCheck (refill word count a pos stop hs hq).word (refill word count a pos stop hs hq).count = true :=
    fun hq => wfCheck_of_wf (refill_spec hs hq hinv.wf).1
  simp only [mkCmd, stepAt, stepLiterals, literalsRun, finishLiterals, clearRing, markStep, Cmd.lCur, Cmd.lPrev,
    literalRunCS_eq, litInto, hL, hwin, hp', hwf, and_self, ↓reduceDIte]
  ksplit

theorem kstep_distance (hcont : Drops H k stop contC g)
    (hinv : KInv H k stop word count ring wpos written iCur iPrev lCur lPrev dCur dPrev copyBits dist wordBuf wordPos _ pos) :
    KStepIs H k a stop hs contC g exit word count ring wpos pend cap written p1 p2 remaining iCount lCount dCount flags iCur
      iPrev lCur lPrev dCur dPrev d0 d1 d2 d3 code ilen clen copyBits copyBase dist wordBuf wordPos left pos sp ss cell
      .distance hinv := by
  unfold KStepIs kstep stepCmd
  simp only [hcont]
  rw [dite_eq_left (USize.le_iff_toNat_le.mpr hinv.pos)]
  simp only [mkCmd, stepAt, stepDistance, applyDistance, applyWord, applyBuilt, kapply, markStep, Cmd.code, Cmd.d0,
    Cmd.d1, Cmd.d2, Cmd.clen, Cmd.dCur, Cmd.dPrev, hcont]
  ksplit

theorem kstep_distanceSymbol (hcont : Drops H k stop contC g)
    (hinv : KInv H k stop word count ring wpos written iCur iPrev lCur lPrev dCur dPrev copyBits dist wordBuf wordPos _ pos) :
    KStepIs H k a stop hs contC g exit word count ring wpos pend cap written p1 p2 remaining iCount lCount dCount flags iCur
      iPrev lCur lPrev dCur dPrev d0 d1 d2 d3 code ilen clen copyBits copyBase dist wordBuf wordPos left pos sp ss cell
      .distanceSymbol hinv := by
  unfold KStepIs kstep stepCmd
  simp only [hcont]
  rw [dite_eq_left (USize.le_iff_toNat_le.mpr hinv.pos)]
  simp only [mkCmd, stepAt, stepDistanceSymbol, distanceThrough, distanceStep, setBits, applyDistance, applyWord,
    applyBuilt, kapply, markStep, Cmd.dCur, Cmd.clen, Cmd.d0, Cmd.d1, Cmd.d2, Cmd.d3, hcont]
  -- `split` doesn't take this outer test apart, so the invariant's fact settles it
  have hD : dCur < H.nD := UInt64.lt_iff_toNat_lt.mpr hinv.dCur
  have hbits : ∀ (p : USize) (hp : p.toNat < H.dMap.size)
      (hb : 4 * (H.dMap.uget p hp).toUInt64.toNat + 4 ≤ H.dBase.size)
      (hf : TableFits H.arena (tableBase H.dBase (H.dMap.uget p hp).toUInt64 hb H.d32).toNat) (w c : UInt64),
      wordBits (lookup H.arena (tableBase H.dBase (H.dMap.uget p hp).toUInt64 hb H.d32) w hf H.lit.arena32) ≤ c →
      extraBitsFast H.npostfix H.ndirect
        (wordSym (lookup H.arena (tableBase H.dBase (H.dMap.uget p hp).toUInt64 hb H.d32) w hf H.lit.arena32)) ≤ 24 :=
    fun p hp _ _ _ _ h => d_bits hinv.hdr (H.dMapLt p hp) h
  have h0 : extraBitsFast H.npostfix H.ndirect 0 ≤ 24 := by
    apply UInt64.le_iff_toNat_le.mpr
    rw [extraBitsFast_toNat H.npLe H.ndLe (by decide)]
    show distanceExtraBits _ _ 0 ≤ 24
    unfold distanceExtraBits
    split <;> omega
  simp only [hD, ↓reduceDIte]
  -- `stepCmd`'s extra-bits test failing is ruled out by the table's code (where the symbol is known to be 0, by the
  -- extra bits of symbol 0)
  ksplitT
    with_reducible first
    | exact absurd (hbits _ _ _ _ _ _ (by assumption)) (by assumption)
    | exact absurd h0 (by assumption)

theorem kstep_copy (hcont : Drops H k stop contC g)
    (hinv : KInv H k stop word count ring wpos written iCur iPrev lCur lPrev dCur dPrev copyBits dist wordBuf wordPos _ pos) :
    KStepIs H k a stop hs contC g exit word count ring wpos pend cap written p1 p2 remaining iCount lCount dCount flags iCur
      iPrev lCur lPrev dCur dPrev d0 d1 d2 d3 code ilen clen copyBits copyBase dist wordBuf wordPos left pos sp ss cell
      .copy hinv := by
  unfold KStepIs kstep stepCmd
  simp only [hcont]
  rw [dite_eq_left (USize.le_iff_toNat_le.mpr hinv.pos)]
  have hwin := hinv.win
  have hdd := copy_dist hinv.k24 hinv.tagged
  simp only [mkCmd, stepAt, stepCopy, finishCopy, clearRing, markStep, Cmd.dist, copyRunF_eq, hwin, hdd.1, hdd.2.1,
    and_self, ↓reduceDIte]
  ksplit

theorem kstep_word (hcont : Drops H k stop contC g)
    (hinv : KInv H k stop word count ring wpos written iCur iPrev lCur lPrev dCur dPrev copyBits dist wordBuf wordPos _ pos) :
    KStepIs H k a stop hs contC g exit word count ring wpos pend cap written p1 p2 remaining iCount lCount dCount flags iCur
      iPrev lCur lPrev dCur dPrev d0 d1 d2 d3 code ilen clen copyBits copyBase dist wordBuf wordPos left pos sp ss cell
      .word hinv := by
  unfold KStepIs kstep stepCmd
  simp only [hcont]
  rw [dite_eq_left (USize.le_iff_toNat_le.mpr hinv.pos)]
  have hwin := hinv.win
  have hA := fun x => (word_bounds hinv.tagged x).1
  have hB := fun x => (word_bounds hinv.tagged x).2
  simp only [mkCmd, stepAt, stepWord, finishWord, clearRing, markStep, Cmd.wordBuf, Cmd.wordPos, wordRunF_eq, hwin, hA,
    hB, and_self, ↓reduceDIte]
  ksplit

set_option linter.unusedSimpArgs true

/-- A step on the fields is `stepCmd` on the record they make, gone on with. -/
theorem kstep_eq (hcont : Drops H k stop contC g) (tag : Tag)
    (hinv : KInv H k stop word count ring wpos written iCur iPrev lCur lPrev dCur dPrev copyBits dist wordBuf wordPos tag pos) :
    KStepIs H k a stop hs contC g exit word count ring wpos pend cap written p1 p2 remaining iCount lCount dCount flags iCur
      iPrev lCur lPrev dCur dPrev d0 d1 d2 d3 code ilen clen copyBits copyBase dist wordBuf wordPos left pos sp ss cell tag
      hinv := by
  · cases tag
    · exact kstep_command H k a stop hs contC g exit word count ring wpos pend cap written p1 p2 remaining iCount lCount
        dCount flags iCur iPrev lCur lPrev dCur dPrev d0 d1 d2 d3 code ilen clen copyBits copyBase dist wordBuf wordPos
        left pos sp ss cell hcont hinv
    · exact kstep_insertCopy H k a stop hs contC g exit word count ring wpos pend cap written p1 p2 remaining iCount lCount
        dCount flags iCur iPrev lCur lPrev dCur dPrev d0 d1 d2 d3 code ilen clen copyBits copyBase dist wordBuf wordPos
        left pos sp ss cell hcont hinv
    · exact kstep_copyLength H k a stop hs contC g exit word count ring wpos pend cap written p1 p2 remaining iCount lCount
        dCount flags iCur iPrev lCur lPrev dCur dPrev d0 d1 d2 d3 code ilen clen copyBits copyBase dist wordBuf wordPos
        left pos sp ss cell hcont hinv
    · exact kstep_literals H k a stop hs contC g exit word count ring wpos pend cap written p1 p2 remaining iCount lCount
        dCount flags iCur iPrev lCur lPrev dCur dPrev d0 d1 d2 d3 code ilen clen copyBits copyBase dist wordBuf wordPos
        left pos sp ss cell hcont hinv
    · exact kstep_distance H k a stop hs contC g exit word count ring wpos pend cap written p1 p2 remaining iCount lCount
        dCount flags iCur iPrev lCur lPrev dCur dPrev d0 d1 d2 d3 code ilen clen copyBits copyBase dist wordBuf wordPos
        left pos sp ss cell hcont hinv
    · exact kstep_distanceSymbol H k a stop hs contC g exit word count ring wpos pend cap written p1 p2 remaining iCount
        lCount dCount flags iCur iPrev lCur lPrev dCur dPrev d0 d1 d2 d3 code ilen clen copyBits copyBase dist wordBuf
        wordPos left pos sp ss cell hcont hinv
    · exact kstep_copy H k a stop hs contC g exit word count ring wpos pend cap written p1 p2 remaining iCount lCount
        dCount flags iCur iPrev lCur lPrev dCur dPrev d0 d1 d2 d3 code ilen clen copyBits copyBase dist wordBuf wordPos
        left pos sp ss cell hcont hinv
    · exact kstep_word H k a stop hs contC g exit word count ring wpos pend cap written p1 p2 remaining iCount lCount
        dCount flags iCur iPrev lCur lPrev dCur dPrev d0 d1 d2 d3 code ilen clen copyBits copyBase dist wordBuf wordPos
        left pos sp ss cell hcont hinv

end

/-- The loop on the fields is `runCmd` on the record they make. -/
theorem runCmdK_eq (H : Hdr) (k : USize) (a : ByteArray) (stop : USize) (hs : stop.toNat ≤ a.size) :
    ∀ (N : Nat) (n : USize) (cell : RunOut) (word count : UInt64) (ring : ByteArray) (wpos pend cap written : USize)
      (p1 p2 : UInt8) (remaining iCount lCount dCount : UInt64) (flags : Flags)
      (iCur iPrev lCur lPrev dCur dPrev d0 d1 d2 d3 code ilen clen copyBits copyBase dist : UInt64)
      (wordBuf : ByteArray) (wordPos : USize) (tag : Tag) (left : UInt64) (pos sp : USize) (ss : StepStatus)
      (hinv : KInv H k stop word count ring wpos written iCur iPrev lCur lPrev dCur dPrev copyBits dist wordBuf wordPos tag pos),
      n.toNat = N →
      runCmdK H k a stop hs n cell word count ring wpos pend cap written p1 p2 remaining iCount lCount dCount flags iCur
          iPrev lCur lPrev dCur dPrev d0 d1 d2 d3 code ilen clen copyBits copyBase dist wordBuf wordPos tag left pos hinv =
        runCmd H k a stop hs n (mkCmd word count ring wpos pend cap written p1 p2 remaining iCount lCount dCount flags
          iCur iPrev lCur lPrev dCur dPrev d0 d1 d2 d3 code ilen clen copyBits copyBase dist wordBuf wordPos tag left sp ss)
          pos := by
  intro N
  induction N with
  | zero =>
    intro n cell word count ring wpos pend cap written p1 p2 remaining iCount lCount dCount flags iCur iPrev lCur lPrev
      dCur dPrev d0 d1 d2 d3 code ilen clen copyBits copyBase dist wordBuf wordPos tag left pos sp ss hinv hN
    have hn : n = 0 := usize_zero hN
    rw [runCmdK, runCmd, dite_eq_left hn, dite_eq_left hn]
    rfl
  | succ N ih =>
    intro n cell word count ring wpos pend cap written p1 p2 remaining iCount lCount dCount flags iCur iPrev lCur lPrev
      dCur dPrev d0 d1 d2 d3 code ilen clen copyBits copyBase dist wordBuf wordPos tag left pos sp ss hinv hN
    have hn : n ≠ 0 := fun e => by rw [e] at hN; exact Nat.succ_ne_zero _ hN.symm
    have hpred : (n - USize.ofNat 1).toNat = N := by
      rw [usize_pred hn]
      omega
    -- the rest of the loop depends neither on the record it is handed nor on the proof: it is `runCmd`
    have hc : Drops H k stop
        (fun c word count ring wpos pend cap written p1 p2 remaining iCount lCount dCount flags iCur iPrev lCur lPrev dCur
            dPrev d0 d1 d2 d3 code ilen clen copyBits copyBase dist wordBuf wordPos tag left pos h =>
          runCmdK H k a stop hs (n - USize.ofNat 1) c word count ring wpos pend cap written p1 p2 remaining iCount lCount
            dCount flags iCur iPrev lCur lPrev dCur dPrev d0 d1 d2 d3 code ilen clen copyBits copyBase dist wordBuf wordPos
            tag left pos h)
        (fun word count ring wpos pend cap written p1 p2 remaining iCount lCount dCount flags iCur iPrev lCur lPrev dCur
            dPrev d0 d1 d2 d3 code ilen clen copyBits copyBase dist wordBuf wordPos tag left pos =>
          runCmd H k a stop hs (n - USize.ofNat 1) (mkCmd word count ring wpos pend cap written p1 p2 remaining iCount
            lCount dCount flags iCur iPrev lCur lPrev dCur dPrev d0 d1 d2 d3 code ilen clen copyBits copyBase dist wordBuf
            wordPos tag left pos .next) pos) :=
      fun c word count ring wpos pend cap written p1 p2 remaining iCount lCount dCount flags iCur iPrev lCur lPrev dCur
          dPrev d0 d1 d2 d3 code ilen clen copyBits copyBase dist wordBuf wordPos tag left pos h =>
        ih _ c word count ring wpos pend cap written p1 p2 remaining iCount lCount dCount flags iCur iPrev lCur lPrev
          dCur dPrev d0 d1 d2 d3 code ilen clen copyBits copyBase dist wordBuf wordPos tag left pos pos .next h hpred
    rw [runCmdK, runCmd, dite_eq_right hn, dite_eq_right hn, kstep_eq (sp := sp) (ss := ss) (hcont := hc)]
    dsimp only
    generalize stepCmd H k a stop hs (mkCmd word count ring wpos pend cap written p1 p2 remaining iCount lCount dCount
      flags iCur iPrev lCur lPrev dCur dPrev d0 d1 d2 d3 code ilen clen copyBits copyBase dist wordBuf wordPos tag left sp
      ss) pos = r
    obtain ⟨w, c, rg, wp, pe, cp, wr, q1, q2, rm, ic, lc, dc, fl,
      ⟨e1, e2, e3, e4, e5, e6, e7, e8, e9, e10, e11, e12, e13, e14, e15, e16, e17, e18⟩, tg, lf, ps, st⟩ := r
    unfold kcase
    cases st
    all_goals rfl

/-- The compiler runs the loop on the fields in place of `runCmdP`. -/
@[csimp] public theorem runCmdP_csimp : @runCmdP = @runCmdE := by
  funext H k a stop hs n st pos h
  obtain ⟨word, count, ring, wpos, pend, cap, written, p1, p2, remaining, iCount, lCount, dCount, flags,
    ⟨iCur, iPrev, lCur, lPrev, dCur, dPrev, d0, d1, d2, d3, code, ilen, clen, copyBits, copyBase, dist, wordBuf, wordPos⟩,
    tag, left, sp, ss⟩ := st
  exact (runCmdK_eq H k a stop hs _ n ⟨word, count, pos, wpos, ByteArray.empty, p1, p2, 0, 0⟩ word count ring wpos pend
    cap written p1 p2 remaining iCount lCount dCount flags iCur iPrev lCur lPrev dCur dPrev d0 d1 d2 d3 code ilen clen
    copyBits copyBase dist wordBuf wordPos tag left pos sp ss h rfl).symm

end Brotli.Decoder
