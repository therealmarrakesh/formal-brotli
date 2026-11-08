module

public import Brotli.Decoder.FastRead
public import Brotli.Decoder.LoopInv
public import Brotli.Decoder.StepLiterals
public import Brotli.Decoder.WinCopy

@[expose] public section

/-!
# The fast command loop

The command loop of `docs/command-loop.md` ("The final kernel", M32), as a proved definition: literals two at a time by
the pair tables or two lookups, the distance by the resolved map and the shared table, the copy by the window
primitives, the insert-and-copy command by its fused entry. Every read of the table arena is in range by `TabOk`, every
read of the input by the margin the loop keeps (`stop - 40`), and every write to the window by its mask, so the loop
tests none of it at run time.

This file holds the loop's parts, each with what it guarantees.
-/

namespace Brotli.Decoder

open Brotli.Spec

/-! ### The refill under the margin -/

/-- What a refill under the margin leaves: a well-formed buffer with at least `thr` bits, the same bits as before with
the rest of the chunk, and the position in the input of the next bit unread (`8 * pos - count`) unchanged. -/
structure FillOk (a : ByteArray) (stop : USize) (word count : UInt64) (pos : USize) (thr : Nat) (w c : UInt64) (p : USize) :
    Prop where
  wf : (BitBuffer.mk w c).Wf
  enough : thr ≤ c.toNat
  posLe : pos.toNat ≤ p.toNat
  posStop : p.toNat ≤ stop.toNat
  bits : (BitBuffer.mk w c).held ++ chunkBits a p.toNat stop.toNat =
    (BitBuffer.mk word count).held ++ chunkBits a pos.toNat stop.toNat
  acct : 8 * p.toNat + count.toNat = 8 * pos.toNat + c.toNat

/-- Fills the buffer when it holds fewer than `thr` bits, by one 8-byte load: at least 8 bytes of the chunk are left. -/
@[inline] def fillK {α : Type} (a : ByteArray) (stop : USize) (hs : stop.toNat ≤ a.size) (word count : UInt64)
    (pos : USize) (thr : UInt64) (hw : (BitBuffer.mk word count).Wf) (ht : thr.toNat ≤ 56)
    (hp : pos.toNat ≤ stop.toNat) (hm : count.toNat < thr.toNat → pos.toNat + 8 ≤ stop.toNat)
    (k : (w c : UInt64) → (p : USize) → FillOk a stop word count pos thr.toNat w c p → α) : α :=
  if hc : count < thr then
    have hm := hm (UInt64.lt_iff_toNat_lt.mp hc)
    have hu : pos.toNat + 8 ≤ USize.size := by have := stop.toNat_lt_size; omega
    have hf := BitBuffer.fill_spec hw (Nat.le_trans (Nat.le_of_lt (UInt64.lt_iff_toNat_lt.mp hc)) ht) hm hs (by omega) hu
    k ((BitBuffer.mk word count).fill a pos (by omega) hu).1.word ((BitBuffer.mk word count).fill a pos (by omega) hu).1.count
      ((BitBuffer.mk word count).fill a pos (by omega) hu).2
      ⟨hf.1, by have := hf.2.1; omega, hf.2.2.1, hf.2.2.2.1, hf.2.2.2.2, by
        have e := congrArg List.length hf.2.2.2.2
        simp only [List.length_append, BitBuffer.held_length, chunkBits_length hs] at e
        have := hf.2.2.2.1
        have := hf.2.2.1
        have := hw.count_le
        have := hf.1.count_le
        rw [Nat.sub_mul, Nat.sub_mul] at e
        omega⟩
  else
    k word count pos ⟨hw, by have := UInt64.le_iff_toNat_le.mp (UInt64.not_lt.mp hc); exact this, Nat.le_refl _,
      by omega, rfl, rfl⟩

/-! ### Small positions -/

theorem fastShl {x : USize} {s : Nat} (hs : s < 32) (h : x.toNat * 2 ^ s < 2 ^ 32) :
    (x <<< USize.ofNat s).toNat = x.toNat * 2 ^ s := by
  have hsz := USize.le_size
  rw [USize.size_eq_two_pow] at hsz
  have hb : 32 ≤ System.Platform.numBits := by rcases System.Platform.numBits_eq with h | h <;> omega
  rw [USize.toNat_shiftLeft, fastLit (by omega), Nat.mod_eq_of_lt (by omega : s < System.Platform.numBits),
    Nat.shiftLeft_eq]
  exact Nat.mod_eq_of_lt (by omega)

theorem u8_usize (x : UInt8) : x.toUSize.toNat = x.toNat := by simp

theorem u8_shl2 (x : UInt8) : (x.toUSize <<< USize.ofNat 2).toNat = 4 * x.toNat := by
  have := x.toNat_lt
  rw [fastShl (by decide) (by rw [u8_usize]; omega), u8_usize]
  omega

/-! ### What the loop knows of its fixed values -/

/-- What the loop knows of the values fixed while it runs: the header matches a spec header, the arena `T` is the
header's, the block types are in range, and each row offset points at its type's row of the derived tables (`TabOk`):
`lRow` the resolved literal map, `iRow` the fused insert-and-copy entries, `iFb` (in 4-byte units) the insert-and-copy
tree's base, `dRow` the resolved distance map, `s0` the shared distance table. -/
structure FCtx (H : Hdr) (T : ByteArray) (lCur iCur dCur tb : UInt64) (modeOff lRow iRow iFb dRow s0 : USize) : Prop where
  hdr : ∃ m, HdrRel H m
  arena : T = H.arena
  hl : lCur.toNat < H.nL.toNat
  hi : iCur.toNat < H.nI.toNat
  hd : dCur.toNat < H.nD.toNat
  tbEq : tb = trivBase H lCur hl
  mode : modeOff.toNat = 512 * (H.modes.data[lCur.toNat]?.getD 0).toNat
  lRow : lRow.toNat = H.tabF0.toNat + 2048 * H.nI.toNat + 256 * lCur.toNat
  iRow : iRow.toNat = H.tabF0.toNat + 2048 * iCur.toNat
  iFb : 4 * iFb.toNat = H.tabF0.toNat + 2048 * H.nI.toNat + 256 * H.nL.toNat + 16 * H.nD.toNat + 4160 + 4 * iCur.toNat
  dRow : dRow.toNat = H.tabF0.toNat + 2048 * H.nI.toNat + 256 * H.nL.toNat + 16 * dCur.toNat
  s0 : s0.toNat = H.tabF0.toNat + 2048 * H.nI.toNat + 256 * H.nL.toNat + 16 * H.nD.toNat

section
variable {H : Hdr} {T : ByteArray} {lCur iCur dCur tb : UInt64} {modeOff lRow iRow iFb dRow s0 : USize}

theorem FCtx.tab (C : FCtx H T lCur iCur dCur tb modeOff lRow iRow iFb dRow s0) :
    TabOk T H.litBase H.lMap H.icBase H.dBase H.dMap H.lTriv H.nL.toNat H.nI.toNat H.nD.toNat H.treesL.toNat
      H.treesD.toNat H.npostfix H.ndirect H.tabF0.toNat := by
  obtain ⟨m, hm⟩ := C.hdr
  rw [C.arena]
  exact hm.tab

theorem FCtx.size32 (C : FCtx H T lCur iCur dCur tb modeOff lRow iRow iFb dRow s0) : T.size < 2 ^ 32 := C.tab.size32

theorem FCtx.sizeOk (C : FCtx H T lCur iCur dCur tb modeOff lRow iRow iFb dRow s0) :
    H.tabF0.toNat + 2048 * H.nI.toNat + 256 * H.nL.toNat + 16 * H.nD.toNat + 4160 + 4 * H.nI.toNat + 4 * H.nL.toNat ≤
      T.size := C.tab.sizeOk

/-- Every table lies within `tabF0 - 8`, and 6 bytes follow it: what `lookupT` needs. -/
theorem FCtx.lim (C : FCtx H T lCur iCur dCur tb modeOff lRow iRow iFb dRow s0) : H.tabF0.toNat - 8 + 6 ≤ T.size := by
  have := C.sizeOk
  have := C.tab.f0Ok
  omega

/-- A literal tree's number from the context map is below the number of trees. -/
theorem tree_byteN (H : Hdr) {J : Nat} (hJ : J < H.lMap.size) : byteN H.lMap J < H.treesL.toNat := by
  have h32 := H.lit.map32
  have hJu : (USize.ofNat J).toNat = J := fastLit (by omega)
  have := H.lit.treeLt (USize.ofNat J) (by rw [hJu]; exact hJ)
  rw [uget_toNat, hJu] at this
  exact this

/-- A resolved literal map's entry: the base of the context's tree, and that tree's table. -/
theorem FCtx.litIn (C : FCtx H T lCur iCur dCur tb modeOff lRow iRow iFb dRow s0) {cid : Nat} (hc : cid < 64) :
    leAt T (lRow.toNat + 4 * cid) 4 = u32At H.litBase (byteN H.lMap (64 * lCur.toNat + cid)) ∧
      TableIn T (u32At H.litBase (byteN H.lMap (64 * lCur.toNat + cid))) (H.tabF0.toNat - 8) := by
  have hl := C.hl
  have hJ : 64 * lCur.toNat + cid < H.lMap.size := by rw [H.lMapSize]; omega
  have e := C.tab.lres _ hJ
  rw [show H.tabF0.toNat + 2048 * H.nI.toNat + 4 * (64 * lCur.toNat + cid) = lRow.toNat + 4 * cid by
    rw [C.lRow]; omega] at e
  exact ⟨e, C.tab.lFit _ (tree_byteN H hJ)⟩

/-- The block type's context mode. -/
theorem FCtx.modeLt (C : FCtx H T lCur iCur dCur tb modeOff lRow iRow iFb dRow s0) :
    (H.modes.data[lCur.toNat]?.getD 0).toNat < 4 := by
  have hl := C.hl
  have h32 := H.lit.map32
  have hm := H.lMapSize
  have hu : (USize.ofNat lCur.toNat).toNat = lCur.toNat := fastLit (by omega)
  have := H.modesLt (USize.ofNat lCur.toNat) (by rw [hu, H.modesSize]; exact hl)
  rw [uget_toNat, hu] at this
  exact this

theorem FCtx.hm (C : FCtx H T lCur iCur dCur tb modeOff lRow iRow iFb dRow s0) : modeOff.toNat + 512 ≤ 2048 := by
  have := C.modeLt
  rw [C.mode]
  omega

theorem FCtx.hm512 (C : FCtx H T lCur iCur dCur tb modeOff lRow iRow iFb dRow s0) : modeOff.toNat % 512 = 0 := by
  rw [C.mode]
  omega

/-- The shared base of a block type whose contexts share one table. -/
theorem trivBase_toNat {H : Hdr} {t : UInt64} (ht : t.toNat < H.nL.toNat) :
    (trivBase H t ht).toNat = u32At H.lTriv t.toNat := by
  unfold trivBase
  rw [slotWord_toNat, cur_usize ht]

theorem FCtx.tbIn (C : FCtx H T lCur iCur dCur tb modeOff lRow iRow iFb dRow s0) (h : ¬ tb = 4294967295) :
    TableIn T tb.toUSize.toNat (H.tabF0.toNat - 8) := by
  have hv : tb.toNat = u32At H.lTriv lCur.toNat := by rw [C.tbEq, trivBase_toNat]
  have hne : u32At H.lTriv lCur.toNat ≠ 4294967295 := fun e => h (UInt64.toNat_inj.mp (by rw [hv, e]; rfl))
  rw [word_toUSize (by rw [hv]; exact u32At_lt _ _), hv]
  exact C.tab.trivFit _ C.hl hne

/-- The position of a context's entry in the resolved literal map. -/
theorem FCtx.litIdx (C : FCtx H T lCur iCur dCur tb modeOff lRow iRow iFb dRow s0) (cid : UInt8) (hc : cid.toNat < 64) :
    (lRow + (cid.toUSize <<< USize.ofNat 2)).toNat = lRow.toNat + 4 * cid.toNat ∧
      lRow.toNat + 4 * cid.toNat + 4 ≤ T.size := by
  have := C.sizeOk
  have := C.size32
  have := C.lRow
  have := C.hl
  rw [fastAdd (by rw [u8_shl2]; omega), u8_shl2]
  exact ⟨rfl, by omega⟩

/-- The table base of a literal's tree from the resolved map: the context's entry in the block type's row. -/
@[inline] def litRowBase (T : ByteArray) (lRow modeOff : USize) (p1 p2 : UInt8) (hm : modeOff.toNat + 512 ≤ 2048)
    (h : ∀ cid : UInt8, cid.toNat < 64 → (lRow + (cid.toUSize <<< USize.ofNat 2)).toNat + 4 ≤ T.size)
    (h32 : T.size < 2 ^ 32) (hd : modeOff.toNat % 512 = 0) : USize :=
  (load32 T (lRow + ((cidFast modeOff p1 p2 hm).toUSize <<< USize.ofNat 2)) (h _ (cid_lt hm hd)) h32).toUSize

theorem FCtx.rowIn (C : FCtx H T lCur iCur dCur tb modeOff lRow iRow iFb dRow s0) (p1 p2 : UInt8) :
    TableIn T (litRowBase T lRow modeOff p1 p2 C.hm (fun cid hc => by rw [(C.litIdx cid hc).1]; exact (C.litIdx cid hc).2)
      C.size32 C.hm512).toNat (H.tabF0.toNat - 8) := by
  have hc := cid_lt (p1 := p1) (p2 := p2) C.hm C.hm512
  unfold litRowBase
  rw [word_toUSize (by rw [load32_toNat]; exact Nat.lt_of_lt_of_le (leAt_lt _ _ 4) (by decide)), load32_toNat,
    (C.litIdx _ hc).1, (C.litIn hc).1]
  exact (C.litIn hc).2

/-- A literal's lookup: at the block type's shared base, or at its context's tree. -/
@[inline] def litT (C : FCtx H T lCur iCur dCur tb modeOff lRow iRow iFb dRow s0) (p1 p2 : UInt8) (w : UInt64) :
    UInt64 :=
  if h : tb = 4294967295 then
    lookupT T (litRowBase T lRow modeOff p1 p2 C.hm
      (fun cid hc => by rw [(C.litIdx cid hc).1]; exact (C.litIdx cid hc).2) C.size32 C.hm512) w (C.rowIn p1 p2) C.lim
      C.size32
  else lookupT T tb.toUSize w (C.tbIn h) C.lim C.size32

end

/-! ### Symbols in range -/

/-- A table for a complete code over `n` symbols gives, by one load, a symbol below `n`, whatever the bits. -/
theorem lookupT_sym {t : ByteArray} {base : USize} {lim : Nat} (hin : TableIn t base.toNat lim) (hl : lim + 6 ≤ t.size)
    (h32 : t.size < 2 ^ 32) {c : PrefixCode} {n : Nat} (hok : TableOk t base.toNat c) (hC : Complete c)
    (hS : c.Symbols n) (w : UInt64) : (wordSym (lookupT t base w hin hl h32)).toNat < n := by
  rw [lookupT_eq]
  have h15 := (lookup_read (b := ⟨w, 15⟩) hok (hin.fits (by omega)) h32 hC).1
  exact sym_lt hok _ h32 hC hS (cnt := 15) (UInt64.le_iff_toNat_le.mpr h15)

theorem distAlpha_le {np nd : Nat} (hp : np ≤ 3) (hd : nd ≤ 120) : distanceAlphabetSize np nd ≤ 520 := by
  unfold distanceAlphabetSize
  rw [Nat.shiftLeft_eq]
  have : 2 ^ np ≤ 2 ^ 3 := Nat.pow_le_pow_right (by decide) hp
  have h8 : (2 : Nat) ^ 3 = 8 := rfl
  omega

/-! ### Masks, pairs and the other rows -/

theorem and31 (n : UInt64) : (n &&& 31).toNat < 32 := by
  rw [UInt64.toNat_and, show (31 : UInt64).toNat = 2 ^ 5 - 1 from rfl, Nat.and_two_pow_sub_one_eq_mod]
  omega

theorem and255 (n : UInt64) : (n &&& 255).toNat < 256 := by
  rw [UInt64.toNat_and, show (255 : UInt64).toNat = 2 ^ 8 - 1 from rfl, Nat.and_two_pow_sub_one_eq_mod]
  omega

theorem u64_shl {x : UInt64} {s : Nat} (hs : s < 32) (h : x.toNat * 2 ^ s < 2 ^ 32) :
    (x.toUSize <<< USize.ofNat s).toNat = x.toNat * 2 ^ s := by
  have hx : x.toUSize.toNat = x.toNat := word_toUSize (by
    have : 1 ≤ 2 ^ s := Nat.one_le_two_pow
    exact Nat.lt_of_le_of_lt (Nat.le_mul_of_pos_right _ this) h)
  rw [fastShl hs (by rw [hx]; exact h), hx]

/-- The mask `2 ^ n - 1` for `n < 32` from the arena's first 256 bytes (`n` taken below 32). -/
@[inline] def maskT (T : ByteArray) (h : 256 ≤ T.size) (h32 : T.size < 2 ^ 32) (n : UInt64) : UInt64 :=
  load64 T ((n &&& 31).toUSize <<< USize.ofNat 3)
    (by have := and31 n; rw [u64_shl (by decide) (by omega)]; omega) h32

/-- The mask `2 ^ n - 1` from the arena's first 256 bytes, for an `n` known to be below 32: the index unmasked. -/
@[inline] def maskB (T : ByteArray) (h : 256 ≤ T.size) (h32 : T.size < 2 ^ 32) (n : UInt64) (hn : n.toNat < 32) :
    UInt64 :=
  load64 T (n.toUSize <<< USize.ofNat 3) (by rw [u64_shl (by decide) (by omega)]; omega) h32

theorem maskB_eq_maskT {T : ByteArray} {h : 256 ≤ T.size} {h32 : T.size < 2 ^ 32} {n : UInt64} {hn : n.toNat < 32} :
    maskB T h h32 n hn = maskT T h h32 n := by
  have h31 : n &&& 31 = n := UInt64.toNat_inj.mp (by
    rw [UInt64.toNat_and, show (31 : UInt64).toNat = 2 ^ 5 - 1 from rfl, Nat.and_two_pow_sub_one_eq_mod,
      Nat.mod_eq_of_lt hn])
  apply UInt64.toNat_inj.mp
  unfold maskB maskT
  rw [load64_toNat, load64_toNat, h31]

/-- An entry of 4 bytes of a row indexed by the next 8 bits. -/
@[inline] def row32 (T : ByteArray) (base : USize) (h : base.toNat + 1024 ≤ T.size) (h32 : T.size < 2 ^ 32) (w : UInt64) :
    UInt64 :=
  load32 T (base + ((w &&& 255).toUSize <<< USize.ofNat 2))
    (by
      have := and255 w
      rw [fastAdd (by rw [u64_shl (by decide) (by omega)]; omega), u64_shl (by decide) (by omega)]
      omega) h32

/-- An entry of 8 bytes of a row indexed by the next 8 bits. -/
@[inline] def row64 (T : ByteArray) (base : USize) (h : base.toNat + 2048 ≤ T.size) (h32 : T.size < 2 ^ 32) (w : UInt64) :
    UInt64 :=
  load64 T (base + ((w &&& 255).toUSize <<< USize.ofNat 3))
    (by
      have := and255 w
      rw [fastAdd (by rw [u64_shl (by decide) (by omega)]; omega), u64_shl (by decide) (by omega)]
      omega) h32

section
variable {H : Hdr} {T : ByteArray} {lCur iCur dCur tb : UInt64} {modeOff lRow iRow iFb dRow s0 : USize}

theorem FCtx.big (C : FCtx H T lCur iCur dCur tb modeOff lRow iRow iFb dRow s0) : 256 ≤ T.size := by
  have := C.sizeOk
  have := C.tab.f0Ok
  omega

theorem FCtx.iRowLe (C : FCtx H T lCur iCur dCur tb modeOff lRow iRow iFb dRow s0) : iRow.toNat + 2048 ≤ T.size := by
  have := C.sizeOk
  have := C.hi
  rw [C.iRow]
  omega

/-- The position of a distance context's entry in the resolved distance map. -/
theorem FCtx.dIdx (C : FCtx H T lCur iCur dCur tb modeOff lRow iRow iFb dRow s0) (clen : UInt64) :
    (dRow + ((distCid clen).toUSize <<< USize.ofNat 2)).toNat = dRow.toNat + 4 * distanceContextId clen.toNat ∧
      dRow.toNat + 4 * distanceContextId clen.toNat + 4 ≤ T.size := by
  have := C.sizeOk
  have := C.size32
  have := C.dRow
  have := C.hd
  have hc := distanceContextId_lt clen.toNat
  rw [fastAdd (by rw [u64_shl (by decide) (by rw [distCid_toNat]; omega)]; rw [distCid_toNat]; omega),
    u64_shl (by decide) (by rw [distCid_toNat]; omega), distCid_toNat]
  exact ⟨by omega, by omega⟩

/-- The table base of the distance tree for the copy length's context, from the resolved distance map. -/
@[inline] def dRowBase (C : FCtx H T lCur iCur dCur tb modeOff lRow iRow iFb dRow s0) (clen : UInt64) : USize :=
  (load32 T (dRow + ((distCid clen).toUSize <<< USize.ofNat 2))
    (by rw [(C.dIdx clen).1]; exact (C.dIdx clen).2) C.size32).toUSize

/-- A distance tree's number from the distance map is below the number of trees. -/
theorem tree_dMap (H : Hdr) {J : Nat} (hJ : J < H.dMap.size) : byteN H.dMap J < H.treesD.toNat := by
  have h32 := H.dMap32
  have hJu : (USize.ofNat J).toNat = J := fastLit (by omega)
  have := H.dMapLt (USize.ofNat J) (by rw [hJu]; exact hJ)
  rw [uget_toNat, hJu] at this
  exact this

theorem FCtx.dRowBase_toNat (C : FCtx H T lCur iCur dCur tb modeOff lRow iRow iFb dRow s0) (clen : UInt64) :
    (dRowBase C clen).toNat = u32At H.dBase (byteN H.dMap (4 * dCur.toNat + distanceContextId clen.toNat)) := by
  have hc := distanceContextId_lt clen.toNat
  have hd := C.hd
  have hJ : 4 * dCur.toNat + distanceContextId clen.toNat < H.dMap.size := by rw [H.dMapSize]; omega
  have e := C.tab.dres _ hJ
  unfold dRowBase
  rw [word_toUSize (by rw [load32_toNat]; exact Nat.lt_of_lt_of_le (leAt_lt _ _ 4) (by decide)), load32_toNat,
    (C.dIdx clen).1, ← e, C.dRow]
  congr 1
  omega

theorem FCtx.dIn (C : FCtx H T lCur iCur dCur tb modeOff lRow iRow iFb dRow s0) (clen : UInt64) :
    TableIn T (dRowBase C clen).toNat (H.tabF0.toNat - 8) := by
  have hc := distanceContextId_lt clen.toNat
  have hd := C.hd
  have hJ : 4 * dCur.toNat + distanceContextId clen.toNat < H.dMap.size := by rw [H.dMapSize]; omega
  rw [C.dRowBase_toNat]
  exact C.tab.dFit _ (tree_dMap H hJ)

/-- A distance symbol from the tree is in the distance alphabet, so below 520. -/
theorem FCtx.dSym (C : FCtx H T lCur iCur dCur tb modeOff lRow iRow iFb dRow s0) (clen w : UInt64) :
    (wordSym (lookupT T (dRowBase C clen) w (C.dIn clen) C.lim C.size32)).toNat < 520 := by
  have hc := distanceContextId_lt clen.toNat
  have hd := C.hd
  have hJ : 4 * dCur.toNat + distanceContextId clen.toNat < H.dMap.size := by rw [H.dMapSize]; omega
  obtain ⟨m, hm⟩ := C.hdr
  obtain ⟨code, _, hok, hC, hS⟩ := hm.d _ (tree_dMap H hJ)
  rw [← C.dRowBase_toNat, ← C.arena] at hok
  have := lookupT_sym (C.dIn clen) C.lim C.size32 hok hC hS w
  rw [← hm.npostfix, ← hm.ndirect] at this
  exact Nat.lt_of_lt_of_le this (distAlpha_le H.npLe H.ndLe)

theorem FCtx.s0Le (C : FCtx H T lCur iCur dCur tb modeOff lRow iRow iFb dRow s0) : s0.toNat + 4160 ≤ T.size := by
  have := C.sizeOk
  rw [C.s0]
  omega

/-- A distance symbol's entry in the shared distance table: its extra bits and its base distance. -/
@[inline] def dshT (T : ByteArray) (s0 : USize) (h : s0.toNat + 4160 ≤ T.size) (h32 : T.size < 2 ^ 32) (dc : UInt64)
    (hd : dc.toNat < 520) : UInt64 :=
  load64 T (s0 + (dc.toUSize <<< USize.ofNat 3))
    (by rw [fastAdd (by rw [u64_shl (by decide) (by omega)]; omega), u64_shl (by decide) (by omega)]; omega) h32

theorem FCtx.fbLe (C : FCtx H T lCur iCur dCur tb modeOff lRow iRow iFb dRow s0) : 4 * iFb.toNat + 4 ≤ T.size := by
  have := C.sizeOk
  have := C.hi
  rw [C.iFb]
  omega

/-- The insert-and-copy tree's base, for a code word the fused entries don't hold. -/
@[inline] def icFbBase (C : FCtx H T lCur iCur dCur tb modeOff lRow iRow iFb dRow s0) : USize :=
  (slotWord T iFb C.fbLe C.size32).toUSize

theorem FCtx.icFbBase_toNat (C : FCtx H T lCur iCur dCur tb modeOff lRow iRow iFb dRow s0) :
    (icFbBase C).toNat = u32At H.icBase iCur.toNat := by
  unfold icFbBase
  rw [word_toUSize (by rw [slotWord_toNat]; exact u32At_lt _ _), slotWord_toNat, ← leAt_u32, C.iFb]
  exact C.tab.ires _ C.hi

theorem FCtx.icIn (C : FCtx H T lCur iCur dCur tb modeOff lRow iRow iFb dRow s0) :
    TableIn T (icFbBase C).toNat (H.tabF0.toNat - 8) := by
  rw [C.icFbBase_toNat]
  exact C.tab.iFit _ C.hi

/-- An insert-and-copy symbol from the tree is below 704. -/
theorem FCtx.icSym (C : FCtx H T lCur iCur dCur tb modeOff lRow iRow iFb dRow s0) (w : UInt64) :
    (wordSym (lookupT T (icFbBase C) w C.icIn C.lim C.size32)).toNat < 704 := by
  obtain ⟨m, hm⟩ := C.hdr
  obtain ⟨code, _, hok, hC, hS⟩ := hm.ic _ C.hi
  rw [← C.icFbBase_toNat, ← C.arena] at hok
  exact lookupT_sym C.icIn C.lim C.size32 hok hC hS w

end

/-! ### Window stores and the copy -/

/-- A window index masked with the constant `0xFFFFFF`, which is no change (every window is at most `2 ^ 24` bytes) but
tells the C compiler the index is small, so that a byte store can't reach the array's reference count and the store's
exclusivity check isn't repeated (P25, `docs/lean-facts.md`). -/
@[inline] def wix (i : USize) : USize := i &&& USize.ofNat 0xFFFFFF

theorem wix_toNat {i : USize} (h : i.toNat < 2 ^ 24) : (wix i).toNat = i.toNat := by
  unfold wix
  rw [USize.toNat_and, fastLit (by decide), show 16777215 = 2 ^ 24 - 1 from rfl, Nat.and_two_pow_sub_one_eq_mod]
  exact Nat.mod_eq_of_lt h

theorem mask_lt {i mask : USize} {k : Nat} (hm : mask.toNat = 2 ^ k - 1) : (i &&& mask).toNat < 2 ^ k := by
  rw [USize.toNat_and, hm, Nat.and_two_pow_sub_one_eq_mod]
  exact Nat.mod_lt _ (Nat.two_pow_pos _)

/-- A store at a masked window position. -/
@[inline] def wput (ring : ByteArray) (i mask : USize) {k : Nat} (hk : k ≤ 24) (hm : mask.toNat = 2 ^ k - 1)
    (hs : ring.size = 2 ^ k) (v : UInt8) : ByteArray :=
  ring.uset (wix (i &&& mask)) v (by
    have := mask_lt (i := i) hm
    have : 2 ^ k ≤ 2 ^ 24 := Nat.pow_le_pow_right (by decide) hk
    rw [wix_toNat (by omega)]
    omega)

theorem wput_size (ring : ByteArray) (i mask : USize) {k : Nat} (hk : k ≤ 24) (hm : mask.toNat = 2 ^ k - 1)
    (hs : ring.size = 2 ^ k) (v : UInt8) : (wput ring i mask hk hm hs v).size = 2 ^ k := by
  unfold wput
  rw [size_uset']
  exact hs

/-- A load at a masked window position. -/
@[inline] def wget (ring : ByteArray) (i mask : USize) {k : Nat} (hm : mask.toNat = 2 ^ k - 1) (hs : ring.size = 2 ^ k) :
    UInt8 :=
  ring.uget (i &&& mask) (by have := mask_lt (i := i) hm; omega)

/-- A copy of `n` bytes from `s` to `d`, both masked, in byte order (so an overlap repeats bytes, as the format's copy
does). -/
def copyMasked (ring : ByteArray) (d s n mask : USize) {k : Nat} (hk : k ≤ 24) (hm : mask.toNat = 2 ^ k - 1)
    (hs : ring.size = 2 ^ k) : ByteArray :=
  if _hn : n = 0 then ring
  else
    copyMasked (wput ring d mask hk hm hs (wget ring s mask hm hs)) (d + USize.ofNat 1) (s + USize.ofNat 1)
      (n - USize.ofNat 1) mask hk hm (wput_size ring d mask hk hm hs _)
termination_by n.toNat
decreasing_by
  have := usize_pred _hn
  have := usize_ne _hn
  omega

theorem copyMasked_size {mask : USize} {k : Nat} (hk : k ≤ 24) (hm : mask.toNat = 2 ^ k - 1) :
    ∀ (N : Nat) (ring : ByteArray) (d s n : USize) (hs : ring.size = 2 ^ k), n.toNat = N →
      (copyMasked ring d s n mask hk hm hs).size = 2 ^ k := by
  intro N
  induction N with
  | zero =>
    intro ring d s n hs hN
    rw [copyMasked, dite_eq_left (usize_zero hN)]
    exact hs
  | succ N ih =>
    intro ring d s n hs hN
    have hn : n ≠ 0 := fun e => by rw [e] at hN; exact Nat.succ_ne_zero _ hN.symm
    rw [copyMasked, dite_eq_right hn]
    exact ih _ _ _ _ _ (by rw [usize_pred hn]; omega)

/-- Where a copy's source starts, and that its two 16-byte blocks don't overlap, at a distance of 16 or more that
doesn't wrap. -/
theorem copy16_ok {wpos d mask size : USize} {k : Nat} (hk : k ≤ 24) (hm : mask.toNat = 2 ^ k - 1)
    (hsz : size.toNat = 2 ^ k) (hd : d.toNat + 16 ≤ 2 ^ k) (h16 : 16 ≤ d.toNat)
    (j : Nat) (hwp : wpos.toNat + 32 ≤ 2 ^ k) :
    ((wpos - d) &&& mask).toNat + j + 16 ≤ wpos.toNat + j ∨ wpos.toNat + j + 16 ≤ ((wpos - d) &&& mask).toNat + j := by
  have hR : 2 ^ k ≤ 2 ^ 24 := Nat.pow_le_pow_right (by decide) hk
  have hU := USize.le_size
  rw [USize.size_eq_two_pow] at hU
  have hb : 32 ≤ System.Platform.numBits := by rcases System.Platform.numBits_eq with h | h <;> omega
  have hP : 2 ^ 32 ≤ 2 ^ System.Platform.numBits := Nat.pow_le_pow_right (by decide) hb
  rw [USize.toNat_and, hm, Nat.and_two_pow_sub_one_eq_mod]
  by_cases hle : d.toNat ≤ wpos.toNat
  · rw [USize.toNat_sub_of_le _ _ (USize.le_iff_toNat_le.mpr hle), Nat.mod_eq_of_lt (by omega)]
    omega
  · have hsub : (wpos - d).toNat = 2 ^ System.Platform.numBits - (d.toNat - wpos.toNat) := by
      rw [USize.toNat_sub, Nat.mod_eq_of_lt (by omega)]
      omega
    have e : (2 ^ System.Platform.numBits - (d.toNat - wpos.toNat)) % 2 ^ k = 2 ^ k - (d.toNat - wpos.toNat) := by
      have h1 : 2 ^ System.Platform.numBits = 2 ^ k * 2 ^ (System.Platform.numBits - k) := by
        rw [← Nat.pow_add, Nat.add_sub_cancel' (by omega)]
      have h2 : 1 ≤ 2 ^ (System.Platform.numBits - k) := Nat.one_le_two_pow
      rw [h1]
      have e2 : 2 ^ k * 2 ^ (System.Platform.numBits - k) - (d.toNat - wpos.toNat) =
          (2 ^ k - (d.toNat - wpos.toNat)) + 2 ^ k * (2 ^ (System.Platform.numBits - k) - 1) := by
        rw [Nat.mul_sub, Nat.mul_one]
        have : 2 ^ k ≤ 2 ^ k * 2 ^ (System.Platform.numBits - k) := Nat.le_mul_of_pos_right _ h2
        omega
      rw [e2, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt (by omega)]
    rw [hsub, e]
    omega

/-! ### Blocks of 8 -/

/-- A window of a known size, through stores that keep it. -/
abbrev Win (n : Nat) : Type := { w : ByteArray // w.size = n }

@[inline] def wst {n : Nat} (w : Win n) (i : USize) (v : UInt8) (h : i.toNat < n) : Win n :=
  ⟨w.1.uset i v (by rw [w.2]; exact h), by rw [size_uset']; exact w.2⟩

@[inline] def wld {n : Nat} (w : Win n) (i : USize) (h : i.toNat < n) : UInt8 := w.1.uget i (by rw [w.2]; exact h)

theorem idx8 {d : USize} {n i : Nat} (hd : d.toNat + 8 ≤ n) (h32 : n < 2 ^ 32) (hi : i < 8) :
    (d + USize.ofNat i).toNat < n := by
  rw [fastIdx_add (by omega)]
  omega

/-- A byte copied from `s` to `d`, the store's index masked (`wix`). -/
@[inline] def cp1 {n : Nat} (w : Win n) (d s : USize) (hd : d.toNat < n) (hs : s.toNat < n) (h24 : n ≤ 2 ^ 24) : Win n :=
  wst w (wix d) (wld w s hs) (by rw [wix_toNat (by omega)]; exact hd)

/-- 8 bytes copied one at a time from `s` to `d`, in order: with `s` fewer than 8 bytes before `d`, bytes the copy wrote
are read again, as the format's copy repeats them. -/
@[inline] def cp8 {n : Nat} (w : Win n) (d s : USize) (hd : d.toNat + 8 ≤ n) (hs : s.toNat + 8 ≤ n) (h24 : n ≤ 2 ^ 24) :
    Win n :=
  have h32 : n < 2 ^ 32 := by omega
  let w := cp1 w d s (by omega) (by omega) h24
  let w := cp1 w (d + USize.ofNat 1) (s + USize.ofNat 1) (idx8 hd h32 (by decide)) (idx8 hs h32 (by decide)) h24
  let w := cp1 w (d + USize.ofNat 2) (s + USize.ofNat 2) (idx8 hd h32 (by decide)) (idx8 hs h32 (by decide)) h24
  let w := cp1 w (d + USize.ofNat 3) (s + USize.ofNat 3) (idx8 hd h32 (by decide)) (idx8 hs h32 (by decide)) h24
  let w := cp1 w (d + USize.ofNat 4) (s + USize.ofNat 4) (idx8 hd h32 (by decide)) (idx8 hs h32 (by decide)) h24
  let w := cp1 w (d + USize.ofNat 5) (s + USize.ofNat 5) (idx8 hd h32 (by decide)) (idx8 hs h32 (by decide)) h24
  let w := cp1 w (d + USize.ofNat 6) (s + USize.ofNat 6) (idx8 hd h32 (by decide)) (idx8 hs h32 (by decide)) h24
  cp1 w (d + USize.ofNat 7) (s + USize.ofNat 7) (idx8 hd h32 (by decide)) (idx8 hs h32 (by decide)) h24

theorem win_size {n : Nat} (w : Win n) : w.1.size = n := w.2

/-- 8 bytes of `x` stored from `d`, lowest first. -/
@[inline] def put8At {n : Nat} (w : Win n) (d : USize) (x : UInt64) (hd : d.toNat + 8 ≤ n) (h32 : n < 2 ^ 32) : Win n :=
  let w := wst w d x.toUInt8 (by omega)
  let w := wst w (d + USize.ofNat 1) (x >>> 8).toUInt8 (idx8 hd h32 (by decide))
  let w := wst w (d + USize.ofNat 2) (x >>> 16).toUInt8 (idx8 hd h32 (by decide))
  let w := wst w (d + USize.ofNat 3) (x >>> 24).toUInt8 (idx8 hd h32 (by decide))
  let w := wst w (d + USize.ofNat 4) (x >>> 32).toUInt8 (idx8 hd h32 (by decide))
  let w := wst w (d + USize.ofNat 5) (x >>> 40).toUInt8 (idx8 hd h32 (by decide))
  let w := wst w (d + USize.ofNat 6) (x >>> 48).toUInt8 (idx8 hd h32 (by decide))
  wst w (d + USize.ofNat 7) (x >>> 56).toUInt8 (idx8 hd h32 (by decide))

/-- 8 bytes of `x` stored from `d`, lowest first, the base index masked once (`wix`). -/
@[inline] def put8 {n : Nat} (w : Win n) (d : USize) (x : UInt64) (hd : d.toNat + 8 ≤ n) (h24 : n ≤ 2 ^ 24) : Win n :=
  put8At w (wix d) x (by rw [wix_toNat (by omega)]; exact hd) (by omega)

/-- A block of 8 of the format's copy at distance `dist`: one 8-byte load when the distance is at least 8 (so the block
reads no byte it writes), byte by byte otherwise. -/
@[inline] def blk8 {n : Nat} (w : Win n) (d s dist : USize) (hd : d.toNat + 8 ≤ n) (hs : s.toNat + 8 ≤ n)
    (h24 : n ≤ 2 ^ 24) : Win n :=
  if dist < USize.ofNat 8 then cp8 w d s hd hs h24
  else put8 w d (load64 w.1 s (by rw [w.2]; exact hs) (by rw [w.2]; omega)) hd h24

/-- The format's copy of `n` bytes from `d` back to `wpos`, `d` within the window: two 16-byte blocks at a distance of
16 or more, up to 32 bytes; one `memmove` at a distance of at least the length, beyond 32 bytes; blocks of 8 up to 32
bytes otherwise; the masked byte loop when the copy wraps or is long and overlapping. The blocks write up to 15 bytes
past the copy, in the window's slack. The tests choose how; none is redundant. -/
@[inline] def copyF (ring : ByteArray) (wpos d n mask size : USize) {k : Nat} (hk : k ≤ 24) (hm : mask.toNat = 2 ^ k - 1)
    (hsz : size.toNat = 2 ^ k) (hs : ring.size = 2 ^ k) (hw : wpos.toNat < 2 ^ k) (hd : d.toNat + 16 ≤ 2 ^ k) :
    ByteArray :=
  let s := (wpos - d) &&& mask
  have hsl : s.toNat < 2 ^ k := mask_lt hm
  have hR : 2 ^ k ≤ 2 ^ 24 := Nat.pow_le_pow_right (by decide) hk
  if h : USize.ofNat 16 ≤ d ∧ n ≤ USize.ofNat 32 ∧ s + USize.ofNat 32 ≤ size ∧ wpos + USize.ofNat 32 ≤ size then
    have h16 : 16 ≤ d.toNat := by have := USize.le_iff_toNat_le.mp h.1; rwa [fastLit (by decide)] at this
    have hs32 : s.toNat + 32 ≤ 2 ^ k := by
      have := USize.le_iff_toNat_le.mp h.2.2.1; rwa [fastIdx_add (by omega), hsz] at this
    have hw32 : wpos.toNat + 32 ≤ 2 ^ k := by
      have := USize.le_iff_toNat_le.mp h.2.2.2; rwa [fastIdx_add (by omega), hsz] at this
    have hsep0 := copy16_ok hk hm hsz hd h16 0 hw32
    let r := winCopy16 ring wpos s ⟨by omega, by omega, by omega⟩
    if n ≤ USize.ofNat 16 then r
    else
      have hsep1 := copy16_ok hk hm hsz hd h16 16 hw32
      winCopy16 r (wpos + USize.ofNat 16) (s + USize.ofNat 16)
        (by
          rw [fastIdx_add (by omega), fastIdx_add (by omega), winCopy16_size]
          exact ⟨by omega, by omega, by omega⟩)
  else if h2 : USize.ofNat 32 < n ∧ n ≤ d ∧ s + n ≤ size ∧ wpos + n ≤ size then
    winMove ring wpos s n
      (by
        have hnd := USize.le_iff_toNat_le.mp h2.2.1
        have e1 := USize.le_iff_toNat_le.mp h2.2.2.1
        have e2 := USize.le_iff_toNat_le.mp h2.2.2.2
        rw [fastAdd (by omega), hsz] at e1
        rw [fastAdd (by omega), hsz] at e2
        exact ⟨by omega, by omega⟩)
  else if h3 : n ≤ USize.ofNat 32 ∧ s + USize.ofNat 32 ≤ size ∧ wpos + USize.ofNat 32 ≤ size then
    have hs32 : s.toNat + 32 ≤ 2 ^ k := by
      have := USize.le_iff_toNat_le.mp h3.2.1; rwa [fastIdx_add (by omega), hsz] at this
    have hw32 : wpos.toNat + 32 ≤ 2 ^ k := by
      have := USize.le_iff_toNat_le.mp h3.2.2; rwa [fastIdx_add (by omega), hsz] at this
    let w1 := blk8 ⟨ring, hs⟩ wpos s d (by omega) (by omega) hR
    if n ≤ USize.ofNat 8 then w1.1
    else
    let w2 := blk8 w1 (wpos + USize.ofNat 8) (s + USize.ofNat 8) d (by rw [fastIdx_add (by omega)]; omega)
      (by rw [fastIdx_add (by omega)]; omega) hR
    if n ≤ USize.ofNat 16 then w2.1
    else
    let w3 := blk8 w2 (wpos + USize.ofNat 16) (s + USize.ofNat 16) d (by rw [fastIdx_add (by omega)]; omega)
      (by rw [fastIdx_add (by omega)]; omega) hR
    if n ≤ USize.ofNat 24 then w3.1
    else
    (blk8 w3 (wpos + USize.ofNat 24) (s + USize.ofNat 24) d (by rw [fastIdx_add (by omega)]; omega)
      (by rw [fastIdx_add (by omega)]; omega) hR).1
  else copyMasked ring wpos s n mask hk hm hs

theorem copyF_size (ring : ByteArray) (wpos d n mask size : USize) {k : Nat} (hk : k ≤ 24)
    (hm : mask.toNat = 2 ^ k - 1) (hsz : size.toNat = 2 ^ k) (hs : ring.size = 2 ^ k) (hw : wpos.toNat < 2 ^ k)
    (hd : d.toNat + 16 ≤ 2 ^ k) : (copyF ring wpos d n mask size hk hm hsz hs hw hd).size = 2 ^ k := by
  unfold copyF
  dsimp only
  split
  · split
    · rw [winCopy16_size]; exact hs
    · rw [winCopy16_size, winCopy16_size]; exact hs
  · split
    · rw [winMove_size]; exact hs
    · split
      · split
        · exact win_size _
        · split
          · exact win_size _
          · split
            · exact win_size _
            · exact win_size _
      · exact copyMasked_size hk hm _ _ _ _ _ hs rfl

/-! ### Bits taken -/

theorem and15_lt (v : UInt64) : (v &&& 15).toNat < 16 := by
  rw [UInt64.toNat_and, show (15 : UInt64).toNat = 2 ^ 4 - 1 from rfl, Nat.and_two_pow_sub_one_eq_mod]
  omega

theorem and63_lt (v : UInt64) : (v &&& 63).toNat < 64 := by
  rw [UInt64.toNat_and, show (63 : UInt64).toNat = 2 ^ 6 - 1 from rfl, Nat.and_two_pow_sub_one_eq_mod]
  omega

theorem u64_add_small {a b : UInt64} (h : a.toNat + b.toNat < 2 ^ 64) : (a + b).toNat = a.toNat + b.toNat := by
  rw [UInt64.toNat_add]
  exact Nat.mod_eq_of_lt h

theorem drop1_wf {w c a : UInt64} (hw : (BitBuffer.mk w c).Wf) (ha : a.toNat < 64) (h : a.toNat ≤ c.toNat) :
    (BitBuffer.mk (w >>> a) (c - a)).Wf :=
  BitBuffer.drop_wf hw ha h

theorem u64_sub_le {a b : UInt64} (h : b.toNat ≤ a.toNat) : (a - b).toNat = a.toNat - b.toNat :=
  UInt64.toNat_sub_of_le _ _ (UInt64.le_iff_toNat_le.mpr h)

theorem drop2_wf {w c a b : UInt64} (hw : (BitBuffer.mk w c).Wf) (ha : a.toNat < 64) (hb : b.toNat < 64)
    (h : a.toNat + b.toNat ≤ c.toNat) : (BitBuffer.mk ((w >>> a) >>> b) (c - a - b)).Wf := by
  have h1 := drop1_wf hw ha (by omega)
  have e1 : (c - a).toNat = c.toNat - a.toNat := u64_sub_le (by omega)
  exact drop1_wf h1 hb (by rw [e1]; omega)

theorem drop3_wf {w c a b d : UInt64} (hw : (BitBuffer.mk w c).Wf) (ha : a.toNat < 64) (hb : b.toNat < 64)
    (hd : d.toNat < 64) (h : a.toNat + b.toNat + d.toNat ≤ c.toNat) :
    (BitBuffer.mk (((w >>> a) >>> b) >>> d) (c - a - b - d)).Wf := by
  have h2 := drop2_wf hw ha hb (by omega)
  have e1 : (c - a).toNat = c.toNat - a.toNat := u64_sub_le (by omega)
  have e2 : (c - a - b).toNat = c.toNat - a.toNat - b.toNat := by rw [u64_sub_le (by rw [e1]; omega), e1]
  exact drop1_wf h2 hd (by rw [e2]; omega)

/-- A short distance code's distance (codes below 16), branch-free: which last distance (two bits a code in
`0x555000E4`) plus an offset (`0x6051426051423333`, four bits a code, offset + 3). A value the spec rejects comes out 0
or past the bytes written, and the loop leaves at either. -/
@[inline] def shortFast (d0 d1 d2 d3 dcode : UInt64) : UInt64 :=
  let idx := ((0x555000E4 : UInt64) >>> (dcode <<< 1)) &&& 3
  let odd := idx &&& 1 = 1
  let lo := if odd then d1 else d0
  let hi := if odd then d3 else d2
  let base := if idx &&& 2 = 2 then hi else lo
  base + (((0x6051426051423333 : UInt64) >>> (dcode <<< 2)) &&& 15) - 3

section
variable {H : Hdr} {T : ByteArray} {lCur iCur dCur tb : UInt64} {modeOff lRow iRow iFb dRow s0 : USize}

/-- Head 2's explicit distance: the tree for the copy length's context, the symbol, and the distance, by the short
codes or by the shared table and the extra bits; with whether the buffer held the bits. -/
@[inline] def distK {α : Type} (C : FCtx H T lCur iCur dCur tb modeOff lRow iRow iFb dRow s0) (np : UInt64)
    (word count clen d0 d1 d2 d3 : UInt64) (hw : (BitBuffer.mk word count).Wf)
    (k : (ok : Bool) → (w c dcode d : UInt64) → (ok = true → (BitBuffer.mk w c).Wf) → α) : α :=
  let v := lookupT T (dRowBase C clen) word (C.dIn clen) C.lim C.size32
  let l := v &&& 15
  let dcode := wordSym v
  let w1 := word >>> l
  have hl : l.toNat < 16 := and15_lt v
  if dcode < 16 then
    k (decide (l ≤ count)) w1 (count - l) dcode (shortFast d0 d1 d2 d3 dcode)
      (fun h => drop1_wf hw (by omega) (UInt64.le_iff_toNat_le.mp (of_decide_eq_true h)))
  else
    let e := dshT T s0 C.s0Le C.size32 dcode (C.dSym clen word)
    let nb := e &&& 31
    have hnb : nb.toNat < 32 := and31 e
    k (decide (l + nb ≤ count)) (w1 >>> nb) (count - l - nb) dcode ((e >>> 32) + ((w1 &&& maskT T C.big C.size32 nb) <<< np))
      (fun h => by
        have h1 := UInt64.le_iff_toNat_le.mp (of_decide_eq_true h)
        rw [u64_add_small (by omega)] at h1
        exact drop2_wf hw (by omega) (by omega) h1)

/-! ### The fused insert-and-copy entry's fields -/

theorem insertRow_bits24 {c : UInt64} (hc : c.toNat < 704) : (rowBits (insertRow c hc)).toNat ≤ 24 := by
  have h1 := (insertRow_fields hc).1
  have h2 := (cmdRow_small hc).1
  omega

theorem or_shl_toNat {a b s : UInt64} {k P : Nat} (hs : s.toNat = k) (hk : k < 64) (hP : 2 ^ k = P)
    (ha : a.toNat < P) (hb : P * b.toNat < 18446744073709551616) : (a ||| (b <<< s)).toNat = a.toNat + P * b.toNat := by
  subst hP
  have h64 : (2 : Nat) ^ 64 = 18446744073709551616 := rfl
  have hsh : (b <<< s).toNat = 2 ^ k * b.toNat := by
    rw [UInt64.toNat_shiftLeft, hs, Nat.mod_eq_of_lt hk, Nat.shiftLeft_eq, Nat.mul_comm]
    exact Nat.mod_eq_of_lt (by omega)
  rw [UInt64.toNat_or, hsh, Nat.or_comm, ← Nat.two_pow_add_eq_or_of_lt ha, Nat.add_comm]

/-- An entry that isn't 255 in its low byte is the fused entry of a root slot holding a code word of at most 8 bits and
a symbol below 704. -/
theorem icEntryU_fused {v j : UInt64} (h : icEntryU v j &&& 255 ≠ 255) :
    ∃ (_ : v &&& 15 ≤ 8) (hs : ((v >>> 4) &&& 4095).toNat < 704),
      icEntryU v j = icEntryOf (v &&& 15) ((v >>> 4) &&& 4095) j hs := by
  unfold icEntryU at h ⊢
  split
  · rename_i hc
    exact ⟨hc.1, lt704 hc.2, rfl⟩
  · rename_i hc
    rw [dite_eq_right hc] at h
    exact absurd (by decide) h

/-- The fields of a fused entry, each read as a whole byte or more: the symbol's class, and either the bits taken with
both lengths, or the code word's bits, both extra bits and both lengths' lowest values. -/
theorem icEntryOf_split {l sym j : UInt64} (hs : sym.toNat < 704) (hl : l.toNat ≤ 8) (hj : j.toNat < 256) :
    (icEntryOf l sym j hs >>> 8) &&& 255 = codeClass sym ∧
    (l + rowBits (insertRow sym hs) + rowBits (copyRow sym hs) ≤ 8 →
      icEntryOf l sym j hs &&& 255 = l + rowBits (insertRow sym hs) + rowBits (copyRow sym hs) ∧
      (icEntryOf l sym j hs >>> 16) &&& 255 = 0 ∧ (icEntryOf l sym j hs >>> 24) &&& 255 = 0 ∧
      (icEntryOf l sym j hs >>> 32) &&& 0xFFFF =
        rowBase (insertRow sym hs) + ((j >>> l) &&& (((1 : UInt64) <<< rowBits (insertRow sym hs)) - 1)) ∧
      icEntryOf l sym j hs >>> 48 = rowBase (copyRow sym hs) +
        ((j >>> (l + rowBits (insertRow sym hs))) &&& (((1 : UInt64) <<< rowBits (copyRow sym hs)) - 1))) ∧
    (¬ l + rowBits (insertRow sym hs) + rowBits (copyRow sym hs) ≤ 8 →
      icEntryOf l sym j hs &&& 255 = l ∧ (icEntryOf l sym j hs >>> 16) &&& 255 = rowBits (insertRow sym hs) ∧
      (icEntryOf l sym j hs >>> 24) &&& 255 = rowBits (copyRow sym hs) ∧
      (icEntryOf l sym j hs >>> 32) &&& 0xFFFF = rowBase (insertRow sym hs) ∧
      icEntryOf l sym j hs >>> 48 = rowBase (copyRow sym hs)) := by
  have hib : (rowBits (insertRow sym hs)).toNat ≤ 24 := insertRow_bits24 hs
  have hcb : (rowBits (copyRow sym hs)).toNat ≤ 24 := copyRow_bits hs
  have hibase : (rowBase (insertRow sym hs)).toNat ≤ 22594 := by
    rw [(insertRow_fields hs).2]; exact (cmdRow_small hs).2.1
  have hcbase : (rowBase (copyRow sym hs)).toNat ≤ 2118 := by
    rw [(copyRow_fields hs).2]; exact (cmdRow_small hs).2.2.2
  unfold icEntryOf
  dsimp only
  generalize rowBits (insertRow sym hs) = ib at *
  generalize rowBits (copyRow sym hs) = cb at *
  generalize rowBase (insertRow sym hs) = ibase at *
  generalize rowBase (copyRow sym hs) = cbase at *
  have hcc := codeClass_le sym
  generalize codeClass sym = cc at *
  have f8 : ∀ e : UInt64, ((e >>> 8) &&& 255).toNat = e.toNat / 256 % 256 := fun e => by
    rw [UInt64.toNat_and, UInt64.toNat_shiftRight]
    show e.toNat >>> 8 &&& (2 ^ 8 - 1) = _
    rw [Nat.and_two_pow_sub_one_eq_mod, Nat.shiftRight_eq_div_pow]
  have f16 : ∀ e : UInt64, ((e >>> 16) &&& 255).toNat = e.toNat / 65536 % 256 := fun e => by
    rw [UInt64.toNat_and, UInt64.toNat_shiftRight]
    show e.toNat >>> 16 &&& (2 ^ 8 - 1) = _
    rw [Nat.and_two_pow_sub_one_eq_mod, Nat.shiftRight_eq_div_pow]
  have f24 : ∀ e : UInt64, ((e >>> 24) &&& 255).toNat = e.toNat / 16777216 % 256 := fun e => by
    rw [UInt64.toNat_and, UInt64.toNat_shiftRight]
    show e.toNat >>> 24 &&& (2 ^ 8 - 1) = _
    rw [Nat.and_two_pow_sub_one_eq_mod, Nat.shiftRight_eq_div_pow]
  have f32 : ∀ e : UInt64, ((e >>> 32) &&& 0xFFFF).toNat = e.toNat / 4294967296 % 65536 := fun e => by
    rw [UInt64.toNat_and, UInt64.toNat_shiftRight]
    show e.toNat >>> 32 &&& (2 ^ 16 - 1) = _
    rw [Nat.and_two_pow_sub_one_eq_mod, Nat.shiftRight_eq_div_pow]
  have f48 : ∀ e : UInt64, (e >>> 48).toNat = e.toNat / 281474976710656 := fun e => by
    rw [UInt64.toNat_shiftRight]
    show e.toNat >>> 48 = _
    rw [Nat.shiftRight_eq_div_pow]
  have f0 : ∀ e : UInt64, (e &&& 255).toNat = e.toNat % 256 := fun e => by
    rw [UInt64.toNat_and]
    show e.toNat &&& (2 ^ 8 - 1) = _
    rw [Nat.and_two_pow_sub_one_eq_mod]
  have h0 : (0 : UInt64).toNat = 0 := rfl
  by_cases hr : l + ib + cb ≤ 8
  · rw [ite_eq_left hr]
    have hA : (l + ib + cb).toNat = l.toNat + ib.toNat + cb.toNat := by
      rw [u64_add_small (by rw [u64_add_small (by omega)]; omega), u64_add_small (by omega)]
    have hr' : (l + ib + cb).toNat ≤ 8 := UInt64.le_iff_toNat_le.mp hr
    rw [hA] at hr'
    have hb1 : ((j >>> l) &&& (((1 : UInt64) <<< ib) - 1)).toNat < 256 := by
      rw [UInt64.toNat_and]
      refine Nat.lt_of_le_of_lt Nat.and_le_left ?_
      rw [UInt64.toNat_shiftRight, Nat.shiftRight_eq_div_pow]
      exact Nat.lt_of_le_of_lt (Nat.div_le_self _ _) hj
    have hb2 : ((j >>> (l + ib)) &&& (((1 : UInt64) <<< cb) - 1)).toNat < 256 := by
      rw [UInt64.toNat_and]
      refine Nat.lt_of_le_of_lt Nat.and_le_left ?_
      rw [UInt64.toNat_shiftRight, Nat.shiftRight_eq_div_pow]
      exact Nat.lt_of_le_of_lt (Nat.div_le_self _ _) hj
    generalize (j >>> l) &&& (((1 : UInt64) <<< ib) - 1) = M1 at *
    generalize (j >>> (l + ib)) &&& (((1 : UInt64) <<< cb) - 1) = M2 at *
    have hX : (ibase + M1).toNat = ibase.toNat + M1.toNat := u64_add_small (by omega)
    have hY : (cbase + M2).toNat = cbase.toNat + M2.toNat := u64_add_small (by omega)
    have e1 := or_shl_toNat (a := l + ib + cb) (b := cc) (s := 8) (P := 256) rfl (by decide) rfl (by omega)
      (by omega)
    have e2 := or_shl_toNat (a := (l + ib + cb) ||| (cc <<< 8)) (b := ibase + M1) (s := 32) (P := 4294967296) rfl
      (by decide) rfl (by rw [e1]; omega) (by omega)
    have e3 := or_shl_toNat (a := (l + ib + cb) ||| (cc <<< 8) ||| ((ibase + M1) <<< 32)) (b := cbase + M2) (s := 48)
      (P := 281474976710656) rfl (by decide) rfl (by rw [e2, e1]; omega) (by omega)
    rw [e2, e1, hA, hX, hY] at e3
    refine ⟨UInt64.toNat_inj.mp (by rw [f8, e3]; omega), fun _ => ⟨?_, ?_, ?_, ?_, ?_⟩,
      fun h => absurd hr h⟩
    · exact UInt64.toNat_inj.mp (by rw [f0, e3, hA]; omega)
    · exact UInt64.toNat_inj.mp (by rw [f16, e3, h0]; omega)
    · exact UInt64.toNat_inj.mp (by rw [f24, e3, h0]; omega)
    · exact UInt64.toNat_inj.mp (by rw [f32, e3]; omega)
    · exact UInt64.toNat_inj.mp (by rw [f48, e3]; omega)
  · rw [ite_eq_right hr]
    have e1 := or_shl_toNat (a := l) (b := cc) (s := 8) (P := 256) rfl (by decide) rfl (by omega) (by omega)
    have e2 := or_shl_toNat (a := l ||| (cc <<< 8)) (b := ib) (s := 16) (P := 65536) rfl (by decide) rfl
      (by rw [e1]; omega) (by omega)
    have e3 := or_shl_toNat (a := l ||| (cc <<< 8) ||| (ib <<< 16)) (b := cb) (s := 24) (P := 16777216) rfl
      (by decide) rfl (by rw [e2, e1]; omega) (by omega)
    have e4 := or_shl_toNat (a := l ||| (cc <<< 8) ||| (ib <<< 16) ||| (cb <<< 24)) (b := ibase) (s := 32)
      (P := 4294967296) rfl (by decide) rfl (by rw [e3, e2, e1]; omega) (by omega)
    have e5 := or_shl_toNat (a := l ||| (cc <<< 8) ||| (ib <<< 16) ||| (cb <<< 24) ||| (ibase <<< 32)) (b := cbase)
      (s := 48) (P := 281474976710656) rfl (by decide) rfl (by rw [e4, e3, e2, e1]; omega) (by omega)
    rw [e4, e3, e2, e1] at e5
    refine ⟨UInt64.toNat_inj.mp (by rw [f8, e5]; omega), fun h => absurd h hr, fun _ => ⟨?_, ?_, ?_, ?_, ?_⟩⟩
    · exact UInt64.toNat_inj.mp (by rw [f0, e5]; omega)
    · exact UInt64.toNat_inj.mp (by rw [f16, e5]; omega)
    · exact UInt64.toNat_inj.mp (by rw [f24, e5]; omega)
    · exact UInt64.toNat_inj.mp (by rw [f32, e5]; omega)
    · exact UInt64.toNat_inj.mp (by rw [f48, e5]; omega)

/-- The fused entry the loop loads is the block type's entry for the next 8 bits. -/
theorem FCtx.row64_eq (C : FCtx H T lCur iCur dCur tb modeOff lRow iRow iFb dRow s0) (w : UInt64) :
    row64 T iRow C.iRowLe C.size32 w =
      icEntryU (UInt64.ofNat (slotNum T (u32At H.icBase iCur.toNat + w.toNat % 256))) (UInt64.ofNat (w.toNat % 256)) := by
  have h32 := C.size32
  have hle := C.iRowLe
  have hj : w.toNat % 256 < 256 := Nat.mod_lt _ (by decide)
  have h255 : (w &&& 255).toNat = w.toNat % 256 := by
    rw [UInt64.toNat_and]
    exact Nat.and_two_pow_sub_one_eq_mod w.toNat 8
  have e := C.tab.ic _ C.hi _ hj
  apply UInt64.toNat_inj.mp
  unfold row64
  rw [load64_toNat, fastAdd (by rw [u64_shl (by decide) (by rw [h255]; omega)]; rw [h255]; omega),
    u64_shl (by decide) (by rw [h255]; omega), h255, C.iRow,
    show w.toNat % 256 * 2 ^ 3 = 8 * (w.toNat % 256) by rw [Nat.mul_comm], e]

/-- A fused entry's bits taken are at most 8 and its extra bits at most 24 each: so the loop reads them as whole bytes
and indexes the masks with them unmasked. -/
theorem FCtx.icBytes (C : FCtx H T lCur iCur dCur tb modeOff lRow iRow iFb dRow s0) (w : UInt64)
    (hne : ¬ row64 T iRow C.iRowLe C.size32 w &&& 255 = 255) :
    (row64 T iRow C.iRowLe C.size32 w &&& 255).toNat ≤ 8 ∧
      ((row64 T iRow C.iRowLe C.size32 w >>> 16) &&& 255).toNat ≤ 24 ∧
      ((row64 T iRow C.iRowLe C.size32 w >>> 24) &&& 255).toNat ≤ 24 := by
  rw [C.row64_eq w] at hne ⊢
  obtain ⟨hl8, hs, hEo⟩ := icEntryU_fused hne
  rw [hEo]
  have hl : (UInt64.ofNat (slotNum T (u32At H.icBase iCur.toNat + w.toNat % 256)) &&& 15).toNat ≤ 8 :=
    UInt64.le_iff_toNat_le.mp hl8
  have hw : w.toNat % 256 < 256 := Nat.mod_lt _ (by decide)
  have hj : (UInt64.ofNat (w.toNat % 256)).toNat < 256 := by
    rw [UInt64.toNat_ofNat']
    exact Nat.lt_of_le_of_lt (Nat.mod_le _ _) hw
  obtain ⟨_, hres, hunres⟩ := icEntryOf_split hs hl hj
  have hib := insertRow_bits24 hs
  have hcb := copyRow_bits hs
  by_cases hr : (UInt64.ofNat (slotNum T (u32At H.icBase iCur.toNat + w.toNat % 256)) &&& 15) +
      rowBits (insertRow _ hs) + rowBits (copyRow _ hs) ≤ 8
  · obtain ⟨f1, f2, f3, _, _⟩ := hres hr
    have hr' : (_ : UInt64).toNat ≤ (8 : UInt64).toNat := UInt64.le_iff_toNat_le.mp hr
    rw [f1, f2, f3]
    exact ⟨hr', by decide, by decide⟩
  · obtain ⟨f1, f2, f3, _, _⟩ := hunres hr
    rw [f1, f2, f3]
    exact ⟨hl, hib, hcb⟩

/-- Head 1: the insert-and-copy symbol and both lengths, from the fused entry (one 8-byte load, each field a whole
byte, the masks indexed unmasked) or, for a code word longer than 8 bits, from the tree; with whether the buffer held
the bits. -/
@[inline] def icK {α : Type} (C : FCtx H T lCur iCur dCur tb modeOff lRow iRow iFb dRow s0) (word count : UInt64)
    (hw : (BitBuffer.mk word count).Wf)
    (k : (ok : Bool) → (w c code ilen clen : UInt64) → (ok = true → (BitBuffer.mk w c).Wf) → α) : α :=
  let e := row64 T iRow C.iRowLe C.size32 word
  if hne : e &&& 255 = 255 then
    let v := lookupT T (icFbBase C) word C.icIn C.lim C.size32
    let l := v &&& 15
    let sym := wordSym v
    have hc : sym.toNat < 704 := C.icSym word
    let row := insertRow sym hc
    let cr := copyRow sym hc
    let ib := rowBits row
    let cb := rowBits cr
    let w1 := word >>> l
    let ilen := rowBase row + (w1 &&& maskT T C.big C.size32 ib)
    let w2 := w1 >>> ib
    let clen := rowBase cr + (w2 &&& maskT T C.big C.size32 cb)
    have hl : l.toNat < 16 := and15_lt v
    have hib : ib.toNat < 64 := insertRow_bits hc
    have hcb : cb.toNat ≤ 24 := copyRow_bits hc
    k (decide (l + ib + cb ≤ count)) (w2 >>> cb) (count - l - ib - cb) (codeClass sym) ilen clen
      (fun h => by
        have h1 := UInt64.le_iff_toNat_le.mp (of_decide_eq_true h)
        rw [u64_add_small (by rw [u64_add_small (by omega)]; omega), u64_add_small (by omega)] at h1
        exact drop3_wf hw (by omega) (by omega) (by omega) h1)
  else
    have hb := C.icBytes word hne
    let l := e &&& 255
    let ib := (e >>> 16) &&& 255
    let cb := (e >>> 24) &&& 255
    have hl : l.toNat < 16 := Nat.lt_of_le_of_lt hb.1 (by decide)
    have hib : ib.toNat < 32 := Nat.lt_of_le_of_lt hb.2.1 (by decide)
    have hcb : cb.toNat < 32 := Nat.lt_of_le_of_lt hb.2.2 (by decide)
    let w1 := word >>> l
    let ilen := ((e >>> 32) &&& 0xFFFF) + (w1 &&& maskB T C.big C.size32 ib hib)
    let w2 := w1 >>> ib
    let clen := (e >>> 48) + (w2 &&& maskB T C.big C.size32 cb hcb)
    k (decide (l + ib + cb ≤ count)) (w2 >>> cb) (count - l - ib - cb) ((e >>> 8) &&& 255) ilen clen
      (fun h => by
        have h1 := UInt64.le_iff_toNat_le.mp (of_decide_eq_true h)
        rw [u64_add_small (by rw [u64_add_small (by omega)]; omega), u64_add_small (by omega)] at h1
        exact drop3_wf hw (by omega) (by omega) (by omega) h1)

end

/-! ### The loop -/

/-- What the loop knows of its window and input while it runs: the window's size and mask, its size less the slack,
the margin (`posLim` is 40 bytes before the chunk's end), the two-literal table's place, and the header's `NPOSTFIX`. -/
structure FWin (H : Hdr) (T : ByteArray) (kk mask size cap16 posLim stop pairBase : USize) (np : UInt64) : Prop where
  k24 : kk.toNat ≤ 24
  k16 : 16 ≤ 2 ^ kk.toNat
  mask : mask.toNat = 2 ^ kk.toNat - 1
  size : size.toNat = 2 ^ kk.toNat
  cap16 : cap16.toNat = 2 ^ kk.toNat - 16
  lim : posLim.toNat + 40 = stop.toNat
  pair : pairBase ≠ USize.ofNat 4294967295 → pairBase.toNat + 1024 ≤ T.size
  np : np = H.npostfix

/-- What the loop knows of a state: the bits well formed, the position within the chunk, the window's size, and, inside
a segment of `m` literals, the margin: the next bit unread (`8 * pos - count`) at most `15 * m` bits short of 30 bytes
past `posLim`, which every literal's refill keeps in the chunk. -/
structure FSt (kk stop posLim : USize) (word count : UInt64) (pos : USize) (ring : ByteArray) (m : UInt64) : Prop where
  wf : (BitBuffer.mk word count).Wf
  posStop : pos.toNat ≤ stop.toNat
  size : ring.size = 2 ^ kk.toNat
  margin : m.toNat ≠ 0 → 8 * pos.toNat + 15 * m.toNat ≤ 8 * posLim.toNat + 240 + count.toNat

/-- The step machine's state at a place the loop leaves at: the window position, the bytes waiting and written, and
what remains of the meta-block from `opos`, the position the loop writes at, unmasked. -/
@[inline] def fexit (word count : UInt64) (ring : ByteArray) (opos mask pB cap cap16 wB : USize) (rEnd : UInt64)
    (iCount lCount dCount : UInt64) (flags : Flags) (x : CmdExt) (d01 d23 code ilen clen : UInt64) (p1 p2 : UInt8)
    (tag : Tag) (left : UInt64) (pos : USize) : Cmd :=
  ⟨word, count, ring, opos &&& mask, opos + pB, cap, usmin cap16 (opos + wB), p1, p2, rEnd - opos.toUInt64, iCount,
    lCount, dCount, flags,
    ⟨x.iCur, x.iPrev, x.lCur, x.lPrev, x.dCur, x.dPrev, d01 &&& 0xFFFFFFFF, d01 >>> 32, d23 &&& 0xFFFFFFFF, d23 >>> 32,
      code, ilen, clen, x.copyBits, x.copyBase, x.dist, x.wordBuf, x.wordPos⟩,
    tag, left, pos, .next⟩

/-- What the loop knows of the block types it doesn't change: the previous ones in range when there is a switch. -/
structure XInv (H : Hdr) (x : CmdExt) : Prop where
  iPrev : 2 ≤ H.nI.toNat → x.iPrev.toNat < H.nI.toNat
  lPrev : 2 ≤ H.nL.toNat → x.lPrev.toNat < H.nL.toNat
  dPrev : 2 ≤ H.nD.toNat → x.dPrev.toNat < H.nD.toNat

/-- A state the loop leaves, with what the compiled step machine needs of it at its position (`KInv`, which
`LoopK.lean`'s `CmdInv` names). -/
abbrev FOut (H : Hdr) (kk stop : USize) : Type :=
  { r : Cmd // KInv H kk stop r.word r.count r.ring r.wpos r.written r.iCur r.iPrev r.lCur r.lPrev r.dCur r.dPrev
    r.copyBits r.dist r.wordBuf r.wordPos r.tag r.pos }

/-- `fexit`, with what the compiled step machine needs of the state it leaves (`CmdInv`), at a place among the
literals, a distance or a command. -/
@[inline] def fexitP {H : Hdr} {T : ByteArray} {kk stop mask size cap16 posLim pairBase : USize} {np tb : UInt64}
    {x : CmdExt} {modeOff lRow iRow iFb dRow s0 : USize} (C : FCtx H T x.lCur x.iCur x.dCur tb modeOff lRow iRow iFb dRow s0)
    (X : XInv H x) (W : FWin H T kk mask size cap16 posLim stop pairBase np)
    (word count : UInt64) (ring : ByteArray) (opos pB cap wB : USize) (rEnd : UInt64) (iCount lCount dCount : UInt64)
    (flags : Flags) (d01 d23 code ilen clen : UInt64) (p1 p2 : UInt8) (tag : Tag) (left : UInt64) (pos : USize)
    (hw : (BitBuffer.mk word count).Wf) (hp : pos.toNat ≤ stop.toNat) (hsz : ring.size = 2 ^ kk.toNat)
    (ht : tag = .literals ∨ tag = .distance ∨ tag = .command) : FOut H kk stop :=
  ⟨fexit word count ring opos mask pB cap cap16 wB rEnd iCount lCount dCount flags x d01 d23 code ilen clen p1 p2 tag left
      pos, by
    unfold fexit
    refine ⟨C.hdr, W.k24, W.k16, hsz, mask_lt W.mask, ?_, hw, hp, C.hi, X.iPrev, C.hl, X.lPrev, C.hd, X.dPrev, ?_⟩
    · show (usmin cap16 (opos + wB)).toNat + 16 ≤ _
      rw [usmin_toNat, W.cap16]
      have := W.k16
      omega
    · rcases ht with h | h | h <;> subst h <;> trivial⟩

theorem fill_margin {posLim stop pos : USize} {count m thr : UInt64} (hl : posLim.toNat + 40 = stop.toNat)
    (hm : m.toNat ≠ 0 → 8 * pos.toNat + 15 * m.toNat ≤ 8 * posLim.toNat + 240 + count.toNat) (hm1 : 1 ≤ m.toNat)
    (ht : thr.toNat ≤ 30) : count.toNat < thr.toNat → pos.toNat + 8 ≤ stop.toNat := by
  intro hc
  have := hm (by omega)
  omega

/-- The bits a literal round takes, kept in the margin: `l` bits for `j` literals, at most 15 each. -/
theorem lit_margin {posLim pos p : USize} {count c l m j : UInt64} (hm : m.toNat ≠ 0 → 8 * pos.toNat + 15 * m.toNat ≤
    8 * posLim.toNat + 240 + count.toNat) (hjm : j.toNat ≤ m.toNat) (hj : 1 ≤ j.toNat)
    (hacct : 8 * p.toNat + count.toNat = 8 * pos.toNat + c.toNat) (hl : l.toNat ≤ 15 * j.toNat)
    (hlc : l.toNat ≤ c.toNat) :
    (m - j).toNat ≠ 0 → 8 * p.toNat + 15 * (m - j).toNat ≤ 8 * posLim.toNat + 240 + (c - l).toNat := by
  intro _
  have := hm (by omega)
  rw [u64_sub_le (by omega), u64_sub_le (by omega)]
  omega

theorem wix_lt {i mask : USize} {k : Nat} (hk : k ≤ 24) (hm : mask.toNat = 2 ^ k - 1) : (i &&& mask).toNat < 2 ^ 24 := by
  have := mask_lt (i := i) hm
  have : 2 ^ k ≤ 2 ^ 24 := Nat.pow_le_pow_right (by decide) hk
  omega

/-- What a literal round leaves of the literals at hand: one or two fewer. -/
theorem lit_dec {m j : UInt64} (hj : 1 ≤ j.toNat) (hjm : j.toNat ≤ m.toNat) : (m - j).toNat < m.toNat := by
  rw [u64_sub_le hjm]
  omega

/-- What a segment's start leaves: `m'` of the command's literals taken from what is left to the literals at hand. -/
theorem seg_dec {lits lCount m : UInt64} (hm : m.toNat = 0) (hl : lits.toNat ≠ 0) (hc : lCount.toNat ≠ 0) :
    17 * (lits - umin (umin lits lCount) 16).toNat + (umin (umin lits lCount) 16).toNat < 17 * lits.toNat + m.toNat := by
  have e : (umin (umin lits lCount) 16).toNat = min (min lits.toNat lCount.toNat) 16 := by
    rw [umin_toNat, umin_toNat]
    rfl
  rw [u64_sub_le (by rw [e]; omega), e]
  omega

/-- A round of one literal lowers the loop's measure. -/
theorem lit_dec1 (l : Nat) {m : UInt64} (h : m ≠ 0) : 17 * l + (m - 1).toNat < 17 * l + m.toNat := by
  have := lit_dec (j := 1) (by decide) (show 1 ≤ m.toNat from by
    have : m.toNat ≠ 0 := fun e => h (UInt64.toNat_inj.mp (by rw [e]; rfl))
    omega)
  omega

/-- A round of two literals lowers the loop's measure. -/
theorem lit_dec2 (l : Nat) {m : UInt64} (h : 2 ≤ m) : 17 * l + (m - 2).toNat < 17 * l + m.toNat := by
  have := lit_dec (j := 2) (by decide) (UInt64.le_iff_toNat_le.mp h)
  omega

/-- What a command round leaves of the commands: one fewer. -/
theorem icount_dec {iCount : UInt64} (hi : ¬ iCount = 0) : (iCount - 1).toNat < iCount.toNat :=
  lit_dec (j := 1) (by decide) (by
    have : iCount.toNat ≠ 0 := fun e => hi (UInt64.toNat_inj.mp (by rw [e]; rfl))
    show 1 ≤ iCount.toNat
    omega)

/-- The fast command loop. A round is a literal or two, a segment's start, or a command's distance, copy and next
insert-and-copy symbol: each takes the commands left down, or keeps them and takes `17 · lits + m` down, so it ends. It
leaves, with the step machine's state at the place it is at, when a block switch is due, the margin is reached, the
meta-block or the room would end inside the next command, a distance is past the bytes written or 0, or a code word is
too long for the bits at hand. -/
def fastLoop (H : Hdr) (kk : USize) (a : ByteArray) (stop : USize) (hs : stop.toNat ≤ a.size) (cap : USize)
    (T : ByteArray) (np : UInt64) (x : CmdExt) (flags : Flags) (mask size cap16 pB wB posLim : USize)
    (rEnd bEnd tb : UInt64) (modeOff lRow pairBase iRow iFb dRow s0 : USize)
    (C : FCtx H T x.lCur x.iCur x.dCur tb modeOff lRow iRow iFb dRow s0) (X : XInv H x)
    (W : FWin H T kk mask size cap16 posLim stop pairBase np)
    (word count : UInt64) (pos : USize) (ring : ByteArray) (opos : USize)
    (iCount lCount dCount d01 d23 code ilen clen lits m : UInt64) (p1 p2 : UInt8)
    (S : FSt kk stop posLim word count pos ring m) : FOut H kk stop :=
  have hk := W.k24
  have hmk := W.mask
  if hm0 : m ≠ 0 then
    have hm1 : 1 ≤ m.toNat := by
      have : m.toNat ≠ 0 := fun e => hm0 (UInt64.toNat_inj.mp (by rw [e]; rfl))
      omega
    have _hd1 : (m - 1).toNat < m.toNat := lit_dec (j := 1) (by decide) hm1
    if hp : 2 ≤ m ∧ pairBase ≠ USize.ofNat 4294967295 then
      have hm2 : 2 ≤ m.toNat := UInt64.le_iff_toNat_le.mp hp.1
      have _hd2 : (m - 2).toNat < m.toNat := lit_dec (j := 2) (by decide) hm2
      fillK a stop hs word count pos 15 S.wf (by decide) S.posStop (fill_margin W.lim S.margin hm1 (by decide))
        fun word' count' pos' hf =>
      let e := row32 T pairBase (W.pair hp.2) C.size32 word'
      if (e >>> 8) &&& 255 = 2 then
        let l := e &&& 15
        have hl : l.toNat < 16 := and15_lt e
        have hc15 : 15 ≤ count'.toNat := hf.enough
        let b1 := (e >>> 16).toUInt8
        let b2 := (e >>> 24).toUInt8
        let r1 := wput ring opos mask hk hmk S.size b1
        let r2 := wput r1 (opos + USize.ofNat 1) mask hk hmk (wput_size ring opos mask hk hmk S.size b1) b2
        fastLoop H kk a stop hs cap T np x flags mask size cap16 pB wB posLim rEnd bEnd tb modeOff lRow pairBase iRow iFb
          dRow s0 C X W (word' >>> l) (count' - l) pos' r2 (opos + USize.ofNat 2) iCount lCount dCount
          d01 d23 code ilen clen lits (m - 2) b2 b1
          ⟨drop1_wf hf.wf (by omega) (by omega), hf.posStop, wput_size _ _ _ hk hmk _ _,
            lit_margin (j := 2) S.margin hm2 (by decide) hf.acct (by show l.toNat ≤ 15 * 2; omega) (by omega)⟩
      else
        let v := litT C p1 p2 word'
        let l := v &&& 15
        have hl : l.toNat < 16 := and15_lt v
        have hc15 : 15 ≤ count'.toNat := hf.enough
        let b := (v >>> 4).toUInt8
        fastLoop H kk a stop hs cap T np x flags mask size cap16 pB wB posLim rEnd bEnd tb modeOff lRow pairBase iRow iFb
          dRow s0 C X W (word' >>> l) (count' - l) pos' (wput ring opos mask hk hmk S.size b)
          (opos + USize.ofNat 1) iCount lCount dCount d01 d23 code ilen clen lits (m - 1) b p1
          ⟨drop1_wf hf.wf (by omega) (by omega), hf.posStop, wput_size _ _ _ hk hmk _ _,
            lit_margin (j := 1) S.margin hm1 (by decide) hf.acct (by show l.toNat ≤ 15 * 1; omega) (by omega)⟩
    else if hm2' : 2 ≤ m then
      have hm2 : 2 ≤ m.toNat := UInt64.le_iff_toNat_le.mp hm2'
      have _hd2 : (m - 2).toNat < m.toNat := lit_dec (j := 2) (by decide) hm2
      fillK a stop hs word count pos 30 S.wf (by decide) S.posStop (fill_margin W.lim S.margin hm1 (by decide))
        fun word' count' pos' hf =>
      let v := litT C p1 p2 word'
      let l := v &&& 15
      have hl : l.toNat < 16 := and15_lt v
      let b1 := (v >>> 4).toUInt8
      let w1 := word' >>> l
      let v2 := litT C b1 p1 w1
      let l2 := v2 &&& 15
      have hl2 : l2.toNat < 16 := and15_lt v2
      have hc30 : 30 ≤ count'.toNat := hf.enough
      let b2 := (v2 >>> 4).toUInt8
      let r1 := wput ring opos mask hk hmk S.size b1
      let r2 := wput r1 (opos + USize.ofNat 1) mask hk hmk (wput_size ring opos mask hk hmk S.size b1) b2
      fastLoop H kk a stop hs cap T np x flags mask size cap16 pB wB posLim rEnd bEnd tb modeOff lRow pairBase iRow iFb
        dRow s0 C X W (w1 >>> l2) (count' - l - l2) pos' r2 (opos + USize.ofNat 2) iCount lCount dCount
        d01 d23 code ilen clen lits (m - 2) b2 b1
        ⟨drop2_wf (a := l) (b := l2) hf.wf (by omega) (by omega) (by omega), hf.posStop, wput_size _ _ _ hk hmk _ _, by
          intro _
          have hacct := hf.acct
          have hmar := S.margin (by omega)
          have h2 : (2 : UInt64).toNat = 2 := rfl
          have e1 : (count' - l).toNat = count'.toNat - l.toNat := u64_sub_le (by omega)
          have e2 : (count' - l - l2).toNat = count'.toNat - l.toNat - l2.toNat := by
            rw [u64_sub_le (by rw [e1]; omega), e1]
          have e3 : (m - 2).toNat = m.toNat - 2 := by rw [u64_sub_le (by rw [h2]; omega), h2]
          rw [e2, e3]
          omega⟩
    else
      fillK a stop hs word count pos 15 S.wf (by decide) S.posStop (fill_margin W.lim S.margin hm1 (by decide))
        fun word' count' pos' hf =>
      let v := litT C p1 p2 word'
      let l := v &&& 15
      have hl : l.toNat < 16 := and15_lt v
      have hc15 : 15 ≤ count'.toNat := hf.enough
      let b := (v >>> 4).toUInt8
      fastLoop H kk a stop hs cap T np x flags mask size cap16 pB wB posLim rEnd bEnd tb modeOff lRow pairBase iRow iFb
        dRow s0 C X W (word' >>> l) (count' - l) pos' (wput ring opos mask hk hmk S.size b)
        (opos + USize.ofNat 1) iCount lCount dCount d01 d23 code ilen clen lits (m - 1) b p1
        ⟨drop1_wf hf.wf (by omega) (by omega), hf.posStop, wput_size _ _ _ hk hmk _ _,
          lit_margin (j := 1) S.margin hm1 (by decide) hf.acct (by show l.toNat ≤ 15 * 1; omega) (by omega)⟩
  else if hl : lits ≠ 0 then
    if hcl : lCount = 0 ∨ posLim < pos then
      fexitP C X W word count ring opos pB cap wB rEnd iCount lCount dCount flags d01 d23 code ilen clen
        (wget ring (opos - USize.ofNat 1) mask hmk S.size) (wget ring (opos - USize.ofNat 2) mask hmk S.size)
        .literals lits pos S.wf S.posStop S.size (Or.inl rfl)
    else
      let m' := umin (umin lits lCount) 16
      have hm' : m'.toNat ≤ 16 := by
        rw [umin_toNat, umin_toNat]
        exact Nat.le_trans (Nat.min_le_right _ _) (by decide)
      have hpl : pos.toNat ≤ posLim.toNat := Nat.le_of_not_lt fun h => hcl (Or.inr (USize.lt_iff_toNat_lt.mpr h))
      have _hds : 17 * (lits - m').toNat + m'.toNat < 17 * lits.toNat + m.toNat :=
        seg_dec (by rw [Decidable.of_not_not hm0]; rfl) (fun e => hl (UInt64.toNat_inj.mp (by rw [e]; rfl)))
          (fun e => hcl (Or.inl (UInt64.toNat_inj.mp (by rw [e]; rfl))))
      fastLoop H kk a stop hs cap T np x flags mask size cap16 pB wB posLim rEnd bEnd tb modeOff lRow pairBase iRow iFb
        dRow s0 C X W word count pos ring opos iCount (lCount - m') dCount d01 d23 code ilen clen
        (lits - m') m' (wget ring (opos - USize.ofNat 1) mask hmk S.size) (wget ring (opos - USize.ofNat 2) mask hmk S.size)
        ⟨S.wf, S.posStop, S.size, fun _ => by omega⟩
  else
    if hd2 : posLim < pos ∨ (128 ≤ code ∧ dCount = 0) then
      fexitP C X W word count ring opos pB cap wB rEnd iCount lCount dCount flags d01 d23 code ilen clen
        (wget ring (opos - USize.ofNat 1) mask hmk S.size) (wget ring (opos - USize.ofNat 2) mask hmk S.size)
        .distance 0 pos S.wf S.posStop S.size (Or.inr (Or.inl rfl))
    else
    have hpl : pos.toNat ≤ posLim.toNat := Nat.le_of_not_lt fun h => hd2 (Or.inl (USize.lt_iff_toNat_lt.mpr h))
    have hlim := W.lim
    fillK a stop hs word count pos 40 S.wf (by decide) S.posStop (fun _ => by omega) fun word1 count1 pos1 hf1 =>
    let d0 := d01 &&& 0xFFFFFFFF
    distK C np word1 count1 clen d0 (d01 >>> 32) (d23 &&& 0xFFFFFFFF) (d23 >>> 32) hf1.wf
      fun ok2 word2x count2x dcode dx hok2 =>
    let d := if code < 128 then d0 else dx
    let written := usmin cap16 (opos + wB)
    if hbad : (¬ code < 128 ∧ ok2 = false) ∨ d = 0 ∨ written.toUInt64 < d then
      fexitP C X W word count ring opos pB cap wB rEnd iCount lCount dCount flags d01 d23 code ilen clen
        (wget ring (opos - USize.ofNat 1) mask hmk S.size) (wget ring (opos - USize.ofNat 2) mask hmk S.size)
        .distance 0 pos S.wf S.posStop S.size (Or.inr (Or.inl rfl))
    else
    have hw2 : (BitBuffer.mk (if code < 128 then word1 else word2x) (if code < 128 then count1 else count2x)).Wf := by
      by_cases hc : code < 128
      · rw [ite_eq_left hc, ite_eq_left hc]
        exact hf1.wf
      · rw [ite_eq_right hc, ite_eq_right hc]
        exact hok2 (by cases h : ok2 with
          | false => exact absurd (Or.inl ⟨hc, h⟩) hbad
          | true => rfl)
    have hd : d.toUSize.toNat + 16 ≤ 2 ^ kk.toNat := by
      have h1 : ¬ written.toUInt64 < d := fun h => hbad (Or.inr (Or.inr h))
      have h2 : written.toNat ≤ 2 ^ kk.toNat - 16 := by
        show (usmin cap16 (opos + wB)).toNat ≤ _
        rw [usmin_toNat, W.cap16]
        omega
      have h3 : d.toNat ≤ written.toNat := by
        have := UInt64.le_iff_toNat_le.mp (UInt64.not_lt.mp h1)
        rwa [USize.toNat_toUInt64] at this
      have h16 : 16 ≤ 2 ^ kk.toNat := W.k16
      have h24 : 2 ^ kk.toNat ≤ 2 ^ 24 := Nat.pow_le_pow_right (by decide) hk
      rw [word_toUSize (by omega)]
      omega
    -- the bit buffer after the distance, chosen once before the copy, so that only it lives across the copy's call
    let word2 := if code < 128 then word1 else word2x
    let count2 := if code < 128 then count1 else count2x
    let dCount' := if code < 128 then dCount else dCount - 1
    let push := !(decide (code < 128)) && dcode != 0
    let n01 := if push then d ||| (d01 <<< 32) else d01
    let n23 := if push then (d01 >>> 32) ||| (d23 <<< 32) else d23
    let ring' := copyF ring (opos &&& mask) d.toUSize clen.toUSize mask size hk hmk W.size S.size (mask_lt hmk) hd
    have hsz' : ring'.size = 2 ^ kk.toNat := copyF_size _ _ _ _ _ _ hk hmk W.size S.size _ hd
    let opos' := opos + clen.toUSize
    if hi0 : iCount = 0 then
      fexitP C X W word2 count2 ring' opos' pB cap wB
        rEnd iCount lCount dCount' flags n01 n23 code ilen clen
        (wget ring' (opos' - USize.ofNat 1) mask hmk hsz') (wget ring' (opos' - USize.ofNat 2) mask hmk hsz')
        .command 0 pos1 hw2 hf1.posStop hsz' (Or.inr (Or.inr rfl))
    else
    have _hdi : (iCount - 1).toNat < iCount.toNat :=
      lit_dec (j := 1) (by decide) (by
        have : iCount.toNat ≠ 0 := fun e => hi0 (UInt64.toNat_inj.mp (by rw [e]; rfl))
        show 1 ≤ iCount.toNat
        omega)
    have hp1 : pos1.toNat + 8 ≤ stop.toNat := by
      have := hf1.acct
      have : count1.toNat ≤ 64 := hf1.wf.count_le
      omega
    fillK a stop hs word2 count2 pos1 40 hw2
      (by decide) hf1.posStop (fun _ => hp1) fun word3 count3 pos3 hf3 =>
    icK C word3 count3 hf3.wf fun ok1 word4 count4 code' ilen' clen' hok1 =>
    if h1 : ok1 = false ∨ bEnd < opos'.toUInt64 + ilen' + clen' then
      fexitP C X W word2 count2 ring' opos' pB cap wB
        rEnd iCount lCount dCount' flags n01 n23 code ilen clen
        (wget ring' (opos' - USize.ofNat 1) mask hmk hsz') (wget ring' (opos' - USize.ofNat 2) mask hmk hsz')
        .command 0 pos1 hw2 hf1.posStop hsz' (Or.inr (Or.inr rfl))
    else
      -- no segment is open: the context bytes are read from the window when the next one starts
      fastLoop H kk a stop hs cap T np x flags mask size cap16 pB wB posLim rEnd bEnd tb modeOff lRow pairBase iRow iFb
        dRow s0 C X W word4 count4 pos3 ring' opos' (iCount - 1) lCount dCount' n01 n23 code' ilen'
        clen' ilen' 0 0 0
        ⟨hok1 (by cases h : ok1 with
          | false => exact absurd (Or.inl h) h1
          | true => rfl), hf3.posStop, hsz', fun h => absurd rfl h⟩
termination_by (iCount.toNat, 17 * lits.toNat + m.toNat)
decreasing_by
  all_goals
    first
    | exact Prod.Lex.left _ _ ‹_›
    | exact Prod.Lex.right _ (by omega)

/-! ### Into the loop -/

/-- The derived tables' row offsets, as positions, for a header that matches a spec header. -/
theorem rows_toNat {H : Hdr} (hH : ∃ m, HdrRel H m) {lCur iCur dCur : UInt64} (hl : lCur.toNat < H.nL.toNat)
    (hi : iCur.toNat < H.nI.toNat) (hd : dCur.toNat < H.nD.toNat) :
    let l0 := H.tabF0 + (H.nI.toUSize <<< USize.ofNat 11)
    let d0 := l0 + (H.nL.toUSize <<< USize.ofNat 8)
    let s0 := d0 + (H.nD.toUSize <<< USize.ofNat 4)
    (l0 + (lCur.toUSize <<< USize.ofNat 8)).toNat = H.tabF0.toNat + 2048 * H.nI.toNat + 256 * lCur.toNat ∧
      (H.tabF0 + (iCur.toUSize <<< USize.ofNat 11)).toNat = H.tabF0.toNat + 2048 * iCur.toNat ∧
      4 * (((s0 + USize.ofNat 4160) >>> USize.ofNat 2) + iCur.toUSize).toNat =
        H.tabF0.toNat + 2048 * H.nI.toNat + 256 * H.nL.toNat + 16 * H.nD.toNat + 4160 + 4 * iCur.toNat ∧
      (d0 + (dCur.toUSize <<< USize.ofNat 4)).toNat =
        H.tabF0.toNat + 2048 * H.nI.toNat + 256 * H.nL.toNat + 16 * dCur.toNat ∧
      s0.toNat = H.tabF0.toNat + 2048 * H.nI.toNat + 256 * H.nL.toNat + 16 * H.nD.toNat := by
  obtain ⟨m, hm⟩ := hH
  have t := hm.tab
  have hz := t.sizeOk
  have h32 := t.size32
  have hf := t.f0Ok
  have uI : H.nI.toUSize.toNat = H.nI.toNat := word_toUSize (by omega)
  have uL : H.nL.toUSize.toNat = H.nL.toNat := word_toUSize (by omega)
  have uD : H.nD.toUSize.toNat = H.nD.toNat := word_toUSize (by omega)
  have ul : lCur.toUSize.toNat = lCur.toNat := word_toUSize (by omega)
  have ui : iCur.toUSize.toNat = iCur.toNat := word_toUSize (by omega)
  have ud : dCur.toUSize.toNat = dCur.toNat := word_toUSize (by omega)
  have sI : (H.nI.toUSize <<< USize.ofNat 11).toNat = 2048 * H.nI.toNat := by
    rw [u64_shl (by decide) (by omega)]; omega
  have sL : (H.nL.toUSize <<< USize.ofNat 8).toNat = 256 * H.nL.toNat := by
    rw [u64_shl (by decide) (by omega)]; omega
  have sD : (H.nD.toUSize <<< USize.ofNat 4).toNat = 16 * H.nD.toNat := by
    rw [u64_shl (by decide) (by omega)]; omega
  have sl : (lCur.toUSize <<< USize.ofNat 8).toNat = 256 * lCur.toNat := by
    rw [u64_shl (by decide) (by omega)]; omega
  have si : (iCur.toUSize <<< USize.ofNat 11).toNat = 2048 * iCur.toNat := by
    rw [u64_shl (by decide) (by omega)]; omega
  have sd : (dCur.toUSize <<< USize.ofNat 4).toNat = 16 * dCur.toNat := by
    rw [u64_shl (by decide) (by omega)]; omega
  have el0 : (H.tabF0 + (H.nI.toUSize <<< USize.ofNat 11)).toNat = H.tabF0.toNat + 2048 * H.nI.toNat := by
    rw [fastAdd (by rw [sI]; omega), sI]
  have ed0 : (H.tabF0 + (H.nI.toUSize <<< USize.ofNat 11) + (H.nL.toUSize <<< USize.ofNat 8)).toNat =
      H.tabF0.toNat + 2048 * H.nI.toNat + 256 * H.nL.toNat := by
    rw [fastAdd (by rw [el0, sL]; omega), el0, sL]
  have es0 : (H.tabF0 + (H.nI.toUSize <<< USize.ofNat 11) + (H.nL.toUSize <<< USize.ofNat 8) +
      (H.nD.toUSize <<< USize.ofNat 4)).toNat = H.tabF0.toNat + 2048 * H.nI.toNat + 256 * H.nL.toNat + 16 * H.nD.toNat := by
    rw [fastAdd (by rw [ed0, sD]; omega), ed0, sD]
  have e4 : (H.tabF0 + (H.nI.toUSize <<< USize.ofNat 11) + (H.nL.toUSize <<< USize.ofNat 8) +
      (H.nD.toUSize <<< USize.ofNat 4) + USize.ofNat 4160).toNat =
      H.tabF0.toNat + 2048 * H.nI.toNat + 256 * H.nL.toNat + 16 * H.nD.toNat + 4160 := by
    rw [fastIdx_add (by rw [es0]; omega), es0]
  have hb : 32 ≤ System.Platform.numBits := by rcases System.Platform.numBits_eq with h | h <;> omega
  have e5 : ((H.tabF0 + (H.nI.toUSize <<< USize.ofNat 11) + (H.nL.toUSize <<< USize.ofNat 8) +
      (H.nD.toUSize <<< USize.ofNat 4) + USize.ofNat 4160) >>> USize.ofNat 2).toNat =
      (H.tabF0.toNat + 2048 * H.nI.toNat + 256 * H.nL.toNat + 16 * H.nD.toNat + 4160) / 4 := by
    rw [USize.toNat_shiftRight, e4, fastLit (by decide), Nat.mod_eq_of_lt (by omega), Nat.shiftRight_eq_div_pow]
  refine ⟨?_, ?_, ?_, ?_, es0⟩
  · rw [fastAdd (by rw [el0, sl]; omega), el0, sl]
  · rw [fastAdd (by rw [si]; omega), si]
  · rw [fastAdd (by rw [e5, ui]; omega), e5, ui]
    omega
  · rw [fastAdd (by rw [ed0, sd]; omega), ed0, sd]

/-- Where a literal block type's two-literal table's position is: in the last `4 * nL` bytes of the arena. -/
theorem pairIdx_toNat {H : Hdr} (hH : ∃ m, HdrRel H m) {lCur : UInt64} (hl : lCur.toNat < H.nL.toNat) :
    (USize.ofNat H.arena.size - (H.nL.toUSize <<< USize.ofNat 2) + (lCur.toUSize <<< USize.ofNat 2)).toNat =
      H.arena.size - 4 * H.nL.toNat + 4 * lCur.toNat ∧ H.arena.size - 4 * H.nL.toNat + 4 * lCur.toNat + 4 ≤ H.arena.size := by
  obtain ⟨m, hm⟩ := hH
  have t := hm.tab
  have hz := t.sizeOk
  have h32 := t.size32
  have sL : (H.nL.toUSize <<< USize.ofNat 2).toNat = 4 * H.nL.toNat := by
    rw [u64_shl (by decide) (by omega)]; omega
  have sl : (lCur.toUSize <<< USize.ofNat 2).toNat = 4 * lCur.toNat := by
    rw [u64_shl (by decide) (by omega)]; omega
  have e1 : (USize.ofNat H.arena.size - (H.nL.toUSize <<< USize.ofNat 2)).toNat = H.arena.size - 4 * H.nL.toNat := by
    rw [USize.toNat_sub_of_le _ _ (USize.le_iff_toNat_le.mpr (by rw [sL, fastLit h32]; omega)), sL, fastLit h32]
  rw [fastAdd (by rw [e1, sl]; omega), e1, sl]
  exact ⟨rfl, by omega⟩

/-- Into the fast loop from the step machine's state at a command's literals or its distance, with at least 40 bytes of
the chunk left: the row offsets for the block types, the shared base, the context mode and the two-literal table's
place, computed once. `bEnd` is where the room or the meta-block ends, which the loop's commands must fit. -/
@[inline] def fastEnter (H : Hdr) (kk : USize) (a : ByteArray) (stop : USize) (hs : stop.toNat ≤ a.size) (cap : USize)
    (word count : UInt64) (ring : ByteArray) (wpos pend written : USize) (p1 p2 : UInt8)
    (remaining iCount lCount dCount : UInt64) (flags : Flags) (x : CmdExt) (tag : Tag) (lits bEnd : UInt64) (pos : USize)
    (hinv : KInv H kk stop word count ring wpos written x.iCur x.iPrev x.lCur x.lPrev x.dCur x.dPrev x.copyBits x.dist
      x.wordBuf x.wordPos tag pos) (hm : pos.toNat + 40 ≤ stop.toNat) : FOut H kk stop :=
  have hT : TabOk H.arena H.litBase H.lMap H.icBase H.dBase H.dMap H.lTriv H.nL.toNat H.nI.toNat H.nD.toNat
      H.treesL.toNat H.treesD.toNat H.npostfix H.ndirect H.tabF0.toNat := by
    obtain ⟨m, hm⟩ := hinv.hdr
    exact hm.tab
  let l0 := H.tabF0 + (H.nI.toUSize <<< USize.ofNat 11)
  let d0 := l0 + (H.nL.toUSize <<< USize.ofNat 8)
  let s0 := d0 + (H.nD.toUSize <<< USize.ofNat 4)
  have hr := rows_toNat hinv.hdr hinv.lCur hinv.iCur hinv.dCur
  have hmodes : x.lCur.toUSize.toNat < H.modes.size := by rw [cur_usize hinv.lCur, H.modesSize]; exact hinv.lCur
  let modeOff := ((H.modes.uget x.lCur.toUSize hmodes).toUInt64 <<< 9).toUSize
  have hx := pairIdx_toNat hinv.hdr hinv.lCur
  let pv := load32 H.arena (USize.ofNat H.arena.size - (H.nL.toUSize <<< USize.ofNat 2) +
    (x.lCur.toUSize <<< USize.ofNat 2)) (by rw [hx.1]; exact hx.2) hT.size32
  let pairBase := if pv = 4294967295 then USize.ofNat 4294967295 else pv.toUSize
  have hpair : pairBase ≠ USize.ofNat 4294967295 → pairBase.toNat + 1024 ≤ H.arena.size := by
    intro hne
    by_cases hv : pv = 4294967295
    · exact absurd (by show (if pv = 4294967295 then USize.ofNat 4294967295 else pv.toUSize) = _; rw [ite_eq_left hv]) hne
    · have hpv : pv.toNat = leAt H.arena (H.arena.size - 4 * H.nL.toNat + 4 * x.lCur.toNat) 4 := by
        show (load32 _ _ _ _).toNat = _
        rw [load32_toNat, hx.1]
      have hpv' : leAt H.arena (H.arena.size - 4 * H.nL.toNat + 4 * x.lCur.toNat) 4 ≠ 4294967295 := fun e =>
        hv (UInt64.toNat_inj.mp (by rw [hpv, e]; rfl))
      have hp := (hT.pix _ hinv.lCur hpv').2.1
      show (if pv = 4294967295 then USize.ofNat 4294967295 else pv.toUSize).toNat + 1024 ≤ _
      rw [ite_eq_right hv, word_toUSize (by rw [hpv]; exact Nat.lt_of_lt_of_le (leAt_lt _ _ 4) (by decide)), hpv]
      omega
  have h40 : (USize.ofNat 40).toNat = 40 := fastLit (by decide)
  have h16 : (USize.ofNat 16).toNat = 16 := fastLit (by decide)
  fastLoop H kk a stop hs cap H.arena H.npostfix x flags (ringMask kk) (ringSize kk) (ringSize kk - USize.ofNat 16)
    (pend - wpos) (written - wpos) (stop - USize.ofNat 40) (remaining + wpos.toUInt64) bEnd (trivBase H x.lCur hinv.lCur)
    modeOff (l0 + (x.lCur.toUSize <<< USize.ofNat 8)) pairBase (H.tabF0 + (x.iCur.toUSize <<< USize.ofNat 11))
    (((s0 + USize.ofNat 4160) >>> USize.ofNat 2) + x.iCur.toUSize) (d0 + (x.dCur.toUSize <<< USize.ofNat 4)) s0
    ⟨hinv.hdr, rfl, hinv.lCur, hinv.iCur, hinv.dCur, rfl,
      by rw [modeOff_toNat (H.modesLt _ hmodes), uget_toNat, cur_usize hinv.lCur], hr.1, hr.2.1, hr.2.2.1, hr.2.2.2.1,
      hr.2.2.2.2⟩
    ⟨hinv.iPrev, hinv.lPrev, hinv.dPrev⟩
    ⟨hinv.k24, hinv.k16, ringMask_toNat hinv.k24, ringSize_toNat hinv.k24,
      by rw [USize.toNat_sub_of_le _ _ (USize.le_iff_toNat_le.mpr (by rw [h16, ringSize_toNat hinv.k24]; exact hinv.k16)),
        h16, ringSize_toNat hinv.k24],
      by rw [USize.toNat_sub_of_le _ _ (USize.le_iff_toNat_le.mpr (by rw [h40]; omega)), h40]; omega, hpair, rfl⟩
    word count pos ring wpos iCount lCount dCount (x.d0 ||| (x.d1 <<< 32)) (x.d2 ||| (x.d3 <<< 32)) x.code x.ilen x.clen
    lits 0 p1 p2 ⟨hinv.wf, hinv.pos, hinv.size, fun h => absurd rfl h⟩

end Brotli.Decoder
