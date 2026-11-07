module

public import Brotli.Decoder.FastRead
public import Brotli.Decoder.LoopK
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
    (hm : pos.toNat + 8 ≤ stop.toNat)
    (k : (w c : UInt64) → (p : USize) → FillOk a stop word count pos thr.toNat w c p → α) : α :=
  if hc : count < thr then
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

/-- The format's copy of `n` bytes from `d` back to `wpos`, `d` within the window: two 16-byte blocks at a distance of
16 or more (writing up to 15 bytes past the copy, in the window's slack), one `memmove` at a distance of at least the
length, the masked byte loop otherwise. The tests choose how; none is redundant. -/
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
  else if h2 : n ≤ d ∧ s + n ≤ size ∧ wpos + n ≤ size then
    winMove ring wpos s n
      (by
        have hnd := USize.le_iff_toNat_le.mp h2.1
        have e1 := USize.le_iff_toNat_le.mp h2.2.1
        have e2 := USize.le_iff_toNat_le.mp h2.2.2
        rw [fastAdd (by omega), hsz] at e1
        rw [fastAdd (by omega), hsz] at e2
        exact ⟨by omega, by omega⟩)
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

/-- Head 1: the insert-and-copy symbol and both lengths, from the fused entry (one 8-byte load) or, for a code word
longer than 8 bits, from the tree; with whether the buffer held the bits. -/
@[inline] def icK {α : Type} (C : FCtx H T lCur iCur dCur tb modeOff lRow iRow iFb dRow s0) (word count : UInt64)
    (hw : (BitBuffer.mk word count).Wf)
    (k : (ok : Bool) → (w c code ilen clen : UInt64) → (ok = true → (BitBuffer.mk w c).Wf) → α) : α :=
  let e := row64 T iRow C.iRowLe C.size32 word
  if e &&& 255 = 255 then
    let v := lookupT T (icFbBase C) word C.icIn C.lim C.size32
    let l := v &&& 15
    let code := wordSym v
    have hc : code.toNat < 704 := C.icSym word
    let row := insertRow code hc
    let cr := copyRow code hc
    let ib := rowBits row
    let cb := rowBits cr
    let w1 := word >>> l
    let ilen := rowBase row + (w1 &&& maskT T C.big C.size32 ib)
    let w2 := w1 >>> ib
    let clen := rowBase cr + (w2 &&& maskT T C.big C.size32 cb)
    have hl : l.toNat < 16 := and15_lt v
    have hib : ib.toNat < 64 := insertRow_bits hc
    have hcb : cb.toNat ≤ 24 := copyRow_bits hc
    k (decide (l + ib + cb ≤ count)) (w2 >>> cb) (count - l - ib - cb) code ilen clen
      (fun h => by
        have h1 := UInt64.le_iff_toNat_le.mp (of_decide_eq_true h)
        rw [u64_add_small (by rw [u64_add_small (by omega)]; omega), u64_add_small (by omega)] at h1
        exact drop3_wf hw (by omega) (by omega) (by omega) h1)
  else
    let l := e &&& 15
    let ib := (e >>> 18) &&& 63
    let cb := (e >>> 24) &&& 63
    let w1 := word >>> l
    let ilen := ((e >>> 32) &&& 0xFFFF) + (w1 &&& maskT T C.big C.size32 ib)
    let w2 := w1 >>> ib
    let clen := (e >>> 48) + (w2 &&& maskT T C.big C.size32 cb)
    have hl : l.toNat < 16 := and15_lt e
    have hib : ib.toNat < 64 := and63_lt _
    have hcb : cb.toNat < 64 := and63_lt _
    k (decide (l + ib + cb ≤ count)) (w2 >>> cb) (count - l - ib - cb) ((e >>> 8) &&& 1023) ilen clen
      (fun h => by
        have h1 := UInt64.le_iff_toNat_le.mp (of_decide_eq_true h)
        rw [u64_add_small (by rw [u64_add_small (by omega)]; omega), u64_add_small (by omega)] at h1
        exact drop3_wf hw (by omega) (by omega) (by omega) h1)

end

end Brotli.Decoder
