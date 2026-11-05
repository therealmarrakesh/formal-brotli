import Brotli.Decoder.Order
import Brotli.Decoder.Refill
import Brotli.Decoder.Lookup
import Brotli.Decoder.Window
import Brotli.Decoder.ContextLut
import Brotli.Decoder.Copy

/-!
# The literal loop

The hot path for literals. It runs for `n` literals in a row, where `n` is at most the literals left in the command,
in the block, and the room in the window, so it counts only one thing. Its state is plain values, and it returns
only when `n` runs out or the bits at hand can't finish a symbol.
-/

namespace Brotli.Decoder

open Brotli.Spec

/-- What the header's check has established about the literal tables, with no mention of the spec. -/
structure LitChecked (arena litBase lMap : ByteArray) (nTrees : Nat) : Prop where
  arena32 : arena.size < 2 ^ 32
  base32 : litBase.size < 2 ^ 32
  map32 : lMap.size < 2 ^ 32
  baseSize : litBase.size = 4 * nTrees
  treeLt : ∀ p : USize, ∀ h : p.toNat < lMap.size, (lMap.uget p h).toNat < nTrees
  fits : ∀ tree, tree < nTrees → TableFits arena (u32At litBase tree)

/-- A literal loop's result, flat so the loop keeps every field as a plain value. -/
structure LitRun where
  word : UInt64
  count : UInt64
  pos : USize
  wpos : USize
  ring : ByteArray
  p1 : UInt8
  p2 : UInt8
  left : USize

private theorem usize_add {a b : USize} (h : a.toNat + b.toNat < 2 ^ 32) : (a + b).toNat = a.toNat + b.toNat := by
  rw [USize.toNat_add, ← USize.size_eq_two_pow]
  have := USize.le_size
  exact Nat.mod_eq_of_lt (by omega)

private theorem u8_usize (x : UInt8) : x.toUSize.toNat = x.toNat := by
  simp

/-- The slot base of a literal tree. -/
@[inline] def treeBase (litBase : ByteArray) (tree : UInt8) (h : 4 * tree.toNat + 4 ≤ litBase.size)
    (h32 : litBase.size < 2 ^ 32) : USize :=
  (slotWord litBase tree.toUSize (by rw [u8_usize]; exact h) h32).toUSize

theorem treeBase_toNat {litBase : ByteArray} {tree : UInt8} (h : 4 * tree.toNat + 4 ≤ litBase.size)
    (h32 : litBase.size < 2 ^ 32) : (treeBase litBase tree h h32).toNat = u32At litBase tree.toNat := by
  unfold treeBase
  rw [word_toUSize (by rw [slotWord_toNat]; exact u32At_lt _ _), slotWord_toNat, u8_usize]

/-- The position of a literal's tree in the context map. -/
@[inline] def mapIndex (mapBase : USize) (cid : UInt8) : USize := mapBase + cid.toUSize

theorem mapIndex_toNat {mapBase : USize} {cid : UInt8} (h : mapBase.toNat + cid.toNat < 2 ^ 32) :
    (mapIndex mapBase cid).toNat = mapBase.toNat + cid.toNat := by
  unfold mapIndex
  rw [usize_add (by rw [u8_usize]; exact h), u8_usize]

/-- The context ID is below 64. -/
theorem cid_lt {modeOff : USize} {p1 p2 : UInt8} (hm : modeOff.toNat + 512 ≤ 2048) (hd : modeOff.toNat % 512 = 0) :
    (cidFast modeOff p1 p2 hm).toNat < 64 := by
  rw [cid_eq hm hd]
  exact contextId_lt _ _ p1.toNat_lt

/-- Runs up to `n` literals. -/
def literalRun {nTrees : Nat} {arena litBase lMap : ByteArray} (C : LitChecked arena litBase lMap nTrees)
    (a : ByteArray) (stop : USize) (hs : stop.toNat ≤ a.size) (mapBase modeOff mask : USize) (k : Nat)
    (hmb : mapBase.toNat + 64 ≤ lMap.size) (hm : modeOff.toNat + 512 ≤ 2048) (hd : modeOff.toNat % 512 = 0)
    (hmask : mask.toNat = 2 ^ k - 1) (hk : k ≤ 24) (n : USize) (word count : UInt64) (pos wpos : USize) (ring : ByteArray)
    (p1 p2 : UInt8) (hp : pos.toNat ≤ stop.toNat) (hw : (BitBuffer.mk word count).Wf) (hsize : ring.size = 2 ^ k)
    (hwp : wpos.toNat < 2 ^ k) : LitRun :=
  if hn : n = 0 then ⟨word, count, pos, wpos, ring, p1, p2, 0⟩
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
      literalRun C a stop hs mapBase modeOff mask k hmb hm hd hmask hk (n - USize.ofNat 1) b.word b.count rp (ringNext wpos mask) ring'
        byte p1 hspec.2.2.1 (BitBuffer.drop_wf hspec.1 hl63 (UInt64.le_iff_toNat_le.mp hl)) hsize' hnext
    else ⟨rw, rc, rp, wpos, ring, p1, p2, n⟩
termination_by n.toNat
decreasing_by
  have := usize_pred hn
  have := usize_ne hn
  omega

/-! ### What the loop does -/

/-- The literal tables match the spec's header: the map's bytes are its context map, and each tree's table decodes
its prefix code. -/
structure LitRel (arena litBase lMap : ByteArray) (nTrees : Nat) (m : MetaBlockHeader) : Prop where
  map : ∀ p : USize, ∀ h : p.toNat < lMap.size, m.literalMap[p.toNat]? = some (lMap.uget p h).toNat
  code : ∀ tree, tree < nTrees → ∃ code, m.literalCodes[tree]? = some code ∧
    TableOk arena (u32At litBase tree) code ∧ Complete code ∧ code.Symbols literalAlphabetSize

/-- The bits the decoder holds, then the rest of the chunk, then any future. -/
def availBits (word count : UInt64) (a : ByteArray) (pos stop : USize) (F : List Bool) : List Bool :=
  (BitBuffer.mk word count).held ++ (chunkBits a pos.toNat stop.toNat ++ F)

private theorem contextBytes_cons (b : Nat) (out : List Nat) :
    contextBytes (b :: out) = (b, (contextBytes out).1) := by
  cases out with
  | nil => rfl
  | cons x xs =>
    cases xs with
    | nil => rfl
    | cons y ys => rfl

private theorem and15 (v : UInt64) (_h : v.toNat % 16 ≤ 15) : (v &&& 15).toNat = v.toNat % 16 := by
  rw [UInt64.toNat_and, show (15 : UInt64).toNat = 2 ^ 4 - 1 from rfl, Nat.and_two_pow_sub_one_eq_mod]

private theorem byte_of (v : UInt64) (h : v.toNat / 16 < literalAlphabetSize) :
    (v >>> 4).toUInt8.toNat = v.toNat / 16 := by
  have h' : v.toNat / 16 < 256 := h
  simp only [UInt64.toNat_toUInt8, UInt64.toNat_shiftRight]
  rw [show (4 : UInt64).toNat % 64 = 4 from rfl, Nat.shiftRight_eq_div_pow, show (2 : Nat) ^ 4 = 16 from rfl]
  omega

/-- One literal with no block switch, in the spec's terms. -/
private theorem literal_step {α : Type} {w : Nat} {m : MetaBlockHeader} {K : CommandState → List Bool → Option α}
    {s : CommandState} {ic : BlockState} {c ilen clen n : Nat} {lit : BlockState} {out : List Nat} {t mode tree : Nat}
    {code : PrefixCode} {bs r : List Bool} {sym : Nat} (hc : lit.count ≠ 0) (hcur : lit.types.cur = t)
    (hmode : m.contextModes[t]? = some mode)
    (hmap : literalPrefixCodeIndex m.literalMap t (contextId mode (contextBytes out).1 (contextBytes out).2) = some tree)
    (hcode : m.literalCodes[tree]? = some code) (hd : decodeSymbol code bs = some (sym, r)) :
    rest w m K (.literals s ic c ilen clen (n + 1) lit out) bs =
      rest w m K (.literals s ic c ilen clen n { lit with count := lit.count - 1 } (sym :: out)) r := by
  have hnext : nextElement m.literal lit bs = some ({ lit with count := lit.count - 1 }, bs) := by
    simp [nextElement, hc]
  rw [rest_literal, hnext]
  show rest w m K (.literalSymbol s ic c ilen clen n { lit with count := lit.count - 1 } out) bs = _
  rw [rest_literalSymbol]
  have hc' : ({ lit with count := lit.count - 1 } : BlockState).types.cur = t := hcur
  rw [hc', hmode]
  show (literalPrefixCodeIndex m.literalMap t (contextId mode (contextBytes out).1 (contextBytes out).2) >>= _) = _
  rw [hmap]
  show (m.literalCodes[tree]? >>= _) = _
  rw [hcode]
  show (decodeSymbol code bs >>= _) = _
  rw [hd]
  rfl

/-- With nothing more than these bits, a literal's symbol can't be read, so the spec rejects. -/
private theorem literal_none {α : Type} {w : Nat} {m : MetaBlockHeader} {K : CommandState → List Bool → Option α}
    {s : CommandState} {ic : BlockState} {c ilen clen n : Nat} {lit : BlockState} {out : List Nat} {t mode tree : Nat}
    {code : PrefixCode} {bs : List Bool} (hc : lit.count ≠ 0) (hcur : lit.types.cur = t)
    (hmode : m.contextModes[t]? = some mode)
    (hmap : literalPrefixCodeIndex m.literalMap t (contextId mode (contextBytes out).1 (contextBytes out).2) = some tree)
    (hcode : m.literalCodes[tree]? = some code) (hd : decodeSymbol code bs = none) :
    rest w m K (.literals s ic c ilen clen (n + 1) lit out) bs = none := by
  have hnext : nextElement m.literal lit bs = some ({ lit with count := lit.count - 1 }, bs) := by
    simp [nextElement, hc]
  rw [rest_literal, hnext]
  show rest w m K (.literalSymbol s ic c ilen clen n { lit with count := lit.count - 1 } out) bs = _
  rw [rest_literalSymbol]
  have hc' : ({ lit with count := lit.count - 1 } : BlockState).types.cur = t := hcur
  rw [hc', hmode]
  show (literalPrefixCodeIndex m.literalMap t (contextId mode (contextBytes out).1 (contextBytes out).2) >>= _) = _
  rw [hmap]
  show (m.literalCodes[tree]? >>= _) = _
  rw [hcode]
  show (decodeSymbol code bs >>= _) = _
  rw [hd]
  rfl

/-- One literal with no block switch, read in order. -/
private theorem literal_reach {w : Nat} {m : MetaBlockHeader}
    {s : CommandState} {ic : BlockState} {c ilen clen n : Nat} {lit : BlockState} {out : List Nat} {t mode tree : Nat}
    {code : PrefixCode} {bs r : List Bool} {sym : Nat} (hc : lit.count ≠ 0) (hcur : lit.types.cur = t)
    (hmode : m.contextModes[t]? = some mode)
    (hmap : literalPrefixCodeIndex m.literalMap t (contextId mode (contextBytes out).1 (contextBytes out).2) = some tree)
    (hcode : m.literalCodes[tree]? = some code) (hd : decodeSymbol code bs = some (sym, r)) :
    Reach (cStep w m) (.literals s ic c ilen clen (n + 1) lit out) bs
      (.literals s ic c ilen clen n { lit with count := lit.count - 1 } (sym :: out)) r := by
  refine .next (show (if lit.count = 0 then _ else _) = _ by rw [ite_eq_right hc]) (Reach.one ?_)
  have hc' : ({ lit with count := lit.count - 1 } : BlockState).types.cur = t := hcur
  show lookIn m.contextModes[({ lit with count := lit.count - 1 } : BlockState).types.cur]? _ = _
  rw [hc', lookIn_some hmode, lookIn_some hmap, lookIn_some hcode]
  show readIn 15 (decodeSymbol code) bs _ = _
  rw [readIn_some hd]

/-- With these bits, a literal's symbol can't be read, and the reading in order has too few bits. -/
private theorem literal_cshort {w : Nat} {m : MetaBlockHeader}
    {s : CommandState} {ic : BlockState} {c ilen clen n : Nat} {lit : BlockState} {out : List Nat} {t mode tree : Nat}
    {code : PrefixCode} {bs : List Bool} (hc : lit.count ≠ 0) (hcur : lit.types.cur = t)
    (hmode : m.contextModes[t]? = some mode)
    (hmap : literalPrefixCodeIndex m.literalMap t (contextId mode (contextBytes out).1 (contextBytes out).2) = some tree)
    (hcode : m.literalCodes[tree]? = some code) (hd : decodeSymbol code bs = none) (hl : bs.length < 15) :
    CShort w m (.literals s ic c ilen clen (n + 1) lit out) bs := by
  refine ⟨.literalSymbol s ic c ilen clen n { lit with count := lit.count - 1 } out, bs,
    Reach.one (show (if lit.count = 0 then _ else _) = _ by rw [ite_eq_right hc]), ?_, rfl⟩
  have hc' : ({ lit with count := lit.count - 1 } : BlockState).types.cur = t := hcur
  show lookIn m.contextModes[({ lit with count := lit.count - 1 } : BlockState).types.cur]? _ = _
  rw [hc', lookIn_some hmode, lookIn_some hmap, lookIn_some hcode]
  exact readIn_short hd hl

/-- The literal loop's whole effect. Each literal it runs is one the spec reads, whatever bits follow. It stops when
its count runs out, or when the chunk is used up and the bits at hand can't finish a symbol, in which case the spec
rejects if no more bits come, and its reading in order has too few bits. -/
theorem literalRun_spec {α : Type} {nTrees : Nat} {arena litBase lMap : ByteArray} (C : LitChecked arena litBase lMap nTrees)
    {a : ByteArray} {stop : USize} (hs : stop.toNat ≤ a.size) {mapBase modeOff mask : USize} {k : Nat}
    (hmb : mapBase.toNat + 64 ≤ lMap.size) (hm : modeOff.toNat + 512 ≤ 2048) (hd : modeOff.toNat % 512 = 0)
    (hmask : mask.toNat = 2 ^ k - 1) (hk : k ≤ 24)
    {w : Nat} {m : MetaBlockHeader} {K : CommandState → List Bool → Option α} (R : LitRel arena litBase lMap nTrees m)
    {t : Nat} (hmap : mapBase.toNat = 64 * t) (hmode : m.contextModes[t]? = some (modeOff.toNat / 512))
    (s : CommandState) (ic : BlockState) (c ilen clen : Nat) :
    ∀ (N : Nat) (n : USize) (word count : UInt64) (pos wpos : USize) (ring : ByteArray) (p1 p2 : UInt8)
      (hp : pos.toNat ≤ stop.toNat) (hw : (BitBuffer.mk word count).Wf) (hsize : ring.size = 2 ^ k)
      (hwp : wpos.toNat < 2 ^ k) (L : Nat) (lit : BlockState) (out : List Nat),
      n.toNat = N → N ≤ L → N ≤ lit.count → lit.types.cur = t → contextBytes out = (p1.toNat, p2.toNat) →
      RingOk ring k wpos.toNat out → (∀ b ∈ out, b < 256) →
      let r := literalRun C a stop hs mapBase modeOff mask k hmb hm hd hmask hk n word count pos wpos ring p1 p2 hp hw hsize hwp
      ∃ (lit' : BlockState) (out' : List Nat),
        r.left.toNat ≤ N ∧ lit'.types = lit.types ∧ lit'.seen = lit.seen ∧ lit'.count = lit.count - (N - r.left.toNat) ∧
        out'.length = out.length + (N - r.left.toNat) ∧ (∃ l, out' = l ++ out) ∧ RingOk r.ring k r.wpos.toNat out' ∧
        contextBytes out' = (r.p1.toNat, r.p2.toNat) ∧ (BitBuffer.mk r.word r.count).Wf ∧
        pos.toNat ≤ r.pos.toNat ∧ r.pos.toNat ≤ stop.toNat ∧ (∀ b ∈ out', b < 256) ∧
        (∀ F, rest w m K (.literals s ic c ilen clen L lit out) (availBits word count a pos stop F) =
          rest w m K (.literals s ic c ilen clen (L - (N - r.left.toNat)) lit' out') (availBits r.word r.count a r.pos stop F)) ∧
        (r.left.toNat ≠ 0 → r.pos = stop ∧
          rest w m K (.literals s ic c ilen clen (L - (N - r.left.toNat)) lit' out') (BitBuffer.mk r.word r.count).held = none ∧
          CShort w m (.literals s ic c ilen clen (L - (N - r.left.toNat)) lit' out') (BitBuffer.mk r.word r.count).held) ∧
        (∀ F, Reach (cStep w m) (.literals s ic c ilen clen L lit out) (availBits word count a pos stop F)
          (.literals s ic c ilen clen (L - (N - r.left.toNat)) lit' out') (availBits r.word r.count a r.pos stop F)) := by
  intro N
  induction N with
  | zero =>
    intro n word count pos wpos ring p1 p2 hp hw hsize hwp L lit out hN _ _ _ hctx hring hbytes
    rw [literalRun, dite_eq_left (usize_zero hN)]
    have h0 : (0 : USize).toNat = 0 := rfl
    exact ⟨lit, out, by simp, rfl, rfl, by simp, by simp, ⟨[], rfl⟩, hring, hctx, hw,
      Nat.le_refl _, hp, hbytes, fun F => by simp, fun h => absurd h0 h, fun F => by simpa using Reach.refl _ _⟩
  | succ N ih =>
    intro n word count pos wpos ring p1 p2 hp hw hsize hwp L lit out hN hL hcount hcur hctx hring hbytes
    have hn : n ≠ 0 := fun e => by rw [e] at hN; exact Nat.succ_ne_zero _ hN.symm
    have hpred := usize_pred hn
    rw [literalRun, dite_eq_right hn]
    dsimp only
    obtain ⟨hrw, hrp1, hrp2, hbits, hdisj⟩ := refill_spec hs hp hw
    have hcidlt : (cidFast modeOff p1 p2 hm).toNat < 64 := cid_lt hm hd
    have hcidv : (cidFast modeOff p1 p2 hm).toNat = contextId (modeOff.toNat / 512) p1.toNat p2.toNat := cid_eq hm hd
    have hidx : (mapIndex mapBase (cidFast modeOff p1 p2 hm)).toNat = mapBase.toNat + (cidFast modeOff p1 p2 hm).toNat :=
      mapIndex_toNat (by have := C.map32; omega)
    have hi : (mapIndex mapBase (cidFast modeOff p1 p2 hm)).toNat < lMap.size := by
      rw [hidx]
      omega
    have htree := C.treeLt _ hi
    have hmapv := R.map _ hi
    obtain ⟨code, hcode, hok, hC, hsym⟩ := R.code _ htree
    have hb : 4 * (lMap.uget _ hi).toNat + 4 ≤ litBase.size := by
      rw [C.baseSize]
      omega
    have hbase := treeBase_toNat hb C.base32
    rw [← hbase] at hok
    obtain ⟨hv1, hv2⟩ := lookup_spec (w := (refill word count a pos stop hs hp).word) hok.toTableFits C.arena32
    have hhit := hok.hit (refill word count a pos stop hs hp).word.toNat
    rw [← hv1, ← hv2] at hhit
    have hl15 := hhit.le_15 hC
    have hl63 := and15 _ hl15
    have hrest : ∀ F, availBits word count a pos stop F =
        (refill word count a pos stop hs hp).buf.held ++ (chunkBits a (refill word count a pos stop hs hp).pos.toNat stop.toNat ++ F) := by
      intro F
      unfold availBits
      rw [← List.append_assoc, ← hbits, List.append_assoc]
    split
    · rename_i hl
      have hle := UInt64.le_iff_toNat_le.mp hl
      rw [hl63] at hle
      have hdec := fun F : List Bool => hhit.decode hC hle (chunkBits a (refill word count a pos stop hs hp).pos.toNat stop.toNat ++ F)
      have hsymlt : _ < literalAlphabetSize := decodeSymbol_lt hsym (hdec [])
      have hbyte := byte_of _ hsymlt
      simp only [← hbyte] at hdec
      have hlit : lit.count ≠ 0 := by omega
      obtain ⟨L', rfl⟩ : ∃ L', L = L' + 1 := ⟨L - 1, by omega⟩
      have hmapget : literalPrefixCodeIndex m.literalMap t
          (contextId (modeOff.toNat / 512) (contextBytes out).1 (contextBytes out).2) =
            some (lMap.uget (mapIndex mapBase (cidFast modeOff p1 p2 hm)) hi).toNat := by
        unfold literalPrefixCodeIndex
        rw [hctx]
        dsimp only
        rw [← hcidv, ← hmap, ← hidx]
        exact hmapv
      have hstep := fun F : List Bool => literal_step (w := w) (K := K) (s := s) (ic := ic) (c := c) (ilen := ilen)
        (clen := clen) (n := L') hlit hcur hmode hmapget hcode (hdec F)
      have hwr : wpos.toNat < ring.size := by rw [hsize]; exact hwp
      have hringNew := RingOk.write (v := (lookup arena _ (refill word count a pos stop hs hp).word hok.toTableFits C.arena32 >>> 4).toUInt8)
        hring hk hmask hwr
      have hnextLt : (ringNext wpos mask).toNat < 2 ^ k := hringNew.pos_lt
      have hsizeNew := hringNew.size
      have hdropLt : (lookup arena _ (refill word count a pos stop hs hp).word hok.toTableFits C.arena32 &&& 15).toNat < 64 := by
        rw [hl63]
        omega
      have hleCount := UInt64.le_iff_toNat_le.mp hl
      have hih := ih (n - USize.ofNat 1)
        ((BitBuffer.mk (refill word count a pos stop hs hp).word (refill word count a pos stop hs hp).count).drop
          (lookup arena _ (refill word count a pos stop hs hp).word hok.toTableFits C.arena32 &&& 15)).word
        ((BitBuffer.mk (refill word count a pos stop hs hp).word (refill word count a pos stop hs hp).count).drop
          (lookup arena _ (refill word count a pos stop hs hp).word hok.toTableFits C.arena32 &&& 15)).count
        (refill word count a pos stop hs hp).pos (ringNext wpos mask) _ _ p1 hrp2
        (BitBuffer.drop_wf hrw hdropLt hleCount) hsizeNew hnextLt L' { lit with count := lit.count - 1 } _
        (by omega) (by omega) (by show N ≤ lit.count - 1; omega) hcur (by rw [contextBytes_cons, hctx]) hringNew
        (by
          intro b hb
          rcases List.mem_cons.mp hb with rfl | hb
          · exact UInt8.toNat_lt _
          · exact hbytes b hb)
      dsimp only at hih
      generalize literalRun C a stop hs mapBase modeOff mask k hmb hm hd hmask hk (n - USize.ofNat 1) _ _ _ _ _ _ _ _ _ _ _ = run at hih ⊢
      obtain ⟨lit', out', h1, h2, h3, h4, h5, ⟨l0, hl0⟩, h6, h7, h8, h9, h10, h13, h11, h12, h14⟩ := hih
      refine ⟨lit', out', Nat.le_succ_of_le h1, h2, h3, ?_, ?_, ⟨l0 ++ [_], by rw [hl0, List.append_assoc]; rfl⟩, h6, h7, h8, by omega, h10, h13, ?_, ?_, ?_⟩
      rotate_left 3
      · intro hne
        have eL : L' + 1 - (N + 1 - run.left.toNat) = L' - (N - run.left.toNat) := by omega
        rw [eL]
        exact h12 hne
      · intro F
        have hw' := drop_word (BitBuffer.mk (refill word count a pos stop hs hp).word (refill word count a pos stop hs hp).count) hdropLt
        have hc' := drop_count (b := BitBuffer.mk (refill word count a pos stop hs hp).word (refill word count a pos stop hs hp).count) hleCount
        have e1 : (refill word count a pos stop hs hp).buf.held =
            lowBits (refill word count a pos stop hs hp).word.toNat (refill word count a pos stop hs hp).count.toNat := rfl
        have eL : L' + 1 - (N + 1 - run.left.toNat) = L' - (N - run.left.toNat) := by omega
        have hb : availBits ((BitBuffer.mk (refill word count a pos stop hs hp).word (refill word count a pos stop hs hp).count).drop
              (lookup arena _ (refill word count a pos stop hs hp).word hok.toTableFits C.arena32 &&& 15)).word
            ((BitBuffer.mk (refill word count a pos stop hs hp).word (refill word count a pos stop hs hp).count).drop
              (lookup arena _ (refill word count a pos stop hs hp).word hok.toTableFits C.arena32 &&& 15)).count
            a (refill word count a pos stop hs hp).pos stop F =
            lowBits ((refill word count a pos stop hs hp).word.toNat /
                2 ^ ((lookup arena _ (refill word count a pos stop hs hp).word hok.toTableFits C.arena32).toNat % 16))
              ((refill word count a pos stop hs hp).count.toNat -
                (lookup arena _ (refill word count a pos stop hs hp).word hok.toTableFits C.arena32).toNat % 16) ++
              (chunkBits a (refill word count a pos stop hs hp).pos.toNat stop.toNat ++ F) := by
          unfold availBits
          simp only [BitBuffer.held]
          rw [hw', hc', hl63]
        rw [hrest, e1, eL]
        refine (literal_reach (w := w) (s := s) (ic := ic) (c := c) (ilen := ilen) (clen := clen) (n := L') hlit hcur hmode hmapget
          hcode (hdec F)).trans ?_
        rw [← hb]
        exact h14 F
      · rw [h4]
        show lit.count - 1 - _ = _
        omega
      · rw [h5]
        simp only [List.length_cons]
        omega
      · intro F
        have hw' := drop_word (BitBuffer.mk (refill word count a pos stop hs hp).word (refill word count a pos stop hs hp).count) hdropLt
        have hc' := drop_count (b := BitBuffer.mk (refill word count a pos stop hs hp).word (refill word count a pos stop hs hp).count) hleCount
        have e1 : (refill word count a pos stop hs hp).buf.held =
            lowBits (refill word count a pos stop hs hp).word.toNat (refill word count a pos stop hs hp).count.toNat := rfl
        have eL : L' + 1 - (N + 1 - run.left.toNat) = L' - (N - run.left.toNat) := by omega
        rw [hrest, e1, hstep, eL, ← h11 F]
        unfold availBits
        simp only [BitBuffer.held]
        rw [hw', hc', hl63]
    · rename_i hl
      have hnot : (refill word count a pos stop hs hp).count.toNat < (lookup arena _ (refill word count a pos stop hs hp).word hok.toTableFits C.arena32 &&& 15).toNat :=
        Nat.lt_of_not_le fun hle => hl (UInt64.le_iff_toNat_le.mpr hle)
      rw [hl63] at hnot
      refine ⟨lit, out, by simp only; omega, rfl, rfl, by simp only; omega, by simp only; omega, ⟨[], rfl⟩, hring, hctx, hrw, hrp1, hrp2, hbytes, ?_, ?_, ?_⟩
      · intro F
        rw [hrest]
        simp only [hN, Nat.sub_self, Nat.sub_zero]
        rfl
      · intro _
        have hlit : lit.count ≠ 0 := by omega
        obtain ⟨L', rfl⟩ : ∃ L', L = L' + 1 := ⟨L - 1, by omega⟩
        have hmapget : literalPrefixCodeIndex m.literalMap t
            (contextId (modeOff.toNat / 512) (contextBytes out).1 (contextBytes out).2) =
              some (lMap.uget (mapIndex mapBase (cidFast modeOff p1 p2 hm)) hi).toNat := by
          unfold literalPrefixCodeIndex
          rw [hctx]
          dsimp only
          rw [← hcidv, ← hmap, ← hidx]
          exact hmapv
        refine ⟨?_, ?_, ?_⟩
        · rcases hdisj with h | h
          · omega
          · exact h
        · simp only [hN, Nat.sub_self, Nat.sub_zero]
          exact literal_none hlit hcur hmode hmapget hcode (hhit.short hC hnot)
        · simp only [hN, Nat.sub_self, Nat.sub_zero]
          exact literal_cshort hlit hcur hmode hmapget hcode (hhit.short hC hnot) (by simp only [BitBuffer.held, lowBits_length]; omega)
      · intro F
        rw [hrest]
        simp only [hN, Nat.sub_self, Nat.sub_zero]
        exact .refl _ _

end Brotli.Decoder
