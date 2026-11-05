module

public import Brotli.Decoder.Reader
public import Brotli.Decoder.CmdLut
public import Brotli.Spec.Stream

@[expose] public section

/-!
# Block switches

A block switch reads a block type and a block count. Together they take at most 54 bits, so a refilled buffer holds
them unless the chunk ran out, and the read is all or nothing: if the bits run short, nothing is used.
-/

namespace Brotli.Decoder

open Brotli.Spec

/-- Every symbol of the block count alphabet has a row in the table. -/
theorem blockCount_table {c : Nat} (h : c < blockCountAlphabetSize) :
    ∃ row, blockCountCodes[c]? = some row :=
  ⟨blockCountCodes[c]'(by rw [blockCountCodes_length]; exact h), List.getElem?_eq_getElem _⟩

/-- How a small read ended. -/
inductive ReadStatus where
  /-- It finished. -/
  | ok
  /-- The bits held can't finish it, and nothing was used. -/
  | short
  /-- The spec rejects, whatever bits follow. -/
  | bad
  deriving DecidableEq

/-- A block switch's result: the new buffer, block type and count, flat. -/
structure Switched where
  status : ReadStatus
  word : UInt64
  count : UInt64
  cur : UInt64
  blockCount : UInt64

/-- The block type a block type symbol gives. -/
@[inline] def nextTypeFast (n prev cur sym : UInt64) : UInt64 :=
  if sym = 0 then prev
  else if sym = 1 then (if cur + 1 = n then 0 else cur + 1)
  else sym - 2

/-- `nextTypeFast` is the spec's `nextBlockType`. -/
theorem nextTypeFast_toNat {n prev cur sym : UInt64} (hn : n.toNat < 2 ^ 16) (hc : cur.toNat < n.toNat) :
    (nextTypeFast n prev cur sym).toNat = nextBlockType n.toNat prev.toNat cur.toNat sym.toNat := by
  have h0 : (0 : UInt64).toNat = 0 := rfl
  have h1 : (1 : UInt64).toNat = 1 := rfl
  have h2 : (2 : UInt64).toNat = 2 := rfl
  have hsucc : (cur + 1).toNat = cur.toNat + 1 := by
    rw [UInt64.toNat_add, h1]
    exact Nat.mod_eq_of_lt (by omega)
  unfold nextTypeFast nextBlockType
  by_cases hs0 : sym = 0
  · subst hs0
    rfl
  · have hs0' : sym.toNat ≠ 0 := fun e => hs0 (UInt64.toNat_inj.mp (by rw [e]; rfl))
    rw [ite_eq_right hs0, ite_eq_right hs0']
    by_cases hs1 : sym = 1
    · subst hs1
      rw [ite_eq_left rfl, ite_eq_left h1]
      by_cases he : cur + 1 = n
      · have he' : cur.toNat = n.toNat - 1 := by
          have := congrArg UInt64.toNat he
          omega
        rw [ite_eq_left he, ite_eq_left he']
        rfl
      · have he' : ¬ cur.toNat = n.toNat - 1 := fun e => he (UInt64.toNat_inj.mp (by omega))
        rw [ite_eq_right he, ite_eq_right he', hsucc]
    · have hs1' : sym.toNat ≠ 1 := fun e => hs1 (UInt64.toNat_inj.mp (by rw [e]; rfl))
      rw [ite_eq_right hs1, ite_eq_right hs1']
      rw [UInt64.toNat_sub_of_le _ _ (UInt64.le_iff_toNat_le.mpr (by rw [h2]; omega)), h2]

/-- A block switch's count, once its symbol is looked up. -/
@[inline] def countStep (next cur word count : UInt64) (b1 : BitBuffer) (v2 : UInt64) : Switched :=
  if hc : wordSym v2 < 26 then
    let row := countRow (wordSym v2) (lt26 hc)
    let b2 := b1.drop (wordBits v2)
    if rowBits row ≤ b2.count then
      let b3 := b2.drop (rowBits row)
      ⟨.ok, b3.word, b3.count, next, rowBase row + b2.peek (rowBits row)⟩
    else ⟨.short, word, count, cur, 0⟩
  else ⟨.bad, word, count, cur, 0⟩

/-- Reads a block switch's type and count. Inlined, so that its result is read as it is built and never allocated. -/
@[inline] def blockSwitch (arena : ByteArray) (h32 : arena.size < 2 ^ 32) (tBase cBase : USize) (hT : TableFits arena tBase.toNat)
    (hC : TableFits arena cBase.toNat) (n cur prev word count : UInt64) : Switched :=
  let b0 : BitBuffer := ⟨word, count⟩
  let v1 := lookup arena tBase word hT h32
  let l1 := wordBits v1
  if l1 ≤ count then
    let next := nextTypeFast n prev cur (wordSym v1)
    if next = cur then ⟨.bad, word, count, cur, 0⟩
    else
      let b1 := b0.drop l1
      let v2 := lookup arena cBase b1.word hC h32
      let l2 := wordBits v2
      if l2 ≤ b1.count then countStep next cur word count b1 v2
      else ⟨.short, word, count, cur, 0⟩
  else ⟨.short, word, count, cur, 0⟩

private theorem rows_low : ∀ r ∈ blockCountCodes, 1 ≤ r.2.1 := by
  decide +kernel

private theorem rows_fit {c bits lowest high : Nat} (h : blockCountCodes[c]? = some (bits, lowest, high)) :
    bits ≤ 24 ∧ 1 ≤ lowest ∧ lowest + 2 ^ bits ≤ 16793841 := by
  have hmem := List.mem_of_getElem? h
  have h1 := blockCountCodes_extraBits.1 _ hmem
  have h2 := blockCountCodes_ranges _ hmem
  have h3 := blockCountCodes_largest.1 _ hmem
  have h4 := rows_low _ hmem
  have hp : 0 < 2 ^ bits := Nat.two_pow_pos _
  simp only at h1 h2 h3 h4
  omega

private theorem readBlockType_of {n : Nat} {code : PrefixCode} {bt : BlockTypes} {bs r : List Bool} {sym : Nat}
    (h : decodeSymbol code bs = some (sym, r)) :
    readBlockType n code bt bs =
      if (switchBlockType n bt sym).cur = bt.cur then none else some (switchBlockType n bt sym, r) := by
  unfold readBlockType
  rw [h]
  rfl

private theorem if_cur_eq {α : Type} {n : Nat} {bt : BlockTypes} {sym : Nat} {a b : Option α}
    (h : nextBlockType n bt.prev bt.cur sym = bt.cur) :
    (if (switchBlockType n bt sym).cur = bt.cur then a else b) = a := by
  have : (switchBlockType n bt sym).cur = bt.cur := h
  rw [ite_eq_left this]

private theorem if_cur_ne {α : Type} {n : Nat} {bt : BlockTypes} {sym : Nat} {a b : Option α}
    (h : ¬ nextBlockType n bt.prev bt.cur sym = bt.cur) :
    (if (switchBlockType n bt sym).cur = bt.cur then a else b) = b := by
  have : ¬ (switchBlockType n bt sym).cur = bt.cur := h
  rw [ite_eq_right this]

private theorem readBlockCount_some {code : PrefixCode} {bs r r' : List Bool} {c bits lowest high e : Nat}
    (h : decodeSymbol code bs = some (c, r)) (hr : blockCountCodes[c]? = some (bits, lowest, high))
    (hx : readInt bits r = some (e, r')) : readBlockCount code bs = some (lowest + e, r') := by
  unfold readBlockCount
  rw [h]
  dsimp only [bind, Option.bind]
  rw [hr]
  dsimp only
  rw [hx]

private theorem readBlockCount_noBits {code : PrefixCode} {bs r : List Bool} {c bits lowest high : Nat}
    (h : decodeSymbol code bs = some (c, r)) (hr : blockCountCodes[c]? = some (bits, lowest, high))
    (hx : readInt bits r = none) : readBlockCount code bs = none := by
  unfold readBlockCount
  rw [h]
  dsimp only [bind, Option.bind]
  rw [hr]
  dsimp only
  rw [hx]

/-- What a block switch does, in the spec's terms, for a category with at least two block types. When it finishes,
the spec's `nextElement` gives the same block types and count, whatever bits follow. When it's short, nothing was
used and the bits held are fewer than a switch can take. When it rejects, so does the spec. -/
theorem blockSwitch_spec {arena : ByteArray} {h32 : arena.size < 2 ^ 32} {tBase cBase : USize}
    {hT : TableFits arena tBase.toNat} {hC : TableFits arena cBase.toNat} {cur prev word count : UInt64} {c : BlockCategory}
    {n : UInt64} (hnn : n.toNat = c.n) (okT : TableOk arena tBase.toNat c.typeCode) (okC : TableOk arena cBase.toNat c.countCode)
    (cT : Complete c.typeCode) (cC : Complete c.countCode) (hw : (BitBuffer.mk word count).Wf) (hn2 : 2 ≤ c.n)
    (hn : c.n < 2 ^ 16) (hsym : c.typeCode.Symbols (blockTypeAlphabetSize c.n))
    (hcnt : c.countCode.Symbols blockCountAlphabetSize) (hcn : cur.toNat < c.n) (hpn : prev.toNat < c.n)
    (seen : List Nat) :
    let r := blockSwitch arena h32 tBase cBase hT hC n cur prev word count
    (r.status = .ok → (BitBuffer.mk r.word r.count).Wf ∧ r.cur.toNat < c.n ∧
      1 ≤ r.blockCount.toNat ∧ r.blockCount.toNat ≤ 16793840 ∧ ∀ f,
      nextElement c ⟨⟨prev.toNat, cur.toNat⟩, 0, seen⟩ ((BitBuffer.mk word count).held ++ f) =
        some (⟨⟨cur.toNat, r.cur.toNat⟩, r.blockCount.toNat - 1, r.cur.toNat :: seen⟩,
          (BitBuffer.mk r.word r.count).held ++ f)) ∧
    (r.status = .short → r.word = word ∧ r.count = count ∧ count.toNat < 54 ∧
      nextElement c ⟨⟨prev.toNat, cur.toNat⟩, 0, seen⟩ (BitBuffer.mk word count).held = none) ∧
    (r.status = .bad → ∀ f, nextElement c ⟨⟨prev.toNat, cur.toNat⟩, 0, seen⟩ ((BitBuffer.mk word count).held ++ f) = none) := by
  have hnotlt : ¬ c.n < 2 := by omega
  have hnext : ∀ f, nextElement c ⟨⟨prev.toNat, cur.toNat⟩, 0, seen⟩ ((BitBuffer.mk word count).held ++ f) =
      readBlockType c.n c.typeCode ⟨prev.toNat, cur.toNat⟩ ((BitBuffer.mk word count).held ++ f) >>= fun (types, bs) =>
      readBlockCount c.countCode bs >>= fun (cnt, bs) => some (⟨types, cnt - 1, types.cur :: seen⟩, bs) := by
    intro f
    simp only [nextElement, ↓reduceIte, hnotlt]
  have hnextNil : nextElement c ⟨⟨prev.toNat, cur.toNat⟩, 0, seen⟩ (BitBuffer.mk word count).held =
      readBlockType c.n c.typeCode ⟨prev.toNat, cur.toNat⟩ (BitBuffer.mk word count).held >>= fun (types, bs) =>
      readBlockCount c.countCode bs >>= fun (cnt, bs) => some (⟨types, cnt - 1, types.cur :: seen⟩, bs) := by
    simp only [nextElement, ↓reduceIte, hnotlt]
  have L1 := lookup_read (b := ⟨word, count⟩) okT hT h32 cT
  dsimp only at L1
  obtain ⟨t1, h1ok, h1short⟩ := L1
  dsimp only
  unfold blockSwitch
  dsimp only
  generalize lookup arena tBase word hT h32 = v1 at t1 h1ok h1short ⊢
  split
  · rename_i hl1
    have hl1' : (wordBits v1).toNat ≤ count.toNat := UInt64.le_iff_toNat_le.mp hl1
    have hd1 := h1ok hl1
    have hd1Nil := hd1 []
    rw [List.append_nil, List.append_nil] at hd1Nil
    have hsym1 : wordValue v1 < blockTypeAlphabetSize c.n := decodeSymbol_lt hsym hd1Nil
    have hnx : (nextTypeFast n prev cur (wordSym v1)).toNat = nextBlockType c.n prev.toNat cur.toNat (wordValue v1) := by
      rw [nextTypeFast_toNat (by omega) (by omega), hnn]
      rfl
    have hltn := nextBlockType_lt hpn hcn hsym1
    split
    · rename_i heq
      refine ⟨fun h => ReadStatus.noConfusion h, fun h => ReadStatus.noConfusion h, fun _ f => ?_⟩
      have he : nextBlockType c.n prev.toNat cur.toNat (wordValue v1) = cur.toNat := by
        rw [← hnx, heq]
      rw [hnext, readBlockType_of (hd1 f), if_cur_eq he]
      rfl
    · rename_i hne
      have he : ¬ nextBlockType c.n prev.toNat cur.toNat (wordValue v1) = cur.toNat := by
        rw [← hnx]
        exact fun e => hne (UInt64.toNat_inj.mp e)
      have hw1 := BitBuffer.drop_wf hw (wordBits_lt v1) hl1'
      have hc1 : ((BitBuffer.mk word count).drop (wordBits v1)).count.toNat = count.toNat - (wordBits v1).toNat :=
        drop_count hl1'
      generalize hb1 : (BitBuffer.mk word count).drop (wordBits v1) = b1 at hd1 hd1Nil hw1 hc1 ⊢
      have L2 := lookup_read (b := b1) okC hC h32 cC
      dsimp only at L2
      obtain ⟨t2, h2ok, h2short⟩ := L2
      generalize lookup arena cBase b1.word hC h32 = v2 at t2 h2ok h2short ⊢
      split
      · rename_i hl2
        have hl2' := UInt64.le_iff_toNat_le.mp hl2
        have hd2 := h2ok hl2
        have hd2Nil := hd2 []
        rw [List.append_nil, List.append_nil] at hd2Nil
        have hsym2 : wordValue v2 < blockCountAlphabetSize := decodeSymbol_lt hcnt hd2Nil
        have hsym26 : (wordSym v2).toNat < 26 := hsym2
        have h26 : (26 : UInt64).toNat = 26 := rfl
        have hcU : wordSym v2 < 26 := UInt64.lt_iff_toNat_lt.mpr (by rw [h26]; exact hsym26)
        unfold countStep
        rw [dite_eq_left hcU]
        dsimp only
        obtain ⟨⟨bits, lowest, high⟩, hrow⟩ := blockCount_table hsym2
        obtain ⟨hb24, hlow, hmax⟩ := rows_fit hrow
        have hgetD : blockCountCodes.getD (wordSym v2).toNat (0, 0, 0) = (bits, lowest, high) := by
          rw [List.getD_eq_getElem?_getD]
          show (blockCountCodes[wordValue v2]?).getD _ = _
          rw [hrow]
          rfl
        obtain ⟨hk, hlo⟩ := countRow_fields (lt26 hcU)
        rw [hgetD] at hk hlo
        generalize countRow (wordSym v2) (lt26 hcU) = row at hk hlo ⊢
        have hw2 := BitBuffer.drop_wf hw1 (wordBits_lt v2) hl2'
        have hc2 : (b1.drop (wordBits v2)).count.toNat = b1.count.toNat - (wordBits v2).toNat := drop_count hl2'
        generalize b1.drop (wordBits v2) = b2 at hd2 hd2Nil hw2 hc2 ⊢
        have hk' : (rowBits row).toNat = bits := hk
        have hlo' : (rowBase row).toNat = lowest := hlo
        split
        · rename_i hk3
          have hk3' := UInt64.le_iff_toNat_le.mp hk3
          have hext := fun f => read_int (b := b2) (k := rowBits row) f (by omega) hk3
          rw [hk'] at hext
          have hx := BitBuffer.peek_toNat b2 (k := rowBits row) (by omega)
          rw [hk'] at hx
          have hxlt : (b2.peek (rowBits row)).toNat < 2 ^ bits := by
            rw [hx]
            exact Nat.mod_lt _ (Nat.two_pow_pos _)
          have hsum : (rowBase row + b2.peek (rowBits row)).toNat = lowest + (b2.peek (rowBits row)).toNat := by
            rw [UInt64.toNat_add, hlo']
            exact Nat.mod_eq_of_lt (by have : (16793841 : Nat) < 2 ^ 64 := by decide
                                       omega)
          have hwf := BitBuffer.drop_wf hw2 (k := rowBits row) (by omega) hk3'
          generalize b2.drop (rowBits row) = b3 at hext hwf ⊢
          refine ⟨fun _ => ⟨hwf, by show (nextTypeFast n prev cur (wordSym v1)).toNat < c.n; rw [hnx]; exact hltn,
              ?_, ?_, fun f => ?_⟩, fun h => ReadStatus.noConfusion h, fun h => ReadStatus.noConfusion h⟩
          · show 1 ≤ (rowBase row + b2.peek (rowBits row)).toNat
            omega
          · show (rowBase row + b2.peek (rowBits row)).toNat ≤ 16793840
            omega
          · rw [hnext, readBlockType_of (hd1 f), if_cur_ne he]
            dsimp only [bind, Option.bind]
            rw [readBlockCount_some (hd2 f) hrow (hext f)]
            show _ = some ((⟨⟨cur.toNat, (nextTypeFast n prev cur (wordSym v1)).toNat⟩,
              (rowBase row + b2.peek (rowBits row)).toNat - 1, (nextTypeFast n prev cur (wordSym v1)).toNat :: seen⟩ : BlockState), _)
            rw [hsum, hnx]
            rfl
        · rename_i hk3
          have hnot : b2.count.toNat < bits := by
            rw [← hk']
            exact Nat.lt_of_not_le fun h => hk3 (UInt64.le_iff_toNat_le.mpr h)
          have hshort := readInt_short (b := b2) hnot
          refine ⟨fun h => ReadStatus.noConfusion h, fun _ => ⟨rfl, rfl, by omega, ?_⟩, fun h => ReadStatus.noConfusion h⟩
          rw [hnextNil, readBlockType_of hd1Nil, if_cur_ne he]
          dsimp only [bind, Option.bind]
          rw [readBlockCount_noBits hd2Nil hrow hshort]
      · rename_i hl2
        have hnot : b1.count.toNat < (wordBits v2).toNat := Nat.lt_of_not_le fun h => hl2 (UInt64.le_iff_toNat_le.mpr h)
        refine ⟨fun h => ReadStatus.noConfusion h, fun _ => ⟨rfl, rfl, by omega, ?_⟩, fun h => ReadStatus.noConfusion h⟩
        rw [hnextNil, readBlockType_of hd1Nil, if_cur_ne he]
        dsimp only [bind, Option.bind]
        unfold readBlockCount
        rw [h2short hl2]
        rfl
  · rename_i hl1
    have hnot : count.toNat < (wordBits v1).toNat :=
      Nat.lt_of_not_le fun h => hl1 (UInt64.le_iff_toNat_le.mpr h)
    refine ⟨fun h => ReadStatus.noConfusion h, fun _ => ⟨rfl, rfl, by omega, ?_⟩, fun h => ReadStatus.noConfusion h⟩
    rw [hnextNil]
    unfold readBlockType
    rw [h1short hl1]
    rfl

end Brotli.Decoder
