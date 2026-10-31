import Brotli.Decoder.Reader

/-!
# Block switches

A block switch reads a block type and a block count. Together they take at most 54 bits, so a refilled buffer holds
them unless the chunk ran out, and the read is all or nothing: if the bits run short, nothing is used.
-/

namespace Brotli.Decoder

open Brotli.Spec Brotli.Properties

/-- How a small read ended. -/
inductive ReadStatus where
  /-- It finished. -/
  | ok
  /-- The bits held can't finish it, and nothing was used. -/
  | short
  /-- The spec rejects, whatever bits follow. -/
  | bad
  deriving DecidableEq

/-- A block switch's result: the new buffer, block types and count, flat. -/
structure Switched where
  status : ReadStatus
  word : UInt64
  count : UInt64
  cur : UInt64
  prev : UInt64
  blockCount : UInt64

/-- Reads a block switch's type and count. -/
def blockSwitch (arena : ByteArray) (h32 : arena.size < 2 ^ 32) (tBase cBase : USize) (hT : TableFits arena tBase.toNat)
    (hC : TableFits arena cBase.toNat) (n : Nat) (cur prev word count : UInt64) : Switched :=
  let b0 : BitBuffer := ⟨word, count⟩
  let v1 := lookup arena tBase word hT h32
  let l1 := wordBits v1
  if l1 ≤ count then
    let next := nextBlockType n prev.toNat cur.toNat (wordValue v1)
    if next = cur.toNat then ⟨.bad, word, count, cur, prev, 0⟩
    else
      let b1 := b0.drop l1
      let v2 := lookup arena cBase b1.word hC h32
      let l2 := wordBits v2
      if l2 ≤ b1.count then
        match blockCountCodes[wordValue v2]? with
        | none => ⟨.bad, word, count, cur, prev, 0⟩
        | some (bits, lowest, _) =>
          let b2 := b1.drop l2
          let k := UInt64.ofNat bits
          if k ≤ b2.count then
            let extra := (b2.peek k).toNat
            let b3 := b2.drop k
            ⟨.ok, b3.word, b3.count, UInt64.ofNat next, cur, UInt64.ofNat (lowest + extra)⟩
          else ⟨.short, word, count, cur, prev, 0⟩
      else ⟨.short, word, count, cur, prev, 0⟩
  else ⟨.short, word, count, cur, prev, 0⟩

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

private theorem ofNat_small {n : Nat} (h : n < 2 ^ 32) : (UInt64.ofNat n).toNat = n := by
  rw [UInt64.toNat_ofNat']
  exact Nat.mod_eq_of_lt (by omega)

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

private theorem readBlockCount_none {code : PrefixCode} {bs r : List Bool} {c : Nat}
    (h : decodeSymbol code bs = some (c, r)) (hr : blockCountCodes[c]? = none) : readBlockCount code bs = none := by
  unfold readBlockCount
  rw [h]
  dsimp only [bind, Option.bind]
  rw [hr]

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
    {n : Nat} (hnn : n = c.n) (okT : TableOk arena tBase.toNat c.typeCode) (okC : TableOk arena cBase.toNat c.countCode)
    (cT : Complete c.typeCode) (cC : Complete c.countCode) (hw : (BitBuffer.mk word count).Wf) (hn2 : 2 ≤ c.n)
    (hn : c.n < 2 ^ 16) (hsym : c.typeCode.Symbols (blockTypeAlphabetSize c.n))
    (hcnt : c.countCode.Symbols blockCountAlphabetSize) (hcn : cur.toNat < c.n) (hpn : prev.toNat < c.n)
    (seen : List Nat) :
    let r := blockSwitch arena h32 tBase cBase hT hC n cur prev word count
    (r.status = .ok → (BitBuffer.mk r.word r.count).Wf ∧ r.cur.toNat < c.n ∧ r.prev = cur ∧
      1 ≤ r.blockCount.toNat ∧ r.blockCount.toNat ≤ 16793840 ∧ ∀ f,
      nextElement c ⟨⟨prev.toNat, cur.toNat⟩, 0, seen⟩ ((BitBuffer.mk word count).held ++ f) =
        some (⟨⟨cur.toNat, r.cur.toNat⟩, r.blockCount.toNat - 1, r.cur.toNat :: seen⟩,
          (BitBuffer.mk r.word r.count).held ++ f)) ∧
    (r.status = .short → r.word = word ∧ r.count = count ∧ count.toNat < 54 ∧
      nextElement c ⟨⟨prev.toNat, cur.toNat⟩, 0, seen⟩ (BitBuffer.mk word count).held = none) ∧
    (r.status = .bad → ∀ f, nextElement c ⟨⟨prev.toNat, cur.toNat⟩, 0, seen⟩ ((BitBuffer.mk word count).held ++ f) = none) := by
  subst hnn
  have hnotlt : ¬ c.n < 2 := by omega
  have hnext : ∀ f, nextElement c ⟨⟨prev.toNat, cur.toNat⟩, 0, seen⟩ ((BitBuffer.mk word count).held ++ f) =
      readBlockType c.n c.typeCode ⟨prev.toNat, cur.toNat⟩ ((BitBuffer.mk word count).held ++ f) >>= fun (types, bs) =>
      readBlockCount c.countCode bs >>= fun (cnt, bs) => some (⟨types, cnt - 1, types.cur :: seen⟩, bs) := by
    intro f
    simp only [nextElement, ↓reduceIte, hnotlt]
  have L1 := lookup_read (b := ⟨word, count⟩) okT hT h32 cT
  dsimp only at L1
  obtain ⟨t1, h1ok, h1short⟩ := L1
  have hnextNil : nextElement c ⟨⟨prev.toNat, cur.toNat⟩, 0, seen⟩ (BitBuffer.mk word count).held =
      readBlockType c.n c.typeCode ⟨prev.toNat, cur.toNat⟩ (BitBuffer.mk word count).held >>= fun (types, bs) =>
      readBlockCount c.countCode bs >>= fun (cnt, bs) => some (⟨types, cnt - 1, types.cur :: seen⟩, bs) := by
    simp only [nextElement, ↓reduceIte, hnotlt]
  dsimp only
  unfold blockSwitch
  dsimp only
  split
  · rename_i hl1
    have hd1 := h1ok hl1
    split
    · rename_i heq
      refine ⟨fun h => ReadStatus.noConfusion h, fun h => ReadStatus.noConfusion h, fun _ f => ?_⟩
      rw [hnext, readBlockType_of (hd1 f), if_cur_eq heq]
      rfl
    · rename_i hne
      have hw1 := BitBuffer.drop_wf hw (wordBits_lt _) (UInt64.le_iff_toNat_le.mp hl1)
      have L2 := lookup_read (b := (BitBuffer.mk word count).drop (wordBits (lookup arena tBase word hT h32)))
        okC hC h32 cC
      dsimp only at L2
      obtain ⟨t2, h2ok, h2short⟩ := L2
      have hd1Nil := hd1 []
      rw [List.append_nil, List.append_nil] at hd1Nil
      split
      · rename_i hl2
        have hd2 := h2ok hl2
        have hw2 := BitBuffer.drop_wf hw1 (wordBits_lt _) (UInt64.le_iff_toNat_le.mp hl2)
        split
        · rename_i hnone
          refine ⟨fun h => ReadStatus.noConfusion h, fun h => ReadStatus.noConfusion h, fun _ f => ?_⟩
          rw [hnext, readBlockType_of (hd1 f), if_cur_ne hne]
          dsimp only [bind, Option.bind]
          rw [readBlockCount_none (hd2 f) hnone]
        · rename_i bits lowest high hrow
          obtain ⟨hb24, hlow, hmax⟩ := rows_fit hrow
          have hk : (UInt64.ofNat bits).toNat = bits := ofNat_small (by omega)
          split
          · rename_i hk3
            have hext := fun f => read_int (b := ((BitBuffer.mk word count).drop (wordBits (lookup arena tBase word hT h32))).drop
              (wordBits (lookup arena cBase ((BitBuffer.mk word count).drop (wordBits (lookup arena tBase word hT h32))).word hC h32)))
              f (by rw [hk]; omega) hk3
            rw [hk] at hext
            have hx := BitBuffer.peek_toNat ((((BitBuffer.mk word count).drop (wordBits (lookup arena tBase word hT h32))).drop
              (wordBits (lookup arena cBase ((BitBuffer.mk word count).drop (wordBits (lookup arena tBase word hT h32))).word hC h32))))
              (k := UInt64.ofNat bits) (by rw [hk]; omega)
            have hextra : ∀ x : UInt64, x.toNat % 2 ^ bits < 2 ^ bits := fun x => Nat.mod_lt _ (Nat.two_pow_pos _)
            have hxlt := hextra ((((BitBuffer.mk word count).drop (wordBits (lookup arena tBase word hT h32))).drop
              (wordBits (lookup arena cBase ((BitBuffer.mk word count).drop (wordBits (lookup arena tBase word hT h32))).word hC h32)))).word
            rw [hk] at hx
            rw [← hx] at hxlt
            have hsym1 : wordValue (lookup arena tBase word hT h32) < blockTypeAlphabetSize c.n := decodeSymbol_lt hsym (hd1 [])
            have hltn := nextBlockType_lt hpn hcn hsym1
            have hnu : (UInt64.ofNat (nextBlockType c.n prev.toNat cur.toNat (wordValue (lookup arena tBase word hT h32)))).toNat =
                nextBlockType c.n prev.toNat cur.toNat (wordValue (lookup arena tBase word hT h32)) :=
              ofNat_small (by have : (2 : Nat) ^ 16 ≤ 2 ^ 32 := by decide
                              omega)
            have hcu : ∀ e, e < 2 ^ bits → (UInt64.ofNat (lowest + e)).toNat = lowest + e := by
              intro e he
              exact ofNat_small (by have : (16793841 : Nat) < 2 ^ 32 := by decide
                                    omega)
            refine ⟨fun _ => ⟨BitBuffer.drop_wf hw2 (by rw [hk]; omega) (UInt64.le_iff_toNat_le.mp hk3), ?_, rfl, ?_, ?_, ?_⟩,
              fun h => ReadStatus.noConfusion h, fun h => ReadStatus.noConfusion h⟩
            · simp only [hnu]
              exact hltn
            · simp only [hcu _ hxlt]
              omega
            · simp only [hcu _ hxlt]
              omega
            · intro f
              rw [hnext, readBlockType_of (hd1 f), if_cur_ne hne]
              dsimp only [bind, Option.bind]
              rw [readBlockCount_some (hd2 f) hrow (hext f)]
              simp only [hnu, hcu _ hxlt]
              rfl
          · rename_i hk3
            have hsym2 : wordValue (lookup arena cBase ((BitBuffer.mk word count).drop (wordBits (lookup arena tBase word hT h32))).word hC h32) <
                blockCountAlphabetSize := decodeSymbol_lt hcnt (hd2 [])
            have hnot : ((((BitBuffer.mk word count).drop (wordBits (lookup arena tBase word hT h32))).drop
                (wordBits (lookup arena cBase ((BitBuffer.mk word count).drop (wordBits (lookup arena tBase word hT h32))).word hC h32)))).count.toNat < bits := by
              rw [← hk]
              exact Nat.lt_of_not_le fun h => hk3 (UInt64.le_iff_toNat_le.mpr h)
            rw [drop_count (UInt64.le_iff_toNat_le.mp hl2), drop_count (UInt64.le_iff_toNat_le.mp hl1)] at hnot
            have hl1' := UInt64.le_iff_toNat_le.mp hl1
            have hl2' := UInt64.le_iff_toNat_le.mp hl2
            rw [drop_count (UInt64.le_iff_toNat_le.mp hl1)] at hl2'
            have hd2Nil := hd2 []
            rw [List.append_nil, List.append_nil] at hd2Nil
            have hshort := readInt_short (b := ((BitBuffer.mk word count).drop (wordBits (lookup arena tBase word hT h32))).drop
              (wordBits (lookup arena cBase ((BitBuffer.mk word count).drop (wordBits (lookup arena tBase word hT h32))).word hC h32)))
              (k := bits) (by
                rw [drop_count (UInt64.le_iff_toNat_le.mp hl2), drop_count (UInt64.le_iff_toNat_le.mp hl1)]
                exact hnot)
            refine ⟨fun h => ReadStatus.noConfusion h, fun _ => ⟨rfl, rfl, by simp only at hnot hl1' hl2' t1 t2 ⊢; omega, ?_⟩,
              fun h => ReadStatus.noConfusion h⟩
            rw [hnextNil, readBlockType_of hd1Nil, if_cur_ne hne]
            dsimp only [bind, Option.bind]
            rw [readBlockCount_noBits hd2Nil hrow hshort]
      · rename_i hl2
        have hnot : ((BitBuffer.mk word count).drop (wordBits (lookup arena tBase word hT h32))).count.toNat <
            (wordBits (lookup arena cBase ((BitBuffer.mk word count).drop (wordBits (lookup arena tBase word hT h32))).word hC h32)).toNat :=
          Nat.lt_of_not_le fun h => hl2 (UInt64.le_iff_toNat_le.mpr h)
        rw [drop_count (UInt64.le_iff_toNat_le.mp hl1)] at hnot
        refine ⟨fun h => ReadStatus.noConfusion h, fun _ => ⟨rfl, rfl, by simp only at hnot t1 t2 ⊢; omega, ?_⟩,
          fun h => ReadStatus.noConfusion h⟩
        rw [hnextNil, readBlockType_of hd1Nil, if_cur_ne hne]
        dsimp only [bind, Option.bind]
        unfold readBlockCount
        rw [h2short hl2]
        rfl
  · rename_i hl1
    have hnot : count.toNat < (wordBits (lookup arena tBase word hT h32)).toNat :=
      Nat.lt_of_not_le fun h => hl1 (UInt64.le_iff_toNat_le.mpr h)
    refine ⟨fun h => ReadStatus.noConfusion h, fun _ => ⟨rfl, rfl, by omega, ?_⟩, fun h => ReadStatus.noConfusion h⟩
    rw [hnextNil]
    unfold readBlockType
    rw [h1short hl1]
    rfl

end Brotli.Decoder
