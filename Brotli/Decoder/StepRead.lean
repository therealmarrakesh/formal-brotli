import Brotli.Decoder.Step
import Brotli.Decoder.CmdLut

/-!
# The steps that read bits

Each runs on a buffer that a refill has just filled, so the bits held fall short only when the chunk is used up.
-/

namespace Brotli.Decoder

open Brotli.Spec Brotli.Properties

/-! ### Small facts -/

theorem u64_sub {a b : UInt64} (h : b.toNat ≤ a.toNat) : (a - b).toNat = a.toNat - b.toNat :=
  UInt64.toNat_sub_of_le _ _ (UInt64.le_iff_toNat_le.mpr h)

theorem u64_sub_one {a : UInt64} (h : 1 ≤ a.toNat) : (a - 1).toNat = a.toNat - 1 :=
  u64_sub (b := 1) h

theorem u64_add {a b : UInt64} (h : a.toNat + b.toNat < 2 ^ 32) : (a + b).toNat = a.toNat + b.toNat := by
  rw [UInt64.toNat_add]
  exact Nat.mod_eq_of_lt (by omega)

/-- The bits of a state, with the chunk and future written out. -/
theorem stateBits_eq (st : Cmd) (a : ByteArray) (pos stop : USize) (F : List Bool) :
    stateBits st a pos stop F = (BitBuffer.mk st.word st.count).held ++ (chunkBits a pos.toNat stop.toNat ++ F) :=
  rfl

/-! ### Block states -/

/-- Marks a block type as having occurred, at flag `i`. -/
@[inline] def markSeen (seen : ByteArray) (i : USize) : ByteArray :=
  if h : i.toNat < seen.size then seen.uset i 1 h else seen

private theorem data_uset (t : ByteArray) (i : USize) (v : UInt8) (h : i.toNat < t.size) :
    (t.uset i v h).data = t.data.set i.toNat v h := by
  cases t
  rfl

theorem size_markSeen (seen : ByteArray) (i : USize) : (markSeen seen i).size = seen.size := by
  unfold markSeen
  split
  · rename_i h
    show (seen.uset i 1 h).data.size = seen.data.size
    rw [data_uset, Array.size_set]
  · rfl

private theorem flag_same {seen : ByteArray} {i : USize} (h : i.toNat < seen.size) :
    ((markSeen seen i).data[i.toNat]?.getD 0) = 1 := by
  unfold markSeen
  rw [dite_eq_left h, data_uset]
  simp

private theorem flag_other {seen : ByteArray} {i : USize} {j : Nat} (h : j ≠ i.toNat) :
    (markSeen seen i).data[j]? = seen.data[j]? := by
  unfold markSeen
  split
  · rw [data_uset, Array.getElem?_set, ite_eq_right (Ne.symm h)]
  · rfl

/-- The position of a block type's flag. -/
theorem seen_index {off : Nat} {t : UInt64} (hoff : off ≤ 512) (ht : t.toNat < 256) :
    (USize.ofNat off + t.toUSize).toNat = off + t.toNat := by
  have hu : t.toUSize.toNat = t.toNat := word_toUSize (by omega)
  rw [USize.toNat_add, usize_ofNat' (by omega), hu, ← USize.size_eq_two_pow]
  have := USize.le_size
  exact Nat.mod_eq_of_lt (by omega)

/-- A block state's count going down by one. -/
theorem BlockRel.decr {seen : ByteArray} {off : Nat} {cur prev count : UInt64} {st : BlockState} {c : BlockCategory}
    (b : BlockRel seen off cur prev count st c) (h : count.toNat ≠ 0) :
    BlockRel seen off cur prev (count - 1) { st with count := st.count - 1 } c := by
  refine { b with count := ?_ }
  show st.count - 1 = _
  rw [u64_sub_one (by omega), b.count]

/-- A block switch, for the category whose flags it marks. -/
theorem BlockRel.switched {seen : ByteArray} {off : Nat} {i : USize} {cur prev count next cnt : UInt64} {st : BlockState}
    {c : BlockCategory} {v : Nat} (b : BlockRel seen off cur prev count st c) (hoff : off + 256 ≤ seen.size)
    (hi : i.toNat = off + next.toNat) (hn : next.toNat < c.n) (hv : v = cnt.toNat) :
    BlockRel (markSeen seen i) off next cur cnt ⟨⟨cur.toNat, next.toNat⟩, v, next.toNat :: st.seen⟩ c := by
  refine ⟨rfl, rfl, hv, ⟨fun _ => ?_, hn, ?_⟩, ?_⟩
  · have := b.wf.2.1
    rw [b.cur] at this
    exact this
  · intro t ht
    rcases List.mem_cons.mp ht with rfl | ht
    · exact hn
    · exact b.wf.2.2 t ht
  · intro t ht
    by_cases he : t = next.toNat
    · subst he
      rw [← hi, flag_same (by omega)]
      simp
    · have hne : off + t ≠ i.toNat := by omega
      rw [flag_other hne]
      have hm := b.flags t ht
      constructor
      · intro hf
        exact List.mem_cons_of_mem _ (hm.mp hf)
      · intro hf
        rcases List.mem_cons.mp hf with hf | hf
        · exact absurd hf he
        · exact hm.mpr hf

/-- Marking another category's flag leaves a block state's flags alone. -/
theorem BlockRel.marked {seen : ByteArray} {off : Nat} {i : USize} {cur prev count : UInt64} {st : BlockState} {c : BlockCategory}
    (b : BlockRel seen off cur prev count st c) (hdis : ∀ t, t < 256 → off + t ≠ i.toNat) :
    BlockRel (markSeen seen i) off cur prev count st c := by
  refine { b with flags := ?_ }
  intro t ht
  rw [flag_other (hdis t ht)]
  exact b.flags t ht

/-- A literal run keeps the block types and flags. -/
theorem BlockRel.run {seen : ByteArray} {off : Nat} {cur prev count count' : UInt64} {st st' : BlockState} {c : BlockCategory}
    (b : BlockRel seen off cur prev count st c) (h1 : st'.types = st.types) (h2 : st'.seen = st.seen)
    (h3 : st'.count = count'.toNat) : BlockRel seen off cur prev count' st' c := by
  refine ⟨by rw [h1]; exact b.cur, by rw [h1]; exact b.prev, h3, ?_, by rw [h2]; exact b.flags⟩
  unfold BlockState.Wf
  rw [h1, h2]
  exact b.wf

/-- With the count zero, the fields are the whole state. -/
theorem BlockRel.eq_zero {seen : ByteArray} {off : Nat} {cur prev count : UInt64} {st : BlockState} {c : BlockCategory}
    (b : BlockRel seen off cur prev count st c) (hz : count.toNat = 0) :
    st = ⟨⟨prev.toNat, cur.toNat⟩, 0, st.seen⟩ := by
  obtain ⟨⟨pr, cu⟩, co, se⟩ := st
  have h1 : cu = cur.toNat := b.cur
  have h2 : pr = prev.toNat := b.prev
  have h3 : co = count.toNat := b.count
  subst h1 h2
  rw [h3, hz]

/-- A count not zero needs no block switch. -/
theorem nextElement_count {c : BlockCategory} {st : BlockState} (bs : List Bool) (h : st.count ≠ 0) :
    nextElement c st bs = some ({ st with count := st.count - 1 }, bs) := by
  simp [nextElement, h]

/-- With one block type, a block count reaching zero is invalid. -/
theorem nextElement_single {c : BlockCategory} {st : BlockState} (bs : List Bool) (h : st.count = 0) (hn : c.n < 2) :
    nextElement c st bs = none := by
  simp [nextElement, h, hn]

/-- A block switch in the terms of a block state's fields. -/
theorem blockSwitch_rel {arena : ByteArray} {h32 : arena.size < 2 ^ 32} {tBase cBase : USize}
    {hT : TableFits arena tBase.toNat} {hCt : TableFits arena cBase.toNat} {seen : ByteArray} {off : Nat}
    {cur prev count word bcount : UInt64} {st : BlockState} {c : BlockCategory} {n : UInt64} (hnn : n.toNat = c.n)
    (cat : CatRel arena tBase cBase c) (hcw : c.Wf) (b : BlockRel seen off cur prev count st c) (hz : count.toNat = 0)
    (hw : (BitBuffer.mk word bcount).Wf) (hn2 : 2 ≤ c.n) :
    let r := blockSwitch arena h32 tBase cBase hT hCt n cur prev word bcount
    (r.status = .ok → (BitBuffer.mk r.word r.count).Wf ∧ r.cur.toNat < c.n ∧
      1 ≤ r.blockCount.toNat ∧ r.blockCount.toNat ≤ 16793840 ∧ ∀ f,
      nextElement c st ((BitBuffer.mk word bcount).held ++ f) =
        some (⟨⟨cur.toNat, r.cur.toNat⟩, r.blockCount.toNat - 1, r.cur.toNat :: st.seen⟩,
          (BitBuffer.mk r.word r.count).held ++ f)) ∧
    (r.status = .short → r.word = word ∧ r.count = bcount ∧ bcount.toNat < 54 ∧
      nextElement c st (BitBuffer.mk word bcount).held = none) ∧
    (r.status = .bad → ∀ f, nextElement c st ((BitBuffer.mk word bcount).held ++ f) = none) := by
  have hst := b.eq_zero hz
  have h256 : c.n < 2 ^ 16 := by
    have := hcw.2.1
    have : (256 : Nat) < 2 ^ 16 := by decide
    omega
  have hsp := blockSwitch_spec (arena := arena) (h32 := h32) (hT := hT) (hC := hCt) (cur := cur) (prev := prev)
    (word := word) (count := bcount) hnn (cat.type hn2).1 (cat.count hn2).1 (cat.type hn2).2.1 (cat.count hn2).2.1 hw hn2 h256
    (cat.type hn2).2.2 (cat.count hn2).2.2 (by rw [← b.cur]; exact b.wf.2.1) (by rw [← b.prev]; exact b.wf.1 hn2) st.seen
  rw [← hst] at hsp
  exact hsp

/-! ### The start of a command -/

/-- The start of a command: finish at MLEN, otherwise the insert-and-copy element's block switch. -/
def stepCommand (H : Hdr) (st : Cmd) (pos : USize) : Cmd :=
  if st.remaining = 0 then markStep st pos .done
  else if st.iCount = 0 then
    if hn : 2 ≤ H.nI then
      let hn' := UInt64.le_iff_toNat_le.mp hn
      let r := blockSwitch H.arena H.lit.arena32 H.baseTI H.baseCI (H.swI hn').1 (H.swI hn').2 H.nI st.iCur st.iPrev
        st.word st.count
      match r.status with
      | .ok =>
        let seen := st.seen
        let st0 := clearSeen st
        { st0 with
          word := r.word, count := r.count, iCur := r.cur, iPrev := st0.iCur, iCount := r.blockCount - 1
          seen := markSeen seen (USize.ofNat 256 + r.cur.toUSize), tag := .insertCopy, pos := pos, status := .next }
      | .short => markStep st pos .needsInput
      | .bad => markStep st pos .bad
    else markStep st pos .bad
  else { st with iCount := st.iCount - 1, tag := .insertCopy, pos := pos, status := .next }

/-- The start of a command, in the spec's terms. -/
theorem rest_command_of {α : Type} {w : Nat} {m : MetaBlockHeader} {K : CommandState → List Bool → Option α}
    (hK : ∀ s bs, s.remaining ≠ 0 → K s bs = readCommand w m s bs >>= fun (s1, b) => K s1 b) {s : CommandState}
    (bs : List Bool) (h0 : s.remaining ≠ 0) :
    rest w m K (.command s) bs =
      nextElement m.insertCopy s.insertCopy bs >>= fun (ic, b) => rest w m K (.insertCopy s ic) b := by
  rw [rest_command, hK s bs h0, readCommand_rest]

/-- The start of a command does its job. -/
theorem stepCommand_ok {α : Type} {w k : Nat} {H : Hdr} {m : MetaBlockHeader} {K : CommandState → List Bool → Option α}
    {a : ByteArray} {stop : USize} {s : CommandState} {st : Cmd} {pos : USize}
    (hK : ∀ s bs, s.remaining ≠ 0 → K s bs = readCommand w m s bs >>= fun (s1, b) => K s1 b) (hH : HdrRel H m)
    (hrel : Rel w k m st (.command s)) (hp : pos.toNat ≤ stop.toNat) (hfull : 56 < st.count.toNat ∨ pos = stop) :
    StepOk w k m K a stop (.command s) st pos (stepCommand H st pos) := by
  have hrel0 := hrel
  obtain ⟨hC, htag, hprod⟩ := hrel
  have hrem := hC.rem
  unfold stepCommand
  split
  · rename_i h0
    have h0N := u64_zero h0
    exact ⟨fun h => StepStatus.noConfusion h, fun h => StepStatus.noConfusion h, fun h => StepStatus.noConfusion h,
      fun _ => ⟨s, hrel0.mark _ _, Nat.le_refl _, hp, fun _ => rfl, by omega⟩, fun h => StepStatus.noConfusion h⟩
  · rename_i h0
    have h0N := u64_ne h0
    have h0' : s.remaining ≠ 0 := by omega
    split
    rotate_left
    · rename_i hcnt
      have hcntN := u64_ne hcnt
      have hcs : s.insertCopy.count ≠ 0 := by
        rw [hC.iRel.count]
        exact hcntN
      refine StepOk.ofNext (p' := .insertCopy s { s.insertCopy with count := s.insertCopy.count - 1 }) rfl
        ⟨{ hC with iRel := hC.iRel.decr hcntN }, rfl, hprod⟩ (Nat.le_refl _) hp fun F => ?_
      rw [stateBits_eq, rest_command_of hK _ h0', nextElement_count _ hcs]
      rfl
    · rename_i hcnt
      have hcntN : st.iCount.toNat = 0 := u64_zero hcnt
      have hcz : s.insertCopy.count = 0 := by
        rw [hC.iRel.count]
        exact hcntN
      split
      · rename_i hn
        have hn' : 2 ≤ H.nI.toNat := UInt64.le_iff_toNat_le.mp hn
        have hn2 : 2 ≤ m.insertCopy.n := by
          rw [← hH.nI]
          exact hn'
        have hsp := blockSwitch_rel (h32 := H.lit.arena32) (hT := (H.swI hn').1) (hCt := (H.swI hn').2) hH.nI hH.catI
          hH.ok.insertCopy hC.iRel hcntN hC.wf hn2
        dsimp only at hsp ⊢
        generalize blockSwitch _ _ _ _ _ _ _ _ _ _ _ = r at hsp ⊢
        obtain ⟨hok, hshort, hbad⟩ := hsp
        cases hs : r.status with
        | ok =>
          obtain ⟨hw, hlt, hc1, hc2, hnext⟩ := hok hs
          have h256 := hH.ok.insertCopy.2.1
          have hsize := hC.seenSize
          have hi := seen_index (off := 256) (t := r.cur) (by omega) (by omega)
          refine StepOk.ofNext (p' := .insertCopy s ⟨⟨st.iCur.toNat, r.cur.toNat⟩, r.blockCount.toNat - 1,
            r.cur.toNat :: s.insertCopy.seen⟩) rfl ⟨?_, rfl, hprod⟩ (Nat.le_refl _) hp fun F => ?_
          · exact { hC with
              wf := hw
              iRel := hC.iRel.switched (by omega) hi hlt (u64_sub_one hc1).symm
              lRel := hC.lRel.marked (by rw [hi]; omega)
              dRel := hC.dRel.marked (by rw [hi]; omega)
              seenSize := by
                show (markSeen st.seen _).size = _
                rw [size_markSeen]
                exact hsize }
          · rw [stateBits_eq, rest_command_of hK _ h0', hnext]
            rfl
        | short =>
          obtain ⟨_, _, hc54, hnone⟩ := hshort hs
          refine StepOk.ofShort hrel0 (hfull.resolve_left (by omega)) ?_
          rw [rest_command_of hK _ h0', hnone]
          rfl
        | bad =>
          refine StepOk.ofBad rfl fun F => ?_
          rw [stateBits_eq, rest_command_of hK _ h0', hbad hs]
          rfl
      · rename_i hn
        have hn' : m.insertCopy.n < 2 := by
          rw [← hH.nI]
          exact Nat.lt_of_not_le fun e => hn (UInt64.le_iff_toNat_le.mpr e)
        refine StepOk.ofBad rfl fun F => ?_
        rw [rest_command_of hK _ h0', nextElement_single _ hcz hn']
        rfl

/-- The start of a command in terms of the insert-and-copy element's block switch, whatever follows the command. -/
theorem stepCommand_cases {w k : Nat} {H : Hdr} {m : MetaBlockHeader} {a : ByteArray} {stop : USize} {s : CommandState} {st : Cmd} {pos : USize}
    (hH : HdrRel H m) (hrel : Rel w k m st (.command s)) :
    ((stepCommand H st pos).status = .next → ∃ ic, Rel w k m (stepCommand H st pos) (.insertCopy s ic) ∧ (stepCommand H st pos).pos = pos ∧ s.remaining ≠ 0 ∧
      ∀ F, nextElement m.insertCopy s.insertCopy (stateBits st a pos stop F) =
        some (ic, stateBits (stepCommand H st pos) a (stepCommand H st pos).pos stop F)) ∧
    ((stepCommand H st pos).status = .needsInput → stepCommand H st pos = markStep st pos .needsInput) ∧
    ((stepCommand H st pos).status = .done → stepCommand H st pos = markStep st pos .done ∧ s.remaining = 0) ∧
    (stepCommand H st pos).status ≠ .needsOutput := by
  obtain ⟨hC, htag, hprod⟩ := hrel
  have hrem := hC.rem
  unfold stepCommand
  split
  · rename_i h0
    have h0N := u64_zero h0
    exact ⟨fun h => StepStatus.noConfusion h, fun h => StepStatus.noConfusion h, fun _ => ⟨rfl, by omega⟩, fun h => StepStatus.noConfusion h⟩
  · rename_i h0
    have h0N := u64_ne h0
    have h0' : s.remaining ≠ 0 := by omega
    split
    rotate_left
    · rename_i hcnt
      have hcntN := u64_ne hcnt
      have hcs : s.insertCopy.count ≠ 0 := by
        rw [hC.iRel.count]
        exact hcntN
      refine ⟨fun _ => ⟨{ s.insertCopy with count := s.insertCopy.count - 1 }, ⟨{ hC with iRel := hC.iRel.decr hcntN }, rfl, hprod⟩, rfl, h0', fun F => ?_⟩,
        fun h => StepStatus.noConfusion h, fun h => StepStatus.noConfusion h, fun h => StepStatus.noConfusion h⟩
      rw [nextElement_count _ hcs]
      rfl
    · rename_i hcnt
      have hcntN : st.iCount.toNat = 0 := u64_zero hcnt
      split
      · rename_i hn
        have hn' : 2 ≤ H.nI.toNat := UInt64.le_iff_toNat_le.mp hn
        have hn2 : 2 ≤ m.insertCopy.n := by
          rw [← hH.nI]
          exact hn'
        have hsp := blockSwitch_rel (h32 := H.lit.arena32) (hT := (H.swI hn').1) (hCt := (H.swI hn').2) hH.nI hH.catI
          hH.ok.insertCopy hC.iRel hcntN hC.wf hn2
        dsimp only at hsp ⊢
        generalize blockSwitch _ _ _ _ _ _ _ _ _ _ _ = r at hsp ⊢
        obtain ⟨hok, _, _⟩ := hsp
        cases hs : r.status with
        | ok =>
          obtain ⟨hw, hlt, hc1, hc2, hnext⟩ := hok hs
          have h256 := hH.ok.insertCopy.2.1
          have hsize := hC.seenSize
          have hi := seen_index (off := 256) (t := r.cur) (by omega) (by omega)
          refine ⟨fun _ => ⟨⟨⟨st.iCur.toNat, r.cur.toNat⟩, r.blockCount.toNat - 1, r.cur.toNat :: s.insertCopy.seen⟩, ⟨?_, rfl, hprod⟩, rfl, h0', fun F => ?_⟩,
            fun h => StepStatus.noConfusion h, fun h => StepStatus.noConfusion h, fun h => StepStatus.noConfusion h⟩
          · exact { hC with
              wf := hw
              iRel := hC.iRel.switched (by omega) hi hlt (u64_sub_one hc1).symm
              lRel := hC.lRel.marked (by rw [hi]; omega)
              dRel := hC.dRel.marked (by rw [hi]; omega)
              seenSize := by
                show (markSeen st.seen _).size = _
                rw [size_markSeen]
                exact hsize }
          · rw [stateBits_eq, hnext]
            rfl
        | short => exact ⟨fun h => StepStatus.noConfusion h, fun _ => rfl, fun h => StepStatus.noConfusion h, fun h => StepStatus.noConfusion h⟩
        | bad => exact ⟨fun h => StepStatus.noConfusion h, fun h => StepStatus.noConfusion h, fun h => StepStatus.noConfusion h, fun h => StepStatus.noConfusion h⟩
      · exact ⟨fun h => StepStatus.noConfusion h, fun h => StepStatus.noConfusion h, fun h => StepStatus.noConfusion h, fun h => StepStatus.noConfusion h⟩

/-! ### The insert-and-copy element -/

/-- A table's start, read from a table of starts. -/
@[inline] def tableBase (t : ByteArray) (i : UInt64) (h : 4 * i.toNat + 4 ≤ t.size) (h32 : t.size < 2 ^ 32) : USize :=
  (slotWord t i.toUSize (by rw [word_toUSize (by omega)]; exact h) h32).toUSize

theorem tableBase_toNat {t : ByteArray} {i : UInt64} (h : 4 * i.toNat + 4 ≤ t.size) (h32 : t.size < 2 ^ 32) :
    (tableBase t i h h32).toNat = u32At t i.toNat := by
  unfold tableBase
  rw [word_toUSize (by rw [slotWord_toNat]; exact u32At_lt _ _), slotWord_toNat, word_toUSize (by omega)]

/-- The element, once its symbol is looked up. -/
@[inline] def insertStep (st : Cmd) (pos : USize) (v : UInt64) : Cmd :=
  if wordBits v ≤ st.count then
    if hc : wordSym v < 704 then
      let b1 := (BitBuffer.mk st.word st.count).drop (wordBits v)
      let row := insertRow (wordSym v) (lt704 hc)
      if rowBits row ≤ b1.count then
        let b2 := b1.drop (rowBits row)
        let cr := copyRow (wordSym v) (lt704 hc)
        { st with
          word := b2.word, count := b2.count, code := wordSym v
          ilen := rowBase row + b1.peek (rowBits row), copyBits := rowBits cr, copyBase := rowBase cr
          tag := .copyLength, pos := pos, status := .next }
      else markStep st pos .needsInput
    else markStep st pos .bad
  else markStep st pos .needsInput

/-- The element's symbol and insert extra bits. -/
def stepInsertCopy (H : Hdr) (st : Cmd) (pos : USize) : Cmd :=
  if ht : st.iCur < H.nI then
    have ht' := UInt64.lt_iff_toNat_lt.mp ht
    have hb : 4 * st.iCur.toNat + 4 ≤ H.icBase.size := by
      rw [H.icSize]
      omega
    insertStep st pos (lookup H.arena (tableBase H.icBase st.iCur hb H.ic32) st.word
      (by rw [tableBase_toNat]; exact H.icFits _ ht') H.lit.arena32)
  else markStep st pos .bad

/-- The element, once its symbol is read. -/
theorem rest_insertCopy_row {α : Type} {w : Nat} {m : MetaBlockHeader} {K : CommandState → List Bool → Option α}
    {s : CommandState} {ic : BlockState} {t c : Nat} {code : PrefixCode} {bs r : List Bool} (hcur : ic.types.cur = t)
    (hcode : m.insertCopyCodes[t]? = some code) (hd : decodeSymbol code bs = some (c, r)) (hc : c < 704) :
    rest w m K (.insertCopy s ic) bs =
      readInt (cmdRow c).1 r >>= fun (e, b) =>
      rest w m K (.copyLength s ic c ((cmdRow c).2.1 + e) (cmdRow c).2.2.1 (cmdRow c).2.2.2) b := by
  obtain ⟨icode, ccode, ih, ch, h1, h2, h3⟩ := cmdRow_spec hc
  rw [rest_insertCopy, hcur, hcode]
  simp only [bind, Option.bind, hd, h1, h2, h3]

/-- The element's symbol can't be read from these bits. -/
theorem rest_insertCopy_none {α : Type} {w : Nat} {m : MetaBlockHeader} {K : CommandState → List Bool → Option α}
    {s : CommandState} {ic : BlockState} {t : Nat} {code : PrefixCode} {bs : List Bool} (hcur : ic.types.cur = t)
    (hcode : m.insertCopyCodes[t]? = some code) (hd : decodeSymbol code bs = none) :
    rest w m K (.insertCopy s ic) bs = none := by
  rw [rest_insertCopy, hcur, hcode]
  simp only [bind, Option.bind, hd]

/-- The element's step, when its reads finish. -/
private theorem insertCopy_next {α : Type} {w k : Nat} {m : MetaBlockHeader} {K : CommandState → List Bool → Option α}
    {a : ByteArray} {stop : USize} {s : CommandState} {ic : BlockState} {st : Cmd} {pos : USize} {b2 : BitBuffer}
    {code ilen copyBits copyBase : UInt64} {sym ilenN copyBitsN copyBaseN : Nat}
    (hC : Core w k m st s.output s.remaining s.distances ic s.literal s.distance) (hprod : s.produced = s.output.length)
    (hw : b2.Wf) (hp : pos.toNat ≤ stop.toNat) (h1 : code.toNat = sym) (h2 : ilen.toNat = ilenN)
    (h3 : copyBits.toNat = copyBitsN) (h4 : copyBase.toNat = copyBaseN) (h5 : copyBitsN ≤ 24) (h6 : copyBaseN ≤ 2118)
    (hrest : ∀ F, rest w m K (.insertCopy s ic) (stateBits st a pos stop F) =
      rest w m K (.copyLength s ic sym ilenN copyBitsN copyBaseN) (b2.held ++ (chunkBits a pos.toNat stop.toNat ++ F))) :
    StepOk w k m K a stop (.insertCopy s ic) st pos
      { st with
        word := b2.word, count := b2.count, code := code, ilen := ilen, copyBits := copyBits, copyBase := copyBase
        tag := .copyLength, pos := pos, status := .next } :=
  StepOk.ofNext (p' := .copyLength s ic sym ilenN copyBitsN copyBaseN) rfl
    ⟨{ hC with wf := hw }, rfl, hprod, h1, h2, h3, h4, h5, h6⟩ (Nat.le_refl _) hp hrest

/-- The element's step does its job. -/
theorem stepInsertCopy_ok {α : Type} {w k : Nat} {H : Hdr} {m : MetaBlockHeader} {K : CommandState → List Bool → Option α}
    {a : ByteArray} {stop : USize} {s : CommandState} {ic : BlockState} {st : Cmd} {pos : USize} (hH : HdrRel H m)
    (hrel : Rel w k m st (.insertCopy s ic)) (hp : pos.toNat ≤ stop.toNat) (hfull : 56 < st.count.toNat ∨ pos = stop) :
    StepOk w k m K a stop (.insertCopy s ic) st pos (stepInsertCopy H st pos) := by
  have hrel0 := hrel
  obtain ⟨hC, htag, hprod⟩ := hrel
  have ht : st.iCur.toNat < H.nI.toNat := by
    rw [hH.nI, ← hC.iRel.cur]
    exact hC.iRel.wf.2.1
  obtain ⟨code, hcode, hok, hcomp, hsym⟩ := hH.ic _ ht
  have hcur : ic.types.cur = st.iCur.toNat := hC.iRel.cur
  unfold stepInsertCopy
  rw [dite_eq_left (UInt64.lt_iff_toNat_lt.mpr ht)]
  dsimp only
  have hb : 4 * st.iCur.toNat + 4 ≤ H.icBase.size := by
    rw [H.icSize]
    omega
  rw [← tableBase_toNat hb H.ic32] at hok
  obtain ⟨h15, hread, hshort⟩ := lookup_read (b := ⟨st.word, st.count⟩) hok (by rw [tableBase_toNat]; exact H.icFits _ ht)
    H.lit.arena32 hcomp
  dsimp only at h15 hread hshort
  generalize lookup H.arena _ st.word _ _ = v at h15 hread hshort ⊢
  have hcount := hC.wf.count_le
  have hcount' : st.count.toNat ≤ 64 := hcount
  unfold insertStep
  split
  · rename_i hl
    have hl' := UInt64.le_iff_toNat_le.mp hl
    have hcN : wordValue v < 704 := decodeSymbol_lt hsym (hread hl [])
    have hcS : (wordSym v).toNat < 704 := hcN
    have hcU : wordSym v < 704 :=
      UInt64.lt_iff_toNat_lt.mpr (by rw [show (704 : UInt64).toNat = 704 from rfl]; exact hcS)
    rw [dite_eq_left hcU]
    dsimp only
    have hw1 := BitBuffer.drop_wf hC.wf (wordBits_lt v) hl'
    have hc1 : ((BitBuffer.mk st.word st.count).drop (wordBits v)).count.toNat = st.count.toNat - (wordBits v).toNat :=
      drop_count hl'
    obtain ⟨hib, hibase⟩ : (rowBits (insertRow (wordSym v) (lt704 hcU))).toNat = (cmdRow (wordValue v)).1 ∧
        (rowBase (insertRow (wordSym v) (lt704 hcU))).toNat = (cmdRow (wordValue v)).2.1 := insertRow_fields (lt704 hcU)
    obtain ⟨hcb, hcbase⟩ : (rowBits (copyRow (wordSym v) (lt704 hcU))).toNat = (cmdRow (wordValue v)).2.2.1 ∧
        (rowBase (copyRow (wordSym v) (lt704 hcU))).toNat = (cmdRow (wordValue v)).2.2.2 := copyRow_fields (lt704 hcU)
    obtain ⟨s1, s2, s3, s4⟩ := cmdRow_small hcN
    generalize hb1 : (BitBuffer.mk st.word st.count).drop (wordBits v) = b1 at hw1 hc1 ⊢
    -- The rows and the symbol stay abstract here: the kernel can't reduce the table they read.
    generalize insertRow (wordSym v) (lt704 hcU) = row at hib hibase ⊢
    generalize copyRow (wordSym v) (lt704 hcU) = cr at hcb hcbase ⊢
    have hE : (wordSym v).toNat = wordValue v := rfl
    generalize wordValue v = sym at hcN hE hread hib hibase hcb hcbase s1 s2 s3 s4 ⊢
    generalize hrow : cmdRow sym = cells at hib hibase hcb hcbase s1 s2 s3 s4 ⊢
    split
    · rename_i hle
      have hle' := UInt64.le_iff_toNat_le.mp hle
      have hw2 := BitBuffer.drop_wf hw1 (k := rowBits row) (by omega) hle'
      have hpeek : (b1.peek (rowBits row)).toNat < 2 ^ cells.1 := by
        rw [BitBuffer.peek_toNat _ (by omega), hib]
        exact Nat.mod_lt _ (Nat.two_pow_pos _)
      have hpow : 2 ^ cells.1 ≤ 2 ^ 24 := Nat.pow_le_pow_right (by decide) s1
      have h24 : (2 : Nat) ^ 24 = 16777216 := by decide
      have hint := fun f : List Bool => read_int (b := b1) (k := rowBits row) f (by omega) hle
      rw [hib] at hint
      -- Abstract too, or the kernel, comparing the new state with the old field by field, unfolds the shift.
      generalize b1.drop (rowBits row) = b2 at hw2 hint ⊢
      refine insertCopy_next hC hprod hw2 hp hE (by rw [u64_add (by omega), hibase]) hcb hcbase s3 s4 fun F => ?_
      rw [stateBits_eq, rest_insertCopy_row hcur hcode (hread hl _) hcN, hb1, hrow, hint]
      rfl
    · rename_i hle
      have hnot : b1.count.toNat < cells.1 := by
        rw [← hib]
        exact Nat.lt_of_not_le fun h => hle (UInt64.le_iff_toNat_le.mpr h)
      refine StepOk.ofShort hrel0 (hfull.resolve_left (by omega)) ?_
      have hd := hread hl []
      rw [List.append_nil, List.append_nil] at hd
      rw [rest_insertCopy_row hcur hcode hd hcN, hb1, hrow, readInt_short hnot]
      rfl
  · rename_i hl
    have hnot : st.count.toNat < (wordBits v).toNat := Nat.lt_of_not_le fun h => hl (UInt64.le_iff_toNat_le.mpr h)
    exact StepOk.ofShort hrel0 (hfull.resolve_left (by omega)) (rest_insertCopy_none hcur hcode (hshort hl))

/-! ### The copy length -/

/-- The copy extra bits, which begin the literals. -/
def stepCopyLength (st : Cmd) (pos : USize) : Cmd :=
  if st.copyBits ≤ st.count then
    if st.remaining < st.ilen then markStep st pos .bad
    else
      let b := (BitBuffer.mk st.word st.count)
      let b1 := b.drop st.copyBits
      { st with
        word := b1.word, count := b1.count, clen := st.copyBase + b.peek st.copyBits, left := st.ilen
        tag := .literals, pos := pos, status := .next }
  else markStep st pos .needsInput

/-- The copy length's step does its job. -/
theorem stepCopyLength_ok {α : Type} {w k : Nat} {m : MetaBlockHeader} {K : CommandState → List Bool → Option α}
    {a : ByteArray} {stop : USize} {s : CommandState} {ic : BlockState} {c ilen copyBits copyBase : Nat} {st : Cmd}
    {pos : USize} (hrel : Rel w k m st (.copyLength s ic c ilen copyBits copyBase)) (hp : pos.toNat ≤ stop.toNat)
    (hfull : 56 < st.count.toNat ∨ pos = stop) :
    StepOk w k m K a stop (.copyLength s ic c ilen copyBits copyBase) st pos (stepCopyLength st pos) := by
  have hrel0 := hrel
  obtain ⟨hC, htag, hprod, hcode, hilen, hbits, hbase, hb24, hb2118⟩ := hrel
  have hrem := hC.rem
  unfold stepCopyLength
  have hk64 : st.copyBits.toNat < 64 := by omega
  split
  · rename_i hle
    have hle' := UInt64.le_iff_toNat_le.mp hle
    have hint := fun f : List Bool => read_int (b := BitBuffer.mk st.word st.count) (k := st.copyBits) f hk64 hle
    rw [show st.copyBits.toNat = copyBits from hbits] at hint
    split
    · rename_i hlt
      have hlt' := UInt64.lt_iff_toNat_lt.mp hlt
      refine StepOk.ofBad rfl fun F => ?_
      rw [stateBits_eq, rest_copyLength, hint]
      show (if s.remaining < ilen then none else _) = none
      rw [ite_eq_left (by omega)]
    · rename_i hlt
      have hlt' : ¬ st.remaining.toNat < st.ilen.toNat := fun e => hlt (UInt64.lt_iff_toNat_lt.mpr e)
      have hpeek : ((BitBuffer.mk st.word st.count).peek st.copyBits).toNat < 2 ^ copyBits := by
        rw [BitBuffer.peek_toNat _ hk64, show st.copyBits.toNat = copyBits from hbits]
        exact Nat.mod_lt _ (Nat.two_pow_pos _)
      have hpow : 2 ^ copyBits ≤ 2 ^ 24 := Nat.pow_le_pow_right (by decide) hb24
      have h24 : (2 : Nat) ^ 24 = 16777216 := by decide
      refine StepOk.ofNext (p' := .literals s ic c ilen (copyBase + ((BitBuffer.mk st.word st.count).peek st.copyBits).toNat)
        ilen s.literal s.output) rfl ⟨{ hC with wf := BitBuffer.drop_wf hC.wf hk64 hle', rem := ?_ }, rfl, hprod, hcode, hilen,
          ?_, hilen, Nat.le_refl _, by omega, rfl⟩ (Nat.le_refl _) hp fun F => ?_
      · show st.remaining.toNat = _
        omega
      · show (st.copyBase + (BitBuffer.mk st.word st.count).peek st.copyBits).toNat = _
        rw [u64_add (by omega), hbase]
      · rw [stateBits_eq, rest_copyLength, hint]
        show (if s.remaining < ilen then none else _) = _
        rw [ite_eq_right (by omega)]
        rfl
  · rename_i hle
    have hnot : st.count.toNat < copyBits := by
      rw [← hbits]
      exact Nat.lt_of_not_le fun h => hle (UInt64.le_iff_toNat_le.mpr h)
    refine StepOk.ofShort hrel0 (hfull.resolve_left (by omega)) ?_
    rw [rest_copyLength, readInt_short (b := BitBuffer.mk st.word st.count) hnot]
    rfl

end Brotli.Decoder
