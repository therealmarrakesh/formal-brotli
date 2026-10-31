import Brotli.Decoder.StepLiterals

/-!
# The distance's steps

After a command's literals: finish if MLEN is reached, otherwise find the distance, implied or read, and begin the copy
it selects, a backward copy or a dictionary word.
-/

namespace Brotli.Decoder

open Brotli.Spec Brotli.Properties

/-- A dictionary word's bytes. -/
def wordBytes (word : List Nat) : ByteArray :=
  (word.map Nat.toUInt8).toByteArray

private theorem wordBytes_data {word : List Nat} (h : ∀ b ∈ word, b < 256) :
    (wordBytes word).data.toList.map UInt8.toNat = word := by
  unfold wordBytes
  simp only [List.data_toByteArray, List.toList_toArray]
  exact map_toUInt8 word h

private theorem wordBytes_size (word : List Nat) : (wordBytes word).size = word.length := by
  simp [wordBytes, List.size_toByteArray]

/-- The most recent distances a state holds. -/
@[inline] def cmdDistances (st : Cmd) : Distances :=
  ⟨st.d0.toNat, st.d1.toNat, st.d2.toNat, st.d3.toNat⟩

/-- Begins the copy a distance selects. -/
def applyDistance (st : Cmd) (pos : USize) (dcode d : Nat) : Stepped :=
  if st.written.toNat < d then
    match dictionaryWord st.clen.toNat d st.written.toNat with
    | none => ⟨st, pos, .bad⟩
    | some word =>
      if st.remaining.toNat < word.length then ⟨st, pos, .bad⟩
      else
        ⟨{ st with
            remaining := st.remaining - UInt64.ofNat word.length, wordBuf := wordBytes word, wordPos := 0
            tag := .word }, pos, .next⟩
  else if st.remaining.toNat < st.clen.toNat then ⟨st, pos, .bad⟩
  else
    ⟨{ st with
        remaining := st.remaining - st.clen, left := st.clen, dist := UInt64.ofNat d, tag := .copy
        d0 := if dcode = 0 then st.d0 else UInt64.ofNat d
        d1 := if dcode = 0 then st.d1 else st.d0
        d2 := if dcode = 0 then st.d2 else st.d1
        d3 := if dcode = 0 then st.d3 else st.d2 }, pos, .next⟩

/-- What `applyDistance` does: it rejects when `copyPhase` does, and otherwise stands for the place `copyPhase` gives,
with the buffer and position unchanged. -/
theorem applyDistance_spec {w k : Nat} {m : MetaBlockHeader} {st : Cmd} {s : CommandState} {pos : USize} {clen dcode d : Nat}
    (hC : Core w k m st s.output s.remaining s.distances s.insertCopy s.literal s.distance)
    (hprod : s.produced = s.output.length) (hclen : st.clen.toNat = clen) (hd1 : 1 ≤ d) :
    (copyPhase w s clen dcode d = none ∧ (applyDistance st pos dcode d).status = .bad) ∨
      ∃ p, copyPhase w s clen dcode d = some p ∧ (applyDistance st pos dcode d).status = .next ∧
        (applyDistance st pos dcode d).pos = pos ∧ (applyDistance st pos dcode d).st.word = st.word ∧
        (applyDistance st pos dcode d).st.count = st.count ∧ Rel w k m (applyDistance st pos dcode d).st p := by
  have hmax : maxBackwardDistance w s.produced = st.written.toNat := by
    unfold maxBackwardDistance
    rw [hprod, hC.written]
  have hrem := hC.rem
  have hk := hC.k24
  have hRmax : 2 ^ k ≤ 2 ^ 24 := Nat.pow_le_pow_right (by decide) hk
  have h24 : (2 : Nat) ^ 24 = 16777216 := by decide
  have hwin := hC.win
  have hwri := hC.written
  unfold applyDistance
  subst hclen
  by_cases hdict : st.written.toNat < d
  · rw [ite_eq_left hdict, copyPhase_word (by rw [hmax]; exact hdict), hmax]
    cases hword : dictionaryWord st.clen.toNat d st.written.toNat with
    | none => exact Or.inl ⟨rfl, rfl⟩
    | some word =>
      dsimp only [Option.bind]
      have hlen := dictionaryWord_length hword
      have hb := dictionaryWord_bytes hword
      by_cases hr : st.remaining.toNat < word.length
      · have hr' : s.remaining < word.length := by omega
        rw [ite_eq_left hr, ite_eq_left hr']
        exact Or.inl ⟨rfl, rfl⟩
      · have hr' : ¬ s.remaining < word.length := by omega
        rw [ite_eq_right hr, ite_eq_right hr']
        have hu : (UInt64.ofNat word.length).toNat = word.length := u64_ofNat (by omega)
        refine Or.inr ⟨_, rfl, rfl, rfl, rfl, rfl, ⟨?_, rfl, ?_, ?_, ?_, ?_⟩⟩
        · refine { hC with rem := ?_ }
          show (st.remaining - UInt64.ofNat word.length).toNat = _
          rw [u64_sub (by rw [hu]; omega), hu]
          show _ = s.remaining - word.length
          omega
        · show s.produced + word.length = s.output.length + word.length
          omega
        · show ((wordBytes word).data.toList.drop (0 : USize).toNat).map UInt8.toNat = word
          exact wordBytes_data hb
        · show (wordBytes word).size ≤ 38
          rw [wordBytes_size]
          omega
        · exact Nat.zero_le _
  · rw [ite_eq_right hdict, copyPhase_copy (by rw [hmax]; exact hdict)]
    by_cases hr : st.remaining.toNat < st.clen.toNat
    · have hr' : s.remaining < st.clen.toNat := by omega
      rw [ite_eq_left hr, ite_eq_left hr']
      exact Or.inl ⟨rfl, rfl⟩
    · have hr' : ¬ s.remaining < st.clen.toNat := by omega
      rw [ite_eq_right hr, ite_eq_right hr']
      have hdsmall : d < 2 ^ 32 := by omega
      have hu : (UInt64.ofNat d).toNat = d := u64_ofNat hdsmall
      have hlt := hC.dsLt
      refine Or.inr ⟨_, rfl, rfl, rfl, rfl, rfl, ⟨?_, rfl, ?_, hu, rfl, hd1, by omega, by show d ≤ s.output.length; omega⟩⟩
      · refine { hC with rem := ?_, d0 := ?_, d1 := ?_, d2 := ?_, d3 := ?_, dsLt := ?_ }
        · show (st.remaining - st.clen).toNat = _
          rw [u64_sub (by omega)]
          show _ = s.remaining - st.clen.toNat
          omega
        · show (pushDistance s.distances dcode d false).last = (if dcode = 0 then st.d0 else UInt64.ofNat d).toNat
          by_cases h0 : dcode = 0
          · simp only [pushDistance, h0, true_or, ↓reduceIte]
            exact hC.d0
          · simp only [pushDistance, h0, false_or, Bool.false_eq_true, ↓reduceIte]
            exact hu.symm
        · show (pushDistance s.distances dcode d false).secondToLast = (if dcode = 0 then st.d1 else st.d0).toNat
          by_cases h0 : dcode = 0
          · simp only [pushDistance, h0, true_or, ↓reduceIte]
            exact hC.d1
          · simp only [pushDistance, h0, false_or, Bool.false_eq_true, ↓reduceIte]
            exact hC.d0
        · show (pushDistance s.distances dcode d false).thirdToLast = (if dcode = 0 then st.d2 else st.d1).toNat
          by_cases h0 : dcode = 0
          · simp only [pushDistance, h0, true_or, ↓reduceIte]
            exact hC.d2
          · simp only [pushDistance, h0, false_or, Bool.false_eq_true, ↓reduceIte]
            exact hC.d1
        · show (pushDistance s.distances dcode d false).fourthToLast = (if dcode = 0 then st.d3 else st.d2).toNat
          by_cases h0 : dcode = 0
          · simp only [pushDistance, h0, true_or, ↓reduceIte]
            exact hC.d3
          · simp only [pushDistance, h0, false_or, Bool.false_eq_true, ↓reduceIte]
            exact hC.d2
        · show (pushDistance s.distances dcode d false).last < 2 ^ 32 ∧ (pushDistance s.distances dcode d false).secondToLast < 2 ^ 32 ∧
            (pushDistance s.distances dcode d false).thirdToLast < 2 ^ 32 ∧ (pushDistance s.distances dcode d false).fourthToLast < 2 ^ 32
          by_cases h0 : dcode = 0
          · simp only [pushDistance, h0, true_or, ↓reduceIte]
            exact hlt
          · simp only [pushDistance, h0, false_or, Bool.false_eq_true, ↓reduceIte]
            exact ⟨hdsmall, hlt.1, hlt.2.1, hlt.2.2.1⟩
      · show s.produced + st.clen.toNat = s.output.length + st.clen.toNat
        omega

/-- A distance's result, in the terms of a step. -/
private theorem step_of_apply {α : Type} {w k : Nat} {m : MetaBlockHeader} {K : CommandState → List Bool → Option α}
    {a : ByteArray} {stop : USize} {p : Phase} {st st1 : Cmd} {s : CommandState} {pos : USize} {clen dcode d : Nat}
    (hC : Core w k m st1 s.output s.remaining s.distances s.insertCopy s.literal s.distance)
    (hprod : s.produced = s.output.length) (hclen : st1.clen.toNat = clen) (hd1 : 1 ≤ d) (hp : pos.toNat ≤ stop.toNat)
    (hrest : ∀ F, rest w m K p (stateBits st a pos stop F) =
      copyPhase w s clen dcode d >>= fun q => rest w m K q (stateBits st1 a pos stop F)) :
    StepOk w k m K a stop p st pos (applyDistance st1 pos dcode d) := by
  rcases applyDistance_spec (pos := pos) (dcode := dcode) hC hprod hclen hd1 with ⟨hn, hs⟩ | ⟨q, hq, hs, hpos, hw, hc, hR⟩
  · refine StepOk.ofBad hs fun F => ?_
    rw [hrest, hn]
    rfl
  · refine StepOk.ofNext hs hR (by rw [hpos]; exact Nat.le_refl _) (by rw [hpos]; exact hp) fun F => ?_
    rw [hrest, hq]
    show rest w m K q (stateBits st1 a pos stop F) = rest w m K q (stateBits _ a _ stop F)
    rw [hpos, stateBits_eq, stateBits_eq, hw, hc]

/-! ### Where the distance comes from -/

/-- The start of a command's distance. -/
def stepDistance (H : Hdr) (st : Cmd) (pos : USize) : Stepped :=
  if st.remaining.toNat = 0 then ⟨{ st with tag := .command }, pos, .next⟩
  else if st.code.toNat < 128 then
    match distanceOf H.npostfix.toNat H.ndirect.toNat (cmdDistances st) 0 0 with
    | none => ⟨st, pos, .bad⟩
    | some d => applyDistance st pos 0 d
  else if st.dCount.toNat ≠ 0 then ⟨{ st with dCount := st.dCount - 1, tag := .distanceSymbol }, pos, .next⟩
  else if hn : 2 ≤ H.nD.toNat then
    let r := blockSwitch H.arena H.lit.arena32 H.baseTD H.baseCD (H.swD hn).1 (H.swD hn).2 H.nD.toNat st.dCur st.dPrev
      st.word st.count
    match r.status with
    | .ok =>
      let seen := st.seen
      let st0 := clearSeen st
      ⟨{ st0 with
          word := r.word, count := r.count, dCur := r.cur, dPrev := st0.dCur, dCount := r.blockCount - 1
          seen := markSeen seen 512 r.cur.toNat, tag := .distanceSymbol }, pos, .next⟩
    | .short => ⟨st, pos, .needsInput⟩
    | .bad => ⟨st, pos, .bad⟩
  else ⟨st, pos, .bad⟩

/-- The start of a command's distance does its job. -/
theorem stepDistance_ok {α : Type} {w k : Nat} {H : Hdr} {m : MetaBlockHeader} {K : CommandState → List Bool → Option α}
    {a : ByteArray} {stop : USize} {s : CommandState} {c clen : Nat} {st : Cmd} {pos : USize} (hH : HdrRel H m)
    (hrel : Rel w k m st (.distance s c clen)) (hp : pos.toNat ≤ stop.toNat) (hfull : 56 < st.count.toNat ∨ pos = stop) :
    StepOk w k m K a stop (.distance s c clen) st pos (stepDistance H st pos) := by
  have hrel0 := hrel
  obtain ⟨hC, htag, hprod, hcode, hclen⟩ := hrel
  have hrem := hC.rem
  have hds : cmdDistances st = s.distances := by
    have h0 := hC.d0
    have h1 := hC.d1
    have h2 := hC.d2
    have h3 := hC.d3
    unfold cmdDistances
    rw [← h0, ← h1, ← h2, ← h3]
  have hnp : H.npostfix.toNat = m.npostfix := hH.npostfix
  have hnd : H.ndirect.toNat = m.ndirect := hH.ndirect
  unfold stepDistance
  split
  · rename_i h0
    exact StepOk.ofNext (p' := .command s) rfl ⟨{ hC with }, rfl, hprod⟩ (Nat.le_refl _) hp
      fun F => rest_distance_end _ (by omega)
  · rename_i h0
    have h0' : s.remaining ≠ 0 := by omega
    split
    · rename_i himp
      have hc : implicitZeroDistance c = true := by
        unfold implicitZeroDistance
        rw [← hcode]
        exact decide_eq_true himp
      rw [hds, hnp, hnd]
      cases hd : distanceOf m.npostfix m.ndirect s.distances 0 0 with
      | none =>
        refine StepOk.ofBad rfl fun F => ?_
        rw [rest_distance_implicit _ h0' hc, hd]
        rfl
      | some d =>
        refine step_of_apply (s := s) (clen := clen) hC hprod hclen (distanceOf_pos hd) hp fun F => ?_
        rw [rest_distance_implicit _ h0' hc, hd]
        rfl
    · rename_i himp
      have hc : implicitZeroDistance c = false := by
        unfold implicitZeroDistance
        rw [← hcode]
        exact decide_eq_false himp
      split
      · rename_i hcnt
        have hcs : s.distance.count ≠ 0 := by
          rw [hC.dRel.count]
          exact hcnt
        refine StepOk.ofNext (p' := .distanceSymbol s clen { s.distance with count := s.distance.count - 1 }) rfl
          ⟨{ hC with dRel := hC.dRel.decr hcnt }, rfl, hprod, hclen⟩ (Nat.le_refl _) hp fun F => ?_
        rw [stateBits_eq, rest_distance_switch _ h0' hc, nextElement_count _ hcs]
        rfl
      · rename_i hcnt
        have hcz : s.distance.count = 0 := by
          rw [hC.dRel.count]
          omega
        split
        · rename_i hn
          have hn2 : 2 ≤ m.distance.n := by
            rw [← hH.nD]
            exact hn
          have hsp := blockSwitch_rel (h32 := H.lit.arena32) (hT := (H.swD hn).1) (hCt := (H.swD hn).2) hH.nD hH.catD
            hH.ok.distance hC.dRel (by omega) hC.wf hn2
          dsimp only at hsp ⊢
          generalize blockSwitch _ _ _ _ _ _ _ _ _ _ _ = r at hsp ⊢
          obtain ⟨hok, hshort, hbad⟩ := hsp
          cases hs : r.status with
          | ok =>
            obtain ⟨hw, hlt, hc1, hc2, hnext⟩ := hok hs
            have h256 := hH.ok.distance.2.1
            have hsize := hC.seenSize
            refine StepOk.ofNext (p' := .distanceSymbol s clen ⟨⟨st.dCur.toNat, r.cur.toNat⟩, r.blockCount.toNat - 1,
              r.cur.toNat :: s.distance.seen⟩) rfl ⟨?_, rfl, hprod, hclen⟩ (Nat.le_refl _) hp fun F => ?_
            · exact { hC with
                wf := hw
                dRel := hC.dRel.switched (by omega) hlt (u64_sub_one hc1).symm
                lRel := hC.lRel.marked (by omega)
                iRel := hC.iRel.marked (by omega)
                seenSize := by rw [show _ = (markSeen st.seen 512 r.cur.toNat).size from rfl, size_markSeen]; exact hsize }
            · rw [stateBits_eq, rest_distance_switch _ h0' hc, hnext]
              rfl
          | short =>
            obtain ⟨_, _, hc54, hnone⟩ := hshort hs
            refine StepOk.ofShort hrel0 (hfull.resolve_left (by omega)) ?_
            rw [rest_distance_switch _ h0' hc, hnone]
            rfl
          | bad =>
            refine StepOk.ofBad rfl fun F => ?_
            rw [stateBits_eq, rest_distance_switch _ h0' hc, hbad hs]
            rfl
        · rename_i hn
          have hn' : m.distance.n < 2 := by
            rw [← hH.nD]
            omega
          refine StepOk.ofBad rfl fun F => ?_
          rw [rest_distance_switch _ h0' hc, nextElement_single _ hcz hn']
          rfl

/-! ### The distance's symbol -/

/-- The distance's symbol and extra bits, through a tree. -/
def distanceThrough (H : Hdr) (st : Cmd) (pos : USize) (tree : UInt8) (htree : tree.toNat < H.treesD.toNat) : Stepped :=
  have hb : 4 * tree.toUInt64.toNat + 4 ≤ H.dBase.size := by
    rw [H.dSize, UInt8.toNat_toUInt64]
    omega
  have hfit : TableFits H.arena (tableBase H.dBase tree.toUInt64 hb H.d32).toNat := by
    rw [tableBase_toNat, UInt8.toNat_toUInt64]
    exact H.dFits _ htree
  let v := lookup H.arena (tableBase H.dBase tree.toUInt64 hb H.d32) st.word hfit H.lit.arena32
  if wordBits v ≤ st.count then
    let nbits := distanceExtraBits H.npostfix.toNat H.ndirect.toNat (wordValue v)
    let b1 := (BitBuffer.mk st.word st.count).drop (wordBits v)
    if nbits ≤ 24 then
      let kb := UInt64.ofNat nbits
      if kb ≤ b1.count then
        let b2 := b1.drop kb
        match distanceOf H.npostfix.toNat H.ndirect.toNat (cmdDistances st) (wordValue v) (b1.peek kb).toNat with
        | none => ⟨st, pos, .bad⟩
        | some d => applyDistance { st with word := b2.word, count := b2.count } pos (wordValue v) d
      else ⟨st, pos, .needsInput⟩
    else ⟨st, pos, .bad⟩
  else ⟨st, pos, .needsInput⟩

/-- The distance's tree from the context map, then its symbol and extra bits. -/
def stepDistanceSymbol (H : Hdr) (st : Cmd) (pos : USize) : Stepped :=
  if ht : 4 * st.dCur.toNat + 4 ≤ H.dMap.size then
    have hcid := distanceContextId_lt st.clen.toNat
    have hi : (USize.ofNat (4 * st.dCur.toNat + distanceContextId st.clen.toNat)).toNat < H.dMap.size := by
      have := H.dMap32
      rw [usize_ofNat' (by omega)]
      omega
    distanceThrough H st pos (H.dMap.uget (USize.ofNat (4 * st.dCur.toNat + distanceContextId st.clen.toNat)) hi)
      (H.dMapLt _ hi)
  else ⟨st, pos, .bad⟩

/-- The distance's symbol and extra bits do their job. -/
theorem distanceThrough_ok {α : Type} {w k : Nat} {H : Hdr} {m : MetaBlockHeader} {K : CommandState → List Bool → Option α}
    {a : ByteArray} {stop : USize} {s : CommandState} {clen : Nat} {dist : BlockState} {st : Cmd} {pos : USize} {tree : UInt8}
    (htree : tree.toNat < H.treesD.toNat) (hH : HdrRel H m) (hrel : Rel w k m st (.distanceSymbol s clen dist))
    (hindex : distancePrefixCodeIndex m.distanceMap dist.types.cur (distanceContextId clen) = some tree.toNat)
    (hp : pos.toNat ≤ stop.toNat) (hfull : 56 < st.count.toNat ∨ pos = stop) :
    StepOk w k m K a stop (.distanceSymbol s clen dist) st pos (distanceThrough H st pos tree htree) := by
  have hrel0 := hrel
  obtain ⟨hC, htag, hprod, hclen⟩ := hrel
  have hds : cmdDistances st = s.distances := by
    have h0 := hC.d0
    have h1 := hC.d1
    have h2 := hC.d2
    have h3 := hC.d3
    unfold cmdDistances
    rw [← h0, ← h1, ← h2, ← h3]
  have hnp : H.npostfix.toNat = m.npostfix := hH.npostfix
  have hnd : H.ndirect.toNat = m.ndirect := hH.ndirect
  obtain ⟨code, hcode, hok, hcomp, hsym⟩ := hH.d _ htree
  have hb : 4 * tree.toUInt64.toNat + 4 ≤ H.dBase.size := by
    rw [H.dSize, UInt8.toNat_toUInt64]
    omega
  have hbase : (tableBase H.dBase tree.toUInt64 hb H.d32).toNat = u32At H.dBase tree.toNat := by
    rw [tableBase_toNat, UInt8.toNat_toUInt64]
  rw [← hbase] at hok
  obtain ⟨h15, hread, hshort⟩ := lookup_read (b := ⟨st.word, st.count⟩) hok hok.toTableFits H.lit.arena32 hcomp
  dsimp only at h15 hread hshort
  unfold distanceThrough
  dsimp only
  generalize lookup H.arena _ st.word _ _ = v at h15 hread hshort ⊢
  split
  · rename_i hl
    have hl' := UInt64.le_iff_toNat_le.mp hl
    have hsymv : wordValue v < distanceAlphabetSize m.npostfix m.ndirect := decodeSymbol_lt hsym (hread hl [])
    have hn24 := (distanceExtraBits_le_iff _ _ _).mp hsymv
    rw [hnp, hnd, ite_eq_left hn24, hds]
    have hw1 := BitBuffer.drop_wf hC.wf (wordBits_lt v) hl'
    have hc1 : ((BitBuffer.mk st.word st.count).drop (wordBits v)).count.toNat = st.count.toNat - (wordBits v).toNat :=
      drop_count hl'
    have hku : (UInt64.ofNat (distanceExtraBits m.npostfix m.ndirect (wordValue v))).toNat =
        distanceExtraBits m.npostfix m.ndirect (wordValue v) := u64_ofNat (by omega)
    generalize hb1 : (BitBuffer.mk st.word st.count).drop (wordBits v) = b1 at hw1 hc1 ⊢
    split
    · rename_i hle
      have hle' := UInt64.le_iff_toNat_le.mp hle
      have hint := fun f : List Bool => read_int (b := b1) (k := UInt64.ofNat (distanceExtraBits m.npostfix m.ndirect (wordValue v)))
        f (by omega) hle
      rw [hku] at hint
      have hw2 := BitBuffer.drop_wf hw1 (k := UInt64.ofNat (distanceExtraBits m.npostfix m.ndirect (wordValue v))) (by omega) hle'
      cases hd : distanceOf m.npostfix m.ndirect s.distances (wordValue v)
          (b1.peek (UInt64.ofNat (distanceExtraBits m.npostfix m.ndirect (wordValue v)))).toNat with
      | none =>
        refine StepOk.ofBad rfl fun F => ?_
        rw [stateBits_eq, rest_distanceSymbol hindex hcode (hread hl _), hb1, hint]
        show (distanceOf m.npostfix m.ndirect s.distances (wordValue v) _ >>= _) = none
        rw [hd]
        rfl
      | some d =>
        generalize b1.drop (UInt64.ofNat (distanceExtraBits m.npostfix m.ndirect (wordValue v))) = b2 at hw2 hint ⊢
        refine step_of_apply (s := { s with distance := dist }) (clen := clen) { hC with wf := hw2 } hprod hclen
          (distanceOf_pos hd) hp fun F => ?_
        rw [stateBits_eq, rest_distanceSymbol hindex hcode (hread hl _), hb1, hint]
        show (distanceOf m.npostfix m.ndirect s.distances (wordValue v) _ >>= _) = _
        rw [hd]
        rfl
    · rename_i hle
      have hnot : b1.count.toNat < distanceExtraBits m.npostfix m.ndirect (wordValue v) := by
        rw [← hku]
        exact Nat.lt_of_not_le fun h => hle (UInt64.le_iff_toNat_le.mpr h)
      refine StepOk.ofShort hrel0 (hfull.resolve_left (by have := hC.wf.count_le; omega)) ?_
      have hd := hread hl []
      rw [List.append_nil, List.append_nil] at hd
      rw [rest_distanceSymbol hindex hcode hd, hb1, readInt_short hnot]
      rfl
  · rename_i hl
    have hnot : st.count.toNat < (wordBits v).toNat := Nat.lt_of_not_le fun h => hl (UInt64.le_iff_toNat_le.mpr h)
    exact StepOk.ofShort hrel0 (hfull.resolve_left (by omega)) (rest_distanceSymbol_none hindex hcode (hshort hl))

/-- The distance's symbol does its job. -/
theorem stepDistanceSymbol_ok {α : Type} {w k : Nat} {H : Hdr} {m : MetaBlockHeader} {K : CommandState → List Bool → Option α}
    {a : ByteArray} {stop : USize} {s : CommandState} {clen : Nat} {dist : BlockState} {st : Cmd} {pos : USize} (hH : HdrRel H m)
    (hrel : Rel w k m st (.distanceSymbol s clen dist)) (hp : pos.toNat ≤ stop.toNat)
    (hfull : 56 < st.count.toNat ∨ pos = stop) :
    StepOk w k m K a stop (.distanceSymbol s clen dist) st pos (stepDistanceSymbol H st pos) := by
  have hrel0 := hrel
  obtain ⟨hC, htag, hprod, hclen⟩ := hrel
  have hcurLt : st.dCur.toNat < m.distance.n := by
    rw [← hC.dRel.cur]
    exact hC.dRel.wf.2.1
  have ht : 4 * st.dCur.toNat + 4 ≤ H.dMap.size := by
    rw [H.dMapSize, hH.nD]
    omega
  have hcid := distanceContextId_lt st.clen.toNat
  have hdm32 := H.dMap32
  have hu : (USize.ofNat (4 * st.dCur.toNat + distanceContextId st.clen.toNat)).toNat =
      4 * st.dCur.toNat + distanceContextId st.clen.toNat := usize_ofNat' (by omega)
  unfold stepDistanceSymbol
  rw [dite_eq_left ht]
  have hi : (USize.ofNat (4 * st.dCur.toNat + distanceContextId st.clen.toNat)).toNat < H.dMap.size := by
    rw [hu]
    omega
  have hmapv := hH.dMap _ hi
  rw [hu] at hmapv
  refine distanceThrough_ok _ hH hrel0 ?_ hp hfull
  unfold distancePrefixCodeIndex
  rw [hC.dRel.cur, ← hclen]
  exact hmapv

end Brotli.Decoder
