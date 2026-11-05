import Brotli.Decoder.StepLiterals
import Brotli.Decoder.DictBytes

/-!
# The distance's steps

After a command's literals: finish if MLEN is reached, otherwise find the distance, implied or read, and begin the copy
it selects, a backward copy or a dictionary word.
-/

namespace Brotli.Decoder

open Brotli.Spec

/-- Begins a word that has been built. -/
def applyBuilt (st : Cmd) (pos : USize) (word : ByteArray) : Cmd :=
  if st.remaining < word.usize.toUInt64 then markStep st pos .bad
  else
    { st with
      remaining := st.remaining - word.usize.toUInt64, ext := { st.ext with wordBuf := word, wordPos := 0 }
      tag := .word, pos := pos, status := .next }

/-- Begins the dictionary word a distance selects. -/
def applyWord (st : Cmd) (pos : USize) (wordId : UInt64) : Cmd :=
  if h : dictValid st.clen wordId then applyBuilt st pos (dictBuild st.clen wordId h)
  else markStep st pos .bad

/-- Begins the copy a distance selects. -/
def applyDistance (st : Cmd) (pos : USize) (dcode d : UInt64) : Cmd :=
  if st.written.toUInt64 < d then applyWord st pos (d - (st.written.toUInt64 + 1))
  else if st.remaining < st.clen then markStep st pos .bad
  else if dcode = 0 then
    { st with
      remaining := st.remaining - st.clen, left := st.clen, tag := .copy, pos := pos, status := .next
      ext := { st.ext with dist := d } }
  else
    { st with
      remaining := st.remaining - st.clen, left := st.clen, tag := .copy, pos := pos, status := .next
      ext := { st.ext with dist := d, d0 := d, d1 := st.d0, d2 := st.d1, d3 := st.d2 } }

/-- A built word, in the terms of `copyPhase`. -/
private theorem word_cases {w k : Nat} {m : MetaBlockHeader} {st : Cmd} {s : CommandState} {pos : USize} {wb : ByteArray}
    (hC : Core w k m st s.output s.remaining s.distances s.insertCopy s.literal s.distance)
    (hprod : s.produced = s.output.length) (hlen : (wb.data.toList.map UInt8.toNat).length + 1 ≤ 38) :
    (((some (wb.data.toList.map UInt8.toNat)).bind fun word =>
        if s.remaining < word.length then none
        else some (Phase.word { s with
          produced := s.produced + word.length
          remaining := s.remaining - word.length } word)) = none ∧
      (applyBuilt st pos wb).status = .bad) ∨
      ∃ p, ((some (wb.data.toList.map UInt8.toNat)).bind fun word =>
          if s.remaining < word.length then none
          else some (Phase.word { s with
            produced := s.produced + word.length
            remaining := s.remaining - word.length } word)) = some p ∧
        (applyBuilt st pos wb).status = .next ∧ (applyBuilt st pos wb).pos = pos ∧ (applyBuilt st pos wb).word = st.word ∧
        (applyBuilt st pos wb).count = st.count ∧ Rel w k m (applyBuilt st pos wb) p := by
  unfold applyBuilt
  have hrem := hC.rem
  have hmapLen : (wb.data.toList.map UInt8.toNat).length = wb.size := by
    simp only [List.length_map, Array.length_toList]
    rfl
  have hsizeU : wb.usize.toUInt64.toNat = wb.size := by
    rw [USize.toNat_toUInt64]
    exact usize_ofNat' (by omega)
  dsimp only [Option.bind]
  by_cases hr : st.remaining < wb.usize.toUInt64
  · have hrN := UInt64.lt_iff_toNat_lt.mp hr
    have hr' : s.remaining < (wb.data.toList.map UInt8.toNat).length := by omega
    rw [ite_eq_left hr, ite_eq_left hr']
    exact Or.inl ⟨rfl, rfl⟩
  · have hrN : ¬ st.remaining.toNat < wb.usize.toUInt64.toNat := fun e => hr (UInt64.lt_iff_toNat_lt.mpr e)
    have hr' : ¬ s.remaining < (wb.data.toList.map UInt8.toNat).length := by omega
    rw [ite_eq_right hr, ite_eq_right hr']
    refine Or.inr ⟨_, rfl, rfl, rfl, rfl, rfl, ⟨?_, rfl, ?_, ?_, ?_, ?_⟩⟩
    · have hwLe : wb.size ≤ 38 := by omega
      refine { hC with rem := ?_, wordLe := hwLe }
      show (st.remaining - wb.usize.toUInt64).toNat = _
      rw [u64_sub (by omega), hsizeU]
      show _ = s.remaining - (wb.data.toList.map UInt8.toNat).length
      omega
    · show s.produced + (wb.data.toList.map UInt8.toNat).length = s.output.length + (wb.data.toList.map UInt8.toNat).length
      omega
    · rfl
    · show wb.size ≤ 38
      omega
    · exact Nat.zero_le _

/-- What `applyDistance` does: it rejects when `copyPhase` does, and otherwise stands for the place `copyPhase` gives,
with the buffer unchanged. -/
theorem applyDistance_spec {w k : Nat} {m : MetaBlockHeader} {st : Cmd} {s : CommandState} {pos : USize} {clen : Nat}
    {dcode d : UInt64} (hC : Core w k m st s.output s.remaining s.distances s.insertCopy s.literal s.distance)
    (hprod : s.produced = s.output.length) (hclen : st.clen.toNat = clen) (hd1 : 1 ≤ d.toNat) :
    (copyPhase w s clen dcode.toNat d.toNat = none ∧ (applyDistance st pos dcode d).status = .bad) ∨
      ∃ p, copyPhase w s clen dcode.toNat d.toNat = some p ∧ (applyDistance st pos dcode d).status = .next ∧
        (applyDistance st pos dcode d).pos = pos ∧ (applyDistance st pos dcode d).word = st.word ∧
        (applyDistance st pos dcode d).count = st.count ∧ Rel w k m (applyDistance st pos dcode d) p := by
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
  by_cases hdict : st.written.toNat < d.toNat
  · have hdU : st.written.toUInt64 < d := UInt64.lt_iff_toNat_lt.mpr hdict
    have hwid : (d - (st.written.toUInt64 + 1)).toNat = d.toNat - (st.written.toNat + 1) := by
      have h1 : (st.written.toUInt64 + 1).toNat = st.written.toNat + 1 := by
        rw [UInt64.toNat_add, USize.toNat_toUInt64, show (1 : UInt64).toNat = 1 from rfl]
        exact Nat.mod_eq_of_lt (by omega)
      rw [u64_sub (by rw [h1]; omega), h1]
    rw [ite_eq_left hdU, copyPhase_word (by rw [hmax]; exact hdict), hmax, dictBuild_spec hwid]
    unfold applyWord
    by_cases hv : dictValid st.clen (d - (st.written.toUInt64 + 1))
    · rw [dite_eq_left hv, dite_eq_left hv]
      have hsomeW := dictBuild_spec (clen := st.clen) hwid
      rw [dite_eq_left hv] at hsomeW
      generalize dictBuild st.clen (d - (st.written.toUInt64 + 1)) hv = wb at hsomeW ⊢
      exact word_cases hC hprod (dictionaryWord_length hsomeW)
    · rw [dite_eq_right hv, dite_eq_right hv]
      exact Or.inl ⟨rfl, rfl⟩
  · have hdU : ¬ st.written.toUInt64 < d := fun e => hdict (UInt64.lt_iff_toNat_lt.mp e)
    rw [ite_eq_right hdU, copyPhase_copy (by rw [hmax]; exact hdict)]
    by_cases hr : st.remaining < st.clen
    · have hrN := UInt64.lt_iff_toNat_lt.mp hr
      have hr' : s.remaining < st.clen.toNat := by omega
      rw [ite_eq_left hr, ite_eq_left hr']
      exact Or.inl ⟨rfl, rfl⟩
    · have hrN : ¬ st.remaining.toNat < st.clen.toNat := fun e => hr (UInt64.lt_iff_toNat_lt.mpr e)
      have hr' : ¬ s.remaining < st.clen.toNat := by omega
      rw [ite_eq_right hr, ite_eq_right hr']
      have hdsmall : d.toNat < 2 ^ 32 := by omega
      have hlt := hC.dsLt
      have hremNew : (st.remaining - st.clen).toNat = s.remaining - st.clen.toNat := by
        rw [u64_sub (by omega)]
        omega
      by_cases h0 : dcode = 0
      · have hpush : pushDistance s.distances dcode.toNat d.toNat false = s.distances := by
          simp [pushDistance, u64_zero h0]
        rw [ite_eq_left h0]
        refine Or.inr ⟨_, rfl, rfl, rfl, rfl, rfl, ⟨?_, rfl, ?_, rfl, rfl, hd1, by omega, by show d.toNat ≤ s.output.length; omega⟩⟩
        · refine { hC with rem := hremNew, d0 := ?_, d1 := ?_, d2 := ?_, d3 := ?_, dsLt := ?_ }
          · show (pushDistance s.distances dcode.toNat d.toNat false).last = _
            rw [hpush]
            exact hC.d0
          · show (pushDistance s.distances dcode.toNat d.toNat false).secondToLast = _
            rw [hpush]
            exact hC.d1
          · show (pushDistance s.distances dcode.toNat d.toNat false).thirdToLast = _
            rw [hpush]
            exact hC.d2
          · show (pushDistance s.distances dcode.toNat d.toNat false).fourthToLast = _
            rw [hpush]
            exact hC.d3
          · show (pushDistance s.distances dcode.toNat d.toNat false).last < 2 ^ 32 ∧
              (pushDistance s.distances dcode.toNat d.toNat false).secondToLast < 2 ^ 32 ∧
              (pushDistance s.distances dcode.toNat d.toNat false).thirdToLast < 2 ^ 32 ∧
              (pushDistance s.distances dcode.toNat d.toNat false).fourthToLast < 2 ^ 32
            rw [hpush]
            exact hlt
        · show s.produced + st.clen.toNat = s.output.length + st.clen.toNat
          omega
      · have hpush : pushDistance s.distances dcode.toNat d.toNat false =
            ⟨d.toNat, s.distances.last, s.distances.secondToLast, s.distances.thirdToLast⟩ := by
          simp [pushDistance, u64_ne h0]
        rw [ite_eq_right h0]
        refine Or.inr ⟨_, rfl, rfl, rfl, rfl, rfl, ⟨?_, rfl, ?_, rfl, rfl, hd1, by omega, by show d.toNat ≤ s.output.length; omega⟩⟩
        · refine { hC with rem := hremNew, d0 := ?_, d1 := ?_, d2 := ?_, d3 := ?_, dsLt := ?_ }
          · show (pushDistance s.distances dcode.toNat d.toNat false).last = _
            rw [hpush]
          · show (pushDistance s.distances dcode.toNat d.toNat false).secondToLast = _
            rw [hpush]
            exact hC.d0
          · show (pushDistance s.distances dcode.toNat d.toNat false).thirdToLast = _
            rw [hpush]
            exact hC.d1
          · show (pushDistance s.distances dcode.toNat d.toNat false).fourthToLast = _
            rw [hpush]
            exact hC.d2
          · show (pushDistance s.distances dcode.toNat d.toNat false).last < 2 ^ 32 ∧
              (pushDistance s.distances dcode.toNat d.toNat false).secondToLast < 2 ^ 32 ∧
              (pushDistance s.distances dcode.toNat d.toNat false).thirdToLast < 2 ^ 32 ∧
              (pushDistance s.distances dcode.toNat d.toNat false).fourthToLast < 2 ^ 32
            rw [hpush]
            exact ⟨hdsmall, hlt.1, hlt.2.1, hlt.2.2.1⟩
        · show s.produced + st.clen.toNat = s.output.length + st.clen.toNat
          omega

/-- A copy adds nothing to the output yet. -/
private theorem copyPhase_out {w : Nat} {s : CommandState} {clen dcode d : Nat} {q : Phase} (h : copyPhase w s clen dcode d = some q) :
    q.out = s.output := by
  unfold copyPhase at h
  dsimp only at h
  split at h
  · obtain ⟨word, _, h⟩ := Option.bind_eq_some_iff.mp h
    split at h
    · cases h
    · cases h
      rfl
  · split at h
    · cases h
    · cases h
      rfl

private theorem applyDistance_pend (st : Cmd) (pos : USize) (dcode d : UInt64) : (applyDistance st pos dcode d).pend = st.pend := by
  unfold applyDistance applyWord applyBuilt
  split
  · split
    · split <;> rfl
    · rfl
  · split
    · rfl
    · split <;> rfl

/-- A distance's result, in the terms of a step. -/
private theorem step_of_apply {α : Type} {w k : Nat} {m : MetaBlockHeader} {K : CommandState → List Bool → Option α}
    {a : ByteArray} {stop : USize} {p : Phase} {st st1 : Cmd} {s : CommandState} {pos : USize} {clen : Nat} {dcode d : UInt64}
    (hC : Core w k m st1 s.output s.remaining s.distances s.insertCopy s.literal s.distance)
    (hprod : s.produced = s.output.length) (hclen : st1.clen.toNat = clen) (hd1 : 1 ≤ d.toNat) (hp : pos.toNat ≤ stop.toNat)
    (hrank : 1 < (rankC p).1) (hpo : p.out = s.output) (hpe : st1.pend = st.pend)
    (hrest : ∀ F, rest w m K p (stateBits st a pos stop F) =
      copyPhase w s clen dcode.toNat d.toNat >>= fun q => rest w m K q (stateBits st1 a pos stop F))
    (hj : ∀ F, cStep w m p (stateBits st a pos stop F) =
      lookIn (copyPhase w s clen dcode.toNat d.toNat) fun q => .next q (stateBits st1 a pos stop F)) :
    StepOk w k m K a stop p st pos (applyDistance st1 pos dcode d) := by
  rcases applyDistance_spec (pos := pos) (dcode := dcode) hC hprod hclen hd1 with ⟨hn, hs⟩ | ⟨q, hq, hs, hpos, hw, hc, hR⟩
  · refine StepOk.ofBad hs fun F => ?_
    rw [hrest, hn]
    rfl
  · refine StepOk.ofNext (hd := Or.inr (Or.inl (by rw [copyPhase_rank hq]; exact hrank)))
      (hout := ⟨[], by rw [copyPhase_out hq, hpo]; rfl, by rw [applyDistance_pend, hpe]; rfl⟩) hs hR (by rw [hpos]; exact Nat.le_refl _) (by rw [hpos]; exact hp) (fun F => ?_)
      (fun F => Reach.one ?_)
    · rw [hrest, hq]
      show rest w m K q (stateBits st1 a pos stop F) = rest w m K q (stateBits _ a _ stop F)
      rw [hpos, stateBits_eq, stateBits_eq, hw, hc]
    · rw [hj, lookIn_some hq, hpos, stateBits_eq, stateBits_eq, hw, hc]

/-! ### Where the distance comes from -/

/-- The start of a command's distance. -/
def stepDistance (H : Hdr) (st : Cmd) (pos : USize) : Cmd :=
  if st.remaining = 0 then { st with tag := .command, pos := pos, status := .next }
  else if st.code < 128 then
    if st.d0 = 0 then markStep st pos .bad
    else applyDistance st pos 0 st.d0
  else if st.dCount = 0 then
    if hn : 2 ≤ H.nD then
      let hn' := UInt64.le_iff_toNat_le.mp hn
      let r := blockSwitch H.arena H.lit.arena32 H.baseTD H.baseCD (H.swD hn').1 (H.swD hn').2 H.nD st.dCur st.dPrev
        st.word st.count
      match r.status with
      | .ok =>
        { st with
          word := r.word, count := r.count, dCount := r.blockCount - 1, ext := { st.ext with dCur := r.cur, dPrev := st.dCur }
          flags := { st.flags with
            fD0 := markWord st.flags.fD0 r.cur 0, fD1 := markWord st.flags.fD1 r.cur 1, fD2 := markWord st.flags.fD2 r.cur 2
            fD3 := markWord st.flags.fD3 r.cur 3 }
          tag := .distanceSymbol, pos := pos, status := .next }
      | .short => markStep st pos .needsInput
      | .bad => markStep st pos .bad
    else markStep st pos .bad
  else { st with dCount := st.dCount - 1, tag := .distanceSymbol, pos := pos, status := .next }

/-- The start of a command's distance does its job. -/
theorem stepDistance_ok {α : Type} {w k : Nat} {H : Hdr} {m : MetaBlockHeader} {K : CommandState → List Bool → Option α}
    {a : ByteArray} {stop : USize} {s : CommandState} {c clen : Nat} {st : Cmd} {pos : USize} (hH : HdrRel H m)
    (hrel : Rel w k m st (.distance s c clen)) (hp : pos.toNat ≤ stop.toNat) (hfull : 56 < st.count.toNat ∨ pos = stop) :
    StepOk w k m K a stop (.distance s c clen) st pos (stepDistance H st pos) := by
  have hrel0 := hrel
  obtain ⟨hC, htag, hprod, hcode, hclen⟩ := hrel
  have hrem := hC.rem
  have h0d := hC.d0
  unfold stepDistance
  split
  · rename_i h0
    have h0N := u64_zero h0
    exact StepOk.ofNext (p' := .command s) rfl ⟨{ hC with }, rfl, hprod⟩ (Nat.le_refl _) hp
      (fun F => rest_distance_end _ (by omega)) (fun F => Reach.one (cStep_distance_end _ (by omega)))
  · rename_i h0
    have h0N := u64_ne h0
    have h0' : s.remaining ≠ 0 := by omega
    split
    · rename_i himp
      have himpN := UInt64.lt_iff_toNat_lt.mp himp
      have hc : implicitZeroDistance c = true := by
        unfold implicitZeroDistance
        rw [← hcode]
        exact decide_eq_true himpN
      by_cases hz : st.d0 = 0
      · rw [ite_eq_left hz]
        refine StepOk.ofBad rfl fun F => ?_
        rw [rest_distance_implicit _ h0' hc, distanceOf_zero, ite_eq_left (by rw [h0d]; exact u64_zero hz)]
        rfl
      · rw [ite_eq_right hz]
        have hne := u64_ne hz
        refine step_of_apply (s := s) (clen := clen) hC hprod hclen (by omega) hp (by simp only [rankC]; omega) rfl rfl
          (fun F => ?_) (fun F => ?_)
        · rw [rest_distance_implicit _ h0' hc, distanceOf_zero, ite_eq_right (by rw [h0d]; exact hne), h0d]
          rfl
        · rw [cStep_distance_implicit _ h0' hc, distanceOf_zero, ite_eq_right (by rw [h0d]; exact hne), h0d]
          rfl
    · rename_i himp
      have hc : implicitZeroDistance c = false := by
        unfold implicitZeroDistance
        rw [← hcode]
        exact decide_eq_false fun e => himp (UInt64.lt_iff_toNat_lt.mpr e)
      split
      rotate_left
      · rename_i hcnt
        have hcntN := u64_ne hcnt
        have hcs : s.distance.count ≠ 0 := by
          rw [hC.dRel.count]
          exact hcntN
        refine StepOk.ofNext (p' := .distanceSymbol s clen { s.distance with count := s.distance.count - 1 }) rfl
          ⟨{ hC with dRel := hC.dRel.decr hcntN }, rfl, hprod, hclen⟩ (Nat.le_refl _) hp (fun F => ?_)
          (fun F => Reach.one (by rw [cStep_distance_switch _ h0' hc, nextIn_some (fun h => hcs h.1) (nextElement_count _ hcs)]; rfl))
        rw [stateBits_eq, rest_distance_switch _ h0' hc, nextElement_count _ hcs]
        rfl
      · rename_i hcnt
        have hcntN : st.dCount.toNat = 0 := u64_zero hcnt
        have hcz : s.distance.count = 0 := by
          rw [hC.dRel.count]
          exact hcntN
        split
        · rename_i hn
          have hn' : 2 ≤ H.nD.toNat := UInt64.le_iff_toNat_le.mp hn
          have hn2 : 2 ≤ m.distance.n := by
            rw [← hH.nD]
            exact hn'
          have hsp := blockSwitch_rel (h32 := H.lit.arena32) (hT := (H.swD hn').1) (hCt := (H.swD hn').2) hH.nD hH.catD
            hH.ok.distance hC.dRel hcntN hC.wf hn2
          dsimp only at hsp ⊢
          generalize blockSwitch _ _ _ _ _ _ _ _ _ _ _ = r at hsp ⊢
          obtain ⟨hok, hshort, hbad⟩ := hsp
          cases hs : r.status with
          | ok =>
            obtain ⟨hw, hlt, hc1, hc2, hnext⟩ := hok hs
            have h256 := hH.ok.distance.2.1
            refine StepOk.ofNext (p' := .distanceSymbol s clen ⟨⟨st.dCur.toNat, r.cur.toNat⟩, r.blockCount.toNat - 1,
              r.cur.toNat :: s.distance.seen⟩) rfl ⟨?_, rfl, hprod, hclen⟩ (Nat.le_refl _) hp (fun F => ?_)
              (fun F => Reach.one (by rw [stateBits_eq, cStep_distance_switch _ h0' hc, nextIn_some (fun h => absurd h.2 (by omega)) (hnext _)]; rfl))
            · exact { hC with
                wf := hw
                dRel := hC.dRel.switched hlt h256 (u64_sub_one hc1).symm }
            · rw [stateBits_eq, rest_distance_switch _ h0' hc, hnext]
              rfl
          | short =>
            obtain ⟨_, _, hc54, hnone⟩ := hshort hs
            refine StepOk.ofShort hrel0 (hfull.resolve_left (by omega)) ?_
              (by rw [cStep_distance_switch _ h0' hc]; exact nextIn_short (fun h => absurd h.2 (by omega)) hnone (by simp only [BitBuffer.held_length]; omega))
            rw [rest_distance_switch _ h0' hc, hnone]
            rfl
          | bad =>
            refine StepOk.ofBad rfl fun F => ?_
            rw [stateBits_eq, rest_distance_switch _ h0' hc, hbad hs]
            rfl
        · rename_i hn
          have hn' : m.distance.n < 2 := by
            rw [← hH.nD]
            exact Nat.lt_of_not_le fun e => hn (UInt64.le_iff_toNat_le.mpr e)
          refine StepOk.ofBad rfl fun F => ?_
          rw [rest_distance_switch _ h0' hc, nextElement_single _ hcz hn']
          rfl

/-! ### The distance's symbol -/

/-- A state with a new bit buffer. Not inlined, so that it reuses the state even after the branches of a distance. -/
@[noinline] def setBits (st : Cmd) (word count : UInt64) : Cmd := { st with word := word, count := count }

/-- The distance, once its symbol is looked up. -/
@[inline] def distanceStep (H : Hdr) (st : Cmd) (pos : USize) (v : UInt64) : Cmd :=
  if wordBits v ≤ st.count then
    let nbits := extraBitsFast H.npostfix H.ndirect (wordSym v)
    let b1 := (BitBuffer.mk st.word st.count).drop (wordBits v)
    if nbits ≤ 24 then
      if nbits ≤ b1.count then
        let b2 := b1.drop nbits
        let d := distFast H.npostfix H.ndirect st.d0 st.d1 st.d2 st.d3 (wordSym v) (b1.peek nbits)
        if d = 0 then markStep st pos .bad
        else applyDistance (setBits st b2.word b2.count) pos (wordSym v) d
      else markStep st pos .needsInput
    else markStep st pos .bad
  else markStep st pos .needsInput

/-- The distance's symbol and extra bits, through a tree. -/
def distanceThrough (H : Hdr) (st : Cmd) (pos : USize) (tree : UInt8) (htree : tree.toNat < H.treesD.toNat) : Cmd :=
  have hb : 4 * tree.toUInt64.toNat + 4 ≤ H.dBase.size := by
    rw [H.dSize, UInt8.toNat_toUInt64]
    omega
  have hfit : TableFits H.arena (tableBase H.dBase tree.toUInt64 hb H.d32).toNat := by
    rw [tableBase_toNat, UInt8.toNat_toUInt64]
    exact H.dFits _ htree
  distanceStep H st pos (lookup H.arena (tableBase H.dBase tree.toUInt64 hb H.d32) st.word hfit H.lit.arena32)

/-- The position in the distance context map. -/
@[inline] def dMapIndex (cur clen : UInt64) : USize :=
  (cur + cur + cur + cur + distCid clen).toUSize

theorem dMapIndex_toNat {cur clen : UInt64} (h : cur.toNat < 2 ^ 30) :
    (dMapIndex cur clen).toNat = 4 * cur.toNat + distanceContextId clen.toNat := by
  have hcid := distanceContextId_lt clen.toNat
  have hv : (cur + cur + cur + cur + distCid clen).toNat = 4 * cur.toNat + distanceContextId clen.toNat := by
    rw [UInt64.toNat_add, UInt64.toNat_add, UInt64.toNat_add, UInt64.toNat_add, distCid_toNat]
    have e1 : (cur.toNat + cur.toNat) % 2 ^ 64 = cur.toNat + cur.toNat := Nat.mod_eq_of_lt (by omega)
    have e2 : (cur.toNat + cur.toNat + cur.toNat) % 2 ^ 64 = cur.toNat + cur.toNat + cur.toNat := Nat.mod_eq_of_lt (by omega)
    have e3 : (cur.toNat + cur.toNat + cur.toNat + cur.toNat) % 2 ^ 64 = cur.toNat + cur.toNat + cur.toNat + cur.toNat :=
      Nat.mod_eq_of_lt (by omega)
    rw [e1, e2, e3]
    exact (Nat.mod_eq_of_lt (by omega)).trans (by omega)
  unfold dMapIndex
  rw [word_toUSize (by rw [hv]; omega), hv]

/-- The distance's tree from the context map, then its symbol and extra bits. -/
def stepDistanceSymbol (H : Hdr) (st : Cmd) (pos : USize) : Cmd :=
  if ht : st.dCur < H.nD then
    have ht' := UInt64.lt_iff_toNat_lt.mp ht
    have hi : (dMapIndex st.dCur st.clen).toNat < H.dMap.size := by
      have h1 := H.dMap32
      have h2 := H.dMapSize
      have hcid := distanceContextId_lt st.clen.toNat
      rw [dMapIndex_toNat (by omega)]
      omega
    distanceThrough H st pos (H.dMap.uget (dMapIndex st.dCur st.clen) hi) (H.dMapLt _ hi)
  else markStep st pos .bad

private theorem readDistanceParts_eq {np nd : Nat} {code : PrefixCode} {bs r : List Bool} {dc : Nat}
    (hd : decodeSymbol code bs = some (dc, r)) :
    readDistanceParts np nd code bs = readInt (distanceExtraBits np nd dc) r >>= fun (e, b) => some ((dc, e), b) := by
  simp only [readDistanceParts, bind, Option.bind, hd]

private theorem readDistanceParts_none {np nd : Nat} {code : PrefixCode} {bs : List Bool} (hd : decodeSymbol code bs = none) :
    readDistanceParts np nd code bs = none := by
  simp only [readDistanceParts, bind, Option.bind, hd]

/-- The distance's symbol and extra bits do their job. -/
theorem distanceThrough_ok {α : Type} {w k : Nat} {H : Hdr} {m : MetaBlockHeader} {K : CommandState → List Bool → Option α}
    {a : ByteArray} {stop : USize} {s : CommandState} {clen : Nat} {dist : BlockState} {st : Cmd} {pos : USize} {tree : UInt8}
    (htree : tree.toNat < H.treesD.toNat) (hH : HdrRel H m) (hrel : Rel w k m st (.distanceSymbol s clen dist))
    (hindex : distancePrefixCodeIndex m.distanceMap dist.types.cur (distanceContextId clen) = some tree.toNat)
    (hp : pos.toNat ≤ stop.toNat) (hfull : 56 < st.count.toNat ∨ pos = stop) :
    StepOk w k m K a stop (.distanceSymbol s clen dist) st pos (distanceThrough H st pos tree htree) := by
  have hrel0 := hrel
  obtain ⟨hC, htag, hprod, hclen⟩ := hrel
  have hds : s.distances = ⟨st.d0.toNat, st.d1.toNat, st.d2.toNat, st.d3.toNat⟩ := by
    have h0 := hC.d0
    have h1 := hC.d1
    have h2 := hC.d2
    have h3 := hC.d3
    rw [← h0, ← h1, ← h2, ← h3]
  have hnp : H.npostfix.toNat = m.npostfix := hH.npostfix
  have hnd : H.ndirect.toNat = m.ndirect := hH.ndirect
  have hd0lt : st.d0.toNat < 2 ^ 32 := by
    rw [← hC.d0]
    exact hC.dsLt.1
  have hd1lt : st.d1.toNat < 2 ^ 32 := by
    rw [← hC.d1]
    exact hC.dsLt.2.1
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
  unfold distanceStep
  dsimp only
  split
  · rename_i hl
    have hl' := UInt64.le_iff_toNat_le.mp hl
    have hsymv : wordValue v < distanceAlphabetSize m.npostfix m.ndirect := decodeSymbol_lt hsym (hread hl [])
    have hn24 := (distanceExtraBits_le_iff _ _ _).mp hsymv
    have hsym16 : (wordSym v).toNat < 2 ^ 16 := wordValue_lt v
    have hbitsE : (extraBitsFast H.npostfix H.ndirect (wordSym v)).toNat = distanceExtraBits m.npostfix m.ndirect (wordValue v) := by
      rw [extraBitsFast_toNat H.npLe H.ndLe hsym16, hnp, hnd]
      rfl
    have hbits24 : extraBitsFast H.npostfix H.ndirect (wordSym v) ≤ 24 := UInt64.le_iff_toNat_le.mpr (by
      rw [hbitsE, show (24 : UInt64).toNat = 24 from rfl]
      exact hn24)
    rw [ite_eq_left hbits24]
    have hw1 := BitBuffer.drop_wf hC.wf (wordBits_lt v) hl'
    have hc1 : ((BitBuffer.mk st.word st.count).drop (wordBits v)).count.toNat = st.count.toNat - (wordBits v).toNat :=
      drop_count hl'
    generalize hb1 : (BitBuffer.mk st.word st.count).drop (wordBits v) = b1 at hw1 hc1 ⊢
    split
    · rename_i hle
      have hle' := UInt64.le_iff_toNat_le.mp hle
      have hint := fun f : List Bool => read_int (b := b1) (k := extraBitsFast H.npostfix H.ndirect (wordSym v))
        f (by omega) hle
      rw [hbitsE] at hint
      have hw2 := BitBuffer.drop_wf hw1 (k := extraBitsFast H.npostfix H.ndirect (wordSym v)) (by omega) hle'
      have hpeekLt : (b1.peek (extraBitsFast H.npostfix H.ndirect (wordSym v))).toNat <
          2 ^ (extraBitsFast H.npostfix H.ndirect (wordSym v)).toNat := by
        rw [BitBuffer.peek_toNat _ (by omega)]
        exact Nat.mod_lt _ (Nat.two_pow_pos _)
      have hdspec := distFast_spec (d2 := st.d2) (d3 := st.d3) H.npLe H.ndLe hsym16 hd0lt hd1lt (by omega) hpeekLt
      rw [← hds, hnp, hnd] at hdspec
      have hdE : distanceOf m.npostfix m.ndirect s.distances (wordValue v)
          (b1.peek (extraBitsFast H.npostfix H.ndirect (wordSym v))).toNat = _ := hdspec
      generalize distFast H.npostfix H.ndirect st.d0 st.d1 st.d2 st.d3 (wordSym v) _ = d at hdE ⊢
      generalize b1.drop (extraBitsFast H.npostfix H.ndirect (wordSym v)) = b2 at hw2 hint ⊢
      split
      · rename_i hz
        rw [ite_eq_left hz] at hdE
        refine StepOk.ofBad rfl fun F => ?_
        rw [stateBits_eq, rest_distanceSymbol hindex hcode (hread hl _), hb1, hint]
        show (distanceOf m.npostfix m.ndirect s.distances (wordValue v) _ >>= _) = none
        rw [hdE]
        rfl
      · rename_i hz
        rw [ite_eq_right hz] at hdE
        have hd1 := u64_ne hz
        refine step_of_apply (st1 := setBits st b2.word b2.count) (s := { s with distance := dist }) (clen := clen)
          { hC with wf := hw2 } hprod hclen (by omega) hp (by simp only [rankC]; omega) rfl rfl (fun F => ?_) (fun F => ?_)
        · rw [stateBits_eq, rest_distanceSymbol hindex hcode (hread hl _), hb1, hint]
          show (distanceOf m.npostfix m.ndirect s.distances (wordValue v) _ >>= _) = _
          rw [hdE]
          rfl
        · rw [stateBits_eq]
          show lookIn (distancePrefixCodeIndex m.distanceMap dist.types.cur (distanceContextId clen)) _ = _
          rw [lookIn_some hindex, lookIn_some hcode]
          show readIn 39 (readDistanceParts m.npostfix m.ndirect code) _ _ = _
          rw [readIn, readDistanceParts_eq (hread hl _), hb1, hint]
          show lookIn (distanceOf m.npostfix m.ndirect s.distances (wordValue v) _) _ = _
          rw [lookIn_some hdE]
          rfl
    · rename_i hle
      have hnot : b1.count.toNat < distanceExtraBits m.npostfix m.ndirect (wordValue v) := by
        rw [← hbitsE]
        exact Nat.lt_of_not_le fun h => hle (UInt64.le_iff_toNat_le.mpr h)
      have hd := hread hl []
      rw [List.append_nil, List.append_nil] at hd
      refine StepOk.ofShort hrel0 (hfull.resolve_left (by have := hC.wf.count_le; omega)) ?_ ?_
      · rw [rest_distanceSymbol hindex hcode hd, hb1, readInt_short hnot]
        rfl
      · show lookIn (distancePrefixCodeIndex m.distanceMap dist.types.cur (distanceContextId clen)) _ = _
        rw [lookIn_some hindex, lookIn_some hcode]
        show readIn 39 (readDistanceParts m.npostfix m.ndirect code) _ _ = _
        refine readIn_short ?_ (by simp only [BitBuffer.held_length]; omega)
        rw [readDistanceParts_eq hd, hb1, readInt_short hnot]
        rfl
  · rename_i hl
    have hnot : st.count.toNat < (wordBits v).toNat := Nat.lt_of_not_le fun h => hl (UInt64.le_iff_toNat_le.mpr h)
    refine StepOk.ofShort hrel0 (hfull.resolve_left (by omega)) (rest_distanceSymbol_none hindex hcode (hshort hl)) ?_
    show lookIn (distancePrefixCodeIndex m.distanceMap dist.types.cur (distanceContextId clen)) _ = _
    rw [lookIn_some hindex, lookIn_some hcode]
    exact readIn_short (readDistanceParts_none (hshort hl)) (by simp only [BitBuffer.held_length]; omega)

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
  have ht : st.dCur.toNat < H.nD.toNat := by
    rw [hH.nD]
    exact hcurLt
  have hcid := distanceContextId_lt st.clen.toNat
  have hdm32 := H.dMap32
  have hsize := H.dMapSize
  have hu : (dMapIndex st.dCur st.clen).toNat = 4 * st.dCur.toNat + distanceContextId st.clen.toNat :=
    dMapIndex_toNat (by omega)
  unfold stepDistanceSymbol
  rw [dite_eq_left (UInt64.lt_iff_toNat_lt.mpr ht)]
  have hi : (dMapIndex st.dCur st.clen).toNat < H.dMap.size := by
    rw [hu]
    omega
  have hmapv := hH.dMap _ hi
  rw [hu] at hmapv
  refine distanceThrough_ok _ hH hrel0 ?_ hp hfull
  unfold distancePrefixCodeIndex
  rw [hC.dRel.cur, ← hclen]
  exact hmapv

end Brotli.Decoder
