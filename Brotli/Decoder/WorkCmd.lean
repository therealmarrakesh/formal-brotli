import Brotli.Decoder.WorkHdr

/-!
# The work of a meta-block's commands

Each function here mirrors the command loop's step or helper of the same name without its `W`, branch by branch, and
counts the rounds of its loops. A step's work is a constant, ten for each byte it adds to the window, and for a step that
begins a dictionary word, the word's building.
-/

namespace Brotli.Decoder

open Brotli.Spec Brotli.Properties

/-! ### The loops -/

/-- The work of `literalRun`: a refill and a round for each literal, and one for the round that stops it. -/
def literalRunW {nTrees : Nat} {arena litBase lMap : ByteArray} (C : LitChecked arena litBase lMap nTrees)
    (a : ByteArray) (stop : USize) (hs : stop.toNat ≤ a.size) (mapBase modeOff mask : USize) (k : Nat)
    (hmb : mapBase.toNat + 64 ≤ lMap.size) (hm : modeOff.toNat + 512 ≤ 2048) (hd : modeOff.toNat % 512 = 0)
    (hmask : mask.toNat = 2 ^ k - 1) (hk : k ≤ 24) (n : USize) (word count : UInt64) (pos wpos : USize) (ring : ByteArray)
    (p1 p2 : UInt8) (hp : pos.toNat ≤ stop.toNat) (hw : (BitBuffer.mk word count).Wf) (hsize : ring.size = 2 ^ k)
    (hwp : wpos.toNat < 2 ^ k) : Nat :=
  if hn : n = 0 then 1
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
    let l := v &&& 63
    if hl : l ≤ rc then
      let byte := (v >>> 8).toUInt8
      have hl63 : l.toNat < 64 := by
        have : (v &&& 63).toNat = v.toNat % 64 := by
          rw [UInt64.toNat_and]
          exact Nat.and_two_pow_sub_one_eq_mod v.toNat 6
        show (v &&& 63).toNat < 64
        omega
      have hr : wpos.toNat < ring.size := by omega
      let ring' := ringWrite ring wpos byte hr
      have hsize' : ring'.size = 2 ^ k := (size_ringWrite ring wpos byte hr).trans hsize
      have hnext : (ringNext wpos mask).toNat < 2 ^ k := by
        unfold ringNext
        rw [USize.toNat_and, hmask, Nat.and_two_pow_sub_one_eq_mod]
        exact Nat.mod_lt _ (Nat.two_pow_pos _)
      let b := (BitBuffer.mk rw rc).drop l
      refillW word count a pos stop hs + 1 +
        literalRunW C a stop hs mapBase modeOff mask k hmb hm hd hmask hk (n - USize.ofNat 1) b.word b.count rp (ringNext wpos mask) ring'
          byte p1 hspec.2.2.1 (BitBuffer.drop_wf hspec.1 hl63 (UInt64.le_iff_toNat_le.mp hl)) hsize' hnext
    else refillW word count a pos stop hs + 1
termination_by n.toNat
decreasing_by
  have := usize_pred hn
  have := usize_ne hn
  omega

/-- The literal loop's work: ten for each literal it writes, and eleven. -/
theorem literalRunW_le {nTrees : Nat} {arena litBase lMap : ByteArray} (C : LitChecked arena litBase lMap nTrees)
    (a : ByteArray) (stop : USize) (hs : stop.toNat ≤ a.size) (mapBase modeOff mask : USize) (k : Nat)
    (hmb : mapBase.toNat + 64 ≤ lMap.size) (hm : modeOff.toNat + 512 ≤ 2048) (hd : modeOff.toNat % 512 = 0)
    (hmask : mask.toNat = 2 ^ k - 1) (hk : k ≤ 24) : ∀ (N : Nat) (n : USize) (word count : UInt64) (pos wpos : USize) (ring : ByteArray)
    (p1 p2 : UInt8) (hp : pos.toNat ≤ stop.toNat) (hw : (BitBuffer.mk word count).Wf) (hsize : ring.size = 2 ^ k)
    (hwp : wpos.toNat < 2 ^ k), n.toNat = N →
    literalRunW C a stop hs mapBase modeOff mask k hmb hm hd hmask hk n word count pos wpos ring p1 p2 hp hw hsize hwp +
      10 * (literalRun C a stop hs mapBase modeOff mask k hmb hm hd hmask hk n word count pos wpos ring p1 p2 hp hw hsize hwp).left.toNat ≤
      10 * N + 11 := by
  intro N
  induction N with
  | zero =>
    intro n word count pos wpos ring p1 p2 hp hw hsize hwp hN
    have hz : n = 0 := usize_zero hN
    rw [literalRunW, dite_eq_left hz, literalRun, dite_eq_left hz]
    show 1 + 10 * (0 : USize).toNat ≤ _
    rw [show (0 : USize).toNat = 0 from rfl]
    omega
  | succ N ih =>
    intro n word count pos wpos ring p1 p2 hp hw hsize hwp hN
    have hn : n ≠ 0 := fun e => by rw [e] at hN; exact Nat.succ_ne_zero _ hN.symm
    have hpred := usize_pred hn
    have hR := refillW_le (word := word) (count := count) hs hp
    rw [literalRunW, dite_eq_right hn, literalRun, dite_eq_right hn]
    dsimp only
    split
    · rw [Nat.add_assoc]
      refine Nat.le_trans (Nat.add_le_add_left (ih _ _ _ _ _ _ _ _ _ _ _ _ ?_) _) ?_
      · rw [hpred]
        omega
      · omega
    · show refillW word count a pos stop hs + 1 + 10 * n.toNat ≤ _
      omega

/-- The literal loop leaves at most the literals it was given. -/
theorem literalRun_left_le {nTrees : Nat} {arena litBase lMap : ByteArray} (C : LitChecked arena litBase lMap nTrees)
    (a : ByteArray) (stop : USize) (hs : stop.toNat ≤ a.size) (mapBase modeOff mask : USize) (k : Nat)
    (hmb : mapBase.toNat + 64 ≤ lMap.size) (hm : modeOff.toNat + 512 ≤ 2048) (hd : modeOff.toNat % 512 = 0)
    (hmask : mask.toNat = 2 ^ k - 1) (hk : k ≤ 24) : ∀ (N : Nat) (n : USize) (word count : UInt64) (pos wpos : USize) (ring : ByteArray)
    (p1 p2 : UInt8) (hp : pos.toNat ≤ stop.toNat) (hw : (BitBuffer.mk word count).Wf) (hsize : ring.size = 2 ^ k)
    (hwp : wpos.toNat < 2 ^ k), n.toNat = N →
    (literalRun C a stop hs mapBase modeOff mask k hmb hm hd hmask hk n word count pos wpos ring p1 p2 hp hw hsize hwp).left.toNat ≤ N := by
  intro N
  induction N with
  | zero =>
    intro n word count pos wpos ring p1 p2 hp hw hsize hwp hN
    have hz : n = 0 := usize_zero hN
    rw [literalRun, dite_eq_left hz]
    show (0 : USize).toNat ≤ 0
    exact Nat.le_refl _
  | succ N ih =>
    intro n word count pos wpos ring p1 p2 hp hw hsize hwp hN
    have hn : n ≠ 0 := fun e => by rw [e] at hN; exact Nat.succ_ne_zero _ hN.symm
    have hpred := usize_pred hn
    rw [literalRun, dite_eq_right hn]
    dsimp only
    split
    · exact Nat.le_trans (ih _ _ _ _ _ _ _ _ _ _ _ _ (by omega)) (Nat.le_succ _)
    · show n.toNat ≤ _
      omega

/-! ### A dictionary word -/

/-- The work of `elementStep`: a round for each byte of the run, and the first byte's ferment. -/
def elementStepW (kind : UInt8) (len : USize) : Nat :=
  if kind = 1 then len.toNat + 2 else len.toNat + 1

/-- The work of `buildWord`: the buffer's 38 bytes, then a round for each byte of the prefix, the run and the suffix. -/
def buildWordW (id len : USize) : Nat :=
  let base := id * USize.ofNat 32
  38 + (getU transLut (base + USize.ofNat 2)).toNat + elementStepW (getU transLut base) len +
    (getU transLut (base + USize.ofNat 3)).toNat + 1

/-- The work of `dictBuild`. -/
def dictBuildW (clen wordId : UInt64) (h : dictValid clen wordId) : Nat :=
  buildWordW (dictTid (lenRow clen (lt25 h.1)) wordId).toUSize clen.toUSize

private theorem base_plus {id : USize} (hid : id.toNat < 121) (j : Nat) (hj : j < 32) :
    (id * USize.ofNat 32 + USize.ofNat j).toNat = 32 * id.toNat + j := by
  have hs := USize.le_size
  have e32 : (USize.ofNat 32).toNat = 32 := usize_ofNat' (by decide)
  have ej : (USize.ofNat j).toNat = j := usize_ofNat' (by omega)
  have hmul : (id * USize.ofNat 32).toNat = 32 * id.toNat := by
    rw [USize.toNat_mul, e32, Nat.mul_comm, ← USize.size_eq_two_pow]
    exact Nat.mod_eq_of_lt (by omega)
  rw [USize.toNat_add, hmul, ej, ← USize.size_eq_two_pow]
  exact Nat.mod_eq_of_lt (by omega)

/-- A dictionary word's building: at most 93 rounds. -/
theorem dictBuildW_le (clen wordId : UInt64) (h : dictValid clen wordId) : dictBuildW clen wordId h ≤ 93 := by
  obtain ⟨hc, ht⟩ := h
  have hid : (dictTid (lenRow clen (lt25 hc)) wordId).toUSize.toNat < 121 := by
    rw [word_toUSize (by have := lt121 ht; omega)]
    exact lt121 ht
  have hl : clen.toUSize.toNat ≤ 24 := by
    rw [word_toUSize (by have := lt25 hc; omega)]
    have := lt25 hc
    omega
  unfold dictBuildW buildWordW elementStepW
  generalize (dictTid (lenRow clen (lt25 hc)) wordId).toUSize = id at hid ⊢
  generalize clen.toUSize = len at hl ⊢
  have h2 : (getU transLut (id * USize.ofNat 32 + USize.ofNat 2)).toNat = (transLut.data[32 * id.toNat + 2]?.getD 0).toNat := by
    rw [getU_toNat, base_plus hid 2 (by decide)]
  have h3 : (getU transLut (id * USize.ofNat 32 + USize.ofNat 3)).toNat = (transLut.data[32 * id.toNat + 3]?.getD 0).toNat := by
    rw [getU_toNat, base_plus hid 3 (by decide)]
  have := affix_le hid
  dsimp only
  rw [h2, h3]
  split <;> omega

/-! ### The steps -/

/-- The work of `applyWord`: the word's building. -/
def applyWordW (st : Cmd) (wordId : UInt64) : Nat :=
  if h : dictValid st.clen wordId then dictBuildW st.clen wordId h + 1 else 1

/-- The work of `applyDistance`. -/
def applyDistanceW (st : Cmd) (d : UInt64) : Nat :=
  if st.written.toUInt64 < d then applyWordW st (d - (st.written.toUInt64 + 1)) else 1

/-- The work of `distanceStep`. -/
def distanceStepW (H : Hdr) (st : Cmd) (v : UInt64) : Nat :=
  if wordBits v ≤ st.count then
    let nbits := extraBitsFast H.npostfix H.ndirect (wordSym v)
    let b1 := (BitBuffer.mk st.word st.count).drop (wordBits v)
    if nbits ≤ 24 then
      if nbits ≤ b1.count then
        let b2 := b1.drop nbits
        let d := distFast H.npostfix H.ndirect st.d0 st.d1 st.d2 st.d3 (wordSym v) (b1.peek nbits)
        if d = 0 then 1 else applyDistanceW (setBits st b2.word b2.count) d
      else 1
    else 1
  else 1

/-- The work of `distanceThrough`. -/
def distanceThroughW (H : Hdr) (st : Cmd) (tree : UInt8) (htree : tree.toNat < H.treesD.toNat) : Nat :=
  have hb : 4 * tree.toUInt64.toNat + 4 ≤ H.dBase.size := by
    rw [H.dSize, UInt8.toNat_toUInt64]
    omega
  have hfit : TableFits H.arena (tableBase H.dBase tree.toUInt64 hb H.d32).toNat := by
    rw [tableBase_toNat, UInt8.toNat_toUInt64]
    exact H.dFits _ htree
  distanceStepW H st (lookup H.arena (tableBase H.dBase tree.toUInt64 hb H.d32) st.word hfit H.lit.arena32)

/-- The work of `stepDistanceSymbol`. -/
def stepDistanceSymbolW (H : Hdr) (st : Cmd) : Nat :=
  if ht : st.dCur < H.nD then
    have ht' := UInt64.lt_iff_toNat_lt.mp ht
    have hi : (dMapIndex st.dCur st.clen).toNat < H.dMap.size := by
      have h1 := H.dMap32
      have h2 := H.dMapSize
      have hcid := distanceContextId_lt st.clen.toNat
      rw [dMapIndex_toNat (by omega)]
      omega
    distanceThroughW H st (H.dMap.uget (dMapIndex st.dCur st.clen) hi) (H.dMapLt _ hi)
  else 1

/-- The work of `stepDistance`. -/
def stepDistanceW (st : Cmd) : Nat :=
  if st.remaining = 0 then 1
  else if st.code < 128 then (if st.d0 = 0 then 1 else applyDistanceW st st.d0)
  else 1

/-- The work of `literalsRun`. -/
def literalsRunW (H : Hdr) (k : USize) (a : ByteArray) (stop : USize) (hs : stop.toNat ≤ a.size) (st : Cmd) (pos : USize) : Nat :=
  if ht : st.lCur < H.nL then
    have ht' := UInt64.lt_iff_toNat_lt.mp ht
    have hm : st.lCur.toUSize.toNat < H.modes.size := by
      rw [cur_usize ht', H.modesSize]
      exact ht'
    have hmLt := H.modesLt _ hm
    if h : winCheck k st.wpos st.ring = true ∧ pos ≤ stop ∧ wfCheck st.word st.count = true then
      let run := (umin st.left (umin st.lCount (room k st.cap - st.pend).toUInt64)).toUSize
      let ring := st.ring
      let st0 := clearRing st
      literalRunW H.lit a stop hs (st.lCur <<< 6).toUSize ((H.modes.uget st.lCur.toUSize hm).toUInt64 <<< 9).toUSize
        (ringMask k) k.toNat
        (by
          rw [mapBase_toNat ht', H.lMapSize]
          omega)
        (by
          rw [modeOff_toNat hmLt]
          omega)
        (by
          rw [modeOff_toNat hmLt]
          omega)
        (ringMask_toNat (winCheck_k h.1)) (winCheck_k h.1) run st0.word st0.count pos st0.wpos ring st0.p1 st0.p2
        (USize.le_iff_toNat_le.mp h.2.1) (wfCheck_wf h.2.2) (winCheck_size h.1) (winCheck_pos h.1) + 1
    else 1
  else 1

/-- The work of `stepLiterals`. -/
def stepLiteralsW (H : Hdr) (k : USize) (a : ByteArray) (stop : USize) (hs : stop.toNat ≤ a.size) (st : Cmd) (pos : USize) : Nat :=
  if st.left = 0 then 1
  else if st.lCount = 0 then 1
  else if room k st.cap ≤ st.pend then 1
  else literalsRunW H k a stop hs st pos

/-- The work of `stepCopy`: a round for each byte copied. -/
def stepCopyW (k : USize) (st : Cmd) : Nat :=
  if st.left = 0 then 1
  else if room k st.cap ≤ st.pend then 1
  else
    let run := (umin st.left (room k st.cap - st.pend).toUInt64).toUSize
    let d := st.dist.toUSize
    if winCheck k st.wpos st.ring = true ∧ USize.ofNat 1 ≤ d ∧ d ≤ ringSize k then run.toNat + 1 else 1

/-- The work of `stepWord`: a round for each byte written. -/
def stepWordW (k : USize) (st : Cmd) : Nat :=
  let n := st.wordBuf.usize - st.wordPos
  if n = 0 then 1
  else if room k st.cap ≤ st.pend then 1
  else
    let run := usmin n (room k st.cap - st.pend)
    if winCheck k st.wpos st.ring = true ∧ st.wordPos.toNat + run.toNat ≤ st.wordBuf.size ∧
        st.wordPos.toNat + run.toNat ≤ 2 ^ 32 - 1 then run.toNat + 1 else 1

/-- The work of a command loop step, once the buffer is refilled. -/
def stepAtW (H : Hdr) (k : USize) (a : ByteArray) (stop : USize) (hs : stop.toNat ≤ a.size) (st : Cmd) (pos : USize) : Nat :=
  match st.tag with
  | .command => 1
  | .insertCopy => 1
  | .copyLength => 1
  | .literals => stepLiteralsW H k a stop hs st pos
  | .distance => stepDistanceW st
  | .distanceSymbol => stepDistanceSymbolW H st
  | .copy => stepCopyW k st
  | .word => stepWordW k st

/-- The work of a command loop step: the refill, then the step. -/
def stepCmdW (H : Hdr) (k : USize) (a : ByteArray) (stop : USize) (hs : stop.toNat ≤ a.size) (st : Cmd) (pos : USize) : Nat :=
  if hp : pos ≤ stop then
    let r := refill st.word st.count a pos stop hs (USize.le_iff_toNat_le.mp hp)
    refillW st.word st.count a pos stop hs + stepAtW H k a stop hs { st with word := r.word, count := r.count } r.pos
  else 1

/-- The work of the command loop: its rounds, and each one's step. -/
def runCmdW (H : Hdr) (k : USize) (a : ByteArray) (stop : USize) (hs : stop.toNat ≤ a.size) (n : USize) (st : Cmd) (pos : USize) :
    Nat :=
  if _hn : n = 0 then 1
  else
    let r := stepCmd H k a stop hs st pos
    stepCmdW H k a stop hs st pos + 1 +
      match r.status with
      | .next => runCmdW H k a stop hs (n - USize.ofNat 1) r r.pos
      | _ => 0
termination_by n.toNat
decreasing_by
  have := usize_pred _hn
  have := usize_ne _hn
  omega

/-! ### A step's work -/

/-- A distance's copy: a dictionary word is built only when the step goes on to its bytes or stops. -/
theorem applyDistanceW_le (st : Cmd) (pos : USize) (dc d : UInt64) :
    applyDistanceW st d ≤ 1 + (if (applyDistance st pos dc d).status = .next ∧ (applyDistance st pos dc d).tag ≠ .word then 0 else 94) ∧
      (applyDistance st pos dc d).pend = st.pend := by
  unfold applyDistanceW applyDistance
  by_cases hw : st.written.toUInt64 < d
  · rw [ite_eq_left hw, ite_eq_left hw]
    unfold applyWordW applyWord
    by_cases hv : dictValid st.clen (d - (st.written.toUInt64 + 1))
    · rw [dite_eq_left hv, dite_eq_left hv]
      have := dictBuildW_le st.clen (d - (st.written.toUInt64 + 1)) hv
      unfold applyBuilt
      split
      · refine ⟨?_, rfl⟩
        rw [ite_eq_right (fun h => StepStatus.noConfusion h.1)]
        omega
      · refine ⟨?_, rfl⟩
        rw [ite_eq_right (fun h => h.2 rfl)]
        omega
    · rw [dite_eq_right hv, dite_eq_right hv]
      exact ⟨by omega, rfl⟩
  · rw [ite_eq_right hw, ite_eq_right hw]
    split
    · exact ⟨by omega, rfl⟩
    · split
      · exact ⟨by omega, rfl⟩
      · exact ⟨by omega, rfl⟩

/-- A run that fits the room left: adding it to the bytes waiting doesn't wrap. -/
theorem pend_add {pend run : USize} (h : pend.toNat + run.toNat ≤ 2 ^ 24) : (pend + run).toNat = pend.toNat + run.toNat := by
  rw [USize.toNat_add, ← USize.size_eq_two_pow]
  have := USize.le_size
  exact Nat.mod_eq_of_lt (by omega)

/-- A run of at most the room left, as an index. -/
theorem run_le {k cap pend : USize} {x : UInt64} (hk : k.toNat ≤ 24) (hr : ¬ room k cap ≤ pend) :
    (umin x (room k cap - pend).toUInt64).toUSize.toNat ≤ (room k cap).toNat - pend.toNat := by
  have h1 := room_lt hr
  have h2 := room_le (cap := cap) hk
  have h3 : (2 : Nat) ^ k.toNat ≤ 2 ^ 24 := Nat.pow_le_pow_right (by decide) hk
  have hs : (room k cap - pend).toNat = (room k cap).toNat - pend.toNat := room_sub' (by omega)
  have hm := umin_toNat x (room k cap - pend).toUInt64
  rw [USize.toNat_toUInt64, hs] at hm
  have h4 : (2 : Nat) ^ 24 < 2 ^ 32 := by decide
  rw [word_toUSize (by rw [hm]; omega), hm]
  omega

theorem copyW_le {k : USize} {st : Cmd} {pos : USize} (hk : k.toNat ≤ 24) :
    stepCopyW k st ≤ 1 + ((stepCopy k st pos).pend.toNat - st.pend.toNat) := by
  unfold stepCopyW stepCopy
  by_cases h0 : st.left = 0
  · rw [ite_eq_left h0, ite_eq_left h0]
    omega
  rw [ite_eq_right h0, ite_eq_right h0]
  by_cases hr : room k st.cap ≤ st.pend
  · rw [ite_eq_left hr, ite_eq_left hr]
    omega
  rw [ite_eq_right hr, ite_eq_right hr]
  dsimp only
  have hrun := run_le (x := st.left) hk hr
  have h1 := room_lt hr
  have h2 := room_le (cap := st.cap) hk
  have h3 : (2 : Nat) ^ k.toNat ≤ 2 ^ 24 := Nat.pow_le_pow_right (by decide) hk
  generalize (umin st.left (room k st.cap - st.pend).toUInt64).toUSize = run at hrun ⊢
  by_cases hc : winCheck k st.wpos st.ring = true ∧ USize.ofNat 1 ≤ st.dist.toUSize ∧ st.dist.toUSize ≤ ringSize k
  · rw [ite_eq_left hc, dite_eq_left hc]
    show _ ≤ 1 + ((((clearRing st).pend + run)).toNat - st.pend.toNat)
    rw [show (clearRing st).pend = st.pend from rfl, pend_add (by omega)]
    omega
  · rw [ite_eq_right hc, dite_eq_right hc]
    omega

theorem wordW_le {k : USize} {st : Cmd} {pos : USize} (hk : k.toNat ≤ 24) :
    stepWordW k st ≤ 1 + ((stepWord k st pos).pend.toNat - st.pend.toNat) := by
  unfold stepWordW stepWord
  dsimp only
  by_cases h0 : st.wordBuf.usize - st.wordPos = 0
  · rw [ite_eq_left h0, ite_eq_left h0]
    omega
  rw [ite_eq_right h0, ite_eq_right h0]
  by_cases hr : room k st.cap ≤ st.pend
  · rw [ite_eq_left hr, ite_eq_left hr]
    omega
  rw [ite_eq_right hr, ite_eq_right hr]
  have h1 := room_lt hr
  have h2 := room_le (cap := st.cap) hk
  have h3 : (2 : Nat) ^ k.toNat ≤ 2 ^ 24 := Nat.pow_le_pow_right (by decide) hk
  have hs : (room k st.cap - st.pend).toNat = (room k st.cap).toNat - st.pend.toNat := room_sub' (by omega)
  have hrun : (usmin (st.wordBuf.usize - st.wordPos) (room k st.cap - st.pend)).toNat ≤ (room k st.cap).toNat - st.pend.toNat := by
    rw [usmin_toNat, hs]
    omega
  by_cases hc : winCheck k st.wpos st.ring = true ∧
      st.wordPos.toNat + (usmin (st.wordBuf.usize - st.wordPos) (room k st.cap - st.pend)).toNat ≤ st.wordBuf.size ∧
      st.wordPos.toNat + (usmin (st.wordBuf.usize - st.wordPos) (room k st.cap - st.pend)).toNat ≤ 2 ^ 32 - 1
  · rw [ite_eq_left hc, dite_eq_left hc]
    show _ ≤ 1 + (((clearRing st).pend + usmin (st.wordBuf.usize - st.wordPos) (room k st.cap - st.pend)).toNat - st.pend.toNat)
    rw [show (clearRing st).pend = st.pend from rfl, pend_add (by omega)]
    omega
  · rw [ite_eq_right hc, dite_eq_right hc]
    omega

theorem literalsW_le {H : Hdr} {k : USize} {a : ByteArray} {stop : USize} {hs : stop.toNat ≤ a.size} {st : Cmd} {pos : USize}
    (hk : k.toNat ≤ 24) : stepLiteralsW H k a stop hs st pos ≤ 12 + 10 * ((stepLiterals H k a stop hs st pos).pend.toNat - st.pend.toNat) := by
  unfold stepLiteralsW stepLiterals
  by_cases h0 : st.left = 0
  · rw [ite_eq_left h0]
    omega
  rw [ite_eq_right h0, ite_eq_right h0]
  by_cases hc : st.lCount = 0
  · rw [ite_eq_left hc]
    omega
  rw [ite_eq_right hc, ite_eq_right hc]
  by_cases hr : room k st.cap ≤ st.pend
  · rw [ite_eq_left hr]
    omega
  rw [ite_eq_right hr, ite_eq_right hr]
  have h1 := room_lt hr
  have h2 := room_le (cap := st.cap) hk
  have h3 : (2 : Nat) ^ k.toNat ≤ 2 ^ 24 := Nat.pow_le_pow_right (by decide) hk
  unfold literalsRunW literalsRun
  split
  · split
    · dsimp only
      have hrun' : (umin st.left (umin st.lCount (room k st.cap - st.pend).toUInt64)).toUSize.toNat ≤
          (room k st.cap).toNat - st.pend.toNat := by
        have hm1 := umin_toNat st.left (umin st.lCount (room k st.cap - st.pend).toUInt64)
        have hm2 := umin_toNat st.lCount (room k st.cap - st.pend).toUInt64
        have hs : (room k st.cap - st.pend).toNat = (room k st.cap).toNat - st.pend.toNat := room_sub' (by omega)
        have h4 : (2 : Nat) ^ 24 < 2 ^ 32 := by decide
        rw [USize.toNat_toUInt64, hs] at hm2
        rw [word_toUSize (by rw [hm1, hm2]; omega), hm1, hm2]
        omega
      generalize (umin st.left (umin st.lCount (room k st.cap - st.pend).toUInt64)).toUSize = run at hrun' ⊢
      have key : ∀ (W : Nat) (L : LitRun), W + 10 * L.left.toNat ≤ 10 * run.toNat + 11 → L.left.toNat ≤ run.toNat →
          W + 1 ≤ 12 + 10 * ((finishLiterals (clearRing st) L run (ringSize k)).pend.toNat - st.pend.toNat) := by
        intro W L hW hL
        show W + 1 ≤ 12 + 10 * (((clearRing st).pend + (run - L.left)).toNat - st.pend.toNat)
        have hsub : (run - L.left).toNat = run.toNat - L.left.toNat := USize.toNat_sub_of_le _ _ (USize.le_iff_toNat_le.mpr hL)
        rw [show (clearRing st).pend = st.pend from rfl, pend_add (by rw [hsub]; omega), hsub]
        omega
      exact key _ _ (literalRunW_le _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ rfl)
        (literalRun_left_le _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ rfl)
    · dsimp only
      omega
  · omega

/-- The word cost a step may have: none when it goes on to anything but a word's bytes. -/
def wordCost (t : Tag) (r : Cmd) : Nat := if r.status = .next ∧ ¬ (r.tag = .word ∧ t ≠ .word) then 0 else 95

theorem distanceW_le {H : Hdr} {st : Cmd} {pos : USize} (ht : st.tag = .distance) :
    stepDistanceW st ≤ 1 + (wordCost st.tag (stepDistance H st pos) - 1) ∧ (stepDistance H st pos).pend = st.pend := by
  unfold stepDistanceW stepDistance wordCost
  by_cases h0 : st.remaining = 0
  · rw [ite_eq_left h0, ite_eq_left h0]
    exact ⟨by omega, rfl⟩
  rw [ite_eq_right h0, ite_eq_right h0]
  by_cases hc : st.code < 128
  · rw [ite_eq_left hc, ite_eq_left hc]
    by_cases hd : st.d0 = 0
    · rw [ite_eq_left hd, ite_eq_left hd]
      exact ⟨by omega, rfl⟩
    · rw [ite_eq_right hd, ite_eq_right hd]
      obtain ⟨h1, h2⟩ := applyDistanceW_le st pos 0 st.d0
      refine ⟨?_, h2⟩
      have hne : (st.tag ≠ .word) := by rw [ht]; exact fun e => Tag.noConfusion e
      split
      · rename_i hh
        have : (applyDistance st pos 0 st.d0).tag ≠ .word := fun e => hh.2 ⟨e, hne⟩
        rw [ite_eq_left ⟨hh.1, this⟩] at h1
        omega
      · split at h1 <;> omega
  · rw [ite_eq_right hc, ite_eq_right hc]
    refine ⟨by omega, ?_⟩
    dsimp only
    repeat' split
    all_goals rfl

theorem distanceStepW_le {H : Hdr} {st : Cmd} {pos : USize} {v : UInt64} (ht : st.tag ≠ .word) :
    distanceStepW H st v ≤ 1 + (wordCost st.tag (distanceStep H st pos v) - 1) ∧ (distanceStep H st pos v).pend = st.pend := by
  unfold distanceStepW distanceStep wordCost
  by_cases h1 : wordBits v ≤ st.count
  · rw [ite_eq_left h1, ite_eq_left h1]
    dsimp only
    by_cases h2 : extraBitsFast H.npostfix H.ndirect (wordSym v) ≤ 24
    · rw [ite_eq_left h2, ite_eq_left h2]
      by_cases h3 : extraBitsFast H.npostfix H.ndirect (wordSym v) ≤ ((BitBuffer.mk st.word st.count).drop (wordBits v)).count
      · rw [ite_eq_left h3, ite_eq_left h3]
        generalize distFast H.npostfix H.ndirect st.d0 st.d1 st.d2 st.d3 (wordSym v)
          (((BitBuffer.mk st.word st.count).drop (wordBits v)).peek (extraBitsFast H.npostfix H.ndirect (wordSym v))) = d
        by_cases h4 : d = 0
        · rw [ite_eq_left h4, ite_eq_left h4]
          exact ⟨by omega, rfl⟩
        · rw [ite_eq_right h4, ite_eq_right h4]
          have key : ∀ st' : Cmd, st'.pend = st.pend →
              applyDistanceW st' d ≤ 1 + ((if (applyDistance st' pos (wordSym v) d).status = .next ∧
                ¬ ((applyDistance st' pos (wordSym v) d).tag = .word ∧ st.tag ≠ .word) then 0 else 95) - 1) ∧
              (applyDistance st' pos (wordSym v) d).pend = st.pend := by
            intro st' hp
            obtain ⟨e1, e2⟩ := applyDistanceW_le st' pos (wordSym v) d
            refine ⟨?_, e2.trans hp⟩
            by_cases hh : (applyDistance st' pos (wordSym v) d).status = .next ∧
                (applyDistance st' pos (wordSym v) d).tag ≠ .word
            · rw [ite_eq_left hh] at e1
              omega
            · rw [ite_eq_right hh] at e1
              have : ¬ ((applyDistance st' pos (wordSym v) d).status = .next ∧
                  ¬ ((applyDistance st' pos (wordSym v) d).tag = .word ∧ st.tag ≠ .word)) :=
                fun h => hh ⟨h.1, fun e => h.2 ⟨e, ht⟩⟩
              rw [ite_eq_right this]
              omega
          exact key _ rfl
      · rw [ite_eq_right h3, ite_eq_right h3]
        exact ⟨by omega, rfl⟩
    · rw [ite_eq_right h2, ite_eq_right h2]
      exact ⟨by omega, rfl⟩
  · rw [ite_eq_right h1, ite_eq_right h1]
    exact ⟨by omega, rfl⟩

theorem distanceSymbolW_le {H : Hdr} {st : Cmd} {pos : USize} (ht : st.tag = .distanceSymbol) :
    stepDistanceSymbolW H st ≤ 1 + (wordCost st.tag (stepDistanceSymbol H st pos) - 1) ∧
      (stepDistanceSymbol H st pos).pend = st.pend := by
  have hne : st.tag ≠ .word := by rw [ht]; exact fun e => Tag.noConfusion e
  unfold stepDistanceSymbolW stepDistanceSymbol
  by_cases hd : st.dCur < H.nD
  · rw [dite_eq_left hd, dite_eq_left hd]
    unfold distanceThroughW distanceThrough
    exact distanceStepW_le hne
  · rw [dite_eq_right hd, dite_eq_right hd]
    exact ⟨by unfold wordCost; split <;> omega, rfl⟩

/-- A command loop step's work, once the buffer is refilled: twelve, ten for each byte it adds to the window, and a
dictionary word's building when it begins one or stops. -/
theorem stepAtW_le {H : Hdr} {k : USize} {a : ByteArray} {stop : USize} {hs : stop.toNat ≤ a.size} {st : Cmd} {pos : USize}
    (hk : k.toNat ≤ 24) : stepAtW H k a stop hs st pos ≤
      12 + 10 * ((stepAt H k a stop hs st pos).pend.toNat - st.pend.toNat) + wordCost st.tag (stepAt H k a stop hs st pos) := by
  unfold stepAtW stepAt
  cases ht : st.tag with
  | command => dsimp only; omega
  | insertCopy => dsimp only; omega
  | copyLength => dsimp only; omega
  | literals => have := literalsW_le (H := H) (a := a) (hs := hs) (st := st) (pos := pos) hk; dsimp only; omega
  | distance =>
    have := distanceW_le (H := H) (pos := pos) ht
    rw [ht] at this
    dsimp only
    omega
  | distanceSymbol =>
    have := distanceSymbolW_le (H := H) (pos := pos) ht
    rw [ht] at this
    dsimp only
    omega
  | copy => have := copyW_le (st := st) (pos := pos) hk; dsimp only; omega
  | word => have := wordW_le (st := st) (pos := pos) hk; dsimp only; omega

/-- A command loop step's work: the refill's, then the step's. -/
theorem stepCmdW_le {H : Hdr} {k : USize} {a : ByteArray} {stop : USize} {hs : stop.toNat ≤ a.size} {st : Cmd} {pos : USize}
    (hk : k.toNat ≤ 24) (hp : pos.toNat ≤ stop.toNat) : stepCmdW H k a stop hs st pos ≤
      21 + 10 * ((stepCmd H k a stop hs st pos).pend.toNat - st.pend.toNat) + wordCost st.tag (stepCmd H k a stop hs st pos) := by
  have hp' : pos ≤ stop := USize.le_iff_toNat_le.mpr hp
  unfold stepCmdW stepCmd
  rw [dite_eq_left hp', dite_eq_left hp']
  dsimp only
  have h1 := refillW_le (word := st.word) (count := st.count) hs hp
  have h2 := stepAtW_le (H := H) (a := a) (hs := hs)
    (st := { st with word := (refill st.word st.count a pos stop hs hp).word, count := (refill st.word st.count a pos stop hs hp).count })
    (pos := (refill st.word st.count a pos stop hs hp).pos) hk
  dsimp only at h2
  exact Nat.le_trans (Nat.add_le_add_left h2 _) (by omega)

end Brotli.Decoder
